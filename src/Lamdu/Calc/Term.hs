-- | Val AST
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, StandaloneDeriving, TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables, DerivingStrategies, DataKinds #-}
{-# LANGUAGE PolyKinds, TypeApplications #-}

module Lamdu.Calc.Term
    ( Val
    , Leaf(..), _LVar, _LHole, _LLiteral, _LRecEmpty, _LAbsurd, _LFromNom
    , PrimVal(..), primType, primData
    , Term(..)
        , _BApp, _BLam, _BGetField, _BRecExtend
        , _BInject, _BCase, _BToNom, _BLeaf
        , W_Term(..)
    , App(..), appFunc, appArg
    , GetField(..), getFieldRecord, getFieldTag
    , Inject(..), injectVal, injectTag
    , Lam(..), lamIn, lamOut
    , Var(..)
    , Scope(..), scopeNominals, scopeVarTypes, scopeLevel
    , emptyScope
    , ToNom(..), FromNom(..), RowExtend(..)
    , HPlain(..)
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import           Data.Constraint
import           Data.Hashable (Hashable(..))
import           Data.Map (Map)
import           Data.Proxy (Proxy(..))
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import           Generics.Constraints (makeDerivings, makeInstances)
import           Hyper
import           Hyper.Infer
import           Hyper.Infer.Blame (Blame(..))
import           Hyper.Recurse
import           Hyper.Type.AST.App (App(..), appFunc, appArg)
import           Hyper.Type.AST.FuncType (FuncType(..))
import           Hyper.Type.AST.Lam (Lam(..), lamIn, lamOut)
import           Hyper.Type.AST.Nominal (ToNom(..), FromNom(..), NominalInst(..), MonadNominals, LoadedNominalDecl)
import           Hyper.Type.AST.Row (RowExtend(..), rowElementInfer)
import           Hyper.Type.AST.Scheme (QVarInstances(..))
import qualified Hyper.Type.AST.Var as TermVar
import           Hyper.Unify
import qualified Hyper.Unify.Generalize as G
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.New (newTerm, newUnbound)
import           Hyper.Unify.Term (UTerm(..))
import           Lamdu.Calc.Identifier (Identifier)
import qualified Lamdu.Calc.Type as T
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

{-# ANN module ("HLint: ignore Use const"::String) #-}

newtype Var = Var { vvName :: Identifier }
    deriving stock Show
    deriving newtype (Eq, Ord, NFData, IsString, Pretty, Binary, Hashable)

data PrimVal = PrimVal
    { _primType :: {-# UNPACK #-} !T.NominalId
    , _primData :: {-# UNPACK #-} !ByteString
    } deriving (Generic, Show, Eq, Ord)
instance NFData PrimVal
instance Binary PrimVal
instance Hashable PrimVal

Lens.makeLenses ''PrimVal

data Leaf
    =  LVar {-# UNPACK #-}!Var
    |  LHole
    |  LLiteral {-# UNPACK #-} !PrimVal
    |  LRecEmpty
    |  LAbsurd
    |  LFromNom {-# UNPACK #-} !T.NominalId
    deriving (Generic, Show, Eq, Ord)
instance NFData Leaf
instance Binary Leaf
instance Hashable Leaf

Lens.makePrisms ''Leaf

data GetField k = GetField
    { _getFieldRecord :: k :# Term
    , _getFieldTag :: T.Tag
    } deriving Generic

data Inject k = Inject
    { _injectTag :: T.Tag
    , _injectVal :: k :# Term
    } deriving Generic

data Term k
    = BApp {-# UNPACK #-}!(App Term k)
    | BLam {-# UNPACK #-}!(Lam Var Term k)
    | BGetField {-# UNPACK #-}!(GetField k)
    | BRecExtend {-# UNPACK #-}!(RowExtend T.Tag Term Term k)
    | BInject {-# UNPACK #-}!(Inject k)
    | BCase {-# UNPACK #-}!(RowExtend T.Tag Term Term k)
    | -- Convert to Nominal type
      BToNom {-# UNPACK #-}!(ToNom T.NominalId Term k)
    | BLeaf Leaf
    deriving Generic

Lens.makePrisms ''Term
Lens.makeLenses ''GetField
Lens.makeLenses ''Inject
makeHTraversableAndBases ''GetField
makeHTraversableAndBases ''Inject
makeHTraversableAndBases ''Term
makeZipMatch ''GetField
makeZipMatch ''Inject
makeZipMatch ''Term
makeHContext ''GetField
makeHContext ''Inject
makeHContext ''Term
makeHasHPlain [''Term]

instance RNodes Term
instance c Term => Recursively c Term
instance RTraversable Term

instance Recursive ((~) Term) where
    recurse _ = Dict

instance IsString (HPlain Term) where
    fromString = BLeafP . LVar . fromString

instance Pretty (f :# Term) => Pretty (Term f) where
    pPrintPrec lvl prec b =
        case b of
        BLeaf (LVar var)          -> pPrint var
        BLeaf (LLiteral (PrimVal _p d)) -> PP.text (BS8.unpack d)
        BLeaf LHole               -> PP.text "?"
        BLeaf LAbsurd             -> PP.text "absurd"
        BLeaf (LFromNom ident)    -> PP.text "[" <+> PP.text "unpack" <+> pPrint ident <+> PP.text "]"
        BApp (App e1 e2)          -> maybeParens (10 < prec) $
                                     pPrintPrec lvl 10 e1 <+> pPrintPrec lvl 11 e2
        BLam (Lam n e)            -> maybeParens (0 < prec) $
                                     PP.char '\\' PP.<> pPrint n <+>
                                     PP.text "->" <+>
                                     pPrint e
        BGetField (GetField e n)  -> maybeParens (12 < prec) $
                                     pPrintPrec lvl 12 e <> PP.char '.' <> pPrint n
        BInject (Inject n e)      -> maybeParens (12 < prec) $
                                     pPrint n <> PP.char '{' <> pPrintPrec lvl 12 e <> PP.char '}'
        BCase (RowExtend n m mm)  -> maybeParens (0 < prec) $
                                     PP.vcat
                                     [ PP.text "case of"
                                     , pPrint n <> PP.text " -> " <> pPrint m
                                     , PP.text "_" <> PP.text " -> " <> pPrint mm
                                     ]
        BToNom (ToNom ident val)  -> PP.text "[" <+> pPrint ident <+> PP.text "pack" <+> pPrint val <+> PP.text "]"
        BLeaf LRecEmpty           -> PP.text "{}"
        BRecExtend (RowExtend tag val rest) ->
                                     PP.text "{" <+>
                                     prField PP.<>
                                     PP.comma <+>
                                     pPrint rest <+>
                                     PP.text "}"
            where
                prField = pPrint tag <+> PP.text "=" <+> pPrint val

data Scope v = Scope
    { _scopeNominals :: Map T.NominalId (LoadedNominalDecl T.Type v)
    , _scopeVarTypes :: Map Var (HFlip G.GTerm T.Type v)
    , _scopeLevel :: ScopeLevel
    } deriving Generic
Lens.makeLenses ''Scope

makeHTraversableAndBases ''Scope

{-# INLINE emptyScope #-}
emptyScope :: Scope # v
emptyScope = Scope mempty mempty (ScopeLevel 0)

type instance TermVar.ScopeOf Term = Scope
type instance InferOf Term = ANode T.Type
instance HasInferredType Term where
    type instance TypeOf Term = T.Type
    inferredType _ = _ANode

makeDerivings [''Eq, ''Ord, ''Show] [''Term, ''Scope, ''GetField, ''Inject]
makeInstances [''Binary, ''NFData, ''Hashable] [''Term, ''Scope, ''GetField, ''Inject]

instance TermVar.VarType Var Term where
    {-# INLINE varType #-}
    varType _ v x = x ^?! scopeVarTypes . Lens.ix v . _HFlip & G.instantiate

instance
    ( MonadNominals T.NominalId T.Type m
    , MonadScopeLevel m
    , TermVar.HasScope m Scope
    , UnifyGen m T.Type, UnifyGen m T.Row
    , LocalScopeType Var (UVarOf m # T.Type) m
    ) =>
    Infer m Term where

    {-# INLINE inferBody #-}
    inferBody (BApp x) = inferBody x <&> Lens._1 %~ BApp
    inferBody (BLam x) = inferBody x <&> Lens._1 %~ BLam
    inferBody (BToNom x) =
        do
            (xI, xT) <- inferBody x
            newTerm (T.TInst xT) <&> MkANode <&> (BToNom xI, )
    inferBody (BLeaf leaf) =
        case leaf of
        LHole -> newUnbound
        LRecEmpty -> newTerm T.REmpty >>= newTerm . T.TRecord
        LAbsurd ->
            FuncType
            <$> (newTerm T.REmpty >>= newTerm . T.TVariant)
            <*> newUnbound
            >>= newTerm . T.TFun
        LLiteral (PrimVal t _) ->
            T.Types (QVarInstances mempty) (QVarInstances mempty)
            & NominalInst t
            & T.TInst & newTerm
        LVar x ->
            inferBody (TermVar.Var x :: TermVar.Var Var Term # InferChild k w)
            <&> (^. Lens._2 . _ANode)
        LFromNom x ->
            inferBody (FromNom x :: FromNom T.NominalId Term # InferChild k w)
            <&> (^. Lens._2)
            >>= newTerm . T.TFun
        <&> MkANode
        <&> (BLeaf leaf, )
    inferBody (BGetField (GetField w k)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild wI wT <- inferChild w
            _ <- T.TRecord wR & newTerm >>= unify (wT ^. _ANode)
            pure (BGetField (GetField wI k), MkANode rT)
    inferBody (BInject (Inject k p)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild pI pT <- inferChild p
            _ <- unify rT (pT ^. _ANode)
            newTerm (T.TVariant wR)
                <&> MkANode
                <&> (BInject (Inject k pI), )
    inferBody (BRecExtend (RowExtend k v r)) =
        do
            InferredChild vI vR <- inferChild v
            InferredChild rI rR <- inferChild r
            restR <-
                scopeConstraints (Proxy @T.Row) <&> T.rForbiddenFields . Lens.contains k .~ True
                >>= newVar binding . UUnbound
            _ <- T.TRecord restR & newTerm >>= unify (rR ^. _ANode)
            RowExtend k (vR ^. _ANode) restR & T.RExtend & newTerm
                >>= newTerm . T.TRecord
                <&> MkANode
                <&> (BRecExtend (RowExtend k vI rI), )
    inferBody (BCase (RowExtend tag handler rest)) =
        do
            InferredChild handlerI handlerT <- inferChild handler
            InferredChild restI restT <- inferChild rest
            fieldT <- newUnbound
            restR <- newUnbound
            result <- newUnbound
            _ <-
                FuncType fieldT result & T.TFun & newTerm
                >>= unify (handlerT ^. _ANode)
            restVarT <- T.TVariant restR & newTerm
            _ <-
                FuncType restVarT result & T.TFun & newTerm
                >>= unify (restT ^. _ANode)
            whole <- RowExtend tag fieldT restR & T.RExtend & newTerm >>= newTerm . T.TVariant
            FuncType whole result & T.TFun & newTerm
                <&> MkANode
                <&> (BCase (RowExtend tag handlerI restI), )

instance
    ( MonadNominals T.NominalId T.Type m
    , MonadScopeLevel m
    , TermVar.HasScope m Scope
    , UnifyGen m T.Type, UnifyGen m T.Row
    , LocalScopeType Var (UVarOf m # T.Type) m
    ) =>
    Blame m Term where
    inferOfUnify _ x y = () <$ unify (x ^. _ANode) (y ^. _ANode)
    inferOfMatches _ x y =
        (==)
        <$> (semiPruneLookup (x ^. _ANode) <&> fst)
        <*> (semiPruneLookup (y ^. _ANode) <&> fst)

-- Type synonym to ease the transition

type Val a = Ann (Const a) # Term

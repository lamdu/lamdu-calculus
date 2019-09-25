-- | Val AST
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, StandaloneDeriving, TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables, DerivingStrategies, DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Lamdu.Calc.Term
    ( Val
    , Leaf(..), _LVar, _LHole, _LLiteral, _LRecEmpty, _LAbsurd, _LFromNom
    , PrimVal(..), primType, primData
    , Term(..)
        , _BApp, _BLam, _BGetField, _BRecExtend
        , _BInject, _BCase, _BToNom, _BLeaf
    , App(..), appFunc, appArg
    , GetField(..), getFieldRecord, getFieldTag
    , Inject(..), injectVal, injectTag
    , Lam(..), lamIn, lamOut
    , Var(..)
    , Scope(..), scopeNominals, scopeVarTypes, scopeLevel
    , emptyScope
    , IResult(..), iType, iScope
    , ToNom(..), FromNom(..), RowExtend(..)
    , HWitness(..), HPlain(..)
    ) where

import           Hyper
import           Hyper.Type.Combinator.Flip (Flip, _Flip)
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
import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import           Data.Hashable (Hashable(..))
import           Data.Map (Map)
import           Data.Semigroup ((<>))
import           Data.String (IsString(..))
import           Generics.Constraints (makeDerivings, makeInstances)
import           GHC.Generics (Generic)
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
    { _getFieldRecord :: k # Term
    , _getFieldTag :: T.Tag
    } deriving Generic

data Inject k = Inject
    { _injectTag :: T.Tag
    , _injectVal :: k # Term
    } deriving Generic

data Term (k :: AHyperType)
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
makeHasHPlain [''Term]

instance RNodes Term
instance c Term => Recursively c Term
instance RTraversable Term

instance IsString (HPlain Term) where
    fromString = BLeafP . LVar . fromString

instance Pretty (f # Term) => Pretty (Term f) where
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
    , _scopeVarTypes :: Map Var (Tree (G.GTerm (GetHyperType v)) T.Type)
    , _scopeLevel :: ScopeLevel
    } deriving Generic
Lens.makeLenses ''Scope

instance HNodes Scope where
    data HWitness Scope n where
        KW_Scope_E0 :: HWitness (LoadedNominalDecl T.Type) n -> HWitness Scope n
        KW_Scope_E1 :: HWitness (Flip G.GTerm T.Type) n -> HWitness Scope n
    type HNodesConstraint Scope c = (Recursive c, c T.Type, c T.Row)
    kLiftConstraint (KW_Scope_E0 w) = kLiftConstraint w
    kLiftConstraint (KW_Scope_E1 w) = kLiftConstraint w

instance HFunctor Scope where
    mapK f (Scope n v l) =
        Scope
        (n <&> mapK (f . KW_Scope_E0))
        (v <&> Lens.from _Flip %~ mapK (f . KW_Scope_E1)) l

instance HFoldable Scope where
    foldMapK f (Scope n v _) =
        (n ^. Lens.folded . Lens.to (foldMapK (f . KW_Scope_E0))) <>
        (v ^. Lens.folded . Lens.from _Flip . Lens.to (foldMapK (f . KW_Scope_E1)))

instance HTraversable Scope where
    sequenceK (Scope n v l) =
        Scope
        <$> traverse sequenceK n
        <*> (traverse . Lens.from _Flip) sequenceK v
        ?? l

{-# INLINE emptyScope #-}
emptyScope :: Scope v
emptyScope = Scope mempty mempty (ScopeLevel 0)

data IResult v = IResult
    { _iScope :: Scope v
    , _iType :: v # T.Type
    }
Lens.makeLenses ''IResult
makeHTraversableAndBases ''IResult

instance HPointed IResult where
    pureK f = IResult emptyScope (f W_IResult_Type)

type instance TermVar.ScopeOf Term = Scope
type instance InferOf Term = IResult
instance HasInferredType Term where
    type instance TypeOf Term = T.Type
    inferredType _ = iType

makeDerivings [''Eq, ''Ord, ''Show] [''Term, ''Scope, ''GetField, ''Inject]
makeInstances [''Binary, ''NFData, ''Hashable] [''Term, ''Scope, ''GetField, ''Inject]

instance TermVar.VarType Var Term where
    {-# INLINE varType #-}
    varType _ v x = x ^?! scopeVarTypes . Lens.ix v & G.instantiate

mkResult ::
    (Functor m, TermVar.HasScope m Scope) =>
    m (Tree (UVarOf m) T.Type ->
    Tree IResult (UVarOf m))
mkResult = TermVar.getScope <&> IResult

instance
    ( MonadNominals T.NominalId T.Type m
    , MonadScopeLevel m
    , TermVar.HasScope m Scope
    , Unify m T.Type, Unify m T.Row
    , LocalScopeType Var (Tree (UVarOf m) T.Type) m
    ) =>
    Infer m Term where

    {-# INLINE inferBody #-}
    inferBody (BApp x) =
        do
            (xI, xT) <- inferBody x
            mkResult
                ?? xT ^. _ANode
                <&> (BApp xI, )
    inferBody (BLam x) =
        do
            (xI, xT) <- inferBody x
            mkResult
                <*> newTerm (T.TFun xT)
                <&> (BLam xI, )
    inferBody (BToNom x) =
        do
            (xI, xT) <- inferBody x
            mkResult
                <*> newTerm (T.TInst xT)
                <&> (BToNom xI, )
    inferBody (BLeaf leaf) =
        mkResult <*>
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
            inferBody (TermVar.Var x :: Tree (TermVar.Var Var Term) (InferChild k w))
            <&> (^. Lens._2 . _ANode)
        LFromNom x ->
            inferBody (FromNom x :: Tree (FromNom T.NominalId Term) (InferChild k w))
            <&> (^. Lens._2)
            >>= newTerm . T.TFun
        <&> (BLeaf leaf, )
    inferBody (BGetField (GetField w k)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild wI wT <- inferChild w
            _ <- T.TRecord wR & newTerm >>= unify (wT ^. iType)
            mkResult
                ?? rT
                <&> (BGetField (GetField wI k), )
    inferBody (BInject (Inject k p)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild pI pT <- inferChild p
            _ <- unify rT (pT ^. iType)
            mkResult
                <*> newTerm (T.TVariant wR)
                <&> (BInject (Inject k pI), )
    inferBody (BRecExtend (RowExtend k v r)) =
        do
            InferredChild vI vR <- inferChild v
            InferredChild rI rR <- inferChild r
            restR <-
                scopeConstraints <&> T.rForbiddenFields . Lens.contains k .~ True
                >>= newVar binding . UUnbound
            _ <- T.TRecord restR & newTerm >>= unify (rR ^. iType)
            mkResult
                <*> ( RowExtend k (vR ^. iType) restR & T.RExtend & newTerm
                        >>= newTerm . T.TRecord)
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
                >>= unify (handlerT ^. iType)
            restVarT <- T.TVariant restR & newTerm
            _ <-
                FuncType restVarT result & T.TFun & newTerm
                >>= unify (restT ^. iType)
            whole <- RowExtend tag fieldT restR & T.RExtend & newTerm >>= newTerm . T.TVariant
            mkResult
                <*> (FuncType whole result & T.TFun & newTerm)
                <&> (BCase (RowExtend tag handlerI restI), )

instance
    ( MonadNominals T.NominalId T.Type m
    , MonadScopeLevel m
    , TermVar.HasScope m Scope
    , Unify m T.Type, Unify m T.Row
    , LocalScopeType Var (Tree (UVarOf m) T.Type) m
    ) =>
    Blame m Term where
    inferOfUnify _ x y = () <$ unify (x ^. iType) (y ^. iType)
    inferOfMatches _ x y =
        (==)
        <$> (semiPruneLookup (x ^. iType) <&> fst)
        <*> (semiPruneLookup (y ^. iType) <&> fst)

-- Type synonym to ease the transition

type Val a = Tree (Ann a) Term

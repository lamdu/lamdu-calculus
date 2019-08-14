-- | Val AST
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables, DerivingStrategies #-}

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
    ) where

import           AST
import           AST.Infer
import           AST.Term.App (App(..), appFunc, appArg)
import           AST.Term.FuncType (FuncType(..))
import           AST.Term.Lam (Lam(..), lamIn, lamOut)
import           AST.Term.Nominal (ToNom(..), FromNom(..), NominalInst(..), MonadNominals, LoadedNominalDecl)
import           AST.Term.Row (RowExtend(..), rowElementInfer)
import           AST.Term.Scheme (QVarInstances(..))
import qualified AST.Term.Var as TermVar
import           AST.Unify
import qualified AST.Unify.Generalize as G
import           AST.Unify.New (newTerm, newUnbound)
import           AST.Unify.Term (UTerm(..))
import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import           Data.Constraint (Constraint, withDict)
import           Data.Hashable (Hashable(..))
import           Data.Map (Map)
import           Data.Semigroup ((<>))
import           Data.String (IsString(..))
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

data GetField exp = GetField
    { _getFieldRecord :: exp
    , _getFieldTag :: T.Tag
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq, Ord)
instance NFData exp => NFData (GetField exp)
instance Binary exp => Binary (GetField exp)
instance Hashable exp => Hashable (GetField exp)

Lens.makeLenses ''GetField

data Inject exp = Inject
    { _injectTag :: T.Tag
    , _injectVal :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq, Ord)
instance NFData exp => NFData (Inject exp)
instance Binary exp => Binary (Inject exp)
instance Hashable exp => Hashable (Inject exp)

Lens.makeLenses ''Inject

data Term k
    = BApp {-# UNPACK #-}!(App Term k)
    | BLam {-# UNPACK #-}!(Lam Var Term k)
    | BGetField {-# UNPACK #-}!(GetField (Node k Term))
    | BRecExtend {-# UNPACK #-}!(RowExtend T.Tag Term Term k)
    | BInject {-# UNPACK #-}!(Inject (Node k Term))
    | BCase {-# UNPACK #-}!(RowExtend T.Tag Term Term k)
    | -- Convert to Nominal type
      BToNom {-# UNPACK #-}!(ToNom T.NominalId Term k)
    | BLeaf Leaf
    deriving Generic

-- NOTE: Careful of Eq, it's not alpha-eq!
deriving instance Eq   (Node f Term) => Eq   (Term f)
deriving instance Ord  (Node f Term) => Ord  (Term f)
deriving instance Show (Node f Term) => Show (Term f)
instance Binary (Node f Term) => Binary (Term f)

instance KNodes Term where
    type NodeTypesOf Term = ANode Term

Lens.makePrisms ''Term
makeKTraversableAndBases ''Term

instance c Term => Recursively c Term

instance Pretty (Node f Term) => Pretty (Term f) where
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
    , _scopeVarTypes :: Map Var (Tree (G.GTerm (RunKnot v)) T.Type)
    , _scopeLevel :: ScopeLevel
    }
Lens.makeLenses ''Scope

emptyScope :: Scope v
emptyScope = Scope mempty mempty (ScopeLevel 0)

data IResult v = IResult
    { _iScope :: Maybe (Scope v)
    , _iType :: Node v T.Type
    }
Lens.makeLenses ''IResult

type instance TermVar.ScopeOf Term = Scope
type instance TypeOf Term = T.Type
type instance InferOf Term = IResult
instance HasInferredType Term where inferredType _ = iType

type ScopeDeps c v =
    ((c (Node v T.Type), c (Node v T.Row)) :: Constraint)
deriving instance ScopeDeps Eq   v => Eq   (Scope v)
deriving instance ScopeDeps Ord  v => Ord  (Scope v)
deriving instance ScopeDeps Show v => Show (Scope v)

instance TermVar.VarType Var Term where
    {-# INLINE varType #-}
    varType _ v x = x ^?! scopeVarTypes . Lens.ix v & G.instantiate

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
        inferBody x <&>
        \(InferRes xI xT) ->
        IResult Nothing (xT ^. _ANode) & InferRes (BApp xI)
    inferBody (BLam x) =
        do
            InferRes xI xT <- inferBody x
            T.TFun xT & newTerm
                <&> IResult Nothing
                <&> InferRes (BLam xI)
    inferBody (BToNom x) =
        do
            InferRes xI xT <- inferBody x
            T.TInst xT & newTerm
                <&> IResult Nothing
                <&> InferRes (BToNom xI)
    inferBody (BLeaf leaf) =
        case leaf of
        LHole ->
            IResult
            <$> (TermVar.getScope <&> Just)
            <*> newUnbound
            <&> InferRes (BLeaf LHole)
        LRecEmpty -> newTerm T.REmpty >>= newTerm . T.TRecord <&> r
        LAbsurd ->
            FuncType
            <$> (newTerm T.REmpty >>= newTerm . T.TVariant)
            <*> newUnbound
            >>= newTerm . T.TFun
            <&> r
        LLiteral (PrimVal t _) ->
            T.Types (QVarInstances mempty) (QVarInstances mempty)
            & NominalInst t
            & T.TInst & newTerm
            <&> r
        LVar x ->
            inferBody (TermVar.Var x :: Tree (TermVar.Var Var Term) (InferChild k w))
            <&> (^. inferResVal . _ANode)
            <&> r
        LFromNom x ->
            inferBody (FromNom x :: Tree (FromNom T.NominalId Term) (InferChild k w))
            <&> (^. inferResVal)
            >>= newTerm . T.TFun
            <&> r
        where
            r = InferRes (BLeaf leaf) . IResult Nothing
    inferBody (BGetField (GetField w k)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild wI wT <- inferChild w
            _ <- T.TRecord wR & newTerm >>= unify (wT ^. iType)
            IResult Nothing rT
                & InferRes (BGetField (GetField wI k))
                & pure
    inferBody (BInject (Inject k p)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild pI pT <- inferChild p
            _ <- unify rT (pT ^. iType)
            T.TVariant wR & newTerm
                <&> IResult Nothing
                <&> InferRes (BInject (Inject k pI))
    inferBody (BRecExtend (RowExtend k v r)) =
        withDict (recursive :: RecursiveDict T.Type (Unify m)) $
        do
            InferredChild vI vR <- inferChild v
            InferredChild rI rR <- inferChild r
            restR <-
                scopeConstraints <&> T.rForbiddenFields . Lens.contains k .~ True
                >>= newVar binding . UUnbound
            _ <- T.TRecord restR & newTerm >>= unify (rR ^. iType)
            RowExtend k (vR ^. iType) restR & T.RExtend & newTerm
                >>= newTerm . T.TRecord
                <&> IResult Nothing
                <&> InferRes (BRecExtend (RowExtend k vI rI))
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
            FuncType whole result & T.TFun & newTerm
                <&> IResult Nothing
                <&> InferRes (BCase (RowExtend tag handlerI restI))

-- Type synonym to ease the transition

type Val a = Tree (Ann a) Term

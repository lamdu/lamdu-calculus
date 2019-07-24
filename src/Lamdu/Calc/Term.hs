-- | Val AST
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables #-}

module Lamdu.Calc.Term
    ( Val
    , Leaf(..), _LVar, _LHole, _LLiteral, _LRecEmpty, _LAbsurd, _LFromNom
    , PrimVal(..), primType, primData
    , Term(..)
        , _BApp, _BLam, _BGetField, _BRecExtend
        , _BInject, _BCase, _BToNom, _BLeaf
    , Apply(..), applyFunc, applyArg
    , GetField(..), getFieldRecord, getFieldTag
    , Inject(..), injectVal, injectTag
    , Lam(..), lamIn, lamOut
    , Var(..)
    , Scope(..), scopeNominals, scopeVarTypes, scopeLevel
    , emptyScope
    , ToNom(..), FromNom(..), RowExtend(..)
    ) where

import           AST
import           AST.Combinator.Single
import           AST.Infer
import           AST.Term.Apply (Apply(..), applyFunc, applyArg)
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
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

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
    = BApp {-# UNPACK #-}!(Apply Term k)
    | BLam {-# UNPACK #-}!(Lam Var Term k)
    | BGetField {-# UNPACK #-}!(GetField (Tie k Term))
    | BRecExtend {-# UNPACK #-}!(RowExtend T.Tag Term Term k)
    | BInject {-# UNPACK #-}!(Inject (Tie k Term))
    | BCase {-# UNPACK #-}!(RowExtend T.Tag Term Term k)
    | -- Convert to Nominal type
      BToNom {-# UNPACK #-}!(ToNom T.NominalId Term k)
    | BLeaf Leaf
    deriving Generic

-- NOTE: Careful of Eq, it's not alpha-eq!
deriving instance Eq   (Tie f Term) => Eq   (Term f)
deriving instance Ord  (Tie f Term) => Ord  (Term f)
deriving instance Show (Tie f Term) => Show (Term f)
instance Binary (Tie f Term) => Binary (Term f)

Lens.makePrisms ''Term
makeChildren ''Term

type instance ChildrenTypesOf Term = Single Term
instance HasChildrenTypes Term
makeKTraversableAndBases ''Term

instance c Term => Recursive c Term

instance Pretty (Tie f Term) => Pretty (Term f) where
    pPrintPrec lvl prec b =
        case b of
        BLeaf (LVar var)          -> pPrint var
        BLeaf (LLiteral (PrimVal _p d)) -> PP.text (BS8.unpack d)
        BLeaf LHole               -> PP.text "?"
        BLeaf LAbsurd             -> PP.text "absurd"
        BLeaf (LFromNom ident)    -> PP.text "[" <+> PP.text "unpack" <+> pPrint ident <+> PP.text "]"
        BApp (Apply e1 e2)        -> maybeParens (10 < prec) $
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

type instance ScopeOf Term = Scope
type instance TypeOf Term = T.Type

type ScopeDeps c v =
    ((c (Tie v T.Type), c (Tie v T.Row)) :: Constraint)
deriving instance ScopeDeps Eq   v => Eq   (Scope v)
deriving instance ScopeDeps Ord  v => Ord  (Scope v)
deriving instance ScopeDeps Show v => Show (Scope v)

instance TermVar.VarType Var Term where
    {-# INLINE varType #-}
    varType _ v x = x ^?! scopeVarTypes . Lens.ix v & G.instantiate

instance
    ( MonadNominals T.NominalId T.Type m
    , MonadScopeLevel m
    , HasScope m Scope
    , Unify m T.Type, Unify m T.Row
    , LocalScopeType Var (Tree (UVarOf m) T.Type) m
    ) =>
    Infer m Term where

    {-# INLINE inferBody #-}
    inferBody (BApp x) = inferBody x <&> inferResBody %~ BApp
    inferBody (BLam x) = inferBody x <&> inferResBody %~ BLam
    inferBody (BToNom x) = inferBody x <&> inferResBody %~ BToNom
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
            inferBody (TermVar.Var x :: Tree (TermVar.Var Var Term) (InferChild k w))
            <&> (^. inferResType)
        LFromNom x ->
            inferBody (FromNom x :: Tree (FromNom T.NominalId Term) (InferChild k w))
            <&> (^. inferResType)
        <&> InferRes (BLeaf leaf)
    inferBody (BGetField (GetField w k)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild wI wT <- inferChild w
            _ <- T.TRecord wR & newTerm >>= unify wT
            InferRes (BGetField (GetField wI k)) rT & pure
    inferBody (BInject (Inject k p)) =
        do
            (rT, wR) <- rowElementInfer T.RExtend k
            InferredChild pI pT <- inferChild p
            _ <- unify rT pT
            T.TVariant wR & newTerm <&> InferRes (BInject (Inject k pI))
    inferBody (BRecExtend (RowExtend k v r)) =
        withDict (recursive :: RecursiveDict (Unify m) T.Type) $
        do
            InferredChild vI vT <- inferChild v
            InferredChild rI rT <- inferChild r
            restR <-
                scopeConstraints <&> T.rForbiddenFields . Lens.contains k .~ True
                >>= newVar binding . UUnbound
            _ <- T.TRecord restR & newTerm >>= unify rT
            RowExtend k vT restR & T.RExtend & newTerm
                >>= newTerm . T.TRecord
                <&> InferRes (BRecExtend (RowExtend k vI rI))
    inferBody (BCase (RowExtend tag handler rest)) =
        do
            InferredChild handlerI handlerT <- inferChild handler
            InferredChild restI restT <- inferChild rest
            fieldT <- newUnbound
            restR <- newUnbound
            result <- newUnbound
            _ <- FuncType fieldT result & T.TFun & newTerm >>= unify handlerT
            restVarT <- T.TVariant restR & newTerm
            _ <- FuncType restVarT result & T.TFun & newTerm >>= unify restT
            whole <- RowExtend tag fieldT restR & T.RExtend & newTerm >>= newTerm . T.TVariant
            FuncType whole result & T.TFun & newTerm
                <&> InferRes (BCase (RowExtend tag handlerI restI))

-- Type synonym to ease the transition

type Val a = Tree (Ann a) Term

-- | The Lamdu Calculus type AST.
--
-- The Lamdu Calculus type system includes the set of types that can
-- be expressed via the AST elements in this module.
--
-- The Lamdu Calculus type AST is actually 2 different ASTs:
--
-- * The AST for structural composite types (records, variants). The kinds of
--   composite are differentiated via a phantom type-level tag
--
-- * The AST for types: Nominal types, structural composite types,
--   function types.
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving, TypeApplications #-}
{-# LANGUAGE TemplateHaskell, DataKinds, StandaloneDeriving, DerivingVia, TypeOperators #-}
{-# LANGUAGE UndecidableInstances, ConstraintKinds, FlexibleContexts, GADTs, TupleSections #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies, MultiParamTypeClasses, RankNTypes #-}

module Lamdu.Calc.Type
    (
    -- * Type Variable kinds
      RowVar, TypeVar
    -- * Typed identifiers of the Type AST
    , Var(..), NominalId(..), Tag(..)
    -- * Rows
    , Row(..), W_Row(..)
    -- * Row Prisms
    , _RExtend, _REmpty, _RVar
    -- * Type AST
    , Type(..), W_Type(..)
    , Scheme, Nominal
    , (~>)
    -- * Type Prisms
    , _Var
    , _TVar, _TFun, _TInst, _TRecord, _TVariant
    -- TODO: describe
    , Types(..), W_Types(..), tType, tRow
    , RConstraints(..), rForbiddenFields, rScope
    , rStructureMismatch

    , TypeError(..), _TypeError, _RowError

    , flatRow

    , HPlain(..)
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import qualified Control.Lens as Lens
import           Generic.Data (Generically(..))
import           Generics.Constraints (makeDerivings, makeInstances)
import           Hyper
import           Hyper.Class.Optic (HNodeLens(..), HSubset(..))
import           Hyper.Infer
import           Hyper.Infer.Blame (Blame(..))
import           Hyper.Syntax hiding (Var, _Var)
import           Hyper.Syntax.Nominal
import           Hyper.Syntax.Row
import qualified Hyper.Syntax.Scheme as S
import           Hyper.Unify
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..))
import           Lamdu.Calc.Identifier (Identifier)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Lamdu.Calc.Internal.Prelude

-- | A type varible of some kind ('Var' 'Type', 'Var' 'Variant', or 'Var' 'Record')
newtype Var (t :: HyperType) = Var { tvName :: Identifier }
    deriving stock Show
    deriving newtype (Eq, Ord, NFData, IsString, Pretty, Binary, Hashable)

-- | An identifier for a nominal type
newtype NominalId = NominalId { nomId :: Identifier }
    deriving stock Show
    deriving newtype (Eq, Ord, NFData, IsString, Pretty, Binary, Hashable)

-- | An identifier for a component in a variant type (aka data
-- constructor) or a component(field) in a record
newtype Tag = Tag { tagName :: Identifier }
    deriving stock Show
    deriving newtype (Eq, Ord, NFData, IsString, Pretty, Binary, Hashable)

-- | A row type variable that represents a set of
-- typed fields in a row
type RowVar = Var Row

-- | A type variable that represents a type
type TypeVar = Var Type

-- | The AST for rows (records, variants) For
-- example: RExtend "a" int (RExtend "b" bool (RVar "c")) represents
-- the composite type:
-- > { a : int, b : bool | c }
data Row k
    = RExtend (RowExtend Tag Type Row k)
      -- ^ Extend a row type with an extra component (field /
      -- data constructor).
    | REmpty
      -- ^ The empty row type (empty record [unit] or empty variant [void])
    | RVar RowVar
      -- ^ A row type variable
    deriving Generic

-- | The AST for any Lamdu Calculus type
data Type k
    = TVar TypeVar
      -- ^ A type variable
    | TFun (FuncType Type k)
      -- ^ A (non-dependent) function of the given parameter and result types
    | TInst (NominalInst NominalId Types k)
      -- ^ An instantiation of a nominal type of the given id with the
      -- given keyword type arguments
    | TRecord (k :# Row)
      -- ^ Lifts a composite record type
    | TVariant (k :# Row)
      -- ^ Lifts a composite variant type
    deriving Generic

data Types k = Types
    { _tType :: k :# Type
    , _tRow :: k :# Row
    } deriving Generic

data RConstraints = RowConstraints
    { _rForbiddenFields :: Set Tag
    , _rScope :: ScopeLevel
    } deriving (Generic, Eq, Ord, Show)
    deriving (Semigroup, Monoid) via Generically RConstraints

data TypeError k
    = TypeError (UnifyError Type k)
    | RowError (UnifyError Row k)
    | NominalNotFound NominalId
    deriving Generic

Lens.makeLenses ''RConstraints
Lens.makeLenses ''Types
Lens.makePrisms ''Row
Lens.makePrisms ''Type
Lens.makePrisms ''TypeError
Lens.makePrisms ''Var

makeHTraversableApplyAndBases ''Types
makeHTraversableAndBases ''Row
makeHTraversableAndBases ''Type
makeZipMatch ''Row
makeZipMatch ''Type
makeZipMatch ''Types
makeHContext ''Row
makeHContext ''Type
makeHContext ''Types
instance RNodes Row
instance RNodes Type
instance (c Type, c Row) => Recursively c Type
instance (c Type, c Row) => Recursively c Row
instance RTraversable Row
instance RTraversable Type

type Nominal = NominalInst NominalId Types
type Scheme = S.Scheme Types Type

instance HNodeLens Types Type where
    {-# INLINE hNodeLens #-}
    hNodeLens = tType

instance HNodeLens Types Row where
    {-# INLINE hNodeLens #-}
    hNodeLens = tRow

instance (UnifyGen m Type, UnifyGen m Row) => S.HasScheme Types m Type
instance (UnifyGen m Type, UnifyGen m Row) => S.HasScheme Types m Row

-- | A convenience infix alias for 'TFun'
infixr 2 ~>
(~>) :: Pure # Type -> Pure # Type -> Pure # Type
x ~> y = _Pure # TFun (FuncType x y)

type Deps c k = ((c (k :# Type), c (k :# Row)) :: Constraint)

instance Deps Pretty k => Pretty (Type k) where
    pPrintPrec lvl prec typ =
        case typ of
        TVar n -> pPrint n
        TInst n -> pPrint n
        TFun (FuncType t s) ->
            maybeParens (8 < prec) $
            pPrintPrec lvl 9 t <+> PP.text "->" <+> pPrintPrec lvl 8 s
        TRecord r -> PP.text "*" <> pPrint r
        TVariant s -> PP.text "+" <> pPrint s

instance Pretty (Row # Pure) where
    pPrint REmpty = PP.text "{}"
    pPrint x =
        PP.text "{" <+> go PP.empty x <+> PP.text "}"
        where
            go _   REmpty = PP.empty
            go sep (RVar tv) = sep <> pPrint tv <> PP.text "..."
            go sep (RExtend (RowExtend f t r)) =
                sep PP.<> pPrint f <+> PP.text ":" <+> pPrint t PP.<> go (PP.text ", ") (r ^. _Pure)

instance Deps Pretty k => Pretty (Types k) where
    pPrint (Types t r) = PP.text "{" <+> pPrint t <+> PP.text "|" <+> pPrint r <+> PP.text "}"

instance Pretty RConstraints where
    pPrint (RowConstraints tags level) =
        pPrint (tags ^.. Lens.folded) PP.<+>
        (PP.text "(" <> pPrint level <> PP.text ")")

instance Pretty (TypeError # Pure) where
    pPrint (TypeError x) = pPrint x
    pPrint (RowError x) = pPrint x
    pPrint (NominalNotFound x) = PP.text "Nominal not found:" <+> pPrint x

type instance NomVarTypes Type = Types

instance HSubset Type Type (FuncType Type) (FuncType Type) where
    {-# INLINE hSubset #-}
    hSubset = _TFun

instance HasNominalInst NominalId Type where
    {-# INLINE nominalInst #-}
    nominalInst = _TInst

instance HasQuantifiedVar Type where
    type QVar Type = TypeVar
    quantifiedVar = _TVar

instance HasQuantifiedVar Row where
    type QVar Row = RowVar
    quantifiedVar = _RVar

instance HasTypeConstraints Type where
    type instance TypeConstraintsOf Type = ScopeLevel
    {-# INLINE verifyConstraints #-}
    verifyConstraints _ (TVar x) = TVar x & Just
    verifyConstraints c (TFun x) = x & hmapped1 %~ WithConstraint c & TFun & Just
    verifyConstraints c (TRecord x) =
        WithConstraint (RowConstraints mempty c) x & TRecord & Just
    verifyConstraints c (TVariant x) =
        WithConstraint (RowConstraints mempty c) x & TVariant & Just
    verifyConstraints c (TInst (NominalInst n (Types t r))) =
        Types
        (t & S._QVarInstances . traverse %~ WithConstraint c)
        (r & S._QVarInstances . traverse %~ WithConstraint (RowConstraints mempty c))
        & NominalInst n & TInst & Just

instance HasTypeConstraints Row where
    type instance TypeConstraintsOf Row = RConstraints
    {-# INLINE verifyConstraints #-}
    verifyConstraints _ REmpty = Just REmpty
    verifyConstraints _ (RVar x) = RVar x & Just
    verifyConstraints c (RExtend x) = verifyRowExtendConstraints (^. rScope) c x <&> RExtend

instance TypeConstraints RConstraints where
    {-# INLINE generalizeConstraints #-}
    generalizeConstraints = rScope .~ mempty
    toScopeConstraints = rForbiddenFields .~ mempty

instance RowConstraints RConstraints where
    type RowConstraintsKey RConstraints = Tag
    {-# INLINE forbidden #-}
    forbidden = rForbiddenFields

instance PartialOrd RConstraints where
    {-# INLINE leq #-}
    RowConstraints f0 s0 `leq` RowConstraints f1 s1 = f0 `leq` f1 && s0 `leq` s1

type instance InferOf Type = ANode Type
type instance InferOf Row = ANode Row
instance HasInferredValue Type where inferredValue = _ANode
instance HasInferredValue Row where inferredValue = _ANode

instance (Monad m, UnifyGen m Type, UnifyGen m Row) => Infer m Type where
    inferBody x =
        do
            xI <- htraverse (const inferChild) x
            hmap (Proxy @HasInferredValue #> (^. inType . inferredValue)) xI
                & newTerm
                <&> (hmap (const (^. inRep)) xI, ) . MkANode

instance (Monad m, UnifyGen m Type, UnifyGen m Row) => Infer m Row where
    inferBody x =
        do
            xI <- htraverse (const inferChild) x
            hmap (Proxy @HasInferredValue #> (^. inType . inferredValue)) xI
                & newTerm
                <&> (hmap (const (^. inRep)) xI, ) . MkANode

instance (UnifyGen m Type, UnifyGen m Row) => Blame m Row where
    inferOfUnify _ x y = unify (x ^. _ANode) (y ^. _ANode) & void
    inferOfMatches _ x y =
        (==)
        <$> (semiPruneLookup (x ^. _ANode) <&> fst)
        <*> (semiPruneLookup (y ^. _ANode) <&> fst)

instance (UnifyGen m Type, UnifyGen m Row) => Blame m Type where
    inferOfUnify _ x y = unify (x ^. _ANode) (y ^. _ANode) & void
    inferOfMatches _ x y =
        (==)
        <$> (semiPruneLookup (x ^. _ANode) <&> fst)
        <*> (semiPruneLookup (y ^. _ANode) <&> fst)

{-# INLINE rStructureMismatch #-}
rStructureMismatch ::
    (Unify m Type, Unify m Row) =>
    (forall c. Unify m c => UVarOf m # c -> UVarOf m # c -> m (UVarOf m # c)) ->
    Row # UVarOf m ->
    Row # UVarOf m ->
    m ()
rStructureMismatch f (RExtend r0) (RExtend r1) =
    rowExtendStructureMismatch f _RExtend r0 r1
rStructureMismatch _ x y = Mismatch x y & unifyError

flatRow :: Lens.Iso' (Pure # Row) (FlatRowExtends Tag Type Row # Pure)
flatRow =
    Lens.iso flatten unflatten
    where
        flatten =
            Lens.runIdentity .
            flattenRow (Lens.Identity . (^? _Pure . _RExtend))
        unflatten =
            Lens.runIdentity .
            unflattenRow (Lens.Identity . (_Pure . _RExtend #))

makeDerivings [''Eq, ''Ord, ''Show] [''Row, ''Type, ''Types, ''TypeError]
makeInstances [''Binary, ''NFData] [''Row, ''Type, ''Types, ''TypeError]

makeHasHPlain [''Type, ''Row, ''Types]

instance NFData RConstraints
instance Binary RConstraints

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
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell, DataKinds, StandaloneDeriving, DerivingVia #-}
{-# LANGUAGE UndecidableInstances, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies, MultiParamTypeClasses, RankNTypes #-}

module Lamdu.Calc.Type
    (
    -- * Type Variable kinds
      RowVar, TypeVar
    -- * Typed identifiers of the Type AST
    , Var(..), NominalId(..), Tag(..)
    -- * Rows
    , Row(..)
    -- * Row Prisms
    , _RExtend, _REmpty, _RVar
    -- * Type AST
    , Type(..)
    , Scheme, Nominal
    , (~>)
    -- * Type Prisms
    , _TVar, _TFun, _TInst, _TRecord, _TVariant
    -- TODO: describe
    , Types(..), tType, tRow
    , RConstraints(..), rForbiddenFields, rScope
    , rStructureMismatch

    , TypeError(..), _TypeError, _RowError

    , flatRow
    ) where

import           AST
import           AST.Class.Has
import           AST.Infer
import           AST.Term.FuncType
import           AST.Term.Nominal
import           AST.Term.Row
import qualified AST.Term.Scheme as S
import           AST.Unify
import           AST.Unify.QuantifiedVar
import           AST.Unify.Term
import           Algebra.PartialOrd
import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Hashable (Hashable)
import           Data.Semigroup ((<>))
import           Data.Set (Set, singleton)
import           Data.String (IsString(..))
import           GHC.Exts (Constraint)
import           GHC.Generics (Generic)
import           Generic.Data (Generically(..))
import           Lamdu.Calc.Identifier (Identifier)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A type varible of some kind ('Var' 'Type', 'Var' 'Variant', or 'Var' 'Record')
newtype Var (t :: Knot -> *) = Var { tvName :: Identifier }
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
    | TRecord (Node k Row)
      -- ^ Lifts a composite record type
    | TVariant (Node k Row)
      -- ^ Lifts a composite variant type
    deriving Generic

data Types k = Types
    { _tType :: Node k Type
    , _tRow :: Node k Row
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

instance KNodes Types where
    type NodeTypesOf Types = Types
    type NodesConstraint Types = ConcatConstraintFuncs '[On Type, On Row]
instance KNodes Type where type NodeTypesOf Type = Types
instance KNodes Row  where type NodeTypesOf Row  = Types

instance KHas (ANode Type) Types where hasK (Types t _) = MkANode t
instance KHas (Product (ANode Type) (ANode Row)) Types where
    hasK (Types t r) = Pair (MkANode t) (MkANode r)

makeKApplicativeBases ''Types
makeKTraversableAndFoldable ''Types
makeKTraversableAndBases ''Row
makeKTraversableAndBases ''Type
makeZipMatch ''Row
makeZipMatch ''Type
makeZipMatch ''Types

type Nominal = NominalInst NominalId Types
type Scheme = S.Scheme Types Type

instance HasChild Types Type where
    {-# INLINE getChild #-}
    getChild = tType

instance HasChild Types Row where
    {-# INLINE getChild #-}
    getChild = tRow

-- | A convenience infix alias for 'TFun'
infixr 2 ~>
(~>) :: Tree Pure Type -> Tree Pure Type -> Tree Pure Type
x ~> y = _Pure # TFun (FuncType x y)

type Deps c k = ((c (Node k Type), c (Node k Row)) :: Constraint)

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

instance Pretty (Tree Row Pure) where
    pPrint REmpty = PP.text "{}"
    pPrint x =
        PP.text "{" <+> go PP.empty x <+> PP.text "}"
        where
            go _   REmpty = PP.empty
            go sep (RVar tv) = sep <> pPrint tv <> PP.text "..."
            go sep (RExtend (RowExtend f t (MkPure r))) =
                sep PP.<> pPrint f <+> PP.text ":" <+> pPrint t PP.<> go (PP.text ", ") r

instance Deps Pretty k => Pretty (Types k) where
    pPrint (Types t r) = PP.text "{" <+> pPrint t <+> PP.text "|" <+> pPrint r <+> PP.text "}"

instance Pretty RConstraints where
    pPrint (RowConstraints tags level) =
        pPrint (tags ^.. Lens.folded) <+>
        (PP.text "(" <> pPrint level <> PP.text ")")

instance Pretty (Tree TypeError Pure) where
    pPrint (TypeError x) = pPrint x
    pPrint (RowError x) = pPrint x
    pPrint (NominalNotFound x) = PP.text "Nominal not found:" <+> pPrint x

type instance NomVarTypes Type = Types

instance (c Type, c Row) => Recursively c Type
instance (c Type, c Row) => Recursively c Row

instance HasFuncType Type where
    {-# INLINE funcType #-}
    funcType = _TFun

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
    type TypeConstraintsOf Type = ScopeLevel
    {-# INLINE verifyConstraints #-}
    verifyConstraints _ _ _ _ (TVar x) = TVar x & pure
    verifyConstraints _ c _ u (TFun x) = traverseK1 (u c) x <&> TFun
    verifyConstraints _ c _ u (TRecord x) = u (RowConstraints mempty c) x <&> TRecord
    verifyConstraints _ c _ u (TVariant x) = u (RowConstraints mempty c) x <&> TVariant
    verifyConstraints _ c _ u (TInst (NominalInst n (Types t r))) =
        Types
        <$> (S._QVarInstances . traverse) (u c) t
        <*> (S._QVarInstances . traverse) (u (RowConstraints mempty c)) r
        <&> NominalInst n <&> TInst

instance HasTypeConstraints Row where
    type TypeConstraintsOf Row = RConstraints
    {-# INLINE verifyConstraints #-}
    verifyConstraints _ _ _ _ REmpty = pure REmpty
    verifyConstraints _ _ _ _ (RVar x) = RVar x & pure
    verifyConstraints p c e u (RExtend x) =
        applyRowExtendConstraints p c (^. rScope)
        (e . (`RowConstraints` mempty) . singleton) u x
        <&> RExtend

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

{-# INLINE rStructureMismatch #-}
rStructureMismatch ::
    (Unify m Type, Unify m Row) =>
    (forall c. Recursively (Unify m) c => Tree (UVarOf m) c -> Tree (UVarOf m) c -> m (Tree (UVarOf m) c)) ->
    Tree (UTermBody (UVarOf m)) Row ->
    Tree (UTermBody (UVarOf m)) Row ->
    m ()
rStructureMismatch f (UTermBody c0 (RExtend r0)) (UTermBody c1 (RExtend r1)) =
    rowExtendStructureMismatch f _RExtend (c0, r0) (c1, r1)
rStructureMismatch _ x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))

flatRow ::
    Lens.Iso'
    (Tree Pure Row)
    (Tree (FlatRowExtends Tag Type Row) Pure)
flatRow =
    Lens.iso flatten unflatten
    where
        flatten =
            Lens.runIdentity .
            flattenRow (Lens.Identity . (^? _Pure . _RExtend))
        unflatten =
            Lens.runIdentity .
            unflattenRow (Lens.Identity . (_Pure . _RExtend #))

deriving instance Deps Eq   k => Eq   (Row k)
deriving instance Deps Ord  k => Ord  (Row k)
deriving instance Deps Show k => Show (Row k)
instance Deps NFData k => NFData (Row k)
instance Deps Binary k => Binary (Row k)

deriving instance Deps Eq   k => Eq   (Type k)
deriving instance Deps Ord  k => Ord  (Type k)
deriving instance Deps Show k => Show (Type k)
instance Deps NFData k => NFData (Type k)
instance Deps Binary k => Binary (Type k)

deriving instance Deps Eq   k => Eq   (Types k)
deriving instance Deps Ord  k => Ord  (Types k)
deriving instance Deps Show k => Show (Types k)
instance Deps NFData k => NFData (Types k)
instance Deps Binary k => Binary (Types k)

deriving instance Deps Eq   k => Eq   (TypeError k)
deriving instance Deps Show k => Show (TypeError k)
instance Deps NFData k => NFData (TypeError k)
instance Deps Binary k => Binary (TypeError k)

instance NFData RConstraints
instance Binary RConstraints

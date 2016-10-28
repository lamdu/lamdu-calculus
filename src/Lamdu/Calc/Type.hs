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
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, EmptyDataDecls, GeneralizedNewtypeDeriving, OverloadedStrings, TemplateHaskell #-}
module Lamdu.Calc.Type
    (
    -- * Type Variable kinds
      ProductTag, SumTag
    , ProductVar, SumVar, TypeVar
    , Product   , Sum
    -- * Typed identifiers of the Type AST
    , Var(..), NominalId(..), Tag(..), ParamId(..)
    -- * Composites
    , Composite(..)
    -- * Composite Prisms
    , _CExtend, _CEmpty, _CVar
    -- * Type AST
    , Type(..)
    , (~>)
    -- * Type Prisms
    , _TVar, _TFun, _TInst, _TRecord, _TSum
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Hashable (Hashable)
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import           Lamdu.Calc.Identifier (Identifier)
import           Text.PrettyPrint ((<+>), (<>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A type varible of some kind ('Var' 'Type', 'Var' 'Sum', or 'Var' 'Product')
newtype Var t = Var { tvName :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | An identifier for a nominal type
newtype NominalId = NominalId { nomId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | An identifier for a component in a sum type (aka data
-- constructor) or a component in a product type (aka record field)
newtype Tag = Tag { tagName :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | In Lamdu Calculus, all type parameters are named (keyword
-- arguments), this is the type of the type parameter names.
newtype ParamId = ParamId { typeParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | This is a type-level tag used to tag composites as products
-- (records) in the type-level. It is not used as the type of values.
data ProductTag

-- | This is a type-level tag used to tag composites as sums
-- (variants) in the type-level. It is not used as the type of values.
data SumTag

-- | The AST type for product types (records)
type Product = Composite ProductTag

-- | The AST type for sum types (variants)
type Sum = Composite SumTag

-- | A row type variable (of kind 'Product') that represents a set of
-- typed fields in a record
type ProductVar = Var Product

-- | A column type variable (of kind 'Sum') that represents a set of
-- typed data constructors in a variant
type SumVar = Var Sum

-- | A type variable that represents a type
type TypeVar = Var Type

-- | The AST for extensible composite types (records, variants) For
-- example: CExtend "a" int (CExtend "b" bool (CVar "c")) represents
-- the composite type:
-- > { a : int, b : bool | c }
-- This composite type can be a record or variant, depending on the
-- phantom type tag ('ProductTag' or 'SumTag')
data Composite p
    = CExtend Tag Type (Composite p)
      -- ^ Extend a composite type with an extra component (field /
      -- data constructor).
    | CEmpty
      -- ^ The empty composite type (empty record [unit] or empty variant [void])
    | CVar (Var (Composite p))
      -- ^ A row/column type variable (represents some unknown
      -- composite of the same kind)
    deriving (Generic, Show, Eq, Ord)
instance NFData (Composite p)
instance Binary (Composite p)

-- | The AST for any Lamdu Calculus type
data Type
    = TVar TypeVar
      -- ^ A type variable
    | TFun Type Type
      -- ^ A (non-dependent) function of the given parameter and result types
    | TInst NominalId (Map ParamId Type)
      -- ^ An instantiation of a nominal type of the given id with the
      -- given keyword type arguments
    | TRecord Product
      -- ^ Lifts a composite record type
    | TSum Sum
      -- ^ Lifts a composite variant type
    deriving (Generic, Show, Eq, Ord)
instance NFData Type
instance Binary Type

Lens.makePrisms ''Composite
Lens.makePrisms ''Type

-- | A convenience infix alias for 'TFun'
infixr 2 ~>
(~>) :: Type -> Type -> Type
(~>) = TFun

instance Pretty Type where
    pPrintPrec lvl prec typ =
        case typ of
        TVar n -> pPrint n
        TFun t s ->
            maybeParens (8 < prec) $
            pPrintPrec lvl 9 t <+> PP.text "->" <+> pPrintPrec lvl 8 s
        TInst n ps ->
            pPrint n <>
            if Map.null ps then PP.empty
            else
                PP.text "<" <>
                PP.hsep (List.intersperse PP.comma (map showParam (Map.toList ps))) <>
                PP.text ">"
            where
                showParam (p, v) = pPrint p <+> PP.text "=" <+> pPrint v
        TRecord r -> PP.text "*" <> pPrint r
        TSum s -> PP.text "+" <> pPrint s

instance Pretty (Composite p) where
    pPrint CEmpty = PP.text "{}"
    pPrint x =
        PP.text "{" <+> go PP.empty x <+> PP.text "}"
        where
            go _   CEmpty          = PP.empty
            go sep (CVar tv)       = sep <> pPrint tv <> PP.text "..."
            go sep (CExtend f t r) = sep <> pPrint f <+> PP.text ":" <+> pPrint t <> go (PP.text ", ") r

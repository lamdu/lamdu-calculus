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
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module Lamdu.Calc.Type
    (
    -- * Type Variable kinds
      RowVar, TypeVar
    -- * Typed identifiers of the Type AST
    , Var(..), NominalId(..), Tag(..), ParamId(..)
    -- * Rows
    , Row(..)
    -- * Composite Prisms
    , _RExtend, _REmpty, _RVar
    -- * Type AST
    , Type(..)
    , (~>)
    -- * Type Prisms
    , _TVar, _TFun, _TInst, _TRecord, _TVariant
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Hashable (Hashable)
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Semigroup ((<>))
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import           Lamdu.Calc.Identifier (Identifier)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A type varible of some kind ('Var' 'Type', 'Var' 'Variant', or 'Var' 'Record')
newtype Var t = Var { tvName :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | An identifier for a nominal type
newtype NominalId = NominalId { nomId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | An identifier for a component in a variant type (aka data
-- constructor) or a component(field) in a record
newtype Tag = Tag { tagName :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | In Lamdu Calculus, all type parameters are named (keyword
-- arguments), this is the type of the type parameter names.
newtype ParamId = ParamId { typeParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty, Binary, Hashable)

-- | A row type variable that represents a set of
-- typed fields in a row
type RowVar = Var Row

-- | A type variable that represents a type
type TypeVar = Var Type

-- | The AST for rows (records, variants) For
-- example: RExtend "a" int (RExtend "b" bool (RVar "c")) represents
-- the composite type:
-- > { a : int, b : bool | c }
data Row
    = RExtend Tag Type Row
      -- ^ Extend a row type with an extra component (field /
      -- data constructor).
    | REmpty
      -- ^ The empty row type (empty record [unit] or empty variant [void])
    | RVar (Var Row)
      -- ^ A row type variable
    deriving (Generic, Show, Eq, Ord)
instance NFData Row
instance Binary Row

-- | The AST for any Lamdu Calculus type
data Type
    = TVar TypeVar
      -- ^ A type variable
    | TFun Type Type
      -- ^ A (non-dependent) function of the given parameter and result types
    | TInst NominalId (Map ParamId Type)
      -- ^ An instantiation of a nominal type of the given id with the
      -- given keyword type arguments
    | TRecord Row
      -- ^ Lifts a composite record type
    | TVariant Row
      -- ^ Lifts a composite variant type
    deriving (Generic, Show, Eq, Ord)
instance NFData Type
instance Binary Type

Lens.makePrisms ''Row
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
        TVariant s -> PP.text "+" <> pPrint s

instance Pretty Row where
    pPrint REmpty = PP.text "{}"
    pPrint x =
        PP.text "{" <+> go PP.empty x <+> PP.text "}"
        where
            go _   REmpty          = PP.empty
            go sep (RVar tv)       = sep <> pPrint tv <> PP.text "..."
            go sep (RExtend f t r) = sep PP.<> pPrint f <+> PP.text ":" <+> pPrint t PP.<> go (PP.text ", ") r

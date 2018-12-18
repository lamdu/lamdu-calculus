-- | Val AST
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, GeneralizedNewtypeDeriving, TemplateHaskell, FlexibleContexts, UndecidableInstances, StandaloneDeriving, TypeFamilies, MultiParamTypeClasses #-}
module Lamdu.Calc.Term
    ( Val
    , Leaf(..), _LVar, _LHole, _LLiteral, _LRecEmpty, _LAbsurd
    , PrimVal(..), primType, primData
    , Term(..)
        , _BApp, _BLam, _BGetField, _BRecExtend
        , _BInject, _BCase, _BToNom, _BFromNom, _BLeaf
    , Apply(..), applyFunc, applyArg
    , GetField(..), getFieldRecord, getFieldTag
    , Inject(..), injectVal, injectTag
    , Case(..), caseTag, caseMatch, caseMismatch
    , Lam(..), lamIn, lamOut
    , RecExtend(..), recTag, recFieldVal, recRest
    , Nom(..), nomId, nomVal
    , Var(..)
    ) where

import           Prelude.Compat

import           AST (Tree, Tie, Ann, makeChildren)
import           AST.Term.Apply (Apply(..), applyFunc, applyArg)
import           AST.Term.Lam (Lam(..), lamIn, lamOut)
import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import           Data.Hashable (Hashable(..))
import           Data.Semigroup ((<>))
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import           Lamdu.Calc.Identifier (Identifier)
import qualified Lamdu.Calc.Type as T
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

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

data Case exp = Case
    { _caseTag :: T.Tag
    , _caseMatch :: exp
    , _caseMismatch :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq, Ord)
instance NFData exp => NFData (Case exp)
instance Binary exp => Binary (Case exp)
instance Hashable exp => Hashable (Case exp)

Lens.makeLenses ''Case

data RecExtend exp = RecExtend
    { _recTag :: T.Tag
    , _recFieldVal :: exp
    , _recRest :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq, Ord)
instance NFData exp => NFData (RecExtend exp)
instance Binary exp => Binary (RecExtend exp)
instance Hashable exp => Hashable (RecExtend exp)

Lens.makeLenses ''RecExtend

data Nom exp = Nom
    { _nomId :: T.NominalId
    , _nomVal :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq, Ord)
instance NFData exp => NFData (Nom exp)
instance Hashable exp => Hashable (Nom exp)
instance Binary exp => Binary (Nom exp)

Lens.makeLenses ''Nom

data Term f
    = BApp {-# UNPACK #-}!(Apply Term f)
    | BLam {-# UNPACK #-}!(Lam Var Term f)
    | BGetField {-# UNPACK #-}!(GetField (Tie f Term))
    | BRecExtend {-# UNPACK #-}!(RecExtend (Tie f Term))
    | BInject {-# UNPACK #-}!(Inject (Tie f Term))
    | BCase {-# UNPACK #-}!(Case (Tie f Term))
    | -- Convert to Nominal type
      BToNom {-# UNPACK #-}!(Nom (Tie f Term))
    | -- Convert from Nominal type
      BFromNom {-# UNPACK #-}!(Nom (Tie f Term))
    | BLeaf Leaf
    deriving Generic

-- NOTE: Careful of Eq, it's not alpha-eq!
deriving instance Eq   (Tie f Term) => Eq   (Term f)
deriving instance Ord  (Tie f Term) => Ord  (Term f)
deriving instance Show (Tie f Term) => Show (Term f)
instance Binary (Tie f Term) => Binary (Term f)

Lens.makePrisms ''Term

makeChildren [''Term]

instance Pretty (Tie f Term) => Pretty (Term f) where
    pPrintPrec lvl prec b =
        case b of
        BLeaf (LVar var)          -> pPrint var
        BLeaf (LLiteral (PrimVal _p d)) -> PP.text (BS8.unpack d)
        BLeaf LHole               -> PP.text "?"
        BLeaf LAbsurd             -> PP.text "absurd"
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
        BCase (Case n m mm)       -> maybeParens (0 < prec) $
                                     PP.vcat
                                     [ PP.text "case of"
                                     , pPrint n <> PP.text " -> " <> pPrint m
                                     , PP.text "_" <> PP.text " -> " <> pPrint mm
                                     ]
        BToNom (Nom ident val)    -> PP.text "[ ->" <+> pPrint ident <+> pPrint val <+> PP.text "]"
        BFromNom (Nom ident val)  -> PP.text "[" <+> pPrint ident <+> pPrint val <+> PP.text "-> ]"
        BLeaf LRecEmpty           -> PP.text "{}"
        BRecExtend (RecExtend tag val rest) ->
                                     PP.text "{" <+>
                                     prField PP.<>
                                     PP.comma <+>
                                     pPrint rest <+>
                                     PP.text "}"
            where
                prField = pPrint tag <+> PP.text "=" <+> pPrint val

-- Type synonym to ease the transition
type Val a = Tree (Ann a) Term

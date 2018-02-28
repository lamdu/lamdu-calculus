-- | Val AST
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module Lamdu.Calc.Val
    ( Leaf(..), _LVar, _LHole, _LLiteral, _LRecEmpty, _LAbsurd
    , PrimVal(..), primType, primData
    , Body(..)
        , _BApp, _BLam, _BGetField, _BRecExtend
        , _BInject, _BCase, _BToNom, _BFromNom, _BLeaf
    , Apply(..), applyFunc, applyArg
    , GetField(..), getFieldRecord, getFieldTag
    , Inject(..), injectVal, injectTag
    , Case(..), caseTag, caseMatch, caseMismatch
    , Lam(..), lamParamId, lamResult
    , RecExtend(..), recTag, recFieldVal, recRest
    , Nom(..), nomId, nomVal
    , Var(..)
    , Match(..)
    ) where

import           Prelude.Compat

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
    deriving (Generic, Show, Eq)
instance NFData Leaf
instance Binary Leaf
instance Hashable Leaf

Lens.makePrisms ''Leaf

class Match f where
    match :: (a -> b -> c) -> f a -> f b -> Maybe (f c)

data Apply exp = Apply
    { _applyFunc :: exp
    , _applyArg :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (Apply exp)
instance Binary exp => Binary (Apply exp)
instance Hashable exp => Hashable (Apply exp)
instance Match Apply where
    match f (Apply f0 a0) (Apply f1 a1) = Just $ Apply (f f0 f1) (f a0 a1)

Lens.makeLenses ''Apply

data GetField exp = GetField
    { _getFieldRecord :: exp
    , _getFieldTag :: T.Tag
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (GetField exp)
instance Binary exp => Binary (GetField exp)
instance Hashable exp => Hashable (GetField exp)
instance Match GetField where
    match f (GetField r0 t0) (GetField r1 t1)
        | t0 == t1 = Just $ GetField (f r0 r1) t0
        | otherwise = Nothing

Lens.makeLenses ''GetField

data Inject exp = Inject
    { _injectTag :: T.Tag
    , _injectVal :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (Inject exp)
instance Binary exp => Binary (Inject exp)
instance Hashable exp => Hashable (Inject exp)
instance Match Inject where
    match f (Inject t0 r0) (Inject t1 r1)
        | t0 == t1 = Just $ Inject t0 (f r0 r1)
        | otherwise = Nothing

Lens.makeLenses ''Inject

data Case exp = Case
    { _caseTag :: T.Tag
    , _caseMatch :: exp
    , _caseMismatch :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (Case exp)
instance Binary exp => Binary (Case exp)
instance Hashable exp => Hashable (Case exp)
instance Match Case where
    match f (Case t0 h0 hr0) (Case t1 h1 hr1)
        | t0 == t1 = Just $ Case t0 (f h0 h1) (f hr0 hr1)
        | otherwise = Nothing

Lens.makeLenses ''Case

data Lam exp = Lam
    { _lamParamId :: Var
    , _lamResult :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (Lam exp)
instance Hashable exp => Hashable (Lam exp)
instance Binary exp => Binary (Lam exp)

Lens.makeLenses ''Lam

data RecExtend exp = RecExtend
    { _recTag :: T.Tag
    , _recFieldVal :: exp
    , _recRest :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (RecExtend exp)
instance Binary exp => Binary (RecExtend exp)
instance Hashable exp => Hashable (RecExtend exp)
instance Match RecExtend where
    match f (RecExtend t0 f0 r0) (RecExtend t1 f1 r1)
        | t0 == t1 = Just $ RecExtend t0 (f f0 f1) (f r0 r1)
        | otherwise = Nothing

Lens.makeLenses ''RecExtend

data Nom exp = Nom
    { _nomId :: T.NominalId
    , _nomVal :: exp
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData exp => NFData (Nom exp)
instance Hashable exp => Hashable (Nom exp)
instance Binary exp => Binary (Nom exp)
instance Match Nom where
    match f (Nom i0 v0) (Nom i1 v1)
        | i0 == i1 = Just $ Nom i0 (f v0 v1)
        | otherwise = Nothing

Lens.makeLenses ''Nom

data Body exp
    =  BApp {-# UNPACK #-}!(Apply exp)
    |  BLam {-# UNPACK #-}!(Lam exp)
    |  BGetField {-# UNPACK #-}!(GetField exp)
    |  BRecExtend {-# UNPACK #-}!(RecExtend exp)
    |  BInject {-# UNPACK #-}!(Inject exp)
    |  BCase {-# UNPACK #-}!(Case exp)
    |  -- Convert to Nominal type
       BToNom {-# UNPACK #-}!(Nom exp)
    |  -- Convert from Nominal type
       BFromNom {-# UNPACK #-}!(Nom exp)
    |  BLeaf Leaf
    deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
-- NOTE: Careful of Eq, it's not alpha-eq!
instance NFData exp => NFData (Body exp)
instance Hashable exp => Hashable (Body exp)
instance Binary exp => Binary (Body exp)

Lens.makePrisms ''Body

instance Pretty a => Pretty (Body a) where
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

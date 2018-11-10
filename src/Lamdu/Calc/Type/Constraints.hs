{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, GeneralizedNewtypeDeriving #-}
module Lamdu.Calc.Type.Constraints
    ( Constraints(..), null
    , applyRenames
    , intersect, difference
    , CompositeVar(..), forbiddenFields
    , CompositeVars(..), compositeVars
    , nullComposite
    , getRecordVar
    , getVariantVar
    , TypeVar
    , getTypeVar
    ) where

import           Prelude.Compat hiding (null)
import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Vars (TypeVars)
import qualified Lamdu.Calc.Type.Vars as TypeVars
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

type TypeVar = ()

newtype CompositeVar t = CompositeVar
    { _forbiddenFields :: Set T.Tag
    } deriving (Generic, Eq, Ord, Show, Semigroup, Monoid)

Lens.makeLenses ''CompositeVar

newtype CompositeVars t = CompositeVars
    { _compositeVars :: Map (T.Var (T.Composite t)) (CompositeVar t)
    } deriving (Generic, Eq, Ord, Show)

Lens.makeLenses ''CompositeVars

nullComposite :: CompositeVars t -> Bool
nullComposite (CompositeVars m) = Map.null m

instance Semigroup (CompositeVars t) where
    CompositeVars x <> CompositeVars y =
        CompositeVars (Map.unionWith (<>) x y)
instance Monoid (CompositeVars t) where
    mempty = CompositeVars Map.empty
    mappend = (<>)

instance NFData (CompositeVar t) where
instance NFData (CompositeVars t) where

instance Pretty (CompositeVars t) where
    pPrint (CompositeVars m)
        | Map.null m = PP.text "NoConstraints"
        | otherwise =
            PP.hcat $ PP.punctuate PP.comma $ Lens.imap pPrintConstraint m ^.. Lens.folded

instance Binary (CompositeVar t)
instance Binary (CompositeVars t)

renameApply ::
    Map (T.Var (T.Composite t)) (T.Var (T.Composite t)) ->
    CompositeVars t -> CompositeVars t
renameApply renames (CompositeVars m) =
    CompositeVars (Map.mapKeys rename m)
    where
        rename x = fromMaybe x $ Map.lookup x renames

data Constraints = Constraints
    { recordVar :: CompositeVars T.RecordTag
    , variantVar :: CompositeVars T.VariantTag
    } deriving (Generic, Eq, Ord, Show)

null :: Constraints -> Bool
null (Constraints rtvs stvs) =
    nullComposite rtvs
    && nullComposite stvs

instance Semigroup Constraints where
    Constraints p0 s0 <> Constraints p1 s1 = Constraints (p0 <> p1) (s0 <> s1)
instance Monoid Constraints where
    mempty = Constraints mempty mempty
    mappend = (<>)

instance Binary Constraints
instance NFData Constraints where
instance Pretty Constraints where
    pPrint (Constraints p s) =
        PP.text "{" <> pPrint p <> PP.text "}" <>
        PP.text "[" <> pPrint s <> PP.text "]"

getTVComposite :: T.Var (T.Composite t) -> CompositeVars t -> CompositeVar t
getTVComposite tv cs = cs ^. compositeVars . Lens.at tv . Lens._Just

getRecordVar :: T.RecordVar -> Constraints -> CompositeVar T.RecordTag
getRecordVar tv c = getTVComposite tv $ recordVar c

getVariantVar :: T.VariantVar -> Constraints -> CompositeVar T.VariantTag
getVariantVar tv c = getTVComposite tv $ variantVar c

getTypeVar :: T.TypeVar -> Constraints -> TypeVar
getTypeVar _ _ = ()

pPrintConstraint :: T.Var (T.Composite t) -> CompositeVar t -> PP.Doc
pPrintConstraint tv (CompositeVar forbidden) =
    PP.text "{" PP.<>
    (PP.hsep . map pPrint . Set.toList) forbidden PP.<>
    PP.text "}" <+>
    PP.text "∉" <+> pPrint tv

{-# INLINE applyRenames #-}
applyRenames :: TypeVars.Renames -> Constraints -> Constraints
applyRenames
    (TypeVars.Renames _ prodRenames variantRenames)
    (Constraints prod variant) =
        Constraints
        (renameApply prodRenames prod)
        (renameApply variantRenames variant)

compositeIntersect ::
    TypeVars.CompositeVarKind t =>
    TypeVars -> CompositeVars t -> CompositeVars t
compositeIntersect tvs (CompositeVars c) =
    CompositeVars (Map.filterWithKey inTVs c)
    where
        inTVs rtv _ = rtv `TypeVars.member` tvs

intersect :: TypeVars -> Constraints -> Constraints
intersect tvs (Constraints p s) =
    Constraints (compositeIntersect tvs p) (compositeIntersect tvs s)

compositeDifference :: CompositeVars t -> CompositeVars t -> CompositeVars t
compositeDifference (CompositeVars big) (CompositeVars small) =
    CompositeVars (Map.difference big small)

difference :: Constraints -> Constraints -> Constraints
difference (Constraints bigp bigs) (Constraints smallp smalls) =
    Constraints (compositeDifference bigp smallp) (compositeDifference bigs smalls)

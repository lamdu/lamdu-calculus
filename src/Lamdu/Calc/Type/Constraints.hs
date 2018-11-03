{-# LANGUAGE NoImplicitPrelude, DeriveGeneric #-}
module Lamdu.Calc.Type.Constraints
    ( Constraints(..), null
    , ForbiddenFields
    , applyRenames
    , intersect, difference
    , CompositeVarsConstraints(..), nullCompositeConstraints
    , getRecordVarConstraints
    , getVariantVarConstraints
    , TypeVarConstraints
    , getTypeVarConstraints
    ) where

import           Prelude.Compat hiding (null)
import           Control.DeepSeq (NFData(..))
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

type ForbiddenFields = Set T.Tag

type TypeVarConstraints = ()

newtype CompositeVarsConstraints t = CompositeVarsConstraints
    { compositeVarsConstraints :: Map (T.Var (T.Composite t)) ForbiddenFields
    } deriving (Generic, Eq, Ord, Show)

nullCompositeConstraints :: CompositeVarsConstraints t -> Bool
nullCompositeConstraints (CompositeVarsConstraints m) = Map.null m

instance Semigroup (CompositeVarsConstraints t) where
    CompositeVarsConstraints x <> CompositeVarsConstraints y =
        CompositeVarsConstraints (Map.unionWith (<>) x y)
instance Monoid (CompositeVarsConstraints t) where
    mempty = CompositeVarsConstraints Map.empty
    mappend = (<>)

instance NFData (CompositeVarsConstraints t) where

instance Pretty (CompositeVarsConstraints t) where
    pPrint (CompositeVarsConstraints m)
        | Map.null m = PP.text "NoConstraints"
        | otherwise =
            PP.hcat $ PP.punctuate PP.comma $ map (uncurry pPrintConstraint) $
            Map.toList m

instance Binary (CompositeVarsConstraints t)

renameApply ::
    Map (T.Var (T.Composite t)) (T.Var (T.Composite t)) ->
    CompositeVarsConstraints t -> CompositeVarsConstraints t
renameApply renames (CompositeVarsConstraints m) =
    CompositeVarsConstraints (Map.mapKeys rename m)
    where
        rename x = fromMaybe x $ Map.lookup x renames

data Constraints = Constraints
    { recordVarConstraints :: CompositeVarsConstraints T.RecordTag
    , variantVarConstraints :: CompositeVarsConstraints T.VariantTag
    } deriving (Generic, Eq, Ord, Show)

null :: Constraints -> Bool
null (Constraints rtvs stvs) =
    nullCompositeConstraints rtvs
    && nullCompositeConstraints stvs

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

getTVCompositeConstraints :: T.Var (T.Composite t) -> CompositeVarsConstraints t -> Set T.Tag
getTVCompositeConstraints tv = fromMaybe Set.empty . Map.lookup tv . compositeVarsConstraints

getRecordVarConstraints :: T.RecordVar -> Constraints -> ForbiddenFields
getRecordVarConstraints tv c = getTVCompositeConstraints tv $ recordVarConstraints c

getVariantVarConstraints :: T.VariantVar -> Constraints -> ForbiddenFields
getVariantVarConstraints tv c = getTVCompositeConstraints tv $ variantVarConstraints c

getTypeVarConstraints :: T.TypeVar -> Constraints -> TypeVarConstraints
getTypeVarConstraints _ _ = ()

pPrintConstraint :: T.Var t -> Set T.Tag -> PP.Doc
pPrintConstraint tv forbiddenFields =
    PP.text "{" PP.<>
    (PP.hsep . map pPrint . Set.toList) forbiddenFields PP.<>
    PP.text "}" <+>
    PP.text "∉" <+> pPrint tv

{-# INLINE applyRenames #-}
applyRenames :: TypeVars.Renames -> Constraints -> Constraints
applyRenames
    (TypeVars.Renames _ prodRenames variantRenames)
    (Constraints prodConstraints variantConstraints) =
        Constraints
        (renameApply prodRenames prodConstraints)
        (renameApply variantRenames variantConstraints)

compositeIntersect ::
    TypeVars.CompositeVarKind t =>
    TypeVars -> CompositeVarsConstraints t -> CompositeVarsConstraints t
compositeIntersect tvs (CompositeVarsConstraints c) =
    CompositeVarsConstraints (Map.filterWithKey inTVs c)
    where
        inTVs rtv _ = rtv `TypeVars.member` tvs

intersect :: TypeVars -> Constraints -> Constraints
intersect tvs (Constraints p s) =
    Constraints (compositeIntersect tvs p) (compositeIntersect tvs s)

compositeDifference ::
    CompositeVarsConstraints t ->
    CompositeVarsConstraints t ->
    CompositeVarsConstraints t
compositeDifference
    (CompositeVarsConstraints big)
    (CompositeVarsConstraints small) =
        CompositeVarsConstraints (Map.difference big small)

difference :: Constraints -> Constraints -> Constraints
difference (Constraints bigp bigs) (Constraints smallp smalls) =
    Constraints (compositeDifference bigp smallp) (compositeDifference bigs smalls)

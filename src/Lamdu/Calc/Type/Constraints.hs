{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving #-}
module Lamdu.Calc.Type.Constraints
    ( Constraints(..), null
    , ForbiddenFields
    , applyRenames
    , intersect, difference
    , CompositeVarConstraints(..), nullCompositeConstraints
    , getProductVarConstraints
    , getSumVarConstraints
    , TypeVarConstraints
    , getTypeVarConstraints
    ) where

import           Prelude.Compat hiding (null)
import           Control.DeepSeq (NFData(..))
import           Control.DeepSeq.Generics (genericRnf)
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Vars (TypeVars)
import qualified Lamdu.Calc.Type.Vars as TypeVars
import           Text.PrettyPrint ((<+>), (<>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

type ForbiddenFields = Set T.Tag

type TypeVarConstraints = ()

newtype CompositeVarConstraints t = CompositeVarConstraints
    { compositeVarConstraints :: Map (T.Var (T.Composite t)) ForbiddenFields
    } deriving (Generic, Eq, Show)

nullCompositeConstraints :: CompositeVarConstraints t -> Bool
nullCompositeConstraints (CompositeVarConstraints m) = Map.null m

instance Monoid (CompositeVarConstraints t) where
    mempty = CompositeVarConstraints Map.empty
    mappend (CompositeVarConstraints x) (CompositeVarConstraints y) =
        CompositeVarConstraints $ Map.unionWith mappend x y

instance NFData (CompositeVarConstraints t) where rnf = genericRnf

instance Pretty (CompositeVarConstraints t) where
    pPrint (CompositeVarConstraints m)
        | Map.null m = PP.text "NoConstraints"
        | otherwise =
            PP.hcat $ PP.punctuate PP.comma $ map (uncurry pPrintConstraint) $
            Map.toList m

instance Binary (CompositeVarConstraints t)

renameApply ::
    Map (T.Var (T.Composite t)) (T.Var (T.Composite t)) ->
    CompositeVarConstraints t -> CompositeVarConstraints t
renameApply renames (CompositeVarConstraints m) =
    CompositeVarConstraints (Map.mapKeys rename m)
    where
        rename x = fromMaybe x $ Map.lookup x renames

data Constraints = Constraints
    { productVarConstraints :: CompositeVarConstraints T.ProductTag
    , sumVarConstraints :: CompositeVarConstraints T.SumTag
    } deriving (Generic, Eq, Show)

null :: Constraints -> Bool
null (Constraints rtvs stvs) =
    nullCompositeConstraints rtvs
    && nullCompositeConstraints stvs

instance Monoid Constraints where
    mempty = Constraints mempty mempty
    mappend (Constraints p0 s0) (Constraints p1 s1) =
        Constraints (mappend p0 p1) (mappend s0 s1)

instance Binary Constraints
instance NFData Constraints where rnf = genericRnf
instance Pretty Constraints where
    pPrint (Constraints p s) =
        PP.text "{" <> pPrint p <> PP.text "}" <>
        PP.text "[" <> pPrint s <> PP.text "]"

getTVCompositeConstraints :: T.Var (T.Composite t) -> CompositeVarConstraints t -> Set T.Tag
getTVCompositeConstraints tv = fromMaybe Set.empty . Map.lookup tv . compositeVarConstraints

getProductVarConstraints :: T.ProductVar -> Constraints -> ForbiddenFields
getProductVarConstraints tv c = getTVCompositeConstraints tv $ productVarConstraints c

getSumVarConstraints :: T.SumVar -> Constraints -> ForbiddenFields
getSumVarConstraints tv c = getTVCompositeConstraints tv $ sumVarConstraints c

getTypeVarConstraints :: T.TypeVar -> Constraints -> TypeVarConstraints
getTypeVarConstraints _ _ = ()

pPrintConstraint :: T.Var t -> Set T.Tag -> PP.Doc
pPrintConstraint tv forbiddenFields =
    PP.text "{" <>
    (PP.hsep . map pPrint . Set.toList) forbiddenFields <>
    PP.text "}" <+>
    PP.text "∉" <+> pPrint tv

{-# INLINE applyRenames #-}
applyRenames :: TypeVars.Renames -> Constraints -> Constraints
applyRenames
    (TypeVars.Renames _ prodRenames sumRenames)
    (Constraints prodConstraints sumConstraints) =
        Constraints
        (renameApply prodRenames prodConstraints)
        (renameApply sumRenames sumConstraints)

compositeIntersect ::
    TypeVars.CompositeVarKind t =>
    TypeVars -> CompositeVarConstraints t -> CompositeVarConstraints t
compositeIntersect tvs (CompositeVarConstraints c) =
    CompositeVarConstraints (Map.filterWithKey inTVs c)
    where
        inTVs rtv _ = rtv `TypeVars.member` tvs

intersect :: TypeVars -> Constraints -> Constraints
intersect tvs (Constraints p s) =
    Constraints (compositeIntersect tvs p) (compositeIntersect tvs s)

compositeDifference ::
    TypeVars.CompositeVarKind t =>
    CompositeVarConstraints t ->
    CompositeVarConstraints t ->
    CompositeVarConstraints t
compositeDifference
    (CompositeVarConstraints big)
    (CompositeVarConstraints small) =
        CompositeVarConstraints (Map.difference big small)

difference :: Constraints -> Constraints -> Constraints
difference (Constraints bigp bigs) (Constraints smallp smalls) =
    Constraints (compositeDifference bigp smallp) (compositeDifference bigs smalls)

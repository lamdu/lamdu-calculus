{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, GeneralizedNewtypeDeriving #-}
module Lamdu.Calc.Type.Constraints
    ( Constraints(..), compositeVars
    , null
    , applyRenames
    , intersect, difference
    , CompositeVar(..), forbiddenFields
    , getRowVar
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

newtype CompositeVar = CompositeVar
    { _forbiddenFields :: Set T.Tag
    } deriving (Generic, Eq, Ord, Show, Semigroup, Monoid)

Lens.makeLenses ''CompositeVar

newtype Constraints = Constraints
    { _compositeVars :: Map T.RowVar CompositeVar
    } deriving (Generic, Eq, Ord, Show)

Lens.makeLenses ''Constraints

null :: Constraints -> Bool
null (Constraints m) = Map.null m

instance Semigroup Constraints where
    Constraints x <> Constraints y =
        Constraints (Map.unionWith (<>) x y)
instance Monoid Constraints where
    mempty = Constraints Map.empty
    mappend = (<>)

instance NFData CompositeVar
instance NFData Constraints

instance Pretty Constraints where
    pPrint (Constraints m)
        | Map.null m = PP.text "NoConstraints"
        | otherwise =
            PP.hcat $ PP.punctuate PP.comma $ Lens.imap pPrintConstraint m ^.. Lens.folded

instance Binary CompositeVar
instance Binary Constraints

renameApply ::
    Map T.RowVar T.RowVar ->
    Constraints -> Constraints
renameApply renames (Constraints m) =
    Constraints (Map.mapKeys rename m)
    where
        rename x = fromMaybe x $ Map.lookup x renames

getRowVar :: T.RowVar -> Constraints -> CompositeVar
getRowVar tv cs = cs ^. compositeVars . Lens.ix tv

getTypeVar :: T.TypeVar -> Constraints -> TypeVar
getTypeVar _ _ = ()

pPrintConstraint :: T.RowVar -> CompositeVar -> PP.Doc
pPrintConstraint tv (CompositeVar forbidden) =
    PP.text "{" PP.<>
    (PP.hsep . map pPrint . Set.toList) forbidden PP.<>
    PP.text "}" <+>
    PP.text "∉" <+> pPrint tv

{-# INLINE applyRenames #-}
applyRenames :: TypeVars.Renames -> Constraints -> Constraints
applyRenames (TypeVars.Renames _ rowRenames) = renameApply rowRenames

intersect :: TypeVars -> Constraints -> Constraints
intersect tvs (Constraints c) =
    Constraints (Map.filterWithKey inTVs c)
    where
        inTVs rtv _ = rtv `TypeVars.member` tvs

difference :: Constraints -> Constraints -> Constraints
difference (Constraints big) (Constraints small) =
    Constraints (Map.difference big small)

-- | A lamdu-calculus `Definition` is a top-level definition of a
-- value along with the types of all free variables/nominals it uses
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, TypeOperators #-}

module Lamdu.Calc.Definition
    ( Deps(..), depsGlobalTypes, depsNominals
    , pruneDeps
    ) where

import           Hyper (Ann, Pure, Const(..), Generic, HFunctor(..), hflipped, type (#))
import           Hyper.Type.AST.Nominal (NominalDecl)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Lamdu.Calc.Lens (valGlobals, valNominals)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

data Deps = Deps
    { _depsGlobalTypes :: !(Map V.Var (Pure # T.Scheme))
    , _depsNominals :: !(Map T.NominalId (Pure # NominalDecl Type))
    } deriving (Generic, Show, Eq, Ord)
instance NFData Deps
instance Binary Deps

Lens.makeLenses ''Deps

instance Semigroup Deps where
    Deps t0 n0 <> Deps t1 n1 = Deps (t0 <> t1) (n0 <> n1)
instance Monoid Deps where
    mempty = Deps mempty mempty
    mappend = (<>)

pruneDeps ::
    Ann a # V.Term -> Deps -> Deps
pruneDeps e deps =
    deps
    & depsGlobalTypes %~ prune (valGlobals mempty)
    & depsNominals %~ prune valNominals
    where
        ev = e & hflipped %~ hmap (\_ _ -> Const ())
        prune f = Map.filterWithKey (const . (`Set.member` Set.fromList (ev ^.. f)))

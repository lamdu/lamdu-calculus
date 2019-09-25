-- | A lamdu-calculus `Definition` is a top-level definition of a
-- value along with the types of all free variables/nominals it uses
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric #-}

module Lamdu.Calc.Definition
    ( Deps(..), depsGlobalTypes, depsNominals
    , pruneDeps
    ) where

import           Hyper (Ann, Tree, Pure)
import           Hyper.Type.AST.Nominal (NominalDecl)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import           Lamdu.Calc.Lens (valGlobals, valNominals)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

data Deps = Deps
    { _depsGlobalTypes :: !(Map V.Var (Tree Pure T.Scheme))
    , _depsNominals :: !(Map T.NominalId (Tree Pure (NominalDecl Type)))
    } deriving (Generic, Show, Eq, Ord)
instance NFData Deps
instance Binary Deps

Lens.makeLenses ''Deps

instance Semigroup Deps where
    Deps t0 n0 <> Deps t1 n1 = Deps (t0 <> t1) (n0 <> n1)
instance Monoid Deps where
    mempty = Deps mempty mempty
    mappend = (<>)

pruneDeps :: Tree (Ann a) V.Term -> Deps -> Deps
pruneDeps e deps =
    deps
    & depsGlobalTypes %~ prune (valGlobals mempty)
    & depsNominals %~ prune valNominals
    where
        prune f = Map.filterWithKey (const . (`Set.member` Set.fromList (e ^.. f)))

-- depSchemes :: Lens.Traversal' Deps (Tree T.Scheme Pure)
-- depSchemes f (Deps globals nominals) =
--     Deps
--     <$> traverse f globals
--     <*> (traverse . nScheme) f nominals

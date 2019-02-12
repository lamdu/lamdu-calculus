-- | A lamdu-calculus `Definition` is a top-level definition of a
-- value along with the types of all free variables/nominals it uses
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric #-}

module Lamdu.Calc.Definition
    ( Deps(..), depsGlobalTypes, depsNominals
    ) where

import           AST (Tree, Pure)
import           AST.Term.Nominal (NominalDecl)
import           AST.Term.Scheme (Scheme)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Map (Map)
import           GHC.Generics (Generic)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

data Deps = Deps
    { _depsGlobalTypes :: !(Map V.Var (Tree Pure (Scheme T.Types Type)))
    , _depsNominals :: !(Map T.NominalId (Tree Pure (NominalDecl Type)))
    } deriving (Generic, Show, Eq)
instance NFData Deps
instance Binary Deps

Lens.makeLenses ''Deps

instance Semigroup Deps where
    Deps t0 n0 <> Deps t1 n1 = Deps (t0 <> t1) (n0 <> n1)
instance Monoid Deps where
    mempty = Deps mempty mempty
    mappend = (<>)

-- depSchemes :: Lens.Traversal' Deps (Tree (Scheme T.Types Type) Pure)
-- depSchemes f (Deps globals nominals) =
--     Deps
--     <$> traverse f globals
--     <*> (traverse . nScheme) f nominals

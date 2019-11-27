{-# LANGUAGE NoImplicitPrelude, TypeApplications, TypeOperators #-}

module Lamdu.Calc.Term.Eq
    ( couldEq
    ) where

import           Hyper
import           Hyper.Class.ZipMatch
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (guard, join)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           Lamdu.Calc.Term

import           Prelude.Compat

class CouldEq e where
    go :: Map Var Var -> Pure # e -> Pure # e -> Bool

instance CouldEq Term where
    go xToY (Pure (BLam (Lam xvar xresult))) (Pure (BLam (Lam yvar yresult))) =
        go (xToY & Lens.at xvar ?~ yvar) xresult yresult
    go xToY (Pure xBody) (Pure yBody) =
        case join (zipMatch_ (Proxy @CouldEq #> \x -> guard . go xToY x) xBody yBody) of
        Just () -> True
        Nothing ->
            case (xBody, yBody) of
            (BLeaf LHole, _) -> True
            (_, BLeaf LHole) -> True
            (BLeaf (LVar x), BLeaf (LVar y)) -> xToY ^. Lens.at x == Just y
            _ -> False

couldEq :: Pure # Term -> Pure # Term -> Bool
couldEq = go Map.empty

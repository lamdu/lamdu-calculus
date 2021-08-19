{-# LANGUAGE NoImplicitPrelude, TypeApplications, TypeOperators, FlexibleInstances #-}

module Lamdu.Calc.Term.Eq
    ( couldEq
    ) where

import           Hyper
import           Hyper.Class.ZipMatch
import           Hyper.Type.Prune
import qualified Control.Lens as Lens
import qualified Data.Map as Map
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T

import           Lamdu.Calc.Internal.Prelude

class CouldEq e where
    go :: Map Var Var -> Pure # e -> Pure # e -> Bool

instance CouldEq Term where
    go xToY (Pure (BLam (TypedLam xvar xtyp xresult))) (Pure (BLam (TypedLam yvar ytyp yresult))) =
        go xToY xtyp ytyp &&
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

instance CouldEq (HCompose Prune T.Type) where
    go _ (Pure (HCompose Pruned)) _ = True
    go _ _ (Pure (HCompose Pruned)) = True
    go xToY (Pure xBody) (Pure yBody) =
        Lens.has Lens._Just
        (join (zipMatch_ (Proxy @CouldEq #> \x -> guard . go xToY x) xBody yBody))

instance CouldEq (HCompose Prune T.Row) where
    go _ (Pure (HCompose Pruned)) _ = True
    go _ _ (Pure (HCompose Pruned)) = True
    go xToY (Pure xBody) (Pure yBody) =
        Lens.has Lens._Just
        (join (zipMatch_ (Proxy @CouldEq #> \x -> guard . go xToY x) xBody yBody))

couldEq :: Pure # Term -> Pure # Term -> Bool
couldEq = go Map.empty

{-# LANGUAGE NoImplicitPrelude #-}

module Lamdu.Calc.Term.Eq
    ( alphaEq, couldEq
    ) where

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Tree.Diverse (Node(..), Ann(..))
import           Lamdu.Calc.Term

import           Prelude.Compat

eqCommon :: Bool -> Val () -> Val () -> Bool
eqCommon holeIsJoker =
    go Map.empty
    where
        xToYConv xToY x =
            fromMaybe x $ Map.lookup x xToY
        go xToY (Node (Ann _ xBody)) (Node (Ann _ yBody)) =
            case (xBody, yBody) of
            (BLeaf LHole, _) | holeIsJoker -> True
            (_, BLeaf LHole) | holeIsJoker -> True
            (BLam (Lam xvar xresult),
              BLam (Lam yvar yresult)) ->
                go (Map.insert xvar yvar xToY) xresult yresult
            (BLeaf (LVar x), BLeaf (LVar y)) ->
                -- TODO: This is probably not 100% correct for various
                -- shadowing corner cases
                xToYConv xToY x == y
            (BLeaf x, BLeaf y) -> x == y
            (BApp x, BApp y) -> goRecurse x y
            (BGetField x, BGetField y) -> goRecurse x y
            (BRecExtend x, BRecExtend y) -> goRecurse x y
            (BCase x, BCase y) -> goRecurse x y
            (BInject x, BInject y) -> goRecurse x y
            (BFromNom x, BFromNom y) -> goRecurse x y
            (BToNom x, BToNom y) -> goRecurse x y
            (_, _) -> False
            where
                goRecurse x y = maybe False Foldable.and $ match (go xToY) x y

alphaEq :: Val () -> Val () -> Bool
alphaEq = eqCommon False

-- could be equal if holes will be filled the same
couldEq :: Val () -> Val () -> Bool
couldEq = eqCommon True

{-# LANGUAGE NoImplicitPrelude #-}

module Lamdu.Calc.Term.Eq
    ( alphaEq, couldEq
    ) where

import           AST (Ann(..))
import           AST.Class.ZipMatch (zipMatchWith_)
import           AST.Term.Nominal (ToNom(..))
import           AST.Term.Row (RowExtend(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (guard)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))
import           Lamdu.Calc.Term

import           Prelude.Compat

-- TODO:
-- * Is this needed?
-- * `syntax-tree` package should make this simple

eqCommon :: Bool -> Val () -> Val () -> Bool
eqCommon holeIsJoker =
    go Map.empty
    where
        xToYConv xToY x =
            fromMaybe x $ Map.lookup x xToY
        go xToY (Ann _ xBody) (Ann _ yBody) =
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
            (BApp x, BApp y) ->
                zipMatchWith_ (Proxy :: Proxy ((~) Term)) (fmap guard . go xToY) x y
                & Lens.has (Lens._Just . Lens._Just)
            (BGetField (GetField r0 f0), BGetField (GetField r1 f1))
                | f0 == f1 -> go xToY r0 r1
            (BRecExtend (RowExtend t0 f0 r0), BRecExtend (RowExtend t1 f1 r1))
                -- TODO: this is wrong actually, fields can have different order!
                | t0 == t1 -> go xToY f0 f1 && go xToY r0 r1
            (BCase (RowExtend t0 a0 r0), BCase (RowExtend t1 a1 r1))
                -- TODO: this is wrong actually, fields can have different order!
                | t0 == t1 -> go xToY a0 a1 && go xToY r0 r1
            (BInject (Inject t0 v0), BInject (Inject t1 v1))
                | t0 == t1 -> go xToY v0 v1
            (BFromNom (Nom n0 v0), BFromNom (Nom n1 v1))
                | n0 == n1 -> go xToY v0 v1
            (BToNom (ToNom n0 v0), BToNom (ToNom n1 v1))
                | n0 == n1 -> go xToY v0 v1
            (_, _) -> False

alphaEq :: Val () -> Val () -> Bool
alphaEq = eqCommon False

-- could be equal if holes will be filled the same
couldEq :: Val () -> Val () -> Bool
couldEq = eqCommon True

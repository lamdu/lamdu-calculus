{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Calc.Type.Match
    ( VarMatches, matchVars
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import qualified Data.Map as Map
import qualified Data.Map.Utils as MapUtils
import           Lamdu.Calc.FlatComposite (FlatComposite(..))
import qualified Lamdu.Calc.FlatComposite as Flat
import           Lamdu.Calc.Type

type VarMatches = ([(TypeVar, TypeVar)], [(ProductVar, ProductVar)], [(SumVar, SumVar)])

matchVars :: Type -> Type -> Maybe VarMatches
matchVars (TVar tv0)         (TVar tv1)         = Just ([(tv0, tv1)], [], [])
matchVars (TFun a0 b0)       (TFun a1 b1)       = mappend <$> matchVars a0 a1 <*> matchVars b0 b1
matchVars (TInst i0 params0) (TInst i1 params1)
    | i0 == i1 =
        MapUtils.match matchVars params0 params1
        <&> Map.elems >>= sequence <&> mconcat
matchVars (TRecord c0) (TRecord c1) =
    matchCompositeVars (\x -> ([], x, [])) c0 c1
matchVars (TSum c0) (TSum c1) =
    matchCompositeVars (\x -> ([], [], x)) c0 c1
matchVars _ _ = Nothing

matchCompositeVars ::
    ([(Var (Composite t), Var (Composite t))] -> VarMatches) ->
    Composite t -> Composite t -> Maybe VarMatches
matchCompositeVars f c0 c1 =
    case (v0, v1) of
    (Nothing, Nothing) -> fMatch
    (Just r0, Just r1) -> fMatch `mappend` Just (f [(r0, r1)])
    _ -> Nothing
    where
        FlatComposite f0 v0 = Flat.fromComposite c0
        FlatComposite f1 v1 = Flat.fromComposite c1
        fMatch =
            MapUtils.match matchVars f0 f1
            <&> Map.elems >>= sequence <&> mconcat

{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Calc.Type.Match
    ( VarMatches, matchVars
    ) where

import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Lamdu.Calc.Type
import           Lamdu.Calc.Type.FlatComposite (FlatComposite(..))
import qualified Lamdu.Calc.Type.FlatComposite as Flat

import           Prelude.Compat

type VarMatches = ([(TypeVar, TypeVar)], [(RowVar, RowVar)])

matchMap :: Ord k => (a -> b -> c) -> Map k a -> Map k b -> Maybe (Map k c)
matchMap valMatch m0 m1
    | Map.keysSet m0 == Map.keysSet m1 =
          Just $ Map.intersectionWith valMatch m0 m1
    | otherwise = Nothing

matchVars :: Type -> Type -> Maybe VarMatches
matchVars (TVar tv0)         (TVar tv1)         = Just ([(tv0, tv1)], [])
matchVars (TFun a0 b0)       (TFun a1 b1)       = mappend <$> matchVars a0 a1 <*> matchVars b0 b1
matchVars (TInst i0 params0) (TInst i1 params1)
    | i0 == i1 =
        matchMap matchVars params0 params1
        <&> Map.elems >>= sequence <&> mconcat
matchVars (TRecord c0) (TRecord c1) =
    matchCompositeVars (\x -> ([], x)) c0 c1
matchVars (TVariant c0) (TVariant c1) =
    matchCompositeVars (\x -> ([], x)) c0 c1
matchVars _ _ = Nothing

matchCompositeVars ::
    ([(RowVar, RowVar)] -> VarMatches) ->
    Row -> Row -> Maybe VarMatches
matchCompositeVars f c0 c1 =
    case (v0, v1) of
    (Nothing, Nothing) -> fMatch
    (Just r0, Just r1) -> fMatch <> Just (f [(r0, r1)])
    _ -> Nothing
    where
        FlatComposite f0 v0 = Flat.fromComposite c0
        FlatComposite f1 v1 = Flat.fromComposite c1
        fMatch =
            matchMap matchVars f0 f1
            <&> Map.elems >>= sequence <&> mconcat

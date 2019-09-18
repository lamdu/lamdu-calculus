{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}

import           AST
import           AST.Knot.Ann (addAnnotations)
import           AST.Infer
import           AST.Unify
import           AST.Unify.Apply
import           Control.DeepSeq (rnf)
import           Control.Exception (evaluate)
import           Control.Lens (ASetter', _Right)
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.Reader
import           Control.Monad.ST.Class
import           Control.Monad.Trans.Maybe
import           Criterion (Benchmarkable, whnfIO)
import           Criterion.Main (bench, defaultMain)
import           Data.STRef
import           Lamdu.Calc.Definition (pruneDeps)
import           Lamdu.Calc.Infer
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T
import           TestVals

import           Prelude.Compat

localInitEnv ::
    ( MonadReader env m
    , Unify m T.Type, Unify m T.Row
    ) =>
    ASetter' env (Tree Scope (UVarOf m)) -> Tree (Ann z) Term -> m a -> m a
localInitEnv inferEnv e action =
    do
        addScope <- loadDeps (pruneDeps e allDeps)
        local (inferEnv %~ addScope) action

toAnn :: KPlain Term -> Tree (Ann ()) Term
toAnn = addAnnotations (const (const ())) . (^. kPlain)

benchInferPure :: KPlain Term -> Benchmarkable
benchInferPure e =
    infer x
    <&> (^. iRes . iType)
    >>= applyBindings
    & localInitEnv id x
    & runPureInfer emptyScope (InferState emptyPureInferState varGen)
    & _Right %~ (^. _1)
    & rnf
    & evaluate
    & whnfIO
    where
        x = toAnn e

benchInferST :: KPlain Term -> Benchmarkable
benchInferST e =
    do
        vg <- newSTRef varGen
        localInitEnv _1 x
            (infer x <&> (^. iRes . iType) >>= applyBindings) ^. _STInfer
            & (`runReaderT` (emptyScope, vg))
            & runMaybeT
    & liftST >>= evaluate . rnf & whnfIO
    where
        x = toAnn e

benches :: [(String, Benchmarkable)]
benches =
    [ ("S_factorial", benchInferST factorialVal)
    , ("S_euler1", benchInferST euler1Val)
    , ("S_solveDepressedQuartic", benchInferST solveDepressedQuarticVal)
    , ("S_factors", benchInferST factorsVal)
    , ("P_factorial", benchInferPure factorialVal)
    , ("P_euler1", benchInferPure euler1Val)
    , ("P_solveDepressedQuartic", benchInferPure solveDepressedQuarticVal)
    , ("P_factors", benchInferPure factorsVal)
    ]

main :: IO ()
main = defaultMain $ map (uncurry bench) benches

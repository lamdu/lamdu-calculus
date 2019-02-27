{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}
import           AST
import           AST.Infer
import           AST.Unify
import           Control.DeepSeq (rnf)
import           Control.Exception (evaluate)
import           Control.Lens (ASetter', _Right, _Left)
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.Reader
import           Control.Monad.ST.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.RWS (RWST(..))
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
    ASetter' env (InferEnv (UVar m)) -> Tree (Ann z) Term -> m a -> m a
localInitEnv inferEnv e action =
    do
        addScope <- loadDeps (pruneDeps e allDeps)
        local (inferEnv %~ addScope) action

benchInferPure :: Val () -> Benchmarkable
benchInferPure e =
    runRWST (action ^. _PureInferT) emptyInferEnv (InferState emptyPureInferState varGen)
    & _Right %~ (^. _1)
    & _Left %~ (\x -> x :: Tree Pure T.TypeError)
    & rnf
    & evaluate
    & whnfIO
    where
        action =
            localInitEnv id e
            (inferNode e <&> (^. iType) >>= applyBindings)

benchInferST :: Val () -> Benchmarkable
benchInferST e =
    do
        vg <- newSTRef varGen
        localInitEnv _1 e
            (inferNode e <&> (^. iType) >>= applyBindings) ^. _STInfer
            & (`runReaderT` (emptyInferEnv, vg))
            & runMaybeT
    & liftST >>= evaluate . rnf & whnfIO

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

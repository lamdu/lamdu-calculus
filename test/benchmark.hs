{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}

import           Hyper
import           Hyper.Infer
import           Hyper.Recurse
import           Hyper.Unify
import           Hyper.Unify.Apply
import           Control.DeepSeq (rnf)
import           Control.Exception (evaluate)
import           Control.Lens (ASetter')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
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
    , UnifyGen m T.Type
    , UnifyGen m T.Row
    , HFunctor z
    ) =>
    ASetter' env (Tree Scope (UVarOf m)) -> Tree (Ann z) Term -> m a -> m a
localInitEnv inferEnv e action =
    do
        addScope <- loadDeps (pruneDeps e allDeps)
        local (inferEnv %~ addScope) action

toAnn :: HPlain Term -> Tree (Ann (Const ())) Term
toAnn = wrap (\_ x -> Ann (Const ()) x) . (^. hPlain)

benchInferPure :: HPlain Term -> Benchmarkable
benchInferPure e =
    infer x
    <&> (^. hAnn . Lens._2 . inferResult)
    >>= applyBindings
    & localInitEnv id x
    & runPureInfer emptyScope (InferState emptyPureInferState varGen)
    & Lens._Right %~ (^. Lens._1)
    & rnf
    & evaluate
    & whnfIO
    where
        x = toAnn e

benchInferST :: HPlain Term -> Benchmarkable
benchInferST e =
    do
        vg <- newSTRef varGen
        localInitEnv Lens._1 x
            (infer x <&> (^. hAnn . Lens._2 . inferResult) >>= applyBindings) ^. _STInfer
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

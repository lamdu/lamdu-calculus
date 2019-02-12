{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}
import           AST.Infer
import           AST.Term.Nominal
import           AST.Term.Scheme
import           AST.Unify
import           Control.DeepSeq (rnf)
import           Control.Exception (evaluate)
import           Control.Lens (ASetter')
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.Reader
import           Control.Monad.ST.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.RWS (RWST(..))
import           Criterion (Benchmarkable, whnfIO)
import           Criterion.Main (bench, defaultMain)
import qualified Data.Map as Map
import           Data.STRef
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Calc.Definition (depsGlobalTypes, depsNominals)
import           Lamdu.Calc.Infer
import           Lamdu.Calc.Lens
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T
import           TestVals

import           Prelude.Compat

localInitEnv ::
    ( MonadReader env m
    , Unify m T.Type, Unify m T.Row
    ) =>
    ASetter' env (InferEnv (UVar m)) ->
    Set T.NominalId -> Set Var -> m a -> m a
localInitEnv l usedNominals usedGlobals action =
    do
        loadedNoms <-
            allDeps ^. depsNominals
            & Map.filterWithKey (\k _ -> k `Set.member` usedNominals)
            & traverse loadNominalDecl
        loadedSchemes <-
            allDeps ^. depsGlobalTypes
            & Map.filterWithKey (\k _ -> k `Set.member` usedGlobals)
            & traverse loadScheme
        let addScope x =
                x
                & ieScope . _ScopeTypes <>~ loadedSchemes
                & ieNominals <>~ loadedNoms
        local (l %~ addScope) action

varGen :: ([T.TypeVar], [T.RowVar])
varGen = (["t0", "t1", "t2", "t3", "t4"], ["r0", "r1", "r2", "r3", "r4"])

benchInferPure :: Val () -> Benchmarkable
benchInferPure e =
    runRWST (action ^. _PureInfer) emptyInferEnv (InferState emptyPureInferState varGen)
    <&> (^. _1)
    & rnf
    & evaluate
    & whnfIO
    where
        action =
            localInitEnv id
            (Set.fromList (e ^.. valNominals))
            (Set.fromList (e ^.. valGlobals mempty))
            (inferNode e <&> (^. iType) >>= applyBindings)

benchInferST :: Val () -> Benchmarkable
benchInferST e =
    do
        vg <- newSTRef varGen
        localInitEnv _1
            (Set.fromList (e ^.. valNominals))
            (Set.fromList (e ^.. valGlobals mempty))
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

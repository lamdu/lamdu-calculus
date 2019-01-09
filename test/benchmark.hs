{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}
import Prelude.Compat

import AST
import AST.Infer
import AST.Term.Nominal
import AST.Term.Scheme
import AST.Unify
import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Lens.Operators
import Control.Lens.Tuple
import Control.Monad.Reader
import Control.Monad.ST.Class
import Control.Monad.Trans.Maybe
import Criterion (Benchmarkable, whnfIO)
import Criterion.Main (bench, defaultMain)
import Data.STRef
import Lamdu.Calc.Infer
import Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T

import TestVals

localInitEnv :: STInfer s a -> STInfer s a
localInitEnv action =
    do
        loadedSchemes <- traverse loadScheme envTypes
        loadedNoms <- traverse loadNominalDecl envNominals
        let addScope x =
                x
                & ieScope . _ScopeTypes <>~ loadedSchemes
                & ieNominals <>~ loadedNoms
        local (_1 %~ addScope) action

inferExpr ::
    forall s.
    Val () ->
    STInfer s (Tree Pure T.Type)
inferExpr x =
    inferNode x
    <&> (^. iType)
    >>= applyBindings

benchInfer :: Val () -> Benchmarkable
benchInfer e =
    do
        varGen <- newSTRef (["t0", "t1", "t2", "t3", "t4"], ["r0", "r1", "r2", "r3", "r4"])
        localInitEnv (inferExpr e) ^. _STInfer
            & (`runReaderT` (emptyInferEnv, varGen))
            & runMaybeT
    & liftST >>= evaluate . rnf & whnfIO

benches :: [(String, Benchmarkable)]
benches =
    [ ("factorial", benchInfer factorialVal)
    , ("euler1", benchInfer euler1Val)
    , ("solveDepressedQuartic", benchInfer solveDepressedQuarticVal)
    , ("factors", benchInfer factorsVal)
    ]

main :: IO ()
main = defaultMain $ map (uncurry bench) benches

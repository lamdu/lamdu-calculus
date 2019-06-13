{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Lamdu.Calc.Infer.Refragment
    ( refragment
    ) where

import           AST (Tree, Ann(..), annotations, monoChildren)
import           AST.Infer (Infer(..), ITerm(..), IResult(..))
import           AST.Unify (unify, applyBindings, newUnbound)
import           AST.Unify.Binding (UVar)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Control.Monad.Reader as Reader
import           Control.Monad.State (MonadState(..), State, evalState)
import           Data.List (sortOn)
import           Lamdu.Calc.Infer (PureInfer, runPureInfer, InferState(..), emptyPureInferState, varGen)
import           Lamdu.Calc.Term (Term, Scope, emptyScope)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type)

inferBodies ::
    Tree UVar Type ->
    Tree (Ann a) Term ->
    PureInfer (Tree (Ann (a, Tree UVar Type, Tree UVar Type)) Term)
inferBodies extTyp (Ann a v) =
    v & monoChildren %~ childPre
    & inferBody
    >>=
    \(intTyp, infBody) ->
    monoChildren childPost infBody
    <&> Ann (a, extTyp, intTyp)
    where
        childPre x = Ann x (V.BLeaf V.LHole)
        childPost (ITerm x (IResult childTyp childScope) _) =
            inferBodies childTyp x
            & Reader.local (id .~ childScope)

tryUnify ::
    (Bool -> a -> r) ->
    (a, Tree UVar Type, Tree UVar Type) ->
    State InferState r
tryUnify mkRes (pl, outTyp, inTyp) =
    do
        s0 <- get
        case runPureInfer V.emptyScope s0 (unify outTyp inTyp) of
            Left{} -> pure (mkRes False pl)
            Right (t, s1) ->
                case runPureInfer V.emptyScope s1 (applyBindings t) of
                Left{} -> pure (mkRes False pl)
                Right{} -> mkRes True pl <$ put s1

refragment ::
    Ord priority =>
    (pl -> priority) ->
    (Bool -> pl -> r) ->
    (Tree UVar Type -> PureInfer (Tree Scope UVar -> Tree Scope UVar)) ->
    Tree (Ann pl) Term ->
    [r]
refragment order mkRes prepareInfer term =
    prep ^.. annotations
    & sortOn (order . (^. Lens._1))
    & traverse (tryUnify mkRes)
    & (`evalState` inferState)
    where
        (prep, inferState) = mPrep ^?! Lens._Right
        mPrep =
            do
                topVar <- newUnbound
                addDeps <- prepareInfer topVar
                inferBodies topVar term
                    & Reader.local addDeps
            & runPureInfer emptyScope (InferState emptyPureInferState varGen)

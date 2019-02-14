{-# LANGUAGE NoImplicitPrelude, TypeFamilies #-}

module Lamdu.Calc.Suggest
    ( value
    ) where

import AST
import AST.Infer
import AST.Term.FuncType
import AST.Term.Row
import Control.Lens
import Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T

import Prelude.Compat

class Applicative m => MonadGenVar m where
    genVar :: m Var

value :: MonadGenVar m => IResult Pure Term -> m [Tree (ITerm () Pure) Term]
value r@(IResult (Pure (T.TVariant (Pure (T.RExtend v)))) scope) =
    exts ^@.. itraversed <&> genOpt & sequenceA
    where
        Identity (FlatRowExtends exts _rest) =
            flatten (Identity . (^? _Pure . T._RExtend)) v
        genOpt (tag, innerTyp) =
            valueNoSplit (IResult innerTyp scope) <&> Inject tag <&> BInject
            <&> ITerm () r
value r = valueNoSplit r <&> (:[])

valueNoSplit :: MonadGenVar m => IResult Pure Term -> m (Tree (ITerm () Pure) Term)
valueNoSplit (IResult (Pure (T.TRecord r)) scope) =
    suggestRecord r scope
valueNoSplit r@(IResult (Pure (T.TFun f)) scope) =
    case f ^. funcIn . _Pure of
    T.TVariant v -> suggestCase v (IResult (f ^. funcOut) scope)
    _ ->
        Lam
        <$> genVar
        <*> valueNoSplit (IResult (f ^. funcOut) scope)
        <&> BLam
        <&> ITerm () r
valueNoSplit r = BLeaf LHole & ITerm () r & pure

suggestRecord :: MonadGenVar m => Tree Pure T.Row -> Tree ScopeTypes Pure -> m (Tree (ITerm () Pure) Term)
suggestRecord (Pure r) scope =
    case r of
    T.RVar{} -> BLeaf LHole & pure
    T.REmpty -> BLeaf LRecEmpty & pure
    T.RExtend (RowExtend tag fieldType rest) ->
        RowExtend tag
        <$> valueSimple (IResult fieldType scope)
        <*> suggestRecord rest scope
        <&> BRecExtend
    <&> ITerm () (IResult (Pure (T.TRecord (Pure r))) scope)

suggestCase :: MonadGenVar m => Tree Pure T.Row -> IResult Pure Term -> m (Tree (ITerm () Pure) Term)
suggestCase (Pure v) r@(IResult res scope) =
    case v of
    T.RVar{} -> BLeaf LHole & pure
    T.REmpty -> BLeaf LAbsurd & pure
    T.RExtend (RowExtend tag fieldType rest) ->
        RowExtend tag
        <$> valueSimple (IResult (Pure (T.TFun (FuncType fieldType res))) scope)
        <*> suggestCase rest r
        <&> BCase
    <&> ITerm () r

valueSimple :: MonadGenVar m => IResult Pure Term -> m (Tree (ITerm () Pure) Term)
valueSimple r@(IResult (Pure (T.TFun f)) scope) =
    Lam <$> genVar <*> valueSimple (IResult (f ^. funcOut) scope) <&> BLam
    <&> ITerm () r
valueSimple r = BLeaf LHole & ITerm () r & pure

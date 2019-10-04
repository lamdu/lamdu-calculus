{-# LANGUAGE NoImplicitPrelude, RankNTypes, NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, TypeApplications, FlexibleInstances #-}
{-# LANGUAGE DataKinds, ScopedTypeVariables, LambdaCase #-}
module Lamdu.Calc.Lens
    ( -- Leafs
      valHole    , valBodyHole
    , valVar     , valBodyVar
    , valRecEmpty, valBodyRecEmpty
    , valLiteral , valBodyLiteral
    , valLeafs
    -- Non-leafs
    , valGetField
    , valApply
    , valAbs
    , valTags
    , valGlobals
    , valNominals
    -- Subexpressions:
    , subExprPayloads
    , payloadsOf
    , HasTIds(..), tIds
    ) where

import           Hyper
import           Hyper.Type.Combinator.Ann (val)
import           Hyper.Recurse
import           Hyper.Type.AST.Nominal (ToNom(..), NominalInst(..), NominalDecl, nScheme)
import           Hyper.Type.AST.Row (RowExtend(..))
import           Hyper.Type.AST.Scheme (Scheme, _QVarInstances, sTyp)
import           Control.Lens (Traversal', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

tIds ::
    forall k expr.
    (RTraversable k, HasTIds expr) =>
    Traversal' (Tree k expr) T.NominalId
tIds f =
    withDict (recurse (Proxy @(RTraversable k))) $
    htraverse (Proxy @RTraversable #> bodyTIds f)

class HasTIds expr where
    bodyTIds :: RTraversable k => Traversal' (Tree expr k) T.NominalId

instance HasTIds T.Type where
    {-# INLINE bodyTIds #-}
    bodyTIds f (T.TInst (NominalInst tId args)) =
        NominalInst
        <$> f tId
        <*> htraverse (Proxy @HasTIds #> _QVarInstances %%~ traverse (tIds f))
            args
        <&> T.TInst
    bodyTIds f x = htraverse (Proxy @HasTIds #> tIds f) x

instance HasTIds T.Row where
    {-# INLINE bodyTIds #-}
    bodyTIds f = htraverse (Proxy @HasTIds #> tIds f)

instance HasTIds (Scheme T.Types T.Type) where
    bodyTIds = sTyp . tIds

instance HasTIds (NominalDecl T.Type) where
    bodyTIds = nScheme . bodyTIds

{-# INLINE valApply #-}
valApply :: Traversal' (Tree (Ann a) V.Term) (Tree (V.App V.Term) (Ann a))
valApply = val . V._BApp

{-# INLINE valAbs #-}
valAbs :: Traversal' (Tree (Ann a) V.Term) (Tree (V.Lam V.Var V.Term) (Ann a))
valAbs = val . V._BLam

{-# INLINE valHole #-}
valHole :: Traversal' (Val a) ()
valHole = val . valBodyHole

{-# INLINE valVar #-}
valVar :: Traversal' (Val a) V.Var
valVar = val . valBodyVar

{-# INLINE valRecEmpty #-}
valRecEmpty :: Traversal' (Val a) ()
valRecEmpty = val . valBodyRecEmpty

{-# INLINE valLiteral #-}
valLiteral :: Traversal' (Val a) V.PrimVal
valLiteral = val . valBodyLiteral

{-# INLINE valGetField #-}
valGetField  :: Traversal' (Tree (Ann a) V.Term) (Tree V.GetField (Ann a))
valGetField = val . V._BGetField

{-# INLINE valBodyHole #-}
valBodyHole :: Prism' (V.Term expr) ()
valBodyHole = V._BLeaf . V._LHole

{-# INLINE valBodyVar #-}
valBodyVar :: Prism' (V.Term expr) V.Var
valBodyVar = V._BLeaf . V._LVar

{-# INLINE valBodyRecEmpty #-}
valBodyRecEmpty :: Prism' (V.Term expr) ()
valBodyRecEmpty = V._BLeaf . V._LRecEmpty

{-# INLINE valBodyLiteral #-}
valBodyLiteral :: Prism' (V.Term expr) V.PrimVal
valBodyLiteral = V._BLeaf . V._LLiteral

{-# INLINE valLeafs #-}
valLeafs :: Lens.IndexedTraversal' a (Val a) V.Leaf
valLeafs f (Ann (Const pl) body) =
    case body of
    V.BLeaf l -> Lens.indexed f pl l <&> V.BLeaf
    _ -> htraverse1 (valLeafs f) body
    <&> Ann (Const pl)

{-# INLINE subExprPayloads #-}
subExprPayloads :: Lens.IndexedTraversal (Tree Pure V.Term) (Val a) (Val b) a b
subExprPayloads f x@(Ann (Const pl) body) =
    Ann
    <$> (Lens.indexed f (unwrap (const (^. val)) x) pl <&> Const)
    <*> (htraverse1 .> subExprPayloads) f body

{-# INLINE payloadsOf #-}
payloadsOf ::
    Lens.Fold (Tree Pure V.Term) a -> Lens.IndexedTraversal' (Tree Pure V.Term) (Val b) b
payloadsOf l =
    subExprPayloads . Lens.ifiltered predicate
    where
        predicate idx _ = Lens.has l idx

{-# INLINE valTags #-}
valTags :: Lens.Traversal' (Val a) T.Tag
valTags =
    val .
    \f ->
    \case
    V.BInject (V.Inject t v) ->
        V.Inject <$> f t <*> valTags f v <&> V.BInject
    V.BGetField (V.GetField r t) ->
        V.GetField <$> valTags f r <*> f t <&> V.BGetField
    V.BCase (RowExtend t v r) ->
        RowExtend <$> f t <*> valTags f v <*> valTags f r <&> V.BCase
    V.BRecExtend (RowExtend t v r) ->
        RowExtend <$> f t <*> valTags f v <*> valTags f r <&> V.BRecExtend
    body -> htraverse1 (valTags f) body

{-# INLINE valGlobals #-}
valGlobals ::
    HFunctor a =>
    Set V.Var ->
    Lens.IndexedFold (Tree a (Const ())) (Tree (Ann a) V.Term) V.Var
valGlobals scope f (Ann pl body) =
    case body of
    V.BLeaf (V.LVar v)
        | scope ^. Lens.contains v -> V.LVar v & V.BLeaf & pure
        | otherwise -> Lens.indexed f (hmap (\_ _ -> Const ()) pl) v <&> V.LVar <&> V.BLeaf
    V.BLam (V.Lam var lamBody) ->
        valGlobals (Set.insert var scope) f lamBody
        <&> V.Lam var <&> V.BLam
    _ -> (htraverse1 . valGlobals scope) f body
    <&> Ann pl

{-# INLINE valNominals #-}
valNominals :: Lens.Traversal' (Tree (Ann a) V.Term) T.NominalId
valNominals =
    val .
    \f ->
    \case
    V.BLeaf (V.LFromNom nomId) -> f nomId <&> V.LFromNom <&> V.BLeaf
    V.BToNom (ToNom nomId x) ->
        ToNom
        <$> f nomId
        <*> valNominals f x
        <&> V.BToNom
    body -> body & htraverse1 . valNominals %%~ f

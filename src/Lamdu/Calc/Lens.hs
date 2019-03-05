{-# LANGUAGE NoImplicitPrelude, RankNTypes, NoMonomorphismRestriction, FlexibleContexts, TypeFamilies, TypeApplications #-}
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
    -- Pure vals:
    , pureValBody
    , pureValApply
    --
    , valTags, bodyTags, biTraverseBodyTags
    , valGlobals
    , valNominals
    -- Subexpressions:
    , subExprPayloads
    , subExprs
    , payloadsIndexedByPath
    , payloadsOf
    , HasTIds(..), tIds
    , itermAnn
    , flatRow
    ) where

import           AST (Tree, Pure(..), _Pure, Children(..), Recursive(..), recursiveChildren)
import           AST.Class.Children.Mono (monoChildren)
import           AST.Infer (ITerm(..), IResult)
import           AST.Knot.Ann (Ann(..), annotations, val)
import           AST.Term.Nominal (ToNom(..), NominalInst(..))
import           AST.Term.Row (RowExtend(..), FlatRowExtends(..), flattenRow, unflattenRow)
import           AST.Term.Scheme (_QVarInstances)
import           Control.Lens (Traversal', Prism', Iso', iso)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

tIds ::
    (Recursive Children k, HasTIds expr) =>
    Traversal' (Tree k expr) T.NominalId
tIds f = recursiveChildren (Proxy @Children) (bodyTIds f)

class HasTIds expr where
    bodyTIds :: Recursive Children k => Traversal' (Tree expr k) T.NominalId

instance HasTIds T.Type where
    {-# INLINE bodyTIds #-}
    bodyTIds f (T.TInst (NominalInst tId args)) =
        NominalInst
        <$> f tId
        <*> children (Proxy @HasTIds) (_QVarInstances %%~ traverse (tIds f))
            args
        <&> T.TInst
    bodyTIds f x = children (Proxy @HasTIds) (tIds f) x

instance HasTIds T.Row where
    {-# INLINE bodyTIds #-}
    bodyTIds f = children (Proxy @HasTIds) (tIds f)

{-# INLINE valApply #-}
valApply :: Traversal' (Val a) (Tree (V.Apply V.Term) (Ann a))
valApply = val . V._BApp

{-# INLINE valAbs #-}
valAbs :: Traversal' (Val a) (Tree (V.Lam V.Var V.Term) (Ann a))
valAbs = val . V._BLam

{-# INLINE pureValBody #-}
pureValBody :: Iso' (Val ()) (Tree V.Term (Ann ()))
pureValBody = iso (^. val) (Ann ())

{-# INLINE pureValApply #-}
pureValApply :: Prism' (Val ()) (Tree (V.Apply V.Term) (Ann ()))
pureValApply = pureValBody . V._BApp

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
valGetField  :: Traversal' (Val a) (V.GetField (Val a))
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
valLeafs f (Ann pl body) =
    case body of
    V.BLeaf l -> Lens.indexed f pl l <&> V.BLeaf
    _ -> monoChildren (valLeafs f) body
    <&> Ann pl

{-# INLINE subExprPayloads #-}
subExprPayloads :: Lens.IndexedTraversal (Val ()) (Val a) (Val b) a b
subExprPayloads f x@(Ann pl body) =
    Ann
    <$> Lens.indexed f (x & annotations .~ ()) pl
    <*> (monoChildren .> subExprPayloads) f body

{-# INLINE subExprs #-}
subExprs :: Lens.Fold (Val a) (Val a)
subExprs =
    Lens.folding f
    where
        f x = x : x ^.. val . monoChildren . subExprs

{-# INLINE payloadsIndexedByPath #-}
payloadsIndexedByPath ::
    Lens.IndexedTraversal
    [Val ()]
    (Val a)
    (Val b)
    a b
payloadsIndexedByPath f =
    go f []
    where
        go ::
            ( Lens.Indexable [Tree (Ann ()) V.Term] p, Applicative f
            ) =>
            p a (f b) -> [Tree (Ann ()) V.Term] -> Val a -> f (Val b)
        go g path x@(Ann pl body) =
            Ann
            <$> Lens.indexed g newPath pl
            <*> monoChildren (go g newPath) body
            where
                newPath = (x & annotations .~ ()) : path

{-# INLINE payloadsOf #-}
payloadsOf ::
    Lens.Fold (Tree V.Term (Ann ())) a -> Lens.IndexedTraversal' (Val ()) (Val b) b
payloadsOf body =
    subExprPayloads . Lens.ifiltered predicate
    where
        predicate idx _ = Lens.has (val . body) idx

{-# INLINE biTraverseBodyTags #-}
biTraverseBodyTags ::
    Applicative f =>
    (T.Tag -> f T.Tag) -> (Val a -> f (Val b)) ->
    Tree V.Term (Ann a) -> f (Tree V.Term (Ann b))
biTraverseBodyTags onTag onChild body =
    case body of
    V.BInject (V.Inject t v) ->
        V.BInject <$> (V.Inject <$> onTag t <*> onChild v)
    V.BGetField (V.GetField r t) ->
        V.BGetField <$> (V.GetField <$> onChild r <*> onTag t)
    V.BCase (RowExtend t v r) ->
        V.BCase <$> (RowExtend <$> onTag t <*> onChild v <*> onChild r)
    V.BRecExtend (RowExtend t v r) ->
        V.BRecExtend <$> (RowExtend <$> onTag t <*> onChild v <*> onChild r)
    _ -> monoChildren onChild body

{-# INLINE bodyTags #-}
bodyTags :: Lens.Traversal' (Tree V.Term (Ann a)) T.Tag
bodyTags f = biTraverseBodyTags f pure

{-# INLINE valTags #-}
valTags :: Lens.Traversal' (Val a) T.Tag
valTags f = val $ biTraverseBodyTags f (valTags f)

{-# INLINE valGlobals #-}
valGlobals :: Set V.Var -> Lens.IndexedFold a (Val a) V.Var
valGlobals scope f (Ann pl body) =
    case body of
    V.BLeaf (V.LVar v)
        | scope ^. Lens.contains v -> V.LVar v & V.BLeaf & pure
        | otherwise -> Lens.indexed f pl v <&> V.LVar <&> V.BLeaf
    V.BLam (V.Lam var lamBody) ->
        valGlobals (Set.insert var scope) f lamBody
        <&> V.Lam var <&> V.BLam
    _ -> (monoChildren . valGlobals scope) f body
    <&> Ann pl

{-# INLINE valNominals #-}
valNominals :: Lens.Traversal' (Val a) T.NominalId
valNominals f (Ann pl body) =
    case body of
    V.BLeaf (V.LFromNom nomId) -> f nomId <&> V.LFromNom <&> V.BLeaf
    V.BToNom (ToNom nomId x) ->
        ToNom
        <$> f nomId
        <*> valNominals f x
        <&> V.BToNom
    _ -> body & monoChildren . valNominals %%~ f
    <&> Ann pl

-- Lamdu-calculus uses a uniform type for all subexpression types, so
-- ITerm yields unnecessary power compared to Ann, and is less usable
itermAnn ::
    Lens.Iso
    (Tree (ITerm a n) V.Term)
    (Tree (ITerm b m) V.Term)
    (Tree (Ann (a, IResult n V.Term)) V.Term)
    (Tree (Ann (b, IResult m V.Term)) V.Term)
itermAnn =
    Lens.iso toAnn fromAnn
    where
        fromAnn (Ann (pl, ires) term) =
            term & monoChildren %~ fromAnn & ITerm pl ires
        toAnn (ITerm pl ires term) =
            term & monoChildren %~ toAnn & Ann (pl, ires)

flatRow ::
    Lens.Iso'
    (Tree Pure T.Row)
    (Tree (FlatRowExtends T.Tag T.Type T.Row) Pure)
flatRow =
    Lens.iso flatten unflatten
    where
        flatten =
            Lens.runIdentity .
            flattenRow (Lens.Identity . (^? _Pure . T._RExtend))
        unflatten =
            Lens.runIdentity .
            unflattenRow (Lens.Identity . Pure . T.RExtend)

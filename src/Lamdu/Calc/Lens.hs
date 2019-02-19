{-# LANGUAGE NoImplicitPrelude, RankNTypes, NoMonomorphismRestriction, FlexibleContexts, TypeFamilies #-}
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
    -- Type traversals:
    , schemeTags, schemeGetTags
    , compositeTypes
    , compositeTags
    , compositeFieldTags, compositeFields
    , nextLayer
    , typeTIds
    , typeTags
    ) where

import           AST (Tree)
import           AST.Class.Children.Mono (monoChildren)
import           AST.Knot.Ann (Ann(..), annotations, val)
import           AST.Term.Nominal (ToNom(..))
import           AST.Term.Row (RowExtend(..))
import           Control.Lens (Traversal', Prism', Iso', iso)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Set.Lens (setmapped)
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..))
import qualified Lamdu.Calc.Type.Constraints as Constraints
import           Lamdu.Calc.Type.Scheme (Scheme(..))

import           Prelude.Compat

{-# INLINE compositeTypes #-}
compositeTypes :: Lens.Traversal' T.Row Type
compositeTypes f (T.RExtend tag typ rest) = T.RExtend tag <$> f typ <*> compositeTypes f rest
compositeTypes _ T.REmpty = pure T.REmpty
compositeTypes _ (T.RVar v) = pure (T.RVar v)

{-# INLINE nextLayer #-}
-- | Traverse direct types within a type
nextLayer :: Lens.Traversal' Type Type
nextLayer _ (T.TVar tv) = pure (T.TVar tv)
nextLayer f (T.TFun a r) = T.TFun <$> f a <*> f r
nextLayer f (T.TInst tid m) = T.TInst tid <$> Lens.traverse f m
nextLayer f (T.TRecord p) = T.TRecord <$> compositeTypes f p
nextLayer f (T.TVariant s) = T.TVariant <$> compositeTypes f s

{-# INLINE typeTIds #-}
typeTIds :: Lens.Traversal' Type T.NominalId
typeTIds f (T.TInst tId args) =
    T.TInst <$> f tId <*> Lens.traverse (typeTIds f) args
typeTIds f x = nextLayer (typeTIds f) x

{-# INLINE schemeTags #-}
schemeTags :: Lens.Setter' Scheme T.Tag
schemeTags f (Scheme tvs constraints typ) =
    Scheme tvs
    <$> (constraintsTagsSet . setmapped) f constraints
    <*> typeTags f typ

schemeGetTags :: Lens.Fold Scheme T.Tag
schemeGetTags =
    Lens.folding $
    \(Scheme _tvs constraints typ) ->
    constraints ^.. constraintsTagsSet . Lens.folded
    ++ typ ^.. typeTags

{-# INLINE typeTags #-}
typeTags :: Lens.Traversal' Type T.Tag
typeTags f (T.TRecord composite) = T.TRecord <$> compositeTags f composite
typeTags f (T.TVariant composite) = T.TVariant <$> compositeTags f composite
typeTags f x = nextLayer (typeTags f) x

{-# INLINE constraintsTagsSet #-}
constraintsTagsSet :: Traversal' Constraints (Set T.Tag)
constraintsTagsSet = Constraints.compositeVars . traverse . Constraints.forbiddenFields

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

{-# INLINE compositeFields #-}
compositeFields :: Traversal' T.Row (T.Tag, Type)
compositeFields f (T.RExtend tag typ rest) =
    uncurry T.RExtend <$> f (tag, typ) <*> compositeFields f rest
compositeFields _ r = pure r

{-# INLINE compositeFieldTags #-}
compositeFieldTags :: Traversal' T.Row T.Tag
compositeFieldTags = compositeFields . Lens._1

{-# INLINE compositeTags #-}
compositeTags :: Traversal' T.Row T.Tag
compositeTags f = compositeFields $ \(tag, typ) -> (,) <$> f tag <*> typeTags f typ

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
    V.BFromNom (V.Nom nomId x) ->
        V.Nom <$> f nomId <*> valNominals f x <&> V.BFromNom
    V.BToNom (ToNom nomId x) ->
        ToNom <$> f nomId <*> valNominals f x <&> V.BToNom
    _ -> body & monoChildren . valNominals %%~ f
    <&> Ann pl

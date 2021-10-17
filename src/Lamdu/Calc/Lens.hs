{-# LANGUAGE NoImplicitPrelude, RankNTypes, NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, TypeApplications, FlexibleInstances #-}
{-# LANGUAGE DataKinds, ScopedTypeVariables, LambdaCase, TypeOperators #-}
module Lamdu.Calc.Lens
    ( -- Leafs
      valHole    , valBodyHole
    , valVar
    , valLiteral , valBodyLiteral
    , valLeafs
    -- Non-leafs
    , valApply
    , valTags
    , valGlobals
    , valNominals
    -- Subexpressions:
    , subExprPayloads
    , payloadsOf
    , HasTIds(..), tIds, qVarIds
    , HasQVarIds(..)
    , HasQVar(..), qvarsQVarIds
    ) where

import           Control.Lens (Traversal', Prism')
import qualified Control.Lens as Lens
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Hyper
import           Hyper.Recurse
import           Hyper.Syntax.Nominal (ToNom(..), NominalInst(..), NominalDecl, nScheme)
import           Hyper.Syntax.Row (RowExtend(..))
import           Hyper.Syntax.Scheme (Scheme, QVars, _QVars, QVarInstances, _QVarInstances, sTyp)
import           Hyper.Type.Prune (Prune, _Unpruned)
import           Lamdu.Calc.Identifier (Identifier)
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T
import           Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..))

import           Lamdu.Calc.Internal.Prelude

tIds ::
    forall k expr.
    (RTraversable k, HasTIds expr) =>
    Traversal' (k # expr) T.NominalId
tIds f =
    withDict (recurse (Proxy @(RTraversable k))) $
    htraverse (Proxy @RTraversable #> bodyTIds f)

qVarIds ::
    forall k expr.
    (RTraversable k, HasQVarIds expr) =>
    Traversal' (k # expr) Identifier
qVarIds f =
    withDict (recurse (Proxy @(RTraversable k))) $
    htraverse (Proxy @RTraversable #> bodyQVarIds f)

class HasTIds expr where
    bodyTIds :: RTraversable k => Traversal' (expr # k) T.NominalId

class HasQVarIds expr where
    bodyQVarIds :: RTraversable k => Traversal' (expr # k) Identifier -- only a legal traversal if keys not modified to be duplicates!

unsafeMapList :: Ord k1 => Lens.Iso (Map k0 v0) (Map k1 v1) [(k0, v0)] [(k1, v1)]
unsafeMapList = Lens.iso (^@.. Lens.itraversed) Map.fromList

class (HasQVarIds expr, Ord (QVar expr)) => HasQVar expr where
    qvarId :: Proxy expr -> Lens.Iso' (QVar expr) Identifier

instance HasQVar T.Type where qvarId _ = T._Var
instance HasQVar T.Row where qvarId _ = T._Var

instance HasTIds T.Type where
    {-# INLINE bodyTIds #-}
    bodyTIds f (T.TInst (NominalInst tId args)) =
        NominalInst
        <$> f tId
        <*> htraverse (Proxy @HasTIds #> (_QVarInstances . traverse . tIds) f)
            args
        <&> T.TInst
    bodyTIds f x = htraverse (Proxy @HasTIds #> tIds f) x

instance HasQVarIds T.Type where
    bodyQVarIds f (T.TInst (NominalInst tId args)) =
        NominalInst tId
        <$> htraverse (Proxy @HasQVar #> qvarInstancesQVarIds f) args
        <&> T.TInst
    bodyQVarIds f (T.TVar v) = T._Var f v <&> T.TVar
    bodyQVarIds f x = htraverse (Proxy @HasQVar #> qVarIds f) x

qvarInstancesQVarIds :: forall expr h. (HasQVar expr, RTraversable h) => Traversal' (QVarInstances h # expr) Identifier
qvarInstancesQVarIds f =
    (_QVarInstances . unsafeMapList . traverse)
    (\(k, typ) ->
        (,) <$> qvarId (Proxy @expr) f k <*> qVarIds f typ)

instance HasTIds T.Row where
    {-# INLINE bodyTIds #-}
    bodyTIds f = htraverse (Proxy @HasTIds #> tIds f)

instance HasQVarIds T.Row where
    bodyQVarIds f = htraverse (Proxy @HasQVarIds #> qVarIds f)

instance HasTIds (Scheme T.Types T.Type) where
    bodyTIds = sTyp . tIds

qvarsQVarIds ::
    forall expr.
    HasQVar expr =>
    Traversal' (QVars # expr) Identifier
qvarsQVarIds =
    _QVars . unsafeMapList . traverse . Lens._1 . qvarId (Proxy @expr)

instance HasTIds (NominalDecl T.Type) where
    bodyTIds = nScheme . bodyTIds

{-# INLINE valApply #-}
valApply :: Traversal' (Ann a # V.Term) (V.App V.Term # Ann a)
valApply = hVal . V._BApp

{-# INLINE valHole #-}
valHole :: Traversal' (Ann a # V.Term) ()
valHole = hVal . valBodyHole

{-# INLINE valVar #-}
valVar :: Traversal' (Ann a # V.Term) V.Var
valVar = hVal . valBodyVar

{-# INLINE valLiteral #-}
valLiteral :: Traversal' (Ann a # V.Term) V.PrimVal
valLiteral = hVal . valBodyLiteral

{-# INLINE valBodyHole #-}
valBodyHole :: Prism' (V.Term expr) ()
valBodyHole = V._BLeaf . V._LHole

{-# INLINE valBodyVar #-}
valBodyVar :: Prism' (V.Term expr) V.Var
valBodyVar = V._BLeaf . V._LVar

{-# INLINE valBodyLiteral #-}
valBodyLiteral :: Prism' (V.Term expr) V.PrimVal
valBodyLiteral = V._BLeaf . V._LLiteral

subTerms :: Lens.Traversal' (V.Term # k) (k # V.Term)
subTerms f =
    htraverse
    ( \case
        HWitness V.W_Term_Term -> f
        HWitness V.W_Term_HCompose_Prune_Type -> pure
    )

{-# INLINE valLeafs #-}
valLeafs :: Lens.IndexedTraversal' (a # V.Term) (Ann a # V.Term) V.Leaf
valLeafs f (Ann pl body) =
    case body of
    V.BLeaf l -> Lens.indexed f pl l <&> V.BLeaf
    _ -> subTerms (valLeafs f) body
    <&> Ann pl

{-# INLINE subExprPayloads #-}
subExprPayloads :: Lens.IndexedTraversal' (Pure # V.Term) (Val a) a
subExprPayloads f x@(Ann (Const pl) body) =
    Ann
    <$> (Lens.indexed f (unwrap (const (^. hVal)) x) pl <&> Const)
    <*> (subTerms .> subExprPayloads) f body

{-# INLINE payloadsOf #-}
payloadsOf ::
    Lens.Fold (Pure # V.Term) a -> Lens.IndexedTraversal' (Pure # V.Term) (Val b) b
payloadsOf l =
    subExprPayloads . Lens.ifiltered predicate
    where
        predicate idx _ = Lens.has l idx

leafTags :: Lens.Traversal' V.Leaf T.Tag
leafTags f (V.LInject t) = f t <&> V.LInject
leafTags f (V.LGetField t) = f t <&> V.LGetField
leafTags _ x = pure x

{-# INLINE valTags #-}
valTags :: Lens.Traversal' (Ann a # V.Term) T.Tag
valTags =
    hVal .
    \f ->
    \case
    V.BLeaf l -> leafTags f l <&> V.BLeaf
    V.BCase (RowExtend t v r) ->
        RowExtend <$> f t <*> valTags f v <*> valTags f r <&> V.BCase
    V.BRecExtend (RowExtend t v r) ->
        RowExtend <$> f t <*> valTags f v <*> valTags f r <&> V.BRecExtend
    body ->
        htraverse
        ( \case
            HWitness V.W_Term_Term -> valTags f
            HWitness V.W_Term_HCompose_Prune_Type -> typeTags f
        ) body

typeTags :: Lens.Traversal' (Ann a # HCompose Prune T.Type) T.Tag
typeTags f =
    (hVal . hcomposed _Unpruned)
    ( htraverse
        ( \case
            HWitness T.W_Type_Type -> (_HCompose . typeTags) f
            HWitness T.W_Type_Row -> (_HCompose . rowTags) f
            HWitness (T.E_Type_NominalInst_NominalId_Types (HWitness T.W_Types_Type)) -> (_HCompose . typeTags) f
            HWitness (T.E_Type_NominalInst_NominalId_Types (HWitness T.W_Types_Row)) -> (_HCompose . rowTags) f
        )
    )

rowTags :: Lens.Traversal' (Ann a # HCompose Prune T.Row) T.Tag
rowTags =
    hVal . hcomposed _Unpruned . T._RExtend . onRExtend
    where
        onRExtend f (RowExtend tag val rest) =
            RowExtend
            <$> f tag
            <*> (_HCompose . typeTags) f val
            <*> (_HCompose . rowTags) f rest

{-# INLINE valGlobals #-}
valGlobals ::
    Set V.Var ->
    Lens.IndexedFold (a # V.Term) (Ann a # V.Term) V.Var
valGlobals scope f (Ann pl body) =
    case body of
    V.BLeaf (V.LVar v)
        | scope ^. Lens.contains v -> V.LVar v & V.BLeaf & pure
        | otherwise -> Lens.indexed f pl v <&> V.LVar <&> V.BLeaf
    V.BLam (V.TypedLam var typ lamBody) ->
        valGlobals (Set.insert var scope) f lamBody
        <&> V.TypedLam var typ <&> V.BLam
    _ ->
        htraverse
        ( \case
            HWitness V.W_Term_Term -> valGlobals scope f
            HWitness V.W_Term_HCompose_Prune_Type -> pure
        ) body
    <&> Ann pl

{-# INLINE valNominals #-}
valNominals :: Lens.Traversal' (Ann a # V.Term) T.NominalId
valNominals =
    hVal .
    \f ->
    \case
    V.BLeaf (V.LFromNom nomId) -> f nomId <&> V.LFromNom <&> V.BLeaf
    V.BToNom (ToNom nomId x) ->
        ToNom
        <$> f nomId
        <*> valNominals f x
        <&> V.BToNom
    body ->
        htraverse
        ( \case
            HWitness V.W_Term_Term -> valNominals f
            HWitness V.W_Term_HCompose_Prune_Type -> typeNominals f
        ) body

{-# INLINE typeNominals #-}
typeNominals :: Lens.Traversal' (Ann a # HCompose Prune T.Type) T.NominalId
typeNominals =
    hVal . hcomposed _Unpruned .
    \f ->
    \case
    T.TInst (NominalInst nomId args) ->
        NominalInst
        <$> f nomId
        <*> htraverse
            ( \case
                HWitness T.W_Types_Type -> (_QVarInstances . traverse . _HCompose . typeNominals) f
                HWitness T.W_Types_Row -> (_QVarInstances . traverse . _HCompose . rowNominals) f
            ) args
        <&> T.TInst
    body ->
        htraverse
        ( \case
            HWitness T.W_Type_Type -> (_HCompose . typeNominals) f
            HWitness T.W_Type_Row -> (_HCompose . rowNominals) f
            HWitness (T.E_Type_NominalInst_NominalId_Types (HWitness T.W_Types_Type)) -> (_HCompose . typeNominals) f
            HWitness (T.E_Type_NominalInst_NominalId_Types (HWitness T.W_Types_Row)) -> (_HCompose . rowNominals) f
        ) body

{-# INLINE rowNominals #-}
rowNominals :: Lens.Traversal' (Ann a # HCompose Prune T.Row) T.NominalId
rowNominals =
    hVal . hcomposed _Unpruned .
    \f ->
    htraverse
    ( \case
        HWitness T.W_Row_Type -> (_HCompose . typeNominals) f
        HWitness T.W_Row_Row -> (_HCompose . rowNominals) f
    )

{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, FlexibleContexts, RankNTypes, StandaloneDeriving, TemplateHaskell, UndecidableInstances, GeneralizedNewtypeDeriving #-}

module Data.Tree.Diverse
    ( Node(..), _Node
    , Children(..), overChildren
    , leaf, hoist
    , Ann(..), ann, val
    , annotations
    ) where

import           Control.Lens (Lens)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

newtype Node f expr = Node (f (expr f))
    deriving Generic
deriving instance Eq (f (expr f)) => Eq (Node f expr)
deriving instance Ord (f (expr f)) => Ord (Node f expr)
deriving instance Show (f (expr f)) => Show (Node f expr)
deriving instance Pretty (f (expr f)) => Pretty (Node f expr)
deriving instance Binary (f (expr f)) => Binary (Node f expr)

Lens.makePrisms ''Node

class Children expr where
    children ::
        (Applicative f, Functor n, Functor m) =>
        (forall sub. Children sub => Node n sub -> f (Node m sub)) ->
        expr n -> f (expr m)

overChildren ::
    (Children expr, Functor n, Functor m) =>
    (forall sub. Children sub => Node n sub -> Node m sub) ->
    expr n -> expr m
overChildren f = runIdentity . children (Identity . f)

instance Children (Const val) where
    children _ (Const x) = pure (Const x)

leaf ::
    (Functor n, Functor m) =>
    Lens (n a) (m b) (Node n (Const a)) (Node m (Const b))
leaf f x =
    x
    <&> Lens.Const
    & Lens.from _Node f
    <&> fmap Lens.getConst

hoist ::
    (Children expr, Functor f, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoist f = overChildren (_Node %~ f . fmap (hoist f))

-- Annotate tree nodes
data Ann a v = Ann
    { _ann :: a
    , _val :: v
    } deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
instance (Binary a, Binary v) => Binary (Ann a v)
Lens.makeLenses ''Ann

instance (Pretty a, Pretty v) => Pretty (Ann a v) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

annotations ::
    Children e =>
    Lens.Traversal
    (Node (Ann a) e)
    (Node (Ann b) e)
    a b
annotations f (Node (Ann pl x)) =
    Ann <$> f pl <*> children (annotations f) x <&> Node

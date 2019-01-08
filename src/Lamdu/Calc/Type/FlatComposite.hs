{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}
module Lamdu.Calc.Type.FlatComposite
    ( FlatComposite(..), fields, extension
    , fromComposite
    , toComposite
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

data FlatComposite = FlatComposite
    { _fields :: Map T.Tag Type
    , _extension :: Maybe (T.Var T.Row) -- TyVar of more possible fields
    } deriving Show

Lens.makeLenses ''FlatComposite

-- From a record type to a sorted list of fields
fromComposite :: T.Row -> FlatComposite
fromComposite (T.RExtend name typ rest) = fromComposite rest & fields %~ Map.insert name typ
fromComposite T.REmpty                  = FlatComposite Map.empty Nothing
fromComposite (T.RVar name)             = FlatComposite Map.empty (Just name)

toComposite :: FlatComposite -> T.Row
toComposite (FlatComposite fs ext) =
    Map.foldrWithKey T.RExtend (maybe T.REmpty T.RVar ext) fs

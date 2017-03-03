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

data FlatComposite p = FlatComposite
    { _fields :: Map T.Tag Type
    , _extension :: Maybe (T.Var (T.Composite p)) -- TyVar of more possible fields
    } deriving (Show)

Lens.makeLenses ''FlatComposite

-- From a record type to a sorted list of fields
fromComposite :: T.Composite p -> FlatComposite p
fromComposite (T.CExtend name typ rest) = fromComposite rest & fields %~ Map.insert name typ
fromComposite T.CEmpty                  = FlatComposite Map.empty Nothing
fromComposite (T.CVar name)             = FlatComposite Map.empty (Just name)

toComposite :: FlatComposite p -> T.Composite p
toComposite (FlatComposite fs ext) =
    Map.foldWithKey T.CExtend (maybe T.CEmpty T.CVar ext) fs

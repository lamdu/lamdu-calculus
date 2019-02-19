{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell #-}

module Lamdu.Calc.Type.Nominal
    ( Nominal(..), nomType, nomParams
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Map (Map)
import           GHC.Generics (Generic)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Scheme (Scheme)

import           Prelude.Compat

data Nominal = Nominal
    { _nomParams :: Map T.ParamId T.TypeVar
    , _nomType :: Scheme
    } deriving (Generic, Show, Eq, Ord)
instance NFData Nominal
instance Binary Nominal

Lens.makeLenses ''Nominal

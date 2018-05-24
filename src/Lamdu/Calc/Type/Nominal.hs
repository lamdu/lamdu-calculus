{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell #-}

module Lamdu.Calc.Type.Nominal
    ( Nominal(..), nomType, nomParams
    , NominalType(..), _NominalType, _OpaqueNominal
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Map (Map)
import           GHC.Generics (Generic)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Scheme (Scheme)

import           Prelude.Compat

data NominalType = NominalType Scheme | OpaqueNominal
    deriving (Generic, Show, Eq, Ord)
instance NFData NominalType
instance Binary NominalType

Lens.makePrisms ''NominalType

data Nominal = Nominal
    { _nomParams :: Map T.ParamId T.TypeVar
    , _nomType :: NominalType
    } deriving (Generic, Show, Eq, Ord)
instance NFData Nominal
instance Binary Nominal

Lens.makeLenses ''Nominal

-- | This module defines the 'Identifier' type and is meant to be
-- cheaply importable without creaeting import cycles.
{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving #-}
module Lamdu.Calc.Identifier
    (
    -- * Identifier type
      Identifier(..)
    -- * Hex representation of identifier bytes
    , identHex, identFromHex
    -- ** Laws

    -- |
    -- > identFromHex . identHex == Right
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Base16 as Hex
import qualified Data.ByteString.Char8 as BS
import qualified Data.Char as Char
import           Data.Hashable (Hashable)
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

-- | A low-level identifier data-type. This is used to identify
-- variables, type variables, tags and more.
newtype Identifier = Identifier ByteString
    deriving (Eq, Ord, Generic, Show, Binary, Hashable)
instance NFData Identifier
instance Pretty Identifier    where
    pPrint (Identifier x)
        | all Char.isPrint (BS.unpack x) = PP.text $ BS.unpack x
        | otherwise = PP.text $ identHex $ Identifier x
instance IsString Identifier  where fromString = Identifier . fromString
-- ^ IsString uses the underlying `ByteString.Char8` instance, use
-- only with Latin1 strings

-- | Convert the identifier bytes to a hex string
--
-- > > identHex (Identifier "a1")
-- > "6131"
identHex :: Identifier -> String
identHex (Identifier bs) = Hex.encode bs & BS.unpack

-- | Convert a hex string (e.g: one generated by 'identHex') to an
-- Identifier
--
-- > > identFromHex (Identifier "6131")
-- > Right (Identifier "a1")
identFromHex :: String -> Either String Identifier
identFromHex str
    | BS.null remain = Identifier result & Right
    | otherwise = "Hex doesnt parse: " ++ show str & Left
    where
        (result, remain) = BS.pack str & Hex.decode

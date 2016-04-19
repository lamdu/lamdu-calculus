{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving #-}
module Lamdu.Calc.Identifier
    ( Identifier(..), identHex, identFromHex
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS
import           Data.ByteString.Hex (showHexBytes, parseHexBytes)
import           Data.Hashable (Hashable)
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

newtype Identifier = Identifier ByteString
    deriving (Eq, Ord, Generic, Show, Binary, Hashable)
instance NFData Identifier
instance IsString Identifier  where fromString = Identifier . fromString
instance Pretty Identifier    where pPrint (Identifier x) = PP.text $ BS.unpack x

identHex :: Identifier -> String
identHex (Identifier bs) = showHexBytes bs

identFromHex :: String -> Either String Identifier
identFromHex str = parseHexBytes str <&> Identifier

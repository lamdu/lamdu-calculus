-- TODO: Find existing/create better alternative

{-# LANGUAGE NoImplicitPrelude #-}
module Data.ByteString.Hex
    ( showHexByte
    , showHexBytes
    , parseHexDigit
    , parseHexByte
    , parseHexBytes
    ) where

import           Control.Lens.Operators
import qualified Data.ByteString as SBS
import qualified Data.Char as Char
import           Data.Word (Word8)
import           Text.Printf (printf)

import Prelude.Compat

showHexByte :: Word8 -> String
showHexByte = printf "%02x"

showHexBytes :: SBS.ByteString -> String
showHexBytes = concatMap showHexByte . SBS.unpack

chunks :: Int -> [a] -> Either String [[a]]
chunks _ [] = Right []
chunks n xs
    | length firstChunk == n = chunks n rest <&> (firstChunk :)
    | otherwise = Left $ unwords ["Expecting chunks of size", show n, "found", show (length firstChunk)]
    where
        (firstChunk, rest) = splitAt n xs

parseHexDigit :: Char -> Either String Word8
parseHexDigit x
    | Char.isHexDigit x = Right (fromIntegral (Char.digitToInt x))
    | otherwise = Left $ "Expecting digit, found " ++ show x

parseHexByte :: String -> Either String Word8
parseHexByte [x,y] =
    (+)
    <$> (parseHexDigit x <&> (16 *))
    <*> parseHexDigit y
parseHexByte other =
    Left $ unwords ["Expecting two hex digits, found", show (length other), "characters"]

parseHexBytes :: String -> Either String SBS.ByteString
parseHexBytes str =
    chunks 2 str >>= mapM parseHexByte <&> SBS.pack

{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Calc.Pure
    ( abs, var, lit, recEmpty, app, recExtend, getField
    , inject, absurd, _case
    , fromNom, toNom
    , leaf, hole

    , record, lambda, lambdaRecord
    , ($$), ($$:), ($.), ($=)
    ) where

import           AST (Ann(..))
import           AST.Term.Row (RowExtend(..))
import           Data.ByteString (ByteString)
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat hiding (abs)

abs :: Monoid a => V.Var -> Val a -> Val a
abs name body =
    Ann mempty $ V.BLam $ V.Lam name body

leaf :: Monoid a => V.Leaf -> Val a
leaf = Ann mempty . V.BLeaf

var :: Monoid a => V.Var -> Val a
var = leaf . V.LVar

lit :: Monoid a => T.NominalId -> ByteString -> Val a
lit p d = leaf $ V.LLiteral $ V.PrimVal p d

recEmpty :: Monoid a => Val a
recEmpty = Ann mempty $ V.BLeaf V.LRecEmpty

app :: Monoid a => Val a -> Val a -> Val a
app f x = Ann mempty $ V.BApp $ V.Apply f x

recExtend :: Monoid a => T.Tag -> Val a -> Val a -> Val a
recExtend name typ rest = Ann mempty $ V.BRecExtend $ RowExtend name typ rest

getField :: Monoid a => Val a -> T.Tag -> Val a
getField r n = Ann mempty $ V.BGetField $ V.GetField r n

inject :: Monoid a => T.Tag -> Val a -> Val a
inject n r = Ann mempty $ V.BInject $ V.Inject n r

absurd :: Monoid a => Val a
absurd = leaf V.LAbsurd

_case :: Monoid a => T.Tag -> Val a -> Val a -> Val a
_case tag match mismatch = Ann mempty $ V.BCase $ RowExtend tag match mismatch

fromNom :: Monoid a => T.NominalId -> Val a -> Val a
fromNom tid v = Ann mempty $ V.BFromNom $ V.Nom tid v

toNom :: Monoid a => T.NominalId -> Val a -> Val a
toNom tid v = Ann mempty $ V.BToNom $ V.Nom tid v

hole :: Monoid a => Val a
hole = leaf V.LHole



infixl 4 $$
($$) :: Val () -> Val () -> Val ()
($$) = app

infixl 4 $$:
($$:) :: Val () -> [(T.Tag, Val ())] -> Val ()
func $$: fields = func $$ record fields

infixl 9 $.
($.) :: Val () -> T.Tag -> Val ()
($.) = getField

infixl 3 $=
($=) :: T.Tag -> Val () -> Val () -> Val ()
($=) = recExtend

record :: Monoid a => [(T.Tag, Val a)] -> Val a
record = foldr (uncurry recExtend) recEmpty

lambda :: Monoid a => V.Var -> (Val a -> Val a) -> Val a
lambda v body = abs v $ body $ var v

lambdaRecord :: Monoid a => V.Var -> [T.Tag] -> ([Val a] -> Val a) -> Val a
lambdaRecord v tags body =
    abs v $ body $ map (getField (var v)) tags

-- | Annotated (cofree) Expr.Val ASTs
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Lamdu.Calc.Val.Annotated
    ( Val(..), body, payload, alphaEq
    , pPrintUnannotated
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.Lens (Lens')
import           Data.Binary (Binary)
import qualified Data.Foldable as Foldable
import           Data.Hashable (Hashable(..))
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           GHC.Generics (Generic)
import           Lamdu.Calc.Val (Body(..))
import qualified Lamdu.Calc.Val as Val
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Val a = Val
    { _valPayload :: a
    , _valBody :: !(Body (Val a))
    } deriving (Functor, Foldable, Traversable, Generic, Show, Eq)
instance NFData a => NFData (Val a)
instance Hashable a => Hashable (Val a)
instance Binary a => Binary (Val a)

body :: Lens' (Val a) (Body (Val a))
body f (Val pl b) = Val pl <$> f b

payload :: Lens' (Val a) a
payload f (Val pl b) = (`Val` b) <$> f pl

instance Pretty a => Pretty (Val a) where
    pPrintPrec lvl prec (Val pl b)
        | PP.isEmpty plDoc = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

data EmptyDoc = EmptyDoc
instance Pretty EmptyDoc where
    pPrint _ = PP.empty

pPrintUnannotated :: Val a -> PP.Doc
pPrintUnannotated = pPrint . (EmptyDoc <$)

alphaEq :: Val () -> Val () -> Bool
alphaEq =
    go Map.empty
    where
        xToYConv xToY x =
            fromMaybe x $ Map.lookup x xToY
        go xToY (Val _ xBody) (Val _ yBody) =
            case (xBody, yBody) of
            (BLam (Val.Lam xvar xresult),
              BLam (Val.Lam yvar yresult)) ->
                go (Map.insert xvar yvar xToY) xresult yresult
            (BLeaf (Val.LVar x), BLeaf (Val.LVar y)) ->
                -- TODO: This is probably not 100% correct for various
                -- shadowing corner cases
                xToYConv xToY x == y
            (BLeaf x, BLeaf y) -> x == y
            (BApp x, BApp y) -> goRecurse x y
            (BGetField x, BGetField y) -> goRecurse x y
            (BRecExtend x, BRecExtend y) -> goRecurse x y
            (BCase x, BCase y) -> goRecurse x y
            (BInject x, BInject y) -> goRecurse x y
            (BFromNom x, BFromNom y) -> goRecurse x y
            (BToNom x, BToNom y) -> goRecurse x y
            (_, _) -> False
            where
                goRecurse x y = maybe False Foldable.and $ Val.match (go xToY) x y

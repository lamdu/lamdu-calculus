{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS -fno-warn-orphans #-} -- Arbitrary instances
module Lamdu.Calc.Val.Annotated.Arbitrary () where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (replicateM, join)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import qualified Control.Monad.Trans.Reader as Reader
import           Control.Monad.Trans.State (StateT, evalStateT)
import qualified Control.Monad.Trans.State as State
import qualified Data.ByteString as BS
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.String (IsString(..))
import           Lamdu.Calc.Identifier (Identifier(..))
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Scheme (Scheme)
import           Lamdu.Calc.Val.Annotated (Val(..))
import qualified Lamdu.Calc.Val as V
import           Test.QuickCheck (Arbitrary(..), Gen)
import qualified Test.QuickCheck.Gen as Gen

import           Prelude.Compat hiding (any)

data Env = Env
    { _envScope :: [V.Var]
    , __envGlobals :: Map V.Var Scheme
    }
envScope :: Lens' Env [V.Var]
envScope f e = mkEnv <$> f (_envScope e)
    where
        mkEnv x = e { _envScope = x }

type GenVal = ReaderT Env (StateT [V.Var] Gen)

liftGen :: Gen a -> GenVal a
liftGen = lift . lift

next :: GenVal V.Var
next = lift $ State.gets head <* State.modify tail

arbitraryLam :: Arbitrary a => GenVal (V.Lam (Val a))
arbitraryLam = do
    par <- next
    V.Lam par {-TODO: Arbitrary constraints on param types??-}
        <$> Reader.local (envScope %~ (par :)) arbitraryVal

arbitraryRecExtend :: Arbitrary a => GenVal (V.RecExtend (Val a))
arbitraryRecExtend =
    V.RecExtend <$> liftGen arbitrary <*> arbitraryVal <*> arbitraryVal

arbitraryCase :: Arbitrary a => GenVal (V.Case (Val a))
arbitraryCase =
    V.Case <$> liftGen arbitrary <*> arbitraryVal <*> arbitraryVal

arbitraryInject :: Arbitrary a => GenVal (V.Inject (Val a))
arbitraryInject =
    V.Inject <$> liftGen arbitrary <*> arbitraryVal

arbitraryGetField :: Arbitrary a => GenVal (V.GetField (Val a))
arbitraryGetField = V.GetField <$> arbitraryVal <*> liftGen arbitrary

arbitraryNom :: Arbitrary a => GenVal (V.Nom (Val a))
arbitraryNom = V.Nom <$> liftGen arbitrary <*> arbitraryVal

arbitraryApply :: Arbitrary a => GenVal (V.Apply (Val a))
arbitraryApply = V.Apply <$> arbitraryVal <*> arbitraryVal

arbitraryLeaf :: GenVal V.Leaf
arbitraryLeaf = do
    Env locals globals <- Reader.ask
    join . liftGen . Gen.elements $
        [ pure V.LHole
        , pure V.LRecEmpty
        , pure V.LAbsurd
        ] ++
        map (pure . V.LVar) locals ++
        map (pure . V.LVar) (Map.keys globals)

arbitraryBody :: Arbitrary a => GenVal (V.Body (Val a))
arbitraryBody =
    join . liftGen . Gen.frequency . (Lens.mapped . _2 %~ pure) $
    [ weight 2  $ V.BLam         <$> arbitraryLam
    , weight 2  $ V.BRecExtend   <$> arbitraryRecExtend
    , weight 2  $ V.BCase        <$> arbitraryCase
    , weight 2  $ V.BInject      <$> arbitraryInject
    , weight 2  $ V.BGetField    <$> arbitraryGetField
    , weight 2  $ V.BFromNom     <$> arbitraryNom
    , weight 2  $ V.BToNom       <$> arbitraryNom
    , weight 5  $ V.BApp         <$> arbitraryApply
    , weight 17 $ V.BLeaf        <$> arbitraryLeaf
    ]
    where
        weight = (,)

arbitraryVal :: Arbitrary a => GenVal (Val a)
arbitraryVal = Val <$> liftGen arbitrary <*> arbitraryBody

valGen :: Arbitrary a => Map V.Var Scheme -> Gen (Val a)
valGen globals =
    (`evalStateT` names) .
    (`runReaderT` Env [] globals) $
    arbitraryVal
    where
        names = fromString . (: []) <$> ['a'..]

instance Arbitrary Identifier where
    arbitrary = Identifier . BS.pack <$> replicateM 8 arbitrary

instance Arbitrary T.Tag where
    arbitrary = T.Tag <$> arbitrary

instance Arbitrary T.NominalId where
    arbitrary = T.NominalId <$> arbitrary

-- TODO: This instance doesn't know which Definitions exist in the
-- world so avoids DefinitionRef and only has valid ParameterRefs to
-- its own lambdas.
instance Arbitrary a => Arbitrary (Val a) where
    arbitrary = valGen Map.empty

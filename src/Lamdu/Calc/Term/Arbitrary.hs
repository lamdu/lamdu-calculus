{-# LANGUAGE NoImplicitPrelude, TypeFamilies, TemplateHaskell, StandaloneDeriving, GeneralizedNewtypeDeriving, ConstraintKinds, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-} -- Arbitrary instances
module Lamdu.Calc.Term.Arbitrary () where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (replicateM)
import qualified Data.ByteString as BS
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.Tree.Diverse.Arbitrary (ArbitraryWithContext(..), ArbitraryWithContextOf)
import           Lamdu.Calc.Identifier (Identifier(..))
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Scheme (Scheme)
import           Test.QuickCheck (Arbitrary(..))
import qualified Test.QuickCheck.Gen as Gen

import           Prelude.Compat hiding (any)

data Env = Env
    { _envScope :: Set Var
    , _envGlobals :: Map Var Scheme
    }
Lens.makeLenses ''Env

emptyEnv :: Env
emptyEnv = Env mempty mempty

inScope :: Env -> Var -> Bool
inScope env var =
    Lens.has (envScope . Lens.ix var) env ||
    Lens.has (envGlobals . Lens.ix var) env

instance Arbitrary Identifier where
    arbitrary = Identifier . BS.pack <$> replicateM 8 arbitrary
deriving instance Arbitrary Var
deriving instance Arbitrary T.Tag
deriving instance Arbitrary T.NominalId

instance Arbitrary Leaf where
    arbitrary = arbitraryCtx emptyEnv

instance ArbitraryWithContext Leaf where
    type Context Leaf = Env
    arbitraryCtx ctx =
        [ LHole
        , LRecEmpty
        , LAbsurd
        ]
        <> ( ctx ^.. envScope . Lens.folded
            <> ctx ^.. envGlobals . Lens.itraversed . Lens.asIndex
            <&> LVar)
        & Gen.elements

instance ArbitraryWithContextOf Env (f (Term f)) => Arbitrary (Term f) where
    arbitrary = arbitraryCtx emptyEnv

instance ArbitraryWithContextOf Env (f (Term f)) => ArbitraryWithContext (Term f) where
    type Context (Term f) = Env
    arbitraryCtx ctx =
        Gen.frequency
        [ (2, arbitraryLam <&> BLam)
        , (2, RecExtend <$> arbitrary <*> arbitraryCtx ctx <*> arbitraryCtx ctx <&> BRecExtend)
        , (2, Case <$> arbitrary <*> arbitraryCtx ctx <*> arbitraryCtx ctx <&> BCase)
        , (2, Inject <$> arbitrary <*> arbitraryCtx ctx <&> BInject)
        , (2, GetField <$> arbitraryCtx ctx <*> arbitrary <&> BGetField)
        , (2, arbitraryNom <&> BFromNom)
        , (2, arbitraryNom <&> BToNom)
        , (5, Apply <$> arbitraryCtx ctx <*> arbitraryCtx ctx <&> BApp)
        , (17, arbitraryCtx ctx <&> BLeaf)
        ]
        where
            arbitraryNom = Nom <$> arbitrary <*> arbitraryCtx ctx
            arbitraryLam =
                do
                    var <- Gen.suchThat arbitrary (not . inScope ctx)
                    arbitraryCtx (ctx & envScope . Lens.at var ?~ ()) <&> Lam var

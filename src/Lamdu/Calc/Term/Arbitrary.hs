{-# LANGUAGE NoImplicitPrelude, TypeFamilies, TemplateHaskell, StandaloneDeriving, GeneralizedNewtypeDeriving, ConstraintKinds, UndecidableInstances, FlexibleInstances #-}
{-# OPTIONS -fno-warn-orphans #-} -- Arbitrary instances
module Lamdu.Calc.Term.Arbitrary () where

import           AST (Tree)
import           AST.Knot.Ann.Arbitrary (ArbitraryWithContext(..), ArbitraryWithContextOf)
import           AST.Term.Nominal (ToNom(..))
import           AST.Term.Row (RowExtend(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (replicateM)
import qualified Data.ByteString as BS
import           Data.Set (Set)
import           Lamdu.Calc.Identifier (Identifier(..))
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T
import           Test.QuickCheck (Arbitrary(..))
import qualified Test.QuickCheck.Gen as Gen

import           Prelude.Compat hiding (any)

data Env = Env
    { _envScope :: Set Var
    , _envGlobals :: Set Var
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
            <> ctx ^.. envGlobals . Lens.folded
            <&> LVar)
        & Gen.elements

instance ArbitraryWithContextOf Env (Tree f Term) => Arbitrary (Tree Term f) where
    arbitrary = arbitraryCtx emptyEnv

instance ArbitraryWithContextOf Env (Tree f Term) => ArbitraryWithContext (Tree Term f) where
    type Context (Tree Term f) = Env
    arbitraryCtx ctx =
        Gen.frequency
        [ (2, arbitraryLam <&> BLam)
        , (2, RowExtend <$> arbitrary <*> arbitraryCtx ctx <*> arbitraryCtx ctx <&> BRecExtend)
        , (2, RowExtend <$> arbitrary <*> arbitraryCtx ctx <*> arbitraryCtx ctx <&> BCase)
        , (2, Inject <$> arbitrary <*> arbitraryCtx ctx <&> BInject)
        , (2, GetField <$> arbitraryCtx ctx <*> arbitrary <&> BGetField)
        , (2, ToNom <$> arbitrary <*> arbitraryCtx ctx <&> BToNom)
        , (5, Apply <$> arbitraryCtx ctx <*> arbitraryCtx ctx <&> BApp)
        , (17, arbitraryCtx ctx <&> BLeaf)
        ]
        where
            arbitraryLam =
                do
                    var <- Gen.suchThat arbitrary (not . inScope ctx)
                    arbitraryCtx (ctx & envScope . Lens.at var ?~ ()) <&> Lam var

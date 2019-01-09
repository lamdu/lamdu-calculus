{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, LambdaCase #-}

module Lamdu.Calc.Infer
    ( InferEnv(..), ieNominals, ieScope, ieScopeLevel
    , emptyInferEnv
    , STInfer(..), _STInfer
    ) where

import           AST
import           AST.Infer
import           AST.Term.Nominal
import           AST.Unify
import           AST.Unify.Binding.ST
import           AST.Unify.Generalize
import           Algebra.Lattice
import           Control.Applicative (Alternative(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader.Class
import           Control.Monad.ST
import           Control.Monad.ST.Class (MonadST(..))
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Reader (ReaderT)
import           Data.Map (Map)
import           Data.STRef
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

data InferEnv v = InferEnv
    { _ieNominals :: Map T.NominalId (Tree (LoadedNominalDecl T.Type) v)
    , _ieScope :: Tree ScopeTypes v
    , _ieScopeLevel :: ScopeLevel
    }
Lens.makeLenses ''InferEnv

emptyInferEnv :: InferEnv v
emptyInferEnv = InferEnv mempty (ScopeTypes mempty) bottom

type QVarGen = ([T.TypeVar], [T.RowVar])

newtype STInfer s a = STInfer
    (ReaderT (InferEnv (STVar s), STRef s QVarGen) (MaybeT (ST s)) a)
    deriving
    ( Functor, Alternative, Applicative, Monad, MonadST
    , MonadReader (InferEnv (STVar s), STRef s QVarGen)
    )
Lens.makePrisms ''STInfer

type instance UVar (STInfer s) = STVar s

instance MonadNominals T.NominalId T.Type (STInfer s) where
    getNominalDecl n =
        Lens.view (Lens._1 . ieNominals . Lens.at n) >>= maybe empty pure

instance HasScope (STInfer s) ScopeTypes where
    getScope = Lens.view (Lens._1 . ieScope)

instance LocalScopeType Var (Tree (STVar s) T.Type) (STInfer s) where
    localScopeType k v =
        local (Lens._1 . ieScope . _ScopeTypes . Lens.at k ?~ monomorphic v)

instance MonadScopeConstraints ScopeLevel (STInfer s) where
    scopeConstraints = Lens.view (Lens._1 . ieScopeLevel)

instance MonadQuantify ScopeLevel T.TypeVar (STInfer s) where
    newQuantifiedVariable _ =
        do
            gen <- Lens.view Lens._2
            readSTRef gen & liftST >>=
                \case
                ([], _) -> empty
                (x:xs, ys) -> x <$ liftST (writeSTRef gen (xs, ys))

instance MonadScopeConstraints T.RConstraints (STInfer s) where
    scopeConstraints = scopeConstraints <&> T.RowConstraints mempty

instance MonadQuantify T.RConstraints T.RowVar (STInfer s) where
    newQuantifiedVariable _ =
        do
            gen <- Lens.view Lens._2
            readSTRef gen & liftST >>=
                \case
                (_, []) -> empty
                (xs, y:ys) -> y <$ liftST (writeSTRef gen (xs, ys))

instance Unify (STInfer s) T.Type where
    binding = stBinding
    unifyError _ = empty

instance Unify (STInfer s) T.Row where
    binding = stBinding
    unifyError _ = empty
    structureMismatch = T.rStructureMismatch

{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, LambdaCase, DataKinds #-}

module Lamdu.Calc.Infer
    ( InferEnv(..), ieNominals, ieScope, ieScopeLevel
    , InferState(..), isBinding, isQVarGen
    , emptyInferEnv, emptyPureInferState
    , PureInfer(..), _PureInfer
    , STInfer(..), _STInfer
    ) where

import           AST
import           AST.Infer
import           AST.Term.Nominal
import           AST.Unify
import           AST.Unify.Binding.Pure
import           AST.Unify.Binding.ST
import           AST.Unify.Generalize
import           Algebra.Lattice
import           Control.Applicative (Alternative(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader.Class
import           Control.Monad.ST
import           Control.Monad.ST.Class (MonadST(..))
import           Control.Monad.State.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Reader (ReaderT)
import           Control.Monad.Trans.RWS (RWST)
import           Data.Functor.Const
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

data InferState = InferState
    { _isBinding :: Tree T.Types PureBinding
    , _isQVarGen :: QVarGen
    }
Lens.makeLenses ''InferState

newtype PureInfer a = PureInfer
    (RWST (InferEnv (Const Int)) () InferState Maybe a)
    deriving
    ( Functor, Alternative, Applicative, Monad
    , MonadReader (InferEnv (Const Int))
    , MonadState InferState
    )
Lens.makePrisms ''PureInfer

type instance UVar PureInfer = Const Int

instance MonadNominals T.NominalId T.Type PureInfer where
    {-# INLINE getNominalDecl #-}
    getNominalDecl n = Lens.view (ieNominals . Lens.at n) >>= maybe empty pure

instance HasScope PureInfer ScopeTypes where
    {-# INLINE getScope #-}
    getScope = Lens.view ieScope

instance LocalScopeType Var (Tree (Const Int) T.Type) PureInfer where
    {-# INLINE localScopeType #-}
    localScopeType k v = local (ieScope . _ScopeTypes . Lens.at k ?~ monomorphic v)

instance MonadScopeConstraints ScopeLevel PureInfer where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = Lens.view ieScopeLevel

instance MonadQuantify ScopeLevel T.TypeVar PureInfer where
    newQuantifiedVariable _ = isQVarGen . Lens._1 <<%= tail <&> head

instance MonadScopeConstraints T.RConstraints PureInfer where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = scopeConstraints <&> T.RowConstraints mempty

instance MonadQuantify T.RConstraints T.RowVar PureInfer where
    newQuantifiedVariable _ = isQVarGen . Lens._2 <<%= tail <&> head

instance Unify PureInfer T.Type where
    {-# INLINE binding #-}
    binding = pureBinding (isBinding . T.tType)
    unifyError _ = empty

instance Unify PureInfer T.Row where
    {-# INLINE binding #-}
    binding = pureBinding (isBinding . T.tRow)
    unifyError _ = empty
    {-# INLINE structureMismatch #-}
    structureMismatch = T.rStructureMismatch

emptyPureInferState :: Tree T.Types PureBinding
emptyPureInferState = T.Types emptyPureBinding emptyPureBinding

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

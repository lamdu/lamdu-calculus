{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, LambdaCase, DataKinds, FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Lamdu.Calc.Infer
    ( InferEnv(..), ieNominals, ieScope, ieScopeLevel
    , InferState(..), isBinding, isQVarGen
    , emptyInferEnv, emptyPureInferState
    , PureInferT(..), _PureInferT
    , PureInfer
    , STInfer(..), _STInfer
    , loadDeps
    , varGen
    ) where

import           AST
import           AST.Infer
import           AST.Term.Nominal
import           AST.Term.Scheme (loadScheme)
import           AST.Unify
import           AST.Unify.Binding.Pure
import           AST.Unify.Binding.ST
import           AST.Unify.Generalize
import           AST.Unify.Term
import           Algebra.Lattice
import           Control.Applicative (Alternative(..))
import qualified Control.Lens as Lens
import           Control.Lens (LensLike')
import           Control.Lens.Operators
import           Control.Monad.Except
import           Control.Monad.Reader.Class
import           Control.Monad.ST
import           Control.Monad.ST.Class (MonadST(..))
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.RWS (RWST)
import           Control.Monad.Trans.Reader (ReaderT)
import           Control.Monad.Trans.Writer (WriterT)
import           Data.Functor.Const
import           Data.Map (Map)
import           Data.Proxy (Proxy(..))
import           Data.STRef
import           Data.String (IsString(..))
import           Lamdu.Calc.Definition (Deps, depsNominals, depsGlobalTypes)
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

data QVarGen = QVarGen
    { _nextTV :: !Int
    , _nextRV :: !Int
    } deriving (Eq, Ord, Show)
Lens.makeLenses ''QVarGen

varGen :: QVarGen
varGen = QVarGen 0 0

data InferState = InferState
    { _isBinding :: Tree T.Types PureBinding
    , _isQVarGen :: QVarGen
    } deriving (Eq, Ord)
Lens.makeLenses ''InferState

newtype PureInferT m a = PureInferT
    (RWST (InferEnv (Const Int)) () InferState m a)
    deriving
    ( Functor, Alternative, Applicative, Monad
    , MonadReader (InferEnv (Const Int))
    , MonadError e
    , MonadState InferState
    , MonadTrans
    )
Lens.makePrisms ''PureInferT

type PureInfer = PureInferT (Either (Tree Pure T.TypeError))

type instance UVar PureInfer = Const Int

loadDeps ::
    (Unify m T.Row, Unify m T.Type) =>
    Deps -> m (InferEnv (UVar m) -> InferEnv (UVar m))
loadDeps deps =
    do
        loadedNoms <- deps ^. depsNominals & traverse loadNominalDecl
        loadedSchemes <- deps ^. depsGlobalTypes & traverse loadScheme
        pure $ \env ->
            env
            & ieScope . _ScopeTypes <>~ loadedSchemes
            & ieNominals <>~ loadedNoms

instance MonadNominals T.NominalId T.Type PureInfer where
    {-# INLINE getNominalDecl #-}
    getNominalDecl n =
        Lens.view (ieNominals . Lens.at n)
        >>= maybe (throwError (Pure (T.NominalNotFound n))) pure

instance HasScope PureInfer ScopeTypes where
    {-# INLINE getScope #-}
    getScope = Lens.view ieScope

instance LocalScopeType Var (Tree (Const Int) T.Type) PureInfer where
    {-# INLINE localScopeType #-}
    localScopeType k v = local (ieScope . _ScopeTypes . Lens.at k ?~ GMono v)

instance MonadScopeConstraints ScopeLevel PureInfer where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = Lens.view ieScopeLevel

nextTVNamePure ::
    (MonadState InferState m, IsString a) =>
    Char -> LensLike' ((,) Int) QVarGen Int -> m a
nextTVNamePure prefix lens =
    isQVarGen . lens <<%= (+1) <&> show <&> (prefix :) <&> fromString

instance MonadQuantify ScopeLevel T.TypeVar PureInfer where
    newQuantifiedVariable _ = nextTVNamePure 't' nextTV

instance MonadScopeConstraints T.RConstraints PureInfer where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = scopeConstraints <&> T.RowConstraints mempty

instance MonadQuantify T.RConstraints T.RowVar PureInfer where
    newQuantifiedVariable _ = nextTVNamePure 'r' nextRV

instance Unify PureInfer T.Type where
    {-# INLINE binding #-}
    binding = pureBinding (isBinding . T.tType)
    unifyError e =
        children (Proxy @(Recursive (Unify PureInfer))) applyBindings e
        >>= throwError . Pure . T.TypeError

instance Unify PureInfer T.Row where
    {-# INLINE binding #-}
    binding = pureBinding (isBinding . T.tRow)
    unifyError e =
        children (Proxy @(Recursive (Unify PureInfer))) applyBindings e
        >>= throwError . Pure . T.RowError
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
    {-# INLINE getNominalDecl #-}
    getNominalDecl n =
        Lens.view (Lens._1 . ieNominals . Lens.at n) >>= maybe empty pure

instance HasScope (STInfer s) ScopeTypes where
    {-# INLINE getScope #-}
    getScope = Lens.view (Lens._1 . ieScope)

instance LocalScopeType Var (Tree (STVar s) T.Type) (STInfer s) where
    {-# INLINE localScopeType #-}
    localScopeType k v =
        local (Lens._1 . ieScope . _ScopeTypes . Lens.at k ?~ GMono v)

instance MonadScopeConstraints ScopeLevel (STInfer s) where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = Lens.view (Lens._1 . ieScopeLevel)

nextTVNameST :: IsString a => Char -> Lens.ALens' QVarGen Int -> STInfer s a
nextTVNameST prefix lens =
    do
        genRef <- Lens.view Lens._2
        gen <- readSTRef genRef & liftST
        let res = prefix : show (gen ^# lens) & fromString
        let newGen = gen & lens #%~ (+1)
        res <$ writeSTRef genRef newGen & liftST

instance MonadQuantify ScopeLevel T.TypeVar (STInfer s) where
    newQuantifiedVariable _ = nextTVNameST 't' nextTV

instance MonadScopeConstraints T.RConstraints (STInfer s) where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = scopeConstraints <&> T.RowConstraints mempty

instance MonadQuantify T.RConstraints T.RowVar (STInfer s) where
    newQuantifiedVariable _ = nextTVNameST 'r' nextRV

instance Unify (STInfer s) T.Type where
    {-# INLINE binding #-}
    binding = stBinding
    unifyError _ = empty

instance Unify (STInfer s) T.Row where
    {-# INLINE binding #-}
    binding = stBinding
    unifyError _ = empty
    {-# INLINE structureMismatch #-}
    structureMismatch = T.rStructureMismatch

{-# SPECIALIZE semiPruneLookup :: Tree (Const Int) T.Type -> PureInfer (Tree (Const Int) T.Type, Tree (UTerm (Const Int)) T.Type) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (Const Int) T.Row -> PureInfer (Tree (Const Int) T.Row, Tree (UTerm (Const Int)) T.Row) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (STVar s) T.Type -> STInfer s (Tree (STVar s) T.Type, Tree (UTerm (STVar s)) T.Type) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (STVar s) T.Row -> STInfer s (Tree (STVar s) T.Row, Tree (UTerm (STVar s)) T.Row) #-}
{-# SPECIALIZE updateConstraints :: ScopeLevel -> Tree (Const Int) T.Type -> PureInfer (Tree (Const Int) T.Type) #-}
{-# SPECIALIZE updateConstraints :: T.RConstraints -> Tree (Const Int) T.Row -> PureInfer (Tree (Const Int) T.Row) #-}
{-# SPECIALIZE updateConstraints :: ScopeLevel -> Tree (STVar s) T.Type -> STInfer s (Tree (STVar s) T.Type) #-}
{-# SPECIALIZE updateConstraints :: T.RConstraints -> Tree (STVar s) T.Row -> STInfer s (Tree (STVar s) T.Row) #-}
{-# SPECIALIZE unify :: Tree (Const Int) T.Type -> Tree (Const Int) T.Type -> PureInfer (Tree (Const Int) T.Type) #-}
{-# SPECIALIZE unify :: Tree (Const Int) T.Row -> Tree (Const Int) T.Row -> PureInfer (Tree (Const Int) T.Row) #-}
{-# SPECIALIZE unify :: Tree (STVar s) T.Type -> Tree (STVar s) T.Type -> STInfer s (Tree (STVar s) T.Type) #-}
{-# SPECIALIZE unify :: Tree (STVar s) T.Row -> Tree (STVar s) T.Row -> STInfer s (Tree (STVar s) T.Row) #-}
{-# SPECIALIZE applyBindings :: Tree (Const Int) T.Type -> PureInfer (Tree Pure T.Type) #-}
{-# SPECIALIZE applyBindings :: Tree (Const Int) T.Row -> PureInfer (Tree Pure T.Row) #-}
{-# SPECIALIZE applyBindings :: Tree (STVar s) T.Type -> STInfer s (Tree Pure T.Type) #-}
{-# SPECIALIZE applyBindings :: Tree (STVar s) T.Row -> STInfer s (Tree Pure T.Row) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm (Const Int)) T.Type -> WriterT [PureInfer ()] PureInfer (Tree (Const Int) T.Type) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm (Const Int)) T.Row -> WriterT [PureInfer ()] PureInfer (Tree (Const Int) T.Row) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm (STVar s)) T.Type -> WriterT [STInfer s ()] (STInfer s) (Tree (STVar s) T.Type) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm (STVar s)) T.Row -> WriterT [STInfer s ()] (STInfer s) (Tree (STVar s) T.Row) #-}

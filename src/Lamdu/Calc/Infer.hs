{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, LambdaCase, DataKinds, FlexibleContexts #-}
{-# LANGUAGE TypeApplications, RankNTypes #-}

module Lamdu.Calc.Infer
    ( InferState(..), isBinding, isQVarGen
    , emptyPureInferState
    , PureInfer(..), _PureInfer, runPureInfer
    , STInfer(..), _STInfer
    , loadDeps
    , varGen
    , alphaEq
    ) where

import           AST
import           AST.Infer
import           AST.Term.Nominal
import qualified AST.Term.Scheme as S
import qualified AST.Term.Scheme.AlphaEq as S
import           AST.Unify
import           AST.Unify.Binding
import           AST.Unify.Binding.ST
import           AST.Unify.Generalize
import           AST.Unify.Term
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
import           Control.Monad.Trans.RWS (RWST(..))
import           Control.Monad.Trans.Reader (ReaderT(..))
import           Control.Monad.Trans.Writer (WriterT)
import           Data.Proxy (Proxy(..))
import           Data.STRef
import           Data.String (IsString(..))
import           Lamdu.Calc.Definition (Deps, depsNominals, depsGlobalTypes)
import           Lamdu.Calc.Term
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

data QVarGen = QVarGen
    { _nextTV :: !Int
    , _nextRV :: !Int
    } deriving (Eq, Ord, Show)
Lens.makeLenses ''QVarGen

varGen :: QVarGen
varGen = QVarGen 0 0

data InferState = InferState
    { _isBinding :: Tree T.Types Binding
    , _isQVarGen :: QVarGen
    } deriving (Eq, Ord, Show)
Lens.makeLenses ''InferState

newtype PureInfer a =
    PureInfer
    (RWST (Tree Scope UVar) () InferState (Either (Tree Pure T.TypeError)) a)
    deriving
    ( Functor, Applicative, Monad
    , MonadReader (Tree Scope UVar)
    , MonadError (Tree Pure T.TypeError)
    , MonadState InferState
    )
Lens.makePrisms ''PureInfer

runPureInfer ::
    Tree Scope UVar -> InferState -> PureInfer a ->
    Either (Tree Pure T.TypeError) (a, InferState)
runPureInfer env st (PureInfer act) =
    runRWST act env st <&> \(x, s, ~()) -> (x, s)

type instance UVarOf PureInfer = UVar

loadDeps ::
    (Unify m T.Row, Unify m T.Type) =>
    Deps -> m (Tree Scope (UVarOf m) -> Tree Scope (UVarOf m))
loadDeps deps =
    do
        loadedNoms <- deps ^. depsNominals & traverse loadNominalDecl
        loadedSchemes <- deps ^. depsGlobalTypes & traverse S.loadScheme
        pure $ \env ->
            env
            & scopeVarTypes <>~ loadedSchemes
            & scopeNominals <>~ loadedNoms

instance MonadScopeLevel PureInfer where
    localLevel = local (scopeLevel . _ScopeLevel +~ 1)

instance MonadNominals T.NominalId T.Type PureInfer where
    {-# INLINE getNominalDecl #-}
    getNominalDecl n =
        Lens.view (scopeNominals . Lens.at n)
        >>= maybe (throwError (_Pure # T.NominalNotFound n)) pure

instance HasScope PureInfer Scope where
    {-# INLINE getScope #-}
    getScope = Lens.view id

instance LocalScopeType Var (Tree UVar T.Type) PureInfer where
    {-# INLINE localScopeType #-}
    localScopeType k v = local (scopeVarTypes . Lens.at k ?~ GMono v)

instance MonadScopeConstraints ScopeLevel PureInfer where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = Lens.view scopeLevel

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
    binding = bindingDict (isBinding . T.tType)
    unifyError e =
        children (Proxy @(Recursive (Unify PureInfer))) applyBindings e
        >>= throwError . MkPure . T.TypeError

instance Unify PureInfer T.Row where
    {-# INLINE binding #-}
    binding = bindingDict (isBinding . T.tRow)
    unifyError e =
        children (Proxy @(Recursive (Unify PureInfer))) applyBindings e
        >>= throwError . MkPure . T.RowError
    {-# INLINE structureMismatch #-}
    structureMismatch = T.rStructureMismatch

emptyPureInferState :: Tree T.Types Binding
emptyPureInferState = T.Types emptyBinding emptyBinding

newtype STInfer s a = STInfer
    (ReaderT (Tree Scope (STUVar s), STRef s QVarGen) (MaybeT (ST s)) a)
    deriving
    ( Functor, Alternative, Applicative, Monad, MonadST
    , MonadReader (Tree Scope (STUVar s), STRef s QVarGen)
    )
Lens.makePrisms ''STInfer

type instance UVarOf (STInfer s) = STUVar s

instance MonadScopeLevel (STInfer s) where
    localLevel = local (Lens._1 . scopeLevel . _ScopeLevel +~ 1)

instance MonadNominals T.NominalId T.Type (STInfer s) where
    {-# INLINE getNominalDecl #-}
    getNominalDecl n =
        Lens.view (Lens._1 . scopeNominals . Lens.at n) >>= maybe empty pure

instance HasScope (STInfer s) Scope where
    {-# INLINE getScope #-}
    getScope = Lens.view Lens._1

instance LocalScopeType Var (Tree (STUVar s) T.Type) (STInfer s) where
    {-# INLINE localScopeType #-}
    localScopeType k v =
        local (Lens._1 . scopeVarTypes . Lens.at k ?~ GMono v)

instance MonadScopeConstraints ScopeLevel (STInfer s) where
    {-# INLINE scopeConstraints #-}
    scopeConstraints = Lens.view (Lens._1 . scopeLevel)

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

alphaEq ::
    Tree Pure (S.Scheme T.Types T.Type) ->
    Tree Pure (S.Scheme T.Types T.Type) ->
    Bool
alphaEq x y =
    runST $
    do
        vg <- newSTRef varGen
        S.alphaEq x y
            ^. _STInfer
            & (`runReaderT` (emptyScope, vg))
            & runMaybeT
    <&> Lens.has Lens._Just

{-# SPECIALIZE semiPruneLookup :: Tree UVar T.Type -> PureInfer (Tree UVar T.Type, Tree (UTerm UVar) T.Type) #-}
{-# SPECIALIZE semiPruneLookup :: Tree UVar T.Row -> PureInfer (Tree UVar T.Row, Tree (UTerm UVar) T.Row) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (STUVar s) T.Type -> STInfer s (Tree (STUVar s) T.Type, Tree (UTerm (STUVar s)) T.Type) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (STUVar s) T.Row -> STInfer s (Tree (STUVar s) T.Row, Tree (UTerm (STUVar s)) T.Row) #-}
{-# SPECIALIZE updateConstraints :: ScopeLevel -> Tree UVar T.Type -> Tree (UTerm UVar) T.Type -> PureInfer () #-}
{-# SPECIALIZE updateConstraints :: T.RConstraints -> Tree UVar T.Row -> Tree (UTerm UVar) T.Row -> PureInfer () #-}
{-# SPECIALIZE updateConstraints :: ScopeLevel -> Tree (STUVar s) T.Type -> Tree (UTerm (STUVar s)) T.Type -> STInfer s () #-}
{-# SPECIALIZE updateConstraints :: T.RConstraints -> Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> STInfer s () #-}
{-# SPECIALIZE unify :: Tree UVar T.Type -> Tree UVar T.Type -> PureInfer (Tree UVar T.Type) #-}
{-# SPECIALIZE unify :: Tree UVar T.Row -> Tree UVar T.Row -> PureInfer (Tree UVar T.Row) #-}
{-# SPECIALIZE unify :: Tree (STUVar s) T.Type -> Tree (STUVar s) T.Type -> STInfer s (Tree (STUVar s) T.Type) #-}
{-# SPECIALIZE unify :: Tree (STUVar s) T.Row -> Tree (STUVar s) T.Row -> STInfer s (Tree (STUVar s) T.Row) #-}
{-# SPECIALIZE unifyUnbound :: Tree UVar T.Type -> ScopeLevel -> Tree UVar T.Type -> Tree (UTerm UVar) T.Type -> PureInfer (Tree UVar T.Type) #-}
{-# SPECIALIZE unifyUnbound :: Tree UVar T.Row -> T.RConstraints -> Tree UVar T.Row -> Tree (UTerm UVar) T.Row -> PureInfer (Tree UVar T.Row) #-}
{-# SPECIALIZE unifyUnbound :: Tree (STUVar s) T.Type -> ScopeLevel -> Tree (STUVar s) T.Type -> Tree (UTerm (STUVar s)) T.Type -> STInfer s (Tree (STUVar s) T.Type) #-}
{-# SPECIALIZE unifyUnbound :: Tree (STUVar s) T.Row -> T.RConstraints -> Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> STInfer s (Tree (STUVar s) T.Row) #-}
{-# SPECIALIZE unifyUTerms :: Tree UVar T.Type -> Tree (UTerm UVar) T.Type -> Tree UVar T.Type -> Tree (UTerm UVar) T.Type -> PureInfer (Tree UVar T.Type) #-}
{-# SPECIALIZE unifyUTerms :: Tree UVar T.Row -> Tree (UTerm UVar) T.Row -> Tree UVar T.Row -> Tree (UTerm UVar) T.Row -> PureInfer (Tree UVar T.Row) #-}
{-# SPECIALIZE unifyUTerms :: Tree (STUVar s) T.Type -> Tree (UTerm (STUVar s)) T.Type -> Tree (STUVar s) T.Type -> Tree (UTerm (STUVar s)) T.Type -> STInfer s (Tree (STUVar s) T.Type) #-}
{-# SPECIALIZE unifyUTerms :: Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> STInfer s (Tree (STUVar s) T.Row) #-}
{-# SPECIALIZE applyBindings :: Tree UVar T.Type -> PureInfer (Tree Pure T.Type) #-}
{-# SPECIALIZE applyBindings :: Tree UVar T.Row -> PureInfer (Tree Pure T.Row) #-}
{-# SPECIALIZE applyBindings :: Tree (STUVar s) T.Type -> STInfer s (Tree Pure T.Type) #-}
{-# SPECIALIZE applyBindings :: Tree (STUVar s) T.Row -> STInfer s (Tree Pure T.Row) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm UVar) T.Type -> WriterT [PureInfer ()] PureInfer (Tree UVar T.Type) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm UVar) T.Row -> WriterT [PureInfer ()] PureInfer (Tree UVar T.Row) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm (STUVar s)) T.Type -> WriterT [STInfer s ()] (STInfer s) (Tree (STUVar s) T.Type) #-}
{-# SPECIALIZE instantiateH :: Tree (GTerm (STUVar s)) T.Row -> WriterT [STInfer s ()] (STInfer s) (Tree (STUVar s) T.Row) #-}

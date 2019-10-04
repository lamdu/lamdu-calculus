{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, LambdaCase, DataKinds, FlexibleContexts #-}
{-# LANGUAGE TypeApplications, RankNTypes, DerivingStrategies, TypeOperators #-}

module Lamdu.Calc.Infer
    ( InferState(..), isBinding, isQVarGen
    , emptyPureInferState
    , PureInfer(..), _PureInfer, runPureInfer
    , STInfer(..), _STInfer
    , loadDeps
    , varGen
    , alphaEq
    ) where

import           Hyper
import           Hyper.Infer
import           Hyper.Type.AST.Nominal
import qualified Hyper.Type.AST.Var as TermVar
import qualified Hyper.Type.AST.Scheme as S
import qualified Hyper.Type.AST.Scheme.AlphaEq as S
import           Hyper.Type.Combinator.Flip
import           Hyper.Unify
import           Hyper.Unify.Apply (applyBindings)
import           Hyper.Unify.Binding
import           Hyper.Unify.Binding.ST
import           Hyper.Unify.Generalize
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.QuantifiedVar
import           Hyper.Unify.Term (UTerm, UTermBody)
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
    deriving newtype
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
    (Unify m T.Row, S.HasScheme T.Types m T.Type) =>
    Deps -> m (Tree Scope (UVarOf m) -> Tree Scope (UVarOf m))
loadDeps deps =
    do
        loadedNoms <- deps ^. depsNominals & traverse loadNominalDecl
        loadedSchemes <- deps ^. depsGlobalTypes & traverse S.loadScheme
        pure $ \env ->
            env
            & scopeVarTypes <>~ (loadedSchemes <&> MkFlip)
            & scopeNominals <>~ loadedNoms

instance MonadScopeLevel PureInfer where
    localLevel = local (scopeLevel . _ScopeLevel +~ 1)

instance MonadNominals T.NominalId T.Type PureInfer where
    {-# INLINE getNominalDecl #-}
    getNominalDecl n =
        Lens.view (scopeNominals . Lens.at n)
        >>= maybe (throwError (_Pure # T.NominalNotFound n)) pure

instance TermVar.HasScope PureInfer Scope where
    {-# INLINE getScope #-}
    getScope = Lens.view id

instance LocalScopeType Var (Tree UVar T.Type) PureInfer where
    {-# INLINE localScopeType #-}
    localScopeType k v = local (scopeVarTypes . Lens.at k ?~ MkFlip (GMono v))

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
        htraverse (Proxy @(Unify PureInfer) #> applyBindings) e
        >>= throwError . Pure . T.TypeError

instance Unify PureInfer T.Row where
    {-# INLINE binding #-}
    binding = bindingDict (isBinding . T.tRow)
    unifyError e =
        htraverse (Proxy @(Unify PureInfer) #> applyBindings) e
        >>= throwError . Pure . T.RowError
    {-# INLINE structureMismatch #-}
    structureMismatch = T.rStructureMismatch

emptyPureInferState :: Tree T.Types Binding
emptyPureInferState = T.Types emptyBinding emptyBinding

newtype STInfer s a = STInfer
    (ReaderT (Tree Scope (STUVar s), STRef s QVarGen) (MaybeT (ST s)) a)
    deriving newtype
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

instance TermVar.HasScope (STInfer s) Scope where
    {-# INLINE getScope #-}
    getScope = Lens.view Lens._1

instance LocalScopeType Var (Tree (STUVar s) T.Type) (STInfer s) where
    {-# INLINE localScopeType #-}
    localScopeType k v =
        local (Lens._1 . scopeVarTypes . Lens.at k ?~ MkFlip (GMono v))

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

{-# SPECIALIZE inferH :: Tree (Ann a) Term -> Tree (InferChild PureInfer (Ann (a :*: InferResult UVar))) Term #-}
{-# SPECIALIZE unify :: Tree UVar T.Row -> Tree UVar T.Row -> PureInfer (Tree UVar T.Row) #-}
{-# SPECIALIZE unify :: Tree (STUVar s) T.Row -> Tree (STUVar s) T.Row -> STInfer s (Tree (STUVar s) T.Row) #-}
{-# SPECIALIZE updateConstraints :: ScopeLevel -> Tree (STUVar s) T.Type -> Tree (UTerm (STUVar s)) T.Type -> STInfer s () #-}
{-# SPECIALIZE updateConstraints :: T.RConstraints -> Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> STInfer s () #-}
{-# SPECIALIZE updateTermConstraints :: Tree UVar T.Row -> Tree (UTermBody UVar) T.Row -> T.RConstraints -> PureInfer () #-}
{-# SPECIALIZE updateTermConstraints :: Tree (STUVar s) T.Row -> Tree (UTermBody (STUVar s)) T.Row -> T.RConstraints -> STInfer s () #-}
{-# SPECIALIZE instantiateH :: (forall n. TypeConstraintsOf n -> Tree (UTerm UVar) n) -> Tree (GTerm UVar) T.Row -> WriterT [PureInfer ()] PureInfer (Tree UVar T.Row) #-}
{-# SPECIALIZE instantiateH :: (forall n. TypeConstraintsOf n -> Tree (UTerm (STUVar s)) n) -> Tree (GTerm (STUVar s)) T.Row -> WriterT [STInfer s ()] (STInfer s) (Tree (STUVar s) T.Row) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (STUVar s) T.Type -> STInfer s (Tree (STUVar s) T.Type, Tree (UTerm (STUVar s)) T.Type) #-}
{-# SPECIALIZE semiPruneLookup :: Tree (STUVar s) T.Row -> STInfer s (Tree (STUVar s) T.Row, Tree (UTerm (STUVar s)) T.Row) #-}
{-# SPECIALIZE unifyUTerms :: Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> Tree (STUVar s) T.Row -> Tree (UTerm (STUVar s)) T.Row -> STInfer s (Tree (STUVar s) T.Row) #-}

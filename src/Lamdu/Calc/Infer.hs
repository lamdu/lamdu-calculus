{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, LambdaCase, DataKinds, FlexibleContexts #-}
{-# LANGUAGE TypeApplications, RankNTypes, DerivingStrategies, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    { _isBinding :: T.Types # Binding
    , _isQVarGen :: QVarGen
    } deriving (Eq, Ord, Show)
Lens.makeLenses ''InferState

newtype PureInfer env a =
    PureInfer
    (RWST env () InferState (Either (Pure # T.TypeError)) a)
    deriving newtype
    ( Functor, Applicative, Monad
    , MonadReader env
    , MonadError (Pure # T.TypeError)
    , MonadState InferState
    )
Lens.makePrisms ''PureInfer

runPureInfer ::
    env -> InferState -> PureInfer env a ->
    Either (Pure # T.TypeError) (a, InferState)
runPureInfer env st (PureInfer act) =
    runRWST act env st <&> \(x, s, ~()) -> (x, s)

type instance UVarOf (PureInfer env) = UVar

loadDeps ::
    (UnifyGen m T.Row, S.HasScheme T.Types m T.Type) =>
    Deps -> m (Scope # UVarOf m -> Scope # UVarOf m)
loadDeps deps =
    do
        loadedNoms <- deps ^. depsNominals & traverse loadNominalDecl
        loadedSchemes <- deps ^. depsGlobalTypes & traverse S.loadScheme
        pure $ \env ->
            env
            & scopeVarTypes <>~ (loadedSchemes <&> MkHFlip)
            & scopeNominals <>~ loadedNoms

instance MonadScopeLevel (PureInfer (Scope # UVar)) where
    localLevel = local (scopeLevel . _ScopeLevel +~ 1)

instance MonadNominals T.NominalId T.Type (PureInfer (Scope # UVar)) where
    {-# INLINE getNominalDecl #-}
    getNominalDecl n =
        Lens.view (scopeNominals . Lens.at n)
        >>= maybe (throwError (_Pure # T.NominalNotFound n)) pure

instance TermVar.HasScope (PureInfer (Scope # UVar)) Scope where
    {-# INLINE getScope #-}
    getScope = Lens.view id

instance LocalScopeType Var (UVar # T.Type) (PureInfer (Scope # UVar)) where
    {-# INLINE localScopeType #-}
    localScopeType k v = local (scopeVarTypes . Lens.at k ?~ MkHFlip (GMono v))

instance UnifyGen (PureInfer (Scope # UVar)) T.Type where
    {-# INLINE scopeConstraints #-}
    scopeConstraints _ = Lens.view scopeLevel

nextTVNamePure ::
    (MonadState InferState m, IsString a) =>
    Char -> LensLike' ((,) Int) QVarGen Int -> m a
nextTVNamePure prefix lens =
    isQVarGen . lens <<%= (+1) <&> show <&> (prefix :) <&> fromString

instance MonadQuantify ScopeLevel T.TypeVar (PureInfer env) where
    newQuantifiedVariable _ = nextTVNamePure 't' nextTV

instance UnifyGen (PureInfer (Scope # UVar)) T.Row where
    {-# INLINE scopeConstraints #-}
    scopeConstraints _ = scopeConstraints (Proxy @T.Type) <&> T.RowConstraints mempty

instance MonadQuantify T.RConstraints T.RowVar (PureInfer env) where
    newQuantifiedVariable _ = nextTVNamePure 'r' nextRV

instance Unify (PureInfer env) T.Type where
    {-# INLINE binding #-}
    binding = bindingDict (isBinding . T.tType)
    unifyError e =
        htraverse (Proxy @(Unify (PureInfer env)) #> applyBindings) e
        >>= throwError . Pure . T.TypeError

instance Unify (PureInfer env) T.Row where
    {-# INLINE binding #-}
    binding = bindingDict (isBinding . T.tRow)
    unifyError e =
        htraverse (Proxy @(Unify (PureInfer env)) #> applyBindings) e
        >>= throwError . Pure . T.RowError
    {-# INLINE structureMismatch #-}
    structureMismatch = T.rStructureMismatch

emptyPureInferState :: T.Types # Binding
emptyPureInferState = T.Types emptyBinding emptyBinding

newtype STInfer s a = STInfer
    (ReaderT (Scope # STUVar s, STRef s QVarGen) (MaybeT (ST s)) a)
    deriving newtype
    ( Functor, Alternative, Applicative, Monad, MonadST
    , MonadReader (Scope # STUVar s, STRef s QVarGen)
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

instance LocalScopeType Var (STUVar s # T.Type) (STInfer s) where
    {-# INLINE localScopeType #-}
    localScopeType k v =
        local (Lens._1 . scopeVarTypes . Lens.at k ?~ MkHFlip (GMono v))

instance UnifyGen (STInfer s) T.Type where
    {-# INLINE scopeConstraints #-}
    scopeConstraints _ = Lens.view (Lens._1 . scopeLevel)

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

instance UnifyGen (STInfer s) T.Row where
    {-# INLINE scopeConstraints #-}
    scopeConstraints _ = scopeConstraints (Proxy @T.Type) <&> T.RowConstraints mempty

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
    Pure # S.Scheme T.Types T.Type ->
    Pure # S.Scheme T.Types T.Type ->
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

{-# SPECIALIZE inferH :: Ann a # Term -> InferChild (PureInfer (Scope # UVar)) (Ann (a :*: InferResult UVar)) # Term #-}
{-# SPECIALIZE unify :: UVar # T.Row -> UVar # T.Row -> (PureInfer env) (UVar # T.Row) #-}
{-# SPECIALIZE unify :: STUVar s # T.Row -> STUVar s # T.Row -> STInfer s (STUVar s # T.Row) #-}
{-# SPECIALIZE updateConstraints :: ScopeLevel -> STUVar s # T.Type -> UTerm (STUVar s) # T.Type -> STInfer s () #-}
{-# SPECIALIZE updateConstraints :: T.RConstraints -> STUVar s # T.Row -> UTerm (STUVar s) # T.Row -> STInfer s () #-}
{-# SPECIALIZE updateTermConstraints :: UVar # T.Row -> UTermBody UVar # T.Row -> T.RConstraints -> (PureInfer env) () #-}
{-# SPECIALIZE updateTermConstraints :: STUVar s # T.Row -> UTermBody (STUVar s) # T.Row -> T.RConstraints -> STInfer s () #-}
{-# SPECIALIZE instantiateH :: (forall n. TypeConstraintsOf n -> UTerm UVar # n) -> GTerm UVar # T.Row -> WriterT [PureInfer (Scope # UVar) ()] (PureInfer (Scope # UVar)) (UVar # T.Row) #-}
{-# SPECIALIZE instantiateH :: (forall n. TypeConstraintsOf n -> UTerm (STUVar s) # n) -> GTerm (STUVar s) # T.Row -> WriterT [STInfer s ()] (STInfer s) (STUVar s # T.Row) #-}
{-# SPECIALIZE semiPruneLookup :: STUVar s # T.Type -> STInfer s (STUVar s # T.Type, UTerm (STUVar s) # T.Type) #-}
{-# SPECIALIZE semiPruneLookup :: STUVar s # T.Row -> STInfer s (STUVar s # T.Row, UTerm (STUVar s) # T.Row) #-}
{-# SPECIALIZE unifyUTerms :: STUVar s # T.Row -> UTerm (STUVar s) # T.Row -> STUVar s # T.Row -> UTerm (STUVar s) # T.Row -> STInfer s (STUVar s # T.Row) #-}

{-# LANGUAGE NoImplicitPrelude, DeriveGeneric #-}
module Lamdu.Calc.Type.Vars
    ( TypeVars(..)
    , null
    , Free(..)
    , VarKind(..)
    , difference, intersection
    , Renames(..), applyRenames, renameDest
    , nullRenames
    ) where

import           Prelude.Compat hiding (null)

import           Control.DeepSeq (NFData(..))
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

data TypeVars = TypeVars
    { typeVars :: !(Set T.TypeVar)
    , rowVars :: !(Set T.RowVar)
    } deriving (Eq, Ord, Generic, Show)
instance NFData TypeVars where
instance Semigroup TypeVars where
    TypeVars t0 r0 <> TypeVars t1 r1 = TypeVars (t0 <> t1) (r0 <> r1)
instance Monoid TypeVars where
    mempty = TypeVars mempty mempty
    mappend = (<>)

instance Pretty TypeVars where
    pPrint (TypeVars tvs rvs) =
        PP.hcat $ PP.punctuate (PP.text ", ") $ p tvs ++ p rvs
        where
            p :: Set (T.Var t) -> [PP.Doc]
            p = map pPrint . Set.elems

instance Binary TypeVars

difference :: TypeVars -> TypeVars -> TypeVars
difference (TypeVars t0 r0) (TypeVars t1 r1) =
    TypeVars (Set.difference t0 t1) (Set.difference r0 r1)

intersection :: TypeVars -> TypeVars -> TypeVars
intersection (TypeVars t0 r0) (TypeVars t1 r1) =
    TypeVars (Set.intersection t0 t1) (Set.intersection r0 r1)

{-# INLINE null #-}
null :: TypeVars -> Bool
null (TypeVars t r) = Set.null t && Set.null r

class Free t where free :: t -> TypeVars

instance Free a => Free [a] where
    {-# INLINE free #-}
    free = mconcat . map free

instance Free Type where
    free (T.TVar n)      =  singleton n
    free (T.TInst _ p)   =  mconcat $ map free $ Map.elems p
    free (T.TFun t1 t2)  =  free t1 <> free t2
    free (T.TRecord r)   =  free r
    free (T.TVariant s)  =  free s

instance Free T.Row where
    free T.REmpty          = mempty
    free (T.RVar n)        = singleton n
    free (T.RExtend _ t r) = free t <> free r

class VarKind t where
    lift :: T.Var t -> t
    unlift :: t -> Maybe (T.Var t)
    member :: T.Var t -> TypeVars -> Bool
    singleton :: T.Var t -> TypeVars

instance VarKind Type where
    lift = T.TVar
    {-# INLINE lift #-}
    unlift (T.TVar tv) = Just tv
    unlift _ = Nothing
    {-# INLINE unlift #-}
    member v tvs = v `Set.member` typeVars tvs
    singleton v = mempty { typeVars = Set.singleton v }

instance VarKind T.Row where
    lift = T.RVar
    {-# INLINE lift #-}
    unlift (T.RVar tv) = Just tv
    unlift _ = Nothing
    {-# INLINE unlift #-}
    member v tvs = v `Set.member` rowVars tvs
    {-# INLINE member #-}
    singleton v = mempty { rowVars = Set.singleton v }
    {-# INLINE singleton #-}

data Renames = Renames
    { renamesTv :: Map T.TypeVar T.TypeVar
    , renamesRv :: Map T.RowVar T.RowVar
    } deriving (Eq, Ord, Show)

nullRenames :: Renames -> Bool
nullRenames (Renames tv rv) = Map.null tv && Map.null rv

renameDest :: Renames -> TypeVars
renameDest (Renames tvRenames rvRenames) =
    TypeVars
    (Set.fromList (Map.elems tvRenames))
    (Set.fromList (Map.elems rvRenames))

{-# INLINE applyRenames #-}
applyRenames :: Renames -> TypeVars -> TypeVars
applyRenames (Renames tvRenames rvRenames) (TypeVars tvs rvs) =
    TypeVars
    (apply tvRenames tvs)
    (apply rvRenames rvs)
    where
        apply renames = Set.map (applyRename renames)
        applyRename m k = fromMaybe k (Map.lookup k m)

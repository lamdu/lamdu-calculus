{-# LANGUAGE NoImplicitPrelude, DeriveGeneric #-}
module Lamdu.Calc.Type.Vars
    ( TypeVars(..)
    , null
    , Free(..)
    , VarKind(..), CompositeVarKind(..)
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
    , recordTypeVars :: !(Set T.RecordVar)
    , variantTypeVars :: !(Set T.VariantVar)
    } deriving (Eq, Ord, Generic, Show)
instance NFData TypeVars where
instance Semigroup TypeVars where
    TypeVars t0 r0 s0 <> TypeVars t1 r1 s1 = TypeVars (t0 <> t1) (r0 <> r1) (s0 <> s1)
instance Monoid TypeVars where
    mempty = TypeVars mempty mempty mempty
    mappend = (<>)

instance Pretty TypeVars where
    pPrint (TypeVars tvs rtvs stvs) =
        PP.hcat $ PP.punctuate (PP.text ", ") $ p tvs ++ p rtvs ++ p stvs
        where
            p :: Set (T.Var t) -> [PP.Doc]
            p = map pPrint . Set.elems

instance Binary TypeVars

difference :: TypeVars -> TypeVars -> TypeVars
difference (TypeVars t0 r0 s0) (TypeVars t1 r1 s1) =
    TypeVars (Set.difference t0 t1) (Set.difference r0 r1) (Set.difference s0 s1)

intersection :: TypeVars -> TypeVars -> TypeVars
intersection (TypeVars t0 r0 s0) (TypeVars t1 r1 s1) =
    TypeVars (Set.intersection t0 t1) (Set.intersection r0 r1) (Set.intersection s0 s1)

{-# INLINE null #-}
null :: TypeVars -> Bool
null (TypeVars t r s) = Set.null t && Set.null r && Set.null s

class Free t where free :: t -> TypeVars

instance Free a => Free [a] where
    {-# INLINE free #-}
    free = mconcat . map free

instance Free Type where
    free (T.TVar n)      =  singleton n
    free (T.TInst _ p)   =  mconcat $ map free $ Map.elems p
    free (T.TFun t1 t2)  =  free t1 <> free t2
    free (T.TRecord r)   =  free r
    free (T.TVariant s)      =  free s

instance CompositeVarKind p => Free (T.Composite p) where
    free T.CEmpty          = mempty
    free (T.CVar n)        = singleton n
    free (T.CExtend _ t r) = free t <> free r

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

class CompositeVarKind p where
    compositeMember :: T.Var (T.Composite p) -> TypeVars -> Bool
    compositeSingleton :: T.Var (T.Composite p) -> TypeVars

instance CompositeVarKind T.RecordTag where
    compositeMember v tvs = v `Set.member` recordTypeVars tvs
    compositeSingleton v = mempty { recordTypeVars = Set.singleton v }

instance CompositeVarKind T.VariantTag where
    compositeMember v tvs = v `Set.member` variantTypeVars tvs
    compositeSingleton v = mempty { variantTypeVars = Set.singleton v }

instance CompositeVarKind p => VarKind (T.Composite p) where
    lift = T.CVar
    {-# INLINE lift #-}
    unlift (T.CVar tv) = Just tv
    unlift _ = Nothing
    {-# INLINE unlift #-}
    member = compositeMember
    {-# INLINE member #-}
    singleton = compositeSingleton
    {-# INLINE singleton #-}

data Renames = Renames
    { renamesTv :: Map T.TypeVar T.TypeVar
    , renamesProd :: Map T.RecordVar T.RecordVar
    , renamesVariant :: Map T.VariantVar T.VariantVar
    } deriving (Eq, Ord, Show)

nullRenames :: Renames -> Bool
nullRenames (Renames tv rtv stv) = Map.null tv && Map.null rtv && Map.null stv

renameDest :: Renames -> TypeVars
renameDest (Renames tvRenames prodRenames variantRenames) =
    TypeVars
    (Set.fromList (Map.elems tvRenames))
    (Set.fromList (Map.elems prodRenames))
    (Set.fromList (Map.elems variantRenames))

{-# INLINE applyRenames #-}
applyRenames :: Renames -> TypeVars -> TypeVars
applyRenames (Renames tvRenames prodRenames variantRenames) (TypeVars tvs rtvs stvs) =
    TypeVars
    (apply tvRenames tvs)
    (apply prodRenames rtvs)
    (apply variantRenames stvs)
    where
        apply renames = Set.map (applyRename renames)
        applyRename m k = fromMaybe k (Map.lookup k m)

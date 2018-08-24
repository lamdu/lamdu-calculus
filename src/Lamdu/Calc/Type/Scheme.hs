{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, OverloadedStrings, RecordWildCards #-}
module Lamdu.Calc.Type.Scheme
    ( Scheme(..), schemeForAll, schemeConstraints, schemeType
    , make, mono, any
    , alphaEq
    ) where

import           Prelude.Compat hiding (any)

import           Control.DeepSeq (NFData(..))
import           Control.Lens (Lens')
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (guard)
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Tuple as Tuple
import           GHC.Generics (Generic)
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..), getTypeVarConstraints, getVariantVarConstraints, getRecordVarConstraints)
import qualified Lamdu.Calc.Type.Constraints as Constraints
import qualified Lamdu.Calc.Type.Match as TypeMatch
import           Lamdu.Calc.Type.Vars (TypeVars(..))
import qualified Lamdu.Calc.Type.Vars as TV
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

data Scheme = Scheme
    { _schemeForAll :: TypeVars
    , _schemeConstraints :: Constraints
    , _schemeType :: Type
    } deriving (Generic, Show, Eq, Ord)

schemeForAll :: Lens' Scheme TypeVars
schemeForAll f Scheme{..} = f _schemeForAll <&> \_schemeForAll -> Scheme{..}

schemeConstraints :: Lens' Scheme Constraints
schemeConstraints f Scheme{..} = f _schemeConstraints <&> \_schemeConstraints -> Scheme{..}

schemeType :: Lens' Scheme Type
schemeType f Scheme{..} = f _schemeType <&> \_schemeType -> Scheme{..}

-- a Consistent List is an assoc list where each key is never
-- associated to non-eq values
fromConsistentList :: (Ord a, Eq b) => [(a, b)] -> Maybe (Map a b)
fromConsistentList pairs =
    pairs
    <&> _2 %~ Just
    & Map.fromListWith checkConsistency
    & sequenceA
    where
        checkConsistency x y = guard (x == y) >> x

fromDoublyConsistentList :: (Ord a, Ord b) => [(a, b)] -> Maybe (Map a b)
fromDoublyConsistentList pairs =
    do
        m <- fromConsistentList pairs
        _ <- fromConsistentList $ map Tuple.swap $ Map.toList m
        pure m

alphaEq :: Scheme -> Scheme -> Bool
alphaEq
    (Scheme aForall aConstraints aType)
    (Scheme bForall bConstraints bType) =
        case TypeMatch.matchVars aType bType of
        Just (tvPairs, ctvPairs, stvPairs)
            | Just tvMap <- fromDoublyConsistentList tvPairs
            , Just ctvMap <- fromDoublyConsistentList ctvPairs
            , Just stvMap <- fromDoublyConsistentList stvPairs
            -> all (checkVarsMatch getVariantVarConstraints) (Map.toList stvMap) &&
               all (checkVarsMatch getRecordVarConstraints) (Map.toList ctvMap) &&
               all (checkVarsMatch getTypeVarConstraints) (Map.toList tvMap)
        _ -> False
    where
        checkVarsMatch getTVConstraints (a, b) =
            ( a `TV.member` aForall ==
              b `TV.member` bForall
            ) &&
            ( getTVConstraints a aConstraints ==
              getTVConstraints b bConstraints
            )

make :: Constraints -> Type -> Scheme
make c t =
    Scheme freeVars (freeVars `Constraints.intersect` c) t
    where
        freeVars = TV.free t

mono :: Type -> Scheme
mono x =
    Scheme
    { _schemeForAll = mempty
    , _schemeConstraints = mempty
    , _schemeType = x
    }

any :: Scheme
any =
    Scheme (TV.singleton a) mempty (T.TVar a)
    where
        a :: T.TypeVar
        a = "a"

instance NFData Scheme where

instance Pretty Scheme where
    pPrintPrec lvl prec (Scheme vars@(TypeVars tv rv sv) constraints t)  =
        maybeParens (0 < prec) $
        forallStr <+> constraintsStr <+> pPrintPrec lvl 0 t
        where
            forallStr
                | mempty == vars = mempty
                | otherwise =
                    PP.text "forall" <+>
                    PP.hsep (map pPrint (Set.toList tv) ++ map pPrint (Set.toList rv) ++ map pPrint (Set.toList sv)) PP.<>
                    PP.text "."
            constraintsStr
                | mempty == constraints = mempty
                | otherwise = pPrint constraints <+> PP.text "=>"

instance Binary Scheme

instance TV.Free Scheme where
    -- constraints apply to the forAll'd variables so free variables
    -- there are irrelevant:
    free (Scheme forAll _constraints typ) =
        TV.free typ `TV.difference` forAll

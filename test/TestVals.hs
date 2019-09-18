{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}

module TestVals
    ( allDeps
    , factorialVal, euler1Val, solveDepressedQuarticVal
    , factorsVal
    , recordType
    , intType
    , listTypePair, boolTypePair
    ) where

import           AST
import           AST.Term.Nominal
import           AST.Term.Row
import           AST.Term.Scheme
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Map as Map
import           Lamdu.Calc.Definition (Deps(..))
import           Lamdu.Calc.Term
import           Lamdu.Calc.Type (Type, (~>))
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

{-# ANN module ("HLint: ignore Redundant $" :: String) #-}

-- TODO: $$ to be type-classed for TApp vs BApp
-- TODO: TCon "->" instead of TFun

recExtends :: Tree Pure T.Row -> [(T.Tag, Tree Pure Type)] -> Tree Pure Type
recExtends recTail fields =
    foldr
    (\(tag, typ) -> (&# T.RExtend) . RowExtend tag typ) recTail fields
    &# T.TRecord

recordType :: [(T.Tag, Tree Pure Type)] -> Tree Pure Type
recordType = recExtends (_Pure # T.REmpty)

forAll ::
    [T.TypeVar] -> ([Tree Pure Type] -> Tree Pure Type) -> Tree Pure T.Scheme
forAll tvs mkType =
    tvs <&> T.TVar <&> (_Pure #) & mkType
    &# Scheme T.Types
    { T._tType = QVars (Map.fromList [(tv, mempty) | tv <- tvs])
    , T._tRow = mempty
    }

stOf :: Tree Pure Type -> Tree Pure Type -> Tree Pure Type
stOf s a =
    T.Types (QVarInstances (mempty & Lens.at "res" ?~ a & Lens.at "s" ?~ s)) (QVarInstances mempty)
    & NominalInst "ST" &# T.TInst

listTypePair :: (T.NominalId, Tree Pure (NominalDecl Type))
listTypePair =
    ( "List"
    , _Pure # NominalDecl
        { _nParams =
            T.Types
            { T._tType = mempty & Lens.at "elem" ?~ mempty
            , T._tRow = mempty
            }
        , _nScheme =
            _Pure # T.REmpty
            & RowExtend "[]" (recordType []) &# T.RExtend
            & RowExtend ":" (recordType [("head", tv), ("tail", listOf tv)])
            &# T.RExtend
            &# T.TVariant
            & Scheme (T.Types mempty mempty)
        }
    )
    where
        tv = _Pure # T.TVar "a"

listOf :: Tree Pure Type -> Tree Pure Type
listOf x =
    T.Types (QVarInstances (mempty & Lens.at "elem" ?~ x)) (QVarInstances mempty)
    & NominalInst (fst listTypePair) &# T.TInst

boolType :: Tree Pure Type
boolType =
    T.Types (QVarInstances mempty) (QVarInstances mempty)
    & NominalInst (fst boolTypePair) &# T.TInst

intType :: Tree Pure Type
intType =
    T.Types (QVarInstances mempty) (QVarInstances mempty)
    & NominalInst "Int" &# T.TInst

boolTypePair :: (T.NominalId, Tree Pure (NominalDecl Type))
boolTypePair =
    ( "Bool"
    , _Pure # NominalDecl
        { _nParams = T.Types mempty mempty
        , _nScheme =
            _Pure # T.REmpty
            & RowExtend "True" (recordType []) &# T.RExtend
            & RowExtend "False" (recordType []) &# T.RExtend
            &# T.TVariant
            & Scheme (T.Types mempty mempty)
        }
    )

maybeOf :: Tree Pure Type -> Tree Pure Type
maybeOf t =
    _Pure # T.REmpty
    & RowExtend "Just" t &# T.RExtend
    & RowExtend "Nothing" (recordType []) &# T.RExtend
    &# T.TVariant

infixType :: Tree Pure Type -> Tree Pure Type -> Tree Pure Type -> Tree Pure Type
infixType a b c = recordType [("l", a), ("r", b)] ~> c

allDeps :: Deps
allDeps =
    Deps
    { _depsNominals = Map.fromList [boolTypePair, listTypePair]
    , _depsGlobalTypes =
        Map.fromList
        [ ("fix",    forAll ["a"] $ \ [a] -> (a ~> a) ~> a)
        , ("if",     forAll ["a"] $ \ [a] -> recordType [("condition", boolType), ("then", a), ("else", a)] ~> a)
        , ("==",     forAll ["a"] $ \ [a] -> infixType a a boolType)
        , (">",      forAll ["a"] $ \ [a] -> infixType a a boolType)
        , ("%",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("*",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("-",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("+",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("/",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("//",     forAll []    $ \ []  -> infixType intType intType intType)
        , ("sum",    forAll ["a"] $ \ [a] -> listOf a ~> a)
        , ("filter", forAll ["a"] $ \ [a] -> recordType [("from", listOf a), ("predicate", a ~> boolType)] ~> listOf a)
        , (":",      forAll ["a"] $ \ [a] -> recordType [("head", a), ("tail", listOf a)] ~> listOf a)
        , ("[]",     forAll ["a"] $ \ [a] -> listOf a)
        , ("concat", forAll ["a"] $ \ [a] -> listOf (listOf a) ~> listOf a)
        , ("map",    forAll ["a", "b"] $ \ [a, b] -> recordType [("list", listOf a), ("mapping", a ~> b)] ~> listOf b)
        , ("..",     forAll [] $ \ [] -> infixType intType intType (listOf intType))
        , ("||",     forAll [] $ \ [] -> infixType boolType boolType boolType)
        , ("head",   forAll ["a"] $ \ [a] -> listOf a ~> a)
        , ("negate", forAll ["a"] $ \ [a] -> a ~> a)
        , ("sqrt",   forAll ["a"] $ \ [a] -> a ~> a)
        , ("id",     forAll ["a"] $ \ [a] -> a ~> a)
        , ("zipWith",forAll ["a","b","c"] $ \ [a,b,c] ->
                                    (a ~> b ~> c) ~> listOf a ~> listOf b ~> listOf c )
        , ("Just",   forAll ["a"] $ \ [a] -> a ~> maybeOf a)
        , ("Nothing",forAll ["a"] $ \ [a] -> maybeOf a)
        , ("maybe",  forAll ["a", "b"] $ \ [a, b] -> b ~> (a ~> b) ~> maybeOf a ~> b)
        , ("plus1",  forAll [] $ \ [] -> intType ~> intType)
        , ("True",   forAll [] $ \ [] -> boolType)
        , ("False",  forAll [] $ \ [] -> boolType)

        , ("stBind", forAll ["s", "a", "b"] $ \ [s, a, b] -> infixType (stOf s a) (a ~> stOf s b) (stOf s b))
        ]
    }

litInt :: Integer -> KPlain Term
litInt = BLeafP . LLiteral . PrimVal "Int" . BS8.pack . show

record :: [(T.Tag, KPlain Term)] -> KPlain Term
record = foldr (uncurry BRecExtendP) (BLeafP LRecEmpty)

($$:) :: KPlain Term -> [(T.Tag, KPlain Term)] -> KPlain Term
f $$: args = BAppP f (record args)

inf :: KPlain Term -> KPlain Term -> KPlain Term -> KPlain Term
inf l f r = f $$: [("l", l), ("r", r)]

factorialVal :: KPlain Term
factorialVal =
    BAppP "fix" $
    BLamP "loop" $
    BLamP "x" $
    "if" $$:
    [ ("condition", inf "x" "==" (litInt 0))
    , ("then", litInt 1)
    , ("else", inf "x" "*" (BAppP "loop" $ inf "x" "-" (litInt 1)))
    ]

euler1Val :: KPlain Term
euler1Val =
    BAppP "sum" $
    "filter" $$:
    [ ("from", inf (litInt 1) ".." (litInt 1000))
    , ("predicate",
        BLamP "x" $
        inf
        (inf (litInt 0) "==" (inf "x" "%" (litInt 3)))
        "||"
        (inf (litInt 0) "==" (inf "x" "%" (litInt 5)))
        )
    ]

let_ :: Var -> KPlain Term -> KPlain Term -> KPlain Term
let_ k v r = BAppP (BLamP k r) v

cons :: KPlain Term -> KPlain Term -> KPlain Term
cons h t = BToNomP "List" $ BInjectP ":" $ record [("head", h), ("tail", t)]

list :: [KPlain Term] -> KPlain Term
list = foldr cons (BToNomP "List" (BInjectP "[]" (BLeafP LRecEmpty)))

solveDepressedQuarticVal :: KPlain Term
solveDepressedQuarticVal =
    BLamP "params" $
    let_ "solvePoly" "id" $
    let_ "sqrts"
    ( BLamP "x" $
        let_ "r" (BAppP "sqrt" "x") $
        list ["r", BAppP "negate" "r"]
    ) $
    "if" $$:
    [ ("condition", inf d "==" (litInt 0))
    , ( "then",
        BAppP "concat" $
        "map" $$:
        [ ("list", BAppP "solvePoly" $ list [e, c, litInt 1])
        , ("mapping", "sqrts")
        ])
    , ( "else",
        BAppP "concat" $
        "map" $$:
        [ ( "list",
            BAppP "sqrts" $ BAppP "head" $ BAppP "solvePoly" $
            list
            [ BAppP "negate" (d %* d)
            , (c %* c) %- (litInt 4 %* e)
            , litInt 2 %* c
            , litInt 1
            ])
        , ( "mapping",
            BLamP "x" $
            BAppP "solvePoly" $
            list
            [ (c %+ ("x" %* "x")) %- (d %/ "x")
            , litInt 2 %* "x"
            , litInt 2
            ])
        ])
    ]
    where
        c = BGetFieldP "params" "c"
        d = BGetFieldP "params" "d"
        e = BGetFieldP "params" "e"

(%+), (%-), (%*), (%/), (%//), (%>), (%%), (%==) :: KPlain Term -> KPlain Term -> KPlain Term
x %+ y = inf x "+" y
x %- y = inf x "-" y
x %* y = inf x "*" y
x %/ y = inf x "/" y
x %// y = inf x "//" y
x %> y = inf x ">" y
x %% y = inf x "%" y
x %== y = inf x "==" y

factorsVal :: KPlain Term
factorsVal =
    BAppP "fix" $
    BLamP "loop" $
    BLamP "params" $
    if_ ((m %* m) %> n) (list [n]) $
    if_ ((n %% m) %== litInt 0)
    (cons m $ "loop" $$: [("n", n %// m), ("min", m)]) $
    "loop" $$: [("n", n), ("min", m %+ litInt 1)]
    where
        n = BGetFieldP "params" "n"
        m = BGetFieldP "params" "min"
        if_ b t f =
            BCaseP "False" (BLamP "_" f) (BCaseP "True" (BLamP "_" t) (BLeafP LAbsurd))
            `BAppP` (BLeafP (LFromNom "Bool") `BAppP` b)

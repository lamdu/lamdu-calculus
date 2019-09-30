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

import           Hyper
import           Hyper.Type.AST.Nominal
import           Hyper.Type.AST.Row
import           Hyper.Type.AST.Scheme
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
    (\(tag, typ) -> Pure . T.RExtend . RowExtend tag typ) recTail fields
    & T.TRecord & Pure

recordType :: [(T.Tag, Tree Pure Type)] -> Tree Pure Type
recordType = recExtends (_Pure # T.REmpty)

forAll ::
    [T.TypeVar] -> ([Tree Pure Type] -> Tree Pure Type) -> Tree Pure T.Scheme
forAll tvs mkType =
    tvs <&> T.TVar <&> (_Pure #) & mkType
    & Scheme T.Types
    { T._tType = QVars (Map.fromList [(tv, mempty) | tv <- tvs])
    , T._tRow = mempty
    } & Pure

stOf :: Tree Pure Type -> Tree Pure Type -> Tree Pure Type
stOf s a =
    T.Types (QVarInstances (mempty & Lens.at "res" ?~ a & Lens.at "s" ?~ s)) (QVarInstances mempty)
    & NominalInst "ST" & T.TInst & Pure

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
            & RowExtend "[]" (recordType []) & T.RExtend & Pure
            & RowExtend ":" (recordType [("head", tv), ("tail", listOf tv)])
            & T.RExtend & Pure
            & T.TVariant & Pure
            & Scheme (T.Types mempty mempty)
        }
    )
    where
        tv = _Pure # T.TVar "a"

listOf :: Tree Pure Type -> Tree Pure Type
listOf x =
    T.Types (QVarInstances (mempty & Lens.at "elem" ?~ x)) (QVarInstances mempty)
    & NominalInst (fst listTypePair) & T.TInst & Pure

boolType :: Tree Pure Type
boolType =
    T.Types (QVarInstances mempty) (QVarInstances mempty)
    & NominalInst (fst boolTypePair) & T.TInst & Pure

intType :: Tree Pure Type
intType =
    T.Types (QVarInstances mempty) (QVarInstances mempty)
    & NominalInst "Int" & T.TInst & Pure

boolTypePair :: (T.NominalId, Tree Pure (NominalDecl Type))
boolTypePair =
    ( "Bool"
    , _Pure # NominalDecl
        { _nParams = T.Types mempty mempty
        , _nScheme =
            _Pure # T.REmpty
            & RowExtend "True" (recordType []) & T.RExtend & Pure
            & RowExtend "False" (recordType []) & T.RExtend & Pure
            & T.TVariant & Pure
            & Scheme (T.Types mempty mempty)
        }
    )

maybeOf :: Tree Pure Type -> Tree Pure Type
maybeOf t =
    _Pure # T.REmpty
    & RowExtend "Just" t & T.RExtend & Pure
    & RowExtend "Nothing" (recordType []) & T.RExtend & Pure
    & T.TVariant & Pure

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

litInt :: Integer -> HPlain Term
litInt = BLeafP . LLiteral . PrimVal "Int" . BS8.pack . show

record :: [(T.Tag, HPlain Term)] -> HPlain Term
record = foldr (uncurry BRecExtendP) (BLeafP LRecEmpty)

($$:) :: HPlain Term -> [(T.Tag, HPlain Term)] -> HPlain Term
f $$: args = BAppP f (record args)

inf :: HPlain Term -> HPlain Term -> HPlain Term -> HPlain Term
inf l f r = f $$: [("l", l), ("r", r)]

factorialVal :: HPlain Term
factorialVal =
    BAppP "fix" $
    BLamP "loop" $
    BLamP "x" $
    "if" $$:
    [ ("condition", inf "x" "==" (litInt 0))
    , ("then", litInt 1)
    , ("else", inf "x" "*" (BAppP "loop" $ inf "x" "-" (litInt 1)))
    ]

euler1Val :: HPlain Term
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

let_ :: Var -> HPlain Term -> HPlain Term -> HPlain Term
let_ k v r = BAppP (BLamP k r) v

cons :: HPlain Term -> HPlain Term -> HPlain Term
cons h t = BToNomP "List" $ BInjectP ":" $ record [("head", h), ("tail", t)]

list :: [HPlain Term] -> HPlain Term
list = foldr cons (BToNomP "List" (BInjectP "[]" (BLeafP LRecEmpty)))

solveDepressedQuarticVal :: HPlain Term
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

(%+), (%-), (%*), (%/), (%//), (%>), (%%), (%==) :: HPlain Term -> HPlain Term -> HPlain Term
x %+ y = inf x "+" y
x %- y = inf x "-" y
x %* y = inf x "*" y
x %/ y = inf x "/" y
x %// y = inf x "//" y
x %> y = inf x ">" y
x %% y = inf x "%" y
x %== y = inf x "==" y

factorsVal :: HPlain Term
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

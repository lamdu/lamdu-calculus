{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}

module TestVals
    ( allDeps
    , list
    , factorialVal, euler1Val, solveDepressedQuarticVal
    , factorsVal
    , letItem, recordType
    , infixArgs
    , eLet
    , litInt, intType
    , listTypePair, boolTypePair
    ) where

import           AST
import           AST.Term.Nominal
import           AST.Term.Row
import           AST.Term.Scheme
import           Algebra.Lattice
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Map as Map
import           Lamdu.Calc.Definition (Deps(..))
import           Lamdu.Calc.Pure (($$), ($$:))
import qualified Lamdu.Calc.Pure as P
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type, (~>))
import qualified Lamdu.Calc.Type as T

import           Prelude.Compat

{-# ANN module ("HLint: ignore Redundant $" :: String) #-}

-- TODO: $$ to be type-classed for TApp vs BApp
-- TODO: TCon "->" instead of TFun

eLet :: V.Var -> Val () -> (Val () -> Val ()) -> Val ()
eLet name val mkBody = P.app (P.abs name body) val
    where
        body = mkBody $ P.var name

letItem :: V.Var -> Val () -> (Val () -> Val ()) -> Val ()
letItem name val mkBody = P.lambda name mkBody $$ val

recExtends :: Tree Pure T.Row -> [(T.Tag, Tree Pure Type)] -> Tree Pure Type
recExtends recTail fields =
    foldr
    (\(tag, typ) -> MkPure . T.RExtend . RowExtend tag typ) recTail fields
    & T.TRecord
    & MkPure

recordType :: [(T.Tag, Tree Pure Type)] -> Tree Pure Type
recordType = recExtends (_Pure # T.REmpty)

forAll ::
    [T.TypeVar] -> ([Tree Pure Type] -> Tree Pure Type) -> Tree Pure T.Scheme
forAll tvs mkType =
    tvs <&> T.TVar <&> (_Pure #) & mkType
    & Scheme T.Types
    { T._tType = QVars (Map.fromList [(tv, bottom) | tv <- tvs])
    , T._tRow = bottom
    }
    & MkPure

stOf :: Tree Pure Type -> Tree Pure Type -> Tree Pure Type
stOf s a =
    T.Types (QVarInstances (mempty & Lens.at "res" ?~ a & Lens.at "s" ?~ s)) (QVarInstances mempty)
    & NominalInst "ST" & T.TInst & MkPure

listTypePair :: (T.NominalId, Tree Pure (NominalDecl Type))
listTypePair =
    ( "List"
    , _Pure # NominalDecl
        { _nParams =
            T.Types
            { T._tType = bottom & Lens.at "elem" ?~ bottom
            , T._tRow = bottom
            }
        , _nScheme =
            _Pure # T.REmpty
            & RowExtend "[]" (recordType []) & T.RExtend & MkPure
            & RowExtend ":" (recordType [("head", tv), ("tail", listOf tv)])
            & T.RExtend & MkPure
            & T.TVariant & MkPure
            & Scheme (T.Types bottom bottom)
        }
    )
    where
        tv = _Pure # T.TVar "a"

listOf :: Tree Pure Type -> Tree Pure Type
listOf x =
    T.Types (QVarInstances (mempty & Lens.at "elem" ?~ x)) (QVarInstances mempty)
    & NominalInst (fst listTypePair) & T.TInst & MkPure

boolType :: Tree Pure Type
boolType =
    T.Types (QVarInstances mempty) (QVarInstances mempty)
    & NominalInst (fst boolTypePair) & T.TInst & MkPure

intType :: Tree Pure Type
intType =
    T.Types (QVarInstances mempty) (QVarInstances mempty)
    & NominalInst "Int" & T.TInst & MkPure

boolTypePair :: (T.NominalId, Tree Pure (NominalDecl Type))
boolTypePair =
    ( "Bool"
    , _Pure # NominalDecl
        { _nParams = T.Types bottom bottom
        , _nScheme =
            _Pure # T.REmpty
            & RowExtend "True" (recordType []) & T.RExtend & MkPure
            & RowExtend "False" (recordType []) & T.RExtend & MkPure
            & T.TVariant & MkPure
            & Scheme (T.Types bottom bottom)
        }
    )

maybeOf :: Tree Pure Type -> Tree Pure Type
maybeOf t =
    _Pure # T.REmpty
    & RowExtend "Just" t & T.RExtend & MkPure
    & RowExtend "Nothing" (recordType []) & T.RExtend & MkPure
    & T.TVariant & MkPure

infixType :: Tree Pure Type -> Tree Pure Type -> Tree Pure Type -> Tree Pure Type
infixType a b c = recordType [("l", a), ("r", b)] ~> c

infixArgs :: Val () -> Val () -> Val ()
infixArgs l r = P.record [("l", l), ("r", r)]

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

list :: [Val ()] -> Val ()
list = foldr cons (P.toNom "List" $ P.inject "[]" P.recEmpty)

cons :: Val () -> Val () -> Val ()
cons h t = P.toNom "List" $ P.inject ":" $ P.record [("head", h), ("tail", t)]

litInt :: Integer -> Val ()
litInt = P.lit "Int" . BS8.pack . show

factorialVal :: Val ()
factorialVal =
    P.var "fix" $$
    P.lambda "loop"
    ( \loop ->
        P.lambda "x" $ \x ->
        P.var "if" $$:
        [ ( "condition", P.var "==" $$
                infixArgs x (litInt 0) )
        , ( "then", litInt 1 )
        , ( "else", P.var "*" $$
                infixArgs x (loop $$ (P.var "-" $$ infixArgs x (litInt 1)))
            )
        ]
    )

euler1Val :: Val ()
euler1Val =
    P.var "sum" $$
    ( P.var "filter" $$:
        [ ("from", P.var ".." $$ infixArgs (litInt 1) (litInt 1000))
        , ( "predicate",
                P.lambda "x" $ \x ->
                P.var "||" $$ infixArgs
                ( P.var "==" $$ infixArgs
                    (litInt 0) (P.var "%" $$ infixArgs x (litInt 3)) )
                ( P.var "==" $$ infixArgs
                    (litInt 0) (P.var "%" $$ infixArgs x (litInt 5)) )
            )
        ]
    )

solveDepressedQuarticVal :: Val ()
solveDepressedQuarticVal =
    P.lambdaRecord "params" ["e", "d", "c"] $ \[e, d, c] ->
    letItem "solvePoly" (P.var "id")
    $ \solvePoly ->
    letItem "sqrts"
    ( P.lambda "x" $ \x ->
        letItem "r"
        ( P.var "sqrt" $$ x
        ) $ \r ->
        list [r, P.var "negate" $$ r]
    )
    $ \sqrts ->
    P.var "if" $$:
    [ ("condition", P.var "==" $$ infixArgs d (litInt 0))
    , ( "then",
            P.var "concat" $$
            ( P.var "map" $$:
                [ ("list", solvePoly $$ list [e, c, litInt 1])
                , ("mapping", sqrts)
                ]
            )
        )
    , ( "else",
            P.var "concat" $$
            ( P.var "map" $$:
                [ ( "list", sqrts $$ (P.var "head" $$ (solvePoly $$ list
                        [ P.var "negate" $$ (d %* d)
                        , (c %* c) %- (litInt 4 %* e)
                        , litInt 2 %* c
                        , litInt 1
                        ]))
                    )
                , ( "mapping",
                        P.lambda "x" $ \x ->
                        solvePoly $$ list
                        [ (c %+ (x %* x)) %- (d %/ x)
                        , litInt 2 %* x
                        , litInt 2
                        ]
                    )
                ]
            )
        )
    ]
    where
        (%+) = inf "+"
        (%-) = inf "-"
        (%*) = inf "*"
        (%/) = inf "/"

inf :: V.Var -> Val () -> Val () -> Val ()
inf str x y = P.var str $$ infixArgs x y

factorsVal :: Val ()
factorsVal =
    fix_ $ \loop ->
    P.lambdaRecord "params" ["n", "min"] $ \ [n, m] ->
    if_ ((m %* m) %> n) (list [n]) $
    if_ ((n %% m) %== litInt 0)
    (cons m $ loop $$: [("n", n %// m), ("min", m)]) $
    loop $$: [ ("n", n), ("min", m %+ litInt 1) ]
    where
        fix_ f = P.var "fix" $$ P.lambda "loop" f
        if_ b t f =
            nullaryCase "False" f
            (nullaryCase "True" t P.absurd)
            $$ (P.fromNom "Bool" $$ b)
        nullaryCase tag handler = P._case tag (defer handler)
        defer = P.lambda "_" . const
        (%>) = inf ">"
        (%%) = inf "%"
        (%*) = inf "*"
        (%+) = inf "+"
        (%//) = inf "//"
        (%==) = inf "=="

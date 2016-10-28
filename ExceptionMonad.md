# Exception monad in Lamdu Calculus

In Haskell, exception monads are not used for most code that can throw
exceptions. Usually, their use is localized where the domain of known
errors is fixed.

The reason for this, we believe, is the type of bind in Haskell's exception
monad:

`(>>=) :: Either err a -> (a -> Either err b) -> Either err b`

Note that `err` must be the same type in both sides of the bind - even
if the kinds of errors thrown by the two bound actions are vastly
different.

Haskell's sum types are also fully nominal, meaning that one must
manually declare all possible errors in all bound actions in a single
sum type, to use that as the error type.

This inhibits use of Haskell exception monads, and instead, much more
code uses dynamically typed exceptions (`SomeException` and the
`Exception` class).

However, with extensible sum types and Lamdu Calculus's powerful case
expressions, we can do better.

## Throwing errors

```
div x y =
  case y == 0 of
  #True  () -> #Error (#DivByZero ())
  #False () -> #Success (x / y)
```

The inferred type of `div` is:
```
forall err. #DivByZero ∉ err =>
Int -> Int -> +{ #Error : +{ #DivByZero : () | err }, #Success : Int }
```

Note that the only possible error is inferred, and we need not
manually declare an error type.

We also declare `fromJust` to extract a value from a `Maybe` type:

```
fromJust = \case
  #Just x -> #Success x
  #Nothing () -> #Error #NotJust
```
which has type:
```
forall a err. #NotJust ∉ err =>
+{ #Just : a, #Nothing : () } -> +{ #Success : a, #Error : +{ #NotJust : () | err } }
```

If we bind the two actions together (using an ordinary exception monad):

`\v -> fromJust v >>= div 1000`

The resulting type is automatically inferred to be:
```
forall err. {#NotJust, #DivByZero} ∉ err =>
+{ #Nothing : (), #Just : Int } ->
+{ #Error : +{#NotJust : (), #DivByZero : () | err}
 , #Success : Int
 }
```

The automatically inferred set of errors is visibly available in the type.

## Catching errors

We can declare an error catcher:

```
catch handler =
\case
  #Success v -> #Success v
  #Error -> handler
```

And then we can catch just the `#DivByZero` error above:

```
\v ->
catch (\case
       #DivByZero -> #Success 0
       err -> #Error err)
(fromJust v >>= div 1000)`
```

The inferred type then becomes:
```
forall err. {#NotJust} ∉ err =>
+{ #Nothing : (), #Just : Int } ->
+{ #Error : +{#NotJust : () | err}
 , #Success : Int
 }
```

Once all errors are caught, a result type becomes:

`forall err. +{ Error : +{| err}, #Success : ... }`

We can then eliminate the variant wrapper with:

```
successful : forall err a. +{ Error : +{| err}, #Success : a } -> a
successful = \case
  #Error -> absurd
  #Success -> id
```

This instantiates `err` to be the empty sum type (void), and is thus
allowed to eliminate the #Error/#Success wrapper to yield an `a`.

# lamdu-calculus

An extended typed Lambda Calculus AST.

Used by [Lamdu](http://www.lamdu.org/) as the underlying unsugared language.

The Lamdu Calculus language is a statically typed polymorphic
non-dependent lambda calculus extension.

The language does not include a parser, as it is meant to be used
structurally via its AST directly. It does include a pretty-printer,
for ease of debugging.

Type inference for Lamdu Calculus is implemented in a [separate
package](https://github.com/lamdu/Algorithm-W-Step-By-Step).

## Values

The term language supports lambda abstractions and variables, literal
values of custom types, holes, nominal type wrapping/unwrapping,
extensible variant types and extensible records.

## Types

The type language includes nominal types with polymoprhic components,
extensible record types (row types) and extensible variant types
(polymorphic variants / column types).

## Composite types

In Lamdu Calculus, both records and variants are "composite" types and
share an underlying AST, using a phantom type to distinguish them.

Records are sets of typed and named fields.

Variants are a value of a set of possible typed data constructors.

Both records and variants are order-agnostic, and disallow repeated
appearance of the same names for fields or data constructors.

Both records and variants are extensible. This is usually called "row
types" for records and "polymorphic variants" for variants. We use the
terminology of "row" and "column" types instead.

## Records

In the term language, records are constructed using these AST constructions:

`BLeaf LRecEmpty` denotes the empty record (denote in pseudo-syntax as `()`).
Its type is `TRecord CEmpty`.


`BRecExtend ident (value : T) (rest : R)` denotes a record extension
of an existing record `rest`.
Its type is `TRecord (CExtend ident T R)`.

A sequence of `BRecExtend` followed by a `BLeaf LRecEmpty` is denoted
in pseudo-syntax as { x : T, y : U, ... }.

To deconstruct a record, we use the `GetField` operation (denoted in
pseudo-syntax as `.`).

### Row types

Row types are denoted using a record type variable.

For example, lets examine a lambda abstraction. Assume `(+) : Int ->
Int -> Int`.

```
\vector -> vector.x + vector.y
```

We can infer the type:

`{ x : Int, y : Int } -> Int`

But the most general type is:

`forall r1. {x, y} ∉ r1 => { x : Int, y : Int | r1 } -> Int`<sup>1</sup>

The lambda may be applied with a record that contains more fields
besides `x` and `y`, and that is what the `| r1` denotes. Note that to
enforce the no-duplication requirement Lamdu Calculus uses a
constraint on composite type variables, for each field that they may
not duplicate.

<sup>1. The `|` symbol in the pseudo-syntax is used to indicate
that some set of fields denoted by the variable that follows (in this
case, `r1`) is concatenated to the set)</sup>

## Variants

In the term language, variants are constructed using value *injection*.

Injection means *lifting* a value into a variant type - thereby
throwing away type information to make the type compliant with a
larger variant type.

For example, let's look at the type:

`+{ Nothing : (), Just : Int }`

This pseudo syntax means the structural sum type isomorphic to
Haskell's `Maybe Int`.

The value `5 : Int` is not of the type: `+{ Nothing : (), Just : Int }`.

In Haskell, we use `Just` to lift 5 from `Int` to `Maybe Int`.  In
Lamdu Calculus, we inject via `BInject (Inject "Just" 5)`, which we denote in
pseudo-syntax as `#Just 5`.

`BInject (Inject ident (value : T))` *injects* a given value into a
sum type. Its type is `forall alts. ident ∉ alts => TSum (CExtend ident T alts)`.

This type means that the injected value allows any set of typed
alternatives to exist in the larger variant.

### Case expressions

Deconstructing a variant requires a case statement. Lamdu Calculus
case statements *peel* one alternate case at a time, so need to be
composed to create an ordinary full case.

`BCase (Case tag handler default)` denoted in pseudo syntax as
```
\case
  #tag -> handler
  _ -> default
```

The above case expression creates a function with a variant
parameter. It analyzes its argument, and if it is a `#tag`, the given
`handler` is invoked with the typed content of the `#tag`.

If the argument is not a `#tag`, then the `default` handler is
invoked. The `default` handler is given a smaller sum type as an
argument. A sum type which no longer has the `#tag` case inside it, as
that was ruled out.

Let's examine an example:

```
\case
  #Just -> (+1)
  _ -> \case
         #Nothing -> \() -> 0
         _ -> ?
```

The above composed case expression will match against `#Just`:

 * Match: it will evaluate to the content of the `#Just` added to 1.

 * Mismatch: it will match against `#Nothing`:

   * Match: it will ignore the empty record contained in the
     `#Nothing` case, and evaluate to 0

   * Mismatch: Evaluate to a hole (denoted by `?`) which is like
     Haskell's `undefined`, and takes on any type.

The type of the above case statement would be inferred to:

```
forall v1. (Just, Nothing) ∉ v1 =>
+{ #Just : Int , #Nothing : () | v1 } -> Int
```

Note that the case statement allows *any* structural variant type that
has the proper `Nothing` and `Just` cases (and it would crash if the
value happens to be neither `Nothing` nor `Just`). This is not
typically what we want. We'd like to *close* the sum type so it is *not* extensible.

To do that, we must also support the empty case statement that matches
no possible alternatives, allowing us to *close* the composition. The
empty case statement AST construction is:

BLeaf LAbsurd, and is denoted as `absurd` (as it is the analogue of
the `absurd` function in Haskell and Agda). The type of `absurd` is:
`forall r. +{} -> r` (`+{}` is the empty sum type, aka `Void`).

We can now close the above case expression:

```
\case
  #Just -> (+1)
  _ -> \case
         #Nothing -> \() -> 0
         _ -> absurd
```

And now our inferred type will be simpler:

`+{ #Just : Int, #Nothing : () } -> Int`

As a short-hand for nested/composed cases, we'll use Haskell-like
syntax for cases as well, meaning the expanded, composed case. We'll
also bind variables in left hand of `->` to avoid some more clutter.

```\case
#Just x -> x+1
#Nothing () -> 0
```

### Example use-case: Composing interpreters

We can define single-command interpreters:

```
interpretAdd default =
  \case
    #Add {x, y} -> x + y
    _ -> default
```

```
interpretMul default =
  \case
    #Mul {x, y} -> x * y
    _ -> default
```

And then we can compose them:

```
interpreterArithmetic = interpretAdd . interpretMul

interpreter = (interpreterArithmetic . interpreterConditionals) absurd
```

Yielding a single interperter that can handle the full set of cases in
its composition.

### Example use-case: Exception Monads

See the [Exception Monad](ExceptionMonad.md) use-case for a more
compelling example use-case of extensible variants.

# Nominal types

# Future plans

* Unifying with the underlying AST in
  [AlgoWMutable](https://github.com/Peaker/AlgoWMutable) which
  implements type inference more efficiently than
  [Algorithm-W-Step-By-Step](https://github.com/lamdu/Algorithm-W-Step-By-Step)
  which is compatible with this package.

* Support for type-classes

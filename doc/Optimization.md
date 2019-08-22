# The process for optimizing the inference with SPECIALIZE and RULES pragmas

This document is work-in-progress! I need help!

Run the benchmark while dumping GHC core:

* If building after not changing the code, force recomplication of `benchmark.hs` by adding a space or something
* `stack bench --ghc-options "-dumpdir dumps -ddump-simpl -dsuppress-coercions -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-timestamps"`
* Open `test/benchmark.dump-simpl` in your editor
* Skim over `benchInferPure` and some of its calls
* Now look for usages of type applications and spurious constraint introduction calls

## Type applications and SPECIALIZE

Type applications may look like:

* `pruneDeps1 @ ()`
* `emptyScope @ ('Knot UVar)`
* `$fNFDataTypeError_$crnf @ ('Knot Pure)`

Now we need to see which of those are benign.
If the type of the definition, does not have class constraints on these variables, such as

    pruneDeps :: Tree (Ann a) V.Term -> Deps -> Deps

Then this is a benign type application (i.e no benefit from adding a `SPECIALIZE` pragma for it).
Other applications may not be benign but are not significant,
for example if they are only called one time when the inference results in an error, but not in inner loops,
such as the `NFData` instance above.

We want to add `SPECIALIZE` pragmas to significant unspecialized (using type applications) calls.

We can find such type applications using the `tools/core-type-apps.py` script.

## Constraint introductions and RULES

Let's start with an example - `AST.Infer.infer` calls `inferRecursive` which introduces the `Infer` constraint for the term type's nodes. This call is equivalent to `id` and should disappear, but GHC isn't always smart enough for it.

In the core, it appeared in the beginning of `$s$winfer1` (specialized `infer`) via a call to `$s$fInfermTerm_$cinferRecursive_$s$w$cinferRecursive` which is itself a specialization of `inferRecursive`.

We helped GHC remove it by adding the following rule:

    {-# RULES "inferRecursive/PureInfer/Term" inferRecursive @PureInfer @Term Proxy Proxy = id #-}

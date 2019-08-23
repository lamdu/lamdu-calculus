# The process for optimizing the inference with SPECIALIZATION

This document is work-in-progress! I need help!

Run the benchmark while dumping GHC core:

* If building after not changing the code, force a build via `stack clean lamdu-calculus`
* `stack bench --ghc-options "-dumpdir dumps -ddump-simpl -dsuppress-coercions -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-timestamps"`
* This generated `.dump-simpl` files in the `dumps` folder
* The top-level file of interest is `dumps/test/benchmark.dump-simpl`
* In `dumps/src/Lamdu/Calc/` there are dump files for `Infer` and `Term` which are also of interest

## Searching for type applications

The type applications may look like:

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

We can find such type applications using the `tools/core-type-apps.py` script and manually searching for important functions in the code (the wip script isn't fully functional..)

Note that apparently sometimes specializing one function causes GHC to not use a specialized version of an inner call due to type family confusion.

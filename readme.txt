TODO

Some bugs related to custom types in interpreter and type reconstructor



==============
Revelation:

the input for the nom parser doesn't have to be &str. It can be (&str, ContextStack) or Context or whatever I want

==============

records = tuples with fields in a total order (perhaps alphabetic by name)

# ideas to explore

* pattern matching exhaustiveness checking
* operators
* pattern-matching in function definition:
    fact 0 = 1
    fact n = n * (fact (n - 1))
* open variant types
* closed variant types
* let-desugaring
* CSP-ify
* low-level codegen (procedural IR)
* wasm codegen (through cranelift)
* tail-call optimization
* constant folding
* extensible records
* alpha and beta reductions
* compilation attributes (@inline, @comptime, @tailrec, @derive(Eq, .., Ord))
* effect handling (like multicore ocaml)
* file-module
* higher-kinded types (mostly for interface constraints like "Ord", "Eq", "Hash", etc.)
* derive macros
* quantitative type theory
* perceus garbage collection

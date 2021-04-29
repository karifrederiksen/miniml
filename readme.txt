TODO

Custom type should be able to contain other types for example `List a` or `List Int` kinda thing

the current CustomType should probably be called CustomTypeSymbol

===============


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

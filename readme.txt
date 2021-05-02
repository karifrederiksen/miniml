TODO:

* pattern-matching in function definition:
    fact 0 = 1
    fact n = n * (fact (n - 1))
* Exhaustiveness check for patterns
* Replace panics with Error variants
* error sourcing (wrapping AST nodes with annotation nodes, containing source-code spans and stuff)

==============
Revelation:

the input for the nom parser doesn't have to be &str. It can be (&str, ContextStack) or Context or whatever I want

==============

records = tuples with fields in a total order (perhaps alphabetic by name)

# ideas to explore

* quantitative type theory
* arbitrary order of statements (statements are exclusively top-level)
    * There can be a transformation for putting them in dependence-order, and we can modify the binding-statement so that it contains a vector of bindings so that bindings that are mutually recursive will be part of the same statement.
* operators
* open variant types
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
* perceus garbage collection

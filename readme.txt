TODO:

* Replace panics with Error variants
* Build a javascript codegen to replace the interpreter. The interpreter is too much work to maintain.
    * I think there exists some Javascript interpreter crate that I could use for running the output

==============

# ideas to explore

* dependency graph
    * reorder declarations based on the dependency graph
* odin-style variants
    * the name of the `case` is simplfy the name of whatever it contains. Example:
      type Thing = String | Int | (Int, Int)
    Then we can match on it like so:
      match x with String s -> s, Int i -> String.fromInt i , (Int l, Int r) -> String.fromInt
    Maybe it should be qualified like `Thing.String s`?

    Then Custom types can be simplified to only define one atomic type, instead of defining multiple variants of a type
      
* algebraic effects and effect handlers (top level "effect Print a where a : Display")
* arbitrary order of statements (statements are exclusively top-level)
    * There can be a transformation for putting them in dependence-order, and we can modify the binding-statement so that it contains a vector of bindings so that bindings that are mutually recursive will be part of the same statement.
* rewrite parser
    * I've already made a lexer, but nom doesn't play well with custom input types, so the parser has to be rebuilt from the ground up.
    * Parser should support having a context (this was very difficult in nom)
    * Stateless input like &[Token] is very nice to work with
* pattern-matching in function definition:
    fact 0 = 1
    fact n = n * (fact (n - 1))
* operators (generic in such as way that the operators are user-definable)
* quantitative type theory
    * do I need erased types? maybe a linear type modifier is enough?
* let-desugaring
* CSP-ify
* procedural IR for expressing mutations and loops
    * interpreter for this IR
* wasm codegen (through cranelift)
* tail-call optimization
* constant folding
* records
    * unify if they have _exactly_ the same fields. order doesn't matter
    * can be implemented as a tuple where the fields are ordered alphabetically
        * so { b: Int, a: Bool, c: {} } and { c: {}, a: Bool, b: Int } both become (Bool, Int, {}) at runtime
* extensible records
    * unify if the extensible record's fields are a subset of the other one's fields. order doesn't matter
    * if we monomorphize generic function then this becomes trivial
    * if we don't, then all extensible records have to have a field-mapping passed in with them
        * so passing { a: Bool, b: Int, c: Int } into { x | b: Int, c: Int } -> { x | b: Int } would pass
        ((1, 2), (true, 4, 4)) where the mapping (1, 2) coresponds to the position of the b and c fields in the input tuple. These position would likely be offsets rather than indices.
        * or maybe we have the field-mapping be a global constant and just pass a reference to it
    * I think the 2nd approach is more interesting
* alpha and beta reductions
* perceus garbage collection
* compilation attributes (@inline, @comp_time, @non_tail_rec, @derive(Eq, .., Ord))
    * @inline: this expression should be duplicated at each call site
    * @comp_time: this expression must be evaluated fully at compile time(meaning it isn't allowed to capture a variable from the stack)
    * @non_tail_rec: tail-recursion would be enforced for recursive functions unless this attribute is specified
* modules (each file is a module)
* higher-kinded types (for constraints like "Ord", "Eq", "Hash", "Serialize", "Deserialize", etc.)
        type StringBuilder
            = Single String
            | Multi (Vec StringBuilder)

        class Display a where
            build_display : a -> StringBuilder

        display :: Display a, Ord a => a -> String
* derive macros for traits


## 

[Haskell's IR ((System F)++)]  (https://www.youtube.com/watch?v=uR_VzYxvbxg)
```
data Expr
    = Var  Var
    | Lit  Literal
    | App  Expr         -- both term and type application
    | Lam  Var Expr     -- both term and type lambda
    | Let  Bind Expr
    | Case Expr Var Type [(AltCon, [Var], Expr)]
    | Type Type         -- promote type to be an expr so types can be applied

data Var
    = Id Name Type
    | TyVar Name Kind

type Kind = Type

data Type
    = TyVarTy  Var
    | LitTy    TyLit
    | AppTy    Type Type
    | TyConApp TyCon [Type]
    | FunTy    Type Type
    | ForAllTy Var Type
```
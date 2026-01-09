# Appendix A: Syntax Comparison

For readers coming from other functional languages, these tables map familiar syntax to Lean equivalents. The goal is not completeness but orientation: enough to read Lean code without constantly consulting documentation.

## Type Declarations

| Concept        | Haskell                                   | OCaml                                    | Lean 4                                        |
| -------------- | ----------------------------------------- | ---------------------------------------- | --------------------------------------------- |
| Type alias     | `type Name = String`                      | `type name = string`                     | `abbrev Name := String`                       |
| Product type   | `data Point = Point Int Int`              | `type point = { x: int; y: int }`        | `structure Point where x : Int; y : Int`      |
| Sum type       | `data Maybe a = Nothing \| Just a`        | `type 'a option = None \| Some of 'a`    | `inductive Option (α : Type) where ...`       |
| Recursive type | `data List a = Nil \| Cons a (List a)`    | `type 'a list = Nil \| Cons of 'a * ...` | `inductive List (α : Type) where ...`         |
| Type class     | `class Eq a where (==) :: a -> a -> Bool` | N/A (use modules)                        | `class Eq (α : Type) where eq : α → α → Bool` |
| Instance       | `instance Eq Int where ...`               | N/A                                      | `instance : Eq Int where ...`                 |

## Function Definitions

| Concept             | Haskell                                       | OCaml                                       | Lean 4                                         |
| ------------------- | --------------------------------------------- | ------------------------------------------- | ---------------------------------------------- |
| Named function      | `f x = x + 1`                                 | `let f x = x + 1`                           | `def f (x : Nat) := x + 1`                     |
| Lambda              | `\x -> x + 1`                                 | `fun x -> x + 1`                            | `fun x => x + 1`                               |
| Type signature      | `f :: Int -> Int`                             | `val f : int -> int`                        | `def f : Int → Int`                            |
| Pattern matching    | `case x of { Just a -> ...; Nothing -> ... }` | `match x with Some a -> ... \| None -> ...` | `match x with \| some a => ... \| none => ...` |
| Guards              | `f x \| x > 0 = ... \| otherwise = ...`       | N/A (use if)                                | `if x > 0 then ... else ...`                   |
| Where clause        | `f x = y + 1 where y = x * 2`                 | `let f x = let y = x * 2 in y + 1`          | `def f x := let y := x * 2; y + 1`             |
| Partial application | `map (+1)`                                    | `List.map ((+) 1)`                          | `List.map (· + 1)`                             |

## Monads and Effects

| Concept           | Haskell                           | OCaml                   | Lean 4                           |
| ----------------- | --------------------------------- | ----------------------- | -------------------------------- |
| Bind              | `x >>= f` or `do { a <- x; f a }` | N/A (use let*)          | `x >>= f` or `do let a ← x; f a` |
| Return            | `return x` or `pure x`            | N/A                     | `pure x`                         |
| Monad transformer | `StateT s m a`                    | N/A                     | `StateT σ m α`                   |
| IO action         | `IO a`                            | `unit -> 'a`            | `IO α`                           |
| Print             | `putStrLn "hello"`                | `print_endline "hello"` | `IO.println "hello"`             |

## Common Operations

| Concept              | Haskell              | OCaml                        | Lean 4                        |
| -------------------- | -------------------- | ---------------------------- | ----------------------------- |
| List literal         | `[1, 2, 3]`          | `[1; 2; 3]`                  | `[1, 2, 3]`                   |
| List cons            | `x : xs`             | `x :: xs`                    | `x :: xs`                     |
| List map             | `map f xs`           | `List.map f xs`              | `xs.map f` or `List.map f xs` |
| List filter          | `filter p xs`        | `List.filter p xs`           | `xs.filter p`                 |
| Function composition | `f . g`              | N/A (use `fun x -> f (g x)`) | `f ∘ g`                       |
| String concat        | `s1 ++ s2`           | `s1 ^ s2`                    | `s1 ++ s2`                    |
| Tuple                | `(a, b)`             | `(a, b)`                     | `(a, b)`                      |
| Tuple access         | `fst p`, `snd p`     | `fst p`, `snd p`             | `p.1`, `p.2`                  |
| If expression        | `if c then t else f` | `if c then t else f`         | `if c then t else f`          |

## Key Differences

**Explicit types**: Lean requires explicit type annotations more often than Haskell. Where Haskell infers `id x = x` has type `a -> a`, Lean prefers `def id (x : α) : α := x`.

**Unicode**: Lean uses unicode operators freely: `→` for function types, `∀` for universal quantification, `∧` for conjunction. ASCII alternatives exist (`->`, `forall`, `/\`) but idiomatic Lean uses unicode.

**Termination**: Every Lean function must terminate. Haskell allows infinite loops; Lean rejects them. Use `partial` for functions you cannot prove terminating.

**Dependent types**: Lean's `(n : Nat) → Vector α n` has no Haskell equivalent. Types depending on values is what makes Lean a theorem prover.

**Propositions vs Booleans**: Lean distinguishes `Prop` (logical propositions, erased at runtime) from `Bool` (computational booleans). Haskell's `Bool` is both.

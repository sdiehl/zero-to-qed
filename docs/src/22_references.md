# References

## Official Documentation

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

## Theorem Proving Games

- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) - HHU Düsseldorf
- [Real Analysis Game](https://adam.math.hhu.de/#/g/AlexKontorovich/RealAnalysisGame) - Rutgers University
- [Reintroduction to Proofs](https://adam.math.hhu.de/#/g/emilyriehl/ReintroductionToProofs) - A game introducing proofs, dependent type theory, and Lean prepared by Emily Riehl for a first year seminar at Johns Hopkins (Fall 2025). Covers types, functions, products, coproducts, quantifiers, and dependent types through interactive puzzles. [Source](https://github.com/emilyriehl/ReintroductionToProofs)

## University Courses (Lean 4)

- [Functional Programming and Theorem Proving](https://web.stanford.edu/class/cs99/) - Stanford University
- [Formal Proof and Verification](https://browncs1951x.github.io/) - Brown University
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001) - Fordham University
- [Formalising Mathematics](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024) - Imperial College London
- [Formalized Mathematics in Lean](https://github.com/fpvandoorn/LeanCourse24) - University of Bonn
- [Interactive Theorem Proving](https://www.tcs.ifi.lmu.de/lehre/ss-2024/itp_de.html) - LMU Munich
- [Proofs and Programs](http://math.iisc.ac.in/~gadgil/proofs-and-programs-2025/) - Indian Institute of Science
- [Theorem Proving with Lean](https://adomani.github.io/Syllabus/MA4N1/toc) - University of Warwick
- [Logic and Mechanized Reasoning](https://avigad.github.io/lamr/) - Carnegie Mellon University
- [Lean for Scientists and Engineers](https://github.com/ATOMSLab/LFSE2024/) - University of Maryland
- [An Introduction to Lean 4](https://www.uv.es/coslloen/Lean4/) - Universitat de València
- [Interactive Theorem Proving in Lean](https://matematiflo.github.io/LeanCompactCourse/) - MPI Leipzig
- [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025) - Various institutions
- [Formal Methods in Mathematics](https://elo.mastermath.nl/course/info.php?id=1121) - Mastermath (Netherlands)
- [Logique et démonstrations assistées](https://www.imo.universite-paris-saclay.fr/~patrick.massot/enseignement/) - Université Paris-Saclay
- [Semantics and Verification of Software](https://moves.rwth-aachen.de/teaching/ws-2024-25/savos/) - RWTH Aachen
- [Formal Proof](https://github.com/math4345) - Ohio State University
- [Lean Community Course Catalog](https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/data/courses.yaml) - Full listing

## University Courses (Lean 3)

- [Logic and Proof](https://lean-lang.org/logic_and_proof/) - Carnegie Mellon University
- [Modern Mathematics with Lean](https://gihanmarasingha.github.io/modern-maths-pages/) - University of Exeter
- [Graduate Introduction to Logic](https://math.hawaii.edu/wordpress/bjoern/math-654-fall-2022/) - University of Hawaii
- [Introduction to Proofs with Lean](https://sinhp.github.io/teaching/2022-introduction-to-proofs-with-Lean) - Johns Hopkins University
- [Logic and Modelling](https://studiegids.vu.nl/en/2022-2023/courses/X_401015) - Vrije Universiteit Amsterdam
- [Harvard MATH 161](https://beta.my.harvard.edu/course/MATH161/2026-Spring/001) - University course on theorem proving with Lean and Mathlib.

## Syntax Comparison: Haskell, OCaml, and Lean

For readers coming from other functional languages, this table maps familiar syntax to Lean equivalents.

### Type Declarations

| Concept        | Haskell                                   | OCaml                                    | Lean 4                                        |
| -------------- | ----------------------------------------- | ---------------------------------------- | --------------------------------------------- |
| Type alias     | `type Name = String`                      | `type name = string`                     | `abbrev Name := String`                       |
| Product type   | `data Point = Point Int Int`              | `type point = { x: int; y: int }`        | `structure Point where x : Int; y : Int`      |
| Sum type       | `data Maybe a = Nothing \| Just a`        | `type 'a option = None \| Some of 'a`    | `inductive Option (α : Type) where ...`       |
| Recursive type | `data List a = Nil \| Cons a (List a)`    | `type 'a list = Nil \| Cons of 'a * ...` | `inductive List (α : Type) where ...`         |
| Type class     | `class Eq a where (==) :: a -> a -> Bool` | N/A (use modules)                        | `class Eq (α : Type) where eq : α → α → Bool` |
| Instance       | `instance Eq Int where ...`               | N/A                                      | `instance : Eq Int where ...`                 |

### Function Definitions

| Concept             | Haskell                                       | OCaml                                       | Lean 4                                         |
| ------------------- | --------------------------------------------- | ------------------------------------------- | ---------------------------------------------- |
| Named function      | `f x = x + 1`                                 | `let f x = x + 1`                           | `def f (x : Nat) := x + 1`                     |
| Lambda              | `\x -> x + 1`                                 | `fun x -> x + 1`                            | `fun x => x + 1`                               |
| Type signature      | `f :: Int -> Int`                             | `val f : int -> int`                        | `def f : Int → Int`                            |
| Pattern matching    | `case x of { Just a -> ...; Nothing -> ... }` | `match x with Some a -> ... \| None -> ...` | `match x with \| some a => ... \| none => ...` |
| Guards              | `f x \| x > 0 = ... \| otherwise = ...`       | N/A (use if)                                | `if x > 0 then ... else ...`                   |
| Where clause        | `f x = y + 1 where y = x * 2`                 | `let f x = let y = x * 2 in y + 1`          | `def f x := let y := x * 2; y + 1`             |
| Partial application | `map (+1)`                                    | `List.map ((+) 1)`                          | `List.map (· + 1)`                             |

### Monads and Effects

| Concept           | Haskell                           | OCaml                   | Lean 4                           |
| ----------------- | --------------------------------- | ----------------------- | -------------------------------- |
| Bind              | `x >>= f` or `do { a <- x; f a }` | N/A (use let*)          | `x >>= f` or `do let a ← x; f a` |
| Return            | `return x` or `pure x`            | N/A                     | `pure x`                         |
| Monad transformer | `StateT s m a`                    | N/A                     | `StateT σ m α`                   |
| IO action         | `IO a`                            | `unit -> 'a`            | `IO α`                           |
| Print             | `putStrLn "hello"`                | `print_endline "hello"` | `IO.println "hello"`             |

### Common Operations

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

### Key Differences

**Explicit types**: Lean requires explicit type annotations more often than Haskell. Where Haskell infers `id x = x` has type `a -> a`, Lean prefers `def id (x : α) : α := x`.

**Unicode**: Lean uses unicode operators freely: `→` for function types, `∀` for universal quantification, `∧` for conjunction. ASCII alternatives exist (`->`, `forall`, `/\`) but idiomatic Lean uses unicode.

**Termination**: Every Lean function must terminate. Haskell allows infinite loops; Lean rejects them. Use `partial` for functions you cannot prove terminating.

**Dependent types**: Lean's `(n : Nat) → Vector α n` has no Haskell equivalent. Types depending on values is what makes Lean a theorem prover.

**Propositions vs Booleans**: Lean distinguishes `Prop` (logical propositions, erased at runtime) from `Bool` (computational booleans). Haskell's `Bool` is both.

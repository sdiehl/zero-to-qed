# Basics

True to the title of this article series, we start from zero. Not "Hello, World!" but an actual zero: the natural number that forms the foundation of arithmetic.

## Zero

```lean
{{#include ../../src/ZeroToQED/Basics.lean:from_zero}}
```

This first example introduces three toplevel **declarations** that you will use constantly:

- **`def`** defines a named value or function. Here `def zero : Nat := 0` declares that `zero` has type `Nat` (natural number) and equals `0`. Every Lean program is built from **`def`** declarations.

- **`#eval`** evaluates an expression and prints the result. This command runs code immediately, useful for testing as you work. Commands starting with `#` are interactive queries that do not create permanent **definitions**.

- **`theorem`** declares a proposition to be proved. The name `deep_thought` labels the statement `fortyTwo = 6 * 7`, and `rfl` (**reflexivity**) proves it by computation: both sides reduce to `42`. Unlike `def`, **theorem** proofs are opaque and never unfold during type checking.

The natural numbers are perhaps the most fundamental type in mathematics and programming. Lean represents them inductively: zero is the base case, and every other natural number is the successor of another. This simple construction gives us the entire infinite sequence 0, 1, 2, 3, and so on.

## Natural Numbers

Natural numbers in Lean represent non-negative integers, defined inductively just as Peano intended in 1889. They support standard arithmetic operations, but subtraction truncates at zero since negative results would fall outside the type. This has caused approximately as many bugs as unsigned integers in C, which is to say: more than anyone wants to admit.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:natural_numbers}}
```

Lean has two equality operators. The `==` operator is **decidable equality**, returning a `Bool` for use in programs. The `=` operator is **propositional equality**, returning a `Prop` for use in proofs. For runtime computation, use `==`. For stating theorems, use `=`. Both work with `#eval` because Lean can decide equality for natural numbers.

## Integers

When you need negative numbers, use `Int`. Integer arithmetic behaves as you would expect from standard mathematics, unburdened by the horrors of two's complement overflow that have plagued systems programmers since the PDP-11.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:integers}}
```

## Modules and Namespaces

Lean organizes code into **modules** and **namespaces**. This section covers the practical syntax; we revisit the underlying mechanics in [Type Theory](./12_type_theory.md).

**Files and Modules.** Each `.lean` file defines a **module**. The file `Foo/Bar/Baz.lean` defines module `Foo.Bar.Baz`. To use definitions from another module, import it at the top of your file with `import Mathlib.Data.Nat.Prime` or `import Mathlib` for an entire library. Imports are transitive: if `A` imports `B` and `B` imports `C`, then `A` has access to `C`'s definitions. The Lake build system (covered in [Build System](./05_build_system.md)) manages dependencies and ensures modules are compiled in the correct order.

**Namespaces.** **Namespaces** group related definitions under a common prefix. They prevent name collisions and organize large codebases:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:namespace_example}}
```

The angle brackets `⟨` and `⟩` are shorthand for structure constructors. These two lines are equivalent:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:angle_brackets}}
```

The **`open`** command brings namespace contents into scope, so you can write `dist` instead of `Geometry2.dist`:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:open_example}}
```

**Sections and Variables.** The **`section`** command creates a scope for temporary declarations. Variables declared with **`variable`** inside a section are automatically added as parameters to definitions that use them:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:section_variable}}
```

The bracket notation deserves explanation. Round brackets mark explicit arguments you pass directly. Square brackets mark **instance arguments** that Lean finds automatically through type class resolution. Here, `[Add α]` means the type must have an `Add` instance, which provides the `+` operator. Curly braces mark implicit arguments that Lean infers from context.

**Visibility.** By default, all definitions are public. Mark definitions as `private` to hide them outside the current file:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:visibility}}
```

**Export.** The **`export`** command re-exports definitions from one namespace into another, making them available without opening the original:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:export_example}}
```

**The Init Namespace.** Every Lean file automatically imports the `Init` namespace, which provides foundational types and functions without explicit imports. This is Lean's equivalent of Haskell's `Prelude` or OCaml's `Stdlib`, though the design differs.

| Category         | Contents                                                                                                         |
| ---------------- | ---------------------------------------------------------------------------------------------------------------- |
| Core types       | `Unit`, `Bool`, `Nat`, `Int`, `String`, `Char`, `Option`, `List`, `Array`                                        |
| Monads           | `Id`, `Option`, `Except`, `StateM`, `ReaderM`, `IO`, plus transformers `StateT`, `ReaderT`, `ExceptT`, `OptionT` |
| Type classes     | `Monad`, `Functor`, `Applicative`, `ToString`, `Repr`, `Inhabited`, `BEq`, `Ord`, `Hashable`                     |
| Proof primitives | `Eq`, `And`, `Or`, `Not`, `True`, `False`, `Exists`                                                              |

Haskell's Prelude is imported unqualified by default, meaning all its names are directly available. You disable this with `NoImplicitPrelude`. OCaml takes the opposite approach: all modules are available qualified (you write `List.map`), and you must explicitly `open List` to use names unqualified.

Lean splits the difference. The `Init` namespace is always available without qualification. Unlike Haskell, there is no pragma to disable it, but you can shadow any definition with your own. The `Init` hierarchy is organized into submodules (`Init.Prelude`, `Init.Data`, `Init.Control`), but from the user's perspective it appears as a unified set of defaults.

## Functions

Functions are first-class values in Lean. You can define them in multiple ways and partially apply them to create new functions.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:functions}}
```

When declaring multiple parameters of the same type, you can group them: `(x y z : Nat)` is identical to `(x : Nat) (y : Nat) (z : Nat)`. Use whichever reads better.

## Pattern Matching

Pattern matching is a powerful feature for destructuring data and defining functions by cases.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:pattern_matching}}
```

The factorial definition uses `n + 1` rather than the seemingly more natural `| n => n * factorial (n - 1)`. This is not a style choice. Lean must verify that recursive calls terminate, and it does this by checking that arguments decrease structurally. The pattern `n + 1` desugars to `Nat.succ n`, explicitly matching a successor. When you recurse on `n`, Lean sees that `n` is structurally smaller than `Nat.succ n`. With `| n => ... factorial (n - 1)`, Lean cannot immediately see that `n - 1` is smaller than `n` (subtraction is a function, not a constructor), so termination checking fails.

The `describe` function uses string interpolation with `s!"many ({n})"`. The `s!` prefix enables interpolation: expressions inside `{...}` are evaluated and converted to strings. Without the prefix, curly braces are literal characters.

## More Declarations

**Abbreviations** are transparent definitions that unfold automatically during elaboration. Use them for type aliases:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:abbrev_example}}
```

The interactive commands `#check`, `#print`, and `#reduce` help you explore code:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:check_print_reduce}}
```

A [complete reference](./appendix_b_declarations.md) of all declarations appears in the appendix. Advanced declarations like `axiom`, `opaque`, `universe`, `notation`, and `set_option` are covered in later articles where they arise naturally.

## Function Composition

Lean provides three operators for combining functions:

| Operator  | Name    | Direction     | Meaning            |
| --------- | ------- | ------------- | ------------------ |
| `f ∘ g`   | compose | right-to-left | `fun x => f (g x)` |
| `x \|> f` | pipe    | left-to-right | `f x`              |
| `f <\| x` | apply   | right-to-left | `f x`              |

Composition builds new functions by chaining existing ones. The `∘` operator reads right-to-left: in `f ∘ g`, apply `g` first, then `f`. Pipelines with `|>` read left-to-right, which often matches how you think about data transformations: "take this, then do that, then do this."

```lean
{{#include ../../src/ZeroToQED/Basics.lean:composition}}
```

The `<|` operator is just function application with low precedence. It lets you write `f <| expensive computation` instead of `f (expensive computation)`. Some find this cleaner; others prefer explicit parentheses. Use whichever reads better.

Point-free style defines functions without naming their arguments: `square ∘ twice` rather than `fun x => square (twice x)`. This can be elegant for simple compositions but obscure for complex ones. The goal is clarity, not cleverness.

## Higher-Order Functions

**Higher-order functions** take functions as arguments. The classics: `map` transforms each element, `filter` keeps elements matching a predicate, `foldl` reduces a list to a single value by accumulating from the left.

And because Lean is also a theorem prover, we can prove properties by computation. The theorem `add_comm_example` states that `2 + 3 = 3 + 2`, and `rfl` proves it because both sides reduce to `5`. The examples at the end go further: reversing a list twice returns the original, list lengths add correctly, mapping a function produces the expected result.

What is the difference between `#eval [1,2,3].reverse.reverse = [1,2,3]` and `example : [1,2,3].reverse.reverse = [1,2,3] := rfl`? The `#eval` runs at runtime and prints `true`. The `example` is verified at compile time by the type checker, and if the equality did not hold, compilation would fail. Both check the same fact, but `example` catches the error before you ship. Note that this `rfl` proof verifies this specific list; proving it for all lists requires a `theorem` with induction. We cover proofs properly in [Proofs](./11_proving.md).

```lean
{{#include ../../src/ZeroToQED/Basics.lean:fp_essentials}}
```

## From Values to Structure

For a complete reference of all toplevel declarations (`def`, `theorem`, `inductive`, `structure`, etc.) and interactive commands (`#eval`, `#check`, `#print`), see [Appendix B](./appendix_b_declarations.md).

You now have the building blocks: numbers, functions, modules, and the fundamental declarations. Next we cover the data structures that make programs useful: lists, arrays, maps, and user-defined types. After that, we explore control flow, polymorphism, effects, and IO. By the end of Arc I, you will have built a D&D character generator, which is either a useful demonstration of structured programming or an excuse to start a D&D campaign. Possibly both.

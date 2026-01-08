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

**Files and Modules.** Each `.lean` file defines a **module**. The file `Foo/Bar/Baz.lean` defines module `Foo.Bar.Baz`. To use definitions from another module, import it at the top of your file with `import Mathlib.Data.Nat.Prime` or `import Mathlib` for an entire library. Imports are transitive: if `A` imports `B` and `B` imports `C`, then `A` has access to `C`'s definitions. The Lake build system (covered in [Build System](./04_build_system.md)) manages dependencies and ensures modules are compiled in the correct order.

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

A [complete reference](#toplevel-declarations-reference) of all declarations appears at the end of this chapter. Advanced declarations like `axiom`, `opaque`, `universe`, `notation`, and `set_option` are covered in later chapters where they arise naturally.

## Functional Programming Essentials

Lean is a functional language. Functions compose, pipelines chain, and higher-order functions do the heavy lifting.

**Composition** combines functions right-to-left: `(f ∘ g) x` means `f (g x)`. **Pipelines** chain left-to-right: `x |> f |> g` means `g (f x)`. Both express the same computation; choose whichever reads better.

**Higher-order functions** take functions as arguments. The classics: `map` transforms each element, `filter` keeps elements matching a predicate, `foldl` reduces a list to a single value by accumulating from the left. In `foldl (· + ·) 100 [1,2,3,4,5]`, the 100 is the initial accumulator; the function adds each element in turn, producing 115.

And because Lean is also a theorem prover, we can prove properties by computation. The theorem `add_comm_example` states that `2 + 3 = 3 + 2`, and `rfl` proves it because both sides reduce to `5`. The examples at the end go further: reversing a list twice returns the original, list lengths add correctly, mapping a function produces the expected result.

What is the difference between `#eval [1,2,3].reverse.reverse = [1,2,3]` and `example : [1,2,3].reverse.reverse = [1,2,3] := rfl`? The `#eval` runs at runtime and prints `true`. The `example` is verified at compile time by the type checker, and if the equality did not hold, compilation would fail. Both check the same fact, but `example` catches the error before you ship. Note that this `rfl` proof verifies this specific list; proving it for all lists requires a `theorem` with induction. We cover proofs properly in [Proofs](./11_proving.md).

```lean
{{#include ../../src/ZeroToQED/Basics.lean:fp_essentials}}
```

## Toplevel Declarations Reference

_You do not need to memorize all of this. This section is a reference for every toplevel declaration in Lean, with links to where each is explained in later chapters. Skim it now, come back when you need it._

Every Lean file is a sequence of toplevel declarations. These are the building blocks of every program and proof.

**Definitions and Proofs:**

| Declaration   | Purpose                                | Example                                             |
| ------------- | -------------------------------------- | --------------------------------------------------- |
| **`def`**     | Define a value or function             | [Zero](#zero)                                       |
| **`theorem`** | State and prove a proposition (opaque) | [Zero](#zero), [Proving](./11_proving.md)           |
| **`lemma`**   | Same as `theorem`                      | [Proving](./11_proving.md)                          |
| **`example`** | Anonymous proof (not saved)            | [Type Theory](./12_type_theory.md)                  |
| **`abbrev`**  | Transparent abbreviation               | [More Declarations](#more-declarations)             |
| **`opaque`**  | Hide implementation                    | [Proofs](./11_proving.md#axioms-and-escape-hatches) |
| **`axiom`**   | Unproven assumption                    | [Proofs](./11_proving.md#axioms-and-escape-hatches) |

**Type Declarations:**

| Declaration     | Purpose                        | Example                                                                      |
| --------------- | ------------------------------ | ---------------------------------------------------------------------------- |
| **`inductive`** | Define type with constructors  | [Data Structures](./06_data_structures.md#inductive-types)                   |
| **`structure`** | Single-constructor with fields | [Data Structures](./06_data_structures.md#structures)                        |
| **`class`**     | Type class interface           | [Polymorphism](./08_polymorphism.md#defining-type-classes)                   |
| **`instance`**  | Type class implementation      | [Polymorphism](./08_polymorphism.md#polymorphic-instances)                   |
| **`mutual`**    | Mutually recursive definitions | [Dependent Types](./13_dependent_types.md#mutual-and-nested-inductive-types) |

**Organization:**

| Declaration      | Purpose                  | Example                                                    |
| ---------------- | ------------------------ | ---------------------------------------------------------- |
| **`import`**     | Load another module      | [Modules and Namespaces](#modules-and-namespaces)          |
| **`variable`**   | Auto-add to definitions  | [Modules and Namespaces](#modules-and-namespaces)          |
| **`namespace`**  | Group under prefix       | [Modules and Namespaces](#modules-and-namespaces)          |
| **`section`**    | Scope for variables      | [Modules and Namespaces](#modules-and-namespaces)          |
| **`open`**       | Bring names into scope   | [Modules and Namespaces](#modules-and-namespaces)          |
| **`universe`**   | Declare universe levels  | [Type Theory](./12_type_theory.md#universe-stratification) |
| **`attribute`**  | Attach metadata          | [Polymorphism](./08_polymorphism.md#attributes)            |
| **`export`**     | Re-export from namespace | [Modules and Namespaces](#modules-and-namespaces)          |
| **`notation`**   | Custom syntax            | [Dependent Types](./13_dependent_types.md#custom-notation) |
| **`set_option`** | Configure compiler       | [Type Theory](./12_type_theory.md#compiler-options)        |

**Interactive Commands:**

| Command       | Purpose                | Example                                 |
| ------------- | ---------------------- | --------------------------------------- |
| **`#eval`**   | Evaluate and print     | [Zero](#zero)                           |
| **`#check`**  | Display type           | [More Declarations](#more-declarations) |
| **`#print`**  | Print declaration info | [More Declarations](#more-declarations) |
| **`#reduce`** | Reduce to normal form  | [More Declarations](#more-declarations) |

The distinction between **`def`** and **`theorem`** matters for performance. Lean marks **theorem** proofs as opaque, meaning they are never unfolded during type checking. This keeps proof terms from bloating computations. Use `def` for values you need to compute with and `theorem` for propositions you need to prove.

## From Values to Structure

You now have the building blocks: numbers, functions, modules, and the fundamental declarations. Next we cover the data structures that make programs useful: lists, arrays, maps, and user-defined types. After that, we explore control flow, polymorphism, effects, and IO. By the end of Arc I, you will have built a D&D character generator, which is either a useful demonstration of structured programming or an excuse to start a D&D campaign. Possibly both.

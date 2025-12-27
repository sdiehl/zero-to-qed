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

Now that we have numbers, let us also greet the world:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:hello_world}}
```

## Natural Numbers

Natural numbers in Lean represent non-negative integers, defined inductively just as Peano intended in 1889. They support standard arithmetic operations, but subtraction truncates at zero since negative results would fall outside the type. This has caused approximately as many bugs as unsigned integers in C, which is to say: more than anyone wants to admit.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:natural_numbers}}
```

## Integers

When you need negative numbers, use `Int`. Integer arithmetic behaves as you would expect from standard mathematics, unburdened by the horrors of two's complement overflow that have plagued systems programmers since the PDP-11.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:integers}}
```

## Modules and Namespaces

Lean organizes code into **modules** and **namespaces**. Understanding this system early will help you read and write Lean code.

**Files and Modules.** Each `.lean` file defines a **module**. The file `Foo/Bar/Baz.lean` defines module `Foo.Bar.Baz`. To use definitions from another module, import it at the top of your file with `import Mathlib.Data.Nat.Prime` or `import Mathlib` for an entire library. Imports are transitive: if `A` imports `B` and `B` imports `C`, then `A` has access to `C`'s definitions. The Lake build system (covered in [Build System](./04_build_system.md)) manages dependencies and ensures modules are compiled in the correct order.

**Namespaces.** **Namespaces** group related definitions under a common prefix. They prevent name collisions and organize large codebases:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:namespace_example}}
```

The **`open`** command brings namespace contents into scope, so you can write `dist` instead of `Geometry2.dist`:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:open_example}}
```

**Sections and Variables.** The **`section`** command creates a scope for temporary declarations. Variables declared with **`variable`** inside a section are automatically added as parameters to definitions that use them:

```lean
{{#include ../../src/ZeroToQED/Basics.lean:section_variable}}
```

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

## Pattern Matching

Pattern matching is a powerful feature for destructuring data and defining functions by cases.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:pattern_matching}}
```

## Toplevel Declarations

Every Lean file is a sequence of toplevel declarations. These are the building blocks of every program and proof. You have now encountered most of them; here is a complete reference with links to examples.

**Definitions and Proofs:**

| Declaration   | Purpose                                | Example                                   |
| ------------- | -------------------------------------- | ----------------------------------------- |
| **`def`**     | Define a value or function             | [Zero](#zero)                             |
| **`theorem`** | State and prove a proposition (opaque) | [Zero](#zero), [Proving](./11_proving.md) |
| **`lemma`**   | Same as `theorem`                      | [Proving](./11_proving.md)                |
| **`example`** | Anonymous proof (not saved)            | [Type Theory](./12_type_theory.md)        |
| **`abbrev`**  | Transparent abbreviation               | [Abbrev example](#abbrev-example)         |
| **`opaque`**  | Hide implementation                    | [Opaque example](#opaque-example)         |
| **`axiom`**   | Unproven assumption                    | [Axiom example](#axiom-example)           |

**Type Declarations:**

| Declaration     | Purpose                        | Example                                                                      |
| --------------- | ------------------------------ | ---------------------------------------------------------------------------- |
| **`inductive`** | Define type with constructors  | [Data Structures](./06_data_structures.md#inductive-types)                   |
| **`structure`** | Single-constructor with fields | [Data Structures](./06_data_structures.md#structures)                        |
| **`class`**     | Type class interface           | [Polymorphism](./08_polymorphism.md#defining-type-classes)                   |
| **`instance`**  | Type class implementation      | [Polymorphism](./08_polymorphism.md#polymorphic-instances)                   |
| **`mutual`**    | Mutually recursive definitions | [Dependent Types](./13_dependent_types.md#mutual-and-nested-inductive-types) |

**Organization:**

| Declaration      | Purpose                  | Example                                           |
| ---------------- | ------------------------ | ------------------------------------------------- |
| **`import`**     | Load another module      | [Modules and Namespaces](#modules-and-namespaces) |
| **`variable`**   | Auto-add to definitions  | [Modules and Namespaces](#modules-and-namespaces) |
| **`namespace`**  | Group under prefix       | [Modules and Namespaces](#modules-and-namespaces) |
| **`section`**    | Scope for variables      | [Modules and Namespaces](#modules-and-namespaces) |
| **`open`**       | Bring names into scope   | [Modules and Namespaces](#modules-and-namespaces) |
| **`universe`**   | Declare universe levels  | [Universe example](#universe-example)             |
| **`attribute`**  | Attach metadata          | [Attribute example](#attribute-example)           |
| **`export`**     | Re-export from namespace | [Modules and Namespaces](#modules-and-namespaces) |
| **`notation`**   | Custom syntax            | [Notation example](#notation-example)             |
| **`set_option`** | Configure compiler       | [Set Option example](#set-option-example)         |

**Interactive Commands:**

| Command       | Purpose                | Example                               |
| ------------- | ---------------------- | ------------------------------------- |
| **`#eval`**   | Evaluate and print     | [Zero](#zero)                         |
| **`#check`**  | Display type           | [Commands example](#commands-example) |
| **`#print`**  | Print declaration info | [Commands example](#commands-example) |
| **`#reduce`** | Reduce to normal form  | [Commands example](#commands-example) |

The distinction between **`def`** and **`theorem`** matters for performance. Lean marks **theorem** proofs as opaque, meaning they are never unfolded during type checking. This keeps proof terms from bloating computations. Use `def` for values you need to compute with and `theorem` for propositions you need to prove.

### Abbrev Example

Abbreviations are transparent definitions that unfold automatically during elaboration. Use them for type aliases.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:abbrev_example}}
```

### Opaque Example

Opaque definitions hide their implementation from the type checker. Useful for abstracting implementation details.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:opaque_example}}
```

### Axiom Example

The **`axiom`** declaration asserts something without proof. It is the escape hatch from the proof system: you declare that something is true and Lean believes you. This is extremely dangerous. If you assert something false, you can then prove anything at all, including `False` itself. The system becomes unsound.

> [!WARNING]
> **Axioms** should be used only in narrow circumstances: foundational assumptions like the law of excluded middle or the axiom of choice (which Mathlib already provides), FFI bindings where proofs are impossible because the implementation is external, or as temporary placeholders during development (though `sorry` is preferred since it generates a warning). Before adding a custom axiom, ask whether you actually need it. Usually the answer is no.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:axiom_example}}
```

Lean's **kernel** accepts axioms unconditionally. The `#print axioms` command shows which axioms a theorem depends on, which is useful for verifying that your proofs rely only on the standard foundational axioms you expect.

### Attribute Example

Attributes tag declarations with metadata that affects how Lean processes them. The `@[simp]` attribute is the most common; see [Tactics](./15_tactics.md) for how `simp` uses it.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:attribute_example}}
```

### Commands Example

```lean
{{#include ../../src/ZeroToQED/Basics.lean:check_print_reduce}}
```

### Universe Example

**Universes** prevent paradoxes in type theory. Here is the basic syntax; see [Universe Stratification](./12_type_theory.md#universe-stratification) for why they exist.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:universe_example}}
```

### Notation Example

Custom notation lets you extend Lean's syntax. Here is the basic syntax; see [Dependent Types: Notation](./13_dependent_types.md#notation) for more.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:notation_example}}
```

### Set Option Example

Compiler options control elaboration and pretty-printing. You will rarely need these until you hit edge cases.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:set_option_example}}
```

## Mathematical Curiosities

Numbers hold surprises. Here are a few classics you can verify computationally.

The **taxicab number** 1729 is the smallest number expressible as the sum of two cubes in two different ways. When Hardy visited Ramanujan in hospital and mentioned arriving in taxi 1729, calling it "rather a dull number," Ramanujan immediately replied that it was actually quite interesting. He was right: \\(1^3 + 12^3 = 9^3 + 10^3 = 1729\\).

**Perfect numbers** equal the sum of their proper divisors. The ancients knew 6, 28, 496, and 8128. Euclid proved that \\(2^{p-1}(2^p - 1)\\) is perfect when \\(2^p - 1\\) is prime. Whether odd perfect numbers exist remains open after two millennia.

The **Fibonacci sequence** appears everywhere: bad interview questions, crackpot science, and occasionally number theory. Each term is the sum of the two preceding ones. To understand recursion, see Fibonacci. To understand Fibonacci, see recursion.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:mathematical_curio}}
```

## From Values to Structure

You now have the building blocks: numbers, functions, modules, and the fundamental declarations. Next we cover the data structures that make programs useful: lists, arrays, maps, and user-defined types. After that, we explore control flow, polymorphism, effects, and IO. By the end of Arc I, you will have built a D&D character generator, which is either a useful demonstration of structured programming or an excuse to start a D&D campaign. Possibly both.

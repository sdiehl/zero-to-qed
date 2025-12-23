# Basics

True to the title of this article series, we start from zero. Not "Hello, World!" but an actual zero: the natural number that forms the foundation of arithmetic.

## Zero

```lean
{{#include ../../src/ZeroToQED/Basics.lean:from_zero}}
```

This first example introduces three toplevel declarations that you will use constantly:

- **`def`** defines a named value or function. Here `def zero : Nat := 0` declares that `zero` has type `Nat` (natural number) and equals `0`. Every Lean program is built from `def` declarations.

- **`#eval`** evaluates an expression and prints the result. This command runs code immediately, useful for testing as you work. Commands starting with `#` are interactive queries that do not create permanent definitions.

- **`theorem`** declares a proposition to be proved. The name `deep_thought` labels the statement `fortyTwo = 6 * 7`, and `rfl` (reflexivity) proves it by computation: both sides reduce to `42`. Unlike `def`, theorem proofs are opaque and never unfold during type checking.

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

Lean organizes code into modules and namespaces. Understanding this system early will help you read and write Lean code.

**Files and Modules.** Each `.lean` file defines a module. The file `Foo/Bar/Baz.lean` defines module `Foo.Bar.Baz`. To use definitions from another module, import it at the top of your file with `import Mathlib.Data.Nat.Prime` or `import Mathlib` for an entire library. Imports are transitive: if `A` imports `B` and `B` imports `C`, then `A` has access to `C`'s definitions. The Lake build system (covered in the [Build System](./04_build_system.md) chapter) manages dependencies and ensures modules are compiled in the correct order.

**Namespaces.** Namespaces group related definitions under a common prefix. They prevent name collisions and organize large codebases:

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

## Fin

`Fin n` represents natural numbers strictly less than `n`. The type carries a proof that its value is in bounds, making it useful for safe array indexing.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:fin}}
```

> [!TIP]
> Notice that `Fin n` bundles a value with a proof about that value. This pattern appears everywhere in Lean. Types can contain proofs. Later you will see this is not a special feature but a consequence of something deeper: the Curry-Howard correspondence, where propositions are types and proofs are values.

## Fixed-Precision Integers

For performance-critical code or when interfacing with external systems, Lean provides fixed-precision integers that map directly to machine types.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:fixed_precision}}
```

## Bitvectors

Bitvectors represent fixed-width binary data and support bitwise operations. They are essential for low-level programming, cryptography, and hardware verification.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:bitvectors}}
```

## Floats

Lean supports IEEE 754 double-precision floating-point numbers for scientific computing and applications that require real number approximations.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:floats}}
```

## Chars

Characters in Lean are Unicode scalar values, capable of representing any character from any human language, mathematical symbols, and 🐻.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:chars}}
```

## Strings

Strings are sequences of characters with a rich set of operations for text processing. They are UTF-8 encoded, which means you have already won half the battle that consumed the first decade of web development.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:strings}}
```

## Unit

The `Unit` type has exactly one value: `()`. It serves as a placeholder when a function has no meaningful return value, similar to `void` in C except that `void` is a lie and `Unit` is honest about being boring. Colloquially: every function can return `Unit` because there is only one possible value to return. Category theorists call this the terminal object (for any type $A$, there exists exactly one function $A \to \text{Unit}$), but you do not need category theory to use it.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:unit}}
```

## Empty

The `Empty` type has no values at all. Colloquially: you can write a function from `Empty` to anything because you will never have to actually produce an output, there are no inputs to handle. Category theorists call this the initial object (for any type $A$, there exists exactly one function $\text{Empty} \to A$), but again, the jargon is optional. `Empty` represents logical impossibility and marks unreachable code branches. If you somehow obtain a value of type `Empty`, you can derive anything from it, a principle the medievals called _ex falso quodlibet_: from falsehood, anything follows.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:empty}}
```

> [!NOTE]
> You do not need to fully understand `Unit`, `Empty`, or `Fin` to write Lean programs. Use them when they fit; ignore the theory until you need it. The [Proofs](./10_proving.md) and [Type Theory](./11_type_theory.md) articles explain the deeper connections, including the Curry-Howard correspondence that links these types to logic.

## Booleans

Booleans represent truth values and form the basis of conditional logic. George Boole would be pleased, though he might find it curious that his algebra of logic became the foundation for arguments about whether `0` or `1` should represent truth.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:booleans}}
```

## Option

The `Option` type represents values that may or may not exist. It is Lean's safe alternative to null references, which Tony Hoare famously called his "billion dollar mistake." With `Option`, absence is explicit in the type: you cannot forget to check because the compiler will not let you. The hollow log either contains honey or it does not, and you must handle both cases.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:option}}
```

## Tuples

Tuples combine values of potentially different types into a single value. They are the basic building block for returning multiple values from functions.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:tuples}}
```

## Sum Types

Sum types represent a choice between two alternatives. The `Except` variant is commonly used for error handling.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:sum_types}}
```

## Lists

Lists are singly-linked sequences of elements, the workhorse data structure of functional programming since LISP introduced them in 1958. They support pattern matching and have a rich set of higher-order operations. Prepending is $O(1)$; appending is $O(n)$. If this bothers you, wait until you meet Arrays.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:lists}}
```

## Arrays

Arrays provide $O(1)$ random access and are the preferred choice when you need indexed access without the pointer-chasing of linked lists. Thanks to Lean's reference counting, operations on unshared arrays mutate in place, giving you the performance of imperative code with the semantics of pure functions. Purity without the performance penalty. The trick is that "unshared" does a lot of work in that sentence.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:arrays}}
```

## ByteArrays

ByteArrays are efficient arrays of bytes, useful for binary data, file I/O, and network protocols.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:bytearrays}}
```

## Maps and Sets

Hash maps and hash sets provide efficient key-value storage and membership testing.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:maps_sets}}
```

## Subtypes

Subtypes refine an existing type with a predicate. The value carries both the data and a proof that the predicate holds. This is where dependent types begin to flex: instead of checking at runtime whether a number is positive, you encode positivity in the type itself. The predicate becomes part of the contract, enforced at compile time.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:subtypes}}
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

## Structures

Structures are Lean's way of grouping related data with named fields.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:structures}}
```

## Inductive Types

Inductive types allow you to define custom data types by specifying their constructors.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:inductive_types}}
```

## Type Classes

Type classes provide a way to define generic interfaces that can be implemented for different types.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:type_classes}}
```

## Toplevel Declarations

Every Lean file is a sequence of toplevel declarations. These are the building blocks of every program and proof. You have now encountered most of them; here is a complete reference with links to examples.

**Definitions and Proofs:**

| Declaration   | Purpose                                | Example                                   |
| ------------- | -------------------------------------- | ----------------------------------------- |
| **`def`**     | Define a value or function             | [Zero](#zero)                             |
| **`theorem`** | State and prove a proposition (opaque) | [Zero](#zero), [Proving](./10_proving.md) |
| **`lemma`**   | Same as `theorem`                      | [Proving](./10_proving.md)                |
| **`example`** | Anonymous proof (not saved)            | [Type Theory](./11_type_theory.md)        |
| **`abbrev`**  | Transparent abbreviation               | [Abbrev example](#abbrev-example)         |
| **`opaque`**  | Hide implementation                    | [Opaque example](#opaque-example)         |
| **`axiom`**   | Unproven assumption                    | [Axiom example](#axiom-example)           |

**Type Declarations:**

| Declaration     | Purpose                        | Example                                                                      |
| --------------- | ------------------------------ | ---------------------------------------------------------------------------- |
| **`inductive`** | Define type with constructors  | [Inductive Types](#inductive-types)                                          |
| **`structure`** | Single-constructor with fields | [Structures](#structures)                                                    |
| **`class`**     | Type class interface           | [Polymorphism](./07_polymorphism.md#defining-type-classes)                   |
| **`instance`**  | Type class implementation      | [Polymorphism](./07_polymorphism.md#polymorphic-instances)                   |
| **`mutual`**    | Mutually recursive definitions | [Dependent Types](./12_dependent_types.md#mutual-and-nested-inductive-types) |

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

The distinction between **`def`** and **`theorem`** matters for performance. Lean marks theorem proofs as opaque, meaning they are never unfolded during type checking. This keeps proof terms from bloating computations. Use `def` for values you need to compute with and `theorem` for propositions you need to prove.

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
> Axioms should be used only in narrow circumstances: foundational assumptions like the law of excluded middle or the axiom of choice (which Mathlib already provides), FFI bindings where proofs are impossible because the implementation is external, or as temporary placeholders during development (though `sorry` is preferred since it generates a warning). Before adding a custom axiom, ask whether you actually need it. Usually the answer is no.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:axiom_example}}
```

Lean's kernel accepts axioms unconditionally. The `#print axioms` command shows which axioms a theorem depends on, which is useful for verifying that your proofs rely only on the standard foundational axioms you expect.

### Attribute Example

Attributes tag declarations with metadata that affects how Lean processes them. The `@[simp]` attribute is the most common; see [Tactics](./14_tactics.md) for how `simp` uses it.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:attribute_example}}
```

### Commands Example

```lean
{{#include ../../src/ZeroToQED/Basics.lean:check_print_reduce}}
```

### Universe Example

Universes prevent paradoxes in type theory. Here is the basic syntax; see [Universe Stratification](./11_type_theory.md#universe-stratification) for why they exist.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:universe_example}}
```

### Notation Example

Custom notation lets you extend Lean's syntax. Here is the basic syntax; see [Dependent Types: Notation](./12_dependent_types.md#notation) for more.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:notation_example}}
```

### Set Option Example

Compiler options control elaboration and pretty-printing. You will rarely need these until you hit edge cases.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:set_option_example}}
```

## Example Programs

Now let's put everything together to build some non-trivial trivial programs! The following examples demonstrate Lean as a general-purpose programming language, showing how its type system and functional style work together in practice.

### FizzBuzz

FizzBuzz is the canonical "can you actually program" interview question, famous for its ability to filter candidates who cannot write a loop. Here it demonstrates pattern matching on multiple conditions: "Fizz" for multiples of 3, "Buzz" for multiples of 5, "FizzBuzz" for both, and the number itself otherwise. The Lean version is more elegant than the nested conditionals you have seen in lesser languages.

```lean
{{#include ../../src/Examples/FizzBuzz.lean}}
```

Build and run with:

```bash
lake exe fizzbuzz 20
```

### Word Frequency

This example uses a hash map to count word occurrences in a string. The `foldl` function threads an accumulator through the word list, updating counts as it goes.

```lean
{{#include ../../src/Examples/WordFreq.lean}}
```

Build and run with:

```bash
lake exe wordfreq "the spice must flow the spice extends life"
```

### Collatz Conjecture

The Collatz conjecture states that repeatedly applying a simple rule (halve if even, triple and add one if odd) will eventually reach 1 for any positive starting integer. Proposed in 1937, it remains unproven. Mathematicians have verified it for numbers up to $2^{68}$, yet no one can prove it always works. Erdos famously said of Collatz that "Mathematics is not yet ready for such problems."

But we can still explore it computationally in Lean!

```lean
{{#include ../../src/ZeroToQED/Basics.lean:collatz}}
```

The full Collatz explorer is available as a standalone executable. Build and run it with:

```bash
lake exe collatz 27
```

## From Values to Structure

You now have the building blocks: types, functions, data structures, and basic I/O. Next we explore control flow, pattern matching, and user-defined types. By the end you will have built a D&D character generator, which is either a useful demonstration of structured programming or an excuse to start a D&D campaign. Possibly both.

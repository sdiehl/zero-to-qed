# Data Structures

Programs are nothing without data to manipulate. Here we cover the types that hold your data: from simple primitives like characters and booleans to collections like lists and arrays to user-defined structures and inductive types. By the end, you will have the vocabulary to represent any data your program needs.

## Fin

[`Fin n`](./13_dependent_types.md) represents natural numbers strictly less than `n`. The type carries a proof that its value is in bounds, making it useful for safe array indexing.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:fin}}
```

> [!TIP]
> Notice that `Fin n` bundles a value with a proof about that value. This pattern appears everywhere in Lean. Types can contain proofs. Later you will see this is not a special feature but a consequence of something deeper: the [Curry-Howard correspondence](./12_type_theory.md), where propositions are types and proofs are values.

## Fixed-Precision Integers

For performance-critical code or when interfacing with external systems, Lean provides fixed-precision integers that map directly to machine types.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:fixed_precision}}
```

## Bitvectors

Bitvectors represent fixed-width binary data and support bitwise operations. They are essential for low-level programming, cryptography, and hardware verification.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:bitvectors}}
```

## Floats

Lean supports IEEE 754 double-precision floating-point numbers for scientific computing and applications that require real number approximations.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:floats}}
```

## Chars

Characters in Lean are Unicode scalar values, capable of representing any character from any human language, mathematical symbols, and bears.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:chars}}
```

## Strings

Strings are sequences of characters with a rich set of operations for text processing. They are UTF-8 encoded, which means you have already won half the battle that consumed the first decade of web development.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:strings}}
```

## Unit

The `Unit` type has exactly one value: `()`. It serves as a placeholder when a function has no meaningful return value, similar to `void` in C except that `void` is a lie and `Unit` is honest about being boring. Colloquially: every function can return `Unit` because there is only one possible value to return. Category theorists call this the terminal object (for any type \\(A\\), there exists exactly one function \\(A \to \text{Unit}\\)), but you do not need category theory to use it.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:unit}}
```

## Empty

The `Empty` type has no values at all. Colloquially: you can write a function from `Empty` to anything because you will never have to actually produce an output, there are no inputs to handle. Category theorists call this the initial object (for any type \\(A\\), there exists exactly one function \\(\text{Empty} \to A\\)), but again, the jargon is optional. `Empty` represents logical impossibility and marks unreachable code branches. If you somehow obtain a value of type `Empty`, you can derive anything from it, a principle the medievals called _ex falso quodlibet_: from falsehood, anything follows.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:empty}}
```

> [!NOTE]
> You do not need to fully understand `Unit`, `Empty`, or `Fin` to write Lean programs. Use them when they fit; ignore the theory until you need it. The [Proofs](./11_proving.md) and [Type Theory](./12_type_theory.md) articles explain the deeper connections, including the Curry-Howard correspondence that links these types to logic.

## Booleans

Booleans represent truth values and form the basis of conditional logic. George Boole would be pleased, though he might find it curious that his algebra of logic became the foundation for arguments about whether `0` or `1` should represent truth.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:booleans}}
```

## Option

The `Option` type represents values that may or may not exist. It is Lean's safe alternative to null references, which Tony Hoare famously called his "billion dollar mistake." With `Option`, absence is explicit in the type: you cannot forget to check because the compiler will not let you. The hollow log either contains honey or it does not, and you must handle both cases.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:option}}
```

## Tuples

Tuples combine values of potentially different types into a single value. They are the basic building block for returning multiple values from functions.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:tuples}}
```

## Sum Types

Sum types represent a choice between two alternatives. The `Except` variant is commonly used for error handling.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:sum_types}}
```

## Lists

Lists are singly-linked sequences of elements, the workhorse data structure of functional programming since LISP introduced them in 1958. They support pattern matching and have a rich set of higher-order operations. Prepending is \\(O(1)\\); appending is \\(O(n)\\). If this bothers you, wait until you meet Arrays.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:lists}}
```

## Arrays

Arrays provide \\(O(1)\\) random access and are the preferred choice when you need indexed access without the pointer-chasing of linked lists. Thanks to Lean's reference counting, operations on unshared arrays mutate in place, giving you the performance of imperative code with the semantics of pure functions. Purity without the performance penalty. The trick is that "unshared" does a lot of work in that sentence.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:arrays}}
```

## ByteArrays

ByteArrays are efficient arrays of bytes, useful for binary data, file I/O, and network protocols.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:bytearrays}}
```

## Maps and Sets

Hash maps and hash sets provide efficient key-value storage and membership testing.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:maps_sets}}
```

## Subtypes

Subtypes refine an existing type with a predicate. The value carries both the data and a proof that the predicate holds. This is where [dependent types](./13_dependent_types.md) begin to flex: instead of checking at runtime whether a number is positive, you encode positivity in the type itself. The predicate becomes part of the contract, enforced at compile time.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:subtypes}}
```

## Structures

**Structures** are Lean's way of grouping related data with named fields.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:structures}}
```

## Inductive Types

**Inductive types** allow you to define custom data types by specifying their constructors. An inductive type with no arguments on its constructors represents a finite set of values, like an enumeration. The `SpellSchool` type below can take exactly eight values (abjuration, conjuration, etc.), and the `schoolDanger` function assigns a danger rating to each via pattern matching.

When constructors take arguments, the type becomes recursive and can represent unbounded data. `MyList α` is parameterized by a type `α` and has two constructors: `nil` for the empty list and `cons` for prepending an element. The `length` function recurses through the structure, counting elements.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:inductive_types}}
```

## Type Classes

**Type classes** provide a way to define generic interfaces that can be implemented for different types.

```lean
{{#include ../../src/ZeroToQED/DataStructures.lean:type_classes}}
```

## Example: Magic The Gathering

We now have enough Lean to model something from the real world. Naturally, we choose [Magic: The Gathering](https://en.wikipedia.org/wiki/Magic:_The_Gathering). The game has been proven [Turing complete](https://arxiv.org/pdf/1904.09828) and [as hard as the halting problem](https://arxiv.org/abs/2003.05119), so it makes a worthy adversary.

### Mana System

Five colors of mana (white, blue, black, red, green) plus colorless. An `inductive` type captures the colors; a `structure` captures costs with default values of zero:

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:mana_colors}}
```

Players accumulate mana in a pool. The key question: can you afford a spell? The `pay` function returns `Option ManaPool`, giving back the remaining mana on success or `none` if you cannot afford the cost:

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:mana_pool}}
```

### Card Types

Cards come in different types. Creatures have power and toughness; instants, sorceries, and artifacts do not. An `inductive` type with arguments captures this: the `creature` constructor carries two `Nat` values, while others carry nothing:

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:card_types}}
```

Some iconic cards to work with. Note how `.creature 2 2` constructs a creature type inline, using the dot notation shorthand:

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:sample_cards}}
```

Pattern matching extracts information from cards. Querying a non-creature for its power returns `none`:

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:card_queries}}
```

### Combat

Creatures on the battlefield can attack and block. A `Creature` structure tracks accumulated damage. When damage meets or exceeds toughness, the creature dies:

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:combat}}
```

Combat is simultaneous: both creatures deal damage at once. Two 2/2 creatures blocking each other results in mutual destruction.

### Hand Management

A hand is a list of cards. List operations let us query it: which cards can we cast with our current mana? How many creatures do we have? What is the total mana cost?

```lean
{{#include ../../src/Examples/MagicTheGathering.lean:hand}}
```

The `filter` function takes a predicate and keeps matching elements. The `foldl` function reduces a list to a single value. These are the workhorses of functional programming, and they compose naturally: `hand.filter Card.isCreature` gives all creatures, `hand.playable pool` gives everything castable.

> [!TIP]
> Run from the repository: `lake exe mtg`. The full source is on [GitHub](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/MagicTheGathering.lean).

## From Data to Control

You now have the building blocks for representing any data your program needs. Next we cover how to work with that data: control flow, recursion, and the patterns that give programs their structure.

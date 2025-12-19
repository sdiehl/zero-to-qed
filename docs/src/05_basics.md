# Basics

True to the title of this article series, we start from zero. Not "Hello, World!" but an actual zero: the natural number that forms the foundation of arithmetic.

## Zero

```lean
{{#include ../../src/ZeroToQED/Basics.lean:from_zero}}
```

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

The `Unit` type has exactly one value: `()`. It serves as a placeholder when a function has no meaningful return value, similar to `void` in C except that `void` is a lie and `Unit` is honest about being boring. Colloquially: every function can return `Unit` because there is only one possible value to return. Category theorists call this the terminal object (for any type \\(A\\), there exists exactly one function \\(A \to \text{Unit}\\)), but you do not need category theory to use it.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:unit}}
```

## Empty

The `Empty` type has no values at all. Colloquially: you can write a function from `Empty` to anything because you will never have to actually produce an output, there are no inputs to handle. Category theorists call this the initial object (for any type \\(A\\), there exists exactly one function \\(\text{Empty} \to A\\)), but again, the jargon is optional. `Empty` represents logical impossibility and marks unreachable code branches. If you somehow obtain a value of type `Empty`, you can derive anything from it, a principle the medievals called _ex falso quodlibet_: from falsehood, anything follows.

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

Lists are singly-linked sequences of elements, the workhorse data structure of functional programming since LISP introduced them in 1958. They support pattern matching and have a rich set of higher-order operations. Prepending is \\(O(1)\\); appending is \\(O(n)\\). If this bothers you, wait until you meet Arrays.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:lists}}
```

## Arrays

Arrays provide \\(O(1)\\) random access and are the preferred choice when you need indexed access without the pointer-chasing of linked lists. Thanks to Lean's reference counting, operations on unshared arrays mutate in place, giving you the performance of imperative code with the semantics of pure functions. Purity without the performance penalty. The trick is that "unshared" does a lot of work in that sentence.

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

The Collatz conjecture states that repeatedly applying a simple rule (halve if even, triple and add one if odd) will eventually reach 1 for any positive starting integer. Proposed in 1937, it remains unproven. Mathematicians have verified it for numbers up to \\(2^{68}\\), yet no one can prove it always works. Erdos famously said of Collatz that "Mathematics is not yet ready for such problems."

But we can still explore it computationally in Lean!

```lean
{{#include ../../src/ZeroToQED/Basics.lean:collatz}}
```

The full Collatz explorer is available as a standalone executable. Build and run it with:

```bash
lake exe collatz 27
```

## From Values to Structure

You now have the building blocks: types, functions, data structures, and basic I/O. Next we explore control flow, pattern matching, and user-defined types. By the end you will have built a D&D character generator, which is either a useful demonstration of structured programming or an excuse to roll dice. Possibly both.

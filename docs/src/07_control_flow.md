# Control Flow and Structures

Most languages let you lie to the compiler. Lean does not. There are no statements, only **expressions**. Every `if` produces a value. Every `match` is exhaustive or the compiler complains. Every recursive function must **terminate** or you must convince the system otherwise. Where imperative languages let you wave your hands, Lean demands you show your work.

## Conditionals

Lean's if-then-else is an expression, not a statement. Every branch must produce a value of the same type, and the entire expression evaluates to that value. There is no `void`, no implicit fall-through, no forgetting to return. The ternary operator that other languages treat as a curiosity is simply how conditionals work here.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:conditionals}}
```

## Pattern Matching

**Pattern matching** with `match` expressions lets you destructure data and handle cases exhaustively. The compiler verifies you have covered every possibility, which eliminates an entire category of bugs that haunt languages where the default case is "do nothing and hope for the best." You can match on constructors, literals, and multiple values simultaneously.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:pattern_matching}}
```

## Simple Recursion

**Recursive functions** are fundamental to functional programming. A function processing a list works through elements one by one, patient and systematic, eventually reaching the empty case and returning upstream with its catch. In Lean, functions that call themselves must be shown to terminate. For simple **structural recursion** on inductive types like `Nat` or `List`, Lean can automatically verify termination.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:simple_recursion}}
```

## Tail Recursion

Naive recursion can overflow the stack for large inputs because each recursive call adds a frame. **Tail recursion** solves this by restructuring the computation so the recursive call is the last operation, allowing the compiler to optimize it into a loop. Scheme mandated tail call optimization in 1975. Most other languages did not, which is why stack traces exist.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:tail_recursion}}
```

## Structural Recursion

Lean requires all recursive functions to terminate, which prevents you from accidentally writing infinite loops and passing them off as proofs. For simple cases where the recursive argument structurally decreases, Lean verifies termination automatically. For more complex cases, you must provide termination hints, essentially explaining to the compiler why your clever recursion scheme actually finishes. The termination checker is not easily fooled.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:structural_recursion}}
```

## Structures

**Structures** group related data with named fields. If you have used records in ML, structs in Rust, or data classes in Kotlin, the concept is familiar. Unlike C structs, Lean structures come with automatically generated accessor functions, projection notation, and none of the memory layout anxiety.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:structures_basic}}
```

## Updating Structures

Rather than modifying structures in place, Lean provides the `with` syntax for creating new structures based on existing ones with some fields changed. This functional update pattern means you never have to wonder whether some other part of the code is holding a reference to your data and will be surprised by your mutations.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:structures_update}}
```

## Nested Structures

Structures can contain other structures, allowing you to build complex data hierarchies. Lean's projection notation makes accessing nested fields readable: `person.address.city` works as you would hope, without the verbose getter chains of enterprise Java.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:structures_nested}}
```

## Default Values

Structures can have default values for their fields, making it easy to create instances with sensible defaults while overriding only specific fields.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:structures_defaults}}
```

## Inductive Types: Enumerations

**Inductive types** let you define custom data types by specifying their constructors. This is the core mechanism that makes Lean's type system expressive: natural numbers, lists, trees, and abstract syntax all emerge from the same primitive. Simple enumerations have constructors with no arguments; more complex types carry data in each variant. Like Starfleet's ship classification system, each variant is distinct and the compiler ensures you handle them all.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:inductive_enum}}
```

## Recursive Inductive Types

Inductive types can be recursive, allowing you to define trees, linked lists, and other self-referential structures. This is where inductive types earn their name: you define larger values in terms of smaller ones, and the recursion has a base case that grounds the whole edifice.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:inductive_recursive}}
```

Reading constructor type signatures takes practice. The `node` constructor has type `α → BinaryTree α → BinaryTree α → BinaryTree α`. In any arrow chain `A → B → C → D`, the last type is the return type; everything before is an input. So `node` takes a value of type `α`, a left subtree, a right subtree, and produces a tree. The `leaf` constructor takes no arguments and represents an empty position where the tree ends.

## Parameterized Types

Inductive types can be parameterized, making them generic over the types they contain. This is how you write a `List α` that works for any element type, or an expression tree parameterized by its literal type. One definition, infinitely many instantiations.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:inductive_parameterized}}
```

## Mutual Recursion

Sometimes you need multiple definitions that refer to each other, like `even` and `odd` functions that call each other, or a parser and its sub-parsers. Lean supports **mutually recursive** definitions within a `mutual` block. The termination checker handles these jointly, so your circular definitions must still demonstrably finish.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:mutual_recursion}}
```

## FizzBuzz

FizzBuzz is the canonical "can you actually program" interview question, famous for filtering candidates who cannot write a loop. Pattern matching on multiple conditions makes it elegant: match on whether divisible by 3, whether divisible by 5, and the four cases fall out naturally.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:fizzbuzz}}
```

> [!TIP]
> Run from the repository: `lake exe fizzbuzz 20`

## The Collatz Conjecture

The Collatz conjecture states that repeatedly applying a simple rule (halve if even, triple and add one if odd) eventually reaches 1 for any positive starting integer. Proposed in 1937, it remains unproven. Mathematicians have verified it for numbers up to \\(2^{68}\\), yet no one can prove it always works. Erdos said "Mathematics is not yet ready for such problems."

The recursion here needs fuel (a maximum step count) because we cannot prove termination. If we could, we would have solved a famous open problem.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:collatz}}
```

> [!TIP]
> Run from the repository: `lake exe collatz 27`

## Role Playing Game Example

The constructs above combine naturally in larger programs. What better way to demonstrate this than a D&D character generator? Structures hold character data, inductive types represent races and classes, pattern matching computes racial bonuses, and recursion drives the dice-rolling simulation.

We start by defining the data types that model our domain. The `AbilityScores` structure bundles the six core abilities. Inductive types enumerate races, classes, and backgrounds. The `Character` structure ties everything together:

```lean
{{#include ../../src/Examples/DndCharacter.lean:data_types}}
```

Racial bonuses modify ability scores based on the character's race. Pattern matching maps each race to its specific bonuses. Humans get +1 to everything; elves favor dexterity and intelligence; dwarves are sturdy:

```lean
{{#include ../../src/Examples/DndCharacter.lean:racial_bonuses}}
```

Each character class has a different hit die, representing how much health they gain per level. Wizards are fragile with a d6, while barbarians are tanks with a d12:

```lean
{{#include ../../src/Examples/DndCharacter.lean:game_mechanics}}
```

Random character generation needs randomness. A linear congruential generator provides deterministic pseudo-random numbers, which means the same seed produces the same character:

```lean
{{#include ../../src/Examples/DndCharacter.lean:rng}}
```

D&D ability scores use 4d6-drop-lowest: roll four six-sided dice and discard the lowest. This generates scores between 3 and 18, heavily weighted toward the middle. We thread the RNG state through each dice roll to maintain determinism:

```lean
{{#include ../../src/Examples/DndCharacter.lean:dice_rolling}}
```

Character generation threads the RNG through multiple operations: pick a name, race, class, and background, roll ability scores, apply racial bonuses, and calculate starting hit points:

```lean
{{#include ../../src/Examples/DndCharacter.lean:character_generation}}
```

Display functions convert internal representations to human-readable strings. The modifier calculation implements D&D's (score / 2 - 5) formula:

```lean
{{#include ../../src/Examples/DndCharacter.lean:display_formatting}}
```

The main function reads a seed from command-line arguments (defaulting to 42), generates a character, and prints it in a formatted sheet:

```lean
{{#include ../../src/Examples/DndCharacter.lean:main_program}}
```

Build and run the character generator with:

```bash
lake exe dnd 42
```

Try different seeds to generate different characters. The generator uses a deterministic pseudo-random number generator, so the same seed always produces the same character.

## Toward Abstraction

With structures and inductive types, you can model complex domains. But real programs need abstraction over types themselves. Polymorphism and type classes let you write code that works for any type satisfying certain constraints. This is how you build generic libraries without sacrificing type safety.

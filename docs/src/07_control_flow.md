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

The `merge` function is structurally recursive: each call operates on a smaller list. The `mergeSort` function is trickier. It splits the list at the midpoint and recurses on both halves. Lean cannot immediately see that `take` and `drop` produce shorter lists, so we provide `have` clauses that prove the lengths decrease. The `termination_by xs.length` annotation tells Lean to measure termination by list length rather than structural decrease. The [next chapter](./08_termination.md) covers `termination_by`, `decreasing_by`, and `WellFounded.fix` in depth, which is what you reach for when neither structural recursion nor a simple length measure works.

## Escape Hatches: partial and do

Sometimes you just want to compute something. The termination checker is a feature, not a prison. When proving termination would require more ceremony than the problem warrants, Lean provides escape hatches.

The `partial` keyword marks a function that might not terminate. Lean skips the termination proof and trusts you. The tradeoff: partial functions cannot be used in proofs since a non-terminating function could "prove" anything. For computation, this is often acceptable.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:partial_functions}}
```

The second example uses `Id.run do` to write imperative-looking code in a pure context. The `Id` monad is the identity monad, and `Id.run` extracts the final value. The `mut` keyword introduces mutable bindings; `:=` reassigns them. Lean compiles this into pure functional operations. The resulting code is referentially transparent, but the syntax is familiar to programmers from imperative backgrounds.

This style shines for algorithms where the functional version would be contorted. Consider [Project Euler Problem 2](https://projecteuler.net/problem=2): sum even Fibonacci numbers below four million. The imperative version is direct. The pure functional version would thread accumulators through recursive calls, which is correct but harder to read.

Use `partial` when exploring, prototyping, or when the termination argument would distract from the actual logic. When you need to prove properties about the function, you will need to establish termination. But not everything needs to be a theorem. Sometimes you just want an answer.

## Unless

The `unless` keyword is syntactic sugar for `if not`. When you find yourself writing `if !condition then ...`, the negation can obscure intent. With `unless`, the code reads closer to how you would describe it in English: "unless this is valid, bail out early."

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:unless}}
```

The `unless` keyword works in do blocks as a guard clause. Combined with `continue`, it provides a clean way to skip iterations that fail some condition without nesting the rest of the loop body inside an `if`.

## For Loops

For loops iterate over anything with a `ForIn` instance. Lists, arrays, ranges, and custom types all work uniformly. The syntax `for x in collection do` binds `x` to each element in turn.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:for_loops}}
```

The range syntax `[start:stop]` generates numbers from `start` up to but not including `stop`. Add a third component `[start:stop:step]` to control the increment. Like Python slices, these are exclusive on the right. Unlike C loops, there is no opportunity to mess up the bounds.

## While Loops

While loops repeat until their condition becomes false. They work within do blocks using `Id.run do` for pure computation or directly in `IO` for effectful operations.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:while_loops}}
```

The `while true do` pattern with early `return` handles cases where the exit condition is easier to express as "stop when" rather than "continue while." The GCD example uses the standard Euclidean algorithm, which terminates because the remainder strictly decreases.

## Break and Continue

Lean's `continue` skips to the next iteration; early `return` serves as `break` by exiting the entire function. There is no dedicated `break` keyword because the do notation's early return provides the same control flow with clearer semantics.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:break_continue}}
```

In nested loops, early `return` exits all the way out, which is usually what you want when searching. If you need to break only the inner loop while continuing the outer, restructure into separate functions.

## Mutable State

The `let mut` syntax introduces mutable bindings within do blocks. Assignment uses `:=`, and the compiler tracks that mutations happen only within the do block's scope. Under the hood, Lean transforms this into pure functional code by threading state through the computation.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:mutable_state}}
```

The `Id.run do` wrapper extracts the pure result from what looks like imperative code. The `Id` monad is the identity monad: it adds no effects, just provides the syntax. This pattern shines when the algorithm is naturally stateful but the result is pure.

## Structures

**Structures** group related data with named fields. If you have used records in ML, structs in Rust, or data classes in Kotlin, the concept is familiar. Unlike C structs, Lean structures come with automatically generated accessor functions, projection notation, and none of the memory layout anxiety.

```lean
{{#include ../../src/ZeroToQED/ControlFlow.lean:structures_basic}}
```

The `deriving Repr` clause automatically generates a `Repr` instance, which lets `#eval` display the structure's contents. Without it, Lean would not know how to print a `Point`. Other commonly derived instances include `BEq` for equality comparison with `==`, `Hashable` for use in hash maps, and `DecidableEq` for propositional equality that can be checked at runtime. You can derive multiple instances by listing them: `deriving Repr, BEq, Hashable`. The [Polymorphism article](./10_polymorphism.md#deriving-instances) covers this in more detail.

## Updating Structures

Rather than modifying structures in place, Lean provides the `with` syntax for creating new structures based on existing ones with some fields changed. The form `{ p with field := value }` produces a fresh structure whose listed fields take the new values and whose remaining fields are copied from `p`. This functional update pattern means you never have to wonder whether some other part of the code is holding a reference to your data and will be surprised by your mutations.

You can also list several sources, as in `{ p, q with x := value }`. Each field you do not assign is filled from the first listed source that provides it, so the sources are tried left to right. This is handy for layering a partial override on top of one or more base values.

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

The constructs above combine naturally in larger programs. What better way to demonstrate this than modeling the "real world"? We will build a [Dungeons & Dragons](https://en.wikipedia.org/wiki/Dungeons_%26_Dragons) character generator. D&D is a tabletop role-playing game where players create characters with ability scores, races, and classes, then embark on adventures guided by dice rolls and a referee called the Dungeon Master. The game has been running since 1974, which makes it older than most programming languages and considerably more fun than COBOL.

Structures hold character data, inductive types represent races and classes, pattern matching computes racial bonuses, and recursion drives the dice-rolling simulation.

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

Try different seeds to generate different characters. The generator uses a deterministic pseudo-random number generator, so the same seed always produces the same character.

> [!TIP]
> Run from the repository: `lake exe dnd 42`. The full source is on [GitHub](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/DndCharacter.lean).

## Toward Abstraction

With structures and inductive types, you can model complex domains. But real programs need abstraction over types themselves. Polymorphism and type classes let you write code that works for any type satisfying certain constraints. This is how you build generic libraries without sacrificing type safety.

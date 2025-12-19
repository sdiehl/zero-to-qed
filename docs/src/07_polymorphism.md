# Polymorphism and Type Classes

On September 23, 1999, the Mars Climate Orbiter disintegrated in the Martian atmosphere because one piece of software produced thrust data in pound-force seconds while another expected newton-seconds. A \\$327 million spacecraft, destroyed by a unit conversion error that any undergraduate physics student could catch. The software worked. The math was correct. The types simply failed to express the constraints that mattered.

This is what motivates the machinery in this article. Type classes and phantom types let you encode dimensional constraints directly in the type system. You cannot add meters to seconds because the compiler will not let you. You cannot pass thrust in the wrong units because the function signature forbids it. These constraints cost nothing at runtime, they compile away completely, but they catch at compile time the very class of error that destroyed a spacecraft. By the end of this article, you will see how to build such a system yourself.

But safety is only half the story. Polymorphism is also about not writing the same code twice. A sorting algorithm should not care whether it sorts integers, strings, or financial instruments. A data structure should not be rewritten for each type it might contain. The alternative is copying code and changing types by hand, which is how bugs are born and how programmers lose their minds. Polymorphism is the machinery that makes abstraction possible without sacrificing type safety.

In 1967, Christopher Strachey drew a distinction that would shape programming languages for decades: parametric polymorphism, where code works uniformly for all types, versus ad-hoc polymorphism, where the behavior changes based on the specific type involved. The first gives you `reverse : List α → List α`, a function blissfully ignorant of what the list contains. The second gives you `+`, which does quite different things to integers, floats, and matrices. Lean provides both, unified under a type class system that traces its lineage back to the 1989 paper [How to Make Ad-Hoc Polymorphism Less Ad Hoc](https://dl.acm.org/doi/pdf/10.1145/75277.75283). The result is generic code that is simultaneously flexible and precise.

## Parametric Polymorphism

Functions can take type parameters, allowing them to work with any type without knowing or caring what that type is. The function `length : List α → Nat` counts elements whether they are integers, strings, or proof terms. The curly braces indicate implicit arguments that Lean infers automatically, sparing you the tedium of writing `length (α := Int) myList` everywhere.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:parametric_polymorphism}}
```

## Polymorphic Data Types

Data types can also be parameterized, creating generic containers that work with any element type. You define `List α` once and get lists of integers, lists of strings, and lists of lists for free. The alternative, writing `IntList`, `StringList`, and `ListOfLists` separately, is how Java programmers spent the 1990s.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:polymorphic_data}}
```

## Implicit Arguments

Implicit arguments in curly braces are inferred by Lean from context. When inference fails or you want to override it, the `@` prefix makes everything explicit. This escape hatch is rarely needed, but when you need it, you really need it.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:implicit_arguments}}
```

## Instance Arguments

Square brackets denote instance arguments, resolved through type class inference. When you write `[Add α]`, you are saying "give me any type that knows how to add." The compiler finds the right implementation automatically. This is the mechanism that lets `+` work on integers, floats, vectors, and anything else with an `Add` instance.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:instance_implicit}}
```

## Defining Type Classes

Type classes define interfaces that types can implement, but unlike object-oriented interfaces, the implementation is external to the type. You can add new capabilities to existing types without modifying them. This is how Lean can make `+` work for types defined in libraries you do not control.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:typeclass_definition}}
```

> [!TIP]
> A type class constraint like `[Add α]` is a proof obligation. The compiler must find evidence that `α` supports addition. Instance resolution is proof search. This connection between "finding implementations" and "finding proofs" is not a metaphor; it is the same mechanism. When you reach the Proofs article, you will see the compiler searching for proofs exactly as it searches for instances here.

## Polymorphic Instances

Instances themselves can be polymorphic, building complex instances from simpler ones. If you can print an `α`, you can print a `List α`. This compositionality is the quiet superpower of type classes: small building blocks assemble into sophisticated behavior without explicit wiring.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:typeclass_polymorphic}}
```

## Numeric Type Classes

Type classes excel at abstracting over numeric operations. Write your algorithm once against an abstract `Mul` and `Add`, and it works for integers, rationals, complex numbers, matrices, and polynomials. The abstraction costs nothing at runtime because instance resolution happens at compile time. The generic code specializes to concrete operations in the generated code.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:numeric_classes}}
```

## Extending Classes

Type classes can extend other classes, inheriting their operations while adding new ones. An `Ord` instance gives you `compare`, and from that you get `<`, `≤`, `>`, `≥`, `min`, and `max` for free. The hierarchy of algebraic structures in Mathlib, from magmas through groups to rings and fields, is built this way.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:extending_classes}}
```

## Functor

The Functor pattern captures the idea of mapping a function over a structure while preserving its shape. Lists, options, arrays, trees, and IO actions are all functors. Once you see the pattern, you see it everywhere: any context that wraps a value and lets you transform that value without escaping the context. Category theory formalizes this intuition, and the [Yoneda lemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Yoneda.html) reveals that an object is completely determined by how other objects map into it.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:functor_class}}
```

## Multiple Constraints

Functions can require multiple type class constraints, combining capabilities from different classes. A sorting function needs `Ord`; a function that sorts and prints needs `[Ord α] [Repr α]`. The constraints document exactly what your function requires, nothing more, nothing less.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:multiple_constraints}}
```

## Deriving Instances

Many standard type classes can be automatically derived, saving you from writing boilerplate that follows predictable patterns. The `deriving` clause generates instances for `Repr`, `BEq`, `Hashable`, and others. Let the machine do the mechanical work; save your creativity for the parts that require thought.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:deriving}}
```

## Semigroups and Monoids

Algebraic structures like semigroups and monoids capture patterns that recur across mathematics and programming. A semigroup has an associative operation; a monoid adds an identity element. String concatenation, list append, function composition, and integer addition are all monoids. Recognizing the common structure lets you write code once and apply it to all of them.

```lean
{{#include ../../src/ZeroToQED/Polymorphism.lean:default_methods}}
```

## Units of Measurement: Safety for Free

Here is the payoff for all the type class machinery. We can prevent the Mars Orbiter bug entirely, not through runtime checks but through types that make the error inexpressible. Consider representing physical quantities with phantom types:

```lean
{{#include ../../src/Examples/Units.lean}}
```

The `Quantity` type wraps a `Float` but carries a phantom type parameter representing its unit. You cannot add meters to seconds because `Quantity.add` requires both arguments to have the same unit type. You cannot pass thrust in the wrong units because the function signature encodes the dimensional requirements.

The crucial insight is that these phantom types vanish at runtime. The `Meters` and `Seconds` types have no constructors, no fields, no runtime representation whatsoever. The generated code manipulates raw floats with raw floating-point operations. The type checker enforces dimensional correctness; the compiled program pays no cost for it. This is the dream of static typing: safety that exists only in the compiler's mind, free at runtime, catching at compile time the very class of error that destroyed a spacecraft.

There is a broader lesson here about the direction of software. The mathematics that physicists scribble on whiteboards, the dimensional analysis that engineers perform by hand, the invariants that programmers hold in their heads and document in comments: these are all pseudocode. They are precise enough for humans to follow but not precise enough for machines to verify. The project of programming language research, from Curry and Howard through ML and Haskell to Lean and dependent types, has been to formalize this pseudocode. To turn informal reasoning into machine-checked artifacts.

As code generation by large language models becomes routine, this formalization becomes essential. A neural network can produce syntactically correct code that passes tests yet harbors subtle unit errors, off-by-one mistakes, and violated invariants. The guardrails cannot be more tests, more code review, more human attention. The guardrails must be formalisms that make entire categories of errors unrepresentable. Type classes, phantom types, dependent types: these are not academic curiosities but safety controls for a future where most code is synthesized. The Mars Climate Orbiter was written by humans who made a human error. The code that replaces them must be held to a higher standard. (For more on this trajectory, see [Artificial Intelligence](./18_artificial_intelligence.md).)

Build and run with:

```bash
lake exe units
```

## Side Effects Ahead

Type classes and phantom types give you abstraction and compile-time safety. But programs must eventually interact with the world: reading files, handling errors, managing state. Next up: monads. Yes, those monads. Do not worry, we will not explain them using burritos.

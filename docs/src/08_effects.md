# Effects

"A monad is just a monoid in the category of endofunctors, what's the problem?" This infamous quip became the ur-meme of functional programming, spawning a thousand blog posts explaining monads via burritos, boxes, and space suits. The tragedy is that the concept is not hard. It just got wrapped in mystique before anyone explained it clearly.

Here is what matters: programs have effects. They might fail, consult state, perform IO, branch nondeterministically, or launch the missiles. In languages without effect tracking, any function call might do any of these things. You call `getUsername()` and hope it only reads from a database rather than initiating thermonuclear war. The type signature offers no guarantees. The question is how to represent effects in a way that lets us reason about composition and know, from the types alone, what a function might do. Monads are one answer. They capture a pattern for sequencing operations where each step produces both a result and some context. Bind chains these operations, threading the context automatically. Do notation makes the sequencing readable. The interface is minimal; the applications are broad.

But monads are not the only answer, and treating them as sacred obscures the deeper point. Algebraic effect systems, linear types, graded monads, and effect handlers all attack the same problem from different angles. What they share is the conviction that effects should be visible in types and that composition should be governed by laws. The specific mechanism matters less than the principle: make the structure explicit so that humans and machines can reason about it.

Lean uses monads because they work well and the ecosystem inherited them from functional programming research of the 1990s. They are a good tool. But the goal is not to be monadic; the goal is to capture effects algebraically, whatever form that takes. When you understand monads, you understand one particularly elegant solution to sequencing effectful computations. You also understand a template for how programming abstractions should work: a minimal interface, a set of laws, and the discipline to respect both.

## The Option Monad

The simplest monad handles computations that might fail. You already understand this pattern: look something up, and if it exists, do something with it; if not, propagate the absence. Every programmer has written this code a hundred times. The monad just gives it a name and a uniform interface.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:option_monad}}
```

## Chaining Without Monads

Without the abstraction, chaining fallible operations produces the pyramid of doom: nested conditionals, each handling failure explicitly, the actual logic buried under boilerplate. This is not hypothetical. This is what error handling looks like in languages without monadic structure. It is also what early JavaScript looked like before Promises, which are, of course, monads by another name.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:option_chaining_ugly}}
```

## The bind Operation

The `bind` operation (written `>>=`) is the heart of the monad. It takes a value in context and a function that produces a new value in context, and chains them together. For `Option`, this means: if the first computation succeeded, apply the function; if it failed, propagate the failure. The pattern generalizes far beyond failure, but failure is the clearest example.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:option_bind}}
```

## Do Notation

Do notation is syntactic sugar that makes monadic code look imperative. The left arrow `←` desugars to bind; the semicolon sequences operations. This is not a concession to programmers who cannot handle functional style. It is recognition that sequential composition is how humans think about processes, and fighting that serves no purpose. The abstraction remains; only the syntax yields to ergonomics.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:do_notation}}
```

## The Except Monad

`Option` tells you that something failed but not why. `Except` carries the reason. This is the difference between a function returning null and a function throwing an exception with a message. The monadic structure is identical; only the context changes. This uniformity is the point. Learn the pattern once, apply it to failure, to errors, to state, to nondeterminism, to parsing, to probability distributions. The shape is always the same.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:except_monad}}
```

## The State Monad

The state monad threads mutable state through a pure computation. You get the ergonomics of mutation, the ability to read and write a value as you go, without actually mutating anything. Each computation takes a state and returns a new state alongside its result. The threading is automatic, hidden behind the monadic interface. This is not a trick. It is a different way of thinking about state: not as a mutable box but as a value that flows through your computation, transformed at each step.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:state_monad}}
```

## StateM in Practice

Lean provides `StateM`, a production-ready state monad. The operations `get`, `set`, and `modify` do exactly what their names suggest. Combined with do notation, stateful code looks almost identical to imperative code, except that the state is explicit in the type and the purity is preserved. You can run the same computation with different initial states and get reproducible results. You can reason about what the code does without worrying about hidden mutation elsewhere.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:state_example}}
```

## The List Monad

Lists as a monad represent nondeterministic computation: a value that could be many things at once. Bind explores all combinations, like nested loops but without the nesting. This is how you generate permutations, enumerate possibilities, or implement backtracking search. The abstraction is the same; only the interpretation differs. A monad does not care whether its context is failure, state, or multiplicity. It only knows how to sequence.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:list_monad}}
```

## The Monad Type Class

Under the hood, all monads implement the same interface. `pure` lifts a plain value into the monadic context. `bind` sequences two computations, passing the result of the first to the second. That is the entire interface. Everything else, the do notation, the specialized operations, the ergonomic helpers, builds on these two primitives. The simplicity is deliberate. A minimal interface means maximal generality.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:monad_class}}
```

## Monad Laws

Here is where the algebra becomes essential. Monads must satisfy three laws: left identity, right identity, and associativity. These are not suggestions. They are the contract that makes generic programming possible.

In the traditional bind/return formulation:

| Law            | Lean                                         | Math                                                          |
| -------------- | -------------------------------------------- | ------------------------------------------------------------- |
| Left Identity  | `pure a >>= f = f a`                         | \\(\eta(a) \star f = f(a)\\)                                  |
| Right Identity | `m >>= pure = m`                             | \\(m \star \eta = m\\)                                        |
| Associativity  | `(m >>= f) >>= g = m >>= (λ x => f x >>= g)` | \\((m \star f) \star g = m \star (\lambda x. f(x) \star g)\\) |

The same laws look cleaner in the Kleisli category, where we compose monadic functions directly. If \\(f : A \to M B\\) and \\(g : B \to M C\\), their Kleisli composition is \\(g \circ f : A \to M C\\):

| Law            | Lean                                | Math                                            |
| -------------- | ----------------------------------- | ----------------------------------------------- |
| Left Identity  | `pure >=> f = f`                    | \\(\eta \circ f = f\\)                          |
| Right Identity | `f >=> pure = f`                    | \\(f \circ \eta = f\\)                          |
| Associativity  | `(f >=> g) >=> h = f >=> (g >=> h)` | \\((h \circ g) \circ f = h \circ (g \circ f)\\) |

The Kleisli formulation reveals that monads give you a category where objects are types and morphisms are functions \\(A \to M B\\). The laws say `pure` is the identity morphism and `>=>` is associative composition. A monad is a way of embedding effectful computation into the compositional structure of functions.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:monad_laws}}
```

> [!TIP]
> In most languages, monad laws are documentation or tests. In Lean, they are theorems. You can state them as propositions and prove them. This is the Curry-Howard correspondence at work: the law "left identity" becomes a type, and proving it means constructing a value of that type. The [Proofs](./10_proving.md) article shows how.

At this point someone usually asks what a monad "really is." The answers have become a genre: a burrito, a spacesuit, a programmable semicolon, a monoid in the category of endofunctors. These metaphors are not wrong, but they are not enlightening either. A monad is the three laws above and nothing else. Everything follows from the laws. The metaphors are for people who want to feel like they understand before they do the work of understanding.

If you want the category theory (colloquially known as "[abstract nonsense](https://ncatlab.org/nlab/show/abstract+nonsense)," which is their term of endearment for their own field): a monad is a [monoid object](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category) in the monoidal category of [endofunctors](https://ncatlab.org/nlab/show/endofunctor) under composition. Equivalently, it is a [lax 2-functor](https://ncatlab.org/nlab/show/lax+2-functor) from the terminal 2-category to [Cat](https://ncatlab.org/nlab/show/Cat). A category is just a monoid in the endomorphism hom-category of the [bicategory of spans](https://ncatlab.org/nlab/show/span). The [Kleisli category](https://ncatlab.org/nlab/show/Kleisli+category) is the free algebra of the monad. `some` is just the identity morphism in the Kleisli category of `Option`. In Haskell it's called `Just`, which humorously is Just an endomorphism in the Kleisli category of `Option`. Har har. Feeling enlightened yet? 🙃

## Early Return

Do notation supports early return, loops, and mutable references, all the imperative conveniences. Combined with monads, this gives you the syntax of imperative programming with the semantics of pure functions. You can write code that reads like Python and reasons like Haskell. This is not cheating. It is the whole point: capturing effects in types so that the compiler knows what your code might do, while letting you write in whatever style is clearest.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:early_return}}
```

## Combining Monadic Operations

Functions like `mapM` and `filterMap` combine monadic operations over collections. Map a fallible function over a list and either get all the results or the first failure. Filter a list with a predicate that consults external state. These combinators emerge naturally once you have the abstraction. They are not special cases but instances of a general pattern, composable because they respect the monad laws.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:combining_monads}}
```

## The Larger Pattern

Monads are one algebraic structure among many. Functors capture mapping. Applicatives capture independent combination. Monads capture dependent sequencing. Comonads capture context extraction. Arrows generalize computation graphs. Algebraic effects decompose monads into composable pieces. Each abstraction comes with laws, and those laws are the actual content. The specific names matter less than the discipline: identify a pattern, find its laws, and build an interface that enforces them.

The trajectory of programming language research has been toward making this structure explicit. Effects that C programmers handle with conventions, functional programmers handle with types. Invariants that documentation describes, dependent types enforce. Properties that tests sample, proofs establish. Each step reduces the burden on human memory and attention, encoding knowledge in artifacts that machines can check.

This matters because the economics of software are changing. When code is cheap to generate, correctness becomes the bottleneck. A language model can produce plausible implementations faster than any human, but "plausible" is not "correct." The leverage shifts to whoever can specify precisely what correct means. Types, laws, contracts, proofs: these are the tools for specifying. Monads are a small example, one worked case of a pattern made precise. The concept itself was always simple. Sequencing with context. The value was never in the mystery but in the laws that let us reason compositionally about programs we did not write and cannot fully read. (For more on where this is heading, see [Artificial Intelligence](./19_artificial_intelligence.md).)

## From Abstract to Concrete

Monads describe effects abstractly. The next article makes them concrete: actual file I/O, process management, environment variables, and the runtime machinery that connects your pure descriptions to the impure world. This completes the programming half of our journey.

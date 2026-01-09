# Effects

"A monad is just a monoid in the category of endofunctors, what's the problem?" This infamous quip became the ur-meme of functional programming, spawning a thousand blog posts explaining monads via burritos, boxes, and space suits. The tragedy is that the concept is not hard. It just got wrapped in mystique before anyone explained it clearly.

Here is what matters: programs have **effects**. They might fail, consult state, perform IO, branch nondeterministically, or launch the missiles. In languages without effect tracking, any function call might do any of these things. You call `getUsername()` and hope it only reads from a database rather than initiating thermonuclear war. The type signature offers no guarantees. The question is how to represent effects in a way that lets us reason about composition and know, from the types alone, what a function might do. **Monads** are one answer. They capture a pattern for sequencing operations where each step produces both a result and some context. Bind chains these operations, threading the context automatically. Do notation makes the sequencing readable. The interface is minimal; the applications are broad.

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

The **`bind`** operation (written `>>=`) is the heart of the monad. It takes a value in context and a function that produces a new value in context, and chains them together. For `Option`, this means: if the first computation succeeded, apply the function; if it failed, propagate the failure. The pattern generalizes far beyond failure, but failure is the clearest example.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:option_bind}}
```

## Do Notation

**Do notation** is syntactic sugar that makes monadic code look imperative. The left arrow `←` desugars to bind; the semicolon sequences operations. This is not a concession to programmers who cannot handle functional style. It is recognition that sequential composition is how humans think about processes, and fighting that serves no purpose. The abstraction remains; only the syntax yields to ergonomics.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:do_notation}}
```

## Do Notation Desugaring

Do notation is syntactic sugar for bind chains. The compiler transforms your imperative-looking code into applications of `>>=` and `pure`. Understanding the desugaring helps when types do not match or when you want to optimize.

A monadic bind extracts the value and passes it to the continuation:

```
do                              e1 >>= fun x =>
  let x ← e1        ⟹           do es
  es
```

A pure let binding has no monadic involvement:

```
do                              let x := e
  let x := e        ⟹           do es
  es
```

An action without binding discards the result:

```
do                              e1 >>= fun () =>
  e1                ⟹           do es
  es
```

Pattern matching with a fallback handles failure:

```
do                              e1 >>= fun
  let some x ← e1   ⟹             | some x => do es
    | fallback                    | _ => fallback
  es
```

The `return` keyword is just `pure`:

```
return e            ⟹           pure e
```

The `←` operator can appear as a prefix within expressions. Each occurrence is hoisted to a fresh binding, processed left-to-right, inside-to-outside:

```
do                              do
  f (← e1) (← e2)   ⟹             let x ← e1
  es                              let y ← e2
                                  f x y
                                  es
```

Effects like early return, mutable state, and loops with `break`/`continue` transform the entire do block rather than desugaring locally, similar to monad transformers.

> [!NOTE]
> Semicolons can replace newlines in do blocks: `do let x ← e1; let y ← e2; pure (x + y)`. This is rarely used since multiline format is "more readable." Fifty years of programming language research and we still cannot agree on what makes syntax objectively good. Perhaps because syntax is more fashion and culture than science.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:do_desugaring}}
```

## Mutable Variables in Do

The `let mut` syntax introduces mutable bindings that desugar to `StateT`. Assignment with `:=` modifies the state. The compiler threads the state automatically, transforming imperative-looking code into pure functional operations.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:do_mutable}}
```

The `Id.run do` pattern runs a do block that uses only local mutable state. The `Id` monad adds no effects; it just provides the scaffolding for the state transformation. For IO operations, you work directly in the `IO` monad and the mutations interleave with side effects.

## The Except Monad

`Option` tells you that something failed but not why. `Except` carries the reason. This is the difference between a function returning null and a function throwing an exception with a message. The monadic structure is identical; only the context changes. This uniformity is the point. Learn the pattern once, apply it to failure, to errors, to state, to nondeterminism, to parsing, to probability distributions. The shape is always the same.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:except_monad}}
```

## Transporter Malfunction

The [transporter](https://memory-alpha.fandom.com/wiki/Transporter) is Star Trek's matter-energy teleportation device. It is also perhaps the most horrifying device in science fiction. It disassembles you at the atomic level, transmits your pattern as information, and reassembles a copy at the destination. The original is destroyed. What arrives is a perfect duplicate with all your memories, convinced it is you. Philosophers call this the [teleportation problem](https://www3.nd.edu/~jspeaks/courses/2011-12/20229/handouts/8%20Personal%20identity.pdf). Starfleet calls it Tuesday.

From an engineering perspective, the transporter is a pipeline of fallible operations that must also maintain a log. Initialize the pattern buffer. Scan the subject. Dematerialize. Transmit. Rematerialize. Each step can fail (buffer overflows, Heisenberg compensator malfunctions), and each step should be logged for the accident investigation. This requires combining two effects: error handling and state.

```lean
{{#include ../../src/Examples/Transporter.lean:errors_and_types}}
```

### Transformer Ordering Matters

When you combine `StateT` and `Except`, the order matters. These two type aliases have different semantics:

```lean
{{#include ../../src/Examples/Transporter.lean:transformer_stacks}}
```

The difference emerges when an operation fails partway through. With `StateT` on the outside, the error discards the accumulated state. With `ExceptT` on the outside, the state persists even after failure. In database terms: transaction rollback versus audit logging.

```lean
{{#include ../../src/Examples/Transporter.lean:operations_b}}
```

### The Philosophical Horror

Consider what happens when transport fails after dematerialization but before rematerialization. The log reads: "Pattern in buffer, subject no longer exists at origin" followed by "ERROR: Heisenberg compensator failure."

With audit log semantics (`ExceptT` outside), the log persists. The crew member does not.

```lean
{{#include ../../src/Examples/Transporter.lean:running}}
```

For databases, you choose the transformer ordering based on requirements. Financial audits need persistent logs; atomic transactions need rollback. For humans, "transaction aborted after dematerialization" raises questions not covered in the Starfleet manual. The log shows you were disassembled. The error shows you were never reassembled. What exactly should rollback mean here?

> [!TIP]
> Run from the repository: `lake exe transporter`

If formal verification ever finds a practical purpose beyond software, reassembling humans at the molecular level might be a suitable application. You would want mathematical certainty that the rematerialized crew member has all their organs in the correct configuration, that no quantum state got flipped during transmission, that the thing stepping off the pad is topologically equivalent to what stepped on. (A human turned inside-out is [homeomorphic](https://www.youtube.com/watch?v=nW-NiGp1gys) to the original, but the crew tends to file complaints.) Supposing we can get the Heisenberg compensator to work, of course. Until then, we practice on programs.

## The State Monad

The **state monad** threads mutable state through a pure computation. You get the ergonomics of mutation, the ability to read and write a value as you go, without actually mutating anything. Each computation takes a state and returns a new state alongside its result. The threading is automatic, hidden behind the monadic interface. This is not a trick. It is a different way of thinking about state: not as a mutable box but as a value that flows through your computation, transformed at each step.

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

## Iteration Type Classes

The `ForIn` type class powers for loops. Any type with a `ForIn` instance can be iterated with `for x in collection do`. The mechanism is more flexible than it first appears: you can implement custom iteration patterns, control early exit, and work in any monad.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:forin_class}}
```

The `ForInStep` type controls loop flow. Returning `.done value` breaks out of the loop with the accumulated result. Returning `.yield value` continues to the next iteration. This desugars to monadic operations, so early return in a for loop is not a special case but an application of the general mechanism.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:form_class}}
```

The `forIn` function can be called directly when you need explicit control over the accumulator and continuation. The callback returns `some (.done acc)` to break or `some (.yield acc)` to continue. Returning `none` propagates failure in the `Option` monad. This is how Lean unifies iteration with monadic effects.

## Collection Operations

Lists and arrays share a common vocabulary of operations. These functions compose naturally into data processing pipelines.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:iterators}}
```

The operations compose cleanly: `filter` selects, `map` transforms, `filterMap` fuses both. `find?` returns `Option` because absence is a valid result, not an exception.

## Folds

Folds are the fundamental iteration pattern. Every loop, every accumulation, every reduction can be expressed as a fold. Understanding folds means understanding how computation flows through a data structure.

A **left fold** processes elements left-to-right, accumulating from the left:

\\[
\text{foldl}(f, z, [a, b, c]) = f(f(f(z, a), b), c) = ((z \oplus a) \oplus b) \oplus c
\\]

A **right fold** processes elements right-to-left, accumulating from the right:

\\[
\text{foldr}(f, z, [a, b, c]) = f(a, f(b, f(c, z))) = a \oplus (b \oplus (c \oplus z))
\\]

Here \\(\oplus\\) is just \\(f\\) written infix: \\(a \oplus b = f(a, b)\\).

For associative operations like addition, both folds give the same result. For non-associative operations, the parenthesization matters:

```lean
{{#include ../../src/ZeroToQED/Effects.lean:folds}}
```

The cons example reveals the structural difference. Building a list with `foldl` reverses order because each new element is prepended to the growing accumulator. Building with `foldr` preserves order because the accumulator grows from the right. This is why `map` is typically defined using `foldr`: `map f xs = foldr (fun x acc => f x :: acc) [] xs`.

Left folds are tail-recursive and run in constant stack space. Right folds are not tail-recursive but can work with lazy data structures since they do not need to traverse to the end before producing output. In strict languages like Lean, prefer `foldl` for efficiency unless you need the structural properties of `foldr`.

## The Monad Type Class

Under the hood, all monads implement the same interface. `pure` lifts a plain value into the monadic context. `bind` sequences two computations, passing the result of the first to the second. That is the entire interface. Everything else, the do notation, the specialized operations, the ergonomic helpers, builds on these two primitives. The simplicity is deliberate. A minimal interface means maximal generality.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:monad_class}}
```

## Monad Laws

Here is where the algebra becomes essential. Monads must satisfy three laws: left identity, right identity, and associativity. These are not suggestions. They are the contract that makes generic programming possible.

In the traditional bind/return formulation:

| Law            | Lean                                         | Math                                                      |
| -------------- | -------------------------------------------- | --------------------------------------------------------- |
| Left Identity  | `pure a >>= f = f a`                         | $\eta(a) \star f = f(a)$                                  |
| Right Identity | `m >>= pure = m`                             | $m \star \eta = m$                                        |
| Associativity  | `(m >>= f) >>= g = m >>= (λ x => f x >>= g)` | $(m \star f) \star g = m \star (\lambda x. f(x) \star g)$ |

The same laws look cleaner in the Kleisli category, where we compose monadic functions directly. If $f : A \to M B$ and $g : B \to M C$, their Kleisli composition is $g \circ f : A \to M C$:

| Law            | Lean                                | Math                                        |
| -------------- | ----------------------------------- | ------------------------------------------- |
| Left Identity  | `pure >=> f = f`                    | $\eta \circ f = f$                          |
| Right Identity | `f >=> pure = f`                    | $f \circ \eta = f$                          |
| Associativity  | `(f >=> g) >=> h = f >=> (g >=> h)` | $(h \circ g) \circ f = h \circ (g \circ f)$ |

The Kleisli formulation reveals that monads give you a category where objects are types and morphisms are functions $A \to M B$. The laws say `pure` is the identity morphism and `>=>` is associative composition. A monad is a way of embedding effectful computation into the compositional structure of functions.

```lean
{{#include ../../src/ZeroToQED/Effects.lean:monad_laws}}
```

> [!TIP]
> In Haskell (and most other languages), you can claim your monad follows the laws but the compiler takes your word for it. In Lean, you can prove it. The laws become theorems, and proving them means constructing values of the corresponding types. This is the Curry-Howard correspondence at work. The [Proofs](./11_proving.md) article shows how.

At this point someone usually asks what a monad "really is." The answers have become a genre: a burrito, a spacesuit, a programmable semicolon, a monoid in the category of endofunctors. These metaphors are not wrong, but they are not enlightening either. A monad is the three laws above and nothing else. Everything follows from the laws. The metaphors are for people who want to feel like they understand before they do the work of understanding.

If you want the category theory (colloquially known as "[abstract nonsense](https://ncatlab.org/nlab/show/abstract+nonsense)," which is their term of endearment for their own field): a monad is a [monoid object](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category) in the monoidal category of [endofunctors](https://ncatlab.org/nlab/show/endofunctor) under composition. Equivalently, it is a [lax 2-functor](https://ncatlab.org/nlab/show/lax+2-functor) from the terminal 2-category to [Cat](https://ncatlab.org/nlab/show/Cat). A category is just a monoid in the endomorphism hom-category of the [bicategory of spans](https://ncatlab.org/nlab/show/span). The [Kleisli category](https://ncatlab.org/nlab/show/Kleisli+category) is the free algebra of the monad. `some` is just the identity morphism in the Kleisli category of `Option`. In Haskell it is called `Just`, which humorously is Just an endomorphism in the Kleisli category of `Option`. If this clarified nothing, congratulations: you understood monads before and still do now.

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

This matters because the economics of software are changing. When code is cheap to generate, correctness becomes the bottleneck. A language model can produce plausible implementations faster than any human, but "plausible" is not "correct." The leverage shifts to whoever can specify precisely what correct means. Types, laws, contracts, proofs: these are the tools for specifying. Monads are a small example, one worked case of a pattern made precise. The concept itself was always simple. Sequencing with context. The value was never in the mystery but in the laws that let us reason compositionally about programs we increasingly do not write ourselves and cannot fully understand. (For more on where this is heading, see [Artificial Intelligence](./21_artificial_intelligence.md).)

## From Abstract to Concrete

Monads describe effects abstractly. The [next article](./10_io.md) makes them concrete: actual file I/O, process management, environment variables, and the runtime machinery that connects your pure descriptions to the impure world. This completes the programming half of our journey.

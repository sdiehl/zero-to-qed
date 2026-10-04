# Termination and Well-Founded Recursion

The previous article showed structural recursion, where Lean accepts your function because each recursive call peels off a constructor. That covers most everyday programming. It does not cover the Euclidean algorithm, Ackermann's function, binary search, or anything that recurses on a computed value rather than a structurally smaller piece of its input. Hit that wall and the compiler stops being your friend. It asks you to prove that your function terminates, and the error message is rarely helpful the first time you see it. This article is about getting past that wall.

The reason Lean asks at all is foundational, not pedantic. A non-terminating function in a dependently typed language is not a bug, it is a paradox. If you could write a function `loop : Empty` that runs forever, the kernel would believe you had inhabited the empty type. Every theorem becomes provable, the logic collapses, and the proof of `1 = 2` is two lines. Most programming languages let you write `while True`. Lean refuses to laugh at that joke.

## Structural Recursion: The Easy Case

When the recursive argument structurally decreases by peeling off `Nat.succ` or `List.cons` one constructor at a time, Lean accepts the definition without ceremony. You have written dozens of these already and never had to prove anything.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:structural_review}}
```

The compiler synthesizes the termination proof from the inductive type's recursor. No annotation is needed because the argument structurally decreases on every call. This is the path of least resistance, and you should follow it whenever the shape of your data lets you.

## termination_by

When the recursive call passes a _computed_ expression rather than a structural sub-piece, Lean falls back to well-founded recursion. It first tries to guess a measure from the arguments; when that guess fails or you want to be explicit, the `termination_by` clause names the measure. Lean then synthesizes the proof using the well-founded order on whatever type you named.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:termination_by_basic}}
```

`halve` recurses on `n / 2`, which is structurally unrelated to `n` but strictly less than `n` whenever `n ≥ 2`. The `termination_by n` clause tells Lean to use `Nat`'s well-founded `<` order on `n`, and the elaborator discharges the goal automatically because `n / 2 < n` is a known lemma. The trick is to name something the compiler can already reason about. `Nat`, `List.length`, anything that ships with a `WellFoundedRelation` instance.

## When the Proof Is Not Automatic

`termination_by` works when Lean can already see why the measure shrinks. The Euclidean algorithm recursing on `a % b`, Ackermann's function juggling two arguments, merge sort splitting a list in the middle: each of these needs a short proof that the measure decreases, written by you. Those proofs use tactics, hypotheses, and inequalities, which is the subject of the second arc. We return to them in [Proving Termination](./14_proof_strategy.md#proving-termination), after the basics of proving are in place. For now, the two escape hatches below cover the cases where you do not want to prove termination at all.

## Partial Functions

Sometimes you do not want to prove termination. The function might genuinely not terminate, like a server loop or a REPL. The proof obligation might be a research problem, like Collatz. Mark the definition `partial` to compile it without a termination proof while keeping its body opaque to the logic.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:partial_escape}}
```

Partial functions are opaque to the kernel: their recursive bodies do not unfold during proofs or type checking. They still exist in the logic as constants, so reflexive equalities about them are available. Their implementations compile and execute, potentially without terminating. To reason about the recursive computation itself, use a total definition with a termination proof or an explicit fuel parameter.

The deeper reason `partial` is safe is that the kernel never uses the recursive body as a logical definition. Lean requires a nonempty result type, supplied through `Nonempty` or `Inhabited`, so the opaque constant can be justified without assuming that execution terminates. Thus `partial def loop : Nat := loop` does not break soundness, but its runtime implementation cannot justify equations in a proof.

## The Fuel Pattern

When you need a partial function but want to use it in proofs anyway, pass an explicit fuel parameter. The fuel is a `Nat` that strictly decreases on every recursive call, and it doubles as the termination measure. When fuel runs out, the function returns a default. The function is total, because fuel always runs out, and the original semantics is recovered by passing enough fuel for the input you care about.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:fuel_pattern}}
```

The Collatz conjecture is the canonical excuse for this pattern. Nobody knows how to bound the actual descent, but we can still compute trajectories by capping the steps. Lothar Collatz proposed the conjecture in 1937. Computers have verified it up to roughly 2^68. Erdős said "Mathematics is not yet ready for such problems." Until someone proves him wrong, fuel is the workaround. The `mergeSort` example in the previous chapter avoided fuel because the list length is a real measure that does decrease. Use fuel when you genuinely cannot find a measure, and document the cap so future readers know it is an artifact, not a property.

## Where This Bites

The first time you write a recursive function on something other than a `Nat` or a `List`, you will hit one of these cases. Recursing on `n / 2` needs `termination_by` and nothing more. Recursing on `a % b`, on a list you split in the middle, or on two arguments where neither decreases consistently needs a measure plus a short proof that it shrinks. Those proofs are mechanical once you recognize the shape, and [Proving Termination](./14_proof_strategy.md#proving-termination) catalogs the shapes. The error message rarely points you at the right one, so the next time you see "failed to prove termination", work out which argument decreases on which call before reaching for `partial`.

When no measure works, you have either written something that genuinely does not terminate (use `partial`), something whose termination is a real theorem (use fuel), or something where the measure exists but you have not found it yet (read the goal carefully, and write the measure as a tuple if two arguments take turns decreasing). The third case is the most common. The compiler is rarely wrong, even when it is unhelpful.

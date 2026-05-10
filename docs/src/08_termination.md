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

When the recursive call passes a _computed_ expression rather than a structural sub-piece, Lean cannot guess your termination measure. The `termination_by` clause names it explicitly. Lean then synthesizes the proof using the well-founded order on whatever type you named.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:termination_by_basic}}
```

`halve` recurses on `n / 2`, which is structurally unrelated to `n` but strictly less than `n` whenever `n ≥ 2`. The `termination_by n` clause tells Lean to use `Nat`'s well-founded `<` order on `n`, and the elaborator discharges the goal automatically because `n / 2 < n` is a known lemma. The trick is to name something the compiler can already reason about. `Nat`, `List.length`, anything that ships with a `WellFoundedRelation` instance.

## decreasing_by

Sometimes Lean cannot find the proof on its own. The `decreasing_by` clause attaches a tactic block that closes the termination goal manually.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:gcd_decreasing}}
```

The Euclidean GCD recurses on `(b, a % b)`, and the second argument decreases only when `b > 0`. The `if h : b = 0` binding makes the negation `b ≠ 0` available in the `else` branch, and `Nat.pos_of_ne_zero` converts that to `b > 0`. From there, `Nat.mod_lt` finishes the proof. The `_h` underscore prefix tells the linter you know `h` is unused in the `then` branch, since you only need it in `decreasing_by`. Euclid wrote this algorithm down around 300 BC, which makes it older than most everything except dirt, and Lean still wants to see your work.

## Lexicographic Termination

When a function takes multiple arguments and the decreasing one varies between calls, name a tuple as the measure. Lean compares tuples lexicographically. The first component decreases, or it stays equal and the second component decreases.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:lex_termination}}
```

Ackermann is the textbook case, and it is on the textbook for a reason. The function grows faster than every primitive recursive function combined, which is exactly the property that breaks naive termination checkers. The middle clause decreases the first argument from `m + 1` to `m`. The last clause does the same on the outer call, but the inner call `ackermann (m + 1) n` keeps the first argument and decreases the second. The lexicographic order on `(m, n)` covers both. Any drop in `m` wins. If `m` is equal, a drop in `n` suffices. The recursion tree is monstrous, the values are astronomical, and the proof is six tokens.

## Have Clauses

When you can prove the decreasing fact more naturally inline, write a `have` in the body. The compiler scans local hypotheses when synthesizing the termination proof, so a well-named inequality is often all you need.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:have_termination}}
```

This is the same technique [the merge sort example](./07_control_flow.md#structural-recursion) used in the previous article. Prove the decrease where you compute it, and the rest happens automatically. Of all the patterns in this chapter, this is the one to reach for first when something other than a `Nat` is decreasing.

## WellFounded.fix

Every well-founded recursion compiles down to `WellFounded.fix`. The `def` machinery, `termination_by`, `decreasing_by`, and the lexicographic order all desugar to a single application of this fixpoint combinator. Calling it directly is occasionally useful when you want to see what the elaborator is doing, or when you need a one-off recursion outside the usual frame. Mostly it is useful for understanding what was happening behind the curtain the whole time.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:wellfounded_fix}}
```

`WellFounded.fix` takes three things. A proof that some relation is well-founded. A step function that may recurse via the `rec` parameter. An initial argument. The step function must show, for every recursive call, that the new argument is smaller in the well-founded relation. Here that proof is the `have : n - 1 < n` clause, passed explicitly as the second argument to `rec`. Compare this to writing `def countdown` with `termination_by n` and the equivalence becomes clear. The latter is sugar for the former. The sugar is good. The plain version is what the kernel sees.

## Partial Functions

Sometimes you do not want to prove termination. The function might genuinely not terminate, like a server loop or a REPL. The proof obligation might be a research problem, like Collatz. Mark the definition `partial` and Lean trusts you.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:partial_escape}}
```

The cost is steep but localized. Partial functions are opaque to the kernel, which means you cannot unfold them in proofs, cannot use them in `decide`, and cannot reduce them in type checking. They compile and execute normally. They just do not exist for the logic. This is the right trade-off when you are writing an interpreter that loops until the user quits, and the wrong trade-off when you want to prove anything about the function later.

The deeper reason `partial` is safe is that Lean splits the universe in two. Code lives in `Type` and proofs live in `Prop`, and the partiality of a function in `Type` cannot leak into a proof in `Prop` because `partial` definitions are kept opaque. You can write `partial def loop : Nat := loop` without breaking soundness, because the kernel never sees the body. The body is just C code as far as the logic is concerned. Run it, do not reason about it.

## The Fuel Pattern

When you need a partial function but want to use it in proofs anyway, pass an explicit fuel parameter. The fuel is a `Nat` that strictly decreases on every recursive call, and it doubles as the termination measure. When fuel runs out, the function returns a default. The function is total, because fuel always runs out, and the original semantics is recovered by passing enough fuel for the input you care about.

```lean
{{#include ../../src/ZeroToQED/Termination.lean:fuel_pattern}}
```

The Collatz conjecture is the canonical excuse for this pattern. Nobody knows how to bound the actual descent, but we can still compute trajectories by capping the steps. Lothar Collatz proposed the conjecture in 1937. Computers have verified it up to roughly 2^68. Erdős said "Mathematics is not yet ready for such problems." Until someone proves him wrong, fuel is the workaround. The `mergeSort` example in the previous chapter avoided fuel because the list length is a real measure that does decrease. Use fuel when you genuinely cannot find a measure, and document the cap so future readers know it is an artifact, not a property.

## Where This Bites

The first time you write a recursive function on something other than a `Nat` or a `List`, you will hit one of these cases. Recursing on `n / 2` needs `termination_by`. Recursing on `a % b` needs `decreasing_by`. Recursing on a list you split in the middle needs a `have` clause showing the halves are shorter. Recursing on two arguments where neither decreases consistently needs a tuple. The good news is that the fix is mechanical once you recognize the shape. The bad news is that the error message rarely points you at the right shape, so the next time you see "failed to prove termination", come back here and match your function against the list above.

When none of these work, you have either written something that genuinely does not terminate (use `partial`), something whose termination is a real theorem (use fuel), or something where the measure exists but you have not found it yet (read the goal carefully, work out which argument decreases on which call, and write the measure as a tuple). The third case is the most common. The compiler is rarely wrong, even when it is unhelpful.

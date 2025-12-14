# Classic Proofs

This article presents proofs you likely encountered in undergraduate mathematics, now written in Lean. Each example shows the traditional proof and its formalization side by side. The goal is not to teach you these theorems; you already know them. The goal is to build intuition for how mathematical reasoning translates into Lean code. When you see a proof by contradiction in English, what tactic does that become? When a textbook says "by strong induction," what does Lean require? The side-by-side format lets you map familiar reasoning patterns onto unfamiliar syntax.

[Euclid's proof](https://en.wikipedia.org/wiki/Euclid%27s_theorem) of the infinitude of primes has survived for over two thousand years. It requires no calculus, no abstract algebra, only the observation that \\(n! + 1\\) shares no prime factors with \\(n!\\). Yet formalizing this argument reveals hidden assumptions: that every number greater than one has a prime divisor, that primes are well-defined, that contradiction is a valid proof technique. The proofs here are not difficult by mathematical standards, but they exercise the full machinery of dependent types, tactics, and theorem proving. They are finger exercises, etudes that build fluency before attempting harder compositions.

## The Infinitude of Primes

**Traditional Proof**

**Theorem.** There exist infinitely many prime numbers.

The proof proceeds in two parts. First, we establish that every integer \\(n \geq 2\\) has a prime divisor. If \\(n\\) is prime, it divides itself. Otherwise, \\(n\\) has a proper divisor \\(m\\) with \\(1 < m < n\\). By strong induction, \\(m\\) has a prime divisor \\(p\\), and since \\(p \mid m\\) and \\(m \mid n\\), we have \\(p \mid n\\).

Second, we show that for any \\(n\\), there exists a prime \\(p > n\\). Consider \\(N = n! + 1\\). Since \\(n! \geq 1\\), we have \\(N \geq 2\\), so \\(N\\) has a prime divisor \\(p\\). We claim \\(p > n\\). Suppose for contradiction that \\(p \leq n\\). Then \\(p \mid n!\\) since \\(n!\\) contains all factors from 1 to \\(n\\). Since \\(p \mid N\\) and \\(p \mid n!\\), we have \\(p \mid (N - n!) = 1\\). But \\(p \geq 2\\), so \\(p \nmid 1\\), a contradiction. Therefore \\(p > n\\). **QED**

**Lean Formalization**

The Lean proof mirrors this structure exactly. The theorem `exists_prime_factor` establishes the first part by case analysis and strong induction (via `termination_by`). The main theorem `InfinitudeOfPrimes` constructs \\(n! + 1\\), extracts a prime divisor, then derives a contradiction using `dvd_factorial` and `Nat.dvd_add_right`.

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:infinitude_primes}}
```

## Irrationality of the Square Root of Two

**Traditional Proof**

**Theorem.** [\\(\sqrt{2}\\) is irrational](https://en.wikipedia.org/wiki/Square_root_of_2#Proofs_of_irrationality).

The key lemma is: if \\(n^2\\) is even, then \\(n\\) is even. We prove the contrapositive. Suppose \\(n\\) is odd, so \\(n = 2k + 1\\) for some integer \\(k\\). Then \\(n^2 = (2k+1)^2 = 4k^2 + 4k + 1 = 2(2k^2 + 2k) + 1\\), which is odd. Therefore, if \\(n^2\\) is even, \\(n\\) cannot be odd, so \\(n\\) must be even.

Now suppose \\(\sqrt{2} = p/q\\) where \\(p, q\\) are integers with \\(q \neq 0\\) and \\(\gcd(p,q) = 1\\). Then \\(2q^2 = p^2\\), so \\(p^2\\) is even, hence \\(p\\) is even. Write \\(p = 2k\\). Then \\(2q^2 = 4k^2\\), so \\(q^2 = 2k^2\\), meaning \\(q^2\\) is even, hence \\(q\\) is even. But then \\(\gcd(p,q) \geq 2\\), contradicting our assumption. **QED**

**Lean Formalization**

The Lean code proves the parity lemmas explicitly. The theorem `sq_odd_of_odd` shows that squaring an odd number yields an odd number by expanding \\((2k+1)^2\\). The theorem `even_of_sq_even` proves the contrapositive: assuming \\(n\\) is odd leads to \\(n^2\\) being odd, which contradicts \\(n^2\\) being even. The final irrationality result follows from Mathlib's `irrational_sqrt_two`, which uses this same parity argument internally.

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:sqrt2_irrational}}
```

## Euclid's Lemma

**Traditional Proof**

**Theorem ([Euclid's Lemma](https://en.wikipedia.org/wiki/Euclid%27s_lemma)).** If a prime \\(p\\) divides a product \\(ab\\), then \\(p \mid a\\) or \\(p \mid b\\).

Let \\(p\\) be prime with \\(p \mid ab\\). Since \\(p\\) is prime, the only divisors of \\(p\\) are 1 and \\(p\\). Therefore \\(\gcd(p, a) \in \\{1, p\\}\\).

**Case 1:** If \\(\gcd(p, a) = p\\), then \\(p \mid a\\) and we are done.

**Case 2:** If \\(\gcd(p, a) = 1\\), we show \\(p \mid b\\). Consider \\(\gcd(pb, ab)\\). Since \\(p \mid pb\\) and \\(p \mid ab\\), we have \\(p \mid \gcd(pb, ab)\\). By the property \\(\gcd(pb, ab) = b \cdot \gcd(p, a) = b \cdot 1 = b\\), we conclude \\(p \mid b\\). **QED**

**Lean Formalization**

The Lean proof follows this GCD-based argument directly. It case-splits on whether \\(\gcd(p, a) = 1\\) or \\(\gcd(p, a) > 1\\). In the coprime case, it uses `Nat.gcd_mul_right` to establish that \\(\gcd(pb, ab) = b\\), then shows \\(p\\) divides this GCD. In the non-coprime case, since \\(p\\) is prime, \\(\gcd(p, a) = p\\), so \\(p \mid a\\).

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:euclid_lemma}}
```

## The Binomial Theorem

**Traditional Proof**

**Theorem ([Binomial Theorem](https://en.wikipedia.org/wiki/Binomial_theorem)).** For real numbers \\(x, y\\) and natural number \\(n\\):
\\[(x + y)^n = \sum_{k=0}^{n} \binom{n}{k} x^k y^{n-k}\\]

The proof proceeds by induction. The base case \\(n = 0\\) gives \\((x+y)^0 = 1 = \binom{0}{0}x^0y^0\\). For the inductive step, we expand \\((x+y)^{n+1} = (x+y)(x+y)^n\\), distribute, and apply Pascal's identity \\(\binom{n}{k} + \binom{n}{k-1} = \binom{n+1}{k}\\) to combine terms.

As concrete examples: \\((x+1)^2 = x^2 + 2x + 1\\) and \\((x+1)^3 = x^3 + 3x^2 + 3x + 1\\). **QED**

**Lean Formalization**

Mathlib provides `add_pow`, which establishes the binomial theorem via the same inductive argument. Our `binomial_theorem` reformulates this in the standard notation. The specific cases `binomial_two` and `binomial_three` are verified by the `ring` tactic, which normalizes polynomial expressions.

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:binomial_theorem}}
```

## Fibonacci Numbers

**Traditional Proof**

**Definition.** The [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence): \\(F_0 = 0\\), \\(F_1 = 1\\), \\(F_{n+2} = F_{n+1} + F_n\\). The sequence that appears everywhere: rabbit populations, sunflower spirals, financial markets, bad interview questions.

**Theorem.** \\(\sum_{k=0}^{n-1} F_k + 1 = F_{n+1}\\)

**Base case** (\\(n = 0\\)): The empty sum equals 0, and \\(0 + 1 = 1 = F_1\\).

**Inductive step:** Assume \\(\sum_{k=0}^{n-1} F_k + 1 = F_{n+1}\\). Then:
\\[\sum_{k=0}^{n} F_k + 1 = \left(\sum_{k=0}^{n-1} F_k + 1\right) + F_n = F_{n+1} + F_n = F_{n+2}\\]
which equals \\(F_{(n+1)+1}\\). **QED**

**Lean Formalization**

The Lean proof follows the same structure. The definition `fib` uses pattern matching on 0, 1, and \\(n+2\\). The theorem `fib_sum` proceeds by induction: the base case simplifies directly, and the inductive step uses `Finset.sum_range_succ` to split off the last term, applies the inductive hypothesis, then uses the recurrence relation.

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:fibonacci}}
```

## The Pigeonhole Principle

**Traditional Proof**

**Theorem ([Pigeonhole Principle](https://en.wikipedia.org/wiki/Pigeonhole_principle)).** Let \\(f : A \to B\\) be a function between finite sets with \\(|A| > |B|\\). Then \\(f\\) is not injective: there exist distinct \\(a_1, a_2 \in A\\) with \\(f(a_1) = f(a_2)\\).

Suppose for contradiction that \\(f\\) is injective, meaning \\(f(a_1) = f(a_2)\\) implies \\(a_1 = a_2\\). An injective function from \\(A\\) to \\(B\\) implies \\(|A| \leq |B|\\), since distinct elements of \\(A\\) map to distinct elements of \\(B\\). But we assumed \\(|A| > |B|\\), a contradiction. Therefore \\(f\\) is not injective, so there exist distinct \\(a_1 \neq a_2\\) with \\(f(a_1) = f(a_2)\\). **QED**

**Corollary.** In any group of \\(n > 365\\) people, at least two share a birthday.

**Lean Formalization**

The Lean proof mirrors this argument precisely. It assumes by contradiction (`by_contra hinj`) that no two distinct elements collide. The `push_neg` tactic transforms this into: for all \\(a_1, a_2\\), if \\(a_1 \neq a_2\\) then \\(f(a_1) \neq f(a_2)\\). This is exactly injectivity. We then apply `Fintype.card_le_of_injective`, which states that an injective function implies \\(|A| \leq |B|\\), contradicting our hypothesis \\(|B| < |A|\\).

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:pigeonhole}}
```

## Divisibility

**Traditional Proof**

**Definition.** We write \\(a \mid b\\) if there exists \\(k\\) such that \\(b = ak\\).

**Theorem.** Divisibility satisfies:
1. \\(a \mid a\\) (reflexivity)
2. \\(a \mid b \land b \mid c \Rightarrow a \mid c\\) (transitivity)
3. \\(a \mid b \land a \mid c \Rightarrow a \mid (b + c)\\)
4. \\(a \mid b \Rightarrow a \mid bc\\)

**Proof.** (1) \\(a = a \cdot 1\\), so take \\(k = 1\\).

(2) If \\(b = ak\\) and \\(c = bm\\), then \\(c = (ak)m = a(km)\\).

(3) If \\(b = ak\\) and \\(c = am\\), then \\(b + c = ak + am = a(k + m)\\).

(4) If \\(b = ak\\), then \\(bc = (ak)c = a(kc)\\). **QED**

**Lean Formalization**

Each Lean proof constructs the witness \\(k\\) explicitly. The `obtain` tactic extracts the witnesses from divisibility hypotheses, then we provide the new witness as an anonymous constructor `⟨_, _⟩`. The equality proofs use `rw` to substitute and `mul_assoc` or `mul_add` to rearrange.

```lean
{{#include ../../src/ZeroToQED/Mathematics.lean:divisibility_examples}}
```

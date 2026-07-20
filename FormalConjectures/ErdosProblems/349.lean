/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-! # Erdős Problem 349

*Reference:* [erdosproblems.com/349](https://www.erdosproblems.com/349)
-/

namespace Erdos349

open Set Filter Real Nat Function


/--
This defines the core property of the problem: For what values of $t,\alpha \in (0,\infty)$
is the sequence $\lfloor t\alpha^n\rfloor$ complete?
-/
def IsGoodPair (t α : ℝ) : Prop :=
  IsAddComplete (range (fun n ↦ ⌊t * α ^ n⌋))

/--
For what values of $t,\alpha \in (0,\infty)$ is the sequence $\lfloor t\alpha^n\rfloor$ complete
(that is, all sufficiently large integers are the sum of distinct integers of the form $\lfloor t\alpha^n\rfloor$)?
-/
@[category research open, AMS 11]
theorem erdos_349 :
    {(t, α) | 0 < t ∧ 0 < α ∧ IsGoodPair t α} = answer(sorry) := by
  sorry

/--
It seems likely that the sequence is complete for all
for all $t>0$ and all $1 < \alpha < \frac{1+\sqrt{5}}{2}$.
-/
@[category research open, AMS 11]
theorem complete_for_alpha_in_Ioo_one_to_goldenRatio (t α : ℝ) (ht : 0 < t)
    (hα : α ∈ Set.Ioo 1 ((1 + √5) / 2)) : IsGoodPair t α := by
  sorry

/--
For any $k$ there exists some $t_k\in (0,1)$ such that the set of $\alpha$
such that the sequence $\lfloor t_k\alpha^n\rfloor$ is complete consists of at least $k$
disjoint line segments.
-/
@[category research solved, AMS 11]
theorem exists_t_for_k_disjoint_segments (k : ℕ) :
    ∃ t ∈ Ioo 0 1, ∃ (ι : Type), k ≤ (Set.univ : Set ι).encard ∧ ∃ I : ι → Set ℝ,
      (∀ i, 2 ≤ (I i).encard ∧ (I i).Nonempty ∧ IsConnected (I i)) ∧
      Pairwise (Disjoint on I) ∧ (⋃ i, I i) ⊆ {α | α > 0 ∧ IsGoodPair t α} := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are odd infinitely
often and even infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_349.variants.floor_3_halves_odd :
    answer(sorry) ↔ {n | Odd ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are even infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_349.variants.floor_3_halves_even :
    answer(sorry) ↔ {n | Even ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/-- For $\alpha > 2$ and any $t > 0$, the sequence $\lfloor t\alpha^n\rfloor$ is not additively
complete; equivalently $(t, \alpha)$ is not a "good pair". A partial result on the open Erdős
Problem 349: it complements `complete_for_alpha_in_Ioo_one_to_goldenRatio`.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/23c629bc2347864782ce88f957a64d6567b978a1/FormalConjectures/ErdosProblems/349.lean#L87"]
theorem alpha_gt_two_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα : 2 < α) : ¬ IsGoodPair t α := by
  sorry

/-- For $0 < \alpha \le 1$ and any $t > 0$, $(t, \alpha)$ is not a good pair: every term
$\lfloor t\alpha^n\rfloor$ lies in the finite interval $[0, \lfloor t\rfloor]$ (since
$\alpha^n \le 1$), so every subset sum is bounded by the constant $\sum_{i \in [0,\lfloor t\rfloor]} i$,
and no large integer can be a subset sum. A partial result on the open Erdős Problem 349,
complementing the $2 < \alpha$ and integer-coefficient cases. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem alpha_le_one_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ¬ IsGoodPair t α := by
  sorry

/-- **Binary expansion.** Every natural number $k$ is a sum of distinct powers of two: there is
a finite set $E$ of exponents with $k = \sum_{i \in E} 2^i$. Proved by strong induction:
subtract the largest power $2^m \le k$, recurse on the remainder. A textbook-level building
block for `one_two_isGoodPair` below; it says nothing about `IsGoodPair` itself. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem exists_finset_sum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := by
  sorry

/-- **The pair $(1, 2)$ is good.** The powers of two $\lfloor 1\cdot 2^n\rfloor = 2^n$ form an
additively complete set: every $k \ge 1$ is a finite sum of distinct powers of two. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem one_two_isGoodPair : IsGoodPair 1 2 := by
  sorry

/-- **The dyadic fiber at $\alpha = 2$.** For every $k$, the pair $(1/2^k, 2)$ is good: the
sequence $\lfloor 2^n / 2^k\rfloor$ is additively complete because at index $n = m + k$ it equals
the exact power $2^m$, so its range contains all powers of two, which already form an additively
complete set. Uses monotonicity `IsAddComplete.mono`. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem dyadic_two_isGoodPair (k : ℕ) : IsGoodPair (1 / 2 ^ k) 2 := by
  sorry

/-- **Integer leading coefficient $t \ge 2$ blocks completeness.** For every integer base
$\alpha$, the pair $(t, \alpha)$ with integer $t \ge 2$ is not good: $\lfloor t\alpha^n\rfloor =
t\alpha^n$ is a multiple of $t$, so every subset sum is too, but two consecutive large integers
cannot both be multiples of $t$. Generalizes the parity obstruction ($t = 2$). A partial result
on Erdős Problem 349. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem int_coeff_ge_two_not_isGoodPair (t : ℤ) (ht : 2 ≤ t) (α : ℤ) :
    ¬ IsGoodPair (t : ℝ) (α : ℝ) := by
  sorry

/-- **Erdős Problem 349, complete characterization on positive integer pairs.** For integers
$t \ge 1$, $\alpha \ge 1$, the pair $(t, \alpha)$ is good (i.e. $\lfloor t\alpha^n\rfloor$ is
additively complete) iff $(t, \alpha) = (1, 2)$. Assembles the four partial results: $(1,2)$ is
good, $\alpha \le 1$ fails, $2 < \alpha$ fails (`alpha_gt_two_not_isGoodPair`), and integer
$t \ge 2$ fails. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-integer-characterization-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem integer_isGoodPair_iff (t α : ℤ) (ht : 1 ≤ t) (hα : 1 ≤ α) :
    IsGoodPair (t : ℝ) (α : ℝ) ↔ t = 1 ∧ α = 2 := by
  sorry

/-- **The pair $(3/2, 2)$ is NOT good.** The negative companion of `dyadic_two_isGoodPair`:
while every dyadic coefficient $1/2^k$ gives a good pair at $\alpha = 2$, the non-dyadic rational
$t = 3/2$ does not. The sequence $\lfloor (3/2)\cdot 2^n\rfloor = 1, 3, 6, 12, 24, \ldots$ is not
additively complete because every term but the first $\lfloor 3/2\rfloor = 1$ is a multiple of
$3$ (namely $\lfloor (3/2)\cdot 2^{n+1}\rfloor = 3\cdot 2^n$), so every subset sum is
$\equiv 0$ or $1 \pmod 3$; the infinitely many integers $\equiv 2 \pmod 3$ are never reached.
A partial result on Erdős Problem 349 in the same divisibility family as
`int_coeff_ge_two_not_isGoodPair` (here the modulus is $3$). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-three-halves-fiber-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem three_halves_two_not_isGoodPair : ¬ IsGoodPair (3 / 2) 2 := by
  sorry

/-- A set $A \subseteq \mathbb{Z}$ is *entirely additively complete* if **every** positive integer
is a finite subset sum of $A$ (van Doorn's "entirely complete": $P(A) = \mathbb{N}_{\ge 1}$).
Strictly stronger than `IsAddComplete`, which only requires all *sufficiently large* integers.

This is a problem-local definition; it could be promoted to
`FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean` (next to `IsAddComplete`) if
the maintainers prefer it to live there. -/
def IsEntirelyAddComplete (A : Set ℤ) : Prop :=
  ∀ k : ℤ, 1 ≤ k → k ∈ subsetSums A

/-- **Glue.** Entire completeness implies (eventual) completeness: if every $k \ge 1$ is a subset
sum, then in particular all sufficiently large $k$ are. Textbook-level: an immediate consequence
of the definitions, not itself a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem isEntirelyAddComplete_imp_isAddComplete {A : Set ℤ}
    (h : IsEntirelyAddComplete A) : IsAddComplete A :=
  Filter.eventually_atTop.mpr ⟨1, fun k hk => h k hk⟩

/-- **Abstract single-gap criterion.** For a monotone, nonnegative integer sequence $a$, a single
gap $\sum_{k < r+1} a_k < m < a_{r+1}$ with $m \ge 1$ already shows that $m$ is not a subset sum,
hence the range of $a$ is not entirely additively complete.

This is the pure-$\mathbb{Z}$ core of `alpha_gt_two_not_isGoodPair`'s
`by_cases ∃ b ∈ B, a (r+1) ≤ b` case-split, with $m$ *given* rather than constructed via
`Tendsto` (strictly easier, and enough for the band $5/3 \le \alpha < 2$ below). A textbook-level
combinatorial fact about monotone integer sequences, phrased abstractly (no $t, \alpha$); the
research content of Erdős Problem 349 is in its application below. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-entire-gap-criterion-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem entire_gap_not_complete (a : ℕ → ℤ) (hmono : Monotone a) (hnn : ∀ n, 0 ≤ a n)
    (r : ℕ) (m : ℤ) (hm : 1 ≤ m)
    (hlo : (∑ k ∈ Finset.range (r + 1), a k) < m) (hhi : m < a (r + 1)) :
    ¬ IsEntirelyAddComplete (Set.range a) := by
  sorry

/-- The $0$-th term of $\lfloor t\alpha^n\rfloor$ is $\lfloor t\rfloor$ (since $\alpha^0 = 1$).
Textbook-level: a one-line simplification, not a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_zero (t α : ℝ) : ⌊t * α ^ (0 : ℕ)⌋ = ⌊t⌋ := by
  simp [pow_zero, mul_one]

/-- The $1$-st term of $\lfloor t\alpha^n\rfloor$ is $\lfloor t\alpha\rfloor$. Textbook-level:
a one-line simplification, not a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_one (t α : ℝ) : ⌊t * α ^ (1 : ℕ)⌋ = ⌊t * α⌋ := by
  simp [pow_one]

/-- $n \mapsto \lfloor t\alpha^n\rfloor$ is monotone when $0 \le t$ and $1 \le \alpha$.
Textbook-level: elementary monotonicity of `Int.floor` composed with a monotone power. -/
@[category textbook, AMS 11]
theorem floorSeq_monotone (t α : ℝ) (ht : 0 ≤ t) (hα : 1 ≤ α) :
    Monotone (fun n => ⌊t * α ^ n⌋) := by
  intro n m hnm
  simp only
  apply Int.floor_le_floor
  apply mul_le_mul_of_nonneg_left _ ht
  exact pow_le_pow_right₀ hα hnm

/-- $n \mapsto \lfloor t\alpha^n\rfloor$ is nonnegative when $0 \le t$ and $0 \le \alpha$.
Textbook-level: an immediate `positivity` consequence, not a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_nonneg (t α : ℝ) (ht : 0 ≤ t) (hα : 0 ≤ α) (n : ℕ) :
    0 ≤ (fun n => ⌊t * α ^ n⌋) n := by
  simp only
  rw [Int.floor_nonneg]
  positivity

/-- **Application inside the band $5/3 \le \alpha < 2$.** For $t \ge 3$ and $5/3 \le \alpha < 2$,
the sequence $\lfloor t\alpha^n\rfloor$ is NOT entirely additively complete: the very first gap
$\lfloor t\rfloor < \lfloor t\rfloor+1 < \lfloor t\alpha\rfloor$ already misses the positive
integer $\lfloor t\rfloor+1$.

This is the $r = 0$, $m = \lfloor t\rfloor + 1$ instance of `entire_gap_not_complete`. The gap
inequality comes from $t\alpha \ge t\cdot(5/3) = t + 2t/3 \ge t + 2 \ge \lfloor t\rfloor + 2$.
The constant $5/3$ (not $\varphi$) is the sharp clean threshold uniform in $t \ge 3$: at
$\alpha = \varphi$, $t = 3$ gives $\lfloor 3\varphi\rfloor = 4 = \lfloor t\rfloor+1$, so the first
gap closes. This is *entire* (not eventual) incompleteness; the gap need not recur for
$\varphi \le \alpha < 2$, where Erdős Problem 349 stays open. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/erdos-349-entire-gap-criterion-proof/FormalConjectures/ErdosProblems/349.lean"]
theorem floorSeq_not_entirelyComplete_of_le_two
    (t α : ℝ) (ht : 3 ≤ t) (hα : 5 / 3 ≤ α) (hα2 : α < 2) :
    ¬ IsEntirelyAddComplete (Set.range (fun n => ⌊t * α ^ n⌋)) := by
  sorry

/-- **Abstract doubling criterion** (van Doorn's Lemma 3, applied with base phase length $r = 0$).

Let $a : \mathbb{N} \to \mathbb{Z}$ be a monotone integer sequence with $a_0 = 1$, satisfying the
doubling bound $a_{n+1} \le 2 a_n$ for every $n$, and unbounded ($\forall M,\ \exists n,\ M \le
a_n$). Then every positive integer is a finite subset sum of distinct values of $a$, i.e. the
range of $a$ is entirely additively complete.

A textbook-level combinatorial fact about monotone integer sequences (no $t, \alpha$); its
application to $a_n = \lfloor \alpha^n \rfloor$ below (`isGoodPair_one_alpha_of_lt_three_halves`)
is the research content of Erdős Problem 349.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/6e869b32eccf185e6c57f3f5cae571a8ce1bb4fb/FormalConjectures/ErdosProblems/349.lean#L708"]
theorem entirely_complete_of_doubling (a : ℕ → ℤ)
    (ha0 : a 0 = 1)
    (hmono : Monotone a)
    (hdouble : ∀ n, a (n + 1) ≤ 2 * a n)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n) :
    IsEntirelyAddComplete (Set.range a) := by
  sorry

/-- **Doubling bound for the floor of a power sequence.** For $1 < \alpha < 3/2$ and any
$n \ge 0$, $\lfloor \alpha^{n+1} \rfloor \le 2 \lfloor \alpha^n \rfloor$.

Proof: $\alpha^{n+1} = \alpha \cdot \alpha^n < \tfrac{3}{2}\alpha^n \le \tfrac{3}{2}(\lfloor
\alpha^n\rfloor + 1) \le 2\lfloor \alpha^n\rfloor + 1$, using $\lfloor \alpha^n\rfloor \ge 1$
(since $\alpha > 1$). A textbook-level floor/inequality fact. -/
@[category textbook, AMS 11]
theorem floor_pow_succ_le_two_mul_floor_pow (α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (n : ℕ) :
    ⌊α ^ (n + 1)⌋ ≤ 2 * ⌊α ^ n⌋ := by
  have hpos : (0 : ℝ) < α ^ n := by positivity
  have hone : (1 : ℝ) ≤ α ^ n := one_le_pow₀ hα_lo.le
  have hm1 : (1 : ℤ) ≤ ⌊α ^ n⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hflo : (↑(⌊α ^ n⌋) : ℝ) ≤ α ^ n := Int.floor_le _
  have hfle : α ^ n - 1 < (↑(⌊α ^ n⌋) : ℝ) := by linarith [Int.sub_one_lt_floor (α ^ n)]
  rw [Int.floor_le_iff]
  push_cast
  have hsucc : α ^ (n + 1) = α * α ^ n := by ring
  rw [hsucc]
  have hm1r : (1 : ℝ) ≤ (↑(⌊α ^ n⌋) : ℝ) := by exact_mod_cast hm1
  nlinarith [mul_pos (by linarith : (0 : ℝ) < α) hpos, hflo, hfle, hm1r]

/-- **Erdős Problem 349, Proposition 6 (van Doorn), "if" direction, case $t = 1$.**

For $1 < \alpha < 3/2$, the pair $(1, \alpha)$ is good: the sequence $\lfloor \alpha^n\rfloor$ is
additively complete (in fact *entirely* additively complete — every $k \ge 1$ is a finite subset
sum of distinct terms $\lfloor \alpha^n\rfloor$).

A **partial result** on the open Erdős Problem 349: it complements
`floorSeq_not_entirelyComplete_of_le_two` (which rules out $5/3 \le \alpha < 2$ for $t \ge 3$) and
the integer-pair characterization `integer_isGoodPair_iff`. Proof: instantiate
`entirely_complete_of_doubling` with $a_n = \lfloor \alpha^n\rfloor$, using
`floor_pow_succ_le_two_mul_floor_pow` for the doubling bound.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/6e869b32eccf185e6c57f3f5cae571a8ce1bb4fb/FormalConjectures/ErdosProblems/349.lean#L864"]
theorem isGoodPair_one_alpha_of_lt_three_halves (α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2) :
    IsGoodPair 1 α := by
  sorry

/-- **First-term value for $1 \le t < 2$.** The $0$-th term of the floor sequence is
$\lfloor t\alpha^0\rfloor = \lfloor t\rfloor = 1$. Textbook-level: an immediate consequence of
`floorSeq_zero` and `Int.floor_eq_iff`, not itself a partial result on Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floorSeq_zero_eq_one_of_lt_two (t α : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    ⌊t * α ^ (0 : ℕ)⌋ = 1 := by
  simp only [pow_zero, mul_one]
  rw [Int.floor_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- **Doubling bound for a general floor power sequence.** For $1 < \alpha < 3/2$, $1 \le t$, and
any $n \ge 0$, $\lfloor t\alpha^{n+1}\rfloor \le 2\lfloor t\alpha^n\rfloor$.

Generalizes `floor_pow_succ_le_two_mul_floor_pow` (the $t = 1$ case) to every $t \ge 1$: the
argument only needs $\lfloor t\alpha^n\rfloor \ge 1$, which now comes from $t \ge 1$ rather than
from $\alpha > 1$ alone. Textbook-level floor/inequality fact, not itself a partial result on
Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem floor_mul_pow_succ_le_two_mul (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (n : ℕ) :
    ⌊t * α ^ (n + 1)⌋ ≤ 2 * ⌊t * α ^ n⌋ := by
  have hpos : (0 : ℝ) < α ^ n := by positivity
  have hone : (1 : ℝ) ≤ α ^ n := one_le_pow₀ hα_lo.le
  have htpow : (1 : ℝ) ≤ t * α ^ n := by nlinarith [ht1, hone]
  have hm1 : (1 : ℤ) ≤ ⌊t * α ^ n⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hflo : (↑(⌊t * α ^ n⌋) : ℝ) ≤ t * α ^ n := Int.floor_le _
  have hfle : (t * α ^ n) - 1 < (↑(⌊t * α ^ n⌋) : ℝ) := by
    linarith [Int.sub_one_lt_floor (t * α ^ n)]
  rw [Int.floor_le_iff]
  push_cast
  have hsucc : t * α ^ (n + 1) = α * (t * α ^ n) := by ring
  rw [hsucc]
  have hm1r : (1 : ℝ) ≤ (↑(⌊t * α ^ n⌋) : ℝ) := by exact_mod_cast hm1
  nlinarith [mul_pos (by linarith : (0 : ℝ) < α) (by nlinarith [htpow] : (0 : ℝ) < t * α ^ n),
    hflo, hfle, hm1r]

/-- **Erdős Problem 349, sharp entire completeness for $1 \le t < 2$ on the strip
$1 < \alpha < 3/2$.**

The sequence $\lfloor t\alpha^n\rfloor$ is *entirely* additively complete: every positive
integer $k \ge 1$ is a finite subset sum of distinct terms.

A **partial result** on the open Erdős Problem 349 and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to $\alpha < 3/2$, entire sense, and
$t < 2$). Sharpens `isGoodPair_one_alpha_of_lt_three_halves` (its $t = 1$ special case) by taking
$t < 2$ as a direct hypothesis instead of deriving it from $t\alpha < 2$: the doubling bound
`floor_mul_pow_succ_le_two_mul` already holds for every $1 \le t$ on this strip, so the widening
is free. E.g. $(t, \alpha) = (1.7, 1.4)$ has $t\alpha = 2.38 > 2$ yet is covered here.

Proof: instantiate `entirely_complete_of_doubling` with $a_n = \lfloor t\alpha^n\rfloor$, using
`floorSeq_zero_eq_one_of_lt_two` for $a_0 = 1$ and `floor_mul_pow_succ_le_two_mul` for the
doubling bound.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L949"]
theorem isEntirelyAddComplete_of_one_le_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  sorry

/-- **Erdős Problem 349, good pair for $1 \le t < 2$ on the strip $1 < \alpha < 3/2$.**

Corollary of `isEntirelyAddComplete_of_one_le_lt_two`, lifted from entire to eventual
completeness via `isEntirelyAddComplete_imp_isAddComplete`. A partial result on the named open
conjecture `complete_for_alpha_in_Ioo_one_to_goldenRatio`, restricted to $\alpha < 3/2$ and
$t < 2$.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on a linked theorem). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L983"]
theorem isGoodPair_of_one_le_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    IsGoodPair t α := by
  sorry

/-- **Erdős Problem 349, not entirely complete for $2 \le t$.**

For $2 \le t$ and $1 \le \alpha$, every term $\lfloor t\alpha^n\rfloor \ge \lfloor t\rfloor \ge 2$,
so every subset sum of the range is $0$ (empty subset) or $\ge 2$ (nonempty subset of values each
$\ge 2$): the value $1$ is never a subset sum, so the range is not entirely additively complete.

This is the DeepMind-faithful "only if" direction of the sharp threshold ($t \ge 2$), and it
matters to state precisely: the superficially plausible stronger claim "$t\alpha \ge 2 \Rightarrow$
not entirely complete" is FALSE under this repository's $n = 0$ indexing — e.g.
$(t, \alpha) = (3/2, 7/5)$ has $t\alpha = 2.1 \ge 2$ yet IS entirely complete, because
$a_0 = \lfloor t\rfloor = 1$ already saves it. The correct sharp threshold is on $t$ alone, not on
$t\alpha$; that is exactly `entirelyComplete_floorSeq_iff_lt_two` below.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L1006"]
theorem not_entirelyComplete_of_two_le (t α : ℝ) (ht : 2 ≤ t) (hα : 1 ≤ α) :
    ¬ IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  sorry

/-- **Erdős Problem 349, sharp entire characterization on the strip $1 < \alpha < 3/2$.**

For $1 \le t$ and $1 < \alpha < 3/2$:
$$\text{IsEntirelyAddComplete}\big(\operatorname{range}(n \mapsto \lfloor t\alpha^n\rfloor)\big)
\iff t < 2.$$
Assembles `isEntirelyAddComplete_of_one_le_lt_two` and `not_entirelyComplete_of_two_le`, split on
$t < 2 \lor 2 \le t$. The threshold is exactly $t = 2$: that is where the front term $a_0$ jumps
from $1$ to $2$ and blocks the value $1$. A partial result on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio`, sharp on the sub-strip $1 < \alpha < 3/2$ (in the
entire sense).

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on two linked theorems). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/fc02fb6d4045478b070742b7d04d09ceed561183/FormalConjectures/ErdosProblems/349.lean#L1041"]
theorem entirelyComplete_floorSeq_iff_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) :
    IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) ↔ t < 2 := by
  sorry


/-- **Distinct-value prefix sum.** `C a N` is the sum of the *distinct* values among
`a 0, ..., a (N - 1)`, i.e. the "running reachable total" for subset sums over the SET
`Set.range a` (duplicate values counted once, unlike a plain prefix sum). Auxiliary to
`floorSeq_brown_all` / `eventuallyComplete_of_brown_of_base_window` below. -/
noncomputable def C (a : ℕ → ℤ) (N : ℕ) : ℤ := ∑ x ∈ (Finset.range N).image a, x

/-- **Unboundedness of the floor sequence.** For $t > 0$ and $\alpha > 1$, the sequence
$n \mapsto \lfloor t\alpha^n\rfloor$ is unbounded above: for every $M$ there is an $n$ with
$M \le \lfloor t\alpha^n\rfloor$. Textbook-level consequence of $\alpha^n \to \infty$, not itself
a partial result on Erdős Problem 349; a building block for `isGoodPair_of_pos_of_lt_two` below. -/
@[category textbook, AMS 11]
theorem floorSeq_unbounded (t α : ℝ) (ht : 0 < t) (hα1 : 1 < α) :
    ∀ M : ℤ, ∃ n : ℕ, M ≤ ⌊t * α ^ n⌋ := by
  intro M
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((M : ℝ) + 1) / t) hα1
  refine ⟨n, Int.le_floor.mpr ?_⟩
  have : (M : ℝ) + 1 < t * α ^ n := by
    rw [div_lt_iff₀ ht] at hn; linarith
  linarith

/-- **Distinct-value prefix sum, toolbox: the empty prefix.** $C\ a\ 0 = 0$. Textbook-level;
shared with `entirely_complete_of_doubling` above (same `C`), reused here for the small-$t$
eventual-completeness engine. -/
@[category textbook, AMS 11]
theorem C_zero (a : ℕ → ℤ) : C a 0 = 0 := by simp [C]

/-- **Distinct-value prefix sum, toolbox: the one-term prefix.** $C\ a\ 1 = a_0$.
Textbook-level. -/
@[category textbook, AMS 11]
theorem C_one (a : ℕ → ℤ) : C a 1 = a 0 := by simp [C]

/-- **Distinct-value prefix sum, toolbox: duplicates.** If $a_n$ already occurred among
$a_0, \ldots, a_{n-1}$, then $C\ a\ (n+1) = C\ a\ n$. Textbook-level. -/
@[category textbook, AMS 11]
theorem C_succ_of_mem (a : ℕ → ℤ) {n : ℕ} (h : a n ∈ (Finset.range n).image a) :
    C a (n + 1) = C a n := by
  have himg : (Finset.range (n + 1)).image a = (Finset.range n).image a := by
    rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr h]
  simp only [C, himg]

/-- **Distinct-value prefix sum, toolbox: genuinely new values.** If $a_n$ did not occur among
$a_0, \ldots, a_{n-1}$, then $C\ a\ (n+1) = a_n + C\ a\ n$. Textbook-level. -/
@[category textbook, AMS 11]
theorem C_succ_of_notMem (a : ℕ → ℤ) {n : ℕ} (h : a n ∉ (Finset.range n).image a) :
    C a (n + 1) = a n + C a n := by
  have himg : (Finset.range (n + 1)).image a = insert (a n) ((Finset.range n).image a) := by
    rw [Finset.range_add_one, Finset.image_insert]
  simp only [C, himg, Finset.sum_insert h]

/-- **Distinct-value prefix sum, toolbox: strict novelty.** A value strictly larger than all of
its predecessors has not occurred before. Textbook-level. -/
@[category textbook, AMS 11]
theorem notMem_image_of_forall_lt (a : ℕ → ℤ) {n : ℕ} (h : ∀ j, j < n → a j < a n) :
    a n ∉ (Finset.range n).image a := by
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨j, hj, hja⟩ := hmem
  have := h j (Finset.mem_range.mp hj)
  omega

/-- **Distinct-value prefix sum, toolbox: domination.** Each nonnegative term is dominated by
the prefix sum containing it: $a_n \le C\ a\ (n+1)$. Textbook-level. -/
@[category textbook, AMS 11]
theorem le_C_succ (a : ℕ → ℤ) (hnn : ∀ n, 0 ≤ a n) (n : ℕ) : a n ≤ C a (n + 1) := by
  have hmem : a n ∈ (Finset.range (n + 1)).image a := by
    rw [Finset.mem_image]; exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
  have : a n ≤ ∑ x ∈ (Finset.range (n + 1)).image a, x := by
    apply Finset.single_le_sum (f := id) _ hmem
    intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
  simpa [C] using this

/-- **Abstract eventual-completeness engine from a base window.** Let $a : \mathbb{N} \to
\mathbb{Z}$ be nonnegative, monotone and unbounded, and suppose there are a rank $N_0$ and a
threshold $L$ such that: (i) *base window* — every $k$ with $L \le k \le C\ a\ N_0$ is already a
subset sum of $\{a_0, \ldots, a_{N_0 - 1}\}$; (ii) *shifted Brown margin* — $a_n + L \le 1 + C\ a\
n$ for every $n \ge N_0$. Then $\operatorname{range} a$ is additively complete in the eventual
sense (in fact every $k \ge L$ is a finite subset sum).

Textbook-level: a purely combinatorial merge-induction on monotone integer sequences, phrased
abstractly (no $t, \alpha$); the research content of Erdős Problem 349 is in its instantiation
`isGoodPair_of_pos_of_lt_two` below. Analogous in spirit to `entirely_complete_of_doubling` above,
but concluding *eventual* (not *entire*) completeness from a *base-window* hypothesis instead of a
doubling bound — the two are independent engines for different regimes.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1134"]
theorem eventuallyComplete_of_brown_of_base_window (a : ℕ → ℤ)
    (hnn : ∀ n, 0 ≤ a n)
    (hmono : Monotone a)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n)
    (N₀ : ℕ) (L : ℤ)
    (hbase : ∀ k : ℤ, L ≤ k → k ≤ C a N₀ →
      k ∈ subsetSums (((Finset.range N₀).image a : Finset ℤ) : Set ℤ))
    (hbrown : ∀ n : ℕ, N₀ ≤ n → a n + L ≤ 1 + C a n) :
    IsAddComplete (Set.range a) := by
  sorry

/-- **Universal Brown condition for $0 < t < 2$ on the strip $1 < \alpha < 3/2$.** The floor
sequence $a_n = \lfloor t\alpha^n\rfloor$ satisfies $a_n \le 1 + C(n)$ for **every** $n$ (not
merely eventually), where $C(n)$ sums the distinct values among $a_0, \ldots, a_{n-1}$. This is
the `hbrown` hypothesis of `eventuallyComplete_of_brown_of_base_window` instantiated with the
witnesses $N_0 = 0$, $L = 0$: since $C\ a\ 0 = 0$, no "eventually" is available and the bound must
hold from $n = 0$ on.

Proof sketch (two phases, split at the first index $n_0$ where the sequence jumps by at least
$2$): while all increments are $\le 1$ (Phase 1), $t < 2$ gives $a_0 \le 1$ so the values form an
initial segment and $2C(n+1) \ge a_n(a_n + 1)$ grows quadratically, giving the Brown condition
directly. If a jump $a_{n_0 + 1} \ge a_{n_0} + 2$ occurs (Phase 2), it forces
$t\alpha^{n_0}(\alpha - 1) > 1$, hence $t\alpha^{n_0} > 2$ (as $\alpha - 1 < 1/2$ from
$\alpha < 3/2$), hence $a_{n_0} \ge 2$; the Phase 1 quadratic stock then starts the linear
invariant $a_n + 1 \le 2C(n)$, which is self-propagating (all terms distinct past $n_0$, so
$C(n+1) = a_n + C(n)$) and carries the Brown condition forward:
$2a_{n+1} \le 3a_n + 2 < 2(1 + C(n+1))$.

A **partial result** on the open Erdős Problem 349 and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to $\alpha < 3/2$): this is the new
mathematical content behind `isGoodPair_of_pos_of_lt_two` below.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1244"]
theorem floorSeq_brown_all (t α : ℝ) (ht : 0 < t) (ht2 : t < 2) (hα1 : 1 < α) (hα2 : α < 3 / 2) :
    ∀ n : ℕ, ⌊t * α ^ n⌋ ≤ 1 + C (fun m : ℕ => ⌊t * α ^ m⌋) n := by
  sorry

/-- **Erdős Problem 349, eventual completeness for $0 < t < 2$ on the strip $1 < \alpha < 3/2$.**

The pair $(t, \alpha)$ is good, i.e. $\lfloor t\alpha^n\rfloor$ is additively complete in the
**eventual** sense. Instantiates `eventuallyComplete_of_brown_of_base_window` with the explicit
base window $N_0 = 0$, $L = 0$: `hbase` is trivial ($C\ a\ 0 = 0$, so the only admissible $k$ is
$0 = \sum_{i \in \emptyset} i$) and `hbrown` is `floorSeq_brown_all`.

This closes the sub-case $0 < t < 1$ left out of scope by `isGoodPair_of_one_le_lt_two` /
`entirelyComplete_floorSeq_iff_lt_two` above (which need $1 \le t$): for $0 < t < 1$,
$a_0 = \lfloor t\rfloor = 0$ and the sequence begins with a prefix of zeros, so *entire*
completeness is not even the right notion there — only *eventual* completeness, which is exactly
`IsGoodPair`. Together with `isGoodPair_of_one_le_lt_two` this gives eventual completeness for
**all** $0 < t < 2$ on the strip, strictly beyond the *entire*-completeness threshold $t < 2$
proved there: e.g. $(t, \alpha) = (7/4, 7/5)$ has $t\alpha = 2.45 > 2$, outside van Doorn's
"easy" $t\alpha < 2$ range, yet is covered here.

A **partial result** on the open Erdős Problem 349 and on the named open conjecture
`complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to $\alpha < 3/2$, eventual sense,
$t < 2$); nothing is claimed for $t \ge 2$ on this route, and no "only if" direction is claimed.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on two linked theorems). -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1436"]
theorem isGoodPair_of_pos_of_lt_two (t α : ℝ) (ht : 0 < t) (ht2 : t < 2)
    (hα1 : 1 < α) (hα2 : α < 3 / 2) : IsGoodPair t α := by
  sorry

/-- **Erdős Problem 349, eventual completeness for $0 < t < 1$ on the strip $1 < \alpha < 3/2$.**

Corollary of `isGoodPair_of_pos_of_lt_two`, specialized to $t < 1$: the sub-case left entirely out
of scope by the *entire*-completeness results above (`isGoodPair_of_one_le_lt_two`,
`entirelyComplete_floorSeq_iff_lt_two`), which all require $1 \le t$. A **partial result** on the
open Erdős Problem 349 and on `complete_for_alpha_in_Ioo_one_to_goldenRatio` (restricted to
$\alpha < 3/2$, eventual sense, $t < 1$).

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it depends
on a linked theorem. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/0ed837c90387a146fc88a23172074d01533f94ee/FormalConjectures/ErdosProblems/349.lean#L1460"]
theorem isGoodPair_of_pos_of_lt_one (t α : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hα1 : 1 < α) (hα2 : α < 3 / 2) : IsGoodPair t α := by
  sorry

/- ## Good pairs deep in the open zone `1 < α < 3/2` for `t ≥ 2`

The results below extend the partial characterization of Erdős Problem 349 with 21 concrete good
pairs $(t, \alpha)$ satisfying $t \ge 2$, reaching well beyond the strip $\alpha \le 1 +
1/(2\lfloor t\rfloor + 2)$ already covered by `isGoodPair_of_pos_of_lt_two` above (which only
handles $t < 2$).

The engine is a **reduction theorem**, `isGoodPair_of_run`: the whole (still open) band $t \ge
2$, $1 < \alpha < 3/2$ collapses to a single finite combinatorial certificate — a rank $N_0$ at
which the floor sequence produces a *new* value whose predecessors' subset sums already cover a
run of length $\ge a_{N_0}$. It is proved by adding a *deficit* parameter to the base-window
engine `eventuallyComplete_of_brown_of_base_window` above (letting the covered window sit
strictly inside $[L, C\ a\ N_0]$ instead of filling it exactly), then instantiated below with 21
explicit finite certificates, each kernel-checked by `decide` on concrete `Finset ℤ` literals.

**Why this does not close the band.** The reduction does not narrow the band itself: at its
$\alpha \to 3/2^-$ endpoint, the arithmetic core of the (RUN) certificate — the existence of a
$t$ making every $\lfloor t\alpha^n\rfloor$ share a nontrivial common structure forever — is
literally Mahler's $3/2$ problem (non-existence of "$Z$-numbers"), open since 1968. What *is*
proved here is that the band can be filled **arbitrarily close to $3/2$, point by point**: the
barrier obstructs only the universal statement over the whole band, not any single concrete
pair. -/

/-- **Subset-sum witness constructor.** If $B \subseteq A$ (as finite sets of integers) and
$k = \sum_{i \in B} i$, then $k$ is a subset sum of $A$. A trivial repackaging of the definition
of `subsetSums`, used throughout the finite window certificates below. Textbook-level. -/
@[category textbook, AMS 11]
theorem mem_subsetSums_of_subset {A B : Finset ℤ} (hsub : B ⊆ A) {k : ℤ}
    (hk : k = ∑ i ∈ B, i) : k ∈ subsetSums ((A : Finset ℤ) : Set ℤ) :=
  ⟨B, by exact_mod_cast Finset.coe_subset.mpr hsub, hk⟩

/-- **Eventual-completeness engine with an interior deficit window.** Generalizes
`eventuallyComplete_of_brown_of_base_window` above by letting the covered base window sit
*strictly inside* $[L, C\ a\ N_0]$, at distance $D$ from its right end. Let $a : \mathbb{N} \to
\mathbb{Z}$ be nonnegative, monotone and unbounded, and suppose there are $N_0 : \mathbb{N}$ and
$L, D \in \mathbb{Z}$ such that: (i) *interior base window* — every $k$ with $L \le k \le C\ a\
N_0 - D$ is already a subset sum of $\{a_0, \ldots, a_{N_0-1}\}$; (ii) *shifted Brown margin* —
$a_n + L + D \le 1 + C\ a\ n$ for every $n \ge N_0$. Then $\operatorname{range} a$ is additively
complete in the eventual sense.

Taking $D = 0$ recovers `eventuallyComplete_of_brown_of_base_window` exactly. The deficit $D$ is
what lets `isGoodPair_of_run` below reduce goodness to a *finite* certificate: taking
$D := C\ a\ N_0 - U$ for an explicit run $[L, U]$ collapses (i) to the run hypothesis and the base
case of (ii) to a single arithmetic inequality on $a_{N_0}$.

Textbook-level: a purely combinatorial merge-induction on monotone integer sequences (no $t,
\alpha$), directly analogous to `eventuallyComplete_of_brown_of_base_window`; the research content
of Erdős Problem 349 is in `isGoodPair_of_run` below.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11]
theorem eventuallyComplete_of_brown_of_deficit_window (a : ℕ → ℤ)
    (hnn : ∀ n, 0 ≤ a n)
    (hmono : Monotone a)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n)
    (N₀ : ℕ) (L D : ℤ)
    (hbase : ∀ k : ℤ, L ≤ k → k ≤ C a N₀ - D →
      k ∈ subsetSums (((Finset.range N₀).image a : Finset ℤ) : Set ℤ))
    (hbrown : ∀ n : ℕ, N₀ ≤ n → a n + L + D ≤ 1 + C a n) :
    IsAddComplete (Set.range a) := by
  have _hmono : Monotone a := hmono
  have hmemC : ∀ N, a N ≤ C a (N + 1) := le_C_succ a hnn
  have hCmono : Monotone (C a) := by
    intro M N hMN
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.image_subset_image (Finset.range_subset_range.mpr hMN)
    · intro x hx _; rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
  have key : ∀ N : ℕ, N₀ ≤ N → ∀ k : ℤ, L ≤ k → k ≤ C a N - D →
      k ∈ subsetSums (((Finset.range N).image a : Finset ℤ) : Set ℤ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hbase
    | succ N hN ih =>
      intro k hkL hkC
      by_cases hnew : a N ∈ (Finset.range N).image a
      · have himg : (Finset.range (N + 1)).image a = (Finset.range N).image a := by
          rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr hnew]
        have hCC : C a (N + 1) = C a N := by simp only [C, himg]
        rw [hCC] at hkC
        rw [himg]
        exact ih k hkL hkC
      · have himg : (Finset.range (N + 1)).image a
            = insert (a N) ((Finset.range N).image a) := by
          rw [Finset.range_add_one, Finset.image_insert]
        have hCC : C a (N + 1) = a N + C a N := by
          simp only [C, himg, Finset.sum_insert hnew]
        rw [hCC] at hkC
        by_cases hkle : k ≤ C a N - D
        · obtain ⟨B, hB, hBeq⟩ := ih k hkL hkle
          refine ⟨B, ?_, hBeq⟩
          refine hB.trans ?_
          rw [himg, Finset.coe_insert]
          exact Set.subset_insert _ _
        · rw [not_le] at hkle
          have hb := hbrown N hN
          have hkL' : L ≤ k - a N := by omega
          have hkC' : k - a N ≤ C a N - D := by omega
          obtain ⟨B, hB, hBeq⟩ := ih (k - a N) hkL' hkC'
          have haN : a N ∉ B := by
            intro hmem
            have := hB hmem
            simp only [Finset.mem_coe] at this
            exact hnew this
          refine ⟨insert (a N) B, ?_, ?_⟩
          · rw [himg, Finset.coe_insert, Finset.coe_insert]
            intro x hx
            rcases Set.mem_insert_iff.mp hx with hx | hx
            · subst hx; exact Set.mem_insert _ _
            · exact Set.mem_insert_iff.mpr (Or.inr (hB hx))
          · rw [Finset.sum_insert haN]; omega
  rw [IsAddComplete, eventually_atTop]
  refine ⟨L, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hub (k + D)
  have hkC : k ≤ C a (max (n + 1) N₀) - D := by
    have h1 : k + D ≤ C a (n + 1) := le_trans hn (hmemC n)
    have h2 := hCmono (le_max_left (n + 1) N₀)
    omega
  obtain ⟨B, hB, hBeq⟩ := key (max (n + 1) N₀) (le_max_right _ _) k hk hkC
  refine ⟨B, ?_, hBeq⟩
  refine hB.trans ?_
  intro x hx
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Set.mem_range_self i

/-- **Shifted Brown margin propagates from a doubling bound.** For a monotone sequence $a$
satisfying the doubling bound $a_{n+1} \le 2 a_n$, if $a_{N_0}$ is a new value (not among $a_0,
\ldots, a_{N_0-1}$) and the base inequality $a_{N_0} + L + D \le 1 + C\ a\ N_0$ holds, then the
shifted margin $a_n + L + D \le 1 + C\ a\ n$ propagates to every $n \ge N_0$.

Textbook-level: a purely combinatorial induction on monotone integer sequences (no $t, \alpha$);
its instantiation `floorSeq_brown_shifted` below (for $a_n = \lfloor t\alpha^n\rfloor$) supplies
hypothesis (ii) of `eventuallyComplete_of_brown_of_deficit_window` for `isGoodPair_of_run`.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category textbook, AMS 11]
theorem brown_shifted_of_doubling (a : ℕ → ℤ) (L D : ℤ) (N₀ : ℕ)
    (hmono : Monotone a)
    (hdouble : ∀ n, a (n + 1) ≤ 2 * a n)
    (hnew : a N₀ ∉ (Finset.range N₀).image a)
    (hbase : a N₀ + L + D ≤ 1 + C a N₀) :
    ∀ n : ℕ, N₀ ≤ n → a n + L + D ≤ 1 + C a n := by
  classical
  have hT : ∀ n : ℕ, N₀ ≤ n → 2 * a n + L + D ≤ 1 + C a (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [C_succ_of_notMem a hnew]
      omega
    | succ n _ ih =>
      by_cases hdup : a (n + 1) ∈ (Finset.range (n + 1)).image a
      · have heq : a (n + 1) = a n := by
          rw [Finset.mem_image] at hdup
          obtain ⟨j, hj, hja⟩ := hdup
          have h1 : a j ≤ a n := hmono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          have h2 : a n ≤ a (n + 1) := hmono (Nat.le_succ n)
          omega
        rw [C_succ_of_mem a hdup, heq]
        exact ih
      · rw [C_succ_of_notMem a hdup]
        have hd := hdouble n
        omega
  intro n hn
  rcases eq_or_lt_of_le hn with heq | hlt
  · rw [← heq]; omega
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hp : N₀ ≤ p := by omega
    have h1 := hT p hp
    have h2 := hdouble p
    omega

/-- **Shifted Brown margin for the floor sequence.** Instance of `brown_shifted_of_doubling` for
$a_n = \lfloor t\alpha^n\rfloor$, whose doubling bound is `floor_mul_pow_succ_le_two_mul` above
(valid for $1 \le t$, $1 < \alpha < 3/2$). A building block for `isGoodPair_of_run` below.
Textbook-level. -/
@[category textbook, AMS 11]
theorem floorSeq_brown_shifted (t α : ℝ) (L D : ℤ) (N₀ : ℕ)
    (ht : 1 ≤ t) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋))
    (hbase : ⌊t * α ^ N₀⌋ + L + D ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) N₀) :
    ∀ n : ℕ, N₀ ≤ n →
      ⌊t * α ^ n⌋ + L + D ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) n :=
  brown_shifted_of_doubling (fun n : ℕ => ⌊t * α ^ n⌋) L D N₀
    (floorSeq_monotone t α (by linarith) hα1.le)
    (fun n => floor_mul_pow_succ_le_two_mul t α hα1 hα2 ht n)
    hnew hbase

/-- **The Reduction Theorem for Erdős Problem 349, `t ≥ 2` regime.** Let $t, \alpha \in
\mathbb{R}$ with $1 \le t$, $1 < \alpha < 3/2$, and write $a_n = \lfloor t\alpha^n\rfloor$. If
there are $N_0 \in \mathbb{N}$ and $L, U \in \mathbb{Z}$ such that

* $a_{N_0}$ is a *new* value (not among $a_0, \ldots, a_{N_0-1}$);
* every integer of $[L, U]$ is a subset sum of $\{a_0, \ldots, a_{N_0-1}\}$;
* $a_{N_0} \le U - L + 1$ (the run already covered is at least as long as the next term needs),

then $(t, \alpha)$ is a good pair.

This is the honest permanent statement of what remains open about the band $t \ge 2$, $1 < \alpha
< 3/2$: it is *exactly* the collection of pairs admitting such a run certificate, and no
soft/metric criterion can imply the certificate in general — its arithmetic core at $\alpha \to
3/2^-$ is Mahler's $3/2$ problem, open since 1968. Instantiated below for 21 explicit pairs, never
asserted for a whole region.

Proof: instantiate `eventuallyComplete_of_brown_of_deficit_window` with $a_n = \lfloor
t\alpha^n\rfloor$ and deficit $D := C\ a\ N_0 - U$; then $C\ a\ N_0 - D = U$, the interior base
window collapses to exactly the run hypothesis, and the base case of the shifted Brown margin
(`floorSeq_brown_shifted`) collapses to exactly $a_{N_0} \le U - L + 1$.

A **partial result** on the open Erdős Problem 349, in the same family as
`isGoodPair_of_pos_of_lt_two` above but for the $t \ge 2$ regime that theorem does not cover.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11]
theorem isGoodPair_of_run (t α : ℝ) (ht : 1 ≤ t) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (N₀ : ℕ) (L U : ℤ)
    (hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋))
    (hrun : ∀ k : ℤ, L ≤ k → k ≤ U →
      k ∈ subsetSums (((Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) : Finset ℤ) : Set ℤ))
    (hfit : ⌊t * α ^ N₀⌋ ≤ U - L + 1) :
    IsGoodPair t α := by
  have ht0 : (0:ℝ) < t := by linarith
  have hα0 : (0:ℝ) < α := by linarith
  show IsAddComplete (Set.range fun n : ℕ => ⌊t * α ^ n⌋)
  refine eventuallyComplete_of_brown_of_deficit_window (fun n : ℕ => ⌊t * α ^ n⌋)
    (fun n => floorSeq_nonneg t α ht0.le hα0.le n) (floorSeq_monotone t α ht0.le hα1.le)
    (floorSeq_unbounded t α ht0 hα1) N₀ L
    (C (fun n : ℕ => ⌊t * α ^ n⌋) N₀ - U) ?_ ?_
  · intro k hkL hkU
    exact hrun k hkL (by omega)
  · exact floorSeq_brown_shifted t α L (C (fun n : ℕ => ⌊t * α ^ n⌋) N₀ - U) N₀
      ht hα1 hα2 hnew (by omega)
/-- Every integer of $[2, 7]$ is a subset sum of $\{2, 3, 4\}$ (6 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]

theorem window_two_four : ∀ k : ℤ, 2 ≤ k → k ≤ 7 →
    k ∈ subsetSums ((({2, 3, 4} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {2}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 3}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4}) (by decide) (by decide)

/-- Every integer of $[7, 21]$ is a subset sum of $\{3, 4, 5, 7, 9\}$ (15 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_three_nine : ∀ k : ℤ, 7 ≤ k → k ≤ 21 →
    k ∈ subsetSums ((({3, 4, 5, 7, 9} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨
      k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact mem_subsetSums_of_subset (B := {7}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 7}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 7}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 7, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 9}) (by decide) (by decide)

/-- Every integer of $[8, 49]$ is a subset sum of $\{2, 4, 6, 9, 14, 22\}$ (42 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W1 : ∀ k : ℤ, 8 ≤ k → k ≤ 49 →
    k ∈ subsetSums ((({2, 4, 6, 9, 14, 22} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {2, 6}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4, 6}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4, 6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4, 6, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4, 6, 9, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 9, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4, 6, 14, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9, 14, 22}) (by decide) (by decide)

/-- Every integer of $[14, 79]$ is a subset sum of $\{2, 4, 6, 10, 15, 22, 34\}$ (66 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W2 : ∀ k : ℤ, 14 ≤ k → k ≤ 79 →
    k ∈ subsetSums ((({2, 4, 6, 10, 15, 22, 34} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {4, 10}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 10}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 10, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 10, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 15}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 10, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 10, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 4, 6, 10, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 6, 15, 22, 34}) (by decide) (by decide)

/-- Every integer of $[23, 77]$ is a subset sum of $\{2, 3, 5, 7, 11, 16, 23, 33\}$ (55 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W3 : ∀ k : ℤ, 23 ≤ k → k ≤ 77 →
    k ∈ subsetSums ((({2, 3, 5, 7, 11, 16, 23, 33} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 16}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 11, 16}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 7, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 11, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 16, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 7, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 11, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 11, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 7, 16, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 7, 11, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 11, 16, 23}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 11, 16, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 7, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 11, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 11, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 7, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 3, 5, 7, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 16, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 16, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 7, 11, 23, 33}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 16, 23, 33}) (by decide) (by decide)

/-- Every integer of $[25, 93]$ is a subset sum of $\{2, 3, 5, 8, 12, 18, 28, 42\}$ (69 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W4 : ∀ k : ℤ, 25 ≤ k → k ≤ 93 →
    k ∈ subsetSums ((({2, 3, 5, 8, 12, 18, 28, 42} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 ∨ k = 80 ∨ k = 81 ∨ k = 82 ∨ k = 83 ∨ k = 84 ∨ k = 85 ∨ k = 86 ∨ k = 87 ∨ k = 88 ∨ k = 89 ∨ k = 90 ∨ k = 91 ∨ k = 92 ∨ k = 93 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {2, 5, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 8, 12}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 8, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 12, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 8, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 12, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 8, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 8, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 12, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 18, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 18, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 8, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 8, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 18, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 8, 12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 12, 18, 28}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 8, 12, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 8, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 12, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 8, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 12, 18, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 8, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 8, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 12, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 12, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 5, 8, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 12, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 5, 12, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 18, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 18, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {2, 8, 12, 28, 42}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 18, 28, 42}) (by decide) (by decide)

/-- Every integer of $[12, 45]$ is a subset sum of $\{3, 4, 6, 9, 14, 21\}$ (34 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W5 : ∀ k : ℤ, 12 ≤ k → k ≤ 45 →
    k ∈ subsetSums ((({3, 4, 6, 9, 14, 21} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {3, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 6, 9}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 9, 14}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 14, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 14, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 14, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 14, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 6, 9, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 14, 21}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 14, 21}) (by decide) (by decide)

/-- Every integer of $[34, 111]$ is a subset sum of $\{3, 4, 6, 10, 15, 22, 34, 51\}$ (78 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W6 : ∀ k : ℤ, 34 ≤ k → k ≤ 111 →
    k ∈ subsetSums ((({3, 4, 6, 10, 15, 22, 34, 51} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 ∨ k = 80 ∨ k = 81 ∨ k = 82 ∨ k = 83 ∨ k = 84 ∨ k = 85 ∨ k = 86 ∨ k = 87 ∨ k = 88 ∨ k = 89 ∨ k = 90 ∨ k = 91 ∨ k = 92 ∨ k = 93 ∨ k = 94 ∨ k = 95 ∨ k = 96 ∨ k = 97 ∨ k = 98 ∨ k = 99 ∨ k = 100 ∨ k = 101 ∨ k = 102 ∨ k = 103 ∨ k = 104 ∨ k = 105 ∨ k = 106 ∨ k = 107 ∨ k = 108 ∨ k = 109 ∨ k = 110 ∨ k = 111 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 10, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 10, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 6, 10, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 15, 22}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 10, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 10, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 15, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 15, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 15, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 10, 15, 22, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 10, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 10, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 6, 10, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 15, 22, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 15, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 15, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 6, 10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {6, 15, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {22, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 4, 6, 10, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 6, 15, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 22, 34, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 22, 34, 51}) (by decide) (by decide)

/-- Every integer of $[31, 120]$ is a subset sum of $\{4, 5, 8, 11, 16, 24, 34, 49\}$ (90 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W7 : ∀ k : ℤ, 31 ≤ k → k ≤ 120 →
    k ∈ subsetSums ((({4, 5, 8, 11, 16, 24, 34, 49} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 ∨ k = 80 ∨ k = 81 ∨ k = 82 ∨ k = 83 ∨ k = 84 ∨ k = 85 ∨ k = 86 ∨ k = 87 ∨ k = 88 ∨ k = 89 ∨ k = 90 ∨ k = 91 ∨ k = 92 ∨ k = 93 ∨ k = 94 ∨ k = 95 ∨ k = 96 ∨ k = 97 ∨ k = 98 ∨ k = 99 ∨ k = 100 ∨ k = 101 ∨ k = 102 ∨ k = 103 ∨ k = 104 ∨ k = 105 ∨ k = 106 ∨ k = 107 ∨ k = 108 ∨ k = 109 ∨ k = 110 ∨ k = 111 ∨ k = 112 ∨ k = 113 ∨ k = 114 ∨ k = 115 ∨ k = 116 ∨ k = 117 ∨ k = 118 ∨ k = 119 ∨ k = 120 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {4, 11, 16}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 8, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 16, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 16, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 16, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 16, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 11, 16, 24}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 16, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 11, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 16, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 16, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 11, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 8, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 16, 24, 34}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 16, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 8, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {16, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 11, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 16, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 16, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 11, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 11, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 16, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 11, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 16, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 11, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 16, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {8, 24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 5, 8, 11, 16, 24, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 8, 24, 34, 49}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 8, 24, 34, 49}) (by decide) (by decide)

/-- Every integer of $[47, 146]$ is a subset sum of $\{5, 7, 10, 14, 21, 30, 43, 63\}$ (100 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W8 : ∀ k : ℤ, 47 ≤ k → k ≤ 146 →
    k ∈ subsetSums ((({5, 7, 10, 14, 21, 30, 43, 63} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 ∨ k = 80 ∨ k = 81 ∨ k = 82 ∨ k = 83 ∨ k = 84 ∨ k = 85 ∨ k = 86 ∨ k = 87 ∨ k = 88 ∨ k = 89 ∨ k = 90 ∨ k = 91 ∨ k = 92 ∨ k = 93 ∨ k = 94 ∨ k = 95 ∨ k = 96 ∨ k = 97 ∨ k = 98 ∨ k = 99 ∨ k = 100 ∨ k = 101 ∨ k = 102 ∨ k = 103 ∨ k = 104 ∨ k = 105 ∨ k = 106 ∨ k = 107 ∨ k = 108 ∨ k = 109 ∨ k = 110 ∨ k = 111 ∨ k = 112 ∨ k = 113 ∨ k = 114 ∨ k = 115 ∨ k = 116 ∨ k = 117 ∨ k = 118 ∨ k = 119 ∨ k = 120 ∨ k = 121 ∨ k = 122 ∨ k = 123 ∨ k = 124 ∨ k = 125 ∨ k = 126 ∨ k = 127 ∨ k = 128 ∨ k = 129 ∨ k = 130 ∨ k = 131 ∨ k = 132 ∨ k = 133 ∨ k = 134 ∨ k = 135 ∨ k = 136 ∨ k = 137 ∨ k = 138 ∨ k = 139 ∨ k = 140 ∨ k = 141 ∨ k = 142 ∨ k = 143 ∨ k = 144 ∨ k = 145 ∨ k = 146 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {7, 10, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 14, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {21, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 10, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 21, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 14, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 21, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 14, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 21, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 21, 30}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 14, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 14, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 10, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 10, 21, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 14, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 10, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 21, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 14, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 21, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 21, 30, 43}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 14, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 10, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 14, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 14, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {14, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 14, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 14, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {30, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 14, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 7, 14, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 30, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {5, 10, 21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 30, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 21, 43, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 10, 14, 21, 30, 63}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 30, 43, 63}) (by decide) (by decide)

/-- Every integer of $[42, 117]$ is a subset sum of $\{7, 9, 13, 18, 26, 36, 50\}$ (76 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W9 : ∀ k : ℤ, 42 ≤ k → k ≤ 117 →
    k ∈ subsetSums ((({7, 9, 13, 18, 26, 36, 50} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 ∨ k = 64 ∨ k = 65 ∨ k = 66 ∨ k = 67 ∨ k = 68 ∨ k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 ∨ k = 80 ∨ k = 81 ∨ k = 82 ∨ k = 83 ∨ k = 84 ∨ k = 85 ∨ k = 86 ∨ k = 87 ∨ k = 88 ∨ k = 89 ∨ k = 90 ∨ k = 91 ∨ k = 92 ∨ k = 93 ∨ k = 94 ∨ k = 95 ∨ k = 96 ∨ k = 97 ∨ k = 98 ∨ k = 99 ∨ k = 100 ∨ k = 101 ∨ k = 102 ∨ k = 103 ∨ k = 104 ∨ k = 105 ∨ k = 106 ∨ k = 107 ∨ k = 108 ∨ k = 109 ∨ k = 110 ∨ k = 111 ∨ k = 112 ∨ k = 113 ∨ k = 114 ∨ k = 115 ∨ k = 116 ∨ k = 117 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {7, 9, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 18}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 18, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 18, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 18, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 18, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 18, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 18, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 18, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 18, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 18, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 18, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 18, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {18, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 18, 26, 36}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 18, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {26, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 18, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 13, 18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 9, 13, 36, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {9, 13, 18, 26, 50}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {13, 18, 36, 50}) (by decide) (by decide)

/-- Every integer of $[69, 136]$ is a subset sum of $\{10, 12, 15, 20, 25, 32, 40, 51\}$ (68 explicit witnesses, kernel-checked by `decide` on concrete `Finset ℤ` literals). A finite building block for `isGoodPair_of_run`'s run hypothesis. -/
@[category textbook, AMS 11]
theorem window_W10 : ∀ k : ℤ, 69 ≤ k → k ≤ 136 →
    k ∈ subsetSums ((({10, 12, 15, 20, 25, 32, 40, 51} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 69 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 73 ∨ k = 74 ∨ k = 75 ∨ k = 76 ∨ k = 77 ∨ k = 78 ∨ k = 79 ∨ k = 80 ∨ k = 81 ∨ k = 82 ∨ k = 83 ∨ k = 84 ∨ k = 85 ∨ k = 86 ∨ k = 87 ∨ k = 88 ∨ k = 89 ∨ k = 90 ∨ k = 91 ∨ k = 92 ∨ k = 93 ∨ k = 94 ∨ k = 95 ∨ k = 96 ∨ k = 97 ∨ k = 98 ∨ k = 99 ∨ k = 100 ∨ k = 101 ∨ k = 102 ∨ k = 103 ∨ k = 104 ∨ k = 105 ∨ k = 106 ∨ k = 107 ∨ k = 108 ∨ k = 109 ∨ k = 110 ∨ k = 111 ∨ k = 112 ∨ k = 113 ∨ k = 114 ∨ k = 115 ∨ k = 116 ∨ k = 117 ∨ k = 118 ∨ k = 119 ∨ k = 120 ∨ k = 121 ∨ k = 122 ∨ k = 123 ∨ k = 124 ∨ k = 125 ∨ k = 126 ∨ k = 127 ∨ k = 128 ∨ k = 129 ∨ k = 130 ∨ k = 131 ∨ k = 132 ∨ k = 133 ∨ k = 134 ∨ k = 135 ∨ k = 136 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {12, 25, 32}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 20, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 20, 32}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 25, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {25, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 25, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 15, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 25, 32}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 25, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 20, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 25, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 25, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 25, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 20, 25, 32}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 15, 25, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 25, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 15, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 20, 25, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 20, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 20, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {25, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 15, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 20, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 20, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {25, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 25, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 25, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 20, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 15, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {32, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 15, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 20, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 25, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 20, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 25, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 20, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 25, 32, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 25, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {15, 20, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 32, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {10, 12, 15, 25, 32, 40}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {12, 32, 40, 51}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {20, 25, 40, 51}) (by decide) (by decide)

/-- **First good pair strictly outside the near-one strip.** $(5/2, 7/5)$ is a good pair:
$N_0 = 3$, the floor sequence gives the distinct values $\{2, 3, 4\}$, then $a_3 = 6$ exactly
fits the run $[2, 7]$ (`window_two_four`). Since $\lfloor 5/2\rfloor = 2$, the strip
`isGoodPair_of_pos_of_lt_two` only reaches $\alpha \le 1 + 1/(2\cdot 2+2) = 7/6 \approx 1.167$;
here $\alpha = 7/5 = 1.4$ is $70\%$ of the way across the open interval $(7/6, 3/2)$. Instance of
`isGoodPair_of_run`. -/
@[category research solved, AMS 11]
theorem isGoodPair_five_halves_seven_fifths : IsGoodPair (5 / 2 : ℝ) (7 / 5 : ℝ) := by
  have e0 : ⌊(5 / 2 : ℝ) * (7 / 5) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
  have e1 : ⌊(5 / 2 : ℝ) * (7 / 5) ^ (1 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
  have e2 : ⌊(5 / 2 : ℝ) * (7 / 5) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
  have e3 : ⌊(5 / 2 : ℝ) * (7 / 5) ^ (3 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
  have himg : (Finset.range 3).image (fun n : ℕ => ⌊(5 / 2 : ℝ) * (7 / 5) ^ n⌋) = {2, 3, 4} := by
    rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
    simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2]
    decide
  refine isGoodPair_of_run (5 / 2) (7 / 5) (by norm_num) (by norm_num) (by norm_num) 3 2 7 ?_ ?_ ?_
  · rw [himg, e3]; decide
  · rw [himg]; exact window_two_four
  · omega

/-- **Reaching $\alpha = 1.4999$, deep toward the $3/2$ endpoint (headline, $t = 2$).**
$(2, 14999/10000)$ is a good pair: $N_0 = 8$, distinct values
$\{2, 4, 6, 10, 15, 22, 34\}$, then $a_8 = 51$ fits the run $[14, 79]$ (`window_W2`). Instance of
`isGoodPair_of_run`, showing the band can be filled arbitrarily close to $3/2$ point by point even
though the full band $t \ge 2$, $1 < \alpha < 3/2$ remains open. -/
@[category research solved, AMS 11]
theorem isGoodPair_two_alpha_1_4999 : IsGoodPair (2 : ℝ) (14999 / 10000 : ℝ) := by
  have e0 : ⌊(2 : ℝ) * (14999 / 10000) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
  have e1 : ⌊(2 : ℝ) * (14999 / 10000) ^ (1 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
  have e2 : ⌊(2 : ℝ) * (14999 / 10000) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
  have e3 : ⌊(2 : ℝ) * (14999 / 10000) ^ (3 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
  have e4 : ⌊(2 : ℝ) * (14999 / 10000) ^ (4 : ℕ)⌋ = 10 := by rw [Int.floor_eq_iff]; norm_num
  have e5 : ⌊(2 : ℝ) * (14999 / 10000) ^ (5 : ℕ)⌋ = 15 := by rw [Int.floor_eq_iff]; norm_num
  have e6 : ⌊(2 : ℝ) * (14999 / 10000) ^ (6 : ℕ)⌋ = 22 := by rw [Int.floor_eq_iff]; norm_num
  have e7 : ⌊(2 : ℝ) * (14999 / 10000) ^ (7 : ℕ)⌋ = 34 := by rw [Int.floor_eq_iff]; norm_num
  have e8 : ⌊(2 : ℝ) * (14999 / 10000) ^ (8 : ℕ)⌋ = 51 := by rw [Int.floor_eq_iff]; norm_num
  have himg : (Finset.range 8).image (fun n : ℕ => ⌊(2 : ℝ) * (14999 / 10000) ^ n⌋) = {2, 4, 6, 10, 15, 22, 34} := by
    rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
    simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
    decide
  refine isGoodPair_of_run (2 : ℝ) (14999 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 14 79 ?_ ?_ ?_
  · rw [himg, e8]; decide
  · rw [himg]; exact window_W2
  · omega

/-- **Reaching $\alpha = 1.4999$, deep toward the $3/2$ endpoint (headline, $t = 5/2$).**
$(5/2, 14999/10000)$ is a good pair: $N_0 = 8$, distinct values
$\{2, 3, 5, 8, 12, 18, 28, 42\}$, then $a_8 = 64$ fits the run $[25, 93]$ (`window_W4`). Instance
of `isGoodPair_of_run`; see `isGoodPair_two_alpha_1_4999` for the significance of this frontier. -/
@[category research solved, AMS 11]
theorem isGoodPair_five_halves_alpha_1_4999 : IsGoodPair (5 / 2 : ℝ) (14999 / 10000 : ℝ) := by
  have e0 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
  have e1 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (1 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
  have e2 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (2 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
  have e3 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (3 : ℕ)⌋ = 8 := by rw [Int.floor_eq_iff]; norm_num
  have e4 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (4 : ℕ)⌋ = 12 := by rw [Int.floor_eq_iff]; norm_num
  have e5 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (5 : ℕ)⌋ = 18 := by rw [Int.floor_eq_iff]; norm_num
  have e6 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (6 : ℕ)⌋ = 28 := by rw [Int.floor_eq_iff]; norm_num
  have e7 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (7 : ℕ)⌋ = 42 := by rw [Int.floor_eq_iff]; norm_num
  have e8 : ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ (8 : ℕ)⌋ = 64 := by rw [Int.floor_eq_iff]; norm_num
  have himg : (Finset.range 8).image (fun n : ℕ => ⌊(5 / 2 : ℝ) * (14999 / 10000) ^ n⌋) = {2, 3, 5, 8, 12, 18, 28, 42} := by
    rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
    simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
    decide
  refine isGoodPair_of_run (5 / 2 : ℝ) (14999 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 25 93 ?_ ?_ ?_
  · rw [himg, e8]; decide
  · rw [himg]; exact window_W4
  · omega

/-- **Reaching $\alpha = 1.4999$, deep toward the $3/2$ endpoint (headline, $t = 3$).**
$(3, 14999/10000)$ is a good pair: $N_0 = 8$, distinct values
$\{3, 4, 6, 10, 15, 22, 34, 51\}$, then $a_8 = 76$ fits the run $[34, 111]$ (`window_W6`). Instance
of `isGoodPair_of_run`; see `isGoodPair_two_alpha_1_4999` for the significance of this frontier. -/
@[category research solved, AMS 11]
theorem isGoodPair_three_alpha_1_4999 : IsGoodPair (3 : ℝ) (14999 / 10000 : ℝ) := by
  have e0 : ⌊(3 : ℝ) * (14999 / 10000) ^ (0 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
  have e1 : ⌊(3 : ℝ) * (14999 / 10000) ^ (1 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
  have e2 : ⌊(3 : ℝ) * (14999 / 10000) ^ (2 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
  have e3 : ⌊(3 : ℝ) * (14999 / 10000) ^ (3 : ℕ)⌋ = 10 := by rw [Int.floor_eq_iff]; norm_num
  have e4 : ⌊(3 : ℝ) * (14999 / 10000) ^ (4 : ℕ)⌋ = 15 := by rw [Int.floor_eq_iff]; norm_num
  have e5 : ⌊(3 : ℝ) * (14999 / 10000) ^ (5 : ℕ)⌋ = 22 := by rw [Int.floor_eq_iff]; norm_num
  have e6 : ⌊(3 : ℝ) * (14999 / 10000) ^ (6 : ℕ)⌋ = 34 := by rw [Int.floor_eq_iff]; norm_num
  have e7 : ⌊(3 : ℝ) * (14999 / 10000) ^ (7 : ℕ)⌋ = 51 := by rw [Int.floor_eq_iff]; norm_num
  have e8 : ⌊(3 : ℝ) * (14999 / 10000) ^ (8 : ℕ)⌋ = 76 := by rw [Int.floor_eq_iff]; norm_num
  have himg : (Finset.range 8).image (fun n : ℕ => ⌊(3 : ℝ) * (14999 / 10000) ^ n⌋) = {3, 4, 6, 10, 15, 22, 34, 51} := by
    rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
    simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
    decide
  refine isGoodPair_of_run (3 : ℝ) (14999 / 10000 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 34 111 ?_ ?_ ?_
  · rw [himg, e8]; decide
  · rw [himg]; exact window_W6
  · omega

/-- **Seventeen further good pairs, same reduction, compactly bundled.** All instantiate
`isGoodPair_of_run` exactly like the four headline results above (explicit floor values up to a
new rank $N_0$, matched against a finite window certificate); bundled into one statement so the
family is reviewed as a single declaration rather than seventeen near-identical ones. In the order
listed: $t = 5/2$ at $\alpha = 4/3$; $t = 2$ at $\alpha \in \{4/3, 5/4, 112/75, 299/200,
1499/1000\}$; $t = 5/2$ at $\alpha \in \{29/20, 449/300\}$; $t = 3$ at $\alpha \in \{4/3, 5/4,
37/25, 89/60, 1499/1000\}$; $t = 4$ at $\alpha = 76/53$; $t = 5$ at $\alpha = 79/55$; $t = 7$ at
$\alpha = 71/51$; $t = 10$ at $\alpha = 43/34$. Together with the four headline pairs, this gives
**21 good pairs total** with $t \in \{2, 5/2, 3, 4, 5, 7, 10\}$ and $\alpha$ ranging from $5/4$ up
to $14999/10000$, all strictly outside the strip $\alpha \le 1 + 1/(2\lfloor t\rfloor+2)$ covered
by `isGoodPair_of_pos_of_lt_two`.

A **partial result** on the open Erdős Problem 349: these are 17 more explicit instances of
`isGoodPair_of_run`, never a claim about a whole region. The full band $t \ge 2$, $1 < \alpha <
3/2$ remains open.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline. -/
@[category research solved, AMS 11]
theorem isGoodPair_run_further_instances :
    IsGoodPair (5 / 2 : ℝ) (4 / 3 : ℝ) ∧
    IsGoodPair (2 : ℝ) (4 / 3 : ℝ) ∧
    IsGoodPair (2 : ℝ) (5 / 4 : ℝ) ∧
    IsGoodPair (3 : ℝ) (4 / 3 : ℝ) ∧
    IsGoodPair (3 : ℝ) (5 / 4 : ℝ) ∧
    IsGoodPair (2 : ℝ) (112 / 75 : ℝ) ∧
    IsGoodPair (2 : ℝ) (299 / 200 : ℝ) ∧
    IsGoodPair (2 : ℝ) (1499 / 1000 : ℝ) ∧
    IsGoodPair (5 / 2 : ℝ) (29 / 20 : ℝ) ∧
    IsGoodPair (5 / 2 : ℝ) (449 / 300 : ℝ) ∧
    IsGoodPair (3 : ℝ) (37 / 25 : ℝ) ∧
    IsGoodPair (3 : ℝ) (89 / 60 : ℝ) ∧
    IsGoodPair (3 : ℝ) (1499 / 1000 : ℝ) ∧
    IsGoodPair (4 : ℝ) (76 / 53 : ℝ) ∧
    IsGoodPair (5 : ℝ) (79 / 55 : ℝ) ∧
    IsGoodPair (7 : ℝ) (71 / 51 : ℝ) ∧
    IsGoodPair (10 : ℝ) (43 / 34 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : ⌊(5 / 2 : ℝ) * (4 / 3) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(5 / 2 : ℝ) * (4 / 3) ^ (1 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(5 / 2 : ℝ) * (4 / 3) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(5 / 2 : ℝ) * (4 / 3) ^ (3 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 3).image (fun n : ℕ => ⌊(5 / 2 : ℝ) * (4 / 3) ^ n⌋) = {2, 3, 4} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2]
      decide
    refine isGoodPair_of_run (5 / 2) (4 / 3) (by norm_num) (by norm_num) (by norm_num) 3 2 7 ?_ ?_ ?_
    · rw [himg, e3]; decide
    · rw [himg]; exact window_two_four
    · omega
  · have e0 : ⌊(2 : ℝ) * (4 / 3) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(2 : ℝ) * (4 / 3) ^ (1 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(2 : ℝ) * (4 / 3) ^ (2 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(2 : ℝ) * (4 / 3) ^ (3 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(2 : ℝ) * (4 / 3) ^ (4 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 4).image (fun n : ℕ => ⌊(2 : ℝ) * (4 / 3) ^ n⌋) = {2, 3, 4} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3]
      decide
    refine isGoodPair_of_run (2) (4 / 3) (by norm_num) (by norm_num) (by norm_num) 4 2 7 ?_ ?_ ?_
    · rw [himg, e4]; decide
    · rw [himg]; exact window_two_four
    · omega
  · have e0 : ⌊(2 : ℝ) * (5 / 4) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(2 : ℝ) * (5 / 4) ^ (1 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(2 : ℝ) * (5 / 4) ^ (2 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(2 : ℝ) * (5 / 4) ^ (3 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(2 : ℝ) * (5 / 4) ^ (4 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(2 : ℝ) * (5 / 4) ^ (5 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 5).image (fun n : ℕ => ⌊(2 : ℝ) * (5 / 4) ^ n⌋) = {2, 3, 4} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4]
      decide
    refine isGoodPair_of_run (2) (5 / 4) (by norm_num) (by norm_num) (by norm_num) 5 2 7 ?_ ?_ ?_
    · rw [himg, e5]; decide
    · rw [himg]; exact window_two_four
    · omega
  · have e0 : ⌊(3 : ℝ) * (4 / 3) ^ (0 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(3 : ℝ) * (4 / 3) ^ (1 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(3 : ℝ) * (4 / 3) ^ (2 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(3 : ℝ) * (4 / 3) ^ (3 : ℕ)⌋ = 7 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(3 : ℝ) * (4 / 3) ^ (4 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(3 : ℝ) * (4 / 3) ^ (5 : ℕ)⌋ = 12 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 5).image (fun n : ℕ => ⌊(3 : ℝ) * (4 / 3) ^ n⌋) = {3, 4, 5, 7, 9} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4]
      decide
    refine isGoodPair_of_run (3) (4 / 3) (by norm_num) (by norm_num) (by norm_num) 5 7 21 ?_ ?_ ?_
    · rw [himg, e5]; decide
    · rw [himg]; exact window_three_nine
    · omega
  · have e0 : ⌊(3 : ℝ) * (5 / 4) ^ (0 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(3 : ℝ) * (5 / 4) ^ (1 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(3 : ℝ) * (5 / 4) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(3 : ℝ) * (5 / 4) ^ (3 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(3 : ℝ) * (5 / 4) ^ (4 : ℕ)⌋ = 7 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(3 : ℝ) * (5 / 4) ^ (5 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(3 : ℝ) * (5 / 4) ^ (6 : ℕ)⌋ = 11 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 6).image (fun n : ℕ => ⌊(3 : ℝ) * (5 / 4) ^ n⌋) = {3, 4, 5, 7, 9} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5]
      decide
    refine isGoodPair_of_run (3) (5 / 4) (by norm_num) (by norm_num) (by norm_num) 6 7 21 ?_ ?_ ?_
    · rw [himg, e6]; decide
    · rw [himg]; exact window_three_nine
    · omega
  · have e0 : ⌊(2 : ℝ) * (112 / 75) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(2 : ℝ) * (112 / 75) ^ (1 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(2 : ℝ) * (112 / 75) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(2 : ℝ) * (112 / 75) ^ (3 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(2 : ℝ) * (112 / 75) ^ (4 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(2 : ℝ) * (112 / 75) ^ (5 : ℕ)⌋ = 14 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(2 : ℝ) * (112 / 75) ^ (6 : ℕ)⌋ = 22 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(2 : ℝ) * (112 / 75) ^ (7 : ℕ)⌋ = 33 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 7).image (fun n : ℕ => ⌊(2 : ℝ) * (112 / 75) ^ n⌋) = {2, 4, 6, 9, 14, 22} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6]
      decide
    refine isGoodPair_of_run (2 : ℝ) (112 / 75 : ℝ) (by norm_num) (by norm_num) (by norm_num) 7 8 49 ?_ ?_ ?_
    · rw [himg, e7]; decide
    · rw [himg]; exact window_W1
    · omega
  · have e0 : ⌊(2 : ℝ) * (299 / 200) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(2 : ℝ) * (299 / 200) ^ (1 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(2 : ℝ) * (299 / 200) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(2 : ℝ) * (299 / 200) ^ (3 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(2 : ℝ) * (299 / 200) ^ (4 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(2 : ℝ) * (299 / 200) ^ (5 : ℕ)⌋ = 14 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(2 : ℝ) * (299 / 200) ^ (6 : ℕ)⌋ = 22 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(2 : ℝ) * (299 / 200) ^ (7 : ℕ)⌋ = 33 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 7).image (fun n : ℕ => ⌊(2 : ℝ) * (299 / 200) ^ n⌋) = {2, 4, 6, 9, 14, 22} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6]
      decide
    refine isGoodPair_of_run (2 : ℝ) (299 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) 7 8 49 ?_ ?_ ?_
    · rw [himg, e7]; decide
    · rw [himg]; exact window_W1
    · omega
  · have e0 : ⌊(2 : ℝ) * (1499 / 1000) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(2 : ℝ) * (1499 / 1000) ^ (1 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(2 : ℝ) * (1499 / 1000) ^ (2 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(2 : ℝ) * (1499 / 1000) ^ (3 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(2 : ℝ) * (1499 / 1000) ^ (4 : ℕ)⌋ = 10 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(2 : ℝ) * (1499 / 1000) ^ (5 : ℕ)⌋ = 15 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(2 : ℝ) * (1499 / 1000) ^ (6 : ℕ)⌋ = 22 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(2 : ℝ) * (1499 / 1000) ^ (7 : ℕ)⌋ = 34 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(2 : ℝ) * (1499 / 1000) ^ (8 : ℕ)⌋ = 50 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(2 : ℝ) * (1499 / 1000) ^ n⌋) = {2, 4, 6, 10, 15, 22, 34} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (2 : ℝ) (1499 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 14 79 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W2
    · omega
  · have e0 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (1 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (2 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (3 : ℕ)⌋ = 7 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (4 : ℕ)⌋ = 11 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (5 : ℕ)⌋ = 16 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (6 : ℕ)⌋ = 23 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (7 : ℕ)⌋ = 33 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(5 / 2 : ℝ) * (29 / 20) ^ (8 : ℕ)⌋ = 48 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(5 / 2 : ℝ) * (29 / 20) ^ n⌋) = {2, 3, 5, 7, 11, 16, 23, 33} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (5 / 2 : ℝ) (29 / 20 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 23 77 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W3
    · omega
  · have e0 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (0 : ℕ)⌋ = 2 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (1 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (2 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (3 : ℕ)⌋ = 8 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (4 : ℕ)⌋ = 12 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (5 : ℕ)⌋ = 18 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (6 : ℕ)⌋ = 28 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (7 : ℕ)⌋ = 42 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(5 / 2 : ℝ) * (449 / 300) ^ (8 : ℕ)⌋ = 62 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(5 / 2 : ℝ) * (449 / 300) ^ n⌋) = {2, 3, 5, 8, 12, 18, 28, 42} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (5 / 2 : ℝ) (449 / 300 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 25 93 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W4
    · omega
  · have e0 : ⌊(3 : ℝ) * (37 / 25) ^ (0 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(3 : ℝ) * (37 / 25) ^ (1 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(3 : ℝ) * (37 / 25) ^ (2 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(3 : ℝ) * (37 / 25) ^ (3 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(3 : ℝ) * (37 / 25) ^ (4 : ℕ)⌋ = 14 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(3 : ℝ) * (37 / 25) ^ (5 : ℕ)⌋ = 21 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(3 : ℝ) * (37 / 25) ^ (6 : ℕ)⌋ = 31 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 6).image (fun n : ℕ => ⌊(3 : ℝ) * (37 / 25) ^ n⌋) = {3, 4, 6, 9, 14, 21} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5]
      decide
    refine isGoodPair_of_run (3 : ℝ) (37 / 25 : ℝ) (by norm_num) (by norm_num) (by norm_num) 6 12 45 ?_ ?_ ?_
    · rw [himg, e6]; decide
    · rw [himg]; exact window_W5
    · omega
  · have e0 : ⌊(3 : ℝ) * (89 / 60) ^ (0 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(3 : ℝ) * (89 / 60) ^ (1 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(3 : ℝ) * (89 / 60) ^ (2 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(3 : ℝ) * (89 / 60) ^ (3 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(3 : ℝ) * (89 / 60) ^ (4 : ℕ)⌋ = 14 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(3 : ℝ) * (89 / 60) ^ (5 : ℕ)⌋ = 21 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(3 : ℝ) * (89 / 60) ^ (6 : ℕ)⌋ = 31 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 6).image (fun n : ℕ => ⌊(3 : ℝ) * (89 / 60) ^ n⌋) = {3, 4, 6, 9, 14, 21} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5]
      decide
    refine isGoodPair_of_run (3 : ℝ) (89 / 60 : ℝ) (by norm_num) (by norm_num) (by norm_num) 6 12 45 ?_ ?_ ?_
    · rw [himg, e6]; decide
    · rw [himg]; exact window_W5
    · omega
  · have e0 : ⌊(3 : ℝ) * (1499 / 1000) ^ (0 : ℕ)⌋ = 3 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(3 : ℝ) * (1499 / 1000) ^ (1 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(3 : ℝ) * (1499 / 1000) ^ (2 : ℕ)⌋ = 6 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(3 : ℝ) * (1499 / 1000) ^ (3 : ℕ)⌋ = 10 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(3 : ℝ) * (1499 / 1000) ^ (4 : ℕ)⌋ = 15 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(3 : ℝ) * (1499 / 1000) ^ (5 : ℕ)⌋ = 22 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(3 : ℝ) * (1499 / 1000) ^ (6 : ℕ)⌋ = 34 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(3 : ℝ) * (1499 / 1000) ^ (7 : ℕ)⌋ = 51 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(3 : ℝ) * (1499 / 1000) ^ (8 : ℕ)⌋ = 76 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(3 : ℝ) * (1499 / 1000) ^ n⌋) = {3, 4, 6, 10, 15, 22, 34, 51} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (3 : ℝ) (1499 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 34 111 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W6
    · omega
  · have e0 : ⌊(4 : ℝ) * (76 / 53) ^ (0 : ℕ)⌋ = 4 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(4 : ℝ) * (76 / 53) ^ (1 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(4 : ℝ) * (76 / 53) ^ (2 : ℕ)⌋ = 8 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(4 : ℝ) * (76 / 53) ^ (3 : ℕ)⌋ = 11 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(4 : ℝ) * (76 / 53) ^ (4 : ℕ)⌋ = 16 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(4 : ℝ) * (76 / 53) ^ (5 : ℕ)⌋ = 24 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(4 : ℝ) * (76 / 53) ^ (6 : ℕ)⌋ = 34 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(4 : ℝ) * (76 / 53) ^ (7 : ℕ)⌋ = 49 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(4 : ℝ) * (76 / 53) ^ (8 : ℕ)⌋ = 71 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(4 : ℝ) * (76 / 53) ^ n⌋) = {4, 5, 8, 11, 16, 24, 34, 49} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (4 : ℝ) (76 / 53 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 31 120 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W7
    · omega
  · have e0 : ⌊(5 : ℝ) * (79 / 55) ^ (0 : ℕ)⌋ = 5 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(5 : ℝ) * (79 / 55) ^ (1 : ℕ)⌋ = 7 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(5 : ℝ) * (79 / 55) ^ (2 : ℕ)⌋ = 10 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(5 : ℝ) * (79 / 55) ^ (3 : ℕ)⌋ = 14 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(5 : ℝ) * (79 / 55) ^ (4 : ℕ)⌋ = 21 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(5 : ℝ) * (79 / 55) ^ (5 : ℕ)⌋ = 30 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(5 : ℝ) * (79 / 55) ^ (6 : ℕ)⌋ = 43 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(5 : ℝ) * (79 / 55) ^ (7 : ℕ)⌋ = 63 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(5 : ℝ) * (79 / 55) ^ (8 : ℕ)⌋ = 90 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(5 : ℝ) * (79 / 55) ^ n⌋) = {5, 7, 10, 14, 21, 30, 43, 63} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (5 : ℝ) (79 / 55 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 47 146 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W8
    · omega
  · have e0 : ⌊(7 : ℝ) * (71 / 51) ^ (0 : ℕ)⌋ = 7 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(7 : ℝ) * (71 / 51) ^ (1 : ℕ)⌋ = 9 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(7 : ℝ) * (71 / 51) ^ (2 : ℕ)⌋ = 13 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(7 : ℝ) * (71 / 51) ^ (3 : ℕ)⌋ = 18 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(7 : ℝ) * (71 / 51) ^ (4 : ℕ)⌋ = 26 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(7 : ℝ) * (71 / 51) ^ (5 : ℕ)⌋ = 36 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(7 : ℝ) * (71 / 51) ^ (6 : ℕ)⌋ = 50 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(7 : ℝ) * (71 / 51) ^ (7 : ℕ)⌋ = 70 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 7).image (fun n : ℕ => ⌊(7 : ℝ) * (71 / 51) ^ n⌋) = {7, 9, 13, 18, 26, 36, 50} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6]
      decide
    refine isGoodPair_of_run (7 : ℝ) (71 / 51 : ℝ) (by norm_num) (by norm_num) (by norm_num) 7 42 117 ?_ ?_ ?_
    · rw [himg, e7]; decide
    · rw [himg]; exact window_W9
    · omega
  · have e0 : ⌊(10 : ℝ) * (43 / 34) ^ (0 : ℕ)⌋ = 10 := by rw [Int.floor_eq_iff]; norm_num
    have e1 : ⌊(10 : ℝ) * (43 / 34) ^ (1 : ℕ)⌋ = 12 := by rw [Int.floor_eq_iff]; norm_num
    have e2 : ⌊(10 : ℝ) * (43 / 34) ^ (2 : ℕ)⌋ = 15 := by rw [Int.floor_eq_iff]; norm_num
    have e3 : ⌊(10 : ℝ) * (43 / 34) ^ (3 : ℕ)⌋ = 20 := by rw [Int.floor_eq_iff]; norm_num
    have e4 : ⌊(10 : ℝ) * (43 / 34) ^ (4 : ℕ)⌋ = 25 := by rw [Int.floor_eq_iff]; norm_num
    have e5 : ⌊(10 : ℝ) * (43 / 34) ^ (5 : ℕ)⌋ = 32 := by rw [Int.floor_eq_iff]; norm_num
    have e6 : ⌊(10 : ℝ) * (43 / 34) ^ (6 : ℕ)⌋ = 40 := by rw [Int.floor_eq_iff]; norm_num
    have e7 : ⌊(10 : ℝ) * (43 / 34) ^ (7 : ℕ)⌋ = 51 := by rw [Int.floor_eq_iff]; norm_num
    have e8 : ⌊(10 : ℝ) * (43 / 34) ^ (8 : ℕ)⌋ = 65 := by rw [Int.floor_eq_iff]; norm_num
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊(10 : ℝ) * (43 / 34) ^ n⌋) = {10, 12, 15, 20, 25, 32, 40, 51} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run (10 : ℝ) (43 / 34 : ℝ) (by norm_num) (by norm_num) (by norm_num) 8 69 136 ?_ ?_ ?_
    · rw [himg, e8]; decide
    · rw [himg]; exact window_W10
    · omega

end Erdos349

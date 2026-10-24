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
module

public import FormalConjecturesUtil

/-! # Erdős Problem 349

*Reference:* [erdosproblems.com/349](https://www.erdosproblems.com/349)
-/

@[expose] public section

namespace Erdos349

open Set Filter Real Nat Function


/--
This defines the core property of the problem: For what values of $t,\alpha \in (0,\infty)$
is the sequence $\lfloor t\alpha^n\rfloor$ complete?
-/
def IsGoodPair (t α : ℝ) : Prop :=
  IsAddComplete (range (fun n ↦ ⌊t * α ^ n⌋))

def erdos_349.answer : Set (ℝ × ℝ) := sorry

/--
For what values of $t,\alpha \in (0,\infty)$ is the sequence $\lfloor t\alpha^n\rfloor$ complete
(that is, all sufficiently large integers are the sum of distinct integers of the form $\lfloor t\alpha^n\rfloor$)?
-/
@[category research open, question value, AMS 11]
theorem erdos_349 :
    {(t, α) | 0 < t ∧ 0 < α ∧ IsGoodPair t α} = erdos_349.answer := by
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
For any $k$ there exists some $t_k\in (0,1)$ such that the set of $\alpha > 0$
such that the sequence $\lfloor t_k\alpha^n\rfloor$ is complete consists of at least $k$
disjoint line segments, that is, it has at least $k$ connected components.
-/
@[category research solved, AMS 11]
theorem exists_t_for_k_disjoint_segments (k : ℕ) :
    ∃ t ∈ Ioo 0 1,
      let S := {α | 0 < α ∧ IsGoodPair t α}
      k ≤ (connectedComponentIn S '' S).encard := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are odd infinitely
often and even infinitely often?
-/
@[category research open, question, AMS 11]
theorem erdos_349.variants.floor_3_halves_odd :
    {n | Odd ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are even infinitely often?
-/
@[category research open, question, AMS 11]
theorem erdos_349.variants.floor_3_halves_even :
    {n | Even ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
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
  "https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean"]
theorem alpha_le_one_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ¬ IsGoodPair t α := by
  sorry

/-- **Binary expansion.** Every natural number $k$ is a sum of distinct powers of two: there is
a finite set $E$ of exponents with $k = \sum_{i \in E} 2^i$. Proved by strong induction:
subtract the largest power $2^m \le k$, recurse on the remainder. A textbook-level building
block for `one_two_isGoodPair` below; it says nothing about `IsGoodPair` itself. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean#L319"]
theorem exists_finsetSum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := by
  sorry

/-- **The pair $(1, 2)$ is good.** The powers of two $\lfloor 1\cdot 2^n\rfloor = 2^n$ form an
additively complete set: every $k \ge 1$ is a finite sum of distinct powers of two. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean"]
theorem one_two_isGoodPair : IsGoodPair 1 2 := by
  sorry

/-- **The dyadic fiber at $\alpha = 2$.** For every $k$, the pair $(1/2^k, 2)$ is good: the
sequence $\lfloor 2^n / 2^k\rfloor$ is additively complete because at index $n = m + k$ it equals
the exact power $2^m$, so its range contains all powers of two, which already form an additively
complete set. Uses monotonicity `IsAddComplete.mono`. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean"]
theorem dyadic_two_isGoodPair (k : ℕ) : IsGoodPair (1 / 2 ^ k) 2 := by
  sorry

/-- **Integer leading coefficient $t \ge 2$ blocks completeness.** For every integer base
$\alpha$, the pair $(t, \alpha)$ with integer $t \ge 2$ is not good: $\lfloor t\alpha^n\rfloor =
t\alpha^n$ is a multiple of $t$, so every subset sum is too, but two consecutive large integers
cannot both be multiples of $t$. Generalizes the parity obstruction ($t = 2$). A partial result
on Erdős Problem 349. -/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
  "https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean"]
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
  "https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean"]
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

/-! ### Layer sharpening of the near-one strip for `t ≥ 2` (proof, sub-namespace `Layer`) -/

namespace Layer

/-- **Distinct-value prefix sum.** $C\ a\ N = \sum$ of the *distinct* values among
$a_0, \ldots, a_{N-1}$. This is the relevant "running reachable total" for subset sums over
the SET $\operatorname{range} a$ (duplicate values are counted once). -/
noncomputable def C (a : ℕ → ℤ) (N : ℕ) : ℤ := ∑ x ∈ (Finset.range N).image a, x

/-! ## §2. Toolbox for `C` (from `349/SmallT.lean` §2 via `349/DeficitWindow.lean` §1) -/

/-- A duplicate value leaves `C` unchanged. -/
lemma C_succ_of_mem (a : ℕ → ℤ) {n : ℕ} (h : a n ∈ (Finset.range n).image a) :
    C a (n + 1) = C a n := by
  have himg : (Finset.range (n + 1)).image a = (Finset.range n).image a := by
    rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr h]
  simp only [C, himg]

/-- A genuinely new value increases `C` by exactly itself. -/
lemma C_succ_of_notMem (a : ℕ → ℤ) {n : ℕ} (h : a n ∉ (Finset.range n).image a) :
    C a (n + 1) = a n + C a n := by
  have himg : (Finset.range (n + 1)).image a = insert (a n) ((Finset.range n).image a) := by
    rw [Finset.range_add_one, Finset.image_insert]
  simp only [C, himg, Finset.sum_insert h]

/-- Each term is dominated by the prefix sum containing it (all terms being nonnegative). -/
lemma le_C_succ (a : ℕ → ℤ) (hnn : ∀ n, 0 ≤ a n) (n : ℕ) : a n ≤ C a (n + 1) := by
  have hmem : a n ∈ (Finset.range (n + 1)).image a := by
    rw [Finset.mem_image]; exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
  have : a n ≤ ∑ x ∈ (Finset.range (n + 1)).image a, x := by
    apply Finset.single_le_sum (f := id) _ hmem
    intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
  simpa [C] using this

/-! ## §3. Sub-lemma 4 — the deficit engine

The CLOSED `eventuallyComplete_of_brown_of_base_window` (`349/T2Crux.lean` §3) with a deficit
parameter `D` added: the covered window stops `D` short of the top of the prefix sum, and the
Brown condition pays for it. Every line of the original proof survives with `C a N` replaced by
`C a N − D`, and the final unboundedness call applied at `k + D` instead of `k`. -/

/-- **THE DEFICIT ENGINE** (sub-lemma 4 of `349/STRATEGY-4.md`).

Assume $a : \mathbb{N} \to \mathbb{Z}$ is nonnegative, monotone and unbounded, and that there
are a rank $N_0$, a threshold $L$ and a **deficit** $D$ such that

* `hbase` — every integer $k$ with $L \le k \le C\,a\,N_0 - D$ is already a subset sum of the
  first $N_0$ values $\{a_0, \dots, a_{N_0-1}\}$ (an **interior** window: for $D > 0$ it does
  not reach the top $C\,a\,N_0$, which is exactly what makes the hypothesis satisfiable when
  every value is $\ge 2$);
* `hbrown` — the $(L+D)$-shifted Brown margin $a_n + L + D \le 1 + C\,a\,n$ for every
  $n \ge N_0$.

Then $\operatorname{range} a$ is additively complete in the eventual sense; the proof in fact
shows the sharp statement that **every** $k \ge L$ is a finite subset sum of
$\operatorname{range} a$.

Taking $D = 0$ recovers `eventuallyComplete_of_brown_of_base_window` verbatim.

`hmono` is retained only for signature compatibility with the instantiation lemmas; the
induction does not use it. No numeric constant, rank or gap bound is hard-coded: $N_0$, $L$ and
$D$ are parameters. -/
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
  -- plumbing: `C` dominates each term and is monotone in `N`
  have hmemC : ∀ N, a N ≤ C a (N + 1) := le_C_succ a hnn
  have hCmono : Monotone (C a) := by
    intro M N hMN
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.image_subset_image (Finset.range_subset_range.mpr hMN)
    · intro x hx _; rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
  -- the merge induction, started at the given (interior) base window
  have key : ∀ N : ℕ, N₀ ≤ N → ∀ k : ℤ, L ≤ k → k ≤ C a N - D →
      k ∈ subsetSums (((Finset.range N).image a : Finset ℤ) : Set ℤ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hbase
    | succ N hN ih =>
      intro k hkL hkC
      by_cases hnew : a N ∈ (Finset.range N).image a
      · -- the new value is a duplicate: nothing changes
        have himg : (Finset.range (N + 1)).image a = (Finset.range N).image a := by
          rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr hnew]
        have hCC : C a (N + 1) = C a N := by simp only [C, himg]
        rw [hCC] at hkC
        rw [himg]
        exact ih k hkL hkC
      · -- genuinely new value: `C a (N+1) = a N + C a N`, merge the two windows
        have himg : (Finset.range (N + 1)).image a
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
          -- here `hbrown` is consumed: `k - a N` lands back inside `[L, C a N - D]`
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
  -- conclude: every `k ≥ L` is a subset sum of `Set.range a`
  rw [IsAddComplete, eventually_atTop]
  refine ⟨L, fun k hk => ?_⟩
  -- the deficit is absorbed here: reach `k + D`, not merely `k`
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

/-! ## §4. Sub-lemmas 1, 2, 3, 5, 6 — the floor sequence on the near-one strip -/

/-- **Nonnegativity** (engine hypothesis `hnn`); from `349/T2Instances.lean`, CLOSED. -/
theorem floorSeq_nonneg (t α : ℝ) (ht : 0 ≤ t) (hα : 0 ≤ α) (n : ℕ) :
    0 ≤ ⌊t * α ^ n⌋ :=
  Int.floor_nonneg.mpr (mul_nonneg ht (pow_nonneg hα n))

/-- **Monotonicity** (engine hypothesis `hmono`); from `349/T2Instances.lean`, CLOSED. -/
theorem floorSeq_mono (t α : ℝ) (ht : 0 ≤ t) (hα : 1 ≤ α) :
    Monotone (fun n : ℕ => ⌊t * α ^ n⌋) := by
  intro m n hmn
  simp only
  exact Int.floor_le_floor (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα hmn) ht)

/-- **Unboundedness** (engine hypothesis `hub`); from `349/T2Instances.lean`, CLOSED. -/
theorem floorSeq_unbounded (t α : ℝ) (ht : 0 < t) (hα1 : 1 < α) :
    ∀ M : ℤ, ∃ n : ℕ, M ≤ ⌊t * α ^ n⌋ := by
  intro M
  have htend : Tendsto (fun n : ℕ => t * α ^ n) atTop atTop :=
    Tendsto.const_mul_atTop ht (tendsto_pow_atTop_atTop_of_one_lt hα1)
  obtain ⟨n, hn⟩ := (htend.eventually_ge_atTop (M : ℝ)).exists
  exact ⟨n, Int.le_floor.mpr hn⟩

/-- **Doubling bound**, verbatim from `349/StripIff.lean` (`floor_mul_pow_succ_le_two_mul`,
CLOSED). Needs only $1 \le t$ and $\alpha < 3/2$, both comfortably satisfied on the near-one
strip ($t \ge 2$ and $\alpha \le 1 + 1/M \le 7/6$). -/
theorem floor_mul_pow_succ_le_two_mul (α t : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (n : ℕ) :
    ⌊t * α ^ (n + 1)⌋ ≤ 2 * ⌊t * α ^ n⌋ := by
  have hpos : (0:ℝ) < α ^ n := by positivity
  have hone : (1:ℝ) ≤ α ^ n := one_le_pow₀ (le_of_lt hα_lo)
  have htpow : (1:ℝ) ≤ t * α ^ n := by nlinarith [ht1, hone]
  have hm1 : (1:ℤ) ≤ ⌊t * α ^ n⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hflo : (↑(⌊t * α ^ n⌋):ℝ) ≤ t * α ^ n := Int.floor_le _
  have hfle : (t * α ^ n) - 1 < ↑(⌊t * α ^ n⌋) := by
    have := Int.sub_one_lt_floor (t * α ^ n); linarith
  rw [Int.floor_le_iff]
  push_cast
  have hsucc : t * α ^ (n + 1) = α * (t * α ^ n) := by ring
  rw [hsucc]
  have hm1r : (1:ℝ) ≤ (↑(⌊t * α ^ n⌋):ℝ) := by exact_mod_cast hm1
  nlinarith [mul_pos (by linarith : (0:ℝ) < α) (by nlinarith [htpow] : (0:ℝ) < t * α ^ n),
    hflo, hfle, hm1r]

/-- **Sub-lemma 1.** $a_0 = \lfloor t\rfloor$ — the sequence starts at the integer part of $t$,
with no dependence on $\alpha$. (This is what makes the *top*-anchored window of
`349/T2Crux.lean` §3 void for $t \ge 2$: $a_0 = \lfloor t\rfloor \ge 2$.) -/
theorem floorSeq_zero_eq_floor (t α : ℝ) : ⌊t * α ^ (0 : ℕ)⌋ = ⌊t⌋ := by
  norm_num

/-- The near-one hypothesis $\alpha \le 1 + 1/M$, cleared of denominators:
$M(\alpha - 1) \le 1$. -/
private lemma mul_sub_one_le_one_of_near_one {α : ℝ} {M : ℤ} (hM : 1 ≤ M)
    (hα : α ≤ 1 + 1 / (M : ℝ)) : (M : ℝ) * (α - 1) ≤ 1 := by
  have hMR : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h := mul_le_mul_of_nonneg_left (by linarith : α - 1 ≤ 1 / (M : ℝ)) hMR.le
  rwa [mul_one_div, div_self (ne_of_gt hMR)] at h

/-- **Sub-lemma 2 — contiguity step.** On the near-one strip $1 < \alpha \le 1 + 1/M$, as long
as the sequence stays at most $M - 1$ it can increase by at most $1$.

Indeed $a_n \le M - 1$ gives $t\alpha^n < M$, hence
$t\alpha^{n+1} = t\alpha^n + t\alpha^n(\alpha-1) < t\alpha^n + M(\alpha-1)
\le t\alpha^n + 1 < a_n + 2$. -/
theorem floorSeq_succ_le_succ_of_lt (t α : ℝ) (M : ℤ) (n : ℕ)
    (ht : 0 ≤ t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (h : ⌊t * α ^ n⌋ ≤ M - 1) :
    ⌊t * α ^ (n + 1)⌋ ≤ ⌊t * α ^ n⌋ + 1 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hx0 : (0:ℝ) ≤ t * α ^ n := mul_nonneg ht (pow_nonneg hα0.le n)
  have hxM : t * α ^ n < (M : ℝ) := Int.floor_lt.mp (by omega)
  have hMa := mul_sub_one_le_one_of_near_one hM hα
  have hkey : (t * α ^ n) * (α - 1) < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hxM) (sub_pos.mpr hα1)]
  have hfl : t * α ^ n < (⌊t * α ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : t * α ^ (n + 1) < ((⌊t * α ^ n⌋ + 2 : ℤ) : ℝ) := by
    have hsucc : t * α ^ (n + 1) = t * α ^ n + (t * α ^ n) * (α - 1) := by ring
    push_cast
    rw [hsucc]
    linarith
  have := Int.floor_lt.mpr hlt
  omega

/-- **Sub-lemma 3 — the term just past the cut.** On the near-one strip, one step after a term
that is at most $M$ the sequence is at most $M + 2$.

Indeed $a_n \le M$ gives $t\alpha^n < M + 1$, hence
$t\alpha^{n+1} = t\alpha^n + t\alpha^n(\alpha-1) < (M+1) + (M(\alpha-1) + (\alpha-1))
\le (M+1) + 2 = M + 3$.

Applied at $n = N_0 - 1$, where $N_0$ is the first rank with $a_{N_0} > M$, this is step 5 of
`349/STRATEGY-4.md` §3: $a_{N_0} \le M + 2$. It is stated in this one-step form so that no
`Nat.find` appears inside the lemma. -/
theorem floorSeq_le_add_two_at_cut (t α : ℝ) (M : ℤ) (n : ℕ)
    (ht : 0 ≤ t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (h : ⌊t * α ^ n⌋ ≤ M) :
    ⌊t * α ^ (n + 1)⌋ ≤ M + 2 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hMR : (1:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hx0 : (0:ℝ) ≤ t * α ^ n := mul_nonneg ht (pow_nonneg hα0.le n)
  have hxM : t * α ^ n < (M : ℝ) + 1 := by
    have : t * α ^ n < ((M + 1 : ℤ) : ℝ) := Int.floor_lt.mp (by omega)
    push_cast at this; linarith
  have hMa := mul_sub_one_le_one_of_near_one hM hα
  have hsmall : α - 1 ≤ 1 := by nlinarith
  have hkey : (t * α ^ n) * (α - 1) < 2 := by
    nlinarith [mul_pos (sub_pos.mpr hxM) (sub_pos.mpr hα1)]
  have hlt : t * α ^ (n + 1) < ((M + 3 : ℤ) : ℝ) := by
    have hsucc : t * α ^ (n + 1) = t * α ^ n + (t * α ^ n) * (α - 1) := by ring
    push_cast
    rw [hsucc]
    linarith
  have := Int.floor_lt.mpr hlt
  omega

/-- **Sub-lemma 5 — the block is swept (discrete IVT).** On the near-one strip
$1 < \alpha \le 1 + 1/M$, every integer $v$ of the block $[\lfloor t\rfloor, M]$ is *attained*
by the sequence.

Take the least $n$ with $v \le a_n$ (it exists: the sequence is unbounded). If $n = 0$ then
$v \le a_0 = \lfloor t\rfloor \le v$. Otherwise $n = k+1$ with $a_k \le v - 1 \le M - 1$, so
sub-lemma 2 gives $a_{k+1} \le a_k + 1 \le v$, and minimality gives $v \le a_{k+1}$. -/
theorem floorSeq_covers_Icc (t α : ℝ) (M : ℤ)
    (ht : 0 < t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (v : ℤ) (hv1 : ⌊t⌋ ≤ v) (hv2 : v ≤ M) :
    ∃ n : ℕ, ⌊t * α ^ n⌋ = v := by
  classical
  have hex : ∃ n : ℕ, v ≤ ⌊t * α ^ n⌋ := floorSeq_unbounded t α ht hα1 v
  obtain ⟨N, hN, hmin⟩ : ∃ N : ℕ, v ≤ ⌊t * α ^ N⌋ ∧ ∀ j, j < N → ⌊t * α ^ j⌋ < v :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => by have := Nat.find_min hex hj; omega⟩
  refine ⟨N, ?_⟩
  cases N with
  | zero =>
    rw [floorSeq_zero_eq_floor] at hN ⊢
    omega
  | succ k =>
    have hk : ⌊t * α ^ k⌋ < v := hmin k (Nat.lt_succ_self k)
    have hstep := floorSeq_succ_le_succ_of_lt t α M k ht.le hM hα1 hα (by omega)
    omega

/-- **Sub-lemma 6 — the clean cut.** Let $N_0$ be the first rank at which the sequence exceeds
$M$ (given here by its two defining properties, so that no `Nat.find` appears in the statement).
Then the distinct values produced before the cut are **exactly** the block
$[\lfloor t\rfloor, M]$.

$\subseteq$ is monotonicity ($a_j \ge a_0 = \lfloor t\rfloor$) plus minimality of $N_0$
($a_j \le M$); $\supseteq$ is sub-lemma 5, whose witness $n$ must satisfy $n < N_0$ since
$a_n \le M < a_{N_0}$ and $a$ is monotone. -/
theorem floorSeq_image_range_cut (t α : ℝ) (M : ℤ)
    (ht : 0 < t) (hM : 1 ≤ M) (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (N₀ : ℕ) (hN₀ : M < ⌊t * α ^ N₀⌋) (hN₀min : ∀ j, j < N₀ → ⌊t * α ^ j⌋ ≤ M) :
    (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) = Finset.Icc ⌊t⌋ M := by
  have hmono := floorSeq_mono t α ht.le hα1.le
  ext v
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, hN₀min j hj⟩
    have h0 : ⌊t * α ^ (0 : ℕ)⌋ ≤ ⌊t * α ^ j⌋ := hmono (Nat.zero_le j)
    rw [floorSeq_zero_eq_floor] at h0
    exact h0
  · rintro ⟨hv1, hv2⟩
    obtain ⟨n, hn⟩ := floorSeq_covers_Icc t α M ht hM hα1 hα v hv1 hv2
    refine ⟨n, ?_, hn⟩
    by_contra hcon
    have hle : ⌊t * α ^ N₀⌋ ≤ ⌊t * α ^ n⌋ := hmono (by omega)
    omega

/-! ## §5. Sub-lemma 8 — the shifted Brown condition

The one delicate induction. A naive induction on $a_n + L + D \le 1 + C\,a\,n$ does **not**
close: on a step where $a_{n+1}$ repeats an earlier value, $C$ stalls while $a$ may still move.
The fix is the *stronger*, duplicate-proof invariant

$$ T(n) : \quad 2 a_n + L + D \le 1 + C\,a\,(n+1), $$

for which the duplicate case is an identity ($a_{n+1} = a_n$ and $C\,a\,(n+2) = C\,a\,(n+1)$,
so $T(n+1)$ *is* $T(n)$) and the new-value case is $T(n)$ plus the doubling bound. -/

/-- **Abstract core of sub-lemma 8.** For a monotone sequence satisfying the doubling bound
$a_{n+1} \le 2 a_n$, whose value at a rank $N_0$ is new and satisfies the base inequality
$a_{N_0} + L + D \le 1 + C\,a\,N_0$, the shifted Brown condition propagates to every
$n \ge N_0$. -/
theorem brown_shifted_of_doubling (a : ℕ → ℤ) (L D : ℤ) (N₀ : ℕ)
    (hmono : Monotone a)
    (hdouble : ∀ n, a (n + 1) ≤ 2 * a n)
    (hnew : a N₀ ∉ (Finset.range N₀).image a)
    (hbase : a N₀ + L + D ≤ 1 + C a N₀) :
    ∀ n : ℕ, N₀ ≤ n → a n + L + D ≤ 1 + C a n := by
  classical
  -- the strengthened, duplicate-proof invariant
  have hT : ∀ n : ℕ, N₀ ≤ n → 2 * a n + L + D ≤ 1 + C a (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [C_succ_of_notMem a hnew]
      omega
    | succ n _ ih =>
      by_cases hdup : a (n + 1) ∈ (Finset.range (n + 1)).image a
      · -- duplicate: `a (n+1) = a n` and `C` stalls, so the invariant is unchanged
        have heq : a (n + 1) = a n := by
          rw [Finset.mem_image] at hdup
          obtain ⟨j, hj, hja⟩ := hdup
          have h1 : a j ≤ a n := hmono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          have h2 : a n ≤ a (n + 1) := hmono (Nat.le_succ n)
          omega
        rw [C_succ_of_mem a hdup, heq]
        exact ih
      · -- genuinely new value: `C` grows by `a (n+1)`, and the doubling bound closes the gap
        rw [C_succ_of_notMem a hdup]
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

/-- **Sub-lemma 8 — the shifted Brown condition for the floor sequence.** Instance of
`brown_shifted_of_doubling` for $a_n = \lfloor t\alpha^n\rfloor$, whose doubling bound is
`floor_mul_pow_succ_le_two_mul` (valid since $1 \le t$ and $\alpha < 3/2$). -/
theorem floorSeq_brown_shifted (t α : ℝ) (L D : ℤ) (N₀ : ℕ)
    (ht : 1 ≤ t) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋))
    (hbase : ⌊t * α ^ N₀⌋ + L + D ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) N₀) :
    ∀ n : ℕ, N₀ ≤ n →
      ⌊t * α ^ n⌋ + L + D ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) n :=
  brown_shifted_of_doubling (fun n : ℕ => ⌊t * α ^ n⌋) L D N₀
    (floorSeq_mono t α (by linarith) hα1.le)
    (fun n => floor_mul_pow_succ_le_two_mul α t hα1 hα2 ht n)
    hnew hbase

/-! ## §6. The generalised assembly — the window `[L, U]` carried as a parameter

`349/TwoLeFinal.lean` §6 hard-codes `L = M/2 + 1` and `U = M + ∑_{v ∈ ⟦⌊t⌋, M/2⟧} v`, the window
its merge chain happens to produce, and pays for that choice with the hypothesis
`M ≥ 2⌊t⌋ + 2`. Nothing in the deficit engine needs those particular values: with the canonical
deficit `D := C a N₀ − U` the engine's base inequality `a N₀ + L + D ≤ 1 + C a N₀` collapses,
using `a N₀ ≤ M + 2` (§4), to the single **length condition** `M + L + 1 ≤ U`.

This is `isGoodPair_of_two_le_of_window` with `(L, U)` freed; instantiating `L := M/2 + 1`,
`U := M + S₁` recovers it verbatim. -/

/-- **The near-one strip, modulo an arbitrary base window.** For `t ≥ 2`, an integer `M > ⌊t⌋`
and `1 < α ≤ 1 + 1/M`, the pair `(t, α)` is good as soon as the subset sums of the block
`⟦⌊t⌋, M⟧` cover *some* interval `[L, U]` with `U ≥ M + L + 1`.

`hmM` is not decoration: it is what makes the block non-empty, hence what forbids the cut rank
`N₀` from being `0`. `349/TwoLeFinal.lean` got it for free from `M ≥ 2⌊t⌋ + 2`; freeing `M`
exposes it. Together with `⌊t⌋ ≥ 2` it also delivers `M ≥ 3`, whence `α ≤ 4/3 < 3/2` and the
doubling bound the Brown condition consumes. -/
theorem isGoodPair_of_two_le_of_run (t α : ℝ) (M L U : ℤ)
    (ht : 2 ≤ t) (hmM : ⌊t⌋ < M)
    (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ))
    (hfit : M + L + 1 ≤ U)
    (hwin : ∀ k : ℤ, L ≤ k → k ≤ U →
      k ∈ subsetSums ((Finset.Icc ⌊t⌋ M : Finset ℤ) : Set ℤ)) :
    IsGoodPair t α := by
  classical
  have ht0 : (0:ℝ) < t := by linarith
  have hα0 : (0:ℝ) < α := by linarith
  have hm2 : (2:ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by exact_mod_cast ht)
  have hM : (3:ℤ) ≤ M := by omega
  have hM1 : (1:ℤ) ≤ M := by omega
  -- on the strip, `α ≤ 1 + 1/M ≤ 4/3 < 3/2`
  have hα32 : α < 3 / 2 := by
    have hMR : (3:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : 1 / (M : ℝ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  -- the cut rank `N₀`: the first index at which the sequence exceeds `M`
  have hex : ∃ n : ℕ, M < ⌊t * α ^ n⌋ := by
    obtain ⟨n, hn⟩ := floorSeq_unbounded t α ht0 hα1 (M + 1); exact ⟨n, by omega⟩
  obtain ⟨N₀, hN₀, hN₀min⟩ : ∃ N₀ : ℕ, M < ⌊t * α ^ N₀⌋ ∧ ∀ j, j < N₀ → ⌊t * α ^ j⌋ ≤ M :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => by have := Nat.find_min hex hj; omega⟩
  -- the values before the cut are exactly the block `⟦⌊t⌋, M⟧`
  have himg : (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) = Finset.Icc ⌊t⌋ M :=
    floorSeq_image_range_cut t α M ht0 hM1 hα1 hα N₀ hN₀ hN₀min
  have hC : C (fun n : ℕ => ⌊t * α ^ n⌋) N₀ = ∑ v ∈ Finset.Icc ⌊t⌋ M, v := by
    simp only [C, himg]
  -- the term just past the cut is at most `M + 2`
  have hcut : ⌊t * α ^ N₀⌋ ≤ M + 2 := by
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, N₀ = p + 1 := by
      cases N₀ with
      | zero =>
        rw [floorSeq_zero_eq_floor] at hN₀
        omega
      | succ p => exact ⟨p, rfl⟩
    exact floorSeq_le_add_two_at_cut t α M p ht0.le hM1 hα1 hα (hN₀min p (Nat.lt_succ_self p))
  -- the base inequality, now *equivalent* to the length condition `hfit`
  have hbaseineq : ⌊t * α ^ N₀⌋ + L + (∑ v ∈ Finset.Icc ⌊t⌋ M, v - U)
      ≤ 1 + C (fun n : ℕ => ⌊t * α ^ n⌋) N₀ := by
    rw [hC]; omega
  have hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) := by
    intro hmem
    rw [himg, Finset.mem_Icc] at hmem
    omega
  show IsAddComplete (Set.range fun n : ℕ => ⌊t * α ^ n⌋)
  refine eventuallyComplete_of_brown_of_deficit_window (fun n : ℕ => ⌊t * α ^ n⌋)
    (fun n => floorSeq_nonneg t α ht0.le hα0.le n) (floorSeq_mono t α ht0.le hα1.le)
    (floorSeq_unbounded t α ht0 hα1) N₀ L (∑ v ∈ Finset.Icc ⌊t⌋ M, v - U) ?_ ?_
  · -- `hbase`: `C a N₀ - D` is exactly `U`, and `hwin` covers `[L, U]`
    intro k hkL hkC
    rw [hC] at hkC
    rw [himg]
    exact hwin k hkL (by omega)
  · exact floorSeq_brown_shifted t α L (∑ v ∈ Finset.Icc ⌊t⌋ M, v - U) N₀
      (by linarith) hα1 hα32 hnew hbaseineq

/-! ## §7. The layer machinery

The combinatorial content, replacing `349/TwoLeFinal.lean` §7's merge chain. All of it is gated
by `349/t5b-check.md` (script `349/t5b-layers.py`, verdict **VRAI**, four negative controls). -/

/-- `Tri j = 0 + 1 + ⋯ + (j−1)`, kept as a `Finset.range` sum so that no integer division ever
enters the arithmetic. -/
def Tri (j : ℕ) : ℤ := ∑ i ∈ Finset.range j, (i : ℤ)

@[simp] lemma Tri_zero : Tri 0 = 0 := by simp [Tri]

lemma Tri_succ (j : ℕ) : Tri (j + 1) = Tri j + (j : ℤ) := by
  simp [Tri, Finset.sum_range_succ]

/-- Gauss's identity in the division-free form every inequality below consumes. -/
lemma two_Tri (j : ℕ) : 2 * Tri j = (j : ℤ) * ((j : ℤ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Tri_succ]
    push_cast
    linarith

/-- **The staircase construction** (`t5b-layers.py` C3). Fix a base `m` and a free width
`w ≥ 0`. For every `j` and every budget `0 ≤ r ≤ j·w` there is a `j`-element set `B` of integers
lying in `⟦m, m + j − 1 + min w r⟧` — note the upper bound is itself throttled by the budget —
with `∑ B = j·m + Tri j + r`.

Induction on `j`, peeling the **largest** element `m + (j−1) + min w r`. The recursive call runs
on the budget `r − min w r`, and the monotonicity `min w (r − min w r) ≤ min w r` is exactly what
places the whole recursive set strictly below the peeled element — which is what makes the
`insert` legal and the cardinality grow. -/
theorem staircase_exists (m w : ℤ) (hw : 0 ≤ w) :
    ∀ (j : ℕ) (r : ℤ), 0 ≤ r → r ≤ (j : ℤ) * w →
      ∃ B : Finset ℤ, (∀ x ∈ B, m ≤ x ∧ x ≤ m + (j : ℤ) - 1 + min w r) ∧
        B.card = j ∧ ∑ v ∈ B, v = (j : ℤ) * m + Tri j + r := by
  intro j
  induction j with
  | zero =>
    intro r hr0 hr
    have hr' : r = 0 := le_antisymm (by simpa using hr) hr0
    exact ⟨∅, by simp, by simp, by simp [hr', Tri]⟩
  | succ j ih =>
    intro r hr0 hr
    have hjnn : (0:ℤ) ≤ (j:ℤ) := by positivity
    have hjw0 : (0:ℤ) ≤ (j:ℤ) * w := mul_nonneg hjnn hw
    set g : ℤ := min w r with hg
    have hg0 : 0 ≤ g := le_min hw hr0
    have hgw : g ≤ w := min_le_left _ _
    have hgr : g ≤ r := min_le_right _ _
    have hr' : r ≤ (j:ℤ) * w + w := by push_cast at hr; linarith
    have hrec0 : 0 ≤ r - g := by linarith
    have hrecle : r - g ≤ (j:ℤ) * w := by
      rcases le_total r w with h | h
      · have hgeq : g = r := by rw [hg]; exact min_eq_right h
        linarith
      · have hgeq : g = w := by rw [hg]; exact min_eq_left h
        linarith
    obtain ⟨B, hBmem, hBcard, hBsum⟩ := ih (r - g) hrec0 hrecle
    set g' : ℤ := min w (r - g) with hg'
    have hg'g : g' ≤ g := by
      simp only [hg', hg]
      exact min_le_min le_rfl (by linarith)
    have hyB : m + (j:ℤ) + g ∉ B := by
      intro hmem
      have h := (hBmem (m + (j:ℤ) + g) hmem).2
      linarith
    refine ⟨insert (m + (j:ℤ) + g) B, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact ⟨by linarith, by push_cast; linarith⟩
      · exact ⟨(hBmem x hxB).1, by have := (hBmem x hxB).2; push_cast; linarith⟩
    · rw [Finset.card_insert_of_notMem hyB, hBcard]
    · rw [Finset.sum_insert hyB, hBsum, Tri_succ]
      push_cast
      ring

/-- **The layer lemma** (`t5b-layers.py` C1, "if" half). Every integer of
`⟦j·m + Tri j, j·M − Tri j⟧` — the exact range of the sums of `j` distinct elements of the block
`⟦m, M⟧` — is a subset sum of that block.

Only this half is needed; the converse (that no *other* integer is a `j`-element sum) is true
and measured, but never consumed. -/
theorem layer_mem_subsetSums (m M : ℤ) (j : ℕ) (hjM : (j : ℤ) ≤ M - m + 1) :
    ∀ k : ℤ, (j : ℤ) * m + Tri j ≤ k → k ≤ (j : ℤ) * M - Tri j →
      k ∈ subsetSums ((Finset.Icc m M : Finset ℤ) : Set ℤ) := by
  intro k hk1 hk2
  set w : ℤ := M - m - (j : ℤ) + 1 with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  set r : ℤ := k - ((j : ℤ) * m + Tri j) with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hjw : (j : ℤ) * w = (j : ℤ) * M - (j : ℤ) * m - 2 * Tri j := by
    rw [hw, two_Tri]; ring
  have hrjw : r ≤ (j : ℤ) * w := by rw [hr, hjw]; linarith
  obtain ⟨B, hBmem, _, hBsum⟩ := staircase_exists m w hw0 j r hr0 hrjw
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    have hx' := hBmem x (Finset.mem_coe.mp hx)
    have hmin : min w r ≤ w := min_le_left _ _
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hx'.1, by have := hx'.2; linarith⟩)
  · rw [hBsum, hr]; ring

/-- **Two abutting layers** (`t5b-layers.py` C2). If `m − 1 ≤ j·(M − m − j)` then layers `j` and
`j + 1` of the block `⟦m, M⟧` overlap or abut, so their union
`⟦j·m + Tri j, (j+1)·M − Tri (j+1)⟧` is entirely covered by subset sums of the block.

The hypothesis is exactly `Lo (j+1) ≤ Hi j + 1` after clearing `Tri` with `two_Tri`. -/
theorem two_layer_run (m M : ℤ) (j : ℕ) (hj : 1 ≤ j) (hm : 2 ≤ m)
    (habut : m - 1 ≤ (j : ℤ) * (M - m - (j : ℤ))) :
    ∀ k : ℤ, (j : ℤ) * m + Tri j ≤ k → k ≤ ((j : ℤ) + 1) * M - Tri (j + 1) →
      k ∈ subsetSums ((Finset.Icc m M : Finset ℤ) : Set ℤ) := by
  intro k h1 h2
  have hj1 : (1:ℤ) ≤ (j:ℤ) := by exact_mod_cast hj
  have habut' : m - 1 ≤ (j:ℤ) * M - (j:ℤ) * m - (j:ℤ) * (j:ℤ) := by
    have hring : (j : ℤ) * (M - m - (j : ℤ)) = (j:ℤ) * M - (j:ℤ) * m - (j:ℤ) * (j:ℤ) := by ring
    linarith [habut, hring.symm.le, hring.le]
  -- the abut hypothesis forces the block to be wide enough for BOTH layers to exist
  have hgap : 1 ≤ M - m - (j:ℤ) := by nlinarith [habut, hj1, hm]
  have hcast : ((j + 1 : ℕ) : ℤ) = (j:ℤ) + 1 := by push_cast; ring
  by_cases hlo : k ≤ (j:ℤ) * M - Tri j
  · exact layer_mem_subsetSums m M j (by linarith) k h1 hlo
  · rw [not_le] at hlo
    refine layer_mem_subsetSums m M (j + 1) (by rw [hcast]; linarith) k ?_ ?_
    · rw [hcast, Tri_succ]
      linarith [two_Tri j]
    · rw [hcast]; exact h2

/-- The **run-length identity**: the top of layer `j+1` sits exactly `j·(M − m − j)` above
`M` plus the bottom of layer `j`. So the abut hypothesis of `two_layer_run` and the length
condition `hfit` of `isGoodPair_of_two_le_of_run` are, for `m ≥ 2`, *the same inequality* —
which is why no union over further layers is needed. -/
theorem two_layer_fit (m M : ℤ) (j : ℕ) :
    ((j : ℤ) + 1) * M - Tri (j + 1) - ((j : ℤ) * m + Tri j) - M
      = (j : ℤ) * (M - m - (j : ℤ)) := by
  rw [Tri_succ]
  linarith [two_Tri j]

/-! ## §8. The sharpened strip -/

/-- **THE THEOREM (sharpened near-one strip, all `t ≥ 2`), `M`-parametrised.** For `t ≥ 2` and
any `j ≥ 1` and integer `M` with `⌊t⌋ − 1 ≤ j·(M − ⌊t⌋ − j)`, every `α` with `1 < α ≤ 1 + 1/M`
makes `(t, α)` a good pair.

Taking `j` to maximise `j·(M − ⌊t⌋ − j)` — i.e. `j ≈ (M − ⌊t⌋)/2` — this admits every `M` with
`⌊(M − ⌊t⌋)²/4⌋ ≥ ⌊t⌋ − 1`, the sharp threshold measured by `349/t5b-layers.py` (C6a). -/
theorem isGoodPair_of_two_le_of_layer (t α : ℝ) (M : ℤ) (j : ℕ)
    (ht : 2 ≤ t) (hj : 1 ≤ j)
    (habut : ⌊t⌋ - 1 ≤ (j : ℤ) * (M - ⌊t⌋ - (j : ℤ)))
    (hα1 : 1 < α) (hα : α ≤ 1 + 1 / (M : ℝ)) :
    IsGoodPair t α := by
  have hm2 : (2:ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by exact_mod_cast ht)
  have hj1 : (1:ℤ) ≤ (j:ℤ) := by exact_mod_cast hj
  have hgap : 1 ≤ M - ⌊t⌋ - (j:ℤ) := by nlinarith [habut, hj1, hm2]
  refine isGoodPair_of_two_le_of_run t α M ((j:ℤ) * ⌊t⌋ + Tri j)
    (((j:ℤ) + 1) * M - Tri (j + 1)) ht (by linarith) hα1 hα ?_ ?_
  · linarith [two_layer_fit ⌊t⌋ M j]
  · exact two_layer_run ⌊t⌋ M j hj hm2 habut

/-- **THE HEADLINE THEOREM.** For every `t ≥ 2`, every `j ≥ 1` with `j² ≥ ⌊t⌋ − 1`, and every `α`
with
$$ 1 < \alpha \le 1 + \frac{1}{\lfloor t\rfloor + 2j}, $$
the pair `(t, α)` is good.

Against `isGoodPair_of_two_le` of `349/TwoLeFinal.lean` (denominator `2⌊t⌋ + 2`) the admissible
denominator drops from `2m + 2` to `m + 2⌈√(m−1)⌉` — a measured widening of `1.25×` at `m = 4`,
`1.49×` at `m = 25`, `1.76×` at `m = 200` (`349/t5b-layers.py` C7).

PARTIAL: the band `t ≥ 2`, `1 < α < 3/2` remains **OPEN**; this is still a strip around
`α = 1`, merely a wider one. -/
theorem isGoodPair_of_two_le_layer_sq (t α : ℝ) (j : ℕ)
    (ht : 2 ≤ t) (hj : 1 ≤ j) (hsq : ⌊t⌋ - 1 ≤ (j : ℤ) * (j : ℤ))
    (hα1 : 1 < α) (hα : α ≤ 1 + 1 / ((⌊t⌋ + 2 * (j : ℤ) : ℤ) : ℝ)) :
    IsGoodPair t α := by
  refine isGoodPair_of_two_le_of_layer t α (⌊t⌋ + 2 * (j:ℤ)) j ht hj ?_ hα1 hα
  have hrw : (j:ℤ) * ((⌊t⌋ + 2 * (j:ℤ)) - ⌊t⌋ - (j:ℤ)) = (j:ℤ) * (j:ℤ) := by ring
  rw [hrw]
  exact hsq

/-! ## §9. Non-vacuity, and the comparison with the published strip

Both witnesses are strictly outside `isGoodPair_of_two_le` of `349/TwoLeFinal.lean`, and neither
is one of the 21 isolated good pairs of `349/RunLemma.lean` / `349/RunLemma2.lean` (those all
have `t ∈ {2, 5/2, 3, 4, 5, 7, 10}`). -/

/-- **Non-vacuity 1 — the `t ∈ [2,3)` layer.** `(29/10, 5/4)`: here `⌊t⌋ = 2`, `j = 1`
(`j² = 1 ≥ 1`), so `M = 4` and the strip reaches `1 + 1/4 = 5/4`, attained with equality.
The published strip for `⌊t⌋ = 2` stops at `1 + 1/6 = 7/6 < 5/4`. -/
theorem isGoodPair_witness_small : IsGoodPair (29 / 10 : ℝ) (5 / 4 : ℝ) := by
  have hfl : ⌊(29 / 10 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  refine isGoodPair_of_two_le_layer_sq (29 / 10) (5 / 4) 1 (by norm_num) le_rfl ?_
    (by norm_num) ?_
  · rw [hfl]; norm_num
  · rw [hfl]; norm_num

/-- **Non-vacuity 2 — where the `√` actually pays.** `(50, 65/64)`: `⌊t⌋ = 50`, `j = 7`
(`j² = 49 ≥ 49`), so `M = 50 + 14 = 64` and the strip reaches `1 + 1/64`, attained with
equality. The published strip for `t = 50` stops at `1 + 1/102`, so `65/64` was **not** a
theorem before this file. -/
theorem isGoodPair_witness_fifty : IsGoodPair (50 : ℝ) (65 / 64 : ℝ) := by
  have hfl : ⌊(50 : ℝ)⌋ = 50 := by norm_num
  refine isGoodPair_of_two_le_layer_sq 50 (65 / 64) 7 (by norm_num) (by norm_num) ?_
    (by norm_num) ?_
  · rw [hfl]; norm_num
  · rw [hfl]; norm_num

end Layer

end Erdos349

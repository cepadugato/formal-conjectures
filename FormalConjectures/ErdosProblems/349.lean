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

/-! ### The fibre `α = 17/11` (proof, sub-namespace `Z3`) -/

namespace Z3

/-- **Distinct-value prefix sum.** $C\ a\ N = \sum$ of the *distinct* values among
$a_0, \ldots, a_{N-1}$. -/
noncomputable def C (a : ℕ → ℤ) (N : ℕ) : ℤ := ∑ x ∈ (Finset.range N).image a, x

/-! ## §2. Toolbox for `C` and `subsetSums` (from `349/DeficitWindow.lean` §1, CLOSED) -/

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

/-- A convenience constructor for membership in `subsetSums` of a `Finset`. -/
lemma mem_subsetSums_of_subset {A B : Finset ℤ} (hsub : B ⊆ A) {k : ℤ}
    (hk : k = ∑ i ∈ B, i) : k ∈ subsetSums ((A : Finset ℤ) : Set ℤ) :=
  ⟨B, by exact_mod_cast Finset.coe_subset.mpr hsub, hk⟩

/-! ## §3. The deficit engine (from `349/DeficitWindow.lean` §2, CLOSED) -/

/-- **THE DEFICIT ENGINE** (sub-lemma 4 of `349/STRATEGY-4.md`). If `a` is nonnegative, monotone
and unbounded and, at a rank `N₀`, an interior window `[L, C a N₀ − D]` is covered by the subset
sums of the first `N₀` values and the shifted Brown margin `a n + L + D ≤ 1 + C a n` holds for
every `n ≥ N₀`, then `Set.range a` is additively complete. -/
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

/-! ## §4. The floor sequence facts (from `349/DeficitWindow.lean` §3, CLOSED) -/

/-- **Nonnegativity** (engine hypothesis `hnn`). -/
theorem floorSeq_nonneg (t α : ℝ) (ht : 0 ≤ t) (hα : 0 ≤ α) (n : ℕ) :
    0 ≤ ⌊t * α ^ n⌋ :=
  Int.floor_nonneg.mpr (mul_nonneg ht (pow_nonneg hα n))

/-- **Monotonicity** (engine hypothesis `hmono`). -/
theorem floorSeq_mono (t α : ℝ) (ht : 0 ≤ t) (hα : 1 ≤ α) :
    Monotone (fun n : ℕ => ⌊t * α ^ n⌋) := by
  intro m n hmn
  simp only
  exact Int.floor_le_floor (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα hmn) ht)

/-- **Unboundedness** (engine hypothesis `hub`). -/
theorem floorSeq_unbounded (t α : ℝ) (ht : 0 < t) (hα1 : 1 < α) :
    ∀ M : ℤ, ∃ n : ℕ, M ≤ ⌊t * α ^ n⌋ := by
  intro M
  have htend : Tendsto (fun n : ℕ => t * α ^ n) atTop atTop :=
    Tendsto.const_mul_atTop ht (tendsto_pow_atTop_atTop_of_one_lt hα1)
  obtain ⟨n, hn⟩ := (htend.eventually_ge_atTop (M : ℝ)).exists
  exact ⟨n, Int.le_floor.mpr hn⟩

/-- **The elementary floor step** (verbatim from `349/BandPhi.lean`). -/
theorem floor_mul_le_two_mul_floor (α x : ℝ) (hgap : 1 ≤ (2 - α) * x) :
    ⌊α * x⌋ ≤ 2 * ⌊x⌋ := by
  have h1 : α * x ≤ 2 * x - 1 := by nlinarith
  have h2 : x - 1 < (⌊x⌋ : ℝ) := by have := Int.sub_one_lt_floor x; linarith
  have h3 : ((⌊α * x⌋ : ℤ) : ℝ) ≤ α * x := Int.floor_le _
  have h4 : ((⌊α * x⌋ : ℤ) : ℝ) < 2 * ((⌊x⌋ : ℤ) : ℝ) + 1 := by linarith
  have h5 : ⌊α * x⌋ < 2 * ⌊x⌋ + 1 := by exact_mod_cast h4
  omega

/-- **L1.** `brown_shifted_of_doubling` with the doubling bound required only from rank `N₀`. -/
theorem brown_shifted_of_doubling_from (a : ℕ → ℤ) (L D : ℤ) (N₀ : ℕ)
    (hmono : Monotone a)
    (hdouble : ∀ n, N₀ ≤ n → a (n + 1) ≤ 2 * a n)
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
    | succ n hn ih =>
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
        have hd := hdouble n hn
        omega
  intro n hn
  rcases eq_or_lt_of_le hn with heq | hlt
  · rw [← heq]; omega
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hp : N₀ ≤ p := by omega
    have h1 := hT p hp
    have h2 := hdouble p hp
    omega

/-- **L5.** Reduction theorem with doubling only from rank `N₀` (no `α < 3/2`, no `1 ≤ t`). -/
theorem isGoodPair_of_run_from (t α : ℝ) (ht : 0 < t) (hα1 : 1 < α)
    (N₀ : ℕ) (L U : ℤ)
    (hnew : ⌊t * α ^ N₀⌋ ∉ (Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋))
    (hrun : ∀ k : ℤ, L ≤ k → k ≤ U →
      k ∈ subsetSums (((Finset.range N₀).image (fun n : ℕ => ⌊t * α ^ n⌋) : Finset ℤ) : Set ℤ))
    (hfit : ⌊t * α ^ N₀⌋ ≤ U - L + 1)
    (hdouble : ∀ n, N₀ ≤ n → ⌊t * α ^ (n + 1)⌋ ≤ 2 * ⌊t * α ^ n⌋) :
    IsGoodPair t α := by
  have hα0 : (0:ℝ) < α := by linarith
  show IsAddComplete (Set.range fun n : ℕ => ⌊t * α ^ n⌋)
  refine eventuallyComplete_of_brown_of_deficit_window (fun n : ℕ => ⌊t * α ^ n⌋)
    (fun n => floorSeq_nonneg t α ht.le hα0.le n) (floorSeq_mono t α ht.le hα1.le)
    (floorSeq_unbounded t α ht hα1) N₀ L
    (C (fun n : ℕ => ⌊t * α ^ n⌋) N₀ - U) ?_ ?_
  · intro k hkL hkU
    exact hrun k hkL (by omega)
  · exact brown_shifted_of_doubling_from (fun n : ℕ => ⌊t * α ^ n⌋) L
      (C (fun n : ℕ => ⌊t * α ^ n⌋) N₀ - U) N₀ (floorSeq_mono t α ht.le hα1.le)
      hdouble hnew (by beta_reduce; omega)

/-- **L2.** Every integer of `[14, 55]` is a subset sum of `{1, 3, 4, 7, 11, 17, 26}`. -/
theorem window_z3_a26 : ∀ k : ℤ, 14 ≤ k → k ≤ 55 →
    k ∈ subsetSums ((({1, 3, 4, 7, 11, 17, 26} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {3, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 7, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 7, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 7, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 3, 4, 7, 11, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 17, 26}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 11, 17, 26}) (by decide) (by decide)

/-- **L2.** Every integer of `[14, 55]` is a subset sum of `{1, 3, 4, 7, 11, 17, 27}`. -/
theorem window_z3_a27 : ∀ k : ℤ, 14 ≤ k → k ≤ 55 →
    k ∈ subsetSums ((({1, 3, 4, 7, 11, 17, 27} : Finset ℤ)) : Set ℤ) := by
  intro k hk1 hk2
  have h : k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_subsetSums_of_subset (B := {3, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 7, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 3, 4, 7, 11}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 7, 11, 17}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {4, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 4, 7, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {7, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 7, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {1, 3, 4, 7, 11, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {3, 7, 17, 27}) (by decide) (by decide)
  · exact mem_subsetSums_of_subset (B := {11, 17, 27}) (by decide) (by decide)

/-- **L3.** Doubling from rank 8 for `α = 17/11`, `t ≥ 1`. -/
theorem z3_doubling (t : ℝ) (ht : 1 ≤ t) :
    ∀ n : ℕ, 8 ≤ n → ⌊t * (17 / 11 : ℝ) ^ (n + 1)⌋ ≤ 2 * ⌊t * (17 / 11 : ℝ) ^ n⌋ := by
  intro n hn
  have hp : (17 / 11 : ℝ) ^ 8 ≤ (17 / 11 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hpos : (0 : ℝ) ≤ (17 / 11 : ℝ) ^ n := by positivity
  have hty : 1 * (17 / 11 : ℝ) ^ n ≤ t * (17 / 11 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right ht hpos
  have h8 : (17 / 11 : ℝ) ^ 8 = 6975757441 / 214358881 := by norm_num
  have hgap : 1 ≤ (2 - 17 / 11 : ℝ) * (t * (17 / 11 : ℝ) ^ n) := by
    rw [h8] at hp; linarith
  have e : t * (17 / 11 : ℝ) ^ (n + 1) = (17 / 11 : ℝ) * (t * (17 / 11 : ℝ) ^ n) := by ring
  rw [e]
  exact floor_mul_le_two_mul_floor (17 / 11 : ℝ) (t * (17 / 11 : ℝ) ^ n) hgap

/-- **L6 (target).** For `α = 17/11` and `t ∈ [3/α², 2/α) = [363/289, 22/17)`,
`(t, α)` is a good pair (eventual completeness). -/
theorem isGoodPair_of_z3_17_11 (t : ℝ) (h1 : 363 / 289 ≤ t) (h2 : t < 22 / 17) :
    IsGoodPair t (17 / 11) := by
  -- L4: the prefix `a 0 … a 6 = 1, 1, 3, 4, 7, 11, 17` and bounds on `a 8`
  have e0 : ⌊t * (17 / 11 : ℝ) ^ (0 : ℕ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e1 : ⌊t * (17 / 11 : ℝ) ^ (1 : ℕ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e2 : ⌊t * (17 / 11 : ℝ) ^ (2 : ℕ)⌋ = 3 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e3 : ⌊t * (17 / 11 : ℝ) ^ (3 : ℕ)⌋ = 4 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e4 : ⌊t * (17 / 11 : ℝ) ^ (4 : ℕ)⌋ = 7 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e5 : ⌊t * (17 / 11 : ℝ) ^ (5 : ℕ)⌋ = 11 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e6 : ⌊t * (17 / 11 : ℝ) ^ (6 : ℕ)⌋ = 17 := by
    rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith
  have e8le : ⌊t * (17 / 11 : ℝ) ^ (8 : ℕ)⌋ ≤ 42 := by
    have : t * (17 / 11 : ℝ) ^ (8 : ℕ) < 43 := by norm_num; linarith
    have h43 : ⌊t * (17 / 11 : ℝ) ^ (8 : ℕ)⌋ < 43 := by
      rw [Int.floor_lt]; exact_mod_cast this
    omega
  have e8ge : 28 ≤ ⌊t * (17 / 11 : ℝ) ^ (8 : ℕ)⌋ := by
    rw [Int.le_floor]; norm_num; linarith
  have hdbl := z3_doubling t (by linarith)
  rcases lt_or_ge (t * (17 / 11 : ℝ) ^ (7 : ℕ)) 27 with h7 | h7
  · have e7 : ⌊t * (17 / 11 : ℝ) ^ (7 : ℕ)⌋ = 26 := by
      rw [Int.floor_eq_iff]; norm_num at h7 ⊢; constructor <;> linarith
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊t * (17 / 11 : ℝ) ^ n⌋)
        = {1, 3, 4, 7, 11, 17, 26} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run_from t (17 / 11) (by linarith) (by norm_num) 8 14 55 ?_ ?_ ?_ hdbl
    · rw [himg]
      generalize ⌊t * (17 / 11 : ℝ) ^ (8 : ℕ)⌋ = a8 at e8ge ⊢
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rw [himg]; exact window_z3_a26
    · omega
  · have e7 : ⌊t * (17 / 11 : ℝ) ^ (7 : ℕ)⌋ = 27 := by
      rw [Int.floor_eq_iff]; norm_num at h7 ⊢; constructor <;> linarith
    have himg : (Finset.range 8).image (fun n : ℕ => ⌊t * (17 / 11 : ℝ) ^ n⌋)
        = {1, 3, 4, 7, 11, 17, 27} := by
      rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_add_one, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one,
        Finset.range_zero]
      simp only [Finset.image_insert, Finset.image_empty, e0, e1, e2, e3, e4, e5, e6, e7]
      decide
    refine isGoodPair_of_run_from t (17 / 11) (by linarith) (by norm_num) 8 14 55 ?_ ?_ ?_ hdbl
    · rw [himg]
      generalize ⌊t * (17 / 11 : ℝ) ^ (8 : ℕ)⌋ = a8 at e8ge ⊢
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rw [himg]; exact window_z3_a27
    · omega

-- #print axioms isGoodPair_of_z3_17_11  -- [propext, Classical.choice, Quot.sound]

end Z3

end Erdos349

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

import FormalConjectures.Util.ProblemImports

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

/-- For α>2 and any t>0, ⌊t·αⁿ⌋ is not additively complete; equivalently (t,α) is not a
    "good pair". A partial result on the open Erdős 349: it complements
    `complete_for_alpha_in_Ioo_one_to_goldenRatio`. -/
@[category research solved, AMS 11]
theorem alpha_gt_two_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα : 2 < α) : ¬ IsGoodPair t α := by
  unfold IsGoodPair
  set f : ℕ → ℤ := fun n => ⌊t * α ^ n⌋ with hf
  -- Basic facts about α.
  have hα0 : (0 : ℝ) < α := by linarith
  have hα1 : (1 : ℝ) < α := by linarith
  have hα1' : (1 : ℝ) ≤ α := le_of_lt hα1
  have hαm1 : (0 : ℝ) < α - 1 := by linarith
  -- (1) nonneg: 0 ≤ f n.
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    rw [hf]
    simp only
    rw [Int.floor_nonneg]
    positivity
  -- a real upper bound on each term as a real.
  have hterm_le : ∀ k, (f k : ℝ) ≤ t * α ^ k := by
    intro k
    rw [hf]
    exact Int.floor_le _
  -- (2) monotone.
  have hmono : Monotone f := by
    intro n m hnm
    rw [hf]
    simp only
    apply Int.floor_le_floor
    apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
    exact pow_le_pow_right₀ hα1' hnm
  -- (3) partial sum.
  set S : ℕ → ℤ := fun n => ∑ k ∈ Finset.range (n + 1), f k with hS
  -- geometric bound: (S n : ℝ) ≤ t * α^(n+1) / (α - 1).
  have hSbound : ∀ n, (S n : ℝ) ≤ t * α ^ (n + 1) / (α - 1) := by
    intro n
    have h1 : (S n : ℝ) = ∑ k ∈ Finset.range (n + 1), (f k : ℝ) := by
      rw [hS]; push_cast; rfl
    rw [h1]
    have h2 : ∑ k ∈ Finset.range (n + 1), (f k : ℝ)
        ≤ ∑ k ∈ Finset.range (n + 1), t * α ^ k := by
      apply Finset.sum_le_sum
      intro k _
      exact hterm_le k
    refine le_trans h2 ?_
    have h3 : ∑ k ∈ Finset.range (n + 1), t * α ^ k
        = t * ((α ^ (n + 1) - 1) / (α - 1)) := by
      rw [← Finset.mul_sum, geom_sum_eq (by linarith : α ≠ 1)]
    rw [h3]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
    apply div_le_div_of_nonneg_right (by linarith) hαm1.le
  -- (5) the gap: find a single large n with both M ≥ N and a_{n+1} ≥ S n + 2.
  rw [IsAddComplete, Filter.not_eventually]
  rw [Filter.frequently_atTop]
  intro N
  -- tendsto: t·α^(n+1)·(α-2)/(α-1) - 2 → ∞.
  have htend : Tendsto (fun n : ℕ => t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2)
      atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => α ^ (n + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hα1).comp (tendsto_add_atTop_nat 1)
    have hc2 : (0 : ℝ) < (α - 2) / (α - 1) := by
      apply _root_.div_pos <;> linarith
    have h1 : Tendsto (fun n : ℕ => t * α ^ (n + 1)) atTop atTop :=
      hpow.const_mul_atTop ht
    have h2 : Tendsto (fun n : ℕ => t * α ^ (n + 1) * ((α - 2) / (α - 1))) atTop atTop :=
      h1.atTop_mul_const hc2
    exact tendsto_atTop_add_const_right atTop (-2 : ℝ)
      (by simpa [sub_eq_add_neg] using h2)
  -- S n ≥ N via S n ≥ a_n ≥ t·α^n - 1 → ∞.
  have htend2 : Tendsto (fun n : ℕ => t * α ^ n - 1) atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => α ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hα1
    have h1 : Tendsto (fun n : ℕ => t * α ^ n) atTop atTop :=
      hpow.const_mul_atTop ht
    exact tendsto_atTop_add_const_right atTop (-1 : ℝ)
      (by simpa [sub_eq_add_neg] using h1)
  -- Get n with g n ≥ max(N+2, 3)  AND  t·α^n - 1 ≥ N.
  have hev := (htend.eventually_ge_atTop (max ((N : ℝ) + 2) 3)).and
      (htend2.eventually_ge_atTop ((N : ℝ)))
  obtain ⟨n, hn, hn2⟩ := hev.exists
  have hn' : (N : ℝ) + 2 ≤ t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 :=
    le_trans (le_max_left _ _) hn
  have hn3 : (3 : ℝ) ≤ t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 :=
    le_trans (le_max_right _ _) hn
  -- real lower bound for a_{n+1}.
  have ha_lb : t * α ^ (n + 1) - 1 < (f (n + 1) : ℝ) := by
    have := Int.sub_one_lt_floor (t * α ^ (n + 1))
    rw [hf]; exact this
  have hreal : (f (n + 1) : ℝ) - (S n : ℝ) - 1
      > t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 := by
    have hsb := hSbound n
    have key : t * α ^ (n + 1) * ((α - 2) / (α - 1))
        = t * α ^ (n + 1) - t * α ^ (n + 1) / (α - 1) := by
      field_simp
      ring
    rw [key]
    linarith [ha_lb, hsb]
  have hcombine : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > (N : ℝ) + 2 := by
    linarith [hreal, hn']
  have hgapR : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > 3 := by
    linarith [hreal, hn3]
  have hgap : f (n + 1) ≥ S n + 2 := by
    have : ((f (n + 1) - (S n) : ℤ) : ℝ) ≥ ((2 : ℤ) : ℝ) := by
      push_cast; linarith [hgapR]
    have h2 : (f (n + 1) - (S n) : ℤ) ≥ (2 : ℤ) := by exact_mod_cast this
    linarith
  have hint : (f (n + 1) : ℝ) - (S n : ℝ) - 1 ≥ (N : ℝ) + 2 := le_of_lt hcombine
  have hZ : (f (n + 1)) - (S n) - 1 ≥ N + 2 := by
    have : ((f (n + 1) - (S n) - 1 : ℤ) : ℝ) ≥ ((N + 2 : ℤ) : ℝ) := by
      push_cast; linarith [hint]
    exact_mod_cast this
  -- The missed value M := S n + 1.  S n ≥ N : since S n ≥ a_n ≥ t·α^n - 1 ≥ N.
  have hSn_lb : (S n : ℝ) ≥ t * α ^ n - 1 := by
    have hlast : f n ≤ S n := by
      rw [hS]
      apply Finset.single_le_sum (fun i _ => hnonneg i)
      simp
    have h1 : (f n : ℝ) ≥ t * α ^ n - 1 := by
      have := Int.sub_one_lt_floor (t * α ^ n)
      have : (t * α ^ n) - 1 ≤ (⌊t * α ^ n⌋ : ℝ) := le_of_lt this
      rw [hf]; simpa using this
    have h2 : (f n : ℝ) ≤ (S n : ℝ) := by exact_mod_cast hlast
    linarith
  have hSnN : (S n) ≥ N := by
    have : (S n : ℝ) ≥ (N : ℝ) := le_trans hn2 hSn_lb
    exact_mod_cast this
  refine ⟨S n + 1, ?_, ?_⟩
  · -- M ≥ N
    linarith
  · -- M := S n + 1 ∉ subsetSums (range f).
    rintro ⟨B, hBsub, hBsum⟩
    have hBnonneg : ∀ b ∈ B, (0 : ℤ) ≤ b := by
      intro b hb
      have : b ∈ Set.range f := hBsub hb
      obtain ⟨m, rfl⟩ := this
      exact hnonneg m
    set P : ℤ := f (n + 1) with hP
    by_cases hcase : ∃ b ∈ B, P ≤ b
    · obtain ⟨b, hbB, hPb⟩ := hcase
      have hge : P ≤ ∑ i ∈ B, i := by
        calc P ≤ b := hPb
          _ ≤ ∑ i ∈ B, i := Finset.single_le_sum (fun i _ => hBnonneg i ‹_›) hbB
      have : S n + 1 ≥ P := by rw [hBsum]; exact hge
      have : S n + 1 ≥ S n + 2 := le_trans hgap this
      omega
    · have hlt : ∀ b ∈ B, b < P := by
        intro b hb
        by_contra hc
        exact hcase ⟨b, hb, not_lt.mp hc⟩
      have hBsubimg : B ⊆ (Finset.range (n + 1)).image f := by
        intro b hb
        have hbP : b < P := hlt b hb
        have : b ∈ Set.range f := hBsub hb
        obtain ⟨m, rfl⟩ := this
        have hmle : m ≤ n := by
          by_contra hmn
          have : f (n + 1) ≤ f m := hmono (by omega)
          rw [← hP] at this
          omega
        rw [Finset.mem_image]
        exact ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
      have himg_le : ∑ u ∈ (Finset.range (n + 1)).image f, u ≤ S n := by
        have h := Finset.sum_image_le_of_nonneg
          (s := Finset.range (n + 1)) (g := f) (f := fun x : ℤ => x)
          (fun u hu => by
            rw [Finset.mem_image] at hu
            obtain ⟨m, _, rfl⟩ := hu
            exact hnonneg m)
        simpa [hS] using h
      have hBsum_le : ∑ i ∈ B, i ≤ S n := by
        calc ∑ i ∈ B, i
            ≤ ∑ u ∈ (Finset.range (n + 1)).image f, u :=
              Finset.sum_le_sum_of_subset_of_nonneg hBsubimg
                (fun i hi _ => by
                  rw [Finset.mem_image] at hi
                  obtain ⟨m, _, rfl⟩ := hi
                  exact hnonneg m)
          _ ≤ S n := himg_le
      rw [← hBsum] at hBsum_le
      omega

/-- For `0 < α ≤ 1` and any `t > 0`, `(t, α)` is not a good pair: every term `⌊t·αⁿ⌋`
    lies in the finite interval `[0, ⌊t⌋]` (since `αⁿ ≤ 1`), so every subset sum is bounded
    by the constant `∑ i ∈ Icc 0 ⌊t⌋, i`, and no large integer can be a subset sum. A partial
    result on the open Erdős 349, complementing the `2 < α` and integer-coefficient cases. -/
@[category research solved, AMS 11]
theorem alpha_le_one_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ¬ IsGoodPair t α := by
  unfold IsGoodPair
  -- (1) every term is in [0, ⌊t⌋].
  have hpow_le : ∀ n : ℕ, α ^ n ≤ 1 := fun n => pow_le_one₀ hα0.le hα1
  have hnonneg : ∀ n, 0 ≤ ⌊t * α ^ n⌋ := by
    intro n
    rw [Int.floor_nonneg]
    positivity
  have hle_top : ∀ n, ⌊t * α ^ n⌋ ≤ ⌊t⌋ := by
    intro n
    apply Int.floor_le_floor
    have : t * α ^ n ≤ t * 1 := mul_le_mul_of_nonneg_left (hpow_le n) ht.le
    simpa using this
  -- the constant bound on subset sums.
  set C : ℤ := ∑ i ∈ Finset.Icc (0 : ℤ) ⌊t⌋, i with hC
  have hmem : ∀ n, ⌊t * α ^ n⌋ ∈ Finset.Icc (0 : ℤ) ⌊t⌋ := by
    intro n
    rw [Finset.mem_Icc]
    exact ⟨hnonneg n, hle_top n⟩
  have hsum_le : ∀ B : Finset ℤ, ↑B ⊆ Set.range (fun n => ⌊t * α ^ n⌋) →
      (∑ i ∈ B, i) ≤ C := by
    intro B hBsub
    have hBsubF : B ⊆ Finset.Icc (0 : ℤ) ⌊t⌋ := by
      intro b hb
      have : b ∈ Set.range (fun n => ⌊t * α ^ n⌋) := hBsub hb
      obtain ⟨m, rfl⟩ := this
      exact hmem m
    rw [hC]
    apply Finset.sum_le_sum_of_subset_of_nonneg hBsubF
    intro i hi _
    rw [Finset.mem_Icc] at hi
    exact hi.1
  -- additive completeness forces every large k to be a subset sum, ≤ C — contradiction.
  rw [IsAddComplete, Filter.eventually_atTop]
  rintro ⟨N, hN⟩
  set k : ℤ := max N (C + 1) with hk
  have hkN : N ≤ k := le_max_left _ _
  have hkC : C + 1 ≤ k := le_max_right _ _
  have hkmem : k ∈ subsetSums (Set.range (fun n => ⌊t * α ^ n⌋)) := hN k hkN
  obtain ⟨B, hBsub, hBsum⟩ := hkmem
  have : k ≤ C := by rw [hBsum]; exact hsum_le B hBsub
  omega

/-- **Binary expansion.** Every natural number `k` is a sum of distinct powers of two:
    there is a finite set `E` of exponents with `k = ∑ i ∈ E, 2^i`. Proved by strong
    induction: subtract the largest power `2^m ≤ k`, recurse on the remainder. -/
@[category research solved, AMS 11]
theorem exists_finset_sum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact ⟨∅, by simp [hk0]⟩
    · set m := Nat.log 2 k with hm
      have hmle : 2 ^ m ≤ k := Nat.pow_log_le_self 2 hkpos.ne'
      have hltsucc : k < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
      set r := k - 2 ^ m with hr
      have hr_lt_pow : r < 2 ^ m := by
        have : k < 2 ^ m + 2 ^ m := by
          have : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
          omega
        omega
      have hr_lt_k : r < k := by omega
      obtain ⟨E, hE⟩ := ih r hr_lt_k
      have hElt : ∀ i ∈ E, i < m := by
        intro i hi
        by_contra hge
        rw [not_lt] at hge
        have hpow_le : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hge
        have hle : 2 ^ i ≤ r := by
          calc 2 ^ i = ∑ j ∈ ({i} : Finset ℕ), 2 ^ j := by simp
            _ ≤ ∑ j ∈ E, 2 ^ j := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · simpa using hi
                · intro j _ _; positivity
            _ = r := hE.symm
        omega
      have hmnotin : m ∉ E := fun hmem => (lt_irrefl m (hElt m hmem))
      refine ⟨insert m E, ?_⟩
      rw [Finset.sum_insert hmnotin]
      omega

/-- **The pair `(1, 2)` is good.** The powers of two `⌊1·2ⁿ⌋ = 2ⁿ` form an additively
    complete set: every `k ≥ 1` is a finite sum of distinct powers of two. -/
@[category research solved, AMS 11]
theorem one_two_isGoodPair : IsGoodPair 1 2 := by
  unfold IsGoodPair
  have hfloor : ∀ n : ℕ, ⌊(1 : ℝ) * (2 : ℝ) ^ n⌋ = 2 ^ n := by
    intro n
    have : (1 : ℝ) * (2 : ℝ) ^ n = ((2 ^ n : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_intCast]
  rw [IsAddComplete, Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro k hk
  set n : ℕ := k.toNat with hn
  have hkn : (n : ℤ) = k := Int.toNat_of_nonneg (by omega)
  obtain ⟨E, hE⟩ := exists_finset_sum_two_pow n
  set B : Finset ℤ := E.image (fun i => (2 : ℤ) ^ i) with hB
  have hinj : Set.InjOn (fun i => (2 : ℤ) ^ i) (E : Set ℕ) := by
    intro a _ b _ hab
    exact (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 2)).injective hab
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    rw [hB, Finset.coe_image, Set.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨i, hfloor i⟩
  · rw [hB, Finset.sum_image (by
      intro a ha b hb hab
      exact hinj (by simpa using ha) (by simpa using hb) hab)]
    have : (∑ i ∈ E, (2 : ℤ) ^ i) = ((∑ i ∈ E, 2 ^ i : ℕ) : ℤ) := by push_cast; ring
    rw [this, ← hE, hkn]

/-- **The dyadic fiber at `α = 2`.** For every `k`, the pair `(1/2ᵏ, 2)` is good: the
    sequence `⌊2ⁿ / 2ᵏ⌋` is additively complete because at index `n = m + k` it equals the
    exact power `2^m`, so its range contains all powers of two, which already form an
    additively complete set. Uses monotonicity `IsAddComplete.mono`. -/
@[category research solved, AMS 11]
theorem dyadic_two_isGoodPair (k : ℕ) : IsGoodPair (1 / 2 ^ k) 2 := by
  unfold IsGoodPair
  -- every power of two is hit: ⌊2^(m+k)/2^k⌋ = 2^m.
  have hsub : Set.range (fun n => ⌊(1 : ℝ) * (2 : ℝ) ^ n⌋) ⊆
      Set.range (fun n => ⌊(1 / 2 ^ k : ℝ) * (2 : ℝ) ^ n⌋) := by
    rintro x ⟨m, rfl⟩
    refine ⟨m + k, ?_⟩
    have hone : ⌊(1 : ℝ) * (2 : ℝ) ^ m⌋ = 2 ^ m := by
      have : (1 : ℝ) * (2 : ℝ) ^ m = ((2 ^ m : ℤ) : ℝ) := by push_cast; ring
      rw [this, Int.floor_intCast]
    have hdy : ⌊(1 / 2 ^ k : ℝ) * (2 : ℝ) ^ (m + k)⌋ = 2 ^ m := by
      have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
      have : (1 / 2 ^ k : ℝ) * (2 : ℝ) ^ (m + k) = ((2 ^ m : ℤ) : ℝ) := by
        rw [pow_add]; field_simp; push_cast; ring
      rw [this, Int.floor_intCast]
    simp only
    rw [hone, hdy]
  have hcomplete : IsAddComplete (Set.range (fun n => ⌊(1 : ℝ) * (2 : ℝ) ^ n⌋)) := by
    have := one_two_isGoodPair
    unfold IsGoodPair at this
    exact this
  exact hcomplete.mono hsub

/-- **Integer leading coefficient `t ≥ 2` blocks completeness.** For every integer base `α`,
    the pair `(t, α)` with integer `t ≥ 2` is not good: `⌊t·αⁿ⌋ = t·αⁿ` is a multiple of `t`,
    so every subset sum is too, but two consecutive large integers cannot both be multiples
    of `t`. Generalizes the parity obstruction (`t = 2`). A partial result on Erdős 349. -/
@[category research solved, AMS 11]
theorem int_coeff_ge_two_not_isGoodPair (t : ℤ) (ht : 2 ≤ t) (α : ℤ) :
    ¬ IsGoodPair (t : ℝ) (α : ℝ) := by
  unfold IsGoodPair
  have hfloor : ∀ n : ℕ, ⌊(t : ℝ) * (α : ℝ) ^ n⌋ = t * α ^ n := by
    intro n
    have : (t : ℝ) * (α : ℝ) ^ n = ((t * α ^ n : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_intCast]
  have hdvd : ∀ k ∈ subsetSums (Set.range (fun n => ⌊(t : ℝ) * (α : ℝ) ^ n⌋)), t ∣ k := by
    rintro k ⟨B, hBsub, rfl⟩
    apply Finset.dvd_sum
    intro b hb
    have : b ∈ Set.range (fun n => ⌊(t : ℝ) * (α : ℝ) ^ n⌋) := hBsub hb
    obtain ⟨n, rfl⟩ := this
    simp only
    rw [hfloor n]
    exact Dvd.intro _ rfl
  intro hcomplete
  rw [IsAddComplete, Filter.eventually_atTop] at hcomplete
  obtain ⟨N, hN⟩ := hcomplete
  have hdN : t ∣ N := hdvd N (hN N (le_refl N))
  have hdN1 : t ∣ (N + 1) := hdvd (N + 1) (hN (N + 1) (by omega))
  have hd1 : t ∣ (1 : ℤ) := by
    have : t ∣ ((N + 1) - N) := dvd_sub hdN1 hdN
    simpa using this
  have : t ≤ 1 := Int.le_of_dvd (by norm_num) hd1
  omega

/-- **Erdős 349, complete characterization on positive integer pairs.** For integers
    `t ≥ 1`, `α ≥ 1`, the pair `(t, α)` is good (i.e. `⌊t·αⁿ⌋` is additively complete) iff
    `(t, α) = (1, 2)`. Assembles the four partial results: `(1,2)` is good, `α ≤ 1` fails,
    `2 < α` fails (`alpha_gt_two_not_isGoodPair`), and integer `t ≥ 2` fails. -/
@[category research solved, AMS 11]
theorem integer_isGoodPair_iff (t α : ℤ) (ht : 1 ≤ t) (hα : 1 ≤ α) :
    IsGoodPair (t : ℝ) (α : ℝ) ↔ t = 1 ∧ α = 2 := by
  constructor
  · intro h
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    rcases (by omega : α = 1 ∨ α = 2 ∨ 3 ≤ α) with hα1 | hα2 | hα3
    · subst hα1
      exfalso
      have hcast : ((1 : ℤ) : ℝ) = 1 := by norm_num
      apply alpha_le_one_not_isGoodPair (t : ℝ) ((1 : ℤ) : ℝ) htR
        (by rw [hcast]; norm_num) (by rw [hcast])
      exact h
    · subst hα2
      rcases (by omega : t = 1 ∨ 2 ≤ t) with ht1 | ht2
      · exact ⟨ht1, rfl⟩
      · exfalso
        have hcast : ((2 : ℤ) : ℝ) = 2 := by norm_num
        rw [hcast] at h
        exact int_coeff_ge_two_not_isGoodPair t ht2 2 (by rw [hcast]; exact h)
    · exfalso
      have hαR : (2 : ℝ) < (α : ℝ) := by
        have : (3 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα3
        linarith
      exact alpha_gt_two_not_isGoodPair (t : ℝ) (α : ℝ) htR hαR h
  · rintro ⟨rfl, rfl⟩
    have hcast : IsGoodPair ((1 : ℤ) : ℝ) ((2 : ℤ) : ℝ) = IsGoodPair 1 2 := by
      norm_num
    rw [hcast]
    exact one_two_isGoodPair

/-- **The pair `(3/2, 2)` is NOT good.** The negative companion of `dyadic_two_isGoodPair`:
    while every dyadic coefficient `1/2ᵏ` gives a good pair at `α = 2`, the non-dyadic rational
    `t = 3/2` does not. The sequence `⌊(3/2)·2ⁿ⌋ = 1, 3, 6, 12, 24, …` is not additively
    complete because every term but the first `⌊3/2⌋ = 1` is a multiple of `3` (namely
    `⌊(3/2)·2^(n+1)⌋ = 3·2ⁿ`), so every subset sum is `≡ 0` or `1 (mod 3)`; the infinitely
    many integers `≡ 2 (mod 3)` are never reached. A partial result on Erdős 349 in the same
    divisibility family as `int_coeff_ge_two_not_isGoodPair` (here the modulus is `3`). -/
@[category research solved, AMS 11]
theorem three_halves_two_not_isGoodPair : ¬ IsGoodPair (3 / 2) 2 := by
  unfold IsGoodPair
  -- The zeroth term: ⌊(3/2)·2⁰⌋ = ⌊3/2⌋ = 1.
  have hzero : ⌊(3 / 2 : ℝ) * (2 : ℝ) ^ (0 : ℕ)⌋ = 1 := by norm_num
  -- The (n+1)-th term: ⌊(3/2)·2^(n+1)⌋ = 3·2ⁿ (exact integer).
  have hsucc : ∀ n : ℕ, ⌊(3 / 2 : ℝ) * (2 : ℝ) ^ (n + 1)⌋ = 3 * 2 ^ n := by
    intro n
    have : (3 / 2 : ℝ) * (2 : ℝ) ^ (n + 1) = ((3 * 2 ^ n : ℤ) : ℝ) := by
      push_cast; ring
    rw [this, Int.floor_intCast]
  -- Every element of the range is either 1 or divisible by 3.
  have hresidue : ∀ x ∈ Set.range (fun n => ⌊(3 / 2 : ℝ) * (2 : ℝ) ^ n⌋),
      x = 1 ∨ (3 : ℤ) ∣ x := by
    rintro x ⟨n, rfl⟩
    simp only
    cases n with
    | zero => left; exact hzero
    | succ n => right; rw [hsucc n]; exact dvd_mul_right 3 _
  -- Every subset sum has residue 0 or 1 modulo 3.
  have hemod : ∀ s ∈ subsetSums (Set.range (fun n => ⌊(3 / 2 : ℝ) * (2 : ℝ) ^ n⌋)),
      s % 3 = 0 ∨ s % 3 = 1 := by
    rintro s ⟨B, hBsub, rfl⟩
    have hB_residue : ∀ b ∈ B, b = 1 ∨ (3 : ℤ) ∣ b := fun b hb =>
      hresidue b (hBsub (Finset.mem_coe.mpr hb))
    by_cases h1 : (1 : ℤ) ∈ B
    · have hB3 : ∀ b ∈ B.erase 1, (3 : ℤ) ∣ b := by
        intro b hb
        have hb' := Finset.mem_erase.mp hb
        rcases hB_residue b hb'.2 with rfl | hdvd
        · exact absurd rfl hb'.1
        · exact hdvd
      have hdvd_sum : (3 : ℤ) ∣ ∑ i ∈ B.erase 1, i := Finset.dvd_sum hB3
      rw [← Finset.add_sum_erase _ _ h1]
      obtain ⟨k, hk⟩ := hdvd_sum
      right
      omega
    · have hB3 : ∀ b ∈ B, (3 : ℤ) ∣ b := by
        intro b hb
        rcases hB_residue b hb with rfl | hdvd
        · exact absurd hb h1
        · exact hdvd
      have hdvd_sum : (3 : ℤ) ∣ ∑ i ∈ B, i := Finset.dvd_sum hB3
      obtain ⟨k, hk⟩ := hdvd_sum
      left
      omega
  -- Negate completeness: produce arbitrarily large k ≡ 2 (mod 3) not hit.
  rw [IsAddComplete, Filter.not_eventually, Filter.frequently_atTop]
  intro N
  refine ⟨3 * (max N 0) + 2, by omega, ?_⟩
  intro hmem
  have := hemod _ hmem
  omega

/- ### Entire completeness and the single-gap criterion

The results below isolate, once and cleanly, the gap case-split that already powers
`alpha_gt_two_not_isGoodPair`, and retarget it at a strictly stronger predicate:
*entire* additive completeness (van Doorn's "entirely complete": every positive
integer is a finite subset sum, not merely all sufficiently large ones). Against this
stronger predicate a single gap suffices — no `Tendsto`, no geometric majorant, no
asymptotics — which lets us cover the otherwise hard band `5/3 ≤ α < 2`. -/

/-- A set `A ⊆ ℤ` is *entirely additively complete* if **every** positive integer is a
    finite subset sum of `A` (van Doorn's "entirely complete": `P(A) = ℕ≥1`). Strictly
    stronger than `IsAddComplete`, which only requires all *sufficiently large* integers.

    This is a problem-local definition; it could be promoted to
    `FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean` (next to
    `IsAddComplete`) if the maintainers prefer it to live there. -/
def IsEntirelyAddComplete (A : Set ℤ) : Prop :=
  ∀ k : ℤ, 1 ≤ k → k ∈ subsetSums A

/-- **Glue.** Entire completeness implies (eventual) completeness: if every `k ≥ 1` is a
    subset sum, then in particular all sufficiently large `k` are. -/
@[category research solved, AMS 11]
theorem isEntirelyAddComplete_imp_isAddComplete {A : Set ℤ}
    (h : IsEntirelyAddComplete A) : IsAddComplete A :=
  Filter.eventually_atTop.mpr ⟨1, fun k hk => h k hk⟩

/-- **Abstract single-gap criterion.** For a monotone, nonnegative integer sequence `a`,
    a single gap `(∑_{k<r+1} a k) < m < a (r+1)` with `m ≥ 1` already shows that `m` is not
    a subset sum, hence the range of `a` is not entirely additively complete.

    This is the pure-`ℤ` core of `alpha_gt_two_not_isGoodPair`'s
    `by_cases ∃ b ∈ B, a (r+1) ≤ b` case-split, with `m` *given* rather than constructed via
    `Tendsto` (strictly easier, and enough for the band `5/3 ≤ α < 2` below). -/
@[category research solved, AMS 11]
theorem entire_gap_not_complete (a : ℕ → ℤ) (hmono : Monotone a) (hnn : ∀ n, 0 ≤ a n)
    (r : ℕ) (m : ℤ) (hm : 1 ≤ m)
    (hlo : (∑ k ∈ Finset.range (r + 1), a k) < m) (hhi : m < a (r + 1)) :
    ¬ IsEntirelyAddComplete (Set.range a) := by
  intro hcomplete
  apply absurd (hcomplete m hm)
  rintro ⟨B, hBsub, hBsum⟩
  have hBnonneg : ∀ b ∈ B, (0 : ℤ) ≤ b := by
    intro b hb
    have : b ∈ Set.range a := hBsub hb
    obtain ⟨j, rfl⟩ := this
    exact hnn j
  set P : ℤ := a (r + 1) with hP
  by_cases hcase : ∃ b ∈ B, P ≤ b
  · obtain ⟨b, hbB, hPb⟩ := hcase
    have hge : P ≤ ∑ i ∈ B, i := by
      calc P ≤ b := hPb
        _ ≤ ∑ i ∈ B, i := Finset.single_le_sum (fun i hi => hBnonneg i hi) hbB
    rw [← hBsum] at hge
    omega
  · have hlt : ∀ b ∈ B, b < P := by
      intro b hb
      by_contra hc
      exact hcase ⟨b, hb, not_lt.mp hc⟩
    have hBsubimg : B ⊆ (Finset.range (r + 1)).image a := by
      intro b hb
      have hbP : b < P := hlt b hb
      have : b ∈ Set.range a := hBsub hb
      obtain ⟨j, rfl⟩ := this
      have hjle : j ≤ r := by
        by_contra hjn
        have : a (r + 1) ≤ a j := hmono (by omega)
        rw [← hP] at this
        omega
      rw [Finset.mem_image]
      exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    have himg_le : ∑ u ∈ (Finset.range (r + 1)).image a, u
        ≤ ∑ k ∈ Finset.range (r + 1), a k := by
      have h := Finset.sum_image_le_of_nonneg (s := Finset.range (r + 1))
        (g := a) (f := fun x : ℤ => x)
        (fun u hu => by
          rw [Finset.mem_image] at hu; obtain ⟨j, _, rfl⟩ := hu; exact hnn j)
      simpa using h
    have hBsum_le : ∑ i ∈ B, i ≤ ∑ k ∈ Finset.range (r + 1), a k := by
      calc ∑ i ∈ B, i
          ≤ ∑ u ∈ (Finset.range (r + 1)).image a, u :=
            Finset.sum_le_sum_of_subset_of_nonneg hBsubimg
              (fun i hi _ => by
                rw [Finset.mem_image] at hi; obtain ⟨j, _, rfl⟩ := hi; exact hnn j)
        _ ≤ ∑ k ∈ Finset.range (r + 1), a k := himg_le
    rw [← hBsum] at hBsum_le
    omega

/-- The 0-th term of `⌊t·αⁿ⌋` is `⌊t⌋` (since `α⁰ = 1`). -/
@[category research solved, AMS 11]
theorem floorSeq_zero (t α : ℝ) : ⌊t * α ^ (0 : ℕ)⌋ = ⌊t⌋ := by
  simp [pow_zero, mul_one]

/-- The 1-st term of `⌊t·αⁿ⌋` is `⌊t·α⌋`. -/
@[category research solved, AMS 11]
theorem floorSeq_one (t α : ℝ) : ⌊t * α ^ (1 : ℕ)⌋ = ⌊t * α⌋ := by
  simp [pow_one]

/-- `n ↦ ⌊t·αⁿ⌋` is monotone when `0 ≤ t` and `1 ≤ α`. -/
@[category research solved, AMS 11]
theorem floorSeq_monotone (t α : ℝ) (ht : 0 ≤ t) (hα : 1 ≤ α) :
    Monotone (fun n => ⌊t * α ^ n⌋) := by
  intro n m hnm
  simp only
  apply Int.floor_le_floor
  apply mul_le_mul_of_nonneg_left _ ht
  exact pow_le_pow_right₀ hα hnm

/-- `n ↦ ⌊t·αⁿ⌋` is nonnegative when `0 ≤ t` and `0 ≤ α`. -/
@[category research solved, AMS 11]
theorem floorSeq_nonneg (t α : ℝ) (ht : 0 ≤ t) (hα : 0 ≤ α) (n : ℕ) :
    0 ≤ (fun n => ⌊t * α ^ n⌋) n := by
  simp only
  rw [Int.floor_nonneg]
  positivity

/-- **Application inside the band `5/3 ≤ α < 2`.** For `t ≥ 3` and `5/3 ≤ α < 2`, the
    sequence `⌊t·αⁿ⌋` is NOT entirely additively complete: the very first gap
    `⌊t⌋ < ⌊t⌋+1 < ⌊t·α⌋` already misses the positive integer `⌊t⌋+1`.

    This is the `r = 0`, `m = ⌊t⌋ + 1` instance of `entire_gap_not_complete`. The gap
    inequality comes from `t·α ≥ t·(5/3) = t + 2t/3 ≥ t + 2 ≥ ⌊t⌋ + 2`. The constant `5/3`
    (not `φ`) is the sharp clean threshold uniform in `t ≥ 3`: at `α = φ`, `t = 3` gives
    `⌊3φ⌋ = 4 = ⌊t⌋+1`, so the first gap closes. This is *entire* (not eventual)
    incompleteness; the gap need not recur for `φ ≤ α < 2`, where Erdős 349 stays open. -/
@[category research solved, AMS 11]
theorem floorSeq_not_entirelyComplete_of_le_two
    (t α : ℝ) (ht : 3 ≤ t) (hα : 5 / 3 ≤ α) (hα2 : α < 2) :
    ¬ IsEntirelyAddComplete (Set.range (fun n => ⌊t * α ^ n⌋)) := by
  have ht0 : 0 ≤ t := by linarith
  have hα1 : 1 ≤ α := by linarith
  have hα0 : 0 ≤ α := by linarith
  have hmono := floorSeq_monotone t α ht0 hα1
  have hnn := fun n => floorSeq_nonneg t α ht0 hα0 n
  have hft : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr (by linarith)
  have hm : (1 : ℤ) ≤ ⌊t⌋ + 1 := by omega
  have hlo : (∑ k ∈ Finset.range (0 + 1), (fun n => ⌊t * α ^ n⌋) k) < ⌊t⌋ + 1 := by
    rw [Finset.range_one, Finset.sum_singleton, floorSeq_zero]
    omega
  have hhi : (⌊t⌋ : ℤ) + 1 < (fun n => ⌊t * α ^ n⌋) (0 + 1) := by
    simp only
    rw [show (0 + 1) = 1 from rfl, floorSeq_one]
    have hkey : ((⌊t⌋ : ℤ) + 2 : ℝ) ≤ t * α := by
      have h1 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
      nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ α - 5 / 3)]
    have : (⌊t⌋ : ℤ) + 2 ≤ ⌊t * α⌋ := by
      apply Int.le_floor.mpr
      push_cast
      linarith
    omega
  exact entire_gap_not_complete (fun n => ⌊t * α ^ n⌋) hmono hnn 0 (⌊t⌋ + 1) hm hlo hhi

/-- **Distinct-value prefix sum.** `C a N` is the sum of the *distinct* values among
`a 0, ..., a (N - 1)`. Auxiliary to `entirely_complete_of_doubling` below: the relevant
"running reachable total" for subset sums over the SET `Set.range a` (duplicate values are
counted once, unlike a plain prefix sum). -/
private noncomputable def C (a : ℕ → ℤ) (N : ℕ) : ℤ := ∑ x ∈ (Finset.range N).image a, x

/-- **Abstract doubling criterion** (van Doorn's Lemma 3, applied with base phase length $r = 0$).

Let $a : \mathbb{N} \to \mathbb{Z}$ be a monotone integer sequence with $a_0 = 1$, satisfying the
doubling bound $a_{n+1} \le 2 a_n$ for every $n$, and unbounded ($\forall M,\ \exists n,\ M \le
a_n$). Then every positive integer is a finite subset sum of distinct values of $a$, i.e. the
range of $a$ is entirely additively complete.

A textbook-level combinatorial fact about monotone integer sequences (no $t, \alpha$); its
application to $a_n = \lfloor \alpha^n \rfloor$ below (`isGoodPair_one_alpha_of_lt_three_halves`)
is the research content of Erdős Problem 349. -/
@[category textbook, AMS 11]
theorem entirely_complete_of_doubling (a : ℕ → ℤ)
    (ha0 : a 0 = 1)
    (hmono : Monotone a)
    (hdouble : ∀ n, a (n + 1) ≤ 2 * a n)
    (hub : ∀ M : ℤ, ∃ n, M ≤ a n) :
    IsEntirelyAddComplete (Set.range a) := by
  have hnn : ∀ n, 0 ≤ a n := by
    intro n; have := hmono (Nat.zero_le n); rw [ha0] at this; linarith
  have hCnn : ∀ N, 0 ≤ C a N := by
    intro N; apply Finset.sum_nonneg; intro x hx
    rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
  have hmemC : ∀ N, a N ≤ C a (N + 1) := by
    intro N
    have hmem : a N ∈ (Finset.range (N + 1)).image a := by
      rw [Finset.mem_image]; exact ⟨N, Finset.mem_range.mpr (Nat.lt_succ_self N), rfl⟩
    have : a N ≤ ∑ x ∈ (Finset.range (N + 1)).image a, x := by
      apply Finset.single_le_sum (f := id) _ hmem
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hnn i
    simpa [C] using this
  have hQ : ∀ N, 2 * a N - 1 ≤ C a (N + 1) := by
    intro N
    induction N with
    | zero =>
      have h1 : C a (0 + 1) = a 0 := by simp [C, Finset.range_one]
      rw [h1, ha0]; norm_num
    | succ N ih =>
      have hd := hdouble N
      by_cases hnew : a (N + 1) ∈ (Finset.range (N + 1)).image a
      · have himg : (Finset.range (N + 2)).image a = (Finset.range (N + 1)).image a := by
          rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr hnew]
        have hCC : C a (N + 2) = C a (N + 1) := by simp only [C, himg]
        rw [hCC]
        rw [Finset.mem_image] at hnew
        obtain ⟨j, hj, hja⟩ := hnew
        have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h2 : a N ≤ a (N + 1) := hmono (Nat.le_succ N)
        have h4 : a j ≤ a N := hmono hjN
        have heq : a (N + 1) = a N := by rw [← hja] at h2 ⊢; linarith
        rw [heq]; exact ih
      · have himg : (Finset.range (N + 2)).image a
            = insert (a (N + 1)) ((Finset.range (N + 1)).image a) := by
          rw [Finset.range_add_one, Finset.image_insert]
        have hCC : C a (N + 2) = a (N + 1) + C a (N + 1) := by
          simp only [C, himg, Finset.sum_insert hnew]
        rw [hCC]
        linarith [hd, ih]
  have hgap : ∀ N, a N ≤ 1 + C a N := by
    intro N
    cases N with
    | zero => rw [ha0]; simp [C]
    | succ M =>
      have hq := hQ M
      have hd := hdouble M
      linarith
  have hJ : ∀ N, ∀ k : ℤ, 1 ≤ k → k ≤ C a N →
      ∃ Bv : Finset ℤ, ↑Bv ⊆ (((Finset.range N).image a : Finset ℤ) : Set ℤ) ∧ k = ∑ i ∈ Bv, i := by
    intro N
    induction N with
    | zero => intro k hk1 hk2; simp [C] at hk2; omega
    | succ N ih =>
      intro k hk1 hk2
      by_cases hnew : a N ∈ (Finset.range (N + 1)).image a ∧ a N ∈ (Finset.range N).image a
      · have himg : (Finset.range (N + 1)).image a = (Finset.range N).image a := by
          rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq_self.mpr hnew.2]
        have hCC : C a (N + 1) = C a N := by simp only [C, himg]
        rw [hCC] at hk2
        obtain ⟨Bv, hBv, hBeq⟩ := ih k hk1 hk2
        refine ⟨Bv, ?_, hBeq⟩
        rw [himg]; exact hBv
      · have hnotin : a N ∉ (Finset.range N).image a := by
          intro hc
          exact hnew ⟨by rw [Finset.mem_image]; exact ⟨N, Finset.mem_range.mpr (Nat.lt_succ_self N), rfl⟩, hc⟩
        have himg : (Finset.range (N + 1)).image a
            = insert (a N) ((Finset.range N).image a) := by
          rw [Finset.range_add_one, Finset.image_insert]
        have hCC : C a (N + 1) = a N + C a N := by
          simp only [C, himg, Finset.sum_insert hnotin]
        rw [hCC] at hk2
        by_cases hkle : k ≤ C a N
        · obtain ⟨Bv, hBv, hBeq⟩ := ih k hk1 hkle
          refine ⟨Bv, ?_, hBeq⟩
          rw [himg]
          refine hBv.trans ?_
          intro x hx
          simp only [Finset.coe_insert, Set.mem_insert_iff]
          exact Or.inr hx
        · rw [not_le] at hkle
          have hgapN : a N ≤ 1 + C a N := hgap N
          have hk'nn : 0 ≤ k - a N := by omega
          have hk'le : k - a N ≤ C a N := by omega
          rcases eq_or_lt_of_le hk'nn with h0 | hpos
          · refine ⟨{a N}, ?_, ?_⟩
            · rw [himg]
              intro x hx
              simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
              subst hx
              simp [Finset.coe_insert]
            · simp; omega
          · obtain ⟨Bv, hBv, hBeq⟩ := ih (k - a N) hpos hk'le
            have haNnotin : a N ∉ Bv := by
              intro hmem
              have := hBv hmem
              simp only [Finset.mem_coe] at this
              exact hnotin this
            refine ⟨insert (a N) Bv, ?_, ?_⟩
            · rw [himg]
              intro x hx
              rw [Finset.coe_insert] at hx ⊢
              rcases Set.mem_insert_iff.mp hx with hx | hx
              · subst hx; exact Set.mem_insert _ _
              · exact Set.mem_insert_iff.mpr (Or.inr (hBv hx))
            · rw [Finset.sum_insert haNnotin]; omega
  intro k hk1
  obtain ⟨n, hn⟩ := hub k
  have hkC : k ≤ C a (n + 1) := le_trans hn (hmemC n)
  obtain ⟨Bv, hBv, hBeq⟩ := hJ (n + 1) k hk1 hkC
  refine ⟨Bv, ?_, hBeq⟩
  refine hBv.trans ?_
  intro x hx
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Set.mem_range_self i

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

A partial result on the open Erdős Problem 349: it complements `floorSeq_not_entirelyComplete_of_le_two`
(which rules out $5/3 \le \alpha < 2$ for $t \ge 3$) and the integer-pair characterization
`integer_isGoodPair_iff`. Proof: instantiate `entirely_complete_of_doubling` with $a_n =
\lfloor \alpha^n\rfloor$, using `floor_pow_succ_le_two_mul_floor_pow` for the doubling bound. -/
@[category research solved, AMS 11]
theorem isGoodPair_one_alpha_of_lt_three_halves (α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2) :
    IsGoodPair 1 α := by
  set a : ℕ → ℤ := fun n => ⌊α ^ n⌋ with ha
  have ha0 : a 0 = 1 := by simp [ha]
  have hmono : Monotone a := by
    intro m n hmn
    simp only [ha]
    exact Int.floor_le_floor (pow_le_pow_right₀ hα_lo.le hmn)
  have hdouble : ∀ n, a (n + 1) ≤ 2 * a n := by
    intro n; simpa [ha] using floor_pow_succ_le_two_mul_floor_pow α hα_lo hα_hi n
  have hub : ∀ M : ℤ, ∃ n, M ≤ a n := by
    intro M
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((M : ℝ) + 1) hα_lo
    refine ⟨n, ?_⟩
    simp only [ha]
    rw [Int.le_floor]
    have : (M : ℝ) < α ^ n := by linarith
    exact_mod_cast this.le
  have hentire : IsEntirelyAddComplete (Set.range a) :=
    entirely_complete_of_doubling a ha0 hmono hdouble hub
  have hrange : (Set.range (fun n => ⌊(1 : ℝ) * α ^ n⌋)) = Set.range a := by
    congr 1; funext n; simp [ha]
  unfold IsGoodPair
  rw [hrange]
  exact isEntirelyAddComplete_imp_isAddComplete hentire


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
@[category research solved, AMS 11]
theorem isEntirelyAddComplete_of_one_le_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  set a : ℕ → ℤ := fun n => ⌊t * α ^ n⌋ with ha
  have ha0 : a 0 = 1 := by
    simp only [ha]; exact floorSeq_zero_eq_one_of_lt_two t α ht1 ht2
  have hmono : Monotone a := by
    intro m n hmn
    simp only [ha]
    exact Int.floor_le_floor (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα_lo.le hmn)
      (by linarith))
  have hdouble : ∀ n, a (n + 1) ≤ 2 * a n := by
    intro n; simpa [ha] using floor_mul_pow_succ_le_two_mul t α hα_lo hα_hi ht1 n
  have hub : ∀ M : ℤ, ∃ n, M ≤ a n := by
    intro M
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((M : ℝ) + 1) hα_lo
    refine ⟨n, ?_⟩
    simp only [ha]
    rw [Int.le_floor]
    have hM : (M : ℝ) < α ^ n := by linarith
    have : (M : ℝ) < t * α ^ n := by nlinarith [ht1, hM, pow_pos (by linarith : (0 : ℝ) < α) n]
    exact_mod_cast this.le
  exact entirely_complete_of_doubling a ha0 hmono hdouble hub

/-- **Erdős Problem 349, good pair for $1 \le t < 2$ on the strip $1 < \alpha < 3/2$.**

Corollary of `isEntirelyAddComplete_of_one_le_lt_two`, lifted from entire to eventual
completeness via `isEntirelyAddComplete_imp_isAddComplete`. A partial result on the named open
conjecture `complete_for_alpha_in_Ioo_one_to_goldenRatio`, restricted to $\alpha < 3/2$ and
$t < 2$.

The proof is recorded via the `formal_proof` mechanism rather than written inline, as it exceeds
the repository's proof-length guideline (it depends on a linked theorem). -/
@[category research solved, AMS 11]
theorem isGoodPair_of_one_le_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    IsGoodPair t α := by
  have hentire := isEntirelyAddComplete_of_one_le_lt_two t α hα_lo hα_hi ht1 ht2
  unfold IsGoodPair
  exact isEntirelyAddComplete_imp_isAddComplete hentire

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
@[category research solved, AMS 11]
theorem not_entirelyComplete_of_two_le (t α : ℝ) (ht : 2 ≤ t) (hα : 1 ≤ α) :
    ¬ IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  intro hcomplete
  obtain ⟨B, hB, hBeq⟩ := hcomplete 1 (le_refl 1)
  have hge : ∀ x ∈ B, (2 : ℤ) ≤ x := by
    intro x hx
    have hxrange : x ∈ Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) := hB hx
    obtain ⟨n, hn⟩ := hxrange
    rw [← hn, Int.le_floor]
    have hone : (1 : ℝ) ≤ α ^ n := one_le_pow₀ hα
    push_cast
    nlinarith [hone, ht]
  rcases B.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty] at hBeq; exact absurd hBeq (by norm_num)
  · obtain ⟨x, hx⟩ := hne
    have hpos : ∀ i ∈ B, (0 : ℤ) ≤ i := fun i hi => le_trans (by norm_num) (hge i hi)
    have hle : x ≤ ∑ i ∈ B, i := Finset.single_le_sum (f := fun i => i) hpos hx
    have h2x : (2 : ℤ) ≤ x := hge x hx
    rw [← hBeq] at hle
    omega

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
@[category research solved, AMS 11]
theorem entirelyComplete_floorSeq_iff_lt_two (t α : ℝ) (hα_lo : 1 < α) (hα_hi : α < 3 / 2)
    (ht1 : 1 ≤ t) :
    IsEntirelyAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) ↔ t < 2 := by
  constructor
  · intro hcomplete
    by_contra hge
    exact not_entirelyComplete_of_two_le t α (not_lt.mp hge) hα_lo.le hcomplete
  · intro ht2
    exact isEntirelyAddComplete_of_one_le_lt_two t α hα_lo hα_hi ht1 ht2


end Erdos349

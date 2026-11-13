/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Div
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.AbelSummation

/-!
# Section 2: Valuation-Parity Equidistribution of Factorials

This module translates and formalizes Section 2 of the manuscript:
* `lemma_2_1_i`, `lemma_2_1_ii`: Harmonic prime layers and asymptotics of `𝒫_odd(n)` and `log q_n`.
* `lemma_2_2_i`, `lemma_2_2_ii`: Exact Legendre base-`p` digit reduction on `3 ≤ p ≤ √n`.
* `lemma_2_3`: Vaaler trigonometric polynomial approximation with even-harmonic cancellation.
* `lemma_2_4_i`, `lemma_2_4_ii`: Prime exponential sum bounds on `[n^δ, n / (log n)^{12}]`
  (with Audit Item 1 documenting the middle exponent in Eq. (2.15) and `η_δ` in Eq. (2.16)).
* `theorem_2_5_i`, `theorem_2_5_ii`, `theorem_2_5_iii`: Second-order discrepancy formula,
  full-range 50–50 weight split, and multi-modulus power-band equidistribution.
* `prop_2_6`: Jessen–Wintner Rademacher limit distribution of the truncated base-`p` parity series.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 2.1 Harmonic Prime Layers and the Square-Free Factorial Core -/

/-- Harmonic layer `I_j(n) = (n/(j+1), n/j]` as integers `p` with `n / (j + 1) < p ∧ p ≤ n / j`. -/
def harmonicLayer (n j : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun p => p.Prime ∧ (n : ℝ) / ((j : ℝ) + 1) < p ∧ (p : ℝ) ≤ (n : ℝ) / (j : ℝ)

private lemma mem_harmonicLayer_iff {n j p : ℕ} (hj : 1 ≤ j) :
    p ∈ harmonicLayer n j ↔ p.Prime ∧ p ≤ n ∧ n / (j + 1) < p ∧ p ≤ n / j := by
  unfold harmonicLayer
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hpn⟩, hp, hlt, hle⟩
    have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have h1 : n < p * (j + 1) := by
      have : (n : ℝ) < (p : ℝ) * ((j : ℝ) + 1) := (div_lt_iff₀ hj1pos).mp hlt
      exact_mod_cast this
    have h2 : p * j ≤ n := by
      have : (p : ℝ) * (j : ℝ) ≤ (n : ℝ) := (le_div_iff₀ hjpos).mp hle
      exact_mod_cast this
    exact ⟨hp, hpn, (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mpr h1,
      (Nat.le_div_iff_mul_le hj).mpr h2⟩
  · rintro ⟨hp, hpn, hlt, hle⟩
    have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have h1 : n < p * (j + 1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hlt
    have h2 : p * j ≤ n := (Nat.le_div_iff_mul_le hj).mp hle
    refine ⟨⟨hp.two_le, hpn⟩, hp, (div_lt_iff₀ hj1pos).mpr ?_, (le_div_iff₀ hjpos).mpr ?_⟩
    · exact_mod_cast h1
    · exact_mod_cast h2

private lemma padicValNat_factorial_of_lt_sq {n p : ℕ} (hp : p.Prime) (hnsq : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p n < 2 := by
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · exact (Nat.log_lt_iff_lt_pow hp.one_lt (by norm_num)).mpr hnsq
  rw [padicValNat_factorial hlog]
  have hico : Finset.Ico 1 2 = {1} := by decide
  rw [hico, Finset.sum_singleton, pow_one]

private lemma padicValNat_prod_primes_pow {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) (e : ℕ → ℕ) :
    padicValNat p (∏ q ∈ S, q ^ e q) = if p ∈ S then e p else 0 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.prod (fun q hq => pow_ne_zero _ (hS q hq).ne_zero)]
  have hterm : ∀ q ∈ S, padicValNat p (q ^ e q) = if q = p then e p else 0 := by
    intro q hq
    rw [padicValNat.pow _ (hS q hq).ne_zero]
    by_cases hqp : q = p
    · subst hqp; simp [padicValNat_self hp.one_lt]
    · simp only [hqp, ↓reduceIte]
      have hndvd : ¬ p ∣ q := fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hd).symm
      rw [padicValNat.eq_zero_of_not_dvd hndvd, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']

theorem lemma_2_1_i (n j : ℕ) (hn : 4 ≤ n) (hj1 : 1 ≤ j) (hj2 : j ≤ Nat.sqrt n - 1) :
    (∀ p ∈ harmonicLayer n j, padicValNat p n.factorial = j) ∧
    (∀ r : ℕ, j = 2 * r - 1 → ∀ p ∈ harmonicLayer n j,
      p ∈ Podd n ∧ padicValNat p (qn n) = 1 ∧ padicValNat p (sn n) = r - 1) ∧
    (∀ r : ℕ, j = 2 * r → ∀ p ∈ harmonicLayer n j,
      p ∈ Peven n ∧ padicValNat p (qn n) = 0 ∧ padicValNat p (sn n) = r) := by
  have hsqrt2 : 2 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]; omega
  have hj1_le_sqrt : j + 1 ≤ Nat.sqrt n := by omega
  have hj1_sq_le_n : (j + 1) ^ 2 ≤ n := by
    calc (j + 1) ^ 2 ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hj1_le_sqrt 2
      _ ≤ n := Nat.sqrt_le n
  have hp_val : ∀ p ∈ harmonicLayer n j, padicValNat p n.factorial = j := by
    intro p hp
    rcases (mem_harmonicLayer_iff hj1).mp hp with ⟨hp_prime, _, hlt, hle⟩
    have hsqrt_le_div : Nat.sqrt n ≤ n / (j + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.succ_pos j)]
      calc Nat.sqrt n * (j + 1) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_left _ hj1_le_sqrt
        _ ≤ n := Nat.sqrt_le n
    have hp_gt_sqrt : Nat.sqrt n < p := lt_of_le_of_lt hsqrt_le_div hlt
    have hn_lt_psq : n < p ^ 2 := by
      have h1 : Nat.sqrt n + 1 ≤ p := hp_gt_sqrt
      calc n < (Nat.sqrt n + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt' n
        _ ≤ p ^ 2 := Nat.pow_le_pow_left h1 2
    rw [padicValNat_factorial_of_lt_sq hp_prime hn_lt_psq]
    have hmul_le : j * p ≤ n := by
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le hj1).mp hle
    have hn_lt_mul : n < (j + 1) * p := by
      rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hlt
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp_prime.pos).mpr hn_lt_mul)
    · exact (Nat.le_div_iff_mul_le hp_prime.pos).mpr hmul_le
  refine ⟨hp_val, ?_, ?_⟩
  · intro r hr p hp
    have hv := hp_val p hp
    rcases (mem_harmonicLayer_iff hj1).mp hp with ⟨hp_prime, hpn, _, _⟩
    have hr1 : 1 ≤ r := by omega
    have hodd : ¬ 2 ∣ padicValNat p n.factorial := by omega
    have hp_Podd : p ∈ Podd n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hpn⟩, hp_prime, hodd⟩
    refine ⟨hp_Podd, ?_, ?_⟩
    · rw [qn_eq_prod_Podd, padicValNat_prod_primes_pow hp_prime (Podd n)
        (fun q hq => (Finset.mem_filter.mp hq).2.1) (fun _ => 1), if_pos hp_Podd]
    · rw [sn_eq_prod_primes, padicValNat_prod_primes_pow hp_prime _
        (fun q hq => (Finset.mem_filter.mp hq).2) (fun q => padicValNat q n.factorial / 2)]
      have hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hpn⟩, hp_prime⟩
      rw [if_pos hmem, hv, hr]
      omega
  · intro r hr p hp
    have hv := hp_val p hp
    rcases (mem_harmonicLayer_iff hj1).mp hp with ⟨hp_prime, hpn, _, _⟩
    have heven : 2 ∣ padicValNat p n.factorial := by omega
    have hp_Peven : p ∈ Peven n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hpn⟩, hp_prime, heven⟩
    refine ⟨hp_Peven, ?_, ?_⟩
    · rw [qn_eq_prod_Podd, padicValNat_prod_primes_pow hp_prime (Podd n)
        (fun q hq => (Finset.mem_filter.mp hq).2.1) (fun _ => 1)]
      have hnot : p ∉ Podd n := Finset.disjoint_right.mp (Podd_disjoint_Peven n) hp_Peven
      rw [if_neg hnot]
    · rw [sn_eq_prod_primes, padicValNat_prod_primes_pow hp_prime _
        (fun q hq => (Finset.mem_filter.mp hq).2) (fun q => padicValNat q n.factorial / 2)]
      have hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hpn⟩, hp_prime⟩
      rw [if_pos hmem, hv, hr]
      omega

private lemma alternating_harmonic_pair_sum_eq (K : ℕ) :
    Real.log 2 - ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) =
      ∫ t in (0 : ℝ)..1, t ^ (2 * K) / (1 + t) := by
  have hsum_eq :
      ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) =
        ∑ j ∈ Finset.range (2 * K), (-1 : ℝ) ^ j / ((j : ℝ) + 1) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.mul_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, add_assoc]
      congr 1
      have hpow1 : (-1 : ℝ) ^ (2 * K) = 1 := by simp [pow_mul]
      have hpow2 : (-1 : ℝ) ^ (2 * K + 1) = -1 := by simp [pow_succ, pow_mul]
      rw [hpow1, hpow2]
      push_cast
      ring
  rw [hsum_eq]
  have hint_log : ∫ t in (0 : ℝ)..1, (1 + t)⁻¹ = Real.log 2 := by
    have h := integral_inv_of_pos (a := (1 : ℝ)) (b := 2) zero_lt_one zero_lt_two
    have hc : ∫ t in (0 : ℝ)..1, (t + 1)⁻¹ = ∫ t in (1 : ℝ)..2, t⁻¹ := by
      simpa using intervalIntegral.integral_comp_add_right (fun t : ℝ => t⁻¹) (1 : ℝ) (a := 0) (b := 1)
    rw [div_one] at h
    calc ∫ t in (0 : ℝ)..1, (1 + t)⁻¹ = ∫ t in (0 : ℝ)..1, (t + 1)⁻¹ := by
          refine intervalIntegral.integral_congr fun t _ => by ring
      _ = Real.log 2 := by rw [hc, h]
  have hint_pow :
      ∑ j ∈ Finset.range (2 * K), (-1 : ℝ) ^ j / ((j : ℝ) + 1) =
        ∫ t in (0 : ℝ)..1, ∑ j ∈ Finset.range (2 * K), (-t) ^ j := by
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : ∀ t : ℝ, (-t) ^ j = (-1 : ℝ) ^ j * t ^ j := fun t => by rw [← mul_pow]; ring_nf
      simp_rw [h1]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    · intro j _
      exact (Continuous.intervalIntegrable (by fun_prop) 0 1)
  have hpoly : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      (1 + t)⁻¹ - ∑ j ∈ Finset.range (2 * K), (-t) ^ j = t ^ (2 * K) / (1 + t) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hg : (∑ j ∈ Finset.range (2 * K), (-t) ^ j) * (1 - (-t)) = 1 - (-t) ^ (2 * K) :=
      geom_sum_mul_neg (-t) (2 * K)
    have heven : (-t) ^ (2 * K) = t ^ (2 * K) := by rw [pow_mul, neg_sq, ← pow_mul]
    rw [heven] at hg
    have hg' : (∑ j ∈ Finset.range (2 * K), (-t) ^ j) * (1 + t) = 1 - t ^ (2 * K) := by
      simpa [sub_neg_eq_add] using hg
    field_simp [hpos.ne']
    linarith
  rw [← hint_log, hint_pow, ← intervalIntegral.integral_sub]
  · exact intervalIntegral.integral_congr hpoly
  · refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact continuousAt_inv₀ (by linarith [ht.1])
  · exact (Continuous.intervalIntegrable (by fun_prop) 0 1)

private lemma alternating_harmonic_tail_bound (K : ℕ) :
    0 ≤ Real.log 2 - ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) ∧
    Real.log 2 - ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) ≤
      1 / (2 * (K : ℝ) + 1) := by
  rw [alternating_harmonic_pair_sum_eq]
  have hint1 : IntervalIntegrable (fun t : ℝ => t ^ (2 * K) / (1 + t)) MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    fun_prop (disch := linarith)
  have hint2 : IntervalIntegrable (fun t : ℝ => t ^ (2 * K)) MeasureTheory.volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  constructor
  · refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
    exact div_nonneg (pow_nonneg ht.1 _) (by linarith [ht.1])
  · calc ∫ t in (0 : ℝ)..1, t ^ (2 * K) / (1 + t)
        ≤ ∫ t in (0 : ℝ)..1, t ^ (2 * K) := by
          refine intervalIntegral.integral_mono_on zero_le_one hint1 hint2 fun t ht => ?_
          exact div_le_self (pow_nonneg ht.1 _) (by linarith [ht.1])
      _ = 1 / (2 * (K : ℝ) + 1) := by
          rw [integral_pow]; norm_num; push_cast; ring

private lemma sum_log_harmonicLayer {n j : ℕ} (hj : 1 ≤ j) :
    ∑ p ∈ harmonicLayer n j, Real.log p =
      Chebyshev.theta ((n : ℝ) / (j : ℝ)) - Chebyshev.theta ((n : ℝ) / ((j : ℝ) + 1)) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsub : ((Finset.Ioc 0 ⌊(n : ℝ) / ((j : ℝ) + 1)⌋₊).filter Nat.Prime) ⊆
      ((Finset.Ioc 0 ⌊(n : ℝ) / (j : ℝ)⌋₊).filter Nat.Prime) := by
    refine Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right ?_)
    exact Nat.floor_mono (div_le_div_of_nonneg_left hn0 hjpos (by linarith))
  have hsdiff :
      ((Finset.Ioc 0 ⌊(n : ℝ) / (j : ℝ)⌋₊).filter Nat.Prime) \
          ((Finset.Ioc 0 ⌊(n : ℝ) / ((j : ℝ) + 1)⌋₊).filter Nat.Prime) =
        harmonicLayer n j := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, mem_harmonicLayer_iff hj]
    constructor
    · rintro ⟨⟨⟨hp0, hp1⟩, hp_prime⟩, hnot⟩
      have hpn_le : p ≤ n / j := Nat.le_floor_iff (div_nonneg hn0 hjpos.le) |>.mp hp1 |>.trans_eq rfl |> fun h => by
        rw [Nat.le_div_iff_mul_le hj]
        have : (p : ℝ) * (j : ℝ) ≤ (n : ℝ) := (le_div_iff₀ hjpos).mp ((Nat.le_floor_iff (div_nonneg hn0 hjpos.le)).mp hp1)
        exact_mod_cast this
      have hpn : p ≤ n := hpn_le.trans (Nat.div_le_self n j)
      have hgt : n / (j + 1) < p := by
        by_contra hle
        rw [not_lt] at hle
        apply hnot
        refine ⟨⟨hp0, (Nat.le_floor_iff (div_nonneg hn0 hj1pos.le)).mpr ?_⟩, hp_prime⟩
        rw [le_div_iff₀ hj1pos]
        exact_mod_cast (Nat.le_div_iff_mul_le (Nat.succ_pos j)).mp hle
      exact ⟨hp_prime, hpn, hgt, hpn_le⟩
    · rintro ⟨hp_prime, _, hgt, hle⟩
      refine ⟨⟨hp_prime.pos, (Nat.le_floor_iff (div_nonneg hn0 hjpos.le)).mpr ?_⟩, ?_⟩
      · rw [le_div_iff₀ hjpos]
        exact_mod_cast (Nat.le_div_iff_mul_le hj).mp hle
      · rintro ⟨⟨_, hfl⟩, _⟩
        have : (p : ℝ) ≤ (n : ℝ) / ((j : ℝ) + 1) := (Nat.le_floor_iff (div_nonneg hn0 hj1pos.le)).mp hfl
        have : p * (j + 1) ≤ n := by exact_mod_cast (le_div_iff₀ hj1pos).mp this
        have : p ≤ n / (j + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos j)).mpr this
        omega
  unfold Chebyshev.theta
  rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]

private lemma card_harmonicLayer {n j : ℕ} (hj : 1 ≤ j) :
    (harmonicLayer n j).card =
      Nat.primeCounting ⌊(n : ℝ) / (j : ℝ)⌋₊ - Nat.primeCounting ⌊(n : ℝ) / ((j : ℝ) + 1)⌋₊ := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : ⌊(n : ℝ) / ((j : ℝ) + 1)⌋₊ ≤ ⌊(n : ℝ) / (j : ℝ)⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_left hn0 hjpos (by linarith))
  have hpi : ∀ N : ℕ, Nat.primeCounting N = ((Finset.Ioc 0 N).filter Nat.Prime).card := by
    intro N
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
    congr 1 with p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor <;> rintro ⟨hp1, hp⟩ <;> exact ⟨⟨by omega, hp1.2⟩, hp⟩
  rw [hpi, hpi]
  have hsub : ((Finset.Ioc 0 ⌊(n : ℝ) / ((j : ℝ) + 1)⌋₊).filter Nat.Prime) ⊆
      ((Finset.Ioc 0 ⌊(n : ℝ) / (j : ℝ)⌋₊).filter Nat.Prime) :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hle)
  rw [← Finset.card_sdiff hsub]
  congr 1
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, mem_harmonicLayer_iff hj]
  constructor
  · rintro ⟨⟨⟨hp0, hp1⟩, hp_prime⟩, hnot⟩
    have hpn_le : p ≤ n / j := by
      rw [Nat.le_div_iff_mul_le hj]
      have : (p : ℝ) * (j : ℝ) ≤ (n : ℝ) := (le_div_iff₀ hjpos).mp ((Nat.le_floor_iff (div_nonneg hn0 hjpos.le)).mp hp1)
      exact_mod_cast this
    have hpn : p ≤ n := hpn_le.trans (Nat.div_le_self n j)
    have hgt : n / (j + 1) < p := by
      by_contra hlt'
      rw [not_lt] at hlt'
      apply hnot
      refine ⟨⟨hp0, (Nat.le_floor_iff (by positivity)).mpr ?_⟩, hp_prime⟩
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast (Nat.le_div_iff_mul_le (Nat.succ_pos j)).mp hlt'
    exact ⟨hp_prime, hpn, hgt, hpn_le⟩
  · rintro ⟨hp_prime, _, hgt, hle'⟩
    refine ⟨⟨hp_prime.pos, (Nat.le_floor_iff (div_nonneg hn0 hjpos.le)).mpr ?_⟩, ?_⟩
    · rw [le_div_iff₀ hjpos]
      exact_mod_cast (Nat.le_div_iff_mul_le hj).mp hle'
    · rintro ⟨⟨_, hfl⟩, _⟩
      have : (p : ℝ) ≤ (n : ℝ) / ((j : ℝ) + 1) := (Nat.le_floor_iff (by positivity)).mp hfl
      have : p * (j + 1) ≤ n := by exact_mod_cast (le_div_iff₀ (by positivity)).mp this
      have : p ≤ n / (j + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos j)).mpr this
      omega

private lemma li_sub_div_log_isBigO :
    (fun x : ℝ => (∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) - x / Real.log x) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ 2) := by
  have hint_id : ∀ᶠ x in atTop,
      (∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) - x / Real.log x =
        (-2 / Real.log 2) + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun u : ℝ => u / Real.log u) ((Real.log t)⁻¹ - 1 / (Real.log t) ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have htpos : 0 < t := by linarith [ht.1]
      have hlogne : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      have hd := (hasDerivAt_id t).div (Real.hasDerivAt_log htpos.ne') hlogne
      convert hd using 1
      field_simp [htpos.ne', hlogne]
    have hint1 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 2 x := by
      refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      have hlogne : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      fun_prop (disch := exact hlogne)
    have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 2) MeasureTheory.volume 2 x :=
      Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
    rw [intervalIntegral.integral_sub hint1 hint2] at hftc
    linarith
  have hconst : (fun _ : ℝ => (-2 : ℝ) / Real.log 2) =O[atTop] (fun x : ℝ => x / (Real.log x) ^ 2) := by
    have hlog2_sq : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num)
    have hbound : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ 2 ≤ x := by
      have hb := hlog2_sq.bound (by norm_num : (0 : ℝ) < 1)
      filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx1
      have h1 : Real.log x ^ (2 : ℝ) = (Real.log x) ^ 2 := by norm_cast
      have h2 : x ^ (1 : ℝ) = x := Real.rpow_one x
      rw [h1, h2, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by linarith), one_mul] at hx
      exact hx
    refine Asymptotics.IsBigO.of_bound (|(-2 : ℝ) / Real.log 2|) ?_
    filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlog_pos : 0 < Real.log x := Real.log_pos hx1
    have h1 : 1 ≤ x / (Real.log x) ^ 2 := (one_le_div (sq_pos_of_pos hlog_pos)).mpr hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    nlinarith [abs_nonneg ((-2 : ℝ) / Real.log 2)]
  have hsum : (fun x : ℝ => (-2 / Real.log 2) + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ 2) :=
    hconst.add Chebyshev.integral_one_div_log_sq_isBigO
  exact hsum.congr' (by filter_upwards [hint_id] with x hx; exact hx.symm) EventuallyEq.rfl

theorem lemma_2_1_ii :
    (∃ c₀ : ℝ, 0 < c₀ ∧
      IsBigOAtTop (fun n => Real.log (qn n) - Real.log 2 * n)
        (fun n => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n)))) ∧
    Tendsto (fun n : ℕ => ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hpnt⟩ := deLaValleePoussin_pnt
  have hlog_qn : ∀ n : ℕ, Real.log (qn n : ℝ) = ∑ p ∈ Podd n, Real.log (p : ℝ) := by
    intro n
    rw [qn_eq_prod_Podd, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.1.ne_zero
  -- Partition Podd n into harmonic layers 2r-1 (1 ≤ r ≤ K) and the remaining primes ≤ n/(2K+1)
  have hpart_odd : ∀ n : ℕ, 4 ≤ n →
      let K : ℕ := (Nat.sqrt n - 1) / 2
      let L : Finset ℕ := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
      let Tail : Finset ℕ := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
      Disjoint L Tail ∧ L ∪ Tail = Podd n ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ s ∈ Finset.Icc 1 K, r ≠ s →
        Disjoint (harmonicLayer n (2 * r - 1)) (harmonicLayer n (2 * s - 1))) := by
    intro n hn K L Tail
    have hK_le : 2 * K + 1 ≤ Nat.sqrt n := by omega
    have hdisj_rs : ∀ r ∈ Finset.Icc 1 K, ∀ s ∈ Finset.Icc 1 K, r ≠ s →
        Disjoint (harmonicLayer n (2 * r - 1)) (harmonicLayer n (2 * s - 1)) := by
      intro r hr s hs hrs
      rw [Finset.disjoint_left]
      intro p hpr hps
      have hr1 : 1 ≤ 2 * r - 1 := by simp only [Finset.mem_Icc] at hr; omega
      have hs1 : 1 ≤ 2 * s - 1 := by simp only [Finset.mem_Icc] at hs; omega
      have hr2 : 2 * r - 1 ≤ Nat.sqrt n - 1 := by simp only [Finset.mem_Icc] at hr; omega
      have hs2 : 2 * s - 1 ≤ Nat.sqrt n - 1 := by simp only [Finset.mem_Icc] at hs; omega
      have hv1 := (lemma_2_1_i n (2 * r - 1) hn hr1 hr2).1 p hpr
      have hv2 := (lemma_2_1_i n (2 * s - 1) hn hs1 hs2).1 p hps
      omega
    have hL_gt : ∀ p ∈ L, n / (2 * K + 1) < p := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨r, hr, hpr⟩
      simp only [Finset.mem_Icc] at hr
      have hr1 : 1 ≤ 2 * r - 1 := by omega
      rcases (mem_harmonicLayer_iff hr1).mp hpr with ⟨_, _, hgt, _⟩
      have hdiv : n / (2 * K + 1) ≤ n / ((2 * r - 1) + 1) :=
        Nat.div_le_div_left (by omega) (by omega)
      exact lt_of_le_of_lt hdiv hgt
    have hL_sub : L ⊆ Podd n := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨r, hr, hpr⟩
      simp only [Finset.mem_Icc] at hr
      have hr1 : 1 ≤ 2 * r - 1 := by omega
      have hr2 : 2 * r - 1 ≤ Nat.sqrt n - 1 := by omega
      exact ((lemma_2_1_i n (2 * r - 1) hn hr1 hr2).2.1 r rfl p hpr).1
    refine ⟨?_, ?_, hdisj_rs⟩
    · rw [Finset.disjoint_left]
      intro p hpL hpT
      have h1 := hL_gt p hpL
      have h2 := (Finset.mem_filter.mp hpT).2
      omega
    · ext p
      constructor
      · intro hp
        rcases Finset.mem_union.mp hp with hpL | hpT
        · exact hL_sub hpL
        · exact (Finset.mem_filter.mp hpT).1
      · intro hp
        by_cases hle : p ≤ n / (2 * K + 1)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hle⟩)
        · rw [Finset.mem_union]
          left
          have hgt : n / (2 * K + 1) < p := not_le.mp hle
          have hp_mem := hp
          simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hp_mem
          rcases hp_mem with ⟨⟨_, hpn⟩, hp_prime, hodd⟩
          have hsqrt_le : Nat.sqrt n ≤ n / Nat.sqrt n := by
            rw [Nat.le_div_iff_mul_le (Nat.sqrt_pos.mpr (by omega))]
            exact Nat.sqrt_le n
          have hdiv_le : n / Nat.sqrt n ≤ n / (2 * K + 1) :=
            Nat.div_le_div_left hK_le (by omega)
          have hp_gt_sqrt : Nat.sqrt n < p := lt_of_le_of_lt (hsqrt_le.trans hdiv_le) hgt
          have hnsq : n < p ^ 2 := by
            calc n < (Nat.sqrt n + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt' n
              _ ≤ p ^ 2 := Nat.pow_le_pow_left hp_gt_sqrt 2
          have hv : padicValNat p n.factorial = n / p := padicValNat_factorial_of_lt_sq hp_prime hnsq
          rw [hv] at hodd
          set j : ℕ := n / p
          have hj1 : 1 ≤ j := Nat.div_pos hpn hp_prime.pos
          have hj_lt : j < 2 * K + 1 := by
            by_contra hge
            rw [not_lt] at hge
            have : p * (2 * K + 1) ≤ p * j := Nat.mul_le_mul_left p hge
            have hmul : p * j ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n p
            have hle' : p ≤ n / (2 * K + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (this.trans hmul)
            omega
          have hj_odd : j % 2 = 1 := Nat.mod_two_ne_zero.mpr (fun h0 => hodd (Nat.dvd_of_mod_eq_zero h0))
          set r : ℕ := (j + 1) / 2
          have hr_mem : r ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hj_eq : j = 2 * r - 1 := by omega
          refine Finset.mem_biUnion.mpr ⟨r, hr_mem, (mem_harmonicLayer_iff (by omega)).mpr ⟨hp_prime, hpn, ?_, ?_⟩⟩
          · rw [← hj_eq]
            rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos j), mul_comm]
            exact Nat.lt_div_mul_add hp_prime.pos |>.trans_eq (by ring)
          · rw [← hj_eq, Nat.le_div_iff_mul_le hj1, mul_comm]
            exact Nat.div_mul_le_self n p
  -- Eventual growth helpers for n : ℕ
  have h_inf : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h_log : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp h_inf
  have h_sqrt_log : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp h_log
  have hev_setup : ∀ᶠ n : ℕ in atTop,
      16 ≤ n ∧
      (c₁ / 2 + 4) ≤ Real.sqrt (Real.log (n : ℝ)) ∧
      (1 + Real.log 2 + Real.log (n : ℝ)) ≤ Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) ∧
      (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have h1 : ∀ᶠ n : ℕ in atTop, 16 ≤ n := eventually_ge_atTop 16
    have h2 : ∀ᶠ n : ℕ in atTop, (c₁ / 2 + 4) ≤ Real.sqrt (Real.log (n : ℝ)) :=
      h_sqrt_log.eventually (eventually_ge_atTop _)
    have h3 : ∀ᶠ n : ℕ in atTop,
        (1 + Real.log 2 + Real.log (n : ℝ)) ≤ Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
      have hexp0 : Tendsto (fun x : ℝ => (1 + Real.log 2 + (4 / c₁) ^ 2 * x ^ 2) * Real.exp (-x)) atTop (𝓝 0) := by
        have ht0 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
          Real.tendsto_exp_atTop.comp tendsto_neg_atTop_atTop |> fun _ =>
            by simpa using Real.tendsto_exp_neg_atTop_nhds_zero
        have ht2 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
          Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
        have ht_comb : Tendsto (fun x : ℝ => (1 + Real.log 2) * Real.exp (-x) + (4 / c₁) ^ 2 * (x ^ 2 * Real.exp (-x)))
            atTop (𝓝 ((1 + Real.log 2) * 0 + (4 / c₁) ^ 2 * 0)) :=
          (ht0.const_mul (1 + Real.log 2)).add (ht2.const_mul ((4 / c₁) ^ 2))
        simp only [mul_zero, add_zero] at ht_comb
        refine ht_comb.congr' (Eventually.of_forall fun x => ?_)
        ring
      have hcomp := hexp0.comp (h_sqrt_log.const_mul_atTop (by positivity : 0 < c₁ / 4))
      have hev1 : ∀ᶠ n : ℕ in atTop,
          (1 + Real.log 2 + (4 / c₁) ^ 2 * ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) ^ 2) *
            Real.exp (-((c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) ≤ 1 :=
        hcomp.eventually (eventually_le_nhds one_pos)
      filter_upwards [hev1, h2] with n hn hsq
      have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
        have : (0 : ℝ) < Real.sqrt (Real.log (n : ℝ)) := by linarith
        by_contra hlt
        rw [not_le] at hlt
        rw [Real.sqrt_eq_zero_of_nonpos hlt.le] at this
        linarith
      have hmul_eq : (4 / c₁) ^ 2 * ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) := by
        have hc1ne : c₁ ≠ 0 := hc₁.ne'
        rw [mul_pow, Real.sq_sqrt hlog_nonneg]
        field_simp [hc1ne]
      rw [hmul_eq, ← neg_mul] at hn
      exact (mul_le_iff_le_one_right (Real.exp_pos _)).mp (by
        calc (1 + Real.log 2 + Real.log (n : ℝ)) * (Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))))⁻¹
            = (1 + Real.log 2 + Real.log (n : ℝ)) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
              rw [Real.exp_neg]; ring_nf
          _ ≤ 1 := hn)
    have h4 : ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
      have ho : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) :=
        isLittleO_log_rpow_rpow_atTop 2 zero_lt_one
      filter_upwards [(ho.bound zero_lt_one).comp_tendsto h_inf, eventually_ge_atTop 2] with n hn hn2
      have hpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      simpa [Real.rpow_two, Real.rpow_one, Real.norm_of_nonneg hpos, Real.norm_of_nonneg (Nat.cast_nonneg n)] using hn
    exact h1.and (h2.and (h3.and h4))
  -- Common structural bounds for all large n
  have hlayer_log_bound : ∀ n : ℕ, 16 ≤ n → (c₁ / 2 + 4) ≤ Real.sqrt (Real.log (n : ℝ)) →
      ∀ j ∈ Finset.Icc 1 (Nat.sqrt n - 1),
        (2 : ℝ) ≤ (n : ℝ) / (j : ℝ) ∧
        (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log ((n : ℝ) / (j : ℝ))) ∧
        (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log ((n : ℝ) / (j : ℝ)) := by
    intro n hn hsq j hj
    simp only [Finset.mem_Icc] at hj
    have hsqrt_le : (j : ℝ) ≤ Real.sqrt n := by
      have hj_le : j ≤ Nat.sqrt n := by omega
      exact (Nat.cast_le.mpr hj_le).trans (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _) |>.mpr (by exact_mod_cast Nat.sqrt_le n))
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj.1
    have hn_ge_sqrt : Real.sqrt n ≤ (n : ℝ) / (j : ℝ) := by
      rw [le_div_iff₀ hjpos]
      calc Real.sqrt n * (j : ℝ) ≤ Real.sqrt n * Real.sqrt n := by gcongr
        _ = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have h4sqrt : (4 : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast (by omega : 16 ≤ n))
    have h2le : (2 : ℝ) ≤ (n : ℝ) / (j : ℝ) := by linarith
    have hlog_half : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log ((n : ℝ) / (j : ℝ)) := by
      rw [← Real.log_sqrt (by exact_mod_cast (by omega : 0 < n))]
      exact Real.log_le_log (by positivity) hn_ge_sqrt
    have hsqrt_half : (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log ((n : ℝ) / (j : ℝ))) := by
      have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith)
    exact ⟨h2le, hsqrt_half, hlog_half⟩
  have hsqrt_exp_bound : ∀ n : ℕ, 16 ≤ n → (c₁ / 2 + 4) ≤ Real.sqrt (Real.log (n : ℝ)) →
      Real.sqrt (n : ℝ) ≤ (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
    intro n hn hsq
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn_pos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hexp_le : (c₁ / 4) * Real.sqrt (Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      have hsq2 : (c₁ / 2) * Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) := by
        gcongr; linarith
      rw [Real.mul_self_sqrt hlogn_pos] at hsq2
      linarith
    have h1 : Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) ≤ Real.sqrt n := by
      calc Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))
          ≤ Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexp_le
        _ = Real.sqrt n := by
            rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]; ring_nf
    calc Real.sqrt (n : ℝ) = (n : ℝ) / Real.sqrt (n : ℝ) := by
          rw [eq_div_iff (Real.sqrt_ne_zero'.mpr hn0), Real.mul_self_sqrt hn0.le]
      _ ≤ (n : ℝ) / Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by gcongr
      _ = (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
          rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf
  -- Part 1: Asymptotic formula for log (qn n)
  have hpart1 : ∃ c₀ : ℝ, 0 < c₀ ∧
      IsBigOAtTop (fun n => Real.log (qn n) - Real.log 2 * n)
        (fun n => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n))) := by
    obtain ⟨N₀, hN₀⟩ := hev_setup.exists_forall_of_atTop
    refine ⟨c₁ / 4, by positivity, 4 * C₁ + 2 * Real.log 4 + 6, by positivity, N₀, fun n hn => ?_⟩
    rcases hN₀ n hn with ⟨hn16, hsq, hlog_exp, _⟩
    have hn4 : 4 ≤ n := by omega
    set K : ℕ := (Nat.sqrt n - 1) / 2
    set L : Finset ℕ := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
    set Tail : Finset ℕ := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
    obtain ⟨hdisj, hunion, hdisj_rs⟩ := hpart_odd n hn4
    have hlog_split : Real.log (qn n : ℝ) =
        (∑ r ∈ Finset.Icc 1 K, (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
          Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))))) +
        ∑ p ∈ Tail, Real.log (p : ℝ) := by
      rw [hlog_qn, ← hunion, Finset.sum_union hdisj, Finset.sum_biUnion (fun r hr s hs hrs => hdisj_rs r hr s hs hrs)]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_Icc] at hr
      have hr1 : 1 ≤ 2 * r - 1 := by omega
      rw [sum_log_harmonicLayer hr1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
      ring_nf
    -- Tail log bound
    have h2K1_ge : (1 / 2 : ℝ) * Real.sqrt n ≤ (2 * (K : ℝ) + 1) := by
      have hsqrt_ge4 : (4 : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast (by omega : 16 ≤ n))
      have h_lt : Real.sqrt n - 1 < (Nat.sqrt n : ℝ) := by
        have : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
        have : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := Real.sqrt_lt' (by positivity) |>.mpr this
        linarith
      have hK_nat : Nat.sqrt n - 2 ≤ 2 * K := by omega
      have hK_real : (Nat.sqrt n : ℝ) - 1 ≤ 2 * (K : ℝ) + 1 := by
        have : ((Nat.sqrt n - 2 : ℕ) : ℝ) ≤ (2 * K : ℕ) := by exact_mod_cast hK_nat
        have hns2 : 2 ≤ Nat.sqrt n := (Nat.le_sqrt).mpr (by omega)
        rw [Nat.cast_sub hns2] at this
        push_cast at this
        linarith
      linarith
    have hTail_le : |∑ p ∈ Tail, Real.log (p : ℝ)| ≤ 2 * Real.log 4 * Real.sqrt n := by
      have hnonneg : 0 ≤ ∑ p ∈ Tail, Real.log (p : ℝ) :=
        Finset.sum_nonneg fun p hp => Real.log_nonneg (by
          have := ((Finset.mem_filter.mp hp).1 |> Finset.mem_filter.mp).2.1.one_le
          exact_mod_cast this)
      rw [abs_of_nonneg hnonneg]
      have hTail_sub : Tail ⊆ (Finset.Ioc 0 ⌊(n : ℝ) / ((2 * (K : ℝ) + 1))⌋₊).filter Nat.Prime := by
        intro p hp
        have hpmem := Finset.mem_filter.mp hp
        have hp_mem := Finset.mem_filter.mp hpmem.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_mem.2.1.pos, (Nat.le_floor_iff (by positivity)).mpr ?_⟩, hp_mem.2.1⟩
        rw [le_div_iff₀ (by positivity)]
        have : p * (2 * K + 1) ≤ n := by
          rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp hpmem.2
        exact_mod_cast this
      calc ∑ p ∈ Tail, Real.log (p : ℝ)
          ≤ ∑ p ∈ (Finset.Ioc 0 ⌊(n : ℝ) / (2 * (K : ℝ) + 1)⌋₊).filter Nat.Prime, Real.log (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hTail_sub fun p _ _ => Real.log_nonneg (by
              have : p = 0 ∨ 1 ≤ p := by omega
              rcases this with rfl | hp1
              · simp
              · exact_mod_cast hp1)
        _ = Chebyshev.theta ((n : ℝ) / (2 * (K : ℝ) + 1)) := rfl
        _ ≤ Real.log 4 * ((n : ℝ) / (2 * (K : ℝ) + 1)) := Chebyshev.theta_le_log4_mul_x (by positivity)
        _ ≤ Real.log 4 * ((n : ℝ) / ((1 / 2 : ℝ) * Real.sqrt n)) := by gcongr; positivity
        _ = 2 * Real.log 4 * Real.sqrt n := by
            have hsn0 : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast (by omega : 0 < n))
            calc Real.log 4 * ((n : ℝ) / ((1 / 2 : ℝ) * Real.sqrt n))
                = 2 * Real.log 4 * ((n : ℝ) / Real.sqrt n) := by ring
              _ = 2 * Real.log 4 * Real.sqrt n := by
                  rw [div_eq_iff hsn0, Real.mul_self_sqrt (Nat.cast_nonneg n)]; ring
    -- Main theta error sum bound over r ∈ Icc 1 K
    have htheta_err :
        |∑ r ∈ Finset.Icc 1 K, ((Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
            Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
            ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))| ≤
          2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
      have hterm_err : ∀ r ∈ Finset.Icc 1 K,
          |(Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
            ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))| ≤
            C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
              Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        have hj1 : 2 * r - 1 ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hj2 : 2 * r ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        obtain ⟨h2_1, hsq_1, _⟩ := hlayer_log_bound n hn16 hsq (2 * r - 1) hj1
        obtain ⟨h2_2, hsq_2, _⟩ := hlayer_log_bound n hn16 hsq (2 * r) hj2
        have hcast1 : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hcast2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
        rw [hcast1] at h2_1 hsq_1
        rw [hcast2] at h2_2 hsq_2
        have hp1 := (hpnt _ h2_1).1
        have hp2 := (hpnt _ h2_2).1
        have hexp1 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1)))) ≤
            Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
          apply Real.exp_le_exp.mpr; nlinarith
        have hexp2 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ))))) ≤
            Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
          apply Real.exp_le_exp.mpr; nlinarith
        calc |(Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))|
            = |(Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)) -
                (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ)))| := by ring_nf
          _ ≤ |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)| +
                |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))| := abs_sub _ _
          _ ≤ C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1)))) +
                C₁ * ((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ))))) := add_le_add hp1 hp2
          _ ≤ C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) +
                C₁ * ((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by gcongr
          _ = C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
                Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by ring
      have hharm_sum :
          ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) ≤
            1 + Real.log (n : ℝ) := by
        have hbound_k : ∀ r ∈ Finset.Icc 1 K,
            (1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ)) ≤
              (1 / ((2 * r - 1 : ℕ) : ℝ)) + (1 / ((2 * r : ℕ) : ℝ)) := by
          intro r hr; rw [Finset.mem_Icc] at hr
          have hc1 : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
          have hc2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
          rw [hc1, hc2]
        have hpair :
            ∑ r ∈ Finset.Icc 1 K, ((1 / ((2 * r - 1 : ℕ) : ℝ)) + (1 / ((2 * r : ℕ) : ℝ))) =
              (harmonic (2 * K) : ℝ) := by
          rw [harmonic_eq_sum_Icc, Rat.cast_sum]
          induction K with
          | zero => simp
          | succ K ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.mul_succ,
              Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
            simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
            rw [show 2 * (K + 1) - 1 = 2 * K + 1 by omega]
            push_cast
            ring
        have hle_harm : (harmonic (2 * K) : ℝ) ≤ 1 + Real.log (n : ℝ) := by
          rcases eq_or_ne K 0 with rfl | hK0
          · simp; exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
          · calc (harmonic (2 * K) : ℝ) ≤ 1 + Real.log (2 * K : ℕ) := harmonic_le_one_add_log (2 * K)
              _ ≤ 1 + Real.log (n : ℝ) := by
                  gcongr
                  have : 2 * K ≤ n := by omega
                  exact_mod_cast this
        calc ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ)))
            ≤ ∑ r ∈ Finset.Icc 1 K, ((1 / ((2 * r - 1 : ℕ) : ℝ)) + (1 / ((2 * r : ℕ) : ℝ))) :=
              Finset.sum_le_sum hbound_k
          _ = (harmonic (2 * K) : ℝ) := hpair
          _ ≤ 1 + Real.log (n : ℝ) := hle_harm
      calc |∑ r ∈ Finset.Icc 1 K, ((Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))|
          ≤ ∑ r ∈ Finset.Icc 1 K,
              |(Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
                ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ Finset.Icc 1 K,
              C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
                Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := Finset.sum_le_sum hterm_err
        _ = C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) *
              ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
        _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) * (1 + Real.log (n : ℝ)) := by
              gcongr
        _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) *
              Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
              gcongr; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
        _ = C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ 2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
              have : 0 ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by positivity
              linarith
    -- Tail of alternating harmonic sum
    have halt_tail :
        |∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) - Real.log 2 * n| ≤
          2 * Real.sqrt n := by
      have hfactor :
          ∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) - Real.log 2 * n =
            -(n : ℝ) * (Real.log 2 - ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) := by
        rw [Finset.mul_sum]
        ring_nf
        simp only [sub_left_inj]
        refine Finset.sum_congr rfl fun r _ => by ring
      rw [hfactor, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
      have htb := alternating_harmonic_tail_bound K
      rw [abs_of_nonneg htb.1]
      calc (n : ℝ) * (Real.log 2 - ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))))
          ≤ (n : ℝ) * (1 / (2 * (K : ℝ) + 1)) := by gcongr; exact htb.2
        _ ≤ (n : ℝ) * (1 / ((1 / 2 : ℝ) * Real.sqrt n)) := by gcongr; positivity
        _ = 2 * Real.sqrt n := by
            have hsn0 : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast (by omega : 0 < n))
            rw [mul_one_div, div_eq_iff (by positivity)]
            nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg n)]
    have hsqrt_le_exp := hsqrt_exp_bound n hn16 hsq
    calc |Real.log (qn n) - Real.log 2 * n|
        = |(∑ r ∈ Finset.Icc 1 K, ((Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))) +
            (∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) - Real.log 2 * n) +
            (∑ p ∈ Tail, Real.log (p : ℝ))| := by
            rw [hlog_split]; ring_nf
      _ ≤ |∑ r ∈ Finset.Icc 1 K, ((Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))| +
            |∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) - Real.log 2 * n| +
            |∑ p ∈ Tail, Real.log (p : ℝ)| := by
            exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ 2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) +
            2 * Real.sqrt n + 2 * Real.log 4 * Real.sqrt n := by gcongr
      _ ≤ 2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) +
            2 * ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) +
            2 * Real.log 4 * ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) := by
            gcongr; positivity
      _ ≤ (4 * C₁ + 2 * Real.log 4 + 6) * ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) := by
            have hnn : 0 ≤ (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by positivity
            linarith
  -- Part 2: Podd.card / π(n) → log 2
  refine ⟨hpart1, ?_⟩
  have hlog_sq_sqrt : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    have ho : (fun x : ℝ => Real.log x ^ (1 : ℝ)) =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop 1 (by norm_num)
    have ht : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
      refine ho.tendsto_div_nhds_zero.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      simp [Real.rpow_one, Real.sqrt_eq_rpow]
    exact ht.comp h_inf
  have hlog_exp_zero : ∀ c : ℝ, 0 < c →
      Tendsto (fun n : ℕ => Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) atTop (𝓝 0) := by
    intro c hc
    have hexp2 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have hcomp := (hexp2.const_mul (1 / c ^ 2)).comp (h_sqrt_log.const_mul_atTop hc)
    rw [mul_zero] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [h_log.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    simp only [Function.comp_apply]
    have hcne : c ≠ 0 := hc.ne'
    rw [mul_pow, Real.sq_sqrt hn]
    field_simp [hcne]
    ring_nf
  have h_pi_asymp : Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 1) := by
    have hli_o : (fun n : ℕ => (∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) - (n : ℝ) / Real.log (n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 2) :=
      li_sub_div_log_isBigO.comp_tendsto h_inf
    obtain ⟨C₂, hC₂pos, hC₂w⟩ := hli_o.exists_pos
    have hli_div : Tendsto (fun n : ℕ =>
        ((∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) - (n : ℝ) / Real.log (n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
      have hlog_inv : Tendsto (fun n : ℕ => C₂ * (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp h_log).const_mul C₂
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlog_inv.neg hlog_inv ?_ ?_ <;>
        filter_upwards [hC₂w.bound, hev_setup] with n hn ⟨hn16, _, _, _⟩
      all_goals
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have hnorm : ‖(n : ℝ) / (Real.log (n : ℝ)) ^ 2‖ = (n : ℝ) / (Real.log (n : ℝ)) ^ 2 :=
          Real.norm_of_nonneg (by positivity)
        rw [Real.norm_eq_abs, hnorm] at hn
        have hdiv_bound :
            |((∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) - (n : ℝ) / Real.log (n : ℝ)) /
                ((n : ℝ) / Real.log (n : ℝ))| ≤ C₂ * (Real.log (n : ℝ))⁻¹ := by
          rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) / Real.log (n : ℝ))]
          calc |(∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) - (n : ℝ) / Real.log (n : ℝ)| /
                ((n : ℝ) / Real.log (n : ℝ))
              ≤ (C₂ * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) / ((n : ℝ) / Real.log (n : ℝ)) := by gcongr
            _ = C₂ * (Real.log (n : ℝ))⁻¹ := by field_simp [hn_pos.ne', hlog_pos.ne']
      · exact (abs_le.mp hdiv_bound).1
      · exact (abs_le.mp hdiv_bound).2
    have hpnt_div : Tendsto (fun n : ℕ =>
        ((Nat.primeCounting n : ℝ) - ∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
      have hbd : Tendsto (fun n : ℕ => C₁ * (Real.log (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ))))) atTop (𝓝 0) := by
        simpa using (hlog_exp_zero c₁ hc₁).const_mul C₁
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbd.neg hbd ?_ ?_ <;>
        filter_upwards [hev_setup] with n ⟨hn16, _, _, _⟩
      all_goals
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have h2le : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
        have hp2 := (hpnt (n : ℝ) h2le).2
        rw [Nat.floor_natCast] at hp2
        have hdiv_bd :
            |((Nat.primeCounting n : ℝ) - ∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) /
                ((n : ℝ) / Real.log (n : ℝ))| ≤
              C₁ * (Real.log (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ)))) := by
          rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) / Real.log (n : ℝ))]
          calc |(Nat.primeCounting n : ℝ) - ∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹| /
                ((n : ℝ) / Real.log (n : ℝ))
              ≤ (C₁ * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ)))) / ((n : ℝ) / Real.log (n : ℝ)) := by gcongr
            _ = C₁ * (Real.log (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ)))) := by
                field_simp [hn_pos.ne', hlog_pos.ne']
      · exact (abs_le.mp hdiv_bd).1
      · exact (abs_le.mp hdiv_bd).2
    have hsum := (hpnt_div.add hli_div).add tendsto_const_nhds (b := (1 : ℝ))
    simp only [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [hev_setup] with n ⟨hn16, _, _, _⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hden : ((n : ℝ) / Real.log (n : ℝ)) ≠ 0 := by positivity
    field_simp [hden]
    ring
  -- Now prove (Podd n).card / (n / log n) → log 2
  have h_podd_asymp : Tendsto (fun n : ℕ => ((Podd n).card : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (Real.log 2)) := by
    have hev_card : ∀ᶠ n : ℕ in atTop,
        16 ≤ n ∧ (c₁ / 2 + 4) ≤ Real.sqrt (Real.log (n : ℝ)) ∧
        (1 + Real.log 2 + Real.log (n : ℝ)) ≤ Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) ∧
        (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ∧
        1 ≤ ⌊Real.log (n : ℝ)⌋₊ ∧ ⌊Real.log (n : ℝ)⌋₊ ≤ (Nat.sqrt n - 1) / 2 ∧
        (4 : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) ∧
        Real.log (2 * Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      have hlog_lt_sqrt : ∀ᶠ n : ℕ in atTop, (4 : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        filter_upwards [hlog_sq_sqrt.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
          eventually_ge_atTop 2] with n hn hn2
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
        have h1 : Real.log (n : ℝ) / Real.sqrt (n : ℝ) ≤ 1 / 4 := hn
        have h2 := (div_le_iff₀ hsn).mp h1
        linarith
      have hlog2log : ∀ᶠ n : ℕ in atTop, Real.log (2 * Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
        have ht : Tendsto (fun x : ℝ => Real.log (2 * x) / x) atTop (𝓝 0) := by
          have ho : (fun y : ℝ => Real.log y ^ (1 : ℝ)) =o[atTop] (fun y : ℝ => y ^ (1 : ℝ)) :=
            isLittleO_log_rpow_rpow_atTop 1 one_pos
          have ht2 := (ho.tendsto_div_nhds_zero.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul 2
          rw [mul_zero] at ht2
          refine ht2.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          simp [Real.rpow_one]
          field_simp [hx.ne']
        filter_upwards [(ht.comp h_log).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
          h_log.eventually (eventually_gt_atTop 1)] with n hn hln
        exact (div_le_iff₀ (by linarith)).mp hn |>.trans_eq (by ring)
      filter_upwards [hev_setup, hlog_lt_sqrt, hlog2log, eventually_ge_atTop 100] with n
        ⟨hn16, hsq, hlexp, hlsq⟩ h4l h2l hn100
      have hlog_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ) := by
        have h1 : Real.log (n : ℝ) ≥ Real.log (100 : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn100)
        have h2 : Real.exp 2 < 100 := by
          have : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
          calc Real.exp 2 = Real.exp (1 + 1) := by ring_nf
            _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
            _ < 3 * 3 := mul_lt_mul' this.le this (by positivity) (by norm_num)
            _ < 100 := by norm_num
        have h3 : 2 < Real.log (100 : ℝ) := (Real.lt_log_iff_exp_lt (by norm_num)).mpr h2
        linarith
      have hfl1 : 1 ≤ ⌊Real.log (n : ℝ)⌋₊ := Nat.one_le_floor_iff.mpr (by linarith)
      have hflK : ⌊Real.log (n : ℝ)⌋₊ ≤ (Nat.sqrt n - 1) / 2 := by
        have h1 : (⌊Real.log (n : ℝ)⌋₊ : ℝ) ≤ Real.log (n : ℝ) := Nat.floor_le (by linarith)
        have h2 : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
          have : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
          exact Real.sqrt_lt' (by positivity) |>.mpr this
        have h3 : (2 * ⌊Real.log (n : ℝ)⌋₊ + 2 : ℝ) ≤ Nat.sqrt n := by linarith
        have h3' : 2 * ⌊Real.log (n : ℝ)⌋₊ + 2 ≤ Nat.sqrt n := by exact_mod_cast h3
        omega
      exact ⟨hn16, hsq, hlexp, hlsq, hfl1, hflK, h4l, h2l⟩
    -- Define the exact integral main term and show difference from Podd.card/(n/log n) -> 0
    let M : ℕ → ℝ := fun n =>
      let K : ℕ := (Nat.sqrt n - 1) / 2
      ∑ r ∈ Finset.Icc 1 K, ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹
    have hdiff_zero : Tendsto (fun n : ℕ =>
        (((Podd n).card : ℝ) - M n) / ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 0) := by
      have hbd : Tendsto (fun n : ℕ =>
          2 * C₁ * (Real.log (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) +
          2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
        have h1 := (hlog_exp_zero (c₁ / 4) (by positivity)).const_mul (2 * C₁)
        have h2 := hlog_sq_sqrt.const_mul 2
        simpa using h1.add h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbd.neg hbd ?_ ?_ <;>
        filter_upwards [hev_card] with n ⟨hn16, hsq, hlexp, _, _, _, _, _⟩
      all_goals
        have hn4 : 4 ≤ n := by omega
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        set K : ℕ := (Nat.sqrt n - 1) / 2
        set L : Finset ℕ := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
        set Tail : Finset ℕ := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
        obtain ⟨hdisj, hunion, hdisj_rs⟩ := hpart_odd n hn4
        have hcard_split : ((Podd n).card : ℝ) =
            (∑ r ∈ Finset.Icc 1 K,
              ((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ))) +
            (Tail.card : ℝ) := by
          rw [← hunion, Finset.card_union_of_disjoint hdisj,
            Finset.card_biUnion (fun r hr s hs hrs => hdisj_rs r hr s hs hrs),
            Nat.cast_add, Nat.cast_sum]
          congr 1
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.mem_Icc] at hr
          have hr1 : 1 ≤ 2 * r - 1 := by omega
          have hcard_r := card_harmonicLayer (n := n) (j := 2 * r - 1) hr1
          have hsub_nat : Nat.primeCounting ⌊(n : ℝ) / ((2 * r - 1 : ℕ) : ℝ) + 1⌋₊ ≤
              Nat.primeCounting ⌊(n : ℝ) / ((2 * r - 1 : ℕ) : ℝ)⌋₊ := by
            gcongr
            apply Nat.floor_mono
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) (by linarith)
          have hle_div : (n : ℝ) / (((2 * r - 1 : ℕ) : ℝ) + 1) ≤ (n : ℝ) / ((2 * r - 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) (by linarith)
          have hmono : Nat.primeCounting ⌊(n : ℝ) / (((2 * r - 1 : ℕ) : ℝ) + 1)⌋₊ ≤
              Nat.primeCounting ⌊(n : ℝ) / ((2 * r - 1 : ℕ) : ℝ)⌋₊ :=
            Nat.monotone_primeCounting (Nat.floor_mono hle_div)
          rw [hcard_r, Nat.cast_sub hmono]
          push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
          ring_nf
        have hTail_card : (Tail.card : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
          have h2K1_ge : (1 / 2 : ℝ) * Real.sqrt n ≤ (2 * (K : ℝ) + 1) := by
            have hsqrt_ge4 : (4 : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast hn16)
            have h_lt : Real.sqrt n - 1 < (Nat.sqrt n : ℝ) := by
              have : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
              have : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := Real.sqrt_lt' (by positivity) |>.mpr this
              linarith
            have hK_nat : Nat.sqrt n - 2 ≤ 2 * K := by omega
            have hK_real : (Nat.sqrt n : ℝ) - 1 ≤ 2 * (K : ℝ) + 1 := by
              have : ((Nat.sqrt n - 2 : ℕ) : ℝ) ≤ (2 * K : ℕ) := by exact_mod_cast hK_nat
              have hns2 : 2 ≤ Nat.sqrt n := (Nat.le_sqrt).mpr (by omega)
              rw [Nat.cast_sub hns2] at this
              push_cast at this
              linarith
            linarith
          have hsub_tail : Tail ⊆ Finset.Icc 1 (n / (2 * K + 1)) := by
            intro p hp
            have h1 := (Finset.mem_filter.mp hp).1
            have h2 := (Finset.mem_filter.mp hp).2
            have hp_prime := (Finset.mem_filter.mp h1).2.1
            exact Finset.mem_Icc.mpr ⟨hp_prime.pos, h2⟩
          have hcard_le : Tail.card ≤ n / (2 * K + 1) := by
            simpa [Nat.card_Icc] using Finset.card_le_card hsub_tail
          calc (Tail.card : ℝ) ≤ ((n / (2 * K + 1) : ℕ) : ℝ) := by exact_mod_cast hcard_le
            _ ≤ (n : ℝ) / ((2 * K + 1 : ℕ) : ℝ) := by
                rw [le_div_iff₀ (by positivity)]; exact_mod_cast Nat.div_mul_le_self n (2 * K + 1)
            _ ≤ (n : ℝ) / ((1 / 2 : ℝ) * Real.sqrt n) := by
                push_cast; gcongr; positivity
            _ = 2 * Real.sqrt (n : ℝ) := by
                have hsn0 : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hn_pos
                rw [div_eq_iff (by positivity)]
                nlinarith [Real.mul_self_sqrt hn_pos.le]
        have hli_err :
            |∑ r ∈ Finset.Icc 1 K,
                (((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                    (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ)) -
                  ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹)| ≤
              2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
          have hterm : ∀ r ∈ Finset.Icc 1 K,
              |((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                  (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ)) -
                ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹| ≤
                C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
                  Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
            intro r hr
            rw [Finset.mem_Icc] at hr
            have hj1 : 2 * r - 1 ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hj2 : 2 * r ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            obtain ⟨h2_1, hsq_1, _⟩ := hlayer_log_bound n hn16 hsq (2 * r - 1) hj1
            obtain ⟨h2_2, hsq_2, _⟩ := hlayer_log_bound n hn16 hsq (2 * r) hj2
            have hcast1 : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega)]; push_cast; ring
            have hcast2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
            rw [hcast1] at h2_1 hsq_1
            rw [hcast2] at h2_2 hsq_2
            have hp1 := (hpnt _ h2_1).2
            have hp2 := (hpnt _ h2_2).2
            have hint1 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 2 ((n : ℝ) / (2 * (r : ℝ) - 1)) := by
              refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
              rw [Set.uIcc_of_le h2_1] at ht
              have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
              fun_prop (disch := exact hl)
            have hint2 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 2 ((n : ℝ) / (2 * (r : ℝ))) := by
              refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
              rw [Set.uIcc_of_le h2_2] at ht
              have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
              fun_prop (disch := exact hl)
            have hint3 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume
                ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) := by
              refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
              have hle : (n : ℝ) / (2 * (r : ℝ)) ≤ (n : ℝ) / (2 * (r : ℝ) - 1) :=
                div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith)
              rw [Set.uIcc_of_le hle] at ht
              have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
              fun_prop (disch := exact hl)
            have hadj := intervalIntegral.integral_add_adjacent_intervals hint2 hint3
            have heq_int : ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ =
                (∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹) -
                (∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ))), (Real.log t)⁻¹) := by linarith
            rw [heq_int]
            have hexp1 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1)))) ≤
                Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
              apply Real.exp_le_exp.mpr; nlinarith
            have hexp2 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ))))) ≤
                Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
              apply Real.exp_le_exp.mpr; nlinarith
            calc |((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                    (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ)) -
                  ((∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹) -
                    (∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ))), (Real.log t)⁻¹))|
                = |((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                      ∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹) -
                    ((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ) -
                      ∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ))), (Real.log t)⁻¹)| := by ring_nf
              _ ≤ |(Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                      ∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹| +
                    |(Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ) -
                      ∫ t in (2 : ℝ)..((n : ℝ) / (2 * (r : ℝ))), (Real.log t)⁻¹| := abs_sub _ _
              _ ≤ C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) +
                    C₁ * ((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
                    calc _ ≤ C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1)))) +
                            C₁ * ((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ))))) := add_le_add hp1 hp2
                      _ ≤ _ := by gcongr
              _ = C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
                    Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by ring
          have hharm_sum :
              ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) ≤
                1 + Real.log (n : ℝ) := by
            have hbound_k : ∀ r ∈ Finset.Icc 1 K,
                (1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ)) ≤
                  (1 / ((2 * r - 1 : ℕ) : ℝ)) + (1 / ((2 * r : ℕ) : ℝ)) := by
              intro r hr; rw [Finset.mem_Icc] at hr
              have hc1 : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
              have hc2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
              rw [hc1, hc2]
            have hpair :
                ∑ r ∈ Finset.Icc 1 K, ((1 / ((2 * r - 1 : ℕ) : ℝ)) + (1 / ((2 * r : ℕ) : ℝ))) =
                  (harmonic (2 * K) : ℝ) := by
              rw [harmonic_eq_sum_Icc, Rat.cast_sum]
              induction K with
              | zero => simp
              | succ K ih =>
                rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.mul_succ,
                  Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
                simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
                rw [show 2 * (K + 1) - 1 = 2 * K + 1 by omega]
                push_cast
                ring
            have hle_harm : (harmonic (2 * K) : ℝ) ≤ 1 + Real.log (n : ℝ) := by
              rcases eq_or_ne K 0 with rfl | hK0
              · simp; exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
              · calc (harmonic (2 * K) : ℝ) ≤ 1 + Real.log (2 * K : ℕ) := harmonic_le_one_add_log (2 * K)
                  _ ≤ 1 + Real.log (n : ℝ) := by gcongr; exact_mod_cast (by omega : 2 * K ≤ n)
            exact (Finset.sum_le_sum hbound_k).trans (hpair ▸ hle_harm)
          calc |∑ r ∈ Finset.Icc 1 K,
                  (((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                      (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ)) -
                    ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹)|
              ≤ ∑ r ∈ Finset.Icc 1 K,
                  |((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                      (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ)) -
                    ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ Finset.Icc 1 K,
                  C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
                    Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := Finset.sum_le_sum hterm
            _ = C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) *
                  ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) := by
                  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
            _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) * (1 + Real.log (n : ℝ)) := by
                  gcongr
            _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) *
                  Real.exp ((c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
                  gcongr; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
            _ ≤ 2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by
                  rw [mul_assoc, ← Real.exp_add]
                  have : 0 ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) := by positivity
                  ring_nf at *; linarith
        have htot :
            |(((Podd n).card : ℝ) - M n) / ((n : ℝ) / Real.log (n : ℝ))| ≤
              2 * C₁ * (Real.log (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) +
              2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) := by
          rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) / Real.log (n : ℝ))]
          have hsub_eq : ((Podd n).card : ℝ) - M n =
              (∑ r ∈ Finset.Icc 1 K,
                (((Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ : ℝ) -
                    (Nat.primeCounting ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ : ℝ)) -
                  ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹)) +
              (Tail.card : ℝ) := by
            simp only [M, K]
            rw [hcard_split, Finset.sum_sub_distrib]
            ring
          calc |((Podd n).card : ℝ) - M n| / ((n : ℝ) / Real.log (n : ℝ))
              ≤ (2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) +
                  2 * Real.sqrt (n : ℝ)) / ((n : ℝ) / Real.log (n : ℝ)) := by
                gcongr
                rw [hsub_eq]
                calc |_ + (Tail.card : ℝ)| ≤ |_| + |(Tail.card : ℝ)| := abs_add_le _ _
                  _ ≤ 2 * C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ))) +
                        2 * Real.sqrt (n : ℝ) := by
                        rw [abs_of_nonneg (Nat.cast_nonneg _)]
                        exact add_le_add hli_err hTail_card
            _ = 2 * C₁ * (Real.log (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) +
                  2 * (Real.log (n : ℝ) * Real.sqrt (n : ℝ) / (n : ℝ)) := by
                  field_simp [hn_pos.ne', hlog_pos.ne']
            _ = 2 * C₁ * (Real.log (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log (n : ℝ)))) +
                  2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) := by
                  have hsn0 : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hn_pos
                  congr 2
                  rw [div_eq_div_iff hn_pos.ne' hsn0]
                  nlinarith [Real.mul_self_sqrt hn_pos.le]
      · exact (abs_le.mp htot).1
      · exact (abs_le.mp htot).2
    have hM_asymp : Tendsto (fun n : ℕ => M n / ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 (Real.log 2)) := by
      let lb : ℕ → ℝ := fun n =>
        Real.log 2 - 1 / (2 * (((Nat.sqrt n - 1) / 2 : ℕ) : ℝ) + 1)
      let ub : ℕ → ℝ := fun n =>
        let R₀ : ℕ := ⌊Real.log (n : ℝ)⌋₊
        (Real.log (n : ℝ) / (Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)))) * Real.log 2 +
          2 / (2 * (R₀ : ℝ) + 1)
      have hlb_lim : Tendsto lb atTop (𝓝 (Real.log 2)) := by
        have hK_inf : Tendsto (fun n : ℕ => 2 * (((Nat.sqrt n - 1) / 2 : ℕ) : ℝ) + 1) atTop atTop := by
          have hs : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop := by
            refine tendsto_atTop_atTop.mpr fun B => ⟨(Nat.ceil (max B 0)) ^ 2, fun n hn => ?_⟩
            have := Nat.le_sqrt.mpr hn
            exact (le_trans (le_max_left _ _) (Nat.le_ceil _)).trans (by exact_mod_cast this)
          refine tendsto_atTop_atTop.mpr fun B => ?_
          filter_upwards [hs.eventually (eventually_ge_atTop (B + 4))] with n hn
          have h1 : B + 4 ≤ (Nat.sqrt n : ℝ) := hn
          have h2 : (Nat.sqrt n : ℝ) - 2 ≤ 2 * (((Nat.sqrt n - 1) / 2 : ℕ) : ℝ) + 1 := by
            have hnat : Nat.sqrt n - 2 ≤ 2 * ((Nat.sqrt n - 1) / 2) := by omega
            have : ((Nat.sqrt n - 2 : ℕ) : ℝ) ≤ (2 * ((Nat.sqrt n - 1) / 2) : ℕ) := by exact_mod_cast hnat
            have : (Nat.sqrt n : ℝ) - 2 ≤ ((Nat.sqrt n - 2 : ℕ) : ℝ) := by
              by_cases h2 : 2 ≤ Nat.sqrt n
              · rw [Nat.cast_sub h2]; norm_num
              · have : Nat.sqrt n ≤ 1 := by omega
                have hcast : (Nat.sqrt n : ℝ) ≤ 1 := by exact_mod_cast this
                linarith [Nat.cast_nonneg (Nat.sqrt n - 2)]
            push_cast at *
            linarith
          linarith
        simpa using (tendsto_const_nhds (x := Real.log 2)).sub (tendsto_inv_atTop_zero.comp hK_inf)
      have hub_lim : Tendsto ub atTop (𝓝 (Real.log 2)) := by
        have hratio : Tendsto (fun n : ℕ =>
            Real.log (n : ℝ) / (Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)))) atTop (𝓝 1) := by
          have hsub : Tendsto (fun n : ℕ =>
              Real.log (2 * Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0) := by
            have ho : (fun y : ℝ => Real.log y ^ (1 : ℝ)) =o[atTop] (fun y : ℝ => y ^ (1 : ℝ)) :=
              isLittleO_log_rpow_rpow_atTop 1 one_pos
            have ht2 := (ho.tendsto_div_nhds_zero.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul 2
            rw [mul_zero] at ht2
            refine (ht2.comp h_log).congr' ?_
            filter_upwards [h_log.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
            simp [Real.rpow_one]
            field_simp [hn.ne']
          have hden : Tendsto (fun n : ℕ => 1 - Real.log (2 * Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 (1 - 0)) :=
            tendsto_const_nhds.sub hsub
          rw [sub_zero] at hden
          refine (hden.inv₀ one_ne_zero).congr' ?_
          filter_upwards [h_log.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
          field_simp [hn.ne']
        have hR0_inf : Tendsto (fun n : ℕ => 2 * (⌊Real.log (n : ℝ)⌋₊ : ℝ) + 1) atTop atTop := by
          refine tendsto_atTop_atTop.mpr fun B => ?_
          filter_upwards [h_log.eventually (eventually_ge_atTop (B + 2))] with n hn
          have := Nat.lt_floor_add_one (Real.log (n : ℝ))
          linarith
        have htail0 : Tendsto (fun n : ℕ => 2 / (2 * (⌊Real.log (n : ℝ)⌋₊ : ℝ) + 1)) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hR0_inf).const_mul 2
        simpa using ((hratio.mul_const (Real.log 2)).add htail0)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlb_lim hub_lim ?_ ?_ <;>
        filter_upwards [hev_card] with n ⟨hn16, hsq, _, _, hfl1, hflK, _, h2l⟩
      all_goals
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        set K : ℕ := (Nat.sqrt n - 1) / 2
        set R₀ : ℕ := ⌊Real.log (n : ℝ)⌋₊
        have hK_ge1 : 1 ≤ K := by omega
      · -- Lower bound: M n / (n / log n) ≥ lb n
        have hterm_lb : ∀ r ∈ Finset.Icc 1 K,
            (n : ℝ) / Real.log (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) ≤
              ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ := by
          intro r hr
          rw [Finset.mem_Icc] at hr
          have hj2 : 2 * r ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          obtain ⟨h2_2, _, _⟩ := hlayer_log_bound n hn16 hsq (2 * r) hj2
          have hcast2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
          rw [hcast2] at h2_2
          have hle_ab : (n : ℝ) / (2 * (r : ℝ)) ≤ (n : ℝ) / (2 * (r : ℝ) - 1) :=
            div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith)
          have hupper : (n : ℝ) / (2 * (r : ℝ) - 1) ≤ (n : ℝ) := by
            apply div_le_self hn_pos.le
            have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
            linarith
          have hint_lb : IntervalIntegrable (fun _ : ℝ => (Real.log (n : ℝ))⁻¹) MeasureTheory.volume
              ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) :=
            intervalIntegrable_const
          have hint_log : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume
              ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) := by
            refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
            rw [Set.uIcc_of_le hle_ab] at ht
            have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
            fun_prop (disch := exact hl)
          have hmono := intervalIntegral.integral_mono_on hle_ab hint_lb hint_log fun t ht => by
            have htpos : 0 < t := by linarith [ht.1]
            have hlt : Real.log t ≤ Real.log (n : ℝ) := Real.log_le_log htpos (ht.2.trans hupper)
            have hlt_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
            exact inv_anti₀ hlt_pos hlt
          rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
          calc (n : ℝ) / Real.log (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))
              = ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) * (Real.log (n : ℝ))⁻¹ := by ring
            _ ≤ ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ := hmono
        have hsum_lb := Finset.sum_le_sum hterm_lb
        rw [← Finset.mul_sum] at hsum_lb
        have htb := alternating_harmonic_tail_bound K
        have h1 : (n : ℝ) / Real.log (n : ℝ) * lb n ≤ M n := by
          calc (n : ℝ) / Real.log (n : ℝ) * lb n
              ≤ (n : ℝ) / Real.log (n : ℝ) *
                  ∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) := by
                gcongr; dsimp [lb]; linarith [htb.2]
            _ ≤ M n := hsum_lb
        exact (le_div_iff₀ (by positivity : 0 < (n : ℝ) / Real.log (n : ℝ))).mpr (by linarith)
      · -- Upper bound: M n / (n / log n) ≤ ub n
        have hsplit_Icc : Finset.Icc 1 K = Finset.Icc 1 R₀ ∪ Finset.Icc (R₀ + 1) K := by
          ext r; simp only [Finset.mem_union, Finset.mem_Icc]; omega
        have hdisj_Icc : Disjoint (Finset.Icc 1 R₀) (Finset.Icc (R₀ + 1) K) := by
          rw [Finset.disjoint_left]; intro r h1 h2
          simp only [Finset.mem_Icc] at h1 h2; omega
        have hlog_sub_pos : 0 < Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)) := by linarith
        have hsum1 : ∑ r ∈ Finset.Icc 1 R₀,
              ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ ≤
            ((n : ℝ) / (Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)))) * Real.log 2 := by
          have hterm1 : ∀ r ∈ Finset.Icc 1 R₀,
              ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ ≤
                (n : ℝ) / (Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ))) *
                  (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) := by
            intro r hr
            rw [Finset.mem_Icc] at hr
            have hj2 : 2 * r ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            obtain ⟨h2_2, _, _⟩ := hlayer_log_bound n hn16 hsq (2 * r) hj2
            have hcast2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
            rw [hcast2] at h2_2
            have hle_ab : (n : ℝ) / (2 * (r : ℝ)) ≤ (n : ℝ) / (2 * (r : ℝ) - 1) :=
              div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith)
            have hR0_le : (R₀ : ℝ) ≤ Real.log (n : ℝ) := Nat.floor_le hlog_pos.le
            have hr_le : (r : ℝ) ≤ Real.log (n : ℝ) := (by exact_mod_cast hr.2 : (r : ℝ) ≤ R₀).trans hR0_le
            have ht_min : (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ (n : ℝ) / (2 * (r : ℝ)) :=
              div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith)
            have hint_ub : IntervalIntegrable (fun _ : ℝ => (Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)))⁻¹)
                MeasureTheory.volume ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) :=
              intervalIntegrable_const
            have hint_log : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume
                ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) := by
              refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
              rw [Set.uIcc_of_le hle_ab] at ht
              have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
              fun_prop (disch := exact hl)
            have hmono := intervalIntegral.integral_mono_on hle_ab hint_log hint_ub fun t ht => by
              have ht_ge : (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ t := ht_min.trans ht.1
              have hl_ge : Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)) ≤ Real.log t := by
                rw [← Real.log_div hn_pos.ne' (by positivity)]
                exact Real.log_le_log (by positivity) ht_ge
              exact inv_anti₀ hlog_sub_pos hl_ge
            rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
            exact hmono.trans_eq (by ring)
          have hs := Finset.sum_le_sum hterm1
          rw [← Finset.mul_sum] at hs
          have htb := alternating_harmonic_tail_bound R₀
          exact hs.trans (by gcongr; linarith [htb.1])
        have hsum2 : ∑ r ∈ Finset.Icc (R₀ + 1) K,
              ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ ≤
            (n : ℝ) / Real.log (n : ℝ) * (2 / (2 * (R₀ : ℝ) + 1)) := by
          have hterm2 : ∀ r ∈ Finset.Icc (R₀ + 1) K,
              ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹ ≤
                2 * (n : ℝ) / Real.log (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) := by
            intro r hr
            rw [Finset.mem_Icc] at hr
            have hj2 : 2 * r ∈ Finset.Icc 1 (Nat.sqrt n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            obtain ⟨h2_2, _, hlog_half⟩ := hlayer_log_bound n hn16 hsq (2 * r) hj2
            have hcast2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
            rw [hcast2] at h2_2 hlog_half
            have hle_ab : (n : ℝ) / (2 * (r : ℝ)) ≤ (n : ℝ) / (2 * (r : ℝ) - 1) :=
              div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith)
            have hint_ub : IntervalIntegrable (fun _ : ℝ => 2 / Real.log (n : ℝ))
                MeasureTheory.volume ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) :=
              intervalIntegrable_const
            have hint_log : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume
                ((n : ℝ) / (2 * (r : ℝ))) ((n : ℝ) / (2 * (r : ℝ) - 1)) := by
              refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
              rw [Set.uIcc_of_le hle_ab] at ht
              have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
              fun_prop (disch := exact hl)
            have hmono := intervalIntegral.integral_mono_on hle_ab hint_log hint_ub fun t ht => by
              have hlt : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log t :=
                hlog_half.trans (Real.log_le_log (by linarith [h2_2]) ht.1)
              have hinv := inv_anti₀ (by positivity : 0 < (1 / 2 : ℝ) * Real.log (n : ℝ)) hlt
              exact hinv.trans_eq (by ring)
            rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
            exact hmono.trans_eq (by ring)
          have hs := Finset.sum_le_sum hterm2
          rw [← Finset.mul_sum] at hs
          have hsub_sum :
              ∑ r ∈ Finset.Icc (R₀ + 1) K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) ≤
                1 / (2 * (R₀ : ℝ) + 1) := by
            have htot := Finset.sum_union hdisj_Icc
            have hs_eq :
                (∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) -
                  (∑ r ∈ Finset.Icc 1 R₀, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) =
                  ∑ r ∈ Finset.Icc (R₀ + 1) K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) := by
              rw [hsplit_Icc, Finset.sum_union hdisj_Icc]; ring
            have htbK := alternating_harmonic_tail_bound K
            have htbR := alternating_harmonic_tail_bound R₀
            linarith [htbK.1, htbR.2]
          calc _ ≤ 2 * (n : ℝ) / Real.log (n : ℝ) *
                  ∑ r ∈ Finset.Icc (R₀ + 1) K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) := hs
            _ ≤ 2 * (n : ℝ) / Real.log (n : ℝ) * (1 / (2 * (R₀ : ℝ) + 1)) := by gcongr
            _ = (n : ℝ) / Real.log (n : ℝ) * (2 / (2 * (R₀ : ℝ) + 1)) := by ring
        have hM_le : M n ≤ (n : ℝ) / Real.log (n : ℝ) * ub n := by
          have hM_split : M n =
              (∑ r ∈ Finset.Icc 1 R₀,
                ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹) +
              (∑ r ∈ Finset.Icc (R₀ + 1) K,
                ∫ t in ((n : ℝ) / (2 * (r : ℝ)))..((n : ℝ) / (2 * (r : ℝ) - 1)), (Real.log t)⁻¹) := by
            simp only [M, K]; rw [hsplit_Icc, Finset.sum_union hdisj_Icc]
          rw [hM_split]
          calc _ ≤ ((n : ℝ) / (Real.log (n : ℝ) - Real.log (2 * Real.log (n : ℝ)))) * Real.log 2 +
                  (n : ℝ) / Real.log (n : ℝ) * (2 / (2 * (R₀ : ℝ) + 1)) := add_le_add hsum1 hsum2
            _ = (n : ℝ) / Real.log (n : ℝ) * ub n := by
                dsimp [ub]
                field_simp [hlog_pos.ne', hlog_sub_pos.ne']
        exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) / Real.log (n : ℝ))).mpr (by linarith)
    have hcomb := hdiff_zero.add hM_asymp
    rw [zero_add] at hcomb
    refine hcomb.congr' (Eventually.of_forall fun n => ?_)
    ring
  have hfinal := h_podd_asymp.div h_pi_asymp one_ne_zero
  rw [div_one] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [hev_setup, eventually_ge_atTop 2] with n ⟨hn16, _, _, _⟩ _
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hden : ((n : ℝ) / Real.log (n : ℝ)) ≠ 0 := by positivity
  rw [div_div_div_cancel_right₀ hden]

/-! ### 2.2 Exact Base-p Digit Reduction Below √n -/

/-- Sum of base-`p` digits `s_p(n)`. -/
def digitSum (p n : ℕ) : ℕ :=
  (Nat.digits p n).sum

/-- Sum of odd-indexed base-`p` digits `∑_{m ≥ 0} d^{(p)}_{2m+1}(n)`. -/
def oddIndexedDigitSum (p n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range ((Nat.digits p n).length / 2 + 1), (Nat.digits p n).getD (2 * m + 1) 0

/-- Digit-sum remainder `E_digit(n) := ∑_{3 ≤ p ≤ √n} (-1)^{v_p(n!)-1} s_p(n) log p / (p - 1)`. -/
def Edigit (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
    (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
      ((digitSum p n : ℝ) * Real.log p / ((p : ℝ) - 1))

private lemma oddIndexedDigitSum_add_even (L : List ℕ) :
    (∑ m ∈ Finset.range (L.length / 2 + 1), L.getD (2 * m + 1) 0) +
    (∑ m ∈ Finset.range (L.length / 2 + 1), L.getD (2 * m) 0) = L.sum := by
  induction L using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b L ih =>
    have hlen : (a :: b :: L).length / 2 + 1 = (L.length / 2 + 1) + 1 := by simp; omega
    have hodd : ∀ m, (a :: b :: L).getD (2 * (m + 1) + 1) 0 = L.getD (2 * m + 1) 0 := fun m => by
      simp [List.getD, show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
    have heven : ∀ m, (a :: b :: L).getD (2 * (m + 1)) 0 = L.getD (2 * m) 0 := fun m => by
      simp [List.getD, show 2 * (m + 1) = (2 * m) + 2 by omega]
    rw [hlen, Finset.sum_range_succ', Finset.sum_range_succ']
    simp_rw [hodd, heven]
    simp only [List.getD, List.getElem?_cons_zero, Option.getD_some,
      show 2 * 0 + 1 = 1 by rfl, mul_zero, List.getElem?_cons_succ, List.sum_cons]
    linarith

private lemma oddIndexedDigitSum_of_mod_p {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    (oddIndexedDigitSum p n + oddIndexedDigitSum p (n / p)) % 2 = (Nat.digits p (n / p)).sum % 2 := by
  have hn0 : n ≠ 0 := by have := hp.pos; omega
  have hdig : Nat.digits p n = (n % p) :: Nat.digits p (n / p) := Nat.digits_def' hp.one_lt (by omega)
  have hsum1 : oddIndexedDigitSum p n =
      ∑ m ∈ Finset.range ((Nat.digits p (n / p)).length / 2 + 1), (Nat.digits p (n / p)).getD (2 * m) 0 := by
    unfold oddIndexedDigitSum
    rw [hdig, List.length_cons]
    have hget : ∀ m, ((n % p) :: Nat.digits p (n / p)).getD (2 * m + 1) 0 = (Nat.digits p (n / p)).getD (2 * m) 0 :=
      fun m => by simp [List.getD]
    simp_rw [hget]
    rcases Nat.even_or_odd (Nat.digits p (n / p)).length with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hlen1 : (Nat.digits p (n / p)).length / 2 + 1 = k + 1 := by omega
      have hlen2 : ((Nat.digits p (n / p)).length + 1) / 2 + 1 = k + 1 := by omega
      rw [hlen1, hlen2]
    · have hlen1 : (Nat.digits p (n / p)).length / 2 + 1 = k + 1 := by omega
      have hlen2 : ((Nat.digits p (n / p)).length + 1) / 2 + 1 = k + 2 := by omega
      rw [hlen1, hlen2, Finset.sum_range_succ]
      have hout : (Nat.digits p (n / p)).getD (2 * (k + 1)) 0 = 0 := by
        simp [List.getD, List.getElem?_eq_none (by omega : (Nat.digits p (n / p)).length ≤ 2 * (k + 1))]
      rw [hout, add_zero]
  rw [hsum1, add_comm]
  unfold oddIndexedDigitSum
  rw [oddIndexedDigitSum_add_even]

theorem lemma_2_2_i (n p : ℕ) (_hn : 4 ≤ n) (hp : p.Prime) (hp3 : 3 ≤ p) :
    padicValNat p n.factorial % 2 = oddIndexedDigitSum p n % 2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with | _ n ih =>
  by_cases hlt : n < p
  · have hv0 : padicValNat p n.factorial = 0 := by
      have hnsq : n < p ^ 2 := hlt.trans (by nlinarith)
      rw [padicValNat_factorial_of_lt_sq hp hnsq, Nat.div_eq_of_lt hlt]
    have hdig0 : oddIndexedDigitSum p n = 0 := by
      unfold oddIndexedDigitSum
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hdig : Nat.digits p n = [n] := Nat.digits_of_lt p n hn0 hlt
        simp [hdig, List.getD]
    rw [hv0, hdig0]
  · have hpn : p ≤ n := not_lt.mp hlt
    have hndiv : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
    have hv_step : padicValNat p n.factorial = padicValNat p (n / p).factorial + n / p := by
      rw [← padicValNat_mul_div_factorial, padicValNat_factorial_mul]
    have hp2 : p % 2 = 1 := Nat.Prime.mod_two_eq_one_iff_ne_two.mpr (by omega)
    have hmodeq : n / p ≡ (Nat.digits p (n / p)).sum [MOD 2] :=
      Nat.modEq_digits_sum 2 p (by omega) (n / p)
    have hih := ih (n / p) hndiv
    have hrel := oddIndexedDigitSum_of_mod_p hp hpn
    have h1 : padicValNat p n.factorial % 2 = (oddIndexedDigitSum p (n / p) + (Nat.digits p (n / p)).sum) % 2 := by
      rw [hv_step, Nat.add_mod, hih, ← Nat.ModEq.eq hmodeq, ← Nat.add_mod]
    rw [h1, ← hrel]
    omega

theorem lemma_2_2_ii (n : ℕ) (hn : 4 ≤ n) :
    (∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
      (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p =
        -(n : ℝ) * SigmaParityStar n + Edigit n) ∧
    |Edigit n| ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n ∧
    IsBigOAtTop Edigit (fun m => Real.sqrt m) := by
  have hSigma : SigmaParityStar n =
      ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)) := by
    unfold SigmaParityStar SigmaParity
    congr 2 with p
    simp [Nat.floor_sqrt]
  have hid :
      ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p =
          -(n : ℝ) * SigmaParityStar n + Edigit n := by
    rw [hSigma, Finset.mul_sum]
    unfold Edigit
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    let _ : Fact p.Prime := ⟨hp.2⟩
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.one_lt
    have hp1_ne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hleg := sub_one_mul_padicValNat_factorial p n
    have hsd : digitSum p n ≤ n := Nat.digit_sum_le p n
    have hlegR : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = (n : ℝ) - (digitSum p n : ℝ) := by
      have hp_ge1 : 1 ≤ p := hp.2.one_le
      have : ((p - 1 : ℕ) : ℝ) * (padicValNat p n.factorial : ℝ) = ((n - digitSum p n : ℕ) : ℝ) := by
        exact_mod_cast hleg
      rwa [Nat.cast_sub hp_ge1, Nat.cast_sub hsd, Nat.cast_one] at this
    have hv_eq : (padicValNat p n.factorial : ℝ) = ((n : ℝ) - (digitSum p n : ℝ)) / ((p : ℝ) - 1) := by
      field_simp [hp1_ne]; linarith
    have hsign : (-1 : ℝ) ^ padicValNat p n.factorial =
        -((-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1)) := by
      have hz : (-1 : ℝ) ^ (padicValNat p n.factorial : ℤ) =
          (-1 : ℝ) ^ (((padicValNat p n.factorial : ℤ) - 1) + 1) := by ring_nf
      rw [← zpow_natCast (-1 : ℝ), hz, zpow_add₀ (by norm_num), zpow_one]
      ring
    rw [hv_eq, hsign]
    ring
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hterm_bound : ∀ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
      (digitSum p n : ℝ) * Real.log p / ((p : ℝ) - 1) ≤ 2 * Real.log n := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.one_lt
    have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
    have hdig_lt : ∀ d ∈ Nat.digits p n, d ≤ p - 1 := fun d hd =>
      Nat.le_pred_of_lt (Nat.digits_lt_base hp.2.one_lt hd)
    have hdig_sum : digitSum p n ≤ (Nat.digits p n).length * (p - 1) := by
      unfold digitSum
      calc (Nat.digits p n).sum ≤ ((Nat.digits p n).map (fun _ => p - 1)).sum :=
            List.sum_le_sum (fun d hd => hdig_lt d hd)
        _ = (Nat.digits p n).length * (p - 1) := by simp
    have hpow_len : p ^ (Nat.digits p n).length ≤ p * n :=
      Nat.base_pow_length_digits_le p n hp.2.one_lt (by omega)
    have hlog_len : ((Nat.digits p n).length : ℝ) * Real.log p ≤ Real.log p + Real.log n := by
      have h1 : Real.log ((p ^ (Nat.digits p n).length : ℕ) : ℝ) ≤ Real.log ((p * n : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpow_len)
      rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul (by positivity) (by positivity)] at h1
      exact h1
    have hpsq : (p : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : p * p ≤ n := (Nat.sqrt_le n).trans' (Nat.mul_le_mul hp.1.2 hp.1.2)
      exact_mod_cast (by simpa [sq] using this)
    have hlogp_half : Real.log p ≤ (1 / 2 : ℝ) * Real.log n := by
      have h1 : Real.log ((p : ℝ) ^ 2) ≤ Real.log n := Real.log_le_log (by positivity) hpsq
      rw [Real.log_pow] at h1
      linarith
    have hlogp_nonneg : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_le)
    calc (digitSum p n : ℝ) * Real.log p / ((p : ℝ) - 1)
        ≤ (((Nat.digits p n).length : ℝ) * ((p : ℝ) - 1)) * Real.log p / ((p : ℝ) - 1) := by
          gcongr
          have : ((digitSum p n : ℕ) : ℝ) ≤ (((Nat.digits p n).length * (p - 1) : ℕ) : ℝ) := by
            exact_mod_cast hdig_sum
          simpa [Nat.cast_sub hp.2.one_le] using this
      _ = ((Nat.digits p n).length : ℝ) * Real.log p := by field_simp [hp_sub_pos.ne']
      _ ≤ Real.log p + Real.log n := hlog_len
      _ ≤ (1 / 2 : ℝ) * Real.log n + Real.log n := by linarith
      _ ≤ 2 * Real.log n := by linarith
  have hpi_card : (((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime).card : ℝ) ≤
      (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc (by omega) le_rfl))
  have hed : |Edigit n| ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n := by
    unfold Edigit
    calc |∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
            ((digitSum p n : ℝ) * Real.log p / ((p : ℝ) - 1))|
        ≤ ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
            |(-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
              ((digitSum p n : ℝ) * Real.log p / ((p : ℝ) - 1))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
            (digitSum p n : ℝ) * Real.log p / ((p : ℝ) - 1) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
          rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul, abs_of_nonneg]
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) (sub_nonneg.mpr hp1.le)
      _ ≤ ∑ _p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime, 2 * Real.log n :=
          Finset.sum_le_sum hterm_bound
      _ = (((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime).card : ℝ) * (2 * Real.log n) := by
          simp [nsmul_eq_mul]
      _ ≤ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * Real.log n) := by gcongr
      _ = 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n := by ring
  exact ⟨hid, hed, ?_⟩
  -- Wait: let's prove `|Edigit m| ≤ 2 * π(√m) * log m` inline via a helper, or reuse a uniform bound
  have hed_all : ∀ m : ℕ, 4 ≤ m → |Edigit m| ≤ 2 * (Nat.primeCounting (Nat.sqrt m) : ℝ) * Real.log m := by
    intro m hm4
    have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hterm_m : ∀ p ∈ (Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime,
        (digitSum p m : ℝ) * Real.log p / ((p : ℝ) - 1) ≤ 2 * Real.log m := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.one_lt
      have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
      have hdig_lt : ∀ d ∈ Nat.digits p m, d ≤ p - 1 := fun d hd =>
        Nat.le_pred_of_lt (Nat.digits_lt_base hp.2.one_lt hd)
      have hdig_sum : digitSum p m ≤ (Nat.digits p m).length * (p - 1) := by
        unfold digitSum
        calc (Nat.digits p m).sum ≤ ((Nat.digits p m).map (fun _ => p - 1)).sum :=
              List.sum_le_sum (fun d hd => hdig_lt d hd)
          _ = (Nat.digits p m).length * (p - 1) := by simp
      have hpow_len : p ^ (Nat.digits p m).length ≤ p * m :=
        Nat.base_pow_length_digits_le p m hp.2.one_lt (by omega)
      have hlog_len : ((Nat.digits p m).length : ℝ) * Real.log p ≤ Real.log p + Real.log m := by
        have h1 : Real.log ((p ^ (Nat.digits p m).length : ℕ) : ℝ) ≤ Real.log ((p * m : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hpow_len)
        rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul (by positivity) (by positivity)] at h1
        exact h1
      have hpsq : (p : ℝ) ^ 2 ≤ (m : ℝ) := by
        have : p * p ≤ m := (Nat.sqrt_le m).trans' (Nat.mul_le_mul hp.1.2 hp.1.2)
        exact_mod_cast (by simpa [sq] using this)
      have hlogp_half : Real.log p ≤ (1 / 2 : ℝ) * Real.log m := by
        have h1 : Real.log ((p : ℝ) ^ 2) ≤ Real.log m := Real.log_le_log (by positivity) hpsq
        rw [Real.log_pow] at h1
        linarith
      have hlogp_nonneg : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_le)
      calc (digitSum p m : ℝ) * Real.log p / ((p : ℝ) - 1)
          ≤ (((Nat.digits p m).length : ℝ) * ((p : ℝ) - 1)) * Real.log p / ((p : ℝ) - 1) := by
            gcongr
            have : ((digitSum p m : ℕ) : ℝ) ≤ (((Nat.digits p m).length * (p - 1) : ℕ) : ℝ) := by
              exact_mod_cast hdig_sum
            simpa [Nat.cast_sub hp.2.one_le] using this
        _ = ((Nat.digits p m).length : ℝ) * Real.log p := by field_simp [hp_sub_pos.ne']
        _ ≤ Real.log p + Real.log m := hlog_len
        _ ≤ (1 / 2 : ℝ) * Real.log m + Real.log m := by linarith
        _ ≤ 2 * Real.log m := by linarith
    have hpi_m : (((Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime).card : ℝ) ≤
        (Nat.primeCounting (Nat.sqrt m) : ℝ) := by
      rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc (by omega) le_rfl))
    unfold Edigit
    calc |∑ p ∈ (Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p m.factorial : ℤ) - 1) *
            ((digitSum p m : ℝ) * Real.log p / ((p : ℝ) - 1))|
        ≤ ∑ p ∈ (Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime,
            |(-1 : ℝ) ^ ((padicValNat p m.factorial : ℤ) - 1) *
              ((digitSum p m : ℝ) * Real.log p / ((p : ℝ) - 1))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p ∈ (Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime,
            (digitSum p m : ℝ) * Real.log p / ((p : ℝ) - 1) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
          rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul, abs_of_nonneg]
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) (sub_nonneg.mpr hp1.le)
      _ ≤ ∑ _p ∈ (Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime, 2 * Real.log m :=
          Finset.sum_le_sum hterm_m
      _ = (((Finset.Icc 3 (Nat.sqrt m)).filter Nat.Prime).card : ℝ) * (2 * Real.log m) := by
          simp [nsmul_eq_mul]
      _ ≤ (Nat.primeCounting (Nat.sqrt m) : ℝ) * (2 * Real.log m) := by gcongr
      _ = 2 * (Nat.primeCounting (Nat.sqrt m) : ℝ) * Real.log m := by ring
  refine ⟨16 * Real.log 4 + 8, by positivity, 16, fun m hm => ?_⟩
  have hm_sqrt_gt1 : (1 : ℝ) < (Nat.sqrt m : ℝ) := by
    have : 4 ≤ Nat.sqrt m := (Nat.le_sqrt).mpr (by omega)
    exact_mod_cast (by omega : 1 < Nat.sqrt m)
  have hpi_cheb : (Nat.primeCounting (Nat.sqrt m) : ℝ) ≤
      Real.log 4 * (Nat.sqrt m : ℝ) / Real.log (Real.sqrt (Nat.sqrt m : ℝ)) + Real.sqrt (Nat.sqrt m : ℝ) := by
    simpa [Nat.floor_natCast] using Chebyshev.pi_le_log4_mul_div hm_sqrt_gt1
  have hsqrt_le : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le m
  have hm_half_sqrt : (1 / 2 : ℝ) * Real.sqrt m ≤ (Nat.sqrt m : ℝ) := by
    have hlt : Real.sqrt m - 1 < (Nat.sqrt m : ℝ) := by
      have : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' m
      have hsq : Real.sqrt m < (Nat.sqrt m : ℝ) + 1 :=
        Real.sqrt_lt' (by positivity) |>.mpr this
      linarith
    have h4 : (4 : ℝ) ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by exact_mod_cast hm)
    linarith
  have hlog_sqrt_sqrt : (1 / 8 : ℝ) * Real.log m ≤ Real.log (Real.sqrt (Nat.sqrt m : ℝ)) := by
    rw [Real.log_sqrt (by positivity)]
    have h1 : Real.log ((1 / 2 : ℝ) * Real.sqrt m) ≤ Real.log (Nat.sqrt m : ℝ) :=
      Real.log_le_log (by positivity) hm_half_sqrt
    have h2 : (1 / 2 : ℝ) * Real.log m = Real.log (Real.sqrt m) := (Real.log_sqrt (by positivity)).symm
    have hlog4 : Real.log 2 ≤ (1 / 4 : ℝ) * Real.log m := by
      have : (2 : ℝ) ^ 4 ≤ (m : ℝ) := by exact_mod_cast hm
      have hl := Real.log_le_log (by positivity) this
      rw [Real.log_pow] at hl
      linarith
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub] at h1
    linarith
  have hlog_ss_pos : 0 < Real.log (Real.sqrt (Nat.sqrt m : ℝ)) := by
    have : 0 < (1 / 8 : ℝ) * Real.log m := mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (by omega : 1 < m)))
    linarith
  have hss_le_sqrt : Real.sqrt (Nat.sqrt m : ℝ) * Real.log m ≤ 4 * Real.sqrt m := by
    have h14 : Real.sqrt (Nat.sqrt m : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by
      calc Real.sqrt (Nat.sqrt m : ℝ) ≤ Real.sqrt (Real.sqrt m) := Real.sqrt_le_sqrt hsqrt_le
        _ = (m : ℝ) ^ (1 / 4 : ℝ) := by
          simp [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]; norm_num
    have hlog_le : Real.log (m : ℝ) ≤ 4 * (m : ℝ) ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div (Nat.cast_nonneg m) (by norm_num : (0 : ℝ) < 1 / 4)
      linarith
    calc Real.sqrt (Nat.sqrt m : ℝ) * Real.log m
        ≤ (m : ℝ) ^ (1 / 4 : ℝ) * (4 * (m : ℝ) ^ (1 / 4 : ℝ)) := by
          gcongr; exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
      _ = 4 * ((m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = 4 * Real.sqrt m := by
          rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < m)), Real.sqrt_eq_rpow]; norm_num
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  calc |Edigit m|
      ≤ 2 * (Nat.primeCounting (Nat.sqrt m) : ℝ) * Real.log m := hed_all m (by omega)
    _ ≤ 2 * (Real.log 4 * (Nat.sqrt m : ℝ) / Real.log (Real.sqrt (Nat.sqrt m : ℝ)) +
          Real.sqrt (Nat.sqrt m : ℝ)) * Real.log m := by gcongr
    _ ≤ 2 * (Real.log 4 * Real.sqrt m / ((1 / 8 : ℝ) * Real.log m) + Real.sqrt (Nat.sqrt m : ℝ)) * Real.log m := by
        gcongr; positivity
    _ = 16 * Real.log 4 * Real.sqrt m + 2 * (Real.sqrt (Nat.sqrt m : ℝ) * Real.log m) := by
        field_simp [hlogm_pos.ne']
        ring
    _ ≤ 16 * Real.log 4 * Real.sqrt m + 2 * (4 * Real.sqrt m) := by gcongr
    _ = (16 * Real.log 4 + 8) * Real.sqrt m := by ring

/-! ### 2.3 Vaaler Approximation and Exponential Sum Bounds -/

private lemma ePhase_add (x y : ℝ) : ePhase (x + y) = ePhase x * ePhase y := by
  unfold ePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma ePhase_int (m : ℤ) : ePhase (m : ℝ) = 1 := by
  unfold ePhase
  rw [show (2 * Real.pi * Complex.I * (m : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

private lemma ePhase_half_int (h : ℤ) : ePhase (-(h : ℝ) / 2) = ((-1 : ℂ) ^ h) := by
  unfold ePhase
  rcases Int.even_or_odd h with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hev : h = 2 * k := by omega
    subst hev
    rw [show (-(2 * (k : ℝ)) / 2) = ((-k : ℤ) : ℝ) by push_cast; ring]
    have h1 : ePhase ((-k : ℤ) : ℝ) = 1 := ePhase_int (-k)
    unfold ePhase at h1
    rw [h1]
    simp [zpow_mul]
  · have hod : h = 2 * k + 1 := hk
    subst hod
    have hadd : (-(2 * (k : ℝ) + 1) / 2) = ((-k : ℤ) : ℝ) + (-1 / 2 : ℝ) := by push_cast; ring
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (((-k : ℤ) : ℂ) + (-1 / 2 : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ)) * Complex.exp (-Real.pi * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; ring
    push_cast
    rw [show (2 * Real.pi * Complex.I * (-(2 * (k : ℂ) + 1) / 2)) =
        2 * Real.pi * Complex.I * (((-k : ℤ) : ℂ) + (-1 / 2 : ℂ)) by ring, h1]
    have hk1 : Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ)) = 1 := by
      simpa [ePhase] using ePhase_int (-k)
    rw [hk1, one_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]

private lemma parity_floor_eq_sawtooth (x : ℝ) :
    (-1 : ℝ) ^ ⌊x⌋ =
      -2 * ((x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2) - ((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2)) := by
  set k : ℤ := ⌊x⌋
  have hkx : (k : ℝ) ≤ x ∧ x < (k : ℝ) + 1 := ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hkm : k = 2 * m := by omega
    have hf1 : ⌊x / 2⌋ = m := Int.floor_eq_iff.mpr ⟨by push_cast [← hkm]; linarith [hkx.1],
      by push_cast [← hkm]; linarith [hkx.2]⟩
    have hf2 : ⌊(x - 1) / 2⌋ = m - 1 := Int.floor_eq_iff.mpr ⟨by push_cast [← hkm]; linarith [hkx.1],
      by push_cast [← hkm]; linarith [hkx.2]⟩
    rw [hf1, hf2, hkm, zpow_mul, show (-1 : ℝ) ^ (2 : ℤ) = 1 by norm_num, one_zpow]
    push_cast
    ring
  · have hkm : k = 2 * m + 1 := hm
    have hf1 : ⌊x / 2⌋ = m := Int.floor_eq_iff.mpr ⟨by push_cast [← hkm]; linarith [hkx.1],
      by push_cast [← hkm]; linarith [hkx.2]⟩
    have hf2 : ⌊(x - 1) / 2⌋ = m := Int.floor_eq_iff.mpr ⟨by push_cast [← hkm]; linarith [hkx.1],
      by push_cast [← hkm]; linarith [hkx.2]⟩
    rw [hf1, hf2, hkm, zpow_add₀ (by norm_num), zpow_mul, show (-1 : ℝ) ^ (2 : ℤ) = 1 by norm_num,
      one_zpow, zpow_one]
    push_cast
    ring

theorem lemma_2_3 (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Ψtilde Btilde : ℝ → ℝ) (cTilde bTilde : ℤ → ℂ),
      (∀ x : ℝ, (Ψtilde x : ℂ) =
        ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
          cTilde h * ePhase ((h : ℝ) * x / 2)) ∧
      (∀ x : ℝ, (Btilde x : ℂ) =
        (bTilde 0) + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
          bTilde h * ePhase ((h : ℝ) * x / 2)) ∧
      (bTilde 0 = ((2 : ℂ) / ((H : ℂ) + 1))) ∧
      (∀ h : ℤ, h ≠ 0 → ‖cTilde h‖ ≤ 2 / (Real.pi * |(h : ℝ)|)) ∧
      (∀ h : ℤ, ‖bTilde h‖ < 3 / ((H : ℝ) + 1)) ∧
      (∀ x : ℝ, |(-1 : ℝ) ^ ⌊x⌋ - Ψtilde x| ≤ Btilde x) ∧
      (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
        ‖cTilde h‖ ≤ (4 / Real.pi) * (Real.log (2 * H + 1) + 1)) := by
  classical
  obtain ⟨W, _, _, hV⟩ := vaaler_sawtooth_approx
  obtain ⟨Ψ, B, c, b, hΨ, hB, _hc_eq, hc_bound, hb0, hb_bound, _hint, happrox⟩ := hV H hH
  let Ψtilde : ℝ → ℝ := fun x => -2 * (Ψ (x / 2) - Ψ ((x - 1) / 2))
  let Btilde : ℝ → ℝ := fun x => 2 * (B (x / 2) + B ((x - 1) / 2))
  let cTilde : ℤ → ℂ := fun h => if |h| ≤ (H : ℤ) ∧ ¬ 2 ∣ h then -4 * c h else 0
  let bTilde : ℤ → ℂ := fun h => if |h| ≤ (H : ℤ) then 2 * (1 + (-1 : ℂ) ^ h) * b h else 0
  refine ⟨Ψtilde, Btilde, cTilde, bTilde, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hsplit : (Ψtilde x : ℂ) = -2 * ((Ψ (x / 2) : ℂ) - (Ψ ((x - 1) / 2) : ℂ)) := by
      simp [Ψtilde]
    rw [hsplit, hΨ (x / 2), hΨ ((x - 1) / 2), ← Finset.sum_sub_distrib, Finset.mul_sum]
    have hsub :
        ((Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0 ∧ ¬ 2 ∣ h)) ⊆
          ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h : ℤ => h ≠ 0 ∧ ¬ 2 ∣ h)) := by
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      exact ⟨⟨by omega, by omega⟩, hh.2⟩
    have hterm : ∀ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
        (-2 : ℂ) * (c h * ePhase ((h : ℝ) * (x / 2)) - c h * ePhase ((h : ℝ) * ((x - 1) / 2))) =
          cTilde h * ePhase ((h : ℝ) * x / 2) := by
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh
      have hhab : |h| ≤ (H : ℤ) := abs_le.mpr hh.1
      have hep : ePhase ((h : ℝ) * ((x - 1) / 2)) = (-1 : ℂ) ^ h * ePhase ((h : ℝ) * x / 2) := by
        rw [show (h : ℝ) * ((x - 1) / 2) = -(h : ℝ) / 2 + (h : ℝ) * x / 2 by ring, ePhase_add, ePhase_half_int]
      rw [show (h : ℝ) * (x / 2) = (h : ℝ) * x / 2 by ring, hep]
      by_cases h2 : 2 ∣ h
      · have hzpow : (-1 : ℂ) ^ h = 1 := by
          obtain ⟨k, rfl⟩ := h2; simp [zpow_mul]
        simp [cTilde, hhab, h2, hzpow]
      · have hzpow : (-1 : ℂ) ^ h = -1 := by
          rcases Int.even_or_odd h with ⟨k, hk⟩ | ⟨k, hk⟩
          · exact absurd ⟨k, by omega⟩ h2
          · rw [hk, zpow_add₀ (by norm_num), zpow_mul]; simp
        simp [cTilde, hhab, h2, hzpow]
        ring
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_filter (p := fun h : ℤ => ¬ 2 ∣ h)]
    have hfilt : ((Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0)).filter (fun h : ℤ => ¬ 2 ∣ h) =
        (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0 ∧ ¬ 2 ∣ h) := by
      ext h; simp [Finset.mem_filter, and_assoc]
    rw [hfilt]
    refine Finset.sum_subset hsub ?_
    intro h hh hnot
    simp only [Finset.mem_filter, Finset.mem_Icc] at hh hnot
    have hnotabs : ¬ |h| ≤ (H : ℤ) := by
      intro hab; apply hnot
      exact ⟨abs_le.mp hab, hh.2⟩
    simp [cTilde, hnotabs]
  · intro x
    have hsplit : (Btilde x : ℂ) = 2 * ((B (x / 2) : ℂ) + (B ((x - 1) / 2) : ℂ)) := by
      simp [Btilde]
    rw [hsplit, hB (x / 2), hB ((x - 1) / 2), ← Finset.sum_add_distrib, Finset.mul_sum]
    have hterm : ∀ h ∈ Finset.Icc (-(H : ℤ)) H,
        (2 : ℂ) * (b h * ePhase ((h : ℝ) * (x / 2)) + b h * ePhase ((h : ℝ) * ((x - 1) / 2))) =
          bTilde h * ePhase ((h : ℝ) * x / 2) := by
      intro h hh
      rw [Finset.mem_Icc] at hh
      have hhab : |h| ≤ (H : ℤ) := abs_le.mpr hh
      have hep : ePhase ((h : ℝ) * ((x - 1) / 2)) = (-1 : ℂ) ^ h * ePhase ((h : ℝ) * x / 2) := by
        rw [show (h : ℝ) * ((x - 1) / 2) = -(h : ℝ) / 2 + (h : ℝ) * x / 2 by ring, ePhase_add, ePhase_half_int]
      rw [show (h : ℝ) * (x / 2) = (h : ℝ) * x / 2 by ring, hep]
      simp [bTilde, hhab]
      ring
    rw [Finset.sum_congr rfl hterm]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← Finset.add_sum_erase _ _ h0mem]
    have h0phase : bTilde 0 * ePhase ((0 : ℝ) * x / 2) = bTilde 0 := by
      have : ePhase ((0 : ℝ) * x / 2) = 1 := by simpa using ePhase_int 0
      rw [this, mul_one]
    rw [h0phase]
    congr 1
    have hsub : (Finset.Icc (-(H : ℤ)) H).erase 0 ⊆
        (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0) := by
      intro h hh
      rw [Finset.mem_erase, Finset.mem_Icc] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hh.1⟩
    refine Finset.sum_subset hsub ?_
    intro h hh hnot
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, not_and] at hh hnot
    have hnotabs : ¬ |h| ≤ (H : ℤ) := by
      intro hab; exact hnot hh.2 (abs_le.mp hab)
    simp [bTilde, hnotabs]
  · have hhab : |(0 : ℤ)| ≤ (H : ℤ) := by simp
    simp only [bTilde, if_pos hhab, zpow_zero, hb0]
    norm_num
    field_simp
    ring
  · intro h hh
    by_cases hcond : |h| ≤ (H : ℤ) ∧ ¬ 2 ∣ h
    · simp only [cTilde, if_pos hcond, norm_mul]
      have h4 : ‖(-4 : ℂ)‖ = 4 := by norm_num
      have hc := hc_bound h hh
      rw [h4]
      linarith
    · simp only [cTilde, if_neg hcond, norm_zero]
      positivity
  · intro h
    by_cases hcond : |h| ≤ (H : ℤ)
    · simp only [bTilde, if_pos hcond, norm_mul]
      have h1pow : ‖(1 : ℂ) + (-1 : ℂ) ^ h‖ ≤ 2 := by
        calc ‖(1 : ℂ) + (-1 : ℂ) ^ h‖ ≤ ‖(1 : ℂ)‖ + ‖(-1 : ℂ) ^ h‖ := norm_add_le _ _
          _ = 2 := by simp
      have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hb := hb_bound h
      have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
      calc ‖(2 : ℂ) * (1 + (-1 : ℂ) ^ h)‖ * ‖b h‖
          = 2 * ‖(1 : ℂ) + (-1 : ℂ) ^ h‖ * ‖b h‖ := by rw [norm_mul, h2norm]
        _ ≤ 2 * 2 * (1 / (2 * (H : ℝ) + 2)) := by gcongr
        _ = 2 / ((H : ℝ) + 1) := by field_simp [hpos.ne']; ring
        _ < 3 / ((H : ℝ) + 1) := by gcongr; norm_num
    · simp only [bTilde, if_neg hcond, norm_zero]
      positivity
  · intro x
    rw [parity_floor_eq_sawtooth x]
    have ha1 := happrox (x / 2)
    have ha2 := happrox ((x - 1) / 2)
    change |-2 * ((x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2) - ((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2)) -
        (-2 * (Ψ (x / 2) - Ψ ((x - 1) / 2)))| ≤ 2 * (B (x / 2) + B ((x - 1) / 2))
    have hrew : -2 * ((x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2) - ((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2)) -
        (-2 * (Ψ (x / 2) - Ψ ((x - 1) / 2))) =
        (-2) * ((x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2 - Ψ (x / 2)) -
          ((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2 - Ψ ((x - 1) / 2))) := by ring
    rw [hrew, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    have htri := abs_sub (x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2 - Ψ (x / 2))
      ((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2 - Ψ ((x - 1) / 2))
    linarith
  · have hsum_le :
        ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
          ‖cTilde h‖ ≤
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
            (if |h| ≤ (H : ℤ) then 2 / (Real.pi * |(h : ℝ)|) else 0) := by
      rw [← Finset.sum_filter (p := fun h : ℤ => ¬ 2 ∣ h)]
      calc ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), ‖cTilde h‖
          ≤ ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
              (if |h| ≤ (H : ℤ) then 2 / (Real.pi * |(h : ℝ)|) else 0) := by
            refine Finset.sum_le_sum fun h hh => ?_
            simp only [Finset.mem_filter] at hh
            by_cases hcond : |h| ≤ (H : ℤ)
            · simp only [if_pos hcond]
              have h4 : ‖cTilde h‖ ≤ 2 / (Real.pi * |(h : ℝ)|) := by
                by_cases h0 : h = 0
                · exact absurd h0 hh.2.1
                · simp [cTilde, hcond, hh.2.2]
                  have hnorm := hc_bound h h0
                  have h4norm : ‖(-4 : ℂ)‖ = 4 := by norm_num
                  rw [norm_mul, h4norm]; linarith
              exact h4
            · simp [cTilde, hcond]
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => by
              simp only [Finset.mem_filter] at hh ⊢; exact ⟨hh.1, hh.2.1⟩) (fun h _ _ => by
              split_ifs <;> positivity)
    have hle_harm :
        ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
          (if |h| ≤ (H : ℤ) then 2 / (Real.pi * |(h : ℝ)|) else 0) ≤
          (4 / Real.pi) * (harmonic H : ℝ) := by
      have hpos_neg :
          ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h : ℤ => h ≠ 0 ∧ |h| ≤ (H : ℤ))) =
            (Finset.Icc (1 : ℤ) H) ∪ (Finset.Icc (1 : ℤ) H).image Neg.neg := by
        ext h
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨_, hne, hab⟩
          rcases le_or_gt h 0 with hle0 | hgt0
          · right; refine ⟨-h, ⟨by omega, by omega⟩, by omega⟩
          · left; exact ⟨by omega, by omega⟩
        · rintro (⟨h1, h2⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
          · exact ⟨⟨by omega, by omega⟩, by omega, by rw [abs_of_nonneg (by omega)]; exact h2⟩
          · exact ⟨⟨by omega, by omega⟩, by omega, by rw [abs_neg, abs_of_nonneg (by omega)]; exact hk2⟩
      have hdisj : Disjoint (Finset.Icc (1 : ℤ) H) ((Finset.Icc (1 : ℤ) H).image Neg.neg) := by
        rw [Finset.disjoint_left]
        intro h h1 h2
        simp only [Finset.mem_Icc, Finset.mem_image] at h1 h2
        rcases h2 with ⟨k, hk, rfl⟩
        omega
      have hfilt1 :
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
            (if |h| ≤ (H : ℤ) then 2 / (Real.pi * |(h : ℝ)|) else 0) =
            ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
              (fun h : ℤ => h ≠ 0 ∧ |h| ≤ (H : ℤ)), 2 / (Real.pi * |(h : ℝ)|) := by
        rw [← Finset.sum_filter (p := fun h : ℤ => |h| ≤ (H : ℤ))]
        have hfeq :
            ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).filter
                (fun h : ℤ => |h| ≤ (H : ℤ)) =
              (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
                (fun h : ℤ => h ≠ 0 ∧ |h| ≤ (H : ℤ)) := by
          ext h; simp [Finset.mem_filter, and_assoc]
        rw [hfeq]
      rw [hfilt1, hpos_neg, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => neg_inj.mp h)]
      have hneg_eq : ∑ x ∈ Finset.Icc (1 : ℤ) H, 2 / (Real.pi * |((-x : ℤ) : ℝ)|) =
          ∑ x ∈ Finset.Icc (1 : ℤ) H, 2 / (Real.pi * |(x : ℝ)|) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Int.cast_neg, abs_neg]
      rw [hneg_eq, ← two_mul, Finset.mul_sum]
      have hIcc_eq : ∑ x ∈ Finset.Icc (1 : ℤ) H, (2 : ℝ) * (2 / (Real.pi * |(x : ℝ)|)) =
          ∑ k ∈ Finset.Icc (1 : ℕ) H, 4 / (Real.pi * (k : ℝ)) := by
        refine Finset.sum_bij (fun x _ => x.natAbs) ?_ ?_ ?_ ?_
        · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
        · intro a ha b hb hab; rw [Finset.mem_Icc] at ha hb; omega
        · intro k hk; rw [Finset.mem_Icc] at hk
          refine ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
        · intro x hx
          rw [Finset.mem_Icc] at hx
          have hxpos : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 0 ≤ x)
          rw [abs_of_nonneg hxpos, show (x.natAbs : ℝ) = (x : ℝ) by exact_mod_cast Int.natAbs_of_nonneg (by omega)]
          ring
      rw [hIcc_eq]
      have hharm : (4 / Real.pi) * (harmonic H : ℝ) = ∑ k ∈ Finset.Icc (1 : ℕ) H, 4 / (Real.pi * (k : ℝ)) := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Rat.cast_inv, Rat.cast_natCast]
        ring
      rw [hharm]
    calc _ ≤ (4 / Real.pi) * (harmonic H : ℝ) := hsum_le.trans hle_harm
      _ ≤ (4 / Real.pi) * (1 + Real.log H) := by gcongr; exact harmonic_le_one_add_log H
      _ ≤ (4 / Real.pi) * (Real.log (2 * H + 1) + 1) := by
          gcongr
          exact Real.log_le_log (by exact_mod_cast hH) (by linarith)

/-- Smooth prime exponential sum bound on `[n^δ, n / (log n)^12]` (Lemma 2.4).
Note (Audit Item 1): the middle saving exponent `P^{-1/(2R+3)}` in Eq. (2.15) and the explicit
formula `min(δ/20, δ/2^{R+3})` in Eq. (2.16) are replaced by the justified saving exponents
`η'_δ > 0` and `η_δ > 0` while preserving the exact final `(log n)^{-(R+2)}` and `n^{-η_δ}` bounds. -/
theorem lemma_2_4_i (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    let AR : ℕ := 6 * R + 16
    ∃ (C η' : ℝ) (N₀ : ℕ), 0 < C ∧ 0 < η' ∧
      ∀ (n : ℕ), N₀ ≤ n →
        let H : ℕ := ⌊(Real.log n) ^ (R + 2)⌋₊
        ∀ (P a b : ℝ) (AI : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
          (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
          P ≤ a → a ≤ b → b ≤ 2 * P →
          AI ⊆ Finset.Icc 1 R →
          (∃ r ∈ AI, h r ≠ 0) →
          (∀ r ∈ AI, |h r| ≤ 2 * (H : ℤ) + 1 ∧
            (n : ℝ) / P ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) →
          0 < W₀ →
          (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
          DifferentiableOn ℝ w (Set.Icc P (2 * P)) →
          (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
          ∃ r₀ ∈ AI, h r₀ ≠ 0 ∧ (∀ r ∈ AI, h r ≠ 0 → r₀ ≤ r) ∧
            let T₀ : ℝ := (|(h r₀ : ℝ)| * n) / P ^ r₀
            let F : ℝ → ℝ := fun t => ∑ r ∈ AI, (h r : ℝ) * n / (2 * t ^ r)
            ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
                (w p : ℂ) * (Real.log p : ℂ) * ePhase (F p)‖ ≤
              C * W₀ * P * (T₀ ^ (-(1 / 6 : ℝ)) + P ^ (-η')) * (Real.log P) ^ 3 ∧
            ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
                (w p : ℂ) * (Real.log p : ℂ) * ePhase (F p)‖ ≤
              C * W₀ * P * (Real.log n) ^ (-((R : ℤ) + 2)) := by
  sorry

theorem lemma_2_4_ii (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    let AR : ℕ := 6 * R + 16
    ∃ (C ηδ : ℝ) (N₀ : ℕ), 0 < C ∧ 0 < ηδ ∧
      ∀ (n : ℕ), N₀ ≤ n →
        let H : ℕ := ⌊(Real.log n) ^ (R + 2)⌋₊
        ∀ (P a b : ℝ) (AI : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
          (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
          P ≤ a → a ≤ b → b ≤ 2 * P →
          AI ⊆ Finset.Icc 1 R →
          (∃ r ∈ AI, h r ≠ 0) →
          (∀ r ∈ AI, |h r| ≤ 2 * (H : ℤ) + 1 ∧
            (n : ℝ) / P ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) →
          0 < W₀ →
          (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
          DifferentiableOn ℝ w (Set.Icc P (2 * P)) →
          (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
          (∀ r₀ ∈ AI, h r₀ ≠ 0 → (∀ r ∈ AI, h r ≠ 0 → r₀ ≤ r) →
            (|(h r₀ : ℝ)| * n) / P ^ r₀ ≥ (n : ℝ) ^ (δ / 2)) →
          let F : ℝ → ℝ := fun t => ∑ r ∈ AI, (h r : ℝ) * n / (2 * t ^ r)
          ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
              (w p : ℂ) * (Real.log p : ℂ) * ePhase (F p)‖ ≤
            C * W₀ * P * (n : ℝ) ^ (-ηδ) := by
  sorry

theorem theorem_2_5_i :
    IsBigOAtTop (fun n => DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * n)
      (fun n => (n : ℝ) / Real.log n) := by
  sorry

theorem theorem_2_5_ii :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
      IsBigOAtTop
        (fun n => ∑ p ∈ (Finset.Icc (Nat.ceil ((n : ℝ) ^ δ)) (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)))
        (fun n => 1 / Real.log n)) ∧
    IsLittleOAtTop SigmaParityStar (fun n => Real.log n) ∧
    IsLittleOAtTop DeltaParity (fun n => (n : ℝ) * Real.log n) ∧
    IsLittleOAtTop (fun n => Sodd n - (1 / 2 : ℝ) * n * Real.log n) (fun n => (n : ℝ) * Real.log n) ∧
    IsLittleOAtTop (fun n => Seven n - (1 / 2 : ℝ) * n * Real.log n) (fun n => (n : ℝ) * Real.log n) := by
  sorry

theorem theorem_2_5_iii (h : ℕ) (hh : 2 ≤ h) (c : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ =>
      ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ padicValNat p n.factorial % h = c % h),
          (padicValNat p n.factorial : ℝ) * Real.log p) / ((n : ℝ) * Real.log n)))
      atTop (𝓝 ((b - a) / (h : ℝ))) := by
  sorry

/-- `r`-digit truncated base-`p` parity sign `ξ_p^{(r)}(n) := - ∏_{m=0}^{r-1} (-1)^{d^{(p)}_{2m+1}(n)}`. -/
def xiTrunc (p r n : ℕ) : ℝ :=
  -(∏ m ∈ Finset.range r, (-1 : ℝ) ^ ((Nat.digits p n).getD (2 * m + 1) 0))

/-- `r`-digit truncated series `Σ_parity^{(r)}(n; B)`. -/
def SigmaParityTrunc (n : ℕ) (B : ℝ) (r : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 ⌊B⌋₊).filter Nat.Prime, xiTrunc p r n * (Real.log p / ((p : ℝ) - 1))

theorem prop_2_6 :
    ∃ (Φ ρ : ℝ → ℝ),
      (∀ τ : ℝ, Tendsto (fun B : ℕ => ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
        Real.cos (τ * Real.log p / ((p : ℝ) - 1))) atTop (𝓝 (Φ τ))) ∧
      (∀ x : ℝ, 0 < ρ x ∧ ρ (-x) = ρ x) ∧
      ContDiff ℝ ⊤ ρ ∧
      (∫ x : ℝ, ρ x) = 1 ∧
      (∀ τ : ℝ, (∫ x : ℝ, Complex.exp (Complex.I * τ * x) * (ρ x : ℂ)) = (Φ τ : ℂ)) ∧
      (∀ B : ℝ, 3 ≤ B → ∀ r : ℕ, 1 ≤ r → ∀ τ : ℝ,
        ∃ φ_Br : ℝ,
          Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) *
            ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * τ * SigmaParityTrunc n B r))
            atTop (𝓝 (φ_Br : ℂ))) ∧
      (∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
          ∃ L_Br : ℝ,
            Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) *
              ∑ n ∈ Finset.Icc 1 N, (SigmaParityTrunc n B r) ^ (2 * m))
              atTop (𝓝 L_Br) ∧
            |L_Br - ∫ x : ℝ, x ^ (2 * m) * ρ x| ≤ ε) := by
  sorry

end BrocardFormalization

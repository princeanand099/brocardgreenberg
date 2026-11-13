/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Section 2: Valuation-Parity Equidistribution of Factorials

This module formalizes Section 2 of the manuscript:
* `lemma_2_1_i`, `lemma_2_1_ii`: Harmonic layer stratification and asymptotics of `𝒫_odd(n)` and `log q_n`.
* `lemma_2_2_i`, `lemma_2_2_ii`: Exact Legendre base-`p` digit reduction on `3 ≤ p ≤ √n`.
* `lemma_2_3`: Vaaler's trigonometric polynomial approximation and even-harmonic cancellation.
* `lemma_2_4_i`, `lemma_2_4_ii`: Prime exponential sum bounds on `[n^δ, n/(log n)^{12}]`.
* `theorem_2_5_i`, `theorem_2_5_ii`, `theorem_2_5_iii`: Valuation-parity equidistribution,
  second-order discrepancy formula, and multi-modulus power-band equidistribution.
* `prop_2_6`: Jessen–Wintner Rademacher limit distribution of truncated base-`p` parity series.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 2.1 Harmonic Prime Layers and the Square-Free Factorial Core -/

/-- Harmonic layer `I_j(n) := {p ≤ n : p prime, n / (j + 1) < p ≤ n / j}`. -/
def harmonicLayer (n j : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun p => p.Prime ∧ n / (j + 1) < p ∧ p ≤ n / j

private lemma padicValNat_factorial_of_lt_sq {n p : ℕ} (hp : p.Prime) (hnsq : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.padicValNat_factorial hnsq]
  have hico : Finset.Ico 1 2 = {1} := by decide
  rw [hico, Finset.sum_singleton, pow_one]

private lemma padicValNat_prod_primes {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ}
    (hp : p.Prime) :
    padicValNat p (∏ q ∈ S, q) = if p ∈ S then 1 else 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  induction S using Finset.induction with
  | empty => simp
  | @insert q s hqs ih =>
    have hq : q.Prime := hS q (Finset.mem_insert_self q s)
    have hs : ∀ r ∈ s, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hqs]
    have hq0 : q ≠ 0 := hq.ne_zero
    have hs0 : (∏ r ∈ s, r) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r hr => (hs r hr).ne_zero
    rw [padicValNat.mul hq0 hs0, ih hs]
    by_cases hpq : p = q
    · subst hpq
      simp [hqs, padicValNat.self hp.one_lt]
    · have hndvd : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
      rw [padicValNat.eq_zero_of_not_dvd hndvd, zero_add]
      simp [hpq]

theorem lemma_2_1_i (n j : ℕ) (hn : 4 ≤ n) (hj1 : 1 ≤ j) (hj2 : j ≤ Nat.sqrt n - 1) :
    (∀ p ∈ harmonicLayer n j, padicValNat p n.factorial = j) ∧
    (∀ r : ℕ, j = 2 * r - 1 → 1 ≤ r → ∀ p ∈ harmonicLayer n j,
      p ∈ Podd n ∧ padicValNat p (qn n) = 1 ∧ padicValNat p (sn n) = r - 1) ∧
    (∀ r : ℕ, j = 2 * r → ∀ p ∈ harmonicLayer n j,
      p ∈ Peven n ∧ padicValNat p (qn n) = 0 ∧ padicValNat p (sn n) = r) := by
  have hsqrt2 : 2 ≤ Nat.sqrt n := by
    have : 2 * 2 ≤ n := by omega
    exact (Nat.le_sqrt).mpr this
  have hj1_le_sqrt : j + 1 ≤ Nat.sqrt n := by omega
  have hsq_le : (j + 1) ^ 2 ≤ n := by
    calc (j + 1) ^ 2 = (j + 1) * (j + 1) := sq (j + 1)
      _ ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hj1_le_sqrt hj1_le_sqrt
      _ ≤ n := Nat.sqrt_le n
  have hp_val : ∀ p ∈ harmonicLayer n j, padicValNat p n.factorial = j := by
    intro p hp
    simp only [harmonicLayer, Finset.mem_filter, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨_, hpn⟩, hp_prime, hlo, hhi⟩
    have hlt_sq : n < p ^ 2 := by
      have h1 : n / (j + 1) + 1 ≤ p := hlo
      have h2 : n < (n / (j + 1) + 1) * (j + 1) := Nat.lt_mul_div_succ n (by omega)
      have h3 : (j + 1) * (j + 1) ≤ n := hsq_le
      have h4 : j + 1 ≤ n / (j + 1) + 1 := by
        by_contra hlt
        push_neg at hlt
        have hle : n / (j + 1) + 1 ≤ j := by omega
        have : n < j * (j + 1) := lt_of_lt_of_le h2 (Nat.mul_le_mul_right _ hle)
        nlinarith
      nlinarith
    rw [padicValNat_factorial_of_lt_sq hp_prime hlt_sq]
    have hmul_le : j * p ≤ n := by
      calc j * p ≤ j * (n / j) := Nat.mul_le_mul_left j hhi
        _ ≤ n := Nat.mul_div_le n j
    have hlt_mul : n < (j + 1) * p := by
      have h1 : n / (j + 1) + 1 ≤ p := hlo
      have h2 : n < (j + 1) * (n / (j + 1) + 1) := by
        rw [mul_comm]; exact Nat.lt_mul_div_succ n (by omega)
      exact lt_of_lt_of_le h2 (Nat.mul_le_mul_left (j + 1) h1)
    exact Nat.div_eq_of_lt_le hmul_le hlt_mul
  refine ⟨hp_val, ?_, ?_⟩
  · intro r hr hr1 p hp
    have hv := hp_val p hp
    simp only [harmonicLayer, Finset.mem_filter, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨hp2, hpn⟩, hp_prime, _, _⟩
    have hodd : ¬ 2 ∣ padicValNat p n.factorial := by omega
    have hp_Podd : p ∈ Podd n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp2, hpn⟩, hp_prime, hodd⟩
    have hvq : padicValNat p (qn n) = 1 := by
      rw [qn_eq_prod_Podd, padicValNat_prod_primes (fun q hq => (Finset.mem_filter.mp hq).2.1) hp_prime]
      simp [hp_Podd]
    have hfac := factorial_eq_qn_mul_sn_sq n
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have hvs : padicValNat p n.factorial = padicValNat p (qn n) + 2 * padicValNat p (sn n) := by
      conv_lhs => rw [hfac]
      rw [padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'), padicValNat.pow 2 (sn_pos n).ne']
    omega
  · intro r hr p hp
    have hv := hp_val p hp
    simp only [harmonicLayer, Finset.mem_filter, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨hp2, hpn⟩, hp_prime, _, _⟩
    have heven : 2 ∣ padicValNat p n.factorial := by omega
    have hp_Peven : p ∈ Peven n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp2, hpn⟩, hp_prime, heven⟩
    have hnot_Podd : p ∉ Podd n := fun h => (Finset.mem_filter.mp h).2.2 heven
    have hvq : padicValNat p (qn n) = 0 := by
      rw [qn_eq_prod_Podd, padicValNat_prod_primes (fun q hq => (Finset.mem_filter.mp hq).2.1) hp_prime]
      simp [hnot_Podd]
    have hfac := factorial_eq_qn_mul_sn_sq n
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have hvs : padicValNat p n.factorial = padicValNat p (qn n) + 2 * padicValNat p (sn n) := by
      conv_lhs => rw [hfac]
      rw [padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'), padicValNat.pow 2 (sn_pos n).ne']
    omega

private lemma alternating_harmonic_sum_bound (K : ℕ) :
    |∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2| ≤
      1 / (2 * (K : ℝ) + 1) := by
  have hsum_eq :
      ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) =
        ∑ j ∈ Finset.range (2 * K), (-1 : ℝ) ^ j / ((j : ℝ) + 1) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.mul_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have h1 : (-1 : ℝ) ^ (2 * K) = 1 := by simp [pow_mul]
      have h2 : (-1 : ℝ) ^ (2 * K + 1) = -1 := by simp [pow_add, pow_mul]
      push_cast
      rw [h1, h2]
      ring
  rw [hsum_eq]
  have hint_log : ∫ t in (0 : ℝ)..1, (1 + t)⁻¹ = Real.log 2 := by
    have h := intervalIntegral.integral_comp_add_right (fun t : ℝ => t⁻¹) (1 : ℝ) (a := 0) (b := 1)
    simp only [zero_add] at h
    rw [h, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have hint_pow :
      ∑ j ∈ Finset.range (2 * K), (-1 : ℝ) ^ j / ((j : ℝ) + 1) =
        ∫ t in (0 : ℝ)..1, ∑ j ∈ Finset.range (2 * K), (-t) ^ j := by
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hpow : ∀ t : ℝ, (-t) ^ j = (-1 : ℝ) ^ j * t ^ j := fun t => by
        rw [neg_eq_neg_one_mul, mul_pow]
      simp_rw [hpow, intervalIntegral.integral_const_mul, integral_pow]
      ring
    · intro j _
      exact (continuous_neg.pow j).intervalIntegrable 0 1
  have hpoly : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 + t)⁻¹ - ∑ j ∈ Finset.range (2 * K), (-t) ^ j = t ^ (2 * K) / (1 + t) := by
    intro t ht
    have h1t : 1 + t ≠ 0 := by linarith [ht.1]
    have hgeom : (1 + t) * ∑ j ∈ Finset.range (2 * K), (-t) ^ j = 1 - (-t) ^ (2 * K) := by
      have := geom_sum_mul (-t) (2 * K)
      calc (1 + t) * ∑ j ∈ Finset.range (2 * K), (-t) ^ j
          = -((-t - 1) * ∑ j ∈ Finset.range (2 * K), (-t) ^ j) := by ring
        _ = -((-t) ^ (2 * K) - 1) := by rw [this]
        _ = 1 - (-t) ^ (2 * K) := by ring
    have heven : (-t) ^ (2 * K) = t ^ (2 * K) := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp [pow_mul]
    rw [heven] at hgeom
    field_simp [h1t]
    linarith
  have hdiff_eq :
      ∑ j ∈ Finset.range (2 * K), (-1 : ℝ) ^ j / ((j : ℝ) + 1) - Real.log 2 =
        - ∫ t in (0 : ℝ)..1, t ^ (2 * K) / (1 + t) := by
    rw [hint_pow, ← hint_log, ← intervalIntegral.integral_sub]
    · rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      linarith [hpoly t ht']
    · exact (Finset.continuous_finset_sum _ fun j _ => continuous_neg.pow j).intervalIntegrable 0 1
    · exact ContinuousOn.intervalIntegrable (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact (continuousAt_const.add continuousAt_id).inv₀ (by linarith [ht'.1]))
  rw [hdiff_eq, abs_neg]
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, t ^ (2 * K) / (1 + t) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
    exact div_nonneg (pow_nonneg ht.1 _) (by linarith [ht.1])
  rw [abs_of_nonneg hnonneg]
  have hle_pow : ∫ t in (0 : ℝ)..1, t ^ (2 * K) / (1 + t) ≤ ∫ t in (0 : ℝ)..1, t ^ (2 * K) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ((continuous_id.pow (2 * K)).intervalIntegrable 0 1) ?_
    · exact ContinuousOn.intervalIntegrable (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact ((continuousAt_id.pow _).div (continuousAt_const.add continuousAt_id) (by linarith [ht'.1])))
    · intro t ht
      exact div_le_self (pow_nonneg ht.1 _) (by linarith [ht.1])
  have hint_mono : ∫ t in (0 : ℝ)..1, t ^ (2 * K) = 1 / (2 * (K : ℝ) + 1) := by
    rw [integral_pow]
    push_cast
    ring
  linarith

theorem lemma_2_1_ii :
    (∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      |Real.log (qn n) - Real.log 2 * (n : ℝ)| ≤
        C * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n))) ∧
    Tendsto (fun n : ℕ => ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  sorry

/-! ### 2.2 Exact Base-p Digit Reduction Below √n -/

/-- Odd-indexed base-`p` digit sum `∑_{m} d_{2m+1}^{(p)}(n)` (Equation 2.6). -/
def oddIndexedDigitSum (p n : ℕ) : ℕ :=
  ((Nat.digits p n).zipIdx.filter (fun x => x.2 % 2 = 1)).map Prod.fst |>.sum

theorem lemma_2_2_i (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (_hn : 4 ≤ n) :
    padicValNat p n.factorial % 2 = oddIndexedDigitSum p n % 2 := by
  sorry

/-- Digit-sum remainder `E_digit(n) := ∑_{3 ≤ p ≤ √n} (-1)^{v_p(n!) - 1} s_p(n) log p / (p - 1)`. -/
def Edigit (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
    (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
      (((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1))

theorem lemma_2_2_ii :
    (∀ n : ℕ, 4 ≤ n →
      ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p =
        -(n : ℝ) * SigmaParityStar n + Edigit n ∧
      |Edigit n| ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n) ∧
    IsBigOAtTop Edigit (fun n => Real.sqrt n) := by
  sorry

/-! ### 2.3 Vaaler Approximation, Exponential Sums, and Equidistribution -/

theorem lemma_2_3 (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Ψtilde Btilde : ℝ → ℝ) (cTilde bTilde : ℤ → ℂ),
      (∀ x : ℝ, (Ψtilde x : ℂ) =
        ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
            (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
          cTilde h * ePhase ((h : ℝ) * x / 2)) ∧
      (∀ x : ℝ, (Btilde x : ℂ) =
        bTilde 0 +
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
            bTilde h * ePhase ((h : ℝ) * x / 2)) ∧
      (bTilde 0 = 2 / ((H : ℂ) + 1)) ∧
      (∀ h : ℤ, h ≠ 0 → ¬ 2 ∣ h → ‖cTilde h‖ ≤ 2 / (Real.pi * |(h : ℝ)|)) ∧
      (∀ h : ℤ, ‖bTilde h‖ < 3 / ((H : ℝ) + 1)) ∧
      (∀ x : ℝ, |(-1 : ℝ) ^ ⌊x⌋ - Ψtilde x| ≤ Btilde x) ∧
      (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
          (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), ‖cTilde h‖ ≤
        (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) := by
  sorry

theorem lemma_2_4_i (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    let AR : ℕ := 6 * R + 16
    ∃ (η'_δ C_δ C'_δ : ℝ), 0 < η'_δ ∧ 0 < C_δ ∧ 0 < C'_δ ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ (n : ℕ) (P : ℝ) (a b : ℝ) (A : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
        N₀ ≤ n → (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
        P ≤ a → a ≤ b → b ≤ 2 * P →
        A ⊆ Finset.Icc 1 R → A.Nonempty →
        (∀ r ∈ A, (n : ℝ) / P ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) →
        (∃ r ∈ A, h r ≠ 0) →
        (∀ r ∈ A, |h r| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1) →
        0 ≤ W₀ → (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
        let r₀ : ℕ := (A.filter (fun r => h r ≠ 0)).min' (by sorry)
        let T₀ : ℝ := (|(h r₀ : ℝ)| * n) / P ^ r₀
        T₀ ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR →
        ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
          C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 ∧
        C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 ≤
          C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by
  sorry

theorem lemma_2_4_ii (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    ∃ (η_δ C_δ : ℝ), 0 < η_δ ∧ 0 < C_δ ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ (n : ℕ) (P : ℝ) (a b : ℝ) (A : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
        N₀ ≤ n → (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
        P ≤ a → a ≤ b → b ≤ 2 * P →
        A ⊆ Finset.Icc 1 R → A.Nonempty →
        (∃ r ∈ A, h r ≠ 0) →
        (∀ r ∈ A, |h r| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1) →
        0 ≤ W₀ → (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
        let r₀ : ℕ := (A.filter (fun r => h r ≠ 0)).min' (by sorry)
        let T₀ : ℝ := (|(h r₀ : ℝ)| * n) / P ^ r₀
        T₀ ≥ (n : ℝ) ^ (δ / 2) →
        ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
          C_δ * W₀ * P * (n : ℝ) ^ (-η_δ) := by
  sorry

theorem theorem_2_5_i :
    IsBigOAtTop
      (fun n => DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ))
      (fun n => (n : ℝ) / Real.log n) := by
  sorry

theorem theorem_2_5_ii :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
      IsBigOAtTop
        (fun n => ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)))
        (fun n => (Real.log n)⁻¹)) ∧
    IsLittleOAtTop SigmaParityStar (fun n => Real.log n) ∧
    IsLittleOAtTop DeltaParity (fun n => (n : ℝ) * Real.log n) ∧
    IsLittleOAtTop (fun n => Sodd n - (1 / 2 : ℝ) * n * Real.log n)
      (fun n => (n : ℝ) * Real.log n) ∧
    IsLittleOAtTop (fun n => Seven n - (1 / 2 : ℝ) * n * Real.log n)
      (fun n => (n : ℝ) * Real.log n) := by
  sorry

theorem theorem_2_5_iii (h : ℕ) (hh : 2 ≤ h) (c : ZMod h) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IsLittleOAtTop
      (fun n =>
        (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
            (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
          (padicValNat p n.factorial : ℝ) * Real.log p) -
        ((b - a) / (h : ℝ)) * (n : ℝ) * Real.log n)
      (fun n => (n : ℝ) * Real.log n) := by
  sorry

/-- `r`-digit truncated base-`p` parity sign `ξ_p^{(r)}(n)` (Proposition 2.6). -/
def truncParitySign (p r n : ℕ) : ℝ :=
  - ∏ m ∈ Finset.range r, (-1 : ℝ) ^ ((n / p ^ (2 * m + 1)) % p)

/-- Truncated base-`p` parity series `Σ_parity^{(r)}(n; B)`. -/
def SigmaParityTrunc (r n B : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
    truncParitySign p r n * (Real.log p / ((p : ℝ) - 1))

theorem prop_2_6 :
    ∃ (Φ ρ : ℝ → ℝ),
      (∀ τ : ℝ, Tendsto (fun B : ℕ => ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
        Real.cos (τ * Real.log p / ((p : ℝ) - 1))) atTop (𝓝 (Φ τ))) ∧
      (∀ x : ℝ, 0 < ρ x ∧ ρ (-x) = ρ x) ∧
      ContDiff ℝ ⊤ ρ ∧
      (∫ x : ℝ, ρ x) = 1 ∧
      (∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ B₀ : ℕ, ∀ B ≥ B₀, ∃ r₀ : ℕ, ∀ r ≥ r₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
          |((1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (SigmaParityTrunc r n B) ^ (2 * m)) -
            ∫ x : ℝ, x ^ (2 * m) * ρ x| ≤ ε) := by
  sorry

end BrocardFormalization

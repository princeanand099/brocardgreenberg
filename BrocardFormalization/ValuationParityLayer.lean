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

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization


/-- Harmonic layer `I_j(n) := {p ≤ n : p prime, n / (j + 1) < p ≤ n / j}`. -/
def harmonicLayer (n j : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun p => p.Prime ∧ n / (j + 1) < p ∧ p ≤ n / j

private lemma padicValNat_factorial_of_lt_sq {n p : ℕ} (hp : p.Prime) (hnsq : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  have : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow hn0 hnsq
  rw [padicValNat_factorial hlog]
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
      rw [padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'), padicValNat.pow (sn n) 2]
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
      rw [padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'), padicValNat.pow (sn n) 2]
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
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hpow : (fun t : ℝ => (-t) ^ j) = (fun t : ℝ => (-1 : ℝ) ^ j * t ^ j) := by
        ext t; rw [neg_eq_neg_one_mul, mul_pow]
      rw [hpow, intervalIntegral.integral_const_mul, integral_pow]
      ring
    · intro j _
      exact (continuous_neg.pow j).intervalIntegrable 0 1
  have hpoly : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 + t)⁻¹ - ∑ j ∈ Finset.range (2 * K), (-t) ^ j = t ^ (2 * K) / (1 + t) := by
    intro t ht
    have h1t : 1 + t ≠ 0 := by linarith [ht.1]
    have hgeom : (1 + t) * ∑ j ∈ Finset.range (2 * K), (-t) ^ j = 1 - (-t) ^ (2 * K) := by
      have := geom_sum_mul (-t) (2 * K)
      have heq : -t - 1 = -(1 + t) := by ring
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
    · exact (continuous_finsetSum _ fun j _ => continuous_neg.pow j).intervalIntegrable 0 1
    · exact ContinuousOn.intervalIntegrable (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        have ht1 : (1 : ℝ) + t ≠ 0 := by linarith [ht'.1]
        exact (continuousAt_const.add continuousAt_id).inv₀ ht1)
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
        have ht1 : (1 : ℝ) + t ≠ 0 := by linarith [ht'.1]
        exact ((continuousAt_id.pow _).div (continuousAt_const.add continuousAt_id) ht1))
    · intro t ht
      exact div_le_self (pow_nonneg ht.1 _) (by linarith [ht.1])
  have hint_mono : ∫ t in (0 : ℝ)..1, t ^ (2 * K) = 1 / (2 * (K : ℝ) + 1) := by
    rw [integral_pow]
    push_cast
    ring
  linarith

theorem lemma_2_1_ii_part1 :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      |Real.log (qn n) - Real.log 2 * (n : ℝ)| ≤
        C * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hpnt⟩ := deLaValleePoussin_pnt
  have hlog_qn : ∀ n : ℕ, Real.log (qn n) = ∑ p ∈ Podd n, Real.log p := by
    intro n
    rw [qn_eq_prod_Podd, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.1.ne_zero
  -- Harmonic layer union / disjointness on odd layers
  have hpart_odd : ∀ n : ℕ, 4 ≤ n →
      let K := (Nat.sqrt n - 1) / 2
      let L := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
      let Tail := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
      Disjoint L Tail ∧ L ∪ Tail = Podd n ∧
      ∀ r ∈ Finset.Icc 1 K, ∀ s ∈ Finset.Icc 1 K, r ≠ s →
        Disjoint (harmonicLayer n (2 * r - 1)) (harmonicLayer n (2 * s - 1)) := by
    intro n hn K L Tail
    have hK_le : 2 * K + 1 ≤ Nat.sqrt n := by omega
    have hdisj_rs : ∀ r ∈ Finset.Icc 1 K, ∀ s ∈ Finset.Icc 1 K, r ≠ s →
        Disjoint (harmonicLayer n (2 * r - 1)) (harmonicLayer n (2 * s - 1)) := by
      intro r hr s hs hrs
      rw [Finset.disjoint_left]
      intro p hpr hps
      simp only [Finset.mem_Icc] at hr hs
      have h1 := (lemma_2_1_i n (2 * r - 1) hn (by omega) (by omega)).1 p hpr
      have h2 := (lemma_2_1_i n (2 * s - 1) hn (by omega) (by omega)).1 p hps
      omega
    have hL_gt : ∀ p ∈ L, n / (2 * K + 1) < p := by
      intro p hp
      simp only [L, Finset.mem_biUnion, Finset.mem_Icc] at hp
      rcases hp with ⟨r, hr, hpr⟩
      simp only [harmonicLayer, Finset.mem_filter] at hpr
      have hle : 2 * r ≤ 2 * K + 1 := by omega
      exact lt_of_le_of_lt (Nat.div_le_div_left hle (by omega)) hpr.2.2.1
    have hL_sub : L ⊆ Podd n := by
      intro p hp
      simp only [L, Finset.mem_biUnion, Finset.mem_Icc] at hp
      rcases hp with ⟨r, hr, hpr⟩
      exact (lemma_2_1_i n (2 * r - 1) hn (by omega) (by omega)).2.1 r rfl hr.1 p hpr |>.1
    refine ⟨?_, ?_, hdisj_rs⟩
    · rw [Finset.disjoint_left]
      intro p hpL hpT
      have := hL_gt p hpL
      have := (Finset.mem_filter.mp hpT).2
      omega
    · apply Finset.Subset.antisymm
      · exact Finset.union_subset hL_sub (Finset.filter_subset _ _)
      · intro p hp
        by_cases hle : p ≤ n / (2 * K + 1)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hle⟩)
        · push_neg at hle
          apply Finset.mem_union_left
          simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hp
          rcases hp with ⟨⟨_, hpn⟩, hp_prime, hodd⟩
          have hsqrt_le : Nat.sqrt n ≤ n / Nat.sqrt n :=
            (Nat.le_div_iff_mul_le (Nat.sqrt_pos.mpr (by omega))).mpr (Nat.sqrt_le n)
          have hdiv_le : n / Nat.sqrt n ≤ n / (2 * K + 1) :=
            Nat.div_le_div_left hK_le (by omega)
          have hp_gt_sqrt : Nat.sqrt n < p := by omega
          have hnsq : n < p ^ 2 := by
            have := Nat.lt_succ_sqrt n
            have hp_ge : Nat.sqrt n + 1 ≤ p := hp_gt_sqrt
            calc n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := this
              _ ≤ p * p := Nat.mul_le_mul hp_ge hp_ge
              _ = p ^ 2 := (sq p).symm
          have hv := padicValNat_factorial_of_lt_sq hp_prime hnsq
          set j := n / p
          rw [hv] at hodd
          have hj1 : 1 ≤ j := Nat.div_pos hpn hp_prime.pos
          have hj_lt : j < 2 * K + 1 := by
            rw [Nat.div_lt_iff_lt_mul hp_prime.pos]
            have h1 : n < (2 * K + 1) * (n / (2 * K + 1) + 1) := by
              rw [mul_comm]; exact Nat.lt_mul_div_succ n (by omega)
            have h2 : n / (2 * K + 1) + 1 ≤ p := hle
            calc n < (2 * K + 1) * (n / (2 * K + 1) + 1) := h1
              _ ≤ (2 * K + 1) * p := Nat.mul_le_mul_left _ h2
          have hj_odd : j % 2 = 1 := Nat.mod_two_ne_zero.mp (fun h0 => hodd (Nat.dvd_of_mod_eq_zero h0))
          set r := (j + 1) / 2
          have hr_mem : r ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hj_eq : j = 2 * r - 1 := by omega
          refine Finset.mem_biUnion.mpr ⟨r, hr_mem, ?_⟩
          simp only [harmonicLayer, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨hp_prime.two_le, hpn⟩, hp_prime, ?_, ?_⟩
          · rw [← hj_eq]
            exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
              have : n < (j + 1) * p := by
                rw [mul_comm]; exact Nat.lt_mul_div_succ n hp_prime.pos
              linarith)
          · rw [← hj_eq]
            exact (Nat.le_div_iff_mul_le hj1).mpr (by
              rw [mul_comm]; exact Nat.div_mul_le_self n p)
  -- Chebyshev theta difference helper
  have htheta_layer : ∀ n j : ℕ, 1 ≤ j →
      ∑ p ∈ harmonicLayer n j, Real.log p =
        Chebyshev.theta ((n : ℝ) / (j : ℝ)) - Chebyshev.theta ((n : ℝ) / ((j : ℝ) + 1)) := by
    intro n j hj
    have hdisj : Disjoint (harmonicLayer n j)
        ((Finset.Icc 2 (n / (j + 1))).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [harmonicLayer, Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
      omega
    have hunion : harmonicLayer n j ∪ (Finset.Icc 2 (n / (j + 1))).filter Nat.Prime =
        (Finset.Icc 2 (n / j)).filter Nat.Prime := by
      ext p
      simp only [harmonicLayer, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro (⟨⟨hp2, _⟩, hp, _, hhi⟩ | ⟨⟨hp2, hle⟩, hp⟩)
        · exact ⟨⟨hp2, hhi⟩, hp⟩
        · have : n / (j + 1) ≤ n / j := Nat.div_le_div_left (by omega) (by omega)
          exact ⟨⟨hp2, le_trans hle this⟩, hp⟩
      · rintro ⟨⟨hp2, hhi⟩, hp⟩
        by_cases hgt : n / (j + 1) < p
        · exact Or.inl ⟨⟨hp2, le_trans hhi (Nat.div_le_self n j)⟩, hp, hgt, hhi⟩
        · exact Or.inr ⟨⟨hp2, by omega⟩, hp⟩
    have htheta_eq : ∀ m : ℕ,
        Chebyshev.theta (m : ℝ) = ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, Real.log p := by
      intro m
      unfold Chebyshev.theta
      rw [Nat.floor_natCast]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hpm⟩, hp⟩; exact ⟨⟨hp.two_le, hpm⟩, hp⟩
      · rintro ⟨⟨hp2, hpm⟩, hp⟩; exact ⟨⟨by omega, hpm⟩, hp⟩
    have hfloor1 : Chebyshev.theta ((n : ℝ) / (j : ℝ)) = Chebyshev.theta ((n / j : ℕ) : ℝ) := by
      unfold Chebyshev.theta
      congr 2
      rw [← Nat.floor_div_eq_div (by positivity) (by positivity)]
      simp [Nat.floor_natCast]
    have hfloor2 : Chebyshev.theta ((n : ℝ) / ((j : ℝ) + 1)) =
        Chebyshev.theta ((n / (j + 1) : ℕ) : ℝ) := by
      unfold Chebyshev.theta
      congr 2
      have hcast : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; rfl
      rw [hcast, ← Nat.floor_div_eq_div (by positivity) (by positivity)]
      simp [Nat.floor_natCast]
    rw [hfloor1, hfloor2, htheta_eq (n / j), htheta_eq (n / (j + 1)), ← hunion,
      Finset.sum_union hdisj]
    ring
-- Pick `c₀ := c₁ / 4` and sufficiently large `C`
  have h_sqrt_log : Tendsto (fun n : ℕ => Real.sqrt (Real.log n)) atTop atTop :=
    tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h_ev : ∀ᶠ n : ℕ in atTop,
      16 ≤ n ∧ c₁ / 2 + 4 ≤ Real.sqrt (Real.log n) ∧
      (1 + Real.log 2 + Real.log n) ≤ Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) ∧
      (Real.log n) ^ 2 ≤ (n : ℝ) := by
    have h1 : ∀ᶠ n : ℕ in atTop, 16 ≤ n := eventually_ge_atTop 16
    have h2 : ∀ᶠ n : ℕ in atTop, c₁ / 2 + 4 ≤ Real.sqrt (Real.log n) :=
      h_sqrt_log.eventually_ge_atTop _
    have h3 : ∀ᶠ n : ℕ in atTop,
        1 + Real.log 2 + Real.log n ≤ Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) := by
      have hexp0 : Tendsto (fun x : ℝ => (1 + Real.log 2 + (4 / c₁) ^ 2 * x ^ 2) * Real.exp (-x))
          atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul ((4 / c₁) ^ 2)
        have h0 : Tendsto (fun x : ℝ => (1 + Real.log 2) * Real.exp (-x)) atTop (𝓝 0) :=
          (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (1 + Real.log 2) |>.trans (by simp)
        have hadd := h0.add this
        simp only [add_zero] at hadd
        refine hadd.congr fun x => ?_
        ring
      have hcomp : Tendsto (fun n : ℕ =>
          (1 + Real.log 2 + (4 / c₁) ^ 2 * ((c₁ / 4) * Real.sqrt (Real.log n)) ^ 2) *
            Real.exp (-((c₁ / 4) * Real.sqrt (Real.log n)))) atTop (𝓝 0) :=
        hexp0.comp ((h_sqrt_log.const_mul (by positivity : 0 < c₁ / 4)).mono_right le_rfl)
      filter_upwards [h2, hcomp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn2 hn1
      have hlog_nn : 0 ≤ Real.log n := by
        have : (4 : ℝ) ≤ Real.sqrt (Real.log n) := by linarith
        nlinarith [Real.sq_sqrt (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16))]
      have hmul : (4 / c₁) ^ 2 * ((c₁ / 4) * Real.sqrt (Real.log n)) ^ 2 = Real.log n := by
        rw [mul_pow, Real.sq_sqrt hlog_nn]
        field_simp [hc₁.ne']
      rw [hmul] at hn1
      have hexp_pos : 0 < Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) := Real.exp_pos _
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hexp_pos] at hn1
      exact hn1
    have h4 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ (n : ℝ) := by
      have hlo := Real.isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      have h1' : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (1 / 2 : ℝ) := by
        filter_upwards [hlo.bound zero_lt_one, eventually_ge_atTop (1 : ℝ)] with x hx hx1
        have := hx
        rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (by positivity),
          one_mul] at this
        exact this
      filter_upwards [tendsto_natCast_atTop_atTop.eventually h1', eventually_ge_atTop 1] with n hn hn1
      have hnn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      calc (Real.log n) ^ 2 ≤ ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ hnn hn 2
        _ = (n : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    exact h1.and (h2.and (h3.and h4))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
  -- For `4 ≤ n < N₀`, bound `|log q_n - log 2 * n|` by a finite max constant `C_fin`
  set C_fin : ℝ := (Finset.Icc 4 N₀).sup' ⟨4, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    (fun n => |Real.log (qn n) - Real.log 2 * n| / ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n))))
  refine ⟨c₁ / 4, max (max C_fin 1) (2 * C₁ + 2 * Real.log 4 + 2), by positivity, by positivity, ?_⟩
  intro n hn4
  by_cases hlt : n < N₀
  · have hmem : n ∈ Finset.Icc 4 N₀ := Finset.mem_Icc.mpr ⟨hn4, hlt.le⟩
    have hle : |Real.log (qn n) - Real.log 2 * n| /
        ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n))) ≤ C_fin :=
      Finset.le_sup' (fun m => |Real.log (qn m) - Real.log 2 * m| /
        ((m : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log m)))) hmem
    have hden : 0 < (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by positivity
    calc |Real.log (qn n) - Real.log 2 * n|
        ≤ C_fin * ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n))) := (div_le_iff₀ hden).mp hle
      _ ≤ max (max C_fin 1) (2 * C₁ + 2 * Real.log 4 + 2) * (n : ℝ) *
          Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hden.le
  · push_neg at hlt
    obtain ⟨hn16, hsq, hlog_exp, _⟩ := hN₀ n hlt
    set K := (Nat.sqrt n - 1) / 2
    set L := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
    set Tail := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
    obtain ⟨hdisj, hunion, hdisj_rs⟩ := hpart_odd n hn4
    have hlog_split :
        Real.log (qn n) =
          ∑ r ∈ Finset.Icc 1 K,
            (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) +
            ∑ p ∈ Tail, Real.log p := by
      rw [hlog_qn, ← hunion, Finset.sum_union hdisj, Finset.sum_biUnion hdisj_rs]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      rw [htheta_layer n (2 * r - 1) (by omega)]
      have h1 : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
        have : 1 ≤ 2 * r := by omega
        push_cast [this]; ring
      have h2 : ((2 * r - 1 : ℕ) : ℝ) + 1 = 2 * (r : ℝ) := by linarith
      rw [h1, h2]
    have hsqrt_ge4 : (4 : ℝ) ≤ Real.sqrt n := by
      have : (16 : ℝ) ≤ n := by exact_mod_cast hn16
      have : (4 : ℝ) ^ 2 ≤ n := by linarith
      exact (Real.le_sqrt_of_sq_le this)
    have h2K1_ge : 1 / 2 * Real.sqrt n ≤ (2 * (K : ℝ) + 1) := by
      have h1 : Nat.sqrt n - 1 ≤ 2 * K + 1 := by omega
      have h2 : Real.sqrt n - 1 ≤ (Nat.sqrt n : ℝ) := by
        have := Nat.lt_succ_sqrt n
        have h3 : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast this
        have h4 : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 :=
          Real.sqrt_lt' (by positivity) |>.mpr h3
        linarith
      have h5 : (Nat.sqrt n : ℝ) - 1 ≤ (2 * (K : ℝ) + 1) := by
        have : Nat.sqrt n ≤ 2 * K + 2 := by omega
        exact_mod_cast (by omega : Nat.sqrt n - 1 ≤ 2 * K + 1)
      linarith
    have hTail_le : |∑ p ∈ Tail, Real.log p| ≤ 2 * Real.log 4 * Real.sqrt n := by
      have hnn : 0 ≤ ∑ p ∈ Tail, Real.log p :=
        Finset.sum_nonneg fun p hp => Real.log_nonneg (by
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.two_le
          exact_mod_cast this)
      rw [abs_of_nonneg hnn]
      have hsub : Tail ⊆ (Finset.Icc 2 (n / (2 * K + 1))).filter Nat.Prime := by
        intro p hp
        have hp1 := Finset.mem_filter.mp hp
        have hp2 := Finset.mem_filter.mp hp1.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp2.1).1, hp1.2⟩, hp2.2.1⟩
      have hle_sum : ∑ p ∈ Tail, Real.log p ≤
          ∑ p ∈ (Finset.Icc 2 (n / (2 * K + 1))).filter Nat.Prime, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.log_nonneg (by norm_num)
      have htheta_cheb : ∑ p ∈ (Finset.Icc 2 (n / (2 * K + 1))).filter Nat.Prime, Real.log p ≤
          Real.log 4 * ((n / (2 * K + 1) : ℕ) : ℝ) := by
        -- Chebyshev theta ≤ log 4 * x
        have h1 : Chebyshev.theta ((n / (2 * K + 1) : ℕ) : ℝ) =
            ∑ p ∈ (Finset.Icc 2 (n / (2 * K + 1))).filter Nat.Prime, Real.log p := by
          unfold Chebyshev.theta
          rw [Nat.floor_natCast]
          congr 1
          ext p
          simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
          exact ⟨fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨hp.two_le, h⟩, hp⟩, fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨hp.pos, h⟩, hp⟩⟩
        rw [← h1]
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      have hdiv_le : ((n / (2 * K + 1) : ℕ) : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1) := by
        have : (n / (2 * K + 1) : ℕ) * (2 * K + 1) ≤ n := Nat.div_mul_le_self n (2 * K + 1)
        have hpos : (0 : ℝ) < 2 * (K : ℝ) + 1 := by positivity
        rw [le_div_iff₀ hpos]
        exact_mod_cast this
      have hdiv_le2 : (n : ℝ) / (2 * (K : ℝ) + 1) ≤ (n : ℝ) / (1 / 2 * Real.sqrt n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2K1_ge
      have hsqrt_eq : (n : ℝ) / (1 / 2 * Real.sqrt n) = 2 * Real.sqrt n := by
        have hsn0 : Real.sqrt n ≠ 0 := (by positivity : 0 < Real.sqrt n).ne'
        field_simp [hsn0]
        rw [Real.sq_sqrt (by positivity)]
      linarith [mul_le_mul_of_nonneg_left (le_trans hdiv_le (le_trans hdiv_le2 hsqrt_eq.le))
        (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))]
    -- Layer log bounds
    have hterm_err : ∀ r ∈ Finset.Icc 1 K,
        |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
          Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
          ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))| ≤
          C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
            Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrK : r ≤ K := (Finset.mem_Icc.mp hr).2
      have h2r_le : 2 * (r : ℝ) ≤ Real.sqrt n := by
        have : 2 * r ≤ Nat.sqrt n := by omega
        exact le_trans (by exact_mod_cast this) (Nat.sqrt_le' n)
      have h2r1_le : 2 * (r : ℝ) - 1 ≤ Real.sqrt n := by linarith
      have hx1 : 2 ≤ (n : ℝ) / (2 * (r : ℝ) - 1) := by
        rw [le_div_iff₀ (by linarith : 0 < 2 * (r : ℝ) - 1)]
        have hsn : 2 * (2 * (r : ℝ) - 1) ≤ 2 * Real.sqrt n := by linarith
        nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
      have hx2 : 2 ≤ (n : ℝ) / (2 * (r : ℝ)) := by
        rw [le_div_iff₀ (by linarith : 0 < 2 * (r : ℝ))]
        have hsn : 2 * (2 * (r : ℝ)) ≤ 2 * Real.sqrt n := by linarith
        nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
      have hlog_ge : ∀ y : ℝ, 2 ≤ y → y ≤ 2 * (r : ℝ) →
          Real.sqrt (Real.log n) / 2 ≤ Real.sqrt (Real.log ((n : ℝ) / y)) := by
        intro y hy2 hyr
        have hny : Real.sqrt n ≤ (n : ℝ) / y := by
          rw [le_div_iff₀ (by linarith)]
          calc Real.sqrt n * y ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left (le_trans hyr h2r_le) (by positivity)
            _ = n := Real.mul_self_sqrt (by positivity)
        have hlog_ge' : 1 / 2 * Real.log n ≤ Real.log ((n : ℝ) / y) := by
          have h1 : 1 / 2 * Real.log n = Real.log (Real.sqrt n) := by
            rw [Real.log_sqrt (by positivity)]; ring
          rw [h1]
          exact Real.log_le_log (by positivity) hny
        have hsq1 : (Real.sqrt (Real.log n) / 2) ^ 2 ≤ Real.log ((n : ℝ) / y) := by
          rw [div_pow, Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))]
          linarith
        exact Real.le_sqrt_of_sq_le hsq1
      have he1 := (hpnt _ hx1).1
      have he2 := (hpnt _ hx2).1
      have hsq1 := hlog_ge (2 * (r : ℝ) - 1) (by have : (1 : ℝ) ≤ r := by exact_mod_cast hr1; linarith) (by linarith)
      have hsq2 := hlog_ge (2 * (r : ℝ)) (by have : (1 : ℝ) ≤ r := by exact_mod_cast hr1; linarith) le_rfl
      have hexp1 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1)))) ≤
          Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      have hexp2 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ))))) ≤
          Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      have htri : |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
          Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
          ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))| ≤
          |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)| +
          |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))| := by
        have : Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
            Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
            ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) =
            (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)) -
            (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))) := by ring
        rw [this]
        exact abs_sub _ _
      calc |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) - Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
            ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))|
          ≤ C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) +
            C₁ * ((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) := by
            refine le_trans htri (add_le_add ?_ ?_)
            · exact le_trans he1 (mul_le_mul_of_nonneg_left hexp1 (by positivity))
            · exact le_trans he2 (mul_le_mul_of_nonneg_left hexp2 (by positivity))
        _ = C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
            Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) := by ring
    have hharm_sum : ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) =
        (harmonic (2 * K) : ℝ) := by
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.mul_succ, harmonic_succ, harmonic_succ]
        push_cast
        ring
    have hharm_le : (harmonic (2 * K) : ℝ) ≤ 1 + Real.log n := by
      have h1 := harmonic_le_one_add_log (2 * K)
      have h2K_le : (2 * K : ℝ) ≤ n := by
        have : 2 * K ≤ Nat.sqrt n := by omega
        exact le_trans (by exact_mod_cast this) (le_trans (Nat.sqrt_le' n) (by
          have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]))
      by_cases hK0 : K = 0
      · simp [hK0]
        exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      · have h2K_pos : (0 : ℝ) < 2 * K := by positivity
        have := Real.log_le_log h2K_pos h2K_le
        linarith
    have htheta_err :
        |∑ r ∈ Finset.Icc 1 K,
          (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
            Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
            ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))| ≤
          C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by
      calc |∑ r ∈ Finset.Icc 1 K, _|
          ≤ ∑ r ∈ Finset.Icc 1 K, |Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ Finset.Icc 1 K, C₁ * ((n : ℝ) / (2 * (r : ℝ) - 1) + (n : ℝ) / (2 * (r : ℝ))) *
              Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) := Finset.sum_le_sum hterm_err
        _ = C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) *
              ∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => by ring
        _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) * (1 + Real.log n) := by
            rw [hharm_sum]
            exact mul_le_mul_of_nonneg_left hharm_le (by positivity)
        _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log n)) *
              Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
        _ = C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2; ring_nf
    have halt_tail :
        |∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) -
          Real.log 2 * (n : ℝ)| ≤ 2 * Real.sqrt n := by
      have hfac :
          ∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) -
            Real.log 2 * (n : ℝ) =
            (n : ℝ) * (∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) -
              Real.log 2) := by
        rw [mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun r _ => by ring
      rw [hfac, abs_mul, abs_of_nonneg (by positivity)]
      have hbd := alternating_harmonic_sum_bound K
      have hdiv_le : 1 / (2 * (K : ℝ) + 1) ≤ 2 / Real.sqrt n := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc (n : ℝ) * |∑ r ∈ Finset.Icc 1 K, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2|
          ≤ (n : ℝ) * (2 / Real.sqrt n) := mul_le_mul_of_nonneg_left (le_trans hbd hdiv_le) (by positivity)
        _ = 2 * Real.sqrt n := by
            have hsn0 : Real.sqrt n ≠ 0 := (by positivity : 0 < Real.sqrt n).ne'
            field_simp [hsn0]; rw [Real.sq_sqrt (by positivity)]
    have hsqrt_le_exp : Real.sqrt n ≤ (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by
      have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hexp_le_sqrt : Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) ≤ Real.sqrt n := by
        have h1 : (c₁ / 4) * Real.sqrt (Real.log n) ≤ (1 / 2) * Real.log n := by
          have h2 : c₁ / 4 ≤ (1 / 2) * Real.sqrt (Real.log n) := by linarith
          calc (c₁ / 4) * Real.sqrt (Real.log n)
              ≤ ((1 / 2) * Real.sqrt (Real.log n)) * Real.sqrt (Real.log n) :=
                mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
            _ = (1 / 2) * (Real.sqrt (Real.log n)) ^ 2 := by ring
            _ = (1 / 2) * Real.log n := by rw [Real.sq_sqrt hlog_nn]
        calc Real.exp ((c₁ / 4) * Real.sqrt (Real.log n))
            ≤ Real.exp ((1 / 2) * Real.log n) := Real.exp_le_exp.mpr h1
          _ = (n : ℝ) ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < n), mul_comm]
          _ = Real.sqrt n := (Real.sqrt_eq_rpow n).symm
      have h2 : Real.sqrt n * Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) ≤ (n : ℝ) := by
        calc Real.sqrt n * Real.exp ((c₁ / 4) * Real.sqrt (Real.log n))
            ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hexp_le_sqrt (Real.sqrt_nonneg _)
          _ = (n : ℝ) := Real.mul_self_sqrt (by positivity)
      have hexp_pos : 0 < Real.exp ((c₁ / 4) * Real.sqrt (Real.log n)) := Real.exp_pos _
      rw [neg_mul, Real.exp_neg, mul_inv_le_iff₀ hexp_pos]
      simpa [mul_comm] using h2
    have hcomb :
        |Real.log (qn n) - Real.log 2 * (n : ℝ)| ≤
          |∑ r ∈ Finset.Icc 1 K,
            (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))| +
          |∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) -
            Real.log 2 * (n : ℝ)| +
          |∑ p ∈ Tail, Real.log p| := by
      rw [hlog_split]
      have hsub :
          ∑ r ∈ Finset.Icc 1 K,
              (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
                Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ)))) +
            ∑ p ∈ Tail, Real.log p - Real.log 2 * (n : ℝ) =
          (∑ r ∈ Finset.Icc 1 K,
            (Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ) - 1)) -
              Chebyshev.theta ((n : ℝ) / (2 * (r : ℝ))) -
              ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))))) +
          (∑ r ∈ Finset.Icc 1 K, ((n : ℝ) / (2 * (r : ℝ) - 1) - (n : ℝ) / (2 * (r : ℝ))) -
            Real.log 2 * (n : ℝ)) +
          ∑ p ∈ Tail, Real.log p := by
        simp only [Finset.sum_sub_distrib]; ring
      rw [hsub]
      exact le_trans (abs_add_le _ _) (add_le_add_right (abs_add_le _ _) _)
    have hbd_all :
        |Real.log (qn n) - Real.log 2 * (n : ℝ)| ≤
          (C₁ + 2 + 2 * Real.log 4) * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by
      calc |Real.log (qn n) - Real.log 2 * (n : ℝ)|
          ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) +
            2 * Real.sqrt n + 2 * Real.log 4 * Real.sqrt n := by
              linarith [htheta_err, halt_tail, hTail_le]
        _ ≤ C₁ * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) +
            (2 + 2 * Real.log 4) * ((n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n))) := by
              have hpos : 0 ≤ 2 + 2 * Real.log 4 := by positivity
              nlinarith [hsqrt_le_exp]
        _ = (C₁ + 2 + 2 * Real.log 4) * (n : ℝ) * Real.exp (-(c₁ / 4) * Real.sqrt (Real.log n)) := by ring
    refine le_trans hbd_all ?_
    have hC_le : C₁ + 2 + 2 * Real.log 4 ≤ max (max C_fin 1) (2 * C₁ + 2 * Real.log 4 + 2) := by
      exact le_trans (by linarith [hC₁]) (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC_le (by positivity)) (Real.exp_pos _).le

end BrocardFormalization

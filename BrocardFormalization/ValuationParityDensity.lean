/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParityLayer
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

theorem lemma_2_1_ii_part2 :
    Tendsto (fun n : ℕ => ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hpnt⟩ := deLaValleePoussin_pnt
  have hpc_eq : ∀ m : ℕ, (Nat.primeCounting m : ℝ) = ((Finset.Icc 2 m).filter Nat.Prime).card := by
    intro m
    congr 1
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    exact ⟨fun ⟨hp1, hp2⟩ => ⟨⟨hp2.two_le, Nat.lt_succ_iff.mp hp1⟩, hp2⟩,
      fun ⟨⟨_, hp1⟩, hp2⟩ => ⟨Nat.lt_succ_iff.mpr hp1, hp2⟩⟩
  have hpi_ub : ∀ m : ℕ, 4 ≤ m →
      (Nat.primeCounting m : ℝ) ≤ 2 * Real.sqrt m + 2 * Real.log 4 * (m : ℝ) / Real.log m := by
    intro m hm4
    have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hsplit : (Finset.Icc 2 m).filter Nat.Prime =
        ((Finset.Icc 2 (Nat.sqrt m)).filter Nat.Prime) ∪
        ((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      omega
    have hcard_le : ((Finset.Icc 2 m).filter Nat.Prime).card ≤
        Nat.sqrt m + ((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card := by
      rw [hsplit]
      refine le_trans (Finset.card_union_le _ _) (add_le_add_right ?_ _)
      exact le_trans (Finset.card_filter_le _ _) (by simp [Nat.card_Icc]; omega)
    have hlog_sum : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) *
        ((1 / 2 : ℝ) * Real.log m) ≤ Real.log 4 * (m : ℝ) := by
      have h1 : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) *
          ((1 / 2 : ℝ) * Real.log m) ≤
          ∑ p ∈ (Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime, Real.log p := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_gt : Nat.sqrt m < p := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
          omega
        have hm_lt : (m : ℝ) < (p : ℝ) ^ 2 := by
          have : m < p * p := by
            have hlt := Nat.lt_succ_sqrt m
            have hge : Nat.sqrt m + 1 ≤ p := hp_gt
            exact lt_of_lt_of_le hlt (Nat.mul_le_mul hge hge)
          exact_mod_cast (by simpa [sq] using this)
        have hlog_lt : Real.log m < 2 * Real.log p := by
          have := Real.log_lt_log (by positivity) hm_lt
          rwa [Real.log_pow] at this
        linarith
      have h2 : ∑ p ∈ (Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime, Real.log p ≤
          Chebyshev.theta (m : ℝ) := by
        unfold Chebyshev.theta
        rw [Nat.floor_natCast]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_nonneg (by norm_num)
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩
      exact le_trans h1 (le_trans h2 (Chebyshev.theta_le_log4_mul_x (by positivity)))
    have hsqrt_le : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le m)
    have hcard_hi : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) ≤
        2 * Real.log 4 * (m : ℝ) / Real.log m := by
      rw [le_div_iff₀ hlogm_pos]
      linarith
    rw [hpc_eq m]
    have hcard_cast : (((Finset.Icc 2 m).filter Nat.Prime).card : ℝ) ≤
        (Nat.sqrt m : ℝ) + (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) := by
      exact_mod_cast hcard_le
    linarith
  have hli_est : ∀ x : ℝ, 16 ≤ x → (Real.log x) ^ 2 ≤ Real.sqrt x →
      |(∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) - x / Real.log x| ≤
        (x / (Real.log x) ^ 2) / Real.log 2 +
        (x / (Real.log x) ^ 2) / Real.log x +
        x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) := by
    intro x hx16 hlog_sq_le
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hsqrt_ge4 : 4 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    set a : ℝ := x / (Real.log x) ^ 2
    have ha_le_sqrt : a ≤ Real.sqrt x := by
      rw [div_le_iff₀ (pow_pos hlogx_pos 2)]
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg x]
    have ha_le_x : a ≤ x := by
      have hsqrt_le_x : Real.sqrt x ≤ x := by
        have : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
        nlinarith [hsqrt_ge4]
      exact le_trans ha_le_sqrt hsqrt_le_x
    have h2_le_a : 2 ≤ a := by
      have h1 : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
      rw [div_le_div_iff₀] at *
      · exact le_trans (by linarith) (show Real.sqrt x ≤ a from by
          rw [le_div_iff₀ (pow_pos hlogx_pos 2)]
          nlinarith [Real.mul_self_sqrt (by linarith : 0 ≤ x)])
      all_goals positivity
    have hint1 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 2 a := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le h2_le_a] at ht
      have hlt : 1 < t := by linarith [ht.1]
      exact (Real.continuousAt_log hlt.ne').inv₀ (Real.log_pos hlt).ne' |>.continuousWithinAt
    have hint2 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume a x := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le ha_le_x] at ht
      have hlt : 1 < t := by linarith [ht.1, h2_le_a]
      exact (Real.continuousAt_log hlt.ne').inv₀ (Real.log_pos hlt).ne' |>.continuousWithinAt
    have hsplit_int : ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ =
        (∫ t in (2 : ℝ)..a, (Real.log t)⁻¹) + (∫ t in a..x, (Real.log t)⁻¹) :=
      (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    have h1_nn : 0 ≤ ∫ t in (2 : ℝ)..a, (Real.log t)⁻¹ := by
      refine intervalIntegral.integral_nonneg h2_le_a fun t ht => ?_
      exact inv_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
    have h1_ub : ∫ t in (2 : ℝ)..a, (Real.log t)⁻¹ ≤ a / Real.log 2 := by
      have hbd : ∫ t in (2 : ℝ)..a, (Real.log t)⁻¹ ≤ ∫ _t in (2 : ℝ)..a, (Real.log 2)⁻¹ := by
        refine intervalIntegral.integral_mono_on h2_le_a hint1 (continuous_const.intervalIntegrable _ _) fun t ht => ?_
        exact inv_anti₀ (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) ht.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hbd
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc ∫ t in (2 : ℝ)..a, (Real.log t)⁻¹
          ≤ (a - 2) * (Real.log 2)⁻¹ := hbd
        _ ≤ a * (Real.log 2)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hlog2.le)
        _ = a / Real.log 2 := (div_eq_mul_inv _ _).symm
    have h2_bd : |∫ t in a..x, (Real.log t)⁻¹ - (x - a) / Real.log x| ≤
        x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) := by
      have hconst : (x - a) / Real.log x = ∫ _t in a..x, (Real.log x)⁻¹ := by
        rw [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]
      rw [hconst, ← intervalIntegral.integral_sub hint2 (continuous_const.intervalIntegrable _ _)]
      have hle_int : |∫ t in a..x, ((Real.log t)⁻¹ - (Real.log x)⁻¹)| ≤
          ∫ t in a..x, |(Real.log t)⁻¹ - (Real.log x)⁻¹| :=
        intervalIntegral.abs_integral_le_integral_abs ha_le_x
      have hpt : ∀ t ∈ Set.Icc a x,
          |(Real.log t)⁻¹ - (Real.log x)⁻¹| ≤
            (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) := by
        intro t ht
        have ht_pos : 0 < t := by linarith [ht.1, h2_le_a]
        have hlogt_ge_a : Real.log a ≤ Real.log t := Real.log_le_log (by linarith [h2_le_a]) ht.1
        have hloga_eq : Real.log a = Real.log x - 2 * Real.log (Real.log x) := by
          rw [Real.log_div (by linarith) (pow_pos hlogx_pos 2).ne', Real.log_pow]; ring
        have hlogt_ge : 1 / 2 * Real.log x ≤ Real.log t := by
          have hsqrt_le_a : Real.sqrt x ≤ a := by
            rw [le_div_iff₀ (pow_pos hlogx_pos 2)]
            nlinarith [Real.mul_self_sqrt (by linarith : 0 ≤ x)]
          have h1 := Real.log_le_log (by positivity) (le_trans hsqrt_le_a ht.1)
          rwa [Real.log_sqrt (by positivity)] at h1
        have hlogt_pos : 0 < Real.log t := by linarith
        have hlogt_le : Real.log t ≤ Real.log x := Real.log_le_log ht_pos ht.2
        have hdiff : |(Real.log t)⁻¹ - (Real.log x)⁻¹| =
            (Real.log x - Real.log t) / (Real.log t * Real.log x) := by
          rw [abs_of_nonneg (sub_nonneg.mpr (inv_anti₀ hlogt_pos hlogt_le)),
            inv_sub_inv hlogt_pos.ne' hlogx_pos.ne']
        rw [hdiff]
        have hnum : Real.log x - Real.log t ≤ 2 * Real.log (Real.log x) := by linarith
        have hden : (1 / 2 * Real.log x) * Real.log x ≤ Real.log t * Real.log x :=
          mul_le_mul_of_nonneg_right hlogt_ge hlogx_pos.le
        exact div_le_div₀ (by positivity) hnum (by positivity) hden
      have hint_abs : IntervalIntegrable (fun t : ℝ => |(Real.log t)⁻¹ - (Real.log x)⁻¹|)
          MeasureTheory.volume a x :=
        (hint2.sub (continuous_const.intervalIntegrable _ _)).abs
      have hmono := intervalIntegral.integral_mono_on ha_le_x hint_abs
        (continuous_const.intervalIntegrable a x) hpt
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      have hlen : x - a ≤ x := by linarith [h2_le_a]
      have hnn_rhs : 0 ≤ (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) := by
        have : 1 ≤ Real.log x := by
          have : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
          exact Real.one_le_log_iff.mpr ⟨by linarith, by linarith⟩
        exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg this)) (by positivity)
      calc |∫ t in a..x, ((Real.log t)⁻¹ - (Real.log x)⁻¹)|
          ≤ (x - a) * ((2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x)) :=
            le_trans hle_int hmono
        _ ≤ x * ((2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x)) :=
            mul_le_mul_of_nonneg_right hlen hnn_rhs
        _ = x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) := by ring
    rw [hsplit_int]
    have hdecomp : (∫ t in (2 : ℝ)..a, (Real.log t)⁻¹) + (∫ t in a..x, (Real.log t)⁻¹) - x / Real.log x =
        (∫ t in (2 : ℝ)..a, (Real.log t)⁻¹) - a / Real.log x +
        ((∫ t in a..x, (Real.log t)⁻¹) - (x - a) / Real.log x) := by ring
    rw [hdecomp]
    have ha_nn : 0 ≤ a / Real.log x := div_nonneg (by linarith) hlogx_pos.le
    calc |(∫ t in (2 : ℝ)..a, (Real.log t)⁻¹) - a / Real.log x +
            ((∫ t in a..x, (Real.log t)⁻¹) - (x - a) / Real.log x)|
        ≤ |(∫ t in (2 : ℝ)..a, (Real.log t)⁻¹) - a / Real.log x| +
          |(∫ t in a..x, (Real.log t)⁻¹) - (x - a) / Real.log x| := abs_add_le _ _
      _ ≤ (|∫ t in (2 : ℝ)..a, (Real.log t)⁻¹| + |a / Real.log x|) +
          x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) :=
          add_le_add (abs_sub _ _) h2_bd
      _ ≤ (a / Real.log 2 + a / Real.log x) +
          x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) := by
          rw [abs_of_nonneg h1_nn, abs_of_nonneg ha_nn]
          linarith [h1_ub]
  have h_ev2 : ∀ᶠ n : ℕ in atTop,
      64 ≤ n ∧ 2 * ⌊Real.log n⌋₊ + 1 ≤ Nat.sqrt n ∧
      (Real.log (n : ℝ) / (2 * ⌊Real.log n⌋₊ + 1)) ≥ 16 ∧
      ∀ x : ℝ, (n : ℝ) / (2 * (⌊Real.log n⌋₊ : ℝ) + 1) ≤ x → x ≤ (n : ℝ) →
        16 ≤ x ∧ (Real.log x) ^ 2 ≤ Real.sqrt x := by
    have hlo_sq : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ 2 ≤ Real.sqrt x := by
      filter_upwards [eventually_ge_atTop ((64 : ℝ) ^ 4)] with x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
      have hx_pos : 0 < x := by positivity
      have hr8 : 0 < x ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hx_pos _
      have hlog8 : Real.log (x ^ (1 / 8 : ℝ)) ≤ x ^ (1 / 8 : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hr8]
      rw [Real.log_rpow hx_pos] at hlog8
      have h1 : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by linarith
      have h2 : (Real.log x) ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := by
        calc (Real.log x) ^ 2 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (Real.log_nonneg hx1) h1 2
          _ = 64 * (x ^ (1 / 8 : ℝ)) ^ 2 := by ring
          _ = 64 * x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]; norm_num
      have h64 : (64 : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (64 : ℝ) 4] at hx
        exact (Real.le_rpow_inv_iff_of_pos (by positivity) hx_pos.le (by norm_num : (0 : ℝ) < 4)).mpr (by simpa using hx)
      calc (Real.log x) ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := h2
        _ ≤ x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right h64 (by positivity)
        _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx_pos]; norm_num
        _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    obtain ⟨M, hM⟩ := eventually_atTop.mp hlo_sq
    have h_n_ev : ∀ᶠ n : ℕ in atTop,
        64 ≤ n ∧ 2 * Real.log n + 1 ≤ Real.sqrt n ∧
        M ≤ (n : ℝ) / (2 * Real.log n + 1) ∧ 16 ≤ (n : ℝ) / (2 * Real.log n + 1) := by
      have hlog_lt : ∀ᶠ n : ℕ in atTop, (2 * Real.log n + 1) * max (max M 16) 1 ≤ (n : ℝ) ∧
          (2 * Real.log n + 1) ^ 2 ≤ (n : ℝ) := by
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max (max M 16) (8 ^ 8) ^ 4))] with n hn_big
        have hn1 : (1 : ℝ) ≤ n := by
          have h16 : (16 : ℝ) ≤ max (max M 16) (8 ^ 8) := le_trans (by norm_num) (le_max_right _ _)
          exact le_trans (by norm_num : (1 : ℝ) ≤ 16 ^ 4) (le_trans (pow_le_pow_left₀ (by positivity) h16 4) hn_big)
        have hn_pos : (0 : ℝ) < n := by positivity
        have h8_8 : (8 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
          have hbig : (8 : ℝ) ^ (8 : ℕ) ≤ (n : ℝ) := by
            have h1 : (8 : ℝ) ^ (8 : ℕ) ≤ max (max M 16) (8 ^ 8) := le_max_right _ _
            have h2 : max (max M 16) (8 ^ 8) ≤ max (max M 16) (8 ^ 8) ^ 4 := by
              have hge1 : (1 : ℝ) ≤ max (max M 16) (8 ^ 8) := le_trans (by norm_num) h1
              calc max (max M 16) (8 ^ 8) ≤ max (max M 16) (8 ^ 8) * 1 := by ring
                _ ≤ max (max M 16) (8 ^ 8) * max (max M 16) (8 ^ 8) ^ 3 :=
                  mul_le_mul_of_nonneg_left (one_le_pow₀ hge1) (by positivity)
                _ = max (max M 16) (8 ^ 8) ^ 4 := by ring
            exact le_trans h1 (le_trans h2 hn_big)
          rw [← Real.rpow_natCast (8 : ℝ) 8] at hbig
          exact (Real.le_rpow_inv_iff_of_pos (by positivity) hn_pos.le (by norm_num : (0 : ℝ) < 8)).mpr (by simpa using hbig)
        have hlog_le : Real.log n ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
          have hr8 : 0 < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hn_pos _
          have hlog8 : Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
            linarith [Real.log_le_sub_one_of_pos hr8]
          rw [Real.log_rpow hn_pos] at hlog8
          calc Real.log n ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by linarith
            _ ≤ (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_right h8_8 (by positivity)
            _ = (n : ℝ) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hn_pos]; norm_num
        have hn4_ge : max (max M 16) 16 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
          have hmax_le : max (max M 16) 16 ^ 4 ≤ (n : ℝ) := by
            have hle : max (max M 16) 16 ≤ max (max M 16) (8 ^ 8) := max_le_max le_rfl (by norm_num)
            exact le_trans (pow_le_pow_left₀ (by positivity) hle 4) hn_big
          rw [← Real.rpow_natCast (max (max M 16) 16) 4] at hmax_le
          exact (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 4)).mpr hmax_le
        have h2log : 2 * Real.log n + 1 ≤ 3 * (n : ℝ) ^ (1 / 4 : ℝ) := by
          have : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := le_trans (by norm_num) (le_trans (le_max_right _ _) hn4_ge)
          linarith
        constructor
        · calc (2 * Real.log n + 1) * max (max M 16) 1
              ≤ (3 * (n : ℝ) ^ (1 / 4 : ℝ)) * (n : ℝ) ^ (1 / 4 : ℝ) := by
                refine mul_le_mul h2log ?_ (by positivity) (by positivity)
                exact le_trans (max_le_max (le_rfl) (by norm_num)) hn4_ge
            _ = 3 * (n : ℝ) ^ (1 / 2 : ℝ) := by
                rw [mul_assoc, ← Real.rpow_add (by positivity)]; norm_num
            _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact le_trans (by norm_num) (le_trans (le_max_right _ _) hn4_ge)
            _ ≤ (n : ℝ) := by
                rw [← Real.rpow_add (by positivity)]
                exact Real.rpow_le_self_of_one_le hn1 (by norm_num)
        · calc (2 * Real.log n + 1) ^ 2
              ≤ (3 * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2log 2
            _ = 9 * (n : ℝ) ^ (1 / 2 : ℝ) := by
                rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
            _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact le_trans (by norm_num) (le_trans (le_max_right _ _) hn4_ge)
            _ ≤ (n : ℝ) := by
                rw [← Real.rpow_add (by positivity)]
                exact Real.rpow_le_self_of_one_le hn1 (by norm_num)
      filter_upwards [eventually_ge_atTop 64, hlog_lt] with n hn64 ⟨h1, h2⟩
      refine ⟨hn64, Real.le_sqrt_of_sq_le h2, ?_, ?_⟩
      · rw [le_div_iff₀ (by have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)); positivity)]
        exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)); positivity))
          (le_trans h1 (mul_le_mul_of_nonneg_left (le_max_left _ _) (by have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)); positivity) |>.trans h1 |> fun _ => le_rfl))
      · rw [le_div_iff₀ (by have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)); positivity)]
        exact le_trans (mul_le_mul_of_nonneg_left (le_trans (by norm_num : (16 : ℝ) ≤ max (max M 16) 1) (le_rfl)) (by have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)); positivity)) h1
    filter_upwards [h_n_ev] with n ⟨hn64, hsqrt, hM_le, h16_le⟩
    have hfl_le : (⌊Real.log n⌋₊ : ℝ) ≤ Real.log n := Nat.floor_le (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    refine ⟨hn64, ?_, ?_, ?_⟩
    · have h1 : (2 * ⌊Real.log n⌋₊ + 1 : ℝ) ≤ Real.sqrt n := by linarith
      have h2 : (2 * ⌊Real.log n⌋₊ + 1 : ℝ) ^ 2 ≤ n := by
        have := pow_le_pow_left₀ (by positivity) h1 2
        rwa [Real.sq_sqrt (by positivity)] at this
      exact Nat.le_sqrt.mpr (by exact_mod_cast (by simpa [sq] using h2 : ((2 * ⌊Real.log n⌋₊ + 1) ^ 2 : ℝ) ≤ n))
    · exact le_trans h16_le (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
    · intro x hx_lo hx_hi
      have hx_ge : (n : ℝ) / (2 * Real.log n + 1) ≤ x :=
        le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)) hx_lo
      exact ⟨le_trans h16_le hx_ge, hM x (le_trans hM_le hx_ge)⟩
  have hpart_odd_gen : ∀ n K : ℕ, 4 ≤ n → 2 * K + 1 ≤ Nat.sqrt n →
      let L := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
      let Tail := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
      Disjoint L Tail ∧ L ∪ Tail = Podd n ∧
        (Finset.Icc 1 K : Set ℕ).PairwiseDisjoint (fun r => harmonicLayer n (2 * r - 1)) := by
    intro n K hn hK_le
    dsimp only
    set L := (Finset.Icc 1 K).biUnion (fun r => harmonicLayer n (2 * r - 1))
    set Tail := (Podd n).filter (fun p => p ≤ n / (2 * K + 1))
    have hdisj_rs : (Finset.Icc 1 K : Set ℕ).PairwiseDisjoint (fun r => harmonicLayer n (2 * r - 1)) := by
      intro r hr s hs hrs
      simp only [Finset.mem_coe, Finset.mem_Icc] at hr hs
      rw [Finset.disjoint_left]
      intro p hpr hps
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
  have hlayer_card : ∀ n j : ℕ, 1 ≤ j →
      ((harmonicLayer n j).card : ℝ) =
        (Nat.primeCounting (n / j) : ℝ) - (Nat.primeCounting (n / (j + 1)) : ℝ) := by
    intro n j hj
    have hdisj : Disjoint (harmonicLayer n j) ((Finset.Icc 2 (n / (j + 1))).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [harmonicLayer, Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
      omega
    have hunion : harmonicLayer n j ∪ (Finset.Icc 2 (n / (j + 1))).filter Nat.Prime =
        (Finset.Icc 2 (n / j)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_union, harmonicLayer, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro (⟨⟨hp2, _⟩, hp, _, hhi⟩ | ⟨⟨hp2, hhi⟩, hp⟩)
        · exact ⟨⟨hp2, hhi⟩, hp⟩
        · exact ⟨⟨hp2, le_trans hhi (Nat.div_le_div_left (by omega) (by omega))⟩, hp⟩
      · rintro ⟨⟨hp2, hhi⟩, hp⟩
        by_cases hle : p ≤ n / (j + 1)
        · exact Or.inr ⟨⟨hp2, hle⟩, hp⟩
        · push_neg at hle
          have hpn : p ≤ n := le_trans hhi (Nat.div_le_self n j)
          exact Or.inl ⟨⟨hp2, hpn⟩, hp, hle, hhi⟩
    have hcard_u := Finset.card_union_of_disjoint hdisj
    rw [hunion] at hcard_u
    have h1 : (((Finset.Icc 2 (n / j)).filter Nat.Prime).card : ℝ) = (Nat.primeCounting (n / j) : ℝ) :=
      (hpc_eq (n / j)).symm
    have h2 : (((Finset.Icc 2 (n / (j + 1))).filter Nat.Prime).card : ℝ) =
        (Nat.primeCounting (n / (j + 1)) : ℝ) := (hpc_eq (n / (j + 1))).symm
    have hcast : ((harmonicLayer n j).card : ℝ) +
        (((Finset.Icc 2 (n / (j + 1))).filter Nat.Prime).card : ℝ) =
        (((Finset.Icc 2 (n / j)).filter Nat.Prime).card : ℝ) := by exact_mod_cast hcard_u
    linarith
  have h_unif : ∀ᶠ n : ℕ in atTop,
      let K₀ := ⌊Real.log n⌋₊
      1 ≤ K₀ ∧ 2 * K₀ + 1 ≤ Nat.sqrt n ∧ 4 ≤ Real.log n ∧
      (1 / 2 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / (2 * (K₀ : ℝ) + 1)) ∧
      (∀ x : ℝ, (n : ℝ) / (2 * (K₀ : ℝ) + 1) ≤ x → x ≤ (n : ℝ) →
        |(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log n| ≤
          (C₁ + 40) * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) := by
    have h_log_big : ∀ᶠ n : ℕ in atTop,
        4 ≤ Real.log n ∧ 2 * Real.log (2 * Real.log n + 1) ≤ (1 / 2 : ℝ) * Real.log n ∧
        (1 / 2 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / (2 * Real.log n + 1)) ∧
        Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n)) ≤ 1 / (Real.log n) ^ 2 := by
      have h1 : ∀ᶠ n : ℕ in atTop, 4 ≤ Real.log n :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
      have h2 : ∀ᶠ n : ℕ in atTop, 2 * Real.log (2 * Real.log n + 1) ≤ (1 / 2 : ℝ) * Real.log n := by
        filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 16] with n hn16
        have hlog_pos : 0 < Real.log n := by linarith
        have hle : 2 * Real.log n + 1 ≤ 3 * Real.log n := by linarith
        have h3 : Real.log (2 * Real.log n + 1) ≤ Real.log (3 * Real.log n) :=
          Real.log_le_log (by positivity) hle
        have hsqrt : Real.log (Real.sqrt (Real.log n)) ≤ Real.sqrt (Real.log n) - 1 :=
          Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hlog_pos)
        have hlog_u : Real.log (Real.log n) = 2 * Real.log (Real.sqrt (Real.log n)) := by
          rw [← Real.log_pow, Real.sq_sqrt hlog_pos.le]
        have hlog3 : Real.log (3 * Real.log n) = Real.log 3 + Real.log (Real.log n) :=
          Real.log_mul (by norm_num) hlog_pos.ne'
        have hlog3_le : Real.log 3 ≤ 2 := by
          have : (3 : ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
            linarith
          exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
        have hsq4 : 4 ≤ Real.sqrt (Real.log n) := Real.le_sqrt_of_sq_le hn16
        nlinarith [Real.sq_sqrt hlog_pos.le]
      have h3 : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / (2 * Real.log n + 1)) := by
        filter_upwards [h1, h2] with n hn4 hn_le
        have hlog_pos : 0 < Real.log n := by linarith
        rw [Real.log_div (by positivity) (by positivity)]
        linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)]
      have h4 : ∀ᶠ n : ℕ in atTop, Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n)) ≤ 1 / (Real.log n) ^ 2 := by
        have h_tend : Tendsto (fun n : ℕ => (Real.log n) ^ 2 * Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n)))
            atTop (𝓝 0) := by
          have h0 : Tendsto (fun x : ℝ => ((2 / c₁ ^ 2) * x ^ 2) ^ 2 * Real.exp (-x)) atTop (𝓝 0) := by
            have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul ((2 / c₁ ^ 2) ^ 2)
            simpa [pow_mul, mul_pow] using this
          have harg : Tendsto (fun n : ℕ => c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n)) atTop atTop := by
            rw [Filter.tendsto_atTop_atTop]
            intro b
            have hb : ∀ᶠ n : ℕ in atTop, 2 * (max b 0 / c₁) ^ 2 ≤ Real.log n :=
              (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
            obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
            refine ⟨N, fun n hn => ?_⟩
            have h1 : max b 0 / c₁ ≤ Real.sqrt ((1 / 2 : ℝ) * Real.log n) := by
              rw [← Real.sqrt_sq (div_nonneg (le_max_right b 0) hc₁.le)]
              exact Real.sqrt_le_sqrt (by linarith [hN n hn])
            calc b ≤ max b 0 := le_max_left b 0
              _ = c₁ * (max b 0 / c₁) := by field_simp [hc₁.ne']
              _ ≤ c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n) := mul_le_mul_of_nonneg_left h1 hc₁.le
          refine (h0.comp harg).congr' ?_
          filter_upwards [h1] with n hn4
          have hsq : (c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n)) ^ 2 = c₁ ^ 2 * ((1 / 2 : ℝ) * Real.log n) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          have heq : (2 / c₁ ^ 2) * (c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log n)) ^ 2 = Real.log n := by
            rw [hsq]; field_simp [hc₁.ne']
          dsimp only [Function.comp_def]
          rw [heq, neg_mul]
        filter_upwards [h1, h_tend.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn4 hn1
        have hlog_pos : 0 < Real.log n := by linarith
        rw [le_div_iff₀ (pow_pos hlog_pos 2), mul_comm]
        exact hn1
      exact h1.and (h2.and (h3.and h4))
    filter_upwards [h_ev2, h_log_big] with n ⟨hn64, hsqrt, _, hx_ok⟩ ⟨hn4, _, hhalf, hexp⟩
    set K₀ := ⌊Real.log n⌋₊
    have hK₀_pos : 1 ≤ K₀ := Nat.one_le_floor_iff.mpr (by linarith)
    have hfl_le : (K₀ : ℝ) ≤ Real.log n := Nat.floor_le (by linarith)
    have hhalf_K₀ : (1 / 2 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / (2 * (K₀ : ℝ) + 1)) :=
      le_trans hhalf (Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)))
    refine ⟨hK₀_pos, hsqrt, hn4, hhalf_K₀, fun x hx_lo hx_hi => ?_⟩
    obtain ⟨hx16, hlog_sq_le⟩ := hx_ok x hx_lo hx_hi
    have hlogx_ge : (1 / 2 : ℝ) * Real.log n ≤ Real.log x :=
      le_trans hhalf_K₀ (Real.log_le_log (by positivity) hx_lo)
    have hlogx_pos : 0 < Real.log x := by linarith
    have hlogn_pos : 0 < Real.log n := by linarith
    have hpnt_x := (hpnt x (by linarith)).2
    have hli_x := hli_est x hx16 hlog_sq_le
    have hdiff_log : Real.log n - Real.log x ≤ Real.log (2 * Real.log n + 1) := by
      have hx_ge : (n : ℝ) / (2 * Real.log n + 1) ≤ x :=
        le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)) hx_lo
      have h1 : Real.log ((n : ℝ) / (2 * Real.log n + 1)) ≤ Real.log x := Real.log_le_log (by positivity) hx_ge
      rw [Real.log_div (by positivity) (by positivity)] at h1
      linarith
    have hrat_diff : |x / Real.log x - x / Real.log n| ≤
        4 * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := by
      have h1 : x / Real.log x - x / Real.log n = x * (Real.log n - Real.log x) / (Real.log x * Real.log n) := by
        field_simp [hlogx_pos.ne', hlogn_pos.ne']
      rw [h1, abs_div, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by positivity)]
      have hden : (1 / 2 * Real.log n) * Real.log n ≤ Real.log x * Real.log n :=
        mul_le_mul_of_nonneg_right hlogx_ge hlogn_pos.le
      calc x * (Real.log n - Real.log x) / (Real.log x * Real.log n)
          ≤ x * (Real.log (2 * Real.log n + 1) + 1) / ((1 / 2 * Real.log n) * Real.log n) :=
            div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) (by positivity) hden
        _ = 2 * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := by ring
        _ ≤ 4 * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := by
            have hnn : 0 ≤ (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n :=
              div_nonneg (mul_nonneg (div_nonneg (by linarith) hlogn_pos.le)
                (by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)])) hlogn_pos.le
            linarith
    have hexp_x : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ 1 / (Real.log n) ^ 2 := by
      refine le_trans (Real.exp_le_exp.mpr ?_) hexp
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlogx_ge) (by linarith)
    have hC1_bd : C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤
        C₁ * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := by
      have h1 : C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ C₁ * x * (1 / (Real.log n) ^ 2) :=
        mul_le_mul_of_nonneg_left hexp_x (by positivity)
      have h2 : C₁ * x * (1 / (Real.log n) ^ 2) = C₁ * (x / Real.log n) * 1 / Real.log n := by ring
      have h3 : (1 : ℝ) ≤ Real.log (2 * Real.log n + 1) + 1 := by
        linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)]
      calc C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x))
          ≤ C₁ * (x / Real.log n) * 1 / Real.log n := by linarith
        _ ≤ C₁ * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hlogn_pos.le
    have hlog_log_x : Real.log (Real.log x) ≤ Real.log (2 * Real.log n + 1) + 1 := by
      have : Real.log x ≤ 2 * Real.log n + 1 := by linarith [Real.log_le_log (by linarith) hx_hi]
      linarith [Real.log_le_log hlogx_pos this]
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h_li_bd : (x / (Real.log x) ^ 2) / Real.log 2 + (x / (Real.log x) ^ 2) / Real.log x +
        x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) ≤
        36 * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := by
      have hlogx_sq : (1 / 4 : ℝ) * (Real.log n) ^ 2 ≤ (Real.log x) ^ 2 := by nlinarith
      have h1 : (x / (Real.log x) ^ 2) / Real.log 2 ≤ 8 * (x / Real.log n) * 1 / Real.log n := by
        have : (x / (Real.log x) ^ 2) / Real.log 2 ≤ (x / ((1 / 4 : ℝ) * (Real.log n) ^ 2)) / (1 / 2) :=
          div_le_div₀ (by positivity) (div_le_div_of_nonneg_left (by linarith) (by positivity) hlogx_sq)
            (by positivity) hlog2_ge
        linarith [show (x / ((1 / 4 : ℝ) * (Real.log n) ^ 2)) / (1 / 2) = 8 * (x / Real.log n) * 1 / Real.log n by ring]
      have h2 : (x / (Real.log x) ^ 2) / Real.log x ≤ 8 * (x / Real.log n) * 1 / Real.log n := by
        have hlogx_ge1 : (1 : ℝ) ≤ Real.log x := by linarith
        have : (x / (Real.log x) ^ 2) / Real.log x ≤ (x / ((1 / 4 : ℝ) * (Real.log n) ^ 2)) / 1 :=
          div_le_div₀ (by positivity) (div_le_div_of_nonneg_left (by linarith) (by positivity) hlogx_sq)
            (by positivity) hlogx_ge1
        linarith [show (x / ((1 / 4 : ℝ) * (Real.log n) ^ 2)) / 1 = 4 * (x / Real.log n) * 1 / Real.log n by ring,
          show 0 ≤ (x / Real.log n) * 1 / Real.log n by positivity]
      have h3 : x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) ≤
          20 * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := by
        have hden : (1 / 8 : ℝ) * (Real.log n) ^ 2 ≤ (1 / 2 * Real.log x) * Real.log x := by nlinarith
        have : x * (2 * Real.log (Real.log x)) / ((1 / 2 * Real.log x) * Real.log x) ≤
            x * (2 * (Real.log (2 * Real.log n + 1) + 1)) / ((1 / 8 : ℝ) * (Real.log n) ^ 2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
            (by positivity) hden
        linarith [show x * (2 * (Real.log (2 * Real.log n + 1) + 1)) / ((1 / 8 : ℝ) * (Real.log n) ^ 2) =
          16 * (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n by ring,
          show 0 ≤ (x / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n by
            exact div_nonneg (mul_nonneg (div_nonneg (by linarith) hlogn_pos.le)
              (by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)])) hlogn_pos.le]
      have h1_le : (1 : ℝ) ≤ Real.log (2 * Real.log n + 1) + 1 := by
        linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)]
      have hnn_f : 0 ≤ (x / Real.log n) / Real.log n := by positivity
      nlinarith
    have htri : |(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log n| ≤
        |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹| +
        |(∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) - x / Real.log x| +
        |x / Real.log x - x / Real.log n| := by
      have := abs_add_le ((Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹)
        ((∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) - x / Real.log x)
      have := abs_add_le ((Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) (x / Real.log x - x / Real.log n)
      linarith
    linarith
  have h_err_zero : Tendsto (fun n : ℕ =>
      (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (Real.log (2 * u + 1) + 1) ^ 2 / u) atTop (𝓝 0) := by
      have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
        refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx; exact div_nonneg (Real.log_nonneg hx) (by positivity)) ?_
          ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).const_mul 8)
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        have hr8 : 0 < x ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hx _
        have hlog8 : Real.log (x ^ (1 / 8 : ℝ)) ≤ x ^ (1 / 8 : ℝ) := by linarith [Real.log_le_sub_one_of_pos hr8]
        rw [Real.log_rpow hx] at hlog8
        calc Real.log x / x ^ (1 / 4 : ℝ)
            ≤ (8 * x ^ (1 / 8 : ℝ)) / x ^ (1 / 4 : ℝ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ = 8 * x ^ (-(1 / 8 : ℝ)) := by
              rw [mul_div_assoc, div_eq_mul_inv, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]; norm_num
      have hcomp : Tendsto (fun u : ℝ => Real.log (2 * u + 1) / (2 * u + 1) ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
        hlo.comp (tendsto_atTop_add_const_right _ 1 (tendsto_id.const_mul_atTop (by norm_num)))
      have hsq : Tendsto (fun u : ℝ =>
          (Real.log (2 * u + 1) / (2 * u + 1) ^ (1 / 4 : ℝ) + 1 / (2 * u + 1) ^ (1 / 4 : ℝ)) ^ 2 *
            ((2 * u + 1) ^ (1 / 2 : ℝ) / u)) atTop (𝓝 0) := by
        have hinv : Tendsto (fun u : ℝ => 1 / (2 * u + 1) ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            ((tendsto_rpow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ 1 (tendsto_id.const_mul_atTop (by norm_num))))
        have hsum := (hcomp.add hinv).pow 2
        simp only [add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsum
        have hrat : Tendsto (fun u : ℝ => (2 * u + 1) ^ (1 / 2 : ℝ) / u) atTop (𝓝 0) := by
          have h0 : Tendsto (fun u : ℝ => (2 + 1 / u) ^ (1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
            have hA : Tendsto (fun u : ℝ => (2 + 1 / u) ^ (1 / 2 : ℝ)) atTop (𝓝 ((2 + 0 : ℝ) ^ (1 / 2 : ℝ))) :=
              ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).rpow_const (by left; norm_num))
            have hB : Tendsto (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
              tendsto_rpow_neg_atTop (by norm_num)
            simpa using hA.mul hB
          refine h0.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
          have h2u : 2 * u + 1 = u * (2 + 1 / u) := by field_simp [hu.ne']; ring
          rw [h2u, Real.mul_rpow hu.le (by positivity)]
          have hu1 : u ^ (1 / 2 : ℝ) / u = u ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hu]; norm_num
          rw [mul_div_assoc, mul_comm (u ^ (1 / 2 : ℝ)), ← mul_div_assoc, mul_div_right_comm, hu1, mul_comm]
        simpa using hsum.mul hrat
      refine hsq.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have h2u : 0 < 2 * u + 1 := by linarith
      have hr : ((2 * u + 1) ^ (1 / 4 : ℝ)) ^ 2 = (2 * u + 1) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h2u.le]; norm_num
      field_simp [h2u.ne', hu.ne']
      rw [div_pow, hr, div_mul_cancel₀ _ (Real.rpow_pos_of_pos h2u _).ne']
    exact h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h_pi_lim : Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h_ev_err := h_err_zero.eventually (Metric.ball_mem_nhds 0 (div_pos hε (by norm_num : (0 : ℝ) < C₁ + 41)))
    filter_upwards [h_unif, h_ev_err] with n ⟨hK₀, _, hn4, _, hunif_n⟩ herr
    have hlogn_pos : 0 < Real.log n := by linarith
    have hn_pos : (0 : ℝ) < n := by
      by_contra h0
      push_neg at h0
      have : n = 0 := by exact_mod_cast le_antisymm h0 (Nat.cast_nonneg n)
      subst this; simp at hn4
    have hbd := hunif_n (n : ℝ) (div_le_self hn_pos.le (by exact_mod_cast (by omega : 1 ≤ 2 * ⌊Real.log n⌋₊ + 1))) le_rfl
    rw [Nat.floor_natCast] at hbd
    have hden_pos : 0 < (n : ℝ) / Real.log n := div_pos hn_pos hlogn_pos
    rw [Real.dist_eq, show (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n) - 1 =
        ((Nat.primeCounting n : ℝ) - (n : ℝ) / Real.log n) / ((n : ℝ) / Real.log n) by field_simp [hden_pos.ne']]
    rw [abs_div, abs_of_pos hden_pos, div_lt_iff₀ hden_pos]
    have h1_le : (1 : ℝ) ≤ Real.log (2 * Real.log n + 1) + 1 := by
      linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)]
    have herr' : (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n < ε / (C₁ + 41) := by
      simpa [Real.dist_eq, abs_of_nonneg (div_nonneg (sq_nonneg _) hlogn_pos.le)] using herr
    have hlin : (Real.log (2 * Real.log n + 1) + 1) / Real.log n ≤
        (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n :=
      div_le_div_of_nonneg_right (by nlinarith) hlogn_pos.le
    calc |(Nat.primeCounting n : ℝ) - (n : ℝ) / Real.log n|
        ≤ (C₁ + 40) * ((n : ℝ) / Real.log n) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n := hbd
      _ = (C₁ + 40) * ((Real.log (2 * Real.log n + 1) + 1) / Real.log n) * ((n : ℝ) / Real.log n) := by ring
      _ ≤ (C₁ + 40) * (ε / (C₁ + 41)) * ((n : ℝ) / Real.log n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans hlin herr'.le) (by positivity)) hden_pos.le
      _ < ε * ((n : ℝ) / Real.log n) := by
          refine mul_lt_mul_of_pos_right ?_ hden_pos
          rw [mul_div_assoc', div_lt_iff₀ (by positivity : 0 < C₁ + 41)]
          nlinarith [hC₁, hε]
  have h_podd_lim : Tendsto (fun n : ℕ => ((Podd n).card : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 (Real.log 2)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h_K0_atTop : Tendsto (fun n : ℕ => ⌊Real.log n⌋₊) atTop atTop :=
      Nat.tendsto_floor_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h_alt_ev : ∀ᶠ n : ℕ in atTop, 1 / (2 * (⌊Real.log n⌋₊ : ℝ) + 1) < ε / 4 := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * (⌊Real.log n⌋₊ : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 1 ((tendsto_natCast_atTop_atTop.comp h_K0_atTop).const_mul_atTop (by norm_num)))
      exact h1.eventually (Metric.ball_mem_nhds 0 (div_pos hε (by norm_num))) |>.mono fun n hn => by
        simpa [Real.dist_eq, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * (⌊Real.log n⌋₊ : ℝ) + 1))] using hn
    have h_err_ev : ∀ᶠ n : ℕ in atTop,
        (C₁ + 40) * 4 * (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n < ε / 4 := by
      have h1 := (h_err_zero.const_mul ((C₁ + 40) * 4)).eventually (Metric.ball_mem_nhds 0 (div_pos hε (by norm_num)))
      exact h1.mono fun n hn => by
        have : (C₁ + 40) * 4 * ((Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n) =
            (C₁ + 40) * 4 * (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n := by ring
        rw [← this]
        simpa [Real.dist_eq] using lt_of_le_of_lt (le_abs_self _) hn
    have h_tail_ev : ∀ᶠ n : ℕ in atTop,
        2 * Real.log n / Real.sqrt n + 8 * Real.log 4 / (2 * (⌊Real.log n⌋₊ : ℝ) + 1) < ε / 4 := by
      have hA : Tendsto (fun n : ℕ => 2 * Real.log n / Real.sqrt n) atTop (𝓝 0) := by
        have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
          refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx; exact div_nonneg (Real.log_nonneg hx) (by positivity)) ?_
            ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4)
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          have hr4 : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
          have hlog4 : Real.log (x ^ (1 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) := by linarith [Real.log_le_sub_one_of_pos hr4]
          rw [Real.log_rpow hx] at hlog4
          calc Real.log x / x ^ (1 / 2 : ℝ)
              ≤ (4 * x ^ (1 / 4 : ℝ)) / x ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
            _ = 4 * x ^ (-(1 / 4 : ℝ)) := by
                rw [mul_div_assoc, div_eq_mul_inv, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]; norm_num
        have h1 : Tendsto (fun n : ℕ => 2 * (Real.log n / (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
          simpa using (hlo.comp tendsto_natCast_atTop_atTop).const_mul 2
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        rw [Real.sqrt_eq_rpow]; ring
      have hB : Tendsto (fun n : ℕ => 8 * Real.log 4 / (2 * (⌊Real.log n⌋₊ : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 1 ((tendsto_natCast_atTop_atTop.comp h_K0_atTop).const_mul_atTop (by norm_num)))
      have hAB := hA.add hB
      simp only [add_zero] at hAB
      exact (hAB.eventually (Metric.ball_mem_nhds 0 (div_pos hε (by norm_num)))).mono fun n hn =>
        lt_of_le_of_lt (le_abs_self _) hn
    filter_upwards [h_unif, h_ev2, h_alt_ev, h_err_ev, h_tail_ev] with n ⟨hK₀, hsqrt, hn4, hhalf_K₀, hunif_n⟩ ⟨hn64, _, _, _⟩ halt_bd herr_bd htail_bd
    set K₀ := ⌊Real.log n⌋₊
    have hlogn_pos : 0 < Real.log n := by linarith
    have hn_pos : (0 : ℝ) < n := by positivity
    have hden_pos : 0 < (n : ℝ) / Real.log n := div_pos hn_pos hlogn_pos
    obtain ⟨hdisj, hunion, hdisj_rs⟩ := hpart_odd_gen n K₀ (by omega) hsqrt
    have hcard_split : ((Podd n).card : ℝ) =
        (∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ)) +
        (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) := by
      have h1 : (Podd n).card =
          (∑ r ∈ Finset.Icc 1 K₀, (harmonicLayer n (2 * r - 1)).card) +
          ((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card := by
        rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hdisj_rs]
      exact_mod_cast h1
    have hL_sum : ∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) =
        ∑ r ∈ Finset.Icc 1 K₀,
          ((Nat.primeCounting (n / (2 * r - 1)) : ℝ) - (Nat.primeCounting (n / (2 * r)) : ℝ)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      rw [hlayer_card n (2 * r - 1) (by omega), show 2 * r - 1 + 1 = 2 * r by omega]
    have hL_err : |∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
        ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| ≤
        ((n : ℝ) / Real.log n) * (ε / 4) := by
      rw [hL_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ r ∈ Finset.Icc 1 K₀,
          |(Nat.primeCounting (n / (2 * r - 1)) : ℝ) - (Nat.primeCounting (n / (2 * r)) : ℝ) -
            ((n : ℝ) / Real.log n) * ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| ≤
          ((n : ℝ) / Real.log n) * ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) *
            (1 / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) := by
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hrK : r ≤ K₀ := (Finset.mem_Icc.mp hr).2
        have h1_lo : (n : ℝ) / (2 * (K₀ : ℝ) + 1) ≤ (n : ℝ) / (2 * (r : ℝ) - 1) :=
          div_le_div_of_nonneg_left hn_pos.le (by positivity) (by
            have : (r : ℝ) ≤ K₀ := by exact_mod_cast hrK
            linarith)
        have h2_lo : (n : ℝ) / (2 * (K₀ : ℝ) + 1) ≤ (n : ℝ) / (2 * (r : ℝ)) :=
          div_le_div_of_nonneg_left hn_pos.le (by positivity) (by
            have : (r : ℝ) ≤ K₀ := by exact_mod_cast hrK
            linarith)
        have h1_hi : (n : ℝ) / (2 * (r : ℝ) - 1) ≤ n :=
          div_le_self hn_pos.le (by have : (1 : ℝ) ≤ r := by exact_mod_cast hr1; linarith)
        have h2_hi : (n : ℝ) / (2 * (r : ℝ)) ≤ n :=
          div_le_self hn_pos.le (by have : (1 : ℝ) ≤ r := by exact_mod_cast hr1; linarith)
        have hb1 := hunif_n ((n : ℝ) / (2 * (r : ℝ) - 1)) h1_lo h1_hi
        have hb2 := hunif_n ((n : ℝ) / (2 * (r : ℝ))) h2_lo h2_hi
        have hfl1 : ⌊(n : ℝ) / (2 * (r : ℝ) - 1)⌋₊ = n / (2 * r - 1) := by
          have hcast : 2 * (r : ℝ) - 1 = ((2 * r - 1 : ℕ) : ℝ) := by
            have : 1 ≤ 2 * r := by omega
            push_cast [this]; ring
          rw [hcast, ← Nat.floor_div_eq_div (by positivity) (by positivity), Nat.floor_natCast]
        have hfl2 : ⌊(n : ℝ) / (2 * (r : ℝ))⌋₊ = n / (2 * r) := by
          have hcast : 2 * (r : ℝ) = ((2 * r : ℕ) : ℝ) := by push_cast; rfl
          rw [hcast, ← Nat.floor_div_eq_div (by positivity) (by positivity), Nat.floor_natCast]
        rw [hfl1] at hb1; rw [hfl2] at hb2
        have hsub_eq : (Nat.primeCounting (n / (2 * r - 1)) : ℝ) - (Nat.primeCounting (n / (2 * r)) : ℝ) -
            ((n : ℝ) / Real.log n) * ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) =
            ((Nat.primeCounting (n / (2 * r - 1)) : ℝ) - ((n : ℝ) / (2 * (r : ℝ) - 1)) / Real.log n) -
            ((Nat.primeCounting (n / (2 * r)) : ℝ) - ((n : ℝ) / (2 * (r : ℝ))) / Real.log n) := by ring
        rw [hsub_eq]
        refine le_trans (abs_sub _ _) ?_
        linarith [show ((n : ℝ) / (2 * (r : ℝ) - 1) / Real.log n) = ((n : ℝ) / Real.log n) * (1 / (2 * (r : ℝ) - 1)) by ring,
          show ((n : ℝ) / (2 * (r : ℝ)) / Real.log n) = ((n : ℝ) / Real.log n) * (1 / (2 * (r : ℝ))) by ring]
      calc ∑ r ∈ Finset.Icc 1 K₀,
            |(Nat.primeCounting (n / (2 * r - 1)) : ℝ) - (Nat.primeCounting (n / (2 * r)) : ℝ) -
              ((n : ℝ) / Real.log n) * ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))|
          ≤ ∑ r ∈ Finset.Icc 1 K₀,
              ((n : ℝ) / Real.log n) * ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) *
                (1 / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) := Finset.sum_le_sum hterm
        _ = ((n : ℝ) / Real.log n) * ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) *
              ∑ r ∈ Finset.Icc 1 K₀, (1 / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) := by
              rw [Finset.mul_sum]
        _ ≤ ((n : ℝ) / Real.log n) * ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) *
              (1 + Real.log (2 * (K₀ : ℝ))) := by
              have hharm : ∑ r ∈ Finset.Icc 1 K₀, (1 / (2 * (r : ℝ) - 1) + 1 / (2 * (r : ℝ))) = (harmonic (2 * K₀) : ℝ) := by
                clear hterm
                induction K₀ with
                | zero => simp
                | succ k ih =>
                  rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.mul_succ, harmonic_succ, harmonic_succ]
                  push_cast; ring
              rw [hharm]
              refine mul_le_mul_of_nonneg_left ?_ (by
                exact mul_nonneg hden_pos.le (div_nonneg (mul_nonneg (by positivity)
                  (by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)])) hlogn_pos.le))
              simpa using harmonic_le_one_add_log (2 * K₀)
        _ ≤ ((n : ℝ) / Real.log n) * (ε / 4) := by
              have hlog2K : 1 + Real.log (2 * (K₀ : ℝ)) ≤ 4 * (Real.log (2 * Real.log n + 1) + 1) := by
                have hfl_le : (K₀ : ℝ) ≤ Real.log n := Nat.floor_le (by linarith)
                have h1 : Real.log (2 * (K₀ : ℝ)) ≤ Real.log (2 * Real.log n + 1) :=
                  Real.log_le_log (by positivity) (by linarith)
                linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)]
              have hmul_le : ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) *
                  (1 + Real.log (2 * (K₀ : ℝ))) ≤
                  (C₁ + 40) * 4 * (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n := by
                have hnn : 0 ≤ (C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n :=
                  div_nonneg (mul_nonneg (by positivity) (by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * Real.log n + 1)])) hlogn_pos.le
                calc ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) * (1 + Real.log (2 * (K₀ : ℝ)))
                    ≤ ((C₁ + 40) * (Real.log (2 * Real.log n + 1) + 1) / Real.log n) *
                        (4 * (Real.log (2 * Real.log n + 1) + 1)) := mul_le_mul_of_nonneg_left hlog2K hnn
                  _ = (C₁ + 40) * 4 * (Real.log (2 * Real.log n + 1) + 1) ^ 2 / Real.log n := by ring
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (le_trans hmul_le herr_bd.le) hden_pos.le
    have hTail_bd : (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) ≤
        ((n : ℝ) / Real.log n) * (ε / 4) := by
      have hsub : (Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1)) ⊆
          (Finset.Icc 2 (n / (2 * K₀ + 1))).filter Nat.Prime := by
        intro p hp
        have hp1 := Finset.mem_filter.mp hp
        have hp2 := Finset.mem_filter.mp hp1.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp2.1).1, hp1.2⟩, hp2.2.1⟩
      have hcard_le : (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) ≤
          (Nat.primeCounting (n / (2 * K₀ + 1)) : ℝ) := by
        rw [hpc_eq]
        exact_mod_cast Finset.card_le_card hsub
      have hdiv1 : Nat.sqrt n ≤ n / Nat.sqrt n :=
        (Nat.le_div_iff_mul_le (Nat.sqrt_pos.mpr (by omega))).mpr (Nat.sqrt_le n)
      have hdiv2 : n / Nat.sqrt n ≤ n / (2 * K₀ + 1) := Nat.div_le_div_left hsqrt (by omega)
      have hsq8 : 8 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
      have hm4 : 4 ≤ n / (2 * K₀ + 1) := by omega
      have hpi_m := hpi_ub (n / (2 * K₀ + 1)) hm4
      have hdiv_le : ((n / (2 * K₀ + 1) : ℕ) : ℝ) ≤ (n : ℝ) / (2 * (K₀ : ℝ) + 1) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self n (2 * K₀ + 1)
      have hm_le_n : ((n / (2 * K₀ + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n _
      have hsqrt_m : Real.sqrt ((n / (2 * K₀ + 1) : ℕ) : ℝ) ≤ Real.sqrt n := Real.sqrt_le_sqrt hm_le_n
      have hlog_m : (1 / 4 : ℝ) * Real.log n ≤ Real.log ((n / (2 * K₀ + 1) : ℕ) : ℝ) := by
        have hm_ge_sq : (Nat.sqrt n : ℝ) ≤ ((n / (2 * K₀ + 1) : ℕ) : ℝ) := by exact_mod_cast le_trans hdiv1 hdiv2
        have hsq_half : (1 / 2 : ℝ) * Real.sqrt n ≤ (Nat.sqrt n : ℝ) := by
          have hlt := Nat.lt_succ_sqrt n
          have h1 : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast hlt)
          have h2 : (8 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hsq8
          linarith
        have h1 : Real.log ((1 / 2 : ℝ) * Real.sqrt n) ≤ Real.log ((n / (2 * K₀ + 1) : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (le_trans hsq_half hm_ge_sq)
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity)] at h1
        have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
        have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        linarith
      have h_term2 : 2 * Real.log 4 * ((n / (2 * K₀ + 1) : ℕ) : ℝ) / Real.log ((n / (2 * K₀ + 1) : ℕ) : ℝ) ≤
          ((n : ℝ) / Real.log n) * (8 * Real.log 4 / (2 * (K₀ : ℝ) + 1)) := by
        have h1 : 2 * Real.log 4 * ((n / (2 * K₀ + 1) : ℕ) : ℝ) / Real.log ((n / (2 * K₀ + 1) : ℕ) : ℝ) ≤
            2 * Real.log 4 * ((n : ℝ) / (2 * (K₀ : ℝ) + 1)) / ((1 / 4 : ℝ) * Real.log n) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hdiv_le (by positivity))
            (by positivity) hlog_m
        linarith [show 2 * Real.log 4 * ((n : ℝ) / (2 * (K₀ : ℝ) + 1)) / ((1 / 4 : ℝ) * Real.log n) =
          ((n : ℝ) / Real.log n) * (8 * Real.log 4 / (2 * (K₀ : ℝ) + 1)) by ring]
      calc (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ)
          ≤ 2 * Real.sqrt n + ((n : ℝ) / Real.log n) * (8 * Real.log 4 / (2 * (K₀ : ℝ) + 1)) := by linarith
        _ = ((n : ℝ) / Real.log n) * (2 * Real.log n / Real.sqrt n + 8 * Real.log 4 / (2 * (K₀ : ℝ) + 1)) := by
            have hsn0 : Real.sqrt n ≠ 0 := (by positivity : 0 < Real.sqrt n).ne'
            field_simp [hsn0, hlogn_pos.ne']
            rw [Real.sq_sqrt hn_pos.le]
        _ ≤ ((n : ℝ) / Real.log n) * (ε / 4) := mul_le_mul_of_nonneg_left htail_bd.le hden_pos.le
    rw [Real.dist_eq, hcard_split]
    have hdiv_eq : ((∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ)) +
        (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ)) / ((n : ℝ) / Real.log n) - Real.log 2 =
        ((∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
          ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) / ((n : ℝ) / Real.log n)) +
        (∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) +
        (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) / ((n : ℝ) / Real.log n) := by
      field_simp [hden_pos.ne']
      ring
    rw [hdiv_eq]
    have h1 : |∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
        ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| / ((n : ℝ) / Real.log n) ≤ ε / 4 :=
      (div_le_iff₀ hden_pos).mpr (by linarith)
    have h2 : |∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2| < ε / 4 :=
      lt_of_le_of_lt (alternating_harmonic_sum_bound K₀) halt_bd
    have h3 : (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) / ((n : ℝ) / Real.log n) ≤ ε / 4 :=
      (div_le_iff₀ hden_pos).mpr (by linarith)
    have htri : |((∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
          ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) / ((n : ℝ) / Real.log n)) +
        (∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) +
        (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) / ((n : ℝ) / Real.log n)| ≤
        |∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
          ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| / ((n : ℝ) / Real.log n) +
        |∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2| +
        (((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) / ((n : ℝ) / Real.log n) := by
      have ha := abs_add_le
        ((∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
          ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) / ((n : ℝ) / Real.log n))
        (∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2)
      have hb := abs_add_le
        (((∑ r ∈ Finset.Icc 1 K₀, ((harmonicLayer n (2 * r - 1)).card : ℝ) -
          ((n : ℝ) / Real.log n) * ∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) / ((n : ℝ) / Real.log n)) +
          (∑ r ∈ Finset.Icc 1 K₀, ((1 : ℝ) / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2))
        ((((Podd n).filter (fun p => p ≤ n / (2 * K₀ + 1))).card : ℝ) / ((n : ℝ) / Real.log n))
      rw [abs_div, abs_of_pos hden_pos] at ha
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hden_pos.le)] at hb
      linarith
    linarith
  have h_quot := h_podd_lim.div h_pi_lim one_ne_zero
  simp only [div_one] at h_quot
  refine h_quot.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hpc_pos : (Nat.primeCounting n : ℝ) ≠ 0 := by
    have : 1 ≤ Nat.primeCounting n := by
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      exact Finset.card_pos.mpr ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
    exact_mod_cast (by omega : Nat.primeCounting n ≠ 0)
  have hlog_ne : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  have hden_ne : (n : ℝ) / Real.log n ≠ 0 := div_ne_zero (by positivity) hlog_ne
  field_simp [hpc_pos, hden_ne]

end BrocardFormalization

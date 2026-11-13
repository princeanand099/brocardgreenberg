/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxiomsAnalytic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential Sum Bounds — Part 1: Partial Summation, Vaughan's Identity & Derivative Bounds

This module proves partial summation, Vaughan's identity, and derivative estimates for
Laurent-polynomial phases `F(t) = ∑_{r ∈ A} c_r t^{-r}`.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

lemma contDiffOn_Icc_abs_deriv_intervalIntegrable {a b : ℝ} {w : ℝ → ℝ}
    (hab : a < b) (hw : ContDiffOn ℝ 1 w (Set.Icc a b)) :
    IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume a b := by
  have h_deriv_eq : ∀ t ∈ Set.Ioo a b, deriv w t = derivWithin w (Set.Icc a b) t := fun t ht =>
    (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
  have h_deriv_cont : ContinuousOn (derivWithin w (Set.Icc a b)) (Set.Icc a b) :=
    hw.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hint_within : IntervalIntegrable (fun t => |derivWithin w (Set.Icc a b) t|)
      MeasureTheory.volume a b :=
    (h_deriv_cont.abs).intervalIntegrable_of_Icc hab.le
  have hae : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      |derivWithin w (Set.Icc a b) t| = |deriv w t| := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    have hne_pt : ∀ᵐ t ∂MeasureTheory.volume, t ≠ b := by
      rw [MeasureTheory.ae_iff]
      simp only [Classical.not_not, Set.setOf_eq_eq_singleton, MeasureTheory.measure_singleton]
    filter_upwards [hne_pt] with t ht_ne ht_mem
    rw [Set.uIoc_of_le hab.le] at ht_mem
    rw [h_deriv_eq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩]
  have hmp := intervalIntegrable_iff.mp hint_within
  exact intervalIntegrable_iff.mpr ⟨hmp.1.congr hae, hmp.2.congr hae⟩

/-- Partial summation on `[a, b] ⊆ [P, 2P]` for a `C¹` weight `w` with total variation `≤ W₀`. -/
lemma partial_summation_Icc {P a b W₀ E : ℝ} {w : ℝ → ℝ} {f : ℕ → ℂ}
    (hP : 0 < P) (hPa : P ≤ a) (hab : a ≤ b) (hb2P : b ≤ 2 * P)
    (hW₀ : 0 ≤ W₀) (hE : 0 ≤ E)
    (hw_bd : ∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀)
    (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (hsum_bd : ∀ u : ℕ, ⌈a⌉₊ ≤ u → u ≤ ⌊b⌋₊ →
      ‖∑ m ∈ Finset.Icc ⌈a⌉₊ u, f m‖ ≤ E) :
    ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, (w m : ℂ) * f m‖ ≤ 2 * W₀ * E := by
  by_cases h_empty : ⌊b⌋₊ < ⌈a⌉₊
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.sum_empty, norm_zero]
    positivity
  · have h_le : ⌈a⌉₊ ≤ ⌊b⌋₊ := not_lt.mp h_empty
    set A₀ : ℕ := ⌈a⌉₊
    set B₀ : ℕ := ⌊b⌋₊
    let S : ℕ → ℂ := fun k => ∑ m ∈ Finset.Icc A₀ k, f m
    have hS_bd : ∀ k : ℕ, A₀ ≤ k → k ≤ B₀ → ‖S k‖ ≤ E := hsum_bd
    have h_abel : ∑ m ∈ Finset.Icc A₀ B₀, (w m : ℂ) * f m =
        (w B₀ : ℂ) * S B₀ -
          ∑ m ∈ Finset.Ico A₀ B₀, ((w (m + 1 : ℕ) : ℂ) - (w m : ℂ)) * S m := by
      have hf_eq : ∀ m : ℕ, A₀ ≤ m → f m = S m - (if m = A₀ then 0 else S (m - 1)) := by
        intro m hm
        by_cases hmA : m = A₀
        · subst hmA; simp [S]
        · simp only [hmA, ↓reduceIte, S]
          rw [show Finset.Icc A₀ m = insert m (Finset.Icc A₀ (m - 1)) by
            ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
          rw [Finset.sum_insert (by simp; omega)]
          ring
      have h1 : ∑ m ∈ Finset.Icc A₀ B₀, (w m : ℂ) * f m =
          ∑ m ∈ Finset.Icc A₀ B₀, (w m : ℂ) * S m -
          ∑ m ∈ Finset.Icc A₀ B₀, (w m : ℂ) * (if m = A₀ then 0 else S (m - 1)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hf_eq m (Finset.mem_Icc.mp hm).1]; ring
      rw [h1]
      have hshift : ∑ m ∈ Finset.Icc A₀ B₀, (w m : ℂ) * (if m = A₀ then 0 else S (m - 1)) =
          ∑ m ∈ Finset.Ico A₀ B₀, (w (m + 1 : ℕ) : ℂ) * S m := by
        have hIcc : Finset.Icc A₀ B₀ = insert A₀ (Finset.Icc (A₀ + 1) B₀) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), if_pos rfl, mul_zero, zero_add]
        refine Finset.sum_nbij' (fun m => m - 1) (fun m => m + 1) ?_ ?_ ?_ ?_ ?_
        · intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.mem_Ico]; omega
        · intro m hm; rw [Finset.mem_Ico] at hm; rw [Finset.mem_Icc]; omega
        · intro m hm; rw [Finset.mem_Icc] at hm; omega
        · intro m _; omega
        · intro m hm
          rw [Finset.mem_Icc] at hm
          have hne : m ≠ A₀ := by omega
          simp [hne, show m - 1 + 1 = m by omega]
      have hIcc_top : Finset.Icc A₀ B₀ = insert B₀ (Finset.Ico A₀ B₀) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hshift, hIcc_top, Finset.sum_insert (by simp)]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [h_abel]
    have hA₀_ge : P ≤ (A₀ : ℝ) := le_trans hPa (Nat.le_ceil a)
    have hB₀_le : (B₀ : ℝ) ≤ 2 * P := le_trans (Nat.floor_le (by linarith)) hb2P
    have hB₀_mem : (B₀ : ℝ) ∈ Set.Icc P (2 * P) := by
      have hA₀_le_B₀ : (A₀ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast h_le
      exact ⟨le_trans hA₀_ge hA₀_le_B₀, hB₀_le⟩
    have hterm1 : ‖(w B₀ : ℂ) * S B₀‖ ≤ W₀ * E := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hw_bd B₀ hB₀_mem) (hS_bd B₀ h_le le_rfl) (norm_nonneg _) hW₀
    have h_deriv_eq : ∀ t ∈ Set.Ioo P (2 * P),
        deriv w t = derivWithin w (Set.Icc P (2 * P)) t := by
      intro t ht
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    have h_deriv_cont : ContinuousOn (derivWithin w (Set.Icc P (2 * P))) (Set.Icc P (2 * P)) :=
      hw_diff.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl
    have h_tv_step : ∀ m ∈ Finset.Ico A₀ B₀,
        ‖(w (m + 1 : ℕ) : ℂ) - (w m : ℂ)‖ ≤ ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), |deriv w t| := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hm_ge : P ≤ (m : ℝ) := le_trans hA₀_ge (by exact_mod_cast hm.1)
      have hm1_le : ((m + 1 : ℕ) : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hm.2) hB₀_le
      have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
      have hsub : Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc P (2 * P) := fun t ht =>
        ⟨le_trans hm_ge ht.1, le_trans ht.2 hm1_le⟩
      have hcont : ContinuousOn w (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :=
        hw_diff.continuousOn.mono hsub
      have hderiv : ∀ t ∈ Set.Ioo (m : ℝ) ((m + 1 : ℕ) : ℝ), HasDerivAt w (deriv w t) t := by
        intro t ht
        have hmem : t ∈ Set.Ioo P (2 * P) := ⟨lt_of_le_of_lt hm_ge ht.1, lt_of_lt_of_le ht.2 hm1_le⟩
        have hdiff_within := hw_diff.differentiableOn one_ne_zero t (Set.Ioo_subset_Icc_self hmem)
        exact (hdiff_within.differentiableAt (Icc_mem_nhds hmem.1 hmem.2)).hasDerivAt
      have hint_within : IntervalIntegrable (derivWithin w (Set.Icc P (2 * P)))
          MeasureTheory.volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
        (h_deriv_cont.mono hsub).intervalIntegrable_of_Icc hm_le
      have hae_sub : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc (m : ℝ) ((m + 1 : ℕ) : ℝ)),
          derivWithin w (Set.Icc P (2 * P)) t = deriv w t := by
        refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
        have hne_pt : ∀ᵐ t ∂MeasureTheory.volume, t ≠ ((m + 1 : ℕ) : ℝ) := by
          rw [MeasureTheory.ae_iff]
          simp only [Classical.not_not, Set.setOf_eq_eq_singleton, MeasureTheory.measure_singleton]
        filter_upwards [hne_pt] with t ht_ne ht_mem
        rw [Set.uIoc_of_le hm_le] at ht_mem
        have ht_lt : t < ((m + 1 : ℕ) : ℝ) := lt_of_le_of_ne ht_mem.2 ht_ne
        exact (h_deriv_eq t ⟨lt_of_le_of_lt hm_ge ht_mem.1, lt_of_lt_of_le ht_lt hm1_le⟩).symm
      have hmp := intervalIntegrable_iff.mp hint_within
      have hint : IntervalIntegrable (deriv w) MeasureTheory.volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
        intervalIntegrable_iff.mpr ⟨hmp.1.congr hae_sub, hmp.2.congr hae_sub⟩
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hm_le hcont hderiv hint
      rw [show (w (m + 1 : ℕ) : ℂ) - (w m : ℂ) = ((w (m + 1 : ℕ) - w m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, ← hftc]
      exact intervalIntegral.abs_integral_le_integral_abs hm_le
    have h_tv_abs_int : IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume P (2 * P) :=
      contDiffOn_Icc_abs_deriv_intervalIntegrable (by linarith) hw_diff
    have h_tv_sum : ∑ m ∈ Finset.Ico A₀ B₀, ‖(w (m + 1 : ℕ) : ℂ) - (w m : ℂ)‖ ≤ W₀ := by
      refine le_trans (Finset.sum_le_sum h_tv_step) ?_
      have h_adj : ∀ k : ℕ, A₀ ≤ k → k ≤ B₀ →
          ∑ m ∈ Finset.Ico A₀ k, ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), |deriv w t| =
            ∫ t in (A₀ : ℝ)..(k : ℝ), |deriv w t| := by
        intro k hkA hkB
        induction k with
        | zero =>
          have hA0 : A₀ = 0 := by omega
          subst hA0; simp
        | succ k ih =>
          by_cases hk : A₀ ≤ k
          · rw [Finset.sum_Ico_succ_top hk, ih hk (by omega)]
            have h1 : IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume (A₀ : ℝ) (k : ℝ) :=
              h_tv_abs_int.mono_set (by
                rw [Set.uIcc_of_le (by exact_mod_cast hk), Set.uIcc_of_le (by linarith)]
                have hk_le : (k : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast (by omega : k ≤ B₀)) hB₀_le
                exact fun t ht => ⟨le_trans hA₀_ge ht.1, le_trans ht.2 hk_le⟩)
            have h2 : IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
              h_tv_abs_int.mono_set (by
                rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ k), Set.uIcc_of_le (by linarith)]
                have hk_ge : P ≤ (k : ℝ) := le_trans hA₀_ge (by exact_mod_cast hk)
                have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hkB) hB₀_le
                exact fun t ht => ⟨le_trans hk_ge ht.1, le_trans ht.2 hk1_le⟩)
            exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
          · have hA_eq : A₀ = k + 1 := by omega
            subst hA_eq; simp
      rw [h_adj B₀ h_le le_rfl]
      refine le_trans (intervalIntegral.integral_mono_interval hA₀_ge (by exact_mod_cast h_le)
        hB₀_le (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_tv_abs_int) hw_tv
    have hterm2 : ‖∑ m ∈ Finset.Ico A₀ B₀, ((w (m + 1 : ℕ) : ℂ) - (w m : ℂ)) * S m‖ ≤ W₀ * E := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ Finset.Ico A₀ B₀, ‖((w (m + 1 : ℕ) : ℂ) - (w m : ℂ)) * S m‖
          = ∑ m ∈ Finset.Ico A₀ B₀, ‖(w (m + 1 : ℕ) : ℂ) - (w m : ℂ)‖ * ‖S m‖ := by
            refine Finset.sum_congr rfl fun m _ => norm_mul _ _
        _ ≤ ∑ m ∈ Finset.Ico A₀ B₀, ‖(w (m + 1 : ℕ) : ℂ) - (w m : ℂ)‖ * E := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [Finset.mem_Ico] at hm
            exact mul_le_mul_of_nonneg_left (hS_bd m hm.1 hm.2.le) (norm_nonneg _)
        _ = (∑ m ∈ Finset.Ico A₀ B₀, ‖(w (m + 1 : ℕ) : ℂ) - (w m : ℂ)‖) * E := (Finset.sum_mul _ _ _).symm
        _ ≤ W₀ * E := mul_le_mul_of_nonneg_right h_tv_sum hE
    calc ‖(w B₀ : ℂ) * S B₀ - ∑ m ∈ Finset.Ico A₀ B₀, ((w (m + 1 : ℕ) : ℂ) - (w m : ℂ)) * S m‖
        ≤ ‖(w B₀ : ℂ) * S B₀‖ + ‖∑ m ∈ Finset.Ico A₀ B₀, ((w (m + 1 : ℕ) : ℂ) - (w m : ℂ)) * S m‖ :=
          norm_sub_le _ _
      _ ≤ W₀ * E + W₀ * E := add_le_add hterm1 hterm2
      _ = 2 * W₀ * E := by ring


/-! ### Vaughan's Identity and Prime-Power Tail -/

lemma sum_vonMangoldt_sub_prime_log_le {A₀ B₀ : ℕ} (hA : 1 ≤ A₀) (hB : 4 ≤ B₀) {g : ℕ → ℂ}
    (hg : ∀ m, ‖g m‖ ≤ 1) :
    ‖∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m -
      ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (Real.log p : ℂ) * g p‖ ≤
      2 * Real.sqrt B₀ * (Real.log B₀) ^ 2 := by
  have hsplit : ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m -
      ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (Real.log p : ℂ) * g p =
      ∑ m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m),
        (ArithmeticFunction.vonMangoldt m : ℂ) * g m := by
    have hsum1 : ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m =
        ∑ m ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (ArithmeticFunction.vonMangoldt m : ℂ) * g m +
        ∑ m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime),
          (ArithmeticFunction.vonMangoldt m : ℂ) * g m :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hp_eq : ∑ m ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (ArithmeticFunction.vonMangoldt m : ℂ) * g m =
        ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (Real.log p : ℂ) * g p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    have hnp_eq : ∑ m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime),
          (ArithmeticFunction.vonMangoldt m : ℂ) * g m =
        ∑ m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m),
          (ArithmeticFunction.vonMangoldt m : ℂ) * g m := by
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime))
        IsPrimePow]
      have h0 : ∑ m ∈ ((Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime)).filter (fun m => ¬ IsPrimePow m),
          (ArithmeticFunction.vonMangoldt m : ℂ) * g m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hnp : ¬ IsPrimePow m := (Finset.mem_filter.mp hm).2
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp]; simp
      rw [h0, add_zero, Finset.filter_filter]
    rw [hsum1, hp_eq, hnp_eq]; ring
  rw [hsplit]
  let S_pp := (Finset.Icc 2 (Nat.sqrt B₀)) ×ˢ (Finset.Icc 2 (Nat.log 2 B₀ + 1))
  have hsub : (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m) ⊆
      S_pp.image (fun pk => pk.1 ^ pk.2) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rcases hm with ⟨⟨hmA, hmB⟩, hm_np, p, k, hp_pr, hk_pos, rfl⟩
    have hp_nat : p.Prime := Nat.prime_iff.mpr hp_pr
    have hk2 : 2 ≤ k := by
      by_contra hk1
      have : k = 1 := by omega
      subst this; simp at hm_np; exact hm_np hp_nat
    have hp_sq : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp_nat.pos hk2
    have hp_le_sqrt : p ≤ Nat.sqrt B₀ := Nat.le_sqrt.mpr (by nlinarith [le_trans hp_sq hmB])
    have hk_le_log : k ≤ Nat.log 2 B₀ := by
      have h2k : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp_nat.two_le k
      exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (le_trans h2k hmB)
    exact Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp_nat.two_le, hp_le_sqrt⟩, Finset.mem_Icc.mpr ⟨hk2, by omega⟩⟩, rfl⟩
  have hcard_le : ((Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m)).card ≤
      Nat.sqrt B₀ * Nat.log 2 B₀ := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
    rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
    have : Nat.sqrt B₀ + 1 - 2 ≤ Nat.sqrt B₀ := by omega
    have : Nat.log 2 B₀ + 1 + 1 - 2 = Nat.log 2 B₀ := by omega
    exact Nat.mul_le_mul (by omega) (by omega)
  have hterm_le : ∀ m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m),
      ‖(ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ ≤ Real.log B₀ := by
    intro m hm
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hm_le : m ≤ B₀ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have hm_pos : 0 < m := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega
    have hvm : ArithmeticFunction.vonMangoldt m ≤ Real.log m := ArithmeticFunction.vonMangoldt_le_log
    have hlog_le : Real.log m ≤ Real.log B₀ := Real.log_le_log (by exact_mod_cast hm_pos) (by exact_mod_cast hm_le)
    calc ArithmeticFunction.vonMangoldt m * ‖g m‖
        ≤ ArithmeticFunction.vonMangoldt m * 1 := mul_le_mul_of_nonneg_left (hg m) ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ Real.log B₀ := by linarith
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m),
          ‖(ArithmeticFunction.vonMangoldt m : ℂ) * g m‖
      ≤ ∑ _m ∈ (Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m), Real.log B₀ :=
        Finset.sum_le_sum hterm_le
    _ = (((Finset.Icc A₀ B₀).filter (fun m => ¬ m.Prime ∧ IsPrimePow m)).card : ℝ) * Real.log B₀ := by
        simp
    _ ≤ (Nat.sqrt B₀ * Nat.log 2 B₀ : ℝ) * Real.log B₀ := by
        refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le)
          (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B₀)))
    _ ≤ 2 * Real.sqrt B₀ * (Real.log B₀) ^ 2 := by
        have hsqrt_le : (Nat.sqrt B₀ : ℝ) ≤ Real.sqrt B₀ :=
          Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le B₀))
        have hlog2_le : (Nat.log 2 B₀ : ℝ) ≤ 2 * Real.log B₀ := by
          have hpow : (2 : ℝ) ^ (Nat.log 2 B₀) ≤ (B₀ : ℝ) := by
            exact_mod_cast Nat.pow_log_le_self 2 (by omega : B₀ ≠ 0)
          have h1 := Real.log_le_log (by positivity) hpow
          rw [Real.log_pow] at h1
          have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          nlinarith
        have hlogB_nn : 0 ≤ Real.log B₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B₀))
        calc (Nat.sqrt B₀ : ℝ) * (Nat.log 2 B₀ : ℝ) * Real.log B₀
            ≤ Real.sqrt B₀ * (2 * Real.log B₀) * Real.log B₀ := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul hsqrt_le hlog2_le (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hlogB_nn
          _ = 2 * Real.sqrt B₀ * (Real.log B₀) ^ 2 := by ring

lemma div_succ_le_iff_le_mul {A d k : ℕ} (hA : 1 ≤ A) (hd : 1 ≤ d) :
    (A - 1) / d + 1 ≤ k ↔ A ≤ d * k := by
  rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hd, mul_comm]
  omega

lemma sum_Icc_divisors_filter {A₀ B₀ L U : ℕ} (hA : 1 ≤ A₀) (hL : 1 ≤ L)
    (F : ℕ → ℕ → ℂ) :
    ∑ m ∈ Finset.Icc A₀ B₀, ∑ d ∈ m.divisors.filter (fun d => L ≤ d ∧ d ≤ U), F d (m / d) =
      ∑ d ∈ Finset.Icc L U, ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), F d k := by
  have h1 : ∀ m ∈ Finset.Icc A₀ B₀,
      ∑ d ∈ m.divisors.filter (fun d => L ≤ d ∧ d ≤ U), F d (m / d) =
      ∑ d ∈ Finset.Icc L U, if d ∣ m then F d (m / d) else 0 := by
    intro m hm
    have hm_pos : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc, hm_pos, not_false_eq_true, and_true]
    tauto
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : 1 ≤ d := le_trans hL (Finset.mem_Icc.mp hd).1
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun m => m / d) (fun k => d * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rcases hm with ⟨⟨hmA, hmB⟩, hd_dvd⟩
    have hmul : d * (m / d) = m := Nat.mul_div_cancel' hd_dvd
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨(div_succ_le_iff_le_mul hA hd_pos).mpr (by omega),
      (Nat.le_div_iff_mul_le hd_pos).mpr (by omega)⟩
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hA_dk : A₀ ≤ d * k := (div_succ_le_iff_le_mul hA hd_pos).mp hk.1
    have hdk_B : d * k ≤ B₀ := (Nat.le_div_iff_mul_le hd_pos).mp (by simpa [mul_comm] using hk.2)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hA_dk, hdk_B⟩, dvd_mul_right d k⟩
  · intro m hm
    rw [Finset.mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro k _
    exact Nat.mul_div_cancel_left k hd_pos
  · intro _ _; rfl

lemma vaughan_identity (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) {A₀ B₀ : ℕ} (hA : 1 ≤ A₀)
    (g : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m =
      ∑ m ∈ (Finset.Icc A₀ B₀).filter (· ≤ V), (ArithmeticFunction.vonMangoldt m : ℂ) * g m +
      ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), (Real.log k : ℂ) * g (d * k) -
      ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ Finset.Icc 1 V, (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ m ∈ Finset.Icc ((A₀ - 1) / (d * k) + 1) (B₀ / (d * k)), g (d * k * m) +
      ∑ k ∈ Finset.Icc (V + 1) (B₀ / U), (ArithmeticFunction.vonMangoldt k : ℂ) *
        ∑ r ∈ Finset.Icc (max (U + 1) ((A₀ - 1) / k + 1)) (B₀ / k),
          (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) := by
  have hpt : ∀ m : ℕ, 1 ≤ m →
      (ArithmeticFunction.vonMangoldt m : ℂ) =
      (if m ≤ V then (ArithmeticFunction.vonMangoldt m : ℂ) else 0) +
      ∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) -
      ∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ (m / d).divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) +
      ∑ k ∈ m.divisors.filter (V < ·), (ArithmeticFunction.vonMangoldt k : ℂ) *
        (if U < m / k then -∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) else 0) := by
    intro m hm
    have hlog_sum : ∀ n : ℕ, 1 ≤ n →
        (Real.log (n : ℝ) : ℂ) = ∑ k ∈ n.divisors, (ArithmeticFunction.vonMangoldt k : ℂ) := by
      intro n _
      have h := ArithmeticFunction.vonMangoldt_sum (n := n)
      exact_mod_cast h.symm
    have hmoeb_sum : ∀ n : ℕ, 1 ≤ n →
        (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
      intro n hn
      have h := congr_arg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
      have hsum : (∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) *
          (ArithmeticFunction.zeta x.2 : ℤ)) = ∑ d ∈ n.divisors, ArithmeticFunction.moebius d := by
        rw [Nat.sum_divisorsAntidiagonal']
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hnd_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) hd_pos
        simp [ArithmeticFunction.zeta_apply, hnd_pos.ne']
      rw [hsum] at h
      exact_mod_cast h
    have hswap : ∀ (f : ℕ → ℕ → ℂ),
        ∑ d ∈ m.divisors, ∑ k ∈ (m / d).divisors, f d k =
        ∑ k ∈ m.divisors, ∑ d ∈ (m / k).divisors, f d k := by
      intro f
      have hinner : ∀ a ∈ m.divisors, ∀ (g0 : ℕ → ℂ),
          ∑ b ∈ (m / a).divisors, g0 b =
          ∑ b ∈ m.divisors, if a * b ∣ m then g0 b else 0 := by
        intro a ha g0
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext b
        simp only [Finset.mem_filter, Nat.mem_divisors]
        have ha_dvd : a ∣ m := (Nat.mem_divisors.mp ha).1
        have ha_pos : 0 < a := Nat.pos_of_mem_divisors ha
        have hma_ne : m / a ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) ha_dvd) ha_pos).ne'
        constructor
        · rintro ⟨hb_dvd, _⟩
          have hab_dvd : a * b ∣ m := Nat.mul_dvd_of_dvd_div ha_dvd hb_dvd
          exact ⟨⟨dvd_trans (dvd_mul_left b a) hab_dvd, by omega⟩, hab_dvd⟩
        · rintro ⟨_, hab_dvd⟩
          exact ⟨Nat.dvd_div_of_mul_dvd hab_dvd, hma_ne⟩
      have hL : ∑ d ∈ m.divisors, ∑ k ∈ (m / d).divisors, f d k =
          ∑ d ∈ m.divisors, ∑ k ∈ m.divisors, if d * k ∣ m then f d k else 0 :=
        Finset.sum_congr rfl fun d hd => hinner d hd (fun k => f d k)
      have hR : ∑ k ∈ m.divisors, ∑ d ∈ (m / k).divisors, f d k =
          ∑ k ∈ m.divisors, ∑ d ∈ m.divisors, if d * k ∣ m then f d k else 0 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hinner k hk (fun d => f d k)]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [mul_comm]
      rw [hL, hR, Finset.sum_comm]
    have htotal : (ArithmeticFunction.vonMangoldt m : ℂ) =
        ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) := by
      have h1 : ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) =
          ∑ d ∈ m.divisors, ∑ k ∈ (m / d).divisors,
            (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hmd_pos : 1 ≤ m / d := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) hd_pos
        rw [hlog_sum (m / d) hmd_pos, Finset.mul_sum]
      rw [h1, hswap]
      have h2 : ∑ k ∈ m.divisors, ∑ d ∈ (m / k).divisors,
            (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) =
          (ArithmeticFunction.vonMangoldt m : ℂ) := by
        have h3 : ∀ k ∈ m.divisors,
            ∑ d ∈ (m / k).divisors, (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) =
            if k = m then (ArithmeticFunction.vonMangoldt m : ℂ) else 0 := by
          intro k hk
          rw [← Finset.sum_mul]
          have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
          have hk_le : k ≤ m := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hk)
          have hmk_pos : 1 ≤ m / k := Nat.div_pos hk_le hk_pos
          rw [hmoeb_sum (m / k) hmk_pos]
          by_cases hkm : k = m
          · subst hkm; simp [Nat.div_self hk_pos]
          · have hmk_gt : 1 < m / k := by
              have hdvd := Nat.dvd_of_mem_divisors hk
              rcases hdvd with ⟨q, hq⟩
              have hq1 : q ≠ 1 := fun h1 => hkm (by rw [hq, h1, mul_one])
              have hq0 : 0 < q := by
                by_contra h0; simp only [not_lt, Nat.le_zero] at h0; rw [hq, h0, mul_zero] at hm; omega
              rw [hq, Nat.mul_div_cancel_left q hk_pos]; omega
            simp [hkm, hmk_gt.ne']
        rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq']
        have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
        simp [hm_mem]
      exact h2.symm
    have hsplit_d : ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) =
        ∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) +
        ∑ d ∈ m.divisors.filter (U < ·), ∑ k ∈ (m / d).divisors,
          (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) := by
      rw [← Finset.sum_filter_add_sum_filter_not m.divisors (· ≤ U)]
      congr 1
      refine Finset.sum_congr (by ext d; simp [not_le]) fun d hd => ?_
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
      have hmd_pos : 1 ≤ m / d := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)) hd_pos
      rw [hlog_sum (m / d) hmd_pos, Finset.mul_sum]
    have htail_d : ∑ d ∈ m.divisors.filter (U < ·), ∑ k ∈ (m / d).divisors,
          (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) =
        ∑ k ∈ m.divisors, (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) := by
      have h1 : ∑ d ∈ m.divisors.filter (U < ·), ∑ k ∈ (m / d).divisors,
            (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) =
          ∑ d ∈ m.divisors, ∑ k ∈ (m / d).divisors,
            (if U < d then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) := by
        rw [← Finset.sum_filter_add_sum_filter_not m.divisors (U < ·)]
        have h0 : ∑ d ∈ m.divisors.filter (fun x => ¬ U < x), ∑ k ∈ (m / d).divisors,
            (if U < d then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) = 0 :=
          Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun k _ => by
            have hnot : ¬ U < d := (Finset.mem_filter.mp hd).2
            simp [hnot]
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun k _ => ?_
        have hlt : U < d := (Finset.mem_filter.mp hd).2
        simp [hlt]
      rw [h1, hswap]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_filter_add_sum_filter_not (m / k).divisors (U < ·)]
      simp only [Finset.mul_sum]
      have h0 : ∑ d ∈ (m / k).divisors.filter (fun x => ¬ U < x),
          (if U < d then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) = 0 :=
        Finset.sum_eq_zero fun d hd => by
          have hnot : ¬ U < d := (Finset.mem_filter.mp hd).2
          simp [hnot]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hlt : U < d := (Finset.mem_filter.mp hd).2
      simp [hlt, mul_comm]
    have hV_le : ∑ k ∈ m.divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) =
        (if m ≤ V then (ArithmeticFunction.vonMangoldt m : ℂ) else 0) -
        ∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) *
          ∑ k ∈ (m / d).divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) := by
      have h_inner : ∀ k ∈ m.divisors.filter (· ≤ V),
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) =
          (if k = m then (1 : ℂ) else 0) -
            ∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) := by
        intro k hk
        have hk_pos : 0 < k := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hk).1
        have hmk_pos : 1 ≤ m / k := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1)) hk_pos
        have hsum_all := hmoeb_sum (m / k) hmk_pos
        rw [← Finset.sum_filter_add_sum_filter_not (m / k).divisors (· ≤ U)] at hsum_all
        have hflt : (m / k).divisors.filter (fun x => ¬ x ≤ U) = (m / k).divisors.filter (U < ·) := by
          ext x; simp [not_le]
        rw [hflt] at hsum_all
        have hkm_iff : m / k = 1 ↔ k = m := by
          have hdvd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1
          rcases hdvd with ⟨q, hq⟩
          constructor
          · intro h1
            have hq1 : q = 1 := by rw [hq, Nat.mul_div_cancel_left q hk_pos] at h1; exact h1
            rw [hq, hq1, mul_one]
          · intro hkm
            subst hkm
            exact Nat.div_self hk_pos
        rw [if_congr hkm_iff rfl rfl] at hsum_all
        exact eq_sub_of_add_eq' hsum_all
      rw [Finset.sum_congr rfl h_inner]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · by_cases hmV : m ≤ V
        · simp only [hmV, ↓reduceIte]
          have hm_mem : m ∈ m.divisors.filter (· ≤ V) :=
            Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, hmV⟩
          rw [Finset.sum_eq_single m (fun k _ hkm => by simp [hkm]) (fun h => absurd hm_mem h)]
          simp
        · simp only [hmV, ↓reduceIte]
          refine Finset.sum_eq_zero fun k hk => ?_
          have hkV : k ≤ V := (Finset.mem_filter.mp hk).2
          have hkm : k ≠ m := fun h => hmV (h ▸ hkV)
          simp [hkm]
      · have h1 : ∑ k ∈ m.divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) *
              ∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) =
            ∑ k ∈ m.divisors, ∑ d ∈ (m / k).divisors,
              (if k ≤ V ∧ d ≤ U then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) := by
          rw [← Finset.sum_filter_add_sum_filter_not m.divisors (· ≤ V)]
          have h0 : ∑ k ∈ m.divisors.filter (fun x => ¬ x ≤ V), ∑ d ∈ (m / k).divisors,
              (if k ≤ V ∧ d ≤ U then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) = 0 :=
            Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun d _ => by
              have hnot : ¬ k ≤ V := (Finset.mem_filter.mp hk).2
              simp [hnot]
          rw [h0, add_zero]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (m / k).divisors (· ≤ U)]
          have h0' : ∑ d ∈ (m / k).divisors.filter (fun x => ¬ x ≤ U),
              (if k ≤ V ∧ d ≤ U then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) = 0 :=
            Finset.sum_eq_zero fun d hd => by
              have hnot : ¬ d ≤ U := (Finset.mem_filter.mp hd).2
              simp [hnot]
          rw [h0', add_zero]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hkV : k ≤ V := (Finset.mem_filter.mp hk).2
          have hdU : d ≤ U := (Finset.mem_filter.mp hd).2
          simp [hkV, hdU, mul_comm]
        rw [h1, ← hswap]
        rw [← Finset.sum_filter_add_sum_filter_not m.divisors (· ≤ U)]
        have h0 : ∑ d ∈ m.divisors.filter (fun x => ¬ x ≤ U), ∑ k ∈ (m / d).divisors,
            (if k ≤ V ∧ d ≤ U then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) = 0 :=
          Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun k _ => by
            have hnot : ¬ d ≤ U := (Finset.mem_filter.mp hd).2
            simp [hnot]
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (m / d).divisors (· ≤ V)]
        have h0' : ∑ k ∈ (m / d).divisors.filter (fun x => ¬ x ≤ V),
            (if k ≤ V ∧ d ≤ U then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) else 0) = 0 :=
          Finset.sum_eq_zero fun k hk => by
            have hnot : ¬ k ≤ V := (Finset.mem_filter.mp hk).2
            simp [hnot]
        rw [h0', add_zero]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkV : k ≤ V := (Finset.mem_filter.mp hk).2
        have hdU : d ≤ U := (Finset.mem_filter.mp hd).2
        simp [hkV, hdU]
    have hV_gt : ∑ k ∈ m.divisors.filter (fun x => ¬ x ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) =
        ∑ k ∈ m.divisors.filter (V < ·), (ArithmeticFunction.vonMangoldt k : ℂ) *
          (if U < m / k then -∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) else 0) := by
      have hflt : m.divisors.filter (fun x => ¬ x ≤ V) = m.divisors.filter (V < ·) := by
        ext x; simp [not_le]
      rw [hflt]
      refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      by_cases hU_mk : U < m / k
      · simp only [hU_mk, ↓reduceIte]
        have hmk_gt1 : 1 < m / k := lt_of_le_of_lt hU hU_mk
        have hsum_all := hmoeb_sum (m / k) (le_of_lt hmk_gt1)
        have hmk_ne1 : m / k ≠ 1 := hmk_gt1.ne'
        simp only [hmk_ne1, ↓reduceIte] at hsum_all
        rw [← Finset.sum_filter_add_sum_filter_not (m / k).divisors (· ≤ U)] at hsum_all
        have hflt2 : (m / k).divisors.filter (fun x => ¬ x ≤ U) = (m / k).divisors.filter (U < ·) := by
          ext x; simp [not_le]
        rw [hflt2] at hsum_all
        exact eq_neg_of_add_eq_zero_right hsum_all
      · simp only [hU_mk, ↓reduceIte]
        refine Finset.sum_eq_zero fun d hd => ?_
        have hd_gt : U < d := (Finset.mem_filter.mp hd).2
        have hmk_pos : 0 < m / k := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1))
          (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hk).1)
        have hd_le : d ≤ m / k := Nat.le_of_dvd hmk_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
        exact absurd (lt_of_lt_of_le hd_gt hd_le) hU_mk
    have htail_split : ∑ k ∈ m.divisors, (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) =
        ∑ k ∈ m.divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) +
        ∑ k ∈ m.divisors.filter (fun x => ¬ x ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ d ∈ (m / k).divisors.filter (U < ·), (ArithmeticFunction.moebius d : ℂ) :=
      (Finset.sum_filter_add_sum_filter_not m.divisors (· ≤ V) _).symm
    linear_combination htotal + hsplit_d + htail_d + htail_split + hV_le + hV_gt
  have hsum_pt : ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m =
      ∑ m ∈ Finset.Icc A₀ B₀,
        ((if m ≤ V then (ArithmeticFunction.vonMangoldt m : ℂ) * g m else 0) +
        (∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ)) * g m -
        (∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) *
          ∑ k ∈ (m / d).divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ)) * g m +
        (∑ k ∈ m.divisors.filter (V < ·), (ArithmeticFunction.vonMangoldt k : ℂ) *
          (if U < m / k then -∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) else 0)) * g m) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have h1 := congr_arg (· * g m) (hpt m (le_trans hA (Finset.mem_Icc.mp hm).1))
    dsimp only at h1
    rw [h1]
    by_cases hmV : m ≤ V <;> simp [hmV, add_mul, sub_mul]
  have hS1 : ∑ m ∈ Finset.Icc A₀ B₀, (if m ≤ V then (ArithmeticFunction.vonMangoldt m : ℂ) * g m else 0) =
      ∑ m ∈ (Finset.Icc A₀ B₀).filter (· ≤ V), (ArithmeticFunction.vonMangoldt m : ℂ) * g m :=
    (Finset.sum_filter _ _).symm
  have hS2 : ∑ m ∈ Finset.Icc A₀ B₀,
        (∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ)) * g m =
      ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), (Real.log k : ℂ) * g (d * k) := by
    have hflt : ∀ m ∈ Finset.Icc A₀ B₀,
        (∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ)) * g m =
        ∑ d ∈ m.divisors.filter (fun d => 1 ≤ d ∧ d ≤ U),
          (ArithmeticFunction.moebius d : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) * g (d * (m / d)) := by
      intro m _
      rw [Finset.sum_mul]
      have hset : m.divisors.filter (· ≤ U) = m.divisors.filter (fun d => 1 ≤ d ∧ d ≤ U) := by
        ext d; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hd, hU⟩ => ⟨hd, Nat.pos_of_mem_divisors hd, hU⟩, fun ⟨hd, _, hU⟩ => ⟨hd, hU⟩⟩
      refine Finset.sum_congr hset fun d hd => ?_
      have hd_dvd : d ∣ m := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      rw [Nat.mul_div_cancel' hd_dvd]
    rw [Finset.sum_congr rfl hflt, sum_Icc_divisors_filter hA (by norm_num)
      (fun d k => (ArithmeticFunction.moebius d : ℂ) * (Real.log k : ℂ) * g (d * k))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  have hS3 : ∑ m ∈ Finset.Icc A₀ B₀,
        (∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) *
          ∑ k ∈ (m / d).divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ)) * g m =
      ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ Finset.Icc 1 V, (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ m ∈ Finset.Icc ((A₀ - 1) / (d * k) + 1) (B₀ / (d * k)), g (d * k * m) := by
    have hflt1 : ∀ m ∈ Finset.Icc A₀ B₀,
        (∑ d ∈ m.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) *
          ∑ k ∈ (m / d).divisors.filter (· ≤ V), (ArithmeticFunction.vonMangoldt k : ℂ)) * g m =
        ∑ d ∈ m.divisors.filter (fun d => 1 ≤ d ∧ d ≤ U),
          (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ (m / d).divisors.filter (fun k => 1 ≤ k ∧ k ≤ V),
              (ArithmeticFunction.vonMangoldt k : ℂ) * g (d * (m / d)) := by
      intro m _
      rw [Finset.sum_mul]
      have hset : m.divisors.filter (· ≤ U) = m.divisors.filter (fun d => 1 ≤ d ∧ d ≤ U) := by
        ext d; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hd, hU⟩ => ⟨hd, Nat.pos_of_mem_divisors hd, hU⟩, fun ⟨hd, _, hU⟩ => ⟨hd, hU⟩⟩
      refine Finset.sum_congr hset fun d hd => ?_
      have hd_dvd : d ∣ m := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      rw [Nat.mul_div_cancel' hd_dvd, mul_assoc, Finset.sum_mul]
      congr 1
      have hset_k : (m / d).divisors.filter (· ≤ V) = (m / d).divisors.filter (fun k => 1 ≤ k ∧ k ≤ V) := by
        ext k; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hk, hV⟩ => ⟨hk, Nat.pos_of_mem_divisors hk, hV⟩, fun ⟨hk, _, hV⟩ => ⟨hk, hV⟩⟩
      exact Finset.sum_congr hset_k fun _ _ => rfl
    rw [Finset.sum_congr rfl hflt1, sum_Icc_divisors_filter hA (by norm_num)
      (fun d q => (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ q.divisors.filter (fun k => 1 ≤ k ∧ k ≤ V),
          (ArithmeticFunction.vonMangoldt k : ℂ) * g (d * q))]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← Finset.mul_sum]
    congr 1
    have hflt2 : ∀ q ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d),
        ∑ k ∈ q.divisors.filter (fun k => 1 ≤ k ∧ k ≤ V),
          (ArithmeticFunction.vonMangoldt k : ℂ) * g (d * q) =
        ∑ k ∈ q.divisors.filter (fun k => 1 ≤ k ∧ k ≤ V),
          (ArithmeticFunction.vonMangoldt k : ℂ) * g (d * k * (q / k)) := by
      intro q _
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_dvd : k ∣ q := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1
      rw [mul_assoc, Nat.mul_div_cancel' hk_dvd]
    rw [Finset.sum_congr rfl hflt2, sum_Icc_divisors_filter (by omega) (by norm_num)
      (fun k m => (ArithmeticFunction.vonMangoldt k : ℂ) * g (d * k * m))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    congr 1
    · rw [Nat.div_div_eq_div_mul]; congr 1
      have : ((A₀ - 1) / d + 1 - 1) = (A₀ - 1) / d := by omega
      rw [this, Nat.div_div_eq_div_mul]
    · rw [Nat.div_div_eq_div_mul]
  have hS4 : ∑ m ∈ Finset.Icc A₀ B₀,
        (∑ k ∈ m.divisors.filter (V < ·), (ArithmeticFunction.vonMangoldt k : ℂ) *
          (if U < m / k then -∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) else 0)) * g m =
      ∑ k ∈ Finset.Icc (V + 1) (B₀ / U), (ArithmeticFunction.vonMangoldt k : ℂ) *
        ∑ r ∈ Finset.Icc (max (U + 1) ((A₀ - 1) / k + 1)) (B₀ / k),
          (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) := by
    have hflt3 : ∀ m ∈ Finset.Icc A₀ B₀,
        (∑ k ∈ m.divisors.filter (V < ·), (ArithmeticFunction.vonMangoldt k : ℂ) *
          (if U < m / k then -∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) else 0)) * g m =
        ∑ k ∈ m.divisors.filter (fun k => V + 1 ≤ k ∧ k ≤ B₀ / U),
          (ArithmeticFunction.vonMangoldt k : ℂ) *
            (if U + 1 ≤ m / k then
              (-∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * (m / k)) else 0) := by
      intro m hm
      have hmB : m ≤ B₀ := (Finset.mem_Icc.mp hm).2
      rw [Finset.sum_mul]
      rw [← Finset.sum_filter_add_sum_filter_not (m.divisors.filter (V < ·)) (· ≤ B₀ / U)]
      have h0 : ∑ k ∈ (m.divisors.filter (V < ·)).filter (fun k => ¬ k ≤ B₀ / U),
          ((ArithmeticFunction.vonMangoldt k : ℂ) *
            (if U < m / k then -∑ d ∈ (m / k).divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ) else 0)) * g m = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_filter, Finset.mem_filter, not_le] at hk
        have hmk : m / k ≤ U := by
          rw [Nat.div_le_iff_le_mul_add_pred (Nat.pos_of_mem_divisors hk.1.1)]
          have h1 : B₀ / U + 1 ≤ k := hk.2
          have h2 : B₀ < U * k := by
            have := Nat.lt_mul_div_succ B₀ hU
            nlinarith
          nlinarith
        have hnot : ¬ U < m / k := by omega
        simp [hnot]
      rw [h0, add_zero, Finset.filter_filter]
      refine Finset.sum_congr (by ext k; simp; omega) fun k hk => ?_
      have hk_dvd : k ∣ m := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1
      rw [Nat.mul_div_cancel' hk_dvd]
      by_cases hU_mk : U < m / k
      · have hU1 : U + 1 ≤ m / k := by omega
        simp only [hU_mk, hU1, ↓reduceIte]; ring
      · have hU1 : ¬ U + 1 ≤ m / k := by omega
        simp [hU_mk, hU1]
    rw [Finset.sum_congr rfl hflt3, sum_Icc_divisors_filter hA (by omega : 1 ≤ V + 1)
      (fun k r => (ArithmeticFunction.vonMangoldt k : ℂ) *
        (if U + 1 ≤ r then (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) else 0))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc ((A₀ - 1) / k + 1) (B₀ / k)) (U + 1 ≤ ·)]
    have h0 : ∑ r ∈ (Finset.Icc ((A₀ - 1) / k + 1) (B₀ / k)).filter (fun r => ¬ U + 1 ≤ r),
        (if U + 1 ≤ r then (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) else 0) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        have hnot : ¬ U + 1 ≤ r := (Finset.mem_filter.mp hr).2
        simp [hnot]
    rw [h0, add_zero]
    refine Finset.sum_nbij' id id ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_
    · intro r hr; rw [Finset.mem_filter, Finset.mem_Icc] at hr; rw [Finset.mem_Icc]; omega
    · intro r hr; rw [Finset.mem_Icc] at hr; rw [Finset.mem_filter, Finset.mem_Icc]; omega
    · intro r hr
      have hle : U + 1 ≤ r := (Finset.mem_filter.mp hr).2
      simp [hle]
  rw [hsum_pt, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hS1, hS2, hS3, hS4]


/-! ### Derivative Estimates for Laurent Phase Functions -/

lemma iteratedDeriv_zpow_neg (r : ℕ) (hr : 1 ≤ r) (k : ℕ) :
    ∀ t : ℝ, 0 < t →
      iteratedDeriv k (fun u : ℝ => u ^ (-(r : ℤ))) t =
        (-1 : ℝ) ^ k * (Nat.descFactorial (r + k - 1) k : ℝ) * t ^ (-(r + k : ℤ)) := by
  induction k with
  | zero =>
    intro t _
    simp
  | succ k ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have heq : Set.EqOn (iteratedDeriv k (fun u : ℝ => u ^ (-(r : ℤ))))
        (fun u : ℝ => (-1 : ℝ) ^ k * (Nat.descFactorial (r + k - 1) k : ℝ) * u ^ (-(r + k : ℤ)))
        (Set.Ioi 0) := fun u hu => ih u hu
    rw [Filter.EventuallyEq.deriv_eq (heq.eventuallyEq_of_mem (Ioi_mem_nhds ht))]
    have hderiv : HasDerivAt
        (fun u : ℝ => (-1 : ℝ) ^ k * (Nat.descFactorial (r + k - 1) k : ℝ) * u ^ (-(r + k : ℤ)))
        ((-1 : ℝ) ^ k * (Nat.descFactorial (r + k - 1) k : ℝ) *
          ((-(r + k : ℤ) : ℝ) * t ^ (-(r + k : ℤ) - 1))) t :=
      (hasDerivAt_zpow (-(r + k : ℤ)) t (Or.inl ht.ne')).const_mul _
    rw [hderiv.deriv]
    have hdesc : Nat.descFactorial (r + (k + 1) - 1) (k + 1) =
        Nat.descFactorial (r + k - 1) k * (r + k) := by
      rw [show r + (k + 1) - 1 = (r + k - 1) + 1 by omega, Nat.succ_descFactorial_succ, mul_comm]
      congr 1; omega
    rw [hdesc, pow_succ]
    push_cast
    rw [show -(r + (k + 1) : ℤ) = -(r + k : ℤ) - 1 by omega]
    ring

lemma iteratedDeriv_sum_laurent (A : Finset ℕ) (hA : ∀ r ∈ A, 1 ≤ r) (c : ℕ → ℝ) (k : ℕ) :
    ∀ t : ℝ, 0 < t →
      iteratedDeriv k (fun u : ℝ => ∑ r ∈ A, c r * u ^ (-(r : ℤ))) t =
        (-1 : ℝ) ^ k * ∑ r ∈ A, c r * (Nat.descFactorial (r + k - 1) k : ℝ) * t ^ (-(r + k : ℤ)) := by
  induction k with
  | zero =>
    intro t _
    simp
  | succ k ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have heq : Set.EqOn (iteratedDeriv k (fun u : ℝ => ∑ r ∈ A, c r * u ^ (-(r : ℤ))))
        (fun u : ℝ => (-1 : ℝ) ^ k * ∑ r ∈ A, c r * (Nat.descFactorial (r + k - 1) k : ℝ) * u ^ (-(r + k : ℤ)))
        (Set.Ioi 0) := fun u hu => ih u hu
    rw [Filter.EventuallyEq.deriv_eq (heq.eventuallyEq_of_mem (Ioi_mem_nhds ht))]
    have hderiv : HasDerivAt
        (fun u : ℝ => (-1 : ℝ) ^ k * ∑ r ∈ A, c r * (Nat.descFactorial (r + k - 1) k : ℝ) * u ^ (-(r + k : ℤ)))
        ((-1 : ℝ) ^ k * ∑ r ∈ A, c r * (Nat.descFactorial (r + k - 1) k : ℝ) *
          ((-(r + k : ℤ) : ℝ) * t ^ (-(r + k : ℤ) - 1))) t := by
      refine HasDerivAt.const_mul _ (HasDerivAt.sum fun r _ => ?_)
      exact (hasDerivAt_zpow (-(r + k : ℤ)) t (Or.inl ht.ne')).const_mul _
    rw [hderiv.deriv, pow_succ, mul_assoc, Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr1 : 1 ≤ r := hA r hr
    have hdesc : Nat.descFactorial (r + (k + 1) - 1) (k + 1) =
        Nat.descFactorial (r + k - 1) k * (r + k) := by
      rw [show r + (k + 1) - 1 = (r + k - 1) + 1 by omega, Nat.succ_descFactorial_succ, mul_comm]
      congr 1; omega
    rw [hdesc, show -(r + (k + 1) : ℤ) = -(r + k : ℤ) - 1 by omega]
    push_cast
    ring

lemma laurent_sum_dom_bounds (A : Finset ℕ) (R k : ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
    (r₀ : ℕ) (hr₀ : r₀ ∈ A) (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (hk : 1 ≤ k)
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₁₂ : M₁ ≤ M₂) (hM₂ : M₂ ≤ 2 * M₁)
    (hdom : ∀ r ∈ A, r ≠ r₀ →
      |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) :
    let lam := (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ + k : ℤ))
    0 < lam ∧
    ∀ t ∈ Set.Icc M₁ M₂,
      lam ≤ |iteratedDeriv k (fun u : ℝ => ∑ r ∈ A, c r * u ^ (-(r : ℤ))) t| ∧
      |iteratedDeriv k (fun u : ℝ => ∑ r ∈ A, c r * u ^ (-(r : ℤ))) t| ≤
        (3 * (2 : ℝ) ^ (R + k)) * lam := by
  intro lam
  have hr₀_1 : 1 ≤ r₀ := (hA r₀ hr₀).1
  have hr₀_R : r₀ ≤ R := (hA r₀ hr₀).2
  have hdesc_pos : 0 < (Nat.descFactorial (r₀ + k - 1) k : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : k ≤ r₀ + k - 1)
  have hM₂_pos : 0 < M₂ := lt_of_lt_of_le hM₁ hM₁₂
  have hlam_pos : 0 < lam := by
    dsimp only [lam]
    positivity
  refine ⟨hlam_pos, fun t ht => ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le hM₁ ht.1
  rw [iteratedDeriv_sum_laurent A (fun r hr => (hA r hr).1) c k t ht_pos]
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  let term : ℕ → ℝ := fun r => c r * (Nat.descFactorial (r + k - 1) k : ℝ) * t ^ (-(r + k : ℤ))
  have hsplit : ∑ r ∈ A, term r = term r₀ + ∑ r ∈ A.erase r₀, term r :=
    (Finset.add_sum_erase A term hr₀).symm
  have hterm_abs : ∀ s : ℕ, |term s| =
      |c s| * (Nat.descFactorial (s + k - 1) k : ℝ) * t ^ (-(s + k : ℤ)) := by
    intro s
    dsimp only [term]
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (Nat.descFactorial _ _)),
      abs_of_pos (zpow_pos ht_pos _)]
  have htail : |∑ r ∈ A.erase r₀, term r| ≤ (1 / 2 : ℝ) * |term r₀| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hpt : ∀ r ∈ A.erase r₀, |term r| ≤ (1 / (2 * max (A.card : ℝ) 1)) * |term r₀| := by
      intro r hr
      have hrA : r ∈ A := Finset.mem_of_mem_erase hr
      have hne : r ≠ r₀ := Finset.ne_of_mem_erase hr
      have htk_nn : 0 ≤ t ^ (-(k : ℤ)) := (zpow_pos ht_pos _).le
      have htr : t ^ (-(r : ℤ)) ≤ M₁ ^ (-(r : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hM₁ r) (pow_le_pow_left₀ hM₁.le ht.1 r)
      have htr₀ : M₂ ^ (-(r₀ : ℤ)) ≤ t ^ (-(r₀ : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos ht_pos r₀) (pow_le_pow_left₀ ht_pos.le ht.2 r₀)
      have hterm_eq : ∀ s : ℕ, |term s| =
          (|c s| * (Nat.descFactorial (s + k - 1) k : ℝ) * t ^ (-(s : ℤ))) * t ^ (-(k : ℤ)) := by
        intro s
        rw [hterm_abs s, show -(s + k : ℤ) = -(s : ℤ) + -(k : ℤ) by omega,
          zpow_add₀ ht_pos.ne', ← mul_assoc]
      rw [hterm_eq r, hterm_eq r₀, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ htk_nn
      calc |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * t ^ (-(r : ℤ))
          ≤ |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) :=
            mul_le_mul_of_nonneg_left htr (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
        _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ))) := hdom r hrA hne
        _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * t ^ (-(r₀ : ℤ))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htr₀
              (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (by positivity)
    calc ∑ r ∈ A.erase r₀, |term r|
        ≤ ∑ _r ∈ A.erase r₀, (1 / (2 * max (A.card : ℝ) 1)) * |term r₀| := Finset.sum_le_sum hpt
      _ = ((A.erase r₀).card : ℝ) * ((1 / (2 * max (A.card : ℝ) 1)) * |term r₀|) := by simp
      _ ≤ (A.card : ℝ) * ((1 / (2 * max (A.card : ℝ) 1)) * |term r₀|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (Finset.card_erase_le : (A.erase r₀).card ≤ A.card)
      _ ≤ (1 / 2 : ℝ) * |term r₀| := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          linarith [le_max_left (A.card : ℝ) 1]
  have hlo_r₀ : 2 * lam ≤ |term r₀| := by
    rw [hterm_abs r₀]
    dsimp only [lam]
    have hz : M₂ ^ (-(r₀ + k : ℤ)) ≤ t ^ (-(r₀ + k : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos ht_pos _) (pow_le_pow_left₀ ht_pos.le ht.2 _)
    calc 2 * ((1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ + k : ℤ)))
        = |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ + k : ℤ)) := by ring
      _ ≤ |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * t ^ (-(r₀ + k : ℤ)) :=
          mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hhi_r₀ : |term r₀| ≤ (2 : ℝ) ^ (R + k) * (2 * lam) := by
    rw [hterm_abs r₀]
    dsimp only [lam]
    have hz : t ^ (-(r₀ + k : ℤ)) ≤ (2 : ℝ) ^ (R + k) * M₂ ^ (-(r₀ + k : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      have hpow_le : M₂ ^ (r₀ + k) ≤ (2 : ℝ) ^ (R + k) * t ^ (r₀ + k) := by
        calc M₂ ^ (r₀ + k) ≤ (2 * M₁) ^ (r₀ + k) := pow_le_pow_left₀ hM₂_pos.le hM₂ _
          _ ≤ (2 * t) ^ (r₀ + k) := pow_le_pow_left₀ (by positivity) (by linarith [ht.1]) _
          _ = (2 : ℝ) ^ (r₀ + k) * t ^ (r₀ + k) := mul_pow 2 t _
          _ ≤ (2 : ℝ) ^ (R + k) * t ^ (r₀ + k) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      rw [inv_le_comm₀ (pow_pos ht_pos _) (mul_pos (by positivity) (pow_pos hM₂_pos _))]
      simpa [mul_inv] using (div_le_iff₀ (pow_pos hM₂_pos _)).mpr (by
        rw [inv_mul_eq_div, le_div_iff₀ (pow_pos ht_pos _)]
        linarith)
    calc |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * t ^ (-(r₀ + k : ℤ))
        ≤ |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * ((2 : ℝ) ^ (R + k) * M₂ ^ (-(r₀ + k : ℤ))) :=
          mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      _ = (2 : ℝ) ^ (R + k) * (2 * ((1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ + k : ℤ)))) := by ring
  constructor
  · rw [hsplit]
    have htri := abs_sub_abs_le_abs_add (term r₀) (∑ r ∈ A.erase r₀, term r)
    linarith
  · rw [hsplit]
    have htri := abs_add_le (term r₀) (∑ r ∈ A.erase r₀, term r)
    linarith

lemma laurent_sum_deriv_mono_or_anti (A : Finset ℕ) (R : ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
    (r₀ : ℕ) (hr₀ : r₀ ∈ A) (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0)
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₁₂ : M₁ ≤ M₂) (hM₂ : M₂ ≤ 2 * M₁)
    (hdom2 : ∀ r ∈ A, r ≠ r₀ →
      |c r| * (Nat.descFactorial (r + 2 - 1) 2 : ℝ) * M₁ ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|c r₀| * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * M₂ ^ (-(r₀ : ℤ)))) :
    let G : ℝ → ℝ := fun u => ∑ r ∈ A, c r * u ^ (-(r : ℤ))
    MonotoneOn (deriv G) (Set.Icc M₁ M₂) ∨ AntitoneOn (deriv G) (Set.Icc M₁ M₂) := by
  intro G
  have hdiff1 : DifferentiableOn ℝ (deriv G) (Set.Icc M₁ M₂) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hM₁ ht.1
    have heq : Set.EqOn (deriv G)
        (fun u : ℝ => (-1 : ℝ) ^ 1 * ∑ r ∈ A, c r * (Nat.descFactorial (r + 1 - 1) 1 : ℝ) * u ^ (-(r + 1 : ℤ)))
        (Set.Ioi 0) := by
      intro u hu
      rw [← iteratedDeriv_one]
      exact iteratedDeriv_sum_laurent A (fun r hr => (hA r hr).1) c 1 u hu
    have hda : HasDerivAt
        (fun u : ℝ => (-1 : ℝ) ^ 1 * ∑ r ∈ A, c r * (Nat.descFactorial (r + 1 - 1) 1 : ℝ) * u ^ (-(r + 1 : ℤ)))
        ((-1 : ℝ) ^ 1 * ∑ r ∈ A, c r * (Nat.descFactorial (r + 1 - 1) 1 : ℝ) *
          ((-(r + 1 : ℤ) : ℝ) * t ^ (-(r + 1 : ℤ) - 1))) t := by
      refine HasDerivAt.const_mul _ (HasDerivAt.sum fun r _ => ?_)
      exact (hasDerivAt_zpow (-(r + 1 : ℤ)) t (Or.inl ht_pos.ne')).const_mul _
    exact (hda.differentiableAt.congr_of_eventuallyEq (heq.eventuallyEq_of_mem (Ioi_mem_nhds ht_pos))).differentiableWithinAt
  have hcont1 : ContinuousOn (deriv G) (Set.Icc M₁ M₂) := hdiff1.continuousOn
  have hderiv2_sign : ∀ t ∈ Set.Icc M₁ M₂,
      let term : ℕ → ℝ := fun r => c r * (Nat.descFactorial (r + 2 - 1) 2 : ℝ) * t ^ (-(r + 2 : ℤ))
      deriv (deriv G) t = term r₀ + ∑ r ∈ A.erase r₀, term r ∧
      |∑ r ∈ A.erase r₀, term r| ≤ (1 / 2 : ℝ) * |term r₀| := by
    intro t ht term
    have ht_pos : 0 < t := lt_of_lt_of_le hM₁ ht.1
    have hderiv_eq : deriv (deriv G) t = term r₀ + ∑ r ∈ A.erase r₀, term r := by
      rw [← iteratedDeriv_one (f := G), ← iteratedDeriv_succ,
        iteratedDeriv_sum_laurent A (fun r hr => (hA r hr).1) c 2 t ht_pos]
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      exact (Finset.add_sum_erase A term hr₀).symm
    have hterm_abs : ∀ s : ℕ, |term s| =
        |c s| * (Nat.descFactorial (s + 2 - 1) 2 : ℝ) * t ^ (-(s + 2 : ℤ)) := by
      intro s
      dsimp only [term]
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (Nat.descFactorial _ _)),
        abs_of_pos (zpow_pos ht_pos _)]
    have htail : |∑ r ∈ A.erase r₀, term r| ≤ (1 / 2 : ℝ) * |term r₀| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hpt : ∀ r ∈ A.erase r₀, |term r| ≤ (1 / (2 * max (A.card : ℝ) 1)) * |term r₀| := by
        intro r hr
        have hrA : r ∈ A := Finset.mem_of_mem_erase hr
        have hne : r ≠ r₀ := Finset.ne_of_mem_erase hr
        have htk_nn : 0 ≤ t ^ (-(2 : ℤ)) := (zpow_pos ht_pos _).le
        have htr : t ^ (-(r : ℤ)) ≤ M₁ ^ (-(r : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hM₁ r) (pow_le_pow_left₀ hM₁.le ht.1 r)
        have htr₀ : M₂ ^ (-(r₀ : ℤ)) ≤ t ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos ht_pos r₀) (pow_le_pow_left₀ ht_pos.le ht.2 r₀)
        have hterm_eq : ∀ s : ℕ, |term s| =
            (|c s| * (Nat.descFactorial (s + 2 - 1) 2 : ℝ) * t ^ (-(s : ℤ))) * t ^ (-(2 : ℤ)) := by
          intro s
          rw [hterm_abs s, show -(s + 2 : ℤ) = -(s : ℤ) + -(2 : ℤ) by omega,
            zpow_add₀ ht_pos.ne', ← mul_assoc]
        rw [hterm_eq r, hterm_eq r₀, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ htk_nn
        calc |c r| * (Nat.descFactorial (r + 2 - 1) 2 : ℝ) * t ^ (-(r : ℤ))
            ≤ |c r| * (Nat.descFactorial (r + 2 - 1) 2 : ℝ) * M₁ ^ (-(r : ℤ)) :=
              mul_le_mul_of_nonneg_left htr (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
          _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                (|c r₀| * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * M₂ ^ (-(r₀ : ℤ))) := hdom2 r hrA hne
          _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                (|c r₀| * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * t ^ (-(r₀ : ℤ))) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htr₀
                (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (by positivity)
      calc ∑ r ∈ A.erase r₀, |term r|
          ≤ ∑ _r ∈ A.erase r₀, (1 / (2 * max (A.card : ℝ) 1)) * |term r₀| := Finset.sum_le_sum hpt
        _ = ((A.erase r₀).card : ℝ) * ((1 / (2 * max (A.card : ℝ) 1)) * |term r₀|) := by simp
        _ ≤ (A.card : ℝ) * ((1 / (2 * max (A.card : ℝ) 1)) * |term r₀|) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast (Finset.card_erase_le : (A.erase r₀).card ≤ A.card)
        _ ≤ (1 / 2 : ℝ) * |term r₀| := by
            rw [← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            rw [mul_one_div, div_le_iff₀ (by positivity)]
            linarith [le_max_left (A.card : ℝ) 1]
    exact ⟨hderiv_eq, htail⟩
  rcases lt_or_gt_of_ne hc₀ with hneg | hpos
  · right
    refine antitoneOn_of_deriv_nonpos (convex_Icc M₁ M₂) hcont1 (hdiff1.mono interior_subset) fun t ht => ?_
    have ht_icc : t ∈ Set.Icc M₁ M₂ := interior_subset ht
    have ht_pos : 0 < t := lt_of_lt_of_le hM₁ ht_icc.1
    rcases hderiv2_sign t ht_icc with ⟨heq, htail⟩
    have hterm_neg : c r₀ * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * t ^ (-(r₀ + 2 : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg.le (Nat.cast_nonneg _))
        (zpow_pos ht_pos _).le
    rw [abs_of_nonpos hterm_neg] at htail
    have hle := le_abs_self (∑ r ∈ A.erase r₀, c r * (Nat.descFactorial (r + 2 - 1) 2 : ℝ) * t ^ (-(r + 2 : ℤ)))
    linarith
  · left
    refine monotoneOn_of_deriv_nonneg (convex_Icc M₁ M₂) hcont1 (hdiff1.mono interior_subset) fun t ht => ?_
    have ht_icc : t ∈ Set.Icc M₁ M₂ := interior_subset ht
    have ht_pos : 0 < t := lt_of_lt_of_le hM₁ ht_icc.1
    rcases hderiv2_sign t ht_icc with ⟨heq, htail⟩
    have hterm_pos : 0 ≤ c r₀ * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * t ^ (-(r₀ + 2 : ℤ)) :=
      mul_nonneg (mul_nonneg hpos.le (Nat.cast_nonneg _)) (zpow_pos ht_pos _).le
    rw [abs_of_nonneg hterm_pos] at htail
    have hge := neg_abs_le (∑ r ∈ A.erase r₀, c r * (Nat.descFactorial (r + 2 - 1) 2 : ℝ) * t ^ (-(r + 2 : ℤ)))
    linarith

lemma van_der_corput_for_range (j : ℕ) (hj : 3 ≤ j) (α : ℝ) (hα : 1 ≤ α) :
    ∃ C > 0, ∀ (M₁ M₂ lam : ℝ) (G : ℝ → ℝ),
      0 ≤ M₁ → 1 ≤ M₂ - M₁ →
      (M₂ - M₁) ^ (-(5 / 2 : ℝ)) ≤ lam → lam ≤ (M₂ - M₁) ^ (-(1 / 2 : ℝ)) →
      (∀ t ∈ Set.Icc M₁ M₂, lam ≤ |iteratedDeriv j G t| ∧ |iteratedDeriv j G t| ≤ α * lam) →
      ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖ ≤
        2 * C * (M₂ - M₁) ^ (1 - (1 : ℝ) / (2 * ((2 ^ j - 2 : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hvd⟩ := van_der_corput_kth_derivative j (by omega) α hα
  refine ⟨C, hC, fun M₁ M₂ lam G hM₁ hL1 hlam_lo hlam_hi hG => ?_⟩
  set L := M₂ - M₁
  have hL_pos : 0 < L := by linarith
  have hlam_pos : 0 < lam := lt_of_lt_of_le (Real.rpow_pos_of_pos hL_pos _) hlam_lo
  have h1 := hvd M₁ M₂ lam G hM₁ hL1 hlam_pos hG
  set d : ℝ := ((2 ^ j - 2 : ℕ) : ℝ)
  have hd_pos : 0 < d := by
    dsimp only [d]
    have : 6 ≤ 2 ^ j - 2 := by
      have : 8 ≤ 2 ^ j := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj)
      omega
    exact_mod_cast (by omega : 0 < 2 ^ j - 2)
  have hterm1 : L * lam ^ ((1 : ℝ) / d) ≤ L ^ (1 - (1 : ℝ) / (2 * d)) := by
    have hpow : lam ^ ((1 : ℝ) / d) ≤ (L ^ (-(1 / 2 : ℝ))) ^ ((1 : ℝ) / d) :=
      Real.rpow_le_rpow hlam_pos.le hlam_hi (by positivity)
    rw [← Real.rpow_mul hL_pos.le] at hpow
    calc L * lam ^ ((1 : ℝ) / d)
        ≤ L * L ^ (-(1 / 2 : ℝ) * ((1 : ℝ) / d)) := mul_le_mul_of_nonneg_left hpow hL_pos.le
      _ = L ^ (1 : ℝ) * L ^ (-(1 / 2 : ℝ) * ((1 : ℝ) / d)) := by rw [Real.rpow_one]
      _ = L ^ (1 + -(1 / 2 : ℝ) * ((1 : ℝ) / d)) := (Real.rpow_add hL_pos _ _).symm
      _ = L ^ (1 - (1 : ℝ) / (2 * d)) := by congr 1; ring
  have hterm2 : L ^ (1 - (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ))) * lam ^ (-(1 : ℝ) / d) ≤
      L ^ (1 - (1 : ℝ) / (2 * d)) := by
    have hneg_le : (-(1 : ℝ) / d) ≤ 0 := by
      rw [neg_div]; exact neg_nonpos.mpr (by positivity)
    have hpow : lam ^ (-(1 : ℝ) / d) ≤ (L ^ (-(5 / 2 : ℝ))) ^ (-(1 : ℝ) / d) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hL_pos _) hlam_lo hneg_le
    rw [← Real.rpow_mul hL_pos.le] at hpow
    have hexp_le : (1 - (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ))) + (-(5 / 2 : ℝ) * (-(1 : ℝ) / d)) ≤
        1 - (1 : ℝ) / (2 * d) := by
      have hd_eq : d = (2 : ℝ) ^ j - 2 := by
        dsimp only [d]
        have h2j : 2 ≤ 2 ^ j := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj)
        rw [Nat.cast_sub h2j]; push_cast; rfl
      have h2_le : (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ)) * (2 : ℝ) ^ j = 4 := by
        rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      have h2_inv : (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ)) ≤ (2 : ℝ) ^ (-(1 : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2_ge : (3 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ)) * d := by
        rw [hd_eq, mul_sub, h2_le]
        have : (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ)) * 2 ≤ 1 := by
          have hle := mul_le_mul_of_nonneg_right h2_inv (by norm_num : (0 : ℝ) ≤ 2)
          norm_num at hle ⊢; exact hle
        linarith
      have hsub : (1 : ℝ) / (2 * d) + (5 / 2 : ℝ) / d ≤ (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ)) := by
        rw [← div_div, show (1 : ℝ) / 2 / d + 5 / 2 / d = 3 / d by ring, div_le_iff₀ hd_pos]
        linarith
      have hring : -(5 / 2 : ℝ) * (-(1 : ℝ) / d) = (5 / 2 : ℝ) / d := by ring
      linarith
    calc L ^ (1 - (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ))) * lam ^ (-(1 : ℝ) / d)
        ≤ L ^ (1 - (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ))) * L ^ (-(5 / 2 : ℝ) * (-(1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = L ^ ((1 - (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ))) + -(5 / 2 : ℝ) * (-(1 : ℝ) / d)) :=
          (Real.rpow_add hL_pos _ _).symm
      _ ≤ L ^ (1 - (1 : ℝ) / (2 * d)) := Real.rpow_le_rpow_of_exponent_le hL1 hexp_le
  calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
      ≤ C * (L * lam ^ ((1 : ℝ) / d) + L ^ (1 - (2 : ℝ) ^ ((2 : ℤ) - (j : ℤ))) * lam ^ (-(1 : ℝ) / d)) := h1
    _ ≤ C * (L ^ (1 - (1 : ℝ) / (2 * d)) + L ^ (1 - (1 : ℝ) / (2 * d))) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC.le
    _ = 2 * C * L ^ (1 - (1 : ℝ) / (2 * d)) := by ring

end BrocardFormalization

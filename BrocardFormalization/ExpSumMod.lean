/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ExpSumTypeI
import BrocardFormalization.ExpSumVaughan
import BrocardFormalization.ExpSumCore
import BrocardFormalization.ExpSumMid

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

lemma type_I_single_d_bound_mod (q_den : ℕ) (hq_den : 1 ≤ q_den)
    (R K_max : ℕ) (hK_max : 3 ≤ K_max)
    (C_exp η_exp M₀ : ℝ) (hC_exp : 0 < C_exp) (hη_exp : 0 < η_exp) (hη_le : η_exp ≤ 1 / 4) (hM₀ : 16 ≤ M₀)
    (hexp : ∀ (A : Finset ℕ) (r₀ : ℕ) (hr₀ : r₀ ∈ A) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
        (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (M₁ M₂ : ℝ),
        M₀ ≤ M₁ → M₁ ≤ M₂ → M₂ ≤ 2 * M₁ →
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) →
        let T := |c r₀| * (r₀ : ℝ) * M₂ ^ (-(r₀ : ℤ))
        T ≤ M₂ ^ (K_max - 1) →
        ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (∑ r ∈ A, c r * (m : ℝ) ^ (-(r : ℤ)))‖ ≤
          C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)))
    (n : ℕ) (P a b : ℝ) (hP1 : 1 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hb2P : b ≤ 2 * P)
    (A : Finset ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R) (r₀ : ℕ) (hr₀ : r₀ ∈ A)
    (h : ℕ → ℤ) (hh₀ : h r₀ ≠ 0) (w : ℝ → ℝ) (W₀ : ℝ) (hW₀ : 0 ≤ W₀)
    (hw_bd : ∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀)
    (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (d : ℕ) (hd1 : 1 ≤ d) (hd_M0 : M₀ ≤ P / (d : ℝ))
    (hdom_d : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
      |(h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))))
    (hT_ub : |(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (K_max - 1)) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
        (Real.log k * w (d * k) : ℂ) *
          ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
      4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
        ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
  intro T₀
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hP_pos : 0 < P := by linarith
  have hPd_pos : 0 < P / d := div_pos hP_pos hd_pos
  have hPd_ge16 : 16 ≤ P / d := le_trans hM₀ hd_M0
  have hPd_ge1 : 1 ≤ P / d := by linarith
  have hlog2P1_nn : 0 ≤ Real.log (2 * P) + 1 := by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * P)]
  by_cases h_empty : ⌊b⌋₊ / d < (⌈a⌉₊ - 1) / d + 1
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW₀) hlog2P1_nn) (by positivity)) (by positivity)
  · push_neg at h_empty
    set a' : ℝ := (⌈a⌉₊ : ℝ) / d
    set b' : ℝ := (⌊b⌋₊ : ℝ) / d
    have hPa' : P / d ≤ a' := div_le_div_of_nonneg_right (le_trans hPa (Nat.le_ceil a)) hd_pos.le
    have hb'2P : b' ≤ 2 * (P / d) := by
      rw [show 2 * (P / d) = (2 * P) / d by ring]
      exact div_le_div_of_nonneg_right (le_trans (Nat.floor_le (by linarith)) hb2P) hd_pos.le
    have hceil_eq : ⌈a'⌉₊ = (⌈a⌉₊ - 1) / d + 1 := by
      have ha_pos : 1 ≤ ⌈a⌉₊ := Nat.ceil_pos.mpr (by linarith)
      apply le_antisymm
      · rw [Nat.ceil_le]
        have h1 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d + 1) * d := by
          have := Nat.lt_mul_div_succ (⌈a⌉₊ - 1) hd1
          rw [mul_comm] at this; omega
        rw [div_le_iff₀ hd_pos]
        exact_mod_cast h1
      · by_contra hlt
        push_neg at hlt
        have h1 : ⌈a'⌉₊ ≤ (⌈a⌉₊ - 1) / d := by omega
        have h2 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        have h3 : (⌈a⌉₊ : ℝ) / d ≤ ((⌈a⌉₊ - 1) / d : ℕ) := le_trans h2 (by exact_mod_cast h1)
        rw [div_le_iff₀ hd_pos] at h3
        have h4 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d) * d := by exact_mod_cast h3
        have h5 : ((⌈a⌉₊ - 1) / d) * d ≤ ⌈a⌉₊ - 1 := Nat.div_mul_le_self _ _
        omega
    have hfloor_eq : ⌊b'⌋₊ = ⌊b⌋₊ / d := by
      rw [Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hd_pos.le)]
      refine ⟨(le_div_iff₀ hd_pos).mpr (by exact_mod_cast Nat.div_mul_le_self ⌊b⌋₊ d), ?_⟩
      rw [div_lt_iff₀ hd_pos]
      have hlt : ⌊b⌋₊ < (⌊b⌋₊ / d + 1) * d := by
        calc ⌊b⌋₊ = d * (⌊b⌋₊ / d) + ⌊b⌋₊ % d := (Nat.div_add_mod ⌊b⌋₊ d).symm
          _ < d * (⌊b⌋₊ / d) + d := Nat.add_lt_add_left (Nat.mod_lt _ hd1) _
          _ = (⌊b⌋₊ / d + 1) * d := by ring
      exact_mod_cast hlt
    have ha'b' : a' ≤ b' := by
      have h1 : ((⌈a⌉₊ - 1) / d + 1 : ℕ) ≤ ⌊b⌋₊ / d := h_empty
      have h2 : a' ≤ ((⌈a⌉₊ - 1) / d + 1 : ℕ) := by rw [← hceil_eq]; exact Nat.le_ceil a'
      have h3 : ((⌊b⌋₊ / d : ℕ) : ℝ) ≤ b' := by
        rw [← hfloor_eq]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
      exact le_trans h2 (le_trans (by exact_mod_cast h1) h3)
    let wd : ℕ → ℝ := fun k => Real.log k * w (d * k)
    let W₀' : ℝ := W₀ * (Real.log (2 * P) + 1)
    have hW₀' : 0 ≤ W₀' := mul_nonneg hW₀ hlog2P1_nn
    have hA'B' : ⌈a'⌉₊ ≤ ⌊b'⌋₊ := by rw [hceil_eq, hfloor_eq]; exact h_empty
    have hA'_ge : P ≤ ((d * ⌈a'⌉₊ : ℕ) : ℝ) := by
      push_cast
      calc P = (d : ℝ) * (P / d) := by field_simp [hd_pos.ne']
        _ ≤ (d : ℝ) * a' := mul_le_mul_of_nonneg_left hPa' hd_pos.le
        _ ≤ (d : ℝ) * ⌈a'⌉₊ := mul_le_mul_of_nonneg_left (Nat.le_ceil a') hd_pos.le
    have hB'_le : ((d * ⌊b'⌋₊ : ℕ) : ℝ) ≤ 2 * P := by
      push_cast
      calc (d : ℝ) * ⌊b'⌋₊ ≤ (d : ℝ) * b' := mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) hd_pos.le
        _ ≤ (d : ℝ) * (2 * (P / d)) := mul_le_mul_of_nonneg_left hb'2P hd_pos.le
        _ = 2 * P := by field_simp [hd_pos.ne']
    have hwd_bd : ∀ k ∈ Finset.Icc ⌈a'⌉₊ ⌊b'⌋₊, |wd k| ≤ W₀' := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk_ge1 : (1 : ℝ) ≤ k := le_trans hPd_ge1 (le_trans hPa' (le_trans (Nat.le_ceil a') (by exact_mod_cast hk.1)))
      have hk_le : (k : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hk.2) (le_trans (Nat.floor_le (by linarith))
        (le_trans hb'2P (by rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)))
      have hdk_mem : (d : ℝ) * k ∈ Set.Icc P (2 * P) := ⟨by
        exact le_trans hA'_ge (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.1) hd_pos.le),
        by exact le_trans (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.2) hd_pos.le) hB'_le⟩
      dsimp only [wd]
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg hk_ge1)]
      calc Real.log k * |w (d * k)|
          ≤ Real.log (2 * P) * W₀ := mul_le_mul (Real.log_le_log (by positivity) hk_le) (hw_bd _ hdk_mem)
            (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ ≤ W₀ * (Real.log (2 * P) + 1) := by linarith
    have hwd_tv : ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |wd (k + 1) - wd k| ≤ 3 * W₀' := by
      have hstep : ∀ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊,
          |wd (k + 1) - wd k| ≤
            (Real.log (k + 1 : ℕ) - Real.log k) * W₀ +
            Real.log (2 * P) * |w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)| := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hk_ge1 : (1 : ℝ) ≤ k := le_trans hPd_ge1 (le_trans hPa' (le_trans (Nat.le_ceil a') (by exact_mod_cast hk.1)))
        have hk_le : (k : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hk.2.le) (le_trans (Nat.floor_le (by linarith))
          (le_trans hb'2P (by rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)))
        have hdk1_mem : ((d * (k + 1) : ℕ) : ℝ) ∈ Set.Icc P (2 * P) := ⟨by
          exact le_trans hA'_ge (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : ⌈a'⌉₊ ≤ k + 1)) hd_pos.le),
          by exact le_trans (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.2) hd_pos.le) hB'_le⟩
        have hlog_mono : Real.log (k : ℝ) ≤ Real.log (k + 1 : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
        have hsplit : wd (k + 1) - wd k =
            (Real.log (k + 1 : ℕ) - Real.log k) * w ((d * (k + 1) : ℕ) : ℝ) +
            Real.log k * (w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)) := by
          dsimp only [wd]; push_cast; ring
        rw [hsplit]
        refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hlog_mono)]
          exact mul_le_mul_of_nonneg_left (hw_bd _ hdk1_mem) (sub_nonneg.mpr hlog_mono)
        · rw [abs_mul, abs_of_nonneg (Real.log_nonneg hk_ge1)]
          exact mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) hk_le) (abs_nonneg _)
      have htel : ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, (Real.log (k + 1 : ℕ) - Real.log k) * W₀ ≤ W₀ * Real.log (2 * P) := by
        rw [← Finset.sum_mul, Finset.sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hA'B']
        have hA'_ge1 : (1 : ℝ) ≤ ⌈a'⌉₊ := le_trans hPd_ge1 (le_trans hPa' (Nat.le_ceil a'))
        have hB'_le2P : (⌊b'⌋₊ : ℝ) ≤ 2 * P := le_trans (Nat.floor_le (by linarith))
          (le_trans hb'2P (by rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1))
        have hlog_le : Real.log (⌊b'⌋₊ : ℝ) - Real.log (⌈a'⌉₊ : ℝ) ≤ Real.log (2 * P) := by
          linarith [Real.log_nonneg hA'_ge1, Real.log_le_log (by linarith [hA'_ge1, show (⌈a'⌉₊ : ℝ) ≤ ⌊b'⌋₊ by exact_mod_cast hA'B']) hB'_le2P]
        nlinarith
      have htv_w := discrete_tv_scale_le hP_pos hw_diff hw_tv d ⌈a'⌉₊ ⌊b'⌋₊ hA'B' hA'_ge hB'_le
      calc ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |wd (k + 1) - wd k|
          ≤ ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊,
              ((Real.log (k + 1 : ℕ) - Real.log k) * W₀ +
                Real.log (2 * P) * |w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)|) := Finset.sum_le_sum hstep
        _ = (∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, (Real.log (k + 1 : ℕ) - Real.log k) * W₀) +
            Real.log (2 * P) * ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)| := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ W₀ * Real.log (2 * P) + Real.log (2 * P) * W₀ :=
              add_le_add htel (mul_le_mul_of_nonneg_left htv_w (Real.log_nonneg (by linarith)))
        _ ≤ 3 * W₀' := by dsimp only [W₀']; nlinarith
    set E : ℝ := max C_exp 3 *
      ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := mul_nonneg (by positivity) (add_nonneg (div_nonneg (by positivity)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
    have hsum_bd : ∀ u : ℕ, ⌈a'⌉₊ ≤ u → u ≤ ⌊b'⌋₊ →
        ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖ ≤ E := by
      intro u hau hub
      have hu_ge : P / d ≤ (u : ℝ) := by
        have h1 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        exact le_trans hPa' (le_trans h1 (by exact_mod_cast hau))
      have hu_le : (u : ℝ) ≤ 2 * (P / d) := by
        have h1 : (⌊b'⌋₊ : ℝ) ≤ b' := Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
        exact le_trans (by exact_mod_cast hub) (le_trans h1 hb'2P)
      have hu_le' : (u : ℝ) ≤ 2 * P / d := by linarith [hu_le, show 2 * (P / d) = 2 * P / d by ring]
      by_cases hn0 : n = 0
      · subst hn0
        have htriv : ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
            ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          simp [norm_ePhase]
        have hcard : ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) ≤ 2 * P / d := by
          rw [Nat.card_Icc]
          have h1 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (lt_of_lt_of_le hPd_pos hPa')
          have h2 : u + 1 - ⌈a'⌉₊ ≤ u := by omega
          exact le_trans (by exact_mod_cast h2) hu_le'
        have hT0_0 : T₀ = 0 := by dsimp only [T₀]; simp
        have hmax1 : max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 = 1 := by rw [hT0_0, mul_zero, max_eq_right zero_le_one]
        calc ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖
            ≤ 2 * P / d := le_trans htriv hcard
          _ = 1 * ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + 0) := by rw [hmax1, div_one, one_mul, add_zero]
          _ ≤ E := by
              dsimp only [E]
              refine mul_le_mul (le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_right _ _))
                (add_le_add le_rfl (by positivity)) (by positivity) (by positivity)
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have h_eq_phase : ∀ k : ℕ, 1 ≤ k →
            ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r)) =
            ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
          intro k _
          congr 1
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Nat.cast_mul, mul_pow, zpow_neg, zpow_natCast]
          ring
        have hsum_eq : ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r)) =
            ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
              ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
          refine Finset.sum_congr rfl fun k hk => h_eq_phase k (by
            have h1 : (1 : ℝ) ≤ a' := le_trans hPd_ge1 hPa'
            have h2 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (by linarith)
            exact le_trans h2 (Finset.mem_Icc.mp hk).1)
        rw [hsum_eq]
        let cd : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)
        have hcd0 : cd r₀ ≠ 0 :=
          div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hh₀) hn_pos.ne') (by positivity)
        have hM0_a' : M₀ ≤ a' := le_trans hd_M0 hPa'
        have ha'u : a' ≤ (u : ℝ) := le_trans (Nat.le_ceil a') (by exact_mod_cast hau)
        have hu2a' : (u : ℝ) ≤ 2 * a' := le_trans hu_le (by linarith [hPa'])
        have hdom_u : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
            |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a' ^ (-(r : ℤ)) ≤
              (1 / (2 * max (A.card : ℝ) 1)) *
                (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) := by
          intro k hk r hr hne
          have ha'_pow : a' ^ (-(r : ℤ)) ≤ (P / d) ^ (-(r : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos hPd_pos r) (pow_le_pow_left₀ hPd_pos.le hPa' r)
          have hu_pow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
          calc |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a' ^ (-(r : ℤ))
              ≤ |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) :=
                mul_le_mul_of_nonneg_left ha'_pow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
            _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                  (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                hdom_d k hk r hr hne
            _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                  (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_pow
                  (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (by positivity)
        have hTu_ub : |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (K_max - 1) := by
          have h1 : (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos hPd_pos r₀) (pow_le_pow_left₀ hPd_pos.le hu_ge r₀)
          have h3 : (P / d) ^ (K_max - 1) ≤ (u : ℝ) ^ (K_max - 1) :=
            pow_le_pow_left₀ hPd_pos.le hu_ge _
          calc |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))
              ≤ |cd r₀| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (P / d) ^ (K_max - 1) := hT_ub
            _ ≤ (u : ℝ) ^ (K_max - 1) := h3
        have hhexp := hexp A r₀ hr₀ hA cd hcd0 a' (u : ℝ) hM0_a' ha'u hu2a' hdom_u hTu_ub
        rw [Nat.floor_natCast] at hhexp
        have hT_ge : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀ ≤ |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
          dsimp only [cd, T₀]
          have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
          have hupow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
          have h2pow : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * P ^ (-(r₀ : ℤ)) ≤ ((q_den : ℝ) * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ)) := by
            have hq_pos : (0 : ℝ) < q_den := by exact_mod_cast hq_den
            rw [show (2 * P / d) = (2 * P) / d by ring,
              zpow_neg (2 : ℝ) (R : ℤ), zpow_natCast (2 : ℝ) R,
              zpow_neg P (r₀ : ℤ), zpow_natCast P r₀,
              zpow_neg ((2 * P) / d) (r₀ : ℤ), zpow_natCast ((2 * P) / d) r₀, div_pow, inv_div]
            rw [mul_pow, mul_inv]
            field_simp [hq_pos.ne', hd_pos.ne', hP_pos.ne']
            have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
            linarith [h2r]
          have habs_cd : |(h r₀ : ℝ) * n / ((q_den : ℝ) * (d : ℝ) ^ r₀)| = |(h r₀ : ℝ)| * n / ((q_den : ℝ) * (d : ℝ) ^ r₀) := by
            rw [abs_div, abs_mul, abs_of_pos hn_pos, abs_of_pos (by positivity : (0 : ℝ) < (q_den : ℝ) * (d : ℝ) ^ r₀)]
          rw [habs_cd]
          calc ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * (|(h r₀ : ℝ)| * n / P ^ r₀)
              = |(h r₀ : ℝ)| * n * (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * P ^ (-(r₀ : ℤ))) := by
                  simp only [zpow_neg, zpow_natCast]; ring
            _ ≤ |(h r₀ : ℝ)| * n * (((q_den : ℝ) * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                  mul_le_mul_of_nonneg_left h2pow (by positivity)
            _ = |(h r₀ : ℝ)| * n / ((q_den : ℝ) * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) := by ring
            _ ≤ |(h r₀ : ℝ)| * n / ((q_den : ℝ) * (d : ℝ) ^ r₀) * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hr0_1 (by positivity)) hupow (by positivity) (by positivity)
        refine le_trans hhexp ?_
        dsimp only [E]
        refine mul_le_mul (le_max_left _ _) ?_ (add_nonneg (div_nonneg (by positivity)
          (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity)) (by positivity)
        refine add_le_add ?_ ?_
        · exact div_le_div₀ (by positivity) hu_le' (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (max_le_max hT_ge le_rfl)
        · exact Real.rpow_le_rpow (by positivity) hu_le' (by linarith)
    have hps := abel_summation_Icc hA'B' hW₀' (by positivity : 0 ≤ 3 * W₀') hE_nn hwd_bd hwd_tv hsum_bd
    rw [hceil_eq, hfloor_eq] at hps
    calc ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
            (Real.log k * w (d * k) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖
        ≤ (W₀' + 3 * W₀') * E := by simpa [wd] using hps
      _ = 4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
            ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          dsimp only [W₀', E]; ring


lemma type_II_inner_sum_bound_mod (q_den : ℕ) (hq_den : 1 ≤ q_den)
    (R K_max : ℕ) (hK_max : 3 ≤ K_max)
    (C_exp η_exp M₀ : ℝ) (hC_exp : 0 < C_exp) (hη_exp : 0 < η_exp) (hη_le : η_exp ≤ 1 / 4) (hM₀ : 16 ≤ M₀)
    (hexp : ∀ (A : Finset ℕ) (r₀ : ℕ) (hr₀ : r₀ ∈ A) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
        (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (M₁ M₂ : ℝ),
        M₀ ≤ M₁ → M₁ ≤ M₂ → M₂ ≤ 2 * M₁ →
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) →
        let T := |c r₀| * (r₀ : ℝ) * M₂ ^ (-(r₀ : ℤ))
        T ≤ M₂ ^ (K_max - 1) →
        ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (∑ r ∈ A, c r * (m : ℝ) ^ (-(r : ℤ)))‖ ≤
          C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)))
    (n : ℕ) (P a b : ℝ) (hP1 : 1 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hb2P : b ≤ 2 * P)
    (A : Finset ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R) (r₀ : ℕ) (hr₀ : r₀ ∈ A)
    (h : ℕ → ℤ) (hh₀ : h r₀ ≠ 0) (w : ℝ → ℝ) (W₀ : ℝ) (hW₀ : 0 ≤ W₀)
    (hw_bd : ∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀)
    (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (X₁ X_top Y₁ : ℕ) (hX₁ : 1 ≤ X₁) (hM₀_X₁ : M₀ ≤ (X₁ : ℝ)) (hX_top : X_top ≤ 2 * X₁)
    (hY₁ : 1 ≤ Y₁) (hXY_hi : (2 * X₁ : ℝ) * (2 * Y₁ : ℝ) ≤ 16 * P)
    (y₁ y₂ : ℕ) (hy₁_lo : Y₁ ≤ y₁) (hy₁_hi : y₁ ≤ 2 * Y₁)
    (hy₂_lo : Y₁ ≤ y₂) (hy₂_hi : y₂ ≤ 2 * Y₁) (hy_ne : y₁ ≠ y₂)
    (hdom_y : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
      |(h r : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))| *
          (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
            (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ))))
    (hT_ub : |(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
        (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) ≤ (X₁ : ℝ) ^ (K_max - 1))
    (hT₀_ge1 : 1 ≤ |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    let T_y := ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ * (|(y₁ : ℝ) - y₂| / Y₁)
    ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * y₁ ∧ x * y₁ ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * y₂ ∧ x * y₂ ≤ ⌊b⌋₊),
        (w (x * y₁) * w (x * y₂) : ℂ) *
          ePhase ((∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₁ : ℕ) : ℝ) ^ r)) -
            (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₂ : ℕ) : ℝ) ^ r)))‖ ≤
      8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) := by
  intro T₀ T_y
  have hX₁_pos : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
  have hY₁_pos : (0 : ℝ) < Y₁ := by exact_mod_cast hY₁
  have hy₁_pos : (0 : ℝ) < y₁ := by exact_mod_cast (by omega : 0 < y₁)
  have hy₂_pos : (0 : ℝ) < y₂ := by exact_mod_cast (by omega : 0 < y₂)
  set a₁₂ : ℝ := max (X₁ : ℝ) (max ((⌈a⌉₊ : ℝ) / y₁) ((⌈a⌉₊ : ℝ) / y₂))
  set b₁₂ : ℝ := min (X_top : ℝ) (min ((⌊b⌋₊ : ℝ) / y₁) ((⌊b⌋₊ : ℝ) / y₂))
  have hflt_eq : (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * y₁ ∧ x * y₁ ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * y₂ ∧ x * y₂ ≤ ⌊b⌋₊) =
      Finset.Icc ⌈a₁₂⌉₊ ⌊b₁₂⌋₊ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hceil_iff : ⌈a₁₂⌉₊ ≤ x ↔ X₁ ≤ x ∧ ⌈a⌉₊ ≤ x * y₁ ∧ ⌈a⌉₊ ≤ x * y₂ := by
      rw [Nat.ceil_le]
      simp only [a₁₂, max_le_iff, div_le_iff₀ hy₁_pos, div_le_iff₀ hy₂_pos]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    have hfloor_iff : x ≤ ⌊b₁₂⌋₊ ↔ x ≤ X_top ∧ x * y₁ ≤ ⌊b⌋₊ ∧ x * y₂ ≤ ⌊b⌋₊ := by
      have hb_nn : 0 ≤ b₁₂ := by
        simp only [b₁₂, le_min_iff]
        exact ⟨Nat.cast_nonneg _, div_nonneg (Nat.cast_nonneg _) hy₁_pos.le,
          div_nonneg (Nat.cast_nonneg _) hy₂_pos.le⟩
      rw [Nat.le_floor_iff hb_nn]
      simp only [b₁₂, le_min_iff, le_div_iff₀ hy₁_pos, le_div_iff₀ hy₂_pos]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    rw [hceil_iff, hfloor_iff]; tauto
  rw [hflt_eq]
  have hTy_rhs_nn : 0 ≤ (2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp) :=
    add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity)
  by_cases h_empty_nat : ⌊b₁₂⌋₊ < ⌈a₁₂⌉₊
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty_nat), Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hC_exp.le) hTy_rhs_nn
  · push_neg at h_empty_nat
    have hb₁₂_nn : 0 ≤ b₁₂ := by
      simp only [b₁₂, le_min_iff]
      exact ⟨Nat.cast_nonneg _, div_nonneg (Nat.cast_nonneg _) hy₁_pos.le,
        div_nonneg (Nat.cast_nonneg _) hy₂_pos.le⟩
    have h_empty : a₁₂ ≤ b₁₂ := le_trans (Nat.le_ceil a₁₂) (le_trans (by exact_mod_cast h_empty_nat) (Nat.floor_le hb₁₂_nn))
    have ha₁₂_pos : 0 < a₁₂ := lt_of_lt_of_le hX₁_pos (le_max_left _ _)
    have hb₁₂_2a : b₁₂ ≤ 2 * a₁₂ := by
      calc b₁₂ ≤ (X_top : ℝ) := min_le_left _ _
        _ ≤ 2 * (X₁ : ℝ) := by exact_mod_cast hX_top
        _ ≤ 2 * a₁₂ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    let w₁₂ : ℕ → ℝ := fun x => w (x * y₁) * w (x * y₂)
    have hmem_P2P : ∀ t ∈ Set.Icc a₁₂ b₁₂, t * (y₁ : ℝ) ∈ Set.Icc P (2 * P) ∧ t * (y₂ : ℝ) ∈ Set.Icc P (2 * P) := by
      intro t ht
      have ht_lo1 : (⌈a⌉₊ : ℝ) / y₁ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht.1
      have ht_lo2 : (⌈a⌉₊ : ℝ) / y₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht.1
      have ht_hi1 : t ≤ (⌊b⌋₊ : ℝ) / y₁ := le_trans ht.2 (le_trans (min_le_right _ _) (min_le_left _ _))
      have ht_hi2 : t ≤ (⌊b⌋₊ : ℝ) / y₂ := le_trans ht.2 (le_trans (min_le_right _ _) (min_le_right _ _))
      have h1a : P ≤ t * y₁ := le_trans hPa (le_trans (Nat.le_ceil a) ((div_le_iff₀ hy₁_pos).mp ht_lo1))
      have h1b : t * y₁ ≤ 2 * P := le_trans ((le_div_iff₀ hy₁_pos).mp ht_hi1) (le_trans (Nat.floor_le (by linarith)) hb2P)
      have h2a : P ≤ t * y₂ := le_trans hPa (le_trans (Nat.le_ceil a) ((div_le_iff₀ hy₂_pos).mp ht_lo2))
      have h2b : t * y₂ ≤ 2 * P := le_trans ((le_div_iff₀ hy₂_pos).mp ht_hi2) (le_trans (Nat.floor_le (by linarith)) hb2P)
      exact ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩
    have hx_mem_ab : ∀ x ∈ Finset.Icc ⌈a₁₂⌉₊ ⌊b₁₂⌋₊, (x : ℝ) ∈ Set.Icc a₁₂ b₁₂ := fun x hx =>
      ⟨le_trans (Nat.le_ceil a₁₂) (by exact_mod_cast (Finset.mem_Icc.mp hx).1),
        le_trans (by exact_mod_cast (Finset.mem_Icc.mp hx).2) (Nat.floor_le hb₁₂_nn)⟩
    have hw₁₂_bd : ∀ x ∈ Finset.Icc ⌈a₁₂⌉₊ ⌊b₁₂⌋₊, |w₁₂ x| ≤ 2 * W₀ ^ 2 := by
      intro x hx
      dsimp only [w₁₂]
      rw [abs_mul]
      have h1 := hw_bd _ (hmem_P2P (x : ℝ) (hx_mem_ab x hx)).1
      have h2 := hw_bd _ (hmem_P2P (x : ℝ) (hx_mem_ab x hx)).2
      have hsq : |w (x * y₁)| * |w (x * y₂)| ≤ W₀ ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hW₀
      linarith [sq_nonneg W₀]
    have hw₁₂_tv : ∑ x ∈ Finset.Ico ⌈a₁₂⌉₊ ⌊b₁₂⌋₊, |w₁₂ (x + 1) - w₁₂ x| ≤ 2 * W₀ ^ 2 := by
      have hP_pos : 0 < P := by linarith
      have hstep : ∀ x ∈ Finset.Ico ⌈a₁₂⌉₊ ⌊b₁₂⌋₊,
          |w₁₂ (x + 1) - w₁₂ x| ≤
            W₀ * |w ((y₁ * (x + 1) : ℕ) : ℝ) - w ((y₁ * x : ℕ) : ℝ)| +
            W₀ * |w ((y₂ * (x + 1) : ℕ) : ℝ) - w ((y₂ * x : ℕ) : ℝ)| := by
        intro x hx
        rw [Finset.mem_Ico] at hx
        have hx_mem : x ∈ Finset.Icc ⌈a₁₂⌉₊ ⌊b₁₂⌋₊ := Finset.mem_Icc.mpr ⟨hx.1, hx.2.le⟩
        have hx1_mem : x + 1 ∈ Finset.Icc ⌈a₁₂⌉₊ ⌊b₁₂⌋₊ := Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
        have hsplit : w₁₂ (x + 1) - w₁₂ x =
            w (((x + 1 : ℕ) : ℝ) * y₂) * (w ((y₁ * (x + 1) : ℕ) : ℝ) - w ((y₁ * x : ℕ) : ℝ)) +
            w ((x : ℝ) * y₁) * (w ((y₂ * (x + 1) : ℕ) : ℝ) - w ((y₂ * x : ℕ) : ℝ)) := by
          dsimp only [w₁₂]
          push_cast
          rw [mul_comm (y₁ : ℝ) ((x : ℝ) + 1), mul_comm (y₁ : ℝ) (x : ℝ),
            mul_comm (y₂ : ℝ) ((x : ℝ) + 1), mul_comm (y₂ : ℝ) (x : ℝ)]
          ring
        rw [hsplit]
        refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hw_bd _ (hmem_P2P _ (hx_mem_ab _ hx1_mem)).2) (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hw_bd _ (hmem_P2P _ (hx_mem_ab _ hx_mem)).1) (abs_nonneg _)
      have hy1_lo : P ≤ ((y₁ * ⌈a₁₂⌉₊ : ℕ) : ℝ) := by
        have := (hmem_P2P _ (hx_mem_ab ⌈a₁₂⌉₊ (Finset.mem_Icc.mpr ⟨le_rfl, h_empty_nat⟩))).1.1
        push_cast; linarith
      have hy1_hi : ((y₁ * ⌊b₁₂⌋₊ : ℕ) : ℝ) ≤ 2 * P := by
        have := (hmem_P2P _ (hx_mem_ab ⌊b₁₂⌋₊ (Finset.mem_Icc.mpr ⟨h_empty_nat, le_rfl⟩))).1.2
        push_cast; linarith
      have hy2_lo : P ≤ ((y₂ * ⌈a₁₂⌉₊ : ℕ) : ℝ) := by
        have := (hmem_P2P _ (hx_mem_ab ⌈a₁₂⌉₊ (Finset.mem_Icc.mpr ⟨le_rfl, h_empty_nat⟩))).2.1
        push_cast; linarith
      have hy2_hi : ((y₂ * ⌊b₁₂⌋₊ : ℕ) : ℝ) ≤ 2 * P := by
        have := (hmem_P2P _ (hx_mem_ab ⌊b₁₂⌋₊ (Finset.mem_Icc.mpr ⟨h_empty_nat, le_rfl⟩))).2.2
        push_cast; linarith
      have htv1 := discrete_tv_scale_le hP_pos hw_diff hw_tv y₁ ⌈a₁₂⌉₊ ⌊b₁₂⌋₊ h_empty_nat hy1_lo hy1_hi
      have htv2 := discrete_tv_scale_le hP_pos hw_diff hw_tv y₂ ⌈a₁₂⌉₊ ⌊b₁₂⌋₊ h_empty_nat hy2_lo hy2_hi
      calc ∑ x ∈ Finset.Ico ⌈a₁₂⌉₊ ⌊b₁₂⌋₊, |w₁₂ (x + 1) - w₁₂ x|
          ≤ ∑ x ∈ Finset.Ico ⌈a₁₂⌉₊ ⌊b₁₂⌋₊,
              (W₀ * |w ((y₁ * (x + 1) : ℕ) : ℝ) - w ((y₁ * x : ℕ) : ℝ)| +
                W₀ * |w ((y₂ * (x + 1) : ℕ) : ℝ) - w ((y₂ * x : ℕ) : ℝ)|) := Finset.sum_le_sum hstep
        _ = W₀ * (∑ x ∈ Finset.Ico ⌈a₁₂⌉₊ ⌊b₁₂⌋₊, |w ((y₁ * (x + 1) : ℕ) : ℝ) - w ((y₁ * x : ℕ) : ℝ)|) +
            W₀ * (∑ x ∈ Finset.Ico ⌈a₁₂⌉₊ ⌊b₁₂⌋₊, |w ((y₂ * (x + 1) : ℕ) : ℝ) - w ((y₂ * x : ℕ) : ℝ)|) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ W₀ * W₀ + W₀ * W₀ := add_le_add (mul_le_mul_of_nonneg_left htv1 hW₀) (mul_le_mul_of_nonneg_left htv2 hW₀)
        _ = 2 * W₀ ^ 2 := by ring
    set E : ℝ := C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := mul_nonneg hC_exp.le hTy_rhs_nn
    have hn_pos : (0 : ℝ) < n := by
      by_contra h0
      have hn0 : n = 0 := by exact_mod_cast le_antisymm (not_lt.mp h0) (Nat.cast_nonneg n)
      subst hn0
      simp at hT₀_ge1
      linarith
    have hsum_bd : ∀ u : ℕ, ⌈a₁₂⌉₊ ≤ u → u ≤ ⌊b₁₂⌋₊ →
        ‖∑ x ∈ Finset.Icc ⌈a₁₂⌉₊ u,
            ePhase ((∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₁ : ℕ) : ℝ) ^ r)) -
              (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₂ : ℕ) : ℝ) ^ r)))‖ ≤ E := by
      intro u hau hub
      have ha₁₂_u : a₁₂ ≤ (u : ℝ) := le_trans (Nat.le_ceil a₁₂) (by exact_mod_cast hau)
      have hu_2a₁₂ : (u : ℝ) ≤ 2 * a₁₂ := le_trans (by
        have h1 : (⌊b₁₂⌋₊ : ℝ) ≤ b₁₂ := Nat.floor_le (by
          simp only [b₁₂, le_min_iff]
          exact ⟨Nat.cast_nonneg _, div_nonneg (Nat.cast_nonneg _) hy₁_pos.le,
            div_nonneg (Nat.cast_nonneg _) hy₂_pos.le⟩)
        exact le_trans (by exact_mod_cast hub) h1) hb₁₂_2a
      have hu_2X₁ : (u : ℝ) ≤ 2 * (X₁ : ℝ) := by
        have h1 : (⌊b₁₂⌋₊ : ℝ) ≤ b₁₂ := Nat.floor_le (by
          simp only [b₁₂, le_min_iff]
          exact ⟨Nat.cast_nonneg _, div_nonneg (Nat.cast_nonneg _) hy₁_pos.le,
            div_nonneg (Nat.cast_nonneg _) hy₂_pos.le⟩)
        exact le_trans (by exact_mod_cast hub) (le_trans h1 (le_trans (min_le_left _ _) (by exact_mod_cast hX_top)))
      let cy : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))
      have hcy0 : cy r₀ ≠ 0 := by
        dsimp only [cy]
        have hh0R : (h r₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hh₀
        have hpow_ne : (y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)) ≠ 0 := by
          intro heq
          have h1 : (y₁ : ℝ) ^ r₀ = (y₂ : ℝ) ^ r₀ := by
            rw [sub_eq_zero, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_inj] at heq
            exact heq
          have h2 : (y₁ : ℝ) = (y₂ : ℝ) :=
            (pow_left_inj₀ hy₁_pos.le hy₂_pos.le (by have := (hA r₀ hr₀).1; omega)).mp h1
          exact hy_ne (by exact_mod_cast h2)
        exact mul_ne_zero (div_ne_zero (mul_ne_zero hh0R hn_pos.ne') (by positivity)) hpow_ne
      have hphase_eq : ∀ x ∈ Finset.Icc ⌈a₁₂⌉₊ u,
          (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₁ : ℕ) : ℝ) ^ r)) -
            (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₂ : ℕ) : ℝ) ^ r)) =
          ∑ r ∈ A, cy r * (x : ℝ) ^ (-(r : ℤ)) := by
        intro x _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        dsimp only [cy]
        simp only [Nat.cast_mul, mul_pow, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv]; ring
      have hsum_eq : ∑ x ∈ Finset.Icc ⌈a₁₂⌉₊ u,
            ePhase ((∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₁ : ℕ) : ℝ) ^ r)) -
              (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₂ : ℕ) : ℝ) ^ r))) =
          ∑ x ∈ Finset.Icc ⌈a₁₂⌉₊ u, ePhase (∑ r ∈ A, cy r * (x : ℝ) ^ (-(r : ℤ))) :=
        Finset.sum_congr rfl fun x hx => by rw [hphase_eq x hx]
      rw [hsum_eq]
      have hM0_a : M₀ ≤ a₁₂ := le_trans hM₀_X₁ (le_max_left _ _)
      have hdom_u : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |cy r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a₁₂ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|cy r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) := by
        intro k hk r hr hne
        have ha_pow : a₁₂ ^ (-(r : ℤ)) ≤ (X₁ : ℝ) ^ (-(r : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hX₁_pos r) (pow_le_pow_left₀ hX₁_pos.le (le_max_left _ _) r)
        have hu_pow : (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_2X₁ r₀)
        calc |cy r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a₁₂ ^ (-(r : ℤ))
            ≤ |cy r| * (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) :=
              mul_le_mul_of_nonneg_left ha_pow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
          _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                (|cy r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ))) :=
              hdom_y k hk r hr hne
          _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                (|cy r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_pow
                (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (by positivity)
      have hTu_ub : |cy r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (K_max - 1) := by
        have h1 : (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (X₁ : ℝ) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hX₁_pos r₀) (pow_le_pow_left₀ hX₁_pos.le (le_trans (le_max_left _ _) ha₁₂_u) r₀)
        have h2 : (X₁ : ℝ) ^ (K_max - 1) ≤ (u : ℝ) ^ (K_max - 1) :=
          pow_le_pow_left₀ hX₁_pos.le (le_trans (le_max_left _ _) ha₁₂_u) _
        calc |cy r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))
            ≤ |cy r₀| * (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (X₁ : ℝ) ^ (K_max - 1) := hT_ub
          _ ≤ (u : ℝ) ^ (K_max - 1) := h2
      have hhexp := hexp A r₀ hr₀ hA cy hcy0 a₁₂ (u : ℝ) hM0_a ha₁₂_u hu_2a₁₂ hdom_u hTu_ub
      rw [Nat.floor_natCast] at hhexp
      have hTy_le : T_y ≤ |cy r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
        have hdiff_lo := (y_pow_diff_bounds r₀ (hA r₀ hr₀).1 Y₁ y₁ y₂ hY₁_pos
          (by exact_mod_cast hy₁_lo) (by exact_mod_cast hy₁_hi)
          (by exact_mod_cast hy₂_lo) (by exact_mod_cast hy₂_hi)).1
        have hupow : (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_2X₁ r₀)
        have hXY_pow : (P : ℝ) ^ (-(r₀ : ℤ)) ≤ (2 : ℝ) ^ (3 * R) * ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) := by
          rw [zpow_neg, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, ← mul_inv]
          have h1 : (2 * (X₁ : ℝ)) * (Y₁ : ℝ) ≤ (2 : ℝ) ^ 3 * P := by linarith [hXY_hi]
          have h2 : ((2 * (X₁ : ℝ)) * (Y₁ : ℝ)) ^ r₀ ≤ (2 : ℝ) ^ (3 * R) * P ^ r₀ := by
            calc ((2 * (X₁ : ℝ)) * (Y₁ : ℝ)) ^ r₀ ≤ ((2 : ℝ) ^ 3 * P) ^ r₀ := pow_le_pow_left₀ (by positivity) h1 r₀
              _ = (2 : ℝ) ^ (3 * r₀) * P ^ r₀ := by rw [mul_pow, ← pow_mul]
              _ ≤ (2 : ℝ) ^ (3 * R) * P ^ r₀ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 3 (hA r₀ hr₀).2)) (by positivity)
          rw [← mul_pow, le_mul_inv_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
          linarith
        have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
        have h2_le : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * (2 : ℝ) ^ (3 * R) ≤ (q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) := by
          have hpow2 : (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (2 : ℝ) ^ (3 * R) ≤ (2 : ℝ) ^ (-(2 * r₀ : ℤ)) := by
            rw [← zpow_natCast (2 : ℝ) (3 * R), ← zpow_add₀ (by norm_num)]
            refine zpow_le_zpow_right₀ (by norm_num) ?_
            have hrR : r₀ ≤ R := (hA r₀ hr₀).2
            zify [hrR]; omega
          calc ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * (2 : ℝ) ^ (3 * R)
              = (q_den : ℝ)⁻¹ * ((2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (2 : ℝ) ^ (3 * R)) := by ring
            _ ≤ (q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) :=
                mul_le_mul_of_nonneg_left hpow2 (by positivity)
        dsimp only [T_y, T₀, cy]
        rw [abs_mul, abs_div, abs_mul, abs_of_pos hn_pos, abs_of_pos (a := (q_den : ℝ)) (by positivity)]
        calc ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * (|(h r₀ : ℝ)| * n / P ^ r₀) * (|(y₁ : ℝ) - y₂| / Y₁)
            = |(h r₀ : ℝ)| * n * ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * P ^ (-(r₀ : ℤ)) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by
              rw [zpow_neg P (r₀ : ℤ), zpow_natCast P r₀, zpow_neg_one]; ring
          _ ≤ |(h r₀ : ℝ)| * n * (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * (2 : ℝ) ^ (3 * R)) *
                ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by
              have hmul1 : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * P ^ (-(r₀ : ℤ)) ≤
                  ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * (2 : ℝ) ^ (3 * R) *
                    ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) := by
                rw [mul_assoc _ ((2 : ℝ) ^ (3 * R))]; exact mul_le_mul_of_nonneg_left hXY_pow (by positivity)
              have hnn : 0 ≤ |(h r₀ : ℝ)| * n := by positivity
              calc |(h r₀ : ℝ)| * n * ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * P ^ (-(r₀ : ℤ)) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ)
                  = (|(h r₀ : ℝ)| * n) * (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * P ^ (-(r₀ : ℤ))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by ring
                _ ≤ (|(h r₀ : ℝ)| * n) * (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * (2 : ℝ) ^ (3 * R) *
                      ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ)))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul1 hnn) (abs_nonneg _)) (by positivity)
                _ = _ := by ring
          _ ≤ |(h r₀ : ℝ)| * n * ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(2 * r₀ : ℤ))) *
                ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h2_le (by positivity)) (by positivity)) (abs_nonneg _)) (by positivity)
          _ = (|(h r₀ : ℝ)| * n / (q_den : ℝ)) * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) *
                (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := by
              rw [show -(r₀ + 1 : ℤ) = -(r₀ : ℤ) + (-1 : ℤ) by omega, zpow_add₀ hY₁_pos.ne']
              ring
          _ ≤ (|(h r₀ : ℝ)| * n / (q_den : ℝ)) * ((r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) *
                (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
              calc |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))
                  = 1 * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) := (one_mul _).symm
                _ ≤ (r₀ : ℝ) * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) :=
                    mul_le_mul_of_nonneg_right hr0_1 (by positivity)
                _ = _ := by ring
          _ ≤ (|(h r₀ : ℝ)| * n / (q_den : ℝ) * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) *
                (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
              have hle1 : |(h r₀ : ℝ)| * n / (q_den : ℝ) * ((r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) ≤
                  |(h r₀ : ℝ)| * n / (q_den : ℝ) * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| :=
                mul_le_mul_of_nonneg_left hdiff_lo (by positivity)
              calc (|(h r₀ : ℝ)| * n / (q_den : ℝ)) * ((r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) *
                    (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ))
                  ≤ (|(h r₀ : ℝ)| * n / (q_den : ℝ) * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) *
                      (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := mul_le_mul_of_nonneg_right hle1 (by positivity)
                _ ≤ (|(h r₀ : ℝ)| * n / (q_den : ℝ) * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) *
                      (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
                    rw [mul_assoc _ (r₀ : ℝ)]
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    calc (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) = 1 * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := (one_mul _).symm
                      _ ≤ (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := mul_le_mul hr0_1 hupow (by positivity) (by positivity)
      refine le_trans hhexp ?_
      dsimp only [E]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC_exp.le
      · exact div_le_div₀ (by positivity) hu_2X₁ (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (max_le_max hTy_le le_rfl)
      · exact Real.rpow_le_rpow (by positivity) hu_2X₁ (by linarith)
    have hps := abel_summation_Icc h_empty_nat (by positivity : 0 ≤ 2 * W₀ ^ 2) (by positivity : 0 ≤ 2 * W₀ ^ 2)
      hE_nn hw₁₂_bd hw₁₂_tv hsum_bd
    calc ‖∑ x ∈ Finset.Icc ⌈a₁₂⌉₊ ⌊b₁₂⌋₊,
            (w (x * y₁) * w (x * y₂) : ℂ) *
              ePhase ((∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₁ : ℕ) : ℝ) ^ r)) -
                (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y₂ : ℕ) : ℝ) ^ r)))‖
        ≤ (2 * W₀ ^ 2 + 2 * W₀ ^ 2) * E := by simpa [w₁₂] using hps
      _ = 4 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) := by
          dsimp only [E]; ring
      _ ≤ 8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) := by
          have hnn : 0 ≤ W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) :=
            mul_nonneg (mul_nonneg (sq_nonneg W₀) hC_exp.le) hTy_rhs_nn
          linarith


lemma type_II_block_bound_mod (q_den : ℕ) (hq_den : 1 ≤ q_den)
    (R K_max : ℕ) (hK_max : 3 ≤ K_max)
    (C_exp η_exp M₀ : ℝ) (hC_exp : 0 < C_exp) (hη_exp : 0 < η_exp) (hη_le : η_exp ≤ 1 / 4) (hM₀ : 16 ≤ M₀)
    (hexp : ∀ (A : Finset ℕ) (r₀ : ℕ) (hr₀ : r₀ ∈ A) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
        (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (M₁ M₂ : ℝ),
        M₀ ≤ M₁ → M₁ ≤ M₂ → M₂ ≤ 2 * M₁ →
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) →
        let T := |c r₀| * (r₀ : ℝ) * M₂ ^ (-(r₀ : ℤ))
        T ≤ M₂ ^ (K_max - 1) →
        ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (∑ r ∈ A, c r * (m : ℝ) ^ (-(r : ℤ)))‖ ≤
          C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)))
    (n : ℕ) (P a b : ℝ) (hP1 : 1 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hb2P : b ≤ 2 * P)
    (A : Finset ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R) (r₀ : ℕ) (hr₀ : r₀ ∈ A)
    (h : ℕ → ℤ) (hh₀ : h r₀ ≠ 0) (w : ℝ → ℝ) (W₀ : ℝ) (hW₀ : 0 ≤ W₀)
    (hw_bd : ∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀)
    (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (X₁ X_top Y₁ Y₂ : ℕ) (hX₁ : 1 ≤ X₁) (hM₀_X₁ : M₀ ≤ (X₁ : ℝ)) (hX_top : X_top ≤ 2 * X₁)
    (hY₁ : 1 ≤ Y₁) (hY₂ : Y₁ ≤ Y₂) (hY₂_2 : Y₂ ≤ 2 * Y₁)
    (hXY_hi : (2 * X₁ : ℝ) * (2 * Y₁ : ℝ) ≤ 16 * P)
    (hX_sqrt : (X₁ : ℝ) ≤ 2 * Real.sqrt P)
    (a_coeff b_coeff : ℕ → ℂ)
    (A_norm B_norm : ℝ) (hA_norm : ∑ x ∈ Finset.Icc X₁ X_top, ‖a_coeff x‖ ^ 2 ≤ A_norm)
    (hB_norm : ∑ y ∈ Finset.Icc Y₁ Y₂, ‖b_coeff y‖ ^ 2 ≤ B_norm)
    (hA_nn : 0 ≤ A_norm) (hB_nn : 0 ≤ B_norm)
    (hdom_all : ∀ y₁ ∈ Finset.Icc Y₁ Y₂, ∀ y₂ ∈ Finset.Icc Y₁ Y₂, y₁ ≠ y₂ →
      (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
        |(h r : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))| *
            (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) ≤
          (1 / (2 * max (A.card : ℝ) 1)) *
            (|(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
              (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)))) ∧
      |(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
          (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) ≤ (X₁ : ℝ) ^ (K_max - 1)) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    1 ≤ T₀ →
    ‖∑ x ∈ Finset.Icc X₁ X_top, a_coeff x *
        ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) *
            ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 ≤
      A_norm * B_norm * W₀ ^ 2 *
        (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
          128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
          128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
  intro T₀ hT₀_ge1
  have hX₁_pos : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
  have hY₁_pos : (0 : ℝ) < Y₁ := by exact_mod_cast hY₁
  have hP_pos : 0 < P := by linarith
  have hCS : ‖∑ x ∈ Finset.Icc X₁ X_top, a_coeff x *
        ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) *
            ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 ≤
      (∑ x ∈ Finset.Icc X₁ X_top, ‖a_coeff x‖ ^ 2) *
        ∑ x ∈ Finset.Icc X₁ X_top,
          ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
            b_coeff y * (w (x * y) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 := by
    calc ‖∑ x ∈ Finset.Icc X₁ X_top, _‖ ^ 2
        ≤ (∑ x ∈ Finset.Icc X₁ X_top, ‖a_coeff x‖ *
            ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊), _‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
          rw [norm_mul]
      _ ≤ (∑ x ∈ Finset.Icc X₁ X_top, ‖a_coeff x‖ ^ 2) *
            ∑ x ∈ Finset.Icc X₁ X_top, ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊), _‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- Expand inner square
  let F : ℕ → ℝ := fun m => ∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * (m : ℝ) ^ r)
  have hexp_sq : ∑ x ∈ Finset.Icc X₁ X_top,
        ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) * ePhase (F (x * y))‖ ^ 2 =
      (∑ y₁ ∈ Finset.Icc Y₁ Y₂, ∑ y₂ ∈ Finset.Icc Y₁ Y₂,
        b_coeff y₁ * star (b_coeff y₂) *
          ∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * y₁ ∧ x * y₁ ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * y₂ ∧ x * y₂ ≤ ⌊b⌋₊),
            (w (x * y₁) * w (x * y₂) : ℂ) * ePhase (F (x * y₁) - F (x * y₂))).re := by
    have hpt : ∀ x ∈ Finset.Icc X₁ X_top,
        ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) * ePhase (F (x * y))‖ ^ 2 =
        (∑ y₁ ∈ Finset.Icc Y₁ Y₂, ∑ y₂ ∈ Finset.Icc Y₁ Y₂,
          if (⌈a⌉₊ ≤ x * y₁ ∧ x * y₁ ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * y₂ ∧ x * y₂ ≤ ⌊b⌋₊) then
            b_coeff y₁ * star (b_coeff y₂) *
              ((w (x * y₁) * w (x * y₂) : ℂ) * ePhase (F (x * y₁) - F (x * y₂)))
          else 0).re := by
      intro x _
      classical
      have hns : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := fun z => by
        rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj]; simp
      rw [hns]
      congr 1
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y₁ _ => ?_
      by_cases h1a : ⌈a⌉₊ ≤ x * y₁ <;> by_cases h1b : x * y₁ ≤ ⌊b⌋₊
      · simp only [h1a, h1b, true_and, ↓reduceIte]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun y₂ _ => ?_
        by_cases h2a : ⌈a⌉₊ ≤ x * y₂ <;> by_cases h2b : x * y₂ ≤ ⌊b⌋₊
        · simp only [h2a, h2b, true_and, and_true, ↓reduceIte]
          rw [star_mul, star_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def,
            ← ePhase_mul_star]
          push_cast; ring
        · simp only [h2a, h2b, false_and, and_false, ↓reduceIte, mul_zero]
        · simp only [h2a, h2b, false_and, and_false, ↓reduceIte, mul_zero]
        · simp only [h2a, h2b, false_and, and_false, ↓reduceIte, mul_zero]
      · simp only [h1a, h1b, false_and, and_false, ↓reduceIte, zero_mul, Finset.sum_const_zero]
      · simp only [h1a, h1b, false_and, and_false, ↓reduceIte, zero_mul, Finset.sum_const_zero]
      · simp only [h1a, h1b, false_and, and_false, ↓reduceIte, zero_mul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl hpt, ← Complex.re_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y₂ _ => ?_
    rw [← Finset.sum_filter, Finset.mul_sum]
  have hre_le : ∑ x ∈ Finset.Icc X₁ X_top,
        ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) * ePhase (F (x * y))‖ ^ 2 ≤
      ∑ p ∈ Finset.Icc Y₁ Y₂ ×ˢ Finset.Icc Y₁ Y₂,
        ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ := by
    rw [hexp_sq]
    refine le_trans (Complex.re_le_norm _) ?_
    rw [← Finset.sum_product (s := Finset.Icc Y₁ Y₂) (t := Finset.Icc Y₁ Y₂) (f := fun p => b_coeff p.1 * star (b_coeff p.2) * ∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊), (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2)))]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
  set D : ℝ := (Y₁ : ℝ) * T₀ ^ (-1 / 3 : ℝ)
  have hD_nn : 0 ≤ D := by positivity
  let Near := (Finset.Icc Y₁ Y₂ ×ˢ Finset.Icc Y₁ Y₂).filter (fun p => |(p.1 : ℝ) - p.2| ≤ D)
  let Far := (Finset.Icc Y₁ Y₂ ×ˢ Finset.Icc Y₁ Y₂).filter (fun p => ¬ |(p.1 : ℝ) - p.2| ≤ D)
  have hsplit : ∑ p ∈ Finset.Icc Y₁ Y₂ ×ˢ Finset.Icc Y₁ Y₂,
        ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ =
      (∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖) +
      (∑ p ∈ Far, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖) := by
    dsimp only [Near, Far]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hNear_bd : ∑ p ∈ Near,
        ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ ≤
      B_norm * W₀ ^ 2 * (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ)) := by
    have hinner : ∀ p ∈ Near,
        ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
          (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ ≤
        2 * (X₁ : ℝ) * W₀ ^ 2 := by
      intro p _
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
          ‖(w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ ≤ W₀ ^ 2 := by
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        have h1P : P ≤ (x * p.1 : ℝ) ∧ (x * p.1 : ℝ) ≤ 2 * P :=
          ⟨le_trans hPa (le_trans (Nat.le_ceil a) (by exact_mod_cast hx'.1)),
            le_trans (by exact_mod_cast hx'.2.1) (le_trans (Nat.floor_le (by linarith)) hb2P)⟩
        have h2P : P ≤ (x * p.2 : ℝ) ∧ (x * p.2 : ℝ) ≤ 2 * P :=
          ⟨le_trans hPa (le_trans (Nat.le_ceil a) (by exact_mod_cast hx'.2.2.1)),
            le_trans (by exact_mod_cast hx'.2.2.2) (le_trans (Nat.floor_le (by linarith)) hb2P)⟩
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          norm_ePhase (F (x * p.1) - F (x * p.2)),
          mul_one, sq]
        exact mul_le_mul (hw_bd _ h1P) (hw_bd _ h2P) (abs_nonneg _) hW₀
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_le : (((Finset.Icc X₁ X_top).filter _).card : ℝ) ≤ 2 * (X₁ : ℝ) := by
        have h1 : ((Finset.Icc X₁ X_top).filter _).card ≤ (Finset.Icc X₁ X_top).card := Finset.card_filter_le _ _
        have h2 : (Finset.Icc X₁ X_top).card ≤ X_top := by rw [Nat.card_Icc]; omega
        exact_mod_cast le_trans h1 (le_trans h2 hX_top)
      exact mul_le_mul_of_nonneg_right hcard_le (sq_nonneg W₀)
    have hnear_sum : ∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ ≤ (2 * D + 1) * B_norm := by
      have h1 : ∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ ≤
          ∑ p ∈ Near, (‖b_coeff p.1‖ ^ 2 + ‖b_coeff p.2‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun p _ => by nlinarith [sq_nonneg (‖b_coeff p.1‖ - ‖b_coeff p.2‖)]
      have h2 : ∑ p ∈ Near, ‖b_coeff p.1‖ ^ 2 ≤ (2 * D + 1) * B_norm := by
        have hsub : Near ⊆ (Finset.Icc Y₁ Y₂).biUnion (fun y₁ =>
            ((Finset.Icc Y₁ Y₂).filter (fun y₂ => |(y₁ : ℝ) - y₂| ≤ D)).map ⟨fun y₂ => (y₁, y₂), fun _ _ h => (Prod.ext_iff.mp h).2⟩) := by
          intro ⟨y₁, y₂⟩ hp
          simp only [Near, Finset.mem_filter, Finset.mem_product] at hp
          exact Finset.mem_biUnion.mpr ⟨y₁, hp.1.1, Finset.mem_map.mpr ⟨y₂, Finset.mem_filter.mpr ⟨hp.1.2, hp.2⟩, rfl⟩⟩
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)) ?_
        refine le_trans Finset.sum_biUnion_le ?_
        have hrow : ∀ y₁ ∈ Finset.Icc Y₁ Y₂,
            ∑ p ∈ ((Finset.Icc Y₁ Y₂).filter (fun y₂ => |(y₁ : ℝ) - y₂| ≤ D)).map
              ⟨fun y₂ => (y₁, y₂), fun _ _ h => (Prod.ext_iff.mp h).2⟩, ‖b_coeff p.1‖ ^ 2 ≤
            (2 * D + 1) * ‖b_coeff y₁‖ ^ 2 := by
          intro y₁ _
          rw [Finset.sum_map, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hsub_y : (Finset.Icc Y₁ Y₂).filter (fun y₂ => |(y₁ : ℝ) - y₂| ≤ D) ⊆
              Finset.Icc (y₁ - ⌊D⌋₊) (y₁ + ⌊D⌋₊) := by
            intro y₂ hy₂
            have hyD : |(y₁ : ℝ) - y₂| ≤ D := (Finset.mem_filter.mp hy₂).2
            rw [abs_le] at hyD
            have hfl : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD_nn
            have hlt : D < (⌊D⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one D
            rw [Finset.mem_Icc]
            have hlo : (y₁ : ℤ) - (⌊D⌋₊ : ℤ) ≤ y₂ := by
              have : (y₁ : ℝ) - (⌊D⌋₊ : ℝ) - 1 < y₂ := by linarith
              have : (y₁ : ℤ) - (⌊D⌋₊ : ℤ) - 1 < y₂ := by exact_mod_cast this
              omega
            have hhi : (y₂ : ℤ) ≤ (y₁ : ℤ) + (⌊D⌋₊ : ℤ) := by
              have : (y₂ : ℝ) < (y₁ : ℝ) + (⌊D⌋₊ : ℝ) + 1 := by linarith
              have : (y₂ : ℤ) < (y₁ : ℤ) + (⌊D⌋₊ : ℤ) + 1 := by exact_mod_cast this
              omega
            omega
          have hcard_le : ((Finset.Icc Y₁ Y₂).filter (fun y₂ => |(y₁ : ℝ) - y₂| ≤ D)).card ≤ 2 * ⌊D⌋₊ + 1 := by
            refine le_trans (Finset.card_le_card hsub_y) ?_
            rw [Nat.card_Icc]; omega
          calc (((Finset.Icc Y₁ Y₂).filter (fun y₂ => |(y₁ : ℝ) - y₂| ≤ D)).card : ℝ)
              ≤ (2 * ⌊D⌋₊ + 1 : ℕ) := by exact_mod_cast hcard_le
            _ ≤ 2 * D + 1 := by push_cast; linarith [Nat.floor_le hD_nn]
        calc ∑ y₁ ∈ Finset.Icc Y₁ Y₂, ∑ p ∈ ((Finset.Icc Y₁ Y₂).filter _).map _, ‖b_coeff p.1‖ ^ 2
            ≤ ∑ y₁ ∈ Finset.Icc Y₁ Y₂, (2 * D + 1) * ‖b_coeff y₁‖ ^ 2 :=
              Finset.sum_le_sum fun y₁ hy₁ => hrow y₁ hy₁
          _ = (2 * D + 1) * ∑ y₁ ∈ Finset.Icc Y₁ Y₂, ‖b_coeff y₁‖ ^ 2 := by rw [Finset.mul_sum]
          _ ≤ (2 * D + 1) * B_norm := mul_le_mul_of_nonneg_left hB_norm (by positivity)
      have h3 : ∑ p ∈ Near, ‖b_coeff p.2‖ ^ 2 ≤ (2 * D + 1) * B_norm := by
        have hsub : Near ⊆ (Finset.Icc Y₁ Y₂).biUnion (fun y₂ =>
            ((Finset.Icc Y₁ Y₂).filter (fun y₁ => |(y₁ : ℝ) - y₂| ≤ D)).map ⟨fun y₁ => (y₁, y₂), fun _ _ h => (Prod.ext_iff.mp h).1⟩) := by
          intro ⟨y₁, y₂⟩ hp
          simp only [Near, Finset.mem_filter, Finset.mem_product] at hp
          exact Finset.mem_biUnion.mpr ⟨y₂, hp.1.2, Finset.mem_map.mpr ⟨y₁, Finset.mem_filter.mpr ⟨hp.1.1, hp.2⟩, rfl⟩⟩
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)) ?_
        refine le_trans Finset.sum_biUnion_le ?_
        have hrow : ∀ y₂ ∈ Finset.Icc Y₁ Y₂,
            ∑ p ∈ ((Finset.Icc Y₁ Y₂).filter (fun y₁ => |(y₁ : ℝ) - y₂| ≤ D)).map
              ⟨fun y₁ => (y₁, y₂), fun _ _ h => (Prod.ext_iff.mp h).1⟩, ‖b_coeff p.2‖ ^ 2 ≤
            (2 * D + 1) * ‖b_coeff y₂‖ ^ 2 := by
          intro y₂ _
          rw [Finset.sum_map, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hsub_y : (Finset.Icc Y₁ Y₂).filter (fun y₁ => |(y₁ : ℝ) - y₂| ≤ D) ⊆
              Finset.Icc (y₂ - ⌊D⌋₊) (y₂ + ⌊D⌋₊) := by
            intro y₁ hy₁
            have hyD : |(y₁ : ℝ) - y₂| ≤ D := (Finset.mem_filter.mp hy₁).2
            rw [abs_le] at hyD
            have hfl : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD_nn
            have hlt : D < (⌊D⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one D
            rw [Finset.mem_Icc]
            have hlo : (y₂ : ℤ) - (⌊D⌋₊ : ℤ) ≤ y₁ := by
              have : (y₂ : ℝ) - (⌊D⌋₊ : ℝ) - 1 < y₁ := by linarith
              have : (y₂ : ℤ) - (⌊D⌋₊ : ℤ) - 1 < y₁ := by exact_mod_cast this
              omega
            have hhi : (y₁ : ℤ) ≤ (y₂ : ℤ) + (⌊D⌋₊ : ℤ) := by
              have : (y₁ : ℝ) < (y₂ : ℝ) + (⌊D⌋₊ : ℝ) + 1 := by linarith
              have : (y₁ : ℤ) < (y₂ : ℤ) + (⌊D⌋₊ : ℤ) + 1 := by exact_mod_cast this
              omega
            omega
          have hcard_le : ((Finset.Icc Y₁ Y₂).filter (fun y₁ => |(y₁ : ℝ) - y₂| ≤ D)).card ≤ 2 * ⌊D⌋₊ + 1 := by
            refine le_trans (Finset.card_le_card hsub_y) ?_
            rw [Nat.card_Icc]; omega
          calc (((Finset.Icc Y₁ Y₂).filter (fun y₁ => |(y₁ : ℝ) - y₂| ≤ D)).card : ℝ)
              ≤ (2 * ⌊D⌋₊ + 1 : ℕ) := by exact_mod_cast hcard_le
            _ ≤ 2 * D + 1 := by push_cast; linarith [Nat.floor_le hD_nn]
        calc ∑ y₂ ∈ Finset.Icc Y₁ Y₂, ∑ p ∈ ((Finset.Icc Y₁ Y₂).filter _).map _, ‖b_coeff p.2‖ ^ 2
            ≤ ∑ y₂ ∈ Finset.Icc Y₁ Y₂, (2 * D + 1) * ‖b_coeff y₂‖ ^ 2 :=
              Finset.sum_le_sum fun y₂ hy₂ => hrow y₂ hy₂
          _ = (2 * D + 1) * ∑ y₂ ∈ Finset.Icc Y₁ Y₂, ‖b_coeff y₂‖ ^ 2 := by rw [Finset.mul_sum]
          _ ≤ (2 * D + 1) * B_norm := mul_le_mul_of_nonneg_left hB_norm (by positivity)
      rw [← Finset.sum_div, Finset.sum_add_distrib] at h1
      linarith
    have hX1_Y1 : (X₁ : ℝ) * (Y₁ : ℝ) ≤ 4 * P := by linarith [hXY_hi]
    have hX_sqrt' : (X₁ : ℝ) ≤ 2 * P ^ (1 / 2 : ℝ) := by
      rwa [Real.sqrt_eq_rpow] at hX_sqrt
    calc ∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ * ‖∑ x ∈ _, _‖
        ≤ ∑ p ∈ Near, (‖b_coeff p.1‖ * ‖b_coeff p.2‖) * (2 * (X₁ : ℝ) * W₀ ^ 2) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hinner p hp) (by positivity)
      _ = (∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖) * (2 * (X₁ : ℝ) * W₀ ^ 2) := by rw [Finset.sum_mul]
      _ ≤ ((2 * D + 1) * B_norm) * (2 * (X₁ : ℝ) * W₀ ^ 2) :=
          mul_le_mul_of_nonneg_right hnear_sum (by positivity)
      _ = B_norm * W₀ ^ 2 * (4 * ((X₁ : ℝ) * (Y₁ : ℝ)) * T₀ ^ (-1 / 3 : ℝ) + 2 * (X₁ : ℝ)) := by
          dsimp only [D]; ring
      _ ≤ B_norm * W₀ ^ 2 * (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ (by linarith)) (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hFar_bd : ∑ p ∈ Far,
        ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ ≤
      B_norm * W₀ ^ 2 * (32 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
        32 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
    have hinner : ∀ p ∈ Far,
        ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
          (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ ≤
        8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
          (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
      intro ⟨y₁, y₂⟩ hp
      simp only [Far, Finset.mem_filter, Finset.mem_product, not_le] at hp
      have hy_ne : y₁ ≠ y₂ := by
        intro heq; subst heq; rw [sub_self, abs_zero] at hp; linarith [hp.2, hD_nn]
      have hy₁_mem := (Finset.mem_Icc.mp hp.1.1)
      have hy₂_mem := (Finset.mem_Icc.mp hp.1.2)
      have hdom_pair := hdom_all y₁ hp.1.1 y₂ hp.1.2 hy_ne
      have h_in := type_II_inner_sum_bound_mod q_den hq_den R K_max hK_max C_exp η_exp M₀ hC_exp hη_exp hη_le hM₀ hexp
        n P a b hP1 hPa hab hb2P A hA r₀ hr₀ h hh₀ w W₀ hW₀ hw_bd hw_diff hw_tv
        X₁ X_top Y₁ hX₁ hM₀_X₁ hX_top hY₁ hXY_hi y₁ y₂ hy₁_mem.1 hy₁_mem.2 hy₂_mem.1 hy₂_mem.2 hy_ne
        hdom_pair.1 hdom_pair.2 hT₀_ge1
      dsimp only at h_in
      set T_y := ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ * (|(y₁ : ℝ) - y₂| / Y₁)
      have hTy_gt : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ ^ (2 / 3 : ℝ) ≤ T_y := by
        dsimp only [T_y]
        have hdiff_gt : T₀ ^ (-1 / 3 : ℝ) < |(y₁ : ℝ) - y₂| / Y₁ := by
          rw [lt_div_iff₀ hY₁_pos]; linarith [hp.2]
        have hT_eq : T₀ * T₀ ^ (-1 / 3 : ℝ) = T₀ ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_one T₀, ← Real.rpow_add (by linarith)]
          norm_num; rw [Real.rpow_one]
        calc ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ ^ (2 / 3 : ℝ)
            = ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ * T₀ ^ (-1 / 3 : ℝ) := by rw [← hT_eq]; ring
          _ ≤ ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ * (|(y₁ : ℝ) - y₂| / Y₁) :=
              mul_le_mul_of_nonneg_left hdiff_gt.le (by positivity)
      have hdiv_le : (2 * (X₁ : ℝ)) / max T_y 1 ≤
          (2 * (X₁ : ℝ)) * (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ)) := by
        have h1 : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ ^ (2 / 3 : ℝ) ≤ max T_y 1 :=
          le_trans hTy_gt (le_max_left _ _)
        calc (2 * (X₁ : ℝ)) / max T_y 1
            ≤ (2 * (X₁ : ℝ)) / (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(5 * R + 1 : ℤ))) * T₀ ^ (2 / 3 : ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) h1
          _ = (2 * (X₁ : ℝ)) * (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ)) := by
              rw [div_eq_mul_inv, mul_inv, inv_inv, zpow_neg, zpow_natCast, inv_inv,
                ← Real.rpow_neg (by linarith), show -(2 / 3 : ℝ) = -2 / 3 by norm_num]
              ring
      have hpow_eq : (2 * (X₁ : ℝ)) ^ (1 - η_exp) = (2 * (X₁ : ℝ)) * (2 * (X₁ : ℝ)) ^ (-η_exp) := by
        rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
      refine le_trans h_in ?_
      rw [hpow_eq]
      calc 8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + 2 * (X₁ : ℝ) * (2 * (X₁ : ℝ)) ^ (-η_exp))
          ≤ 8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) * (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ)) +
              2 * (X₁ : ℝ) * (2 * (X₁ : ℝ)) ^ (-η_exp)) :=
            mul_le_mul_of_nonneg_left (add_le_add hdiv_le le_rfl) (by positivity)
        _ = 8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp)) := by ring
    have hfar_sum : ∑ p ∈ Far, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ ≤ 2 * (Y₁ : ℝ) * B_norm := by
      have hsub : Far ⊆ Finset.Icc Y₁ Y₂ ×ˢ Finset.Icc Y₁ Y₂ := Finset.filter_subset _ _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
      rw [Finset.sum_product, ← Finset.sum_mul_sum]
      have h1 : (∑ y ∈ Finset.Icc Y₁ Y₂, ‖b_coeff y‖) ^ 2 ≤ ((Finset.Icc Y₁ Y₂).card : ℝ) * B_norm := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc Y₁ Y₂) (fun _ => (1 : ℝ)) (fun y => ‖b_coeff y‖)
        simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
        exact le_trans hcs (mul_le_mul_of_nonneg_left hB_norm (Nat.cast_nonneg _))
      have hcard : ((Finset.Icc Y₁ Y₂).card : ℝ) ≤ 2 * (Y₁ : ℝ) := by
        have : (Finset.Icc Y₁ Y₂).card ≤ Y₂ := by rw [Nat.card_Icc]; omega
        exact_mod_cast le_trans this hY₂_2
      rw [← sq]
      exact le_trans h1 (mul_le_mul_of_nonneg_right hcard hB_nn)
    calc ∑ p ∈ Far, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ * ‖∑ x ∈ _, _‖
        ≤ ∑ p ∈ Far, (‖b_coeff p.1‖ * ‖b_coeff p.2‖) *
            (8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hinner p hp) (by positivity)
      _ = (∑ p ∈ Far, ‖b_coeff p.1‖ * ‖b_coeff p.2‖) *
            (8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) := by rw [Finset.sum_mul]
      _ ≤ (2 * (Y₁ : ℝ) * B_norm) *
            (8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) :=
          mul_le_mul_of_nonneg_right hfar_sum (by positivity)
      _ = B_norm * W₀ ^ 2 * (8 * ((2 * (X₁ : ℝ)) * (2 * (Y₁ : ℝ))) * C_exp *
            (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) := by ring
      _ ≤ B_norm * W₀ ^ 2 * (8 * (16 * P) * C_exp *
            (((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY_hi (by norm_num)) hC_exp.le)
            (by positivity)) (by positivity)
      _ = B_norm * W₀ ^ 2 * (32 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
            32 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by ring
  have htot : ∑ x ∈ Finset.Icc X₁ X_top,
        ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) *
            ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 ≤
      B_norm * W₀ ^ 2 *
        (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
          128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
          128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
    refine le_trans hre_le ?_
    rw [hsplit]
    linarith [hNear_bd, hFar_bd]
  exact le_trans hCS (mul_le_mul hA_norm htot (Finset.sum_nonneg fun _ _ => sq_nonneg _) hA_nn)

lemma type_I_no_log_single_d_bound_mod (q_den : ℕ) (hq_den : 1 ≤ q_den)
    (R K_max : ℕ) (hK_max : 3 ≤ K_max)
    (C_exp η_exp M₀ : ℝ) (hC_exp : 0 < C_exp) (hη_exp : 0 < η_exp) (hη_le : η_exp ≤ 1 / 4) (hM₀ : 16 ≤ M₀)
    (hexp : ∀ (A : Finset ℕ) (r₀ : ℕ) (hr₀ : r₀ ∈ A) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
        (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (M₁ M₂ : ℝ),
        M₀ ≤ M₁ → M₁ ≤ M₂ → M₂ ≤ 2 * M₁ →
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) →
        let T := |c r₀| * (r₀ : ℝ) * M₂ ^ (-(r₀ : ℤ))
        T ≤ M₂ ^ (K_max - 1) →
        ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (∑ r ∈ A, c r * (m : ℝ) ^ (-(r : ℤ)))‖ ≤
          C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)))
    (n : ℕ) (P a b : ℝ) (hP1 : 1 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hb2P : b ≤ 2 * P)
    (A : Finset ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R) (r₀ : ℕ) (hr₀ : r₀ ∈ A)
    (h : ℕ → ℤ) (hh₀ : h r₀ ≠ 0) (w : ℝ → ℝ) (W₀ : ℝ) (hW₀ : 0 ≤ W₀)
    (hw_bd : ∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀)
    (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (d : ℕ) (hd1 : 1 ≤ d) (hd_M0 : M₀ ≤ P / (d : ℝ))
    (hdom_d : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
      |(h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))))
    (hT_ub : |(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (K_max - 1)) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
        (w (d * k) : ℂ) *
          ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
      4 * W₀ * max C_exp 3 *
        ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
  intro T₀
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hP_pos : 0 < P := by linarith
  have hPd_pos : 0 < P / d := div_pos hP_pos hd_pos
  have hPd_ge16 : 16 ≤ P / d := le_trans hM₀ hd_M0
  have hPd_ge1 : 1 ≤ P / d := by linarith
  by_cases h_empty : ⌊b⌋₊ / d < (⌈a⌉₊ - 1) / d + 1
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW₀) (by positivity))
      (add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
  · push_neg at h_empty
    set a' : ℝ := (⌈a⌉₊ : ℝ) / d
    set b' : ℝ := (⌊b⌋₊ : ℝ) / d
    have hPa' : P / d ≤ a' := div_le_div_of_nonneg_right (le_trans hPa (Nat.le_ceil a)) hd_pos.le
    have hb'2P : b' ≤ 2 * (P / d) := by
      rw [show 2 * (P / d) = (2 * P) / d by ring]
      exact div_le_div_of_nonneg_right (le_trans (Nat.floor_le (by linarith)) hb2P) hd_pos.le
    have hceil_eq : ⌈a'⌉₊ = (⌈a⌉₊ - 1) / d + 1 := by
      have ha_pos : 1 ≤ ⌈a⌉₊ := Nat.ceil_pos.mpr (by linarith)
      apply le_antisymm
      · rw [Nat.ceil_le]
        have h1 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d + 1) * d := by
          have := Nat.lt_mul_div_succ (⌈a⌉₊ - 1) hd1
          rw [mul_comm] at this; omega
        rw [div_le_iff₀ hd_pos]; exact_mod_cast h1
      · by_contra hlt; push_neg at hlt
        have h1 : ⌈a'⌉₊ ≤ (⌈a⌉₊ - 1) / d := by omega
        have h3 : (⌈a⌉₊ : ℝ) / d ≤ ((⌈a⌉₊ - 1) / d : ℕ) := le_trans (Nat.le_ceil a') (by exact_mod_cast h1)
        rw [div_le_iff₀ hd_pos] at h3
        have h4 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d) * d := by exact_mod_cast h3
        have h5 : ((⌈a⌉₊ - 1) / d) * d ≤ ⌈a⌉₊ - 1 := Nat.div_mul_le_self _ _
        omega
    have hfloor_eq : ⌊b'⌋₊ = ⌊b⌋₊ / d := by
      rw [Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hd_pos.le)]
      refine ⟨(le_div_iff₀ hd_pos).mpr (by exact_mod_cast Nat.div_mul_le_self ⌊b⌋₊ d), ?_⟩
      rw [div_lt_iff₀ hd_pos]
      have hlt : ⌊b⌋₊ < (⌊b⌋₊ / d + 1) * d := by
        calc ⌊b⌋₊ = d * (⌊b⌋₊ / d) + ⌊b⌋₊ % d := (Nat.div_add_mod ⌊b⌋₊ d).symm
          _ < d * (⌊b⌋₊ / d) + d := Nat.add_lt_add_left (Nat.mod_lt _ hd1) _
          _ = (⌊b⌋₊ / d + 1) * d := by ring
      exact_mod_cast hlt
    have ha'b' : a' ≤ b' := by
      have h2 : a' ≤ ((⌈a⌉₊ - 1) / d + 1 : ℕ) := by rw [← hceil_eq]; exact Nat.le_ceil a'
      have h3 : ((⌊b⌋₊ / d : ℕ) : ℝ) ≤ b' := by
        rw [← hfloor_eq]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
      exact le_trans h2 (le_trans (by exact_mod_cast h_empty) h3)
    let wd : ℕ → ℝ := fun k => w (d * k)
    have hA'B' : ⌈a'⌉₊ ≤ ⌊b'⌋₊ := by rw [hceil_eq, hfloor_eq]; exact h_empty
    have hA'_ge : P ≤ ((d * ⌈a'⌉₊ : ℕ) : ℝ) := by
      push_cast
      calc P = (d : ℝ) * (P / d) := by field_simp [hd_pos.ne']
        _ ≤ (d : ℝ) * a' := mul_le_mul_of_nonneg_left hPa' hd_pos.le
        _ ≤ (d : ℝ) * ⌈a'⌉₊ := mul_le_mul_of_nonneg_left (Nat.le_ceil a') hd_pos.le
    have hB'_le : ((d * ⌊b'⌋₊ : ℕ) : ℝ) ≤ 2 * P := by
      push_cast
      calc (d : ℝ) * ⌊b'⌋₊ ≤ (d : ℝ) * b' := mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) hd_pos.le
        _ ≤ (d : ℝ) * (2 * (P / d)) := mul_le_mul_of_nonneg_left hb'2P hd_pos.le
        _ = 2 * P := by field_simp [hd_pos.ne']
    have hwd_bd : ∀ k ∈ Finset.Icc ⌈a'⌉₊ ⌊b'⌋₊, |wd k| ≤ W₀ := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact hw_bd _ ⟨le_trans hA'_ge (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.1) hd_pos.le),
        le_trans (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.2) hd_pos.le) hB'_le⟩
    have hwd_tv : ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |wd (k + 1) - wd k| ≤ W₀ := by
      have htv := discrete_tv_scale_le hP_pos hw_diff hw_tv d ⌈a'⌉₊ ⌊b'⌋₊ hA'B' hA'_ge hB'_le
      simpa [wd] using htv
    set E : ℝ := max C_exp 3 *
      ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := mul_nonneg (by positivity)
      (add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
    have hsum_bd : ∀ u : ℕ, ⌈a'⌉₊ ≤ u → u ≤ ⌊b'⌋₊ →
        ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖ ≤ E := by
      intro u hau hub
      have hu_ge : P / d ≤ (u : ℝ) := le_trans hPa' (le_trans (Nat.le_ceil a') (by exact_mod_cast hau))
      have hu_le : (u : ℝ) ≤ 2 * (P / d) := le_trans (by exact_mod_cast hub)
        (le_trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)) hb'2P)
      have hu_le' : (u : ℝ) ≤ 2 * P / d := by linarith [hu_le, show 2 * (P / d) = 2 * P / d by ring]
      by_cases hn0 : n = 0
      · subst hn0
        have htriv : ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
            ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          simp [norm_ePhase]
        have hcard : ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) ≤ 2 * P / d := by
          rw [Nat.card_Icc]
          have h1 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (lt_of_lt_of_le hPd_pos hPa')
          have h2 : u + 1 - ⌈a'⌉₊ ≤ u := by omega
          exact le_trans (by exact_mod_cast h2) hu_le'
        have hT0_0 : T₀ = 0 := by dsimp only [T₀]; simp
        have hmax1 : max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 = 1 := by rw [hT0_0, mul_zero, max_eq_right zero_le_one]
        calc ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖
            ≤ 2 * P / d := le_trans htriv hcard
          _ = 1 * ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + 0) := by rw [hmax1, div_one, one_mul, add_zero]
          _ ≤ E := by
              dsimp only [E]
              refine mul_le_mul (le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_right _ _))
                (add_le_add le_rfl (by positivity)) (by positivity) (by positivity)
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have h_eq_phase : ∀ k : ℕ, 1 ≤ k →
            ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r)) =
            ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
          intro k _
          congr 1; refine Finset.sum_congr rfl fun r _ => ?_
          rw [Nat.cast_mul, mul_pow, zpow_neg, zpow_natCast]; ring
        have hsum_eq : ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r)) =
            ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
              ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) :=
          Finset.sum_congr rfl fun k hk => h_eq_phase k (by
            have h1 : (1 : ℝ) ≤ a' := le_trans hPd_ge1 hPa'
            exact le_trans (Nat.ceil_pos.mpr (by linarith)) (Finset.mem_Icc.mp hk).1)
        rw [hsum_eq]
        let cd : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)
        have hcd0 : cd r₀ ≠ 0 :=
          div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hh₀) hn_pos.ne') (by positivity)
        have hM0_a' : M₀ ≤ a' := le_trans hd_M0 hPa'
        have ha'u : a' ≤ (u : ℝ) := le_trans (Nat.le_ceil a') (by exact_mod_cast hau)
        have hu2a' : (u : ℝ) ≤ 2 * a' := le_trans hu_le (by linarith [hPa'])
        have hdom_u : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
            |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a' ^ (-(r : ℤ)) ≤
              (1 / (2 * max (A.card : ℝ) 1)) *
                (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) := by
          intro k hk r hr hne
          have ha'_pow : a' ^ (-(r : ℤ)) ≤ (P / d) ^ (-(r : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos hPd_pos r) (pow_le_pow_left₀ hPd_pos.le hPa' r)
          have hu_pow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
          calc |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a' ^ (-(r : ℤ))
              ≤ |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) :=
                mul_le_mul_of_nonneg_left ha'_pow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
            _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                  (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                hdom_d k hk r hr hne
            _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                  (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_pow
                  (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (by positivity)
        have hTu_ub : |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (K_max - 1) := by
          have h1 : (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos hPd_pos r₀) (pow_le_pow_left₀ hPd_pos.le hu_ge r₀)
          have h3 : (P / d) ^ (K_max - 1) ≤ (u : ℝ) ^ (K_max - 1) := pow_le_pow_left₀ hPd_pos.le hu_ge _
          calc |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))
              ≤ |cd r₀| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (P / d) ^ (K_max - 1) := hT_ub
            _ ≤ (u : ℝ) ^ (K_max - 1) := h3
        have hhexp := hexp A r₀ hr₀ hA cd hcd0 a' (u : ℝ) hM0_a' ha'u hu2a' hdom_u hTu_ub
        rw [Nat.floor_natCast] at hhexp
        have hT_ge : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀ ≤ |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
          dsimp only [cd, T₀]
          have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
          have hupow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
          have h2pow : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * P ^ (-(r₀ : ℤ)) ≤ ((q_den : ℝ) * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ)) := by
            have hq_pos : (0 : ℝ) < q_den := by exact_mod_cast hq_den
            rw [show (2 * P / d) = (2 * P) / d by ring,
              zpow_neg (2 : ℝ) (R : ℤ), zpow_natCast (2 : ℝ) R,
              zpow_neg P (r₀ : ℤ), zpow_natCast P r₀,
              zpow_neg ((2 * P) / d) (r₀ : ℤ), zpow_natCast ((2 * P) / d) r₀,
              div_pow, inv_div, mul_pow, mul_inv]
            field_simp [hq_pos.ne', hd_pos.ne', hP_pos.ne']
            have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
            linarith [h2r]
          have habs_cd : |(h r₀ : ℝ) * n / ((q_den : ℝ) * (d : ℝ) ^ r₀)| = |(h r₀ : ℝ)| * n / ((q_den : ℝ) * (d : ℝ) ^ r₀) := by
            rw [abs_div, abs_mul, abs_of_pos hn_pos, abs_of_pos (by positivity : (0 : ℝ) < (q_den : ℝ) * (d : ℝ) ^ r₀)]
          rw [habs_cd]
          calc ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * (|(h r₀ : ℝ)| * n / P ^ r₀)
              = |(h r₀ : ℝ)| * n * (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * P ^ (-(r₀ : ℤ))) := by
                  simp only [zpow_neg, zpow_natCast]; ring
            _ ≤ |(h r₀ : ℝ)| * n * (((q_den : ℝ) * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                  mul_le_mul_of_nonneg_left h2pow (by positivity)
            _ = |(h r₀ : ℝ)| * n / ((q_den : ℝ) * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) := by ring
            _ ≤ |(h r₀ : ℝ)| * n / ((q_den : ℝ) * (d : ℝ) ^ r₀) * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hr0_1 (by positivity)) hupow (by positivity) (by positivity)
        refine le_trans hhexp ?_
        dsimp only [E]
        refine mul_le_mul (le_max_left _ _) (add_le_add ?_ ?_)
          (add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity)) (by positivity)
        · exact div_le_div₀ (by positivity) hu_le' (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (max_le_max hT_ge le_rfl)
        · exact Real.rpow_le_rpow (by positivity) hu_le' (by linarith)
    have hps := abel_summation_Icc hA'B' hW₀ hW₀ hE_nn hwd_bd hwd_tv hsum_bd
    rw [hceil_eq, hfloor_eq] at hps
    calc ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
            (w (d * k) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r))‖
        ≤ (W₀ + W₀) * E := by simpa [wd] using hps
      _ = 2 * (W₀ * max C_exp 3 *
            ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))) := by
          dsimp only [E]; ring
      _ ≤ 4 * W₀ * max C_exp 3 *
            ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          have hnn : 0 ≤ W₀ * max C_exp 3 *
              ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) :=
            mul_nonneg (mul_nonneg hW₀ (by positivity))
              (add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
          linarith


lemma lemma_2_4_core_mod (q_den : ℕ) (hq_den : 1 ≤ q_den) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    ∃ (η'_δ C_δ : ℝ), 0 < η'_δ ∧ 0 < C_δ ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ (n : ℕ) (P : ℝ) (a b : ℝ) (A : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
        N₀ ≤ n → (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
        P ≤ a → a ≤ b → b ≤ 2 * P →
        A ⊆ Finset.Icc 1 R → A.Nonempty →
        (hnonzero : ∃ r ∈ A, h r ≠ 0) →
        (∀ r ∈ A, |h r| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1) →
        0 ≤ W₀ → (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        ContDiffOn ℝ 1 w (Set.Icc P (2 * P)) →
        (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
        let r₀ : ℕ := (A.filter (fun r => h r ≠ 0)).min' (let ⟨r, hr, hhr⟩ := hnonzero; ⟨r, Finset.mem_filter.mpr ⟨hr, hhr⟩⟩)
        let T₀ : ℝ := (|(h r₀ : ℝ)| * n) / P ^ r₀
        1 ≤ T₀ →
        ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * (p : ℝ) ^ r))‖ ≤
          C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
  intro R
  have hR3 : 3 ≤ R := by
    have h1 : (3 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    exact Nat.le_floor h1
  set K_max : ℕ := Nat.ceil (4 / δ) + 3
  have hK_max : 3 ≤ K_max := by omega
  obtain ⟨C_exp, η_exp, M₀, hC_exp, hη_exp, hη_le, hM₀, hexp⟩ :=
    exp_sum_laurent_bound R K_max hK_max
  let η'_δ : ℝ := min (η_exp / 6) (1 / 12 : ℝ)
  have hη'_pos : 0 < η'_δ := by positivity
  let K_fact : ℝ := ((R + K_max).factorial : ℝ)
  have h_ev : ∀ᶠ n : ℕ in atTop,
      16 ≤ n ∧
      (max (8 * M₀ + 8) (Real.exp 2)) ^ 3 ≤ (n : ℝ) ^ δ ∧
      (2 : ℝ) * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
        (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ)) ≤ (n : ℝ) ^ δ ∧
      (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R ≤
        ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) := by
    have h1 : ∀ᶠ n : ℕ in atTop, 16 ≤ n := eventually_ge_atTop 16
    have h2 : ∀ᶠ n : ℕ in atTop, (max (8 * M₀ + 8) (Real.exp 2)) ^ 3 ≤ (n : ℝ) ^ δ :=
      ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    have h3 : ∀ᶠ n : ℕ in atTop,
        (2 : ℝ) * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
          (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ)) ≤ (n : ℝ) ^ δ := by
      have hlim : Tendsto (fun n : ℕ =>
          ((2 : ℝ) * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
            (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ))) / (n : ℝ) ^ δ) atTop (𝓝 0) := by
        have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ (R + 2) / x ^ δ) atTop (𝓝 0) := by
          have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (δ / (R + 2 : ℝ))) atTop (𝓝 0) := by
            have hpos : 0 < δ / (R + 2 : ℝ) := by positivity
            have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
              have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Real.tendsto_log_atTop
              refine h0.congr' ?_
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
              simp [Function.comp_def, Real.exp_neg, Real.exp_log hu, div_eq_mul_inv]
            have hcomp := (h1.comp (tendsto_rpow_atTop hpos)).const_mul ((R + 2 : ℝ) / δ)
            simp only [mul_zero] at hcomp
            refine hcomp.congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
            dsimp only [Function.comp_def]
            rw [Real.log_rpow hx]
            field_simp [hpos.ne']
          have hpow := hsub.pow (R + 2)
          simp only [zero_pow (by omega : R + 2 ≠ 0)] at hpow
          refine hpow.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          rw [div_pow, ← Real.rpow_natCast (x ^ (δ / (R + 2 : ℝ))), ← Real.rpow_mul hx.le]
          have hexp : δ / (R + 2 : ℝ) * ((R + 2 : ℕ) : ℝ) = δ := by
            push_cast; field_simp [show (R + 2 : ℝ) ≠ 0 by positivity]
          rw [hexp]
        have hconst : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ δ) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop)
        have hsum := ((hlog.comp tendsto_natCast_atTop_atTop).const_mul 2).add hconst
        simp only [mul_zero, add_zero] at hsum
        have hfin := hsum.const_mul ((2 : ℝ) * (R : ℝ) * K_fact * (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ)))
        simp only [mul_zero] at hfin
        refine hfin.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n _
        dsimp only [Function.comp_def]
        ring
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        eventually_ge_atTop 1] with n hn hn1
      have hpos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos (by exact_mod_cast hn1) δ
      rwa [div_le_one hpos] at hn
    have h4 : ∀ᶠ n : ℕ in atTop,
        (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R ≤
          ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) := by
      have hexp_ge : 4 / 3 ≤ (δ / 3) * ((K_max - 1 : ℕ) : ℝ) := by
        have hK1 : 4 / δ ≤ ((K_max - 1 : ℕ) : ℝ) := by
          have h1 : 4 / δ ≤ (Nat.ceil (4 / δ) : ℝ) := Nat.le_ceil _
          have h2 : Nat.ceil (4 / δ) ≤ K_max - 1 := by dsimp only [K_max]; omega
          exact le_trans h1 (by exact_mod_cast h2)
        calc (4 / 3 : ℝ) = (δ / 3) * (4 / δ) := by field_simp [hδ0.ne']
          _ ≤ (δ / 3) * ((K_max - 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hK1 (by positivity)
      have hlim : Tendsto (fun n : ℕ =>
          ((2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R) /
            ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1)) atTop (𝓝 0) := by
        refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
          (by
            have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / (3 * (R + 2 : ℝ)))) atTop (𝓝 0) := by
              have hpos : 0 < (1 : ℝ) / (3 * (R + 2 : ℝ)) := by positivity
              have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
                have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Real.tendsto_log_atTop
                refine h0.congr' ?_
                filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
                simp [Function.comp_def, Real.exp_neg, Real.exp_log hu, div_eq_mul_inv]
              have hcomp := (h1.comp (tendsto_rpow_atTop hpos)).const_mul (3 * (R + 2 : ℝ))
              simp only [mul_zero] at hcomp
              refine hcomp.congr' ?_
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
              dsimp only [Function.comp_def]
              rw [Real.log_rpow hx]
              field_simp [hpos.ne']
            have hpow := (hsub.comp tendsto_natCast_atTop_atTop).pow (R + 2)
            simp only [zero_pow (by omega : R + 2 ≠ 0)] at hpow
            have hfin := (hpow.const_mul 3).const_mul
              ((R : ℝ) ^ 2 * (q_den : ℝ) * (2 : ℝ) ^ R * (8 : ℝ) ^ (K_max - 1))
            simpa only [mul_zero] using hfin)
        filter_upwards [eventually_ge_atTop 3] with n hn3
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hden_ge : (n : ℝ) ^ (4 / 3 : ℝ) / (8 : ℝ) ^ (K_max - 1) ≤ ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) := by
          rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ (δ / 3)), ← Real.rpow_mul hn_pos.le]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hexp_ge) (by positivity)
        have hlog1 : 1 ≤ Real.log n := by
          have : Real.exp 1 ≤ (n : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ (3 : ℝ)) (by exact_mod_cast hn3)
          simpa using Real.log_le_log (Real.exp_pos 1) this
        have hnum_le : 2 * (Real.log n) ^ (R + 2) + 1 ≤ 3 * (Real.log n) ^ (R + 2) := by
          have : 1 ≤ (Real.log n) ^ (R + 2) := one_le_pow₀ hlog1
          linarith
        have hpow_eq : ((Real.log n / (n : ℝ) ^ (1 / (3 * (R + 2 : ℝ)))) ^ (R + 2)) =
            (Real.log n) ^ (R + 2) / (n : ℝ) ^ (1 / 3 : ℝ) := by
          rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le]
          have hexp : 1 / (3 * (R + 2 : ℝ)) * ((R + 2 : ℕ) : ℝ) = 1 / 3 := by
            push_cast; field_simp [show (R + 2 : ℝ) ≠ 0 by positivity]
          rw [hexp]
        calc ((2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R) /
              ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1)
            ≤ (3 * (Real.log n) ^ (R + 2) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R) /
                ((n : ℝ) ^ (4 / 3 : ℝ) / (8 : ℝ) ^ (K_max - 1)) :=
              div_le_div₀ (by positivity) (by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnum_le (by positivity)) (by positivity)) (by positivity)) (by positivity))
                (by positivity) hden_ge
          _ = ((R : ℝ) ^ 2 * (q_den : ℝ) * (2 : ℝ) ^ R * (8 : ℝ) ^ (K_max - 1)) *
                (3 * ((Real.log n / (n : ℝ) ^ (1 / (3 * (R + 2 : ℝ)))) ^ (R + 2))) := by
              have h43 : (n : ℝ) ^ (4 / 3 : ℝ) = (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
                rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hn_pos, Real.rpow_one]
              rw [hpow_eq, h43]
              field_simp [hn_pos.ne']
              ring
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        eventually_ge_atTop 1] with n hn hn1
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      rwa [div_le_one (by positivity)] at hn
    exact h1.and (h2.and (h3.and h4))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
  let C_I : ℝ := 128 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R
  let C_II_sq : ℝ := (Real.log 4 + 4) * 256 * (1 + ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp + C_exp)
  let C_II : ℝ := 16 * Real.sqrt C_II_sq
  let C_δ : ℝ := max (C_I + C_II + 64) 1
  refine ⟨η'_δ, C_δ, hη'_pos, by positivity, N₀, (hN₀ N₀ le_rfl).1, ?_⟩
  intro n P a b A h w W₀ hnN₀ hP_lo hP_hi hPa hab hb2P hA_sub hA_ne hnonzero hh_bd hW₀ hw_bd hw_diff hw_tv r₀ T₀ hT₀_ge1
  obtain ⟨hn16, hP_M0, hdom_n, hT_n⟩ := hN₀ n hnN₀
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP_ge_cube : (max (8 * M₀ + 8) (Real.exp 2)) ^ 3 ≤ P := le_trans hP_M0 hP_lo
  have hP_ge_e6 : Real.exp 6 ≤ P := by
    have h1 : Real.exp 2 ≤ max (8 * M₀ + 8) (Real.exp 2) := le_max_right _ _
    have h2 : (Real.exp 2) ^ 3 = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [← h2]; exact le_trans (pow_le_pow_left₀ (Real.exp_pos 2).le h1 3) hP_ge_cube
  have hlogP_ge6 : 6 ≤ Real.log P := by
    have := Real.log_le_log (Real.exp_pos 6) hP_ge_e6
    rwa [Real.log_exp] at this
  have hP_pos : 0 < P := lt_of_lt_of_le (Real.exp_pos 6) hP_ge_e6
  have hP_ge1 : 1 ≤ P := by linarith [show (1 : ℝ) ≤ Real.exp 6 by exact_mod_cast Real.one_le_exp (by norm_num)]
  have hA_bd : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R := fun r hr => Finset.mem_Icc.mp (hA_sub hr)
  have hr₀_mem : r₀ ∈ A := (Finset.mem_filter.mp (Finset.min'_mem (A.filter (fun r => h r ≠ 0))
    (let ⟨r, hr, hhr⟩ := hnonzero; ⟨r, Finset.mem_filter.mpr ⟨hr, hhr⟩⟩))).1
  have hh₀ : h r₀ ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem (A.filter (fun r => h r ≠ 0))
    (let ⟨r, hr, hhr⟩ := hnonzero; ⟨r, Finset.mem_filter.mpr ⟨hr, hhr⟩⟩))).2
  have h_min_r₀ : ∀ r ∈ A, h r ≠ 0 → r₀ ≤ r := fun r hr hhr =>
    Finset.min'_le _ r (Finset.mem_filter.mpr ⟨hr, hhr⟩)
  set U : ℕ := ⌊P ^ (1 / 3 : ℝ)⌋₊
  have hP13_ge : max (8 * M₀ + 8) (Real.exp 2) ≤ P ^ (1 / 3 : ℝ) := by
    have h1 : (max (8 * M₀ + 8) (Real.exp 2)) ^ (3 : ℝ) ≤ P := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hP_ge_cube
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
    exact (Real.le_rpow_inv_iff_of_pos (by positivity) hP_pos.le (by norm_num : (0 : ℝ) < 3)).mpr h1
  have hU_ge_M0 : 8 * M₀ + 7 ≤ (U : ℝ) := by
    have h1 : 8 * M₀ + 8 ≤ P ^ (1 / 3 : ℝ) := le_trans (le_max_left _ _) hP13_ge
    linarith [Nat.lt_floor_add_one (P ^ (1 / 3 : ℝ))]
  have hU_pos : 1 ≤ U := by
    have : (1 : ℝ) ≤ (U : ℝ) := by linarith
    exact_mod_cast this
  have hU_le_P13 : (U : ℝ) ≤ P ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  have hU_sq_lt_P : (U : ℝ) ^ 2 < P := by
    have h1 : P ^ (2 / 3 : ℝ) < P := by
      have hP1lt : 1 < P := by
        have : (1 : ℝ) < Real.exp 6 := Real.one_lt_exp_iff.mpr (by norm_num)
        linarith only [this, hP_ge_e6]
      simpa using Real.rpow_lt_rpow_of_exponent_lt hP1lt (by norm_num : (2 / 3 : ℝ) < 1)
    calc (U : ℝ) ^ 2 ≤ (P ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hU_le_P13 2
      _ = P ^ (2 / 3 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]; norm_num
      _ < P := h1
  set A₀ : ℕ := ⌈a⌉₊
  set B₀ : ℕ := ⌊b⌋₊
  have hU_lt_A₀ : U * U < A₀ := by
    have h1 : ((U * U : ℕ) : ℝ) < P := by push_cast; simpa [sq] using hU_sq_lt_P
    have h2 : P ≤ (A₀ : ℝ) := le_trans hPa (Nat.le_ceil a)
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hU_lt_A₀' : U < A₀ := by nlinarith [hU_pos]
  by_cases h_empty : B₀ < A₀
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.filter_empty, Finset.sum_empty, norm_zero]
    positivity
  · push_neg at h_empty
    have hA₀_pos : 1 ≤ A₀ := by omega
    have hB₀_le_2P : (B₀ : ℝ) ≤ 2 * P := le_trans (Nat.floor_le (by linarith)) hb2P
    let F : ℕ → ℝ := fun m => ∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * (m : ℝ) ^ r)
    let g : ℕ → ℂ := fun m => (w m : ℂ) * ePhase (F m)
    -- Step 1: Replace prime indicator * log with vonMangoldt
    have h_diff_vm : ‖∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p) -
        ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ ≤
        64 * W₀ * P * P ^ (-η'_δ) := by
      have hB4 : 4 ≤ B₀ := by
        have he6 : (64 : ℝ) ≤ Real.exp 6 := by
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
            _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
            _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
        have h4B : (4 : ℝ) ≤ B₀ := by
          have : (A₀ : ℝ) ≤ B₀ := by exact_mod_cast h_empty
          linarith [Nat.le_ceil a, hPa, hP_ge_e6, he6]
        exact_mod_cast h4B
      let g_ind : ℕ → ℂ := fun m => if A₀ ≤ m ∧ m ≤ B₀ then (w m : ℂ) * ePhase (F m) else 0
      have hg_bd : ∀ m, ‖g_ind m‖ ≤ W₀ := by
        intro m; dsimp only [g_ind]; split_ifs with hm
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            norm_ePhase (F m), mul_one]
          exact hw_bd m ⟨le_trans hPa (le_trans (Nat.le_ceil a) (by exact_mod_cast hm.1)),
            le_trans (by exact_mod_cast hm.2) hB₀_le_2P⟩
        · simp [hW₀]
      have hvm : ‖∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m -
          ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p)‖ ≤
          W₀ * (2 * Real.sqrt B₀ * (Real.log B₀) ^ 2) := by
        by_cases hW0 : W₀ = 0
        · have hg0 : ∀ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m = 0 := by
            intro m hm
            have := hw_bd m ⟨le_trans hPa (le_trans (Nat.le_ceil a) (by exact_mod_cast (Finset.mem_Icc.mp hm).1)),
              le_trans (by exact_mod_cast (Finset.mem_Icc.mp hm).2) hB₀_le_2P⟩
            have hw0 : w m = 0 := abs_nonpos_iff.mp (hW0 ▸ this)
            dsimp only [g]; rw [hw0]; simp
          have hp0 : ∀ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p) = 0 := by
            intro p hp
            have hm := (Finset.mem_filter.mp hp).1
            have := hw_bd p ⟨le_trans hPa (le_trans (Nat.le_ceil a) (by exact_mod_cast (Finset.mem_Icc.mp hm).1)),
              le_trans (by exact_mod_cast (Finset.mem_Icc.mp hm).2) hB₀_le_2P⟩
            have hw0 : w p = 0 := abs_nonpos_iff.mp (hW0 ▸ this)
            rw [hw0]; simp
          rw [Finset.sum_eq_zero hg0, Finset.sum_eq_zero hp0, hW0]; simp
        · have hW_pos : 0 < W₀ := lt_of_le_of_ne hW₀ (Ne.symm hW0)
          have h1 := sum_vonMangoldt_sub_prime_log_le hA₀_pos hB4 (g := fun m => g_ind m / (W₀ : ℂ)) (fun m => by
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hW₀]
            exact div_le_one_of_le₀ (hg_bd m) hW₀)
          have heq_l : (∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * (g_ind m / (W₀ : ℂ)) -
              ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (Real.log p : ℂ) * (g_ind p / (W₀ : ℂ))) * (W₀ : ℂ) =
              ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m -
              ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p) := by
            rw [sub_mul, Finset.sum_mul, Finset.sum_mul]
            congr 1
            · refine Finset.sum_congr rfl fun m hm => ?_
              have hm' := Finset.mem_Icc.mp hm
              dsimp only [g_ind, g]; rw [if_pos hm']
              field_simp [Complex.ofReal_ne_zero.mpr hW_pos.ne']
            · refine Finset.sum_congr rfl fun p hp => ?_
              have hp' := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
              dsimp only [g_ind]; rw [if_pos hp']
              field_simp [Complex.ofReal_ne_zero.mpr hW_pos.ne']
          rw [← heq_l, norm_mul, Complex.norm_real, Real.norm_of_nonneg hW₀, mul_comm]
          exact mul_le_mul_of_nonneg_left h1 hW₀
      have hsqrt_bd : 2 * Real.sqrt B₀ * (Real.log B₀) ^ 2 ≤ 64 * P * P ^ (-η'_δ) := by
        have hB_pos : (0 : ℝ) < B₀ := by exact_mod_cast (by omega : 0 < B₀)
        have hB_ge1 : (1 : ℝ) ≤ B₀ := by exact_mod_cast (by omega : 1 ≤ B₀)
        have h1 : Real.sqrt B₀ ≤ Real.sqrt (2 * P) := Real.sqrt_le_sqrt hB₀_le_2P
        have h2 : Real.log B₀ ≤ Real.log (2 * P) := Real.log_le_log hB_pos hB₀_le_2P
        have hlog_le : Real.log (2 * P) ≤ 4 * (2 * P) ^ (1 / 8 : ℝ) := by
          have hr8 : 0 < (2 * P) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
          have hlog8 : Real.log ((2 * P) ^ (1 / 8 : ℝ)) ≤ (2 * P) ^ (1 / 8 : ℝ) / Real.exp 1 := by
            have hu := Real.log_le_sub_one_of_pos (div_pos hr8 (Real.exp_pos 1))
            rw [Real.log_div hr8.ne' (Real.exp_pos 1).ne', Real.log_exp] at hu
            linarith
          rw [Real.log_rpow (by positivity)] at hlog8
          have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have : (2 * P) ^ (1 / 8 : ℝ) / Real.exp 1 ≤ (2 * P) ^ (1 / 8 : ℝ) / 2 :=
            div_le_div_of_nonneg_left hr8.le (by norm_num) he2
          linarith
        have hlog_sq : (Real.log (2 * P)) ^ 2 ≤ 16 * (2 * P) ^ (1 / 4 : ℝ) := by
          calc (Real.log (2 * P)) ^ 2 ≤ (4 * (2 * P) ^ (1 / 8 : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_le 2
            _ = 16 * ((2 * P) ^ (1 / 8 : ℝ)) ^ 2 := by ring
            _ = 16 * (2 * P) ^ (1 / 4 : ℝ) := by
                rw [← Real.rpow_natCast ((2 * P) ^ _), ← Real.rpow_mul (by positivity)]; norm_num
        have hprod : 2 * Real.sqrt (2 * P) * (Real.log (2 * P)) ^ 2 ≤ 32 * (2 * P) ^ (3 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          calc 2 * (2 * P) ^ (1 / 2 : ℝ) * (Real.log (2 * P)) ^ 2
              ≤ 2 * (2 * P) ^ (1 / 2 : ℝ) * (16 * (2 * P) ^ (1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_left hlog_sq (by positivity)
            _ = 32 * ((2 * P) ^ (1 / 2 : ℝ) * (2 * P) ^ (1 / 4 : ℝ)) := by ring
            _ = 32 * (2 * P) ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add (by positivity)]; norm_num
        have h2p34 : (2 * P) ^ (3 / 4 : ℝ) ≤ 2 * P ^ (3 / 4 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hP_pos.le]
          have h2le : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 4 : ℝ) ≤ 1)
          exact mul_le_mul_of_nonneg_right h2le (by positivity)
        have h34_le : P ^ (3 / 4 : ℝ) ≤ P * P ^ (-η'_δ) := by
          have hrhs : P * P ^ (-η'_δ) = P ^ (1 + -η'_δ) := by
            rw [Real.rpow_add hP_pos, Real.rpow_one]
          rw [hrhs]
          refine Real.rpow_le_rpow_of_exponent_le hP_ge1 ?_
          have : η'_δ ≤ 1 / 12 := min_le_right _ _
          linarith
        calc 2 * Real.sqrt B₀ * (Real.log B₀) ^ 2
            ≤ 2 * Real.sqrt (2 * P) * (Real.log (2 * P)) ^ 2 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (pow_le_pow_left₀ (Real.log_nonneg hB_ge1) h2 2) (by positivity) (by positivity)
          _ ≤ 32 * (2 * P) ^ (3 / 4 : ℝ) := hprod
          _ ≤ 64 * P ^ (3 / 4 : ℝ) := by linarith
          _ ≤ 64 * (P * P ^ (-η'_δ)) := mul_le_mul_of_nonneg_left h34_le (by norm_num)
          _ = 64 * P * P ^ (-η'_δ) := by ring
      rw [norm_sub_rev]
      calc ‖∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m -
            ∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p)‖
          ≤ W₀ * (2 * Real.sqrt B₀ * (Real.log B₀) ^ 2) := hvm
        _ ≤ W₀ * (64 * P * P ^ (-η'_δ)) := mul_le_mul_of_nonneg_left hsqrt_bd hW₀
        _ = 64 * W₀ * P * P ^ (-η'_δ) := by ring
    -- Step 2: Vaughan's identity
    have hvaugh := vaughan_identity U U hU_pos hU_pos hA₀_pos g
    have hS1_zero : ∑ m ∈ (Finset.Icc A₀ B₀).filter (· ≤ U), (ArithmeticFunction.vonMangoldt m : ℂ) * g m = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_filter, Finset.mem_Icc] at hm; omega
    -- Step 3: Dominance for Type I (`d ≤ U * U`)
    have hdom_I : ∀ d : ℕ, 1 ≤ d → d ≤ U * U →
        M₀ ≤ P / (d : ℝ) ∧
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |(h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ)))) ∧
        |(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (K_max - 1) := by
      intro d hd1 hd_uu
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hPd_pos : 0 < P / d := div_pos hP_pos hd_pos
      have hPd_ge_P13 : P ^ (1 / 3 : ℝ) ≤ P / d := by
        have hd_le_P23 : (d : ℝ) ≤ P ^ (2 / 3 : ℝ) := by
          have h1 : (d : ℝ) ≤ (U : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : d ≤ U * U)
          calc (d : ℝ) ≤ (U : ℝ) ^ 2 := h1
            _ ≤ (P ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hU_le_P13 2
            _ = P ^ (2 / 3 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]; norm_num
        rw [le_div_iff₀ hd_pos]
        calc P ^ (1 / 3 : ℝ) * (d : ℝ) ≤ P ^ (1 / 3 : ℝ) * P ^ (2 / 3 : ℝ) :=
              mul_le_mul_of_nonneg_left hd_le_P23 (by positivity)
          _ = P := by rw [← Real.rpow_add hP_pos]; norm_num
      have hPd_M0 : M₀ ≤ P / d := by linarith [le_max_left (8 * M₀ + 8) (Real.exp 2), hP13_ge]
      have hr₀_1 : 1 ≤ r₀ := (hA_bd r₀ hr₀_mem).1
      have hr₀_R : r₀ ≤ R := (hA_bd r₀ hr₀_mem).2
      refine ⟨hPd_M0, ?_, ?_⟩
      · intro k hk r hr hne
        by_cases hhr : h r = 0
        · simp [hhr]; positivity
        · have hr_gt : r₀ < r := lt_of_le_of_ne (h_min_r₀ r hr hhr) hne.symm
          have hr_R : r ≤ R := (hA_bd r hr).2
          have hh_r0 : (1 : ℝ) ≤ |(h r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hh₀
          have hh_r : |(h r : ℝ)| ≤ 2 * (Real.log n) ^ (R + 2) + 1 := by
            have h1 := hh_bd r hr
            have h2 : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
            have h3 : (|h r| : ℝ) ≤ 2 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1 := by exact_mod_cast h1
            linarith [show (|h r| : ℝ) = |(h r : ℝ)| by push_cast; rfl]
          have hdesc_le : (Nat.descFactorial (r + k - 1) k : ℝ) ≤ K_fact * (Nat.descFactorial (r₀ + k - 1) k : ℝ) := by
            have hk_le : k ≤ K_max := (Finset.mem_Icc.mp hk).2
            have h1 : Nat.descFactorial (r + k - 1) k ≤ (R + K_max).factorial := by
              exact le_trans (descFactorial_le_factorial (r + k - 1) k) (Nat.factorial_le (by omega))
            have h2 : 1 ≤ Nat.descFactorial (r₀ + k - 1) k := Nat.descFactorial_pos.mpr (by omega : k ≤ r₀ + k - 1)
            have h1R : (Nat.descFactorial (r + k - 1) k : ℝ) ≤ K_fact := by dsimp only [K_fact]; exact_mod_cast h1
            have h2R : (1 : ℝ) ≤ (Nat.descFactorial (r₀ + k - 1) k : ℝ) := by exact_mod_cast h2
            nlinarith
          have h_cancel_lhs : |(h r : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r)| * (P / d) ^ (-(r : ℤ)) =
              |(h r : ℝ)| * (n : ℝ) / (q_den : ℝ) * P ^ (-(r : ℤ)) := by
            rw [abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
              abs_of_pos (a := (q_den : ℝ) * (d : ℝ) ^ r) (by positivity),
              zpow_neg, zpow_natCast, div_pow]
            field_simp [hd_pos.ne', hP_pos.ne']
          have h_cancel_rhs : |(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (2 * P / d) ^ (-(r₀ : ℤ)) =
              |(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * (2 : ℝ) ^ (-(r₀ : ℤ)) * P ^ (-(r₀ : ℤ)) := by
            rw [abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
              abs_of_pos (a := (q_den : ℝ) * (d : ℝ) ^ r₀) (by positivity),
              zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, div_pow, mul_pow]
            field_simp [hd_pos.ne', hP_pos.ne']
          rw [mul_assoc _ (Nat.descFactorial _ _ : ℝ) _, mul_comm (Nat.descFactorial _ _ : ℝ) _,
            ← mul_assoc _ ((P / d) ^ (-(r : ℤ))) _, h_cancel_lhs]
          rw [mul_assoc _ (Nat.descFactorial _ _ : ℝ) _, mul_comm (Nat.descFactorial _ _ : ℝ) _,
            ← mul_assoc _ ((2 * P / d) ^ (-(r₀ : ℤ))) _, h_cancel_rhs]
          have hP_sub : P ^ (-(r : ℤ)) ≤ P ^ (-1 : ℤ) * P ^ (-(r₀ : ℤ)) := by
            rw [← zpow_add₀ hP_pos.ne']
            exact zpow_le_zpow_right₀ hP_ge1 (by omega)
          have h2_le : (2 : ℝ) ^ (r₀ : ℤ) ≤ (2 : ℝ) ^ R := by
            rw [zpow_natCast]; exact pow_le_pow_right₀ (by norm_num) hr₀_R
          have hA_le_R : max (A.card : ℝ) 1 ≤ (R : ℝ) := by
            have h1 : A.card ≤ R := by
              calc A.card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hA_sub
                _ = R := by rw [Nat.card_Icc]; omega
            have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
            exact max_le (by exact_mod_cast h1) hR1
          have hdom_P : (2 * (Real.log n) ^ (R + 2) + 1) * K_fact * (2 : ℝ) ^ R * (2 * (R : ℝ)) ≤ P := by
            have h1 : (2 * (Real.log n) ^ (R + 2) + 1) * K_fact * (2 : ℝ) ^ R * (2 * (R : ℝ)) ≤
                (2 : ℝ) * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ)) := by
              have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
              have h2R : (2 : ℝ) ^ R ≤ (2 : ℝ) ^ (4 * R + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
              have hnn : 0 ≤ (2 * (Real.log n) ^ (R + 2) + 1) * K_fact * (2 * (R : ℝ)) := by positivity
              calc (2 * (Real.log n) ^ (R + 2) + 1) * K_fact * (2 : ℝ) ^ R * (2 * (R : ℝ))
                  ≤ (2 * (Real.log n) ^ (R + 2) + 1) * K_fact * (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ)) := by
                    rw [mul_assoc _ ((2 : ℝ) ^ R) _, mul_assoc _ ((2 : ℝ) ^ (4 * R + 4)) _]
                    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2R (by positivity)) (by positivity)
                _ ≤ 2 * (R : ℝ) * ((2 * (Real.log n) ^ (R + 2) + 1) * K_fact * (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ))) := by
                    have h2R1 : 1 ≤ 2 * (R : ℝ) := by linarith
                    exact le_mul_of_one_le_left (by positivity) h2R1
                _ = _ := by ring
            exact le_trans h1 (le_trans hdom_n hP_lo)
          calc |(h r : ℝ)| * (n : ℝ) / (q_den : ℝ) * P ^ (-(r : ℤ)) * (Nat.descFactorial (r + k - 1) k : ℝ)
              ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (n : ℝ) / (q_den : ℝ) * (P ^ (-1 : ℤ) * P ^ (-(r₀ : ℤ))) *
                  (K_fact * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by
                refine mul_le_mul (mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh_r (by positivity)) (by positivity))
                  hP_sub (by positivity) (by positivity)) hdesc_le (by positivity) (by positivity)
            _ = ((2 * (Real.log n) ^ (R + 2) + 1) * K_fact * P⁻¹) *
                  ((n : ℝ) / (q_den : ℝ) * P ^ (-(r₀ : ℤ)) * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by
                rw [zpow_neg_one]; ring
            _ ≤ (1 / (2 * (R : ℝ) * (2 : ℝ) ^ R)) *
                  (|(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * P ^ (-(r₀ : ℤ)) * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by
                refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
                · rw [mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hP_pos (by positivity)]
                  linarith [hdom_P]
                · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
                  calc (n : ℝ) / (q_den : ℝ) = 1 * (n : ℝ) / (q_den : ℝ) := by ring
                    _ ≤ |(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh_r0 (by positivity)) (by positivity)
            _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                  (|(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * (2 : ℝ) ^ (-(r₀ : ℤ)) * P ^ (-(r₀ : ℤ)) * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by
                have hdiv_le : 1 / (2 * (R : ℝ) * (2 : ℝ) ^ R) ≤ 1 / (2 * max (A.card : ℝ) 1) * (2 : ℝ) ^ (-(r₀ : ℤ)) := by
                  rw [zpow_neg, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
                  have h1 : 2 * max (A.card : ℝ) 1 * (2 : ℝ) ^ (r₀ : ℤ) ≤ 2 * (R : ℝ) * (2 : ℝ) ^ R :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hA_le_R (by norm_num)) h2_le (by positivity) (by positivity)
                  linarith
                calc (1 / (2 * (R : ℝ) * (2 : ℝ) ^ R)) *
                      (|(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * P ^ (-(r₀ : ℤ)) * (Nat.descFactorial (r₀ + k - 1) k : ℝ))
                    ≤ (1 / (2 * max (A.card : ℝ) 1) * (2 : ℝ) ^ (-(r₀ : ℤ))) *
                        (|(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * P ^ (-(r₀ : ℤ)) * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) :=
                      mul_le_mul_of_nonneg_right hdiv_le (by positivity)
                  _ = _ := by ring
      · have h_cancel : |(h r₀ : ℝ) * (n : ℝ) / ((q_den : ℝ) * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) =
            |(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * (r₀ : ℝ) * P ^ (-(r₀ : ℤ)) := by
          rw [abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
            abs_of_pos (a := (q_den : ℝ) * (d : ℝ) ^ r₀) (by positivity), zpow_neg, zpow_natCast, div_pow]
          field_simp [hd_pos.ne', hP_pos.ne']
        rw [h_cancel]
        have hh_r0_le : |(h r₀ : ℝ)| ≤ 2 * (Real.log n) ^ (R + 2) + 1 := by
          have h1 := hh_bd r₀ hr₀_mem
          have h2 : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
          have h3 : (|h r₀| : ℝ) ≤ 2 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1 := by exact_mod_cast h1
          linarith [show (|h r₀| : ℝ) = |(h r₀ : ℝ)| by push_cast; rfl]
        have hr0_le_R : (r₀ : ℝ) ≤ R := by exact_mod_cast hr₀_R
        have hP_le1 : P ^ (-(r₀ : ℤ)) ≤ 1 := by
          rw [zpow_neg, zpow_natCast]
          exact inv_le_one_of_one_le₀ (one_le_pow₀ hP_ge1)
        have hpow_le : ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) ≤ (P / d) ^ (K_max - 1) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have h1 : (n : ℝ) ^ (δ / 3) ≤ P ^ (1 / 3 : ℝ) := by
            rw [show δ / 3 = δ * (1 / 3 : ℝ) by ring, Real.rpow_mul (Nat.cast_nonneg n)]
            exact Real.rpow_le_rpow (by positivity) hP_lo (by positivity)
          linarith [hPd_ge_P13, show (n : ℝ) ^ (δ / 3) / 8 ≤ (n : ℝ) ^ (δ / 3) by linarith [Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) (δ / 3)]]
        calc |(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * (r₀ : ℝ) * P ^ (-(r₀ : ℤ))
            ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (n : ℝ) * (R : ℝ) * 1 := by
              refine mul_le_mul (mul_le_mul (div_le_self (mul_le_mul_of_nonneg_right hh_r0_le (by positivity)) (by positivity))
                hr0_le_R (by positivity) (by positivity)) hP_le1 (by positivity) (by positivity)
          _ ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R := by
              have h21 : (1 : ℝ) ≤ (q_den : ℝ) * (2 : ℝ) ^ R := by
                have hq1 : (1 : ℝ) ≤ (q_den : ℝ) := by exact_mod_cast hq_den
                have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ R := one_le_pow₀ (by norm_num)
                nlinarith
              have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
              nlinarith [sq_nonneg (R : ℝ)]
          _ ≤ ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) := hT_n
          _ ≤ (P / d) ^ (K_max - 1) := hpow_le
    -- Step 4: Bound Type I sums (`S2a` and `S2b`)
    have h_harm_eq : ∀ M : ℕ, ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / d = (harmonic M : ℝ) := by
      intro M
      induction M with
      | zero => simp
      | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]; push_cast; ring
    have h_sum_inv_U : ∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / d ≤ 2 * Real.log P := by
      rw [h_harm_eq U]
      have h1 := harmonic_le_one_add_log U
      have h2 : Real.log U ≤ Real.log P := Real.log_le_log (by exact_mod_cast hU_pos)
        (le_trans hU_le_P13 (Real.rpow_le_rpow_of_exponent_le hP_ge1 (by norm_num)))
      linarith
    have h_sum_inv_UU : ∑ d ∈ Finset.Icc 1 (U * U), (1 : ℝ) / d ≤ 2 * Real.log P := by
      rw [h_harm_eq (U * U)]
      have h1 := harmonic_le_one_add_log (U * U)
      have h2 : Real.log ((U * U : ℕ) : ℝ) ≤ Real.log P := Real.log_le_log (by exact_mod_cast (by nlinarith [hU_pos]))
        (by push_cast; simpa [sq] using hU_sq_lt_P.le)
      linarith
    -- Now bound `S2a` using `type_I_single_d_bound` and `S2b` using `type_I_no_log_single_d_bound`!
    have h_err_sum : ∀ d : ℕ, 1 ≤ d → d ≤ U * U →
        (2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp) ≤
          2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) := by
      intro d hd1 hd_uu
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hPd_ge_P13 : P ^ (1 / 3 : ℝ) ≤ P / d := by
        have hd_le_P23 : (d : ℝ) ≤ P ^ (2 / 3 : ℝ) := by
          have h1 : (d : ℝ) ≤ (U : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : d ≤ U * U)
          calc (d : ℝ) ≤ (U : ℝ) ^ 2 := h1
            _ ≤ (P ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hU_le_P13 2
            _ = P ^ (2 / 3 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]; norm_num
        rw [le_div_iff₀ hd_pos]
        calc P ^ (1 / 3 : ℝ) * (d : ℝ) ≤ P ^ (1 / 3 : ℝ) * P ^ (2 / 3 : ℝ) :=
              mul_le_mul_of_nonneg_left hd_le_P23 (by positivity)
          _ = P := by rw [← Real.rpow_add hP_pos]; norm_num
      have hT_term : (2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 ≤
          2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * T₀ ^ (-1 / 6 : ℝ) := by
        have h1 : ((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀ ^ (1 / 6 : ℝ) ≤ max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 := by
          refine le_trans ?_ (le_max_left _ _)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using Real.rpow_le_rpow_of_exponent_le hT₀_ge1 (by norm_num : (1 / 6 : ℝ) ≤ 1)
        calc (2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1
            ≤ (2 * P / d) / (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀ ^ (1 / 6 : ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) h1
          _ = 2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * T₀ ^ (-1 / 6 : ℝ) := by
              have hq_pos : (0 : ℝ) < q_den := by exact_mod_cast hq_den
              rw [zpow_neg, zpow_natCast,
                ← Real.rpow_neg (by linarith), show -(1 / 6 : ℝ) = -1 / 6 by norm_num]
              field_simp [hq_pos.ne']; ring
      have hP_term : (2 * P / d) ^ (1 - η_exp) ≤ 2 * (P / d) * P ^ (-η'_δ) := by
        have h1 : (2 * P / d) ^ (1 - η_exp) = (2 * (P / d)) ^ (1 - η_exp) := by ring_nf
        rw [h1, Real.mul_rpow (by norm_num) (by positivity)]
        have h2le : (2 : ℝ) ^ (1 - η_exp) ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith only [hη_exp] : 1 - η_exp ≤ 1)
        have hPd_pow : (P / d) ^ (1 - η_exp) = (P / d) * (P / d) ^ (-η_exp) := by
          rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
        have hP_pow : (P / d) ^ (-η_exp) ≤ P ^ (-η'_δ) := by
          have h1 : (P / d) ^ (-η_exp) ≤ (P ^ (1 / 3 : ℝ)) ^ (-η_exp) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hPd_ge_P13 (by linarith [hη_exp])
          rw [← Real.rpow_mul hP_pos.le] at h1
          refine le_trans h1 (Real.rpow_le_rpow_of_exponent_le hP_ge1 ?_)
          have : η'_δ ≤ η_exp / 6 := min_le_left _ _
          linarith
        calc (2 : ℝ) ^ (1 - η_exp) * (P / d) ^ (1 - η_exp)
            ≤ 2 * ((P / d) * P ^ (-η'_δ)) := by
              rw [hPd_pow]
              exact mul_le_mul h2le (mul_le_mul_of_nonneg_left hP_pow (by positivity)) (by positivity) (by norm_num)
          _ = 2 * (P / d) * P ^ (-η'_δ) := by ring
      have h2R : (1 : ℝ) ≤ (q_den : ℝ) * (2 : ℝ) ^ R := by
        have hq1 : (1 : ℝ) ≤ (q_den : ℝ) := by exact_mod_cast hq_den
        have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ R := one_le_pow₀ (by norm_num)
        nlinarith
      calc (2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)
          ≤ 2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * T₀ ^ (-1 / 6 : ℝ) + 2 * (P / d) * P ^ (-η'_δ) :=
            add_le_add hT_term hP_term
        _ ≤ 2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * T₀ ^ (-1 / 6 : ℝ) +
              2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * P ^ (-η'_δ) := by
            refine add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity))
            linarith
        _ = 2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) := by ring
    have hlog2P_le : Real.log (2 * P) + 1 ≤ 2 * Real.log P := by
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      rw [Real.log_mul (by norm_num) hP_pos.ne']
      linarith
    have hS2a_bd : ‖∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
          ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), (Real.log k : ℂ) * g (d * k)‖ ≤
        64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 := by
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ d ∈ Finset.Icc 1 U,
          ‖(ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), (Real.log k : ℂ) * g (d * k)‖ ≤
          16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) *
            Real.log P * (1 / d : ℝ) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd_uu : d ≤ U * U := le_trans (Finset.mem_Icc.mp hd).2 (Nat.le_mul_self U)
        have hdom_d := hdom_I d hd1 hd_uu
        have h1 := type_I_single_d_bound_mod q_den hq_den R K_max hK_max C_exp η_exp M₀ hC_exp hη_exp hη_le hM₀ hexp
          n P a b hP_ge1 hPa hab hb2P A hA_bd r₀ hr₀_mem h hh₀ w W₀ hW₀ hw_bd hw_diff hw_tv
          d hd1 hdom_d.1 hdom_d.2.1 hdom_d.2.2
        dsimp only at h1
        have hsum_eq : ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), (Real.log k : ℂ) * g (d * k) =
            ∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
              (Real.log k * w (d * k) : ℂ) *
                ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * ((d * k : ℕ) : ℝ) ^ r)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp only [g, F]; push_cast; ring
        have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          have hmu_le : |ArithmeticFunction.moebius d| ≤ 1 := by
            unfold ArithmeticFunction.moebius
            split_ifs <;> simp [← neg_one_pow_eq_ite]
            exact abs_neg_one_pow _ |>.le
          exact_mod_cast hmu_le
        rw [norm_mul, hsum_eq]
        calc ‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖∑ k ∈ _, _‖
            ≤ 1 * ‖∑ k ∈ _, _‖ := mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
          _ = ‖∑ k ∈ _, _‖ := one_mul _
          _ ≤ 4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
                ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := h1
          _ ≤ 4 * W₀ * (2 * Real.log P) * max C_exp 3 *
                (2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ))) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2P_le (by positivity)) (by positivity))
                (h_err_sum d hd1 hd_uu) (by positivity) (by positivity)
          _ = 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) *
                Real.log P * (1 / d : ℝ) := by ring
      calc ∑ d ∈ Finset.Icc 1 U, ‖_‖
          ≤ ∑ d ∈ Finset.Icc 1 U, 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * (1 / d : ℝ) := Finset.sum_le_sum hterm
        _ = 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * ∑ d ∈ Finset.Icc 1 U, (1 / d : ℝ) := by
            rw [← Finset.mul_sum]
        _ ≤ 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * (2 * Real.log P) :=
            mul_le_mul_of_nonneg_left h_sum_inv_U (by positivity)
        _ ≤ 64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 := by
            have hnn : 0 ≤ max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 := by positivity
            linarith [show 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * (2 * Real.log P) =
              32 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 by ring]
    have hS2b_rew : ∑ u ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius u : ℂ) *
          ∑ k ∈ Finset.Icc 1 U, (ArithmeticFunction.vonMangoldt k : ℂ) *
            ∑ m ∈ Finset.Icc ((A₀ - 1) / (u * k) + 1) (B₀ / (u * k)), g (u * k * m) =
        ∑ d ∈ Finset.Icc 1 (U * U),
          (∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
            (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)) *
          ∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r) := by
      have hR : ∑ d ∈ Finset.Icc 1 (U * U),
            (∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
              (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)) *
            ∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r) =
          ∑ u ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius u : ℂ) *
            ∑ k ∈ Finset.Icc 1 U, (ArithmeticFunction.vonMangoldt k : ℂ) *
              ∑ m ∈ Finset.Icc ((A₀ - 1) / (u * k) + 1) (B₀ / (u * k)), g (u * k * m) := by
        have hflt : ∀ d ∈ Finset.Icc 1 (U * U),
            (∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
              (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)) *
            ∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r) =
            ∑ u ∈ d.divisors.filter (fun u => 1 ≤ u ∧ u ≤ U),
              (if d / u ≤ U then
                (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ) *
                  ∑ r ∈ Finset.Icc ((A₀ - 1) / (u * (d / u)) + 1) (B₀ / (u * (d / u))), g (u * (d / u) * r)
              else 0) := by
          intro d _
          rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not (d.divisors.filter (fun u => 1 ≤ u ∧ u ≤ U)) (fun u => d / u ≤ U)]
          have h0 : ∑ u ∈ (d.divisors.filter (fun u => 1 ≤ u ∧ u ≤ U)).filter (fun u => ¬ d / u ≤ U),
              (if d / u ≤ U then
                (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ) *
                  ∑ r ∈ Finset.Icc ((A₀ - 1) / (u * (d / u)) + 1) (B₀ / (u * (d / u))), g (u * (d / u) * r)
              else 0) = 0 :=
            Finset.sum_eq_zero fun u hu => by
              have hnot : ¬ d / u ≤ U := (Finset.mem_filter.mp hu).2
              simp [hnot]
          rw [h0, add_zero, Finset.filter_filter]
          have hset : d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U) =
              d.divisors.filter (fun u => (1 ≤ u ∧ u ≤ U) ∧ d / u ≤ U) := by
            ext u; simp only [Finset.mem_filter]
            exact ⟨fun ⟨hu, h1, h2⟩ => ⟨hu, ⟨Nat.pos_of_mem_divisors hu, h1⟩, h2⟩,
              fun ⟨hu, ⟨_, h1⟩, h2⟩ => ⟨hu, h1, h2⟩⟩
          refine Finset.sum_congr hset fun u hu => ?_
          have hu_dvd : u ∣ d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hu).1
          have hdu : d / u ≤ U := (Finset.mem_filter.mp hu).2.2
          simp only [hdu, ↓reduceIte, Nat.mul_div_cancel' hu_dvd]
        rw [Finset.sum_congr rfl hflt, sum_Icc_divisors_filter (by norm_num) (by norm_num)
          (fun u k => if k ≤ U then
            (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) *
              ∑ r ∈ Finset.Icc ((A₀ - 1) / (u * k) + 1) (B₀ / (u * k)), g (u * k * r)
          else 0)]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
        have huU : u ≤ U := (Finset.mem_Icc.mp hu).2
        rw [show (1 - 1) / u + 1 = 1 by simp, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (U * U / u)) (· ≤ U)]
        have h0 : ∑ k ∈ (Finset.Icc 1 (U * U / u)).filter (fun k => ¬ k ≤ U),
            (if k ≤ U then
              (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt k : ℂ) *
                ∑ r ∈ Finset.Icc ((A₀ - 1) / (u * k) + 1) (B₀ / (u * k)), g (u * k * r)
            else 0) = 0 :=
          Finset.sum_eq_zero fun k hk => by
            have hnot : ¬ k ≤ U := (Finset.mem_filter.mp hk).2
            simp [hnot]
        rw [h0, add_zero, Finset.mul_sum]
        have hset_k : (Finset.Icc 1 (U * U / u)).filter (· ≤ U) = Finset.Icc 1 U := by
          ext k; simp only [Finset.mem_filter, Finset.mem_Icc]
          have hU_le : U ≤ U * U / u := (Nat.le_div_iff_mul_le hu1).mpr (Nat.mul_le_mul_left U huU)
          omega
        refine Finset.sum_congr hset_k fun k hk => ?_
        have hkU : k ≤ U := (Finset.mem_Icc.mp hk).2
        simp only [hkU, ↓reduceIte, mul_assoc]
      exact hR.symm
    have hS2b_bd : ‖∑ d ∈ Finset.Icc 1 (U * U),
          (∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
            (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)) *
          ∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r)‖ ≤
        64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 := by
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ d ∈ Finset.Icc 1 (U * U),
          ‖(∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
              (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)) *
            ∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r)‖ ≤
          16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) *
            Real.log P * (1 / d : ℝ) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd_uu : d ≤ U * U := (Finset.mem_Icc.mp hd).2
        have hdom_d := hdom_I d hd1 hd_uu
        have h1 := type_I_no_log_single_d_bound_mod q_den hq_den R K_max hK_max C_exp η_exp M₀ hC_exp hη_exp hη_le hM₀ hexp
          n P a b hP_ge1 hPa hab hb2P A hA_bd r₀ hr₀_mem h hh₀ w W₀ hW₀ hw_bd hw_diff hw_tv
          d hd1 hdom_d.1 hdom_d.2.1 hdom_d.2.2
        dsimp only at h1
        have hcoeff_bd : ‖∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
            (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)‖ ≤
            2 * Real.log P := by
          have hle_logd : ‖∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
              (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)‖ ≤ Real.log d := by
            refine le_trans (norm_sum_le _ _) ?_
            have hpt : ∀ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
                ‖(ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)‖ ≤
                (ArithmeticFunction.vonMangoldt (d / u) : ℝ) := by
              intro u _
              rw [norm_mul, Complex.norm_intCast, Complex.norm_real,
                Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
              have hmu : |ArithmeticFunction.moebius u| ≤ 1 := by
                unfold ArithmeticFunction.moebius; split_ifs <;> simp [← neg_one_pow_eq_ite]
                exact abs_neg_one_pow _ |>.le
              exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (by exact_mod_cast hmu)
            refine le_trans (Finset.sum_le_sum hpt) ?_
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)) ?_
            have hswap : ∑ u ∈ d.divisors, (ArithmeticFunction.vonMangoldt (d / u) : ℝ) =
                ∑ k ∈ d.divisors, (ArithmeticFunction.vonMangoldt k : ℝ) := by
              rw [← Nat.sum_div_divisors]
            rw [hswap, ArithmeticFunction.vonMangoldt_sum]
          have hd_le_2P : (d : ℝ) ≤ 2 * P := by
            have h1 : (d : ℝ) ≤ (U : ℝ) ^ 2 := by exact_mod_cast hd_uu
            linarith [hU_sq_lt_P]
          have hlog_le : Real.log d ≤ Real.log (2 * P) := Real.log_le_log (by exact_mod_cast hd1) hd_le_2P
          linarith [hlog2P_le]
        rw [norm_mul]
        calc ‖∑ u ∈ _, _‖ * ‖∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r)‖
            ≤ (2 * Real.log P) * (4 * W₀ * max C_exp 3 *
                ((2 * P / d) / max (((q_den : ℝ)⁻¹ * (2 : ℝ) ^ (-(R : ℤ))) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))) :=
              mul_le_mul hcoeff_bd (by simpa [g, F] using h1) (norm_nonneg _) (by positivity)
          _ ≤ (2 * Real.log P) * (4 * W₀ * max C_exp 3 *
                (2 * (q_den : ℝ) * (2 : ℝ) ^ R * (P / d) * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h_err_sum d hd1 hd_uu) (by positivity)) (by positivity)
          _ = 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) *
                Real.log P * (1 / d : ℝ) := by ring
      calc ∑ d ∈ Finset.Icc 1 (U * U), ‖_‖
          ≤ ∑ d ∈ Finset.Icc 1 (U * U), 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * (1 / d : ℝ) := Finset.sum_le_sum hterm
        _ = 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * ∑ d ∈ Finset.Icc 1 (U * U), (1 / d : ℝ) := by
            rw [← Finset.mul_sum]
        _ ≤ 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * (2 * Real.log P) :=
            mul_le_mul_of_nonneg_left h_sum_inv_UU (by positivity)
        _ ≤ 64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P *
              (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 := by
            have hnn : 0 ≤ max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 := by positivity
            linarith [show 16 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * Real.log P * (2 * Real.log P) =
              32 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 2 by ring]
    -- Step 5: Dominance for Type II
    have hdom_II : ∀ (X₁ Y₁ Y₂ : ℕ), 1 ≤ X₁ → P ^ (1 / 3 : ℝ) / 8 ≤ (X₁ : ℝ) → 1 ≤ Y₁ → Y₁ ≤ Y₂ → Y₂ ≤ 2 * Y₁ →
        P / 4 ≤ (X₁ : ℝ) * (Y₁ : ℝ) →
        ∀ y₁ ∈ Finset.Icc Y₁ Y₂, ∀ y₂ ∈ Finset.Icc Y₁ Y₂, y₁ ≠ y₂ →
          (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
            |(h r : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))| *
                (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) ≤
              (1 / (2 * max (A.card : ℝ) 1)) *
                (|(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
                  (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)))) ∧
          |(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
              (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) ≤ (X₁ : ℝ) ^ (K_max - 1) := by
      intro X₁ Y₁ Y₂ hX₁ hX₁_lo hY₁ hY₁₂ hY₂ hXY_lo y₁ hy₁ y₂ hy₂ hy_ne
      have hX₁_pos : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
      have hY₁_pos : (0 : ℝ) < Y₁ := by exact_mod_cast hY₁
      have hy₁_mem := Finset.mem_Icc.mp hy₁
      have hy₂_mem := Finset.mem_Icc.mp hy₂
      have hr₀_1 : 1 ≤ r₀ := (hA_bd r₀ hr₀_mem).1
      have hr₀_R : r₀ ≤ R := (hA_bd r₀ hr₀_mem).2
      have hdiff0 := (y_pow_diff_bounds r₀ hr₀_1 Y₁ y₁ y₂ hY₁_pos
        (by exact_mod_cast hy₁_mem.1) (by exact_mod_cast hy₁_mem.2)
        (by exact_mod_cast hy₂_mem.1) (by exact_mod_cast hy₂_mem.2))
      constructor
      · intro k hk r hr hne
        by_cases hhr : h r = 0
        · simp [hhr]; positivity
        · have hr_gt : r₀ < r := lt_of_le_of_ne (h_min_r₀ r hr hhr) hne.symm
          have hr_R : r ≤ R := (hA_bd r hr).2
          have hdiffr := (y_pow_diff_bounds r (hA_bd r hr).1 Y₁ y₁ y₂ hY₁_pos
            (by exact_mod_cast hy₁_mem.1) (by exact_mod_cast hy₁_mem.2)
            (by exact_mod_cast hy₂_mem.1) (by exact_mod_cast hy₂_mem.2)).2
          have hh_r0 : (1 : ℝ) ≤ |(h r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hh₀
          have hh_r : |(h r : ℝ)| ≤ 2 * (Real.log n) ^ (R + 2) + 1 := by
            have h1 := hh_bd r hr
            have h2 : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
            have h3 : (|h r| : ℝ) ≤ 2 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1 := by exact_mod_cast h1
            linarith [show (|h r| : ℝ) = |(h r : ℝ)| by push_cast; rfl]
          have hdesc_le : (Nat.descFactorial (r + k - 1) k : ℝ) ≤ K_fact * (Nat.descFactorial (r₀ + k - 1) k : ℝ) := by
            have hk_le : k ≤ K_max := (Finset.mem_Icc.mp hk).2
            have h1 : Nat.descFactorial (r + k - 1) k ≤ (R + K_max).factorial := by
              exact le_trans (descFactorial_le_factorial (r + k - 1) k) (Nat.factorial_le (by omega))
            have h2 : 1 ≤ Nat.descFactorial (r₀ + k - 1) k := Nat.descFactorial_pos.mpr (by omega : k ≤ r₀ + k - 1)
            have h1R : (Nat.descFactorial (r + k - 1) k : ℝ) ≤ K_fact := by dsimp only [K_fact]; exact_mod_cast h1
            have h2R : (1 : ℝ) ≤ (Nat.descFactorial (r₀ + k - 1) k : ℝ) := by exact_mod_cast h2
            nlinarith
          have hA_le_R : max (A.card : ℝ) 1 ≤ (R : ℝ) := by
            have h1 : A.card ≤ R := le_trans (Finset.card_le_card hA_sub) (by rw [Nat.card_Icc]; omega)
            exact max_le (by exact_mod_cast h1) (by exact_mod_cast (by omega : 1 ≤ R))
          have hXY_sub : (X₁ : ℝ) ^ (-(r : ℤ)) * (Y₁ : ℝ) ^ (-(r + 1 : ℤ)) ≤
              (4 / P) * ((X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) := by
            have h1 : ((X₁ : ℝ) * (Y₁ : ℝ)) ^ (-(r - r₀ : ℤ)) ≤ (P / 4) ^ (-(r - r₀ : ℤ)) := by
              rw [show -(r - r₀ : ℤ) = -(((r - r₀ : ℕ) : ℤ)) by omega,
                zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
              exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hXY_lo _)
            have h2 : (P / 4) ^ (-(r - r₀ : ℤ)) ≤ (4 / P) := by
              rw [show -(r - r₀ : ℤ) = -(((r - r₀ : ℕ) : ℤ)) by omega,
                zpow_neg, zpow_natCast, inv_div]
              have hP4 : 1 ≤ P / 4 := by linarith
              calc (4 / P) ^ (r - r₀) ≤ (4 / P) ^ 1 := pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hP_pos]; linarith) (by omega)
                _ = 4 / P := pow_one _
            have h3 : (X₁ : ℝ) ^ (-(r : ℤ)) * (Y₁ : ℝ) ^ (-(r + 1 : ℤ)) =
                ((X₁ : ℝ) * (Y₁ : ℝ)) ^ (-(r - r₀ : ℤ)) * ((X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) := by
              rw [mul_zpow, show -(r : ℤ) = -(r - r₀ : ℤ) + -(r₀ : ℤ) by omega,
                show -(r + 1 : ℤ) = -(r - r₀ : ℤ) + -(r₀ + 1 : ℤ) by omega,
                zpow_add₀ hX₁_pos.ne', zpow_add₀ hY₁_pos.ne']
              ring
            rw [h3]
            exact mul_le_mul_of_nonneg_right (le_trans h1 h2) (by positivity)
          have hdom_P' : 4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
              (2 : ℝ) ^ (4 * R + 1) * (2 * (R : ℝ)) ≤ P := by
            have h1 : 4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
                (2 : ℝ) ^ (4 * R + 1) * (2 * (R : ℝ)) ≤
                (2 : ℝ) * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
                  (2 : ℝ) ^ (4 * R + 4) * (2 * (R : ℝ)) := by
              have h2eq : (4 : ℝ) * (2 : ℝ) ^ (4 * R + 1) ≤ (2 : ℝ) * (2 : ℝ) ^ (4 * R + 4) := by
                rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add, ← pow_succ']
                exact pow_le_pow_right₀ (by norm_num) (by omega)
              have hnn : 0 ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 * (R : ℝ)) := by positivity
              calc 4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (4 * R + 1) * (2 * (R : ℝ))
                  = (4 * (2 : ℝ) ^ (4 * R + 1)) * ((2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 * (R : ℝ))) := by ring
                _ ≤ (2 * (2 : ℝ) ^ (4 * R + 4)) * ((2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 * (R : ℝ))) :=
                    mul_le_mul_of_nonneg_right h2eq hnn
                _ = _ := by ring
            exact le_trans h1 (le_trans hdom_n hP_lo)
          have h2_prod : (2 : ℝ) ^ (r - 1) * (2 : ℝ) ^ (2 * r₀ : ℤ) * (2 : ℝ) ^ (r₀ : ℤ) ≤ (2 : ℝ) ^ (4 * R + 1) := by
            rw [← zpow_natCast (2 : ℝ) (r - 1), ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
              ← zpow_natCast (2 : ℝ) (4 * R + 1)]
            exact zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hr_le_R : (r : ℝ) ≤ R := by exact_mod_cast hr_R
          have hr0_ge1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast hr₀_1
          calc |(h r : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))| *
                (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ))
              = (|(h r : ℝ)| * (n : ℝ) / (q_den : ℝ)) * |(y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ))| *
                  (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) := by
                  rw [abs_mul, abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
                    abs_of_pos (a := (q_den : ℝ)) (by positivity)]
            _ ≤ ((2 * (Real.log n) ^ (R + 2) + 1) * (n : ℝ) / (q_den : ℝ)) *
                  ((r : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (r - 1) * (Y₁ : ℝ) ^ (-(r + 1 : ℤ))) *
                  (K_fact * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) * (X₁ : ℝ) ^ (-(r : ℤ)) := by
                  refine mul_le_mul (mul_le_mul (mul_le_mul (div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hh_r (by positivity)) (by positivity)) hdiffr (by positivity) (by positivity))
                    hdesc_le (by positivity) (by positivity)) le_rfl (by positivity) (by positivity)
            _ = (2 * (Real.log n) ^ (R + 2) + 1) * (r : ℝ) * K_fact * (2 : ℝ) ^ (r - 1) *
                  ((X₁ : ℝ) ^ (-(r : ℤ)) * (Y₁ : ℝ) ^ (-(r + 1 : ℤ))) *
                  ((n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by ring
            _ ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (r - 1) *
                  ((4 / P) * ((X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)))) *
                  ((n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr_le_R (by positivity)) (by positivity))
                    (by positivity)) hXY_sub (by positivity) (by positivity)) (by positivity)
            _ ≤ (1 / (2 * (R : ℝ) * (2 : ℝ) ^ (2 * r₀ : ℤ) * (2 : ℝ) ^ (r₀ : ℤ))) *
                  ((n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)) *
                    (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by
                  have hP_inv : (4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (r - 1)) / P ≤
                      1 / (2 * (R : ℝ) * (2 : ℝ) ^ (2 * r₀ : ℤ) * (2 : ℝ) ^ (r₀ : ℤ)) := by
                    rw [div_le_div_iff₀ hP_pos (by positivity)]
                    calc 4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (r - 1) *
                          (2 * (R : ℝ) * (2 : ℝ) ^ (2 * r₀ : ℤ) * (2 : ℝ) ^ (r₀ : ℤ))
                        = 4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
                            ((2 : ℝ) ^ (r - 1) * (2 : ℝ) ^ (2 * r₀ : ℤ) * (2 : ℝ) ^ (r₀ : ℤ)) * (2 * (R : ℝ)) := by ring
                      _ ≤ 4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact *
                            (2 : ℝ) ^ (4 * R + 1) * (2 * (R : ℝ)) :=
                          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2_prod (by positivity)) (by positivity)
                      _ ≤ 1 * P := by linarith [hdom_P']
                  have hnn : 0 ≤ (n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)) *
                      (Nat.descFactorial (r₀ + k - 1) k : ℝ) := by positivity
                  calc (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (r - 1) *
                        ((4 / P) * ((X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)))) *
                        ((n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (Nat.descFactorial (r₀ + k - 1) k : ℝ))
                      = ((4 * (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) * K_fact * (2 : ℝ) ^ (r - 1)) / P) *
                          ((n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)) *
                            (Nat.descFactorial (r₀ + k - 1) k : ℝ)) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_right hP_inv hnn
            _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                  (|(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
                    (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ))) := by
                  rw [abs_mul, abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
                    abs_of_pos (a := (2 : ℝ)) (by norm_num), mul_zpow, zpow_neg (2 : ℝ), zpow_natCast]
                  have h1 : (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) ≤
                      |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| := by
                    calc |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))
                        = 1 * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) := (one_mul _).symm
                      _ ≤ (r₀ : ℝ) * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) :=
                          mul_le_mul_of_nonneg_right hr0_ge1 (by positivity)
                      _ = (r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)) := by ring
                      _ ≤ |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| := hdiff0.1
                  have h2 : (1 / (2 * (R : ℝ))) ≤ 1 / (2 * max (A.card : ℝ) 1) :=
                    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hA_le_R (by norm_num))
                  calc (1 / (2 * (R : ℝ) * (2 : ℝ) ^ (2 * r₀ : ℤ) * (2 : ℝ) ^ (r₀ : ℤ))) *
                        ((n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) - y₂| * (X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ)) *
                          (Nat.descFactorial (r₀ + k - 1) k : ℝ))
                      = (1 / (2 * (R : ℝ))) * ((n : ℝ) / (q_den : ℝ) *
                          (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) *
                          (Nat.descFactorial (r₀ + k - 1) k : ℝ) * ((2 : ℝ) ^ (r₀ : ℤ))⁻¹ * (X₁ : ℝ) ^ (-(r₀ : ℤ))) := by
                          rw [zpow_neg (2 : ℝ), zpow_natCast]; ring
                    _ ≤ (1 / (2 * max (A.card : ℝ) 1)) * (|(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) *
                          |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| *
                          (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (((2 : ℝ) ^ r₀)⁻¹ * (X₁ : ℝ) ^ (-(r₀ : ℤ)))) := by
                          refine mul_le_mul h2 ?_ (by positivity) (by positivity)
                          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                            (mul_le_mul ?_ h1 (by positivity) (by positivity)) (by positivity)) (by positivity)) (by positivity)
                          calc (n : ℝ) / (q_den : ℝ) = 1 * (n : ℝ) / (q_den : ℝ) := by ring
                            _ ≤ |(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh_r0 (by positivity)) (by positivity)
                    _ = _ := by rw [zpow_neg, zpow_natCast]; ring
      · have hh_r0_le : |(h r₀ : ℝ)| ≤ 2 * (Real.log n) ^ (R + 2) + 1 := by
          have h1 := hh_bd r₀ hr₀_mem
          have h2 : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
          have h3 : (|h r₀| : ℝ) ≤ 2 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1 := by exact_mod_cast h1
          linarith [show (|h r₀| : ℝ) = |(h r₀ : ℝ)| by push_cast; rfl]
        have hdiff0_hi := hdiff0.2
        have hy_diff : |(y₁ : ℝ) - y₂| ≤ 2 * (Y₁ : ℝ) := by
          have h1 : (y₁ : ℝ) ≤ 2 * Y₁ := by exact_mod_cast hy₁_mem.2
          have h2 : (y₂ : ℝ) ≤ 2 * Y₁ := by exact_mod_cast hy₂_mem.2
          rw [abs_le]; constructor <;> linarith
        have hXY_pow : (X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ)) ≤ (4 / P) ^ r₀ := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← mul_inv, ← mul_pow,
            show (4 / P) ^ r₀ = (P / 4)⁻¹ ^ r₀ by rw [inv_div], ← inv_pow]
          exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hXY_lo) r₀
        have h4P_le : (4 / P) ^ r₀ ≤ 1 := by
          have h4P : 4 / P ≤ 1 := by rw [div_le_one hP_pos]; linarith
          exact pow_le_one₀ (by positivity) h4P
        have hr0_R : (r₀ : ℝ) ≤ R := by exact_mod_cast hr₀_R
        have hX1_ge : (n : ℝ) ^ (δ / 3) / 8 ≤ (X₁ : ℝ) := by
          have h1 : (n : ℝ) ^ (δ / 3) ≤ P ^ (1 / 3 : ℝ) := by
            rw [show δ / 3 = δ * (1 / 3 : ℝ) by ring, Real.rpow_mul (Nat.cast_nonneg n)]
            exact Real.rpow_le_rpow (by positivity) hP_lo (by positivity)
          linarith [hX₁_lo]
        have hpow_le : ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) ≤ (X₁ : ℝ) ^ (K_max - 1) :=
          pow_le_pow_left₀ (by positivity) hX1_ge _
        calc |(h r₀ : ℝ) * (n : ℝ) / (q_den : ℝ) * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
              (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ))
            = |(h r₀ : ℝ)| * (n : ℝ) / (q_den : ℝ) * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| *
                (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) := by
                rw [abs_mul, abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
                  abs_of_pos (a := (q_den : ℝ)) (by positivity)]
          _ ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (n : ℝ) / (q_den : ℝ) *
                ((r₀ : ℝ) * (2 * (Y₁ : ℝ)) * (2 : ℝ) ^ (r₀ - 1) * (Y₁ : ℝ) ^ (-(r₀ + 1 : ℤ))) *
                (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  (mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh_r0_le (by positivity)) (by norm_num))
                    (le_trans hdiff0_hi (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hy_diff (by positivity)) (by positivity)) (by positivity)))
                    (by positivity) (by positivity)) (by positivity)) (by positivity)
          _ = (2 * (Real.log n) ^ (R + 2) + 1) * (r₀ : ℝ) ^ 2 * (n : ℝ) * (2 : ℝ) ^ (r₀ : ℕ) *
                ((X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) := by
                rw [show -(r₀ + 1 : ℤ) = -(r₀ : ℤ) + (-1 : ℤ) by omega, zpow_add₀ hY₁_pos.ne',
                  zpow_neg_one, ← Nat.sub_add_cancel hr₀_1, pow_succ']
                field_simp [hY₁_pos.ne']
                ring
          _ ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R * 1 := by
                have h2q : (2 : ℝ) ^ r₀ ≤ (q_den : ℝ) * (2 : ℝ) ^ R := by
                  have hq1 : (1 : ℝ) ≤ q_den := by exact_mod_cast hq_den
                  have h2p : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) hr₀_R
                  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r₀]
                calc (2 * (Real.log n) ^ (R + 2) + 1) * (r₀ : ℝ) ^ 2 * (n : ℝ) * (2 : ℝ) ^ (r₀ : ℕ) *
                      ((X₁ : ℝ) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ)))
                    ≤ (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * ((q_den : ℝ) * (2 : ℝ) ^ R) * 1 :=
                      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr0_R 2) (by positivity)) (by positivity)) h2q (by positivity) (by positivity)) (le_trans hXY_pow h4P_le) (by positivity) (by positivity)
                  _ = (2 * (Real.log n) ^ (R + 2) + 1) * (R : ℝ) ^ 2 * (n : ℝ) * (q_den : ℝ) * (2 : ℝ) ^ R * 1 := by ring
          _ ≤ ((n : ℝ) ^ (δ / 3) / 8) ^ (K_max - 1) := by linarith [hT_n]
          _ ≤ (X₁ : ℝ) ^ (K_max - 1) := hpow_le
    -- Step 6: Bound Type II sum (`S3`)
    have hS3_bd : ‖∑ k ∈ Finset.Icc (U + 1) (B₀ / U), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ r ∈ Finset.Icc (max ((A₀ - 1) / k + 1) (U + 1)) (B₀ / k),
            (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r)‖ ≤
        C_II * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
      by_cases h_empty3 : B₀ / U < U + 1
      · rw [Finset.Icc_eq_empty (not_le.mpr h_empty3), Finset.sum_empty, norm_zero]
        positivity
      · push_neg at h_empty3
        set j₁ := Nat.log 2 (U + 1)
        set j₂ := Nat.log 2 (B₀ / U)
        have hj₁₂ : j₁ ≤ j₂ := Nat.log_mono_right h_empty3
        have hpart_k : Finset.Icc (U + 1) (B₀ / U) =
            (Finset.Icc j₁ j₂).biUnion (fun j => Finset.Icc (max (U + 1) (2 ^ j)) (min (2 * 2 ^ j - 1) (B₀ / U))) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_biUnion]
          constructor
          · rintro ⟨hk1, hk2⟩
            refine ⟨Nat.log 2 k, ⟨Nat.log_mono_right hk1, Nat.log_mono_right hk2⟩, ?_, ?_⟩
            · exact le_max_iff.mpr (Or.inr (Nat.pow_log_le_self 2 (by omega)))
            · exact le_min (Nat.le_pred_of_lt (by simpa [two_mul] using Nat.lt_pow_succ_log_self (by norm_num) k)) hk2
          · rintro ⟨j, _, hk1, hk2⟩
            exact ⟨le_trans (le_max_left _ _) hk1, le_trans hk2 (min_le_right _ _)⟩
        have hdisj_k : (Finset.Icc j₁ j₂ : Set ℕ).PairwiseDisjoint
            (fun j => Finset.Icc (max (U + 1) (2 ^ j)) (min (2 * 2 ^ j - 1) (B₀ / U))) := by
          intro j _ j' _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro k hk hk'
          simp only [Finset.mem_Icc] at hk hk'
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have h2 : 2 * 2 ^ j ≤ 2 ^ j' := by
              rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hlt
            omega
          · have h2 : 2 * 2 ^ j' ≤ 2 ^ j := by
              rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hgt
            omega
        rw [hpart_k, Finset.sum_biUnion hdisj_k]
        refine le_trans (norm_sum_le _ _) ?_
        have hblock_bd : ∀ j ∈ Finset.Icc j₁ j₂,
            ‖∑ k ∈ Finset.Icc (max (U + 1) (2 ^ j)) (min (2 * 2 ^ j - 1) (B₀ / U)),
              (ArithmeticFunction.vonMangoldt k : ℂ) *
                ∑ r ∈ Finset.Icc (max ((A₀ - 1) / k + 1) (U + 1)) (B₀ / k),
                  (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r)‖ ≤
            6 * Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) := by
          intro j _
          set K₁ := max (U + 1) (2 ^ j)
          set K₂ := min (2 * 2 ^ j - 1) (B₀ / U)
          by_cases hK₁₂ : K₂ < K₁
          · rw [Finset.Icc_eq_empty (not_le.mpr hK₁₂), Finset.sum_empty, norm_zero]
            positivity
          · push_neg at hK₁₂
            have hK₁_pos : 1 ≤ K₁ := le_trans (by omega : 1 ≤ U + 1) (le_max_left _ _)
            have hK₂_2K₁ : K₂ ≤ 2 * K₁ := by
              have h1 : K₂ ≤ 2 * 2 ^ j - 1 := min_le_left _ _
              have h2 : 2 ^ j ≤ K₁ := le_max_right _ _
              omega
            have hK₁_ge_P13 : P ^ (1 / 3 : ℝ) ≤ (K₁ : ℝ) := by
              have h1 : P ^ (1 / 3 : ℝ) < (U : ℝ) + 1 := Nat.lt_floor_add_one _
              have h2 : (U + 1 : ℝ) ≤ K₁ := by exact_mod_cast le_max_left (U + 1) (2 ^ j)
              linarith
            have hK₁_M0 : M₀ ≤ (K₁ : ℝ) := by
              linarith [le_max_left (8 * M₀ + 8) (Real.exp 2), hP13_ge, hK₁_ge_P13]
            let c_r : ℕ → ℂ := fun r => -∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)
            have hc_r_bd : ∀ r : ℕ, ‖c_r r‖ ≤ (r.divisors.card : ℝ) := by
              intro r; dsimp only [c_r]; rw [norm_neg]
              refine le_trans (norm_sum_le _ _) ?_
              have hpt : ∀ d ∈ r.divisors.filter (· ≤ U), ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
                intro d _; rw [Complex.norm_intCast]
                have hmu : |ArithmeticFunction.moebius d| ≤ 1 := by
                  unfold ArithmeticFunction.moebius; split_ifs <;> simp [← neg_one_pow_eq_ite]
                  exact abs_neg_one_pow _ |>.le
                exact_mod_cast hmu
              refine le_trans (Finset.sum_le_sum hpt) ?_
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
              exact_mod_cast Finset.card_filter_le _ _
            have hLam_sq : ∀ X₁ X₂ : ℕ, 1 ≤ X₁ → X₂ ≤ 2 * X₁ → X₂ ≤ B₀ →
                ∑ x ∈ Finset.Icc X₁ X₂, ‖(ArithmeticFunction.vonMangoldt x : ℂ)‖ ^ 2 ≤
                  4 * (Real.log 4 + 4) * (X₁ : ℝ) * Real.log P := by
              intro X₁ X₂ hX₁ hX₂ hX₂B
              have hpt : ∀ x ∈ Finset.Icc X₁ X₂,
                  ‖(ArithmeticFunction.vonMangoldt x : ℂ)‖ ^ 2 ≤
                    (Real.log (2 * P)) * (ArithmeticFunction.vonMangoldt x : ℝ) := by
                intro x hx
                rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, sq]
                refine mul_le_mul_of_nonneg_right ?_ ArithmeticFunction.vonMangoldt_nonneg
                have hx_le : (x : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast le_trans (Finset.mem_Icc.mp hx).2 hX₂B) hB₀_le_2P
                have hx_pos : 0 < x := lt_of_lt_of_le hX₁ (Finset.mem_Icc.mp hx).1
                exact le_trans (ArithmeticFunction.vonMangoldt_le_log)
                  (Real.log_le_log (by exact_mod_cast hx_pos) hx_le)
              have hsub : Finset.Icc X₁ X₂ ⊆ Finset.Icc 1 X₂ := fun x hx =>
                Finset.mem_Icc.mpr ⟨le_trans hX₁ (Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hx).2⟩
              have hsum_le : ∑ x ∈ Finset.Icc X₁ X₂, (ArithmeticFunction.vonMangoldt x : ℝ) ≤
                  (Real.log 4 + 4) * (2 * X₁ : ℝ) := by
                by_cases hX₂0 : X₂ = 0
                · rw [hX₂0]; simp [Finset.Icc_eq_empty (by omega : ¬ X₁ ≤ 0)]; positivity
                · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)) ?_
                  refine le_trans (sum_vonMangoldt_le X₂ (by omega)) ?_
                  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hX₂) (by positivity)
              calc ∑ x ∈ Finset.Icc X₁ X₂, ‖(ArithmeticFunction.vonMangoldt x : ℂ)‖ ^ 2
                  ≤ ∑ x ∈ Finset.Icc X₁ X₂, (Real.log (2 * P)) * (ArithmeticFunction.vonMangoldt x : ℝ) :=
                    Finset.sum_le_sum hpt
                _ = Real.log (2 * P) * ∑ x ∈ Finset.Icc X₁ X₂, (ArithmeticFunction.vonMangoldt x : ℝ) := by
                    rw [← Finset.mul_sum]
                _ ≤ Real.log (2 * P) * ((Real.log 4 + 4) * (2 * X₁ : ℝ)) :=
                    mul_le_mul_of_nonneg_left hsum_le (Real.log_nonneg (by linarith))
                _ ≤ (2 * Real.log P) * ((Real.log 4 + 4) * (2 * X₁ : ℝ)) := by
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    linarith [hlog2P_le]
                _ = 4 * (Real.log 4 + 4) * (X₁ : ℝ) * Real.log P := by ring
            have hCr_sq : ∀ Y₁ Y₂ : ℕ, 1 ≤ Y₁ → Y₂ ≤ 2 * Y₁ → Y₂ ≤ B₀ →
                ∑ y ∈ Finset.Icc Y₁ Y₂, ‖c_r y‖ ^ 2 ≤ 16 * (Y₁ : ℝ) * (Real.log P) ^ 3 := by
              intro Y₁ Y₂ hY₁ hY₂ hY₂B
              by_cases hY₁₂ : Y₂ < Y₁
              · rw [Finset.Icc_eq_empty (not_le.mpr hY₁₂), Finset.sum_empty]; positivity
              · push_neg at hY₁₂
                have hsub : Finset.Icc Y₁ Y₂ ⊆ Finset.Icc 1 Y₂ := fun y hy =>
                  Finset.mem_Icc.mpr ⟨le_trans hY₁ (Finset.mem_Icc.mp hy).1, (Finset.mem_Icc.mp hy).2⟩
                have hsum_d := sum_divisors_card_sq_le Y₂ (by omega)
                have hY2_pos : (0 : ℝ) < Y₂ := by exact_mod_cast (by omega : 0 < Y₂)
                have hY2_2P : (Y₂ : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hY₂B) hB₀_le_2P
                have hlog_bd : 1 + Real.log Y₂ ≤ 2 * Real.log P := by
                  linarith [Real.log_le_log hY2_pos hY2_2P, hlog2P_le]
                calc ∑ y ∈ Finset.Icc Y₁ Y₂, ‖c_r y‖ ^ 2
                    ≤ ∑ y ∈ Finset.Icc Y₁ Y₂, (y.divisors.card : ℝ) ^ 2 :=
                      Finset.sum_le_sum fun y _ => pow_le_pow_left₀ (norm_nonneg _) (hc_r_bd y) 2
                  _ ≤ ∑ y ∈ Finset.Icc 1 Y₂, (y.divisors.card : ℝ) ^ 2 :=
                      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
                  _ ≤ (Y₂ : ℝ) * (1 + Real.log Y₂) ^ 3 := hsum_d
                  _ ≤ (2 * (Y₁ : ℝ)) * (2 * Real.log P) ^ 3 :=
                      mul_le_mul (by exact_mod_cast hY₂) (pow_le_pow_left₀ (by
                        linarith [Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y₂) : (1 : ℝ) ≤ Y₂)]) hlog_bd 3)
                        (by positivity) (by positivity)
                  _ = 16 * (Y₁ : ℝ) * (Real.log P) ^ 3 := by ring
            -- Helper for a single `(X₁, X_top, Y₁, Y₂)` sub-block
            have hsub_block : ∀ (X₁ X_top Y₁ Y₂ : ℕ) (a_c b_c : ℕ → ℂ) (A_n B_n : ℝ),
                1 ≤ X₁ → M₀ ≤ (X₁ : ℝ) → P ^ (1 / 3 : ℝ) / 8 ≤ (X₁ : ℝ) → X_top ≤ 2 * X₁ →
                (X₁ : ℝ) ≤ 2 * Real.sqrt P →
                1 ≤ Y₁ → Y₁ ≤ Y₂ → Y₂ ≤ 2 * Y₁ →
                P / 4 ≤ (X₁ : ℝ) * (Y₁ : ℝ) → (2 * X₁ : ℝ) * (2 * Y₁ : ℝ) ≤ 16 * P →
                ∑ x ∈ Finset.Icc X₁ X_top, ‖a_c x‖ ^ 2 ≤ A_n →
                ∑ y ∈ Finset.Icc Y₁ Y₂, ‖b_c y‖ ^ 2 ≤ B_n →
                0 ≤ A_n → 0 ≤ B_n →
                A_n * B_n ≤ 256 * (Real.log 4 + 4) * P * (Real.log P) ^ 4 →
                ‖∑ x ∈ Finset.Icc X₁ X_top, a_c x *
                    ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => A₀ ≤ x * y ∧ x * y ≤ B₀),
                      b_c y * (w (x * y) : ℂ) * ePhase (F (x * y))‖ ≤
                  Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) := by
              intro X₁ X_top Y₁ Y₂ a_c b_c A_n B_n hX₁ hM0X hX1_lo hX_top hX_sq hY₁ hY₁₂ hY₂ hXY_lo hXY_hi hAn hBn hAnn hBnn hAB
              have htb := type_II_block_bound_mod q_den hq_den R K_max hK_max C_exp η_exp M₀ hC_exp hη_exp hη_le hM₀ hexp
                n P a b hP_ge1 hPa hab hb2P A hA_bd r₀ hr₀_mem h hh₀ w W₀ hW₀ hw_bd hw_diff hw_tv
                X₁ X_top Y₁ Y₂ hX₁ hM0X hX_top hY₁ hY₁₂ hY₂ hXY_hi hX_sq a_c b_c A_n B_n hAn hBn hAnn hBnn
                (hdom_II X₁ Y₁ Y₂ hX₁ hX1_lo hY₁ hY₁₂ hY₂ hXY_lo) hT₀_ge1
              dsimp only at htb
              have hT_le : T₀ ^ (-2 / 3 : ℝ) ≤ T₀ ^ (-1 / 3 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hT₀_ge1 (by norm_num)
              have hX_pow : (2 * (X₁ : ℝ)) ^ (-η_exp) ≤ 2 * P ^ (-2 * η'_δ) := by
                have h1 : P ^ (1 / 3 : ℝ) / 4 ≤ 2 * (X₁ : ℝ) := by linarith
                have h2 : (2 * (X₁ : ℝ)) ^ (-η_exp) ≤ (P ^ (1 / 3 : ℝ) / 4) ^ (-η_exp) :=
                  Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith [hη_exp])
                have h3 : (P ^ (1 / 3 : ℝ) / 4) ^ (-η_exp) = (4 : ℝ) ^ η_exp * P ^ (-η_exp / 3) := by
                  rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
                    ← Real.rpow_mul hP_pos.le, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
                  ring_nf
                have h4 : (4 : ℝ) ^ η_exp ≤ 2 := by
                  calc (4 : ℝ) ^ η_exp ≤ (4 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη_le
                    _ ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                    _ = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
                have h5 : P ^ (-η_exp / 3) ≤ P ^ (-2 * η'_δ) := by
                  refine Real.rpow_le_rpow_of_exponent_le hP_ge1 ?_
                  have : η'_δ ≤ η_exp / 6 := min_le_left _ _
                  linarith
                calc (2 * (X₁ : ℝ)) ^ (-η_exp) ≤ (4 : ℝ) ^ η_exp * P ^ (-η_exp / 3) := h2.trans_eq h3
                  _ ≤ 2 * P ^ (-2 * η'_δ) := mul_le_mul h4 h5 (by positivity) (by norm_num)
              have hP_half : P ^ (1 / 2 : ℝ) ≤ P * P ^ (-2 * η'_δ) := by
                have hrhs : P * P ^ (-2 * η'_δ) = P ^ (1 + -2 * η'_δ) := by
                  rw [Real.rpow_add hP_pos, Real.rpow_one]
                rw [hrhs]
                refine Real.rpow_le_rpow_of_exponent_le hP_ge1 ?_
                have : η'_δ ≤ 1 / 12 := min_le_right _ _
                linarith
              have h_inner_le : 32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
                    128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
                    128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp) ≤
                  256 * (1 + ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp + C_exp) * P *
                    (T₀ ^ (-1 / 3 : ℝ) + P ^ (-2 * η'_δ)) := by
                have hA1 : 32 * P * T₀ ^ (-1 / 3 : ℝ) + 128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) ≤
                    256 * (1 + ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp + C_exp) * P * T₀ ^ (-1 / 3 : ℝ) := by
                  have h1 : 128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) ≤
                      128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-1 / 3 : ℝ) :=
                    mul_le_mul_of_nonneg_left hT_le (by positivity)
                  have h2 : 0 ≤ P * T₀ ^ (-1 / 3 : ℝ) := by positivity
                  have h3 : 0 ≤ ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-1 / 3 : ℝ) := by positivity
                  have h4 : 0 ≤ C_exp * P * T₀ ^ (-1 / 3 : ℝ) := by positivity
                  linarith
                have hA2 : 8 * P ^ (1 / 2 : ℝ) + 128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp) ≤
                    256 * (1 + ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp + C_exp) * P * P ^ (-2 * η'_δ) := by
                  have h1 : 8 * P ^ (1 / 2 : ℝ) ≤ 8 * (P * P ^ (-2 * η'_δ)) := mul_le_mul_of_nonneg_left hP_half (by norm_num)
                  have h2 : 128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp) ≤ 256 * C_exp * P * P ^ (-2 * η'_δ) := by
                    have := mul_le_mul_of_nonneg_left hX_pow (by positivity : 0 ≤ 128 * C_exp * P)
                    linarith
                  have h3 : 0 ≤ ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * P ^ (-2 * η'_δ) := by positivity
                  have h4 : 0 ≤ P * P ^ (-2 * η'_δ) := by positivity
                  linarith
                linarith
              have hsq_le : ‖∑ x ∈ Finset.Icc X₁ X_top, a_c x *
                    ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => A₀ ≤ x * y ∧ x * y ≤ B₀),
                      b_c y * (w (x * y) : ℂ) * ePhase (F (x * y))‖ ^ 2 ≤
                  (Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ))) ^ 2 := by
                have hT_sq : T₀ ^ (-1 / 3 : ℝ) = (T₀ ^ (-1 / 6 : ℝ)) ^ 2 := by
                  rw [← Real.rpow_natCast (T₀ ^ _), ← Real.rpow_mul (by linarith)]; norm_num
                have hP_sq : P ^ (-2 * η'_δ) = (P ^ (-η'_δ)) ^ 2 := by
                  rw [← Real.rpow_natCast (P ^ _), ← Real.rpow_mul hP_pos.le]; norm_num
                have hsum_sq : T₀ ^ (-1 / 3 : ℝ) + P ^ (-2 * η'_δ) ≤ (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) ^ 2 := by
                  rw [hT_sq, hP_sq]; nlinarith [Real.rpow_pos_of_pos (by linarith : 0 < T₀) (-1 / 6 : ℝ),
                    Real.rpow_pos_of_pos hP_pos (-η'_δ)]
                calc ‖∑ x ∈ _, _‖ ^ 2
                    ≤ A_n * B_n * W₀ ^ 2 * (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
                        128 * ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
                        128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := htb
                  _ ≤ (256 * (Real.log 4 + 4) * P * (Real.log P) ^ 4) * W₀ ^ 2 *
                        (256 * (1 + ((q_den : ℝ) * (2 : ℝ) ^ (5 * R + 1)) * C_exp + C_exp) * P *
                          (T₀ ^ (-1 / 3 : ℝ) + P ^ (-2 * η'_δ))) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right hAB (sq_nonneg W₀)) h_inner_le (by positivity) (by positivity)
                  _ = C_II_sq * W₀ ^ 2 * P ^ 2 * (Real.log P) ^ 4 * (T₀ ^ (-1 / 3 : ℝ) + P ^ (-2 * η'_δ)) := by
                      dsimp only [C_II_sq]; ring
                  _ ≤ C_II_sq * W₀ ^ 2 * P ^ 2 * (Real.log P) ^ 4 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) ^ 2 :=
                      mul_le_mul_of_nonneg_left hsum_sq (by positivity)
                  _ = (Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ))) ^ 2 := by
                      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
              exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq_le
            -- Now apply `hsub_block` by splitting `[Y_lo, Y_hi]` into at most 3 dyadic pieces!
            set Y_lo := max (U + 1) (A₀ / (2 * K₁))
            set Y_hi := B₀ / K₁
            have hY_lo_hi : ∀ k ∈ Finset.Icc K₁ K₂,
                Finset.Icc (max ((A₀ - 1) / k + 1) (U + 1)) (B₀ / k) =
                (Finset.Icc Y_lo Y_hi).filter (fun r => A₀ ≤ k * r ∧ k * r ≤ B₀) := by
              intro k hk
              have hk_mem := Finset.mem_Icc.mp hk
              ext r
              simp only [Finset.mem_filter, Finset.mem_Icc, Y_lo, Y_hi]
              constructor
              · rintro ⟨hr1, hr2⟩
                have hr_U : U + 1 ≤ r := le_trans (le_max_right _ _) hr1
                have hr_A : (A₀ - 1) / k + 1 ≤ r := le_trans (le_max_left _ _) hr1
                have hAk : A₀ ≤ k * r := by
                  have := Nat.lt_mul_div_succ (A₀ - 1) (by omega : 0 < k)
                  nlinarith
                have hkB : k * r ≤ B₀ := by
                  calc k * r ≤ k * (B₀ / k) := Nat.mul_le_mul_left k hr2
                    _ ≤ B₀ := Nat.mul_div_le B₀ k
                have hr_A2 : A₀ / (2 * K₁) ≤ r := by
                  exact Nat.div_le_of_le_mul (le_trans hAk (Nat.mul_le_mul_right r (by omega)))
                have hr_B1 : r ≤ B₀ / K₁ := le_trans hr2 (Nat.div_le_div_left hk_mem.1 hK₁_pos)
                exact ⟨⟨max_le hr_U hr_A2, hr_B1⟩, hAk, hkB⟩
              · rintro ⟨⟨hr_lo, _⟩, hAk, hkB⟩
                have hr_U : U + 1 ≤ r := le_trans (le_max_left _ _) hr_lo
                have hr_A : (A₀ - 1) / k + 1 ≤ r :=
                  Nat.succ_le_of_lt (Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega))
                exact ⟨max_le hr_A hr_U, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩
            -- Split `[Y_lo, Y_hi]` into at most 3 dyadic intervals `[Y_lo, 2*Y_lo]`, `[2*Y_lo+1, 4*Y_lo]`, `[4*Y_lo+1, Y_hi]`
            -- First check `Y_hi ≤ 8 * Y_lo` (when `Y_lo ≤ Y_hi`):
            by_cases hY_empty : Y_hi < Y_lo
            · have h0 : ∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                  ∑ r ∈ Finset.Icc (max ((A₀ - 1) / k + 1) (U + 1)) (B₀ / k), c_r r * g (k * r) = 0 := by
                refine Finset.sum_eq_zero fun k hk => ?_
                rw [hY_lo_hi k hk, Finset.Icc_eq_empty (not_le.mpr hY_empty), Finset.filter_empty, Finset.sum_empty, mul_zero]
              simpa [c_r] using by rw [h0, norm_zero]; positivity
            · push_neg at hY_empty
              have hY_lo_pos : 1 ≤ Y_lo := le_trans (by omega : 1 ≤ U + 1) (le_max_left _ _)
              have hY_hi_8 : Y_hi ≤ 8 * Y_lo := by
                -- `Y_hi = B₀ / K₁ ≤ 2 * P / K₁`, and `Y_lo ≥ A₀ / (2 * K₁) ≥ (P - 2 K₁) / (2 K₁)`
                have h1 : (Y_hi : ℝ) ≤ 2 * P / K₁ := by
                  rw [le_div_iff₀ (by exact_mod_cast hK₁_pos)]
                  exact le_trans (by exact_mod_cast Nat.div_mul_le_self B₀ K₁) hB₀_le_2P
                have h2 : P / (2 * K₁) - 1 ≤ (A₀ / (2 * K₁) : ℕ) := by
                  have hlt : P / (2 * K₁) < ((A₀ / (2 * K₁) + 1 : ℕ) : ℝ) := by
                    rw [div_lt_iff₀ (by positivity)]
                    have : A₀ < (2 * K₁) * (A₀ / (2 * K₁) + 1) := Nat.lt_mul_div_succ A₀ (by omega)
                    have hPA : P ≤ (A₀ : ℝ) := le_trans hPa (Nat.le_ceil a)
                    exact lt_of_le_of_lt hPA (by exact_mod_cast (by linarith : A₀ < (A₀ / (2 * K₁) + 1) * (2 * K₁)))
                  push_cast at hlt; linarith
                have h2' : P / (4 * K₁) ≤ (Y_lo : ℝ) := by
                  have h1 : 2 * (K₁ : ℝ) ≤ P / 2 := by
                    have hK2_BU : (K₁ : ℝ) ≤ B₀ / U := by exact_mod_cast le_trans hK₁₂ (min_le_right _ _)
                    have hP13_16 : 16 ≤ P ^ (1 / 3 : ℝ) := by linarith [le_trans (le_max_left _ _) hP13_ge, hM₀]
                    have hU_half : P ^ (1 / 3 : ℝ) / 2 ≤ (U : ℝ) := by
                      linarith [Nat.lt_floor_add_one (P ^ (1 / 3 : ℝ))]
                    have hBU : (B₀ : ℝ) / U ≤ 2 * P / (P ^ (1 / 3 : ℝ) / 2) :=
                      div_le_div₀ (by positivity) hB₀_le_2P (by positivity) hU_half
                    have h8 : 8 * P ^ (2 / 3 : ℝ) ≤ P / 2 := by
                      calc 8 * P ^ (2 / 3 : ℝ) ≤ (P ^ (1 / 3 : ℝ) / 2) * P ^ (2 / 3 : ℝ) :=
                            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
                        _ = P / 2 := by rw [div_mul_eq_mul_div, ← Real.rpow_add hP_pos]; norm_num
                    calc 2 * (K₁ : ℝ) ≤ 2 * (2 * P / (P ^ (1 / 3 : ℝ) / 2)) := by linarith
                      _ = 8 * P ^ (2 / 3 : ℝ) := by
                          rw [show P = P ^ (1 / 3 : ℝ) * P ^ (2 / 3 : ℝ) by rw [← Real.rpow_add hP_pos]; norm_num]
                          field_simp [(Real.rpow_pos_of_pos hP_pos _).ne']; ring
                      _ ≤ P / 2 := h8
                  have h_one : 1 ≤ P / (4 * K₁) := by
                    rw [le_div_iff₀ (by positivity)]; linarith
                  have hY_A : (A₀ / (2 * K₁) : ℝ) ≤ (Y_lo : ℝ) := by exact_mod_cast le_max_right (U + 1) (A₀ / (2 * K₁))
                  linarith
                have h8_real : (Y_hi : ℝ) ≤ 8 * (Y_lo : ℝ) := by
                  calc (Y_hi : ℝ) ≤ 2 * P / K₁ := h1
                    _ = 8 * (P / (4 * K₁)) := by ring
                    _ ≤ 8 * (Y_lo : ℝ) := mul_le_mul_of_nonneg_left h2' (by norm_num)
                exact_mod_cast h8_real
              have hP4_lo : P / 4 ≤ (K₁ : ℝ) * (Y_lo : ℝ) := by
                have h1 : P / (4 * K₁) ≤ (Y_lo : ℝ) := by
                  have hK2_BU : (K₁ : ℝ) ≤ B₀ / U := by exact_mod_cast le_trans hK₁₂ (min_le_right _ _)
                  have hP13_16 : 16 ≤ P ^ (1 / 3 : ℝ) := by linarith [le_trans (le_max_left _ _) hP13_ge, hM₀]
                  have hU_half : P ^ (1 / 3 : ℝ) / 2 ≤ (U : ℝ) := by linarith [Nat.lt_floor_add_one (P ^ (1 / 3 : ℝ))]
                  have hBU : (B₀ : ℝ) / U ≤ 2 * P / (P ^ (1 / 3 : ℝ) / 2) :=
                    div_le_div₀ (by positivity) hB₀_le_2P (by positivity) hU_half
                  have h8 : 8 * P ^ (2 / 3 : ℝ) ≤ P / 2 := by
                    calc 8 * P ^ (2 / 3 : ℝ) ≤ (P ^ (1 / 3 : ℝ) / 2) * P ^ (2 / 3 : ℝ) :=
                          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
                      _ = P / 2 := by rw [div_mul_eq_mul_div, ← Real.rpow_add hP_pos]; norm_num
                  have h2K : 2 * (K₁ : ℝ) ≤ P / 2 := by
                    calc 2 * (K₁ : ℝ) ≤ 2 * (2 * P / (P ^ (1 / 3 : ℝ) / 2)) := by linarith
                      _ = 8 * P ^ (2 / 3 : ℝ) := by
                          rw [show P = P ^ (1 / 3 : ℝ) * P ^ (2 / 3 : ℝ) by rw [← Real.rpow_add hP_pos]; norm_num]
                          field_simp [(Real.rpow_pos_of_pos hP_pos _).ne']; ring
                      _ ≤ P / 2 := h8
                  have h2 : P / (2 * K₁) - 1 ≤ (A₀ / (2 * K₁) : ℕ) := by
                    have hlt : P / (2 * K₁) < ((A₀ / (2 * K₁) + 1 : ℕ) : ℝ) := by
                      rw [div_lt_iff₀ (by positivity)]
                      have : A₀ < (2 * K₁) * (A₀ / (2 * K₁) + 1) := Nat.lt_mul_div_succ A₀ (by omega)
                      have hPA : P ≤ (A₀ : ℝ) := le_trans hPa (Nat.le_ceil a)
                      exact lt_of_le_of_lt hPA (by exact_mod_cast (by linarith : A₀ < (A₀ / (2 * K₁) + 1) * (2 * K₁)))
                    push_cast at hlt; linarith
                  have h_one : 1 ≤ P / (4 * K₁) := by rw [le_div_iff₀ (by positivity)]; linarith
                  have hY_A : (A₀ / (2 * K₁) : ℝ) ≤ (Y_lo : ℝ) := by exact_mod_cast le_max_right (U + 1) (A₀ / (2 * K₁))
                  linarith
                calc P / 4 = (K₁ : ℝ) * (P / (4 * K₁)) := by field_simp [(by exact_mod_cast hK₁_pos : (0 : ℝ) < K₁).ne']
                  _ ≤ (K₁ : ℝ) * (Y_lo : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
              have hY_hi_2P : (Y_hi : ℝ) ≤ 2 * P / K₁ := by
                rw [le_div_iff₀ (by exact_mod_cast hK₁_pos)]
                exact le_trans (by exact_mod_cast Nat.div_mul_le_self B₀ K₁) hB₀_le_2P
              have hY_hi_B0 : Y_hi ≤ B₀ := Nat.div_le_self B₀ K₁
              have hK₂_B0 : K₂ ≤ B₀ := le_trans (min_le_right _ _) (Nat.div_le_self B₀ U)
              -- Split `Finset.Icc Y_lo Y_hi` into `[Y_lo, min Y_hi (2 * Y_lo)]`, `[2 * Y_lo + 1, min Y_hi (4 * Y_lo)]`, `[4 * Y_lo + 1, Y_hi]`
              have hpart_Y : Finset.Icc Y_lo Y_hi =
                  Finset.Icc Y_lo (min Y_hi (2 * Y_lo)) ∪
                  Finset.Icc (2 * Y_lo + 1) (min Y_hi (4 * Y_lo)) ∪
                  Finset.Icc (4 * Y_lo + 1) Y_hi := by
                ext r; simp only [Finset.mem_union, Finset.mem_Icc]; omega
              have hd12 : Disjoint (Finset.Icc Y_lo (min Y_hi (2 * Y_lo)))
                  (Finset.Icc (2 * Y_lo + 1) (min Y_hi (4 * Y_lo))) := by
                rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
              have hd123 : Disjoint (Finset.Icc Y_lo (min Y_hi (2 * Y_lo)) ∪
                  Finset.Icc (2 * Y_lo + 1) (min Y_hi (4 * Y_lo))) (Finset.Icc (4 * Y_lo + 1) Y_hi) := by
                rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_union, Finset.mem_Icc] at h1 h2; omega
              -- Helper for one `(Y_a, Y_b)` piece
              have hpiece : ∀ (Y_a Y_b : ℕ), Y_lo ≤ Y_a → Y_b ≤ Y_hi → Y_b ≤ 2 * Y_a →
                  ‖∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                      ∑ r ∈ (Finset.Icc Y_a Y_b).filter (fun r => A₀ ≤ k * r ∧ k * r ≤ B₀),
                        c_r r * g (k * r)‖ ≤
                    Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) := by
                intro Y_a Y_b hYa hYb hYb2
                by_cases hYab : Y_b < Y_a
                · rw [Finset.Icc_eq_empty (not_le.mpr hYab), Finset.filter_empty]
                  simp; positivity
                · push_neg at hYab
                  have hYa_pos : 1 ≤ Y_a := le_trans hY_lo_pos hYa
                  have hKY_lo : P / 4 ≤ (K₁ : ℝ) * (Y_a : ℝ) :=
                    le_trans hP4_lo (mul_le_mul_of_nonneg_left (by exact_mod_cast hYa) (by positivity))
                  have hKY_hi : (2 * K₁ : ℝ) * (2 * Y_a : ℝ) ≤ 16 * P := by
                    have hYa_hi : (Y_a : ℝ) ≤ (Y_hi : ℝ) := by exact_mod_cast le_trans hYab hYb
                    calc (2 * K₁ : ℝ) * (2 * Y_a : ℝ) ≤ (2 * K₁ : ℝ) * (2 * (2 * P / K₁)) :=
                          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_trans hYa_hi hY_hi_2P) (by norm_num)) (by positivity)
                      _ = 8 * P := by field_simp [(by exact_mod_cast hK₁_pos : (0 : ℝ) < K₁).ne']; ring
                      _ ≤ 16 * P := by linarith
                  by_cases hK_sq : (K₁ : ℝ) ≤ 2 * Real.sqrt P
                  · have hAn := hLam_sq K₁ K₂ hK₁_pos hK₂_2K₁ hK₂_B0
                    have hBn := hCr_sq Y_a Y_b hYa_pos hYb2 (le_trans hYb hY_hi_B0)
                    have hAB : (4 * (Real.log 4 + 4) * (K₁ : ℝ) * Real.log P) * (16 * (Y_a : ℝ) * (Real.log P) ^ 3) ≤
                        256 * (Real.log 4 + 4) * P * (Real.log P) ^ 4 := by
                      have hKY4 : (K₁ : ℝ) * (Y_a : ℝ) ≤ 4 * P := by linarith [hKY_hi]
                      calc (4 * (Real.log 4 + 4) * (K₁ : ℝ) * Real.log P) * (16 * (Y_a : ℝ) * (Real.log P) ^ 3)
                          = 64 * (Real.log 4 + 4) * ((K₁ : ℝ) * (Y_a : ℝ)) * (Real.log P) ^ 4 := by ring
                        _ ≤ 64 * (Real.log 4 + 4) * (4 * P) * (Real.log P) ^ 4 :=
                            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKY4 (by positivity)) (by positivity)
                        _ = 256 * (Real.log 4 + 4) * P * (Real.log P) ^ 4 := by ring
                    exact hsub_block K₁ K₂ Y_a Y_b (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) c_r
                      (4 * (Real.log 4 + 4) * (K₁ : ℝ) * Real.log P) (16 * (Y_a : ℝ) * (Real.log P) ^ 3)
                      hK₁_pos hK₁_M0 (by linarith) hK₂_2K₁ hK_sq hYa_pos hYab hYb2 hKY_lo hKY_hi
                      hAn hBn (by positivity) (by positivity) hAB
                  · push_neg at hK_sq
                    -- Swap `k` and `r`!
                    have hswap : ∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                          ∑ r ∈ (Finset.Icc Y_a Y_b).filter (fun r => A₀ ≤ k * r ∧ k * r ≤ B₀),
                            c_r r * g (k * r) =
                        ∑ r ∈ Finset.Icc Y_a Y_b, c_r r *
                          ∑ k ∈ (Finset.Icc K₁ K₂).filter (fun k => A₀ ≤ r * k ∧ r * k ≤ B₀),
                            (ArithmeticFunction.vonMangoldt k : ℂ) * g (r * k) := by
                      simp_rw [Finset.mul_sum, Finset.sum_filter]
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun r _ => ?_
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun k _ => ?_
                      rw [mul_comm r k]
                      split_ifs <;> ring
                    rw [hswap]
                    have hYa_ge_P13 : P ^ (1 / 3 : ℝ) ≤ (Y_a : ℝ) := by
                      have h1 : P ^ (1 / 3 : ℝ) < (U : ℝ) + 1 := Nat.lt_floor_add_one _
                      have h2 : (U + 1 : ℝ) ≤ Y_a := by exact_mod_cast le_trans (le_max_left _ _) hYa
                      linarith
                    have hYa_M0 : M₀ ≤ (Y_a : ℝ) := by linarith [le_max_left (8 * M₀ + 8) (Real.exp 2), hP13_ge, hYa_ge_P13]
                    have hYa_sq : (Y_a : ℝ) ≤ 2 * Real.sqrt P := by
                      have h1 : (Y_a : ℝ) ≤ 2 * P / K₁ := le_trans (by exact_mod_cast le_trans hYab hYb) hY_hi_2P
                      calc (Y_a : ℝ) ≤ 2 * P / K₁ := h1
                        _ ≤ 2 * P / (2 * Real.sqrt P) :=
                            div_le_div_of_nonneg_left (by positivity) (by positivity) hK_sq.le
                        _ = Real.sqrt P := by
                            field_simp [(Real.sqrt_pos.mpr hP_pos).ne']
                            rw [Real.sq_sqrt hP_pos.le]; ring
                        _ ≤ 2 * Real.sqrt P := by linarith [Real.sqrt_pos.mpr hP_pos]
                    have hAn := hCr_sq Y_a Y_b hYa_pos hYb2 (le_trans hYb hY_hi_B0)
                    have hBn := hLam_sq K₁ K₂ hK₁_pos hK₂_2K₁ hK₂_B0
                    have hAB : (16 * (Y_a : ℝ) * (Real.log P) ^ 3) * (4 * (Real.log 4 + 4) * (K₁ : ℝ) * Real.log P) ≤
                        256 * (Real.log 4 + 4) * P * (Real.log P) ^ 4 := by
                      have hYK4 : (Y_a : ℝ) * (K₁ : ℝ) ≤ 4 * P := by linarith [hKY_hi]
                      calc (16 * (Y_a : ℝ) * (Real.log P) ^ 3) * (4 * (Real.log 4 + 4) * (K₁ : ℝ) * Real.log P)
                          = 64 * (Real.log 4 + 4) * ((Y_a : ℝ) * (K₁ : ℝ)) * (Real.log P) ^ 4 := by ring
                        _ ≤ 64 * (Real.log 4 + 4) * (4 * P) * (Real.log P) ^ 4 :=
                            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYK4 (by positivity)) (by positivity)
                        _ = 256 * (Real.log 4 + 4) * P * (Real.log P) ^ 4 := by ring
                    exact hsub_block Y_a Y_b K₁ K₂ c_r (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
                      (16 * (Y_a : ℝ) * (Real.log P) ^ 3) (4 * (Real.log 4 + 4) * (K₁ : ℝ) * Real.log P)
                      hYa_pos hYa_M0 (by linarith) hYb2 hYa_sq hK₁_pos hK₁₂ hK₂_2K₁
                      (by linarith [hKY_lo]) (by linarith [hKY_hi]) hAn hBn (by positivity) (by positivity) hAB
              have hrew_j : ∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                    ∑ r ∈ Finset.Icc (max ((A₀ - 1) / k + 1) (U + 1)) (B₀ / k),
                      (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) =
                  (∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                      ∑ r ∈ (Finset.Icc Y_lo (min Y_hi (2 * Y_lo))).filter (fun r => A₀ ≤ k * r ∧ k * r ≤ B₀),
                        c_r r * g (k * r)) +
                  (∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                      ∑ r ∈ (Finset.Icc (2 * Y_lo + 1) (min Y_hi (4 * Y_lo))).filter (fun r => A₀ ≤ k * r ∧ k * r ≤ B₀),
                        c_r r * g (k * r)) +
                  (∑ k ∈ Finset.Icc K₁ K₂, (ArithmeticFunction.vonMangoldt k : ℂ) *
                      ∑ r ∈ (Finset.Icc (4 * Y_lo + 1) Y_hi).filter (fun r => A₀ ≤ k * r ∧ k * r ≤ B₀),
                        c_r r * g (k * r)) := by
                rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun k hk => ?_
                rw [← mul_add, ← mul_add, hY_lo_hi k hk, hpart_Y,
                  Finset.filter_union, Finset.filter_union,
                  Finset.sum_union (Finset.disjoint_filter_filter hd123),
                  Finset.sum_union (Finset.disjoint_filter_filter hd12)]
              rw [hrew_j]
              have hp1 := hpiece Y_lo (min Y_hi (2 * Y_lo)) le_rfl (min_le_left _ _) (min_le_right _ _)
              have hp2 := hpiece (2 * Y_lo + 1) (min Y_hi (4 * Y_lo)) (by omega) (min_le_left _ _) (by
                have := min_le_right Y_hi (4 * Y_lo); omega)
              have hp3 := hpiece (4 * Y_lo + 1) Y_hi (by omega) le_rfl hY_hi_8
              have htri := le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
              linarith
        have hcard_j : ((Finset.Icc j₁ j₂).card : ℝ) ≤ 2 * Real.log P := by
          have hj2_bd : (j₂ : ℝ) ≤ (3 / 2 : ℝ) * Real.log P := by
            have h2pow : (2 : ℝ) ^ j₂ ≤ P := by
              have h1 : 2 ^ j₂ ≤ B₀ / U := Nat.pow_log_le_self 2 (by omega)
              have hU4 : 4 ≤ U := by
                have : (4 : ℝ) ≤ (U : ℝ) := by linarith [hU_ge_M0, hM₀]
                exact_mod_cast this
              have h2 : B₀ / U ≤ B₀ / 4 := Nat.div_le_div_left hU4 (by norm_num)
              have h3 : ((B₀ / 4 : ℕ) : ℝ) ≤ (B₀ : ℝ) / 4 := by
                rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
                exact_mod_cast Nat.div_mul_le_self B₀ 4
              have h1r : (2 : ℝ) ^ j₂ ≤ ((B₀ / U : ℕ) : ℝ) := by exact_mod_cast h1
              have h2r : ((B₀ / U : ℕ) : ℝ) ≤ ((B₀ / 4 : ℕ) : ℝ) := by exact_mod_cast h2
              linarith [hB₀_le_2P, hP_pos]
            have hlog : (j₂ : ℝ) * Real.log 2 ≤ Real.log P := by
              have := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j₂) h2pow
              rwa [Real.log_pow] at this
            have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
            have hj2_nn : (0 : ℝ) ≤ j₂ := Nat.cast_nonneg j₂
            nlinarith
          have hcard_le : (Finset.Icc j₁ j₂).card ≤ j₂ + 1 := by rw [Nat.card_Icc]; omega
          have h1 : ((Finset.Icc j₁ j₂).card : ℝ) ≤ (j₂ : ℝ) + 1 := by exact_mod_cast hcard_le
          have hlogP_ge6 : 6 ≤ Real.log P := by
            simpa using Real.log_le_log (Real.exp_pos 6) hP_ge_e6
          linarith
        calc ∑ j ∈ Finset.Icc j₁ j₂, ‖∑ k ∈ Finset.Icc (max (U + 1) (2 ^ j)) (min (2 * 2 ^ j - 1) (B₀ / U)), _‖
            ≤ ∑ _j ∈ Finset.Icc j₁ j₂,
                6 * Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) :=
              Finset.sum_le_sum hblock_bd
          _ = ((Finset.Icc j₁ j₂).card : ℝ) *
                (6 * Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 * Real.log P) *
                (6 * Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ))) :=
              mul_le_mul_of_nonneg_right hcard_j (by positivity)
          _ ≤ C_II * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
              dsimp only [C_II]
              have hnn : 0 ≤ Real.sqrt C_II_sq * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by positivity
              linarith [show (2 * Real.log P) * (6 * Real.sqrt C_II_sq * W₀ * P * (Real.log P) ^ 2 * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ))) =
                12 * Real.sqrt C_II_sq * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 by ring]
    -- Combine Steps 1–6!
    have hS3_rew : ∑ k ∈ Finset.Icc (U + 1) (B₀ / U), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ r ∈ Finset.Icc (max (U + 1) ((A₀ - 1) / k + 1)) (B₀ / k),
            (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) =
        ∑ k ∈ Finset.Icc (U + 1) (B₀ / U), (ArithmeticFunction.vonMangoldt k : ℂ) *
          ∑ r ∈ Finset.Icc (max ((A₀ - 1) / k + 1) (U + 1)) (B₀ / k),
            (-∑ d ∈ r.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℂ)) * g (k * r) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [max_comm]
    have hvm_bd : ‖∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ ≤
        (C_I + C_II) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
      rw [hvaugh, hS1_zero, zero_add, hS2b_rew, hS3_rew]
      have htri := le_trans (norm_add_le _ _) (add_le_add (norm_sub_le _ _) le_rfl)
      have hlog1 : 1 ≤ Real.log P := by linarith
      have hlog_sq_cube : (Real.log P) ^ 2 ≤ (Real.log P) ^ 3 := by
        calc (Real.log P) ^ 2 = (Real.log P) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (Real.log P) ^ 2 * Real.log P := mul_le_mul_of_nonneg_left hlog1 (by positivity)
          _ = (Real.log P) ^ 3 := by ring
      have hS2a' : ‖∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), (Real.log k : ℂ) * g (d * k)‖ ≤
          (64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
        refine le_trans hS2a_bd ?_
        exact mul_le_mul_of_nonneg_left hlog_sq_cube (by positivity)
      have hS2b' : ‖∑ d ∈ Finset.Icc 1 (U * U),
            (∑ u ∈ d.divisors.filter (fun u => u ≤ U ∧ d / u ≤ U),
              (ArithmeticFunction.moebius u : ℂ) * (ArithmeticFunction.vonMangoldt (d / u) : ℂ)) *
            ∑ r ∈ Finset.Icc ((A₀ - 1) / d + 1) (B₀ / d), g (d * r)‖ ≤
          (64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
        refine le_trans hS2b_bd ?_
        exact mul_le_mul_of_nonneg_left hlog_sq_cube (by positivity)
      calc ‖_‖ ≤ ‖_‖ + ‖_‖ + ‖_‖ := htri
        _ ≤ (64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 +
              (64 * max C_exp 3 * (q_den : ℝ) * (2 : ℝ) ^ R) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 +
              C_II * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 :=
            add_le_add (add_le_add hS2a' hS2b') hS3_bd
        _ = (C_I + C_II) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
            dsimp only [C_I]; ring
    have hdiff_le : 64 * W₀ * P * P ^ (-η'_δ) ≤
        64 * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
      have h1 : 1 ≤ (Real.log P) ^ 3 := one_le_pow₀ (by linarith)
      have h2 : P ^ (-η'_δ) ≤ (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 :=
        le_mul_of_le_of_one_le (le_add_of_nonneg_left (by positivity)) h1
      calc 64 * W₀ * P * P ^ (-η'_δ)
          ≤ 64 * W₀ * P * ((T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 64 * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by ring
    have htot : ‖∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p)‖ ≤
        ‖∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ +
          ‖∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p) -
            ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ := by
      simpa using norm_add_le
        (∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m)
        (∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p) -
          ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m)
    have hC_ge : C_I + C_II + 64 ≤ C_δ := le_max_left _ _
    have hnn_rhs : 0 ≤ W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by positivity
    calc ‖∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p)‖
        ≤ ‖∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ +
            ‖∑ p ∈ (Finset.Icc A₀ B₀).filter Nat.Prime, (w p * Real.log p : ℂ) * ePhase (F p) -
              ∑ m ∈ Finset.Icc A₀ B₀, (ArithmeticFunction.vonMangoldt m : ℂ) * g m‖ := htot
      _ ≤ (C_I + C_II + 64) * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
          linarith [hvm_bd, h_diff_vm, hdiff_le]
      _ ≤ C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 := by
          have h1 : (C_I + C_II + 64) * (W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3) ≤
              C_δ * (W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3) :=
            mul_le_mul_of_nonneg_right hC_ge hnn_rhs
          linarith


theorem lemma_2_4_i_mod (q_den : ℕ) (hq_den : 1 ≤ q_den) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    let AR : ℕ := 6 * R + 30
    ∃ (η'_δ C_δ C'_δ : ℝ), 0 < η'_δ ∧ 0 < C_δ ∧ 0 < C'_δ ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ (n : ℕ) (P : ℝ) (a b : ℝ) (A : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
        N₀ ≤ n → (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
        P ≤ a → a ≤ b → b ≤ 2 * P →
        A ⊆ Finset.Icc 1 R → A.Nonempty →
        (∀ r ∈ A, (n : ℝ) / P ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) →
        (hnonzero : ∃ r ∈ A, h r ≠ 0) →
        (∀ r ∈ A, |h r| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1) →
        0 ≤ W₀ → (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        ContDiffOn ℝ 1 w (Set.Icc P (2 * P)) →
        (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
        let r₀ : ℕ := (A.filter (fun r => h r ≠ 0)).min' (let ⟨r, hr, hhr⟩ := hnonzero; ⟨r, Finset.mem_filter.mpr ⟨hr, hhr⟩⟩)
        let T₀ : ℝ := (|(h r₀ : ℝ)| * n) / P ^ r₀
        T₀ ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR →
        ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / ((q_den : ℝ) * (p : ℝ) ^ r))‖ ≤
          C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 ∧
        C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 ≤
          C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by
  intro R AR
  obtain ⟨η'_δ, C_δ, hη'_pos, hC_pos, N₀_core, hN₀_core, hcore⟩ := lemma_2_4_core_mod q_den hq_den δ hδ0 hδ1
  let C'_δ : ℝ := 2 * C_δ * (2 : ℝ) ^ R
  have hC'_pos : 0 < C'_δ := by positivity
  have h_ev : ∀ᶠ n : ℕ in atTop,
      N₀_core ≤ n ∧
      (2 : ℝ) ^ R ≤ (Real.log n) ^ AR ∧
      (Real.log n) ^ (R + 5) ≤ ((n : ℝ) ^ δ) ^ η'_δ := by
    have h1 : ∀ᶠ n : ℕ in atTop, N₀_core ≤ n := eventually_ge_atTop N₀_core
    have h2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ R ≤ (Real.log n) ^ AR := by
      have hAR_pos : 0 < AR := by omega
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ AR) atTop atTop :=
        (tendsto_pow_atTop hAR_pos.ne').comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact hlim.eventually_ge_atTop _
    have h3 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ (R + 5) ≤ ((n : ℝ) ^ δ) ^ η'_δ := by
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ (R + 5) / ((n : ℝ) ^ δ) ^ η'_δ) atTop (𝓝 0) := by
        have hpos : 0 < (δ * η'_δ) / (R + 5 : ℝ) := by positivity
        have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ ((δ * η'_δ) / (R + 5 : ℝ))) atTop (𝓝 0) := by
          have h0 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            have h0' := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Real.tendsto_log_atTop
            refine h0'.congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
            simp [Function.comp_def, Real.exp_neg, Real.exp_log hu, div_eq_mul_inv]
          have hcomp := (h0.comp (tendsto_rpow_atTop hpos)).const_mul ((R + 5 : ℝ) / (δ * η'_δ))
          simp only [mul_zero] at hcomp
          refine hcomp.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          dsimp only [Function.comp_def]
          rw [Real.log_rpow hx]
          field_simp [hpos.ne']
        have hpow := (hsub.comp tendsto_natCast_atTop_atTop).pow (R + 5)
        simp only [zero_pow (by omega : R + 5 ≠ 0)] at hpow
        refine hpow.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        dsimp only [Function.comp_def]
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((δ * η'_δ) / (R + 5 : ℝ))),
          ← Real.rpow_mul hn_pos.le, ← Real.rpow_mul hn_pos.le]
        have hexp : (δ * η'_δ) / (R + 5 : ℝ) * ((R + 5 : ℕ) : ℝ) = δ * η'_δ := by
          push_cast; field_simp [show (R + 5 : ℝ) ≠ 0 by positivity]
        rw [hexp]
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        eventually_ge_atTop 1] with n hn hn1
      have hpos : 0 < ((n : ℝ) ^ δ) ^ η'_δ :=
        Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn1) δ) η'_δ
      rwa [div_le_one hpos] at hn
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3 using ⟨hn1, hn2, hn3⟩
  obtain ⟨N₀, hN₀_all⟩ := eventually_atTop.mp h_ev
  refine ⟨η'_δ, C_δ, C'_δ, hη'_pos, hC_pos, hC'_pos, max N₀ 16, le_max_right _ _, ?_⟩
  intro n P a b A h w W₀ hn hP_lo hP_hi hPa hab hb2P hA hAne h_ar hnonzero hh_bd hW₀ hw_bd hw_diff hw_tv r₀ T₀ hT₀
  obtain ⟨hn_core, h2R_log, hlog_P⟩ := hN₀_all n (le_trans (le_max_left _ _) hn)
  have hn16 : 16 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hP_pos : 0 < P := lt_of_lt_of_le (Real.rpow_pos_of_pos hn_pos δ) hP_lo
  have hT₀_ge1 : 1 ≤ T₀ := by
    calc (1 : ℝ) = (2 : ℝ) ^ (-(R : ℤ)) * (2 : ℝ) ^ R := by
          rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
      _ ≤ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR :=
          mul_le_mul_of_nonneg_left h2R_log (by positivity)
      _ ≤ T₀ := hT₀
  have hbd1 := hcore n P a b A h w W₀ hn_core hP_lo hP_hi hPa hab hb2P hA hAne
    hnonzero hh_bd hW₀ hw_bd hw_diff hw_tv hT₀_ge1
  refine ⟨hbd1, ?_⟩
  have hlog1 : 1 ≤ Real.log n := by
    have : Real.exp 1 ≤ (n : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ (16 : ℝ)) (by exact_mod_cast hn16)
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hP_le_n : P ≤ n := by
    have : (1 : ℝ) ≤ (Real.log n) ^ 12 := one_le_pow₀ hlog1
    exact le_trans hP_hi (div_le_self hn_pos.le this)
  have hlogP_le : Real.log P ≤ Real.log n := Real.log_le_log hP_pos hP_le_n
  have hlogP_nn : 0 ≤ Real.log P := by
    have hP1 : 1 ≤ P := le_trans (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hδ0.le) hP_lo
    exact Real.log_nonneg hP1
  have hlogP_cube : (Real.log P) ^ 3 ≤ (Real.log n) ^ 3 := pow_le_pow_left₀ hlogP_nn hlogP_le 3
  -- Bound `T₀ ^ (-1 / 6) * (log P)^3`
  have hT₀_pow : T₀ ^ (-1 / 6 : ℝ) * (Real.log P) ^ 3 ≤ (2 : ℝ) ^ R * (Real.log n) ^ (-(R + 2 : ℤ)) := by
    have hT0_rpow : T₀ ^ (-1 / 6 : ℝ) ≤ ((2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) ^ (-1 / 6 : ℝ) := by
      rw [show (-1 / 6 : ℝ) = -(1 / 6 : ℝ) by ring, Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_le_rpow (by positivity) hT₀ (by positivity))
    have h_rhs_eq : ((2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) ^ (-1 / 6 : ℝ) =
        ((2 : ℝ) ^ (-(R : ℤ))) ^ (-1 / 6 : ℝ) * (Real.log n) ^ (-(R + 5 : ℤ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast (Real.log n), ← Real.rpow_mul hlog_pos.le]
      congr 1
      have hexp : (AR : ℝ) * (-1 / 6 : ℝ) = ((-(R + 5 : ℤ) : ℤ) : ℝ) := by
        dsimp only [AR]; push_cast; ring
      rw [hexp, Real.rpow_intCast]
    have h2_le : ((2 : ℝ) ^ (-(R : ℤ))) ^ (-1 / 6 : ℝ) ≤ (2 : ℝ) ^ R := by
      rw [← Real.rpow_intCast (2 : ℝ) (-(R : ℤ)), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast (2 : ℝ) R]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    calc T₀ ^ (-1 / 6 : ℝ) * (Real.log P) ^ 3
        ≤ ((2 : ℝ) ^ R * (Real.log n) ^ (-(R + 5 : ℤ))) * (Real.log n) ^ 3 := by
          refine mul_le_mul (le_trans hT0_rpow ?_) hlogP_cube (by positivity) (by positivity)
          rw [h_rhs_eq]
          exact mul_le_mul_of_nonneg_right h2_le (by positivity)
      _ = (2 : ℝ) ^ R * ((Real.log n) ^ (-(R + 5 : ℤ)) * (Real.log n) ^ (3 : ℤ)) := by
          rw [show (Real.log n) ^ (3 : ℕ) = (Real.log n) ^ (3 : ℤ) by norm_cast]
      _ = (2 : ℝ) ^ R * (Real.log n) ^ (-(R + 2 : ℤ)) := by
          rw [← zpow_add₀ hlog_pos.ne', show -(R + 5 : ℤ) + 3 = -(R + 2 : ℤ) by omega]
  -- Bound `P ^ (-η'_δ) * (log P)^3`
  have hP_pow : P ^ (-η'_δ) * (Real.log P) ^ 3 ≤ (2 : ℝ) ^ R * (Real.log n) ^ (-(R + 2 : ℤ)) := by
    have hP_rpow : P ^ (-η'_δ) ≤ (Real.log n) ^ (-(R + 5 : ℤ)) := by
      rw [Real.rpow_neg hP_pos.le, show -(R + 5 : ℤ) = -(((R + 5 : ℕ) : ℤ)) by push_cast; rfl,
        zpow_neg, zpow_natCast]
      refine inv_anti₀ (by positivity) (le_trans hlog_P ?_)
      exact Real.rpow_le_rpow (by positivity) hP_lo hη'_pos.le
    calc P ^ (-η'_δ) * (Real.log P) ^ 3
        ≤ (Real.log n) ^ (-(R + 5 : ℤ)) * (Real.log n) ^ 3 :=
          mul_le_mul hP_rpow hlogP_cube (by positivity) (by positivity)
      _ = 1 * ((Real.log n) ^ (-(R + 5 : ℤ)) * (Real.log n) ^ (3 : ℤ)) := by
          rw [show (Real.log n) ^ (3 : ℕ) = (Real.log n) ^ (3 : ℤ) by norm_cast, one_mul]
      _ = 1 * (Real.log n) ^ (-(R + 2 : ℤ)) := by
          rw [← zpow_add₀ hlog_pos.ne', show -(R + 5 : ℤ) + 3 = -(R + 2 : ℤ) by omega]
      _ ≤ (2 : ℝ) ^ R * (Real.log n) ^ (-(R + 2 : ℤ)) :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)
  calc C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3
      = C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) * (Real.log P) ^ 3 + P ^ (-η'_δ) * (Real.log P) ^ 3) := by ring
    _ ≤ C_δ * W₀ * P * ((2 : ℝ) ^ R * (Real.log n) ^ (-(R + 2 : ℤ)) + (2 : ℝ) ^ R * (Real.log n) ^ (-(R + 2 : ℤ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hT₀_pow hP_pow) (by positivity)
    _ = C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by dsimp only [C'_δ]; ring


end BrocardFormalization

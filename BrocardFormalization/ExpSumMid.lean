/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.ExpSumCore

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

lemma y_pow_diff_bounds (r : ℕ) (hr : 1 ≤ r) (Y₁ y₁ y₂ : ℝ)
    (hY₁ : 0 < Y₁) (hy₁_lo : Y₁ ≤ y₁) (hy₁_hi : y₁ ≤ 2 * Y₁)
    (hy₂_lo : Y₁ ≤ y₂) (hy₂_hi : y₂ ≤ 2 * Y₁) :
    (r : ℝ) * |y₁ - y₂| * (2 : ℝ) ^ (-(2 * r : ℤ)) * Y₁ ^ (-(r + 1 : ℤ)) ≤
      |y₁ ^ (-(r : ℤ)) - y₂ ^ (-(r : ℤ))| ∧
    |y₁ ^ (-(r : ℤ)) - y₂ ^ (-(r : ℤ))| ≤
      (r : ℝ) * |y₁ - y₂| * (2 : ℝ) ^ (r - 1) * Y₁ ^ (-(r + 1 : ℤ)) := by
  have hy₁_pos : 0 < y₁ := lt_of_lt_of_le hY₁ hy₁_lo
  have hy₂_pos : 0 < y₂ := lt_of_lt_of_le hY₁ hy₂_lo
  have hdiff : y₁ ^ (-(r : ℤ)) - y₂ ^ (-(r : ℤ)) = (y₂ ^ r - y₁ ^ r) / (y₁ ^ r * y₂ ^ r) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp [hy₁_pos.ne', hy₂_pos.ne']
  have hgeom : y₂ ^ r - y₁ ^ r = (y₂ - y₁) * ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i) := by
    have h := geom_sum₂_mul y₂ y₁ r
    linarith [h]
  rw [hdiff, hgeom, abs_div, abs_mul, abs_sub_comm y₂ y₁,
    abs_of_pos (a := y₁ ^ r * y₂ ^ r) (mul_pos (pow_pos hy₁_pos r) (pow_pos hy₂_pos r))]
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hy₂_pos.le i) (pow_nonneg hy₁_pos.le _)
  rw [abs_of_nonneg (a := ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i)) hsum_nn]
  have hsum_lo : (r : ℝ) * Y₁ ^ (r - 1) ≤ ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i) := by
    calc (r : ℝ) * Y₁ ^ (r - 1) = ∑ _i ∈ Finset.range r, Y₁ ^ (r - 1) := by simp
      _ ≤ ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi_lt : i < r := Finset.mem_range.mp hi
          calc Y₁ ^ (r - 1) = Y₁ ^ i * Y₁ ^ (r - 1 - i) := by
                rw [← pow_add, Nat.add_sub_cancel' (by omega : i ≤ r - 1)]
            _ ≤ y₂ ^ i * y₁ ^ (r - 1 - i) :=
                mul_le_mul (pow_le_pow_left₀ hY₁.le hy₂_lo i)
                  (pow_le_pow_left₀ hY₁.le hy₁_lo _) (by positivity) (by positivity)
  have hsum_hi : ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i) ≤ (r : ℝ) * (2 * Y₁) ^ (r - 1) := by
    calc ∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i)
        ≤ ∑ _i ∈ Finset.range r, (2 * Y₁) ^ (r - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi_lt : i < r := Finset.mem_range.mp hi
          calc y₂ ^ i * y₁ ^ (r - 1 - i) ≤ (2 * Y₁) ^ i * (2 * Y₁) ^ (r - 1 - i) :=
                mul_le_mul (pow_le_pow_left₀ hy₂_pos.le hy₂_hi i)
                  (pow_le_pow_left₀ hy₁_pos.le hy₁_hi _) (by positivity) (by positivity)
            _ = (2 * Y₁) ^ (r - 1) := by rw [← pow_add, Nat.add_sub_cancel' (by omega : i ≤ r - 1)]
      _ = (r : ℝ) * (2 * Y₁) ^ (r - 1) := by simp
  have hden_lo : Y₁ ^ (2 * r) ≤ y₁ ^ r * y₂ ^ r := by
    rw [two_mul, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hY₁.le hy₁_lo r) (pow_le_pow_left₀ hY₁.le hy₂_lo r) (by positivity) (by positivity)
  have hden_hi : y₁ ^ r * y₂ ^ r ≤ (2 * Y₁) ^ (2 * r) := by
    rw [show 2 * r = r + r by omega, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hy₁_pos.le hy₁_hi r) (pow_le_pow_left₀ hy₂_pos.le hy₂_hi r) (by positivity) (by positivity)
  constructor
  · calc (r : ℝ) * |y₁ - y₂| * (2 : ℝ) ^ (-(2 * r : ℤ)) * Y₁ ^ (-(r + 1 : ℤ))
        = |y₁ - y₂| * ((r : ℝ) * Y₁ ^ (r - 1)) / (2 * Y₁) ^ (2 * r) := by
          rw [show -(2 * r : ℤ) = -(((2 * r : ℕ) : ℤ)) by push_cast; rfl,
            show -(r + 1 : ℤ) = -(((r + 1 : ℕ) : ℤ)) by push_cast; rfl,
            zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow,
            show 2 * r = (r - 1) + (r + 1) by omega, pow_add, pow_add]
          field_simp [hY₁.ne']; ring
      _ ≤ |y₁ - y₂| * (∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i)) / (y₁ ^ r * y₂ ^ r) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsum_lo (abs_nonneg _)) (by positivity) hden_hi
  · calc |y₁ - y₂| * (∑ i ∈ Finset.range r, y₂ ^ i * y₁ ^ (r - 1 - i)) / (y₁ ^ r * y₂ ^ r)
        ≤ |y₁ - y₂| * ((r : ℝ) * (2 * Y₁) ^ (r - 1)) / Y₁ ^ (2 * r) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsum_hi (abs_nonneg _)) (by positivity) hden_lo
      _ = (r : ℝ) * |y₁ - y₂| * (2 : ℝ) ^ (r - 1) * Y₁ ^ (-(r + 1 : ℤ)) := by
          rw [show -(r + 1 : ℤ) = -(((r + 1 : ℕ) : ℤ)) by push_cast; rfl,
            zpow_neg, zpow_natCast, mul_pow, show 2 * r = (r - 1) + (r + 1) by omega, pow_add]
          field_simp [hY₁.ne']

lemma type_II_inner_sum_bound
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
      |(h r : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))| *
          (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|(h r₀ : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
            (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ))))
    (hT_ub : |(h r₀ : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
        (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) ≤ (X₁ : ℝ) ^ (K_max - 1))
    (hT₀_ge1 : 1 ≤ |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    let T_y := (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ * (|(y₁ : ℝ) - y₂| / Y₁)
    ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * y₁ ∧ x * y₁ ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * y₂ ∧ x * y₂ ≤ ⌊b⌋₊),
        (w (x * y₁) * w (x * y₂) : ℂ) *
          ePhase ((∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₁ : ℕ) : ℝ) ^ r)) -
            (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₂ : ℕ) : ℝ) ^ r)))‖ ≤
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
            ePhase ((∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₁ : ℕ) : ℝ) ^ r)) -
              (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₂ : ℕ) : ℝ) ^ r)))‖ ≤ E := by
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
      let cy : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))
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
        exact mul_ne_zero (div_ne_zero (mul_ne_zero hh0R hn_pos.ne') (by norm_num)) hpow_ne
      have hphase_eq : ∀ x ∈ Finset.Icc ⌈a₁₂⌉₊ u,
          (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₁ : ℕ) : ℝ) ^ r)) -
            (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₂ : ℕ) : ℝ) ^ r)) =
          ∑ r ∈ A, cy r * (x : ℝ) ^ (-(r : ℤ)) := by
        intro x _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        dsimp only [cy]
        rw [Nat.cast_mul, Nat.cast_mul, mul_pow, mul_pow, zpow_neg, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast]
        ring
      have hsum_eq : ∑ x ∈ Finset.Icc ⌈a₁₂⌉₊ u,
            ePhase ((∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₁ : ℕ) : ℝ) ^ r)) -
              (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₂ : ℕ) : ℝ) ^ r))) =
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
          linarith [h2]
        have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
        have h2_le : (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (2 : ℝ) ^ (3 * R) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) by norm_num, ← zpow_natCast (2 : ℝ) (3 * R),
            ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by have := (hA r₀ hr₀).2; omega)
        dsimp only [T_y, T₀, cy]
        rw [abs_mul, abs_div, abs_mul, abs_of_pos hn_pos, abs_of_pos (a := (2 : ℝ)) (by norm_num)]
        calc (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (|(h r₀ : ℝ)| * n / P ^ r₀) * (|(y₁ : ℝ) - y₂| / Y₁)
            = |(h r₀ : ℝ)| * n * (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * P ^ (-(r₀ : ℤ)) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by
              rw [zpow_neg P (r₀ : ℤ), zpow_natCast P r₀, zpow_neg_one]; ring
          _ ≤ |(h r₀ : ℝ)| * n * ((2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (2 : ℝ) ^ (3 * R)) *
                ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by
              have hmul1 : (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * P ^ (-(r₀ : ℤ)) ≤
                  (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (2 : ℝ) ^ (3 * R) *
                    ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hXY_pow (by positivity)
              have hnn : 0 ≤ |(h r₀ : ℝ)| * n := by positivity
              calc |(h r₀ : ℝ)| * n * (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * P ^ (-(r₀ : ℤ)) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ)
                  = (|(h r₀ : ℝ)| * n) * ((2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * P ^ (-(r₀ : ℤ))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by ring
                _ ≤ (|(h r₀ : ℝ)| * n) * ((2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * (2 : ℝ) ^ (3 * R) *
                      ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ)))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul1 hnn) (abs_nonneg _)) (by positivity)
                _ = _ := by ring
          _ ≤ |(h r₀ : ℝ)| * n * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(2 * r₀ : ℤ))) *
                ((2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) * (Y₁ : ℝ) ^ (-(r₀ : ℤ))) * |(y₁ : ℝ) - y₂| * (Y₁ : ℝ) ^ (-1 : ℤ) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h2_le (by positivity)) (by positivity)) (abs_nonneg _)) (by positivity)
          _ = (|(h r₀ : ℝ)| * n / 2) * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) *
                (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := by
              rw [show -(r₀ + 1 : ℤ) = -(r₀ : ℤ) + (-1 : ℤ) by omega, zpow_add₀ hY₁_pos.ne']
              ring
          _ ≤ (|(h r₀ : ℝ)| * n / 2) * ((r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) *
                (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
              calc |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))
                  = 1 * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) := (one_mul _).symm
                _ ≤ (r₀ : ℝ) * (|(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) :=
                    mul_le_mul_of_nonneg_right hr0_1 (by positivity)
                _ = _ := by ring
          _ ≤ (|(h r₀ : ℝ)| * n / 2 * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) *
                (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
              have hle1 : |(h r₀ : ℝ)| * n / 2 * ((r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) ≤
                  |(h r₀ : ℝ)| * n / 2 * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| :=
                mul_le_mul_of_nonneg_left hdiff_lo (by positivity)
              calc (|(h r₀ : ℝ)| * n / 2) * ((r₀ : ℝ) * |(y₁ : ℝ) - y₂| * (2 : ℝ) ^ (-(2 * r₀ : ℤ)) * Y₁ ^ (-(r₀ + 1 : ℤ))) *
                    (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ))
                  ≤ (|(h r₀ : ℝ)| * n / 2 * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) *
                      (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)) := mul_le_mul_of_nonneg_right hle1 (by positivity)
                _ ≤ (|(h r₀ : ℝ)| * n / 2 * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) *
                      (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
                    rw [mul_assoc (|(h r₀ : ℝ)| * n / 2 * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))|) (r₀ : ℝ)]
                    have h_lhs_nn : 0 ≤ |(h r₀ : ℝ)| * n / 2 * |(y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ))| := by positivity
                    refine mul_le_mul_of_nonneg_left ?_ h_lhs_nn
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
              ePhase ((∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₁ : ℕ) : ℝ) ^ r)) -
                (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y₂ : ℕ) : ℝ) ^ r)))‖
        ≤ (2 * W₀ ^ 2 + 2 * W₀ ^ 2) * E := by simpa [w₁₂] using hps
      _ = 4 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) := by
          dsimp only [E]; ring
      _ ≤ 8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) := by
          have hnn : 0 ≤ W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + (2 * (X₁ : ℝ)) ^ (1 - η_exp)) :=
            mul_nonneg (mul_nonneg (sq_nonneg W₀) hC_exp.le) hTy_rhs_nn
          linarith

lemma ePhase_mul_star (α β : ℝ) : ePhase α * star (ePhase β) = ePhase (α - β) := by
  unfold ePhase
  rw [Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

lemma type_II_block_bound
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
        |(h r : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r : ℤ)) - (y₂ : ℝ) ^ (-(r : ℤ)))| *
            (Nat.descFactorial (r + k - 1) k : ℝ) * (X₁ : ℝ) ^ (-(r : ℤ)) ≤
          (1 / (2 * max (A.card : ℝ) 1)) *
            (|(h r₀ : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
              (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * (X₁ : ℝ)) ^ (-(r₀ : ℤ)))) ∧
      |(h r₀ : ℝ) * (n : ℝ) / 2 * ((y₁ : ℝ) ^ (-(r₀ : ℤ)) - (y₂ : ℝ) ^ (-(r₀ : ℤ)))| *
          (r₀ : ℝ) * (X₁ : ℝ) ^ (-(r₀ : ℤ)) ≤ (X₁ : ℝ) ^ (K_max - 1)) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    1 ≤ T₀ →
    ‖∑ x ∈ Finset.Icc X₁ X_top, a_coeff x *
        ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) *
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 ≤
      A_norm * B_norm * W₀ ^ 2 *
        (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
          128 * (2 : ℝ) ^ (5 * R + 1) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
          128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
  intro T₀ hT₀_ge1
  have hX₁_pos : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
  have hY₁_pos : (0 : ℝ) < Y₁ := by exact_mod_cast hY₁
  have hP_pos : 0 < P := by linarith
  have hCS : ‖∑ x ∈ Finset.Icc X₁ X_top, a_coeff x *
        ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) *
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 ≤
      (∑ x ∈ Finset.Icc X₁ X_top, ‖a_coeff x‖ ^ 2) *
        ∑ x ∈ Finset.Icc X₁ X_top,
          ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
            b_coeff y * (w (x * y) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 := by
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
  let F : ℕ → ℝ := fun m => ∑ r ∈ A, (h r : ℝ) * n / (2 * (m : ℝ) ^ r)
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
      have hns : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := fun z => by
        rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj]; simp
      rw [hns]
      congr 1
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y₁ _ => ?_
      by_cases h1 : ⌈a⌉₊ ≤ x * y₁ ∧ x * y₁ ≤ ⌊b⌋₊
      · rw [if_pos h1, Finset.sum_filter]
        refine Finset.sum_congr rfl fun y₂ _ => ?_
        by_cases h2 : ⌈a⌉₊ ≤ x * y₂ ∧ x * y₂ ≤ ⌊b⌋₊
        · rw [if_pos h2, if_pos ⟨h1.1, h1.2, h2.1, h2.2⟩]
          rw [star_mul, star_mul, Complex.star_def, Complex.conj_ofReal,
            ← Complex.star_def, ← ePhase_mul_star]
          ring
        · rw [if_neg h2, if_neg (fun h => h2 ⟨h.2.2.1, h.2.2.2⟩)]
      · rw [if_neg h1]
        symm
        exact Finset.sum_eq_zero fun y₂ _ => if_neg (fun h => h1 ⟨h.1, h.2.1⟩)
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
      (∑ p ∈ Near,
        ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
          ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
            (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖) +
      (∑ p ∈ Far,
        ‖b_coeff p.1‖ * ‖b_coeff p.2‖ *
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
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs,
          norm_ePhase (F (x * p.1) - F (x * p.2)),
          mul_one, sq]
        exact mul_le_mul (hw_bd _ h1P) (hw_bd _ h2P) (abs_nonneg _) hW₀
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_le : (((Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊)).card : ℝ) ≤ 2 * (X₁ : ℝ) := by
        have h1 := Finset.card_filter_le (Finset.Icc X₁ X_top) (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊)
        have h2 : (Finset.Icc X₁ X_top).card ≤ X_top := by rw [Nat.card_Icc]; omega
        exact_mod_cast le_trans h1 (le_trans h2 hX_top)
      exact mul_le_mul_of_nonneg_right hcard_le (sq_nonneg W₀)
    have hnear_sum : ∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ ≤ (2 * D + 1) * B_norm := by
      have h1 : ∑ p ∈ Near, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ ≤
          ∑ p ∈ Near, (‖b_coeff p.1‖ ^ 2 + ‖b_coeff p.2‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun p _ => by nlinarith [sq_nonneg (‖b_coeff p.1‖ - ‖b_coeff p.2‖)]
      have h2 : ∑ p ∈ Near, ‖b_coeff p.1‖ ^ 2 ≤ (2 * D + 1) * B_norm := by
        dsimp only [Near]
        rw [Finset.sum_filter, Finset.sum_product]
        have hrow : ∀ y₁ ∈ Finset.Icc Y₁ Y₂,
            ∑ y₂ ∈ Finset.Icc Y₁ Y₂, (if |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D then ‖b_coeff (y₁, y₂).1‖ ^ 2 else 0) ≤
            (2 * D + 1) * ‖b_coeff y₁‖ ^ 2 := by
          intro y₁ _
          dsimp only
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hsub_y : (Finset.Icc Y₁ Y₂).filter (fun y₂ : ℕ => |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D) ⊆
              Finset.Icc (y₁ - ⌊D⌋₊) (y₁ + ⌊D⌋₊) := by
            intro y₂ hy₂
            have hyD : |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D := (Finset.mem_filter.mp hy₂).2
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
          have hcard_le : ((Finset.Icc Y₁ Y₂).filter (fun y₂ : ℕ => |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D)).card ≤ 2 * ⌊D⌋₊ + 1 := by
            refine le_trans (Finset.card_le_card hsub_y) ?_
            rw [Nat.card_Icc]; omega
          calc (((Finset.Icc Y₁ Y₂).filter (fun y₂ : ℕ => |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D)).card : ℝ)
              ≤ (2 * ⌊D⌋₊ + 1 : ℕ) := by exact_mod_cast hcard_le
            _ ≤ 2 * D + 1 := by push_cast; linarith [Nat.floor_le hD_nn]
        calc ∑ y₁ ∈ Finset.Icc Y₁ Y₂, ∑ y₂ ∈ Finset.Icc Y₁ Y₂, (if |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D then ‖b_coeff (y₁, y₂).1‖ ^ 2 else 0)
            ≤ ∑ y₁ ∈ Finset.Icc Y₁ Y₂, (2 * D + 1) * ‖b_coeff y₁‖ ^ 2 :=
              Finset.sum_le_sum fun y₁ hy₁ => hrow y₁ hy₁
          _ = (2 * D + 1) * ∑ y₁ ∈ Finset.Icc Y₁ Y₂, ‖b_coeff y₁‖ ^ 2 := by rw [Finset.mul_sum]
          _ ≤ (2 * D + 1) * B_norm := mul_le_mul_of_nonneg_left hB_norm (by positivity)
      have h3 : ∑ p ∈ Near, ‖b_coeff p.2‖ ^ 2 ≤ (2 * D + 1) * B_norm := by
        dsimp only [Near]
        rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
        have hrow : ∀ y₂ ∈ Finset.Icc Y₁ Y₂,
            ∑ y₁ ∈ Finset.Icc Y₁ Y₂, (if |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D then ‖b_coeff (y₁, y₂).2‖ ^ 2 else 0) ≤
            (2 * D + 1) * ‖b_coeff y₂‖ ^ 2 := by
          intro y₂ _
          dsimp only
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hsub_y : (Finset.Icc Y₁ Y₂).filter (fun y₁ : ℕ => |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D) ⊆
              Finset.Icc (y₂ - ⌊D⌋₊) (y₂ + ⌊D⌋₊) := by
            intro y₁ hy₁
            have hyD : |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D := (Finset.mem_filter.mp hy₁).2
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
          have hcard_le : ((Finset.Icc Y₁ Y₂).filter (fun y₁ : ℕ => |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D)).card ≤ 2 * ⌊D⌋₊ + 1 := by
            refine le_trans (Finset.card_le_card hsub_y) ?_
            rw [Nat.card_Icc]; omega
          calc (((Finset.Icc Y₁ Y₂).filter (fun y₁ : ℕ => |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D)).card : ℝ)
              ≤ (2 * ⌊D⌋₊ + 1 : ℕ) := by exact_mod_cast hcard_le
            _ ≤ 2 * D + 1 := by push_cast; linarith [Nat.floor_le hD_nn]
        calc ∑ y₂ ∈ Finset.Icc Y₁ Y₂, ∑ y₁ ∈ Finset.Icc Y₁ Y₂, (if |(y₁ : ℝ) - (y₂ : ℝ)| ≤ D then ‖b_coeff (y₁, y₂).2‖ ^ 2 else 0)
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
      B_norm * W₀ ^ 2 * (128 * (2 : ℝ) ^ (5 * R + 1) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
        128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
    have hinner : ∀ p ∈ Far,
        ‖∑ x ∈ (Finset.Icc X₁ X_top).filter (fun x => ⌈a⌉₊ ≤ x * p.1 ∧ x * p.1 ≤ ⌊b⌋₊ ∧ ⌈a⌉₊ ≤ x * p.2 ∧ x * p.2 ≤ ⌊b⌋₊),
          (w (x * p.1) * w (x * p.2) : ℂ) * ePhase (F (x * p.1) - F (x * p.2))‖ ≤
        8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
          ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
      intro ⟨y₁, y₂⟩ hp
      simp only [Far, Finset.mem_filter, Finset.mem_product, not_le] at hp
      have hy_ne : y₁ ≠ y₂ := by
        intro heq; subst heq; rw [sub_self, abs_zero] at hp; exact not_le_of_gt hp.2 hD_nn
      have hy₁_mem := (Finset.mem_Icc.mp hp.1.1)
      have hy₂_mem := (Finset.mem_Icc.mp hp.1.2)
      have hdom_pair := hdom_all y₁ hp.1.1 y₂ hp.1.2 hy_ne
      have h_in := type_II_inner_sum_bound R K_max hK_max C_exp η_exp M₀ hC_exp hη_exp hη_le hM₀ hexp
        n P a b hP1 hPa hab hb2P A hA r₀ hr₀ h hh₀ w W₀ hW₀ hw_bd hw_diff hw_tv
        X₁ X_top Y₁ hX₁ hM₀_X₁ hX_top hY₁ hXY_hi y₁ y₂ hy₁_mem.1 (le_trans hy₁_mem.2 hY₂_2) hy₂_mem.1 (le_trans hy₂_mem.2 hY₂_2) hy_ne
        hdom_pair.1 hdom_pair.2 hT₀_ge1
      dsimp only at h_in
      set T_y := (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ * (|(y₁ : ℝ) - y₂| / Y₁)
      have hTy_gt : (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ ^ (2 / 3 : ℝ) ≤ T_y := by
        dsimp only [T_y]
        have hdiff_gt : T₀ ^ (-1 / 3 : ℝ) < |(y₁ : ℝ) - y₂| / Y₁ := by
          rw [lt_div_iff₀ hY₁_pos, mul_comm]; exact hp.2
        have hT_eq : T₀ * T₀ ^ (-1 / 3 : ℝ) = T₀ ^ (2 / 3 : ℝ) := by
          rw [show (2 / 3 : ℝ) = 1 + (-1 / 3 : ℝ) by norm_num,
            Real.rpow_add (by linarith only [hT₀_ge1]), Real.rpow_one]
        calc (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ ^ (2 / 3 : ℝ)
            = (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ * T₀ ^ (-1 / 3 : ℝ) := by rw [← hT_eq]; ring
          _ ≤ (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ * (|(y₁ : ℝ) - y₂| / Y₁) :=
              mul_le_mul_of_nonneg_left hdiff_gt.le (by positivity)
      have hdiv_le : (2 * (X₁ : ℝ)) / max T_y 1 ≤
          (2 * (X₁ : ℝ)) * ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ)) := by
        have h1 : (2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ ^ (2 / 3 : ℝ) ≤ max T_y 1 :=
          le_trans hTy_gt (le_max_left _ _)
        calc (2 * (X₁ : ℝ)) / max T_y 1
            ≤ (2 * (X₁ : ℝ)) / ((2 : ℝ) ^ (-(5 * R + 1 : ℤ)) * T₀ ^ (2 / 3 : ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) h1
          _ = (2 * (X₁ : ℝ)) * ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ)) := by
              rw [show -(5 * R + 1 : ℤ) = -(((5 * R + 1 : ℕ) : ℤ)) by push_cast; rfl,
                div_eq_mul_inv, mul_inv, zpow_neg, zpow_natCast, inv_inv,
                ← Real.rpow_neg (by linarith only [hT₀_ge1]), show -(2 / 3 : ℝ) = -2 / 3 by norm_num]
      have hpow_eq : (2 * (X₁ : ℝ)) ^ (1 - η_exp) = (2 * (X₁ : ℝ)) * (2 * (X₁ : ℝ)) ^ (-η_exp) := by
        rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
      refine le_trans h_in ?_
      rw [hpow_eq]
      calc 8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) / max T_y 1 + 2 * (X₁ : ℝ) * (2 * (X₁ : ℝ)) ^ (-η_exp))
          ≤ 8 * W₀ ^ 2 * C_exp * ((2 * (X₁ : ℝ)) * ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ)) +
              2 * (X₁ : ℝ) * (2 * (X₁ : ℝ)) ^ (-η_exp)) :=
            mul_le_mul_of_nonneg_left (add_le_add hdiv_le le_rfl) (by positivity)
        _ = 8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp)) := by ring
    have hfar_sum : ∑ p ∈ Far, ‖b_coeff p.1‖ * ‖b_coeff p.2‖ ≤ 2 * (Y₁ : ℝ) * B_norm := by
      have hsub : Far ⊆ Finset.Icc Y₁ Y₂ ×ˢ Finset.Icc Y₁ Y₂ := Finset.filter_subset _ _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
      rw [Finset.sum_product]
      dsimp only
      rw [← Finset.sum_mul_sum]
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
              ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hinner p hp) (by positivity)
      _ = (∑ p ∈ Far, ‖b_coeff p.1‖ * ‖b_coeff p.2‖) *
            (8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) := by rw [Finset.sum_mul]
      _ ≤ (2 * (Y₁ : ℝ) * B_norm) *
            (8 * W₀ ^ 2 * C_exp * (2 * (X₁ : ℝ)) *
              ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) :=
          mul_le_mul_of_nonneg_right hfar_sum (by positivity)
      _ = B_norm * W₀ ^ 2 * (8 * ((2 * (X₁ : ℝ)) * (2 * (Y₁ : ℝ))) * C_exp *
            ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) := by ring
      _ ≤ B_norm * W₀ ^ 2 * (8 * (16 * P) * C_exp *
            ((2 : ℝ) ^ (5 * R + 1) * T₀ ^ (-2 / 3 : ℝ) + (2 * (X₁ : ℝ)) ^ (-η_exp))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY_hi (by norm_num)) hC_exp.le)
            (by positivity)) (by positivity)
      _ = B_norm * W₀ ^ 2 * (128 * (2 : ℝ) ^ (5 * R + 1) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
            128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by ring
  have htot : ∑ x ∈ Finset.Icc X₁ X_top,
        ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
          b_coeff y * (w (x * y) : ℂ) *
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 ≤
      B_norm * W₀ ^ 2 *
        (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
          128 * (2 : ℝ) ^ (5 * R + 1) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
          128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by
    refine le_trans hre_le ?_
    rw [hsplit]
    linarith only [hNear_bd, hFar_bd]
  calc ‖∑ x ∈ Finset.Icc X₁ X_top,
        a_coeff x *
          ∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
            b_coeff y * (w (x * y) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2
      ≤ (∑ x ∈ Finset.Icc X₁ X_top, ‖a_coeff x‖ ^ 2) *
          ∑ x ∈ Finset.Icc X₁ X_top,
            ‖∑ y ∈ (Finset.Icc Y₁ Y₂).filter (fun y => ⌈a⌉₊ ≤ x * y ∧ x * y ≤ ⌊b⌋₊),
              b_coeff y * (w (x * y) : ℂ) *
                ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((x * y : ℕ) : ℝ) ^ r))‖ ^ 2 := hCS
    _ ≤ A_norm * (B_norm * W₀ ^ 2 *
          (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
            128 * (2 : ℝ) ^ (5 * R + 1) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
            128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp))) :=
        mul_le_mul hA_norm htot (Finset.sum_nonneg fun _ _ => sq_nonneg _) hA_nn
    _ = A_norm * B_norm * W₀ ^ 2 *
          (32 * P * T₀ ^ (-1 / 3 : ℝ) + 8 * P ^ (1 / 2 : ℝ) +
            128 * (2 : ℝ) ^ (5 * R + 1) * C_exp * P * T₀ ^ (-2 / 3 : ℝ) +
            128 * C_exp * P * (2 * (X₁ : ℝ)) ^ (-η_exp)) := by ring

lemma type_I_no_log_single_d_bound
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
      |(h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|(h r₀ : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r₀)| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))))
    (hT_ub : |(h r₀ : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (K_max - 1)) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
        (w (d * k) : ℂ) *
          ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
      4 * W₀ * max C_exp 3 *
        ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
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
      ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := mul_nonneg (by positivity)
      (add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
    have hsum_bd : ∀ u : ℕ, ⌈a'⌉₊ ≤ u → u ≤ ⌊b'⌋₊ →
        ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤ E := by
      intro u hau hub
      have hu_ge : P / d ≤ (u : ℝ) := le_trans hPa' (le_trans (Nat.le_ceil a') (by exact_mod_cast hau))
      have hu_le : (u : ℝ) ≤ 2 * (P / d) := le_trans (by exact_mod_cast hub)
        (le_trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)) hb'2P)
      have hu_le' : (u : ℝ) ≤ 2 * P / d := by linarith [hu_le, show 2 * (P / d) = 2 * P / d by ring]
      by_cases hn0 : n = 0
      · subst hn0
        have htriv : ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
            ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          simp [norm_ePhase]
        have hcard : ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) ≤ 2 * P / d := by
          rw [Nat.card_Icc]
          have h1 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (lt_of_lt_of_le hPd_pos hPa')
          have h2 : u + 1 - ⌈a'⌉₊ ≤ u := by omega
          exact le_trans (by exact_mod_cast h2) hu_le'
        have hT0_0 : T₀ = 0 := by dsimp only [T₀]; simp
        have hmax1 : max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 = 1 := by rw [hT0_0, mul_zero, max_eq_right zero_le_one]
        calc ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / (2 * ((d * k : ℕ) : ℝ) ^ r))‖
            ≤ 2 * P / d := le_trans htriv hcard
          _ = 1 * ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + 0) := by rw [hmax1, div_one, one_mul, add_zero]
          _ ≤ E := by
              dsimp only [E]
              refine mul_le_mul (le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_right _ _))
                (add_le_add le_rfl (by positivity)) (by positivity) (by positivity)
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have h_eq_phase : ∀ k : ℕ, 1 ≤ k →
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
            ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
          intro k _
          congr 1; refine Finset.sum_congr rfl fun r _ => ?_
          rw [Nat.cast_mul, mul_pow, zpow_neg, zpow_natCast]; ring
        have hsum_eq : ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
            ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
              ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) :=
          Finset.sum_congr rfl fun k hk => h_eq_phase k (by
            have h1 : (1 : ℝ) ≤ a' := le_trans hPd_ge1 hPa'
            exact le_trans (Nat.ceil_pos.mpr (by linarith)) (Finset.mem_Icc.mp hk).1)
        rw [hsum_eq]
        let cd : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)
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
        have hT_ge : (2 : ℝ) ^ (-(R : ℤ) - 1) * T₀ ≤ |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
          dsimp only [cd, T₀]
          have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
          have hupow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
          have h2pow : (2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ)) ≤ (2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ)) := by
            rw [show (2 * P / d) = (2 * P) / d by ring, zpow_sub₀ (by norm_num),
              zpow_neg (2 : ℝ) (R : ℤ), zpow_natCast (2 : ℝ) R, zpow_one,
              zpow_neg P (r₀ : ℤ), zpow_natCast P r₀,
              zpow_neg ((2 * P) / d) (r₀ : ℤ), zpow_natCast ((2 * P) / d) r₀,
              div_pow, inv_div, mul_pow, ← div_eq_mul_inv]
            field_simp [hd_pos.ne', hP_pos.ne']
            have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
            linarith [h2r]
          have habs_cd : |(h r₀ : ℝ) * n / (2 * (d : ℝ) ^ r₀)| = |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) := by
            rw [abs_div, abs_mul, abs_of_pos hn_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ r₀)]
          rw [habs_cd]
          calc (2 : ℝ) ^ (-(R : ℤ) - 1) * (|(h r₀ : ℝ)| * n / P ^ r₀)
              = |(h r₀ : ℝ)| * n * ((2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ))) := by
                  rw [zpow_neg, zpow_natCast]; ring
            _ ≤ |(h r₀ : ℝ)| * n * ((2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                  mul_le_mul_of_nonneg_left h2pow (by positivity)
            _ = |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) := by ring
            _ ≤ |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) :=
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
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖
        ≤ (W₀ + W₀) * E := by simpa [wd] using hps
      _ = 2 * (W₀ * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))) := by
          dsimp only [E]; ring
      _ ≤ 4 * W₀ * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          have hnn : 0 ≤ W₀ * max C_exp 3 *
              ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) :=
            mul_nonneg (mul_nonneg hW₀ (by positivity))
              (add_nonneg (div_nonneg (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
          linarith

end BrocardFormalization

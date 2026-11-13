/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.ExpSumVaughan

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

lemma exp_sum_laurent_bound (R K_max : ℕ) (hK_max : 3 ≤ K_max) :
    ∃ (C_exp η_exp : ℝ) (M₀ : ℝ), 0 < C_exp ∧ 0 < η_exp ∧ η_exp ≤ 1 / 4 ∧ 16 ≤ M₀ ∧
      ∀ (A : Finset ℕ) (r₀ : ℕ) (hr₀ : r₀ ∈ A) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
        (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (M₁ M₂ : ℝ),
        M₀ ≤ M₁ → M₁ ≤ M₂ → M₂ ≤ 2 * M₁ →
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) →
        let T := |c r₀| * (r₀ : ℝ) * M₂ ^ (-(r₀ : ℤ))
        T ≤ M₂ ^ (K_max - 1) →
        ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (∑ r ∈ A, c r * (m : ℝ) ^ (-(r : ℤ)))‖ ≤
          C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) := by
  obtain ⟨C_KL, hC_KL, hKL⟩ := kusmin_landau_bound
  have hvd2 := van_der_corput_kth_derivative 2 (by omega) (3 * (2 : ℝ) ^ (R + 2)) (by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (R + 2) := one_le_pow₀ (by norm_num)
    linarith)
  obtain ⟨C2, hC2, hvd2_bd⟩ := hvd2
  have hex_j : ∀ j ∈ Finset.Icc 3 K_max, ∃ Cj > 0, ∀ (M₁ M₂ lam : ℝ) (G : ℝ → ℝ),
      0 ≤ M₁ → 1 ≤ M₂ - M₁ →
      (M₂ - M₁) ^ (-(5 / 2 : ℝ)) ≤ lam → lam ≤ (M₂ - M₁) ^ (-(1 / 2 : ℝ)) →
      (∀ t ∈ Set.Icc M₁ M₂, lam ≤ |iteratedDeriv j G t| ∧ |iteratedDeriv j G t| ≤ (3 * (2 : ℝ) ^ (R + K_max)) * lam) →
      ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖ ≤
        2 * Cj * (M₂ - M₁) ^ (1 - (1 : ℝ) / (2 * ((2 ^ j - 2 : ℕ) : ℝ))) := by
    intro j hj
    have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    exact van_der_corput_for_range j hj3 (3 * (2 : ℝ) ^ (R + K_max)) (by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (R + K_max) := one_le_pow₀ (by norm_num)
      linarith)
  choose Cj_fn hCj_pos hCj_bd using hex_j
  let C_max_j : ℝ := (Finset.Icc 3 K_max).sup' ⟨3, Finset.mem_Icc.mpr ⟨le_rfl, hK_max⟩⟩
    (fun j => if hj : j ∈ Finset.Icc 3 K_max then 2 * Cj_fn j hj else 0)
  have hC_max_pos : 0 < C_max_j := by
    have hmem : (3 : ℕ) ∈ Finset.Icc 3 K_max := Finset.mem_Icc.mpr ⟨le_rfl, hK_max⟩
    have hle := Finset.le_sup' (fun j => if hj : j ∈ Finset.Icc 3 K_max then 2 * Cj_fn j hj else 0) hmem
    simp only [hmem, ↓reduceDIte] at hle
    linarith [hCj_pos 3 hmem]
  let η_exp : ℝ := min (1 / 4 : ℝ) ((1 : ℝ) / (2 * ((2 ^ K_max - 2 : ℕ) : ℝ)))
  have hη_pos : 0 < η_exp := by
    have : 6 ≤ 2 ^ K_max - 2 := by
      have : 8 ≤ 2 ^ K_max := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK_max)
      omega
    positivity
  let K_fact : ℝ := ((R + K_max).factorial : ℝ)
  let C_exp : ℝ := max (4 * C_KL) (max (C2 * ((R + 1 : ℝ) + (12 * (2 : ℝ) ^ R) ^ (1 / 2 : ℝ) + 1)) (max C_max_j 4))
  have hC_exp_pos : 0 < C_exp := by positivity
  let M₀ : ℝ := max 16 ((K_fact + 1) ^ 4)
  refine ⟨C_exp, η_exp, M₀, hC_exp_pos, hη_pos, min_le_left _ _, le_max_left _ _, ?_⟩
  intro A r₀ hr₀ hA c hc₀ M₁ M₂ hM₁ hM₁₂ hM₂ hdom T hT_ub
  have hM₁_pos : 0 < M₁ := lt_of_lt_of_le (by positivity) (le_trans (le_max_left _ _) hM₁)
  have hM₂_ge16 : 16 ≤ M₂ := le_trans (le_max_left _ _) (le_trans hM₁ hM₁₂)
  have hM₂_pos : 0 < M₂ := by linarith
  have hr₀_1 : 1 ≤ r₀ := (hA r₀ hr₀).1
  have hr₀_R : r₀ ≤ R := (hA r₀ hr₀).2
  set G : ℝ → ℝ := fun u => ∑ r ∈ A, c r * u ^ (-(r : ℤ))
  by_cases hL_small : M₂ - M₁ < M₂ ^ (3 / 4 : ℝ)
  · have htriv : ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖ ≤
        ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      simp [ePhase, Complex.norm_exp_ofReal_mul_I]
    have hcard : ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) ≤ M₂ - M₁ + 2 := by
      rw [Nat.card_Icc]
      by_cases hle : ⌈M₁⌉₊ ≤ ⌊M₂⌋₊ + 1
      · rw [Nat.cast_sub hle]
        have h1 : (⌊M₂⌋₊ : ℝ) ≤ M₂ := Nat.floor_le hM₂_pos.le
        have h2 : M₁ ≤ (⌈M₁⌉₊ : ℝ) := Nat.le_ceil M₁
        push_cast; linarith
      · push_neg at hle
        rw [Nat.sub_eq_zero_of_le hle.le]; push_cast; linarith
    have hM2_pow : M₂ ^ (3 / 4 : ℝ) ≤ M₂ ^ (1 - η_exp) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      have : η_exp ≤ 1 / 4 := min_le_left _ _
      linarith
    have h2_le : (2 : ℝ) ≤ M₂ ^ (1 - η_exp) := by
      have : (2 : ℝ) ≤ M₂ ^ (3 / 4 : ℝ) := by
        have h16 : (16 : ℝ) ^ (3 / 4 : ℝ) = 8 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        linarith [Real.rpow_le_rpow (by norm_num) hM₂_ge16 (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      linarith
    calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
        ≤ M₂ - M₁ + 2 := le_trans htriv hcard
      _ ≤ 2 * M₂ ^ (1 - η_exp) := by linarith
      _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) := by
          have hC4 : (4 : ℝ) ≤ C_exp := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          have hnn : 0 ≤ M₂ / max T 1 := by positivity
          nlinarith
  · push_neg at hL_small
    set L : ℝ := M₂ - M₁
    have hL_ge1 : 1 ≤ L := by
      have : (1 : ℝ) ≤ M₂ ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      linarith
    have hL_le_M2 : L ≤ M₂ := by linarith
    have hT_pos : 0 < T := by dsimp only [T]; positivity
    by_cases hT_small : T ≤ M₂ / (6 * (2 : ℝ) ^ R)
    · have h1 := laurent_sum_dom_bounds A R 1 hA r₀ hr₀ c hc₀ (by omega) M₁ M₂ hM₁_pos hM₁₂ hM₂
        (hdom 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
      set lam1 := (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + 1 - 1) 1 : ℝ) * M₂ ^ (-(r₀ + 1 : ℤ))
      have hlam1_eq : lam1 = T / (2 * M₂) := by
        dsimp only [lam1, T]
        rw [show r₀ + 1 - 1 = r₀ by omega, Nat.descFactorial_one,
          show -(r₀ + 1 : ℤ) = -(r₀ : ℤ) + (-1 : ℤ) by omega, zpow_add₀ hM₂_pos.ne', zpow_neg_one]
        ring
      have hmono : MonotoneOn (deriv G) (Set.Icc M₁ M₂) ∨ AntitoneOn (deriv G) (Set.Icc M₁ M₂) :=
        laurent_sum_deriv_mono_or_anti A R hA r₀ hr₀ c hc₀ M₁ M₂ hM₁_pos hM₁₂ hM₂
          (hdom 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      have hbd1 : ∀ t ∈ Set.Icc M₁ M₂, lam1 ≤ |deriv G t| ∧ |deriv G t| ≤ 1 / 2 := by
        intro t ht
        have ht1 := h1.2 t ht
        rw [iteratedDeriv_one] at ht1
        refine ⟨ht1.1, le_trans ht1.2 ?_⟩
        rw [hlam1_eq, pow_succ]
        rw [show 3 * ((2 : ℝ) ^ R * 2) * (T / (2 * M₂)) = 3 * (2 : ℝ) ^ R * (T / M₂) by ring]
        rw [mul_div_assoc', div_le_iff₀ hM₂_pos]
        rw [le_div_iff₀ (by positivity)] at hT_small
        linarith
      have hkl := hKL M₁ M₂ lam1 G hM₁_pos.le hM₁₂ h1.1 hmono hbd1
      have hT_le_1_or : M₂ / T ≤ M₂ / max T 1 + M₂ ^ (1 - η_exp) ∨ T < 1 := by
        by_cases hT1 : 1 ≤ T
        · left; rw [max_eq_left hT1]; linarith [Real.rpow_pos_of_pos hM₂_pos (1 - η_exp)]
        · right; linarith
      by_cases hT1 : 1 ≤ T
      · have hmax : max T 1 = T := max_eq_left hT1
        calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
            ≤ C_KL / lam1 := hkl
          _ = 2 * C_KL * (M₂ / T) := by rw [hlam1_eq]; ring
          _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) := by
              rw [hmax]
              have hC : 4 * C_KL ≤ C_exp := le_max_left _ _
              have hnn1 : 0 ≤ M₂ / T := by positivity
              have hnn2 : 0 ≤ M₂ ^ (1 - η_exp) := by positivity
              nlinarith
      · push_neg at hT1
        have hmax : max T 1 = 1 := max_eq_right hT1.le
        have htriv : ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖ ≤
            ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          simp [ePhase, Complex.norm_exp_ofReal_mul_I]
        have hcard : ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) ≤ M₂ - M₁ + 2 := by
          rw [Nat.card_Icc]
          by_cases hle : ⌈M₁⌉₊ ≤ ⌊M₂⌋₊ + 1
          · rw [Nat.cast_sub hle]
            have h1 : (⌊M₂⌋₊ : ℝ) ≤ M₂ := Nat.floor_le hM₂_pos.le
            have h2 : M₁ ≤ (⌈M₁⌉₊ : ℝ) := Nat.le_ceil M₁
            push_cast; linarith
          · push_neg at hle
            rw [Nat.sub_eq_zero_of_le hle.le]; push_cast; linarith
        calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
            ≤ M₂ - M₁ + 2 := le_trans htriv hcard
          _ ≤ 2 * M₂ := by linarith
          _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) := by
              rw [hmax, div_one]
              have hC4 : (4 : ℝ) ≤ C_exp := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
              have hnn2 : 0 ≤ M₂ ^ (1 - η_exp) := by positivity
              nlinarith
    · push_neg at hT_small
      by_cases hT_vd2 : T ≤ M₂ ^ (3 / 2 : ℝ)
      · have h2 := laurent_sum_dom_bounds A R 2 hA r₀ hr₀ c hc₀ (by omega) M₁ M₂ hM₁_pos hM₁₂ hM₂
          (hdom 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        set lam2 := (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * M₂ ^ (-(r₀ + 2 : ℤ))
        have hlam2_eq : lam2 = ((r₀ + 1 : ℝ) / 2) * (T / M₂ ^ 2) := by
          dsimp only [lam2, T]
          have hdesc2 : Nat.descFactorial (r₀ + 2 - 1) 2 = (r₀ + 1) * r₀ := by
            rw [show r₀ + 2 - 1 = r₀ + 1 by omega, Nat.succ_descFactorial_succ, Nat.descFactorial_one]
          rw [hdesc2, show -(r₀ + 2 : ℤ) = -(r₀ : ℤ) + (-2 : ℤ) by omega, zpow_add₀ hM₂_pos.ne',
            show M₂ ^ (-2 : ℤ) = (M₂ ^ 2)⁻¹ by rw [zpow_neg, zpow_natCast]]
          push_cast; ring
        have hlam2_ge : T / (2 * M₂ ^ 2) ≤ lam2 := by
          rw [hlam2_eq]
          have : (1 : ℝ) ≤ r₀ + 1 := by exact_mod_cast (by omega : 1 ≤ r₀ + 1)
          nlinarith [div_nonneg hT_pos.le (pow_nonneg hM₂_pos.le 2)]
        have hlam2_le : lam2 ≤ (R + 1 : ℝ) * (T / M₂ ^ 2) := by
          rw [hlam2_eq]
          have : (r₀ + 1 : ℝ) / 2 ≤ R + 1 := by
            have : (r₀ : ℝ) ≤ R := by exact_mod_cast hr₀_R
            linarith
          exact mul_le_mul_of_nonneg_right this (div_nonneg hT_pos.le (pow_nonneg hM₂_pos.le 2))
        have hvd := hvd2_bd M₁ M₂ lam2 G hM₁_pos.le hL_ge1 h2.1 (fun t ht => h2.2 t ht)
        have hpow2 : (2 ^ 2 - 2 : ℕ) = 2 := by norm_num
        have hz2 : (2 : ℤ) - (2 : ℤ) = 0 := by norm_num
        rw [hpow2, hz2, zpow_zero, sub_self, Real.rpow_zero] at hvd
        have hterm1 : L * lam2 ^ ((1 : ℝ) / (2 : ℕ)) ≤ (R + 1 : ℝ) * M₂ ^ (3 / 4 : ℝ) := by
          have hlam2_ub : lam2 ≤ (R + 1 : ℝ) ^ 2 * M₂ ^ (-(1 / 2 : ℝ)) := by
            have h1 : lam2 ≤ (R + 1 : ℝ) * (M₂ ^ (3 / 2 : ℝ) / M₂ ^ 2) :=
              le_trans hlam2_le (mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hT_vd2 (by positivity)) (by positivity))
            have h2 : M₂ ^ (3 / 2 : ℝ) / M₂ ^ 2 = M₂ ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_natCast M₂ 2, ← Real.rpow_sub hM₂_pos]; norm_num
            have hR1 : (R + 1 : ℝ) ≤ (R + 1 : ℝ) ^ 2 := by
              have : (1 : ℝ) ≤ R + 1 := by exact_mod_cast (by omega : 1 ≤ R + 1)
              nlinarith
            rw [h2] at h1
            exact le_trans h1 (mul_le_mul_of_nonneg_right hR1 (by positivity))
          have hpow : lam2 ^ ((1 : ℝ) / (2 : ℕ)) ≤ (R + 1 : ℝ) * M₂ ^ (-(1 / 4 : ℝ)) := by
            have h1 := Real.rpow_le_rpow (by positivity) hlam2_ub (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℕ))
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (R + 1 : ℝ) 2,
              ← Real.rpow_mul (by positivity), ← Real.rpow_mul hM₂_pos.le] at h1
            norm_num at h1
            exact h1
          calc L * lam2 ^ ((1 : ℝ) / (2 : ℕ))
              ≤ M₂ * ((R + 1 : ℝ) * M₂ ^ (-(1 / 4 : ℝ))) := mul_le_mul hL_le_M2 hpow (by positivity) hM₂_pos.le
            _ = (R + 1 : ℝ) * (M₂ ^ (1 : ℝ) * M₂ ^ (-(1 / 4 : ℝ))) := by rw [Real.rpow_one]; ring
            _ = (R + 1 : ℝ) * M₂ ^ (3 / 4 : ℝ) := by
                rw [← Real.rpow_add hM₂_pos]; norm_num
        have hterm2 : lam2 ^ (-(1 : ℝ) / (2 : ℕ)) ≤ (12 * (2 : ℝ) ^ R) ^ (1 / 2 : ℝ) * M₂ ^ (3 / 4 : ℝ) := by
          have hlam2_lb : (12 * (2 : ℝ) ^ R)⁻¹ * M₂ ^ (-(1 : ℝ)) ≤ lam2 := by
            have h1 : (M₂ / (6 * (2 : ℝ) ^ R)) / (2 * M₂ ^ 2) ≤ lam2 :=
              le_trans (div_le_div_of_nonneg_right hT_small.le (by positivity)) hlam2_ge
            have h2 : (M₂ / (6 * (2 : ℝ) ^ R)) / (2 * M₂ ^ 2) = (12 * (2 : ℝ) ^ R)⁻¹ * M₂ ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg_one]; field_simp [hM₂_pos.ne']; ring
            linarith
          have hneg : (-(1 : ℝ) / (2 : ℕ)) ≤ 0 := by norm_num
          have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) hlam2_lb hneg
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hM₂_pos.le,
            show (-(1 : ℝ) * (-(1 : ℝ) / (2 : ℕ))) = 1 / 2 by norm_num,
            show (-(1 : ℝ) / (2 : ℕ)) = -(1 / 2 : ℝ) by norm_num, Real.inv_rpow (by positivity),
            Real.rpow_neg (by positivity), inv_inv] at hpow
          have hM_le : M₂ ^ (1 / 2 : ℝ) ≤ M₂ ^ (3 / 4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          exact le_trans hpow (mul_le_mul_of_nonneg_left hM_le (by positivity))
        have hM2_pow : M₂ ^ (3 / 4 : ℝ) ≤ M₂ ^ (1 - η_exp) := by
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          have : η_exp ≤ 1 / 4 := min_le_left _ _
          linarith
        calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
            ≤ C2 * (L * lam2 ^ ((1 : ℝ) / (2 : ℕ)) + 1 * lam2 ^ (-(1 : ℝ) / (2 : ℕ))) := hvd
          _ ≤ C2 * ((R + 1 : ℝ) * M₂ ^ (3 / 4 : ℝ) + (12 * (2 : ℝ) ^ R) ^ (1 / 2 : ℝ) * M₂ ^ (3 / 4 : ℝ)) := by
              refine mul_le_mul_of_nonneg_left (add_le_add hterm1 (by linarith)) hC2.le
          _ = C2 * ((R + 1 : ℝ) + (12 * (2 : ℝ) ^ R) ^ (1 / 2 : ℝ)) * M₂ ^ (3 / 4 : ℝ) := by ring
          _ ≤ C_exp * M₂ ^ (1 - η_exp) := by
              refine mul_le_mul ?_ hM2_pow (by positivity) hC_exp_pos.le
              exact le_trans (by linarith [hC2.le]) (le_trans (le_max_left _ _) (le_max_right _ _))
          _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC_exp_pos.le
      · push_neg at hT_vd2
        let lam_fn : ℕ → ℝ := fun j =>
          (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + j - 1) j : ℝ) * M₂ ^ (-(r₀ + j : ℤ))
        have hlam_K : lam_fn K_max ≤ L ^ (-(1 / 2 : ℝ)) := by
          dsimp only [lam_fn]
          have hdesc_le : (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) ≤ K_fact * (r₀ : ℝ) := by
            have h1 : Nat.descFactorial (r₀ + K_max - 1) K_max ≤ (r₀ + K_max).factorial := by
              rw [Nat.descFactorial_eq_factorial_div_factorial (r₀ + K_max - 1) K_max]
              exact le_trans (Nat.div_le_self _ _) (Nat.factorial_le (by omega))
            have h1R : (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) ≤ K_fact := by exact_mod_cast h1
            have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast hr₀_1
            nlinarith
          have hlam_ub : (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) * M₂ ^ (-(r₀ + K_max : ℤ)) ≤
              K_fact * (T / M₂ ^ K_max) := by
            have hz : M₂ ^ (-(r₀ + K_max : ℤ)) = M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max := by
              rw [show -(r₀ + K_max : ℤ) = -(r₀ : ℤ) + -(K_max : ℤ) by omega,
                zpow_add₀ hM₂_pos.ne', zpow_neg, zpow_natCast, div_eq_mul_inv]
            rw [hz]
            dsimp only [T]
            have : (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max) ≤
                (1 : ℝ) * |c r₀| * (K_fact * (r₀ : ℝ)) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              refine mul_le_mul ?_ hdesc_le (by positivity) (by positivity)
              linarith [abs_nonneg (c r₀)]
            linarith
          have hT_div : T / M₂ ^ K_max ≤ M₂ ^ (-(1 : ℝ)) := by
            rw [div_le_iff₀ (by positivity)]
            have hpow_eq : M₂ ^ (-(1 : ℝ)) * M₂ ^ K_max = M₂ ^ (K_max - 1) := by
              rw [Real.rpow_neg_one, ← Nat.sub_add_cancel (by omega : 1 ≤ K_max), pow_succ']
              field_simp [hM₂_pos.ne']
            linarith
          have hK_le : K_fact * M₂ ^ (-(1 : ℝ)) ≤ M₂ ^ (-(1 / 2 : ℝ)) := by
            have hM0_K : K_fact ≤ M₂ ^ (1 / 4 : ℝ) := by
              have h1 : (K_fact + 1 : ℝ) ^ (4 : ℝ) ≤ M₂ := by
                have hle : (K_fact + 1 : ℝ) ^ 4 ≤ M₀ := le_max_right _ _
                rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
                exact le_trans hle (le_trans hM₁ hM₁₂)
              have h2 := (Real.le_rpow_inv_iff_of_pos (by positivity) hM₂_pos.le (by norm_num : (0 : ℝ) < 4)).mpr h1
              rw [one_div]
              linarith
            calc K_fact * M₂ ^ (-(1 : ℝ))
                ≤ M₂ ^ (1 / 4 : ℝ) * M₂ ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_right hM0_K (by positivity)
              _ = M₂ ^ (-(3 / 4 : ℝ)) := by rw [← Real.rpow_add hM₂_pos]; norm_num
              _ ≤ M₂ ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          have hM_L : M₂ ^ (-(1 / 2 : ℝ)) ≤ L ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hL_ge1 hL_le_M2 (by norm_num)
          exact le_trans hlam_ub (le_trans (mul_le_mul_of_nonneg_left hT_div (by positivity)) (le_trans hK_le hM_L))
        let S_j := (Finset.Icc 3 K_max).filter (fun j => lam_fn j ≤ L ^ (-(1 / 2 : ℝ)))
        have hS_ne : S_j.Nonempty := ⟨K_max, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hK_max, le_rfl⟩, hlam_K⟩⟩
        set j₀ := S_j.min' hS_ne
        have hj₀_mem : j₀ ∈ Finset.Icc 3 K_max := (Finset.mem_filter.mp (Finset.min'_mem S_j hS_ne)).1
        have hj₀_le : lam_fn j₀ ≤ L ^ (-(1 / 2 : ℝ)) := (Finset.mem_filter.mp (Finset.min'_mem S_j hS_ne)).2
        have hj₀_3 : 3 ≤ j₀ := (Finset.mem_Icc.mp hj₀_mem).1
        have hj₀_ge : L ^ (-(5 / 2 : ℝ)) ≤ lam_fn j₀ := by
          by_cases h3 : j₀ = 3
          · subst h3
            have hlam3 : T / (2 * M₂ ^ 3) ≤ lam_fn 3 := by
              dsimp only [lam_fn, T]
              have hdesc3 : (r₀ : ℝ) ≤ (Nat.descFactorial (r₀ + 3 - 1) 3 : ℝ) := by
                have : r₀ ≤ Nat.descFactorial (r₀ + 3 - 1) 3 := by
                  rw [show r₀ + 3 - 1 = r₀ + 2 by omega, Nat.descFactorial_succ, Nat.descFactorial_succ,
                    Nat.descFactorial_one]
                  nlinarith
                exact_mod_cast this
              have hz : M₂ ^ (-(r₀ + 3 : ℤ)) = M₂ ^ (-(r₀ : ℤ)) / M₂ ^ 3 := by
                rw [show -(r₀ + 3 : ℤ) = -(r₀ : ℤ) + (-3 : ℤ) by omega,
                  zpow_add₀ hM₂_pos.ne', zpow_neg, zpow_natCast, div_eq_mul_inv]
              rw [hz]
              have : (1 / 2 : ℝ) * |c r₀| * (r₀ : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ 3) ≤
                  (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + 3 - 1) 3 : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ 3) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdesc3 (by positivity)) (by positivity)
              linarith
            have hT_bd : M₂ ^ (-(3 / 2 : ℝ)) / 2 ≤ T / (2 * M₂ ^ 3) := by
              have h1 : M₂ ^ (3 / 2 : ℝ) / (2 * M₂ ^ 3) ≤ T / (2 * M₂ ^ 3) :=
                div_le_div_of_nonneg_right hT_vd2.le (by positivity)
              have h2 : M₂ ^ (3 / 2 : ℝ) / (2 * M₂ ^ 3) = M₂ ^ (-(3 / 2 : ℝ)) / 2 := by
                rw [div_mul_eq_div_div, ← Real.rpow_natCast M₂ 3, ← Real.rpow_sub hM₂_pos]
                norm_num; ring
              linarith
            have hL_bd : L ^ (-(5 / 2 : ℝ)) ≤ M₂ ^ (-(3 / 2 : ℝ)) / 2 := by
              have h1 : L ^ (-(5 / 2 : ℝ)) ≤ (M₂ ^ (3 / 4 : ℝ)) ^ (-(5 / 2 : ℝ)) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hL_small (by norm_num)
              rw [← Real.rpow_mul hM₂_pos.le] at h1
              have h2 : (M₂ ^ ((3 / 4 : ℝ) * -(5 / 2 : ℝ))) * 2 ≤ M₂ ^ (-(3 / 2 : ℝ)) := by
                have hM2_16 : (2 : ℝ) ≤ M₂ ^ (3 / 8 : ℝ) := by
                  have h16 : (2 : ℝ) ≤ (16 : ℝ) ^ (3 / 8 : ℝ) := by
                    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
                    norm_num
                    exact Real.one_le_rpow (by norm_num) (by norm_num) |>.trans_le (by
                      rw [← Real.rpow_one (2 : ℝ)]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
                  exact le_trans h16 (Real.rpow_le_rpow (by norm_num) hM₂_ge16 (by norm_num))
                calc M₂ ^ ((3 / 4 : ℝ) * -(5 / 2 : ℝ)) * 2
                    ≤ M₂ ^ (-(15 / 8 : ℝ)) * M₂ ^ (3 / 8 : ℝ) := by
                      rw [show (3 / 4 : ℝ) * -(5 / 2 : ℝ) = -(15 / 8 : ℝ) by norm_num]
                      exact mul_le_mul_of_nonneg_left hM2_16 (by positivity)
                  _ = M₂ ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hM₂_pos]; norm_num
              linarith
            exact le_trans hL_bd (le_trans hT_bd hlam3)
          · have hj1_mem : j₀ - 1 ∈ Finset.Icc 3 K_max := by
              rw [Finset.mem_Icc] at hj₀_mem ⊢; omega
            have hj1_not : ¬ lam_fn (j₀ - 1) ≤ L ^ (-(1 / 2 : ℝ)) := by
              intro hle
              have := Finset.min'_le S_j (j₀ - 1) (Finset.mem_filter.mpr ⟨hj1_mem, hle⟩)
              omega
            push_neg at hj1_not
            have hratio : lam_fn (j₀ - 1) / M₂ ≤ lam_fn j₀ := by
              dsimp only [lam_fn]
              have hdesc : Nat.descFactorial (r₀ + j₀ - 1) j₀ =
                  (r₀ + j₀ - 1) * Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) := by
                rw [show r₀ + j₀ - 1 = (r₀ + (j₀ - 1) - 1) + 1 by omega, Nat.succ_descFactorial_succ]
              have hz : M₂ ^ (-(r₀ + j₀ : ℤ)) = M₂ ^ (-(r₀ + (j₀ - 1) : ℤ)) / M₂ := by
                rw [show -(r₀ + j₀ : ℤ) = -(r₀ + (j₀ - 1) : ℤ) + (-1 : ℤ) by omega,
                  zpow_add₀ hM₂_pos.ne', zpow_neg_one, div_eq_mul_inv]
              rw [hdesc, hz]
              push_cast
              have hge1 : (1 : ℝ) ≤ (r₀ + j₀ - 1 : ℝ) := by
                exact_mod_cast (by omega : 1 ≤ r₀ + j₀ - 1)
              have hnn : 0 ≤ (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) : ℝ) *
                  (M₂ ^ (-(r₀ + (j₀ - 1) : ℤ)) / M₂) := by positivity
              calc (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) : ℝ) *
                    M₂ ^ (-(r₀ + (j₀ - 1) : ℤ)) / M₂
                  = 1 * ((1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) : ℝ) *
                      (M₂ ^ (-(r₀ + (j₀ - 1) : ℤ)) / M₂)) := by ring
                _ ≤ (r₀ + j₀ - 1 : ℝ) * ((1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) : ℝ) *
                      (M₂ ^ (-(r₀ + (j₀ - 1) : ℤ)) / M₂)) := mul_le_mul_of_nonneg_right hge1 hnn
                _ = _ := by ring
            have hL_M2 : L ^ (-(5 / 2 : ℝ)) ≤ L ^ (-(1 / 2 : ℝ)) / M₂ := by
              have hM2_L : M₂ ≤ L ^ (4 / 3 : ℝ) := by
                have h1 := Real.rpow_le_rpow (by positivity) hL_small (by norm_num : (0 : ℝ) ≤ 4 / 3)
                rw [← Real.rpow_mul hM₂_pos.le] at h1
                norm_num at h1; exact h1
              calc L ^ (-(5 / 2 : ℝ))
                  ≤ L ^ (-(11 / 6 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL_ge1 (by norm_num)
                _ = L ^ (-(1 / 2 : ℝ)) / L ^ (4 / 3 : ℝ) := by
                    rw [← Real.rpow_sub hL_pos]; norm_num
                _ ≤ L ^ (-(1 / 2 : ℝ)) / M₂ :=
                    div_le_div_of_nonneg_left (by positivity) hM₂_pos hM2_L
            exact le_trans hL_M2 (le_trans (div_le_div_of_nonneg_right hj1_not.le hM₂_pos.le) hratio)
        have hj₀_dom := laurent_sum_dom_bounds A R j₀ hA r₀ hr₀ c hc₀ (by omega) M₁ M₂ hM₁_pos hM₁₂ hM₂
          (hdom j₀ hj₀_mem)
        have hj₀_bd : ∀ t ∈ Set.Icc M₁ M₂,
            lam_fn j₀ ≤ |iteratedDeriv j₀ G t| ∧ |iteratedDeriv j₀ G t| ≤ (3 * (2 : ℝ) ^ (R + K_max)) * lam_fn j₀ := by
          intro t ht
          have hpt := hj₀_dom.2 t ht
          refine ⟨hpt.1, le_trans hpt.2 (mul_le_mul_of_nonneg_right ?_ ?_)⟩
          · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by
              have := (Finset.mem_Icc.mp hj₀_mem).2; omega)) (by norm_num)
          · exact hj₀_dom.1.le
        have hvd_j := hCj_bd j₀ hj₀_mem M₁ M₂ (lam_fn j₀) G hM₁_pos.le hL_ge1 hj₀_ge hj₀_le hj₀_bd
        have hC_le : 2 * Cj_fn j₀ hj₀_mem ≤ C_exp := by
          have h1 : 2 * Cj_fn j₀ hj₀_mem ≤ C_max_j := by
            have hle := Finset.le_sup' (fun j => if hj : j ∈ Finset.Icc 3 K_max then 2 * Cj_fn j hj else 0) hj₀_mem
            simpa [hj₀_mem] using hle
          exact le_trans h1 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
        have hpow_le : L ^ (1 - (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ))) ≤ M₂ ^ (1 - η_exp) := by
          have hexp1 : 1 - (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ)) ≤ 1 - η_exp := by
            have hη : η_exp ≤ (1 : ℝ) / (2 * ((2 ^ K_max - 2 : ℕ) : ℝ)) := min_le_right _ _
            have hd_le : (2 ^ j₀ - 2 : ℕ) ≤ 2 ^ K_max - 2 := by
              have h2j : 2 ^ j₀ ≤ 2 ^ K_max := Nat.pow_le_pow_right (by norm_num) (Finset.mem_Icc.mp hj₀_mem).2
              omega
            have hd_pos : (0 : ℝ) < (2 ^ j₀ - 2 : ℕ) := by
              have : 8 ≤ 2 ^ j₀ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj₀_3)
              exact_mod_cast (by omega : 0 < 2 ^ j₀ - 2)
            have hdiv : (1 : ℝ) / (2 * ((2 ^ K_max - 2 : ℕ) : ℝ)) ≤ (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ)) :=
              one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hd_le) (by norm_num))
            linarith
          have hL_pow : L ^ (1 - (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ))) ≤ M₂ ^ (1 - (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ))) := by
            refine Real.rpow_le_rpow (by positivity) hL_le_M2 ?_
            have : (1 : ℝ) ≤ 2 * ((2 ^ j₀ - 2 : ℕ) : ℝ) := by
              have : 8 ≤ 2 ^ j₀ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj₀_3)
              have : (6 : ℝ) ≤ (2 ^ j₀ - 2 : ℕ) := by exact_mod_cast (by omega : 6 ≤ 2 ^ j₀ - 2)
              linarith
            have : (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ)) ≤ 1 := div_le_one_of_le₀ this (by positivity)
            linarith
          exact le_trans hL_pow (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp1)
        calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
            ≤ 2 * Cj_fn j₀ hj₀_mem * L ^ (1 - (1 : ℝ) / (2 * ((2 ^ j₀ - 2 : ℕ) : ℝ))) := hvd_j
          _ ≤ C_exp * M₂ ^ (1 - η_exp) := mul_le_mul hC_le hpow_le (by positivity) hC_exp_pos.le
          _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC_exp_pos.le

lemma sum_divisors_card_sq_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ x ∈ Finset.Icc 1 X, ((x.divisors.card : ℝ) ^ 2) ≤ (X : ℝ) * (1 + Real.log X) ^ 3 := by
  have h1 : ∑ x ∈ Finset.Icc 1 X, (x.divisors.card : ℝ) ^ 2 =
      ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X,
        (((Finset.Icc 1 X).filter (fun x => Nat.lcm d₁ d₂ ∣ x)).card : ℝ) := by
    have hsq : ∀ x ∈ Finset.Icc 1 X, (x.divisors.card : ℝ) ^ 2 =
        ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X,
          if Nat.lcm d₁ d₂ ∣ x then (1 : ℝ) else 0 := by
      intro x hx
      have hx_pos : 0 < x := (Finset.mem_Icc.mp hx).1
      have hsub : x.divisors ⊆ Finset.Icc 1 X := fun d hd =>
        Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
          le_trans (Nat.le_of_dvd hx_pos (Nat.dvd_of_mem_divisors hd)) (Finset.mem_Icc.mp hx).2⟩
      rw [sq, ← Finset.sum_boole_mul]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Nat.cast_mul]
      rw [← Finset.sum_subset hsub (fun d _ hd => by simp [Nat.mem_divisors.not.mp hd])]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset hsub (fun d _ hd => by simp [Nat.mem_divisors.not.mp hd])]
      refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
      by_cases h1 : d₁ ∣ x <;> by_cases h2 : d₂ ∣ x
      · have hl : Nat.lcm d₁ d₂ ∣ x := Nat.lcm_dvd h1 h2
        simp [h1, h2, hl, hx_pos.ne']
      · have hl : ¬ Nat.lcm d₁ d₂ ∣ x := fun h => h2 (dvd_trans (Nat.dvd_lcm_right d₁ d₂) h)
        simp [h1, h2, hl]
      · have hl : ¬ Nat.lcm d₁ d₂ ∣ x := fun h => h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) h)
        simp [h1, h2, hl]
      · have hl : ¬ Nat.lcm d₁ d₂ ∣ x := fun h => h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) h)
        simp [h1, h2, hl]
    rw [Finset.sum_congr rfl hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    simp [Finset.card_filter]
  have h2 : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ →
      (((Finset.Icc 1 X).filter (fun x => Nat.lcm d₁ d₂ ∣ x)).card : ℝ) ≤
        (X : ℝ) / (Nat.lcm d₁ d₂ : ℝ) := by
    intro d₁ d₂ hd₁ hd₂
    set L := Nat.lcm d₁ d₂
    have hL_pos : 0 < L := Nat.lcm_pos hd₁ hd₂
    have hsub : (Finset.Icc 1 X).filter (fun x => L ∣ x) ⊆
        (Finset.Icc 1 (X / L)).image (fun k => L * k) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      rcases hx.2 with ⟨k, rfl⟩
      refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · by_contra hk0
        have : k = 0 := by omega
        subst this; simp at hx
      · exact (Nat.le_div_iff_mul_le hL_pos).mpr (by linarith [hx.1.2])
    have hcard : ((Finset.Icc 1 X).filter (fun x => L ∣ x)).card ≤ X / L := by
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      simp
    have hcast : (((Finset.Icc 1 X).filter (fun x => L ∣ x)).card : ℝ) ≤ ((X / L : ℕ) : ℝ) := by
      exact_mod_cast hcard
    refine le_trans hcast ?_
    rw [le_div_iff₀ (by exact_mod_cast hL_pos)]
    exact_mod_cast Nat.div_mul_le_self X L
  have h3 : ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm d₁ d₂ : ℝ) ≤
      (X : ℝ) * (∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g) ^ 3 := by
    let f : ℕ × ℕ → ℕ × ℕ × ℕ := fun p =>
      (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    have hinj : Set.InjOn f (Finset.Icc 1 X ×ˢ Finset.Icc 1 X : Set (ℕ × ℕ)) := by
      intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [f, Prod.mk.injEq] at h
      have h1 : a₁ = a₂ := by
        calc a₁ = Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ b₁)).symm
          _ = Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := by rw [h.1, h.2.1]
          _ = a₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left a₂ b₂)
      have h2 : b₁ = b₂ := by
        calc b₁ = Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ b₁)).symm
          _ = Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := by rw [h.1, h.2.2]
          _ = b₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right a₂ b₂)
      exact Prod.ext h1 h2
    have hmaps : Set.MapsTo f (Finset.Icc 1 X ×ˢ Finset.Icc 1 X : Set (ℕ × ℕ))
        (Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X : Set (ℕ × ℕ × ℕ)) := by
      intro ⟨d₁, d₂⟩ hd
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hd ⊢
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd.1.1
      have hg_le : Nat.gcd d₁ d₂ ≤ X := le_trans (Nat.gcd_le_left d₂ hd.1.1) hd.1.2
      have ha_pos : 0 < d₁ / Nat.gcd d₁ d₂ := Nat.div_pos (Nat.gcd_le_left d₂ hd.1.1) hg_pos
      have hb_pos : 0 < d₂ / Nat.gcd d₁ d₂ := Nat.div_pos (Nat.gcd_le_right d₁ hd.2.1) hg_pos
      exact ⟨⟨hg_pos, hg_le⟩, ⟨ha_pos, le_trans (Nat.div_le_self _ _) hd.1.2⟩,
        ⟨hb_pos, le_trans (Nat.div_le_self _ _) hd.2.2⟩⟩
    have hlcm_eq : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ →
        Nat.lcm d₁ d₂ = Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
      intro d₁ d₂ hd₁ hd₂
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd₁
      have hmul := Nat.gcd_mul_lcm d₁ d₂
      have hdvd1 : Nat.gcd d₁ d₂ ∣ d₁ := Nat.gcd_dvd_left d₁ d₂
      have hdvd2 : Nat.gcd d₁ d₂ ∣ d₂ := Nat.gcd_dvd_right d₁ d₂
      nlinarith [Nat.mul_div_cancel' hdvd1, Nat.mul_div_cancel' hdvd2]
    rw [← Finset.sum_product']
    have hrew : ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm p.1 p.2 : ℝ) =
        ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
          (X : ℝ) / (((f p).1 : ℝ) * ((f p).2.1 : ℝ) * ((f p).2.2 : ℝ)) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      rw [hlcm_eq p.1 p.2 hp.1.1 hp.2.1]
      push_cast; rfl
    rw [hrew]
    have hle_img : ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
          (X : ℝ) / (((f p).1 : ℝ) * ((f p).2.1 : ℝ) * ((f p).2.2 : ℝ)) ≤
        ∑ q ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
          (X : ℝ) / ((q.1 : ℝ) * (q.2.1 : ℝ) * (q.2.2 : ℝ)) := by
      rw [← Finset.sum_image (f := f) (fun a ha b hb hab => hinj ha hb hab)]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by positivity)
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      exact hmaps hp
    refine le_trans hle_img ?_
    rw [Finset.sum_product, pow_three]
    simp_rw [Finset.sum_product, div_eq_mul_inv, mul_inv, ← mul_assoc]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring_nf; rfl
  have hharm : ∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g ≤ 1 + Real.log X := by
    have heq : ∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g = (harmonic X : ℝ) := by
      clear h1 h2 h3
      induction X with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
        push_cast; ring
    rw [heq]
    simpa using harmonic_le_one_add_log X
  calc ∑ x ∈ Finset.Icc 1 X, (x.divisors.card : ℝ) ^ 2
      = ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X,
          (((Finset.Icc 1 X).filter (fun x => Nat.lcm d₁ d₂ ∣ x)).card : ℝ) := h1
    _ ≤ ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm d₁ d₂ : ℝ) := by
        refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
        exact h2 d₁ d₂ (Finset.mem_Icc.mp hd₁).1 (Finset.mem_Icc.mp hd₂).1
    _ ≤ (X : ℝ) * (∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g) ^ 3 := h3
    _ ≤ (X : ℝ) * (1 + Real.log X) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hharm 3)
          (Nat.cast_nonneg X)

lemma type_I_single_d_bound
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
        (Real.log k * w (d * k) : ℂ) *
          ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
      4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
        ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
  intro T₀
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hP_pos : 0 < P := by linarith
  have hPd_pos : 0 < P / d := div_pos hP_pos hd_pos
  have hPd_ge16 : 16 ≤ P / d := le_trans hM₀ hd_M0
  have hPd_ge1 : 1 ≤ P / d := by linarith
  by_cases h_empty : ⌊b⌋₊ / d < (⌈a⌉₊ - 1) / d + 1
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.sum_empty, norm_zero]
    positivity
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
        have h5 : ((⌈a⌉₊ - 1) / d) * d ≤ ⌈a⌉₊ - 1 := by
          rw [mul_comm]; exact Nat.div_mul_le_self _ _
        omega
    have hfloor_eq : ⌊b'⌋₊ = ⌊b⌋₊ / d := by
      rw [show b' = (⌊b⌋₊ : ℝ) / (d : ℝ) from rfl, ← Nat.floor_div_eq_div (by positivity) hd_pos,
        Nat.floor_natCast]
    have ha'b' : a' ≤ b' := by
      have h1 : ((⌈a⌉₊ - 1) / d + 1 : ℕ) ≤ ⌊b⌋₊ / d := h_empty
      have h2 : a' ≤ ((⌈a⌉₊ - 1) / d + 1 : ℕ) := by rw [← hceil_eq]; exact Nat.le_ceil a'
      have h3 : ((⌊b⌋₊ / d : ℕ) : ℝ) ≤ b' := by
        rw [← hfloor_eq]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
      exact le_trans h2 (le_trans (by exact_mod_cast h1) h3)
    let wd : ℝ → ℝ := fun t => Real.log t * w (d * t)
    let W₀' : ℝ := W₀ * (Real.log (2 * P) + 1)
    have hW₀' : 0 ≤ W₀' := mul_nonneg hW₀ (by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * P)])
    have hwd_bd : ∀ t ∈ Set.Icc (P / d) (2 * (P / d)), |wd t| ≤ W₀' := by
      intro t ht
      have ht_ge1 : 1 ≤ t := le_trans hPd_ge1 ht.1
      have ht_le : t ≤ 2 * P := le_trans ht.2 (by
        rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)
      have hdt_mem : d * t ∈ Set.Icc P (2 * P) := ⟨by
        calc P = d * (P / d) := by field_simp [hd_pos.ne']
          _ ≤ d * t := mul_le_mul_of_nonneg_left ht.1 hd_pos.le,
        by
        calc d * t ≤ d * (2 * (P / d)) := mul_le_mul_of_nonneg_left ht.2 hd_pos.le
          _ = 2 * P := by field_simp [hd_pos.ne']⟩
      dsimp only [wd]
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg ht_ge1)]
      calc Real.log t * |w (d * t)|
          ≤ Real.log (2 * P) * W₀ := mul_le_mul (Real.log_le_log (by positivity) ht_le) (hw_bd _ hdt_mem) (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ ≤ W₀ * (Real.log (2 * P) + 1) := by linarith
    have hwd_diff : ContDiffOn ℝ 1 wd (Set.Icc (P / d) (2 * (P / d))) := by
      refine ContDiffOn.mul ?_ ?_
      · refine (contDiffOn_iff_contDiffAt.mpr fun t ht => ?_).mono (fun t ht => ?_)
        · exact Real.contDiffAt_log (by linarith [ht])
        · exact lt_of_lt_of_le hPd_pos ht.1
      · refine hw_diff.comp (contDiff_const.mul contDiff_id).contDiffOn fun t ht => ?_
        exact ⟨by calc P = d * (P / d) := by field_simp [hd_pos.ne']
          _ ≤ d * t := mul_le_mul_of_nonneg_left ht.1 hd_pos.le,
          by calc d * t ≤ d * (2 * (P / d)) := mul_le_mul_of_nonneg_left ht.2 hd_pos.le
          _ = 2 * P := by field_simp [hd_pos.ne']⟩
    have hwd_tv : (∫ t in (P / d)..(2 * (P / d)), |deriv wd t|) ≤ W₀' := by
      have hderiv_eq : Set.EqOn (fun t => |deriv wd t|)
          (fun t => |t⁻¹ * w (d * t) + Real.log t * (d * deriv w (d * t))|) (Set.Ioo (P / d) (2 * (P / d))) := by
        intro t ht
        have ht_pos : 0 < t := lt_trans hPd_pos ht.1
        have hlog_da : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht_pos.ne'
        have hw_da : DifferentiableAt ℝ w (d * t) := by
          have hmem : d * t ∈ Set.Ioo P (2 * P) := ⟨by
            calc P = d * (P / d) := by field_simp [hd_pos.ne']
              _ < d * t := mul_lt_mul_of_pos_left ht.1 hd_pos,
            by
            calc d * t < d * (2 * (P / d)) := mul_lt_mul_of_pos_left ht.2 hd_pos
              _ = 2 * P := by field_simp [hd_pos.ne']⟩
          exact (hw_diff.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hmem.1 hmem.2)
        have hcomp_da : HasDerivAt (fun u => w (d * u)) (deriv w (d * t) * d) t :=
          hw_da.hasDerivAt.comp t ((hasDerivAt_id t).const_mul (d : ℝ))
        have hmul_da := hlog_da.mul hcomp_da
        rw [hmul_da.deriv]
        congr 1; ring
      have hint_eq : ∫ t in (P / d)..(2 * (P / d)), |deriv wd t| =
          ∫ t in (P / d)..(2 * (P / d)), |t⁻¹ * w (d * t) + Real.log t * (d * deriv w (d * t))| := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_iff.mpr (MeasureTheory.measure_singleton (2 * (P / d)))] with t ht hmem
        rw [Set.uIoc_of_le (by linarith : P / d ≤ 2 * (P / d))] at hmem
        exact hderiv_eq ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩
      have hint_abs1 : IntervalIntegrable (fun t => W₀ * t⁻¹) MeasureTheory.volume (P / d) (2 * (P / d)) := by
        refine ContinuousOn.intervalIntegrable fun t ht => ?_
        rw [Set.uIcc_of_le (by linarith : P / d ≤ 2 * (P / d))] at ht
        exact (continuousOn_const.mul (continuousOn_inv₀.mono fun u hu => by
          intro h0; subst h0; linarith [ht.1])).continuousWithinAt
      have hw'_int : IntervalIntegrable (fun u => |deriv w u|) MeasureTheory.volume P (2 * P) :=
        (hw_diff.continuousOn_deriv (uniqueDiffOn_Icc (by linarith : P < 2 * P)) le_rfl).abs.intervalIntegrable
      have hw'_mul_int : IntervalIntegrable (fun t => |deriv w ((d : ℝ) * t)|)
          MeasureTheory.volume (P / d) (2 * (P / d)) := by
        have h1 := hw'_int
        rw [show P = (d : ℝ) * (P / d) by field_simp [hd_pos.ne'],
          show 2 * P = (d : ℝ) * (2 * (P / d)) by field_simp [hd_pos.ne']] at h1
        exact h1.comp_mul_left (d : ℝ)
      have hint_abs2 : IntervalIntegrable (fun t => Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|))
          MeasureTheory.volume (P / d) (2 * (P / d)) :=
        (hw'_mul_int.const_mul (d : ℝ)).const_mul (Real.log (2 * P))
      have hint_wd : IntervalIntegrable (fun t => |deriv wd t|) MeasureTheory.volume (P / d) (2 * (P / d)) :=
        (hwd_diff.continuousOn_deriv (uniqueDiffOn_Icc (by linarith : P / d < 2 * (P / d))) le_rfl).abs.intervalIntegrable
      have hmono : ∫ t in (P / d)..(2 * (P / d)), |deriv wd t| ≤
          ∫ t in (P / d)..(2 * (P / d)), (W₀ * t⁻¹ + Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|)) := by
        refine intervalIntegral.integral_mono_ae_restrict (by linarith) hint_wd (hint_abs1.add hint_abs2) ?_
        filter_upwards [MeasureTheory.ae_iff.mpr (MeasureTheory.measure_singleton (2 * (P / d)))] with t ht hmem
        have ht_oo : t ∈ Set.Ioo (P / d) (2 * (P / d)) :=
          ⟨(Set.Ioc_subset_Icc_self hmem).1, lt_of_le_of_ne hmem.2 ht⟩
        rw [hderiv_eq t ht_oo]
        have ht_ge1 : 1 ≤ t := le_trans hPd_ge1 ht_oo.1.le
        have ht_le : t ≤ 2 * P := le_trans ht_oo.2.le (by
          rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)
        have hdt_mem : d * t ∈ Set.Icc P (2 * P) := ⟨by
          calc P = d * (P / d) := by field_simp [hd_pos.ne']
            _ ≤ d * t := mul_le_mul_of_nonneg_left ht_oo.1.le hd_pos.le,
          by
          calc d * t ≤ d * (2 * (P / d)) := mul_le_mul_of_nonneg_left ht_oo.2.le hd_pos.le
            _ = 2 * P := by field_simp [hd_pos.ne']⟩
        calc |t⁻¹ * w (d * t) + Real.log t * (d * deriv w (d * t))|
            ≤ |t⁻¹ * w (d * t)| + |Real.log t * (d * deriv w (d * t))| := abs_add_le _ _
          _ ≤ W₀ * t⁻¹ + Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|) := by
              refine add_le_add ?_ ?_
              · rw [abs_mul, abs_of_pos (inv_pos.mpr (lt_trans hPd_pos ht_oo.1)), mul_comm]
                exact mul_le_mul_of_nonneg_right (hw_bd _ hdt_mem) (by positivity)
              · rw [abs_mul, abs_of_nonneg (Real.log_nonneg ht_ge1), abs_mul, abs_of_pos hd_pos]
                exact mul_le_mul (Real.log_le_log (by positivity) ht_le) le_rfl (by positivity)
                  (Real.log_nonneg (by linarith))
      have hint1_val : ∫ t in (P / d)..(2 * (P / d)), W₀ * t⁻¹ ≤ W₀ := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_of_pos hPd_pos (by linarith : 0 < 2 * (P / d)),
          show (2 * (P / d)) / (P / d) = 2 by field_simp [hPd_pos.ne', hd_pos.ne']]
        have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        exact mul_le_of_le_one_right hW₀ hlog2
      have hint2_val : ∫ t in (P / d)..(2 * (P / d)), Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|) ≤
          W₀ * Real.log (2 * P) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have hcomp : ∫ t in (P / d)..(2 * (P / d)), |deriv w (d * t)| =
            (d : ℝ)⁻¹ * ∫ u in P..(2 * P), |deriv w u| := by
          have h := intervalIntegral.integral_comp_mul_left (fun u => |deriv w u|) (c := (d : ℝ))
            (a := P / d) (b := 2 * (P / d))
          rw [show (d : ℝ) * (P / d) = P by field_simp [hd_pos.ne'],
            show (d : ℝ) * (2 * (P / d)) = 2 * P by field_simp [hd_pos.ne'], smul_eq_mul] at h
          exact h
        rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hd_pos.ne', one_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hw_tv (Real.log_nonneg (by linarith))
      rw [intervalIntegral.integral_add hint_abs1 hint_abs2] at hmono
      linarith
    set E : ℝ := max C_exp 3 *
      ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := by positivity
    have hsum_bd : ∀ u : ℕ, ⌈a'⌉₊ ≤ u → u ≤ ⌊b'⌋₊ →
        ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤ E := by
      intro u hau hub
      have hu_ge : P / d ≤ (u : ℝ) := by
        have h1 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        exact le_trans hPa' (le_trans h1 (by exact_mod_cast hau))
      have hu_le : (u : ℝ) ≤ 2 * (P / d) := by
        have h1 : (⌊b'⌋₊ : ℝ) ≤ b' := Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
        exact le_trans (by exact_mod_cast hub) (le_trans h1 hb'2P)
      have h_eq_phase : ∀ k : ℕ, 1 ≤ k →
          ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
          ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
        intro k hk
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Nat.cast_mul, mul_pow, zpow_neg, zpow_natCast]
        ring
      have hsum_eq : ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
          ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
            ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
        refine Finset.sum_congr rfl fun k hk => h_eq_phase k (by
          have h1 : (1 : ℝ) ≤ a' := le_trans hPd_ge1 hPa'
          have h2 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (by linarith)
          exact le_trans h2 (Finset.mem_Icc.mp hk).1)
      rw [hsum_eq]
      let cd : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)
      have hcd0 : cd r₀ ≠ 0 := by
        dsimp only [cd]
        have hn_pos : (0 : ℝ) < n := by
          by_contra h0
          have : n = 0 := by exact_mod_cast le_antisymm (not_lt.mp h0) (Nat.cast_nonneg n)
          subst this; linarith
        have hh0R : (h r₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hh₀
        positivity
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
          exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) (by linarith [hu_le]) r₀)
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
        have h2 : (P / d) ^ (-(r₀ : ℤ)) ≤ (2 : ℝ) ^ R * (2 * P / d) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, show 2 * P / d = 2 * (P / d) by ring,
            mul_pow, mul_inv, mul_comm ((2 : ℝ) ^ r₀)⁻¹ _, ← mul_assoc]
          have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
          rw [inv_mul_le_iff₀ (by positivity)]
          calc (P / d) ^ r₀ * (2 : ℝ) ^ r₀ ≤ (P / d) ^ r₀ * (2 : ℝ) ^ R :=
                mul_le_mul_of_nonneg_left h2r (by positivity)
            _ = (2 : ℝ) ^ R * (P / d) ^ r₀ := mul_comm _ _
        have h3 : (P / d) ^ (K_max - 1) ≤ (u : ℝ) ^ (K_max - 1) :=
          pow_le_pow_left₀ hPd_pos.le hu_ge _
        calc |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))
            ≤ |cd r₀| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (P / d) ^ (K_max - 1) := hT_ub
          _ ≤ (u : ℝ) ^ (K_max - 1) := h3
      have hhexp := hexp A r₀ hr₀ hA cd hcd0 a' (u : ℝ) hM0_a' ha'u hu2a' hdom_u hTu_ub
      rw [Nat.floor_natCast] at hhexp
      have hT_ge : (2 : ℝ) ^ (-(R : ℤ) - 1) * T₀ ≤ |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
        dsimp only [cd, T₀]
        have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
        have hupow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) (by linarith [hu_le]) r₀)
        have h2pow : (2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ)) ≤ (2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ)) := by
          rw [show (2 * P / d) = (2 * P) / d by ring, zpow_neg, zpow_natCast, div_pow, inv_div]
          rw [zpow_neg, zpow_natCast, zpow_sub₀ (by norm_num), zpow_neg, zpow_natCast, zpow_one]
          rw [mul_pow, ← div_eq_mul_inv]
          field_simp [hd_pos.ne', hP_pos.ne']
          have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
          linarith [h2r]
        calc (2 : ℝ) ^ (-(R : ℤ) - 1) * (|(h r₀ : ℝ)| * n / P ^ r₀)
            = |(h r₀ : ℝ)| * n * ((2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ))) := by
                rw [zpow_neg, zpow_natCast]; ring
          _ ≤ |(h r₀ : ℝ)| * n * ((2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                mul_le_mul_of_nonneg_left h2pow (by positivity)
          _ ≤ |(h r₀ : ℝ) * n / (2 * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
                rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n),
                  abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ r₀)]
                have hle1 : |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) ≤
                    |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left hr0_1 (by positivity)) hupow (by positivity) (by positivity)
                linarith [show |(h r₀ : ℝ)| * n * ((2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) =
                  |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) by ring]
      refine le_trans hhexp ?_
      refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (by positivity)
      refine add_le_add ?_ ?_
      · exact div_le_div₀ (by positivity) (by linarith [hu_le]) (by positivity) (max_le_max hT_ge le_rfl)
      · refine Real.rpow_le_rpow (by positivity) (by linarith [hu_le]) (by linarith)
    have hps := partial_summation_Icc (P := P / d) (a := a') (b := b') (W₀ := W₀') (E := E)
      hPd_pos hPa' ha'b' hb'2P hW₀' hE_nn hwd_bd hwd_diff hwd_tv hsum_bd
    rw [hceil_eq, hfloor_eq] at hps
    calc ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
            (Real.log k * w (d * k) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖
        ≤ 2 * W₀' * E := by simpa [wd] using hps
      _ = 2 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          dsimp only [W₀', E]; ring
      _ ≤ 4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          have hnn : 0 ≤ W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
              ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by positivity
          linarith

lemma sum_vonMangoldt_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt k : ℝ) ≤ (Real.log 4 + 4) * (X : ℝ) := by
  by_cases hX4 : X < 4
  · have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 3 := fun k hk =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, by have := (Finset.mem_Icc.mp hk).2; omega⟩
    have hterm : ∀ k ∈ Finset.Icc 1 3, (ArithmeticFunction.vonMangoldt k : ℝ) ≤ Real.log 3 := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk3 : k ≤ 3 := (Finset.mem_Icc.mp hk).2
      exact le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hk3))
    have hsum3 : ∑ k ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt k : ℝ) ≤ 3 * Real.log 3 := by
      calc ∑ k ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt k : ℝ)
          ≤ ∑ k ∈ Finset.Icc 1 3, (ArithmeticFunction.vonMangoldt k : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        _ ≤ ∑ _k ∈ Finset.Icc 1 3, Real.log 3 := Finset.sum_le_sum hterm
        _ = 3 * Real.log 3 := by simp
    have hlog3 : Real.log 3 ≤ 4 / 3 := by
      have h2 : Real.log (3 / 2 : ℝ) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at h2
      linarith [Real.log_two_lt_d9]
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  · push_neg at hX4
    have hdiff := sum_vonMangoldt_sub_prime_log_le (A₀ := 1) (B₀ := X) le_rfl hX4 (g := fun _ => 1) (fun _ => by simp)
    simp only [mul_one, ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hdiff
    have h1 : ∑ k ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt k : ℝ) -
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, Real.log p ≤
        2 * Real.sqrt X * (Real.log X) ^ 2 := le_trans (le_abs_self _) hdiff
    have htheta : ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, Real.log p ≤ Real.log 4 * (X : ℝ) := by
      have heq : ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, Real.log p = Chebyshev.theta (X : ℝ) := by
        unfold Chebyshev.theta
        rw [Nat.floor_natCast]
        congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        exact ⟨fun ⟨⟨hp1, hpX⟩, hp⟩ => ⟨⟨hp.pos, hpX⟩, hp⟩, fun ⟨⟨hp0, hpX⟩, hp⟩ => ⟨⟨hp.pos, hpX⟩, hp⟩⟩
      rw [heq]
      exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg X)
    have hsqrt : 2 * Real.sqrt X * (Real.log X) ^ 2 ≤ 4 * (X : ℝ) := by
      have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX
      have hr4 : 0 < (X : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hX_pos _
      have hlog4 : Real.log ((X : ℝ) ^ (1 / 4 : ℝ)) ≤ (X : ℝ) ^ (1 / 4 : ℝ) / Real.exp 1 := by
        have h_u := Real.log_le_sub_one_of_pos (div_pos hr4 (Real.exp_pos 1))
        rw [Real.log_div hr4.ne' (Real.exp_pos 1).ne', Real.log_exp] at h_u
        linarith
      rw [Real.log_rpow hX_pos] at hlog4
      have hlog_le : Real.log X ≤ (4 / Real.exp 1) * (X : ℝ) ^ (1 / 4 : ℝ) := by linarith
      have hlog_nn : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
      have hsq : (Real.log X) ^ 2 ≤ (4 / Real.exp 1) ^ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
        calc (Real.log X) ^ 2 ≤ ((4 / Real.exp 1) * (X : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ hlog_nn hlog_le 2
          _ = (4 / Real.exp 1) ^ 2 * ((X : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := mul_pow _ _ 2
          _ = (4 / Real.exp 1) ^ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_natCast ((X : ℝ) ^ _), ← Real.rpow_mul hX_pos.le]; norm_num
      have he_sq : (4 / Real.exp 1) ^ 2 ≤ 2 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        have : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        nlinarith
      rw [Real.sqrt_eq_rpow]
      calc 2 * (X : ℝ) ^ (1 / 2 : ℝ) * (Real.log X) ^ 2
          ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) * (2 * (X : ℝ) ^ (1 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (le_trans hsq (mul_le_mul_of_nonneg_right he_sq (by positivity))) (by positivity)
        _ = 4 * ((X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = 4 * (X : ℝ) := by rw [← Real.rpow_add hX_pos]; norm_num
    linarith

end BrocardFormalization

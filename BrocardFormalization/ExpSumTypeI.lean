/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.ExpSumVaughan

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

lemma norm_ePhase (x : ℝ) : ‖ePhase x‖ = 1 := by
  unfold ePhase
  rw [show (2 * Real.pi * Complex.I * (x : ℂ)) = (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

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
    rw [dif_pos hmem] at hle
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
      simp [norm_ePhase]
    have hcard : ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) ≤ M₂ - M₁ + 2 := by
      rw [Nat.card_Icc]
      by_cases hle : ⌈M₁⌉₊ ≤ ⌊M₂⌋₊ + 1
      · rw [Nat.cast_sub hle]
        have h1 : (⌊M₂⌋₊ : ℝ) ≤ M₂ := Nat.floor_le hM₂_pos.le
        have h2 : M₁ ≤ (⌈M₁⌉₊ : ℝ) := Nat.le_ceil M₁
        push_cast; linarith
      · have hle' : ⌊M₂⌋₊ + 1 ≤ ⌈M₁⌉₊ := by omega
        rw [Nat.sub_eq_zero_of_le hle']; push_cast; linarith
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
  · have hL_small' : M₂ ^ (3 / 4 : ℝ) ≤ M₂ - M₁ := not_lt.mp hL_small
    set L : ℝ := M₂ - M₁
    have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_small'
    have hL_ge1 : 1 ≤ L := by
      have : (1 : ℝ) ≤ M₂ ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      linarith
    have hL_le_M2 : L ≤ M₂ := by linarith
    have hT_pos : 0 < T := by dsimp only [T]; positivity
    by_cases hT_small : T ≤ M₂ / (6 * (2 : ℝ) ^ R)
    · have h1 := laurent_sum_dom_bounds A R 1 hA r₀ hr₀ c hc₀ (by omega) M₁ M₂ hM₁_pos hM₁₂ hM₂
        (hdom 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
      set lam1 := (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + 1 - 1) 1 : ℝ) * M₂ ^ (-((r₀ : ℤ) + ((1 : ℕ) : ℤ)))
      have hlam1_eq : lam1 = T / (2 * M₂) := by
        dsimp only [lam1, T]
        rw [show r₀ + 1 - 1 = r₀ by omega, Nat.descFactorial_one,
          show -((r₀ : ℤ) + ((1 : ℕ) : ℤ)) = -(r₀ : ℤ) + (-1 : ℤ) by omega, zpow_add₀ hM₂_pos.ne', zpow_neg_one]
        ring
      have hmono : MonotoneOn (deriv G) (Set.Icc M₁ M₂) ∨ AntitoneOn (deriv G) (Set.Icc M₁ M₂) :=
        laurent_sum_deriv_mono_or_anti A R hA r₀ hr₀ c hc₀ M₁ M₂ hM₁_pos hM₁₂ hM₂
          (hdom 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      have hbd1 : ∀ t ∈ Set.Icc M₁ M₂, lam1 ≤ |deriv G t| ∧ |deriv G t| ≤ 1 / 2 := by
        intro t ht
        have ht1 := h1.2 t ht
        rw [iteratedDeriv_one] at ht1
        refine ⟨ht1.1, le_trans ht1.2 ?_⟩
        change 3 * (2 : ℝ) ^ (R + 1) * lam1 ≤ 1 / 2
        rw [hlam1_eq, pow_succ]
        rw [show 3 * ((2 : ℝ) ^ R * 2) * (T / (2 * M₂)) = 3 * (2 : ℝ) ^ R * (T / M₂) by ring]
        rw [mul_div_assoc', div_le_iff₀ hM₂_pos]
        rw [le_div_iff₀ (by positivity)] at hT_small
        linarith
      have hkl := hKL M₁ M₂ lam1 G hM₁_pos.le hM₁₂ h1.1 hmono hbd1
      by_cases hT1 : 1 ≤ T
      · have hmax : max T 1 = T := max_eq_left hT1
        calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
            ≤ C_KL / lam1 := hkl
          _ = 2 * C_KL * (M₂ / T) := by rw [hlam1_eq, div_div_eq_mul_div]; ring
          _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) := by
              rw [hmax]
              have hC : 4 * C_KL ≤ C_exp := le_max_left _ _
              have hnn1 : 0 ≤ M₂ / T := by positivity
              have hnn2 : 0 ≤ M₂ ^ (1 - η_exp) := by positivity
              nlinarith
      · have hT1' : T ≤ 1 := le_of_not_ge hT1
        have hmax : max T 1 = 1 := max_eq_right hT1'
        have htriv : ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖ ≤
            ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          simp [norm_ePhase]
        have hcard : ((Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊).card : ℝ) ≤ M₂ - M₁ + 2 := by
          rw [Nat.card_Icc]
          by_cases hle : ⌈M₁⌉₊ ≤ ⌊M₂⌋₊ + 1
          · rw [Nat.cast_sub hle]
            have h1 : (⌊M₂⌋₊ : ℝ) ≤ M₂ := Nat.floor_le hM₂_pos.le
            have h2 : M₁ ≤ (⌈M₁⌉₊ : ℝ) := Nat.le_ceil M₁
            push_cast; linarith
          · have hle' : ⌊M₂⌋₊ + 1 ≤ ⌈M₁⌉₊ := by omega
            rw [Nat.sub_eq_zero_of_le hle']; push_cast; linarith
        calc ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (G m)‖
            ≤ M₂ - M₁ + 2 := le_trans htriv hcard
          _ ≤ 2 * M₂ := by linarith
          _ ≤ C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)) := by
              rw [hmax, div_one]
              have hC4 : (4 : ℝ) ≤ C_exp := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
              have hnn2 : 0 ≤ M₂ ^ (1 - η_exp) := by positivity
              nlinarith
    · have hT_small' : M₂ / (6 * (2 : ℝ) ^ R) ≤ T := le_of_not_ge hT_small
      by_cases hT_vd2 : T ≤ M₂ ^ (3 / 2 : ℝ)
      · have h2 := laurent_sum_dom_bounds A R 2 hA r₀ hr₀ c hc₀ (by omega) M₁ M₂ hM₁_pos hM₁₂ hM₂
          (hdom 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        set lam2 := (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + 2 - 1) 2 : ℝ) * M₂ ^ (-((r₀ : ℤ) + ((2 : ℕ) : ℤ)))
        have hlam2_eq : lam2 = ((r₀ + 1 : ℝ) / 2) * (T / M₂ ^ 2) := by
          dsimp only [lam2, T]
          have hdesc2 : Nat.descFactorial (r₀ + 2 - 1) 2 = (r₀ + 1) * r₀ := by
            rw [show r₀ + 2 - 1 = r₀ + 1 by omega, Nat.succ_descFactorial_succ, Nat.descFactorial_one]
          rw [hdesc2, show -((r₀ : ℤ) + ((2 : ℕ) : ℤ)) = -(r₀ : ℤ) + (-2 : ℤ) by omega,
            zpow_add₀ hM₂_pos.ne', show M₂ ^ (-2 : ℤ) = (M₂ ^ 2)⁻¹ by rw [zpow_neg]]
          push_cast; ring
        have hlam2_ge : T / (2 * M₂ ^ 2) ≤ lam2 := by
          rw [hlam2_eq, show T / (2 * M₂ ^ 2) = (1 / 2 : ℝ) * (T / M₂ ^ 2) by ring]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (1 : ℝ) ≤ r₀ + 1 := by exact_mod_cast (by omega : 1 ≤ r₀ + 1)
          linarith
        have hlam2_le : lam2 ≤ (R + 1 : ℝ) * (T / M₂ ^ 2) := by
          rw [hlam2_eq]
          have : (r₀ + 1 : ℝ) / 2 ≤ R + 1 := by
            have : (r₀ : ℝ) ≤ R := by exact_mod_cast hr₀_R
            linarith
          exact mul_le_mul_of_nonneg_right this (div_nonneg hT_pos.le (pow_nonneg hM₂_pos.le 2))
        have hvd := hvd2_bd M₁ M₂ lam2 G hM₁_pos.le hL_ge1 h2.1 (fun t ht => h2.2 t ht)
        have hpow2 : (2 ^ 2 - 2 : ℕ) = 2 := by norm_num
        have hz2 : (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
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
              le_trans (div_le_div_of_nonneg_right hT_small' (by positivity)) hlam2_ge
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
      · have hT_vd2' : M₂ ^ (3 / 2 : ℝ) ≤ T := le_of_not_ge hT_vd2
        let lam_fn : ℕ → ℝ := fun j =>
          (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + j - 1) j : ℝ) * M₂ ^ (-((r₀ : ℤ) + (j : ℤ)))
        have hlam_K : lam_fn K_max ≤ L ^ (-(1 / 2 : ℝ)) := by
          dsimp only [lam_fn]
          have hdesc_le : (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) ≤ K_fact * (r₀ : ℝ) := by
            have h1 : Nat.descFactorial (r₀ + K_max - 1) K_max ≤ (R + K_max).factorial :=
              le_trans (Nat.descFactorial_le_factorial _ _) (Nat.factorial_le (by omega))
            have h1R : (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) ≤ K_fact := by
              dsimp only [K_fact]; exact_mod_cast h1
            have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast hr₀_1
            nlinarith
          have hlam_ub : (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) * M₂ ^ (-((r₀ : ℤ) + (K_max : ℤ))) ≤
              K_fact * (T / M₂ ^ K_max) := by
            have hz : M₂ ^ (-((r₀ : ℤ) + (K_max : ℤ))) = M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max := by
              rw [show -((r₀ : ℤ) + (K_max : ℤ)) = -(r₀ : ℤ) + -(K_max : ℤ) by omega,
                zpow_add₀ hM₂_pos.ne', zpow_neg M₂ (K_max : ℤ), zpow_natCast M₂ K_max, div_eq_mul_inv]
            rw [hz]
            have hstep : (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max) ≤
                (1 : ℝ) * |c r₀| * (K_fact * (r₀ : ℝ)) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              refine mul_le_mul ?_ hdesc_le (by positivity) (by positivity)
              linarith [abs_nonneg (c r₀)]
            calc (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + K_max - 1) K_max : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max)
                ≤ (1 : ℝ) * |c r₀| * (K_fact * (r₀ : ℝ)) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ K_max) := hstep
              _ = K_fact * (T / M₂ ^ K_max) := by dsimp only [T]; ring
          have hT_div : T / M₂ ^ K_max ≤ M₂ ^ (-(1 : ℝ)) := by
            rw [div_le_iff₀ (by positivity)]
            have hpow_eq : M₂ ^ (-(1 : ℝ)) * M₂ ^ K_max = M₂ ^ (K_max - 1) := by
              have hK1 : M₂ ^ K_max = M₂ * M₂ ^ (K_max - 1) := by
                conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ K_max), pow_succ']
              rw [Real.rpow_neg_one, hK1, inv_mul_cancel_left₀ hM₂_pos.ne']
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
            Real.rpow_le_rpow_of_nonpos hL_pos hL_le_M2 (by norm_num)
          exact le_trans hlam_ub (le_trans (mul_le_mul_of_nonneg_left hT_div (by positivity)) (le_trans hK_le hM_L))
        let S_j := (Finset.Icc 3 K_max).filter (fun j => lam_fn j ≤ L ^ (-(1 / 2 : ℝ)))
        have hS_ne : S_j.Nonempty := ⟨K_max, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hK_max, le_rfl⟩, hlam_K⟩⟩
        set j₀ := S_j.min' hS_ne
        have hj₀_mem : j₀ ∈ Finset.Icc 3 K_max := (Finset.mem_filter.mp (Finset.min'_mem S_j hS_ne)).1
        have hj₀_le : lam_fn j₀ ≤ L ^ (-(1 / 2 : ℝ)) := (Finset.mem_filter.mp (Finset.min'_mem S_j hS_ne)).2
        have hj₀_3 : 3 ≤ j₀ := (Finset.mem_Icc.mp hj₀_mem).1
        have hj₀_ge : L ^ (-(5 / 2 : ℝ)) ≤ lam_fn j₀ := by
          by_cases h3 : j₀ = 3
          · rw [h3]
            have hlam3 : T / (2 * M₂ ^ 3) ≤ lam_fn 3 := by
              dsimp only [lam_fn, T]
              have hdesc3 : (r₀ : ℝ) ≤ (Nat.descFactorial (r₀ + 3 - 1) 3 : ℝ) := by
                have : r₀ ≤ Nat.descFactorial (r₀ + 3 - 1) 3 := by
                  rw [show r₀ + 3 - 1 = r₀ + 2 by omega, Nat.descFactorial_succ, Nat.descFactorial_succ,
                    Nat.descFactorial_one]
                  nlinarith
                exact_mod_cast this
              have hz : M₂ ^ (-((r₀ : ℤ) + ((3 : ℕ) : ℤ))) = M₂ ^ (-(r₀ : ℤ)) / M₂ ^ 3 := by
                rw [show -((r₀ : ℤ) + ((3 : ℕ) : ℤ)) = -(r₀ : ℤ) + -(3 : ℤ) by omega,
                  zpow_add₀ hM₂_pos.ne', zpow_neg M₂ (3 : ℤ), zpow_natCast M₂ 3, div_eq_mul_inv]
              rw [hz]
              have : (1 / 2 : ℝ) * |c r₀| * (r₀ : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ 3) ≤
                  (1 / 2 : ℝ) * |c r₀| * (Nat.descFactorial (r₀ + 3 - 1) 3 : ℝ) * (M₂ ^ (-(r₀ : ℤ)) / M₂ ^ 3) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdesc3 (by positivity)) (by positivity)
              linarith
            have hT_bd : M₂ ^ (-(3 / 2 : ℝ)) / 2 ≤ T / (2 * M₂ ^ 3) := by
              have h1 : M₂ ^ (3 / 2 : ℝ) / (2 * M₂ ^ 3) ≤ T / (2 * M₂ ^ 3) :=
                div_le_div_of_nonneg_right hT_vd2' (by positivity)
              have h2 : M₂ ^ (3 / 2 : ℝ) / (2 * M₂ ^ 3) = M₂ ^ (-(3 / 2 : ℝ)) / 2 := by
                rw [div_mul_eq_div_div, ← Real.rpow_natCast M₂ 3, ← Real.rpow_sub hM₂_pos]
                norm_num; ring
              linarith
            have hL_bd : L ^ (-(5 / 2 : ℝ)) ≤ M₂ ^ (-(3 / 2 : ℝ)) / 2 := by
              have h1 : L ^ (-(5 / 2 : ℝ)) ≤ (M₂ ^ (3 / 4 : ℝ)) ^ (-(5 / 2 : ℝ)) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hL_small' (by norm_num)
              rw [← Real.rpow_mul hM₂_pos.le] at h1
              have h2 : (M₂ ^ ((3 / 4 : ℝ) * -(5 / 2 : ℝ))) * 2 ≤ M₂ ^ (-(3 / 2 : ℝ)) := by
                have hM2_16 : (2 : ℝ) ≤ M₂ ^ (3 / 8 : ℝ) := by
                  have h16 : (2 : ℝ) ≤ (16 : ℝ) ^ (3 / 8 : ℝ) := by
                    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
                    norm_num
                    exact le_trans (by norm_num : (2 : ℝ) ≤ 2 ^ (1 : ℝ))
                      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
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
            have hj1_gt : L ^ (-(1 / 2 : ℝ)) ≤ lam_fn (j₀ - 1) := le_of_not_ge hj1_not
            have hratio : lam_fn (j₀ - 1) / M₂ ≤ lam_fn j₀ := by
              dsimp only [lam_fn]
              have hdesc : (Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) : ℝ) ≤
                  (Nat.descFactorial (r₀ + j₀ - 1) j₀ : ℝ) := by
                have h1 : Nat.descFactorial (r₀ + j₀ - 1) j₀ =
                    (r₀ + j₀ - 1) * Nat.descFactorial (r₀ + (j₀ - 1) - 1) (j₀ - 1) := by
                  conv_lhs => rw [show r₀ + j₀ - 1 = (r₀ + (j₀ - 1) - 1) + 1 by omega,
                    show j₀ = (j₀ - 1) + 1 by omega]
                  rw [Nat.succ_descFactorial_succ]
                rw [h1]
                exact_mod_cast Nat.le_mul_of_pos_left _ (by omega : 0 < r₀ + j₀ - 1)
              have hz : M₂ ^ (-((r₀ : ℤ) + (j₀ : ℤ))) = M₂ ^ (-((r₀ : ℤ) + ((j₀ - 1 : ℕ) : ℤ))) / M₂ := by
                rw [show -((r₀ : ℤ) + (j₀ : ℤ)) = -((r₀ : ℤ) + ((j₀ - 1 : ℕ) : ℤ)) + (-1 : ℤ) by omega,
                  zpow_add₀ hM₂_pos.ne', zpow_neg_one, div_eq_mul_inv]
              rw [hz, mul_div_assoc']
              refine div_le_div_of_nonneg_right ?_ hM₂_pos.le
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdesc (by positivity)) (by positivity)
            have hL_M2 : L ^ (-(5 / 2 : ℝ)) ≤ L ^ (-(1 / 2 : ℝ)) / M₂ := by
              have hM2_L : M₂ ≤ L ^ (4 / 3 : ℝ) := by
                have h1 := Real.rpow_le_rpow (by positivity) hL_small' (by norm_num : (0 : ℝ) ≤ 4 / 3)
                rw [← Real.rpow_mul hM₂_pos.le] at h1
                norm_num at h1; exact h1
              calc L ^ (-(5 / 2 : ℝ))
                  ≤ L ^ (-(11 / 6 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL_ge1 (by norm_num)
                _ = L ^ (-(1 / 2 : ℝ)) / L ^ (4 / 3 : ℝ) := by
                    rw [← Real.rpow_sub hL_pos]; norm_num
                _ ≤ L ^ (-(1 / 2 : ℝ)) / M₂ :=
                    div_le_div_of_nonneg_left (by positivity) hM₂_pos hM2_L
            exact le_trans hL_M2 (le_trans (div_le_div_of_nonneg_right hj1_gt hM₂_pos.le) hratio)
        have hj₀_dom := laurent_sum_dom_bounds A R j₀ hA r₀ hr₀ c hc₀ (by omega) M₁ M₂ hM₁_pos hM₁₂ hM₂
          (hdom j₀ (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hj₀_mem).2⟩))
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
            rw [dif_pos hj₀_mem] at hle
            exact hle
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

end BrocardFormalization

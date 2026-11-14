/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.PellChebyshev

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

theorem theorem_1_1 :
    (∀ (h4 : IsBrocardSol 4 5), pellIndex (by omega) h4 = 1) ∧
    (∀ (h5 : IsBrocardSol 5 11), pellIndex (by omega) h5 = 1) ∧
    (∀ (h7 : IsBrocardSol 7 71), pellIndex (by omega) h7 = 2) ∧
    (∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn8 : 8 ≤ n) → (hN : N₀ ≤ n) → (hsol : IsBrocardSol n m) →
      pellIndex (by omega) hsol = 1 ∨ pellIndex (by omega) hsol = 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn8 : 8 ≤ n) → (hN : N₀ ≤ n) → (hsol : IsBrocardSol n m) →
      ∀ (hn : 3 ≤ n) (hn6 : n ≠ 6),
        |Real.log (epsReal n hn hn6) / ((n : ℝ) * Real.log n) -
          1 / (2 * (pellIndex (by omega) hsol : ℝ))| ≤ C / Real.log n) ∧
    (∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n₁ n₂ m₁ m₂ : ℕ, 4 ≤ n₁ → (n₁ ≤ 10 ^ 9 ∨ N₀ ≤ n₁) → n₁ < n₂ →
      IsBrocardSol n₁ m₁ → IsBrocardSol n₂ m₂ → qn n₁ ≠ qn n₂) := by
  have h4_eq : ∀ (h4 : IsBrocardSol 4 5), pellIndex (by omega) h4 = 1 := by
    intro h4
    obtain ⟨hn6, hk1, _, hsny⟩ := pellIndex_spec (by omega : 4 ≤ 4) h4
    set k := pellIndex (by omega : 4 ≤ 4) h4
    have hqn4 : qn 4 = 6 := by rw [← qnFast_eq_qn 4]; decide
    have hsn4 : sn 4 = 2 := by
      have hfac := factorial_eq_qn_mul_sn_sq 4
      rw [hqn4, show Nat.factorial 4 = 24 by decide] at hfac
      nlinarith [sn_pos 4]
    have hYr_k : Yr 4 (by omega) hn6 k = 2 := by
      have : (Yr 4 (by omega) hn6 k : ℤ) = (sn 4 : ℤ) := by rw [Yr_eq, ← hsny]
      have : Yr 4 (by omega) hn6 k = sn 4 := by exact_mod_cast this
      omega
    have hYr2 : 4 ≤ Yr 4 (by omega) hn6 2 := by
      have h2 := (lemma_3_2_i 4 (by omega) hn6 2 (by norm_num)).2.1
      have hU : (Polynomial.Chebyshev.U ℤ ((2 : ℕ) - 1)).eval (X1 4 (by omega) hn6 : ℤ) =
          2 * (X1 4 (by omega) hn6 : ℤ) := by
        simp [Polynomial.Chebyshev.U_one]
      rw [hU] at h2
      have hX2 : 2 ≤ X1 4 (by omega) hn6 := by
        have := (pellFundUnit_isFundamental (by omega : 3 ≤ 4) hn6).one_lt_x
        have := X1_eq (by omega : 3 ≤ 4) hn6
        omega
      have hY1 : 1 ≤ Y1 4 (by omega) hn6 := Y1_pos (by omega) hn6
      have hZ : (4 : ℤ) ≤ (Yr 4 (by omega) hn6 2 : ℤ) := by
        rw [h2]; nlinarith
      exact_mod_cast hZ
    have hk_lt2 : k < 2 := by
      by_contra hge
      have := (Yr_strictMono (by omega : 3 ≤ 4) hn6).monotone (by omega : 2 ≤ k)
      omega
    omega
  have h5_eq : ∀ (h5 : IsBrocardSol 5 11), pellIndex (by omega) h5 = 1 := by
    intro h5
    obtain ⟨hn6, hk1, _, hsny⟩ := pellIndex_spec (by omega : 4 ≤ 5) h5
    set k := pellIndex (by omega : 4 ≤ 5) h5
    have hqn5 : qn 5 = 30 := by rw [← qnFast_eq_qn 5]; decide
    have hsn5 : sn 5 = 2 := by
      have hfac := factorial_eq_qn_mul_sn_sq 5
      rw [hqn5, show Nat.factorial 5 = 120 by decide] at hfac
      nlinarith [sn_pos 5]
    have hYr_k : Yr 5 (by omega) hn6 k = 2 := by
      have : (Yr 5 (by omega) hn6 k : ℤ) = (sn 5 : ℤ) := by rw [Yr_eq, ← hsny]
      have : Yr 5 (by omega) hn6 k = sn 5 := by exact_mod_cast this
      omega
    have hYr2 : 4 ≤ Yr 5 (by omega) hn6 2 := by
      have h2 := (lemma_3_2_i 5 (by omega) hn6 2 (by norm_num)).2.1
      have hU : (Polynomial.Chebyshev.U ℤ ((2 : ℕ) - 1)).eval (X1 5 (by omega) hn6 : ℤ) =
          2 * (X1 5 (by omega) hn6 : ℤ) := by
        simp [Polynomial.Chebyshev.U_one]
      rw [hU] at h2
      have hX2 : 2 ≤ X1 5 (by omega) hn6 := by
        have := (pellFundUnit_isFundamental (by omega : 3 ≤ 5) hn6).one_lt_x
        have := X1_eq (by omega : 3 ≤ 5) hn6
        omega
      have hY1 : 1 ≤ Y1 5 (by omega) hn6 := Y1_pos (by omega) hn6
      have hZ : (4 : ℤ) ≤ (Yr 5 (by omega) hn6 2 : ℤ) := by
        rw [h2]; nlinarith
      exact_mod_cast hZ
    have hk_lt2 : k < 2 := by
      by_contra hge
      have := (Yr_strictMono (by omega : 3 ≤ 5) hn6).monotone (by omega : 2 ≤ k)
      omega
    omega
  have h7_eq : ∀ (h7 : IsBrocardSol 7 71), pellIndex (by omega) h7 = 2 := by
    intro h7
    obtain ⟨hn6, hk1, _, hsny⟩ := pellIndex_spec (by omega : 4 ≤ 7) h7
    set k := pellIndex (by omega : 4 ≤ 7) h7
    have hqn7 : qn 7 = 35 := by rw [← qnFast_eq_qn 7]; decide
    have hsn7 : sn 7 = 12 := by
      have hfac := factorial_eq_qn_mul_sn_sq 7
      rw [hqn7, show Nat.factorial 7 = 5040 by decide] at hfac
      nlinarith [sn_pos 7]
    let b : Pell.Solution₁ (qn 7 : ℤ) := ⟨6, 1, by rw [hqn7]; norm_num⟩
    have hfund := pellFundUnit_isFundamental (by omega : 3 ≤ 7) hn6
    obtain ⟨r, hr⟩ := hfund.eq_pow_of_nonneg b (by norm_num) (by norm_num)
    have hr1 : 1 ≤ r := by
      by_contra hr0
      have hr0' : r = 0 := by omega
      subst hr0'
      have hy0 : b.y = 0 := by rw [hr]; rfl
      norm_num [b] at hy0
    have hYr_r : Yr 7 (by omega) hn6 r = 1 := by
      have h1 : (Yr 7 (by omega) hn6 r : ℤ) = b.y := by
        rw [Yr_eq, hr]; rfl
      exact_mod_cast h1
    have hr_eq1 : r = 1 := by
      by_contra hr_ne
      have := (Yr_strictMono (by omega : 3 ≤ 7) hn6) (by omega : 1 < r)
      have hY1 := Y1_pos (by omega : 3 ≤ 7) hn6
      have hYr1 : Yr 7 (by omega) hn6 1 = Y1 7 (by omega) hn6 := by
        have : (Yr 7 (by omega) hn6 1 : ℤ) = (Y1 7 (by omega) hn6 : ℤ) := by rw [Yr_eq, Y1_eq]; rfl
        exact_mod_cast this
      omega
    have hY1_eq1 : Y1 7 (by omega) hn6 = 1 := by
      have : (Y1 7 (by omega) hn6 : ℤ) = 1 := by
        have := congr_arg Pell.Solution₁.y hr
        rw [hr_eq1, pow_one] at this
        rw [Y1_eq, ← this]
      exact_mod_cast this
    have hX1_eq6 : X1 7 (by omega) hn6 = 6 := by
      have : (X1 7 (by omega) hn6 : ℤ) = 6 := by
        have := congr_arg Pell.Solution₁.x hr
        rw [hr_eq1, pow_one] at this
        rw [X1_eq, ← this]
      exact_mod_cast this
    have hYr2_eq12 : Yr 7 (by omega) hn6 2 = 12 := by
      have h2 := (lemma_3_2_i 7 (by omega) hn6 2 (by norm_num)).2.1
      have hU : (Polynomial.Chebyshev.U ℤ ((2 : ℕ) - 1)).eval (X1 7 (by omega) hn6 : ℤ) =
          2 * (X1 7 (by omega) hn6 : ℤ) := by
        simp [Polynomial.Chebyshev.U_one]
      rw [hU, hX1_eq6, hY1_eq1] at h2
      exact_mod_cast h2
    have hYr_k : Yr 7 (by omega) hn6 k = 12 := by
      have : (Yr 7 (by omega) hn6 k : ℤ) = (sn 7 : ℤ) := by rw [Yr_eq, ← hsny]
      have : Yr 7 (by omega) hn6 k = sn 7 := by exact_mod_cast this
      omega
    exact (Yr_strictMono (by omega : 3 ≤ 7) hn6).injective (hYr_k.trans hYr2_eq12.symm)
  have hpart4 : ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn8 : 8 ≤ n) → (hN : N₀ ≤ n) → (hsol : IsBrocardSol n m) →
      pellIndex (by omega) hsol = 1 ∨ pellIndex (by omega) hsol = 2 := by
    have hSodd_lo := theorem_2_5_ii.2.2.2.1
    have h_ev1 : ∀ᶠ n : ℕ in atTop, |Sodd n - (1 / 2 : ℝ) * n * Real.log n| ≤ (1 / 40 : ℝ) * ((n : ℝ) * Real.log n) := by
      have h1 := hSodd_lo.bound (by norm_num : (0 : ℝ) < 1 / 40)
      filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
      have hnn : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
      simpa [Real.norm_eq_abs, abs_of_nonneg hnn] using hn
    have h_ev2 : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.log 3 + 2 * Real.log (2.5 * Real.log n) + 2 * Real.log 3 ≤ (1 / 40 : ℝ) * ((n : ℝ) * Real.log n) := by
      have h_tend : Tendsto (fun n : ℕ =>
          Real.log 3 / Real.log n + 5 / (n : ℝ) + 2 * Real.log 3 / ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => Real.log 3 / Real.log n) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        have h2 : Tendsto (fun n : ℕ => (5 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        have h3 : Tendsto (fun n : ℕ => 2 * Real.log 3 / ((n : ℝ) * Real.log n)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_atTop
            (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
        simpa using (h1.add h2).add h3
      filter_upwards [h_tend.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 40)),
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
        eventually_ge_atTop 2] with n hle hlog1 hn2
      have hlog_pos : 0 < Real.log n := by linarith
      have hn_pos : (0 : ℝ) < n := by positivity
      have hlog_25 : Real.log (2.5 * Real.log n) ≤ 2.5 * Real.log n :=
        le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
      have hnum_le : (n : ℝ) * Real.log 3 + 2 * Real.log (2.5 * Real.log n) + 2 * Real.log 3 ≤
          (Real.log 3 / Real.log n + 5 / (n : ℝ) + 2 * Real.log 3 / ((n : ℝ) * Real.log n)) * ((n : ℝ) * Real.log n) := by
        have heq : (Real.log 3 / Real.log n + 5 / (n : ℝ) + 2 * Real.log 3 / ((n : ℝ) * Real.log n)) * ((n : ℝ) * Real.log n) =
            (n : ℝ) * Real.log 3 + 5 * Real.log n + 2 * Real.log 3 := by
          field_simp [hlog_pos.ne', hn_pos.ne']
        rw [heq]
        linarith
      exact le_trans hnum_le (mul_le_mul_of_nonneg_right hle (by positivity))
    have h_ev3 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) * Real.log 3 ≤ (1 / 20 : ℝ) * ((n : ℝ) * Real.log n) := by
      have h_tend : Tendsto (fun n : ℕ => (n : ℝ) * Real.log n) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      filter_upwards [h_tend.eventually_ge_atTop (40 * Real.log 3)] with n hn
      linarith
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_ge_atTop 8 |>.and (h_ev1.and (h_ev2.and h_ev3)))
    refine ⟨max N₀ 8, le_max_right _ _, fun n m hn8 hN hsol => ?_⟩
    obtain ⟨_, hSodd_bd, herr_bd, h3_bd⟩ := hN₀ n (le_trans (le_max_left _ _) hN)
    obtain ⟨hn6, hk1, hmx, hsny⟩ := pellIndex_spec (by omega : 4 ≤ n) hsol
    set k := pellIndex (by omega : 4 ≤ n) hsol
    have hk_ub : (k : ℝ) < 2.5 * Real.log n :=
      (lemma_3_1_i n (by omega) hn6).2.2.2.2.2 hn8 m hsol |>.2.1
    have h_lo : Sodd n - (n : ℝ) * Real.log 3 - 2 * Real.log k ≤ Real.log ((qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2) := by
      have hM_eq : qn n * (Y1 n (by omega) hn6) ^ 2 =
          ∏ p ∈ (qn n * (Y1 n (by omega) hn6) ^ 2).primeFactors,
            p ^ padicValNat p (qn n * (Y1 n (by omega) hn6) ^ 2) :=
        (Nat.prod_primeFactors_pow_factorization (mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos (by omega) hn6).ne'))).symm
      have hsub : ((Podd n).filter (3 ≤ ·)).erase 3 ⊆ (qn n * (Y1 n (by omega) hn6) ^ 2).primeFactors := by
        intro p hp
        have hp_mem := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
        have hp_prime : p.Prime := (Finset.mem_filter.mp hp_mem).2.1
        have hp_qn : p ∣ qn n := by rw [qn_eq_prod_Podd]; exact Finset.dvd_prod_of_mem _ hp_mem
        exact Nat.mem_primeFactors.mpr ⟨hp_prime, dvd_mul_of_dvd_left hp_qn _, mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos (by omega) hn6).ne')⟩
      have hlog_M : Real.log ((qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2) =
          ∑ p ∈ (qn n * (Y1 n (by omega) hn6) ^ 2).primeFactors,
            (padicValNat p (qn n * (Y1 n (by omega) hn6) ^ 2) : ℝ) * Real.log p := by
        have hnat : ((qn n * (Y1 n (by omega) hn6) ^ 2 : ℕ) : ℝ) =
            ∏ p ∈ (qn n * (Y1 n (by omega) hn6) ^ 2).primeFactors,
              ((p : ℝ) ^ padicValNat p (qn n * (Y1 n (by omega) hn6) ^ 2)) := by
          conv_lhs => rw [hM_eq]
          push_cast; rfl
        have : (qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2 = ((qn n * (Y1 n (by omega) hn6) ^ 2 : ℕ) : ℝ) := by
          push_cast; rfl
        rw [this, hnat, Real.log_prod]
        · refine Finset.sum_congr rfl fun p _ => Real.log_pow _ _
        · intro p hp
          have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hp).1
          exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp_prime.ne_zero)
      have hsum_ge : ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p (qn n * (Y1 n (by omega) hn6) ^ 2) : ℝ) * Real.log p ≤
          Real.log ((qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2) := by
        rw [hlog_M]
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
        have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
      have hterm_eq : ∀ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3,
          (padicValNat p (qn n * (Y1 n (by omega) hn6) ^ 2) : ℝ) * Real.log p =
          ((padicValNat p n.factorial : ℝ) - 2 * (padicValNat p k : ℝ)) * Real.log p := by
        intro p hp
        have hp_ne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
        have hp_mem := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
        have hv := (lemma_3_2_i n (by omega) hn6 k hk1).2.2.2.2.2 (by omega) m hsol rfl p hp_mem (Or.inl hp_ne3)
        have hle : 2 * padicValNat p k ≤ padicValNat p n.factorial := by
          have hp_prime : p.Prime := (Finset.mem_filter.mp hp_mem).2.1
          haveI : Fact p.Prime := ⟨hp_prime⟩
          have hsn_eq : (sn n : ℤ) = (Yr n (by omega) hn6 k : ℤ) := by rw [Yr_eq, ← hsny]
          have hp_dvd_sn : p ^ padicValNat p k ∣ sn n := by
            have h2 := (lemma_3_2_i n (by omega) hn6 k hk1).2.1
            have h5 := (lemma_3_2_i n (by omega) hn6 k hk1).2.2.2.2.1 p hp_prime (by
              have hp_qn : p ∣ qn n := by rw [qn_eq_prod_Podd]; exact Finset.dvd_prod_of_mem _ hp_mem
              exact dvd_mul_of_dvd_left hp_qn _) (Or.inl hp_ne3)
            have hsn_nat : sn n = Y1 n (by omega) hn6 * ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n (by omega) hn6 : ℤ)).natAbs := by
              have hZ : (sn n : ℤ) = (Y1 n (by omega) hn6 : ℤ) * (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n (by omega) hn6 : ℤ) := by
                rw [hsn_eq, h2]
              simpa [Int.natAbs_mul] using congr_arg Int.natAbs hZ
            rw [hsn_nat]
            exact dvd_mul_of_dvd_right ((padicValNat_dvd_iff_le (by
              intro h0
              have hZ0 : (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n (by omega) hn6 : ℤ) = 0 := Int.natAbs_eq_zero.mp h0
              rw [hZ0, mul_zero] at h2
              have := Yr_pos (by omega : 3 ≤ n) hn6 hk1
              omega)).mpr (by exact_mod_cast h5.le)) _
          have hfac := factorial_eq_qn_mul_sn_sq n
          have hval_fac : padicValNat p n.factorial = padicValNat p (qn n) + 2 * padicValNat p (sn n) := by
            rw [hfac, padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'), padicValNat.pow 2 (sn_pos n).ne']
          have hle_sn : padicValNat p k ≤ padicValNat p (sn n) :=
            (padicValNat_dvd_iff_le (sn_pos n).ne').mp hp_dvd_sn
          omega
        rw [hv, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
      have hsum_eq : ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p (qn n * (Y1 n (by omega) hn6) ^ 2) : ℝ) * Real.log p =
          (∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p n.factorial : ℝ) * Real.log p) -
          2 * ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p k : ℝ) * Real.log p := by
        rw [Finset.sum_congr rfl hterm_eq]
        simp_rw [sub_mul, mul_assoc]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hSodd_diff : Sodd n - (n : ℝ) * Real.log 3 ≤
          ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p n.factorial : ℝ) * Real.log p := by
        unfold Sodd
        by_cases h3 : 3 ∈ (Podd n).filter (3 ≤ ·)
        · rw [← Finset.add_sum_erase _ _ h3]
          have h3_le : padicValNat 3 n.factorial ≤ n := by
            haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
            have := sub_one_mul_padicValNat_factorial (p := 3) n
            omega
          have h3R : (padicValNat 3 n.factorial : ℝ) * Real.log 3 ≤ (n : ℝ) * Real.log 3 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h3_le) (Real.log_nonneg (by norm_num))
          linarith
        · rw [Finset.erase_eq_of_notMem h3]
          linarith [mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))]
      have hk_sum_le : ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p k : ℝ) * Real.log p ≤ Real.log k := by
        have hsub_k : ((Podd n).filter (3 ≤ ·)).erase 3 ∩ k.primeFactors ⊆ k.primeFactors := Finset.inter_subset_right
        have h1 : ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3, (padicValNat p k : ℝ) * Real.log p =
            ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3 ∩ k.primeFactors, (padicValNat p k : ℝ) * Real.log p := by
          rw [← Finset.sum_inter_add_sum_diff (((Podd n).filter (3 ≤ ·)).erase 3) k.primeFactors]
          have hz : ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3 \ k.primeFactors, (padicValNat p k : ℝ) * Real.log p = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hmem := Finset.mem_sdiff.mp hp
            have hp_prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hmem.1).2).1).2.1
            have hndvd : ¬ p ∣ k := fun hd => hmem.2 (Nat.mem_primeFactors.mpr ⟨hp_prime, hd, by omega⟩)
            simp [padicValNat.eq_zero_of_not_dvd hndvd]
          linarith
        rw [h1]
        have hle_k : ∑ p ∈ ((Podd n).filter (3 ≤ ·)).erase 3 ∩ k.primeFactors, (padicValNat p k : ℝ) * Real.log p ≤
            ∑ p ∈ k.primeFactors, (padicValNat p k : ℝ) * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_k fun p hp _ =>
            mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le))
        have hlog_k : ∑ p ∈ k.primeFactors, (padicValNat p k : ℝ) * Real.log p = Real.log k := by
          have hk_eq : k = ∏ p ∈ k.primeFactors, p ^ padicValNat p k := (Nat.prod_primeFactors_pow_factorization (by omega : k ≠ 0)).symm
          have hR : (k : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) ^ padicValNat p k) := by
            conv_lhs => rw [hk_eq]
            push_cast; rfl
          rw [hR, Real.log_prod]
          · refine Finset.sum_congr rfl fun p _ => Real.log_pow _ _
          · intro p hp; exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)
        linarith
      linarith
    have h_hi : Real.log ((qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2) ≤
        (1 / (k : ℝ)) * ((n : ℝ) * Real.log n) + 2 * Real.log 3 := by
      have hX_gt : (Y1 n (by omega) hn6 : ℝ) * Real.sqrt (qn n) < (X1 n (by omega) hn6 : ℝ) := by
        have hsq : ((Y1 n (by omega) hn6 : ℝ) * Real.sqrt (qn n)) ^ 2 < (X1 n (by omega) hn6 : ℝ) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n).le)]
          have hprop : (X1 n (by omega) hn6 : ℝ) ^ 2 - (qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2 = 1 := by
            rw [X1_eq, Y1_eq]; exact_mod_cast (pellFundUnit n (by omega) hn6).prop
          linarith
        nlinarith [Real.sqrt_nonneg (qn n)]
      have heps_gt : 2 * ((Y1 n (by omega) hn6 : ℝ) * Real.sqrt (qn n)) < epsReal n (by omega) hn6 := by
        unfold epsReal; linarith
      have hM_lt : (qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2 < (epsReal n (by omega) hn6) ^ 2 := by
        have h1 : (qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2 = ((Y1 n (by omega) hn6 : ℝ) * Real.sqrt (qn n)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n).le)]; ring
        rw [h1]
        nlinarith [Real.sqrt_nonneg (qn n)]
      have heps_k : (epsReal n (by omega) hn6) ^ k = (m : ℝ) + (sn n : ℝ) * Real.sqrt (qn n) := by
        have hpow := pell_pow_real_eq (n := n) (by omega) hn6 k
        rw [← hmx, ← hsny] at hpow
        exact hpow.symm
      have hm_le : (m : ℝ) ≤ (3 / 2 : ℝ) * Real.sqrt n.factorial := by
        have hm2 : (m : ℝ) ^ 2 = (n.factorial : ℝ) + 1 := by exact_mod_cast hsol.2.2.symm
        have hfac1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
        have hsq : (m : ℝ) ^ 2 ≤ ((3 / 2 : ℝ) * Real.sqrt n.factorial) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          linarith
        nlinarith [Real.sqrt_nonneg n.factorial]
      have hsn_le : (sn n : ℝ) * Real.sqrt (qn n) = Real.sqrt n.factorial := by
        have hfac := factorial_eq_qn_mul_sn_sq n
        have hR : (n.factorial : ℝ) = (qn n : ℝ) * (sn n : ℝ) ^ 2 := by exact_mod_cast hfac
        rw [hR, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
      have heps_k_le : (epsReal n (by omega) hn6) ^ k ≤ 3 * Real.sqrt n.factorial := by
        linarith
      have hlog_eps_k : (k : ℝ) * Real.log (epsReal n (by omega) hn6) ≤ (1 / 2 : ℝ) * Real.log n.factorial + Real.log 3 := by
        have hpos_e : 0 < epsReal n (by omega) hn6 := by unfold epsReal; positivity
        have h1 := Real.log_le_log (pow_pos hpos_e k) heps_k_le
        rw [Real.log_pow, Real.log_mul (by norm_num) (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos n)).ne',
          Real.log_sqrt (by positivity)] at h1
        linarith
      have hlog_M : Real.log ((qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2) < 2 * Real.log (epsReal n (by omega) hn6) := by
        have h1 := Real.log_lt_log (mul_pos (by exact_mod_cast qn_pos n) (pow_pos (by exact_mod_cast Y1_pos (by omega) hn6) 2)) hM_lt
        rwa [Real.log_pow] at h1
      have hfac_le_nn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
        exact_mod_cast Nat.factorial_le_pow n
      have hlog_fac : Real.log n.factorial ≤ (n : ℝ) * Real.log n := by
        have h1 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) hfac_le_nn
        rwa [Real.log_pow] at h1
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      calc Real.log ((qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2)
          ≤ 2 * Real.log (epsReal n (by omega) hn6) := hlog_M.le
        _ ≤ 2 * (((1 / 2 : ℝ) * Real.log n.factorial + Real.log 3) / (k : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ((le_div_iff₀ hk_pos).mpr (by linarith)) (by norm_num)
        _ = (1 / (k : ℝ)) * Real.log n.factorial + (2 / (k : ℝ)) * Real.log 3 := by ring
        _ ≤ (1 / (k : ℝ)) * ((n : ℝ) * Real.log n) + 2 * Real.log 3 := by
            have h2k : 2 / (k : ℝ) ≤ 2 := div_le_self (by norm_num) (by exact_mod_cast hk1)
            refine add_le_add (mul_le_mul_of_nonneg_left hlog_fac (by positivity))
              (mul_le_mul_of_nonneg_right h2k (Real.log_nonneg (by norm_num)))
    have hlog_k_bd : Real.log k ≤ Real.log (2.5 * Real.log n) :=
      Real.log_le_log (by exact_mod_cast hk1) hk_ub.le
    have hn_log_pos : 0 < (n : ℝ) * Real.log n :=
      mul_pos (by exact_mod_cast (by omega : 0 < n)) (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
    have h_comb : (2 / 5 : ℝ) * ((n : ℝ) * Real.log n) ≤
        (1 / (k : ℝ)) * ((n : ℝ) * Real.log n) := by
      have h1 : (1 / 2 - 1 / 40 : ℝ) * ((n : ℝ) * Real.log n) ≤ Sodd n := by
        have := (abs_le.mp hSodd_bd).1; linarith
      linarith
    have h_inv_k : (2 / 5 : ℝ) ≤ 1 / (k : ℝ) := by
      have : ((2 / 5 : ℝ) - 1 / (k : ℝ)) * ((n : ℝ) * Real.log n) ≤ 0 := by linarith
      exact le_of_sub_nonpos (nonpos_of_mul_nonpos_left this hn_log_pos)
    have hk_lt3 : k < 3 := by
      have hk_le_real : (k : ℝ) ≤ 5 / 2 := by
        rw [le_div_iff₀ (by exact_mod_cast hk1 : (0 : ℝ) < k)] at h_inv_k
        linarith
      by_contra hge3
      have : (3 : ℝ) ≤ k := by exact_mod_cast (by omega : 3 ≤ k)
      linarith
    omega
  have hpart5 : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn8 : 8 ≤ n) → (hN : N₀ ≤ n) → (hsol : IsBrocardSol n m) →
      ∀ (hn : 3 ≤ n) (hn6 : n ≠ 6),
        |Real.log (epsReal n hn hn6) / ((n : ℝ) * Real.log n) -
          1 / (2 * (pellIndex (by omega) hsol : ℝ))| ≤ C / Real.log n := by
    obtain ⟨C₁, hC₁, N₁, hN₁⟩ := lemma_3_1_ii.1
    refine ⟨C₁ + 3, by positivity, max N₁ 8, le_max_right _ _, fun n m hn8 hN hsol hn hn6 => ?_⟩
    obtain ⟨hn6', hk1, hmx, hsny⟩ := pellIndex_spec (by omega : 4 ≤ n) hsol
    set k := pellIndex (by omega : 4 ≤ n) hsol
    have hst := hN₁ n (le_trans (le_max_left _ _) hN)
    have heps_k : (epsReal n hn hn6) ^ k = (m : ℝ) + (sn n : ℝ) * Real.sqrt (qn n) := by
      have hpow := pell_pow_real_eq (n := n) hn hn6 k
      rw [← hmx, ← hsny] at hpow
      exact hpow.symm
    have hsn_lt : (sn n : ℝ) * Real.sqrt (qn n) < (m : ℝ) := by
      have hsq : ((sn n : ℝ) * Real.sqrt (qn n)) ^ 2 < (m : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n).le)]
        have hfac : (n.factorial : ℝ) = (qn n : ℝ) * (sn n : ℝ) ^ 2 := by exact_mod_cast (factorial_eq_qn_mul_sn_sq n).symm
        have hm2 : (n.factorial : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hsol.2.2
        linarith
      nlinarith [Real.sqrt_nonneg (qn n)]
    have hm_le : (m : ℝ) ≤ 2 * ((sn n : ℝ) * Real.sqrt (qn n)) := by
      have hsq : (m : ℝ) ^ 2 ≤ (2 * ((sn n : ℝ) * Real.sqrt (qn n))) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n).le)]
        have hfac : (n.factorial : ℝ) = (qn n : ℝ) * (sn n : ℝ) ^ 2 := by exact_mod_cast (factorial_eq_qn_mul_sn_sq n).symm
        have hm2 : (n.factorial : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hsol.2.2
        have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
        linarith
      nlinarith [Real.sqrt_nonneg (qn n)]
    have heps_lo : 2 * ((sn n : ℝ) * Real.sqrt (qn n)) < (epsReal n hn hn6) ^ k := by linarith
    have heps_hi : (epsReal n hn hn6) ^ k ≤ 3 * ((sn n : ℝ) * Real.sqrt (qn n)) := by linarith
    have hpos_snq : 0 < (sn n : ℝ) * Real.sqrt (qn n) :=
      mul_pos (by exact_mod_cast sn_pos n) (Real.sqrt_pos.mpr (by exact_mod_cast qn_pos n))
    have hpos_e : 0 < epsReal n hn hn6 := by unfold epsReal; positivity
    have hlog_lo : Real.log 2 + Real.log ((sn n : ℝ) * Real.sqrt (qn n)) < (k : ℝ) * Real.log (epsReal n hn hn6) := by
      have h1 := Real.log_lt_log (by positivity) heps_lo
      rw [Real.log_mul (by norm_num) hpos_snq.ne', Real.log_pow] at h1
      exact h1
    have hlog_hi : (k : ℝ) * Real.log (epsReal n hn hn6) ≤ Real.log 3 + Real.log ((sn n : ℝ) * Real.sqrt (qn n)) := by
      have h1 := Real.log_le_log (pow_pos hpos_e k) heps_hi
      rw [Real.log_mul (by norm_num) hpos_snq.ne', Real.log_pow] at h1
      exact h1
    have hdiff1 : |(k : ℝ) * Real.log (epsReal n hn hn6) - Real.log ((sn n : ℝ) * Real.sqrt (qn n))| ≤ Real.log 3 := by
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog3_gt : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hn_pos : (0 : ℝ) < n := by positivity
    have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hlog2pin : |Real.log (2 * Real.pi * n)| ≤ 2 * n := by
      have h1 : 1 ≤ 2 * Real.pi * n := by nlinarith [Real.pi_gt_three]
      have h3 : 2 * Real.pi * n ≤ 8 * n := by nlinarith [Real.pi_lt_four]
      have h4 : Real.log (2 * Real.pi * n) ≤ Real.log 8 + Real.log n := by
        rw [← Real.log_mul (by norm_num) hn_pos.ne']
        exact Real.log_le_log (by positivity) h3
      have h5 : Real.log 8 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]
      have h6 : Real.log n ≤ n := by linarith [Real.log_le_sub_one_of_pos hn_pos]
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      linarith
    have hdiff2 : |(k : ℝ) * Real.log (epsReal n hn hn6) - (1 / 2 : ℝ) * n * Real.log n| ≤ (C₁ + 3) * n := by
      have h1 : |Real.log ((sn n : ℝ) * Real.sqrt (qn n)) - (1 / 2 : ℝ) * n * Real.log n| ≤
          C₁ * (n : ℝ)⁻¹ + (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * |Real.log (2 * Real.pi * n)| := by
        have heq : Real.log ((sn n : ℝ) * Real.sqrt (qn n)) - (1 / 2 : ℝ) * n * Real.log n =
            (Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
              ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n))) -
            (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n) := by ring
        rw [heq]
        have ht1 := abs_add_le
          ((Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
            ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n))) -
            (1 / 2 : ℝ) * n)
          ((1 / 4 : ℝ) * Real.log (2 * Real.pi * n))
        have ht2 := abs_sub
          (Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
            ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n)))
          ((1 / 2 : ℝ) * n)
        rw [abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) * n)] at ht2
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] at ht1
        linarith
      have hinv_le : (n : ℝ)⁻¹ ≤ n := by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        exact le_trans (inv_le_one_of_one_le₀ hn1) hn1
      have hlog3_le : Real.log 3 ≤ (3 / 2 : ℝ) * n := by
        have h1 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
        have hn8R : (8 : ℝ) ≤ n := by exact_mod_cast hn8
        linarith
      have htri := abs_add_le
        ((k : ℝ) * Real.log (epsReal n hn hn6) - Real.log ((sn n : ℝ) * Real.sqrt (qn n)))
        (Real.log ((sn n : ℝ) * Real.sqrt (qn n)) - (1 / 2 : ℝ) * n * Real.log n)
      have hC1_le : C₁ * (n : ℝ)⁻¹ ≤ C₁ * n := mul_le_mul_of_nonneg_left hinv_le hC₁.le
      linarith
    have hdiv_eq : Real.log (epsReal n hn hn6) / ((n : ℝ) * Real.log n) - 1 / (2 * (k : ℝ)) =
        ((k : ℝ) * Real.log (epsReal n hn hn6) - (1 / 2 : ℝ) * n * Real.log n) / ((k : ℝ) * ((n : ℝ) * Real.log n)) := by
      field_simp [hk_pos.ne', hn_pos.ne', hlogn_pos.ne']
    rw [hdiv_eq, abs_div, abs_of_pos (mul_pos hk_pos (mul_pos hn_pos hlogn_pos))]
    calc |(k : ℝ) * Real.log (epsReal n hn hn6) - (1 / 2 : ℝ) * n * Real.log n| / ((k : ℝ) * ((n : ℝ) * Real.log n))
        ≤ ((C₁ + 3) * n) / ((k : ℝ) * ((n : ℝ) * Real.log n)) :=
          div_le_div_of_nonneg_right hdiff2 (by positivity)
      _ ≤ ((C₁ + 3) * n) / (1 * ((n : ℝ) * Real.log n)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) (by positivity))
      _ = (C₁ + 3) / Real.log n := by
          field_simp [hn_pos.ne', hlogn_pos.ne']
  have hpart6 : ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n₁ n₂ m₁ m₂ : ℕ, 4 ≤ n₁ → (n₁ ≤ 10 ^ 9 ∨ N₀ ≤ n₁) → n₁ < n₂ →
      IsBrocardSol n₁ m₁ → IsBrocardSol n₂ m₂ → qn n₁ ≠ qn n₂ := by
    obtain ⟨N₀, hN₀_ge, hN₀⟩ := hpart4
    refine ⟨N₀, hN₀_ge, fun n₁ n₂ m₁ m₂ hn₁ hcase hn12 hsol₁ hsol₂ hq_eq => ?_⟩
    rcases hcase with hn₁_small | hn₁_big
    · have hn₁_list : n₁ = 4 ∨ n₁ = 5 ∨ n₁ = 7 := by
        by_cases h8 : 8 ≤ n₁
        · exact False.elim (berndt_galway_brocard_bound n₁ m₁ hsol₁ h8 hn₁_small)
        · have : n₁ = 4 ∨ n₁ = 5 ∨ n₁ = 6 ∨ n₁ = 7 := by omega
          rcases this with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact False.elim ((pellIndex_spec (by omega : 4 ≤ 6) hsol₁).1 rfl)
          · exact Or.inr (Or.inr rfl)
      have hq1_le35 : qn n₁ ≤ 35 := by
        rcases hn₁_list with rfl | rfl | rfl
        · rw [← qnFast_eq_qn 4]; decide
        · rw [← qnFast_eq_qn 5]; decide
        · rw [← qnFast_eq_qn 7]; decide
      by_cases hn₂_small : n₂ ≤ 10 ^ 9
      · have hn₂_list : n₂ = 4 ∨ n₂ = 5 ∨ n₂ = 7 := by
          by_cases h8 : 8 ≤ n₂
          · exact False.elim (berndt_galway_brocard_bound n₂ m₂ hsol₂ h8 hn₂_small)
          · have : n₂ = 4 ∨ n₂ = 5 ∨ n₂ = 6 ∨ n₂ = 7 := by omega
          rcases this with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact False.elim ((pellIndex_spec (by omega : 4 ≤ 6) hsol₂).1 rfl)
          · exact Or.inr (Or.inr rfl)
        have hq4 : qn 4 = 6 := by rw [← qnFast_eq_qn 4]; decide
        have hq5 : qn 5 = 30 := by rw [← qnFast_eq_qn 5]; decide
        have hq7 : qn 7 = 35 := by rw [← qnFast_eq_qn 7]; decide
        rcases hn₁_list with rfl | rfl | rfl <;> rcases hn₂_list with rfl | rfl | rfl <;> omega
      · push_neg at hn₂_small
        have hlog2 := (lemma_3_1_i n₂ (by omega) (by omega)).2.2.2.1 (Or.inl (by omega))
        have hlog1 : Real.log (qn n₁) ≤ Real.log 35 := Real.log_le_log (by exact_mod_cast qn_pos n₁) (by exact_mod_cast hq1_le35)
        have h35 : Real.log 35 < 35 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 35)]
        have hn2R : (10 ^ 9 : ℝ) < n₂ := by exact_mod_cast hn₂_small
        rw [hq_eq] at hlog1
        linarith
    · have hk12 := hN₀ n₁ m₁ (by omega) hn₁_big hsol₁
      obtain ⟨hn6₁, hk₁_pos, hmx₁, hsny₁⟩ := pellIndex_spec (by omega : 4 ≤ n₁) hsol₁
      obtain ⟨hn6₂, hk₂_pos, hmx₂, hsny₂⟩ := pellIndex_spec (by omega : 4 ≤ n₂) hsol₂
      have hp_contra : ∀ p : ℕ, p.Prime → n₁ < p → p ≤ n₂ → n₂ < 2 * p → False := by
        intro p hp hnp1 hpn2 hn2_2p
        have hnsq : n₂ < p ^ 2 := by nlinarith
        have hv2 : padicValNat p n₂.factorial = 1 := by
          rw [padicValNat_factorial_of_lt_sq hp hnsq]
          rw [Nat.div_eq_iff_eq_mul_add_mod] <;> omega
        have hp_mem2 : p ∈ Podd n₂ := by
          simp only [Podd, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hp.two_le, hpn2⟩, hp, by rw [hv2]; decide⟩
        have hp_dvd2 : p ∣ qn n₂ := by rw [qn_eq_prod_Podd]; exact Finset.dvd_prod_of_mem _ hp_mem2
        have hp_ndvd1 : ¬ p ∣ qn n₁ := by
          intro h1
          rw [qn_eq_prod_Podd] at h1
          rcases hp.dvd_finset_prod_iff.mp h1 with ⟨q, hq, hpq⟩
          have hq_prime : q.Prime := (Finset.mem_filter.mp hq).2.1
          have hq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq
          have hq_le : q ≤ n₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
          omega
        exact hp_ndvd1 (hq_eq ▸ hp_dvd2)
      by_cases h2n : 2 * n₁ ≤ n₂
      · obtain ⟨p, hp, hplo, hphi, _⟩ := breusch_bertrand_mod_four ((n₂ : ℝ) / 2) (by
          have : (16 : ℝ) ≤ n₂ := by exact_mod_cast (by omega : 16 ≤ n₂)
          linarith)
        have hnp1 : n₁ < p := by
          have : (n₁ : ℝ) ≤ (n₂ : ℝ) / 2 := by
            have : (2 * n₁ : ℝ) ≤ n₂ := by exact_mod_cast h2n
            linarith
          exact_mod_cast (lt_of_le_of_lt this hplo)
        have hpn2 : p ≤ n₂ := by exact_mod_cast (by linarith : (p : ℝ) ≤ n₂)
        have hn2_2p : n₂ < 2 * p := by exact_mod_cast (by linarith : (n₂ : ℝ) < 2 * p)
        exact hp_contra p hp hnp1 hpn2 hn2_2p
      · push_neg at h2n
        by_cases hn1_small : n₁ ≤ 10 ^ 9
        · exact berndt_galway_brocard_bound n₁ m₁ hsol₁ (by omega) hn1_small
        · push_neg at hn1_small
          have htheta : Chebyshev.theta ((n₁ : ℝ) + (n₁ : ℝ) / 16597) > Chebyshev.theta (n₁ : ℝ) :=
            schoenfeld_prime_gap (n₁ : ℝ) (by exact_mod_cast (by omega : 2010760 ≤ n₁))
          have hdiff_pos : 0 < Chebyshev.theta ((n₁ : ℝ) + (n₁ : ℝ) / 16597) - Chebyshev.theta (n₁ : ℝ) := by linarith
          have hsub_ne : ((Finset.Ioc 0 ⌊(n₁ : ℝ) + (n₁ : ℝ) / 16597⌋₊).filter Nat.Prime \ (Finset.Ioc 0 ⌊(n₁ : ℝ)⌋₊).filter Nat.Prime).Nonempty := by
            by_contra hempty
            rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
            have hle : Chebyshev.theta ((n₁ : ℝ) + (n₁ : ℝ) / 16597) ≤ Chebyshev.theta (n₁ : ℝ) := by
              unfold Chebyshev.theta
              exact Finset.sum_le_sum_of_subset_of_nonneg hempty fun q hq _ =>
                Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le)
            linarith
          obtain ⟨p, hp_sdiff⟩ := hsub_ne
          rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc] at hp_sdiff
          have hp : p.Prime := hp_sdiff.1.2
          have hnp1 : n₁ < p := by
            have hfl1 : ⌊(n₁ : ℝ)⌋₊ = n₁ := Nat.floor_natCast n₁
            rw [hfl1] at hp_sdiff
            by_contra hle
            exact hp_sdiff.2 ⟨⟨hp.pos, by omega⟩, hp⟩
          have hp_le_real : (p : ℝ) ≤ (n₁ : ℝ) + (n₁ : ℝ) / 16597 := by
            have hfl := Nat.floor_le (by positivity : 0 ≤ (n₁ : ℝ) + (n₁ : ℝ) / 16597)
            exact le_trans (by exact_mod_cast hp_sdiff.1.1.2) hfl
          -- Show `n₁ + n₁ / 16597 ≤ n₂` using `k₁ < k₂`
          set k₁ := pellIndex (by omega : 4 ≤ n₁) hsol₁
          set k₂ := pellIndex (by omega : 4 ≤ n₂) hsol₂
          have heps1_eq : epsReal n₁ (by omega) hn6₁ = epsReal n₂ (by omega) hn6₂ := by
            -- Actually `q_{n₁} = q_{n₂}`, so `pellFundUnit` depends only on `qn`, wait: `pellFundUnit` uses `Classical.choose` on `qn_pos` and `qn_not_isSquare` which depend on `n`!
            -- Better: `pellFundUnit n₁` and `pellFundUnit n₂` are BOTH fundamental units for the SAME `qn`, so their `x, y` are EQUAL!
            have h1 := pellFundUnit_isFundamental (by omega : 3 ≤ n₁) hn6₁
            have h2 := pellFundUnit_isFundamental (by omega : 3 ≤ n₂) hn6₂
            let u₁ : Pell.Solution₁ (qn n₂ : ℤ) := ⟨(pellFundUnit n₁ (by omega) hn6₁).x, (pellFundUnit n₁ (by omega) hn6₁).y, by
              rw [← hq_eq]; exact (pellFundUnit n₁ (by omega) hn6₁).prop⟩
            have hx_le1 : u₁.x ≤ (pellFundUnit n₂ (by omega) hn6₂).x := by
              obtain ⟨r, hr⟩ := h1.eq_pow_of_nonneg ⟨(pellFundUnit n₂ (by omega) hn6₂).x, (pellFundUnit n₂ (by omega) hn6₂).y, by
                rw [hq_eq]; exact (pellFundUnit n₂ (by omega) hn6₂).prop⟩ (by linarith [h2.one_lt_x]) (by linarith [h2.zero_lt_y])
              have hr1 : 1 ≤ r := by
                by_contra hr0; have : r = 0 := by omega; subst this
                have := congr_arg Pell.Solution₁.y hr; simp at this; linarith [h2.zero_lt_y]
              have := (pell_xy_pos (by omega : 3 ≤ n₁) hn6₁ r hr1)
              have hxr := congr_arg Pell.Solution₁.x hr
              dsimp at hxr
              have hmono : ∀ s : ℕ, 1 ≤ s → (pellFundUnit n₁ (by omega) hn6₁).x ≤ (pellFundUnit n₁ (by omega) hn6₁ ^ (s : ℤ)).x := by
                intro s hs
                induction s, hs using Nat.le_induction with
                | base => simp
                | succ m hm ih =>
                  rw [Nat.cast_succ, zpow_add, zpow_one, Pell.Solution₁.mul_x]
                  have hq0 : (0 : ℤ) ≤ qn n₁ := by exact_mod_cast (qn_pos n₁).le
                  have hx0 : 1 ≤ (pellFundUnit n₁ (by omega) hn6₁).x := by linarith [h1.one_lt_x]
                  have hy0 : 0 ≤ (pellFundUnit n₁ (by omega) hn6₁).y := by linarith [h1.zero_lt_y]
                  have hym : 0 ≤ (pellFundUnit n₁ (by omega) hn6₁ ^ (m : ℤ)).y := (pell_xy_nonneg (by omega : 3 ≤ n₁) hn6₁ m).2
                  nlinarith
              rw [← hxr, ← zpow_natCast]
              exact hmono r hr1
            have hx_le2 : (pellFundUnit n₂ (by omega) hn6₂).x ≤ u₁.x := by
              obtain ⟨r, hr⟩ := h2.eq_pow_of_nonneg u₁ (by linarith [h1.one_lt_x]) (by linarith [h1.zero_lt_y])
              have hr1 : 1 ≤ r := by
                by_contra hr0; have : r = 0 := by omega; subst this
                have := congr_arg Pell.Solution₁.y hr; simp [u₁] at this; linarith [h1.zero_lt_y]
              have hxr := congr_arg Pell.Solution₁.x hr
              dsimp [u₁] at hxr
              have hmono : ∀ s : ℕ, 1 ≤ s → (pellFundUnit n₂ (by omega) hn6₂).x ≤ (pellFundUnit n₂ (by omega) hn6₂ ^ (s : ℤ)).x := by
                intro s hs
                induction s, hs using Nat.le_induction with
                | base => simp
                | succ m hm ih =>
                  rw [Nat.cast_succ, zpow_add, zpow_one, Pell.Solution₁.mul_x]
                  have hq0 : (0 : ℤ) ≤ qn n₂ := by exact_mod_cast (qn_pos n₂).le
                  have hx0 : 1 ≤ (pellFundUnit n₂ (by omega) hn6₂).x := by linarith [h2.one_lt_x]
                  have hy0 : 0 ≤ (pellFundUnit n₂ (by omega) hn6₂).y := by linarith [h2.zero_lt_y]
                  have hym : 0 ≤ (pellFundUnit n₂ (by omega) hn6₂ ^ (m : ℤ)).y := (pell_xy_nonneg (by omega : 3 ≤ n₂) hn6₂ m).2
                  nlinarith
              rw [← hxr, ← zpow_natCast]
              exact hmono r hr1
            have hx_eq : (pellFundUnit n₁ (by omega) hn6₁).x = (pellFundUnit n₂ (by omega) hn6₂).x := le_antisymm hx_le1 hx_le2
            have hy_eq : (pellFundUnit n₁ (by omega) hn6₁).y = (pellFundUnit n₂ (by omega) hn6₂).y := by
              have hp1 := (pellFundUnit n₁ (by omega) hn6₁).prop
              have hp2 := (pellFundUnit n₂ (by omega) hn6₂).prop
              rw [hq_eq, hx_eq] at hp1
              have hq_pos : (0 : ℤ) < qn n₂ := by exact_mod_cast qn_pos n₂
              have hsq : (pellFundUnit n₁ (by omega) hn6₁).y ^ 2 = (pellFundUnit n₂ (by omega) hn6₂).y ^ 2 := by nlinarith
              nlinarith [h1.zero_lt_y, h2.zero_lt_y]
            unfold epsReal X1 Y1
            rw [hx_eq, hy_eq, hq_eq]
          have hm1_lt_m2 : m₁ < m₂ := by
            have h1 : m₁ ^ 2 = n₁.factorial + 1 := hsol₁.2.2
            have h2 : m₂ ^ 2 = n₂.factorial + 1 := hsol₂.2.2
            have hfac_lt : n₁.factorial < n₂.factorial := by
              have hle : (n₁ + 1).factorial ≤ n₂.factorial := Nat.factorial_le hn12
              rw [Nat.factorial_succ] at hle
              nlinarith [Nat.factorial_pos n₁]
            nlinarith
          have hk1_lt_k2 : k₁ < k₂ := by
            have hpow1 := pell_pow_real_eq (n := n₁) (by omega) hn6₁ k₁
            have hpow2 := pell_pow_real_eq (n := n₂) (by omega) hn6₂ k₂
            rw [← hmx₁, ← hsny₁] at hpow1
            rw [← hmx₂, ← hsny₂] at hpow2
            have hsq1 : (sn n₁ : ℝ) * Real.sqrt (qn n₁) < m₁ := by
              have hfac : (n₁.factorial : ℝ) = (qn n₁ : ℝ) * (sn n₁ : ℝ) ^ 2 := by exact_mod_cast (factorial_eq_qn_mul_sn_sq n₁).symm
              have hm2 : (n₁.factorial : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hsol₁.2.2
              have hsq : ((sn n₁ : ℝ) * Real.sqrt (qn n₁)) ^ 2 < (m₁ : ℝ) ^ 2 := by
                rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n₁).le)]; linarith
              nlinarith [Real.sqrt_nonneg (qn n₁)]
            have hsq2 : (sn n₂ : ℝ) * Real.sqrt (qn n₂) < m₂ := by
              have hfac : (n₂.factorial : ℝ) = (qn n₂ : ℝ) * (sn n₂ : ℝ) ^ 2 := by exact_mod_cast (factorial_eq_qn_mul_sn_sq n₂).symm
              have hm2 : (n₂.factorial : ℝ) + 1 = (m₂ : ℝ) ^ 2 := by exact_mod_cast hsol₂.2.2
              have hsq : ((sn n₂ : ℝ) * Real.sqrt (qn n₂)) ^ 2 < (m₂ : ℝ) ^ 2 := by
                rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n₂).le)]; linarith
              nlinarith [Real.sqrt_nonneg (qn n₂)]
            have hsn1_lt_sn2 : (sn n₁ : ℝ) * Real.sqrt (qn n₁) < (sn n₂ : ℝ) * Real.sqrt (qn n₂) := by
              have hfac1 : (n₁.factorial : ℝ) = (qn n₁ : ℝ) * (sn n₁ : ℝ) ^ 2 := by exact_mod_cast (factorial_eq_qn_mul_sn_sq n₁).symm
              have hfac2 : (n₂.factorial : ℝ) = (qn n₂ : ℝ) * (sn n₂ : ℝ) ^ 2 := by exact_mod_cast (factorial_eq_qn_mul_sn_sq n₂).symm
              have hfac_lt : (n₁.factorial : ℝ) < (n₂.factorial : ℝ) := by
                exact_mod_cast (show n₁.factorial < n₂.factorial by
                  have hle : (n₁ + 1).factorial ≤ n₂.factorial := Nat.factorial_le hn12
                  rw [Nat.factorial_succ] at hle; nlinarith [Nat.factorial_pos n₁])
              have hsq : ((sn n₁ : ℝ) * Real.sqrt (qn n₁)) ^ 2 < ((sn n₂ : ℝ) * Real.sqrt (qn n₂)) ^ 2 := by
                rw [mul_pow, mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n₁).le),
                  Real.sq_sqrt (by exact_mod_cast (qn_pos n₂).le)]
                linarith
              nlinarith [Real.sqrt_nonneg (qn n₁), Real.sqrt_nonneg (qn n₂)]
            have hlt_pow : (epsReal n₁ (by omega) hn6₁) ^ k₁ < (epsReal n₁ (by omega) hn6₁) ^ k₂ := by
              rw [hpow1, heps1_eq, hpow2]
              linarith [show (m₁ : ℝ) < (m₂ : ℝ) by exact_mod_cast hm1_lt_m2]
            have heps_gt1 : 1 < epsReal n₁ (by omega) hn6₁ := by
              have := (lemma_3_1_i n₁ (by omega) hn6₁).2.2.2.2.1 (by omega)
              have hpos : (0 : ℝ) < 0.2 * n₁ := by positivity
              exact (Real.log_pos_iff (by unfold epsReal; positivity)).mp (lt_trans hpos this)
            exact (pow_lt_pow_iff_right₀ heps_gt1).mp hlt_pow
          -- Now `k₂ - k₁ ≥ 1` and `k₁ ≤ 2`, so `2 * log(ε₁) ≥ log(n₁!) / 2`
          have heps_pow_ge : (n₁.factorial : ℝ) ^ (1 / 2 : ℝ) ≤ (epsReal n₁ (by omega) hn6₁) ^ 2 := by
            have h1 : (n₁.factorial : ℝ) ≤ (m₁ : ℝ) ^ 2 := by
              have : (n₁.factorial : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hsol₁.2.2
              linarith
            have h2 : (m₁ : ℝ) < (epsReal n₁ (by omega) hn6₁) ^ k₁ := by
              have hpow1 := pell_pow_real_eq (n := n₁) (by omega) hn6₁ k₁
              rw [← hmx₁, ← hsny₁] at hpow1
              have hpos : 0 < (sn n₁ : ℝ) * Real.sqrt (qn n₁) :=
                mul_pos (by exact_mod_cast sn_pos n₁) (Real.sqrt_pos.mpr (by exact_mod_cast qn_pos n₁))
              linarith
            have h3 : (epsReal n₁ (by omega) hn6₁) ^ k₁ ≤ (epsReal n₁ (by omega) hn6₁) ^ 2 := by
              have heps_gt1 : 1 ≤ epsReal n₁ (by omega) hn6₁ := by
                have := (lemma_3_1_i n₁ (by omega) hn6₁).2.2.2.2.1 (by omega)
                have hpos : (0 : ℝ) < 0.2 * n₁ := by positivity
                exact ((Real.log_pos_iff (by unfold epsReal; positivity)).mp (lt_trans hpos this)).le
              exact pow_le_pow_right₀ heps_gt1 (by rcases hk12 with h | h <;> omega)
            have h4 : (n₁.factorial : ℝ) ≤ ((epsReal n₁ (by omega) hn6₁) ^ 2) ^ 2 := by nlinarith
            rw [Real.sqrt_eq_rpow] at *
            rw [← Real.sqrt_eq_rpow]
            exact Real.sqrt_le_iff.mpr ⟨by unfold epsReal; positivity, h4⟩
          have hpow_diff : (epsReal n₁ (by omega) hn6₁) ^ 2 ≤ (epsReal n₁ (by omega) hn6₁) ^ (2 * (k₂ - k₁)) := by
            have heps_gt1 : 1 ≤ epsReal n₁ (by omega) hn6₁ := by
              have := (lemma_3_1_i n₁ (by omega) hn6₁).2.2.2.2.1 (by omega)
              have hpos : (0 : ℝ) < 0.2 * n₁ := by positivity
              exact ((Real.log_pos_iff (by unfold epsReal; positivity)).mp (lt_trans hpos this)).le
            exact pow_le_pow_right₀ heps_gt1 (by omega)
          have hprod_le : (n₂.factorial : ℝ) / (n₁.factorial : ℝ) ≤ (2 * (n₁ : ℝ)) ^ (n₂ - n₁) := by
            have hnat : n₂.factorial ≤ (2 * n₁) ^ (n₂ - n₁) * n₁.factorial := by
              have h1 : n₂.factorial = (∏ i ∈ Finset.Ioc n₁ n₂, i) * n₁.factorial := by
                clear hp_contra hp hnp1 hp_le_real hq_eq
                induction n₂, hn12.le using Nat.le_induction with
                | base => simp
                | succ m hm ih =>
                  rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top (by omega), ih]
                  ring
              rw [h1]
              refine Nat.mul_le_mul_right _ ?_
              calc ∏ i ∈ Finset.Ioc n₁ n₂, i
                  ≤ ∏ _i ∈ Finset.Ioc n₁ n₂, (2 * n₁) :=
                    Finset.prod_le_prod' fun i hi => by
                      have := (Finset.mem_Ioc.mp hi).2; omega
                _ = (2 * n₁) ^ (n₂ - n₁) := by simp [Nat.card_Ioc]
            rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n₁)]
            exact_mod_cast hnat
          have heps_k2_le : (epsReal n₁ (by omega) hn6₁) ^ (2 * k₂) ≤ 9 * (n₂.factorial : ℝ) := by
            have hpow2 := pell_pow_real_eq (n := n₂) (by omega) hn6₂ k₂
            rw [← hmx₂, ← hsny₂, ← heps1_eq] at hpow2
            have hm2_le : (m₂ : ℝ) ≤ 2 * Real.sqrt n₂.factorial := by
              have hm2 : (m₂ : ℝ) ^ 2 = (n₂.factorial : ℝ) + 1 := by exact_mod_cast hsol₂.2.2.symm
              have hfac1 : (1 : ℝ) ≤ n₂.factorial := by exact_mod_cast Nat.factorial_pos n₂
              have hsq : (m₂ : ℝ) ^ 2 ≤ (2 * Real.sqrt n₂.factorial) ^ 2 := by
                rw [mul_pow, Real.sq_sqrt (by positivity)]; linarith
              nlinarith [Real.sqrt_nonneg n₂.factorial]
            have hsn2_eq : (sn n₂ : ℝ) * Real.sqrt (qn n₂) = Real.sqrt n₂.factorial := by
              have hfac := factorial_eq_qn_mul_sn_sq n₂
              have hR : (n₂.factorial : ℝ) = (qn n₂ : ℝ) * (sn n₂ : ℝ) ^ 2 := by exact_mod_cast hfac
              rw [hR, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
            have hle3 : (epsReal n₁ (by omega) hn6₁) ^ k₂ ≤ 3 * Real.sqrt n₂.factorial := by
              rw [← hpow2]; linarith
            have hsq : ((epsReal n₁ (by omega) hn6₁) ^ k₂) ^ 2 ≤ (3 * Real.sqrt n₂.factorial) ^ 2 :=
              pow_le_pow_left₀ (by unfold epsReal; positivity) hle3 2
            rw [← pow_mul, mul_comm k₂ 2, mul_pow, Real.sq_sqrt (by positivity)] at hsq
            linarith
          have heps_k1_ge : (n₁.factorial : ℝ) ≤ (epsReal n₁ (by omega) hn6₁) ^ (2 * k₁) := by
            have hpow1 := pell_pow_real_eq (n := n₁) (by omega) hn6₁ k₁
            rw [← hmx₁, ← hsny₁] at hpow1
            have hm1_gt : (n₁.factorial : ℝ) ^ (1 / 2 : ℝ) ≤ (m₁ : ℝ) := by
              have hm2 : (n₁.factorial : ℝ) ≤ (m₁ : ℝ) ^ 2 := by
                have : (n₁.factorial : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hsol₁.2.2
                linarith
              rw [← Real.sqrt_eq_rpow]
              exact Real.sqrt_le_iff.mpr ⟨by positivity, hm2⟩
            have hge : (n₁.factorial : ℝ) ^ (1 / 2 : ℝ) ≤ (epsReal n₁ (by omega) hn6₁) ^ k₁ := by
              have hpos : 0 ≤ (sn n₁ : ℝ) * Real.sqrt (qn n₁) := by positivity
              linarith
            have hsq : ((n₁.factorial : ℝ) ^ (1 / 2 : ℝ)) ^ 2 ≤ ((epsReal n₁ (by omega) hn6₁) ^ k₁) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hge 2
            rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm k₁ 2] at hsq
            exact hsq
          have hpow_comb : (n₁.factorial : ℝ) ^ (1 / 2 : ℝ) ≤ 9 * (2 * (n₁ : ℝ)) ^ (n₂ - n₁) := by
            have h1 : (epsReal n₁ (by omega) hn6₁) ^ (2 * k₂) =
                (epsReal n₁ (by omega) hn6₁) ^ (2 * k₁) * (epsReal n₁ (by omega) hn6₁) ^ (2 * (k₂ - k₁)) := by
              rw [← pow_add, show 2 * k₁ + 2 * (k₂ - k₁) = 2 * k₂ by omega]
            have h2 : (n₁.factorial : ℝ) * (n₁.factorial : ℝ) ^ (1 / 2 : ℝ) ≤ 9 * (n₂.factorial : ℝ) := by
              calc (n₁.factorial : ℝ) * (n₁.factorial : ℝ) ^ (1 / 2 : ℝ)
                  ≤ (epsReal n₁ (by omega) hn6₁) ^ (2 * k₁) * (epsReal n₁ (by omega) hn6₁) ^ (2 * (k₂ - k₁)) :=
                    mul_le_mul heps_k1_ge (le_trans heps_pow_ge hpow_diff) (by positivity) (by positivity)
                _ = (epsReal n₁ (by omega) hn6₁) ^ (2 * k₂) := h1.symm
                _ ≤ 9 * (n₂.factorial : ℝ) := heps_k2_le
            have h3 : (n₁.factorial : ℝ) ^ (1 / 2 : ℝ) ≤ 9 * ((n₂.factorial : ℝ) / (n₁.factorial : ℝ)) := by
              rw [mul_div_assoc', le_div_iff₀ (by exact_mod_cast Nat.factorial_pos n₁)]
              linarith
            linarith
          have hfac_ge : (n₁ / 2 : ℕ) ^ (n₁ / 2) ≤ n₁.factorial := by
            have hsub : Finset.Icc (n₁ - n₁ / 2 + 1) n₁ ⊆ Finset.Icc 1 n₁ :=
              Finset.Icc_subset_Icc (by omega) le_rfl
            have hprod_le : (n₁ / 2 : ℕ) ^ (n₁ / 2) ≤ ∏ i ∈ Finset.Icc (n₁ - n₁ / 2 + 1) n₁, i := by
              calc (n₁ / 2 : ℕ) ^ (n₁ / 2)
                  = ∏ _i ∈ Finset.Icc (n₁ - n₁ / 2 + 1) n₁, (n₁ / 2 : ℕ) := by
                    simp [Nat.card_Icc]; congr 1; omega
                _ ≤ ∏ i ∈ Finset.Icc (n₁ - n₁ / 2 + 1) n₁, i :=
                    Finset.prod_le_prod' fun i hi => by
                      have := (Finset.mem_Icc.mp hi).1; omega
            have hfac_eq : ∏ i ∈ Finset.Icc 1 n₁, i = n₁.factorial := by
              simpa [Nat.factorial_eq_prod_range_add_one] using rfl
            rw [← hfac_eq]
            exact le_trans hprod_le (Finset.prod_le_prod_of_subset_of_one_le' hsub fun i _ _ => by omega)
          have hlog_comb := Real.log_le_log (by positivity) hpow_comb
          rw [Real.log_rpow (by exact_mod_cast Nat.factorial_pos n₁),
            Real.log_mul (by norm_num) (pow_ne_zero _ (by positivity)),
            Real.log_pow] at hlog_comb
          have hlog_fac_ge : ((n₁ / 2 : ℕ) : ℝ) * Real.log ((n₁ / 2 : ℕ) : ℝ) ≤ Real.log n₁.factorial := by
            have h1 := Real.log_le_log (pow_pos (by exact_mod_cast (by omega : 0 < n₁ / 2)) _) (by exact_mod_cast hfac_ge : ((n₁ / 2 : ℕ) : ℝ) ^ (n₁ / 2) ≤ n₁.factorial)
            rwa [Real.log_pow] at h1
          have hn1_half : (n₁ : ℝ) / 3 ≤ ((n₁ / 2 : ℕ) : ℝ) := by
            have : 2 * (n₁ / 2) ≥ n₁ - 1 := by omega
            have : (n₁ : ℝ) - 1 ≤ 2 * ((n₁ / 2 : ℕ) : ℝ) := by exact_mod_cast this
            have : (3 : ℝ) ≤ n₁ := by exact_mod_cast (by omega : 3 ≤ n₁)
            linarith
          have hlog_half : (1 / 2 : ℝ) * Real.log n₁ ≤ Real.log ((n₁ / 2 : ℕ) : ℝ) := by
            have h1 : Real.log ((n₁ : ℝ) / 3) ≤ Real.log ((n₁ / 2 : ℕ) : ℝ) :=
              Real.log_le_log (by positivity) hn1_half
            rw [Real.log_div (by positivity) (by norm_num)] at h1
            have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
            have hlogn1 : 4 ≤ Real.log n₁ := by
              have h10 : (Real.exp 4 : ℝ) < 10 ^ 9 := by
                have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
                calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
                  _ < 3 ^ 4 := pow_lt_pow_left₀ this (Real.exp_pos 1).le (by norm_num)
                  _ < 10 ^ 9 := by norm_num
              exact (Real.le_log_iff_exp_le (by positivity)).mpr (by exact_mod_cast (by linarith [show (10 ^ 9 : ℝ) < n₁ by exact_mod_cast hn1_small]))
            linarith
          have hlog_fac_ge2 : (1 / 12 : ℝ) * n₁ * Real.log n₁ ≤ (1 / 2 : ℝ) * Real.log n₁.factorial := by
            have : ((n₁ / 2 : ℕ) : ℝ) * ((1 / 2 : ℝ) * Real.log n₁) ≤ ((n₁ / 2 : ℕ) : ℝ) * Real.log ((n₁ / 2 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hlog_half (Nat.cast_nonneg _)
            have : (n₁ : ℝ) / 3 * ((1 / 2 : ℝ) * Real.log n₁) ≤ ((n₁ / 2 : ℕ) : ℝ) * ((1 / 2 : ℝ) * Real.log n₁) :=
              mul_le_mul_of_nonneg_right hn1_half (by positivity)
            linarith
          have hlog2n1 : Real.log (2 * (n₁ : ℝ)) ≤ 2 * Real.log n₁ := by
            rw [Real.log_mul (by norm_num) (by positivity)]
            have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
            have hlogn1 : 1 ≤ Real.log n₁ := by
              have : Real.exp 1 < (n₁ : ℝ) := by
                have := Real.exp_one_lt_d9
                have : (10 ^ 9 : ℝ) < n₁ := by exact_mod_cast hn1_small
                linarith
              exact (Real.le_log_iff_exp_le (by positivity)).mpr this.le
            linarith
          have hlog9 : Real.log 9 ≤ 9 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)]
          have hdiff_n : (n₁ : ℝ) / 16597 < ((n₂ - n₁ : ℕ) : ℝ) := by
            have hlogn1_pos : 0 < Real.log n₁ := by
              have : (10 ^ 9 : ℝ) < n₁ := by exact_mod_cast hn1_small
              exact Real.log_pos (by linarith)
            have h9_bd : Real.log 9 ≤ (1 / 24 : ℝ) * n₁ * Real.log n₁ := by
              have : (10 ^ 9 : ℝ) < n₁ := by exact_mod_cast hn1_small
              nlinarith
            have hle_diff : (1 / 24 : ℝ) * n₁ * Real.log n₁ ≤ ((n₂ - n₁ : ℕ) : ℝ) * (2 * Real.log n₁) := by
              have hmul : ((n₂ - n₁ : ℕ) : ℝ) * Real.log (2 * (n₁ : ℝ)) ≤ ((n₂ - n₁ : ℕ) : ℝ) * (2 * Real.log n₁) :=
                mul_le_mul_of_nonneg_left hlog2n1 (Nat.cast_nonneg _)
              linarith
            have hdiv : (n₁ : ℝ) / 48 ≤ ((n₂ - n₁ : ℕ) : ℝ) := by
              have : ((n₁ : ℝ) / 48 - ((n₂ - n₁ : ℕ) : ℝ)) * (2 * Real.log n₁) ≤ 0 := by linarith
              exact le_of_sub_nonpos (nonpos_of_mul_nonpos_left this (by positivity))
            have : (n₁ : ℝ) / 16597 < (n₁ : ℝ) / 48 := by
              have : (0 : ℝ) < n₁ := by positivity
              linarith
            linarith
          have hpn2 : p ≤ n₂ := by
            have h1 : (p : ℝ) ≤ (n₁ : ℝ) + (n₁ : ℝ) / 16597 := hp_le_real
            have h2 : (n₁ : ℝ) + ((n₂ - n₁ : ℕ) : ℝ) = n₂ := by
              have : n₁ + (n₂ - n₁) = n₂ := Nat.add_sub_cancel' hn12.le
              exact_mod_cast this
            exact_mod_cast (by linarith : (p : ℝ) ≤ n₂)
          have hn2_2p : n₂ < 2 * p := by omega
          exact hp_contra p hp hnp1 hpn2 hn2_2p
  exact ⟨h4_eq, h5_eq, h7_eq, hpart4, hpart5, hpart6⟩

theorem remark_3_3 :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn8 : 8 ≤ n) → (hN : N₀ ≤ n) → (hsol : IsBrocardSol n m) →
      ∀ ell : ℕ, ell.Prime → 3 ≤ ell → ¬ ell ∣ pellIndex (by omega) hsol := by
  obtain ⟨N₀, hN₀, hmain⟩ := theorem_1_1.2.2.2.1
  refine ⟨N₀, hN₀, fun n m hn8 hN hsol ell hell hell3 hdvd => ?_⟩
  rcases hmain n m hn8 hN hsol with hk1 | hk2
  · rw [hk1] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · rw [hk2] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem prop_3_4 (n m : ℕ) (hn : 8 ≤ n) (hsol : IsBrocardSol n m)
    (hk : pellIndex (by omega) hsol = 1 ∨ pellIndex (by omega) hsol = 2)
    (hn6 : n ≠ 6) (p : ℕ) (hp : p.Prime)
    (hp_lo : (n : ℝ) / 3 < (p : ℝ)) (hp_hi : (p : ℝ) ≤ (n : ℝ) / 2) :
    ¬ p ∣ qn n ∧ padicValNat p (sn n) = 1 ∧
    let α := alphaRank n p (by omega) hn6
    (α ∣ pellIndex (by omega) hsol) ∧ (α = 1 ∨ α = 2) ∧
    padicValNat p (Yr n (by omega) hn6 α) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have : (8 : ℝ) / 3 < p := lt_of_le_of_lt (by
      have : (8 : ℝ) ≤ n := by exact_mod_cast hn
      linarith) hp_lo
    have hp_gt2 : 2 < p := by exact_mod_cast (by linarith : (2 : ℝ) < p)
    omega
  have h2p : 2 * p ≤ n := by
    have : (p : ℝ) * 2 ≤ n := by linarith
    exact_mod_cast this
  have hn_lt_3p : n < 3 * p := by
    have : (n : ℝ) < 3 * p := by linarith
    exact_mod_cast this
  have hnsq : n < p ^ 2 := by
    by_cases hn9 : 9 ≤ n
    · have hp_ge3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have : (n : ℝ) < (p : ℝ) ^ 2 := by nlinarith
      exact_mod_cast this
    · have hn8' : n = 8 := by omega
      subst hn8'
      have hp_le4 : p ≤ 4 := by omega
      have : p = 3 ∨ p = 4 := by omega
      rcases this with rfl | rfl
      · norm_num
      · exact absurd hp (by decide)
  have hv_fac : padicValNat p n.factorial = 2 := by
    rw [padicValNat_factorial_of_lt_sq hp hnsq]
    rw [Nat.div_eq_iff_eq_mul_add_mod]
    · omega
    · exact hp.pos
  have hp_ndvd_qn : ¬ p ∣ qn n := by
    intro hdvd
    rw [qn_eq_prod_Podd] at hdvd
    have hmem : p ∈ Podd n := by
      rcases hp.dvd_finset_prod_iff.mp hdvd with ⟨q, hq, hqp⟩
      have hq_prime : q.Prime := (Finset.mem_filter.mp hq).2.1
      have hq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hqp
      rwa [hq_eq]
    have hodd := (Finset.mem_filter.mp hmem).2.2
    rw [hv_fac] at hodd
    exact hodd (by decide)
  have hfac_eq := factorial_eq_qn_mul_sn_sq n
  have hval_fac : padicValNat p n.factorial = padicValNat p (qn n) + 2 * padicValNat p (sn n) := by
    rw [hfac_eq, padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'),
      padicValNat.pow 2 (sn_pos n).ne']
  have hval_qn0 : padicValNat p (qn n) = 0 := padicValNat.eq_zero_of_not_dvd hp_ndvd_qn
  have hv_sn : padicValNat p (sn n) = 1 := by omega
  have hp_dvd_sn : p ∣ sn n := (padicValNat_dvd_iff_le (sn_pos n).ne').mpr (by omega)
  set k := pellIndex (by omega : 4 ≤ n) hsol
  obtain ⟨hn6', hk1, _, hsny⟩ := pellIndex_spec (by omega : 4 ≤ n) hsol
  have hYr_k : Yr n (by omega) hn6 k = sn n := by
    have hZ : (Yr n (by omega) hn6 k : ℤ) = (sn n : ℤ) := by
      rw [Yr_eq, ← hsny]
    exact_mod_cast hZ
  have hp_dvd_Yrk : p ∣ Yr n (by omega) hn6 k := hYr_k ▸ hp_dvd_sn
  obtain ⟨hα1, _, hlem⟩ := lemma_3_2_ii n p (by omega) hn6 hp hp3 hp_ndvd_qn
  set α := alphaRank n p (by omega) hn6
  have hα_dvd_k : α ∣ k := (hlem k hk1).1.mp hp_dvd_Yrk
  have hα_12 : α = 1 ∨ α = 2 := by
    rcases hk with hk_1 | hk_2
    · rw [hk_1] at hα_dvd_k
      exact Or.inl (Nat.eq_one_of_dvd_one hα_dvd_k)
    · rw [hk_2] at hα_dvd_k
      have hle : α ≤ 2 := Nat.le_of_dvd (by norm_num) hα_dvd_k
      omega
  have hval_Yrk := (hlem k hk1).2 hα_dvd_k
  rw [hYr_k, hv_sn] at hval_Yrk
  have hp_dvd_Yα : p ∣ Yr n (by omega) hn6 α := (hlem α hα1).1.mpr dvd_rfl
  have hv_Yα_ge1 : 1 ≤ padicValNat p (Yr n (by omega) hn6 α) :=
    (padicValNat_dvd_iff_le (Yr_pos (by omega) hn6 hα1).ne').mp hp_dvd_Yα
  have hv_Yα : padicValNat p (Yr n (by omega) hn6 α) = 1 := by omega
  exact ⟨hp_ndvd_qn, hv_sn, hα_dvd_k, hα_12, hv_Yα⟩

end

end BrocardFormalization

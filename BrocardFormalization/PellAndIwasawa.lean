import Mathlib
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.PellChebyshev
import BrocardFormalization.PellCapacity

open Real Complex Nat Finset

namespace BrocardFormalization

noncomputable section

theorem theorem_1_2 :
    (∀ n m : ℕ, (hn116 : 116 ≤ n) → (hsol : IsBrocardSol n m) →
      (∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < p ∧ (p : ℝ) ≤ (n : ℝ) / 4) ∧
      (∀ p : ℕ, p.Prime → 5 ≤ p → p ∈ Peven n →
        ¬ p ∣ pellIndex (by omega) hsol → 4 ≤ padicValNat p n.factorial →
        let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) (by omega)⟩
        ¬ p ∣ (fundDiscrQuad (qn n : ℤ)).natAbs ∧
        ∃ vp_Lp1 : ℤ, ∃ lamP : ℕ, 1 ≤ vp_Lp1 ∧ 1 ≤ lamP ∧
          (∃ vp_Rtilde muP : ℕ,
            muP = 0 ∧
            (vp_Lp1 = (padicValNat p (NumberField.classNumber (QuadField (qn n : ℚ))) : ℤ) +
              (vp_Rtilde : ℤ) - 1) ∧
            1 ≤ lamP))) ∧
    (Tendsto (fun n : ℕ =>
      (((Finset.Icc 5 n).filter fun p => p.Prime ∧ 2 ∣ padicValNat p n.factorial ∧
        4 ≤ padicValNat p n.factorial).card : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (5 / 6 - Real.log 2))) ∧
    ((∀ n m : ℕ, (hn116 : 116 ≤ n) → IsBrocardSol n m →
        ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < p ∧ (p : ℝ) ≤ (n : ℝ) / 4 ∧
          let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) (by omega)⟩
          ∀ (vp_Rtilde vp_Lp1 : ℤ) (lamP muP : ℕ),
            (vp_Lp1 = (padicValNat p (NumberField.classNumber (QuadField (qn n : ℚ))) : ℤ) +
              vp_Rtilde - 1) →
            (1 ≤ vp_Lp1 → 1 ≤ lamP) →
            lamP = 0) →
      ∀ n m : ℕ, IsBrocardSol n m → (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71)) := by
  have hpart1 : ∀ n m : ℕ, (hn116 : 116 ≤ n) → (hsol : IsBrocardSol n m) →
      (∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < p ∧ (p : ℝ) ≤ (n : ℝ) / 4) ∧
      (∀ p : ℕ, p.Prime → 5 ≤ p → p ∈ Peven n →
        ¬ p ∣ pellIndex (by omega) hsol → 4 ≤ padicValNat p n.factorial →
        let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) (by omega)⟩
        ¬ p ∣ (fundDiscrQuad (qn n : ℤ)).natAbs ∧
        ∃ vp_Lp1 : ℤ, ∃ lamP : ℕ, 1 ≤ vp_Lp1 ∧ 1 ≤ lamP ∧
          (∃ vp_Rtilde muP : ℕ,
            muP = 0 ∧
            (vp_Lp1 = (padicValNat p (NumberField.classNumber (QuadField (qn n : ℚ))) : ℤ) +
              (vp_Rtilde : ℤ) - 1) ∧
            1 ≤ lamP)) := by
    intro n m hn116 hsol
    constructor
    · by_cases hn125 : 125 ≤ n
      · obtain ⟨p, hp, hlo, hhi⟩ := nagura_prime_interval ((n : ℝ) / 5) (by
          have : (125 : ℝ) ≤ n := by exact_mod_cast hn125
          linarith)
        exact ⟨p, hp, hlo, by linarith⟩
      · refine ⟨29, by decide, ?_, ?_⟩
        · have : (n : ℝ) ≤ 124 := by exact_mod_cast (by omega : n ≤ 124)
          linarith
        · have : (116 : ℝ) ≤ n := by exact_mod_cast hn116
          linarith
    · intro p hp hp5 hp_even hp_ndvd_k hp_val4
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) (by omega)⟩
      have hp_ndvd_qn : ¬ p ∣ qn n := by
        intro hdvd
        rw [qn_eq_prod_Podd] at hdvd
        rcases hp.dvd_finset_prod_iff.mp hdvd with ⟨q, hq, hpq⟩
        have hq_prime : q.Prime := (Finset.mem_filter.mp hq).2.1
        have hq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq
        subst hq_eq
        have hodd := (Finset.mem_filter.mp hq).2.2
        have heven := (Finset.mem_filter.mp hp_even).2.2
        omega
      have hp_ndvd_D : ¬ p ∣ (fundDiscrQuad (qn n : ℤ)).natAbs := by
        intro hdvd
        have hdvdZ : (p : ℤ) ∣ fundDiscrQuad (qn n : ℤ) := Int.natCast_dvd.mpr hdvd
        unfold fundDiscrQuad at hdvdZ
        split_ifs at hdvdZ
        · exact hp_ndvd_qn (by exact_mod_cast hdvdZ)
        · have hcop : IsCoprime (p : ℤ) 4 := by
            refine (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr fun h4 => ?_
            have := Int.le_of_dvd (by norm_num) h4
            omega
          exact hp_ndvd_qn (by exact_mod_cast hcop.dvd_of_dvd_mul_left hdvdZ)
      have hqn1 : 1 < qn n := by
        obtain ⟨q, hq, hdvd, _⟩ := (lemma_3_1_i n (by omega) (by omega)).1
        exact lt_of_lt_of_le (by have := hq.two_le; omega) (Nat.le_of_dvd (qn_pos n) hdvd)
      obtain ⟨vp_Rtilde, vp_Lp1, lamP, muP, hR, hL, hmu, hMW⟩ :=
        iwasawa_kubota_leopoldt_package (qn n) p hp hp5 (squarefree_qn n) hqn1 hp_ndvd_qn
      obtain ⟨hn6, hk1, hmx, hsny⟩ := pellIndex_spec (by omega : 4 ≤ n) hsol
      set k := pellIndex (by omega : 4 ≤ n) hsol
      have hv_sn : 2 ≤ padicValNat p (sn n) := by
        have hfac := factorial_eq_qn_mul_sn_sq n
        have hval : padicValNat p n.factorial = padicValNat p (qn n) + 2 * padicValNat p (sn n) := by
          rw [hfac, padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'),
            padicValNat.pow 2 (sn_pos n).ne']
        have hq0 : padicValNat p (qn n) = 0 := padicValNat.eq_zero_of_not_dvd hp_ndvd_qn
        omega
      have hR_eq : vp_Rtilde = (padicValNat p (sn n) : ℤ) := by
        refine hR (pellFundUnit n (by omega) hn6) (pellFundUnit_isFundamental (by omega) hn6)
          k m (sn n) 1 (Or.inl rfl) (by simpa using hp_ndvd_k) ?_ hmx hsny (by omega)
        have hfac : (n.factorial : ℤ) = (qn n : ℤ) * (sn n : ℤ) ^ 2 := by exact_mod_cast factorial_eq_qn_mul_sn_sq n
        have hm2 : (n.factorial : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hsol.2.2
        linarith
      have hvp_Lp1_ge1 : 1 ≤ vp_Lp1 := by
        have : (0 : ℤ) ≤ padicValNat p (NumberField.classNumber (QuadField (qn n : ℚ))) := Nat.cast_nonneg _
        omega
      have hlam_ge1 : 1 ≤ lamP := hMW hvp_Lp1_ge1
      refine ⟨hp_ndvd_D, vp_Lp1, lamP, hvp_Lp1_ge1, hlam_ge1, padicValNat p (sn n), muP, hmu, ?_, hlam_ge1⟩
      omega
  have hpart2 : Tendsto (fun n : ℕ =>
      (((Finset.Icc 5 n).filter fun p => p.Prime ∧ 2 ∣ padicValNat p n.factorial ∧
        4 ≤ padicValNat p n.factorial).card : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (5 / 6 - Real.log 2)) := by
    obtain ⟨c₁, C₁, hc₁, hC₁, hpnt⟩ := deLaValleePoussin_pnt
    have hpc_eq : ∀ m : ℕ, (Nat.primeCounting m : ℝ) = ((Finset.Icc 2 m).filter Nat.Prime).card := by
      intro m; congr 1
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨fun ⟨a, b⟩ => ⟨⟨b.two_le, Nat.lt_succ_iff.mp a⟩, b⟩, fun ⟨⟨_, a⟩, b⟩ => ⟨Nat.lt_succ_iff.mpr a, b⟩⟩
    have h_pi_asymp : Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
      have h_li_asymp : Tendsto (fun n : ℕ => (∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        set δ : ℝ := min (ε / 16) (1 / 4)
        have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
        have h1 : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
          have hlo : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu; exact div_nonneg (Real.log_nonneg hu) (by positivity)) ?_
              ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2)
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
            have hr2 : 0 < u ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hu _
            have hlog2 : Real.log (u ^ (1 / 2 : ℝ)) ≤ u ^ (1 / 2 : ℝ) := by linarith [Real.log_le_sub_one_of_pos hr2]
            rw [Real.log_rpow hu] at hlog2
            calc Real.log u / u ≤ (2 * u ^ (1 / 2 : ℝ)) / u := div_le_div_of_nonneg_right (by linarith) hu.le
              _ = 2 * u ^ (-(1 / 2 : ℝ)) := by
                  rw [mul_div_assoc, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hu]; norm_num
          exact hlo.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        have h2 : Tendsto (fun n : ℕ => 1 / (Real.log 2 * Real.log n)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (Real.log_pos (by norm_num)))
        have h5 : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        have h_b2 : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) / (Real.log n) ^ 2 := by
          have hlo : Tendsto (fun u : ℝ => u / (Real.log u) ^ 2) atTop atTop := by
            have hinv : Tendsto (fun u : ℝ => (Real.log u) ^ 2 / u) atTop (𝓝 0) := by
              refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu; positivity) ?_
                ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 16)
              filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
              have hu_pos : 0 < u := by linarith
              have hr4 : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu_pos _
              have hlog4 : Real.log (u ^ (1 / 4 : ℝ)) ≤ u ^ (1 / 4 : ℝ) := by linarith [Real.log_le_sub_one_of_pos hr4]
              rw [Real.log_rpow hu_pos] at hlog4
              have hsq : (Real.log u) ^ 2 ≤ (4 * u ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (Real.log_nonneg hu) (by linarith) 2
              calc (Real.log u) ^ 2 / u ≤ (16 * u ^ (1 / 2 : ℝ)) / u := by
                    refine div_le_div_of_nonneg_right ?_ hu_pos.le
                    calc (Real.log u) ^ 2 ≤ (4 * u ^ (1 / 4 : ℝ)) ^ 2 := hsq
                      _ = 16 * (u ^ (1 / 4 : ℝ)) ^ 2 := by ring
                      _ = 16 * u ^ (1 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hu_pos.le]; norm_num
                _ = 16 * u ^ (-(1 / 2 : ℝ)) := by
                    rw [mul_div_assoc, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hu_pos]; norm_num
            have hinv' : Tendsto (fun u : ℝ => ((Real.log u) ^ 2 / u)⁻¹) atTop atTop :=
              Tendsto.inv_tendsto_nhdsGT_zero (by
                refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinv ?_
                filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
                exact div_pos (pow_pos (Real.log_pos hu) 2) (by linarith))
            exact hinv'.congr' (by
              filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
              rw [inv_div])
          exact (hlo.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
          h_b2,
          h1.eventually (Metric.ball_mem_nhds 0 hδ),
          h2.eventually (Metric.ball_mem_nhds 0 (div_pos hε (by norm_num))),
          h5.eventually (Metric.ball_mem_nhds 0 (div_pos hε (by norm_num))),
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2] with n hn16 h2b hb1 hb2 hb5 hlog2
        have hb1' : Real.log (Real.log n) / Real.log n < δ := by
          simpa [Real.dist_eq] using lt_of_le_of_lt (le_abs_self _) hb1
        have hb2' : 1 / (Real.log 2 * Real.log n) < ε / 4 := by
          simpa [Real.dist_eq] using lt_of_le_of_lt (le_abs_self _) hb2
        have hb5' : (Real.log n)⁻¹ < ε / 4 := by
          simpa [Real.dist_eq] using lt_of_le_of_lt (le_abs_self _) hb5
        set b : ℝ := (n : ℝ) / (Real.log n) ^ 2
        set a : ℝ := (n : ℝ) / Real.log n
        have hlogn_pos : 0 < Real.log n := by linarith
        have hb_le : b ≤ n := div_le_self (by linarith) (one_le_pow₀ (by linarith))
        have ha_pos : 0 < a := by positivity
        have hint1 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 2 b := by
          refine ContinuousOn.intervalIntegrable fun t ht => ?_
          rw [Set.uIcc_of_le h2b] at ht
          exact (Real.continuousAt_log (by linarith [ht.1])).inv₀ (Real.log_pos (by linarith [ht.1])).ne' |>.continuousWithinAt
        have hint2 : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume b n := by
          refine ContinuousOn.intervalIntegrable fun t ht => ?_
          rw [Set.uIcc_of_le hb_le] at ht
          exact (Real.continuousAt_log (by linarith [ht.1])).inv₀ (Real.log_pos (by linarith [ht.1])).ne' |>.continuousWithinAt
        rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
        have h1_nn : 0 ≤ ∫ t in (2 : ℝ)..b, (Real.log t)⁻¹ :=
          intervalIntegral.integral_nonneg h2b fun t ht => inv_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
        have h1_ub : ∫ t in (2 : ℝ)..b, (Real.log t)⁻¹ ≤ b / Real.log 2 := by
          have hbd := intervalIntegral.integral_mono_on h2b hint1 (continuous_const.intervalIntegrable _ _) fun t ht =>
            inv_anti₀ (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) ht.1)
          rw [intervalIntegral.integral_const, smul_eq_mul] at hbd
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          calc ∫ t in (2 : ℝ)..b, (Real.log t)⁻¹ ≤ (b - 2) * (Real.log 2)⁻¹ := hbd
            _ ≤ b * (Real.log 2)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hlog2.le)
            _ = b / Real.log 2 := (div_eq_mul_inv _ _).symm
        have hlogb : Real.log b = Real.log n - 2 * Real.log (Real.log n) := by
          rw [Real.log_div (by linarith) (pow_pos hlogn_pos 2).ne', Real.log_pow]
        have hlogb_ge : (1 / 2 : ℝ) * Real.log n ≤ Real.log b := by
          have : Real.log (Real.log n) ≤ (1 / 4 : ℝ) * Real.log n := by
            have hlt : Real.log (Real.log n) / Real.log n < 1 / 4 := lt_of_lt_of_le hb1' (min_le_right _ _)
            exact (div_lt_iff₀ hlogn_pos).mp hlt |>.le
          linarith
        have hlogb_pos : 0 < Real.log b := by linarith
        have h2_lo : ((n : ℝ) - b) / Real.log n ≤ ∫ t in b..(n : ℝ), (Real.log t)⁻¹ := by
          have hbd := intervalIntegral.integral_mono_on hb_le (continuous_const.intervalIntegrable _ _) hint2 fun t ht =>
            inv_anti₀ (Real.log_pos (by linarith [ht.1])) (Real.log_le_log (by linarith [ht.1]) ht.2)
          rw [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at hbd
          exact hbd
        have h2_hi : ∫ t in b..(n : ℝ), (Real.log t)⁻¹ ≤ ((n : ℝ) - b) / Real.log b := by
          have hbd := intervalIntegral.integral_mono_on hb_le hint2 (continuous_const.intervalIntegrable _ _) fun t ht =>
            inv_anti₀ hlogb_pos (Real.log_le_log (by linarith) ht.1)
          rw [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at hbd
          exact hbd
        have h1_div : (∫ t in (2 : ℝ)..b, (Real.log t)⁻¹) / a ≤ 1 / (Real.log 2 * Real.log n) := by
          have heq : (b / Real.log 2) / a = 1 / (Real.log 2 * Real.log n) := by
            simp only [a, b]; field_simp [hlogn_pos.ne', (by linarith : (n : ℝ) ≠ 0), (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
          exact le_trans (div_le_div_of_nonneg_right h1_ub ha_pos.le) (le_of_eq heq)
        have hlo_div : 1 - (Real.log n)⁻¹ ≤ (((n : ℝ) - b) / Real.log n) / a := by
          have : (((n : ℝ) - b) / Real.log n) / a = 1 - (Real.log n)⁻¹ := by
            simp only [a, b]; field_simp [hlogn_pos.ne', (by linarith : (n : ℝ) ≠ 0)]
          linarith
        have hhi_div : (((n : ℝ) - b) / Real.log b) / a ≤ Real.log n / Real.log b := by
          have h1 : (n : ℝ) - b ≤ n := by linarith
          have h2 : (((n : ℝ) - b) / Real.log b) / a ≤ ((n : ℝ) / Real.log b) / a :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h1 hlogb_pos.le) ha_pos.le
          have heq : ((n : ℝ) / Real.log b) / a = Real.log n / Real.log b := by
            simp only [a]; field_simp [hlogn_pos.ne', hlogb_pos.ne', (by linarith : (n : ℝ) ≠ 0)]
          linarith
        have h_ratio : Real.log n / Real.log b - 1 < ε / 4 := by
          have h1 : Real.log n / Real.log b - 1 = 2 * Real.log (Real.log n) / Real.log b := by
            rw [hlogb]; field_simp [hlogb_pos.ne']; ring
          have hlog_log_nn : 0 ≤ Real.log (Real.log n) := Real.log_nonneg (by linarith)
          have h2 : 2 * Real.log (Real.log n) / Real.log b ≤ 4 * (Real.log (Real.log n) / Real.log n) := by
            calc 2 * Real.log (Real.log n) / Real.log b
                ≤ 2 * Real.log (Real.log n) / ((1 / 2 : ℝ) * Real.log n) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hlogb_ge
              _ = 4 * (Real.log (Real.log n) / Real.log n) := by ring
          have hlt : Real.log (Real.log n) / Real.log n < ε / 16 := lt_of_lt_of_le hb1' (min_le_left _ _)
          linarith
        rw [Real.dist_eq, abs_lt, add_div]
        constructor
        · have h0 : 0 ≤ (∫ t in (2 : ℝ)..b, (Real.log t)⁻¹) / a := div_nonneg h1_nn ha_pos.le
          have h2 : (((n : ℝ) - b) / Real.log n) / a ≤ (∫ t in b..(n : ℝ), (Real.log t)⁻¹) / a :=
            div_le_div_of_nonneg_right h2_lo ha_pos.le
          linarith
        · have h2 : (∫ t in b..(n : ℝ), (Real.log t)⁻¹) / a ≤ (((n : ℝ) - b) / Real.log b) / a :=
            div_le_div_of_nonneg_right h2_hi ha_pos.le
          linarith
      have h_err : Tendsto (fun n : ℕ =>
          ((Nat.primeCounting n : ℝ) - ∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹) / ((n : ℝ) / Real.log n)) atTop (𝓝 0) := by
        have h_exp0 : Tendsto (fun n : ℕ => C₁ * Real.log n * Real.exp (-c₁ * Real.sqrt (Real.log n))) atTop (𝓝 0) := by
          have h0 : Tendsto (fun x : ℝ => (C₁ / c₁ ^ 2) * (x ^ 2 * Real.exp (-x))) atTop (𝓝 0) := by
            simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (C₁ / c₁ ^ 2)
          have harg : Tendsto (fun n : ℕ => c₁ * Real.sqrt (Real.log n)) atTop atTop := by
            rw [Filter.tendsto_atTop_atTop]
            intro b
            have hb : ∀ᶠ n : ℕ in atTop, (max b 0 / c₁) ^ 2 ≤ Real.log n :=
              (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
            obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
            refine ⟨N, fun n hn => ?_⟩
            have h1 : max b 0 / c₁ ≤ Real.sqrt (Real.log n) := by
              rw [← Real.sqrt_sq (div_nonneg (le_max_right b 0) hc₁.le)]
              exact Real.sqrt_le_sqrt (hN n hn)
            calc b ≤ max b 0 := le_max_left b 0
              _ = c₁ * (max b 0 / c₁) := by field_simp [hc₁.ne']
              _ ≤ c₁ * Real.sqrt (Real.log n) := mul_le_mul_of_nonneg_left h1 hc₁.le
          refine (h0.comp harg).congr' ?_
          filter_upwards [eventually_ge_atTop 2] with n hn2
          have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
          have hsq : (c₁ * Real.sqrt (Real.log n)) ^ 2 = c₁ ^ 2 * Real.log n := by
            rw [mul_pow, Real.sq_sqrt hlog_nn]
          dsimp only [Function.comp_def]
          rw [hsq, neg_mul]
          field_simp [hc₁.ne']
        refine squeeze_zero_norm' ?_ h_exp0
        filter_upwards [eventually_ge_atTop 2] with n hn2
        have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have hn_pos : (0 : ℝ) < n := by positivity
        have hpnt_n := (hpnt (n : ℝ) (by exact_mod_cast hn2)).2
        rw [Nat.floor_natCast] at hpnt_n
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (div_pos hn_pos hlog_pos)]
        calc |(Nat.primeCounting n : ℝ) - ∫ t in (2 : ℝ)..(n : ℝ), (Real.log t)⁻¹| / ((n : ℝ) / Real.log n)
            ≤ (C₁ * n * Real.exp (-c₁ * Real.sqrt (Real.log n))) / ((n : ℝ) / Real.log n) :=
              div_le_div_of_nonneg_right hpnt_n (by positivity)
          _ = C₁ * Real.log n * Real.exp (-c₁ * Real.sqrt (Real.log n)) := by
              field_simp [hn_pos.ne', hlog_pos.ne']
      have hsum := h_li_asymp.add h_err
      simp only [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn2
      ring
    have h_pi_div_ratio : ∀ d : ℕ, 1 ≤ d →
        Tendsto (fun n : ℕ => (Nat.primeCounting (n / d) : ℝ) / (Nat.primeCounting n : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
      intro d hd
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
      have h_sub : Tendsto (fun n : ℕ => n / d) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro b
        refine ⟨b * d, fun n hn => (Nat.le_div_iff_mul_le hd).mpr hn⟩
      have h1 : Tendsto (fun n : ℕ => (Nat.primeCounting (n / d) : ℝ) / (((n / d : ℕ) : ℝ) / Real.log (n / d : ℕ))) atTop (𝓝 1) :=
        h_pi_asymp.comp h_sub
      have h_scale : Tendsto (fun n : ℕ =>
          ((((n / d : ℕ) : ℝ) / Real.log (n / d : ℕ)) / ((n : ℝ) / Real.log n))) atTop (𝓝 (1 / (d : ℝ))) := by
        have hA' : Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / (n : ℝ) - 1 / (d : ℝ)) atTop (𝓝 0) := by
          refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0))
          filter_upwards [eventually_ge_atTop 1] with n hn
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
          have h1 : (n : ℝ) - d < ((n / d : ℕ) : ℝ) * d := by
            have : n < (n / d + 1) * d := by rw [mul_comm]; exact Nat.lt_mul_div_succ n hd
            have : (n : ℝ) < (((n / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast this
            linarith
          have h2 : ((n / d : ℕ) : ℝ) * d ≤ n := by exact_mod_cast Nat.div_mul_le_self n d
          rw [Real.norm_eq_abs, abs_le]
          constructor
          · have : ((n / d : ℕ) : ℝ) / n - 1 / d = (((n / d : ℕ) : ℝ) * d - n) / (n * d) := by field_simp [hn_pos.ne', hd_pos.ne']
            rw [this, neg_le_div_iff₀ (mul_pos hn_pos hd_pos)]
            nlinarith
          · have : ((n / d : ℕ) : ℝ) / n - 1 / d = (((n / d : ℕ) : ℝ) * d - n) / (n * d) := by field_simp [hn_pos.ne', hd_pos.ne']
            rw [this, div_le_iff₀ (mul_pos hn_pos hd_pos)]
            nlinarith
        have hA'' : Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
          simpa using hA'.add_const (1 / (d : ℝ))
        have hB : Tendsto (fun n : ℕ => Real.log n / Real.log (n / d : ℕ)) atTop (𝓝 1) := by
          have hB' : Tendsto (fun n : ℕ => Real.log (n / d : ℕ) / Real.log n) atTop (𝓝 1) := by
            have h1 : Tendsto (fun n : ℕ => Real.log (((n / d : ℕ) : ℝ) / (n : ℝ)) / Real.log n + 1) atTop (𝓝 (0 + 1)) := by
              refine Tendsto.add ?_ tendsto_const_nhds
              have hlim : Tendsto (fun n : ℕ => Real.log (((n / d : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 (Real.log (1 / (d : ℝ)))) :=
                (Real.continuousAt_log (by positivity)).tendsto.comp hA''
              exact hlim.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
            simp only [zero_add] at h1
            refine h1.congr' ?_
            filter_upwards [eventually_ge_atTop (2 * d)] with n hn
            have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
            have hnd_pos : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos (by omega) hd
            have hlog_ne : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
            rw [Real.log_div hnd_pos.ne' hn_pos.ne']
            field_simp [hlog_ne]; ring
          simpa using hB'.inv₀ one_ne_zero
        have hmul := hA''.mul hB
        simp only [mul_one] at hmul
        refine hmul.congr' ?_
        filter_upwards [eventually_ge_atTop (2 * d)] with n hn
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hnd_ge2 : 2 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
        have hlog1 : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
        have hlog2 : Real.log (n / d : ℕ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n / d))).ne'
        field_simp [hn_pos.ne', hlog1, hlog2]
      have hquot := (h1.mul h_scale).div h_pi_asymp one_ne_zero
      simp only [one_mul, div_one] at hquot
      refine hquot.congr' ?_
      filter_upwards [eventually_ge_atTop (2 * d)] with n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hnd_ge2 : 2 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
      have hnd_pos : (0 : ℝ) < (n / d : ℕ) := by exact_mod_cast (by omega : 0 < n / d)
      have hlog1 : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
      have hlog2 : Real.log (n / d : ℕ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n / d))).ne'
      have hpi_ne : (Nat.primeCounting n : ℝ) ≠ 0 := by
        have : 1 ≤ Nat.primeCounting n := by
          rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
          exact Finset.card_pos.mpr ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
        exact_mod_cast (by omega : Nat.primeCounting n ≠ 0)
      field_simp [hn_pos.ne', hnd_pos.ne', hlog1, hlog2, hpi_ne]
    have h_sqrt_zero : Tendsto (fun n : ℕ => ((Nat.sqrt n + 2 : ℕ) : ℝ) / (Nat.primeCounting n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((Nat.sqrt n + 2 : ℕ) : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 0) := by
        have hlo : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ) + 2) * Real.log x / x) atTop (𝓝 0) := by
          have hA : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
            refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx; exact div_nonneg (Real.log_nonneg hx) (by positivity)) ?_
              ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4)
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
            have hr4 : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
            have hlog4 : Real.log (x ^ (1 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) := by linarith [Real.log_le_sub_one_of_pos hr4]
            rw [Real.log_rpow hx] at hlog4
            calc Real.log x / x ^ (1 / 2 : ℝ) ≤ (4 * x ^ (1 / 4 : ℝ)) / x ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
              _ = 4 * x ^ (-(1 / 4 : ℝ)) := by rw [mul_div_assoc, div_eq_mul_inv, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]; norm_num
          have hB : Tendsto (fun x : ℝ => 2 * Real.log x / x) atTop (𝓝 0) := by
            have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
              refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx; exact div_nonneg (Real.log_nonneg hx) (by positivity)) ?_
                ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2)
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
              have hr2 : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
              have hlog2 : Real.log (x ^ (1 / 2 : ℝ)) ≤ x ^ (1 / 2 : ℝ) := by linarith [Real.log_le_sub_one_of_pos hr2]
              rw [Real.log_rpow hx] at hlog2
              calc Real.log x / x ≤ (2 * x ^ (1 / 2 : ℝ)) / x := div_le_div_of_nonneg_right (by linarith) hx.le
                _ = 2 * x ^ (-(1 / 2 : ℝ)) := by rw [mul_div_assoc, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx]; norm_num
            simpa using h0.const_mul 2
          have hAB := hA.add hB
          simp only [add_zero] at hAB
          refine hAB.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          have hx12 : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
            rw [← Real.rpow_add hx]; norm_num
          field_simp [hx.ne', (Real.rpow_pos_of_pos hx (1 / 2 : ℝ)).ne']
          rw [mul_add, mul_assoc, hx12]; ring
        refine squeeze_zero' ?_ ?_ (hlo.comp tendsto_natCast_atTop_atTop)
        · filter_upwards [eventually_ge_atTop 2] with n hn2
          have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
          positivity
        · filter_upwards [eventually_ge_atTop 2] with n hn2
          have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
          have hn_pos : (0 : ℝ) < n := by positivity
          have hsq : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.sqrt_eq_rpow]
            exact Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
          have h1' : ((Nat.sqrt n + 2 : ℕ) : ℝ) / ((n : ℝ) / Real.log n) =
              ((Nat.sqrt n : ℝ) + 2) * Real.log n / (n : ℝ) := by
            push_cast; field_simp [hn_pos.ne', hlog_pos.ne']
          rw [h1']
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hlog_pos.le) hn_pos.le
      simpa using (h1.div h_pi_asymp one_ne_zero).congr' (by
        filter_upwards [eventually_ge_atTop 2] with n hn2
        have hpi_ne : (Nat.primeCounting n : ℝ) ≠ 0 := by
          have : 1 ≤ Nat.primeCounting n := by
            rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
            exact Finset.card_pos.mpr ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
          exact_mod_cast (by omega : Nat.primeCounting n ≠ 0)
        have hlog_ne : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
        have hden_ne : (n : ℝ) / Real.log n ≠ 0 := div_ne_zero (by positivity) hlog_ne
        field_simp [hpi_ne, hden_ne])
    have h_main_lim : Tendsto (fun n : ℕ =>
        1 - ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ) -
          ((Nat.primeCounting (n / 2) : ℝ) / (Nat.primeCounting n : ℝ) -
            (Nat.primeCounting (n / 3) : ℝ) / (Nat.primeCounting n : ℝ))) atTop (𝓝 (5 / 6 - Real.log 2)) := by
      have h1 := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub lemma_2_1_ii_part2).sub
        ((h_pi_div_ratio 2 (by norm_num)).sub (h_pi_div_ratio 3 (by norm_num)))
      convert h1 using 1
      norm_num; ring
    have h_diff_zero : Tendsto (fun n : ℕ =>
        (((Finset.Icc 5 n).filter fun p => p.Prime ∧ 2 ∣ padicValNat p n.factorial ∧
          4 ≤ padicValNat p n.factorial).card : ℝ) / (Nat.primeCounting n : ℝ) -
        (1 - ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ) -
          ((Nat.primeCounting (n / 2) : ℝ) / (Nat.primeCounting n : ℝ) -
            (Nat.primeCounting (n / 3) : ℝ) / (Nat.primeCounting n : ℝ)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h_sqrt_zero
      filter_upwards [eventually_ge_atTop 9] with n hn9
      have hpi_pos : (0 : ℝ) < Nat.primeCounting n := by
        have : 1 ≤ Nat.primeCounting n := by
          rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
          exact Finset.card_pos.mpr ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
        exact_mod_cast this
      set S := (Finset.Icc 5 n).filter fun p => p.Prime ∧ 2 ∣ padicValNat p n.factorial ∧ 4 ≤ padicValNat p n.factorial
      set AllP := (Finset.Icc 2 n).filter Nat.Prime
      set I2 := (Finset.Ioc (n / 3) (n / 2)).filter Nat.Prime
      have hPodd_sub : Podd n ⊆ AllP := fun p hp => by
        simp only [Podd, AllP, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
      have hI2_sub : I2 ⊆ AllP := fun p hp => by
        simp only [I2, AllP, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨hp.2.two_le, le_trans hp.1.2 (Nat.div_le_self n 2)⟩, hp.2⟩
      have hdisj_PI2 : Disjoint (Podd n) I2 := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [I2, Finset.mem_filter, Finset.mem_Ioc] at hp2
        have hnsq : n < p ^ 2 := by
          have h1 : n / 3 ≥ 3 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
          have hp4 : 4 ≤ p := by omega
          have h3p : n < 3 * p := by
            have := Nat.lt_mul_div_succ n (by norm_num : 0 < 3)
            nlinarith
          nlinarith
        have hv2 : padicValNat p n.factorial = 2 := by
          rw [padicValNat_factorial_of_lt_sq hp2.2 hnsq]
          have h2p : 2 * p ≤ n := (Nat.le_div_iff_mul_le (by norm_num)).mp hp2.1.2
          have h3p : n < 3 * p := by
            have := Nat.lt_mul_div_succ n (by norm_num : 0 < 3)
            nlinarith
          rw [Nat.div_eq_iff_eq_mul_add_mod] <;> omega
        have hodd := (Finset.mem_filter.mp hp1).2.2
        rw [hv2] at hodd; exact hodd (by decide)
      have hI2_card : (I2.card : ℝ) = (Nat.primeCounting (n / 2) : ℝ) - (Nat.primeCounting (n / 3) : ℝ) := by
        have hdisj : Disjoint I2 ((Finset.Icc 2 (n / 3)).filter Nat.Prime) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [I2, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at h1 h2; omega
        have hu : I2 ∪ (Finset.Icc 2 (n / 3)).filter Nat.Prime = (Finset.Icc 2 (n / 2)).filter Nat.Prime := by
          ext p; simp only [Finset.mem_union, I2, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
          constructor
          · rintro (⟨⟨_, h⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
            · exact ⟨⟨hp.two_le, h⟩, hp⟩
            · exact ⟨⟨h1, le_trans h2 (Nat.div_le_div_left (by norm_num) (by norm_num))⟩, hp⟩
          · rintro ⟨⟨h1, h2⟩, hp⟩
            by_cases h : p ≤ n / 3
            · exact Or.inr ⟨⟨h1, h⟩, hp⟩
            · exact Or.inl ⟨⟨by omega, h2⟩, hp⟩
        have hc := Finset.card_union_of_disjoint hdisj
        rw [hu] at hc
        have h1 : (((Finset.Icc 2 (n / 2)).filter Nat.Prime).card : ℝ) = (Nat.primeCounting (n / 2) : ℝ) := (hpc_eq (n / 2)).symm
        have h2 : (((Finset.Icc 2 (n / 3)).filter Nat.Prime).card : ℝ) = (Nat.primeCounting (n / 3) : ℝ) := (hpc_eq (n / 3)).symm
        have hcast : (I2.card : ℝ) + (((Finset.Icc 2 (n / 3)).filter Nat.Prime).card : ℝ) =
            (((Finset.Icc 2 (n / 2)).filter Nat.Prime).card : ℝ) := by exact_mod_cast hc.symm
        linarith
      have hT_card : ((AllP \ (Podd n ∪ I2)).card : ℝ) =
          (Nat.primeCounting n : ℝ) - (Podd n).card - ((Nat.primeCounting (n / 2) : ℝ) - (Nat.primeCounting (n / 3) : ℝ)) := by
        have hsub_u : Podd n ∪ I2 ⊆ AllP := Finset.union_subset hPodd_sub hI2_sub
        have h1 : (AllP \ (Podd n ∪ I2)).card + (Podd n ∪ I2).card = AllP.card :=
          Finset.card_sdiff_add_card_eq_card hsub_u
        rw [Finset.card_union_of_disjoint hdisj_PI2] at h1
        have hAll : (AllP.card : ℝ) = (Nat.primeCounting n : ℝ) := (hpc_eq n).symm
        have hcast : ((AllP \ (Podd n ∪ I2)).card : ℝ) + ((Podd n).card : ℝ) + (I2.card : ℝ) = (AllP.card : ℝ) := by
          exact_mod_cast h1
        linarith
      set T := AllP \ (Podd n ∪ I2)
      have hS_sub_T : S ⊆ T := by
        intro p hp
        simp only [S, Finset.mem_filter, Finset.mem_Icc] at hp
        rcases hp with ⟨⟨hp5, hpn⟩, hp_prime, h2dvd, hv4⟩
        simp only [T, Finset.mem_sdiff, AllP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, I2, Finset.mem_Ioc]
        refine ⟨⟨⟨hp_prime.two_le, hpn⟩, hp_prime⟩, ?_⟩
        rintro (hp_odd | ⟨⟨hlo, hhi⟩, _⟩)
        · have hodd := (Finset.mem_filter.mp hp_odd).2.2
          exact hodd h2dvd
        · have hnsq : n < p ^ 2 := by
            have : n / 3 ≥ 3 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
            have hp4 : 4 ≤ p := by omega
            have h3p : n < 3 * p := by
              have := Nat.lt_mul_div_succ n (by norm_num : 0 < 3)
              nlinarith
            nlinarith
          have hv2 : padicValNat p n.factorial = 2 := by
            rw [padicValNat_factorial_of_lt_sq hp_prime hnsq]
            have h2p : 2 * p ≤ n := (Nat.le_div_iff_mul_le (by norm_num)).mp hhi
            have h3p : n < 3 * p := by
              have := Nat.lt_mul_div_succ n (by norm_num : 0 < 3)
              nlinarith
            rw [Nat.div_eq_iff_eq_mul_add_mod] <;> omega
          omega
      have hT_sdiff_S : T \ S ⊆ Finset.Icc 1 (Nat.sqrt n) ∪ {2, 3} := by
        intro p hp
        rw [Finset.mem_sdiff] at hp
        rcases hp with ⟨hpT, hpS⟩
        simp only [T, Finset.mem_sdiff, AllP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Podd, I2, Finset.mem_Ioc] at hpT
        rcases hpT with ⟨⟨⟨_, hpn⟩, hp_prime⟩, hnot⟩
        by_cases hp5 : p < 5
        · have : p = 2 ∨ p = 3 := by
            have := hp_prime.two_le; rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact absurd hp_prime (by decide)
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases this with rfl | rfl <;> tauto
        · apply Finset.mem_union_left
          rw [Finset.mem_Icc]
          refine ⟨hp_prime.pos, ?_⟩
          by_contra hgt
          have hnsq : n < p ^ 2 := by
            have h1 := Nat.lt_succ_sqrt n
            have h2 : Nat.sqrt n + 1 ≤ p := by omega
            calc n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := h1
              _ ≤ p * p := Nat.mul_le_mul h2 h2
              _ = p ^ 2 := (sq p).symm
          have h2dvd : 2 ∣ padicValNat p n.factorial := by
            by_contra hodd
            exact hnot (Or.inl ⟨⟨hp_prime.two_le, hpn⟩, hp_prime, hodd⟩)
          have hv_eq : padicValNat p n.factorial = n / p := padicValNat_factorial_of_lt_sq hp_prime hnsq
          have hv_ne0 : padicValNat p n.factorial ≠ 0 := by
            rw [hv_eq]
            exact (Nat.div_pos hpn hp_prime.pos).ne'
          have hv_ne2 : padicValNat p n.factorial ≠ 2 := by
            intro h2
            rw [hv_eq] at h2
            have hlo : n / 3 < p := by
              have : 3 * p > n := by
                have := Nat.lt_mul_div_succ n hp_prime.pos
                nlinarith
              exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by linarith)
            have hhi : p ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
              have := Nat.div_mul_le_self n p; nlinarith)
            exact hnot (Or.inr ⟨⟨hlo, hhi⟩, hp_prime⟩)
          have hv_ge4 : 4 ≤ padicValNat p n.factorial := by
            obtain ⟨k, hk⟩ := h2dvd
            have : k ≠ 0 := by intro h0; subst h0; simp at hv_ne0
            have : k ≠ 1 := by intro h1; subst h1; omega
            omega
          exact hpS (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hpn⟩, hp_prime, h2dvd, hv_ge4⟩)
      have hcard_diff : (T.card : ℝ) - (S.card : ℝ) ≤ (Nat.sqrt n + 2 : ℕ) := by
        have h1 : T.card - S.card = (T \ S).card := (Finset.card_sdiff hS_sub_T).symm
        have h2 : (T \ S).card ≤ (Finset.Icc 1 (Nat.sqrt n) ∪ {2, 3}).card := Finset.card_le_card hT_sdiff_S
        have h3 : (Finset.Icc 1 (Nat.sqrt n) ∪ {2, 3}).card ≤ Nat.sqrt n + 2 := by
          refine le_trans (Finset.card_union_le _ _) ?_
          simp only [Nat.card_Icc, add_tsub_cancel_right]
          have : ({2, 3} : Finset ℕ).card ≤ 2 := Finset.card_le_two
          omega
        have hS_le_T : S.card ≤ T.card := Finset.card_le_card hS_sub_T
        have hcast : (T.card : ℝ) - (S.card : ℝ) = ((T.card - S.card : ℕ) : ℝ) := by
          rw [Nat.cast_sub hS_le_T]
        rw [hcast]
        exact_mod_cast le_trans (by omega : T.card - S.card ≤ (T \ S).card) (le_trans h2 h3)
      have hS_le_T : (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card hS_sub_T
      have heq_sub : (S.card : ℝ) / (Nat.primeCounting n : ℝ) -
          (1 - ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ) -
            ((Nat.primeCounting (n / 2) : ℝ) / (Nat.primeCounting n : ℝ) -
              (Nat.primeCounting (n / 3) : ℝ) / (Nat.primeCounting n : ℝ))) =
          -((T.card : ℝ) - (S.card : ℝ)) / (Nat.primeCounting n : ℝ) := by
        rw [hT_card]
        field_simp [hpi_pos.ne']
        ring
      rw [Real.norm_eq_abs, heq_sub, abs_div, abs_neg, abs_of_nonneg (by linarith), abs_of_pos hpi_pos]
      exact div_le_div_of_nonneg_right hcard_diff hpi_pos.le
    simpa using (h_main_lim.add h_diff_zero).congr fun n => by ring
  have hpart3 : (∀ n m : ℕ, (hn116 : 116 ≤ n) → IsBrocardSol n m →
        ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < p ∧ (p : ℝ) ≤ (n : ℝ) / 4 ∧
          let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) (by omega)⟩
          ∀ (vp_Rtilde vp_Lp1 : ℤ) (lamP muP : ℕ),
            (vp_Lp1 = (padicValNat p (NumberField.classNumber (QuadField (qn n : ℚ))) : ℤ) +
              vp_Rtilde - 1) →
            (1 ≤ vp_Lp1 → 1 ≤ lamP) →
            lamP = 0) →
      ∀ n m : ℕ, IsBrocardSol n m → (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
    intro hgreen n m hsol
    by_cases hn8 : n < 8
    · have hm2 := hsol.2.2
      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; have : m ^ 2 = 2 := by simpa using hm2.symm
        rcases le_or_gt m 1 with h | h <;> nlinarith
      · exfalso; have : m ^ 2 = 2 := by simpa using hm2.symm
        rcases le_or_gt m 1 with h | h <;> nlinarith
      · exfalso; have : m ^ 2 = 3 := by simpa using hm2.symm
        rcases le_or_gt m 1 with h | h <;> nlinarith
      · exfalso; have : m ^ 2 = 7 := by simpa using hm2.symm
        rcases le_or_gt m 2 with h | h <;> nlinarith
      · exact Or.inl ⟨rfl, by have : m ^ 2 = 25 := by simpa using hm2.symm; nlinarith [hsol.2.1]⟩
      · exact Or.inr (Or.inl ⟨rfl, by have : m ^ 2 = 121 := by simpa using hm2.symm; nlinarith [hsol.2.1]⟩)
      · exfalso; exact (pellIndex_spec (by omega : 4 ≤ 6) hsol).1 rfl
      · exact Or.inr (Or.inr ⟨rfl, by have : m ^ 2 = 5041 := by simpa using hm2.symm; nlinarith [hsol.2.1]⟩)
    · by_cases hn116 : n < 116
      · exact False.elim (berndt_galway_brocard_bound n m hsol (by omega) (by omega))
      · obtain ⟨p, hp, hplo, hphi, hgr⟩ := hgreen n m (by omega) hsol
        have hp5 : 5 ≤ p := by
          have : (23 : ℝ) < (n : ℝ) / 5 := by
            have : (116 : ℝ) ≤ n := by exact_mod_cast (by omega : 116 ≤ n)
            linarith
          have : (23 : ℝ) < p := lt_trans this hplo
          exact_mod_cast (by linarith : (5 : ℝ) ≤ p)
        have hnsq : n < p ^ 2 := by
          have : (23 : ℝ) < p := lt_trans (by
            have : (116 : ℝ) ≤ n := by exact_mod_cast (by omega : 116 ≤ n)
            linarith) hplo
          have hp24 : 24 ≤ p := by exact_mod_cast (by linarith : (23 : ℝ) < p)
          have h1 : (n : ℝ) < 5 * p := by linarith
          have hn_lt : n < 5 * p := by exact_mod_cast h1
          nlinarith
        have hnp : n / p = 4 := by
          have h1 : 4 * p ≤ n := by exact_mod_cast (by linarith : (p : ℝ) * 4 ≤ n)
          have h2 : n < 5 * p := by exact_mod_cast (by linarith : (n : ℝ) < 5 * p)
          rw [Nat.div_eq_iff_eq_mul_add_mod] <;> omega
        have hv4 : padicValNat p n.factorial = 4 := by
          rw [padicValNat_factorial_of_lt_sq hp hnsq, hnp]
        have hp_even : p ∈ Peven n := by
          simp only [Peven, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨hp.two_le, by
            have : (p : ℝ) ≤ n := by linarith [show (0 : ℝ) ≤ n by positivity]
            exact_mod_cast this⟩, hp, ?_⟩
          rw [hv4]; decide
        have hp_ndvd_k : ¬ p ∣ pellIndex (by omega : 4 ≤ n) hsol := by
          intro hdvd
          have hk_ub := (lemma_3_1_i n (by omega) (by omega)).2.2.2.2.2 (by omega) m hsol
          have hk_lt : (pellIndex (by omega : 4 ≤ n) hsol : ℝ) < p := lt_trans (lt_trans hk_ub.2.1 (hk_ub.2.2 (by omega))) hplo
          have hk_pos : 0 < pellIndex (by omega : 4 ≤ n) hsol := hk_ub.1
          have hle : p ≤ pellIndex (by omega : 4 ≤ n) hsol := Nat.le_of_dvd hk_pos hdvd
          have hleR : (p : ℝ) ≤ pellIndex (by omega : 4 ≤ n) hsol := by exact_mod_cast hle
          linarith
        obtain ⟨_, vp_Lp1, lamP, hvp1, hlam1, vp_Rtilde, muP, _, hEq, hMW⟩ :=
          (hpart1 n m (by omega) hsol).2 p hp hp5 hp_even hp_ndvd_k (by omega)
        have h0 := hgr (vp_Rtilde : ℤ) vp_Lp1 lamP muP hEq (fun _ => hMW)
        omega
  exact ⟨hpart1, hpart2, hpart3⟩

/-- Fermat quotient `q_p(a) = (a^{p-1} - 1) / p mod p`. -/
def fermatQuot (p : ℕ) (a : ℤ) : ZMod p :=
  (((a ^ (p - 1) - 1) / (p : ℤ) : ℤ) : ZMod p)

private lemma fermatQuot_congr {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (h : (p : ℤ) ^ 2 ∣ a - b) : fermatQuot p a = fermatQuot p b := by
  unfold fermatQuot
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdvd : (p : ℤ) ^ 2 ∣ a ^ (p - 1) - b ^ (p - 1) := by
    obtain ⟨k, hk⟩ := h
    have ha : a = b + (p : ℤ) ^ 2 * k := by linarith
    have hmod : (a ^ (p - 1) - b ^ (p - 1) : ℤ) =
        ∑ i ∈ Finset.Ico 1 p, (Nat.choose (p - 1) i : ℤ) * b ^ (p - 1 - i) * ((p : ℤ) ^ 2 * k) ^ i := by
      rw [ha, add_pow]
      have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
      have hr : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
      rw [hr, ← Finset.add_sum_erase _ _ h0]
      simp only [pow_zero, mul_one, tsub_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_left]
      have her : (Finset.range p).erase 0 = Finset.Ico 1 p := by
        ext i; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]; omega
      rw [her]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hmod]
    refine Finset.dvd_sum fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hpow : (p : ℤ) ^ 2 ∣ ((p : ℤ) ^ 2 * k) ^ i := by
      have : ((p : ℤ) ^ 2 * k) ^ i = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * k) ^ (i - 1) * k := by
        calc ((p : ℤ) ^ 2 * k) ^ i
            = ((p : ℤ) ^ 2 * k) * ((p : ℤ) ^ 2 * k) ^ (i - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel hi1]
          _ = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * k) ^ (i - 1) * k := by ring
      rw [this]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    exact dvd_mul_of_dvd_right hpow _
  -- Actually, if `a^(p-1) - 1 = (b^(p-1) - 1) + p^2 * q`, then `(a^(p-1) - 1)/p = (b^(p-1) - 1)/p + p * q`!
  -- Wait: integer division `(u + p^2 * q) / p = u / p + p * q` ALWAYS holds in `ℤ`!
  obtain ⟨q, hq⟩ := hdvd
  have h1 : a ^ (p - 1) - 1 = (b ^ (p - 1) - 1) + q * (p : ℤ) * (p : ℤ) := by linarith
  rw [h1, Int.add_mul_ediv_right _ _ hpZ]
  push_cast
  simp [ZMod.natCast_self]

private lemma fermatQuot_mul {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    fermatQuot p (a * b) = fermatQuot p a + fermatQuot p b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha_mod : (a : ZMod p) ≠ 0 := fun h => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hb_mod : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have ha_flt : (p : ℤ) ∣ a ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one ha_mod, sub_self]
  have hb_flt : (p : ℤ) ∣ b ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hb_mod, sub_self]
  obtain ⟨qa, hqa⟩ := ha_flt
  obtain ⟨qb, hqb⟩ := hb_flt
  have ha_eq : a ^ (p - 1) = 1 + (p : ℤ) * qa := by linarith
  have hb_eq : b ^ (p - 1) = 1 + (p : ℤ) * qb := by linarith
  have hab_eq : (a * b) ^ (p - 1) - 1 = (p : ℤ) * (qa + qb + (p : ℤ) * qa * qb) := by
    rw [mul_pow, ha_eq, hb_eq]; ring
  unfold fermatQuot
  rw [hab_eq, show a ^ (p - 1) - 1 = (p : ℤ) * qa by linarith,
    show b ^ (p - 1) - 1 = (p : ℤ) * qb by linarith]
  rw [Int.mul_ediv_cancel_left _ hpZ, Int.mul_ediv_cancel_left _ hpZ, Int.mul_ediv_cancel_left _ hpZ]
  push_cast
  simp [ZMod.natCast_self]

theorem cor_3_5 (n m : ℕ) (hn : 4 ≤ n) (hsol : IsBrocardSol n m)
    (d₁ d₂ xₙ yₙ : ℕ) (hd₁ : m - 1 = d₁ * xₙ ^ 2) (hd₂ : m + 1 = d₂ * yₙ ^ 2) :
    (∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ (n : ℝ) / 2 →
      ((p ∣ m + 1 → ¬ ((p : ℤ) ∣ xₙ) →
        fermatQuot p d₁ = fermatQuot p 2 - 2 * fermatQuot p xₙ) ∧
       (p ∣ m - 1 → ¬ ((p : ℤ) ∣ yₙ) →
        fermatQuot p (-d₂) = fermatQuot p 2 - 2 * fermatQuot p yₙ))) ∧
    (n ≥ 9 → 2 ∣ padicValNat 3 n.factorial →
      (15 ≤ n ∨ ∃ dn : ℕ, (dn = 1 ∨ dn = 3) ∧ ((qn n : ℤ) % 8 ≠ 5 → dn = 1) ∧
        ¬ 3 ∣ (dn * pellIndex hn hsol)) →
      let _ : Fact (¬ IsSquare (-(3 * (qn n : ℚ)))) := ⟨by
        rintro ⟨r, hr⟩
        have hpos : (0 : ℚ) < 3 * (qn n : ℚ) := by positivity [qn_pos n]
        have hsq : 0 ≤ r * r := mul_self_nonneg r
        linarith⟩
      let chi_neg3D_3 : ℤ := jacobiSym (-3 * fundDiscrQuad (qn n : ℤ)) 3
      (3 : ℤ) ∣ (1 - chi_neg3D_3) *
        (NumberField.classNumber (QuadField (-(3 * (qn n : ℚ)))) : ℤ)) := by
  have hm_ge2 : 2 ≤ m := by
    obtain ⟨_, _, hm⟩ := hsol
    have h24 : 24 ≤ n.factorial := by
      have : Nat.factorial 4 ≤ n.factorial := Nat.factorial_le hn
      linarith [show Nat.factorial 4 = 24 by decide]
    nlinarith
  constructor
  · intro p hp hp3 hp_le
    haveI : Fact p.Prime := ⟨hp⟩
    have h2p : 2 * p ≤ n := by
      have : (p : ℝ) * 2 ≤ n := by linarith
      exact_mod_cast this
    have hp2_fac : p ^ 2 ∣ n.factorial := by
      have h1 : 2 * p * p ∣ n.factorial := by
        have hp_dvd1 : p ∣ n.factorial := hp.dvd_factorial.mpr (by omega)
        have h2p_le : 2 * p ≤ n := h2p
        -- Both `p` and `2 * p` are distinct factors in `{1, ..., n}`
        have hprod : p * (2 * p) ∣ n.factorial := by
          have hmem1 : p ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hp.pos, by omega⟩
          have hmem2 : 2 * p ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, h2p_le⟩
          have hne : p ≠ 2 * p := by omega
          have hdvd_prod : p * (2 * p) ∣ ∏ i ∈ Finset.Icc 1 n, i := by
            rw [← Finset.prod_pair hne]
            exact Finset.prod_dvd_prod_of_subset _ _ _ (fun x hx => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
          simpa [Nat.factorial_eq_prod_range_add_one] using hdvd_prod
        exact dvd_trans ⟨2, by ring⟩ hprod
      exact dvd_trans ⟨2, by ring⟩ h1
    have hp2_m : p ^ 2 ∣ (m - 1) * (m + 1) := by
      have hfac : n.factorial = (m - 1) * (m + 1) := by
        have hm := hsol.2.2
        have : (m - 1) * (m + 1) + 1 = m ^ 2 := by
          zify [show 1 ≤ m by omega]; ring
        omega
      rwa [← hfac]
    have hcop_pm : Nat.Coprime (m - 1) (m + 1) ∨ (p ∣ m - 1 → ¬ p ∣ m + 1) := by
      refine Or.inr fun h1 h2 => ?_
      have hd2 : p ∣ (m + 1) - (m - 1) := Nat.dvd_sub h2 h1
      have hsub : (m + 1) - (m - 1) = 2 := by omega
      rw [hsub] at hd2
      have := Nat.le_of_dvd (by norm_num) hd2
      omega
    have hf_neg2 : fermatQuot p (-2) = fermatQuot p 2 := by
      unfold fermatQuot
      have hp_even : Even (p - 1) := by
        have := hp.eq_two_or_odd.resolve_left (by omega)
        exact Nat.even_sub (by omega) |>.mpr (by omega)
      rw [hp_even.neg_pow]
    constructor
    · intro hp_mp1 hpx
      have hp_ndvd_mm1 : ¬ p ∣ m - 1 := fun h => by
        rcases hcop_pm with hcop | hnd
        · have := hp.not_dvd_one (hcop.symm ▸ Nat.dvd_gcd hp_mp1 h)
          exact this
        · exact hnd h hp_mp1
      have hp2_mp1 : p ^ 2 ∣ m + 1 :=
        (hp.coprime_iff_not_dvd.mpr hp_ndvd_mm1).pow_right 2 |>.symm.dvd_of_dvd_mul_left hp2_m
      have hcongr : (p : ℤ) ^ 2 ∣ (d₁ : ℤ) * (xₙ : ℤ) ^ 2 - (-2 : ℤ) := by
        have h1 : (d₁ : ℤ) * (xₙ : ℤ) ^ 2 = (m : ℤ) - 1 := by
          have : ((m - 1 : ℕ) : ℤ) = ((d₁ * xₙ ^ 2 : ℕ) : ℤ) := by exact_mod_cast hd₁
          rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at this
          simpa using this.symm
        rw [h1, show (m : ℤ) - 1 - (-2 : ℤ) = ((m + 1 : ℕ) : ℤ) by push_cast; ring]
        exact_mod_cast hp2_mp1
      have hpd₁ : ¬ (p : ℤ) ∣ (d₁ : ℤ) := by
        intro h
        have hd2 : (p : ℤ) ∣ (-2 : ℤ) := by
          have : (-2 : ℤ) = (d₁ : ℤ) * (xₙ : ℤ) ^ 2 - ((d₁ : ℤ) * (xₙ : ℤ) ^ 2 - (-2 : ℤ)) := by ring
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_trans (dvd_pow_self _ (by norm_num)) hcongr)
        have := Int.le_of_dvd (by norm_num) hd2.neg_right
        omega
      have hfq := fermatQuot_congr hp hcongr
      rw [hf_neg2, fermatQuot_mul hp hpd₁ (pow_ne_zero 2 (by exact_mod_cast fun h => hpx (by exact_mod_cast h)) |> fun _ => by
        intro h
        have h' : (p : ℤ) ∣ (xₙ : ℤ) ^ 2 := h
        exact hpx ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h' |> fun h'' => h''.elim id id)),
        show (xₙ : ℤ) ^ 2 = (xₙ : ℤ) * (xₙ : ℤ) by ring, fermatQuot_mul hp hpx hpx] at hfq
      linear_combination -hfq
    · intro hp_mm1 hpy
      have hp_ndvd_mp1 : ¬ p ∣ m + 1 := fun h => by
        rcases hcop_pm with hcop | hnd
        · exact hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hp_mm1 h)
        · exact hnd hp_mm1 h
      have hp2_mm1 : p ^ 2 ∣ m - 1 :=
        (hp.coprime_iff_not_dvd.mpr hp_ndvd_mp1).pow_right 2 |>.symm.dvd_of_dvd_mul_right hp2_m
      have hcongr : (p : ℤ) ^ 2 ∣ (-d₂ : ℤ) * (yₙ : ℤ) ^ 2 - (-2 : ℤ) := by
        have h1 : (d₂ : ℤ) * (yₙ : ℤ) ^ 2 = (m : ℤ) + 1 := by exact_mod_cast hd₂.symm
        rw [show (-d₂ : ℤ) * (yₙ : ℤ) ^ 2 - (-2 : ℤ) = -((m - 1 : ℕ) : ℤ) by
          rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; linarith]
        exact dvd_neg.mpr (by exact_mod_cast hp2_mm1)
      have hpd₂ : ¬ (p : ℤ) ∣ (-d₂ : ℤ) := by
        intro h
        have hd2 : (p : ℤ) ∣ (-2 : ℤ) := by
          have : (-2 : ℤ) = (-d₂ : ℤ) * (yₙ : ℤ) ^ 2 - ((-d₂ : ℤ) * (yₙ : ℤ) ^ 2 - (-2 : ℤ)) := by ring
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_trans (dvd_pow_self _ (by norm_num)) hcongr)
        have := Int.le_of_dvd (by norm_num) hd2.neg_right
        omega
      have hfq := fermatQuot_congr hp hcongr
      rw [hf_neg2, fermatQuot_mul hp hpd₂ (by
        intro h
        exact hpy ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h |> fun h'' => h''.elim id id)),
        show (yₙ : ℤ) ^ 2 = (yₙ : ℤ) * (yₙ : ℤ) by ring, fermatQuot_mul hp hpy hpy] at hfq
      linear_combination -hfq
  · intro hn9 h3_even _
    by_cases hn_big : n ≤ 10 ^ 9
    · exact False.elim (berndt_galway_brocard_bound n m hsol (by omega) hn_big)
    · push_neg at hn_big
      have h3_ndvd_qn : ¬ 3 ∣ qn n := by
        intro h3
        rw [qn_eq_prod_Podd] at h3
        rcases (by decide : Nat.Prime 3).dvd_finset_prod_iff.mp h3 with ⟨q, hq, h3q⟩
        have hq_prime : q.Prime := (Finset.mem_filter.mp hq).2.1
        have hq_eq : 3 = q := (Nat.prime_dvd_prime_iff_eq (by decide) hq_prime).mp h3q
        subst hq_eq
        exact (Finset.mem_filter.mp hq).2.2 h3_even
      have hqn1 : 1 < qn n := by
        have := lemma_3_1_i n (by omega) (by omega)
        have h4 := this.1
        rcases h4 with ⟨p, hp, hdvd, hmod⟩
        exact lt_of_lt_of_le (by have := hp.two_le; omega) (Nat.le_of_dvd (qn_pos n) hdvd)
      haveI : Fact (¬ IsSquare (-(3 * (qn n : ℚ)))) := ⟨by
        rintro ⟨r, hr⟩
        have hpos : (0 : ℚ) < 3 * (qn n : ℚ) := by positivity [qn_pos n]
        have hsq : 0 ≤ r * r := mul_self_nonneg r
        linarith⟩
      obtain ⟨hn6, _, _, hsny⟩ := pellIndex_spec (by omega : 4 ≤ n) hsol
      set k := pellIndex (by omega : 4 ≤ n) hsol
      have hk_bd : (k : ℝ) < 2.5 * Real.log n :=
        (lemma_3_1_i n (by omega) (by omega)).2.2.2.2.2 (by omega) m hsol |>.2.1
      have hv_sn : (n / 6 : ℕ) ≤ padicValNat 3 (sn n) := by
        have hfac := factorial_eq_qn_mul_sn_sq n
        haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
        have hval_fac : padicValNat 3 n.factorial = padicValNat 3 (qn n) + 2 * padicValNat 3 (sn n) := by
          rw [hfac, padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'),
            padicValNat.pow 2 (sn_pos n).ne']
        have hq0 : padicValNat 3 (qn n) = 0 := padicValNat.eq_zero_of_not_dvd h3_ndvd_qn
        have h3_le : n / 3 ≤ padicValNat 3 n.factorial := by
          have hleg := sub_one_mul_padicValNat_factorial (p := 3) n
          have hdig_le : (Nat.digits 3 n).sum ≤ 2 * (Nat.log 3 n + 1) := by
            have h1 : ∀ d ∈ Nat.digits 3 n, d ≤ 2 := fun d hd => by
              have := Nat.digits_lt_base (by decide : 1 < 3) hd; omega
            have h2 : (Nat.digits 3 n).sum ≤ (Nat.digits 3 n).length * 2 := by
              simpa using List.sum_le_sum (l := Nat.digits 3 n) (f := id) (g := fun _ => 2) fun d hd => h1 d hd
            have hlen : (Nat.digits 3 n).length ≤ Nat.log 3 n + 1 := by
              rw [Nat.digits_len 3 n (by decide) (by omega)]
            omega
          have hlog_ge : 18 ≤ Nat.log 3 n :=
            (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
          have h24 : ∀ r : ℕ, 5 ≤ r → 24 * (r + 1) ≤ 3 ^ r := by
            intro r hr
            induction r, hr using Nat.le_induction with
            | base => norm_num
            | succ m hm ih => rw [pow_succ]; omega
          have hpow_le : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 (by omega)
          have h24_le : 24 * (Nat.log 3 n + 1) ≤ n := le_trans (h24 _ (by omega)) hpow_le
          omega
        omega
      have hk1 : 1 ≤ k := (lemma_3_1_i n (by omega) hn6).2.2.2.2.2 (by omega) m hsol |>.1
      have hk_lt_3pow : padicValNat 3 k < k := by
        have h1 : padicValNat 3 k < 3 ^ padicValNat 3 k := Nat.lt_pow_self (by decide : 1 < 3)
        have h2 : 3 ^ padicValNat 3 k ≤ k :=
          Nat.le_of_dvd hk1 ((padicValNat_dvd_iff_le (by omega : k ≠ 0)).mpr le_rfl)
        omega
      have hk_le_n60 : k ≤ n / 60 := by
        have hn_pos : (0 : ℝ) < n := by positivity
        have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
        have hlog_sq : Real.log n ≤ 2 * Real.sqrt n := by
          have h1 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hsqrt_pos
          have h2 : Real.log n = 2 * Real.log (Real.sqrt n) := by
            have hsq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn_pos.le
            conv_lhs => rw [← hsq, Real.log_pow]
            norm_num
          linarith
        have hk_real : (k : ℝ) < (n : ℝ) / 60 := by
          have h300 : (300 : ℝ) * Real.sqrt n < n := by
            have hsq : ((300 : ℝ) * Real.sqrt n) ^ 2 < (n : ℝ) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hn_pos.le]
              have : (90000 : ℝ) < n := by exact_mod_cast (by omega : 90000 < n)
              nlinarith
            nlinarith [Real.sqrt_nonneg n]
          linarith
        have : (k : ℝ) < ((n / 60 : ℕ) : ℝ) + 1 := by
          have hdiv : (n : ℝ) / 60 < ((n / 60 : ℕ) : ℝ) + 1 := by
            have : n < (n / 60 + 1) * 60 := by rw [mul_comm]; exact Nat.lt_mul_div_succ n (by norm_num)
            have hR : (n : ℝ) < (((n / 60 : ℕ) : ℝ) + 1) * 60 := by exact_mod_cast this
            linarith
          linarith
        exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
      have hdiff_ge2 : (2 : ℤ) ≤ (padicValNat 3 (sn n) : ℤ) - (padicValNat 3 (1 * k) : ℤ) := by
        rw [one_mul]
        omega
      exact sinnott_and_kummer_congruence (qn n) (squarefree_qn n) hqn1 h3_ndvd_qn
        (pellFundUnit n (by omega) hn6) (pellFundUnit_isFundamental (by omega) hn6)
        k m (sn n) 1 (Or.inl rfl) (by exact_mod_cast hsol.2.2.symm) hmx hsny hdiff_ge2

theorem theorem_3_6 (n m : ℕ) (hn : 4 ≤ n) (hsol : IsBrocardSol n m)
    (hn6 : n ≠ 6) (hk : pellIndex hn hsol = 1 ∨ pellIndex hn hsol = 2) :
    let k := pellIndex hn hsol
    (k = 2 ↔ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
      (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v|) ∧
    (k = 1 ↔ (∃ δ₂ z₂ z₁ : ℕ, Squarefree δ₂ ∧ (m + 1) / 2 = δ₂ * z₂ ^ 2 ∧
      (m - 1) / 2 = (qn n / δ₂) * z₁ ^ 2 ∧
      ¬ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
        (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v|)) ∧
    (k = 2 →
      let _ : Fact (¬ IsSquare (-(qn n : ℚ))) := ⟨by
        rintro ⟨r, hr⟩
        have hpos : (0 : ℚ) < qn n := by exact_mod_cast qn_pos n
        have hsq : 0 ≤ r * r := mul_self_nonneg r
        linarith⟩
      2 ∣ NumberField.classNumber (QuadField (-(qn n : ℚ)))) := by
  obtain ⟨hn6', hk1, hmx, hsny⟩ := pellIndex_spec hn hsol
  set k := pellIndex hn hsol
  have hk_eq_fund : pellFundUnit n (by omega) hn6 = pellFundUnit n (by omega) hn6' := rfl
  have hpart1 : k = 2 ↔ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
      (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v| := by
    constructor
    · intro hk2
      refine ⟨(X1 n (by omega) hn6 : ℤ), (Y1 n (by omega) hn6 : ℤ), ?_, ?_, ?_⟩
      · rw [X1_eq, Y1_eq]; exact (pellFundUnit n (by omega) hn6).prop
      · have hm_eq : (m : ℤ) = (Xr n (by omega) hn6 2 : ℤ) := by
          rw [Xr_eq, ← hk2, ← hmx, hk_eq_fund]
        have h1 := (lemma_3_2_i n (by omega) hn6 2 (by norm_num)).1
        have hT2 : (Polynomial.Chebyshev.T ℤ (2 : ℤ)).eval (X1 n (by omega) hn6 : ℤ) =
            2 * (X1 n (by omega) hn6 : ℤ) ^ 2 - 1 := by
          have := Polynomial.Chebyshev.T_two ℤ
          simp [this, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
        have hprop : (X1 n (by omega) hn6 : ℤ) ^ 2 - (qn n : ℤ) * (Y1 n (by omega) hn6 : ℤ) ^ 2 = 1 := by
          rw [X1_eq, Y1_eq]; exact (pellFundUnit n (by omega) hn6).prop
        linarith
      · have hs_eq : (sn n : ℤ) = (Yr n (by omega) hn6 2 : ℤ) := by
          rw [Yr_eq, ← hk2, ← hsny, hk_eq_fund]
        have h2 := (lemma_3_2_i n (by omega) hn6 2 (by norm_num)).2.1
        have hU1 : (Polynomial.Chebyshev.U ℤ ((2 : ℕ) - 1)).eval (X1 n (by omega) hn6 : ℤ) =
            2 * (X1 n (by omega) hn6 : ℤ) := by
          simp [Polynomial.Chebyshev.U_one]
        rw [hU1] at h2
        have hnn : 0 ≤ (X1 n (by omega) hn6 : ℤ) * (Y1 n (by omega) hn6 : ℤ) := by positivity
        rw [abs_of_nonneg hnn]
        linarith
    · rintro ⟨u, v, huv, hm_eq, hsn_eq⟩
      let b : Pell.Solution₁ (qn n : ℤ) := ⟨u.natAbs, v.natAbs, by
        have hu2 : (u.natAbs : ℤ) ^ 2 = u ^ 2 := Int.natAbs_sq u
        have hv2 : (v.natAbs : ℤ) ^ 2 = v ^ 2 := Int.natAbs_sq v
        linarith⟩
      have hfund := pellFundUnit_isFundamental (by omega : 3 ≤ n) hn6
      obtain ⟨r, hr⟩ := hfund.eq_pow_of_nonneg b (by positivity) (by positivity)
      have hr1 : 1 ≤ r := by
        by_contra hr0
        have hr0' : r = 0 := by omega
        subst hr0'
        have hy0 : b.y = 0 := by rw [hr]; rfl
        have hv0 : v = 0 := by
          have : (v.natAbs : ℤ) = 0 := hy0
          exact Int.natAbs_eq_zero.mp (by exact_mod_cast this)
        rw [hv0, mul_zero, abs_zero, mul_zero] at hsn_eq
        have hsn_pos := sn_pos n
        omega
      have hb2_eq : b ^ 2 = ⟨(m : ℤ), (sn n : ℤ), by
          have hfac : (n.factorial : ℤ) = (qn n : ℤ) * (sn n : ℤ) ^ 2 := by exact_mod_cast factorial_eq_qn_mul_sn_sq n
          have hm2 : (n.factorial : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hsol.2.2
          linarith⟩ := by
        ext
        · change b.x ^ 2 + (qn n : ℤ) * b.y ^ 2 = (m : ℤ)
          rw [show b.x ^ 2 = u ^ 2 from Int.natAbs_sq u, show b.y ^ 2 = v ^ 2 from Int.natAbs_sq v]
          exact hm_eq.symm
        · change 2 * b.x * b.y = (sn n : ℤ)
          have : (b.x : ℤ) * b.y = |u * v| := by
            change (u.natAbs : ℤ) * (v.natAbs : ℤ) = |u * v|
            rw [← Int.natCast_mul, ← Int.natAbs_mul]
            exact (Int.natAbs_eq_abs (u * v)).symm
          linarith
      have hpow_eq : pellFundUnit n (by omega) hn6 ^ ((2 * r : ℕ) : ℤ) =
          pellFundUnit n (by omega) hn6 ^ (k : ℤ) := by
        calc pellFundUnit n (by omega) hn6 ^ ((2 * r : ℕ) : ℤ)
            = (pellFundUnit n (by omega) hn6 ^ r) ^ 2 := by
              rw [zpow_natCast, ← pow_mul, mul_comm]
          _ = b ^ 2 := by rw [← hr]
          _ = pellFundUnit n (by omega) hn6 ^ (k : ℤ) := by
              rw [hb2_eq]
              ext <;> [exact hmx; exact hsny]
      have hy_eq : Yr n (by omega) hn6 (2 * r) = Yr n (by omega) hn6 k := by
        have := congr_arg Pell.Solution₁.y hpow_eq
        have h1 : (Yr n (by omega) hn6 (2 * r) : ℤ) = (Yr n (by omega) hn6 k : ℤ) := by
          rw [Yr_eq, Yr_eq, this]
        exact_mod_cast h1
      have h2r_eq_k : 2 * r = k := (Yr_strictMono (by omega : 3 ≤ n) hn6).injective hy_eq
      omega
  have hpart2 : k = 1 ↔ (∃ δ₂ z₂ z₁ : ℕ, Squarefree δ₂ ∧ (m + 1) / 2 = δ₂ * z₂ ^ 2 ∧
      (m - 1) / 2 = (qn n / δ₂) * z₁ ^ 2 ∧
      ¬ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
        (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v|) := by
    constructor
    · intro hk1_eq
      have hnot2 : ¬ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
          (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v| := by
        intro h; have := hpart1.mpr h; omega
      have hm_odd : m % 2 = 1 := by
        have hm2 := hsol.2.2
        have h2fac : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
        have hm2_odd : m ^ 2 % 2 = 1 := by omega
        rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exfalso; have : (t + t) ^ 2 % 2 = 0 := by ring_nf; omega
          omega
        · omega
      have hcop : Nat.Coprime ((m + 1) / 2) ((m - 1) / 2) := by
        have h1 : (m + 1) / 2 - (m - 1) / 2 = 1 := by omega
        exact Nat.coprime_of_dvd fun p hp hpa hpb => by
          have hd : p ∣ (m + 1) / 2 - (m - 1) / 2 := Nat.dvd_sub hpa hpb
          rw [h1] at hd
          exact hp.not_dvd_one hd
      have hprod : ((m + 1) / 2) * ((m - 1) / 2) = qn n * (sn n / 2) ^ 2 := by
        have hfac := factorial_eq_qn_mul_sn_sq n
        have hm2 := hsol.2.2
        have hsn_even : 2 ∣ sn n := by
          have h4fac : 4 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
          have h2qn : ¬ 4 ∣ qn n := fun h => (squarefree_qn n 2 (by simpa using h)).elim
          have h4qns : 4 ∣ qn n * (sn n) ^ 2 := hfac ▸ h4fac
          have h2s2 : 2 ∣ (sn n) ^ 2 := by
            by_contra hns
            have hodd_sn : sn n ^ 2 % 2 = 1 := by omega
            have hcop4 : Nat.Coprime 4 (sn n ^ 2) := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
              exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 2
            exact h2qn (hcop4.dvd_of_dvd_mul_right h4qns)
          exact Nat.prime_two.dvd_of_dvd_pow h2s2
        have hmul4 : 4 * (((m + 1) / 2) * ((m - 1) / 2)) = 4 * (qn n * (sn n / 2) ^ 2) := by
          have h1 : 2 * ((m + 1) / 2) = m + 1 := by omega
          have h2 : 2 * ((m - 1) / 2) = m - 1 := by omega
          have h3 : 2 * (sn n / 2) = sn n := Nat.mul_div_cancel' hsn_even
          calc 4 * (((m + 1) / 2) * ((m - 1) / 2))
              = (2 * ((m + 1) / 2)) * (2 * ((m - 1) / 2)) := by ring
            _ = (m + 1) * (m - 1) := by rw [h1, h2]
            _ = m ^ 2 - 1 := by zify [show 1 ≤ m by omega]; ring
            _ = n.factorial := by omega
            _ = qn n * (sn n) ^ 2 := hfac
            _ = qn n * (2 * (sn n / 2)) ^ 2 := by rw [h3]
            _ = 4 * (qn n * (sn n / 2) ^ 2) := by ring
        omega
      let A := (m + 1) / 2
      let B := (m - 1) / 2
      have hA_pos : 0 < A := by omega
      have hB_pos : 0 < B := by
        have hm2 := hsol.2.2
        have h24 : 24 ≤ n.factorial := by
          have := Nat.factorial_le hn; linarith [show Nat.factorial 4 = 24 by decide]
        have : 5 ≤ m := by nlinarith
        omega
      let δ₂ := ∏ p ∈ A.primeFactors.filter (fun p => padicValNat p A % 2 = 1), p
      let z₂ := ∏ p ∈ A.primeFactors, p ^ (padicValNat p A / 2)
      have hδ₂_sqf : Squarefree δ₂ := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro p hp hpsq
        have hpdvd : p ∣ δ₂ := dvd_trans (dvd_mul_right p p) hpsq
        have hmem : p ∈ A.primeFactors.filter (fun p => padicValNat p A % 2 = 1) := by
          rcases hp.dvd_finset_prod_iff.mp hpdvd with ⟨q, hq, hpq⟩
          have hq_prime : q.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
          rwa [(Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq]
        have heq : δ₂ = p * ∏ q ∈ (A.primeFactors.filter (fun p => padicValNat p A % 2 = 1)).erase p, q :=
          (Finset.mul_prod_erase _ _ hmem).symm
        rw [heq, sq] at hpsq
        have hdvd_rest : p ∣ ∏ q ∈ (A.primeFactors.filter (fun p => padicValNat p A % 2 = 1)).erase p, q :=
          Nat.dvd_of_mul_dvd_mul_left hp.pos hpsq
        rcases hp.dvd_finset_prod_iff.mp hdvd_rest with ⟨q, hq, hpq⟩
        have hq_prime : q.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).1).1
        exact (Finset.mem_erase.mp hq).1 ((Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq).symm
      have hA_eq : A = δ₂ * z₂ ^ 2 := by
        have hfac_A : A = ∏ p ∈ A.primeFactors, p ^ padicValNat p A :=
          (Nat.prod_primeFactors_pow_factorization hA_pos.ne').symm
        have h1 : δ₂ = ∏ p ∈ A.primeFactors, p ^ (padicValNat p A % 2) := by
          rw [← Finset.prod_filter_mul_prod_filter_not A.primeFactors (fun p => padicValNat p A % 2 = 1)]
          have hrest : ∏ p ∈ A.primeFactors.filter (fun p => ¬ padicValNat p A % 2 = 1), p ^ (padicValNat p A % 2) = 1 := by
            refine Finset.prod_eq_one fun p hp => ?_
            have : padicValNat p A % 2 = 0 := by
              have := (Finset.mem_filter.mp hp).2; omega
            rw [this, pow_zero]
          rw [hrest, mul_one]
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [(Finset.mem_filter.mp hp).2, pow_one]
        have hz2 : z₂ ^ 2 = ∏ p ∈ A.primeFactors, p ^ (2 * (padicValNat p A / 2)) := by
          rw [Finset.prod_pow]
          refine Finset.prod_congr rfl fun p _ => by rw [← pow_mul, mul_comm]
        rw [h1, hz2, ← Finset.prod_mul_distrib]
        conv_lhs => rw [hfac_A]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← pow_add, Nat.mod_add_div]
      have hδ₂_dvd_qn : δ₂ ∣ qn n := by
        have hδ₂_dvd_A : δ₂ ∣ A := ⟨z₂ ^ 2, hA_eq⟩
        have hδ₂_dvd_prod : δ₂ ∣ qn n * (sn n / 2) ^ 2 := hprod ▸ dvd_mul_of_dvd_left hδ₂_dvd_A B
        rw [← Nat.prod_primeFactors_pow_factorization (by
          intro h0; rw [h0, zero_mul] at hA_eq; omega : δ₂ ≠ 0)]
        refine Finset.prod_dvd_of_coprime (fun p _ q _ hpq => ?_) (fun p hp => ?_)
        · exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (by assumption))
            (Nat.prime_of_mem_primeFactors (by assumption))).mpr hpq |>.pow _ _
        · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
          haveI : Fact p.Prime := ⟨hp_prime⟩
          have hp_dvd_δ : p ∣ δ₂ := Nat.dvd_of_mem_primeFactors hp
          have hp_val_δ : padicValNat p δ₂ = 1 := by
            have hp_ndvd2 : ¬ p ^ 2 ∣ δ₂ := fun h => hp_prime.not_unit (hδ₂_sqf p (by simpa [sq] using h))
            have hge1 : 1 ≤ padicValNat p δ₂ := (padicValNat_dvd_iff_le (by
              intro h0; rw [h0, zero_mul] at hA_eq; omega)).mp hp_dvd_δ
            have hlt2 : ¬ 2 ≤ padicValNat p δ₂ := fun h => hp_ndvd2 ((padicValNat_dvd_iff_le (by
              intro h0; rw [h0, zero_mul] at hA_eq; omega)).mpr h)
            omega
          rw [Nat.factorization_def δ₂ hp_prime, hp_val_δ, pow_one]
          have hp_val_prod : padicValNat p (A * B) % 2 = 1 := by
            have hcop_AB : ¬ p ∣ B := fun h => hp_prime.not_dvd_one (hcop ▸ Nat.dvd_gcd (dvd_trans hp_dvd_δ hδ₂_dvd_A) h)
            rw [padicValNat.mul hA_pos.ne' hB_pos.ne', padicValNat.eq_zero_of_not_dvd hcop_AB, add_zero]
            have hp_val_A : padicValNat p A = padicValNat p δ₂ + 2 * padicValNat p z₂ := by
              rw [hA_eq, padicValNat.mul (by intro h0; rw [h0, zero_mul] at hA_eq; omega)
                (pow_ne_zero 2 (by intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hA_eq; omega)),
                padicValNat.pow 2 (by intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hA_eq; omega)]
            omega
          rw [hprod, padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (by
            intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hprod; exact (mul_pos hA_pos hB_pos).ne' hprod)),
            padicValNat.pow 2 (by
            intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hprod; exact (mul_pos hA_pos hB_pos).ne' hprod)] at hp_val_prod
          have hvp_qn : 1 ≤ padicValNat p (qn n) := by omega
          exact (padicValNat_dvd_iff_le (qn_pos n).ne').mpr hvp_qn
      obtain ⟨δ₁, hδ₁⟩ := hδ₂_dvd_qn
      have hδ₁_eq : qn n / δ₂ = δ₁ := by
        rw [hδ₁, Nat.mul_div_cancel_left _ (by intro h0; rw [h0, zero_mul] at hA_eq; omega)]
      have h_eq_sq : B * δ₂ * z₂ ^ 2 = δ₁ * δ₂ * (sn n / 2) ^ 2 := by
        calc B * δ₂ * z₂ ^ 2 = A * B := by rw [hA_eq]; ring
          _ = qn n * (sn n / 2) ^ 2 := hprod
          _ = δ₁ * δ₂ * (sn n / 2) ^ 2 := by rw [hδ₁]; ring
      have hB_mul : B * z₂ ^ 2 = δ₁ * (sn n / 2) ^ 2 := by
        have hδ₂_pos : 0 < δ₂ := by intro h0; rw [h0, zero_mul] at hA_eq; omega
        nlinarith
      have hz2_dvd_sn : z₂ ∣ sn n / 2 := by
        have hsq_dvd : z₂ ^ 2 ∣ (sn n / 2) ^ 2 := by
          have h1 : z₂ ^ 2 ∣ δ₁ * (sn n / 2) ^ 2 := ⟨B, by linarith⟩
          have hcop_z2_δ1 : Nat.Coprime z₂ δ₁ := by
            refine Nat.coprime_of_dvd fun p hp hpz hpδ1 => ?_
            have hpA : p ∣ A := dvd_trans hpz (⟨δ₂ * z₂, by rw [hA_eq]; ring⟩)
            have hpB : ¬ p ∣ B := fun h => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpA h)
            haveI : Fact p.Prime := ⟨hp⟩
            have hvB0 : padicValNat p B = 0 := padicValNat.eq_zero_of_not_dvd hpB
            have hp_dvd_qn : p ∣ qn n := hδ₁ ▸ dvd_mul_of_dvd_right hpδ1 _
            have hv_qn : padicValNat p (qn n) = 1 := by
              have hge1 : 1 ≤ padicValNat p (qn n) := (padicValNat_dvd_iff_le (qn_pos n).ne').mp hp_dvd_qn
              have hlt2 : ¬ 2 ≤ padicValNat p (qn n) := fun h =>
                hp.not_unit (squarefree_qn n p (by simpa [sq] using (padicValNat_dvd_iff_le (qn_pos n).ne').mpr h))
              omega
            have hv_prod : padicValNat p (A * B) = padicValNat p (qn n * (sn n / 2) ^ 2) := congr_arg (padicValNat p) hprod
            rw [padicValNat.mul hA_pos.ne' hB_pos.ne', hvB0, add_zero,
              padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (by
                intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hprod; exact (mul_pos hA_pos hB_pos).ne' hprod)),
              padicValNat.pow 2 (by
                intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hprod; exact (mul_pos hA_pos hB_pos).ne' hprod),
              hv_qn] at hv_prod
            have hp_dvd_δ2 : p ∣ δ₂ := by
              have hp_mem : p ∈ A.primeFactors.filter (fun p => padicValNat p A % 2 = 1) := by
                refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpA, hA_pos.ne'⟩, ?_⟩
                omega
              exact Finset.dvd_prod_of_mem _ hp_mem
            have hp2_qn : p * p ∣ qn n := hδ₁ ▸ mul_dvd_mul hp_dvd_δ2 hpδ1
            exact hp.not_unit (squarefree_qn n p hp2_qn)
          exact (hcop_z2_δ1.pow_left 2).dvd_of_dvd_mul_left h1
        exact Nat.pow_dvd_pow_iff_left (by norm_num) |>.mp hsq_dvd
      obtain ⟨z₁, hz₁⟩ := hz2_dvd_sn
      refine ⟨δ₂, z₂, z₁, hδ₂_sqf, hA_eq, ?_, hnot2⟩
      rw [hδ₁_eq]
      have hz2_pos : 0 < z₂ := by intro h0; rw [h0, zero_pow (by norm_num), mul_zero] at hA_eq; omega
      have h1 : B * z₂ ^ 2 = δ₁ * (z₁ ^ 2) * z₂ ^ 2 := by
        calc B * z₂ ^ 2 = δ₁ * (sn n / 2) ^ 2 := hB_mul
          _ = δ₁ * (z₂ * z₁) ^ 2 := by rw [hz₁]
          _ = δ₁ * z₁ ^ 2 * z₂ ^ 2 := by ring
      exact mul_right_cancel₀ (pow_ne_zero 2 hz2_pos.ne') h1
    · rintro ⟨_, _, _, _, _, _, hnot2⟩
      rcases hk with hk1_eq | hk2_eq
      · exact hk1_eq
      · exact absurd (hpart1.mp hk2_eq) hnot2
  refine ⟨hpart1, hpart2, ?_⟩
  intro hk2
  haveI : Fact (¬ IsSquare (-(qn n : ℚ))) := ⟨by
    rintro ⟨r, hr⟩
    have hpos : (0 : ℚ) < qn n := by exact_mod_cast qn_pos n
    have hsq : 0 ≤ r * r := mul_self_nonneg r
    linarith⟩
  have hp_exists : ∃ p : ℕ, p.Prime ∧ p ∣ qn n ∧ (4 * p < qn n ∨ (qn n = 6 ∧ p = 2)) := by
    by_cases hn4 : n = 4
    · subst hn4
      have hqn4 : qn 4 = 6 := by rw [← qnFast_eq_qn 4]; decide
      exact ⟨2, by decide, by rw [hqn4]; decide, Or.inr ⟨hqn4, rfl⟩⟩
    · by_cases hn5 : n = 5
      · subst hn5
        have hqn5 : qn 5 = 30 := by rw [← qnFast_eq_qn 5]; decide
        exact ⟨2, by decide, by rw [hqn5]; decide, Or.inl (by rw [hqn5]; decide)⟩
      · by_cases hn7 : n = 7
        · subst hn7
          have hqn7 : qn 7 = 35 := by rw [← qnFast_eq_qn 7]; decide
          exact ⟨5, by decide, by rw [hqn7]; decide, Or.inl (by rw [hqn7]; decide)⟩
        · by_cases hn8 : n ≤ 10 ^ 9
          · exact False.elim (berndt_galway_brocard_bound n m hsol (by omega) hn8)
          · push_neg at hn8
            obtain ⟨p₁, hp₁, hlo₁, hhi₁⟩ := nagura_prime_interval ((n : ℝ) / 2) (by
              have : (10 ^ 9 : ℝ) < n := by exact_mod_cast hn8
              linarith)
            obtain ⟨p₂, hp₂, hlo₂, hhi₂⟩ := nagura_prime_interval ((3 : ℝ) * n / 5) (by
              have : (10 ^ 9 : ℝ) < n := by exact_mod_cast hn8
              linarith)
            have hp_mem : ∀ q : ℕ, q.Prime → (n : ℝ) / 2 < q → (q : ℝ) ≤ n → q ∣ qn n := by
              intro q hq hqlo hqhi
              have hq_gt : n / 2 < q := by
                have : (n / 2 : ℕ) ≤ (n : ℝ) / 2 := by
                  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; exact_mod_cast Nat.div_mul_le_self n 2
                exact_mod_cast lt_of_le_of_lt this hqlo
              have hq_le : q ≤ n := by exact_mod_cast hqhi
              have hnsq : n < q ^ 2 := by nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n (by norm_num : 0 < 2)]
              have hv : padicValNat q n.factorial = 1 := by
                rw [padicValNat_factorial_of_lt_sq hq hnsq]
                rw [Nat.div_eq_iff_eq_mul_add_mod] <;> omega
              rw [qn_eq_prod_Podd]
              exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.two_le, hq_le⟩, hq, by rw [hv]; decide⟩)
            have hp₁_dvd : p₁ ∣ qn n := hp_mem p₁ hp₁ hlo₁ (by linarith)
            have hp₂_dvd : p₂ ∣ qn n := hp_mem p₂ hp₂ hlo₂ (by linarith)
            have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast lt_trans hhi₁ hlo₂
            have hp₁_gt4 : 4 < p₁ := by
              have : (4 : ℝ) < (n : ℝ) / 2 := by
                have : (10 ^ 9 : ℝ) < n := by exact_mod_cast hn8
                linarith
              exact_mod_cast lt_trans this hlo₁
            have hmul_dvd : p₁ * p₂ ∣ qn n := (Nat.coprime_primes hp₁ hp₂).mpr hp₁_lt_p₂.ne |>.mul_dvd_of_dvd_of_dvd hp₁_dvd hp₂_dvd
            have hle_qn : p₁ * p₂ ≤ qn n := Nat.le_of_dvd (qn_pos n) hmul_dvd
            exact ⟨p₁, hp₁, hp₁_dvd, Or.inl (by nlinarith)⟩
  obtain ⟨p, hp, hp_dvd, hp_cond⟩ := hp_exists
  let K := QuadField (-(qn n : ℚ))
  let 𝒪 := NumberField.RingOfIntegers K
  let ωK : K := ⟨0, 1⟩
  have hω_int : IsIntegral ℤ ωK := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (qn n : ℤ), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, eq_intCast]
    ext <;> simp [ωK, sq, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  let ω : 𝒪 := ⟨ωK, hω_int⟩
  have hω_sq : ω ^ 2 = -((qn n : ℤ) : 𝒪) := by
    ext
    simp only [SubmonoidClass.coe_pow, NegMemClass.coe_neg, Int.cast_natCast]
    ext <;> simp [ω, ωK, sq, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  let I : Ideal 𝒪 := Ideal.span {(p : 𝒪), ω}
  have hI_ne0 : I ≠ 0 := by
    intro h0
    have hp_mem : (p : 𝒪) ∈ I := Ideal.subset_span (Set.mem_insert _ _)
    rw [h0, Ideal.mem_bot] at hp_mem
    have hp_K : ((p : 𝒪) : K) = 0 := congr_arg Subtype.val hp_mem
    have hp_re : ((p : 𝒪) : K).re = 0 := congr_arg QuadraticAlgebra.re hp_K
    simp only [Int.cast_natCast, AddSubgroupClass.coe_natCast, QuadraticAlgebra.re_natCast, Nat.cast_eq_zero] at hp_re
    exact hp.ne_zero hp_re
  have hI_sq : I * I = Ideal.span {(p : 𝒪)} := by
    apply le_antisymm
    · rw [Ideal.mul_le]
      intro a ha b hb
      have ha' : a ∈ Ideal.span {(p : 𝒪), ω} := ha
      have hb' : b ∈ Ideal.span {(p : 𝒪), ω} := hb
      rw [Ideal.mem_span_pair] at ha' hb'
      rcases ha' with ⟨x₁, y₁, rfl⟩
      rcases hb' with ⟨x₂, y₂, rfl⟩
      have h_eq : (x₁ * (p : 𝒪) + y₁ * ω) * (x₂ * (p : 𝒪) + y₂ * ω) =
          (x₁ * x₂ * (p : 𝒪) + x₁ * y₂ * ω + y₁ * x₂ * ω - y₁ * y₂ * ((qn n / p : ℕ) : 𝒪)) * (p : 𝒪) := by
        have hqn_eq : ((qn n : ℤ) : 𝒪) = ((qn n / p : ℕ) : 𝒪) * (p : 𝒪) := by
          have : qn n = (qn n / p) * p := (Nat.div_mul_cancel hp_dvd).symm
          exact_mod_cast congr_arg (Nat.cast (R := 𝒪)) this
        calc (x₁ * (p : 𝒪) + y₁ * ω) * (x₂ * (p : 𝒪) + y₂ * ω)
            = x₁ * x₂ * (p : 𝒪) * (p : 𝒪) + x₁ * y₂ * (p : 𝒪) * ω + y₁ * x₂ * ω * (p : 𝒪) + y₁ * y₂ * ω ^ 2 := by ring
          _ = x₁ * x₂ * (p : 𝒪) * (p : 𝒪) + x₁ * y₂ * (p : 𝒪) * ω + y₁ * x₂ * ω * (p : 𝒪) - y₁ * y₂ * ((qn n : ℤ) : 𝒪) := by
              rw [hω_sq]; ring
          _ = (x₁ * x₂ * (p : 𝒪) + x₁ * y₂ * ω + y₁ * x₂ * ω - y₁ * y₂ * ((qn n / p : ℕ) : 𝒪)) * (p : 𝒪) := by
              rw [hqn_eq]; ring
      rw [h_eq]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    · rw [Ideal.span_singleton_le_iff_mem]
      have hcop : IsCoprime (p : ℤ) ((qn n / p : ℕ) : ℤ) := by
        refine (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr fun hdvd => ?_
        have hp2 : p * p ∣ qn n := by
          have : qn n = p * (qn n / p) := (Nat.mul_div_cancel' hp_dvd).symm
          rw [this]
          exact mul_dvd_mul_left p (by exact_mod_cast hdvd)
        exact hp.not_unit (squarefree_qn n p hp2)
      obtain ⟨a, b, hab⟩ := hcop
      have hp_id : (p : 𝒪) = (a : 𝒪) * ((p : 𝒪) * (p : 𝒪)) - (b : 𝒪) * (ω * ω) := by
        have hZ : (p : ℤ) = a * ((p : ℤ) * (p : ℤ)) + b * (qn n : ℤ) := by
          have h1 : (qn n : ℤ) = (p : ℤ) * ((qn n / p : ℕ) : ℤ) := by
            exact_mod_cast (Nat.mul_div_cancel' hp_dvd).symm
          linarith [show a * (p : ℤ) + b * ((qn n / p : ℕ) : ℤ) = 1 from hab]
        have hO : (p : 𝒪) = (a : 𝒪) * ((p : 𝒪) * (p : 𝒪)) + (b : 𝒪) * ((qn n : ℤ) : 𝒪) := by
          exact_mod_cast congr_arg (Int.cast (R := 𝒪)) hZ
        rw [hO, show ω * ω = ω ^ 2 from (sq ω).symm, hω_sq]
        ring
      rw [hp_id]
      have hp_mem : (p : 𝒪) ∈ I := Ideal.subset_span (Set.mem_insert _ _)
      have hω_mem : ω ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hp_mem hp_mem))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hω_mem hω_mem))
  let g : ClassGroup 𝒪 := ClassGroup.mk0 I hI_ne0
  have hg_sq : g ^ 2 = 1 := by
    have hp_ne0 : Ideal.span {(p : 𝒪)} ≠ 0 := by
      intro h0
      have hp_mem : (p : 𝒪) ∈ Ideal.span {(p : 𝒪)} := Ideal.subset_span (Set.mem_singleton _)
      rw [h0, Ideal.mem_bot] at hp_mem
      have hp_re : ((p : 𝒪) : K).re = 0 := congr_arg QuadraticAlgebra.re (congr_arg Subtype.val hp_mem)
      simp only [Int.cast_natCast, AddSubgroupClass.coe_natCast, QuadraticAlgebra.re_natCast, Nat.cast_eq_zero] at hp_re
      exact hp.ne_zero hp_re
    calc g ^ 2 = g * g := sq g
      _ = ClassGroup.mk0 (I * I) (mul_ne_zero hI_ne0 hI_ne0) := (ClassGroup.mk0_mul I I hI_ne0 hI_ne0).symm
      _ = ClassGroup.mk0 (Ideal.span {(p : 𝒪)}) hp_ne0 := by congr 1; exact hI_sq
      _ = 1 := ClassGroup.mk0_principal (p : 𝒪) (by
          intro h0
          have hp_re : ((p : 𝒪) : K).re = 0 := congr_arg QuadraticAlgebra.re (congr_arg Subtype.val h0)
          simp only [Int.cast_natCast, AddSubgroupClass.coe_natCast, QuadraticAlgebra.re_natCast, Nat.cast_eq_zero] at hp_re
          exact hp.ne_zero hp_re)
  have hg_ne1 : g ≠ 1 := by
    intro h1
    rw [ClassGroup.mk0_eq_one_iff] at h1
    obtain ⟨α, hα_ne0, hI_eq⟩ := h1
    have hα2_eq : Ideal.span {α ^ 2} = Ideal.span {(p : 𝒪)} := by
      calc Ideal.span {α ^ 2} = Ideal.span {α} * Ideal.span {α} := by
            rw [Ideal.span_singleton_mul_span_singleton, sq]
        _ = I * I := by rw [← hI_eq]
        _ = Ideal.span {(p : 𝒪)} := hI_sq
    have hassoc : Associated (α ^ 2) (p : 𝒪) := Ideal.span_singleton_eq_span_singleton.mp hα2_eq
    obtain ⟨u, hu⟩ := hassoc
    have hnorm_formula : ∀ z : K, Algebra.norm ℚ z = z.re ^ 2 + (qn n : ℚ) * z.im ^ 2 := by
      intro z
      rw [QuadraticField.norm_eq]
      ring
    have hnorm_nn : ∀ z : K, 0 ≤ Algebra.norm ℚ z := fun z => by
      rw [hnorm_formula]
      have hq : (0 : ℚ) ≤ qn n := by exact_mod_cast (qn_pos n).le
      positivity
    have hnorm_u : Algebra.norm ℚ ((u : 𝒪) : K) = 1 := by
      have hu_int : Algebra.norm ℤ (u : 𝒪) = 1 ∨ Algebra.norm ℤ (u : 𝒪) = -1 := by
        have hunit : IsUnit (Algebra.norm ℤ (u : 𝒪)) := (u.isUnit.map (Algebra.norm ℤ).toMonoidHom)
        exact Int.isUnit_iff.mp hunit
      have hcoe : (Algebra.norm ℤ (u : 𝒪) : ℚ) = Algebra.norm ℚ ((u : 𝒪) : K) :=
        (Algebra.coe_norm_int (u : 𝒪)).symm
      rcases hu_int with h | h <;> rw [h] at hcoe
      · exact hcoe.symm
      · have := hnorm_nn ((u : 𝒪) : K)
        linarith
    have hnorm_p : Algebra.norm ℚ ((p : 𝒪) : K) = (p : ℚ) ^ 2 := by
      have h1 : ((p : 𝒪) : K) = algebraMap ℚ K (p : ℚ) := by
        ext <;> simp
      rw [h1, Algebra.norm_algebraMap, QuadraticField.finrank]
    have hnorm_eq : (Algebra.norm ℚ (α : K)) ^ 2 = (p : ℚ) ^ 2 := by
      have huK : ((α : K) ^ 2) * ((u : 𝒪) : K) = ((p : 𝒪) : K) := by exact_mod_cast congr_arg Subtype.val hu
      have h := congr_arg (Algebra.norm ℚ) huK
      rw [map_mul, map_pow, hnorm_u, mul_one, hnorm_p] at h
      exact h
    have hnorm_α : Algebra.norm ℚ (α : K) = (p : ℚ) := by
      have hnn := hnorm_nn (α : K)
      nlinarith
    have htr_int : IsIntegral ℤ (Algebra.trace ℚ (α : K)) :=
      Algebra.isIntegral_trace α.2
    have htr_eq : Algebra.trace ℚ (α : K) = 2 * (α : K).re := by
      rw [QuadraticField.trace_eq]
    have h2re_rat : ∃ A : ℤ, (A : ℚ) = 2 * (α : K).re := by
      rw [htr_eq] at htr_int
      exact IsIntegrallyClosed.isIntegral_iff.mp htr_int
    obtain ⟨A, hA⟩ := h2re_rat
    have h_im_int : IsIntegral ℤ (⟨0, 2 * (α : K).im⟩ : K) := by
      have heq : (⟨0, 2 * (α : K).im⟩ : K) = 2 * (α : K) - algebraMap ℤ K A := by
        ext <;> simp [hA]
      rw [heq]
      exact IsIntegral.sub (IsIntegral.mul isIntegral_of_noetherian α.2) isIntegral_algebraMap
    have h_sq_int : IsIntegral ℤ (-4 * (qn n : ℚ) * (α : K).im ^ 2) := by
      have h1 : (⟨0, 2 * (α : K).im⟩ : K) ^ 2 = algebraMap ℚ K (-4 * (qn n : ℚ) * (α : K).im ^ 2) := by
        ext <;> simp [sq, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
      have h2 := h_im_int.pow 2
      rw [h1] at h2
      exact h2
    obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp h_sq_int
    have h2im_rat : ∃ B : ℤ, (B : ℚ) = 2 * (α : K).im := by
      set y := 2 * (α : K).im
      have hMy : (M : ℤ) = y.num ^ 2 * (-qn n : ℤ) ∧ y.den ^ 2 ∣ 1 := by
        have hq : -(qn n : ℚ) * y ^ 2 = (M : ℚ) := by
          have : -4 * (qn n : ℚ) * (α : K).im ^ 2 = (M : ℚ) := hM
          linarith [show -4 * (qn n : ℚ) * (α : K).im ^ 2 = -(qn n : ℚ) * y ^ 2 by simp only [y]; ring]
        have hy_eq : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
        rw [hy_eq] at hq
        have hden_ne : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
        field_simp [hden_ne] at hq
        have hZ : -(qn n : ℤ) * y.num ^ 2 = (M : ℤ) * (y.den : ℤ) ^ 2 := by exact_mod_cast hq
        have hden_dvd : y.den ^ 2 ∣ qn n * y.num.natAbs ^ 2 := by
          have hnat : qn n * y.num.natAbs ^ 2 = M.natAbs * y.den ^ 2 := by
            have := congr_arg Int.natAbs hZ
            simpa [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow] using this
          exact ⟨M.natAbs, by linarith⟩
        have hcop_sq : Nat.Coprime (y.num.natAbs ^ 2) (y.den ^ 2) := y.reduced.pow 2 2
        have hden_dvd_qn : y.den ^ 2 ∣ qn n := hcop_sq.symm.dvd_of_dvd_mul_right hden_dvd
        have hden1 : y.den = 1 := by
          by_contra hne
          obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
          have hq2 : q * q ∣ qn n := dvd_trans (mul_dvd_mul hq_dvd hq_dvd) (by simpa [sq] using hden_dvd_qn)
          exact hq_prime.not_unit (squarefree_qn n q hq2)
        refine ⟨0, by simp [hden1]⟩
      -- Directly from `y.den = 1`:
      have hden1 : y.den = 1 := hMy.2 |> Nat.eq_one_of_dvd_one
      exact ⟨y.num, by rw [← Rat.num_div_den y, hden1]; simp⟩
    obtain ⟨B, hB⟩ := h2im_rat
    have h_eq_int : A ^ 2 + (qn n : ℤ) * B ^ 2 = 4 * (p : ℤ) := by
      have h1 : (A : ℚ) ^ 2 + (qn n : ℚ) * (B : ℚ) ^ 2 = 4 * (p : ℚ) := by
        have h2 := hnorm_α
        rw [hnorm_formula] at h2
        rw [hA, hB]
        linarith
      exact_mod_cast h1
    rcases hp_cond with hlt | ⟨hqn6, rfl⟩
    · have hB0 : B = 0 := by
        by_contra hne
        have hB2 : 1 ≤ B ^ 2 := by nlinarith [sq_nonneg B, Int.le_sub_one_of_lt (show 0 < B.natAbs by omega)]
        have hqnB : (qn n : ℤ) ≤ (qn n : ℤ) * B ^ 2 := le_mul_of_one_le_right (by exact_mod_cast (qn_pos n).le) hB2
        linarith [sq_nonneg A]
      rw [hB0, zero_pow (by norm_num), mul_zero, add_zero] at h_eq_int
      have hp_dvd_A : (p : ℤ) ∣ A := by
        have hd : (p : ℤ) ∣ A ^ 2 := ⟨4, by linarith⟩
        exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hd
      obtain ⟨C, hC⟩ := hp_dvd_A
      rw [hC, mul_pow] at h_eq_int
      have hC2 : (p : ℤ) * C ^ 2 = 4 := by
        have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        nlinarith
      have hp_dvd4 : p ∣ 4 := by
        have : (p : ℤ) ∣ 4 := ⟨C ^ 2, hC2.symm⟩
        exact_mod_cast this
      have hp2 : p = 2 := by
        have := hp.two_le
        have := Nat.le_of_dvd (by norm_num) hp_dvd4
        rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with rfl | rfl | rfl
        · rfl
        · norm_num at hp_dvd4
        · exact absurd hp (by decide)
      subst hp2
      nlinarith
    · rw [hqn6] at h_eq_int
      have hB2 : B ^ 2 ≤ 1 := by nlinarith [sq_nonneg A]
      have hB_cases : B = 0 ∨ B = 1 ∨ B = -1 := by
        rcases le_or_gt B 1 with h1 | h1 <;> rcases le_or_gt (-1) B with h2 | h2
        · omega
        · nlinarith
        · nlinarith
        · nlinarith
      rcases hB_cases with rfl | rfl | rfl <;> norm_num at h_eq_int
      · have : A ^ 2 = 8 := by linarith
        rcases le_or_gt A 2 with h1 | h1 <;> rcases le_or_gt (-2) A with h2 | h2 <;> nlinarith
      · have : A ^ 2 = 2 := by linarith
        rcases le_or_gt A 1 with h1 | h1 <;> rcases le_or_gt (-1) A with h2 | h2 <;> nlinarith
      · have : A ^ 2 = 2 := by linarith
        rcases le_or_gt A 1 with h1 | h1 <;> rcases le_or_gt (-1) A with h2 | h2 <;> nlinarith
  have hord : orderOf g = 2 := orderOf_eq_iff (by norm_num) |>.mpr
    ⟨hg_sq, fun m hm hm0 => by have : m = 1 := by omega; subst this; simpa using hg_ne1⟩
  change 2 ∣ Fintype.card (ClassGroup 𝒪)
  rw [← hord]
  exact orderOf_dvd_card

end

end BrocardFormalization

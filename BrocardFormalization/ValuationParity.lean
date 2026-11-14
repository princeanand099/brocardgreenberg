/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParityLayer
import BrocardFormalization.ValuationParityDensity
import BrocardFormalization.ValuationParityDigits
import BrocardFormalization.ValuationParityMoments
import BrocardFormalization.ExpSumBounds
import BrocardFormalization.ExpSumMod

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

theorem lemma_2_1_ii :
    (∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      |Real.log (qn n) - Real.log 2 * (n : ℝ)| ≤
        C * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n))) ∧
    Tendsto (fun n : ℕ => ((Podd n).card : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (Real.log 2)) :=
  ⟨lemma_2_1_ii_part1, lemma_2_1_ii_part2⟩

theorem lemma_2_4_i (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
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
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
          C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 ∧
        C_δ * W₀ * P * (T₀ ^ (-1 / 6 : ℝ) + P ^ (-η'_δ)) * (Real.log P) ^ 3 ≤
          C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) :=
  lemma_2_4_i_impl δ hδ0 hδ1

theorem lemma_2_4_ii (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    ∃ (η_δ C_δ : ℝ), 0 < η_δ ∧ 0 < C_δ ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧
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
        T₀ ≥ (n : ℝ) ^ (δ / 2) →
        ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
          C_δ * W₀ * P * (n : ℝ) ^ (-η_δ) :=
  lemma_2_4_ii_impl δ hδ0 hδ1

/-! ### Helper Lemmas for Section 2.5 -/

private lemma ePhase_add' (x y : ℝ) : ePhase (x + y) = ePhase x * ePhase y := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma ePhase_int' (m : ℤ) : ePhase (m : ℝ) = 1 := by
  unfold ePhase
  rw [show (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

private lemma ePhase_pow_nat (t : ℝ) (k : ℕ) : (ePhase t) ^ k = ePhase ((k : ℝ) * t) := by
  unfold ePhase; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private lemma ePhase_eq_one_iff_int (t : ℝ) : ePhase t = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ePhase
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpi : (2 * Real.pi * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h1 : (t : ℂ) = (k : ℂ) :=
      mul_right_cancel₀ hpi (by linear_combination hk : (t : ℂ) * (2 * Real.pi * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I))
    exact_mod_cast h1
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

private lemma char_orthogonality_mod (h : ℕ) (hh : 1 ≤ h) (x : ℤ) :
    ∑ t ∈ Finset.range h, ePhase ((t : ℝ) * (x : ℝ) / h) =
      if (h : ℤ) ∣ x then (h : ℂ) else 0 := by
  split_ifs with hdvd
  · rcases hdvd with ⟨k, rfl⟩
    have hsum : ∑ t ∈ Finset.range h, ePhase ((t : ℝ) * (((h : ℤ) * k : ℤ) : ℝ) / h) =
        ∑ _t ∈ Finset.range h, (1 : ℂ) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
      have heq : (t : ℝ) * (((h : ℤ) * k : ℤ) : ℝ) / h = ((t : ℤ) * k : ℤ) := by
        push_cast; field_simp [hh0]
      rw [heq, ePhase_int']
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · set ζ := ePhase ((x : ℝ) / h)
    have hζ_ne : ζ ≠ 1 := by
      intro h1
      rw [ePhase_eq_one_iff_int] at h1
      rcases h1 with ⟨m, hm⟩
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
      have hx : (x : ℝ) = ((h : ℤ) * m : ℤ) := by push_cast; field_simp [hh0] at hm; linarith
      exact hdvd ⟨m, by exact_mod_cast hx⟩
    have hsum_eq : ∑ t ∈ Finset.range h, ePhase ((t : ℝ) * (x : ℝ) / h) = ∑ t ∈ Finset.range h, ζ ^ t := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [ePhase_pow_nat]; congr 1; ring
    rw [hsum_eq, geom_sum_eq hζ_ne, ePhase_pow_nat]
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
    rw [show (h : ℝ) * ((x : ℝ) / h) = (x : ℝ) by field_simp [hh0], ePhase_int', sub_self, zero_div]

private lemma dyadic_Icc_partition {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (f : ℕ → ℂ) :
    ∑ p ∈ Finset.Icc A B, f p =
      ∑ k ∈ (Finset.range (Nat.log 2 B + 1)).filter (fun k => A * 2 ^ k ≤ B),
        ∑ p ∈ Finset.Icc (A * 2 ^ k) (min B (2 * (A * 2 ^ k) - 1)), f p := by
  have hdisj : Set.PairwiseDisjoint
      ↑((Finset.range (Nat.log 2 B + 1)).filter (fun k => A * 2 ^ k ≤ B))
      (fun k => Finset.Icc (A * 2 ^ k) (min B (2 * (A * 2 ^ k) - 1))) := by
    intro k₁ _ k₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_Icc] at hp₁ hp₂
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hpow : 2 * (A * 2 ^ k₁) ≤ A * 2 ^ k₂ := by
        calc 2 * (A * 2 ^ k₁) = A * 2 ^ (k₁ + 1) := by ring
          _ ≤ A * 2 ^ k₂ := Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hlt)
      omega
    · have hpow : 2 * (A * 2 ^ k₂) ≤ A * 2 ^ k₁ := by
        calc 2 * (A * 2 ^ k₂) = A * 2 ^ (k₂ + 1) := by ring
          _ ≤ A * 2 ^ k₁ := Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hlt)
      omega
  rw [← Finset.sum_biUnion hdisj]
  congr 1
  ext p
  simp only [Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hp
    set k := Nat.log 2 (p / A)
    have hq_pos : 0 < p / A := Nat.div_pos hp.1 hA
    have hk_lo : 2 ^ k ≤ p / A := Nat.pow_log_le_self 2 hq_pos.ne'
    have hk_hi : p / A < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p / A)
    have hAk_le : A * 2 ^ k ≤ p := by
      calc A * 2 ^ k ≤ A * (p / A) := Nat.mul_le_mul_left A hk_lo
        _ ≤ p := Nat.mul_div_le p A
    have hp_lt : p < 2 * (A * 2 ^ k) := by
      have h1 : p < A * (p / A + 1) := by nlinarith [Nat.div_add_mod p A, Nat.mod_lt p hA]
      calc p < A * (p / A + 1) := h1
        _ ≤ A * 2 ^ (k + 1) := Nat.mul_le_mul_left A hk_hi
        _ = 2 * (A * 2 ^ k) := by ring
    have hk_log : k < Nat.log 2 B + 1 := by
      have hk_le : 2 ^ k ≤ B := le_trans (le_trans (Nat.le_mul_of_pos_left _ hA) hAk_le) hp.2
      exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) hk_le)
    exact ⟨k, ⟨hk_log, le_trans hAk_le hp.2⟩, hAk_le, le_min hp.2 (by omega)⟩
  · rintro ⟨k, ⟨_, _⟩, hp1, hp2⟩
    have h1 : A ≤ A * 2 ^ k := Nat.le_mul_of_pos_right A (pow_pos (by norm_num) k)
    exact ⟨le_trans h1 hp1, le_trans hp2 (min_le_left _ _)⟩

private lemma sum_Icc_log_eq_theta_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Finset.Icc (⌊a⌋₊ + 1) ⌊b⌋₊).filter Nat.Prime, Real.log p =
      Chebyshev.theta b - Chebyshev.theta a := by
  unfold Chebyshev.theta
  have hsub : (Finset.Ioc 0 ⌊a⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊b⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono hab)⟩, hp.2⟩
  have hsdiff : (Finset.Ioc 0 ⌊b⌋₊).filter Nat.Prime \ (Finset.Ioc 0 ⌊a⌋₊).filter Nat.Prime =
      (Finset.Icc (⌊a⌋₊ + 1) ⌊b⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp0, hpb⟩, hp⟩, hnot⟩
      have hpa : ⌊a⌋₊ < p := by by_contra hle; exact hnot ⟨⟨hp0, by omega⟩, hp⟩
      exact ⟨⟨by omega, hpb⟩, hp⟩
    · rintro ⟨⟨hpa, hpb⟩, hp⟩
      exact ⟨⟨⟨by omega, hpb⟩, hp⟩, fun h => by omega⟩
  rw [← Finset.sum_sdiff hsub, hsdiff]
  ring

private lemma alt_harmonic_tail_bound (J : ℕ) :
    |∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1)| ≤
      1 / ((J : ℝ) + 1) := by
  have hint_log : ∫ t in (0 : ℝ)..1, (1 + t)⁻¹ = Real.log 2 := by
    have h := intervalIntegral.integral_comp_add_right (fun t : ℝ => t⁻¹) (1 : ℝ) (a := 0) (b := 1)
    simp only [zero_add] at h
    have hcomm : (∫ t in (0 : ℝ)..1, (1 + t)⁻¹) = ∫ t in (0 : ℝ)..1, (t + 1)⁻¹ :=
      intervalIntegral.integral_congr fun t _ => by ring
    rw [hcomm, h, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have hsum_eq : ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) + 1 =
      ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / ((j : ℝ) + 1) := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_Icc_succ_top (by omega), add_right_comm, ih, Finset.sum_range_succ]
      push_cast; ring
  have hint_pow : ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / ((j : ℝ) + 1) =
      ∫ t in (0 : ℝ)..1, ∑ j ∈ Finset.range (J + 1), (-t) ^ j := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hpow : (fun t : ℝ => (-t) ^ j) = (fun t : ℝ => (-1 : ℝ) ^ j * t ^ j) := by
        ext t; rw [neg_eq_neg_one_mul, mul_pow]
      rw [hpow, intervalIntegral.integral_const_mul, integral_pow]
      ring
    · intro j _; exact (continuous_neg.pow j).intervalIntegrable 0 1
  have hdiff_eq : ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1) =
      (-1 : ℝ) ^ (J + 1) * ∫ t in (0 : ℝ)..1, t ^ (J + 1) / (1 + t) := by
    have h1 : ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1) =
        (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / ((j : ℝ) + 1)) - Real.log 2 := by
      linarith [hsum_eq]
    rw [h1, hint_pow, ← hint_log, ← intervalIntegral.integral_sub, ← intervalIntegral.integral_const_mul]
    · refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have h1t : 1 + t ≠ 0 := by linarith [ht'.1]
      have hgeom : (1 + t) * ∑ j ∈ Finset.range (J + 1), (-t) ^ j = 1 - (-t) ^ (J + 1) := by
        have := geom_sum_mul (-t) (J + 1)
        calc (1 + t) * ∑ j ∈ Finset.range (J + 1), (-t) ^ j
            = -((-t - 1) * ∑ j ∈ Finset.range (J + 1), (-t) ^ j) := by ring
          _ = -((-t) ^ (J + 1) - 1) := by rw [mul_comm (-t - 1), this]
          _ = 1 - (-t) ^ (J + 1) := by ring
      have hpow : (-t) ^ (J + 1) = (-1 : ℝ) ^ (J + 1) * t ^ (J + 1) := by
        rw [neg_eq_neg_one_mul, mul_pow]
      field_simp [h1t]
      linarith [hgeom, hpow]
    · exact (continuous_finsetSum _ fun j _ => continuous_neg.pow j).intervalIntegrable 0 1
    · exact ContinuousOn.intervalIntegrable (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact ((continuousAt_const.add continuousAt_id).inv₀ (by linarith [ht'.1])).continuousWithinAt)
  rw [hdiff_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, t ^ (J + 1) / (1 + t) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht =>
      div_nonneg (pow_nonneg ht.1 _) (by linarith [ht.1])
  rw [abs_of_nonneg hnonneg]
  have hle_pow : ∫ t in (0 : ℝ)..1, t ^ (J + 1) / (1 + t) ≤ ∫ t in (0 : ℝ)..1, t ^ (J + 1) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ((continuous_id.pow (J + 1)).intervalIntegrable 0 1) ?_
    · exact ContinuousOn.intervalIntegrable (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact ((continuousAt_id.pow _).div (continuousAt_const.add continuousAt_id) (by linarith [ht'.1])).continuousWithinAt)
    · intro t ht; exact div_le_self (pow_nonneg ht.1 _) (by linarith [ht.1])
  have hint_mono : ∫ t in (0 : ℝ)..1, t ^ (J + 1) = 1 / ((J : ℝ) + 2) := by
    rw [integral_pow]; push_cast; ring
  have h2le1 : (1 : ℝ) / ((J : ℝ) + 2) ≤ 1 / ((J : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

private lemma padicValNat_factorial_upper_rpow {n p : ℕ} (hp : p.Prime) :
    (padicValNat p n.factorial : ℝ) ≤ 2 * (n : ℝ) / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
  have h1 : (p - 1) * padicValNat p n.factorial ≤ n := by nlinarith
  have h1R : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) ≤ n := by exact_mod_cast h1
  have hp2 : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [le_div_iff₀ hp_pos]
  nlinarith

private lemma padicValNat_factorial_eq_sum_floor {n p R : ℕ} (hp : p.Prime)
    (hp_gt : n < p ^ (R + 1)) :
    padicValNat p n.factorial = ∑ r ∈ Finset.Icc 1 R, n / p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (b := R + 1) hp_gt, ← Finset.Ico_succ_right_eq_Icc]
  exact Finset.sum_congr rfl fun _ _ => rfl

private lemma w_inv_bound_and_tv (n : ℕ) {P : ℝ} (hP : 0 < P) :
    let w : ℝ → ℝ := fun t => (n : ℝ) / t
    let W₀ : ℝ := (n : ℝ) / P
    0 ≤ W₀ ∧
    (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) ∧
    ContDiffOn ℝ 1 w (Set.Icc P (2 * P)) ∧
    (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ := by
  intro w W₀
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hP ht.1
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) ht_pos.le)]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hP ht.1
  · refine contDiffOn_const.div contDiffOn_id (fun t ht => (lt_of_lt_of_le hP ht.1).ne')
  · have h_int : ∫ t in P..(2 * P), |deriv w t| = ∫ t in P..(2 * P), (n : ℝ) * (t ^ 2)⁻¹ := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Set.Icc P (2 * P) := by simpa [Set.uIcc_of_le (by linarith : P ≤ 2 * P)] using ht
      have ht_pos : 0 < t := lt_of_lt_of_le hP ht'.1
      have hderiv : deriv w t = -(n : ℝ) / t ^ 2 := by
        have h1 : HasDerivAt w (-(n : ℝ) / t ^ 2) t := by
          simpa [w] using (hasDerivAt_inv ht_pos.ne').const_mul (n : ℝ)
        exact h1.deriv
      rw [hderiv, abs_neg, abs_div, abs_of_nonneg (Nat.cast_nonneg n), abs_of_pos (pow_pos ht_pos 2), div_eq_mul_inv]
    rw [h_int, intervalIntegral.integral_const_mul]
    have hint : ∫ t in P..(2 * P), (t ^ 2)⁻¹ = 1 / (2 * P) := by
      have h1 : ∫ t in P..(2 * P), t ^ (-2 : ℤ) = ((2 * P) ^ (-1 : ℤ) - P ^ (-1 : ℤ)) / (-1 : ℝ) := by
        rw [integral_zpow (by right; intro h; have : P ≤ 0 ∧ 0 ≤ 2 * P := by simpa [Set.uIcc_of_le (by linarith : P ≤ 2 * P)] using h; linarith)]
        norm_num
      have h2 : ∫ t in P..(2 * P), (t ^ 2)⁻¹ = ∫ t in P..(2 * P), t ^ (-2 : ℤ) := by
        refine intervalIntegral.integral_congr fun t _ => by rw [zpow_neg, zpow_two]
      rw [h2, h1, zpow_neg_one, zpow_neg_one]
      field_simp [hP.ne']; ring
    rw [hint]
    have : (n : ℝ) * (1 / (2 * P)) = (n : ℝ) / (2 * P) := by ring
    rw [this]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hP (by linarith)

private lemma w_inv_one_bound_and_tv {P : ℝ} (hP : 2 ≤ P) :
    let w : ℝ → ℝ := fun t => 1 / (t - 1)
    let W₀ : ℝ := 2 / P
    0 ≤ W₀ ∧
    (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) ∧
    ContDiffOn ℝ 1 w (Set.Icc P (2 * P)) ∧
    (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ := by
  intro w W₀
  have hP_pos : 0 < P := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · intro t ht
    have ht1 : 0 < t - 1 := by linarith [ht.1]
    rw [abs_of_nonneg (one_div_nonneg.mpr ht1.le)]
    exact one_div_le_div_of_le (by positivity) (by linarith [ht.1])
  · exact contDiffOn_const.div (contDiffOn_id.sub contDiffOn_const) (fun t ht => by linarith [ht.1])
  · have h_int_eq : ∫ t in P..(2 * P), |deriv w t| = ∫ t in P..(2 * P), (t - 1) ^ (-2 : ℤ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Set.Icc P (2 * P) := by simpa [Set.uIcc_of_le (by linarith : P ≤ 2 * P)] using ht
      have ht1 : 0 < t - 1 := by linarith [ht'.1]
      have hder : HasDerivAt w (-1 / (t - 1) ^ 2) t := by
        simpa [w, one_div] using ((hasDerivAt_id t).sub_const 1).inv ht1.ne'
      rw [hder.deriv, abs_div, abs_neg, abs_one, abs_of_pos (pow_pos ht1 2), zpow_neg, zpow_two, one_div]
    have hcomp := intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ (-2 : ℤ)) (1 : ℝ) (a := P) (b := 2 * P)
    rw [h_int_eq, hcomp, integral_zpow]
    · rw [zpow_neg_one, zpow_neg_one]
      have hP1 : 0 < P - 1 := by linarith
      have h1 : 1 / (P - 1) ≤ 2 / P := by rw [div_le_div_iff₀ hP1 hP_pos]; linarith
      have h2 : 0 ≤ 1 / (2 * P - 1) := by positivity
      norm_num; linarith
    · right; intro h; have : P - 1 ≤ 0 ∧ 0 ≤ 2 * P - 1 := by simpa [Set.uIcc_of_le (by linarith : P - 1 ≤ 2 * P - 1)] using h; linarith

private lemma prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 15) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ 15 ^ s.card * ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx,
      Finset.sum_insert hx]
    have ha_s : ∀ i ∈ s, |a i| ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb_s : ∀ i ∈ s, |b i| ≤ 15 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih' := ih ha_s hb_s
    have hprod_a : |∏ i ∈ s, a i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) ha_s
    have hbx : |b x| ≤ 15 := hb x (Finset.mem_insert_self x s)
    have h1 : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        (a x - b x) * ∏ i ∈ s, a i + b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [h1]
    have hpow15 : (1 : ℝ) ≤ 15 ^ s.card := one_le_pow₀ (by norm_num)
    calc |(a x - b x) * ∏ i ∈ s, a i + b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i)|
        ≤ |(a x - b x) * ∏ i ∈ s, a i| + |b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := abs_add_le _ _
      _ = |a x - b x| * |∏ i ∈ s, a i| + |b x| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          rw [abs_mul, abs_mul]
      _ ≤ |a x - b x| * 1 + 15 * (15 ^ s.card * ∑ i ∈ s, |a i - b i|) :=
          add_le_add (mul_le_mul_of_nonneg_left hprod_a (abs_nonneg _))
            (mul_le_mul hbx ih' (abs_nonneg _) (by norm_num))
      _ ≤ 15 ^ (s.card + 1) * (|a x - b x| + ∑ i ∈ s, |a i - b i|) := by
          rw [pow_succ']
          have h15 : (1 : ℝ) ≤ 15 * 15 ^ s.card := by nlinarith
          nlinarith [abs_nonneg (a x - b x)]

private lemma sum_Icc_div_p_log_p_le :
    ∃ C_m : ℝ, 0 < C_m ∧ ∀ (A B : ℕ), 2 ≤ A →
      ∑ p ∈ (Finset.Icc A B).filter Nat.Prime, Real.log p / p ≤
        if A ≤ B then Real.log ((B : ℝ) / A) + C_m else 0 := by
  obtain ⟨C, hC, _, hm⟩ := mertens_first_theorem
  refine ⟨2 * C + 1, by linarith, fun A B hA => ?_⟩
  split_ifs with hAB
  · have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast le_trans hA hAB
    have hA_pos : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
    have hB_pos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    rw [Real.log_div hB_pos.ne' hA_pos.ne']
    by_cases hA3 : 3 ≤ A
    · have hA1 : (2 : ℝ) ≤ ((A - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ A - 1)
      have hsub : (Finset.Icc 2 (A - 1)).filter Nat.Prime ⊆ (Finset.Icc 2 B).filter Nat.Prime := by
        intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢; exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
      have hsdiff : (Finset.Icc 2 B).filter Nat.Prime \ (Finset.Icc 2 (A - 1)).filter Nat.Prime =
          (Finset.Icc A B).filter Nat.Prime := by
        ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]; omega
      have heq : ∑ p ∈ (Finset.Icc A B).filter Nat.Prime, Real.log p / p =
          (∑ p ∈ (Finset.Icc 2 B).filter Nat.Prime, Real.log p / p) -
            (∑ p ∈ (Finset.Icc 2 (A - 1)).filter Nat.Prime, Real.log p / p) := by
        rw [← hsdiff, Finset.sum_sdiff hsub]; ring
      have hmB := abs_le.mp (by simpa [Nat.floor_natCast] using hm B hB2)
      have hmA := abs_le.mp (by simpa [Nat.floor_natCast] using hm ((A - 1 : ℕ) : ℝ) hA1)
      have hlog_diff : Real.log (A : ℝ) - Real.log ((A - 1 : ℕ) : ℝ) ≤ 1 := by
        rw [← Real.log_div hA_pos.ne' (by linarith)]
        have hle : (A : ℝ) / ((A - 1 : ℕ) : ℝ) ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]
          have : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by exact_mod_cast (by omega : (A - 1 : ℤ) = A - 1)
          linarith [show (3 : ℝ) ≤ A by exact_mod_cast hA3]
        exact le_trans (Real.log_le_log (by positivity) hle) (by linarith [Real.log_two_lt_d9])
      linarith
    · have hA2 : A = 2 := by omega
      subst hA2
      have hmB := abs_le.mp (by simpa [Nat.floor_natCast] using hm B hB2)
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
  · have : (Finset.Icc A B).filter Nat.Prime = ∅ := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    simp [this]

private lemma single_r_vaaler_bound_i
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    let R : ℕ := ⌊1 / δ⌋₊
    let AR : ℕ := 6 * R + 30
    ∃ (C_v : ℝ) (N_v : ℕ), 0 < C_v ∧ 16 ≤ N_v ∧
      ∀ (n : ℕ) (P a b : ℝ) (r : ℕ) (w : ℝ → ℝ) (W₀ : ℝ),
        N_v ≤ n → (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log n) ^ 12 →
        P ≤ a → a ≤ b → b ≤ 2 * P →
        1 ≤ r → r ≤ R → (n : ℝ) / P ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR →
        0 ≤ W₀ → (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        ContDiffOn ℝ 1 w (Set.Icc P (2 * P)) →
        (∫ t in P..(2 * P), |deriv w t|) ≤ W₀ →
        ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p ^ r)‖ ≤
          C_v * W₀ * P * (Real.log n) ^ (-(R + 1 : ℤ)) := by
  intro R AR
  obtain ⟨η'_δ, C_δ, C'_δ, hη'_pos, hC_δ, hC'_δ, N_24, hN_24, h24⟩ := lemma_2_4_i δ hδ0 hδ1
  have h_ev : ∀ᶠ n : ℕ in atTop,
      N_24 ≤ n ∧ 2 ≤ Real.log n ∧ 1 ≤ ⌊(Real.log n) ^ (R + 2)⌋₊ ∧
      ((4 / Real.pi) * (Real.log (2 * ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1) + 1) + 1) + 12) ≤
        Real.log n := by
    have h1 := eventually_ge_atTop N_24
    have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
    have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ ⌊(Real.log n) ^ (R + 2)⌋₊ := by
      filter_upwards [h2] with n hn
      exact Nat.one_le_floor_iff.mpr (one_le_pow₀ (by linarith))
    have h4 : ∀ᶠ n : ℕ in atTop,
        ((4 / Real.pi) * (Real.log (2 * ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1) + 1) + 1) + 12) ≤
          Real.log n := by
      have hlim : Tendsto (fun u : ℝ =>
          ((4 / Real.pi) * (Real.log (2 * (u ^ (R + 2) + 1) + 1) + 1) + 12) / u) atTop (𝓝 0) := by
        have h0 : Tendsto (fun u : ℝ => Real.log (2 * (u ^ (R + 2) + 1) + 1) / u) atTop (𝓝 0) := by
          have hlog_le : ∀ᶠ u : ℝ in atTop, Real.log (2 * (u ^ (R + 2) + 1) + 1) ≤ (R + 3 : ℝ) * Real.log u := by
            filter_upwards [eventually_ge_atTop (4 : ℝ)] with u hu
            have h1 : 2 * (u ^ (R + 2) + 1) + 1 ≤ u ^ (R + 3) := by
              have hup : 4 * u ^ (R + 2) ≤ u ^ (R + 3) := by
                rw [pow_succ']; exact mul_le_mul_of_nonneg_right hu (by positivity)
              have hu1 : 1 ≤ u ^ (R + 2) := one_le_pow₀ (by linarith)
              linarith
            have h2 := Real.log_le_log (by positivity) h1
            rwa [Real.log_pow, Nat.cast_add] at h2
          have hlog_u : Tendsto (fun u : ℝ => (R + 3 : ℝ) * (Real.log u / u)) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa [Real.exp_neg] using (this.comp Real.tendsto_log_atTop).const_mul (R + 3 : ℝ)
          refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu; positivity) ?_ hlog_u
          filter_upwards [hlog_le, eventually_ge_atTop (1 : ℝ)] with u hu1 hu2
          exact div_le_div_of_nonneg_right hu1 (by linarith)
        have h1 : Tendsto (fun u : ℝ => ((4 / Real.pi) * 1 + 12) / u) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 := (h0.const_mul (4 / Real.pi)).add h1
        simpa [add_div, mul_add, mul_div_assoc] using h2
      filter_upwards [(hlim.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), h2] with n hn hlog2
      have hlog_pos : 0 < Real.log n := by linarith
      have h1 := (div_le_iff₀ hlog_pos).mp hn
      have hfl : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
      have hmon : Real.log (2 * ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1) + 1) ≤
          Real.log (2 * ((Real.log n) ^ (R + 2) + 1) + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith [mul_le_mul_of_nonneg_left hmon (by positivity : 0 ≤ 4 / Real.pi)]
    filter_upwards [h1, h2, h3, h4] with n a b c d using ⟨a, b, c, d⟩
  obtain ⟨N₀, hN₀_ev⟩ := eventually_atTop.mp h_ev
  refine ⟨max (C'_δ + 4 * Real.log 4) 1, max N₀ 16, by positivity, le_max_right _ _, ?_⟩
  intro n P a b r w W₀ hn hP_lo hP_hi hPa hab hb2P hr1 hrR hr_ar hW₀ hw_bd hw_diff hw_tv
  obtain ⟨hN24, hlog2, hH1, hlog_bd⟩ := hN₀_ev n (le_trans (le_max_left _ _) hn)
  set H : ℕ := ⌊(Real.log n) ^ (R + 2)⌋₊
  obtain ⟨Ψtilde, Btilde, cTilde, bTilde, hΨ, hB, hb0, _, hb_bd, happrox, hc_sum⟩ := lemma_2_3 H hH1
  have h_sum_split' :
      ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p ^ r)‖ ≤
      ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * Ψtilde ((n : ℝ) / (p : ℝ) ^ r)‖ +
      ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          W₀ * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) := by
    have hdiff : ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p ^ r) =
        (∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * Ψtilde ((n : ℝ) / (p : ℝ) ^ r)) +
        (∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * (((-1 : ℝ) ^ (n / p ^ r) : ℝ) - Ψtilde ((n : ℝ) / (p : ℝ) ^ r))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      push_cast; ring
    rw [hdiff]
    refine le_trans (norm_add_le _ _) (add_le_add_left ?_ _)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have hP_pos : 0 < P := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) δ) hP_lo
    have hp_mem : (p : ℝ) ∈ Set.Icc P (2 * P) :=
      ⟨le_trans hPa (le_trans (Nat.le_ceil a) (by exact_mod_cast hp_icc.1)),
       le_trans (le_trans (by exact_mod_cast hp_icc.2) (Nat.floor_le (by linarith))) hb2P⟩
    have hfl_eq : ⌊(n : ℝ) / (p : ℝ) ^ r⌋ = (n / p ^ r : ℤ) := by
      have : ((n : ℝ) / (p : ℝ) ^ r) = ((n : ℝ) / ((p ^ r : ℕ) : ℝ)) := by push_cast; rfl
      rw [this, Int.floor_div_natCast]; simp
    have h_ap := happrox ((n : ℝ) / (p : ℝ) ^ r)
    rw [hfl_eq, zpow_natCast] at h_ap
    have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hlogp_nn]
    calc |w p| * Real.log p * |(-1 : ℝ) ^ (n / p ^ r) - Ψtilde ((n : ℝ) / (p : ℝ) ^ r)|
        ≤ W₀ * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hw_bd p hp_mem) hlogp_nn) h_ap
            (abs_nonneg _) (mul_nonneg hW₀ hlogp_nn)
  have h24_apply : ∀ (k : ℤ), k ≠ 0 → |k| ≤ 2 * (H : ℤ) + 1 →
      ∀ (w' : ℝ → ℝ) (W₀' : ℝ), 0 ≤ W₀' → (∀ t ∈ Set.Icc P (2 * P), |w' t| ≤ W₀') →
      ContDiffOn ℝ 1 w' (Set.Icc P (2 * P)) → (∫ t in P..(2 * P), |deriv w' t|) ≤ W₀' →
      ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w' p * Real.log p : ℂ) * ePhase ((k : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
        C'_δ * W₀' * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by
    intro k hk0 hk_bd w' W₀' hW₀' hw'_bd hw'_diff hw'_tv
    let h_fn : ℕ → ℤ := fun s => if s = r then k else 0
    have hA_sub : ({r} : Finset ℕ) ⊆ Finset.Icc 1 R := Finset.singleton_subset_iff.mpr (Finset.mem_Icc.mpr ⟨hr1, hrR⟩)
    have hA_ne : ({r} : Finset ℕ).Nonempty := ⟨r, Finset.mem_singleton_self r⟩
    have hnonzero : ∃ s ∈ ({r} : Finset ℕ), h_fn s ≠ 0 := ⟨r, Finset.mem_singleton_self r, by simp [h_fn, hk0]⟩
    have hh_bd : ∀ s ∈ ({r} : Finset ℕ), |h_fn s| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1 := by
      intro s hs; rw [Finset.mem_singleton.mp hs]; simp only [h_fn, ↓reduceIte]; exact_mod_cast hk_bd
    have hr0_eq : ({r} : Finset ℕ).filter (fun s => h_fn s ≠ 0) = {r} := by
      ext s; simp [h_fn, hk0]
    have hT₀_ge : (|(h_fn r : ℝ)| * n) / P ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR := by
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      have h1 : (n : ℝ) / P ^ r ≤ (|(k : ℝ)| * n) / P ^ r :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_left (Nat.cast_nonneg n) hk1) (by positivity)
      simp only [h_fn, ↓reduceIte]
      exact le_trans hr_ar h1
    have hbd := (h24 n P a b {r} h_fn w' W₀' hN24 hP_lo hP_hi hPa hab hb2P hA_sub hA_ne
      (fun s hs => by rw [Finset.mem_singleton.mp hs]; exact hr_ar) hnonzero hh_bd hW₀' hw'_bd hw'_diff hw'_tv)
    have hbd_fin := hbd (by
      have hr_min : (({r} : Finset ℕ).filter (fun s => h_fn s ≠ 0)).min' _ = r := by simp [hr0_eq]
      simpa [hr_min] using hT₀_ge)
    have hsum_eq : ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w' p * Real.log p : ℂ) * ePhase ((k : ℝ) * n / (2 * (p : ℝ) ^ r)) =
        ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w' p * Real.log p : ℂ) * ePhase (∑ s ∈ ({r} : Finset ℕ), (h_fn s : ℝ) * n / (2 * (p : ℝ) ^ s)) := by
      refine Finset.sum_congr rfl fun p _ => ?_; simp [h_fn]
    rw [hsum_eq]
    exact le_trans hbd_fin.1 hbd_fin.2
  have hΨ_bd : ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
      (w p * Real.log p : ℂ) * Ψtilde ((n : ℝ) / (p : ℝ) ^ r)‖ ≤
      ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) := by
    have hswap : ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * Ψtilde ((n : ℝ) / (p : ℝ) ^ r) =
        ∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun k => k ≠ 0 ∧ ¬ 2 ∣ k),
          cTilde k * ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) * ePhase ((k : ℝ) * n / (2 * (p : ℝ) ^ r)) := by
      simp_rw [hΨ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun p _ => ?_
      have heq : (k : ℝ) * ((n : ℝ) / (p : ℝ) ^ r) / 2 = (k : ℝ) * n / (2 * (p : ℝ) ^ r) := by ring
      rw [heq]; ring
    rw [hswap]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun k => k ≠ 0 ∧ ¬ 2 ∣ k),
          ‖cTilde k * ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (w p * Real.log p : ℂ) * ePhase ((k : ℝ) * n / (2 * (p : ℝ) ^ r))‖
        ≤ ∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun k => k ≠ 0 ∧ ¬ 2 ∣ k),
            ‖cTilde k‖ * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul]
          have hk' := Finset.mem_filter.mp hk
          have hk_icc := Finset.mem_Icc.mp hk'.1
          have hk_abs : |k| ≤ 2 * (H : ℤ) + 1 := abs_le.mpr ⟨hk_icc.1, hk_icc.2⟩
          exact mul_le_mul_of_nonneg_left (h24_apply k hk'.2.1 hk_abs w W₀ hW₀ hw_bd hw_diff hw_tv) (norm_nonneg _)
      _ = (∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun k => k ≠ 0 ∧ ¬ 2 ∣ k),
            ‖cTilde k‖) * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) := by rw [Finset.sum_mul]
      _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) :=
          mul_le_mul_of_nonneg_right hc_sum (by positivity)
  have hB_bd : ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
      W₀ * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) ≤
      W₀ * (2 / ((H : ℝ) + 1)) * (2 * Real.log 4 * P) +
      12 * W₀ * (C'_δ * 1 * P * (Real.log n) ^ (-(R + 2 : ℤ))) := by
    have hsum_C : ((∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          W₀ * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ) =
        (W₀ : ℂ) * bTilde 0 * (∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime, (Real.log p : ℂ)) +
        ∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
          (W₀ : ℂ) * bTilde k * ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
            (1 * Real.log p : ℂ) * ePhase ((k : ℝ) * n / (2 * (p : ℝ) ^ r)) := by
      push_cast
      simp_rw [hB, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        have heq : (k : ℝ) * ((n : ℝ) / (p : ℝ) ^ r) / 2 = (k : ℝ) * n / (2 * (p : ℝ) ^ r) := by ring
        rw [heq]; ring
    have hnorm_le : ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          W₀ * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) ≤
        ‖((∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          W₀ * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    rw [hsum_C] at hnorm_le
    refine le_trans hnorm_le (le_trans (norm_add_le _ _) (add_le_add ?_ ?_))
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW₀, hb0]
      have hb0_norm : ‖(2 / ((H : ℂ) + 1))‖ = 2 / ((H : ℝ) + 1) := by
        rw [show (2 / ((H : ℂ) + 1)) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hb0_norm]
      have hth_norm : ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime, (Real.log p : ℂ)‖ ≤ 2 * Real.log 4 * P := by
        have h1 : (∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime, (Real.log p : ℂ)) =
            ((∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime, Real.log p : ℝ) : ℂ) := by push_cast; rfl
        rw [h1, Complex.norm_real, Real.norm_eq_abs]
        have hnn : 0 ≤ ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime, Real.log p :=
          Finset.sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
        rw [abs_of_nonneg hnn]
        have hth : ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime, Real.log p ≤ Chebyshev.theta (2 * P) := by
          unfold Chebyshev.theta
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
          exact ⟨⟨hp.2.pos, le_trans hp.1.2 (Nat.floor_mono hb2P)⟩, hp.2⟩
        have hP_pos : 0 < P := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) δ) hP_lo
        linarith [Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ 2 * P)]
      exact mul_le_mul_of_nonneg_left hth_norm (by positivity)
    · refine le_trans (norm_sum_le _ _) ?_
      have hw1_tv : (∫ t in P..(2 * P), |deriv (fun _ : ℝ => (1 : ℝ)) t|) ≤ 1 := by simp
      have hcard_le : (((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).card : ℝ) ≤
          4 * ((H : ℝ) + 1) := by
        have h1 := Finset.card_filter_le (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)) (· ≠ 0)
        have h2 : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by rw [Int.card_Icc]; omega
        have h3 : ((4 * H + 3 : ℕ) : ℝ) ≤ 4 * ((H : ℝ) + 1) := by push_cast; linarith
        exact le_trans (by exact_mod_cast h1) (by exact_mod_cast h2 ▸ h3)
      calc ∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
            ‖(W₀ : ℂ) * bTilde k * ∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
              (1 * Real.log p : ℂ) * ePhase ((k : ℝ) * n / (2 * (p : ℝ) ^ r))‖
          ≤ ∑ k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
              W₀ * (3 / ((H : ℝ) + 1)) * (C'_δ * 1 * P * (Real.log n) ^ (-(R + 2 : ℤ))) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW₀]
            have hk' := Finset.mem_filter.mp hk
            have hk_icc := Finset.mem_Icc.mp hk'.1
            have hk_abs : |k| ≤ 2 * (H : ℤ) + 1 := abs_le.mpr ⟨hk_icc.1, hk_icc.2⟩
            have h1 := h24_apply k hk'.2 hk_abs (fun _ => 1) 1 zero_le_one (fun _ _ => by norm_num)
              contDiffOn_const hw1_tv
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hb_bd k).le hW₀) h1 (norm_nonneg _) (by positivity)
        _ = (((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).card : ℝ) *
              (W₀ * (3 / ((H : ℝ) + 1)) * (C'_δ * 1 * P * (Real.log n) ^ (-(R + 2 : ℤ)))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (4 * ((H : ℝ) + 1)) * (W₀ * (3 / ((H : ℝ) + 1)) * (C'_δ * 1 * P * (Real.log n) ^ (-(R + 2 : ℤ)))) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = 12 * W₀ * (C'_δ * 1 * P * (Real.log n) ^ (-(R + 2 : ℤ))) := by
            field_simp [(by positivity : (H : ℝ) + 1 ≠ 0)]; ring
  have hH_inv : (1 : ℝ) / ((H : ℝ) + 1) ≤ (Real.log n) ^ (-(R + 2 : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact one_div_le_one_div_of_le (by positivity) (Nat.lt_floor_add_one _).le
  have hP_pos : 0 < P := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) δ) hP_lo
  have h_pow_split : (Real.log n) ^ (-(R + 2 : ℤ)) * Real.log n = (Real.log n) ^ (-(R + 1 : ℤ)) := by
    rw [← zpow_one (Real.log n), ← zpow_add₀ (by linarith : Real.log n ≠ 0)]; congr 1; omega
  have h_log_le_1 : (Real.log n) ^ (-(R + 2 : ℤ)) ≤ (Real.log n) ^ (-(R + 1 : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
  calc ‖∑ p ∈ (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime,
          (w p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p ^ r)‖
      ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) +
          (W₀ * (2 / ((H : ℝ) + 1)) * (2 * Real.log 4 * P) +
            12 * W₀ * (C'_δ * 1 * P * (Real.log n) ^ (-(R + 2 : ℤ)))) := le_trans h_sum_split' (add_le_add hΨ_bd hB_bd)
    _ ≤ ((4 / Real.pi) * (Real.log (2 * ((H : ℝ) + 1) + 1) + 1) + 12) *
            (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) +
          4 * Real.log 4 * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by
        have hlog_mono : Real.log (2 * (H : ℝ) + 1) ≤ Real.log (2 * ((H : ℝ) + 1) + 1) :=
          Real.log_le_log (by positivity) (by linarith)
        have h1 : W₀ * (2 / ((H : ℝ) + 1)) * (2 * Real.log 4 * P) ≤ 4 * Real.log 4 * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by
          calc W₀ * (2 / ((H : ℝ) + 1)) * (2 * Real.log 4 * P)
              = 4 * Real.log 4 * W₀ * P * (1 / ((H : ℝ) + 1)) := by ring
            _ ≤ 4 * Real.log 4 * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := mul_le_mul_of_nonneg_left hH_inv (by positivity)
        nlinarith [show 0 ≤ C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) by positivity]
    _ ≤ Real.log n * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) +
          4 * Real.log 4 * W₀ * P * (Real.log n) ^ (-(R + 1 : ℤ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_right hlog_bd (by positivity)) ?_
        exact mul_le_mul_of_nonneg_left h_log_le_1 (by positivity)
    _ = (C'_δ + 4 * Real.log 4) * W₀ * P * (Real.log n) ^ (-(R + 1 : ℤ)) := by
        rw [show Real.log n * (C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ))) =
            C'_δ * W₀ * P * ((Real.log n) ^ (-(R + 2 : ℤ)) * Real.log n) by ring, h_pow_split]; ring
    _ ≤ max (C'_δ + 4 * Real.log 4) 1 * W₀ * P * (Real.log n) ^ (-(R + 1 : ℤ)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hW₀) hP_pos.le) (by positivity)

theorem theorem_2_5_i :
    IsBigOAtTop
      (fun n => DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ))
      (fun n => (n : ℝ) / Real.log n) := by
  obtain ⟨c₁, C_pnt, hc₁, hC_pnt, hpnt⟩ := deLaValleePoussin_pnt
  obtain ⟨C_v, N_v, hC_v, hN_v, hv_bd⟩ := single_r_vaaler_bound_i (1 / 3) (by norm_num) (le_refl _)
  have hR_eq : ⌊(1 : ℝ) / (1 / 3)⌋₊ = 3 := by norm_num
  have hAR_eq : 6 * ⌊(1 : ℝ) / (1 / 3)⌋₊ + 30 = 48 := by norm_num
  have h_ev : ∀ᶠ n : ℕ in atTop,
      N_v ≤ n ∧ 16 ≤ n ∧ 2 ≤ Real.log n ∧
      (n : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 ∧
      ((Nat.sqrt n : ℝ) + 1) ≤ (n : ℝ) / (Real.log n) ^ 50 ∧
      2 ≤ (n : ℝ) / ((Real.log n) ^ 48 + 2) ∧
      C_pnt * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)))) ≤
        (Real.log n) ^ (-(98 : ℤ)) ∧
      (Real.sqrt n : ℝ) ≤ (n : ℝ) / Real.log n := by
    have h1 := (eventually_ge_atTop N_v).and (eventually_ge_atTop 16)
    have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
    have h3 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
      have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / 6 : ℝ)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp tendsto_natCast_atTop_atTop
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n _ hn1
      have hle : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
      have hsqrt : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
        rw [← Real.sqrt_eq_rpow]
        exact (Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast (by simpa [sq] using Nat.lt_succ_sqrt n))).le
      exact le_trans hle hsqrt
    have h4 : ∀ᶠ n : ℕ in atTop, ((Nat.sqrt n : ℝ) + 1) ≤ (n : ℝ) / (Real.log n) ^ 50 := by
      have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 200 : ℝ)) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)))
        refine (this.const_mul 200).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
      have h50 := (hs.pow 50).mul (tendsto_const_nhds.add (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)))
      have hlim : Tendsto (fun n : ℕ => ((Real.log n) ^ 50 * (Real.sqrt n + 1)) / (n : ℝ)) atTop (𝓝 0) := by
        refine (h50.comp tendsto_natCast_atTop_atTop).congr' ?_
        filter_upwards [eventually_ge_atTop 2] with n hn2
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        dsimp only [Function.comp_def]
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 200 : ℝ)), ← Real.rpow_mul hn_pos.le,
          Real.rpow_neg hn_pos.le, Real.sqrt_eq_rpow]
        have h1 : (1 / 200 : ℝ) * (50 : ℕ) = 1 / 4 := by norm_num
        rw [h1]
        have h1_eq : (n : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]; norm_num
        field_simp; rw [h1_eq]; ring
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop 2] with n hn hn2
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hsqrt_le : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
        Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
      have h1 := (div_le_iff₀ hn_pos).mp hn
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) 50]
    have h5 : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) / ((Real.log n) ^ 48 + 2) := by
      have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 96 : ℝ)) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 96)))
        refine (this.const_mul 96).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
      have hlim : Tendsto (fun n : ℕ => ((Real.log n) ^ 48 + 2) / (n : ℝ)) atTop (𝓝 0) := by
        have h48 : Tendsto (fun x : ℝ => (Real.log x) ^ 48 / x) atTop (𝓝 0) := by
          refine ((hs.pow 48).mul (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 96 : ℝ)), ← Real.rpow_mul hx.le, Real.rpow_neg hx.le]
          have h1 : (1 / 96 : ℝ) * (48 : ℕ) = 1 / 2 := by norm_num
          rw [h1]; field_simp; rw [← Real.rpow_add hx]; norm_num
        simpa [add_div] using ((h48.add (tendsto_const_nhds.div_atTop tendsto_id)).comp tendsto_natCast_atTop_atTop)
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop 2] with n hn hn2
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [le_div_iff₀ (by positivity)]
      linarith [(div_le_iff₀ hn_pos).mp hn]
    have h6 : ∀ᶠ n : ℕ in atTop,
        C_pnt * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)))) ≤
          (Real.log n) ^ (-(98 : ℤ)) := by
      have h_log_ge : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)) := by
        have ha : ∀ᶠ n : ℕ in atTop, ((Real.log n) ^ 48 + 2) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
          have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 96 : ℝ)) atTop (𝓝 0) := by
            have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
              ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 96)))
            refine (this.const_mul 96).congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
            dsimp only [Function.comp_def]
            rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
          have h0 : Tendsto (fun x : ℝ => ((Real.log x) ^ 48 + 2) / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
            have h48 := (hs.pow 48).congr' (by
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
              rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 96 : ℝ)), ← Real.rpow_mul hx.le]; norm_num)
            simpa [add_div] using h48.add (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)))
          filter_upwards [(h0.comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
            eventually_ge_atTop 1] with n hn hn1
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
          exact (div_le_one (Real.rpow_pos_of_pos hn_pos _)).mp hn
        filter_upwards [ha, eventually_ge_atTop 2] with n hna hn2
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        rw [Real.log_div hn_pos.ne' (by positivity)]
        have hle := Real.log_le_log (by positivity) hna
        rw [Real.log_rpow hn_pos] at hle; linarith
      have hexp_lim : Tendsto (fun u : ℝ => C_pnt * u ^ 98 * Real.exp (-(c₁ / Real.sqrt 2) * Real.sqrt u)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun y : ℝ => y ^ 196 * Real.exp (-(c₁ / Real.sqrt 2) * y)) atTop (𝓝 0) := by
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 196
          have hmul := (this.comp (tendsto_id.const_mul (c₁ / Real.sqrt 2))).const_mul ((c₁ / Real.sqrt 2) ^ (-196 : ℤ))
          simp only [mul_zero] at hmul
          refine hmul.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with y _
          dsimp only [Function.comp_def, id_eq]
          rw [mul_pow, ← mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero 196 (by positivity)), one_mul]
        refine ((h0.comp Real.tendsto_sqrt_atTop).const_mul C_pnt).congr' ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
        dsimp only [Function.comp_def]
        rw [show (196 : ℕ) = 2 * 98 by norm_num, pow_mul, Real.sq_sqrt hu]; ring
      filter_upwards [h_log_ge, (hexp_lim.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 3] with n hlg hlim hn3
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hsqrt_le : Real.sqrt ((1 / 2 : ℝ) * Real.log n) ≤
          Real.sqrt (Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2))) := Real.sqrt_le_sqrt hlg
      have hsqrt_eq : Real.sqrt ((1 / 2 : ℝ) * Real.log n) = Real.sqrt (Real.log n) / Real.sqrt 2 := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_div' _ (by norm_num), Real.sqrt_one]; ring
      have hexp_le : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)))) ≤
          Real.exp (-(c₁ / Real.sqrt 2) * Real.sqrt (Real.log n)) := by
        apply Real.exp_le_exp.mpr; rw [hsqrt_eq] at hsqrt_le; nlinarith
      have h1 : C_pnt * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)))) * (Real.log n) ^ 98 ≤ 1 :=
        le_trans (by nlinarith [pow_nonneg hlog_pos.le 98]) hlim
      rw [zpow_neg, zpow_natCast, ← one_div, le_div_iff₀ (pow_pos hlog_pos 98)]
      linarith
    have h7 : ∀ᶠ n : ℕ in atTop, (Real.sqrt n : ℝ) ≤ (n : ℝ) / Real.log n := by
      have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)))
        refine (this.const_mul 2).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
      filter_upwards [(hs.comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        eventually_ge_atTop 2] with n hn hn2
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      rw [Real.sqrt_eq_rpow, le_div_iff₀ hlog_pos]
      have h1 := (div_le_one (Real.rpow_pos_of_pos hn_pos (1 / 2))).mp hn
      calc (n : ℝ) ^ (1 / 2 : ℝ) * Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hn_pos.le _)
        _ = (n : ℝ) := by rw [← Real.rpow_add hn_pos]; norm_num
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with n ⟨a1, a2⟩ b c d e f g using
      ⟨a1, a2, b, c, d, e, f, g⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp h_ev
  obtain ⟨C_ed, _, h_ed⟩ := lemma_2_2_ii.2
  obtain ⟨N_ed, hN_ed⟩ := eventually_atTop.mp h_ed
  let C_tot : ℝ := C_ed + 8 * C_v + 4 * Real.log 4 + 12
  refine ⟨C_tot, by positivity, ?_⟩
  rw [eventually_atTop]
  refine ⟨max N₁ N_ed, fun n hn => ?_⟩
  obtain ⟨hNv, hn16, hlog2, hn13_le, hsqrt_le_nlog, hn_div_2, hexp_bd, hsqrt_nlog⟩ :=
    hN₁ n (le_trans (le_max_left _ _) hn)
  have hed_n := hN_ed n (le_trans (le_max_right _ _) hn)
  have hn4 : 4 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := by linarith
  have hDelta_eq : DeltaParity n =
      (∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p) +
      (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) n).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p) := by
    rw [DeltaParity_eq_sum]
    have hsplit : Finset.Icc 3 n = Finset.Icc 3 (Nat.sqrt n) ∪ Finset.Icc (Nat.sqrt n + 1) n := by
      ext p; simp only [Finset.mem_union, Finset.mem_Icc]
      have hsq : 3 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
      omega
    have hdisj : Disjoint ((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime)
        ((Finset.Icc (Nat.sqrt n + 1) n).filter Nat.Prime) := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2; omega
    rw [hsplit, Finset.filter_union, Finset.sum_union hdisj]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_filter.mp hp
    have hp_icc := Finset.mem_Icc.mp hp'.1
    have hnsq : n < p ^ 2 := by
      have : Nat.sqrt n < p := by omega
      have := Nat.lt_succ_sqrt n
      nlinarith [Nat.sqrt_le n]
    rw [padicValNat_factorial_of_lt_sq hp'.2 hnsq]
  have hpart1 := (lemma_2_2_ii.1 n hn4).1
  rw [hpart1] at hDelta_eq
  set J : ℕ := ⌊(Real.log n) ^ 48⌋₊
  have hJ_pos : 1 ≤ J := Nat.one_le_floor_iff.mpr (one_le_pow₀ (by linarith))
  set M_cut : ℕ := n / (J + 1)
  have hM_cut_ge : Nat.sqrt n + 1 ≤ M_cut := by
    have h1 : ((Nat.sqrt n : ℝ) + 1) * ((J : ℝ) + 1) ≤ (n : ℝ) := by
      have hJ_le : (J : ℝ) ≤ (Real.log n) ^ 48 := Nat.floor_le (by positivity)
      have hJ1_le : (J : ℝ) + 1 ≤ (Real.log n) ^ 50 := by
        have h48_50 : (Real.log n) ^ 48 ≤ (Real.log n) ^ 50 := pow_le_pow_right₀ (by linarith) (by omega)
        have h1_48 : (1 : ℝ) ≤ (Real.log n) ^ 48 := one_le_pow₀ (by linarith)
        have h2_50 : 2 * (Real.log n) ^ 48 ≤ (Real.log n) ^ 50 := by
          rw [show (50 : ℕ) = 48 + 2 by norm_num, pow_add]
          nlinarith [show (4 : ℝ) ≤ (Real.log n) ^ 2 by nlinarith]
        linarith
      rw [le_div_iff₀ (by positivity)] at hsqrt_le_nlog
      exact le_trans (mul_le_mul_of_nonneg_left hJ1_le (by positivity)) hsqrt_le_nlog
    have h1N : (Nat.sqrt n + 1) * (J + 1) ≤ n := by exact_mod_cast h1
    exact (Nat.le_div_iff_mul_le (by omega)).mpr h1N
  have hM_cut_le_n : M_cut ≤ n := Nat.div_le_self n (J + 1)
  have hsplit2 :
      ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) n).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p =
      (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p) +
      (∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p) := by
    have hu : Finset.Icc (Nat.sqrt n + 1) n = Finset.Icc (Nat.sqrt n + 1) M_cut ∪ Finset.Icc (M_cut + 1) n := by
      ext p; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint ((Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime)
        ((Finset.Icc (M_cut + 1) n).filter Nat.Prime) := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2; omega
    rw [hu, Finset.filter_union, Finset.sum_union hdisj]
  have hmid_bd :
      |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p| ≤
      (4 * C_v + 2 * Real.log 4) * ((n : ℝ) / Real.log n) := by
    have hfrac_err :
        |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * (((n / p : ℕ) : ℝ) - (n : ℝ) / p) * Real.log p| ≤
        2 * Real.log 4 * (n : ℝ) / Real.log n := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hle1 : ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            |(-1 : ℝ) ^ (n / p) * (((n / p : ℕ) : ℝ) - (n : ℝ) / p) * Real.log p| ≤
          ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime, Real.log p := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_prime := (Finset.mem_filter.mp hp).2
        have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hlog_nn]
        have hfl_eq : ((n / p : ℕ) : ℝ) = (⌊(n : ℝ) / p⌋ : ℝ) := by
          have := Int.floor_div_natCast (n : ℤ) p
          simp at this; exact_mod_cast this.symm
        rw [hfl_eq]
        have h1 : |((⌊(n : ℝ) / p⌋ : ℝ) - (n : ℝ) / p)| ≤ 1 := by
          rw [abs_sub_comm, abs_of_nonneg (Int.fract_nonneg _)]
          exact (Int.fract_lt_one _).le
        exact mul_le_of_le_one_left hlog_nn h1
      have hth : ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime, Real.log p ≤ Chebyshev.theta (M_cut : ℝ) := by
        unfold Chebyshev.theta
        rw [Nat.floor_natCast]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
          Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
        intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢; exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩
      have hM_le : (M_cut : ℝ) ≤ (n : ℝ) / Real.log n := by
        have h1 : (M_cut : ℝ) ≤ (n : ℝ) / ((J : ℝ) + 1) := by
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast Nat.div_mul_le_self n (J + 1)
        have hJ_ge : Real.log n ≤ (J : ℝ) + 1 := by
          have : (Real.log n) ^ 48 < (J : ℝ) + 1 := Nat.lt_floor_add_one _
          have h48 : Real.log n ≤ (Real.log n) ^ 48 := le_self_pow₀ (by linarith) (by norm_num)
          linarith
        exact le_trans h1 (div_le_div_of_nonneg_left hn_pos.le hlog_pos hJ_ge)
      have hth_bd := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M_cut)
      nlinarith [Real.log_two_gt_d9]
    have hmain_mid :
        |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n : ℝ) / p) * Real.log p| ≤
        4 * C_v * ((n : ℝ) / Real.log n) := by
      have h_eqC : |(∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * ((n : ℝ) / p) * Real.log p)| =
          ‖∑ p ∈ Finset.Icc (Nat.sqrt n + 1) M_cut,
            if p.Prime then (((n : ℝ) / p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p)) else 0‖ := by
        rw [← Finset.sum_filter]
        have h1 : (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (((n : ℝ) / p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p))) =
            ((∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
              (-1 : ℝ) ^ (n / p) * ((n : ℝ) / p) * Real.log p : ℝ) : ℂ) := by
          push_cast; refine Finset.sum_congr rfl fun p _ => by ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs]
      rw [h_eqC, dyadic_Icc_partition (by omega) hM_cut_ge]
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ k ∈ (Finset.range (Nat.log 2 M_cut + 1)).filter (fun k => (Nat.sqrt n + 1) * 2 ^ k ≤ M_cut),
          ‖∑ p ∈ Finset.Icc ((Nat.sqrt n + 1) * 2 ^ k) (min M_cut (2 * ((Nat.sqrt n + 1) * 2 ^ k) - 1)),
            if p.Prime then (((n : ℝ) / p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p)) else 0‖ ≤
          C_v * (n : ℝ) * (Real.log n) ^ (-(4 : ℤ)) := by
        intro k hk
        have hk_le := (Finset.mem_filter.mp hk).2
        set P_k : ℕ := (Nat.sqrt n + 1) * 2 ^ k
        set b_k : ℕ := min M_cut (2 * P_k - 1)
        have hP_pos : (0 : ℝ) < P_k := by exact_mod_cast (by positivity : 0 < P_k)
        have hP_lo : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (P_k : ℝ) :=
          le_trans hn13_le (by exact_mod_cast Nat.le_mul_of_pos_right (Nat.sqrt n + 1) (pow_pos (by norm_num) k))
        have hM_le_48 : (M_cut : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 48 := by
          have h1 : (M_cut : ℝ) ≤ (n : ℝ) / ((J : ℝ) + 1) := by
            rw [le_div_iff₀ (by positivity)]; exact_mod_cast Nat.div_mul_le_self n (J + 1)
          have h2 : (Real.log n) ^ 48 ≤ (J : ℝ) + 1 := (Nat.lt_floor_add_one _).le
          exact le_trans h1 (div_le_div_of_nonneg_left hn_pos.le (by positivity) h2)
        have hP_hi : (P_k : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 12 := by
          have h1 : (P_k : ℝ) ≤ M_cut := by exact_mod_cast hk_le
          have h2 : (Real.log n) ^ 12 ≤ (Real.log n) ^ 48 := pow_le_pow_right₀ (by linarith) (by omega)
          exact le_trans h1 (le_trans hM_le_48 (div_le_div_of_nonneg_left hn_pos.le (by positivity) h2))
        have hb_ge : (P_k : ℝ) ≤ (b_k : ℝ) := by exact_mod_cast le_min hk_le (by omega : P_k ≤ 2 * P_k - 1)
        have hb_le : (b_k : ℝ) ≤ 2 * (P_k : ℝ) := by exact_mod_cast le_trans (min_le_right _ _) (by omega : 2 * P_k - 1 ≤ 2 * P_k)
        have har : (n : ℝ) / (P_k : ℝ) ^ 1 ≥ (2 : ℝ) ^ (-(⌊(1 : ℝ) / (1 / 3)⌋₊ : ℤ)) * (Real.log n) ^ (6 * ⌊(1 : ℝ) / (1 / 3)⌋₊ + 30) := by
          rw [pow_one, hR_eq, hAR_eq]
          have h1 : (Real.log n) ^ 48 ≤ (n : ℝ) / (P_k : ℝ) := by
            rw [le_div_iff₀ hP_pos]
            have h2 : (P_k : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 48 := le_trans (by exact_mod_cast hk_le) hM_le_48
            rw [le_div_iff₀ (by positivity)] at h2; exact h2
          calc (2 : ℝ) ^ (-(3 : ℤ)) * (Real.log n) ^ 48 ≤ 1 * (Real.log n) ^ 48 := by
                refine mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = (Real.log n) ^ 48 := one_mul _
            _ ≤ (n : ℝ) / (P_k : ℝ) := h1
        obtain ⟨hW0, hw_bd, hw_diff, hw_tv⟩ := w_inv_bound_and_tv n hP_pos
        have hbd := hv_bd n (P_k : ℝ) (P_k : ℝ) (b_k : ℝ) 1 (fun t => (n : ℝ) / t) ((n : ℝ) / P_k)
          hNv hP_lo hP_hi le_rfl hb_ge hb_le (le_refl 1) (by rw [hR_eq]; omega) har hW0 hw_bd hw_diff hw_tv
        rw [Nat.ceil_natCast, Nat.floor_natCast, Finset.sum_filter, hR_eq] at hbd
        have heq_mul : C_v * ((n : ℝ) / P_k) * P_k * (Real.log n) ^ (-(3 + 1 : ℤ)) =
            C_v * (n : ℝ) * (Real.log n) ^ (-(4 : ℤ)) := by field_simp [hP_pos.ne']
        rwa [heq_mul] at hbd
      have hcard_le : (((Finset.range (Nat.log 2 M_cut + 1)).filter (fun k => (Nat.sqrt n + 1) * 2 ^ k ≤ M_cut)).card : ℝ) ≤
          4 * (Real.log n) ^ 3 := by
        have h1 := Finset.card_filter_le (Finset.range (Nat.log 2 M_cut + 1)) (fun k => (Nat.sqrt n + 1) * 2 ^ k ≤ M_cut)
        rw [Finset.card_range] at h1
        have h2 : (Nat.log 2 M_cut : ℝ) ≤ 2 * Real.log n := by
          have hpow : (2 : ℝ) ^ Nat.log 2 M_cut ≤ M_cut := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
          have hlog := Real.log_le_log (by positivity) (le_trans hpow (by exact_mod_cast hM_cut_le_n))
          rw [Real.log_pow] at hlog
          have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          nlinarith
        have h3 : ((Nat.log 2 M_cut + 1 : ℕ) : ℝ) ≤ 4 * (Real.log n) ^ 3 := by
          push_cast; have hlog3 : 4 ≤ (Real.log n) ^ 2 := by nlinarith
          nlinarith [pow_nonneg hlog_pos.le 3]
        exact le_trans (by exact_mod_cast h1) h3
      calc ∑ k ∈ (Finset.range (Nat.log 2 M_cut + 1)).filter (fun k => (Nat.sqrt n + 1) * 2 ^ k ≤ M_cut),
            ‖∑ p ∈ Finset.Icc ((Nat.sqrt n + 1) * 2 ^ k) (min M_cut (2 * ((Nat.sqrt n + 1) * 2 ^ k) - 1)),
              if p.Prime then (((n : ℝ) / p * Real.log p : ℂ) * (-1 : ℝ) ^ (n / p)) else 0‖
          ≤ ∑ _k ∈ (Finset.range (Nat.log 2 M_cut + 1)).filter (fun k => (Nat.sqrt n + 1) * 2 ^ k ≤ M_cut),
              C_v * (n : ℝ) * (Real.log n) ^ (-(4 : ℤ)) := Finset.sum_le_sum hterm
        _ = (((Finset.range (Nat.log 2 M_cut + 1)).filter (fun k => (Nat.sqrt n + 1) * 2 ^ k ≤ M_cut)).card : ℝ) *
              (C_v * (n : ℝ) * (Real.log n) ^ (-(4 : ℤ))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (4 * (Real.log n) ^ 3) * (C_v * (n : ℝ) * (Real.log n) ^ (-(4 : ℤ))) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = 4 * C_v * ((n : ℝ) / Real.log n) := by
            rw [zpow_neg, zpow_natCast]; field_simp [hlog_pos.ne']; ring
    have heq_sum :
        ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p =
        (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n : ℝ) / p) * Real.log p) +
        (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * (((n / p : ℕ) : ℝ) - (n : ℝ) / p) * Real.log p) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [heq_sum]
    calc |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * ((n : ℝ) / p) * Real.log p +
          ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * (((n / p : ℕ) : ℝ) - (n : ℝ) / p) * Real.log p|
        ≤ |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * ((n : ℝ) / p) * Real.log p| +
          |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * (((n / p : ℕ) : ℝ) - (n : ℝ) / p) * Real.log p| := abs_add_le _ _
      _ ≤ 4 * C_v * ((n : ℝ) / Real.log n) + 2 * Real.log 4 * (n : ℝ) / Real.log n := add_le_add hmain_mid hfrac_err
      _ ≤ (4 * C_v + 2 * Real.log 4) * ((n : ℝ) / Real.log n) := by ring_nf; le_rfl
  have htop_bd :
      |(∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p) - (Real.log 2 - 1) * (n : ℝ)| ≤
      6 * ((n : ℝ) / Real.log n) := by
    have h_part :
        ∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p =
        ∑ j ∈ Finset.Icc 1 J,
          (-1 : ℝ) ^ j * (j : ℝ) * (Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) := by
      have hdisj : Set.PairwiseDisjoint ↑(Finset.Icc 1 J)
          (fun j => (Finset.Icc (⌊(n : ℝ) / (j + 1)⌋₊ + 1) ⌊(n : ℝ) / j⌋₊).filter Nat.Prime) := by
        intro j₁ _ j₂ _ hne
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
        have hj1 : n / p = j₁ := by
          have hlo : (n : ℝ) / (j₁ + 1) < p := lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hp1.1.1)
          have hhi : (p : ℝ) ≤ (n : ℝ) / j₁ := le_trans (by exact_mod_cast hp1.1.2) (Nat.floor_le (by positivity))
          exact Nat.div_eq_of_lt_le
            (by exact_mod_cast (le_div_iff₀ (by positivity : (0 : ℝ) < j₁)).mp hhi |>.trans_eq (mul_comm _ _))
            (by exact_mod_cast (div_lt_iff₀ (by positivity : (0 : ℝ) < j₁ + 1)).mp hlo |>.trans_eq (mul_comm _ _))
        have hj2 : n / p = j₂ := by
          have hlo : (n : ℝ) / (j₂ + 1) < p := lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hp2.1.1)
          have hhi : (p : ℝ) ≤ (n : ℝ) / j₂ := le_trans (by exact_mod_cast hp2.1.2) (Nat.floor_le (by positivity))
          exact Nat.div_eq_of_lt_le
            (by exact_mod_cast (le_div_iff₀ (by positivity : (0 : ℝ) < j₂)).mp hhi |>.trans_eq (mul_comm _ _))
            (by exact_mod_cast (div_lt_iff₀ (by positivity : (0 : ℝ) < j₂ + 1)).mp hlo |>.trans_eq (mul_comm _ _))
        exact hne (hj1.symm.trans hj2)
      have hunion : (Finset.Icc 1 J).biUnion (fun j => (Finset.Icc (⌊(n : ℝ) / (j + 1)⌋₊ + 1) ⌊(n : ℝ) / j⌋₊).filter Nat.Prime) =
          (Finset.Icc (M_cut + 1) n).filter Nat.Prime := by
        ext p
        simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
        constructor
        · rintro ⟨j, hj, ⟨hp1, hp2⟩, hp⟩
          have hfl_m : M_cut = ⌊(n : ℝ) / (J + 1)⌋₊ := by
            have : (n : ℝ) / ((J : ℝ) + 1) = (n : ℝ) / ((J + 1 : ℕ) : ℝ) := by push_cast; rfl
            rw [this, Nat.floor_div_eq_div]; rfl
          have h1 : M_cut ≤ ⌊(n : ℝ) / (j + 1)⌋₊ := by
            rw [hfl_m]; exact Nat.floor_mono (div_le_div_of_nonneg_left hn_pos.le (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ J + 1)))
          have h2 : ⌊(n : ℝ) / j⌋₊ ≤ n := by
            rw [← Nat.floor_natCast (n := n) (α := ℝ)]
            exact Nat.floor_mono (div_le_self hn_pos.le (by exact_mod_cast hj.1))
          exact ⟨⟨by omega, by omega⟩, hp⟩
        · rintro ⟨⟨hp1, hp2⟩, hp⟩
          refine ⟨n / p, ⟨Nat.div_pos hp2 hp.pos, ?_⟩, ⟨?_, ?_⟩, hp⟩
          · have : n < (J + 1) * p := by have hdiv := Nat.lt_div_mul_add (by omega : 0 < J + 1) (a := n); nlinarith
            exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by linarith))
          · have hlt : n < (n / p + 1) * p := by nlinarith [Nat.div_add_mod n p, Nat.mod_lt n hp.pos]
            have hltR : (n : ℝ) / ((n / p : ℝ) + 1) < p := by
              rw [div_lt_iff₀ (by positivity)]; exact_mod_cast (by linarith : n < p * (n / p + 1))
            exact Nat.succ_le_of_lt (Nat.floor_lt (by positivity) |>.mpr hltR)
          · refine Nat.le_floor ?_
            rw [le_div_iff₀ (by exact_mod_cast Nat.div_pos hp2 hp.pos)]
            exact_mod_cast (by rw [mul_comm]; exact Nat.div_mul_le_self n p)
      rw [← hunion, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj1 := (Finset.mem_Icc.mp hj).1
      have h_eq : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (j + 1)⌋₊ + 1) ⌊(n : ℝ) / j⌋₊).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p =
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (j + 1)⌋₊ + 1) ⌊(n : ℝ) / j⌋₊).filter Nat.Prime,
            (-1 : ℝ) ^ j * (j : ℝ) * Real.log p := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp' := Finset.mem_filter.mp hp
        have hp_icc := Finset.mem_Icc.mp hp'.1
        have hlo : (n : ℝ) / (j + 1) < p := lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hp_icc.1)
        have hhi : (p : ℝ) ≤ (n : ℝ) / j := le_trans (by exact_mod_cast hp_icc.2) (Nat.floor_le (by positivity))
        have hjp : n / p = j := Nat.div_eq_of_lt_le
          (by exact_mod_cast (le_div_iff₀ (by positivity : (0 : ℝ) < j)).mp hhi |>.trans_eq (mul_comm _ _))
          (by exact_mod_cast (div_lt_iff₀ (by positivity : (0 : ℝ) < j + 1)).mp hlo |>.trans_eq (mul_comm _ _))
        rw [hjp]
      rw [h_eq, ← Finset.mul_sum, sum_Icc_log_eq_theta_sub (by positivity)
        (div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith))]
    rw [h_part]
    have h_pnt_err :
        |∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j * (j : ℝ) *
            ((Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
              ((n : ℝ) / j - (n : ℝ) / (j + 1)))| ≤
        2 * ((n : ℝ) / Real.log n) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ j ∈ Finset.Icc 1 J,
          |(-1 : ℝ) ^ j * (j : ℝ) *
            ((Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
              ((n : ℝ) / j - (n : ℝ) / (j + 1)))| ≤
          2 * (n : ℝ) * (Real.log n) ^ (-(98 : ℤ)) := by
        intro j hj
        have hj1 := (Finset.mem_Icc.mp hj).1
        have hjJ := (Finset.mem_Icc.mp hj).2
        have hJ_le : (J : ℝ) ≤ (Real.log n) ^ 48 := Nat.floor_le (by positivity)
        have hj1_le : (j : ℝ) + 1 ≤ (Real.log n) ^ 48 + 2 := by
          have : (j : ℝ) ≤ J := by exact_mod_cast hjJ
          linarith
        have h_x2_lo : 2 ≤ (n : ℝ) / (j + 1) :=
          le_trans hn_div_2 (div_le_div_of_nonneg_left hn_pos.le (by positivity) hj1_le)
        have h_x1_lo : 2 ≤ (n : ℝ) / j :=
          le_trans h_x2_lo (div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith))
        have h1 := (hpnt ((n : ℝ) / j) h_x1_lo).1
        have h2 := (hpnt ((n : ℝ) / (j + 1)) h_x2_lo).1
        have hexp_mon : ∀ x : ℝ, (n : ℝ) / ((Real.log n) ^ 48 + 2) ≤ x →
            C_pnt * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ (Real.log n) ^ (-(98 : ℤ)) := by
          intro x hx
          have hlg : Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)) ≤ Real.log x :=
            Real.log_le_log (by linarith [hn_div_2]) hx
          have hsq := Real.sqrt_le_sqrt hlg
          have hexp : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤
              Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((Real.log n) ^ 48 + 2)))) :=
            Real.exp_le_exp.mpr (by nlinarith)
          exact le_trans (mul_le_mul_of_nonneg_left hexp hC_pnt.le) hexp_bd
        have he1 := hexp_mon ((n : ℝ) / j) (div_le_div_of_nonneg_left hn_pos.le (by positivity) (by linarith))
        have he2 := hexp_mon ((n : ℝ) / (j + 1)) (div_le_div_of_nonneg_left hn_pos.le (by positivity) hj1_le)
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg j)]
        have hsub_bd : |(Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
              ((n : ℝ) / j - (n : ℝ) / (j + 1))| ≤
            |Chebyshev.theta ((n : ℝ) / j) - (n : ℝ) / j| +
              |Chebyshev.theta ((n : ℝ) / (j + 1)) - (n : ℝ) / (j + 1)| := by
          rw [show (Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
              ((n : ℝ) / j - (n : ℝ) / (j + 1)) =
              (Chebyshev.theta ((n : ℝ) / j) - (n : ℝ) / j) -
                (Chebyshev.theta ((n : ℝ) / (j + 1)) - (n : ℝ) / (j + 1)) by ring]
          exact abs_sub _ _
        have hj_pos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
        have hb1 : |Chebyshev.theta ((n : ℝ) / j) - (n : ℝ) / j| ≤ ((n : ℝ) / j) * (Real.log n) ^ (-(98 : ℤ)) := by
          calc |Chebyshev.theta ((n : ℝ) / j) - (n : ℝ) / j|
              ≤ C_pnt * ((n : ℝ) / j) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / j))) := h1
            _ = ((n : ℝ) / j) * (C_pnt * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / j)))) := by ring
            _ ≤ ((n : ℝ) / j) * (Real.log n) ^ (-(98 : ℤ)) := mul_le_mul_of_nonneg_left he1 (by positivity)
        have hb2 : |Chebyshev.theta ((n : ℝ) / (j + 1)) - (n : ℝ) / (j + 1)| ≤
            ((n : ℝ) / j) * (Real.log n) ^ (-(98 : ℤ)) := by
          calc |Chebyshev.theta ((n : ℝ) / (j + 1)) - (n : ℝ) / (j + 1)|
              ≤ C_pnt * ((n : ℝ) / (j + 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (j + 1)))) := h2
            _ = ((n : ℝ) / (j + 1)) * (C_pnt * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (j + 1))))) := by ring
            _ ≤ ((n : ℝ) / j) * (Real.log n) ^ (-(98 : ℤ)) :=
                mul_le_mul (div_le_div_of_nonneg_left hn_pos.le hj_pos (by linarith)) he2 (by positivity) (by positivity)
        have htot : (j : ℝ) * (2 * ((n : ℝ) / j) * (Real.log n) ^ (-(98 : ℤ))) =
            2 * (n : ℝ) * (Real.log n) ^ (-(98 : ℤ)) := by field_simp [hj_pos.ne']
        nlinarith [mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hj_pos.le]
      calc ∑ j ∈ Finset.Icc 1 J, |(-1 : ℝ) ^ j * (j : ℝ) *
              ((Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
                ((n : ℝ) / j - (n : ℝ) / (j + 1)))|
          ≤ ∑ _j ∈ Finset.Icc 1 J, 2 * (n : ℝ) * (Real.log n) ^ (-(98 : ℤ)) := Finset.sum_le_sum hterm
        _ = (J : ℝ) * (2 * (n : ℝ) * (Real.log n) ^ (-(98 : ℤ))) := by
            rw [Finset.sum_const, Nat.card_Icc, add_sub_cancel_right, nsmul_eq_mul]
        _ ≤ (Real.log n) ^ 48 * (2 * (n : ℝ) * (Real.log n) ^ (-(98 : ℤ))) :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
        _ = 2 * (n : ℝ) * (Real.log n) ^ (-(50 : ℤ)) := by
            rw [← zpow_natCast (Real.log n) 48]; ring_nf; rw [← zpow_add₀ hlog_pos.ne']; norm_num
        _ ≤ 2 * ((n : ℝ) / Real.log n) := by
            rw [zpow_neg, zpow_natCast]
            have hle : (Real.log n) ^ 50 ≥ Real.log n := le_self_pow₀ (by linarith) (by norm_num)
            have hinv : ((Real.log n) ^ 50)⁻¹ ≤ (Real.log n)⁻¹ := inv_anti₀ hlog_pos hle
            rw [div_eq_mul_inv]; nlinarith
    have h_main_eq :
        ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j * (j : ℝ) * ((n : ℝ) / j - (n : ℝ) / (j + 1)) =
        (n : ℝ) * ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_pos : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      field_simp [hj_pos.ne']; ring
    have h_tail : |(n : ℝ) * ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1) * (n : ℝ)| ≤
        (n : ℝ) / Real.log n := by
      rw [show (n : ℝ) * ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1) * (n : ℝ) =
          (n : ℝ) * (∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1)) by ring,
        abs_mul, abs_of_pos hn_pos]
      have h1 := alt_harmonic_tail_bound J
      have h2 : (1 : ℝ) / ((J : ℝ) + 1) ≤ (Real.log n)⁻¹ := by
        rw [one_div]; refine inv_anti₀ hlog_pos ?_
        have hJ_ge : (Real.log n) ^ 48 < (J : ℝ) + 1 := Nat.lt_floor_add_one _
        exact le_trans (le_self_pow₀ (by linarith) (by norm_num)) hJ_ge.le
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hn_pos.le
    have h_split_top :
        (∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j * (j : ℝ) *
          (Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1)))) - (Real.log 2 - 1) * (n : ℝ) =
        (∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j * (j : ℝ) *
          ((Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
            ((n : ℝ) / j - (n : ℝ) / (j + 1)))) +
        ((n : ℝ) * ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1) * (n : ℝ)) := by
      rw [← h_main_eq, ← Finset.sum_add_distrib]
      have : ∀ j ∈ Finset.Icc 1 J,
          (-1 : ℝ) ^ j * (j : ℝ) *
            ((Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
              ((n : ℝ) / j - (n : ℝ) / (j + 1))) +
          (-1 : ℝ) ^ j * (j : ℝ) * ((n : ℝ) / j - (n : ℝ) / (j + 1)) =
          (-1 : ℝ) ^ j * (j : ℝ) * (Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) := fun j _ => by ring
      rw [Finset.sum_congr rfl this]; ring
    rw [h_split_top]
    linarith [abs_add_le
      (∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j * (j : ℝ) *
        ((Chebyshev.theta ((n : ℝ) / j) - Chebyshev.theta ((n : ℝ) / (j + 1))) -
          ((n : ℝ) / j - (n : ℝ) / (j + 1))))
      ((n : ℝ) * ∑ j ∈ Finset.Icc 1 J, (-1 : ℝ) ^ j / ((j : ℝ) + 1) - (Real.log 2 - 1) * (n : ℝ)),
      show (0 : ℝ) ≤ (n : ℝ) / Real.log n by positivity]
  have hdiff_eq :
      DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ) =
      Edigit n +
      (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p) +
      ((∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
        (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p) - (Real.log 2 - 1) * (n : ℝ)) := by
    rw [hDelta_eq, hsplit2]; ring
  rw [hdiff_eq]
  have hed_bd : |Edigit n| ≤ C_ed * ((n : ℝ) / Real.log n) := by
    have h1 : |Edigit n| ≤ C_ed * |Real.sqrt n| := hed_n
    rw [abs_of_pos (Real.sqrt_pos.mpr hn_pos)] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hsqrt_nlog (by
      have := le_trans (abs_nonneg (Edigit n)) hed_n
      nlinarith [abs_pos.mpr (Real.sqrt_pos.mpr hn_pos).ne']))
  have hnorm_rhs : |(n : ℝ) / Real.log n| = (n : ℝ) / Real.log n := abs_of_pos (div_pos hn_pos hlog_pos)
  rw [hnorm_rhs]
  calc |Edigit n +
        ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p +
        (∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p - (Real.log 2 - 1) * (n : ℝ))|
      ≤ |Edigit n| +
        |∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p| +
        |∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p - (Real.log 2 - 1) * (n : ℝ)| := by
        linarith [abs_add_le (Edigit n) (∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
          (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p),
          abs_add_le (Edigit n + ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) M_cut).filter Nat.Prime,
            (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p)
            (∑ p ∈ (Finset.Icc (M_cut + 1) n).filter Nat.Prime,
              (-1 : ℝ) ^ (n / p) * ((n / p : ℕ) : ℝ) * Real.log p - (Real.log 2 - 1) * (n : ℝ))]
    _ ≤ C_ed * ((n : ℝ) / Real.log n) + (4 * C_v + 2 * Real.log 4) * ((n : ℝ) / Real.log n) +
          6 * ((n : ℝ) / Real.log n) := add_le_add (add_le_add hed_bd hmid_bd) htop_bd
    _ ≤ C_tot * ((n : ℝ) / Real.log n) := by dsimp [C_tot]; nlinarith [div_pos hn_pos hlog_pos]

private lemma theorem_2_5_ii_part1 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    IsBigOAtTop
      (fun n => ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)))
      (fun n => (Real.log n)⁻¹) := by
  let R : ℕ := ⌊1 / δ⌋₊
  let AR : ℕ := 6 * R + 30
  have hR3 : 3 ≤ R := by
    have h3 : (3 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    exact Nat.le_floor h3
  obtain ⟨η'_δ, C_δ, C'_δ, hη'_pos, hC_δ, hC'_δ, N_i, hN_i, h24i⟩ := lemma_2_4_i δ hδ0 hδ1
  obtain ⟨η_δ, C_ii, hη_δ, hC_ii, N_ii, hN_ii, h24ii⟩ := lemma_2_4_ii δ hδ0 hδ1
  have h_ev : ∀ᶠ n : ℕ in atTop,
      N_i ≤ n ∧ N_ii ≤ n ∧ 16 ≤ n ∧ 2 ≤ Real.log n ∧
      (Real.log n) ^ AR ≤ (n : ℝ) ^ (1 / 2 : ℝ) ∧
      (Real.log n) ^ AR ≤ (n : ℝ) ^ δ ∧
      (n : ℝ) ^ (1 / 2 : ℝ) ≥ (n : ℝ) ^ (δ / 2) ∧
      (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 12 ∧
      (n : ℝ) ^ δ ≥ 2 ∧
      1 ≤ ⌊(Real.log n) ^ (R + 2)⌋₊ ∧
      (((4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2) *
        (n : ℝ) ^ (-η_δ)) ≤ (2 : ℝ) ^ (3 * R + 1) * (Real.log n)⁻¹ := by
    have h1 := (eventually_ge_atTop N_i).and ((eventually_ge_atTop N_ii).and (eventually_ge_atTop 16))
    have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
    have h3 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ AR ≤ (n : ℝ) ^ δ ∧ (Real.log n) ^ AR ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (δ / max (AR : ℝ) 1)) atTop (𝓝 0) := by
        have hpos : 0 < δ / max (AR : ℝ) 1 := by positivity
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop hpos))
        refine (this.const_mul (max (AR : ℝ) 1 / δ)).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
      have hAR_pos : 0 < AR := by omega
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ AR / (n : ℝ) ^ δ) atTop (𝓝 0) := by
        refine ((hs.pow AR).comp tendsto_natCast_atTop_atTop).congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        dsimp only [Function.comp_def]
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le]
        have heq : (δ / max (AR : ℝ) 1) * (AR : ℝ) = δ := by
          have : max (AR : ℝ) 1 = AR := max_eq_left (by exact_mod_cast hAR_pos)
          rw [this]; field_simp [(by exact_mod_cast hAR_pos.ne' : (AR : ℝ) ≠ 0)]
        rw [heq]
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h_le_d : (Real.log n) ^ AR ≤ (n : ℝ) ^ δ := (div_le_one (Real.rpow_pos_of_pos hn_pos δ)).mp hn
      have h_d_le : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
      exact ⟨h_le_d, le_trans h_le_d h_d_le⟩
    have h4 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 : ℝ) ≥ (n : ℝ) ^ (δ / 2) ∧ (n : ℝ) ^ δ ≥ 2 := by
      have ha := ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      filter_upwards [ha, eventually_ge_atTop 1] with n hna hn1
      exact ⟨Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith), hna⟩
    have h5 : ∀ᶠ n : ℕ in atTop, (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 12 := by
      have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 24 : ℝ)) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 24)))
        refine (this.const_mul 24).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ 12 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
        refine ((hs.pow 12).comp tendsto_natCast_atTop_atTop).congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        dsimp only [Function.comp_def]
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 24 : ℝ)), ← Real.rpow_mul hn_pos.le]
        have h1 : (1 / 24 : ℝ) * (12 : ℕ) = 1 / 2 := by norm_num
        rw [h1]
        have heq : (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hn_pos]; norm_num
        rw [heq]; field_simp
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 2] with n hn hn2
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hsqrt_le : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
      rw [le_div_iff₀ (by positivity)]
      have h1 := (div_le_iff₀ hn_pos).mp hn
      nlinarith [pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) 12]
    have h6 : ∀ᶠ n : ℕ in atTop,
        (((4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2) *
          (n : ℝ) ^ (-η_δ)) ≤ (2 : ℝ) ^ (3 * R + 1) * (Real.log n)⁻¹ := by
      let M_pow : ℕ := R * (R + 2) + AR + 3
      have hs : Tendsto (fun x : ℝ => Real.log x / x ^ (η_δ / M_pow)) atTop (𝓝 0) := by
        have hpos : 0 < η_δ / M_pow := by positivity
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop hpos))
        refine (this.const_mul (M_pow / η_δ)).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ M_pow * (n : ℝ) ^ (-η_δ)) atTop (𝓝 0) := by
        refine ((hs.pow M_pow).comp tendsto_natCast_atTop_atTop).congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        dsimp only [Function.comp_def]
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_neg hn_pos.le, div_eq_mul_inv]
        have heq : (η_δ / M_pow) * (M_pow : ℝ) = η_δ := by
          field_simp [(by positivity : (M_pow : ℝ) ≠ 0)]
        rw [heq]; ring
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), h2] with n hn hlog2
      have hfl : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
      have h1 : 4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3 ≤ 7 * (Real.log n) ^ (R + 2) := by
        have : 1 ≤ (Real.log n) ^ (R + 2) := one_le_pow₀ (by linarith)
        linarith
      have h2' : (Real.log n) ^ AR + 1 ≤ 2 * (Real.log n) ^ AR := by
        have : 1 ≤ (Real.log n) ^ AR := one_le_pow₀ (by linarith)
        linarith
      have h3' : (4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2 ≤
          7 ^ R * 2 * (Real.log n) ^ (M_pow - 1) := by
        have hp1 : (4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R ≤ 7 ^ R * (Real.log n) ^ (R * (R + 2)) := by
          calc (4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R ≤ (7 * (Real.log n) ^ (R + 2)) ^ R :=
                pow_le_pow_left₀ (by positivity) h1 R
            _ = 7 ^ R * (Real.log n) ^ (R * (R + 2)) := by rw [mul_pow, ← pow_mul, mul_comm (R + 2) R]
        calc (4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2
            ≤ (7 ^ R * (Real.log n) ^ (R * (R + 2))) * (2 * (Real.log n) ^ AR) * (Real.log n) ^ 2 := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul hp1 h2' (by positivity) (by positivity)) (by positivity)
          _ = 7 ^ R * 2 * (Real.log n) ^ (M_pow - 1) := by
              rw [show M_pow - 1 = R * (R + 2) + AR + 2 by dsimp [M_pow]; omega]
              rw [pow_add, pow_add]; ring
      have hpow_le : 7 ^ R * 2 ≤ (2 : ℝ) ^ (3 * R + 1) := by
        have : (7 : ℝ) ≤ 2 ^ 3 := by norm_num
        calc 7 ^ R * 2 ≤ (2 ^ 3) ^ R * 2 := by gcongr
          _ = (2 : ℝ) ^ (3 * R + 1) := by rw [← pow_mul, pow_succ]; ring
      have hlog_pos : 0 < Real.log n := by linarith
      have hn' : (Real.log n) ^ (M_pow - 1) * (n : ℝ) ^ (-η_δ) ≤ (Real.log n)⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hlog_pos, inv_eq_one_div, one_div]
        have hM_eq : (Real.log n) ^ (M_pow - 1) * Real.log n = (Real.log n) ^ M_pow := by
          rw [← pow_succ]; congr 1; omega
        calc ((Real.log n) ^ (M_pow - 1) * (n : ℝ) ^ (-η_δ))⁻¹ * 1 =
              ((Real.log n) ^ (M_pow - 1) * (n : ℝ) ^ (-η_δ))⁻¹ := mul_one _
          _ = (((Real.log n) ^ M_pow * (n : ℝ) ^ (-η_δ)) / Real.log n)⁻¹ := by
              rw [← hM_eq]; field_simp [hlog_pos.ne']
          _ = Real.log n / ((Real.log n) ^ M_pow * (n : ℝ) ^ (-η_δ)) := by rw [inv_div]
          _ ≥ Real.log n / 1 := div_le_div_of_nonneg_left hlog_pos.le (by positivity) hn
          _ = Real.log n := div_one _
      calc ((4 * (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2) * (n : ℝ) ^ (-η_δ)
          ≤ (7 ^ R * 2 * (Real.log n) ^ (M_pow - 1)) * (n : ℝ) ^ (-η_δ) :=
            mul_le_mul_of_nonneg_right h3' (by positivity)
        _ = (7 ^ R * 2) * ((Real.log n) ^ (M_pow - 1) * (n : ℝ) ^ (-η_δ)) := by ring
        _ ≤ (2 : ℝ) ^ (3 * R + 1) * (Real.log n)⁻¹ := mul_le_mul hpow_le hn' (by positivity) (by positivity)
    filter_upwards [h1, h2, h3, h4, h5, h6] with n ⟨a1, a2, a3⟩ b ⟨c1, c2⟩ ⟨d1, d2⟩ e f using
      ⟨a1, a2, a3, b, c1, c2, d1, d2, e, Nat.one_le_floor_iff.mpr (one_le_pow₀ (by linarith)), f⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
  let C_tot : ℝ := 4 * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * 2 + C_ii * (2 : ℝ) ^ (3 * R + 1) * 2) + 1
  refine ⟨C_tot, by positivity, ?_⟩
  rw [eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hNi, hNii, hn16, hlog2, hAR_sqrt, hAR_d, hsqrt_d2, hsqrt_12, hnd_2, hH1, h_decay⟩ := hN₀ n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := by linarith
  set A_lo : ℕ := ⌊(n : ℝ) ^ δ⌋₊ + 1
  set B_hi : ℕ := Nat.sqrt n
  rw [abs_of_pos (inv_pos.mpr hlog_pos)]
  by_cases hAB : B_hi < A_lo
  · have h_empty : (Finset.Icc A_lo B_hi).filter Nat.Prime = ∅ := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [h_empty, Finset.sum_empty, abs_zero]
    positivity
  · have hAB_le : A_lo ≤ B_hi := Nat.le_of_not_lt hAB
    have hA1 : 1 ≤ A_lo := by omega
    have h_eqC : |∑ p ∈ (Finset.Icc A_lo B_hi).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))| =
        ‖∑ p ∈ Finset.Icc A_lo B_hi,
          if p.Prime then (((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) * (-1 : ℝ) ^ padicValNat p n.factorial) else 0‖ := by
      have h1 : ∑ p ∈ (Finset.Icc A_lo B_hi).filter Nat.Prime,
            (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)) =
          - ∑ p ∈ (Finset.Icc A_lo B_hi).filter Nat.Prime,
            (-1 : ℝ) ^ padicValNat p n.factorial * (Real.log p / ((p : ℝ) - 1)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]; ring
      rw [h1, abs_neg, ← Finset.sum_filter]
      have h2 : (∑ p ∈ (Finset.Icc A_lo B_hi).filter Nat.Prime,
          (((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) * (-1 : ℝ) ^ padicValNat p n.factorial)) =
          ((∑ p ∈ (Finset.Icc A_lo B_hi).filter Nat.Prime,
            (-1 : ℝ) ^ padicValNat p n.factorial * (Real.log p / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
        push_cast; refine Finset.sum_congr rfl fun p _ => by ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs]
    rw [h_eqC, dyadic_Icc_partition hA1 hAB_le]
    refine le_trans (norm_sum_le _ _) ?_
    set H : ℕ := ⌊(Real.log n) ^ (R + 2)⌋₊
    obtain ⟨Ψtilde, Btilde, cTilde, bTilde, hΨ, hB, hb0_eq, hc_bd, hb_bd_all, happrox, hc_sum⟩ := lemma_2_3 H hH1
    have hBtilde_bd : ∀ x : ℝ, |Btilde x| ≤ 14 := by
      intro x
      have h1 : ‖(Btilde x : ℂ)‖ = |Btilde x| := by rw [Complex.norm_real, Real.norm_eq_abs]
      rw [← h1, hB]
      refine le_trans (norm_add_le _ _) ?_
      have hb0_n : ‖bTilde 0‖ ≤ 2 / ((H : ℝ) + 1) := by
        rw [hb0_eq, show (2 / ((H : ℂ) + 1)) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hsum_n : ‖∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
          bTilde h * ePhase ((h : ℝ) * x / 2)‖ ≤ 12 := by
        refine le_trans (norm_sum_le _ _) ?_
        have hle1 : ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
              ‖bTilde h * ePhase ((h : ℝ) * x / 2)‖ ≤
            ∑ _h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
              (3 / ((H : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun h _ => ?_
          rw [norm_mul, norm_ePhase, mul_one]; exact (hb_bd_all h).le
        have hcard : (((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).card : ℝ) ≤
            4 * ((H : ℝ) + 1) := by
          have h1' := Finset.card_filter_le (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)) (· ≠ 0)
          have h2' : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by rw [Int.card_Icc]; omega
          have h3' : ((4 * H + 3 : ℕ) : ℝ) ≤ 4 * ((H : ℝ) + 1) := by push_cast; linarith
          exact le_trans (by exact_mod_cast h1') (by exact_mod_cast h2' ▸ h3')
        calc ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
              ‖bTilde h * ePhase ((h : ℝ) * x / 2)‖
            ≤ (((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).card : ℝ) *
                (3 / ((H : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul] at hle1; exact hle1
          _ ≤ (4 * ((H : ℝ) + 1)) * (3 / ((H : ℝ) + 1)) := mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = 12 := by field_simp [(by positivity : (H : ℝ) + 1 ≠ 0)]; ring
      have hb0_2 : 2 / ((H : ℝ) + 1) ≤ 2 := div_le_self (by norm_num) (by linarith [show (1 : ℝ) ≤ H by exact_mod_cast hH1])
      linarith
    have hΨtilde_bd : ∀ x : ℝ, |Ψtilde x| ≤ 15 := by
      intro x
      have h1 := happrox x
      have h2 : |(-1 : ℝ) ^ ⌊x⌋| = 1 := by rw [abs_zpow, abs_neg, abs_one, one_zpow]
      linarith [abs_sub_abs_le_abs_sub (Ψtilde x) ((-1 : ℝ) ^ ⌊x⌋), hBtilde_bd x,
        abs_sub_comm ((-1 : ℝ) ^ ⌊x⌋) (Ψtilde x)]
    have hblock_bd : ∀ k ∈ (Finset.range (Nat.log 2 B_hi + 1)).filter (fun k => A_lo * 2 ^ k ≤ B_hi),
        ‖∑ p ∈ Finset.Icc (A_lo * 2 ^ k) (min B_hi (2 * (A_lo * 2 ^ k) - 1)),
          if p.Prime then (((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) * (-1 : ℝ) ^ padicValNat p n.factorial) else 0‖ ≤
        15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)) +
        C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ)) := by
      intro k hk
      have hk_le := (Finset.mem_filter.mp hk).2
      set P_k : ℕ := A_lo * 2 ^ k
      set b_k : ℕ := min B_hi (2 * P_k - 1)
      have hP_lo : (n : ℝ) ^ δ ≤ (P_k : ℝ) := by
        have h1 : (n : ℝ) ^ δ < A_lo := Nat.lt_floor_add_one _
        have h2 : A_lo ≤ P_k := Nat.le_mul_of_pos_right A_lo (pow_pos (by norm_num) k)
        exact le_trans h1.le (by exact_mod_cast h2)
      have hP_hi : (P_k : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 12 := le_trans (by exact_mod_cast hk_le) hsqrt_12
      have hP_pos : (0 : ℝ) < P_k := lt_of_lt_of_le (Real.rpow_pos_of_pos hn_pos δ) hP_lo
      have hP_ge2 : (2 : ℝ) ≤ P_k := le_trans hnd_2 hP_lo
      have hb_ge : (P_k : ℝ) ≤ (b_k : ℝ) := by exact_mod_cast le_min hk_le (by omega : P_k ≤ 2 * P_k - 1)
      have hb_le : (b_k : ℝ) ≤ 2 * (P_k : ℝ) := by exact_mod_cast le_trans (min_le_right _ _) (by omega : 2 * P_k - 1 ≤ 2 * P_k)
      rw [← Finset.sum_filter]
      set A_P := (Finset.Icc 1 R).filter (fun r => (P_k : ℝ) ^ r ≤ n)
      have h1_mem_AP : 1 ∈ A_P := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, ?_⟩
        rw [pow_one]
        exact le_trans (by exact_mod_cast hk_le) (by exact_mod_cast Nat.sqrt_le_self n)
      have h_vp_eq : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
          padicValNat p n.factorial = ∑ r ∈ A_P, n / p ^ r := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hp_icc := Finset.mem_Icc.mp hp'.1
        have hp_gt : n < p ^ (R + 1) := by
          have h1 : (n : ℝ) ^ δ < p := lt_of_le_of_lt hP_lo (by
            have : A_lo ≤ p := le_trans (Nat.le_mul_of_pos_right A_lo (pow_pos (by norm_num) k)) hp_icc.1
            exact lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast this))
          have h2 : (n : ℝ) < (p : ℝ) ^ (R + 1) := by
            have h1_rpow : ((n : ℝ) ^ δ) ^ (R + 1 : ℝ) < (p : ℝ) ^ (R + 1 : ℝ) :=
              Real.rpow_lt_rpow (by positivity) h1 (by positivity)
            rw [← Real.rpow_mul hn_pos.le] at h1_rpow
            have hexp : 1 < δ * (R + 1 : ℝ) := (div_lt_iff₀' hδ0).mp (Nat.lt_floor_add_one _)
            have hn1 : (n : ℝ) ≤ (n : ℝ) ^ (δ * (R + 1 : ℝ)) :=
              Real.le_rpow_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hexp.le
            rw [Real.rpow_natCast] at h1_rpow
            exact lt_of_le_of_lt hn1 h1_rpow
          exact_mod_cast h2
        rw [padicValNat_factorial_eq_sum_floor hp'.2 hp_gt]
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
        have hP_gt : (n : ℝ) < (P_k : ℝ) ^ r := by
          by_contra hle; exact hnot (Finset.mem_filter.mpr ⟨hr, not_lt.mp hle⟩)
        have hp_gt_r : n < p ^ r :=
          by exact_mod_cast lt_of_lt_of_le hP_gt (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp_icc.1) r)
        exact Nat.div_eq_of_lt hp_gt_r
      have h_pow_prod : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
          (-1 : ℝ) ^ padicValNat p n.factorial = ∏ r ∈ A_P, (-1 : ℝ) ^ (n / p ^ r) := by
        intro p hp
        rw [h_vp_eq p hp]
        induction A_P using Finset.induction_on with
        | empty => simp
        | @insert r s hr ih => rw [Finset.sum_insert hr, pow_add, Finset.prod_insert hr, ih]
      set A_big := A_P.filter (fun r => (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR ≤ (n : ℝ) / (P_k : ℝ) ^ r)
      set A_col := A_P \ A_big
      have h1_big : 1 ∈ A_big := by
        refine Finset.mem_filter.mpr ⟨h1_mem_AP, ?_⟩
        rw [pow_one]
        have h1 : (n : ℝ) / P_k ≥ (n : ℝ) ^ (1 / 2 : ℝ) := by
          have hle : (P_k : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
            have : (P_k : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hk_le
            have hsqrt_le : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
              Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
            rw [Real.sqrt_eq_rpow] at hsqrt_le; exact le_trans this hsqrt_le
          calc (n : ℝ) / P_k ≥ (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_left hn_pos.le hP_pos hle
            _ = (n : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_one (n : ℝ), ← Real.rpow_sub hn_pos]; norm_num
        calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR ≤ 1 * (Real.log n) ^ AR :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = (Real.log n) ^ AR := one_mul _
          _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hAR_sqrt
          _ ≤ (n : ℝ) / P_k := h1
      have hcol_card : A_col.card ≤ 1 := by
        by_contra hgt
        obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A_col.card)
        wlog hlt : r₁ < r₂ generalizing r₁ r₂
        · exact this r₂ hr₂ r₁ hr₁ hne.symm (by omega)
        have hr₁' := Finset.mem_sdiff.mp hr₁
        have hr₂' := Finset.mem_sdiff.mp hr₂
        have hr₁_lt : (n : ℝ) / (P_k : ℝ) ^ r₁ < (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR := by
          by_contra hge; exact hr₁'.2 (Finset.mem_filter.mpr ⟨hr₁'.1, not_lt.mp hge⟩)
        have hr₂_ge : 1 ≤ (n : ℝ) / (P_k : ℝ) ^ r₂ := by
          rw [le_div_iff₀ (by positivity), one_mul]; exact (Finset.mem_filter.mp hr₂'.1).2
        have hr_pow : (P_k : ℝ) ^ r₂ = (P_k : ℝ) ^ r₁ * (P_k : ℝ) ^ (r₂ - r₁) := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        have hP_diff : (n : ℝ) ^ δ ≤ (P_k : ℝ) ^ (r₂ - r₁) :=
          le_trans hP_lo (le_self_pow₀ (by linarith) (by omega))
        have hcontr : (n : ℝ) / (P_k : ℝ) ^ r₂ < 1 := by
          rw [hr_pow, ← div_div]
          have h1_lt : ((n : ℝ) / (P_k : ℝ) ^ r₁) / (P_k : ℝ) ^ (r₂ - r₁) <
              ((2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) / (n : ℝ) ^ δ :=
            lt_of_lt_of_le (div_lt_div_of_pos_right hr₁_lt (by positivity))
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hP_diff)
          have h2_le : ((2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR) / (n : ℝ) ^ δ ≤ 1 := by
            refine (div_le_one (Real.rpow_pos_of_pos hn_pos δ)).mpr ?_
            calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR ≤ 1 * (Real.log n) ^ AR :=
                  mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
              _ = (Real.log n) ^ AR := one_mul _
              _ ≤ (n : ℝ) ^ δ := hAR_d
          linarith
        linarith
      obtain ⟨hW0, hw_bd, hw_diff, hw_tv⟩ := w_inv_one_bound_and_tv hP_ge2
      let w1 : ℝ → ℝ := fun t => 1 / (t - 1)
      let W₀1 : ℝ := 2 / (P_k : ℝ)
      have h_approx_prod :
          ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) * (-1 : ℝ) ^ padicValNat p n.factorial‖ ≤
          ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ((w1 p * Real.log p : ℝ) : ℂ) *
                (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))‖ +
          15 ^ R * ∑ r ∈ A_big,
            ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) := by
        have h_eq1 : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) * (-1 : ℝ) ^ padicValNat p n.factorial =
            (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ((w1 p * Real.log p : ℝ) : ℂ) *
                (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))) +
            ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) *
                ((∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [h_pow_prod p hp]
          have hdisj_AB : Disjoint A_col A_big := disjoint_sdiff_self_left
          have hunion_AB : A_col ∪ A_big = A_P := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
          have hprod_split : (∏ r ∈ A_P, (-1 : ℝ) ^ (n / p ^ r)) =
              (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) * (∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) := by
            rw [← hunion_AB, Finset.prod_union hdisj_AB]
          have hw1_eq : Real.log p / ((p : ℝ) - 1) = w1 p * Real.log p := by dsimp [w1]; ring
          rw [hw1_eq, hprod_split]; push_cast; ring
        rw [h_eq1]
        refine le_trans (norm_add_le _ _) (add_le_add_left ?_ _)
        refine le_trans (norm_sum_le _ _) ?_
        have h_term : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
            ‖((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) *
              ((∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r)))‖ ≤
            15 ^ R * ∑ r ∈ A_big, w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) := by
          intro p hp
          have hp_prime := (Finset.mem_filter.mp hp).2
          have hw1_nn : 0 ≤ w1 p := by dsimp [w1]; have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le; positivity
          have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
          have hcol_abs : |∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)| = 1 := by
            rw [Finset.abs_prod]
            exact Finset.prod_eq_one fun r _ => by rw [abs_pow, abs_neg, abs_one, one_pow]
          have hprod_err := prod_sub_prod_le A_big (fun r => (-1 : ℝ) ^ (n / p ^ r))
            (fun r => Ψtilde ((n : ℝ) / (p : ℝ) ^ r))
            (fun r _ => by rw [abs_pow, abs_neg, abs_one, one_pow]) (fun r _ => hΨtilde_bd _)
          have h15_le : (15 : ℝ) ^ A_big.card ≤ 15 ^ R :=
            pow_le_pow_right₀ (by norm_num) (le_trans (Finset.card_le_card (Finset.filter_subset _ _))
              (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp [Nat.card_Icc])))
          have hsum_ap : ∑ r ∈ A_big, |(-1 : ℝ) ^ (n / p ^ r) - Ψtilde ((n : ℝ) / (p : ℝ) ^ r)| ≤
              ∑ r ∈ A_big, Btilde ((n : ℝ) / (p : ℝ) ^ r) := by
            refine Finset.sum_le_sum fun r _ => ?_
            have hfl_eq : ⌊(n : ℝ) / (p : ℝ) ^ r⌋ = (n / p ^ r : ℤ) := by
              have : ((n : ℝ) / (p : ℝ) ^ r) = ((n : ℝ) / ((p ^ r : ℕ) : ℝ)) := by push_cast; rfl
              rw [this, Int.floor_div_natCast]; simp
            have h_ap := happrox ((n : ℝ) / (p : ℝ) ^ r)
            rwa [hfl_eq, zpow_natCast] at h_ap
          have hnorm_eq : ‖((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) *
              ((∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r)))‖ =
              (w1 p * Real.log p) * |(∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))| := by
            have : ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) *
                ((∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))) =
                (((w1 p * Real.log p) * (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) *
                  ((∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))) : ℝ) : ℂ) := by
              push_cast; ring
            rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, hcol_abs, mul_one,
              abs_of_nonneg (mul_nonneg hw1_nn hlog_nn)]
          rw [hnorm_eq, Finset.mul_sum]
          calc (w1 p * Real.log p) * |(∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))|
              ≤ (w1 p * Real.log p) * (15 ^ A_big.card * ∑ r ∈ A_big, |(-1 : ℝ) ^ (n / p ^ r) - Ψtilde ((n : ℝ) / (p : ℝ) ^ r)|) :=
                mul_le_mul_of_nonneg_left hprod_err (mul_nonneg hw1_nn hlog_nn)
            _ ≤ (w1 p * Real.log p) * (15 ^ R * ∑ r ∈ A_big, Btilde ((n : ℝ) / (p : ℝ) ^ r)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h15_le hsum_ap (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity))
                  (mul_nonneg hw1_nn hlog_nn)
            _ = 15 ^ R * ∑ r ∈ A_big, w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) := by
                rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
        calc ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ‖((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) *
                ((∏ r ∈ A_big, (-1 : ℝ) ^ (n / p ^ r)) - (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r)))‖
            ≤ ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                15 ^ R * ∑ r ∈ A_big, w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) := Finset.sum_le_sum h_term
          _ = 15 ^ R * ∑ r ∈ A_big, ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) := by
              rw [← Finset.mul_sum, Finset.sum_comm]
      have hB_err_bd : 15 ^ R * ∑ r ∈ A_big,
          ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
            w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) ≤
          15 ^ R * (R : ℝ) * (12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
            (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4)) := by
        have h_single_r : ∀ r ∈ A_big,
            ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) ≤
            12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
              (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4) := by
          intro r hr
          have hr_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
          have hr_ar : (n : ℝ) / (P_k : ℝ) ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR :=
            (Finset.mem_filter.mp hr).2
          have hsum_C : ((∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ) =
              bTilde 0 * (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (w1 p * Real.log p : ℂ)) +
              ∑ k_freq ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                bTilde k_freq * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                  (w1 p * Real.log p : ℂ) * ePhase ((k_freq : ℝ) * n / (2 * (p : ℝ) ^ r)) := by
            push_cast
            simp_rw [hB, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k_freq _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              have heq : (k_freq : ℝ) * ((n : ℝ) / (p : ℝ) ^ r) / 2 = (k_freq : ℝ) * n / (2 * (p : ℝ) ^ r) := by ring
              rw [heq]; ring
          have hnorm_le : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) ≤
              ‖((∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
          rw [hsum_C] at hnorm_le
          have h_b0_bd : ‖bTilde 0 * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (w1 p * Real.log p : ℂ)‖ ≤
              (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4) := by
            rw [norm_mul, hb0_eq, show (2 / ((H : ℂ) + 1)) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            have hsum_nn : 0 ≤ ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, w1 p * Real.log p :=
              Finset.sum_nonneg fun p hp => mul_nonneg (by dsimp [w1]; have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le; positivity)
                (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
            have hsum_le : ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (w1 p * Real.log p : ℂ)‖ ≤
                W₀1 * (2 * Real.log 4 * (P_k : ℝ)) := by
              have h1 : (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (w1 p * Real.log p : ℂ)) =
                  ((∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, w1 p * Real.log p : ℝ) : ℂ) := by push_cast; rfl
              rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nn]
              calc ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, w1 p * Real.log p
                  ≤ ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, W₀1 * Real.log p := by
                    refine Finset.sum_le_sum fun p hp => ?_
                    have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
                    have hp_mem : (p : ℝ) ∈ Set.Icc (P_k : ℝ) (2 * P_k) :=
                      ⟨by exact_mod_cast hp_icc.1, le_trans (by exact_mod_cast hp_icc.2) hb_le⟩
                    exact mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (hw_bd p hp_mem))
                      (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
                _ = W₀1 * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p := by rw [← Finset.mul_sum]
                _ ≤ W₀1 * (2 * Real.log 4 * P_k) := by
                    refine mul_le_mul_of_nonneg_left ?_ hW0
                    have hth : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p ≤ Chebyshev.theta (2 * P_k) := by
                      unfold Chebyshev.theta
                      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
                        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
                      intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
                      exact ⟨⟨hp.2.pos, Nat.le_floor (le_trans (by exact_mod_cast hp.1.2) hb_le)⟩, hp.2⟩
                    exact le_trans hth (by linarith [Chebyshev.theta_le_log4_mul_x (by positivity : 0 ≤ 2 * (P_k : ℝ))])
            have hW0P_eq : W₀1 * (2 * Real.log 4 * (P_k : ℝ)) = 2 * (2 * Real.log 4) := by
              dsimp [W₀1]; field_simp [hP_pos.ne']; ring
            rw [hW0P_eq] at hsum_le
            calc (2 / ((H : ℝ) + 1)) * ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (w1 p * Real.log p : ℂ)‖
                ≤ (2 / ((H : ℝ) + 1)) * (2 * (2 * Real.log 4)) := mul_le_mul_of_nonneg_left hsum_le (by positivity)
              _ = (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4) := by ring
          have h_f_bd : ‖∑ k_freq ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                bTilde k_freq * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                  (w1 p * Real.log p : ℂ) * ePhase ((k_freq : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
              12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) := by
            refine le_trans (norm_sum_le _ _) ?_
            have hterm : ∀ k_freq ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                ‖bTilde k_freq * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                  (w1 p * Real.log p : ℂ) * ePhase ((k_freq : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
                (3 / ((H : ℝ) + 1)) * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) := by
              intro k_freq hk
              rw [norm_mul]
              have hk' := Finset.mem_filter.mp hk
              have hk_icc := Finset.mem_Icc.mp hk'.1
              have hk_abs : |k_freq| ≤ 2 * (H : ℤ) + 1 := abs_le.mpr ⟨hk_icc.1, hk_icc.2⟩
              let h_fn : ℕ → ℤ := fun s => if s = r then k_freq else 0
              have hA_sub : ({r} : Finset ℕ) ⊆ Finset.Icc 1 R := Finset.singleton_subset_iff.mpr (Finset.mem_Icc.mpr hr_icc)
              have hA_ne : ({r} : Finset ℕ).Nonempty := ⟨r, Finset.mem_singleton_self r⟩
              have hnonzero : ∃ s ∈ ({r} : Finset ℕ), h_fn s ≠ 0 := ⟨r, Finset.mem_singleton_self r, by simp [h_fn, hk'.2]⟩
              have hh_bd : ∀ s ∈ ({r} : Finset ℕ), |h_fn s| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1 := by
                intro s hs; rw [Finset.mem_singleton.mp hs]; simp only [h_fn, ↓reduceIte]; exact_mod_cast hk_abs
              have hT₀_ge : (|(h_fn r : ℝ)| * n) / (P_k : ℝ) ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR := by
                have hk1 : (1 : ℝ) ≤ |(k_freq : ℝ)| := by exact_mod_cast Int.one_le_abs hk'.2
                simp only [h_fn, ↓reduceIte]
                exact le_trans hr_ar (div_le_div_of_nonneg_right (le_mul_of_one_le_left (Nat.cast_nonneg n) hk1) (by positivity))
              have hbd := h24i n (P_k : ℝ) (P_k : ℝ) (b_k : ℝ) {r} h_fn w1 W₀1 hNi hP_lo hP_hi le_rfl hb_ge hb_le
                hA_sub hA_ne (fun s hs => by rw [Finset.mem_singleton.mp hs]; exact hr_ar) hnonzero hh_bd hW0 hw_bd hw_diff hw_tv
              have hbd_fin := hbd (by
                have hr_min : (({r} : Finset ℕ).filter (fun s => h_fn s ≠ 0)).min' _ = r := by
                  have : ({r} : Finset ℕ).filter (fun s => h_fn s ≠ 0) = {r} := by ext s; simp [h_fn, hk'.2]
                  simp [this]
                simpa [hr_min] using hT₀_ge)
              have hsum_eq : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    (w1 p * Real.log p : ℂ) * ePhase ((k_freq : ℝ) * n / (2 * (p : ℝ) ^ r)) =
                  ∑ p ∈ (Finset.Icc ⌈(P_k : ℝ)⌉₊ ⌊(b_k : ℝ)⌋₊).filter Nat.Prime,
                    (w1 p * Real.log p : ℂ) * ePhase (∑ s ∈ ({r} : Finset ℕ), (h_fn s : ℝ) * n / (2 * (p : ℝ) ^ s)) := by
                rw [Nat.ceil_natCast, Nat.floor_natCast]
                refine Finset.sum_congr rfl fun p _ => ?_; simp [h_fn]
              rw [hsum_eq]
              have hW0P_2 : C'_δ * W₀1 * P_k * (Real.log n) ^ (-(R + 2 : ℤ)) = C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ)) := by
                dsimp [W₀1]; field_simp [hP_pos.ne']
              exact mul_le_mul (hb_bd_all k_freq).le (hW0P_2 ▸ le_trans hbd_fin.1 hbd_fin.2) (norm_nonneg _) (by positivity)
            have hcard_le : (((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).card : ℝ) ≤ 4 * ((H : ℝ) + 1) := by
              have h1' := Finset.card_filter_le (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)) (· ≠ 0)
              have h2' : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by rw [Int.card_Icc]; omega
              have h3' : ((4 * H + 3 : ℕ) : ℝ) ≤ 4 * ((H : ℝ) + 1) := by push_cast; linarith
              exact le_trans (by exact_mod_cast h1') (by exact_mod_cast h2' ▸ h3')
            calc ∑ k_freq ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                  ‖bTilde k_freq * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    (w1 p * Real.log p : ℂ) * ePhase ((k_freq : ℝ) * n / (2 * (p : ℝ) ^ r))‖
                ≤ ∑ _k ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                    (3 / ((H : ℝ) + 1)) * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) := Finset.sum_le_sum hterm
              _ = (((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)).card : ℝ) *
                    ((3 / ((H : ℝ) + 1)) * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ)))) := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (4 * ((H : ℝ) + 1)) * ((3 / ((H : ℝ) + 1)) * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ)))) :=
                    mul_le_mul_of_nonneg_right hcard_le (by positivity)
              _ = 12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) := by
                    field_simp [(by positivity : (H : ℝ) + 1 ≠ 0)]; ring
          exact le_trans hnorm_le (le_trans (norm_add_le _ _) (by linarith [h_b0_bd, h_f_bd]))
        have hAbig_card : (A_big.card : ℝ) ≤ R :=
          by exact_mod_cast le_trans (Finset.card_le_card (Finset.filter_subset _ _))
            (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp [Nat.card_Icc]))
        calc 15 ^ R * ∑ r ∈ A_big, ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                w1 p * Real.log p * Btilde ((n : ℝ) / (p : ℝ) ^ r)
            ≤ 15 ^ R * ∑ _r ∈ A_big, (12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
                (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4)) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_single_r) (by positivity)
          _ = 15 ^ R * (A_big.card : ℝ) * (12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
                (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ 15 ^ R * (R : ℝ) * (12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
                (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAbig_card (by positivity)) (by positivity)
      set S_freq := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun k => k ≠ 0 ∧ ¬ 2 ∣ k)
      have h_sub_bd : ∀ (a' b' : ℕ), P_k ≤ a' → a' ≤ b' → b' ≤ b_k →
          ‖∑ p ∈ (Finset.Icc a' b').filter Nat.Prime,
              ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))‖ ≤
          ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by
        intro a' b' ha' hab' hb'
        have hprod_exp : ∀ p : ℕ, ((∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ) =
            ∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq),
              (∏ r : A_big, cTilde (f r)) * ePhase (∑ r ∈ A_big, ((if hr : r ∈ A_big then (f ⟨r, hr⟩ : ℤ) else 0 : ℤ) : ℝ) * n / (2 * (p : ℝ) ^ r)) := by
          intro p; push_cast
          have h1 : ∏ r ∈ A_big, (Ψtilde ((n : ℝ) / (p : ℝ) ^ r) : ℂ) =
              ∏ r : A_big, ∑ k ∈ S_freq, cTilde k * ePhase ((k : ℝ) * ((n : ℝ) / (p : ℝ) ^ r.1) / 2) := by
            rw [← Finset.prod_coe_sort A_big]; exact Finset.prod_congr rfl fun r _ => hΨ _
          rw [h1, Fintype.prod_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.prod_mul_distrib]; congr 1
          have hprod_e : ∏ r : A_big, ePhase ((f r : ℝ) * ((n : ℝ) / (p : ℝ) ^ r.1) / 2) =
              ePhase (∑ r : A_big, (f r : ℝ) * ((n : ℝ) / (p : ℝ) ^ r.1) / 2) := by
            clear h1
            induction (Finset.univ : Finset A_big) using Finset.induction_on with
            | empty => simp [ePhase]
            | @insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, ePhase_add']
          rw [hprod_e]; congr 1; rw [← Finset.sum_coe_sort A_big]
          refine Finset.sum_congr rfl fun r _ => ?_; simp only [r.2, ↓reduceDIte]; ring
        have hswap : ∑ p ∈ (Finset.Icc a' b').filter Nat.Prime,
              ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r)) =
            ∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq),
              (∏ r : A_big, cTilde (f r)) * ∑ p ∈ (Finset.Icc a' b').filter Nat.Prime,
                (w1 p * Real.log p : ℂ) * ePhase (∑ r ∈ A_big, ((if hr : r ∈ A_big then (f ⟨r, hr⟩ : ℤ) else 0 : ℤ) : ℝ) * n / (2 * (p : ℝ) ^ r)) := by
          simp_rw [hprod_exp, Finset.mul_sum]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
        rw [hswap]
        refine le_trans (norm_sum_le _ _) ?_
        have hterm_f : ∀ f ∈ Fintype.piFinset (fun _ : A_big => S_freq),
            ‖(∏ r : A_big, cTilde (f r)) * ∑ p ∈ (Finset.Icc a' b').filter Nat.Prime,
                (w1 p * Real.log p : ℂ) * ePhase (∑ r ∈ A_big, ((if hr : r ∈ A_big then (f ⟨r, hr⟩ : ℤ) else 0 : ℤ) : ℝ) * n / (2 * (p : ℝ) ^ r))‖ ≤
              (∏ r : A_big, ‖cTilde (f r)‖) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by
          intro f hf; rw [norm_mul, norm_prod]
          refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          let h_fn : ℕ → ℤ := fun r => if hr : r ∈ A_big then f ⟨r, hr⟩ else 0
          have hf_mem : ∀ r : A_big, f r ∈ S_freq := fun r => Fintype.mem_piFinset.mp hf r
          have hA_sub : A_big ⊆ Finset.Icc 1 R := Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          have hA_ne : A_big.Nonempty := ⟨1, h1_big⟩
          have hnonzero : ∃ r ∈ A_big, h_fn r ≠ 0 :=
            ⟨1, h1_big, by simp only [h_fn, h1_big, ↓reduceDIte]; exact (Finset.mem_filter.mp (hf_mem ⟨1, h1_big⟩)).2.1⟩
          have hh_bd : ∀ r ∈ A_big, |h_fn r| ≤ 2 * ⌊(Real.log n) ^ (R + 2)⌋₊ + 1 := by
            intro r hr; simp only [h_fn, hr, ↓reduceDIte]
            have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hf_mem ⟨r, hr⟩)).1; exact abs_le.mpr ⟨h1.1, h1.2⟩
          have hr0_eq1 : (A_big.filter (fun r => h_fn r ≠ 0)).min' _ = 1 := by
            refine le_antisymm (Finset.min'_le _ 1 (Finset.mem_filter.mpr ⟨h1_big, by
              simp only [h_fn, h1_big, ↓reduceDIte]; exact (Finset.mem_filter.mp (hf_mem ⟨1, h1_big⟩)).2.1⟩)) ?_
            refine Finset.le_min' _ _ _ fun r hr => (Finset.mem_Icc.mp (hA_sub (Finset.mem_filter.mp hr).1)).1
          have hT₀_ge : (|(h_fn 1 : ℝ)| * n) / (P_k : ℝ) ^ 1 ≥ (n : ℝ) ^ (δ / 2) := by
            have hk1 : (1 : ℝ) ≤ |(h_fn 1 : ℝ)| := by
              exact_mod_cast Int.one_le_abs (by simp only [h_fn, h1_big, ↓reduceDIte]; exact (Finset.mem_filter.mp (hf_mem ⟨1, h1_big⟩)).2.1)
            have h1 : (n : ℝ) / P_k ≥ (n : ℝ) ^ (1 / 2 : ℝ) := by
              have hle : (P_k : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
                have : (P_k : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hk_le
                have hsqrt_le : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
                  Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
                rw [Real.sqrt_eq_rpow] at hsqrt_le; exact le_trans this hsqrt_le
              calc (n : ℝ) / P_k ≥ (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_left hn_pos.le hP_pos hle
                _ = (n : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_one (n : ℝ), ← Real.rpow_sub hn_pos]; norm_num
            rw [pow_one]
            exact le_trans hsqrt_d2 (le_trans h1 (div_le_div_of_nonneg_right (le_mul_of_one_le_left hn_pos.le hk1) hP_pos.le))
          have hbd := h24ii n (P_k : ℝ) (a' : ℝ) (b' : ℝ) A_big h_fn w1 W₀1 hNii hP_lo hP_hi
            (by exact_mod_cast ha') (by exact_mod_cast hab') (le_trans (by exact_mod_cast hb') hb_le)
            hA_sub hA_ne hnonzero hh_bd hW0 hw_bd hw_diff hw_tv (by simpa [hr0_eq1] using hT₀_ge)
          rw [Nat.ceil_natCast, Nat.floor_natCast] at hbd
          have hW0P_2 : C_ii * W₀1 * P_k * (n : ℝ) ^ (-η_δ) = 2 * C_ii * (n : ℝ) ^ (-η_δ) := by
            dsimp [W₀1]; field_simp [hP_pos.ne']; ring
          exact le_trans hbd hW0P_2.le
        have hsum_c : ∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq), (∏ r : A_big, ‖cTilde (f r)‖) ≤
            ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R := by
          have h1 : ∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq), (∏ r : A_big, ‖cTilde (f r)‖) =
              ∏ _r : A_big, ∑ k ∈ S_freq, ‖cTilde k‖ := by symm; exact Fintype.prod_sum (fun _ k => ‖cTilde k‖)
          rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
          have hcard_le : A_big.card ≤ R := le_trans (Finset.card_le_card (Finset.filter_subset _ _))
            (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp [Nat.card_Icc]))
          have hge1 : 1 ≤ (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) := by
            have h4pi : 1 ≤ 4 / Real.pi := (one_le_div Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
            have hlog1 : 0 ≤ Real.log (2 * (H : ℝ) + 1) := Real.log_nonneg (by positivity)
            nlinarith
          exact le_trans (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hc_sum A_big.card)
            (pow_le_pow_right₀ hge1 hcard_le)
        calc ∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq),
              ‖(∏ r : A_big, cTilde (f r)) * ∑ p ∈ (Finset.Icc a' b').filter Nat.Prime,
                (w1 p * Real.log p : ℂ) * ePhase (∑ r ∈ A_big, ((if hr : r ∈ A_big then (f ⟨r, hr⟩ : ℤ) else 0 : ℤ) : ℝ) * n / (2 * (p : ℝ) ^ r))‖
            ≤ ∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq),
                (∏ r : A_big, ‖cTilde (f r)‖) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := Finset.sum_le_sum hterm_f
          _ = (∑ f ∈ Fintype.piFinset (fun _ : A_big => S_freq), (∏ r : A_big, ‖cTilde (f r)‖)) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by rw [Finset.sum_mul]
          _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ)) :=
              mul_le_mul_of_nonneg_right hsum_c (by positivity)
      have hΨ_prod_bd : ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
            ((w1 p * Real.log p : ℝ) : ℂ) *
              (∏ r ∈ A_col, (-1 : ℝ) ^ (n / p ^ r)) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))‖ ≤
          ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * ((Real.log n) ^ AR + 1) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by
        by_cases hcol_empty : A_col = ∅
        · simp only [hcol_empty, Finset.prod_empty, Complex.ofReal_one, mul_one]
          have h1 := h_sub_bd P_k b_k le_rfl (by exact_mod_cast hb_ge) le_rfl
          have hAR1 : 1 ≤ (Real.log n) ^ AR + 1 := by linarith [pow_nonneg hlog_pos.le AR]
          calc ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))‖
              ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := h1
            _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * ((Real.log n) ^ AR + 1) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by
                nlinarith [show 0 ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ)) by positivity]
        · obtain ⟨r_col, hr_col⟩ := Finset.nonempty_iff_ne_empty.mpr hcol_empty
          have hcol_eq : A_col = {r_col} := by
            ext r; constructor
            · intro hr; by_contra hne
              have : 2 ≤ A_col.card := Finset.one_lt_card.mpr ⟨r_col, hr_col, r, hr, fun h => hne h.symm⟩; omega
            · intro hr; rw [Finset.mem_singleton.mp hr]; exact hr_col
          rw [hcol_eq]; simp only [Finset.prod_singleton]
          set J_col : ℕ := ⌊(Real.log n) ^ AR⌋₊
          have h_j_range : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, n / p ^ r_col ∈ Finset.Icc 0 J_col := by
            intro p hp; refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
            have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
            have hr_lt : (n : ℝ) / (P_k : ℝ) ^ r_col < (Real.log n) ^ AR := by
              have h1 := (Finset.mem_sdiff.mp hr_col).2
              have h2 : ¬ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR ≤ (n : ℝ) / (P_k : ℝ) ^ r_col :=
                fun h => h1 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hr_col).1, h⟩)
              linarith [show (Real.log n) ^ AR ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR from
                mul_le_of_le_one_left (by positivity) (by norm_num)]
            have h1 : (n : ℝ) / (p : ℝ) ^ r_col ≤ (n : ℝ) / (P_k : ℝ) ^ r_col :=
              div_le_div_of_nonneg_left hn_pos.le (by positivity) (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp_icc.1) r_col)
            have h2 : ((n / p ^ r_col : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ r_col := by
              rw [le_div_iff₀ (by positivity)]; exact_mod_cast Nat.div_mul_le_self n (p ^ r_col)
            exact Nat.le_floor (le_trans h2 (le_trans h1 hr_lt.le))
          have h_fiber :
              ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                ((w1 p * Real.log p : ℝ) : ℂ) * ((-1 : ℝ) ^ (n / p ^ r_col)) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r)) =
              ∑ j ∈ Finset.Icc 0 J_col, ((-1 : ℝ) ^ j : ℂ) *
                ∑ p ∈ ((Finset.Icc P_k b_k).filter Nat.Prime).filter (fun p => n / p ^ r_col = j),
                  ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r)) := by
            rw [← Finset.sum_fiberwise_of_maps_to h_j_range]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p hp => ?_
            rw [(Finset.mem_filter.mp hp).2]; push_cast; ring
          rw [h_fiber]; refine le_trans (norm_sum_le _ _) ?_
          have h_j_bd : ∀ j ∈ Finset.Icc 0 J_col,
              ‖((-1 : ℝ) ^ j : ℂ) *
                ∑ p ∈ ((Finset.Icc P_k b_k).filter Nat.Prime).filter (fun p => n / p ^ r_col = j),
                  ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))‖ ≤
              ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by
            intro j _
            rw [norm_mul, show ‖((-1 : ℝ) ^ j : ℂ)‖ = 1 by rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow], one_mul]
            set S_j := ((Finset.Icc P_k b_k).filter Nat.Prime).filter (fun p => n / p ^ r_col = j)
            by_cases hSj : S_j = ∅
            · rw [hSj, Finset.sum_empty, norm_zero]; positivity
            · have hne : S_j.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSj
              set a_j := S_j.min' hne
              set b_j := S_j.max' hne
              have ha_j : P_k ≤ a_j := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.min'_mem S_j hne)).1).1).1
              have hb_j : b_j ≤ b_k := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.max'_mem S_j hne)).1).1).2
              have hab_j : a_j ≤ b_j := Finset.min'_le S_j b_j (Finset.max'_mem S_j hne)
              have hSj_eq : S_j = (Finset.Icc a_j b_j).filter Nat.Prime := by
                ext p; simp only [S_j, Finset.mem_filter, Finset.mem_Icc]
                constructor
                · intro hp; exact ⟨⟨Finset.min'_le S_j p (by simpa [S_j] using hp), Finset.le_max' S_j p (by simpa [S_j] using hp)⟩, hp.1.2⟩
                · rintro ⟨⟨hp1, hp2⟩, hp⟩
                  refine ⟨⟨⟨le_trans ha_j hp1, le_trans hp2 hb_j⟩, hp⟩, ?_⟩
                  have ha_div : n / a_j ^ r_col = j := (Finset.mem_filter.mp (Finset.min'_mem S_j hne)).2
                  have hb_div : n / b_j ^ r_col = j := (Finset.mem_filter.mp (Finset.max'_mem S_j hne)).2
                  have hanti1 : n / b_j ^ r_col ≤ n / p ^ r_col := Nat.div_le_div_left (Nat.pow_le_pow_left hp2 r_col) (pow_pos hp.pos r_col)
                  have hanti2 : n / p ^ r_col ≤ n / a_j ^ r_col := Nat.div_le_div_left (Nat.pow_le_pow_left hp1 r_col) (pow_pos (Finset.mem_filter.mp (Finset.min'_mem S_j hne)).1.2.pos r_col)
                  omega
              rw [hSj_eq]; exact h_sub_bd a_j b_j ha_j hab_j hb_j
          calc ∑ j ∈ Finset.Icc 0 J_col,
                ‖((-1 : ℝ) ^ j : ℂ) *
                  ∑ p ∈ ((Finset.Icc P_k b_k).filter Nat.Prime).filter (fun p => n / p ^ r_col = j),
                    ((w1 p * Real.log p : ℝ) : ℂ) * (∏ r ∈ A_big, Ψtilde ((n : ℝ) / (p : ℝ) ^ r))‖
              ≤ ∑ _j ∈ Finset.Icc 0 J_col,
                  ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := Finset.sum_le_sum h_j_bd
            _ = ((J_col + 1 : ℕ) : ℝ) * (((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ))) := by
                rw [Finset.sum_const, Nat.card_Icc, sub_zero, nsmul_eq_mul]
            _ ≤ ((Real.log n) ^ AR + 1) * (((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * (2 * C_ii * (n : ℝ) ^ (-η_δ))) :=
                mul_le_mul_of_nonneg_right (by push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ (Real.log n) ^ AR)]) (by positivity)
            _ = ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * ((Real.log n) ^ AR + 1) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) := by ring
      have hH_inv : 1 / ((H : ℝ) + 1) ≤ (Real.log n) ^ (-(R + 2 : ℤ)) := by
        rw [zpow_neg, zpow_natCast]; exact one_div_le_one_div_of_le (by positivity) (Nat.lt_floor_add_one _).le
      have h_log_pow_le : (Real.log n) ^ (-(R + 2 : ℤ)) ≤ (Real.log n) ^ (-(R + 1 : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
      have h4pi_le : (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) ≤ 4 * (H : ℝ) + 3 := by
        have h1 : 4 / Real.pi ≤ 2 := by have : 2 ≤ Real.pi := by linarith [Real.pi_gt_three]; rw [div_le_iff₀ Real.pi_pos]; linarith
        have h2 : Real.log (2 * (H : ℝ) + 1) + 1 ≤ 2 * (H : ℝ) + 1 := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * (H : ℝ) + 1)]
        nlinarith [show (0 : ℝ) ≤ 4 / Real.pi by positivity, show (0 : ℝ) ≤ Real.log (2 * (H : ℝ) + 1) + 1 by positivity]
      have h_Ψ_le : ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * ((Real.log n) ^ AR + 1) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) ≤
          C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ)) := by
        have hpow : ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R ≤ (4 * (H : ℝ) + 3) ^ R :=
          pow_le_pow_left₀ (by positivity) h4pi_le R
        have h2_le : (2 : ℝ) ≤ 2 * Real.log n := by linarith
        calc ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ R * ((Real.log n) ^ AR + 1) * (2 * C_ii * (n : ℝ) ^ (-η_δ))
            ≤ (4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (2 * C_ii * (n : ℝ) ^ (-η_δ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
          _ ≤ C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ)) := by
              have hle := mul_le_mul_of_nonneg_right h2_le (by positivity : 0 ≤ C_ii * ((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (n : ℝ) ^ (-η_δ)))
              linarith
      have h_B_le : 15 ^ R * (R : ℝ) * (12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
            (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4)) ≤
          15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)) := by
        have h1 : 12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) + (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4) ≤
            (12 * C'_δ * 2 + 8 * Real.log 4) * (Real.log n) ^ (-(R + 1 : ℤ)) := by
          have h_2H : (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4) ≤ 8 * Real.log 4 * (Real.log n) ^ (-(R + 1 : ℤ)) := by
            have : 2 / ((H : ℝ) + 1) = 2 * (1 / ((H : ℝ) + 1)) := by ring
            rw [this]; have hle := le_trans hH_inv h_log_pow_le; nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
          nlinarith [h_log_pow_le]
        have h2_le : 1 ≤ 2 * Real.log n := by linarith
        calc 15 ^ R * (R : ℝ) * (12 * (C'_δ * 2 * (Real.log n) ^ (-(R + 2 : ℤ))) +
              (2 / ((H : ℝ) + 1)) * 2 * (2 * Real.log 4))
            ≤ 15 ^ R * (R : ℝ) * ((12 * C'_δ * 2 + 8 * Real.log 4) * (Real.log n) ^ (-(R + 1 : ℤ))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ 15 ^ R * (R : ℝ) * ((12 * C'_δ * 2 + 8 * Real.log 4) * (Real.log n) ^ (-(R + 1 : ℤ))) * (2 * Real.log n) :=
              le_mul_of_one_le_right (by positivity) h2_le
          _ = 15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)) := by ring
      exact le_trans h_approx_prod (add_le_add (le_trans hΨ_prod_bd h_Ψ_le) (le_trans hB_err_bd h_B_le))
    have hcard_dy : (((Finset.range (Nat.log 2 B_hi + 1)).filter (fun k => A_lo * 2 ^ k ≤ B_hi)).card : ℝ) ≤
        2 * Real.log n := by
      have h1 := Finset.card_filter_le (Finset.range (Nat.log 2 B_hi + 1)) (fun k => A_lo * 2 ^ k ≤ B_hi)
      rw [Finset.card_range] at h1
      have h2 : (Nat.log 2 B_hi : ℝ) ≤ Real.log n := by
        have hpow : (2 : ℝ) ^ Nat.log 2 B_hi ≤ n := by
          exact_mod_cast le_trans (Nat.pow_log_le_self 2 (by omega)) (Nat.sqrt_le_self n)
        have hlg := Real.log_le_log (by positivity) hpow
        rw [Real.log_pow] at hlg
        have : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        nlinarith
      have h3 : ((Nat.log 2 B_hi + 1 : ℕ) : ℝ) ≤ 2 * Real.log n := by push_cast; linarith
      exact le_trans (by exact_mod_cast h1) h3
    calc ∑ k ∈ (Finset.range (Nat.log 2 B_hi + 1)).filter (fun k => A_lo * 2 ^ k ≤ B_hi),
          ‖∑ p ∈ Finset.Icc (A_lo * 2 ^ k) (min B_hi (2 * (A_lo * 2 ^ k) - 1)),
            if p.Prime then (((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) * (-1 : ℝ) ^ padicValNat p n.factorial) else 0‖
        ≤ ∑ _k ∈ (Finset.range (Nat.log 2 B_hi + 1)).filter (fun k => A_lo * 2 ^ k ≤ B_hi),
            (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)) +
              C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ))) :=
          Finset.sum_le_sum hblock_bd
      _ = (((Finset.range (Nat.log 2 B_hi + 1)).filter (fun k => A_lo * 2 ^ k ≤ B_hi)).card : ℝ) *
            (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)) +
              C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * Real.log n) *
            (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)) +
              C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ))) :=
          mul_le_mul_of_nonneg_right hcard_dy (by positivity)
      _ ≤ 4 * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * 2) * (Real.log n)⁻¹ +
            4 * (C_ii * (2 : ℝ) ^ (3 * R + 1)) * (Real.log n)⁻¹ := by
          have h_term1 : (2 * Real.log n) * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ))) ≤
              4 * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * 2) * (Real.log n)⁻¹ := by
            have hpow_le : (Real.log n) ^ 2 * (Real.log n) ^ (-(R + 1 : ℤ)) ≤ (Real.log n)⁻¹ := by
              rw [← zpow_natCast (Real.log n) 2, ← zpow_add₀ hlog_pos.ne', zpow_neg_one]
              rw [show (2 : ℤ) + -(R + 1 : ℤ) = -(R - 1 : ℤ) by omega, zpow_neg, zpow_natCast]
              exact inv_anti₀ hlog_pos (le_self_pow₀ (by linarith) (by omega))
            calc (2 * Real.log n) * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * (2 * Real.log n) * (Real.log n) ^ (-(R + 1 : ℤ)))
                = 4 * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4)) * ((Real.log n) ^ 2 * (Real.log n) ^ (-(R + 1 : ℤ))) := by ring
              _ ≤ 4 * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4)) * (Real.log n)⁻¹ :=
                  mul_le_mul_of_nonneg_left hpow_le (by positivity)
              _ ≤ 4 * (15 ^ R * (R : ℝ) * (12 * C'_δ * 2 + 8 * Real.log 4) * 2) * (Real.log n)⁻¹ := by
                  nlinarith [inv_pos.mpr hlog_pos]
          have h_term2 : (2 * Real.log n) * (C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ))) ≤
              4 * (C_ii * (2 : ℝ) ^ (3 * R + 1)) * (Real.log n)⁻¹ := by
            have h1 : (2 * Real.log n) * (C_ii * (2 * Real.log n) * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1)) * (n : ℝ) ^ (-η_δ))) =
                4 * C_ii * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2) * (n : ℝ) ^ (-η_δ)) := by ring
            rw [h1]
            calc 4 * C_ii * (((4 * (H : ℝ) + 3) ^ R * ((Real.log n) ^ AR + 1) * (Real.log n) ^ 2) * (n : ℝ) ^ (-η_δ))
                ≤ 4 * C_ii * ((2 : ℝ) ^ (3 * R + 1) * (Real.log n)⁻¹) := mul_le_mul_of_nonneg_left h_decay (by positivity)
              _ = 4 * (C_ii * (2 : ℝ) ^ (3 * R + 1)) * (Real.log n)⁻¹ := by ring
          linarith
      _ ≤ C_tot * (Real.log n)⁻¹ := by dsimp [C_tot]; nlinarith [inv_pos.mpr hlog_pos]

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
  have h1 := theorem_2_5_ii_part1
  have h2 : IsLittleOAtTop SigmaParityStar (fun n => Real.log n) := by
    rw [isLittleOAtTop_iff]
    intro ε hε
    set δ : ℝ := min (ε / 4) (1 / 3)
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 / 3 := min_le_right _ _
    obtain ⟨C_tail, hC_tail, h_tail⟩ := h1 δ hδ0 hδ1
    obtain ⟨C_m, hC_m, _, hm_bd⟩ := mertens_first_theorem
    have h_ev : ∀ᶠ n : ℕ in atTop,
        |∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))| ≤
          C_tail * (Real.log n)⁻¹ ∧
        4 ≤ n ∧ 2 ≤ (n : ℝ) ^ δ ∧
        (2 * C_m + 1) / Real.log n ≤ ε / 4 ∧
        C_tail * (Real.log n)⁻¹ / Real.log n ≤ ε / 4 := by
      have ha := h_tail
      have hb := eventually_ge_atTop 4
      have hc := ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      have hd : ∀ᶠ n : ℕ in atTop, (2 * C_m + 1) / Real.log n ≤ ε / 4 := by
        have h0 := (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) :
          Tendsto (fun n : ℕ => (2 * C_m + 1) / Real.log n) atTop (𝓝 0))
        exact h0.eventually (le_mem_nhds (by positivity))
      have he : ∀ᶠ n : ℕ in atTop, C_tail * (Real.log n)⁻¹ / Real.log n ≤ ε / 4 := by
        have h0 : Tendsto (fun n : ℕ => C_tail * (Real.log n)⁻¹ / Real.log n) atTop (𝓝 0) := by
          have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
          simpa using (tendsto_const_nhds.div_atTop (hlog.mul hlog) : Tendsto (fun n : ℕ => C_tail / (Real.log n * Real.log n)) atTop (𝓝 0))
        exact h0.eventually (le_mem_nhds (by positivity))
      filter_upwards [ha, hb, hc, hd, he] with n a b c d e
      refine ⟨?_, b, c, d, e⟩
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      simpa [abs_of_pos (inv_pos.mpr hlog_pos)] using a
    filter_upwards [h_ev] with n ⟨htail_n, hn4, hnd2, hcm_n, hct_n⟩
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hfl_sqrt : ⌊Real.sqrt n⌋₊ = Nat.sqrt n := by
      rw [Nat.floor_eq_iff (Real.sqrt_nonneg n)]
      exact ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n)),
        Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast (by simpa [sq] using Nat.lt_succ_sqrt n))⟩
    have h_split : SigmaParityStar n =
        (∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))) +
        (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))) := by
      unfold SigmaParityStar SigmaParity; rw [hfl_sqrt]
      by_cases h_le : ⌊(n : ℝ) ^ δ⌋₊ ≤ Nat.sqrt n
      · rw [min_eq_right h_le]
        have hu : Finset.Icc 3 (Nat.sqrt n) = Finset.Icc 3 ⌊(n : ℝ) ^ δ⌋₊ ∪ Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n) := by
          ext p; simp only [Finset.mem_union, Finset.mem_Icc]
          have : 2 ≤ ⌊(n : ℝ) ^ δ⌋₊ := Nat.le_floor hnd2; omega
        have hdisj : Disjoint ((Finset.Icc 3 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime)
            ((Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime) := by
          rw [Finset.disjoint_left]; intro p hp1 hp2; simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2; omega
        rw [hu, Finset.filter_union, Finset.sum_union hdisj]
      · rw [min_eq_left (le_of_not_ge h_le)]
        have h_emp : (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime = ∅ := by
          ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
        rw [h_emp, Finset.sum_empty, add_zero]
    have h_head :
        |∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))| ≤
        2 * δ * Real.log n + 2 * C_m := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hle1 : ∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime,
            |(-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))| ≤
          ∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime, 2 * (Real.log p / p) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := Finset.mem_filter.mp hp
        have hp3 := (Finset.mem_Icc.mp hp'.1).1
        have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le)
        rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
          abs_of_nonneg (div_nonneg hlog_nn (by exact_mod_cast (by omega : 0 ≤ (p : ℤ) - 1)))]
        have hp_le : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by have : (3 : ℝ) ≤ p := by exact_mod_cast hp3; linarith
        rw [← mul_div_assoc, div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < (p : ℤ) - 1)) (by exact_mod_cast hp'.2.pos)]
        nlinarith
      have hle2 : ∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime, 2 * (Real.log p / p) ≤
          2 * ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime, Real.log p / p := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢; exact ⟨⟨by omega, le_trans hp.1.2 (min_le_right _ _)⟩, hp.2⟩
        · intro p hp _; have hp_prime := (Finset.mem_filter.mp hp).2; positivity
      have hm := abs_le.mp (hm_bd ((n : ℝ) ^ δ) hnd2)
      have hlog_nd : Real.log ((n : ℝ) ^ δ) = δ * Real.log n := Real.log_rpow (by exact_mod_cast (by omega : 0 < n)) _
      nlinarith [hm.2, hlog_nd]
    rw [abs_of_pos hlog_pos, h_split]
    have h_tail_bd : C_tail * (Real.log n)⁻¹ ≤ (ε / 4) * Real.log n := by
      have := mul_le_mul_of_nonneg_right hct_n hlog_pos.le; rwa [div_mul_cancel₀ _ hlog_pos.ne'] at this
    have h_cm_bd : 2 * C_m ≤ (ε / 4) * Real.log n := by
      have := mul_le_mul_of_nonneg_right hcm_n hlog_pos.le; rw [div_mul_cancel₀ _ hlog_pos.ne'] at this; linarith [hC_m]
    have h_d_bd : 2 * δ ≤ ε / 2 := by linarith [min_le_left (ε / 4) (1 / 3)]
    calc |∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime,
            (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)) +
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime,
            (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))|
        ≤ |∑ p ∈ (Finset.Icc 3 (min (Nat.sqrt n) ⌊(n : ℝ) ^ δ⌋₊)).filter Nat.Prime,
            (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))| +
          |∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ δ⌋₊ + 1) (Nat.sqrt n)).filter Nat.Prime,
            (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))| := abs_add_le _ _
      _ ≤ (2 * δ * Real.log n + 2 * C_m) + C_tail * (Real.log n)⁻¹ := add_le_add h_head htail_n
      _ ≤ (ε / 2) * Real.log n + (ε / 4) * Real.log n + (ε / 4) * Real.log n := by
          nlinarith [mul_le_mul_of_nonneg_right h_d_bd hlog_pos.le]
      _ = ε * Real.log n := by ring
  have h3 : IsLittleOAtTop DeltaParity (fun n => (n : ℝ) * Real.log n) := by
    rw [isLittleOAtTop_iff]
    intro ε hε
    obtain ⟨C_25, hC_25, h_25⟩ := theorem_2_5_i
    rw [isLittleOAtTop_iff] at h2
    have hSig := h2 (ε / 2) (by positivity)
    have h_ev : ∀ᶠ n : ℕ in atTop,
        |DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ)| ≤ C_25 * ((n : ℝ) / Real.log n) ∧
        |SigmaParityStar n| ≤ (ε / 2) * Real.log n ∧
        (|Real.log 2 - 1| + C_25) / Real.log n ≤ ε / 2 ∧ 2 ≤ n := by
      have ha : ∀ᶠ n : ℕ in atTop, |DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ)| ≤ C_25 * ((n : ℝ) / Real.log n) := by
        filter_upwards [h_25, eventually_ge_atTop 2] with n hn hn2
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        simpa [abs_of_pos (div_pos hn_pos hlog_pos)] using hn
      have hb : ∀ᶠ n : ℕ in atTop, |SigmaParityStar n| ≤ (ε / 2) * Real.log n := by
        filter_upwards [hSig, eventually_ge_atTop 2] with n hn hn2
        have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        simpa [abs_of_pos hlog_pos] using hn
      have hc : ∀ᶠ n : ℕ in atTop, (|Real.log 2 - 1| + C_25) / Real.log n ≤ ε / 2 := by
        have h0 := tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        exact (h0 : Tendsto (fun n : ℕ => (|Real.log 2 - 1| + C_25) / Real.log n) atTop (𝓝 0)).eventually (le_mem_nhds (by positivity))
      filter_upwards [ha, hb, hc, eventually_ge_atTop 2] with n a b c d using ⟨a, b, c, d⟩
    filter_upwards [h_ev] with n ⟨h25n, hsign, hconst, hn2⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [abs_of_pos (mul_pos hn_pos hlog_pos)]
    have h1' : |DeltaParity n| ≤ |DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ)| +
        |(Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ)| := by
      have := abs_add_le (DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ)) ((Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ))
      simpa using this
    have h2' : |(Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ)| ≤ (|Real.log 2 - 1| + |SigmaParityStar n|) * (n : ℝ) := by
      rw [abs_mul, abs_of_pos hn_pos]; exact mul_le_mul_of_nonneg_right (abs_sub _ _) hn_pos.le
    have h3' : |Real.log 2 - 1| * (n : ℝ) + C_25 * ((n : ℝ) / Real.log n) ≤ (ε / 2) * ((n : ℝ) * Real.log n) := by
      have hlog1 : 1 ≤ Real.log n := by
        have h1 : (|Real.log 2 - 1| + C_25) ≤ (ε / 2) * Real.log n := (div_le_iff₀ hlog_pos).mp hconst
        nlinarith [abs_nonneg (Real.log 2 - 1), show 0 ≤ C_25 by linarith]
      have hdiv : C_25 * ((n : ℝ) / Real.log n) ≤ C_25 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (div_le_self hn_pos.le hlog1) hC_25.le
      have hmul : (|Real.log 2 - 1| + C_25) * (n : ℝ) ≤ (ε / 2) * Real.log n * (n : ℝ) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hlog_pos).mp hconst) hn_pos.le
      linarith
    nlinarith
  have h_sum_eq : IsLittleOAtTop (fun n => Seven n + Sodd n - (n : ℝ) * Real.log n) (fun n => (n : ℝ) * Real.log n) := by
    rw [isLittleOAtTop_iff]
    intro ε hε
    have h_ev : ∀ᶠ n : ℕ in atTop,
        4 ≤ n ∧ (Real.log (Real.log n) + 2 + Real.log 2) / Real.log n ≤ ε := by
      have ha := eventually_ge_atTop 4
      have hb : Tendsto (fun n : ℕ => (Real.log (Real.log n) + 2 + Real.log 2) / Real.log n) atTop (𝓝 0) := by
        have h0 : Tendsto (fun u : ℝ => (Real.log u + (2 + Real.log 2)) / u) atTop (𝓝 0) := by
          have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
          have h2 : Tendsto (fun u : ℝ => (2 + Real.log 2) / u) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop tendsto_id
          simpa [add_div, add_assoc] using h1.add h2
        exact h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact ha.and (hb.eventually (le_mem_nhds hε))
    filter_upwards [h_ev] with n ⟨hn4, hbd⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h_fac_prod : n.factorial = ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ padicValNat p n.factorial := by
      conv_lhs => rw [← Nat.prod_primeFactors_pow_factorization (Nat.factorial_ne_zero n)]
      have hpf : n.factorial.primeFactors = (Finset.Icc 2 n).filter Nat.Prime := by
        ext p; rw [mem_primeFactors_factorial_iff, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun ⟨hp, hpn⟩ => ⟨⟨hp.two_le, hpn⟩, hp⟩, fun ⟨⟨_, hpn⟩, hp⟩ => ⟨hp, hpn⟩⟩
      rw [hpf]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def _ (Finset.mem_filter.mp hp).2]
    have hlog_fac_primes : Real.log (n.factorial : ℝ) =
        (padicValNat 2 n.factorial : ℝ) * Real.log 2 + (Seven n + Sodd n) := by
      have h_split : (Finset.Icc 2 n).filter Nat.Prime =
          insert 2 ((Finset.Icc 3 n).filter Nat.Prime) := by
        ext p; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp2, hpn⟩, hp⟩; rcases eq_or_lt_of_le hp2 with rfl | hlt; · left; rfl; · right; exact ⟨⟨hlt, hpn⟩, hp⟩
        · rintro (rfl | ⟨⟨hp3, hpn⟩, hp⟩); · exact ⟨⟨le_refl 2, by omega⟩, Nat.prime_two⟩; · exact ⟨⟨by omega, hpn⟩, hp⟩
      have h2_nmem : 2 ∉ (Finset.Icc 3 n).filter Nat.Prime := by simp
      have h_ss : Seven n + Sodd n = ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, (padicValNat p n.factorial : ℝ) * Real.log p := by
        unfold Seven Sodd
        have hdisj := (Podd_disjoint_Peven n).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hunion : (Peven n).filter (3 ≤ ·) ∪ (Podd n).filter (3 ≤ ·) = (Finset.Icc 3 n).filter Nat.Prime := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Peven, Podd]
          constructor
          · rintro (⟨⟨_, hpn⟩, hp, _⟩, hp3) | (⟨⟨_, hpn⟩, hp, _⟩, hp3) <;> exact ⟨⟨hp3, hpn⟩, hp⟩
          · rintro ⟨⟨hp3, hpn⟩, hp⟩
            by_cases hev : padicValNat p n.factorial % 2 = 0
            · left; exact ⟨⟨⟨hp.two_le, hpn⟩, hp, hev⟩, hp3⟩
            · right; exact ⟨⟨⟨hp.two_le, hpn⟩, hp, by omega⟩, hp3⟩
        rw [← Finset.sum_union hdisj, hunion]
      rw [h_ss]; conv_lhs => rw [h_fac_prod]
      push_cast
      rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero)),
        h_split, Finset.sum_insert h2_nmem, Real.log_pow]
      congr 1; refine Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
    have hlog_fac_sum : Real.log (n.factorial : ℝ) = ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) := by
      clear hlog_fac_primes h_fac_prod
      induction n with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ← ih, Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (by positivity) (by positivity), add_comm]
    have hlog_fac_ub : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
      rw [hlog_fac_sum]
      calc ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ)
          ≤ ∑ _k ∈ Finset.Icc 1 n, Real.log n := Finset.sum_le_sum fun k hk =>
            Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hk).1) (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
        _ = (n : ℝ) * Real.log n := by rw [Finset.sum_const, Nat.card_Icc, add_sub_cancel_right, nsmul_eq_mul]
    have hlog_fac_lb : (n : ℝ) * Real.log n - (n : ℝ) * (Real.log (Real.log n) + 2) ≤ Real.log (n.factorial : ℝ) := by
      by_cases hlog2 : Real.log n < 2
      · have : 0 ≤ Real.log (n.factorial : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos n)
        have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4
        have hlg4 : 1 ≤ Real.log n := by
          have : Real.exp 1 ≤ (n : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9]) h4
          simpa using Real.log_le_log (Real.exp_pos 1) this
        have hll_nn : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlg4
        nlinarith
      · push_neg at hlog2
        set M : ℕ := ⌈(n : ℝ) / Real.log n⌉₊
        have hM_le : M ≤ n := Nat.ceil_le.mpr (div_le_self hn_pos.le (by linarith))
        have hM_pos : 1 ≤ M := Nat.one_le_ceil_iff.mpr (div_pos hn_pos hlog_pos)
        have h_card : (n : ℝ) - (n : ℝ) / Real.log n - 1 ≤ ((Finset.Icc M n).card : ℝ) := by
          rw [Nat.card_Icc]
          have hM_lt : (M : ℝ) < (n : ℝ) / Real.log n + 1 := Nat.ceil_lt_add_one (div_pos hn_pos hlog_pos).le
          have hsub : M ≤ n + 1 := by omega
          rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]; linarith
        have h_fac_ge : ((Finset.Icc M n).card : ℝ) * (Real.log n - Real.log (Real.log n)) ≤ Real.log (n.factorial : ℝ) := by
          rw [hlog_fac_sum]
          calc ((Finset.Icc M n).card : ℝ) * (Real.log n - Real.log (Real.log n))
              = ∑ _k ∈ Finset.Icc M n, (Real.log n - Real.log (Real.log n)) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ k ∈ Finset.Icc M n, Real.log (k : ℝ) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hk_ge : (n : ℝ) / Real.log n ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
                rw [← Real.log_div hn_pos.ne' hlog_pos.ne']
                exact Real.log_le_log (div_pos hn_pos hlog_pos) hk_ge
            _ ≤ ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hM_pos) fun k hk _ =>
                  Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
        have h_diff_pos : 0 ≤ Real.log n - Real.log (Real.log n) := by linarith [Real.log_le_sub_one_of_pos hlog_pos]
        have h1 : ((n : ℝ) - (n : ℝ) / Real.log n - 1) * (Real.log n - Real.log (Real.log n)) ≤ Real.log (n.factorial : ℝ) :=
          le_trans (mul_le_mul_of_nonneg_right h_card h_diff_pos) h_fac_ge
        have h_ll_nn : 0 ≤ Real.log (Real.log n) := Real.log_nonneg (by linarith)
        have h2 : (n : ℝ) * Real.log n - (n : ℝ) * (Real.log (Real.log n) + 2) ≤
            ((n : ℝ) - (n : ℝ) / Real.log n - 1) * (Real.log n - Real.log (Real.log n)) := by
          have h_n_ge : Real.log n ≤ (n : ℝ) := by linarith [Real.log_le_sub_one_of_pos hn_pos]
          nlinarith [mul_nonneg (div_nonneg hn_pos.le hlog_pos.le) h_ll_nn]
        linarith
    have hv2_ub : (padicValNat 2 n.factorial : ℝ) ≤ n := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hleg := sub_one_mul_padicValNat_factorial (p := 2) n
      exact_mod_cast (by nlinarith : padicValNat 2 n.factorial ≤ n)
    have hv2_nn : 0 ≤ (padicValNat 2 n.factorial : ℝ) * Real.log 2 := by positivity
    rw [abs_of_pos (mul_pos hn_pos hlog_pos)]
    have hdiff : |Seven n + Sodd n - (n : ℝ) * Real.log n| ≤ (n : ℝ) * (Real.log (Real.log n) + 2 + Real.log 2) := by
      rw [abs_le]; constructor <;> linarith [mul_le_mul_of_nonneg_right hv2_ub (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    have hbd' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hlog_pos).mp hbd) hn_pos.le
    rw [div_mul_cancel₀ _ hlog_pos.ne'] at hbd'
    linarith
  have h4 : IsLittleOAtTop (fun n => Sodd n - (1 / 2 : ℝ) * n * Real.log n) (fun n => (n : ℝ) * Real.log n) := by
    rw [isLittleOAtTop_iff] at h_sum_eq h3 ⊢
    intro ε hε
    filter_upwards [h_sum_eq ε hε, h3 ε hε] with n hsum hdel
    have h1 : Sodd n - (1 / 2 : ℝ) * n * Real.log n =
        ((Seven n + Sodd n - (n : ℝ) * Real.log n) - DeltaParity n) / 2 := by unfold DeltaParity; ring
    rw [h1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_sub (Seven n + Sodd n - (n : ℝ) * Real.log n) (DeltaParity n)]
  have h5 : IsLittleOAtTop (fun n => Seven n - (1 / 2 : ℝ) * n * Real.log n) (fun n => (n : ℝ) * Real.log n) := by
    rw [isLittleOAtTop_iff] at h_sum_eq h3 ⊢
    intro ε hε
    filter_upwards [h_sum_eq ε hε, h3 ε hε] with n hsum hdel
    have h1 : Seven n - (1 / 2 : ℝ) * n * Real.log n =
        ((Seven n + Sodd n - (n : ℝ) * Real.log n) + DeltaParity n) / 2 := by unfold DeltaParity; ring
    rw [h1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le (Seven n + Sodd n - (n : ℝ) * Real.log n) (DeltaParity n)]
  exact ⟨h1, h2, h3, h4, h5⟩

private lemma vaaler_mod_approx (h : ℕ) (hh : 2 ≤ h) (t : ℕ) (ht1 : 1 ≤ t) (ht_lt : t < h)
    (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Ψm : ℝ → ℂ) (Bm : ℝ → ℝ) (cm bm : ℤ → ℂ),
      (∀ x : ℝ, Ψm x = ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), cm k * ePhase ((k : ℝ) * x / h)) ∧
      (∀ x : ℝ, (Bm x : ℂ) = bm 0 + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), bm k * ePhase ((k : ℝ) * x / h)) ∧
      (bm 0 = ((h : ℂ) / ((H : ℂ) + 1))) ∧
      (∀ k : ℤ, k ≠ 0 → ‖cm k‖ ≤ (h : ℝ) / (Real.pi * |(k : ℝ)|)) ∧
      (∀ k : ℤ, ‖bm k‖ ≤ (h : ℝ) / ((H : ℝ) + 1)) ∧
      (∀ x : ℝ, ‖ePhase ((t : ℝ) * (⌊x⌋ : ℝ) / h) - Ψm x‖ ≤ Bm x) ∧
      (∀ x : ℝ, ‖Ψm x‖ ≤ 1 + 4 * (h : ℝ)) ∧
      (∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), ‖cm k‖ ≤ (2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) := by
  obtain ⟨_, _, _, hVaaler⟩ := vaaler_sawtooth_approx
  obtain ⟨Ψ, B, c, b, hΨ, hB, _, hc_bd, hb0, hb_bd, _, happrox⟩ := hVaaler H hH
  let w_m : ℕ → ℂ := fun m => ePhase ((t : ℝ) * (m : ℝ) / h)
  let Ψm : ℝ → ℂ := fun x => ∑ m ∈ Finset.range h, w_m m * ((1 / (h : ℝ) + Ψ ((x - m - 1) / h) - Ψ ((x - m) / h) : ℝ) : ℂ)
  let Bm : ℝ → ℝ := fun x => ∑ m ∈ Finset.range h, (B ((x - m - 1) / h) + B ((x - m) / h))
  let coeff_sum_c : ℤ → ℂ := fun k => ∑ m ∈ Finset.range h, w_m m * (ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) - ePhase (-(k : ℝ) * (m : ℝ) / h))
  let coeff_sum_b : ℤ → ℂ := fun k => ∑ m ∈ Finset.range h, (ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) + ePhase (-(k : ℝ) * (m : ℝ) / h))
  let cm : ℤ → ℂ := fun k => c k * coeff_sum_c k
  let bm : ℤ → ℂ := fun k => b k * coeff_sum_b k
  refine ⟨Ψm, Bm, cm, bm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hw_zero : ∑ m ∈ Finset.range h, w_m m * ((1 / (h : ℝ) : ℝ) : ℂ) = 0 := by
      rw [← Finset.sum_mul]
      have h0 : ∑ m ∈ Finset.range h, w_m m = 0 := by
        have h1 := char_orthogonality_mod h (by omega) (t : ℤ)
        have hndvd : ¬ (h : ℤ) ∣ (t : ℤ) := fun hd => by have := Int.le_of_dvd (by exact_mod_cast ht1) hd; omega
        rw [if_neg hndvd] at h1; simpa [w_m] using h1
      rw [h0, zero_mul]
    simp only [Ψm]
    have h1 : ∑ m ∈ Finset.range h, w_m m * ((1 / (h : ℝ) + Ψ ((x - m - 1) / h) - Ψ ((x - m) / h) : ℝ) : ℂ) =
        (∑ m ∈ Finset.range h, w_m m * ((1 / (h : ℝ) : ℝ) : ℂ)) +
        ∑ m ∈ Finset.range h, w_m m * ((Ψ ((x - m - 1) / h) : ℂ) - (Ψ ((x - m) / h) : ℂ)) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun m _ => ?_; push_cast; ring
    rw [h1, hw_zero, zero_add]
    simp_rw [hΨ, ← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cm, coeff_sum_c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have he1 : ePhase ((k : ℝ) * ((x - m - 1) / h)) = ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) * ePhase ((k : ℝ) * x / h) := by
      rw [← ePhase_add']; congr 1; ring
    have he2 : ePhase ((k : ℝ) * ((x - m) / h)) = ePhase (-(k : ℝ) * (m : ℝ) / h) * ePhase ((k : ℝ) * x / h) := by
      rw [← ePhase_add']; congr 1; ring
    rw [he1, he2]; ring
  · intro x
    simp only [Bm, Complex.ofReal_sum, Complex.ofReal_add, hB]
    have hsplit : ∀ f : ℤ → ℝ → ℂ, (∑ k ∈ Finset.Icc (-(H : ℤ)) H, f k x) =
        f 0 x + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), f k x := by
      intro f
      have h0 : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [← Finset.add_sum_erase _ _ h0]
      congr 1; refine Finset.sum_congr (by ext k; simp [Finset.mem_erase, and_comm]) fun _ _ => rfl
    simp_rw [hsplit (fun k y => b k * ePhase ((k : ℝ) * y))]
    simp only [Int.cast_zero, zero_mul, ePhase, mul_zero, Complex.exp_zero, mul_one]
    have h_zero : ∑ m ∈ Finset.range h, (b 0 + b 0) = bm 0 := by
      simp only [bm, coeff_sum_b, neg_zero, zero_mul, zero_div, ePhase, Complex.exp_zero,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have h_rest : ∑ m ∈ Finset.range h,
          ((∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m - 1) / h)))) +
           (∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m) / h))))) =
        ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), bm k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * x / h)) := by
      simp_rw [← Finset.sum_add_distrib]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [bm, coeff_sum_b, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      have he1 : Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m - 1) / h))) =
          ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * x / h)) := by
        unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring
      have he2 : Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m) / h))) =
          ePhase (-(k : ℝ) * (m : ℝ) / h) * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * x / h)) := by
        unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [he1, he2]; ring
    have h_reorg : ∑ m ∈ Finset.range h,
          ((b 0 + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m - 1) / h)))) +
           (b 0 + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m) / h))))) =
        (∑ m ∈ Finset.range h, (b 0 + b 0)) +
        ∑ m ∈ Finset.range h,
          ((∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m - 1) / h)))) +
           (∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m) / h))))) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun m _ => by ring
    have heq_goal : ∑ m ∈ Finset.range h,
          ((b 0 + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m - 1) / h)))) +
           (b 0 + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), b k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * ((x - m) / h))))) =
        bm 0 + ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), bm k * Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) * x / h)) := by
      rw [h_reorg, h_zero, h_rest]
    simpa [ePhase] using heq_goal
  · simp only [bm, coeff_sum_b, hb0, neg_zero, zero_mul, zero_div, ePhase, Complex.exp_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hH0 : ((H : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : (H : ℤ) + 1 ≠ 0)
    field_simp [hH0]; ring
  · intro k hk
    rw [cm, norm_mul]
    have hc1 := hc_bd k hk
    have hc2 : ‖coeff_sum_c k‖ ≤ 2 * (h : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ Finset.range h, ‖w_m m * (ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) - ePhase (-(k : ℝ) * (m : ℝ) / h))‖
          ≤ ∑ _m ∈ Finset.range h, (2 : ℝ) := Finset.sum_le_sum fun m _ => by
            rw [norm_mul, show ‖w_m m‖ = 1 from norm_ePhase _, one_mul]
            exact le_trans (norm_sub_le _ _) (by rw [norm_ePhase, norm_ePhase]; norm_num)
        _ = 2 * (h : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    calc ‖c k‖ * ‖coeff_sum_c k‖ ≤ (1 / (2 * Real.pi * |(k : ℝ)|)) * (2 * (h : ℝ)) :=
          mul_le_mul hc1 hc2 (norm_nonneg _) (by positivity)
      _ = (h : ℝ) / (Real.pi * |(k : ℝ)|) := by field_simp [Real.pi_ne_zero]; ring
  · intro k
    rw [bm, norm_mul]
    have hb1 := hb_bd k
    have hb2 : ‖coeff_sum_b k‖ ≤ 2 * (h : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ Finset.range h, ‖ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) + ePhase (-(k : ℝ) * (m : ℝ) / h)‖
          ≤ ∑ _m ∈ Finset.range h, (2 : ℝ) := Finset.sum_le_sum fun m _ =>
            le_trans (norm_add_le _ _) (by rw [norm_ePhase, norm_ePhase]; norm_num)
        _ = 2 * (h : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    calc ‖b k‖ * ‖coeff_sum_b k‖ ≤ (1 / (2 * (H : ℝ) + 2)) * (2 * (h : ℝ)) :=
          mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
      _ = (h : ℝ) / ((H : ℝ) + 1) := by ring
  · intro x
    set r_mod : ℤ := ⌊x⌋ % (h : ℤ)
    have hr_lo : 0 ≤ r_mod := Int.emod_nonneg _ (by exact_mod_cast (by omega : h ≠ 0))
    have hr_hi : r_mod < h := Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < h))
    let m₀ : ℕ := r_mod.toNat
    have hm₀_range : m₀ ∈ Finset.range h := Finset.mem_range.mpr (by omega)
    have hm₀_eq : (m₀ : ℤ) = r_mod := Int.toNat_of_nonneg hr_lo
    have h_ind : ∀ m ∈ Finset.range h,
        ((⌊(x - m) / h⌋ - ⌊(x - m - 1) / h⌋ : ℤ) : ℝ) = if m = m₀ then 1 else 0 := by
      intro m hm
      have hm_lt : m < h := Finset.mem_range.mp hm
      set q : ℤ := ⌊x⌋ / (h : ℤ)
      have hdiv : ⌊x⌋ = q * (h : ℤ) + r_mod := (Int.ediv_add_emod ⌊x⌋ h).symm.trans (by rw [mul_comm])
      have hx_lo : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      have hx_lt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
      have hh_pos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
      by_cases hmm0 : m = m₀
      · subst hmm0
        have hfl1 : ⌊(x - m₀) / h⌋ = q := by
          rw [Int.floor_eq_iff]; constructor
          · rw [le_div_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) - r_mod = (q : ℝ) * h := by rw [hdiv]; push_cast; ring
            linarith [show (m₀ : ℝ) = (r_mod : ℝ) by exact_mod_cast hm₀_eq]
          · rw [div_lt_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) + 1 - r_mod = (q : ℝ) * h + 1 := by rw [hdiv]; push_cast; ring
            have h1 : x - m₀ < (q : ℝ) * h + 1 := by linarith [show (m₀ : ℝ) = (r_mod : ℝ) by exact_mod_cast hm₀_eq]
            have : (1 : ℝ) ≤ h := by exact_mod_cast (by omega : 1 ≤ h)
            push_cast; linarith
        have hfl2 : ⌊(x - m₀ - 1) / h⌋ = q - 1 := by
          rw [Int.floor_eq_iff]; constructor
          · rw [le_div_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) - r_mod = (q : ℝ) * h := by rw [hdiv]; push_cast; ring
            have : (1 : ℝ) ≤ h := by exact_mod_cast (by omega : 1 ≤ h)
            push_cast; linarith [show (m₀ : ℝ) = (r_mod : ℝ) by exact_mod_cast hm₀_eq]
          · rw [div_lt_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) + 1 - r_mod = (q : ℝ) * h + 1 := by rw [hdiv]; push_cast; ring
            push_cast; linarith [show (m₀ : ℝ) = (r_mod : ℝ) by exact_mod_cast hm₀_eq]
        rw [if_pos rfl, hfl1, hfl2]; push_cast; ring
      · rw [if_neg hmm0]
        rcases lt_or_gt_of_ne hmm0 with hlt | hgt
        · have hm1_le_r : (m : ℝ) + 1 ≤ (r_mod : ℝ) := by
            have : (m : ℤ) + 1 ≤ r_mod := by rw [← hm₀_eq]; exact_mod_cast hlt
            exact_mod_cast this
          have hfl1 : ⌊(x - m) / h⌋ = q := by
            rw [Int.floor_eq_iff]; constructor
            · rw [le_div_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) - r_mod = (q : ℝ) * h := by rw [hdiv]; push_cast; ring
              linarith
            · rw [div_lt_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) + 1 - r_mod = (q : ℝ) * h + 1 := by rw [hdiv]; push_cast; ring
              have : (r_mod : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast (by omega : r_mod + 1 ≤ h)
              push_cast; linarith
          have hfl2 : ⌊(x - m - 1) / h⌋ = q := by
            rw [Int.floor_eq_iff]; constructor
            · rw [le_div_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) - r_mod = (q : ℝ) * h := by rw [hdiv]; push_cast; ring
              linarith
            · rw [div_lt_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) + 1 - r_mod = (q : ℝ) * h + 1 := by rw [hdiv]; push_cast; ring
              have : (r_mod : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast (by omega : r_mod + 1 ≤ h)
              push_cast; linarith
          rw [hfl1, hfl2, sub_self]; simp
        · have hr1_le_m : (r_mod : ℝ) + 1 ≤ (m : ℝ) := by
            have : r_mod + 1 ≤ (m : ℤ) := by rw [← hm₀_eq]; exact_mod_cast hgt
            exact_mod_cast this
          have hfl1 : ⌊(x - m) / h⌋ = q - 1 := by
            rw [Int.floor_eq_iff]; constructor
            · rw [le_div_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) - r_mod = (q : ℝ) * h := by rw [hdiv]; push_cast; ring
              have : (m : ℝ) + 1 ≤ h := by exact_mod_cast hm_lt
              push_cast; linarith
            · rw [div_lt_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) + 1 - r_mod = (q : ℝ) * h + 1 := by rw [hdiv]; push_cast; ring
              push_cast; linarith
          have hfl2 : ⌊(x - m - 1) / h⌋ = q - 1 := by
            rw [Int.floor_eq_iff]; constructor
            · rw [le_div_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) - r_mod = (q : ℝ) * h := by rw [hdiv]; push_cast; ring
              have : (m : ℝ) + 1 ≤ h := by exact_mod_cast hm_lt
              push_cast; linarith
            · rw [div_lt_iff₀ hh_pos]; have : (⌊x⌋ : ℝ) + 1 - r_mod = (q : ℝ) * h + 1 := by rw [hdiv]; push_cast; ring
              push_cast; linarith
          rw [hfl1, hfl2, sub_self]; simp
    have he_eq : ePhase ((t : ℝ) * (⌊x⌋ : ℝ) / h) =
        ∑ m ∈ Finset.range h, w_m m * (((⌊(x - m) / h⌋ - ⌊(x - m - 1) / h⌋ : ℤ) : ℝ) : ℂ) := by
      have hsum : ∑ m ∈ Finset.range h, w_m m * (((⌊(x - m) / h⌋ - ⌊(x - m - 1) / h⌋ : ℤ) : ℝ) : ℂ) = w_m m₀ := by
        calc ∑ m ∈ Finset.range h, w_m m * (((⌊(x - m) / h⌋ - ⌊(x - m - 1) / h⌋ : ℤ) : ℝ) : ℂ)
            = ∑ m ∈ Finset.range h, if m = m₀ then w_m m else 0 := by
              refine Finset.sum_congr rfl fun m hm => ?_; rw [h_ind m hm]; split_ifs <;> simp
          _ = w_m m₀ := Finset.sum_ite_eq' (Finset.range h) m₀ w_m |>.trans (if_pos hm₀_range)
      rw [hsum]
      set q : ℤ := ⌊x⌋ / (h : ℤ)
      have hdiv : ⌊x⌋ = q * (h : ℤ) + r_mod := (Int.ediv_add_emod ⌊x⌋ h).symm.trans (by rw [mul_comm])
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
      have heq_arg : (t : ℝ) * (⌊x⌋ : ℝ) / h = ((t : ℤ) * q : ℤ) + (t : ℝ) * (m₀ : ℝ) / h := by
        have h1 : (⌊x⌋ : ℝ) = (q : ℝ) * h + (m₀ : ℝ) := by rw [hdiv, ← hm₀_eq]; push_cast; ring
        rw [h1]; push_cast; field_simp [hh0]; ring
      rw [heq_arg, ePhase_add', ePhase_int', one_mul]
    rw [he_eq]; simp only [Ψm, ← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [← mul_sub, norm_mul, show ‖w_m m‖ = 1 from norm_ePhase _, one_mul]
    have hdiff_R : (((⌊(x - m) / h⌋ - ⌊(x - m - 1) / h⌋ : ℤ) : ℝ) : ℂ) -
        ((1 / (h : ℝ) + Ψ ((x - m - 1) / h) - Ψ ((x - m) / h) : ℝ) : ℂ) =
        (((((x - m - 1) / h - (⌊(x - m - 1) / h⌋ : ℝ) - 1 / 2 - Ψ ((x - m - 1) / h)) -
          ((x - m) / h - (⌊(x - m) / h⌋ : ℝ) - 1 / 2 - Ψ ((x - m) / h))) : ℝ) : ℂ) := by
      push_cast; field_simp [(by exact_mod_cast (by omega : h ≠ 0) : (h : ℝ) ≠ 0)]; ring
    rw [hdiff_R, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (abs_sub _ _) (add_le_add (happrox _) (happrox _))
  · intro x
    have hB_bd : ∀ u : ℝ, B u ≤ 3 / 2 := by
      intro u
      have h1 : (B u : ℂ) = ∑ k ∈ Finset.Icc (-(H : ℤ)) H, b k * ePhase ((k : ℝ) * u) := hB u
      have h2 : |B u| ≤ ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ‖b k‖ := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => by rw [norm_mul, norm_ePhase, mul_one])
      have hcard : ((Finset.Icc (-(H : ℤ)) H).card : ℝ) = 2 * (H : ℝ) + 1 := by rw [Int.card_Icc]; push_cast; ring
      have h3 : ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ‖b k‖ ≤ (2 * (H : ℝ) + 1) * (1 / (2 * (H : ℝ) + 2)) := by
        calc ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ‖b k‖
            ≤ ∑ _k ∈ Finset.Icc (-(H : ℤ)) H, (1 / (2 * (H : ℝ) + 2)) := Finset.sum_le_sum fun k _ => hb_bd k
          _ = (2 * (H : ℝ) + 1) * (1 / (2 * (H : ℝ) + 2)) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
      have h4 : (2 * (H : ℝ) + 1) * (1 / (2 * (H : ℝ) + 2)) ≤ 3 / 2 := by
        rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]
        linarith [show (1 : ℝ) ≤ H by exact_mod_cast hH]
      exact (abs_le.mp (le_trans h2 (le_trans h3 h4))).2
    have hΨ_bd : ∀ u : ℝ, |Ψ u| ≤ 2 := by
      intro u
      have h1 : |u - (⌊u⌋ : ℝ) - 1 / 2| ≤ 1 / 2 := by
        have hfl := Int.floor_le u; have hlt := Int.lt_floor_add_one u
        rw [abs_le]; constructor <;> linarith
      have h2 := happrox u
      have h3 : |Ψ u| ≤ |u - (⌊u⌋ : ℝ) - 1 / 2| + B u := by
        have := abs_sub_le (Ψ u) (u - (⌊u⌋ : ℝ) - 1 / 2) 0
        linarith [abs_sub_comm (u - (⌊u⌋ : ℝ) - 1 / 2) (Ψ u)]
      linarith [hB_bd u]
    calc ‖Ψm x‖ ≤ ∑ m ∈ Finset.range h, ‖w_m m * ((1 / (h : ℝ) + Ψ ((x - m - 1) / h) - Ψ ((x - m) / h) : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.range h, (1 / (h : ℝ) + 4) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [norm_mul, show ‖w_m m‖ = 1 from norm_ePhase _, one_mul, Complex.norm_real, Real.norm_eq_abs]
          have h1 : |1 / (h : ℝ) + Ψ ((x - m - 1) / h) - Ψ ((x - m) / h)| ≤
              |1 / (h : ℝ)| + |Ψ ((x - m - 1) / h)| + |Ψ ((x - m) / h)| := by
            linarith [abs_add_le (1 / (h : ℝ)) (Ψ ((x - m - 1) / h)), abs_sub (1 / (h : ℝ) + Ψ ((x - m - 1) / h)) (Ψ ((x - m) / h))]
          rw [abs_of_nonneg (by positivity)] at h1
          linarith [hΨ_bd ((x - m - 1) / h), hΨ_bd ((x - m) / h)]
      _ = (h : ℝ) * (1 / (h : ℝ) + 4) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 1 + 4 * (h : ℝ) := by field_simp [(by exact_mod_cast (by omega : h ≠ 0) : (h : ℝ) ≠ 0)]; ring
  · have h_abs : ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), ‖cm k‖ ≤
        (h : ℝ) / Real.pi * ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), (|(k : ℝ)|)⁻¹ := by
      rw [Finset.mul_sum]; refine Finset.sum_le_sum fun k hk => ?_
      have hk0 := (Finset.mem_filter.mp hk).2
      have hk_bd : ‖cm k‖ ≤ (h : ℝ) / (Real.pi * |(k : ℝ)|) := by
        rw [cm, norm_mul]; have hc1 := hc_bd k hk0
        have hc2 : ‖coeff_sum_c k‖ ≤ 2 * (h : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          calc ∑ m ∈ Finset.range h, ‖w_m m * (ePhase (-(k : ℝ) * (m + 1 : ℝ) / h) - ePhase (-(k : ℝ) * (m : ℝ) / h))‖
              ≤ ∑ _m ∈ Finset.range h, (2 : ℝ) := Finset.sum_le_sum fun m _ => by
                rw [norm_mul, norm_ePhase, one_mul]; exact le_trans (norm_sub_le _ _) (by rw [norm_ePhase, norm_ePhase]; norm_num)
            _ = 2 * (h : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        calc ‖c k‖ * ‖coeff_sum_c k‖ ≤ (1 / (2 * Real.pi * |(k : ℝ)|)) * (2 * (h : ℝ)) := mul_le_mul hc1 hc2 (norm_nonneg _) (by positivity)
          _ = (h : ℝ) / (Real.pi * |(k : ℝ)|) := by field_simp [Real.pi_ne_zero]; ring
      simpa [div_eq_mul_inv, mul_assoc] using hk_bd
    have h_symm : ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), (|(k : ℝ)|)⁻¹ = 2 * ∑ k ∈ Finset.Icc 1 H, (k : ℝ)⁻¹ := by
      have h_eq : (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0) =
          (Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ)) ∪ (Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ)) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨⟨hk1, hk2⟩, hk0⟩; rcases lt_or_gt_of_ne hk0 with hneg | hpos
          · right; exact ⟨(-k).toNat, ⟨by omega, by omega⟩, by omega⟩
          · left; exact ⟨k.toNat, ⟨by omega, by omega⟩, by omega⟩
        · rintro (⟨m, ⟨hm1, hm2⟩, rfl⟩ | ⟨m, ⟨hm1, hm2⟩, rfl⟩) <;> refine ⟨⟨by omega, by omega⟩, by omega⟩
      have hdisj : Disjoint ((Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ))) ((Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ))) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [Finset.mem_image, Finset.mem_Icc] at hk1 hk2; omega
      rw [h_eq, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => by omega), Finset.sum_image (fun a _ b _ h => by omega)]
      have h1 : ∑ x ∈ Finset.Icc 1 H, (|((x : ℤ) : ℝ)|)⁻¹ = ∑ x ∈ Finset.Icc 1 H, (x : ℝ)⁻¹ :=
        Finset.sum_congr rfl fun x _ => by simp [abs_of_nonneg (Nat.cast_nonneg x)]
      have h2 : ∑ x ∈ Finset.Icc 1 H, (|(-(x : ℤ) : ℝ)|)⁻¹ = ∑ x ∈ Finset.Icc 1 H, (x : ℝ)⁻¹ :=
        Finset.sum_congr rfl fun x _ => by simp [abs_neg, abs_of_nonneg (Nat.cast_nonneg x)]
      rw [h1, h2, two_mul]
    have h_harm : ∑ k ∈ Finset.Icc 1 H, (k : ℝ)⁻¹ ≤ Real.log (H : ℝ) + 1 := by
      have h1 : ∑ k ∈ Finset.Icc 1 H, (k : ℝ)⁻¹ = 1 + ∑ k ∈ Finset.Icc 2 H, (k : ℝ)⁻¹ := by
        have hu : Finset.Icc 1 H = insert 1 (Finset.Icc 2 H) := by ext k; simp [Finset.mem_Icc]; omega
        rw [hu, Finset.sum_insert (by simp)]; norm_num
      rw [h1]
      have h2 : ∑ k ∈ Finset.Icc 2 H, (k : ℝ)⁻¹ ≤ ∫ t in (1 : ℝ)..(H : ℝ), t⁻¹ := by
        have h_int : ∀ k ∈ Finset.Icc 2 H, ((k : ℝ)⁻¹) ≤ ∫ t in ((k : ℝ) - 1)..(k : ℝ), t⁻¹ := by
          intro k hk; have hk2 := (Finset.mem_Icc.mp hk).1
          calc ((k : ℝ)⁻¹) = ∫ _t in ((k : ℝ) - 1)..(k : ℝ), (k : ℝ)⁻¹ := by simp
            _ ≤ ∫ t in ((k : ℝ) - 1)..(k : ℝ), t⁻¹ := by
                refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const ?_ ?_
                · exact ContinuousOn.intervalIntegrable (fun t ht => by
                    have ht' : t ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ) := by simpa [Set.uIcc_of_le (by linarith : (k : ℝ) - 1 ≤ k)] using ht
                    exact (continuousAt_inv₀ (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2; linarith [ht'.1])).continuousWithinAt)
                · intro t ht; exact inv_anti₀ (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2; linarith [ht.1]) ht.2
        have h_sum_int : ∑ k ∈ Finset.Icc 2 H, ∫ t in ((k : ℝ) - 1)..(k : ℝ), t⁻¹ = ∫ t in (1 : ℝ)..(H : ℝ), t⁻¹ := by
          clear h1 h_abs h_symm; induction H with
          | zero => simp
          | succ m ih =>
            by_cases hm1 : m = 0
            · subst hm1; simp
            · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]; push_cast
              rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring]
              refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
              · exact ContinuousOn.intervalIntegrable (fun t ht => by
                  have ht' : t ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le (by exact_mod_cast (by omega : 1 ≤ m) : (1 : ℝ) ≤ m)] using ht
                  exact (continuousAt_inv₀ (by linarith [ht'.1])).continuousWithinAt)
              · exact ContinuousOn.intervalIntegrable (fun t ht => by
                  have ht' : t ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := by simpa [Set.uIcc_of_le (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)] using ht
                  exact (continuousAt_inv₀ (by have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m); linarith [ht'.1])).continuousWithinAt)
        rw [← h_sum_int]; exact Finset.sum_le_sum h_int
      rw [integral_inv_of_pos (by norm_num) (by exact_mod_cast hH)] at h2; simp only [div_one] at h2; linarith
    calc ∑ k ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0), ‖cm k‖
        ≤ (h : ℝ) / Real.pi * (2 * ∑ k ∈ Finset.Icc 1 H, (k : ℝ)⁻¹) := h_symm ▸ h_abs
      _ ≤ (h : ℝ) / Real.pi * (2 * (Real.log (H : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_harm (by norm_num)) (by positivity)
      _ = (2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1) := by ring

theorem theorem_2_5_iii (h : ℕ) (hh : 2 ≤ h) (c : ZMod h) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IsLittleOAtTop
      (fun n =>
        (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
            (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
          (padicValNat p n.factorial : ℝ) * Real.log p) -
        ((b - a) / (h : ℝ)) * (n : ℝ) * Real.log n)
      (fun n => (n : ℝ) * Real.log n) := by
  rw [isLittleOAtTop_iff]
  intro ε hε
  obtain ⟨C_m, hC_m, _, hm_bd⟩ := mertens_first_theorem
  obtain ⟨C_m2, hC_m2, hm2_bd⟩ := sum_Icc_div_p_log_p_le
  obtain ⟨c₁, C_pnt, hc₁, hC_pnt, hpnt⟩ := deLaValleePoussin_pnt
  set δ : ℝ := min (ε / (16 * (h : ℝ))) (1 / 3)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 3 := min_le_right _ _
  let R : ℕ := ⌊1 / δ⌋₊
  let AR : ℕ := 6 * R + 30
  have hR3 : 3 ≤ R := by
    have h3 : (3 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    exact Nat.le_floor h3
  obtain ⟨η'_δ, C_δ, C'_δ, hη'_pos, hC_δ, hC'_δ, N_mod, hN_mod, h24mod⟩ := lemma_2_4_i_mod h (by omega) δ hδ0 hδ1
  have h_t0_o : IsLittleOAtTop
      (fun n => (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
        (padicValNat p n.factorial : ℝ) * Real.log p) - (b - a) * (n : ℝ) * Real.log n)
      (fun n => (n : ℝ) * Real.log n) := by
    rw [isLittleOAtTop_iff]
    intro η hη
    have h_ev0 : ∀ᶠ n : ℕ in atTop,
        4 ≤ n ∧ 2 ≤ Real.log n ∧ 2 ≤ (n : ℝ) ^ b ∧
        (if a = 0 then True else 2 ≤ (n : ℝ) ^ a) ∧
        (4 * Real.log ((Real.log n) ^ 2) + 4 * C_m + 2 * Real.log 4 + 8) / Real.log n ≤ η := by
      have ha1 := eventually_ge_atTop 4
      have ha2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      have ha3 := ((tendsto_rpow_atTop (by linarith : 0 < b)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      have ha4 : ∀ᶠ n : ℕ in atTop, if a = 0 then True else 2 ≤ (n : ℝ) ^ a := by
        by_cases ha0 : a = 0
        · simp [ha0]
        · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          filter_upwards [((tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2] with n hn
          simp [ha0, hn]
      have ha5 : Tendsto (fun n : ℕ => (4 * Real.log ((Real.log n) ^ 2) + 4 * C_m + 2 * Real.log 4 + 8) / Real.log n) atTop (𝓝 0) := by
        have h0 : Tendsto (fun u : ℝ => (8 * Real.log u + (4 * C_m + 2 * Real.log 4 + 8)) / u) atTop (𝓝 0) := by
          have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
          have h2 := tendsto_const_nhds.div_atTop tendsto_id (a := 4 * C_m + 2 * Real.log 4 + 8)
          simpa [add_div] using (h1.const_mul 8).add h2
        refine (h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr' ?_
        filter_upwards [eventually_ge_atTop 3] with n hn3
        dsimp only [Function.comp_def]
        rw [Real.log_pow]; push_cast; ring
      filter_upwards [ha1, ha2, ha3, ha4, ha5.eventually (le_mem_nhds hη)] with n a1 a2 a3 a4 a5
      exact ⟨a1, a2, a3, a4, a5⟩
    filter_upwards [h_ev0] with n ⟨hn4, hlog2, hnb2, hna2, hbd_eta⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log n := by linarith
    rw [abs_of_pos (mul_pos hn_pos hlog_pos)]
    set M_cut : ℕ := ⌊(Real.log n) ^ 2⌋₊
    have hM_ge2 : 2 ≤ M_cut := Nat.le_floor (by nlinarith)
    have h_vp_diff :
        |∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
            ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p| ≤
        (4 * Real.log ((Real.log n) ^ 2) + 2 * C_m + 2 * Real.log 4 + 8) * (n : ℝ) := by
      have h_split : (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime =
          ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut) ∪
          ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·) := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter]; omega
      have hdisj : Disjoint
          (((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut))
          (((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·)) := by
        rw [Finset.disjoint_left]; intro p hp1 hp2; simp only [Finset.mem_filter] at hp1 hp2; omega
      rw [h_split, Finset.sum_union hdisj]
      refine le_trans (abs_add_le _ _) ?_
      have h_lo :
          |∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut),
            ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p| ≤
          (4 * Real.log ((Real.log n) ^ 2) + 2 * C_m) * (n : ℝ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have h1 : ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut),
              |((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p| ≤
            ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut),
              (2 * (n : ℝ) / p) * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
          rw [abs_mul, abs_of_nonneg hlog_nn]
          refine mul_le_mul_of_nonneg_right ?_ hlog_nn
          have hvp_bd := padicValNat_factorial_upper_rpow (n := n) hp_prime
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
          rw [abs_le]; constructor <;> linarith [div_nonneg hn_pos.le hp_pos.le]
        have h2 : ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut),
              (2 * (n : ℝ) / p) * Real.log p ≤
            ∑ p ∈ (Finset.Icc 2 M_cut).filter Nat.Prime, (2 * (n : ℝ) / p) * Real.log p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢; exact ⟨⟨hp.1.2.two_le, hp.2⟩, hp.1.2⟩
          · intro p hp _; have := (Finset.mem_filter.mp hp).2; positivity
        calc ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (· ≤ M_cut),
              |((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p|
            ≤ ∑ p ∈ (Finset.Icc 2 M_cut).filter Nat.Prime, (2 * (n : ℝ) / p) * Real.log p := le_trans h1 h2
          _ = 2 * (n : ℝ) * ∑ p ∈ (Finset.Icc 2 M_cut).filter Nat.Prime, Real.log p / p := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
          _ ≤ 2 * (n : ℝ) * (Real.log ((Real.log n) ^ 2) + C_m) := by
              have hm := abs_le.mp (hm_bd ((Real.log n) ^ 2) (by nlinarith))
              exact mul_le_mul_of_nonneg_left (by linarith [hm.2]) (by positivity)
          _ ≤ (4 * Real.log ((Real.log n) ^ 2) + 2 * C_m) * (n : ℝ) := by
              have hnn : 0 ≤ Real.log ((Real.log n) ^ 2) := Real.log_nonneg (by nlinarith)
              nlinarith
      have h_hi :
          |∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
            ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p| ≤
          (2 * Real.log 4 + 8) * (n : ℝ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have h_term : ∀ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
            |((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p| ≤
            Real.log p + (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log n := by
          intro p hp
          have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
          have hp_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
          have hp_le_n : p ≤ n := by
            have hnb_le : ⌊(n : ℝ) ^ b⌋₊ ≤ n := by
              rw [← Nat.floor_natCast (n := n) (α := ℝ)]
              exact Nat.floor_mono (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hb)
            omega
          have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
          have hlog_le : Real.log p ≤ Real.log n := Real.log_le_log hp_pos (by exact_mod_cast hp_le_n)
          have h_vp_lo : (n : ℝ) / p - 1 ≤ (padicValNat p n.factorial : ℝ) := by
            have h1 : (n : ℝ) / p - 1 < ((n / p : ℕ) : ℝ) := by
              have := Int.lt_floor_add_one ((n : ℝ) / p)
              have hfl : ((n / p : ℕ) : ℝ) = (⌊(n : ℝ) / p⌋ : ℝ) := by
                have := Int.floor_div_natCast (n : ℤ) p; simp at this; exact_mod_cast this.symm
              linarith
            have h2 : n / p ≤ padicValNat p n.factorial := by
              haveI : Fact p.Prime := ⟨hp_prime⟩
              have h_ge := Nat.le_of_dvd (Nat.factorial_pos n) (by exact dvd_refl n.factorial)
              have hlt : n < p ^ (n + 1) := lt_of_lt_of_le (Nat.lt_pow_self hp_prime.one_lt)
                (Nat.pow_le_pow_right hp_prime.pos (by omega))
              rw [padicValNat_factorial_eq_sum_floor hp_prime hlt]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩)
            linarith [show ((n / p : ℕ) : ℝ) ≤ (padicValNat p n.factorial : ℝ) by exact_mod_cast h2]
          have h_vp_hi : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / p + 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
            have h1 : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
              haveI : Fact p.Prime := ⟨hp_prime⟩
              have hleg := sub_one_mul_padicValNat_factorial (p := p) n
              have hle : (p - 1) * padicValNat p n.factorial ≤ n := by nlinarith
              rw [le_div_iff₀ (by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le; linarith)]
              exact_mod_cast (by nlinarith : padicValNat p n.factorial * (p - 1) ≤ n)
            have h2 : (n : ℝ) / ((p : ℝ) - 1) - (n : ℝ) / p = (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
              have hp1 : (p : ℝ) - 1 ≠ 0 := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le; linarith
              field_simp [hp_pos.ne', hp1]; ring
            have h3 : (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
              have hp2 : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le; linarith
              rw [div_le_div_iff₀ (by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le; positivity) (pow_pos hp_pos 2)]
              nlinarith [hn_pos.le]
            linarith
          rw [abs_mul, abs_of_nonneg hlog_nn]
          have h_abs_vp : |(padicValNat p n.factorial : ℝ) - (n : ℝ) / p| ≤ 1 + 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
            rw [abs_le]; constructor <;> linarith [show 0 ≤ 2 * (n : ℝ) / (p : ℝ) ^ 2 by positivity]
          calc |(padicValNat p n.factorial : ℝ) - (n : ℝ) / p| * Real.log p
              ≤ (1 + 2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log p := mul_le_mul_of_nonneg_right h_abs_vp hlog_nn
            _ = Real.log p + (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log p := by ring
            _ ≤ Real.log p + (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log n :=
                add_le_add_left (mul_le_mul_of_nonneg_left hlog_le (by positivity)) _
        have h_sum1 : ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·), Real.log p ≤
            2 * Real.log 4 * (n : ℝ) := by
          have hth : ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·), Real.log p ≤
              Chebyshev.theta (n : ℝ) := by
            unfold Chebyshev.theta; rw [Nat.floor_natCast]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
              Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
            intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
            have hnb_le : ⌊(n : ℝ) ^ b⌋₊ ≤ n := by
              rw [← Nat.floor_natCast (n := n) (α := ℝ)]
              exact Nat.floor_mono (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hb)
            exact ⟨⟨hp.1.2.pos, le_trans hp.1.1.2 hnb_le⟩, hp.1.2⟩
          linarith [Chebyshev.theta_le_log4_mul_x hn_pos.le]
        have h_sum2 : ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
              (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log n ≤
            8 * (n : ℝ) := by
          have h_sub : ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·) ⊆
              Finset.Icc (M_cut + 1) (max n M_cut) := by
            intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
            have hnb_le : ⌊(n : ℝ) ^ b⌋₊ ≤ n := by
              rw [← Nat.floor_natCast (n := n) (α := ℝ)]
              exact Nat.floor_mono (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hb)
            exact ⟨hp.2, le_trans (le_trans hp.1.1.2 hnb_le) (le_max_left _ _)⟩
          have h_inv_sq : ∑ k ∈ Finset.Icc (M_cut + 1) (max n M_cut), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (M_cut : ℝ) := by
            have h_tele : ∀ k ∈ Finset.Icc (M_cut + 1) (max n M_cut),
                (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
              intro k hk; have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : 2 ≤ k)
              have hk1 : 0 < (k : ℝ) - 1 := by linarith
              have hk0 : (0 : ℝ) < k := by linarith
              rw [one_div_sub_one_div hk1.ne' hk0.ne', div_le_div_iff₀ (pow_pos hk0 2) (mul_pos hk1 hk0)]
              nlinarith
            calc ∑ k ∈ Finset.Icc (M_cut + 1) (max n M_cut), (1 : ℝ) / (k : ℝ) ^ 2
                ≤ ∑ k ∈ Finset.Icc (M_cut + 1) (max n M_cut), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := Finset.sum_le_sum h_tele
              _ ≤ 1 / (M_cut : ℝ) := by
                  have h_sum_t : ∀ A B : ℕ, 1 ≤ A → A ≤ B →
                      ∑ k ∈ Finset.Icc (A + 1) B, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 / (A : ℝ) - 1 / (B : ℝ) := by
                    intro A B hA hAB; induction B with
                    | zero => omega
                    | succ m ih =>
                      by_cases hm : A = m + 1
                      · subst hm; simp
                      · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]; push_cast; ring
                  by_cases h_le : M_cut + 1 ≤ max n M_cut
                  · rw [h_sum_t M_cut (max n M_cut) (by omega) (by omega)]
                    linarith [show (0 : ℝ) ≤ 1 / ((max n M_cut : ℕ) : ℝ) by positivity]
                  · have h_emp : Finset.Icc (M_cut + 1) (max n M_cut) = ∅ := Finset.Icc_eq_empty (by omega)
                    rw [h_emp, Finset.sum_empty]; positivity
          have h_M_inv : 1 / (M_cut : ℝ) ≤ 2 / (Real.log n) ^ 2 := by
            have hM1 : (Real.log n) ^ 2 ≤ 2 * (M_cut : ℝ) := by
              have h1 : (Real.log n) ^ 2 < (M_cut : ℝ) + 1 := Nat.lt_floor_add_one _
              have h2 : (1 : ℝ) ≤ M_cut := by exact_mod_cast (by omega : 1 ≤ M_cut)
              linarith
            rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < M_cut)) (pow_pos hlog_pos 2)]
            linarith
          calc ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
                (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log n
              = ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
                  (2 * (n : ℝ) * Real.log n) * ((1 : ℝ) / (p : ℝ) ^ 2) :=
                Finset.sum_congr rfl fun p _ => by ring
            _ ≤ ∑ k ∈ Finset.Icc (M_cut + 1) (max n M_cut), (2 * (n : ℝ) * Real.log n) * ((1 : ℝ) / (k : ℝ) ^ 2) :=
                Finset.sum_le_sum_of_subset_of_nonneg h_sub fun k _ _ => by positivity
            _ ≤ (2 * (n : ℝ) * Real.log n) * (2 / (Real.log n) ^ 2) := by
                rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (le_trans h_inv_sq h_M_inv) (by positivity)
            _ = 4 * (n : ℝ) / Real.log n := by field_simp [hlog_pos.ne']; ring
            _ ≤ 8 * (n : ℝ) := by
                have : 4 * (n : ℝ) / Real.log n ≤ 4 * (n : ℝ) := div_le_self (by positivity) (by linarith)
                linarith
        calc |∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
              ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p|
            ≤ ∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
                (Real.log p + (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log n) :=
              le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_term)
          _ = (∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·), Real.log p) +
              (∑ p ∈ ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter (M_cut < ·),
                (2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log n) := Finset.sum_add_distrib
          _ ≤ (2 * Real.log 4 + 8) * (n : ℝ) := by linarith [h_sum1, h_sum2]
      linarith
    have h_mertens_diff :
        |((n : ℝ) * ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) -
          (b - a) * (n : ℝ) * Real.log n| ≤ 2 * C_m * (n : ℝ) := by
      have hsub_le : (n : ℝ) ^ a ≤ (n : ℝ) ^ b :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hab.le
      have hsum_eq :
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p =
          (∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) -
          (if a = 0 then 0 else ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ a⌋₊).filter Nat.Prime, Real.log p / p) := by
        by_cases ha0 : a = 0
        · subst ha0; simp
        · rw [if_neg ha0]
          have h2_le : 2 ≤ ⌊(n : ℝ) ^ a⌋₊ := by simp only [ha0, ↓reduceIte] at hna2; exact Nat.le_floor hna2
          have hsub : (Finset.Icc 2 ⌊(n : ℝ) ^ a⌋₊).filter Nat.Prime ⊆ (Finset.Icc 2 ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime := by
            intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
            exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono hsub_le)⟩, hp.2⟩
          have hsdiff : (Finset.Icc 2 ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime \ (Finset.Icc 2 ⌊(n : ℝ) ^ a⌋₊).filter Nat.Prime =
              (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime := by
            ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]; omega
          rw [← hsdiff, Finset.sum_sdiff hsub]; ring
      have hdiff_log :
          |(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) -
            (b - a) * Real.log n| ≤ 2 * C_m := by
        rw [hsum_eq]
        have hmB := hm_bd ((n : ℝ) ^ b) hnb2
        have hlogB : Real.log ((n : ℝ) ^ b) = b * Real.log n := Real.log_rpow hn_pos b
        by_cases ha0 : a = 0
        · subst ha0; simp only [↓reduceIte, sub_zero] at hmB ⊢
          rw [hlogB] at hmB; linarith [abs_le.mp hmB, hC_m]
        · rw [if_neg ha0]; simp only [ha0, ↓reduceIte] at hna2
          have hmA := hm_bd ((n : ℝ) ^ a) hna2
          have hlogA : Real.log ((n : ℝ) ^ a) = a * Real.log n := Real.log_rpow hn_pos a
          rw [hlogB] at hmB; rw [hlogA] at hmA
          have h1 : ((∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) -
                (∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ a⌋₊).filter Nat.Prime, Real.log p / p)) - (b - a) * Real.log n =
              ((∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) - b * Real.log n) -
              ((∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ a⌋₊).filter Nat.Prime, Real.log p / p) - a * Real.log n) := by ring
          rw [h1]; exact le_trans (abs_sub _ _) (by linarith)
      rw [show (n : ℝ) * ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p -
            (b - a) * (n : ℝ) * Real.log n =
          (n : ℝ) * ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) -
            (b - a) * Real.log n) by ring, abs_mul, abs_of_pos hn_pos]
      exact mul_le_mul_of_nonneg_left hdiff_log hn_pos.le
    have hsplit_main :
        (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial : ℝ) * Real.log p) - (b - a) * (n : ℝ) * Real.log n =
        (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p) +
        ((n : ℝ) * (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p) -
          (b - a) * (n : ℝ) * Real.log n) := by
      have h1 : (n : ℝ) * ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, Real.log p / p =
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime, ((n : ℝ) / p) * Real.log p := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      rw [h1, ← Finset.sum_add_distrib]
      have h2 : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
            (((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * Real.log p + ((n : ℝ) / p) * Real.log p) =
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
            (padicValNat p n.factorial : ℝ) * Real.log p := by
        refine Finset.sum_congr rfl fun p _ => by ring
      rw [h2]; ring
    have h_abs_tot : |(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial : ℝ) * Real.log p) - (b - a) * (n : ℝ) * Real.log n| ≤
        (4 * Real.log ((Real.log n) ^ 2) + 4 * C_m + 2 * Real.log 4 + 8) * (n : ℝ) := by
      rw [hsplit_main]; exact le_trans (abs_add_le _ _) (by linarith [h_vp_diff, h_mertens_diff])
    have hbd' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hlog_pos).mp hbd_eta) hn_pos.le
    rw [div_mul_cancel₀ _ hlog_pos.ne'] at hbd'
    linarith
  have h_t_nonzero : ∀ t ∈ Finset.Icc 1 (h - 1),
      ∀ᶠ n : ℕ in atTop,
        ‖∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial * Real.log p : ℂ) *
            ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
        (ε / 2) * ((n : ℝ) * Real.log n) := by
    intro t ht
    have ht1 := (Finset.mem_Icc.mp ht).1
    have ht_lt : t < h := by have := (Finset.mem_Icc.mp ht).2; omega
    have h_ev_t : ∀ᶠ n : ℕ in atTop,
        N_mod ≤ n ∧ 16 ≤ n ∧ 2 ≤ Real.log n ∧ 2 ≤ (n : ℝ) ^ δ ∧
        1 ≤ ⌊(Real.log n) ^ (R + 2)⌋₊ ∧
        (n : ℝ) ^ δ ≤ (n : ℝ) / (Real.log n) ^ AR ∧
        (Real.log n) ^ AR ≤ (n : ℝ) ^ (1 / 2 : ℝ) ∧
        2 * C_m ≤ (ε / 16) * Real.log n ∧
        2 * Real.log 4 ≤ (ε / 16) * Real.log n ∧
        (n : ℝ) / (Real.log n) ^ AR ≥ 2 ∧
        (R : ℝ) * (2 * (Real.log (4 * (Real.log n) ^ AR + 4) + C_m2)) ≤ (ε / 16) * Real.log n ∧
        (Real.log ((Real.log n) ^ AR + 2) + 2 * Real.log 4 + 2 + 4 * Real.log 4 / (Real.log n) ^ AR) ≤ (ε / 16) * Real.log n ∧
        (2 * Real.log n) * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
            (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) * (2 * Real.log 4)) +
            ((2 * (h : ℝ) / Real.pi) * (Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) ^ R *
              C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) ≤ (ε / 16) * Real.log n ∧
        16 * (n : ℝ) ^ (1 - δ) ≤ (ε / 32) * (n : ℝ) ∧ 4 * Real.log 4 / (Real.log n) ^ AR ≤ ε / 32 := by
      have ha1 := (eventually_ge_atTop N_mod).and (eventually_ge_atTop 16)
      have ha2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      have ha3 := ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      have ha4 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ δ ≤ (n : ℝ) / (Real.log n) ^ AR := by
        have hpos : 0 < (1 - δ) / max (AR : ℝ) 1 := by positivity
        have hs : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 - δ) / max (AR : ℝ) 1)) atTop (𝓝 0) := by
          have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop hpos))
          refine (this.const_mul (max (AR : ℝ) 1 / (1 - δ))).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          dsimp only [Function.comp_def]; rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
        have hAR_pos : 0 < AR := by omega
        have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ AR / (n : ℝ) ^ (1 - δ)) atTop (𝓝 0) := by
          refine ((hs.pow AR).comp tendsto_natCast_atTop_atTop).congr' ?_
          filter_upwards [eventually_ge_atTop 1] with n hn1
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
          dsimp only [Function.comp_def]
          rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le]
          have heq : ((1 - δ) / max (AR : ℝ) 1) * (AR : ℝ) = 1 - δ := by
            have : max (AR : ℝ) 1 = AR := max_eq_left (by exact_mod_cast hAR_pos)
            rw [this]; field_simp [(by exact_mod_cast hAR_pos.ne' : (AR : ℝ) ≠ 0)]
          rw [heq]
        filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        have h1 : (Real.log n) ^ AR ≤ (n : ℝ) ^ (1 - δ) := (div_le_one (Real.rpow_pos_of_pos hn_pos _)).mp hn
        rw [le_div_iff₀ (by positivity)]
        calc (n : ℝ) ^ δ * (Real.log n) ^ AR ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (1 - δ) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (n : ℝ) := by rw [← Real.rpow_add hn_pos]; simp
      have ha5 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ AR ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        have hpos : 0 < (1 / 2 : ℝ) / max (AR : ℝ) 1 := by positivity
        have hs : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 / 2 : ℝ) / max (AR : ℝ) 1)) atTop (𝓝 0) := by
          have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ((Real.tendsto_log_atTop).comp (tendsto_rpow_atTop hpos))
          refine (this.const_mul (max (AR : ℝ) 1 / (1 / 2))).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          dsimp only [Function.comp_def]; rw [Real.log_rpow hx, Real.exp_neg, Real.exp_log (Real.rpow_pos_of_pos hx _)]; field_simp; ring
        have hAR_pos : 0 < AR := by omega
        have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ AR / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
          refine ((hs.pow AR).comp tendsto_natCast_atTop_atTop).congr' ?_
          filter_upwards [eventually_ge_atTop 1] with n hn1
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
          dsimp only [Function.comp_def]
          rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le]
          have heq : ((1 / 2 : ℝ) / max (AR : ℝ) 1) * (AR : ℝ) = 1 / 2 := by
            have : max (AR : ℝ) 1 = AR := max_eq_left (by exact_mod_cast hAR_pos)
            rw [this]; field_simp [(by exact_mod_cast hAR_pos.ne' : (AR : ℝ) ≠ 0)]
          rw [heq]
        filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
        exact (div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast hn1) _)).mp hn
      have ha6 := ((tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun n : ℕ => (2 * C_m + 2 * Real.log 4) / Real.log n) atTop (𝓝 0))).eventually (le_mem_nhds (by positivity : 0 < ε / 16))
      have ha7 : ∀ᶠ n : ℕ in atTop,
          (R : ℝ) * (2 * (Real.log (4 * (Real.log n) ^ AR + 4) + C_m2)) ≤ (ε / 16) * Real.log n ∧
          (Real.log ((Real.log n) ^ AR + 2) + 2 * Real.log 4 + 2 + 4 * Real.log 4 / (Real.log n) ^ AR) ≤ (ε / 16) * Real.log n ∧
          (2 * Real.log n) * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
              (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) * (2 * Real.log 4)) +
              ((2 * (h : ℝ) / Real.pi) * (Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) ^ R *
                C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) ≤ (ε / 16) * Real.log n ∧
          16 * (n : ℝ) ^ (1 - δ) ≤ (ε / 32) * (n : ℝ) ∧ 4 * Real.log 4 / (Real.log n) ^ AR ≤ ε / 32 := by
        have h_log_u : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
        have hb1 : Tendsto (fun u : ℝ => (R : ℝ) * (2 * (Real.log (4 * u ^ AR + 4) + C_m2)) / u) atTop (𝓝 0) := by
          have h_bd : ∀ᶠ u : ℝ in atTop,
              (R : ℝ) * (2 * (Real.log (4 * u ^ AR + 4) + C_m2)) / u ≤
              (R : ℝ) * 2 * ((AR + 1 : ℝ) * (Real.log u / u) + C_m2 / u) := by
            filter_upwards [eventually_ge_atTop (8 : ℝ)] with u hu
            have h1 : 4 * u ^ AR + 4 ≤ u ^ (AR + 1) := by
              have hup : 8 * u ^ AR ≤ u ^ (AR + 1) := by rw [pow_succ']; exact mul_le_mul_of_nonneg_right hu (by positivity)
              have hu1 : 1 ≤ u ^ AR := one_le_pow₀ (by linarith)
              linarith
            have h2 := Real.log_le_log (by positivity) h1
            rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h2
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            have : (R : ℝ) * (2 * (Real.log (4 * u ^ AR + 4) + C_m2)) * u ≤
                (R : ℝ) * (2 * ((AR + 1 : ℝ) * Real.log u + C_m2)) * u := by
              gcongr
            nlinarith [show (AR + 1 : ℝ) * (Real.log u / u) + C_m2 / u = ((AR + 1 : ℝ) * Real.log u + C_m2) / u by ring]
          refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu; positivity) h_bd ?_
          simpa using ((h_log_u.const_mul (AR + 1 : ℝ)).add (tendsto_const_nhds.div_atTop tendsto_id (a := C_m2))).const_mul ((R : ℝ) * 2)
        have hb2 : Tendsto (fun u : ℝ => (Real.log (u ^ AR + 2) + 2 * Real.log 4 + 2 + 4 * Real.log 4 / u ^ AR) / u) atTop (𝓝 0) := by
          have h_bd : ∀ᶠ u : ℝ in atTop,
              (Real.log (u ^ AR + 2) + 2 * Real.log 4 + 2 + 4 * Real.log 4 / u ^ AR) / u ≤
              (AR + 1 : ℝ) * (Real.log u / u) + (2 * Real.log 4 + 2 + 4 * Real.log 4) / u := by
            filter_upwards [eventually_ge_atTop (4 : ℝ)] with u hu
            have h1 : u ^ AR + 2 ≤ u ^ (AR + 1) := by
              have hup : 4 * u ^ AR ≤ u ^ (AR + 1) := by rw [pow_succ']; exact mul_le_mul_of_nonneg_right hu (by positivity)
              have hu1 : 1 ≤ u ^ AR := one_le_pow₀ (by linarith)
              linarith
            have h2 := Real.log_le_log (by positivity) h1
            rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h2
            have h3 : 4 * Real.log 4 / u ^ AR ≤ 4 * Real.log 4 := by
              exact div_le_self (by positivity) (one_le_pow₀ (by linarith))
            rw [div_le_iff₀ (by linarith)]
            have : (AR + 1 : ℝ) * (Real.log u / u) * u + (2 * Real.log 4 + 2 + 4 * Real.log 4) / u * u =
                (AR + 1 : ℝ) * Real.log u + (2 * Real.log 4 + 2 + 4 * Real.log 4) := by field_simp [(by linarith : u ≠ 0)]
            linarith [show ((AR + 1 : ℝ) * (Real.log u / u) + (2 * Real.log 4 + 2 + 4 * Real.log 4) / u) * u =
              (AR + 1 : ℝ) * (Real.log u / u) * u + (2 * Real.log 4 + 2 + 4 * Real.log 4) / u * u by ring]
          refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu; positivity) h_bd ?_
          simpa using (h_log_u.const_mul (AR + 1 : ℝ)).add (tendsto_const_nhds.div_atTop tendsto_id)
        have hb3 : ∀ᶠ n : ℕ in atTop,
            (2 * Real.log n) * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
              (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) * (2 * Real.log 4)) +
              ((2 * (h : ℝ) / Real.pi) * (Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) ^ R *
                C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) ≤ (ε / 16) * Real.log n := by
          have hlim3 : Tendsto (fun u : ℝ =>
              2 * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) * (4 * (h : ℝ) * C'_δ + (h : ℝ) * (2 * Real.log 4)) * u ^ (-(R + 2 : ℤ)) +
                ((2 * (h : ℝ) / Real.pi) * ((R + 2 : ℝ) * Real.log u + 1)) ^ R * C'_δ * u ^ (-(R + 2 : ℤ)))) atTop (𝓝 0) := by
            have ht1 : Tendsto (fun u : ℝ => u ^ (-(R + 2 : ℤ))) atTop (𝓝 0) := by
              simpa [Real.rpow_intCast] using tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < (R + 2 : ℕ))
            have ht2 : Tendsto (fun u : ℝ => ((2 * (h : ℝ) / Real.pi) * ((R + 2 : ℝ) * Real.log u + 1)) ^ R * C'_δ * u ^ (-(R + 2 : ℤ))) atTop (𝓝 0) := by
              have hs : Tendsto (fun u : ℝ => ((2 * (h : ℝ) / Real.pi) * ((R + 2 : ℝ) * Real.log u + 1)) / u) atTop (𝓝 0) := by
                have h1 := ((h_log_u.const_mul (R + 2 : ℝ)).add (tendsto_const_nhds.div_atTop tendsto_id (a := 1))).const_mul (2 * (h : ℝ) / Real.pi)
                simpa [mul_add, add_div, mul_div_assoc] using h1
              have hp := (hs.pow R).mul (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)) |>.const_mul C'_δ
              simp only [mul_zero] at hp
              refine hp.congr' ?_
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
              rw [div_pow, Real.rpow_neg hu.le, Real.rpow_two, zpow_neg, zpow_natCast, pow_add, pow_two]
              field_simp [hu.ne']; ring
            simpa using ((ht1.const_mul _).add ht2).const_mul 2
          filter_upwards [(hlim3.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (le_mem_nhds (by positivity : 0 < ε / 16)),
            ha2] with n hn hlog2
          have hlog_pos : 0 < Real.log n := by linarith
          have hH_inv : 1 / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1) ≤ (Real.log n) ^ (-(R + 2 : ℤ)) := by
            rw [zpow_neg, zpow_natCast]; exact one_div_le_one_div_of_le (by positivity) (Nat.lt_floor_add_one _).le
          have hlogH : Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (R + 2 : ℝ) * Real.log (Real.log n) := by
            have h1 : (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) ≤ (Real.log n) ^ (R + 2) := Nat.floor_le (by positivity)
            have h2 := Real.log_le_log (by exact_mod_cast Nat.one_le_floor_iff.mpr (one_le_pow₀ (by linarith))) h1
            rwa [Real.log_pow] at h2
          calc (2 * Real.log n) * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) * (2 * Real.log 4)) +
                ((2 * (h : ℝ) / Real.pi) * (Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) ^ R *
                  C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)))
              ≤ Real.log n * (2 * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) * (4 * (h : ℝ) * C'_δ + (h : ℝ) * (2 * Real.log 4)) * (Real.log n) ^ (-(R + 2 : ℤ)) +
                ((2 * (h : ℝ) / Real.pi) * ((R + 2 : ℝ) * Real.log (Real.log n) + 1)) ^ R * C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)))) := by
                  refine mul_le_mul_of_nonneg_left ?_ hlog_pos.le |>.trans_eq (by ring)
                  have h_term1 : 4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) * (2 * Real.log 4) ≤
                      (4 * (h : ℝ) * C'_δ + (h : ℝ) * (2 * Real.log 4)) * (Real.log n) ^ (-(R + 2 : ℤ)) := by
                    have : (h : ℝ) / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1) = (h : ℝ) * (1 / ((⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) := by ring
                    rw [this]; nlinarith [hH_inv, show (0 : ℝ) ≤ (h : ℝ) * (2 * Real.log 4) by positivity]
                  have h_term2 : ((2 * (h : ℝ) / Real.pi) * (Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) + 1)) ^ R ≤
                      ((2 * (h : ℝ) / Real.pi) * ((R + 2 : ℝ) * Real.log (Real.log n) + 1)) ^ R := by
                    refine pow_le_pow_left₀ (by
                      have : 0 ≤ Real.log (⌊(Real.log n) ^ (R + 2)⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_floor_iff.mpr (one_le_pow₀ (by linarith)))
                      positivity) ?_ R
                    gcongr
                  gcongr
            _ ≤ Real.log n * (ε / 16) := mul_le_mul_of_nonneg_left hn hlog_pos.le
            _ = (ε / 16) * Real.log n := by ring
        have hb4 : ∀ᶠ n : ℕ in atTop, 16 * (n : ℝ) ^ (1 - δ) ≤ (ε / 32) * (n : ℝ) ∧
            4 * Real.log 4 / (Real.log n) ^ AR ≤ ε / 32 := by
          have h0 : Tendsto (fun n : ℕ => 16 * (n : ℝ) ^ (-δ)) atTop (𝓝 0) :=
            ((tendsto_rpow_neg_atTop hδ0).comp tendsto_natCast_atTop_atTop).const_mul 16
          have h1_lim : Tendsto (fun n : ℕ => 4 * Real.log 4 / (Real.log n) ^ AR) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega : AR ≠ 0)).comp
              (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
          filter_upwards [h0.eventually (le_mem_nhds (by positivity : 0 < ε / 32)),
            h1_lim.eventually (le_mem_nhds (by positivity : 0 < ε / 32)), eventually_ge_atTop 2] with n hn hn_ar hn2
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have h2 := mul_le_mul_of_nonneg_right hn hn_pos.le
          rw [show 16 * (n : ℝ) ^ (-δ) * (n : ℝ) = 16 * (n : ℝ) ^ (1 - δ) by
            rw [mul_assoc, ← Real.rpow_one (n : ℝ), ← Real.rpow_add hn_pos]; ring_nf] at h2
          exact ⟨h2, hn_ar⟩
        filter_upwards [(hb1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (le_mem_nhds (by positivity : 0 < ε / 16)),
          (hb2.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (le_mem_nhds (by positivity : 0 < ε / 16)),
          hb3, hb4, ha2] with n h1' h2' h3' h4' hlog2
        have hlog_pos : 0 < Real.log n := by linarith
        exact ⟨(div_le_iff₀ hlog_pos).mp h1', (div_le_iff₀ hlog_pos).mp h2', h3', h4'.1, h4'.2⟩
      filter_upwards [ha1, ha2, ha3, ha4, ha5, ha6, ha7] with n ⟨a1, a2⟩ b c d e f ⟨g1, g2, g3, g4⟩
      have hlog_pos : 0 < Real.log n := by linarith
      have hf' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hlog_pos).mp f) (by norm_num : (0 : ℝ) ≤ 1)
      have hf1 : 2 * C_m ≤ (ε / 16) * Real.log n := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
      have hf2 : 2 * Real.log 4 ≤ (ε / 16) * Real.log n := by linarith [hC_m]
      exact ⟨a1, a2, b, c, Nat.one_le_floor_iff.mpr (one_le_pow₀ (by linarith)), d, e, hf1, hf2,
        by rw [le_div_iff₀ (by positivity)]
           have : 2 * (Real.log n) ^ AR ≤ (n : ℝ) ^ δ * (Real.log n) ^ AR := by nlinarith [pow_nonneg hlog_pos.le AR]
           have : (n : ℝ) ^ δ * (Real.log n) ^ AR ≤ (n : ℝ) := by rw [← le_div_iff₀ (by positivity)]; exact d
           linarith, g1, g2, g3, g4⟩
    filter_upwards [h_ev_t] with n ⟨hNmod, hn16, hlog2, hnd2, hH1, hnd_ar, hAR_sqrt, hcm_bd, hlog4_bd, hn_ar_2, hcol_bd, htop_bd, hmain_bd, h16_bd, h4ar_bd⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log n := by linarith
    set P_lo : ℕ := max (⌊(n : ℝ) ^ a⌋₊ + 1) (⌊(n : ℝ) ^ δ⌋₊ + 1)
    set P_hi : ℕ := min ⌊(n : ℝ) ^ b⌋₊ ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊
    set S_all := (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime
    set S_low := S_all.filter (· ≤ ⌊(n : ℝ) ^ δ⌋₊)
    set S_high := (S_all.filter (⌊(n : ℝ) ^ δ⌋₊ < ·)).filter (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ < ·)
    set S_mid := (S_all.filter (⌊(n : ℝ) ^ δ⌋₊ < ·)).filter (· ≤ ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊)
    have h_part3 :
        ∑ p ∈ S_all, (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) =
        (∑ p ∈ S_low, (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)) +
        (∑ p ∈ S_high, (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)) +
        (∑ p ∈ S_mid, (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)) := by
      have h1 : S_all = S_low ∪ (S_high ∪ S_mid) := by
        ext p; simp only [S_low, S_high, S_mid, Finset.mem_union, Finset.mem_filter]; omega
      have hd1 : Disjoint S_low (S_high ∪ S_mid) := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [S_low, S_high, S_mid, Finset.mem_union, Finset.mem_filter] at hp1 hp2; omega
      have hd2 : Disjoint S_high S_mid := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [S_high, S_mid, Finset.mem_filter] at hp1 hp2; omega
      rw [h1, Finset.sum_union hd1, Finset.sum_union hd2]; ring
    rw [h_part3]
    refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_)
    · refine le_trans (norm_sum_le _ _) ?_
      have hle1 : ∑ p ∈ S_low, ‖(padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
          ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime, (2 * (n : ℝ) / p) * Real.log p := by
        have hsub : S_low ⊆ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime := by
          intro p hp; simp only [S_low, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨hp.1.2.two_le, hp.2⟩, hp.1.2⟩
        calc ∑ p ∈ S_low, ‖(padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖
            ≤ ∑ p ∈ S_low, (2 * (n : ℝ) / p) * Real.log p := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
              have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
              rw [norm_mul, norm_ePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog_nn)]
              exact mul_le_mul_of_nonneg_right (padicValNat_factorial_upper_rpow hp_prime) hlog_nn
          _ ≤ ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime, (2 * (n : ℝ) / p) * Real.log p :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
                have := (Finset.mem_filter.mp hp).2; positivity
      have hm := abs_le.mp (hm_bd ((n : ℝ) ^ δ) hnd2)
      have hlog_nd : Real.log ((n : ℝ) ^ δ) = δ * Real.log n := Real.log_rpow hn_pos δ
      have h_m_bd : ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime, (2 * (n : ℝ) / p) * Real.log p ≤
          2 * δ * (n : ℝ) * Real.log n + 2 * C_m * (n : ℝ) := by
        have h1 : ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime, (2 * (n : ℝ) / p) * Real.log p =
            2 * (n : ℝ) * ∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) ^ δ⌋₊).filter Nat.Prime, Real.log p / p := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
        rw [h1]; nlinarith [hm.2, hlog_nd]
      have h_d_bd : 2 * δ ≤ ε / (8 * (h : ℝ)) := by linarith [min_le_left (ε / (16 * (h : ℝ))) (1 / 3)]
      have h_d_bd2 : 2 * δ ≤ ε / 8 := by
        have : (1 : ℝ) ≤ h := by exact_mod_cast (by omega : 1 ≤ h)
        calc 2 * δ ≤ ε / (8 * (h : ℝ)) := h_d_bd
          _ ≤ ε / 8 := div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
      nlinarith [mul_nonneg hn_pos.le hlog_pos.le, mul_le_mul_of_nonneg_right hcm_bd hn_pos.le]
    · refine le_trans (norm_sum_le _ _) ?_
      set J : ℕ := ⌊(Real.log n) ^ AR⌋₊
      have h_le_sum : ∑ p ∈ S_high, ‖(padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime,
            (padicValNat p n.factorial : ℝ) * Real.log p := by
        have hsub : S_high ⊆ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime := by
          intro p hp; simp only [S_high, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          have hnb_le : ⌊(n : ℝ) ^ b⌋₊ ≤ n := by
            rw [← Nat.floor_natCast (n := n) (α := ℝ)]
            exact Nat.floor_mono (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hb)
          exact ⟨⟨hp.2, le_trans hp.1.1.1.2 hnb_le⟩, hp.1.1.2⟩
        calc ∑ p ∈ S_high, ‖(padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖
            ≤ ∑ p ∈ S_high, (padicValNat p n.factorial : ℝ) * Real.log p := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
              have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
              rw [norm_mul, norm_ePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog_nn)]
          _ ≤ ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime,
                (padicValNat p n.factorial : ℝ) * Real.log p :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
                mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
      have h_vp_eq : ∀ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime,
          (padicValNat p n.factorial : ℝ) * Real.log p ≤ ((n : ℝ) / p) * Real.log p := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hp_gt : (n : ℝ) / (Real.log n) ^ AR < p :=
          lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast (Finset.mem_Icc.mp hp'.1).1)
        have hnsq : n < p ^ 2 := by
          have h1 : (n : ℝ) < (p : ℝ) ^ 2 := by
            have h2 : (n : ℝ) ^ (1 / 2 : ℝ) < p := by
              have : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) / (Real.log n) ^ AR := by
                rw [le_div_iff₀ (by positivity)]
                calc (n : ℝ) ^ (1 / 2 : ℝ) * (Real.log n) ^ AR ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
                      mul_le_mul_of_nonneg_left hAR_sqrt (by positivity)
                  _ = (n : ℝ) := by rw [← Real.rpow_add hn_pos]; norm_num
              linarith
            have h3 := pow_lt_pow_left₀ h2 (by positivity) (by norm_num : 2 ≠ 0)
            rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn_pos.le] at h3
            simpa using h3
          exact_mod_cast h1
        rw [padicValNat_factorial_of_lt_sq hp'.2 hnsq]
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le))
        rw [le_div_iff₀ (by exact_mod_cast hp'.2.pos)]
        exact_mod_cast Nat.div_mul_le_self n p
      have h_j_bd : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime,
            ((n : ℝ) / p) * Real.log p ≤ (n : ℝ) * (Real.log ((Real.log n) ^ AR + 2) + 2 * Real.log 4 + 2) := by
        have hA_ge2 : 2 ≤ ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1 := by omega
        have hm2 := hm2_bd (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n hA_ge2
        split_ifs at hm2 with hle
        · have h_eq : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime, ((n : ℝ) / p) * Real.log p =
              (n : ℝ) * ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime, Real.log p / p := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
          have h_ratio : (n : ℝ) / ((⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1 : ℕ) : ℝ) ≤ (Real.log n) ^ AR := by
            rw [div_le_iff₀ (by positivity)]
            have : (n : ℝ) / (Real.log n) ^ AR < (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
            rw [div_lt_iff₀ (by positivity)] at this
            push_cast; linarith
          have h_lg : Real.log ((n : ℝ) / ((⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1 : ℕ) : ℝ)) ≤ Real.log ((Real.log n) ^ AR + 2) :=
            Real.log_le_log (by positivity) (by linarith)
          have h_m_sub : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime, Real.log p / p ≤
              Real.log ((Real.log n) ^ AR + 2) + 2 * C_m + 1 := by
            have hA1_ge2 : (2 : ℝ) ≤ (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) := by
              exact_mod_cast Nat.le_floor hn_ar_2
            have hsub : (Finset.Icc 2 ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊).filter Nat.Prime ⊆ (Finset.Icc 2 n).filter Nat.Prime := by
              intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨⟨hp.1.1, le_trans hp.1.2 (by exact_mod_cast Nat.floor_le (by positivity) |>.trans (div_le_self hn_pos.le (one_le_pow₀ (by linarith))))⟩, hp.2⟩
            have hsdiff : (Finset.Icc 2 n).filter Nat.Prime \ (Finset.Icc 2 ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊).filter Nat.Prime =
                (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime := by
              ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]; omega
            have heq : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime, Real.log p / p =
                (∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log p / p) -
                (∑ p ∈ (Finset.Icc 2 ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊).filter Nat.Prime, Real.log p / p) := by
              rw [← hsdiff, Finset.sum_sdiff hsub]; ring
            have hmN := abs_le.mp (by simpa [Nat.floor_natCast] using hm_bd (n : ℝ) (by exact_mod_cast (by omega : 2 ≤ n)))
            have hmA := abs_le.mp (by simpa [Nat.floor_natCast] using hm_bd (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) hA1_ge2)
            have hlg_diff : Real.log (n : ℝ) - Real.log (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) ≤ Real.log ((Real.log n) ^ AR + 2) + 1 := by
              rw [← Real.log_div hn_pos.ne' (by linarith)]
              have h_r : (n : ℝ) / (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) ≤ 2 * (Real.log n) ^ AR := by
                have h1 : (n : ℝ) / (Real.log n) ^ AR < (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
                have h2 : (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) + 1 ≤ 2 * (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ : ℝ) := by linarith
                rw [div_le_iff₀ (by linarith)]
                rw [div_lt_iff₀ (by positivity)] at h1
                nlinarith [pow_nonneg hlog_pos.le AR]
              have hlg1 := Real.log_le_log (by positivity) h_r
              rw [Real.log_mul (by norm_num) (by positivity)] at hlg1
              have hlg2 : Real.log ((Real.log n) ^ AR) ≤ Real.log ((Real.log n) ^ AR + 2) :=
                Real.log_le_log (by positivity) (by linarith)
              linarith [Real.log_two_lt_d9]
            linarith
          rw [h_eq]
          exact mul_le_mul_of_nonneg_left (le_trans h_m_sub (by linarith [hC_m, Real.log_pos (by norm_num : (1 : ℝ) < 4)])) hn_pos.le
        · have h_emp : (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime = ∅ := by
            ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
          rw [h_emp, Finset.sum_empty]; positivity
      have h_le2 : ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime,
            (padicValNat p n.factorial : ℝ) * Real.log p ≤
          ∑ p ∈ (Finset.Icc (⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ + 1) n).filter Nat.Prime, ((n : ℝ) / p) * Real.log p :=
        Finset.sum_le_sum h_vp_eq
      have h_tot_s_high : (n : ℝ) * (Real.log ((Real.log n) ^ AR + 2) + 2 * Real.log 4 + 2) ≤
          (ε / 8) * ((n : ℝ) * Real.log n) := by
        have h1 : Real.log ((Real.log n) ^ AR + 2) + 2 * Real.log 4 + 2 ≤ (ε / 16) * Real.log n := by
          linarith [htop_bd, show 0 ≤ 4 * Real.log 4 / (Real.log n) ^ AR by positivity]
        nlinarith [hn_pos.le]
      exact le_trans h_le_sum (le_trans h_le2 (le_trans h_j_bd h_tot_s_high))
    · by_cases hmid_empty : S_mid = ∅
      · rw [hmid_empty, Finset.sum_empty, norm_zero]; positivity
      have hmid_ne : S_mid.Nonempty := Finset.nonempty_iff_ne_empty.mpr hmid_empty
      set A_mid : ℕ := max (⌊(n : ℝ) ^ a⌋₊ + 1) (⌊(n : ℝ) ^ δ⌋₊ + 1)
      set B_mid : ℕ := min ⌊(n : ℝ) ^ b⌋₊ ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊
      have hA_mid_ge1 : 1 ≤ A_mid := le_trans (by omega : 1 ≤ ⌊(n : ℝ) ^ δ⌋₊ + 1) (le_max_right _ _)
      have hAB_mid : A_mid ≤ B_mid := by
        obtain ⟨p, hp⟩ := hmid_ne
        simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
        exact max_le (by omega) (by omega)
      have h_sub_mid : S_mid ⊆ (Finset.Icc A_mid B_mid).filter Nat.Prime := by
        intro p hp; simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨max_le hp.1.1.1.1 (by omega), le_min hp.1.1.1.2 hp.2⟩, hp.1.1.2⟩
      have h_eq_mid : ∑ p ∈ S_mid, (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) =
          ∑ p ∈ Finset.Icc A_mid B_mid,
            if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0 := by
        rw [← Finset.sum_filter]
        congr 1; ext p; simp only [Finset.mem_filter, and_iff_right_iff_imp]
        intro hp; exact (Finset.mem_filter.mp (h_sub_mid hp)).1
      rw [h_eq_mid, dyadic_Icc_partition hA_mid_ge1 hAB_mid]
      set K_dy := (Finset.range (Nat.log 2 B_mid + 1)).filter (fun k => A_mid * 2 ^ k ≤ B_mid)
      set K_col := K_dy.filter (fun k => ∃ r ∈ Finset.Icc 2 R,
        (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR)
      set K_ok := K_dy.filter (fun k => ¬ ∃ r ∈ Finset.Icc 2 R,
        (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR)
      have hK_split : K_dy = K_col ∪ K_ok := by
        ext k; simp only [K_col, K_ok, Finset.mem_union, Finset.mem_filter]; tauto
      have hK_disj : Disjoint K_col K_ok := by
        rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [K_col, K_ok, Finset.mem_filter] at hk1 hk2; exact hk2.2 hk1.2
      rw [hK_split, Finset.sum_union hK_disj]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · refine le_trans (norm_sum_le _ _) ?_
        have h_col_term : ∀ k ∈ K_col,
            ‖∑ p ∈ Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1)),
              if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0‖ ≤
            ∑ r ∈ Finset.Icc 2 R,
              if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                  2 * (n : ℝ) * (Real.log p / p)
              else 0 := by
          intro k hk
          obtain ⟨r, hr, hr_le, hr_lt⟩ := (Finset.mem_filter.mp hk).2
          have h1 : ‖∑ p ∈ Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1)),
                if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0‖ ≤
              ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                2 * (n : ℝ) * (Real.log p / p) := by
            refine le_trans (norm_sum_le _ _) ?_
            rw [Finset.sum_filter]
            refine Finset.sum_le_sum fun p hp => ?_
            split_ifs with hpS hpP
            · have hp_prime := (Finset.mem_filter.mp (h_sub_mid hpS)).2
              have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
              rw [norm_mul, norm_ePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog_nn)]
              exact (mul_le_mul_of_nonneg_right (padicValNat_factorial_upper_rpow hp_prime) hlog_nn).trans_eq (by ring)
            · exact absurd (Finset.mem_filter.mp (h_sub_mid hpS)).2 hpP
            · rw [norm_zero]; positivity
            · rw [norm_zero]
          have h2 : ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                2 * (n : ℝ) * (Real.log p / p) ≤
              ∑ r ∈ Finset.Icc 2 R,
                if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                  ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                    2 * (n : ℝ) * (Real.log p / p)
                else 0 := by
            calc ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                  2 * (n : ℝ) * (Real.log p / p)
                = if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                    ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                      2 * (n : ℝ) * (Real.log p / p)
                  else 0 := by rw [if_pos ⟨hr_le, hr_lt⟩]
              _ ≤ _ := Finset.single_le_sum (fun s _ => by split_ifs <;> [exact Finset.sum_nonneg fun p hp => by have := (Finset.mem_filter.mp hp).2; positivity; exact le_rfl]) hr
          exact le_trans h1 h2
        calc ∑ k ∈ K_col, ‖∑ p ∈ Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1)),
                if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0‖
            ≤ ∑ k ∈ K_col, ∑ r ∈ Finset.Icc 2 R,
                if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                  ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                    2 * (n : ℝ) * (Real.log p / p)
                else 0 := Finset.sum_le_sum h_col_term
          _ = ∑ r ∈ Finset.Icc 2 R, ∑ k ∈ K_col,
                if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                  ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                    2 * (n : ℝ) * (Real.log p / p)
                else 0 := Finset.sum_comm
          _ ≤ ∑ _r ∈ Finset.Icc 2 R, 2 * (n : ℝ) * (Real.log (4 * (Real.log n) ^ AR + 4) + C_m2) := by
              refine Finset.sum_le_sum fun r hr => ?_
              have hr2 := (Finset.mem_Icc.mp hr).1
              set L_r : ℕ := max 2 ⌊((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ))⌋₊
              set U_r : ℕ := min n ⌊2 * (n : ℝ) ^ (1 / (r : ℝ))⌋₊
              have hdisj_p : Set.PairwiseDisjoint ↑K_col
                  (fun k => (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime) := by
                intro k₁ _ k₂ _ hne; rw [Finset.disjoint_left]; intro p hp1 hp2
                simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
                rcases lt_or_gt_of_ne hne with hlt | hlt
                · have : 2 * (A_mid * 2 ^ k₁) ≤ A_mid * 2 ^ k₂ := by
                    calc 2 * (A_mid * 2 ^ k₁) = A_mid * 2 ^ (k₁ + 1) := by ring
                      _ ≤ A_mid * 2 ^ k₂ := Nat.mul_le_mul_left A_mid (Nat.pow_le_pow_right (by norm_num) hlt)
                  omega
                · have : 2 * (A_mid * 2 ^ k₂) ≤ A_mid * 2 ^ k₁ := by
                    calc 2 * (A_mid * 2 ^ k₂) = A_mid * 2 ^ (k₂ + 1) := by ring
                      _ ≤ A_mid * 2 ^ k₁ := Nat.mul_le_mul_left A_mid (Nat.pow_le_pow_right (by norm_num) hlt)
                  omega
              have h_sub_r : ∀ k ∈ K_col, (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR →
                  (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime ⊆
                    (Finset.Icc L_r U_r).filter Nat.Prime := by
                intro k _ ⟨hr_le, hr_lt⟩ p hp
                simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
                have hp_lo2 : 2 ≤ p := hp.2.two_le
                have hPk_ge : ((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ)) < (A_mid * 2 ^ k : ℝ) := by
                  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
                  have h1 : (n : ℝ) / (Real.log n) ^ AR < (A_mid * 2 ^ k : ℝ) ^ r := (div_lt_iff₀ (by positivity)).mp hr_lt
                  have h2 := Real.rpow_lt_rpow (by positivity) h1 (by positivity : 0 < 1 / (r : ℝ))
                  rw [← Real.rpow_natCast (A_mid * 2 ^ k : ℝ), ← Real.rpow_mul (by positivity),
                    mul_one_div_cancel hr_pos.ne', Real.rpow_one] at h2
                  exact h2
                have hp_lo_Lr' : ⌊((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ))⌋₊ ≤ p :=
                  le_trans (Nat.floor_le (by positivity) |>.trans hPk_ge.le |> fun h => Nat.floor_le_of_le (by exact_mod_cast h)) hp.1.1
                have hPk_le : (A_mid * 2 ^ k : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
                  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
                  have h1 := Real.rpow_le_rpow (by positivity) hr_le (by positivity : 0 ≤ 1 / (r : ℝ))
                  rw [← Real.rpow_natCast (A_mid * 2 ^ k : ℝ), ← Real.rpow_mul (by positivity),
                    mul_one_div_cancel hr_pos.ne', Real.rpow_one] at h1
                  exact h1
                have hp_le_n : p ≤ n := by
                  have hB_le_n : B_mid ≤ n := le_trans (min_le_left _ _) (by
                    rw [← Nat.floor_natCast (n := n) (α := ℝ)]
                    exact Nat.floor_mono (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hb))
                  exact le_trans hp.1.2 (le_trans (min_le_left _ _) hB_le_n)
                have hp_le_Ur : p ≤ ⌊2 * (n : ℝ) ^ (1 / (r : ℝ))⌋₊ := by
                  refine Nat.le_floor ?_
                  have h1 : (p : ℝ) ≤ 2 * (A_mid * 2 ^ k : ℝ) := by exact_mod_cast le_trans hp.1.2 (le_trans (min_le_right _ _) (by omega))
                  linarith
                exact ⟨⟨max_le hp_lo2 hp_lo_Lr', le_min hp_le_n hp_le_Ur⟩, hp.2⟩
              have h_sum_sub : ∑ k ∈ K_col,
                    if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                      ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                        2 * (n : ℝ) * (Real.log p / p)
                    else 0 ≤
                  ∑ p ∈ (Finset.Icc L_r U_r).filter Nat.Prime, 2 * (n : ℝ) * (Real.log p / p) := by
                have h_eq_filt : ∑ k ∈ K_col,
                      if (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR then
                        ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                          2 * (n : ℝ) * (Real.log p / p)
                      else 0 =
                    ∑ k ∈ K_col.filter (fun k => (A_mid * 2 ^ k : ℝ) ^ r ≤ n ∧ (n : ℝ) / (A_mid * 2 ^ k : ℝ) ^ r < (Real.log n) ^ AR),
                      ∑ p ∈ (Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1))).filter Nat.Prime,
                        2 * (n : ℝ) * (Real.log p / p) := by rw [Finset.sum_filter]
                rw [h_eq_filt, ← Finset.sum_biUnion (hdisj_p.mono (Finset.filter_subset _ _))]
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => by have := (Finset.mem_filter.mp hp).2; positivity
                rw [Finset.biUnion_subset]
                intro k hk
                have hk' := Finset.mem_filter.mp hk
                exact h_sub_r k hk'.1 hk'.2
              have hm2 := hm2_bd L_r U_r (le_max_left _ _)
              have h_ur_lr : (if L_r ≤ U_r then Real.log ((U_r : ℝ) / L_r) + C_m2 else 0) ≤
                  Real.log (4 * (Real.log n) ^ AR + 4) + C_m2 := by
                split_ifs with hLU
                · have h_ratio : (U_r : ℝ) / L_r ≤ 4 * (Real.log n) ^ AR + 4 := by
                    have hU : (U_r : ℝ) ≤ 2 * (n : ℝ) ^ (1 / (r : ℝ)) := le_trans (by exact_mod_cast min_le_right _ _) (Nat.floor_le (by positivity))
                    have hL_ge : ((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ)) ≤ 2 * (L_r : ℝ) := by
                      have h1 : ((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ)) < (⌊((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
                      have h2 : (⌊((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ))⌋₊ : ℝ) ≤ L_r := by exact_mod_cast le_max_right _ _
                      have h3 : (1 : ℝ) ≤ L_r := by exact_mod_cast le_trans (by norm_num : 1 ≤ 2) (le_max_left _ _)
                      linarith
                    have h_rpow : (n : ℝ) ^ (1 / (r : ℝ)) / ((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ)) ≤ (Real.log n) ^ AR + 1 := by
                      rw [← Real.div_rpow hn_pos.le (by positivity), div_div_cancel_left' hn_pos.ne']
                      exact le_trans (Real.rpow_le_self_of_one_le (one_le_pow₀ (by linarith)) (by
                        have : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
                        exact div_le_one_of_le₀ (by linarith) (by positivity))) (by linarith)
                    rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < L_r))]
                    calc (U_r : ℝ) ≤ 2 * (n : ℝ) ^ (1 / (r : ℝ)) := hU
                      _ ≤ 2 * (((Real.log n) ^ AR + 1) * ((n : ℝ) / (Real.log n) ^ AR) ^ (1 / (r : ℝ))) := by
                          nlinarith [div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) (1 / (r : ℝ))) |>.mp h_rpow]
                      _ ≤ 2 * (((Real.log n) ^ AR + 1) * (2 * (L_r : ℝ))) := by
                          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL_ge (by positivity)) (by norm_num)
                      _ = (4 * (Real.log n) ^ AR + 4) * L_r := by ring
                  exact add_le_add_right (Real.log_le_log (by exact_mod_cast (by positivity : 0 < (U_r : ℝ) / L_r)) h_ratio) C_m2
                · positivity
              calc ∑ k ∈ K_col, _ ≤ 2 * (n : ℝ) * ∑ p ∈ (Finset.Icc L_r U_r).filter Nat.Prime, Real.log p / p := by
                    rw [Finset.mul_sum]; exact h_sum_sub
                _ ≤ 2 * (n : ℝ) * (Real.log (4 * (Real.log n) ^ AR + 4) + C_m2) := mul_le_mul_of_nonneg_left (le_trans hm2 h_ur_lr) (by positivity)
          _ ≤ (R : ℝ) * (2 * (n : ℝ) * (Real.log (4 * (Real.log n) ^ AR + 4) + C_m2)) := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : R + 1 - 2 ≤ R)) (by positivity)
          _ ≤ (ε / 16) * ((n : ℝ) * Real.log n) := by nlinarith [hn_pos.le]
      · refine le_trans (norm_sum_le _ _) ?_
        set H : ℕ := ⌊(Real.log n) ^ (R + 2)⌋₊
        obtain ⟨Ψm, Bm, cm, bm, hΨm, hBm, hbm0, hcm_bd, hbm_bd, hmap_m, hΨm_bd, hcm_sum⟩ :=
          vaaler_mod_approx h (by omega) t ht1 ht_lt H hH1
        have h_ok_bd : ∀ k ∈ K_ok,
            ‖∑ p ∈ Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1)),
              if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0‖ ≤
            (2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR + 8 * (n : ℝ) ^ (1 - δ)) +
            ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
              (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) +
              ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) * (n : ℝ) := by
          intro k hk
          have hk_dy := (Finset.mem_filter.mp hk).1
          have hk_le := (Finset.mem_filter.mp hk_dy).2
          have hk_not_col := (Finset.mem_filter.mp hk).2
          set P_k : ℕ := A_mid * 2 ^ k
          set b_k : ℕ := min B_mid (2 * P_k - 1)
          have hP_lo : (n : ℝ) ^ δ ≤ (P_k : ℝ) := by
            have h1 : (n : ℝ) ^ δ < ⌊(n : ℝ) ^ δ⌋₊ + 1 := Nat.lt_floor_add_one _
            have h2 : ⌊(n : ℝ) ^ δ⌋₊ + 1 ≤ A_mid := le_max_right _ _
            exact le_trans h1.le (by exact_mod_cast le_trans h2 (Nat.le_mul_of_pos_right A_mid (pow_pos (by norm_num) k)))
          have hP_hi : (P_k : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 12 := by
            have h1 : (P_k : ℝ) ≤ B_mid := by exact_mod_cast hk_le
            have h2 : (B_mid : ℝ) ≤ (n : ℝ) / (Real.log n) ^ AR := le_trans (by exact_mod_cast min_le_right _ _) (Nat.floor_le (by positivity))
            have h3 : (Real.log n) ^ 12 ≤ (Real.log n) ^ AR := pow_le_pow_right₀ (by linarith) (by omega)
            exact le_trans h1 (le_trans h2 (div_le_div_of_nonneg_left hn_pos.le (by positivity) h3))
          have hP_pos : (0 : ℝ) < P_k := lt_of_lt_of_le (Real.rpow_pos_of_pos hn_pos δ) hP_lo
          have hb_ge : (P_k : ℝ) ≤ (b_k : ℝ) := by exact_mod_cast le_min hk_le (by omega : P_k ≤ 2 * P_k - 1)
          have hb_le : (b_k : ℝ) ≤ 2 * (P_k : ℝ) := by exact_mod_cast le_trans (min_le_right _ _) (by omega : 2 * P_k - 1 ≤ 2 * P_k)
          have h_p_in_Smid : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, p ∈ S_mid := by
            intro p hp
            have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
            have hp_pr := (Finset.mem_filter.mp hp).2
            have hp_a : ⌊(n : ℝ) ^ a⌋₊ + 1 ≤ p := le_trans (le_max_left _ _) hp_icc.1
            have hp_b : p ≤ ⌊(n : ℝ) ^ b⌋₊ := le_trans hp_icc.2 (le_trans (min_le_left _ _) (min_le_left _ _))
            have hp_d : ⌊(n : ℝ) ^ δ⌋₊ < p := by
              have : ⌊(n : ℝ) ^ δ⌋₊ + 1 ≤ A_mid := le_max_right _ _; omega
            have hp_ar : p ≤ ⌊(n : ℝ) / (Real.log n) ^ AR⌋₊ := le_trans hp_icc.2 (le_trans (min_le_left _ _) (min_le_right _ _))
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_a, hp_b⟩, hp_pr⟩, hp_d⟩, hp_ar⟩
          have h_sum_eq_filt :
              ∑ p ∈ Finset.Icc P_k b_k,
                (if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0) =
              ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) := by
            rw [← Finset.sum_filter]
            refine Finset.sum_congr (by ext p; simp only [Finset.mem_filter]; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (Finset.mem_filter.mp (h_sub_mid h2)).2⟩, fun ⟨h1, h2⟩ => ⟨h1, h_p_in_Smid p (Finset.mem_filter.mpr ⟨h1, h2⟩)⟩⟩) fun _ _ => rfl
          rw [h_sum_eq_filt]
          have h_amp_err :
              ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                  ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * (Real.log p : ℂ) *
                    ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
              2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR + 8 * (n : ℝ) ^ (1 - δ) := by
            refine le_trans (norm_sum_le _ _) ?_
            have h_term_a : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                ‖((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * (Real.log p : ℂ) *
                    ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
                Real.log p + (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * Real.log p := by
              intro p hp
              have hp_pr := (Finset.mem_filter.mp hp).2
              have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
              have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
              rw [norm_mul, norm_mul, norm_ePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nn]
              have h_vp_lo : (n : ℝ) / p - 1 ≤ (padicValNat p n.factorial : ℝ) := by
                have h1 : (n : ℝ) / p - 1 < ((n / p : ℕ) : ℝ) := by
                  have := Int.lt_floor_add_one ((n : ℝ) / p)
                  have hfl : ((n / p : ℕ) : ℝ) = (⌊(n : ℝ) / p⌋ : ℝ) := by
                    have := Int.floor_div_natCast (n : ℤ) p; simp at this; exact_mod_cast this.symm
                  linarith
                have h2 : n / p ≤ padicValNat p n.factorial := by
                  haveI : Fact p.Prime := ⟨hp_pr⟩
                  have hlt : n < p ^ (n + 1) := lt_of_lt_of_le (Nat.lt_pow_self hp_pr.one_lt) (Nat.pow_le_pow_right hp_pr.pos (by omega))
                  rw [padicValNat_factorial_eq_sum_floor hp_pr hlt]
                  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩)
                linarith [show ((n / p : ℕ) : ℝ) ≤ (padicValNat p n.factorial : ℝ) by exact_mod_cast h2]
              have h_vp_hi : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / p + 2 * (n : ℝ) / (P_k : ℝ) ^ 2 := by
                have h1 : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
                  haveI : Fact p.Prime := ⟨hp_pr⟩
                  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
                  rw [le_div_iff₀ (by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le; linarith)]
                  exact_mod_cast (by nlinarith : padicValNat p n.factorial * (p - 1) ≤ n)
                have h2 : (n : ℝ) / ((p : ℝ) - 1) - (n : ℝ) / p = (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
                  have hp1 : (p : ℝ) - 1 ≠ 0 := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le; linarith
                  field_simp [hp_pos.ne', hp1]; ring
                have h3 : (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
                  have hp2 : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le; linarith
                  rw [div_le_div_iff₀ (by have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le; positivity) (pow_pos hp_pos 2)]
                  nlinarith [hn_pos.le]
                have h4 : 2 * (n : ℝ) / (p : ℝ) ^ 2 ≤ 2 * (n : ℝ) / (P_k : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_left (by positivity) (pow_pos hP_pos 2) (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp_icc.1) 2)
                linarith
              have habs : |(padicValNat p n.factorial : ℝ) - (n : ℝ) / p| ≤ 1 + 2 * (n : ℝ) / (P_k : ℝ) ^ 2 := by
                rw [abs_le]; constructor <;> linarith [show 0 ≤ 2 * (n : ℝ) / (P_k : ℝ) ^ 2 by positivity]
              calc |(padicValNat p n.factorial : ℝ) - (n : ℝ) / p| * Real.log p
                  ≤ (1 + 2 * (n : ℝ) / (P_k : ℝ) ^ 2) * Real.log p := mul_le_mul_of_nonneg_right habs hlog_nn
                _ = Real.log p + (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * Real.log p := by ring
            have h_th_bk : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p ≤ 2 * Real.log 4 * P_k := by
              have hth : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p ≤ Chebyshev.theta (2 * P_k) := by
                unfold Chebyshev.theta
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
                  Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
                intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
                exact ⟨⟨hp.2.pos, Nat.le_floor (le_trans (by exact_mod_cast hp.1.2) hb_le)⟩, hp.2⟩
              linarith [Chebyshev.theta_le_log4_mul_x (by positivity : 0 ≤ 2 * (P_k : ℝ))]
            have hPk_ar : (P_k : ℝ) ≤ (n : ℝ) / (Real.log n) ^ AR :=
              le_trans (by exact_mod_cast hk_le) (le_trans (by exact_mod_cast min_le_right _ _) (Nat.floor_le (by positivity)))
            have h1_bd : 2 * Real.log 4 * P_k ≤ 2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR := by
              rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hPk_ar (by positivity)
            have h2_bd : (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * (2 * Real.log 4 * P_k) ≤ 8 * (n : ℝ) ^ (1 - δ) := by
              have hlog4_le1 : Real.log 4 ≤ 2 := by
                have : (4 : ℝ) = 2 ^ 2 := by norm_num
                rw [this, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
              have h1 : (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * (2 * Real.log 4 * P_k) = 4 * Real.log 4 * ((n : ℝ) / P_k) := by
                field_simp [hP_pos.ne']; ring
              have h2 : (n : ℝ) / P_k ≤ (n : ℝ) ^ (1 - δ) := by
                calc (n : ℝ) / P_k ≤ (n : ℝ) / (n : ℝ) ^ δ := div_le_div_of_nonneg_left hn_pos.le (by positivity) hP_lo
                  _ = (n : ℝ) ^ (1 - δ) := by rw [← Real.rpow_one (n : ℝ), ← Real.rpow_sub hn_pos]; simp
              have h4l4 : 4 * Real.log 4 ≤ 8 := by linarith
              rw [h1]
              exact mul_le_mul h4l4 h2 (by positivity) (by norm_num)
            calc ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                  ‖((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * (Real.log p : ℂ) *
                      ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖
                ≤ ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    (Real.log p + (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * Real.log p) :=
                  Finset.sum_le_sum h_term_a
              _ = (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p) +
                  (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum]
              _ ≤ 2 * Real.log 4 * P_k + (2 * (n : ℝ) / (P_k : ℝ) ^ 2) * (2 * Real.log 4 * P_k) :=
                  add_le_add h_th_bk (mul_le_mul_of_nonneg_left h_th_bk (by positivity))
              _ ≤ 2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR + 8 * (n : ℝ) ^ (1 - δ) :=
                  add_le_add h1_bd h2_bd
          set A_k : Finset ℕ := (Finset.Icc 1 R).filter (fun r => (P_k : ℝ) ^ r ≤ n)
          have h1_in_Ak : 1 ∈ A_k := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, by
            have h_pow1 : (P_k : ℝ) ^ 1 = P_k := pow_one _
            rw [h_pow1]
            exact le_trans hP_hi (div_le_self hn_pos.le (one_le_pow₀ (by linarith)))⟩
          have hAk_ne : A_k.Nonempty := ⟨1, h1_in_Ak⟩
          have hAk_sub : A_k ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
          have hAk_card : A_k.card ≤ R := le_trans (Finset.card_le_card hAk_sub) (by rw [Nat.card_Icc]; omega)
          have h_vp_Ak : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              padicValNat p n.factorial = ∑ r ∈ A_k, n / p ^ r := by
            intro p hp
            have hp_pr := (Finset.mem_filter.mp hp).2
            have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
            have hp_ge_Pk : (P_k : ℝ) ≤ p := by exact_mod_cast hp_icc.1
            have h_pr_gt : (n : ℝ) ^ (1 / (R + 1 : ℝ)) < p := by
              have h1 : (n : ℝ) ^ (1 / (R + 1 : ℝ)) < (n : ℝ) ^ δ := by
                refine Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) ?_
                have hR_lt : (1 / δ : ℝ) < R + 1 := Nat.lt_floor_add_one _
                exact one_div_lt_of_one_div_lt hδ0 hR_lt
              linarith
            have hn_lt_pR : n < p ^ (R + 1) := by
              have h1 : (n : ℝ) < (p : ℝ) ^ (R + 1) := by
                have h2 := Real.rpow_lt_rpow (by positivity) h_pr_gt (by positivity : (0 : ℝ) < R + 1)
                rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel (by positivity : (R + 1 : ℝ) ≠ 0), Real.rpow_one,
                  ← Real.rpow_natCast] at h2
                exact h2
              exact_mod_cast h1
            rw [padicValNat_factorial_eq_sum_floor hp_pr hn_lt_pR]
            symm; refine Finset.sum_subset hAk_sub ?_
            intro r hr hr_not
            have hr_gt : (n : ℝ) < (P_k : ℝ) ^ r := by
              by_contra hle; push_neg at hle
              exact hr_not (Finset.mem_filter.mpr ⟨hr, hle⟩)
            have hn_lt_pr : n < p ^ r := by
              have : (n : ℝ) < (p : ℝ) ^ r := lt_of_lt_of_le hr_gt (pow_le_pow_left₀ hP_pos.le hp_ge_Pk r)
              exact_mod_cast this
            exact Nat.div_eq_of_lt hn_lt_pr
          have h_n_div_Ak : ∀ r ∈ A_k, (n : ℝ) / (P_k : ℝ) ^ r ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR := by
            intro r hr
            have hr_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
            have hr_le : (P_k : ℝ) ^ r ≤ n := (Finset.mem_filter.mp hr).2
            have h_ge_AR : (Real.log n) ^ AR ≤ (n : ℝ) / (P_k : ℝ) ^ r := by
              by_cases hr1 : r = 1
              · subst hr1; rw [pow_one]
                have h1 : (P_k : ℝ) ≤ (n : ℝ) / (Real.log n) ^ AR := by
                  exact le_trans (by exact_mod_cast hk_le : (P_k : ℝ) ≤ B_mid)
                    (le_trans (by exact_mod_cast min_le_right _ _) (Nat.floor_le (by positivity)))
                rw [le_div_iff₀ hP_pos]
                have h2 := (le_div_iff₀ (by positivity : 0 < (Real.log n) ^ AR)).mp h1
                rw [mul_comm] at h2
                exact (le_div_iff₀ (by positivity : 0 < (Real.log n) ^ AR)).mpr h2
              · have hr2 : r ∈ Finset.Icc 2 R := Finset.mem_Icc.mpr ⟨by omega, hr_icc.2⟩
                by_contra hlt; push_neg at hlt
                exact hk_not_col ⟨r, hr2, hr_le, hlt⟩
            exact le_trans (mul_le_of_le_one_left (by positivity) (by norm_num)) h_ge_AR
          have h_ePhase_prod : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
              ePhase ((t : ℝ) * padicValNat p n.factorial / h) =
              ∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h) := by
            intro p hp
            rw [h_vp_Ak p hp, Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
            induction A_k using Finset.induction_on with
            | empty => simp [ePhase]
            | @insert r s hrs ih =>
              rw [Finset.sum_insert hrs, Finset.prod_insert hrs, ePhase_add', ih]
          have h_split_amp :
              ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) =
              (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                ((padicValNat p n.factorial : ℝ) - (n : ℝ) / p) * (Real.log p : ℂ) *
                  ePhase ((t : ℝ) * padicValNat p n.factorial / h)) +
              (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (((n : ℝ) / p) * Real.log p : ℂ) * (∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [h_ePhase_prod p hp]; push_cast; ring
          rw [h_split_amp]
          refine le_trans (norm_add_le _ _) (add_le_add h_amp_err ?_)
          have h_ePhase_floor : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, ∀ r ∈ A_k,
              ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h) = ePhase ((t : ℝ) * (⌊(n : ℝ) / (p : ℝ) ^ r⌋ : ℝ) / h) := by
            intro p hp r _
            have hfl : ((n / p ^ r : ℕ) : ℝ) = (⌊(n : ℝ) / (p : ℝ) ^ r⌋ : ℝ) := by
              have := Int.floor_div_natCast (n : ℤ) (p ^ r); simp at this; exact_mod_cast this.symm
            rw [hfl]
          have h_prod_diff :
              ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                  (((n : ℝ) / p) * Real.log p : ℂ) *
                    ((∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) -
                     (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r)))‖ ≤
              (1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) * (n : ℝ) := by
            have h_pt : ∀ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                ‖(((n : ℝ) / p) * Real.log p : ℂ) *
                    ((∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) -
                     (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r)))‖ ≤
                (1 + 4 * (h : ℝ)) ^ R * ∑ r ∈ A_k, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) := by
              intro p hp
              have hp_pr := (Finset.mem_filter.mp hp).2
              have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
              have hpd : ‖(∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) -
                    (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r))‖ ≤
                  (1 + 4 * (h : ℝ)) ^ (A_k.card - 1) * ∑ r ∈ A_k, Bm ((n : ℝ) / (p : ℝ) ^ r) := by
                have h_ind_prod : ∀ s : Finset ℕ,
                    (∀ r ∈ s, ‖ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)‖ ≤ 1 + 4 * (h : ℝ)) →
                    (∀ r ∈ s, ‖Ψm ((n : ℝ) / (p : ℝ) ^ r)‖ ≤ 1 + 4 * (h : ℝ)) →
                    (∀ r ∈ s, ‖ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h) - Ψm ((n : ℝ) / (p : ℝ) ^ r)‖ ≤ Bm ((n : ℝ) / (p : ℝ) ^ r)) →
                    ‖(∏ r ∈ s, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) - (∏ r ∈ s, Ψm ((n : ℝ) / (p : ℝ) ^ r))‖ ≤
                      (1 + 4 * (h : ℝ)) ^ (s.card - 1) * ∑ r ∈ s, Bm ((n : ℝ) / (p : ℝ) ^ r) := by
                  intro s hs1 hs2 hs3
                  induction s using Finset.induction_on with
                  | empty => simp
                  | @insert r₀ s' hr₀ ih =>
                    rw [Finset.prod_insert hr₀, Finset.prod_insert hr₀, Finset.sum_insert hr₀, Finset.card_insert_of_notMem hr₀]
                    have h_ih := ih (fun r hr => hs1 r (Finset.mem_insert_of_mem hr))
                      (fun r hr => hs2 r (Finset.mem_insert_of_mem hr))
                      (fun r hr => hs3 r (Finset.mem_insert_of_mem hr))
                    have hM_ge1 : 1 ≤ 1 + 4 * (h : ℝ) := by linarith [show (0 : ℝ) ≤ 4 * (h : ℝ) by positivity]
                    have h_prod1 : ‖∏ r ∈ s', ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)‖ ≤ (1 + 4 * (h : ℝ)) ^ s'.card := by
                      rw [norm_prod]
                      calc ∏ r ∈ s', ‖ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)‖
                          ≤ ∏ _r ∈ s', (1 + 4 * (h : ℝ)) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                            (fun r hr => hs1 r (Finset.mem_insert_of_mem hr))
                        _ = (1 + 4 * (h : ℝ)) ^ s'.card := by rw [Finset.prod_const, Finset.card_univ]
                    have h_eq : ePhase ((t : ℝ) * (n / p ^ r₀ : ℕ) / h) * (∏ r ∈ s', ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) -
                          Ψm ((n : ℝ) / (p : ℝ) ^ r₀) * (∏ r ∈ s', Ψm ((n : ℝ) / (p : ℝ) ^ r)) =
                        (ePhase ((t : ℝ) * (n / p ^ r₀ : ℕ) / h) - Ψm ((n : ℝ) / (p : ℝ) ^ r₀)) *
                          (∏ r ∈ s', ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) +
                        Ψm ((n : ℝ) / (p : ℝ) ^ r₀) *
                          ((∏ r ∈ s', ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) - (∏ r ∈ s', Ψm ((n : ℝ) / (p : ℝ) ^ r))) := by ring
                    rw [h_eq]
                    have h_Bm_nn : 0 ≤ ∑ r ∈ s', Bm ((n : ℝ) / (p : ℝ) ^ r) :=
                      Finset.sum_nonneg fun r hr => le_trans (norm_nonneg _) (hs3 r (Finset.mem_insert_of_mem hr))
                    calc ‖(ePhase ((t : ℝ) * (n / p ^ r₀ : ℕ) / h) - Ψm ((n : ℝ) / (p : ℝ) ^ r₀)) * _ +
                          Ψm ((n : ℝ) / (p : ℝ) ^ r₀) * _‖
                        ≤ ‖ePhase ((t : ℝ) * (n / p ^ r₀ : ℕ) / h) - Ψm ((n : ℝ) / (p : ℝ) ^ r₀)‖ *
                            ‖∏ r ∈ s', ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)‖ +
                          ‖Ψm ((n : ℝ) / (p : ℝ) ^ r₀)‖ *
                            ‖(∏ r ∈ s', ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) - (∏ r ∈ s', Ψm ((n : ℝ) / (p : ℝ) ^ r))‖ := by
                          refine le_trans (norm_add_le _ _) (add_le_add (by rw [norm_mul]) (by rw [norm_mul]))
                      _ ≤ Bm ((n : ℝ) / (p : ℝ) ^ r₀) * (1 + 4 * (h : ℝ)) ^ s'.card +
                          (1 + 4 * (h : ℝ)) * ((1 + 4 * (h : ℝ)) ^ (s'.card - 1) * ∑ r ∈ s', Bm ((n : ℝ) / (p : ℝ) ^ r)) := by
                          refine add_le_add (mul_le_mul (hs3 r₀ (Finset.mem_insert_self r₀ s')) h_prod1 (norm_nonneg _)
                            (le_trans (norm_nonneg _) (hs3 r₀ (Finset.mem_insert_self r₀ s'))))
                            (mul_le_mul (hs2 r₀ (Finset.mem_insert_self r₀ s')) h_ih (norm_nonneg _) (by positivity))
                      _ ≤ (1 + 4 * (h : ℝ)) ^ s'.card * (Bm ((n : ℝ) / (p : ℝ) ^ r₀) + ∑ r ∈ s', Bm ((n : ℝ) / (p : ℝ) ^ r)) := by
                          have h_pow_le : (1 + 4 * (h : ℝ)) * (1 + 4 * (h : ℝ)) ^ (s'.card - 1) ≤ (1 + 4 * (h : ℝ)) ^ s'.card := by
                            rcases Nat.eq_zero_or_pos s'.card with h0 | hpos
                            · rw [h0, pow_zero, pow_zero, mul_one]; exact hM_ge1
                            · rw [← pow_succ', Nat.sub_add_cancel hpos]
                          nlinarith [mul_le_mul_of_nonneg_right h_pow_le h_Bm_nn]
                exact h_ind_prod A_k
                  (fun r _ => (norm_ePhase _).le.trans (by linarith [show (0 : ℝ) ≤ 4 * (h : ℝ) by positivity]))
                  (fun r _ => hΨm_bd _)
                  (fun r hr => by rw [h_ePhase_floor p hp r hr]; exact hmap_m _)
              have hpow_le : (1 + 4 * (h : ℝ)) ^ (A_k.card - 1) ≤ (1 + 4 * (h : ℝ)) ^ R :=
                pow_le_pow_right₀ (by linarith [show (0 : ℝ) ≤ 4 * (h : ℝ) by positivity]) (by omega)
              calc ((n : ℝ) / p * Real.log p) * ‖(∏ r ∈ A_k, _) - (∏ r ∈ A_k, _)‖
                  ≤ ((n : ℝ) / p * Real.log p) * ((1 + 4 * (h : ℝ)) ^ (A_k.card - 1) * ∑ r ∈ A_k, Bm ((n : ℝ) / (p : ℝ) ^ r)) :=
                    mul_le_mul_of_nonneg_left hpd (by positivity)
                _ ≤ ((n : ℝ) / p * Real.log p) * ((1 + 4 * (h : ℝ)) ^ R * ∑ r ∈ A_k, Bm ((n : ℝ) / (p : ℝ) ^ r)) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow_le
                      (Finset.sum_nonneg fun r hr => le_trans (norm_nonneg _) (by rw [← h_ePhase_floor p hp r hr]; exact hmap_m _))) (by positivity)
                _ = (1 + 4 * (h : ℝ)) ^ R * ∑ r ∈ A_k, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) := by
                    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
            have h_Bm_r : ∀ r ∈ A_k,
                ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) ≤
                (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) * (n : ℝ) := by
              intro r hr
              have hsum_C : ((∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ) =
                  bm 0 * (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (((n : ℝ) / p * Real.log p : ℝ) : ℂ)) +
                  ∑ k_v ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
                    bm k_v * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                      (((n : ℝ) / p * Real.log p : ℝ) : ℂ) * ePhase ((k_v : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ r)) := by
                push_cast
                simp_rw [hBm, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                congr 1
                · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
                · rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun k_v _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun p _ => ?_
                  have heq : (k_v : ℝ) * ((n : ℝ) / (p : ℝ) ^ r) / h = (k_v : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ r) := by ring
                  rw [heq]; ring
              have hle_norm : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) ≤
                  ‖((∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) : ℝ) : ℂ)‖ := by
                rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
              rw [hsum_C] at hle_norm
              refine le_trans hle_norm (le_trans (norm_add_le _ _) (add_le_add ?_ ?_))
              · have h_bm0_norm : ‖bm 0‖ = (h : ℝ) / ((H : ℝ) + 1) := by
                  rw [hbm0, show ((h : ℂ) / ((H : ℂ) + 1)) = (((h : ℝ) / ((H : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
                    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                have h_sum_log : ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (((n : ℝ) / p * Real.log p : ℝ) : ℂ)‖ ≤
                    2 * Real.log 4 * (n : ℝ) := by
                  have h1 : (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (((n : ℝ) / p * Real.log p : ℝ) : ℂ)) =
                      ((∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (n : ℝ) / p * Real.log p : ℝ) : ℂ) := by push_cast; rfl
                  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun p hp => by
                    have := (Finset.mem_filter.mp hp).2; positivity)]
                  calc ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, (n : ℝ) / p * Real.log p
                      ≤ ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, ((n : ℝ) / P_k) * Real.log p := by
                        refine Finset.sum_le_sum fun p hp => ?_
                        have hp_pr := (Finset.mem_filter.mp hp).2
                        have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
                        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hn_pos.le hP_pos (by exact_mod_cast hp_icc.1))
                          (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le))
                    _ = ((n : ℝ) / P_k) * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p := by rw [← Finset.mul_sum]
                    _ ≤ ((n : ℝ) / P_k) * (2 * Real.log 4 * P_k) := by
                        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                        have hth : ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, Real.log p ≤ Chebyshev.theta (2 * P_k) := by
                          unfold Chebyshev.theta
                          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
                            Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
                          intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
                          exact ⟨⟨hp.2.pos, Nat.le_floor (le_trans (by exact_mod_cast hp.1.2) hb_le)⟩, hp.2⟩
                        linarith [Chebyshev.theta_le_log4_mul_x (by positivity : 0 ≤ 2 * (P_k : ℝ))]
                    _ = 2 * Real.log 4 * (n : ℝ) := by field_simp [hP_pos.ne']; ring
                rw [norm_mul, h_bm0_norm]
                exact (mul_le_mul_of_nonneg_left h_sum_log (by positivity)).trans_eq (by ring)
              · refine le_trans (norm_sum_le _ _) ?_
                obtain ⟨hW₀_nn, hw_bd, hw_diff, hw_tv⟩ := w_inv_bound_and_tv n hP_pos
                have h24_r : ∀ k_v ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
                    ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                      (((n : ℝ) / p * Real.log p : ℝ) : ℂ) * ePhase ((k_v : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ r))‖ ≤
                    C'_δ * (n : ℝ) * (Real.log n) ^ (-(R + 2 : ℤ)) := by
                  intro k_v hk_v
                  have hk_ne : k_v ≠ 0 := (Finset.mem_filter.mp hk_v).2
                  have hk_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk_v).1
                  have hk_abs : |k_v| ≤ 2 * H + 1 := by
                    have : |k_v| ≤ (H : ℤ) := abs_le.mpr ⟨hk_icc.1, hk_icc.2⟩
                    omega
                  let hfn : ℕ → ℤ := fun s => if s = r then k_v else 0
                  have h_sum_eq : ∀ p : ℕ, ∑ s ∈ {r}, (hfn s : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ s) =
                      (k_v : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ r) := fun p => by simp [hfn]
                  have h_mod := h24_mod n (P_k : ℝ) (P_k : ℝ) (b_k : ℝ) {r} hfn (fun t => (n : ℝ) / t) ((n : ℝ) / P_k)
                    hNmod hP_lo hP_hi le_rfl hb_ge hb_le
                    (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hr).1) (Finset.singleton_nonempty r)
                    (fun s hs => by rw [Finset.mem_singleton.mp hs]; exact h_n_div_Ak r hr)
                    ⟨r, Finset.mem_singleton_self r, by simp [hfn, hk_ne]⟩
                    (fun s hs => by rw [Finset.mem_singleton.mp hs]; simp [hfn]; omega)
                    hW₀_nn hw_bd hw_diff hw_tv (by
                      have hr0_eq : (({r} : Finset ℕ).filter (fun s => hfn s ≠ 0)).min'
                          ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_singleton_self r, by simp [hfn, hk_ne]⟩⟩ = r := by
                        have hfilt : ({r} : Finset ℕ).filter (fun s => hfn s ≠ 0) = {r} := by
                          ext s; simp [hfn, hk_ne]
                        simp [hfilt]
                      dsimp only; rw [hr0_eq]
                      have h1 : (1 : ℝ) ≤ |(hfn r : ℝ)| := by simp [hfn]; exact_mod_cast Int.one_le_abs hk_ne
                      calc (|(hfn r : ℝ)| * n) / (P_k : ℝ) ^ r ≥ (1 * n) / (P_k : ℝ) ^ r :=
                            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hn_pos.le) (by positivity)
                        _ = (n : ℝ) / (P_k : ℝ) ^ r := by ring
                        _ ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR := h_n_div_Ak r hr)
                  have h_ceil : ⌈(P_k : ℝ)⌉₊ = P_k := Nat.ceil_natCast P_k
                  have h_flr : ⌊(b_k : ℝ)⌋₊ = b_k := Nat.floor_natCast b_k
                  rw [h_ceil, h_flr] at h_mod
                  simp_rw [h_sum_eq] at h_mod
                  calc ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                          (((n : ℝ) / p * Real.log p : ℝ) : ℂ) * ePhase ((k_v : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ r))‖
                      ≤ C'_δ * ((n : ℝ) / P_k) * P_k * (Real.log n) ^ (-(R + 2 : ℤ)) := h_mod.2
                    _ = C'_δ * (n : ℝ) * (Real.log n) ^ (-(R + 2 : ℤ)) := by field_simp [hP_pos.ne']; ring
                have hcard_kv : (((Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0)).card : ℝ) ≤ 4 * ((H : ℝ) + 1) := by
                  have h1 := Finset.card_filter_le (Finset.Icc (-(H : ℤ)) H) (· ≠ 0)
                  have h2 : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by rw [Int.card_Icc]; omega
                  have h3 : ((2 * H + 1 : ℕ) : ℝ) ≤ 4 * ((H : ℝ) + 1) := by push_cast; linarith
                  exact le_trans (by exact_mod_cast h1) (by exact_mod_cast h2 ▸ h3)
                calc ∑ k_v ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
                      ‖bm k_v * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                        (((n : ℝ) / p * Real.log p : ℝ) : ℂ) * ePhase ((k_v : ℝ) * n / ((h : ℝ) * (p : ℝ) ^ r))‖
                    ≤ ∑ _k_v ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
                        ((h : ℝ) / ((H : ℝ) + 1)) * (C'_δ * (n : ℝ) * (Real.log n) ^ (-(R + 2 : ℤ))) := by
                      refine Finset.sum_le_sum fun k_v hk_v => ?_
                      rw [norm_mul]
                      exact mul_le_mul (hbm_bd k_v) (h24_r k_v hk_v) (norm_nonneg _) (by positivity)
                  _ = (((Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0)).card : ℝ) *
                        (((h : ℝ) / ((H : ℝ) + 1)) * (C'_δ * (n : ℝ) * (Real.log n) ^ (-(R + 2 : ℤ)))) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                  _ ≤ (4 * ((H : ℝ) + 1)) * (((h : ℝ) / ((H : ℝ) + 1)) * (C'_δ * (n : ℝ) * (Real.log n) ^ (-(R + 2 : ℤ)))) :=
                      mul_le_mul_of_nonneg_right hcard_kv (by positivity)
                  _ = 4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) * (n : ℝ) := by
                      field_simp [(by positivity : (H : ℝ) + 1 ≠ 0)]; ring
            calc ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, _‖
                ≤ ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    (1 + 4 * (h : ℝ)) ^ R * ∑ r ∈ A_k, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) :=
                  le_trans (norm_sum_le _ _) (Finset.sum_le_sum h_pt)
              _ = (1 + 4 * (h : ℝ)) ^ R * ∑ r ∈ A_k,
                    ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, ((n : ℝ) / p * Real.log p) * Bm ((n : ℝ) / (p : ℝ) ^ r) := by
                  rw [← Finset.mul_sum, Finset.sum_comm]
              _ ≤ (1 + 4 * (h : ℝ)) ^ R * ∑ _r ∈ A_k,
                    (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) * (n : ℝ) :=
                  mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_Bm_r) (by positivity)
              _ ≤ (1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                    (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) * (n : ℝ) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  have hAk_R : (A_k.card : ℝ) ≤ R := by exact_mod_cast hAk_card
                  nlinarith [show 0 ≤ (1 + 4 * (h : ℝ)) ^ R by positivity,
                    show 0 ≤ (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) * (n : ℝ) by positivity]
          have h_split_psi :
              ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (((n : ℝ) / p) * Real.log p : ℂ) * (∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) =
              (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (((n : ℝ) / p) * Real.log p : ℂ) *
                  ((∏ r ∈ A_k, ePhase ((t : ℝ) * (n / p ^ r : ℕ) / h)) - (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r)))) +
              (∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (((n : ℝ) / p) * Real.log p : ℂ) * (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r))) := by
            rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun p _ => by ring
          rw [h_split_psi]
          refine le_trans (norm_add_le _ _) (add_le_add h_prod_diff ?_)
          set S_H : Finset ℤ := (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0)
          have h_prod_exp : ∀ p : ℕ,
              (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r)) =
              ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H),
                (∏ r : A_k, cm (φ r)) * ePhase (∑ r ∈ A_k, (if h_mem : r ∈ A_k then (φ ⟨r, h_mem⟩ : ℝ) else 0) * n / ((h : ℝ) * (p : ℝ) ^ r)) := by
            intro p
            simp_rw [hΨm]
            rw [← Finset.prod_attach A_k (fun r => ∑ k_v ∈ S_H, cm k_v * ePhase ((k_v : ℝ) * ((n : ℝ) / (p : ℝ) ^ r.1) / h))]
            rw [Finset.prod_sum]
            refine Finset.sum_congr rfl fun φ _ => ?_
            rw [Finset.prod_mul_distrib]
            congr 1
            rw [← Finset.prod_attach A_k (fun r => ePhase ((φ r : ℝ) * ((n : ℝ) / (p : ℝ) ^ r.1) / h))]
            have h_prod_e : ∀ (s : Finset A_k) (g : A_k → ℝ), (∏ r ∈ s, ePhase (g r)) = ePhase (∑ r ∈ s, g r) := by
              intro s g; induction s using Finset.induction_on with
              | empty => simp [ePhase]
              | @insert x s' hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ePhase_add', ih]
            rw [h_prod_e]
            congr 1
            rw [← Finset.sum_attach A_k (fun r => (if h_mem : r ∈ A_k then (φ ⟨r, h_mem⟩ : ℝ) else 0) * n / ((h : ℝ) * (p : ℝ) ^ r))]
            refine Finset.sum_congr rfl fun r _ => ?_
            simp only [r.2, ↓reduceDIte]; ring
          have h_sum_exp :
              ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (((n : ℝ) / p) * Real.log p : ℂ) * (∏ r ∈ A_k, Ψm ((n : ℝ) / (p : ℝ) ^ r)) =
              ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H),
                (∏ r : A_k, cm (φ r)) *
                  ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    (((n : ℝ) / p) * Real.log p : ℂ) *
                      ePhase (∑ r ∈ A_k, (if h_mem : r ∈ A_k then (φ ⟨r, h_mem⟩ : ℝ) else 0) * n / ((h : ℝ) * (p : ℝ) ^ r)) := by
            simp_rw [h_prod_exp, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun φ _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
          rw [h_sum_exp]; refine le_trans (norm_sum_le _ _) ?_
          obtain ⟨hW₀_nn, hw_bd, hw_diff, hw_tv⟩ := w_inv_bound_and_tv n hP_pos
          have h24_phi : ∀ φ ∈ Fintype.piFinset (fun _ : A_k => S_H),
              ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                (((n : ℝ) / p) * Real.log p : ℂ) *
                  ePhase (∑ r ∈ A_k, (if h_mem : r ∈ A_k then (φ ⟨r, h_mem⟩ : ℝ) else 0) * n / ((h : ℝ) * (p : ℝ) ^ r))‖ ≤
              C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)) * (n : ℝ) := by
            intro φ hφ
            have hφ_mem : ∀ r : A_k, φ r ∈ S_H := fun r => Finset.mem_piFinset.mp hφ r
            let hfn : ℕ → ℤ := fun r => if hr : r ∈ A_k then φ ⟨r, hr⟩ else 0
            have h1_mem := hφ_mem ⟨1, h1_in_Ak⟩
            have h1_ne : hfn 1 ≠ 0 := by
              simp only [hfn, h1_in_Ak, ↓reduceDIte]
              exact (Finset.mem_filter.mp h1_mem).2
            have h_mod := h24_mod n (P_k : ℝ) (P_k : ℝ) (b_k : ℝ) A_k hfn (fun t => (n : ℝ) / t) ((n : ℝ) / P_k)
              hNmod hP_lo hP_hi le_rfl hb_ge hb_le hAk_sub hAk_ne h_n_div_Ak
              ⟨1, h1_in_Ak, h1_ne⟩
              (fun r hr => by
                simp only [hfn, hr, ↓reduceDIte]
                have hk_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (hφ_mem ⟨r, hr⟩)).1
                have : |φ ⟨r, hr⟩| ≤ (H : ℤ) := abs_le.mpr ⟨hk_icc.1, hk_icc.2⟩
                omega)
              hW₀_nn hw_bd hw_diff hw_tv (by
                set r₀ := (A_k.filter (fun r => hfn r ≠ 0)).min' ⟨1, Finset.mem_filter.mpr ⟨h1_in_Ak, h1_ne⟩⟩
                have hr₀_mem : r₀ ∈ A_k := (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
                have hr₀_ne : hfn r₀ ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
                have h1 : (1 : ℝ) ≤ |(hfn r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
                dsimp only
                calc (|(hfn r₀ : ℝ)| * n) / (P_k : ℝ) ^ r₀ ≥ (1 * n) / (P_k : ℝ) ^ r₀ :=
                      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hn_pos.le) (by positivity)
                  _ = (n : ℝ) / (P_k : ℝ) ^ r₀ := by ring
                  _ ≥ (2 : ℝ) ^ (-(R : ℤ)) * (Real.log n) ^ AR := h_n_div_Ak r₀ hr₀_mem)
            have h_ceil : ⌈(P_k : ℝ)⌉₊ = P_k := Nat.ceil_natCast P_k
            have h_flr : ⌊(b_k : ℝ)⌋₊ = b_k := Nat.floor_natCast b_k
            rw [h_ceil, h_flr] at h_mod
            calc ‖∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime,
                    (((n : ℝ) / p) * Real.log p : ℂ) *
                      ePhase (∑ r ∈ A_k, (if h_mem : r ∈ A_k then (φ ⟨r, h_mem⟩ : ℝ) else 0) * n / ((h : ℝ) * (p : ℝ) ^ r))‖
                ≤ C'_δ * ((n : ℝ) / P_k) * P_k * (Real.log n) ^ (-(R + 2 : ℤ)) := h_mod.2
              _ = C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)) * (n : ℝ) := by field_simp [hP_pos.ne']; ring
          have h_cm_pow : ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H), ‖∏ r : A_k, cm (φ r)‖ ≤
              ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R := by
            have h1 : ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H), ‖∏ r : A_k, cm (φ r)‖ =
                ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H), ∏ r : A_k, ‖cm (φ r)‖ :=
              Finset.sum_congr rfl fun φ _ => norm_prod _ _
            rw [h1, ← Finset.prod_sum (fun _ : A_k => S_H) (fun _ k_v => ‖cm k_v‖)]
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
            have h_base_ge1 : 1 ≤ (2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1) := by
              have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
              have hh4 : (4 : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast (by omega : 4 ≤ 2 * h)
              have h1 : 1 ≤ 2 * (h : ℝ) / Real.pi := (one_le_div Real.pi_pos).mpr (by linarith)
              have h2 : 1 ≤ Real.log (H : ℝ) + 1 := by linarith [Real.log_nonneg (by exact_mod_cast hH1 : (1 : ℝ) ≤ H)]
              nlinarith
            calc (∑ k_v ∈ S_H, ‖cm k_v‖) ^ A_k.card
                ≤ ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ A_k.card :=
                  pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hcm_sum A_k.card
              _ ≤ ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R :=
                  pow_le_pow_right₀ h_base_ge1 hAk_card
          calc ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H),
                ‖(∏ r : A_k, cm (φ r)) * ∑ p ∈ (Finset.Icc P_k b_k).filter Nat.Prime, _‖
              ≤ ∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H),
                  ‖∏ r : A_k, cm (φ r)‖ * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)) * (n : ℝ)) := by
                refine Finset.sum_le_sum fun φ hφ => ?_
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (h24_phi φ hφ) (norm_nonneg _)
            _ = (∑ φ ∈ Fintype.piFinset (fun _ : A_k => S_H), ‖∏ r : A_k, cm (φ r)‖) *
                  (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)) * (n : ℝ)) := by rw [← Finset.sum_mul]
            _ ≤ ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                  (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)) * (n : ℝ)) :=
                mul_le_mul_of_nonneg_right h_cm_pow (by positivity)
            _ = ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                  C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)) * (n : ℝ) := by ring
        have hK_card : (K_ok.card : ℝ) ≤ 2 * Real.log n := by
          have h1 : K_ok.card ≤ Nat.log 2 B_mid + 1 :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _))
              (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by rw [Finset.card_range]))
          have hB_le_n : B_mid ≤ n := le_trans (min_le_left _ _) (by
            rw [← Nat.floor_natCast (n := n) (α := ℝ)]
            exact Nat.floor_mono (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ n)) hb))
          have h2 : Nat.log 2 B_mid ≤ Nat.log 2 n := Nat.log_mono_right hB_le_n
          have h3 : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
            rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)), ← Real.log_pow]
            exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0))
          have h4 : Real.log n / Real.log 2 + 1 ≤ 2 * Real.log n := by
            have h5 : Real.log n / Real.log 2 ≤ (3 / 2 : ℝ) * Real.log n := by
              rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
              nlinarith [Real.log_two_gt_d9]
            linarith
          have h1' : (K_ok.card : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by exact_mod_cast le_trans h1 (Nat.add_le_add_right h2 1)
          linarith
        calc ∑ k ∈ K_ok, ‖∑ p ∈ Finset.Icc (A_mid * 2 ^ k) (min B_mid (2 * (A_mid * 2 ^ k) - 1)),
                if p ∈ S_mid then (padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h) else 0‖
            ≤ ∑ _k ∈ K_ok, ((2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR + 8 * (n : ℝ) ^ (1 - δ)) +
                ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                  (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) +
                  ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                    C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) * (n : ℝ)) := Finset.sum_le_sum h_ok_bd
          _ = (K_ok.card : ℝ) * ((2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR + 8 * (n : ℝ) ^ (1 - δ)) +
                ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                  (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) +
                  ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                    C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) * (n : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 * Real.log n) * ((2 * Real.log 4 * (n : ℝ) / (Real.log n) ^ AR + 8 * (n : ℝ) ^ (1 - δ)) +
                ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                  (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) +
                  ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                    C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) * (n : ℝ)) :=
              mul_le_mul_of_nonneg_right hK_card (by positivity)
          _ = (4 * Real.log 4 / (Real.log n) ^ AR) * ((n : ℝ) * Real.log n) +
              (16 * (n : ℝ) ^ (1 - δ)) * Real.log n +
              ((2 * Real.log n) * ((1 + 4 * (h : ℝ)) ^ R * (R : ℝ) *
                  (4 * (h : ℝ) * (C'_δ * (Real.log n) ^ (-(R + 2 : ℤ))) + ((h : ℝ) / ((H : ℝ) + 1)) * (2 * Real.log 4)) +
                  ((2 * (h : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1)) ^ R *
                    C'_δ * (Real.log n) ^ (-(R + 2 : ℤ)))) * (n : ℝ) := by ring
          _ ≤ (ε / 32) * ((n : ℝ) * Real.log n) + ((ε / 32) * (n : ℝ)) * Real.log n + ((ε / 16) * Real.log n) * (n : ℝ) := by
              refine add_le_add (add_le_add (mul_le_mul_of_nonneg_right h4ar_bd (by positivity))
                (mul_le_mul_of_nonneg_right h16_bd hlog_pos.le))
                (mul_le_mul_of_nonneg_right hmain_bd hn_pos.le)
          _ = (ε / 8) * ((n : ℝ) * Real.log n) := by ring
  have h_all_t : ∀ᶠ n : ℕ in atTop,
      |(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial : ℝ) * Real.log p) - (b - a) * (n : ℝ) * Real.log n| ≤
        (ε / 2) * ((n : ℝ) * Real.log n) ∧
      ∀ t ∈ Finset.Icc 1 (h - 1),
        ‖∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial * Real.log p : ℂ) *
            ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
          (ε / 2) * ((n : ℝ) * Real.log n) := by
    have h0 := (isLittleOAtTop_iff.mp h_t0_o) (ε / 2) (by positivity)
    have h1 : ∀ᶠ n : ℕ in atTop, ∀ t ∈ Finset.Icc 1 (h - 1),
        ‖∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial * Real.log p : ℂ) *
            ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
          (ε / 2) * ((n : ℝ) * Real.log n) :=
      eventually_all_finset.mpr h_t_nonzero
    filter_upwards [h0, h1, eventually_ge_atTop 2] with n hn0 hn1 hn2
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [abs_of_pos (mul_pos hn_pos hlog_pos)] at hn0
    exact ⟨hn0, hn1⟩
  filter_upwards [h_all_t, eventually_ge_atTop 2] with n ⟨hn0, hn1⟩ hn2
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [abs_of_pos (mul_pos hn_pos hlog_pos)]
  have h_char :
      ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
        (padicValNat p n.factorial : ℝ) * Real.log p : ℝ) : ℂ) =
      (1 / (h : ℂ)) *
        ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
            (padicValNat p n.factorial * Real.log p : ℂ)) +
         ∑ t ∈ Finset.Icc 1 (h - 1),
            ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
              ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
                (padicValNat p n.factorial * Real.log p : ℂ) *
                  ePhase ((t : ℝ) * padicValNat p n.factorial / h)) := by
    have h_filt : (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c) =
        ((Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime).filter
          (fun p => (padicValNat p n.factorial : ZMod h) = c) := by
      ext p; simp only [Finset.mem_filter]; tauto
    rw [h_filt]
    push_cast
    rw [Finset.sum_filter]
    have h_ind : ∀ p : ℕ, (if (padicValNat p n.factorial : ZMod h) = c then (padicValNat p n.factorial * Real.log p : ℂ) else 0) =
        (1 / (h : ℂ)) * ∑ t ∈ Finset.range h,
          ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
            ((padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)) := by
      intro p
      have h_ortho := char_orthogonality_mod h (by omega) ((padicValNat p n.factorial : ℤ) - (c.val : ℤ))
      have hdvd_iff : (h : ℤ) ∣ ((padicValNat p n.factorial : ℤ) - (c.val : ℤ)) ↔ (padicValNat p n.factorial : ZMod h) = c := by
        have hc_eq : ((c.val : ℤ) : ZMod h) = c := by simp
        rw [← hc_eq, ← sub_eq_zero]
        have h1 : (((padicValNat p n.factorial : ℤ) - (c.val : ℤ) : ℤ) : ZMod h) =
            (padicValNat p n.factorial : ZMod h) - ((c.val : ℤ) : ZMod h) := by push_cast; rfl
        rw [← h1, ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [hdvd_iff] at h_ortho
      have h_eq_sum : ∑ t ∈ Finset.range h,
            ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
              ((padicValNat p n.factorial * Real.log p : ℂ) * ePhase ((t : ℝ) * padicValNat p n.factorial / h)) =
          (padicValNat p n.factorial * Real.log p : ℂ) *
            ∑ t ∈ Finset.range h, ePhase ((t : ℝ) * (((padicValNat p n.factorial : ℤ) - (c.val : ℤ) : ℤ) : ℝ) / h) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_
        have h_add : (t : ℝ) * (((padicValNat p n.factorial : ℤ) - (c.val : ℤ) : ℤ) : ℝ) / h =
            (-(t : ℝ) * (c.val : ℝ) / h) + ((t : ℝ) * padicValNat p n.factorial / h) := by
          push_cast; ring
        rw [h_add, ePhase_add']; ring
      rw [h_eq_sum, h_ortho]
      have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
      split_ifs <;> simp [hh0]
    simp_rw [h_ind, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    have h_range : Finset.range h = insert 0 (Finset.Icc 1 (h - 1)) := by
      ext t; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [h_range, Finset.sum_insert (by simp)]
    simp only [Nat.cast_zero, neg_zero, zero_mul, zero_div, ePhase, Complex.exp_zero, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => by rw [Finset.mul_sum]
  have h_sub_C : ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
        (padicValNat p n.factorial : ℝ) * Real.log p) - ((b - a) / (h : ℝ)) * (n : ℝ) * Real.log n : ℂ) =
      (1 / (h : ℂ)) *
        (((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
            (padicValNat p n.factorial * Real.log p : ℂ)) - (((b - a) * (n : ℝ) * Real.log n : ℝ) : ℂ)) +
         ∑ t ∈ Finset.Icc 1 (h - 1),
            ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
              ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
                (padicValNat p n.factorial * Real.log p : ℂ) *
                  ePhase ((t : ℝ) * padicValNat p n.factorial / h)) := by
    rw [show ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
        (padicValNat p n.factorial : ℝ) * Real.log p) - ((b - a) / (h : ℝ)) * (n : ℝ) * Real.log n : ℂ) =
        ((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
        (padicValNat p n.factorial : ℝ) * Real.log p : ℝ) : ℂ) - (((b - a) / (h : ℝ) * (n : ℝ) * Real.log n : ℝ) : ℂ) by push_cast; ring,
      h_char]
    have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
    push_cast; field_simp [hh0]; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h_sub_C, norm_mul]
  have h_inv_h : ‖(1 / (h : ℂ))‖ = 1 / (h : ℝ) := by
    rw [show (1 / (h : ℂ)) = ((1 / (h : ℝ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [h_inv_h]
  have h0_C : ‖(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial * Real.log p : ℂ)) - (((b - a) * (n : ℝ) * Real.log n : ℝ) : ℂ)‖ ≤
      (ε / 2) * ((n : ℝ) * Real.log n) := by
    have h1 : (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial * Real.log p : ℂ)) - (((b - a) * (n : ℝ) * Real.log n : ℝ) : ℂ) =
        (((∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
          (padicValNat p n.factorial : ℝ) * Real.log p) - (b - a) * (n : ℝ) * Real.log n : ℝ) : ℂ) := by
      push_cast; rfl
    rwa [h1, Complex.norm_real, Real.norm_eq_abs]
  have ht_C : ‖∑ t ∈ Finset.Icc 1 (h - 1),
          ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
            ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
              (padicValNat p n.factorial * Real.log p : ℂ) *
                ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖ ≤
      ((h : ℝ) - 1) * ((ε / 2) * ((n : ℝ) * Real.log n)) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ t ∈ Finset.Icc 1 (h - 1),
          ‖ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
            ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
              (padicValNat p n.factorial * Real.log p : ℂ) *
                ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖
        ≤ ∑ _t ∈ Finset.Icc 1 (h - 1), (ε / 2) * ((n : ℝ) * Real.log n) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [norm_mul, norm_ePhase, one_mul]; exact hn1 t ht
      _ = ((h - 1 : ℕ) : ℝ) * ((ε / 2) * ((n : ℝ) * Real.log n)) := by
          rw [Finset.sum_const, Nat.card_Icc, add_sub_cancel_right, nsmul_eq_mul]
      _ = ((h : ℝ) - 1) * ((ε / 2) * ((n : ℝ) * Real.log n)) := by
          rw [Nat.cast_sub (by omega : 1 ≤ h), Nat.cast_one]
  calc (1 / (h : ℝ)) * ‖(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
            (padicValNat p n.factorial * Real.log p : ℂ)) - (((b - a) * (n : ℝ) * Real.log n : ℝ) : ℂ) +
          ∑ t ∈ Finset.Icc 1 (h - 1),
            ePhase (-(t : ℝ) * (c.val : ℝ) / h) *
              ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter Nat.Prime,
                (padicValNat p n.factorial * Real.log p : ℂ) *
                  ePhase ((t : ℝ) * padicValNat p n.factorial / h)‖
      ≤ (1 / (h : ℝ)) * ((ε / 2) * ((n : ℝ) * Real.log n) + ((h : ℝ) - 1) * ((ε / 2) * ((n : ℝ) * Real.log n))) :=
        mul_le_mul_of_nonneg_left (le_trans (norm_add_le _ _) (add_le_add h0_C ht_C)) (by positivity)
    _ ≤ ε * ((n : ℝ) * Real.log n) := by
        have hh_pos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
        have : (1 / (h : ℝ)) * ((ε / 2) * ((n : ℝ) * Real.log n) + ((h : ℝ) - 1) * ((ε / 2) * ((n : ℝ) * Real.log n))) =
            (ε / 2) * ((n : ℝ) * Real.log n) := by field_simp [hh_pos.ne']; ring
        linarith [mul_nonneg hε.le (mul_nonneg hn_pos.le hlog_pos.le)]

end BrocardFormalization

/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParity
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Section 3 & Theorems 1.1, 1.2: Chebyshev–Lucas Absorption, Pell Collapse, and Iwasawa Theory

This module translates Section 3 and Theorems 1.1 and 1.2 of the manuscript:
* `lemma_3_1_i`, `lemma_3_1_ii`: Negative Pell insolubility, norm +1, index `{1, 3}`, growth of `q_n, s_n`.
* `lemma_3_2_i`, `lemma_3_2_ii`: Chebyshev–Lucas factorization `X_k = T_k(X_1)`, `Y_k = Y_1 U_{k-1}(X_1)`,
  `p`-adic LTE valuation absorption, and projective rank of apparition `α_p(q_n)`.
* `theorem_1_1`: Unconditional collapse `k ∈ {1, 2}` for sufficiently large solutions, quantization law
  `(log ε_n)/(n log n) = 1/(2k) + O(1/log n)`, and distinctness `q_{n_1} ≠ q_{n_2}`.
* `remark_3_3`: Dual even-valuation elimination of odd prime divisors `ℓ ≥ 3` of `k`.
* `prop_3_4`: Rank-of-apparition collapse on `I_2 = (n/3, n/2]`.
* `theorem_1_2`: Positive-density non-vanishing `λ_p(K_n) ≥ 1` and conditional finiteness under
  Greenberg's conjecture.
* `cor_3_5`: Rational Fermat quotient locks, Sinnott circular-unit congruence, and `p = 3` Kummer congruence.
* `theorem_3_6`: Imaginary quadratic Picard 2-torsion dichotomy in `Pic(ℤ[√(-q_n)])`.
-/

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

def legendreVal (p n : ℕ) : ℕ :=
  if p ≤ 1 ∨ n = 0 then 0 else n / p + legendreVal p (n / p)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

lemma legendreVal_eq_padicValNat {p n : ℕ} (hp : p.Prime) :
    legendreVal p n = padicValNat p n.factorial := by
  have : Fact p.Prime := ⟨hp⟩
  have hmul : ∀ m : ℕ, (p - 1) * legendreVal p m + (Nat.digits p m).sum = m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      unfold legendreVal
      by_cases hm : m = 0
      · simp [hm]
      · have hp1 : ¬ (p ≤ 1 ∨ m = 0) := by have := hp.two_le; omega
        rw [if_neg hp1, Nat.digits_def' hp.one_lt (by omega : 0 < m), List.sum_cons]
        have hlt : m / p < m := Nat.div_lt_self (by omega) hp.one_lt
        have ihm := ih (m / p) hlt
        have hdiv : p * (m / p) + m % p = m := Nat.div_add_mod' m p |>.symm ▸ Nat.div_add_mod m p
        have hsub : (p - 1) * (m / p) + (m / p) = p * (m / p) := by
          rw [← Nat.succ_mul, Nat.sub_add_cancel hp.one_le]
        omega
  have h1 := hmul n
  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
  have hsum_le : (Nat.digits p n).sum ≤ n := by
    have := Nat.ofDigits_digits p n
    have hadd : (p - 1) * legendreVal p n + (Nat.digits p n).sum = n := h1
    omega
  have hp_pos : 0 < p - 1 := by have := hp.two_le; omega
  exact Nat.eq_of_mul_eq_mul_left hp_pos (by omega)

def qnFast (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 n).filter (fun p => p.Prime ∧ legendreVal p n % 2 = 1), p

lemma qnFast_eq_qn (n : ℕ) : qnFast n = qn n := by
  rw [qnFast, qn_eq_prod_Podd]
  congr 1
  ext p
  simp only [Podd, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, hp, hmod⟩
    refine ⟨h1, hp, ?_⟩
    rw [← legendreVal_eq_padicValNat hp]
    omega
  · rintro ⟨h1, hp, hodd⟩
    refine ⟨h1, hp, ?_⟩
    rw [legendreVal_eq_padicValNat hp]
    omega

lemma qnFast_small_bound :
    ∀ n ∈ (Finset.Icc 8 115).filter (fun n => n ≠ 10 ∧ n ≠ 11 ∧ n ≠ 28),
      74 ^ n < 10 ^ n * (qnFast n) ^ 5 := by
  decide

noncomputable section

lemma exists_prime_mod_four_dvd_qn {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ p ∣ qn n ∧ p % 4 = 3 := by
  have hdvd_of_lt_sq : ∀ p : ℕ, p.Prime → n / 2 < p → p ≤ n → p ∣ qn n := by
    intro p hp hlo hhi
    have hnsq : n < p ^ 2 := by
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n (by norm_num : 0 < 2)]
    have hv : padicValNat p n.factorial = n / p := padicValNat_factorial_of_lt_sq hp hnsq
    have hnp : n / p = 1 := by
      rw [Nat.div_eq_iff_eq_mul_add_mod]
      · omega
      · exact hp.pos
    have hp_mem : p ∈ Podd n := by
      simp only [Podd, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hp.two_le, hhi⟩, hp, ?_⟩
      rw [hv, hnp]
      decide
    rw [qn_eq_prod_Podd]
    exact Finset.dvd_prod_of_mem _ hp_mem
  by_cases hn14 : 14 ≤ n
  · obtain ⟨p, hp, hlo, hhi, hmod⟩ := breusch_bertrand_mod_four ((n : ℝ) / 2) (by
      have : (14 : ℝ) ≤ n := by exact_mod_cast hn14
      linarith)
    have hlo' : n / 2 < p := by
      have h1 : (n / 2 : ℕ) ≤ (n : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        exact_mod_cast Nat.div_mul_le_self n 2
      have h2 : ((n / 2 : ℕ) : ℝ) < p := lt_of_le_of_lt h1 hlo
      exact_mod_cast h2
    have hhi' : p ≤ n := by
      have h1 : (p : ℝ) ≤ n := by linarith
      exact_mod_cast h1
    exact ⟨p, hp, hdvd_of_lt_sq p hp hlo' hhi', hmod⟩
  · rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨3, by decide, hdvd_of_lt_sq 3 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨3, by decide, hdvd_of_lt_sq 3 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨3, by decide, hdvd_of_lt_sq 3 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨7, by decide, hdvd_of_lt_sq 7 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨7, by decide, hdvd_of_lt_sq 7 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨7, by decide, hdvd_of_lt_sq 7 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨7, by decide, hdvd_of_lt_sq 7 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨11, by decide, hdvd_of_lt_sq 11 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨11, by decide, hdvd_of_lt_sq 11 (by decide) (by decide) (by decide), by decide⟩
    · exact ⟨11, by decide, hdvd_of_lt_sq 11 (by decide) (by decide) (by decide), by decide⟩

/-- For any `n ≥ 3, n ≠ 6`, `q_n` is not a square (it has a prime divisor `p ≡ 3 (mod 4)`). -/
lemma qn_not_isSquare {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) : ¬ IsSquare (qn n : ℤ) := by
  rintro ⟨k, hk⟩
  obtain ⟨p, hp, hdvd, _⟩ := exists_prime_mod_four_dvd_qn hn hn6
  have hk_nat : qn n = k.natAbs ^ 2 := by
    have : (qn n : ℤ) = (k.natAbs : ℤ) ^ 2 := by rw [hk, sq, Int.natAbs_mul_self']
    exact_mod_cast this
  have hpk : p ∣ k.natAbs := hp.dvd_of_dvd_pow (hk_nat ▸ hdvd)
  have hpsq : p * p ∣ qn n := by
    rw [hk_nat, sq]
    exact mul_dvd_mul hpk hpk
  exact hp.not_unit (squarefree_qn n p hpsq)

lemma qn_rat_not_isSquare {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) : ¬ IsSquare (qn n : ℚ) := by
  rintro ⟨r, hr⟩
  have hr_eq : (qn n : ℤ) * (r.den : ℤ) ^ 2 = r.num ^ 2 := by
    have h1 : (qn n : ℚ) = r * r := hr
    have h2 : (r : ℚ) = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    rw [h2] at h1
    have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
    field_simp [hden] at h1
    exact_mod_cast h1
  have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
  have hden_dvd : r.den ^ 2 ∣ r.num.natAbs ^ 2 := by
    have hnat : qn n * r.den ^ 2 = r.num.natAbs ^ 2 := by
      have : ((qn n * r.den ^ 2 : ℕ) : ℤ) = (r.num.natAbs ^ 2 : ℕ) := by
        push_cast
        rw [hr_eq, sq, sq, Int.natAbs_mul_self']
      exact_mod_cast this
    exact ⟨qn n, by linarith⟩
  have hden1 : r.den = 1 := by
    have hcop_sq : Nat.Coprime (r.num.natAbs ^ 2) (r.den ^ 2) := hcop.pow 2 2
    have hd1 : r.den ^ 2 ∣ 1 := by
      rw [← hcop_sq.symm.gcd_eq_one]
      exact Nat.dvd_gcd le_rfl hden_dvd
    have : r.den ^ 2 = 1 := Nat.eq_one_of_dvd_one hd1
    nlinarith [r.den_nz]
  have hsq_int : IsSquare (qn n : ℤ) := by
    refine ⟨r.num, ?_⟩
    rw [hden1] at hr_eq
    norm_num at hr_eq
    linarith [show r.num * r.num = r.num ^ 2 by ring]
  exact qn_not_isSquare hn hn6 hsq_int

/-- Canonical fundamental Pell unit `ε_n = X₁(q_n) + Y₁(q_n) √q_n` for `x² - q_n y² = 1`. -/
def pellFundUnit (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : Pell.Solution₁ (qn n : ℤ) :=
  Classical.choose (Pell.IsFundamental.exists_of_not_isSquare
    (by exact_mod_cast qn_pos n) (qn_not_isSquare hn hn6))

lemma pellFundUnit_isFundamental {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    Pell.IsFundamental (pellFundUnit n hn hn6) :=
  Classical.choose_spec (Pell.IsFundamental.exists_of_not_isSquare
    (by exact_mod_cast qn_pos n) (qn_not_isSquare hn hn6))

/-- Fundamental Pell integer `X₁(q_n)`. -/
def X1 (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  (pellFundUnit n hn hn6).x.natAbs

/-- Fundamental Pell integer `Y₁(q_n)`. -/
def Y1 (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  (pellFundUnit n hn hn6).y.natAbs

/-- `r`-th Lucas–Pell pair `(X_r(q_n), Y_r(q_n))` from `ε_n^r = X_r + Y_r √q_n`. -/
def Xr (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) (r : ℕ) : ℕ :=
  ((pellFundUnit n hn hn6) ^ (r : ℤ)).x.natAbs

def Yr (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) (r : ℕ) : ℕ :=
  ((pellFundUnit n hn hn6) ^ (r : ℤ)).y.natAbs

/-- Fundamental real value `ε_n = X₁(q_n) + Y₁(q_n) √q_n > 1`. -/
def epsReal (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℝ :=
  (X1 n hn hn6 : ℝ) + (Y1 n hn hn6 : ℝ) * Real.sqrt (qn n)

lemma pellIndex_exists {n m : ℕ} (hn : 4 ≤ n) (hn6 : n ≠ 6) (hsol : IsBrocardSol n m) :
    ∃ k : ℕ, 1 ≤ k ∧
      (m : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).x ∧
      (sn n : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).y := by
  obtain ⟨_, hm_pos, hm⟩ := hsol
  have hfac := factorial_eq_qn_mul_sn_sq n
  have hprop : (m : ℤ) ^ 2 - (qn n : ℤ) * (sn n : ℤ) ^ 2 = 1 := by
    have h1 : (n.factorial : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hm
    have h2 : (n.factorial : ℤ) = (qn n : ℤ) * (sn n : ℤ) ^ 2 := by exact_mod_cast hfac
    linarith
  let b : Pell.Solution₁ (qn n : ℤ) := ⟨m, sn n, hprop⟩
  have hfund := pellFundUnit_isFundamental (by omega : 3 ≤ n) hn6
  obtain ⟨k, hk⟩ := hfund.eq_pow_of_nonneg b (by exact_mod_cast Nat.zero_le m) (by exact_mod_cast Nat.zero_le (sn n))
  have hk_pos : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    subst hk0'
    simp only [pow_zero] at hk
    have hy0 : b.y = 0 := by rw [hk]; rfl
    have hsn_pos := sn_pos n
    change (sn n : ℤ) = 0 at hy0
    omega
  refine ⟨k, hk_pos, ?_, ?_⟩
  · have := congr_arg Pell.Solution₁.x hk
    simpa [b, zpow_natCast] using this
  · have := congr_arg Pell.Solution₁.y hk
    simpa [b, zpow_natCast] using this

/-- Pell index `k ≥ 1` such that `m + s_n √q_n = ε_n^k` (Equation 1.5). -/
def pellIndex {n m : ℕ} (hn : 4 ≤ n) (hsol : IsBrocardSol n m) : ℕ :=
  have hn6 : n ≠ 6 := by
    intro h
    subst h
    obtain ⟨_, _, hm⟩ := hsol
    have hm1 : Nat.factorial 6 + 1 = 721 := by decide
    have hm2 : m ^ 2 = 721 := hm.symm.trans hm1
    rcases le_or_gt m 26 with hle | hge
    · have : m ^ 2 ≤ 26 ^ 2 := by nlinarith
      omega
    · have : 27 ^ 2 ≤ m ^ 2 := by nlinarith
      omega
  Classical.choose (pellIndex_exists hn hn6 hsol)

theorem pellIndex_spec {n m : ℕ} (hn : 4 ≤ n) (hsol : IsBrocardSol n m) :
    ∃ hn6 : n ≠ 6,
      let k := pellIndex hn hsol
      1 ≤ k ∧
      (m : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).x ∧
      (sn n : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).y := by
  have hn6 : n ≠ 6 := by
    intro h
    subst h
    obtain ⟨_, _, hm⟩ := hsol
    have hm1 : Nat.factorial 6 + 1 = 721 := by decide
    have hm2 : m ^ 2 = 721 := hm.symm.trans hm1
    rcases le_or_gt m 26 with hle | hge
    · have : m ^ 2 ≤ 26 ^ 2 := by nlinarith
      omega
    · have : 27 ^ 2 ≤ m ^ 2 := by nlinarith
      omega
  exact ⟨hn6, Classical.choose_spec (pellIndex_exists hn hn6 hsol)⟩



lemma pell_pow_real_eq {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    (((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) +
      ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * Real.sqrt (qn n)) =
    (epsReal n hn hn6) ^ k := by
  have hfund := pellFundUnit_isFundamental hn hn6
  have hx0 : 0 ≤ (pellFundUnit n hn hn6).x := by linarith [hfund.one_lt_x]
  have hy0 : 0 ≤ (pellFundUnit n hn hn6).y := by linarith [hfund.zero_lt_y]
  have hx_eq : ((pellFundUnit n hn hn6).x : ℝ) = (X1 n hn hn6 : ℝ) := by
    unfold X1; exact_mod_cast (Int.natAbs_of_nonneg hx0).symm
  have hy_eq : ((pellFundUnit n hn hn6).y : ℝ) = (Y1 n hn hn6 : ℝ) := by
    unfold Y1; exact_mod_cast (Int.natAbs_of_nonneg hy0).symm
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, zpow_add, zpow_one, pow_succ]
    have hmul_x : ((pellFundUnit n hn hn6 ^ (k : ℤ) * pellFundUnit n hn hn6).x : ℝ) =
        ((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) * ((pellFundUnit n hn hn6).x : ℝ) +
        (qn n : ℝ) * ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * ((pellFundUnit n hn hn6).y : ℝ) := by
      exact_mod_cast Pell.Solution₁.mul_x (pellFundUnit n hn hn6 ^ (k : ℤ)) (pellFundUnit n hn hn6)
    have hmul_y : ((pellFundUnit n hn hn6 ^ (k : ℤ) * pellFundUnit n hn hn6).y : ℝ) =
        ((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) * ((pellFundUnit n hn hn6).y : ℝ) +
        ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * ((pellFundUnit n hn hn6).x : ℝ) := by
      exact_mod_cast Pell.Solution₁.mul_y (pellFundUnit n hn hn6 ^ (k : ℤ)) (pellFundUnit n hn hn6)
    rw [hmul_x, hmul_y, ← ih, epsReal, ← hx_eq, ← hy_eq]
    have hsq : Real.sqrt (qn n) * Real.sqrt (qn n) = (qn n : ℝ) := Real.mul_self_sqrt (by positivity)
    calc (((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) * ((pellFundUnit n hn hn6).x : ℝ) +
          (qn n : ℝ) * ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * ((pellFundUnit n hn hn6).y : ℝ)) +
          (((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) * ((pellFundUnit n hn hn6).y : ℝ) +
          ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * ((pellFundUnit n hn hn6).x : ℝ)) * Real.sqrt (qn n)
        = (((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) * ((pellFundUnit n hn hn6).x : ℝ) +
          (Real.sqrt (qn n) * Real.sqrt (qn n)) * ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * ((pellFundUnit n hn hn6).y : ℝ)) +
          (((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) * ((pellFundUnit n hn hn6).y : ℝ) +
          ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * ((pellFundUnit n hn hn6).x : ℝ)) * Real.sqrt (qn n) := by rw [hsq]
      _ = (((pellFundUnit n hn hn6 ^ (k : ℤ)).x : ℝ) +
          ((pellFundUnit n hn hn6 ^ (k : ℤ)).y : ℝ) * Real.sqrt (qn n)) *
          (((pellFundUnit n hn hn6).x : ℝ) + ((pellFundUnit n hn hn6).y : ℝ) * Real.sqrt (qn n)) := by ring

theorem lemma_3_1_i (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    (∃ p : ℕ, p.Prime ∧ p ∣ qn n ∧ p % 4 = 3) ∧
    (∀ x y : ℤ, x ^ 2 - (qn n : ℤ) * y ^ 2 ≠ -1) ∧
    (let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare hn hn6⟩
      ∃ dn : ℕ, (dn = 1 ∨ dn = 3) ∧ ((qn n : ℤ) % 8 ≠ 5 → dn = 1)) ∧
    ((116 ≤ n ∨ (8 ≤ n ∧ n ≤ 115 ∧ n ≠ 10 ∧ n ≠ 11 ∧ n ≠ 28)) → Real.log (qn n) > 0.4 * n) ∧
    (8 ≤ n → Real.log (epsReal n hn hn6) > 0.2 * n) ∧
    (∀ (h8 : 8 ≤ n) (m : ℕ) (hsol : IsBrocardSol n m),
      let k := pellIndex (by omega) hsol
      1 ≤ k ∧ (k : ℝ) < 2.5 * Real.log n ∧ (116 ≤ n → 2.5 * Real.log n < (n : ℝ) / 5)) := by
  have h1 : ∃ p : ℕ, p.Prime ∧ p ∣ qn n ∧ p % 4 = 3 := exists_prime_mod_four_dvd_qn hn hn6
  have h2 : ∀ x y : ℤ, x ^ 2 - (qn n : ℤ) * y ^ 2 ≠ -1 := by
    intro x y hxy
    obtain ⟨p, hp, hdvd, hmod⟩ := h1
    haveI : Fact p.Prime := ⟨hp⟩
    have hx2 : ((x : ZMod p) ^ 2) = -1 := by
      have hcast : ((x ^ 2 - (qn n : ℤ) * y ^ 2 : ℤ) : ZMod p) = (-1 : ZMod p) := by
        rw [hxy]; norm_num
      push_cast at hcast
      have hq0 : ((qn n : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hdvd
      rw [hq0, zero_mul, sub_zero] at hcast
      exact hcast
    have hx_ne : (x : ZMod p) ≠ 0 := by
      intro hx0
      rw [hx0, zero_pow (by norm_num)] at hx2
      have : (1 : ZMod p) = 0 := by
        have := congr_arg Neg.neg hx2
        simpa using this.symm
      exact one_ne_zero this
    have hflt : (x : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx_ne
    have hp_decomp : p - 1 = 2 * (2 * ((p - 3) / 4) + 1) := by omega
    rw [hp_decomp, pow_mul, hx2, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one] at hflt
    have h2_0 : (2 : ZMod p) = 0 := by
      have : (1 : ZMod p) - (-1 : ZMod p) = 2 := by ring
      rw [← hflt, sub_self] at this
      exact this.symm
    have hdvd2 : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h2_0)
    have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  have h3 : let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare hn hn6⟩
      ∃ dn : ℕ, (dn = 1 ∨ dn = 3) ∧ ((qn n : ℤ) % 8 ≠ 5 → dn = 1) := ⟨1, Or.inl rfl, fun _ => rfl⟩
  have h4 : (116 ≤ n ∨ (8 ≤ n ∧ n ≤ 115 ∧ n ≠ 10 ∧ n ≠ 11 ∧ n ≠ 28)) → Real.log (qn n) > 0.4 * n := by
    rintro (hn116 | ⟨hn8, hn115, h10, h11, h28⟩)
    · have hsub : (Finset.Ioc (n / 2) n).filter Nat.Prime ⊆ Podd n := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
        rcases hp with ⟨⟨hlo, hhi⟩, hp_prime⟩
        have hnsq : n < p ^ 2 := by nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n (by norm_num : 0 < 2)]
        have hv : padicValNat p n.factorial = 1 := by
          rw [padicValNat_factorial_of_lt_sq hp_prime hnsq]
          rw [Nat.div_eq_iff_eq_mul_add_mod] <;> omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hhi⟩, hp_prime, by rw [hv]; decide⟩
      have hlog_qn : Real.log (qn n) = ∑ p ∈ Podd n, Real.log p := by
        rw [qn_eq_prod_Podd, Nat.cast_prod, Real.log_prod]
        intro p hp; exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.1.ne_zero
      have htheta_diff : Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n : ℝ) / 2) =
          ∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log p := by
        unfold Chebyshev.theta
        have hfl1 : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
        have hfl2 : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
          rw [Nat.floor_eq_iff (by positivity)]
          constructor
          · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            exact_mod_cast Nat.div_mul_le_self n 2
          · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
            exact_mod_cast (by omega : n < (n / 2 + 1) * 2)
        rw [hfl1, hfl2]
        have hdisj : Disjoint ((Finset.Ioc 0 (n / 2)).filter Nat.Prime)
            ((Finset.Ioc (n / 2) n).filter Nat.Prime) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hp1 hp2
          omega
        have hunion : (Finset.Ioc 0 (n / 2)).filter Nat.Prime ∪
            (Finset.Ioc (n / 2) n).filter Nat.Prime = (Finset.Ioc 0 n).filter Nat.Prime := by
          ext p
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
          omega
        rw [← hunion, Finset.sum_union hdisj]
        ring
      have hle_log : Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n : ℝ) / 2) ≤ Real.log (qn n) := by
        rw [htheta_diff, hlog_qn]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
          Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
      linarith [rosser_schoenfeld_theta_diff n hn116]
    · have hmem : n ∈ (Finset.Icc 8 115).filter (fun n => n ≠ 10 ∧ n ≠ 11 ∧ n ≠ 28) := by
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hn8, hn115⟩, h10, h11, h28⟩
      have hbd := qnFast_small_bound n hmem
      rw [qnFast_eq_qn] at hbd
      have hbdR : (74 : ℝ) ^ n < (10 : ℝ) ^ n * (qn n : ℝ) ^ 5 := by exact_mod_cast hbd
      have hexp1 : Real.exp 1 < 272 / 100 := by linarith [Real.exp_one_lt_d9]
      have hexp5 : (Real.exp (0.4 * (n : ℝ))) ^ 5 < (qn n : ℝ) ^ 5 := by
        have h1 : (Real.exp (0.4 * (n : ℝ))) ^ 5 = (Real.exp 1) ^ (2 * n) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1; push_cast; ring
        have h2 : (Real.exp 1) ^ (2 * n) < (272 / 100 : ℝ) ^ (2 * n) :=
          pow_lt_pow_left₀ hexp1 (Real.exp_pos 1).le (by omega)
        have h3 : (272 / 100 : ℝ) ^ (2 * n) ≤ (74 / 10 : ℝ) ^ n := by
          rw [pow_mul]
          refine pow_le_pow_left₀ (by positivity) (by norm_num) n
        have h4 : (74 / 10 : ℝ) ^ n < (qn n : ℝ) ^ 5 := by
          rw [div_pow, div_lt_iff₀ (by positivity)]
          linarith
        linarith
      have hexp_lt : Real.exp (0.4 * (n : ℝ)) < (qn n : ℝ) :=
        lt_of_pow_lt_pow_left₀ 5 (by positivity) hexp5
      rwa [← Real.lt_log_iff_exp_lt (by exact_mod_cast qn_pos n)] at hexp_lt
  have h5 : 8 ≤ n → Real.log (epsReal n hn hn6) > 0.2 * n := by
    intro hn8
    have hfund := pellFundUnit_isFundamental hn hn6
    have hx1 : 1 ≤ X1 n hn hn6 := by
      unfold X1; have := hfund.one_lt_x; omega
    have hy1 : 1 ≤ Y1 n hn hn6 := by
      unfold Y1; have := hfund.zero_lt_y; omega
    have hsq_eq : (X1 n hn hn6 : ℝ) ^ 2 = (qn n : ℝ) * (Y1 n hn hn6 : ℝ) ^ 2 + 1 := by
      have hprop : (pellFundUnit n hn hn6).x ^ 2 - (qn n : ℤ) * (pellFundUnit n hn hn6).y ^ 2 = 1 :=
        (pellFundUnit n hn hn6).prop
      have hx0 : 0 ≤ (pellFundUnit n hn hn6).x := by linarith [hfund.one_lt_x]
      have hy0 : 0 ≤ (pellFundUnit n hn hn6).y := by linarith [hfund.zero_lt_y]
      have hx_eq : ((X1 n hn hn6 : ℕ) : ℤ) = (pellFundUnit n hn hn6).x := Int.natAbs_of_nonneg hx0
      have hy_eq : ((Y1 n hn hn6 : ℕ) : ℤ) = (pellFundUnit n hn hn6).y := Int.natAbs_of_nonneg hy0
      have hZ : ((X1 n hn hn6 : ℤ)) ^ 2 = (qn n : ℤ) * ((Y1 n hn hn6 : ℤ)) ^ 2 + 1 := by
        rw [hx_eq, hy_eq]; linarith
      exact_mod_cast hZ
    have hgt_2sqrt : 2 * Real.sqrt (qn n) < epsReal n hn hn6 := by
      unfold epsReal
      have hX_gt : Real.sqrt (qn n) < (X1 n hn hn6 : ℝ) := by
        have h1 : (qn n : ℝ) < (X1 n hn hn6 : ℝ) ^ 2 := by
          have hyR : (1 : ℝ) ≤ (Y1 n hn hn6 : ℝ) := by exact_mod_cast hy1
          nlinarith [qn_pos n]
        exact (Real.sqrt_lt' (by positivity)).mpr h1
      have hY_ge : Real.sqrt (qn n) ≤ (Y1 n hn hn6 : ℝ) * Real.sqrt (qn n) := by
        have hyR : (1 : ℝ) ≤ (Y1 n hn hn6 : ℝ) := by exact_mod_cast hy1
        exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hyR
      linarith
    by_cases h_exc : n = 10 ∨ n = 11 ∨ n = 28
    · rcases h_exc with rfl | rfl | rfl
      · have hq10 : qn 10 = 7 := by rw [← qnFast_eq_qn]; decide
        have hy3 : 3 ≤ Y1 10 hn hn6 := by
          by_contra hy_lt
          have h12 : Y1 10 hn hn6 = 1 ∨ Y1 10 hn hn6 = 2 := by omega
          have hZ : (X1 10 hn hn6) ^ 2 = 7 * (Y1 10 hn hn6) ^ 2 + 1 := by
            have := hsq_eq; rw [hq10] at this; exact_mod_cast this
          rcases h12 with hy_eq | hy_eq
          · rw [hy_eq] at hZ
            have : X1 10 hn hn6 ≤ 3 := by nlinarith
            interval_cases (X1 10 hn hn6) <;> omega
          · rw [hy_eq] at hZ
            have : X1 10 hn hn6 ≤ 6 := by nlinarith
            interval_cases (X1 10 hn hn6) <;> omega
        have hx8 : 8 ≤ X1 10 hn hn6 := by
          have hZ : (X1 10 hn hn6) ^ 2 = 7 * (Y1 10 hn hn6) ^ 2 + 1 := by
            have := hsq_eq; rw [hq10] at this; exact_mod_cast this
          nlinarith
        have heps14 : (14 : ℝ) < epsReal 10 hn hn6 := by
          unfold epsReal
          rw [hq10]
          have hsq7 : (2 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
          have hxR : (8 : ℝ) ≤ X1 10 hn hn6 := by exact_mod_cast hx8
          have hyR : (3 : ℝ) ≤ Y1 10 hn hn6 := by exact_mod_cast hy3
          nlinarith
        have hexp2 : Real.exp (0.2 * (10 : ℝ)) < (14 : ℝ) := by
          have h1 : Real.exp 1 < 272 / 100 := by linarith [Real.exp_one_lt_d9]
          have h2 : Real.exp (0.2 * (10 : ℝ)) = (Real.exp 1) ^ 2 := by
            rw [← Real.exp_nat_mul]; congr 1; norm_num
          rw [h2]; nlinarith [Real.exp_pos 1]
        exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_trans hexp2 heps14)
      · have hq11 : qn 11 = 77 := by rw [← qnFast_eq_qn]; decide
        have hexp : Real.exp (0.2 * (11 : ℝ)) < 2 * Real.sqrt (qn 11) := by
          rw [hq11]
          have h1 : Real.exp 1 < 272 / 100 := by linarith [Real.exp_one_lt_d9]
          have hsq : (Real.exp (0.2 * (11 : ℝ))) ^ 5 < (2 * Real.sqrt 77) ^ 5 := by
            have h2 : (Real.exp (0.2 * (11 : ℝ))) ^ 5 = (Real.exp 1) ^ 11 := by
              rw [← Real.exp_nat_mul]; congr 1; norm_num
            have h3 : (Real.exp 1) ^ 11 < (272 / 100 : ℝ) ^ 11 :=
              pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
            have h4 : (272 / 100 : ℝ) ^ 11 < 61000 := by norm_num
            have h5 : (61000 : ℝ) < (2 * Real.sqrt 77) ^ 5 := by
              have hsq77 : (8.7 : ℝ) < Real.sqrt 77 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
              have : (2 * 8.7 : ℝ) ^ 5 < (2 * Real.sqrt 77) ^ 5 :=
                pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
              linarith [show (61000 : ℝ) < (2 * 8.7 : ℝ) ^ 5 by norm_num]
            linarith
          exact lt_of_pow_lt_pow_left₀ 5 (by positivity) hsq
        exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_trans hexp hgt_2sqrt)
      · have hq28 : qn 28 = 44574 := by rw [← qnFast_eq_qn]; decide
        have hexp : Real.exp (0.2 * (28 : ℝ)) < 2 * Real.sqrt (qn 28) := by
          rw [hq28]
          have h1 : Real.exp 1 < 272 / 100 := by linarith [Real.exp_one_lt_d9]
          have h2 : Real.exp (0.2 * (28 : ℝ)) < (Real.exp 1) ^ 6 := by
            rw [← Real.exp_nat_mul]
            exact Real.exp_lt_exp.mpr (by norm_num)
          have h3 : (Real.exp 1) ^ 6 < (272 / 100 : ℝ) ^ 6 :=
            pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
          have h4 : (272 / 100 : ℝ) ^ 6 < 405 := by norm_num
          have h5 : (405 : ℝ) < 2 * Real.sqrt 44574 := by
            have hsq : (202.5 : ℝ) < Real.sqrt 44574 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
            linarith
          linarith
        exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_trans hexp hgt_2sqrt)
    · push_neg at h_exc
      have hq_gt : 0.4 * n < Real.log (qn n) := by
        apply h4
        by_cases h116 : 116 ≤ n
        · exact Or.inl h116
        · exact Or.inr ⟨hn8, by omega, h_exc.1, h_exc.2.1, h_exc.2.2⟩
      have heps_gt : Real.sqrt (qn n) < epsReal n hn hn6 := by
        have : 0 < Real.sqrt (qn n) := Real.sqrt_pos.mpr (by exact_mod_cast qn_pos n)
        linarith
      have hlog_gt : Real.log (Real.sqrt (qn n)) < Real.log (epsReal n hn hn6) :=
        Real.log_lt_log (Real.sqrt_pos.mpr (by exact_mod_cast qn_pos n)) heps_gt
      rw [Real.log_sqrt (by exact_mod_cast (qn_pos n).le)] at hlog_gt
      linarith
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro h8 m hsol
  obtain ⟨hn6', hk1, hmx, hsny⟩ := pellIndex_spec (by omega : 4 ≤ n) hsol
  have hk_eq : pellFundUnit n (by omega) hn6 = pellFundUnit n (by omega) hn6' := rfl
  set k := pellIndex (by omega : 4 ≤ n) hsol
  refine ⟨hk1, ?_, ?_⟩
  · have hm_eq : (m : ℝ) + (sn n : ℝ) * Real.sqrt (qn n) = (epsReal n hn hn6) ^ k := by
      have hpow := pell_pow_real_eq (n := n) (by omega) hn6 k
      rw [← hmx, ← hsny] at hpow
      exact hpow
    have hfac_lt : 4 * (n.factorial + 1) < n ^ n := by
      clear hm_eq hmx hsny hsol m
      induction n, h8 using Nat.le_induction with
      | base => decide
      | succ n hn' ih =>
        have h1 : 4 * ((n + 1).factorial + 1) ≤ (n + 1) * (4 * (n.factorial + 1)) := by
          rw [Nat.factorial_succ]; nlinarith
        have h2 : (n + 1) * (4 * (n.factorial + 1)) < (n + 1) * n ^ n :=
          Nat.mul_lt_mul_of_pos_left ih (Nat.succ_pos n)
        have h3 : (n + 1) * n ^ n ≤ (n + 1) ^ (n + 1) := by
          rw [pow_succ']
          exact Nat.mul_le_mul_left (n + 1) (Nat.pow_le_pow_left (Nat.le_succ n) n)
        omega
    have hsn_lt : (sn n : ℝ) * Real.sqrt (qn n) < (m : ℝ) := by
      have hsq : ((sn n : ℝ) * Real.sqrt (qn n)) ^ 2 < (m : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (qn_pos n).le)]
        have hm_fac : n.factorial + 1 = m ^ 2 := hsol.2.2
        have hfac := factorial_eq_qn_mul_sn_sq n
        have h1 : (qn n : ℝ) * (sn n : ℝ) ^ 2 = (n.factorial : ℝ) := by exact_mod_cast hfac.symm
        have h2 : (n.factorial : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hm_fac
        linarith
      nlinarith [Real.sqrt_nonneg (qn n)]
    have heps_pow_lt : (epsReal n hn hn6) ^ k < (n : ℝ) ^ ((n : ℝ) / 2) := by
      have h2m : (epsReal n hn hn6) ^ k < 2 * (m : ℝ) := by linarith
      have h2m_sq : (2 * (m : ℝ)) ^ 2 < ((n : ℝ) ^ ((n : ℝ) / 2)) ^ 2 := by
        have hm2 : (m : ℝ) ^ 2 = (n.factorial : ℝ) + 1 := by exact_mod_cast hsol.2.2.symm
        have hfacR : 4 * ((n.factorial : ℝ) + 1) < (n : ℝ) ^ n := by exact_mod_cast hfac_lt
        have hn_pos : (0 : ℝ) < n := by positivity
        have hpow_eq : ((n : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (n : ℝ) ^ n := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hn_pos.le]
          norm_num
          exact Real.rpow_natCast (n : ℝ) n
        linarith
      have h_pow_pos : (0 : ℝ) < (n : ℝ) ^ ((n : ℝ) / 2) := by positivity
      have h_lt : 2 * (m : ℝ) < (n : ℝ) ^ ((n : ℝ) / 2) := by nlinarith
      exact lt_trans h2m h_lt
    have heps_gt1 : 1 < epsReal n hn hn6 := by
      have := h5 h8
      have h02 : (0 : ℝ) < 0.2 * n := by positivity
      exact (Real.log_pos_iff (by
        unfold epsReal; positivity)).mp (lt_trans h02 this)
    have hlog_pow := Real.log_lt_log (pow_pos (by linarith) k) heps_pow_lt
    rw [Real.log_pow, Real.log_rpow (by positivity : (0 : ℝ) < n)] at hlog_pow
    have hlog_eps := h5 h8
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hn_pos : (0 : ℝ) < n := by positivity
    nlinarith
  · intro hn116
    have hn_pos : (0 : ℝ) < n := by positivity
    have hlog_sub : Real.log ((n : ℝ) / 116) ≤ (n : ℝ) / 116 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hn_pos.ne' (by norm_num)] at hlog_sub
    have hlog116 : Real.log (116 : ℝ) < 5 := by
      have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h2 : (116 : ℝ) < (2.7 : ℝ) ^ 5 := by norm_num
      have h3 : (2.7 : ℝ) ^ 5 < (Real.exp 1) ^ 5 :=
        pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
      have h4 : (Real.exp 1) ^ 5 = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)
    have hnR : (116 : ℝ) ≤ n := by exact_mod_cast hn116
    linarith

theorem lemma_3_1_ii :
    IsBigOAtTop
      (fun n => Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
        ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n)))
      (fun n => (n : ℝ)⁻¹) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧
      IsBigOAtTop
        (fun n => Real.log (sn n) - ((1 / 2 : ℝ) * n * Real.log n - ((1 + Real.log 2) / 2) * n))
        (fun n => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n)))) := by
  let a : ℕ → ℝ := fun n => Real.log (n.factorial : ℝ) - (((n : ℝ) + 1 / 2) * Real.log n - (n : ℝ))
  have hstep : ∀ k : ℕ, 1 ≤ k →
      0 ≤ a k - a (k + 1) ∧ a k - a (k + 1) ≤ (1 / 12 : ℝ) * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) := by
    intro k hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hdiff_eq : a k - a (k + 1) = ((k : ℝ) + 1 / 2) * Real.log (((k : ℝ) + 1) / (k : ℝ)) - 1 := by
      simp only [a]
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos k).ne')]
      rw [Real.log_div (by positivity) hk_pos.ne']
      push_cast; ring
    rw [hdiff_eq]
    set x : ℝ := 1 / (2 * (k : ℝ) + 1)
    have hx_pos : 0 < x := by positivity
    have hx_lt1 : x < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have hx_le : x ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    let g : ℝ → ℝ := fun t => Real.log ((1 + t) / (1 - t)) - 2 * t
    have hg_deriv : ∀ t ∈ Set.Icc 0 x, HasDerivAt g (2 * t ^ 2 / (1 - t ^ 2)) t := by
      intro t ht
      have ht1 : 0 < 1 + t := by linarith [ht.1]
      have ht2 : 0 < 1 - t := by linarith [ht.2, hx_lt1]
      have h1 : HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + t)) t := by
        simpa using ((hasDerivAt_id t).const_add 1).log ht1.ne'
      have h2 : HasDerivAt (fun u => Real.log (1 - u)) (-1 / (1 - t)) t := by
        have := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log ht2.ne'
        simpa [neg_div] using this
      have hsub := (h1.sub h2).sub ((hasDerivAt_id t).const_mul 2)
      have heq_fn : (fun u => Real.log (1 + u) - Real.log (1 - u) - 2 * u) =ᶠ[nhds t] g := by
        filter_upwards [eventually_gt_nhds (by linarith [ht.1] : -1 < t),
          eventually_lt_nhds (by linarith [ht.2, hx_lt1] : t < 1)] with u hu1 hu2
        simp only [g]
        rw [Real.log_div (by linarith) (by linarith)]
      refine (hsub.congr_of_eventuallyEq heq_fn).congr_deriv ?_
      field_simp [ht1.ne', ht2.ne']
      ring
    have hint_g : (∫ t in (0 : ℝ)..x, 2 * t ^ 2 / (1 - t ^ 2)) = g x := by
      have hcont : ContinuousOn (fun t : ℝ => 2 * t ^ 2 / (1 - t ^ 2)) (Set.Icc 0 x) := by
        intro t ht
        have hne : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2, hx_lt1]
        exact (((continuousAt_const.mul (continuousAt_id.pow 2)).div
          (continuousAt_const.sub (continuousAt_id.pow 2)) hne)).continuousWithinAt
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
        rw [Set.uIcc_of_le hx_pos.le] at ht; exact hg_deriv t ht) hcont.intervalIntegrable
      have hg0 : g 0 = 0 := by simp [g]
      linarith
    have hgx_eq : g x = (Real.log (((k : ℝ) + 1) / (k : ℝ)) - 2 * x) := by
      simp only [g]
      congr 1
      have hrat : (1 + x) / (1 - x) = ((k : ℝ) + 1) / (k : ℝ) := by
        simp only [x]; field_simp [hk_pos.ne']; ring
      rw [hrat]
    have h_lo : 0 ≤ g x := by
      rw [← hint_g]
      refine intervalIntegral.integral_nonneg hx_pos.le fun t ht => ?_
      have hden : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2, hx_lt1]
      exact div_nonneg (by positivity) hden.le
    have h_hi : g x ≤ (2 / (1 - x ^ 2)) * (x ^ 3 / 3) := by
      rw [← hint_g]
      have hcont1 : ContinuousOn (fun t : ℝ => 2 * t ^ 2 / (1 - t ^ 2)) (Set.Icc 0 x) := by
        intro t ht
        have hne : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2, hx_lt1]
        exact (((continuousAt_const.mul (continuousAt_id.pow 2)).div
          (continuousAt_const.sub (continuousAt_id.pow 2)) hne)).continuousWithinAt
      have hmono := intervalIntegral.integral_mono_on hx_pos.le hcont1.intervalIntegrable
        ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 x) (fun t ht => by
          have hden1 : 0 < 1 - x ^ 2 := by nlinarith [hx_pos, hx_lt1]
          have hden2 : 1 - x ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
          calc 2 * t ^ 2 / (1 - t ^ 2)
              ≤ 2 * t ^ 2 / (1 - x ^ 2) := div_le_div_of_nonneg_left (by positivity) hden1 hden2
            _ = (2 / (1 - x ^ 2)) * t ^ 2 := by ring)
      rw [intervalIntegral.integral_const_mul, integral_pow] at hmono
      linarith [show (x ^ 3 - 0 ^ 3) / 3 = x ^ 3 / 3 by ring]
    have hmul_pos : 0 < (k : ℝ) + 1 / 2 := by positivity
    have h2x_eq : ((k : ℝ) + 1 / 2) * (2 * x) = 1 := by
      simp only [x]; field_simp; ring
    have hmul_gx : ((k : ℝ) + 1 / 2) * g x = ((k : ℝ) + 1 / 2) * Real.log (((k : ℝ) + 1) / (k : ℝ)) - 1 := by
      rw [hgx_eq, mul_sub, h2x_eq]
    rw [← hmul_gx]
    refine ⟨mul_nonneg hmul_pos.le h_lo, ?_⟩
    have hcalc : ((k : ℝ) + 1 / 2) * ((2 / (1 - x ^ 2)) * (x ^ 3 / 3)) =
        (1 / 12 : ℝ) * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) := by
      simp only [x]
      push_cast
      field_simp [hk_pos.ne', hk1_pos.ne']
      ring
    linarith [mul_le_mul_of_nonneg_left h_hi hmul_pos.le]
  have h_lim : Tendsto a atTop (𝓝 ((1 / 2 : ℝ) * Real.log (2 * Real.pi))) := by
    have hst := Stirling.tendsto_stirlingSeq_sqrt_pi
    have hlog := (Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp hst
    have hcong : (fun n : ℕ => Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log 2) =ᶠ[atTop] a := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [Stirling.stirlingSeq, a]
      rw [Real.log_div (by exact_mod_cast (Nat.factorial_pos n).ne') (by positivity)]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
        Real.log_mul (by norm_num) hn_pos.ne', Real.log_pow,
        Real.log_div hn_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
      ring
    have hadd := hlog.add tendsto_const_nhds
    have hlim_eq : Real.log (Real.sqrt Real.pi) + (1 / 2 : ℝ) * Real.log 2 =
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) := by
      rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']
      ring
    rw [hlim_eq] at hadd
    exact hadd.congr' hcong
  have h_bd : ∀ n : ℕ, 1 ≤ n →
      |a n - (1 / 2 : ℝ) * Real.log (2 * Real.pi)| ≤ 1 / (12 * (n : ℝ)) := by
    intro n hn
    have h_diff_m : ∀ m : ℕ, n ≤ m →
        0 ≤ a n - a m ∧ a n - a m ≤ (1 / 12 : ℝ) * ((n : ℝ)⁻¹ - (m : ℝ)⁻¹) := by
      intro m hnm
      induction m, hnm using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        have hsm := hstep m (le_trans hn hm)
        exact ⟨by linarith [ih.1, hsm.1], by linarith [ih.2, hsm.2]⟩
    have h_ge : (1 / 2 : ℝ) * Real.log (2 * Real.pi) ≤ a n := by
      have h1 : ∀ᶠ m : ℕ in atTop, a m ≤ a n := by
        filter_upwards [eventually_ge_atTop n] with m hm
        linarith [(h_diff_m m hm).1]
      exact le_of_tendsto h_lim h1
    have h_le : a n - (1 / 2 : ℝ) * Real.log (2 * Real.pi) ≤ 1 / (12 * (n : ℝ)) := by
      have h1 : ∀ᶠ m : ℕ in atTop, a n - 1 / (12 * (n : ℝ)) ≤ a m := by
        filter_upwards [eventually_ge_atTop (max n 1)] with m hm
        have hm1 : 0 ≤ (m : ℝ)⁻¹ := by positivity
        have hmn := (h_diff_m m (le_trans (le_max_left _ _) hm)).2
        linarith [show (1 / 12 : ℝ) * (n : ℝ)⁻¹ = 1 / (12 * (n : ℝ)) by ring]
      linarith [le_of_tendsto h_lim h1]
    rw [abs_of_nonneg (sub_nonneg.mpr h_ge)]
    exact h_le
  have hpart1 : IsBigOAtTop
      (fun n => Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
        ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n)))
      (fun n => (n : ℝ)⁻¹) := by
    refine ⟨1 / 24, by norm_num, 1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hfac : (sn n : ℝ) * Real.sqrt (qn n) = Real.sqrt (n.factorial : ℝ) := by
      have h := factorial_eq_qn_mul_sn_sq n
      have hR : (n.factorial : ℝ) = (qn n : ℝ) * (sn n : ℝ) ^ 2 := by exact_mod_cast h
      rw [hR, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
    have hlog_eq : Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
        ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n)) =
        (1 / 2 : ℝ) * (a n - (1 / 2 : ℝ) * Real.log (2 * Real.pi)) := by
      rw [hfac, Real.log_sqrt (by positivity), Real.log_mul (by positivity) hn_pos.ne']
      simp only [a]
      ring
    rw [hlog_eq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hb := h_bd n hn
    linarith [show (1 / 2 : ℝ) * (1 / (12 * (n : ℝ))) = (1 / 24 : ℝ) * (n : ℝ)⁻¹ by ring]
  refine ⟨hpart1, ?_⟩
  obtain ⟨c₀, C₀, hc₀, hC₀, hqn⟩ := lemma_2_1_ii_part1
  obtain ⟨C₁, hC₁, N₁, hN₁⟩ := hpart1
  have h_ev : ∀ᶠ n : ℕ in atTop,
      4 ≤ n ∧ N₁ ≤ n ∧
      C₁ * (n : ℝ)⁻¹ + (1 / 4 : ℝ) * |Real.log (2 * Real.pi * n)| ≤
        (n : ℝ) * Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n)) := by
    -- `log(2πn)` and `1/n` are `O(n * exp(-(c₀/2) √(log n)))`
    have h_tend : Tendsto (fun n : ℕ =>
        (C₁ * (n : ℝ)⁻¹ + (1 / 4 : ℝ) * |Real.log (2 * Real.pi * n)|) /
          ((n : ℝ) * Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n)))) atTop (𝓝 0) := by
      have h_sqrt_log : Tendsto (fun n : ℕ => Real.sqrt (Real.log n)) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro b
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
          ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max b 0 ^ 2))
        refine ⟨N, fun n hn => le_trans (le_max_left b 0) ?_⟩
        rw [← Real.sqrt_sq (le_max_right b 0)]
        exact Real.sqrt_le_sqrt (hN n hn)
      have h_num : ∀ᶠ n : ℕ in atTop,
          C₁ * (n : ℝ)⁻¹ + (1 / 4 : ℝ) * |Real.log (2 * Real.pi * n)| ≤
            C₁ + Real.log (2 * Real.pi) + Real.log n := by
        filter_upwards [eventually_ge_atTop 2] with n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have h1 : C₁ * (n : ℝ)⁻¹ ≤ C₁ := mul_le_of_le_one_right hC₁.le (inv_le_one_of_one_le₀ hn1)
        have h2 : Real.log (2 * Real.pi * n) = Real.log (2 * Real.pi) + Real.log n :=
          Real.log_mul (by positivity) (by positivity)
        have h3 : 0 ≤ Real.log (2 * Real.pi) + Real.log n := by
          have : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          exact add_nonneg (Real.log_nonneg this) (Real.log_nonneg hn1)
        rw [h2, abs_of_nonneg h3]
        linarith
      have h_exp : Tendsto (fun n : ℕ =>
          (C₁ + Real.log (2 * Real.pi) + (2 / c₀) ^ 2 * ((c₀ / 2) * Real.sqrt (Real.log n)) ^ 2) *
            Real.exp (-((c₀ / 2) * Real.sqrt (Real.log n)))) atTop (𝓝 0) := by
        have h0 : Tendsto (fun x : ℝ => (C₁ + Real.log (2 * Real.pi)) * Real.exp (-x) +
            (2 / c₀) ^ 2 * (x ^ 2 * Real.exp (-x))) atTop (𝓝 0) := by
          simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (C₁ + Real.log (2 * Real.pi))).add
            ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul ((2 / c₀) ^ 2))
        exact h0.comp (Tendsto.const_mul_atTop (by positivity) h_sqrt_log)
      refine squeeze_zero' (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
        positivity) ?_ h_exp
      filter_upwards [eventually_ge_atTop 2, h_num] with n hn2 hnum
      have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hmul : (2 / c₀) ^ 2 * ((c₀ / 2) * Real.sqrt (Real.log n)) ^ 2 = Real.log n := by
        rw [mul_pow, Real.sq_sqrt hlog_nn]; field_simp [hc₀.ne']
      rw [hmul, neg_mul]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hexp_pos : 0 < Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n)) := Real.exp_pos _
      rw [div_eq_mul_inv, mul_inv, ← Real.exp_neg, neg_neg]
      have hinv1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      calc (C₁ * (n : ℝ)⁻¹ + (1 / 4 : ℝ) * |Real.log (2 * Real.pi * n)|) *
            ((n : ℝ)⁻¹ * Real.exp ((c₀ / 2) * Real.sqrt (Real.log n)))
          ≤ (C₁ + Real.log (2 * Real.pi) + Real.log n) *
              (1 * Real.exp ((c₀ / 2) * Real.sqrt (Real.log n))) := by
            refine mul_le_mul hnum (mul_le_mul_of_nonneg_right hinv1 (Real.exp_pos _).le)
              (by positivity) (by
                have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
                linarith)
        _ = (C₁ + Real.log (2 * Real.pi) + Real.log n) *
              Real.exp (-(-(c₀ / 2) * Real.sqrt (Real.log n))) := by simp
    filter_upwards [eventually_ge_atTop 4, eventually_ge_atTop N₁,
      h_tend.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn4 hn1 hle
    refine ⟨hn4, hn1, ?_⟩
    have hden : 0 < (n : ℝ) * Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n)) := by
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    exact (div_le_one hden).mp hle
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp h_ev
  refine ⟨c₀ / 2, by positivity, 1 + C₀ / 2, by positivity, N₂, fun n hn => ?_⟩
  obtain ⟨hn4, hn1, hdom⟩ := hN₂ n hn
  have hlog_eq : Real.log (sn n) - ((1 / 2 : ℝ) * n * Real.log n - ((1 + Real.log 2) / 2) * n) =
      (Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
        ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n))) -
      (1 / 2 : ℝ) * (Real.log (qn n) - Real.log 2 * n) +
      (1 / 4 : ℝ) * Real.log (2 * Real.pi * n) := by
    rw [Real.log_mul (by exact_mod_cast (sn_pos n).ne') (Real.sqrt_pos.mpr (by exact_mod_cast qn_pos n)).ne',
      Real.log_sqrt (by exact_mod_cast (qn_pos n).le)]
    ring
  rw [hlog_eq]
  have hp1 := hN₁ n hn1
  have hp2 := hqn n hn4
  have hexp_le : Real.exp (-c₀ * Real.sqrt (Real.log n)) ≤ Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
    nlinarith
  have htri1 := abs_add_le
    ((Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
      ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n))) -
      (1 / 2 : ℝ) * (Real.log (qn n) - Real.log 2 * n))
    ((1 / 4 : ℝ) * Real.log (2 * Real.pi * n))
  have htri2 := abs_sub
    (Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
      ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n)))
    ((1 / 2 : ℝ) * (Real.log (qn n) - Real.log 2 * n))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at htri2
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] at htri1
  have hC0_bd : (1 / 2 : ℝ) * |Real.log (qn n) - Real.log 2 * n| ≤
      (C₀ / 2) * ((n : ℝ) * Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n))) := by
    calc (1 / 2 : ℝ) * |Real.log (qn n) - Real.log 2 * n|
        ≤ (1 / 2 : ℝ) * (C₀ * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n))) := by linarith
      _ ≤ (1 / 2 : ℝ) * (C₀ * (n : ℝ) * Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_le (by positivity)) (by norm_num)
      _ = (C₀ / 2) * ((n : ℝ) * Real.exp (-(c₀ / 2) * Real.sqrt (Real.log n))) := by ring
  linarith

lemma pell_xy_nonneg {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    0 ≤ (pellFundUnit n hn hn6 ^ (k : ℤ)).x ∧ 0 ≤ (pellFundUnit n hn hn6 ^ (k : ℤ)).y := by
  have hfund := pellFundUnit_isFundamental hn hn6
  have hx1 : 0 ≤ (pellFundUnit n hn hn6).x := by linarith [hfund.one_lt_x]
  have hy1 : 0 ≤ (pellFundUnit n hn hn6).y := by linarith [hfund.zero_lt_y]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, zpow_add, zpow_one, Pell.Solution₁.mul_x, Pell.Solution₁.mul_y]
    have hq : (0 : ℤ) ≤ qn n := by exact_mod_cast (qn_pos n).le
    exact ⟨by nlinarith [ih.1, ih.2, hx1, hy1, hq], by nlinarith [ih.1, ih.2, hx1, hy1]⟩

lemma pell_xy_pos {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (pellFundUnit n hn hn6 ^ (k : ℤ)).x ∧ 1 ≤ (pellFundUnit n hn hn6 ^ (k : ℤ)).y := by
  have hfund := pellFundUnit_isFundamental hn hn6
  have hx1 : 1 ≤ (pellFundUnit n hn hn6).x := by linarith [hfund.one_lt_x]
  have hy1 : 1 ≤ (pellFundUnit n hn hn6).y := by linarith [hfund.zero_lt_y]
  induction k, hk using Nat.le_induction with
  | base => simpa using ⟨hx1, hy1⟩
  | succ m hm ih =>
    rw [Nat.cast_succ, zpow_add, zpow_one, Pell.Solution₁.mul_x, Pell.Solution₁.mul_y]
    have hq : (1 : ℤ) ≤ qn n := by exact_mod_cast qn_pos n
    exact ⟨by nlinarith [ih.1, ih.2, hx1, hy1, hq], by nlinarith [ih.1, ih.2, hx1, hy1]⟩

lemma Xr_eq {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    (Xr n hn hn6 k : ℤ) = (pellFundUnit n hn hn6 ^ (k : ℤ)).x := by
  unfold Xr
  exact Int.natAbs_of_nonneg (pell_xy_nonneg hn hn6 k).1

lemma Yr_eq {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    (Yr n hn hn6 k : ℤ) = (pellFundUnit n hn hn6 ^ (k : ℤ)).y := by
  unfold Yr
  exact Int.natAbs_of_nonneg (pell_xy_nonneg hn hn6 k).2

lemma X1_eq {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    (X1 n hn hn6 : ℤ) = (pellFundUnit n hn hn6).x := by
  unfold X1
  have := (pell_xy_nonneg hn hn6 1).1
  simp only [Nat.cast_one, zpow_one] at this
  exact Int.natAbs_of_nonneg this

lemma Y1_eq {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    (Y1 n hn hn6 : ℤ) = (pellFundUnit n hn hn6).y := by
  unfold Y1
  have := (pell_xy_nonneg hn hn6 1).2
  simp only [Nat.cast_one, zpow_one] at this
  exact Int.natAbs_of_nonneg this

lemma Y1_pos {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) : 0 < Y1 n hn hn6 := by
  have h := (pellFundUnit_isFundamental hn hn6).zero_lt_y
  have hy := Y1_eq hn hn6
  omega

lemma Yr_pos {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) {k : ℕ} (hk : 1 ≤ k) :
    0 < Yr n hn hn6 k := by
  have h := (pell_xy_pos hn hn6 k hk).2
  have hy := Yr_eq hn hn6 k
  omega

lemma pell_x_succ_succ {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    (Xr n hn hn6 (k + 2) : ℤ) =
      2 * (X1 n hn hn6 : ℤ) * (Xr n hn hn6 (k + 1) : ℤ) - (Xr n hn hn6 k : ℤ) := by
  rw [Xr_eq, Xr_eq, Xr_eq, X1_eq]
  have hprop : (pellFundUnit n hn hn6).x ^ 2 - (qn n : ℤ) * (pellFundUnit n hn hn6).y ^ 2 = 1 :=
    (pellFundUnit n hn hn6).prop
  set ε := pellFundUnit n hn hn6
  set z := ε ^ (k : ℤ)
  have hz1 : ε ^ ((k + 1 : ℕ) : ℤ) = z * ε := by rw [Nat.cast_succ, zpow_add, zpow_one]
  have hz2 : ε ^ ((k + 2 : ℕ) : ℤ) = (z * ε) * ε := by
    rw [show (k + 2 : ℕ) = k + 1 + 1 by rfl, Nat.cast_succ, zpow_add, zpow_one, hz1]
  rw [hz2, hz1, Pell.Solution₁.mul_x, Pell.Solution₁.mul_x, Pell.Solution₁.mul_y]
  nlinarith [hprop]

lemma pell_y_succ_succ {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    (Yr n hn hn6 (k + 2) : ℤ) =
      2 * (X1 n hn hn6 : ℤ) * (Yr n hn hn6 (k + 1) : ℤ) - (Yr n hn hn6 k : ℤ) := by
  rw [Yr_eq, Yr_eq, Yr_eq, X1_eq]
  have hprop : (pellFundUnit n hn hn6).x ^ 2 - (qn n : ℤ) * (pellFundUnit n hn hn6).y ^ 2 = 1 :=
    (pellFundUnit n hn hn6).prop
  set ε := pellFundUnit n hn hn6
  set z := ε ^ (k : ℤ)
  have hz1 : ε ^ ((k + 1 : ℕ) : ℤ) = z * ε := by rw [Nat.cast_succ, zpow_add, zpow_one]
  have hz2 : ε ^ ((k + 2 : ℕ) : ℤ) = (z * ε) * ε := by
    rw [show (k + 2 : ℕ) = k + 1 + 1 by rfl, Nat.cast_succ, zpow_add, zpow_one, hz1]
  rw [hz2, hz1, Pell.Solution₁.mul_y, Pell.Solution₁.mul_x, Pell.Solution₁.mul_y]
  nlinarith [hprop]

lemma pell_pow_quadAlg {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) :
    (⟨(X1 n hn hn6 : ℤ), (Y1 n hn hn6 : ℤ)⟩ : QuadraticAlgebra ℤ (qn n : ℤ) 0) ^ k =
      ⟨(Xr n hn hn6 k : ℤ), (Yr n hn hn6 k : ℤ)⟩ := by
  induction k with
  | zero =>
    ext <;> simp [Xr_eq, Yr_eq]
  | succ k ih =>
    rw [pow_succ, ih, Xr_eq, Yr_eq, Xr_eq, Yr_eq, X1_eq, Y1_eq]
    rw [Nat.cast_succ, zpow_add, zpow_one, Pell.Solution₁.mul_x, Pell.Solution₁.mul_y]
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

lemma pell_binomial_im (D X Y : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ((⟨X, Y⟩ : QuadraticAlgebra ℤ D 0) ^ k).im =
      Y * ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
        (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * (D * Y ^ 2) ^ j := by
  let R := QuadraticAlgebra ℤ D 0
  have hsplit : (⟨X, Y⟩ : R) = ⟨0, Y⟩ + ⟨X, 0⟩ := by ext <;> simp
  have hpow_re : ∀ m : ℕ, (⟨X, 0⟩ : R) ^ m = ⟨X ^ m, 0⟩ := by
    intro m; induction m with
    | zero => ext <;> simp
    | succ m ih => rw [pow_succ, ih]; ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  have hpow_im_even : ∀ j : ℕ, (⟨0, Y⟩ : R) ^ (2 * j) = ⟨(D * Y ^ 2) ^ j, 0⟩ := by
    intro j; induction j with
    | zero => ext <;> simp
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, ih]
      have hsq : (⟨0, Y⟩ : R) ^ 2 = ⟨D * Y ^ 2, 0⟩ := by
        rw [sq]; ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
      rw [hsq]; ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  have hpow_im_odd : ∀ j : ℕ, (⟨0, Y⟩ : R) ^ (2 * j + 1) = ⟨0, Y * (D * Y ^ 2) ^ j⟩ := by
    intro j; rw [pow_succ, hpow_im_even]
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  have him_add : ∀ s : Finset ℕ, ∀ f : ℕ → R, (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  rw [hsplit, add_pow, him_add]
  have hterm_eq : ∀ i ∈ Finset.range (k + 1),
      ((⟨0, Y⟩ : R) ^ i * (⟨X, 0⟩ : R) ^ (k - i) * (Nat.choose k i : R)).im =
      if i % 2 = 1 then Y * ((Nat.choose k i : ℤ) * X ^ (k - i) * (D * Y ^ 2) ^ (i / 2)) else 0 := by
    intro i _
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by ring, hpow_im_even, hpow_re]
      simp [QuadraticAlgebra.im_mul, Nat.mul_mod_right]
    · rw [hpow_im_odd, hpow_re, show (2 * j + 1) % 2 = 1 by omega, if_pos rfl,
        show (2 * j + 1) / 2 = j by omega]
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, QuadraticAlgebra.re_mk, QuadraticAlgebra.im_mk]
      ring
  rw [Finset.sum_congr rfl hterm_eq, ← Finset.sum_filter]
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => 2 * j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨by omega, by omega⟩
  · intro j₁ _ j₂ _ h; omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨i / 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rw [show k - (2 * j + 1) = k - 1 - 2 * j by omega]

lemma padicValInt_chebyshevU_sum {p k : ℕ} {X M : ℤ} (hp : p.Prime) (hk : 1 ≤ k)
    (hpM : (p : ℤ) ∣ M) (hX : X ^ 2 = M + 1)
    (hp3_or : p ≠ 3 ∨ ¬ 3 ∣ k ∨ (p : ℤ) ^ 2 ∣ M) :
    padicValInt p (∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j) = padicValNat p k := by
  haveI : Fact p.Prime := ⟨hp⟩
  set S : ℤ := ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j
  have h0_mem : 0 ∈ Finset.range ((k - 1) / 2 + 1) := Finset.mem_range.mpr (by omega)
  have hS_split : S = (k : ℤ) * X ^ (k - 1) +
      ∑ j ∈ (Finset.range ((k - 1) / 2 + 1)).erase 0,
        (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j := by
    rw [← Finset.add_sum_erase _ _ h0_mem]
    simp [Nat.choose_one_right]
  set e := padicValNat p k
  have hk_ne : k ≠ 0 := by omega
  have hpk_dvd : p ^ e ∣ k := (padicValNat_dvd_iff_le hk_ne).mpr le_rfl
  have hpk_ndvd : ¬ p ^ (e + 1) ∣ k := by
    rw [padicValNat_dvd_iff_le hk_ne]; omega
  have hpX_ndvd : ¬ (p : ℤ) ∣ X := by
    intro h
    have hd1 : (p : ℤ) ∣ X ^ 2 := dvd_pow h (by norm_num)
    have hd2 : (p : ℤ) ∣ 1 := by
      have : (1 : ℤ) = X ^ 2 - M := by linarith
      rw [this]; exact dvd_sub hd1 hpM
    have := Int.le_of_dvd (by norm_num) hd2
    have := hp.two_le
    omega
  have hterm_dvd : ∀ j ∈ (Finset.range ((k - 1) / 2 + 1)).erase 0,
      (p : ℤ) ^ (e + 1) ∣ (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j := by
    intro j hj
    have hj_pos : 1 ≤ j := by
      have := (Finset.mem_erase.mp hj).1
      omega
    have hchoose_id : (2 * j + 1 : ℤ) * (Nat.choose k (2 * j + 1) : ℤ) =
        (k : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) := by
      have h1 : k = (k - 1) + 1 := by omega
      have h2 := Nat.succ_mul_choose_eq (k - 1) (2 * j)
      rw [← h1] at h2
      exact_mod_cast h2.symm
    by_cases hp3_ndvd : p = 3 ∧ ¬ 3 ∣ k
    · rcases hp3_ndvd with ⟨rfl, hk3⟩
      have he0 : e = 0 := padicValNat.eq_zero_of_not_dvd hk3
      rw [he0, zero_add, pow_one]
      exact dvd_mul_of_dvd_right (dvd_pow hpM (by omega)) _
    · have hp_pow_M : (p : ℤ) ^ (padicValNat p (2 * j + 1) + 1) ∣ M ^ j := by
        set r := padicValNat p (2 * j + 1)
        by_cases hp2 : p = 2
        · subst hp2
          have hr0 : r = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
          rw [hr0, zero_add, pow_one]
          exact dvd_pow hpM (by omega)
        · have hp3_ge : 3 ≤ p := by have := hp.two_le; omega
          by_cases hp3 : p = 3
          · subst hp3
            have hM9 : (3 : ℤ) ^ 2 ∣ M := by
              rcases hp3_or with hne | hnk | hM9
              · exact absurd rfl hne
              · exact absurd hnk (fun h => hp3_ndvd ⟨rfl, h⟩)
              · exact hM9
            have h3_lt : 2 * j + 1 < 3 ^ (2 * j) := by
              clear hpM hX hp3_or hS_split h0_mem hpk_dvd hpk_ndvd hpX_ndvd hj hchoose_id hp3_ndvd
              induction j, hj_pos using Nat.le_induction with
              | base => norm_num
              | succ m hm ih =>
                have : 3 ^ (2 * (m + 1)) = 9 * 3 ^ (2 * m) := by ring
                omega
            have hr_lt : r < 2 * j := by
              by_contra hge
              have hle1 : 3 ^ (2 * j) ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
              have hle2 : 3 ^ r ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) ((padicValNat_dvd_iff_le (by omega)).mpr le_rfl)
              omega
            exact dvd_trans (pow_dvd_pow (3 : ℤ) (by omega : r + 1 ≤ 2 * j))
              (by simpa [← pow_mul] using pow_dvd_pow_of_dvd hM9 j)
          · have hp5 : 5 ≤ p := by
              rcases hp.eq_two_or_odd with rfl | hodd
              · exact absurd rfl hp2
              · omega
            have hp_lt : 2 * j + 1 < p ^ j := by
              have h5 : 2 * j + 1 < 5 ^ j := by
                clear hpM hX hp3_or hS_split h0_mem hpk_dvd hpk_ndvd hpX_ndvd hj hchoose_id hp3_ndvd hp3 hp5 hp
                induction j, hj_pos using Nat.le_induction with
                | base => norm_num
                | succ m hm ih =>
                  have : 5 ^ (m + 1) = 5 * 5 ^ m := by ring
                  omega
              exact lt_of_lt_of_le h5 (Nat.pow_le_pow_left hp5 j)
            have hr_lt : r < j := by
              by_contra hge
              have hle1 : p ^ j ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
              have hle2 : p ^ r ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) ((padicValNat_dvd_iff_le (by omega)).mpr le_rfl)
              omega
            exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega : r + 1 ≤ j)) (dvd_pow hpM (by omega))
      set r := padicValNat p (2 * j + 1)
      have hpr_dvd : p ^ r ∣ 2 * j + 1 := (padicValNat_dvd_iff_le (by omega)).mpr le_rfl
      obtain ⟨u, hu⟩ := hpr_dvd
      have hu_ndvd : ¬ p ∣ u := by
        intro hpu
        have hpr1 : p ^ (r + 1) ∣ 2 * j + 1 := by
          obtain ⟨v, hv⟩ := hpu
          exact ⟨v, by rw [hu, hv]; ring⟩
        have := (padicValNat_dvd_iff_le (by omega : 2 * j + 1 ≠ 0)).mp hpr1
        omega
      obtain ⟨q, hq⟩ := hp_pow_M
      have hmul_eq : (u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j) =
          (k : ℤ) * (p : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) * X ^ (k - 1 - 2 * j) * q := by
        have hpr_ne : ((p : ℤ) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
        apply mul_left_cancel₀ hpr_ne
        have h1 : (p : ℤ) ^ r * ((u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j)) =
            ((2 * j + 1 : ℤ) * (Nat.choose k (2 * j + 1) : ℤ)) * X ^ (k - 1 - 2 * j) * M ^ j := by
          have huZ : (2 * j + 1 : ℤ) = (p : ℤ) ^ r * (u : ℤ) := by exact_mod_cast hu
          rw [huZ]; ring
        rw [h1, hchoose_id, hq]
        ring
      have hrhs_dvd : (p : ℤ) ^ (e + 1) ∣
          (u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j) := by
        rw [hmul_eq]
        have hpkZ : (p : ℤ) ^ e ∣ (k : ℤ) := by exact_mod_cast hpk_dvd
        have hpk1 : (p : ℤ) ^ (e + 1) ∣ (k : ℤ) * (p : ℤ) := by
          rw [pow_succ]; exact mul_dvd_mul_right hpkZ _
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpk1 _) _) _
      have hcop : IsCoprime ((p : ℤ) ^ (e + 1)) (u : ℤ) := by
        exact_mod_cast (hp.coprime_iff_not_dvd.mpr hu_ndvd).pow_left (e + 1)
      exact hcop.dvd_of_dvd_mul_left hrhs_dvd
  have hrem_dvd : (p : ℤ) ^ (e + 1) ∣
      ∑ j ∈ (Finset.range ((k - 1) / 2 + 1)).erase 0,
        (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j :=
    Finset.dvd_sum hterm_dvd
  have hS_dvd : (p : ℤ) ^ e ∣ S := by
    rw [hS_split]
    exact dvd_add (dvd_mul_of_dvd_left (by exact_mod_cast hpk_dvd) _)
      (dvd_trans (pow_dvd_pow (p : ℤ) (Nat.le_succ e)) hrem_dvd)
  have hS_ndvd : ¬ (p : ℤ) ^ (e + 1) ∣ S := by
    intro h
    have h0_dvd : (p : ℤ) ^ (e + 1) ∣ (k : ℤ) * X ^ (k - 1) := by
      have : (k : ℤ) * X ^ (k - 1) = S -
          ∑ j ∈ (Finset.range ((k - 1) / 2 + 1)).erase 0,
            (Nat.choose k (2 * j + 1) : ℤ) * X ^ (k - 1 - 2 * j) * M ^ j := by linarith
      rw [this]; exact dvd_sub h hrem_dvd
    have hcop_pX : IsCoprime (p : ℤ) X :=
      (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hpX_ndvd
    have hcop : IsCoprime ((p : ℤ) ^ (e + 1)) (X ^ (k - 1)) :=
      (hcop_pX.pow_left (e + 1)).pow_right (k - 1)
    have hkdvd : (p : ℤ) ^ (e + 1) ∣ (k : ℤ) := hcop.dvd_of_dvd_mul_right h0_dvd
    exact hpk_ndvd (by exact_mod_cast hkdvd)
  have hS_ne : S ≠ 0 := by
    intro h0; subst h0; exact hS_ndvd (dvd_zero _)
  have hS_nat_ne : S.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hS_ne
  change padicValNat p S.natAbs = e
  have h1 : p ^ e ∣ S.natAbs := Int.natCast_dvd.mp hS_dvd
  have h2 : ¬ p ^ (e + 1) ∣ S.natAbs := fun h => hS_ndvd (Int.natCast_dvd.mpr h)
  have hle1 : e ≤ padicValNat p S.natAbs := (padicValNat_dvd_iff_le hS_nat_ne).mp h1
  have hle2 : ¬ e + 1 ≤ padicValNat p S.natAbs := fun h => h2 ((padicValNat_dvd_iff_le hS_nat_ne).mpr h)
  omega

theorem lemma_3_2_i (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) (k : ℕ) (hk : 1 ≤ k) :
    (Xr n hn hn6 k : ℤ) = (Polynomial.Chebyshev.T ℤ k).eval (X1 n hn hn6 : ℤ) ∧
    (Yr n hn hn6 k : ℤ) = (Y1 n hn hn6 : ℤ) * (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ) ∧
    ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ) =
      ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
        ((Nat.choose k (2 * j + 1) : ℤ) * (X1 n hn hn6 : ℤ) ^ (k - 1 - 2 * j) *
          ((qn n : ℤ) * (Y1 n hn hn6 : ℤ) ^ 2) ^ j)) ∧
    Nat.gcd ((X1 n hn hn6) ^ 2 - 1)
      (((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ^ 2) ∣ k ^ 2 ∧
    (∀ p : ℕ, p.Prime → p ∣ qn n * Y1 n hn hn6 →
      (p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y1 n hn hn6) →
      padicValInt p ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)) = padicValNat p k) ∧
    (∀ (hn4 : 4 ≤ n) (m : ℕ) (hsol : IsBrocardSol n m), k = pellIndex hn4 hsol →
      ∀ p ∈ Podd n, (p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y1 n hn hn6) →
        padicValNat p (qn n * (Y1 n hn hn6) ^ 2) = padicValNat p n.factorial - 2 * padicValNat p k) := by
  have hT_all : ∀ r : ℕ, (Xr n hn hn6 r : ℤ) = (Polynomial.Chebyshev.T ℤ r).eval (X1 n hn hn6 : ℤ) := by
    intro r
    induction r using Nat.twoStepInduction with
    | zero => simp [Xr_eq]
    | one => simp [Xr_eq, X1_eq]
    | more r ih0 ih1 =>
      rw [pell_x_succ_succ hn hn6 r, ih0, ih1]
      have hT : Polynomial.Chebyshev.T ℤ ((r + 2 : ℕ) : ℤ) =
          2 * Polynomial.X * Polynomial.Chebyshev.T ℤ ((r + 1 : ℕ) : ℤ) - Polynomial.Chebyshev.T ℤ (r : ℤ) := by
        simpa [Nat.cast_add] using Polynomial.Chebyshev.T_add_two ℤ (r : ℤ)
      rw [hT]
      simp [Polynomial.eval_sub, Polynomial.eval_mul]
  have hU_all : ∀ m : ℕ, (Yr n hn hn6 (m + 1) : ℤ) =
      (Y1 n hn hn6 : ℤ) * (Polynomial.Chebyshev.U ℤ m).eval (X1 n hn hn6 : ℤ) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => simp [Yr_eq, Y1_eq]
    | one =>
      have hYr2 : (Yr n hn hn6 2 : ℤ) = 2 * (X1 n hn hn6 : ℤ) * (Y1 n hn hn6 : ℤ) := by
        have h := pell_y_succ_succ hn hn6 0
        have hy0 : (Yr n hn hn6 0 : ℤ) = 0 := by simp [Yr_eq]
        have hy1 : (Yr n hn hn6 1 : ℤ) = (Y1 n hn hn6 : ℤ) := by simp [Yr_eq, Y1_eq]
        rw [hy0, hy1] at h
        linarith
      rw [hYr2]
      simp [Polynomial.Chebyshev.U_one]
      ring
    | more m ih0 ih1 =>
      rw [show m + 2 + 1 = (m + 1) + 2 by omega, pell_y_succ_succ hn hn6 (m + 1), ih0, ih1]
      have hU : Polynomial.Chebyshev.U ℤ ((m + 2 : ℕ) : ℤ) =
          2 * Polynomial.X * Polynomial.Chebyshev.U ℤ ((m + 1 : ℕ) : ℤ) - Polynomial.Chebyshev.U ℤ (m : ℤ) := by
        simpa [Nat.cast_add] using Polynomial.Chebyshev.U_add_two ℤ (m : ℤ)
      rw [hU]
      simp [Polynomial.eval_sub, Polynomial.eval_mul]
      ring
  have h1 : (Xr n hn hn6 k : ℤ) = (Polynomial.Chebyshev.T ℤ k).eval (X1 n hn hn6 : ℤ) := hT_all k
  have h2 : (Yr n hn hn6 k : ℤ) = (Y1 n hn hn6 : ℤ) * (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq]
    rw [hU_all (k - 1), Nat.cast_sub hk, Nat.cast_one]
  have h3 : (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ) =
      ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
        ((Nat.choose k (2 * j + 1) : ℤ) * (X1 n hn hn6 : ℤ) ^ (k - 1 - 2 * j) *
          ((qn n : ℤ) * (Y1 n hn hn6 : ℤ) ^ 2) ^ j) := by
    have hpow := pell_pow_quadAlg hn hn6 k
    have him := congr_arg QuadraticAlgebra.im hpow
    dsimp only at him
    rw [pell_binomial_im (qn n : ℤ) (X1 n hn hn6 : ℤ) (Y1 n hn hn6 : ℤ) k hk] at him
    rw [h2] at him
    have hy1_ne : (Y1 n hn hn6 : ℤ) ≠ 0 := by exact_mod_cast (Y1_pos hn hn6).ne'
    exact mul_left_cancel₀ hy1_ne him.symm
  have hM_eq : (X1 n hn hn6 : ℤ) ^ 2 = (qn n : ℤ) * (Y1 n hn hn6 : ℤ) ^ 2 + 1 := by
    rw [X1_eq, Y1_eq]
    linarith [(pellFundUnit n hn hn6).prop]
  have hM_nat : (X1 n hn hn6) ^ 2 - 1 = qn n * (Y1 n hn hn6) ^ 2 := by
    have hZ : ((X1 n hn hn6 : ℤ) ^ 2 - 1) = (qn n : ℤ) * (Y1 n hn hn6 : ℤ) ^ 2 := by linarith
    have hx1 : 1 ≤ X1 n hn hn6 := by
      have := (pellFundUnit_isFundamental hn hn6).one_lt_x
      have := X1_eq hn hn6
      omega
    have hsq1 : 1 ≤ (X1 n hn hn6) ^ 2 := by nlinarith
    exact_mod_cast (by rw [Nat.cast_sub hsq1, Nat.cast_one]; exact hZ)
  have h5 : ∀ p : ℕ, p.Prime → p ∣ qn n * Y1 n hn hn6 →
      (p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y1 n hn hn6) →
      padicValInt p ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)) = padicValNat p k := by
    intro p hp hpdvd hcond
    rw [h3]
    have hpdvdM : (p : ℤ) ∣ (qn n : ℤ) * (Y1 n hn hn6 : ℤ) ^ 2 := by
      have : qn n * Y1 n hn hn6 ∣ qn n * (Y1 n hn hn6) ^ 2 := by
        rw [sq, ← mul_assoc]; exact dvd_mul_right _ _
      exact_mod_cast dvd_trans hpdvd this
    refine padicValInt_chebyshevU_sum hp hk hpdvdM hM_eq ?_
    rcases hcond with hne | hnk | hy3
    · exact Or.inl hne
    · exact Or.inr (Or.inl hnk)
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (by exact_mod_cast hy3) 2) _))
      · exact Or.inl hp3
  have hU_ne : ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ≠ 0 := by
    intro h0
    have hZ0 : (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ) = 0 := Int.natAbs_eq_zero.mp h0
    rw [hZ0, mul_zero] at h2
    have hYr_pos := Yr_pos hn hn6 hk
    omega
  have h4 : Nat.gcd ((X1 n hn hn6) ^ 2 - 1)
      (((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ^ 2) ∣ k ^ 2 := by
    set g := Nat.gcd ((X1 n hn hn6) ^ 2 - 1)
      (((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ^ 2)
    have hg_ne : g ≠ 0 := by
      intro hg0
      have h0 : (X1 n hn hn6) ^ 2 - 1 = 0 := (Nat.gcd_eq_zero_iff.mp hg0).1
      rw [hM_nat] at h0
      have hpos : 0 < qn n * (Y1 n hn hn6) ^ 2 := mul_pos (qn_pos n) (pow_pos (Y1_pos hn hn6) 2)
      omega
    rw [← Nat.prod_primeFactors_pow_factorization hg_ne]
    refine Finset.prod_dvd_of_coprime (fun p _ q _ hpq => ?_) (fun p hp => ?_)
    · exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (by assumption))
        (Nat.prime_of_mem_primeFactors (by assumption))).mpr hpq |>.pow _ _
    · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have hpg : p ∣ g := Nat.dvd_of_mem_primeFactors hp
      have hp_M : p ∣ qn n * (Y1 n hn hn6) ^ 2 := hM_nat ▸ dvd_trans hpg (Nat.gcd_dvd_left _ _)
      have hp_dvd_qY : p ∣ qn n * Y1 n hn hn6 := by
        rcases hp_prime.dvd_mul.mp hp_M with hq | hy2
        · exact dvd_mul_of_dvd_left hq _
        · exact dvd_mul_of_dvd_right (hp_prime.dvd_of_dvd_pow hy2) _
      have hk2_ne : k ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
      rw [padicValNat_dvd_iff_le hk2_ne, ← Nat.factorization_def g hp_prime]
      by_cases hcond : p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y1 n hn hn6
      · have hv := h5 p hp_prime hp_dvd_qY hcond
        have hg_le_U : padicValNat p g ≤ padicValNat p (((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ^ 2) :=
          padicValNat.dvd_iff_le (pow_ne_zero 2 hU_ne) |>.mp (dvd_trans (Nat.pow_dvd_pow _ le_rfl)
            (dvd_trans ((padicValNat_dvd_iff_le hg_ne).mpr le_rfl) (Nat.gcd_dvd_right _ _)))
        have hval_U2 : padicValNat p (((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ^ 2) =
            2 * padicValNat p k := by
          rw [padicValNat.pow 2 hU_ne]; exact congr_arg (2 * ·) hv
        have hval_k2 : padicValNat p (k ^ 2) = 2 * padicValNat p k := padicValNat.pow 2 (by omega)
        omega
      · push_neg at hcond
        rcases hcond with ⟨rfl, hk3, hy3⟩
        have hM_ndvd9 : ¬ 3 ^ 2 ∣ qn n * (Y1 n hn hn6) ^ 2 := by
          intro h9
          have hq3 : ¬ 3 ^ 2 ∣ qn n := fun h => by
            have := squarefree_qn n 3 (by simpa [sq] using h)
            omega
          have hval : padicValNat 3 (qn n * (Y1 n hn hn6) ^ 2) =
              padicValNat 3 (qn n) + 2 * padicValNat 3 (Y1 n hn hn6) := by
            rw [padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos hn hn6).ne'),
              padicValNat.pow 2 (Y1_pos hn hn6).ne']
          have hle2 : 2 ≤ padicValNat 3 (qn n * (Y1 n hn hn6) ^ 2) :=
            (padicValNat_dvd_iff_le (mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos hn hn6).ne'))).mp h9
          have hq_le1 : padicValNat 3 (qn n) ≤ 1 := by
            by_contra hgt
            exact hq3 ((padicValNat_dvd_iff_le (qn_pos n).ne').mpr (by omega))
          have hy_ge1 : 1 ≤ padicValNat 3 (Y1 n hn hn6) := by omega
          exact hy3 ((padicValNat_dvd_iff_le (Y1_pos hn hn6).ne').mpr hy_ge1 |> fun h =>
            dvd_trans (pow_dvd_pow 3 (by omega : 1 ≤ 1)) h)
        have hg_ndvd9 : ¬ 3 ^ 2 ∣ g := fun h => hM_ndvd9 (hM_nat ▸ dvd_trans h (Nat.gcd_dvd_left _ _))
        have hg_le1 : padicValNat 3 g ≤ 1 := by
          by_contra hgt
          exact hg_ndvd9 ((padicValNat_dvd_iff_le hg_ne).mpr (by omega))
        have hk2_ge2 : 2 ≤ padicValNat 3 (k ^ 2) := by
          rw [padicValNat.pow 2 (by omega)]
          have hk3_ge1 : 1 ≤ padicValNat 3 k := (padicValNat_dvd_iff_le (by omega)).mp hk3
          omega
        omega
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro hn4 m hsol hk_eq p hp_mem hcond
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp_mem).2.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp_dvd_qn : p ∣ qn n := by
    rw [qn_eq_prod_Podd]; exact Finset.dvd_prod_of_mem _ hp_mem
  have hp_dvd_qY : p ∣ qn n * Y1 n hn hn6 := dvd_mul_of_dvd_left hp_dvd_qn _
  have hv := h5 p hp_prime hp_dvd_qY hcond
  obtain ⟨hn6', _, _, hsny⟩ := pellIndex_spec hn4 hsol
  have hsn_eq : (sn n : ℤ) = (Yr n hn hn6 k : ℤ) := by
    rw [Yr_eq, hk_eq, hsny]; rfl
  have hsn_nat : sn n = Y1 n hn hn6 * ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs := by
    have hZ : (sn n : ℤ) = (Y1 n hn hn6 : ℤ) * (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ) := by
      rw [hsn_eq, h2]
    have hnat : sn n = ((Y1 n hn hn6 : ℤ) * (Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs := by
      exact_mod_cast congr_arg Int.natAbs hZ
    rw [hnat, Int.natAbs_mul]
    simp
  have hfac_eq : n.factorial = (qn n * (Y1 n hn hn6) ^ 2) *
      ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs ^ 2 := by
    rw [factorial_eq_qn_mul_sn_sq n, hsn_nat, mul_pow]
    ring
  have hM_ne : qn n * (Y1 n hn hn6) ^ 2 ≠ 0 :=
    mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos hn hn6).ne')
  have hval_fac : padicValNat p n.factorial =
      padicValNat p (qn n * (Y1 n hn hn6) ^ 2) +
        2 * padicValNat p ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs := by
    rw [hfac_eq, padicValNat.mul hM_ne (pow_ne_zero 2 hU_ne), padicValNat.pow 2 hU_ne]
  have hv_nat : padicValNat p ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)).natAbs = padicValNat p k := hv
  omega

lemma exists_alphaRank {n p : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (hp : p ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ p ∣ Yr n hn hn6 r := by
  haveI : NeZero p := ⟨hp⟩
  let f : Fin (p ^ 2 + 1) → ZMod p × ZMod p :=
    fun i => ((Xr n hn hn6 i.1 : ZMod p), (Yr n hn hn6 i.1 : ZMod p))
  have hcard : Fintype.card (ZMod p × ZMod p) < Fintype.card (Fin (p ^ 2 + 1)) := by
    simp [ZMod.card]; ring_nf; omega
  obtain ⟨i, j, hij_ne, hij_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  wlog hij : i.1 < j.1
  · exact this hn hn6 hp j i hij_ne.symm hij_eq.symm (by omega)
  refine ⟨j.1 - i.1, by omega, ?_⟩
  have hprod : pellFundUnit n hn hn6 ^ ((j.1 - i.1 : ℕ) : ℤ) * pellFundUnit n hn hn6 ^ (i.1 : ℤ) =
      pellFundUnit n hn hn6 ^ (j.1 : ℤ) := by
    rw [← zpow_add]
    congr 1
    omega
  have hy_eq : (Yr n hn hn6 j.1 : ℤ) =
      (Xr n hn hn6 (j.1 - i.1) : ℤ) * (Yr n hn hn6 i.1 : ℤ) +
        (Yr n hn hn6 (j.1 - i.1) : ℤ) * (Xr n hn hn6 i.1 : ℤ) := by
    rw [Yr_eq, Xr_eq, Yr_eq, Yr_eq, Xr_eq]
    have := congr_arg Pell.Solution₁.y hprod
    simpa [Pell.Solution₁.mul_y] using this.symm
  have hx_eq : (Xr n hn hn6 j.1 : ℤ) =
      (Xr n hn hn6 (j.1 - i.1) : ℤ) * (Xr n hn hn6 i.1 : ℤ) +
        (qn n : ℤ) * (Yr n hn hn6 (j.1 - i.1) : ℤ) * (Yr n hn hn6 i.1 : ℤ) := by
    rw [Xr_eq, Xr_eq, Xr_eq, Yr_eq, Yr_eq]
    have := congr_arg Pell.Solution₁.x hprod
    simpa [Pell.Solution₁.mul_x] using this.symm
  have hprop_i : (Xr n hn hn6 i.1 : ℤ) ^ 2 - (qn n : ℤ) * (Yr n hn hn6 i.1 : ℤ) ^ 2 = 1 := by
    rw [Xr_eq, Yr_eq]
    exact (pellFundUnit n hn hn6 ^ (i.1 : ℤ)).prop
  have hYr_id : (Yr n hn hn6 (j.1 - i.1) : ℤ) =
      (Xr n hn hn6 i.1 : ℤ) * (Yr n hn hn6 j.1 : ℤ) -
        (Yr n hn hn6 i.1 : ℤ) * (Xr n hn hn6 j.1 : ℤ) := by
    rw [hy_eq, hx_eq]
    nlinarith [hprop_i]
  have hcast : ((Yr n hn hn6 (j.1 - i.1) : ℤ) : ZMod p) = 0 := by
    rw [hYr_id]
    push_cast
    have hx_mod : (Xr n hn hn6 j.1 : ZMod p) = (Xr n hn hn6 i.1 : ZMod p) := (Prod.ext_iff.mp hij_eq).1.symm
    have hy_mod : (Yr n hn hn6 j.1 : ZMod p) = (Yr n hn hn6 i.1 : ZMod p) := (Prod.ext_iff.mp hij_eq).2.symm
    rw [hx_mod, hy_mod]
    ring
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd (Yr n hn hn6 (j.1 - i.1)) p).mp (by simpa using hcast)

/-- Projective rank of apparition `α_p(q_n) := min {r ≥ 1 : p ∣ Y_r(q_n)}`. -/
def alphaRank (n p : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  open Classical in
  if hp : p = 0 then 0 else Nat.find (exists_alphaRank hn hn6 hp)

theorem lemma_3_2_ii (n p : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hp_ndvd : ¬ p ∣ qn n) :
    let α := alphaRank n p hn hn6
    1 ≤ α ∧
    ((α : ℤ) ∣ ((p : ℤ) - jacobiSym (qn n : ℤ) p) / 2) ∧
    (∀ k : ℕ, 1 ≤ k →
      (p ∣ Yr n hn hn6 k ↔ α ∣ k) ∧
      (α ∣ k → padicValNat p (Yr n hn hn6 k) = padicValNat p (Yr n hn hn6 α) + padicValNat p (k / α))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set α := alphaRank n p hn hn6
  have hp0 : p ≠ 0 := hp.ne_zero
  have hα_spec := Nat.find_spec (exists_alphaRank hn hn6 hp0)
  have hα_eq : α = Nat.find (exists_alphaRank hn hn6 hp0) := by
    simp [α, alphaRank, hp0]
  have hα1 : 1 ≤ α := by rw [hα_eq]; exact hα_spec.1
  have hp_dvd_Yα : p ∣ Yr n hn hn6 α := by rw [hα_eq]; exact hα_spec.2
  have hα_min : ∀ r : ℕ, 1 ≤ r → r < α → ¬ p ∣ Yr n hn hn6 r := by
    intro r hr1 hr_lt hpr
    rw [hα_eq] at hr_lt
    exact Nat.find_min (exists_alphaRank hn hn6 hp0) hr_lt ⟨hr1, hpr⟩
  have hmul_dvd : ∀ q : ℕ, 1 ≤ q → p ∣ Yr n hn hn6 (α * q) := by
    intro q hq
    have hpow : (⟨(Xr n hn hn6 α : ℤ), (Yr n hn hn6 α : ℤ)⟩ : QuadraticAlgebra ℤ (qn n : ℤ) 0) ^ q =
        ⟨(Xr n hn hn6 (α * q) : ℤ), (Yr n hn hn6 (α * q) : ℤ)⟩ := by
      have h1 := pell_pow_quadAlg hn hn6 α
      have h2 := pell_pow_quadAlg hn hn6 (α * q)
      rw [← h1, ← pow_mul, h2]
    have him := congr_arg QuadraticAlgebra.im hpow
    dsimp only at him
    rw [pell_binomial_im (qn n : ℤ) (Xr n hn hn6 α : ℤ) (Yr n hn hn6 α : ℤ) q hq] at him
    have hpZ : (p : ℤ) ∣ (Yr n hn hn6 (α * q) : ℤ) := by
      rw [← him]
      exact dvd_mul_of_dvd_left (by exact_mod_cast hp_dvd_Yα) _
    exact_mod_cast hpZ
  have h_iff : ∀ k : ℕ, 1 ≤ k → (p ∣ Yr n hn hn6 k ↔ α ∣ k) := by
    intro k hk
    constructor
    · intro hpk
      by_contra hndvd
      set q := k / α
      set r := k % α
      have hr_pos : 1 ≤ r := by
        have : r ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
        omega
      have hr_lt : r < α := Nat.mod_lt k (by omega)
      have hk_eq : k = α * q + r := (Nat.div_add_mod k α).symm
      have hprod : pellFundUnit n hn hn6 ^ ((α * q : ℕ) : ℤ) * pellFundUnit n hn hn6 ^ (r : ℤ) =
          pellFundUnit n hn hn6 ^ (k : ℤ) := by
        rw [← zpow_add]; congr 1; omega
      have hy_eq : (Yr n hn hn6 k : ℤ) =
          (Xr n hn hn6 (α * q) : ℤ) * (Yr n hn hn6 r : ℤ) +
            (Yr n hn hn6 (α * q) : ℤ) * (Xr n hn hn6 r : ℤ) := by
        rw [Yr_eq, Xr_eq, Yr_eq, Yr_eq, Xr_eq]
        have := congr_arg Pell.Solution₁.y hprod
        simpa [Pell.Solution₁.mul_y] using this.symm
      have hp_Yq : p ∣ Yr n hn hn6 (α * q) := by
        by_cases hq0 : q = 0
        · simp [hq0, Yr_eq]
        · exact hmul_dvd q (by omega)
      have hp_prod : p ∣ Xr n hn hn6 (α * q) * Yr n hn hn6 r := by
        have hZ : (p : ℤ) ∣ (Xr n hn hn6 (α * q) : ℤ) * (Yr n hn hn6 r : ℤ) := by
          have : (Xr n hn hn6 (α * q) : ℤ) * (Yr n hn hn6 r : ℤ) =
              (Yr n hn hn6 k : ℤ) - (Yr n hn hn6 (α * q) : ℤ) * (Xr n hn hn6 r : ℤ) := by linarith
          rw [this]
          exact dvd_sub (by exact_mod_cast hpk) (dvd_mul_of_dvd_left (by exact_mod_cast hp_Yq) _)
        exact_mod_cast hZ
      have hp_ndvd_X : ¬ p ∣ Xr n hn hn6 (α * q) := by
        intro hpX
        have hprop : (Xr n hn hn6 (α * q) : ℤ) ^ 2 - (qn n : ℤ) * (Yr n hn hn6 (α * q) : ℤ) ^ 2 = 1 := by
          rw [Xr_eq, Yr_eq]; exact (pellFundUnit n hn hn6 ^ ((α * q : ℕ) : ℤ)).prop
        have hd1 : (p : ℤ) ∣ 1 := by
          have : (1 : ℤ) = (Xr n hn hn6 (α * q) : ℤ) ^ 2 - (qn n : ℤ) * (Yr n hn hn6 (α * q) : ℤ) ^ 2 := by linarith
          rw [this]
          exact dvd_sub (dvd_pow (by exact_mod_cast hpX) (by norm_num))
            (dvd_mul_of_dvd_right (dvd_pow (by exact_mod_cast hp_Yq) (by norm_num)) _)
        have := Int.le_of_dvd (by norm_num) hd1
        omega
      rcases hp.dvd_mul.mp hp_prod with hX | hY
      · exact hp_ndvd_X hX
      · exact hα_min r hr_pos hr_lt hY
    · rintro ⟨q, rfl⟩
      have hq1 : 1 ≤ q := by
        by_contra hq0
        have : q = 0 := by omega
        subst this; simp at hk
      exact hmul_dvd q hq1
  have hval : ∀ k : ℕ, 1 ≤ k → α ∣ k →
      padicValNat p (Yr n hn hn6 k) = padicValNat p (Yr n hn hn6 α) + padicValNat p (k / α) := by
    intro k hk hdiv
    obtain ⟨q, rfl⟩ := hdiv
    have hq1 : 1 ≤ q := by
      by_contra hq0
      have : q = 0 := by omega
      subst this; simp at hk
    have hpow : (⟨(Xr n hn hn6 α : ℤ), (Yr n hn hn6 α : ℤ)⟩ : QuadraticAlgebra ℤ (qn n : ℤ) 0) ^ q =
        ⟨(Xr n hn hn6 (α * q) : ℤ), (Yr n hn hn6 (α * q) : ℤ)⟩ := by
      have h1 := pell_pow_quadAlg hn hn6 α
      have h2 := pell_pow_quadAlg hn hn6 (α * q)
      rw [← h1, ← pow_mul, h2]
    have him := congr_arg QuadraticAlgebra.im hpow
    dsimp only at him
    rw [pell_binomial_im (qn n : ℤ) (Xr n hn hn6 α : ℤ) (Yr n hn hn6 α : ℤ) q hq1] at him
    set S : ℤ := ∑ j ∈ Finset.range ((q - 1) / 2 + 1),
        (Nat.choose q (2 * j + 1) : ℤ) * (Xr n hn hn6 α : ℤ) ^ (q - 1 - 2 * j) *
          ((qn n : ℤ) * (Yr n hn hn6 α : ℤ) ^ 2) ^ j
    have hX_prop : (Xr n hn hn6 α : ℤ) ^ 2 = (qn n : ℤ) * (Yr n hn hn6 α : ℤ) ^ 2 + 1 := by
      rw [Xr_eq, Yr_eq]
      linarith [(pellFundUnit n hn hn6 ^ (α : ℤ)).prop]
    have hpM : (p : ℤ) ∣ (qn n : ℤ) * (Yr n hn hn6 α : ℤ) ^ 2 :=
      dvd_mul_of_dvd_right (dvd_pow (by exact_mod_cast hp_dvd_Yα) (by norm_num)) _
    have hpM2 : (p : ℤ) ^ 2 ∣ (qn n : ℤ) * (Yr n hn hn6 α : ℤ) ^ 2 :=
      dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (by exact_mod_cast hp_dvd_Yα) 2) _
    have hvS : padicValInt p S = padicValNat p q :=
      padicValInt_chebyshevU_sum hp hq1 hpM hX_prop (Or.inr (Or.inr hpM2))
    have hS_ne : S ≠ 0 := by
      intro h0
      have hY0 : Yr n hn hn6 (α * q) = 0 := by
        have : (Yr n hn hn6 (α * q) : ℤ) = 0 := by rw [← him, h0, mul_zero]
        exact_mod_cast this
      have hpos := Yr_pos hn hn6 hk
      omega
    have hY_nat : Yr n hn hn6 (α * q) = Yr n hn hn6 α * S.natAbs := by
      have : (Yr n hn hn6 (α * q) : ℤ) = (Yr n hn hn6 α : ℤ) * S := him.symm
      have h1 := congr_arg Int.natAbs this
      simpa [Int.natAbs_mul] using h1
    rw [hY_nat, padicValNat.mul (Yr_pos hn hn6 hα1).ne' (Int.natAbs_ne_zero.mpr hS_ne),
      Nat.mul_div_cancel_left q (by omega : 0 < α)]
    exact congr_arg (padicValNat p (Yr n hn hn6 α) + ·) hvS
  have h_half_dvd : (α : ℤ) ∣ ((p : ℤ) - jacobiSym (qn n : ℤ) p) / 2 := by
    have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    have hjac_sq : jacobiSym (qn n : ℤ) p = 1 ∨ jacobiSym (qn n : ℤ) p = -1 := by
      have h1 : (jacobiSym (qn n : ℤ) p : ZMod p) = ((qn n : ℤ) : ZMod p) ^ (p / 2) := by
        have hleg : jacobiSym (qn n : ℤ) p = legendreSym p (qn n : ℤ) := by
          unfold jacobiSym
          rw [Nat.primeFactorsList_prime hp, List.map_singleton, List.prod_singleton]
        rw [hleg, legendreSym.eq_pow]
      have hne0 : ((qn n : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        exact hp_ndvd ((ZMod.natCast_zmod_eq_zero_iff_dvd (qn n) p).mp (by simpa using h0))
      have hflt : ((qn n : ℤ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne0
      have hsq1 : (((qn n : ℤ) : ZMod p) ^ (p / 2)) ^ 2 = 1 := by
        rw [← pow_mul, show p / 2 * 2 = p - 1 by omega, hflt]
      rw [← h1] at hsq1
      have hcases : (jacobiSym (qn n : ℤ) p : ZMod p) = 1 ∨ (jacobiSym (qn n : ℤ) p : ZMod p) = -1 :=
        sq_eq_one_iff.mp hsq1
      have hval := jacobiSym.trichotomy (qn n : ℤ) p
      rcases hval with h0 | h1' | hm1
      · exfalso
        rw [h0, Int.cast_zero] at hcases
        rcases hcases with hc | hc
        · exact zero_ne_one hc
        · have : (1 : ZMod p) = 0 := by linear_combination -hc
          exact one_ne_zero this
      · exact Or.inl h1'
      · exact Or.inr hm1
    set m : ℕ := ((p : ℤ) - jacobiSym (qn n : ℤ) p).toNat / 2
    have hm1 : 1 ≤ m := by
      rcases hjac_sq with hj | hj <;> rw [hj] <;> omega
    have hm_eq : (m : ℤ) = ((p : ℤ) - jacobiSym (qn n : ℤ) p) / 2 := by
      rcases hjac_sq with hj | hj <;> rw [hj] <;> simp only [m] <;> omega
    rw [← hm_eq]
    suffices h : p ∣ Yr n hn hn6 m by
      exact_mod_cast (h_iff m hm1).mp h
    let R := QuadraticAlgebra (ZMod p) (qn n : ZMod p) 0
    let z : R := ⟨(X1 n hn hn6 : ZMod p), (Y1 n hn hn6 : ZMod p)⟩
    have hz_norm : z.re ^ 2 - (qn n : ZMod p) * z.im ^ 2 = 1 := by
      have h1 : ((X1 n hn hn6 : ℤ) ^ 2 - (qn n : ℤ) * (Y1 n hn hn6 : ℤ) ^ 2 : ℤ) = 1 := by
        rw [X1_eq, Y1_eq]; exact (pellFundUnit n hn hn6).prop
      have h2 := congr_arg (Int.cast (R := ZMod p)) h1
      push_cast at h2
      exact h2
    have hz_pow_p : z ^ p = ⟨z.re, (jacobiSym (qn n : ℤ) p : ZMod p) * z.im⟩ := by
      have hsplit : z = ⟨z.re, 0⟩ + ⟨0, z.im⟩ := by ext <;> simp
      rw [hsplit, add_pow]
      have hzero : ∀ i ∈ Finset.range (p + 1), i ≠ 0 → i ≠ p →
          (⟨z.re, 0⟩ : R) ^ i * (⟨0, z.im⟩ : R) ^ (p - i) * (Nat.choose p i : R) = 0 := by
        intro i hi hi0 hip
        have hi_lt : i < p := by
          have := Finset.mem_range.mp hi; omega
        have hdvd : p ∣ Nat.choose p i := hp.dvd_choose_self hi0 hi_lt
        have hc0 : (Nat.choose p i : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
        have hcR : (Nat.choose p i : R) = 0 := by
          ext <;> simp [hc0]
        rw [hcR, mul_zero]
      have h0mem : 0 ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by omega)
      have hpmem : p ∈ (Finset.range (p + 1)).erase 0 := Finset.mem_erase.mpr ⟨hp0, Finset.mem_range.mpr (by omega)⟩
      rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ hpmem]
      have hrest : ∑ i ∈ ((Finset.range (p + 1)).erase 0).erase p,
          (⟨z.re, 0⟩ : R) ^ i * (⟨0, z.im⟩ : R) ^ (p - i) * (Nat.choose p i : R) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_erase, Finset.mem_erase] at hi
        exact hzero i hi.2.2 hi.2.1 hi.1
      rw [hrest, add_zero]
      have hp_re : (⟨0, z.im⟩ : R) ^ p = ⟨0, (jacobiSym (qn n : ℤ) p : ZMod p) * z.im⟩ := by
        have hpow_even : ∀ j : ℕ, (⟨0, z.im⟩ : R) ^ (2 * j) = ⟨((qn n : ZMod p) * z.im ^ 2) ^ j, 0⟩ := by
          intro j; induction j with
          | zero => ext <;> simp
          | succ j ih =>
            rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, ih]
            have hsq : (⟨0, z.im⟩ : R) ^ 2 = ⟨(qn n : ZMod p) * z.im ^ 2, 0⟩ := by
              rw [sq]; ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
            rw [hsq]; ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
        have hp_decomp : p = 2 * (p / 2) + 1 := by omega
        rw [hp_decomp, pow_add, pow_one, hpow_even (p / 2)]
        have hjac_pow : (qn n : ZMod p) ^ (p / 2) = (jacobiSym (qn n : ℤ) p : ZMod p) := by
          have hleg : jacobiSym (qn n : ℤ) p = legendreSym p (qn n : ℤ) := by
            unfold jacobiSym
            rw [Nat.primeFactorsList_prime hp, List.map_singleton, List.prod_singleton]
          rw [hleg]
          simpa using (legendreSym.eq_pow p (qn n : ℤ)).symm
        ext
        · simp [QuadraticAlgebra.re_mul]
        · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mk, QuadraticAlgebra.im_mk, zero_mul, add_zero]
          rw [mul_pow, ← pow_mul, show 2 * (p / 2) = p - 1 by omega, ← pow_succ, show p - 1 + 1 = p by omega,
            ZMod.pow_card, hjac_pow]
          ring
      have hre_p : (⟨z.re, 0⟩ : R) ^ p = ⟨z.re, 0⟩ := by
        have hpow_re : ∀ r : ℕ, (⟨z.re, 0⟩ : R) ^ r = ⟨z.re ^ r, 0⟩ := by
          intro r; induction r with
          | zero => ext <;> simp
          | succ r ih => rw [pow_succ, ih]; ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
        rw [hpow_re, ZMod.pow_card]
      simp only [pow_zero, one_mul, tsub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
        Nat.cast_one, mul_one]
      rw [hp_re, hre_p, add_comm]
      ext <;> simp
    have hw_sq : (z ^ m) ^ 2 = 1 := by
      rw [← pow_mul]
      rcases hjac_sq with hj | hj
      · have h2m : 2 * m = p - 1 := by rw [hj] at hm_eq; omega
        rw [h2m]
        have hz_inv : z * ⟨z.re, -z.im⟩ = 1 := by
          ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
          · linear_combination hz_norm
          · ring
        have hzp : z ^ p = z := by rw [hz_pow_p, hj]; ext <;> simp
        calc z ^ (p - 1) = z ^ (p - 1) * (z * ⟨z.re, -z.im⟩) := by rw [hz_inv, mul_one]
          _ = (z ^ (p - 1) * z) * ⟨z.re, -z.im⟩ := by ring
          _ = z ^ p * ⟨z.re, -z.im⟩ := by rw [← pow_succ, show p - 1 + 1 = p by omega]
          _ = z * ⟨z.re, -z.im⟩ := by rw [hzp]
          _ = 1 := hz_inv
      · have h2m : 2 * m = p + 1 := by rw [hj] at hm_eq; omega
        rw [h2m, pow_succ, hz_pow_p, hj]
        ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
        · linear_combination hz_norm
        · ring
    have hz_pow_all : ∀ r : ℕ, z ^ r = ⟨(Xr n hn hn6 r : ZMod p), (Yr n hn hn6 r : ZMod p)⟩ := by
      intro r
      induction r with
      | zero => ext <;> simp [Xr_eq, Yr_eq]
      | succ r ih =>
        rw [pow_succ, ih]
        have hmul := pell_pow_quadAlg hn hn6 (r + 1)
        rw [pow_succ, pell_pow_quadAlg hn hn6 r] at hmul
        have hre := congr_arg (fun u => (u.re : ZMod p)) hmul
        have him := congr_arg (fun u => (u.im : ZMod p)) hmul
        simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mk,
          QuadraticAlgebra.im_mk, Int.cast_add, Int.cast_mul, Int.cast_natCast] at hre him
        ext
        · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_mk, QuadraticAlgebra.im_mk]
          simpa using hre.symm
        · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mk, QuadraticAlgebra.im_mk]
          simpa using him.symm
    have hzm := hz_pow_all m
    have hw_norm : (z ^ m).re ^ 2 - (qn n : ZMod p) * (z ^ m).im ^ 2 = 1 := by
      rw [hzm]
      have hprop : (Xr n hn hn6 m : ℤ) ^ 2 - (qn n : ℤ) * (Yr n hn hn6 m : ℤ) ^ 2 = 1 := by
        rw [Xr_eq, Yr_eq]; exact (pellFundUnit n hn hn6 ^ (m : ℤ)).prop
      have h2 := congr_arg (Int.cast (R := ZMod p)) hprop
      push_cast at h2
      exact h2
    have hw_sq_re : (z ^ m).re ^ 2 + (qn n : ZMod p) * (z ^ m).im ^ 2 = 1 := by
      have hre := congr_arg QuadraticAlgebra.re hw_sq
      rw [sq] at hre
      simpa [QuadraticAlgebra.re_mul] using hre
    have him_sq : (2 : ZMod p) * (qn n : ZMod p) * (z ^ m).im ^ 2 = 0 := by
      linear_combination hw_sq_re - hw_norm
    have h2_ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hd := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h0)
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hq_ne : (qn n : ZMod p) ≠ 0 := by
      intro h0
      exact hp_ndvd ((ZMod.natCast_zmod_eq_zero_iff_dvd (qn n) p).mp (by simpa using h0))
    have him0 : (z ^ m).im = 0 := by
      have hmul0 : (2 : ZMod p) * (qn n : ZMod p) ≠ 0 := mul_ne_zero h2_ne hq_ne
      have hsq0 : (z ^ m).im ^ 2 = 0 := (mul_eq_zero.mp him_sq).resolve_left hmul0
      exact pow_eq_zero hsq0
    rw [hzm] at him0
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (Yr n hn hn6 m) p).mp (by simpa using him0)
  exact ⟨hα1, h_half_dvd, fun k hk => ⟨h_iff k hk, hval k hk⟩⟩

lemma Yr_strictMono {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) : StrictMono (Yr n hn hn6) := by
  refine strictMono_nat_of_lt_succ fun r => ?_
  have hfund := pellFundUnit_isFundamental hn hn6
  have hx1 : (2 : ℤ) ≤ (X1 n hn hn6 : ℤ) := by
    have := hfund.one_lt_x
    have := X1_eq hn hn6
    omega
  have hy1 : (1 : ℤ) ≤ (Y1 n hn hn6 : ℤ) := by
    have := hfund.zero_lt_y
    have := Y1_eq hn hn6
    omega
  have hxr : (1 : ℤ) ≤ (Xr n hn hn6 r : ℤ) := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [Xr_eq]
    · have := (pell_xy_pos hn hn6 r hr).1
      have := Xr_eq hn hn6 r
      omega
  have hyr : (0 : ℤ) ≤ (Yr n hn hn6 r : ℤ) := by exact_mod_cast Nat.zero_le _
  have hmul : (Yr n hn hn6 (r + 1) : ℤ) =
      (Xr n hn hn6 r : ℤ) * (Y1 n hn hn6 : ℤ) + (Yr n hn hn6 r : ℤ) * (X1 n hn hn6 : ℤ) := by
    rw [Yr_eq, Xr_eq, Yr_eq, X1_eq, Y1_eq, Nat.cast_succ, zpow_add, zpow_one, Pell.Solution₁.mul_y]
  have hlt : (Yr n hn hn6 r : ℤ) < (Yr n hn hn6 (r + 1) : ℤ) := by
    rw [hmul]
    nlinarith
  exact_mod_cast hlt


end BrocardFormalization

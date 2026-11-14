/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParity
import BrocardFormalization.PellAndIwasawa
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Section 5: The Fundamental Regime `k = 1` and Rédei–Reichardt Cohomology

This module translates Section 5 of the manuscript:
* `prop_5_1_i`, `prop_5_1_ii`: Continued-fraction midpoint denominator and square-root conductor bias.
* `theorem_5_2_i`, `theorem_5_2_ii`: Midpoint core bipartition, cross-symmetry laws,
  unconditional radical bounds, and effective Landau–Siegel sub-exponential core bounds.
* `lemma_5_3_i`, `lemma_5_3_ii`: Homogeneous `𝔽₂`-Laplacian cascade, Fermat-quotient equations,
  and Wolstenholme evaluation on `(n/3, n/2]`.
* `prop_5_4`: Explicit `𝔽₂` block structure of `ℳ_n^{(1)}` and all-ones reciprocity duality
  (with Audit Item 3 correcting `-q_n^*/p_i` to `-q_n/p_i`).
* `theorem_5_5_i`, `theorem_5_5_ii`: Galois cohomology exact sequence, Rédei–Reichardt 4-rank
  identity, deterministic `𝒫_even^-(n)`-absorption, and reduced dual quartic laws.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### Auxiliary Arithmetic & Squarefree-Core Helpers -/

private lemma oddPart_pos_of_pos {a : ℕ} (ha : 0 < a) : 0 < oddPart a := by
  unfold oddPart
  exact Nat.div_pos (Nat.le_of_dvd ha (Nat.ordProj_dvd a 2)) (pow_pos (by norm_num) _)

private lemma oddPart_le {a : ℕ} : oddPart a ≤ a := by
  unfold oddPart; exact Nat.div_le_self a _

private lemma oddPart_dvd {a : ℕ} : oddPart a ∣ a := by
  unfold oddPart; exact Nat.div_dvd_of_dvd (Nat.ordProj_dvd a 2)

private lemma oddPart_odd {a : ℕ} (ha : a ≠ 0) : ¬ 2 ∣ oddPart a := by
  unfold oddPart; exact Nat.not_dvd_ordCompl (by decide) ha

private lemma oddPart_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    oddPart (a * b) = oddPart a * oddPart b := by
  unfold oddPart
  have h1 : padicValNat 2 (a * b) = padicValNat 2 a + padicValNat 2 b := padicValNat.mul ha hb
  rw [h1, pow_add]
  rcases (pow_padicValNat_dvd : 2 ^ padicValNat 2 a ∣ a) with ⟨ka, hka⟩
  rcases (pow_padicValNat_dvd : 2 ^ padicValNat 2 b ∣ b) with ⟨kb, hkb⟩
  have hka_eq : a / 2 ^ padicValNat 2 a = ka := by
    rw [hka, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hkb_eq : b / 2 ^ padicValNat 2 b = kb := by
    rw [hkb, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  rw [hka_eq, hkb_eq]
  calc (a * b) / (2 ^ padicValNat 2 a * 2 ^ padicValNat 2 b)
      = ((2 ^ padicValNat 2 a * 2 ^ padicValNat 2 b) * (ka * kb)) /
          (2 ^ padicValNat 2 a * 2 ^ padicValNat 2 b) := by congr 1; rw [hka, hkb]; ring
    _ = ka * kb := Nat.mul_div_cancel_left _ (mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _))

private lemma oddPart_pow {a k : ℕ} (ha : a ≠ 0) : oddPart (a ^ k) = (oddPart a) ^ k := by
  induction k with
  | zero => simp [oddPart]
  | succ k ih => rw [pow_succ, pow_succ, oddPart_mul (pow_ne_zero k ha) ha, ih]

private lemma dvd_coreNat_iff {a p : ℕ} (ha : a ≠ 0) (hp : p.Prime) :
    p ∣ coreNat a ↔ p ∣ a ∧ ¬ 2 ∣ padicValNat p a := by
  unfold coreNat
  haveI : Fact p.Prime := ⟨hp⟩
  rw [hp.dvd_finset_prod_iff]
  constructor
  · rintro ⟨q, hq, hpd⟩
    have hq_mem := Finset.mem_filter.mp hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq_mem.1
    have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpd
    subst hpeq
    exact ⟨Nat.dvd_of_mem_primeFactors hq_mem.1, hq_mem.2⟩
  · rintro ⟨hpa, hodd⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpa, ha⟩, hodd⟩, dvd_rfl⟩

private lemma coreNat_dvd_self {a : ℕ} (ha : a ≠ 0) : coreNat a ∣ a := by
  rw [coreNat_mul_sqrtPart_sq ha]; exact dvd_mul_right _ _

private lemma coreNat_eq_self_of_squarefree {a : ℕ} (ha : a ≠ 0) (hsq : Squarefree a) :
    coreNat a = a := by
  have h1 := coreNat_mul_sqrtPart_sq ha
  have hsq_dvd : (sqrtPartNat a) ^ 2 ∣ a := ⟨coreNat a, by linarith⟩
  have hs1 : sqrtPartNat a = 1 := by
    have := hsq (sqrtPartNat a) (by simpa [sq] using hsq_dvd)
    exact Nat.isUnit_iff.mp this
  rw [hs1, one_pow, mul_one] at h1
  exact h1.symm

private lemma coreNat_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) : coreNat (a * b) = coreNat a * coreNat b := by
  apply Nat.eq_of_factorization_eq coreNat_pos.ne' (mul_pos coreNat_pos coreNat_pos).ne'
  intro p
  by_cases hp : p.Prime
  · have h_lhs : (coreNat (a * b)).factorization p = if p ∣ coreNat (a * b) then 1 else 0 := by
      by_cases hd : p ∣ coreNat (a * b)
      · rw [if_pos hd]
        have hsq := squarefree_coreNat (A := a * b)
        have h2 : ¬ p ^ 2 ∣ coreNat (a * b) := fun h => hp.not_isUnit (hsq p (by simpa [sq] using h))
        have h1 := hp.factorization_pos_of_dvd coreNat_pos.ne' hd
        have hlt : (coreNat (a * b)).factorization p < 2 := by
          by_contra hge; push_neg at hge
          exact h2 ((hp.pow_dvd_iff_le_factorization coreNat_pos.ne').mpr hge)
        omega
      · rw [if_neg hd, Nat.factorization_eq_zero_of_not_dvd hd]
    have h_rhs1 : (coreNat a).factorization p = if p ∣ coreNat a then 1 else 0 := by
      by_cases hd : p ∣ coreNat a
      · rw [if_pos hd]
        have h2 : ¬ p ^ 2 ∣ coreNat a := fun h => hp.not_isUnit (squarefree_coreNat p (by simpa [sq] using h))
        have h1 := hp.factorization_pos_of_dvd coreNat_pos.ne' hd
        have hlt : (coreNat a).factorization p < 2 := by
          by_contra hge; push_neg at hge
          exact h2 ((hp.pow_dvd_iff_le_factorization coreNat_pos.ne').mpr hge)
        omega
      · rw [if_neg hd, Nat.factorization_eq_zero_of_not_dvd hd]
    have h_rhs2 : (coreNat b).factorization p = if p ∣ coreNat b then 1 else 0 := by
      by_cases hd : p ∣ coreNat b
      · rw [if_pos hd]
        have h2 : ¬ p ^ 2 ∣ coreNat b := fun h => hp.not_isUnit (squarefree_coreNat p (by simpa [sq] using h))
        have h1 := hp.factorization_pos_of_dvd coreNat_pos.ne' hd
        have hlt : (coreNat b).factorization p < 2 := by
          by_contra hge; push_neg at hge
          exact h2 ((hp.pow_dvd_iff_le_factorization coreNat_pos.ne').mpr hge)
        omega
      · rw [if_neg hd, Nat.factorization_eq_zero_of_not_dvd hd]
    rw [Nat.factorization_mul coreNat_pos.ne' coreNat_pos.ne', Finsupp.add_apply, h_lhs, h_rhs1, h_rhs2]
    rw [dvd_coreNat_iff (mul_ne_zero ha hb) hp, dvd_coreNat_iff ha hp, dvd_coreNat_iff hb hp]
    by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b
    · exfalso; exact hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpa hpb)
    · have hvb : padicValNat p b = 0 := padicValNat.eq_zero_of_not_dvd hpb
      have hvm : padicValNat p (a * b) = padicValNat p a := by rw [padicValNat.mul ha hb, hvb, add_zero]
      simp [hp.dvd_mul.mpr (Or.inl hpa), hpa, hpb, hvm]
    · have hva : padicValNat p a = 0 := padicValNat.eq_zero_of_not_dvd hpa
      have hvm : padicValNat p (a * b) = padicValNat p b := by rw [padicValNat.mul ha hb, hva, zero_add]
      simp [hp.dvd_mul.mpr (Or.inr hpb), hpa, hpb, hvm]
    · simp [hp.dvd_mul, hpa, hpb]
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

private lemma coreNat_mul_sq {a s : ℕ} (ha : a ≠ 0) (hs : s ≠ 0) :
    coreNat (a * s ^ 2) = coreNat a := by
  apply Nat.eq_of_factorization_eq coreNat_pos.ne' coreNat_pos.ne'
  intro p
  by_cases hp : p.Prime
  · have h1 : p ∣ coreNat (a * s ^ 2) ↔ p ∣ coreNat a := by
      rw [dvd_coreNat_iff (mul_ne_zero ha (pow_ne_zero 2 hs)) hp, dvd_coreNat_iff ha hp]
      have hv : padicValNat p (a * s ^ 2) = padicValNat p a + 2 * padicValNat p s := by
        rw [padicValNat.mul ha (pow_ne_zero 2 hs), padicValNat.pow 2 hs]
      have hpar : (¬ 2 ∣ padicValNat p (a * s ^ 2)) ↔ ¬ 2 ∣ padicValNat p a := by rw [hv]; omega
      constructor
      · rintro ⟨hpas, hodd⟩
        have hodd' := hpar.mp hodd
        have hpa : p ∣ a := by
          by_contra hna
          exact hodd' (by rw [padicValNat.eq_zero_of_not_dvd hna]; exact dvd_zero 2)
        exact ⟨hpa, hodd'⟩
      · rintro ⟨hpa, hodd⟩
        exact ⟨dvd_mul_of_dvd_left hpa _, hpar.mpr hodd⟩
    by_cases hd : p ∣ coreNat a
    · have hd' := h1.mpr hd
      have hfa : (coreNat a).factorization p = 1 := by
        have h2 : ¬ p ^ 2 ∣ coreNat a := fun h => hp.not_isUnit (squarefree_coreNat p (by simpa [sq] using h))
        have h1' := hp.factorization_pos_of_dvd coreNat_pos.ne' hd
        have hlt : (coreNat a).factorization p < 2 := by
          by_contra hge; push_neg at hge
          exact h2 ((hp.pow_dvd_iff_le_factorization coreNat_pos.ne').mpr hge)
        omega
      have hfb : (coreNat (a * s ^ 2)).factorization p = 1 := by
        have h2 : ¬ p ^ 2 ∣ coreNat (a * s ^ 2) := fun h => hp.not_isUnit (squarefree_coreNat p (by simpa [sq] using h))
        have h1' := hp.factorization_pos_of_dvd coreNat_pos.ne' hd'
        have hlt : (coreNat (a * s ^ 2)).factorization p < 2 := by
          by_contra hge; push_neg at hge
          exact h2 ((hp.pow_dvd_iff_le_factorization coreNat_pos.ne').mpr hge)
        omega
      rw [hfa, hfb]
    · have hd' : ¬ p ∣ coreNat (a * s ^ 2) := fun h => hd (h1.mp h)
      rw [Nat.factorization_eq_zero_of_not_dvd hd', Nat.factorization_eq_zero_of_not_dvd hd]
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

private lemma oddPart_coreNat {a : ℕ} (ha : a ≠ 0) :
    oddPart (coreNat a) = coreNat (oddPart a) := by
  have hodd_pos : oddPart a ≠ 0 := (oddPart_pos_of_pos (Nat.pos_of_ne_zero ha)).ne'
  apply Nat.eq_of_factorization_eq (oddPart_pos_of_pos coreNat_pos).ne' coreNat_pos.ne'
  intro p
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst hp2
      have h1 : ¬ 2 ∣ oddPart (coreNat a) := oddPart_odd coreNat_pos.ne'
      have h2 : ¬ 2 ∣ coreNat (oddPart a) := fun h => oddPart_odd ha (dvd_trans h (coreNat_dvd_self hodd_pos))
      rw [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2]
    · have hiff : p ∣ oddPart (coreNat a) ↔ p ∣ coreNat (oddPart a) := by
        have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp (by decide)).mpr hp2
        have h1 : p ∣ oddPart (coreNat a) ↔ p ∣ coreNat a := by
          unfold oddPart
          constructor
          · intro h; exact dvd_trans h (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ 2))
          · intro h
            have hdecomp : coreNat a = 2 ^ padicValNat 2 (coreNat a) * (coreNat a / 2 ^ padicValNat 2 (coreNat a)) :=
              (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
            rw [hdecomp] at h
            exact (hcop2.pow_right _).dvd_of_dvd_mul_left h
        have h2 : p ∣ oddPart a ↔ p ∣ a := by
          unfold oddPart
          constructor
          · intro h; exact dvd_trans h (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ 2))
          · intro h
            have hdecomp : a = 2 ^ padicValNat 2 a * (a / 2 ^ padicValNat 2 a) :=
              (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
            rw [hdecomp] at h
            exact (hcop2.pow_right _).dvd_of_dvd_mul_left h
        have hv : padicValNat p (oddPart a) = padicValNat p a := by
          have hdecomp : a = 2 ^ padicValNat 2 a * oddPart a := by
            unfold oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
          have hv2 : padicValNat p (2 ^ padicValNat 2 a) = 0 :=
            padicValNat.eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)))
          conv_rhs => rw [hdecomp]
          rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hodd_pos, hv2, zero_add]
        rw [h1, dvd_coreNat_iff ha hp, dvd_coreNat_iff hodd_pos hp, h2, hv]
      have hsq1 : Squarefree (oddPart (coreNat a)) :=
        (squarefree_coreNat (A := a)).squarefree_of_dvd oddPart_dvd
      have hsq2 : Squarefree (coreNat (oddPart a)) := squarefree_coreNat
      by_cases hd : p ∣ oddPart (coreNat a)
      · have hd' := hiff.mp hd
        have hf1 : (oddPart (coreNat a)).factorization p = 1 := by
          have h2 : ¬ p ^ 2 ∣ oddPart (coreNat a) := fun h => hp.not_isUnit (hsq1 p (by simpa [sq] using h))
          have h1' := hp.factorization_pos_of_dvd (oddPart_pos_of_pos coreNat_pos).ne' hd
          have hlt : (oddPart (coreNat a)).factorization p < 2 := by
            by_contra hge; push_neg at hge
            exact h2 ((hp.pow_dvd_iff_le_factorization (oddPart_pos_of_pos coreNat_pos).ne').mpr hge)
          omega
        have hf2 : (coreNat (oddPart a)).factorization p = 1 := by
          have h2 : ¬ p ^ 2 ∣ coreNat (oddPart a) := fun h => hp.not_isUnit (hsq2 p (by simpa [sq] using h))
          have h1' := hp.factorization_pos_of_dvd coreNat_pos.ne' hd'
          have hlt : (coreNat (oddPart a)).factorization p < 2 := by
            by_contra hge; push_neg at hge
            exact h2 ((hp.pow_dvd_iff_le_factorization coreNat_pos.ne').mpr hge)
          omega
        rw [hf1, hf2]
      · have hd' : ¬ p ∣ coreNat (oddPart a) := fun h => hd (hiff.mpr h)
        rw [Nat.factorization_eq_zero_of_not_dvd hd, Nat.factorization_eq_zero_of_not_dvd hd']
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

private lemma oddPart_coprime_of_gcd_dvd_two {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hgcd : Nat.gcd a b ∣ 2) : Nat.Coprime (oddPart a) (oddPart b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hgt : 1 < Nat.gcd (oddPart a) (oddPart b) := by
    have hpos : 0 < Nat.gcd (oddPart a) (oddPart b) :=
      Nat.gcd_pos_of_pos_left _ (oddPart_pos_of_pos (Nat.pos_of_ne_zero ha))
    omega
  have hdvd : Nat.gcd (oddPart a) (oddPart b) ∣ Nat.gcd a b :=
    Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) oddPart_dvd)
      (dvd_trans (Nat.gcd_dvd_right _ _) oddPart_dvd)
  have hle : Nat.gcd (oddPart a) (oddPart b) ≤ 2 := Nat.le_of_dvd (by norm_num) (dvd_trans hdvd hgcd)
  have heq2 : Nat.gcd (oddPart a) (oddPart b) = 2 := by omega
  exact oddPart_odd ha (heq2 ▸ Nat.gcd_dvd_left _ _)

private lemma sqrtPartNat_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) : sqrtPartNat (a * b) = sqrtPartNat a * sqrtPartNat b := by
  have h1 := coreNat_mul_sqrtPart_sq (mul_ne_zero ha hb)
  have h2 := coreNat_mul_sqrtPart_sq ha
  have h3 := coreNat_mul_sqrtPart_sq hb
  rw [coreNat_mul_of_coprime ha hb hcop] at h1
  have hsq : (sqrtPartNat (a * b)) ^ 2 = (sqrtPartNat a * sqrtPartNat b) ^ 2 := by
    have hmul : (coreNat a * coreNat b) * (sqrtPartNat a * sqrtPartNat b) ^ 2 =
        (coreNat a * (sqrtPartNat a) ^ 2) * (coreNat b * (sqrtPartNat b) ^ 2) := by ring
    rw [← h2, ← h3] at hmul
    exact Nat.eq_of_mul_eq_mul_left (mul_pos coreNat_pos coreNat_pos) (h1.symm.trans hmul)
  exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq

private lemma padicValNat_factorial_eq_one_of_half_lt {n p : ℕ} (hp : p.Prime)
    (hlo : n / 2 < p) (hhi : p ≤ n) : padicValNat p n.factorial = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
  have hnsq : n < p ^ 2 := by
    have := hp.two_le
    nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n (by norm_num : 0 < 2)]
  have hlog : Nat.log p n = 1 := by
    rw [Nat.log_eq_iff (by omega : p ≠ 1) (by omega : n ≠ 0)]
    exact ⟨by simpa using hhi, by simpa using hnsq⟩
  rw [hlog, Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Ico_self, Finset.sum_empty,
    zero_add, pow_one] at hleg
  have hdiv : n / p = 1 := Nat.div_eq_of_lt_le (by omega)
    (by nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n (by norm_num : 0 < 2)])
  rw [hdiv] at hleg
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  exact Nat.eq_of_mul_eq_mul_left hp1 (by omega)

/-! ### 5.1 Midpoint Core Bipartition, Cross-Symmetry, and Landau–Siegel Bounds -/

/-- Midpoint square-free core `δ₁^mid(n) := core(X₁(q_n) - 1)` (5.1). -/
def deltaMid1 (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  coreNat (X1 n hn hn6 - 1)

/-- Midpoint square-free core `δ₂^mid(n) := core(X₁(q_n) + 1)` (5.1). -/
def deltaMid2 (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  coreNat (X1 n hn hn6 + 1)

theorem prop_5_1_i (n : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6) :
    let d1s := oddPart (deltaMid1 n (by omega) hn6)
    let d2s := oddPart (deltaMid2 n (by omega) hn6)
    d1s * d2s = oddPart (qn n) ∧
    Nat.gcd d1s d2s = 1 ∧
    d1s ≠ d2s ∧
    ((min d1s d2s : ℝ) < Real.sqrt (oddPart (qn n))) ∧
    Real.sqrt (oddPart (qn n)) ≤ Real.sqrt (qn n) ∧
    ∃ (L M Qstar : ℕ) (a : ℤ) (sign : Bool),
      L = 2 * M ∧ 0 < M ∧ 0 < Qstar ∧ (Qstar : ℝ) < 2 * Real.sqrt (qn n) ∧
      Qstar ∣ 2 * qn n ∧ a ∈ ({-1, 0, 1} : Set ℤ) ∧
      (Qstar : ℝ) = (2 : ℝ) ^ a *
        ((if sign then deltaMid1 n (by omega) hn6 else deltaMid2 n (by omega) hn6 : ℕ) : ℝ) := by
  dsimp only
  have hfund := pellFundUnit_isFundamental (by omega : 3 ≤ n) hn6
  have hx_pos : 0 ≤ (pellFundUnit n (by omega) hn6).x := by linarith [hfund.one_lt_x]
  have hy_pos : 0 ≤ (pellFundUnit n (by omega) hn6).y := by linarith [hfund.zero_lt_y]
  have hX1_gt1 : 1 < X1 n (by omega) hn6 := by
    unfold X1
    have h1 := hfund.one_lt_x
    have h2 : ((pellFundUnit n (by omega) hn6).x.natAbs : ℤ) = (pellFundUnit n (by omega) hn6).x :=
      Int.natAbs_of_nonneg hx_pos
    omega
  have hY1_pos : 0 < Y1 n (by omega) hn6 := Y1_pos (by omega) hn6
  have hpell_eq : X1 n (by omega) hn6 ^ 2 = qn n * Y1 n (by omega) hn6 ^ 2 + 1 := by
    have hprop := (pellFundUnit n (by omega) hn6).prop
    have h2 : ((X1 n (by omega) hn6 : ℤ)) = (pellFundUnit n (by omega) hn6).x := by
      unfold X1; exact Int.natAbs_of_nonneg hx_pos
    have h3 : ((Y1 n (by omega) hn6 : ℤ)) = (pellFundUnit n (by omega) hn6).y := by
      unfold Y1; exact Int.natAbs_of_nonneg hy_pos
    have hZ : (X1 n (by omega) hn6 : ℤ) ^ 2 = (qn n : ℤ) * (Y1 n (by omega) hn6 : ℤ) ^ 2 + 1 := by
      rw [h2, h3]; linarith
    exact_mod_cast hZ
  set u1 := X1 n (by omega) hn6 - 1
  set u2 := X1 n (by omega) hn6 + 1
  have hu1_pos : 0 < u1 := by omega
  have hu2_pos : 0 < u2 := by omega
  have hu_prod : u1 * u2 = qn n * Y1 n (by omega) hn6 ^ 2 := by
    have h1 : u1 * u2 + 1 = X1 n (by omega) hn6 ^ 2 := by
      dsimp only [u1, u2]
      zify [show 1 ≤ X1 n (by omega) hn6 by omega]
      ring
    omega
  have hgcd_2 : Nat.gcd u1 u2 ∣ 2 := by
    have hsub : u2 - u1 = 2 := by dsimp only [u1, u2]; omega
    rw [← hsub]
    exact Nat.dvd_sub (Nat.gcd_dvd_right u1 u2) (Nat.gcd_dvd_left u1 u2)
  have hcop_odd : Nat.Coprime (oddPart u1) (oddPart u2) :=
    oddPart_coprime_of_gcd_dvd_two hu1_pos.ne' hu2_pos.ne' hgcd_2
  have hd1_eq : oddPart (deltaMid1 n (by omega) hn6) = coreNat (oddPart u1) :=
    oddPart_coreNat hu1_pos.ne'
  have hd2_eq : oddPart (deltaMid2 n (by omega) hn6) = coreNat (oddPart u2) :=
    oddPart_coreNat hu2_pos.ne'
  have hprod_eq : oddPart (deltaMid1 n (by omega) hn6) * oddPart (deltaMid2 n (by omega) hn6) = oddPart (qn n) := by
    rw [hd1_eq, hd2_eq, ← coreNat_mul_of_coprime (oddPart_pos_of_pos hu1_pos).ne'
      (oddPart_pos_of_pos hu2_pos).ne' hcop_odd, ← oddPart_mul hu1_pos.ne' hu2_pos.ne', hu_prod,
      oddPart_mul (qn_pos n).ne' (pow_ne_zero 2 hY1_pos.ne'), oddPart_pow hY1_pos.ne',
      coreNat_mul_sq (oddPart_pos_of_pos (qn_pos n)).ne' (oddPart_pos_of_pos hY1_pos).ne',
      coreNat_eq_self_of_squarefree (oddPart_pos_of_pos (qn_pos n)).ne'
        ((squarefree_qn n).squarefree_of_dvd oddPart_dvd)]
  have hgcd_1 : Nat.gcd (oddPart (deltaMid1 n (by omega) hn6)) (oddPart (deltaMid2 n (by omega) hn6)) = 1 := by
    rw [hd1_eq, hd2_eq, ← Nat.coprime_iff_gcd_eq_one]
    exact (hcop_odd.coprime_dvd_left (coreNat_dvd_self (oddPart_pos_of_pos hu1_pos).ne')).coprime_dvd_right
      (coreNat_dvd_self (oddPart_pos_of_pos hu2_pos).ne')
  have hodd_gt1 : 1 < oddPart (qn n) := by
    obtain ⟨p, hp, hpdvd, hp4⟩ := (lemma_3_1_i n (by omega) hn6).1
    have hp_odd : p ≠ 2 := by omega
    have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp (by decide)).mpr hp_odd
    have hdecomp : qn n = 2 ^ padicValNat 2 (qn n) * oddPart (qn n) := by
      unfold oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have hpdvd_odd : p ∣ oddPart (qn n) := by
      rw [hdecomp] at hpdvd
      exact (hcop2.pow_right _).dvd_of_dvd_mul_left hpdvd
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (oddPart_pos_of_pos (qn_pos n)) hpdvd_odd)
  have hne : oddPart (deltaMid1 n (by omega) hn6) ≠ oddPart (deltaMid2 n (by omega) hn6) := by
    intro heq
    rw [heq, Nat.gcd_self] at hgcd_1
    rw [heq, hgcd_1, mul_one] at hprod_eq
    omega
  have hmin_lt : (min (oddPart (deltaMid1 n (by omega) hn6)) (oddPart (deltaMid2 n (by omega) hn6)) : ℝ) <
      Real.sqrt (oddPart (qn n)) := by
    set d1s := oddPart (deltaMid1 n (by omega) hn6)
    set d2s := oddPart (deltaMid2 n (by omega) hn6)
    have hsq_lt : min d1s d2s * min d1s d2s < oddPart (qn n) := by
      rw [← hprod_eq]
      rcases lt_trichotomy d1s d2s with hlt | heq | hgt
      · rw [min_eq_left hlt.le]
        exact Nat.mul_lt_mul_of_pos_left hlt (oddPart_pos_of_pos coreNat_pos)
      · exact absurd heq hne
      · rw [min_eq_right hgt.le, mul_comm d1s d2s]
        exact Nat.mul_lt_mul_of_pos_left hgt (oddPart_pos_of_pos coreNat_pos)
    have hsq_ltR : ((min d1s d2s : ℝ) ^ 2) < (oddPart (qn n) : ℝ) := by
      rw [sq]; exact_mod_cast hsq_lt
    exact (Real.lt_sqrt (Nat.cast_nonneg _)).mpr hsq_ltR
  have hsqrt_le : Real.sqrt (oddPart (qn n)) ≤ Real.sqrt (qn n) :=
    Real.sqrt_le_sqrt (by exact_mod_cast oddPart_le)
  have hmin_X1 : ∀ x y : ℕ, 0 < y → x ^ 2 = qn n * y ^ 2 + 1 → X1 n (by omega) hn6 ≤ x := by
    intro x y hy hxy
    have hprop : (x : ℤ) ^ 2 - (qn n : ℤ) * (y : ℤ) ^ 2 = 1 := by
      have h1 : (x : ℤ) ^ 2 = (qn n : ℤ) * (y : ℤ) ^ 2 + 1 := by exact_mod_cast hxy
      linarith
    let b : Pell.Solution₁ (qn n : ℤ) := ⟨x, y, hprop⟩
    obtain ⟨k, hk⟩ := hfund.eq_pow_of_nonneg b (Nat.cast_nonneg x) (Nat.cast_nonneg y)
    have hk_pos : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      subst hk0'
      have hy0 : b.y = 0 := by rw [hk]; rfl
      change (y : ℤ) = 0 at hy0
      omega
    have hx_eq : (x : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).x := by
      have := congr_arg Pell.Solution₁.x hk; simpa [b, zpow_natCast] using this
    have hy_eq : (y : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).y := by
      have := congr_arg Pell.Solution₁.y hk; simpa [b, zpow_natCast] using this
    have hreal : (x : ℝ) + (y : ℝ) * Real.sqrt (qn n) = (epsReal n (by omega) hn6) ^ k := by
      have hpr := pell_pow_real_eq (by omega : 3 ≤ n) hn6 k
      rw [← hx_eq, ← hy_eq] at hpr
      exact hpr
    have h1 : (1 : ℝ) < epsReal n (by omega) hn6 := by
      unfold epsReal
      have hX1r : (1 : ℝ) < X1 n (by omega) hn6 := by exact_mod_cast hX1_gt1
      have hY1r : (0 : ℝ) ≤ Y1 n (by omega) hn6 * Real.sqrt (qn n) := by positivity
      linarith
    have hge1 : epsReal n (by omega) hn6 ≤ (epsReal n (by omega) hn6) ^ k := by
      calc epsReal n (by omega) hn6 = (epsReal n (by omega) hn6) ^ 1 := (pow_one _).symm
        _ ≤ (epsReal n (by omega) hn6) ^ k := pow_le_pow_right₀ h1.le hk_pos
    rw [← hreal, epsReal] at hge1
    by_contra hlt; push_neg at hlt
    have hlt_sq : (x : ℝ) ^ 2 < (X1 n (by omega) hn6 : ℝ) ^ 2 := by
      exact_mod_cast Nat.pow_lt_pow_left hlt (by norm_num)
    have hy_lt : (y : ℝ) < (Y1 n (by omega) hn6 : ℝ) := by
      have hqpos : (0 : ℝ) < qn n := by exact_mod_cast qn_pos n
      have hx_eq' : (x : ℝ) ^ 2 = (qn n : ℝ) * (y : ℝ) ^ 2 + 1 := by exact_mod_cast hxy
      have hX1_eq' : (X1 n (by omega) hn6 : ℝ) ^ 2 = (qn n : ℝ) * (Y1 n (by omega) hn6 : ℝ) ^ 2 + 1 := by
        exact_mod_cast hpell_eq
      have hysq' : (y : ℝ) ^ 2 < (Y1 n (by omega) hn6 : ℝ) ^ 2 := by nlinarith
      nlinarith [Nat.cast_nonneg y, Nat.cast_nonneg (Y1 n (by omega) hn6)]
    have hX1r : (x : ℝ) < (X1 n (by omega) hn6 : ℝ) := by exact_mod_cast hlt
    nlinarith [Real.sqrt_nonneg (qn n)]
  have hlag := lagrange_continued_fraction_midpoint (qn n) (X1 n (by omega) hn6) (Y1 n (by omega) hn6)
    (qn_pos n) (by
      intro ⟨s, hs⟩
      exact qn_not_isSquare (by omega) hn6 ⟨(s : ℤ), by exact_mod_cast hs⟩)
    hpell_eq hY1_pos (lemma_3_1_i n (by omega) hn6).2.1 hmin_X1
  refine ⟨hprod_eq, hgcd_1, hne, hmin_lt, hsqrt_le, ?_⟩
  rcases hlag with ⟨L, M, Qstar, a, sign, hL, hM, hQ0, hQlt, hQdvd, ha, hQeq⟩
  exact ⟨L, M, Qstar, a, sign, hL, hM, hQ0, hQlt, hQdvd, ha, by
    cases sign <;> simpa [deltaMid1, deltaMid2] using hQeq⟩

/-- Minimal midpoint character `ψ_min` on primes `p`: Kronecker symbol `(-2 δ₁^mid / p)` or `(2 δ₂^mid / p)`. -/
def psiMin (n : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6) (p : ℕ) : ℤ :=
  let d1s := oddPart (deltaMid1 n (by omega) hn6)
  let d2s := oddPart (deltaMid2 n (by omega) hn6)
  if d1s ≤ d2s then jacobiSym (-2 * (deltaMid1 n (by omega) hn6 : ℤ)) p
  else jacobiSym (2 * (deltaMid2 n (by omega) hn6 : ℤ)) p

private lemma psiMin_eq_one_or_zero {n : ℕ} (hn : 8 ≤ n) (hn6 : n ≠ 6) {p : ℕ}
    (hp : p.Prime) (hlo : n / 2 + 1 ≤ p) (hhi : p ≤ n) :
    psiMin n hn hn6 p = if p ∣ min (oddPart (deltaMid1 n (by omega) hn6)) (oddPart (deltaMid2 n (by omega) hn6))
      then 0 else 1 := by
  have hp5 : 5 ≤ p := by omega
  have hp_odd : p ≠ 2 := by omega
  have hprop := prop_5_1_i n hn hn6
  set d1s := oddPart (deltaMid1 n (by omega) hn6)
  set d2s := oddPart (deltaMid2 n (by omega) hn6)
  have hp_Podd : p ∈ Podd n := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hhi⟩, hp, ?_⟩
    rw [padicValNat_factorial_eq_one_of_half_lt hp (by omega) hhi]
    decide
  have hp_qn : p ∣ qn n := by rw [qn_eq_prod_Podd]; exact Finset.dvd_prod_of_mem _ hp_Podd
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp (by decide)).mpr hp_odd
  have hp_odd_qn : p ∣ oddPart (qn n) := by
    have hdecomp : qn n = 2 ^ padicValNat 2 (qn n) * oddPart (qn n) := by
      unfold oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    rw [hdecomp] at hp_qn
    exact (hcop2.pow_right _).dvd_of_dvd_mul_left hp_qn
  rw [← hprop.1] at hp_odd_qn
  have hfund := pellFundUnit_isFundamental (by omega : 3 ≤ n) hn6
  have hx_pos : 0 ≤ (pellFundUnit n (by omega) hn6).x := by linarith [hfund.one_lt_x]
  have hX1_gt1 : 1 < X1 n (by omega) hn6 := by
    unfold X1
    have h1 := hfund.one_lt_x
    have h2 : ((pellFundUnit n (by omega) hn6).x.natAbs : ℤ) = (pellFundUnit n (by omega) hn6).x :=
      Int.natAbs_of_nonneg hx_pos
    omega
  set u1 := X1 n (by omega) hn6 - 1
  set u2 := X1 n (by omega) hn6 + 1
  have hu1_pos : 0 < u1 := by omega
  have hu2_pos : 0 < u2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  unfold psiMin
  dsimp only
  by_cases hle : d1s ≤ d2s
  · rw [if_pos hle, min_eq_left hle]
    by_cases hpd : p ∣ d1s
    · rw [if_pos hpd]
      have hpd1 : p ∣ deltaMid1 n (by omega) hn6 := dvd_trans hpd oddPart_dvd
      have hpd_int : (p : ℤ) ∣ -2 * (deltaMid1 n (by omega) hn6 : ℤ) :=
        dvd_mul_of_dvd_right (by exact_mod_cast hpd1) _
      exact jacobiSym.eq_zero_iff.mpr ⟨by omega, by
        have : (p : ℤ).gcd (-2 * (deltaMid1 n (by omega) hn6 : ℤ)) = p := by
          rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
          exact Nat.gcd_eq_left (Int.natCast_dvd.mp hpd_int)
        omega⟩
    · rw [if_neg hpd]
      have hpd2 : p ∣ d2s := (hp.dvd_mul.mp hp_odd_qn).resolve_left hpd
      have hpu2 : p ∣ u2 := dvd_trans (dvd_trans hpd2 oddPart_dvd) (coreNat_dvd_self hu2_pos.ne')
      have hnpu1 : ¬ p ∣ u1 := by
        intro h1
        have h2 : p ∣ u2 - u1 := Nat.dvd_sub hpu2 h1
        have hsub : u2 - u1 = 2 := by dsimp only [u1, u2]; omega
        rw [hsub] at h2
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      set z1 := sqrtPartNat u1
      have hfac1 : u1 = deltaMid1 n (by omega) hn6 * z1 ^ 2 := coreNat_mul_sqrtPart_sq hu1_pos.ne'
      have hnpz1 : ¬ p ∣ z1 := fun h => hnpu1 (hfac1 ▸ dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
      have hcongr : (-2 * (deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2) % p = (2 : ℤ) ^ 2 % p := by
        have h1 : (deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2 = (u1 : ℤ) := by exact_mod_cast hfac1.symm
        have h2 : (u2 : ℤ) - (u1 : ℤ) = 2 := by dsimp only [u1, u2]; omega
        rcases (by exact_mod_cast hpu2 : (p : ℤ) ∣ (u2 : ℤ)) with ⟨t, ht⟩
        have heq : -2 * (deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2 - (2 : ℤ) ^ 2 = -2 * (p : ℤ) * t := by
          calc -2 * (deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2 - (2 : ℤ) ^ 2
              = -2 * ((deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2) - 4 := by ring
            _ = -2 * (u1 : ℤ) - 4 := by rw [h1]
            _ = -2 * (u2 : ℤ) := by linarith
            _ = -2 * (p : ℤ) * t := by rw [ht]; ring
        exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (by
          rw [heq]; exact Int.emod_eq_zero_of_dvd ⟨-2 * t, by ring⟩)
      have h2 := jacobiSym.mod_left (-2 * (deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2) p
      have h3 := jacobiSym.mod_left ((2 : ℤ) ^ 2) p
      have hjac_sq : jacobiSym (-2 * (deltaMid1 n (by omega) hn6 : ℤ) * (z1 : ℤ) ^ 2) p = 1 := by
        rw [h2, hcongr, ← h3, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr (by omega : ¬ p ∣ 2)).symm]
      rw [jacobiSym.mul_left, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr hnpz1).symm, mul_one] at hjac_sq
      exact hjac_sq
  · push_neg at hle
    rw [if_neg (not_le.mpr hle), min_eq_right hle.le]
    by_cases hpd : p ∣ d2s
    · rw [if_pos hpd]
      have hpd2 : p ∣ deltaMid2 n (by omega) hn6 := dvd_trans hpd oddPart_dvd
      have hpd_int : (p : ℤ) ∣ 2 * (deltaMid2 n (by omega) hn6 : ℤ) :=
        dvd_mul_of_dvd_right (by exact_mod_cast hpd2) _
      exact jacobiSym.eq_zero_iff.mpr ⟨by omega, by
        have : (p : ℤ).gcd (2 * (deltaMid2 n (by omega) hn6 : ℤ)) = p := by
          rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
          exact Nat.gcd_eq_left (Int.natCast_dvd.mp hpd_int)
        omega⟩
    · rw [if_neg hpd]
      have hpd1 : p ∣ d1s := (hp.dvd_mul.mp hp_odd_qn).resolve_right hpd
      have hpu1 : p ∣ u1 := dvd_trans (dvd_trans hpd1 oddPart_dvd) (coreNat_dvd_self hu1_pos.ne')
      have hnpu2 : ¬ p ∣ u2 := by
        intro h2
        have h1 : p ∣ u2 - u1 := Nat.dvd_sub h2 hpu1
        have hsub : u2 - u1 = 2 := by dsimp only [u1, u2]; omega
        rw [hsub] at h1
        have := Nat.le_of_dvd (by norm_num) h1
        omega
      set z2 := sqrtPartNat u2
      have hfac2 : u2 = deltaMid2 n (by omega) hn6 * z2 ^ 2 := coreNat_mul_sqrtPart_sq hu2_pos.ne'
      have hnpz2 : ¬ p ∣ z2 := fun h => hnpu2 (hfac2 ▸ dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
      have hcongr : (2 * (deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2) % p = (2 : ℤ) ^ 2 % p := by
        have h1 : (deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2 = (u2 : ℤ) := by exact_mod_cast hfac2.symm
        have h2 : (u2 : ℤ) - (u1 : ℤ) = 2 := by dsimp only [u1, u2]; omega
        rcases (by exact_mod_cast hpu1 : (p : ℤ) ∣ (u1 : ℤ)) with ⟨t, ht⟩
        have heq : 2 * (deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2 - (2 : ℤ) ^ 2 = 2 * (p : ℤ) * t := by
          calc 2 * (deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2 - (2 : ℤ) ^ 2
              = 2 * ((deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2) - 4 := by ring
            _ = 2 * (u2 : ℤ) - 4 := by rw [h1]
            _ = 2 * (u1 : ℤ) := by linarith
            _ = 2 * (p : ℤ) * t := by rw [ht]; ring
        exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (by
          rw [heq]; exact Int.emod_eq_zero_of_dvd ⟨2 * t, by ring⟩)
      have h2 := jacobiSym.mod_left (2 * (deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2) p
      have h3 := jacobiSym.mod_left ((2 : ℤ) ^ 2) p
      have hjac_sq : jacobiSym (2 * (deltaMid2 n (by omega) hn6 : ℤ) * (z2 : ℤ) ^ 2) p = 1 := by
        rw [h2, hcongr, ← h3, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr (by omega : ¬ p ∣ 2)).symm]
      rw [jacobiSym.mul_left, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr hnpz2).symm, mul_one] at hjac_sq
      exact hjac_sq

theorem prop_5_1_ii :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      ∀ n : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
        let d1s := oddPart (deltaMid1 n (by omega) hn6)
        let d2s := oddPart (deltaMid2 n (by omega) hn6)
        let dmin := min d1s d2s
        let Qmin := 8 * dmin
        (Qmin : ℝ) < 8 * Real.sqrt (qn n) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N_ε : ℕ, N_ε ≤ n →
          ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
            (psiMin n (by omega) hn6 p : ℝ) * Real.log p =
            Chebyshev.theta n - Chebyshev.theta ((n : ℝ) / 2) -
              ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin), Real.log p ∧
          ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
            (psiMin n (by omega) hn6 p : ℝ) * Real.log p ≥
              ((1 - Real.log 2) / 2 - ε) * (n : ℝ) := by
  refine ⟨8, le_rfl, fun n hn hn6 => ?_⟩
  dsimp only
  set d1s := oddPart (deltaMid1 n (by omega) hn6)
  set d2s := oddPart (deltaMid2 n (by omega) hn6)
  set dmin := min d1s d2s
  have h51 := prop_5_1_i n hn hn6
  have hQ_lt : ((8 * dmin : ℕ) : ℝ) < 8 * Real.sqrt (qn n) := by
    push_cast; linarith [h51.2.2.2.1, h51.2.2.2.2.1]
  refine ⟨hQ_lt, fun ε hε => ?_⟩
  have hsum_eq : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
        (psiMin n (by omega) hn6 p : ℝ) * Real.log p =
      Chebyshev.theta n - Chebyshev.theta ((n : ℝ) / 2) -
        ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin), Real.log p := by
    have hpt : ∀ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
        (psiMin n (by omega) hn6 p : ℝ) * Real.log p =
          Real.log p - (if p ∣ dmin then Real.log p else 0) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp_icc := Finset.mem_Icc.mp hp_mem.1
      rw [psiMin_eq_one_or_zero hn hn6 hp_mem.2 hp_icc.1 hp_icc.2]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.filter_filter]
    have htheta : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, Real.log p =
        Chebyshev.theta n - Chebyshev.theta ((n : ℝ) / 2) := by
      have hfl1 : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_div_eq_div]
      have hfl2 : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
      have hsub : (Finset.Ioc 0 ⌊(n : ℝ) / 2⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊(n : ℝ)⌋₊).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono (by linarith))⟩, hp.2⟩
      have hsdiff : (Finset.Ioc 0 ⌊(n : ℝ)⌋₊).filter Nat.Prime \ (Finset.Ioc 0 ⌊(n : ℝ) / 2⌋₊).filter Nat.Prime =
          (Finset.Icc (n / 2 + 1) n).filter Nat.Prime := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, hfl1, hfl2]
        constructor
        · rintro ⟨⟨⟨_, hpb⟩, hp⟩, hnot⟩
          have hpa : n / 2 < p := by by_contra hle; exact hnot ⟨⟨by omega, by omega⟩, hp⟩
          exact ⟨⟨by omega, hpb⟩, hp⟩
        · rintro ⟨⟨hpa, hpb⟩, hp⟩
          exact ⟨⟨⟨hp.pos, hpb⟩, hp⟩, fun h => by omega⟩
      unfold Chebyshev.theta
      rw [← Finset.sum_sdiff hsub, hsdiff]
      ring
    rw [htheta]
  obtain ⟨c₁, C₁, hc₁, hC₁, hpnt⟩ := deLaValleePoussin_pnt
  obtain ⟨c₂, C₂, hc₂, hC₂, hqn_err⟩ := lemma_2_1_ii.1
  have hlim_exp : ∀ (c C : ℝ), 0 < c → Tendsto (fun m : ℕ => C * Real.exp (-c * Real.sqrt (Real.log m))) atTop (𝓝 0) := by
    intro c C hc
    have hlog : Tendsto (fun m : ℕ => Real.sqrt (Real.log m)) atTop atTop :=
      tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hbot : Tendsto (fun m : ℕ => -c * Real.sqrt (Real.log m)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hlog.const_mul_atTop hc)
    simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C
  have hlim_half : Tendsto (fun m : ℕ => C₁ * Real.exp (-c₁ * Real.sqrt (Real.log ((m : ℝ) / 2)))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun m : ℕ => (m : ℝ) / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    have hlog : Tendsto (fun m : ℕ => Real.sqrt (Real.log ((m : ℝ) / 2))) atTop atTop :=
      tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hdiv)
    have hbot : Tendsto (fun m : ℕ => -c₁ * Real.sqrt (Real.log ((m : ℝ) / 2))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hlog.const_mul_atTop hc₁)
    simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C₁
  have h_ev : ∀ᶠ m : ℕ in atTop,
      8 ≤ m ∧
      C₁ * Real.exp (-c₁ * Real.sqrt (Real.log m)) +
      (1 / 2 : ℝ) * C₁ * Real.exp (-c₁ * Real.sqrt (Real.log ((m : ℝ) / 2))) +
      (1 / 2 : ℝ) * C₂ * Real.exp (-c₂ * Real.sqrt (Real.log m)) ≤ ε := by
    have hsum_lim : Tendsto (fun m : ℕ =>
        C₁ * Real.exp (-c₁ * Real.sqrt (Real.log m)) +
        (1 / 2 : ℝ) * (C₁ * Real.exp (-c₁ * Real.sqrt (Real.log ((m : ℝ) / 2)))) +
        (1 / 2 : ℝ) * (C₂ * Real.exp (-c₂ * Real.sqrt (Real.log m)))) atTop (𝓝 0) := by
      simpa using ((hlim_exp c₁ C₁ hc₁).add (hlim_half.const_mul (1 / 2))).add ((hlim_exp c₂ C₂ hc₂).const_mul (1 / 2))
    filter_upwards [eventually_ge_atTop 8, hsum_lim.eventually (ge_mem_nhds hε)] with m hm8 hm_eps
    exact ⟨hm8, by linarith⟩
  obtain ⟨N_ε, hN_ε⟩ := eventually_atTop.mp h_ev
  refine ⟨N_ε, fun hnN => ?_⟩
  refine ⟨hsum_eq, ?_⟩
  rw [hsum_eq]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h_err := (hN_ε n hnN).2
  have hpnt1 := (hpnt n (by exact_mod_cast (by omega : 2 ≤ n))).1
  have hpnt2 := (hpnt ((n : ℝ) / 2) (by
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)).1
  have hqn1 := hqn_err n (by omega)
  have hdmin_sum : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin), Real.log p ≤
      Real.log dmin := by
    set S := (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin)
    have hprod_dvd : (∏ p ∈ S, p) ∣ dmin := by
      refine Finset.prod_primes_dvd dmin (fun p hp => (Finset.mem_filter.mp hp).2.1)
        (fun p hp => (Finset.mem_filter.mp hp).2.2)
    have hdmin_pos : 0 < dmin := lt_min (oddPart_pos_of_pos coreNat_pos) (oddPart_pos_of_pos coreNat_pos)
    have hprod_le : (∏ p ∈ S, (p : ℝ)) ≤ (dmin : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hdmin_pos hprod_dvd
    have hlog_prod : ∑ p ∈ S, Real.log p = Real.log (∏ p ∈ S, (p : ℝ)) := by
      rw [Real.log_prod]
      intro p hp
      exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.1.ne_zero
    rw [hlog_prod]
    exact Real.log_le_log (Finset.prod_pos fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos) hprod_le
  have hdmin_log_lt : Real.log dmin < (1 / 2 : ℝ) * Real.log (qn n) := by
    have hdmin_pos : (0 : ℝ) < dmin := by exact_mod_cast lt_min (oddPart_pos_of_pos coreNat_pos) (oddPart_pos_of_pos coreNat_pos)
    have hlt1 : Real.log dmin < Real.log (Real.sqrt (qn n)) :=
      Real.log_lt_log hdmin_pos (lt_of_lt_of_le h51.2.2.2.1 h51.2.2.2.2.1)
    rwa [Real.sqrt_eq_rpow, Real.log_rpow (by exact_mod_cast qn_pos n), mul_comm, one_div] at hlt1
  have h1 : Chebyshev.theta n ≥ (n : ℝ) - C₁ * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log n)) := by
    linarith [(abs_le.mp hpnt1).1]
  have h2 : Chebyshev.theta ((n : ℝ) / 2) ≤ (n : ℝ) / 2 + C₁ * ((n : ℝ) / 2) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / 2))) := by
    linarith [(abs_le.mp hpnt2).2]
  have h3 : Real.log (qn n) ≤ Real.log 2 * (n : ℝ) + C₂ * (n : ℝ) * Real.exp (-c₂ * Real.sqrt (Real.log n)) := by
    linarith [(abs_le.mp hqn1).2]
  have h4 : (C₁ * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log n)) +
      C₁ * ((n : ℝ) / 2) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / 2))) +
      (1 / 2 : ℝ) * C₂ * (n : ℝ) * Real.exp (-c₂ * Real.sqrt (Real.log n))) ≤ ε * (n : ℝ) := by
    nlinarith [hn_pos]
  linarith

/-! ### 5.2 Brocard Midpoint Factorization, Exponential Bounds, and Cohomology -/

/-- Odd-core factor `B^{(1)}(n, m) := ∏_{p ∈ 𝒫_odd(n), p ∣ ((m-1)/2)*} p^{v_p(n!)}`. -/
def B1sol (n m : ℕ) : ℕ :=
  ∏ p ∈ (Podd n).filter (fun p => p ∣ oddPart ((m - 1) / 2)), p ^ padicValNat p n.factorial

/-- Odd-core factor `B^{(2)}(n, m) := ∏_{p ∈ 𝒫_odd(n), p ∣ ((m+1)/2)*} p^{v_p(n!)}`. -/
def B2sol (n m : ℕ) : ℕ :=
  ∏ p ∈ (Podd n).filter (fun p => p ∣ oddPart ((m + 1) / 2)), p ^ padicValNat p n.factorial

/-- Even-square factor `Z₁^*(n, m) := ∏_{q ∈ 𝒫_even(n), q ∣ ((m-1)/2)*} q^{v_q(n!)/2}`. -/
def Z1starSol (n m : ℕ) : ℕ :=
  ∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart ((m - 1) / 2)), q ^ (padicValNat q n.factorial / 2)

/-- Even-square factor `Z₂^*(n, m) := ∏_{q ∈ 𝒫_even(n), q ∣ ((m+1)/2)*} q^{v_q(n!)/2}`. -/
def Z2starSol (n m : ℕ) : ℕ :=
  ∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart ((m + 1) / 2)), q ^ (padicValNat q n.factorial / 2)

private lemma brocard_sol_u1_u2 {n m : ℕ} (hn : 4 ≤ n) (hsol : IsBrocardSol n m) :
    let u1 := (m - 1) / 2
    let u2 := (m + 1) / 2
    m % 2 = 1 ∧ 5 ≤ m ∧ u2 = u1 + 1 ∧ 0 < u1 ∧ 0 < u2 ∧
    u1 * u2 = n.factorial / 4 ∧ Nat.Coprime u1 u2 := by
  obtain ⟨_, hm_pos, hm_eq⟩ := hsol
  have h4_dvd : 4 ∣ n.factorial := by
    have h24 : 24 ∣ n.factorial := by
      have : Nat.factorial 4 ∣ n.factorial := Nat.factorial_dvd_factorial hn
      simpa using this
    exact dvd_trans (by norm_num : 4 ∣ 24) h24
  have hm_odd : m % 2 = 1 := by
    have h4m : m ^ 2 % 4 = 1 := by
      rcases h4_dvd with ⟨k, hk⟩
      rw [← hm_eq, hk]; omega
    rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
    · exfalso
      have : m ^ 2 % 4 = 0 := by
        have hm2 : 2 ∣ m := Nat.dvd_of_mod_eq_zero hm0
        rcases hm2 with ⟨t, ht⟩
        rw [ht]; ring_nf; omega
      omega
    · exact hm1
  have hm5 : 5 ≤ m := by
    have h24 : 24 ≤ n.factorial := by
      simpa using Nat.factorial_le hn
    nlinarith
  set u1 := (m - 1) / 2
  set u2 := (m + 1) / 2
  have hu2_eq : u2 = u1 + 1 := by omega
  have hu1_pos : 0 < u1 := by omega
  have hu2_pos : 0 < u2 := by omega
  have hprod : u1 * u2 = n.factorial / 4 := by
    have hm1 : m - 1 = 2 * u1 := by omega
    have hm2 : m + 1 = 2 * u2 := by omega
    have hmul : 4 * (u1 * u2) = n.factorial := by
      have h1 : (m - 1) * (m + 1) + 1 = m ^ 2 := by
        zify [show 1 ≤ m by omega]; ring
      rw [hm1, hm2] at h1
      linarith
    rw [← hmul, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcop : Nat.Coprime u1 u2 := by
    rw [hu2_eq]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right u1)
  exact ⟨hm_odd, hm5, hu2_eq, hu1_pos, hu2_pos, hprod, hcop⟩

private lemma brocard_B_Z_prod_eq {n m : ℕ} (hn : 4 ≤ n) (hsol : IsBrocardSol n m) :
    let u1 := (m - 1) / 2
    let u2 := (m + 1) / 2
    B1sol n m * B2sol n m = ∏ p ∈ (Podd n).filter (3 ≤ ·), p ^ padicValNat p n.factorial ∧
    Z1starSol n m ^ 2 * Z2starSol n m ^ 2 = ∏ q ∈ (Peven n).filter (3 ≤ ·), q ^ padicValNat q n.factorial ∧
    (u1 : ℝ) = (2 : ℝ) ^ padicValNat 2 u1 * (B1sol n m : ℝ) * (Z1starSol n m : ℝ) ^ 2 ∧
    (u2 : ℝ) = (2 : ℝ) ^ padicValNat 2 u2 * (B2sol n m : ℝ) * (Z2starSol n m : ℝ) ^ 2 ∧
    padicValNat 2 u1 + padicValNat 2 u2 = padicValNat 2 n.factorial - 2 := by
  obtain ⟨hm_odd, hm5, hu2_eq, hu1_pos, hu2_pos, hprod, hcop⟩ := brocard_sol_u1_u2 hn hsol
  set u1 := (m - 1) / 2
  set u2 := (m + 1) / 2
  have hfac_pos : 0 < n.factorial := Nat.factorial_pos n
  have h4_dvd : 4 ∣ n.factorial := dvd_trans (by norm_num : 4 ∣ 24) (by simpa using Nat.factorial_dvd_factorial hn)
  have hv2_ge2 : 2 ≤ padicValNat 2 n.factorial := by
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    exact (padicValNat_dvd_iff_le hfac_pos.ne').mp (by simpa using h4_dvd)
  have hv2_sum : padicValNat 2 u1 + padicValNat 2 u2 = padicValNat 2 n.factorial - 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    have h1 : padicValNat 2 (u1 * u2) = padicValNat 2 u1 + padicValNat 2 u2 :=
      padicValNat.mul hu1_pos.ne' hu2_pos.ne'
    have h2 : 4 * (u1 * u2) = n.factorial := by
      have : 4 * (n.factorial / 4) = n.factorial := Nat.mul_div_cancel' h4_dvd
      omega
    have h3 : padicValNat 2 (4 * (u1 * u2)) = 2 + padicValNat 2 (u1 * u2) := by
      rw [padicValNat.mul (by norm_num) (mul_ne_zero hu1_pos.ne' hu2_pos.ne'),
        show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.pow 2 (by norm_num),
        padicValNat.self (by norm_num)]
    rw [h2] at h3
    omega
  -- Helper: for any odd prime `p ≤ n`, `p ∣ u1` xor `p ∣ u2`, and `v_p(u_i) = v_p(n!)` when `p ∣ u_i`
  have hp_split : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ n →
      (p ∣ oddPart u1 ↔ ¬ p ∣ oddPart u2) ∧
      (p ∣ oddPart u1 → padicValNat p u1 = padicValNat p n.factorial ∧ padicValNat p u2 = 0) ∧
      (p ∣ oddPart u2 → padicValNat p u2 = padicValNat p n.factorial ∧ padicValNat p u1 = 0) := by
    intro p hp hp3 hpn
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_odd : p ≠ 2 := by omega
    have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp (by decide)).mpr hp_odd
    have hdvd_fac : p ∣ n.factorial := Nat.dvd_factorial hp.pos hpn
    have hdvd_4 : p ∣ n.factorial / 4 := by
      have h4_eq : 4 * (n.factorial / 4) = n.factorial := Nat.mul_div_cancel' h4_dvd
      rw [← h4_eq] at hdvd_fac
      exact (hcop2.pow_right 2).dvd_of_dvd_mul_left hdvd_fac
    rw [← hprod] at hdvd_4
    have h1 : ∀ u : ℕ, u ≠ 0 → (p ∣ oddPart u ↔ p ∣ u) := fun u hu => by
      constructor
      · intro h; exact dvd_trans h oddPart_dvd
      · intro h
        have hdecomp : u = 2 ^ padicValNat 2 u * oddPart u := by
          unfold oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
        rw [hdecomp] at h
        exact (hcop2.pow_right _).dvd_of_dvd_mul_left h
    rw [h1 u1 hu1_pos.ne', h1 u2 hu2_pos.ne']
    have hxor : p ∣ u1 ↔ ¬ p ∣ u2 := by
      constructor
      · intro hu1_d hu2_d
        exact hp.not_dvd_one (hcop.symm ▸ Nat.dvd_gcd hu2_d hu1_d)
      · intro hnu2
        exact (hp.dvd_mul.mp hdvd_4).resolve_right hnu2
    refine ⟨hxor, ?_, ?_⟩
    · intro hu1_d
      have hnu2 : ¬ p ∣ u2 := hxor.mp hu1_d
      have hv2 : padicValNat p u2 = 0 := padicValNat.eq_zero_of_not_dvd hnu2
      have hv4 : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega)
      have h4_eq : 4 * (u1 * u2) = n.factorial := by
        have := Nat.mul_div_cancel' h4_dvd; omega
      have hvp : padicValNat p n.factorial = padicValNat p 4 + (padicValNat p u1 + padicValNat p u2) := by
        rw [← h4_eq, padicValNat.mul (by norm_num) (mul_ne_zero hu1_pos.ne' hu2_pos.ne'),
          padicValNat.mul hu1_pos.ne' hu2_pos.ne']
      rw [hv4, hv2, zero_add, add_zero] at hvp
      exact ⟨hvp.symm, hv2⟩
    · intro hu2_d
      have hnu1 : ¬ p ∣ u1 := fun h => hxor.mp h hu2_d
      have hv1 : padicValNat p u1 = 0 := padicValNat.eq_zero_of_not_dvd hnu1
      have hv4 : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega)
      have h4_eq : 4 * (u1 * u2) = n.factorial := by
        have := Nat.mul_div_cancel' h4_dvd; omega
      have hvp : padicValNat p n.factorial = padicValNat p 4 + (padicValNat p u1 + padicValNat p u2) := by
        rw [← h4_eq, padicValNat.mul (by norm_num) (mul_ne_zero hu1_pos.ne' hu2_pos.ne'),
          padicValNat.mul hu1_pos.ne' hu2_pos.ne']
      rw [hv4, hv1, zero_add, zero_add] at hvp
      exact ⟨hvp.symm, hv1⟩
  have hB_prod : B1sol n m * B2sol n m = ∏ p ∈ (Podd n).filter (3 ≤ ·), p ^ padicValNat p n.factorial := by
    unfold B1sol B2sol
    have hdisj : Disjoint ((Podd n).filter (fun p => p ∣ oddPart u1)) ((Podd n).filter (fun p => p ∣ oddPart u2)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have hmem1 := Finset.mem_filter.mp hp1
      have hmem2 := Finset.mem_filter.mp hp2
      have hp_pr : p.Prime := (Finset.mem_filter.mp hmem1.1).2.1
      have hp3 : 3 ≤ p := by
        by_contra hlt
        have hp2 : p = 2 := by have := hp_pr.two_le; omega
        subst hp2
        exact oddPart_odd hu1_pos.ne' hmem1.2
      have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem1.1).1).2
      exact (hp_split p hp_pr hp3 hpn).1.mp hmem1.2 hmem2.2
    have hunion : (Podd n).filter (fun p => p ∣ oddPart u1) ∪ (Podd n).filter (fun p => p ∣ oddPart u2) =
        (Podd n).filter (3 ≤ ·) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hp, hd⟩ | ⟨hp, hd⟩)
        · have hp_pr := (Finset.mem_filter.mp hp).2.1
          have hp3 : 3 ≤ p := by
            by_contra hlt
            have hp2 : p = 2 := by have := hp_pr.two_le; omega
            subst hp2; exact oddPart_odd hu1_pos.ne' hd
          exact ⟨hp, hp3⟩
        · have hp_pr := (Finset.mem_filter.mp hp).2.1
          have hp3 : 3 ≤ p := by
            by_contra hlt
            have hp2 : p = 2 := by have := hp_pr.two_le; omega
            subst hp2; exact oddPart_odd hu2_pos.ne' hd
          exact ⟨hp, hp3⟩
      · rintro ⟨hp, hp3⟩
        have hp_pr := (Finset.mem_filter.mp hp).2.1
        have hpn := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        by_cases h1 : p ∣ oddPart u1
        · exact Or.inl ⟨hp, h1⟩
        · exact Or.inr ⟨hp, not_not.mp fun h2 => h1 ((hp_split p hp_pr hp3 hpn).1.mpr h2)⟩
    rw [← Finset.prod_union hdisj, hunion]
  have hZ_prod : Z1starSol n m ^ 2 * Z2starSol n m ^ 2 = ∏ q ∈ (Peven n).filter (3 ≤ ·), q ^ padicValNat q n.factorial := by
    unfold Z1starSol Z2starSol
    have hpow_eq : ∀ S : Finset ℕ, S ⊆ Peven n →
        (∏ q ∈ S, q ^ (padicValNat q n.factorial / 2)) ^ 2 = ∏ q ∈ S, q ^ padicValNat q n.factorial := by
      intro S hS
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun q hq => ?_
      have heven : 2 ∣ padicValNat q n.factorial := (Finset.mem_filter.mp (hS hq)).2.2
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow_eq _ (Finset.filter_subset _ _), hpow_eq _ (Finset.filter_subset _ _)]
    have hdisj : Disjoint ((Peven n).filter (fun p => p ∣ oddPart u1)) ((Peven n).filter (fun p => p ∣ oddPart u2)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have hmem1 := Finset.mem_filter.mp hp1
      have hmem2 := Finset.mem_filter.mp hp2
      have hp_pr : p.Prime := (Finset.mem_filter.mp hmem1.1).2.1
      have hp3 : 3 ≤ p := by
        by_contra hlt
        have hp2 : p = 2 := by have := hp_pr.two_le; omega
        subst hp2; exact oddPart_odd hu1_pos.ne' hmem1.2
      have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem1.1).1).2
      exact (hp_split p hp_pr hp3 hpn).1.mp hmem1.2 hmem2.2
    have hunion : (Peven n).filter (fun p => p ∣ oddPart u1) ∪ (Peven n).filter (fun p => p ∣ oddPart u2) =
        (Peven n).filter (3 ≤ ·) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hp, hd⟩ | ⟨hp, hd⟩)
        · have hp_pr := (Finset.mem_filter.mp hp).2.1
          have hp3 : 3 ≤ p := by
            by_contra hlt
            have hp2 : p = 2 := by have := hp_pr.two_le; omega
            subst hp2; exact oddPart_odd hu1_pos.ne' hd
          exact ⟨hp, hp3⟩
        · have hp_pr := (Finset.mem_filter.mp hp).2.1
          have hp3 : 3 ≤ p := by
            by_contra hlt
            have hp2 : p = 2 := by have := hp_pr.two_le; omega
            subst hp2; exact oddPart_odd hu2_pos.ne' hd
          exact ⟨hp, hp3⟩
      · rintro ⟨hp, hp3⟩
        have hp_pr := (Finset.mem_filter.mp hp).2.1
        have hpn := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        by_cases h1 : p ∣ oddPart u1
        · exact Or.inl ⟨hp, h1⟩
        · exact Or.inr ⟨hp, not_not.mp fun h2 => h1 ((hp_split p hp_pr hp3 hpn).1.mpr h2)⟩
    rw [← Finset.prod_union hdisj, hunion]
  have hu_fact : ∀ (u : ℕ) (hu_pos : 0 < u) (hu_dvd : u ∣ n.factorial),
      (u : ℝ) = (2 : ℝ) ^ padicValNat 2 u *
        ((∏ p ∈ (Podd n).filter (fun p => p ∣ oddPart u), p ^ padicValNat p n.factorial : ℕ) : ℝ) *
        ((∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart u), q ^ (padicValNat q n.factorial / 2) : ℕ) : ℝ) ^ 2 := by
    intro u hu_pos hu_dvd
    have hnat : u = 2 ^ padicValNat 2 u *
        ((∏ p ∈ (Podd n).filter (fun p => p ∣ oddPart u), p ^ padicValNat p n.factorial) *
         (∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart u), q ^ (padicValNat q n.factorial / 2)) ^ 2) := by
      have hdecomp : u = 2 ^ padicValNat 2 u * oddPart u := by
        unfold oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
      have hodd_pos : 0 < oddPart u := oddPart_pos_of_pos hu_pos
      have hodd_prod : oddPart u =
          (∏ p ∈ (Podd n).filter (fun p => p ∣ oddPart u), p ^ padicValNat p n.factorial) *
          (∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart u), q ^ (padicValNat q n.factorial / 2)) ^ 2 := by
        have hpow_eq : (∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart u), q ^ (padicValNat q n.factorial / 2)) ^ 2 =
            ∏ q ∈ (Peven n).filter (fun q => q ∣ oddPart u), q ^ padicValNat q n.factorial := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun q hq => ?_
          have hev : 2 ∣ padicValNat q n.factorial := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2
          rw [← pow_mul]; congr 1; omega
        rw [hpow_eq]
        have hdisj : Disjoint ((Podd n).filter (fun p => p ∣ oddPart u)) ((Peven n).filter (fun p => p ∣ oddPart u)) :=
          Finset.disjoint_filter_filter (Podd_disjoint_Peven n)
        rw [← Finset.prod_union hdisj]
        have hunion : (Podd n).filter (fun p => p ∣ oddPart u) ∪ (Peven n).filter (fun p => p ∣ oddPart u) =
            (oddPart u).primeFactors := by
          ext p
          simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_primeFactors, ne_eq, hodd_pos.ne', not_false_eq_true,
            and_true]
          constructor
          · rintro (⟨hp, hd⟩ | ⟨hp, hd⟩)
            · exact ⟨(Finset.mem_filter.mp hp).2.1, hd⟩
            · exact ⟨(Finset.mem_filter.mp hp).2.1, hd⟩
          · rintro ⟨hp, hd⟩
            have hpn : p ≤ n := by
              have hd_fac : p ∣ n.factorial := dvd_trans (dvd_trans hd oddPart_dvd) hu_dvd
              exact (hp.dvd_factorial.mp hd_fac)
            have hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpn⟩, hp⟩
            rw [← Podd_union_Peven n, Finset.mem_union] at hmem
            rcases hmem with h1 | h2
            · exact Or.inl ⟨h1, hd⟩
            · exact Or.inr ⟨h2, hd⟩
        rw [hunion]
        have hcongr : ∏ p ∈ (oddPart u).primeFactors, p ^ padicValNat p n.factorial =
            ∏ p ∈ (oddPart u).primeFactors, p ^ (oddPart u).factorization p := by
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          have hpd : p ∣ oddPart u := Nat.dvd_of_mem_primeFactors hp
          have hp_odd : p ≠ 2 := fun h => by subst h; exact oddPart_odd hu_pos.ne' hpd
          have h4_eq : 4 * (u1 * u2) = n.factorial := by have := Nat.mul_div_cancel' h4_dvd; omega
          have hvp_eq : padicValNat p (oddPart u) = padicValNat p n.factorial := by
            have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp_pr (by decide)).mpr hp_odd
            have hvp_u : padicValNat p (oddPart u) = padicValNat p u := by
              conv_rhs => rw [hdecomp]
              rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hodd_pos.ne',
                padicValNat.eq_zero_of_not_dvd (fun h => hp_odd ((Nat.prime_dvd_prime_iff_eq hp_pr (by decide)).mp (hp_pr.dvd_of_dvd_pow h))),
                zero_add]
            rw [hvp_u]
            -- Since `u` is either `u1` or `u2`:
            rcases (by omega : u = u1 ∨ u = u2) with rfl | rfl
            · exact (hp_split p hp_pr (by omega) (hp_pr.dvd_factorial.mp (dvd_trans (dvd_trans hpd oddPart_dvd) hu_dvd))).2.1 hpd |>.1
            · exact (hp_split p hp_pr (by omega) (hp_pr.dvd_factorial.mp (dvd_trans (dvd_trans hpd oddPart_dvd) hu_dvd))).2.2 hpd |>.1
          rw [← Nat.factorization_def (oddPart u) hp_pr, hvp_eq]
        rw [hcongr, Nat.prod_primeFactors_pow_factorization hodd_pos.ne']
      conv_lhs => rw [hdecomp, hodd_prod]
    exact_mod_cast (by rw [mul_assoc]; exact hnat)
  refine ⟨hB_prod, hZ_prod, ?_, ?_, hv2_sum⟩
  · have := hu_fact u1 hu1_pos ⟨u2, by rw [hprod, Nat.mul_div_cancel' h4_dvd]⟩
    simpa [B1sol, Z1starSol, mul_assoc] using this
  · have := hu_fact u2 hu2_pos ⟨u1, by rw [mul_comm, hprod, Nat.mul_div_cancel' h4_dvd]⟩
    simpa [B2sol, Z2starSol, mul_assoc] using this

theorem theorem_5_2_i :
    (∀ n m : ℕ, (hn : 4 ≤ n) → (hsol : IsBrocardSol n m) →
      (pellIndex hn hsol = 1 ∨ pellIndex hn hsol = 2) →
      let u1 := (m - 1) / 2
      let u2 := (m + 1) / 2
      let δ₁ := coreNat u1
      let δ₂ := coreNat u2
      let z₁ := sqrtPartNat u1
      let z₂ := sqrtPartNat u2
      δ₁ * δ₂ = qn n ∧ Nat.gcd δ₁ δ₂ = 1 ∧ z₁ * z₂ = sn n / 2 ∧
      (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 - (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = 1 ∧
      1 < δ₁ ∧
      (δ₂ = 1 ↔ pellIndex hn hsol = 2) ∧
      (1 < δ₂ ↔ pellIndex hn hsol = 1)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n m : ℕ, (hn : 4 ≤ n) → N₀ ≤ n → IsBrocardSol n m →
        let w1 := padicValNat 2 ((m - 1) / 2)
        let w2 := padicValNat 2 ((m + 1) / 2)
        let s2 : ℝ := if 2 ∣ padicValNat 2 n.factorial then -(padicValNat 2 n.factorial : ℝ) else (padicValNat 2 n.factorial : ℝ)
        |Real.log (B2sol n m) - Real.log ((Z1starSol n m : ℝ) ^ 2) -
          (1 / 2 : ℝ) * (DeltaParity n - ((w2 : ℝ) - w1 + s2) * Real.log 2)| ≤
            C * Real.exp (-(1 / 3 : ℝ) * n * Real.log n) ∧
        |Real.log (B1sol n m) - Real.log ((Z2starSol n m : ℝ) ^ 2) -
          (1 / 2 : ℝ) * (DeltaParity n - ((w1 : ℝ) - w2 + s2) * Real.log 2)| ≤
            C * Real.exp (-(1 / 3 : ℝ) * n * Real.log n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n m : ℕ, N₀ ≤ n → IsBrocardSol n m →
        (largestPrimeFactor (m - 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (largestPrimeFactor (m + 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (omegaNat (m - 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (omegaNat (m + 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (radNat (m - 1) : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ∧
        (radNat (m + 1) : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m hn hsol hk
    dsimp only
    obtain ⟨hm_odd, hm5, hu2_eq, hu1_pos, hu2_pos, hprod, hcop⟩ := brocard_sol_u1_u2 hn hsol
    set u1 := (m - 1) / 2
    set u2 := (m + 1) / 2
    set δ₁ := coreNat u1
    set δ₂ := coreNat u2
    set z₁ := sqrtPartNat u1
    set z₂ := sqrtPartNat u2
    have h4_dvd : 4 ∣ n.factorial := dvd_trans (by norm_num : 4 ∣ 24) (by simpa using Nat.factorial_dvd_factorial hn)
    have hfac4_pos : 0 < n.factorial / 4 := Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) h4_dvd) (by norm_num)
    have hfac4_eq : n.factorial = (n.factorial / 4) * 2 ^ 2 := by
      have := Nat.mul_div_cancel' h4_dvd; linarith
    have hδ_prod : δ₁ * δ₂ = qn n := by
      unfold qn
      rw [← coreNat_mul_of_coprime hu1_pos.ne' hu2_pos.ne' hcop, hprod]
      conv_rhs => rw [hfac4_eq]
      exact (coreNat_mul_sq hfac4_pos.ne' (by norm_num)).symm
    have hδ_gcd : Nat.gcd δ₁ δ₂ = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      exact (hcop.coprime_dvd_left (coreNat_dvd_self hu1_pos.ne')).coprime_dvd_right
        (coreNat_dvd_self hu2_pos.ne')
    have hz_prod : z₁ * z₂ = sn n / 2 := by
      unfold sn
      have h1 := sqrtPartNat_mul_of_coprime hu1_pos.ne' hu2_pos.ne' hcop
      rw [hprod] at h1
      have h2 := coreNat_mul_sqrtPart_sq (Nat.factorial_pos n).ne'
      have h3 := coreNat_mul_sqrtPart_sq hfac4_pos.ne'
      have h4 : coreNat n.factorial = coreNat (n.factorial / 4) := by
        conv_lhs => rw [hfac4_eq]
        exact coreNat_mul_sq hfac4_pos.ne' (by norm_num)
      have hsq : (sqrtPartNat n.factorial) ^ 2 = (2 * sqrtPartNat (n.factorial / 4)) ^ 2 := by
        have h5 : coreNat n.factorial * (2 * sqrtPartNat (n.factorial / 4)) ^ 2 =
            (coreNat (n.factorial / 4) * (sqrtPartNat (n.factorial / 4)) ^ 2) * 4 := by rw [h4]; ring
        rw [← h3, ← hfac4_eq] at h5
        exact Nat.eq_of_mul_eq_mul_left coreNat_pos (h2.symm.trans h5)
      have hsn_eq : sqrtPartNat n.factorial = 2 * sqrtPartNat (n.factorial / 4) :=
        (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq
      rw [← h1, hsn_eq, Nat.mul_div_cancel_left _ (by norm_num)]
    have hdiff : (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 - (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = 1 := by
      have h1 : (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = (u1 : ℤ) := by exact_mod_cast (coreNat_mul_sqrtPart_sq hu1_pos.ne').symm
      have h2 : (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 = (u2 : ℤ) := by exact_mod_cast (coreNat_mul_sqrtPart_sq hu2_pos.ne').symm
      rw [h1, h2]; exact_mod_cast (by omega : (u2 : ℤ) - (u1 : ℤ) = 1)
    have hn6 : n ≠ 6 := (pellIndex_spec hn hsol).1
    have hδ₁_gt1 : 1 < δ₁ := by
      by_contra hle
      have hδ1_eq1 : δ₁ = 1 := by have := coreNat_pos (A := u1); omega
      rw [hδ1_eq1, one_mul] at hδ_prod
      rw [hδ1_eq1, hδ_prod, one_mul] at hdiff
      have hneg : (z₁ : ℤ) ^ 2 - (qn n : ℤ) * (z₂ : ℤ) ^ 2 = -1 := by linarith
      exact (lemma_3_1_i n (by omega) hn6).2.1 z₁ z₂ hneg
    have h36 := theorem_3_6 n m hn hsol hk
    have hδ₂_eq1_iff : δ₂ = 1 ↔ pellIndex hn hsol = 2 := by
      constructor
      · intro hδ2
        by_contra hk2
        have hk1 : pellIndex hn hsol = 1 := by omega
        obtain ⟨_, _, hm_x, hsn_y⟩ := (pellIndex_spec hn hsol).2
        rw [hk1, zpow_one] at hm_x hsn_y
        have hfund := pellFundUnit_isFundamental (by omega : 3 ≤ n) hn6
        have h_u2 : u2 = z₂ ^ 2 := by
          have := coreNat_mul_sqrtPart_sq hu2_pos.ne'
          change u2 = δ₂ * z₂ ^ 2 at this
          rw [hδ2, one_mul] at this; exact this
        have h_u1 : u1 = qn n * z₁ ^ 2 := by
          have := coreNat_mul_sqrtPart_sq hu1_pos.ne'
          change u1 = δ₁ * z₁ ^ 2 at this
          rw [hδ2, mul_one] at hδ_prod
          rw [hδ_prod] at this; exact this
        have hpell_z : (z₂ : ℤ) ^ 2 - (qn n : ℤ) * (z₁ : ℤ) ^ 2 = 1 := by
          rw [hδ2, mul_one] at hδ_prod
          rw [hδ2, hδ_prod, Nat.cast_one, one_mul] at hdiff
          exact hdiff
        let b : Pell.Solution₁ (qn n : ℤ) := ⟨z₂, z₁, hpell_z⟩
        obtain ⟨r, hr⟩ := hfund.eq_pow_of_nonneg b (Nat.cast_nonneg z₂) (Nat.cast_nonneg z₁)
        have hr_pos : 1 ≤ r := by
          by_contra hr0; have hr0' : r = 0 := by omega; subst hr0'
          have hy0 : b.y = 0 := by rw [hr]; rfl
          change (z₁ : ℤ) = 0 at hy0
          have := sqrtPartNat_pos u1; omega
        have hz2_lt_m : z₂ < m := by
          have : m = 2 * u2 - 1 := by omega
          rw [h_u2] at this
          have hz2_ge2 : 2 ≤ z₂ := by nlinarith [show 5 ≤ m by exact hm5]
          nlinarith
        have hX1_le_z2 : m ≤ z₂ := by
          have hreal := pell_pow_real_eq (by omega : 3 ≤ n) hn6 r
          have hx_r : (z₂ : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (r : ℤ)).x := by
            have := congr_arg Pell.Solution₁.x hr; simpa [b, zpow_natCast] using this
          have hy_r : (z₁ : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (r : ℤ)).y := by
            have := congr_arg Pell.Solution₁.y hr; simpa [b, zpow_natCast] using this
          rw [← hx_r, ← hy_r] at hreal
          have h1 : (1 : ℝ) < epsReal n (by omega) hn6 := by
            unfold epsReal
            have : (X1 n (by omega) hn6 : ℤ) = m := by
              unfold X1; rw [← hm_x]; exact Int.natAbs_natCast m
            have : (5 : ℝ) ≤ X1 n (by omega) hn6 := by exact_mod_cast (by omega : 5 ≤ X1 n (by omega) hn6)
            have : (0 : ℝ) ≤ Y1 n (by omega) hn6 * Real.sqrt (qn n) := by positivity
            linarith
          have hpow : epsReal n (by omega) hn6 ≤ (epsReal n (by omega) hn6) ^ r := by
            calc epsReal n (by omega) hn6 = (epsReal n (by omega) hn6) ^ 1 := (pow_one _).symm
              _ ≤ (epsReal n (by omega) hn6) ^ r := pow_le_pow_right₀ h1.le hr_pos
          rw [← hreal] at hpow
          have hX1m : X1 n (by omega) hn6 = m := by
            unfold X1; rw [← hm_x]; exact Int.natAbs_natCast m
          have hY1s : Y1 n (by omega) hn6 = sn n := by
            unfold Y1; rw [← hsn_y]; exact Int.natAbs_natCast (sn n)
          by_contra hlt; push_neg at hlt
          have hz2_lt_X1 : z₂ < X1 n (by omega) hn6 := by omega
          have hz1_lt_Y1 : (z₁ : ℝ) < Y1 n (by omega) hn6 := by
            have hqpos : (0 : ℝ) < qn n := by exact_mod_cast qn_pos n
            have h1' : (z₂ : ℝ) ^ 2 = (qn n : ℝ) * (z₁ : ℝ) ^ 2 + 1 := by exact_mod_cast (by linarith : z₂ ^ 2 = qn n * z₁ ^ 2 + 1)
            have h2' : (m : ℝ) ^ 2 = (qn n : ℝ) * (sn n : ℝ) ^ 2 + 1 := by
              have := hsol.2.2; have := factorial_eq_qn_mul_sn_sq n; exact_mod_cast (by linarith : m ^ 2 = qn n * sn n ^ 2 + 1)
            have hlt_sq : (z₂ : ℝ) ^ 2 < (m : ℝ) ^ 2 := by exact_mod_cast Nat.pow_lt_pow_left hlt (by norm_num)
            have hysq : (z₁ : ℝ) ^ 2 < (sn n : ℝ) ^ 2 := by nlinarith
            rw [hY1s]; nlinarith [Nat.cast_nonneg z₁, Nat.cast_nonneg (sn n)]
          unfold epsReal at hpow
          have h1' : (z₂ : ℝ) < X1 n (by omega) hn6 := by exact_mod_cast hz2_lt_X1
          nlinarith [Real.sqrt_nonneg (qn n)]
        omega
      · intro hk2
        obtain ⟨u, v, hm_uv, _⟩ := h36.2.1.mp hk2
        have hu2_sq : u2 = u.natAbs ^ 2 := by
          have h1 : (2 * u2 : ℤ) = (m + 1 : ℤ) := by exact_mod_cast (by omega : 2 * u2 = m + 1)
          have h2 : (m + 1 : ℤ) = 2 * u ^ 2 := by linarith
          have h3 : (u2 : ℤ) = u ^ 2 := by linarith
          have h4 : (u2 : ℤ) = (u.natAbs : ℤ) ^ 2 := by rw [h3, sq_abs]
          exact_mod_cast h4
        rw [show δ₂ = coreNat u2 from rfl, hu2_sq, ← one_mul (u.natAbs ^ 2),
          coreNat_mul_sq (by norm_num) (by
            intro h0; rw [h0, zero_pow (by norm_num)] at hu2_sq; omega)]
        simp [coreNat]
    have hδ₂_gt1_iff : 1 < δ₂ ↔ pellIndex hn hsol = 1 := by
      have hpos := coreNat_pos (A := u2)
      constructor
      · intro hgt
        rcases hk with hk1 | hk2
        · exact hk1
        · exfalso; have := hδ₂_eq1_iff.mpr hk2; omega
      · intro hk1
        by_contra hle
        have h1 : δ₂ = 1 := by omega
        have := hδ₂_eq1_iff.mp h1
        omega
    exact ⟨hδ_prod, hδ_gcd, hz_prod, hdiff, hδ₁_gt1, hδ₂_eq1_iff, hδ₂_gt1_iff⟩
  · -- Conjunct 2: Exponential error bound
    have hfac_lb : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
      intro n hn1
      have hpow_le : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ k ≤ (3 : ℝ) ^ k * (k.factorial : ℝ) := by
        intro k hk1
        induction k with
        | zero => omega
        | succ k ih =>
          rcases eq_or_lt_of_le hk1 with h1 | hgt
          · injection h1 with hk0; subst hk0; norm_num
          · have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
            have ih' := ih (by omega)
            have h1k : (1 + 1 / (k : ℝ)) ^ k ≤ 3 := by
              calc (1 + 1 / (k : ℝ)) ^ k ≤ Real.exp (k * (1 / (k : ℝ))) := by
                    have hle := Real.add_one_le_exp (1 / (k : ℝ))
                    rw [add_comm] at hle
                    calc (1 + 1 / (k : ℝ)) ^ k ≤ (Real.exp (1 / (k : ℝ))) ^ k :=
                          pow_le_pow_left₀ (by positivity) hle k
                      _ = Real.exp (k * (1 / (k : ℝ))) := by rw [← Real.exp_nat_mul]
                _ = Real.exp 1 := by rw [mul_one_div_cancel hk_pos.ne']
                _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
            have hkp : ((k + 1 : ℕ) : ℝ) ^ (k + 1) = ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k * (1 + 1 / (k : ℝ)) ^ k := by
              rw [pow_succ']
              have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) * (1 + 1 / (k : ℝ)) := by
                push_cast; field_simp [hk_pos.ne']; ring
              rw [this, mul_pow]; ring
            rw [hkp, Nat.factorial_succ, Nat.cast_mul, pow_succ']
            calc ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k * (1 + 1 / (k : ℝ)) ^ k
                ≤ ((k + 1 : ℕ) : ℝ) * ((3 : ℝ) ^ k * (k.factorial : ℝ)) * 3 := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left ih' (by positivity)) h1k (by positivity) (by positivity)
              _ = 3 * (3 : ℝ) ^ k * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) := by ring
      have h := hpow_le n hn1
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith
    refine ⟨2, by norm_num, 27, by norm_num, fun n m hn hn27 hsol => ?_⟩
    obtain ⟨hm_odd, hm5, hu2_eq, hu1_pos, hu2_pos, hprod, hcop⟩ := brocard_sol_u1_u2 hn hsol
    obtain ⟨hB_prod, hZ_prod, hu1_eq, hu2_eqR, hv2_sum⟩ := brocard_B_Z_prod_eq hn hsol
    set u1 := (m - 1) / 2
    set u2 := (m + 1) / 2
    set w1 := padicValNat 2 u1
    set w2 := padicValNat 2 u2
    have hn1 : 1 ≤ n := by omega
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hfac_ge : Real.exp ((2 / 3 : ℝ) * n * Real.log n) ≤ (n.factorial : ℝ) := by
      have h1 := hfac_lb n hn1
      have h27 : (27 : ℝ) ≤ n := by exact_mod_cast hn27
      have hlog27 : Real.log 27 ≤ Real.log n := Real.log_le_log (by norm_num) h27
      have hlog3 : Real.log 3 ≤ (1 / 3 : ℝ) * Real.log n := by
        have h27eq : Real.log 27 = 3 * Real.log 3 := by
          rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
        linarith
      have hlog_div : (2 / 3 : ℝ) * Real.log n ≤ Real.log ((n : ℝ) / 3) := by
        rw [Real.log_div hn_pos.ne' (by norm_num)]; linarith
      have h_exp : Real.exp ((2 / 3 : ℝ) * n * Real.log n) ≤ ((n : ℝ) / 3) ^ n := by
        rw [← Real.log_le_log_iff (Real.exp_pos _) (pow_pos (div_pos hn_pos (by norm_num)) _),
          Real.log_exp, Real.log_pow]
        nlinarith [Nat.cast_nonneg n]
      exact le_trans h_exp h1
    have hu1_ge : (1 / 4 : ℝ) * Real.exp ((1 / 3 : ℝ) * n * Real.log n) ≤ (u1 : ℝ) := by
      have hsq : (n.factorial : ℝ) ≤ 4 * ((u1 : ℝ) + 1) ^ 2 := by
        have h4 : 4 * (u1 * u2) ≤ n.factorial := by
          rw [hprod]; exact Nat.mul_div_le n.factorial 4
        have h4' : n.factorial ≤ 4 * ((u1 + 1) ^ 2) := by
          have h4_dvd : 4 ∣ n.factorial := dvd_trans (by norm_num : 4 ∣ 24) (by simpa using Nat.factorial_dvd_factorial hn)
          have := Nat.mul_div_cancel' h4_dvd
          rw [← hprod] at this
          nlinarith [hu2_eq]
        exact_mod_cast h4'
      have hexp_sq : Real.exp ((2 / 3 : ℝ) * n * Real.log n) = (Real.exp ((1 / 3 : ℝ) * n * Real.log n)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have h1 : Real.exp ((1 / 3 : ℝ) * n * Real.log n) ≤ 2 * ((u1 : ℝ) + 1) := by
        have hle : (Real.exp ((1 / 3 : ℝ) * n * Real.log n)) ^ 2 ≤ (2 * ((u1 : ℝ) + 1)) ^ 2 := by
          rw [← hexp_sq]; linarith
        nlinarith [Real.exp_pos ((1 / 3 : ℝ) * n * Real.log n), Nat.cast_nonneg u1]
      have hexp_ge2 : 2 ≤ Real.exp ((1 / 3 : ℝ) * n * Real.log n) := by
        have : 1 ≤ (1 / 3 : ℝ) * n * Real.log n := by
          have hlog3 : 1 ≤ Real.log n := by
            have : Real.exp 1 ≤ (n : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9]) (by exact_mod_cast (by omega : 3 ≤ n))
            simpa using Real.log_le_log (Real.exp_pos 1) this
          have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
          nlinarith
        linarith [Real.add_one_le_exp ((1 / 3 : ℝ) * n * Real.log n)]
      linarith
    have hlog_u_diff : 0 ≤ Real.log (u2 : ℝ) - Real.log (u1 : ℝ) ∧
        Real.log (u2 : ℝ) - Real.log (u1 : ℝ) ≤ 4 * Real.exp (-(1 / 3 : ℝ) * n * Real.log n) := by
      have hu1_posR : (0 : ℝ) < u1 := by exact_mod_cast hu1_pos
      have hu2_posR : (0 : ℝ) < u2 := by exact_mod_cast hu2_pos
      have hu2_cast : (u2 : ℝ) = (u1 : ℝ) + 1 := by exact_mod_cast hu2_eq
      rw [← Real.log_div hu2_posR.ne' hu1_posR.ne', hu2_cast, add_div, div_self hu1_posR.ne']
      have hnn : 0 ≤ Real.log (1 + 1 / (u1 : ℝ)) := Real.log_nonneg (by linarith [div_pos one_pos hu1_posR])
      have hle : Real.log (1 + 1 / (u1 : ℝ)) ≤ 1 / (u1 : ℝ) := by
        have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (u1 : ℝ))
        linarith
      have hinv : 1 / (u1 : ℝ) ≤ 4 * Real.exp (-(1 / 3 : ℝ) * n * Real.log n) := by
        rw [div_le_iff₀ hu1_posR]
        calc (1 : ℝ) = 4 * Real.exp (-(1 / 3 : ℝ) * n * Real.log n) * ((1 / 4 : ℝ) * Real.exp ((1 / 3 : ℝ) * n * Real.log n)) := by
              rw [show -(1 / 3 : ℝ) * n * Real.log n = -((1 / 3 : ℝ) * n * Real.log n) by ring,
                Real.exp_neg]; field_simp
          _ ≤ 4 * Real.exp (-(1 / 3 : ℝ) * n * Real.log n) * (u1 : ℝ) :=
              mul_le_mul_of_nonneg_left hu1_ge (by positivity)
      exact ⟨hnn, le_trans hle hinv⟩
    -- Exact algebraic relation between `log u2 - log u1`, `B1sol`, `B2sol`, `Z1starSol`, `Z2starSol`, and `DeltaParity n`:
    have hB1_pos : 0 < B1sol n m := Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _
    have hB2_pos : 0 < B2sol n m := Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _
    have hZ1_pos : 0 < Z1starSol n m := Finset.prod_pos fun q hq => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos _
    have hZ2_pos : 0 < Z2starSol n m := Finset.prod_pos fun q hq => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos _
    have hSodd_eq : Sodd n = Real.log (B1sol n m) + Real.log (B2sol n m) +
        (if ¬ 2 ∣ padicValNat 2 n.factorial then (padicValNat 2 n.factorial : ℝ) * Real.log 2 else 0) := by
      have hlog_B : Real.log (B1sol n m) + Real.log (B2sol n m) =
          ∑ p ∈ (Podd n).filter (3 ≤ ·), (padicValNat p n.factorial : ℝ) * Real.log p := by
        rw [← Real.log_mul (by exact_mod_cast hB1_pos.ne') (by exact_mod_cast hB2_pos.ne'),
          ← Nat.cast_mul, hB_prod, Nat.cast_prod, Real.log_prod]
        · refine Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
        · intro p hp; exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.ne_zero)
      rw [hlog_B]; unfold Sodd
      by_cases h2 : 2 ∈ Podd n
      · have hodd2 : ¬ 2 ∣ padicValNat 2 n.factorial := (Finset.mem_filter.mp h2).2.2
        rw [if_pos hodd2, ← Finset.add_sum_erase _ _ h2]
        have herase : (Podd n).erase 2 = (Podd n).filter (3 ≤ ·) := by
          ext p; simp only [Finset.mem_erase, Finset.mem_filter]
          constructor
          · rintro ⟨hp2, hp⟩; exact ⟨hp, by have := (Finset.mem_filter.mp hp).2.1.two_le; omega⟩
          · rintro ⟨hp, hp3⟩; exact ⟨by omega, hp⟩
        rw [herase]; ring
      · have hev2 : 2 ∣ padicValNat 2 n.factorial := by
          by_contra hodd
          exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by decide, hodd⟩)
        rw [if_neg (not_not.mpr hev2), add_zero]
        have hflt : (Podd n).filter (3 ≤ ·) = Podd n := by
          ext p; simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.1
          · intro hp; have hne2 : p ≠ 2 := fun h => h2 (h ▸ hp)
            exact ⟨hp, by have := (Finset.mem_filter.mp hp).2.1.two_le; omega⟩
        rw [hflt]
    have hSeven_eq : Seven n = Real.log ((Z1starSol n m : ℝ) ^ 2) + Real.log ((Z2starSol n m : ℝ) ^ 2) +
        (if 2 ∣ padicValNat 2 n.factorial then (padicValNat 2 n.factorial : ℝ) * Real.log 2 else 0) := by
      have hlog_Z : Real.log ((Z1starSol n m : ℝ) ^ 2) + Real.log ((Z2starSol n m : ℝ) ^ 2) =
          ∑ q ∈ (Peven n).filter (3 ≤ ·), (padicValNat q n.factorial : ℝ) * Real.log q := by
        rw [← Real.log_mul (pow_ne_zero 2 (by exact_mod_cast hZ1_pos.ne')) (pow_ne_zero 2 (by exact_mod_cast hZ2_pos.ne')),
          ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, hZ_prod, Nat.cast_prod, Real.log_prod]
        · refine Finset.sum_congr rfl fun q _ => by rw [Nat.cast_pow, Real.log_pow]
        · intro q hq; exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.ne_zero)
      rw [hlog_Z]; unfold Seven
      by_cases h2 : 2 ∈ Peven n
      · have hev2 : 2 ∣ padicValNat 2 n.factorial := (Finset.mem_filter.mp h2).2.2
        rw [if_pos hev2, ← Finset.add_sum_erase _ _ h2]
        have herase : (Peven n).erase 2 = (Peven n).filter (3 ≤ ·) := by
          ext p; simp only [Finset.mem_erase, Finset.mem_filter]
          constructor
          · rintro ⟨hp2, hp⟩; exact ⟨hp, by have := (Finset.mem_filter.mp hp).2.1.two_le; omega⟩
          · rintro ⟨hp, hp3⟩; exact ⟨by omega, hp⟩
        rw [herase]; ring
      · have hodd2 : ¬ 2 ∣ padicValNat 2 n.factorial := by
          intro hev
          exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by decide, hev⟩)
        rw [if_neg hodd2, add_zero]
        have hflt : (Peven n).filter (3 ≤ ·) = Peven n := by
          ext p; simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.1
          · intro hp; have hne2 : p ≠ 2 := fun h => h2 (h ▸ hp)
            exact ⟨hp, by have := (Finset.mem_filter.mp hp).2.1.two_le; omega⟩
        rw [hflt]
    have hlog_u1 : Real.log (u1 : ℝ) = (w1 : ℝ) * Real.log 2 + Real.log (B1sol n m) + Real.log ((Z1starSol n m : ℝ) ^ 2) := by
      rw [hu1_eq, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlog_u2 : Real.log (u2 : ℝ) = (w2 : ℝ) * Real.log 2 + Real.log (B2sol n m) + Real.log ((Z2starSol n m : ℝ) ^ 2) := by
      rw [hu2_eqR, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hDelta_eq : DeltaParity n = Sodd n - Seven n := rfl
    have hid1 : Real.log (B2sol n m) - Real.log ((Z1starSol n m : ℝ) ^ 2) -
        (1 / 2 : ℝ) * (DeltaParity n - ((w2 : ℝ) - w1 +
          (if 2 ∣ padicValNat 2 n.factorial then -(padicValNat 2 n.factorial : ℝ) else (padicValNat 2 n.factorial : ℝ))) * Real.log 2) =
        (1 / 2 : ℝ) * (Real.log (u2 : ℝ) - Real.log (u1 : ℝ)) := by
      rw [hDelta_eq, hSodd_eq, hSeven_eq, hlog_u1, hlog_u2]
      split_ifs <;> ring
    have hid2 : Real.log (B1sol n m) - Real.log ((Z2starSol n m : ℝ) ^ 2) -
        (1 / 2 : ℝ) * (DeltaParity n - ((w1 : ℝ) - w2 +
          (if 2 ∣ padicValNat 2 n.factorial then -(padicValNat 2 n.factorial : ℝ) else (padicValNat 2 n.factorial : ℝ))) * Real.log 2) =
        -(1 / 2 : ℝ) * (Real.log (u2 : ℝ) - Real.log (u1 : ℝ)) := by
      rw [hDelta_eq, hSodd_eq, hSeven_eq, hlog_u1, hlog_u2]
      split_ifs <;> ring
    rw [hid1, hid2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_mul, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hlog_u_diff.1]
    constructor <;> linarith [hlog_u_diff.2]
  · -- Conjunct 3: `largestPrimeFactor`, `omegaNat`, `radNat` bounds
    intro ε hε
    obtain ⟨C_mert, _, hmert_lim, _⟩ := mertens_first_theorem
    have hfac_lb : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
      intro n hn1
      have hpow_le : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ k ≤ (3 : ℝ) ^ k * (k.factorial : ℝ) := by
        intro k hk1
        induction k with
        | zero => omega
        | succ k ih =>
          rcases eq_or_lt_of_le hk1 with h1 | hgt
          · injection h1 with hk0; subst hk0; norm_num
          · have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
            have ih' := ih (by omega)
            have h1k : (1 + 1 / (k : ℝ)) ^ k ≤ 3 := by
              calc (1 + 1 / (k : ℝ)) ^ k ≤ Real.exp (k * (1 / (k : ℝ))) := by
                    have hle := Real.add_one_le_exp (1 / (k : ℝ))
                    rw [add_comm] at hle
                    calc (1 + 1 / (k : ℝ)) ^ k ≤ (Real.exp (1 / (k : ℝ))) ^ k :=
                          pow_le_pow_left₀ (by positivity) hle k
                      _ = Real.exp (k * (1 / (k : ℝ))) := by rw [← Real.exp_nat_mul]
                _ = Real.exp 1 := by rw [mul_one_div_cancel hk_pos.ne']
                _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
            have hkp : ((k + 1 : ℕ) : ℝ) ^ (k + 1) = ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k * (1 + 1 / (k : ℝ)) ^ k := by
              rw [pow_succ']
              have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) * (1 + 1 / (k : ℝ)) := by
                push_cast; field_simp [hk_pos.ne']; ring
              rw [this, mul_pow]; ring
            rw [hkp, Nat.factorial_succ, Nat.cast_mul, pow_succ']
            calc ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k * (1 + 1 / (k : ℝ)) ^ k
                ≤ ((k + 1 : ℕ) : ℝ) * ((3 : ℝ) ^ k * (k.factorial : ℝ)) * 3 := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left ih' (by positivity)) h1k (by positivity) (by positivity)
              _ = 3 * (3 : ℝ) ^ k * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) := by ring
      have h := hpow_le n hn1
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith
    set ε' := min ε (1 / 4 : ℝ)
    have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
    have hε'_le : ε' ≤ 1 / 4 := min_le_right _ _
    have h_ev : ∀ᶠ n : ℕ in atTop,
        8 ≤ n ∧
        (3 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε' / 2) ∧
        (∑ p ∈ (Finset.Icc 3 ⌊(n : ℝ) ^ (1 / 2 - ε' / 2)⌋₊).filter Nat.Prime,
          Real.log p / ((p : ℝ) - 1)) ≤
          Real.log ((n : ℝ) ^ (1 / 2 - ε' / 2)) + |Real.eulerMascheroniConstant| + Real.log 2 + 2 ∧
        (1 / 4 : ℝ) * (n : ℝ) * Real.log n ≤
          (1 / 2 : ℝ) * ((n : ℝ) * (Real.log n - Real.log 3)) - Real.log 4 ∧
        (n : ℝ) * (Real.log ((n : ℝ) ^ (1 / 2 - ε' / 2)) + (|Real.eulerMascheroniConstant| + Real.log 2 + 2) + Real.log 2 + 2) +
          2 * (n : ℝ) ^ (1 - ε' / 2) * Real.log n <
          (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ∧
        (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ≤
          (1 / 2 : ℝ) * ((n : ℝ) * (Real.log n - Real.log 3)) - Real.log 4 := by
      have h1 : ∀ᶠ n : ℕ in atTop, 8 ≤ n := eventually_ge_atTop 8
      have hr_pos : 0 < 1 / 2 - ε' / 2 := by linarith
      have h_pow_atTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 - ε' / 2)) atTop atTop :=
        (tendsto_rpow_atTop hr_pos).comp tendsto_natCast_atTop_atTop
      have h_ge3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε' / 2) :=
        h_pow_atTop.eventually_ge_atTop 3
      have h_mert_ev : ∀ᶠ n : ℕ in atTop,
          (∑ p ∈ (Finset.Icc 3 ⌊(n : ℝ) ^ (1 / 2 - ε' / 2)⌋₊).filter Nat.Prime,
            Real.log p / ((p : ℝ) - 1)) ≤
            Real.log ((n : ℝ) ^ (1 / 2 - ε' / 2)) + |Real.eulerMascheroniConstant| + Real.log 2 + 2 := by
        have hcomp := hmert_lim.comp h_pow_atTop
        filter_upwards [hcomp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
        have h1' : (∑ p ∈ (Finset.Icc 3 ⌊(n : ℝ) ^ (1 / 2 - ε' / 2)⌋₊).filter Nat.Prime,
              Real.log p / ((p : ℝ) - 1)) -
            (Real.log ((n : ℝ) ^ (1 / 2 - ε' / 2)) - Real.eulerMascheroniConstant - Real.log 2) ≤ 1 := by
          rw [Real.dist_eq, sub_zero] at hn
          linarith [(abs_lt.mp hn).2]
        linarith [neg_le_abs Real.eulerMascheroniConstant]
      have h_log3 : ∀ᶠ n : ℕ in atTop,
          (1 / 2 : ℝ) * ((n : ℝ) * (Real.log n - Real.log 3)) - Real.log 4 ≥
            (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n := by
        have hlim : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) * Real.log 3 + Real.log 4 / (n : ℝ)) / Real.log n) atTop (𝓝 0) := by
          have hnum : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * Real.log 3 + Real.log 4 / (n : ℝ)) atTop (𝓝 ((1 / 2 : ℝ) * Real.log 3)) := by
            simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
          exact hnum.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        filter_upwards [eventually_ge_atTop 2, hlim.eventually (ge_mem_nhds (by positivity : 0 < ε' / 3))] with n hn2 hn_lim
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have hdiv : ((1 / 2 : ℝ) * Real.log 3 + Real.log 4 / (n : ℝ)) / Real.log n ≤ ε' / 3 := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hn_lim
          exact hn_lim.le
        have hmul : (1 / 2 : ℝ) * Real.log 3 + Real.log 4 / (n : ℝ) ≤ (ε' / 3) * Real.log n :=
          (div_le_iff₀ hlog_pos).mp hdiv
        have hmul2 : (1 / 2 : ℝ) * (n : ℝ) * Real.log 3 + Real.log 4 ≤ (ε' / 3) * (n : ℝ) * Real.log n := by
          have := mul_le_mul_of_nonneg_left hmul hn_pos.le
          have heq : (n : ℝ) * ((1 / 2 : ℝ) * Real.log 3 + Real.log 4 / (n : ℝ)) =
              (1 / 2 : ℝ) * (n : ℝ) * Real.log 3 + Real.log 4 := by
            field_simp [hn_pos.ne']
          linarith
        linarith
      have h_mert_dom : ∀ᶠ n : ℕ in atTop,
          (n : ℝ) * (Real.log ((n : ℝ) ^ (1 / 2 - ε' / 2)) + (|Real.eulerMascheroniConstant| + Real.log 2 + 2) + Real.log 2 + 2) +
            2 * (n : ℝ) ^ (1 - ε' / 2) * Real.log n <
            (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n := by
        set K : ℝ := (|Real.eulerMascheroniConstant| + Real.log 2 + 2) + Real.log 2 + 2
        have hlim1 : Tendsto (fun n : ℕ => K / Real.log n) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        have hlim2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) ^ (-(ε' / 2)))) atTop (𝓝 0) := by
          have hr : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(ε' / 2))) atTop (𝓝 0) := by
            simpa using (tendsto_rpow_neg_atTop (by positivity : 0 < ε' / 2)).comp tendsto_natCast_atTop_atTop
          simpa using hr.const_mul 2
        have hlim : Tendsto (fun n : ℕ => K / Real.log n + 2 * (n : ℝ) ^ (-(ε' / 2))) atTop (𝓝 0) := by
          simpa using hlim1.add hlim2
        filter_upwards [eventually_ge_atTop 2, hlim.eventually (gt_mem_nhds (by positivity : 0 < ε' / 6))] with n hn2 hlt
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have h_pow : (n : ℝ) ^ (1 - ε' / 2) = (n : ℝ) * (n : ℝ) ^ (-(ε' / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hn_pos, Real.rpow_one]
        have h_logr : Real.log ((n : ℝ) ^ (1 / 2 - ε' / 2)) = (1 / 2 - ε' / 2) * Real.log n :=
          Real.log_rpow hn_pos _
        have hlt' : K / Real.log n + 2 * (n : ℝ) ^ (-(ε' / 2)) < ε' / 6 := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
          exact hlt
        have hmul : K + 2 * (n : ℝ) ^ (-(ε' / 2)) * Real.log n < (ε' / 6) * Real.log n := by
          have := mul_lt_mul_of_pos_right hlt' hlog_pos
          field_simp [hlog_pos.ne'] at this ⊢
          linarith
        have hmul2 := mul_lt_mul_of_pos_left hmul hn_pos
        rw [h_logr, h_pow]
        nlinarith
      filter_upwards [h1, h_ge3, h_mert_ev, h_log3, h_mert_dom] with n hn8 hg3 hmert_n h3 hm
      refine ⟨hn8, hg3, hmert_n, ?_, hm, h3⟩
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) * Real.log n by positivity]
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
    refine ⟨max N₀ 4, le_max_right _ _, fun n m hnN hsol => ?_⟩
    have hn_ge : N₀ ≤ n := le_trans (le_max_left _ _) hnN
    have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hnN
    obtain ⟨hn8, h_ge3, h_mert_n, _, hm_dom, h_fac_dom⟩ := hN₀ n hn_ge
    obtain ⟨_, hm5, hu2_eq, hu1_pos, hu2_pos, hprod, _⟩ := brocard_sol_u1_u2 hn4 hsol
    set u1 := (m - 1) / 2
    set u2 := (m + 1) / 2
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_u1_lb : (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ≤ Real.log (u1 : ℝ) := by
      have hfac := hfac_lb n (by omega)
      have hsq : (n.factorial : ℝ) ≤ 4 * (u1 : ℝ) * ((u1 : ℝ) + 1) := by
        have h4_dvd : 4 ∣ n.factorial := dvd_trans (by norm_num : 4 ∣ 24) (by simpa using Nat.factorial_dvd_factorial hn4)
        have h4' := Nat.mul_div_cancel' h4_dvd
        rw [← hprod] at h4'
        exact_mod_cast (by nlinarith [hu2_eq] : n.factorial ≤ 4 * u1 * (u1 + 1))
      have hsq2 : (n.factorial : ℝ) ≤ 8 * (u1 : ℝ) ^ 2 := by
        have hu1_1 : (1 : ℝ) ≤ u1 := by exact_mod_cast hu1_pos
        nlinarith
      have hlog_fac : (n : ℝ) * (Real.log n - Real.log 3) ≤ Real.log (n.factorial : ℝ) := by
        have h1 : Real.log (((n : ℝ) / 3) ^ n) ≤ Real.log (n.factorial : ℝ) :=
          Real.log_le_log (pow_pos (div_pos hn_pos (by norm_num)) _) hfac
        rw [Real.log_pow, Real.log_div hn_pos.ne' (by norm_num)] at h1
        exact h1
      have hlog_8u : Real.log (n.factorial : ℝ) ≤ Real.log 8 + 2 * Real.log (u1 : ℝ) := by
        have h1 : Real.log (n.factorial : ℝ) ≤ Real.log (8 * (u1 : ℝ) ^ 2) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) hsq2
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (by exact_mod_cast hu1_pos.ne')), Real.log_pow] at h1
        exact h1
      have hlog8_le : Real.log 8 ≤ 2 * Real.log 4 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      linarith
    have hlog_u2_lb : (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ≤ Real.log (u2 : ℝ) := by
      have hle : Real.log (u1 : ℝ) ≤ Real.log (u2 : ℝ) :=
        Real.log_le_log (by exact_mod_cast hu1_pos) (by exact_mod_cast (by omega : u1 ≤ u2))
      linarith
    have hvp_fac_le : ∀ p : ℕ, p.Prime → (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hleg := sub_one_mul_padicValNat_factorial (p := p) n
      have hlegR : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) =
          ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), ((n / p ^ i : ℕ) : ℝ) := by
        have h1 : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) =
            ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), ((n / p ^ i : ℕ) : ℝ) := by exact_mod_cast hleg
        rwa [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h1
      have hgeom : ∀ L : ℕ, ∑ i ∈ Finset.Ico 1 (L + 1), (1 / (p : ℝ)) ^ i ≤
          1 / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ L) := by
        intro L
        induction L with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
          have hstep : 1 / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ k) + (1 / (p : ℝ)) ^ (k + 1) =
              1 / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ (k + 1)) -
                ((p : ℝ) - 2) / ((p : ℝ) - 1) * (1 / (p : ℝ)) ^ (k + 1) := by
            rw [pow_succ']
            field_simp [hp1_pos.ne', (by linarith : (p : ℝ) ≠ 0)]
            ring
          have hnn : 0 ≤ ((p : ℝ) - 2) / ((p : ℝ) - 1) * (1 / (p : ℝ)) ^ (k + 1) := by
            refine mul_nonneg (div_nonneg (by linarith) hp1_pos.le) (by positivity)
          linarith
      have hsum_le : ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), ((n / p ^ i : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
        have hpt : ∀ i ∈ Finset.Ico 1 (Nat.log p n + 1), ((n / p ^ i : ℕ) : ℝ) ≤ (n : ℝ) * (1 / (p : ℝ)) ^ i := by
          intro i _
          rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (by positivity) i)]
          exact_mod_cast Nat.div_mul_le_self n (p ^ i)
        refine le_trans (Finset.sum_le_sum hpt) ?_
        rw [← Finset.mul_sum]
        have h1 := hgeom (Nat.log p n)
        have h2 : 1 - (1 / (p : ℝ)) ^ Nat.log p n ≤ 1 := by linarith [show (0 : ℝ) ≤ (1 / (p : ℝ)) ^ Nat.log p n by positivity]
        have h3 : 1 / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ Nat.log p n) ≤ 1 / ((p : ℝ) - 1) :=
          mul_le_of_le_one_right (by positivity) h2
        calc (n : ℝ) * ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), (1 / (p : ℝ)) ^ i
            ≤ (n : ℝ) * (1 / ((p : ℝ) - 1)) := mul_le_mul_of_nonneg_left (le_trans h1 h3) (Nat.cast_nonneg n)
          _ = (n : ℝ) / ((p : ℝ) - 1) := by ring
      have h1le : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      calc (padicValNat p n.factorial : ℝ) ≤ ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) :=
            le_mul_of_one_le_left (Nat.cast_nonneg _) h1le
        _ ≤ (n : ℝ) / ((p : ℝ) - 1) := by rw [hlegR]; exact hsum_le
    have h_div_ub : ∀ A : ℕ, 2 ≤ A → A ∣ n.factorial →
        (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ≤ Real.log (A : ℝ) →
        (largestPrimeFactor A : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (omegaNat A : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (radNat A : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε)) := by
      intro A hA2 hAdvd hA_log
      have hA_pos : 0 < A := by omega
      have hlogA_eq : Real.log (A : ℝ) = ∑ p ∈ A.primeFactors, (padicValNat p A : ℝ) * Real.log p := by
        have hprodA : A = ∏ p ∈ A.primeFactors, p ^ padicValNat p A := by
          conv_lhs => rw [← Nat.prod_primeFactors_pow_factorization hA_pos.ne']
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [Nat.factorization_def A (Nat.prime_of_mem_primeFactors hp)]
        conv_lhs => rw [hprodA, Nat.cast_prod]
        rw [Real.log_prod _ _ fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)]
        refine Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
      have h_vp_le : ∀ p ∈ A.primeFactors, (padicValNat p A : ℝ) * Real.log p ≤ (n : ℝ) * Real.log p / ((p : ℝ) - 1) := by
        intro p hp
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        haveI : Fact p.Prime := ⟨hp_pr⟩
        have hvp_dvd : padicValNat p A ≤ padicValNat p n.factorial :=
          (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mp (dvd_trans pow_padicValNat_dvd hAdvd)
        have hvpR : (padicValNat p A : ℝ) ≤ (padicValNat p n.factorial : ℝ) := by exact_mod_cast hvp_dvd
        have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
        calc (padicValNat p A : ℝ) * Real.log p
            ≤ (padicValNat p n.factorial : ℝ) * Real.log p := mul_le_mul_of_nonneg_right hvpR hlogp_nn
          _ ≤ ((n : ℝ) / ((p : ℝ) - 1)) * Real.log p := mul_le_mul_of_nonneg_right (hvp_fac_le p hp_pr) hlogp_nn
          _ = (n : ℝ) * Real.log p / ((p : ℝ) - 1) := by ring
      set X : ℝ := (n : ℝ) ^ (1 / 2 - ε' / 2)
      set S_small := A.primeFactors.filter (fun p => (p : ℝ) < X)
      set S_big := A.primeFactors.filter (fun p => X ≤ (p : ℝ))
      have hS_small_bd : ∑ p ∈ S_small, (padicValNat p A : ℝ) * Real.log p ≤
          (n : ℝ) * (Real.log X + |Real.eulerMascheroniConstant| + Real.log 2 + 2 + Real.log 2) := by
        have h1 : ∑ p ∈ S_small, (padicValNat p A : ℝ) * Real.log p ≤
            ∑ p ∈ S_small, (n : ℝ) * (Real.log p / ((p : ℝ) - 1)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have h := h_vp_le p (Finset.filter_subset _ _ hp)
          linarith [show (n : ℝ) * Real.log p / ((p : ℝ) - 1) = (n : ℝ) * (Real.log p / ((p : ℝ) - 1)) by ring]
        rw [← Finset.mul_sum] at h1
        have hsplit : S_small ⊆ insert 2 ((Finset.Icc 3 ⌊X⌋₊).filter Nat.Prime) := by
          intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := Nat.prime_of_mem_primeFactors hp_mem.1
          rcases eq_or_lt_of_le hp_pr.two_le with rfl | hp3
          · exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, ?_⟩, hp_pr⟩)
            exact Nat.le_floor hp_mem.2.le
        have hsum_ins : ∑ p ∈ S_small, Real.log p / ((p : ℝ) - 1) ≤
            Real.log 2 / ((2 : ℝ) - 1) +
              ∑ p ∈ (Finset.Icc 3 ⌊X⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsplit fun p _ _ => by
            by_cases hp2 : 2 ≤ p
            · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))) (by
                have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
                linarith)
            · have hp1 : p = 0 ∨ p = 1 := by omega
              rcases hp1 with rfl | rfl <;> simp) ?_
          exact Finset.sum_insert_le_add _ _ _ (by positivity)
        have hlog2_eq : Real.log (2 : ℕ) / ((2 : ℝ) - 1) = Real.log 2 := by norm_num
        rw [hlog2_eq] at hsum_ins
        refine le_trans h1 (mul_le_mul_of_nonneg_left (le_trans hsum_ins (by linarith [h_mert_n])) (Nat.cast_nonneg n))
      have hS_big_bd : ∑ p ∈ S_big, (padicValNat p A : ℝ) * Real.log p ≤
          (S_big.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n) := by
        have hpt : ∀ p ∈ S_big, (padicValNat p A : ℝ) * Real.log p ≤ 2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n := by
          intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := Nat.prime_of_mem_primeFactors hp_mem.1
          haveI : Fact p.Prime := ⟨hp_pr⟩
          have hp_le_n : p ≤ n := hp_pr.dvd_factorial.mp (dvd_trans (Nat.dvd_of_mem_primeFactors hp_mem.1) hAdvd)
          have hlogp_le : Real.log p ≤ Real.log n := Real.log_le_log (by exact_mod_cast hp_pr.pos) (by exact_mod_cast hp_le_n)
          have hp3 : (3 : ℝ) ≤ p := le_trans h_ge3 hp_mem.2
          have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
          have hvp_dvd : padicValNat p A ≤ padicValNat p n.factorial :=
            (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mp (dvd_trans pow_padicValNat_dvd hAdvd)
          have hvp_le2 : (padicValNat p A : ℝ) ≤ 2 * (n : ℝ) / p := by
            calc (padicValNat p A : ℝ) ≤ (padicValNat p n.factorial : ℝ) := by exact_mod_cast hvp_dvd
              _ ≤ (n : ℝ) / ((p : ℝ) - 1) := hvp_fac_le p hp_pr
              _ ≤ (n : ℝ) / ((p : ℝ) / 2) := div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) hp_half
              _ = 2 * (n : ℝ) / p := by ring
          have hnp_le : 2 * (n : ℝ) / p ≤ 2 * (n : ℝ) ^ (1 / 2 + ε' / 2) := by
            calc 2 * (n : ℝ) / p ≤ 2 * (n : ℝ) / X :=
                  div_le_div_of_nonneg_left (by positivity) (by linarith) hp_mem.2
              _ = 2 * (n : ℝ) ^ (1 / 2 + ε' / 2) := by
                  dsimp only [X]
                  rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n), mul_assoc,
                    ← Real.rpow_one (n : ℝ), ← Real.rpow_add hn_pos]
                  congr 2; ring
          exact mul_le_mul (le_trans hvp_le2 hnp_le) hlogp_le (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)) (by positivity)
        calc ∑ p ∈ S_big, (padicValNat p A : ℝ) * Real.log p
            ≤ ∑ _p ∈ S_big, 2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n := Finset.sum_le_sum hpt
          _ = (S_big.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n) := by rw [Finset.sum_const, nsmul_eq_mul]
      have hS_split : ∑ p ∈ A.primeFactors, (padicValNat p A : ℝ) * Real.log p =
          ∑ p ∈ S_small, (padicValNat p A : ℝ) * Real.log p +
          ∑ p ∈ S_big, (padicValNat p A : ℝ) * Real.log p := by
        rw [← Finset.sum_filter_add_sum_filter_not A.primeFactors (fun p => (p : ℝ) < X)]
        congr 2; ext p; simp [S_big]
      have hS_big_card : (n : ℝ) ^ (1 / 2 - ε) ≤ (S_big.card : ℝ) := by
        by_contra hlt; push_neg at hlt
        have h_pow_prod : (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) ^ (1 / 2 + ε' / 2) ≤ (n : ℝ) ^ (1 - ε' / 2) := by
          rw [← Real.rpow_add hn_pos]
          refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) ?_
          have : ε' ≤ ε := min_le_left _ _
          linarith
        have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        have hbig_lt : (S_big.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n) ≤
            2 * (n : ℝ) ^ (1 - ε' / 2) * Real.log n := by
          calc (S_big.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n)
              ≤ (n : ℝ) ^ (1 / 2 - ε) * (2 * (n : ℝ) ^ (1 / 2 + ε' / 2) * Real.log n) :=
                mul_le_mul_of_nonneg_right hlt.le (by positivity)
            _ = 2 * ((n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) ^ (1 / 2 + ε' / 2)) * Real.log n := by ring
            _ ≤ 2 * (n : ℝ) ^ (1 - ε' / 2) * Real.log n :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_pow_prod (by norm_num)) hlogn_nn
        have htot_lt : Real.log (A : ℝ) < (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n := by
          rw [hlogA_eq, hS_split]
          linarith [hm_dom]
        linarith
      have hS_big_ne : S_big.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        rw [hemp, Finset.card_empty, Nat.cast_zero] at hS_big_card
        have : (0 : ℝ) < (n : ℝ) ^ (1 / 2 - ε) := Real.rpow_pos_of_pos hn_pos _
        linarith
      have hlpf : (n : ℝ) ^ (1 / 2 - ε) ≤ (largestPrimeFactor A : ℝ) := by
        obtain ⟨p, hp⟩ := hS_big_ne
        have hp_mem := Finset.mem_filter.mp hp
        have hle_sup : p ≤ largestPrimeFactor A := Finset.le_sup (f := id) hp_mem.1
        have hX_ge : (n : ℝ) ^ (1 / 2 - ε) ≤ X := by
          refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) ?_
          have : ε' ≤ ε := min_le_left _ _
          linarith
        exact le_trans hX_ge (le_trans hp_mem.2 (by exact_mod_cast hle_sup))
      have homega : (n : ℝ) ^ (1 / 2 - ε) ≤ (omegaNat A : ℝ) := by
        have hle : S_big.card ≤ omegaNat A := Finset.card_le_card (Finset.filter_subset _ _)
        exact le_trans hS_big_card (by exact_mod_cast hle)
      have hrad : Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ (radNat A : ℝ) := by
        have hrad_pos : 0 < radNat A := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
        have hlog_rad : (n : ℝ) ^ (1 / 2 - ε) ≤ Real.log (radNat A : ℝ) := by
          unfold radNat
          rw [Nat.cast_prod, Real.log_prod _ _ fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne']
          have hpt : ∀ p ∈ S_big, (1 : ℝ) ≤ Real.log p := by
            intro p hp
            have hp3 : (3 : ℝ) ≤ p := le_trans h_ge3 (Finset.mem_filter.mp hp).2
            have he1 : Real.exp 1 ≤ (p : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9]) hp3
            simpa using Real.log_le_log (Real.exp_pos 1) he1
          calc (n : ℝ) ^ (1 / 2 - ε) ≤ (S_big.card : ℝ) := hS_big_card
            _ = ∑ _p ∈ S_big, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ ∑ p ∈ S_big, Real.log p := Finset.sum_le_sum hpt
            _ ≤ ∑ p ∈ A.primeFactors, Real.log p :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ =>
                  Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
        calc Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ Real.exp (Real.log (radNat A : ℝ)) := Real.exp_le_exp.mpr hlog_rad
          _ = (radNat A : ℝ) := Real.exp_log (by exact_mod_cast hrad_pos)
      exact ⟨hlpf, homega, hrad⟩
    have hm1_eq : m - 1 = 2 * u1 := by dsimp only [u1]; omega
    have hm2_eq : m + 1 = 2 * u2 := by dsimp only [u2]; omega
    have h4_dvd : 4 ∣ n.factorial := dvd_trans (by norm_num : 4 ∣ 24) (by simpa using Nat.factorial_dvd_factorial hn4)
    have hm_prod : (m - 1) * (m + 1) = n.factorial := by
      rw [hm1_eq, hm2_eq, show 2 * u1 * (2 * u2) = 4 * (u1 * u2) by ring, hprod, Nat.mul_div_cancel' h4_dvd]
    have hlog_m1 : (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ≤ Real.log ((m - 1 : ℕ) : ℝ) := by
      have hle : Real.log (u1 : ℝ) ≤ Real.log ((m - 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hu1_pos) (by exact_mod_cast (by omega : u1 ≤ m - 1))
      linarith
    have hlog_m2 : (1 / 2 - ε' / 3) * (n : ℝ) * Real.log n ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      have hle : Real.log (u2 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hu2_pos) (by exact_mod_cast (by omega : u2 ≤ m + 1))
      linarith
    have h1 := h_div_ub (m - 1) (by omega) ⟨m + 1, hm_prod.symm⟩ hlog_m1
    have h2 := h_div_ub (m + 1) (by omega) ⟨m - 1, by rw [mul_comm]; exact hm_prod.symm⟩ hlog_m2
    exact ⟨h1.1, h2.1, h1.2.1, h2.2.1, h1.2.2, h2.2.2⟩

/-- **Theorem 5.2(ii)** (Effective Landau–Siegel sub-exponential core bound). -/
theorem theorem_5_2_ii :
    ∃ c₀ c₂ c₃ C : ℝ, 0 < c₀ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ n : ℕ, (hn : N₀ ≤ n) → (hn6 : n ≠ 6) →
        let d1s := oddPart (deltaMid1 n (by omega) hn6)
        let d2s := oddPart (deltaMid2 n (by omega) hn6)
        let dmin := min d1s d2s
        let Qmin := 8 * dmin
        1 < dmin →
        (Real.exp (2 * c₀ * Real.sqrt (Real.log n)) < (Qmin : ℝ) ∨
          ∃ β₁ : ℝ, 1 - c₂ / Real.log Qmin < β₁ ∧ β₁ < 1 ∧ 0 < β₁ ∧
            |(∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
                (psiMin n (by omega) hn6 p : ℝ) * Real.log p) +
              ((n : ℝ) ^ β₁ - ((n : ℝ) / 2) ^ β₁) / β₁| ≤
            C * n * Real.exp (-c₃ * Real.sqrt (Real.log n))) := by
  obtain ⟨c₀, c₂, c₃, C, hc₀, hc₂, hc₃, hC, hdav⟩ := davenport_explicit_formula_dirichlet
  obtain ⟨N₁, hN₁, h51⟩ := prop_5_1_ii
  have hε_pos : 0 < (1 - Real.log 2) / 4 := by
    have : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    linarith
  have hlim_exp : Tendsto (fun n : ℕ => C * Real.exp (-c₃ * Real.sqrt (Real.log n))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun m : ℕ => Real.sqrt (Real.log m)) atTop atTop :=
      tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hbot : Tendsto (fun m : ℕ => -c₃ * Real.sqrt (Real.log m)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hlog.const_mul_atTop hc₃)
    simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim_exp.eventually (gt_mem_nhds hε_pos))
  obtain ⟨c₁, C₁, hc₁, hC₁, hpnt⟩ := deLaValleePoussin_pnt
  obtain ⟨c_q, C_q, hc_q, hC_q, hqn_err⟩ := lemma_2_1_ii.1
  have hlim_pnt : Tendsto (fun m : ℕ =>
      C₁ * Real.exp (-c₁ * Real.sqrt (Real.log m)) +
      (1 / 2 : ℝ) * C₁ * Real.exp (-c₁ * Real.sqrt (Real.log ((m : ℝ) / 2))) +
      (1 / 2 : ℝ) * C_q * Real.exp (-c_q * Real.sqrt (Real.log m))) atTop (𝓝 0) := by
    have he1 : Tendsto (fun m : ℕ => C₁ * Real.exp (-c₁ * Real.sqrt (Real.log m))) atTop (𝓝 0) := by
      have hbot := tendsto_neg_atTop_atBot.comp ((tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc₁)
      simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C₁
    have he2 : Tendsto (fun m : ℕ => C₁ * Real.exp (-c₁ * Real.sqrt (Real.log ((m : ℝ) / 2)))) atTop (𝓝 0) := by
      have hdiv := tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      have hbot := tendsto_neg_atTop_atBot.comp ((tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hdiv)).const_mul_atTop hc₁)
      simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C₁
    have he3 : Tendsto (fun m : ℕ => C_q * Real.exp (-c_q * Real.sqrt (Real.log m))) atTop (𝓝 0) := by
      have hbot := tendsto_neg_atTop_atBot.comp ((tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc_q)
      simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul C_q
    simpa using (he1.add (he2.const_mul (1 / 2))).add (he3.const_mul (1 / 2))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (hlim_pnt.eventually (ge_mem_nhds hε_pos))
  refine ⟨c₀, c₂, c₃, C, hc₀, hc₂, hc₃, hC, max (max N₁ N₂) (max N₃ 16), le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro n hn hn6
  dsimp only
  set d1s := oddPart (deltaMid1 n (by omega) hn6)
  set d2s := oddPart (deltaMid2 n (by omega) hn6)
  set dmin := min d1s d2s
  set Qmin := 8 * dmin
  intro hdmin_gt1
  by_cases hQ_gt : Real.exp (2 * c₀ * Real.sqrt (Real.log n)) < (Qmin : ℝ)
  · exact Or.inl hQ_gt
  · push_neg at hQ_gt
    right
    have hn16 : 16 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hn8 : 8 ≤ n := by omega
    have hN1_n : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hN2_n : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hN3_n : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hd1s_odd : ¬ 2 ∣ d1s := oddPart_odd coreNat_pos.ne'
    have hd2s_odd : ¬ 2 ∣ d2s := oddPart_odd coreNat_pos.ne'
    have hdmin_odd : ¬ 2 ∣ dmin := by
      dsimp only [dmin]; rcases min_cases d1s d2s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption
    have hdmin_sqf : Squarefree dmin := by
      dsimp only [dmin]; rcases min_cases d1s d2s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
      · exact squarefree_coreNat.squarefree_of_dvd oddPart_dvd
      · exact squarefree_coreNat.squarefree_of_dvd oddPart_dvd
    set D : ℤ := if d1s ≤ d2s then -2 * (deltaMid1 n (by omega) hn6 : ℤ) else 2 * (deltaMid2 n (by omega) hn6 : ℤ)
    have h_mod_Qmin : ∀ x : ℕ, Nat.Coprime x Qmin → jacobiSym D (x % Qmin) = jacobiSym D x := by
      intro x hx
      have hx_odd : x % 2 = 1 := by
        have h2 : Nat.Coprime x 2 := hx.coprime_dvd_right ⟨4 * dmin, by ring⟩
        exact Nat.odd_iff.mp h2.odd_of_right_even (by decide)
      have hx_mod_odd : (x % Qmin) % 2 = 1 := by
        have h2Q : 2 ∣ Qmin := ⟨4 * dmin, by ring⟩
        rw [Nat.mod_mod_of_dvd x h2Q]; exact hx_odd
      have hx_mod_8 : (x % Qmin) % 8 = x % 8 := Nat.mod_mod_of_dvd x ⟨dmin, rfl⟩
      have hx_mod_4 : (x % Qmin) % 4 = x % 4 := Nat.mod_mod_of_dvd x ⟨2 * dmin, by ring⟩
      have hx_mod_dmin : (x % Qmin) % dmin = x % dmin := Nat.mod_mod_of_dvd x ⟨8, by ring⟩
      have h_jac_eq : ∀ y : ℕ, y % 2 = 1 →
          jacobiSym D y =
            (if d1s ≤ d2s then ZMod.χ₄ y else 1) *
            (if (d1s ≤ d2s ∧ ¬ 2 ∣ deltaMid1 n (by omega) hn6) ∨ (¬ d1s ≤ d2s ∧ ¬ 2 ∣ deltaMid2 n (by omega) hn6) then ZMod.χ₈ y else 1) *
            jacobiSym (dmin : ℤ) y := by
        intro y hy
        have hy_ne2 : y % 2 ≠ 0 := by omega
        have h4 : jacobiSym (-1 : ℤ) y = ZMod.χ₄ y := by
          rw [jacobiSym.at_neg_one hy_ne2, ZMod.χ₄_nat_eq_if_mod_four]
        have h8 : jacobiSym (2 : ℤ) y = ZMod.χ₈ y := by
          rw [jacobiSym.at_two hy_ne2, ZMod.χ₈_nat_eq_if_mod_eight]
        by_cases hle : d1s ≤ d2s
        · have hdmin_eq : dmin = d1s := min_eq_left hle
          have hsq1 : Squarefree (deltaMid1 n (by omega) hn6) := squarefree_coreNat
          have hdecomp1 : deltaMid1 n (by omega) hn6 = 2 ^ padicValNat 2 (deltaMid1 n (by omega) hn6) * d1s := by
            unfold d1s oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
          have hv1 : padicValNat 2 (deltaMid1 n (by omega) hn6) ≤ 1 := by
            by_contra hgt; push_neg at hgt
            have hd4 : 2 ^ 2 ∣ deltaMid1 n (by omega) hn6 := dvd_trans (Nat.pow_dvd_pow 2 hgt) pow_padicValNat_dvd
            exact (by decide : ¬ IsUnit 2) (hsq1 2 (by simpa [sq] using hd4))
          dsimp only [D]; rw [if_pos hle, if_pos hle, hdmin_eq]
          by_cases h2d : 2 ∣ deltaMid1 n (by omega) hn6
          · have hv_eq : padicValNat 2 (deltaMid1 n (by omega) hn6) = 1 := by
              haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
              have := (padicValNat_dvd_iff_le coreNat_pos.ne').mp (by simpa using h2d)
              omega
            rw [hdecomp1, hv_eq, pow_one, if_neg (fun h => h.elim (fun h1 => h1.2 h2d) (fun h1 => h1.1 hle)), mul_one]
            rw [show -2 * ((2 * d1s : ℕ) : ℤ) = (-1 : ℤ) * (2 : ℤ) ^ 2 * (d1s : ℤ) by push_cast; ring]
            rw [jacobiSym.mul_left, jacobiSym.mul_left, h4,
              jacobiSym.sq_one (Nat.Coprime.symm (by rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr hy)), mul_one]
          · have hv_eq : padicValNat 2 (deltaMid1 n (by omega) hn6) = 0 := padicValNat.eq_zero_of_not_dvd h2d
            rw [hdecomp1, hv_eq, pow_zero, one_mul, if_pos (Or.inl ⟨hle, h2d⟩)]
            rw [show -2 * (d1s : ℤ) = (-1 : ℤ) * (2 : ℤ) * (d1s : ℤ) by ring]
            rw [jacobiSym.mul_left, jacobiSym.mul_left, h4, h8]
        · have hdmin_eq : dmin = d2s := min_eq_right (le_of_not_ge hle)
          have hsq2 : Squarefree (deltaMid2 n (by omega) hn6) := squarefree_coreNat
          have hdecomp2 : deltaMid2 n (by omega) hn6 = 2 ^ padicValNat 2 (deltaMid2 n (by omega) hn6) * d2s := by
            unfold d2s oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
          have hv2 : padicValNat 2 (deltaMid2 n (by omega) hn6) ≤ 1 := by
            by_contra hgt; push_neg at hgt
            have hd4 : 2 ^ 2 ∣ deltaMid2 n (by omega) hn6 := dvd_trans (Nat.pow_dvd_pow 2 hgt) pow_padicValNat_dvd
            exact (by decide : ¬ IsUnit 2) (hsq2 2 (by simpa [sq] using hd4))
          dsimp only [D]; rw [if_neg hle, if_neg hle, one_mul, hdmin_eq]
          by_cases h2d : 2 ∣ deltaMid2 n (by omega) hn6
          · have hv_eq : padicValNat 2 (deltaMid2 n (by omega) hn6) = 1 := by
              haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
              have := (padicValNat_dvd_iff_le coreNat_pos.ne').mp (by simpa using h2d)
              omega
            rw [hdecomp2, hv_eq, pow_one, if_neg (fun h => h.elim (fun h1 => hle h1.1) (fun h1 => h1.2 h2d)), one_mul]
            rw [show 2 * ((2 * d2s : ℕ) : ℤ) = (2 : ℤ) ^ 2 * (d2s : ℤ) by push_cast; ring]
            rw [jacobiSym.mul_left, jacobiSym.sq_one (Nat.Coprime.symm (by rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr hy)), one_mul]
          · have hv_eq : padicValNat 2 (deltaMid2 n (by omega) hn6) = 0 := padicValNat.eq_zero_of_not_dvd h2d
            rw [hdecomp2, hv_eq, pow_zero, one_mul, if_pos (Or.inr ⟨hle, h2d⟩)]
            rw [show 2 * (d2s : ℤ) = (2 : ℤ) * (d2s : ℤ) by ring]
            rw [jacobiSym.mul_left, h8]
      rw [h_jac_eq (x % Qmin) hx_mod_odd, h_jac_eq x hx_odd]
      have hchi4 : ZMod.χ₄ (x % Qmin) = ZMod.χ₄ x := by
        rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₄_nat_eq_if_mod_four, hx_mod_4]
      have hchi8 : ZMod.χ₈ (x % Qmin) = ZMod.χ₈ x := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight, hx_mod_8]
      have hjac_d : jacobiSym (dmin : ℤ) (x % Qmin) = jacobiSym (dmin : ℤ) x := by
        have hdmin_odd' : dmin % 2 ≠ 0 := by omega
        rw [jacobiSym.quadratic_reciprocity hdmin_odd' (by omega : (x % Qmin) % 2 ≠ 0),
          jacobiSym.quadratic_reciprocity hdmin_odd' (by omega : x % 2 ≠ 0)]
        have h1 : jacobiSym ((x % Qmin : ℕ) : ℤ) dmin = jacobiSym (x : ℤ) dmin := by
          rw [← jacobiSym.mod_left ((x % Qmin : ℕ) : ℤ) dmin, ← jacobiSym.mod_left (x : ℤ) dmin]
          congr 1; exact_mod_cast hx_mod_dmin
        rw [h1, hx_mod_4]
      rw [hchi4, hchi8, hjac_d]
    have hQ1 : 1 < Qmin := by omega
    haveI : NeZero Qmin := ⟨by omega⟩
    let χ : DirichletCharacter ℝ Qmin :=
      { toFun := fun x => if IsUnit x then (jacobiSym D x.val : ℝ) else 0
        map_one' := by
          rw [if_pos isUnit_one, ZMod.val_one, jacobiSym.one_right]; norm_num
        map_mul' := fun x y => by
          by_cases hxy : IsUnit (x * y)
          · have hx : IsUnit x := isUnit_of_mul_isUnit_left hxy
            have hy : IsUnit y := isUnit_of_mul_isUnit_right hxy
            rw [if_pos hxy, if_pos hx, if_pos hy, ZMod.val_mul]
            have hcop_xy : Nat.Coprime (x.val * y.val) Qmin :=
              ((ZMod.isUnit_iff_coprime x.val Qmin).mp (by simpa using hx)).mul_left
                ((ZMod.isUnit_iff_coprime y.val Qmin).mp (by simpa using hy))
            rw [h_mod_Qmin (x.val * y.val) hcop_xy, Nat.cast_mul, jacobiSym.mul_right]
            push_cast; rfl
          · rw [if_neg hxy]
            rcases not_and_or.mp (mt (fun ⟨hx, hy⟩ => hx.mul hy) hxy) with hnx | hny
            · rw [if_neg hnx, zero_mul]
            · rw [if_neg hny, mul_zero]
        map_nonunit' := fun x hx => if_neg hx }
    have hχ_ne1 : χ ≠ 1 := by
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : dmin ≠ 1)
      have hq_odd : q ≠ 2 := fun h => hdmin_odd (h ▸ hqdvd)
      have hq_sq : ¬ q ^ 2 ∣ dmin := fun h => hq.not_isUnit (hdmin_sqf q (by simpa [sq] using h))
      have hnsq : ∃ a : ℕ, jacobiSym (a : ℤ) q = -1 := by
        haveI : Fact q.Prime := ⟨hq⟩
        obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (ZMod q)
        refine ⟨u.val, ?_⟩
        rw [jacobiSym.legendreSym_eq]
        exact legendreSym.eq_neg_one_iff.mpr (by simpa [ZMod.natCast_zmod_val] using hu)
      obtain ⟨a, ha⟩ := hnsq
      have hcop_a_q : Nat.Coprime a q := by
        by_contra hnc
        have hqa : q ∣ a := hq.dvd_iff_not_coprime.mpr hnc.symm
        have : jacobiSym (a : ℤ) q = 0 := jacobiSym.eq_zero_iff.mpr ⟨by omega, by
          have : (q : ℤ).gcd a = q := by
            rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
            exact Nat.gcd_eq_left hqa
          omega⟩
        omega
      have hcop_q_rest : Nat.Coprime q (Qmin / q) := by
        have h1 : Qmin / q = 8 * (dmin / q) := by
          rcases hqdvd with ⟨t, ht⟩
          rw [show Qmin = 8 * (q * t) by rw [ht], Nat.mul_left_comm, Nat.mul_div_cancel_left _ hq.pos,
            Nat.mul_div_cancel_left _ hq.pos]
        rw [h1]
        refine Nat.Coprime.mul_right (((Nat.coprime_primes hq (by decide)).mpr hq_odd).pow_right 3) ?_
        by_contra hnc
        have hqt : q ∣ dmin / q := hq.dvd_iff_not_coprime.mpr hnc.symm
        rcases hqdvd with ⟨t, ht⟩
        rw [ht, Nat.mul_div_cancel_left _ hq.pos] at hqt
        rcases hqt with ⟨s, hs⟩
        exact hq_sq ⟨s, by rw [ht, hs]; ring⟩
      obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder hcop_q_rest a 1
      have hcop_x_Q : Nat.Coprime x Qmin := by
        have hQ_eq : Qmin = q * (Qmin / q) := (Nat.mul_div_cancel' (dvd_trans hqdvd ⟨8, by ring⟩)).symm
        rw [hQ_eq]
        refine Nat.Coprime.mul_right ?_ ?_
        · rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← Nat.gcd_mod x q, hx1, Nat.gcd_mod]
          exact hcop_a_q.symm.gcd_eq_one
        · rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_mod (Qmin / q) x, Nat.gcd_comm, ← Nat.gcd_mod x (Qmin / q), hx2]
          simp
      have hχ_x : χ (x : ZMod Qmin) = -1 := by
        have hunit : IsUnit (x : ZMod Qmin) := (ZMod.isUnit_iff_coprime x Qmin).mpr hcop_x_Q
        dsimp only [χ]; rw [if_pos hunit, ZMod.val_natCast, h_mod_Qmin x hcop_x_Q]
        have hx8 : x % 8 = 1 := by
          have h8_dvd : 8 ∣ Qmin / q := by
            rcases hqdvd with ⟨t, ht⟩
            exact ⟨t, by rw [show Qmin = 8 * (q * t) by rw [ht], Nat.mul_left_comm, Nat.mul_div_cancel_left _ hq.pos]⟩
          have := Nat.mod_mod_of_dvd x h8_dvd
          rw [hx2, Nat.mod_mod_of_dvd 1 h8_dvd] at this
          exact this
        have hx_dmin_q : x % (dmin / q) = 1 % (dmin / q) := by
          have hd_dvd : dmin / q ∣ Qmin / q := by
            rcases hqdvd with ⟨t, ht⟩
            exact ⟨8, by rw [show Qmin = 8 * (q * t) by rw [ht], Nat.mul_left_comm, Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_cancel_left _ hq.pos]; ring⟩
          have := Nat.mod_mod_of_dvd x hd_dvd
          rw [hx2, Nat.mod_mod_of_dvd 1 hd_dvd] at this
          exact this
        have hjac_d : jacobiSym (dmin : ℤ) x = -1 := by
          rcases hqdvd with ⟨t, ht⟩
          rw [ht, Nat.cast_mul, jacobiSym.mul_left]
          have hjac_q : jacobiSym (q : ℤ) x = -1 := by
            rw [jacobiSym.quadratic_reciprocity (by omega : q % 2 ≠ 0) (by omega : x % 2 ≠ 0), show x % 4 = 1 by omega]
            simp only [ne_eq, OfNat.one_ne_ofMat, false_and, ↓reduceIte, mul_one]
            rw [← jacobiSym.mod_left (x : ℤ) q, show (x : ℤ) % q = (a : ℤ) % q by exact_mod_cast hx1,
              jacobiSym.mod_left, ha]
          have hjac_t : jacobiSym (t : ℤ) x = 1 := by
            have ht_odd : t % 2 ≠ 0 := fun h => hdmin_odd ⟨t / 2, by rw [ht]; omega⟩
            rw [jacobiSym.quadratic_reciprocity ht_odd (by omega : x % 2 ≠ 0), show x % 4 = 1 by omega]
            simp only [ne_eq, OfNat.one_ne_ofMat, false_and, ↓reduceIte, mul_one]
            rw [← jacobiSym.mod_left (x : ℤ) t]
            have hxt : (x : ℤ) % t = 1 % t := by
              have : dmin / q = t := by rw [ht, Nat.mul_div_cancel_left _ hq.pos]
              rw [this] at hx_dmin_q; exact_mod_cast hx_dmin_q
            rw [hxt, jacobiSym.mod_left, jacobiSym.one_left]
          rw [hjac_q, hjac_t]; norm_num
        have h4 : jacobiSym (-1 : ℤ) x = 1 := by
          rw [jacobiSym.at_neg_one (by omega), ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]
        have h8 : jacobiSym (2 : ℤ) x = 1 := by
          rw [jacobiSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight, if_pos (by omega)]
        have hD_neg1 : jacobiSym D x = -1 := by
          dsimp only [D]
          split_ifs with hle
          · rw [show -2 * (deltaMid1 n (by omega) hn6 : ℤ) = (-1 : ℤ) * 2 * (deltaMid1 n (by omega) hn6 : ℤ) by ring,
              jacobiSym.mul_left, jacobiSym.mul_left, h4, h8, one_mul, one_mul]
            have hdecomp : deltaMid1 n (by omega) hn6 = 2 ^ padicValNat 2 (deltaMid1 n (by omega) hn6) * d1s := by
              unfold d1s oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
            have hd1_eq : d1s = dmin := (min_eq_left hle).symm
            rw [hdecomp, Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left, h8, one_pow, one_mul, hd1_eq, hjac_d]
          · rw [show 2 * (deltaMid2 n (by omega) hn6 : ℤ) = (2 : ℤ) * (deltaMid2 n (by omega) hn6 : ℤ) by ring,
              jacobiSym.mul_left, h8, one_mul]
            have hdecomp : deltaMid2 n (by omega) hn6 = 2 ^ padicValNat 2 (deltaMid2 n (by omega) hn6) * d2s := by
              unfold d2s oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
            have hd2_eq : d2s = dmin := (min_eq_right (le_of_not_ge hle)).symm
            rw [hdecomp, Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left, h8, one_pow, one_mul, hd2_eq, hjac_d]
        rw [hD_neg1]; norm_num
      intro h1
      rw [h1] at hχ_x
      have h1_val : (1 : DirichletCharacter ℝ Qmin) (x : ZMod Qmin) = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime x Qmin).mpr hcop_x_Q)
      rw [h1_val] at hχ_x
      norm_num at hχ_x
    have hsum_eq : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, χ p * Real.log p =
        ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, (psiMin n (by omega) hn6 p : ℝ) * Real.log p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_mem := Finset.mem_filter.mp hp
      have hp_icc := Finset.mem_Icc.mp hp_mem.1
      have hp5 : 5 ≤ p := by omega
      have hp_odd : p ≠ 2 := by omega
      have hψ := psiMin_eq_one_or_zero hn8 hn6 hp_mem.2 hp_icc.1 hp_icc.2
      change χ (p : ZMod Qmin) * Real.log p = (psiMin n (by omega) hn6 p : ℝ) * Real.log p
      congr 1
      by_cases hpd : p ∣ dmin
      · have hpQ : p ∣ Qmin := dvd_trans hpd ⟨8, by ring⟩
        have hnu : ¬ IsUnit (p : ZMod Qmin) := by
          rw [ZMod.isUnit_iff_coprime]
          intro hcop
          exact hp_mem.2.not_dvd_one (hcop ▸ Nat.dvd_gcd dvd_rfl hpQ)
        dsimp only [χ]; rw [if_neg hnu, hψ, if_pos hpd]; norm_num
      · have hcop_pQ : Nat.Coprime p Qmin := by
          refine Nat.Coprime.mul_right ?_ (hp_mem.2.coprime_iff_not_dvd.mpr hpd)
          exact ((Nat.coprime_primes hp_mem.2 (by decide)).mpr hp_odd).pow_right 3
        have hu : IsUnit (p : ZMod Qmin) := (ZMod.isUnit_iff_coprime p Qmin).mpr hcop_pQ
        dsimp only [χ]; rw [if_pos hu, ZMod.val_natCast, h_mod_Qmin p hcop_pQ]
        have hψ' : jacobiSym D p = psiMin n (by omega) hn6 p := by
          unfold psiMin; dsimp only [D]; rfl
        rw [hψ']
    have hdav_n := hdav n Qmin χ hn16 hQ1 hχ_ne1 hQ_gt
    rcases hdav_n with hsmall | hzero
    · exfalso
      have h_lb : ((1 - Real.log 2) / 4) * (n : ℝ) ≤
          ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, (psiMin n (by omega) hn6 p : ℝ) * Real.log p := by
        have hsum_theta : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
              (psiMin n (by omega) hn6 p : ℝ) * Real.log p =
            Chebyshev.theta n - Chebyshev.theta ((n : ℝ) / 2) -
              ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin), Real.log p := by
          have hpt : ∀ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
              (psiMin n (by omega) hn6 p : ℝ) * Real.log p =
                Real.log p - (if p ∣ dmin then Real.log p else 0) := by
            intro p hp
            have hp_mem := Finset.mem_filter.mp hp
            have hp_icc := Finset.mem_Icc.mp hp_mem.1
            rw [psiMin_eq_one_or_zero hn8 hn6 hp_mem.2 hp_icc.1 hp_icc.2]
            split_ifs <;> simp
          rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.filter_filter]
          have htheta : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, Real.log p =
              Chebyshev.theta n - Chebyshev.theta ((n : ℝ) / 2) := by
            have hfl1 : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_div_eq_div]
            have hfl2 : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
            have hsub : (Finset.Ioc 0 ⌊(n : ℝ) / 2⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊(n : ℝ)⌋₊).filter Nat.Prime := by
              intro p hp
              simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
              exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono (by linarith))⟩, hp.2⟩
            have hsdiff : (Finset.Ioc 0 ⌊(n : ℝ)⌋₊).filter Nat.Prime \ (Finset.Ioc 0 ⌊(n : ℝ) / 2⌋₊).filter Nat.Prime =
                (Finset.Icc (n / 2 + 1) n).filter Nat.Prime := by
              ext p
              simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, hfl1, hfl2]
              constructor
              · rintro ⟨⟨⟨_, hpb⟩, hp⟩, hnot⟩
                have hpa : n / 2 < p := by by_contra hle; exact hnot ⟨⟨by omega, by omega⟩, hp⟩
                exact ⟨⟨by omega, hpb⟩, hp⟩
              · rintro ⟨⟨hpa, hpb⟩, hp⟩
                exact ⟨⟨⟨hp.pos, hpb⟩, hp⟩, fun h => by omega⟩
            unfold Chebyshev.theta
            rw [← Finset.sum_sdiff hsub, hsdiff]
            ring
          rw [htheta]
        rw [hsum_theta]
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have h_err := hN3 n hN3_n
        have hpnt1 := (hpnt n (by exact_mod_cast (by omega : 2 ≤ n))).1
        have hpnt2 := (hpnt ((n : ℝ) / 2) (by
          have : (8 : ℝ) ≤ n := by exact_mod_cast hn8
          linarith)).1
        have hqn1 := hqn_err n hn8
        have hdmin_sum : ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin), Real.log p ≤
            Real.log dmin := by
          set S := (Finset.Icc (n / 2 + 1) n).filter (fun p => p.Prime ∧ p ∣ dmin)
          have hprod_dvd : (∏ p ∈ S, p) ∣ dmin :=
            Finset.prod_primes_dvd dmin (fun p hp => (Finset.mem_filter.mp hp).2.1) (fun p hp => (Finset.mem_filter.mp hp).2.2)
          have hprod_le : (∏ p ∈ S, (p : ℝ)) ≤ (dmin : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega : 0 < dmin) hprod_dvd
          have hlog_prod : ∑ p ∈ S, Real.log p = Real.log (∏ p ∈ S, (p : ℝ)) := by
            rw [Real.log_prod]; intro p hp; exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.1.ne_zero
          rw [hlog_prod]
          exact Real.log_le_log (Finset.prod_pos fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos) hprod_le
        have h51i := prop_5_1_i n hn8 hn6
        have hdmin_log_lt : Real.log dmin < (1 / 2 : ℝ) * Real.log (qn n) := by
          have hlt1 : Real.log dmin < Real.log (Real.sqrt (qn n)) :=
            Real.log_lt_log (by exact_mod_cast (by omega : 0 < dmin)) (lt_of_lt_of_le h51i.2.2.2.1 h51i.2.2.2.2.1)
          rwa [Real.sqrt_eq_rpow, Real.log_rpow (by exact_mod_cast qn_pos n), mul_comm, one_div] at hlt1
        have h1 : Chebyshev.theta n ≥ (n : ℝ) - C₁ * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log n)) := by
          linarith [(abs_le.mp hpnt1).1]
        have h2 : Chebyshev.theta ((n : ℝ) / 2) ≤ (n : ℝ) / 2 + C₁ * ((n : ℝ) / 2) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / 2))) := by
          linarith [(abs_le.mp hpnt2).2]
        have h3 : Real.log (qn n) ≤ Real.log 2 * (n : ℝ) + C_q * (n : ℝ) * Real.exp (-c_q * Real.sqrt (Real.log n)) := by
          linarith [(abs_le.mp hqn1).2]
        have h4 : (C₁ * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log n)) +
            C₁ * ((n : ℝ) / 2) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / 2))) +
            (1 / 2 : ℝ) * C_q * (n : ℝ) * Real.exp (-c_q * Real.sqrt (Real.log n))) ≤ ((1 - Real.log 2) / 4) * (n : ℝ) := by
          have herr' : C₁ * Real.exp (-c₁ * Real.sqrt (Real.log n)) +
              (1 / 2 : ℝ) * C₁ * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / 2))) +
              (1 / 2 : ℝ) * C_q * Real.exp (-c_q * Real.sqrt (Real.log n)) ≤ (1 - Real.log 2) / 4 := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_err
            exact h_err
          nlinarith [hn_pos]
        linarith
      rw [hsum_eq] at hsmall
      have h_ub := (abs_le.mp hsmall).2
      have hN2' : C * Real.exp (-c₃ * Real.sqrt (Real.log n)) < (1 - Real.log 2) / 4 := by
        have := hN2 n hN2_n
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
        exact this
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have : C * (n : ℝ) * Real.exp (-c₃ * Real.sqrt (Real.log n)) < ((1 - Real.log 2) / 4) * (n : ℝ) := by
        nlinarith [hn_pos]
      linarith
    · rw [hsum_eq] at hzero
      exact hzero

/-- **Lemma 5.3(i)** (Homogeneous `𝔽₂`-Laplacian cascade / bipartition congruences). -/
lemma lemma_5_3_i (n m : ℕ) (hn : 8 ≤ n) (hsol : IsBrocardSol n m) :
    let u1 := (m - 1) / 2
    let u2 := (m + 1) / 2
    let w1 := padicValNat 2 u1
    let w2 := padicValNat 2 u2
    (∀ p ∈ (Podd n).filter (3 ≤ ·), p ∣ B1sol n m →
      (2 ^ w2 * B2sol n m : ZMod p) * (Z2starSol n m : ZMod p) ^ 2 = 1 ∧
      jacobiSym (2 ^ w2 * (B2sol n m : ℤ)) p = 1) ∧
    (∀ p ∈ (Podd n).filter (3 ≤ ·), p ∣ B2sol n m →
      (2 ^ w1 * B1sol n m : ZMod p) * (Z1starSol n m : ZMod p) ^ 2 = -1 ∧
      jacobiSym (-(2 ^ w1 * (B1sol n m : ℤ))) p = 1) := by
  dsimp only
  obtain ⟨_, _, hu2_eq, hu1_pos, hu2_pos, _, _⟩ := brocard_sol_u1_u2 (by omega) hsol
  obtain ⟨_, _, hu1_eq, hu2_eqR, _⟩ := brocard_B_Z_prod_eq (by omega) hsol
  set u1 := (m - 1) / 2
  set u2 := (m + 1) / 2
  set w1 := padicValNat 2 u1
  set w2 := padicValNat 2 u2
  have hu1_nat : u1 = 2 ^ w1 * B1sol n m * Z1starSol n m ^ 2 := by exact_mod_cast hu1_eq
  have hu2_nat : u2 = 2 ^ w2 * B2sol n m * Z2starSol n m ^ 2 := by exact_mod_cast hu2_eqR
  refine ⟨?_, ?_⟩
  · intro p hp hpB1
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hpu1 : p ∣ u1 := dvd_trans hpB1 (by rw [hu1_nat]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    have hu2_mod : (u2 : ZMod p) = 1 := by
      rw [hu2_eq, Nat.cast_add, Nat.cast_one]
      have : (u1 : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd u1 p).mpr hpu1
      rw [this, zero_add]
    have hmod : (2 ^ w2 * B2sol n m : ZMod p) * (Z2starSol n m : ZMod p) ^ 2 = 1 := by
      have h1 : ((2 ^ w2 * B2sol n m * Z2starSol n m ^ 2 : ℕ) : ZMod p) = 1 := by
        rw [← hu2_nat]; exact hu2_mod
      simpa [Nat.cast_mul, Nat.cast_pow] using h1
    refine ⟨hmod, ?_⟩
    have hnp_Z2 : ¬ p ∣ Z2starSol n m := by
      intro hdiv
      have hpu2 : p ∣ u2 := by rw [hu2_nat]; exact dvd_mul_of_dvd_right (dvd_pow hdiv (by norm_num)) _
      have : (u2 : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd u2 p).mpr hpu2
      rw [hu2_mod] at this; exact one_ne_zero this
    have h2 := jacobiSym.mod_left (2 ^ w2 * (B2sol n m : ℤ) * (Z2starSol n m : ℤ) ^ 2) p
    have h3 := jacobiSym.mod_left (1 : ℤ) p
    have hint : (2 ^ w2 * (B2sol n m : ℤ) * (Z2starSol n m : ℤ) ^ 2) % p = (1 : ℤ) % p := by
      rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (by push_cast; exact hmod)
    have hjac_sq : jacobiSym (2 ^ w2 * (B2sol n m : ℤ) * (Z2starSol n m : ℤ) ^ 2) p = 1 := by
      rw [h2, hint, ← h3]; simp [jacobiSym.one_left]
    rwa [jacobiSym.mul_left, jacobiSym.sq_one (hp_pr.coprime_iff_not_dvd.mpr hnp_Z2).symm, mul_one] at hjac_sq
  · intro p hp hpB2
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hpu2 : p ∣ u2 := dvd_trans hpB2 (by rw [hu2_nat]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    have hu1_mod : (u1 : ZMod p) = -1 := by
      have h2 : (u2 : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd u2 p).mpr hpu2
      have h1 : (u1 : ZMod p) + 1 = (u2 : ZMod p) := by exact_mod_cast (by rw [hu2_eq] : u1 + 1 = u2)
      rw [h2] at h1; exact eq_neg_of_add_eq_zero_left h1
    have hmod : (2 ^ w1 * B1sol n m : ZMod p) * (Z1starSol n m : ZMod p) ^ 2 = -1 := by
      have h1 : ((2 ^ w1 * B1sol n m * Z1starSol n m ^ 2 : ℕ) : ZMod p) = -1 := by
        rw [← hu1_nat]; exact hu1_mod
      simpa [Nat.cast_mul, Nat.cast_pow] using h1
    refine ⟨hmod, ?_⟩
    have hnp_Z1 : ¬ p ∣ Z1starSol n m := by
      intro hdiv
      have hpu1 : p ∣ u1 := by rw [hu1_nat]; exact dvd_mul_of_dvd_right (dvd_pow hdiv (by norm_num)) _
      have : (u1 : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd u1 p).mpr hpu1
      rw [hu1_mod] at this
      exact (CharP.cast_eq_zero_iff (ZMod p) p 1).not.mpr (by omega) (neg_eq_zero.mp this.symm ▸ rfl)
    have h2 := jacobiSym.mod_left (-(2 ^ w1 * (B1sol n m : ℤ)) * (Z1starSol n m : ℤ) ^ 2) p
    have h3 := jacobiSym.mod_left (1 : ℤ) p
    have hint : (-(2 ^ w1 * (B1sol n m : ℤ)) * (Z1starSol n m : ℤ) ^ 2) % p = (1 : ℤ) % p := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      refine (ZMod.intCast_eq_intCast_iff _ _ p).mp ?_
      push_cast; rw [neg_mul, hmod, neg_neg]
    have hjac_sq : jacobiSym (-(2 ^ w1 * (B1sol n m : ℤ)) * (Z1starSol n m : ℤ) ^ 2) p = 1 := by
      rw [h2, hint, ← h3]; simp [jacobiSym.one_left]
    rwa [jacobiSym.mul_left, jacobiSym.sq_one (hp_pr.coprime_iff_not_dvd.mpr hnp_Z1).symm, mul_one] at hjac_sq

private lemma k1_fermatQuot_mul {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    fermatQuot p (a * b) = fermatQuot p a + fermatQuot p b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha_mod : (a : ZMod p) ≠ 0 := fun h => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hb_mod : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have ha_flt : (p : ℤ) ∣ a ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
    rw [ZMod.pow_card_sub_one_eq_one ha_mod, sub_self]
  have hb_flt : (p : ℤ) ∣ b ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
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
  push_cast; simp [ZMod.natCast_self]

/-- **Lemma 5.3(ii)** (Fermat-quotient bipartition equation with Audit Item 21 sign fix,
and Wolstenholme evaluation on `(n/3, n/2]`). -/
lemma lemma_5_3_ii :
    (∀ (n p : ℕ) (y : ℕ → Bool), 4 ≤ n → p ∈ (Podd n).filter (3 ≤ ·) →
      let P3 := (Podd n).filter (3 ≤ ·)
      let A := ∏ q ∈ P3.filter (fun q => y q = true), q ^ padicValNat q n.factorial
      let B := ∏ q ∈ P3.filter (fun q => y q = false), q ^ padicValNat q n.factorial
      let Np := ∏ q ∈ P3, q ^ padicValNat q n.factorial
      fermatQuot p ((A / p ^ padicValNat p A : ℕ) : ℤ) +
        fermatQuot p ((B / p ^ padicValNat p B : ℕ) : ℤ) -
        fermatQuot p ((Np / p ^ padicValNat p Np : ℕ) : ℤ) = 0) ∧
    (∀ n p : ℕ, 9 ≤ n → p.Prime → n / 3 < p → p ≤ n / 2 →
      padicValNat p n.factorial = 2 ∧ p ∈ Peven n ∧
      (n.factorial / p ^ 2 : ZMod p) = 2 * ((n - 2 * p).factorial : ZMod p) ∧
      (n.factorial / p ^ 2 : ZMod p) ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro n p y _ hp
    dsimp only
    set P3 := (Podd n).filter (3 ≤ ·)
    set A := ∏ q ∈ P3.filter (fun q => y q = true), q ^ padicValNat q n.factorial
    set B := ∏ q ∈ P3.filter (fun q => y q = false), q ^ padicValNat q n.factorial
    set Np := ∏ q ∈ P3, q ^ padicValNat q n.factorial
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hdisj : Disjoint (P3.filter (fun q => y q = true)) (P3.filter (fun q => y q = false)) := by
      rw [Finset.disjoint_left]; intro q h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      simp_all
    have hunion : P3.filter (fun q => y q = true) ∪ P3.filter (fun q => y q = false) = P3 := by
      ext q; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; cases hy : y q <;> [exact Or.inr ⟨h, hy⟩; exact Or.inl ⟨h, hy⟩]
    have hAB_eq : A * B = Np := by
      dsimp only [A, B, Np]
      rw [← Finset.prod_union hdisj, hunion]
    have hA_pos : 0 < A := Finset.prod_pos fun q hq =>
      pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2.1.pos _
    have hB_pos : 0 < B := Finset.prod_pos fun q hq =>
      pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2.1.pos _
    have hNp_pos : 0 < Np := Finset.prod_pos fun q hq =>
      pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos _
    have hv_eq : padicValNat p A + padicValNat p B = padicValNat p Np := by
      rw [← padicValNat.mul hA_pos.ne' hB_pos.ne', hAB_eq]
    have hAp_dvd : p ^ padicValNat p A ∣ A := pow_padicValNat_dvd
    have hBp_dvd : p ^ padicValNat p B ∣ B := pow_padicValNat_dvd
    have hNpp_dvd : p ^ padicValNat p Np ∣ Np := pow_padicValNat_dvd
    have hprod_div : (A / p ^ padicValNat p A) * (B / p ^ padicValNat p B) = Np / p ^ padicValNat p Np := by
      have h1 : (p ^ padicValNat p A * (A / p ^ padicValNat p A)) * (p ^ padicValNat p B * (B / p ^ padicValNat p B)) =
          p ^ padicValNat p Np * (Np / p ^ padicValNat p Np) := by
        rw [Nat.mul_div_cancel' hAp_dvd, Nat.mul_div_cancel' hBp_dvd, Nat.mul_div_cancel' hNpp_dvd, hAB_eq]
      have h2 : p ^ padicValNat p Np * ((A / p ^ padicValNat p A) * (B / p ^ padicValNat p B)) =
          p ^ padicValNat p Np * (Np / p ^ padicValNat p Np) := by
        rw [← hv_eq, pow_add]; linarith
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp_pr.pos _) h2
    have hnpA : ¬ (p : ℤ) ∣ ((A / p ^ padicValNat p A : ℕ) : ℤ) := by
      exact_mod_cast Nat.not_dvd_ordCompl hp_pr hA_pos.ne'
    have hnpB : ¬ (p : ℤ) ∣ ((B / p ^ padicValNat p B : ℕ) : ℤ) := by
      exact_mod_cast Nat.not_dvd_ordCompl hp_pr hB_pos.ne'
    have hmul := k1_fermatQuot_mul hp_pr hnpA hnpB
    rw [← Nat.cast_mul, hprod_div] at hmul
    rw [← hmul, sub_self]
  · intro n p hn9 hp hlo hhi
    haveI : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 ≤ p := by omega
    have hlog : Nat.log p n = 1 := by
      rw [Nat.log_eq_iff (by omega : p ≠ 1) (by omega : n ≠ 0)]
      have hnsq : n < p ^ 2 := by nlinarith [Nat.div_add_mod n 3, Nat.mod_lt n (by norm_num : 0 < 3)]
      exact ⟨by simpa using (by omega : p ≤ n), by simpa using hnsq⟩
    have hleg := sub_one_mul_padicValNat_factorial (p := p) n
    rw [hlog, Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Ico_self, Finset.sum_empty,
      zero_add, pow_one] at hleg
    have hdiv : n / p = 2 := Nat.div_eq_of_lt_le (by omega)
      (by nlinarith [Nat.div_add_mod n 3, Nat.mod_lt n (by norm_num : 0 < 3)])
    rw [hdiv] at hleg
    have hvp2 : padicValNat p n.factorial = 2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p - 1) (by omega)
    have hp_Peven : p ∈ Peven n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, by omega⟩, hp, hvp2 ▸ dvd_rfl⟩
    have hn_lt_3p : n < 3 * p := by nlinarith [Nat.div_add_mod n 3, Nat.mod_lt n (by norm_num : 0 < 3)]
    have h2p_le_n : 2 * p ≤ n := by omega
    have hfac_nat : n.factorial / p ^ 2 =
        (p - 1).factorial * (∏ i ∈ Finset.Icc (p + 1) (2 * p - 1), i) * 2 * (∏ i ∈ Finset.Icc (2 * p + 1) n, i) := by
      have h1 : n.factorial = ∏ i ∈ Finset.Icc 1 n, i := by
        rw [← Finset.prod_Ico_id_eq_factorial, show Finset.Ico 1 (n + 1) = Finset.Icc 1 n by ext x; simp; omega]
      have hpart : Finset.Icc 1 n =
          Finset.Icc 1 (p - 1) ∪ {p} ∪ Finset.Icc (p + 1) (2 * p - 1) ∪ {2 * p} ∪ Finset.Icc (2 * p + 1) n := by
        ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]; omega
      have hprod_eq : n.factorial = p ^ 2 * ((p - 1).factorial * (∏ i ∈ Finset.Icc (p + 1) (2 * p - 1), i) * 2 *
          (∏ i ∈ Finset.Icc (2 * p + 1) n, i)) := by
        rw [h1, hpart,
          Finset.prod_union (by rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at h1 h2; omega),
          Finset.prod_union (by rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at h1 h2; omega),
          Finset.prod_union (by rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at h1 h2; omega),
          Finset.prod_union (by rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at h1 h2; omega),
          Finset.prod_singleton, Finset.prod_singleton]
        have hf1 : ∏ i ∈ Finset.Icc 1 (p - 1), i = (p - 1).factorial := by
          rw [← Finset.prod_Ico_id_eq_factorial, show Finset.Ico 1 (p - 1 + 1) = Finset.Icc 1 (p - 1) by ext x; simp; omega]
        rw [hf1]; ring
      rw [hprod_eq, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
    have hmod_eq : (n.factorial / p ^ 2 : ZMod p) = 2 * ((n - 2 * p).factorial : ZMod p) := by
      rw [hfac_nat]
      push_cast
      have hw : ((p - 1).factorial : ZMod p) = -1 := ZMod.wilsons_lemma p
      have hmid : (∏ i ∈ Finset.Icc (p + 1) (2 * p - 1), (i : ZMod p)) = -1 := by
        have hbij : ∏ i ∈ Finset.Icc (p + 1) (2 * p - 1), (i : ZMod p) =
            ∏ j ∈ Finset.Icc 1 (p - 1), ((p + j : ℕ) : ZMod p) := by
          refine Finset.prod_bij (fun i _ => i - p)
            (fun i hi => by simp only [Finset.mem_Icc] at hi ⊢; omega)
            (fun i₁ hi₁ i₂ hi₂ h => by simp only [Finset.mem_Icc] at hi₁ hi₂; omega)
            (fun j hj => ⟨p + j, by simp only [Finset.mem_Icc] at hj ⊢; omega, by omega⟩)
            (fun i hi => by simp only [Finset.mem_Icc] at hi; rw [Nat.add_sub_cancel' (by omega)])
        rw [hbij]
        have hcongr : ∏ j ∈ Finset.Icc 1 (p - 1), ((p + j : ℕ) : ZMod p) =
            ∏ j ∈ Finset.Icc 1 (p - 1), (j : ZMod p) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          push_cast; simp [ZMod.natCast_self]
        rw [hcongr]
        have hf1 : ∏ j ∈ Finset.Icc 1 (p - 1), j = (p - 1).factorial := by
          rw [← Finset.prod_Ico_id_eq_factorial, show Finset.Ico 1 (p - 1 + 1) = Finset.Icc 1 (p - 1) by ext x; simp; omega]
        rw [← Nat.cast_prod, hf1, hw]
      have htop : (∏ i ∈ Finset.Icc (2 * p + 1) n, (i : ZMod p)) = ((n - 2 * p).factorial : ZMod p) := by
        have hbij : ∏ i ∈ Finset.Icc (2 * p + 1) n, (i : ZMod p) =
            ∏ j ∈ Finset.Icc 1 (n - 2 * p), ((2 * p + j : ℕ) : ZMod p) := by
          refine Finset.prod_bij (fun i _ => i - 2 * p)
            (fun i hi => by simp only [Finset.mem_Icc] at hi ⊢; omega)
            (fun i₁ hi₁ i₂ hi₂ h => by simp only [Finset.mem_Icc] at hi₁ hi₂; omega)
            (fun j hj => ⟨2 * p + j, by simp only [Finset.mem_Icc] at hj ⊢; omega, by omega⟩)
            (fun i hi => by simp only [Finset.mem_Icc] at hi; rw [Nat.add_sub_cancel' (by omega)])
        rw [hbij]
        have hcongr : ∏ j ∈ Finset.Icc 1 (n - 2 * p), ((2 * p + j : ℕ) : ZMod p) =
            ∏ j ∈ Finset.Icc 1 (n - 2 * p), (j : ZMod p) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          push_cast; simp [ZMod.natCast_self]
        rw [hcongr]
        have hf2 : ∏ j ∈ Finset.Icc 1 (n - 2 * p), j = (n - 2 * p).factorial := by
          rw [← Finset.prod_Ico_id_eq_factorial, show Finset.Ico 1 (n - 2 * p + 1) = Finset.Icc 1 (n - 2 * p) by ext x; simp; omega]
        rw [← Nat.cast_prod, hf2]
      rw [hw, hmid, htop]; ring
    have hne0 : (n.factorial / p ^ 2 : ZMod p) ≠ 0 := by
      rw [hmod_eq]
      have h2_ne : (2 : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp h0
        have := Nat.le_of_dvd (by norm_num) this; omega
      have hfac_ne : ((n - 2 * p).factorial : ZMod p) ≠ 0 := by
        intro h0
        have hdvd := (ZMod.natCast_zmod_eq_zero_iff_dvd (n - 2 * p).factorial p).mp h0
        have hle := hp.dvd_factorial.mp hdvd
        omega
      exact mul_ne_zero h2_ne hfac_ne
    exact ⟨hvp2, hp_Peven, hmod_eq, hne0⟩

/-! ### 5.3 Explicit `𝔽₂` Block Structure of `ℳ_n^{(1)}` and Rédei–Reichardt Cohomology -/

/-- Explicit `𝔽₂`-matrix `ℳ_n^{(1)}` on `𝒫_odd(n) ∩ [3, n]` with Audit Item 3 diagonal
`ℓ_{p_i}(-q_n / p_i)`. -/
def matrixM1 (n : ℕ) : Matrix ((Podd n).filter (3 ≤ ·)) ((Podd n).filter (3 ≤ ·)) (ZMod 2) :=
  fun p q =>
    if p = q then (if jacobiSym (-(qn n / p.1 : ℤ)) p.1 = 1 then 0 else 1)
    else (if jacobiSym (q.1 : ℤ) p.1 = 1 then 0 else 1)

/-- **Proposition 5.4** (Explicit `𝔽₂` block structure of `ℳ_n^{(1)}` and all-ones reciprocity duality,
with Audit Item 3 diagonal `-q_n / p_i`). -/
theorem prop_5_4 (n : ℕ) (hn : 8 ≤ n) :
    ∀ p ∈ (Podd n).filter (3 ≤ ·),
      (∑ q : (Podd n).filter (3 ≤ ·), matrixM1 n ⟨p, ‹_›⟩ q) =
        (if jacobiSym (-(2 ^ padicValNat 2 (qn n) : ℤ)) p = 1 then (0 : ZMod 2) else 1) ∧
      (2 ∣ padicValNat 2 n.factorial →
        (∑ q : (Podd n).filter (3 ≤ ·), matrixM1 n ⟨p, ‹_›⟩ q) =
          (if jacobiSym (-1 : ℤ) p = 1 then (0 : ZMod 2) else 1)) := by
  intro p hp
  have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
  have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2
  have hp_odd : p ≠ 2 := by omega
  have hp_Podd : p ∈ Podd n := (Finset.mem_filter.mp hp).1
  have hp_qn : p ∣ qn n := by rw [qn_eq_prod_Podd]; exact Finset.dvd_prod_of_mem _ hp_Podd
  set P3 := (Podd n).filter (3 ≤ ·)
  have h_ell_mul : ∀ a b : ℤ, jacobiSym a p = 1 ∨ jacobiSym a p = -1 →
      jacobiSym b p = 1 ∨ jacobiSym b p = -1 →
      (if jacobiSym (a * b) p = 1 then (0 : ZMod 2) else 1) =
        (if jacobiSym a p = 1 then (0 : ZMod 2) else 1) + (if jacobiSym b p = 1 then (0 : ZMod 2) else 1) := by
    intro a b ha hb
    rw [jacobiSym.mul_left]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide
  have h_ell_prod : ∀ (S : Finset P3) (f : P3 → ℤ),
      (∀ q ∈ S, jacobiSym (f q) p = 1 ∨ jacobiSym (f q) p = -1) →
      (∑ q ∈ S, (if jacobiSym (f q) p = 1 then (0 : ZMod 2) else 1)) =
        (if jacobiSym (∏ q ∈ S, f q) p = 1 then (0 : ZMod 2) else 1) := by
    intro S f hf
    classical
    induction S using Finset.induction_on with
    | empty => simp [jacobiSym.one_left]
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.prod_insert has]
      have ha := hf a (Finset.mem_insert_self _ _)
      have hs : ∀ q ∈ s, jacobiSym (f q) p = 1 ∨ jacobiSym (f q) p = -1 := fun q hq => hf q (Finset.mem_insert_of_mem hq)
      have hprod_pm : jacobiSym (∏ q ∈ s, f q) p = 1 ∨ jacobiSym (∏ q ∈ s, f q) p = -1 := by
        rw [jacobiSym.prod_left]
        clear ih
        induction s using Finset.induction_on with
        | empty => left; simp
        | @insert b t hbt iht =>
          rw [Finset.prod_insert hbt]
          rcases hs b (Finset.mem_insert_self _ _) with hb | hb <;>
            rcases iht (fun q hq => hs q (Finset.mem_insert_of_mem hq)) with ht | ht <;>
            [left; right; right; left] <;> rw [hb, ht] <;> norm_num
      rw [ih hs, ← h_ell_mul (f a) (∏ q ∈ s, f q) ha hprod_pm]
  let p_sub : P3 := ⟨p, hp⟩
  let f : P3 → ℤ := fun q => if q = p_sub then -(qn n / p : ℤ) else (q.1 : ℤ)
  have hf_pm : ∀ q ∈ (Finset.univ : Finset P3), jacobiSym (f q) p = 1 ∨ jacobiSym (f q) p = -1 := by
    intro q _
    dsimp only [f]
    split_ifs with hqp
    · have hndvd : ¬ p ∣ qn n / p := by
        intro hd
        have hp2 : p ^ 2 ∣ qn n := by
          have : qn n = p * (qn n / p) := (Nat.mul_div_cancel' hp_qn).symm
          rw [this]; rcases hd with ⟨t, ht⟩; exact ⟨t, by rw [ht]; ring⟩
        exact hp_pr.not_isUnit (squarefree_qn n p (by simpa [sq] using hp2))
      have hcop : IsCoprime (-(qn n / p : ℤ)) p := by
        rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_neg, Int.natAbs_natCast]
        exact (hp_pr.coprime_iff_not_dvd.mpr hndvd).symm
      exact sq_eq_one_iff.mp (jacobiSym.sq_one hcop)
    · have hq_pr : q.1.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp q.2).1).2.1
      have hne : q.1 ≠ p := fun h => hqp (Subtype.ext h)
      have hcop : IsCoprime (q.1 : ℤ) p := by
        rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
        exact (Nat.coprime_primes hq_pr hp_pr).mpr hne
      exact sq_eq_one_iff.mp (jacobiSym.sq_one hcop)
  have hsum_f : (∑ q : P3, matrixM1 n p_sub q) =
      ∑ q ∈ (Finset.univ : Finset P3), (if jacobiSym (f q) p = 1 then (0 : ZMod 2) else 1) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold matrixM1; dsimp only [f]
    by_cases hqp : q = p_sub
    · rw [if_pos hqp.symm, if_pos hqp]; rfl
    · rw [if_neg (Ne.symm hqp), if_neg hqp]
  rw [hsum_f, h_ell_prod Finset.univ f hf_pm]
  -- Evaluate `∏ q ∈ univ, f q`:
  have hprod_f : (∏ q ∈ (Finset.univ : Finset P3), f q) =
      -(qn n / p : ℤ) * ∏ q ∈ (Finset.univ.erase p_sub : Finset P3), (q.1 : ℤ) := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ p_sub)]
    congr 1
    · dsimp only [f]; rw [if_pos rfl]
    · refine Finset.prod_congr rfl fun q hq => ?_
      dsimp only [f]; rw [if_neg (Finset.mem_erase.mp hq).1]
  -- Note `qn n = 2 ^ v₂(qn n) * p * ∏ q ∈ univ.erase p_sub, q.1`:
  set Rprod : ℕ := ∏ q ∈ (Finset.univ.erase p_sub : Finset P3), q.1
  have hqn_decomp : qn n = 2 ^ padicValNat 2 (qn n) * (p * Rprod) := by
    have h1 : qn n = 2 ^ padicValNat 2 (qn n) * oddPart (qn n) := by
      unfold oddPart; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have hodd_eq : oddPart (qn n) = ∏ q ∈ P3, q := by
      have hPodd_eq : (∏ q ∈ P3, q) = ∏ q ∈ (Podd n).filter (3 ≤ ·), q := rfl
      have h_qn_prod := qn_eq_prod_Podd n
      by_cases h2 : 2 ∈ Podd n
      · have hv2 : padicValNat 2 (qn n) = 1 := by
          haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
          rw [h_qn_prod]
          have h1' : (2 : ℕ) ^ 1 ∣ ∏ q ∈ Podd n, q := by simpa using Finset.dvd_prod_of_mem _ h2
          have h2' : ¬ 2 ^ 2 ∣ qn n := fun h => (by decide : ¬ IsUnit 2) (squarefree_qn n 2 (by simpa [sq] using h))
          have hge := (padicValNat_dvd_iff_le (qn_pos n).ne').mp (h_qn_prod ▸ h1')
          have hlt : padicValNat 2 (qn n) < 2 := by
            by_contra hge2; push_neg at hge2
            exact h2' ((padicValNat_dvd_iff_le (qn_pos n).ne').mpr hge2)
          omega
        have herase : (Podd n).erase 2 = P3 := by
          ext q; simp only [Finset.mem_erase, Finset.mem_filter, P3]
          constructor
          · rintro ⟨hq2, hq⟩; exact ⟨hq, by have := (Finset.mem_filter.mp hq).2.1.two_le; omega⟩
          · rintro ⟨hq, hq3⟩; exact ⟨by omega, hq⟩
        have hmul2 : 2 * ∏ q ∈ P3, q = qn n := by
          rw [← herase, Finset.mul_prod_erase _ _ h2, ← h_qn_prod]
        have h1' := h1; rw [hv2, pow_one] at h1'
        linarith
      · have hv2 : padicValNat 2 (qn n) = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          rw [h_qn_prod, Nat.Prime.dvd_finset_prod_iff (by decide)]
          rintro ⟨q, hq, h2q⟩
          have hq_pr := (Finset.mem_filter.mp hq).2.1
          have : 2 = q := (Nat.prime_dvd_prime_iff_eq (by decide) hq_pr).mp h2q
          subst this; exact h2 hq
        have hP3_eq : P3 = Podd n := by
          ext q; simp only [Finset.mem_filter, P3]
          constructor
          · exact fun h => h.1
          · intro hq; have : q ≠ 2 := fun h => h2 (h ▸ hq); exact ⟨hq, by have := (Finset.mem_filter.mp hq).2.1.two_le; omega⟩
        rw [hv2, pow_zero, one_mul] at h1
        rw [← h1, hP3_eq, ← h_qn_prod]
    have hP3_prod : (∏ q ∈ P3, q) = p * Rprod := by
      have h1 : (∏ q ∈ (Finset.univ : Finset P3), q.1) = ∏ q ∈ P3, q :=
        Finset.prod_coe_sort P3 id
      rw [← h1, ← Finset.mul_prod_erase Finset.univ (fun q : P3 => q.1) (Finset.mem_univ p_sub)]
    rw [h1, hodd_eq, hP3_prod]
  have hqn_div : qn n / p = 2 ^ padicValNat 2 (qn n) * Rprod := by
    rw [hqn_decomp, mul_comm p Rprod, ← mul_assoc, Nat.mul_div_cancel _ hp_pr.pos]
  have hR_cop : IsCoprime (Rprod : ℤ) p := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
    refine Nat.Coprime.prod_left fun q hq => ?_
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp q.2).1).2.1
    have hne : q.1 ≠ p := fun h => (Finset.mem_erase.mp hq).1 (Subtype.ext h)
    exact (Nat.coprime_primes hq_pr hp_pr).mpr hne
  have hprod_R : (∏ q ∈ (Finset.univ.erase p_sub : Finset P3), (q.1 : ℤ)) = (Rprod : ℤ) := by
    rw [Nat.cast_prod]
  have hjac_main : jacobiSym (∏ q ∈ (Finset.univ : Finset P3), f q) p =
      jacobiSym (-(2 ^ padicValNat 2 (qn n) : ℤ)) p := by
    rw [hprod_f, hprod_R, hqn_div, Nat.cast_mul, Nat.cast_pow,
      show -(2 ^ padicValNat 2 (qn n) * (Rprod : ℤ)) * (Rprod : ℤ) =
        -(2 ^ padicValNat 2 (qn n) : ℤ) * (Rprod : ℤ) ^ 2 by ring,
      jacobiSym.mul_left, jacobiSym.sq_one hR_cop, mul_one]
  refine ⟨by rw [hjac_main]; simp, fun hev2 => ?_⟩
  have hv2_zero : padicValNat 2 (qn n) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [qn_eq_prod_Podd, Nat.Prime.dvd_finset_prod_iff (by decide)]
    rintro ⟨q, hq, h2q⟩
    have hq_pr := (Finset.mem_filter.mp hq).2.1
    have : 2 = q := (Nat.prime_dvd_prime_iff_eq (by decide) hq_pr).mp h2q
    subst this
    exact (Finset.mem_filter.mp hq).2.2 hev2
  rw [hjac_main, hv2_zero, pow_zero]
  simp

/-- **Theorem 5.5(i)** (Galois cohomology / Rédei–Reichardt 4-rank identity for `ℚ(√q_n)`). -/
theorem theorem_5_5_i (n : ℕ) (hn : 4 ≤ n) (hn6 : n ≠ 6) :
    let D : ℕ := (fundDiscrQuad (qn n : ℤ)).natAbs
    ∃ (rank4_Cl_plus rank2_A2 card_A2 card_Cl_odd : ℕ) (exp_A2 : ℕ),
      card_A2 * card_Cl_odd = 2 * NumberField.classNumber (QuadField (qn n : ℚ)) ∧
      rank2_A2 = omegaNat D - 1 ∧
      2 ^ rank2_A2 ≤ card_A2 ∧
      card_A2 ≤ exp_A2 ^ rank2_A2 ∧
      rank4_Cl_plus ≤ rank2_A2 := by
  have hqn1 : 1 < qn n := by
    obtain ⟨p, hp, hpdvd, _⟩ := (lemma_3_1_i n (by omega) hn6).1
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (qn_pos n) hpdvd)
  haveI : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) hn6⟩
  exact hasse_gauss_redei_reichardt (qn n) (squarefree_qn n) hqn1

/-- **Theorem 5.5(ii)** (Deterministic `𝒫_even^-(n)`-absorption and reduced dual quartic laws). -/
theorem theorem_5_5_ii (n m : ℕ) (hn : 8 ≤ n) (hsol : IsBrocardSol n m) :
    let u1 := (m - 1) / 2
    let u2 := (m + 1) / 2
    let w1 := padicValNat 2 u1
    let w2 := padicValNat 2 u2
    (∀ p ∈ (Podd n).filter (3 ≤ ·), p ∣ B1sol n m →
      jacobiSym (Z2starSol n m : ℤ) p ^ 2 = 1 ∧
      jacobiSym (2 ^ w2 * (B2sol n m : ℤ)) p = 1 ∧
      jacobiSym (u2 : ℤ) p = 1) ∧
    (∀ p ∈ (Podd n).filter (3 ≤ ·), p ∣ B2sol n m →
      jacobiSym (Z1starSol n m : ℤ) p ^ 2 = 1 ∧
      jacobiSym (-(2 ^ w1 * (B1sol n m : ℤ))) p = 1 ∧
      jacobiSym (-(u1 : ℤ)) p = 1) := by
  dsimp only
  obtain ⟨_, _, hu2_eq, hu1_pos, hu2_pos, _, hcop⟩ := brocard_sol_u1_u2 (by omega) hsol
  obtain ⟨_, _, hu1_eq, hu2_eqR, _⟩ := brocard_B_Z_prod_eq (by omega) hsol
  have h53 := lemma_5_3_i n m hn hsol
  set u1 := (m - 1) / 2
  set u2 := (m + 1) / 2
  set w1 := padicValNat 2 u1
  set w2 := padicValNat 2 u2
  have hu1_nat : u1 = 2 ^ w1 * B1sol n m * Z1starSol n m ^ 2 := by exact_mod_cast hu1_eq
  have hu2_nat : u2 = 2 ^ w2 * B2sol n m * Z2starSol n m ^ 2 := by exact_mod_cast hu2_eqR
  refine ⟨?_, ?_⟩
  · intro p hp hpB1
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have hpu1 : p ∣ u1 := dvd_trans hpB1 (by rw [hu1_nat]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    have hnpu2 : ¬ p ∣ u2 := fun h => hp_pr.not_dvd_one (hcop ▸ Nat.dvd_gcd hpu1 h)
    have hnp_Z2 : ¬ p ∣ Z2starSol n m := fun h =>
      hnpu2 (by rw [hu2_nat]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
    have hcop_Z2 : IsCoprime (Z2starSol n m : ℤ) p := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
      exact hp_pr.coprime_iff_not_dvd.mpr hnp_Z2 |>.symm
    have hsq1 : jacobiSym (Z2starSol n m : ℤ) p ^ 2 = 1 := jacobiSym.sq_one hcop_Z2
    have h53_1 := (h53.1 p hp hpB1).2
    have hu2_jac : jacobiSym (u2 : ℤ) p = 1 := by
      rw [hu2_nat, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        jacobiSym.mul_left, h53_1, one_mul, jacobiSym.sq_one hcop_Z2]
    exact ⟨hsq1, h53_1, hu2_jac⟩
  · intro p hp hpB2
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have hpu2 : p ∣ u2 := dvd_trans hpB2 (by rw [hu2_nat]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    have hnpu1 : ¬ p ∣ u1 := fun h => hp_pr.not_dvd_one (hcop ▸ Nat.dvd_gcd h hpu2)
    have hnp_Z1 : ¬ p ∣ Z1starSol n m := fun h =>
      hnpu1 (by rw [hu1_nat]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
    have hcop_Z1 : IsCoprime (Z1starSol n m : ℤ) p := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
      exact hp_pr.coprime_iff_not_dvd.mpr hnp_Z1 |>.symm
    have hsq1 : jacobiSym (Z1starSol n m : ℤ) p ^ 2 = 1 := jacobiSym.sq_one hcop_Z1
    have h53_2 := (h53.2 p hp hpB2).2
    have hu1_jac : jacobiSym (-(u1 : ℤ)) p = 1 := by
      rw [hu1_nat, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        neg_mul, jacobiSym.mul_left, h53_2, one_mul, jacobiSym.sq_one hcop_Z1]
    exact ⟨hsq1, h53_2, hu1_jac⟩

end BrocardFormalization

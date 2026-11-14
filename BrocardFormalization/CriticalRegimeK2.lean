/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParity
import BrocardFormalization.PellAndIwasawa
import Mathlib.NumberTheory.Wilson

/-!
# Section 4: Arithmetic Structure of the Critical Regime `k = 2`

This module formalizes Section 4 of the manuscript:
* Equations (4.1)–(4.3): Three-consecutive-integer factorization `n! = 4 (X₁ - 1) X₁^2 (X₁ + 1)`.
* `prop_4_1`: `(n/2)`-smoothness of `m + 1`, biquadratic splitting, and Fermat-quotient lock.
* `theorem_4_2_i`, `theorem_4_2_ii`, `theorem_4_2_iii`: Two-stage Euclidean division quartic laws
  and stretched-exponential lower bounds `exp(n^{1/2 - o(1)})` on midpoint cores `δ₁(n), δ₂(n)`.
* `lemma_4_3`: Stickelberger's `p`-adic factorial congruence.
* `theorem_4_4_i`, `theorem_4_4_ii`: Stickelberger base-`p` reciprocity, inert absorption,
  and conductor-free quadratic residue lock on `core(Z)`.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### Local Helpers for Fermat Quotients and `p`-adic Valuations -/

private lemma k2_fermatQuot_congr {p : ℕ} (hp : p.Prime) {a b : ℤ}
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
  obtain ⟨q, hq⟩ := hdvd
  have h1 : a ^ (p - 1) - 1 = (b ^ (p - 1) - 1) + q * (p : ℤ) * (p : ℤ) := by linarith
  rw [h1, Int.add_mul_ediv_right _ _ hpZ]
  push_cast
  simp [ZMod.natCast_self]

private lemma k2_fermatQuot_mul {p : ℕ} (hp : p.Prime) {a b : ℤ}
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

private lemma k2_fermatQuot_one (p : ℕ) (hp : p.Prime) : fermatQuot p 1 = 0 := by
  unfold fermatQuot
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp [hpZ]

private lemma padicValNat_prod_pow {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (f : ℕ → ℕ)
    {p : ℕ} (hp : p.Prime) :
    padicValNat p (∏ q ∈ S, q ^ f q) = if p ∈ S then f p else 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  induction S using Finset.induction with
  | empty => simp
  | @insert q s hqs ih =>
    have hq : q.Prime := hS q (Finset.mem_insert_self q s)
    have hs : ∀ r ∈ s, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hqs]
    have hq0 : q ^ f q ≠ 0 := pow_ne_zero _ hq.ne_zero
    have hs0 : (∏ r ∈ s, r ^ f r) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun r hr => pow_ne_zero _ (hs r hr).ne_zero
    rw [padicValNat.mul hq0 hs0, padicValNat.pow q (f q), padicValNat_primes_self_or_zero hp hq, ih hs]
    · by_cases hpq : p = q
      · subst hpq; simp [hqs]
      · simp [hpq]
where
  padicValNat_primes_self_or_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
      padicValNat p q = if p = q then 1 else 0 := by
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hpq : p = q
    · subst hpq; simp [padicValNat.self hp.one_lt]
    · have hndvd : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
      simp [hpq, padicValNat.eq_zero_of_not_dvd hndvd]

private lemma prod_filter_prime_dvd_eq {A : ℕ} (hA : A ≠ 0) {S : Finset ℕ}
    (hS_prime : ∀ p ∈ S, p.Prime)
    (hA_supp : ∀ p : ℕ, p.Prime → p ∣ A → p ∈ S) :
    ∏ p ∈ S, p ^ padicValNat p A = A := by
  have h1 : A = ∏ p ∈ A.primeFactors, p ^ A.factorization p :=
    (Nat.prod_primeFactors_pow_factorization hA).symm
  have hsub : A.primeFactors ⊆ S := by
    intro p hp
    exact hA_supp p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have heq : ∏ p ∈ S, p ^ padicValNat p A = ∏ p ∈ A.primeFactors, p ^ A.factorization p := by
    rw [← Finset.prod_subset hsub]
    · refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def A (Nat.prime_of_mem_primeFactors hp)]
    · intro p hp hnot
      have hp_prime : p.Prime := hS_prime p hp
      have hndvd : ¬ p ∣ A := fun hdvd =>
        hnot (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hA⟩)
      rw [padicValNat.eq_zero_of_not_dvd hndvd, pow_zero]
  exact heq.trans h1.symm

/-! ### 4.1 Three-Consecutive-Integer Decomposition and Two-Stage Quartic Law -/

theorem critical_eqs_4_1_to_4_3 (n m : ℕ) (hn : 4 ≤ n) (hn6 : n ≠ 6)
    (hsol : IsBrocardSol n m) (hk2 : pellIndex hn hsol = 2) :
    let x1 := X1 n (by omega) hn6
    let y1 := Y1 n (by omega) hn6
    m = x1 ^ 2 + qn n * y1 ^ 2 ∧
    m = 2 * x1 ^ 2 - 1 ∧
    m = 2 * qn n * y1 ^ 2 + 1 ∧
    sn n = 2 * x1 * y1 ∧
    m + 1 = 2 * x1 ^ 2 ∧
    m - 1 = 2 * (x1 - 1) * (x1 + 1) ∧
    n.factorial = 4 * (x1 - 1) * x1 ^ 2 * (x1 + 1) := by
  dsimp only
  set x1 := X1 n (by omega) hn6
  set y1 := Y1 n (by omega) hn6
  obtain ⟨_, _, hmZ, hsnZ⟩ := pellIndex_spec hn hsol
  rw [hk2] at hmZ hsnZ
  have h_pell1 : (x1 : ℤ) ^ 2 - (qn n : ℤ) * (y1 : ℤ) ^ 2 = 1 :=
    (pellFundUnit (by omega : 3 ≤ n) hn6).prop
  have hx2 : (Xr n (by omega) hn6 2 : ℤ) = (x1 : ℤ) ^ 2 + (qn n : ℤ) * (y1 : ℤ) ^ 2 := by
    have hrec := pell_x_succ_succ (by omega : 3 ≤ n) hn6 0
    have hx0 : (Xr n (by omega) hn6 0 : ℤ) = 1 := by simp [Xr, pellFundUnit]
    have hx1 : (Xr n (by omega) hn6 1 : ℤ) = (x1 : ℤ) := by simp [Xr, X1]
    linarith
  have hy2 : (Yr n (by omega) hn6 2 : ℤ) = 2 * (x1 : ℤ) * (y1 : ℤ) := by
    have hrec := pell_y_succ_succ (by omega : 3 ≤ n) hn6 0
    have hy0 : (Yr n (by omega) hn6 0 : ℤ) = 0 := by simp [Yr, pellFundUnit]
    have hy1 : (Yr n (by omega) hn6 1 : ℤ) = (y1 : ℤ) := by simp [Yr, Y1]
    linarith
  have hm_eq1 : (m : ℤ) = (x1 : ℤ) ^ 2 + (qn n : ℤ) * (y1 : ℤ) ^ 2 := by linarith
  have hm_eq2 : (m : ℤ) = 2 * (x1 : ℤ) ^ 2 - 1 := by linarith
  have hm_eq3 : (m : ℤ) = 2 * (qn n : ℤ) * (y1 : ℤ) ^ 2 + 1 := by linarith
  have hsn_eq : (sn n : ℤ) = 2 * (x1 : ℤ) * (y1 : ℤ) := by linarith
  have hx1_pos : 1 ≤ x1 := by
    have : (1 : ℤ) ≤ (x1 : ℤ) ^ 2 := by nlinarith [sq_nonneg (y1 : ℤ), qn_pos n]
    nlinarith
  have hm_1 : m = x1 ^ 2 + qn n * y1 ^ 2 := by exact_mod_cast hm_eq1
  have hm_2 : m = 2 * x1 ^ 2 - 1 := by
    have : (m : ℤ) + 1 = 2 * (x1 : ℤ) ^ 2 := by linarith
    have : m + 1 = 2 * x1 ^ 2 := by exact_mod_cast this
    omega
  have hm_3 : m = 2 * qn n * y1 ^ 2 + 1 := by exact_mod_cast hm_eq3
  have hsn_4 : sn n = 2 * x1 * y1 := by exact_mod_cast hsn_eq
  have hm_plus : m + 1 = 2 * x1 ^ 2 := by omega
  have hm_minus : m - 1 = 2 * (x1 - 1) * (x1 + 1) := by
    zify [show 1 ≤ m by omega, hx1_pos]
    linarith
  have hfac : n.factorial = 4 * (x1 - 1) * x1 ^ 2 * (x1 + 1) := by
    have hbro := hsol.2.2
    zify [hx1_pos]
    have : (n.factorial : ℤ) = (m : ℤ) ^ 2 - 1 := by linarith
    rw [this, hm_eq2]
    ring
  exact ⟨hm_1, hm_2, hm_3, hsn_4, hm_plus, hm_minus, hfac⟩

theorem prop_4_1 (n m : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6)
    (hsol : IsBrocardSol n m) (hk2 : pellIndex (by omega) hsol = 2) :
    let x1 := X1 n (by omega) hn6
    let y1 := Y1 n (by omega) hn6
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ n →
      (p ∣ x1 - 1 → ¬ p ∣ x1 ∧ ¬ p ∣ x1 + 1) ∧
      (p ∣ x1 → ¬ p ∣ x1 - 1 ∧ ¬ p ∣ x1 + 1) ∧
      (p ∣ x1 + 1 → ¬ p ∣ x1 - 1 ∧ ¬ p ∣ x1)) ∧
    (∀ p ∈ Podd n, 3 ≤ p →
      p ^ padicValNat p n.factorial ∣ qn n * y1 ^ 2 ∧
      padicValNat p (qn n * y1 ^ 2) = padicValNat p n.factorial) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ x1 →
      p ∈ Peven n ∧
      padicValNat p x1 = padicValNat p n.factorial / 2 ∧
      2 * padicValNat p x1 = padicValNat p n.factorial ∧
      (p : ℝ) ≤ (n : ℝ) / 2) ∧
    (∀ p : ℕ, p.Prime → p ∣ m + 1 → (p : ℝ) ≤ (n : ℝ) / 2) ∧
    (∀ δ₁ δ₂ uₙ vₙ : ℕ, Squarefree δ₁ → Squarefree δ₂ →
      x1 - 1 = δ₁ * uₙ ^ 2 → x1 + 1 = δ₂ * vₙ ^ 2 →
      ∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ x1 →
        jacobiSym (-(δ₁ : ℤ)) p = 1 ∧
        jacobiSym (δ₂ : ℤ) p = 1 ∧
        jacobiSym (-(qn n : ℤ)) p = 1 ∧
        ((qn n : ℤ) * (y1 : ℤ) ^ 2 : ZMod (p ^ padicValNat p n.factorial)) = -1 ∧
        fermatQuot p (-(qn n : ℤ)) + 2 * fermatQuot p (y1 : ℤ) = 0) := by
  dsimp only
  set x1 := X1 n (by omega) hn6
  set y1 := Y1 n (by omega) hn6
  obtain ⟨_, _, _, _, hm_plus, _, hfac⟩ := critical_eqs_4_1_to_4_3 n m (by omega) hn6 hsol hk2
  have hx1_pos : 1 ≤ x1 := by
    have : 0 < 2 * x1 ^ 2 := by omega
    nlinarith
  have hqy_eq : qn n * y1 ^ 2 = (x1 - 1) * (x1 + 1) := by
    have h1 : (x1 : ℤ) ^ 2 - (qn n : ℤ) * (y1 : ℤ) ^ 2 = 1 :=
      (pellFundUnit (by omega : 3 ≤ n) hn6).prop
    zify [hx1_pos]
    linarith
  have hfac_qy : n.factorial = 4 * (qn n * y1 ^ 2) * x1 ^ 2 := by
    rw [hfac, hqy_eq]; ring
  have hpair : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ n →
      (p ∣ x1 - 1 → ¬ p ∣ x1 ∧ ¬ p ∣ x1 + 1) ∧
      (p ∣ x1 → ¬ p ∣ x1 - 1 ∧ ¬ p ∣ x1 + 1) ∧
      (p ∣ x1 + 1 → ¬ p ∣ x1 - 1 ∧ ¬ p ∣ x1) := by
    intro p hp hp3 _
    refine ⟨fun h => ⟨fun h1 => ?_, fun h2 => ?_⟩,
            fun h => ⟨fun h1 => ?_, fun h2 => ?_⟩,
            fun h => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
    · have : p ∣ x1 - (x1 - 1) := Nat.dvd_sub h1 h
      rw [show x1 - (x1 - 1) = 1 by omega] at this
      exact hp.not_dvd_one this
    · have : p ∣ (x1 + 1) - (x1 - 1) := Nat.dvd_sub h2 h
      rw [show (x1 + 1) - (x1 - 1) = 2 by omega] at this
      have := Nat.le_of_dvd (by norm_num) this; omega
    · have : p ∣ x1 - (x1 - 1) := Nat.dvd_sub h h1
      rw [show x1 - (x1 - 1) = 1 by omega] at this
      exact hp.not_dvd_one this
    · have : p ∣ (x1 + 1) - x1 := Nat.dvd_sub h2 h
      rw [show (x1 + 1) - x1 = 1 by omega] at this
      exact hp.not_dvd_one this
    · have : p ∣ (x1 + 1) - (x1 - 1) := Nat.dvd_sub h h1
      rw [show (x1 + 1) - (x1 - 1) = 2 by omega] at this
      have := Nat.le_of_dvd (by norm_num) this; omega
    · have : p ∣ (x1 + 1) - x1 := Nat.dvd_sub h h2
      rw [show (x1 + 1) - x1 = 1 by omega] at this
      exact hp.not_dvd_one this
  have hpart2 : ∀ p ∈ Podd n, 3 ≤ p →
      p ^ padicValNat p n.factorial ∣ qn n * y1 ^ 2 ∧
      padicValNat p (qn n * y1 ^ 2) = padicValNat p n.factorial := by
    intro p hp hp3
    have hp_mem := Finset.mem_filter.mp hp
    have hp_prime : p.Prime := hp_mem.2.1
    have hodd : ¬ 2 ∣ padicValNat p n.factorial := hp_mem.2.2
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have hqy_ne : qn n * y1 ^ 2 ≠ 0 := mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos (by omega) hn6).ne')
    have hv_fac : padicValNat p n.factorial =
        padicValNat p 4 + padicValNat p (qn n * y1 ^ 2) + 2 * padicValNat p x1 := by
      conv_lhs => rw [hfac_qy]
      rw [padicValNat.mul (mul_ne_zero (by norm_num) hqy_ne) (pow_ne_zero 2 hx1_pos.ne'),
        padicValNat.mul (by norm_num) hqy_ne, padicValNat.pow x1 2]
    have hv4 : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    rw [hv4, zero_add] at hv_fac
    have hndvd_x1 : ¬ p ∣ x1 := by
      intro hpx
      have hcop : ¬ p ∣ qn n * y1 ^ 2 := by
        rw [hqy_eq]
        intro hd
        rcases hp_prime.dvd_mul.mp hd with h1 | h2
        · exact (hpair p hp_prime hp3 (Finset.mem_Icc.mp hp_mem.1).2).2.1 hpx |>.1 h1
        · exact (hpair p hp_prime hp3 (Finset.mem_Icc.mp hp_mem.1).2).2.1 hpx |>.2 h2
      rw [padicValNat.eq_zero_of_not_dvd hcop, zero_add] at hv_fac
      exact hodd ⟨padicValNat p x1, hv_fac⟩
    rw [padicValNat.eq_zero_of_not_dvd hndvd_x1, mul_zero, add_zero] at hv_fac
    refine ⟨?_, hv_fac.symm⟩
    rw [hv_fac]
    exact padicValNat_dvd_iff_le hqy_ne |>.mpr le_rfl
  have hpart3 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ x1 →
      p ∈ Peven n ∧
      padicValNat p x1 = padicValNat p n.factorial / 2 ∧
      2 * padicValNat p x1 = padicValNat p n.factorial ∧
      (p : ℝ) ≤ (n : ℝ) / 2 := by
    intro p hp hp3 hpx
    haveI : Fact p.Prime := ⟨hp⟩
    have hpn : p ≤ n := hp.dvd_factorial.mp (dvd_trans (dvd_trans (dvd_pow_self x1 (by norm_num))
      (by rw [hfac]; exact dvd_mul_right _ _)) (dvd_mul_right _ _))
    have hndvd_qy : ¬ p ∣ qn n * y1 ^ 2 := by
      rw [hqy_eq]
      intro hd
      rcases hp.dvd_mul.mp hd with h1 | h2
      · exact (hpair p hp hp3 hpn).2.1 hpx |>.1 h1
      · exact (hpair p hp hp3 hpn).2.1 hpx |>.2 h2
    have hqy_ne : qn n * y1 ^ 2 ≠ 0 := mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 (Y1_pos (by omega) hn6).ne')
    have hv_fac : padicValNat p n.factorial = 2 * padicValNat p x1 := by
      conv_lhs => rw [hfac_qy]
      rw [padicValNat.mul (mul_ne_zero (by norm_num) hqy_ne) (pow_ne_zero 2 hx1_pos.ne'),
        padicValNat.mul (by norm_num) hqy_ne,
        padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega),
        padicValNat.eq_zero_of_not_dvd hndvd_qy, padicValNat.pow x1 2]
      ring
    have heven : p ∈ Peven n :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpn⟩, hp, ⟨padicValNat p x1, hv_fac⟩⟩
    have hvx1_pos : 1 ≤ padicValNat p x1 := one_le_padicValNat_of_dvd hx1_pos.ne' hpx
    have hvp_ge2 : 2 ≤ padicValNat p n.factorial := by omega
    have hp_le_n2 : 2 * p ≤ n := by
      by_contra hlt
      push_neg at hlt
      have hnsq : n < p ^ 2 := by nlinarith
      have hv1 : padicValNat p n.factorial = n / p := by
        have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow (by omega) hnsq
        rw [padicValNat_factorial hlog]
        have hico : Finset.Ico 1 2 = {1} := by decide
        rw [hico, Finset.sum_singleton, pow_one]
      have hdiv : n / p ≤ 1 := Nat.div_lt_iff_lt_mul hp.pos |>.mpr (by linarith) |> Nat.lt_succ_iff.mp
      omega
    refine ⟨heven, by omega, hv_fac.symm, ?_⟩
    have : (2 * p : ℝ) ≤ n := by exact_mod_cast hp_le_n2
    linarith
  have hpart4 : ∀ p : ℕ, p.Prime → p ∣ m + 1 → (p : ℝ) ≤ (n : ℝ) / 2 := by
    intro p hp hpm
    rw [hm_plus] at hpm
    rcases hp.dvd_mul.mp hpm with h2 | hx
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst hp2
      have : (8 : ℝ) ≤ n := by exact_mod_cast hn
      norm_num; linarith
    · have hpx1 : p ∣ x1 := hp.dvd_of_dvd_pow hx
      rcases hp.eq_two_or_odd with rfl | hodd
      · have : (8 : ℝ) ≤ n := by exact_mod_cast hn
        norm_num; linarith
      · exact (hpart3 p hp (by omega) hpx1).2.2.2
  refine ⟨hpair, hpart2, hpart3, hpart4, ?_⟩
  intro δ₁ δ₂ uₙ vₙ _ _ hδ₁ hδ₂ p hp hp3 hpx
  haveI : Fact p.Prime := ⟨hp⟩
  have hpx_Z : (p : ℤ) ∣ (x1 : ℤ) := by exact_mod_cast hpx
  have h1_mod : ((x1 - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hx1_pos, Nat.cast_one]
    have hx_mod : (x1 : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd x1 p).mpr hpx
    rw [hx_mod, zero_sub]
  have h2_mod : ((x1 + 1 : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    have hx_mod : (x1 : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd x1 p).mpr hpx
    rw [hx_mod, zero_add]
  have hpu : ¬ (p : ℤ) ∣ (uₙ : ℤ) := by
    intro h
    have hpu_N : p ∣ uₙ := by exact_mod_cast h
    have hpdvd : p ∣ x1 - 1 := by rw [hδ₁]; exact dvd_mul_of_dvd_right (dvd_pow hpu_N (by norm_num)) _
    have hpn : p ≤ n := (hpart3 p hp hp3 hpx).1 |> Finset.mem_filter.mp |>.1 |> Finset.mem_Icc.mp |>.2
    exact (hpair p hp hp3 hpn).2.1 hpx |>.1 hpdvd
  have hpv : ¬ (p : ℤ) ∣ (vₙ : ℤ) := by
    intro h
    have hpv_N : p ∣ vₙ := by exact_mod_cast h
    have hpdvd : p ∣ x1 + 1 := by rw [hδ₂]; exact dvd_mul_of_dvd_right (dvd_pow hpv_N (by norm_num)) _
    have hpn : p ≤ n := (hpart3 p hp hp3 hpx).1 |> Finset.mem_filter.mp |>.1 |> Finset.mem_Icc.mp |>.2
    exact (hpair p hp hp3 hpn).2.1 hpx |>.2 hpdvd
  have hjac_d1 : jacobiSym (-(δ₁ : ℤ)) p = 1 := by
    have hmod_eq : (-(δ₁ : ℤ) * (uₙ : ℤ) ^ 2 : ZMod p) = 1 := by
      have : ((x1 - 1 : ℕ) : ZMod p) = ((δ₁ * uₙ ^ 2 : ℕ) : ZMod p) := by rw [hδ₁]
      rw [h1_mod] at this
      push_cast at this ⊢
      linear_combination -this
    have h1 : ((-(δ₁ : ℤ) * (uₙ : ℤ) ^ 2 : ℤ) : ZMod p) = (1 : ℤ) := by push_cast; exact hmod_eq
    rw [ZMod.intCast_eq_intCast_iff] at h1
    have h2 := jacobiSym.mod_left (-(δ₁ : ℤ) * (uₙ : ℤ) ^ 2) p
    have h3 := jacobiSym.mod_left (1 : ℤ) p
    rw [Int.ModEq.symm h1] at h3
    have hjac_sq : jacobiSym (-(δ₁ : ℤ) * (uₙ : ℤ) ^ 2) p = 1 := by
      rw [← h2, h3]; simp [jacobiSym.one_left]
    rw [jacobiSym.mul_left, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr (by exact_mod_cast hpu)).symm, mul_one] at hjac_sq
    exact hjac_sq
  have hjac_d2 : jacobiSym (δ₂ : ℤ) p = 1 := by
    have hmod_eq : ((δ₂ : ℤ) * (vₙ : ℤ) ^ 2 : ZMod p) = 1 := by
      have : ((x1 + 1 : ℕ) : ZMod p) = ((δ₂ * vₙ ^ 2 : ℕ) : ZMod p) := by rw [hδ₂]
      rw [h2_mod] at this
      push_cast at this ⊢
      exact this.symm
    have h1 : (((δ₂ : ℤ) * (vₙ : ℤ) ^ 2 : ℤ) : ZMod p) = (1 : ℤ) := by push_cast; exact hmod_eq
    rw [ZMod.intCast_eq_intCast_iff] at h1
    have h2 := jacobiSym.mod_left ((δ₂ : ℤ) * (vₙ : ℤ) ^ 2) p
    have h3 := jacobiSym.mod_left (1 : ℤ) p
    rw [Int.ModEq.symm h1] at h3
    have hjac_sq : jacobiSym ((δ₂ : ℤ) * (vₙ : ℤ) ^ 2) p = 1 := by
      rw [← h2, h3]; simp [jacobiSym.one_left]
    rw [jacobiSym.mul_left, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr (by exact_mod_cast hpv)).symm, mul_one] at hjac_sq
    exact hjac_sq
  have hpow_fac : p ^ padicValNat p n.factorial ∣ x1 ^ 2 := by
    have hvf := (hpart3 p hp hp3 hpx).2.2.1
    rw [← hvf, pow_mul]
    exact pow_dvd_pow_of_dvd (pow_padicValNat_dvd) 2
  have hcongr_fac : (p : ℤ) ^ padicValNat p n.factorial ∣ (qn n : ℤ) * (y1 : ℤ) ^ 2 + 1 := by
    have h1 : (qn n : ℤ) * (y1 : ℤ) ^ 2 + 1 = (x1 : ℤ) ^ 2 := by
      have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; linarith
    rw [h1]; exact_mod_cast hpow_fac
  have hqy_zmod : ((qn n : ℤ) * (y1 : ℤ) ^ 2 : ZMod (p ^ padicValNat p n.factorial)) = -1 := by
    rw [← eq_sub_iff_add_eq', sub_neg_eq_add]
    have : ((qn n : ℤ) * (y1 : ℤ) ^ 2 + 1 : ZMod (p ^ padicValNat p n.factorial)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hcongr_fac)
    simpa using this
  have hpy1 : ¬ (p : ℤ) ∣ (y1 : ℤ) := by
    intro h
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by
      have : (1 : ℤ) = (x1 : ℤ) ^ 2 - (qn n : ℤ) * (y1 : ℤ) ^ 2 := by
        have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; linarith
      rw [this]
      exact dvd_sub (dvd_pow hpx_Z (by norm_num)) (dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
    have := Int.le_of_dvd (by norm_num) h1; omega
  have hjac_qn : jacobiSym (-(qn n : ℤ)) p = 1 := by
    have hcongr_p : (p : ℤ) ∣ -(qn n : ℤ) * (y1 : ℤ) ^ 2 - 1 := by
      have h1 := dvd_trans (dvd_pow_self (p : ℤ) (by
        have := (hpart3 p hp hp3 hpx).2.2.1
        have := one_le_padicValNat_of_dvd hx1_pos.ne' hpx; omega)) hcongr_fac
      simpa [show -(qn n : ℤ) * (y1 : ℤ) ^ 2 - 1 = -((qn n : ℤ) * (y1 : ℤ) ^ 2 + 1) by ring] using dvd_neg.mpr h1
    have h1 : ((-(qn n : ℤ) * (y1 : ℤ) ^ 2 : ℤ) : ZMod p) = (1 : ℤ) := by
      rw [ZMod.intCast_eq_intCast_iff]
      exact Int.modEq_iff_dvd.mpr (by simpa using hcongr_p.neg_right)
    rw [ZMod.intCast_eq_intCast_iff] at h1
    have h2 := jacobiSym.mod_left (-(qn n : ℤ) * (y1 : ℤ) ^ 2) p
    have h3 := jacobiSym.mod_left (1 : ℤ) p
    rw [Int.ModEq.symm h1] at h3
    have hjac_sq : jacobiSym (-(qn n : ℤ) * (y1 : ℤ) ^ 2) p = 1 := by
      rw [← h2, h3]; simp [jacobiSym.one_left]
    rw [jacobiSym.mul_left, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr (by exact_mod_cast hpy1)).symm, mul_one] at hjac_sq
    exact hjac_sq
  have hfq : fermatQuot p (-(qn n : ℤ)) + 2 * fermatQuot p (y1 : ℤ) = 0 := by
    have hp2_dvd : (p : ℤ) ^ 2 ∣ -(qn n : ℤ) * (y1 : ℤ) ^ 2 - 1 := by
      have hv2 : 2 ≤ padicValNat p n.factorial := by
        have := (hpart3 p hp hp3 hpx).2.2.1
        have := one_le_padicValNat_of_dvd hx1_pos.ne' hpx; omega
      have h1 := dvd_trans (pow_dvd_pow (p : ℤ) hv2) hcongr_fac
      simpa [show -(qn n : ℤ) * (y1 : ℤ) ^ 2 - 1 = -((qn n : ℤ) * (y1 : ℤ) ^ 2 + 1) by ring] using dvd_neg.mpr h1
    have hpqn : ¬ (p : ℤ) ∣ -(qn n : ℤ) := by
      intro h
      have h1 : (p : ℤ) ∣ (1 : ℤ) := by
        have : (1 : ℤ) = (x1 : ℤ) ^ 2 + (-(qn n : ℤ)) * (y1 : ℤ) ^ 2 := by
          have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; linarith
        rw [this]; exact dvd_add (dvd_pow hpx_Z (by norm_num)) (dvd_mul_of_dvd_left h _)
      have := Int.le_of_dvd (by norm_num) h1; omega
    have hfc := k2_fermatQuot_congr hp hp2_dvd
    rw [k2_fermatQuot_one p hp, k2_fermatQuot_mul hp hpqn (fun h => hpy1 ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h |>.elim id id)),
      show (y1 : ℤ) ^ 2 = (y1 : ℤ) * (y1 : ℤ) by ring, k2_fermatQuot_mul hp hpy1 hpy1] at hfc
    linear_combination hfc
  exact ⟨hjac_d1, hjac_d2, hjac_qn, hqy_zmod, hfq⟩

/-- Odd part of even-valuation factorial product `A_n^* := ∏_{3 ≤ p ≤ n, p ∈ 𝒫_even} p^{v_p(n!)}` (4.7). -/
def AnStar (n : ℕ) : ℕ :=
  ∏ p ∈ (Peven n).filter (3 ≤ ·), p ^ padicValNat p n.factorial

/-- Odd-valuation factorial product `B_n^* := ∏_{3 ≤ p ≤ n, p ∈ 𝒫_odd} p^{v_p(n!)}` (4.7). -/
def BnStar (n : ℕ) : ℕ :=
  ∏ p ∈ (Podd n).filter (3 ≤ ·), p ^ padicValNat p n.factorial

/-- `Z := ∏_{3 ≤ p ≤ n, p ∈ 𝒫_even, p ∣ Y₁(q_n)} p^{v_p(n!)/2}` (4.7). -/
def Zn (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  ∏ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y1 n hn hn6), p ^ (padicValNat p n.factorial / 2)

/-- Even/odd allocation `(A_n, B_n)` allocating `2^{v_2(n!)-2}` according to parity of `X₁(q_n)`. -/
def An (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  if X1 n hn hn6 % 2 = 1 then AnStar n else 2 ^ (padicValNat 2 n.factorial - 2) * AnStar n

def Bn (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  if X1 n hn hn6 % 2 = 1 then 2 ^ (padicValNat 2 n.factorial - 2) * BnStar n else BnStar n

private lemma AnStar_pos (n : ℕ) : 0 < AnStar n :=
  Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _

private lemma BnStar_pos (n : ℕ) : 0 < BnStar n :=
  Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _

private lemma Zn_pos (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : 0 < Zn n hn hn6 :=
  Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _

private lemma theorem_4_2_i_part1 :
    ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
      (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
      let an := An n (by omega) hn6
      let bn := Bn n (by omega) hn6
      let zn := Zn n (by omega) hn6
      Nat.gcd an bn = 1 ∧
      an = (X1 n (by omega) hn6) ^ 2 * zn ^ 2 ∧
      qn n * (Y1 n (by omega) hn6) ^ 2 = bn * zn ^ 2 ∧
      an = bn * zn ^ 4 + zn ^ 2 := by
  intro n m hn hn6 hsol hk2
  dsimp only
  set x1 := X1 n (by omega) hn6
  set y1 := Y1 n (by omega) hn6
  set an := An n (by omega) hn6
  set bn := Bn n (by omega) hn6
  set zn := Zn n (by omega) hn6
  have hx1_pos : 1 ≤ x1 := by
    have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop
    nlinarith [sq_nonneg (y1 : ℤ), qn_pos n]
  have hy1_pos : 0 < y1 := Y1_pos (by omega) hn6
  have hqy_ne : qn n * y1 ^ 2 ≠ 0 := mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 hy1_pos.ne')
  have h_ell := (pellFundUnit (by omega : 3 ≤ n) hn6).prop
  have hqy_x1 : qn n * y1 ^ 2 + 1 = x1 ^ 2 := by zify; linarith
  have h_gcd_AB : Nat.gcd an bn = 1 := by
    refine Nat.coprime_of_dvd fun p hp hpa hpb => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    rcases hp.eq_two_or_odd with rfl | hodd
    · by_cases hxodd : x1 % 2 = 1
      · have hpa' : 2 ∣ AnStar n := by simpa [An, hxodd] using hpa
        have : padicValNat 2 (AnStar n) = 0 := by
          unfold AnStar
          rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ Nat.prime_two]
          simp
        have := one_le_padicValNat_of_dvd (AnStar_pos n).ne' hpa'
        omega
      · have hpb' : 2 ∣ BnStar n := by simpa [Bn, hxodd] using hpb
        have : padicValNat 2 (BnStar n) = 0 := by
          unfold BnStar
          rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ Nat.prime_two]
          simp
        have := one_le_padicValNat_of_dvd (BnStar_pos n).ne' hpb'
        omega
    · have hpa' : p ∣ AnStar n := by
        unfold An at hpa
        split_ifs at hpa with hxodd
        · exact hpa
        · exact (hp.dvd_mul.mp hpa).resolve_left fun h2 => by
            have := hp.dvd_of_dvd_pow h2
            have := Nat.le_of_dvd (by norm_num) this; omega
      have hpb' : p ∣ BnStar n := by
        unfold Bn at hpb
        split_ifs at hpb with hxodd
        · exact (hp.dvd_mul.mp hpb).resolve_left fun h2 => by
            have := hp.dvd_of_dvd_pow h2
            have := Nat.le_of_dvd (by norm_num) this; omega
        · exact hpb
      have h1 : padicValNat p (AnStar n) ≠ 0 := (one_le_padicValNat_of_dvd (AnStar_pos n).ne' hpa').ne'
      have h2 : padicValNat p (BnStar n) ≠ 0 := (one_le_padicValNat_of_dvd (BnStar_pos n).ne' hpb').ne'
      unfold AnStar at h1; unfold BnStar at h2
      rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp] at h1
      rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp] at h2
      split_ifs at h1 with hpE
      · split_ifs at h2 with hpO
        · exact (Podd_disjoint_Peven n).le_bot (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hpO).1, (Finset.mem_filter.mp hpE).1⟩)
        · exact h2 rfl
      · exact h1 rfl
  obtain ⟨_, _, _, _, _, _, hfac⟩ := critical_eqs_4_1_to_4_3 n m (by omega) hn6 hsol hk2
  have hfac_qy : n.factorial = 4 * (qn n * y1 ^ 2) * x1 ^ 2 := by
    rw [hfac, show (x1 - 1) * x1 ^ 2 * (x1 + 1) = ((x1 - 1) * (x1 + 1)) * x1 ^ 2 by ring,
      show (x1 - 1) * (x1 + 1) = qn n * y1 ^ 2 by zify [hx1_pos]; linarith]
    ring
  have hprop := prop_4_1 n m hn hn6 hsol hk2
  have han_eq : an = x1 ^ 2 * zn ^ 2 := by
    refine Nat.eq_of_factorization_eq (by unfold an An; split_ifs <;> positivity [AnStar_pos n])
      (mul_ne_zero (pow_ne_zero 2 hx1_pos.ne') (pow_ne_zero 2 (Zn_pos n (by omega) hn6).ne'))
      fun p => ?_
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [← padicValNat_eq_factorization hp, ← padicValNat_eq_factorization hp]
      rcases hp.eq_two_or_odd with rfl | hodd
      · have hv2_fac : padicValNat 2 n.factorial = 2 + padicValNat 2 (qn n * y1 ^ 2) + 2 * padicValNat 2 x1 := by
          conv_lhs => rw [hfac_qy]
          rw [padicValNat.mul (mul_ne_zero (by norm_num) hqy_ne) (pow_ne_zero 2 hx1_pos.ne'),
            padicValNat.mul (by norm_num) hqy_ne, show (4 : ℕ) = 2 ^ 2 by norm_num,
            padicValNat.pow 2 2, padicValNat.self (by norm_num), mul_one, padicValNat.pow x1 2]
        have hv2_zn : padicValNat 2 zn = 0 := by
          unfold zn Zn
          rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ Nat.prime_two]
          simp
        rw [padicValNat.mul (pow_ne_zero 2 hx1_pos.ne') (pow_ne_zero 2 (Zn_pos n (by omega) hn6).ne'),
          padicValNat.pow x1 2, padicValNat.pow zn 2, hv2_zn, mul_zero, add_zero]
        unfold an An
        split_ifs with hxodd
        · have hv2_A : padicValNat 2 (AnStar n) = 0 := by
            unfold AnStar
            rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ Nat.prime_two]
            simp
          have hv2_x1 : padicValNat 2 x1 = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
          rw [hv2_A, hv2_x1, mul_zero]
        · have hx_even : 2 ∣ x1 := by omega
          have hqy_odd : ¬ 2 ∣ qn n * y1 ^ 2 := by
            intro h2
            have : 2 ∣ x1 ^ 2 - qn n * y1 ^ 2 := dvd_sub (dvd_pow hx_even (by norm_num)) h2
            rw [show x1 ^ 2 - qn n * y1 ^ 2 = 1 by zify; linarith] at this
            omega
          rw [padicValNat.eq_zero_of_not_dvd hqy_odd, add_zero] at hv2_fac
          have hv2_A : padicValNat 2 (AnStar n) = 0 := by
            unfold AnStar
            rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ Nat.prime_two]
            simp
          rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) (AnStar_pos n).ne',
            padicValNat.pow 2 _, padicValNat.self (by norm_num), mul_one, hv2_A, add_zero]
          omega
      · have hp3 : 3 ≤ p := by omega
        have hv_an : padicValNat p an = if p ∈ (Peven n).filter (3 ≤ ·) then padicValNat p n.factorial else 0 := by
          unfold an An
          split_ifs with hxodd
          · unfold AnStar
            exact padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp
          · rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) (AnStar_pos n).ne',
              padicValNat.pow 2 _, padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega),
              mul_zero, zero_add]
            unfold AnStar
            exact padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp
        have hv_zn : padicValNat p zn = if p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ y1) then padicValNat p n.factorial / 2 else 0 := by
          unfold zn Zn
          exact padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp
        rw [hv_an, padicValNat.mul (pow_ne_zero 2 hx1_pos.ne') (pow_ne_zero 2 (Zn_pos n (by omega) hn6).ne'),
          padicValNat.pow x1 2, padicValNat.pow zn 2, hv_zn]
        by_cases hpe : p ∈ Peven n
        · have hpe3 : p ∈ (Peven n).filter (3 ≤ ·) := Finset.mem_filter.mpr ⟨hpe, hp3⟩
          have heven_v : 2 ∣ padicValNat p n.factorial := (Finset.mem_filter.mp hpe).2.2
          have hv_fac : padicValNat p n.factorial = padicValNat p (qn n * y1 ^ 2) + 2 * padicValNat p x1 := by
            conv_lhs => rw [hfac_qy]
            rw [padicValNat.mul (mul_ne_zero (by norm_num) hqy_ne) (pow_ne_zero 2 hx1_pos.ne'),
              padicValNat.mul (by norm_num) hqy_ne,
              padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega),
              zero_add, padicValNat.pow x1 2]
          by_cases hpx1 : p ∣ x1
          · have hndvd_y1 : ¬ p ∣ y1 := fun hpy1 => by
              have h1 : p ∣ x1 ^ 2 - qn n * y1 ^ 2 :=
                dvd_sub (dvd_pow hpx1 (by norm_num)) (dvd_mul_of_dvd_right (dvd_pow hpy1 (by norm_num)) _)
              rw [show x1 ^ 2 - qn n * y1 ^ 2 = 1 by zify; linarith] at h1
              exact hp.not_dvd_one h1
            have h1 := (hprop.2.2.1 p hp hp3 hpx1).2.2.1
            simp [hpe3, hpe, hp3, hndvd_y1, h1]
          · have hndvd_qn : ¬ p ∣ qn n := by
              intro h
              rw [qn_eq_prod_Podd] at h
              obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finset_prod_iff.mp h
              have : p = q := (Nat.prime_dvd_prime_iff_eq hp (Finset.mem_filter.mp hq).2.1).mp hqp
              subst this
              exact (Podd_disjoint_Peven n).le_bot (Finset.mem_inter.mpr ⟨hq, hpe⟩)
            rw [padicValNat.eq_zero_of_not_dvd hpx1, mul_zero, add_zero,
              padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 hy1_pos.ne'),
              padicValNat.eq_zero_of_not_dvd hndvd_qn, zero_add, padicValNat.pow y1 2] at hv_fac
            have hpy1 : p ∣ y1 := by
              have hv_pos : 0 < padicValNat p n.factorial := by
                have hpn := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpe).1).2
                exact one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) (hp.dvd_factorial.mpr hpn)
              have hv_y1_pos : 0 < padicValNat p y1 := by omega
              exact dvd_of_padicValNat_pos hv_y1_pos
            simp [hpe3, hpe, hp3, hpy1]
            omega
        · have hndvd_x1 : ¬ p ∣ x1 := fun h => hpe (hprop.2.2.1 p hp hp3 h).1
          have hpe3 : ¬ p ∈ (Peven n).filter (3 ≤ ·) := fun h => hpe (Finset.mem_filter.mp h).1
          have hzn3 : ¬ p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ y1) := fun h => hpe (Finset.mem_filter.mp h).1
          simp [hpe3, hzn3, padicValNat.eq_zero_of_not_dvd hndvd_x1]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hqy_bn_zn : qn n * y1 ^ 2 = bn * zn ^ 2 := by
    have h1 : 4 * (qn n * y1 ^ 2) * x1 ^ 2 = 4 * (bn * zn ^ 2) * x1 ^ 2 := by
      have hfac_ab : n.factorial = 4 * an * bn := by
        have h_odd2 : padicValNat 2 n.factorial ≥ 2 := by
          have : 4 ∣ n.factorial := Nat.factorial_dvd_of_le (by omega : 4 ≤ n)
          exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp (by simpa using this)
        have hAB_prod : an * bn = 2 ^ (padicValNat 2 n.factorial - 2) * AnStar n * BnStar n := by
          unfold an bn An Bn; split_ifs <;> ring
        rw [hAB_prod]
        have hodd_prod : AnStar n * BnStar n = ∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, p ^ padicValNat p n.factorial := by
          unfold AnStar BnStar
          have hdisj : Disjoint ((Peven n).filter (3 ≤ ·)) ((Podd n).filter (3 ≤ ·)) :=
            (Podd_disjoint_Peven n).symm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          rw [← Finset.prod_union hdisj]
          congr 1
          ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Peven, Podd]
          constructor
          · rintro (⟨⟨⟨_, hpn⟩, hp, _⟩, hp3⟩ | ⟨⟨⟨_, hpn⟩, hp, _⟩, hp3⟩) <;> exact ⟨⟨hp3, hpn⟩, hp⟩
          · rintro ⟨⟨hp3, hpn⟩, hp⟩
            by_cases hd : 2 ∣ padicValNat p n.factorial
            · exact Or.inl ⟨⟨⟨by omega, hpn⟩, hp, hd⟩, hp3⟩
            · exact Or.inr ⟨⟨⟨by omega, hpn⟩, hp, hd⟩, hp3⟩
        have h2_fac : 4 * 2 ^ (padicValNat 2 n.factorial - 2) = 2 ^ padicValNat 2 n.factorial := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_sub_cancel' h_odd2]
        have hfull : 2 ^ padicValNat 2 n.factorial * ∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, p ^ padicValNat p n.factorial =
            n.factorial := by
          have h2_mem : ¬ 2 ∈ (Finset.Icc 3 n).filter Nat.Prime := by simp
          rw [← Finset.prod_insert h2_mem]
          refine prod_filter_prime_dvd_eq (Nat.factorial_ne_zero n) (fun p hp => ?_) (fun p hp hpdvd => ?_)
          · rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact Nat.prime_two
            · exact (Finset.mem_filter.mp hp').2
          · rcases hp.eq_two_or_odd with rfl | hodd
            · exact Finset.mem_insert_self 2 _
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp.dvd_factorial.mp hpdvd⟩, hp⟩)
        calc 4 * (2 ^ (padicValNat 2 n.factorial - 2) * AnStar n * BnStar n)
            = (4 * 2 ^ (padicValNat 2 n.factorial - 2)) * (AnStar n * BnStar n) := by ring
          _ = 2 ^ padicValNat 2 n.factorial * ∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, p ^ padicValNat p n.factorial := by
              rw [h2_fac, hodd_prod]
          _ = n.factorial := hfull
      rw [← hfac_qy, hfac_ab, han_eq]
      ring
    have hx4 : 0 < 4 * x1 ^ 2 := by positivity
    nlinarith
  have han_bn_zn : an = bn * zn ^ 4 + zn ^ 2 := by
    calc an = x1 ^ 2 * zn ^ 2 := han_eq
      _ = (qn n * y1 ^ 2 + 1) * zn ^ 2 := by rw [hqy_x1]
      _ = (bn * zn ^ 2 + 1) * zn ^ 2 := by rw [hqy_bn_zn]
      _ = bn * zn ^ 4 + zn ^ 2 := by ring
  exact ⟨h_gcd_AB, han_eq, hqy_bn_zn, han_bn_zn⟩

theorem theorem_4_2_i :
    (∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
      (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
      let an := An n (by omega) hn6
      let bn := Bn n (by omega) hn6
      let zn := Zn n (by omega) hn6
      Nat.gcd an bn = 1 ∧
      an = (X1 n (by omega) hn6) ^ 2 * zn ^ 2 ∧
      qn n * (Y1 n (by omega) hn6) ^ 2 = bn * zn ^ 2 ∧
      an = bn * zn ^ 4 + zn ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
        let an := An n (by omega) hn6
        let bn := Bn n (by omega) hn6
        let zn := Zn n (by omega) hn6
        let c2 : ℝ := if X1 n (by omega) hn6 % 2 = 1 then -1 else 2 * Real.log 2 - 1
        |4 * Real.log zn - (c2 - SigmaParityStar n) * n| ≤ C * n / Real.log n ∧
        0 < zn ^ 2 ∧ zn ^ 2 < bn ∧
        an / bn = zn ^ 4 ∧ an % bn = zn ^ 2 ∧ (an % bn) ^ 2 = an / bn ∧
        let Zgt : ℕ := ∏ p ∈ (Peven n).filter (fun p => Nat.sqrt n < p ∧ p ∣ Y1 n (by omega) hn6),
          p ^ (padicValNat p n.factorial / 2)
        |4 * Real.log Zgt -
          (c2 + ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
            (if p ∣ X1 n (by omega) hn6 then (1 : ℝ) else -1) *
              (Real.log p / ((p : ℝ) - 1))) * n| ≤ C * n / Real.log n) := by
  refine ⟨theorem_4_2_i_part1, ?_⟩
  obtain ⟨C_25, hC_25, N₀_25, hN₀_25⟩ := theorem_2_5_i
  obtain ⟨_, hSig_o, _, hSodd_o, _⟩ := theorem_2_5_ii
  have h_ev : ∀ᶠ n : ℕ in atTop,
      8 ≤ n ∧ N₀_25 ≤ n ∧
      |SigmaParityStar n| ≤ (1 / 16 : ℝ) * Real.log n ∧
      |Sodd n - (1 / 2 : ℝ) * n * Real.log n| ≤ (1 / 8 : ℝ) * n * Real.log n ∧
      (C_25 + 16) ≤ (1 / 16 : ℝ) * (Real.log n) ^ 2 ∧
      (Real.log n) ^ 2 ≤ n ∧
      4 * Real.sqrt n * (Real.log n) ^ 2 ≤ n := by
    have h1 : ∀ᶠ n : ℕ in atTop, 8 ≤ n := eventually_ge_atTop 8
    have h2 : ∀ᶠ n : ℕ in atTop, N₀_25 ≤ n := eventually_ge_atTop N₀_25
    have h3 : ∀ᶠ n : ℕ in atTop, |SigmaParityStar n| ≤ (1 / 16 : ℝ) * Real.log n := by
      have h := hSig_o.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 16))
      filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog_pos] at hn
      exact (div_le_iff₀ hlog_pos).mp hn.le
    have h4 : ∀ᶠ n : ℕ in atTop, |Sodd n - (1 / 2 : ℝ) * n * Real.log n| ≤ (1 / 8 : ℝ) * n * Real.log n := by
      have h := hSodd_o.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 8))
      filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
      have hpos : 0 < (n : ℝ) * Real.log n := mul_pos (by exact_mod_cast (by omega : 0 < n)) (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos] at hn
      exact (div_le_iff₀ hpos).mp hn.le
    have h5 : ∀ᶠ n : ℕ in atTop, (C_25 + 16) ≤ (1 / 16 : ℝ) * (Real.log n) ^ 2 := by
      have hlim : Tendsto (fun n : ℕ => (1 / 16 : ℝ) * (Real.log n) ^ 2) atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop (by norm_num)
      exact hlim.eventually_ge_atTop (C_25 + 16)
    have h6 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ n := by
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
        have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
          have h0 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
          refine (h0.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          dsimp only [Function.comp_def]; rw [Real.log_rpow hx]; ring
        have hpow := (hsub.comp tendsto_natCast_atTop_atTop).pow 2
        simp only [zero_pow (by norm_num : 2 ≠ 0)] at hpow
        refine hpow.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le]
        norm_num
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
      exact (div_le_one (by exact_mod_cast hn1)).mp hn
    have h7 : ∀ᶠ n : ℕ in atTop, 4 * Real.sqrt n * (Real.log n) ^ 2 ≤ n := by
      have hlim : Tendsto (fun n : ℕ => 4 * Real.sqrt n * (Real.log n) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
        have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
          have h0 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
          refine (h0.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          dsimp only [Function.comp_def]; rw [Real.log_rpow hx]; ring
        have hpow := ((hsub.comp tendsto_natCast_atTop_atTop).pow 2).const_mul 4
        simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hpow
        refine hpow.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le, Real.sqrt_eq_rpow]
        norm_num
        rw [← Real.rpow_one (n : ℝ), ← Real.rpow_add hn_pos]
        norm_num
        rw [div_eq_mul_inv, mul_assoc]
        congr 2
        rw [← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos]
        norm_num
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
      exact (div_le_one (by exact_mod_cast hn1)).mp hn
    exact h1.and (h2.and (h3.and (h4.and (h5.and (h6.and h7)))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
  refine ⟨C_25 + 20, by linarith, max N₀ 8, le_max_right _ _, ?_⟩
  intro n m hn hn6 hN hsol hk2
  obtain ⟨_, hn25, hSig_bd, hSodd_bd, hC_log, hlog2_n, hsqrt_n⟩ := hN₀ n (le_trans (le_max_left _ _) hN)
  obtain ⟨_, han_eq, hqy_bn_zn, han_bn_zn⟩ := theorem_4_2_i_part1 n m hn hn6 hsol hk2
  set x1 := X1 n (by omega) hn6
  set y1 := Y1 n (by omega) hn6
  set an := An n (by omega) hn6
  set bn := Bn n (by omega) hn6
  set zn := Zn n (by omega) hn6
  set c2 : ℝ := if x1 % 2 = 1 then -1 else 2 * Real.log 2 - 1
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog1 : 1 ≤ Real.log n := by
    have : Real.exp 1 ≤ (n : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9]) (by exact_mod_cast hn)
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hzn_pos : 0 < zn := Zn_pos n (by omega) hn6
  have hbn_pos : 0 < bn := by unfold bn Bn; split_ifs <;> positivity [BnStar_pos n]
  have hAn_log : Real.log (AnStar n) = Seven n := by
    unfold AnStar Seven
    rw [Nat.cast_prod, Real.log_prod _ _ fun p hp => pow_ne_zero _ (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.ne_zero)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hBn_log : Real.log (BnStar n) = Sodd n := by
    unfold BnStar Sodd
    rw [Nat.cast_prod, Real.log_prod _ _ fun p hp => pow_ne_zero _ (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.ne_zero)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hv2_bd : |((padicValNat 2 n.factorial : ℝ) - 2) - (n : ℝ)| ≤ 2 * Real.log n / Real.log 2 + 4 := by
    have h2_sum : (padicValNat 2 n.factorial : ℤ) + ((Nat.digits 2 n).sum : ℤ) = n := by
      have := sub_one_mul_padicValNat_factorial (p := 2) n; omega
    have hs2_le : (Nat.digits 2 n).sum ≤ (Nat.digits 2 n).length := by
      calc (Nat.digits 2 n).sum
          = ∑ j ∈ Finset.range (Nat.digits 2 n).length, (Nat.digits 2 n).getD j 0 := list_sum_eq_sum_range _
        _ ≤ ∑ _j ∈ Finset.range (Nat.digits 2 n).length, 1 := Finset.sum_le_sum fun j _ => by
            by_cases hj : j < (Nat.digits 2 n).length
            · have := Nat.digits_lt_base (by norm_num : 1 < 2) (List.getElem_mem hj)
              simp [List.getD_eq_getElem?_getD, hj]; omega
            · simp [List.getD_eq_getElem?_getD, hj]
        _ = (Nat.digits 2 n).length := by simp
    have hlen_le : ((Nat.digits 2 n).length : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
      have h2pow : 2 ^ ((Nat.digits 2 n).length - 1) ≤ n := Nat.base_pow_length_digits_le 2 n (by norm_num) (by omega)
      have hlog : (((Nat.digits 2 n).length - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
        have := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ ((Nat.digits 2 n).length - 1)) (by exact_mod_cast h2pow)
        rwa [Real.log_pow] at this
      have hlen1 : 1 ≤ (Nat.digits 2 n).length := by
        have : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
        exact List.length_pos.mpr this
      have h1 : (((Nat.digits 2 n).length : ℝ) - 1) ≤ Real.log n / Real.log 2 := by
        rw [le_div_iff₀ (Real.log_pos (by norm_num))]
        have : (((Nat.digits 2 n).length - 1 : ℕ) : ℝ) = ((Nat.digits 2 n).length : ℝ) - 1 := by
          rw [Nat.cast_sub hlen1, Nat.cast_one]
        linarith
      linarith
    have hs2_R : ((Nat.digits 2 n).sum : ℝ) ≤ Real.log n / Real.log 2 + 1 :=
      le_trans (by exact_mod_cast hs2_le) hlen_le
    have h_eq : (padicValNat 2 n.factorial : ℝ) - (n : ℝ) = -((Nat.digits 2 n).sum : ℝ) := by
      have : (padicValNat 2 n.factorial : ℝ) + ((Nat.digits 2 n).sum : ℝ) = (n : ℝ) := by exact_mod_cast h2_sum
      linarith
    rw [abs_le]; constructor <;> linarith [show (0 : ℝ) ≤ ((Nat.digits 2 n).sum : ℝ) by positivity]
  have h4zn_eq : 4 * Real.log zn =
      (Real.log (an : ℝ) - Real.log (bn : ℝ)) - Real.log (1 + 1 / ((bn : ℝ) * (zn : ℝ) ^ 2)) := by
    have h1 : (an : ℝ) = (bn : ℝ) * (zn : ℝ) ^ 4 * (1 + 1 / ((bn : ℝ) * (zn : ℝ) ^ 2)) := by
      have h_nat : (an : ℝ) = (bn : ℝ) * (zn : ℝ) ^ 4 + (zn : ℝ) ^ 2 := by exact_mod_cast han_bn_zn
      rw [h_nat]; field_simp [(by positivity : (bn : ℝ) * (zn : ℝ) ^ 2 ≠ 0)]; ring
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog_1_err : 0 ≤ Real.log (1 + 1 / ((bn : ℝ) * (zn : ℝ) ^ 2)) ∧
      Real.log (1 + 1 / ((bn : ℝ) * (zn : ℝ) ^ 2)) ≤ 1 := by
    have h_ge1 : 1 ≤ (bn : ℝ) * (zn : ℝ) ^ 2 := by exact_mod_cast (by positivity : 1 ≤ bn * zn ^ 2)
    constructor
    · exact Real.log_nonneg (by linarith [show 0 < 1 / ((bn : ℝ) * (zn : ℝ) ^ 2) by positivity])
    · have hle : 1 + 1 / ((bn : ℝ) * (zn : ℝ) ^ 2) ≤ 2 := by
        have : 1 / ((bn : ℝ) * (zn : ℝ) ^ 2) ≤ 1 := div_le_one_of_le₀ h_ge1 (by positivity)
        linarith
      exact le_trans (Real.log_le_log (by positivity) hle) (by linarith [Real.log_two_lt_d9])
  have h_ab_diff : |(Real.log (an : ℝ) - Real.log (bn : ℝ)) - (c2 - SigmaParityStar n) * n| ≤
      (C_25 + 6) * n / Real.log n := by
    have h2_ge2 : 2 ≤ padicValNat 2 n.factorial := by
      have : 4 ∣ n.factorial := Nat.factorial_dvd_of_le (by omega : 4 ≤ n)
      exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp (by simpa using this)
    have hDelta := hN₀_25 n hn25
    have hlog_an : Real.log (an : ℝ) = (if x1 % 2 = 1 then 0 else ((padicValNat 2 n.factorial - 2 : ℕ) : ℝ) * Real.log 2) + Seven n := by
      unfold an An; split_ifs
      · rw [zero_add, hAn_log]
      · rw [Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (AnStar_pos n).ne'),
          Nat.cast_pow, Real.log_pow, hAn_log]; simp
    have hlog_bn : Real.log (bn : ℝ) = (if x1 % 2 = 1 then ((padicValNat 2 n.factorial - 2 : ℕ) : ℝ) * Real.log 2 else 0) + Sodd n := by
      unfold bn Bn; split_ifs
      · rw [Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (BnStar_pos n).ne'),
          Nat.cast_pow, Real.log_pow, hBn_log]; simp
      · rw [zero_add, hBn_log]
    have hcast_v2 : ((padicValNat 2 n.factorial - 2 : ℕ) : ℝ) = (padicValNat 2 n.factorial : ℝ) - 2 := by
      rw [Nat.cast_sub h2_ge2, Nat.cast_two]
    have h_err_bd : |((padicValNat 2 n.factorial : ℝ) - 2 - n) * Real.log 2| ≤ 6 * n / Real.log n := by
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by norm_num))]
      have h1 : |((padicValNat 2 n.factorial : ℝ) - 2 - n)| * Real.log 2 ≤ 2 * Real.log n + 4 * Real.log 2 := by
        have h2 := mul_le_mul_of_nonneg_right hv2_bd (Real.log_nonneg (by norm_num))
        rw [add_mul, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne'] at h2
        exact h2
      have h2 : 2 * Real.log n + 4 * Real.log 2 ≤ 6 * Real.log n := by
        have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        nlinarith
      have h3 : 6 * Real.log n ≤ 6 * n / Real.log n := by
        rw [le_div_iff₀ hlog_pos]; nlinarith [hlog2_n]
      linarith
    rw [hlog_an, hlog_bn, hcast_v2]
    dsimp only [c2]
    split_ifs with hxodd
    · have hrew : (0 + Seven n - (((padicValNat 2 n.factorial : ℝ) - 2) * Real.log 2 + Sodd n)) - (-1 - SigmaParityStar n) * n =
          (DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * n) -
          (((padicValNat 2 n.factorial : ℝ) - 2 - n) * Real.log 2) := by
        unfold DeltaParity; ring
      rw [hrew]; exact le_trans (abs_sub _ _) (by linarith)
    · have hrew : ((((padicValNat 2 n.factorial : ℝ) - 2) * Real.log 2 + Seven n) - (0 + Sodd n)) - (2 * Real.log 2 - 1 - SigmaParityStar n) * n =
          (DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * n) +
          (((padicValNat 2 n.factorial : ℝ) - 2 - n) * Real.log 2) := by
        unfold DeltaParity; ring
      rw [hrew]; exact le_trans (abs_add_le _ _) (by linarith)
  have h4zn_bd : |4 * Real.log zn - (c2 - SigmaParityStar n) * n| ≤ (C_25 + 16) * n / Real.log n := by
    rw [h4zn_eq]
    have h1 : 1 ≤ n / Real.log n := by
      rw [le_div_iff₀ hlog_pos]; nlinarith [hlog2_n]
    have hsub := le_trans (abs_sub _ _) (add_le_add h_ab_diff (by rw [abs_of_nonneg hlog_1_err.1]; exact hlog_1_err.2))
    linarith
  have h4zn_bd' : |4 * Real.log zn - (c2 - SigmaParityStar n) * n| ≤ (C_25 + 20) * n / Real.log n :=
    le_trans h4zn_bd (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)) hlog_pos.le)
  have hzn2_pos : 0 < zn ^ 2 := by positivity
  have hzn2_lt_bn : zn ^ 2 < bn := by
    have hc2_bd : |c2| ≤ 1 := by
      dsimp only [c2]; split_ifs
      · norm_num
      · rw [abs_le]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
    have hlog_zn_ub : 4 * Real.log zn ≤ (3 / 16 : ℝ) * n * Real.log n := by
      have h1 : 4 * Real.log zn ≤ (c2 - SigmaParityStar n) * n + (C_25 + 16) * n / Real.log n := by
        linarith [(abs_le.mp h4zn_bd).2]
      have h2 : (c2 - SigmaParityStar n) * n ≤ (1 + (1 / 16 : ℝ) * Real.log n) * n := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)
        linarith [(abs_le.mp hc2_bd).2, (abs_le.mp hSig_bd).1]
      have h3 : (C_25 + 16) * n / Real.log n ≤ (1 / 16 : ℝ) * n * Real.log n := by
        rw [div_le_iff₀ hlog_pos]
        have := mul_le_mul_of_nonneg_right hC_log (Nat.cast_nonneg n)
        linarith
      have h4 : (n : ℝ) ≤ (1 / 16 : ℝ) * n * Real.log n := by
        have hlog16 : 16 ≤ Real.log n := by
          have : 16 ^ 2 ≤ (Real.log n) ^ 2 := by linarith
          nlinarith [hlog_pos]
        nlinarith
      linarith
    have hlog_bn_lb : (3 / 8 : ℝ) * n * Real.log n ≤ Real.log (bn : ℝ) := by
      have h1 : (3 / 8 : ℝ) * n * Real.log n ≤ Sodd n := by linarith [(abs_le.mp hSodd_bd).1]
      have h2 : Sodd n ≤ Real.log (bn : ℝ) := by
        rw [← hBn_log]
        unfold bn Bn; split_ifs
        · rw [Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (BnStar_pos n).ne')]
          have hpow1 : (1 : ℝ) ≤ 2 ^ (padicValNat 2 n.factorial - 2) := one_le_pow₀ (by norm_num)
          linarith [Real.log_nonneg hpow1]
        · exact le_rfl
      linarith
    have hlt_log : Real.log ((zn ^ 2 : ℕ) : ℝ) < Real.log (bn : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      have hn_log_pos : 0 < (n : ℝ) * Real.log n := mul_pos (by exact_mod_cast (by omega : 0 < n)) hlog_pos
      linarith
    have hlt_R : ((zn ^ 2 : ℕ) : ℝ) < (bn : ℝ) := (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlt_log
    exact_mod_cast hlt_R
  have hdiv_eq : an / bn = zn ^ 4 := by
    rw [han_bn_zn, add_comm, Nat.add_mul_div_left _ _ hbn_pos, Nat.div_eq_of_lt hzn2_lt_bn, zero_add]
  have hmod_eq : an % bn = zn ^ 2 := by
    rw [han_bn_zn, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzn2_lt_bn]
  have hsq_eq : (an % bn) ^ 2 = an / bn := by
    rw [hmod_eq, hdiv_eq]; ring
  set Zgt : ℕ := ∏ p ∈ (Peven n).filter (fun p => Nat.sqrt n < p ∧ p ∣ y1),
    p ^ (padicValNat p n.factorial / 2)
  set Zle : ℕ := ∏ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
    p ^ (padicValNat p n.factorial / 2)
  have hZ_split : zn = Zle * Zgt := by
    unfold zn Zn
    have hdisj : Disjoint ((Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1))
        ((Peven n).filter (fun p => Nat.sqrt n < p ∧ p ∣ y1)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2; omega
    rw [← Finset.prod_union hdisj]
    congr 1
    ext p; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hp3, hpy⟩
      by_cases hle : p ≤ Nat.sqrt n
      · exact Or.inl ⟨hp, hp3, hle, hpy⟩
      · exact Or.inr ⟨hp, by omega, hpy⟩
    · rintro (⟨hp, hp3, _, hpy⟩ | ⟨hp, hgt, hpy⟩)
      · exact ⟨hp, hp3, hpy⟩
      · have hsqrt2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
        exact ⟨hp, by omega, hpy⟩
  have hZle_pos : 0 < Zle :=
    Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _
  have hZgt_pos : 0 < Zgt :=
    Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _
  have h4Zgt_eq : 4 * Real.log Zgt = 4 * Real.log zn - 4 * Real.log Zle := by
    rw [hZ_split, Nat.cast_mul, Real.log_mul (by exact_mod_cast hZle_pos.ne') (by exact_mod_cast hZgt_pos.ne')]; ring
  have h4Zle_eq : 4 * Real.log Zle =
      ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
        2 * (padicValNat p n.factorial : ℝ) * Real.log p := by
    unfold Zle
    rw [Nat.cast_prod, Real.log_prod _ _ fun p hp => pow_ne_zero _ (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.ne_zero),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have heven : 2 ∣ padicValNat p n.factorial := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    rw [Nat.cast_pow, Real.log_pow]
    obtain ⟨t, ht⟩ := heven
    have hdiv : padicValNat p n.factorial / 2 = t := by omega
    rw [ht, hdiv]; push_cast; ring
  have h_sig_rew : (c2 - SigmaParityStar n) * n -
      (c2 + ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (if p ∣ x1 then (1 : ℝ) else -1) * (Real.log p / ((p : ℝ) - 1))) * n =
      -(2 * (n : ℝ) * ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
        Real.log p / ((p : ℝ) - 1)) := by
    have hfl_sqrt : ⌊Real.sqrt n⌋₊ = Nat.sqrt n := by
      rw [Nat.floor_eq_iff (Real.sqrt_nonneg n)]
      exact ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n)),
        Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast (by simpa [sq] using Nat.lt_succ_sqrt n))⟩
    have hsig : SigmaParityStar n =
        ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)) := by
      unfold SigmaParityStar SigmaParity; rw [hfl_sqrt]
    rw [hsig]
    have hprop := prop_4_1 n m hn hn6 hsol hk2
    have hsub : (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1) ⊆
        (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, Peven] at hp ⊢
      exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.1.2.1⟩
    have hsum_sub : ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
          Real.log p / ((p : ℝ) - 1) =
        ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          (if p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1) then
            Real.log p / ((p : ℝ) - 1) else 0) :=
      (Finset.sum_ite_mem ((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime) _ _).symm.trans (by
        rw [Finset.inter_eq_right.mpr hsub])
    rw [hsum_sub, Finset.mul_sum, ← sub_mul]
    congr 1
    rw [show c2 - ∑ p ∈ _, _ - (c2 + ∑ p ∈ _, _) =
        -(∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          ((-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) +
            (if p ∣ x1 then (1 : ℝ) else -1)) * (Real.log p / ((p : ℝ) - 1))) by
      rw [← Finset.sum_add_distrib]
      have : ∀ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          ((-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) +
            (if p ∣ x1 then (1 : ℝ) else -1)) * (Real.log p / ((p : ℝ) - 1)) =
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)) +
          (if p ∣ x1 then (1 : ℝ) else -1) * (Real.log p / ((p : ℝ) - 1)) := fun p _ => by ring
      rw [Finset.sum_congr rfl this]; ring]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hp_sqrt : p ≤ Nat.sqrt n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hp_n : p ≤ n := le_trans hp_sqrt (Nat.sqrt_le_self n)
    by_cases hpe : p ∈ Peven n
    · have heven : 2 ∣ padicValNat p n.factorial := (Finset.mem_filter.mp hpe).2.2
      have hpow_neg : (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) = -1 := by
        obtain ⟨t, ht⟩ := heven
        have hv1 : 1 ≤ padicValNat p n.factorial := one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) (hp_prime.dvd_factorial.mpr hp_n)
        have hodd : Odd (padicValNat p n.factorial - 1) := by omega
        rw [show (padicValNat p n.factorial : ℤ) - 1 = ((padicValNat p n.factorial - 1 : ℕ) : ℤ) by omega,
          zpow_natCast, Odd.neg_one_pow hodd]
      by_cases hpy : p ∣ y1
      · have hpx : ¬ p ∣ x1 := fun hpx => by
          have h1 : p ∣ x1 ^ 2 - qn n * y1 ^ 2 := dvd_sub (dvd_pow hpx (by norm_num)) (dvd_mul_of_dvd_right (dvd_pow hpy (by norm_num)) _)
          rw [show x1 ^ 2 - qn n * y1 ^ 2 = 1 by have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify; linarith] at h1
          exact hp_prime.not_dvd_one h1
        have hmem : p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1) :=
          Finset.mem_filter.mpr ⟨hpe, hp3, hp_sqrt, hpy⟩
        simp [hpow_neg, hpx, hmem]; ring
      · have hpx : p ∣ x1 := by
          obtain ⟨_, _, _, _, _, _, hfac⟩ := critical_eqs_4_1_to_4_3 n m (by omega) hn6 hsol hk2
          have hqy_eq : qn n * y1 ^ 2 = (x1 - 1) * (x1 + 1) := by
            have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 by nlinarith [sq_nonneg (y1 : ℤ), qn_pos n]]; linarith
          have hfac_qy : n.factorial = 4 * (qn n * y1 ^ 2) * x1 ^ 2 := by rw [hfac, hqy_eq]; ring
          have hpn_dvd : p ∣ n.factorial := hp_prime.dvd_factorial.mpr hp_n
          rw [hfac_qy] at hpn_dvd
          have hndvd4 : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
          have hndvd_qn : ¬ p ∣ qn n := fun h => by
            rw [qn_eq_prod_Podd] at h
            obtain ⟨q, hq, hqp⟩ := hp_prime.prime.dvd_finset_prod_iff.mp h
            have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime (Finset.mem_filter.mp hq).2.1).mp hqp
            subst this
            exact (Podd_disjoint_Peven n).le_bot (Finset.mem_inter.mpr ⟨hq, hpe⟩)
          rcases hp_prime.dvd_mul.mp hpn_dvd with h4qy | hx2
          · rcases hp_prime.dvd_mul.mp h4qy with h4 | hqy
            · exact absurd h4 hndvd4
            · rcases hp_prime.dvd_mul.mp hqy with hq | hy2
              · exact absurd hq hndvd_qn
              · exact absurd (hp_prime.dvd_of_dvd_pow hy2) hpy
          · exact hp_prime.dvd_of_dvd_pow hx2
        have hmem : ¬ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1) := fun h =>
          hpy (Finset.mem_filter.mp h).2.2.2
        simp [hpow_neg, hpx, hmem]
    · have hpx : ¬ p ∣ x1 := fun h => hpe (hprop.2.2.1 p hp_prime hp3 h).1
      have hmem : ¬ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1) := fun h =>
        hpe (Finset.mem_filter.mp h).1
      have hodd : ¬ 2 ∣ padicValNat p n.factorial := fun hev =>
        hpe (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hp_n⟩, hp_prime, hev⟩)
      have hv1 : 1 ≤ padicValNat p n.factorial := one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) (hp_prime.dvd_factorial.mpr hp_n)
      have heven1 : Even (padicValNat p n.factorial - 1) := by
        have := Nat.not_even_iff_odd.mp (fun h => hodd (even_iff_two_dvd.mp h))
        exact Nat.Odd.sub_odd this (by norm_num)
      have hpow_neg : (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) = 1 := by
        rw [show (padicValNat p n.factorial : ℤ) - 1 = ((padicValNat p n.factorial - 1 : ℕ) : ℤ) by omega,
          zpow_natCast, Even.neg_one_pow heven1]
      simp [hpow_neg, hpx, hmem]
  have hZle_diff : |4 * Real.log Zle - 2 * (n : ℝ) *
      ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
        Real.log p / ((p : ℝ) - 1)| ≤ 4 * n / Real.log n := by
    rw [h4Zle_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
        |2 * (padicValNat p n.factorial : ℝ) * Real.log p - 2 * (n : ℝ) * (Real.log p / ((p : ℝ) - 1))| ≤
          4 * Real.log n := by
      intro p hp
      have hp_prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2.1
      have hp_sqrt : p ≤ Nat.sqrt n := (Finset.mem_filter.mp hp).2.2.1
      have hp_n : p ≤ n := le_trans hp_sqrt (Nat.sqrt_le_self n)
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have hleg := sub_one_mul_padicValNat_factorial (p := p) n
      have hsum_le : (Nat.digits p n).sum ≤ (p - 1) * (Nat.digits p n).length := by
        calc (Nat.digits p n).sum
            = ∑ j ∈ Finset.range (Nat.digits p n).length, (Nat.digits p n).getD j 0 := list_sum_eq_sum_range _
          _ ≤ ∑ _j ∈ Finset.range (Nat.digits p n).length, (p - 1) := Finset.sum_le_sum fun j _ => by
              by_cases hj : j < (Nat.digits p n).length
              · have := Nat.digits_lt_base hp_prime.one_lt (List.getElem_mem hj)
                simp [List.getD_eq_getElem?_getD, hj]; omega
              · simp [List.getD_eq_getElem?_getD, hj]
          _ = (p - 1) * (Nat.digits p n).length := by simp [mul_comm]
      have hlen_le : ((Nat.digits p n).length : ℝ) ≤ Real.log n / Real.log p + 1 := by
        have hppow : p ^ ((Nat.digits p n).length - 1) ≤ n := Nat.base_pow_length_digits_le p n hp_prime.one_lt (by omega)
        have hlog : (((Nat.digits p n).length - 1 : ℕ) : ℝ) * Real.log p ≤ Real.log n := by
          have := Real.log_le_log (by positivity : 0 < (p : ℝ) ^ ((Nat.digits p n).length - 1)) (by exact_mod_cast hppow)
          rwa [Real.log_pow] at this
        have hlen1 : 1 ≤ (Nat.digits p n).length := List.length_pos.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))
        have h1 : (((Nat.digits p n).length : ℝ) - 1) ≤ Real.log n / Real.log p := by
          rw [le_div_iff₀ (Real.log_pos (by exact_mod_cast hp_prime.one_lt))]
          have : (((Nat.digits p n).length - 1 : ℕ) : ℝ) = ((Nat.digits p n).length : ℝ) - 1 := by
            rw [Nat.cast_sub hlen1, Nat.cast_one]
          linarith
        linarith
      have hlegR : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = (n : ℝ) - ((Nat.digits p n).sum : ℝ) := by
        have h1 : (p - 1) * padicValNat p n.factorial + (Nat.digits p n).sum = n := by omega
        have h2 : ((p - 1 : ℕ) : ℝ) * (padicValNat p n.factorial : ℝ) + ((Nat.digits p n).sum : ℝ) = (n : ℝ) := by exact_mod_cast h1
        rw [Nat.cast_sub hp_prime.one_lt.le, Nat.cast_one] at h2; linarith
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by have : (3 : ℝ) ≤ p := by exact_mod_cast hp3; linarith
      have hdiff_eq : 2 * (padicValNat p n.factorial : ℝ) * Real.log p - 2 * (n : ℝ) * (Real.log p / ((p : ℝ) - 1)) =
          -(2 * ((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1)) := by
        have : (padicValNat p n.factorial : ℝ) = ((n : ℝ) - ((Nat.digits p n).sum : ℝ)) / ((p : ℝ) - 1) := by
          rw [eq_div_iff hp1_pos.ne', mul_comm]; exact hlegR
        rw [this]; ring
      rw [hdiff_eq, abs_neg, abs_of_nonneg (by positivity)]
      have h1 : ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) ≤ (Nat.digits p n).length := by
        rw [div_le_iff₀ hp1_pos]
        have : ((Nat.digits p n).sum : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * ((Nat.digits p n).length : ℝ) := by exact_mod_cast hsum_le
        rwa [Nat.cast_sub hp_prime.one_lt.le, Nat.cast_one, mul_comm] at this
      have h2 : ((Nat.digits p n).length : ℝ) * Real.log p ≤ Real.log n + Real.log p := by
        have := mul_le_mul_of_nonneg_right hlen_le (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
        rw [add_mul, div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hp_prime.one_lt)).ne'] at this
        exact this
      have hlogp_le : Real.log p ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hp_n)
      calc 2 * ((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1)
          = 2 * (((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1)) * Real.log p := by ring
        _ ≤ 2 * ((Nat.digits p n).length : ℝ) * Real.log p :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
        _ ≤ 2 * (Real.log n + Real.log p) := by linarith
        _ ≤ 4 * Real.log n := by linarith
    have hcard_le : (((Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1)).card : ℝ) ≤ Real.sqrt n := by
      have hsub : (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1) ⊆ Finset.Icc 1 (Nat.sqrt n) := by
        intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢; exact ⟨by omega, hp.2.2.1⟩
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      have h2 : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
      exact le_trans (by exact_mod_cast h1) h2
    calc ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
          |2 * (padicValNat p n.factorial : ℝ) * Real.log p - 2 * (n : ℝ) * (Real.log p / ((p : ℝ) - 1))|
        ≤ ∑ _p ∈ _, 4 * Real.log n := Finset.sum_le_sum hterm
      _ = ((_ : Finset ℕ).card : ℝ) * (4 * Real.log n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt n * (4 * Real.log n) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ ≤ 4 * n / Real.log n := by
          rw [le_div_iff₀ hlog_pos]
          linarith [hsqrt_n]
  have hZgt_bd : |4 * Real.log Zgt - (c2 + ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
      (if p ∣ x1 then (1 : ℝ) else -1) * (Real.log p / ((p : ℝ) - 1))) * n| ≤
      (C_25 + 20) * n / Real.log n := by
    rw [h4Zgt_eq]
    have hrew : 4 * Real.log zn - 4 * Real.log Zle -
        (c2 + ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          (if p ∣ x1 then (1 : ℝ) else -1) * (Real.log p / ((p : ℝ) - 1))) * n =
        (4 * Real.log zn - (c2 - SigmaParityStar n) * n) -
        (4 * Real.log Zle - 2 * (n : ℝ) *
          ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n ∧ p ∣ y1),
            Real.log p / ((p : ℝ) - 1)) := by
      linarith [h_sig_rew]
    rw [hrew]
    exact le_trans (abs_sub _ _) (by linarith [h4zn_bd, hZle_diff])
  exact ⟨h4zn_bd', hzn2_pos, hzn2_lt_bn, hdiv_eq, hmod_eq, hsq_eq, hZgt_bd⟩

theorem theorem_4_2_ii :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
      (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
      let x1 := X1 n (by omega) hn6
      let bn := Bn n (by omega) hn6
      let zn := Zn n (by omega) hn6
      let c0 := Nat.gcd (x1 - 1) (x1 + 1)
      (c0 = 1 ∨ c0 = 2) ∧
      ∃ Bminus Bplus Zminus Zplus : ℕ,
        Nat.gcd Bminus Bplus = 1 ∧ Nat.gcd Zminus Zplus = 1 ∧
        Bminus * Bplus = bn / c0 ^ 2 ∧ Zminus * Zplus = zn ∧
        (x1 - 1) / c0 = Bminus * Zminus ^ 2 ∧
        (x1 + 1) / c0 = Bplus * Zplus ^ 2 ∧
        (Bplus : ℤ) * (Zplus : ℤ) ^ 2 - (Bminus : ℤ) * (Zminus : ℤ) ^ 2 = 2 / (c0 : ℤ) ∧
        let Rn := An n (by omega) hn6 % bn
        N₀ ≤ n →
        Bplus * Rn = Bminus * Zminus ^ 4 + (2 / c0) * Zminus ^ 2 ∧
        (Bminus : ℤ) * (Rn : ℤ) = (Bplus : ℤ) * (Zplus : ℤ) ^ 4 - (2 / (c0 : ℤ)) * (Zplus : ℤ) ^ 2 ∧
        (Bplus * Rn) / Bminus = Zminus ^ 4 ∧
        Int.ceil ((Bminus : ℝ) * Rn / Bplus) = (Zplus ^ 4 : ℤ) := by
  obtain ⟨C42, hC42, N₀_42, hN₀_42⟩ := theorem_4_2_i.2
  obtain ⟨_, hSig_o, _, _, _⟩ := theorem_2_5_ii
  have h_ev : ∀ᶠ n : ℕ in atTop,
      N₀_42 ≤ n ∧ 8 ≤ n ∧
      |SigmaParityStar n| ≤ (1 / 64 : ℝ) * Real.log n ∧
      C42 ≤ (1 / 64 : ℝ) * (Real.log n) ^ 2 ∧
      (Real.log n) ^ 2 ≤ n ∧
      (1 / 4 : ℝ) * (n : ℝ) * Real.log n ≤ Real.log ((n.factorial : ℝ) / 16) ∧
      64 ≤ Real.log n ∧
      Real.log 16 ≤ (1 / 128 : ℝ) * (n : ℝ) * Real.log n := by
    have h1 : ∀ᶠ n : ℕ in atTop, N₀_42 ≤ n := eventually_ge_atTop N₀_42
    have h2 : ∀ᶠ n : ℕ in atTop, 8 ≤ n := eventually_ge_atTop 8
    have h3 : ∀ᶠ n : ℕ in atTop, |SigmaParityStar n| ≤ (1 / 64 : ℝ) * Real.log n := by
      have h := hSig_o.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 64))
      filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog_pos] at hn
      exact (div_le_iff₀ hlog_pos).mp hn.le
    have h4 : ∀ᶠ n : ℕ in atTop, C42 ≤ (1 / 64 : ℝ) * (Real.log n) ^ 2 :=
      (((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop (by norm_num)).eventually_ge_atTop C42
    have h5 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ n := by
      have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
        have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
          have h0 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
          refine (h0.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          dsimp only [Function.comp_def]; rw [Real.log_rpow hx]; ring
        have hpow := (hsub.comp tendsto_natCast_atTop_atTop).pow 2
        simp only [zero_pow (by norm_num : 2 ≠ 0)] at hpow
        refine hpow.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hn_pos.le]; norm_num
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
      exact (div_le_one (by exact_mod_cast hn1)).mp hn
    have h6 : ∀ᶠ n : ℕ in atTop, (1 / 4 : ℝ) * (n : ℝ) * Real.log n ≤ Real.log ((n.factorial : ℝ) / 16) := by
      filter_upwards [eventually_ge_atTop 256] with n hn256
      have hpow_le : (n / 2) ^ (n / 2) ≤ n.factorial := by
        have h1 : (n / 2) ^ (n - n / 2) ≤ n.factorial := by
          have hsub : Finset.Icc (n / 2 + 1) n ⊆ Finset.Icc 1 n := fun k hk =>
            Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hk).1; omega, (Finset.mem_Icc.mp hk).2⟩
          have hprod : (n / 2) ^ (Finset.Icc (n / 2 + 1) n).card ≤ ∏ k ∈ Finset.Icc (n / 2 + 1) n, k := by
            rw [← Finset.prod_const]
            exact Finset.prod_le_prod' fun k hk => by have := (Finset.mem_Icc.mp hk).1; omega
          rw [Nat.card_Icc, show n + 1 - (n / 2 + 1) = n - n / 2 by omega] at hprod
          have hfac_prod : ∏ k ∈ Finset.Icc 1 n, k = n.factorial := by
            rw [Nat.factorial_eq_prod_range_add_one]
            refine Finset.prod_nbij' (fun k => k - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
            · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
            · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
            · intro k hk; rw [Finset.mem_Icc] at hk; omega
            · intro k _; omega
            · intro k hk; rw [Finset.mem_Icc] at hk; omega
          exact le_trans hprod (Finset.prod_le_prod_of_subset_of_one_le' hsub (fun _ _ _ => by omega) |>.trans_eq hfac_prod)
        exact le_trans (Nat.pow_le_pow_right (by omega) (by omega : n / 2 ≤ n - n / 2)) h1
      have hlog_n2 : Real.log ((n / 2 : ℕ) : ℝ) ≥ Real.log n - Real.log 4 := by
        have h1 : (n : ℝ) / 4 ≤ ((n / 2 : ℕ) : ℝ) := by
          have : n ≤ 4 * (n / 2) := by omega
          exact_mod_cast (by linarith : (n : ℝ) / 4 ≤ ((n / 2 : ℕ) : ℝ))
        have := Real.log_le_log (by positivity) h1
        rwa [Real.log_div (by positivity) (by norm_num)] at this
      have hfac_R : Real.log (n.factorial : ℝ) ≥ ((n / 2 : ℕ) : ℝ) * (Real.log n - Real.log 4) := by
        have h1 := Real.log_le_log (by positivity : 0 < ((n / 2 : ℕ) : ℝ) ^ (n / 2)) (by exact_mod_cast hpow_le)
        rw [Real.log_pow] at h1
        exact le_trans (mul_le_mul_of_nonneg_left hlog_n2 (by positivity)) h1
      have hn_half : (2 : ℝ) / 5 * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
        have : 2 * n ≤ 5 * (n / 2) := by omega
        exact_mod_cast (by linarith : (2 : ℝ) / 5 * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ))
      have hlog4_lt : Real.log 4 ≤ (1 / 4 : ℝ) * Real.log n := by
        have h1 : (4 : ℝ) ^ (4 : ℕ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 256 ≤ n)
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_pow] at h2; push_cast at h2; linarith
      have hlog16_bd : Real.log 16 ≤ (1 / 20 : ℝ) * (n : ℝ) * Real.log n := by
        have hlog16 : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 16 ≤ n))
        have hn20 : (1 : ℝ) ≤ (1 / 20 : ℝ) * (n : ℝ) := by
          have : (20 : ℝ) ≤ n := by exact_mod_cast (by omega : 20 ≤ n)
          linarith
        nlinarith [Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n) : (1 : ℝ) ≤ n)]
      rw [Real.log_div (by exact_mod_cast (Nat.factorial_ne_zero n)) (by norm_num)]
      have h34 : (3 / 4 : ℝ) * Real.log n ≤ Real.log n - Real.log 4 := by linarith
      have hmul : (3 / 10 : ℝ) * (n : ℝ) * Real.log n ≤ ((n / 2 : ℕ) : ℝ) * (Real.log n - Real.log 4) := by
        calc (3 / 10 : ℝ) * (n : ℝ) * Real.log n = ((2 : ℝ) / 5 * (n : ℝ)) * ((3 / 4 : ℝ) * Real.log n) := by ring
          _ ≤ ((n / 2 : ℕ) : ℝ) * (Real.log n - Real.log 4) :=
              mul_le_mul hn_half h34 (by positivity) (by positivity)
      linarith
    have h7 : ∀ᶠ n : ℕ in atTop, 64 ≤ Real.log n :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 64
    have h8 : ∀ᶠ n : ℕ in atTop, Real.log 16 ≤ (1 / 128 : ℝ) * (n : ℝ) * Real.log n := by
      filter_upwards [eventually_ge_atTop 128, h7] with n hn128 hlog64
      have hlog16 : Real.log 16 ≤ Real.log n := by linarith [Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 16 ≤ n) : (16 : ℝ) ≤ n)]
      have hn128' : (1 : ℝ) ≤ (1 / 128 : ℝ) * (n : ℝ) := by
        have : (128 : ℝ) ≤ n := by exact_mod_cast hn128
        linarith
      nlinarith
    exact h1.and (h2.and (h3.and (h4.and (h5.and (h6.and (h7.and h8))))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
  refine ⟨max N₀ 8, le_max_right _ _, ?_⟩
  intro n m hn hn6 hsol hk2
  dsimp only
  set x1 := X1 n (by omega) hn6
  set y1 := Y1 n (by omega) hn6
  set an := An n (by omega) hn6
  set bn := Bn n (by omega) hn6
  set zn := Zn n (by omega) hn6
  set c0 := Nat.gcd (x1 - 1) (x1 + 1)
  have hx1_pos : 1 ≤ x1 := by
    have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop
    nlinarith [sq_nonneg (y1 : ℤ), qn_pos n]
  have hx1_ge2 : 2 ≤ x1 := by
    have hqy_pos : 0 < qn n * y1 ^ 2 := mul_pos (qn_pos n) (pow_pos (Y1_pos (by omega) hn6) 2)
    have h1 := (pellFundUnit (by omega : 3 ≤ n) hn6).prop
    nlinarith
  have hc0_12 : c0 = 1 ∨ c0 = 2 := by
    have hdvd2 : c0 ∣ 2 := by
      have h1 : c0 ∣ x1 - 1 := Nat.gcd_dvd_left _ _
      have h2 : c0 ∣ x1 + 1 := Nat.gcd_dvd_right _ _
      have h3 := Nat.dvd_sub h2 h1
      rwa [show x1 + 1 - (x1 - 1) = 2 by omega] at h3
    have hc0_pos : 0 < c0 := Nat.gcd_pos_of_pos_right _ (by omega)
    have hc0_le : c0 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  have hc0_pos : 0 < c0 := by rcases hc0_12 with h | h <;> omega
  have h_part1 := theorem_4_2_i_part1 n m hn hn6 hsol hk2
  have hqy_eq : qn n * y1 ^ 2 = (x1 - 1) * (x1 + 1) := by
    have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [hx1_pos]; linarith
  have hprod_bn_zn : (x1 - 1) * (x1 + 1) = bn * zn ^ 2 := by
    rw [← hqy_eq]; exact h_part1.2.2.1
  have hc0_dvd1 : c0 ∣ x1 - 1 := Nat.gcd_dvd_left _ _
  have hc0_dvd2 : c0 ∣ x1 + 1 := Nat.gcd_dvd_right _ _
  set u := (x1 - 1) / c0
  set v := (x1 + 1) / c0
  have hu_pos : 0 < u := Nat.div_pos (Nat.le_of_dvd (by omega) hc0_dvd1) hc0_pos
  have hv_pos : 0 < v := Nat.div_pos (Nat.le_of_dvd (by omega) hc0_dvd2) hc0_pos
  have hcop_uv : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hc0_pos
  have hc02_dvd_bn : c0 ^ 2 ∣ bn := by
    rcases hc0_12 with hc01 | hc02
    · rw [hc01]; simp
    · rw [hc02]
      have hxodd : x1 % 2 = 1 := by
        have : 2 ∣ x1 + 1 := hc02 ▸ hc0_dvd2
        omega
      have hv2 : 4 ≤ padicValNat 2 n.factorial := by
        have : (2 ^ 4 : ℕ) ∣ Nat.factorial 8 := by decide
        exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp (by simpa using dvd_trans this (Nat.factorial_dvd_factorial hn))
      unfold bn Bn; rw [if_pos hxodd]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 2 ≤ padicValNat 2 n.factorial - 2)) _
  have huv_eq : u * v = (bn / c0 ^ 2) * zn ^ 2 := by
    have h1 : c0 ^ 2 * (u * v) = c0 ^ 2 * ((bn / c0 ^ 2) * zn ^ 2) := by
      calc c0 ^ 2 * (u * v) = (c0 * u) * (c0 * v) := by ring
        _ = (x1 - 1) * (x1 + 1) := by rw [Nat.mul_div_cancel' hc0_dvd1, Nat.mul_div_cancel' hc0_dvd2]
        _ = bn * zn ^ 2 := hprod_bn_zn
        _ = (c0 ^ 2 * (bn / c0 ^ 2)) * zn ^ 2 := by rw [Nat.mul_div_cancel' hc02_dvd_bn]
        _ = c0 ^ 2 * ((bn / c0 ^ 2) * zn ^ 2) := by ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hc0_pos 2) h1
  set Zminus := Nat.gcd zn u
  set Zplus := Nat.gcd zn v
  have hZ_cop : Nat.gcd Zminus Zplus = 1 := by
    refine Nat.coprime_of_dvd fun p hp h1 h2 => ?_
    exact hp.not_dvd_one (hcop_uv ▸ Nat.dvd_gcd (dvd_trans h1 (Nat.gcd_dvd_right _ _)) (dvd_trans h2 (Nat.gcd_dvd_right _ _)))
  have hZ_prod : Zminus * Zplus = zn := by
    have hzn_dvd : zn ∣ u * v := by
      rw [huv_eq]; exact dvd_trans (dvd_pow_self zn (by norm_num)) (dvd_mul_left _ _)
    have h1 : zn ∣ Zminus * Zplus := by
      rw [← Nat.gcd_mul_left_left]
      exact Nat.dvd_gcd (dvd_mul_right zn _) (dvd_trans hzn_dvd (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _))
    exact Nat.dvd_antisymm (hZ_cop.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)) h1
  have hZm_dvd : Zminus ^ 2 ∣ u := by
    have h1 : Zminus ^ 2 ∣ u * v := by rw [huv_eq, ← hZ_prod, mul_pow]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    exact (Nat.Coprime.symm (hcop_uv.coprime_dvd_left (Nat.gcd_dvd_right zn u))).pow_left 2 |>.dvd_of_dvd_mul_right h1
  have hZp_dvd : Zplus ^ 2 ∣ v := by
    have h1 : Zplus ^ 2 ∣ u * v := by rw [huv_eq, ← hZ_prod, mul_pow]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    exact (Nat.Coprime.symm (hcop_uv.symm.coprime_dvd_left (Nat.gcd_dvd_right zn v))).pow_left 2 |>.dvd_of_dvd_mul_right h1
  set Bminus := u / Zminus ^ 2
  set Bplus := v / Zplus ^ 2
  have hB_cop : Nat.gcd Bminus Bplus = 1 :=
    hcop_uv.coprime_dvd_left (Nat.div_dvd_of_dvd hZm_dvd) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hZp_dvd)
  have hBm_eq : u = Bminus * Zminus ^ 2 := (Nat.div_mul_cancel hZm_dvd).symm
  have hBp_eq : v = Bplus * Zplus ^ 2 := (Nat.div_mul_cancel hZp_dvd).symm
  have hB_prod : Bminus * Bplus = bn / c0 ^ 2 := by
    have hzn_pos : 0 < zn := Zn_pos n (by omega) hn6
    have h1 : (Bminus * Bplus) * zn ^ 2 = (bn / c0 ^ 2) * zn ^ 2 := by
      calc (Bminus * Bplus) * zn ^ 2 = (Bminus * Bplus) * (Zminus * Zplus) ^ 2 := by rw [hZ_prod]
        _ = (Bminus * Zminus ^ 2) * (Bplus * Zplus ^ 2) := by ring
        _ = u * v := by rw [← hBm_eq, ← hBp_eq]
        _ = (bn / c0 ^ 2) * zn ^ 2 := huv_eq
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hzn_pos 2) h1
  have h_diff_Z : (Bplus : ℤ) * (Zplus : ℤ) ^ 2 - (Bminus : ℤ) * (Zminus : ℤ) ^ 2 = 2 / (c0 : ℤ) := by
    have h1 : (c0 : ℤ) * ((Bplus : ℤ) * (Zplus : ℤ) ^ 2 - (Bminus : ℤ) * (Zminus : ℤ) ^ 2) = 2 := by
      have huZ : (c0 : ℤ) * ((Bminus : ℤ) * (Zminus : ℤ) ^ 2) = (x1 : ℤ) - 1 := by
        have : c0 * (Bminus * Zminus ^ 2) = x1 - 1 := by rw [← hBm_eq]; exact Nat.mul_div_cancel' hc0_dvd1
        zify [hx1_pos] at this ⊢; exact this
      have hvZ : (c0 : ℤ) * ((Bplus : ℤ) * (Zplus : ℤ) ^ 2) = (x1 : ℤ) + 1 := by
        have : c0 * (Bplus * Zplus ^ 2) = x1 + 1 := by rw [← hBp_eq]; exact Nat.mul_div_cancel' hc0_dvd2
        exact_mod_cast this
      linarith
    rcases hc0_12 with hc01 | hc02
    · rw [hc01] at h1 ⊢; norm_num at h1 ⊢; linarith
    · rw [hc02] at h1 ⊢; norm_num at h1 ⊢; linarith
  refine ⟨hc0_12, Bminus, Bplus, Zminus, Zplus, hB_cop, hZ_cop, hB_prod, hZ_prod,
    hBm_eq, hBp_eq, h_diff_Z, ?_⟩
  intro hN
  dsimp only
  have hN42 : N₀_42 ≤ n := le_trans (hN₀ n (le_trans (le_max_left _ _) hN)).1 (le_refl n)
  have h42 := hN₀_42 n m hn hn6 hN42 hsol hk2
  dsimp only at h42
  have hRn_eq : an % bn = zn ^ 2 := h42.2.2.2.2.1
  obtain ⟨_, hSig_bd, hC_log, hlog2_n, hfac_lb, hlog64, hlog16_bd⟩ := (hN₀ n (le_trans (le_max_left _ _) hN)).2.2
  have hlog_pos : 0 < Real.log n := by linarith
  have hc2_bd : |if x1 % 2 = 1 then (-1 : ℝ) else 2 * Real.log 2 - 1| ≤ 1 := by
    split_ifs
    · norm_num
    · rw [abs_le]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have h4zn_ub : 4 * Real.log zn ≤ (3 / 64 : ℝ) * n * Real.log n := by
    have h1 : 4 * Real.log zn ≤ ((if x1 % 2 = 1 then (-1 : ℝ) else 2 * Real.log 2 - 1) - SigmaParityStar n) * n +
        C42 * n / Real.log n := by linarith [(abs_le.mp h42.1).2]
    have h2 : ((if x1 % 2 = 1 then (-1 : ℝ) else 2 * Real.log 2 - 1) - SigmaParityStar n) * n ≤
        (1 + (1 / 64 : ℝ) * Real.log n) * n :=
      mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hc2_bd).2, (abs_le.mp hSig_bd).1]) (Nat.cast_nonneg n)
    have h3 : C42 * n / Real.log n ≤ (1 / 64 : ℝ) * n * Real.log n := by
      rw [div_le_iff₀ hlog_pos]; linarith [mul_le_mul_of_nonneg_right hC_log (Nat.cast_nonneg n)]
    have h4 : (n : ℝ) ≤ (1 / 64 : ℝ) * n * Real.log n := by nlinarith
    linarith
  have hx1_4_ge : (n.factorial : ℝ) / 16 ≤ (x1 : ℝ) ^ 4 := by
    obtain ⟨_, _, _, _, _, _, hfac⟩ := critical_eqs_4_1_to_4_3 n m (by omega) hn6 hsol hk2
    have h1 : n.factorial ≤ 16 * x1 ^ 4 := by
      rw [hfac]
      have hx1_p : x1 + 1 ≤ 2 * x1 := by omega
      have hx1_m : x1 - 1 ≤ x1 := by omega
      calc 4 * (x1 - 1) * x1 ^ 2 * (x1 + 1)
          ≤ 4 * x1 * x1 ^ 2 * (2 * x1) := by gcongr
        _ = 8 * x1 ^ 4 := by ring
        _ ≤ 16 * x1 ^ 4 := by omega
    exact_mod_cast (by linarith [show (n.factorial : ℝ) ≤ 16 * (x1 : ℝ) ^ 4 by exact_mod_cast h1] :
      (n.factorial : ℝ) / 16 ≤ (x1 : ℝ) ^ 4)
  have hlog_x1_lb : (1 / 16 : ℝ) * n * Real.log n ≤ Real.log (x1 : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hx1_4_ge
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have h_zn_lt_u : 4 * zn ^ 4 < u := by
    have hu_ge : (x1 : ℝ) / 4 ≤ u := by
      have h1 : x1 / 2 ≤ x1 - 1 := by omega
      have h2 : u * c0 = x1 - 1 := Nat.div_mul_cancel hc0_dvd1
      have hc0_le2 : (c0 : ℝ) ≤ 2 := by rcases hc0_12 with h | h <;> simp [h] <;> norm_num
      have h3 : (x1 : ℝ) / 2 ≤ (u : ℝ) * (c0 : ℝ) := by exact_mod_cast (by omega : x1 / 2 ≤ u * c0)
      nlinarith
    have hlog_4zn4 : Real.log ((4 * zn ^ 4 : ℕ) : ℝ) ≤ Real.log 4 + (3 / 64 : ℝ) * n * Real.log n := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; linarith
    have hlog_u : Real.log (u : ℝ) ≥ (1 / 16 : ℝ) * n * Real.log n - Real.log 4 := by
      have h1 := Real.log_le_log (by positivity) hu_ge
      rw [Real.log_div (by positivity) (by norm_num)] at h1; linarith
    have hlt_log : Real.log ((4 * zn ^ 4 : ℕ) : ℝ) < Real.log (u : ℝ) := by
      have hlog4_16 : Real.log 4 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
      have hn_pos : (0 : ℝ) < n * Real.log n := mul_pos (by exact_mod_cast (by omega : 0 < n)) hlog_pos
      linarith
    exact_mod_cast (Real.log_lt_log_iff (by positivity) (by exact_mod_cast hu_pos)).mp hlt_log
  have h_zn_lt_v : 4 * zn ^ 4 < v := by
    have hv_ge : u ≤ v := by
      have hu_eq : u * c0 = x1 - 1 := Nat.div_mul_cancel hc0_dvd1
      have hv_eq : v * c0 = x1 + 1 := Nat.div_mul_cancel hc0_dvd2
      nlinarith [hc0_pos]
    omega
  have h_2Zm_lt_Bm : (2 / c0) * Zminus ^ 2 < Bminus := by
    have h1 : (2 / c0) * Zminus ^ 2 * Zminus ^ 2 ≤ 2 * zn ^ 4 := by
      have hZm_le : Zminus ≤ zn := by rw [← hZ_prod]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h => by
        rw [h, mul_zero] at hZ_prod; exact (Zn_pos n (by omega) hn6).ne' hZ_prod.symm)
      have h2c : 2 / c0 ≤ 2 := Nat.div_le_self _ _
      calc (2 / c0) * Zminus ^ 2 * Zminus ^ 2 ≤ 2 * Zminus ^ 4 := by gcongr; linarith
        _ ≤ 2 * zn ^ 4 := by gcongr
    rw [hBm_eq] at h_zn_lt_u
    have h_lt : (2 / c0) * Zminus ^ 2 * Zminus ^ 2 < Bminus * Zminus ^ 2 := by linarith
    exact lt_of_mul_lt_mul_right h_lt (Nat.zero_le _)
  have h_2Zp_lt_Bp : (2 / c0) * Zplus ^ 2 < Bplus := by
    have h1 : (2 / c0) * Zplus ^ 2 * Zplus ^ 2 ≤ 2 * zn ^ 4 := by
      have hZp_le : Zplus ≤ zn := by rw [← hZ_prod]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero fun h => by
        rw [h, zero_mul] at hZ_prod; exact (Zn_pos n (by omega) hn6).ne' hZ_prod.symm)
      have h2c : 2 / c0 ≤ 2 := Nat.div_le_self _ _
      calc (2 / c0) * Zplus ^ 2 * Zplus ^ 2 ≤ 2 * Zplus ^ 4 := by gcongr; linarith
        _ ≤ 2 * zn ^ 4 := by gcongr
    rw [hBp_eq] at h_zn_lt_v
    have h_lt : (2 / c0) * Zplus ^ 2 * Zplus ^ 2 < Bplus * Zplus ^ 2 := by linarith
    exact lt_of_mul_lt_mul_right h_lt (Nat.zero_le _)
  have h_eq1 : Bplus * (an % bn) = Bminus * Zminus ^ 4 + (2 / c0) * Zminus ^ 2 := by
    rw [hRn_eq, ← hZ_prod, mul_pow]
    have h1 : (Bplus : ℤ) * (Zplus : ℤ) ^ 2 = (Bminus : ℤ) * (Zminus : ℤ) ^ 2 + (2 / (c0 : ℤ)) := by linarith
    have h2c : ((2 / c0 : ℕ) : ℤ) = 2 / (c0 : ℤ) := by rcases hc0_12 with h | h <;> simp [h]
    zify
    rw [h2c]
    calc (Bplus : ℤ) * ((Zminus : ℤ) ^ 2 * (Zplus : ℤ) ^ 2)
        = ((Bplus : ℤ) * (Zplus : ℤ) ^ 2) * (Zminus : ℤ) ^ 2 := by ring
      _ = ((Bminus : ℤ) * (Zminus : ℤ) ^ 2 + 2 / (c0 : ℤ)) * (Zminus : ℤ) ^ 2 := by rw [h1]
      _ = (Bminus : ℤ) * (Zminus : ℤ) ^ 4 + 2 / (c0 : ℤ) * (Zminus : ℤ) ^ 2 := by ring
  have h_eq2 : (Bminus : ℤ) * ((an % bn : ℕ) : ℤ) = (Bplus : ℤ) * (Zplus : ℤ) ^ 4 - (2 / (c0 : ℤ)) * (Zplus : ℤ) ^ 2 := by
    rw [hRn_eq, ← hZ_prod, mul_pow]
    have h1 : (Bminus : ℤ) * (Zminus : ℤ) ^ 2 = (Bplus : ℤ) * (Zplus : ℤ) ^ 2 - (2 / (c0 : ℤ)) := by linarith
    push_cast
    calc (Bminus : ℤ) * ((Zminus : ℤ) ^ 2 * (Zplus : ℤ) ^ 2)
        = ((Bminus : ℤ) * (Zminus : ℤ) ^ 2) * (Zplus : ℤ) ^ 2 := by ring
      _ = ((Bplus : ℤ) * (Zplus : ℤ) ^ 2 - 2 / (c0 : ℤ)) * (Zplus : ℤ) ^ 2 := by rw [h1]
      _ = (Bplus : ℤ) * (Zplus : ℤ) ^ 4 - 2 / (c0 : ℤ) * (Zplus : ℤ) ^ 2 := by ring
  have h_div_Zm : (Bplus * (an % bn)) / Bminus = Zminus ^ 4 := by
    rw [h_eq1, add_comm, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hBm_eq; exact hu_pos.ne' hBm_eq), Nat.div_eq_of_lt h_2Zm_lt_Bm, zero_add]
  have h_ceil_Zp : Int.ceil ((Bminus : ℝ) * (an % bn : ℕ) / Bplus) = (Zplus ^ 4 : ℤ) := by
    have hBp_pos : (0 : ℝ) < Bplus := by
      exact_mod_cast Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hBp_eq; exact hv_pos.ne' hBp_eq
    have heq_R : (Bminus : ℝ) * (an % bn : ℕ) / Bplus = (Zplus : ℝ) ^ 4 - ((2 / c0 : ℕ) : ℝ) * (Zplus : ℝ) ^ 2 / Bplus := by
      have h2c : ((2 / c0 : ℕ) : ℤ) = 2 / (c0 : ℤ) := by rcases hc0_12 with h | h <;> simp [h]
      have h_eq2' : (Bminus : ℝ) * (an % bn : ℕ) = (Bplus : ℝ) * (Zplus : ℝ) ^ 4 - ((2 / c0 : ℕ) : ℝ) * (Zplus : ℝ) ^ 2 := by
        exact_mod_cast (by rwa [← h2c] at h_eq2)
      rw [h_eq2', sub_div, mul_div_cancel_left₀ _ hBp_pos.ne']
    rw [heq_R, Int.ceil_eq_iff]
    have hrem_pos : 0 < ((2 / c0 : ℕ) : ℝ) * (Zplus : ℝ) ^ 2 / Bplus := by
      have hc_pos : 0 < 2 / c0 := by rcases hc0_12 with h | h <;> simp [h]
      have hZp_pos : 0 < Zplus := Nat.pos_of_ne_zero fun h => by
        rw [h, mul_zero] at hZ_prod; exact (Zn_pos n (by omega) hn6).ne' hZ_prod.symm
      positivity
    have hrem_lt1 : ((2 / c0 : ℕ) : ℝ) * (Zplus : ℝ) ^ 2 / Bplus < 1 := by
      rw [div_lt_one hBp_pos]
      exact_mod_cast h_2Zp_lt_Bp
    push_cast
    constructor <;> linarith
  exact ⟨h_eq1, h_eq2, h_div_Zm, h_ceil_Zp⟩

theorem theorem_4_2_iii (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 6) :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
      (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
      let x1 := X1 n (by omega) hn6
      let δ₁ := coreNat (x1 - 1)
      let δ₂ := coreNat (x1 + 1)
      (∀ δ ∈ ({δ₁, δ₂} : Finset ℕ),
        (omegaNat δ : ℝ) ≥ (8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n ∧
        (δ : ℝ) ≥ Real.exp ((2 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ)) ∧
        (largestPrimeFactor δ : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (omegaNat δ : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (δ : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε))) := by
  let ε' : ℝ := ε / 4
  have hε' : 0 < ε' := by positivity
  have hε'1 : ε' < 1 / 24 := by linarith
  obtain ⟨N₀_ii, hN₀_ii, h42ii⟩ := theorem_4_2_ii
  obtain ⟨C42, hC42, N₀_42, hN₀_42⟩ := theorem_4_2_i.2
  obtain ⟨_, hSig_o, _, _, _⟩ := theorem_2_5_ii
  have h_t25 := theorem_2_5_iii 2 (by norm_num) 1 0 (1 / 2 - ε') (le_refl 0) (by linarith) (by linarith)
  have h_rpow_lim : ∀ (K : ℝ) (η : ℝ), 0 < η →
      ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 4 + η) := by
    intro K η hη
    have hlim : Tendsto (fun n : ℕ => |K| * (n : ℝ) ^ (-η)) atTop (𝓝 0) := by
      have h0 := (tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop
      simpa using h0.const_mul |K|
    filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 : |K| ≤ (n : ℝ) ^ η := by
      have hpos : 0 < (n : ℝ) ^ η := Real.rpow_pos_of_pos hn_pos η
      rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv, div_le_one hpos] at hn
      exact hn
    calc K * (n : ℝ) ^ (1 / 4 : ℝ) ≤ |K| * (n : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hn_pos.le _)
      _ ≤ (n : ℝ) ^ η * (n : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn_pos.le _)
      _ = (n : ℝ) ^ (1 / 4 + η) := by rw [← Real.rpow_add hn_pos]; ring_nf
  have h_log_nfac : ∀ᶠ n : ℕ in atTop,
      (1 - ε' / 16) * (n : ℝ) * Real.log n ≤ Real.log (n.factorial : ℝ) := by
    have hlim : Tendsto (fun n : ℕ =>
        (n : ℝ) * (Real.log (Real.log n) + 1) / ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun u : ℝ => (Real.log u + 1) / u) atTop (𝓝 0) := by
        have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          simpa [Real.exp_neg] using this.comp Real.tendsto_log_atTop
        have h2 : Tendsto (fun u : ℝ => (1 : ℝ) / u) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        simpa [add_div] using h1.add h2
      refine (h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr' ?_
      filter_upwards [eventually_ge_atTop 3] with n hn3
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      dsimp only [Function.comp_def]
      field_simp [hn_pos.ne']
    have hlog_div : ∀ᶠ n : ℕ in atTop,
        (Real.log (Real.log n) + 1) ≤ (ε' / 32) * Real.log n := by
      filter_upwards [hlim.eventually (ge_mem_nhds (by positivity : 0 < ε' / 32)),
        eventually_ge_atTop 3] with n hn hn3
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hpos : 0 < (n : ℝ) * Real.log n := mul_pos hn_pos hlog_pos
      have h1 := (div_le_iff₀ hpos).mp hn
      have h2 : (n : ℝ) * (Real.log (Real.log n) + 1) ≤ (n : ℝ) * ((ε' / 32) * Real.log n) := by
        linarith
      exact le_of_mul_le_mul_left h2 hn_pos
    have h_l_ge : ∀ᶠ n : ℕ in atTop, 4 ≤ n ∧ 2 ≤ Real.log n ∧
        (Real.log (Real.log n) + 1) ≤ (ε' / 32) * Real.log n ∧
        2 * Real.log n ≤ (ε' / 32) * (n : ℝ) := by
      have h1 : ∀ᶠ n : ℕ in atTop, 4 ≤ n := eventually_ge_atTop 4
      have h2 : ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log n :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
      have h4 : ∀ᶠ n : ℕ in atTop, 2 * Real.log n ≤ (ε' / 32) * (n : ℝ) := by
        have h0 : Tendsto (fun n : ℕ => 2 * Real.log n / (n : ℝ)) atTop (𝓝 0) := by
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          have h := (this.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
          simpa [Real.exp_neg, mul_div_assoc] using h.const_mul 2
        filter_upwards [h0.eventually (ge_mem_nhds (by positivity : 0 < ε' / 32)),
          eventually_ge_atTop 1] with n hn hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        exact (div_le_iff₀ hn_pos).mp hn
      filter_upwards [h1, h2, hlog_div, h4] with n a b c d using ⟨a, b, c, d⟩
    filter_upwards [h_l_ge] with n ⟨hn4, hlog2, hlog_bd, hlog_lin⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log n := by linarith
    set M : ℕ := ⌈(n : ℝ) / Real.log n⌉₊
    have hM_le : M ≤ n := Nat.ceil_le.mpr (div_le_self hn_pos.le (by linarith))
    have hM_pos : 1 ≤ M := Nat.one_le_ceil_iff.mpr (div_pos hn_pos hlog_pos)
    have h_card : (n : ℝ) - (n : ℝ) / Real.log n - 1 ≤ ((Finset.Icc M n).card : ℝ) := by
      rw [Nat.card_Icc]
      have hM_lt : (M : ℝ) < (n : ℝ) / Real.log n + 1 := Nat.ceil_lt_add_one (div_pos hn_pos hlog_pos).le
      have hsub : M ≤ n + 1 := by omega
      rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
      linarith
    have hlog_fac_sum : ∀ m : ℕ, Real.log (m.factorial : ℝ) = ∑ k ∈ Finset.Icc 1 m, Real.log (k : ℝ) := by
      intro m; induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ← ih, Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (by positivity) (by positivity), add_comm]
    have h_fac_ge : ((Finset.Icc M n).card : ℝ) * (Real.log n - Real.log (Real.log n)) ≤ Real.log (n.factorial : ℝ) := by
      rw [hlog_fac_sum]
      calc ((Finset.Icc M n).card : ℝ) * (Real.log n - Real.log (Real.log n))
          = ∑ _k ∈ Finset.Icc M n, (Real.log n - Real.log (Real.log n)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Finset.Icc M n, Real.log (k : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkM : (M : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
            have hk_ge : (n : ℝ) / Real.log n ≤ k := le_trans (Nat.le_ceil _) hkM
            rw [← Real.log_div hn_pos.ne' hlog_pos.ne']
            exact Real.log_le_log (div_pos hn_pos hlog_pos) hk_ge
        _ ≤ ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hM_pos) ?_
            intro k hk _
            exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
    have h_diff_pos : 0 ≤ Real.log n - Real.log (Real.log n) := by
      have := Real.log_le_sub_one_of_pos hlog_pos
      linarith
    have h1 : ((n : ℝ) - (n : ℝ) / Real.log n - 1) * (Real.log n - Real.log (Real.log n)) ≤
        ((Finset.Icc M n).card : ℝ) * (Real.log n - Real.log (Real.log n)) :=
      mul_le_mul_of_nonneg_right h_card h_diff_pos
    have h2 : ((n : ℝ) - (n : ℝ) / Real.log n - 1) * (Real.log n - Real.log (Real.log n)) =
        (n : ℝ) * Real.log n - (n : ℝ) * (Real.log (Real.log n) + 1) -
          (Real.log n - Real.log (Real.log n)) + ((n : ℝ) / Real.log n) * Real.log (Real.log n) := by ring
    have h_ll_nn : 0 ≤ Real.log (Real.log n) := Real.log_nonneg (by linarith)
    have h3 : (n : ℝ) * (Real.log (Real.log n) + 1) ≤ (ε' / 32) * (n : ℝ) * Real.log n := by
      calc (n : ℝ) * (Real.log (Real.log n) + 1)
          ≤ (n : ℝ) * ((ε' / 32) * Real.log n) := mul_le_mul_of_nonneg_left hlog_bd hn_pos.le
        _ = (ε' / 32) * (n : ℝ) * Real.log n := by ring
    have h4 : Real.log n - Real.log (Real.log n) ≤ (ε' / 32) * (n : ℝ) * Real.log n := by
      calc Real.log n - Real.log (Real.log n) ≤ Real.log n := by linarith
        _ ≤ 2 * Real.log n := by linarith
        _ ≤ (ε' / 32) * (n : ℝ) := hlog_lin
        _ ≤ (ε' / 32) * (n : ℝ) * Real.log n := by
          have : 1 ≤ Real.log n := by linarith
          nlinarith
    have h5 : 0 ≤ ((n : ℝ) / Real.log n) * Real.log (Real.log n) := by positivity
    linarith
  have h_ev : ∀ᶠ n : ℕ in atTop,
      N₀_ii ≤ n ∧ N₀_42 ≤ n ∧ 8 ≤ n ∧
      |(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ (0 : ℝ)⌋₊ + 1) ⌊(n : ℝ) ^ (1 / 2 - ε')⌋₊).filter
          (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod 2) = 1),
        (padicValNat p n.factorial : ℝ) * Real.log p) -
        ((1 / 2 - ε') / 2) * (n : ℝ) * Real.log n| ≤ (ε' / 8) * (n : ℝ) * Real.log n ∧
      (ε' / 8) * (n : ℝ) ^ (1 / 2 - ε') ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
      (n : ℝ) ^ (1 / 2 - ε') ≥ Real.exp 1 ∧
      (n : ℝ) ^ (1 / 2 - ε) ≥ 1 ∧
      (n : ℝ) ^ (1 / 2 - ε) ≥ (8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n ∧
      (n : ℝ) ^ (1 / 2 - ε) ≥ (2 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) ∧
      (1 - ε' / 16) * (n : ℝ) * Real.log n ≤ Real.log (n.factorial : ℝ) ∧
      |SigmaParityStar n| ≤ (1 / 64 : ℝ) * Real.log n ∧
      C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) +
        (n : ℝ) * Real.log 2 + 2 * Real.log 8 + Real.log 4 ≤ (ε' / 16) * (n : ℝ) * Real.log n := by
    have h1 : ∀ᶠ n : ℕ in atTop, N₀_ii ≤ n := eventually_ge_atTop N₀_ii
    have h2 : ∀ᶠ n : ℕ in atTop, N₀_42 ≤ n := eventually_ge_atTop N₀_42
    have h3 : ∀ᶠ n : ℕ in atTop, 8 ≤ n := eventually_ge_atTop 8
    have h4 : ∀ᶠ n : ℕ in atTop,
        |(∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ (0 : ℝ)⌋₊ + 1) ⌊(n : ℝ) ^ (1 / 2 - ε')⌋₊).filter
            (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod 2) = 1),
          (padicValNat p n.factorial : ℝ) * Real.log p) -
          ((1 / 2 - ε') / 2) * (n : ℝ) * Real.log n| ≤ (ε' / 8) * (n : ℝ) * Real.log n := by
      have h := h_t25.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε' / 8))
      filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
      have hpos : 0 < (n : ℝ) * Real.log n := mul_pos (by exact_mod_cast (by omega : 0 < n)) (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos] at hn
      simpa [sub_zero] using (div_le_iff₀ hpos).mp hn.le
    have h5 : ∀ᶠ n : ℕ in atTop, (ε' / 8) * (n : ℝ) ^ (1 / 2 - ε') ≥ (n : ℝ) ^ (1 / 2 - ε) := by
      have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 - ε) / ((ε' / 8) * (n : ℝ) ^ (1 / 2 - ε'))) atTop (𝓝 0) := by
        have hpos : 0 < ε - ε' := by dsimp only [ε']; linarith
        have h0 := (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
        have hmul := h0.const_mul (8 / ε')
        simp only [mul_zero] at hmul
        refine hmul.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        rw [div_eq_mul_inv, mul_inv, mul_comm ((ε' / 8)⁻¹), ← mul_assoc,
          ← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos]
        ring_nf
      filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
      have hpos : 0 < (ε' / 8) * (n : ℝ) ^ (1 / 2 - ε') := by positivity
      exact (div_le_one hpos).mp hn
    have h6 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 - ε') ≥ Real.exp 1 := by
      have h0 := (tendsto_rpow_atTop (by linarith : 0 < 1 / 2 - ε')).comp tendsto_natCast_atTop_atTop
      exact h0.eventually_ge_atTop (Real.exp 1)
    have h6b : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 - ε) ≥ 1 := by
      filter_upwards [eventually_ge_atTop 1] with n hn1
      exact Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
    have h7 : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (1 / 2 - ε) ≥ (8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n := by
      have hsub := h_rpow_lim (8 * Real.exp Real.eulerMascheroniConstant - ε) (1 / 4 - ε) (by linarith)
      filter_upwards [hsub, eventually_ge_atTop 3] with n hn hn3
      have hlog1 : 1 ≤ Real.log n := by
        have : Real.exp 1 ≤ (n : ℝ) := le_trans (by linarith [Real.exp_one_lt_d9]) (by exact_mod_cast hn3)
        simpa using Real.log_le_log (Real.exp_pos 1) this
      have h1 : (8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n ≤
          max ((8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ)) 0 := by
        rcases le_total 0 ((8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ)) with hnn | hnp
        · rw [max_eq_left hnn]
          exact div_le_self hnn hlog1
        · rw [max_eq_right hnp]
          exact div_nonpos_of_nonpos_of_nonneg hnp (by linarith)
      have h2 : max ((8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ)) 0 ≤ (n : ℝ) ^ (1 / 2 - ε) := by
        refine max_le (by convert hn using 2; ring) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      exact le_trans h1 h2
    have h8 : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (1 / 2 - ε) ≥ (2 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hsub := h_rpow_lim (2 * Real.exp Real.eulerMascheroniConstant - ε) (1 / 4 - ε) (by linarith)
      filter_upwards [hsub] with n hn
      convert hn using 2; ring
    have h9 : ∀ᶠ n : ℕ in atTop, |SigmaParityStar n| ≤ (1 / 64 : ℝ) * Real.log n := by
      have h := hSig_o.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 64))
      filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog_pos] at hn
      exact (div_le_iff₀ hlog_pos).mp hn.le
    have h10 : ∀ᶠ n : ℕ in atTop,
        C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) +
          (n : ℝ) * Real.log 2 + 2 * Real.log 8 + Real.log 4 ≤ (ε' / 16) * (n : ℝ) * Real.log n := by
      have hlog_big : ∀ᶠ n : ℕ in atTop,
          (C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4 + (1 / 64 : ℝ)) * 2 ≤ (ε' / 16) * Real.log n ∧
          1 ≤ Real.log n ∧ 1 ≤ (n : ℝ) := by
        have ha := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
          (((C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4 + (1 / 64 : ℝ)) * 2) / (ε' / 16))
        have hb := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
        have hc : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) := by
          filter_upwards [eventually_ge_atTop 1] with n hn1; exact_mod_cast hn1
        filter_upwards [ha, hb, hc] with n ha hb hc
        exact ⟨(div_le_iff₀ (by positivity : 0 < ε' / 16)).mp ha |>.trans_eq (by ring), hb, hc⟩
      filter_upwards [hlog_big] with n ⟨hbig, hlog1, hn1⟩
      have h1 : C42 * (n : ℝ) / Real.log n ≤ C42 * (n : ℝ) :=
        div_le_self (by positivity) hlog1
      have h2 : (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) = (n : ℝ) + (1 / 64 : ℝ) * (n : ℝ) * Real.log n := by ring
      have h3 : 2 * Real.log 8 + Real.log 4 ≤ (2 * Real.log 8 + Real.log 4) * (n : ℝ) :=
        le_mul_of_one_le_right (by positivity) hn1
      have h4 : C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) +
            (n : ℝ) * Real.log 2 + 2 * Real.log 8 + Real.log 4 ≤
          (C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4) * (n : ℝ) + (1 / 64 : ℝ) * (n : ℝ) * Real.log n := by
        linarith
      have h5 : (C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4) * (n : ℝ) ≤
          (C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4) * (n : ℝ) * Real.log n := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hlog1) (by positivity)
      have h6 : (C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4) * (n : ℝ) * Real.log n +
          (1 / 64 : ℝ) * (n : ℝ) * Real.log n ≤ (ε' / 16) * (n : ℝ) * Real.log n := by
        have : (C42 + 1 + Real.log 2 + 2 * Real.log 8 + Real.log 4 + (1 / 64 : ℝ)) ≤ ε' / 16 := by
          linarith
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) (by linarith : 0 ≤ Real.log n)]
      linarith
    filter_upwards [h1, h2, h3, h4, h5, h6, h6b, h7, h8, h_log_nfac, h9, h10] with
      n a1 a2 a3 a4 a5 a6 a6b a7 a8 a9 a10 a11
    exact ⟨a1, a2, a3, a4, a5, a6, a6b, a7, a8, a9, a10, a11⟩
  obtain ⟨N₀, hN₀_ev⟩ := eventually_atTop.mp h_ev
  refine ⟨max N₀ 8, le_max_right _ _, ?_⟩
  intro n m hn hn6 hn_ge hsol hk2 x1 δ₁ δ₂ δ hδ
  obtain ⟨hN_ii, hN_42, _, ht25_bd, heps_pow, hexp1, hpow1, h_bd1, h_bd2, hnfac_log, hSig_bd, herr_bd⟩ :=
    hN₀_ev n (le_trans (le_max_left _ _) hn_ge)
  have h42i := hN₀_42 n m hn hn6 hN_42 hsol hk2
  have h42ii := h42ii n m hn hn6 hsol hk2
  rcases h42ii with ⟨hc0_12, Bminus, Bplus, Zminus, Zplus, hB_cop, hZ_cop, hBB_eq, hZZ_eq,
    hx1m_eq, hx1p_eq, hB_diff, _, _, _, _⟩
  obtain ⟨_, _, _, _, _, _, hfac_eq⟩ := critical_eqs_4_1_to_4_3 n m hn hn6 hsol hk2
  have hx1_ge2 : 2 ≤ x1 := by
    have hq_pos : 0 < qn n := qn_pos n
    have hy_pos : 0 < Y1 n (by omega) hn6 := Y1_pos n (by omega) hn6
    have hpell : (x1 : ℤ) ^ 2 - (qn n : ℤ) * (Y1 n (by omega) hn6 : ℤ) ^ 2 = 1 :=
      (pellFundUnit (by omega : 3 ≤ n) hn6).prop
    have : 2 ≤ x1 ^ 2 := by zify; nlinarith
    nlinarith
  have hbn_pos : 0 < Bn n (by omega) hn6 := by
    unfold Bn; split_ifs <;> positivity
  have hzn_pos : 0 < Zn n (by omega) hn6 := Zn_pos n (by omega) hn6
  have hc0_pos : 0 < Nat.gcd (x1 - 1) (x1 + 1) := by
    rcases hc0_12 with h | h <;> omega
  have hBm_pos : 0 < Bminus := by
    by_contra h0; simp only [not_lt, Nat.le_zero] at h0
    rw [h0, zero_mul] at hx1m_eq
    have hdvd : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
    have : x1 - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega) |> fun _ => by
      rw [Nat.div_eq_zero_iff] at hx1m_eq
      rcases hx1m_eq with hc | hlt
      · omega
      · exact absurd hlt (not_lt.mpr (Nat.le_of_dvd (by omega) hdvd))
    omega
  have hBp_pos : 0 < Bplus := by
    by_contra h0; simp only [not_lt, Nat.le_zero] at h0
    rw [h0, zero_mul] at hx1p_eq
    have hdvd : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
    rw [Nat.div_eq_zero_iff] at hx1p_eq
    rcases hx1p_eq with hc | hlt
    · omega
    · have := Nat.le_of_dvd (by omega) hdvd; omega
  have hx1m_4 : (Bminus : ℝ) ^ 4 ≤ (n.factorial : ℝ) := by
    have hBm_le : Bminus ≤ x1 - 1 := by
      calc Bminus ≤ Bminus * Zminus ^ 2 := Nat.le_mul_of_pos_right _ (by
            by_contra h0; simp only [not_lt, Nat.le_zero] at h0
            rw [h0, zero_pow (by norm_num), mul_zero] at hx1m_eq
            have hdvd : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
            rw [Nat.div_eq_zero_iff] at hx1m_eq
            rcases hx1m_eq with hc | hlt
            · omega
            · have := Nat.le_of_dvd (by omega) hdvd; omega)
        _ = (x1 - 1) / Nat.gcd (x1 - 1) (x1 + 1) := hx1m_eq.symm
        _ ≤ x1 - 1 := Nat.div_le_self _ _
    have h1 : (x1 - 1) ^ 4 ≤ 4 * (x1 - 1) * (x1 + 1) * x1 ^ 2 := by
      have : (x1 - 1) ^ 2 ≤ x1 ^ 2 := by nlinarith
      nlinarith
    rw [← hfac_eq] at h1
    exact_mod_cast le_trans (Nat.pow_le_pow_left hBm_le 4) h1
  have hx1p_4 : (Bplus : ℝ) ^ 4 ≤ 8 * (n.factorial : ℝ) := by
    have hBp_le : Bplus ≤ x1 + 1 := by
      calc Bplus ≤ Bplus * Zplus ^ 2 := Nat.le_mul_of_pos_right _ (by
            by_contra h0; simp only [not_lt, Nat.le_zero] at h0
            rw [h0, zero_pow (by norm_num), mul_zero] at hx1p_eq
            have hdvd : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
            rw [Nat.div_eq_zero_iff] at hx1p_eq
            rcases hx1p_eq with hc | hlt
            · omega
            · have := Nat.le_of_dvd (by omega) hdvd; omega)
        _ = (x1 + 1) / Nat.gcd (x1 - 1) (x1 + 1) := hx1p_eq.symm
        _ ≤ x1 + 1 := Nat.div_le_self _ _
    have h1 : (x1 + 1) ^ 4 ≤ 8 * (4 * (x1 - 1) * (x1 + 1) * x1 ^ 2) := by
      have : x1 + 1 ≤ 2 * (x1 - 1) := by omega
      have hsq : (x1 + 1) ^ 2 ≤ 4 * x1 ^ 2 := by nlinarith
      nlinarith
    rw [← hfac_eq] at h1
    exact_mod_cast le_trans (Nat.pow_le_pow_left hBp_le 4) h1
  have hlog_Bm_ub : Real.log (Bminus : ℝ) ≤ (1 / 4 : ℝ) * Real.log (n.factorial : ℝ) + Real.log 8 := by
    have h := Real.log_le_log (by positivity) hx1m_4
    rw [Real.log_pow] at h
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hlog_Bp_ub : Real.log (Bplus : ℝ) ≤ (1 / 4 : ℝ) * Real.log (n.factorial : ℝ) + Real.log 8 := by
    have h := Real.log_le_log (by positivity) hx1p_4
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h
    linarith
  have hlog_BB_lb : (1 / 2 : ℝ) * Real.log (n.factorial : ℝ) - Real.log 8 -
      (1 / 2 : ℝ) * (C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ)) - Real.log 4 ≤
      Real.log (Bminus : ℝ) + Real.log (Bplus : ℝ) := by
    have hfac_le : (n.factorial : ℝ) ≤ 8 * ((x1 : ℝ) ^ 2 - 1) ^ 2 := by
      have h1 : n.factorial = 4 * (x1 ^ 2 - 1) * x1 ^ 2 := by
        rw [hfac_eq]; zify [show 1 ≤ x1 by omega]; ring
      have h2 : x1 ^ 2 ≤ 2 * (x1 ^ 2 - 1) := by omega
      have h3 : n.factorial ≤ 8 * (x1 ^ 2 - 1) ^ 2 := by nlinarith
      exact_mod_cast h3
    have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
      have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
    have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
      rw [← hqy_eq]; exact h42i.2.1.symm
    have hlog_xsq : (1 / 2 : ℝ) * (Real.log (n.factorial : ℝ) - Real.log 8) ≤ Real.log ((x1 : ℝ) ^ 2 - 1) := by
      have h := Real.log_le_log (by positivity) hfac_le
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
      linarith
    have hlog_bn : Real.log ((x1 : ℝ) ^ 2 - 1) - 2 * Real.log (Zn n (by omega) hn6 : ℝ) =
        Real.log (Bn n (by omega) hn6 : ℝ) := by
      have h : ((Bn n (by omega) hn6 : ℝ) * (Zn n (by omega) hn6 : ℝ) ^ 2) = (x1 : ℝ) ^ 2 - 1 := by
        exact_mod_cast hbn_zn
      rw [← h, Real.log_mul (by positivity) (by positivity), Real.log_pow]; ring
    have hlog_zn_ub : 4 * Real.log (Zn n (by omega) hn6 : ℝ) ≤
        C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) := by
      have h1 := (abs_le.mp h42i.1).2
      set c2 : ℝ := if X1 n (by omega) hn6 % 2 = 1 then -1 else 2 * Real.log 2 - 1
      have hc2 : |c2| ≤ 1 := by
        dsimp only [c2]; split_ifs
        · norm_num
        · rw [abs_le]; constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
      have h2 : (c2 - SigmaParityStar n) * (n : ℝ) ≤ (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) := by
        have h3 : c2 - SigmaParityStar n ≤ |c2| + |SigmaParityStar n| := by
          linarith [le_abs_self c2, neg_le_abs (SigmaParityStar n)]
        have h4 : c2 - SigmaParityStar n ≤ 1 + (1 / 64 : ℝ) * Real.log n := by linarith
        exact mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg n)
      linarith
    have hBB_real : (Bminus : ℝ) * (Bplus : ℝ) * (Nat.gcd (x1 - 1) (x1 + 1) : ℝ) ^ 2 =
        (Bn n (by omega) hn6 : ℝ) := by
      have hdvd_c0sq : Nat.gcd (x1 - 1) (x1 + 1) ^ 2 ∣ Bn n (by omega) hn6 := by
        have hd1 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
        have hd2 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
        have h1 : Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2 =
            Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := by
          calc Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2
              = (Nat.gcd (x1 - 1) (x1 + 1) * (Bminus * Zminus ^ 2)) *
                (Nat.gcd (x1 - 1) (x1 + 1) * (Bplus * Zplus ^ 2)) := by ring
            _ = (x1 - 1) * (x1 + 1) := by
                rw [← hx1m_eq, ← hx1p_eq, Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]
            _ = x1 ^ 2 - 1 := by zify [show 1 ≤ x1 by omega]; ring
            _ = Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := hbn_zn.symm
        rw [hZZ_eq] at h1
        have h2 := Nat.eq_of_mul_eq_mul_right (pow_pos hzn_pos 2) h1
        exact ⟨Bminus * Bplus, h2.symm⟩
      exact_mod_cast (by rw [hBB_eq, Nat.div_mul_cancel hdvd_c0sq] : Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 = Bn n (by omega) hn6)
    have hlog_c0_ub : Real.log ((Nat.gcd (x1 - 1) (x1 + 1) : ℝ) ^ 2) ≤ Real.log 4 := by
      refine Real.log_le_log (by positivity) ?_
      rcases hc0_12 with h | h <;> simp [h] <;> norm_num
    have hlog_BB_eq : Real.log (Bminus : ℝ) + Real.log (Bplus : ℝ) + Real.log ((Nat.gcd (x1 - 1) (x1 + 1) : ℝ) ^ 2) =
        Real.log (Bn n (by omega) hn6 : ℝ) := by
      rw [← Real.log_mul (by positivity) (by positivity),
        ← Real.log_mul (by positivity) (by positivity), hBB_real]
    linarith
  have h_main : ∀ (B δ_val : ℕ), 0 < B → B ∣ Bn n (by omega) hn6 →
      (1 / 4 : ℝ) * Real.log (n.factorial : ℝ) - 2 * Real.log 8 -
        (1 / 2 : ℝ) * (C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ)) - Real.log 4 ≤
        Real.log (B : ℝ) →
      (∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ B → p ∣ δ_val) →
      0 < δ_val →
      (omegaNat δ_val : ℝ) ≥ (8 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n ∧
      (δ_val : ℝ) ≥ Real.exp ((2 * Real.exp Real.eulerMascheroniConstant - ε) * (n : ℝ) ^ (1 / 4 : ℝ)) ∧
      (largestPrimeFactor δ_val : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
      (omegaNat δ_val : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
      (δ_val : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε)) := by
    intro B δ_val hB_pos hB_dvd hlog_B_lb hp_dvd_δ hδ_pos
    have hlog_B_ge : ((1 / 4 : ℝ) - ε' / 8) * (n : ℝ) * Real.log n ≤ Real.log (B : ℝ) := by
      linarith
    have hB_prod : B = ∏ p ∈ B.primeFactors, p ^ padicValNat p B := by
      conv_lhs => rw [← Nat.prod_primeFactors_pow_factorization hB_pos.ne']
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def B (Nat.prime_of_mem_primeFactors hp)]
    have hlog_B_sum : Real.log (B : ℝ) = ∑ p ∈ B.primeFactors, (padicValNat p B : ℝ) * Real.log p := by
      conv_lhs => rw [hB_prod]
      push_cast
      rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero))]
      refine Finset.sum_congr rfl fun p hp => by rw [Real.log_pow]
    set P_cut : ℕ := ⌊(n : ℝ) ^ (1 / 2 - ε')⌋₊
    set S_le := B.primeFactors.filter (fun p => p ≤ P_cut)
    set S_gt := B.primeFactors.filter (fun p => P_cut < p)
    have h_split : ∑ p ∈ B.primeFactors, (padicValNat p B : ℝ) * Real.log p =
        ∑ p ∈ S_le, (padicValNat p B : ℝ) * Real.log p +
        ∑ p ∈ S_gt, (padicValNat p B : ℝ) * Real.log p := by
      rw [← Finset.sum_filter_add_sum_filter_not B.primeFactors (fun p => p ≤ P_cut)]
      congr 1; ext p; simp [S_gt]
    have hS_le_ub : ∑ p ∈ S_le, (padicValNat p B : ℝ) * Real.log p ≤
        (n : ℝ) * Real.log 2 + ((1 / 2 - ε') / 2 + ε' / 8) * (n : ℝ) * Real.log n := by
      have h_split2 : ∑ p ∈ S_le, (padicValNat p B : ℝ) * Real.log p ≤
          (if 2 ∈ S_le then (padicValNat 2 B : ℝ) * Real.log 2 else 0) +
          ∑ p ∈ S_le.filter (3 ≤ ·), (padicValNat p B : ℝ) * Real.log p := by
        by_cases h2 : 2 ∈ S_le
        · rw [if_pos h2, ← Finset.add_sum_erase S_le (fun p => (padicValNat p B : ℝ) * Real.log p) h2]
          refine add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) _
          · intro p hp
            rw [Finset.mem_erase] at hp
            have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp.2).1
            exact Finset.mem_filter.mpr ⟨hp.2, by have := hp_prime.two_le; omega⟩
          · intro p hp _
            have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
            exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
        · rw [if_neg h2, zero_add]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro p hp
            have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            have hp_ne2 : p ≠ 2 := fun h => by subst h; exact h2 hp
            exact Finset.mem_filter.mpr ⟨hp, by have := hp_prime.two_le; omega⟩
          · intro p hp _
            have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
            exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
      have h2_ub : (if 2 ∈ S_le then (padicValNat 2 B : ℝ) * Real.log 2 else 0) ≤ (n : ℝ) * Real.log 2 := by
        split_ifs
        · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hv2_le : padicValNat 2 B ≤ padicValNat 2 n.factorial := by
            have hBn_dvd : Bn n (by omega) hn6 ∣ n.factorial := by
              rw [hfac_eq]
              have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
                have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
              have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
                rw [← hqy_eq]; exact h42i.2.1.symm
              refine ⟨(Zn n (by omega) hn6) ^ 2 * 4 * x1 ^ 2, ?_⟩
              calc Bn n (by omega) hn6 * ((Zn n (by omega) hn6) ^ 2 * 4 * x1 ^ 2)
                  = 4 * (Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2) * x1 ^ 2 := by ring
                _ = 4 * (x1 ^ 2 - 1) * x1 ^ 2 := by rw [hbn_zn]
                _ = 4 * (x1 - 1) * (x1 + 1) * x1 ^ 2 := by zify [show 1 ≤ x1 by omega]; ring
            exact padicValNat.dvd_iff_le hB_pos.ne' |>.mp (dvd_trans hB_dvd hBn_dvd) |>.2
          have hv2_fac : (padicValNat 2 n.factorial : ℝ) ≤ n := by
            have hleg := sub_one_mul_padicValNat_factorial (p := 2) n
            have : padicValNat 2 n.factorial ≤ n := by nlinarith
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hv2_fac (Real.log_nonneg (by norm_num))
        · positivity
      have hodd_ub : ∑ p ∈ S_le.filter (3 ≤ ·), (padicValNat p B : ℝ) * Real.log p ≤
          ((1 / 2 - ε') / 2 + ε' / 8) * (n : ℝ) * Real.log n := by
        have hsub : S_le.filter (3 ≤ ·) ⊆
            (Finset.Icc (⌊(n : ℝ) ^ (0 : ℝ)⌋₊ + 1) P_cut).filter
              (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod 2) = 1) := by
          intro p hp
          have hp1 := Finset.mem_filter.mp hp
          have hp2 := Finset.mem_filter.mp hp1.1
          have hp_prime := Nat.prime_of_mem_primeFactors hp2.1
          have hp_dvd_B := Nat.dvd_of_mem_primeFactors hp2.1
          have hp_dvd_Bn : p ∣ Bn n (by omega) hn6 := dvd_trans hp_dvd_B hB_dvd
          have hp_Podd : p ∈ (Podd n).filter (3 ≤ ·) := by
            unfold Bn at hp_dvd_Bn
            have hp_ndvd2 : ¬ p ∣ 2 ^ (padicValNat 2 n.factorial - 2) := by
              intro h; have := hp_prime.dvd_of_dvd_pow h; have := Nat.le_of_dvd (by norm_num) this; omega
            have hp_BnStar : p ∣ BnStar n := by
              split_ifs at hp_dvd_Bn
              · exact (hp_prime.dvd_mul.mp hp_dvd_Bn).resolve_left hp_ndvd2
              · exact hp_dvd_Bn
            unfold BnStar at hp_BnStar
            obtain ⟨q, hq, hqp⟩ := hp_prime.prime.dvd_finset_prod_iff.mp hp_BnStar
            have hq_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
            have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hqp)
            rwa [this]
          have hp_mod2 : (padicValNat p n.factorial : ZMod 2) = 1 := by
            have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_Podd).1).2.2
            have : padicValNat p n.factorial % 2 = 1 := by omega
            simpa [ZMod.natCast_eq_zero_iff] using congrArg (Nat.cast : ℕ → ZMod 2) this
          have hfl0 : ⌊(n : ℝ) ^ (0 : ℝ)⌋₊ = 1 := by simp
          rw [hfl0]
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp2.2⟩, hp_prime, hp_mod2⟩
        have hsum_le : ∑ p ∈ S_le.filter (3 ≤ ·), (padicValNat p B : ℝ) * Real.log p ≤
            ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ (0 : ℝ)⌋₊ + 1) P_cut).filter
              (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod 2) = 1),
              (padicValNat p n.factorial : ℝ) * Real.log p := by
          calc ∑ p ∈ S_le.filter (3 ≤ ·), (padicValNat p B : ℝ) * Real.log p
              ≤ ∑ p ∈ S_le.filter (3 ≤ ·), (padicValNat p n.factorial : ℝ) * Real.log p := by
                refine Finset.sum_le_sum fun p hp => ?_
                have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
                haveI : Fact p.Prime := ⟨hp_prime⟩
                have hp_dvd_B := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
                have hBn_dvd : Bn n (by omega) hn6 ∣ n.factorial := by
                  rw [hfac_eq]
                  have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
                    have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
                  have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
                    rw [← hqy_eq]; exact h42i.2.1.symm
                  refine ⟨(Zn n (by omega) hn6) ^ 2 * 4 * x1 ^ 2, ?_⟩
                  calc Bn n (by omega) hn6 * ((Zn n (by omega) hn6) ^ 2 * 4 * x1 ^ 2)
                      = 4 * (Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2) * x1 ^ 2 := by ring
                    _ = 4 * (x1 ^ 2 - 1) * x1 ^ 2 := by rw [hbn_zn]
                    _ = 4 * (x1 - 1) * (x1 + 1) * x1 ^ 2 := by zify [show 1 ≤ x1 by omega]; ring
                have hv_le := (padicValNat.dvd_iff_le hB_pos.ne').mp (dvd_trans hp_dvd_B hBn_dvd) |>.2
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hv_le) (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
            _ ≤ ∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ (0 : ℝ)⌋₊ + 1) P_cut).filter
                  (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod 2) = 1),
                  (padicValNat p n.factorial : ℝ) * Real.log p := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
                have hp_prime := (Finset.mem_filter.mp hp).2.1
                exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
        exact hsum_le.trans (abs_le.mp ht25_bd).2
      linarith
    have hS_gt_lb : (ε' / 4) * (n : ℝ) * Real.log n ≤
        ∑ p ∈ S_gt, (padicValNat p B : ℝ) * Real.log p := by
      have : (n : ℝ) * Real.log 2 ≤ (ε' / 16) * (n : ℝ) * Real.log n := by
        have : 0 ≤ C42 * (n : ℝ) / Real.log n + (1 + (1 / 64 : ℝ) * Real.log n) * (n : ℝ) + 2 * Real.log 8 + Real.log 4 := by
          have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
          positivity
        linarith
      linarith
    have hS_gt_term_ub : ∀ p ∈ S_gt,
        (padicValNat p B : ℝ) * Real.log p ≤ 2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n := by
      intro p hp
      have hp1 := Finset.mem_filter.mp hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp1.1
      have hp_dvd_B := Nat.dvd_of_mem_primeFactors hp1.1
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have hBn_dvd : Bn n (by omega) hn6 ∣ n.factorial := by
        rw [hfac_eq]
        have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
          have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
        have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
          rw [← hqy_eq]; exact h42i.2.1.symm
        refine ⟨(Zn n (by omega) hn6) ^ 2 * 4 * x1 ^ 2, ?_⟩
        calc Bn n (by omega) hn6 * ((Zn n (by omega) hn6) ^ 2 * 4 * x1 ^ 2)
            = 4 * (Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2) * x1 ^ 2 := by ring
          _ = 4 * (x1 ^ 2 - 1) * x1 ^ 2 := by rw [hbn_zn]
          _ = 4 * (x1 - 1) * (x1 + 1) * x1 ^ 2 := by zify [show 1 ≤ x1 by omega]; ring
      have hp_dvd_fac : p ∣ n.factorial := dvd_trans hp_dvd_B hBn_dvd
      have hp_le_n : p ≤ n := hp_prime.dvd_factorial.mp hp_dvd_fac
      have hv_le : padicValNat p B ≤ padicValNat p n.factorial :=
        (padicValNat.dvd_iff_le hB_pos.ne').mp hp_dvd_fac |>.2
      have hv_fac_ub : (padicValNat p n.factorial : ℝ) ≤ 2 * (n : ℝ) / p := by
        have hleg := sub_one_mul_padicValNat_factorial (p := p) n
        have hp2 : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
          linarith
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
        have h1 : (p - 1) * padicValNat p n.factorial ≤ n := by nlinarith
        have h1R : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) ≤ n := by exact_mod_cast h1
        rw [le_div_iff₀ hp_pos]
        nlinarith
      have hp_gt_rpow : (n : ℝ) ^ (1 / 2 - ε') < p := by
        have : P_cut < p := hp1.2
        exact lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast this)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h_np_ub : (n : ℝ) / p ≤ (n : ℝ) ^ (1 / 2 + ε') := by
        calc (n : ℝ) / p ≤ (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε') :=
              div_le_div_of_nonneg_left hn_pos.le (Real.rpow_pos_of_pos hn_pos _) hp_gt_rpow.le
          _ = (n : ℝ) ^ (1 - (1 / 2 - ε')) := by
              rw [← Real.rpow_one (n : ℝ), ← Real.rpow_sub hn_pos]
              simp
          _ = (n : ℝ) ^ (1 / 2 + ε') := by ring_nf
      have hlogp_le : Real.log p ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast hp_prime.pos) (by exact_mod_cast hp_le_n)
      have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
      calc (padicValNat p B : ℝ) * Real.log p
          ≤ (padicValNat p n.factorial : ℝ) * Real.log n :=
            mul_le_mul (by exact_mod_cast hv_le) hlogp_le hlogp_nn (Nat.cast_nonneg _)
        _ ≤ (2 * ((n : ℝ) / p)) * Real.log n := by
            have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
            exact mul_le_mul_of_nonneg_right (by linarith) hlog_nn
        _ ≤ 2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n := by
            have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
            nlinarith
    have hcard_ge : (n : ℝ) ^ (1 / 2 - ε) ≤ (S_gt.card : ℝ) := by
      have h1 : (ε' / 4) * (n : ℝ) * Real.log n ≤ (S_gt.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n) := by
        calc (ε' / 4) * (n : ℝ) * Real.log n
            ≤ ∑ p ∈ S_gt, (padicValNat p B : ℝ) * Real.log p := hS_gt_lb
          _ ≤ ∑ _p ∈ S_gt, 2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n := Finset.sum_le_sum hS_gt_term_ub
          _ = (S_gt.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have h2 : (ε' / 8) * (n : ℝ) ^ (1 / 2 - ε') ≤ (S_gt.card : ℝ) := by
        have hmul : (ε' / 8) * (n : ℝ) ^ (1 / 2 - ε') * (2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n) =
            (ε' / 4) * (n : ℝ) * Real.log n := by
          calc (ε' / 8) * (n : ℝ) ^ (1 / 2 - ε') * (2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n)
              = (ε' / 4) * ((n : ℝ) ^ (1 / 2 - ε') * (n : ℝ) ^ (1 / 2 + ε')) * Real.log n := by ring
            _ = (ε' / 4) * (n : ℝ) ^ ((1 / 2 - ε') + (1 / 2 + ε')) * Real.log n := by
                rw [← Real.rpow_add hn_pos]
            _ = (ε' / 4) * (n : ℝ) * Real.log n := by ring_nf; simp
        have hpos_den : 0 < 2 * (n : ℝ) ^ (1 / 2 + ε') * Real.log n := by positivity
        exact le_of_mul_le_mul_right (hmul.symm ▸ h1) hpos_den
      exact le_trans heps_pow h2
    have hS_gt_sub : S_gt ⊆ δ_val.primeFactors := by
      intro p hp
      have hp1 := Finset.mem_filter.mp hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp1.1
      have hp_dvd_B := Nat.dvd_of_mem_primeFactors hp1.1
      have hp_gt : (n : ℝ) ^ (1 / 2 - ε') < p :=
        lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hp1.2)
      have hp3 : 3 ≤ p := by
        have : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have : (2.7 : ℝ) < p := by linarith
        by_contra hlt; have : (p : ℝ) ≤ 2 := by exact_mod_cast (by omega : p ≤ 2)
        linarith
      exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_δ p hp_prime hp3 hp_dvd_B, hδ_pos.ne'⟩
    have h_omega : (n : ℝ) ^ (1 / 2 - ε) ≤ (omegaNat δ_val : ℝ) := by
      unfold omegaNat
      exact le_trans hcard_ge (by exact_mod_cast Finset.card_le_card hS_gt_sub)
    have h_lpf : (n : ℝ) ^ (1 / 2 - ε) ≤ (largestPrimeFactor δ_val : ℝ) := by
      have hne : S_gt.Nonempty := Finset.card_pos.mp (by
        by_contra h0; simp only [not_lt, Nat.le_zero] at h0
        rw [h0] at hcard_ge; simp at hcard_ge; linarith)
      obtain ⟨p₀, hp₀⟩ := hne
      have hp₀_gt : (n : ℝ) ^ (1 / 2 - ε') < p₀ :=
        lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast (Finset.mem_filter.mp hp₀).2)
      have hp₀_le : p₀ ≤ largestPrimeFactor δ_val :=
        Finset.le_sup (f := id) (hS_gt_sub hp₀)
      have hpow_le : (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 2 - ε') :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by dsimp [ε']; linarith)
      exact le_trans hpow_le (le_trans hp₀_gt.le (by exact_mod_cast hp₀_le))
    have h_delta : Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ (δ_val : ℝ) := by
      have hprod_dvd : ∏ p ∈ S_gt, p ∣ δ_val := by
        calc ∏ p ∈ S_gt, p ∣ ∏ p ∈ δ_val.primeFactors, p :=
              Finset.prod_dvd_prod_of_subset _ _ id hS_gt_sub
          _ ∣ δ_val := Nat.prod_primeFactors_dvd δ_val
      have hprod_le : (∏ p ∈ S_gt, (p : ℝ)) ≤ (δ_val : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hδ_pos hprod_dvd
      have hprod_ge : (Real.exp 1) ^ S_gt.card ≤ ∏ p ∈ S_gt, (p : ℝ) := by
        calc (Real.exp 1) ^ S_gt.card = ∏ _p ∈ S_gt, Real.exp 1 := by rw [Finset.prod_const]
          _ ≤ ∏ p ∈ S_gt, (p : ℝ) := by
              refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos 1).le) fun p hp => ?_
              have hp_gt : (n : ℝ) ^ (1 / 2 - ε') < p :=
                lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast (Finset.mem_filter.mp hp).2)
              exact le_trans hexp1 hp_gt.le
      have hexp_le : Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ (Real.exp 1) ^ S_gt.card := by
        rw [← Real.rpow_natCast (Real.exp 1), Real.exp_one_rpow]
        exact Real.exp_le_exp.mpr hcard_ge
      exact le_trans hexp_le (le_trans hprod_ge hprod_le)
    exact ⟨le_trans h_bd1 h_omega, le_trans (Real.exp_le_exp.mpr h_bd2) h_delta, h_lpf, h_omega, h_delta⟩
  have hBm_dvd : Bminus ∣ Bn n (by omega) hn6 := by
    have hdvd_c0sq : Nat.gcd (x1 - 1) (x1 + 1) ^ 2 ∣ Bn n (by omega) hn6 := by
      have hd1 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
      have hd2 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
      have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
        have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
      have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
        rw [← hqy_eq]; exact h42i.2.1.symm
      have h1 : Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2 =
          Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := by
        calc Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2
            = (Nat.gcd (x1 - 1) (x1 + 1) * (Bminus * Zminus ^ 2)) *
              (Nat.gcd (x1 - 1) (x1 + 1) * (Bplus * Zplus ^ 2)) := by ring
          _ = (x1 - 1) * (x1 + 1) := by
              rw [← hx1m_eq, ← hx1p_eq, Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]
          _ = x1 ^ 2 - 1 := by zify [show 1 ≤ x1 by omega]; ring
          _ = Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := hbn_zn.symm
      rw [hZZ_eq] at h1
      exact ⟨Bminus * Bplus, (Nat.eq_of_mul_eq_mul_right (pow_pos hzn_pos 2) h1).symm⟩
    exact dvd_trans ⟨Bplus, hBB_eq.symm⟩ (Nat.div_dvd_of_dvd hdvd_c0sq)
  have hBp_dvd : Bplus ∣ Bn n (by omega) hn6 := by
    have hdvd_c0sq : Nat.gcd (x1 - 1) (x1 + 1) ^ 2 ∣ Bn n (by omega) hn6 := by
      have hd1 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
      have hd2 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
      have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
        have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
      have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
        rw [← hqy_eq]; exact h42i.2.1.symm
      have h1 : Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2 =
          Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := by
        calc Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2
            = (Nat.gcd (x1 - 1) (x1 + 1) * (Bminus * Zminus ^ 2)) *
              (Nat.gcd (x1 - 1) (x1 + 1) * (Bplus * Zplus ^ 2)) := by ring
          _ = (x1 - 1) * (x1 + 1) := by
              rw [← hx1m_eq, ← hx1p_eq, Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]
          _ = x1 ^ 2 - 1 := by zify [show 1 ≤ x1 by omega]; ring
          _ = Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := hbn_zn.symm
      rw [hZZ_eq] at h1
      exact ⟨Bminus * Bplus, (Nat.eq_of_mul_eq_mul_right (pow_pos hzn_pos 2) h1).symm⟩
    exact dvd_trans ⟨Bminus, by rw [mul_comm, hBB_eq]⟩ (Nat.div_dvd_of_dvd hdvd_c0sq)
  have hp_dvd_δ1 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ Bminus → p ∣ δ₁ := by
    intro p hp hp3 hpB
    have hp_ndvd_Bp : ¬ p ∣ Bplus := fun h => by
      have := Nat.dvd_gcd hpB h; rw [hB_cop] at this; exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
    have hp_ndvd_c0 : ¬ p ∣ Nat.gcd (x1 - 1) (x1 + 1) := fun h => by
      rcases hc0_12 with hc | hc <;> rw [hc] at h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
    haveI : Fact p.Prime := ⟨hp⟩
    have hx1m_prod : x1 - 1 = Nat.gcd (x1 - 1) (x1 + 1) * Bminus * Zminus ^ 2 := by
      have := Nat.mul_div_cancel' (Nat.gcd_dvd_left (x1 - 1) (x1 + 1))
      rw [← hx1m_eq] at this; linarith [this]
    have hv_x1m : padicValNat p (x1 - 1) = padicValNat p Bminus + 2 * padicValNat p Zminus := by
      have hZm_ne : Zminus ≠ 0 := fun h => by
        rw [h, zero_pow (by norm_num), mul_zero, mul_zero] at hx1m_prod; omega
      rw [hx1m_prod, padicValNat.mul (mul_ne_zero hc0_pos.ne' hBm_pos.ne') (pow_ne_zero 2 hZm_ne),
        padicValNat.mul hc0_pos.ne' hBm_pos.ne', padicValNat.eq_zero_of_not_dvd hp_ndvd_c0, zero_add,
        padicValNat.pow Zminus 2]
    have hv_Bm : padicValNat p Bminus = padicValNat p (Bn n (by omega) hn6) := by
      have hc0sq_ndvd : ¬ p ∣ Nat.gcd (x1 - 1) (x1 + 1) ^ 2 := fun h => hp_ndvd_c0 (hp.dvd_of_dvd_pow h)
      have hdvd_c0sq : Nat.gcd (x1 - 1) (x1 + 1) ^ 2 ∣ Bn n (by omega) hn6 := by
        have hd1 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
        have hd2 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
        have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
          have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
        have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
          rw [← hqy_eq]; exact h42i.2.1.symm
        have h1 : Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2 =
            Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := by
          calc Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2
              = (Nat.gcd (x1 - 1) (x1 + 1) * (Bminus * Zminus ^ 2)) *
                (Nat.gcd (x1 - 1) (x1 + 1) * (Bplus * Zplus ^ 2)) := by ring
            _ = (x1 - 1) * (x1 + 1) := by
                rw [← hx1m_eq, ← hx1p_eq, Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]
            _ = x1 ^ 2 - 1 := by zify [show 1 ≤ x1 by omega]; ring
            _ = Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := hbn_zn.symm
        rw [hZZ_eq] at h1
        exact ⟨Bminus * Bplus, (Nat.eq_of_mul_eq_mul_right (pow_pos hzn_pos 2) h1).symm⟩
      have hBn_eq : Bn n (by omega) hn6 = Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 := by
        rw [hBB_eq, Nat.div_mul_cancel hdvd_c0sq]
      rw [hBn_eq, padicValNat.mul (mul_ne_zero hBm_pos.ne' hBp_pos.ne') (pow_ne_zero 2 hc0_pos.ne'),
        padicValNat.mul hBm_pos.ne' hBp_pos.ne', padicValNat.eq_zero_of_not_dvd hp_ndvd_Bp,
        padicValNat.eq_zero_of_not_dvd hc0sq_ndvd, add_zero, add_zero]
    have hv_Bn_odd : ¬ 2 ∣ padicValNat p (Bn n (by omega) hn6) := by
      have hp_dvd_Bn : p ∣ Bn n (by omega) hn6 := dvd_trans hpB hBm_dvd
      have hp_ndvd2 : ¬ p ∣ 2 ^ (padicValNat 2 n.factorial - 2) := fun h => by
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      unfold Bn at hp_dvd_Bn ⊢
      have hv2 : padicValNat p (2 ^ (padicValNat 2 n.factorial - 2)) = 0 :=
        padicValNat.eq_zero_of_not_dvd hp_ndvd2
      have hBnStar_eq : padicValNat p (BnStar n) = padicValNat p n.factorial := by
        have hp_BnStar : p ∣ BnStar n := by
          split_ifs at hp_dvd_Bn
          · exact (hp.dvd_mul.mp hp_dvd_Bn).resolve_left hp_ndvd2
          · exact hp_dvd_Bn
        unfold BnStar at hp_BnStar ⊢
        obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finset_prod_iff.mp hp_BnStar
        have hq_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow hqp)
        rw [← this] at hq
        rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hp]
        simp [hq]
      have hp_mem : p ∈ (Podd n).filter (3 ≤ ·) := by
        have hp_BnStar : p ∣ BnStar n := by
          split_ifs at hp_dvd_Bn
          · exact (hp.dvd_mul.mp hp_dvd_Bn).resolve_left hp_ndvd2
          · exact hp_dvd_Bn
        unfold BnStar at hp_BnStar
        obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finset_prod_iff.mp hp_BnStar
        have hq_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow hqp)
        rwa [this]
      have hodd := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_mem).1).2.2
      split_ifs
      · rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) (BnStar_pos n).ne', hv2, zero_add, hBnStar_eq]; omega
      · rw [hBnStar_eq]; omega
    have hv_x1m_odd : ¬ 2 ∣ padicValNat p (x1 - 1) := by
      rw [hv_x1m, hv_Bm]; omega
    refine Finset.dvd_prod_of_mem _ ?_
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hpB (by rw [hx1m_prod]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _), by omega⟩, hv_x1m_odd⟩
  have hp_dvd_δ2 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ Bplus → p ∣ δ₂ := by
    intro p hp hp3 hpB
    have hp_ndvd_Bm : ¬ p ∣ Bminus := fun h => by
      have := Nat.dvd_gcd h hpB; rw [hB_cop] at this; exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
    have hp_ndvd_c0 : ¬ p ∣ Nat.gcd (x1 - 1) (x1 + 1) := fun h => by
      rcases hc0_12 with hc | hc <;> rw [hc] at h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
    haveI : Fact p.Prime := ⟨hp⟩
    have hx1p_prod : x1 + 1 = Nat.gcd (x1 - 1) (x1 + 1) * Bplus * Zplus ^ 2 := by
      have := Nat.mul_div_cancel' (Nat.gcd_dvd_right (x1 - 1) (x1 + 1))
      rw [← hx1p_eq] at this; linarith [this]
    have hv_x1p : padicValNat p (x1 + 1) = padicValNat p Bplus + 2 * padicValNat p Zplus := by
      have hZp_ne : Zplus ≠ 0 := fun h => by
        rw [h, zero_pow (by norm_num), mul_zero, mul_zero] at hx1p_prod; omega
      rw [hx1p_prod, padicValNat.mul (mul_ne_zero hc0_pos.ne' hBp_pos.ne') (pow_ne_zero 2 hZp_ne),
        padicValNat.mul hc0_pos.ne' hBp_pos.ne', padicValNat.eq_zero_of_not_dvd hp_ndvd_c0, zero_add,
        padicValNat.pow Zplus 2]
    have hv_Bp : padicValNat p Bplus = padicValNat p (Bn n (by omega) hn6) := by
      have hc0sq_ndvd : ¬ p ∣ Nat.gcd (x1 - 1) (x1 + 1) ^ 2 := fun h => hp_ndvd_c0 (hp.dvd_of_dvd_pow h)
      have hdvd_c0sq : Nat.gcd (x1 - 1) (x1 + 1) ^ 2 ∣ Bn n (by omega) hn6 := by
        have hd1 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 - 1 := Nat.gcd_dvd_left _ _
        have hd2 : Nat.gcd (x1 - 1) (x1 + 1) ∣ x1 + 1 := Nat.gcd_dvd_right _ _
        have hqy_eq : qn n * Y1 n (by omega) hn6 ^ 2 = x1 ^ 2 - 1 := by
          have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [show 1 ≤ x1 ^ 2 by nlinarith]; linarith
        have hbn_zn : Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 = x1 ^ 2 - 1 := by
          rw [← hqy_eq]; exact h42i.2.1.symm
        have h1 : Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2 =
            Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := by
          calc Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 * (Zminus * Zplus) ^ 2
              = (Nat.gcd (x1 - 1) (x1 + 1) * (Bminus * Zminus ^ 2)) *
                (Nat.gcd (x1 - 1) (x1 + 1) * (Bplus * Zplus ^ 2)) := by ring
            _ = (x1 - 1) * (x1 + 1) := by
                rw [← hx1m_eq, ← hx1p_eq, Nat.mul_div_cancel' hd1, Nat.mul_div_cancel' hd2]
            _ = x1 ^ 2 - 1 := by zify [show 1 ≤ x1 by omega]; ring
            _ = Bn n (by omega) hn6 * (Zn n (by omega) hn6) ^ 2 := hbn_zn.symm
        rw [hZZ_eq] at h1
        exact ⟨Bminus * Bplus, (Nat.eq_of_mul_eq_mul_right (pow_pos hzn_pos 2) h1).symm⟩
      have hBn_eq : Bn n (by omega) hn6 = Bminus * Bplus * Nat.gcd (x1 - 1) (x1 + 1) ^ 2 := by
        rw [hBB_eq, Nat.div_mul_cancel hdvd_c0sq]
      rw [hBn_eq, padicValNat.mul (mul_ne_zero hBm_pos.ne' hBp_pos.ne') (pow_ne_zero 2 hc0_pos.ne'),
        padicValNat.mul hBm_pos.ne' hBp_pos.ne', padicValNat.eq_zero_of_not_dvd hp_ndvd_Bm, zero_add,
        padicValNat.eq_zero_of_not_dvd hc0sq_ndvd, add_zero]
    have hv_Bn_odd : ¬ 2 ∣ padicValNat p (Bn n (by omega) hn6) := by
      have hp_dvd_Bn : p ∣ Bn n (by omega) hn6 := dvd_trans hpB hBp_dvd
      have hp_ndvd2 : ¬ p ∣ 2 ^ (padicValNat 2 n.factorial - 2) := fun h => by
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      unfold Bn at hp_dvd_Bn ⊢
      have hv2 : padicValNat p (2 ^ (padicValNat 2 n.factorial - 2)) = 0 :=
        padicValNat.eq_zero_of_not_dvd hp_ndvd2
      have hBnStar_eq : padicValNat p (BnStar n) = padicValNat p n.factorial := by
        have hp_BnStar : p ∣ BnStar n := by
          split_ifs at hp_dvd_Bn
          · exact (hp.dvd_mul.mp hp_dvd_Bn).resolve_left hp_ndvd2
          · exact hp_dvd_Bn
        unfold BnStar at hp_BnStar ⊢
        obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finset_prod_iff.mp hp_BnStar
        have hq_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow hqp)
        rw [← this] at hq
        rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hp]
        simp [hq]
      have hp_mem : p ∈ (Podd n).filter (3 ≤ ·) := by
        have hp_BnStar : p ∣ BnStar n := by
          split_ifs at hp_dvd_Bn
          · exact (hp.dvd_mul.mp hp_dvd_Bn).resolve_left hp_ndvd2
          · exact hp_dvd_Bn
        unfold BnStar at hp_BnStar
        obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finset_prod_iff.mp hp_BnStar
        have hq_prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow hqp)
        rwa [this]
      have hodd := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_mem).1).2.2
      split_ifs
      · rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) (BnStar_pos n).ne', hv2, zero_add, hBnStar_eq]; omega
      · rw [hBnStar_eq]; omega
    have hv_x1p_odd : ¬ 2 ∣ padicValNat p (x1 + 1) := by
      rw [hv_x1p, hv_Bp]; omega
    refine Finset.dvd_prod_of_mem _ ?_
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hpB (by rw [hx1p_prod]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _), by omega⟩, hv_x1p_odd⟩
  have hδ1_pos : 0 < δ₁ := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hδ2_pos : 0 < δ₂ := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  rcases Finset.mem_insert.mp hδ with rfl | hδ2
  · exact h_main Bminus δ₁ hBm_pos hBm_dvd (by linarith) hp_dvd_δ1 hδ1_pos
  · rw [Finset.mem_singleton] at hδ2; subst hδ2
    exact h_main Bplus δ₂ hBp_pos hBp_dvd (by linarith) hp_dvd_δ2 hδ2_pos

/-! ### 4.2 Stickelberger Base-p Reciprocity and Conductor-Free Quadratic Residue Lock -/

theorem lemma_4_3_indexed (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 1 ≤ n) :
    ((n.factorial / p ^ padicValNat p n.factorial : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ padicValNat p n.factorial *
        ∏ j ∈ Finset.range (Nat.digits p n).length,
          (((Nat.digits p n).getD j 0).factorial : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hstrong : ∀ m : ℕ,
      ((m.factorial / p ^ padicValNat p m.factorial : ℕ) : ZMod p) =
        (-1 : ZMod p) ^ padicValNat p m.factorial *
          ∏ j ∈ Finset.range (Nat.digits p m).length,
            (((Nat.digits p m).getD j 0).factorial : ZMod p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        set q := m / p
        set r := m % p
        have hq_lt : q < m := Nat.div_lt_self hm_pos hp.one_lt
        have hmr_eq : m = p * q + r := (Nat.div_add_mod m p).symm
        have hr_lt : r < p := Nat.mod_lt m hp.pos
        let M1 : ℕ := ∏ t ∈ Finset.range q, ∏ s ∈ Finset.Icc 1 (p - 1), (p * t + s)
        let M2 : ℕ := ∏ s ∈ Finset.Icc 1 r, (p * q + s)
        have hM1_mod : (M1 : ZMod p) = (-1 : ZMod p) ^ q := by
          dsimp only [M1]
          push_cast
          refine Finset.prod_congr rfl fun t _ => ?_
          have hwil := ZMod.wilsons_lemma p
          have hprod_eq : ∏ s ∈ Finset.Icc 1 (p - 1), (((p : ZMod p) * (t : ZMod p)) + (s : ZMod p)) =
              ((p - 1).factorial : ZMod p) := by
            simp only [ZMod.natCast_self, zero_mul, zero_add]
            have h1 : ∏ s ∈ Finset.Icc 1 (p - 1), (s : ZMod p) =
                ∏ s ∈ Finset.range (p - 1), ((s + 1 : ℕ) : ZMod p) := by
              refine Finset.prod_nbij' (fun s => s - 1) (fun s => s + 1) ?_ ?_ ?_ ?_ ?_
              · intro s hs; rw [Finset.mem_Icc] at hs; rw [Finset.mem_range]; omega
              · intro s hs; rw [Finset.mem_range] at hs; rw [Finset.mem_Icc]; omega
              · intro s hs; rw [Finset.mem_Icc] at hs; omega
              · intro s _; omega
              · intro s hs; rw [Finset.mem_Icc] at hs; congr 1; omega
            rw [h1]
            have hfac_p : (p - 1).factorial = ∏ s ∈ Finset.range (p - 1), (s + 1) := by
              rw [Nat.factorial_eq_prod_range_add_one]
            rw [hfac_p, Nat.cast_prod]
          rw [hprod_eq, hwil]
        have hM2_mod : (M2 : ZMod p) = (r.factorial : ZMod p) := by
          dsimp only [M2]
          push_cast
          simp only [ZMod.natCast_self, zero_mul, zero_add]
          have h1 : ∏ s ∈ Finset.Icc 1 r, (s : ZMod p) = ∏ s ∈ Finset.range r, ((s + 1 : ℕ) : ZMod p) := by
            refine Finset.prod_nbij' (fun s => s - 1) (fun s => s + 1) ?_ ?_ ?_ ?_ ?_
            · intro s hs; rw [Finset.mem_Icc] at hs; rw [Finset.mem_range]; omega
            · intro s hs; rw [Finset.mem_range] at hs; rw [Finset.mem_Icc]; omega
            · intro s hs; rw [Finset.mem_Icc] at hs; omega
            · intro s _; omega
            · intro s hs; rw [Finset.mem_Icc] at hs; congr 1; omega
          rw [h1, Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
        have hfac_decomp : m.factorial = p ^ q * q.factorial * (M1 * M2) := by
          have hfac_Icc : m.factorial = ∏ i ∈ Finset.Icc 1 m, i := by
            rw [Nat.factorial_eq_prod_range_add_one]
            refine Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
            · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
            · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
            · intro i _; omega
            · intro i hi; rw [Finset.mem_Icc] at hi; omega
            · intro i _; rfl
          rw [hfac_Icc, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 m) (fun i => p ∣ i)]
          have hdiv_prod : ∏ i ∈ (Finset.Icc 1 m).filter (fun i => p ∣ i), i = p ^ q * q.factorial := by
            have h1 : ∏ i ∈ (Finset.Icc 1 m).filter (fun i => p ∣ i), i =
                ∏ j ∈ Finset.Icc 1 q, (p * j) := by
              refine Finset.prod_nbij' (fun i => i / p) (fun j => p * j) ?_ ?_ ?_ ?_ ?_
              · intro i hi
                rw [Finset.mem_filter, Finset.mem_Icc] at hi
                rw [Finset.mem_Icc]
                refine ⟨Nat.div_pos (Nat.le_of_dvd hi.1.1 hi.2) hp.pos, Nat.div_le_div_right hi.1.2⟩
              · intro j hj
                rw [Finset.mem_Icc] at hj
                rw [Finset.mem_filter, Finset.mem_Icc]
                exact ⟨⟨by nlinarith [hp.pos], by nlinarith⟩, dvd_mul_right p j⟩
              · intro i hi
                rw [Finset.mem_filter] at hi
                exact Nat.mul_div_cancel' hi.2
              · intro j _; exact Nat.mul_div_cancel_left j hp.pos
              · intro i hi
                rw [Finset.mem_filter] at hi
                exact (Nat.mul_div_cancel' hi.2).symm
            rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
            congr 1
            rw [Nat.factorial_eq_prod_range_add_one]
            refine Finset.prod_nbij' (fun j => j - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
            · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
            · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Icc]; omega
            · intro j hj; rw [Finset.mem_Icc] at hj; omega
            · intro j _; omega
            · intro j hj; rw [Finset.mem_Icc] at hj; omega
          have hndiv_prod : ∏ i ∈ (Finset.Icc 1 m).filter (fun i => ¬ p ∣ i), i = M1 * M2 := by
            have hdisj : Disjoint ((Finset.Icc 1 m).filter (fun i => ¬ p ∣ i ∧ i ≤ p * q))
                ((Finset.Icc 1 m).filter (fun i => ¬ p ∣ i ∧ p * q < i)) := by
              rw [Finset.disjoint_left]; intro i h1 h2
              simp only [Finset.mem_filter] at h1 h2; omega
            have hunion : (Finset.Icc 1 m).filter (fun i => ¬ p ∣ i) =
                (Finset.Icc 1 m).filter (fun i => ¬ p ∣ i ∧ i ≤ p * q) ∪
                (Finset.Icc 1 m).filter (fun i => ¬ p ∣ i ∧ p * q < i) := by
              ext i; simp only [Finset.mem_filter, Finset.mem_union]; tauto
            rw [hunion, Finset.prod_union hdisj]
            congr 1
            · rw [← Finset.prod_product']
              refine Finset.prod_nbij' (fun i => (i / p, i % p)) (fun ts => p * ts.1 + ts.2) ?_ ?_ ?_ ?_ ?_
              · intro i hi
                simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_product, Finset.mem_range] at hi ⊢
                have hmod_ne : i % p ≠ 0 := fun h => hi.2.1 (Nat.dvd_of_mod_eq_zero h)
                have hmod_pos : 1 ≤ i % p := Nat.pos_of_ne_zero hmod_ne
                have hmod_lt : i % p ≤ p - 1 := by have := Nat.mod_lt i hp.pos; omega
                have hdiv_lt : i / p < q := by
                  by_contra hge
                  push_neg at hge
                  have : p * q < p * (i / p) + i % p := by nlinarith
                  rw [Nat.div_add_mod] at this; omega
                exact ⟨hdiv_lt, hmod_pos, hmod_lt⟩
              · intro ⟨t, s⟩ hts
                simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc, Finset.mem_filter] at hts ⊢
                have hnd : ¬ p ∣ p * t + s := by
                  intro h
                  have h1 : p ∣ s := (Nat.dvd_add_right (dvd_mul_right p t)).mp h
                  have h2 := Nat.le_of_dvd hts.2.1 h1; omega
                exact ⟨⟨by omega, by nlinarith⟩, hnd, by nlinarith⟩
              · intro i _; exact Nat.div_add_mod i p
              · intro ⟨t, s⟩ hts
                simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hts
                ext
                · dsimp; rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), add_zero]
                · dsimp; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
              · intro i _; exact (Nat.div_add_mod i p).symm
            · refine Finset.prod_nbij' (fun i => i - p * q) (fun s => p * q + s) ?_ ?_ ?_ ?_ ?_
              · intro i hi
                simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢; omega
              · intro s hs
                simp only [Finset.mem_Icc, Finset.mem_filter] at hs ⊢
                have hnd : ¬ p ∣ p * q + s := by
                  intro h
                  have h1 : p ∣ s := (Nat.dvd_add_right (dvd_mul_right p q)).mp h
                  have h2 := Nat.le_of_dvd hs.1 h1; omega
                exact ⟨⟨by omega, by omega⟩, hnd, by omega⟩
              · intro i hi; simp only [Finset.mem_filter] at hi; omega
              · intro s _; omega
              · intro i hi; simp only [Finset.mem_filter] at hi; omega
          rw [hdiv_prod, hndiv_prod, mul_assoc]
        have hM_ndvd : ¬ p ∣ M1 * M2 := by
          intro h
          have h0 : ((M1 * M2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ p).mpr h
          rw [Nat.cast_mul, hM1_mod, hM2_mod] at h0
          have hr_ndvd : ¬ p ∣ r.factorial := by
            rw [hp.prime.dvd_factorial]; omega
          have hr0 : (r.factorial : ZMod p) ≠ 0 := fun h => hr_ndvd ((ZMod.natCast_zmod_eq_zero_iff_dvd _ p).mp h)
          have h10 : (-1 : ZMod p) ^ q ≠ 0 := pow_ne_zero q (by norm_num)
          exact mul_ne_zero h10 hr0 h0
        have hval_eq : padicValNat p m.factorial = q + padicValNat p q.factorial := by
          rw [hfac_decomp, padicValNat.mul (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Nat.factorial_ne_zero q))
            (by intro h0; rw [h0] at hM_ndvd; exact hM_ndvd (dvd_zero _)),
            padicValNat.eq_zero_of_not_dvd hM_ndvd, add_zero,
            padicValNat.mul (pow_ne_zero _ hp.ne_zero) (Nat.factorial_ne_zero q),
            padicValNat.pow p q, padicValNat.self hp.one_lt, mul_one]
        have hdiv_eq : m.factorial / p ^ padicValNat p m.factorial =
            (q.factorial / p ^ padicValNat p q.factorial) * (M1 * M2) := by
          have hdvd_q : p ^ padicValNat p q.factorial ∣ q.factorial := pow_padicValNat_dvd
          rw [hfac_decomp, hval_eq, pow_add]
          calc (p ^ q * q.factorial * (M1 * M2)) / (p ^ q * p ^ padicValNat p q.factorial)
              = (p ^ q * (q.factorial * (M1 * M2))) / (p ^ q * p ^ padicValNat p q.factorial) := by ring_nf
            _ = (q.factorial * (M1 * M2)) / p ^ padicValNat p q.factorial :=
                Nat.mul_div_mul_left _ _ (pow_pos hp.pos q)
            _ = (q.factorial / p ^ padicValNat p q.factorial) * (M1 * M2) :=
                Nat.div_mul_right_comm hdvd_q (M1 * M2)
        rw [hdiv_eq, Nat.cast_mul, Nat.cast_mul, hM1_mod, hM2_mod, ih q hq_lt, hval_eq, pow_add]
        have hdig : ∏ j ∈ Finset.range (Nat.digits p m).length, (((Nat.digits p m).getD j 0).factorial : ZMod p) =
            (r.factorial : ZMod p) * ∏ j ∈ Finset.range (Nat.digits p q).length, (((Nat.digits p q).getD j 0).factorial : ZMod p) := by
          rw [Nat.digits_def' hp.one_lt hm_pos]
          simp only [List.length_cons, Finset.prod_range_succ', List.getD_cons_zero, List.getD_cons_succ, r, q]
          rw [mul_comm]
        rw [hdig]
        ring
  exact hstrong n

theorem lemma_4_3 (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 1 ≤ n) :
    ((n.factorial / p ^ padicValNat p n.factorial : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ padicValNat p n.factorial *
        ∏ d ∈ (Nat.digits p n).toFinset, (d.factorial : ZMod p) ^ ((Nat.digits p n).count d) := by
  rw [lemma_4_3_indexed p n hp hp3 hn]
  congr 1
  have h1 : ∏ j ∈ Finset.range (Nat.digits p n).length, (((Nat.digits p n).getD j 0).factorial : ZMod p) =
      ((Nat.digits p n).map (fun d => (d.factorial : ZMod p))).prod := by
    clear hn hp3 hp
    induction (Nat.digits p n) with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, Finset.prod_range_succ', List.map_cons, List.prod_cons,
        List.getD_cons_zero, List.getD_cons_succ]
      rw [mul_comm, ih]
  rw [h1]
  have h2 : ∀ (l : List ℕ) (f : ℕ → ZMod p),
      (l.map f).prod = ∏ d ∈ l.toFinset, f d ^ l.count d := by
    intro l f
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.toFinset_cons, ih]
      by_cases ha : a ∈ l
      · have ha_mem : a ∈ l.toFinset := List.mem_toFinset.mpr ha
        rw [Finset.insert_eq_of_mem ha_mem, ← Finset.mul_prod_erase l.toFinset _ ha_mem,
          ← Finset.mul_prod_erase l.toFinset _ ha_mem, List.count_cons_self, pow_succ', mul_assoc]
        congr 2
        refine Finset.prod_congr rfl fun d hd => ?_
        have hne : d ≠ a := (Finset.mem_erase.mp hd).1
        rw [List.count_cons_of_ne hne]
      · have ha_nmem : a ∉ l.toFinset := fun h => ha (List.mem_toFinset.mp h)
        rw [Finset.prod_insert ha_nmem, List.count_cons_self, pow_one]
        congr 1
        refine Finset.prod_congr rfl fun d hd => ?_
        have hne : d ≠ a := fun h => ha_nmem (h ▸ hd)
        rw [List.count_cons_of_ne hne]
  exact h2 (Nat.digits p n) (fun d => (d.factorial : ZMod p))

theorem theorem_4_4_i (n p : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hpeven : p ∈ Peven n) :
    jacobiSym (-(qn n : ℤ)) p =
      jacobiSym (-1 : ℤ) p *
        ∏ j ∈ Finset.range (Nat.digits p n).length,
          jacobiSym ((((Nat.digits p n).getD j 0).factorial : ℤ)) p ∧
    (∀ r : ℕ, 1 ≤ r → 2 * r < p → (n : ℝ) / (2 * r + 1) < p → (p : ℝ) ≤ (n : ℝ) / (2 * r) →
      jacobiSym (-(qn n : ℤ)) p =
        jacobiSym (-(((2 * r).factorial * (n - 2 * r * p).factorial : ℕ) : ℤ)) p ∧
      (p % 4 = 1 → ∀ m0 : ℕ, n - 2 * r * p = (p - 1) / 2 - m0 →
        jacobiSym (-(qn n : ℤ)) p =
          jacobiSym (((2 * r).factorial : ℤ)) p *
            (jacobiSym (2 : ℤ) p) ^ (m0 + 1) *
            ∏ j ∈ Finset.range m0, jacobiSym ((2 * j + 1 : ℤ)) p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have heven : 2 ∣ padicValNat p n.factorial := (Finset.mem_filter.mp hpeven).2.2
  have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpeven).1).2
  have hndvd_qn : ¬ p ∣ qn n := by
    intro h
    rw [qn_eq_prod_Podd] at h
    obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finset_prod_iff.mp h
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp (Finset.mem_filter.mp hq).2.1).mp hqp
    subst this
    exact (Podd_disjoint_Peven n).le_bot (Finset.mem_inter.mpr ⟨hq, hpeven⟩)
  have hfac_eq := factorial_eq_qn_mul_sn_sq n
  have hv_sn : padicValNat p n.factorial = 2 * padicValNat p (sn n) := by
    conv_lhs => rw [hfac_eq]
    rw [padicValNat.mul (qn_pos n).ne' (pow_ne_zero 2 (sn_pos n).ne'),
      padicValNat.eq_zero_of_not_dvd hndvd_qn, zero_add, padicValNat.pow (sn n) 2]
  set t := padicValNat p (sn n)
  set s' := sn n / p ^ t
  have hpt_dvd : p ^ t ∣ sn n := pow_padicValNat_dvd
  have hs'_ndvd : ¬ p ∣ s' := by
    intro h
    have : p ^ (t + 1) ∣ sn n := by
      rw [pow_succ, ← Nat.div_mul_cancel hpt_dvd]
      exact mul_dvd_mul_right h (p ^ t)
    have := (padicValNat_dvd_iff_le (sn_pos n).ne').mp this
    omega
  have hdiv_fac : n.factorial / p ^ padicValNat p n.factorial = qn n * s' ^ 2 := by
    have h1 : n.factorial = p ^ (2 * t) * (qn n * s' ^ 2) := by
      rw [hfac_eq]
      calc qn n * (sn n) ^ 2 = qn n * (p ^ t * s') ^ 2 := by rw [Nat.mul_div_cancel' hpt_dvd]
        _ = p ^ (2 * t) * (qn n * s' ^ 2) := by ring
    rw [hv_sn, h1, Nat.mul_div_cancel_left _ (pow_pos hp.pos (2 * t))]
  have hpart1 : jacobiSym (-(qn n : ℤ)) p =
      jacobiSym (-1 : ℤ) p *
        ∏ j ∈ Finset.range (Nat.digits p n).length,
          jacobiSym ((((Nat.digits p n).getD j 0).factorial : ℤ)) p := by
    have h_stick := lemma_4_3_indexed p n hp hp3 (by omega)
    rw [hv_sn, show (-1 : ZMod p) ^ (2 * t) = 1 by rw [pow_mul]; simp, one_mul] at h_stick
    have h_mod : (-(qn n : ℤ) * (s' : ℤ) ^ 2 : ZMod p) =
        (-1 : ZMod p) * ∏ j ∈ Finset.range (Nat.digits p n).length, (((Nat.digits p n).getD j 0).factorial : ZMod p) := by
      have h1 : (-(qn n : ℤ) * (s' : ℤ) ^ 2 : ZMod p) = -(((qn n * s' ^ 2 : ℕ) : ZMod p)) := by push_cast; ring
      rw [h1, ← hdiv_fac, h_stick]; ring
    have h_int : ((-(qn n : ℤ) * (s' : ℤ) ^ 2 : ℤ) : ZMod p) =
        (((-1 : ℤ) * ∏ j ∈ Finset.range (Nat.digits p n).length, (((Nat.digits p n).getD j 0).factorial : ℤ) : ℤ) : ZMod p) := by
      push_cast; exact h_mod
    rw [ZMod.intCast_eq_intCast_iff] at h_int
    have hjac_eq : jacobiSym (-(qn n : ℤ) * (s' : ℤ) ^ 2) p =
        jacobiSym ((-1 : ℤ) * ∏ j ∈ Finset.range (Nat.digits p n).length, (((Nat.digits p n).getD j 0).factorial : ℤ)) p := by
      rw [← jacobiSym.mod_left _ p, ← jacobiSym.mod_left ((-1 : ℤ) * _) p]
      have h2 := jacobiSym.mod_left (-(qn n : ℤ) * (s' : ℤ) ^ 2) p
      have h3 := jacobiSym.mod_left ((-1 : ℤ) * ∏ j ∈ Finset.range (Nat.digits p n).length, (((Nat.digits p n).getD j 0).factorial : ℤ)) p
      rw [h_int] at h2
      linarith
    rw [jacobiSym.mul_left, jacobiSym.sq_one (hp.coprime_iff_not_dvd.mpr hs'_ndvd).symm, mul_one,
      jacobiSym.mul_left, jacobiSym.prod_left] at hjac_eq
    exact hjac_eq
  refine ⟨hpart1, ?_⟩
  intro r hr1 hrp hlo hhi
  have h2rp_le : 2 * r * p ≤ n := by
    have : (p : ℝ) * (2 * r) ≤ n := (le_div_iff₀ (by positivity)).mp hhi
    exact_mod_cast (by linarith : (2 * r * p : ℝ) ≤ n)
  have hn_lt : n < (2 * r + 1) * p := by
    have : (n : ℝ) < (p : ℝ) * (2 * r + 1) := (div_lt_iff₀ (by positivity)).mp hlo
    exact_mod_cast (by linarith : (n : ℝ) < ((2 * r + 1) * p : ℝ))
  have hdiv_eq : n / p = 2 * r := Nat.div_eq_of_lt_le (by linarith) hn_lt
  have hmod_eq : n % p = n - 2 * r * p := by
    have := Nat.div_add_mod n p
    rw [hdiv_eq] at this; omega
  have hdig_eq : Nat.digits p n = [n - 2 * r * p, 2 * r] := by
    rw [Nat.digits_def' hp.one_lt (by omega : 0 < n), hdiv_eq, hmod_eq,
      Nat.digits_of_lt p (2 * r) (by omega) hrp]
  have hpart2a : jacobiSym (-(qn n : ℤ)) p =
      jacobiSym (-(((2 * r).factorial * (n - 2 * r * p).factorial : ℕ) : ℤ)) p := by
    rw [hpart1, hdig_eq]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul, List.getD_cons_zero, List.getD_cons_succ]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left]
    ring
  refine ⟨hpart2a, ?_⟩
  intro hp1 m0 hm0
  have hp5 : 5 ≤ p := by omega
  have h_half_wil : (((((p - 1) / 2).factorial : ZMod p)) ^ 2) = -1 := by
    have hwil := ZMod.wilsons_lemma p
    have hprod : ((p - 1).factorial : ZMod p) =
        (((p - 1) / 2).factorial : ZMod p) ^ 2 * (-1 : ZMod p) ^ ((p - 1) / 2) := by
      have hp_sub : p - 1 = 2 * ((p - 1) / 2) := by omega
      have hfac_Icc : ((p - 1).factorial : ZMod p) = ∏ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p) := by
        rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
        refine Finset.prod_nbij' (fun k => k + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
        · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
        · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
        · intro k _; omega
        · intro k hk; rw [Finset.mem_Icc] at hk; omega
        · intro k _; rfl
      rw [hfac_Icc]
      have hsplit : Finset.Icc 1 (p - 1) = Finset.Icc 1 ((p - 1) / 2) ∪ Finset.Icc ((p - 1) / 2 + 1) (p - 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 ((p - 1) / 2)) (Finset.Icc ((p - 1) / 2 + 1) (p - 1)) := by
        rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      rw [hsplit, Finset.prod_union hdisj]
      have h1 : ∏ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ZMod p) = (((p - 1) / 2).factorial : ZMod p) := by
        rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
        refine Finset.prod_nbij' (fun k => k - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
        · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
        · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
        · intro k hk; rw [Finset.mem_Icc] at hk; omega
        · intro k _; omega
        · intro k hk; rw [Finset.mem_Icc] at hk; congr 1; omega
      have h2 : ∏ k ∈ Finset.Icc ((p - 1) / 2 + 1) (p - 1), (k : ZMod p) =
          (((p - 1) / 2).factorial : ZMod p) * (-1 : ZMod p) ^ ((p - 1) / 2) := by
        have hbij : ∏ k ∈ Finset.Icc ((p - 1) / 2 + 1) (p - 1), (k : ZMod p) =
            ∏ k ∈ Finset.Icc 1 ((p - 1) / 2), ((p - k : ℕ) : ZMod p) := by
          refine Finset.prod_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
          · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
          · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
          · intro k hk; rw [Finset.mem_Icc] at hk; omega
          · intro k hk; rw [Finset.mem_Icc] at hk; omega
          · intro k hk; rw [Finset.mem_Icc] at hk; congr 1; omega
        rw [hbij]
        have hneg : ∀ k ∈ Finset.Icc 1 ((p - 1) / 2), ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
          intro k hk
          have hk_le : k ≤ p := by rw [Finset.mem_Icc] at hk; omega
          rw [Nat.cast_sub hk_le, ZMod.natCast_self, zero_sub]
        rw [Finset.prod_congr rfl hneg, Finset.prod_neg, Finset.card_Icc,
          show (p - 1) / 2 + 1 - 1 = (p - 1) / 2 by omega, h1, mul_comm]
      rw [h1, h2]; ring
    have heven_half : Even ((p - 1) / 2) := by rw [Nat.even_iff]; omega
    rw [hprod, Even.neg_one_pow heven_half, mul_one] at hwil
    exact hwil
  have hjac_half : jacobiSym ((((p - 1) / 2).factorial : ℤ)) p = jacobiSym (2 : ℤ) p := by
    have hpow_zmod : ((((p - 1) / 2).factorial : ZMod p)) ^ (p / 2) = (-1 : ZMod p) ^ ((p - 1) / 4) := by
      have hp_div : p / 2 = 2 * ((p - 1) / 4) := by omega
      rw [hp_div, pow_mul, h_half_wil]
    have h_leg_half : (legendreSym p (((p - 1) / 2).factorial : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 4) := by
      rw [legendreSym.eq_pow, ← hpow_zmod]; simp
    have h_leg_two : (legendreSym p (2 : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 4) := by
      have h2_eq : legendreSym p (2 : ℤ) = (-1 : ℤ) ^ ((p - 1) / 4) := by
        rw [legendreSym.at_two (by omega : p ≠ 2), ZMod.χ₈_nat_eq_if_mod_eight]
        have hmod8 : p % 8 = 1 ∨ p % 8 = 5 := by omega
        rcases hmod8 with h1 | h5
        · have hev : Even ((p - 1) / 4) := by rw [Nat.even_iff]; omega
          simp [h1, Even.neg_one_pow hev]
        · have hodd : Odd ((p - 1) / 4) := by rw [Nat.odd_iff]; omega
          simp [h5, Odd.neg_one_pow hodd]
      rw [h2_eq]; push_cast; rfl
    have h_eq_zmod : (legendreSym p (((p - 1) / 2).factorial : ℤ) : ZMod p) = (legendreSym p (2 : ℤ) : ZMod p) := by
      rw [h_leg_half, h_leg_two]
    have h_int : legendreSym p (((p - 1) / 2).factorial : ℤ) = legendreSym p (2 : ℤ) := by
      have h1 := legendreSym.eq_one_or_neg_one (p := p) (a := (((p - 1) / 2).factorial : ℤ)) ?_
      · have h2 := legendreSym.eq_one_or_neg_one (p := p) (a := (2 : ℤ)) (by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; intro h0
          have hd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h0)
          have := Nat.le_of_dvd (by norm_num) hd; omega)
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · rw [h1, h2]
        · exfalso; rw [h1, h2] at h_eq_zmod
          have : (2 : ZMod p) = 0 := by linear_combination h_eq_zmod
          have hd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp this
          have := Nat.le_of_dvd (by norm_num) hd; omega
        · exfalso; rw [h1, h2] at h_eq_zmod
          have : (2 : ZMod p) = 0 := by linear_combination -h_eq_zmod
          have hd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp this
          have := Nat.le_of_dvd (by norm_num) hd; omega
        · rw [h1, h2]
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro h0
        have hsq : (((((p - 1) / 2).factorial : ZMod p)) ^ 2) = 0 := by
          have : ((((p - 1) / 2).factorial : ℤ) : ZMod p) = 0 := h0
          simpa using congrArg (· ^ 2) this
        rw [h_half_wil] at hsq
        exact one_ne_zero (by linear_combination -hsq : (1 : ZMod p) = 0)
    simpa [jacobiSym.legendreSym_eq] using h_int
  have hm0_le : m0 ≤ (p - 1) / 2 := by omega
  have h_fac_m0 : (((p - 1) / 2).factorial : ZMod p) =
      (((p - 1) / 2 - m0).factorial : ZMod p) *
        ∏ j ∈ Finset.range m0, ((-(2 * (j : ZMod p) + 1)) * (2 : ZMod p)⁻¹) := by
    clear hpart1 hpart2a h_half_wil hjac_half hdiv_fac h_bell
    induction m0 with
    | zero => simp
    | succ k ih =>
      have hk_le : k ≤ (p - 1) / 2 := by omega
      have hsucc : (p - 1) / 2 - k = ((p - 1) / 2 - (k + 1)) + 1 := by omega
      rw [Finset.prod_range_succ, ← mul_assoc]
      have ih' := ih hk_le
      rw [hsucc, Nat.factorial_succ, Nat.cast_mul] at ih'
      rw [ih']
      congr 1
      have h2_ne : (2 : ZMod p) ≠ 0 := by
        intro h0; have hd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp h0
        have := Nat.le_of_dvd (by norm_num) hd; omega
      have h_id : (((p - 1) / 2 - (k + 1) + 1 : ℕ) : ZMod p) =
          (-(2 * (k : ZMod p) + 1)) * (2 : ZMod p)⁻¹ := by
        apply mul_right_cancel₀ h2_ne
        rw [mul_assoc, inv_mul_cancel₀ h2_ne, mul_one]
        have hnat : 2 * ((p - 1) / 2 - (k + 1) + 1) + (2 * k + 1) = p := by omega
        have hz : ((2 * ((p - 1) / 2 - (k + 1) + 1) + (2 * k + 1) : ℕ) : ZMod p) = 0 := by
          rw [hnat, ZMod.natCast_self]
        push_cast at hz
        linear_combination hz
      rw [← h_id]; ring
  have h_jac_m0 : jacobiSym (((p - 1) / 2 - m0).factorial : ℤ) p =
      jacobiSym (((p - 1) / 2).factorial : ℤ) p *
        (jacobiSym (2 : ℤ) p) ^ m0 *
        ∏ j ∈ Finset.range m0, jacobiSym ((2 * j + 1 : ℤ)) p := by
    have h2_cop : Nat.Coprime 2 p := hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    have h_mul_2 : (((p - 1) / 2).factorial : ZMod p) * (2 : ZMod p) ^ m0 =
        (((p - 1) / 2 - m0).factorial : ZMod p) *
          ∏ j ∈ Finset.range m0, (-(2 * (j : ZMod p) + 1)) := by
      rw [h_fac_m0, mul_assoc, ← Finset.prod_const (b := (2 : ZMod p)), Finset.card_range,
        ← Finset.prod_mul_distrib]
      congr 1; congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      have h2_ne : (2 : ZMod p) ≠ 0 := by
        intro h0; have hd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp h0
        have := Nat.le_of_dvd (by norm_num) hd; omega
      rw [mul_assoc, inv_mul_cancel₀ h2_ne, mul_one]
    have h_int : (((((p - 1) / 2).factorial * 2 ^ m0 : ℕ) : ℤ) : ZMod p) =
        (((((p - 1) / 2 - m0).factorial : ℤ) * ∏ j ∈ Finset.range m0, (-(2 * (j : ℤ) + 1)) : ℤ) : ZMod p) := by
      push_cast; exact h_mul_2
    rw [ZMod.intCast_eq_intCast_iff] at h_int
    have hjac_eq : jacobiSym (((p - 1) / 2).factorial * 2 ^ m0 : ℤ) p =
        jacobiSym ((((p - 1) / 2 - m0).factorial : ℤ) * ∏ j ∈ Finset.range m0, (-(2 * (j : ℤ) + 1))) p := by
      have h2 := jacobiSym.mod_left (((p - 1) / 2).factorial * 2 ^ m0 : ℤ) p
      have h3 := jacobiSym.mod_left ((((p - 1) / 2 - m0).factorial : ℤ) * ∏ j ∈ Finset.range m0, (-(2 * (j : ℤ) + 1))) p
      rw [h_int] at h2; linarith
    rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.mul_left, jacobiSym.prod_left] at hjac_eq
    have hneg_prod : ∏ j ∈ Finset.range m0, jacobiSym (-(2 * (j : ℤ) + 1)) p =
        ∏ j ∈ Finset.range m0, jacobiSym (2 * (j : ℤ) + 1) p := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [show -(2 * (j : ℤ) + 1) = (-1 : ℤ) * (2 * (j : ℤ) + 1) by ring, jacobiSym.mul_left,
        jacobiSym.at_neg_one (by omega), ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]
      ring
    rw [hneg_prod] at hjac_eq
    have h_sq_1 : (∏ j ∈ Finset.range m0, jacobiSym (2 * (j : ℤ) + 1) p) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun j hj => ?_
      have hj_lt : j < m0 := Finset.mem_range.mp hj
      have hcop : Nat.Coprime (2 * j + 1) p := hp.coprime_iff_not_dvd.mpr (fun h => by
        have := Nat.le_of_dvd (by omega) h; omega)
      exact jacobiSym.sq_one hcop
    calc jacobiSym (((p - 1) / 2 - m0).factorial : ℤ) p
        = jacobiSym (((p - 1) / 2 - m0).factorial : ℤ) p *
            (∏ j ∈ Finset.range m0, jacobiSym (2 * (j : ℤ) + 1) p) ^ 2 := by rw [h_sq_1, mul_one]
      _ = (jacobiSym (((p - 1) / 2 - m0).factorial : ℤ) p *
            ∏ j ∈ Finset.range m0, jacobiSym (2 * (j : ℤ) + 1) p) *
            ∏ j ∈ Finset.range m0, jacobiSym (2 * (j : ℤ) + 1) p := by ring
      _ = (jacobiSym (((p - 1) / 2).factorial : ℤ) p * jacobiSym (2 : ℤ) p ^ m0) *
            ∏ j ∈ Finset.range m0, jacobiSym (2 * (j : ℤ) + 1) p := by rw [← hjac_eq]
  rw [hpart2a, hm0]
  have hneg1 : jacobiSym (-1 : ℤ) p = 1 := by
    rw [jacobiSym.at_neg_one (by omega), ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]
  rw [show -(((2 * r).factorial * ((p - 1) / 2 - m0).factorial : ℕ) : ℤ) =
      (-1 : ℤ) * ((2 * r).factorial : ℤ) * (((p - 1) / 2 - m0).factorial : ℤ) by push_cast; ring,
    jacobiSym.mul_left, jacobiSym.mul_left, hneg1, one_mul, h_jac_m0, hjac_half]
  ring

/-- `c_even(n) := ∏_{3 ≤ q ≤ n, v_q(n!) ≡ 2 (mod 4)} q` (4.19). -/
def ceven (n : ℕ) : ℕ :=
  ∏ q ∈ (Finset.Icc 3 n).filter (fun q => q.Prime ∧ padicValNat q n.factorial % 4 = 2), q

theorem theorem_4_4_ii (n m : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6)
    (hsol : IsBrocardSol n m) (hk2 : pellIndex (by omega) hsol = 2) :
    let zn := Zn n (by omega) hn6
    let x1 := X1 n (by omega) hn6
    (∀ p ∈ Peven n, 3 ≤ p → jacobiSym (-(qn n : ℤ)) p = -1 →
      padicValNat p zn = padicValNat p n.factorial / 2) ∧
    (∀ p ∈ Podd n, p % 4 = 1 →
      jacobiSym (coreNat zn : ℤ) p =
        jacobiSym ((2 ^ padicValNat 2 x1 * ceven n : ℕ) : ℤ) p) := by
  dsimp only
  set zn := Zn n (by omega) hn6
  set x1 := X1 n (by omega) hn6
  set y1 := Y1 n (by omega) hn6
  have hprop := prop_4_1 n m hn hn6 hsol hk2
  have hx1_pos : 1 ≤ x1 := by
    have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop
    nlinarith [sq_nonneg (y1 : ℤ), qn_pos n]
  have hy1_pos : 0 < y1 := Y1_pos (by omega) hn6
  have hpart1 : ∀ p ∈ Peven n, 3 ≤ p → jacobiSym (-(qn n : ℤ)) p = -1 →
      padicValNat p zn = padicValNat p n.factorial / 2 := by
    intro p hp hp3 hjac
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hndvd_x1 : ¬ p ∣ x1 := by
      intro hpx
      have h1 := hprop.2.2.2.2 (coreNat (x1 - 1)) (coreNat (x1 + 1))
        (sqrtPartNat (x1 - 1)) (sqrtPartNat (x1 + 1))
        squarefree_coreNat squarefree_coreNat
        (coreNat_mul_sqrtPart_sq (by
          have : 2 ≤ x1 := by
            have hqy_pos : 0 < qn n * y1 ^ 2 := mul_pos (qn_pos n) (pow_pos hy1_pos 2)
            have h_ell := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; nlinarith
          omega))
        (coreNat_mul_sqrtPart_sq (by omega)) p hp_prime hp3 hpx
      linarith [h1.2.2.1]
    have hpy1 : p ∣ y1 := by
      obtain ⟨_, _, _, _, _, _, hfac⟩ := critical_eqs_4_1_to_4_3 n m (by omega) hn6 hsol hk2
      have hqy_eq : qn n * y1 ^ 2 = (x1 - 1) * (x1 + 1) := by
        have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [hx1_pos]; linarith
      have hfac_qy : n.factorial = 4 * (qn n * y1 ^ 2) * x1 ^ 2 := by rw [hfac, hqy_eq]; ring
      have hpn_dvd : p ∣ n.factorial := hp_prime.dvd_factorial.mpr hpn
      rw [hfac_qy] at hpn_dvd
      have hndvd4 : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
      have hndvd_qn : ¬ p ∣ qn n := fun h => by
        rw [qn_eq_prod_Podd] at h
        obtain ⟨q, hq, hqp⟩ := hp_prime.prime.dvd_finset_prod_iff.mp h
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime (Finset.mem_filter.mp hq).2.1).mp hqp
        subst this
        exact (Podd_disjoint_Peven n).le_bot (Finset.mem_inter.mpr ⟨hq, hp⟩)
      rcases hp_prime.dvd_mul.mp hpn_dvd with h4qy | hx2
      · rcases hp_prime.dvd_mul.mp h4qy with h4 | hqy
        · exact absurd h4 hndvd4
        · rcases hp_prime.dvd_mul.mp hqy with hq | hy2
          · exact absurd hq hndvd_qn
          · exact hp_prime.dvd_of_dvd_pow hy2
      · exact absurd (hp_prime.dvd_of_dvd_pow hx2) hndvd_x1
    unfold zn Zn
    rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp_prime]
    simp [hp, hp3, hpy1]
  have hpart2 : ∀ p ∈ Podd n, p % 4 = 1 →
      jacobiSym (coreNat zn : ℤ) p =
        jacobiSym ((2 ^ padicValNat 2 x1 * ceven n : ℕ) : ℤ) p := by
    intro p hp hp4
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp5 : 5 ≤ p := by have := hp_prime.two_le; omega
    have h_p_dvd_qy : p ∣ qn n * y1 ^ 2 := by
      have h1 := (hprop.2.1 p hp (by omega)).1
      have hv_pos : 1 ≤ padicValNat p n.factorial :=
        one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) (hp_prime.dvd_factorial.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
      exact dvd_trans (dvd_pow_self p hv_pos.ne') h1
    have hx1_sq_mod : (x1 : ZMod p) ^ 2 = 1 := by
      have h1 : (x1 : ℤ) ^ 2 - (qn n : ℤ) * (y1 : ℤ) ^ 2 = 1 :=
        (pellFundUnit (by omega : 3 ≤ n) hn6).prop
      have h2 : ((qn n * y1 ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ p).mpr h_p_dvd_qy
      have h3 : ((x1 : ZMod p) ^ 2 - ((qn n * y1 ^ 2 : ℕ) : ZMod p)) = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod p) h1
        simpa using this
      rw [h2, sub_zero] at h3; exact h3
    have hjac_x1 : jacobiSym (x1 : ℤ) p = 1 := by
      haveI : Fact p.Prime := ⟨hp_prime⟩
      rcases (sq_eq_one_iff.mp hx1_sq_mod) with h1 | hm1
      · have h_int : ((x1 : ℤ) : ZMod p) = (1 : ℤ) := by simpa using h1
        rw [ZMod.intCast_eq_intCast_iff] at h_int
        have h2 := jacobiSym.mod_left (x1 : ℤ) p
        have h3 := jacobiSym.mod_left (1 : ℤ) p
        rw [h_int] at h2; simpa [jacobiSym.one_left] using h2.trans h3.symm
      · have h_int : ((x1 : ℤ) : ZMod p) = (-1 : ℤ) := by simpa using hm1
        rw [ZMod.intCast_eq_intCast_iff] at h_int
        have h2 := jacobiSym.mod_left (x1 : ℤ) p
        have h3 := jacobiSym.mod_left (-1 : ℤ) p
        rw [h_int] at h2
        rw [h2, ← h3, jacobiSym.at_neg_one (by omega), ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]
    set x1_odd := oddPart x1
    have hx1_split : x1 = 2 ^ padicValNat 2 x1 * x1_odd := by
      unfold x1_odd oddPart
      exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have hAnStar_eq : AnStar n = x1_odd ^ 2 * zn ^ 2 := by
      have han_eq := (theorem_4_2_i_part1 n m hn hn6 hsol hk2).2.1
      dsimp only at han_eq
      unfold An at han_eq
      split_ifs at han_eq with hxodd
      · have hv2_x1 : padicValNat 2 x1 = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
        have hx1_odd_eq : x1_odd = x1 := by unfold x1_odd oddPart; rw [hv2_x1, pow_zero, Nat.div_one]
        rw [hx1_odd_eq]; exact han_eq
      · have h2_eq : padicValNat 2 n.factorial - 2 = 2 * padicValNat 2 x1 := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          obtain ⟨_, _, _, _, _, _, hfac⟩ := critical_eqs_4_1_to_4_3 n m (by omega) hn6 hsol hk2
          have hqy_eq : qn n * y1 ^ 2 = (x1 - 1) * (x1 + 1) := by
            have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify [hx1_pos]; linarith
          have hfac_qy : n.factorial = 4 * (qn n * y1 ^ 2) * x1 ^ 2 := by rw [hfac, hqy_eq]; ring
          have hqy_odd : ¬ 2 ∣ qn n * y1 ^ 2 := by
            intro h2
            have : 2 ∣ x1 ^ 2 - qn n * y1 ^ 2 := dvd_sub (dvd_pow (by omega : 2 ∣ x1) (by norm_num)) h2
            rw [show x1 ^ 2 - qn n * y1 ^ 2 = 1 by have := (pellFundUnit (by omega : 3 ≤ n) hn6).prop; zify; linarith] at this
            omega
          have hv2_fac : padicValNat 2 n.factorial = 2 + 2 * padicValNat 2 x1 := by
            conv_lhs => rw [hfac_qy]
            rw [padicValNat.mul (mul_ne_zero (by norm_num) (mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 hy1_pos.ne'))) (pow_ne_zero 2 hx1_pos.ne'),
              padicValNat.mul (by norm_num) (mul_ne_zero (qn_pos n).ne' (pow_ne_zero 2 hy1_pos.ne')),
              show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.pow 2 2, padicValNat.self (by norm_num), mul_one,
              padicValNat.eq_zero_of_not_dvd hqy_odd, add_zero, padicValNat.pow x1 2]
          omega
        have h1 : 2 ^ (padicValNat 2 n.factorial - 2) * AnStar n =
            2 ^ (2 * padicValNat 2 x1) * (x1_odd ^ 2 * zn ^ 2) := by
          rw [han_eq, hx1_split, mul_pow, ← pow_mul, mul_comm (padicValNat 2 x1) 2, h2_eq]; ring
        exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) (by rwa [h2_eq])
    have hp_ndvd_An : ¬ p ∣ AnStar n := by
      intro h
      have h1 := one_le_padicValNat_of_dvd (AnStar_pos n).ne' h
      unfold AnStar at h1
      rw [padicValNat_prod_pow (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1) _ hp_prime] at h1
      split_ifs at h1 with hpE
      · exact (Podd_disjoint_Peven n).le_bot (Finset.mem_inter.mpr ⟨hp, (Finset.mem_filter.mp hpE).1⟩)
      · omega
    have hp_ndvd_x1odd : ¬ p ∣ x1_odd := fun h => hp_ndvd_An (by rw [hAnStar_eq]; exact dvd_mul_of_dvd_left (dvd_pow h (by norm_num)) _)
    have hp_ndvd_zn : ¬ p ∣ zn := fun h => hp_ndvd_An (by rw [hAnStar_eq]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
    have hcore_An : coreNat (AnStar n) = ceven n := by
      unfold coreNat ceven AnStar
      congr 1
      ext q
      simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, (AnStar_pos n).ne', not_false_eq_true,
        and_true, Finset.mem_Icc, Peven]
      constructor
      · rintro ⟨⟨hq, hdvd⟩, hodd⟩
        have hq_mem : q ∈ (Peven n).filter (3 ≤ ·) := by
          by_contra hnot
          have h1 : padicValNat q (∏ r ∈ (Peven n).filter (3 ≤ ·), r ^ padicValNat r n.factorial) = 0 := by
            rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hq]
            simp [hnot]
          have := one_le_padicValNat_of_dvd (AnStar_pos n).ne' hdvd
          omega
        have hq_val : padicValNat q (∏ r ∈ (Peven n).filter (3 ≤ ·), r ^ padicValNat r n.factorial) =
            padicValNat q n.factorial := by
          rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hq]
          simp [hq_mem]
        rw [hq_val] at hodd
        have hq_pe := Finset.mem_filter.mp hq_mem
        have hq_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq_pe.1).1
        have hq_ev := (Finset.mem_filter.mp hq_pe.1).2.2
        exact ⟨⟨hq_pe.2, hq_icc.2⟩, hq, by omega⟩
      · rintro ⟨⟨hq3, hqn⟩, hq, hmod4⟩
        have hq_pe : q ∈ (Peven n).filter (3 ≤ ·) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.two_le, hqn⟩, hq, by omega⟩, hq3⟩
        have hq_val : padicValNat q (∏ r ∈ (Peven n).filter (3 ≤ ·), r ^ padicValNat r n.factorial) =
            padicValNat q n.factorial := by
          rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hq]
          simp [hq_pe]
        have hdvd : q ∣ ∏ r ∈ (Peven n).filter (3 ≤ ·), r ^ padicValNat r n.factorial :=
          Finset.dvd_prod_of_mem _ hq_pe |> fun h => dvd_trans (dvd_pow_self q (by omega)) h
        exact ⟨⟨hq, hdvd⟩, by rw [hq_val]; omega⟩
    have hjac_An : jacobiSym (AnStar n : ℤ) p = jacobiSym (ceven n : ℤ) p := by
      have h1 := coreNat_mul_sqrtPart_sq (AnStar_pos n).ne'
      rw [hcore_An] at h1
      conv_lhs => rw [h1]
      push_cast
      rw [jacobiSym.mul_left, jacobiSym.sq_one (hp_prime.coprime_iff_not_dvd.mpr (fun h =>
        hp_ndvd_An (by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _))).symm, mul_one]
    have hjac_x1_split : jacobiSym (2 ^ padicValNat 2 x1 : ℤ) p * jacobiSym (x1_odd : ℤ) p = 1 := by
      rw [← jacobiSym.mul_left, ← Nat.cast_mul, ← hx1_split, hjac_x1]
    have hjac_zn_core : jacobiSym (zn : ℤ) p = jacobiSym (coreNat zn : ℤ) p := by
      have h1 := coreNat_mul_sqrtPart_sq (Zn_pos n (by omega) hn6).ne'
      conv_lhs => rw [h1]
      push_cast
      rw [jacobiSym.mul_left, jacobiSym.sq_one (hp_prime.coprime_iff_not_dvd.mpr (fun h =>
        hp_ndvd_zn (by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _))).symm, mul_one]
    have hjac_An_sq : jacobiSym (AnStar n : ℤ) p = 1 := by
      rw [hAnStar_eq]; push_cast
      rw [jacobiSym.mul_left, jacobiSym.sq_one (hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_x1odd).symm,
        jacobiSym.sq_one (hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_zn).symm, mul_one]
    have hx1zn_pos : 0 < x1_odd * zn := Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hx1_pos pow_padicValNat_dvd) (pow_pos (by norm_num) _)) (Zn_pos n (by omega) hn6)
    have hcore_x1zn : coreNat (x1_odd * zn) = ceven n := by
      unfold coreNat ceven
      congr 1
      ext q
      simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, hx1zn_pos.ne', not_false_eq_true,
        and_true, Finset.mem_Icc, Peven]
      have h_val_sq : ∀ r : ℕ, r.Prime → 2 * padicValNat r (x1_odd * zn) = padicValNat r (AnStar n) := by
        intro r hr
        haveI : Fact r.Prime := ⟨hr⟩
        rw [hAnStar_eq, ← mul_pow, padicValNat.pow _ 2]
      constructor
      · rintro ⟨⟨hq, hdvd⟩, hodd⟩
        have h2v : 2 * padicValNat q (x1_odd * zn) = padicValNat q (AnStar n) := h_val_sq q hq
        have hq_mem : q ∈ (Peven n).filter (3 ≤ ·) := by
          by_contra hnot
          have h1 : padicValNat q (AnStar n) = 0 := by
            unfold AnStar
            rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hq]
            simp [hnot]
          have := one_le_padicValNat_of_dvd hx1zn_pos.ne' hdvd
          omega
        have hq_val : padicValNat q (AnStar n) = padicValNat q n.factorial := by
          unfold AnStar
          rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hq]
          simp [hq_mem]
        have hq_pe := Finset.mem_filter.mp hq_mem
        have hq_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq_pe.1).1
        have hq_ev := (Finset.mem_filter.mp hq_pe.1).2.2
        exact ⟨⟨hq_pe.2, hq_icc.2⟩, hq, by omega⟩
      · rintro ⟨⟨hq3, hqn⟩, hq, hmod4⟩
        have hq_pe : q ∈ (Peven n).filter (3 ≤ ·) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.two_le, hqn⟩, hq, by omega⟩, hq3⟩
        have hq_val : padicValNat q (AnStar n) = padicValNat q n.factorial := by
          unfold AnStar
          rw [padicValNat_prod_pow (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1) _ hq]
          simp [hq_pe]
        have h2v : 2 * padicValNat q (x1_odd * zn) = padicValNat q n.factorial := by
          rw [h_val_sq q hq, hq_val]
        have hdvd : q ∣ x1_odd * zn := by
          haveI : Fact q.Prime := ⟨hq⟩
          exact (padicValNat.dvd_iff_le hx1zn_pos.ne').mpr (by omega)
        exact ⟨⟨hq, hdvd⟩, by omega⟩
    have hjac_ceven : jacobiSym (ceven n : ℤ) p = jacobiSym (x1_odd : ℤ) p * jacobiSym (zn : ℤ) p := by
      have h1 := coreNat_mul_sqrtPart_sq hx1zn_pos.ne'
      rw [hcore_x1zn] at h1
      have hp_ndvd_x1zn : ¬ p ∣ x1_odd * zn := fun h => by
        rcases hp_prime.dvd_mul.mp h with h2 | h2
        · exact hp_ndvd_x1odd h2
        · exact hp_ndvd_zn h2
      have hp_cop_sq : IsCoprime ((sqrtPartNat (x1_odd * zn) : ℤ)) p :=
        (hp_prime.coprime_iff_not_dvd.mpr (fun h =>
          hp_ndvd_x1zn (by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _))).symm.isCoprime
      have hjac_sq1 : jacobiSym ((x1_odd * zn : ℕ) : ℤ) p = jacobiSym (ceven n : ℤ) p := by
        conv_lhs => rw [h1]
        push_cast
        rw [jacobiSym.mul_left, jacobiSym.sq_one (hp_prime.coprime_iff_not_dvd.mpr (fun h =>
          hp_ndvd_x1zn (by rw [h1]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _))).symm, mul_one]
      rw [← hjac_sq1, Nat.cast_mul, jacobiSym.mul_left]
    rw [Nat.cast_mul, jacobiSym.mul_left, hjac_ceven, ← mul_assoc, hjac_x1_split, one_mul, hjac_zn_core]
  exact ⟨hpart1, hpart2⟩

end BrocardFormalization

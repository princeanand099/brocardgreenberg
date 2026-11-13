/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries

/-!
# Proposition 2.6: Rademacher Moment Convergence for Truncated Parity Series

This module formalizes Proposition 2.6 (`prop_2_6`):
For the `r`-digit truncated base-`p` parity series `SigmaParityTrunc r n B`,
the `2m`-th empirical moments converge (as `N → ∞`, then `r → ∞`, then `B → ∞`)
to the `2m`-th moment of the Jessen–Wintner Rademacher density `ρ`.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-- `r`-digit truncated base-`p` parity sign `ξ_p^{(r)}(n)` (Proposition 2.6). -/
def truncParitySign (p r n : ℕ) : ℝ :=
  - ∏ m ∈ Finset.range r, (-1 : ℝ) ^ ((n / p ^ (2 * m + 1)) % p)

/-- Truncated base-`p` parity series `Σ_parity^{(r)}(n; B)`. -/
def SigmaParityTrunc (r n B : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
    truncParitySign p r n * (Real.log p / ((p : ℝ) - 1))

private lemma truncParitySign_sq {p r n : ℕ} : (truncParitySign p r n) ^ 2 = 1 := by
  unfold truncParitySign
  rw [neg_sq, Finset.prod_pow]
  refine Finset.prod_eq_one fun m _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

private lemma abs_truncParitySign {p r n : ℕ} : |truncParitySign p r n| = 1 := by
  rw [← sq_eq_one_iff]
  exact truncParitySign_sq

private lemma truncParitySign_periodic {p r n k : ℕ} (hp : 0 < p) :
    truncParitySign p r (n + k * p ^ (2 * r + 1)) = truncParitySign p r n := by
  unfold truncParitySign
  congr 2
  refine Finset.prod_congr rfl fun m hm => ?_
  have hm_lt : m < r := Finset.mem_range.mp hm
  have hdiv : p ^ (2 * m + 1) * p ∣ p ^ (2 * r + 1) := by
    rw [← pow_succ]
    exact Nat.pow_dvd_pow p (by omega)
  rcases hdiv with ⟨t, ht⟩
  have h1 : (n + k * p ^ (2 * r + 1)) / p ^ (2 * m + 1) =
      n / p ^ (2 * m + 1) + k * t * p := by
    rw [ht, show k * (p ^ (2 * m + 1) * p * t) = (k * t * p) * p ^ (2 * m + 1) by ring]
    exact Nat.add_mul_div_right n (k * t * p) (pow_pos hp _)
  rw [h1, show (n / p ^ (2 * m + 1) + k * t * p) % p = (n / p ^ (2 * m + 1)) % p by
    rw [Nat.add_mul_mod_self_right]]

private lemma truncParitySign_mod_eq {p r n M : ℕ} (hp : 0 < p) (hdvd : p ^ (2 * r + 1) ∣ M) :
    truncParitySign p r (n % M) = truncParitySign p r n := by
  rcases hdvd with ⟨t, ht⟩
  have h1 : n % M + (n / M * t) * p ^ (2 * r + 1) = n := by
    have := Nat.mod_add_div n M
    rw [ht] at this
    linarith
  calc truncParitySign p r (n % M)
      = truncParitySign p r (n % M + (n / M * t) * p ^ (2 * r + 1)) :=
        (truncParitySign_periodic hp).symm
    _ = truncParitySign p r n := by rw [h1]

private lemma truncParitySign_sum_period {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (r : ℕ) :
    ∑ n ∈ Finset.range (p ^ (2 * r + 1)), truncParitySign p r n = -((p : ℝ) ^ (r + 1)) := by
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hsum_digit : ∑ d ∈ Finset.range p, (-1 : ℝ) ^ d = 1 := by
    have h2 : p = 2 * (p / 2) + 1 := by omega
    rw [h2, Finset.sum_range_succ]
    have heven : ∀ k : ℕ, ∑ d ∈ Finset.range (2 * k), (-1 : ℝ) ^ d = 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
        simp [pow_add, pow_mul]
    rw [heven (p / 2), zero_add]
    have hmod : (2 * (p / 2)) % 2 = 0 := by omega
    rw [← Nat.div_add_mod (2 * (p / 2)) 2, hmod, add_zero, pow_mul, neg_one_sq, one_pow]
  induction r with
  | zero =>
    simp [truncParitySign]
  | succ r ih =>
    have hpow_eq : p ^ (2 * (r + 1) + 1) = (p * p) * p ^ (2 * r + 1) := by ring
    have h1 : ∑ n ∈ Finset.range (p ^ (2 * (r + 1) + 1)), truncParitySign p (r + 1) n =
        ∑ qa ∈ Finset.range (p * p) ×ˢ Finset.range (p ^ (2 * r + 1)),
          truncParitySign p (r + 1) (qa.2 + p ^ (2 * r + 1) * qa.1) := by
      refine Finset.sum_nbij'
        (fun n => (n / p ^ (2 * r + 1), n % p ^ (2 * r + 1)))
        (fun qa => qa.2 + p ^ (2 * r + 1) * qa.1) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_range, hpow_eq] at hn
        exact Finset.mem_product.mpr ⟨(Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr
          (by linarith), Nat.mod_lt n (pow_pos hp.pos _)⟩
      · intro ⟨q, a⟩ hqa
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqa
        rw [Finset.mem_range, hpow_eq]
        nlinarith
      · intro n _
        exact Nat.mod_add_div n (p ^ (2 * r + 1))
      · intro ⟨q, a⟩ hqa
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqa
        ext
        · simp [Nat.add_mul_div_left a q (pow_pos hp.pos _), Nat.div_eq_of_lt hqa.2]
        · simp [Nat.mod_eq_of_lt hqa.2]
      · intro _ _; rfl
    rw [h1, Finset.sum_product]
    have h2 : ∀ q ∈ Finset.range (p * p),
        ∑ a ∈ Finset.range (p ^ (2 * r + 1)),
          truncParitySign p (r + 1) (a + p ^ (2 * r + 1) * q) =
        (-1 : ℝ) ^ (q % p) * ∑ a ∈ Finset.range (p ^ (2 * r + 1)), truncParitySign p r a := by
      intro q _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha_lt : a < p ^ (2 * r + 1) := Finset.mem_range.mp ha
      unfold truncParitySign
      rw [Finset.prod_range_succ]
      have hlast : ((a + p ^ (2 * r + 1) * q) / p ^ (2 * r + 1)) % p = q % p := by
        rw [Nat.add_mul_div_left a q (pow_pos hp.pos _), Nat.div_eq_of_lt ha_lt, zero_add]
      have hprev : ∏ m ∈ Finset.range r,
          (-1 : ℝ) ^ (((a + p ^ (2 * r + 1) * q) / p ^ (2 * m + 1)) % p) =
          ∏ m ∈ Finset.range r, (-1 : ℝ) ^ ((a / p ^ (2 * m + 1)) % p) := by
        refine Finset.prod_congr rfl fun m hm => ?_
        have hm_lt : m < r := Finset.mem_range.mp hm
        have hdiv : p ^ (2 * m + 1) * p ∣ p ^ (2 * r + 1) := by
          rw [← pow_succ]; exact Nat.pow_dvd_pow p (by omega)
        rcases hdiv with ⟨t, ht⟩
        have hdiv_eq : (a + p ^ (2 * r + 1) * q) / p ^ (2 * m + 1) =
            a / p ^ (2 * m + 1) + (t * q) * p := by
          rw [ht, show p ^ (2 * m + 1) * p * t * q = (t * q * p) * p ^ (2 * m + 1) by ring]
          rw [Nat.add_mul_div_right a (t * q * p) (pow_pos hp.pos _)]
          ring
        rw [hdiv_eq, Nat.add_mul_mod_self_right]
      rw [hlast, hprev]
      ring
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, ih]
    have hq_sum : ∑ q ∈ Finset.range (p * p), (-1 : ℝ) ^ (q % p) = (p : ℝ) := by
      have hsplit : ∑ q ∈ Finset.range (p * p), (-1 : ℝ) ^ (q % p) =
          ∑ ed ∈ Finset.range p ×ˢ Finset.range p, (-1 : ℝ) ^ ed.2 := by
        refine Finset.sum_nbij' (fun q => (q / p, q % p)) (fun ed => ed.2 + p * ed.1)
          ?_ ?_ ?_ ?_ ?_
        · intro q hq
          rw [Finset.mem_range] at hq
          exact Finset.mem_product.mpr ⟨(Nat.div_lt_iff_lt_mul hp.pos).mpr (by linarith),
            Nat.mod_lt q hp.pos⟩
        · intro ⟨e, d⟩ hed
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hed
          rw [Finset.mem_range]
          nlinarith
        · intro q _; exact Nat.mod_add_div q p
        · intro ⟨e, d⟩ hed
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hed
          ext
          · simp [Nat.add_mul_div_left d e hp.pos, Nat.div_eq_of_lt hed.2]
          · simp [Nat.mod_eq_of_lt hed.2]
        · intro _ _; rfl
      rw [hsplit, Finset.sum_product, Finset.sum_congr rfl (fun _ _ => hsum_digit),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hq_sum]
    push_cast [pow_succ]
    ring

private lemma truncParitySign_pow_avg {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (r c : ℕ) :
    |∑ n ∈ Finset.range (p ^ (2 * r + 1)), (truncParitySign p r n) ^ c| ≤
      if Even c then (p : ℝ) ^ (2 * r + 1) else (p : ℝ) ^ (r + 1) := by
  by_cases hc : Even c
  · simp only [hc, ↓reduceIte]
    have h1 : ∀ n, (truncParitySign p r n) ^ c = 1 := by
      intro n
      rcases hc with ⟨k, rfl⟩
      rw [← two_mul, pow_mul, truncParitySign_sq, one_pow]
    simp [h1, Finset.sum_const, Finset.card_range]
  · simp only [hc, ↓reduceIte]
    have hc_odd : Odd c := Nat.not_even_iff_odd.mp hc
    have h1 : ∀ n, (truncParitySign p r n) ^ c = truncParitySign p r n := by
      intro n
      rcases hc_odd with ⟨k, rfl⟩
      rw [pow_add, pow_mul, truncParitySign_sq, one_pow, one_mul, pow_one]
    simp_rw [h1]
    rw [truncParitySign_sum_period hp hp3 r, abs_neg, abs_of_nonneg (by positivity)]

private lemma crt_prod_sum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) (r : ℕ) (c : ℕ → ℕ) :
    ∑ n ∈ Finset.range (∏ p ∈ S, p ^ (2 * r + 1)), ∏ p ∈ S, (truncParitySign p r n) ^ (c p) =
      ∏ p ∈ S, ∑ n ∈ Finset.range (p ^ (2 * r + 1)), (truncParitySign p r n) ^ (c p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p₀ S' hp₀ ih =>
    have hp₀_pr : p₀.Prime := (hS p₀ (Finset.mem_insert_self _ _)).1
    have hS' : ∀ p ∈ S', p.Prime ∧ 3 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    set A := p₀ ^ (2 * r + 1)
    set B₀ := ∏ p ∈ S', p ^ (2 * r + 1)
    have hA_pos : 0 < A := pow_pos hp₀_pr.pos _
    have hB₀_pos : 0 < B₀ := Finset.prod_pos fun p hp => pow_pos (hS' p hp).1.pos _
    have hcop : Nat.Coprime A B₀ := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      refine Nat.Coprime.pow _ _ ?_
      exact (Nat.coprime_primes hp₀_pr (hS' p hp).1).mpr (fun heq => hp₀ (heq ▸ hp))
    have hbij : ∑ n ∈ Finset.range (A * B₀),
          ((truncParitySign p₀ r n) ^ (c p₀) * ∏ p ∈ S', (truncParitySign p r n) ^ (c p)) =
        ∑ ab ∈ Finset.range A ×ˢ Finset.range B₀,
          ((truncParitySign p₀ r ab.1) ^ (c p₀) * ∏ p ∈ S', (truncParitySign p r ab.2) ^ (c p)) := by
      have hinj : Set.InjOn (fun n => (n % A, n % B₀)) (Finset.range (A * B₀) : Set ℕ) := by
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_range] at hx hy
        have hx1 := (Prod.ext_iff.mp hxy).1
        have hx2 := (Prod.ext_iff.mp hxy).2
        have hmod1 : (x : ℤ) ≡ (y : ℤ) [ZMOD A] := by
          rw [Int.ModEq]; exact_mod_cast hx1
        have hmod2 : (x : ℤ) ≡ (y : ℤ) [ZMOD B₀] := by
          rw [Int.ModEq]; exact_mod_cast hx2
        have hdvd1 : (A : ℤ) ∣ (x : ℤ) - y := hmod1.symm.dvd
        have hdvd2 : (B₀ : ℤ) ∣ (x : ℤ) - y := hmod2.symm.dvd
        have hcopZ : IsCoprime (A : ℤ) (B₀ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
        have hdvd : (A * B₀ : ℤ) ∣ (x : ℤ) - y := hcopZ.mul_dvd hdvd1 hdvd2
        rcases hdvd with ⟨k, hk⟩
        have hlt : |(x : ℤ) - y| < (A * B₀ : ℤ) := by
          rw [abs_lt]; constructor <;> omega
        have hk0 : k = 0 := by
          by_contra hk_ne
          have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
          have h2 : (A * B₀ : ℤ) ≤ (A * B₀ : ℤ) * |k| := le_mul_of_one_le_right (by positivity) h1
          rw [← abs_of_pos (by positivity : (0 : ℤ) < A * B₀), ← abs_mul, ← hk] at h2
          omega
        rw [hk0, mul_zero] at hk
        omega
      have hmaps : Set.MapsTo (fun n => (n % A, n % B₀)) (Finset.range (A * B₀) : Set ℕ)
          (Finset.range A ×ˢ Finset.range B₀ : Set (ℕ × ℕ)) := by
        intro n _
        exact Finset.mem_product.mpr ⟨Nat.mod_lt n hA_pos, Nat.mod_lt n hB₀_pos⟩
      have hcard : (Finset.range A ×ˢ Finset.range B₀).card ≤ (Finset.range (A * B₀)).card := by
        simp [Finset.card_product]
      have hsurj := Finset.surjOn_of_injOn_of_card_le hmaps hinj hcard
      refine Finset.sum_nbij (fun n => (n % A, n % B₀)) hmaps hinj hsurj fun n _ => ?_
      congr 1
      · rw [truncParitySign_mod_eq hp₀_pr.pos dvd_rfl]
      · refine Finset.prod_congr rfl fun p hp => ?_
        have hdvd : p ^ (2 * r + 1) ∣ B₀ := Finset.dvd_prod_of_mem _ hp
        rw [truncParitySign_mod_eq (hS' p hp).1.pos hdvd]
    rw [Finset.prod_insert hp₀]
    simp_rw [Finset.prod_insert hp₀]
    rw [hbij, Finset.sum_product, Finset.sum_mul_sum, ih hS']

private def rademacherMoment (S : Finset ℕ) (k : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ S.card) *
    ∑ σ : S → Bool, (∑ p : S, (if σ p then (1 : ℝ) else -1) *
      (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) ^ k

private lemma rademacherMoment_eq_even_sum (S : Finset ℕ) (m : ℕ) :
    rademacherMoment S (2 * m) =
      ∑ g : Fin (2 * m) → S,
        (if ∀ p : S, Even (Finset.univ.filter fun i => g i = p).card then (1 : ℝ) else 0) *
          ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) := by
  classical
  unfold rademacherMoment
  have hexp : ∀ σ : S → Bool,
      (∑ p : S, (if σ p then (1 : ℝ) else -1) *
        (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) ^ (2 * m) =
      ∑ g : Fin (2 * m) → S,
        (∏ p : S, (if σ p then (1 : ℝ) else -1) ^ (Finset.univ.filter fun i => g i = p).card) *
          ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) := by
    intro σ
    rw [Finset.sum_pow' (Finset.univ : Finset S) _ (2 * m)]
    have hpi : (Fintype.piFinset fun _ : Fin (2 * m) => (Finset.univ : Finset S)) = Finset.univ := by
      ext g; simp
    rw [hpi]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    have hsplit : ∏ i : Fin (2 * m), (if σ (g i) then (1 : ℝ) else -1) =
        ∏ p : S, ∏ i ∈ Finset.univ.filter (fun i => g i = p),
          (if σ (g i) then (1 : ℝ) else -1) := by
      rw [← Finset.prod_biUnion]
      · congr 1; ext i; simp
      · intro p _ q _ hpq
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [Finset.mem_filter] at hi1 hi2
        exact hpq (hi1.2.symm.trans hi2.2)
    rw [hsplit]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hcon : ∀ i ∈ Finset.univ.filter (fun i => g i = p),
        (if σ (g i) then (1 : ℝ) else -1) = (if σ p then (1 : ℝ) else -1) := by
      intro i hi; rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.prod_congr rfl hcon, Finset.prod_const]
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  congr 1
  have hprod_sum : ∑ σ : S → Bool,
      ∏ p : S, (if σ p then (1 : ℝ) else -1) ^ (Finset.univ.filter fun i => g i = p).card =
      ∏ p : S, ((1 : ℝ) ^ (Finset.univ.filter fun i => g i = p).card +
        (-1 : ℝ) ^ (Finset.univ.filter fun i => g i = p).card) := by
    rw [Fintype.prod_sum (fun p b => (if b then (1 : ℝ) else -1) ^ (Finset.univ.filter fun i => g i = p).card)]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [Fintype.sum_bool]
  rw [hprod_sum]
  by_cases hev : ∀ p : S, Even (Finset.univ.filter fun i => g i = p).card
  · simp only [hev, ↓reduceIte]
    have h2 : ∏ p : S, ((1 : ℝ) ^ (Finset.univ.filter fun i => g i = p).card +
        (-1 : ℝ) ^ (Finset.univ.filter fun i => g i = p).card) = (2 : ℝ) ^ S.card := by
      calc ∏ p : S, ((1 : ℝ) ^ (Finset.univ.filter fun i => g i = p).card +
            (-1 : ℝ) ^ (Finset.univ.filter fun i => g i = p).card)
          = ∏ _p : S, (2 : ℝ) := by
            refine Finset.prod_congr rfl fun p _ => ?_
            rcases hev p with ⟨k, hk⟩
            rw [hk, ← two_mul, pow_mul, one_pow, neg_one_sq, one_pow]; norm_num
        _ = (2 : ℝ) ^ S.card := by simp
    rw [h2, one_div_mul_cancel (by positivity)]
  · simp only [hev, ↓reduceIte, mul_zero]
    push_neg at hev
    rcases hev with ⟨p₀, hp₀⟩
    have h0 : (1 : ℝ) ^ (Finset.univ.filter fun i => g i = p₀).card +
        (-1 : ℝ) ^ (Finset.univ.filter fun i => g i = p₀).card = 0 := by
      rcases Nat.not_even_iff_odd.mp hp₀ with ⟨k, hk⟩
      rw [hk, pow_add, pow_mul, neg_one_sq, one_pow, one_pow]; norm_num
    rw [Finset.prod_eq_zero (Finset.mem_univ p₀) h0, mul_zero]

private lemma two_pow_mul_fact_le_two_mul_fact (k : ℕ) :
    2 ^ k * k.factorial ≤ (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    nlinarith

private lemma rademacherMoment_le_factorial (S : Finset ℕ) (a : ℕ → ℝ) (m : ℕ) :
    (1 / (2 : ℝ) ^ S.card) *
      ∑ σ : S → Bool, (∑ p : S, (if σ p then (1 : ℝ) else -1) * a p) ^ (2 * m) ≤
      ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
        (∑ p ∈ S, (a p) ^ 2) ^ m := by
  classical
  induction S using Finset.induction_on generalizing m with
  | empty =>
    cases m with
    | zero => simp
    | succ m => simp [Nat.zero_pow (by omega : 2 * (m + 1) ≠ 0)]
  | @insert p₀ S' hp₀ ih =>
    have hcard : (insert p₀ S').card = S'.card + 1 := Finset.card_insert_of_not_mem hp₀
    have hsum_ins : ∑ p ∈ insert p₀ S', (a p) ^ 2 = (a p₀) ^ 2 + ∑ p ∈ S', (a p) ^ 2 :=
      Finset.sum_insert hp₀
    let eOpt : Option ↥S' ≃ ↥(insert p₀ S') :=
      { toFun := fun o => match o with
          | none => ⟨p₀, Finset.mem_insert_self _ _⟩
          | some p => ⟨p.1, Finset.mem_insert_of_mem p.2⟩
        invFun := fun p => if h : p.1 = p₀ then none else
          some ⟨p.1, (Finset.mem_insert.mp p.2).resolve_left h⟩
        left_inv := fun o => by
          cases o with
          | none => simp
          | some p =>
            have hne : p.1 ≠ p₀ := fun h => hp₀ (h ▸ p.2)
            simp [hne]
        right_inv := fun p => by
          by_cases h : p.1 = p₀
          · simp [h]; exact Subtype.ext h.symm
          · simp [h] }
    let e : (↥(insert p₀ S') → Bool) ≃ Bool × (↥S' → Bool) :=
      { toFun := fun σ => (σ ⟨p₀, Finset.mem_insert_self _ _⟩,
          fun p => σ ⟨p.1, Finset.mem_insert_of_mem p.2⟩)
        invFun := fun bσ p => if h : p.1 = p₀ then bσ.1 else
          bσ.2 ⟨p.1, (Finset.mem_insert.mp p.2).resolve_left h⟩
        left_inv := fun σ => by
          ext p
          by_cases h : p.1 = p₀
          · simp [h]; congr 1; exact Subtype.ext h.symm
          · simp [h]
        right_inv := fun ⟨b, σ'⟩ => by
          ext
          · simp
          · intro p
            have hne : p.1 ≠ p₀ := fun h => hp₀ (h ▸ p.2)
            simp [hne] }
    have hsplit_sum : ∑ σ : ↥(insert p₀ S') → Bool,
        (∑ p : ↥(insert p₀ S'), (if σ p then (1 : ℝ) else -1) * a p) ^ (2 * m) =
        ∑ b : Bool, ∑ σ' : ↥S' → Bool,
          ((if b then (1 : ℝ) else -1) * a p₀ +
            ∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * m) := by
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv e _ _ fun σ => ?_
      congr 1
      rw [← Fintype.sum_equiv eOpt _ (fun o => (if σ (eOpt o) then (1 : ℝ) else -1) * a (eOpt o))
        (fun _ => rfl), Fintype.sum_option]
      rfl
    rw [hcard, hsplit_sum, hsum_ins, Fintype.sum_bool]
    have hbin : ∀ X : ℝ, (a p₀ + X) ^ (2 * m) + (-a p₀ + X) ^ (2 * m) =
        2 * ∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℝ) * (a p₀) ^ (2 * k) * X ^ (2 * (m - k))) := by
      intro X
      rw [add_pow, add_pow, ← Finset.sum_add_distrib]
      have hterm : ∀ j ∈ Finset.range (2 * m + 1),
          (a p₀) ^ j * X ^ (2 * m - j) * (Nat.choose (2 * m) j : ℝ) +
          (-a p₀) ^ j * X ^ (2 * m - j) * (Nat.choose (2 * m) j : ℝ) =
          if Even j then 2 * ((Nat.choose (2 * m) j : ℝ) * (a p₀) ^ j * X ^ (2 * m - j)) else 0 := by
        intro j _
        by_cases hj : Even j
        · simp only [hj, ↓reduceIte]
          rw [hj.neg_pow]; ring
        · simp only [hj, ↓reduceIte]
          rw [(Nat.not_even_iff_odd.mp hj).neg_pow]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
      have hbij : ∑ j ∈ (Finset.range (2 * m + 1)).filter Even,
          2 * ((Nat.choose (2 * m) j : ℝ) * (a p₀) ^ j * X ^ (2 * m - j)) =
          2 * ∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℝ) * (a p₀) ^ (2 * k) * X ^ (2 * (m - k))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_nbij' (fun j => j / 2) (fun k => 2 * k) ?_ ?_ ?_ ?_ ?_
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_range] at hj
          rw [Finset.mem_range]; omega
        · intro k hk
          rw [Finset.mem_range] at hk
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, even_two_mul k⟩
        · intro j hj
          rw [Finset.mem_filter] at hj
          rcases hj.2 with ⟨t, rfl⟩; omega
        · intro k _; omega
        · intro j hj
          rw [Finset.mem_filter] at hj
          rcases hj.2 with ⟨t, rfl⟩
          have : t + t = 2 * t := by ring
          have hdiv : (t + t) / 2 = t := by omega
          rw [this, hdiv, show 2 * m - 2 * t = 2 * (m - t) by omega]
      exact hbij
    have hsum_eq : (∑ σ' : ↥S' → Bool,
        ((1 : ℝ) * a p₀ + ∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * m)) +
        ∑ σ' : ↥S' → Bool,
        ((-1 : ℝ) * a p₀ + ∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * m) =
        2 * ∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ℝ) * (a p₀) ^ (2 * k) *
          ∑ σ' : ↥S' → Bool, (∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * (m - k)) := by
      rw [← Finset.sum_add_distrib]
      simp_rw [one_mul, neg_one_mul, hbin, ← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    rw [show (if true then (1 : ℝ) else -1) = 1 from rfl,
        show (if false then (1 : ℝ) else -1) = -1 from rfl]
    rw [hsum_eq]
    have hpow_half : (1 / (2 : ℝ) ^ (S'.card + 1)) *
        (2 * ∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ℝ) * (a p₀) ^ (2 * k) *
          ∑ σ' : ↥S' → Bool, (∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * (m - k))) =
        ∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ℝ) * ((a p₀) ^ 2) ^ k *
          ((1 / (2 : ℝ) ^ S'.card) *
            ∑ σ' : ↥S' → Bool, (∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * (m - k))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', ← pow_mul]
      field_simp
      ring
    rw [hpow_half]
    calc ∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ℝ) * ((a p₀) ^ 2) ^ k *
          ((1 / (2 : ℝ) ^ S'.card) *
            ∑ σ' : ↥S' → Bool, (∑ p : ↥S', (if σ' p then (1 : ℝ) else -1) * a p) ^ (2 * (m - k)))
        ≤ ∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ℝ) * ((a p₀) ^ 2) ^ k *
            (((2 * (m - k)).factorial : ℝ) / ((2 : ℝ) ^ (m - k) * ((m - k).factorial : ℝ)) *
              (∑ p ∈ S', (a p) ^ 2) ^ (m - k)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_left (ih (m - k)) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg _) _))
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
              ((Nat.choose m k : ℝ) * ((a p₀) ^ 2) ^ k * (∑ p ∈ S', (a p) ^ 2) ^ (m - k)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hcoeff : (Nat.choose (2 * m) (2 * k) : ℝ) *
              (((2 * (m - k)).factorial : ℝ) / ((2 : ℝ) ^ (m - k) * ((m - k).factorial : ℝ))) ≤
              ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (Nat.choose m k : ℝ) := by
            have h2k_le : 2 * k ≤ 2 * m := by omega
            have hch1 : (Nat.choose (2 * m) (2 * k) : ℝ) * ((2 * k).factorial : ℝ) * ((2 * (m - k)).factorial : ℝ) =
                ((2 * m).factorial : ℝ) := by
              exact_mod_cast (by
                rw [show 2 * m - 2 * k = 2 * (m - k) by omega]
                exact Nat.choose_mul_factorial_mul_factorial h2k_le)
            have hch2 : (Nat.choose m k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ) =
                (m.factorial : ℝ) := by
              exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk_le
            have hpow_m : (2 : ℝ) ^ m = (2 : ℝ) ^ k * (2 : ℝ) ^ (m - k) := by
              rw [← pow_add, Nat.add_sub_cancel' hk_le]
            have hfact_k : (2 : ℝ) ^ k * (k.factorial : ℝ) ≤ ((2 * k).factorial : ℝ) := by
              exact_mod_cast two_pow_mul_fact_le_two_mul_fact k
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            calc (Nat.choose (2 * m) (2 * k) : ℝ) * ((2 * (m - k)).factorial : ℝ) * ((2 : ℝ) ^ m * (m.factorial : ℝ))
                = ((Nat.choose (2 * m) (2 * k) : ℝ) * ((2 * (m - k)).factorial : ℝ)) *
                    ((2 : ℝ) ^ k * (2 : ℝ) ^ (m - k) * (m.factorial : ℝ)) := by rw [hpow_m]
              _ = (((2 * m).factorial : ℝ) / ((2 * k).factorial : ℝ)) *
                    ((2 : ℝ) ^ k * (2 : ℝ) ^ (m - k) * (m.factorial : ℝ)) := by
                  congr 1
                  rw [eq_div_iff (by positivity : ((2 * k).factorial : ℝ) ≠ 0)]
                  linarith
              _ = ((2 * m).factorial : ℝ) * ((2 : ℝ) ^ k * (k.factorial : ℝ) / ((2 * k).factorial : ℝ)) *
                    ((2 : ℝ) ^ (m - k) * ((m.factorial : ℝ) / (k.factorial : ℝ))) := by
                  field_simp
              _ ≤ ((2 * m).factorial : ℝ) * 1 * ((2 : ℝ) ^ (m - k) * ((m.factorial : ℝ) / (k.factorial : ℝ))) := by
                  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
                  exact div_le_one_of_le₀ hfact_k (by positivity)
              _ = ((2 * m).factorial : ℝ) * (Nat.choose m k : ℝ) * ((2 : ℝ) ^ (m - k) * ((m.factorial : ℝ) / (k.factorial : ℝ))) := by
                  rw [← hch2]; field_simp
          have hpow_nn : 0 ≤ ((a p₀) ^ 2) ^ k * (∑ p ∈ S', (a p) ^ 2) ^ (m - k) :=
            mul_nonneg (pow_nonneg (sq_nonneg _) _) (pow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
          calc (Nat.choose (2 * m) (2 * k) : ℝ) * ((a p₀) ^ 2) ^ k *
                (((2 * (m - k)).factorial : ℝ) / ((2 : ℝ) ^ (m - k) * ((m - k).factorial : ℝ)) *
                  (∑ p ∈ S', (a p) ^ 2) ^ (m - k))
              = ((Nat.choose (2 * m) (2 * k) : ℝ) *
                  (((2 * (m - k)).factorial : ℝ) / ((2 : ℝ) ^ (m - k) * ((m - k).factorial : ℝ)))) *
                  (((a p₀) ^ 2) ^ k * (∑ p ∈ S', (a p) ^ 2) ^ (m - k)) := by ring
            _ ≤ ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (Nat.choose m k : ℝ) *
                  (((a p₀) ^ 2) ^ k * (∑ p ∈ S', (a p) ^ 2) ^ (m - k)) :=
                mul_le_mul_of_nonneg_right hcoeff hpow_nn
            _ = ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
                  ((Nat.choose m k : ℝ) * ((a p₀) ^ 2) ^ k * (∑ p ∈ S', (a p) ^ 2) ^ (m - k)) := by ring
      _ = ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
            ((a p₀) ^ 2 + ∑ p ∈ S', (a p) ^ 2) ^ m := by
          rw [← Finset.mul_sum, add_pow]
          congr 1
          refine Finset.sum_congr rfl fun k _ => by ring

private lemma summable_prime_log_div_sub_one_sq :
    Summable (fun p : ℕ => if p.Prime ∧ 3 ≤ p then (Real.log p / ((p : ℝ) - 1)) ^ 2 else 0) := by
  have h1 : Summable (fun p : ℕ => (64 : ℝ) / (p : ℝ) ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).const_mul 64 |>.congr fun p => by
      simp [div_eq_mul_inv]
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) (fun p => ?_) h1
  split_ifs with hp
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have hp_pos : (0 : ℝ) < p := by linarith
    have hp1 : (1 : ℝ) / 2 * p ≤ (p : ℝ) - 1 := by linarith
    have hr4 : 0 < (p : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hp_pos _
    have hlog4 : Real.log ((p : ℝ) ^ (1 / 4 : ℝ)) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hr4]
    rw [Real.log_rpow hp_pos] at hlog4
    have hlog_le : Real.log p ≤ 4 * (p : ℝ) ^ (1 / 4 : ℝ) := by linarith
    have hdiv_le : Real.log p / ((p : ℝ) - 1) ≤ 8 / (p : ℝ) ^ (3 / 4 : ℝ) := by
      calc Real.log p / ((p : ℝ) - 1)
          ≤ (4 * (p : ℝ) ^ (1 / 4 : ℝ)) / ((1 / 2 : ℝ) * p) :=
            div_le_div₀ (by positivity) hlog_le (by positivity) hp1
        _ = 8 / (p : ℝ) ^ (3 / 4 : ℝ) := by
            rw [show (p : ℝ) = (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (3 / 4 : ℝ) by
              rw [← Real.rpow_add hp_pos]; norm_num]
            field_simp [hr4.ne']
            ring
    have hsq_le : (Real.log p / ((p : ℝ) - 1)) ^ 2 ≤ (8 / (p : ℝ) ^ (3 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (Real.log_nonneg (by linarith)) (by linarith)) hdiv_le 2
    refine le_trans hsq_le (le_of_eq ?_)
    rw [div_pow, show ((p : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (p : ℝ) ^ (3 / 2 : ℝ) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]; norm_num]
    norm_num
  · positivity

private lemma rademacher_charfun (S : Finset ℕ) (a : ℕ → ℝ) (τ : ℝ) :
    (1 / (2 : ℂ) ^ S.card) *
      ∑ σ : S → Bool, Complex.exp (Complex.I * τ * ∑ p : S, (if σ p then (1 : ℂ) else -1) * a p) =
      ∏ p ∈ S, (Real.cos (τ * a p) : ℂ) := by
  classical
  have h1 : ∀ σ : S → Bool,
      Complex.exp (Complex.I * τ * ∑ p : S, (if σ p then (1 : ℂ) else -1) * a p) =
      ∏ p : S, Complex.exp (Complex.I * τ * ((if σ p then (1 : ℂ) else -1) * a p)) := by
    intro σ
    rw [Finset.mul_sum, Complex.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun p b => Complex.exp (Complex.I * τ * ((if b then (1 : ℂ) else -1) * a p)))]
  have hprod_cos : ∏ p : S, ∑ b : Bool, Complex.exp (Complex.I * τ * ((if b then (1 : ℂ) else -1) * a p)) =
      (2 : ℂ) ^ S.card * ∏ p ∈ S, (Real.cos (τ * a p) : ℂ) := by
    have hterm : ∀ p : S,
        ∑ b : Bool, Complex.exp (Complex.I * τ * ((if b then (1 : ℂ) else -1) * a p)) =
        2 * (Real.cos (τ * a p) : ℂ) := by
      intro p
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, one_mul, neg_one_mul]
      rw [show Complex.I * τ * (a p : ℂ) = (τ * a p : ℝ) * Complex.I by push_cast; ring,
          show Complex.I * τ * -(a p : ℂ) = -((τ * a p : ℝ) * Complex.I) by push_cast; ring,
          Complex.cos_eq_exp_add_exp_neg]
      push_cast; ring
    simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    congr 1
    exact (Finset.prod_coe_sort S (fun p => (Real.cos (τ * a p) : ℂ)))
  rw [hprod_cos, ← mul_assoc, one_div_mul_cancel (by positivity), one_mul]

private def centralDiff (f : ℝ → ℂ) (h : ℝ) (m : ℕ) : ℂ :=
  ((-1 : ℂ) ^ m) * ((h : ℂ) ^ (-(2 * m : ℤ))) *
    ∑ j ∈ Finset.range (2 * m + 1),
      (-1 : ℂ) ^ j * (Nat.choose (2 * m) j : ℂ) * f (((m : ℝ) - (j : ℝ)) * h)

private lemma centralDiff_exp (h x : ℝ) (hh : h ≠ 0) (m : ℕ) :
    centralDiff (fun τ => Complex.exp (Complex.I * τ * x)) h m =
      ((Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) : ℂ) := by
  unfold centralDiff
  have hsum : ∑ j ∈ Finset.range (2 * m + 1),
      (-1 : ℂ) ^ j * (Nat.choose (2 * m) j : ℂ) *
        Complex.exp (Complex.I * (((m : ℝ) - (j : ℝ)) * h) * x) =
      (Complex.exp (Complex.I * (h * x / 2)) - Complex.exp (-Complex.I * (h * x / 2))) ^ (2 * m) := by
    have hpow : (Complex.exp (Complex.I * (h * x / 2)) - Complex.exp (-Complex.I * (h * x / 2))) ^ (2 * m) =
        (Complex.exp (Complex.I * (h * x / 2)) * (1 - Complex.exp (-Complex.I * (h * x)))) ^ (2 * m) := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2; ring
    rw [hpow, mul_pow, sub_eq_add_neg, add_pow]
    have hmul_exp : (Complex.exp (Complex.I * (h * x / 2))) ^ (2 * m) =
        Complex.exp (Complex.I * (m : ℝ) * h * x) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hmul_exp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, neg_pow, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hexp_eq : Complex.I * (m : ℝ) * h * x + (j : ℂ) * (-Complex.I * (h * x)) =
        Complex.I * (((m : ℝ) - (j : ℝ)) * h) * x := by push_cast; ring
    rw [hexp_eq]; ring
  rw [hsum]
  have hsin : Complex.exp (Complex.I * (h * x / 2)) - Complex.exp (-Complex.I * (h * x / 2)) =
      2 * Complex.I * (Real.sin (h * x / 2) : ℂ) := by
    rw [Complex.sin_eq_exp_sub_exp_neg]
    push_cast
    have : Complex.I * (h * x / 2) = (h * x / 2 : ℝ) * Complex.I := by ring
    have : -Complex.I * (h * x / 2) = -((h * x / 2 : ℝ) * Complex.I) := by ring
    field_simp
    ring
  rw [hsin, mul_pow, mul_pow, pow_mul, Complex.I_sq, pow_mul]
  have h2m : (2 : ℂ) ^ (2 * m) = (4 : ℂ) ^ m := by rw [pow_mul]; norm_num
  rw [h2m, zpow_neg, zpow_natCast]
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  push_cast
  field_simp [hhC]
  ring

private lemma sinc_sq_bound (u : ℝ) :
    0 ≤ u ^ 2 - (Real.sin u) ^ 2 ∧ u ^ 2 - (Real.sin u) ^ 2 ≤ u ^ 4 := by
  have h1 : |Real.sin u| ≤ |u| := Real.abs_sin_le_abs u
  have hsq : (Real.sin u) ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs (Real.sin u), sq_abs u]
  refine ⟨sub_nonneg.mpr hsq, ?_⟩
  by_cases hu : 1 ≤ |u|
  · have h1u : u ^ 2 ≤ u ^ 4 := by
      have : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
      nlinarith [sq_nonneg u]
    linarith [sq_nonneg (Real.sin u)]
  · push_neg at hu
    have hsin_diff : |u - Real.sin u| ≤ |u| ^ 3 / 6 := by
      rcases le_total 0 u with hu0 | hu0
      · have hlo : u - u ^ 3 / 6 ≤ Real.sin u := Real.sin_gt_sub_cube hu0 (by linarith [abs_of_nonneg hu0])
        have hhi : Real.sin u ≤ u := Real.sin_le hu0
        rw [abs_of_nonneg (sub_nonneg.mpr hhi), abs_of_nonneg hu0]
        linarith
      · have hlo : (-u) - (-u) ^ 3 / 6 ≤ Real.sin (-u) :=
          Real.sin_gt_sub_cube (neg_nonneg.mpr hu0) (by linarith [abs_of_nonpos hu0])
        have hhi : Real.sin (-u) ≤ -u := Real.sin_le (neg_nonneg.mpr hu0)
        rw [Real.sin_neg] at hlo hhi
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hu0]
        linarith
    have hprod : u ^ 2 - (Real.sin u) ^ 2 = (u - Real.sin u) * (u + Real.sin u) := by ring
    rw [hprod]
    calc (u - Real.sin u) * (u + Real.sin u)
        ≤ |(u - Real.sin u) * (u + Real.sin u)| := le_abs_self _
      _ = |u - Real.sin u| * |u + Real.sin u| := abs_mul _ _
      _ ≤ (|u| ^ 3 / 6) * (2 * |u|) := by
          refine mul_le_mul hsin_diff ?_ (abs_nonneg _) (by positivity)
          calc |u + Real.sin u| ≤ |u| + |Real.sin u| := abs_add_le _ _
            _ ≤ |u| + |u| := add_le_add le_rfl h1
            _ = 2 * |u| := by ring
      _ = |u| ^ 4 / 3 := by ring
      _ = u ^ 4 / 3 := by
          congr 1; rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
      _ ≤ u ^ 4 := by linarith [pow_nonneg (sq_nonneg u) 2, show u ^ 4 = (u ^ 2) ^ 2 by ring]

private lemma sinc_pow_diff_bound (h x : ℝ) (hh : h ≠ 0) (m : ℕ) :
    0 ≤ x ^ (2 * m) - (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) ∧
    x ^ (2 * m) - (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) ≤
      (m : ℝ) * h ^ 2 * x ^ (2 * (m + 1)) := by
  set A : ℝ := x ^ 2
  set B : ℝ := (Real.sin (h * x / 2) / (h / 2)) ^ 2
  have hB_nn : 0 ≤ B := sq_nonneg _
  have hBA : B ≤ A := by
    have h1 := Real.abs_sin_le_abs (h * x / 2)
    have h2 : |Real.sin (h * x / 2) / (h / 2)| ≤ |x| := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr (by positivity : h / 2 ≠ 0))]
      calc |Real.sin (h * x / 2)| ≤ |h * x / 2| := h1
        _ = |x| * |h / 2| := by rw [show h * x / 2 = x * (h / 2) by ring, abs_mul]
    nlinarith [sq_abs (Real.sin (h * x / 2) / (h / 2)), sq_abs x]
  have hdiff_AB : A - B ≤ h ^ 2 * x ^ 4 := by
    have hs := (sinc_sq_bound (h * x / 2)).2
    have hAB_eq : A - B = ((h * x / 2) ^ 2 - (Real.sin (h * x / 2)) ^ 2) / (h / 2) ^ 2 := by
      have hh2 : (h / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (by positivity)
      field_simp [hh2]; ring
    rw [hAB_eq, div_le_iff₀ (pow_pos (abs_pos.mpr (by positivity : h / 2 ≠ 0)) 2 |>.trans_le (by rw [sq_abs]))]
    calc (h * x / 2) ^ 2 - Real.sin (h * x / 2) ^ 2
        ≤ (h * x / 2) ^ 4 := hs
      _ = h ^ 2 * x ^ 4 * (h / 2) ^ 2 / 4 := by ring
      _ ≤ h ^ 2 * x ^ 4 * (h / 2) ^ 2 := by
          have : 0 ≤ h ^ 2 * x ^ 4 * (h / 2) ^ 2 := by positivity
          linarith
  have hpow_AB : 0 ≤ A ^ m - B ^ m ∧ A ^ m - B ^ m ≤ (m : ℝ) * A ^ (m - 1) * (A - B) := by
    induction m with
    | zero => simp
    | succ k ih =>
      have hk1 : A ^ (k + 1) - B ^ (k + 1) = (A - B) * A ^ k + B * (A ^ k - B ^ k) := by ring
      rw [hk1]
      refine ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr hBA) (pow_nonneg (sq_nonneg x) k))
        (mul_nonneg hB_nn ih.1), ?_⟩
      rcases k with _ | k
      · simp; nlinarith
      · have hB_le_A : B ≤ A := hBA
        calc (A - B) * A ^ (k + 1) + B * (A ^ (k + 1) - B ^ (k + 1))
            ≤ (A - B) * A ^ (k + 1) + A * ((k + 1 : ℝ) * A ^ k * (A - B)) := by
              refine add_le_add le_rfl (le_trans (mul_le_mul_of_nonneg_left ih.2 hB_nn) ?_)
              exact mul_le_mul_of_nonneg_right hB_le_A (by positivity)
          _ = ((k + 1 : ℕ) + 1 : ℝ) * A ^ ((k + 1) + 1 - 1) * (A - B) := by
              push_cast; simp; ring
  have hpowA : A ^ m = x ^ (2 * m) := by rw [← pow_mul]; ring_nf
  have hpowB : B ^ m = (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) := by rw [← pow_mul]; ring_nf
  rw [← hpowA, ← hpowB]
  refine ⟨hpow_AB.1, ?_⟩
  rcases m with _ | m
  · simp [hpow_AB.1]
  · refine le_trans hpow_AB.2 ?_
    have h1 : A ^ m * (A - B) ≤ A ^ m * (h ^ 2 * x ^ 4) :=
      mul_le_mul_of_nonneg_left hdiff_AB (pow_nonneg (sq_nonneg x) m)
    have h2 : ((m + 1 : ℕ) : ℝ) * A ^ m * (h ^ 2 * x ^ 4) =
        ((m + 1 : ℕ) : ℝ) * h ^ 2 * x ^ (2 * (m + 1 + 1)) := by
      have : A ^ m = x ^ (2 * m) := by rw [← pow_mul]; ring_nf
      rw [this, show 2 * (m + 1 + 1) = 2 * m + 4 by omega, pow_add]
      ring
    linarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (m + 1))]

theorem prop_2_6 :
    ∃ (Φ ρ : ℝ → ℝ),
      (∀ τ : ℝ, Tendsto (fun B : ℕ => ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
        Real.cos (τ * Real.log p / ((p : ℝ) - 1))) atTop (𝓝 (Φ τ))) ∧
      (∀ x : ℝ, 0 < ρ x ∧ ρ (-x) = ρ x) ∧
      ContDiff ℝ ⊤ ρ ∧
      (∫ x : ℝ, ρ x) = 1 ∧
      (∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ B₀ : ℕ, ∀ B ≥ B₀, ∃ r₀ : ℕ, ∀ r ≥ r₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
          |((1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (SigmaParityTrunc r n B) ^ (2 * m)) -
            ∫ x : ℝ, x ^ (2 * m) * ρ x| ≤ ε) := by
  obtain ⟨Φ, ρ, hΦ_lim, hρ_pos, hρ_smooth, hρ_int1, hρ_cf⟩ := jessen_wintner_rademacher_density
  refine ⟨Φ, ρ, hΦ_lim, hρ_pos, hρ_smooth, hρ_int1, fun m ε hε => ?_⟩
  have hρ_int : MeasureTheory.Integrable ρ :=
    MeasureTheory.integrable_of_integral_eq_one hρ_int1
  set S2 : ℝ := ∑' p : ℕ, if p.Prime ∧ 3 ≤ p then (Real.log p / ((p : ℝ) - 1)) ^ 2 else 0
  have hS2_bd : ∀ B : ℕ,
      ∑ p ∈ (Finset.Icc 3 B).filter Nat.Prime, (Real.log p / ((p : ℝ) - 1)) ^ 2 ≤ S2 := by
    intro B
    have hsub : ∑ p ∈ (Finset.Icc 3 B).filter Nat.Prime, (Real.log p / ((p : ℝ) - 1)) ^ 2 =
        ∑ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
          (if p.Prime ∧ 3 ≤ p then (Real.log p / ((p : ℝ) - 1)) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      simp [hp.2, hp.1.1]
    rw [hsub]
    exact Summable.sum_le_tsum _ (fun p _ => by split_ifs <;> positivity) summable_prime_log_div_sub_one_sq
  let M_const (k : ℕ) : ℝ :=
    ((2 * k).factorial : ℝ) / ((2 : ℝ) ^ k * (k.factorial : ℝ)) * S2 ^ k
  have hM_nn : ∀ k, 0 ≤ M_const k := fun k =>
    mul_nonneg (by positivity) (pow_nonneg (tsum_nonneg fun p => by split_ifs <;> positivity) k)
  have hrad_bd : ∀ (B k : ℕ), rademacherMoment ((Finset.Icc 3 B).filter Nat.Prime) (2 * k) ≤ M_const k := by
    intro B k
    refine le_trans (rademacherMoment_le_factorial _ _ k) ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hS2_bd B) k)
      (by positivity)
  have hcd_Φ_eq : ∀ (h : ℝ) (hh : h ≠ 0) (k : ℕ),
      (centralDiff (fun τ => (Φ τ : ℂ)) h k).re =
        ∫ x : ℝ, (Real.sin (h * x / 2) / (h / 2)) ^ (2 * k) * ρ x := by
    intro h hh k
    unfold centralDiff
    have h_int_fin : ∀ j ∈ Finset.range (2 * k + 1),
        MeasureTheory.Integrable (fun x : ℝ =>
          (-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) *
            Complex.exp (Complex.I * (((k : ℝ) - (j : ℝ)) * h) * x) * (ρ x : ℂ)) := by
      intro j _
      refine MeasureTheory.Integrable.mono' (hρ_int.norm.const_mul _) ?_ ?_
      · exact ((Continuous.mul (continuous_const.mul (Complex.continuous_exp.comp (by continuity)))
          (Complex.continuous_ofReal.comp hρ_smooth.continuous)).aestronglyMeasurable)
      · filter_upwards with x
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
          Complex.norm_natCast, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (hρ_pos x).1.le, mul_comm]
        exact mul_le_mul_of_nonneg_right (Nat.cast_nonneg _) (hρ_pos x).1.le
    have hsum_int : ((-1 : ℂ) ^ k) * ((h : ℂ) ^ (-(2 * k : ℤ))) *
        ∑ j ∈ Finset.range (2 * k + 1),
          (-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) * (Φ (((k : ℝ) - (j : ℝ)) * h) : ℂ) =
        ∫ x : ℝ, centralDiff (fun τ => Complex.exp (Complex.I * τ * x)) h k * (ρ x : ℂ) := by
      simp_rw [← hρ_cf, Finset.mul_sum]
      have h1 : ∀ j ∈ Finset.range (2 * k + 1),
          (-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) *
            ∫ x : ℝ, Complex.exp (Complex.I * (((k : ℝ) - (j : ℝ)) * h) * x) * (ρ x : ℂ) =
          ∫ x : ℝ, ((-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) *
            Complex.exp (Complex.I * (((k : ℝ) - (j : ℝ)) * h) * x) * (ρ x : ℂ)) := by
        intro j _
        rw [← MeasureTheory.integral_const_mul]
        congr 1; ext x; ring
      rw [Finset.sum_congr rfl h1, ← MeasureTheory.integral_finset_sum _ h_int_fin,
        ← MeasureTheory.integral_const_mul]
      congr 1; ext x
      unfold centralDiff
      rw [Finset.sum_mul, Finset.mul_sum]
      ring
    rw [hsum_int]
    have hcd_re : ∀ x : ℝ,
        centralDiff (fun τ => Complex.exp (Complex.I * τ * x)) h k * (ρ x : ℂ) =
        (((Real.sin (h * x / 2) / (h / 2)) ^ (2 * k) * ρ x : ℝ) : ℂ) := by
      intro x
      rw [centralDiff_exp h x hh k]
      push_cast; ring
    simp_rw [hcd_re, integral_ofReal, Complex.ofReal_re]
  have hcd_Φ_bd : ∀ (h : ℝ) (hh : h ≠ 0) (k : ℕ),
      (centralDiff (fun τ => (Φ τ : ℂ)) h k).re ≤ M_const k := by
    intro h hh k
    let Φ_B (B : ℕ) (τ : ℝ) : ℝ :=
      ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime, Real.cos (τ * Real.log p / ((p : ℝ) - 1))
    have hcd_B_bd : ∀ B : ℕ, (centralDiff (fun τ => (Φ_B B τ : ℂ)) h k).re ≤ M_const k := by
      intro B
      set P_B := (Finset.Icc 3 B).filter Nat.Prime
      have h_cf_B : ∀ τ : ℝ, (Φ_B B τ : ℂ) =
          (1 / (2 : ℂ) ^ P_B.card) *
            ∑ σ : P_B → Bool, Complex.exp (Complex.I * τ *
              ∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) := by
        intro τ
        rw [rademacher_charfun]
        unfold Φ_B
        push_cast
        refine Finset.prod_congr rfl fun p _ => by ring_nf
      have hcd_eq : centralDiff (fun τ => (Φ_B B τ : ℂ)) h k =
          (1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
            ((Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
              (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * k) : ℂ) := by
        unfold centralDiff
        simp_rw [h_cf_B]
        rw [Finset.sum_comm]
        have hswap : ∑ j ∈ Finset.range (2 * k + 1),
            (-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) *
              ((1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
                Complex.exp (Complex.I * (((k : ℝ) - (j : ℝ)) * h) *
                  (∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                    (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))))) =
            (1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
              ∑ j ∈ Finset.range (2 * k + 1),
                (-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) *
                  Complex.exp (Complex.I * (((k : ℝ) - (j : ℝ)) * h) *
                    (∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                      (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)))) := by
          rw [Finset.mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => by push_cast; ring
        rw [hswap]
        have hmul : (-1 : ℂ) ^ k * (h : ℂ) ^ (-(2 * k : ℤ)) *
            ((1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
              ∑ j ∈ Finset.range (2 * k + 1),
                (-1 : ℂ) ^ j * (Nat.choose (2 * k) j : ℂ) *
                  Complex.exp (Complex.I * (((k : ℝ) - (j : ℝ)) * h) *
                    (∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                      (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))))) =
            (1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
              centralDiff (fun τ => Complex.exp (Complex.I * τ *
                (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
                  (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))))) h k := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          unfold centralDiff; ring
        rw [hmul]
        congr 1
        refine Finset.sum_congr rfl fun σ _ => centralDiff_exp h _ hh k
      rw [hcd_eq]
      have hre : ((1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
          ((Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
            (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * k) : ℂ)).re =
          (1 / (2 : ℝ) ^ P_B.card) * ∑ σ : P_B → Bool,
            (Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
              (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * k) := by
        push_cast; simp
      rw [hre]
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)) (hrad_bd B k)
      have hs := (sinc_pow_diff_bound h (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
        (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) hh k).1
      linarith
    have hlim : Tendsto (fun B : ℕ => (centralDiff (fun τ => (Φ_B B τ : ℂ)) h k).re) atTop
        (𝓝 (centralDiff (fun τ => (Φ τ : ℂ)) h k).re) := by
      refine Complex.continuous_re.continuousAt.tendsto.comp ?_
      unfold centralDiff
      refine tendsto_const_nhds.mul (tendsto_finset_sum _ fun j _ => tendsto_const_nhds.mul ?_)
      refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
      exact hΦ_lim (((k : ℝ) - (j : ℝ)) * h)
    exact le_of_tendsto hlim (Eventually.of_forall hcd_B_bd)
  -- Integrability of `x^(2*k) * ρ x` via Fatou's lemma for all `k`
  have hint_pow : ∀ k : ℕ, MeasureTheory.Integrable (fun x : ℝ => x ^ (2 * k) * ρ x) := by
    intro k
    have hseq : ∀ x : ℝ, Tendsto (fun N : ℕ =>
        ENNReal.ofReal ((Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)) ^ (2 * k) * ρ x))
        atTop (𝓝 (ENNReal.ofReal (x ^ (2 * k) * ρ x))) := by
      intro x
      refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
      refine Tendsto.mul ?_ tendsto_const_nhds
      refine Tendsto.pow ?_ (2 * k)
      by_cases hx : x = 0
      · subst hx; simp
      · have h0 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * x / 2) atTop (𝓝 0) := by
          simpa using ((tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul_const x).div_const 2
        have hsinc : Tendsto (fun u : ℝ => Real.sin u / u) (𝓝[≠] 0) (𝓝 1) := by
          simpa using Real.tendsto_sin_div_self
        have hcomp : Tendsto (fun N : ℕ =>
            Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) * x / 2)) atTop (𝓝 1) := by
          refine hsinc.comp (tendsto_nhdsWithin_iff.mpr ⟨h0, Eventually.of_forall fun N => ?_⟩)
          have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
          exact div_ne_zero (mul_ne_zero (by positivity) hx) (by norm_num)
        have hmul : Tendsto (fun N : ℕ =>
            (Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) * x / 2)) * x) atTop (𝓝 (1 * x)) :=
          hcomp.mul_const x
        rw [one_mul] at hmul
        refine hmul.congr fun N => ?_
        have hN : (1 / ((N : ℝ) + 1)) / 2 ≠ 0 := by positivity
        field_simp [hN, hx]; ring
    have hfatou : ∫⁻ x : ℝ, ENNReal.ofReal (x ^ (2 * k) * ρ x) ≤ ENNReal.ofReal (M_const k) := by
      have hliminf : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ (2 * k) * ρ x)) ≤
          Filter.liminf (fun N : ℕ => ∫⁻ x : ℝ,
            ENNReal.ofReal ((Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)) ^ (2 * k) * ρ x)) atTop := by
        refine le_trans (le_of_eq (MeasureTheory.lintegral_congr fun x => (hseq x).liminf_eq.symm)) ?_
        refine MeasureTheory.lintegral_liminf_le fun N => ?_
        exact (ENNReal.continuous_ofReal.comp (by continuity)).measurable
      refine le_trans hliminf (Filter.liminf_le_of_le (by isBoundedDefault) (Eventually.of_forall fun N => ?_))
      have hN_ne : (1 / ((N : ℝ) + 1)) ≠ 0 := by positivity
      have hbd := hcd_Φ_bd (1 / ((N : ℝ) + 1)) hN_ne k
      rw [hcd_Φ_eq (1 / ((N : ℝ) + 1)) hN_ne k] at hbd
      have hintN : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)) ^ (2 * k) * ρ x) := by
        refine MeasureTheory.Integrable.mono' (hρ_int.const_mul (((2 : ℝ) * ((N : ℝ) + 1)) ^ (2 * k))) ?_ ?_
        · exact (Continuous.mul (by continuity) hρ_smooth.continuous).aestronglyMeasurable
        · filter_upwards with x
          have hnn : 0 ≤ (Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)) ^ (2 * k) := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hρ_pos x).1.le)]
          refine mul_le_mul_of_nonneg_right ?_ (hρ_pos x).1.le
          have hs1 : |Real.sin ((1 / ((N : ℝ) + 1)) * x / 2)| ≤ 1 := Real.abs_sin_le_one _
          have hdiv : |Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)| ≤ 2 * ((N : ℝ) + 1) := by
            rw [abs_div, show |(1 / ((N : ℝ) + 1)) / 2| = (2 * ((N : ℝ) + 1))⁻¹ by
              rw [abs_of_pos (by positivity)]; ring]
            rw [div_inv_eq_mul]
            exact mul_le_of_le_one_left (by positivity) hs1
          calc (Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)) ^ (2 * k)
              = |Real.sin ((1 / ((N : ℝ) + 1)) * x / 2) / ((1 / ((N : ℝ) + 1)) / 2)| ^ (2 * k) := by
                rw [show 2 * k = k * 2 by ring, pow_mul, ← sq_abs, ← pow_mul]
                ring_nf
            _ ≤ (2 * ((N : ℝ) + 1)) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) hdiv _
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintN (Eventually.of_forall fun x =>
        mul_nonneg (by positivity) (hρ_pos x).1.le)]
      exact ENNReal.ofReal_le_ofReal hbd
    refine ⟨(Continuous.mul (continuous_pow (2 * k)) hρ_smooth.continuous).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have hcon : (∫⁻ x : ℝ, ENNReal.ofReal ‖x ^ (2 * k) * ρ x‖) =
        ∫⁻ x : ℝ, ENNReal.ofReal (x ^ (2 * k) * ρ x) := by
      refine MeasureTheory.lintegral_congr fun x => ?_
      have hnn : 0 ≤ x ^ (2 * k) * ρ x := mul_nonneg (by positivity) (hρ_pos x).1.le
      rw [Real.norm_of_nonneg hnn]
    rw [hcon]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  set I_m1 : ℝ := ∫ x : ℝ, x ^ (2 * (m + 1)) * ρ x
  have hI_m1_nn : 0 ≤ I_m1 :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (by positivity) (hρ_pos x).1.le
  set K_tail : ℝ := (m : ℝ) * max I_m1 (M_const (m + 1)) + 1
  have hK_pos : 0 < K_tail := by positivity
  set h : ℝ := Real.sqrt (ε / (6 * K_tail))
  have hh_pos : 0 < h := Real.sqrt_pos.mpr (by positivity)
  have hh_sq : h ^ 2 = ε / (6 * K_tail) := Real.sq_sqrt (by positivity)
  have h_err_Φ : |∫ x : ℝ, x ^ (2 * m) * ρ x - (centralDiff (fun τ => (Φ τ : ℂ)) h m).re| ≤ ε / 6 := by
    rw [hcd_Φ_eq h hh_pos.ne' m]
    have hint_diff : MeasureTheory.Integrable (fun x : ℝ =>
        x ^ (2 * m) * ρ x - (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) * ρ x) := by
      refine (hint_pow m).sub ?_
      refine MeasureTheory.Integrable.mono' (hint_pow m) ?_ ?_
      · exact (Continuous.mul (by continuity) hρ_smooth.continuous).aestronglyMeasurable
      · filter_upwards with x
        have hnn : 0 ≤ (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) := by positivity
        rw [Real.norm_of_nonneg (mul_nonneg hnn (hρ_pos x).1.le),
          Real.norm_of_nonneg (mul_nonneg (by positivity) (hρ_pos x).1.le)]
        exact mul_le_mul_of_nonneg_right
          (sub_nonneg.mp (sinc_pow_diff_bound h x hh_pos.ne' m).1) (hρ_pos x).1.le
    have hint_sin : MeasureTheory.Integrable (fun x : ℝ =>
        (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) * ρ x) := by
      refine MeasureTheory.Integrable.mono' (hint_pow m) ?_ ?_
      · exact (Continuous.mul (by continuity) hρ_smooth.continuous).aestronglyMeasurable
      · filter_upwards with x
        have hnn : 0 ≤ (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) := by positivity
        rw [Real.norm_of_nonneg (mul_nonneg hnn (hρ_pos x).1.le),
          Real.norm_of_nonneg (mul_nonneg (by positivity) (hρ_pos x).1.le)]
        exact mul_le_mul_of_nonneg_right
          (sub_nonneg.mp (sinc_pow_diff_bound h x hh_pos.ne' m).1) (hρ_pos x).1.le
    rw [← MeasureTheory.integral_sub (hint_pow m) hint_sin]
    have hnn_int : 0 ≤ ∫ x : ℝ, (x ^ (2 * m) * ρ x - (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) * ρ x) :=
      MeasureTheory.integral_nonneg fun x => by
        rw [← sub_mul]
        exact mul_nonneg (sinc_pow_diff_bound h x hh_pos.ne' m).1 (hρ_pos x).1.le
    rw [abs_of_nonneg hnn_int]
    calc ∫ x : ℝ, (x ^ (2 * m) * ρ x - (Real.sin (h * x / 2) / (h / 2)) ^ (2 * m) * ρ x)
        ≤ ∫ x : ℝ, ((m : ℝ) * h ^ 2) * (x ^ (2 * (m + 1)) * ρ x) := by
          refine MeasureTheory.integral_mono hint_diff ((hint_pow (m + 1)).const_mul _) fun x => ?_
          rw [← sub_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (sinc_pow_diff_bound h x hh_pos.ne' m).2 (hρ_pos x).1.le
      _ = (m : ℝ) * h ^ 2 * I_m1 := MeasureTheory.integral_const_mul _ _
      _ ≤ K_tail * h ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg h)
          calc (m : ℝ) * I_m1 ≤ (m : ℝ) * max I_m1 (M_const (m + 1)) :=
                mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg m)
            _ ≤ K_tail := by linarith
      _ = ε / 6 := by rw [hh_sq]; field_simp [hK_pos.ne']
  let Φ_B (B : ℕ) (τ : ℝ) : ℝ :=
    ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime, Real.cos (τ * Real.log p / ((p : ℝ) - 1))
  have hlim_cd : Tendsto (fun B : ℕ => (centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re) atTop
      (𝓝 (centralDiff (fun τ => (Φ τ : ℂ)) h m).re) := by
    refine Complex.continuous_re.continuousAt.tendsto.comp ?_
    unfold centralDiff
    refine tendsto_const_nhds.mul (tendsto_finset_sum _ fun j _ => tendsto_const_nhds.mul ?_)
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hΦ_lim (((m : ℝ) - (j : ℝ)) * h))
  obtain ⟨B₀, hB₀⟩ := Metric.tendsto_atTop.mp hlim_cd (ε / 6) (by positivity)
  refine ⟨B₀, fun B hB => ?_⟩
  set P_B := (Finset.Icc 3 B).filter Nat.Prime
  have h_err_B_rad : |rademacherMoment P_B (2 * m) - ∫ x : ℝ, x ^ (2 * m) * ρ x| ≤ ε / 2 := by
    have h_cf_B : ∀ τ : ℝ, (Φ_B B τ : ℂ) =
        (1 / (2 : ℂ) ^ P_B.card) *
          ∑ σ : P_B → Bool, Complex.exp (Complex.I * τ *
            ∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
              (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) := by
      intro τ
      rw [rademacher_charfun]
      unfold Φ_B
      push_cast
      refine Finset.prod_congr rfl fun p _ => by ring_nf
    have hcd_eq : (centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re =
        (1 / (2 : ℝ) ^ P_B.card) * ∑ σ : P_B → Bool,
          (Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
            (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * m) := by
      have hcdC : centralDiff (fun τ => (Φ_B B τ : ℂ)) h m =
          (1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
            ((Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
              (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * m) : ℂ) := by
        unfold centralDiff
        simp_rw [h_cf_B]
        rw [Finset.sum_comm]
        have hswap : ∑ j ∈ Finset.range (2 * m + 1),
            (-1 : ℂ) ^ j * (Nat.choose (2 * m) j : ℂ) *
              ((1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
                Complex.exp (Complex.I * (((m : ℝ) - (j : ℝ)) * h) *
                  (∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                    (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))))) =
            (1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
              ∑ j ∈ Finset.range (2 * m + 1),
                (-1 : ℂ) ^ j * (Nat.choose (2 * m) j : ℂ) *
                  Complex.exp (Complex.I * (((m : ℝ) - (j : ℝ)) * h) *
                    (∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                      (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)))) := by
          rw [Finset.mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => by push_cast; ring
        rw [hswap]
        have hmul : (-1 : ℂ) ^ m * (h : ℂ) ^ (-(2 * m : ℤ)) *
            ((1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
              ∑ j ∈ Finset.range (2 * m + 1),
                (-1 : ℂ) ^ j * (Nat.choose (2 * m) j : ℂ) *
                  Complex.exp (Complex.I * (((m : ℝ) - (j : ℝ)) * h) *
                    (∑ p : P_B, (if σ p then (1 : ℂ) else -1) *
                      (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))))) =
            (1 / (2 : ℂ) ^ P_B.card) * ∑ σ : P_B → Bool,
              centralDiff (fun τ => Complex.exp (Complex.I * τ *
                (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
                  (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))))) h m := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          unfold centralDiff; ring
        rw [hmul]
        congr 1
        refine Finset.sum_congr rfl fun σ _ => centralDiff_exp h _ hh_pos.ne' m
      rw [hcdC]; push_cast; simp
    have h_err_B1 : |rademacherMoment P_B (2 * m) - (centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re| ≤ ε / 6 := by
      rw [hcd_eq]
      unfold rademacherMoment
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      have hnn : 0 ≤ (1 / (2 : ℝ) ^ P_B.card) * ∑ σ : P_B → Bool,
          ((∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
            (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) ^ (2 * m) -
          (Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
            (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * m)) := by
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => ?_)
        exact (sinc_pow_diff_bound h _ hh_pos.ne' m).1
      rw [abs_of_nonneg hnn]
      calc (1 / (2 : ℝ) ^ P_B.card) * ∑ σ : P_B → Bool,
            ((∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
              (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) ^ (2 * m) -
            (Real.sin (h * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
              (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) / 2) / (h / 2)) ^ (2 * m))
          ≤ (1 / (2 : ℝ) ^ P_B.card) * ∑ σ : P_B → Bool,
              ((m : ℝ) * h ^ 2 * (∑ p : P_B, (if σ p then (1 : ℝ) else -1) *
                (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) ^ (2 * (m + 1))) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
            exact (sinc_pow_diff_bound h _ hh_pos.ne' m).2
        _ = (m : ℝ) * h ^ 2 * rademacherMoment P_B (2 * (m + 1)) := by
            rw [← Finset.mul_sum]; unfold rademacherMoment; ring
        _ ≤ (m : ℝ) * h ^ 2 * M_const (m + 1) :=
            mul_le_mul_of_nonneg_left (hrad_bd B (m + 1)) (by positivity)
        _ ≤ K_tail * h ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg h)
            calc (m : ℝ) * M_const (m + 1) ≤ (m : ℝ) * max I_m1 (M_const (m + 1)) :=
                  mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg m)
              _ ≤ K_tail := by linarith
        _ = ε / 6 := by rw [hh_sq]; field_simp [hK_pos.ne']
    have h_err_B2 : |(centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re -
        (centralDiff (fun τ => (Φ τ : ℂ)) h m).re| ≤ ε / 6 :=
      le_of_lt (by simpa [Real.dist_eq] using hB₀ B hB)
    linarith [abs_add_le
      (rademacherMoment P_B (2 * m) - (centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re)
      ((centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re - (centralDiff (fun τ => (Φ τ : ℂ)) h m).re),
      abs_add_le
      (rademacherMoment P_B (2 * m) - (centralDiff (fun τ => (Φ_B B τ : ℂ)) h m).re)
      ((centralDiff (fun τ => (Φ τ : ℂ)) h m).re - ∫ x : ℝ, x ^ (2 * m) * ρ x),
      abs_sub_comm (∫ x : ℝ, x ^ (2 * m) * ρ x) (centralDiff (fun τ => (Φ τ : ℂ)) h m).re]
  set A_B : ℝ := ∑ p ∈ P_B, Real.log p / ((p : ℝ) - 1)
  have hA_B_nn : 0 ≤ A_B := Finset.sum_nonneg fun p hp => by
    have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))) (by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3; linarith)
  have hr_lim : Tendsto (fun r : ℕ => A_B ^ (2 * m) * (1 / 3 : ℝ) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1)).const_mul (A_B ^ (2 * m))
  obtain ⟨r₀, hr₀⟩ := Metric.tendsto_atTop.mp hr_lim (ε / 4) (by positivity)
  refine ⟨r₀, fun r hr => ?_⟩
  set M_B : ℕ := ∏ p ∈ P_B, p ^ (2 * r + 1)
  have hP_B_pr : ∀ p ∈ P_B, p.Prime ∧ 3 ≤ p := fun p hp => by
    simp only [P_B, Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨hp.2, hp.1.1⟩
  have hM_B_pos : 0 < M_B := Finset.prod_pos fun p hp => pow_pos (hP_B_pr p hp).1.pos _
  have h_err_r : |(1 / (M_B : ℝ)) * ∑ n ∈ Finset.range M_B, (SigmaParityTrunc r n B) ^ (2 * m) -
      rademacherMoment P_B (2 * m)| ≤ ε / 4 := by
    have hexp_trunc : ∀ n : ℕ, (SigmaParityTrunc r n B) ^ (2 * m) =
        ∑ g : Fin (2 * m) → P_B,
          (∏ p : P_B, (truncParitySign (p : ℕ) r n) ^ (Finset.univ.filter fun i => g i = p).card) *
            ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) := by
      intro n
      unfold SigmaParityTrunc
      rw [← Finset.sum_coe_sort P_B]
      rw [Finset.sum_pow' (Finset.univ : Finset P_B) _ (2 * m)]
      have hpi : (Fintype.piFinset fun _ : Fin (2 * m) => (Finset.univ : Finset P_B)) = Finset.univ := by
        ext g; simp
      rw [hpi]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.prod_mul_distrib]
      congr 1
      have hsplit : ∏ i : Fin (2 * m), truncParitySign (g i : ℕ) r n =
          ∏ p : P_B, ∏ i ∈ Finset.univ.filter (fun i => g i = p), truncParitySign (g i : ℕ) r n := by
        rw [← Finset.prod_biUnion]
        · congr 1; ext i; simp
        · intro p _ q _ hpq
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          simp only [Finset.mem_filter] at hi1 hi2
          exact hpq (hi1.2.symm.trans hi2.2)
      rw [hsplit]
      refine Finset.prod_congr rfl fun p _ => ?_
      have hcon : ∀ i ∈ Finset.univ.filter (fun i => g i = p),
          truncParitySign (g i : ℕ) r n = truncParitySign (p : ℕ) r n := by
        intro i hi; rw [(Finset.mem_filter.mp hi).2]
      rw [Finset.prod_congr rfl hcon, Finset.prod_const]
    simp_rw [hexp_trunc]
    rw [Finset.sum_comm, Finset.mul_sum, rademacherMoment_eq_even_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm_bd : ∀ g : Fin (2 * m) → P_B,
        |(1 / (M_B : ℝ)) * ∑ n ∈ Finset.range M_B,
            (∏ p : P_B, (truncParitySign (p : ℕ) r n) ^ (Finset.univ.filter fun i => g i = p).card) *
              ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) -
          (if ∀ p : P_B, Even (Finset.univ.filter fun i => g i = p).card then (1 : ℝ) else 0) *
            ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1))| ≤
          (1 / 3 : ℝ) ^ r * ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) := by
      intro g
      rw [← Finset.sum_mul, ← mul_assoc, ← sub_mul, abs_mul]
      have hprod_nn : 0 ≤ ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) :=
        Finset.prod_nonneg fun i _ => by
          have hp3 : 3 ≤ (g i : ℕ) := (hP_B_pr _ (g i).2).2
          exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (g i : ℕ)))) (by
            have : (3 : ℝ) ≤ (g i : ℕ) := by exact_mod_cast hp3; linarith)
      rw [abs_of_nonneg hprod_nn]
      refine mul_le_mul_of_nonneg_right ?_ hprod_nn
      let c : ℕ → ℕ := fun p => if hp : p ∈ P_B then
        (Finset.univ.filter fun i => g i = ⟨p, hp⟩).card else 0
      have hprod_eq : ∀ n, (∏ p : P_B, (truncParitySign (p : ℕ) r n) ^ (Finset.univ.filter fun i => g i = p).card) =
          ∏ p ∈ P_B, (truncParitySign p r n) ^ (c p) := by
        intro n
        rw [← Finset.prod_coe_sort P_B (fun p => (truncParitySign p r n) ^ (c p))]
        refine Finset.prod_congr rfl fun p _ => by simp [c, p.2]
      simp_rw [hprod_eq]
      rw [crt_prod_sum P_B hP_B_pr r c]
      by_cases hev : ∀ p : P_B, Even (Finset.univ.filter fun i => g i = p).card
      · simp only [hev, ↓reduceIte]
        have hsum1 : ∏ p ∈ P_B, ∑ n ∈ Finset.range (p ^ (2 * r + 1)), (truncParitySign p r n) ^ (c p) =
            (M_B : ℝ) := by
          have h1 : ∀ p ∈ P_B, ∑ n ∈ Finset.range (p ^ (2 * r + 1)), (truncParitySign p r n) ^ (c p) =
              ((p ^ (2 * r + 1) : ℕ) : ℝ) := by
            intro p hp
            have hc_ev : Even (c p) := by simpa [c, hp] using hev ⟨p, hp⟩
            rcases hc_ev with ⟨k, hk⟩
            have hsq1 : ∀ n, (truncParitySign p r n) ^ (c p) = 1 := fun n => by
              rw [hk, ← two_mul, pow_mul, truncParitySign_sq, one_pow]
            simp [hsq1, Finset.sum_const, Finset.card_range]
          rw [Finset.prod_congr rfl h1]
          push_cast [M_B]; rfl
        rw [hsum1, one_div_mul_cancel (by positivity), sub_self, abs_zero]
        positivity
      · simp only [hev, ↓reduceIte, sub_zero]
        push_neg at hev
        rcases hev with ⟨p₀, hp₀⟩
        have hM_cast : (M_B : ℝ) = ∏ p ∈ P_B, ((p ^ (2 * r + 1) : ℕ) : ℝ) := by
          push_cast [M_B]; rfl
        rw [hM_cast, one_div, abs_mul, abs_of_pos (by positivity), abs_prod, ← Finset.prod_div_distrib]
        have hle_prod : ∏ p ∈ P_B,
            |∑ n ∈ Finset.range (p ^ (2 * r + 1)), (truncParitySign p r n) ^ (c p)| /
              ((p ^ (2 * r + 1) : ℕ) : ℝ) ≤
            ∏ p ∈ P_B, (if p = p₀.1 then (1 / 3 : ℝ) ^ r else 1) := by
          refine Finset.prod_le_prod (fun _ _ => by positivity) fun p hp => ?_
          have hp_pr := hP_B_pr p hp
          have havg := truncParitySign_pow_avg hp_pr.1 hp_pr.2 r (c p)
          by_cases hpp : p = p₀.1
          · subst hpp
            have hc_odd : ¬ Even (c p₀.1) := by simpa [c, p₀.2] using hp₀
            simp only [hc_odd, ↓reduceIte] at havg ⊢
            rw [div_le_iff₀ (by positivity)]
            calc |∑ n ∈ Finset.range (p₀.1 ^ (2 * r + 1)), (truncParitySign p₀.1 r n) ^ (c p₀.1)|
                ≤ (p₀.1 : ℝ) ^ (r + 1) := havg
              _ = (1 / (p₀.1 : ℝ)) ^ r * (p₀.1 : ℝ) ^ (2 * r + 1) := by
                  rw [one_div, inv_pow]; field_simp; ring
              _ ≤ (1 / 3 : ℝ) ^ r * ((p₀.1 ^ (2 * r + 1) : ℕ) : ℝ) := by
                  push_cast
                  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ r) (by positivity)
                  rw [one_div_le_one_div (by exact_mod_cast hp_pr.1.pos) (by norm_num)]
                  exact_mod_cast hp_pr.2
          · simp only [hpp, ↓reduceIte]
            rw [div_le_one (by positivity)]
            refine le_trans havg ?_
            split_ifs
            · push_cast; rfl
            · push_cast
              exact pow_le_pow_right₀ (by exact_mod_cast hp_pr.1.one_lt.le) (by omega)
        refine le_trans hle_prod ?_
        rw [Finset.prod_ite_eq', if_pos p₀.2]
    refine le_trans (Finset.sum_le_sum fun g _ => hterm_bd g) ?_
    rw [← Finset.mul_sum]
    have hsum_A : ∑ g : Fin (2 * m) → P_B,
        ∏ i : Fin (2 * m), (Real.log (g i : ℕ) / (((g i : ℕ) : ℝ) - 1)) = A_B ^ (2 * m) := by
      rw [← Finset.sum_pow' (Finset.univ : Finset P_B)
        (fun p => Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) (2 * m)]
      have hpi : (Fintype.piFinset fun _ : Fin (2 * m) => (Finset.univ : Finset P_B)) = Finset.univ := by
        ext g; simp
      rw [hpi, Finset.sum_coe_sort P_B (fun p => Real.log (p : ℝ) / ((p : ℝ) - 1))]
      rfl
    rw [hsum_A, mul_comm]
    exact le_of_lt (by simpa [Real.dist_eq, abs_of_nonneg (mul_nonneg (pow_nonneg hA_B_nn _) (by positivity))] using hr₀ r hr)
  have hN_lim : Tendsto (fun N : ℕ =>
      (2 * (M_B : ℝ) * A_B ^ (2 * m)) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N₀_raw, hN₀_raw⟩ := Metric.tendsto_atTop.mp hN_lim (ε / 4) (by positivity)
  refine ⟨max N₀_raw 1, fun N hN => ?_⟩
  have hN_pos : 0 < N := lt_of_lt_of_le (by omega) hN
  have h_err_N : |((1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (SigmaParityTrunc r n B) ^ (2 * m)) -
      (1 / (M_B : ℝ)) * ∑ n ∈ Finset.range M_B, (SigmaParityTrunc r n B) ^ (2 * m)| ≤ ε / 4 := by
    have hper : ∀ n : ℕ, (SigmaParityTrunc r (n + M_B) B) ^ (2 * m) = (SigmaParityTrunc r n B) ^ (2 * m) := by
      intro n
      congr 1
      unfold SigmaParityTrunc
      refine Finset.sum_congr rfl fun p hp => ?_
      have hdvd : p ^ (2 * r + 1) ∣ M_B := Finset.dvd_prod_of_mem _ hp
      rcases hdvd with ⟨t, ht⟩
      rw [ht, mul_comm (p ^ (2 * r + 1)) t, truncParitySign_periodic (hP_B_pr p hp).1.pos]
    have hper_k : ∀ k n : ℕ, (SigmaParityTrunc r (n + k * M_B) B) ^ (2 * m) =
        (SigmaParityTrunc r n B) ^ (2 * m) := by
      intro k n
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.succ_mul, ← add_assoc, hper, ih]
    have hbd_val : ∀ n : ℕ, |(SigmaParityTrunc r n B) ^ (2 * m)| ≤ A_B ^ (2 * m) := by
      intro n
      rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      unfold SigmaParityTrunc
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p hp => ?_)
      rw [abs_mul, abs_truncParitySign, one_mul, abs_of_nonneg]
      have hp3 : 3 ≤ p := (hP_B_pr p hp).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))) (by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3; linarith)
    set Q := N / M_B
    set R := N % M_B
    have hN_eq : N = Q * M_B + R := (Nat.div_add_mod N M_B).symm
    let f : ℕ → ℝ := fun n => (SigmaParityTrunc r n B) ^ (2 * m)
    have hf_range_QM : ∑ n ∈ Finset.range (Q * M_B), f n =
        (Q : ℝ) * ∑ n ∈ Finset.range M_B, f n := by
      induction Q with
      | zero => simp
      | succ q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add]
        have hshift : ∑ n ∈ Finset.range M_B, f (q * M_B + n) = ∑ n ∈ Finset.range M_B, f n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [add_comm]; exact hper_k q n
        rw [ih, hshift]; push_cast; ring
    have hdiff_Icc : ∑ n ∈ Finset.Icc 1 N, f n =
        ∑ n ∈ Finset.range (Q * M_B), f n - f 0 + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n) := by
      have h1 : ∑ n ∈ Finset.range (N + 1), f n = f 0 + ∑ n ∈ Finset.Icc 1 N, f n := by
        rw [Finset.range_eq_Ico, ← Finset.Ico_insert_succ_left (by omega : 0 ≤ N),
          Finset.sum_insert (by simp), Nat.Ico_succ_right_eq_Icc]
      have h2 : ∑ n ∈ Finset.range (N + 1), f n =
          ∑ n ∈ Finset.range (Q * M_B), f n + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n) := by
        rw [show N + 1 = Q * M_B + (R + 1) by omega, Finset.sum_range_add]
      linarith
    have hS_avg_bd : |∑ n ∈ Finset.range M_B, f n| ≤ (M_B : ℝ) * A_B ^ (2 * m) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ n ∈ Finset.range M_B, |f n| ≤ ∑ _n ∈ Finset.range M_B, A_B ^ (2 * m) :=
            Finset.sum_le_sum fun n _ => hbd_val n
        _ = (M_B : ℝ) * A_B ^ (2 * m) := by simp
    have hR_bd : |∑ n ∈ Finset.range (R + 1), f (Q * M_B + n)| ≤ ((R + 1 : ℕ) : ℝ) * A_B ^ (2 * m) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ n ∈ Finset.range (R + 1), |f (Q * M_B + n)| ≤
            ∑ _n ∈ Finset.range (R + 1), A_B ^ (2 * m) := Finset.sum_le_sum fun n _ => hbd_val _
        _ = ((R + 1 : ℕ) : ℝ) * A_B ^ (2 * m) := by simp
    have hQM_diff : (1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, f n -
        (1 / (M_B : ℝ)) * ∑ n ∈ Finset.range M_B, f n =
        (1 / (N : ℝ)) * (-f 0 + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n)) -
        ((R : ℝ) / ((N : ℝ) * (M_B : ℝ))) * ∑ n ∈ Finset.range M_B, f n := by
      rw [hdiff_Icc, hf_range_QM]
      have hN_cast : (N : ℝ) = (Q : ℝ) * (M_B : ℝ) + (R : ℝ) := by exact_mod_cast hN_eq
      field_simp [show (N : ℝ) ≠ 0 by positivity, show (M_B : ℝ) ≠ 0 by positivity]
      rw [hN_cast]; ring
    rw [hQM_diff]
    have hR_lt : (R : ℝ) + 1 ≤ (M_B : ℝ) := by
      exact_mod_cast (Nat.mod_lt N hM_B_pos)
    have h_part1' : |(1 / (N : ℝ)) * (-f 0 + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n))| ≤
        (((M_B : ℝ) + 1) * A_B ^ (2 * m)) / (N : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ)), one_div_mul_eq_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc |-f 0 + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n)|
          ≤ |f 0| + |∑ n ∈ Finset.range (R + 1), f (Q * M_B + n)| := by
            simpa [abs_neg] using abs_add_le (-f 0) (∑ n ∈ Finset.range (R + 1), f (Q * M_B + n))
        _ ≤ A_B ^ (2 * m) + ((R + 1 : ℕ) : ℝ) * A_B ^ (2 * m) := add_le_add (hbd_val 0) hR_bd
        _ = ((R : ℝ) + 2) * A_B ^ (2 * m) := by push_cast; ring
        _ ≤ ((M_B : ℝ) + 1) * A_B ^ (2 * m) :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hA_B_nn _)
    have h_part2 : |((R : ℝ) / ((N : ℝ) * (M_B : ℝ))) * ∑ n ∈ Finset.range M_B, f n| ≤
        (((M_B : ℝ) - 1) * A_B ^ (2 * m)) / (N : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (R : ℝ) / ((N : ℝ) * (M_B : ℝ)))]
      calc (R : ℝ) / ((N : ℝ) * (M_B : ℝ)) * |∑ n ∈ Finset.range M_B, f n|
          ≤ (R : ℝ) / ((N : ℝ) * (M_B : ℝ)) * ((M_B : ℝ) * A_B ^ (2 * m)) :=
            mul_le_mul_of_nonneg_left hS_avg_bd (by positivity)
        _ = ((R : ℝ) * A_B ^ (2 * m)) / (N : ℝ) := by
            field_simp [show (M_B : ℝ) ≠ 0 by positivity]
        _ ≤ (((M_B : ℝ) - 1) * A_B ^ (2 * m)) / (N : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hA_B_nn _))
              (by positivity)
    calc |(1 / (N : ℝ)) * (-f 0 + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n)) -
          ((R : ℝ) / ((N : ℝ) * (M_B : ℝ))) * ∑ n ∈ Finset.range M_B, f n|
        ≤ |(1 / (N : ℝ)) * (-f 0 + ∑ n ∈ Finset.range (R + 1), f (Q * M_B + n))| +
          |((R : ℝ) / ((N : ℝ) * (M_B : ℝ))) * ∑ n ∈ Finset.range M_B, f n| := abs_sub _ _
      _ ≤ (((M_B : ℝ) + 1) * A_B ^ (2 * m)) / (N : ℝ) +
          (((M_B : ℝ) - 1) * A_B ^ (2 * m)) / (N : ℝ) := add_le_add h_part1' h_part2
      _ = (2 * (M_B : ℝ) * A_B ^ (2 * m)) / (N : ℝ) := by ring
      _ ≤ ε / 4 := le_of_lt (by simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (2 * (M_B : ℝ) * A_B ^ (2 * m)) / (N : ℝ))] using hN₀_raw N (le_trans (le_max_left _ _) hN))
  linarith [abs_add_le
    ((1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (SigmaParityTrunc r n B) ^ (2 * m) -
      (1 / (M_B : ℝ)) * ∑ n ∈ Finset.range M_B, (SigmaParityTrunc r n B) ^ (2 * m))
    ((1 / (M_B : ℝ)) * ∑ n ∈ Finset.range M_B, (SigmaParityTrunc r n B) ^ (2 * m) -
      rademacherMoment P_B (2 * m)),
    abs_add_le
    ((1 / (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (SigmaParityTrunc r n B) ^ (2 * m) -
      rademacherMoment P_B (2 * m))
    (rademacherMoment P_B (2 * m) - ∫ x : ℝ, x ^ (2 * m) * ρ x)]

end BrocardFormalization

/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParity
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.ClassGroup.Basic

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

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-- For any `n ≥ 3, n ≠ 6`, `q_n` is not a square (it has a prime divisor `p ≡ 3 (mod 4)`). -/
lemma qn_not_isSquare {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) : ¬ IsSquare (qn n : ℤ) := by
  sorry

lemma qn_rat_not_isSquare {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) : ¬ IsSquare (qn n : ℚ) := by
  sorry

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

/-- Pell index `k ≥ 1` such that `m + s_n √q_n = ε_n^k` (Equation 1.5). -/
def pellIndex {n m : ℕ} (hn : 4 ≤ n) (hsol : IsBrocardSol n m) : ℕ :=
  have hn6 : n ≠ 6 := by
    intro h
    subst h
    obtain ⟨_, _, hm⟩ := hsol
    have hlt : 26 ^ 2 < 721 := by norm_num
    have hgt : 721 < 27 ^ 2 := by norm_num
    have hm1 : Nat.factorial 6 + 1 = 721 := by decide
    have hm2 : m ^ 2 = 721 := hm.symm.trans hm1
    rcases le_or_gt m 26 with hle | hge
    · have : m ^ 2 ≤ 26 ^ 2 := by nlinarith
      omega
    · have : 27 ^ 2 ≤ m ^ 2 := by nlinarith
      omega
  Classical.choose (show ∃ k : ℕ, 1 ≤ k ∧
    (m : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).x ∧
    (sn n : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).y by sorry)

theorem pellIndex_spec {n m : ℕ} (hn : 4 ≤ n) (hsol : IsBrocardSol n m) :
    ∃ hn6 : n ≠ 6,
      let k := pellIndex hn hsol
      1 ≤ k ∧
      (m : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).x ∧
      (sn n : ℤ) = ((pellFundUnit n (by omega) hn6) ^ (k : ℤ)).y := by
  sorry

theorem lemma_3_1_i (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    (∃ p : ℕ, p.Prime ∧ p ∣ qn n ∧ p % 4 = 3) ∧
    (∀ x y : ℤ, x ^ 2 - (qn n : ℤ) * y ^ 2 ≠ -1) ∧
    (let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare hn hn6⟩
      ∃ dn : ℕ, (dn = 1 ∨ dn = 3) ∧ ((qn n : ℤ) % 8 ≠ 5 → dn = 1)) ∧
    ((116 ≤ n ∨ (8 ≤ n ∧ n ≤ 115 ∧ n ≠ 10)) → Real.log (qn n) > 0.4 * n) ∧
    (8 ≤ n → Real.log (epsReal n hn hn6) > 0.2 * n) ∧
    (∀ (h8 : 8 ≤ n) (m : ℕ) (hsol : IsBrocardSol n m),
      let k := pellIndex (by omega) hsol
      1 ≤ k ∧ (k : ℝ) < 2.5 * Real.log n ∧ (116 ≤ n → 2.5 * Real.log n < (n : ℝ) / 5)) := by
  sorry

theorem lemma_3_1_ii :
    IsBigOAtTop
      (fun n => Real.log ((sn n : ℝ) * Real.sqrt (qn n)) -
        ((1 / 2 : ℝ) * n * Real.log n - (1 / 2 : ℝ) * n + (1 / 4 : ℝ) * Real.log (2 * Real.pi * n)))
      (fun n => (n : ℝ)⁻¹) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧
      IsBigOAtTop
        (fun n => Real.log (sn n) - ((1 / 2 : ℝ) * n * Real.log n - ((1 + Real.log 2) / 2) * n))
        (fun n => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log n)))) := by
  sorry

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
      padicValInt p ((Polynomial.Chebyshev.U ℤ (k - 1)).eval (X1 n hn hn6 : ℤ)) = padicValNat p k) ∧
    (∀ (hn4 : 4 ≤ n) (m : ℕ) (hsol : IsBrocardSol n m), k = pellIndex hn4 hsol →
      ∀ p ∈ Podd n,
        padicValNat p (qn n * (Y1 n hn hn6) ^ 2) = padicValNat p n.factorial - 2 * padicValNat p k) := by
  sorry

/-- Projective rank of apparition `α_p(q_n) := min {r ≥ 1 : p ∣ Y_r(q_n)}`. -/
def alphaRank (n p : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℕ :=
  open Classical in
  Nat.find (show ∃ r : ℕ, 1 ≤ r ∧ p ∣ Yr n hn hn6 r by sorry)

theorem lemma_3_2_ii (n p : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hp_ndvd : ¬ p ∣ qn n) :
    let α := alphaRank n p hn hn6
    1 ≤ α ∧
    ((α : ℤ) ∣ ((p : ℤ) - jacobiSym (qn n : ℤ) p) / 2) ∧
    (∀ k : ℕ, 1 ≤ k →
      (p ∣ Yr n hn hn6 k ↔ α ∣ k) ∧
      (α ∣ k → padicValNat p (Yr n hn hn6 k) = padicValNat p (Yr n hn hn6 α) + padicValNat p (k / α))) := by
  sorry

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
    (∀ n₁ n₂ m₁ m₂ : ℕ, 4 ≤ n₁ → n₁ < n₂ →
      IsBrocardSol n₁ m₁ → IsBrocardSol n₂ m₂ → qn n₁ ≠ qn n₂) := by
  sorry

theorem remark_3_3 :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn8 : 8 ≤ n) → (hN : N₀ ≤ n) → (hsol : IsBrocardSol n m) →
      ∀ ell : ℕ, ell.Prime → 3 ≤ ell → ¬ ell ∣ pellIndex (by omega) hsol := by
  sorry

theorem prop_3_4 (n m : ℕ) (hn : 8 ≤ n) (hsol : IsBrocardSol n m)
    (hk : pellIndex (by omega) hsol = 1 ∨ pellIndex (by omega) hsol = 2)
    (hn6 : n ≠ 6) (p : ℕ) (hp : p.Prime)
    (hp_lo : (n : ℝ) / 3 < (p : ℝ)) (hp_hi : (p : ℝ) ≤ (n : ℝ) / 2) :
    ¬ p ∣ qn n ∧ padicValNat p (sn n) = 1 ∧
    let α := alphaRank n p (by omega) hn6
    (α ∣ pellIndex (by omega) hsol) ∧ (α = 1 ∨ α = 2) ∧
    padicValNat p (Yr n (by omega) hn6 α) = 1 := by
  sorry

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
  sorry

/-- Fermat quotient `q_p(a) = (a^{p-1} - 1) / p mod p`. -/
def fermatQuot (p : ℕ) (a : ℤ) : ZMod p :=
  (((a ^ (p - 1) - 1) / (p : ℤ) : ℤ) : ZMod p)

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
      let _ : Fact (¬ IsSquare (-(3 * (qn n : ℚ)))) := by sorry
      let chi_neg3D_3 : ℤ := jacobiSym (-3 * fundDiscrQuad (qn n : ℤ)) 3
      (3 : ℤ) ∣ (1 - chi_neg3D_3) *
        (NumberField.classNumber (QuadField (-(3 * (qn n : ℚ)))) : ℤ)) := by
  sorry

theorem theorem_3_6 (n m : ℕ) (hn : 4 ≤ n) (hsol : IsBrocardSol n m)
    (hn6 : n ≠ 6) :
    let k := pellIndex hn hsol
    (k = 2 ↔ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
      (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v|) ∧
    (k = 1 ↔ (∃ δ₂ z₂ z₁ : ℕ, Squarefree δ₂ ∧ (m + 1) / 2 = δ₂ * z₂ ^ 2 ∧
      (m - 1) / 2 = (qn n / δ₂) * z₁ ^ 2 ∧
      ¬ ∃ u v : ℤ, u ^ 2 - (qn n : ℤ) * v ^ 2 = 1 ∧
        (m : ℤ) = u ^ 2 + (qn n : ℤ) * v ^ 2 ∧ (sn n : ℤ) = 2 * |u * v|)) ∧
    (k = 2 →
      let _ : Fact (¬ IsSquare (-(qn n : ℚ))) := by sorry
      2 ∣ NumberField.classNumber (QuadField (-(qn n : ℚ)))) := by
  sorry

end BrocardFormalization

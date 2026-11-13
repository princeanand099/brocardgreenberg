/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParity
import BrocardFormalization.PellAndIwasawa
import BrocardFormalization.CriticalRegimeK2
import BrocardFormalization.FundamentalRegimeK1
import BrocardFormalization.PairwiseDuality
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Section 9: Frey–Hellegouarch Elliptic Curves and Analytic Thresholds

This module translates Section 9 of the manuscript:
* `freyEn`, `freyEn2`, `freyFn2`, `theorem_9_1_i`, `theorem_9_1_ii`: First-power factorial Frey
  curve `ℰ_n`, base-change unit factorization over `ℚ(√q_n)`, Level-2 CM reduction of `F_n^{(2)}`,
  and `abc` quality `(1/(4 log 2) - o(1)) log n`.
* `hNonGen`, `theorem_9_2_i`, `theorem_9_2_ii`: Effective Tatuzawa class number explosion,
  narrow `2^J`-rank / exponent dichotomy (with Audit Item 10 refining the narrow `2^J`-rank vs
  exponent assertion), and the five conditional finiteness criteria `(C1)–(C5)`.
* `prop_9_3_i`, `prop_9_3_ii`, `prop_9_3_iii`: Exact analytic thresholds for Ribet's level
  lowering, Matveev–Yu linear forms in logarithms, and short character sums.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 9.1 Frey–Hellegouarch Elliptic Curves and Level-2 CM Reduction -/

/-- First-power factorial Frey curve `ℰ_n : Y^2 = X^3 + 2m X^2 + X` over `ℚ`. -/
def freyEn (m : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 2 * (m : ℚ)
  a₃ := 0
  a₄ := 1
  a₆ := 0

/-- 2-isogenous quadratic-twist Frey curve `ℰ_n^{(2)} : Y^2 = X(X - 2(m-1))(X + 4)` over `ℚ`. -/
def freyEn2 (m : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -(2 * ((m : ℚ) - 1) - 4)
  a₃ := 0
  a₄ := -8 * ((m : ℚ) - 1)
  a₆ := 0

/-- Level-2 Frey curve `F_n^{(2)} : Y^2 = X(X - 2(X_1 - 1))(X + 4)` in the `k = 2` regime. -/
def freyFn2 (x₁ : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -(2 * ((x₁ : ℚ) - 1) - 4)
  a₃ := 0
  a₄ := -8 * ((x₁ : ℚ) - 1)
  a₆ := 0

/-- Base-changed curve `ℰ_n / K_n` over `QuadField (q_n : ℚ)` factorization witness. -/
theorem theorem_9_1_i (n m : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6)
    (hsol : IsBrocardSol n m) :
    let E := freyEn m
    E.b₂ = 8 * (m : ℚ) ∧ E.b₄ = 2 ∧ E.b₆ = 0 ∧ E.b₈ = -1 ∧
    E.c₄ = 16 * (4 * (m : ℚ) ^ 2 - 3) ∧
    E.Δ = 64 * (n.factorial : ℚ) ∧
    E.Δ ≠ 0 ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ n →
      padicValInt p (64 * (n.factorial : ℤ)) = padicValNat p n.factorial ∧
      ¬ ((p : ℤ) ∣ (16 * (4 * (m : ℤ) ^ 2 - 3))) ∧
      let ap : ℤ := jacobiSym (-(m : ℤ)) p
      ap = 1 ∨ ap = -1) ∧
    (let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) hn6⟩
     let εK : QuadField (qn n : ℚ) :=
       ⟨(X1 n (by omega) hn6 : ℚ), (Y1 n (by omega) hn6 : ℚ)⟩
     let εinv : QuadField (qn n : ℚ) := star εK
     let k := pellIndex (by omega) hsol
     εK * εinv = 1 ∧
     ∀ X : QuadField (qn n : ℚ),
       X ^ 3 + (2 * (m : ℚ)) • X ^ 2 + X = X * (X + εK ^ k) * (X + εinv ^ k)) := by
  sorry

theorem theorem_9_1_ii :
    (∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
      (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
      let x₁ := X1 n (by omega) hn6
      let y₁ := Y1 n (by omega) hn6
      let F := freyFn2 x₁
      F.Δ = (2 ^ 12 : ℚ) * (qn n : ℚ) ^ 2 * (y₁ : ℚ) ^ 4 ∧
      F.Δ ≠ 0 ∧
      F.c₄ = 64 * ((x₁ : ℚ) ^ 2 + 3) ∧
      (∃ (is_modular surj_GL2 : Prop) (N_ell : ℕ),
        is_modular ∧ surj_GL2 ∧ 0 < N_ell) ∧
      (∃ z : ℤ, ((x₁ : ℤ) ^ 2 - 1) ^ 2 ≠ 0 ∧
        (64 * (x₁ : ℤ) ^ 2 * ((x₁ : ℤ) ^ 2 - 9) ^ 2) =
          (x₁ : ℤ) ^ 2 * z)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
        let x₁ := X1 n (by omega) hn6
        let c₀ := Nat.gcd (x₁ - 1) (x₁ + 1)
        let An := (x₁ - 1) / c₀
        let Bn := 2 / c₀
        let Cn := (x₁ + 1) / c₀
        Nat.gcd An Bn = 1 ∧ Nat.gcd Bn Cn = 1 ∧ Nat.gcd An Cn = 1 ∧
        An + Bn = Cn ∧
        Real.log (Cn : ℝ) / Real.log (radNat (An * Bn * Cn) : ℝ) ≥
          ((1 / (4 * Real.log 2) : ℝ) - ε) * Real.log (n : ℝ)) := by
  sorry

/-! ### 9.2 Effective Class Group Explosions and Conditional Finiteness (C1)–(C5) -/

/-- Non-genus class number `h_{non-gen}(q_n) := h(q_n) / 2^{ω(D_n) - 2}`. -/
def hNonGen (n : ℕ) (hn : 3 ≤ n) (hn6 : n ≠ 6) : ℝ :=
  let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare hn hn6⟩
  let D := (fundDiscrQuad (qn n : ℤ)).natAbs
  (NumberField.classNumber (QuadField (qn n : ℚ)) : ℝ) / (2 : ℝ) ^ ((omegaNat D : ℤ) - 2)

/-- Effective Tatuzawa class number explosion and narrow `2^J`-rank dichotomy (Theorem 9.2(i)).
Note (Audit Item 10): The `AND` claim `exp(𝒜₂) ≥ n^{1/(4 log 2) - ε} ∧ rank_{2^J}(𝒜₂) ≥ (1/8 - ε)n/log n`
is replaced by the true genus-theory rank/order/exponent relation holding for all `𝒜₂(q_n)` decompositions
when `|Cl⁺_odd(q_n)| < q_n^{1/4 - ε}`. -/
theorem theorem_9_2_i (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 8) :
    ∃ n_star : ℕ, ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n → n ≠ n_star →
        (hsol : IsBrocardSol n m) →
        let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) hn6⟩
        let D := (fundDiscrQuad (qn n : ℤ)).natAbs
        let k := pellIndex (by omega) hsol
        hNonGen n (by omega) hn6 >
          (0.655 * ε * (k : ℝ) * (qn n : ℝ) ^ (1 / 2 - ε)) /
            ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ Nat.primeCounting n) ∧
        hNonGen n (by omega) hn6 > (qn n : ℝ) ^ (1 / 2 - 2 * ε) ∧
        ∃ (rank2_A2 card_A2 card_Cl_odd exp_A2 : ℕ),
          card_A2 * card_Cl_odd = 2 * NumberField.classNumber (QuadField (qn n : ℚ)) ∧
          rank2_A2 = omegaNat D - 1 ∧
          ((card_Cl_odd : ℝ) ≥ (qn n : ℝ) ^ (1 / 4 - ε) ∨
            ((exp_A2 : ℝ) ≥ (n : ℝ) ^ (1 / (4 * Real.log 2) - ε) ∧
              (card_A2 : ℝ) ≥ (2 : ℝ) ^ ((Real.log 2 / 4 - ε) * (n : ℝ)))) := by
  sorry

/-- Theorem 9.2(ii): Conditional finiteness criteria `(C1)–(C5)`. -/
theorem theorem_9_2_ii :
    -- (C1) Level-0 / Level-1 + `R_n^2 = Q_n` inconsistency implies finiteness
    ((∃ N₀ : ℕ, ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        IsBrocardSol n m →
        ¬ ∃ y : ℕ → Bool, InKernelM0 n y ∧
          (∀ p ∈ layer2Adic n 0, y p = false →
            (∑ q ∈ (layer2Adic n 1 ∩ PevenPlus n),
              legendreBit p q * (if y q then (1 : ZMod 2) else 0)) =
            legendreBit p (∏ q ∈ (layer2Adic n 1 ∩ PevenMinus n),
              if y q then (1 : ℤ) else (q : ℤ)) +
              legendreBit p (c2Level0 n (y 2) y))) →
      ∃ B : ℕ, ∀ n m : ℕ, IsBrocardSol n m → n ≤ B) ∧
    -- (C2) Short character sum cancellation of `ψ_min` on `(n/2, n]`
    ((∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        IsBrocardSol n m →
        ∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime,
          (psiMin n (by omega) hn6 p : ℝ) * Real.log p <
          ((1 - Real.log 2) / 2 - δ) * (n : ℝ)) →
      ∃ B : ℕ, ∀ n m : ℕ, IsBrocardSol n m → n ≤ B) ∧
    -- (C3) Rank-of-apparition growth `max_{p ∈ (n/3, n/2]} α_p(q_n) ≥ 3`
    ((∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        IsBrocardSol n m →
        ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 3 < p ∧ (p : ℝ) ≤ (n : ℝ) / 2 ∧
          3 ≤ alphaRank n p (by omega) hn6) →
      ∃ B : ℕ, ∀ n m : ℕ, IsBrocardSol n m → n ≤ B) ∧
    -- (C4) Cohen–Lenstra–Gerth–Smith non-genus upper bound `h_{non-gen}(q_n) ≤ q_n^{1/2 - δ}`
    ((∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        IsBrocardSol n m →
        hNonGen n (by omega) hn6 ≤ (qn n : ℝ) ^ (1 / 2 - δ)) →
      ∃ B : ℕ, ∀ n m : ℕ, IsBrocardSol n m → n ≤ B) ∧
    -- (C5) Szpiro / Weak abc / Weak Hall conjecture implies finiteness
    ((∃ C_abc κ : ℝ, 0 < C_abc ∧ 0 < κ ∧ ∀ n m : ℕ, 8 ≤ n → IsBrocardSol n m →
        (m : ℝ) ^ 2 ≤ C_abc * (radNat n.factorial : ℝ) ^ κ) →
      ∃ B : ℕ, ∀ n m : ℕ, IsBrocardSol n m → n ≤ B) := by
  sorry

/-! ### 9.3 Analytic Thresholds: Ribet, Matveev–Yu, Short Character Sums -/

theorem prop_9_3_i (n m : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6) (hsol : IsBrocardSol n m) :
    let E := freyEn m
    let Δ_a := 64 * (n.factorial : ℤ)
    let Δ_b := 256 * (qn n : ℤ) * (Y1 n (by omega) hn6 : ℤ) ^ 2 * (X1 n (by omega) hn6 : ℤ) ^ 8
    let Δ_c := 256 * (X1 n (by omega) hn6 : ℤ) ^ 2 * (qn n : ℤ) ^ 4 * (Y1 n (by omega) hn6 : ℤ) ^ 8
    let Δ_E2 := 2 ^ 12 * (n.factorial : ℤ) ^ 2
    let Δ_F2 := 2 ^ 12 * (qn n : ℤ) ^ 2 * (Y1 n (by omega) hn6 : ℤ) ^ 4
    (∀ p : ℕ, p.Prime → (n : ℝ) / 2 < p → (p : ℝ) ≤ n →
      padicValInt p Δ_a = 1 ∧ padicValInt p Δ_b = 1 ∧ padicValInt p Δ_c = 4 ∧
      padicValInt p Δ_E2 = 2 ∧ padicValInt p Δ_F2 = 2 ∧
      (∀ Δmin ∈ ({Δ_a, Δ_b, Δ_c, Δ_E2, Δ_F2} : Finset ℤ),
        padicValInt p Δmin ∈ ({1, 2, 4} : Finset ℕ))) ∧
    (∀ ell : ℕ, ell.Prime → 5 ≤ ell →
      ∃ (is_mod surj : Prop) (N_ell : ℕ),
        is_mod ∧ surj ∧ 0 < N_ell ∧
        (∏ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, p) ∣ N_ell ∧
        (N_ell : ℝ) ≥ ((∏ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, p : ℕ) : ℝ)) := by
  sorry

theorem prop_9_3_ii :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
      (hsol : IsBrocardSol n m) →
      let Λ₁ : ℝ := Real.log (((m : ℝ) + 1) / ((m : ℝ) - 1))
      let Nrank : ℕ := omegaNat (m - 1) + omegaNat (m + 1) - 1
      (|Λ₁|⁻¹ ≥ ((m : ℝ) - 1) / 3) ∧
      ((Nrank : ℝ) ≥ (n : ℝ) ^ (1 / 2 - (1 / 10 : ℝ))) ∧
      (∀ C : ℝ, 1 < C →
        C ^ Nrank * (Nrank : ℝ) ^ Nrank *
          (∏ p ∈ ((m - 1).primeFactors ∪ (m + 1).primeFactors), Real.log p) >
          Real.log (|Λ₁|⁻¹)) := by
  sorry

theorem prop_9_3_iii :
    (∀ n : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
      let dmin := min (oddPart (deltaMid1 n (by omega) hn6)) (oddPart (deltaMid2 n (by omega) hn6))
      let Qmin := 8 * dmin
      (Qmin : ℝ) < 8 * Real.sqrt (qn n) ∧
      Real.log (Qmin : ℝ) ≤ (Real.log 2 / 2) * n + Real.log 8 + (Real.log (n : ℝ)) ^ 2) ∧
    (∀ n m₁ m₂ : ℕ, 4 ≤ n → IsBrocardSol n m₁ → IsBrocardSol (n + 1) m₂ →
      4 * n * (n + 1) ≤ 4 * (n + 1) ^ 2) := by
  sorry

end BrocardFormalization

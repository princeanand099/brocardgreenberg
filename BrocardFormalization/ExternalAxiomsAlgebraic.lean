/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

noncomputable section

open scoped BigOperators
open Filter Topology

namespace BrocardFormalization.External

axiom iwasawa_kubota_leopoldt_package :
    ∀ (q p : ℕ) (_hp : p.Prime) (_hp5 : 5 ≤ p) (_hq : Squarefree q) (_hq1 : 1 < q)
      (_hp_unram : ¬ p ∣ q) [Fact (¬ IsSquare (q : ℚ))],
    ∃ (vp_Rtilde vp_Lp1 : ℤ) (lamP muP : ℕ),
      (∀ (ε₁ : Pell.Solution₁ (q : ℤ)), Pell.IsFundamental ε₁ →
        ∀ (k m s dn : ℕ), (dn = 1 ∨ dn = 3) → ¬ p ∣ dn * k →
          (m : ℤ) ^ 2 = (q : ℤ) * (s : ℤ) ^ 2 + 1 →
          (m : ℤ) = (ε₁ ^ (k : ℤ)).x → (s : ℤ) = (ε₁ ^ (k : ℤ)).y →
          1 ≤ padicValNat p s →
          vp_Rtilde = (padicValNat p s : ℤ)) ∧
      (vp_Lp1 = (padicValNat p (NumberField.classNumber (QuadField (q : ℚ))) : ℤ) +
        vp_Rtilde - 1) ∧
      (muP = 0) ∧
      (1 ≤ vp_Lp1 → 1 ≤ lamP)

axiom sinnott_and_kummer_congruence :
    ∀ (q : ℕ) (_hq : Squarefree q) (_hq1 : 1 < q) (_h3 : ¬ 3 ∣ q)
      [Fact (¬ IsSquare (-(3 * (q : ℚ))))]
      (ε₁ : Pell.Solution₁ (q : ℤ)), Pell.IsFundamental ε₁ →
      ∀ (k m s dn : ℕ), (dn = 1 ∨ dn = 3) →
        (m : ℤ) ^ 2 = (q : ℤ) * (s : ℤ) ^ 2 + 1 →
        (m : ℤ) = (ε₁ ^ (k : ℤ)).x → (s : ℤ) = (ε₁ ^ (k : ℤ)).y →
        2 ≤ (padicValNat 3 s : ℤ) - (padicValNat 3 (dn * k) : ℤ) →
        let chi_neg3D_3 : ℤ := jacobiSym (-3 * fundDiscrQuad (q : ℤ)) 3
        (3 : ℤ) ∣ (1 - chi_neg3D_3) *
          (NumberField.classNumber (QuadField (-(3 * (q : ℚ)))) : ℤ)

axiom tatuzawa_effective_siegel :
    ∀ (ε : ℝ), 0 < ε → ε < 1 / 8 →
    ∃ D_star : ℕ, ∀ (q : ℕ) (_hq : Squarefree q) (_hq1 : 1 < q)
      [Fact (¬ IsSquare (q : ℚ))],
      let D : ℕ := (fundDiscrQuad (q : ℤ)).natAbs
      D ≠ D_star →
      ∃ L1 : ℝ, L1 > 0.655 * ε * (D : ℝ) ^ (-ε) ∧
        (NumberField.classNumber (QuadField (q : ℚ)) : ℝ) *
          NumberField.Units.regulator (QuadField (q : ℚ)) =
          (1 / 2 : ℝ) * Real.sqrt D * L1

axiom hasse_gauss_redei_reichardt :
    ∀ (q : ℕ) (_hq : Squarefree q) (_hq1 : 1 < q) [Fact (¬ IsSquare (q : ℚ))],
      let D : ℕ := (fundDiscrQuad (q : ℤ)).natAbs
      ∃ (rank4_Cl_plus rank2_A2 card_A2 card_Cl_odd : ℕ) (exp_A2 : ℕ),
        card_A2 * card_Cl_odd = 2 * NumberField.classNumber (QuadField (q : ℚ)) ∧
        rank2_A2 = omegaNat D - 1 ∧
        2 ^ rank2_A2 ≤ card_A2 ∧
        card_A2 ≤ exp_A2 ^ rank2_A2 ∧
        rank4_Cl_plus ≤ rank2_A2

axiom siegel_differential_wronskian_lemma :
    ∀ (s : ℕ) (_hs : 1 ≤ s) (T : Polynomial ℚ) (P TA : Fin s → Polynomial ℚ)
      (ω : Fin s → PowerSeries ℂ),
      T ≠ 0 → (∀ a, P a ≠ 0) →
      (∀ a, PowerSeries.derivative (ω a) * (Polynomial.map (algebraMap ℚ ℂ) T : PowerSeries ℂ) =
        (Polynomial.map (algebraMap ℚ ℂ) (TA a) : PowerSeries ℂ) * ω a) →
      (∀ c : Fin s → Polynomial ℂ,
        (∑ a : Fin s, (c a : PowerSeries ℂ) * ω a = 0) → ∀ a, c a = 0) →
      let M : Matrix (Fin s) (Fin s) (Polynomial ℚ) :=
        Matrix.of fun k a =>
          Nat.iterate (fun Q => T * Q.derivative + (TA a) * Q) k.1 (P a)
      M.det ≠ 0

axiom grunwald_wang_chebotarev_inert_prime :
    ∀ (A : ℤ) (k : ℕ), A ≠ 0 → 2 ≤ k →
      (¬ ∃ c : ℤ, A = c ^ k) →
      (8 ∣ k → ¬ ∃ c : ℤ, A = 2 ^ (k / 2) * c ^ k) →
      ∃ p₀ : ℕ, p₀.Prime ∧ ¬ ((p₀ : ℤ) ∣ (k : ℤ) * A) ∧
        ∀ x : ZMod p₀, x ^ k ≠ (A : ZMod p₀)

axiom berend_harmse_irreducible_factor :
    ∀ (P : Polynomial ℤ), (∃ Q : Polynomial ℚ, Irreducible Q ∧ 2 ≤ Q.natDegree ∧
      Q ∣ P.map (Int.castRingHom ℚ)) →
      ∃ N₀ : ℕ, ∀ n : ℕ, ∀ x : ℤ, (n.factorial : ℤ) = P.eval x → n ≤ N₀

axiom modularity_serre_ribet_package :
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
      (∃ p₀ : ℕ, p₀.Prime ∧ padicValRat p₀ E.j < 0) →
      (∃ e₁ e₂ e₃ : ℚ, e₁ ≠ e₂ ∧ e₂ ≠ e₃ ∧ e₁ ≠ e₃ ∧
        E.a₁ = 0 ∧ E.a₃ = 0 ∧
        E.a₂ = -(e₁ + e₂ + e₃) ∧ E.a₄ = e₁ * e₂ + e₂ * e₃ + e₃ * e₁ ∧ E.a₆ = -(e₁ * e₂ * e₃)) →
      ∀ (ell : ℕ), ell.Prime → 5 ≤ ell →
      ∃ (is_modular surj_GL2 : Prop) (N_ell : ℕ),
        is_modular ∧ surj_GL2 ∧ 0 < N_ell ∧
        (∀ p : ℕ, p.Prime →
          (∃ (Δ_min : ℤ), Δ_min ≠ 0 ∧ (E.Δ : ℚ) = (Δ_min : ℚ) ∧
            0 < padicValInt p Δ_min ∧ padicValRat p E.j < 0 ∧
            ¬ ((ell : ℤ) ∣ (padicValInt p Δ_min : ℤ))) →
          p ∣ N_ell)

axiom matveev_yu_linear_forms_bound :
    ∃ C : ℝ, 1 < C ∧
      ∀ (N : ℕ) (p : Fin N → ℕ) (b : Fin N → ℤ) (B : ℝ),
        1 ≤ N → (∀ i, (p i).Prime) → Function.Injective p →
        2 ≤ B → (∀ i, |(b i : ℝ)| ≤ B) →
        let Λ : ℝ := ∑ i : Fin N, (b i : ℝ) * Real.log (p i : ℝ)
        Λ ≠ 0 →
        Real.log |Λ| ≥ -(C ^ N * (N : ℝ) ^ N * (∏ i : Fin N, Real.log (p i : ℝ)) * Real.log B)

end BrocardFormalization.External

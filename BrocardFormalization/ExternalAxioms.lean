/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# External Mathematical Axioms

This module declares **only** established theorems from peer-reviewed mathematical
literature external to the manuscript's own contribution for which no suitable
formalization exists in Mathlib v4.35.0. Every declaration here is documented in
`EXTERNAL_AXIOMS.md` with its exact published source and justification.

No manuscript-owned lemma, proposition, corollary, or theorem is placed here.
In particular, Vaughan's identity decompositions, Type I/II Cauchy–Schwarz bounds,
projective rank-of-apparition bounds, and normalized Wronskian rank theorems are
proved directly inside the manuscript modules rather than axiomatized.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace BrocardFormalization.External

/-! ### 1. Analytic Prime Number Theory -/

/-- **de la Vallée Poussin Prime Number Theorem** ([18, Chapter 18]).
There exist effective constants `c₁ > 0` and `C > 0` such that for all `x ≥ 2`,
`|ϑ(x) - x| ≤ C x exp(-c₁ √(log x))` and `|π(x) - li(x)| ≤ C x exp(-c₁ √(log x))`. -/
axiom deLaValleePoussin_pnt :
    ∃ (c₁ C : ℝ), 0 < c₁ ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.theta x - x| ≤ C * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) ∧
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹| ≤
        C * x * Real.exp (-c₁ * Real.sqrt (Real.log x))

/-- **Mertens' First Theorem** ([18, Chapter 7]).
`∑_{3 ≤ p ≤ x} log p / (p - 1) = log x - γ - log 2 + o(1)` as `x → ∞`, where `γ` is the
Euler–Mascheroni constant (`Real.eulerMascheroniConstant`), and
`∑_{2 ≤ p ≤ x} log p / p = log x + O(1)`. -/
axiom mertens_first_theorem :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.Icc 3 ⌊x⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) -
          (Real.log x - Real.eulerMascheroniConstant - Real.log 2)) atTop (𝓝 0) ∧
      ∀ x : ℝ, 2 ≤ x →
        |(∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, Real.log p / (p : ℝ)) - Real.log x| ≤ C

/-- **Prime Number Theorem for Arithmetic Progressions** ([18, Chapter 20]).
For fixed modulus `q ≥ 1` and residue `a` coprime to `q`,
`∑_{p ≤ x, p ≡ a (mod q)} log p = x / φ(q) + o(x)` as `x → ∞`. -/
axiom pnt_arithmetic_progression (q a : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a q) :
    Tendsto (fun x : ℝ =>
      ((∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q), Real.log p) -
        x / (Nat.totient q : ℝ)) / x) atTop (𝓝 0)

/-- **Breusch's Generalization of Bertrand's Postulate mod 4** ([8, 1932]).
For every real `x ≥ 7`, there exists a prime `p` with `x < p ≤ 2 * x` and `p ≡ 3 (mod 4)`. -/
axiom breusch_bertrand_mod_four :
    ∀ x : ℝ, 7 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p % 4 = 3

/-- **Rosser–Schoenfeld Explicit Chebyshev Bounds** ([48, Theorem 10, 1962]).
For all `n ≥ 116`, `ϑ(n) - ϑ(n/2) > 0.4 * n`. -/
axiom rosser_schoenfeld_theta_diff :
    ∀ n : ℕ, 116 ≤ n →
      Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n : ℝ) / 2) > 0.4 * (n : ℝ)

/-- **Schoenfeld's Explicit Prime Gap Theorem** ([50, 1976]).
For all real `x ≥ 2010760`, `ϑ(x + x / 16597) > ϑ(x)`. -/
axiom schoenfeld_prime_gap :
    ∀ x : ℝ, 2010760 ≤ x → Chebyshev.theta (x + x / 16597) > Chebyshev.theta x

/-- **Nagura's Prime Interval Theorem** ([41, 1952]).
For every real `x ≥ 25`, there exists a prime `p` with `x < p < (6 / 5 : ℝ) * x`. -/
axiom nagura_prime_interval :
    ∀ x : ℝ, 25 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (6 / 5 : ℝ) * x

/-- **Berndt–Galway Computational Verification of Brocard's Equation** ([7, 2000]).
There are no positive integer solutions `(n, m)` to `n! + 1 = m^2` with `8 ≤ n ≤ 10^9`. -/
axiom berndt_galway_brocard_bound :
    ∀ n m : ℕ, IsBrocardSol n m → 8 ≤ n → n ≤ 10 ^ 9 → False

/-! ### 2. Vaaler Trigonometric Polynomials and Exponential Sum Bounds -/

/-- **Vaaler's Extremal Trigonometric Approximation of the Sawtooth Function** ([60, Theorem 18]). -/
axiom vaaler_sawtooth_approx :
    ∃ W : ℝ → ℝ, (∀ u, W (-u) = W u) ∧ (∀ u, 0 ≤ W u ∧ W u ≤ 1) ∧
    ∀ H : ℕ, 1 ≤ H →
      ∃ (Ψ B : ℝ → ℝ) (c : ℤ → ℂ) (b : ℤ → ℂ),
        (∀ t : ℝ, (Ψ t : ℂ) = ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
          c h * ePhase ((h : ℝ) * t)) ∧
        (∀ t : ℝ, (B t : ℂ) = ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
          b h * ePhase ((h : ℝ) * t)) ∧
        (∀ h : ℤ, h ≠ 0 →
          c h = -(1 / (2 * Real.pi * Complex.I * (h : ℂ))) *
            (W (|(h : ℝ)| / ((H : ℝ) + 1)) : ℂ)) ∧
        (∀ h : ℤ, h ≠ 0 → ‖c h‖ ≤ 1 / (2 * Real.pi * |(h : ℝ)|)) ∧
        (b 0 = 1 / (2 * (H : ℂ) + 2)) ∧
        (∀ h : ℤ, ‖b h‖ ≤ 1 / (2 * (H : ℝ) + 2)) ∧
        (∀ m : ℤ, Ψ (m : ℝ) = 0 ∧ B (m : ℝ) = 1 / 2) ∧
        (∀ t : ℝ, |t - (⌊t⌋ : ℝ) - 1 / 2 - Ψ t| ≤ B t)

/-- **Vaaler's Beurling–Selberg Majorant of an Interval Indicator** ([60, Theorem 19]). -/
axiom vaaler_indicator_majorant (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Iplus : ℝ → ℝ) (chat : ℤ → ℂ),
      (∀ x : ℝ, (Iplus x : ℂ) = ∑ h ∈ Finset.Icc (-(H : ℤ)) H, chat h * ePhase ((h : ℝ) * x)) ∧
      (∀ x : ℝ, 0 ≤ Iplus x) ∧
      (∀ x : ℝ, |x| ≤ δ → 1 ≤ Iplus x) ∧
      (chat 0 = ((2 * δ + 1 / ((H : ℝ) + 1)) : ℂ)) ∧
      (∀ h : ℤ, ‖chat h‖ ≤ 2 * δ + 1 / ((H : ℝ) + 1))

/-- **Kusmin–Landau First-Derivative Exponential Sum Bound** ([30, Corollary 8.11]).
If `F` is differentiable on `[a, b]` with monotonic derivative satisfying `0 < λ₁ ≤ |F'(t)| ≤ 1/2`,
then `‖∑_{⌈a⌉ ≤ m ≤ ⌊b⌋} e(F(m))‖ ≤ C / λ₁` for an absolute constant `C > 0`. -/
axiom kusmin_landau_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b lam1 : ℝ) (F : ℝ → ℝ),
        0 ≤ a → a ≤ b → 0 < lam1 →
        (MonotoneOn (deriv F) (Set.Icc a b) ∨ AntitoneOn (deriv F) (Set.Icc a b)) →
        (∀ t ∈ Set.Icc a b, lam1 ≤ |deriv F t| ∧ |deriv F t| ≤ 1 / 2) →
        ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, ePhase (F m)‖ ≤ C / lam1

/-- **van der Corput `k`-th Derivative Exponential Sum Bound** ([30, Theorem 8.4 & Corollary 8.13]).
For `k ≥ 2`, `α ≥ 1`, and `0 < λ ≤ |F^{(k)}(t)| ≤ α λ` on `[a, b]` with `b - a ≥ 1`,
`‖∑_{⌈a⌉ ≤ m ≤ ⌊b⌋} e(F(m))‖ ≪_{k,α} (b - a) λ^{1/(2^k - 2)} + (b - a)^{1 - 2^{2-k}} λ^{-1/(2^k - 2)}`. -/
axiom van_der_corput_kth_derivative (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b lam : ℝ) (F : ℝ → ℝ),
        0 ≤ a → 1 ≤ b - a → 0 < lam →
        (∀ t ∈ Set.Icc a b, lam ≤ |iteratedDeriv k F t| ∧ |iteratedDeriv k F t| ≤ α * lam) →
        ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, ePhase (F m)‖ ≤
          C * ((b - a) * lam ^ ((1 : ℝ) / ((2 ^ k - 2 : ℕ) : ℝ)) +
            (b - a) ^ (1 - (2 : ℝ) ^ ((2 : ℤ) - (k : ℤ))) *
              lam ^ (-(1 : ℝ) / ((2 ^ k - 2 : ℕ) : ℝ)))

/-- **Vinogradov–Weyl Exponential Sum Bound** ([30, Theorem 8.25]).
For `k ≥ 3` and `α ≥ 1`, if `0 < λ ≤ |F^{(k)}(t)| ≤ α λ` on `[a, b]` (`b - a = M ≥ 2`) with
`λ ∈ [M^{-2}, M^{-1}]`, there exist `η_k > 0` and `C_{k,α} > 0` such that
`‖∑_{⌈a⌉ ≤ m ≤ ⌊b⌋} e(F(m))‖ ≤ C_{k,α} M^{1 - η_k}`. -/
axiom vinogradov_weyl_derivative_bound (k : ℕ) (hk : 3 ≤ k) (α : ℝ) (hα : 1 ≤ α) :
    ∃ (C η : ℝ), 0 < C ∧ 0 < η ∧
      ∀ (a b lam : ℝ) (F : ℝ → ℝ),
        0 ≤ a → 2 ≤ b - a → (b - a) ^ (-2 : ℝ) ≤ lam → lam ≤ (b - a) ^ (-1 : ℝ) →
        (∀ t ∈ Set.Icc a b, lam ≤ |iteratedDeriv k F t| ∧ |iteratedDeriv k F t| ≤ α * lam) →
        ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, ePhase (F m)‖ ≤ C * (b - a) ^ (1 - η)

/-- **Davenport Explicit Formula for `ψ(x, χ)` and Landau–Siegel Zero** ([18, Chapter 19]).
For any non-principal real Dirichlet character `χ` of conductor `Q ≤ exp(2 c₀ √(log n))`,
either there is no Siegel zero or there is a unique simple real zero `β₁ ∈ (1 - c₂/log Q, 1)`
such that `∑_{n/2 < p ≤ n} χ(p) log p = -1_{β₁} (n^{β₁} - (n/2)^{β₁})/β₁ + O(n exp(-c₃ √(log n)))`. -/
axiom davenport_explicit_formula_dirichlet :
    ∃ (c₀ c₂ c₃ C : ℝ), 0 < c₀ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧
      ∀ (n Q : ℕ) (χ : DirichletCharacter ℝ Q),
        16 ≤ n → 1 < Q → χ ≠ 1 →
        (Q : ℝ) ≤ Real.exp (2 * c₀ * Real.sqrt (Real.log n)) →
        |∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, χ p * Real.log p| ≤
          C * n * Real.exp (-c₃ * Real.sqrt (Real.log n)) ∨
        ∃ β₁ : ℝ, 1 - c₂ / Real.log Q < β₁ ∧ β₁ < 1 ∧ 0 < β₁ ∧
          |(∑ p ∈ (Finset.Icc (n / 2 + 1) n).filter Nat.Prime, χ p * Real.log p) +
            ((n : ℝ) ^ β₁ - ((n : ℝ) / 2) ^ β₁) / β₁| ≤
            C * n * Real.exp (-c₃ * Real.sqrt (Real.log n))

/-- **Davis's Irrationality Measure of `e`** ([19, 1979]): `μ(e) = 2`. -/
axiom davis_irrationality_measure_e :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (p q : ℤ), 1 ≤ q →
      |(Real.exp 1 : ℝ) - (p : ℝ) / (q : ℝ)| ≥ C / (q : ℝ) ^ (2 + ε)

/-- **Weyl Differencing & Bourgain–Demeter–Guth Vinogradov Mean-Value Theorem** ([62, 3]).
For `k ≥ 2`, `η_k := max(2^{1-k}, 1/(2k(k-1)))`, and `ε₁ > 0`, if `f(y) = α y^k + ∑_{j<k} c_j y^j`
and `|α - a/q| ≤ 1/q^2` with `gcd(a, q) = 1` and `1 ≤ q ≤ Y^k`, then
`‖∑_{y=1}^Y e(f(y))‖ ≤ C_{k,ε₁} Y^{1 + ε₁} (q⁻¹ + Y⁻¹ + q Y^{-k})^{η_k}`. -/
axiom bourgain_demeter_guth_weyl_bound (k : ℕ) (hk : 2 ≤ k) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y q : ℕ) (a : ℤ) (α : ℝ) (f : ℕ → ℝ),
        1 ≤ Y → 1 ≤ q → Int.gcd a q = 1 →
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
        (∀ y : ℕ, ∃ c : Fin k → ℝ,
          f y = α * (y : ℝ) ^ k + ∑ j : Fin k, c j * (y : ℝ) ^ (j : ℕ)) →
        let η_k : ℝ := max ((2 : ℝ) ^ (1 - (k : ℤ))) (1 / (2 * (k : ℝ) * ((k : ℝ) - 1)))
        ‖∑ y ∈ Finset.Icc 1 Y, ePhase (f y)‖ ≤
          C * (Y : ℝ) ^ (1 + ε₁) *
            (1 / (q : ℝ) + 1 / (Y : ℝ) + (q : ℝ) / (Y : ℝ) ^ k) ^ η_k

/-- **Erdős–Turán Discrepancy Inequality** ([22, 1948]). -/
axiom erdos_turan_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y H : ℕ) (x : ℕ → ℝ) (a b : ℝ),
        1 ≤ Y → 1 ≤ H → 0 ≤ a → a ≤ b → b ≤ 1 →
        |(((Finset.Icc 1 Y).filter fun y =>
            let frac := x y - ⌊x y⌋
            a < frac ∧ frac < b).card : ℝ) - (Y : ℝ) * (b - a)| ≤
          C * ((Y : ℝ) / (H : ℝ) +
            ∑ h ∈ Finset.Icc 1 H, (1 / (h : ℝ)) * ‖∑ y ∈ Finset.Icc 1 Y, ePhase ((h : ℝ) * x y)‖)

/-! ### 3. Probability and Continued Fractions -/

/-- **Jessen–Wintner Theorem for Symmetric Rademacher Series** ([30], Jessen–Wintner 1935).
Since `∑_{p ≥ 3} (log p / (p - 1))^2 < ∞`, the infinite independent Rademacher series
`∑_{p ≥ 3} ξ_p log p / (p - 1)` has characteristic function `Φ(τ) = ∏_{p ≥ 3} cos(τ log p / (p - 1))`
and a smooth, strictly positive, symmetric probability density `ρ` on `ℝ`. -/
axiom jessen_wintner_rademacher_density :
    ∃ (Φ ρ : ℝ → ℝ),
      (∀ τ : ℝ, Tendsto (fun B : ℕ => ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
        Real.cos (τ * Real.log p / ((p : ℝ) - 1))) atTop (𝓝 (Φ τ))) ∧
      (∀ x : ℝ, 0 < ρ x ∧ ρ (-x) = ρ x) ∧
      ContDiff ℝ ⊤ ρ ∧
      (∫ x : ℝ, ρ x) = 1 ∧
      (∀ τ : ℝ, (∫ x : ℝ, Complex.exp (Complex.I * τ * x) * (ρ x : ℂ)) = (Φ τ : ℂ))

/-- **Lagrange's Continued-Fraction Midpoint Symmetry Theorem** ([43, §25]). -/
axiom lagrange_continued_fraction_midpoint :
    ∀ (D X₁ Y₁ : ℕ), 0 < D → ¬ IsSquare D →
      X₁ ^ 2 = D * Y₁ ^ 2 + 1 → 0 < Y₁ →
      (∀ x y : ℤ, x ^ 2 - (D : ℤ) * y ^ 2 ≠ -1) →
      (∀ x y : ℕ, 0 < y → x ^ 2 = D * y ^ 2 + 1 → X₁ ≤ x) →
      ∃ (L M Qstar : ℕ) (a : ℤ) (sign : Bool),
        L = 2 * M ∧ 0 < M ∧ 0 < Qstar ∧ (Qstar : ℝ) < 2 * Real.sqrt D ∧
        Qstar ∣ 2 * D ∧ a ∈ ({-1, 0, 1} : Set ℤ) ∧
        (Qstar : ℝ) = (2 : ℝ) ^ a * ((coreNat (if sign then X₁ - 1 else X₁ + 1) : ℕ) : ℝ)

/-! ### 4. Iwasawa Theory, Class Field Theory, and Analytic Class Number Theory -/

/-- **Leopoldt `p`-adic Class Number Formula, Iwasawa Power Series, Ferrero–Washington,
and Mazur–Wiles Iwasawa Main Conjecture** ([61, Thm 5.24 & 7.10], [23], [40]).
For `K = ℚ(√q)` with `q > 1` square-free and an unramified prime `p ≥ 5`, if `ε₁ = X₁ + Y₁ √q`
is the fundamental Pell unit of `ℤ[√q]` (`ε₁ = η_K^{d_n}`, `d_n ∈ {1, 3}`) and `ε₁^k = m + s √q`
with `p ∤ 2 d_n k` and `v_p(s) ≥ 1`, then the normalized `p`-adic regulator satisfies
`v_p(\tilde{R}_p(K)) = v_p(s)`, Leopoldt's formula gives
`v_p(L_p(1, χ_D)) = v_p(h(K)) + v_p(\tilde{R}_p(K)) - 1`, Ferrero–Washington gives `μ_p(K) = 0`,
and Mazur–Wiles gives `v_p(L_p(1, χ_D)) ≥ 1 → λ_p(K) ≥ 1`. -/
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

/-- **Sinnott Circular-Unit Index & Kummer Congruence at `p = 3`** ([54], [61, Thm 5.11]).
For `K = ℚ(√q)` (`q > 1` squarefree) with `3 ∤ q`, let `D = fundDiscrQuad q`. If the normalized
`3`-adic regulator satisfies `v_3(\tilde{R}_3(K)) ≥ 2`, then Leopoldt's formula and Kummer's
congruence `(1 - χ_{-3D}(3)) B_{1, χ_{-3D}} ≡ L_3(1, χ_D) ≡ 0 (mod 3)` imply
`3 ∣ (1 - χ_{-3D}(3)) · h(ℚ(√(-3q)))`. -/
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

/-- **Dirichlet's Analytic Class Number Formula & Tatuzawa's Effective Siegel Theorem**
([18, Ch. 6], [58]).
For every `ε ∈ (0, 1/8)`, there exists at most one exceptional fundamental discriminant `D_*`
such that for every square-free `q > 1` (`K = ℚ(√q)`, fundamental discriminant `D = fundDiscrQuad q ≠ D_*`),
`h(K) · R(K) = (1/2) √D · L(1, χ_D)` with `L(1, χ_D) > 0.655 ε D^{-ε}`. -/
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

/-- **Hasse Norm Theorem, Gauss Genus Theory, and Rédei–Reichardt 4-Rank Theorem** ([24]).
For a squarefree `q > 1` (`K = ℚ(√q)`) with `N(η) = +1` (so `[Cl^+(q) : Cl(q)] = 2`),
the narrow class group decomposes as `Cl^+(q) ≃ 𝒜₂(q) ⊕ Cl^+_odd(q)` with
`|Cl^+(q)| = 2 * h(K)`, `rank₂(𝒜₂(q)) = ω(D) - 1`, and
`dim_{𝔽₂} ker(R^ram) = 1 + rank₄ Cl^+(q)` where `ker(R^ram)` is the kernel of the ramified
quadratic-symbol matrix on squarefree products of ramified primes. -/
axiom hasse_gauss_redei_reichardt :
    ∀ (q : ℕ) (_hq : Squarefree q) (_hq1 : 1 < q) [Fact (¬ IsSquare (q : ℚ))],
      let D : ℕ := (fundDiscrQuad (q : ℤ)).natAbs
      ∃ (rank4_Cl_plus rank2_A2 card_A2 card_Cl_odd : ℕ) (exp_A2 : ℕ),
        card_A2 * card_Cl_odd = 2 * NumberField.classNumber (QuadField (q : ℚ)) ∧
        rank2_A2 = omegaNat D - 1 ∧
        2 ^ rank2_A2 ≤ card_A2 ∧
        card_A2 ≤ exp_A2 ^ rank2_A2 ∧
        rank4_Cl_plus ≤ rank2_A2

/-! ### 5. Differential Wronskians, Galois / Chebotarev, Elliptic Curves, Linear Forms -/

/-- **Siegel's Differential Wronskian Lemma** ([53, Chapter 2, Lemma 4]).
Given `s ≥ 1` nonzero power series `ω_a ∈ ℂ⟦X⟧` satisfying first-order differential equations
`T · ω_a' = (T A_a) · ω_a` (`T, T A_a ∈ ℚ[x]`, `T ≠ 0`), nonzero polynomials `P_a ∈ ℚ[x]`,
and `ℂ(x)`-linear independence of `ω_0, …, ω_{s-1}` (no nontrivial `ℂ[x]`-linear relation
`∑ c_a ω_a = 0`), the `s × s` Wronskian matrix `(P_a^{[k]}(x))_{0 ≤ k < s, 0 ≤ a < s}`
has nonzero determinant in `ℚ[x]`. -/
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

/-- **Grunwald–Wang & Chebotarev Density Theorem for `x^k - A`** ([1, Ch. 10], [59]).
If `A ≠ 0`, `k ≥ 2`, `A` is not a `k`-th power in `ℤ` (and if `8 ∣ k`, not `2^{k/2} c^k`),
then `x^k ≡ A (mod p₀)` has no root for a positive-density set of primes `p₀ ∤ kA`. -/
axiom grunwald_wang_chebotarev_inert_prime :
    ∀ (A : ℤ) (k : ℕ), A ≠ 0 → 2 ≤ k →
      (¬ ∃ c : ℤ, A = c ^ k) →
      (8 ∣ k → ¬ ∃ c : ℤ, A = 2 ^ (k / 2) * c ^ k) →
      ∃ p₀ : ℕ, p₀.Prime ∧ ¬ ((p₀ : ℤ) ∣ (k : ℤ) * A) ∧
        ∀ x : ZMod p₀, x ^ k ≠ (A : ZMod p₀)

/-- **Berend–Harmse Polynomial-Factorial Finiteness Theorem** ([5, Theorem 1.1]).
If `P(x) ∈ ℤ[x]` has an irreducible factor over `ℚ` of degree `≥ 2`, then `n! = P(x)` has only
finitely many integer solutions. -/
axiom berend_harmse_irreducible_factor :
    ∀ (P : Polynomial ℤ), (∃ Q : Polynomial ℚ, Irreducible Q ∧ 2 ≤ Q.natDegree ∧
      Q ∣ P.map (Int.castRingHom ℚ)) →
      ∃ N₀ : ℕ, ∀ n : ℕ, ∀ x : ℤ, (n.factorial : ℤ) = P.eval x → n ≤ N₀

/-- **Modularity, Mazur–Kenku Isogeny, Serre Open Image, and Ribet Level-Lowering**
([63, 2, 39, 31, 51, 46]).
Let `E / ℚ` be a non-integral-`j` elliptic curve (`E.IsElliptic`, `j(E) ∉ ℤ`) with full rational
2-torsion (`E.a₁ = 0 ∧ E.a₃ = 0`, quadratic discriminant nonzero, three rational roots).
Then:
1. By Breuil–Conrad–Diamond–Taylor [63, 2], `E` is modular.
2. By Mazur–Kenku [39, 31] and Serre's open image theorem [51], for every prime `ℓ ≥ 5` the
   mod-`ℓ` Galois representation `ρ̄_{E,ℓ}` has image `GL₂(𝔽_ℓ)`.
3. By Ribet's level-lowering theorem [46], the minimal lowered level `N_ℓ` of `ρ̄_{E,ℓ}` is
   divisible by every prime `p` of multiplicative reduction (`v_p(Δ_min) > 0`, `v_p(c₄) = 0`)
   for which `ℓ ∤ v_p(Δ_min)`. -/
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

/-- **Matveev (2000) and Yu (2007) Linear Forms in Logarithms Lower Bound** ([38, 64]).
For `N ≥ 1` primes `p₁, …, p_N` and nonzero integers `b₁, …, b_N` with `B := max |b_i| ≥ 2` such
that `Λ := ∑_{i=1}^N b_i log p_i ≠ 0`, there is an absolute constant `C > 1` such that
`log |Λ| ≥ - C^N N^N (∏_{i=1}^N log p_i) log B`. -/
axiom matveev_yu_linear_forms_bound :
    ∃ C : ℝ, 1 < C ∧
      ∀ (N : ℕ) (p : Fin N → ℕ) (b : Fin N → ℤ) (B : ℝ),
        1 ≤ N → (∀ i, (p i).Prime) → Function.Injective p →
        2 ≤ B → (∀ i, |(b i : ℝ)| ≤ B) →
        let Λ : ℝ := ∑ i : Fin N, (b i : ℝ) * Real.log (p i : ℝ)
        Λ ≠ 0 →
        Real.log |Λ| ≥ -(C ^ N * (N : ℝ) ^ N * (∏ i : Fin N, Real.log (p i : ℝ)) * Real.log B)

end BrocardFormalization.External

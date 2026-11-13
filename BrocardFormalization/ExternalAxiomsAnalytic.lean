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
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

noncomputable section

open scoped BigOperators
open Filter Topology

namespace BrocardFormalization.External

axiom deLaValleePoussin_pnt :
    ∃ (c₁ C : ℝ), 0 < c₁ ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.theta x - x| ≤ C * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) ∧
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹| ≤
        C * x * Real.exp (-c₁ * Real.sqrt (Real.log x))

axiom mertens_first_theorem :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.Icc 3 ⌊x⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) -
          (Real.log x - Real.eulerMascheroniConstant - Real.log 2)) atTop (𝓝 0) ∧
      ∀ x : ℝ, 2 ≤ x →
        |(∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, Real.log p / (p : ℝ)) - Real.log x| ≤ C

axiom pnt_arithmetic_progression (q a : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a q) :
    Tendsto (fun x : ℝ =>
      ((∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q), Real.log p) -
        x / (Nat.totient q : ℝ)) / x) atTop (𝓝 0)

axiom breusch_bertrand_mod_four :
    ∀ x : ℝ, 7 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p % 4 = 3

axiom rosser_schoenfeld_theta_diff :
    ∀ n : ℕ, 116 ≤ n →
      Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n : ℝ) / 2) > 0.4 * (n : ℝ)

axiom schoenfeld_prime_gap :
    ∀ x : ℝ, 2010760 ≤ x → Chebyshev.theta (x + x / 16597) > Chebyshev.theta x

axiom nagura_prime_interval :
    ∀ x : ℝ, 25 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (6 / 5 : ℝ) * x

axiom berndt_galway_brocard_bound :
    ∀ n m : ℕ, IsBrocardSol n m → 8 ≤ n → n ≤ 10 ^ 9 → False

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

axiom vaaler_indicator_majorant (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Iplus : ℝ → ℝ) (chat : ℤ → ℂ),
      (∀ x : ℝ, (Iplus x : ℂ) = ∑ h ∈ Finset.Icc (-(H : ℤ)) H, chat h * ePhase ((h : ℝ) * x)) ∧
      (∀ x : ℝ, 0 ≤ Iplus x) ∧
      (∀ x : ℝ, |x| ≤ δ → 1 ≤ Iplus x) ∧
      (chat 0 = ((2 * δ + 1 / ((H : ℝ) + 1)) : ℂ)) ∧
      (∀ h : ℤ, ‖chat h‖ ≤ 2 * δ + 1 / ((H : ℝ) + 1))

axiom kusmin_landau_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b lam1 : ℝ) (F : ℝ → ℝ),
        0 ≤ a → a ≤ b → 0 < lam1 →
        (MonotoneOn (deriv F) (Set.Icc a b) ∨ AntitoneOn (deriv F) (Set.Icc a b)) →
        (∀ t ∈ Set.Icc a b, lam1 ≤ |deriv F t| ∧ |deriv F t| ≤ 1 / 2) →
        ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, ePhase (F m)‖ ≤ C / lam1

axiom van_der_corput_kth_derivative (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b lam : ℝ) (F : ℝ → ℝ),
        0 ≤ a → 1 ≤ b - a → 0 < lam →
        (∀ t ∈ Set.Icc a b, lam ≤ |iteratedDeriv k F t| ∧ |iteratedDeriv k F t| ≤ α * lam) →
        ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, ePhase (F m)‖ ≤
          C * ((b - a) * lam ^ ((1 : ℝ) / ((2 ^ k - 2 : ℕ) : ℝ)) +
            (b - a) ^ (1 - (2 : ℝ) ^ ((2 : ℤ) - (k : ℤ))) *
              lam ^ (-(1 : ℝ) / ((2 ^ k - 2 : ℕ) : ℝ)))

axiom vinogradov_weyl_derivative_bound (k : ℕ) (hk : 3 ≤ k) (α : ℝ) (hα : 1 ≤ α) :
    ∃ (C η : ℝ), 0 < C ∧ 0 < η ∧
      ∀ (a b lam : ℝ) (F : ℝ → ℝ),
        0 ≤ a → 2 ≤ b - a → (b - a) ^ (-2 : ℝ) ≤ lam → lam ≤ (b - a) ^ (-1 : ℝ) →
        (∀ t ∈ Set.Icc a b, lam ≤ |iteratedDeriv k F t| ∧ |iteratedDeriv k F t| ≤ α * lam) →
        ‖∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, ePhase (F m)‖ ≤ C * (b - a) ^ (1 - η)

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

axiom davis_irrationality_measure_e :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (p q : ℤ), 1 ≤ q →
      |(Real.exp 1 : ℝ) - (p : ℝ) / (q : ℝ)| ≥ C / (q : ℝ) ^ (2 + ε)

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

axiom erdos_turan_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y H : ℕ) (x : ℕ → ℝ) (a b : ℝ),
        1 ≤ Y → 1 ≤ H → 0 ≤ a → a ≤ b → b ≤ 1 →
        |(((Finset.Icc 1 Y).filter fun y =>
            let frac := x y - ⌊x y⌋
            a < frac ∧ frac < b).card : ℝ) - (Y : ℝ) * (b - a)| ≤
          C * ((Y : ℝ) / (H : ℝ) +
            ∑ h ∈ Finset.Icc 1 H, (1 / (h : ℝ)) * ‖∑ y ∈ Finset.Icc 1 Y, ePhase ((h : ℝ) * x y)‖)

axiom jessen_wintner_rademacher_density :
    ∃ (Φ ρ : ℝ → ℝ),
      (∀ τ : ℝ, Tendsto (fun B : ℕ => ∏ p ∈ (Finset.Icc 3 B).filter Nat.Prime,
        Real.cos (τ * Real.log p / ((p : ℝ) - 1))) atTop (𝓝 (Φ τ))) ∧
      (∀ x : ℝ, 0 < ρ x ∧ ρ (-x) = ρ x) ∧
      ContDiff ℝ ⊤ ρ ∧
      (∫ x : ℝ, ρ x) = 1 ∧
      (∀ τ : ℝ, (∫ x : ℝ, Complex.exp (Complex.I * τ * x) * (ρ x : ℂ)) = (Φ τ : ℂ))

axiom lagrange_continued_fraction_midpoint :
    ∀ (D X₁ Y₁ : ℕ), 0 < D → ¬ IsSquare D →
      X₁ ^ 2 = D * Y₁ ^ 2 + 1 → 0 < Y₁ →
      (∀ x y : ℤ, x ^ 2 - (D : ℤ) * y ^ 2 ≠ -1) →
      (∀ x y : ℕ, 0 < y → x ^ 2 = D * y ^ 2 + 1 → X₁ ≤ x) →
      ∃ (L M Qstar : ℕ) (a : ℤ) (sign : Bool),
        L = 2 * M ∧ 0 < M ∧ 0 < Qstar ∧ (Qstar : ℝ) < 2 * Real.sqrt D ∧
        Qstar ∣ 2 * D ∧ a ∈ ({-1, 0, 1} : Set ℤ) ∧
        (Qstar : ℝ) = (2 : ℝ) ^ a * ((coreNat (if sign then X₁ - 1 else X₁ + 1) : ℕ) : ℝ)

end BrocardFormalization.External

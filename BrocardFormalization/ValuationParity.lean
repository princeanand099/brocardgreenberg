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
          C'_δ * W₀ * P * (Real.log n) ^ (-(R + 2 : ℤ)) := by
  sorry

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
          C_δ * W₀ * P * (n : ℝ) ^ (-η_δ) := by
  sorry

theorem theorem_2_5_i :
    IsBigOAtTop
      (fun n => DeltaParity n - (Real.log 2 - 1 - SigmaParityStar n) * (n : ℝ))
      (fun n => (n : ℝ) / Real.log n) := by
  sorry

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
  sorry

theorem theorem_2_5_iii (h : ℕ) (hh : 2 ≤ h) (c : ZMod h) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IsLittleOAtTop
      (fun n =>
        (∑ p ∈ (Finset.Icc (⌊(n : ℝ) ^ a⌋₊ + 1) ⌊(n : ℝ) ^ b⌋₊).filter
            (fun p => p.Prime ∧ (padicValNat p n.factorial : ZMod h) = c),
          (padicValNat p n.factorial : ℝ) * Real.log p) -
        ((b - a) / (h : ℝ)) * (n : ℝ) * Real.log n)
      (fun n => (n : ℝ) * Real.log n) := by
  sorry

end BrocardFormalization

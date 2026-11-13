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

/-!
# Section 6 & Theorem 1.3(i): Pairwise SL₂(ℤ) Duality and Capacity Diamond

This module translates Section 6 and Theorem 1.3(i) of the manuscript:
* `theorem_6_1`: Universal `SL₂(ℤ)` four-GCD system `(X, Y, Z, W)`, twin norm identities,
  `ℤ[√P]` identities, and Quadrant IV character lock.
* `prop_6_2_i`..`prop_6_2_iv`: Quadratic-radical identities (with Audit Item 4 fixing Eq. (6.7)),
  quartic core-split Thue system, consecutive square-parameter `X`-splitting, and
  three-solution octant-pair Pfaffian linear system.
* `theorem_6_3_i`..`theorem_6_3_iii`: Uniqueness of `n = 4` CRT boundary collapse,
  quarter-factorial equipartition for `(n, n+1)`, and unconditional square-shift exclusions.
* `lemma_6_4`: Odd-harmonic Vaaler diagonal non-vanishing for parity-flip primes.
* `theorem_6_5`: Universal Capacity Diamond, `k = 2` separation, and audited Rankin spherical
  cap bound (Audit Item 5).
* `theorem_1_3_i`: Extreme sparsity `#{1 ≤ n ≤ N : k_n = 2} ≪_ε N^ε`.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 6.1 Universal SL₂(ℤ) Four-GCD System and Twin Norm Identities -/

/-- Factorial shift `P(n₁, n₂) := n₂! / n₁!` for `n₁ ≤ n₂`. -/
def factShift (n₁ n₂ : ℕ) : ℕ :=
  n₂.factorial / n₁.factorial

/-- Four GCD components `X, Y, Z, W` attached to two Brocard solutions `(n₁, m₁), (n₂, m₂)`. -/
def gcdX (m₁ m₂ : ℕ) : ℕ := Nat.gcd ((m₁ - 1) / 2) ((m₂ - 1) / 2)
def gcdY (m₁ m₂ : ℕ) : ℕ := Nat.gcd ((m₁ + 1) / 2) ((m₂ + 1) / 2)
def gcdZ (m₁ m₂ : ℕ) : ℕ := Nat.gcd ((m₁ - 1) / 2) ((m₂ + 1) / 2)
def gcdW (m₁ m₂ : ℕ) : ℕ := Nat.gcd ((m₁ + 1) / 2) ((m₂ - 1) / 2)

theorem theorem_6_1 (n₁ n₂ m₁ m₂ : ℕ) (hn₁ : 4 ≤ n₁) (h12 : n₁ < n₂)
    (hsol₁ : IsBrocardSol n₁ m₁) (hsol₂ : IsBrocardSol n₂ m₂) :
    let A₁ := (m₁ - 1) / 2
    let B₁ := (m₁ + 1) / 2
    let A₂ := (m₂ - 1) / 2
    let B₂ := (m₂ + 1) / 2
    let U := (m₂ - m₁) / 2
    let V := (m₂ + m₁) / 2
    let P := factShift n₁ n₂
    let X := gcdX m₁ m₂
    let Y := gcdY m₁ m₂
    let Z := gcdZ m₁ m₂
    let W := gcdW m₁ m₂
    Nat.gcd X Y = 1 ∧ Nat.gcd X Z = 1 ∧ Nat.gcd X W = 1 ∧
    Nat.gcd Y Z = 1 ∧ Nat.gcd Y W = 1 ∧ Nat.gcd Z W = 1 ∧
    0 < X ∧ 0 < Y ∧ 0 < Z ∧ 0 < W ∧
    A₁ = X * Z ∧ B₁ = Y * W ∧ X * Y * Z * W = n₁.factorial / 4 ∧
    (∃! q : ℕ × ℕ × ℕ × ℕ,
      let (a, b, c, d) := q
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a * b = P - 1 ∧ c * d = P ∧
      A₂ = c * X * W ∧ B₂ = d * Y * Z ∧ U = a * X * Y ∧ V = b * Z * W ∧
      (X : ℤ) = (b : ℤ) * W - (d : ℤ) * Y ∧
      (Z : ℤ) = (c : ℤ) * W - (a : ℤ) * Y ∧
      (d : ℤ) * (Y : ℤ) ^ 2 - (c : ℤ) * (X : ℤ) ^ 2 = b ∧
      (c : ℤ) * (W : ℤ) ^ 2 - (d : ℤ) * (Z : ℤ) ^ 2 = a ∧
      2 * a * c * X ^ 2 = P * m₁ - m₂ - (P - 1) ∧
      2 * a * d * Y ^ 2 = P * m₁ - m₂ + (P - 1) ∧
      2 * b * d * Z ^ 2 = P * m₁ + m₂ - (P - 1) ∧
      2 * b * c * W ^ 2 = P * m₁ + m₂ + (P - 1) ∧
      (let α₁ : QuadraticAlgebra ℤ (P : ℤ) 0 := ⟨(d * Y : ℤ), (X : ℤ)⟩
       let α₂ : QuadraticAlgebra ℤ (P : ℤ) 0 := ⟨(c * W : ℤ), (Z : ℤ)⟩
       QuadraticAlgebra.norm α₁ = (b * d : ℤ) ∧
       QuadraticAlgebra.norm α₂ = (a * c : ℤ) ∧
       α₁ * α₂ = ⟨(P * m₁ : ℤ), (m₂ : ℤ)⟩ ∧
       α₁ * star α₂ = ⟨(P : ℤ), -1⟩) ∧
      (∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ n₁ → ¬ p ∣ P * (P - 1) →
        (p ∣ X → jacobiSym ((b * d : ℕ) : ℤ) p = 1) ∧
        (p ∣ Y → jacobiSym (-(b * c : ℤ)) p = 1) ∧
        (p ∣ Z → jacobiSym ((a * c : ℕ) : ℤ) p = 1) ∧
        (p ∣ W → jacobiSym (-(a * d : ℤ)) p = 1) ∧
        (1 + jacobiSym (-(P : ℤ)) p) * (1 + jacobiSym (-((P - 1 : ℕ) : ℤ)) p) *
          (1 - jacobiSym ((b * d : ℕ) : ℤ) p) = 0)) := by
  sorry

/-- Proposition 6.2(i): Exact quadratic-radical identities (with Audit Item 4 fixing Eq. (6.7)). -/
theorem prop_6_2_i (n₁ n₂ m₁ m₂ a b c d : ℕ) (hn₁ : 4 ≤ n₁) (h12 : n₁ < n₂)
    (hsol₁ : IsBrocardSol n₁ m₁) (hsol₂ : IsBrocardSol n₂ m₂)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a * b = factShift n₁ n₂ - 1) (hcd : c * d = factShift n₁ n₂)
    (hA₂ : (m₂ - 1) / 2 = c * gcdX m₁ m₂ * gcdW m₁ m₂)
    (hB₂ : (m₂ + 1) / 2 = d * gcdY m₁ m₂ * gcdZ m₁ m₂)
    (hU : (m₂ - m₁) / 2 = a * gcdX m₁ m₂ * gcdY m₁ m₂)
    (hV : (m₂ + m₁) / 2 = b * gcdZ m₁ m₂ * gcdW m₁ m₂) :
    let P : ℝ := factShift n₁ n₂
    let X : ℝ := gcdX m₁ m₂
    let Y : ℝ := gcdY m₁ m₂
    let Z : ℝ := gcdZ m₁ m₂
    let W : ℝ := gcdW m₁ m₂
    (Real.sqrt d * Y - Real.sqrt c * X) ^ 2 =
      ((P - 1) * (Real.sqrt P + 1)) / ((a : ℝ) * (Real.sqrt P * m₁ + m₂)) ∧
    (Real.sqrt c * W - Real.sqrt d * Z) ^ 2 =
      ((P - 1) * (Real.sqrt P - 1)) / ((b : ℝ) * (Real.sqrt P * m₁ + m₂)) ∧
    ((d : ℝ) * Y + X * Real.sqrt P) ^ 2 =
      ((d : ℝ) / a) * (Real.sqrt P - 1) * (m₂ + m₁ * Real.sqrt P) ∧
    ((c : ℝ) * W + Z * Real.sqrt P) ^ 2 =
      ((c : ℝ) / b) * (Real.sqrt P + 1) * (m₂ + m₁ * Real.sqrt P) := by
  sorry

theorem prop_6_2_ii (n₁ n₂ m₁ m₂ a b c d : ℕ) (hn₁ : 4 ≤ n₁) (h12 : n₁ < n₂)
    (hsol₁ : IsBrocardSol n₁ m₁) (hsol₂ : IsBrocardSol n₂ m₂)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a * b = factShift n₁ n₂ - 1) (hcd : c * d = factShift n₁ n₂)
    (hA₂ : (m₂ - 1) / 2 = c * gcdX m₁ m₂ * gcdW m₁ m₂)
    (hB₂ : (m₂ + 1) / 2 = d * gcdY m₁ m₂ * gcdZ m₁ m₂)
    (hU : (m₂ - m₁) / 2 = a * gcdX m₁ m₂ * gcdY m₁ m₂)
    (hV : (m₂ + m₁) / 2 = b * gcdZ m₁ m₂ * gcdW m₁ m₂) :
    let X := gcdX m₁ m₂
    let Y := gcdY m₁ m₂
    let Z := gcdZ m₁ m₂
    let W := gcdW m₁ m₂
    let δX := coreNat X; let x0 := sqrtPartNat X
    let δY := coreNat Y; let y0 := sqrtPartNat Y
    let δZ := coreNat Z; let z0 := sqrtPartNat Z
    let δW := coreNat W; let w0 := sqrtPartNat W
    (d : ℤ) * (δY : ℤ) ^ 2 * (y0 : ℤ) ^ 4 - (c : ℤ) * (δX : ℤ) ^ 2 * (x0 : ℤ) ^ 4 = b ∧
    (c : ℤ) * (δW : ℤ) ^ 2 * (w0 : ℤ) ^ 4 - (d : ℤ) * (δZ : ℤ) ^ 2 * (z0 : ℤ) ^ 4 = a ∧
    δX * δY * δZ * δW = coreNat (n₁.factorial / 4) ∧
    coreNat (n₁.factorial / 4) ∣ 2 * qn n₁ := by
  sorry

theorem prop_6_2_iii (n m₁ m₂ a b c d : ℕ) (hn : 4 ≤ n)
    (hsol₁ : IsBrocardSol n m₁) (hsol₂ : IsBrocardSol (n + 1) m₂)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a * b = n) (hcd : c * d = n + 1)
    (hA₂ : (m₂ - 1) / 2 = c * gcdX m₁ m₂ * gcdW m₁ m₂)
    (hB₂ : (m₂ + 1) / 2 = d * gcdY m₁ m₂ * gcdZ m₁ m₂)
    (hU : (m₂ - m₁) / 2 = a * gcdX m₁ m₂ * gcdY m₁ m₂)
    (hV : (m₂ + m₁) / 2 = b * gcdZ m₁ m₂ * gcdW m₁ m₂) :
    (IsSquare (b * d) ∨ IsSquare (a * c) ↔
      (IsSquare b ∧ IsSquare d) ∨ (IsSquare a ∧ IsSquare c)) ∧
    (∀ b₀ d₀ : ℕ, b = b₀ ^ 2 → d = d₀ ^ 2 →
      ((d₀ : ℤ) * (gcdY m₁ m₂ : ℤ) - b₀) * ((d₀ : ℤ) * (gcdY m₁ m₂ : ℤ) + b₀) =
        (c : ℤ) * (gcdX m₁ m₂ : ℤ) ^ 2 ∧
      Nat.gcd ((d₀ * gcdY m₁ m₂) - b₀) (d₀ * gcdY m₁ m₂ + b₀) ∣ 2 ∧
      ∃ X₁ X₂ c₁ c₂ : ℕ, gcdX m₁ m₂ = X₁ * X₂ ∧ Nat.gcd X₁ X₂ = 1 ∧
        (c₂ : ℤ) * (X₂ : ℤ) ^ 2 - (c₁ : ℤ) * (X₁ : ℤ) ^ 2 = 2 * b₀ ∧
        (2 * b₀ : ℝ) ≤ 2 * Real.sqrt n) := by
  sorry

theorem prop_6_2_iv (n₁ n₂ n₃ m₁ m₂ m₃ : ℕ) (hn₁ : 4 ≤ n₁) (h12 : n₁ < n₂) (h23 : n₂ < n₃)
    (hsol₁ : IsBrocardSol n₁ m₁) (hsol₂ : IsBrocardSol n₂ m₂) (hsol₃ : IsBrocardSol n₃ m₃)
    (a₁₂ b₁₂ a₁₃ b₁₃ at₂₃ : ℕ)
    (hU₁₂ : (m₂ - m₁) / 2 = a₁₂ * gcdX m₁ m₂ * gcdY m₁ m₂)
    (hV₁₂ : (m₂ + m₁) / 2 = b₁₂ * gcdZ m₁ m₂ * gcdW m₁ m₂)
    (hU₁₃ : (m₃ - m₁) / 2 = a₁₃ * gcdX m₁ m₃ * gcdY m₁ m₃)
    (hV₁₃ : (m₃ + m₁) / 2 = b₁₃ * gcdZ m₁ m₃ * gcdW m₁ m₃)
    (hU₂₃ : (m₃ - m₂) / 2 = at₂₃ * gcdX m₂ m₃ * gcdY m₂ m₃) :
    let octant (σ₁ σ₂ σ₃ : Bool) : ℕ :=
      ∏ p ∈ (Finset.Icc 2 n₁).filter Nat.Prime,
        let e := padicValNat p (n₁.factorial / 4)
        if ((decide (p ∣ (m₁ + 1) / 2) == σ₁) &&
            (decide (p ∣ (m₂ + 1) / 2) == σ₂) &&
            (decide (p ∣ (m₃ + 1) / 2) == σ₃)) then p ^ e else 1
    let α := octant true true true * octant false false false
    let β := octant true true false * octant false false true
    let γ := octant true false true * octant false true false
    let δ := octant true false false * octant false true true
    (a₁₃ : ℤ) * γ - (a₁₂ : ℤ) * β = (at₂₃ : ℤ) * δ ∧
    (b₁₃ : ℤ) * β - (b₁₂ : ℤ) * γ = (at₂₃ : ℤ) * α ∧
    ((a₁₃ : ℤ) * b₁₃ - (a₁₂ : ℤ) * b₁₂) * β * γ = (at₂₃ : ℤ) * γ * ((a₁₃ : ℤ) * α + b₁₂ * δ) := by
  sorry

/-! ### 6.2 Consecutive-Index Rigidity and Unconditional Square-Shift Exclusions -/

theorem theorem_6_3_i (n : ℕ) (hn : 4 ≤ n) :
    (∀ m₁ m₂ : ℕ, IsBrocardSol n m₁ → IsBrocardSol (n + 1) m₂ →
      (m₂ = n.factorial / 2 - 1 ↔ n.factorial = 4 * (n + 2))) ∧
    ((∃ m₁ m₂ : ℕ, IsBrocardSol n m₁ ∧ IsBrocardSol (n + 1) m₂ ∧ m₂ = n.factorial / 2 - 1) ↔
      n = 4) := by
  sorry

theorem theorem_6_3_ii :
    (∀ n m₁ m₂ : ℕ, 6 ≤ n → IsBrocardSol n m₁ → IsBrocardSol (n + 1) m₂ →
      1 < gcdX m₁ m₂ ∧ 1 < gcdY m₁ m₂ ∧ 1 < gcdZ m₁ m₂ ∧ 1 < gcdW m₁ m₂) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n m₁ m₂ : ℕ, 6 ≤ n → IsBrocardSol n m₁ → IsBrocardSol (n + 1) m₂ →
      |Real.log (gcdX m₁ m₂) - (1 / 4 : ℝ) * Real.log n.factorial| ≤ C * Real.log n ∧
      |Real.log (gcdY m₁ m₂) - (1 / 4 : ℝ) * Real.log n.factorial| ≤ C * Real.log n ∧
      |Real.log (gcdZ m₁ m₂) - (1 / 4 : ℝ) * Real.log n.factorial| ≤ C * Real.log n ∧
      |Real.log (gcdW m₁ m₂) - (1 / 4 : ℝ) * Real.log n.factorial| ≤ C * Real.log n) ∧
    (∃ N₀ : ℕ, 6 ≤ N₀ ∧ ∀ n m₁ m₂ : ℕ, N₀ ≤ n → (hn6 : 6 ≤ n) →
      (hsol₁ : IsBrocardSol n m₁) → (hsol₂ : IsBrocardSol (n + 1) m₂) →
      ¬ (pellIndex (by omega) hsol₁ = 2 ∧ pellIndex (by omega) hsol₂ = 2)) := by
  sorry

theorem theorem_6_3_iii :
    (∀ n₁ n₂ m₁ m₂ t : ℕ, 4 ≤ n₁ → n₁ < n₂ →
      IsBrocardSol n₁ m₁ → IsBrocardSol n₂ m₂ →
      factShift n₁ n₂ < 4 * (n₁.factorial + 1) →
      factShift n₁ n₂ = t ^ 2 → False) ∧
    (∀ t : ℕ, 2 ≤ t → ¬ ∃ m₁ m₂ : ℕ, IsBrocardSol (t ^ 2 - 1) m₁ ∧ IsBrocardSol (t ^ 2) m₂) ∧
    (∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ j m₁ m₂ : ℕ, N₀ ≤ j → (hj2 : 2 ≤ j) →
      (hsol₁ : IsBrocardSol (j ^ 2) m₁) → (hsol₂ : IsBrocardSol ((j + 1) ^ 2) m₂) →
      ¬ (pellIndex (by nlinarith) hsol₁ = 2 ∧ pellIndex (by nlinarith) hsol₂ = 2)) := by
  sorry

/-! ### 6.3 Odd-Harmonic Vaaler Diagonal Non-Vanishing, Capacity Diamond, and Theorem 1.3(i) -/

theorem lemma_6_4 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n₁ n₂ : ℕ, N₀ ≤ n₁ → n₁ < n₂ → ((n₂ - n₁ : ℕ) : ℝ) ≤ (n₁ : ℝ) ^ η →
        let α : ℝ := Real.log ((n₂ - n₁ : ℕ) : ℝ) / Real.log (n₁ : ℝ)
        let P := factShift n₁ n₂
        |∑ p ∈ (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p P),
            (padicValNat p n₁.factorial : ℝ) * Real.log p -
          (α / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ)| ≤ ε * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
  sorry

/-- Odd-core polarization weight `θ(n) := log B^{(2)}(n) / S_odd(n)` (0 if `k_n = 2`). -/
def thetaPol (n m : ℕ) (hn : 4 ≤ n) (hsol : IsBrocardSol n m) : ℝ :=
  if pellIndex hn hsol = 2 then 0 else Real.log (B2sol n m) / Sodd n

/-- Upper-band polarization weight `θ_ε(n)` (0 if `k_n = 2`). -/
def thetaEps (n m : ℕ) (hn : 4 ≤ n) (hsol : IsBrocardSol n m) (ε : ℝ) : ℝ :=
  open Classical in
  if pellIndex hn hsol = 2 then 0
  else
    (∑ p ∈ (Podd n).filter (fun p : ℕ => (n : ℝ) ^ (1 - ε / 2) < (p : ℝ) ∧ p ∣ B2sol n m),
      (padicValNat p n.factorial : ℝ) * Real.log p) /
    (∑ p ∈ (Podd n).filter (fun p : ℕ => (n : ℝ) ^ (1 - ε / 2) < (p : ℝ)),
      (padicValNat p n.factorial : ℝ) * Real.log p)

/-- Capacity Diamond and Rankin Spherical Cap Bound (Theorem 6.5).
Note (Audit Item 5): In the Rankin bound, correlation is `η√ε - o(1)` (yielding `≤ ⌊(η^2 ε)⁻¹⌋ + 1`
per interval `[N', N' + N'^{1-ε}]`), and covering `[1, N]` adds a dyadic factor giving
`C_ε η^{-2} N^ε` for `N ≥ N₀(ε, η)`. -/
theorem theorem_6_5 :
    (∀ η : ℝ, 0 < η → η < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n₁ n₂ m₁ m₂ : ℕ, N₀ ≤ n₁ → (hn₁ : 4 ≤ n₁) → (h12 : n₁ < n₂) →
        ((n₂ - n₁ : ℕ) : ℝ) ≤ (n₁ : ℝ) ^ η →
        (hsol₁ : IsBrocardSol n₁ m₁) → (hsol₂ : IsBrocardSol n₂ m₂) →
        let α : ℝ := Real.log ((n₂ - n₁ : ℕ) : ℝ) / Real.log (n₁ : ℝ)
        let θ₁ := thetaPol n₁ m₁ (by omega) hsol₁
        let θ₂ := thetaPol n₂ m₂ (by omega) hsol₂
        (1 - α) / 2 - δ ≤ θ₁ + θ₂ ∧
        θ₁ + θ₂ ≤ (3 + α) / 2 + δ ∧
        |θ₁ - θ₂| ≤ (1 + α) / 2 + δ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n₁ n₂ m₁ m₂ : ℕ, N₀ ≤ n₁ → (hn₁ : 4 ≤ n₁) → (h12 : n₁ < n₂) →
        (hsol₁ : IsBrocardSol n₁ m₁) → (hsol₂ : IsBrocardSol n₂ m₂) →
        pellIndex (by omega) hsol₁ = 2 → pellIndex (by omega) hsol₂ = 2 →
        ((n₂ - n₁ : ℕ) : ℝ) > (n₁ : ℝ) ^ (1 - ε)) ∧
    (∀ ε η : ℝ, 0 < ε → ε < 1 / 4 → 0 < η → η ≤ 1 / 2 →
      open Classical in
      (∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N' : ℕ, N₀ ≤ N' →
        ((Finset.Icc N' (N' + ⌊(N' : ℝ) ^ (1 - ε)⌋₊)).filter (fun n =>
          ∃ m : ℕ, ∃ (hn : 4 ≤ n) (hsol : IsBrocardSol n m),
            |thetaEps n m hn hsol ε - 1 / 2| ≥ η)).card ≤ ⌊(η ^ 2 * ε)⁻¹⌋₊ + 1) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Icc 4 N).filter (fun n =>
          ∃ m : ℕ, ∃ (hn : 4 ≤ n) (hsol : IsBrocardSol n m),
            |thetaEps n m hn hsol ε - 1 / 2| ≥ η)).card : ℝ) ≤
          C * η ^ (-2 : ℝ) * (N : ℝ) ^ ε)) := by
  sorry

theorem theorem_1_3_i (ε : ℝ) (hε : 0 < ε) :
    (∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n₁ n₂ m₁ m₂ : ℕ, N₀ ≤ n₁ → (hn₁ : 4 ≤ n₁) → (h12 : n₁ < n₂) →
        (hsol₁ : IsBrocardSol n₁ m₁) → (hsol₂ : IsBrocardSol n₂ m₂) →
        pellIndex (by omega) hsol₁ = 2 → pellIndex (by omega) hsol₂ = 2 →
        ((n₂ - n₁ : ℕ) : ℝ) > (n₁ : ℝ) ^ (1 - ε)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      open Classical in
      (((Finset.Icc 1 N).filter (fun n =>
        ∃ m : ℕ, ∃ (hn : 4 ≤ n) (hsol : IsBrocardSol n m),
          pellIndex hn hsol = 2)).card : ℝ) ≤ C * (N : ℝ) ^ ε) := by
  sorry

end BrocardFormalization

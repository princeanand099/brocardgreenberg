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
  sorry

/-- Minimal midpoint character `ψ_min` on primes `p`: Kronecker symbol `(-2 δ₁^mid / p)` or `(2 δ₂^mid / p)`. -/
def psiMin (n : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6) (p : ℕ) : ℤ :=
  let d1s := oddPart (deltaMid1 n (by omega) hn6)
  let d2s := oddPart (deltaMid2 n (by omega) hn6)
  if d1s ≤ d2s then jacobiSym (-2 * (deltaMid1 n (by omega) hn6 : ℤ)) p
  else jacobiSym (2 * (deltaMid2 n (by omega) hn6 : ℤ)) p

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
  sorry

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

theorem theorem_5_2_i :
    (∀ n m : ℕ, (hn : 4 ≤ n) → (hsol : IsBrocardSol n m) →
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
        |Real.log (B2sol n m) - Real.log ((Z1starSol n m : ℝ) ^ 2) -
          (1 / 2 : ℝ) * (((2 * (w1 : ℝ) - padicValNat 2 n.factorial) * Real.log 2) -
            DeltaParity n)| ≤ C * Real.exp (-(1 / 3 : ℝ) * n * Real.log n) ∧
        |Real.log (B1sol n m) - Real.log ((Z2starSol n m : ℝ) ^ 2) -
          (1 / 2 : ℝ) * (((2 * (w2 : ℝ) - padicValNat 2 n.factorial) * Real.log 2) -
            DeltaParity n)| ≤ C * Real.exp (-(1 / 3 : ℝ) * n * Real.log n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ n m : ℕ, N₀ ≤ n → IsBrocardSol n m →
        (largestPrimeFactor (m - 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (largestPrimeFactor (m + 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (omegaNat (m - 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (omegaNat (m + 1) : ℝ) ≥ (n : ℝ) ^ (1 / 2 - ε) ∧
        (radNat (m - 1) : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ∧
        (radNat (m + 1) : ℝ) ≥ Real.exp ((n : ℝ) ^ (1 / 2 - ε))) := by
  sorry

theorem theorem_5_2_ii :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      ∀ n : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) → N₀ ≤ n →
        (deltaMid1 n (by omega) hn6 : ℝ) > Real.exp (c₀ * Real.sqrt (Real.log n)) ∧
        (deltaMid2 n (by omega) hn6 : ℝ) > Real.exp (c₀ * Real.sqrt (Real.log n)) ∧
        (∀ x y : ℤ, x ^ 2 - (qn n : ℤ) * y ^ 2 ≠ 2 ∧ x ^ 2 - (qn n : ℤ) * y ^ 2 ≠ -2) := by
  sorry

/-! ### 5.2 Homogeneous 𝔽₂-Laplacian, Galois Cohomology, and Reduced Dual Quartics -/

/-- `r`-th 2-adic valuation layer `ℒ_r(n) := {3 ≤ p ≤ n : p prime, v₂(v_p(n!)) = r}` (5.8). -/
def layer2Adic (n r : ℕ) : Finset ℕ :=
  (Finset.Icc 3 n).filter fun p => p.Prime ∧ padicValNat 2 (padicValNat p n.factorial) = r

/-- Even split prime set `𝒫_even^+(n) := {p ∈ 𝒫_even(n) \ {2} : (-q_n / p) = +1}`. -/
def PevenPlus (n : ℕ) : Finset ℕ :=
  (Peven n).filter fun p => 3 ≤ p ∧ jacobiSym (-(qn n : ℤ)) p = 1

/-- Even inert prime set `𝒫_even^-(n) := {p ∈ 𝒫_even(n) \ {2} : (-q_n / p) = -1}`. -/
def PevenMinus (n : ℕ) : Finset ℕ :=
  (Peven n).filter fun p => 3 ≤ p ∧ jacobiSym (-(qn n : ℤ)) p = -1

/-- Weight `w'_p(n)` with `w'_2(n) = v_2(n!) - 2` and `w'_p(n) = v_p(n!)` for odd `p`. -/
def wpPrime (n p : ℕ) : ℕ :=
  if p = 2 then padicValNat 2 n.factorial - 2 else padicValNat p n.factorial

/-- Binary partition products `A(y)` and `B(y)` satisfying `A(y) B(y) = n!/4`. -/
def binaryProdA (n : ℕ) (y : ℕ → Bool) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (if y p then 0 else wpPrime n p)

def binaryProdB (n : ℕ) (y : ℕ → Bool) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (if y p then wpPrime n p else 0)

/-- Additive Legendre index `ℓ_p(a) ∈ ZMod 2` defined by `(-1)^{ℓ_p(a)} = (a / p)`. -/
def legendreBit (p : ℕ) (a : ℤ) : ZMod 2 :=
  if jacobiSym a p = 1 then 0 else 1

/-- Core factors `c₁(y_{ℒ₀})` and `c₂(y_{ℒ₀})` induced by Level-0 binary vector `y` on `ℒ₀(n)` and `y₂`. -/
def c2Level0 (n : ℕ) (y₂ : Bool) (y : ℕ → Bool) : ℕ :=
  (if 2 ∣ padicValNat 2 n.factorial ∨ ¬ y₂ then 1 else 2) *
    ∏ p ∈ layer2Adic n 0, if y p then p else 1

def c1Level0 (n : ℕ) (y₂ : Bool) (y : ℕ → Bool) : ℕ :=
  (if 2 ∣ padicValNat 2 n.factorial ∨ y₂ then 1 else 2) *
    ∏ p ∈ layer2Adic n 0, if y p then 1 else p

/-- Homogenous Level-0 kernel predicate `M_n^{(0)} y_{ℒ₀} = 0` over `𝔽₂` on `ℒ₀(n)`. -/
def InKernelM0 (n : ℕ) (y : ℕ → Bool) : Prop :=
  let c1 := c1Level0 n (y 2) y
  let c2 := c2Level0 n (y 2) y
  (∀ p ∈ layer2Adic n 0,
    (y p = false → jacobiSym (c2 : ℤ) p = 1) ∧
    (y p = true → jacobiSym (-(c1 : ℤ)) p = 1)) ∧
  (c2 % 8 = 1 ∨ c1 % 8 = 7) ∧
  (∀ q ∈ PevenPlus n, jacobiSym (c2 : ℤ) q = 1)

/-- Wilson quotient `W_p := ((p-1)! + 1)/p mod p`. -/
def wilsonQuot (p : ℕ) : ZMod p :=
  ((((p - 1).factorial + 1) / p : ℕ) : ZMod p)

/-- Harmonic sum `H_r := ∑_{j=1}^r j⁻¹ mod p`. -/
def harmonicMod (p r : ℕ) : ZMod p :=
  ∑ j ∈ Finset.Icc 1 r, (j : ZMod p)⁻¹

theorem lemma_5_3_i (n : ℕ) (hn : 6 ≤ n) :
    (∀ y : ℕ → Bool, binaryProdA n y * binaryProdB n y = n.factorial / 4) ∧
    (∀ m : ℕ, (0 < m ∧ n.factorial + 1 = m ^ 2) ↔
      ∃ y : ℕ → Bool,
        (∃ p ∈ (Finset.Icc 2 n).filter Nat.Prime, y p = true) ∧
        (∃ p ∈ (Finset.Icc 2 n).filter Nat.Prime, y p = false) ∧
        binaryProdB n y - binaryProdA n y = 1 ∧
        binaryProdA n y = (m - 1) / 2 ∧
        binaryProdB n y = (m + 1) / 2) ∧
    (∀ y : ℕ → Bool, binaryProdB n y - binaryProdA n y = 1 →
      InKernelM0 n y ∧
      (∀ q ∈ PevenMinus n,
        y q = decide (jacobiSym (c2Level0 n (y 2) y : ℤ) q = -1)) ∧
      (∀ p ∈ layer2Adic n 0,
        (y p = false →
          (∑ q ∈ (layer2Adic n 1 ∩ PevenPlus n),
            legendreBit p q * (if y q then (1 : ZMod 2) else 0)) =
          legendreBit p (∏ q ∈ (layer2Adic n 1 ∩ PevenMinus n),
            if y q then (1 : ℤ) else (q : ℤ)) +
            legendreBit p (c2Level0 n (y 2) y)) ∧
        (y p = true →
          (∑ q ∈ (layer2Adic n 1 ∩ PevenPlus n),
            legendreBit p q * (if y q then (1 : ZMod 2) else 0)) =
          legendreBit p (∏ q ∈ (layer2Adic n 1 ∩ PevenMinus n),
            if y q then (q : ℤ) else 1) +
            legendreBit p (-(c1Level0 n (y 2) y : ℤ))))) := by
  sorry

theorem lemma_5_3_ii (n : ℕ) (hn : 6 ≤ n) (y : ℕ → Bool)
    (hy : binaryProdB n y - binaryProdA n y = 1) :
    (∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ (n : ℝ) / 2 →
      let Np := n.factorial / (4 * p ^ padicValNat p n.factorial)
      ∑ ℓ ∈ ((Finset.Icc 2 n).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ p)),
        (wpPrime n ℓ : ZMod p) * fermatQuot p ℓ * (if y ℓ then 1 else 0) +
          fermatQuot p Np * (if y p then 1 else 0) = 0) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → (n : ℝ) / 3 < p → (p : ℝ) ≤ (n : ℝ) / 2 →
      (((n.factorial / p ^ 2 : ℕ) : ZMod (p ^ 2))) =
        2 * ((n - 2 * p).factorial : ZMod (p ^ 2)) *
          (1 + 2 * (p : ZMod (p ^ 2)) *
            (((harmonicMod p (n - 2 * p) - wilsonQuot p).val : ZMod (p ^ 2))))) := by
  sorry

/-- Explicit `𝔽₂` block matrix `ℳ_n^{(1)}` from Proposition 5.4 (with Audit Item 3 fix `-q_n/p_i`). -/
inductive Prop54Row (n : ℕ)
  | ramified (p : ℕ) (hp : p ∈ Podd n) (hp3 : 3 ≤ p)
  | splitEven (q : ℕ) (hq : q ∈ PevenPlus n)
  | mod4
  | mod8

def matrixM1Entry (n : ℕ) (r : Prop54Row n) (pj : ℕ) : ZMod 2 :=
  match r with
  | Prop54Row.ramified pi _ _ =>
      if pj = pi then legendreBit pi (-((qn n / pi : ℕ) : ℤ))
      else legendreBit pi pj
  | Prop54Row.splitEven q _ => legendreBit q pj
  | Prop54Row.mod4 => ((pj - 1) / 2 : ℕ)
  | Prop54Row.mod8 => ((pj ^ 2 - 1) / 8 : ℕ)

def applyM1 (n : ℕ) (x : ℕ → ZMod 2) (r : Prop54Row n) : ZMod 2 :=
  ∑ pj ∈ (Podd n).filter (3 ≤ ·), matrixM1Entry n r pj * x pj

def rhsBminus1 (n : ℕ) (r : Prop54Row n) : ZMod 2 :=
  match r with
  | Prop54Row.ramified pi _ _ => legendreBit pi (-1)
  | Prop54Row.splitEven q _ => legendreBit q (-1)
  | Prop54Row.mod4 => 1
  | Prop54Row.mod8 => 0

/-- Proposition 5.4 (Explicit `𝔽₂` block structure and all-ones duality).
Note (Audit Item 3): diagonal entries of the ramified block use `ℓ_{p_i}(-q_n / p_i)`
rather than `ℓ_{p_i}(-q_n^* / p_i)`, matching the true parity behavior when `2 ∤ v_2(n!)`. -/
theorem prop_5_4 (n m : ℕ) (hn : 8 ≤ n) (hsol : IsBrocardSol n m) :
    let u1 := (m - 1) / 2
    let u2 := (m + 1) / 2
    let δ₁s := oddPart (coreNat u1)
    let δ₂s := oddPart (coreNat u2)
    let x : ℕ → ZMod 2 := fun p => if p ∣ δ₂s then 1 else 0
    let xTilde : ℕ → ZMod 2 := fun p => 1 - x p
    (2 ^ (padicValNat 2 n.factorial - 2) ∣ u1 →
      ∀ r : Prop54Row n, applyM1 n x r = 0) ∧
    (2 ^ (padicValNat 2 n.factorial - 2) ∣ u2 →
      ∀ r : Prop54Row n, applyM1 n xTilde r = rhsBminus1 n r) ∧
    (2 ∣ padicValNat 2 n.factorial → qn n % 8 = 7 →
      ∀ r : Prop54Row n, applyM1 n (fun _ => 1) r = rhsBminus1 n r) := by
  sorry

theorem theorem_5_5_i (n : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6) :
    let _ : Fact (¬ IsSquare (qn n : ℚ)) := ⟨qn_rat_not_isSquare (by omega) hn6⟩
    let D := (fundDiscrQuad (qn n : ℤ)).natAbs
    ∃ (rank4_Cl_plus dim_ker_Rram : ℕ),
      dim_ker_Rram = 1 + rank4_Cl_plus ∧
      rank4_Cl_plus ≤ omegaNat D - 1 := by
  sorry

theorem theorem_5_5_ii (n m : ℕ) (hn : 8 ≤ n) (hsol : IsBrocardSol n m) :
    let u1 := (m - 1) / 2
    let u2 := (m + 1) / 2
    let δ₁ := coreNat u1
    let δ₂ := coreNat u2
    let z₁ := sqrtPartNat u1
    let z₂ := sqrtPartNat u2
    (∀ q ∈ PevenMinus n,
      (q ∣ z₁ ↔ jacobiSym (δ₂ : ℤ) q = 1) ∧
      (q ∣ z₂ ↔ jacobiSym (δ₂ : ℤ) q = -1)) ∧
    let AplusStar : ℕ := ∏ q ∈ PevenPlus n, q ^ padicValNat q n.factorial
    ∃ Btilde1 Btilde2 W1 W2 : ℕ,
      (W1 * W2) ^ 2 = AplusStar ∧
      Btilde2 * AplusStar = Btilde1 * W1 ^ 4 + W1 ^ 2 ∧
      (Btilde1 : ℤ) * (AplusStar : ℤ) = (Btilde2 : ℤ) * (W2 : ℤ) ^ 4 - (W2 : ℤ) ^ 2 := by
  sorry

end BrocardFormalization

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

This module translates Section 4 of the manuscript:
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
  sorry

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
  sorry

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

theorem theorem_4_2_i :
    (∀ n m : ℕ, (hn : 8 ≤ n) → (hn6 : n ≠ 6) →
      (hsol : IsBrocardSol n m) → pellIndex (by omega) hsol = 2 →
      let an := An n (by omega) hn6
      let bn := Bn n (by omega) hn6
      let zn := Zn n (by omega) hn6
      let c2 : ℝ := if X1 n (by omega) hn6 % 2 = 1 then -1 else 2 * Real.log 2 - 1
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
  sorry

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
        Bplus * Rn = Bminus * Zminus ^ 4 + (2 / c0) * Zminus ^ 2 ∧
        (Bminus : ℤ) * (Rn : ℤ) = (Bplus : ℤ) * (Zplus : ℤ) ^ 4 - (2 / (c0 : ℤ)) * (Zplus : ℤ) ^ 2 ∧
        (N₀ ≤ n → (Bplus * Rn) / Bminus = Zminus ^ 4 ∧
          Int.ceil ((Bminus : ℝ) * Rn / Bplus) = (Zplus ^ 4 : ℤ)) := by
  sorry

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
  sorry

/-! ### 4.2 Stickelberger Base-p Reciprocity and Conductor-Free Quadratic Residue Lock -/

theorem lemma_4_3 (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 1 ≤ n) :
    ((n.factorial / p ^ padicValNat p n.factorial : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ padicValNat p n.factorial *
        ∏ d ∈ (Nat.digits p n).toFinset, (d.factorial : ZMod p) ^ ((Nat.digits p n).count d) := by
  sorry

/-- Product form `(∏ j, (d_j(n)! : ZMod p))` matching `lemma_4_3` indexed by digit position. -/
theorem lemma_4_3_indexed (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 1 ≤ n) :
    ((n.factorial / p ^ padicValNat p n.factorial : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ padicValNat p n.factorial *
        ∏ j ∈ Finset.range (Nat.digits p n).length,
          (((Nat.digits p n).getD j 0).factorial : ZMod p) := by
  sorry

theorem theorem_4_4_i (n p : ℕ) (hn : 8 ≤ n) (hn6 : n ≠ 6)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hpeven : p ∈ Peven n) :
    jacobiSym (-(qn n : ℤ)) p =
      jacobiSym (-1 : ℤ) p *
        ∏ j ∈ Finset.range (Nat.digits p n).length,
          jacobiSym ((((Nat.digits p n).getD j 0).factorial : ℤ)) p ∧
    (∀ r : ℕ, 1 ≤ r → (n : ℝ) / (2 * r + 1) < p → (p : ℝ) ≤ (n : ℝ) / (2 * r) →
      jacobiSym (-(qn n : ℤ)) p =
        jacobiSym (-(((2 * r).factorial * (n - 2 * r * p).factorial : ℕ) : ℤ)) p ∧
      (p % 4 = 1 → ∀ m0 : ℕ, n - 2 * r * p = (p - 1) / 2 - m0 →
        jacobiSym (-(qn n : ℤ)) p =
          jacobiSym (((2 * r).factorial : ℤ)) p *
            (jacobiSym (2 : ℤ) p) ^ (m0 + 1) *
            ∏ j ∈ Finset.range m0, jacobiSym ((2 * j + 1 : ℤ)) p)) := by
  sorry

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
  sorry

end BrocardFormalization

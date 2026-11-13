/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import BrocardFormalization.ValuationParity
import BrocardFormalization.FundamentalRegimeK1
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Section 8: Harmonic Analysis on the CRT Torus and p-Adic Binomial Lifting

This module translates Section 8 of the manuscript:
* `crtModMn`, `crtBasisPhase`, `crtTorusDist`, `crtSum`: CRT torus setup (Eq. 8.1).
* `theorem_8_1_i`, `theorem_8_1_ii`, `theorem_8_1_iii`: CRT Partition of Unity, punctured torus
  discrepancy, universal torus projection law, and Zero-Dimensional Locked-Torus Collapse.
* `rieszCosine`, `theorem_8_2_i`, `theorem_8_2_ii`: Resonance-free `L^{2k}` Parseval identities
  for the Riesz product and simultaneous `p`-adic binomial series lift.
* `kappa4`, `theorem_8_3_i`, `theorem_8_3_ii`: Fourth-order subgaussian bounds, winding-branch
  decomposition, and Beurling–Selberg–Hölder `L^{2k}` arc bound (Audit Item 9: `H < M_n`).
* `theorem_8_4_i`, `theorem_8_4_ii`: External Wilson QR sieve at primes `q > n` and
  macroscopic independence of the Archimedean Taylor-remainder and primorial sieves.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 8.1 CRT Basis Phases, Partition of Unity, Projection, and Locked-Torus Collapse -/

/-- Half-factorial modulus `M_n := n! / 2`. -/
def crtModMn (n : ℕ) : ℕ := n.factorial / 2

/-- Exponents `w_p(n)`: `w_2(n) = v_2(n!) - 1` and `w_p(n) = v_p(n!)` for odd primes `p ≤ n`. -/
def crtExpW (n p : ℕ) : ℕ :=
  if p = 2 then padicValNat 2 n.factorial - 1 else padicValNat p n.factorial

/-- Prime-power component `q_p(n) := p^{w_p(n)}`. -/
def crtPrimePow (n p : ℕ) : ℕ := p ^ crtExpW n p

/-- Modular inverse `a_p(n) ∈ {1, …, q_p(n) - 1}` of `(M_n / q_p(n))` modulo `q_p(n)`. -/
def crtInvCoeff (n p : ℕ) : ℕ :=
  ((crtModMn n / crtPrimePow n p : ZMod (crtPrimePow n p))⁻¹).val

/-- CRT torus basis phase `θ_p(n) := a_p(n) / q_p(n) ∈ ℝ` (Eq. 8.1). -/
def crtBasisPhase (n p : ℕ) : ℝ :=
  (crtInvCoeff n p : ℝ) / (crtPrimePow n p : ℝ)

/-- Distance to the nearest integer `‖x‖_𝕋 := min_{z ∈ ℤ} |x - z| ∈ [0, 1/2]`. -/
def crtTorusDist (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

/-- Torus signed sum `Σ_n(ε) := ∑_{p ≤ n} ε_p θ_p(n)`. -/
def crtSum (n : ℕ) (ε : ℕ → ℤ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (ε p : ℝ) * crtBasisPhase n p

/-- Locked torus modulus `M_n^{locked}` and free split-even modulus `M_n^+` (8.4). -/
def crtMlocked (n : ℕ) : ℕ :=
  2 ^ (padicValNat 2 n.factorial - 1) *
    (∏ p ∈ (Podd n).filter (3 ≤ ·), p ^ padicValNat p n.factorial) *
    (∏ q ∈ PevenMinus n, q ^ padicValNat q n.factorial)

def crtMplus (n : ℕ) : ℕ :=
  ∏ q ∈ PevenPlus n, q ^ padicValNat q n.factorial

theorem theorem_8_1_i (n : ℕ) (hn : 4 ≤ n) :
    (Set.BijOn
      (fun ε : {p : ℕ // p ∈ (Finset.Icc 2 n).filter Nat.Prime} → Bool =>
        (⌊(crtModMn n : ℝ) * ∑ p : {p : ℕ // p ∈ (Finset.Icc 2 n).filter Nat.Prime},
          (if ε p then (1 : ℝ) else -1) * crtBasisPhase n p.1⌋ : ZMod (crtModMn n)))
      Set.univ
      {m : ZMod (crtModMn n) | m ^ 2 = 1}) ∧
    (∃ z : ℤ, ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, crtBasisPhase n p =
      (z : ℝ) + 2 / (n.factorial : ℝ)) ∧
    crtTorusDist (crtSum n (fun _ => 1)) = 2 / (n.factorial : ℝ) ∧
    crtTorusDist (crtSum n (fun _ => -1)) = 2 / (n.factorial : ℝ) ∧
    (∀ ε : ℕ → ℤ, (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = 1 ∨ ε p = -1) →
      ¬ (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = 1) →
      ¬ (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = -1) →
      ∃! kε : ℕ, 1 ≤ kε ∧
        crtTorusDist (crtSum n ε) = 2 * Real.sqrt (kε * n.factorial + 1) / (n.factorial : ℝ)) ∧
    ((∀ ε : ℕ → ℤ, (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = 1 ∨ ε p = -1) →
      ¬ (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = 1) →
      ¬ (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = -1) →
      2 * Real.sqrt (n.factorial + 1) / (n.factorial : ℝ) ≤ crtTorusDist (crtSum n ε)) ∧
      ((∃ ε : ℕ → ℤ, (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = 1 ∨ ε p = -1) →
        ¬ (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = 1) →
        ¬ (∀ p ∈ (Finset.Icc 2 n).filter Nat.Prime, ε p = -1) →
        crtTorusDist (crtSum n ε) = 2 * Real.sqrt (n.factorial + 1) / (n.factorial : ℝ)) ↔
      ∃ m : ℕ, IsBrocardSol n m)) := by
  sorry

theorem theorem_8_1_ii (n : ℕ) (hn : 4 ≤ n) :
    (∀ p : ℕ, p.Prime → p ≤ n + 1 →
      ∃ z : ℤ, ((n + 1 : ℝ)) * crtBasisPhase (n + 1) p =
        (if p ≤ n then crtBasisPhase n p else 0) + (z : ℝ)) ∧
    (∀ n₁ n₂ m₂ : ℕ, 4 ≤ n₁ → n₁ < n₂ → IsBrocardSol n₂ m₂ →
      ∀ p : ℕ, p.Prime → p ≤ n₂ →
        (∃ z : ℤ, ((n₂.factorial / n₁.factorial : ℕ) : ℝ) * crtBasisPhase n₂ p =
          (if p ≤ n₁ then crtBasisPhase n₁ p else 0) + (z : ℝ)) ∧
        (∃ z : ℤ, ∑ q ∈ (Finset.Icc 2 n₁).filter Nat.Prime,
          (if (q : ℤ) ∣ ((m₂ - 1 : ℕ) : ℤ) then (-1 : ℝ) else 1) * crtBasisPhase n₁ q =
            (m₂ : ℝ) / (crtModMn n₁ : ℝ) + (z : ℝ))) := by
  sorry

theorem theorem_8_1_iii :
    (∀ n : ℕ, 6 ≤ n → crtMlocked n * crtMplus n = crtModMn n) ∧
    IsBigOAtTop
      (fun n => Real.log ((crtMlocked n : ℝ) / Real.sqrt n.factorial) -
        ((1 / 2 : ℝ) * (1 + SigmaParityStar n) * n +
          ∑ q ∈ PevenMinus n, (padicValNat q n.factorial : ℝ) * Real.log q))
      (fun n => (n : ℝ) / Real.log n) ∧
    (∀ n m : ℕ, 8 ≤ n → IsBrocardSol n m → (crtMlocked n : ℝ) > Real.sqrt n.factorial + 1 →
      ∃ rlocked : ℕ, rlocked < crtMlocked n ∧
        m = rlocked ∧ (rlocked : ℝ) ≤ Real.sqrt n.factorial + 1 ∧
        rlocked ^ 2 ≡ 1 [MOD crtMplus n]) := by
  sorry

/-! ### 8.2 Exact Resonance-Free L^{2k} Parseval Identities and p-Adic Binomial Lift -/

/-- Fourier transform of the uniform CRT signed-sum measure: Riesz cosine product `μ̂_n(h)`. -/
def rieszCosine (n : ℕ) (h : ℤ) : ℝ :=
  ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.cos (2 * Real.pi * (h : ℝ) * crtBasisPhase n p)

/-- Minimum prime-power modulus `P_min(n) := min_{p ≤ n} p^{w_p(n)}`. -/
def Pmin (n : ℕ) : ℕ :=
  if h : 2 ≤ n then
    ((Finset.Icc 2 n).filter Nat.Prime).inf'
      ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, h⟩, Nat.prime_two⟩⟩
      (crtPrimePow n)
  else 1

/-- Truncated binomial series polynomial `∑_{j=0}^{R-1} binom(1/2, j) X^j` scaled by `4^R`? No, in `ℤ_p` / `mod (n!/4)^R`,
exact integer formula using `((1/2)_j / j!) (n!)^j = ((-1)^{j-1} ... / 4^j) (n!/4)^j` wait:
`binom(1/2, j) = ((-1)^{j-1} / (2j - 1) 4^j) binom(2j, j)` for `j ≥ 1`, wait `4^j` cancels `(n!/4)^j`?! No, `binom(1/2, j) * (n!)^j`!
Let's write `binomHalfInt j : ℚ` exact in `ℚ` and project to `ZMod ((n.factorial / 4) ^ R)`. -/
def binomHalfRat (j : ℕ) : ℚ :=
  (∏ i ∈ Finset.range j, ((1 / 2 : ℚ) - (i : ℚ))) / (j.factorial : ℚ)

theorem theorem_8_2_i (n : ℕ) (hn : 5 ≤ n) :
    (n : ℝ) / 2 < (Pmin n : ℝ) ∧
    (∀ k : ℕ, 1 ≤ k →
      (1 / (crtModMn n : ℝ)) * ∑ h ∈ Finset.range (crtModMn n), |rieszCosine n h| ^ (2 * k) =
        ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime,
          ((2 : ℝ) ^ (-(2 * (k : ℤ))) *
            ∑ j ∈ (Finset.Icc 0 (2 * k)).filter
                (fun j : ℕ => (2 * (j : ℤ) - 2 * k) % (crtPrimePow n p : ℤ) = 0),
              (Nat.choose (2 * k) j : ℝ))) ∧
    (∀ k : ℕ, 1 ≤ k → (k : ℝ) < (1 / 2 : ℝ) * (Pmin n : ℝ) →
      (1 / (crtModMn n : ℝ)) * ∑ h ∈ Finset.range (crtModMn n), |rieszCosine n h| ^ (2 * k) =
        ((2 : ℝ) ^ (-(2 * (k : ℤ))) * (Nat.choose (2 * k) k : ℝ)) ^ Nat.primeCounting n) := by
  sorry

theorem theorem_8_2_ii (n m : ℕ) (hn : 4 ≤ n) (hsol : IsBrocardSol n m) :
    (∀ p : ℕ, (hp : p.Prime) → p ≤ n →
      let _ : Fact p.Prime := ⟨hp⟩
      let εp : ℤ := if (p : ℤ) ∣ ((m - 1 : ℕ) : ℤ) then -1 else 1
      Tendsto (fun R : ℕ =>
        (m : ℤ_[p]) - (εp : ℤ_[p]) * ∑ j ∈ Finset.range R,
          ((binomHalfRat j * (n.factorial : ℚ) ^ j).num : ℤ_[p]) *
            Ring.inverse ((binomHalfRat j * (n.factorial : ℚ) ^ j).den : ℤ_[p]))
        atTop (𝓝 0)) ∧
    (∀ R : ℕ, 1 ≤ R →
      ∃ XR : ℤ,
        -(crtModMn n ^ R : ℤ) / 2 < XR ∧ XR ≤ (crtModMn n ^ R : ℤ) / 2 ∧
        ((m : ZMod ((n.factorial / 4) ^ R)) =
          (XR : ZMod ((n.factorial / 4) ^ R)) *
            ∑ j ∈ Finset.range R,
              (((binomHalfRat j * (n.factorial : ℚ) ^ j).num : ℤ) : ZMod ((n.factorial / 4) ^ R)) *
              (((binomHalfRat j * (n.factorial : ℚ) ^ j).den : ZMod ((n.factorial / 4) ^ R))⁻¹))) ∧
    (6 ≤ n →
      let X₂ : ℤ := (m : ℤ) * (1 - (n.factorial : ℤ) / 2)
      |X₂| < ((n.factorial / 4) ^ 2 : ℤ) / 2) := by
  sorry

/-! ### 8.3 Subgaussian Concentration, Winding-Branch Decomposition, and Uncertainty Barrier -/

/-- Fourth-order cumulant function `κ₄(u) := u^{-4} (u^2 / 2 - log cosh u)`. -/
def kappa4 (u : ℝ) : ℝ :=
  u ^ (-4 : ℤ) * ((1 / 2 : ℝ) * u ^ 2 - Real.log (Real.cosh u))

/-- Centered real lift `θ̃_p(n) ∈ (-1/2, 1/2]` of `θ_p(n)`. -/
def centeredTorusLift (n p : ℕ) : ℝ :=
  crtBasisPhase n p - (round (crtBasisPhase n p) : ℝ)

/-- Real signed sum `S_n(ε) := ∑_{p ≤ n} ε_p θ̃_p(n)`. -/
def crtSignedRealSum (n : ℕ) (ε : {p : ℕ // p ∈ (Finset.Icc 2 n).filter Nat.Prime} → Bool) : ℝ :=
  ∑ p, (if ε p then (1 : ℝ) else -1) * centeredTorusLift n p.1

/-- Number of sign vectors `ε ∈ {-1, 1}^{π(n)}` landing in `[-δ, δ] mod 1`: `𝒩_arc(n; δ)`. -/
def crtArcCount (n : ℕ) (δ : ℝ) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun ε : {p : ℕ // p ∈ (Finset.Icc 2 n).filter Nat.Prime} → Bool =>
    crtTorusDist (crtSignedRealSum n ε) ≤ δ)).card

theorem theorem_8_3_i :
    (StrictAntiOn kappa4 (Set.Ioi 0) ∧
      (∀ u : ℝ, 0 < u → 0 < kappa4 u) ∧
      Tendsto kappa4 (𝓝[>] 0) (𝓝 (1 / 12 : ℝ))) ∧
    (∀ n : ℕ, 5 ≤ n →
      let σ2 : ℝ := ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (centeredTorusLift n p) ^ 2
      let M4 : ℝ := ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (centeredTorusLift n p) ^ 4
      let Ln : ℤ := ⌊∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, |centeredTorusLift n p|⌋
      let δn : ℝ := 2 * Real.sqrt (n.factorial + 1) / (n.factorial : ℝ)
      let N : ℕ := (Finset.univ : Finset ({p : ℕ // p ∈ (Finset.Icc 2 n).filter Nat.Prime} → Bool)).card
      M4 ≥ σ2 ^ 2 / (Nat.primeCounting n : ℝ) ∧
      (∀ lam : ℝ, lam ≠ 0 →
        ((1 / (N : ℝ)) * ∑ ε, Real.exp (lam * crtSignedRealSum n ε)) ≤
          Real.exp ((1 / 2 : ℝ) * σ2 * lam ^ 2 - kappa4 (|lam| / 2) * M4 * lam ^ 4)) ∧
      (∀ ξ : ℝ, |ξ| < Real.pi →
        ‖(1 / (N : ℝ)) * ∑ ε, Complex.exp (Complex.I * ξ * crtSignedRealSum n ε)‖ ≤
          Real.exp (-(1 / 2 : ℝ) * σ2 * ξ ^ 2 - (1 / 12 : ℝ) * M4 * ξ ^ 4)) ∧
      (∀ Z₀ : ℝ, 0 < Z₀ →
        (∑ z ∈ (Finset.Icc (-Ln) Ln).filter (fun z : ℤ => Z₀ + δn ≤ |(z : ℝ)|),
          ((Finset.univ.filter (fun ε => |crtSignedRealSum n ε - (z : ℝ)| ≤ δn)).card : ℝ) / (N : ℝ)) ≤
          2 * Real.exp (-(Z₀ ^ 2) / (2 * σ2) - kappa4 (Z₀ / (2 * σ2)) * (M4 * Z₀ ^ 4 / σ2 ^ 8)))) := by
  sorry

/-- Theorem 8.3(ii): Beurling–Selberg–Hölder `L^{2k}` arc bound and trivial-solution barrier.
Note (Audit Item 9): Requires `H < crtModMn n` so `∑_{h=1}^H ≤ ∑_{h=0}^{M_n-1}` in Hölder's inequality. -/
theorem theorem_8_3_ii (n H k : ℕ) (hn : 5 ≤ n) (hH : 1 ≤ H) (hH_Mn : H < crtModMn n)
    (hk1 : 1 ≤ k) (hk2 : (k : ℝ) < (1 / 2 : ℝ) * (Pmin n : ℝ)) :
    let δn : ℝ := 2 * Real.sqrt (n.factorial + 1) / (n.factorial : ℝ)
    (crtArcCount n δn : ℝ) ≤
      (2 : ℝ) ^ Nat.primeCounting n * (2 * δn + 1 / ((H : ℝ) + 1)) +
      2 * (2 * δn + 1 / ((H : ℝ) + 1)) * (H : ℝ) ^ (1 - 1 / (2 * (k : ℝ))) *
        (crtModMn n : ℝ) ^ (1 / (2 * (k : ℝ))) *
        (((Nat.choose (2 * k) k : ℝ) ^ (1 / (2 * (k : ℝ)))) ^ Nat.primeCounting n) ∧
    (∀ h : ℤ, 2 * Real.pi * |(2 : ℝ) * h / (n.factorial : ℝ)| ≥ 0 → True) ∧
    ((crtArcCount n δn : ℝ) ≤
      (2 : ℝ) ^ Nat.primeCounting n *
        ((2 * δn + 1 / ((H : ℝ) + 1)) +
          2 * (2 * δn + 1 / ((H : ℝ) + 1)) *
            ∑ h ∈ Finset.Icc 1 H, |rieszCosine n h|)) := by
  sorry

/-- Theorem 8.4(i)–(ii): External Wilson QR sieve and macroscopic sieve independence. -/
theorem theorem_8_4_i (n m : ℕ) (hsol : IsBrocardSol n m) :
    (∀ d q : ℕ, q.Prime → q = n + d + 1 →
      let Wd : ℤ := (d.factorial : ℤ) * ((d.factorial : ℤ) - (-1 : ℤ) ^ d)
      jacobiSym Wd q = 0 ∨ jacobiSym Wd q = 1) ∧
    ((n + 1).Prime → (n + 1) ^ 2 ∣ n.factorial + 1) ∧
    ((n + 2).Prime → jacobiSym 2 (n + 2) = 1 → (n % 8 = 5 ∨ n % 8 = 7)) ∧
    ((n + 3).Prime → jacobiSym 2 (n + 3) = 1 → (n % 8 = 4 ∨ n % 8 = 6)) ∧
    ((n + 4).Prime → jacobiSym 42 (n + 4) = 0 ∨ jacobiSym 42 (n + 4) = 1) := by
  sorry

theorem theorem_8_4_ii (A : ℤ) (hA : A ≠ 0) (k : ℕ) (hk : 2 ≤ k) :
    let ηk : ℝ := max ((2 : ℝ) ^ (1 - (k : ℤ))) (1 / (2 * (k : ℝ) * ((k : ℝ) - 1)))
    let η'k : ℝ := ηk / (1 + ηk)
    ∀ δ : ℝ, 0 < δ → δ < η'k / 2 →
      ∃ Ck : ℝ, 0 < Ck ∧ ∃ C_err : ℝ, 0 < C_err ∧
        ∀ n : ℕ, 2 ≤ n →
          let Qn : ℕ := ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p
          let ρAk : ℝ :=
            (((Finset.range Qn).filter fun r : ℕ =>
              ((r : ℤ) ^ k - A) % (Qn : ℤ) = 0).card : ℝ) / (Qn : ℝ)
          ∀ X : ℕ, (Qn : ℝ) ^ (Ck / δ) ≤ (X : ℝ) →
            let S := (Finset.Icc 1 X).filter fun m : ℕ =>
              ((m : ℤ) ^ k - A) % (Qn : ℤ) = 0 ∧
              let val : ℝ := (m : ℝ) ^ k * Real.exp 1 - (A : ℝ) * Real.exp 1
              let frac : ℝ := val - (⌊val⌋ : ℝ)
              1 / ((n : ℝ) + 1) < frac ∧ frac < 1 / (n : ℝ)
            |(S.card : ℝ) - (X : ℝ) * ρAk / ((n : ℝ) * (n + 1))| ≤
              C_err * ((X : ℝ) * ρAk / ((n : ℝ) * (n + 1))) *
                ((n : ℝ) ^ 2 * (X : ℝ) ^ (-η'k + δ)) := by
  sorry

end BrocardFormalization

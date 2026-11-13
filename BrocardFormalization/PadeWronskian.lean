/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Section 7 & Theorem 1.3(ii): Support-Reduced Padé–Wronskian Approximations

This module translates Section 7 and Theorem 1.3(ii) of the manuscript:
* `lemma_7_1`: Initial `(m+1)`-variable Padé polynomials via Siegel's lemma (with Audit Item 7
  adjusting the `r`-exponent when `ε₀ > m/2` and `(D+1)` prefactor).
* `lemma_7_2`: Linear independence of `ω₀, …, ω_m` and monomial products `Ω_e` over `ℂ(x)`.
* `lemma_7_3_i`..`lemma_7_3_iii`: Support-reduced Wronskian non-vanishing `Δ_S ≠ 0`,
  support size bound `⌈m+1-ε₀⌉ ≤ s` (Audit Item 6 ceiling threshold), full column rank
  of `(P_{i_a}^k(α))`, and Gauss's Lemma multiplicity bound.
* `lemma_7_4_i`..`lemma_7_4_ii`: Leibniz derivative estimates (Audit Item 7) and
  factorial-root approximation at `x = 1/n₀`.
* `theorem_1_3_ii`: Unconditional `N^{6/7 + ε}` bound and monomial-product bounds for
  degree gaps `ν ≥ 3` (Tables 1 and 2).
* `theorem_7_5`: Unconditional finiteness for `n! + A = m^k` outside `n! + c^2 = m^2`.
-/

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 7.1 The (m+1)-Variable Binomial-Product Padé System and Siegel's Lemma -/

/-- Power series `(1 - j X)^{-1/r} = ∑_{u ≥ 0} (-1/r choose u) (-j X)^u ∈ ℚ⟦X⟧`. -/
def invRootLinearSeries (r j : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun u =>
    ((-1 : ℚ) / (r : ℚ)) ^ 0 *
      ((∏ i ∈ Finset.range u, ((-1 : ℚ) / (r : ℚ) - (i : ℚ))) / (u.factorial : ℚ)) *
      (-(j : ℚ)) ^ u

/-- Algebraic basis power series `ω₀ = 1` and `ω_i(x) = ∏_{j=1}^{β_i - 1} (1 - j x)^{-1/r}`. -/
def omegaSeries (r : ℕ) (β : ℕ → ℕ) (i : ℕ) : PowerSeries ℚ :=
  if i = 0 then 1
  else ∏ j ∈ Finset.Icc 1 (β i - 1), invRootLinearSeries r j

/-- Logarithmic derivative numerator `T A_i(x) ∈ ℚ[x]` and common denominator `T(x) = r ∏_{j=1}^M (1 - jx)`. -/
def padeT (r M : ℕ) : Polynomial ℤ :=
  Polynomial.C (r : ℤ) * ∏ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℤ) * Polynomial.X)

def padeTA (_r M : ℕ) (β : ℕ → ℕ) (i : ℕ) : Polynomial ℤ :=
  if i = 0 then 0
  else ∑ j ∈ Finset.Icc 1 (β i - 1),
    Polynomial.C (j : ℤ) *
      ∏ l ∈ (Finset.Icc 1 M).erase j, (1 - Polynomial.C (l : ℤ) * Polynomial.X)

/-- Differential iterate `P_i^{[k]}(x) := (T d/dx + T A_i)^k P_i(x) ∈ ℤ[x]` (7.7). -/
def padeIter (r M : ℕ) (β : ℕ → ℕ) (P : Polynomial ℤ) (i k : ℕ) : Polynomial ℤ :=
  Nat.iterate (fun Q => padeT r M * Polynomial.derivative Q + padeTA r M β i * Q) k P

/-- Normalized differential operator `P_i^k(x) ∈ ℚ[x]` via exact recurrence
`(k+1) P_i^{k+1} = T (P_i^k)' + (T A_i - k T') P_i^k`. -/
def padeNormIter (r M : ℕ) (β : ℕ → ℕ) (P : Polynomial ℤ) (i : ℕ) : ℕ → Polynomial ℚ
  | 0 => P.map (Int.castRingHom ℚ)
  | k + 1 =>
      let prev := padeNormIter r M β P i k
      let tq := (padeT r M).map (Int.castRingHom ℚ)
      let taq := (padeTA r M β i).map (Int.castRingHom ℚ)
      Polynomial.C (1 / ((k + 1 : ℕ) : ℚ)) *
        (tq * Polynomial.derivative prev + (taq - Polynomial.C (k : ℚ) * Polynomial.derivative tq) * prev)

/-- Initial `(m+1)`-variable Padé polynomials via Siegel's Lemma (Lemma 7.1).
Note (Audit Item 7): When `ε₀ > m / 2`, the `r`-power `(r^{2O})^{(m-ε₀)/ε₀ + 1}` uses base
`r^{2m/(m-ε₀)}` rather than `r^4`, and `|r_v|` includes the Cauchy-product factor `m(D+1)`. -/
theorem lemma_7_1 (r m M D : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m) (hD : 10 * m ≤ D)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < (m : ℝ) - 1)
    (β : ℕ → ℕ) (hβ0 : β 0 = 0)
    (hβmono : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ m → β i < β j)
    (hβlo : r ≤ β 1) (hβhi : β m ≤ M) (hβdvd : ∀ i, 1 ≤ i → i ≤ m → r ∣ β i) :
    let O : ℕ := ⌊((m : ℝ) + 1 - ε₀) * (D : ℝ)⌋₊
    ∃ P : Fin (m + 1) → Polynomial ℤ,
      (∀ i, (P i).natDegree ≤ D) ∧
      (∃ i, P i ≠ 0) ∧
      let R : PowerSeries ℚ :=
        ∑ i : Fin (m + 1),
          ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) * omegaSeries r β i.1
      (∀ v : ℕ, v ≤ O → PowerSeries.coeff v R = 0) ∧
      (∀ (i : Fin (m + 1)) (k : ℕ), k ≤ D →
        (|(P i).coeff k| : ℝ) ≤
          (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) *
            ((2 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
              (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀ * (D : ℝ)))) ∧
      (∀ v : ℕ, O < v →
        |PowerSeries.coeff v R| ≤
          (m * (D + 1) : ℝ) * (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) *
            ((2 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
              (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀ * (D : ℝ))) *
            (2 * (M : ℝ)) ^ v) := by
  sorry

/-! ### 7.2 Puiseux Linear Independence, Support-Reduced Wronskian, and Gauss's Lemma -/

theorem lemma_7_2 (r d E : ℕ) (hr : 2 ≤ r) (hd : 1 ≤ d) (hE1 : 1 ≤ E) (hEr : E ≤ r - 1)
    (β : ℕ → ℕ) (hβmono : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ d → β i < β j)
    (hβlo : r ≤ β 1) (hβdvd : ∀ i, 1 ≤ i → i ≤ d → r ∣ β i) :
    let exps := (Finset.univ : Finset (Fin d → Fin (E + 1))).filter
      (fun e => (∑ i : Fin d, (e i).1) ≤ E)
    (∀ U : (Fin d → Fin (E + 1)) → Polynomial ℂ,
      (∑ e ∈ exps, (U e : PowerSeries ℂ) *
        ∏ i : Fin d, (PowerSeries.map (algebraMap ℚ ℂ) (omegaSeries r β (i.1 + 1))) ^ (e i).1) = 0 →
      ∀ e ∈ exps, U e = 0) ∧
    (exps.card = Nat.choose (d + E) d) ∧
    (∀ U : Fin (d + 1) → Polynomial ℂ,
      (∑ i : Fin (d + 1), (U i : PowerSeries ℂ) *
        PowerSeries.map (algebraMap ℚ ℂ) (omegaSeries r β i.1)) = 0 →
      ∀ i : Fin (d + 1), U i = 0) := by
  sorry

/-- Non-zero support `S := {0 ≤ i ≤ m : P i ≠ 0}` as an ordered list `i₁ < ⋯ < i_s`. -/
def nonZeroSupportList {m : ℕ} (P : Fin (m + 1) → Polynomial ℤ) : List ℕ :=
  (List.range (m + 1)).filter fun i =>
    open Classical in if h : i < m + 1 then decide (P ⟨i, h⟩ ≠ 0) else false

/-- Support-reduced `s × s` Wronskian matrix `(P_{i_a}^{[k]}(x))_{0 ≤ k < s, 0 ≤ a < s}`. -/
def supportWronskianMatrix (r M m : ℕ) (β : ℕ → ℕ) (P : Fin (m + 1) → Polynomial ℤ) :
    Matrix (Fin (nonZeroSupportList P).length) (Fin (nonZeroSupportList P).length) (Polynomial ℤ) :=
  let S := nonZeroSupportList P
  Matrix.of fun k a =>
    let idx := S[a.1]'a.2
    have hidx : idx < m + 1 := by
      have hm := List.mem_filter.mp (List.getElem_mem a.2)
      exact List.mem_range.mp hm.1
    padeIter r M β (P ⟨idx, hidx⟩) idx k.1

theorem lemma_7_3_i (r m M D : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < (m : ℝ) - 1)
    (β : ℕ → ℕ) (hβ0 : β 0 = 0)
    (hβmono : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ m → β i < β j)
    (hβlo : r ≤ β 1) (hβhi : β m ≤ M) (hβdvd : ∀ i, 1 ≤ i → i ≤ m → r ∣ β i)
    (P : Fin (m + 1) → Polynomial ℤ) (hPdeg : ∀ i, (P i).natDegree ≤ D) (hPnz : ∃ i, P i ≠ 0)
    (hRord : ∀ v ≤ ⌊((m : ℝ) + 1 - ε₀) * (D : ℝ)⌋₊,
      PowerSeries.coeff v (∑ i : Fin (m + 1),
        ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) * omegaSeries r β i.1) = 0)
    -- Audit Item 6 sharp ceiling threshold:
    (hD_thresh : ((m + 1 : ℝ) ^ 2 * M < D) ∧
      (Int.fract ((m : ℝ) + 1 - ε₀) ≠ 0 →
        (((Nat.choose (m + 1) 2 : ℝ) * M + m + 1) / Int.fract ((m : ℝ) + 1 - ε₀) < D))) :
    let ΔS := (supportWronskianMatrix r M m β P).det
    let s := (nonZeroSupportList P).length
    let O := ⌊((m : ℝ) + 1 - ε₀) * (D : ℝ)⌋₊
    ΔS ≠ 0 ∧
    ΔS.natDegree ≤ s * D + Nat.choose s 2 * M ∧
    O - (s - 1) ≤ ΔS.rootMultiplicity 0 ∧
    Nat.ceil ((m : ℝ) + 1 - ε₀) ≤ s ∧ s ≤ m + 1 ∧ 2 ≤ s ∧
    ((ΔS.natDegree : ℝ) - (ΔS.rootMultiplicity 0 : ℝ) ≤
      ((s : ℝ) - ((m : ℝ) + 1 - ε₀)) * D + (Nat.choose s 2 : ℝ) * M + s) := by
  sorry

theorem lemma_7_3_ii (r m M D : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (β : ℕ → ℕ) (hβ0 : β 0 = 0) (hβhi : β m ≤ M)
    (P : Fin (m + 1) → Polynomial ℤ) (n₀ : ℕ) (hn₀ : M < n₀)
    (hΔnz : (supportWronskianMatrix r M m β P).det ≠ 0) :
    let ΔS := (supportWronskianMatrix r M m β P).det
    let S := nonZeroSupportList P
    let s := S.length
    let a := (ΔS.map (Int.castRingHom ℚ)).rootMultiplicity (1 / (n₀ : ℚ))
    Matrix.rank (Matrix.of (fun (k : Fin (a + s)) (j : Fin s) =>
      let idx := S[j.1]'j.2
      have hidx : idx < m + 1 := by
        have hm' := List.mem_filter.mp (List.getElem_mem j.2)
        exact List.mem_range.mp hm'.1
      (padeNormIter r M β (P ⟨idx, hidx⟩) idx k.1).eval (1 / (n₀ : ℚ)))) = s := by
  sorry

theorem lemma_7_3_iii (r m M D : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m) (hD : 10 * m ≤ D)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < (m : ℝ) - 1)
    (β : ℕ → ℕ) (hβ0 : β 0 = 0) (hβhi : β m ≤ M)
    (P : Fin (m + 1) → Polynomial ℤ)
    (hPdeg : ∀ i, (P i).natDegree ≤ D)
    (hPbd : ∀ i k, (|(P i).coeff k| : ℝ) ≤
      (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) *
        ((2 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
          (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀ * (D : ℝ))))
    (hΔnz : (supportWronskianMatrix r M m β P).det ≠ 0)
    (N t : ℕ) (hN : 2 ≤ N) (nseq : Fin t → ℕ)
    (hnseq_lo : ∀ j, N ≤ nseq j) (hnseq_hi : ∀ j, nseq j < 2 * N)
    (hstrict : StrictMono nseq) :
    let ΔS := (supportWronskianMatrix r M m β P).det
    let S := nonZeroSupportList P
    let s := S.length
    let a := fun j : Fin t => (ΔS.map (Int.castRingHom ℚ)).rootMultiplicity (1 / (nseq j : ℚ))
    (∏ j : Fin t, (Polynomial.C (nseq j : ℤ) * Polynomial.X - 1) ^ a j) ∣ ΔS ∧
    (∏ j : Fin t, (nseq j : ℤ) ^ a j) ∣ ΔS.leadingCoeff ∧
    ∃ Cm : ℝ, 0 < Cm ∧
      (∑ j : Fin t, (a j : ℝ)) ≤
        (s : ℝ) * (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀) *
          (Real.log M / Real.log N) * D +
          Cm * (((D : ℝ) + M * Real.log N) / Real.log N) := by
  sorry

/-- Lemma 7.4(i)–(ii): Leibniz derivative estimates (Audit Item 7) and factorial-root approximation. -/
theorem lemma_7_4_i (r m M D : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m) (hD : 10 * m ≤ D)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < (m : ℝ) - 1)
    (β : ℕ → ℕ) (hβ0 : β 0 = 0) (hβhi : β m ≤ M)
    (P : Fin (m + 1) → Polynomial ℤ) (hPdeg : ∀ i, (P i).natDegree ≤ D)
    (Rcoeff : ℕ → ℚ)
    (hRdef : ∀ v, Rcoeff v = PowerSeries.coeff v (∑ i : Fin (m + 1),
      ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) * omegaSeries r β i.1))
    (hRvan : ∀ v ≤ ⌊((m : ℝ) + 1 - ε₀) * (D : ℝ)⌋₊, Rcoeff v = 0)
    (hPbd : ∀ i k, (|(P i).coeff k| : ℝ) ≤
      (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) *
        ((2 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
          (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀ * (D : ℝ))))
    (hRbd : ∀ v > ⌊((m : ℝ) + 1 - ε₀) * (D : ℝ)⌋₊, |Rcoeff v| ≤
      (m * (D + 1) : ℝ) * (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) *
        ((2 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
          (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀ * (D : ℝ))) *
        (2 * (M : ℝ)) ^ v)
    (N n₀ a s : ℕ) (hn₀_lo : N ≤ n₀) (hn₀_hi : n₀ < 2 * N) (hn₀_M : 8 * M < n₀) (hN : 8 * M < N) :
    let U : ℝ := (2 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
      (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀)
    let W : ℝ := (N : ℝ) ^ ((m : ℝ) + 1 - ε₀) *
      (8 * (m : ℝ) * (r : ℝ) ^ (2 * (m : ℝ) / ((m : ℝ) - ε₀)) * (M : ℝ)) ^
        (-((m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀))
    let Z : ℤ := (r : ℤ) ^ (a + s) * (n₀ : ℤ) ^ (D + (a + s) * M)
    ∃ u w : ℝ,
      u = ((m * (D + 1) : ℝ) * (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) * (4 * (r : ℝ) * N) ^ ((a + s) * M + a + s)) ∧
      w = ((m * (D + 1) : ℝ) * (4 : ℝ) ^ ((m : ℝ) / ε₀ * M) * (4 * (r : ℝ) * N) ^ (2 * ((a + s) * M + a + s))) ∧
      ∀ k ≤ a + s - 1,
        (∀ i : Fin (m + 1),
          ∃ z_int : ℤ, (Z : ℚ) * (padeNormIter r M β (P i) i.1 k).eval (1 / (n₀ : ℚ)) = z_int ∧
          |(((padeNormIter r M β (P i) i.1 k).eval (1 / (n₀ : ℚ)) : ℚ) : ℝ)| ≤ u * U ^ D) ∧
        |∑ i : Fin (m + 1),
          (((padeNormIter r M β (P i) i.1 k).eval (1 / (n₀ : ℚ)) : ℚ) : ℝ) *
            (∏ j ∈ Finset.Icc 1 (β i - 1), (1 - (j : ℝ) / n₀) ^ (-1 / (r : ℝ)))| ≤
          w * W ^ (-(D : ℤ)) := by
  sorry

theorem lemma_7_4_ii (P : Polynomial ℤ) (r ν s d E : ℕ)
    (hr : 2 ≤ r) (hdeg : P.natDegree = r) (har : 0 < P.leadingCoeff) (hs : 0 < s)
    (hdep : P.coeff (r - 1) = 0)
    (hgap : ν = r - (P - Polynomial.C P.leadingCoeff * Polynomial.X ^ r).natDegree)
    (hν2 : 2 ≤ ν) (hνr : ν ≤ r) (hd : 1 ≤ d) (hE : E ≤ min (r - 1) (ν - 1))
    (β : ℕ → ℕ) (hβdvd : ∀ i, 1 ≤ i → i ≤ d → r ∣ β i) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ,
      ∀ (M n₀ : ℕ) (x₀ : ℕ) (x : Fin d → ℕ),
        M₀ ≤ M → 2 * M < n₀ → (∀ i : Fin d, 1 ≤ i.1 + 1 → β (i.1 + 1) ≤ M) →
        (s : ℤ) * (n₀.factorial : ℤ) = P.eval (x₀ : ℤ) →
        (∀ i : Fin d, (s : ℤ) * ((n₀ - β (i.1 + 1)).factorial : ℤ) = P.eval (x i : ℤ)) →
        0 < x₀ →
        ∀ e : Fin d → ℕ, (∑ i : Fin d, e i) ≤ E →
          let qe : ℕ := x₀ ^ (E - ∑ i : Fin d, e i) *
            ∏ i : Fin d, (n₀ ^ (β (i.1 + 1) / r) * x i) ^ e i
          |∏ i : Fin d, (∏ j ∈ Finset.Icc 1 (β (i.1 + 1) - 1),
              (1 - (j : ℝ) / n₀) ^ (-1 / (r : ℝ))) ^ e i -
            (qe : ℝ) / (x₀ : ℝ) ^ E| ≤ C * (M : ℝ) ^ E * (x₀ : ℝ) ^ (-(ν : ℤ)) := by
  sorry

/-! ### 7.3 Main Theorem 1.3(ii) and Section 7.4 Unconditional Finiteness -/

/-- Exact optimal power-saving exponent `θ_{d,E,ν}^*(ε₀)` from (7.19). -/
def thetaFormula (d E ν m : ℕ) (ε₀ : ℝ) : ℝ :=
  min ((ε₀ * (((ν : ℝ) - E) * (m - ε₀) - E)) / ((m + 1 - ε₀) * (ν * m - E * ε₀)))
      (1 / ((d : ℝ) + 2))

theorem theorem_1_3_ii (P : Polynomial ℤ) (s : ℤ) (hs : s ≠ 0) (hr : 2 ≤ P.natDegree) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (polyFactorialCount P s N : ℝ) ≤ C * (N : ℝ) ^ ((6 : ℝ) / 7 + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (brocardCount N : ℝ) ≤ C * (N : ℝ) ^ ((6 : ℝ) / 7 + ε)) ∧
    -- Degree-gap refinement after depressing `x^{r-1}`:
    (∀ (Pdep : Polynomial ℤ) (sdep : ℤ), sdep ≠ 0 → Pdep.natDegree = P.natDegree →
      Pdep.coeff (Pdep.natDegree - 1) = 0 →
      (∀ N, polyFactorialCount P s N ≤ polyFactorialCount Pdep sdep N) →
      let r := Pdep.natDegree
      let ν := r - (Pdep - Polynomial.C Pdep.leadingCoeff * Polynomial.X ^ r).natDegree
      3 ≤ r → 3 ≤ ν →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        (ν = 3 → (polyFactorialCount P s N : ℝ) ≤ C * (N : ℝ) ^ ((5 : ℝ) / 6 + ε)) ∧
        (ν = 4 → (polyFactorialCount P s N : ℝ) ≤ C * (N : ℝ) ^ ((4 : ℝ) / 5 + ε)) ∧
        (6 ≤ ν → (polyFactorialCount P s N : ℝ) ≤ C * (N : ℝ) ^ ((3 : ℝ) / 4 + ε)) ∧
        (∀ E : ℕ, 1 ≤ E → E ≤ min (r - 1) (ν - 1) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < (E : ℝ) - 1 →
            ((polyFactorialCount P s N : ℝ) ≤
              C * (N : ℝ) ^ (1 - thetaFormula 1 E ν E ε₀ + ε)))) := by
  sorry

theorem theorem_7_5 (A : ℤ) (k : ℕ) (hA : A ≠ 0) (hk : 2 ≤ k)
    (h_not_sq : k ≥ 3 ∨ ¬ ∃ c : ℤ, A = c ^ 2) :
    ∃ N₀ : ℕ, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      (n.factorial : ℤ) + A = (m : ℤ) ^ k → n ≤ N₀ := by
  sorry

end BrocardFormalization

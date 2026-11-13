/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# Foundational Definitions and Notation for the Brocard–Ramanujan Formalization

This module implements the foundational definitions and notation from Sections 1.1–1.4
and Equations (2.1)–(2.3) of the manuscript:
* `IsBrocardSol`, `polyFactorialCount`, `brocardCount` (Equations 1.1–1.2)
* `coreNat`, `radNat`, `omegaNat`, `largestPrimeFactor`, `oddPart`, `ePhase` (Section 1.4)
* `Podd`, `Peven`, `qn`, `sn` and the canonical square-free/square factorization
  `n! = qn n * (sn n)^2` (Equation 1.4)
* `Sodd`, `Seven`, `DeltaParity`, `SigmaParity`, `SigmaParityStar` (Equations 2.1–2.3)
-/

noncomputable section

open scoped BigOperators

namespace BrocardFormalization

/-! ### Equations (1.1)–(1.2): Brocard–Ramanujan Equation and Counting Functions -/

/-- Positive integer solution `(n, m)` to the Brocard–Ramanujan equation `n! + 1 = m^2` (1.1). -/
def IsBrocardSol (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ n.factorial + 1 = m ^ 2

/-- Counting function `𝒩_{P,s}(N) := #{1 ≤ n ≤ N : ∃ x ∈ ℤ, s · n! = P(x)}` (1.2). -/
def polyFactorialCount (P : Polynomial ℤ) (s : ℤ) (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.Icc 1 N).filter fun n => ∃ x : ℤ, s * (n.factorial : ℤ) = P.eval x).card

/-- Brocard counting function `𝒩_Brocard(N) := 𝒩_{x^2 - 1, 1}(N)` (1.2). -/
def brocardCount (N : ℕ) : ℕ :=
  polyFactorialCount (Polynomial.X ^ 2 - 1) 1 N

theorem brocardCount_eq_sol_count (N : ℕ) :
    brocardCount N =
      open Classical in
      ((Finset.Icc 1 N).filter fun n => ∃ m : ℕ, IsBrocardSol n m).card := by
  classical
  unfold brocardCount polyFactorialCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, one_mul]
  refine and_congr_right fun hn => ?_
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.natAbs, hn.1, ?_, ?_⟩
    · by_contra h0
      have hx0 : x = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_not_pos h0)
      subst hx0
      have : (n.factorial : ℤ) ≥ 1 := by exact_mod_cast Nat.factorial_pos n
      omega
    · have hsq : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by simp [sq_abs]
      have hfac : (n.factorial : ℤ) + 1 = (x.natAbs : ℤ) ^ 2 := by linarith
      exact_mod_cast hfac
  · rintro ⟨m, _, _, hm⟩
    refine ⟨(m : ℤ), ?_⟩
    have hfac : (n.factorial : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hm
    linarith

/-! ### Section 1.4: Arithmetic Invariants and Notation -/

/-- Square-free core `core(A) := ∏_{2 ∤ v_p(A)} p`. -/
def coreNat (A : ℕ) : ℕ :=
  ∏ p ∈ A.primeFactors with ¬ 2 ∣ padicValNat p A, p

/-- Square part `s(A) := ∏_p p^{⌊v_p(A)/2⌋}`. -/
def sqrtPartNat (A : ℕ) : ℕ :=
  ∏ p ∈ A.primeFactors, p ^ (padicValNat p A / 2)

/-- Radical `rad(A) := ∏_{p ∣ A} p`. -/
def radNat (A : ℕ) : ℕ :=
  ∏ p ∈ A.primeFactors, p

/-- Number of distinct prime factors `ω(A) := ∑_{p ∣ A} 1`. -/
def omegaNat (A : ℕ) : ℕ :=
  A.primeFactors.card

/-- Largest prime factor `P⁺(A)` (returns `0` if `A ≤ 1`). -/
def largestPrimeFactor (A : ℕ) : ℕ :=
  A.primeFactors.sup id

/-- Odd part `A* := A / 2^{v_2(A)}`. -/
def oddPart (A : ℕ) : ℕ :=
  A / 2 ^ padicValNat 2 A

/-- Complex exponential `e(t) := e^{2π i t}`. -/
def ePhase (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * t)

theorem coreNat_mul_sqrtPart_sq {A : ℕ} (hA : A ≠ 0) :
    A = coreNat A * (sqrtPartNat A) ^ 2 := by
  unfold coreNat sqrtPartNat
  rw [← Finset.prod_pow]
  have hprod : ∏ p ∈ A.primeFactors, p ^ padicValNat p A = A := by
    calc
      ∏ p ∈ A.primeFactors, p ^ padicValNat p A
          = ∏ p ∈ A.primeFactors, p ^ A.factorization p := by
            refine Finset.prod_congr rfl fun p hp => ?_
            rw [Nat.factorization_def A (Nat.prime_of_mem_primeFactors hp)]
      _ = A := (Nat.prod_primeFactors_pow_factorization hA).symm
  conv_lhs => rw [← hprod]
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hodd : 2 ∣ padicValNat p A
  · simp [hodd]
    rw [← pow_mul]
    congr 1
    obtain ⟨k, hk⟩ := hodd
    omega
  · simp [hodd]
    rw [← pow_mul, ← pow_succ']
    congr 1
    have hmod : padicValNat p A % 2 = 1 :=
      Nat.mod_two_ne_zero.mp (fun h => hodd (Nat.dvd_of_mod_eq_zero h))
    omega

private lemma squarefree_prod_of_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq' : q.Prime := hs q hq
      exact (Nat.coprime_primes hp hq').mpr (fun h => hps (h ▸ hq))
    exact Nat.squarefree_mul hcop |>.mpr ⟨hp.squarefree, ih hs⟩

theorem squarefree_coreNat {A : ℕ} : Squarefree (coreNat A) := by
  unfold coreNat
  refine squarefree_prod_of_primes fun p hp => ?_
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem coreNat_pos {A : ℕ} : 0 < coreNat A := by
  unfold coreNat
  refine Finset.prod_pos fun p hp => ?_
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem sqrtPartNat_pos (A : ℕ) : 0 < sqrtPartNat A := by
  unfold sqrtPartNat
  refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

/-! ### Equation (1.4): Factorial Prime Sets and Canonical Factorization -/

/-- Odd-valuation prime set `𝒫_odd(n) := {p ≤ n : p prime, 2 ∤ v_p(n!)}`. -/
def Podd (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n.factorial

/-- Even-valuation prime set `𝒫_even(n) := {p ≤ n : p prime, 2 ∣ v_p(n!)}`. -/
def Peven (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun p => p.Prime ∧ 2 ∣ padicValNat p n.factorial

/-- Square-free core of `n!`: `q_n := core(n!)`. -/
def qn (n : ℕ) : ℕ := coreNat n.factorial

/-- Square part of `n!`: `s_n := ∏_{p ≤ n} p^{⌊v_p(n!)/2⌋}`. -/
def sn (n : ℕ) : ℕ := sqrtPartNat n.factorial

lemma mem_primeFactors_factorial_iff {n p : ℕ} :
    p ∈ n.factorial.primeFactors ↔ p.Prime ∧ p ≤ n := by
  rw [Nat.mem_primeFactors_of_ne_zero (Nat.factorial_ne_zero n)]
  exact and_congr_right fun hp => hp.dvd_factorial

theorem qn_eq_prod_Podd (n : ℕ) : qn n = ∏ p ∈ Podd n, p := by
  unfold qn coreNat Podd
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, mem_primeFactors_factorial_iff]
  constructor
  · rintro ⟨⟨hp, hpn⟩, hodd⟩
    exact ⟨⟨hp.two_le, hpn⟩, hp, hodd⟩
  · rintro ⟨⟨_, hpn⟩, hp, hodd⟩
    exact ⟨⟨hp, hpn⟩, hodd⟩

theorem sn_eq_prod_primes (n : ℕ) :
    sn n = ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (padicValNat p n.factorial / 2) := by
  unfold sn sqrtPartNat
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, mem_primeFactors_factorial_iff]
  constructor
  · rintro ⟨hp, hpn⟩
    exact ⟨⟨hp.two_le, hpn⟩, hp⟩
  · rintro ⟨⟨_, hpn⟩, hp⟩
    exact ⟨hp, hpn⟩

theorem factorial_eq_qn_mul_sn_sq (n : ℕ) : n.factorial = qn n * (sn n) ^ 2 :=
  coreNat_mul_sqrtPart_sq (Nat.factorial_ne_zero n)

theorem squarefree_qn (n : ℕ) : Squarefree (qn n) :=
  squarefree_coreNat

theorem qn_pos (n : ℕ) : 0 < qn n :=
  coreNat_pos

theorem sn_pos (n : ℕ) : 0 < sn n :=
  sqrtPartNat_pos n.factorial

theorem Podd_disjoint_Peven (n : ℕ) : Disjoint (Podd n) (Peven n) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [Podd, Peven, Finset.mem_filter] at hp1 hp2
  exact hp1.2.2 hp2.2.2

theorem Podd_union_Peven (n : ℕ) :
    Podd n ∪ Peven n = (Finset.Icc 2 n).filter Nat.Prime := by
  ext p
  simp only [Podd, Peven, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-! ### Equations (2.1)–(2.3): Valuation-Parity Weights and Series -/

/-- Odd-valuation prime weight `S_odd(n) := ∑_{3 ≤ p ≤ n, p ∈ 𝒫_odd(n)} v_p(n!) log p` (2.1). -/
def Sodd (n : ℕ) : ℝ :=
  ∑ p ∈ (Podd n).filter (3 ≤ ·), (padicValNat p n.factorial : ℝ) * Real.log p

/-- Even-valuation prime weight `S_even(n) := ∑_{3 ≤ p ≤ n, p ∈ 𝒫_even(n)} v_p(n!) log p` (2.1). -/
def Seven (n : ℕ) : ℝ :=
  ∑ p ∈ (Peven n).filter (3 ≤ ·), (padicValNat p n.factorial : ℝ) * Real.log p

/-- Parity discrepancy `Δ_parity(n) := S_even(n) - S_odd(n)` (2.2). -/
def DeltaParity (n : ℕ) : ℝ :=
  Seven n - Sodd n

theorem DeltaParity_eq_sum (n : ℕ) :
    DeltaParity n =
      ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime,
        (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p := by
  unfold DeltaParity Seven Sodd
  have hdisj : Disjoint ((Peven n).filter (3 ≤ ·)) ((Podd n).filter (3 ≤ ·)) :=
    (Podd_disjoint_Peven n).symm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hunion :
      (Peven n).filter (3 ≤ ·) ∪ (Podd n).filter (3 ≤ ·) =
        (Finset.Icc 3 n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Peven, Podd]
    constructor
    · rintro (⟨⟨⟨_, hpn⟩, hp, _⟩, hp3⟩ | ⟨⟨⟨_, hpn⟩, hp, _⟩, hp3⟩) <;> exact ⟨⟨hp3, hpn⟩, hp⟩
    · rintro ⟨⟨hp3, hpn⟩, hp⟩
      by_cases hd : 2 ∣ padicValNat p n.factorial
      · exact Or.inl ⟨⟨⟨by omega, hpn⟩, hp, hd⟩, hp3⟩
      · exact Or.inr ⟨⟨⟨by omega, hpn⟩, hp, hd⟩, hp3⟩
  have hEven :
      ∑ p ∈ (Peven n).filter (3 ≤ ·), (padicValNat p n.factorial : ℝ) * Real.log p =
        ∑ p ∈ (Peven n).filter (3 ≤ ·),
          (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have he : 2 ∣ padicValNat p n.factorial :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    rw [Even.neg_one_pow (even_iff_two_dvd.mpr he), one_mul]
  have hOdd :
      ∑ p ∈ (Podd n).filter (3 ≤ ·), (padicValNat p n.factorial : ℝ) * Real.log p =
        - ∑ p ∈ (Podd n).filter (3 ≤ ·),
            (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have ho : ¬ 2 ∣ padicValNat p n.factorial :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    have hodd : Odd (padicValNat p n.factorial) :=
      Nat.not_even_iff_odd.mp (fun h => ho (even_iff_two_dvd.mp h))
    rw [Odd.neg_one_pow hodd]
    ring
  rw [hEven, hOdd, sub_neg_eq_add, ← Finset.sum_union hdisj, hunion]

/-- Small-prime valuation-parity series `Σ_parity(n; B)` (2.3). -/
def SigmaParity (n : ℕ) (B : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 ⌊B⌋₊).filter Nat.Prime,
    (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1))

/-- Square-root cutoff valuation-parity series `Σ*_parity(n) := Σ_parity(n; √n)` (2.3). -/
def SigmaParityStar (n : ℕ) : ℝ :=
  SigmaParity n (Real.sqrt n)

/-! ### Quadratic Fields and Fundamental Discriminants -/

/-- The quadratic field `ℚ(√d)` represented as `QuadraticAlgebra ℚ d 0`. -/
abbrev QuadField (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

instance instNumberFieldQuadField (d : ℚ) [Fact (¬ IsSquare d)] :
    NumberField (QuadField d) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- Fundamental discriminant `D(q)` of the quadratic field `ℚ(√q)` for square-free `q : ℤ`. -/
def fundDiscrQuad (q : ℤ) : ℤ :=
  if q % 4 = 1 then q else 4 * q

/-- Normalized `O(...)` asymptotic wrapper `AsympO f g` meaning `∃ C > 0, ∀ᶠ n in atTop, ‖f n‖ ≤ C * g n`. -/
def IsBigOAtTop (f : ℕ → ℝ) (g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → |f n| ≤ C * g n

/-- `IsLittleOAtTop f g` means `f(n)/g(n) → 0` as `n → ∞`. -/
def IsLittleOAtTop (f : ℕ → ℝ) (g : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => f n / g n) Filter.atTop (nhds 0)

end BrocardFormalization

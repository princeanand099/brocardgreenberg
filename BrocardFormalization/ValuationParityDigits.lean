/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.Basic
import BrocardFormalization.ExternalAxioms
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

/-! ### 2.2 Exact Base-p Digit Reduction Below √n -/

/-- Odd-indexed base-`p` digit sum `∑_{m} d_{2m+1}^{(p)}(n)` (Equation 2.6). -/
def oddIndexedDigitSum (p n : ℕ) : ℕ :=
  ((Nat.digits p n).zipIdx.filter (fun x => x.2 % 2 = 1)).map Prod.fst |>.sum

private lemma geom_sum_mod_two (p j : ℕ) (hp : p % 2 = 1) :
    (∑ i ∈ Finset.range j, p ^ i) % 2 = j % 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

private lemma ofDigits_eq_sum_range (p : ℕ) (L : List ℕ) :
    Nat.ofDigits p L = ∑ j ∈ Finset.range L.length, L.getD j 0 * p ^ j := by
  induction L with
  | nil => simp
  | cons d t ih =>
    simp only [Nat.ofDigits_cons, List.length_cons, Finset.sum_range_succ', pow_zero, mul_one,
      List.getD_cons_zero, List.getD_cons_succ, ih]
    rw [Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']
    ring

private lemma list_sum_eq_sum_range (L : List ℕ) :
    L.sum = ∑ j ∈ Finset.range L.length, L.getD j 0 := by
  induction L with
  | nil => simp
  | cons d t ih =>
    simp only [List.sum_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_zero, List.getD_cons_succ, ih]
    ring

private lemma zipIdx_odd_sum (k : ℕ) (L : List ℕ) :
    (((L.zipIdx k).filter (fun x => x.2 % 2 = 1)).map Prod.fst).sum =
      ∑ j ∈ (Finset.range L.length).filter (fun j => (k + j) % 2 = 1), L.getD j 0 := by
  induction L generalizing k with
  | nil => simp
  | cons d t ih =>
    simp only [List.zipIdx_cons, List.filter_cons, List.length_cons]
    have hsplit :
        (Finset.range (t.length + 1)).filter (fun j => (k + j) % 2 = 1) =
          (if k % 2 = 1 then {0} else ∅) ∪
            ((Finset.range t.length).filter (fun j => (k + 1 + j) % 2 = 1)).map
              ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      cases j with
      | zero => by_cases hk : k % 2 = 1 <;> simp [hk]
      | succ j =>
        simp only [Nat.succ_eq_add_one, add_lt_add_iff_right]
        split_ifs <;> simp [add_left_comm, add_comm]
    rw [hsplit, Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx2
      rcases hx2 with ⟨y, _, rfl⟩
      split_ifs at hx1 <;> simp at hx1)]
    rw [Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, List.getD_cons_succ]
    by_cases hk : k % 2 = 1
    · simp [hk, List.map_cons, List.sum_cons, ih (k + 1)]
    · simp [hk, ih (k + 1)]

private lemma oddIndexedDigitSum_eq_sum_range (p n : ℕ) :
    oddIndexedDigitSum p n =
      ∑ j ∈ (Finset.range (Nat.digits p n).length).filter (fun j => j % 2 = 1),
        (Nat.digits p n).getD j 0 := by
  unfold oddIndexedDigitSum
  simpa using zipIdx_odd_sum 0 (Nat.digits p n)

private lemma mul_geom_sum_add_one (p j : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ i ∈ Finset.range j, p ^ i) + 1 = p ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ']
    calc (p - 1) * (∑ i ∈ Finset.range j, p ^ i + p ^ j) + 1
        = ((p - 1) * ∑ i ∈ Finset.range j, p ^ i + 1) + (p - 1) * p ^ j := by ring
      _ = p ^ j + (p - 1) * p ^ j := by rw [ih]
      _ = (1 + (p - 1)) * p ^ j := by ring
      _ = p * p ^ j := by rw [Nat.add_sub_cancel' hp]

theorem lemma_2_2_i (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (_hn : 4 ≤ n) :
    padicValNat p n.factorial % 2 = oddIndexedDigitSum p n % 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
  have hdigits : Nat.ofDigits p (Nat.digits p n) = n := Nat.ofDigits_digits p n
  have hp1 : 0 < p - 1 := by omega
  have hid : (p - 1) * padicValNat p n.factorial =
      (p - 1) * ∑ j ∈ Finset.range (Nat.digits p n).length,
        (Nat.digits p n).getD j 0 * (∑ i ∈ Finset.range j, p ^ i) := by
    have hadd1 : (p - 1) * padicValNat p n.factorial + (Nat.digits p n).sum = n := by
      have hsum_le : (Nat.digits p n).sum ≤ n := by
        calc (Nat.digits p n).sum
            = ∑ j ∈ Finset.range (Nat.digits p n).length, (Nat.digits p n).getD j 0 := by
                rw [list_sum_eq_sum_range]
          _ ≤ ∑ j ∈ Finset.range (Nat.digits p n).length, (Nat.digits p n).getD j 0 * p ^ j :=
                Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_right _ (pow_pos hp.pos j)
          _ = Nat.ofDigits p (Nat.digits p n) := (ofDigits_eq_sum_range _ _).symm
          _ = n := hdigits
      omega
    have hadd2 : (p - 1) * ∑ j ∈ Finset.range (Nat.digits p n).length,
          (Nat.digits p n).getD j 0 * (∑ i ∈ Finset.range j, p ^ i) + (Nat.digits p n).sum = n := by
      conv_rhs => rw [← hdigits]
      rw [ofDigits_eq_sum_range, list_sum_eq_sum_range, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hg := mul_geom_sum_add_one p j hp.pos
      calc (p - 1) * ((Nat.digits p n).getD j 0 * ∑ i ∈ Finset.range j, p ^ i) + (Nat.digits p n).getD j 0
          = (Nat.digits p n).getD j 0 * ((p - 1) * (∑ i ∈ Finset.range j, p ^ i) + 1) := by ring
        _ = (Nat.digits p n).getD j 0 * p ^ j := by rw [hg]
    omega
  have hval : padicValNat p n.factorial =
      ∑ j ∈ Finset.range (Nat.digits p n).length,
        (Nat.digits p n).getD j 0 * (∑ i ∈ Finset.range j, p ^ i) :=
    Nat.eq_of_mul_eq_mul_left hp1 hid
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  rw [hval, oddIndexedDigitSum_eq_sum_range, Finset.sum_filter, Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.mul_mod, geom_sum_mod_two p j hp_odd]
  by_cases hj : j % 2 = 1
  · simp only [hj, ↓reduceIte, mul_one]
  · have hj0 : j % 2 = 0 := by omega
    simp [hj0]

/-- Digit-sum remainder `E_digit(n) := ∑_{3 ≤ p ≤ √n} (-1)^{v_p(n!) - 1} s_p(n) log p / (p - 1)`. -/
def Edigit (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
    (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
      (((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1))

theorem lemma_2_2_ii :
    (∀ n : ℕ, 4 ≤ n →
      ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p =
        -(n : ℝ) * SigmaParityStar n + Edigit n ∧
      |Edigit n| ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n) ∧
    IsBigOAtTop Edigit (fun n => Real.sqrt n) := by
  have hfl_sqrt : ∀ n : ℕ, ⌊Real.sqrt n⌋₊ = Nat.sqrt n := by
    intro n
    rw [Nat.floor_eq_iff (Real.sqrt_nonneg n)]
    exact ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n)),
      Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast (by simpa [sq] using Nat.lt_succ_sqrt n))⟩
  have hpart1 : ∀ n : ℕ, 4 ≤ n →
      ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        (-1 : ℝ) ^ padicValNat p n.factorial * (padicValNat p n.factorial : ℝ) * Real.log p =
        -(n : ℝ) * SigmaParityStar n + Edigit n ∧
      |Edigit n| ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n := by
    intro n hn4
    have hsig : SigmaParityStar n =
        ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          (-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) * (Real.log p / ((p : ℝ) - 1)) := by
      unfold SigmaParityStar SigmaParity
      rw [hfl_sqrt]
    constructor
    · rw [hsig, Edigit, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
      have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      have : Fact p.Prime := ⟨hp_prime⟩
      have hleg := sub_one_mul_padicValNat_factorial (p := p) n
      have hlegR : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = (n : ℝ) - ((Nat.digits p n).sum : ℝ) := by
        have hsum_le : (Nat.digits p n).sum ≤ n := by
          calc (Nat.digits p n).sum
              = ∑ j ∈ Finset.range (Nat.digits p n).length, (Nat.digits p n).getD j 0 := by
                  rw [list_sum_eq_sum_range]
            _ ≤ ∑ j ∈ Finset.range (Nat.digits p n).length, (Nat.digits p n).getD j 0 * p ^ j :=
                  Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_right _ (pow_pos hp_prime.pos j)
            _ = Nat.ofDigits p (Nat.digits p n) := (ofDigits_eq_sum_range _ _).symm
            _ = n := Nat.ofDigits_digits p n
        have h1 : (p - 1) * padicValNat p n.factorial + (Nat.digits p n).sum = n := by omega
        have h2 : ((p - 1 : ℕ) : ℝ) * (padicValNat p n.factorial : ℝ) + ((Nat.digits p n).sum : ℝ) = (n : ℝ) := by
          exact_mod_cast h1
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h2
        linarith
      have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have hvalR : (padicValNat p n.factorial : ℝ) = ((n : ℝ) - ((Nat.digits p n).sum : ℝ)) / ((p : ℝ) - 1) := by
        rw [eq_div_iff hp1_ne, mul_comm]; exact hlegR
      have hpow_neg : (-1 : ℝ) ^ (padicValNat p n.factorial : ℤ) = -((-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1)) := by
        have h1 : (-1 : ℝ) ^ (padicValNat p n.factorial : ℤ) = (-1 : ℝ) ^ (((padicValNat p n.factorial : ℤ) - 1) + 1) := by
          congr 1; ring
        rw [h1, zpow_add₀ (by norm_num), zpow_one]
        ring
      have hpow_nat : (-1 : ℝ) ^ padicValNat p n.factorial = (-1 : ℝ) ^ (padicValNat p n.factorial : ℤ) :=
        (zpow_natCast (-1 : ℝ) _).symm
      rw [hpow_nat, hpow_neg, hvalR]
      ring
    · unfold Edigit
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          |(-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
            (((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1))| ≤ 2 * Real.log n := by
        intro p hp
        have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
        have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        have hp_le : p ≤ Nat.sqrt n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        have hp_le_n : p ≤ n := le_trans hp_le (Nat.sqrt_le_self n)
        have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.pos)
        rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
          abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogp_nn) hp1_pos.le)]
        have hdig_le : (Nat.digits p n).sum ≤ (p - 1) * (Nat.log p n + 1) := by
          have h1 : ∀ d ∈ Nat.digits p n, d ≤ p - 1 := fun d hd =>
            Nat.le_pred_of_lt (Nat.digits_lt_base hp_prime.one_lt hd)
          have h2 : (Nat.digits p n).sum ≤ (Nat.digits p n).length * (p - 1) := by
            have := List.sum_le_sum (l := Nat.digits p n) (f := id) (g := fun _ => p - 1) fun d hd => h1 d hd
            simpa using this
          have hlen : (Nat.digits p n).length ≤ Nat.log p n + 1 := by
            by_contra hgt
            push_neg at hgt
            have h1 : p ^ (Nat.log p n + 1) ≤ Nat.ofDigits p (Nat.digits p n) := by
              have hlen_pos : 0 < (Nat.digits p n).length := by omega
              have hlast_pos : 0 < (Nat.digits p n).getLast (List.ne_nil_of_length_pos hlen_pos) := by
                have := Nat.getLast_digit_ne_zero p (by omega : n ≠ 0)
                omega
              rw [ofDigits_eq_sum_range]
              have hmem : (Nat.digits p n).length - 1 ∈ Finset.range (Nat.digits p n).length :=
                Finset.mem_range.mpr (by omega)
              have hle_sum := Finset.single_le_sum (f := fun j => (Nat.digits p n).getD j 0 * p ^ j)
                (fun _ _ => Nat.zero_le _) hmem
              have hget : (Nat.digits p n).getD ((Nat.digits p n).length - 1) 0 ≥ 1 := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
                have hne : Nat.digits p n ≠ [] := List.ne_nil_of_length_pos hlen_pos
                have hgl := List.getLast_eq_getElem hne
                rw [← hgl]; exact hlast_pos
              have hpow_le : p ^ (Nat.log p n + 1) ≤ p ^ ((Nat.digits p n).length - 1) :=
                Nat.pow_le_pow_right hp_prime.pos (by omega)
              calc p ^ (Nat.log p n + 1) ≤ 1 * p ^ ((Nat.digits p n).length - 1) := by simpa using hpow_le
                _ ≤ (Nat.digits p n).getD ((Nat.digits p n).length - 1) 0 * p ^ ((Nat.digits p n).length - 1) :=
                    Nat.mul_le_mul_right _ hget
                _ ≤ ∑ j ∈ Finset.range (Nat.digits p n).length, (Nat.digits p n).getD j 0 * p ^ j := hle_sum
            rw [Nat.ofDigits_digits] at h1
            have hlt : n < p ^ (Nat.log p n + 1) := Nat.lt_pow_succ_log_self hp_prime.one_lt n
            omega
          exact le_trans h2 (by rw [mul_comm]; exact Nat.mul_le_mul_left _ hlen)
        have hdig_leR : ((Nat.digits p n).sum : ℝ) ≤ ((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1) := by
          have hcast : ((Nat.digits p n).sum : ℝ) ≤ (((p - 1) * (Nat.log p n + 1) : ℕ) : ℝ) := by exact_mod_cast hdig_le
          rw [Nat.cast_mul, Nat.cast_sub hp_prime.one_le, Nat.cast_add, Nat.cast_one] at hcast
          exact hcast
        have hlog_pow : (Nat.log p n : ℝ) * Real.log p ≤ Real.log n := by
          have hpow : (p : ℝ) ^ Nat.log p n ≤ n := by exact_mod_cast Nat.pow_log_le_self p (by omega)
          have h1 := Real.log_le_log (pow_pos (by exact_mod_cast hp_prime.pos) _) hpow
          rwa [Real.log_pow] at h1
        have hlogp_le : Real.log p ≤ Real.log n :=
          Real.log_le_log (by exact_mod_cast hp_prime.pos) (by exact_mod_cast hp_le_n)
        calc ((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1)
            ≤ (((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1)) * Real.log p / ((p : ℝ) - 1) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdig_leR hlogp_nn) hp1_pos.le
          _ = ((Nat.log p n : ℝ) + 1) * Real.log p := by field_simp [hp1_pos.ne']
          _ = (Nat.log p n : ℝ) * Real.log p + Real.log p := by ring
          _ ≤ Real.log n + Real.log n := add_le_add hlog_pow hlogp_le
          _ = 2 * Real.log n := by ring
      have hcard_le : ((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime).card ≤ Nat.primeCounting (Nat.sqrt n) := by
        rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
        refine Finset.card_le_card fun p hp => ?_
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        exact ⟨Nat.lt_succ_of_le hp.1.2, hp.2⟩
      calc ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
            |(-1 : ℝ) ^ ((padicValNat p n.factorial : ℤ) - 1) *
              (((Nat.digits p n).sum : ℝ) * Real.log p / ((p : ℝ) - 1))|
          ≤ ∑ _p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime, (2 * Real.log n) := Finset.sum_le_sum hterm
        _ = (((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime).card : ℝ) * (2 * Real.log n) := by simp
        _ ≤ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * Real.log n) := by
            refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) ?_
            exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
        _ = 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n := by ring
  refine ⟨hpart1, ?_⟩
  have hpi_sqrt : ∀ n : ℕ, 16 ≤ n →
      (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) + 8 * Real.log 4 * Real.sqrt n / Real.log n := by
    intro n hn16
    set m := Nat.sqrt n
    have hm4 : 4 ≤ m := Nat.le_sqrt.mpr (by omega)
    have hsplit : (Finset.Icc 2 m).filter Nat.Prime =
        ((Finset.Icc 2 (Nat.sqrt m)).filter Nat.Prime) ∪
        ((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases le_or_gt p (Nat.sqrt m) with hle | hgt
        · exact Or.inl ⟨⟨h1, hle⟩, h3⟩
        · exact Or.inr ⟨⟨hgt, h2⟩, h3⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, le_trans h2 (Nat.sqrt_le_self m)⟩, h3⟩
        · exact ⟨⟨by omega, h2⟩, h3⟩
    have hpc_eq : (Nat.primeCounting m : ℝ) = ((Finset.Icc 2 m).filter Nat.Prime).card := by
      congr 1
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h2.two_le, Nat.lt_succ_iff.mp h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨Nat.lt_succ_iff.mpr h1, h2⟩⟩
    have hcard_le : ((Finset.Icc 2 m).filter Nat.Prime).card ≤
        Nat.sqrt m + ((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card := by
      rw [hsplit]
      refine le_trans (Finset.card_union_le _ _) (add_le_add ?_ le_rfl)
      exact le_trans (Finset.card_filter_le _ _) (by simp only [Nat.card_Icc]; omega)
    have hlogm_ge : (1 / 4 : ℝ) * Real.log n ≤ Real.log m := by
      have hm_ge : (1 / 2 : ℝ) * Real.sqrt n ≤ m := by
        have := Nat.lt_succ_sqrt n
        have h1 : Real.sqrt n < (m : ℝ) + 1 := Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast (by simpa [sq] using this : n < (m + 1) ^ 2))
        have h2 : (4 : ℝ) ≤ m := by exact_mod_cast hm4
        linarith
      have h1 := Real.log_le_log (by positivity) hm_ge
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity), one_div, Real.log_inv] at h1
      have hlogn4 : 4 * Real.log 2 ≤ Real.log n := by
        have h16 : (2 : ℝ) ^ 4 ≤ n := by exact_mod_cast (by simpa using hn16 : 16 ≤ n)
        have := Real.log_le_log (by positivity) h16
        rwa [Real.log_pow] at this
      linarith
    have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hlogm_pos : 0 < Real.log m := by linarith
    have hcard2_bd : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) * ((1 / 2 : ℝ) * Real.log m) ≤
        Real.log 4 * (m : ℝ) := by
      have h1 : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) * ((1 / 2 : ℝ) * Real.log m) ≤
          ∑ p ∈ (Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime, Real.log p := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_gt : Nat.sqrt m < p := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega
        have hm_lt : (m : ℝ) < (p : ℝ) ^ 2 := by
          have : m < p * p := lt_of_lt_of_le (Nat.lt_succ_sqrt m) (Nat.mul_le_mul hp_gt hp_gt)
          exact_mod_cast (by simpa [sq] using this)
        have := Real.log_lt_log (by positivity) hm_lt
        rw [Real.log_pow] at this; norm_num at this; linarith
      have h2 : ∑ p ∈ (Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime, Real.log p ≤ Chebyshev.theta (m : ℝ) := by
        unfold Chebyshev.theta; rw [Nat.floor_natCast]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le)
        intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢; exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩
      exact le_trans h1 (le_trans h2 (Chebyshev.theta_le_log4_mul_x (by positivity)))
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le n))
    have hsq_m : (Nat.sqrt m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa [sq] using Nat.sqrt_le m))
      have h2 : Real.sqrt m ≤ Real.sqrt (Real.sqrt n) := Real.sqrt_le_sqrt hm_le_sqrt
      have h3 : Real.sqrt (Real.sqrt n) = (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; norm_num
      linarith [show 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) by positivity]
    have hcard2_hi : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) ≤
        8 * Real.log 4 * Real.sqrt n / Real.log n := by
      have h1 : (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) ≤
          2 * Real.log 4 * (m : ℝ) / Real.log m := (le_div_iff₀ (by positivity)).mpr (by linarith)
      have h2 : 2 * Real.log 4 * (m : ℝ) / Real.log m ≤
          2 * Real.log 4 * Real.sqrt n / ((1 / 4 : ℝ) * Real.log n) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_le_sqrt (by positivity))
          (by positivity) hlogm_ge
      linarith [show 2 * Real.log 4 * Real.sqrt n / ((1 / 4 : ℝ) * Real.log n) =
        8 * Real.log 4 * Real.sqrt n / Real.log n by ring]
    rw [hpc_eq]
    have hcast : (((Finset.Icc 2 m).filter Nat.Prime).card : ℝ) ≤
        (Nat.sqrt m : ℝ) + (((Finset.Icc (Nat.sqrt m + 1) m).filter Nat.Prime).card : ℝ) := by
      exact_mod_cast hcard_le
    linarith
  have hlog_ev : ∀ᶠ n : ℕ in atTop, 16 ≤ n ∧ 4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n ≤ Real.sqrt n := by
    filter_upwards [eventually_ge_atTop (32 ^ 8)] with n hn
    refine ⟨by omega, ?_⟩
    have hn_pos : (0 : ℝ) < n := by positivity
    have hr8_pos : (0 : ℝ) < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    have hlog8 : Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hr8_pos]
    rw [Real.log_rpow hn_pos] at hlog8
    have hlog_le : Real.log n ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by linarith
    have h32 : (32 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
      have h32_8 : (32 : ℝ) ^ (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by simpa using hn : 32 ^ 8 ≤ n)
      rw [one_div]; exact (Real.le_rpow_inv_iff_of_pos (by norm_num) hn_pos.le (by norm_num : (0 : ℝ) < 8)).mpr h32_8
    have hmul : 4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n ≤ 32 * (n : ℝ) ^ (3 / 8 : ℝ) := by
      calc 4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n
          ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) * (8 * (n : ℝ) ^ (1 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
        _ = 32 * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ)) := by ring
        _ = 32 * (n : ℝ) ^ (3 / 8 : ℝ) := by rw [← Real.rpow_add hn_pos]; norm_num
    have hmul2 : 32 * (n : ℝ) ^ (3 / 8 : ℝ) ≤ Real.sqrt n := by
      calc 32 * (n : ℝ) ^ (3 / 8 : ℝ)
          ≤ (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ) :=
            mul_le_mul_of_nonneg_right h32 (by positivity)
        _ = (n : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hn_pos]; norm_num
        _ = Real.sqrt n := (Real.sqrt_eq_rpow n).symm
    exact le_trans hmul hmul2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hlog_ev
  refine ⟨1 + 16 * Real.log 4, by positivity, N₀, fun n hnN => ?_⟩
  obtain ⟨hn16, hlog_le_sq⟩ := hN₀ n hnN
  have h1 := (hpart1 n (by omega)).2
  have h2 := hpi_sqrt n hn16
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  calc |Edigit n| ≤ 2 * (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log n := h1
    _ ≤ 2 * (2 * (n : ℝ) ^ (1 / 4 : ℝ) + 8 * Real.log 4 * Real.sqrt n / Real.log n) * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hlogn_pos.le
    _ = 4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n + 16 * Real.log 4 * Real.sqrt n := by
        field_simp [hlogn_pos.ne']; ring
    _ ≤ Real.sqrt n + 16 * Real.log 4 * Real.sqrt n := add_le_add hlog_le_sq le_rfl
    _ = (1 + 16 * Real.log 4) * Real.sqrt n := by ring

/-! ### 2.3 Vaaler Approximation, Exponential Sums, and Equidistribution -/

private lemma neg_one_pow_floor_eq_sawtooth (x : ℝ) :
    (-1 : ℝ) ^ ⌊x⌋ =
      2 * ((((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2) -
            (x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2))) := by
  have h1 : ∀ m : ℤ, m ≤ x / 2 → x / 2 < m + 1 →
      ⌊x / 2⌋ = m := fun m hlo hhi => Int.floor_eq_iff.mpr ⟨hlo, hhi⟩
  rcases Int.even_or_odd ⌊x⌋ with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk' : ⌊x⌋ = 2 * k := by omega
    have hx_lo : (2 * k : ℝ) ≤ x := by exact_mod_cast hk' ▸ Int.floor_le x
    have hx_hi : x < (2 * k : ℝ) + 1 := by exact_mod_cast hk' ▸ Int.lt_floor_add_one x
    have hfl1 : ⌊x / 2⌋ = k := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hfl2 : ⌊(x - 1) / 2⌋ = k - 1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [hk, (show (-1 : ℝ) ^ (k + k) = 1 by rw [← two_mul, zpow_mul]; norm_num), hfl1, hfl2]
    push_cast; ring
  · have hx_lo : (2 * k + 1 : ℝ) ≤ x := by exact_mod_cast hk ▸ Int.floor_le x
    have hx_hi : x < (2 * k + 1 : ℝ) + 1 := by exact_mod_cast hk ▸ Int.lt_floor_add_one x
    have hfl1 : ⌊x / 2⌋ = k := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hfl2 : ⌊(x - 1) / 2⌋ = k := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [hk, (show (-1 : ℝ) ^ (2 * k + 1) = -1 by
      rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num), hfl1, hfl2]
    ring

private lemma ePhase_sub_one_mul (h : ℤ) (x : ℝ) :
    ePhase ((h : ℝ) * ((x - 1) / 2)) - ePhase ((h : ℝ) * (x / 2)) =
      ((-1 : ℂ) ^ h - 1) * ePhase ((h : ℝ) * x / 2) := by
  unfold ePhase
  have h1 : (2 * Real.pi * Complex.I * (((h : ℝ) * ((x - 1) / 2) : ℝ) : ℂ)) =
      -(Real.pi * Complex.I * (h : ℂ)) + 2 * Real.pi * Complex.I * (((h : ℝ) * x / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (2 * Real.pi * Complex.I * (((h : ℝ) * (x / 2) : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (((h : ℝ) * x / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add]
  have hexp : Complex.exp (-(Real.pi * Complex.I * (h : ℂ))) = (-1 : ℂ) ^ h := by
    rw [Complex.exp_neg, show Real.pi * Complex.I * (h : ℂ) = (h : ℂ) * (Real.pi * Complex.I) by ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
    rcases Int.even_or_odd h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp [← two_mul, zpow_mul]
    · simp [zpow_add₀, zpow_mul]
  rw [hexp]
  ring

private lemma ePhase_add_one_mul (h : ℤ) (x : ℝ) :
    ePhase ((h : ℝ) * ((x - 1) / 2)) + ePhase ((h : ℝ) * (x / 2)) =
      ((-1 : ℂ) ^ h + 1) * ePhase ((h : ℝ) * x / 2) := by
  unfold ePhase
  have h1 : (2 * Real.pi * Complex.I * (((h : ℝ) * ((x - 1) / 2) : ℝ) : ℂ)) =
      -(Real.pi * Complex.I * (h : ℂ)) + 2 * Real.pi * Complex.I * (((h : ℝ) * x / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (2 * Real.pi * Complex.I * (((h : ℝ) * (x / 2) : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (((h : ℝ) * x / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add]
  have hexp : Complex.exp (-(Real.pi * Complex.I * (h : ℂ))) = (-1 : ℂ) ^ h := by
    rw [Complex.exp_neg, show Real.pi * Complex.I * (h : ℂ) = (h : ℂ) * (Real.pi * Complex.I) by ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
    rcases Int.even_or_odd h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp [← two_mul, zpow_mul]
    · simp [zpow_add₀, zpow_mul]
  rw [hexp]
  ring

theorem lemma_2_3 (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Ψtilde Btilde : ℝ → ℝ) (cTilde bTilde : ℤ → ℂ),
      (∀ x : ℝ, (Ψtilde x : ℂ) =
        ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
            (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
          cTilde h * ePhase ((h : ℝ) * x / 2)) ∧
      (∀ x : ℝ, (Btilde x : ℂ) =
        bTilde 0 +
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
            bTilde h * ePhase ((h : ℝ) * x / 2)) ∧
      (bTilde 0 = 2 / ((H : ℂ) + 1)) ∧
      (∀ h : ℤ, h ≠ 0 → ¬ 2 ∣ h → ‖cTilde h‖ ≤ 2 / (Real.pi * |(h : ℝ)|)) ∧
      (∀ h : ℤ, ‖bTilde h‖ < 3 / ((H : ℝ) + 1)) ∧
      (∀ x : ℝ, |(-1 : ℝ) ^ ⌊x⌋ - Ψtilde x| ≤ Btilde x) ∧
      (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
          (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), ‖cTilde h‖ ≤
        (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) := by
  classical
  obtain ⟨W, _, _, hVaaler⟩ := vaaler_sawtooth_approx
  obtain ⟨Ψ, B, c, b, hΨ, hB, _, hc_bd, hb0, hb_bd, _, happrox⟩ := hVaaler H hH
  let Ψtilde : ℝ → ℝ := fun x => 2 * (Ψ ((x - 1) / 2) - Ψ (x / 2))
  let Btilde : ℝ → ℝ := fun x => 2 * (B ((x - 1) / 2) + B (x / 2))
  let cTilde : ℤ → ℂ := fun h => if |h| ≤ (H : ℤ) ∧ h ≠ 0 ∧ ¬ 2 ∣ h then -4 * c h else 0
  let bTilde : ℤ → ℂ := fun h => if |h| ≤ (H : ℤ) ∧ 2 ∣ h then 4 * b h else 0
  refine ⟨Ψtilde, Btilde, cTilde, bTilde, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Ψtilde, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sub, hΨ]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hsub1 : (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0) ⊇
        (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0 ∧ ¬ 2 ∣ h) := by
      intro h hh; simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢; exact ⟨hh.1, hh.2.1⟩
    have hsum1 : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
          (2 : ℂ) * (c h * ePhase ((h : ℝ) * ((x - 1) / 2)) - c h * ePhase ((h : ℝ) * (x / 2))) =
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
          (-4 * c h) * ePhase ((h : ℝ) * x / 2) := by
      rw [← Finset.sum_sdiff hsub1]
      have hzero : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0) \
            (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h),
          (2 : ℂ) * (c h * ePhase ((h : ℝ) * ((x - 1) / 2)) - c h * ePhase ((h : ℝ) * (x / 2))) = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hh
        have heven : 2 ∣ h := by tauto
        have heq : c h * ePhase ((h : ℝ) * ((x - 1) / 2)) - c h * ePhase ((h : ℝ) * (x / 2)) =
            c h * (((-1 : ℂ) ^ h - 1) * ePhase ((h : ℝ) * x / 2)) := by
          rw [← mul_sub, ePhase_sub_one_mul]
        rcases heven with ⟨k, rfl⟩
        have hpow : (-1 : ℂ) ^ (2 * k) = 1 := by rw [zpow_mul]; norm_num
        rw [heq, hpow]; ring
      rw [hzero, zero_add]
      refine Finset.sum_congr rfl fun h hh => ?_
      have hodd : Odd h := Int.not_even_iff_odd.mp fun he => (Finset.mem_filter.mp hh).2.2 (even_iff_two_dvd.mp he)
      have heq : c h * ePhase ((h : ℝ) * ((x - 1) / 2)) - c h * ePhase ((h : ℝ) * (x / 2)) =
          c h * (((-1 : ℂ) ^ h - 1) * ePhase ((h : ℝ) * x / 2)) := by
        rw [← mul_sub, ePhase_sub_one_mul]
      rcases hodd with ⟨k, rfl⟩
      have hpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num
      rw [heq, hpow]; ring
    rw [hsum1]
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      exact ⟨⟨by linarith [Int.natCast_nonneg H], by linarith [Int.natCast_nonneg H]⟩, hh.2⟩
    · intro h hh
      rw [Finset.mem_sdiff] at hh
      rcases hh with ⟨hh1, hh2⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh1
      have hnot : ¬ (|h| ≤ (H : ℤ) ∧ h ≠ 0 ∧ ¬ 2 ∣ h) := fun ⟨hab, hn, ho⟩ =>
        hh2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hab), hn, ho⟩)
      rw [cTilde, if_neg hnot, norm_zero]
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh
      have hok : |h| ≤ (H : ℤ) ∧ h ≠ 0 ∧ ¬ 2 ∣ h := ⟨abs_le.mpr hh.1, hh.2⟩
      simp [cTilde, hok]
  · intro x
    simp only [Btilde, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_add, hB]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← Finset.add_sum_erase _ _ h0mem]
    have h0term : (2 : ℂ) * (b 0 * ePhase ((0 : ℤ) * ((x - 1) / 2)) + b 0 * ePhase ((0 : ℤ) * (x / 2))) = bTilde 0 := by
      simp [bTilde, ePhase, Complex.exp_zero]; ring
    have herase : (Finset.Icc (-(H : ℤ)) H).erase 0 = (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0) := by
      ext h; simp [and_comm]
    rw [h0term, herase]
    congr 1
    have hsub1 : (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0 ∧ 2 ∣ h) ⊆
        (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0) := by
      intro h hh; simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢; exact ⟨hh.1, hh.2.1⟩
    have hsum1 : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0),
          (2 : ℂ) * (b h * ePhase ((h : ℝ) * ((x - 1) / 2)) + b h * ePhase ((h : ℝ) * (x / 2))) =
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ 2 ∣ h),
          (4 * b h) * ePhase ((h : ℝ) * x / 2) := by
      rw [← Finset.sum_sdiff hsub1]
      have hzero : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (· ≠ 0) \
            (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ 2 ∣ h),
          (2 : ℂ) * (b h * ePhase ((h : ℝ) * ((x - 1) / 2)) + b h * ePhase ((h : ℝ) * (x / 2))) = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hh
        have hodd : Odd h := Int.not_even_iff_odd.mp fun he => by
          have := even_iff_two_dvd.mp he; tauto
        have heq : b h * ePhase ((h : ℝ) * ((x - 1) / 2)) + b h * ePhase ((h : ℝ) * (x / 2)) =
            b h * (((-1 : ℂ) ^ h + 1) * ePhase ((h : ℝ) * x / 2)) := by
          rw [← mul_add, ePhase_add_one_mul]
        rcases hodd with ⟨k, rfl⟩
        have hpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num
        rw [heq, hpow]; ring
      rw [hzero, zero_add]
      refine Finset.sum_congr rfl fun h hh => ?_
      have heven : Even h := even_iff_two_dvd.mpr (Finset.mem_filter.mp hh).2.2
      have heq : b h * ePhase ((h : ℝ) * ((x - 1) / 2)) + b h * ePhase ((h : ℝ) * (x / 2)) =
          b h * (((-1 : ℂ) ^ h + 1) * ePhase ((h : ℝ) * x / 2)) := by
        rw [← mul_add, ePhase_add_one_mul]
      rcases heven with ⟨k, rfl⟩
      have hpow : (-1 : ℂ) ^ (k + k) = 1 := by rw [← two_mul, zpow_mul]; norm_num
      rw [heq, hpow]; ring
    rw [hsum1]
    refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
      exact ⟨⟨by linarith [Int.natCast_nonneg H], by linarith [Int.natCast_nonneg H]⟩, hh.2.1⟩
    · intro h hh
      rw [Finset.mem_sdiff] at hh
      rcases hh with ⟨hh1, hh2⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh1
      by_cases h2 : 2 ∣ h
      · have hnot : ¬ (|h| ≤ (H : ℤ) ∧ 2 ∣ h) := fun ⟨hab, _⟩ =>
          hh2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hab), hh1.2⟩)
        simp [bTilde, hnot]
      · simp [bTilde, h2]
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh
      have hok : |h| ≤ (H : ℤ) ∧ 2 ∣ h := ⟨abs_le.mpr hh.1, hh.2.2⟩
      simp [bTilde, hok]
  · simp [bTilde, hb0]
    have hden : ((H : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : H + 1 ≠ 0)
    field_simp [hden]
    ring
  · intro h hh hodd
    by_cases hH_le : |h| ≤ (H : ℤ)
    · have hok : |h| ≤ (H : ℤ) ∧ h ≠ 0 ∧ ¬ 2 ∣ h := ⟨hH_le, hh, hodd⟩
      simp only [cTilde, if_pos hok, norm_mul, norm_neg, Complex.norm_ofNat]
      calc 4 * ‖c h‖ ≤ 4 * (1 / (2 * Real.pi * |(h : ℝ)|)) := mul_le_mul_of_nonneg_left (hc_bd h hh) (by norm_num)
        _ = 2 / (Real.pi * |(h : ℝ)|) := by ring
    · simp only [cTilde, hH_le, false_and, ↓reduceIte, norm_zero]
      positivity
  · intro h
    by_cases hok : |h| ≤ (H : ℤ) ∧ 2 ∣ h
    · simp only [bTilde, if_pos hok, norm_mul, Complex.norm_ofNat]
      calc 4 * ‖b h‖ ≤ 4 * (1 / (2 * (H : ℝ) + 2)) := mul_le_mul_of_nonneg_left (hb_bd h) (by norm_num)
        _ = 2 / ((H : ℝ) + 1) := by field_simp; ring
        _ < 3 / ((H : ℝ) + 1) := by
          have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
          exact div_lt_div_of_pos_right (by norm_num) hpos
    · simp only [bTilde, if_neg hok, norm_zero]
      positivity
  · intro x
    rw [neg_one_pow_floor_eq_sawtooth x]
    simp only [Ψtilde, Btilde]
    have hdiff : 2 * (((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2) - (x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2)) -
        2 * (Ψ ((x - 1) / 2) - Ψ (x / 2)) =
        2 * (((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2 - Ψ ((x - 1) / 2)) -
          (x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2 - Ψ (x / 2))) := by ring
    rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 := happrox ((x - 1) / 2)
    have h2 := happrox (x / 2)
    have htri := abs_sub ((x - 1) / 2 - (⌊(x - 1) / 2⌋ : ℝ) - 1 / 2 - Ψ ((x - 1) / 2))
      (x / 2 - (⌊x / 2⌋ : ℝ) - 1 / 2 - Ψ (x / 2))
    linarith
  · have hsplit : ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter
          (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), ‖cTilde h‖ ≤
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), (2 / (Real.pi * |(h : ℝ)|)) := by
      have hinc : (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h) ⊆
          (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h) := by
        intro h hh; simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢; exact ⟨⟨by omega, by omega⟩, hh.2⟩
      rw [← Finset.sum_sdiff hinc]
      have hz : ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h) \
            (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), ‖cTilde h‖ = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_sdiff] at hh
        rcases hh with ⟨hh1, hh2⟩
        simp only [Finset.mem_filter, Finset.mem_Icc] at hh1
        have hnot : ¬ (|h| ≤ (H : ℤ) ∧ h ≠ 0 ∧ ¬ 2 ∣ h) := fun ⟨hab, hn, ho⟩ =>
          hh2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hab), hn, ho⟩)
        rw [cTilde, if_neg hnot, norm_zero]
      rw [hz, zero_add]
      refine Finset.sum_le_sum fun h hh => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hh
      have hok : |h| ≤ (H : ℤ) ∧ h ≠ 0 ∧ ¬ 2 ∣ h := ⟨abs_le.mpr hh.1, hh.2⟩
      simp only [cTilde, if_pos hok, norm_mul, norm_neg, Complex.norm_ofNat]
      calc 4 * ‖c h‖ ≤ 4 * (1 / (2 * Real.pi * |(h : ℝ)|)) := mul_le_mul_of_nonneg_left (hc_bd h hh.2.1) (by norm_num)
        _ = 2 / (Real.pi * |(h : ℝ)|) := by ring
    have hpos_neg : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), (2 / (Real.pi * |(h : ℝ)|)) ≤
        2 * ∑ k ∈ Finset.Icc 1 H, (2 / (Real.pi * (k : ℝ))) := by
      have hinc2 : (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h) ⊆
          ((Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ))) ∪ ((Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ))) := by
        intro h hh
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image] at hh ⊢
        rcases lt_trichotomy h 0 with hlt | rfl | hgt
        · right; refine ⟨h.natAbs, ⟨?_, ?_⟩, ?_⟩ <;> omega
        · exact absurd rfl hh.2.1
        · left; refine ⟨h.natAbs, ⟨?_, ?_⟩, ?_⟩ <;> omega
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hinc2 (fun _ _ _ => by positivity)) ?_
      have hunion_le : ∑ h ∈ ((Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ))) ∪
            ((Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ))), (2 / (Real.pi * |(h : ℝ)|)) ≤
          ∑ h ∈ (Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ)), (2 / (Real.pi * |(h : ℝ)|)) +
          ∑ h ∈ (Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ)), (2 / (Real.pi * |(h : ℝ)|)) := by
        have h1 := Finset.sum_union_inter (s₁ := (Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ)))
          (s₂ := (Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ))) (f := fun h : ℤ => 2 / (Real.pi * |(h : ℝ)|))
        have hnn : 0 ≤ ∑ h ∈ ((Finset.Icc 1 H).image (fun k : ℕ => (k : ℤ))) ∩
            ((Finset.Icc 1 H).image (fun k : ℕ => -(k : ℤ))), (2 / (Real.pi * |(h : ℝ)|)) :=
          Finset.sum_nonneg fun _ _ => by positivity
        linarith
      refine le_trans hunion_le ?_
      rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h),
        Finset.sum_image (fun a _ b _ h => by exact_mod_cast neg_inj.mp h)]
      have h1 : ∑ k ∈ Finset.Icc 1 H, (2 / (Real.pi * |((k : ℤ) : ℝ)|)) = ∑ k ∈ Finset.Icc 1 H, (2 / (Real.pi * (k : ℝ))) := by
        refine Finset.sum_congr rfl fun k _ => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
      have h2 : ∑ k ∈ Finset.Icc 1 H, (2 / (Real.pi * |((-(k : ℤ) : ℤ) : ℝ)|)) = ∑ k ∈ Finset.Icc 1 H, (2 / (Real.pi * (k : ℝ))) := by
        refine Finset.sum_congr rfl fun k _ => by simp [abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
      linarith
    have hharm : ∑ k ∈ Finset.Icc 1 H, (2 / (Real.pi * (k : ℝ))) = (2 / Real.pi) * (harmonic H : ℝ) := by
      have heq : (harmonic H : ℝ) = ∑ k ∈ Finset.Icc 1 H, (1 : ℝ) / (k : ℝ) := by
        induction H with
        | zero => simp
        | succ m ihm => rw [Finset.sum_Icc_succ_top (by omega), ← ihm, harmonic_succ]; push_cast; ring
      rw [heq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    have hharm_le : (harmonic H : ℝ) ≤ 1 + Real.log H := by simpa using harmonic_le_one_add_log H
    have hlogH_le : Real.log (H : ℝ) ≤ Real.log (2 * (H : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    calc ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ ¬ 2 ∣ h), ‖cTilde h‖
        ≤ 2 * ((2 / Real.pi) * (harmonic H : ℝ)) := by linarith
      _ ≤ 2 * ((2 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by norm_num)
      _ = (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) := by ring

end BrocardFormalization

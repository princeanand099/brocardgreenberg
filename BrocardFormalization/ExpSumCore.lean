/-
Copyright (c) 2026 Formalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BrocardFormalization.ExpSumTypeI

noncomputable section

open scoped BigOperators
open Filter Topology BrocardFormalization.External

namespace BrocardFormalization

lemma sum_divisors_card_sq_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ x ∈ Finset.Icc 1 X, ((x.divisors.card : ℝ) ^ 2) ≤ (X : ℝ) * (1 + Real.log X) ^ 3 := by
  have h1 : ∑ x ∈ Finset.Icc 1 X, (x.divisors.card : ℝ) ^ 2 =
      ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X,
        (((Finset.Icc 1 X).filter (fun x => Nat.lcm d₁ d₂ ∣ x)).card : ℝ) := by
    have hsq : ∀ x ∈ Finset.Icc 1 X, (x.divisors.card : ℝ) ^ 2 =
        ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X,
          if Nat.lcm d₁ d₂ ∣ x then (1 : ℝ) else 0 := by
      intro x hx
      have hx_pos : 0 < x := (Finset.mem_Icc.mp hx).1
      have hsub : x.divisors ⊆ Finset.Icc 1 X := fun d hd =>
        Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
          le_trans (Nat.le_of_dvd hx_pos (Nat.dvd_of_mem_divisors hd)) (Finset.mem_Icc.mp hx).2⟩
      rw [sq, ← Finset.sum_boole_mul]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Nat.cast_mul]
      rw [← Finset.sum_subset hsub (fun d _ hd => by simp [Nat.mem_divisors.not.mp hd])]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset hsub (fun d _ hd => by simp [Nat.mem_divisors.not.mp hd])]
      refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
      by_cases h1 : d₁ ∣ x <;> by_cases h2 : d₂ ∣ x
      · have hl : Nat.lcm d₁ d₂ ∣ x := Nat.lcm_dvd h1 h2
        simp [h1, h2, hl, hx_pos.ne']
      · have hl : ¬ Nat.lcm d₁ d₂ ∣ x := fun h => h2 (dvd_trans (Nat.dvd_lcm_right d₁ d₂) h)
        simp [h1, h2, hl]
      · have hl : ¬ Nat.lcm d₁ d₂ ∣ x := fun h => h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) h)
        simp [h1, h2, hl]
      · have hl : ¬ Nat.lcm d₁ d₂ ∣ x := fun h => h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) h)
        simp [h1, h2, hl]
    rw [Finset.sum_congr rfl hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    simp [Finset.card_filter]
  have h2 : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ →
      (((Finset.Icc 1 X).filter (fun x => Nat.lcm d₁ d₂ ∣ x)).card : ℝ) ≤
        (X : ℝ) / (Nat.lcm d₁ d₂ : ℝ) := by
    intro d₁ d₂ hd₁ hd₂
    set L := Nat.lcm d₁ d₂
    have hL_pos : 0 < L := Nat.lcm_pos hd₁ hd₂
    have hsub : (Finset.Icc 1 X).filter (fun x => L ∣ x) ⊆
        (Finset.Icc 1 (X / L)).image (fun k => L * k) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      rcases hx.2 with ⟨k, rfl⟩
      refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · by_contra hk0
        have : k = 0 := by omega
        subst this; simp at hx
      · exact (Nat.le_div_iff_mul_le hL_pos).mpr (by linarith [hx.1.2])
    have hcard : ((Finset.Icc 1 X).filter (fun x => L ∣ x)).card ≤ X / L := by
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      simp
    have hcast : (((Finset.Icc 1 X).filter (fun x => L ∣ x)).card : ℝ) ≤ ((X / L : ℕ) : ℝ) := by
      exact_mod_cast hcard
    refine le_trans hcast ?_
    rw [le_div_iff₀ (by exact_mod_cast hL_pos)]
    exact_mod_cast Nat.div_mul_le_self X L
  have h3 : ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm d₁ d₂ : ℝ) ≤
      (X : ℝ) * (∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g) ^ 3 := by
    let f : ℕ × ℕ → ℕ × ℕ × ℕ := fun p =>
      (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    have hinj : Set.InjOn f (Finset.Icc 1 X ×ˢ Finset.Icc 1 X : Set (ℕ × ℕ)) := by
      intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [f, Prod.mk.injEq] at h
      have h1 : a₁ = a₂ := by
        calc a₁ = Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ b₁)).symm
          _ = Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := by rw [h.1, h.2.1]
          _ = a₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left a₂ b₂)
      have h2 : b₁ = b₂ := by
        calc b₁ = Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ b₁)).symm
          _ = Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := by rw [h.1, h.2.2]
          _ = b₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right a₂ b₂)
      exact Prod.ext h1 h2
    have hmaps : Set.MapsTo f (Finset.Icc 1 X ×ˢ Finset.Icc 1 X : Set (ℕ × ℕ))
        (Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X : Set (ℕ × ℕ × ℕ)) := by
      intro ⟨d₁, d₂⟩ hd
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hd ⊢
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd.1.1
      have hg_le : Nat.gcd d₁ d₂ ≤ X := le_trans (Nat.gcd_le_left d₂ hd.1.1) hd.1.2
      have ha_pos : 0 < d₁ / Nat.gcd d₁ d₂ := Nat.div_pos (Nat.gcd_le_left d₂ hd.1.1) hg_pos
      have hb_pos : 0 < d₂ / Nat.gcd d₁ d₂ := Nat.div_pos (Nat.gcd_le_right d₁ hd.2.1) hg_pos
      exact ⟨⟨hg_pos, hg_le⟩, ⟨ha_pos, le_trans (Nat.div_le_self _ _) hd.1.2⟩,
        ⟨hb_pos, le_trans (Nat.div_le_self _ _) hd.2.2⟩⟩
    have hlcm_eq : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ →
        Nat.lcm d₁ d₂ = Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
      intro d₁ d₂ hd₁ hd₂
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd₁
      have hmul := Nat.gcd_mul_lcm d₁ d₂
      have hdvd1 : Nat.gcd d₁ d₂ ∣ d₁ := Nat.gcd_dvd_left d₁ d₂
      have hdvd2 : Nat.gcd d₁ d₂ ∣ d₂ := Nat.gcd_dvd_right d₁ d₂
      nlinarith [Nat.mul_div_cancel' hdvd1, Nat.mul_div_cancel' hdvd2]
    rw [← Finset.sum_product (s := Finset.Icc 1 X) (t := Finset.Icc 1 X) (f := fun p => (X : ℝ) / (Nat.lcm p.1 p.2 : ℝ))]
    have hrew : ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm p.1 p.2 : ℝ) =
        ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
          (X : ℝ) / (((f p).1 : ℝ) * ((f p).2.1 : ℝ) * ((f p).2.2 : ℝ)) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      rw [hlcm_eq p.1 p.2 hp.1.1 hp.2.1]
      push_cast; rfl
    rw [hrew]
    have hle_img : ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
          (X : ℝ) / (((f p).1 : ℝ) * ((f p).2.1 : ℝ) * ((f p).2.2 : ℝ)) ≤
        ∑ q ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
          (X : ℝ) / ((q.1 : ℝ) * (q.2.1 : ℝ) * (q.2.2 : ℝ)) := by
      rw [← Finset.sum_image (f := f) (fun a ha b hb hab => hinj ha hb hab)]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by positivity)
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      exact hmaps hp
    refine le_trans hle_img ?_
    rw [Finset.sum_product, pow_three]
    simp_rw [Finset.sum_product, div_eq_mul_inv, mul_inv, ← mul_assoc]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring_nf; rfl
  have hharm : ∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g ≤ 1 + Real.log X := by
    have heq : ∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g = (harmonic X : ℝ) := by
      clear h1 h2 h3
      induction X with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
        push_cast; ring
    rw [heq]
    simpa using harmonic_le_one_add_log X
  calc ∑ x ∈ Finset.Icc 1 X, (x.divisors.card : ℝ) ^ 2
      = ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X,
          (((Finset.Icc 1 X).filter (fun x => Nat.lcm d₁ d₂ ∣ x)).card : ℝ) := h1
    _ ≤ ∑ d₁ ∈ Finset.Icc 1 X, ∑ d₂ ∈ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm d₁ d₂ : ℝ) := by
        refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
        exact h2 d₁ d₂ (Finset.mem_Icc.mp hd₁).1 (Finset.mem_Icc.mp hd₂).1
    _ ≤ (X : ℝ) * (∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g) ^ 3 := h3
    _ ≤ (X : ℝ) * (1 + Real.log X) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hharm 3)
          (Nat.cast_nonneg X)

lemma type_I_single_d_bound
    (R K_max : ℕ) (hK_max : 3 ≤ K_max)
    (C_exp η_exp M₀ : ℝ) (hC_exp : 0 < C_exp) (hη_exp : 0 < η_exp) (hη_le : η_exp ≤ 1 / 4) (hM₀ : 16 ≤ M₀)
    (hexp : ∀ (A : Finset ℕ) (r₀ : ℕ) (hr₀ : r₀ ∈ A) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R)
        (c : ℕ → ℝ) (hc₀ : c r₀ ≠ 0) (M₁ M₂ : ℝ),
        M₀ ≤ M₁ → M₁ ≤ M₂ → M₂ ≤ 2 * M₁ →
        (∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |c r| * (Nat.descFactorial (r + k - 1) k : ℝ) * M₁ ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|c r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * M₂ ^ (-(r₀ : ℤ)))) →
        let T := |c r₀| * (r₀ : ℝ) * M₂ ^ (-(r₀ : ℤ))
        T ≤ M₂ ^ (K_max - 1) →
        ‖∑ m ∈ Finset.Icc ⌈M₁⌉₊ ⌊M₂⌋₊, ePhase (∑ r ∈ A, c r * (m : ℝ) ^ (-(r : ℤ)))‖ ≤
          C_exp * (M₂ / max T 1 + M₂ ^ (1 - η_exp)))
    (n : ℕ) (P a b : ℝ) (hP1 : 1 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hb2P : b ≤ 2 * P)
    (A : Finset ℕ) (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ R) (r₀ : ℕ) (hr₀ : r₀ ∈ A)
    (h : ℕ → ℤ) (hh₀ : h r₀ ≠ 0) (w : ℝ → ℝ) (W₀ : ℝ) (hW₀ : 0 ≤ W₀)
    (hw_bd : ∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀)
    (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (d : ℕ) (hd1 : 1 ≤ d) (hd_M0 : M₀ ≤ P / (d : ℝ))
    (hdom_d : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
      |(h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) ≤
        (1 / (2 * max (A.card : ℝ) 1)) *
          (|(h r₀ : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r₀)| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))))
    (hT_ub : |(h r₀ : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (K_max - 1)) :
    let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
    ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
        (Real.log k * w (d * k) : ℂ) *
          ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
      4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
        ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
  intro T₀
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hP_pos : 0 < P := by linarith
  have hPd_pos : 0 < P / d := div_pos hP_pos hd_pos
  have hPd_ge16 : 16 ≤ P / d := le_trans hM₀ hd_M0
  have hPd_ge1 : 1 ≤ P / d := by linarith
  by_cases h_empty : ⌊b⌋₊ / d < (⌈a⌉₊ - 1) / d + 1
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.sum_empty, norm_zero]
    positivity
  · have h_empty' : (⌈a⌉₊ - 1) / d + 1 ≤ ⌊b⌋₊ / d := not_lt.mp h_empty
    set a' : ℝ := (⌈a⌉₊ : ℝ) / d
    set b' : ℝ := (⌊b⌋₊ : ℝ) / d
    have hPa' : P / d ≤ a' := div_le_div_of_nonneg_right (le_trans hPa (Nat.le_ceil a)) hd_pos.le
    have hb'2P : b' ≤ 2 * (P / d) := by
      rw [show 2 * (P / d) = (2 * P) / d by ring]
      exact div_le_div_of_nonneg_right (le_trans (Nat.floor_le (by linarith)) hb2P) hd_pos.le
    have hceil_eq : ⌈a'⌉₊ = (⌈a⌉₊ - 1) / d + 1 := by
      have ha_pos : 1 ≤ ⌈a⌉₊ := Nat.ceil_pos.mpr (by linarith)
      apply le_antisymm
      · rw [Nat.ceil_le]
        have h1 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d + 1) * d := by
          have := Nat.lt_mul_div_succ (⌈a⌉₊ - 1) hd1
          rw [mul_comm] at this; omega
        rw [div_le_iff₀ hd_pos]
        exact_mod_cast h1
      · by_contra hlt
        have h1 : ⌈a'⌉₊ ≤ (⌈a⌉₊ - 1) / d := by omega
        have h2 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        have h3 : (⌈a⌉₊ : ℝ) / d ≤ ((⌈a⌉₊ - 1) / d : ℕ) := le_trans h2 (by exact_mod_cast h1)
        rw [div_le_iff₀ hd_pos] at h3
        have h4 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d) * d := by exact_mod_cast h3
        have h5 : ((⌈a⌉₊ - 1) / d) * d ≤ ⌈a⌉₊ - 1 := by
          rw [mul_comm]; exact Nat.div_mul_le_self _ _
        omega
    have hfloor_eq : ⌊b'⌋₊ = ⌊b⌋₊ / d := by
      rw [show b' = (⌊b⌋₊ : ℝ) / (d : ℝ) from rfl, ← Nat.floor_div_eq_div (by positivity) hd_pos,
        Nat.floor_natCast]
    have ha'b' : a' ≤ b' := by
      have h1 : ((⌈a⌉₊ - 1) / d + 1 : ℕ) ≤ ⌊b⌋₊ / d := h_empty'
      have h2 : a' ≤ ((⌈a⌉₊ - 1) / d + 1 : ℕ) := by rw [← hceil_eq]; exact Nat.le_ceil a'
      have h3 : ((⌊b⌋₊ / d : ℕ) : ℝ) ≤ b' := by
        rw [← hfloor_eq]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
      exact le_trans h2 (le_trans (by exact_mod_cast h1) h3)
    let wd : ℝ → ℝ := fun t => Real.log t * w (d * t)
    let W₀' : ℝ := W₀ * (Real.log (2 * P) + 1)
    have hW₀' : 0 ≤ W₀' := mul_nonneg hW₀ (by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * P)])
    have hwd_bd : ∀ t ∈ Set.Icc (P / d) (2 * (P / d)), |wd t| ≤ W₀' := by
      intro t ht
      have ht_ge1 : 1 ≤ t := le_trans hPd_ge1 ht.1
      have ht_le : t ≤ 2 * P := le_trans ht.2 (by
        rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)
      have hdt_mem : d * t ∈ Set.Icc P (2 * P) := ⟨by
        calc P = d * (P / d) := by field_simp [hd_pos.ne']
          _ ≤ d * t := mul_le_mul_of_nonneg_left ht.1 hd_pos.le,
        by
        calc d * t ≤ d * (2 * (P / d)) := mul_le_mul_of_nonneg_left ht.2 hd_pos.le
          _ = 2 * P := by field_simp [hd_pos.ne']⟩
      dsimp only [wd]
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg ht_ge1)]
      calc Real.log t * |w (d * t)|
          ≤ Real.log (2 * P) * W₀ := mul_le_mul (Real.log_le_log (by positivity) ht_le) (hw_bd _ hdt_mem) (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ ≤ W₀ * (Real.log (2 * P) + 1) := by linarith
    have hwd_diff : ContDiffOn ℝ 1 wd (Set.Icc (P / d) (2 * (P / d))) := by
      refine ContDiffOn.mul ?_ ?_
      · refine (contDiffOn_iff_contDiffAt.mpr fun t ht => ?_).mono (fun t ht => ?_)
        · exact Real.contDiffAt_log (by linarith [ht])
        · exact lt_of_lt_of_le hPd_pos ht.1
      · refine hw_diff.comp (contDiff_const.mul contDiff_id).contDiffOn fun t ht => ?_
        exact ⟨by calc P = d * (P / d) := by field_simp [hd_pos.ne']
          _ ≤ d * t := mul_le_mul_of_nonneg_left ht.1 hd_pos.le,
          by calc d * t ≤ d * (2 * (P / d)) := mul_le_mul_of_nonneg_left ht.2 hd_pos.le
          _ = 2 * P := by field_simp [hd_pos.ne']⟩
    have hwd_tv : (∫ t in (P / d)..(2 * (P / d)), |deriv wd t|) ≤ W₀' := by
      have hderiv_eq : Set.EqOn (fun t => |deriv wd t|)
          (fun t => |t⁻¹ * w (d * t) + Real.log t * (d * deriv w (d * t))|) (Set.Ioo (P / d) (2 * (P / d))) := by
        intro t ht
        have ht_pos : 0 < t := lt_trans hPd_pos ht.1
        have hlog_da : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht_pos.ne'
        have hw_da : DifferentiableAt ℝ w (d * t) := by
          have hmem : d * t ∈ Set.Ioo P (2 * P) := ⟨by
            calc P = d * (P / d) := by field_simp [hd_pos.ne']
              _ < d * t := mul_lt_mul_of_pos_left ht.1 hd_pos,
            by
            calc d * t < d * (2 * (P / d)) := mul_lt_mul_of_pos_left ht.2 hd_pos
              _ = 2 * P := by field_simp [hd_pos.ne']⟩
          exact (hw_diff.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hmem.1 hmem.2)
        have hcomp_da : HasDerivAt (fun u => w (d * u)) (deriv w (d * t) * d) t :=
          hw_da.hasDerivAt.comp t ((hasDerivAt_id t).const_mul (d : ℝ))
        have hmul_da := hlog_da.mul hcomp_da
        rw [hmul_da.deriv]
        congr 1; ring
      have hint_abs1 : IntervalIntegrable (fun t => W₀ * t⁻¹) MeasureTheory.volume (P / d) (2 * (P / d)) := by
        refine ContinuousOn.intervalIntegrable fun t ht => ?_
        rw [Set.uIcc_of_le (by linarith : P / d ≤ 2 * (P / d))] at ht
        exact (continuousOn_const.mul (continuousOn_inv₀.mono fun u hu => by
          intro h0; subst h0; linarith [hu.1])).continuousWithinAt
      have hw'_int : IntervalIntegrable (fun u => |deriv w u|) MeasureTheory.volume P (2 * P) :=
        contDiffOn_Icc_abs_deriv_intervalIntegrable (by linarith : P < 2 * P) hw_diff
      have hw'_mul_int : IntervalIntegrable (fun t => |deriv w ((d : ℝ) * t)|)
          MeasureTheory.volume (P / d) (2 * (P / d)) := by
        have h1 := hw'_int
        rw [show P = (d : ℝ) * (P / d) by field_simp [hd_pos.ne'],
          show 2 * P = (d : ℝ) * (2 * (P / d)) by field_simp [hd_pos.ne']] at h1
        exact h1.comp_mul_left (d : ℝ)
      have hint_abs2 : IntervalIntegrable (fun t => Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|))
          MeasureTheory.volume (P / d) (2 * (P / d)) :=
        (hw'_mul_int.const_mul (d : ℝ)).const_mul (Real.log (2 * P))
      have hint_wd : IntervalIntegrable (fun t => |deriv wd t|) MeasureTheory.volume (P / d) (2 * (P / d)) :=
        contDiffOn_Icc_abs_deriv_intervalIntegrable (by linarith : P / d < 2 * (P / d)) hwd_diff
      have hmono : ∫ t in (P / d)..(2 * (P / d)), |deriv wd t| ≤
          ∫ t in (P / d)..(2 * (P / d)), (W₀ * t⁻¹ + Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|)) := by
        refine intervalIntegral.integral_mono_ae_restrict (by linarith) hint_wd (hint_abs1.add hint_abs2) ?_
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
        have hne_pt : ∀ᵐ t ∂MeasureTheory.volume, t ≠ 2 * (P / d) := by
          rw [MeasureTheory.ae_iff]
          simp only [Classical.not_not, Set.ofPred_eq_eq_singleton, MeasureTheory.measure_singleton]
        filter_upwards [hne_pt] with t ht hmem
        have ht_oo : t ∈ Set.Ioo (P / d) (2 * (P / d)) :=
          ⟨(Set.Ioc_subset_Icc_self hmem).1, lt_of_le_of_ne hmem.2 ht⟩
        rw [hderiv_eq t ht_oo]
        have ht_ge1 : 1 ≤ t := le_trans hPd_ge1 ht_oo.1.le
        have ht_le : t ≤ 2 * P := le_trans ht_oo.2.le (by
          rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)
        have hdt_mem : d * t ∈ Set.Icc P (2 * P) := ⟨by
          calc P = d * (P / d) := by field_simp [hd_pos.ne']
            _ ≤ d * t := mul_le_mul_of_nonneg_left ht_oo.1.le hd_pos.le,
          by
          calc d * t ≤ d * (2 * (P / d)) := mul_le_mul_of_nonneg_left ht_oo.2.le hd_pos.le
            _ = 2 * P := by field_simp [hd_pos.ne']⟩
        calc |t⁻¹ * w (d * t) + Real.log t * (d * deriv w (d * t))|
            ≤ |t⁻¹ * w (d * t)| + |Real.log t * (d * deriv w (d * t))| := abs_add_le _ _
          _ ≤ W₀ * t⁻¹ + Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|) := by
              refine add_le_add ?_ ?_
              · rw [abs_mul, abs_of_pos (inv_pos.mpr (lt_trans hPd_pos ht_oo.1)), mul_comm]
                exact mul_le_mul_of_nonneg_right (hw_bd _ hdt_mem) (by positivity)
              · rw [abs_mul, abs_of_nonneg (Real.log_nonneg ht_ge1), abs_mul, abs_of_pos hd_pos]
                exact mul_le_mul (Real.log_le_log (by positivity) ht_le) le_rfl (by positivity)
                  (Real.log_nonneg (by linarith))
      have hint1_val : ∫ t in (P / d)..(2 * (P / d)), W₀ * t⁻¹ ≤ W₀ := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_of_pos hPd_pos (by linarith : 0 < 2 * (P / d)),
          show (2 * (P / d)) / (P / d) = 2 by field_simp [hPd_pos.ne', hd_pos.ne']]
        have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        exact mul_le_of_le_one_right hW₀ hlog2
      have hint2_val : ∫ t in (P / d)..(2 * (P / d)), Real.log (2 * P) * ((d : ℝ) * |deriv w (d * t)|) ≤
          W₀ * Real.log (2 * P) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have hcomp : ∫ t in (P / d)..(2 * (P / d)), |deriv w (d * t)| =
            (d : ℝ)⁻¹ * ∫ u in P..(2 * P), |deriv w u| := by
          have h := intervalIntegral.integral_comp_mul_left (fun u => |deriv w u|) (c := (d : ℝ))
            (a := P / d) (b := 2 * (P / d))
          rw [show (d : ℝ) * (P / d) = P by field_simp [hd_pos.ne'],
            show (d : ℝ) * (2 * (P / d)) = 2 * P by field_simp [hd_pos.ne'], smul_eq_mul] at h
          exact h
        rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hd_pos.ne', one_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hw_tv (Real.log_nonneg (by linarith))
      rw [intervalIntegral.integral_add hint_abs1 hint_abs2] at hmono
      linarith
    set E : ℝ := max C_exp 3 *
      ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := by positivity
    have hsum_bd : ∀ u : ℕ, ⌈a'⌉₊ ≤ u → u ≤ ⌊b'⌋₊ →
        ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤ E := by
      intro u hau hub
      have hu_ge : P / d ≤ (u : ℝ) := by
        have h1 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        exact le_trans hPa' (le_trans h1 (by exact_mod_cast hau))
      have hu_le : (u : ℝ) ≤ 2 * (P / d) := by
        have h1 : (⌊b'⌋₊ : ℝ) ≤ b' := Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
        exact le_trans (by exact_mod_cast hub) (le_trans h1 hb'2P)
      have h_eq_phase : ∀ k : ℕ, 1 ≤ k →
          ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
          ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
        intro k hk
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Nat.cast_mul, mul_pow, zpow_neg, zpow_natCast]
        ring
      have hsum_eq : ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
          ∑ k ∈ Finset.Icc ⌈a'⌉₊ u,
            ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
        refine Finset.sum_congr rfl fun k hk => h_eq_phase k (by
          have h1 : (1 : ℝ) ≤ a' := le_trans hPd_ge1 hPa'
          have h2 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (by linarith)
          exact le_trans h2 (Finset.mem_Icc.mp hk).1)
      rw [hsum_eq]
      let cd : ℕ → ℝ := fun r => (h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)
      have hcd0 : cd r₀ ≠ 0 := by
        dsimp only [cd]
        have hn_pos : (0 : ℝ) < n := by
          by_contra h0
          have : n = 0 := by exact_mod_cast le_antisymm (not_lt.mp h0) (Nat.cast_nonneg n)
          subst this; linarith
        have hh0R : (h r₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hh₀
        positivity
      have hM0_a' : M₀ ≤ a' := le_trans hd_M0 hPa'
      have ha'u : a' ≤ (u : ℝ) := le_trans (Nat.le_ceil a') (by exact_mod_cast hau)
      have hu2a' : (u : ℝ) ≤ 2 * a' := le_trans hu_le (by linarith [hPa'])
      have hdom_u : ∀ k ∈ Finset.Icc 1 K_max, ∀ r ∈ A, r ≠ r₀ →
          |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a' ^ (-(r : ℤ)) ≤
            (1 / (2 * max (A.card : ℝ) 1)) *
              (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) := by
        intro k hk r hr hne
        have ha'_pow : a' ^ (-(r : ℤ)) ≤ (P / d) ^ (-(r : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hPd_pos r) (pow_le_pow_left₀ hPd_pos.le hPa' r)
        have hu_pow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) (by linarith [hu_le]) r₀)
        calc |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * a' ^ (-(r : ℤ))
            ≤ |cd r| * (Nat.descFactorial (r + k - 1) k : ℝ) * (P / d) ^ (-(r : ℤ)) :=
              mul_le_mul_of_nonneg_left ha'_pow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
          _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (2 * P / d) ^ (-(r₀ : ℤ))) :=
              hdom_d k hk r hr hne
          _ ≤ (1 / (2 * max (A.card : ℝ) 1)) *
                (|cd r₀| * (Nat.descFactorial (r₀ + k - 1) k : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_pow
                (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (by positivity)
      have hTu_ub : |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (K_max - 1) := by
        have h1 : (u : ℝ) ^ (-(r₀ : ℤ)) ≤ (P / d) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hPd_pos r₀) (pow_le_pow_left₀ hPd_pos.le hu_ge r₀)
        have h2 : (P / d) ^ (-(r₀ : ℤ)) ≤ (2 : ℝ) ^ R * (2 * P / d) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, show 2 * P / d = 2 * (P / d) by ring,
            mul_pow, mul_inv, mul_comm ((2 : ℝ) ^ r₀)⁻¹ _, ← mul_assoc]
          have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
          rw [inv_mul_le_iff₀ (by positivity)]
          calc (P / d) ^ r₀ * (2 : ℝ) ^ r₀ ≤ (P / d) ^ r₀ * (2 : ℝ) ^ R :=
                mul_le_mul_of_nonneg_left h2r (by positivity)
            _ = (2 : ℝ) ^ R * (P / d) ^ r₀ := mul_comm _ _
        have h3 : (P / d) ^ (K_max - 1) ≤ (u : ℝ) ^ (K_max - 1) :=
          pow_le_pow_left₀ hPd_pos.le hu_ge _
        calc |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ))
            ≤ |cd r₀| * (r₀ : ℝ) * (P / d) ^ (-(r₀ : ℤ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (P / d) ^ (K_max - 1) := hT_ub
          _ ≤ (u : ℝ) ^ (K_max - 1) := h3
      have hhexp := hexp A r₀ hr₀ hA cd hcd0 a' (u : ℝ) hM0_a' ha'u hu2a' hdom_u hTu_ub
      rw [Nat.floor_natCast] at hhexp
      have hT_ge : (2 : ℝ) ^ (-(R : ℤ) - 1) * T₀ ≤ |cd r₀| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
        dsimp only [cd, T₀]
        have hr0_1 : (1 : ℝ) ≤ r₀ := by exact_mod_cast (hA r₀ hr₀).1
        have hupow : (2 * P / d) ^ (-(r₀ : ℤ)) ≤ (u : ℝ) ^ (-(r₀ : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) (by linarith [hu_le]) r₀)
        have h2pow : (2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ)) ≤ (2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ)) := by
          rw [show (2 * P / d) = (2 * P) / d by ring, zpow_sub₀ (by norm_num),
            zpow_neg (2 : ℝ) (R : ℤ), zpow_natCast (2 : ℝ) R, zpow_one,
            zpow_neg P (r₀ : ℤ), zpow_natCast P r₀,
            zpow_neg ((2 * P) / d) (r₀ : ℤ), zpow_natCast ((2 * P) / d) r₀, div_pow, inv_div]
          rw [mul_pow, ← div_eq_mul_inv]
          field_simp [hd_pos.ne', hP_pos.ne']
          have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
          linarith [h2r]
        calc (2 : ℝ) ^ (-(R : ℤ) - 1) * (|(h r₀ : ℝ)| * n / P ^ r₀)
            = |(h r₀ : ℝ)| * n * ((2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ))) := by
                rw [zpow_neg, zpow_natCast]; ring
          _ ≤ |(h r₀ : ℝ)| * n * ((2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                mul_le_mul_of_nonneg_left h2pow (by positivity)
          _ ≤ |(h r₀ : ℝ) * n / (2 * (d : ℝ) ^ r₀)| * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
                rw [abs_div, abs_mul, abs_of_pos (a := (n : ℝ)) (by positivity),
                  abs_of_pos (a := 2 * (d : ℝ) ^ r₀) (by positivity)]
                have hle1 : |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) ≤
                    |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left hr0_1 (by positivity)) hupow (by positivity) (by positivity)
                linarith [show |(h r₀ : ℝ)| * n * ((2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) =
                  |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) by ring]
      refine le_trans hhexp ?_
      refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (by positivity)
      refine add_le_add ?_ ?_
      · exact div_le_div₀ (by positivity) (by linarith [hu_le]) (by positivity) (max_le_max hT_ge le_rfl)
      · refine Real.rpow_le_rpow (by positivity) (by linarith [hu_le]) (by linarith)
    have hps := partial_summation_Icc (P := P / d) (a := a') (b := b') (W₀ := W₀') (E := E)
      hPd_pos hPa' ha'b' hb'2P hW₀' hE_nn hwd_bd hwd_diff hwd_tv hsum_bd
    rw [hceil_eq, hfloor_eq] at hps
    calc ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
            (Real.log k * w (d * k) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖
        ≤ 2 * W₀' * E := by simpa [wd] using hps
      _ = 2 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          dsimp only [W₀', E]; ring
      _ ≤ 4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          have hnn : 0 ≤ W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
              ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by positivity
          linarith

lemma factorial_two_mul_le (m : ℕ) :
    (2 * m).factorial ≤ 4 ^ m * (m.factorial) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h1, Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m),
      Nat.factorial_succ m, pow_succ 4 m]
    have h2 : (2 * m + 1 + 1) * (2 * m + 1) ≤ 4 * (m + 1) ^ 2 := by nlinarith
    calc (2 * m + 1 + 1) * ((2 * m + 1) * (2 * m).factorial)
        = ((2 * m + 1 + 1) * (2 * m + 1)) * (2 * m).factorial := by ring
      _ ≤ (4 * (m + 1) ^ 2) * (4 ^ m * (m.factorial) ^ 2) :=
          Nat.mul_le_mul h2 ih
      _ = 4 ^ m * 4 * ((m + 1) * m.factorial) ^ 2 := by ring

lemma log_factorial_eq_sum_vonMangoldt (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ k ∈ Finset.Icc 1 n, ((n / k : ℕ) : ℝ) * (ArithmeticFunction.vonMangoldt k : ℝ) := by
  have hlog : Real.log (n.factorial : ℝ) = ∑ m ∈ Finset.Icc 1 n, Real.log (m : ℝ) := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ← ih, Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) (by positivity), add_comm]
  rw [hlog]
  by_cases hn : n = 0
  · subst hn; simp
  · have hn1 : 1 ≤ n := by omega
    have hvm : ∀ m ∈ Finset.Icc 1 n,
        Real.log (m : ℝ) =
          ∑ k ∈ m.divisors.filter (fun k => 1 ≤ k ∧ k ≤ n), (ArithmeticFunction.vonMangoldt k : ℝ) := by
      intro m hm
      rw [← ArithmeticFunction.vonMangoldt_sum]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [Finset.mem_filter]
      refine ⟨fun hk => ⟨hk, Nat.pos_of_mem_divisors hk,
        le_trans (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 (Nat.dvd_of_mem_divisors hk)) (Finset.mem_Icc.mp hm).2⟩,
        fun ⟨hk, _⟩ => hk⟩
    have h_c := sum_Icc_divisors_filter (A₀ := 1) (B₀ := n) (L := 1) (U := n) le_rfl le_rfl
      (fun k _ => (ArithmeticFunction.vonMangoldt k : ℂ))
    have h_re := congr_arg Complex.re h_c
    simp only [Complex.re_sum, Complex.ofReal_re] at h_re
    rw [Finset.sum_congr rfl hvm, h_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (1 - 1) / k + 1 = 1 by simp, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]

lemma sum_vonMangoldt_dyadic_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc (m + 1) (2 * m), (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      (m : ℝ) * Real.log 4 := by
  have h1 := log_factorial_eq_sum_vonMangoldt (2 * m)
  have h2 := log_factorial_eq_sum_vonMangoldt m
  have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 (2 * m) := fun k hk =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, by have := (Finset.mem_Icc.mp hk).2; omega⟩
  have h2_ext : ∑ k ∈ Finset.Icc 1 m, ((m / k : ℕ) : ℝ) * (ArithmeticFunction.vonMangoldt k : ℝ) =
      ∑ k ∈ Finset.Icc 1 (2 * m), ((m / k : ℕ) : ℝ) * (ArithmeticFunction.vonMangoldt k : ℝ) := by
    refine Finset.sum_subset hsub fun k hk hnot => ?_
    rw [Finset.mem_Icc] at hk hnot
    have hgt : m < k := by omega
    rw [Nat.div_eq_of_lt hgt]; simp
  rw [h2_ext] at h2
  have hdiff : Real.log ((2 * m).factorial : ℝ) - 2 * Real.log (m.factorial : ℝ) =
      ∑ k ∈ Finset.Icc 1 (2 * m),
        (((2 * m / k : ℕ) : ℝ) - 2 * ((m / k : ℕ) : ℝ)) * (ArithmeticFunction.vonMangoldt k : ℝ) := by
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have h_coeff_nn : ∀ k ∈ Finset.Icc 1 (2 * m),
      0 ≤ (((2 * m / k : ℕ) : ℝ) - 2 * ((m / k : ℕ) : ℝ)) * (ArithmeticFunction.vonMangoldt k : ℝ) := by
    intro k hk
    refine mul_nonneg ?_ ArithmeticFunction.vonMangoldt_nonneg
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hle : 2 * (m / k) ≤ 2 * m / k :=
      (Nat.le_div_iff_mul_le hk_pos).mpr (by nlinarith [Nat.div_mul_le_self m k])
    have hleR : (2 * (m / k : ℕ) : ℝ) ≤ (2 * m / k : ℕ) := by exact_mod_cast hle
    linarith
  have h_upper_sub : Finset.Icc (m + 1) (2 * m) ⊆ Finset.Icc 1 (2 * m) := fun k hk =>
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hk).1; omega, (Finset.mem_Icc.mp hk).2⟩
  have h_upper_le : ∑ k ∈ Finset.Icc (m + 1) (2 * m), (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      Real.log ((2 * m).factorial : ℝ) - 2 * Real.log (m.factorial : ℝ) := by
    rw [hdiff]
    calc ∑ k ∈ Finset.Icc (m + 1) (2 * m), (ArithmeticFunction.vonMangoldt k : ℝ)
        ≤ ∑ k ∈ Finset.Icc (m + 1) (2 * m),
            (((2 * m / k : ℕ) : ℝ) - 2 * ((m / k : ℕ) : ℝ)) * (ArithmeticFunction.vonMangoldt k : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          have hm_div : m / k = 0 := Nat.div_eq_of_lt hk.1
          have h2m_div : 1 ≤ 2 * m / k := Nat.div_pos hk.2 (by omega)
          have h2m_R : (1 : ℝ) ≤ (2 * m / k : ℕ) := by exact_mod_cast h2m_div
          rw [hm_div, Nat.cast_zero, mul_zero, sub_zero]
          exact le_mul_of_one_le_left ArithmeticFunction.vonMangoldt_nonneg h2m_R
      _ ≤ ∑ k ∈ Finset.Icc 1 (2 * m),
            (((2 * m / k : ℕ) : ℝ) - 2 * ((m / k : ℕ) : ℝ)) * (ArithmeticFunction.vonMangoldt k : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_upper_sub h_coeff_nn
  have h_fact_le : Real.log ((2 * m).factorial : ℝ) - 2 * Real.log (m.factorial : ℝ) ≤
      (m : ℝ) * Real.log 4 := by
    have hle : ((2 * m).factorial : ℝ) ≤ (4 : ℝ) ^ m * ((m.factorial : ℝ) ^ 2) := by
      exact_mod_cast factorial_two_mul_le m
    have hlog_le := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog_le
    linarith
  exact le_trans h_upper_le h_fact_le

lemma sum_vonMangoldt_two_pow_le (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 ^ K), (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      (2 ^ K : ℝ) * Real.log 4 := by
  induction K with
  | zero =>
    simp [ArithmeticFunction.vonMangoldt_apply_one]
    exact Real.log_nonneg (by norm_num)
  | succ K ih =>
    have hsplit : Finset.Icc 1 (2 ^ (K + 1)) =
        Finset.Icc 1 (2 ^ K) ∪ Finset.Icc (2 ^ K + 1) (2 * 2 ^ K) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union, pow_succ']; omega
    have hdisj : Disjoint (Finset.Icc 1 (2 ^ K)) (Finset.Icc (2 ^ K + 1) (2 * 2 ^ K)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2; rw [Finset.mem_Icc] at hk1 hk2; omega
    rw [hsplit, Finset.sum_union hdisj]
    have hdy := sum_vonMangoldt_dyadic_le (2 ^ K) (by positivity)
    push_cast at hdy ⊢
    linarith

lemma sum_vonMangoldt_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt k : ℝ) ≤ (Real.log 4 + 4) * (X : ℝ) := by
  let K := Nat.log 2 X + 1
  have hX_lt : X < 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) X
  have h2K_le : 2 ^ K ≤ 2 * X := by
    dsimp only [K]
    rw [pow_succ']
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 (2 ^ K) := fun k hk =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 hX_lt.le⟩
  have h1 : ∑ k ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      (2 ^ K : ℝ) * Real.log 4 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg))
      (sum_vonMangoldt_two_pow_le K)
  have h2K_R : (2 ^ K : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast h2K_le
  have hlog4_le : Real.log 4 ≤ 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hX_nn : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  nlinarith

end BrocardFormalization

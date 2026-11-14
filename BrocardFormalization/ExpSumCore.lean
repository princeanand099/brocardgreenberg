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
      have hdiv_eq : x.divisors = (Finset.Icc 1 X).filter (· ∣ x) := by
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨fun ⟨hd, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hd hx_pos,
          le_trans (Nat.le_of_dvd hx_pos hd) (Finset.mem_Icc.mp hx).2⟩, hd⟩,
          fun ⟨_, hd⟩ => ⟨hd, hx_pos.ne'⟩⟩
      have hcard_sum : (x.divisors.card : ℝ) = ∑ d ∈ Finset.Icc 1 X, if d ∣ x then (1 : ℝ) else 0 := by
        rw [hdiv_eq, Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
      rw [sq, hcard_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₂ _ => ?_
      by_cases h1 : d₁ ∣ x <;> by_cases h2 : d₂ ∣ x
      · have hl : Nat.lcm d₁ d₂ ∣ x := Nat.lcm_dvd h1 h2
        simp [h1, h2, hl]
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
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
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
    have hinj : ∀ a ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, ∀ b ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
        f a = f b → a = b := by
      intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [f, Prod.mk.injEq] at h
      have h1 : a₁ = a₂ := by
        calc a₁ = Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ b₁)).symm
          _ = Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := by rw [h.2.1, h.1]
          _ = a₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left a₂ b₂)
      have h2 : b₁ = b₂ := by
        calc b₁ = Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ b₁)).symm
          _ = Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := by rw [h.2.2, h.1]
          _ = b₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right a₂ b₂)
      exact Prod.ext h1 h2
    have hmaps : ∀ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
        f p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X := by
      intro ⟨d₁, d₂⟩ hd
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hd
      rw [Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
      dsimp only [f]
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd.1.1
      have hg_le : Nat.gcd d₁ d₂ ≤ X := le_trans (Nat.gcd_le_left d₂ hd.1.1) hd.1.2
      have ha_pos : 0 < d₁ / Nat.gcd d₁ d₂ := Nat.div_pos (Nat.gcd_le_left d₂ hd.1.1) hg_pos
      have hb_pos : 0 < d₂ / Nat.gcd d₁ d₂ := Nat.div_pos (Nat.gcd_le_right d₁ hd.2.1) hg_pos
      exact ⟨⟨hg_pos, hg_le⟩, ⟨ha_pos, le_trans (Nat.div_le_self _ _) hd.1.2⟩,
        ⟨hb_pos, le_trans (Nat.div_le_self _ _) hd.2.2⟩⟩
    have hlcm_eq : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ →
        Nat.lcm d₁ d₂ = Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
      intro d₁ d₂ hd₁ _
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd₁
      have hmul := Nat.gcd_mul_lcm d₁ d₂
      have hd1_eq : Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) = d₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left d₁ d₂)
      have hd2_eq : Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂) = d₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right d₁ d₂)
      have hprod : Nat.gcd d₁ d₂ * Nat.lcm d₁ d₂ =
          Nat.gcd d₁ d₂ * (Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂)) := by
        calc Nat.gcd d₁ d₂ * Nat.lcm d₁ d₂ = d₁ * d₂ := hmul
          _ = (Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂)) * (Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂)) := by
              rw [hd1_eq, hd2_eq]
          _ = Nat.gcd d₁ d₂ * (Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hg_pos hprod
    rw [← Finset.sum_product (s := Finset.Icc 1 X) (t := Finset.Icc 1 X) (f := fun p => (X : ℝ) / (Nat.lcm p.1 p.2 : ℝ))]
    let g_fn : ℕ × ℕ × ℕ → ℝ := fun q => (X : ℝ) / ((q.1 : ℝ) * (q.2.1 : ℝ) * (q.2.2 : ℝ))
    have hrew : ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, (X : ℝ) / (Nat.lcm p.1 p.2 : ℝ) =
        ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, g_fn (f p) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      rw [hlcm_eq p.1 p.2 hp.1.1 hp.2.1]
      dsimp only [g_fn]; push_cast; rfl
    rw [hrew]
    have hle_img : ∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, g_fn (f p) ≤
        ∑ q ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, g_fn q := by
      rw [← Finset.sum_image (f := g_fn) (g := f) (fun a ha b hb hab => hinj a ha b hb hab)]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by dsimp only [g_fn]; positivity)
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      exact hmaps p hp
    have hprod_eq : ∑ q ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X ×ˢ Finset.Icc 1 X, g_fn q =
        (X : ℝ) * (∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g) ^ 3 := by
      dsimp only [g_fn]
      rw [Finset.sum_product, Finset.sum_product]
      have h_inner : ∀ a b : ℕ, ∑ c ∈ Finset.Icc 1 X, (X : ℝ) / ((a : ℝ) * (b : ℝ) * (c : ℝ)) =
          ((X : ℝ) * ((1 : ℝ) / a) * ((1 : ℝ) / b)) * ∑ c ∈ Finset.Icc 1 X, (1 : ℝ) / c := by
        intro a b
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => by ring
      simp_rw [h_inner, ← Finset.sum_mul]
      have h_mid : ∀ a : ℕ, ∑ b ∈ Finset.Icc 1 X, (X : ℝ) * ((1 : ℝ) / a) * ((1 : ℝ) / b) =
          ((X : ℝ) * ((1 : ℝ) / a)) * ∑ b ∈ Finset.Icc 1 X, (1 : ℝ) / b := by
        intro a
        rw [Finset.mul_sum]
      simp_rw [h_mid, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    exact le_trans hle_img (le_of_eq hprod_eq)
  have hharm : ∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g ≤ 1 + Real.log X := by
    have heq : ∑ g ∈ Finset.Icc 1 X, (1 : ℝ) / g = (harmonic X : ℝ) := by
      clear hX h1 h2 h3
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

lemma abel_summation_Icc {A₀ B₀ : ℕ} {W_sup W_tv E : ℝ} {g : ℕ → ℝ} {f : ℕ → ℂ}
    (h_le : A₀ ≤ B₀) (hW_sup : 0 ≤ W_sup) (_hW_tv : 0 ≤ W_tv) (hE : 0 ≤ E)
    (hg_bd : ∀ m ∈ Finset.Icc A₀ B₀, |g m| ≤ W_sup)
    (hg_tv : ∑ m ∈ Finset.Ico A₀ B₀, |g (m + 1) - g m| ≤ W_tv)
    (hsum_bd : ∀ u : ℕ, A₀ ≤ u → u ≤ B₀ → ‖∑ m ∈ Finset.Icc A₀ u, f m‖ ≤ E) :
    ‖∑ m ∈ Finset.Icc A₀ B₀, (g m : ℂ) * f m‖ ≤ (W_sup + W_tv) * E := by
  let S : ℕ → ℂ := fun k => ∑ m ∈ Finset.Icc A₀ k, f m
  have hS_bd : ∀ k : ℕ, A₀ ≤ k → k ≤ B₀ → ‖S k‖ ≤ E := hsum_bd
  have h_abel : ∑ m ∈ Finset.Icc A₀ B₀, (g m : ℂ) * f m =
      (g B₀ : ℂ) * S B₀ -
        ∑ m ∈ Finset.Ico A₀ B₀, ((g (m + 1) : ℂ) - (g m : ℂ)) * S m := by
    have hf_eq : ∀ m : ℕ, A₀ ≤ m → f m = S m - (if m = A₀ then 0 else S (m - 1)) := by
      intro m hm
      by_cases hmA : m = A₀
      · subst hmA; simp [S]
      · simp only [hmA, ↓reduceIte, S]
        rw [show Finset.Icc A₀ m = insert m (Finset.Icc A₀ (m - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
        rw [Finset.sum_insert (by simp; omega)]
        ring
    have h1 : ∑ m ∈ Finset.Icc A₀ B₀, (g m : ℂ) * f m =
        ∑ m ∈ Finset.Icc A₀ B₀, (g m : ℂ) * S m -
        ∑ m ∈ Finset.Icc A₀ B₀, (g m : ℂ) * (if m = A₀ then 0 else S (m - 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hf_eq m (Finset.mem_Icc.mp hm).1]; ring
    rw [h1]
    have hshift : ∑ m ∈ Finset.Icc A₀ B₀, (g m : ℂ) * (if m = A₀ then 0 else S (m - 1)) =
        ∑ m ∈ Finset.Ico A₀ B₀, (g (m + 1) : ℂ) * S m := by
      have hIcc : Finset.Icc A₀ B₀ = insert A₀ (Finset.Icc (A₀ + 1) B₀) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_nbij' (fun m => m - 1) (fun m => m + 1) ?_ ?_ ?_ ?_ ?_
      · intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.mem_Ico]; omega
      · intro m hm; rw [Finset.mem_Ico] at hm; rw [Finset.mem_Icc]; omega
      · intro m hm; rw [Finset.mem_Icc] at hm; omega
      · intro m _; omega
      · intro m hm
        rw [Finset.mem_Icc] at hm
        have hne : m ≠ A₀ := by omega
        simp [hne, show m - 1 + 1 = m by omega]
    have hIcc_top : Finset.Icc A₀ B₀ = insert B₀ (Finset.Ico A₀ B₀) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hshift, hIcc_top, Finset.sum_insert (by simp)]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  rw [h_abel]
  have hterm1 : ‖(g B₀ : ℂ) * S B₀‖ ≤ W_sup * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hg_bd B₀ (Finset.mem_Icc.mpr ⟨h_le, le_rfl⟩)) (hS_bd B₀ h_le le_rfl) (norm_nonneg _) hW_sup
  have hterm2 : ‖∑ m ∈ Finset.Ico A₀ B₀, ((g (m + 1) : ℂ) - (g m : ℂ)) * S m‖ ≤ W_tv * E := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ m ∈ Finset.Ico A₀ B₀, ‖((g (m + 1) : ℂ) - (g m : ℂ)) * S m‖
        = ∑ m ∈ Finset.Ico A₀ B₀, |g (m + 1) - g m| * ‖S m‖ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [norm_mul, show (g (m + 1) : ℂ) - (g m : ℂ) = ((g (m + 1) - g m : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ m ∈ Finset.Ico A₀ B₀, |g (m + 1) - g m| * E := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.mem_Ico] at hm
          exact mul_le_mul_of_nonneg_left (hS_bd m hm.1 hm.2.le) (abs_nonneg _)
      _ = (∑ m ∈ Finset.Ico A₀ B₀, |g (m + 1) - g m|) * E := (Finset.sum_mul _ _ _).symm
      _ ≤ W_tv * E := mul_le_mul_of_nonneg_right hg_tv hE
  calc ‖(g B₀ : ℂ) * S B₀ - ∑ m ∈ Finset.Ico A₀ B₀, ((g (m + 1) : ℂ) - (g m : ℂ)) * S m‖
      ≤ ‖(g B₀ : ℂ) * S B₀‖ + ‖∑ m ∈ Finset.Ico A₀ B₀, ((g (m + 1) : ℂ) - (g m : ℂ)) * S m‖ := norm_sub_le _ _
    _ ≤ W_sup * E + W_tv * E := add_le_add hterm1 hterm2
    _ = (W_sup + W_tv) * E := by ring

lemma discrete_tv_scale_le {P W₀ : ℝ} {w : ℝ → ℝ}
    (hP : 0 < P) (hw_diff : ContDiffOn ℝ 1 w (Set.Icc P (2 * P)))
    (hw_tv : (∫ t in P..(2 * P), |deriv w t|) ≤ W₀)
    (d A₀ B₀ : ℕ) (h_le : A₀ ≤ B₀)
    (hA₀_ge : P ≤ ((d * A₀ : ℕ) : ℝ)) (hB₀_le : ((d * B₀ : ℕ) : ℝ) ≤ 2 * P) :
    ∑ m ∈ Finset.Ico A₀ B₀, |w ((d * (m + 1) : ℕ) : ℝ) - w ((d * m : ℕ) : ℝ)| ≤ W₀ := by
  have h_deriv_eq : ∀ t ∈ Set.Ioo P (2 * P),
      deriv w t = derivWithin w (Set.Icc P (2 * P)) t := by
    intro t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have h_deriv_cont : ContinuousOn (derivWithin w (Set.Icc P (2 * P))) (Set.Icc P (2 * P)) :=
    hw_diff.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl
  have h_tv_step : ∀ m ∈ Finset.Ico A₀ B₀,
      |w ((d * (m + 1) : ℕ) : ℝ) - w ((d * m : ℕ) : ℝ)| ≤
        ∫ t in ((d * m : ℕ) : ℝ)..((d * (m + 1) : ℕ) : ℝ), |deriv w t| := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm_ge : P ≤ ((d * m : ℕ) : ℝ) :=
      le_trans hA₀_ge (by exact_mod_cast Nat.mul_le_mul_left d hm.1)
    have hm1_le : ((d * (m + 1) : ℕ) : ℝ) ≤ 2 * P :=
      le_trans (by exact_mod_cast Nat.mul_le_mul_left d hm.2) hB₀_le
    have hm_le : ((d * m : ℕ) : ℝ) ≤ ((d * (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left d (Nat.le_succ m)
    have hsub : Set.Icc ((d * m : ℕ) : ℝ) ((d * (m + 1) : ℕ) : ℝ) ⊆ Set.Icc P (2 * P) := fun t ht =>
      ⟨le_trans hm_ge ht.1, le_trans ht.2 hm1_le⟩
    have hcont : ContinuousOn w (Set.Icc ((d * m : ℕ) : ℝ) ((d * (m + 1) : ℕ) : ℝ)) :=
      hw_diff.continuousOn.mono hsub
    have hderiv : ∀ t ∈ Set.Ioo ((d * m : ℕ) : ℝ) ((d * (m + 1) : ℕ) : ℝ), HasDerivAt w (deriv w t) t := by
      intro t ht
      have hmem : t ∈ Set.Ioo P (2 * P) := ⟨lt_of_le_of_lt hm_ge ht.1, lt_of_lt_of_le ht.2 hm1_le⟩
      have hdiff_within := hw_diff.differentiableOn one_ne_zero t (Set.Ioo_subset_Icc_self hmem)
      exact (hdiff_within.differentiableAt (Icc_mem_nhds hmem.1 hmem.2)).hasDerivAt
    have hint_within : IntervalIntegrable (derivWithin w (Set.Icc P (2 * P)))
        MeasureTheory.volume ((d * m : ℕ) : ℝ) ((d * (m + 1) : ℕ) : ℝ) :=
      (h_deriv_cont.mono hsub).intervalIntegrable_of_Icc hm_le
    have hae_sub : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc ((d * m : ℕ) : ℝ) ((d * (m + 1) : ℕ) : ℝ)),
        derivWithin w (Set.Icc P (2 * P)) t = deriv w t := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
      have hne_pt : ∀ᵐ t ∂MeasureTheory.volume, t ≠ ((d * (m + 1) : ℕ) : ℝ) := by
        rw [MeasureTheory.ae_iff]
        simp only [Classical.not_not, Set.ofPred_eq_eq_singleton, MeasureTheory.measure_singleton]
      filter_upwards [hne_pt] with t ht_ne ht_mem
      rw [Set.uIoc_of_le hm_le] at ht_mem
      have ht_lt : t < ((d * (m + 1) : ℕ) : ℝ) := lt_of_le_of_ne ht_mem.2 ht_ne
      exact (h_deriv_eq t ⟨lt_of_le_of_lt hm_ge ht_mem.1, lt_of_lt_of_le ht_lt hm1_le⟩).symm
    have hmp := intervalIntegrable_iff.mp hint_within
    have hint : IntervalIntegrable (deriv w) MeasureTheory.volume ((d * m : ℕ) : ℝ) ((d * (m + 1) : ℕ) : ℝ) :=
      intervalIntegrable_iff.mpr ⟨hmp.1.congr hae_sub, hmp.2.congr hae_sub⟩
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hm_le hcont hderiv hint
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hm_le
  have h_tv_abs_int : IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume P (2 * P) :=
    contDiffOn_Icc_abs_deriv_intervalIntegrable (by linarith) hw_diff
  refine le_trans (Finset.sum_le_sum h_tv_step) ?_
  have h_adj : ∀ k : ℕ, A₀ ≤ k → k ≤ B₀ →
      ∑ m ∈ Finset.Ico A₀ k, ∫ t in ((d * m : ℕ) : ℝ)..((d * (m + 1) : ℕ) : ℝ), |deriv w t| =
        ∫ t in ((d * A₀ : ℕ) : ℝ)..((d * k : ℕ) : ℝ), |deriv w t| := by
    intro k hkA hkB
    induction k with
    | zero =>
      have hA0 : A₀ = 0 := by omega
      rw [hA0]; simp
    | succ k ih =>
      by_cases hk : A₀ ≤ k
      · rw [Finset.sum_Ico_succ_top hk, ih hk (by omega)]
        have h1 : IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume ((d * A₀ : ℕ) : ℝ) ((d * k : ℕ) : ℝ) :=
          h_tv_abs_int.mono_set (by
            rw [Set.uIcc_of_le (by exact_mod_cast Nat.mul_le_mul_left d hk), Set.uIcc_of_le (by linarith)]
            have hk_le : ((d * k : ℕ) : ℝ) ≤ 2 * P :=
              le_trans (by exact_mod_cast Nat.mul_le_mul_left d (by omega : k ≤ B₀)) hB₀_le
            exact fun t ht => ⟨le_trans hA₀_ge ht.1, le_trans ht.2 hk_le⟩)
        have h2 : IntervalIntegrable (fun t => |deriv w t|) MeasureTheory.volume ((d * k : ℕ) : ℝ) ((d * (k + 1) : ℕ) : ℝ) :=
          h_tv_abs_int.mono_set (by
            rw [Set.uIcc_of_le (by exact_mod_cast Nat.mul_le_mul_left d (Nat.le_succ k)), Set.uIcc_of_le (by linarith)]
            have hk_ge : P ≤ ((d * k : ℕ) : ℝ) := le_trans hA₀_ge (by exact_mod_cast Nat.mul_le_mul_left d hk)
            have hk1_le : ((d * (k + 1) : ℕ) : ℝ) ≤ 2 * P :=
              le_trans (by exact_mod_cast Nat.mul_le_mul_left d hkB) hB₀_le
            exact fun t ht => ⟨le_trans hk_ge ht.1, le_trans ht.2 hk1_le⟩)
        exact intervalIntegral.integral_add_adjacent_intervals h1 h2
      · have hA_eq : A₀ = k + 1 := by omega
        rw [hA_eq]; simp
  rw [h_adj B₀ h_le le_rfl]
  refine le_trans (intervalIntegral.integral_mono_interval hA₀_ge
    (by exact_mod_cast Nat.mul_le_mul_left d h_le) hB₀_le
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_tv_abs_int) hw_tv

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
  have hlog2P1_nn : 0 ≤ Real.log (2 * P) + 1 := by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 * P)]
  by_cases h_empty : ⌊b⌋₊ / d < (⌈a⌉₊ - 1) / d + 1
  · rw [Finset.Icc_eq_empty (not_le.mpr h_empty), Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW₀) hlog2P1_nn) (by positivity)) (by positivity)
  · push_neg at h_empty
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
        push_neg at hlt
        have h1 : ⌈a'⌉₊ ≤ (⌈a⌉₊ - 1) / d := by omega
        have h2 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        have h3 : (⌈a⌉₊ : ℝ) / d ≤ ((⌈a⌉₊ - 1) / d : ℕ) := le_trans h2 (by exact_mod_cast h1)
        rw [div_le_iff₀ hd_pos] at h3
        have h4 : ⌈a⌉₊ ≤ ((⌈a⌉₊ - 1) / d) * d := by exact_mod_cast h3
        have h5 : ((⌈a⌉₊ - 1) / d) * d ≤ ⌈a⌉₊ - 1 := Nat.div_mul_le_self _ _
        omega
    have hfloor_eq : ⌊b'⌋₊ = ⌊b⌋₊ / d := by
      rw [Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hd_pos.le)]
      refine ⟨(le_div_iff₀ hd_pos).mpr (by exact_mod_cast Nat.div_mul_le_self ⌊b⌋₊ d), ?_⟩
      rw [div_lt_iff₀ hd_pos]
      have hlt : ⌊b⌋₊ < (⌊b⌋₊ / d + 1) * d := by
        calc ⌊b⌋₊ = d * (⌊b⌋₊ / d) + ⌊b⌋₊ % d := (Nat.div_add_mod ⌊b⌋₊ d).symm
          _ < d * (⌊b⌋₊ / d) + d := Nat.add_lt_add_left (Nat.mod_lt _ hd1) _
          _ = (⌊b⌋₊ / d + 1) * d := by ring
      exact_mod_cast hlt
    have ha'b' : a' ≤ b' := by
      have h1 : ((⌈a⌉₊ - 1) / d + 1 : ℕ) ≤ ⌊b⌋₊ / d := h_empty
      have h2 : a' ≤ ((⌈a⌉₊ - 1) / d + 1 : ℕ) := by rw [← hceil_eq]; exact Nat.le_ceil a'
      have h3 : ((⌊b⌋₊ / d : ℕ) : ℝ) ≤ b' := by
        rw [← hfloor_eq]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
      exact le_trans h2 (le_trans (by exact_mod_cast h1) h3)
    let wd : ℕ → ℝ := fun k => Real.log k * w (d * k)
    let W₀' : ℝ := W₀ * (Real.log (2 * P) + 1)
    have hW₀' : 0 ≤ W₀' := mul_nonneg hW₀ hlog2P1_nn
    have hA'B' : ⌈a'⌉₊ ≤ ⌊b'⌋₊ := by rw [hceil_eq, hfloor_eq]; exact h_empty
    have hA'_ge : P ≤ ((d * ⌈a'⌉₊ : ℕ) : ℝ) := by
      push_cast
      calc P = (d : ℝ) * (P / d) := by field_simp [hd_pos.ne']
        _ ≤ (d : ℝ) * a' := mul_le_mul_of_nonneg_left hPa' hd_pos.le
        _ ≤ (d : ℝ) * ⌈a'⌉₊ := mul_le_mul_of_nonneg_left (Nat.le_ceil a') hd_pos.le
    have hB'_le : ((d * ⌊b'⌋₊ : ℕ) : ℝ) ≤ 2 * P := by
      push_cast
      calc (d : ℝ) * ⌊b'⌋₊ ≤ (d : ℝ) * b' := mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) hd_pos.le
        _ ≤ (d : ℝ) * (2 * (P / d)) := mul_le_mul_of_nonneg_left hb'2P hd_pos.le
        _ = 2 * P := by field_simp [hd_pos.ne']
    have hwd_bd : ∀ k ∈ Finset.Icc ⌈a'⌉₊ ⌊b'⌋₊, |wd k| ≤ W₀' := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk_ge1 : (1 : ℝ) ≤ k := le_trans hPd_ge1 (le_trans hPa' (le_trans (Nat.le_ceil a') (by exact_mod_cast hk.1)))
      have hk_le : (k : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hk.2) (le_trans (Nat.floor_le (by linarith))
        (le_trans hb'2P (by rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)))
      have hdk_mem : (d : ℝ) * k ∈ Set.Icc P (2 * P) := ⟨by
        exact le_trans hA'_ge (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.1) hd_pos.le),
        by exact le_trans (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.2) hd_pos.le) hB'_le⟩
      dsimp only [wd]
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg hk_ge1)]
      calc Real.log k * |w (d * k)|
          ≤ Real.log (2 * P) * W₀ := mul_le_mul (Real.log_le_log (by positivity) hk_le) (hw_bd _ hdk_mem)
            (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ ≤ W₀ * (Real.log (2 * P) + 1) := by linarith
    have hwd_tv : ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |wd (k + 1) - wd k| ≤ 3 * W₀' := by
      have hstep : ∀ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊,
          |wd (k + 1) - wd k| ≤
            (Real.log (k + 1 : ℕ) - Real.log k) * W₀ +
            Real.log (2 * P) * |w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)| := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hk_ge1 : (1 : ℝ) ≤ k := le_trans hPd_ge1 (le_trans hPa' (le_trans (Nat.le_ceil a') (by exact_mod_cast hk.1)))
        have hk_le : (k : ℝ) ≤ 2 * P := le_trans (by exact_mod_cast hk.2.le) (le_trans (Nat.floor_le (by linarith))
          (le_trans hb'2P (by rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1)))
        have hdk1_mem : (d : ℝ) * (k + 1 : ℕ) ∈ Set.Icc P (2 * P) := ⟨by
          exact le_trans hA'_ge (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : ⌈a'⌉₊ ≤ k + 1)) hd_pos.le),
          by exact le_trans (by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk.2) hd_pos.le) hB'_le⟩
        have hlog_mono : Real.log (k : ℝ) ≤ Real.log (k + 1 : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
        have hsplit : wd (k + 1) - wd k =
            (Real.log (k + 1 : ℕ) - Real.log k) * w ((d * (k + 1) : ℕ) : ℝ) +
            Real.log k * (w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)) := by
          dsimp only [wd]; push_cast; ring
        rw [hsplit]
        refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hlog_mono)]
          exact mul_le_mul_of_nonneg_left (hw_bd _ hdk1_mem) (sub_nonneg.mpr hlog_mono)
        · rw [abs_mul, abs_of_nonneg (Real.log_nonneg hk_ge1)]
          exact mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) hk_le) (abs_nonneg _)
      have htel : ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, (Real.log (k + 1 : ℕ) - Real.log k) * W₀ ≤ W₀ * Real.log (2 * P) := by
        rw [← Finset.sum_mul, Finset.sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hA'B']
        have hA'_ge1 : (1 : ℝ) ≤ ⌈a'⌉₊ := le_trans hPd_ge1 (le_trans hPa' (Nat.le_ceil a'))
        have hB'_le2P : (⌊b'⌋₊ : ℝ) ≤ 2 * P := le_trans (Nat.floor_le (by linarith))
          (le_trans hb'2P (by rw [show 2 * (P / d) = (2 * P) / d by ring]; exact div_le_self (by linarith) hd_ge1))
        have hlog_le : Real.log (⌊b'⌋₊ : ℝ) - Real.log (⌈a'⌉₊ : ℝ) ≤ Real.log (2 * P) := by
          linarith [Real.log_nonneg hA'_ge1, Real.log_le_log (by linarith [hA'_ge1, show (⌈a'⌉₊ : ℝ) ≤ ⌊b'⌋₊ by exact_mod_cast hA'B']) hB'_le2P]
        nlinarith
      have htv_w := discrete_tv_scale_le hP_pos hw_diff hw_tv d ⌈a'⌉₊ ⌊b'⌋₊ hA'B' hA'_ge hB'_le
      calc ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |wd (k + 1) - wd k|
          ≤ ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊,
              ((Real.log (k + 1 : ℕ) - Real.log k) * W₀ +
                Real.log (2 * P) * |w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)|) := Finset.sum_le_sum hstep
        _ = (∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, (Real.log (k + 1 : ℕ) - Real.log k) * W₀) +
            Real.log (2 * P) * ∑ k ∈ Finset.Ico ⌈a'⌉₊ ⌊b'⌋₊, |w ((d * (k + 1) : ℕ) : ℝ) - w ((d * k : ℕ) : ℝ)| := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ W₀ * Real.log (2 * P) + Real.log (2 * P) * W₀ :=
              add_le_add htel (mul_le_mul_of_nonneg_left htv_w (Real.log_nonneg (by linarith)))
        _ ≤ 3 * W₀' := by dsimp only [W₀']; nlinarith
    set E : ℝ := max C_exp 3 *
      ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp))
    have hE_nn : 0 ≤ E := mul_nonneg (by positivity) (add_nonneg (div_nonneg (by positivity)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity))
    have hsum_bd : ∀ u : ℕ, ⌈a'⌉₊ ≤ u → u ≤ ⌊b'⌋₊ →
        ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤ E := by
      intro u hau hub
      have hu_ge : P / d ≤ (u : ℝ) := by
        have h1 : a' ≤ (⌈a'⌉₊ : ℝ) := Nat.le_ceil a'
        exact le_trans hPa' (le_trans h1 (by exact_mod_cast hau))
      have hu_le : (u : ℝ) ≤ 2 * (P / d) := by
        have h1 : (⌊b'⌋₊ : ℝ) ≤ b' := Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hd_pos.le)
        exact le_trans (by exact_mod_cast hub) (le_trans h1 hb'2P)
      have hu_le' : (u : ℝ) ≤ 2 * P / d := by linarith [hu_le, show 2 * (P / d) = 2 * P / d by ring]
      by_cases hn0 : n = 0
      · subst hn0
        have htriv : ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / (2 * ((d * k : ℕ) : ℝ) ^ r))‖ ≤
            ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          simp [norm_ePhase]
        have hcard : ((Finset.Icc ⌈a'⌉₊ u).card : ℝ) ≤ 2 * P / d := by
          rw [Nat.card_Icc]
          have h1 : 1 ≤ ⌈a'⌉₊ := Nat.ceil_pos.mpr (lt_of_lt_of_le hPd_pos hPa')
          have h2 : u + 1 - ⌈a'⌉₊ ≤ u := by omega
          exact le_trans (by exact_mod_cast h2) hu_le'
        have hT0_0 : T₀ = 0 := by dsimp only [T₀]; simp
        have hmax1 : max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 = 1 := by rw [hT0_0, mul_zero, max_eq_right zero_le_one]
        calc ‖∑ k ∈ Finset.Icc ⌈a'⌉₊ u, ePhase (∑ r ∈ A, (h r : ℝ) * (0 : ℕ) / (2 * ((d * k : ℕ) : ℝ) ^ r))‖
            ≤ 2 * P / d := le_trans htriv hcard
          _ = 1 * ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + 0) := by rw [hmax1, div_one, one_mul, add_zero]
          _ ≤ E := by
              dsimp only [E]
              refine mul_le_mul (le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_right _ _))
                (add_le_add le_rfl (by positivity)) (by positivity) (by positivity)
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have h_eq_phase : ∀ k : ℕ, 1 ≤ k →
            ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r)) =
            ePhase (∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (2 * (d : ℝ) ^ r)) * (k : ℝ) ^ (-(r : ℤ))) := by
          intro k _
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
        have hcd0 : cd r₀ ≠ 0 :=
          div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hh₀) hn_pos.ne') (by positivity)
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
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
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
            exact inv_anti₀ (pow_pos (by linarith) r₀) (pow_le_pow_left₀ (by linarith) hu_le' r₀)
          have h2pow : (2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ)) ≤ (2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ)) := by
            rw [show (2 * P / d) = (2 * P) / d by ring, zpow_sub₀ (by norm_num),
              zpow_neg (2 : ℝ) (R : ℤ), zpow_natCast (2 : ℝ) R, zpow_one,
              zpow_neg P (r₀ : ℤ), zpow_natCast P r₀,
              zpow_neg ((2 * P) / d) (r₀ : ℤ), zpow_natCast ((2 * P) / d) r₀, div_pow, inv_div]
            rw [mul_pow, ← div_eq_mul_inv]
            field_simp [hd_pos.ne', hP_pos.ne']
            have h2r : (2 : ℝ) ^ r₀ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (hA r₀ hr₀).2
            linarith [h2r]
          have habs_cd : |(h r₀ : ℝ) * n / (2 * (d : ℝ) ^ r₀)| = |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) := by
            rw [abs_div, abs_mul, abs_of_pos hn_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ r₀)]
          rw [habs_cd]
          calc (2 : ℝ) ^ (-(R : ℤ) - 1) * (|(h r₀ : ℝ)| * n / P ^ r₀)
              = |(h r₀ : ℝ)| * n * ((2 : ℝ) ^ (-(R : ℤ) - 1) * P ^ (-(r₀ : ℤ))) := by
                  rw [zpow_neg, zpow_natCast]; ring
            _ ≤ |(h r₀ : ℝ)| * n * ((2 * (d : ℝ) ^ r₀)⁻¹ * (2 * P / d) ^ (-(r₀ : ℤ))) :=
                  mul_le_mul_of_nonneg_left h2pow (by positivity)
            _ = |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * 1 * (2 * P / d) ^ (-(r₀ : ℤ)) := by ring
            _ ≤ |(h r₀ : ℝ)| * n / (2 * (d : ℝ) ^ r₀) * (r₀ : ℝ) * (u : ℝ) ^ (-(r₀ : ℤ)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hr0_1 (by positivity)) hupow (by positivity) (by positivity)
        refine le_trans hhexp ?_
        dsimp only [E]
        refine mul_le_mul (le_max_left _ _) ?_ (add_nonneg (div_nonneg (by positivity)
          (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le) (by positivity)) (by positivity)
        refine add_le_add ?_ ?_
        · exact div_le_div₀ (by positivity) hu_le' (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (max_le_max hT_ge le_rfl)
        · exact Real.rpow_le_rpow (by positivity) hu_le' (by linarith)
    have hps := abel_summation_Icc hA'B' hW₀' (by positivity : 0 ≤ 3 * W₀') hE_nn hwd_bd hwd_tv hsum_bd
    rw [hceil_eq, hfloor_eq] at hps
    calc ‖∑ k ∈ Finset.Icc ((⌈a⌉₊ - 1) / d + 1) (⌊b⌋₊ / d),
            (Real.log k * w (d * k) : ℂ) *
              ePhase (∑ r ∈ A, (h r : ℝ) * n / (2 * ((d * k : ℕ) : ℝ) ^ r))‖
        ≤ (W₀' + 3 * W₀') * E := by simpa [wd] using hps
      _ = 4 * W₀ * (Real.log (2 * P) + 1) * max C_exp 3 *
            ((2 * P / d) / max ((2 : ℝ) ^ (-(R : ℤ) - 1) * T₀) 1 + (2 * P / d) ^ (1 - η_exp)) := by
          dsimp only [W₀', E]; ring

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
          Finset.sum_le_sum_of_subset_of_nonneg h_upper_sub (fun k hk _ => h_coeff_nn k hk)
  have h_fact_le : Real.log ((2 * m).factorial : ℝ) - 2 * Real.log (m.factorial : ℝ) ≤
      (m : ℝ) * Real.log 4 := by
    have hle : ((2 * m).factorial : ℝ) ≤ (4 : ℝ) ^ m * ((m.factorial : ℝ) ^ 2) := by
      exact_mod_cast factorial_two_mul_le m
    have hlog_le := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog_le
    push_cast at hlog_le
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
    rw [hsplit, Finset.sum_union hdisj, pow_succ']
    have hdy := sum_vonMangoldt_dyadic_le (2 ^ K) Nat.one_le_two_pow
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
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hX_nn : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  nlinarith

end BrocardFormalization

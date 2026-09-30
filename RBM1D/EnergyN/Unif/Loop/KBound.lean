/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.EnergyN.Unif.Loop.SumZero
import RBM1D.Loop.KBound

/-!
# The `∃ C after E` reorder for the constant producers of `Loop/KBound.lean`

This file adds the reordered forms `∃ C, ∀ E, |E| ≤ 2 - k → …` of eight constant producers:
`norm_Kpi_empty_alt_le`, `norm_Kpi_empty_short_le`, `norm_Kpi_empty_le`, `sum_norm_innerId_alt_le`,
`sum_norm_innerId_short_le`, `sum_norm_innerId_le`, `norm_Kpi_le`, `norm_Kgen_le`. Two of the
eight (`norm_Kpi_empty_short_le`, `sum_norm_innerId_short_le`) have a constant already explicit in
`k` and `n`/`N` alone (no `sum_zero` call). The other six inherit the `(mE E).im⁻¹` taint through
`sum_zero`/`norm_Alayer_le` (see `EnergyN/Unif/Loop/SumZero.lean`) and are fixed by using
`sum_zero_unif` in place of `sum_zero` (already uniform, no extra κ-bound needed at this level).
-/

namespace RBM

open Finset Cor35

section NonAlternatingUnif

/-- **`norm_Kpi_empty_alt_le`, reordered.** Tainted via `sum_zero`; fixed by calling
`sum_zero_unif`. -/
theorem norm_Kpi_empty_alt_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {n : ℕ}
    [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ : Fin n → Bool, (∀ v, σ v ≠ σ (v + 1)) → ∀ a : Fin n → ZMod L,
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨Csz, hCsz0, hCsz⟩ := sum_zero_unif hk0 hk1 hn
  set SW := sigWeightConst n k 2
  have hSW : 0 ≤ SW := sigWeightConst_nonneg hk0 2
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨3 ^ n * ((Csz + 19 / 4 * SW) * e8 ^ (n - 1)), by positivity, fun E hEk => ?_⟩
  intro L _ hL t ht0 ht1 σ halt a
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
  have hηℓ2 : η * ℓ ^ 2 ≤ 1 := etaT_mul_ellHat_sq_le hE2 ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hA : 3 / 2 ≤ A := by
    have : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
    simp only [A, e8]; nlinarith
  set f : Fin n → ZMod L → ℂ := fun v y => thetaEdge L (mSigma E) t (σ v) (σ (v + 1)) (a v) y
  have hf : ∀ v y, f v y = Theta L (t : ℂ) (a v) y := fun v y => by
    simp only [f, thetaEdge_of_ne hE2 t (halt v)]
  have hsup : ∀ v y, ‖f v y‖ ≤ A := fun v y => by
    rw [hf, hAdef, hηdef, etaT_eq_zt_im, ← div_eq_mul_inv]
    exact norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _ _
  have hl1 : ∀ v, ∑ y, ‖f v y‖ ≤ η⁻¹ := fun v => by
    simp only [hf]; rw [hηdef, etaT_eq_zt_im]
    exact sum_norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _
  have hgrad : ∀ v u, ‖f v (u + 1) - f v u‖ ≤ 3 / 2 := fun v u => by
    rw [hf, hf, norm_sub_rev]; exact norm_Theta_sub_shift_le_uniform L hL ht0 ht1 _ _
  have hlap_eq : ∀ v u, ‖lap (f v) u‖ =
      ‖2 * Theta L (t : ℂ) (a v) u - Theta L (t : ℂ) (a v) (u + 1) -
        Theta L (t : ℂ) (a v) (u - 1)‖ :=
    fun v u => by
      simp only [lap, hf]
      rw [← norm_neg]; congr 1; ring
  have hlap : ∀ v u, ‖lap (f v) u‖ ≤ 3 := fun v u => by
    rw [hlap_eq]; exact norm_Theta_second_diff_le_three L hL ht0 ht1 _ _
  have hoff : ∀ v u, u ≠ a v → ‖lap (f v) u‖ ≤ 24 / ℓ := fun v u hu => by
    rw [hlap_eq]; exact norm_Theta_second_diff_le L hL ht0 ht1 (Ne.symm hu)
  have hMoff : 0 ≤ 24 / ℓ := by positivity
  have h₁ : η⁻¹ * (24 / ℓ) ≤ 2 * A := by
    rw [hAdef, show η⁻¹ * (24 / ℓ) = 24 * (η * ℓ)⁻¹ by field_simp]
    have : 0 < (η * ℓ)⁻¹ := by positivity
    simp only [e8]; nlinarith
  have h₂ : η⁻¹ ≤ 1 * A ^ 2 := by
    rw [one_mul, hAdef, mul_pow, inv_pow]
    rw [show η⁻¹ = (η * ℓ ^ 2) * ((η * ℓ) ^ 2)⁻¹ by field_simp]
    have : 0 < ((η * ℓ) ^ 2)⁻¹ := by positivity
    have : 1 ≤ e8 ^ 2 := by simp only [e8]; nlinarith
    nlinarith
  set g : (Fin n → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ ∅ s
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  have hgneg : ∀ s, g (fun v => -s v) = g s := fun s => SigmaPi_neg (mSigma E) hm hL σ ∅ s
  have hgadd : ∀ s c, g (fun v => s v + c) = g s := fun s c =>
    SigmaPi_add_const (mSigma E) hm hL σ ∅ s c
  set B := (Csz + 19 / 4 * SW) * A ^ (n - 1)
  have hterm : ∀ τ : Fin n → Fin 3,
      ‖∑ c : ZMod L, ∑ s ∈ pinned L n 0, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖ ≤ B := by
    intro τ
    have hA0 : 0 ≤ A := by linarith
    have hB0 : 0 ≤ B := by positivity
    by_cases hR : (∃ v, τ v = 2) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ τ v₁ = 1 ∧ τ v₂ = 1
    · have hW : ∀ s ∈ pinned L n 0, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
          (2 / 2 + 3 / 2 + 9 / 4 * 1) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
        intro s hs
        simp only [pinned, mem_filter, mem_univ, true_and] at hs
        exact sum_prod_taylor_le f a hA hsup hl1 hgrad hlap hoff hMoff h₁ h₂ (by norm_num)
          (by norm_num) τ hR s hs
      have hS := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ (by omega) 2
      calc ‖∑ c : ZMod L, ∑ s ∈ pinned L n 0, g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖
          ≤ ∑ c : ZMod L, ∑ s ∈ pinned L n 0, ‖g s‖ * ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
            refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
            rw [norm_mul, norm_prod]
        _ = ∑ s ∈ pinned L n 0, ‖g s‖ * ∑ c : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            rw [sum_comm]; simp only [mul_sum]
        _ ≤ ∑ s ∈ pinned L n 0, ‖g s‖ *
              ((2 / 2 + 3 / 2 + 9 / 4 * 1) * A ^ (n - 1) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
            sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hW s hs) (norm_nonneg _)
        _ = 19 / 4 * A ^ (n - 1) *
              ∑ s ∈ pinned L n 0, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
            rw [mul_sum]; refine sum_congr rfl fun s _ => by ring
        _ ≤ 19 / 4 * A ^ (n - 1) * SW := by gcongr
        _ ≤ B := by
            simp only [B]
            have : 0 ≤ Csz * A ^ (n - 1) := by positivity
            nlinarith
    push Not at hR
    obtain ⟨hn2, hn11⟩ := hR
    have key : ∀ j : Fin 3, j ≠ 2 → j ≠ 1 → j = 0 := by decide
    by_cases h1 : ∃ v₁, τ v₁ = 1
    · obtain ⟨v₁, hv₁⟩ := h1
      have h0 : ∀ v, v ≠ v₁ → τ v = 0 := fun v hv =>
        key _ (hn2 v) (hn11 v₁ v (Ne.symm hv) hv₁)
      rw [sum_taylor_single_eq_zero g hgneg f τ v₁ hv₁ h0, norm_zero]
      exact hB0
    · push Not at h1
      have h0 : ∀ v, τ v = 0 := fun v => key _ (hn2 v) (h1 v)
      rw [sum_taylor_zero_eq g f τ h0, norm_mul]
      have hlead : ‖∑ c : ZMod L, ∏ v, f v c‖ ≤ η⁻¹ * A ^ (n - 1) := by
        have hT : (univ.erase (0 : Fin n)).card = n - 1 := by
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        calc ‖∑ c : ZMod L, ∏ v, f v c‖ ≤ ∑ c : ZMod L, ‖f 0 c‖ * ∏ v ∈ univ.erase 0, ‖f v c‖ := by
              refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun c _ => ?_))
              rw [norm_prod, mul_prod_erase _ (fun v => ‖f v c‖) (mem_univ 0)]
          _ ≤ (∑ c : ZMod L, ‖f 0 c‖) * ∏ _v ∈ univ.erase (0 : Fin n), A :=
              sum_mul_prod_le _ (fun v c => ‖f v c‖) _ _ (fun c => norm_nonneg _)
                (fun v c => norm_nonneg _) fun v _ c => hsup v c
          _ ≤ η⁻¹ * A ^ (n - 1) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 0
      have hzero : ‖∑ s ∈ pinned L n 0, g s‖ ≤ Csz * η := by
        have h := hCsz E hEk L hL t ht0.le ht1 σ halt
        have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
        rw [sum_eq_mul_sum_pinned g hgadd, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul] at h
        exact h
      calc ‖∑ c : ZMod L, ∏ v, f v c‖ * ‖∑ s ∈ pinned L n 0, g s‖
          ≤ (η⁻¹ * A ^ (n - 1)) * (Csz * η) := by gcongr
        _ = Csz * A ^ (n - 1) := by field_simp
        _ ≤ B := by
            simp only [B]
            have : 0 ≤ SW * A ^ (n - 1) := by positivity
            nlinarith
  rw [Kpi_empty_expand hL hE ht0.le ht1 σ a]
  calc ‖∑ τ : Fin n → Fin 3, ∑ c : ZMod L, ∑ s ∈ pinned L n 0,
          g s * ∏ v, taylorTerm (f v) (τ v) c (s v)‖
      ≤ ∑ τ : Fin n → Fin 3, B := (norm_sum_le _ _).trans (sum_le_sum fun τ _ => hterm τ)
    _ = 3 ^ n * B := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring
    _ = 3 ^ n * ((Csz + 19 / 4 * SW) * e8 ^ (n - 1)) * (η * ℓ)⁻¹ ^ (n - 1) := by
        simp only [B, A, mul_pow]; ring

/-- **`norm_Kpi_empty_short_le`, reordered.** Its constant is already explicit in `k`, `n` (no
`sum_zero` call); a plain reorder. -/
theorem norm_Kpi_empty_short_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ : Fin n → Bool, (∃ v, σ v = σ (v + 1)) → ∀ a : Fin n → ZMod L,
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  set Bk := 2 * cTwo52 / Real.sqrt k + 1
  set κ := cZero * Real.sqrt (Real.sqrt k)
  have hδ : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hκ : 0 < κ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hBk : 1 ≤ Bk := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / Real.sqrt k := by positivity
    simp only [Bk]; linarith
  set S1 := 2 / (1 - Real.exp (-κ))
  have hS1 : 0 ≤ S1 := (zero_le_one.trans (one_le_two_div hκ))
  set SW0 := sigWeightConst n k 0
  have hSW0 : 0 ≤ SW0 := sigWeightConst_nonneg hk0 0
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨SW0 * (Bk * S1) * (Bk * e8) ^ (n - 1), by positivity, fun E hEk => ?_⟩
  intro L _ hL t ht0 ht1 σ ⟨v₀, hv₀⟩ a
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hA1 : 1 ≤ A := by
    have : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
    simp only [A, e8]; nlinarith
  set θ : Fin n → Matrix (ZMod L) (ZMod L) ℂ := fun v => thetaEdge L (mSigma E) t (σ v) (σ (v + 1))
  have hsup : ∀ v x y, ‖θ v x y‖ ≤ Bk * A := by
    intro v x y
    by_cases hv : σ v = σ (v + 1)
    · have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ v) x y
      simp only [θ]; rw [← hv]
      calc _ ≤ Bk * Real.exp (-(κ * zdist L (x - y))) := h
        _ ≤ Bk * 1 := by
            gcongr; rw [Real.exp_le_one_iff, neg_nonpos]; positivity
        _ ≤ Bk * A := by gcongr
    · simp only [θ]
      rw [thetaEdge_of_ne hE2 t hv]
      have h := norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 x y
      rw [← etaT_eq_zt_im, div_eq_mul_inv] at h
      calc _ ≤ A := h
        _ = 1 * A := (one_mul A).symm
        _ ≤ Bk * A := by gcongr
  have hl1 : ∀ x (s : ZMod L), ∑ c : ZMod L, ‖θ v₀ x (s + c)‖ ≤ Bk * S1 := by
    intro x s
    calc ∑ c : ZMod L, ‖θ v₀ x (s + c)‖
        ≤ ∑ c : ZMod L, Bk * Real.exp (-(κ * zdist L (c - (x - s)))) := by
          refine sum_le_sum fun c _ => ?_
          have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ v₀) x (s + c)
          simp only [θ]; rw [← hv₀]
          rw [show x - (s + c) = -(c - (x - s)) by ring, zdist_neg] at h
          exact h
      _ = Bk * ∑ c : ZMod L, Real.exp (-(κ * zdist L (c - (x - s)))) := by rw [mul_sum]
      _ ≤ Bk * S1 := by gcongr; exact sum_exp_zdist_le L hκ _
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  set g : (Fin n → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ ∅ s
  have hgadd : ∀ s c, g (fun v => s v + c) = g s := fun s c =>
    SigmaPi_add_const (mSigma E) hm hL σ ∅ s c
  have hSg := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ hn 0
  simp only [pow_zero, prod_const_one, mul_one] at hSg
  have hT : (univ.erase v₀).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [Kpi_eq_sum_SigmaPi L, sum_center (M := ℂ)]
  calc ‖∑ c : ZMod L, ∑ s ∈ pinned L n 0,
          SigmaPi L (mSigma E) t σ ∅ (fun v => s v + c) * ∏ v, θ v (a v) (s v + c)‖
      ≤ ∑ c : ZMod L, ∑ s ∈ pinned L n 0, ‖g s‖ * ∏ v, ‖θ v (a v) (s v + c)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
        rw [norm_mul, norm_prod, show SigmaPi L (mSigma E) t σ ∅ (fun v => s v + c) = g s from
          hgadd s c]
    _ = ∑ s ∈ pinned L n 0, ‖g s‖ * ∑ c : ZMod L, ∏ v, ‖θ v (a v) (s v + c)‖ := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ s ∈ pinned L n 0, ‖g s‖ * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by
        refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ∑ c : ZMod L, ∏ v, ‖θ v (a v) (s v + c)‖
            = ∑ c : ZMod L, ‖θ v₀ (a v₀) (s v₀ + c)‖ *
                ∏ v ∈ univ.erase v₀, ‖θ v (a v) (s v + c)‖ := by
              refine sum_congr rfl fun c _ => ?_
              rw [mul_prod_erase _ (fun v => ‖θ v (a v) (s v + c)‖) (mem_univ v₀)]
          _ ≤ (∑ c : ZMod L, ‖θ v₀ (a v₀) (s v₀ + c)‖) * ∏ _v ∈ univ.erase v₀, (Bk * A) :=
              sum_mul_prod_le _ (fun v c => ‖θ v (a v) (s v + c)‖) _ _ (fun c => norm_nonneg _)
                (fun v c => norm_nonneg _) fun v _ c => hsup v _ _
          _ ≤ (Bk * S1) * (Bk * A) ^ (n - 1) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 _ _
    _ = (∑ s ∈ pinned L n 0, ‖g s‖) * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by rw [sum_mul]
    _ ≤ SW0 * ((Bk * S1) * (Bk * A) ^ (n - 1)) := by gcongr
    _ = SW0 * (Bk * S1) * (Bk * e8) ^ (n - 1) * (η * ℓ)⁻¹ ^ (n - 1) := by
        simp only [A, mul_pow]; ring

/-- **`norm_Kpi_empty_le`, reordered.** Combines the two above. -/
theorem norm_Kpi_empty_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ : Fin n → Bool) (a : Fin n → ZMod L),
        ‖Kpi L (mSigma E) t σ a ∅‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_Kpi_empty_alt_le_unif hk0 hk1 hn
  obtain ⟨C₂, hC₂, h₂⟩ := norm_Kpi_empty_short_le_unif hk0 hk1 (n := n) (by omega)
  refine ⟨C₁ + C₂, by positivity, fun E hEk => ?_⟩
  intro L _ hL t ht0 ht1 σ a
  have hE : |E| < 2 := by linarith
  have hX : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
    have := etaT_pos hE ht1
    have := one_le_ellHat L hL ht0.le ht1
    positivity
  by_cases halt : ∀ v, σ v ≠ σ (v + 1)
  · exact (h₁ E hEk L hL t ht0 ht1 σ halt a).trans (by nlinarith)
  · push Not at halt
    exact (h₂ E hEk L hL t ht0 ht1 σ halt a).trans (by nlinarith)

end NonAlternatingUnif

section InnerBoundUnif

set_option maxHeartbeats 1000000 in
-- The same long expansion as `sum_norm_innerId_alt_le` (Loop/KBound.lean).
/-- **`sum_norm_innerId_alt_le`, reordered.** Tainted via `sum_zero`; fixed by calling
`sum_zero_unif`. -/
theorem sum_norm_innerId_alt_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ σ' : Fin N → Bool, (∀ v, σ' v ≠ σ' (v + 1)) → ∀ (a' : Fin N → ZMod L) (p : Fin N),
        ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
          ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
  obtain ⟨Csz, hCsz0, hCsz⟩ := sum_zero_unif hk0 hk1 hN
  set SW := sigWeightConst N k 2
  have hSW : 0 ≤ SW := sigWeightConst_nonneg hk0 2
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  set K0 := Csz + 19 / 4 * SW + 3 * (3 / 2) ^ (N - 2) * SW
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨3 ^ N * (K0 * e8 ^ (N - 2)), by positivity, fun E hEk => ?_⟩
  intro L _ hL t ht0 ht1 σ' halt a' p
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
  have hηℓ2 : η * ℓ ^ 2 ≤ 1 := etaT_mul_ellHat_sq_le hE2 ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hinv1 : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
  have hA : 3 / 2 ≤ A := by simp only [A, e8]; nlinarith
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  have hℓA : ℓ ≤ A := by
    have : ℓ ≤ (η * ℓ)⁻¹ := by
      have h1 : ℓ * (η * ℓ) ≤ 1 := by nlinarith
      calc ℓ = ℓ * (η * ℓ) * (η * ℓ)⁻¹ := by field_simp
        _ ≤ 1 * (η * ℓ)⁻¹ := by gcongr
        _ = (η * ℓ)⁻¹ := one_mul _
    simp only [A, e8]; nlinarith
  have hApow : A ≤ A ^ (N - 2) := le_self_pow₀ hA1 (by omega)
  set f : Fin N → ZMod L → ℂ := innerKer (mSigma E) t σ' a' p
  have hfp : ∀ y, f p y = 1 := fun y => by simp only [f, innerKer, Function.update_self]
  have hfv : ∀ v, v ≠ p → ∀ y, f v y = Theta L (t : ℂ) (a' v) y := fun v hv y => by
    simp only [f, innerKer, Function.update_of_ne hv, thetaEdge_of_ne hE2 t (halt v)]
  have hgrad : ∀ v u, ‖f v (u + 1) - f v u‖ ≤ 3 / 2 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hfp, hfp, sub_self, norm_zero]; norm_num
    · rw [hfv v hv, hfv v hv, norm_sub_rev]; exact norm_Theta_sub_shift_le_uniform L hL ht0 ht1 _ _
  have hlap_eq : ∀ v, v ≠ p → ∀ u, ‖lap (f v) u‖ =
      ‖2 * Theta L (t : ℂ) (a' v) u - Theta L (t : ℂ) (a' v) (u + 1) -
        Theta L (t : ℂ) (a' v) (u - 1)‖ :=
    fun v hv u => by
      simp only [lap, hfv v hv]
      rw [← norm_neg]; congr 1; ring
  have hlapp : ∀ u, lap (f p) u = 0 := fun u => by simp only [lap, hfp]; ring
  have hlap : ∀ v u, ‖lap (f v) u‖ ≤ 3 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hlapp, norm_zero]; norm_num
    · rw [hlap_eq v hv]; exact norm_Theta_second_diff_le_three L hL ht0 ht1 _ _
  have hG1 : ∀ v, ∑ u, ‖f v (u + 1) - f v u‖ ≤ 3 * ℓ := fun v => by
    by_cases hv : v = p
    · subst hv; simp only [hfp, sub_self, norm_zero, sum_const_zero]; positivity
    · simp only [hfv v hv]
      calc ∑ u, ‖Theta L (t : ℂ) (a' v) (u + 1) - Theta L (t : ℂ) (a' v) u‖
          = ∑ u, ‖Theta L (t : ℂ) (a' v) u - Theta L (t : ℂ) (a' v) (u + 1)‖ :=
            sum_congr rfl fun u _ => norm_sub_rev _ _
        _ ≤ 3 * ℓ := sum_norm_Theta_sub_shift_le L hL ht0 ht1 _
  have hG2 : ∀ v, ∑ u, ‖lap (f v) u‖ ≤ 2 * (3 * ℓ) := fun v => by
    by_cases hv : v = p
    · subst hv; simp only [hlapp, norm_zero, sum_const_zero]; positivity
    · simp only [hlap_eq v hv]
      calc _ ≤ 6 := sum_norm_Theta_second_diff_le L hL ht0 ht1 _
        _ ≤ 2 * (3 * ℓ) := by linarith
  set f' : Fin N → ZMod L → ℂ := Function.update f p (fun _ => (A : ℂ))
  have hf'p : ∀ y, f' p y = A := fun y => by simp only [f', Function.update_self]
  have hf'v : ∀ v, v ≠ p → f' v = f v := fun v hv => by simp only [f', Function.update_of_ne hv]
  have hsup' : ∀ v y, ‖f' v y‖ ≤ A := fun v y => by
    by_cases hv : v = p
    · subst hv; rw [hf'p, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0]
    · rw [hf'v v hv, hfv v hv, hAdef, hηdef, etaT_eq_zt_im, ← div_eq_mul_inv]
      exact norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _ _
  have hgrad' : ∀ v u, ‖f' v (u + 1) - f' v u‖ ≤ 3 / 2 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hf'p, hf'p, sub_self, norm_zero]; norm_num
    · rw [hf'v v hv]; exact hgrad v u
  have hlap'p : ∀ u, lap (f' p) u = 0 := fun u => by simp only [lap, hf'p]; ring
  have hlap' : ∀ v u, ‖lap (f' v) u‖ ≤ 3 := fun v u => by
    by_cases hv : v = p
    · subst hv; rw [hlap'p, norm_zero]; norm_num
    · rw [hf'v v hv]; exact hlap v u
  have hoff' : ∀ v u, u ≠ a' v → ‖lap (f' v) u‖ ≤ 24 / ℓ := fun v u hu => by
    by_cases hv : v = p
    · subst hv; rw [hlap'p, norm_zero]; positivity
    · rw [hf'v v hv, hlap_eq v hv]; exact norm_Theta_second_diff_le L hL ht0 ht1 (Ne.symm hu)
  have h₁ : η⁻¹ * (24 / ℓ) ≤ 2 * A := by
    rw [hAdef, show η⁻¹ * (24 / ℓ) = 24 * (η * ℓ)⁻¹ by field_simp]
    have : 0 < (η * ℓ)⁻¹ := by positivity
    simp only [e8]; nlinarith
  have h₂ : η⁻¹ ≤ 1 * A ^ 2 := by
    rw [one_mul, hAdef, mul_pow, inv_pow]
    rw [show η⁻¹ = (η * ℓ ^ 2) * ((η * ℓ) ^ 2)⁻¹ by field_simp]
    have : 0 < ((η * ℓ) ^ 2)⁻¹ := by positivity
    have : 1 ≤ e8 ^ 2 := by simp only [e8]; nlinarith
    nlinarith
  have hl1q : ∀ q, q ≠ p → ∑ y, ‖f' q y‖ ≤ η⁻¹ := fun q hq => by
    simp only [hf'v q hq, hfv q hq]; rw [hηdef, etaT_eq_zt_im]
    exact sum_norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 _
  have hscale : ∀ (τ : Fin N → Fin 3), τ p = 0 → ∀ (s : Fin N → ZMod L), ∀ c,
      A * ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ = ∏ v, ‖taylorTerm (f' v) (τ v) c (s v)‖ := by
    intro τ hτp s c
    rw [← mul_prod_erase _ (fun v => ‖taylorTerm (f v) (τ v) c (s v)‖) (mem_univ p),
      ← mul_prod_erase _ (fun v => ‖taylorTerm (f' v) (τ v) c (s v)‖) (mem_univ p), ← mul_assoc]
    congr 1
    · show A * ‖taylorTerm (f p) (τ p) c (s p)‖ = ‖taylorTerm (f' p) (τ p) c (s p)‖
      rw [hτp]
      show A * ‖f p c‖ = ‖f' p c‖
      rw [hfp, hf'p, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0]
    · refine Finset.prod_congr rfl fun v hv => ?_
      rw [hf'v v (ne_of_mem_erase hv)]
  set g : (Fin N → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ' ∅ s
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  have hgneg : ∀ s, g (fun v => -s v) = g s := fun s => SigmaPi_neg (mSigma E) hm hL σ' ∅ s
  have hgadd : ∀ s c, g (fun v => s v + c) = g s := fun s c =>
    SigmaPi_add_const (mSigma E) hm hL σ' ∅ s c
  have hzero : ‖∑ s ∈ pinned L N p, g s‖ ≤ Csz * η := by
    have h := hCsz E hEk L hL t ht0.le ht1 σ' halt
    have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    rw [sum_eq_mul_sum_pinned g hgadd p, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul] at h
    exact h
  have hSW2 := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ' (by omega) 2 p
  set B := K0 * A ^ (N - 2)
  have hB0 : 0 ≤ B := by positivity
  set T : (Fin N → Fin 3) → ZMod L → ℂ := fun τ u =>
    ∑ s ∈ pinned L N p, g s * ∏ v, taylorTerm (f v) (τ v) u (s v)
  have hexp : ∀ u, innerId (mSigma E) t σ' a' p u = ∑ τ : Fin N → Fin 3, T τ u := by
    intro u
    rw [innerId_eq hL (mSigma E) hm σ' a' p u]
    simp only [T]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [← mul_sum, prod_taylor_expand]
  have hWnn : ∀ s : Fin N → ZMod L, 0 ≤ ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 :=
    fun s => prod_nonneg fun _ _ => by positivity
  have habs : ∀ τ : Fin N → Fin 3, ∑ u, ‖T τ u‖ ≤
      ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ := by
    intro τ
    calc ∑ u, ‖T τ u‖
        ≤ ∑ u : ZMod L, ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ := by
          refine sum_le_sum fun u _ => ?_
          refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
          rw [norm_mul, norm_prod]
      _ = _ := by rw [sum_comm]; simp only [mul_sum]
  have hterm : ∀ τ : Fin N → Fin 3, ∑ u, ‖T τ u‖ ≤ B := by
    intro τ
    by_cases hτp : τ p = 0
    swap
    · have hz : ∀ u, T τ u = 0 := fun u => by
        refine sum_eq_zero fun s hs => ?_
        simp only [pinned, mem_filter, mem_univ, true_and] at hs
        have h0 : taylorTerm (f p) (τ p) u (s p) = 0 := by
          rw [hs]
          have : τ p = 1 ∨ τ p = 2 := by revert hτp; generalize τ p = j; decide +revert
          rcases this with h | h <;> rw [h]
          · exact oddPart_zero _ _
          · exact evenPart_zero _ _
        rw [prod_eq_zero (mem_univ p) h0, mul_zero]
      simp only [hz, norm_zero, sum_const_zero]; exact hB0
    by_cases hval : ∃ q, q ≠ p ∧ τ q = 0
    · obtain ⟨q, hqp, hq⟩ := hval
      by_cases hR : (∃ v, τ v = 2) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ τ v₁ = 1 ∧ τ v₂ = 1
      · have hW : ∀ s : Fin N → ZMod L, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
            19 / 4 * A ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
          intro s
          have h := sum_prod_taylor_le_at f' a' hA hsup' q (hl1q q hqp) hgrad' hlap' hoff'
            (by positivity) h₁ h₂ (by norm_num) (by norm_num) τ hR hq s
          have e : ∑ c, ∏ v, ‖taylorTerm (f' v) (τ v) c (s v)‖
              = A * ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ := by
            rw [mul_sum]; exact sum_congr rfl fun c _ => (hscale τ hτp s c).symm
          rw [e, show A ^ (N - 1) = A * A ^ (N - 2) by rw [← pow_succ']; congr 1; omega] at h
          have h' : A * ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
              A * (19 / 4 * A ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) := by
            refine h.trans (le_of_eq ?_); ring
          exact le_of_mul_le_mul_left h' hA0
        calc ∑ u, ‖T τ u‖
            ≤ ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ :=
              habs τ
          _ ≤ ∑ s ∈ pinned L N p, ‖g s‖ *
                (19 / 4 * A ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
              sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hW s) (norm_nonneg _)
          _ = 19 / 4 * A ^ (N - 2) *
                ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
              rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
          _ ≤ 19 / 4 * A ^ (N - 2) * SW := by gcongr
          _ ≤ B := by
              simp only [B, K0]
              have : 0 ≤ (Csz + 3 * (3 / 2) ^ (N - 2) * SW) * A ^ (N - 2) := by positivity
              nlinarith
      · push Not at hR
        obtain ⟨hn2, hn11⟩ := hR
        have key : ∀ j : Fin 3, j ≠ 2 → j ≠ 1 → j = 0 := by decide
        by_cases h1 : ∃ v₁, τ v₁ = 1
        · obtain ⟨v₁, hv₁⟩ := h1
          have h0 : ∀ v, v ≠ v₁ → τ v = 0 := fun v hv =>
            key _ (hn2 v) (hn11 v₁ v (Ne.symm hv) hv₁)
          have hz : ∀ u, T τ u = 0 := fun u =>
            sum_taylor_single_eq_zero_pt g hgneg f τ v₁ hv₁ h0 p u
          simp only [hz, norm_zero, sum_const_zero]; exact hB0
        · push Not at h1
          have h0 : ∀ v, τ v = 0 := fun v => key _ (hn2 v) (h1 v)
          have hT : ∀ u, T τ u = (∏ v, f v u) * ∑ s ∈ pinned L N p, g s := by
            intro u
            simp only [T]
            rw [mul_sum]
            refine sum_congr rfl fun s _ => ?_
            have : ∏ v, taylorTerm (f v) (τ v) u (s v) = ∏ v, f v u :=
              Finset.prod_congr rfl fun v _ => by rw [h0 v]; rfl
            rw [this, mul_comm]
          have hcard : ((univ.erase q).erase p).card = N - 2 := by
            rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hqp, mem_univ _⟩),
              card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
            omega
          have hlead : ∑ u : ZMod L, ‖∏ v, f v u‖ ≤ η⁻¹ * A ^ (N - 2) := by
            calc ∑ u : ZMod L, ‖∏ v, f v u‖
                = ∑ u : ZMod L, ‖f q u‖ * ∏ v ∈ (univ.erase q).erase p, ‖f v u‖ := by
                  refine sum_congr rfl fun u _ => ?_
                  rw [norm_prod, ← mul_prod_erase _ (fun v => ‖f v u‖) (mem_univ q),
                    ← mul_prod_erase _ (fun v => ‖f v u‖) (mem_erase.2 ⟨Ne.symm hqp, mem_univ _⟩),
                    hfp, norm_one, one_mul]
              _ ≤ (∑ u : ZMod L, ‖f q u‖) * ∏ _v ∈ (univ.erase q).erase p, A :=
                  sum_mul_prod_le _ (fun v u => ‖f v u‖) _ _ (fun u => norm_nonneg _)
                    (fun v u => norm_nonneg _) fun v hv u => by
                      have hvp := ne_of_mem_erase hv
                      have := hsup' v u; rwa [hf'v v hvp] at this
              _ ≤ η⁻¹ * A ^ (N - 2) := by
                  rw [prod_const, hcard]
                  gcongr
                  have := hl1q q hqp; rwa [hf'v q hqp] at this
          calc ∑ u, ‖T τ u‖ = (∑ u : ZMod L, ‖∏ v, f v u‖) * ‖∑ s ∈ pinned L N p, g s‖ := by
                simp only [hT, norm_mul, sum_mul]
            _ ≤ (η⁻¹ * A ^ (N - 2)) * (Csz * η) := by gcongr
            _ = Csz * A ^ (N - 2) := by field_simp
            _ ≤ B := by
                simp only [B, K0]
                have : 0 ≤ (19 / 4 * SW + 3 * (3 / 2) ^ (N - 2) * SW) * A ^ (N - 2) := by
                  positivity
                nlinarith
    · push Not at hval
      have hW : ∀ s : Fin N → ZMod L, ∑ c, ∏ v, ‖taylorTerm (f v) (τ v) c (s v)‖ ≤
          3 * ℓ * (3 / 2) ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := fun s =>
        sum_prod_taylor_le_noval f p hfp hgrad hlap hG1 hG2 τ hτp hval s (by omega)
      calc ∑ u, ‖T τ u‖
          ≤ ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖taylorTerm (f v) (τ v) u (s v)‖ :=
            habs τ
        _ ≤ ∑ s ∈ pinned L N p, ‖g s‖ *
              (3 * ℓ * (3 / 2) ^ (N - 2) * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2) :=
            sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hW s) (norm_nonneg _)
        _ = 3 * ℓ * (3 / 2) ^ (N - 2) *
              ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ((1 : ℝ) + zdist L (s v)) ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
        _ ≤ 3 * ℓ * (3 / 2) ^ (N - 2) * SW := by gcongr
        _ ≤ 3 * A ^ (N - 2) * (3 / 2) ^ (N - 2) * SW := by
            gcongr; exact hℓA.trans hApow
        _ ≤ B := by
            simp only [B, K0]
            have : 0 ≤ (Csz + 19 / 4 * SW) * A ^ (N - 2) := by positivity
            nlinarith
  calc ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
      ≤ ∑ u : ZMod L, ∑ τ : Fin N → Fin 3, ‖T τ u‖ := by
        refine sum_le_sum fun u _ => ?_
        rw [hexp u]; exact norm_sum_le _ _
    _ = ∑ τ : Fin N → Fin 3, ∑ u : ZMod L, ‖T τ u‖ := sum_comm
    _ ≤ ∑ τ : Fin N → Fin 3, B := sum_le_sum fun τ _ => hterm τ
    _ = 3 ^ N * B := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring
    _ = 3 ^ N * (K0 * e8 ^ (N - 2)) * (η * ℓ)⁻¹ ^ (N - 2) := by
        simp only [B, A, mul_pow]; ring

/-- **`sum_norm_innerId_short_le`, reordered.** Its constant is already explicit in `k`, `N`
(no `sum_zero` call); a plain reorder. -/
theorem sum_norm_innerId_short_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ' : Fin N → Bool) (p : Fin N), (∃ v, v ≠ p ∧ σ' v = σ' (v + 1)) →
        ∀ a' : Fin N → ZMod L,
          ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
            ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
  set Bk := 2 * cTwo52 / Real.sqrt k + 1
  set κ := cZero * Real.sqrt (Real.sqrt k)
  have hδ : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hκ : 0 < κ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hBk : 1 ≤ Bk := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / Real.sqrt k := by positivity
    simp only [Bk]; linarith
  set S1 := 2 / (1 - Real.exp (-κ))
  have hS1 : 0 ≤ S1 := (zero_le_one.trans (one_le_two_div hκ))
  set SW0 := sigWeightConst N k 0
  have hSW0 : 0 ≤ SW0 := sigWeightConst_nonneg hk0 0
  set e8 := 8 * Real.exp 1
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨SW0 * (Bk * S1) * (Bk * e8) ^ (N - 2), by positivity, fun E hEk => ?_⟩
  intro L _ hL t ht0 ht1 σ' p ⟨v₀, hv₀p, hv₀⟩ a'
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set η := etaT E t with hηdef
  set ℓ := ellHat L (t : ℂ) with hℓdef
  have hη : 0 < η := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ℓ := one_le_ellHat L hL ht0.le ht1
  have hηℓ : η * ℓ ≤ 1 := etaT_mul_ellHat_le hL hE2 ht0.le ht1
  have hηℓ0 : 0 < η * ℓ := by positivity
  set A := e8 * (η * ℓ)⁻¹ with hAdef
  have hA1 : 1 ≤ A := by
    have : 1 ≤ (η * ℓ)⁻¹ := one_le_inv₀ hηℓ0 |>.2 hηℓ
    simp only [A, e8]; nlinarith
  set f : Fin N → ZMod L → ℂ := innerKer (mSigma E) t σ' a' p
  have hfp : ∀ y, f p y = 1 := fun y => by simp only [f, innerKer, Function.update_self]
  have hfv : ∀ v, v ≠ p → ∀ y, f v y = thetaEdge L (mSigma E) t (σ' v) (σ' (v + 1)) (a' v) y :=
    fun v hv y => by simp only [f, innerKer, Function.update_of_ne hv]
  have hsup : ∀ v, v ≠ p → ∀ y, ‖f v y‖ ≤ Bk * A := by
    intro v hvp y
    rw [hfv v hvp]
    by_cases hv : σ' v = σ' (v + 1)
    · have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ' v) (a' v) y
      rw [← hv]
      calc _ ≤ Bk * Real.exp (-(κ * zdist L (a' v - y))) := h
        _ ≤ Bk * 1 := by
            gcongr; rw [Real.exp_le_one_iff, neg_nonpos]; positivity
        _ ≤ Bk * A := by gcongr
    · rw [thetaEdge_of_ne hE2 t hv]
      have h := norm_Theta_long_edge_le L hL hk0 (by linarith) hEk ht0 ht1 (a' v) y
      rw [← etaT_eq_zt_im, div_eq_mul_inv] at h
      calc _ ≤ A := h
        _ = 1 * A := (one_mul A).symm
        _ ≤ Bk * A := by gcongr
  have hl1 : ∀ x : ZMod L, ∑ u : ZMod L, ‖f v₀ (u + x)‖ ≤ Bk * S1 := by
    intro x
    calc ∑ u : ZMod L, ‖f v₀ (u + x)‖
        ≤ ∑ u : ZMod L, Bk * Real.exp (-(κ * zdist L (u - (a' v₀ - x)))) := by
          refine sum_le_sum fun u _ => ?_
          rw [hfv v₀ hv₀p]
          have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0.le ht1 (σ' v₀) (a' v₀) (u + x)
          rw [← hv₀]
          rw [show a' v₀ - (u + x) = -(u - (a' v₀ - x)) by ring, zdist_neg] at h
          exact h
      _ = Bk * ∑ u : ZMod L, Real.exp (-(κ * zdist L (u - (a' v₀ - x)))) := by rw [mul_sum]
      _ ≤ Bk * S1 := by gcongr; exact sum_exp_zdist_le L hκ _
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  set g : (Fin N → ZMod L) → ℂ := fun s => SigmaPi L (mSigma E) t σ' ∅ s
  have hSg := sum_pinned_SigmaPi_le hL hE hk0 hk1 hEk ht0.le ht1 σ' (by omega) 0 p
  simp only [pow_zero, prod_const_one, mul_one] at hSg
  have hmem : p ∈ univ.erase v₀ := mem_erase.2 ⟨Ne.symm hv₀p, mem_univ _⟩
  have hT : ((univ.erase v₀).erase p).card = N - 2 := by
    rw [card_erase_of_mem hmem, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega
  calc ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
      ≤ ∑ u : ZMod L, ∑ s ∈ pinned L N p, ‖g s‖ * ∏ v, ‖f v (u + s v)‖ := by
        refine sum_le_sum fun u _ => ?_
        rw [innerId_eq hL (mSigma E) hm σ' a' p u]
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => ?_))
        rw [norm_mul, norm_prod]
    _ = ∑ s ∈ pinned L N p, ‖g s‖ * ∑ u : ZMod L, ∏ v, ‖f v (u + s v)‖ := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ s ∈ pinned L N p, ‖g s‖ * ((Bk * S1) * (Bk * A) ^ (N - 2)) := by
        refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ∑ u : ZMod L, ∏ v, ‖f v (u + s v)‖
            = ∑ u : ZMod L, ‖f v₀ (u + s v₀)‖ *
                ∏ v ∈ (univ.erase v₀).erase p, ‖f v (u + s v)‖ := by
              refine sum_congr rfl fun u _ => ?_
              rw [← mul_prod_erase _ (fun v => ‖f v (u + s v)‖) (mem_univ v₀),
                ← mul_prod_erase _ (fun v => ‖f v (u + s v)‖) hmem, hfp, norm_one, one_mul]
          _ ≤ (∑ u : ZMod L, ‖f v₀ (u + s v₀)‖) * ∏ _v ∈ (univ.erase v₀).erase p, (Bk * A) :=
              sum_mul_prod_le _ (fun v u => ‖f v (u + s v)‖) _ _ (fun u => norm_nonneg _)
                (fun v u => norm_nonneg _) fun v hv u => hsup v (ne_of_mem_erase hv) _
          _ ≤ (Bk * S1) * (Bk * A) ^ (N - 2) := by
              rw [prod_const, hT]
              gcongr
              exact hl1 _
    _ = (∑ s ∈ pinned L N p, ‖g s‖) * ((Bk * S1) * (Bk * A) ^ (N - 2)) := by rw [sum_mul]
    _ ≤ SW0 * ((Bk * S1) * (Bk * A) ^ (N - 2)) := by gcongr
    _ = SW0 * (Bk * S1) * (Bk * e8) ^ (N - 2) * (η * ℓ)⁻¹ ^ (N - 2) := by
        simp only [A, mul_pow]; ring

/-- **`sum_norm_innerId_le`, reordered.** Combines the two above. -/
theorem sum_norm_innerId_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
      ∀ (σ' : Fin N → Bool) (p : Fin N), σ' p ≠ σ' (p + 1) → ∀ a' : Fin N → ZMod L,
        ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
          ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := sum_norm_innerId_alt_le_unif hk0 hk1 hN
  obtain ⟨C₂, hC₂, h₂⟩ := sum_norm_innerId_short_le_unif hk0 hk1 hN
  refine ⟨C₁ + C₂, by positivity, fun E hEk => ?_⟩
  intro L _ hL t ht0 ht1 σ' p hp a'
  have hE : |E| < 2 := by linarith
  have hX : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
    have := etaT_pos hE ht1
    have := one_le_ellHat L hL ht0.le ht1
    positivity
  by_cases halt : ∀ v, σ' v ≠ σ' (v + 1)
  · exact (h₁ E hEk L hL t ht0 ht1 σ' halt a' p).trans (by nlinarith)
  · push Not at halt
    obtain ⟨v, hv⟩ := halt
    have hvp : v ≠ p := fun h => hp (h ▸ hv)
    exact (h₂ E hEk L hL t ht0 ht1 σ' p ⟨v, hvp, hv⟩ a').trans (by nlinarith)

end InnerBoundUnif

section Lemma311Unif

/-- **`norm_Kpi_le`, reordered.** Uses `exists_uniform` (generic, no `E`) with the predicate
`P N C := ∀ E, |E| ≤ 2 - k → …`, so `Cin` is already uniform; then the outer induction on `Nmax`
threads `E, hEk` through `hC`. -/
theorem norm_Kpi_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (n : ℕ) [NeZero n], 3 ≤ n → n ≤ Nmax →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
        ∀ (σ : Fin n → Bool) (a : Fin n → ZMod L) (π : Finset (Fin n × Fin n)),
          ‖Kpi L (mSigma E) t σ a π‖ ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (n - 1) := by
  obtain ⟨Cin, hCin0, hCin⟩ := exists_uniform (P := fun N C =>
      ∀ E : ℝ, |E| ≤ 2 - k → ∀ [NeZero N], ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ t : ℝ, 0 < t → t < 1 →
        ∀ (σ' : Fin N → Bool) (p : Fin N), σ' p ≠ σ' (p + 1) → ∀ a' : Fin N → ZMod L,
          ∑ u : ZMod L, ‖innerId (mSigma E) t σ' a' p u‖
            ≤ C * (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2))
    (fun N C C' hP hCC' => by
      intro E hEk _ L _ hL t ht0 ht1 σ' p hp a'
      have hb := hP E hEk L hL t ht0 ht1 σ' p hp a'
      have : 0 ≤ (etaT E t * ellHat L (t : ℂ))⁻¹ ^ (N - 2) := by
        have := etaT_pos (by linarith : |E| < 2) ht1
        have := one_le_ellHat L hL ht0.le ht1
        positivity
      exact hb.trans (by nlinarith))
    (fun N hN => by
      have : NeZero N := ⟨by omega⟩
      obtain ⟨C, hC0, hC⟩ := sum_norm_innerId_le_unif hk0 hk1 (N := N) hN
      refine ⟨C, hC0, ?_⟩
      intro E hEk _ L _ hL t ht0 ht1 σ' p hp a'
      exact hC E hEk L hL t ht0 ht1 σ' p hp a')
    Nmax
  induction Nmax with
  | zero => exact ⟨0, le_rfl, fun E _ n _ h3 hN => by omega⟩
  | succ N ih =>
  obtain ⟨C, hC0, hC⟩ := ih (fun N' hN' hN'N => hCin N' hN' (by omega))
  by_cases h3 : 3 ≤ N + 1
  swap
  · exact ⟨C, hC0, fun E _ n _ hn hnN => by omega⟩
  have : NeZero (N + 1) := ⟨by omega⟩
  obtain ⟨Ce, hCe0, hCe⟩ := norm_Kpi_empty_le_unif hk0 hk1 (n := N + 1) h3
  refine ⟨C + Ce + Cin * C, by positivity, fun E hEk => ?_⟩
  intro n _ hn hnN L _ hL t ht0 ht1 σ a π
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set X := (etaT E t * ellHat L (t : ℂ))⁻¹ with hXdef
  have hX0 : 0 ≤ X := by
    have := etaT_pos hE ht1; have := one_le_ellHat L hL ht0.le ht1; positivity
  have hXn : 0 ≤ X ^ (n - 1) := pow_nonneg hX0 _
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · refine (hC E hEk n hn (by omega) L hL t ht0 ht1 σ a π).trans ?_
    have : 0 ≤ (Ce + Cin * C) * X ^ (n - 1) := by positivity
    nlinarith
  obtain rfl : n = N + 1 := by omega
  by_cases hπ0 : π = ∅
  · subst hπ0
    refine (hCe E hEk L hL t ht0 ht1 σ a).trans ?_
    have : 0 ≤ (C + Cin * C) * X ^ (N + 1 - 1) := by positivity
    nlinarith
  rcases (TSPlong (N + 1) σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · simp only [Kpi, hemp, sum_empty, norm_zero]; positivity
  obtain ⟨hF₀T, hπ⟩ := mem_TSPlong.1 hF₀
  have hF₀' := isTSP_of_mem_TSP hF₀T
  have hπne : π.Nonempty := nonempty_iff_ne_empty.2 hπ0
  obtain ⟨J, hJ, hinner⟩ := exists_innermost hF₀' (σ := σ) (hπ ▸ hπne)
  rw [hπ] at hJ hinner
  have hm := norm_mul_mSigma_lt_one hE2 ht0.le ht1
  have hJd : IsDiag (N + 1) J.1 J.2 := hF₀'.1 J (Flong_subset F₀ σ (hπ ▸ hJ))
  have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJ)).2
  have hw := width_of_isDiag hJd
  have hwv : wIn J = J.2.val - J.1.val := rfl
  have hw' : wIn J + 1 < N + 1 := by
    obtain ⟨-, -, hnot⟩ := hJd
    have := J.2.isLt
    simp only [wIn]
    omega
  have hw2 : 2 ≤ wIn J := by omega
  have hroot : sigmaIn σ J (Fin.last _) ≠ sigmaIn σ J (Fin.last _ + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last _) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last, wIn]; congr 1; ext; simp only; omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]; congr 1; ext; simp only; omega
    rw [e1, e2]; exact Ne.symm hJlong
  have hin := hCin (wIn J + 1) (by omega) (by omega) E hEk L hL t ht0 ht1 (sigmaIn σ J)
    (Fin.last _) hroot (aIn J a)
  have hout : ∀ w, ‖Kpi L (mSigma E) t (sigmaOut σ J) (aOut J a w)
      ((π.erase J).image (shiftOut J))‖ ≤ C * X ^ (N + 1 - wIn J + 1 - 1) := fun w =>
    hC E hEk (N + 1 - wIn J + 1) (by omega) (by omega) L hL t ht0 ht1 _ _ _
  have hξ : ‖(t : ℂ) * (mSigma E (σ J.1) * mSigma E (σ J.2))‖ ≤ 1 := by
    rw [mSigma_mul_of_ne hE2 hJlong, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]; exact ht1.le
  rw [Kpi_cut hL (by omega) (mSigma E) hm σ hF₀T hπ hJ hinner a]
  set ξ := (t : ℂ) * (mSigma E (σ J.1) * mSigma E (σ J.2))
  set A := fun u => innerId (mSigma E) t (sigmaIn σ J) (aIn J a) (Fin.last _) u
  set B := fun w => Kpi L (mSigma E) t (sigmaOut σ J) (aOut J a w) ((π.erase J).image (shiftOut J))
  have hpow : X ^ (wIn J - 1) * X ^ (N + 1 - wIn J) = X ^ (N + 1 - 1) := by
    rw [← pow_add]; congr 1; omega
  calc ‖∑ u : ZMod L, ∑ w : ZMod L, ξ * A u * SB L u w * B w‖
      ≤ ∑ u : ZMod L, ∑ w : ZMod L, ‖A u‖ * ‖SB L u w‖ * (C * X ^ (N + 1 - wIn J)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun u _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun w _ => ?_)
        rw [norm_mul, norm_mul, norm_mul]
        have hb := hout w
        rw [show N + 1 - wIn J + 1 - 1 = N + 1 - wIn J by omega] at hb
        calc ‖ξ‖ * ‖A u‖ * ‖SB L u w‖ * ‖B w‖
            ≤ 1 * ‖A u‖ * ‖SB L u w‖ * (C * X ^ (N + 1 - wIn J)) := by
              gcongr
          _ = _ := by ring
    _ = (∑ u : ZMod L, ‖A u‖) * (C * X ^ (N + 1 - wIn J)) := by
        rw [sum_mul]
        refine sum_congr rfl fun u _ => ?_
        rw [← sum_mul, ← mul_sum, sum_norm_SB_row hL u, mul_one]
    _ ≤ (Cin * X ^ (wIn J - 1)) * (C * X ^ (N + 1 - wIn J)) := by
        gcongr
        exact hin
    _ = Cin * C * X ^ (N + 1 - 1) := by rw [← hpow]; ring
    _ ≤ (C + Ce + Cin * C) * X ^ (N + 1 - 1) := by
        have : 0 ≤ (C + Ce) * X ^ (N + 1 - 1) := by positivity
        nlinarith

/-- **`norm_Kgen_le`, reordered.** -/
theorem norm_Kgen_le_unif {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| ≤ 2 - k →
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ) [NeZero W], ∀ t : ℝ, 0 < t → t < 1 →
      ∀ I : LoopIdx (ZMod L), I.WF → 3 ≤ I.length → I.length ≤ Nmax →
        ‖Kgen L W (mSigma E) t I‖ ≤
          C * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ ^ (I.length - 1) := by
  obtain ⟨C, hC0, hC⟩ := norm_Kpi_le_unif hk0 hk1 Nmax
  refine ⟨2 ^ (Nmax * Nmax) * C, by positivity, fun E hEk => ?_⟩
  intro L _ hL W _ t ht0 ht1 I hI h3 hN
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  have hm1 := norm_mSigma_le_one hE
  have : NeZero I.length := ⟨by omega⟩
  set n := I.length
  have hrep := K_eq_sum_Kpi hL W (mSigma E) hm1 ht1 (isPrimitive_Kgen hL W (mSigma E) hm1 ht1)
    subset_rfl (fun s hs J hJ hJ2 => norm_Kgen_two_le hL W (mSigma E) hm1 ht1 hs J hJ hJ2)
    ⟨ht0.le, le_rfl⟩ I hI h3
  set X := (etaT E t * ellHat L (t : ℂ))⁻¹
  have hX0 : 0 ≤ X := by
    have := etaT_pos hE ht1; have := one_le_ellHat L hL ht0.le ht1; positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hprod : ‖(I.σ.map (mSigma E)).prod‖ = 1 := by
    induction I.σ with
    | nil => simp
    | cons b l ih => rw [List.map_cons, List.prod_cons, norm_mul, ih, norm_mSigma hE2, mul_one]
  have hcard : ((diagonals n).powerset.card : ℝ) ≤ 2 ^ (Nmax * Nmax) := by
    rw [card_powerset]
    have h1 : (diagonals n).card ≤ n * n := by
      calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_card (subset_univ _)
        _ = n * n := by rw [card_univ, Fintype.card_prod, Fintype.card_fin]
    have h2 : n * n ≤ Nmax * Nmax := Nat.mul_le_mul hN hN
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (h1.trans h2)
  have hWinv : ‖(W : ℂ)⁻¹ ^ (n - 1)‖ = ((W : ℝ)⁻¹) ^ (n - 1) := by
    rw [norm_pow, norm_inv, Complex.norm_natCast]
  rw [hrep, norm_mul, norm_mul, hprod, one_mul, hWinv]
  have hsum : ‖∑ π ∈ (diagonals n).powerset,
      Kpi L (mSigma E) t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π‖
        ≤ 2 ^ (Nmax * Nmax) * (C * X ^ (n - 1)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ π ∈ (diagonals n).powerset,
          ‖Kpi L (mSigma E) t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π‖
        ≤ ∑ _π ∈ (diagonals n).powerset, C * X ^ (n - 1) :=
          sum_le_sum fun π _ => hC E hEk n h3 hN L hL t ht0 ht1 _ _ π
      _ = ((diagonals n).powerset.card : ℝ) * (C * X ^ (n - 1)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ (Nmax * Nmax) * (C * X ^ (n - 1)) := by
          have : 0 ≤ C * X ^ (n - 1) := by positivity
          gcongr
  calc ((W : ℝ)⁻¹) ^ (n - 1) * ‖∑ π ∈ (diagonals n).powerset,
          Kpi L (mSigma E) t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π‖
      ≤ ((W : ℝ)⁻¹) ^ (n - 1) * (2 ^ (Nmax * Nmax) * (C * X ^ (n - 1))) := by gcongr
    _ = 2 ^ (Nmax * Nmax) * C * ((W : ℝ) * (etaT E t * ellHat L (t : ℂ)))⁻¹ ^ (n - 1) := by
        rw [mul_inv, mul_pow]; ring

end Lemma311Unif

section Compat

end Compat

end RBM

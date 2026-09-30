/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.EnergyN.Flow.Consequences
import RBM1D.Flow.Universality

/-!
# Theorems 2.4 and 2.5 from the gained Theorem 2.21, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

Theorem 2.4 (`RBM.quantumDiffusion_of_Thm221N'`), the expectations (2.8), (2.9) at the spectral
parameters of Theorem 2.5 (`RBM.QDExpect.of_Thm221N'`) and Theorem 2.5
(`RBM.theorem2_5_of_Thm221N'`), from `RBM.Thm221N'` at an `N`-dependent Lemma 2.8 energy
`E : ℕ → ℝ`. The proofs use `RBM.SpecSeqN.boundsN'`, the statements of
`RBM1D.EnergyN.Flow.Consequences`, and `RBM.theorem2_5_of_QDExpect`,
`RBM.Band.size_mul_im_le_zScale`, `RBM.Band.eventually_size_rpow_le_W_sq` of
`Flow/Universality.lean`. Two further declarations:

* `RBM.Band.specSeqN_queZ` — the paper's own remark in the proof of Theorem 2.5 ("by (2.11) …
  `ℓ(z) = L`"): the
  Theorem 2.5 scale `η = N^{-1-τ}(W²/N)^{1/3}` lies in the domain of Theorem 2.4, with the
  `E`-independent exponent `min (B.c/6) 1` and explicit slack `B.c/2 - τ`.
* `RBM.theorem2_5_of_Thm221N'_of_E` — the paper form of Theorem 2.5, with only
  `κ, τ, E, hE` and no spectral-parameter hypothesis, obtained from the previous item.
-/

namespace RBM

open MeasureTheory Filter

section Main

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ : ℝ} {E : ℕ → ℝ}
  {z : ℕ → ℂ}

/-- **Theorem 2.4 (quantum diffusion) from the gained Theorem 2.21, at an `N`-dependent energy**. -/
theorem quantumDiffusion_of_Thm221N' (T : Transfer X) (hκ : 0 < κ) (hT : Thm221N' X κ)
    (hτ : 0 < τ) (hz : SpecSeqN κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3) := by
  have hB := hz.boundsN' X hκ hT hτ
  exact ⟨quantumDiffusion_pm_prob_of_boundsCoreN T hκ hz hB.toBoundsCoreN hτ' hD,
    quantumDiffusion_pp_prob_of_boundsCoreN T hκ hz hB.toBoundsCoreN hτ' hD,
    expect_quantumDiffusion_pm_W_of_boundsN T hκ hz hB hτ',
    expect_quantumDiffusion_pp_W_of_boundsN T hκ hz hB hτ'⟩

end Main

section Sequence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(2.8), (2.9) at the spectral parameters of Theorem 2.5, from the gained Theorem 2.21, at an
`N`-dependent Lemma 2.8 energy `E'`**. -/
theorem QDExpect.of_Thm221N' {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' : ℝ}
    {E' : ℕ → ℝ} (hκ : 0 < κ) (hT : Thm221N' X κ) (hτ' : 0 < τ') (hτ : 0 ≤ τ) (E : ℕ → ℝ)
    (hz : SpecSeqN κ τ' E' (B.queZ τ E))
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    QDExpect B T.Hband (B.queZ τ E) (fun N => Theta (B.L N)) := by
  have hB := hz.boundsN' X hκ hT hτ'
  have key : ∀ N, ((B.size N : ℕ) : ℝ) ≤ (B.W N : ℝ) ^ 2 →
      ((B.size N : ℝ) * (B.queZ τ E N).im)⁻¹ ^ 3 ≥ (B.zScale N (B.queZ τ E N))⁻¹ ^ 3 := by
    intro N hWN
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    have hpos : 0 < (B.size N : ℝ) * (B.queZ τ E N).im := mul_pos (by linarith) (hz.im_pos N)
    exact pow_le_pow_left₀ (inv_nonneg.2 (B.zScale_pos N (hz.im_pos N)).le)
      (inv_anti₀ hpos (B.size_mul_im_le_zScale hτ E hWN)) 3
  have hWN : ∀ᶠ N : ℕ in atTop, ((B.size N : ℕ) : ℝ) ≤ (B.W N : ℝ) ^ 2 := by
    filter_upwards [B.eventually_size_rpow_le_W_sq] with N h
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    refine le_trans ?_ h
    calc ((B.size N : ℕ) : ℝ) = ((B.size N : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [B.c_pos])
  refine ⟨hint_pp, hint_pm, fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [expect_quantumDiffusion_pm_W_of_boundsN T hκ hz hB hδ, hWN] with N h hW x y
    have h1 := h (x, y)
    rw [← mul_assoc]
    refine h1.trans (mul_le_mul_of_nonneg_left (key N hW) (by positivity))
  · filter_upwards [expect_quantumDiffusion_pp_W_of_boundsN T hκ hz hB hδ, hWN] with N h hW x y
    have h1 := h (x, y)
    rw [← mul_assoc]
    refine h1.trans (mul_le_mul_of_nonneg_left (key N hW) (by positivity))

/-- **Theorem 2.5 from the gained Theorem 2.21, at an `N`-dependent Lemma 2.8 energy `E'`**. -/
theorem theorem2_5_of_Thm221N' {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' : ℝ}
    {E' : ℕ → ℝ} (hκ : 0 < κ) (hT : Thm221N' X κ) (hτ' : 0 < τ') (hτ0 : 0 < τ)
    (hτ : τ < B.c / 2) (E : ℕ → ℝ) (hz : SpecSeqN κ τ' E' (B.queZ τ E))
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (T.hermitian N) a (E N) (B.queEtaN τ N) ((B.size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (T.hermitian N) A (E N) (B.queEtaN τ N) τ) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) :=
  theorem2_5_of_QDExpect B hκ hτ0 hτ T.Hband T.hermitian E
    (fun N => by have := hz.abs_re_le N; rwa [B.queZ_re] at this)
    (QDExpect.of_Thm221N' T hκ hT hτ' hτ0.le E hz hint_pp hint_pm)

/-- **The paper's own remark in the proof of Theorem 2.5** ("by (2.11) … `ℓ(z) = L`"): the Theorem
2.5 scale `η = N^{-1-τ}(W²/N)^{1/3}` lies in the domain of Theorem 2.4, with the `E`-independent
exponent `min (B.c/6) 1`. -/
theorem Band.specSeqN_queZ {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {κ τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ < B.c / 2) (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ) :
    SpecSeqN κ (min (B.c / 6) 1) (fun N => lemE (B.queZ τ E N)) (B.queZ τ E) := by
  have hτ1le1 : min (B.c / 6) 1 ≤ (1 : ℝ) := min_le_right _ _
  have hτ1lec6 : min (B.c / 6) 1 ≤ B.c / 6 := min_le_left _ _
  refine ⟨fun N => ?_, fun N => ?_, fun N => ?_, ?_, fun _ => rfl⟩
  · rw [B.queZ_im]
    exact queEta_pos (by exact_mod_cast B.one_le_size N) (by exact_mod_cast B.W_pos N)
  · rw [B.queZ_im]
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hWsize : (B.W N : ℝ) ≤ (B.size N : ℝ) := by
      have hL : (3 : ℝ) ≤ (B.L N : ℝ) := by exact_mod_cast B.three_le_L N
      have hW0' : (0 : ℝ) ≤ (B.W N : ℝ) := hW0.le
      rw [Band.size]; push_cast; nlinarith
    exact queEta_le_one hn1 hW0 hWsize hτ0
  · rw [B.queZ_re]; exact hE N
  · filter_upwards [B.eventually_size_rpow_le_W_sq, B.dim, eventually_ge_atTop 1]
      with N hWc hdimN hN1
    rw [B.queZ_im]
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hnN : (B.size N : ℝ) ≤ (N : ℝ) := by
      have h1 : B.size N ≤ N := by rw [Band.size, mul_comm]; exact hdimN.1
      exact_mod_cast h1
    have hkey : (B.size N : ℝ) ^ (-1 - τ + 2 * B.c / 3) ≤ B.queEtaN τ N :=
      rpow_le_queEta (τ := τ) hn1 hW0 hWc
    have hslack : min (B.c / 6) 1 ≤ (-1 - τ + 2 * B.c / 3) + 1 := by
      have h6 : B.c / 6 ≤ 2 * B.c / 3 - τ := by linarith
      calc min (B.c / 6) 1 ≤ B.c / 6 := hτ1lec6
        _ ≤ 2 * B.c / 3 - τ := h6
        _ = (-1 - τ + 2 * B.c / 3) + 1 := by ring
    rcases lt_or_ge (0 : ℝ) (-1 - τ + 2 * B.c / 3) with hesign | hesign
    · have hstep1 : (1 : ℝ) ≤ (B.size N : ℝ) ^ (-1 - τ + 2 * B.c / 3) :=
        Real.one_le_rpow hn1 hesign.le
      have hstep2 : (N : ℝ) ^ (-1 + min (B.c / 6) 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
      exact hstep2.trans (hstep1.trans hkey)
    · have hstep1 : (N : ℝ) ^ (-1 - τ + 2 * B.c / 3) ≤ (B.size N : ℝ) ^ (-1 - τ + 2 * B.c / 3) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hnN hesign
      have hstep2 : (N : ℝ) ^ (-1 + min (B.c / 6) 1) ≤ (N : ℝ) ^ (-1 - τ + 2 * B.c / 3) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      exact hstep2.trans (hstep1.trans hkey)

/-- **Theorem 2.5, paper form**: the spectral-parameter hypothesis of
`RBM.theorem2_5_of_Thm221N'` is not assumed; `RBM.Band.specSeqN_queZ` supplies it from
`κ, τ, E, hE`. -/
theorem theorem2_5_of_Thm221N'_of_E {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ : ℝ}
    (hκ : 0 < κ) (hT : Thm221N' X κ) (hτ0 : 0 < τ) (hτ : τ < B.c / 2) (E : ℕ → ℝ)
    (hE : ∀ N, |E N| ≤ 2 - κ)
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (T.hermitian N) a (E N) (B.queEtaN τ N) ((B.size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (T.hermitian N) A (E N) (B.queEtaN τ N) τ) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) :=
  theorem2_5_of_Thm221N' T hκ hT (lt_min (by linarith [B.c_pos]) one_pos) hτ0 hτ E
    (B.specSeqN_queZ hτ0.le hτ E hE) hint_pp hint_pm

end Sequence

section Compat

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ E : ℝ}

end Compat

end RBM

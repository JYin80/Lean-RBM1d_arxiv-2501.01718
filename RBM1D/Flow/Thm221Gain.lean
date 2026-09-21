/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Universality

/-!
# Theorems 2.3, 2.4 and 2.5 from the *gained* Theorem 2.21 (T179)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

`RBM.Thm221` takes the paper-literal (2.72) (`RBM.Cond272`), but the six steps of §2.7 consume
(2.72) **with an `N^c` gain** (`hregS`, i.e. `RBM.Cond272'`), which is strictly stronger.  So the
assembly of §2.7 produces `RBM.Thm221'`, not `RBM.Thm221`, and the final statements have to be
available in that form as well.  The gain is free: the grid of p. 24 supplies it by itself
(`RBM.Band.eventually_flow_grid'`), see `Flow/Iteration.lean` and `docs/paper-deltas.md`
#47/#54/#73.

This file re-runs the last three assembly steps of `Flow/Consequences.lean` and
`Flow/Universality.lean` with `RBM.Thm221'` in place of `RBM.Thm221`.  **Only the hypothesis
changes**: each conclusion is the same as the unprimed one, which is checked here by a
`rfl`-probe (`Prop` equality forces the two statements to be definitionally equal, the technique
of T107) rather than by eye.

## Main results

* `RBM.SpecSeq.bounds'` — Lemmas 2.18–2.20 at `t = lemT z`, from `RBM.Thm221'`.  This is the
  *only* place `RBM.Thm221` enters the assembly; everything below just threads it through.
* `RBM.localSemicircleLaw_of_Thm221'` — **Theorem 2.3**.
* `RBM.quantumDiffusion_of_Thm221'` — **Theorem 2.4**.
* `RBM.QDExpect.of_Thm221'`, `RBM.theorem2_5_of_Thm221'` — **Theorem 2.5**.

`RBM.Gauss.theorem2_5_gauss` (`Gauss/Thm25Gauss.lean`) still takes `RBM.Thm221`; the primed
version is the same one-liner with `RBM.theorem2_5_of_Thm221'` in place of
`RBM.theorem2_5_of_Thm221`, and belongs in that file.
-/

namespace RBM

open MeasureTheory Filter

namespace SpecSeq

variable {κ τ E : ℝ} {z : ℕ → ℂ} (hz : SpecSeq κ τ E z)
include hz
variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Lemmas 2.18–2.20 at the time `t = lemT z` of Lemma 2.8**, from the gained Theorem 2.21
(T179).  Verbatim `RBM.SpecSeq.bounds` with `RBM.Thm221'` in place of `RBM.Thm221`. -/
theorem bounds' (X : Sample B) (hκ : 0 < κ) (hT : Thm221' X κ) (hτ : 0 < τ) :
    Bounds X E (fun N => lemT (z N)) :=
  Bounds_of_Thm221' X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

end SpecSeq

section Main

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ E : ℝ} {z : ℕ → ℂ}

/-- **Theorem 2.3 (local semicircle law) from the gained Theorem 2.21** (T179): verbatim
`RBM.localSemicircleLaw_of_Thm221` with `RBM.Thm221'` in place of `RBM.Thm221`. -/
theorem localSemicircleLaw_of_Thm221' (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221' X κ) (hτ : 0 < τ) (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ij : B.Idx N × B.Idx N,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ a : ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ _u : Unit,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) := by
  have hB := hz.bounds' X hκ hT hτ
  exact ⟨localLaw_prob_of_bounds T hκ hz hB hτ' hD,
    partialTrace_prob_of_bounds T T1 hκ hz hB hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N) (trace_of_bounds T T1 hκ hz hB)
      hτ' hD⟩

/-- **Theorem 2.4 (quantum diffusion) from the gained Theorem 2.21** (T179): verbatim
`RBM.quantumDiffusion_of_Thm221` with `RBM.Thm221'` in place of `RBM.Thm221`. -/
theorem quantumDiffusion_of_Thm221' (T : Transfer X) (hκ : 0 < κ) (hT : Thm221' X κ) (hτ : 0 < τ)
    (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
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
  have hB := hz.bounds' X hκ hT hτ
  exact ⟨quantumDiffusion_pm_prob_of_bounds T hκ hz hB hτ' hD,
    quantumDiffusion_pp_prob_of_bounds T hκ hz hB hτ' hD,
    expect_quantumDiffusion_pm_W_of_bounds T hκ hz hB hτ',
    expect_quantumDiffusion_pp_W_of_bounds T hκ hz hB hτ'⟩

/-- The primed statements are the unprimed ones: `Eq` forces both sides to have the same type, so
this type-checks only if the two conclusions are definitionally equal (T107's technique). -/
example (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hT : Thm221 X κ) (hτ : 0 < τ)
    (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    localSemicircleLaw_of_Thm221 T T1 hκ hT hτ hz hτ' hD =
      localSemicircleLaw_of_Thm221' T T1 hκ (hT.toThm221' hκ) hτ hz hτ' hD := rfl

example (T : Transfer X) (hκ : 0 < κ) (hT : Thm221 X κ) (hτ : 0 < τ) (hz : SpecSeq κ τ E z)
    {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    quantumDiffusion_of_Thm221 T hκ hT hτ hz hτ' hD =
      quantumDiffusion_of_Thm221' T hκ (hT.toThm221' hκ) hτ hz hτ' hD := rfl

end Main

section Sequence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(2.8), (2.9) at the spectral parameters of Theorem 2.5, from the gained Theorem 2.21**
(T179): verbatim `RBM.QDExpect.of_Thm221` with `RBM.Thm221'` in place of `RBM.Thm221`. -/
theorem QDExpect.of_Thm221' {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' E' : ℝ}
    (hκ : 0 < κ) (hT : Thm221' X κ) (hτ' : 0 < τ') (hτ : 0 ≤ τ) (E : ℕ → ℝ)
    (hz : SpecSeq κ τ' E' (B.queZ τ E))
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    QDExpect B T.Hband (B.queZ τ E) (fun N => Theta (B.L N)) := by
  have hB := hz.bounds' X hκ hT hτ'
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
  · filter_upwards [expect_quantumDiffusion_pm_W_of_bounds T hκ hz hB hδ, hWN] with N h hW x y
    have h1 := h (x, y)
    rw [← mul_assoc]
    refine h1.trans (mul_le_mul_of_nonneg_left (key N hW) (by positivity))
  · filter_upwards [expect_quantumDiffusion_pp_W_of_bounds T hκ hz hB hδ, hWN] with N h hW x y
    have h1 := h (x, y)
    rw [← mul_assoc]
    refine h1.trans (mul_le_mul_of_nonneg_left (key N hW) (by positivity))

/-- **Theorem 2.5 from the gained Theorem 2.21** (T179): verbatim `RBM.theorem2_5_of_Thm221`
with `RBM.Thm221'` in place of `RBM.Thm221`. -/
theorem theorem2_5_of_Thm221' {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' E' : ℝ}
    (hκ : 0 < κ) (hT : Thm221' X κ) (hτ' : 0 < τ') (hτ0 : 0 < τ) (hτ : τ < B.c / 2)
    (E : ℕ → ℝ) (hz : SpecSeq κ τ' E' (B.queZ τ E))
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
    (QDExpect.of_Thm221' T hκ hT hτ' hτ0.le E hz hint_pp hint_pm)

/-- Same `rfl`-probe as above for the two Theorem 2.5 statements. -/
example {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' E' : ℝ} (hκ : 0 < κ)
    (hT : Thm221 X κ) (hτ' : 0 < τ') (hτ0 : 0 < τ) (hτ : τ < B.c / 2) (E : ℕ → ℝ)
    (hz : SpecSeq κ τ' E' (B.queZ τ E))
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    theorem2_5_of_Thm221 T hκ hT hτ' hτ0 hτ E hz hint_pp hint_pm =
      theorem2_5_of_Thm221' T hκ (hT.toThm221' hκ) hτ' hτ0 hτ E hz hint_pp hint_pm := rfl

end Sequence

end RBM

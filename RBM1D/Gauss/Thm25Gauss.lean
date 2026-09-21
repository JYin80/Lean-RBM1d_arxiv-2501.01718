/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DistEq
import RBM1D.Gauss.Hierarchy
import RBM1D.Flow.Universality

/-!
# Theorem 2.5 for the moment-route Gaussian model — T150

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.5.

`RBM.theorem2_5_of_Thm221` (`RBM1D/Flow/Universality.lean`) reduces Theorem 2.5 to Theorem 2.21
on a fixed energy slice, at the cost of two integrability hypotheses `hint_pp` / `hint_pm`: the
`2`-loops `Tr G E_x G E_y` and `Tr G E_x G* E_y` at the spectral parameter `z_N = E_N + iη_N`
must be Bochner integrable.  The T147 audit (§3, §6(c)) records these as "已卸但没接" — the work
is done elsewhere and was never connected.  This file connects it.

## What does the work

* `RBM.Gauss.integrable_gloop_Hflow` (T76): the `n`-loop of `H_u = √u X` is integrable, because
  it is continuous in `ω` (`RBM.Gauss.continuous_gloop_Hflow`) and bounded pointwise by (5.2)
  (`RBM.norm_gloop_le_of_le_abs_im`) on a probability space.  Nothing probabilistic is used —
  in particular no moment estimate.
* `RBM.gloop_pp_eq` / `RBM.gloop_pm_eq` (`RBM1D/Flow/Consequences.lean`): the two traces
  `RBM.trGG` and `RBM.trGGs` **are** the `(+,+)` and `(+,-)` `2`-loops.  The `(+,-)` direction
  needs `H` Hermitian, which `RBM.Gauss.Xmat_isHermitian` supplies.
* `RBM.Gauss.Hflow_one`: `H_1 = X`, so the flow statement at `u = 1` is a statement about the
  band matrix `X` itself — which is exactly `(RBM.Gauss.transfer_gauss d).Hband`.

The spectral parameter is off the real axis because `η_N = N^{-1-τ*}(W²/N)^{1/3} > 0`
(`RBM.queEta_pos`); that is the only thing needed of `z`.

## Main results

* `RBM.Gauss.Hflow_one` — `H_1 = X`.
* `RBM.Gauss.integrable_trGG_Xmat`, `RBM.Gauss.integrable_trGGs_Xmat` — `RBM.trGG` and
  `RBM.trGGs` of the band matrix are integrable at any `z` off the real axis.
* `RBM.Gauss.int_pp_thm25_gauss`, `RBM.Gauss.int_pm_thm25_gauss` — **the `hint_pp` / `hint_pm`
  slots** of `RBM.QDExpect.of_Thm221` and `RBM.theorem2_5_of_Thm221`.
* `RBM.Gauss.theorem2_5_gauss` — **Theorem 2.5 for the Gaussian model**, with Theorem 2.21 as
  its only remaining hypothesis.

## Deviations from the paper

None.  Integrability is Lean bookkeeping that the paper leaves implicit (`‖G‖ ≤ (Im z)^{-1}`).
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix

/-- **`H_1 = X`.**  The flow `H_u = √u X` of `RBM.Gauss.Hflow` reaches the band matrix itself at
`u = 1`, so everything proved along the flow is available for
`(RBM.Gauss.transfer_gauss d).Hband`. -/
theorem Hflow_one (d : Dims) (N : ℕ) (ω : Ω d) : Hflow d N 1 ω = Xmat d N ω := by
  simp [Hflow]

/-- **`Tr G E_x G E_y` is integrable** at any `z` off the real axis: it is the `(+,+)` `2`-loop
(`RBM.gloop_pp_eq`) of `H_1 = X`, and `RBM.Gauss.integrable_gloop_Hflow` applies with
`η := |Im z|`. -/
theorem integrable_trGG_Xmat (d : Dims) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) (x y : ZMod (d.L N)) :
    Integrable (fun ω : Ω d => trGG (Xmat d N ω) z x y) (P d) := by
  have hη : 0 < |z.im| := abs_pos.2 hz
  have hfun : (fun ω : Ω d => trGG (Xmat d N ω) z x y)
      = fun ω : Ω d => gloop (d.L N) (d.W N) (Hflow d N 1 ω) z ⟨[true, true], [x, y]⟩ := by
    funext ω
    rw [Hflow_one]
    exact (gloop_pp_eq _ _ _ _).symm
  rw [hfun]
  exact integrable_gloop_Hflow d N 1 hη le_rfl _ rfl (by norm_num)

/-- **`Tr G E_x G* E_y` is integrable**, the `(+,-)` half of
`RBM.Gauss.integrable_trGG_Xmat`; `RBM.gloop_pm_eq` needs `X` Hermitian. -/
theorem integrable_trGGs_Xmat (d : Dims) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) (x y : ZMod (d.L N)) :
    Integrable (fun ω : Ω d => trGGs (Xmat d N ω) z x y) (P d) := by
  have hη : 0 < |z.im| := abs_pos.2 hz
  have hfun : (fun ω : Ω d => trGGs (Xmat d N ω) z x y)
      = fun ω : Ω d => gloop (d.L N) (d.W N) (Hflow d N 1 ω) z ⟨[true, false], [x, y]⟩ := by
    funext ω
    rw [Hflow_one]
    exact (gloop_pm_eq (Xmat_isHermitian d N ω) _ _ _).symm
  rw [hfun]
  exact integrable_gloop_Hflow d N 1 hη le_rfl _ rfl (by norm_num)

/-- The spectral parameter of Theorem 2.5 is off the real axis: `η_N > 0` by
`RBM.queEta_pos`. -/
theorem queZ_im_ne_zero (d : Dims) (τ : ℝ) (E : ℕ → ℝ) (N : ℕ) :
    ((band d).queZ τ E N).im ≠ 0 := by
  rw [Band.queZ_im]
  exact (queEta_pos (by exact_mod_cast (band d).one_le_size N)
    (by exact_mod_cast (band d).W_pos N)).ne'

/-- **`hint_pp` of `RBM.QDExpect.of_Thm221` / `RBM.theorem2_5_of_Thm221`**, for the Gaussian
model. -/
theorem int_pp_thm25_gauss (d : Dims) (τ : ℝ) (E : ℕ → ℝ) :
    ∀ N x y, Integrable
      (fun ω => trGG ((transfer_gauss d).Hband N ω) ((band d).queZ τ E N) x y) (band d).P :=
  fun N x y => integrable_trGG_Xmat d N (queZ_im_ne_zero d τ E N) x y

/-- **`hint_pm` of `RBM.QDExpect.of_Thm221` / `RBM.theorem2_5_of_Thm221`**, for the Gaussian
model. -/
theorem int_pm_thm25_gauss (d : Dims) (τ : ℝ) (E : ℕ → ℝ) :
    ∀ N x y, Integrable
      (fun ω => trGGs ((transfer_gauss d).Hband N ω) ((band d).queZ τ E N) x y) (band d).P :=
  fun N x y => integrable_trGGs_Xmat d N (queZ_im_ne_zero d τ E N) x y

/-- **Theorem 2.5 for the moment-route Gaussian model**, on a fixed energy slice of Lemma 2.8.

The only hypothesis left beyond the regime conditions is `RBM.Thm221` — the two integrability
slots of `RBM.theorem2_5_of_Thm221` are discharged, and `RBM.Transfer` is the *proved*
`RBM.Gauss.transfer_gauss` (T111), not a hypothesis. -/
theorem theorem2_5_gauss (d : Dims) {κ τ τ' E' : ℝ} (hκ : 0 < κ)
    (hT : RBM.Thm221 (sample d) κ) (hτ' : 0 < τ') (hτ0 : 0 < τ) (hτ : τ < (band d).c / 2)
    (E : ℕ → ℝ) (hz : RBM.SpecSeq κ τ' E' ((band d).queZ τ E)) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod ((band d).L N),
      (band d).P (queEvent212 ((transfer_gauss d).hermitian N) a (E N)
          ((band d).queEtaN τ N) (((band d).size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod ((band d).L N)), A.Nonempty →
      (band d).P (queEvent213 ((transfer_gauss d).hermitian N) A (E N)
          ((band d).queEtaN τ N) τ) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) :=
  theorem2_5_of_Thm221 (transfer_gauss d) hκ hT hτ' hτ0 hτ E hz
    (int_pp_thm25_gauss d τ E) (int_pm_thm25_gauss d τ E)

end RBM.Gauss

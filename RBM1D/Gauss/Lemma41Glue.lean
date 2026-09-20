/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EntryBoundGauss
import RBM1D.Hierarchy.Step1

/-!
# The interface between `Green/EntryBound.lean` and `Hierarchy/Step1.lean` — T102

`RBM.Lemma41Flow` of `RBM1D/Hierarchy/Step1.lean` is stated in the language of
`RBM.Sample` (`Lval`, `llErr`, `llMax`, `goodEv`), while `RBM.entry_bound_stochDom` and
`RBM.diag_bound_stochDom` are stated in the language of `RBM1D/Green/EntryBound.lean`
(`Lre`, `GoodEvent`, `goodSet`).  The two match; this file writes the dictionary.

It also isolates what is *not* an interface question: `Lemma41Flow` quantifies over
`u ∈ [s_N, t_N]` **inside** the index set of `≺`, while `RBM.Gauss.entry_bound_gauss` and
`RBM.Gauss.diag_bound_gauss` are statements at one fixed `u`.  Bridging that needs a Hölder
modulus in `u` valid uniformly in `ω`, whose constant is `η^{-2}‖X‖` — see `docs/STATUS.md`
(T99) and tickets T100/T101.  Nothing in this file touches that.

## Main statements

* `RBM.norm_gloop_pm_eq_Lre` : `‖L_{(+,-),(a,b)}‖ = L^{re}_{(+,-),(a,b)}` — the `2`-loop is a
  nonnegative real
* `RBM.Sample.llErr_eq`      : `llErr` is the entrywise quantity of `RBM.GoodEvent`
* `RBM.Step1.goodEv_eq_setOf_goodEvent` : `goodEv` is `RBM.GoodEvent` at a fixed time
* `RBM.Gauss.sample_Lval_pm` : the Gaussian sample's `2`-loop is `Lre` of the flow
-/

namespace RBM

open MeasureTheory Filter Finset

/-! ### The `(+,-)` two-loop is a nonnegative real -/

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `‖L_{(+,-),(a,b)}‖ = L^{re}_{(+,-),(a,b)}`: the two-loop of `RBM.pmLoop` equals
`W⁻²∑_{β,α}|G_{(b,β),(a,α)}|²`, a nonnegative real, so its norm is its real part. -/
theorem norm_gloop_pm_eq_Lre {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (a b : ZMod L) :
    ‖gloop L W H z ⟨[true, false], [a, b]⟩‖ = Lre H z a b := by
  have hval : gloop L W H z ⟨[true, false], [a, b]⟩
      = (((((W : ℝ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W,
          ‖green H z (b, β) (a, α)‖ ^ 2 : ℝ)) : ℂ) := by
    rw [gloop_two_plus_minus_blocks hH]
    push_cast
    simp_rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg, Lre_eq hH]
  have : (0 : ℝ) ≤ ∑ β : Fin W, ∑ α : Fin W, ‖green H z (b, β) (a, α)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- `llErr` is exactly the entrywise quantity of `RBM.GoodEvent`. -/
theorem llErr_eq (N : ℕ) (t : ℝ) (ω : Ω) (ij : B.Idx N × B.Idx N) :
    X.llErr E N t ω ij
      = ‖X.G E N t ω ij.1 ij.2 - (if ij.1 = ij.2 then mE E else 0)‖ := by
  show ‖(X.G E N t ω - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖ = _
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

end Sample

namespace Step1

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- `goodEv` is `RBM.GoodEvent` at the threshold `(Wℓ_uη_u)^{-1/6}`. -/
theorem goodEv_eq_setOf_goodEvent (N : ℕ) (u : ℝ) :
    goodEv X E N u
      = {ω | GoodEvent (X.G E N u ω) (mE E) ((B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6))} := by
  ext ω
  simp only [goodEv, GoodEvent, Set.mem_ofPred_eq]
  constructor
  · intro h x y
    rw [← X.llErr_eq N u ω (x, y)]
    exact le_trans (llErr_le_llMax X N u ω (x, y)) h
  · intro h
    refine llMax_le X ?_
    intro ij
    rw [X.llErr_eq N u ω ij]
    exact h ij.1 ij.2

end Step1

namespace Gauss

variable {d : Dims}

/-- The Gaussian sample's Green function is the resolvent of the flow. -/
@[simp] theorem sample_G (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) :
    (sample d).G E N u ω = green (Hflow d N u ω) (zt E u) := rfl

/-- **The Gaussian sample's `2`-loop is `Lre` of the flow.** -/
theorem sample_Lval_pm (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) (a b : ZMod (d.L N)) :
    ‖(sample d).Lval E N u ω (pmLoop a b)‖
      = Lre (Hflow d N u ω) (zt E u) a b :=
  norm_gloop_pm_eq_Lre (Hflow_isHermitian d N u ω) a b

/-- **`goodEv` of the Gaussian sample is `RBM.goodSet` of the flow**, at a fixed time `u`
and with `δ_N = (Wℓ_uη_u)^{-1/6}`.  This is the event `Ω(t,c)` of (4.1) in both languages. -/
theorem goodEv_eq_goodSet (E : ℝ) (N : ℕ) (u : ℝ) :
    Step1.goodEv (sample d) E N u
      = goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N u ω) (zt E u) (mE E)
          (fun N => ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 6)) N :=
  Step1.goodEv_eq_setOf_goodEvent (sample d) N u

end Gauss

end RBM

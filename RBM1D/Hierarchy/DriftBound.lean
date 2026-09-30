/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.DriftDef

/-!
# The power counts (5.76) as pointwise bounds on `L - K`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.76), in the form used by Lemma 5.10, (5.77).

(5.76) defines `Ξ^{(L-K)}_{u,j}` from the maximum of `|(L-K)_{u,σ,a}|` over the loops of length
`j`, normalized by `A^j`, `A = W ℓ_u η_u` (`RBM.Band.scale`).  The bounds of
`RBM1D/Hierarchy/Decay.lean` on the three summands of the drift in (5.77)
(`RBM.Decay.norm_couplingLen_le'`, `RBM.Decay.norm_primBil_sub_le`, `RBM.Decay.norm_eG_le`) take
their inputs in the pointwise form `|(L-K)_J| ≤ Φ A^{-|J|}`.  This file gives that form.

## Main results

* `RBM.DriftBound.exists_loopData` — every well-formed loop index is the index of a
  `RBM.LoopData`.
* `RBM.DriftBound.norm_lk_le` — `|(L - K)_{u,σ,a}| ≤ Ξ^{(L-K)}_{u,j} (Wℓ_uη_u)^{-j}` for a loop
  of length `j`: (5.76) read backwards.
-/

namespace RBM
namespace DriftBound

open Matrix Finset Real

/-! ### Truncating the second argument of the coupling below length `2` -/

section Trunc

variable (L : ℕ) [NeZero L]

variable {L}

variable (L)

end Trunc

/-! ### Every well-formed loop index is the index of a `LoopData` -/

section Repr

theorem exists_loopData {L : ℕ} (J : LoopIdx (ZMod L)) (hJ : J.WF) :
    ∃ d : LoopData L J.length, LoopData.idx d = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [LoopIdx.length]
  refine ⟨(fun i => σ.get (Fin.cast hJ.symm i), fun i => a.get i), ?_⟩
  have hσ' : List.ofFn (fun i : Fin a.length => σ.get (Fin.cast hJ.symm i)) = σ := by
    apply List.ext_get <;> simp [hJ]
  have ha' : List.ofFn (fun i : Fin a.length => a.get i) = a := List.ofFn_get a
  rw [LoopData.idx, hσ', ha']

end Repr

/-! ### The power counts (5.76) as pointwise bounds -/

section Counts

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `|(L - K)_{u,σ,a}| ≤ Ξ^{(L-K)}_{u,j} (Wℓ_uη_u)^{-j}` — (5.76) read backwards. -/
theorem norm_lk_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (hA : B.scale E N u ≠ 0) (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF) {j : ℕ}
    (hj : J.length = j) :
    ‖(gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u) J‖
      ≤ X.xiLK E N u ω j * (B.scale E N u)⁻¹ ^ j := by
  obtain ⟨d, hd⟩ := exists_loopData J hJ
  have h1 : X.lkErr E N u ω J ≤ X.lkMax E N u ω J.length := by
    have := X.lkErr_le_lkMax (E := E) (t := u) (ω := ω) d
    rwa [hd] at this
  subst hj
  have h2 : X.xiLK E N u ω J.length * (B.scale E N u)⁻¹ ^ J.length
      = X.lkMax E N u ω J.length := by
    rw [Sample.xiLK, mul_assoc, ← mul_pow, mul_inv_cancel₀ hA, one_pow, mul_one]
  rw [h2]
  exact h1

end Counts

/-! ### (5.77), lines 1-3, pointwise -/

section Pointwise

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end Pointwise

/-! ### The drift along the flow -/

section Hyp

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
  {n : ℕ}

end Hyp

/-! ### (5.77), lines 1-3, as a `≺` statement -/

section Stoch

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
  {n : ℕ}

end Stoch


/-! ### The moment input of the Duhamel bound -/

section Hfmom

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
  {n : ℕ}

end Hfmom

end DriftBound
end RBM

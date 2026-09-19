/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.WardGeneral
import RBM1D.Loop.TreeRepGeneral

/-!
# Ward's identity and cyclic invariance for the primitive loop itself

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.6 without hypotheses.

`RBM.ward_of_isPrimitive` and `RBM.isPrimitive_rot` hold for any solution of Definition 2.12
with bounded `2`-loops.  Lemma 3.4 (`RBM.isPrimitive_Kgen`, `RBM.norm_Kgen_two_le`) provides
such a solution, the tree representation `Kgen`, and by uniqueness it is *the* primitive loop.
So both statements hold for `K = Kgen` with `m = m^{(E)}`, `|E| < 2`, for every `0 ≤ t < 1`,
with no further assumption.

## Main results

* `RBM.Kgen_rot`        : `K_{t, rot(σ,a)} = K_{t,σ,a}`
* `RBM.ward_Kgen`       : **Lemma 3.6, (3.13)**,
  `∑_x K_{t,(+,μ,-),(a',x)} = (K_{t,(+,μ),a'} - K_{t,(-,μ),a'}) / (2 W i η_t)`
-/

namespace RBM

open LoopIdx

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] {E : ℝ} (hE : |E| < 2)
include hL hE

omit [NeZero L] hL in
theorem norm_mSigma_le_one (s : Bool) : ‖mSigma E s‖ ≤ 1 :=
  (norm_mSigma hE.le s).le

/-- **Cyclic invariance of the primitive loop**, for `0 ≤ t < 1`. -/
theorem Kgen_rot {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (h2 : 2 ≤ I.length) : Kgen L W (mSigma E) t I.rot = Kgen L W (mSigma E) t I :=
  isPrimitive_rot L hL W (mSigma E)
    (isPrimitive_Kgen hL W (mSigma E) (norm_mSigma_le_one hE) ht1) subset_rfl
    (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹ * (1 - t)⁻¹)
    (fun _ hs J hJ hJ2 => norm_Kgen_two_le hL W (mSigma E) (norm_mSigma_le_one hE) ht1 hs J
      hJ hJ2) t ⟨ht0, le_rfl⟩ I hI h2

/-- **Lemma 3.6, (3.13), for the primitive loop**: for `0 ≤ t < 1` and every loop
`(+, μ, -; a', x)`,
`∑_x K_{t,(+,μ,-),(a',x)} = (K_{t,(+,μ),a'} - K_{t,(-,μ),a'}) / (2 W i η_t)`. -/
theorem ward_Kgen {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (μ : List Bool) (a' : List (ZMod L))
    (hμ : μ.length + 1 = a'.length) :
    ∑ x : ZMod L, Kgen L W (mSigma E) t ⟨true :: μ ++ [false], a' ++ [x]⟩
      = (Kgen L W (mSigma E) t ⟨true :: μ, a'⟩ - Kgen L W (mSigma E) t ⟨false :: μ, a'⟩)
          / (2 * W * Complex.I * etaT E t) :=
  sum_fullLoop_eq L hL W hE
    (isPrimitive_Kgen hL W (mSigma E) (norm_mSigma_le_one hE) ht1) ht1 subset_rfl
    (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹ * (1 - t)⁻¹)
    (fun _ hs J hJ hJ2 => norm_Kgen_two_le hL W (mSigma E) (norm_mSigma_le_one hE) ht1 hs J
      hJ hJ2) ⟨ht0, le_rfl⟩ μ a' hμ

end RBM

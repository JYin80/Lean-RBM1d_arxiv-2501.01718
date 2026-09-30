/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma41Glue
import RBM1D.Hierarchy.StepGlue

/-!
# The `1`-loop `L - K` as a block average: (4.5) along the flow

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.5).

(4.5) is used **uniformly in `u ∈ [s_N, t_N]`**: the time sits inside the index set of `≺`, and
the spectral parameter `z = z_u` follows the index.  At a fixed time the proof of (4.5) is
`RBM.StochDom.of_det` on the deterministic lemma `RBM.norm_trace_green_sub_mul_Eblk_le`, which
is pointwise in `(N, ω, u)`; so no time net and no continuity in `u` are needed to carry it
along the flow.

## Main results

* `RBM.Gauss.lkErr_one_eq_norm_trace` — the `1`-loop `L - K` **is** the block average
  `⟨(G_u - m) E_a⟩`, for **both** charges `σ` (for `σ = -` the two differ by a complex
  conjugation, which the norm does not see).  Deterministic, no hypotheses, for an arbitrary
  `X : RBM.Sample B`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

section General

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- The `1`-loop `L - K` is the block average `⟨(G_u - m) E_a⟩`, for **both** charges. -/
theorem lkErr_one_eq_norm_trace (X : Sample B) {N : ℕ} {u : ℝ} {ω : Ω}
    (v : LoopData (B.L N) 1) :
    X.lkErr E N u ω v.idx
      = ‖Matrix.trace ((green (X.H N u ω) (zt E u)
          - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0))‖ := by
  set H := X.H N u ω with hHdef
  set z := zt E u with hzdef
  have hidx : v.idx = (⟨[v.1 0], [v.2 0]⟩ : LoopIdx (ZMod (B.L N))) := by simp [LoopData.idx]
  have hLK : X.Lval E N u ω v.idx - B.Kval E N u v.idx
      = Matrix.trace ((Gsig H z (v.1 0) - mSigma E (v.1 0) •
          (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0)) := by
    rw [hidx, Sample.Lval, Band.Kval, Kgen_one, gloop, gloopProd_cons, gloopProd_nil,
      Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, trace_Eblk, mul_one]
  rw [Sample.lkErr, hLK, trace_sub_mul_Eblk, trace_sub_mul_Eblk]
  cases hv : v.1 0 with
  | true => simp only [Gsig_true, mSigma_true]
  | false =>
    rw [mSigma_false]
    have hG : Gsig H z false = Matrix.conjTranspose (Gsig H z true) :=
      (Gsig_conjTranspose (X.hermitian N u ω) z true).symm
    have hconj : ∀ k : B.Idx N, Gsig H z false k k = (starRingEnd ℂ) (green H z k k) := by
      intro k
      rw [hG, Matrix.conjTranspose_apply, Gsig_true, Complex.star_def]
    have hsum : ∑ k, (blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
          (Gsig H z false k k - (starRingEnd ℂ) (mE E))
        = (starRingEnd ℂ) (∑ k, (blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
          (green H z k k - mE E)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Complex.conj_ofReal, map_sub, hconj k]
    rw [hsum, Complex.norm_conj]

/-! ### The three inputs of (4.5), with the time in the index set -/

/-! ### (4.5) along the flow -/

end General

/-! ### The Gaussian model -/

section Gaussian

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

end Gaussian

end RBM.Gauss

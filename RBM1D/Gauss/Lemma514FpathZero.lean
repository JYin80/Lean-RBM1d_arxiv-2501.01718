/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Iteration
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Gauss.Eq45FlowGrid
import RBM1D.Gauss.MomentDuhamelHyp

/-!
# The actual drift vanishes at the first-cell left endpoint

The identities here concern the literal Gaussian/sample drift at time zero, where
`H_0 = 0` and the loop observable equals its primitive datum.  The first cell has
positive length; these identities do not assert any bound at positive time.
-/

namespace RBM.Gauss

open Finset

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

private theorem loopDiff_zero_at_initial {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N)))
    (hI : I.WF) (hI1 : 1 ≤ I.length) :
    gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) I - B.Kval E N 0 I = 0 := by
  rw [X.H_zero N ω, Band.Kval]
  exact sub_eq_zero.mpr (gloop_zero_zt_zero_eq_Kgen hE.le I hI hI1)

private theorem eGterm_zero_at_initial {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (I : LoopIdx (ZMod (B.L N))) :
    eGterm (B.L N) (B.W N) (mSigma E) (0 : Matrix (B.Idx N) (B.Idx N) ℂ)
      (zt E 0) I = 0 := by
  simp [eGterm, Gsig_zero_zt_zero hE.le]

private theorem cutGlueL_diff_zero {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) (hI : I.WF)
    {k l : ℕ} (hk : k ∈ Finset.Icc 1 I.length) (hl : l ∈ Finset.Ioc k I.length)
    (a : ZMod (B.L N)) :
    gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) (I.cutGlueL k l a)
      - B.Kval E N 0 (I.cutGlueL k l a) = 0 := by
  rcases Finset.mem_Icc.mp hk with ⟨hk1, _⟩
  rcases Finset.mem_Ioc.mp hl with ⟨hkl, hl⟩
  exact loopDiff_zero_at_initial X hE N ω _ (hI.cutGlueL a hk1 hkl hl)
    (by have := LoopIdx.two_le_length_cutGlueL I a hk1 hkl hl; omega)

private theorem cutGlueR_diff_zero {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) (hI : I.WF)
    {k l : ℕ} (hk : k ∈ Finset.Icc 1 I.length) (hl : l ∈ Finset.Ioc k I.length)
    (b : ZMod (B.L N)) :
    gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) (I.cutGlueR k l b)
      - B.Kval E N 0 (I.cutGlueR k l b) = 0 := by
  rcases Finset.mem_Icc.mp hk with ⟨hk1, _⟩
  rcases Finset.mem_Ioc.mp hl with ⟨hkl, hl⟩
  exact loopDiff_zero_at_initial X hE N ω _ (hI.cutGlueR b hk1 hkl hl)
    (by have := LoopIdx.two_le_length_cutGlueR I b hk1 hkl hl; omega)

private theorem primBilLen_zero_at_initial {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) (hI : I.WF) (lK : ℕ) :
    primBilLen (B.L N) (B.W N) lK (B.Kval E N 0)
      (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J) I = 0 := by
  unfold primBilLen
  have hs : (∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length,
      ∑ a : ZMod (B.L N), ∑ b : ZMod (B.L N),
      if (I.cutGlueL k l a).length = lK then
        B.Kval E N 0 (I.cutGlueL k l a) * SB (B.L N) a b *
          (gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) (I.cutGlueR k l b)
            - B.Kval E N 0 (I.cutGlueR k l b)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · rw [cutGlueR_diff_zero X hE N ω I hI hk hl b]
      ring
    · rfl
  rw [hs, mul_zero]

private theorem primBilLenR_zero_at_initial {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) (hI : I.WF) (lK : ℕ) :
    Decay.primBilLenR (B.L N) (B.W N) lK
      (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J)
      (B.Kval E N 0) I = 0 := by
  unfold Decay.primBilLenR
  have hs : (∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length,
      ∑ a : ZMod (B.L N), ∑ b : ZMod (B.L N),
      if (I.cutGlueR k l b).length = lK then
        (gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) (I.cutGlueL k l a)
          - B.Kval E N 0 (I.cutGlueL k l a)) * SB (B.L N) a b *
          B.Kval E N 0 (I.cutGlueR k l b) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · rw [cutGlueL_diff_zero X hE N ω I hI hk hl a]
      ring
    · rfl
  rw [hs, mul_zero]

private theorem primBil_zero_at_initial {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) (hI : I.WF) :
    primBil (B.L N) (B.W N)
      (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J)
      (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J)
      I = 0 := by
  unfold primBil
  have hs : (∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length,
      ∑ a : ZMod (B.L N), ∑ b : ZMod (B.L N),
        (gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) (I.cutGlueL k l a)
          - B.Kval E N 0 (I.cutGlueL k l a)) * SB (B.L N) a b *
        (gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) (I.cutGlueR k l b)
          - B.Kval E N 0 (I.cutGlueR k l b))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [cutGlueL_diff_zero X hE N ω I hI hk hl a]
    ring
  rw [hs, mul_zero]

/-- The actual drift of (5.15) vanishes at the deterministic initial matrix.
The statement is pointwise in every Gaussian sample and every length-`n+2`
loop; it does not assume a hierarchy or a positive-time estimate. -/
theorem driftF_zero_at_initial {E : ℝ} (hE : |E| < 2)
    (N n : ℕ) (ω : Ω) (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) :
    DriftDef.driftF B E N 0 (X.H N 0 ω) σ a = 0 := by
  let I : LoopIdx (ZMod (B.L N)) := LoopData.idx (σ, a)
  have hI : I.WF := LoopData.idx_wf _
  have heG : eGterm (B.L N) (B.W N) (mSigma E) (X.H N 0 ω) (zt E 0) I = 0 := by
    rw [X.H_zero N ω]
    exact eGterm_zero_at_initial hE N I
  have hc : ∀ lK ∈ Finset.Icc 3 (n + 2),
      Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N 0)
        (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J) I = 0 := by
    intro lK _
    rw [Decay.couplingLen, primBilLen_zero_at_initial X hE N ω I hI lK,
      primBilLenR_zero_at_initial X hE N ω I hI lK, add_zero]
  have hb : primBil (B.L N) (B.W N)
      (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J)
      (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J) I = 0 :=
    primBil_zero_at_initial X hE N ω I hI
  change eGterm (B.L N) (B.W N) (mSigma E) (X.H N 0 ω) (zt E 0) I +
      (∑ lK ∈ Finset.Icc 3 (n + 2),
        Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N 0)
          (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J) I) +
      primBil (B.L N) (B.W N)
        (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J)
        (fun J => gloop (B.L N) (B.W N) (X.H N 0 ω) (zt E 0) J - B.Kval E N 0 J) I = 0
  rw [heG, Finset.sum_eq_zero hc, hb]
  ring

/-- The time-zero drift read along a genuine first-cell `MomentDuhamel.Hyp`.
The existence of `H` is an explicit input: on the Gaussian model the producer
`MomentDuhamel.gaussHypOfMoments` still requires its two moment inequalities. -/
theorem Fpath_zero_at_initial {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (H : MomentDuhamel.Hyp X E s t n) (hE : |E| < 2)
    (hs : ∀ N, s N = 0) (ht : ∀ N, 0 ≤ t N)
    (N : ℕ) (ω : Ω) (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) :
    H.Fpath N 0 ω σ a = 0 := by
  rw [DriftDef.Fpath_eq_driftF_of_lt_one H hE le_rfl one_pos
    (hs N).le (ht N) ω σ a]
  exact driftF_zero_at_initial X hE N n ω σ a

/-- The projected drift tensor at the first-cell left endpoint is exactly zero.
This is the tensor appearing in the `hEnvF` row of the weighted Q producer. -/
theorem Qop_Fpath_zero_at_initial {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (H : MomentDuhamel.Hyp X E s t n) (hE : |E| < 2)
    (hs : ∀ N, s N = 0) (ht : ∀ N, 0 ≤ t N)
    (N : ℕ) (ω : Ω) (σ : Fin (n + 2) → Bool) :
    Qop (B.L N) (0 : ℂ) (H.Fpath N 0 ω σ) = 0 := by
  have hF : H.Fpath N 0 ω σ = 0 := by
    funext a
    exact Fpath_zero_at_initial X H hE hs ht N ω σ a
  rw [hF, FastDecayFlow.Qop_zero]

end RBM.Gauss

namespace RBM.Gauss

/-- The Gaussian `Hyp` producer made explicit: its two moment inequalities remain
named inputs.  This is not an unconditional construction of that hypothesis. -/
theorem gaussHypOfMoments_Fpath_zero_at_initial (d : Dims)
    {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2) (hs : ∀ N, s N = 0) (ht : ∀ N, 0 ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (cMD : ℕ → ℝ) (hcMD : ∀ p, 0 ≤ cMD p)
    (hmd : MomentDuhamel.MomentIneq (sample d) E s t n cMD)
    (hmdQ : MomentDuhamel.MomentIneqQ (sample d) E s t n cMD)
    (N : ℕ) (ω : Ω d) (σ : Fin (n + 2) → Bool)
    (a : LoopArg ((band d).L N) (n + 2)) :
    let H := MomentDuhamel.gaussHypOfMoments d E s t n hE
      (fun N => by rw [hs N]) ht1 cMD hcMD hmd hmdQ
    H.Fpath N 0 ω σ a = 0 := by
  exact Fpath_zero_at_initial (sample d)
    (MomentDuhamel.gaussHypOfMoments d E s t n hE
      (fun N => by rw [hs N]) ht1 cMD hcMD hmd hmdQ)
    hE hs ht N ω σ a

/-- The exact identity has a genuine growing Gaussian first-cell witness.
The cell length and the deterministic normalization are positive even though
the time-zero drift is identically zero. -/
theorem driftF_zero_first_cell_exampleGrow :
    ∀ᶠ N : ℕ in Filter.atTop,
      gridT (((band Dims.exampleGrow).W N : ℕ) : ℝ) 1 (1 / 2 : ℝ) 0 <
        gridT (((band Dims.exampleGrow).W N : ℕ) : ℝ) 1 (1 / 2 : ℝ) 1 ∧
      0 < (band Dims.exampleGrow).scale 0 N 0 ∧
      ∀ (ω : Ω Dims.exampleGrow) (n : ℕ) (σ : Fin (n + 2) → Bool)
        (a : LoopArg ((band Dims.exampleGrow).L N) (n + 2)),
        DriftDef.driftF (band Dims.exampleGrow) 0 N 0
          ((sample Dims.exampleGrow).H N 0 ω) σ a = 0 := by
  filter_upwards [first_cell_window_nondegenerate Dims.exampleGrow one_pos] with N hwin
  refine ⟨hwin, ?_, ?_⟩
  · exact (band Dims.exampleGrow).scale_pos' (by norm_num : |(0 : ℝ)| < 2)
      N le_rfl one_pos
  · intro ω n σ a
    exact driftF_zero_at_initial (sample Dims.exampleGrow)
      (by norm_num : |(0 : ℝ)| < 2) N n ω σ a

end RBM.Gauss

#print axioms RBM.Gauss.driftF_zero_at_initial
#print axioms RBM.Gauss.Fpath_zero_at_initial
#print axioms RBM.Gauss.Qop_Fpath_zero_at_initial
#print axioms RBM.Gauss.gaussHypOfMoments_Fpath_zero_at_initial
#print axioms RBM.Gauss.driftF_zero_first_cell_exampleGrow

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellJGCap

/-!
# A one-time actual full evolved QV bound

The Gaussian sample, length-four/six source, and actual block `jG` cap are the
same ones in T366. The conclusion is at one positive first-cell time only.
-/

namespace RBM.APrimeFirstCellQVPointwise

open Filter Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

open APrimeFirstCellJGCap

/-- One actual Gaussian sample realizes T334's complete pointwise evolved QV
profile at the positive time `N⁻²⁴⁸`, for every length-two label. -/
theorem exists_positive_firstTime_full_qv :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Gauss.Ω d,
        ‖Xmat d N ω‖ ≤ (N : ℝ) ∧
        0 < firstTime N ∧
        firstTime N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) ∧
        sourceEll ζ N < 1 ∧
        (∀ p : ℕ, APrimeSmoothWeightActual.weight d 0 60 δ
          (firstCellS τ') (firstCellT τ')
          (fun M => (max 1 M : ℝ) ^ (248 : ℕ)) 2 p N 2 N ω = 1) ∧
        APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (firstTime N) ω
          (sourceEll ζ N) (sourceC4 ζ N) ∧
        APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
          (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤ (N : ℝ) ∧
        ∀ a : LoopArg (d.L N) 2,
          0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2) ∧
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2)
            (firstTime N) ω ≤
          ((APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2))⁻¹ *
            APrimeFullQV.rootProfile (Gauss.band d) 0 N (firstTime N) (1 / 2) 60
              (sourceEll ζ N)
              (APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
                (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60)
              (sourceC4 ζ N) ((d.W N : ℝ)⁻¹) a) ^ 2 := by
  obtain ⟨τ', hτ', hw⟩ :=
    APrimeFirstCellJGCap.exists_positive_time_firstCell_jG_witness
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ δ hδ
  filter_upwards [hw ζ hζ δ hδ,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales] with N hwN hsc
  obtain ⟨ω, hnorm, hpos, hmem, hellLt, hweight, hsource, hJ⟩ := hwN
  obtain ⟨hW, hlog4, hlog, hN, heta, hAu, hAN, hWL, hNW⟩ := hsc
  have hell : 0 < sourceEll ζ N := by
    unfold sourceEll
    have hNpos : (0 : ℝ) < N := by linarith
    exact Real.rpow_pos_of_pos (by positivity) _
  have huv : firstTime N ≤ 1 / 2 := by
    have ht : firstCellT τ' N ≤ 1 / 2 := by
      change gridT (B.W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
      exact gridT_le (1 / 2 : ℝ) 1
    exact hmem.2.trans ht
  refine ⟨ω, hnorm, hpos, hmem, hellLt, hweight, hsource, hJ, ?_⟩
  intro a
  constructor
  · exact APrimeDriftTimeFamily.driftScale_pos d (D := 60)
      (by norm_num) (by norm_num) (by norm_num) N a
  · exact APrimeFullQV.qvAt_full_absorbed d
      (E := 0) (D := 60) (s := 0) (u := firstTime N) (v := 1 / 2)
      (by norm_num) (le_of_lt hpos) (le_of_lt hpos) huv (by norm_num)
      N ω a hsource hell (by norm_num) hW hlog4 hlog hN heta hAu hAN hWL hNW hJ

#print axioms exists_positive_firstTime_full_qv

end RBM.APrimeFirstCellQVPointwise

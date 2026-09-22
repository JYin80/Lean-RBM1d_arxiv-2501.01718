/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVPointwise

/-! T392: the separate near, quadratic-J, cubic-J and leakage rows at the
first positive cut-net time. -/

namespace RBM.APrimeFirstCellQVSharpJ

open Filter Gauss APrimeFirstCellJGCap
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

noncomputable def farTwo (N : ℕ) (u S : ℝ) : ℝ :=
  2 * (etaT 0 u)⁻¹ *
    Lemma57.cFar2 (d.W N : ℝ) (B.ell N u) *
      (4 ^ (2 : ℕ) * (((d.W N : ℝ) * B.ell N u * etaT 0 u) * (2 * √S)))

noncomputable def farThree (N : ℕ) (u : ℝ) : ℝ :=
  2 * (etaT 0 u)⁻¹ * 72 * 4 ^ (3 : ℕ) *
    (((d.W N : ℝ) * B.ell N u * etaT 0 u)⁻¹)

noncomputable def farLeak (N : ℕ) (_u : ℝ) : ℝ :=
  4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-(60 : ℝ)) * 4 ^ (3 : ℕ)

noncomputable def endpointKernel (N : ℕ) (u : ℝ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  (((1 - u) / (1 - (1 / 2 : ℝ))) ^ 2 *
      Step2.xiK (d.L N) (d.W N : ℝ) (mE 0).im *
      Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1)))

noncomputable def nearKernel (N : ℕ) (u : ℝ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  endpointKernel N u a *
    (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
        6 * ellStar (d.W N : ℝ) (B.ell N (1 / 2)) then 1 else 0)

noncomputable def leakKernel (N : ℕ) (u : ℝ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  256 * Real.exp 3 * ((1 - u) / (1 - (1 / 2 : ℝ))) ^ 2 *
    (d.W N : ℝ) ^ (-(60 : ℝ)) *
    Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1))

noncomputable def sharpRootProfile (N : ℕ) (u ellSource S : ℝ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  √(APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹) * nearKernel N u a +
  √(APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
      2 * (d.W N : ℝ)⁻¹) * leakKernel N u a +
  √(farTwo N u S) * endpointKernel N u a +
  √(farThree N u) * endpointKernel N u a +
  √(farLeak N u) * endpointKernel N u a

private theorem sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  have hxy : 0 ≤ √x * √y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt (add_nonneg hx hy), Real.sqrt_nonneg x,
    Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y)]

private theorem diagFarRate_le_two (N : ℕ) (u J S : ℝ)
    (hW : 1 ≤ (d.W N : ℝ)) (hℓ : 0 < B.ell N u)
    (hη : 0 < etaT 0 u) (_hS : 0 ≤ S)
    (hJ0 : 0 ≤ J) (hJ : J ≤ 2) :
    APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 J S ≤
      farTwo N u S + farThree N u + farLeak N u := by
  have hc : 0 ≤ Lemma57.cFar2 (d.W N : ℝ) (B.ell N u) :=
    Lemma57.cFar2_nonneg hW hℓ
  have hJ2 : (2 * J) ^ (2 : ℕ) ≤ 4 ^ (2 : ℕ) := by gcongr; linarith
  have hJ3 : (2 * J) ^ (3 : ℕ) ≤ 4 ^ (3 : ℕ) := by gcongr; linarith
  calc
    _ ≤ APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 2 S := by
      unfold APrimeQVEndpoint.diagFarRate
      gcongr
    _ = farTwo N u S + farThree N u + farLeak N u := by
      unfold APrimeQVEndpoint.diagFarRate farTwo farThree farLeak
      norm_num
      ring

/-- The exact T373 profile, with the actual block observable capped by two,
splits into five nonnegative rows. The length-four source `S` stays explicit. -/
theorem rootProfile_le_sharp (N : ℕ) (u ellSource J S : ℝ)
    (a : LoopArg (d.L N) 2)
    (hW : 1 ≤ (d.W N : ℝ)) (hℓ : 0 < B.ell N u)
    (hη : 0 < etaT 0 u) (hell : 0 < ellSource)
    (hS : 0 ≤ S) (hJ0 : 0 ≤ J) (hJ : J ≤ 2) :
    APrimeFullQV.rootProfile B 0 N u (1 / 2) 60 ellSource J S
        ((d.W N : ℝ)⁻¹) a ≤ sharpRootProfile N u ellSource S a := by
  let An : ℝ := APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT 0 u) +
    2 * (d.W N : ℝ)⁻¹
  let Af : ℝ := APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 J S
  let K : ℝ := endpointKernel N u a
  let Kn : ℝ := nearKernel N u a
  let Kl : ℝ := leakKernel N u a
  have hc : 0 ≤ Lemma57.cNear2 (d.W N : ℝ) (B.ell N u) :=
    Lemma57.cNear2_nonneg hW hℓ
  have hAn : 0 ≤ An := by dsimp [An, APrimeQVEndpoint.diagNearRate]; positivity
  have hF2 : 0 ≤ farTwo N u S := by
    dsimp [farTwo]
    have hcf := Lemma57.cFar2_nonneg hW hℓ
    positivity
  have hF3 : 0 ≤ farThree N u := by dsimp [farThree]; positivity
  have hFL : 0 ≤ farLeak N u := by dsimp [farLeak]; positivity
  have hK : 0 ≤ K := by
    dsimp [K, endpointKernel, Step2.tT]
    have ht : 0 ≤ tailT (d.W N : ℝ) (B.ell N (1 / 2))
        (etaT 0 (1 / 2)) 60 (zdist (d.L N) (a 0 - a 1)) :=
      tailT_nonneg (by linarith : (0 : ℝ) ≤ (d.W N : ℝ)) _
    have hxi := Step2.xiK_nonneg (d.L N) (d.W N : ℝ) (mE 0).im
    positivity
  have hAf : Af ≤ farTwo N u S + farThree N u + farLeak N u :=
    diagFarRate_le_two N u J S hW hℓ hη hS hJ0 hJ
  have hsplit : √Af ≤ √(farTwo N u S) + √(farThree N u) + √(farLeak N u) := by
    calc
      √Af ≤ √(farTwo N u S + farThree N u + farLeak N u) :=
        Real.sqrt_le_sqrt hAf
      _ ≤ √(farTwo N u S + farThree N u) + √(farLeak N u) :=
        sqrt_add_le _ _ (add_nonneg hF2 hF3) hFL
      _ ≤ √(farTwo N u S) + √(farThree N u) + √(farLeak N u) := by
        gcongr
        exact sqrt_add_le _ _ hF2 hF3
  change √An * (Kn + Kl) + √Af * K ≤
    √An * Kn + √An * Kl + √(farTwo N u S) * K +
      √(farThree N u) * K + √(farLeak N u) * K
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hsplit)]

/-- At `s=0`, `v=1/2`, the fixed endpoint denominator is exactly `16 T_v(a)`. -/
theorem driftScale_eq_sixteen (N : ℕ) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2) =
      16 * Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1)) := by
  rw [APrimeDriftTimeFamily.driftScale, Step2.etaT_ratio (by norm_num : |(0 : ℝ)| < 2)]
  norm_num
  ring

/-- Literal full evolved QV on the first positive subcell, after replacing
the actual block parameter by the same-event cap `J≤2`. -/
theorem qvAt_le_sharp (N : ℕ) (ω : Gauss.Ω d)
    (a : LoopArg (d.L N) 2) (ellSource S : ℝ)
    (hu0 : 0 ≤ firstTime N) (huv : firstTime N ≤ 1 / 2)
    (hsource : APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (firstTime N) ω
      ellSource S) (hell : 0 < ellSource) (hS : 0 ≤ S)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * (60 : ℝ)) ^ 2 ≤ Real.log (d.W N : ℝ))
    (hN : 2 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT 0 (firstTime N))
    (hAu : 1 ≤ (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N))
    (hAN : (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N) ≤ N)
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2)
    (hJ : APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
      (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤ 2) :
    APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2)
      (firstTime N) ω ≤
    (((16 * Step2.tT B 0 N 60 (1 / 2)
      (zdist (d.L N) (a 0 - a 1)))⁻¹) *
      sharpRootProfile N (firstTime N) ellSource S a) ^ 2 := by
  have hW1 : 1 ≤ (d.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hW
  have hη : 0 < etaT 0 (firstTime N) :=
    Step2.etaT_pos' (by norm_num) (huv.trans_lt (by norm_num))
  have hℓ : 0 < B.ell N (firstTime N) := by
    have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
    have hh := one_le_ellHat_of_nonneg hL hu0 (huv.trans_lt (by norm_num))
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) ((firstTime N : ℝ) : ℂ) by linarith)
  let J := APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
      (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60
  have hJ0 : 0 ≤ J :=
    (APrimeJG.one_le_jG (Gauss.sample d) 0 N (firstTime N) ω
      (show 0 < (B.W N : ℝ) by change 0 < (d.W N : ℝ); linarith)).trans' (by norm_num)
  have hJcap : J ≤ (N : ℝ) := hJ.trans (by linarith)
  have hraw := APrimeFullQV.qvAt_full_absorbed d
    (E := 0) (D := 60) (s := 0) (u := firstTime N) (v := 1 / 2)
    (by norm_num) hu0 hu0 huv (by norm_num)
    N ω a hsource hell (by norm_num) hW hlog4 hlog
    (by linarith : 1 ≤ (N : ℝ)) heta hAu hAN hWL hNW hJcap
  have hprof := rootProfile_le_sharp N (firstTime N) ellSource J S a
    hW1 hℓ hη hell hS hJ0 hJ
  have hscale : 0 ≤ (APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2))⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d
      (by norm_num) (by norm_num) (by norm_num) N a)).le
  have hAn : 0 ≤ APrimeQVEndpoint.diagNearRate B N (B.ell N (firstTime N))
      ellSource (etaT 0 (firstTime N)) + 2 * (d.W N : ℝ)⁻¹ := by
    unfold APrimeQVEndpoint.diagNearRate
    have hc := Lemma57.cNear2_nonneg hW1 hℓ
    positivity
  have hAf : 0 ≤ APrimeQVEndpoint.diagFarRate B N (B.ell N (firstTime N))
      (etaT 0 (firstTime N)) 60 J S := by
    unfold APrimeQVEndpoint.diagFarRate
    have hc := Lemma57.cFar2_nonneg hW1 hℓ
    positivity
  have hT : 0 ≤ Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1)) := by
    dsimp [Step2.tT]
    exact tailT_nonneg (by linarith : 0 ≤ (d.W N : ℝ)) _
  have hxi := Step2.xiK_nonneg (d.L N) (d.W N : ℝ) (mE 0).im
  have hroot0 : 0 ≤ APrimeFullQV.rootProfile B 0 N (firstTime N) (1 / 2)
      60 ellSource J S ((d.W N : ℝ)⁻¹) a := by
    unfold APrimeFullQV.rootProfile
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hprof hscale
  have hsq := pow_le_pow_left₀ (mul_nonneg hscale hroot0) hscaled 2
  rw [driftScale_eq_sixteen] at hraw hsq
  exact hraw.trans hsq

/-- One positive-time Gaussian sample simultaneously has the T348 source,
the active smooth weight, the T385 sharp block cap and the five-row full QV
bound. The explicit `sourceEll ζ N` and `sourceC4 ζ N` preserve the `N^ζ`
source factors. -/
theorem exists_positive_firstTime_sharp_qv :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Gauss.Ω d,
        ‖Xmat d N ω‖ ≤ (N : ℝ) ∧
        0 < firstTime N ∧
        firstTime N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) ∧
        0 < sourceEll ζ N ∧ sourceEll ζ N < 1 ∧
        0 < sourceC4 ζ N ∧
        (∀ p : ℕ, APrimeSmoothWeightActual.weight d 0 60 δ
          (firstCellS τ') (firstCellT τ')
          (fun M => (max 1 M : ℝ) ^ (248 : ℕ)) 2 p N 2 N ω = 1) ∧
        APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (firstTime N) ω
          (sourceEll ζ N) (sourceC4 ζ N) ∧
        APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
          (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤ 2 ∧
        ∀ a : LoopArg (d.L N) 2,
          0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2) ∧
          APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2) =
            16 * Step2.tT B 0 N 60 (1 / 2) (zdist (d.L N) (a 0 - a 1)) ∧
          APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0 (1 / 2)
            (firstTime N) ω ≤
          (((16 * Step2.tT B 0 N 60 (1 / 2)
            (zdist (d.L N) (a 0 - a 1)))⁻¹) *
            sharpRootProfile N (firstTime N) (sourceEll ζ N)
              (sourceC4 ζ N) a) ^ 2 := by
  obtain ⟨τ', hτ', hw⟩ :=
    APrimeFirstCellJGCap.exists_positive_time_firstCell_jG_two_witness
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ δ hδ
  filter_upwards [hw ζ hζ δ hδ,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    eventually_ge_atTop 2] with N hwN hsc hN2
  obtain ⟨ω, hnorm, hpos, hmem, hellLt, hweight, hsource, _hJsharp, hJtwo⟩ := hwN
  obtain ⟨hW, hlog4, hlog, _hN, heta, hAu, hAN, hWL, hNW⟩ := hsc
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hell : 0 < sourceEll ζ N := by
    unfold sourceEll
    have hNpos : (0 : ℝ) < N := by linarith
    exact Real.rpow_pos_of_pos (by positivity) _
  have huv : firstTime N ≤ 1 / 2 := by
    have ht : firstCellT τ' N ≤ 1 / 2 := by
      change gridT (B.W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
      exact gridT_le (1 / 2 : ℝ) 1
    exact hmem.2.trans ht
  have hℓ : 0 < B.ell N (firstTime N) := by
    have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
    have hh := one_le_ellHat_of_nonneg hL (le_of_lt hpos)
      (huv.trans_lt (by norm_num))
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) ((firstTime N : ℝ) : ℂ) by linarith)
  have hscale : 0 < B.scale 0 N (firstTime N) :=
    B.scale_pos' (by norm_num) N (le_of_lt hpos) (huv.trans_lt (by norm_num))
  have hS : 0 < sourceC4 ζ N := by
    unfold sourceC4
    have hNpos : (0 : ℝ) < N := by linarith
    positivity
  refine ⟨ω, hnorm, hpos, hmem, hell, hellLt, hS, hweight,
    hsource, hJtwo, ?_⟩
  intro a
  refine ⟨APrimeDriftTimeFamily.driftScale_pos d (D := 60)
    (by norm_num) (by norm_num) (by norm_num) N a,
    driftScale_eq_sixteen N a, ?_⟩
  exact qvAt_le_sharp N ω a (sourceEll ζ N) (sourceC4 ζ N)
    (le_of_lt hpos) huv hsource hell (le_of_lt hS)
    hW hlog4 hlog hNr heta hAu hAN hWL hNW hJtwo

#print axioms rootProfile_le_sharp
#print axioms driftScale_eq_sixteen
#print axioms qvAt_le_sharp
#print axioms exists_positive_firstTime_sharp_qv

end RBM.APrimeFirstCellQVSharpJ

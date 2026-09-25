/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossNearGridSharp
import RBM1D.Gauss.APrimeGeneralMovingLoopModulusGeneralDims

/-!
# Continuous-time sharp near bound at fixed `D = 60`

The endpoint-grid estimate and the actual normalized-loop modulus give the continuous-time
near-field estimate for the `exampleGrow` Gaussian model. The interpolation is on the
intersection of the endpoint-grid event and the spectral-norm event.
-/

namespace RBM.APrimeFreeLossNearContinuousSharp

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option maxRecDepth 4096

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60

private theorem target_mesh_ge_N {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ≤ mesh N := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNne : N ≠ 0 := by omega
  have hmesh : mesh N = (N : ℝ) ^ (258 : ℝ) := by
    simp [mesh, APrimeGeneralMovingMesh.targetMesh,
      APrimeGeneralMovingMesh.polynomialMesh, hNne]
    norm_num
  rw [hmesh]
  calc
    (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ ≤ (N : ℝ) ^ (258 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)

set_option maxHeartbeats 1000000 in
/-- A left endpoint of the fixed target mesh covers every point of the moving interval,
including its initial point and the terminal partial cell. -/
private theorem left_mesh_endpoint
    {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) :
    ∃ k ≤ cutNetTop s t mesh N,
      APrimeFreeLossNearGridSharp.gridEndpoint s t N k ∈ Icc (s N) (t N) ∧
        APrimeFreeLossNearGridSharp.gridEndpoint s t N k ≤ u ∧
          u - APrimeFreeLossNearGridSharp.gridEndpoint s t N k ≤ 1 / mesh N := by
  have hm : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  let x := (u - s N) * mesh N
  let k := ⌊x⌋₊
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (sub_nonneg.mpr hu.1) hm.le
  have hkx : (k : ℝ) ≤ x := by
    dsimp [k]
    exact Nat.floor_le hx0
  have hxtop : x ≤ (t N - s N) * mesh N := by
    dsimp [x]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right hu.2 _) hm.le
  have hktop : k ≤ cutNetTop s t mesh N := by
    dsimp [CutHypTheta.cutNetTop]
    exact Nat.le_floor (hkx.trans hxtop)
  have hxstrict : x < (k : ℝ) + 1 := by
    dsimp [x, k]
    exact Nat.lt_floor_add_one _
  let v := APrimeFreeLossNearGridSharp.gridEndpoint s t N k
  have hv : v = s N + (k : ℝ) / mesh N := by
    simp [v, APrimeFreeLossNearGridSharp.gridEndpoint,
      APrimeFreeLossCoordinateBridge.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      CutHypTheta.cutNetPt, mesh]
  have hdiv : (k : ℝ) / mesh N ≤ u - s N :=
    (div_le_iff₀ hm).2 (by simpa [x] using hkx)
  have hvle : v ≤ u := by rw [hv]; linarith
  have hvge : s N ≤ v := by
    rw [hv]
    exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hm.le)
  have hgapEq : u - v = (x - (k : ℝ)) / mesh N := by
    rw [hv]
    dsimp [x]
    field_simp [hm.ne']
    ring
  have hgapNum : x - (k : ℝ) < 1 := by linarith
  have hgap : u - v < 1 / mesh N := by
    rw [hgapEq]
    exact (div_lt_iff₀ hm).2 (by simpa [hm.ne'] using hgapNum)
  refine ⟨k, hktop, ?_, ?_, ?_⟩
  · change v ∈ Icc (s N) (t N)
    exact ⟨hvge, hvle.trans hu.2⟩
  · change v ≤ u
    exact hvle
  · change u - v ≤ 1 / mesh N
    exact hgap.le

set_option maxHeartbeats 1000000 in
/-- Interpolate one actual two-loop error from the endpoint grid. -/
private theorem continuous_pointwise_of_grid_good
    {E τ : ℝ} {s t : ℕ → ℝ} {N : ℕ}
    (hE : |E| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hτ : 0 < τ)
    (hN : 1 ≤ N) (hfloor : (N : ℝ)⁻¹ ≤ 1 - t N)
    (hmeshN : (N : ℝ) ≤ mesh N)
    (hmod : ∀ ω ∈ APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N,
      ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
        |Step2Moment.jSnorm (Gauss.sample d) E 60 s N v ω -
            Step2Moment.jSnorm (Gauss.sample d) E 60 s N w ω| ≤
          (N : ℝ) ^ (2 * (60 : ℝ) + 7) * |v - w| ^ ((1 : ℝ) / 2))
    (ω : Ω d) (hωnorm : ω ∈ APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N)
    (hωgrid : ∀ q : APrimeFreeLossNearGridSharp.GridIndex s t N,
      APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω ≤
        (N : ℝ) ^ (τ / 2) * APrimeFreeLossNearGridSharp.gridNearScale E s t N q)
    (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) :
    (Gauss.sample d).lkErr E N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2) ≤
      21 * (N : ℝ) ^ (τ / 2) * (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
        tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
          (etaT E (p.1 : ℝ)) 60
          (zdist (d.L N) (p.2.1 - p.2.2)) := by
  let u : ℝ := p.1
  have hu : u ∈ Icc (s N) (t N) := p.1.property
  obtain ⟨k, hkTop, hvI, hvu, hgap⟩ := left_mesh_endpoint hu
  let v := APrimeFreeLossNearGridSharp.gridEndpoint s t N k
  have hm : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  let Ru := Step2Moment.ratR E s N u
  let Rv := Step2Moment.ratR E s N v
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hv1 : v < 1 := lt_of_le_of_lt hvI.2 (ht1 N)
  have hRu1 : 1 ≤ Ru := Step2Moment.one_le_ratR hE hu.1 hu1
  have hRv1 : 1 ≤ Rv := Step2Moment.one_le_ratR hE hvI.1 hv1
  have hRuPos : 0 < Ru := lt_of_lt_of_le (by norm_num) hRu1
  have hRvPos : 0 < Rv := lt_of_lt_of_le (by norm_num) hRv1
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hIm : (mE E).im ≠ 0 := (mE_im_pos hE).ne'
  have hRuForm : Ru = (1 - s N) / (1 - u) := by
    dsimp [Ru, Step2Moment.ratR, etaT]
    field_simp [hIm, h1u.ne']
  have hRvForm : Rv = (1 - s N) / (1 - v) := by
    dsimp [Rv, Step2Moment.ratR, etaT]
    field_simp [hIm, h1v.ne']
  have hfloorU : (N : ℝ)⁻¹ ≤ 1 - u :=
    hfloor.trans (by linarith [hu.2])
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdenN : 1 ≤ (N : ℝ) * (1 - u) := by
    have hmul := mul_le_mul_of_nonneg_left hfloorU (le_of_lt hNpos)
    have hcancel : (N : ℝ) * (N : ℝ)⁻¹ = 1 := by
      field_simp [hNpos.ne']
    rw [hcancel] at hmul
    exact hmul
  have hRuN : Ru ≤ (N : ℝ) := by
    rw [hRuForm]
    apply (div_le_iff₀ h1u).2
    nlinarith [hs0 N, hdenN]
  have hInvMesh : 1 / mesh N ≤ 1 / (N : ℝ) := by
    apply (div_le_div_iff₀ hm hNpos).2
    nlinarith [hmeshN]
  have hInvMesh' : 1 / mesh N ≤ (N : ℝ)⁻¹ := by
    simpa [one_div] using hInvMesh
  have hgaple : u - v ≤ 1 / mesh N := hgap
  have h1vsmall : 1 - v ≤ 2 * (1 - u) := by
    have hmeshU : 1 / mesh N ≤ 1 - u := by
      calc
        1 / mesh N ≤ (N : ℝ)⁻¹ := hInvMesh'
        _ ≤ 1 - u := hfloorU
    have hsum : 1 - v ≤ (1 - u) + 1 / mesh N := by
      dsimp [u]
      linarith [hgaple]
    linarith [hsum, hmeshU]
  have hRratio : Ru / Rv = (1 - v) / (1 - u) := by
    rw [hRuForm, hRvForm]
    have h1s : 0 < 1 - s N := by linarith [hst N, ht1 N]
    field_simp [h1s.ne', h1u.ne', h1v.ne']
  have hRuRv : Ru ≤ 2 * Rv := by
    apply (div_le_iff₀ hRvPos).1
    rw [hRratio]
    exact (div_le_iff₀ h1u).2 h1vsmall
  have hRcmp2 : Ru ^ 2 ≤ 4 * Rv ^ 2 := by nlinarith [hRuRv, hRuPos, hRvPos]
  have hRcmp4 : Ru ^ 4 ≤ 16 * Rv ^ 4 := by
    calc
      Ru ^ 4 ≤ (2 * Rv) ^ 4 := by gcongr
      _ = 16 * Rv ^ 4 := by ring

  have hWpos : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hsup : (Finset.univ : Finset (LoopArg (d.L N) 2)).sup'
      Finset.univ_nonempty
      (fun a => ‖Step2.lk (Gauss.sample d) E N v ω a‖ /
        tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
          (zdist (d.L N) (a 0 - a 1))) ≤
        (N : ℝ) ^ (τ / 2) * Rv ^ 2 := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro a ha
    let q : APrimeFreeLossNearGridSharp.GridIndex s t N :=
      (⟨k, Nat.lt_succ_of_le hkTop⟩, a)
    have hq := hωgrid q
    have herr : APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω =
        ‖Step2.lk (Gauss.sample d) E N v ω a‖ := by
      change (Gauss.sample d).lkErr E N
          (APrimeFreeLossNearGridSharp.gridEndpoint s t N k) ω
          (pmLoop (a 0) (a 1)) = _
      exact (Step2.norm_lk_eq (Gauss.sample d) E N v ω a).symm
    have hscale : APrimeFreeLossNearGridSharp.gridNearScale E s t N q =
        Rv ^ 2 * tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
          (zdist (d.L N) (a 0 - a 1)) := by
      change Step2Moment.ratR E s N v ^ 2 *
        tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
          (zdist (d.L N) (a 0 - a 1)) = _
      dsimp [Rv]
    have hTpos : 0 < tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
        (zdist (d.L N) (a 0 - a 1)) := tailT_pos hWpos _
    have hraw : ‖Step2.lk (Gauss.sample d) E N v ω a‖ ≤
        ((N : ℝ) ^ (τ / 2) * Rv ^ 2) *
          tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
            (zdist (d.L N) (a 0 - a 1)) := by
      calc
        ‖Step2.lk (Gauss.sample d) E N v ω a‖ =
            APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω := herr.symm
        _ ≤ (N : ℝ) ^ (τ / 2) *
              APrimeFreeLossNearGridSharp.gridNearScale E s t N q := hq
        _ = (N : ℝ) ^ (τ / 2) *
            (Rv ^ 2 * tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
              (zdist (d.L N) (a 0 - a 1))) := by rw [hscale]
        _ = ((N : ℝ) ^ (τ / 2) * Rv ^ 2) *
            tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
              (zdist (d.L N) (a 0 - a 1)) := by ring
    exact (div_le_iff₀ hTpos).2 hraw

  have hjSv : Step2.jS (Gauss.sample d) E 60 N v ω ≤
      (N : ℝ) ^ (τ / 2) * Rv ^ 2 + 1 := by
    change (Finset.univ : Finset (LoopArg (d.L N) 2)).sup'
        Finset.univ_nonempty (fun a =>
          ‖Step2.lk (Gauss.sample d) E N v ω a‖ /
            tailT (d.W N : ℝ) ((band d).ell N v) (etaT E v) 60
              (zdist (d.L N) (a 0 - a 1))) + 1 ≤
      (N : ℝ) ^ (τ / 2) * Rv ^ 2 + 1
    linarith [hsup]
  have hjSnormV : Step2Moment.jSnorm (Gauss.sample d) E 60 s N v ω ≤
      1 / Rv ^ 4 + (N : ℝ) ^ (τ / 2) / Rv ^ 2 := by
    rw [Step2Moment.jSnorm]
    calc
      Step2.jS (Gauss.sample d) E 60 N v ω / Rv ^ 4 ≤
          ((N : ℝ) ^ (τ / 2) * Rv ^ 2 + 1) / Rv ^ 4 :=
            div_le_div_of_nonneg_right hjSv (by positivity)
      _ = 1 / Rv ^ 4 + (N : ℝ) ^ (τ / 2) / Rv ^ 2 := by
        field_simp [hRvPos.ne']
        ring
        

  have hFine :=
    APrimeGeneralMovingLoopModulusGeneralDims.target_mesh_fine_eq_inv_sq
      (D := (60 : ℝ)) hN
  have hdist : |u - v| ≤ 1 / mesh N := by
    rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hgap
  have hdistPow : |u - v| ^ ((1 : ℝ) / 2) ≤
      (1 / mesh N) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (abs_nonneg _) hdist (by norm_num)
  have hmoduv := hmod ω hωnorm u hu v hvI
  have hjSnormU : Step2Moment.jSnorm (Gauss.sample d) E 60 s N u ω ≤
      Step2Moment.jSnorm (Gauss.sample d) E 60 s N v ω + (N : ℝ) ^ (-2 : ℝ) := by
    have hcost : (N : ℝ) ^ (2 * (60 : ℝ) + 7) * |u - v| ^ ((1 : ℝ) / 2) ≤
        (N : ℝ) ^ (-2 : ℝ) := by
      calc
        (N : ℝ) ^ (2 * (60 : ℝ) + 7) * |u - v| ^ ((1 : ℝ) / 2) ≤
            (N : ℝ) ^ (2 * (60 : ℝ) + 7) * (1 / mesh N) ^ ((1 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left hdistPow (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ (-2 : ℝ) := by
          simpa [mesh, show 2 * (60 : ℝ) + 7 = 127 by norm_num] using hFine
    rcases abs_sub_le_iff.mp hmoduv with ⟨hforward, _⟩
    nlinarith [hforward, hcost]

  have hRpow2 : Ru ^ 2 ≤ 4 * Rv ^ 2 := hRcmp2
  have hInvSq : 1 / Rv ^ 2 ≤ 4 / Ru ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < Rv ^ 2)
      (by positivity : 0 < Ru ^ 2)).2
    nlinarith [hRpow2, hRuPos, hRvPos]
  have hInvFourth : 1 / Rv ^ 4 ≤ 16 / Ru ^ 4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < Rv ^ 4)
      (by positivity : 0 < Ru ^ 4)).2
    nlinarith [hRcmp4, hRuPos, hRvPos]
  have hRuSq : 1 / Ru ^ 4 ≤ 1 / Ru ^ 2 := by
    have hRuSqOne : 1 ≤ Ru ^ 2 := by
      nlinarith [sq_nonneg (Ru - 1)]
    have hInvR2 : 1 / Ru ^ 2 ≤ 1 := (div_le_one₀ (by positivity)).2 hRuSqOne
    calc
      1 / Ru ^ 4 = (1 / Ru ^ 2) * (1 / Ru ^ 2) := by
        field_simp [hRuPos.ne']
      _ ≤ (1 / Ru ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hInvR2 (by positivity)
      _ = 1 / Ru ^ 2 := by ring
  have hNInvSq : (N : ℝ) ^ (-2 : ℝ) ≤ 1 / Ru ^ 2 := by
    have hpowN : (N : ℝ) ^ (-2 : ℝ) = 1 / (N : ℝ) ^ 2 := by
      rw [Real.rpow_neg hNpos.le]
      simp [one_div]
    rw [hpowN]
    apply (div_le_div_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)
      (by positivity : 0 < Ru ^ 2)).2
    have hprod := mul_nonneg (sub_nonneg.mpr hRuN)
      (add_nonneg hNpos.le hRuPos.le)
    nlinarith
  have hNgOne : 1 ≤ (N : ℝ) ^ (τ / 2) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by linarith [hτ])
  have hjsnormBound : Step2Moment.jSnorm (Gauss.sample d) E 60 s N u ω ≤
      21 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by
    calc
      Step2Moment.jSnorm (Gauss.sample d) E 60 s N u ω ≤
          Step2Moment.jSnorm (Gauss.sample d) E 60 s N v ω +
            (N : ℝ) ^ (-2 : ℝ) := hjSnormU
      _ ≤ 1 / Rv ^ 4 + (N : ℝ) ^ (τ / 2) / Rv ^ 2 +
            (N : ℝ) ^ (-2 : ℝ) := by linarith [hjSnormV]
      _ ≤ 16 / Ru ^ 4 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 +
            1 / Ru ^ 2 := by
        have hg0 : 0 ≤ (N : ℝ) ^ (τ / 2) :=
          Real.rpow_nonneg (by positivity) _
        have hg1 : (N : ℝ) ^ (τ / 2) / Rv ^ 2 ≤
            4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by
          calc
            (N : ℝ) ^ (τ / 2) / Rv ^ 2 =
                (N : ℝ) ^ (τ / 2) * (1 / Rv ^ 2) := by ring
            _ ≤ (N : ℝ) ^ (τ / 2) * (4 / Ru ^ 2) :=
              mul_le_mul_of_nonneg_left hInvSq hg0
            _ = 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by ring
        exact add_le_add (add_le_add hInvFourth hg1) hNInvSq
      _ ≤ 17 / Ru ^ 2 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by
        have h16 : 16 / Ru ^ 4 ≤ 16 / Ru ^ 2 := by
          calc
            16 / Ru ^ 4 = 16 * (1 / Ru ^ 4) := by ring
            _ ≤ 16 * (1 / Ru ^ 2) :=
              mul_le_mul_of_nonneg_left hRuSq (by norm_num)
            _ = 16 / Ru ^ 2 := by ring
        calc
          16 / Ru ^ 4 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 + 1 / Ru ^ 2
              ≤ 16 / Ru ^ 2 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 + 1 / Ru ^ 2 := by
                gcongr
          _ = 16 / Ru ^ 2 + 1 / Ru ^ 2 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by ring
          _ ≤ 17 / Ru ^ 2 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by
                ring_nf
                rfl
      _ ≤ 21 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by
        have hcoeff : 17 + 4 * (N : ℝ) ^ (τ / 2) ≤
            21 * (N : ℝ) ^ (τ / 2) := by nlinarith [hNgOne]
        calc
          17 / Ru ^ 2 + 4 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 =
              (17 + 4 * (N : ℝ) ^ (τ / 2)) / Ru ^ 2 := by ring
          _ ≤ 21 * (N : ℝ) ^ (τ / 2) / Ru ^ 2 := by
            apply (div_le_div_iff₀ (by positivity : 0 < Ru ^ 2)
              (by positivity : 0 < Ru ^ 2)).2
            exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

  have hdenorm : Step2.jS (Gauss.sample d) E 60 N u ω =
      Step2Moment.jSnorm (Gauss.sample d) E 60 s N u ω * Ru ^ 4 := by
    change Step2.jS (Gauss.sample d) E 60 N u ω =
      (Step2.jS (Gauss.sample d) E 60 N u ω / Ru ^ 4) * Ru ^ 4
    field_simp [hRuPos.ne']
  have hjSu : Step2.jS (Gauss.sample d) E 60 N u ω ≤
      21 * (N : ℝ) ^ (τ / 2) * Ru ^ 2 := by
    rw [hdenorm]
    calc
      Step2Moment.jSnorm (Gauss.sample d) E 60 s N u ω * Ru ^ 4 ≤
          (21 * (N : ℝ) ^ (τ / 2) / Ru ^ 2) * Ru ^ 4 :=
            mul_le_mul_of_nonneg_right hjsnormBound (by positivity)
      _ = 21 * (N : ℝ) ^ (τ / 2) * Ru ^ 2 := by
        field_simp [hRuPos.ne']

  let a : LoopArg (B.L N) 2 := fun i => if i.val = 0 then p.2.1 else p.2.2
  have ha0 : a 0 = p.2.1 := by simp [a]
  have ha1 : a 1 = p.2.2 := by simp [a]
  have hTailU : 0 < tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
      (zdist (d.L N) (a 0 - a 1)) := tailT_pos hWpos _
  have hpointSup : ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
      tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
        (zdist (d.L N) (a 0 - a 1)) ≤ Step2.jS (Gauss.sample d) E 60 N u ω := by
    change ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
        tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
          (zdist (B.L N) (a 0 - a 1)) ≤
      (Finset.univ : Finset (LoopArg (B.L N) 2)).sup'
        Finset.univ_nonempty (fun b : LoopArg (B.L N) 2 =>
          ‖Step2.lk (Gauss.sample d) E N u ω b‖ /
            tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
              (zdist (B.L N) (b 0 - b 1))) + 1
    exact (Finset.le_sup' (fun b : LoopArg (B.L N) 2 =>
      ‖Step2.lk (Gauss.sample d) E N u ω b‖ /
        tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
          (zdist (B.L N) (b 0 - b 1))) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_right (by positivity))
  have hpointRaw : ‖Step2.lk (Gauss.sample d) E N u ω a‖ ≤
      Step2.jS (Gauss.sample d) E 60 N u ω *
        tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
          (zdist (d.L N) (a 0 - a 1)) :=
    (div_le_iff₀ hTailU).1 hpointSup
  have hraw : ‖Step2.lk (Gauss.sample d) E N u ω a‖ ≤
      21 * (N : ℝ) ^ (τ / 2) * Ru ^ 2 *
        tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) 60
          (zdist (d.L N) (a 0 - a 1)) := by
    exact hpointRaw.trans (by gcongr)
  have hnormErr : ‖Step2.lk (Gauss.sample d) E N u ω a‖ =
      (Gauss.sample d).lkErr E N u ω (pmLoop p.2.1 p.2.2) := by
    simpa [ha0, ha1] using (Step2.norm_lk_eq (Gauss.sample d) E N u ω a)
  rw [hnormErr] at hraw
  exact hraw

set_option maxHeartbeats 1000000 in
/-- The actual `exampleGrow` continuous-time sharp near estimate at the paper's fixed `D=60`.
The endpoint-grid loss is reduced before interpolation and absorbed into the requested loss. -/
theorem continuous_lkErr_stochDom
    {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    StochDom (Gauss.P d)
      (fun N (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
        (Gauss.sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) _ =>
        (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
          tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
            (etaT E (p.1 : ℝ)) 60
            (zdist (d.L N) (p.2.1 - p.2.2))) := by
  let hgrid := APrimeFreeLossNearGridSharp.endpoint_grid_lkErr_stochDom
    (E := E) (c := c) (s := s) (t := t) hE hs0 hst ht1 hc hreg hB
  have hnormHP : HighProb (Gauss.P d)
      (APrimeGeneralMovingLoopModulusGeneralDims.normEvent d) := by
    change HighProb (Gauss.P d)
      (fun N => {ω | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)})
    exact Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)
  have hregPaper : Cond272 (band d) E s t := hreg.toCond272
  have hmod := APrimeGeneralMovingLoopModulusGeneralDims.eventually_jSnorm_modulus
    (d := d) (E := E) (D := (60 : ℝ)) hE (by norm_num) hs0 hst ht1 hregPaper
  have hfloor := APrimeGeneralMovingLoopModulusGeneralDims.eventually_endpoint_floor
    d hE hs0 hst ht1 hregPaper
  intro τ hτ D hD
  let τg := τ / 2
  have hτg : 0 < τg := by dsimp [τg]; linarith
  have hgridHP : HighProb (Gauss.P d)
      (fun N => {ω | ∀ q : APrimeFreeLossNearGridSharp.GridIndex s t N,
        APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω ≤
          (N : ℝ) ^ τg * APrimeFreeLossNearGridSharp.gridNearScale E s t N q}) :=
    StochDom.highProb hgrid hτg
  have hboth := HighProb.inter hgridHP hnormHP
  have hprob := hboth D hD
  have hconst : ∀ᶠ N : ℕ in atTop, 21 ≤ (N : ℝ) ^ τg :=
    eventually_le_rpow 21 hτg
  filter_upwards [hprob, hmod, hfloor, Filter.eventually_ge_atTop 1, hconst]
    with N hprobN hmodN hfloorN hN hconstN
  have hNcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmeshN := target_mesh_ge_N hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hbad : badSet
      (fun n (p : TimeIcc s t n × (ZMod (d.L n) × ZMod (d.L n))) ω =>
        (Gauss.sample d).lkErr E n p.1 ω (pmLoop p.2.1 p.2.2))
      (fun n (p : TimeIcc s t n × (ZMod (d.L n) × ZMod (d.L n))) _ =>
        (etaT E (s n) / etaT E (p.1 : ℝ)) ^ 2 *
          tailT (d.W n : ℝ) ((band d).ell n (p.1 : ℝ))
            (etaT E (p.1 : ℝ)) 60 (zdist (d.L n) (p.2.1 - p.2.2))) τ N ⊆
      (({ω | ∀ q : APrimeFreeLossNearGridSharp.GridIndex s t N,
        APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω ≤
          (N : ℝ) ^ τg *
            APrimeFreeLossNearGridSharp.gridNearScale E s t N q} ∩
        APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N)ᶜ) := by
    intro ω hω
    change ω ∉ ({ω | ∀ q : APrimeFreeLossNearGridSharp.GridIndex s t N,
      APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω ≤
        (N : ℝ) ^ τg * APrimeFreeLossNearGridSharp.gridNearScale E s t N q} ∩
      APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N)
    intro hgood
    simp only [badSet, Set.mem_ofPred_eq] at hω
    obtain ⟨p, hfail⟩ := hω
    have hpoint := continuous_pointwise_of_grid_good
      (E := E) (τ := τ) hE hs0 hst ht1 hτ hN
      hfloorN.1 hmeshN hmodN ω hgood.2 hgood.1 p
    have hNτ : 21 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
      calc
        21 * (N : ℝ) ^ τg ≤ (N : ℝ) ^ τg * (N : ℝ) ^ τg :=
          mul_le_mul_of_nonneg_right hconstN
            (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ)) _)
        _ = (N : ℝ) ^ τ := by
          rw [← Real.rpow_add hNpos]
          congr 1
          dsimp [τg]
          ring
    have hscaled : (Gauss.sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) ≤
        (N : ℝ) ^ τ * (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
          tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
            (etaT E (p.1 : ℝ)) 60 (zdist (d.L N) (p.2.1 - p.2.2)) := by
      calc
        (Gauss.sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) ≤
            21 * (N : ℝ) ^ τg *
              (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                  (etaT E (p.1 : ℝ)) 60
                  (zdist (d.L N) (p.2.1 - p.2.2)) := by
                    simpa [τg, mul_assoc, mul_left_comm, mul_comm] using hpoint
        _ ≤ (N : ℝ) ^ τ *
              (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                  (etaT E (p.1 : ℝ)) 60
                  (zdist (d.L N) (p.2.1 - p.2.2)) := by
            have hfac : 0 ≤ (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                  (etaT E (p.1 : ℝ)) 60
                  (zdist (d.L N) (p.2.1 - p.2.2)) := by
              have hWpos : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
              exact mul_nonneg (sq_nonneg _) (tailT_pos hWpos _).le
            calc
              21 * (N : ℝ) ^ τg *
                  (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                    tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                      (etaT E (p.1 : ℝ)) 60
                      (zdist (d.L N) (p.2.1 - p.2.2))
                = (21 * (N : ℝ) ^ τg) *
                    ((etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                      tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                        (etaT E (p.1 : ℝ)) 60
                        (zdist (d.L N) (p.2.1 - p.2.2))) := by ring
              _ ≤ (N : ℝ) ^ τ *
                    ((etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                      tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                        (etaT E (p.1 : ℝ)) 60
                        (zdist (d.L N) (p.2.1 - p.2.2))) :=
                  mul_le_mul_of_nonneg_right hNτ hfac
              _ = (N : ℝ) ^ τ *
                    (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
                      tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                        (etaT E (p.1 : ℝ)) 60
                        (zdist (d.L N) (p.2.1 - p.2.2)) := by ring
    have hfail' :
        (N : ℝ) ^ τ *
            ((etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 *
              tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
                (etaT E (p.1 : ℝ)) 60
                (zdist (d.L N) (p.2.1 - p.2.2))) <
          (Gauss.sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) := hfail
    exact (not_lt_of_ge (by simpa [mul_assoc] using hscaled)) hfail'
  calc
    (Gauss.P d) (badSet
        (fun n (p : TimeIcc s t n × (ZMod (d.L n) × ZMod (d.L n))) ω =>
          (Gauss.sample d).lkErr E n p.1 ω (pmLoop p.2.1 p.2.2))
        (fun n (p : TimeIcc s t n × (ZMod (d.L n) × ZMod (d.L n))) _ =>
          (etaT E (s n) / etaT E (p.1 : ℝ)) ^ 2 *
            tailT (d.W n : ℝ) ((band d).ell n (p.1 : ℝ))
              (etaT E (p.1 : ℝ)) 60 (zdist (d.L n) (p.2.1 - p.2.2))) τ N)
      ≤ (Gauss.P d)
          (({ω | ∀ q : APrimeFreeLossNearGridSharp.GridIndex s t N,
          APrimeFreeLossNearGridSharp.gridLKErr E s t N q ω ≤
              (N : ℝ) ^ τg *
                APrimeFreeLossNearGridSharp.gridNearScale E s t N q} ∩
            APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N)ᶜ) :=
              measure_mono hbad
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := hprobN

set_option maxHeartbeats 1000000 in
/-- A fresh same-event witness keeps the accepted positive window and active first cell while
adding both the endpoint-grid and actual norm events. The plateau weight is one at `k=1`. -/
theorem exampleGrow_same_event_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ, ∃ lam : ℝ, 0 < lam ∧
      Nonempty (Gauss.APrimeActualWeightHighProbPlateau.PositiveWindowWitness c lam s t) ∧
      StochDom (Gauss.P d)
        (fun N (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
          (Gauss.sample d).lkErr 0 N p.1 ω (pmLoop p.2.1 p.2.2))
        (fun N (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) _ =>
          (etaT 0 (s N) / etaT 0 (p.1 : ℝ)) ^ 2 *
            tailT (d.W N : ℝ) ((band d).ell N (p.1 : ℝ))
              (etaT 0 (p.1 : ℝ)) 60
              (zdist (d.L N) (p.2.1 - p.2.2))) ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ ω ∈ APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
            (lam / 1000) (lam / 1000) (lam / 1000) N,
            ω ∈ Gauss.APrimeActualWeightHighProbPlateau.Good 0 lam s t N ∧
            ω ∈ APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N ∧
            (∀ q : APrimeFreeLossNearGridSharp.GridIndex s t N,
              APrimeFreeLossNearGridSharp.gridLKErr 0 s t N q ω ≤
                (N : ℝ) ^ ((1 : ℝ) / 2) *
                  APrimeFreeLossNearGridSharp.gridNearScale 0 s t N q) ∧
            1 ≤ cutNetTop s t mesh N ∧
            APrimeSmoothWeightActual.weight d 0 60 lam s t mesh 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω = 1 := by
  let lam : ℝ := 1 / 10000
  have hlam : 0 < lam := by norm_num [lam]
  obtain ⟨c, hc, s, t, ⟨W⟩⟩ :=
    Gauss.APrimeActualWeightHighProbPlateau.positive_window_joint_witness hlam
  let hNear := continuous_lkErr_stochDom (E := 0) (c := c) (s := s) (t := t)
    (by norm_num) W.base.hs0 W.base.hst W.base.ht1 W.base.hc
    W.base.hreg W.base.hB
  letI : IsProbabilityMeasure (Gauss.P d) := (band d).isProbabilityMeasure
  have hCommon := APrimeGeneralMovingCommonSources.highProb_commonEvent
    (E := 0) (D := 60) (by norm_num) (by norm_num)
    W.base.hs0 W.base.hst W.base.ht1 W.base.hc
    W.base.hreg W.base.hB (lam / 1000) (lam / 1000) (lam / 1000)
    (by positivity) (by positivity) (by positivity)
  have hGood := Gauss.APrimeActualWeightHighProbPlateau.highProb_Good
    hlam (by norm_num) W.base.hs0 W.base.hst W.base.ht1 W.base.hc
    W.base.hreg W.base.hB
  have hNorm := Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)
  have hGridStoch := APrimeFreeLossNearGridSharp.endpoint_grid_lkErr_stochDom
    (E := 0) (c := c) (s := s) (t := t) (by norm_num)
    W.base.hs0 W.base.hst W.base.ht1 W.base.hc W.base.hreg W.base.hB
  have hGrid := StochDom.highProb hGridStoch (τ := ((1 : ℝ) / 2)) (by norm_num)
  have hTriple := HighProb.inter (HighProb.inter (HighProb.inter hCommon hGood) hNorm) hGrid
  have hPone : Gauss.P d Set.univ = 1 := by simp
  have hNonempty := HighProb.nonempty hPone hTriple
  have hResident := W.resident
  refine ⟨c, hc, s, t, lam, hlam, ⟨W⟩, hNear, ?_⟩
  filter_upwards [hNonempty, hResident] with N hN hR
  obtain ⟨hslt, _ω₀, _hcommon₀, _hgood₀, hactive, _hweight₀⟩ := hR
  obtain ⟨ω, hωall⟩ := hN
  rcases hωall with ⟨⟨⟨hωcommon, hωgood⟩, hωnorm⟩, hωgrid⟩
  have hweight := Gauss.APrimeActualWeightHighProbPlateau.weight_eq_one_of_mem_Good
    (E := (0 : ℝ)) (lam := lam) (s := s) (t := t) (N := N) (k := 1) (p := 1)
    (by norm_num) hlam W.base.hs0 W.base.hst W.base.ht1 hωgood hactive
  exact ⟨ω, hωcommon, hωgood, hωnorm, hωgrid, hactive, hweight⟩

#print axioms continuous_lkErr_stochDom
#print axioms exampleGrow_same_event_witness

end
end RBM.APrimeFreeLossNearContinuousSharp

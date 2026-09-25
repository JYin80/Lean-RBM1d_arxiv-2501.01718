/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossSharpCoordinateRepair
import RBM1D.Gauss.APrimeActualWeightHighProbPlateau
import RBM1D.Gauss.APrimeGeneralMovingEndpointCoord

/-!
# Sharp endpoint-grid near bound from the actual weighted moment

On the target `D = 60` mesh, the accepted weighted endpoint-coordinate moment and the actual
canonical-weight plateau give the unweighted endpoint-grid stochastic domination with the
paper's `R^2 * tailT_60` scale.  For each requested stochastic loss, the proof chooses the weight
loss first and the moment order after the failure exponent and grid/output cardinality.  This is
a fixed endpoint-grid statement; it does not assert the continuous-time near field of (5.48).
-/

namespace RBM.APrimeFreeLossNearGridSharp

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60

/-- A finite index for every active endpoint cell and every two-loop output. -/
abbrev GridIndex (s t : ℕ → ℝ) (N : ℕ) :=
  Fin (cutNetTop s t mesh N + 1) × LoopArg (d.L N) 2

/-- The endpoint associated to a target-mesh cell. -/
noncomputable def gridEndpoint (s t : ℕ → ℝ) (N k : ℕ) : ℝ :=
  APrimeFreeLossCoordinateBridge.endpoint s t 60 N k

/-- The `(L-K)` error at one endpoint-grid output. -/
noncomputable def gridLKErr (E : ℝ) (s t : ℕ → ℝ) (N : ℕ)
    (q : GridIndex s t N) (ω : Ω d) : ℝ :=
  (Gauss.sample d).lkErr E N (gridEndpoint s t N q.1.val) ω
    (LoopData.idx ((Step2.sigPM, q.2) : LoopData (d.L N) 2))

/-- The exact paper scale at that endpoint, with `R = etaT(s) / etaT(v)`. -/
noncomputable def gridNearScale (E : ℝ) (s t : ℕ → ℝ) (N : ℕ)
    (q : GridIndex s t N) : ℝ :=
  Step2Moment.ratR E s N (gridEndpoint s t N q.1.val) ^ 2 *
    tailT (d.W N : ℝ) ((band d).ell N (gridEndpoint s t N q.1.val))
      (etaT E (gridEndpoint s t N q.1.val)) 60
      (zdist (d.L N) (q.2 0 - q.2 1))

/-- The same output, restricted to the common high-probability weight plateau. -/
noncomputable def gridLKErrOnGood (E lam : ℝ) (s t : ℕ → ℝ) (N : ℕ)
    (q : GridIndex s t N) (ω : Ω d) : ℝ := by
  classical
  exact if ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N then
    gridLKErr E s t N q ω else 0

private theorem grid_card_bound {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (GridIndex s t N) : ℝ) ≤ (N : ℝ) ^ (260 : ℝ) := by
  have hmeshCard := APrimeGeneralMovingMesh.eventually_target_card_le
    (D := (60 : ℝ)) (by norm_num) hs0 hst ht1
  filter_upwards [hmeshCard, Filter.eventually_ge_atTop 81] with N hmeshN hN81
  have hfloor : (cutNetTop s t mesh N : ℝ) ≤ (t N - s N) * mesh N := by
    exact Nat.floor_le (mul_nonneg (sub_nonneg.mpr (hst N))
      (APrimeGeneralMovingMesh.targetMesh_pos 60 N).le)
  have hcells : ((cutNetTop s t mesh N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (259 : ℝ) := by
    have hcell0 : (cutNetTop s t mesh N : ℝ) + 1 ≤
        (t N - s N) * mesh N + 2 := by linarith
    have hcell1 : ((cutNetTop s t mesh N + 1 : ℕ) : ℝ) =
        (cutNetTop s t mesh N : ℝ) + 1 := by norm_num
    rw [hcell1]
    have hmeshN' : (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ (259 : ℝ) := by
      have htmp := hmeshN
      norm_num [mesh] at htmp ⊢
      exact htmp
    exact hcell0.trans hmeshN'
  have hLfour : Dims.growL N ^ 4 ≤ N := Dims.growL_pow_le N hN81
  have hLtwo : Dims.growL N ^ 2 ≤ N := by
    have hLone : 1 ≤ Dims.growL N := by have := Dims.three_le_growL N; omega
    exact (Nat.pow_le_pow_right (by omega : 0 < Dims.growL N)
      (by norm_num : 2 ≤ 4)).trans hLfour
  have houts : (Fintype.card (LoopArg (d.L N) 2) : ℝ) ≤ (N : ℝ) := by
    have hcard : Fintype.card (LoopArg (d.L N) 2) = (d.L N) ^ 2 := by
      calc
        Fintype.card (LoopArg (d.L N) 2) =
            (Finset.univ : Finset (LoopArg (d.L N) 2)).card := rfl
        _ = (d.L N) ^ 2 := Gauss.card_loopArg_two
    rw [hcard, Dims.exampleGrow_L]
    exact_mod_cast hLtwo
  have hprod : (Fintype.card (GridIndex s t N) : ℝ) =
      ((cutNetTop s t mesh N + 1 : ℕ) : ℝ) *
        (Fintype.card (LoopArg (d.L N) 2) : ℝ) := by
    change (Fintype.card (Fin (cutNetTop s t mesh N + 1) × LoopArg (d.L N) 2) : ℝ) = _
    rw [Fintype.card_prod, Fintype.card_fin]
    norm_num
  rw [hprod]
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos' : 0 < (N : ℝ) := by linarith
  have hpow : (N : ℝ) ^ (259 : ℝ) * (N : ℝ) = (N : ℝ) ^ (260 : ℝ) := by
    calc
      (N : ℝ) ^ (259 : ℝ) * (N : ℝ)
        = (N : ℝ) ^ (259 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
            congr 1
            exact (Real.rpow_one _).symm
    _ = (N : ℝ) ^ ((259 : ℝ) + 1) := by
      rw [← Real.rpow_add hNpos']
    _ = (N : ℝ) ^ (260 : ℝ) := by norm_num
  calc
    ((cutNetTop s t mesh N + 1 : ℕ) : ℝ) *
        (Fintype.card (LoopArg (d.L N) 2) : ℝ)
      ≤ (N : ℝ) ^ (259 : ℝ) * (N : ℝ) := mul_le_mul hcells houts
          (by positivity) (by positivity)
    _ = (N : ℝ) ^ (260 : ℝ) := hpow

private theorem good_moment_controls_grid_failure
    {E lam τ : ℝ} {s t : ℕ → ℝ} {p N : ℕ}
    {q : GridIndex s t N} {ω : Ω d}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hlam : 0 < lam) (hp : 1 ≤ p)
    (hk : q.1.val ≤ cutNetTop s t mesh N)
    (hGood : ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N)
    (hFail : (N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω) :
    ((N : ℝ) ^ τ) ^ (2 * p) ≤
      APrimeSmoothWeightActual.weight d E 60 lam s t mesh 2 p N q.1.val
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω *
        |Step2Moment.ratR E s N (gridEndpoint s t N q.1.val) ^ 2 *
          APrimeFreeLossCoordinateBridge.endpointCoordinate E 60 s t N q.1.val q.2 ω| ^ (2 * p) := by
  let v := gridEndpoint s t N q.1.val
  let R := Step2Moment.ratR E s N v
  let T := tailT (B.W N : ℝ) (B.ell N v) (etaT E v) 60
    (zdist (d.L N) (q.2 0 - q.2 1))
  let coord := APrimeFreeLossCoordinateBridge.endpointCoordinate E 60 s t N q.1.val q.2
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, gridEndpoint, APrimeFreeLossCoordinateBridge.endpoint]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos 60 N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hR : 1 ≤ R := by
    dsimp [R, Step2Moment.ratR]
    exact Step2Moment.one_le_ratR hE hv.1 hv1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hT : 0 < T := by
    dsimp [T]
    have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
    exact tailT_pos hW _
  have hRaw : gridLKErr E s t N q ω =
      ‖Step2.lk (Gauss.sample d) E N v ω q.2‖ := by
    change (Gauss.sample d).lkErr E N v ω
        (pmLoop (q.2 0) (q.2 1)) = _
    exact (Step2.norm_lk_eq (Gauss.sample d) E N v ω q.2).symm
  have hcoord := APrimeGeneralMovingEndpointCoord.norm_coordAt_endpoint
    (N := N) (E := E) (D := (60 : ℝ)) (s := s) hE
    (hs0 N) hv.1 hv1 ω q.2
  have hcoord' : coord ω =
      (‖Step2.lk (Gauss.sample d) E N v ω q.2‖ /
        Step2.tT B E N 60 v (zdist (d.L N) (q.2 0 - q.2 1))) / R ^ 4 := by
    simpa [coord, APrimeFreeLossCoordinateBridge.endpointCoordinate,
      gridEndpoint, APrimeFreeLossCoordinateBridge.endpoint, v, R] using hcoord
  have hcoordNonneg : 0 ≤ coord ω := by
    dsimp [coord, APrimeFreeLossCoordinateBridge.endpointCoordinate]
    exact norm_nonneg _
  have hratio : R ^ 2 * |coord ω| =
      gridLKErr E s t N q ω / (R ^ 2 * T) := by
    rw [abs_of_nonneg hcoordNonneg, hcoord', hRaw]
    simp only [Step2.tT]
    field_simp [hRpos.ne', hT.ne']
    rw [show T = tailT (B.W N : ℝ) (B.ell N v) (etaT E v) 60
      (zdist (d.L N) (q.2 0 - q.2 1)) from rfl]
    calc
      ‖Step2.lk (Gauss.sample d) E N v ω q.2‖ * T * T⁻¹ =
          ‖Step2.lk (Gauss.sample d) E N v ω q.2‖ * (T * T⁻¹) := by ring
      _ = ‖Step2.lk (Gauss.sample d) E N v ω q.2‖ := by
        rw [mul_inv_cancel₀ hT.ne', mul_one]
  have hden : 0 < R ^ 2 * T := mul_pos (sq_pos_of_pos hRpos) hT
  have hY : (N : ℝ) ^ τ < R ^ 2 * |coord ω| := by
    rw [hratio]
    apply (lt_div_iff₀ hden).2
    simpa [gridNearScale, v, R, T] using hFail
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hY.le (2 * p)
  have hpow' : ((N : ℝ) ^ τ) ^ (2 * p) ≤
      |R ^ 2 * coord ω| ^ (2 * p) := by
    have habs : R ^ 2 * |coord ω| = |R ^ 2 * coord ω| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg R), abs_of_nonneg hcoordNonneg]
    rw [habs] at hpow
    exact hpow
  have hweight := APrimeActualWeightHighProbPlateau.weight_eq_one_of_mem_Good
    (p := p) hE hlam hs0 hst ht1 hGood hk
  have habs : |R ^ 2 * coord ω| = R ^ 2 * |coord ω| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg R), abs_of_nonneg hcoordNonneg]
  rw [hweight, one_mul]
  exact hpow'

/-- For a fixed loss exponent, every grid point's failure intersected with the actual-weight
plateau has arbitrarily high polynomial decay. -/
private theorem eventually_good_grid_failure_le
    {E c τ lam : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore (Gauss.sample d) E s)
    (hτ : 0 < τ) (hlam : 0 < lam)
    (hlamSmall : lam ≤ min (1 / 10000) (c / 10000))
    (hlamTau : lam ≤ τ / 4) :
    ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q : GridIndex s t N,
      (Gauss.P d) {ω | ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
        (N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro D hD
  obtain ⟨p, hpLarge⟩ := exists_nat_ge ((D + 1) / τ)
  have hp : 1 ≤ p := by
    have hpPos : 0 < (p : ℝ) := lt_of_lt_of_le (by positivity) hpLarge
    exact_mod_cast hpPos
  have hpBudget : D + 1 ≤ τ * (p : ℝ) := by
    rw [div_le_iff₀ hτ] at hpLarge
    linarith
  obtain ⟨C, hC, hMoment⟩ :=
    APrimeFreeLossSharpCoordinateRepair.eventually_sharp_actual_coordinate_moment
      (E := E) (D := (60 : ℝ)) (c := c) (lambda := lam) (s := s) (t := t) (p := p)
      hE (by norm_num) hs0 hst ht1 hc hreg hB hlam hlamSmall hp
  have hCevent : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ (τ / 4) :=
    eventually_le_rpow C (by linarith)
  filter_upwards [hMoment, hCevent, Filter.eventually_ge_atTop 2] with N hMomentN hCN hN
  intro q
  let k := q.1.val
  have hk : k ≤ cutNetTop s t mesh N := Nat.lt_succ_iff.mp q.1.isLt
  have hSharp := hMomentN k hk q.2
  let v := gridEndpoint s t N k
  let R := Step2Moment.ratR E s N v
  let coord := APrimeFreeLossCoordinateBridge.endpointCoordinate E 60 s t N k q.2
  let W := APrimeSmoothWeightActual.weight d E 60 lam s t mesh 2 p N k
    (APrimeSmoothWeightActual.canonicalM d s t mesh N)
  let Z : Ω d → ℝ := fun ω => W ω * |R ^ 2 * coord ω| ^ (2 * p)
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v, gridEndpoint, APrimeFreeLossCoordinateBridge.endpoint]
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos 60 N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hR : 1 ≤ R := by
    dsimp [R, Step2Moment.ratR]
    exact Step2Moment.one_le_ratR hE hv.1 hv1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRcancel : R ^ 2 * R ^ (-(2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hRpos]
    norm_num
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact APrimeSmoothWeightActual.weight_nonneg d E 60 lam s t mesh 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω
  have hZnonneg : ∀ ω, 0 ≤ Z ω := by
    intro ω
    exact mul_nonneg (hW0 ω) (by positivity)
  have hZeq : ∀ ω, Z ω = (R ^ 2) ^ (2 * p) * (W ω * |coord ω| ^ (2 * p)) := by
    intro ω
    dsimp [Z]
    rw [abs_mul, abs_of_nonneg (sq_nonneg R), mul_pow]
    ring
  have hZInt : Integrable Z (Gauss.P d) := by
    have hscaled := hSharp.2.1.const_mul ((R ^ 2) ^ (2 * p))
    convert hscaled using 1 <;> ext ω <;> rw [hZeq]
  have hZIntegral : ∫ ω, Z ω ∂(Gauss.P d) ≤
      (C * (N : ℝ) ^ (5 * lam / 32)) ^ (2 * p) := by
    have hfactor : 0 ≤ (R ^ 2) ^ (2 * p) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hSharp.2.2 hfactor
    have hIntEq : (∫ ω, Z ω ∂(Gauss.P d)) =
        (R ^ 2) ^ (2 * p) *
          ∫ ω, W ω * |coord ω| ^ (2 * p) ∂(Gauss.P d) := by
      rw [show Z = fun ω => (R ^ 2) ^ (2 * p) * (W ω * |coord ω| ^ (2 * p)) from
        funext hZeq]
      rw [integral_const_mul]
    have hcancel : (R ^ 2) ^ (2 * p) *
        (C * (N : ℝ) ^ (5 * lam / 32) * R ^ (-(2 : ℝ))) ^ (2 * p) =
        (C * (N : ℝ) ^ (5 * lam / 32)) ^ (2 * p) := by
      rw [← mul_pow]
      congr 1
      calc
        R ^ 2 * (C * (N : ℝ) ^ (5 * lam / 32) * R ^ (-(2 : ℝ)))
          = (C * (N : ℝ) ^ (5 * lam / 32)) * (R ^ 2 * R ^ (-(2 : ℝ))) := by ring
        _ = C * (N : ℝ) ^ (5 * lam / 32) := by rw [hRcancel, mul_one]
    rw [hIntEq]
    calc
      (R ^ 2) ^ (2 * p) *
          ∫ ω, W ω * |coord ω| ^ (2 * p) ∂(Gauss.P d)
        ≤ (R ^ 2) ^ (2 * p) *
            (C * (N : ℝ) ^ (5 * lam / 32) * R ^ (-(2 : ℝ))) ^ (2 * p) := hmul
      _ = (C * (N : ℝ) ^ (5 * lam / 32)) ^ (2 * p) := hcancel
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : 0 < (N : ℝ) := by linarith
  have hbase : C * (N : ℝ) ^ (5 * lam / 32) ≤
      (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (5 * lam / 32) :=
    mul_le_mul_of_nonneg_right hCN (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hbasePow := pow_le_pow_left₀ (by positivity) hbase (2 * p)
  have hpowconv : ((N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (5 * lam / 32)) ^ (2 * p) =
      (N : ℝ) ^ ((τ / 4 + 5 * lam / 32) * (2 * (p : ℝ))) := by
    rw [← Real.rpow_add hNpos]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  have hexp : (τ / 4 + 5 * lam / 32) * (2 * (p : ℝ)) ≤ τ * (p : ℝ) := by
    nlinarith [hlamTau]
  have hmomentPow : (C * (N : ℝ) ^ (5 * lam / 32)) ^ (2 * p) ≤
      (N : ℝ) ^ (τ * (p : ℝ)) := by
    rw [hpowconv] at hbasePow
    exact hbasePow.trans (Real.rpow_le_rpow_of_exponent_le hNreal hexp)
  have hmarkLevel : 0 < ((N : ℝ) ^ τ) ^ (2 * p) := by positivity
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => hZnonneg ω) hZInt (((N : ℝ) ^ τ) ^ (2 * p))
  have hmarkReal : (Gauss.P d).real {ω |
      ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω} ≤ (N : ℝ) ^ (-D) := by
    have hMarkLe : (Gauss.P d).real {ω |
        ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω} ≤
          (∫ ω, Z ω ∂(Gauss.P d)) / (((N : ℝ) ^ τ) ^ (2 * p)) := by
      rw [le_div_iff₀ hmarkLevel]
      simpa [mul_comm] using hmark
    have hZIntegral' : ∫ ω, Z ω ∂(Gauss.P d) ≤ (N : ℝ) ^ (τ * (p : ℝ)) :=
      hZIntegral.trans hmomentPow
    calc
      (Gauss.P d).real {ω | ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω}
        ≤ (∫ ω, Z ω ∂(Gauss.P d)) / (((N : ℝ) ^ τ) ^ (2 * p)) := hMarkLe
      _ ≤ (N : ℝ) ^ (τ * (p : ℝ)) / (((N : ℝ) ^ τ) ^ (2 * p)) :=
        div_le_div_of_nonneg_right hZIntegral' (le_of_lt hmarkLevel)
      _ ≤ (N : ℝ) ^ (-D) := by
        rw [show ((N : ℝ) ^ τ) ^ (2 * p) =
            (N : ℝ) ^ (τ * (2 * (p : ℝ))) by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
              congr 1
              push_cast
              ring]
        rw [← Real.rpow_sub hNpos]
        exact Real.rpow_le_rpow_of_exponent_le hNreal (by
          have := hpBudget
          linarith)
  have hmarkENN : (Gauss.P d) {ω |
      ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    calc
      (Gauss.P d) {ω | ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω}
        = ENNReal.ofReal ((Gauss.P d).real
            {ω | ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω}) := by
              rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hmarkReal
  have hsub : {ω | ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
        (N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω} ⊆
      {ω | ((N : ℝ) ^ τ) ^ (2 * p) ≤ Z ω} := by
    intro ω hω
    have hpoint := good_moment_controls_grid_failure hE hs0 hst ht1 hlam hp hk
      hω.1 hω.2
    simpa [Z, W, coord, v, R, k] using hpoint
  exact (measure_mono hsub).trans hmarkENN

/-- The unweighted endpoint-grid near bound at `D=60`: uniformly for all active target-mesh
cells (including `k=0`) and all two-loop outputs, `lkErr` is stochastically dominated by
`R^2 * tailT_60`, with the same-event actual-weight transfer. -/
theorem endpoint_grid_lkErr_stochDom
    {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    StochDom (Gauss.P d) (gridLKErr E s t)
      (fun N q _ => gridNearScale E s t N q) := by
  have hcard := grid_card_bound hs0 hst ht1
  letI : ∀ N, Fintype (GridIndex s t N) := fun _ => inferInstance
  intro τ hτ D hD
  let lam : ℝ := min (min (1 / 10000) (c / 10000)) (τ / 4)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  have hlamSmall : lam ≤ min (1 / 10000 : ℝ) (c / 10000) := by
    dsimp [lam]
    exact min_le_left _ _
  have hGood := APrimeActualWeightHighProbPlateau.highProb_Good hlam hE
    hs0 hst ht1 hc hreg hB
  let Ξ : ∀ N, GridIndex s t N → Set (Ω d) := fun N q =>
    APrimeActualWeightHighProbPlateau.Good E lam s t N ∩
      {ω | ¬ ((N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω)}
  have hEach : ∀ D' > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q,
      (Gauss.P d) (Ξ N q)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro D' hD'
    have hgood := hGood (D' + 1) (by linarith)
    have hfail := eventually_good_grid_failure_le hE hs0 hst ht1 hc hreg hB
      hτ hlam hlamSmall (by dsimp [lam]; exact min_le_right _ _)
      (D' + 1) (by linarith)
    filter_upwards [hgood, hfail, eventually_ge_atTop 2,
      eventually_two_mul_rpow_le D'] with N hgoodN hfailN hN htwo
    intro q
    have hsub : (Ξ N q)ᶜ ⊆
        (APrimeActualWeightHighProbPlateau.Good E lam s t N)ᶜ ∪
          {ω | ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
            (N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω} := by
      intro ω hω
      by_cases hG : ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N
      · right
        refine ⟨hG, ?_⟩
        have hnot : ¬ (ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
            ¬ ((N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω)) := by
          change ¬ ω ∈ Ξ N q at hω
          change ¬ (ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
            ¬ ((N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω)) at hω
          exact hω
        by_contra hfail
        exact hnot ⟨hG, hfail⟩
      · exact Or.inl hG
    have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (-(D' + 1)) :=
      Real.rpow_nonneg (Nat.cast_nonneg N) _
    calc
      (Gauss.P d) (Ξ N q)ᶜ
        ≤ (Gauss.P d) ((APrimeActualWeightHighProbPlateau.Good E lam s t N)ᶜ ∪
          {ω | ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
            (N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω}) :=
              measure_mono hsub
      _ ≤ (Gauss.P d) (APrimeActualWeightHighProbPlateau.Good E lam s t N)ᶜ +
          (Gauss.P d) {ω | ω ∈ APrimeActualWeightHighProbPlateau.Good E lam s t N ∧
            (N : ℝ) ^ τ * gridNearScale E s t N q < gridLKErr E s t N q ω} :=
              measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) +
          ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := add_le_add hgoodN (hfailN q)
      _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D' + 1))) := by
            rw [← ENNReal.ofReal_add hpos hpos]
            ring_nf
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
            apply ENNReal.ofReal_le_ofReal
            exact htwo
  have hAll : HighProb (Gauss.P d) (fun N => ⋂ q, Ξ N q) :=
    HighProb.biInter (P := Gauss.P d) (C := (260 : ℝ)) (by norm_num) hcard hEach
  filter_upwards [hAll (D + 260) (by linarith), Filter.eventually_ge_atTop 1] with N hNall hN1
  have hbad : badSet (gridLKErr E s t)
      (fun N q _ => gridNearScale E s t N q) τ N ⊆ (⋂ q, Ξ N q)ᶜ := by
    intro ω hω
    simp only [badSet, Set.mem_ofPred_eq] at hω
    obtain ⟨q, hfail⟩ := hω
    change ω ∉ ⋂ q, Ξ N q
    intro hAll
    have hq := Set.mem_iInter.mp hAll q
    exact hq.2 hfail
  have hpow : (N : ℝ) ^ (-(D + 260)) ≤ (N : ℝ) ^ (-D) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
    linarith
  calc
    (Gauss.P d) (badSet (gridLKErr E s t)
        (fun N q _ => gridNearScale E s t N q) τ N)
      ≤ (Gauss.P d) (⋂ q, Ξ N q)ᶜ := measure_mono hbad
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 260))) := hNall
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hpow

/-- A same-window satisfiability witness at `E=0`.  Its resident sample lies simultaneously in
the actual common source event and the plateau event; at the same sample, the positive active
cell `k=1` has actual canonical weight exactly one. -/
theorem exampleGrow_same_event_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ, ∃ lam : ℝ, 0 < lam ∧
      Nonempty (APrimeActualWeightHighProbPlateau.PositiveWindowWitness c lam s t) ∧
      StochDom (Gauss.P d) (gridLKErr 0 s t)
        (fun N q _ => gridNearScale 0 s t N q) := by
  let lam : ℝ := 1 / 10000
  have hlam : 0 < lam := by norm_num [lam]
  obtain ⟨c, hc, s, t, ⟨W⟩⟩ :=
    APrimeActualWeightHighProbPlateau.positive_window_joint_witness hlam
  have hNear := endpoint_grid_lkErr_stochDom (E := 0) (c := c) (s := s) (t := t)
    (by norm_num) W.base.hs0 W.base.hst W.base.ht1 W.base.hc W.base.hreg W.base.hB
  exact ⟨c, hc, s, t, lam, hlam, ⟨W⟩, hNear⟩

#print axioms endpoint_grid_lkErr_stochDom
#print axioms exampleGrow_same_event_witness

end
end RBM.APrimeFreeLossNearGridSharp

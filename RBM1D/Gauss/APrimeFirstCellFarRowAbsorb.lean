/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellScaleFloors
import RBM1D.Gauss.APrimeFirstCellQVEarlyRows

/-!
# T461: deterministic first-cell three-row absorption

The literal stored and current three-row brackets are bounded at every
actual moving endpoint.  Each summand is recorded separately between zero
and one before the sum is bounded by three.
-/

namespace RBM.APrimeFirstCellFarRowAbsorb

open Filter Set Gauss CutHypTheta

/-- The fixed bootstrap exponent `delta = c / 1000` for `c = 1/2`. -/
noncomputable def delta : ℝ := 1 / 2000

/-- The fixed mesh exponent `tau = delta / 16`. -/
noncomputable def tau : ℝ := delta / 16

theorem delta_pos : 0 < delta := by norm_num [delta]

theorem tau_pos : 0 < tau := by norm_num [tau, delta]

/-- The strict exponent left after paying the endpoint half-scale. -/
noncomputable def quadGap : ℝ :=
  1 / 4 - (4 * delta + 2 * tau)

/-- The strict exponent left after paying the endpoint full scale. -/
noncomputable def cubicGap : ℝ :=
  1 / 2 - (6 * delta + 3 * tau)

theorem quadGap_pos : 0 < quadGap := by
  norm_num [quadGap, tau, delta]

theorem cubicGap_pos : 0 < cubicGap := by
  norm_num [cubicGap, tau, delta]

/-- The three stored-time summands. -/
noncomputable def storedNear (u : ℝ) : ℝ :=
  APrimeFirstCellLoopCap.xRate u ^ (-(9 / 2 : ℝ))

noncomputable def storedQuad (N : ℕ) (v u : ℝ) : ℝ :=
  (N : ℝ) ^ (4 * delta + 2 * tau) *
    APrimeFirstCellLoopCap.endpointScale N v ^ (-(1 / 2 : ℝ)) *
      APrimeFirstCellLoopCap.xRate u ^ (7 / 4 : ℝ)

noncomputable def storedCubic (N : ℕ) (v u : ℝ) : ℝ :=
  (N : ℝ) ^ (6 * delta + 3 * tau) *
    (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
      APrimeFirstCellLoopCap.xRate u ^ (5 : ℝ)

/-- The exact bracket occurring in `storedRowsRate`. -/
noncomputable def storedBracket (N : ℕ) (v u : ℝ) : ℝ :=
  storedNear u + storedQuad N v u + storedCubic N v u

/-- The three current-time summands. -/
noncomputable def currentNear (r : ℝ) : ℝ :=
  APrimeFirstCellLoopCap.xRate r ^ (-(3 / 2 : ℝ))

noncomputable def currentQuad (N : ℕ) (v r : ℝ) : ℝ :=
  (N : ℝ) ^ (4 * delta + 2 * tau) *
    APrimeFirstCellLoopCap.endpointScale N v ^ (-(1 / 2 : ℝ)) *
      APrimeFirstCellLoopCap.xRate r ^ (19 / 4 : ℝ)

noncomputable def currentCubic (N : ℕ) (v r : ℝ) : ℝ :=
  (N : ℝ) ^ (6 * delta + 3 * tau) *
    (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
      APrimeFirstCellLoopCap.xRate r ^ (8 : ℝ)

/-- The exact bracket occurring in `currentRate`. -/
noncomputable def currentBracket (N : ℕ) (v r : ℝ) : ℝ :=
  currentNear r + currentQuad N v r + currentCubic N v r

/-- Every row is nonnegative and at most one. -/
structure ThreeRowBounds (row₁ row₂ row₃ : ℝ) : Prop where
  row₁_nonneg : 0 ≤ row₁
  row₁_le_one : row₁ ≤ 1
  row₂_nonneg : 0 ≤ row₂
  row₂_le_one : row₂ ≤ 1
  row₃_nonneg : 0 ≤ row₃
  row₃_le_one : row₃ ≤ 1

theorem ThreeRowBounds.sum_le_three {row₁ row₂ row₃ : ℝ}
    (h : ThreeRowBounds row₁ row₂ row₃) : row₁ + row₂ + row₃ ≤ 3 := by
  linarith [h.row₁_le_one, h.row₂_le_one, h.row₃_le_one]

/-- The public stored rate uses exactly `storedBracket`. -/
theorem storedRowsRate_eq (ν : ℝ) (N : ℕ) (v u : ℝ) :
    APrimeFirstCellQVEarlyRows.storedRowsRate delta ν N v u =
      16384 * (N : ℝ) ^ (ν - 4 * delta) * (etaT 0 0)⁻¹ *
        storedBracket N v u := by
  rfl

/-- The public current rate uses exactly `currentBracket`. -/
theorem currentRate_eq (ν : ℝ) (N : ℕ) (v r : ℝ) :
    APrimeFirstCellQVCurrentRows.currentRate delta tau ν N v r =
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ ν *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) *
            currentBracket N v r := by
  rfl

private theorem xRate_bounds_of_mem {τ' : ℝ} {N k : ℕ} {q : ℝ}
    (hpack : APrimeFirstCellScaleFloors.ScalePackage τ' N k)
    (hq : q ∈ Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    1 ≤ APrimeFirstCellLoopCap.xRate q ∧
      APrimeFirstCellLoopCap.xRate q ≤ 2 := by
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hq1 : q < 1 :=
    hq.2.trans hpack.time_le_half |>.trans_lt (by norm_num)
  have hηq : 0 < etaT 0 q := Step2.etaT_pos' (by norm_num) hq1
  have hηv : 0 < etaT 0 v :=
    Step2.etaT_pos' (by norm_num)
      (hpack.time_le_half.trans_lt (by norm_num))
  have hη0 : etaT 0 0 = 1 := by norm_num [etaT, mE_zero]
  have hqv : APrimeFirstCellLoopCap.xRate q ≤
      APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    rw [hη0, one_div, one_div]
    exact inv_anti₀ hηv (etaT_le_of_le (by norm_num) hq.2)
  have hqone : 1 ≤ APrimeFirstCellLoopCap.xRate q := by
    simpa only [APrimeFirstCellLoopCap.xRate, Step2Moment.ratR] using
      (Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
        (N := N) (by norm_num) hq.1 hq1)
  exact ⟨hqone, hqv.trans hpack.ratio_le_two⟩

private theorem far_row_le_power {N : ℕ} {A x e a b : ℝ}
    (hN : 1 ≤ N)
    (hA : (N : ℝ) ^ (1 / 2 : ℝ) ≤ A)
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (N : ℝ) ^ e * A ^ (-a) * x ^ b ≤
      (2 : ℝ) ^ b * (N : ℝ) ^ (e - a / 2) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hhalfpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hApow : A ^ (-a) ≤
      ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hhalfpos hA (neg_nonpos.mpr ha)
  have hxpow : x ^ b ≤ (2 : ℝ) ^ b :=
    Real.rpow_le_rpow hx0 hx2 hb
  calc
    (N : ℝ) ^ e * A ^ (-a) * x ^ b ≤
        (N : ℝ) ^ e * ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (-a) *
          (2 : ℝ) ^ b := by gcongr
    _ = (2 : ℝ) ^ b * (N : ℝ) ^ (e - a / 2) := by
      calc
        (N : ℝ) ^ e * ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (-a) *
            (2 : ℝ) ^ b =
            (2 : ℝ) ^ b * ((N : ℝ) ^ e *
              ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (-a)) := by ring
        _ = _ := by
          rw [← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
          congr 1
          ring_nf

private theorem far_row_le_one {N : ℕ} {A x e a b bigB : ℝ}
    (hN : 1 ≤ N)
    (hA : (N : ℝ) ^ (1 / 2 : ℝ) ≤ A)
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbB : b ≤ bigB)
    (hdecay : (2 : ℝ) ^ bigB * (N : ℝ) ^ (e - a / 2) ≤ 1) :
    (N : ℝ) ^ e * A ^ (-a) * x ^ b ≤ 1 := by
  have hrow := far_row_le_power (e := e) hN hA hx0 hx2 ha hb
  have hconst : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ bigB :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbB
  have hpow0 : 0 ≤ (N : ℝ) ^ (e - a / 2) := by positivity
  exact hrow.trans ((mul_le_mul_of_nonneg_right hconst hpow0).trans hdecay)

private theorem eventually_constant_decay (C α : ℝ)
    (_hC : 0 ≤ C) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ (-α) ≤ 1 := by
  filter_upwards [eventually_le_rpow C hα, eventually_ge_atTop 1] with N hCN hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hp : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNpos _
  rw [Real.rpow_neg hNpos.le]
  calc
    C * ((N : ℝ) ^ α)⁻¹ ≤
        (N : ℝ) ^ α * ((N : ℝ) ^ α)⁻¹ :=
      mul_le_mul_of_nonneg_right hCN (inv_nonneg.mpr hp.le)
    _ = 1 := mul_inv_cancel₀ hp.ne'

private theorem stored_rows_of_scale {τ' : ℝ} {N k : ℕ} (hN : 1 ≤ N)
    (hpack : APrimeFirstCellScaleFloors.ScalePackage τ' N k)
    (hquad : (2 : ℝ) ^ (19 / 4 : ℝ) *
      (N : ℝ) ^ (-quadGap) ≤ 1)
    (hcubic : (2 : ℝ) ^ (8 : ℝ) *
      (N : ℝ) ^ (-cubicGap) ≤ 1)
    {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k
    ThreeRowBounds (storedNear u) (storedQuad N v u) (storedCubic N v u) ∧
      storedBracket N v u ≤ 3 := by
  dsimp only
  obtain ⟨hxu1, hxu2⟩ := xRate_bounds_of_mem hpack hu
  have hxu0 : 0 ≤ APrimeFirstCellLoopCap.xRate u := zero_le_one.trans hxu1
  have hnear0 : 0 ≤ storedNear u := by
    exact Real.rpow_nonneg hxu0 _
  have hnear1 : storedNear u ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hxu1 (by norm_num)
  have hquadDecay : (2 : ℝ) ^ (19 / 4 : ℝ) *
      (N : ℝ) ^ ((4 * delta + 2 * tau) - (1 / 2 : ℝ) / 2) ≤ 1 := by
    have he : (4 * delta + 2 * tau) - (1 / 2 : ℝ) / 2 =
        -quadGap := by
      unfold quadGap
      ring
    rw [he]
    exact hquad
  have hcubicDecay : (2 : ℝ) ^ (8 : ℝ) *
      (N : ℝ) ^ ((6 * delta + 3 * tau) - (1 : ℝ) / 2) ≤ 1 := by
    have he : (6 * delta + 3 * tau) - (1 : ℝ) / 2 =
        -cubicGap := by
      unfold cubicGap
      ring
    rw [he]
    exact hcubic
  have hquad1 : storedQuad N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) u ≤ 1 := by
    unfold storedQuad
    exact far_row_le_one hN hpack.n_half_le_scale hxu0 hxu2
      (by norm_num) (by norm_num) (by norm_num) hquadDecay
  have hcubic1 : storedCubic N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) u ≤ 1 := by
    unfold storedCubic
    rw [← Real.rpow_neg_one]
    exact far_row_le_one hN hpack.n_half_le_scale hxu0 hxu2
      (by norm_num) (by norm_num) (by norm_num) hcubicDecay
  have hquad0 : 0 ≤ storedQuad N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) u := by
    unfold storedQuad
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (Real.rpow_nonneg hpack.scale_pos.le _))
      (Real.rpow_nonneg hxu0 _)
  have hcubic0 : 0 ≤ storedCubic N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) u := by
    unfold storedCubic
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (inv_nonneg.mpr hpack.scale_pos.le))
      (Real.rpow_nonneg hxu0 _)
  let hrows : ThreeRowBounds (storedNear u)
      (storedQuad N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) u)
      (storedCubic N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) u) :=
    ⟨hnear0, hnear1, hquad0, hquad1, hcubic0, hcubic1⟩
  exact ⟨hrows, by
    unfold storedBracket
    exact hrows.sum_le_three⟩

private theorem current_rows_of_scale {τ' : ℝ} {N k : ℕ} (hN : 1 ≤ N)
    (hpack : APrimeFirstCellScaleFloors.ScalePackage τ' N k)
    (hquad : (2 : ℝ) ^ (19 / 4 : ℝ) *
      (N : ℝ) ^ (-quadGap) ≤ 1)
    (hcubic : (2 : ℝ) ^ (8 : ℝ) *
      (N : ℝ) ^ (-cubicGap) ≤ 1)
    {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ)
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k
    ThreeRowBounds (currentNear r) (currentQuad N v r) (currentCubic N v r) ∧
      currentBracket N v r ≤ 3 := by
  dsimp only
  obtain ⟨hxr1, hxr2⟩ := xRate_bounds_of_mem hpack hr
  have hxr0 : 0 ≤ APrimeFirstCellLoopCap.xRate r := zero_le_one.trans hxr1
  have hnear0 : 0 ≤ currentNear r := by
    exact Real.rpow_nonneg hxr0 _
  have hnear1 : currentNear r ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hxr1 (by norm_num)
  have hquadDecay : (2 : ℝ) ^ (19 / 4 : ℝ) *
      (N : ℝ) ^ ((4 * delta + 2 * tau) - (1 / 2 : ℝ) / 2) ≤ 1 := by
    have he : (4 * delta + 2 * tau) - (1 / 2 : ℝ) / 2 =
        -quadGap := by
      unfold quadGap
      ring
    rw [he]
    exact hquad
  have hcubicDecay : (2 : ℝ) ^ (8 : ℝ) *
      (N : ℝ) ^ ((6 * delta + 3 * tau) - (1 : ℝ) / 2) ≤ 1 := by
    have he : (6 * delta + 3 * tau) - (1 : ℝ) / 2 =
        -cubicGap := by
      unfold cubicGap
      ring
    rw [he]
    exact hcubic
  have hquad1 : currentQuad N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ≤ 1 := by
    unfold currentQuad
    exact far_row_le_one hN hpack.n_half_le_scale hxr0 hxr2
      (by norm_num) (by norm_num) (by norm_num) hquadDecay
  have hcubic1 : currentCubic N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ≤ 1 := by
    unfold currentCubic
    rw [← Real.rpow_neg_one]
    exact far_row_le_one hN hpack.n_half_le_scale hxr0 hxr2
      (by norm_num) (by norm_num) (by norm_num) hcubicDecay
  have hquad0 : 0 ≤ currentQuad N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r := by
    unfold currentQuad
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (Real.rpow_nonneg hpack.scale_pos.le _))
      (Real.rpow_nonneg hxr0 _)
  have hcubic0 : 0 ≤ currentCubic N
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r := by
    unfold currentCubic
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (inv_nonneg.mpr hpack.scale_pos.le))
      (Real.rpow_nonneg hxr0 _)
  let hrows : ThreeRowBounds (currentNear r)
      (currentQuad N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r)
      (currentCubic N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r) :=
    ⟨hnear0, hnear1, hquad0, hquad1, hcubic0, hcubic1⟩
  exact ⟨hrows, by
    unfold currentBracket
    exact hrows.sum_le_three⟩

/-- Uniform stored-row absorption at every actual moving first-cell endpoint. -/
theorem eventually_stored_rows_absorbed {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ u ∈ Icc (0 : ℝ) v,
        ThreeRowBounds (storedNear u) (storedQuad N v u) (storedCubic N v u) ∧
          storedBracket N v u ≤ 3 := by
  filter_upwards [APrimeFirstCellScaleFloors.eventually_scalePackage hτ',
    eventually_constant_decay ((2 : ℝ) ^ (19 / 4 : ℝ)) quadGap
      (by positivity) quadGap_pos,
    eventually_constant_decay ((2 : ℝ) ^ (8 : ℝ)) cubicGap
      (by positivity) cubicGap_pos,
    eventually_ge_atTop 1] with N hpack hquad hcubic hN
  intro k hk
  dsimp only
  intro u hu
  exact stored_rows_of_scale hN (hpack k hk) hquad hcubic hu

/-- Uniform current-row absorption at every actual moving first-cell endpoint. -/
theorem eventually_current_rows_absorbed {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Icc (0 : ℝ) v,
        ThreeRowBounds (currentNear r) (currentQuad N v r) (currentCubic N v r) ∧
          currentBracket N v r ≤ 3 := by
  filter_upwards [APrimeFirstCellScaleFloors.eventually_scalePackage hτ',
    eventually_constant_decay ((2 : ℝ) ^ (19 / 4 : ℝ)) quadGap
      (by positivity) quadGap_pos,
    eventually_constant_decay ((2 : ℝ) ^ (8 : ℝ)) cubicGap
      (by positivity) cubicGap_pos,
    eventually_ge_atTop 1] with N hpack hquad hcubic hN
  intro k hk
  dsimp only
  intro r hr
  exact current_rows_of_scale hN (hpack k hk) hquad hcubic hr

/-- Stored bracket form for later prefix/current cross estimates. -/
theorem eventually_storedBracket_le_three {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ u ∈ Icc (0 : ℝ) v, storedBracket N v u ≤ 3 := by
  filter_upwards [eventually_stored_rows_absorbed hτ'] with N hN
  intro k hk
  dsimp only
  intro u hu
  exact (hN k hk u hu).2

/-- Current bracket form for later prefix/current cross estimates. -/
theorem eventually_currentBracket_le_three {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Icc (0 : ℝ) v, currentBracket N v r ≤ 3 := by
  filter_upwards [eventually_current_rows_absorbed hτ'] with N hN
  intro k hk
  dsimp only
  intro r hr
  exact (hN k hk r hr).2

/-- The zero endpoint and its zero stored/current times are retained. -/
theorem eventually_zero_rows_absorbed {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 0
      v = 0 ∧ storedBracket N v 0 ≤ 3 ∧ currentBracket N v 0 ≤ 3 := by
  filter_upwards [eventually_storedBracket_le_three hτ',
    eventually_currentBracket_le_three hτ'] with N hs hc
  have hv : cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 = 0 := by
    simp only [cutNetPt_zero]
  refine ⟨hv, hs 0 (Nat.zero_le _) 0 ?_, hc 0 (Nat.zero_le _) 0 ?_⟩
  · simp only [hv, mem_Icc]
    exact ⟨le_rfl, le_rfl⟩
  · simp only [hv, mem_Icc]
    exact ⟨le_rfl, le_rfl⟩

/-- At the strictly positive actual `k=2` endpoint, zero time supplies a
nonempty stored/current instance of the uniform bounds. -/
theorem eventually_positive_two_rows_absorbed {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧ storedBracket N v 0 ≤ 3 ∧ currentBracket N v 0 ≤ 3 := by
  filter_upwards [APrimeFirstCellScaleFloors.eventually_positive_two_scalePackage hτ',
    eventually_storedBracket_le_three hτ',
    eventually_currentBracket_le_three hτ'] with N htwo hs hc
  dsimp only at htwo ⊢
  refine ⟨htwo.1, hs 2 htwo.2.resident 0 ?_,
    hc 2 htwo.2.resident 0 ?_⟩
  · exact ⟨le_rfl, htwo.2.time_nonneg⟩
  · exact ⟨le_rfl, htwo.2.time_nonneg⟩

#print axioms eventually_stored_rows_absorbed
#print axioms eventually_current_rows_absorbed
#print axioms eventually_storedBracket_le_three
#print axioms eventually_currentBracket_le_three
#print axioms eventually_zero_rows_absorbed
#print axioms eventually_positive_two_rows_absorbed

end RBM.APrimeFirstCellFarRowAbsorb

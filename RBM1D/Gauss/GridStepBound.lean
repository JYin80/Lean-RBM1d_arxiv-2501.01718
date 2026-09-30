/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridExpansion
import RBM1D.Gauss.GridDriftSum
import RBM1D.Gauss.GridDuhamelTail
import RBM1D.Gauss.GridNetLift
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.DimsExample

/-!
# The grid step bound: the η-pairing, the remainder sum and `phi_arith'`

Paper `(5.39)`–`(5.41)`, `(5.45)`, `(5.47)`; the grid analogue of Step 2's step bound and its
arithmetic (`Hierarchy/Step2.lean`).  Deterministic: fixed `N`, `ω`, target `k ≤ K N`; every
random input is a hypothesis.

## Main results

The five-term bound `‖A_k a‖ ≤ Φg(u_k) T_{u_k}(a)`, from the expansion identity of
`grid_expansion_all'`, has the following deterministic ingredients:
* initial term: `Step2.norm_Uker_le_of_tail`;
* drift: `weighted_duhamel_sum_le`, with `η_{u_j}⁻¹` **paired** with the propagator factor
  (`eta_inv_mul_weight_le`), so the time sum has weight `m⁻¹ R_k²`;
* remainder: `stopped_duhamel_det_bound` at `τ ≡ k`, with its forward-kernel hypothesis obtained
  by **enlarging `r`** to `((1-s)/(1-t))² stepErr_j` (`rsum_le`), and `Δ ≤ N^{-(2D+76)}`
  (explicit `C_R = 2D + 76`, `stepErr_sum_le`).

`Φg` (`RBM.Gauss.Grid.phiG'`) is Step 2's one-step bound at `v = u_k`, with `q_{u_k}` in the `q`
slot and `A^{-3/7}` in place of `A^{-1/3}`, `+ 1` (the `Y`-sum) `+ 1` (the remainder sum).

* `RBM.Gauss.Grid.phi_arith'` — the Step 2 arithmetic of the one-step bound with `q ≤ R^{3/2}`, same conclusion
  `≤ cStep m · x² R⁴`.  `qGrid_le`: `q_u ≤ 65 N^{3ζ} R_u^{3/2}`.
* `RBM.Gauss.Grid.jSMat_le_of_Agrid` — `jSMat` at the grid time is `jStar` of `‖A_k‖`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Finset MeasureTheory Filter Real
open scoped Matrix.Norms.L2Operator

section Defs

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- `q_u = (4 N^ζ ℓ_u/ℓ_s)³ + 1`. -/
noncomputable def qGrid (B : Band Ω') (s : ℕ → ℝ) (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (4 * (N : ℝ) ^ ζ * B.ell N u / B.ell N (s N)) ^ 3 + 1

end Defs

section GridFacts

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)

theorem step_nonneg' (hst : s N ≤ t N) : 0 ≤ step s t K N := by
  unfold step; exact div_nonneg (by linarith) (Nat.cast_nonneg _)

theorem time_eq (j : ℕ) : time s t K N j = s N + j * step s t K N := rfl

theorem time_succ' (j : ℕ) : time s t K N (j + 1) = time s t K N j + step s t K N := by
  simp only [time_eq]; push_cast; ring

theorem time_mono' (hst : s N ≤ t N) {i j : ℕ} (hij : i ≤ j) :
    time s t K N i ≤ time s t K N j := by
  simp only [time_eq]
  have := step_nonneg' s t K N hst
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

theorem K_mul_step (hK1 : 1 ≤ K N) : (K N : ℝ) * step s t K N = t N - s N := by
  unfold step
  have : (K N : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ K N := by exact_mod_cast hK1
                             linarith
  field_simp

theorem mul_step_le (hst : s N ≤ t N) (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) :
    (k : ℝ) * step s t K N ≤ t N - s N := by
  rw [← K_mul_step s t K N hK1]
  have : (k : ℝ) ≤ K N := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this (step_nonneg' s t K N hst)

theorem time_le_t (hst : s N ≤ t N) (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) :
    time s t K N k ≤ t N := by
  have := mul_step_le s t K N hst hK1 hk
  rw [time_eq]; linarith

theorem s_le_time (hst : s N ≤ t N) (k : ℕ) : s N ≤ time s t K N k := by
  have := time_mono' s t K N hst (Nat.zero_le k)
  rwa [time_zero] at this

end GridFacts

section Mono

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s : ℕ → ℝ} {N : ℕ}

theorem thr_nonneg (δ : ℝ) (u : ℝ) : 0 ≤ Step2.thr E s δ N u := by
  unfold Step2.thr
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)

theorem thr_mono (hE : |E| < 2) (δ : ℝ) {u v : ℝ} (hs1 : s N < 1) (huv : u ≤ v)
    (hv1 : v < 1) : Step2.thr E s δ N u ≤ Step2.thr E s δ N v := by
  have hu1 : u < 1 := huv.trans_lt hv1
  unfold Step2.thr
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (div_nonneg (Step2.etaT_pos' hE hs1).le (Step2.etaT_pos' hE hu1).le) ?_ 4)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Step2.etaT_ratio hE, Step2.etaT_ratio hE]
  exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

theorem scale_inv_mono (hE : |E| < 2) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) :
    (B.scale E N u)⁻¹ ≤ (B.scale E N v)⁻¹ := by
  have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have hAuv : B.scale E N v ≤ B.scale E N u := flowScale_antitoneOn hW0 (B.L N) E
    (Set.mem_Iic.2 (huv.trans hv1.le)) (Set.mem_Iic.2 hv1.le) huv
  exact inv_anti₀ (B.scale_pos' hE N (hu0.trans huv) hv1) hAuv

theorem qGrid_mono (ζ : ℝ) {u v : ℝ} (hs1 : s N < 1) (huv : u ≤ v) (hv1 : v < 1) :
    qGrid B s ζ N u ≤ qGrid B s ζ N v := by
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL1 (huv.trans_lt hv1)
  have hℓuv : B.ell N u ≤ B.ell N v := Step3.ellHat_mono huv hv1
  have hNz : 0 ≤ (N : ℝ) ^ ζ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold qGrid
  gcongr

theorem qGrid_nonneg (ζ u : ℝ) (hs1 : s N < 1) (hu1 : u < 1) : 0 ≤ qGrid B s ζ N u := by
  unfold qGrid
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL1 hu1
  have hNz : 0 ≤ (N : ℝ) ^ ζ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- **The η-pairing** (discrete): `η_{u_j}⁻¹ ((1-u_{j+1})/(1-u_k))²
≤ m⁻¹ (1-u_j)/(1-u_k)²`, because `1 - u_{j+1} ≤ 1 - u_j`. -/
theorem eta_inv_mul_weight_le (hE : |E| < 2) {uj uj1 uk : ℝ} (hj : uj ≤ uj1) (hj1 : uj1 ≤ uk)
    (hk1 : uk < 1) :
    (etaT E uj)⁻¹ * ((1 - uj1) / (1 - uk)) ^ 2 ≤ ((mE E).im)⁻¹ * ((1 - uj) / (1 - uk) ^ 2) := by
  have hm := mE_im_pos hE
  have h1k : 0 < 1 - uk := by linarith
  have h1j : 0 < 1 - uj := by linarith
  have h1j1 : 0 ≤ 1 - uj1 := by linarith
  rw [Step2.etaT_eq]
  rw [show ((1 - uj) * (mE E).im)⁻¹ * ((1 - uj1) / (1 - uk)) ^ 2
      = ((mE E).im)⁻¹ * ((1 - uj1) ^ 2 / ((1 - uj) * (1 - uk) ^ 2)) by
    field_simp]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm.le)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1 - uj1) ^ 2 ≤ (1 - uj) ^ 2 := pow_le_pow_left₀ h1j1 (by linarith) 2
  have hk2 : 0 < (1 - uk) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right this hk2.le]

end Mono

section Drift

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}
  {N : ℕ}

end Drift

section StepErr

/-- `∫ ‖X‖ ≤ 1 + E Tr X² = 1 + L W`. -/
theorem integral_norm_Xmat_le (d : Dims) (N : ℕ) :
    ∫ x, ‖Xmat d N x‖ ∂(P d) ≤ 1 + ((d.L N * d.W N : ℕ) : ℝ) := by
  have hint2 := integrable_frobSq_Xmat_pow d N 1 one_pos
  have hint : Integrable (fun x => 1 + frobSq (Xmat d N x ^ 1)) (P d) :=
    (integrable_const 1).add hint2
  calc ∫ x, ‖Xmat d N x‖ ∂(P d) ≤ ∫ x, (1 + frobSq (Xmat d N x ^ 1)) ∂(P d) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
          (Eventually.of_forall fun x => ?_)
        have h1 := l2_opNorm_sq_le_frobSq (Xmat d N x)
        simp only [pow_one]
        nlinarith [norm_nonneg (Xmat d N x), sq_nonneg (‖Xmat d N x‖ - 1)]
    _ = 1 + ((d.L N * d.W N : ℕ) : ℝ) := by
        rw [integral_add (integrable_const 1) hint2, integral_const, integral_frobSq_Xmat_one]
        simp

variable {L W : ℕ} {η Nr : ℝ} {m : Bool → ℂ}

theorem zMotionLip_le (hLW : (W : ℝ) * L ≤ Nr) (hη : 0 < η) (hηN : η⁻¹ ≤ Nr) (hNr : 1 ≤ Nr)
    (hm : max ‖m true‖ ‖m false‖ ≤ 1) : zMotionLip L W 2 η m ≤ 48 * Nr ^ 7 := by
  have h1 : 1 + η⁻¹ ≤ 2 * Nr := by linarith
  have hη0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hLW0 : (0 : ℝ) ≤ (W : ℝ) * L := by positivity
  calc zMotionLip L W 2 η m
      = 6 * max ‖m true‖ ‖m false‖ * ((W : ℝ) * L) ^ 2 * (1 + η⁻¹) ^ 3 * (η⁻¹) ^ 2 := by
        unfold zMotionLip; push_cast; ring
    _ ≤ 6 * 1 * Nr ^ 2 * (2 * Nr) ^ 3 * Nr ^ 2 := by gcongr
    _ = 48 * Nr ^ 7 := by ring

theorem zMotionZLip_le (hLW : (W : ℝ) * L ≤ Nr) (hη : 0 < η) (hηN : η⁻¹ ≤ Nr) (hNr : 1 ≤ Nr)
    (hm : max ‖m true‖ ‖m false‖ ≤ 1) : zMotionZLip L W 2 η m ≤ 192 * Nr ^ 7 := by
  have h1 : 1 + η⁻¹ ≤ 2 * Nr := by linarith
  have hη0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hLW0 : (0 : ℝ) ≤ (W : ℝ) * L := by positivity
  calc zMotionZLip L W 2 η m
      = 6 * max ‖m true‖ ‖m false‖ * ((W : ℝ) * L) ^ 2 * (1 + η⁻¹) ^ 5 := by
        unfold zMotionZLip; push_cast; ring
    _ ≤ 6 * 1 * Nr ^ 2 * (2 * Nr) ^ 5 := by gcongr
    _ = 192 * Nr ^ 7 := by ring

theorem driftLip_le (hLW : (W : ℝ) * L ≤ Nr) (hW1 : 1 ≤ W) (hη : 0 < η) (hηN : η⁻¹ ≤ Nr)
    (hNr : 1 ≤ Nr) (hm : max ‖m true‖ ‖m false‖ ≤ 1) :
    driftLip L W 2 η m ≤ 27648 * Nr ^ 14 := by
  have h1 : 1 + η⁻¹ ≤ 2 * Nr := by linarith
  have h2 : 1 + η⁻¹ + max ‖m true‖ ‖m false‖ ≤ 3 * Nr := by linarith
  have hη0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hLW4 : (L : ℝ) ^ 4 * (W : ℝ) ^ 3 ≤ Nr ^ 4 := by
    calc (L : ℝ) ^ 4 * (W : ℝ) ^ 3 ≤ (L : ℝ) ^ 4 * (W : ℝ) ^ 3 * W :=
          le_mul_of_one_le_right (by positivity) hW1'
      _ = ((W : ℝ) * L) ^ 4 := by ring
      _ ≤ Nr ^ 4 := pow_le_pow_left₀ (by positivity) hLW 4
  calc driftLip L W 2 η m
      = 48 * ((L : ℝ) ^ 4 * (W : ℝ) ^ 3) * (1 + η⁻¹ + max ‖m true‖ ‖m false‖) ^ 2 *
          (1 + η⁻¹) ^ 6 * (η⁻¹) ^ 2 := by
        unfold driftLip; push_cast; ring
    _ ≤ 48 * Nr ^ 4 * (3 * Nr) ^ 2 * (2 * Nr) ^ 6 * Nr ^ 2 := by gcongr
    _ = 27648 * Nr ^ 14 := by ring

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- The two uniform coefficients of `stepErr_le_unif` are polynomial in `N`. -/
theorem stepErrC_le (B : Band Ω') {E : ℝ} (hE : |E| < 2) {N : ℕ} {δ' : ℝ} (hδ' : 0 < δ')
    (hN1 : (1 : ℝ) ≤ N) (hWL : (B.W N : ℝ) * B.L N ≤ N) (hη : (δ' * (mE E).im)⁻¹ ≤ N) :
    stepErrC1 B E N δ' + stepErrC2 B E N δ' ≤ 2 ^ 17 * (N : ℝ) ^ 15 := by
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hη0 : 0 < δ' * (mE E).im := mul_pos hδ' hm0
  have hδinv : δ'⁻¹ ≤ N := by
    refine le_trans ?_ hη
    rw [mul_inv]
    exact le_mul_of_one_le_right (inv_nonneg.2 hδ'.le) (one_le_inv₀ hm0 |>.2 hm1)
  have hδinv0 : 0 ≤ δ'⁻¹ := inv_nonneg.2 hδ'.le
  have hmx : max ‖mSigma E true‖ ‖mSigma E false‖ ≤ 1 := by
    rw [norm_mSigma hE.le, norm_mSigma hE.le, max_self]
  have hW1 : 1 ≤ B.W N := B.W_pos N
  have hW1' : (1 : ℝ) ≤ B.W N := by exact_mod_cast hW1
  have hWinv : ((B.W N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1'
  have hWinv0 : 0 ≤ ((B.W N : ℝ))⁻¹ := by positivity
  have hZZ := zMotionZLip_le hWL hη0 hη hN1 hmx
  have hZL := zMotionLip_le hWL hη0 hη hN1 hmx
  have hDL := driftLip_le hWL hW1 hη0 hη hN1 hmx
  have hX := integral_norm_Xmat_le B.toDims N
  have hLWn : (((B.toDims.L N * B.toDims.W N : ℕ) : ℝ)) ≤ N := by
    have : ((B.toDims.L N * B.toDims.W N : ℕ) : ℝ) = (B.W N : ℝ) * B.L N := by
      simp only [Band.toDims_L, Band.toDims_W]; push_cast; ring
    rw [this]; exact hWL
  have hX2 : ∫ x, ‖Xmat B.toDims N x‖ ∂(P B.toDims) ≤ 2 * N := by linarith
  have hX0 : 0 ≤ ∫ x, ‖Xmat B.toDims N x‖ ∂(P B.toDims) :=
    integral_nonneg fun _ => norm_nonneg _
  have hp7 : (N : ℝ) ^ 7 ≤ (N : ℝ) ^ 14 := pow_le_pow_right₀ hN1 (by norm_num)
  have hp7' : (N : ℝ) ^ 7 ≤ (N : ℝ) ^ 15 := pow_le_pow_right₀ hN1 (by norm_num)
  have hp3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 7 := pow_le_pow_right₀ hN1 (by norm_num)
  have hp4 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 7 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN0 : (0 : ℝ) ≤ N := by linarith
  -- `C₁`
  have hC1 : stepErrC1 B E N δ' ≤ 103 * (N : ℝ) ^ 7 := by
    unfold stepErrC1
    rw [norm_mE hE.le]
    have t1 : (B.W N : ℝ)⁻¹ * δ'⁻¹ * δ'⁻¹ ^ 2 ≤ 1 * N * N ^ 2 := by gcongr
    have t2 : 3 * δ'⁻¹ ^ 2 * ((δ' * (mE E).im)⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ + (B.W N : ℝ)⁻¹ * δ'⁻¹)
        ≤ 3 * N ^ 2 * (N ^ 2 * 1 + 1 * N) := by
      have : 0 ≤ (δ' * (mE E).im)⁻¹ := inv_nonneg.2 hη0.le
      gcongr
    have t3 : (N : ℝ) * N ≤ N ^ 2 * N := by nlinarith
    nlinarith
  -- `C₂`
  have hC2 : stepErrC2 B E N δ' ≤ 65536 * (N : ℝ) ^ 15 := by
    unfold stepErrC2 genPtLip
    have hZL0 : 0 ≤ zMotionLip (B.L N) (B.W N) 2 (δ' * (mE E).im) (mSigma E) := by
      unfold zMotionLip; positivity
    have hDL0 : 0 ≤ driftLip (B.L N) (B.W N) 2 (δ' * (mE E).im) (mSigma E) := by
      unfold driftLip; positivity
    calc (zMotionLip (B.L N) (B.W N) 2 (δ' * (mE E).im) (mSigma E) + 2 / 3 *
          (driftLip (B.L N) (B.W N) 2 (δ' * (mE E).im) (mSigma E) +
            zMotionLip (B.L N) (B.W N) 2 (δ' * (mE E).im) (mSigma E))) *
          ∫ x, ‖Xmat B.toDims N x‖ ∂(P B.toDims)
        ≤ (48 * (N : ℝ) ^ 7 + 2 / 3 * (27648 * (N : ℝ) ^ 14 + 48 * (N : ℝ) ^ 7)) * (2 * N) := by
          gcongr
      _ ≤ (18512 * (N : ℝ) ^ 14) * (2 * N) := by gcongr; nlinarith
      _ = 37024 * (N : ℝ) ^ 15 := by ring
      _ ≤ 65536 * (N : ℝ) ^ 15 := by gcongr; norm_num
  nlinarith

/-- **The stepErr time sum**: `Σ_{j<k} stepErr_j ≤ 2¹⁷ N¹⁵ Δ^{1/2}`, from `stepErr_le_unif`
(`δ' = 1 - t`), `η_t⁻¹ ≤ N`, `W L ≤ N`, `k Δ ≤ 1`, `Δ ≤ 1`. -/
theorem stepErr_sum_le (B : Band Ω') {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N)
    (hN1 : (1 : ℝ) ≤ N) (hWL : (B.W N : ℝ) * B.L N ≤ N) (hηt : (etaT E (t N))⁻¹ ≤ N)
    (hΔ1 : step s t K N ≤ 1) :
    ∑ j ∈ Finset.range k, stepErr B E N (time s t K N j) (time s t K N (j + 1)) (step s t K N)
      ≤ 2 ^ 17 * (N : ℝ) ^ 15 * step s t K N ^ ((1 : ℝ) / 2) := by
  set Δ := step s t K N with hΔ
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t K N hst
  set δ' := 1 - t N with hδ'
  have hδ'0 : 0 < δ' := by linarith
  have hC1 : 0 ≤ stepErrC1 B E N δ' := by
    have hm0 := mE_im_pos hE
    have : 0 ≤ zMotionZLip (B.L N) (B.W N) 2 (δ' * (mE E).im) (mSigma E) := by
      have : 0 ≤ (δ' * (mE E).im)⁻¹ := inv_nonneg.2 (mul_pos hδ'0 hm0).le
      unfold zMotionZLip; positivity
    have : 0 ≤ δ'⁻¹ := inv_nonneg.2 hδ'0.le
    have : 0 ≤ (δ' * (mE E).im)⁻¹ := inv_nonneg.2 (mul_pos hδ'0 hm0).le
    unfold stepErrC1; positivity
  have hC2 : 0 ≤ stepErrC2 B E N δ' := by
    have hm0 := mE_im_pos hE
    have : 0 ≤ (δ' * (mE E).im)⁻¹ := inv_nonneg.2 (mul_pos hδ'0 hm0).le
    have hX0 : 0 ≤ ∫ x, ‖Xmat B.toDims N x‖ ∂(P B.toDims) :=
      integral_nonneg fun _ => norm_nonneg _
    unfold stepErrC2 genPtLip driftLip zMotionLip; positivity
  have hterm : ∀ j ∈ Finset.range k,
      stepErr B E N (time s t K N j) (time s t K N (j + 1)) Δ ≤
        stepErrC1 B E N δ' * Δ ^ 2 + stepErrC2 B E N δ' * Δ ^ (3 / 2 : ℝ) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    refine stepErr_le_unif B hE N hδ'0 (time_mono' s t K N hst (Nat.le_succ j)) ?_ hΔ0
    rw [hδ']; simp only [sub_sub_cancel]
    exact time_le_t s t K N hst hK1 (by omega)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    have := mul_step_le s t K N hst hK1 hk; linarith
  set r := Δ ^ ((1 : ℝ) / 2) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hΔ0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one hΔ0 hΔ1 (by norm_num)
  have hrr : Δ = r * r := by
    rw [hr, ← Real.rpow_add' hΔ0 (by norm_num)]; norm_num
  have h32 : Δ ^ (3 / 2 : ℝ) = Δ * r := by
    rw [hr, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hΔ0 (by norm_num),
      Real.rpow_one]
  have hΔr : Δ ≤ r := by rw [hrr]; nlinarith
  have hmain : (k : ℝ) * (stepErrC1 B E N δ' * Δ ^ 2 + stepErrC2 B E N δ' * Δ ^ (3 / 2 : ℝ))
      ≤ (stepErrC1 B E N δ' + stepErrC2 B E N δ') * r := by
    rw [h32]
    have e : (k : ℝ) * (stepErrC1 B E N δ' * Δ ^ 2 + stepErrC2 B E N δ' * (Δ * r))
        = ((k : ℝ) * Δ) * (stepErrC1 B E N δ' * Δ + stepErrC2 B E N δ' * r) := by ring
    rw [e]
    have hin : 0 ≤ stepErrC1 B E N δ' * Δ + stepErrC2 B E N δ' * r := by positivity
    calc ((k : ℝ) * Δ) * (stepErrC1 B E N δ' * Δ + stepErrC2 B E N δ' * r)
        ≤ 1 * (stepErrC1 B E N δ' * Δ + stepErrC2 B E N δ' * r) :=
          mul_le_mul_of_nonneg_right hkΔ hin
      _ ≤ (stepErrC1 B E N δ' + stepErrC2 B E N δ') * r := by
          have := mul_le_mul_of_nonneg_left hΔr hC1
          nlinarith
  refine hmain.trans ?_
  have hηδ : (δ' * (mE E).im)⁻¹ ≤ N := by rw [hδ']; exact hηt
  exact mul_le_mul_of_nonneg_right (stepErrC_le B hE hδ'0 hN1 hWL hηδ) hr0

end StepErr

section RSum

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}
  {N : ℕ}

/-- The forward kernel bound for a general `t < 1`: the row sums of `U(u_{j+1}, u_k)` are
`(1-u_{j+1})/(1-u_k) ≤ (1-s)/(1-t)`. -/
theorem norm_Uker_fwd_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {s t u v : ℝ} (hsu : s ≤ u)
    (huv : u ≤ v) (hv0 : 0 ≤ v) (hvt : v ≤ t) (ht1 : t < 1) {A : LoopArg L 2 → ℂ} {M : ℝ}
    (hM0 : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L 2) :
    ‖Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) A a‖ ≤ ((1 - s) / (1 - t)) ^ 2 * M := by
  have hv1 : v < 1 := hvt.trans_lt ht1
  have ht : ∀ i : Fin 2, ‖(v : ℂ) * (fun _ => (1 : ℂ)) i‖ < 1 := by
    intro i; simp [Complex.norm_real, abs_of_nonneg hv0, hv1]
  have hC : ∀ i : Fin 2, 1 + ‖((u : ℂ) - (v : ℂ)) * (fun _ => (1 : ℂ)) i‖ *
      (1 - ‖(v : ℂ) * (fun _ => (1 : ℂ)) i‖)⁻¹ ≤ (1 - s) / (1 - t) := by
    intro i
    have e1 : ‖((u : ℂ) - (v : ℂ)) * (fun _ => (1 : ℂ)) i‖ = v - u := by
      simp only [mul_one]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have e2 : ‖(v : ℂ) * (fun _ => (1 : ℂ)) i‖ = v := by
      simp [Complex.norm_real, abs_of_nonneg hv0]
    rw [e1, e2]
    have h1v : 0 < 1 - v := by linarith
    have e3 : 1 + (v - u) * (1 - v)⁻¹ = (1 - u) / (1 - v) := by field_simp; ring
    rw [e3]
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  exact norm_Uker_apply_le L hL ht hM0 hC hA a

/-- **The remainder sum**, via `stopped_duhamel_det_bound` at the fixed target
`τ ≡ k`, with its forward-kernel hypothesis `hFwd` obtained by **enlarging `r`** to
`r'_j = ((1-s)/(1-t))² stepErr_j`, and `hΔR : Δ ≤ N^{-(2D+76)}`. -/
theorem rsum_le (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) (hN2 : 2 ≤ N) (hWL : (B.W N : ℝ) * B.L N ≤ N)
    (hηt : (etaT E (t N))⁻¹ ≤ N) {D : ℝ} (hD0 : 0 ≤ D)
    (hΔR : step s t K N ≤ (N : ℝ) ^ (-(2 * D + 76)))
    (Rv : ℕ → LoopArg (B.L N) 2 → ℂ)
    (hRstep : ∀ j < k, ∀ b, ‖Rv j b‖ ≤
      stepErr B E N (time s t K N j) (time s t K N (j + 1)) (step s t K N))
    (a : LoopArg (B.L N) 2) :
    ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rv j)) a‖ ≤
      Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) := by
  classical
  set Δ := step s t K N with hΔ
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t K N hst
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hΔ1 : Δ ≤ 1 := hΔR.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  set u : ℕ → ℝ := fun j => time s t K N j with hudef
  have hsu : ∀ j, s N ≤ u j := fun j => s_le_time s t K N hst j
  have hu_succ : ∀ j, u j ≤ u (j + 1) := fun j => time_mono' s t K N hst (Nat.le_succ j)
  have hu0 : 0 ≤ u 0 := hs0.trans (hsu 0)
  have huk : u k ≤ t N := time_le_t s t K N hst hK1 hk
  have huk1 : u k < 1 := huk.trans_lt ht1
  set C := (1 - s N) / (1 - t N) with hC
  have h1t : 0 < 1 - t N := by linarith
  have hC1 : 1 ≤ C := by rw [hC, le_div_iff₀ h1t]; linarith
  set e : ℕ → ℝ := fun j => stepErr B E N (u j) (u (j + 1)) Δ with he
  have he0 : ∀ j < k, 0 ≤ e j := fun j hj =>
    (norm_nonneg _).trans (hRstep j hj (fun _ => 0))
  set r : ℕ → ℝ := fun j => if j < k then C ^ 2 * e j else 0 with hr
  have hr0 : ∀ j, 0 ≤ r j := by
    intro j; simp only [hr]; split_ifs with h
    · exact mul_nonneg (by positivity) (he0 j h)
    · exact le_rfl
  have hR : ∀ j (ω : Unit), j < (fun _ : Unit => k) ω → ∀ b, ‖Rv j b‖ ≤ r j := by
    intro j _ hj b
    simp only at hj
    simp only [hr, hj, ↓reduceIte]
    refine (hRstep j hj b).trans ?_
    exact le_mul_of_one_le_left (he0 j hj) (one_le_pow₀ hC1)
  have hFwd : ∀ j (ω : Unit), j < (fun _ : Unit => k) ω → ∀ a',
      ‖Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (Rv j) a'‖ ≤ 2 ^ 2 * r j := by
    intro j _ hj a'
    simp only at hj
    have hj1k : u (j + 1) ≤ u k := time_mono' s t K N hst (by omega)
    have hb := norm_Uker_fwd_le (B.L N) (B.three_le_L N) (hsu (j + 1)) hj1k
      (hs0.trans (hsu k)) huk ht1 (he0 j hj) (hRstep j hj) a'
    simp only [hr, hj, ↓reduceIte]
    have : 0 ≤ C ^ 2 * e j := mul_nonneg (by positivity) (he0 j hj)
    linarith
  have hmain := stopped_duhamel_det_bound (Ω' := Unit) (B.L N) (B.three_le_L N) (n := 2)
    (ξ := fun _ => (1 : ℂ)) (fun _ => by simp) (u := u) (t := u k) hu0 hu_succ (K := k) rfl
    huk1 (τ := fun _ => k) (fun _ => le_rfl) (fun j _ => Rv j) hr0 hR hFwd () a
  refine hmain.trans ?_
  have hsum : ∑ j ∈ Finset.range k, r j = C ^ 2 * ∑ j ∈ Finset.range k, e j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by simp only [hr, Finset.mem_range.mp hj, ↓reduceIte]
  rw [hsum]
  have hS := stepErr_sum_le B hE hs0 hst ht1 hK1 hk hN1 hWL hηt hΔ1
  -- `C ≤ N`
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hCN : C ≤ N := by
    refine le_trans ?_ hηt
    rw [hC, Step2.etaT_eq, mul_inv]
    calc (1 - s N) / (1 - t N) ≤ 1 / (1 - t N) := div_le_div_of_nonneg_right (by linarith) h1t.le
      _ = (1 - t N)⁻¹ * 1 := by rw [one_div, mul_one]
      _ ≤ (1 - t N)⁻¹ * ((mE E).im)⁻¹ :=
          mul_le_mul_of_nonneg_left (one_le_inv₀ hm0 |>.2 hm1) (inv_nonneg.2 h1t.le)
  set ρ := Δ ^ ((1 : ℝ) / 2) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hΔ0 _
  have hρN : ρ ≤ (N : ℝ) ^ (-(D + 38)) := by
    calc ρ ≤ ((N : ℝ) ^ (-(2 * D + 76))) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hΔ0 hΔR (by norm_num)
      _ = (N : ℝ) ^ (-(D + 38)) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have hS0 : 0 ≤ ∑ j ∈ Finset.range k, e j :=
    Finset.sum_nonneg fun j hj => he0 j (Finset.mem_range.mp hj)
  have h221 : (2 : ℝ) ^ 21 ≤ (N : ℝ) ^ 21 := pow_le_pow_left₀ (by norm_num) hN2' 21
  have hNpow : (N : ℝ) ^ 38 * (N : ℝ) ^ (-(D + 38)) = (N : ℝ) ^ (-D) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]; congr 1; push_cast; ring
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL1 : (1 : ℝ) ≤ B.L N := by exact_mod_cast B.one_le_L N
  have hWN : (B.W N : ℝ) ≤ N := le_trans (le_mul_of_one_le_right hW0.le hL1) hWL
  calc (2 : ℝ) ^ 2 * (2 ^ 2 * (C ^ 2 * ∑ j ∈ Finset.range k, e j))
      = 16 * C ^ 2 * ∑ j ∈ Finset.range k, e j := by ring
    _ ≤ 16 * (N : ℝ) ^ 2 * (2 ^ 17 * (N : ℝ) ^ 15 * ρ) := by
        gcongr
    _ = 2 ^ 21 * (N : ℝ) ^ 17 * ρ := by ring
    _ ≤ (N : ℝ) ^ 21 * (N : ℝ) ^ 17 * (N : ℝ) ^ (-(D + 38)) := by gcongr
    _ = (N : ℝ) ^ 38 * (N : ℝ) ^ (-(D + 38)) := by ring
    _ = (N : ℝ) ^ (-D) := hNpow
    _ ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    _ ≤ Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) := rpow_neg_le_tailT _

end RSum

section StepBound

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}
  {N : ℕ}

end StepBound

section Arith

/-- **`phi_arith'`**: the Step 2 arithmetic of the one-step bound with `hq : q ≤ R^{3/2}` in place of `q ≤ R`, and
the **same conclusion** `≤ cStep m · x² R⁴` (the `q`-term is now `≤ m⁻¹ x² R^{7/2} ≤ m⁻¹ x² R⁴`). -/
theorem phi_arith' {x R Ξ m A ε q α : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (hΞ : Ξ ≤ x)
    (hm0 : 0 < m) (hA : x ^ 17 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε) (hε : ε * x ^ 17 * R ^ 10 ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ R ^ ((3 : ℝ) / 2)) (hα0 : 0 ≤ α) (hα : α * (x ^ 24 * R ^ 10) ≤ 1) :
    x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + α * (x ^ 8 * R ^ 4) ^ 3)) + x * (R ^ 2 + 1) + 1
      ≤ Step2.cStep m * x ^ 2 * R ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hxA : x ^ 17 * R ^ 10 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hA
  have hΞ0 : 0 ≤ Ξ ∨ Ξ < 0 := le_or_gt 0 Ξ
  have hR32 : R ^ ((3 : ℝ) / 2) ≤ R ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (3 : ℝ) / 2 ≤ 2)
    rwa [Real.rpow_two] at this
  have hq2 : q ≤ R ^ 2 := hq.trans hR32
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 4 := by
    rcases hΞ0 with h | h
    · calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
        _ = x ^ 2 * R ^ 2 := by ring
        _ ≤ x ^ 2 * R ^ 4 := by gcongr
    · have : x * R ^ 2 * Ξ ≤ 0 := by
        have : 0 ≤ x * R ^ 2 := by positivity
        nlinarith
      nlinarith
  rcases hΞ0 with hΞ0 | hΞneg
  · have t2 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by
      calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
          = 36 * exp 1 * m⁻¹ * (Ξ * x ^ 16 * R ^ 10 * A⁻¹) := by ring
        _ ≤ 36 * exp 1 * m⁻¹ * (x * x ^ 16 * R ^ 10 * A⁻¹) := by gcongr
        _ = 36 * exp 1 * m⁻¹ * (x ^ 17 * R ^ 10 * A⁻¹) := by ring
        _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
        _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by gcongr
    have t3 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) ≤ exp 1 * (x ^ 2 * R ^ 4) := by
      calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε))
          = exp 1 * (Ξ * x ^ 16 * R ^ 10 * ε) := by ring
        _ ≤ exp 1 * (x * x ^ 16 * R ^ 10 * ε) := by gcongr
        _ = exp 1 * (ε * x ^ 17 * R ^ 10) := by ring
        _ ≤ exp 1 * 1 := by gcongr
        _ ≤ exp 1 * (x ^ 2 * R ^ 4) := by gcongr
    -- the only changed term: `q ≤ R^{3/2}` gives `R² q ≤ R^{7/2} ≤ R⁴`
    have t4 : Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
      calc Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ x * (x * m⁻¹ * R ^ 2 * R ^ 2) := by gcongr
        _ = m⁻¹ * (x ^ 2 * R ^ 4) := by ring
    have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3)) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
      calc Ξ * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3))
          ≤ x * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3)) := by gcongr
        _ = m⁻¹ * (x ^ 2 * R ^ 4) * (α * (x ^ 24 * R ^ 10)) := by ring
        _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) * 1 := by gcongr
        _ = m⁻¹ * (x ^ 2 * R ^ 4) := mul_one _
    have t6 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 4) := by nlinarith
    have hsplit : x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 *
          (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) + x * m⁻¹ * R ^ 2 * (q + α * (x ^ 8 * R ^ 4) ^ 3))
          + x * (R ^ 2 + 1) + 1
        = x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
          + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) + Ξ * (x * m⁻¹ * R ^ 2 * q)
          + Ξ * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3)) + x * (R ^ 2 + 1) + 1 := by ring
    rw [hsplit, Step2.cStep]
    nlinarith
  · -- `Ξ < 0`: every `Ξ`-term is `≤ 0`
    have hB : 0 ≤ exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * m⁻¹ * R ^ 2 * (q + α * (x ^ 8 * R ^ 4) ^ 3) := by positivity
    have h1 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * m⁻¹ * R ^ 2 * (q + α * (x ^ 8 * R ^ 4) ^ 3)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hΞneg.le hB
    have t6 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 4) := by nlinarith
    rw [Step2.cStep]
    have : 0 ≤ (36 * exp 1 + 2) * m⁻¹ * (x ^ 2 * R ^ 4) := by positivity
    nlinarith

/-- `q_u ≤ 65 N^{3ζ} R_u^{3/2}` (`ℓ_u/ℓ_s ≤ R_u^{1/2}`, `Step3.ellHat_le_sqrt_mul`). -/
theorem qGrid_le {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} (hE : |E| < 2)
    {s : ℕ → ℝ} {N : ℕ} (hN1 : 1 ≤ N) {ζ : ℝ} (hζ : 0 ≤ ζ) {u : ℝ} (hsu : s N ≤ u)
    (hu1 : u < 1) :
    qGrid B s ζ N u ≤ 65 * (N : ℝ) ^ (3 * ζ) * (etaT E (s N) / etaT E u) ^ ((3 : ℝ) / 2) := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL1 hu1
  set R := etaT E (s N) / etaT E u with hR
  have hRe : R = (1 - s N) / (1 - u) := Step2.etaT_ratio hE _ _
  have h1u : 0 < 1 - u := by linarith
  have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1u]; linarith
  have hR0 : 0 ≤ R := by linarith
  set y := B.ell N u / B.ell N (s N) with hy
  have hy0 : 0 ≤ y := div_nonneg hℓu.le hℓs.le
  have hyR : y ≤ R ^ ((1 : ℝ) / 2) := by
    have h := Step3.ellHat_le_sqrt_mul (L := B.L N) hsu hu1
    rw [hy, div_le_iff₀ hℓs, hRe, ← Real.sqrt_eq_rpow]; exact h
  have hy3 : y ^ 3 ≤ R ^ ((3 : ℝ) / 2) := by
    calc y ^ 3 ≤ (R ^ ((1 : ℝ) / 2)) ^ 3 := pow_le_pow_left₀ hy0 hyR 3
      _ = R ^ ((3 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hR0]; norm_num
  have hNz : ((N : ℝ) ^ ζ) ^ 3 = (N : ℝ) ^ (3 * ζ) := by
    rw [Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hN3 : 1 ≤ (N : ℝ) ^ (3 * ζ) := Real.one_le_rpow hN1' (by positivity)
  have hR3 : 1 ≤ R ^ ((3 : ℝ) / 2) := Real.one_le_rpow hR1 (by norm_num)
  have hq : qGrid B s ζ N u = 64 * (N : ℝ) ^ (3 * ζ) * y ^ 3 + 1 := by
    unfold qGrid
    rw [← hNz, hy]; ring
  rw [hq]
  have h1 : 1 ≤ (N : ℝ) ^ (3 * ζ) * R ^ ((3 : ℝ) / 2) := one_le_mul_of_one_le_of_one_le hN3 hR3
  have h2 : 64 * (N : ℝ) ^ (3 * ζ) * y ^ 3 ≤ 64 * (N : ℝ) ^ (3 * ζ) * R ^ ((3 : ℝ) / 2) := by
    gcongr
  nlinarith

end Arith

section Improve

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}

/-- `jSMat` at the grid time is `jStar` of `‖A_k‖`. -/
theorem jSMat_le_of_Agrid {N k : ℕ} {ω : Ωg B.toDims} {D c : ℝ}
    (h : ∀ a, ‖Agrid B E s t K N k ω a‖ ≤
      c * Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1))) :
    jSMat B.toDims E D N (time s t K N k) (H B.toDims s t K N k ω) ≤ c + 1 := by
  have hW0 : (0 : ℝ) < (B.toDims.W N : ℝ) := by exact_mod_cast B.W_pos N
  unfold jSMat
  refine Step2.jStar_le hW0 (fun a => ?_)
  have hidx : LoopData.idx (Step2.sigPM, a)
      = (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) := by
    have hσ : List.ofFn (Step2.sigPM) = [true, false] := by
      change List.ofFn (![true, false] : Fin 2 → Bool) = [true, false]
      simp [List.ofFn_succ]
    unfold LoopData.idx
    rw [hσ]
    rfl
  have ha := h a
  unfold Agrid Lval Kv at ha
  rw [hidx]
  exact ha

end Improve

section Witness

end Witness

end RBM.Gauss.Grid

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridSharp47
import RBM1D.Gauss.GridFarMart
import RBM1D.Gauss.GridFarLift
import RBM1D.Gauss.QVEndpoint

/-!
# Pass 2: the deterministic ingredients of the far closure

The far closure bounds `A_k` at an arbitrary grid index `k`, at every far label
`6ℓ*_{u_k} < d_a`, by `‖A_k(a)‖ ≤ 6 N^{δ/4} T_{u_k, D-5}(a)`, from the Duhamel identity, the
initial datum, the split drift of `GridDriftSplit.lean` at the far level `Λ = thrFar`, the far
martingale, `Y` and `R`, all at the grid order `D`.  The output order `D - 5` absorbs the (7.2)
remainder `Mi m⁻² (η_s/η_{u_k})² W^{-D}`.  This file supplies the deterministic ingredients.

## Route

The initial term uses (7.2) in the form `norm_Uker_tail_le_sigma` (KernelDecay), not
`norm_Uker_le_of_tail`; see `FarClosure.init_far_le`. The drift `D_j` is split
pointwise at the near band `d_b ≤ ℓ*_{u_j}`:
* the near-band part (carrying `drNear` and the `ρ`-residue) reaches the far label only through
  `QVEndpoint.weightedKernel_supp_far_le` (`FarClosure.near_leak_le`);
* the far part is bounded by `drFar` alone (`FarClosure.coefFar_le`) and summed through
  `Sharp47.drift_sum_split` with zero near coefficient.

No `driftCoef'` is used. `Step2.thr` appears only as the comparison level `thrFar ≤ thr` (and in
the quadratic term of `drFar`); it is never a localisation.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM Finset
open scoped NNReal ENNReal Matrix.Norms.L2Operator

namespace FarClosure

/-! ### The initial term: Lemma 7.2 (7.2) in the far field -/

/-- **Initial term, far field, (7.2) form.** If `‖A_b‖ ≤ Mi T_{u,D}(b)` (with `η = (1-u)m`), then
at every label with `ℓ*_v ≤ d_a`:
`‖U_{u,v}A(a)‖ ≤ Mi Ξ T_{v,D}(a) + Mi m⁻² ((1-u)/(1-v))² W^{-D}`.
Proof: `norm_Uker_tail_le_sigma` applied to `A / (Mi m⁻²)`. The main part carries **no**
`(η_u/η_v)²`; only the `W^{-D}` remainder does. -/
theorem init_far_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {u v : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) {W D Mi : ℝ} (hW : Real.exp 1 ≤ W)
    (hMi : 0 ≤ Mi) {A : LoopArg L 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤
      Mi * tailT W (ellHat L (u : ℂ)) ((1 - u) * (mE E).im) D (zdist L (b 0 - b 1)))
    (a : LoopArg L 2) (hd : ellStar W (ellHat L (v : ℂ)) ≤ (zdist L (a 0 - a 1) : ℝ)) :
    ‖Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a‖ ≤
      Mi * Step2.xiK L W (mE E).im *
          tailT W (ellHat L (v : ℂ)) ((1 - v) * (mE E).im) D (zdist L (a 0 - a 1))
        + Mi * ((mE E).im ^ 2)⁻¹ * ((1 - u) / (1 - v)) ^ 2 * W ^ (-D) := by
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  set m := (mE E).im with hm
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hL1 : 1 ≤ L := by omega
  have hu1 : u < 1 := huv.trans_lt hv1
  have hv0 : 0 ≤ v := hu0.trans huv
  have hℓu : 1 ≤ ellHat L (u : ℂ) := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hℓv : 1 ≤ ellHat L (v : ℂ) := one_le_ellHat_of_nonneg hL1 hv0 hv1
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hε : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hX := Step2.xiK_nonneg L W m
  have hcT := cTail_nonneg
  have hxi1 : cTail * (1 + 2 * L * Real.exp (-(Real.log W ^ (3 / 2 : ℝ) / 8))) ≤
      Step2.xiK L W m := by
    unfold Step2.xiK
    have := Real.exp_pos (Real.log W ^ (3 / 4 : ℝ))
    have : 0 ≤ (m ^ 2)⁻¹ := by positivity
    linarith
  by_cases hM0 : Mi = 0
  · have hA0 : A = 0 := by
      funext b
      have := hA b
      rw [hM0, zero_mul] at this
      simpa using norm_le_zero_iff.1 this
    have : Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a = 0 := by
      simp [Uker_apply, hA0]
    rw [this, norm_zero, hM0]
    simp
  have hMpos : 0 < Mi := lt_of_le_of_ne hMi (Ne.symm hM0)
  set c : ℝ := Mi * (m ^ 2)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  set A' : LoopArg L 2 → ℂ := ((c : ℂ)⁻¹) • A with hA'def
  have hAA' : A = (c : ℂ) • A' := by
    rw [hA'def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hcpos.ne'), one_smul]
  have hA' : ∀ b, ‖A' b‖ ≤ tailT W (ellHat L (u : ℂ)) (1 - u) D (zdist L (b 0 - b 1)) := by
    intro b
    have hb := hA b
    have hnc : ‖((c : ℂ)⁻¹)‖ = c⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    rw [hA'def, Pi.smul_apply, smul_eq_mul, norm_mul, hnc]
    rw [inv_mul_le_iff₀ hcpos]
    refine hb.trans ?_
    unfold tailT
    set e := Real.exp (-√((zdist L (b 0 - b 1) : ℝ) / ellHat L (u : ℂ)))
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have hm2 : 0 < m ^ 2 := by positivity
    have hm21 : m ^ 2 ≤ 1 := by nlinarith
    have e1 : ((W * ellHat L (u : ℂ) * ((1 - u) * m)) ^ 2)⁻¹
        = (m ^ 2)⁻¹ * ((W * ellHat L (u : ℂ) * (1 - u)) ^ 2)⁻¹ := by
      rw [← mul_inv]; congr 1; ring
    rw [e1, hc]
    have hP : 0 ≤ ((W * ellHat L (u : ℂ) * (1 - u)) ^ 2)⁻¹ := by positivity
    have hmi : 1 ≤ (m ^ 2)⁻¹ := one_le_inv₀ hm2 |>.2 hm21
    nlinarith [mul_le_mul_of_nonneg_left hmi (mul_nonneg hMpos.le hε)]
  have key := norm_Uker_tail_le_sigma L hL hE.le hu0 huv hv0 hv1 hW hA' a hd
  rw [xiOf_mSigma_true_false hE.le] at key
  have hU : Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a
      = (c : ℂ) * Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A' a := by
    rw [hAA', Uker_smul]; rfl
  rw [hU, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
  set X := cTail * (1 + 2 * L * Real.exp (-(Real.log W ^ (3 / 2 : ℝ) / 8))) with hXdef
  set e := Real.exp (-√((zdist L (a 0 - a 1) : ℝ) / ellHat L (v : ℂ))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set Av := W * ellHat L (v : ℂ) * ((1 - v) * m) with hAv
  have hAv0 : 0 < Av := by positivity
  have hPv : ((W * ellHat L (v : ℂ) * (1 - v)) ^ 2)⁻¹ = m ^ 2 * (Av ^ 2)⁻¹ := by
    rw [hAv]; field_simp
  have hTveq : tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (a 0 - a 1))
      = (Av ^ 2)⁻¹ * e + W ^ (-D) := rfl
  have hQ : 0 ≤ (Av ^ 2)⁻¹ := by positivity
  have hX0 : 0 ≤ X := by positivity
  calc c * ‖Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A' a‖
      ≤ c * (X * (((W * ellHat L (v : ℂ) * (1 - v)) ^ 2)⁻¹ * e)
          + ((1 - u) / (1 - v)) ^ 2 * W ^ (-D)) :=
        mul_le_mul_of_nonneg_left key hcpos.le
    _ = Mi * (X * ((Av ^ 2)⁻¹ * e)) + Mi * (m ^ 2)⁻¹ * ((1 - u) / (1 - v)) ^ 2 * W ^ (-D) := by
        rw [hPv, hc]; field_simp
    _ ≤ Mi * (Step2.xiK L W m * tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
            (zdist L (a 0 - a 1)))
          + Mi * (m ^ 2)⁻¹ * ((1 - u) / (1 - v)) ^ 2 * W ^ (-D) := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ hMi) le_rfl
        rw [hTveq]
        exact mul_le_mul hxi1 (le_add_of_nonneg_right hε) (mul_nonneg hQ he0) hX
    _ = _ := by ring

/-! ### The drift coefficients -/

/-- **The far drift coefficient at a level `Λ ≤ thr(v)`**, `s N ≤ u ≤ v < 1`: the unmerged far
part of (5.35) at the jG-level `N^{2ε}Λ ≤ N^{2ε} thr(v)` and the quadratic term, with every
constant evaluated at `v` (monotonicity), as in `Sharp47.coef_le` but **without** the
near part. -/
theorem coefFar_le {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s : ℕ → ℝ}
    {N : ℕ} (hE : |E| < 2) {δ D Λ : ℝ} (hs0 : 0 ≤ s N) {u v : ℝ} (hsu : s N ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hW1 : (1 : ℝ) ≤ B.W N) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ Step2.thr E s δ N v) :
    drFar B E s δ (δ / 4) (δ / 96) D Λ N u ≤
      (Lemma57.cFar (B.W N : ℝ) 1 *
            (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) ^ ((3 : ℝ) / 2) *
            (√(B.scale E N v))⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v)
          + 169 * (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) * (B.scale E N v)⁻¹ *
            ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v) ^ ((3 : ℝ) / 2)
          + Real.exp 1 * Step2.thr E s δ N v ^ 2 * 36 * (B.scale E N v)⁻¹) * (etaT E u)⁻¹
        + Real.exp 1 * Step2.thr E s δ N v ^ 2 *
            ((B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D)) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1 hs0 hs1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hℓuv : B.ell N u ≤ B.ell N v := Step3.ellHat_mono huv hv1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hηu0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu.le
  have hAu0 : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
  have hAv0 : 0 < B.scale E N v := B.scale_pos' hE N (hu0.trans huv) hv1
  have hAvu : B.scale E N v ≤ B.scale E N u := flowScale_antitoneOn (Nat.cast_nonneg _) (B.L N) E
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 hv1.le) huv
  have hAinv : (B.scale E N u)⁻¹ ≤ (B.scale E N v)⁻¹ := inv_anti₀ hAv0 hAvu
  have hsqinv : (√(B.scale E N u))⁻¹ ≤ (√(B.scale E N v))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hAv0) (Real.sqrt_le_sqrt hAvu)
  have hNe0 : 0 ≤ (N : ℝ) ^ (2 * (δ / 4)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hthruv : Step2.thr E s δ N u ≤ Step2.thr E s δ N v := thr_mono hE δ hs1 huv hv1
  have hthru0 : 0 ≤ Step2.thr E s δ N u := thr_nonneg δ u
  set Ju := (N : ℝ) ^ (2 * (δ / 4)) * Λ with hJudef
  set Jv := (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v with hJvdef
  have hJuv : Ju ≤ Jv := mul_le_mul_of_nonneg_left hΛ hNe0
  have hJu0 : 0 ≤ Ju := mul_nonneg hNe0 hΛ0
  set ru := 4 * (N : ℝ) ^ (δ / 96) * B.ell N u / B.ell N (s N) with hrudef
  set rv := 4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N) with hrvdef
  have hNz0 : 0 ≤ (N : ℝ) ^ (δ / 96) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hru0 : 0 ≤ ru := div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  have hruv : ru ≤ rv :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hℓuv (by positivity)) (by linarith)
  set cF1 := Lemma57.cFar (B.W N : ℝ) 1 with hcF1
  have hcF1_0 : 0 ≤ cF1 := Lemma57.cFar_nonneg hW1 one_pos
  set εW := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hεW
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hεW0 : 0 ≤ εW := by have := Real.rpow_nonneg hW0.le (-D); positivity
  have hF1 : Lemma57.cFar (B.W N : ℝ) (B.ell N u) * ru ^ ((3 : ℝ) / 2) *
      (√(B.scale E N u))⁻¹ * Ju ≤ cF1 * rv ^ ((3 : ℝ) / 2) * (√(B.scale E N v))⁻¹ * Jv := by
    have hc := Step2FarInputs.cFar_le_cFar_one hW1 hℓu1
    have hr32 : ru ^ ((3 : ℝ) / 2) ≤ rv ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hru0 hruv (by norm_num)
    have hr320 : 0 ≤ ru ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hru0 _
    have hsq0 : 0 ≤ (√(B.scale E N u))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hrv32 : 0 ≤ rv ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (hru0.trans hruv) _
    have hsqv0 : 0 ≤ (√(B.scale E N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    exact mul_le_mul (mul_le_mul (mul_le_mul hc hr32 hr320 hcF1_0) hsqinv hsq0
            (mul_nonneg hcF1_0 hrv32)) hJuv hJu0 (mul_nonneg (mul_nonneg hcF1_0 hrv32) hsqv0)
  have hF2 : 169 * ru * (B.scale E N u)⁻¹ * Ju ^ ((3 : ℝ) / 2) ≤
      169 * rv * (B.scale E N v)⁻¹ * Jv ^ ((3 : ℝ) / 2) := by
    have hJ32 : Ju ^ ((3 : ℝ) / 2) ≤ Jv ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hJu0 hJuv (by norm_num)
    have hAi0 : 0 ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 hAu0.le
    have hrv0 : 0 ≤ rv := hru0.trans hruv
    have hJ320 : 0 ≤ Ju ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hJu0 _
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hruv (by norm_num)) hAinv hAi0
            (by positivity)) hJ32 hJ320 (by positivity)
  have hQ1 : Real.exp 1 * Step2.thr E s δ N u ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹)) ≤
      Real.exp 1 * Step2.thr E s δ N v ^ 2 * 36 * (B.scale E N v)⁻¹ * (etaT E u)⁻¹ := by
    have ht2 : Step2.thr E s δ N u ^ 2 ≤ Step2.thr E s δ N v ^ 2 :=
      pow_le_pow_left₀ hthru0 hthruv 2
    have hAi0 : 0 ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 hAu0.le
    calc Real.exp 1 * Step2.thr E s δ N u ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹))
        ≤ Real.exp 1 * Step2.thr E s δ N v ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N v)⁻¹)) := by
          gcongr
      _ = _ := by ring
  have hQ2 : Real.exp 1 * Step2.thr E s δ N u ^ 2 * εW ≤
      Real.exp 1 * Step2.thr E s δ N v ^ 2 * εW := by
    have ht2 : Step2.thr E s δ N u ^ 2 ≤ Step2.thr E s δ N v ^ 2 :=
      pow_le_pow_left₀ hthru0 hthruv 2
    gcongr
  unfold drFar
  rw [← hJudef, ← hrudef, ← hεW]
  have h12 := mul_le_mul_of_nonneg_left (add_le_add hF1 hF2) hηu0
  refine (le_of_eq ?_).trans ((add_le_add h12 (add_le_add hQ1 hQ2)).trans (le_of_eq ?_))
  all_goals ring

/-- The near drift coefficient is polynomially bounded: `drNear ≤ 64 N⁸`. -/
theorem drNear_le {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s : ℕ → ℝ}
    {N : ℕ} (hE : |E| < 2) {δ : ℝ} (hδ1 : δ ≤ 1) (hs0 : 0 ≤ s N) {u : ℝ}
    (hsu : s N ≤ u)
    (hu1 : u < 1) (hN1 : (1 : ℝ) ≤ N) (hW1 : (1 : ℝ) ≤ B.W N) (hLN : (B.L N : ℝ) ≤ N)
    (hηu : (etaT E u)⁻¹ ≤ N) (hcN : Lemma57.cNear (B.W N : ℝ) 1 ≤ N) :
    drNear B E s (δ / 96) N u ≤ 64 * (N : ℝ) ^ 8 := by
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1 hs0 hs1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hℓuL : B.ell N u ≤ (B.L N : ℝ) := by
    simp only [Band.ell, ellHat]; exact min_le_right _ _
  have hηu0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (Step2.etaT_pos' hE hu1).le
  have hcu : Lemma57.cNear (B.W N : ℝ) (B.ell N u) ≤ Lemma57.cNear (B.W N : ℝ) 1 :=
    Step2FarInputs.cNear_le_cNear_one hW1 hℓu1
  have hcu0 : 0 ≤ Lemma57.cNear (B.W N : ℝ) (B.ell N u) :=
    Lemma57.cNear_nonneg hW1 (by linarith)
  have hNz : (N : ℝ) ^ (δ / 96) ≤ N := by
    calc (N : ℝ) ^ (δ / 96) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  have hNz0 : 0 ≤ (N : ℝ) ^ (δ / 96) := Real.rpow_nonneg (by linarith) _
  have hr0 : 0 ≤ 4 * (N : ℝ) ^ (δ / 96) * B.ell N u / B.ell N (s N) := by positivity
  have hr : 4 * (N : ℝ) ^ (δ / 96) * B.ell N u / B.ell N (s N) ≤ 4 * (N : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    calc 4 * (N : ℝ) ^ (δ / 96) * B.ell N u ≤ 4 * N * N := by gcongr; linarith
      _ = 4 * (N : ℝ) ^ 2 * 1 := by ring
      _ ≤ 4 * (N : ℝ) ^ 2 * B.ell N (s N) := by gcongr
  unfold drNear
  calc (etaT E u)⁻¹ * Lemma57.cNear (B.W N : ℝ) (B.ell N u) *
        (4 * (N : ℝ) ^ (δ / 96) * B.ell N u / B.ell N (s N)) ^ 3
      ≤ N * N * (4 * (N : ℝ) ^ 2) ^ 3 := by
        refine mul_le_mul (mul_le_mul hηu (hcu.trans hcN) hcu0 (by linarith))
          (pow_le_pow_left₀ hr0 hr 3) (pow_nonneg hr0 3) (by positivity)
    _ = 64 * (N : ℝ) ^ 8 := by ring

/-- The `ρ`-residue at a level `Λ` with `N^{2ε}Λ ≤ N⁶`: `drRes ≤ 8 N^{-20} η_u⁻¹` (the residue
step of `Sharp47.coef_le`, at a general level). -/
theorem drRes_le {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s : ℕ → ℝ}
    {N : ℕ} (hE : |E| < 2) {δ D Λ : ℝ} (hδ1 : δ ≤ 1) (hs0 : 0 ≤ s N) {u : ℝ}
    (hsu : s N ≤ u) (hu1 : u < 1) (hN1 : (1 : ℝ) ≤ N) (hW1 : (1 : ℝ) ≤ B.W N)
    (hLN : (B.L N : ℝ) ≤ N) (hηu : (etaT E u)⁻¹ ≤ N)
    (hWD : (B.W N : ℝ) ^ (-D) ≤ ((N : ℝ) ^ 32)⁻¹)
    (hex : Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) ≤ N) (hAu : B.scale E N u ≤ N)
    (hΛ0 : 0 ≤ Λ) (hJ : (N : ℝ) ^ (2 * (δ / 4)) * Λ ≤ (N : ℝ) ^ 6) :
    drRes B E s (δ / 96) N u
        (2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Λ) * (B.W N : ℝ) ^ (-D))
      ≤ 8 * ((N : ℝ) ^ 20)⁻¹ * (etaT E u)⁻¹ := by
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1 hs0 hs1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hηu0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu.le
  have hAu0 : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
  have hW0 : (0 : ℝ) < B.W N := by linarith
  set Ju := (N : ℝ) ^ (2 * (δ / 4)) * Λ with hJudef
  have hJu0 : 0 ≤ Ju := mul_nonneg (Real.rpow_nonneg hN0.le _) hΛ0
  set ρ := 2 * (etaT E u)⁻¹ * Ju * (B.W N : ℝ) ^ (-D) with hρ
  have hℓu0 : B.ell N u ≠ 0 := by linarith
  have hηne : etaT E u ≠ 0 := hηu.ne'
  have e : drRes B E s (δ / 96) N u ρ = (etaT E u)⁻¹ *
      (4 * (N : ℝ) ^ (δ / 96) * (B.ell N (s N))⁻¹ * (B.L N : ℝ) * ρ *
        (Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2)) := by
    unfold drRes
    field_simp
  rw [e, mul_comm (8 * ((N : ℝ) ^ 20)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ hηu0
  have hNz : (N : ℝ) ^ (δ / 96) ≤ N := by
    calc (N : ℝ) ^ (δ / 96) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  have hℓsi : (B.ell N (s N))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓs1
  have hℓsi0 : 0 ≤ (B.ell N (s N))⁻¹ := inv_nonneg.2 (by linarith)
  have hWD0 : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hρ0 : 0 ≤ ρ := by positivity
  have hρle : ρ ≤ 2 * N * (N : ℝ) ^ 6 * ((N : ℝ) ^ 32)⁻¹ := by
    calc ρ = 2 * (etaT E u)⁻¹ * Ju * (B.W N : ℝ) ^ (-D) := rfl
      _ ≤ 2 * N * (N : ℝ) ^ 6 * ((N : ℝ) ^ 32)⁻¹ := by gcongr
  have hexA : Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2 ≤
      N * (N : ℝ) ^ 2 :=
    mul_le_mul hex (pow_le_pow_left₀ hAu0.le hAu 2) (by positivity) hN0.le
  have hNz0 : 0 ≤ (N : ℝ) ^ (δ / 96) := Real.rpow_nonneg hN0.le _
  calc 4 * (N : ℝ) ^ (δ / 96) * (B.ell N (s N))⁻¹ * (B.L N : ℝ) * ρ *
        (Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2)
      ≤ 4 * N * 1 * N * (2 * N * (N : ℝ) ^ 6 * ((N : ℝ) ^ 32)⁻¹) * (N * (N : ℝ) ^ 2) := by
        gcongr
    _ = 8 * ((N : ℝ) ^ 20)⁻¹ := by field_simp; ring

/-- `T_{u,D}(d) ≤ 2` once `scale(u) ≥ 1`, `W ≥ 1`, `D ≥ 0`. -/
theorem tT_le_two {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {N : ℕ}
    {D u d : ℝ} (hD : 0 ≤ D) (hW1 : (1 : ℝ) ≤ B.W N) (hA : 1 ≤ B.scale E N u) :
    Step2.tT B E N D u d ≤ 2 := by
  unfold Step2.tT tailT
  have hA' : (1 : ℝ) ≤ (B.W N : ℝ) * B.ell N u * etaT E u := hA
  have h1 : (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hA')
  have h2 : Real.exp (-√(d / B.ell N u)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
  have h3 : (B.W N : ℝ) ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have h0 : 0 ≤ (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ := by positivity
  have := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
  linarith

/-! ### (5.35)-far closures with the extra `R²` (pass 2) -/

/-- (5.35)-far term 1, pass 2:
`(Ξ P₁ R²)² ≤ 64 Ξ² c_F² z³ x^{24} R^{14} / A ≤ x^{32}R^{14}/A ≤ 1`. -/
theorem far1R_le {Ξ cF z r R A x J : ℝ} (hΞ : 0 ≤ Ξ) (hcF : 0 ≤ cF) (hr0 : 0 ≤ r)
    (hr3 : r ^ 3 ≤ 64 * z ^ 3 * R ^ 2) (hA : 0 < A) (hx1 : 1 ≤ x) (hR1 : 1 ≤ R)
    (hJ : J = x ^ 12 * R ^ 4) (hxA : x ^ 48 * R ^ 20 ≤ A)
    (hC : 64 * Ξ ^ 2 * cF ^ 2 * z ^ 3 ≤ x ^ 8) :
    Ξ * (cF * r ^ ((3 : ℝ) / 2) * (√A)⁻¹ * J) * R ^ 2 ≤ 1 := by
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hsr : √r ^ 2 = r := Real.sq_sqrt hr0
  have hx0 : 0 ≤ x := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hL0 : 0 ≤ Ξ * cF * r * √r * J * R ^ 2 := by positivity
  have hL2 : (Ξ * cF * r * √r * J * R ^ 2) ^ 2 ≤ (√A) ^ 2 := by
    rw [show (Ξ * cF * r * √r * J * R ^ 2) ^ 2
        = Ξ ^ 2 * cF ^ 2 * (r ^ 2 * √r ^ 2) * J ^ 2 * R ^ 4 by ring, hsr,
      Real.sq_sqrt hA.le, hJ]
    have hr3' : r ^ 2 * r ≤ 64 * z ^ 3 * R ^ 2 := by rw [← pow_succ]; exact hr3
    have hx32 : x ^ 32 ≤ x ^ 48 := pow_le_pow_right₀ hx1 (by norm_num)
    have hR14 : R ^ 14 ≤ R ^ 20 := pow_le_pow_right₀ hR1 (by norm_num)
    calc Ξ ^ 2 * cF ^ 2 * (r ^ 2 * r) * (x ^ 12 * R ^ 4) ^ 2 * R ^ 4
        ≤ Ξ ^ 2 * cF ^ 2 * (64 * z ^ 3 * R ^ 2) * (x ^ 12 * R ^ 4) ^ 2 * R ^ 4 := by gcongr
      _ = (64 * Ξ ^ 2 * cF ^ 2 * z ^ 3) * (x ^ 24 * R ^ 14) := by ring
      _ ≤ x ^ 8 * (x ^ 24 * R ^ 14) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = x ^ 32 * R ^ 14 := by ring
      _ ≤ x ^ 48 * R ^ 20 := mul_le_mul hx32 hR14 (by positivity) (by positivity)
      _ ≤ A := hxA
  have hL : Ξ * cF * r * √r * J * R ^ 2 ≤ √A :=
    (pow_le_pow_iff_left₀ hL0 (Real.sqrt_nonneg _) two_ne_zero).1 hL2
  have hsA : 0 < √A := Real.sqrt_pos.2 hA
  rw [DrSplit.rpow_three_halves hr0]
  calc Ξ * (cF * (r * √r) * (√A)⁻¹ * J) * R ^ 2 = (Ξ * cF * r * √r * J * R ^ 2) * (√A)⁻¹ := by
        ring
    _ ≤ √A * (√A)⁻¹ := mul_le_mul_of_nonneg_right hL (inv_nonneg.2 hsA.le)
    _ = 1 := by field_simp

/-- (5.35)-far term 2, pass 2:
`(Ξ P₂ R²)² ≤ Ξ² 169² 16 z² x^{36}R^{17}/A² ≤ x^{56}R^{17}/A² ≤ 1`. -/
theorem far2R_le {Ξ z r R A x J : ℝ} (hΞ : 0 ≤ Ξ) (hr0 : 0 ≤ r)
    (hr2 : r ^ 2 ≤ 16 * z ^ 2 * R) (hA : 0 < A) (hx1 : 1 ≤ x) (hR1 : 1 ≤ R)
    (hJ : J = x ^ 12 * R ^ 4) (hxA : x ^ 48 * R ^ 20 ≤ A)
    (hC : Ξ ^ 2 * 169 ^ 2 * 16 * z ^ 2 ≤ x ^ 20) :
    Ξ * (169 * r * A⁻¹ * J ^ ((3 : ℝ) / 2)) * R ^ 2 ≤ 1 := by
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hsJ : √J ^ 2 = J := Real.sq_sqrt hJ0
  have hx0 : 0 ≤ x := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hL0 : 0 ≤ Ξ * 169 * r * J * √J * R ^ 2 := by positivity
  have hL2 : (Ξ * 169 * r * J * √J * R ^ 2) ^ 2 ≤ A ^ 2 := by
    rw [show (Ξ * 169 * r * J * √J * R ^ 2) ^ 2
        = Ξ ^ 2 * 169 ^ 2 * r ^ 2 * (J ^ 2 * √J ^ 2) * R ^ 4 by ring, hsJ, hJ]
    have hx56 : x ^ 56 ≤ x ^ 96 := pow_le_pow_right₀ hx1 (by norm_num)
    have hR17 : R ^ 17 ≤ R ^ 40 := pow_le_pow_right₀ hR1 (by norm_num)
    have hA2 : (x ^ 48 * R ^ 20) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hxA 2
    calc Ξ ^ 2 * 169 ^ 2 * r ^ 2 * ((x ^ 12 * R ^ 4) ^ 2 * (x ^ 12 * R ^ 4)) * R ^ 4
        ≤ Ξ ^ 2 * 169 ^ 2 * (16 * z ^ 2 * R) * ((x ^ 12 * R ^ 4) ^ 2 * (x ^ 12 * R ^ 4)) *
            R ^ 4 := by gcongr
      _ = (Ξ ^ 2 * 169 ^ 2 * 16 * z ^ 2) * x ^ 36 * R ^ 17 := by ring
      _ ≤ x ^ 20 * x ^ 36 * R ^ 17 := by gcongr
      _ = x ^ 56 * R ^ 17 := by ring
      _ ≤ x ^ 96 * R ^ 40 := mul_le_mul hx56 hR17 (by positivity) (by positivity)
      _ = (x ^ 48 * R ^ 20) ^ 2 := by ring
      _ ≤ A ^ 2 := hA2
  have hL : Ξ * 169 * r * J * √J * R ^ 2 ≤ A :=
    (pow_le_pow_iff_left₀ hL0 hA.le two_ne_zero).1 hL2
  rw [DrSplit.rpow_three_halves hJ0]
  calc Ξ * (169 * r * A⁻¹ * (J * √J)) * R ^ 2 = (Ξ * 169 * r * J * √J * R ^ 2) * A⁻¹ := by ring
    _ ≤ A * A⁻¹ := mul_le_mul_of_nonneg_right hL (inv_nonneg.2 hA.le)
    _ = 1 := by field_simp

/-! ### The near band reaches the far field only through the kernel's exponential tail -/

/-- `e^{-(5/4)(log W)^{3/2}} ≤ W^{-a}` once `a² ≤ log W`, `a ≥ 0`, `W ≥ 1`. -/
theorem exp_log_le_rpow {W a : ℝ} (hW : 1 ≤ W) (ha : 0 ≤ a) (hlog : a ^ 2 ≤ Real.log W) :
    Real.exp (-(5 / 4 * Real.log W ^ (3 / 2 : ℝ))) ≤ W ^ (-a) := by
  have hW0 : 0 < W := by linarith
  have hl0 : 0 ≤ Real.log W := Real.log_nonneg hW
  rw [Real.rpow_def_of_pos hW0, Real.exp_le_exp]
  have hsq : a ≤ √(Real.log W) := by
    have := Real.sqrt_le_sqrt hlog
    rwa [Real.sqrt_sq ha] at this
  have h32 : Real.log W ^ (3 / 2 : ℝ) = Real.log W * √(Real.log W) :=
    DrSplit.rpow_three_halves hl0
  rw [h32]
  have h1 : a * Real.log W ≤ √(Real.log W) * Real.log W := mul_le_mul_of_nonneg_right hsq hl0
  have h2 : 0 ≤ Real.log W * √(Real.log W) := mul_nonneg hl0 (Real.sqrt_nonneg _)
  nlinarith

/-- **Near-band leakage into the far field.** If every `Dn j` is supported on the near band
`d_b ≤ ℓ*_{u_j}` with `‖Dn j‖ ≤ C` there, then at a far label (`6ℓ*_{u_k} < d_a`) the drift sum
is `≤ C · 128e³ (η_s/η_{u_k})² e^{-(5/4)(log W)^{3/2}}`. The kernel step is
`QVEndpoint.weightedKernel_supp_far_le` with `ρ = ℓ*_{u_j} ≤ ℓ*_{u_k}` and
`Δ = (5/2)ℓ*_{u_k}` (so `ρ + 2Δ ≤ 6ℓ*_{u_k}`); the time sum uses `kΔ ≤ 1`. -/
theorem near_leak_le {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ}
    {K : ℕ → ℕ} {N : ℕ} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) (hW : Real.exp 1 ≤ (B.W N : ℝ)) {C : ℝ}
    (hC : 0 ≤ C) (Dn : ℕ → LoopArg (B.L N) 2 → ℂ)
    (hDn : ∀ j < k, ∀ b, ‖Dn j b‖ ≤ C *
      (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N (time s t K N j))
        then 1 else 0))
    (a : LoopArg (B.L N) 2)
    (ha : 6 * ellStar (B.W N : ℝ) (B.ell N (time s t K N k)) < (zdist (B.L N) (a 0 - a 1) : ℝ)) :
    ‖(∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dn j)) a‖ ≤
      C * (128 * Real.exp 3 * (etaT E (s N) / etaT E (time s t K N k)) ^ 2 *
        Real.exp (-(5 / 4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ)))) := by
  classical
  set u : ℕ → ℝ := fun j => time s t K N j with hudef
  set Δ := step s t K N with hΔ
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t K N hst
  set v := u k with hv
  have hvt : v ≤ t N := time_le_t s t K N hst hK1 hk
  have hv1 : v < 1 := hvt.trans_lt ht1
  have hsv : s N ≤ v := s_le_time s t K N hst k
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have h1v : 0 < 1 - v := by linarith
  have hW0 : (0 : ℝ) < B.W N := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hlog1 : 1 ≤ Real.log (B.W N : ℝ) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hW
  have hlp : 0 < Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓv1 : 1 ≤ B.ell N v := one_le_ellHat_of_nonneg hL1 (hs0.trans hsv) hv1
  set R := etaT E (s N) / etaT E v with hR
  have hRe : R = (1 - s N) / (1 - v) := Step2.etaT_ratio hE _ _
  set Ex := Real.exp (-(5 / 4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ))) with hEx
  have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
  set X := C * (128 * Real.exp 3 * R ^ 2 * Ex) with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ j ∈ Finset.range k,
      ‖(Δ • Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (v : ℂ) (Dn j)) a‖ ≤ Δ * X := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hj1k : u (j + 1) ≤ v := time_mono' s t K N hst (by omega)
    have hjv : u j ≤ v := time_mono' s t K N hst hjk.le
    have hu0j1 : 0 ≤ u (j + 1) := hs0.trans (s_le_time s t K N hst (j + 1))
    have hu0j : 0 ≤ u j := hs0.trans (s_le_time s t K N hst j)
    have heval : (Δ • Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (v : ℂ) (Dn j)) a
        = (Δ : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (v : ℂ) (Dn j) a := by
      rw [Pi.smul_apply, Complex.real_smul]
    rw [heval, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    refine mul_le_mul_of_nonneg_left ?_ hΔ0
    -- the kernel sum
    set χ : LoopArg (B.L N) 2 → ℝ := fun b =>
      if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N (u j)) then 1 else 0
      with hχ
    have hU1 : ‖Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (v : ℂ) (Dn j) a‖ ≤
        C * ∑ b : LoopArg (B.L N) 2,
          ‖∏ i : Fin 2, edgeKer (B.L N) 1 (u (j + 1) : ℂ) (v : ℂ) (a i) (b i)‖ * χ b := by
      rw [Uker_apply, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      have h := hDn j hjk b
      calc ‖∏ i : Fin 2, edgeKer (B.L N) ((fun _ => (1 : ℂ)) i) (u (j + 1) : ℂ) (v : ℂ)
              (a i) (b i)‖ * ‖Dn j b‖
          ≤ ‖∏ i : Fin 2, edgeKer (B.L N) 1 (u (j + 1) : ℂ) (v : ℂ) (a i) (b i)‖ *
              (C * χ b) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = C * (‖∏ i : Fin 2, edgeKer (B.L N) 1 (u (j + 1) : ℂ) (v : ℂ) (a i) (b i)‖ *
              χ b) := by ring
    have hstar : ellStar (B.W N : ℝ) (B.ell N (u j)) ≤ ellStar (B.W N : ℝ) (B.ell N v) := by
      unfold ellStar
      exact mul_le_mul_of_nonneg_left (Step3.ellHat_mono hjv hv1) hlp.le
    have hΔpos : 0 < 5 / 2 * ellStar (B.W N : ℝ) (B.ell N v) := by
      unfold ellStar; positivity
    have hd : ellStar (B.W N : ℝ) (B.ell N (u j)) + 2 * (5 / 2 * ellStar (B.W N : ℝ) (B.ell N v))
        ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by linarith
    have hsup := QVEndpoint.weightedKernel_supp_far_le (B.L N) (B.three_le_L N) hu0j1
      hj1k hv1 hΔpos a hd
    have hexp : Real.exp (-(5 / 2 * ellStar (B.W N : ℝ) (B.ell N v) /
        ellHat (B.L N) (v : ℂ) / 2)) = Ex := by
      rw [hEx]
      congr 1
      have hℓ0 : ellHat (B.L N) (v : ℂ) ≠ 0 := by
        have : (1 : ℝ) ≤ ellHat (B.L N) (v : ℂ) := hℓv1
        linarith
      unfold ellStar
      change -(5 / 2 * (Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) * ellHat (B.L N) (v : ℂ)) /
        ellHat (B.L N) (v : ℂ) / 2) = _
      field_simp
      ring
    rw [hexp] at hsup
    have hw : ((1 - u (j + 1)) / (1 - v)) ^ 2 ≤ R ^ 2 := by
      rw [hRe]
      have hsu1 : s N ≤ u (j + 1) := s_le_time s t K N hst (j + 1)
      refine pow_le_pow_left₀ (div_nonneg (by linarith) h1v.le) ?_ 2
      exact div_le_div_of_nonneg_right (by linarith) h1v.le
    refine hU1.trans ?_
    rw [hX]
    refine mul_le_mul_of_nonneg_left (hsup.trans ?_) hC
    have he3 : 0 ≤ 128 * Real.exp 3 := by positivity
    calc 128 * Real.exp 3 * ((1 - u (j + 1)) / (1 - v)) ^ 2 * Ex
        ≤ 128 * Real.exp 3 * R ^ 2 * Ex := by gcongr
      _ = _ := rfl
  have hkΔ : (k : ℝ) * Δ = v - s N := by simp only [hv, hudef, time_eq]; ring
  calc ‖(∑ j ∈ Finset.range k, Δ • Uker (B.L N) (fun _ => (1 : ℂ))
        (u (j + 1) : ℂ) (v : ℂ) (Dn j)) a‖
      = ‖∑ j ∈ Finset.range k,
          (Δ • Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (v : ℂ) (Dn j)) a‖ := by
        rw [Finset.sum_apply]
    _ ≤ ∑ j ∈ Finset.range k,
          ‖(Δ • Uker (B.L N) (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (v : ℂ) (Dn j)) a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, Δ * X := Finset.sum_le_sum hterm
    _ = ((k : ℝ) * Δ) * X := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 1 * X := by
        refine mul_le_mul_of_nonneg_right ?_ hX0
        rw [hkΔ]; linarith
    _ = X := one_mul X

/-- `e³ ≤ 21`. -/
theorem exp_three_le : Real.exp 3 ≤ 21 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ h0.le h.le 3
    _ ≤ 21 := by norm_num

/-- `e ≤ 3`. -/
theorem exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9
  linarith

/-- `W^n W^a = W^b` when `n + a = b` (`W > 0`). -/
theorem rpow_nat_mul_rpow {W : ℝ} (hW : 0 < W) (n : ℕ) {a b : ℝ} (h : (n : ℝ) + a = b) :
    W ^ n * W ^ a = W ^ b := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hW, h]

/-- The final allocation of the far closure into `6 x² T'`. -/
theorem final_far_arith {Mi Ξ x c T T' w : ℝ}
    {zI zZ zY zDn zDf zR : ℂ}
    (hI : ‖zI‖ ≤ Mi * Ξ * T + w) (hZ : ‖zZ‖ ≤ x * T) (hY : ‖zY‖ ≤ T)
    (hDn : ‖zDn‖ ≤ w) (hDf : ‖zDf‖ ≤ c * T) (hR : ‖zR‖ ≤ T)
    (hMiΞ : Mi * Ξ ≤ x ^ 2) (hx : x ≤ x ^ 2) (hc4 : c + 4 ≤ x ^ 2) (hc : 0 ≤ c)
    (hT0 : 0 ≤ T) (hTT : T ≤ T') (hw : w ≤ T') :
    ‖zI + zZ + zY + (zDn + zDf) + zR‖ ≤ 6 * x ^ 2 * T' := by
  have h1 := norm_add_le (zI + zZ + zY + (zDn + zDf)) zR
  have h2 := norm_add_le (zI + zZ + zY) (zDn + zDf)
  have h3 := norm_add_le (zI + zZ) zY
  have h4 := norm_add_le zI zZ
  have h5 := norm_add_le zDn zDf
  have hT'0 : 0 ≤ T' := hT0.trans hTT
  have hx2 : 0 ≤ x ^ 2 := by nlinarith
  have a1 : Mi * Ξ * T ≤ x ^ 2 * T' := mul_le_mul hMiΞ hTT hT0 hx2
  have a2 : x * T ≤ x ^ 2 * T' := mul_le_mul hx hTT hT0 hx2
  have a3 : c * T ≤ c * T' := mul_le_mul_of_nonneg_left hTT hc
  have a4 : (c + 4) * T' ≤ x ^ 2 * T' := mul_le_mul_of_nonneg_right hc4 hT'0
  have a5 : 0 ≤ x ^ 2 * T' := mul_nonneg hx2 hT'0
  nlinarith

/-- The per-`N` union bound: a set covered by `A ∪ C` has measure at most `μ A + μ C`. -/
theorem measure_le_of_subset_union {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S A C : Set Ω} {x y : ENNReal} (h : S ⊆ A ∪ C) (hA : μ A ≤ x) (hC : μ C ≤ y) :
    μ S ≤ x + y :=
  (measure_mono h).trans ((measure_union_le A C).trans (add_le_add hA hC))

/-- `lkErrMat` at the grid time is the norm of the grid `2`-loop `A_k`. -/
theorem lkErrMat_eq_norm_Agrid (d : Dims) {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (k : ℕ) (ω : Ωg d) (p q : ZMod (d.L N)) :
    lkErrMat d E N (time s u K N k) (H d s u K N k ω) (pmLoop p q)
      = ‖Agrid (band d) E s u K N k ω ![p, q]‖ := by
  have hofn : List.ofFn (![p, q] : Fin 2 → ZMod (d.L N)) = [p, q] := by
    simp [List.ofFn_succ]
  have hpm : (pmLoop p q : LoopIdx (ZMod (d.L N)))
      = ⟨[true, false], List.ofFn (![p, q] : Fin 2 → ZMod (d.L N))⟩ := by
    rw [hofn]; rfl
  rw [hpm]
  rfl

end FarClosure

/-! ## The main statements -/

variable (d : Dims)

/-! ### Acceptance checks -/

end RBM.Gauss.Grid

end

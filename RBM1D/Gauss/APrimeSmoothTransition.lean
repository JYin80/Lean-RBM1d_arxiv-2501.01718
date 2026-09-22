/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothWeightActual
import RBM1D.Gauss.Step6Sample
import RBM1D.Gauss.FirstCellStep1LocalLaw

/-! # Actual scalar samples for the smooth-prefix transition -/
namespace RBM.APrimeSmoothTransition
open Gauss Step2Bootstrap CutHypTheta Cutoff Filter
open scoped Matrix.Norms.L2Operator

noncomputable def scalarSample (d : Gauss.Dims) (x : ℝ) : Gauss.Ω d :=
  fun c => if c.2.1 = c.2.2.1 then x else 0

theorem Xmat_scalarSample (d : Gauss.Dims) (N : ℕ) (x : ℝ) :
    Gauss.Xmat d N (scalarSample d x) = (x : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Gauss.Xmat, Gauss.Xentry, scalarSample]
  · simp [Gauss.Xmat, Gauss.Xentry, scalarSample, hij, Ne.symm hij,
      Matrix.smul_apply]

theorem green_scalar {n : Type*} [Fintype n] [DecidableEq n] {x z : ℂ}
    (h : x - z ≠ 0) :
    green (x • (1 : Matrix n n ℂ)) z = (x-z)⁻¹ • (1 : Matrix n n ℂ) := by
  rw [green, ← sub_smul]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ h, one_smul]

theorem gloop_scalar_two {L W : ℕ} [NeZero L] [NeZero W]
    (x z : ℂ) (hx : x-z ≠ 0) (hxc : x-(starRingEnd ℂ) z ≠ 0)
    (a b : ZMod L) :
    gloop L W (x • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) z
      ⟨[true,false],[a,b]⟩ =
      if a=b then (x-z)⁻¹ * (x-(starRingEnd ℂ) z)⁻¹ * (W : ℂ)⁻¹ else 0 := by
  rw [gloop_two, Gsig_true, Gsig_false, green_scalar hx, green_scalar hxc]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  rw [Eblk_mul_Eblk]
  split_ifs with hab
  · simp [Matrix.trace_smul, trace_Eblk, smul_eq_mul]
    ring
  · simp

theorem gloop_scalar_zero_energy {L W : ℕ} [NeZero L] [NeZero W]
    (x u : ℝ) (hu : u < 1) (a b : ZMod L) :
    gloop L W ((x : ℂ) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      (zt 0 u) ⟨[true,false],[a,b]⟩ =
      if a=b then (((W : ℝ) * (x^2+(1-u)^2))⁻¹ : ℝ) else 0 := by
  have hz : (x : ℂ) - zt 0 u ≠ 0 := by
    intro hh
    have := congrArg Complex.im hh
    simp [Gauss.zt_zero_energy] at this
    linarith
  have hzc : (x : ℂ) - (starRingEnd ℂ) (zt 0 u) ≠ 0 := by
    intro hh
    have := congrArg Complex.im hh
    simp [Gauss.zt_zero_energy] at this
    linarith
  rw [gloop_scalar_two _ _ hz hzc]
  split_ifs
  · rw [← mul_inv, ← mul_inv]
    push_cast
    congr 1
    simp only [Gauss.zt_zero_energy, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
    simp
    ring
  · rfl

theorem Hflow_scalarSample (d : Gauss.Dims) (N : ℕ) (u x : ℝ) :
    Gauss.Hflow d N u (scalarSample d x) =
      ((Real.sqrt u * x : ℝ) : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  rw [Gauss.Hflow, Xmat_scalarSample, smul_smul, Complex.ofReal_mul]

theorem Hflow_transitionSample (d : Gauss.Dims) (N : ℕ) {h : ℝ} (hh : 0 < h) :
    Gauss.Hflow d N h (scalarSample d (2 / Real.sqrt h)) =
      (2 : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  rw [Hflow_scalarSample]
  have hr : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  have he : Real.sqrt h * (2 / Real.sqrt h) = 2 := by field_simp
  rw [he]
  norm_num

theorem lk_scalarSample (d : Gauss.Dims) (N : ℕ) (u x : ℝ) (hu : u < 1)
    (a : LoopArg (d.L N) 2) :
    Step2.lk (Gauss.sample d) 0 N u (scalarSample d x) a =
      (if a 0 = a 1 then ((((d.W N : ℝ) * ((Real.sqrt u*x)^2+(1-u)^2))⁻¹ : ℝ) : ℂ)
        else 0) - (d.W N : ℂ)⁻¹ * Theta (d.L N) (u : ℂ) (a 0) (a 1) := by
  have hi : LoopData.idx ((Step2.sigPM,a) : LoopData (d.L N) 2) =
      ⟨[true,false],[a 0,a 1]⟩ := by
    simp [LoopData.idx, Step2.sigPM, List.ofFn_succ]
  change gloop (d.L N) (d.W N) (Gauss.Hflow d N u (scalarSample d x)) (zt 0 u)
      (LoopData.idx (Step2.sigPM,a)) -
      Kgen (d.L N) (d.W N) (mSigma 0) u (LoopData.idx (Step2.sigPM,a)) = _
  rw [hi, Hflow_scalarSample, gloop_scalar_zero_energy _ _ hu,
    Kgen_two, kTwo, Step2FarInputs.mSigma_true_mul_false (by norm_num)]
  simp only [mul_one]
  split_ifs <;> push_cast <;> rfl

theorem norm_Theta_sub_identity (d : Gauss.Dims) (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1/2) (a b : ZMod (d.L N)) :
    ‖Theta (d.L N) (u : ℂ) a b - (if a=b then 1 else 0)‖ ≤ 4*u := by
  have hh := norm_Theta_apply_sub_le (L := d.L N) (d.three_le_L N)
    (r := 1/2) (ξ := (u : ℂ)) (ζ := 0) (by norm_num)
    (by simpa [Complex.norm_real, abs_of_nonneg hu0] using hu) (by norm_num) a b
  norm_num [Theta_zero, Matrix.one_apply, Complex.norm_real, abs_of_nonneg hu0,
    mul_comm] at hh ⊢
  exact hh

theorem norm_lk_zero_le (d : Gauss.Dims) (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1/2) (a : LoopArg (d.L N) 2) :
    ‖Step2.lk (Gauss.sample d) 0 N u (scalarSample d 0) a‖ ≤
      10*u/(d.W N : ℝ) := by
  have hu1 : u < 1 := by linarith
  have hv : 0 < 1-u := by linarith
  have hW : (0:ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hi : Step2.lk (Gauss.sample d) 0 N u (scalarSample d 0) a =
      (d.W N : ℂ)⁻¹ *
        ((if a 0 = a 1 then ((((1-u)^2)⁻¹ : ℝ) : ℂ) else 0) -
          Theta (d.L N) (u : ℂ) (a 0) (a 1)) := by
    rw [lk_scalarSample d N u 0 hu1 a]
    split_ifs <;> push_cast <;> simp [mul_inv] <;> ring
  have hs : |((1-u)^2)⁻¹-1| ≤ 6*u := by
    have hb : 1 ≤ ((1-u)^2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hv)).2 (by nlinarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hb)]
    have hp : (1-u)^2 > 0 := sq_pos_of_pos hv
    apply (sub_le_iff_le_add).2
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg hu0 (mul_nonneg (by linarith : 0 ≤ 1-2*u)
      (by linarith : 0 ≤ 4-3*u))]
  have hs' : ‖(if a 0 = a 1 then ((((1-u)^2)⁻¹ : ℝ) : ℂ) else 0) -
      (if a 0 = a 1 then (1:ℂ) else 0)‖ ≤ 6*u := by
    split_ifs
    · simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hs
    · simp only [sub_self, norm_zero]
      positivity
  have ht := norm_Theta_sub_identity d N hu0 hu (a 0) (a 1)
  have ht' := (norm_sub_le_norm_sub_add_norm_sub
    (if a 0 = a 1 then ((((1-u)^2)⁻¹ : ℝ) : ℂ) else 0)
    (if a 0 = a 1 then (1:ℂ) else 0)
    (Theta (d.L N) (u : ℂ) (a 0) (a 1)))
  rw [norm_sub_rev (if a 0 = a 1 then (1:ℂ) else 0)] at ht'
  rw [hi, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d.W N : ℝ)⁻¹ * (10*u) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hW.le)
    _ = _ := by ring

theorem jSnorm_zero_le_two (d : Gauss.Dims) (N : ℕ) {u D : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1/2)
    (hsmall : 10*u*(d.W N : ℝ)^(D-1) ≤ 1) :
    Step2Moment.jSnorm (Gauss.sample d) 0 D (fun _ => 0) N u (scalarSample d 0) ≤ 2 := by
  have hW : (0:ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hp : 0 < (d.W N : ℝ)^(-D) := Real.rpow_pos_of_pos hW _
  have he : (d.W N : ℝ)^(D-1)*(d.W N : ℝ)^(-D) = (d.W N : ℝ)⁻¹ := by
    rw [← Real.rpow_add hW]
    convert Real.rpow_neg_one (d.W N : ℝ) using 1 <;> ring
  have hb : 10*u/(d.W N : ℝ) ≤ (d.W N : ℝ)^(-D) := by
    calc
      _ = (10*u*(d.W N : ℝ)^(D-1))*(d.W N : ℝ)^(-D) := by rw [mul_assoc, he]; ring
      _ ≤ 1*(d.W N : ℝ)^(-D) := mul_le_mul_of_nonneg_right hsmall hp.le
      _ = _ := one_mul _
  have hj : Step2.jS (Gauss.sample d) 0 D N u (scalarSample d 0) ≤ 2 := by
    unfold Step2.jS Step2.jStar
    rw [← le_sub_iff_add_le]
    norm_num only [show (2:ℝ)-1=1 by norm_num]
    apply Finset.sup'_le
    intro a ha
    have ht : 0 < tailT (d.W N : ℝ) ((Gauss.band d).ell N u) (etaT 0 u) D
        (zdist (d.L N) (a 0-a 1)) := tailT_pos hW _
    apply (div_le_one ht).2
    exact (norm_lk_zero_le d N hu0 hu a).trans
      (hb.trans (rpow_neg_le_tailT _))
  have hR : 1 ≤ (Step2Moment.ratR 0 (fun _ => 0) N u)^4 :=
    one_le_pow₀ (Step2Moment.one_le_ratR (by norm_num) hu0 (by linarith))
  unfold Step2Moment.jSnorm
  apply (div_le_iff₀ (by linarith : 0 < (Step2Moment.ratR 0 (fun _ => 0) N u)^4)).2
  linarith

theorem weight_zeroSample_eq_one (d : Gauss.Dims) {N N0 p m : ℕ}
    {D δ : ℝ} {t mesh : ℕ → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ)
    (ht0 : 0 ≤ t N) (ht1 : t N < 1) (hmesh : 0 < mesh N)
    (hm : 1 ≤ m) (hk : 2 ≤ cutNetTop (fun _ => 0) t mesh N)
    (hh : (mesh N)⁻¹ ≤ 1/2)
    (hsmall : 10*(mesh N)⁻¹*(d.W N : ℝ)^(D-1) ≤ 1)
    (hcard : (((2*Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1:ℝ)/(2*(m:ℝ)))) ≤ Real.exp 1) :
    APrimeSmoothWeightActual.weight d 0 D δ (fun _ => 0) t mesh N0 p N 2 m
      (scalarSample d 0) = 1 := by
  have hbound := APrimeSmoothWeightActual.prefixSample_le_of_jSnorm_bound d
    (E := 0) (D := D) (B := 2) (s := fun _ => 0) (t := t) (mesh := mesh)
    (N := N) (k := 2) (m := m) (by norm_num) ht0 ht1 hmesh (by omega) hm hk
    (by norm_num) (scalarSample d 0) (by
      intro j hj
      interval_cases j
      · simpa [cutNetPt] using jSnorm_zero_le_two d N (D := D)
          (u := 0) (by norm_num) (by norm_num) (by norm_num)
      · simpa [cutNetPt] using jSnorm_zero_le_two d N (D := D)
          (u := (mesh N)⁻¹) (inv_nonneg.mpr hmesh.le) hh hsmall)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn10 : (N : ℝ)^(-(10:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hnδ : 1 ≤ (N : ℝ)^(2*δ) := Real.one_le_rpow hN1 (by positivity)
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hS : APrimeSmoothWeightActual.prefixSample d 0 D (fun _ => 0) mesh N 2 m
      (scalarSample d 0) ≤ APrimeSmoothWeightActual.threshold δ N := by
    have hmul := mul_le_mul_of_nonneg_right hcard
      (by positivity : 0 ≤ (2:ℝ)+(N:ℝ)^(-(10:ℝ)))
    have hh3 : Real.exp 1*(2+(N:ℝ)^(-(10:ℝ))) ≤ 3*Real.exp 1 := by nlinarith
    have ht : 3*Real.exp 1 ≤ 8*(Real.exp 1)^2*(N:ℝ)^(2*δ) := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 8*(Real.exp 1)^2)
        (sub_nonneg.mpr hnδ)]
    exact hbound.trans (hmul.trans (hh3.trans ht))
  have hc : APrimeSmoothWeightActual.cutoff d 0 D δ (fun _ => 0) mesh N 2 m
      (scalarSample d 0) = 1 := by
    apply cutChi_eq_one
    exact (div_le_one (APrimeSmoothWeightActual.threshold_pos (δ := δ) (by omega))).2 hS
  unfold APrimeSmoothWeightActual.weight
  split_ifs <;> simp [hc]

theorem norm_lk_transition_lower (d : Gauss.Dims) (N : ℕ) {h : ℝ}
    (hh : 0 < h) (hh8 : h ≤ 1/8) (a : ZMod (d.L N)) :
    (1:ℝ)/(4*(d.W N : ℝ)) ≤
      ‖Step2.lk (Gauss.sample d) 0 N h (scalarSample d (2/Real.sqrt h)) (fun _ => a)‖ := by
  have hu : h < 1 := by linarith
  have hW : (0:ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hr : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  have he : Real.sqrt h*(2/Real.sqrt h) = 2 := by field_simp
  have hTheta : (1:ℝ)/2 ≤ ‖Theta (d.L N) (h : ℂ) a a‖ := by
    have hd := norm_Theta_sub_identity d N hh.le (by linarith) a a
    simp only [ite_true] at hd
    have hn := norm_sub_norm_le (1:ℂ) (Theta (d.L N) (h : ℂ) a a)
    rw [norm_one, norm_sub_rev] at hn
    linarith
  have hK : (1:ℝ)/(2*(d.W N : ℝ)) ≤
      ‖(d.W N : ℂ)⁻¹ * Theta (d.L N) (h : ℂ) a a‖ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hb := mul_le_mul_of_nonneg_left hTheta (inv_nonneg.mpr hW.le)
    convert hb using 1 <;> ring
  have hL : ‖((((d.W N : ℝ)*(2^2+(1-h)^2))⁻¹ : ℝ) : ℂ)‖ ≤
      1/(4*(d.W N : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg (1-h)]
  rw [lk_scalarSample d N h _ hu, he, if_pos rfl]
  have hn := norm_sub_norm_le ((d.W N : ℂ)⁻¹ * Theta (d.L N) (h : ℂ) a a)
    (((((d.W N : ℝ)*(2^2+(1-h)^2))⁻¹ : ℝ) : ℂ))
  rw [norm_sub_rev] at hn
  have heq : (1:ℝ)/(2*(d.W N : ℝ))-1/(4*(d.W N : ℝ)) = 1/(4*(d.W N : ℝ)) := by ring
  linarith

theorem tail_normalization_le_sixteen {W ell h D : ℝ}
    (hW : 1 ≤ W) (hell : 1 ≤ ell) (hh0 : 0 ≤ h) (hh : h ≤ 1/8) (hD : 2 ≤ D) :
    tailT W ell (1-h) D 0 * (1/(1-h))^4 ≤ 16/W^2 := by
  have hW0 : 0 < W := by linarith
  have he0 : 0 < ell := by linarith
  have hh1 : 0 < 1-h := by linarith
  have hb : 3/4*W ≤ W*ell*(1-h) := by
    have h1 : W ≤ W*ell := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-h-3/4) (by positivity : 0 ≤ W*ell)]
  have hden : 0 < (W*ell*(1-h))^2 := sq_pos_of_pos (by positivity)
  have hmain : ((W*ell*(1-h))^2)⁻¹ ≤ 2/W^2 := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hW0)).2
    nlinarith [sq_nonneg (W*ell*(1-h)-3/4*W)]
  have htail : W^(-D) ≤ 1/W^2 := by
    calc
      _ ≤ W^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
      _ = _ := by rw [Real.rpow_neg hW0.le, Real.rpow_two]; simp
  have hR : 1/(1-h) ≤ 4/3 := (div_le_iff₀ hh1).2 (by linarith)
  have hR4 : (1/(1-h))^4 ≤ 4 := by
    calc _ ≤ (4/3:ℝ)^4 := pow_le_pow_left₀ (by positivity) hR _
         _ ≤ _ := by norm_num
  have ht : tailT W ell (1-h) D 0 ≤ 3/W^2 := by
    simp only [tailT, zero_div, Real.sqrt_zero, neg_zero, Real.exp_zero, mul_one]
    calc _ ≤ 2/W^2+1/W^2 := add_le_add hmain htail
         _ = 3/W^2 := by ring
  calc
    _ ≤ (3/W^2)*4 := mul_le_mul ht hR4 (by positivity) (by positivity)
    _ ≤ 16/W^2 := by have := sq_pos_of_pos hW0; field_simp; norm_num

theorem actual_tail_normalization_le_sixteen (d : Gauss.Dims) (N : ℕ)
    {h D : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1/8) (hD : 2 ≤ D) :
    Step2.tT (Gauss.band d) 0 N D h 0 *
      (Step2Moment.ratR 0 (fun _ => 0) N h)^4 ≤ 16/(d.W N : ℝ)^2 := by
  have hW : (1:ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have he := one_le_ellHat (d.L N) (d.three_le_L N) hh0 (by linarith : h<1)
  simpa [Step2.tT, Band.ell, Step2Moment.ratR, Step2.etaT_eq, Gauss.mE_zero] using
    tail_normalization_le_sixteen hW he hh0 hh hD

theorem jSnorm_transition_lower (d : Gauss.Dims) (N : ℕ) {h D : ℝ}
    (hh : 0 < h) (hh8 : h ≤ 1/8) (hD : 2 ≤ D) :
    (d.W N : ℝ)/64 ≤ Step2Moment.jSnorm (Gauss.sample d) 0 D (fun _ => 0)
      N h (scalarSample d (2/Real.sqrt h)) := by
  let ω := scalarSample d (2/Real.sqrt h)
  let J := Step2Moment.jSnorm (Gauss.sample d) 0 D (fun _ => 0) N h ω
  let R := (Step2Moment.ratR 0 (fun _ => 0) N h)^4
  let T := Step2.tT (Gauss.band d) 0 N D h 0
  have hW : (0:ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hR : 0 < R := pow_pos (Step2Moment.ratR_pos (by norm_num)
    (by norm_num) (by linarith : h<1)) _
  have hJ : 0 ≤ J := Step2Moment.jSnorm_nonneg (Gauss.sample d) (by norm_num)
    (by norm_num) (by linarith) ω
  have hc : ‖Step2.lk (Gauss.sample d) 0 N h ω (fun _ => 0)‖ ≤
      Step2.jS (Gauss.sample d) 0 D N h ω * T := by
    have hh' := Step2.le_jStar_mul
      (f := fun a => ‖Step2.lk (Gauss.sample d) 0 N h ω a‖)
      (W := ((Gauss.band d).W N : ℝ)) (ℓu := (Gauss.band d).ell N h)
      (ηu := etaT 0 h) (D := D) hW (fun _ => 0)
    simpa only [Step2.jS, T, Step2.tT, sub_self, zdist_zero, Nat.cast_zero] using hh'
  have hc' : ‖Step2.lk (Gauss.sample d) 0 N h ω (fun _ => 0)‖ ≤ J*(T*R) := by
    convert hc using 1
    dsimp [J, Step2Moment.jSnorm, R]
    have hr0 : Step2Moment.ratR 0 (fun _ => 0) N h ≠ 0 :=
      (Step2Moment.ratR_pos (by norm_num) (by norm_num) (by linarith : h<1)).ne'
    field_simp [hr0]
  have hd : T*R ≤ 16/(d.W N : ℝ)^2 := actual_tail_normalization_le_sixteen d N hh.le hh8 hD
  have hl := norm_lk_transition_lower d N hh hh8 0
  have hall : (1:ℝ)/(4*(d.W N : ℝ)) ≤ J*(16/(d.W N : ℝ)^2) :=
    hl.trans (hc'.trans (mul_le_mul_of_nonneg_left hd hJ))
  have hWn := hW.ne'
  dsimp [J] at *
  field_simp [hWn] at hall
  nlinarith

theorem jSnorm_net_le_prefixSample (d : Gauss.Dims) {N k m j : ℕ}
    {D : ℝ} {mesh : ℕ → ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hj : j < k)
    (hu : cutNetPt (fun _ => 0) mesh N j < 1) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) 0 D (fun _ => 0) N
      (cutNetPt (fun _ => 0) mesh N j) ω ≤
      APrimeSmoothWeightActual.prefixSample d 0 D (fun _ => 0) mesh N k m ω := by
  have hinner := APrimeSmoothPrefix.jSnorm_le_smoothJS d (E := 0) (by norm_num)
    (s := fun _ => 0) (N := N) (D := D) (by norm_num) hu
    (APrimeSmoothWeightActual.epsilon_pos d D hN).le hm ω
  have heq : APrimeSmoothWeightActual.prefixSample d 0 D (fun _ => 0) mesh N k m ω =
      softMax m (Finset.range k) (fun i =>
        APrimeSmoothPrefix.smoothJS d 0 D (fun _ => 0) N
          (cutNetPt (fun _ => 0) mesh N i) (APrimeSmoothWeightActual.epsilon d D N) m ω) := by
    unfold APrimeSmoothWeightActual.prefixSample APrimeSmoothWeightActual.prefixMatrix
    apply congrArg (fun f : ℕ → ℝ => softMax m (Finset.range k) f)
    funext i
    exact APrimeSmoothPrefix.smoothJSMatrix_flow d 0 D (fun _ => 0) N
      (cutNetPt (fun _ => 0) mesh N i) (APrimeSmoothWeightActual.epsilon d D N) m ω
  rw [heq]
  exact hinner.trans ((le_abs_self _).trans (le_softMax hm (ρ := fun i => APrimeSmoothPrefix.smoothJS d 0 D (fun _ => 0) N
      (cutNetPt (fun _ => 0) mesh N i) (APrimeSmoothWeightActual.epsilon d D N) m ω)
      (Finset.mem_range.mpr hj)))

theorem weight_transitionSample_eq_zero (d : Gauss.Dims) {N N0 p m : ℕ}
    {D δ : ℝ} {t mesh : ℕ → ℝ} (hN : 0 < N) (hN0 : N0 ≤ N) (hp : 1 ≤ p)
    (hm : 1 ≤ m) (hk : 2 ≤ cutNetTop (fun _ => 0) t mesh N)
    (hmesh : 0 < mesh N) (hh : (mesh N)⁻¹ ≤ 1/8) (hD : 2 ≤ D)
    (hlarge : 1024*(Real.exp 1)^2*(N:ℝ)^(2*δ) < (d.W N : ℝ)) :
    APrimeSmoothWeightActual.weight d 0 D δ (fun _ => 0) t mesh N0 p N 2 m
      (scalarSample d (2/Real.sqrt ((mesh N)⁻¹))) = 0 := by
  let ω := scalarSample d (2/Real.sqrt ((mesh N)⁻¹))
  have hl := jSnorm_transition_lower d N (inv_pos.mpr hmesh) hh hD
  have hn := jSnorm_net_le_prefixSample d (D := D) (mesh := mesh) (k := 2)
    (j := 1) hN hm (by omega) (by simp [cutNetPt]; linarith) ω
  have hcap : 2*APrimeSmoothWeightActual.threshold δ N ≤
      APrimeSmoothWeightActual.prefixSample d 0 D (fun _ => 0) mesh N 2 m ω := by
    simp only [cutNetPt, Nat.cast_one, zero_add, one_div] at hn
    unfold APrimeSmoothWeightActual.threshold
    linarith
  have hz : APrimeSmoothWeightActual.cutoff d 0 D δ (fun _ => 0) mesh N 2 m ω = 0 :=
    cutChi_eq_zero ((le_div_iff₀ (APrimeSmoothWeightActual.threshold_pos hN)).2 hcap)
  unfold APrimeSmoothWeightActual.weight
  rw [if_pos ⟨hk,hN0⟩]
  change APrimeSmoothWeightActual.cutoff d 0 D δ (fun _ => 0) mesh N 2 m ω ^ (2*p) = 0
  rw [hz, zero_pow (by omega : 2*p ≠ 0)]

theorem finite_transition (d : Gauss.Dims) {N N0 p m : ℕ}
    {D δ : ℝ} {t mesh : ℕ → ℝ} (hN : 2 ≤ N) (hN0 : N0 ≤ N) (hp : 1 ≤ p)
    (hm : 1 ≤ m) (hδ : 0 < δ) (hD : 2 ≤ D)
    (ht0 : 0 ≤ t N) (ht1 : t N < 1) (hmesh : 0 < mesh N)
    (hk : 2 ≤ cutNetTop (fun _ => 0) t mesh N)
    (hsmall : 10*(mesh N)⁻¹*(d.W N : ℝ)^(D-1) ≤ 1)
    (hcard : (((2*Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1:ℝ)/(2*(m:ℝ)))) ≤ Real.exp 1)
    (hlarge : 1024*(Real.exp 1)^2*(N:ℝ)^(2*δ) < (d.W N : ℝ)) :
    APrimeSmoothWeightActual.weight d 0 D δ (fun _ => 0) t mesh N0 p N 2 m
      (scalarSample d 0) = 1 ∧
    APrimeSmoothWeightActual.weight d 0 D δ (fun _ => 0) t mesh N0 p N 2 m
      (scalarSample d (2/Real.sqrt ((mesh N)⁻¹))) = 0 := by
  have hW1 : (1:ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hpow : 1 ≤ (d.W N : ℝ)^(D-1) := Real.one_le_rpow hW1 (by linarith)
  have hh : (mesh N)⁻¹ ≤ 1/8 := by
    have hinv : 0 ≤ (mesh N)⁻¹ := (inv_pos.mpr hmesh).le
    nlinarith [mul_nonneg (by positivity : 0 ≤ 10*(mesh N)⁻¹) (sub_nonneg.mpr hpow)]
  exact ⟨weight_zeroSample_eq_one d hN hδ ht0 ht1 hmesh hm hk (by linarith)
    hsmall hcard, weight_transitionSample_eq_zero d (by omega) hN0 hp hm hk hmesh hh hD hlarge⟩

noncomputable def transitionMesh (N : ℕ) : ℝ := (max (1:ℝ) N)^248

private theorem eventually_firstCell_half {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, Gauss.firstCellT τ N = 1/2 := by
  have ht : Tendsto (fun N : ℕ => (Gauss.Dims.exampleGrow.W N : ℝ)^(-τ))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ).comp (Step2.tendsto_W (Gauss.band Gauss.Dims.exampleGrow))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with N hN
  change gridT ((Gauss.band Gauss.Dims.exampleGrow).W N : ℝ) τ (1/2) 1 = 1/2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Gauss.Dims.growW N : ℝ)^(-τ) < 1/2 at hN
  linarith

private theorem eventually_transition_large {δ : ℝ} (hδ : δ < 1/4) :
    ∀ᶠ N : ℕ in atTop,
      1024*(Real.exp 1)^2*(N:ℝ)^(2*δ) < (Gauss.Dims.exampleGrow.W N : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/8-2*δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [Gauss.Dims.bandwidth_grow,
    ht.eventually_gt_atTop (1024*(Real.exp 1)^2), eventually_ge_atTop 1] with N hW hN hn
  have hn0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hm := mul_lt_mul_of_pos_right hN (Real.rpow_pos_of_pos hn0 (2*δ))
  rw [← Real.rpow_add hn0] at hm
  have he : (1:ℝ)/2+1/8-2*δ+2*δ = 1/2+1/8 := by ring
  rw [he] at hm
  exact hm.trans_le hW

private theorem calibrated_two_grow (N : ℕ) (hN : 81 ≤ N) :
    (((2*Fintype.card (LoopArg (Gauss.Dims.exampleGrow.L N) 2) : ℕ) : ℝ) ^
      ((1:ℝ)/(2*(N:ℝ)))) ≤ Real.exp 1 := by
  have hNr : (81:ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : (1:ℝ) ≤ Gauss.Dims.growL N := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) (Gauss.Dims.three_le_growL N))
  have hL4 : (Gauss.Dims.growL N : ℝ)^4 ≤ N := by
    exact_mod_cast Gauss.Dims.growL_pow_le N hN
  have hL2 : (Gauss.Dims.growL N : ℝ)^2 ≤ N :=
    (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 4)).trans hL4
  have hcard : Fintype.card (LoopArg (Gauss.Dims.exampleGrow.L N) 2) =
      (Gauss.Dims.growL N)^2 := Gauss.card_loopArg_two
  have hc0 : (0:ℝ) < ((2*Fintype.card (LoopArg (Gauss.Dims.exampleGrow.L N) 2) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by omega) Fintype.card_pos)
  have hc : ((2*Fintype.card (LoopArg (Gauss.Dims.exampleGrow.L N) 2) : ℕ) : ℝ) ≤
      (N:ℝ)^(2:ℝ) := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Real.rpow_ofNat]
    nlinarith
  have hq : (2:ℝ)*Real.log N ≤ 2*(N:ℝ) := by
    have := Real.log_le_self (show (0:ℝ) ≤ N by positivity)
    linarith
  exact rpow_card_le_exp_one hc0 (by omega : 2≤N) hc (by norm_num) hq

/-- A growing actual Gaussian family, at the first positive auxiliary net time.
The two samples and the eventual lower size threshold do not depend on p. -/
theorem eventually_exampleGrow_transition {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ4 : δ < 1/4) :
    ∀ᶠ N : ℕ in atTop,
      0 < (transitionMesh N)⁻¹ ∧
      2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ) transitionMesh N ∧
      ∀ p : ℕ, 1 ≤ p →
        APrimeSmoothWeightActual.weight Gauss.Dims.exampleGrow 0 60 δ
          (fun _ => 0) (Gauss.firstCellT τ) transitionMesh 2 p N 2 (max 1 N)
          (scalarSample Gauss.Dims.exampleGrow 0) = 1 ∧
        APrimeSmoothWeightActual.weight Gauss.Dims.exampleGrow 0 60 δ
          (fun _ => 0) (Gauss.firstCellT τ) transitionMesh 2 p N 2 (max 1 N)
          (scalarSample Gauss.Dims.exampleGrow (2/Real.sqrt ((transitionMesh N)⁻¹))) = 0 := by
  filter_upwards [eventually_firstCell_half hτ, eventually_transition_large hδ4,
    Gauss.Dims.dim_grow, eventually_ge_atTop 81] with N ht hlarge hdim hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
  have hNr : (81:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hmesh : transitionMesh N = (N:ℝ)^248 := by
    unfold transitionMesh
    rw [max_eq_right hN1]
  have hmesh0 : 0 < transitionMesh N := by rw [hmesh]; positivity
  have hp4 : (4:ℝ) ≤ (N:ℝ)^248 := by
    have hn : (N:ℝ) ≤ (N:ℝ)^248 := by
      simpa only [pow_one] using (pow_le_pow_right₀ hN1 (by norm_num : 1 ≤ 248))
    linarith
  have hk : 2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ) transitionMesh N := by
    unfold cutNetTop
    rw [ht]
    apply Nat.le_floor
    simp only [sub_zero, hmesh]
    linarith
  refine ⟨inv_pos.mpr hmesh0, hk, ?_⟩
  intro p hp
  have hWn : Gauss.Dims.growW N ≤ N := by
    have hl : 1 ≤ Gauss.Dims.growL N := le_trans (by norm_num) (Gauss.Dims.three_le_growL N)
    nlinarith [hdim.1]
  have hW : (Gauss.Dims.exampleGrow.W N : ℝ) ≤ N := by exact_mod_cast hWn
  have hWp : (Gauss.Dims.exampleGrow.W N : ℝ)^(59:ℕ) ≤ (N:ℝ)^59 :=
    pow_le_pow_left₀ (by positivity) hW _
  have hnum : 10*(Gauss.Dims.exampleGrow.W N : ℝ)^(59:ℕ) ≤ (N:ℝ)^248 := by
    calc
      _ ≤ 10*(N:ℝ)^59 := mul_le_mul_of_nonneg_left hWp (by norm_num)
      _ ≤ (N:ℝ)*(N:ℝ)^59 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (N:ℝ)^60 := by ring
      _ ≤ (N:ℝ)^248 := pow_le_pow_right₀ hN1 (by norm_num)
  have hsmall : 10*(transitionMesh N)⁻¹*(Gauss.Dims.exampleGrow.W N : ℝ)^((60:ℝ)-1) ≤ 1 := by
    rw [hmesh, show (60:ℝ)-1=59 by norm_num, Real.rpow_ofNat]
    calc
      _ = (10*(Gauss.Dims.exampleGrow.W N : ℝ)^(59:ℕ))/(N:ℝ)^248 := by ring
      _ ≤ 1 := (div_le_one (by positivity)).2 hnum
  have hcal := calibrated_two_grow N hN
  rw [Nat.max_eq_right (show 1 ≤ N by omega)]
  exact finite_transition Gauss.Dims.exampleGrow (by omega) (by omega) hp (by omega)
    hδ (by norm_num) (by rw [ht]; norm_num) (by rw [ht]; norm_num)
    hmesh0 hk hsmall hcal hlarge

#print axioms Xmat_scalarSample
#print axioms gloop_scalar_zero_energy
#print axioms weight_zeroSample_eq_one
#print axioms actual_tail_normalization_le_sixteen
#print axioms weight_transitionSample_eq_zero
#print axioms finite_transition
#print axioms eventually_exampleGrow_transition
end RBM.APrimeSmoothTransition

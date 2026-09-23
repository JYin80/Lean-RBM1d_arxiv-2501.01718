/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LoopC2
import RBM1D.Analysis.StretchedExp

/-!
# Clean smooth-prefix and canonical calibration core

This file contains the dependency-clean producer surface for the literal smooth-prefix
construction and its canonical smoothing order.
-/

set_option maxHeartbeats 1000000

namespace RBM

namespace Step2Bootstrap

variable {ι : Type*}

noncomputable def softMax (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) : ℝ :=
  (∑ i ∈ S, ρ i ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)))

theorem even_pow_nonneg (x : ℝ) (r : ℕ) : 0 ≤ x ^ (2 * r) := by
  rw [pow_mul]
  positivity

theorem sum_even_pow_nonneg (S : Finset ι) (ρ : ι → ℝ) (r : ℕ) :
    0 ≤ ∑ i ∈ S, ρ i ^ (2 * r) :=
  Finset.sum_nonneg fun _ _ => even_pow_nonneg _ _

theorem softMax_nonneg (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) : 0 ≤ softMax r S ρ :=
  Real.rpow_nonneg (sum_even_pow_nonneg _ _ _) _

theorem abs_even_pow (x : ℝ) (r : ℕ) : |x| ^ (2 * r) = x ^ (2 * r) := by
  rw [← abs_pow, abs_of_nonneg (even_pow_nonneg x r)]

theorem rpow_inv_even_pow {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    ((|x| ^ (2 * r) : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) = |x| := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  rw [← Real.rpow_natCast |x| (2 * r), ← Real.rpow_mul (abs_nonneg x)]
  push_cast
  rw [mul_one_div, div_self hr0.ne', Real.rpow_one]

theorem le_softMax {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {i : ι}
    (hi : i ∈ S) : |ρ i| ≤ softMax r S ρ := by
  have h1 : |ρ i| ^ (2 * r) ≤ ∑ j ∈ S, ρ j ^ (2 * r) := by
    rw [abs_even_pow]
    exact Finset.single_le_sum (fun j _ => even_pow_nonneg _ _) hi
  have h2 := Real.rpow_le_rpow (even_pow_nonneg |ρ i| r) h1
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)))
  rwa [rpow_inv_even_pow hr] at h2

theorem softMax_le {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ S, |ρ i| ≤ M) :
    softMax r S ρ ≤ ((S.card : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) * M := by
  have hsum : ∑ i ∈ S, ρ i ^ (2 * r) ≤ (S.card : ℝ) * M ^ (2 * r) := by
    have := Finset.sum_le_card_nsmul S (fun i => ρ i ^ (2 * r)) (M ^ (2 * r)) fun i hi => by
      rw [← abs_even_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (h i hi) _
    simpa [nsmul_eq_mul] using this
  have h2 := Real.rpow_le_rpow (sum_even_pow_nonneg S ρ r) hsum
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)))
  refine h2.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (even_pow_nonneg M r)]
  congr 1
  rw [← abs_of_nonneg hM, rpow_inv_even_pow hr, abs_of_nonneg hM]

end Step2Bootstrap

namespace Step2

open Finset Real

noncomputable def jStar (L : ℕ) [NeZero L] (f : LoopArg L 2 → ℝ)
    (W ℓu ηu D : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))) + 1

def sigPM : Fin 2 → Bool := ![true, false]

noncomputable def lk {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℂ :=
  fun a => X.Lval E N u ω (LoopData.idx (sigPM, a)) -
    B.Kval E N u (LoopData.idx (sigPM, a))

noncomputable def tT {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω) (E : ℝ) (N : ℕ) (D u ℓ : ℝ) : ℝ :=
  tailT (B.W N) (B.ell N u) (etaT E u) D ℓ

noncomputable def jS {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  jStar (B.L N) (fun a => ‖lk X E N u ω a‖)
    (B.W N) (B.ell N u) (etaT E u) D

end Step2

namespace Step2Moment

noncomputable def ratR (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  etaT E (s N) / etaT E u

theorem ratR_pos {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {N : ℕ}
    (hs : s N < 1) {u : ℝ} (hu : u < 1) : 0 < ratR E s N u :=
  div_pos (by unfold etaT; exact mul_pos (by linarith) (mE_im_pos hE))
    (by unfold etaT; exact mul_pos (by linarith) (mE_im_pos hE))

noncomputable def jSnorm {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    (X : Sample B) (E D : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  Step2.jS X E D N u ω / ratR E s N u ^ 4

theorem one_le_ratR {E : ℝ} {s : ℕ → ℝ} (hE : |E| < 2)
    {N : ℕ} {u : ℝ} (hsu : s N ≤ u) (hu : u < 1) :
    1 ≤ ratR E s N u := by
  have h1u : 0 < 1 - u := by linarith
  have hm := mE_im_pos hE
  have hratio : etaT E (s N) / etaT E u = (1 - s N) / (1 - u) := by
    unfold etaT
    field_simp
  rw [ratR, hratio, le_div_iff₀ h1u]
  linarith

end Step2Moment

namespace CutHypTheta

noncomputable def cutNetPt (s mesh : ℕ → ℝ) (N k : ℕ) : ℝ :=
  s N + (k : ℝ) / mesh N

noncomputable def cutNetTop (s t mesh : ℕ → ℝ) (N : ℕ) : ℕ :=
  ⌊(t N - s N) * mesh N⌋₊

end CutHypTheta

namespace APrimeSmoothPrefix

open Real Finset Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def regularized (f c : ι → ℝ) (ε : ℝ) (a : ι) : ℝ :=
  √(f a ^ 2 + ε ^ 2) / c a

noncomputable def smoothMax (m : ℕ) (f c : ι → ℝ) (ε : ℝ) : ℝ :=
  Step2Bootstrap.softMax m Finset.univ (regularized f c ε)

private theorem sqrt_sq_add_sq_bounds {x eps : ℝ} (hx : 0 ≤ x) (heps : 0 ≤ eps) :
    x ≤ √(x ^ 2 + eps ^ 2) ∧ √(x ^ 2 + eps ^ 2) ≤ x + eps := by
  have hsq : 0 ≤ x ^ 2 + eps ^ 2 := by positivity
  have hlow : x ^ 2 ≤ x ^ 2 + eps ^ 2 := by nlinarith [sq_nonneg eps]
  constructor
  · calc x = √(x ^ 2) := (Real.sqrt_sq hx).symm
      _ ≤ √(x ^ 2 + eps ^ 2) := Real.sqrt_le_sqrt hlow
  · have hroot := Real.sqrt_nonneg (x ^ 2 + eps ^ 2)
    have heq := Real.sq_sqrt hsq
    nlinarith [mul_nonneg hx heps]

omit [Fintype ι] [Nonempty ι] in
theorem ratio_le_regularized {f c : ι → ℝ} {ε : ℝ}
    (hf : ∀ a, 0 ≤ f a) (hc : ∀ a, 0 < c a) (hε : 0 ≤ ε) (a : ι) :
    f a / c a ≤ regularized f c ε a := by
  exact (div_le_div_iff_of_pos_right (hc a)).2 (sqrt_sq_add_sq_bounds (hf a) hε).1

omit [Fintype ι] [Nonempty ι] in
theorem regularized_le_ratio_add {f c : ι → ℝ} {ε Tmin : ℝ}
    (hf : ∀ a, 0 ≤ f a) (hc : ∀ a, 0 < c a) (hε : 0 ≤ ε)
    (hTmin : 0 < Tmin) (hmin : ∀ a, Tmin ≤ c a) (a : ι) :
    regularized f c ε a ≤ f a / c a + ε / Tmin := by
  have h1 : regularized f c ε a ≤ (f a + ε) / c a :=
    (div_le_div_iff_of_pos_right (hc a)).2 (sqrt_sq_add_sq_bounds (hf a) hε).2
  have h2 : ε / c a ≤ ε / Tmin :=
    div_le_div_of_nonneg_left hε hTmin (hmin a)
  calc regularized f c ε a ≤ (f a + ε) / c a := h1
    _ = f a / c a + ε / c a := add_div _ _ _
    _ ≤ f a / c a + ε / Tmin := by
      simpa [add_comm] using add_le_add_right h2 (f a / c a)

theorem hard_le_smooth {f c : ι → ℝ} {ε : ℝ} {m : ℕ}
    (hf : ∀ a, 0 ≤ f a) (hc : ∀ a, 0 < c a) (hε : 0 ≤ ε) (hm : 1 ≤ m) :
    (Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a)) ≤
      smoothMax m f c ε := by
  apply Finset.sup'_le
  intro a _
  exact (ratio_le_regularized hf hc hε a).trans
    ((le_abs_self _).trans (Step2Bootstrap.le_softMax hm (Finset.mem_univ a)))

theorem smooth_le_hard_add {f c : ι → ℝ} {ε Tmin : ℝ} {m : ℕ}
    (hf : ∀ a, 0 ≤ f a) (hc : ∀ a, 0 < c a) (hε : 0 ≤ ε)
    (hTmin : 0 < Tmin) (hmin : ∀ a, Tmin ≤ c a) (hm : 1 ≤ m) :
    smoothMax m f c ε ≤
      (((Finset.univ : Finset ι).card : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ)))) *
        ((Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a)) + ε / Tmin) := by
  let H : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a)
  have hH : 0 ≤ H := by
    obtain ⟨a⟩ := ‹Nonempty ι›
    exact (div_nonneg (hf a) (hc a).le).trans
      (Finset.le_sup' (fun a => f a / c a) (Finset.mem_univ a))
  have hM : 0 ≤ H + ε / Tmin := by positivity
  unfold smoothMax
  apply Step2Bootstrap.softMax_le hm hM
  intro a ha
  have hreg : 0 ≤ regularized f c ε a :=
    div_nonneg (Real.sqrt_nonneg _) (hc a).le
  rw [abs_of_nonneg hreg]
  exact (regularized_le_ratio_add hf hc hε hTmin hmin a).trans (by
    simpa only [H, add_comm] using
      (add_le_add_right (Finset.le_sup' (fun a => f a / c a) ha) (ε / Tmin)))

noncomputable def hardJ (f c : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a + 1)

theorem hardJ_eq (f c : ι → ℝ) :
    hardJ f c = 1 + Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a) := by
  unfold hardJ
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    have h := Finset.le_sup' (fun a => f a / c a) ha
    linarith
  · have h : (Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a)) ≤
        hardJ f c - 1 := by
      apply Finset.sup'_le
      intro a ha
      have h := Finset.le_sup' (fun a => f a / c a + 1) ha
      dsimp [hardJ]
      linarith
    change 1 + (Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a)) ≤ hardJ f c
    linarith

theorem hardJ_sandwich {f c : ι → ℝ} {ε Tmin : ℝ} {m : ℕ}
    (hf : ∀ a, 0 ≤ f a) (hc : ∀ a, 0 < c a) (hε : 0 ≤ ε)
    (hTmin : 0 < Tmin) (hmin : ∀ a, Tmin ≤ c a) (hm : 1 ≤ m) :
    hardJ f c ≤ 1 + smoothMax m f c ε ∧
    1 + smoothMax m f c ε ≤
      1 + (((Finset.univ : Finset ι).card : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ)))) *
        ((Finset.univ.sup' Finset.univ_nonempty (fun a => f a / c a)) + ε / Tmin) := by
  rw [hardJ_eq]
  exact ⟨by simpa [add_comm] using
      (add_le_add_left (hard_le_smooth hf hc hε hm) 1),
    by simpa [add_comm] using
      (add_le_add_left (smooth_le_hard_add hf hc hε hTmin hmin hm) 1)⟩

section Smoothness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def smoothMaxOf (m : ℕ) (F : ι → V → ℂ) (c : ι → ℝ)
    (ε : ℝ) (M : V) : ℝ :=
  smoothMax m (fun a => ‖F a M‖) c ε

theorem contDiff_smoothMaxOf {m : ℕ} (_hm : 1 ≤ m) {F : ι → V → ℂ}
    (hF : ∀ a, ContDiff ℝ 1 (F a)) {c : ι → ℝ} (hc : ∀ a, 0 < c a)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (smoothMaxOf m F c ε) := by
  let ρ : ι → V → ℝ := fun a M => regularized (fun a => ‖F a M‖) c ε a
  have hρ : ∀ a, ContDiff ℝ 1 (ρ a) := by
    intro a
    have hsq : ContDiff ℝ 1 (fun M : V => ‖F a M‖ ^ 2 + ε ^ 2) :=
      ((contDiff_norm_sq ℂ).comp (hF a)).add contDiff_const
    have hpos : ∀ M : V, 0 < ‖F a M‖ ^ 2 + ε ^ 2 := by
      intro M
      have : 0 < ε ^ 2 := sq_pos_of_pos hε
      positivity
    simpa [ρ, regularized] using (hsq.sqrt (fun M => (hpos M).ne')).div_const (c a)
  let Y : V → ℝ := fun M => ∑ a ∈ Finset.univ, ρ a M ^ (2 * m)
  have hY : ContDiff ℝ 1 Y := by
    exact ContDiff.sum (fun a _ => (hρ a).pow (2 * m))
  have hYpos : ∀ M, 0 < Y M := by
    intro M
    obtain ⟨a⟩ := ‹Nonempty ι›
    have hρpos : 0 < ρ a M := by
      dsimp [ρ, regularized]
      apply div_pos _ (hc a)
      apply Real.sqrt_pos.2
      have : 0 < ε ^ 2 := sq_pos_of_pos hε
      positivity
    have hnonneg : ∀ b ∈ (Finset.univ : Finset ι), 0 ≤ ρ b M ^ (2 * m) := by
      intro b _
      have hb : 0 ≤ ρ b M := by
        change 0 ≤ √(‖F b M‖ ^ 2 + ε ^ 2) / c b
        exact div_nonneg (Real.sqrt_nonneg _) (hc b).le
      exact pow_nonneg hb _
    have hsingle : ρ a M ^ (2 * m) ≤ Y M :=
      Finset.single_le_sum hnonneg (Finset.mem_univ a)
    exact (pow_pos hρpos _).trans_le hsingle
  have hroot : ContDiff ℝ 1 (fun M => Y M ^ ((1 : ℝ) / (2 * (m : ℝ)))) :=
    hY.rpow_const_of_ne (fun M => (hYpos M).ne')
  change ContDiff ℝ 1 (fun M => Y M ^ ((1 : ℝ) / (2 * (m : ℝ))))
  exact hroot

end Smoothness

section Model

open Gauss

noncomputable def coordFun (d : Gauss.Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Gauss.loopObs d N (zt E u) (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M -
    (Gauss.band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))

theorem contDiff_coordFun (d : Gauss.Dims) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (N : ℕ) (a : LoopArg (d.L N) 2) :
    ContDiff ℝ 1 (coordFun d E N u a) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]
    exact (mul_pos (by linarith) (mE_im_pos hE)).ne'
  have hloop : ContDiff ℝ 1
      (Gauss.loopObs d N (zt E u)
        (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))) :=
    (Gauss.bddC2_loopObs hz (abs_pos.mpr hz) le_rfl (LoopData.idx_wf _)).contDiff.of_le
      (by norm_num)
  exact hloop.sub contDiff_const

noncomputable def smoothJSMatrix (d : Gauss.Dims) (E D : ℝ) (s : ℕ → ℝ)
    (N : ℕ) (u ε : ℝ) (m : ℕ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  (1 + smoothMaxOf m (coordFun d E N u) c ε M) / (Step2Moment.ratR E s N u) ^ 4

theorem contDiff_smoothJSMatrix (d : Gauss.Dims) {E D u ε : ℝ} {s : ℕ → ℝ}
    (hE : |E| < 2) {N : ℕ} (_hs : s N < 1) (hu : u < 1)
    (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) :
    ContDiff ℝ 1 (smoothJSMatrix d E D s N u ε m) := by
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  have hc : ∀ a, 0 < c a := by
    intro a
    exact tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
  have hsm : ContDiff ℝ 1 (smoothMaxOf m (coordFun d E N u) c ε) :=
    contDiff_smoothMaxOf hm (contDiff_coordFun d hE hu N) hc hε
  change ContDiff ℝ 1 (fun M =>
    (1 + smoothMaxOf m (coordFun d E N u) c ε M) /
      (Step2Moment.ratR E s N u) ^ 4)
  exact (contDiff_const.add hsm).div_const _

noncomputable def smoothJS (d : Gauss.Dims) (E D : ℝ) (s : ℕ → ℝ)
    (N : ℕ) (u ε : ℝ) (m : ℕ) (ω : Gauss.Ω d) : ℝ :=
  let f : LoopArg (d.L N) 2 → ℝ := fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  (1 + smoothMax m f c ε) / (Step2Moment.ratR E s N u) ^ 4

theorem smoothJSMatrix_flow (d : Gauss.Dims) (E D : ℝ) (s : ℕ → ℝ)
    (N : ℕ) (u ε : ℝ) (m : ℕ) (ω : Gauss.Ω d) :
    smoothJSMatrix d E D s N u ε m (Gauss.Hflow d N u ω) =
      smoothJS d E D s N u ε m ω := by
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  have hfun : (fun a : LoopArg (d.L N) 2 =>
      ‖coordFun d E N u a (Gauss.Hflow d N u ω)‖) =
      (fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖) := by
    funext a
    unfold coordFun Step2.lk Sample.Lval
    rw [Gauss.loopObs_Hflow]
    rfl
  change (1 + smoothMax m
    (fun a => ‖coordFun d E N u a (Gauss.Hflow d N u ω)‖) c ε) /
      (Step2Moment.ratR E s N u) ^ 4 =
    (1 + smoothMax m
      (fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖) c ε) /
      (Step2Moment.ratR E s N u) ^ 4
  rw [hfun]
  rfl

theorem smoothJS_pos (d : Gauss.Dims) {E D u ε : ℝ} {s : ℕ → ℝ}
    (hE : |E| < 2) {N : ℕ} (hs : s N < 1) (hu : u < 1)
    (m : ℕ) (ω : Gauss.Ω d) :
    0 < smoothJS d E D s N u ε m ω := by
  have hR : 0 < (Step2Moment.ratR E s N u) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs hu) _
  unfold smoothJS
  apply div_pos _ hR
  have hsm := Step2Bootstrap.softMax_nonneg m
    (Finset.univ : Finset (LoopArg (d.L N) 2))
    (regularized
      (fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖)
      (fun a => Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))) ε)
  dsimp [smoothMax]
  linarith

theorem smoothJS_le_hard (d : Gauss.Dims) {E D u ε : ℝ} {s : ℕ → ℝ}
    (hE : |E| < 2) {N : ℕ} (hs : s N < 1) (hu : u < 1)
    (hε : 0 ≤ ε) {m : ℕ} (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    smoothJS d E D s N u ε m ω ≤
      (1 + (((Finset.univ : Finset (LoopArg (d.L N) 2)).card : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) *
        ((Finset.univ.sup' Finset.univ_nonempty (fun a : LoopArg (d.L N) 2 =>
          ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
            Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)))) +
            ε / ((d.W N : ℝ) ^ (-D)))) /
      (Step2Moment.ratR E s N u) ^ 4 := by
  let f : LoopArg (d.L N) 2 → ℝ := fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast (Gauss.band d).W_pos N
  have hc : ∀ a, 0 < c a := fun a => tailT_pos hW _
  have hmin : ∀ a, (d.W N : ℝ) ^ (-D) ≤ c a := fun a => rpow_neg_le_tailT _
  have hR : 0 ≤ (Step2Moment.ratR E s N u) ^ 4 :=
    (pow_pos (Step2Moment.ratR_pos hE hs hu) _).le
  dsimp [smoothJS]
  exact div_le_div_of_nonneg_right
    (hardJ_sandwich (fun a => norm_nonneg _) hc hε
      (Real.rpow_pos_of_pos hW _) hmin hm).2 hR

end Model

end APrimeSmoothPrefix

namespace APrimeSmoothWeightActual

open Real Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

private theorem cutNetPt_mem_Icc {s t mesh : ℕ → ℝ} {N j : ℕ}
    (hst : s N ≤ t N) (hmesh : 0 < mesh N)
    (hj : j ≤ cutNetTop s t mesh N) :
    cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) := by
  have hnn : (0 : ℝ) ≤ (t N - s N) * mesh N := by
    have : (0 : ℝ) ≤ t N - s N := by linarith
    positivity
  have h1 : (j : ℝ) ≤ (t N - s N) * mesh N :=
    le_trans (by exact_mod_cast Nat.cast_le.2 hj) (Nat.floor_le hnn)
  have h2 : (j : ℝ) / mesh N ≤ t N - s N := by
    rw [div_le_iff₀ hmesh]
    exact h1
  have h3 : (0 : ℝ) ≤ (j : ℝ) / mesh N :=
    div_nonneg (Nat.cast_nonneg j) hmesh.le
  exact ⟨by simp [cutNetPt]; linarith, by simp [cutNetPt]; linarith⟩

noncomputable def epsilon (d : Gauss.Dims) (D : ℝ) (N : ℕ) : ℝ :=
  (d.W N : ℝ) ^ (-D) * (N : ℝ) ^ (-(10 : ℝ))

noncomputable def threshold (δ : ℝ) (N : ℕ) : ℝ :=
  8 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (2 * δ)

noncomputable def prefixMatrix (d : Gauss.Dims) (E D : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  softMax m (Finset.range k) (fun j =>
    APrimeSmoothPrefix.smoothJSMatrix d E D s N
      (cutNetPt s mesh N j) (epsilon d D N) m
      ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M))

noncomputable def prefixSample (d : Gauss.Dims) (E D : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (ω : Gauss.Ω d) : ℝ :=
  prefixMatrix d E D s mesh N k m (Gauss.Xmat d N ω)

theorem epsilon_pos (d : Gauss.Dims) (D : ℝ) {N : ℕ} (hN : 0 < N) :
    0 < epsilon d D N := by
  unfold epsilon
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast (Gauss.band d).W_pos N) _)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)

private theorem contDiff_softMax_of_pos {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (S : Finset ι) (hS : S.Nonempty) (m : ℕ) (hm : 1 ≤ m)
    (f : ι → V → ℝ) (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i))
    (hpos : ∀ i ∈ S, ∀ x, 0 < f i x) :
    ContDiff ℝ 1 (fun x => softMax m S (fun i => f i x)) := by
  classical
  let A : V → ℝ := fun x => ∑ i ∈ S, f i x ^ (2 * m)
  have hA : ContDiff ℝ 1 A := by
    exact ContDiff.sum (fun i hi => (hf i hi).pow (2 * m))
  have hApos : ∀ x, 0 < A x := by
    intro x
    obtain ⟨i, hi⟩ := hS
    have hterm : 0 < f i x ^ (2 * m) := pow_pos (hpos i hi x) _
    have hsum : f i x ^ (2 * m) ≤ A x :=
      Finset.single_le_sum (fun j hj => pow_nonneg (hpos j hj x).le _) hi
    exact lt_of_lt_of_le hterm hsum
  change ContDiff ℝ 1 (fun x => A x ^ ((1 : ℝ) / (2 * (m : ℝ))))
  exact hA.rpow_const_of_ne (fun x => (hApos x).ne')

theorem contDiff_prefixMatrix (d : Gauss.Dims) {E D : ℝ} {s mesh : ℕ → ℝ}
    {N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    ContDiff ℝ 1 (prefixMatrix d E D s mesh N k m) := by
  classical
  by_cases hk : k = 0
  · subst hk
    have hzero : prefixMatrix d E D s mesh N 0 m = fun _ => (0 : ℝ) := by
      funext M
      simp only [prefixMatrix, softMax, Finset.range_zero, Finset.sum_empty]
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < 1 / (2 * (m : ℝ))))
    rw [hzero]
    exact contDiff_const
  · have hnonempty : (Finset.range k).Nonempty := by
      exact ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)⟩
    let f : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ := fun j M =>
      APrimeSmoothPrefix.smoothJSMatrix d E D s N
        (cutNetPt s mesh N j) (epsilon d D N) m
        ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)
    have hf : ∀ j ∈ Finset.range k, ContDiff ℝ 1 (f j) := by
      intro j hj
      have hbase := APrimeSmoothPrefix.contDiff_smoothJSMatrix d
        (E := E) (D := D) (u := cutNetPt s mesh N j)
        (ε := epsilon d D N) (s := s) (N := N) (m := m)
        hE hs (hu j (Finset.mem_range.mp hj)) (epsilon_pos d D hN) hm
      have hline : ContDiff ℝ 1
          (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
            (Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) := by
        have hc : ContDiff ℝ 1
            (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
              Real.sqrt (cutNetPt s mesh N j)) := contDiff_const
        have hi : ContDiff ℝ 1
            (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => M) := contDiff_id
        convert (hc.smul hi) using 1
      exact hbase.comp hline
    have hpos : ∀ j ∈ Finset.range k, ∀ M, 0 < f j M := by
      intro j hj M
      have hR : 0 < (Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4 :=
        pow_pos (Step2Moment.ratR_pos hE hs (hu j (Finset.mem_range.mp hj))) _
      have hsoft : 0 ≤ APrimeSmoothPrefix.smoothMaxOf m
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j))
          (fun a : LoopArg (d.L N) 2 =>
            Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
              (zdist (d.L N) (a 0 - a 1))) (epsilon d D N)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) :=
        softMax_nonneg _ _ _
      exact div_pos (by linarith) hR
    change ContDiff ℝ 1 (fun M => softMax m (Finset.range k) (fun j => f j M))
    exact contDiff_softMax_of_pos _ hnonempty m hm f hf hpos

theorem smoothJS_le_card_mul_jSnorm_add (d : Gauss.Dims)
    {E D u : ℝ} {s : ℕ → ℝ} {N m : ℕ}
    (hE : |E| < 2) (hsu : s N ≤ u) (hu : u < 1)
    (hN : 0 < N) (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    APrimeSmoothPrefix.smoothJS d E D s N u (epsilon d D N) m ω ≤
      ((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) *
      (Step2Moment.jSnorm (Gauss.sample d) E D s N u ω +
        (N : ℝ) ^ (-(10 : ℝ))) := by
  let A : ℝ := (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
    ((1 : ℝ) / (2 * (m : ℝ)))
  let R : ℝ := (Step2Moment.ratR E s N u) ^ 4
  let H : ℝ := (Finset.univ : Finset (LoopArg (d.L N) 2)).sup'
    Finset.univ_nonempty (fun a =>
      ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)))
  have hR1 : 1 ≤ R := one_le_pow₀ (Step2Moment.one_le_ratR hE hsu hu)
  have hR0 : 0 < R := by linarith
  have hA1 : 1 ≤ A := by
    have hcard : (1 : ℝ) ≤ Fintype.card (LoopArg (d.L N) 2) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.one_le_rpow hcard (by positivity)
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast (Gauss.band d).W_pos N
  have hH0 : 0 ≤ H := by
    let a : LoopArg (d.L N) 2 := Classical.choice inferInstance
    have hc : 0 < Step2.tT (Gauss.band d) E N D u
        (zdist (d.L N) (a 0 - a 1)) := tailT_pos hW _
    have ht : 0 ≤ ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)) :=
      div_nonneg (norm_nonneg _) hc.le
    exact ht.trans (by simpa only [H] using (Finset.le_sup'
      (fun b : LoopArg (d.L N) 2 =>
        ‖Step2.lk (Gauss.sample d) E N u ω b‖ /
          Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (b 0 - b 1)))
      (Finset.mem_univ a)))
  have hJ : Step2Moment.jSnorm (Gauss.sample d) E D s N u ω = (H + 1) / R := by
    change Step2.jS (Gauss.sample d) E D N u ω / R = _
    congr 1
  have hε : 0 < epsilon d D N := epsilon_pos d D hN
  have hepsratio : epsilon d D N / (d.W N : ℝ) ^ (-D) =
      (N : ℝ) ^ (-(10 : ℝ)) := by
    unfold epsilon
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hW _)]
  have hsm := APrimeSmoothPrefix.smoothJS_le_hard d
    (E := E) (D := D) (u := u) (ε := epsilon d D N) (s := s) (N := N) (m := m)
    hE (hsu.trans_lt hu) hu hε.le hm ω
  rw [hepsratio] at hsm
  have hsm' : APrimeSmoothPrefix.smoothJS d E D s N u (epsilon d D N) m ω ≤
      (1 + A * (H + (N : ℝ) ^ (-(10 : ℝ)))) / R := by
    simpa only [A, R, H, Finset.card_univ] using hsm
  have hn10 : 0 ≤ (N : ℝ) ^ (-(10 : ℝ)) := by positivity
  have hn10R : (N : ℝ) ^ (-(10 : ℝ)) / R ≤ (N : ℝ) ^ (-(10 : ℝ)) := by
    apply (div_le_iff₀ hR0).2
    nlinarith [mul_nonneg hn10 (sub_nonneg.mpr hR1)]
  rw [hJ]
  change APrimeSmoothPrefix.smoothJS d E D s N u (epsilon d D N) m ω ≤
    A * ((H + 1) / R + (N : ℝ) ^ (-(10 : ℝ)))
  calc
    _ ≤ (1 + A * (H + (N : ℝ) ^ (-(10 : ℝ)))) / R := hsm'
    _ ≤ (A * (1 + H + (N : ℝ) ^ (-(10 : ℝ)))) / R := by
      apply div_le_div_of_nonneg_right _ hR0.le
      nlinarith
    _ = A * ((H + 1) / R + (N : ℝ) ^ (-(10 : ℝ)) / R) := by ring
    _ ≤ A * ((H + 1) / R + (N : ℝ) ^ (-(10 : ℝ))) := by gcongr

theorem prefixSample_le_of_jSnorm_bound (d : Gauss.Dims)
    {E D B : ℝ} {s t mesh : ℕ → ℝ} {N k m : ℕ}
    (hE : |E| < 2) (hst : s N ≤ t N) (ht : t N < 1)
    (hmesh : 0 < mesh N) (hN : 0 < N) (hm : 1 ≤ m)
    (hk : k ≤ cutNetTop s t mesh N) (hB0 : 0 ≤ B)
    (ω : Gauss.Ω d)
    (hJ : ∀ j < k, Step2Moment.jSnorm (Gauss.sample d) E D s N
      (cutNetPt s mesh N j) ω ≤ B) :
    prefixSample d E D s mesh N k m ω ≤
      (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) *
      (B + (N : ℝ) ^ (-(10 : ℝ))) := by
  classical
  let A : ℝ := (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
    ((1 : ℝ) / (2 * (m : ℝ)))
  have hA0 : 0 ≤ A := by positivity
  have hJsm : ∀ j ∈ Finset.range k,
      APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N j)
        (epsilon d D N) m ω ≤ A * (B + (N : ℝ) ^ (-(10 : ℝ))) := by
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have huIcc := cutNetPt_mem_Icc hst hmesh (hjk.le.trans hk)
    have hinner := smoothJS_le_card_mul_jSnorm_add d
      (E := E) (D := D) (u := cutNetPt s mesh N j) (s := s) (N := N) (m := m)
      hE huIcc.1 (huIcc.2.trans_lt ht) hN hm ω
    calc
      _ ≤ A * (Step2Moment.jSnorm (Gauss.sample d) E D s N
          (cutNetPt s mesh N j) ω + (N : ℝ) ^ (-(10 : ℝ))) := hinner
      _ ≤ A * (B + (N : ℝ) ^ (-(10 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [add_comm] using
          (add_le_add_right (hJ j hjk) ((N : ℝ) ^ (-(10 : ℝ))))) hA0
  have hM0 : 0 ≤ A * (B + (N : ℝ) ^ (-(10 : ℝ))) := by positivity
  have heq : prefixSample d E D s mesh N k m ω =
      softMax m (Finset.range k) (fun j =>
        APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N j)
          (epsilon d D N) m ω) := by
    change softMax m (Finset.range k) (fun j =>
      APrimeSmoothPrefix.smoothJSMatrix d E D s N (cutNetPt s mesh N j)
        (epsilon d D N) m
        ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • Gauss.Xmat d N ω)) = _
    apply congrArg (fun f : ℕ → ℝ => softMax m (Finset.range k) f)
    funext j
    have hflow := APrimeSmoothPrefix.smoothJSMatrix_flow d E D s N
      (cutNetPt s mesh N j) (epsilon d D N) m ω
    rw [Gauss.Hflow_eq_realSmul] at hflow
    exact hflow
  rw [heq]
  have houter := softMax_le hm hM0 (S := Finset.range k)
    (ρ := fun j => APrimeSmoothPrefix.smoothJS d E D s N
      (cutNetPt s mesh N j) (epsilon d D N) m ω)
    (M := A * (B + (N : ℝ) ^ (-(10 : ℝ)))) (by
      intro j hj
      have huIcc := cutNetPt_mem_Icc hst hmesh ((Finset.mem_range.mp hj).le.trans hk)
      rw [abs_of_pos (APrimeSmoothPrefix.smoothJS_pos d hE
        (huIcc.1.trans_lt (huIcc.2.trans_lt ht)) (huIcc.2.trans_lt ht) m ω)]
      exact hJsm j hj)
  calc
    _ ≤ (k : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) *
        (A * (B + (N : ℝ) ^ (-(10 : ℝ)))) := by
          simpa only [Finset.card_range] using houter
    _ = (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ)))) *
          (B + (N : ℝ) ^ (-(10 : ℝ))) := by
            rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
            ring

noncomputable def canonicalM (d : Gauss.Dims) (s t mesh : ℕ → ℝ) (N : ℕ) : ℕ :=
  cutNetTop s t mesh N * Fintype.card (LoopArg (d.L N) 2) + 1

theorem canonicalM_pos (d : Gauss.Dims) (s t mesh : ℕ → ℝ) (N : ℕ) :
    1 ≤ canonicalM d s t mesh N := by
  unfold canonicalM
  omega

private theorem card_calib_top_local (n k : ℕ) (hk : k ≤ n) :
    (k : ℝ) ^ ((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) ≤ Real.exp 1 := by
  have hd : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  have he : (0 : ℝ) < (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) := by positivity
  by_cases hk0 : k = 0
  · subst k
    push_cast
    have he' : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    rw [Real.zero_rpow he'.ne']
    exact (Real.exp_pos 1).le
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hlog : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
    have hkn : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ_of_le hk
    rw [Real.rpow_def_of_pos hkpos]
    apply Real.exp_le_exp.mpr
    have hden : Real.log (k : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by linarith
    simpa [div_eq_mul_inv] using (div_le_one hd).mpr hden

theorem canonicalM_calibration (d : Gauss.Dims) (s t mesh : ℕ → ℝ)
    (N k : ℕ) (hk : k ≤ cutNetTop s t mesh N) :
    (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1 : ℝ) / (2 * (canonicalM d s t mesh N : ℝ)))) ≤ Real.exp 1 := by
  unfold canonicalM
  exact card_calib_top_local
    (cutNetTop s t mesh N * Fintype.card (LoopArg (d.L N) 2))
    (k * Fintype.card (LoopArg (d.L N) 2))
    (Nat.mul_le_mul_right _ hk)

end APrimeSmoothWeightActual

end RBM

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeWeight
import RBM1D.Gauss.MomentDuhamelBddT

/-!
# T314: a smooth finite-coordinate surrogate for the actual `jSnorm`

The regularized coordinate is `sqrt (‖z‖² + ε²) / T`.  All statements in this
file are finite-dimensional and use neither a good event nor a first-pass moment bound.
-/

namespace RBM
namespace APrimeSmoothPrefix

open Real Finset Step2Bootstrap
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def regularized (f c : ι → ℝ) (ε : ℝ) (a : ι) : ℝ :=
  √(f a ^ 2 + ε ^ 2) / c a

noncomputable def smoothMax (m : ℕ) (f c : ι → ℝ) (ε : ℝ) : ℝ :=
  Step2Bootstrap.softMax m Finset.univ (regularized f c ε)

private theorem sqrt_sq_add_sq_bounds {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    x ≤ √(x ^ 2 + ε ^ 2) ∧ √(x ^ 2 + ε ^ 2) ≤ x + ε := by
  have hsq : 0 ≤ x ^ 2 + ε ^ 2 := by positivity
  have hlow : x ^ 2 ≤ x ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ε]
  constructor
  · calc x = √(x ^ 2) := (Real.sqrt_sq hx).symm
      _ ≤ √(x ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt hlow
  · have hroot := Real.sqrt_nonneg (x ^ 2 + ε ^ 2)
    have heq := Real.sq_sqrt hsq
    nlinarith [mul_nonneg hx hε]

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
  apply contDiff_iff_contDiffAt.mpr
  intro M
  have hz : (zt E u).im ≠ 0 := Gauss.zt_im_ne_zero_of_lt_one hE hu
  have hloop := Gauss.contDiffAt_loopObs_zt_pair E hz
    (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M
  have hp : ContDiffAt ℝ 1
      (fun M' : Matrix (d.Idx N) (d.Idx N) ℂ => (u, M')) M :=
    contDiffAt_const.prodMk contDiffAt_id
  have hcomp := (hloop.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp M hp
  convert hcomp.sub contDiffAt_const using 1 <;> rfl

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
    exact congrArg norm
      (Gauss.lk_eq_loopObs_sub (d := d) (E := E) (N := N) (u := u) ω a).symm
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

theorem jSnorm_le_smoothJS (d : Gauss.Dims) {E D u ε : ℝ} {s : ℕ → ℝ}
    (hE : |E| < 2) {N : ℕ} (hs : s N < 1) (hu : u < 1)
    (hε : 0 ≤ ε) {m : ℕ} (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω ≤
      smoothJS d E D s N u ε m ω := by
  let f : LoopArg (d.L N) 2 → ℝ := fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  have hc : ∀ a, 0 < c a := by
    intro a
    exact tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast (Gauss.band d).W_pos N
  have hnum : Step2.jS (Gauss.sample d) E D N u ω = hardJ f c := by
    rw [hardJ_eq]
    simp only [Step2.jS, Step2.jStar, Step2.tT, f, c,
      Gauss.band_W, Gauss.band_L]
    conv_lhs => rw [add_comm]
    congr 1
  have hR : 0 < (Step2Moment.ratR E s N u) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs hu) _
  rw [Step2Moment.jSnorm, smoothJS, hnum]
  exact div_le_div_of_nonneg_right
    (hardJ_sandwich (fun a => norm_nonneg _) hc hε
      (Real.rpow_pos_of_pos hW _) (by
        intro a
        exact rpow_neg_le_tailT _) hm).1 hR.le

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

theorem first_cell_witness (d : Gauss.Dims) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) 0 0 (fun _ => 0) N (1 / 4) ω ≤
      smoothJS d 0 0 (fun _ => 0) N (1 / 4) ε 1 ω ∧
    0 < smoothJS d 0 0 (fun _ => 0) N (1 / 4) ε 1 ω ∧
    ContDiff ℝ 1 (smoothJSMatrix d 0 0 (fun _ => 0) N (1 / 4) ε 1) := by
  refine ⟨jSnorm_le_smoothJS d (by norm_num) (by norm_num) (by norm_num)
    hε.le (by norm_num) ω,
    smoothJS_pos d (by norm_num) (by norm_num) (by norm_num) 1 ω,
    contDiff_smoothJSMatrix d (by norm_num) (by norm_num) (by norm_num)
      hε (by norm_num)⟩

end Model

end APrimeSmoothPrefix
end RBM

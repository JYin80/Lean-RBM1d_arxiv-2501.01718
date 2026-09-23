/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.XiLKTwoCutMoment
import RBM1D.Gauss.Step2Bootstrap
import RBM1D.Gauss.APrimeRatioBdd
import RBM1D.Gauss.APrimeDuhamel
import RBM1D.Gauss.APrimeGronwall
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.Step1Hyp
import RBM1D.Flow.Thm221Bare

/-!
# T619: the all-charge smooth-prefix localizer

This file constructs one regularized `2r`-smooth maximum over all pairs consisting of an
earlier target-mesh point and an arbitrary two-loop charge/label.  All times are evaluated on
the same Gaussian base matrix.  The resulting moment-order-`P` cutoff is a `Gauss.WeightC1`;
both its ordinary support and the support of one Gaussian coordinate derivative imply the
same running cap for the actual all-charge `Sample.xiLK`.

Only the pre-Step-3 loop modulus is used.  In particular this module does not use (2.77), a
`CutHypEvOnSlot`, an A-prime family, `jSnorm`, or a first-cell producer.
-/

namespace RBM.Gauss.XiLKTwoSmoothPrefix

open Filter Real Set
open RBM Step2Bootstrap MomentDuhamelCut CutHypTheta Cutoff
open scoped Matrix.Norms.L2Operator

noncomputable section

private abbrev targetMesh : ℕ → ℝ := meshK 21 ((1 : ℝ) / 2)

/-- The literal all-charge normalized two-loop coordinate, as a function of the matrix. -/
noncomputable def twoCoordFun (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (q : LoopData (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ((band d).scale E N u ^ 2 : ℝ) •
    (loopObs d N (zt E u) q.idx M - (band d).Kval E N u q.idx)

/-- A fixed positive polynomial regularizer. -/
noncomputable def twoPrefixEpsilon (N : ℕ) : ℝ := (N : ℝ) ^ (-(10 : ℝ))

/-- One regularized `2r`-smooth maximum over `Fin k × LoopData (L_N) 2`. -/
noncomputable def twoPrefixMatrix (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (N k r : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  softMax r (Finset.univ : Finset (Fin k × LoopData (d.L N) 2)) (fun iq =>
    √(‖twoCoordFun d E N (cutNetPt s targetMesh N iq.1) iq.2
      ((Real.sqrt (cutNetPt s targetMesh N iq.1) : ℂ) • M)‖ ^ 2 +
        twoPrefixEpsilon N ^ 2))

/-- The common-base-sample version of `twoPrefixMatrix`. -/
noncomputable def twoPrefixSample (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (N k r : ℕ) (omega : Ω d) : ℝ :=
  twoPrefixMatrix d E s N k r (Xmat d N omega)

/-- The cutoff base at internal threshold `2 e * twoCutLevel`. -/
noncomputable def twoPrefixBase (d : Dims) (E : ℝ) (s : ℕ → ℝ) (delta : ℝ)
    (N k r : ℕ) (omega : Ω d) : ℝ :=
  cutChi (twoPrefixSample d E s N k r omega /
    (2 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N))

/-- The order-`2P` all-charge smooth-prefix weight. -/
noncomputable def twoPrefixWeight (d : Dims) (E : ℝ) (s : ℕ → ℝ) (delta : ℝ)
    (N k P r : ℕ) (omega : Ω d) : ℝ :=
  twoPrefixBase d E s delta N k r omega ^ (2 * P)

private noncomputable def twoPrefixWeightMatrix (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (delta : ℝ) (N k P r : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  cutChi (twoPrefixMatrix d E s N k r M /
    (2 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N)) ^ (2 * P)

/-- The Gaussian coordinate derivative of `twoPrefixWeight`. -/
noncomputable def twoPrefixWeightD (d : Dims) (E : ℝ) (s : ℕ → ℝ) (delta : ℝ)
    (N k P r : ℕ) (a : d.Idx N × d.Idx N × Bool) (omega : Ω d) : ℝ :=
  fderiv ℝ (twoPrefixWeightMatrix d E s delta N k P r) (Xmat d N omega)
    (Bmat d N a.1 a.2.1 a.2.2)

theorem twoPrefixWeight_eq_matrix (d : Dims) (E : ℝ) (s : ℕ → ℝ) (delta : ℝ)
    (N k P r : ℕ) (omega : Ω d) :
    twoPrefixWeight d E s delta N k P r omega =
      twoPrefixWeightMatrix d E s delta N k P r (Xmat d N omega) := rfl

theorem twoPrefixEpsilon_pos {N : ℕ} (hN : 0 < N) : 0 < twoPrefixEpsilon N := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem twoCoordFun_flow_norm (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (q : LoopData (d.L N) 2) (omega : Ω d) :
    ‖twoCoordFun d E N u q
      ((Real.sqrt u : ℂ) • Xmat d N omega)‖ =
      XiLKTwoCutMoment.twoXiCoord d E N u omega q := by
  rw [twoCoordFun, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [show ((Real.sqrt u : ℂ) • Xmat d N omega) = Hflow d N u omega by rfl]
  change (band d).scale E N u ^ 2 *
      ‖loopObs d N (zt E u) q.idx (Hflow d N u omega) - (band d).Kval E N u q.idx‖ = _
  rw [loopObs_Hflow]
  rfl

theorem twoXiCoord_le_xiLK (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (omega : Ω d) (q : LoopData (d.L N) 2) :
    XiLKTwoCutMoment.twoXiCoord d E N u omega q ≤ (sample d).xiLK E N u omega 2 := by
  simpa [XiLKTwoCutMoment.twoXiCoord, Sample.xiLK, mul_comm] using
    (mul_le_mul_of_nonneg_right
      (SumZeroDyn.norm_lkT_le (sample d) E N u omega q.1 q.2)
      (sq_nonneg ((band d).scale E N u)))

theorem xiLK_two_eq_iSup_twoXiCoord (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (omega : Ω d) :
    (sample d).xiLK E N u omega 2 =
      ⨆ q : LoopData (d.L N) 2, XiLKTwoCutMoment.twoXiCoord d E N u omega q := by
  rw [Sample.xiLK, Sample.lkMax, Real.iSup_mul_of_nonneg (sq_nonneg _)]
  congr 1
  funext q
  change (sample d).lkErr E N u omega q.idx * (band d).scale E N u ^ 2 =
    (band d).scale E N u ^ 2 * ‖SumZeroDyn.lkT (sample d) E N u omega q.1 q.2‖
  rw [SumZeroDyn.norm_lkT]
  exact mul_comm _ _

/-- Every all-charge length-two error vanishes at the deterministic initial time. -/
theorem xiLK_two_zero_at_initial (d : Dims) {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (omega : Ω d) :
    (sample d).xiLK E N 0 omega 2 = 0 := by
  have hlk : (sample d).lkMax E N 0 omega 2 = 0 := by
    apply le_antisymm
    · apply ciSup_le
      intro q
      exact le_of_eq ((sample d).lkErr_zero hE.le N omega q.idx
        (LoopData.idx_wf q) (by simp only [LoopData.idx_length]; omega))
    · exact (sample d).lkMax_nonneg
  simp [Sample.xiLK, hlk]

private theorem iSup_abs_sub_le_of_forall {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |f i - g i| ≤ C) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ C := by
  have hfg : (⨆ i, f i) ≤ (⨆ i, g i) + C := by
    apply ciSup_le
    intro i
    have hi : f i ≤ g i + C := by linarith [h i, le_abs_self (f i - g i)]
    exact hi.trans (add_le_add_left
      (le_ciSup (Set.finite_range g).bddAbove i) C)
  have hgf : (⨆ i, g i) ≤ (⨆ i, f i) + C := by
    apply ciSup_le
    intro i
    have hi : g i ≤ f i + C := by linarith [h i, neg_le_abs (f i - g i)]
    exact hi.trans (add_le_add_left
      (le_ciSup (Set.finite_range f).bddAbove i) C)
  rw [abs_le]
  constructor <;> linarith

private theorem xiLK_two_modulus_of_coord
    (d : Dims) (E : ℝ) (N : ℕ) (omega : Ω d) {u v C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ q : LoopData (d.L N) 2,
      |XiLKTwoCutMoment.twoXiCoord d E N u omega q -
        XiLKTwoCutMoment.twoXiCoord d E N v omega q| ≤ C) :
    |(sample d).xiLK E N u omega 2 - (sample d).xiLK E N v omega 2| ≤ C := by
  rw [xiLK_two_eq_iSup_twoXiCoord, xiLK_two_eq_iSup_twoXiCoord]
  exact iSup_abs_sub_le_of_forall _ _ hC h

private theorem xiLK_two_le_of_all_coord (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (omega : Ω d) {C : ℝ} (h : ∀ q : LoopData (d.L N) 2,
      XiLKTwoCutMoment.twoXiCoord d E N u omega q ≤ C) :
    (sample d).xiLK E N u omega 2 ≤ C := by
  rw [xiLK_two_eq_iSup_twoXiCoord]
  exact ciSup_le h

/-! ### Matrix regularity and the Gaussian `WeightC1` package -/

private theorem contDiff_twoCoordFun (d : Dims) {E u : ℝ} (hE : |E| < 2)
    (hu : u < 1) (N : ℕ) (q : LoopData (d.L N) 2) :
    ContDiff ℝ 1 (twoCoordFun d E N u q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro M
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu
  have hloop := contDiffAt_loopObs_zt_pair E hz q.idx M
  have hp : ContDiffAt ℝ 1
      (fun M' : Matrix (d.Idx N) (d.Idx N) ℂ => (u, M')) M :=
    contDiffAt_const.prodMk contDiffAt_id
  have hcomp := (hloop.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp M hp
  change ContDiffAt ℝ 1 (fun M' => (band d).scale E N u ^ 2 •
    (loopObs d N (zt E u) q.idx M' - (band d).Kval E N u q.idx)) M
  simpa only [Function.comp_apply] using
    (hcomp.sub contDiffAt_const).const_smul ((band d).scale E N u ^ 2)

private theorem exists_twoCoordFun_fderiv_bound (d : Dims)
    {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (N : ℕ)
    (q : LoopData (d.L N) 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M, ‖fderiv ℝ (twoCoordFun d E N u q) M‖ ≤ C := by
  let eta := etaT E u
  let C0 := 2 * (1 + eta⁻¹) ^ 3
  have heta : 0 < eta := Step2.etaT_pos' hE hu
  have hz : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact heta.ne'
  have hzeta : eta ≤ |(zt E u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos heta]
  obtain ⟨hCa, hCb, hCc⟩ := le_two_mul_one_add_inv_cube heta
  have hbdd := bddC2C_loopObs_sub (d := d) (N := N)
    hz heta hzeta hCa hCb hCc q.idx_wf ((band d).Kval E N u q.idx)
  let C1 : ℝ := (Fintype.card (d.Idx N) : ℝ) *
    ((q.idx.a.length : ℝ) * C0 ^ q.idx.a.length) + 0
  refine ⟨(band d).scale E N u ^ 2 * C1,
    mul_nonneg (sq_nonneg _) hbdd.nonneg₁, ?_⟩
  intro M
  let G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun X =>
    loopObs d N (zt E u) q.idx X - (band d).Kval E N u q.idx
  have hfd : fderiv ℝ (twoCoordFun d E N u q) M =
      (band d).scale E N u ^ 2 • fderiv ℝ G M := by
    change fderiv ℝ (((band d).scale E N u ^ 2) • G) M = _
    rw [fderiv_const_smul_field, Pi.smul_apply]
  rw [hfd, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hbdd.bdd₁ M) (sq_nonneg _)

private theorem contDiff_reg {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {F : V → ℂ}
    (hF : ContDiff ℝ 1 F) {eps : ℝ} (heps : 0 < eps) :
    ContDiff ℝ 1 (fun X => √(‖F X‖ ^ 2 + eps ^ 2)) := by
  have hsq : ContDiff ℝ 1 (fun X : V => ‖F X‖ ^ 2 + eps ^ 2) :=
    ((contDiff_norm_sq ℂ).comp hF).add contDiff_const
  exact hsq.sqrt (fun X => (by
    have hp : 0 < eps ^ 2 := sq_pos_of_pos heps
    have : 0 < ‖F X‖ ^ 2 + eps ^ 2 := by positivity
    exact this.ne'))

private theorem abs_fderiv_reg_apply_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {F : V → ℂ} (hF : ContDiff ℝ 1 F)
    {eps : ℝ} (heps : 0 < eps) (M B : V) :
    |fderiv ℝ (fun X => √(‖F X‖ ^ 2 + eps ^ 2)) M B| ≤
      ‖fderiv ℝ F M B‖ := by
  have hd : HasFDerivAt F (fderiv ℝ F M) M :=
    (hF.differentiable (by norm_num) M).hasFDerivAt
  have hsq := hd.norm_sq
  have hpos : 0 < ‖F M‖ ^ 2 + eps ^ 2 := by
    have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
    positivity
  have hr := (hsq.add_const (eps ^ 2)).sqrt hpos.ne'
  have hfd : fderiv ℝ (fun X => √(‖F X‖ ^ 2 + eps ^ 2)) M =
      (1 / (2 * √(‖F M‖ ^ 2 + eps ^ 2))) •
        (2 • (innerSL ℝ (F M)).comp (fderiv ℝ F M)) := hr.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, nsmul_eq_mul, smul_eq_mul]
  have hroot : 0 < √(‖F M‖ ^ 2 + eps ^ 2) := Real.sqrt_pos.2 hpos
  have hnorm : ‖F M‖ ≤ √(‖F M‖ ^ 2 + eps ^ 2) := by
    have h := Real.sqrt_le_sqrt
      (show ‖F M‖ ^ 2 ≤ ‖F M‖ ^ 2 + eps ^ 2 by nlinarith [sq_nonneg eps])
    simpa [Real.sqrt_sq (norm_nonneg (F M))] using h
  have hinner := abs_real_inner_le_norm (F M) (fderiv ℝ F M B)
  simp only [abs_mul, abs_of_nonneg
    (by positivity : (0 : ℝ) ≤ 1 / (2 * √(‖F M‖ ^ 2 + eps ^ 2))), Nat.cast_ofNat]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    (1 / (2 * √(‖F M‖ ^ 2 + eps ^ 2))) *
        (2 * |inner ℝ (F M) (fderiv ℝ F M B)|)
        ≤ (1 / (2 * √(‖F M‖ ^ 2 + eps ^ 2))) *
          (2 * (‖F M‖ * ‖fderiv ℝ F M B‖)) := by gcongr
    _ = (‖F M‖ / √(‖F M‖ ^ 2 + eps ^ 2)) * ‖fderiv ℝ F M B‖ := by ring
    _ ≤ ‖fderiv ℝ F M B‖ := by
      have hratio : ‖F M‖ / √(‖F M‖ ^ 2 + eps ^ 2) ≤ 1 :=
        (div_le_one hroot).2 hnorm
      nlinarith [norm_nonneg (fderiv ℝ F M B)]

private theorem contDiff_softMax_of_pos {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (S : Finset ι) (hS : S.Nonempty) (r : ℕ) (hr : 1 ≤ r)
    (f : ι → V → ℝ) (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i))
    (hpos : ∀ i ∈ S, ∀ x, 0 < f i x) :
    ContDiff ℝ 1 (fun x => softMax r S (fun i => f i x)) := by
  classical
  let A : V → ℝ := fun x => ∑ i ∈ S, f i x ^ (2 * r)
  have hA : ContDiff ℝ 1 A :=
    ContDiff.sum fun i hi => (hf i hi).pow (2 * r)
  have hApos : ∀ x, 0 < A x := by
    intro x
    obtain ⟨i, hi⟩ := hS
    exact (pow_pos (hpos i hi x) _).trans_le
      (Finset.single_le_sum (fun j hj => pow_nonneg (hpos j hj x).le _) hi)
  change ContDiff ℝ 1 (fun x => A x ^ ((1 : ℝ) / (2 * (r : ℝ))))
  exact hA.rpow_const_of_ne fun x => (hApos x).ne'

private theorem contDiff_twoPrefixMatrix (d : Dims) {E : ℝ} {s : ℕ → ℝ}
    {N k r : ℕ} (hE : |E| < 2) (hN : 0 < N) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hu : ∀ j < k, cutNetPt s targetMesh N j < 1) :
    ContDiff ℝ 1 (twoPrefixMatrix d E s N k r) := by
  classical
  letI : NeZero k := ⟨by omega⟩
  let S : Finset (Fin k × LoopData (d.L N) 2) := Finset.univ
  have hS : S.Nonempty := Finset.univ_nonempty
  let f : (Fin k × LoopData (d.L N) 2) →
      Matrix (d.Idx N) (d.Idx N) ℂ → ℝ := fun iq M =>
    √(‖twoCoordFun d E N (cutNetPt s targetMesh N iq.1) iq.2
      ((Real.sqrt (cutNetPt s targetMesh N iq.1) : ℂ) • M)‖ ^ 2 +
        twoPrefixEpsilon N ^ 2)
  have hf : ∀ iq ∈ S, ContDiff ℝ 1 (f iq) := by
    intro iq _
    have hbase := contDiff_twoCoordFun d hE (hu iq.1 iq.1.isLt) N iq.2
    have hline : ContDiff ℝ 1 (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        (Real.sqrt (cutNetPt s targetMesh N iq.1) : ℂ) • M) := by
      have hc : ContDiff ℝ 1 (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
          Real.sqrt (cutNetPt s targetMesh N iq.1)) := contDiff_const
      exact hc.smul contDiff_id
    exact contDiff_reg (hbase.comp hline) (twoPrefixEpsilon_pos hN)
  have hpos : ∀ iq ∈ S, ∀ M, 0 < f iq M := by
    intro iq _ M
    apply Real.sqrt_pos.2
    have hepssq : 0 < twoPrefixEpsilon N ^ 2 :=
      sq_pos_of_pos (twoPrefixEpsilon_pos hN)
    positivity
  change ContDiff ℝ 1 (fun M => softMax r
    (Finset.univ : Finset (Fin k × LoopData (d.L N) 2)) (fun iq =>
      √(‖twoCoordFun d E N (cutNetPt s targetMesh N iq.1) iq.2
        ((Real.sqrt (cutNetPt s targetMesh N iq.1) : ℂ) • M)‖ ^ 2 +
          twoPrefixEpsilon N ^ 2)))
  exact contDiff_softMax_of_pos S hS r hr f hf hpos

private theorem abs_fderiv_softMax_le_of_bound {V iota : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (S : Finset iota) (f : iota → V → ℂ) (c : iota → ℝ)
    (r : ℕ) (hr : 1 ≤ r) (hc : ∀ i ∈ S, 0 < c i)
    (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i)) (M B : V)
    (hY : 0 < ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ i ∈ S, ‖fderiv ℝ (f i) M B‖ / c i ≤ K) :
    |fderiv ℝ (fun X => softMax r S (fun i => ‖f i X‖ / c i)) M B| ≤
      (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K := by
  let Y : ℝ := ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r)
  let a : ℝ := (1 : ℝ) / (2 * (r : ℝ))
  have hbase := abs_fderiv_softMax_apply_le S hr hc hf M B hY
  have hpow : ∀ i ∈ S, 0 ≤ (‖f i M‖ / c i) ^ (2 * r - 1) := by
    intro i hi
    exact pow_nonneg (div_nonneg (norm_nonneg _) (hc i hi).le) _
  have hsum : ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) *
      (‖fderiv ℝ (f i) M B‖ / c i) ≤
      K * ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hK i hi) (hpow i hi)
  have hholder := sum_abs_pow_pred_le
    (S := S) (ρ := fun i => ‖f i M‖ / c i) hr
  have hholder' : ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) ≤
      (S.card : ℝ) ^ a * Y ^ (1 - a) := by
    have heq : (∑ i ∈ S, |‖f i M‖ / c i| ^ (2 * r - 1)) =
        ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (hc i hi).le)]
    rw [heq] at hholder
    simpa [Y, a] using hholder
  have hYa : 0 < Y ^ (a - 1) := Real.rpow_pos_of_pos hY _
  calc
    |fderiv ℝ (fun X => softMax r S (fun i => ‖f i X‖ / c i)) M B|
        ≤ Y ^ (a - 1) *
          ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) *
            (‖fderiv ℝ (f i) M B‖ / c i) := hbase
    _ ≤ Y ^ (a - 1) * (K * ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1)) :=
      mul_le_mul_of_nonneg_left hsum hYa.le
    _ ≤ Y ^ (a - 1) * (K * ((S.card : ℝ) ^ a * Y ^ (1 - a))) := by gcongr
    _ = (S.card : ℝ) ^ a * K := by
      have hmul : Y ^ (a - 1) * Y ^ (1 - a) = 1 := by
        rw [← Real.rpow_add hY]
        have he : a - 1 + (1 - a) = 0 := by ring
        rw [he, Real.rpow_zero]
      rw [show Y ^ (a - 1) * (K * ((S.card : ℝ) ^ a * Y ^ (1 - a))) =
          (Y ^ (a - 1) * Y ^ (1 - a)) * ((S.card : ℝ) ^ a * K) by ring,
        hmul, one_mul]

private theorem exists_twoCoordPullback_fderiv_bound (d : Dims)
    {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ)
    (q : LoopData (d.L N) 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M,
      ‖fderiv ℝ (fun X => twoCoordFun d E N u q
        ((Real.sqrt u : ℂ) • X)) M‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_twoCoordFun_fderiv_bound d hE hu1 N q
  refine ⟨Real.sqrt u * C, mul_nonneg (Real.sqrt_nonneg _) hC0, ?_⟩
  intro M
  let F := twoCoordFun d E N u q
  have hfd : fderiv ℝ (fun X => F ((Real.sqrt u : ℂ) • X)) M =
      Real.sqrt u • fderiv ℝ F (Real.sqrt u • M) := by
    rw [show (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
      F ((Real.sqrt u : ℂ) • X)) = fun X => F (Real.sqrt u • X) from rfl]
    rw [fderiv_comp_smul]
  rw [hfd, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hC _) (Real.sqrt_nonneg _)

private theorem exists_twoPrefixMatrix_fderiv_bound (d : Dims)
    {E : ℝ} {s : ℕ → ℝ} {N k r : ℕ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hN : 0 < N) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hu : ∀ j < k, cutNetPt s targetMesh N j < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M, ‖fderiv ℝ (twoPrefixMatrix d E s N k r) M‖ ≤ C := by
  classical
  letI : NeZero k := ⟨by omega⟩
  let iota := Fin k × LoopData (d.L N) 2
  let S : Finset iota := Finset.univ
  let F : iota → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun iq M =>
    twoCoordFun d E N (cutNetPt s targetMesh N iq.1) iq.2
      ((Real.sqrt (cutNetPt s targetMesh N iq.1) : ℂ) • M)
  let g : iota → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ := fun iq M =>
    √(‖F iq M‖ ^ 2 + twoPrefixEpsilon N ^ 2)
  have hu0 : ∀ j < k, 0 ≤ cutNetPt s targetMesh N j := by
    intro j hj
    unfold cutNetPt
    exact add_nonneg hs0 (div_nonneg (Nat.cast_nonneg _) (meshK_pos 21 ((1 : ℝ) / 2) N).le)
  have hF : ∀ iq : iota, ContDiff ℝ 1 (F iq) := by
    intro iq
    have hbase := contDiff_twoCoordFun d hE (hu iq.1 iq.1.isLt) N iq.2
    have hline : ContDiff ℝ 1 (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        (Real.sqrt (cutNetPt s targetMesh N iq.1) : ℂ) • M) := by
      have hc : ContDiff ℝ 1 (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
          Real.sqrt (cutNetPt s targetMesh N iq.1)) := contDiff_const
      exact hc.smul contDiff_id
    exact hbase.comp hline
  have hg : ∀ iq : iota, ContDiff ℝ 1 (g iq) := fun iq =>
    contDiff_reg (hF iq) (twoPrefixEpsilon_pos hN)
  let Ci : iota → ℝ := fun iq => Classical.choose
    (exists_twoCoordPullback_fderiv_bound d hE
      (hu0 iq.1 iq.1.isLt) (hu iq.1 iq.1.isLt) N iq.2)
  have hCi0 : ∀ iq, 0 ≤ Ci iq := fun iq =>
    (Classical.choose_spec (exists_twoCoordPullback_fderiv_bound d hE
      (hu0 iq.1 iq.1.isLt) (hu iq.1 iq.1.isLt) N iq.2)).1
  have hCi : ∀ iq M, ‖fderiv ℝ (F iq) M‖ ≤ Ci iq := fun iq M =>
    (Classical.choose_spec (exists_twoCoordPullback_fderiv_bound d hE
      (hu0 iq.1 iq.1.isLt) (hu iq.1 iq.1.isLt) N iq.2)).2 M
  obtain ⟨K, hK⟩ := Finset.exists_le (S.image Ci)
  have hK0 : 0 ≤ K := (hCi0 (Classical.choice inferInstance)).trans
    (hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hCiK : ∀ iq, Ci iq ≤ K := fun iq =>
    hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ iq))
  refine ⟨(Fintype.card iota : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K,
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hK0, ?_⟩
  intro M
  have hY : 0 < ∑ iq ∈ S, (‖((g iq M : ℝ) : ℂ)‖ / 1) ^ (2 * r) := by
    let iq : iota := Classical.choice inferInstance
    have hgi : 0 < g iq M := Real.sqrt_pos.2 (by
      have hepssq : 0 < twoPrefixEpsilon N ^ 2 :=
        sq_pos_of_pos (twoPrefixEpsilon_pos hN)
      positivity)
    have hterm : 0 < (‖((g iq M : ℝ) : ℂ)‖ / 1) ^ (2 * r) := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgi] using pow_pos hgi (2 * r)
    have hnonneg : ∀ j ∈ S, 0 ≤ (‖((g j M : ℝ) : ℂ)‖ / 1) ^ (2 * r) := by
      intro j hj
      positivity
    have hsingle : (‖((g iq M : ℝ) : ℂ)‖ / 1) ^ (2 * r) ≤
        ∑ j ∈ S, (‖((g j M : ℝ) : ℂ)‖ / 1) ^ (2 * r) := by
      exact Finset.single_le_sum hnonneg (show iq ∈ S by simp [S])
    exact hterm.trans_le hsingle
  have heq : twoPrefixMatrix d E s N k r = fun M =>
      softMax r S (fun iq => ‖((g iq M : ℝ) : ℂ)‖ / 1) := by
    funext M
    unfold twoPrefixMatrix
    congr 1
    funext iq
    simp [F, g, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [heq]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun B => ?_)
  rw [Real.norm_eq_abs]
  have hdir : ∀ iq ∈ S,
      ‖fderiv ℝ (fun X => ((g iq X : ℝ) : ℂ)) M B‖ / 1 ≤ K * ‖B‖ := by
    intro iq _
    have hof : ‖fderiv ℝ (fun X => ((g iq X : ℝ) : ℂ)) M B‖ =
        |fderiv ℝ (g iq) M B| := by
      have hd : fderiv ℝ (fun X => ((g iq X : ℝ) : ℂ)) M =
          Complex.ofRealCLM.comp (fderiv ℝ (g iq) M) :=
        (Complex.ofRealCLM.hasFDerivAt.comp M
          ((hg iq).differentiable (by norm_num) M).hasFDerivAt).fderiv
      rw [hd]
      simp [Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [div_one, hof]
    calc
      |fderiv ℝ (g iq) M B| ≤ ‖fderiv ℝ (F iq) M B‖ :=
        abs_fderiv_reg_apply_le (hF iq) (twoPrefixEpsilon_pos hN) M B
      _ ≤ ‖fderiv ℝ (F iq) M‖ * ‖B‖ := (fderiv ℝ (F iq) M).le_opNorm B
      _ ≤ Ci iq * ‖B‖ := mul_le_mul_of_nonneg_right (hCi iq M) (norm_nonneg _)
      _ ≤ K * ‖B‖ := mul_le_mul_of_nonneg_right (hCiK iq) (norm_nonneg _)
  have hbound := abs_fderiv_softMax_le_of_bound S
    (fun iq X => ((g iq X : ℝ) : ℂ)) (fun _ => (1 : ℝ)) r hr
    (fun _ _ => by norm_num)
    (fun iq _ => Complex.ofRealCLM.contDiff.comp (hg iq)) M B hY
    (K * ‖B‖) (mul_nonneg hK0 (norm_nonneg _)) hdir
  simpa only [S, Finset.card_univ, mul_assoc] using hbound

private theorem twoCutLevel_pos (d : Dims) {E delta : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hN : 0 < N) : 0 < XiLKTwoCutMoment.twoCutLevel d E s delta N := by
  unfold XiLKTwoCutMoment.twoCutLevel Step3.flowAs
  have hscale : 0 < (band d).scale E N (s N) :=
    (band d).scale_pos' hE N hs0 (hst.trans_lt ht1)
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)
    (Real.rpow_pos_of_pos hscale _)

private theorem contDiff_twoPrefixWeightMatrix (d : Dims)
    {E delta : ℝ} {s t : ℕ → ℝ} {N k P r : ℕ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hN : 0 < N) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hu : ∀ j < k, cutNetPt s targetMesh N j < 1) :
    ContDiff ℝ 1 (twoPrefixWeightMatrix d E s delta N k P r) := by
  have hprefix := contDiff_twoPrefixMatrix d hE hN hk hr hu
  have htheta : 0 < 2 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N :=
    mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (twoCutLevel_pos d hE hs0 hst ht1 hN)
  exact ((contDiff_cutChi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp
    (hprefix.div_const _)).pow (2 * P)

private theorem norm_fderiv_cutChi_pow_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : V → ℝ) (hg : ContDiff ℝ 1 g) (theta : ℝ) (htheta : 0 < theta)
    (P : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ M, ‖fderiv ℝ g M‖ ≤ C) (M : V) :
    ‖fderiv ℝ (fun X => cutChi (g X / theta) ^ (2 * P)) M‖ ≤
      ((2 * P : ℕ) : ℝ) * ((15 / 8) / theta) * C := by
  let w : V → ℝ := fun X => cutChi (g X / theta)
  have hdiv : HasFDerivAt (fun X => g X / theta)
      (theta⁻¹ • fderiv ℝ g M) M := by
    have hd := ((hg.differentiable (by norm_num) M).hasFDerivAt).const_mul (theta⁻¹ : ℝ)
    simpa [div_eq_inv_mul] using hd
  have hw : HasFDerivAt w
      (cutChiD (g M / theta) • (theta⁻¹ • fderiv ℝ g M)) M := by
    simpa only [w, Function.comp_def] using
      (hasDerivAt_cutChi (g M / theta)).comp_hasFDerivAt M hdiv
  have hwp := hw.pow (2 * P)
  have hchi0 : 0 ≤ w M := cutChi_nonneg _
  have hchi1 : w M ≤ 1 := cutChi_le_one _
  have hchipow : w M ^ (2 * P - 1) ≤ 1 := pow_le_one₀ hchi0 hchi1
  have hchid : |cutChiD (g M / theta)| ≤ 15 / 8 := abs_cutChiD_le _
  have hthetainv : 0 ≤ theta⁻¹ := inv_nonneg.mpr htheta.le
  have hcast : 0 ≤ ((2 * P : ℕ) : ℝ) := by positivity
  change ‖fderiv ℝ (fun X => w X ^ (2 * P)) M‖ ≤ _
  rw [hwp.fderiv, norm_smul, Real.norm_eq_abs, nsmul_eq_mul,
    abs_of_nonneg (mul_nonneg hcast (pow_nonneg hchi0 _))]
  calc
    ((2 * P : ℕ) : ℝ) * w M ^ (2 * P - 1) *
        ‖cutChiD (g M / theta) • (theta⁻¹ • fderiv ℝ g M)‖
      ≤ ((2 * P : ℕ) : ℝ) * ((15 / 8) * (theta⁻¹ * C)) := by
        rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hthetainv]
        have ha : theta⁻¹ * ‖fderiv ℝ g M‖ ≤ theta⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hC M) hthetainv
        have hb : |cutChiD (g M / theta)| * (theta⁻¹ * ‖fderiv ℝ g M‖) ≤
            (15 / 8) * (theta⁻¹ * C) :=
          mul_le_mul hchid ha (by positivity) (by norm_num)
        have hinner : w M ^ (2 * P - 1) *
            (|cutChiD (g M / theta)| * (theta⁻¹ * ‖fderiv ℝ g M‖)) ≤
            (15 / 8) * (theta⁻¹ * C) := by
          calc
            _ ≤ w M ^ (2 * P - 1) * ((15 / 8) * (theta⁻¹ * C)) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hchi0 _)
            _ ≤ 1 * ((15 / 8) * (theta⁻¹ * C)) :=
              mul_le_mul_of_nonneg_right hchipow (by positivity)
            _ = _ := one_mul _
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hcast
    _ = ((2 * P : ℕ) : ℝ) * ((15 / 8) / theta) * C := by
      rw [div_eq_mul_inv]
      ring

private theorem weightC1_of_matrix (d : Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ)
    (hF : ContDiff ℝ 1 F) (hval : ∀ M, |F M| ≤ 1)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ M, ‖fderiv ℝ F M‖ ≤ C) :
    WeightC1 d N (fun omega => F (Xmat d N omega))
      (fun a omega => fderiv ℝ F (Xmat d N omega)
        (Bmat d N a.1 a.2.1 a.2.2)) := by
  classical
  obtain ⟨C, hC0, hC⟩ := hbd
  let I : Finset (Coord d) := (usedCoord d N).image (crd d N)
  have hcongr : ∀ omega omega' : Ω d,
      (∀ e ∈ I, omega e = omega' e) → Xmat d N omega = Xmat d N omega' := by
    intro omega omega' h
    have hh := Hflow_congr_of_agree d N 1 omega omega' h
    simpa [Hflow_eq_realSmul] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF.continuous.comp (continuous_Xmat d N)
  · intro a _
    exact ((hF.continuous_fderiv (by norm_num)).comp (continuous_Xmat d N)).clm_apply
      continuous_const
  · exact ⟨I, fun omega omega' h => congrArg F (hcongr omega omega' h)⟩
  · intro a _
    exact ⟨I, fun omega omega' h => congrArg
      (fun M => fderiv ℝ F M (Bmat d N a.1 a.2.1 a.2.2))
      (hcongr omega omega' h)⟩
  · intro a ha omega
    have hpath := hasDerivAt_Hflow_update d N 1 omega ha
    have hpath' : HasDerivAt
        (fun x : ℝ => Xmat d N (Function.update omega (crd d N a) x))
        (Bmat d N a.1 a.2.1 a.2.2) (omega (crd d N a)) := by
      simpa [Hflow_eq_realSmul] using hpath
    have hself : Xmat d N
        (Function.update omega (crd d N a) (omega (crd d N a))) = Xmat d N omega := by simp
    have hcomp := ((hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt
      (omega (crd d N a)) hpath')
    rw [hself] at hcomp
    exact hcomp
  · exact ⟨1, fun omega => hval _⟩
  · obtain ⟨B, hB⟩ := Finset.exists_le
      ((usedCoord d N).image (fun a => ‖Bmat d N a.1 a.2.1 a.2.2‖))
    refine ⟨C * B, ?_⟩
    intro a ha omega
    have hBa : ‖Bmat d N a.1 a.2.1 a.2.2‖ ≤ B :=
      hB _ (Finset.mem_image_of_mem _ ha)
    calc
      |fderiv ℝ F (Xmat d N omega) (Bmat d N a.1 a.2.1 a.2.2)|
          ≤ ‖fderiv ℝ F (Xmat d N omega)‖ * ‖Bmat d N a.1 a.2.1 a.2.2‖ := by
            simpa [Real.norm_eq_abs] using
              (fderiv ℝ F (Xmat d N omega)).le_opNorm (Bmat d N a.1 a.2.1 a.2.2)
      _ ≤ C * ‖Bmat d N a.1 a.2.1 a.2.2‖ :=
        mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      _ ≤ C * B := mul_le_mul_of_nonneg_left hBa hC0

private theorem twoPrefixWeightC1 (d : Dims)
    {E delta : ℝ} {s t : ℕ → ℝ} {N k P r : ℕ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hN : 0 < N) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hu : ∀ j < k, cutNetPt s targetMesh N j < 1) :
    WeightC1 d N (twoPrefixWeight d E s delta N k P r)
      (twoPrefixWeightD d E s delta N k P r) := by
  let F := twoPrefixWeightMatrix d E s delta N k P r
  have hF : ContDiff ℝ 1 F :=
    contDiff_twoPrefixWeightMatrix d hE hs0 hst ht1 hN hk hr hu
  have hval : ∀ M, |F M| ≤ 1 := by
    intro M
    dsimp [F, twoPrefixWeightMatrix]
    rw [abs_of_nonneg (pow_nonneg (cutChi_nonneg _) _)]
    exact pow_le_one₀ (cutChi_nonneg _) (cutChi_le_one _)
  obtain ⟨C, hC0, hC⟩ := exists_twoPrefixMatrix_fderiv_bound d
    hE hs0 hN hk hr hu
  let theta := 2 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N
  have htheta : 0 < theta := mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
    (twoCutLevel_pos d hE hs0 hst ht1 hN)
  have hbd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ M, ‖fderiv ℝ F M‖ ≤ C' := by
    refine ⟨((2 * P : ℕ) : ℝ) * ((15 / 8) / theta) * C, by positivity, ?_⟩
    intro M
    exact norm_fderiv_cutChi_pow_le (twoPrefixMatrix d E s N k r)
      (contDiff_twoPrefixMatrix d hE hN hk hr hu) theta htheta P C hC0 hC M
  change WeightC1 d N (fun omega => F (Xmat d N omega))
    (fun a omega => fderiv ℝ F (Xmat d N omega) (Bmat d N a.1 a.2.1 a.2.2))
  exact weightC1_of_matrix d N F hF hval hbd

/-! ### Plateau and support of the single all-charge cutoff -/

private theorem sqrt_sq_add_sq_bounds {x eps : ℝ} (hx : 0 ≤ x) (heps : 0 ≤ eps) :
    x ≤ √(x ^ 2 + eps ^ 2) ∧ √(x ^ 2 + eps ^ 2) ≤ x + eps := by
  have hsum : 0 ≤ x ^ 2 + eps ^ 2 := by positivity
  constructor
  · calc
      x = √(x ^ 2) := (Real.sqrt_sq hx).symm
      _ ≤ √(x ^ 2 + eps ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg eps])
  · have hroot := Real.sqrt_nonneg (x ^ 2 + eps ^ 2)
    have heq := Real.sq_sqrt hsum
    nlinarith [mul_nonneg hx heps]

private theorem twoPrefixSample_eq_softMax (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (N k r : ℕ) (omega : Ω d) :
    twoPrefixSample d E s N k r omega =
      softMax r (Finset.univ : Finset (Fin k × LoopData (d.L N) 2)) (fun iq =>
        √(XiLKTwoCutMoment.twoXiCoord d E N
          (cutNetPt s targetMesh N iq.1) omega iq.2 ^ 2 + twoPrefixEpsilon N ^ 2)) := by
  unfold twoPrefixSample twoPrefixMatrix
  congr 2
  funext iq
  rw [twoCoordFun_flow_norm]

theorem twoPrefixBase_nonneg (d : Dims) (E : ℝ) (s : ℕ → ℝ) (delta : ℝ)
    (N k r : ℕ) (omega : Ω d) :
    0 ≤ twoPrefixBase d E s delta N k r omega := cutChi_nonneg _

theorem twoPrefixBase_le_one (d : Dims) (E : ℝ) (s : ℕ → ℝ) (delta : ℝ)
    (N k r : ℕ) (omega : Ω d) :
    twoPrefixBase d E s delta N k r omega ≤ 1 := cutChi_le_one _

private theorem twoPrefixBase_eq_one_of_prefix
    (d : Dims) {E delta : ℝ} {s t : ℕ → ℝ} {N k r : ℕ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hN : 0 < N) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hcalib : (((k * (4 * (d.L N) ^ 2) : ℕ) : ℝ) ^
      ((1 : ℝ) / (2 * (r : ℝ))) ≤ Real.exp 1))
    (heps : twoPrefixEpsilon N ≤ XiLKTwoCutMoment.twoCutLevel d E s delta N)
    (omega : Ω d)
    (hprefix : ∀ j < k, (sample d).xiLK E N
      (cutNetPt s targetMesh N j) omega 2 ≤
        XiLKTwoCutMoment.twoCutLevel d E s delta N) :
    twoPrefixBase d E s delta N k r omega = 1 := by
  let theta := XiLKTwoCutMoment.twoCutLevel d E s delta N
  have htheta : 0 < theta := twoCutLevel_pos d hE hs0 hst ht1 hN
  have heps0 : 0 ≤ twoPrefixEpsilon N := (twoPrefixEpsilon_pos hN).le
  have hentry : ∀ iq : Fin k × LoopData (d.L N) 2,
      |√(XiLKTwoCutMoment.twoXiCoord d E N
        (cutNetPt s targetMesh N iq.1) omega iq.2 ^ 2 + twoPrefixEpsilon N ^ 2)| ≤
          2 * theta := by
    intro iq
    have hcoord0 : 0 ≤ XiLKTwoCutMoment.twoXiCoord d E N
        (cutNetPt s targetMesh N iq.1) omega iq.2 := by
      exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
    have hcoord := (twoXiCoord_le_xiLK d E N _ omega iq.2).trans
      (hprefix iq.1 iq.1.isLt)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (sqrt_sq_add_sq_bounds hcoord0 heps0).2.trans (by
      dsimp [theta] at *
      linarith)
  have hcard : ((Fintype.card (Fin k × LoopData (d.L N) 2) : ℝ) ^
      ((1 : ℝ) / (2 * (r : ℝ)))) ≤ Real.exp 1 := by
    rw [Fintype.card_prod, Fintype.card_fin, XiLKTwoCutMoment.twoLoopData_card]
    exact hcalib
  have hsoft := softMax_le
    (S := (Finset.univ : Finset (Fin k × LoopData (d.L N) 2)))
    (ρ := fun iq => √(XiLKTwoCutMoment.twoXiCoord d E N
      (cutNetPt s targetMesh N iq.1) omega iq.2 ^ 2 + twoPrefixEpsilon N ^ 2))
    hr (by positivity : 0 ≤ 2 * theta) (fun iq _ => hentry iq)
  have hsoft' : twoPrefixSample d E s N k r omega ≤ 2 * Real.exp 1 * theta := by
    rw [twoPrefixSample_eq_softMax]
    calc
      _ ≤ ((Fintype.card (Fin k × LoopData (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (r : ℝ)))) * (2 * theta) := by simpa using hsoft
      _ ≤ Real.exp 1 * (2 * theta) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * Real.exp 1 * theta := by ring
  unfold twoPrefixBase
  exact cutChi_eq_one ((div_le_one (by positivity)).2 hsoft')

private theorem cutWeight_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : V → ℝ) (hg : ContDiff ℝ 1 g) (theta : ℝ) (htheta : 0 < theta)
    (P : ℕ) (M : V) :
    fderiv ℝ (fun X => cutChi (g X / theta) ^ (2 * P)) M =
      (((2 * P : ℕ) : ℝ) * cutChi (g M / theta) ^ (2 * P - 1) *
        cutChiD (g M / theta) / theta) • fderiv ℝ g M := by
  let c : V → ℝ := fun X => cutChi (g X / theta)
  have hdiv : HasFDerivAt (fun X => g X / theta)
      (theta⁻¹ • fderiv ℝ g M) M := by
    have hd := ((hg.differentiable (by norm_num) M).hasFDerivAt).const_mul (theta⁻¹ : ℝ)
    simpa [div_eq_inv_mul] using hd
  have hc : HasFDerivAt c
      (cutChiD (g M / theta) • (theta⁻¹ • fderiv ℝ g M)) M := by
    simpa only [c, Function.comp_def] using
      (hasDerivAt_cutChi (g M / theta)).comp_hasFDerivAt M hdiv
  have hpw := (hc.pow (2 * P)).fderiv
  change fderiv ℝ (fun X => c X ^ (2 * P)) M = _
  rw [hpw]
  simp only [nsmul_eq_mul, smul_smul]
  congr 1
  simp only [c]
  ring

private theorem twoPrefixBase_ne_zero_of_weightD_ne_zero
    (d : Dims) {E delta : ℝ} {s t : ℕ → ℝ} {N k P r : ℕ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hN : 0 < N) (hk : 1 ≤ k) (hP : 1 ≤ P) (hr : 1 ≤ r)
    (hu : ∀ j < k, cutNetPt s targetMesh N j < 1)
    {a : d.Idx N × d.Idx N × Bool} {omega : Ω d}
    (hne : twoPrefixWeightD d E s delta N k P r a omega ≠ 0) :
    twoPrefixBase d E s delta N k r omega ≠ 0 := by
  intro hbase
  let theta := 2 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N
  have htheta : 0 < theta := mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
    (twoCutLevel_pos d hE hs0 hst ht1 hN)
  have hg := contDiff_twoPrefixMatrix d hE hN hk hr hu
  have hfd := cutWeight_fderiv (twoPrefixMatrix d E s N k r) hg theta htheta P
    (Xmat d N omega)
  apply hne
  unfold twoPrefixWeightD twoPrefixWeightMatrix
  rw [hfd]
  have hcut : cutChi (twoPrefixMatrix d E s N k r (Xmat d N omega) / theta) = 0 := by
    simpa [twoPrefixBase, twoPrefixSample, theta] using hbase
  rw [hcut]
  have hpow : 0 < 2 * P - 1 := by omega
  simp [Nat.ne_of_gt hpow]

private theorem earlier_xiLK_le_of_base_ne_zero
    (d : Dims) {E delta : ℝ} {s t : ℕ → ℝ} {N k r : ℕ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hN : 0 < N) (hk : 1 ≤ k) (hr : 1 ≤ r)
    {omega : Ω d} (hne : twoPrefixBase d E s delta N k r omega ≠ 0) :
    ∀ j < k, (sample d).xiLK E N (cutNetPt s targetMesh N j) omega 2 ≤
      4 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N := by
  intro j hj
  apply xiLK_two_le_of_all_coord
  intro q
  let iq : Fin k × LoopData (d.L N) 2 := (⟨j, hj⟩, q)
  let theta := XiLKTwoCutMoment.twoCutLevel d E s delta N
  have htheta : 0 < theta := twoCutLevel_pos d hE hs0 hst ht1 hN
  have hinternal : 0 < 2 * Real.exp 1 * theta := by positivity
  have hcut : softW r (Finset.univ : Finset (Fin k × LoopData (d.L N) 2))
      (fun x => √(XiLKTwoCutMoment.twoXiCoord d E N
        (cutNetPt s targetMesh N x.1) omega x.2 ^ 2 + twoPrefixEpsilon N ^ 2))
      (2 * Real.exp 1 * theta) ≠ 0 := by
    simpa [softW, twoPrefixBase, theta, twoPrefixSample_eq_softMax] using hne
  have hsupp := abs_le_two_mul_of_softW_ne_zero hr hinternal hcut
    (i := iq) (Finset.mem_univ iq)
  have hcoord0 : 0 ≤ XiLKTwoCutMoment.twoXiCoord d E N
      (cutNetPt s targetMesh N j) omega q :=
    mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have hreg0 : 0 ≤ √(XiLKTwoCutMoment.twoXiCoord d E N
      (cutNetPt s targetMesh N j) omega q ^ 2 + twoPrefixEpsilon N ^ 2) :=
    Real.sqrt_nonneg _
  have hrawreg := (sqrt_sq_add_sq_bounds hcoord0 (twoPrefixEpsilon_pos hN).le).1
  calc
    XiLKTwoCutMoment.twoXiCoord d E N (cutNetPt s targetMesh N j) omega q
        ≤ √(XiLKTwoCutMoment.twoXiCoord d E N
          (cutNetPt s targetMesh N j) omega q ^ 2 + twoPrefixEpsilon N ^ 2) := hrawreg
    _ = |√(XiLKTwoCutMoment.twoXiCoord d E N
          (cutNetPt s targetMesh N j) omega q ^ 2 + twoPrefixEpsilon N ^ 2)| :=
      (abs_of_nonneg hreg0).symm
    _ ≤ 2 * (2 * Real.exp 1 * theta) := by simpa [iq] using hsupp
    _ = 4 * Real.exp 1 * XiLKTwoCutMoment.twoCutLevel d E s delta N := by
      dsimp [theta]
      ring

/-! ### The pre-Step-3 all-charge modulus -/

private theorem eventually_xiLK_two_modulus
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ omega ∈ {omega : Ω d | ‖Xmat d N omega‖ ≤ (N : ℝ)},
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |(sample d).xiLK E N u omega 2 - (sample d).xiLK E N v omega 2| ≤
          (N : ℝ) ^ (21 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
  have hfloor := rpow_neg_one_le_one_sub_of_scale_ge
    (band d) hE ht1 hc hreg.2
  have heta := eventually_etaT_inv_le_rpow (E := E) hE (a := (1 : ℝ)) hfloor
  have hX : ∀ᶠ N : ℕ in atTop, ∀ omega ∈ {omega : Ω d | ‖Xmat d N omega‖ ≤ (N : ℝ)},
      ‖Xmat d N omega‖ + 1 ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN omega homega
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have htinv : ∀ᶠ N : ℕ in atTop, (1 - t N)⁻¹ ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [hfloor, eventually_ge_atTop 1] with N hfloorN hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have htpos : 0 < 1 - t N := by linarith [ht1 N]
    have hinv : (1 - t N)⁻¹ ≤ (N : ℝ) := by
      rw [inv_le_comm₀ htpos hNpos]
      simpa [Real.rpow_neg_one] using hfloorN
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hKbEq := norm_Kval_two_le_rpow d hE ht1 htinv
  have hKb : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
        ‖(band d).Kval E N w J‖ ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [hKbEq] with N hN w hw J hJ h2 hle
    exact hN w hw J hJ (by omega)
  have hcoord := hHol_flow d hE hs0 ht1 (c := (2 : ℝ)) (by norm_num)
    (m := 2) (by norm_num) (by convert heta using 1 <;> norm_num) hX hKb
  filter_upwards [hcoord] with N hN omega homega u hu v hv
  apply xiLK_two_modulus_of_coord d E N omega
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.rpow_nonneg (abs_nonneg _) _))
  intro q
  convert hN omega homega q u hu v hv using 1 <;>
    norm_num [XiLKTwoCutMoment.twoXiCoord]

/-! ### Bundled localizer -/

/-- The all-charge smooth prefix simultaneously supplies Gaussian `C¹` regularity, the
unit plateau, and the ordinary/derivative-support running cap.  The smooth-max order `r` and
the moment order `P` remain separate parameters. -/
theorem eventually_twoPrefix_localizer
    (d : Dims) {E c delta : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hdelta : 0 < delta)
    (P : ℕ) (hP : 1 ≤ P) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (k r : ℕ),
        1 ≤ k →
        k ≤ cutNetTop s t targetMesh N →
        1 ≤ r →
        (((k * (4 * (d.L N)^2) : ℕ) : ℝ) ^
            ((1 : ℝ) / (2 * (r : ℝ))) ≤ Real.exp 1) →
        WeightC1 d N
          (twoPrefixWeight d E s delta N k P r)
          (twoPrefixWeightD d E s delta N k P r) ∧
        (∀ omega,
          0 ≤ twoPrefixBase d E s delta N k r omega ∧
          twoPrefixBase d E s delta N k r omega ≤ 1) ∧
        (∀ omega,
          (∀ j < k,
            (sample d).xiLK E N
              (cutNetPt s targetMesh N j) omega 2 ≤
                XiLKTwoCutMoment.twoCutLevel d E s delta N) →
          twoPrefixBase d E s delta N k r omega = 1) ∧
        (∀ omega,
          omega ∈ {omega | ‖Xmat d N omega‖ ≤ (N : ℝ)} →
          (twoPrefixWeight d E s delta N k P r omega ≠ 0 ∨
            ∃ a ∈ usedCoord d N,
              twoPrefixWeightD d E s delta N k P r a omega ≠ 0) →
          ∀ u ∈ Set.Icc (s N) (cutNetPt s targetMesh N k),
            (sample d).xiLK E N u omega 2 ≤
              (4 * Real.exp 1 + 2) *
                XiLKTwoCutMoment.twoCutLevel d E s delta N) := by
  have hmod := eventually_xiLK_two_modulus d hE hs0 hst ht1 hc hreg
  have hflow : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2) := by
    filter_upwards [Step1.eventually_one_le_scale_s
      (B := band d) (s := s) (t := t) hE hst ht1 hreg.1] with N hscale
    exact Real.one_le_rpow hscale (by norm_num)
  filter_upwards [hmod, hflow, eventually_ge_atTop 1] with N hmodN hflowN hN1
  intro k r hk hkTop hr hcalib
  have hN : 0 < N := by omega
  have hmesh : 0 < targetMesh N := meshK_pos 21 ((1 : ℝ) / 2) N
  have hnetIcc : ∀ j < k, cutNetPt s targetMesh N j ∈ Set.Icc (s N) (t N) := by
    intro j hj
    apply netFinset_subset_Icc (hst N) hmesh
    apply cutNetPt_mem_netFinset
    omega
  have hu : ∀ j < k, cutNetPt s targetMesh N j < 1 := fun j hj =>
    (hnetIcc j hj).2.trans_lt (ht1 N)
  let theta := XiLKTwoCutMoment.twoCutLevel d E s delta N
  have htheta : 0 < theta := twoCutLevel_pos d hE (hs0 N) (hst N) (ht1 N) hN
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ (2 * delta) :=
    Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  have htheta1 : 1 ≤ theta := by
    dsimp [theta, XiLKTwoCutMoment.twoCutLevel]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpow) (sub_nonneg.mpr hflowN)]
  have heps1 : twoPrefixEpsilon N ≤ 1 := by
    unfold twoPrefixEpsilon
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by norm_num)
  have heps : twoPrefixEpsilon N ≤ theta := heps1.trans htheta1
  refine ⟨twoPrefixWeightC1 d hE (hs0 N) (hst N) (ht1 N) hN hk hr hu,
    fun omega => ⟨twoPrefixBase_nonneg d E s delta N k r omega,
      twoPrefixBase_le_one d E s delta N k r omega⟩,
    fun omega hprefix => twoPrefixBase_eq_one_of_prefix d hE (hs0 N) (hst N)
      (ht1 N) hN hk hr hcalib heps omega hprefix, ?_⟩
  intro omega homega hsupport u huIcc
  have hbase : twoPrefixBase d E s delta N k r omega ≠ 0 := by
    rcases hsupport with hw | ⟨a, ha, hDa⟩
    · intro hb
      apply hw
      simp [twoPrefixWeight, hb, show P ≠ 0 by omega]
    · exact twoPrefixBase_ne_zero_of_weightD_ne_zero d hE (hs0 N) (hst N)
        (ht1 N) hN hk hP hr hu hDa
  have hearlier := earlier_xiLK_le_of_base_ne_zero d hE (hs0 N) (hst N)
    (ht1 N) hN hk hr hbase
  have hfine : (N : ℝ) ^ (21 : ℝ) * (1 / targetMesh N) ^ ((1 : ℝ) / 2) ≤ theta :=
    (mesh_fine_at_meshK (by norm_num : (0 : ℝ) ≤ 21)
      (by norm_num : (0 : ℝ) < 1 / 2) N).trans htheta1
  have hrun := prefix_of_modulus (s := s) (t := t)
    (Kmod := (21 : ℝ)) (γ := (1 : ℝ) / 2)
    (thr := theta) (c := 4 * Real.exp 1 * theta)
    (by norm_num : (0 : ℝ) < 1 / 2) (hst N) hmesh hk hkTop
    (hmodN omega homega) hfine hearlier u huIcc
  calc
    (sample d).xiLK E N u omega 2 ≤ 4 * Real.exp 1 * theta + theta := hrun
    _ ≤ (4 * Real.exp 1 + 2) * XiLKTwoCutMoment.twoCutLevel d E s delta N := by
      dsimp [theta]
      nlinarith [htheta.le]

/-! ### A fixed-model domain witness -/

private theorem card_calib_self (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / (2 * (((n + 1 : ℕ) : ℝ)))) ≤ Real.exp 1 := by
  have hd : (0 : ℝ) < 2 * (((n + 1 : ℕ) : ℝ)) := by positivity
  by_cases hn0 : n = 0
  · subst n
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.zero_add]
    exact (Real.exp_pos 1).le
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hnpos
    rw [Real.rpow_def_of_pos hnpos]
    apply Real.exp_le_exp.mpr
    have hden : Real.log (n : ℝ) ≤ 2 * (((n + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    simpa [div_eq_mul_inv] using (div_le_one hd).mpr hden

/-- The localization geometry is genuinely nonempty on the fixed model
`Dims.exampleGrow`: the first cell has positive duration, the `(j,q)` family is nonempty,
the smooth-max calibration has an explicit order, and the zero base sample belongs to the
operator-norm event and has zero initial all-charge error.  This is only a domain witness;
it does not assert the later full-window loop-decay event. -/
theorem positive_twoPrefix_localization_witness :
    ∃ (N k P r : ℕ) (omega : Ω Dims.exampleGrow),
      0 < cutNetPt (fun _ => (0 : ℝ)) targetMesh N k ∧
      cutNetPt (fun _ => (0 : ℝ)) targetMesh N k ≤ 1 / 2 ∧
      k ≤ cutNetTop (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) targetMesh N ∧
      1 ≤ P ∧ 1 ≤ r ∧
      (((k * (4 * (Dims.exampleGrow.L N)^2) : ℕ) : ℝ) ^
        ((1 : ℝ) / (2 * (r : ℝ))) ≤ Real.exp 1) ∧
      Nonempty (Fin k × LoopData (Dims.exampleGrow.L N) 2) ∧
      omega ∈ {omega | ‖Xmat Dims.exampleGrow N omega‖ ≤ (N : ℝ)} ∧
      (sample Dims.exampleGrow).xiLK 0 N 0 omega 2 = 0 ∧
      twoPrefixBase Dims.exampleGrow 0 (fun _ => 0) 1 N k r omega = 1 := by
  let n : ℕ := 4 * (Dims.exampleGrow.L 1)^2
  refine ⟨1, 1, 1, n + 1, 0, ?_, ?_, ?_, by norm_num, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cutNetPt]
    simp only [Nat.cast_one, zero_add]
    exact div_pos one_pos (meshK_pos 21 ((1 : ℝ) / 2) 1)
  · have hmem : cutNetPt (fun _ => (0 : ℝ)) targetMesh 1 1 ∈
        netFinset (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) targetMesh 1 := by
      apply cutNetPt_mem_netFinset
      norm_num [cutNetTop, targetMesh, meshK]
    exact (netFinset_subset_Icc (by norm_num)
      (meshK_pos 21 ((1 : ℝ) / 2) 1) _ hmem).2
  · norm_num [cutNetTop, targetMesh, meshK]
  · simpa [n] using card_calib_self n
  · infer_instance
  · have hX0 : Xmat Dims.exampleGrow 1 (0 : Ω Dims.exampleGrow) = 0 := by
      ext i j
      simp [Xmat, Xentry]
    simp [hX0]
  · exact xiLK_two_zero_at_initial Dims.exampleGrow (by norm_num) 1 0
  · have hscale : (1 : ℝ) ≤
        Step3.flowAs (band Dims.exampleGrow) 0 (fun _ => 0) 1 := by
      have hW : (1 : ℝ) ≤ Dims.exampleGrow.W 1 := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Dims.exampleGrow.W_pos 1))
      have hell : (1 : ℝ) ≤ (band Dims.exampleGrow).ell 1 0 := by
        exact one_le_ellHat (Dims.exampleGrow.L 1)
          (Dims.exampleGrow.three_le_L 1) (by norm_num) (by norm_num)
      change (1 : ℝ) ≤
        (Dims.exampleGrow.W 1 : ℝ) * (band Dims.exampleGrow).ell 1 0 * etaT 0 0
      have hm : mE 0 = Complex.I := by
        rw [mE]
        norm_num
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        push_cast
        ring
      rw [show etaT 0 0 = 1 by norm_num [etaT, hm], mul_one]
      nlinarith [mul_nonneg (sub_nonneg.mpr hW) (sub_nonneg.mpr hell)]
    have htheta : (1 : ℝ) ≤
        XiLKTwoCutMoment.twoCutLevel Dims.exampleGrow 0 (fun _ => 0) 1 1 := by
      unfold XiLKTwoCutMoment.twoCutLevel
      norm_num only [Nat.cast_one, Real.one_rpow, one_mul]
      exact Real.one_le_rpow hscale (by norm_num)
    have heps : twoPrefixEpsilon 1 ≤
        XiLKTwoCutMoment.twoCutLevel Dims.exampleGrow 0 (fun _ => 0) 1 1 := by
      simpa [twoPrefixEpsilon] using htheta
    apply twoPrefixBase_eq_one_of_prefix Dims.exampleGrow
      (E := 0) (delta := 1) (s := fun _ => 0) (t := fun _ => 1 / 2)
      (N := 1) (k := 1) (r := n + 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by omega) (by simpa [n] using card_calib_self n) heps
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [cutNetPt_zero, xiLK_two_zero_at_initial Dims.exampleGrow (by norm_num)]
    linarith

#print axioms twoCoordFun
#print axioms twoPrefixEpsilon
#print axioms twoPrefixMatrix
#print axioms twoPrefixSample
#print axioms twoPrefixBase
#print axioms twoPrefixWeight
#print axioms twoPrefixWeightD
#print axioms twoPrefixWeight_eq_matrix
#print axioms twoPrefixEpsilon_pos
#print axioms twoCoordFun_flow_norm
#print axioms twoXiCoord_le_xiLK
#print axioms xiLK_two_eq_iSup_twoXiCoord
#print axioms xiLK_two_zero_at_initial
#print axioms twoPrefixBase_nonneg
#print axioms twoPrefixBase_le_one
#print axioms eventually_twoPrefix_localizer
#print axioms positive_twoPrefix_localization_witness

end

end RBM.Gauss.XiLKTwoSmoothPrefix

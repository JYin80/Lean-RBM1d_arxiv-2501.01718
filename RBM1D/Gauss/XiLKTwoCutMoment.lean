/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.TestFunQGeneral
import RBM1D.Gauss.MomentDuhamelRhs
import RBM1D.Gauss.MomentDuhamelCut
import RBM1D.Gauss.Lemma514Q716
import RBM1D.Gauss.CutHypTheta
import RBM1D.Flow.Eq548Producer

/-!
# The positive-grid `(+,+)` two-loop cutoff Duhamel step (T596)

This module isolates the first noncircular analytic step needed for the all-charge
`Sample.xiLK ... 2` cutoff moment.  At a strictly positive point of the exact
`meshK 21 (1/2)` net it applies the closed Gaussian moment identity to every charge and label,
after multiplying each coordinate by the literal `scale^2` appearing in `xiLK`.  A finite-sum
power inequality then controls the actual all-charge maximum.  The output keeps every initial,
drift, and quadratic-variation term explicit; in particular it contains the independent
constant charge `(+,+)` rather than replacing it by the already treated `(+,-)` charge.

No Step-3 conclusion, `(2.77)`, `CutHypEvOnSlot`, A-prime family, or `jSnorm` result is used.
The missing implication is the uniform analytic absorption of these explicit family terms into
the target `N^(epsilon*p) * flowAs^(p)` budget.
-/

namespace RBM.Gauss.XiLKTwoCutMoment

open Filter MeasureTheory Real Set
open RBM.MomentDuhamel RBM.MomentDuhamelCut

noncomputable section

/-- The independent constant two-loop charge `(+,+)`. -/
def ppCharge : Fin 2 → Bool := fun _ => true

/-- One actual `(+,+)` coordinate of `Xi^(L-K)_{v,2}`, including its literal `scale^2`. -/
noncomputable def ppXiCoord (d : Dims) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω d)
    (a : LoopArg (d.L N) 2) : ℝ :=
  (band d).scale E N v ^ 2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖

/-- The cutoff level required by the slot-3 consumer. -/
noncomputable def twoCutLevel (d : Dims) (E : ℝ) (s : ℕ → ℝ) (δ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 * δ) * (Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2))

/-- One charge/label coordinate of `Xi^(L-K)_{v,2}`, with the literal `scale(v)^2`. -/
noncomputable def twoXiCoord (d : Dims) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω d)
    (q : LoopData (d.L N) 2) : ℝ :=
  (band d).scale E N v ^ 2 * ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖

/-- The exact Gaussian Duhamel right-hand side for one arbitrary two-loop charge/label. -/
noncomputable def twoCoordDuhamelRhs (d : Dims) (E : ℝ) (s : ℕ → ℝ) (N p : ℕ) (v : ℝ)
    (q : LoopData (d.L N) 2) : ℝ :=
  momNorm (band d).P (2 * p) (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.lkT (sample d) E N (s N) ω q.1) q.2‖)
    + 2 * (∫ u in (s N)..v, momNorm (band d).P (2 * p) (fun ω =>
        ‖Uker (d.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) q.1) q.2‖))
    + (cMDval' p 0 * ∫ u in (s N)..v, momNorm (band d).P p (fun ω =>
        ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (eeFun (band d) E N u ((sample d).H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^
        ((1 : ℝ) / 2)

/-- The actual two-loop charge/label family has exactly `4 * L_N^2` members. -/
theorem twoLoopData_card (d : Dims) (N : ℕ) :
    Fintype.card (LoopData (d.L N) 2) = 4 * (d.L N) ^ 2 := by
  simp [LoopData, ZMod.card]

/-- The exact right-hand side of the Gaussian two-loop Duhamel inequality for `(+,+)`. -/
noncomputable def ppDuhamelRhs (d : Dims) (E : ℝ) (s : ℕ → ℝ) (N p : ℕ) (v : ℝ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  momNorm (band d).P (2 * p) (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) ppCharge) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.lkT (sample d) E N (s N) ω ppCharge) a‖)
    + 2 * (∫ u in (s N)..v, momNorm (band d).P (2 * p) (fun ω =>
        ‖Uker (d.L N) (xiOf (mSigma E) ppCharge) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) ppCharge) a‖))
    + (cMDval' p 0 * ∫ u in (s N)..v, momNorm (band d).P p (fun ω =>
        ‖Uker (d.L N) (SumZeroDyn.xi2 E ppCharge) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (eeFun (band d) E N u ((sample d).H N u ω) ppCharge) (Fin.append a a)‖)) ^
        ((1 : ℝ) / 2)

/-- The `(+,+)` coordinate is genuinely a component of the all-charge `xiLK` maximum. -/
theorem ppXiCoord_le_xiLK (d : Dims) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω d)
    (a : LoopArg (d.L N) 2) :
    ppXiCoord d E N v ω a ≤ (sample d).xiLK E N v ω 2 := by
  simpa [ppXiCoord, Sample.xiLK, mul_comm] using
    (mul_le_mul_of_nonneg_right
      (SumZeroDyn.norm_lkT_le (sample d) E N v ω ppCharge a)
      (sq_nonneg ((band d).scale E N v)))

/-- The zeroth moment in the requested all-charge family is exactly one. -/
theorem xiLK_two_cut_moment_zero (d : Dims) (E δ : ℝ) (s : ℕ → ℝ) (N : ℕ) (v : ℝ) :
    ∫ ω, |cutTrunc (twoCutLevel d E s δ N) ((sample d).xiLK E N v ω 2)| ^ (2 * 0)
      ∂(band d).P = 1 := by
  simp

/-- The closed Gaussian Duhamel inequality for one arbitrary two-loop charge/label, after the
literal `scale(v)^2` normalization.  This is the coordinate input to the finite-family theorem
below; unlike the `(+,-)` hierarchy route, it also applies to the independent `(+,+)` charge. -/
theorem twoXiCoord_momNorm_le_duhamel_at_positive_net
    (d : Dims) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {N p : ℕ} (hp : 1 ≤ p) {v : ℝ}
    (hv : v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N) (hvpos : s N < v)
    (q : LoopData (d.L N) 2) :
    momNorm (band d).P (2 * p) (fun ω => twoXiCoord d E N v ω q)
      ≤ (band d).scale E N v ^ 2 * twoCoordDuhamelRhs d E s N p v q := by
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hst N) (meshK_pos 21 ((1 : ℝ) / 2) N) v hv
  have hduh := (momentIneq_gauss_cMDval'_closed (n := 0) d hE hs0 ht1)
    p hp N q.1 v hvpos.le hvIcc.2 q.2
  have hA2 : 0 ≤ (band d).scale E N v ^ 2 := sq_nonneg _
  change momNorm (band d).P (2 * p) (fun ω =>
      (band d).scale E N v ^ 2 *
        ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖)
      ≤ (band d).scale E N v ^ 2 * twoCoordDuhamelRhs d E s N p v q
  rw [momNorm_const_mul (by omega) hA2]
  exact mul_le_mul_of_nonneg_left (by simpa [twoCoordDuhamelRhs] using hduh) hA2

/-- A finite maximum of nonnegative coordinates has its `n`th power bounded by the sum of
the coordinate `n`th powers. -/
private theorem finsetMax_pow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    (Finset.univ.sup' Finset.univ_nonempty f) ^ n ≤ ∑ i, f i ^ n := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  rw [hmax]
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : ι => f j ^ n)
    (fun j _ => pow_nonneg (hf j) _) hi

/-- **Actual all-charge positive-grid cutoff Duhamel estimate.**

The left side is the requested `Sample.xiLK ... 2`, not a single coordinate.  Pointwise,
`lkMax` is identified with the finite maximum over `LoopData (L N) 2`; the power of that
maximum is bounded by the sum of coordinate powers with coefficient one.  Every summand on the
right is then bounded by the closed Gaussian Duhamel identity for its own charge and label.
Thus the independent `(+,+)` sector and the finite maximum are both present without any
Step-3 or A-prime input. -/
theorem xiLK_two_cut_integral_le_duhamel_family_at_positive_net
    (d : Dims) {E δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {N p : ℕ} (hp : 1 ≤ p) {v : ℝ}
    (hv : v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N) (hvpos : s N < v) :
    ∫ ω, |cutTrunc (twoCutLevel d E s δ N) ((sample d).xiLK E N v ω 2)| ^ (2 * p)
        ∂(band d).P
      ≤ ∑ q : LoopData (d.L N) 2,
          ((band d).scale E N v ^ 2 * twoCoordDuhamelRhs d E s N p v q) ^ (2 * p) := by
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hst N) (meshK_pos 21 ((1 : ℝ) / 2) N) v hv
  have hv0 : 0 ≤ v := (hs0 N).trans hvIcc.1
  have hv1 : v < 1 := hvIcc.2.trans_lt (ht1 N)
  have hA : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hA2 : 0 ≤ (band d).scale E N v ^ 2 := sq_nonneg _
  have hcoord0 : ∀ (ω : Ω d) (q : LoopData (d.L N) 2),
      0 ≤ twoXiCoord d E N v ω q := fun ω q =>
    mul_nonneg hA2 (norm_nonneg _)
  have hxiMax : ∀ ω : Ω d,
      (sample d).xiLK E N v ω 2 ≤
        (Finset.univ : Finset (LoopData (d.L N) 2)).sup' Finset.univ_nonempty
          (fun q => twoXiCoord d E N v ω q) := by
    intro ω
    have hmax : (sample d).lkMax E N v ω 2 ≤
        (Finset.univ : Finset (LoopData (d.L N) 2)).sup' Finset.univ_nonempty (fun q =>
          ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖) := by
      refine ciSup_le fun q => ?_
      rw [← SumZeroDyn.norm_lkT]
      exact Finset.le_sup'
        (fun r : LoopData (d.L N) 2 =>
          ‖SumZeroDyn.lkT (sample d) E N v ω r.1 r.2‖)
        (Finset.mem_univ q)
    calc
      (sample d).xiLK E N v ω 2 =
          (sample d).lkMax E N v ω 2 * (band d).scale E N v ^ 2 := rfl
      _ ≤ ((Finset.univ : Finset (LoopData (d.L N) 2)).sup' Finset.univ_nonempty
          (fun q => ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖)) *
            (band d).scale E N v ^ 2 := mul_le_mul_of_nonneg_right hmax hA2
      _ = (Finset.univ : Finset (LoopData (d.L N) 2)).sup' Finset.univ_nonempty
          (fun q => twoXiCoord d E N v ω q) := by
        rw [Finset.sup'_mul₀ hA2]
        apply congrArg
        funext q
        rw [twoXiCoord, mul_comm]
  have hpoint : ∀ ω : Ω d,
      |cutTrunc (twoCutLevel d E s δ N) ((sample d).xiLK E N v ω 2)| ^ (2 * p)
        ≤ ∑ q : LoopData (d.L N) 2, twoXiCoord d E N v ω q ^ (2 * p) := by
    intro ω
    have hxi0 : 0 ≤ (sample d).xiLK E N v ω 2 := (sample d).xiLK_nonneg hA.le
    have hcut0 : 0 ≤ cutTrunc (twoCutLevel d E s δ N)
        ((sample d).xiLK E N v ω 2) := cutTrunc_nonneg hxi0
    have hcutMax : cutTrunc (twoCutLevel d E s δ N)
          ((sample d).xiLK E N v ω 2) ≤
        (Finset.univ : Finset (LoopData (d.L N) 2)).sup' Finset.univ_nonempty
          (fun q => twoXiCoord d E N v ω q) :=
      (cutTrunc_le_self hxi0).trans (hxiMax ω)
    have hpow := pow_le_pow_left₀ hcut0 hcutMax (2 * p)
    rw [abs_of_nonneg hcut0]
    exact hpow.trans (finsetMax_pow_le_sum
      (fun q : LoopData (d.L N) 2 => twoXiCoord d E N v ω q) (hcoord0 ω) (2 * p))
  have hintCoord : ∀ q : LoopData (d.L N) 2,
      Integrable (fun ω => twoXiCoord d E N v ω q ^ (2 * p)) (band d).P := by
    intro q
    have hintRaw := MomentDuhamel.integrable_gauss d E s t 0 hE hs0 ht1
      (2 * p) N v hvpos.le hvIcc.2 q.1 q.2
    have heq : (fun ω => twoXiCoord d E N v ω q ^ (2 * p)) =
        fun ω => ((band d).scale E N v ^ 2) ^ (2 * p) *
          |‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖| ^ (2 * p) := by
      funext ω
      rw [twoXiCoord, mul_pow, abs_norm]
    rw [heq]
    exact hintRaw.const_mul _
  have hintSum : Integrable (fun ω =>
      ∑ q : LoopData (d.L N) 2, twoXiCoord d E N v ω q ^ (2 * p)) (band d).P :=
    integrable_finsetSum Finset.univ (fun q _ => hintCoord q)
  have hInt := integral_mono_of_nonneg
    (Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) (2 * p))
    hintSum
    (Eventually.of_forall hpoint)
  rw [integral_finsetSum Finset.univ (fun q _ => hintCoord q)] at hInt
  refine hInt.trans (Finset.sum_le_sum fun q _ => ?_)
  have hmom := twoXiCoord_momNorm_le_duhamel_at_positive_net d hE hs0 hst ht1 hp hv hvpos q
  have hpow := pow_le_pow_left₀ (momNorm_nonneg (band d).P (2 * p)
      (fun ω => twoXiCoord d E N v ω q)) hmom (2 * p)
  rw [momNorm_pow (band d).P (by omega) (fun ω => twoXiCoord d E N v ω q)] at hpow
  simpa [abs_of_nonneg (hcoord0 _ q)] using hpow

/-- **Positive-grid `(+,+)` truncated Duhamel estimate.**

The endpoint is a strictly positive point of the exact `meshK 21 (1/2)` net.  The cutoff is
the literal target cutoff and the observable carries the literal `scale(v)^2`.  The proof is
the closed Gaussian moment identity of `(5.20)`/`(5.24)`, specialized to `n=0` and
`sigma=(+,+)`, plus monotonicity under `cutTrunc`.

The two time-integral terms are intentionally retained: bounding them by the requested
`N^(epsilon*p) * flowAs^(p)` scale is precisely the remaining analytic implication. -/
theorem ppXiCoord_cut_momNorm_le_duhamel_at_positive_net
    (d : Dims) {E δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {N p : ℕ} (hp : 1 ≤ p) {v : ℝ}
    (hv : v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N) (hvpos : s N < v)
    (a : LoopArg (d.L N) 2) :
    momNorm (band d).P (2 * p) (fun ω =>
        cutTrunc (twoCutLevel d E s δ N) (ppXiCoord d E N v ω a))
      ≤ (band d).scale E N v ^ 2 * ppDuhamelRhs d E s N p v a := by
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hst N) (meshK_pos 21 ((1 : ℝ) / 2) N) v hv
  have hraw := momentIneq_gauss_cMDval'_closed (n := 0) d hE hs0 ht1
  have hduh := hraw p hp N ppCharge v hvpos.le hvIcc.2 a
  have hintRaw := MomentDuhamel.integrable_gauss d E s t 0 hE hs0 ht1
    (2 * p) N v hvpos.le hvIcc.2 ppCharge a
  let A2 : ℝ := (band d).scale E N v ^ 2
  have hA2 : 0 ≤ A2 := sq_nonneg _
  have hintScaled : Integrable (fun ω =>
      |A2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖| ^ (2 * p)) (band d).P := by
    have heq : (fun ω =>
        |A2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖| ^ (2 * p)) =
        fun ω => A2 ^ (2 * p) *
          |‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖| ^ (2 * p) := by
      funext ω
      rw [abs_mul, abs_of_nonneg hA2, mul_pow]
    rw [heq]
    exact hintRaw.const_mul _
  have hmono : momNorm (band d).P (2 * p) (fun ω =>
        cutTrunc (twoCutLevel d E s δ N)
          (A2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖))
      ≤ momNorm (band d).P (2 * p) (fun ω =>
        A2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖) := by
    refine momNorm_mono hintScaled fun ω => ?_
    have hx : 0 ≤ A2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖ :=
      mul_nonneg hA2 (norm_nonneg _)
    rw [abs_of_nonneg (cutTrunc_nonneg hx), abs_of_nonneg hx]
    exact cutTrunc_le_self hx
  rw [momNorm_const_mul (by omega) hA2] at hmono
  change momNorm (band d).P (2 * p) (fun ω =>
      cutTrunc (twoCutLevel d E s δ N)
        (A2 * ‖SumZeroDyn.lkT (sample d) E N v ω ppCharge a‖))
      ≤ A2 * ppDuhamelRhs d E s N p v a
  exact hmono.trans (mul_le_mul_of_nonneg_left (by simpa [ppDuhamelRhs] using hduh) hA2)

/-- The hypotheses of the positive-grid theorem are nondegenerate: on the window
`[0,1/2]`, the exact prescribed mesh has a strictly positive net point. -/
theorem positive_target_mesh_witness :
    ∃ N : ℕ, ∃ v : ℝ,
      v ∈ netFinset (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ))
          (meshK 21 ((1 : ℝ) / 2)) N ∧
      0 < v ∧ v ≤ 1 / 2 := by
  let s : ℕ → ℝ := fun _ => 0
  let t : ℕ → ℝ := fun _ => 1 / 2
  let mesh := meshK 21 ((1 : ℝ) / 2)
  refine ⟨1, CutHypTheta.cutNetPt s mesh 1 1, ?_, ?_, ?_⟩
  · apply CutHypTheta.cutNetPt_mem_netFinset
    norm_num [CutHypTheta.cutNetTop, mesh, meshK, s, t]
  · rw [CutHypTheta.cutNetPt]
    simp only [s, Nat.cast_one, zero_add]
    change 0 < (1 : ℝ) / mesh 1
    apply div_pos
    · norm_num
    · simpa [mesh] using meshK_pos 21 ((1 : ℝ) / 2) 1
  · have hmem : CutHypTheta.cutNetPt s mesh 1 1 ∈ netFinset s t mesh 1 := by
      apply CutHypTheta.cutNetPt_mem_netFinset
      norm_num [CutHypTheta.cutNetTop, mesh, meshK, s, t]
    exact (netFinset_subset_Icc (by norm_num [s, t])
      (meshK_pos 21 ((1 : ℝ) / 2) 1) _ hmem).2

/-- A simultaneous nondegenerate witness for every hypothesis of the positive-grid theorem. -/
theorem positive_pp_duhamel_domain_witness :
    ∃ (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (N p : ℕ) (v : ℝ),
      |E| < 2 ∧
      (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ t n) ∧ (∀ n, t n < 1) ∧
      1 ≤ p ∧
      v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N ∧ s N < v ∧
      Nonempty (LoopArg (d.L N) 2) := by
  obtain ⟨N, v, hv, hvpos, _hvend⟩ := positive_target_mesh_witness
  refine ⟨Dims.exampleGrow, 0, (fun _ => 0), (fun _ => 1 / 2), N, 1, v, ?_⟩
  exact ⟨by norm_num, (fun _ => by norm_num), (fun _ => by norm_num),
    (fun _ => by norm_num), by norm_num, hv, hvpos, ⟨fun _ => 0⟩⟩

#print axioms ppCharge
#print axioms ppXiCoord
#print axioms twoCutLevel
#print axioms twoXiCoord
#print axioms twoCoordDuhamelRhs
#print axioms twoLoopData_card
#print axioms ppDuhamelRhs
#print axioms ppXiCoord_le_xiLK
#print axioms xiLK_two_cut_moment_zero
#print axioms twoXiCoord_momNorm_le_duhamel_at_positive_net
#print axioms xiLK_two_cut_integral_le_duhamel_family_at_positive_net
#print axioms ppXiCoord_cut_momNorm_le_duhamel_at_positive_net
#print axioms positive_target_mesh_witness
#print axioms positive_pp_duhamel_domain_witness

end

end RBM.Gauss.XiLKTwoCutMoment

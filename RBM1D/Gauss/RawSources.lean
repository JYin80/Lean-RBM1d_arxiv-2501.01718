/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp
import Mathlib.Analysis.Calculus.Deriv.Abs
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.TestFunHerm
import RBM1D.Gauss.WeightedSumSqrt
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Gauss.FullQuadVar
import RBM1D.Gauss.MinorDiffCond
import RBM1D.Gauss.TwoChargeOneLoop
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.Gauss.FullQuadVar
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.Step1Hyp

/-!
# The Gaussian raw-source carrier for arbitrary dimensions

The event below puts the Gaussian norm bound and the order-three, order-four,
and order-six moving-window Step-1 estimates on one sample.  The length-four
and length-six bounds give the actual quadratic-variation `SourceEvent`.
-/

namespace RBM.RawSources

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The Gaussian norm-good event in dimension `d`. -/
def normGood (d : Dims) (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- The order-`n` moving-window raw Step-1 estimate, in dimension `d`. -/
def rawEvent (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (n N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc s t N × LoopData (d.L N) n,
    ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ * Step1.aprioriRhs (band d) E s t n N p ω}

/-- The shared Gaussian carrier for the norm bound and raw orders 3, 4, 6. -/
def sourceGood (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (N : ℕ) : Set (Ω d) :=
  normGood d N ∩ rawEvent d E s t ζ 3 N ∩
    rawEvent d E s t ζ 4 N ∩ rawEvent d E s t ζ 6 N

/-- Source scale from the band at the initial time. -/
noncomputable def sourceEll (d : Dims) (s : ℕ → ℝ) (ζ : ℝ) (N : ℕ) : ℝ :=
  (band d).ell N (s N) * (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ))

/-- The raw order-three source coefficient. -/
noncomputable def sourceC3 (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * ((band d).ell N u / (band d).ell N (s N)) ^ (2 : ℕ) *
    ((band d).scale E N u)⁻¹ ^ (2 : ℕ)

/-- The raw order-four source coefficient. -/
noncomputable def sourceC4 (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * ((band d).ell N u / (band d).ell N (s N)) ^ (3 : ℕ) *
    ((band d).scale E N u)⁻¹ ^ (3 : ℕ)

/-- The raw order-six source coefficient. -/
noncomputable def sourceC6 (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * ((band d).ell N u / (band d).ell N (s N)) ^ (5 : ℕ) *
    ((band d).scale E N u)⁻¹ ^ (5 : ℕ)

theorem sourceGood_subset_normGood (d : Dims) (E : ℝ) (s t : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) :
    sourceGood d E s t ζ N ⊆ normGood d N :=
  fun _ hω => hω.1.1.1

private theorem rawEvent_isClosed (d : Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    (ζ : ℝ) (n N : ℕ) : IsClosed (rawEvent d E s t ζ n N) := by
  have heq : rawEvent d E s t ζ n N =
      ⋂ p : TimeIcc s t N × LoopData (d.L N) n,
        {ω : Ω d |
          ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ * Step1.aprioriRhs (band d) E s t n N p ω} := by
    ext ω
    simp [rawEvent]
  rw [heq]
  apply isClosed_iInter
  intro p
  have hu : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hcont : Continuous (fun ω : Ω d =>
      ‖(sample d).Lval E N p.1 ω p.2.idx‖) := by
    simpa only [sample_Lval] using
      (continuous_gloop_Hflow d N (p.1 : ℝ)
        (zt_im_ne_zero_of_lt_one hE hu) p.2.idx).norm
  exact isClosed_le hcont (by dsimp [Step1.aprioriRhs]; fun_prop)

theorem measurableSet_sourceGood (d : Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    (ζ : ℝ) (N : ℕ) : MeasurableSet (sourceGood d E s t ζ N) := by
  exact (((Gauss.measurableSet_normX_le d N).inter
    (rawEvent_isClosed d hE ht1 ζ 3 N).measurableSet).inter
    (rawEvent_isClosed d hE ht1 ζ 4 N).measurableSet).inter
    (rawEvent_isClosed d hE ht1 ζ 6 N).measurableSet

private theorem source_level_identity {ellu ells A q : ℝ}
    (hells : 0 < ells) (hA : 0 < A) (hq : 0 < q) :
    2 * (q * (ellu / ells) ^ 5 * (A⁻¹) ^ 5) =
      (ellu / (ells * (2 * q) ^ (-(1 / 5 : ℝ)))) ^ 5 *
        (((A ^ 2)⁻¹) ^ 2) * A⁻¹ := by
  have hb : 0 < 2 * q := by positivity
  have hr : ((2 * q) ^ (-(1 / 5 : ℝ))) ^ 5 = (2 * q)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hb.le]
    norm_num [Real.rpow_neg_one]
  simp only [div_pow, mul_pow, hr]
  field_simp

theorem sourceEvent_on_sourceGood (d : Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {ζ : ℝ} (_hζ : 0 < ζ) {N : ℕ} (hN : 0 < N)
    (u : TimeIcc s t N) {ω : Ω d}
    (hω : ω ∈ sourceGood d E s t ζ N) :
    FullQuadVar.SourceEvent (sample d) E N (u : ℝ) ω
      (sourceEll d s ζ N) (sourceC4 d E s ζ N u) := by
  have h4 : ∀ p : LoopData (d.L N) 4,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC4 d E s ζ N u := by
    intro p
    have hp := hω.1.2 (u, p)
    simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC4, mul_assoc] using hp
  have h6 : ∀ p : LoopData (d.L N) 6,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC6 d E s ζ N u := by
    intro p
    have hp := hω.2 (u, p)
    simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC6, mul_assoc] using hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) ^ ζ := Real.rpow_pos_of_pos hNr _
  have hs1 : s N < 1 := u.2.1.trans_lt (u.2.2.trans_lt (ht1 N))
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hells : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N)
      (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat ((band d).L N) (s N : ℂ) by linarith)
  have hA : 0 < (band d).scale E N (u : ℝ) :=
    (band d).scale_pos' hE N ((hs0 N).trans u.2.1) hu1
  have hlevel : 2 * sourceC6 d E s ζ N (u : ℝ) ≤
      ((band d).ell N (u : ℝ) / sourceEll d s ζ N) ^ 5 *
        ((((band d).W N : ℝ) * (band d).ell N (u : ℝ) *
          etaT E (u : ℝ)) ^ 2)⁻¹ ^ 2 *
        ((band d).W N * (band d).ell N (u : ℝ) * etaT E (u : ℝ))⁻¹ := by
    unfold sourceC6 sourceEll
    exact le_of_eq (by simpa only [Band.scale] using
      (source_level_identity
        (ellu := (band d).ell N (u : ℝ))
        (ells := (band d).ell N (s N))
        (A := (band d).scale E N (u : ℝ))
        (q := (N : ℝ) ^ ζ) hells hA hq))
  exact FullQuadVar.sourceEvent_of_step1 (sample d) E N (u : ℝ) ω h4 h6 hlevel

theorem rawThree_on_sourceGood (d : Dims) {E : ℝ} {s t : ℕ → ℝ}
    {ζ : ℝ} {N : ℕ} (u : TimeIcc s t N) {ω : Ω d}
    (hω : ω ∈ sourceGood d E s t ζ N) :
    ∀ p : LoopData (d.L N) 3,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC3 d E s ζ N u := by
  intro p
  have hp := hω.1.1.2 (u, p)
  simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC3, mul_assoc] using hp

end
end RBM.RawSources

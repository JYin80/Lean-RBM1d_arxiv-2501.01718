/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Exp
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
import RBM1D.Gauss.Lemma514Moment
import RBM1D.Gauss.QVEndpoint
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.MinorDiffCond

/-!
# Arbitrary-dimension deterministic-selector singleton local law

The generic length-two Step-1 estimate, Lemma 4.1, and simultaneous weak-law
event give the sharp entry scale at any deterministic selector chosen before
the eventual cutoff.
-/

namespace RBM.SingletonLocalLaw

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable def selectorQ (d : Dims) (E : ℝ) (s u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (band d).ell N (u N) / (band d).ell N (s N) * ((band d).scale E N (u N))⁻¹

noncomputable def selectorPsi (d : Dims) (E : ℝ) (s u : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (selectorQ d E s u N + (d.W N : ℝ)⁻¹)

theorem selectorQ_nonneg (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    0 ≤ selectorQ d E s u N := by
  have hu0 : 0 ≤ u N := (hs0 N).trans (hu N).1
  have hu1 : u N < 1 := (hu N).2.trans_lt (ht1 N)
  have hr : 1 ≤ (band d).ell N (u N) / (band d).ell N (s N) :=
    Step1.one_le_ell_div (B := band d) (hu N).1 hu1
  have hA : 0 < (band d).scale E N (u N) := (band d).scale_pos' hE N hu0 hu1
  exact mul_nonneg (zero_le_one.trans hr) (inv_nonneg.mpr hA.le)

theorem W_inv_le_selectorQ (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    (d.W N : ℝ)⁻¹ ≤ selectorQ d E s u N := by
  have hu0 : 0 ≤ u N := (hs0 N).trans (hu N).1
  have hu1 : u N < 1 := (hu N).2.trans_lt (ht1 N)
  have hbase := Step1.inv_W_le_inv_scale (B := band d) hE N hu0 hu1
  have hr : 1 ≤ (band d).ell N (u N) / (band d).ell N (s N) :=
    Step1.one_le_ell_div (B := band d) (hu N).1 hu1
  have hAi : 0 ≤ ((band d).scale E N (u N))⁻¹ :=
    inv_nonneg.mpr ((band d).scale_nonneg E N hu1.le)
  unfold selectorQ
  exact hbase.trans (by nlinarith [mul_le_mul_of_nonneg_right hr hAi])

theorem W_inv_sqrt_le_selectorPsi (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    Real.sqrt ((d.W N : ℝ)⁻¹) ≤ selectorPsi d E s u N := by
  unfold selectorPsi
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (selectorQ_nonneg d hE hs0 ht1 hu N))

theorem W_rpow_neg_half_le_selectorPsi (d : Dims) {E : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    (d.W N : ℝ) ^ (-(1 : ℝ) / 2) ≤ selectorPsi d E s u N := by
  have hW : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have heq : (d.W N : ℝ) ^ (-(1 : ℝ) / 2) =
      Real.sqrt ((d.W N : ℝ)⁻¹) := by
    calc
      (d.W N : ℝ) ^ (-(1 : ℝ) / 2) =
          (d.W N : ℝ) ^ (-((1 : ℝ) / 2)) := by congr 1; ring
      _ = ((d.W N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := Real.rpow_neg hW _
      _ = ((d.W N : ℝ)⁻¹) ^ ((1 : ℝ) / 2) :=
        (Real.inv_rpow hW _).symm
      _ = Real.sqrt ((d.W N : ℝ)⁻¹) := (Real.sqrt_eq_rpow _).symm
  rw [heq]
  exact W_inv_sqrt_le_selectorPsi d hE hs0 ht1 hu N

end
end RBM.SingletonLocalLaw

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514FDecayEvent
import RBM1D.Gauss.Lemma514QAssembly

/-!
# The projected drift envelope with its fast-decay event supplied

The event producer uses the same flow, window and decay parameters as the
projected-drift estimate.  The remaining stochastic inputs are displayed in
the theorem signature.
-/

namespace RBM.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The drift envelope of T290 with the `H.F` fast-decay input discharged by
T289.  The length-one loop and right-hand-side stochastic bounds remain
separate inputs. -/
theorem psiF_stochDom_etaT_inv_of_drift_inputs'' (X : Sample B)
    {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    (hxi1 : StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun _ _ _ => (1 : ℝ)))
    (hRhs : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => SumZeroDyn.xiRhs X E (n + 2) N u ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        psiF H N (p.1 : ℝ) p.2 ω)
      (fun N p _ => (etaT E (p.1 : ℝ))⁻¹) :=
  psiF_stochDom_etaT_inv_of_drift_inputs' H hE hs0 hst ht1 hc hFI hxi1 hRhs
    (highProb_Fpath_fastDecay X H hE hs0 hst ht1 hc hFI)

/-- The drift event remains inhabited on a genuinely forward window.  The
positive-length hypothesis is supplied by the p.24 grid's first cell. -/
theorem eventually_Fpath_fastDecay_forward_nonempty (X : Sample B)
    {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    (hforward : ∀ᶠ N : ℕ in Filter.atTop, s N < t N) :
    ∀ θ > (0 : ℝ), ∀ D > (0 : ℝ),
      ∀ᶠ N : ℕ in Filter.atTop, s N < t N ∧
        ({ω | ∀ u : TimeIcc s t N, ∀ q : LoopData (B.L N) (n + 2),
          FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) *
            (4 * (N : ℝ) ^ θ)) ((N : ℝ) ^ (-D))
            (H.F N (u : ℝ) (X.H N (u : ℝ) ω) q.1)} : Set Ω).Nonempty := by
  intro θ hθ D hD
  exact hforward.and (eventually_Fpath_fastDecay_nonempty X H hE hs0 hst ht1 hc hFI
    θ hθ D hD)

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSingletonLocalLaw
import RBM1D.Gauss.APrimeGeneralMovingControlExtension
import RBM1D.Gauss.APrimeGeneralMovingNormHolder
import RBM1D.Gauss.APrimeGeneralMovingNetNumerics

/-!
# T516: same-parameter deterministic time-net base

The accepted control, norm Holder, numerical, and literal norm-event fields
are assembled on one original moving-window parameter tuple.
-/

namespace RBM.APrimeGeneralMovingSameParameterNetBase

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow
noncomputable abbrev B : Band (Ω d) := band d

/-- All accepted deterministic time-net base fields on one moving window and
the single literal norm event `{omega | ||Xmat|| <= N}`. -/
structure NetBase (E c : ℝ) (s t : ℕ → ℝ) : Prop where
  qExt_pos : ∀ N u,
    0 < APrimeGeneralMovingControlExtension.qExt E s t N u
  qExt_eq_q : ∀ N u, u ∈ Icc (s N) (t N) →
    APrimeGeneralMovingControlExtension.qExt E s t N u =
      APrimeGeneralMovingControlExtension.q E s N u
  qExt_comparable : ∀ᶠ N : ℕ in atTop,
    ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      APrimeGeneralMovingControlExtension.qExt E s t N u ≤
          2 * APrimeGeneralMovingControlExtension.qExt E s t N v ∧
        APrimeGeneralMovingControlExtension.qExt E s t N v ≤
          2 * APrimeGeneralMovingControlExtension.qExt E s t N u
  xi_holder : ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ σ b,
          |APrimeGeneralMovingNormHolder.xi E N u σ b ω -
              APrimeGeneralMovingNormHolder.xi E N u' σ b ω| ≤
            (N : ℝ) ^ (6 : ℝ) * |u - u'| ^ ((1 : ℝ) / 2)
  numerics : APrimeGeneralMovingNetNumerics.NetNumerics s t
  good_measurable : ∀ N,
    MeasurableSet (APrimeGeneralMovingGoodMesh.good N)
  good_highProb : HighProb (P d) APrimeGeneralMovingGoodMesh.good
  good_nonempty : ∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty

/-- Every original admissible moving window supplies all base fields on the
same literal norm event. -/
theorem netBase {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) : NetBase E c s t :=
  { qExt_pos := APrimeGeneralMovingControlExtension.qExt_pos
      hE hs0 hst ht1
    qExt_eq_q := fun _ _ hu =>
      APrimeGeneralMovingControlExtension.qExt_eq_q hu
    qExt_comparable :=
      APrimeGeneralMovingControlExtension.eventually_qExt_short_time_comparable
        hE hs0 hst ht1 hc hreg
    xi_holder := APrimeGeneralMovingNormHolder.eventually_xi_holder
      hE hs0 hst ht1 hc hreg
    numerics := APrimeGeneralMovingNetNumerics.netNumerics hs0 hst ht1
    good_measurable := APrimeGeneralMovingGoodMesh.measurableSet_good
    good_highProb := APrimeGeneralMovingGoodMesh.highProb_good
    good_nonempty := APrimeGeneralMovingGoodMesh.good_nonempty }

/-- T495's one positive-length tuple carries `BoundsCore`, `Step1.Hyp`, and
all fields of `NetBase` simultaneously. -/
theorem positive_length_same_parameter_net_base_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧ NetBase 0 c s t := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hpos, _hll⟩ :=
    APrimeGeneralMovingSingletonLocalLaw.positive_length_same_parameter_witness
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hpos, netBase (by norm_num) hs0 hst ht1 hc hreg⟩

#print axioms netBase
#print axioms positive_length_same_parameter_net_base_witness

end
end RBM.APrimeGeneralMovingSameParameterNetBase

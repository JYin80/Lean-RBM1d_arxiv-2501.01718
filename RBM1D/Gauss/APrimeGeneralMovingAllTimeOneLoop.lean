/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSameParameterNetBase
import RBM1D.Gauss.APrimeGeneralMovingNetControl
import RBM1D.Gauss.APrimeGeneralMovingUnifDom

/-!
# T518: all-time centered one-loop domination on a moving window

The accepted same-parameter event, control, Holder, numerical, and
fixed-time-uniform fields are inserted into the public time-net theorem.
-/

namespace RBM.APrimeGeneralMovingAllTimeOneLoop

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow
noncomputable abbrev B : Band (Ω d) := band d

/-- The exact time-net consumer applied to the accepted base, control, and
fixed-time-uniform fields. -/
theorem centeredTrace_stochDom_timeIcc_of_fields {E c : ℝ}
    {s t : ℕ → ℝ}
    (hbase : APrimeGeneralMovingSameParameterNetBase.NetBase E c s t)
    (hcontrol : APrimeGeneralMovingNetControl.ControlFields E s t)
    (hfix : UnifDomIcc (P d) s t
      (fun N u (b : ZMod (d.L N)) ω =>
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
          E N u ω true b‖)
      (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
        2 * APrimeGeneralMovingControlExtension.qExt E s t N u)) :
    StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
          E N (p.1 : ℝ) ω true p.2‖)
      (fun N p _ω =>
        2 * APrimeGeneralMovingControlExtension.qExt E s t N (p.1 : ℝ)) := by
  let ξ : ∀ N, ℝ → ZMod (d.L N) → Ω d → ℝ := fun N u b ω =>
    APrimeGeneralMovingNormHolder.xi E N u true b ω
  let ζ : ∀ N, ℝ → ZMod (d.L N) → Ω d → ℝ := fun N u _b _ω =>
    2 * APrimeGeneralMovingControlExtension.qExt E s t N u
  have hfix' : UnifDomIcc (P d) s t ξ ζ := by
    simpa only [ξ, ζ, APrimeGeneralMovingNormHolder.xi] using hfix
  have hζ0 : ∀ N u b ω, 0 ≤ ζ N u b ω := by
    intro N u b ω
    simpa only [ζ, APrimeGeneralMovingNetControl.control] using
      hcontrol.nonneg N u b ω
  have hHol : ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          ∀ v ∈ Icc (s N) (t N),
            |ξ N u b ω - ξ N v b ω| ≤
              (N : ℝ) ^ (6 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
    filter_upwards [hbase.xi_holder] with N hN
    intro ω hω b u hu v hv
    exact hN ω hω u hu v hv true b
  have hlow : ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          (N : ℝ) ^ (-1 : ℝ) ≤ ζ N u b ω := by
    filter_upwards [hcontrol.lower] with N hN
    intro ω _hω b u hu
    simpa only [ζ, APrimeGeneralMovingNetControl.control] using hN ω b u hu
  have hslow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          ∀ v ∈ Icc (s N) (t N),
            |u - v| ≤ APrimeGeneralMovingNetNumerics.meshSpacing N →
              ζ N v b ω ≤ (N : ℝ) ^ ε * ζ N u b ω := by
    intro ε hε
    filter_upwards [hcontrol.slow ε hε] with N hN
    intro ω _hω b u hu v hv hdist
    simpa only [ζ, APrimeGeneralMovingNetControl.control] using
      hN ω b u hu v hv (by
        simpa only [APrimeGeneralMovingNetNumerics.meshSpacing] using hdist)
  have hall := Gauss.stochDom_timeIcc_of_unifDom
    (P := P d) (Cv := (1 : ℝ)) (T := (1 : ℝ))
    (K := (6 : ℝ)) (B := (1 : ℝ)) (γ := (1 : ℝ) / 2)
    (ξ := ξ) (ζ := ζ)
    (δ := APrimeGeneralMovingNetNumerics.meshSpacing)
    hbase.numerics.hcard hbase.numerics.hst hbase.numerics.hT
    hbase.numerics.hlen hbase.numerics.hK hbase.numerics.hB
    hbase.numerics.hγ hζ0 hbase.numerics.hδ
    hbase.good_highProb hHol hlow hslow hfix'
  simpa only [ξ, ζ, APrimeGeneralMovingNormHolder.xi] using hall

/-- The actual Gaussian model supplies every field of the all-time theorem
from the original moving-window inputs. -/
theorem centeredTrace_stochDom_timeIcc {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
          E N (p.1 : ℝ) ω true p.2‖)
      (fun N p _ω =>
        2 * APrimeGeneralMovingControlExtension.qExt E s t N (p.1 : ℝ)) := by
  have hbase := APrimeGeneralMovingSameParameterNetBase.netBase
    hE hs0 hst ht1 hc hreg
  have hcontrol := APrimeGeneralMovingNetControl.controlFields
    hE hs0 hst ht1 hc hreg
  have hfix := APrimeGeneralMovingUnifDom.centeredTrace_unifDomIcc
    hE hs0 hst ht1 hc hreg hB hStep
  exact centeredTrace_stochDom_timeIcc_of_fields hbase hcontrol hfix

/-- T516's single positive-length tuple satisfies the actual all-time
centered one-loop conclusion together with its current-window inputs. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
        (fun N p ω =>
          ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
            0 N (p.1 : ℝ) ω true p.2‖)
        (fun N p _ω =>
          2 * APrimeGeneralMovingControlExtension.qExt
            0 s t N (p.1 : ℝ)) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hpos, hbase⟩ :=
    APrimeGeneralMovingSameParameterNetBase.positive_length_same_parameter_net_base_witness
  have hcontrol := APrimeGeneralMovingNetControl.controlFields
    (E := 0) (s := s) (t := t) (by norm_num) hs0 hst ht1 hc hreg
  have hfix := APrimeGeneralMovingUnifDom.centeredTrace_unifDomIcc
    (E := 0) (s := s) (t := t) (by norm_num) hs0 hst ht1 hc hreg hB hStep
  have hall := centeredTrace_stochDom_timeIcc_of_fields hbase hcontrol hfix
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hpos, hall⟩

#print axioms centeredTrace_stochDom_timeIcc_of_fields
#print axioms centeredTrace_stochDom_timeIcc
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingAllTimeOneLoop

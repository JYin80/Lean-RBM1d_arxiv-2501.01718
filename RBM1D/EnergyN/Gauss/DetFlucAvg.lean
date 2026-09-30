/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.MinorDiffCond
import RBM1D.Flow.Thm221Bare
import RBM1D.Flow.EnergyUniform
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.CutoffBounds
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Flow.Eq548Producer
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.Eq45Small
import RBM1D.EnergyN.Gauss.Eq45Small
import RBM1D.EnergyN.Gauss.GoodSetFlow

/-!
# The fixed-time fluctuation-average statement at an `N`-dependent energy

The predicate `RBM.Gauss.fixedTimeFAStatementN` and the moment bound
`RBM.Gauss.fixedMoment_gain_of_goodSetFlowN`, at an `N`-dependent energy `E : ℕ → ℝ`. No
energy-dependent constant is fixed here: the two `E`-uses inside the proof,
`RBM.Gauss.flucGainUpTo'_goodSetFlow` and `RBM.Gauss.condCost_condEps`
(`Gauss/MinorDiffCond.lean`), take `{N : ℕ}`/`{v : ℝ}` explicitly and are applied after `N` is
bound by `filter_upwards ... with N ... v hv`, i.e. they are energy-free deterministic facts used
at `E N`. The remaining input is `hsmall_of_highProbN` (`RBM1D/EnergyN/Gauss/Eq45Small.lean`).
-/

namespace RBM.Gauss

open Filter MeasureTheory Finset

/-- **The fixed-time fluctuation-average statement**: for `0 < a`, `0 ≤ K`, `|E N| < 2`,
`u N ∈ [0, 1)`, `N^{-K} ≤ η_u` and `W^{-1/2} ≤ Ψ ≤ N^{-a}` eventually, the uniform local law at `u`
gives fluctuation averages at most `Ψ²`, for the rows of `S` and for the blocks. No
energy-dependent constant is fixed here. -/
def fixedTimeFAStatementN (d : Dims) (E : ℕ → ℝ) (u Ψ : ℕ → ℝ) (a K : ℝ) : Prop :=
  0 < a → 0 ≤ K → (∀ N, |E N| < 2) →
  (∀ N, 0 ≤ u N ∧ u N < 1) →
  (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N)) →
  (∀ᶠ N : ℕ in atTop,
    ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N ∧
      Ψ N ≤ (N : ℝ) ^ (-a)) →
  LocalLawUnifIccN d E u u Ψ →
  (UnifDomIcc (P d) u u
    (fun N v (i : d.Idx N) ω =>
      ‖flucAvg d N v (zt (E N) v) (mE (E N))
        (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
    (fun N _ _ _ => Ψ N ^ 2) ∧
  UnifDomIcc (P d) u u
    (fun N v (b : ZMod (d.L N)) ω =>
      ‖flucAvg d N v (zt (E N) v) (mE (E N)) (blkCoef (d.L N) (d.W N) b) ω‖)
    (fun N _ _ _ => Ψ N ^ 2))

/-- **The moment gain `FlucGainUpTo'` at every `v ∈ [s, t]`**, eventually, from the good set `hΩ`,
with `δ` polynomially small and `η_t⁻¹` polynomially bounded. -/
theorem fixedMoment_gain_of_goodSetFlowN (d : Dims) {E : ℕ → ℝ} {s t δ : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hδpos : ∀ N, 0 < δ N) (hδ4 : ∀ N, δ N ≤ 1 / 4)
    (hδlo : PolyLo δ)
    (hηhi : PolyHi fun N => (etaT (E N) (t N))⁻¹ + 1)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (p : ℕ)
    (hMδ : ∀ᶠ N : ℕ in atTop, 8 * (2 * p : ℝ) * δ N ≤ 1)
    (hδC : ∀ᶠ N : ℕ in atTop,
      2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N v (zt (E N) v) (mE (E N))
        (2 * (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N))
        (4 * δ N) (2 * p) (2 * p) := by
  have hsmall := hsmall_of_highProbN d hE ht1 hδpos hδlo hηhi hΩ p
  filter_upwards [hMδ, hδC, hsmall] with N hMδN hδCN hsmallN v hv
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
  have hΨ : (0 : ℝ) < 2 * δ N := by linarith [hδpos N]
  have hcc : condCost (E N) v (2 * p) (2 * δ N)
      (condEps (E N) v (2 * p) (2 * δ N)) = 2 * δ N :=
    condCost_condEps (hE N) hv1 (2 * p) hΨ
  have h := flucGainUpTo'_goodSetFlow (E := E N) (s := s) (t := t) (δ := δ)
    (M := 2 * p) (n := 2 * p) (hE N) hv1 hv
    (condEps_nonneg (hE N) hv1 (2 * p) hΨ.le)
    (hδpos N) (hδ4 N) (by push_cast; linarith [hMδN])
    (by rw [hcc]; exact hδCN) (by rw [hcc]; exact hsmallN v hv)
  convert h using 1 <;> norm_num [hcc] <;> ring

end RBM.Gauss

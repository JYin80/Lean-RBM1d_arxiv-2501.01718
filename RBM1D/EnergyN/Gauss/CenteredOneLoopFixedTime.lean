/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.SingletonLocalLaw
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.EnergyN.Gauss.SingletonLocalLaw
import RBM1D.EnergyN.Gauss.DetAvgIBPFlow

/-!
# The centered one-loop trace at a fixed time, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`:
`RBM.CenteredOneLoopFixedTime.localLawUnifIcc_of_selector_llErrN` and
`RBM.CenteredOneLoopFixedTime.centered_block_trace_stochDomN`.

## The external `κ`

`centered_block_trace_stochDomN` takes an external `κ` (`hE : ∀ N, |E N| ≤ 2 - κ` and
`hκ1 : κ ≤ 1`, which its consumer needs) and passes it directly into
`detAvgIBP_stochDom_of_localLaw_completeN` (`RBM1D/EnergyN/Gauss/DetAvgIBPFlow.lean`), so no
`κ` is derived from `2 - |E N|`. `localLawUnifIcc_of_selector_llErrN` needs no `κ`: it uses only
the generic (`E`-free) `Gauss.unifDomIcc_of_stochDom_timeIcc`.
-/

namespace RBM.CenteredOneLoopFixedTime

open Filter MeasureTheory Set Gauss

noncomputable section

/-- **The uniform local law `LocalLawUnifIccN` on `[u, u]`** from the entrywise bound
`llErr ≺ selectorPsi` at the single time `u`. No energy-dependent constant is fixed here: it uses
only the generic (`E`-free) `Gauss.unifDomIcc_of_stochDom_timeIcc`. -/
theorem localLawUnifIcc_of_selector_llErrN (d : Dims) {E : ℕ → ℝ}
    {s u : ℕ → ℝ}
    (hll : StochDom (P d)
      (fun N (ij : d.Idx N × d.Idx N) ω =>
        (sample d).llErr (E N) N (u N) ω ij)
      (fun N _ _ => SingletonLocalLaw.selectorPsi d (E N) s u N)) :
    LocalLawUnifIccN d E u u
      (fun N => SingletonLocalLaw.selectorPsi d (E N) s u N) := by
  have hidx := hll.precomp_param
    (fun N (p : TimeIcc u u N × (d.Idx N × d.Idx N)) => p.2)
  have hgreen : StochDom (P d)
      (fun N (p : TimeIcc u u N × (d.Idx N × d.Idx N)) ω =>
        ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1 p.2.2 -
          (if p.2.1 = p.2.2 then mE (E N) else 0)‖)
      (fun N _ _ => SingletonLocalLaw.selectorPsi d (E N) s u N) := by
    refine StochDom.of_le_left (fun N p ω => le_of_eq ?_) hidx
    have hp : (p.1 : ℝ) = u N := le_antisymm p.1.2.2 p.1.2.1
    rw [hp, (sample d).llErr_eq N (u N) ω p.2]
    simp only [Sample.G, sample_H]
    congr 2
  exact Gauss.unifDomIcc_of_stochDom_timeIcc hgreen

set_option maxHeartbeats 1000000 in
-- The dimension-generic producer/IBP composition exceeds the default budget.
/-- **`|tr((G_u - m) E_b)| ≺ 2 selectorQ`** at a time `u ∈ [s, t]`, from (2.68)–(2.70) at `s`
and the hypotheses of Step 1. The margin is the external `κ` of `hE`/`hκ1`, passed directly into
`detAvgIBP_stochDom_of_localLaw_completeN`. -/
theorem centered_block_trace_stochDomN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t u : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt (E N) (u N))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ =>
        2 * SingletonLocalLaw.selectorQ d (E N) s u N) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  let a : ℝ := 59 * c / 240
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha : a < 59 * c / 120 := by dsimp [a]; linarith
  have hu0 : ∀ N, 0 ≤ u N := fun N => (hs0 N).trans (hu N).1
  have hu1 : ∀ N, u N < 1 := fun N => (hu N).2.trans_lt (ht1 N)
  have hpack :=
    SingletonLocalLaw.general_moving_singleton_localLawN
      d hκ0 hE hs0 hst ht1 hu hc hreg hB hStep ha0 ha
  have hlocal : LocalLawUnifIccN d E u u
      (fun N => SingletonLocalLaw.selectorPsi d (E N) s u N) :=
    localLawUnifIcc_of_selector_llErrN d hpack.1
  have hone := Gauss.detAvgIBP_stochDom_of_localLaw_completeN d
    hκ0 hκ1 hE hu0 hu1 ha0 (show (0 : ℝ) ≤ 2 by norm_num)
    hpack.2.2.2 (Eventually.of_forall hpack.2.1) hpack.2.2.1 hlocal
  refine StochDom.control_mono hone ?_
  intro N b ω
  have hq0 := SingletonLocalLaw.selectorQ_nonneg
    d (hE2 N) hs0 ht1 hu N
  have hwq := SingletonLocalLaw.W_inv_le_selectorQ
    d (hE2 N) hs0 ht1 hu N
  have hsqrt :
      SingletonLocalLaw.selectorPsi d (E N) s u N ^ 2 =
        SingletonLocalLaw.selectorQ d (E N) s u N +
          (d.W N : ℝ)⁻¹ := by
    unfold SingletonLocalLaw.selectorPsi
    rw [Real.sq_sqrt]
    exact add_nonneg hq0 (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [← pow_two, hsqrt]
  linarith

section Compat

end Compat

end
end RBM.CenteredOneLoopFixedTime

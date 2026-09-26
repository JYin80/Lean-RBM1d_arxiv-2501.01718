/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.Gauss.Eq45Flow
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.Step2Close

/-!
# The sharp one-loop bound `Ξ₁ ≺ 1` at a grid point (T1527)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.5) composed with (2.76): the `Ξ₁` input of `goodSet514` (supervisor
`2026-09-26-1120.md` §1a(i), condition 2; `docs/reports/T1525-prove.md` (I2)).

`RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete` (`DetAvgIBPFlow.lean:274`) already proves,
for a **general** `Dims`, the sharp block-average bound `‖trace((G_u - m) E_a)‖ ≺ Ψ_N · Ψ_N` at
one deterministic grid time `u_N`, both charges (the conclusion does not distinguish `σ`, since
`RBM.Gauss.lkErr_one_eq_norm_trace` shows the `1`-loop `L - K` **is** this block average for
either charge — `σ = -` differs only by a complex conjugation that the norm does not see).
Choosing the control `Ψ_N` to be the **tight** per-point local-law scale `(scale_{u_N})⁻¹^{1/2}`
(not an interval-uniform majorant) gives `scale_{u_N} · Ψ_N · Ψ_N = 1` exactly, i.e. the sharp
bound `Ξ^{(L-K)}_{u_N,1} ≺ 1` at that grid point, for general `Dims`. No `MomentDuhamel.Hyp`,
`Step2.Hyp`, `EarlyQVRateEv.jStar`, `gmOfJS`-`h560` or `exampleGrow` constant occurs in the
dependency closure; the A'-era declarations that do occur (through the fixed-time good event
`goodSetFlow` and through the merged `steps12_gauss`) are listed in `docs/reports/T1527-prove.md`
(DECISIONS §10b).

## Main results

* `RBM.Gauss.stochDom_lkMax_one_of_localLaw` (T1) — the composition, general `Dims`, from
  `RBM.Gauss.detAvgIBP_stochDom_of_localLaw_complete`'s own hypothesis list.
* `RBM.Gauss.stochDom_lkMax_one_of_steps12` (T2) — the same conclusion at any grid point
  `u_N ∈ [s_N, t_N]`, from exactly `RBM.Gauss.steps12_gauss`'s hypothesis list (T1524, no `Hy`),
  with `hll` produced from `Steps12.localLaw` restricted to the singleton window `{u_N}` via
  `RBM.Gauss.localLawUnifIcc_of_localLawFlow`, and the regime at `u_N` derived from (2.72).

Route: `detAvgIBP_stochDom_of_localLaw_complete`, then `lkErr_one_eq_norm_trace` (the
block-average / `1`-loop identity, both charges automatically), then the sup-absorption step
`exists_lt_of_lt_ciSup` (a genuine per-`N` supremum over the finitely many `LoopData (d.L N) 1`),
finishing with the arithmetic identity `scale · Ψ · Ψ = 1`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

section OneLoopSharpGrid

variable (d : Dims)

/-- **The arithmetic identity `scale_u · Ψ_u · Ψ_u = 1`** for the tight pointwise scale
`Ψ_u := (scale_u)⁻¹^{1/2}`. -/
theorem scale_mul_inv_rpow_half_sq {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (band d).scale E N u *
      (((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) * ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2))
      = 1 := by
  have hx : 0 < (band d).scale E N u := (band d).scale_pos' hE N hu0 hu1
  have hxi : 0 < ((band d).scale E N u)⁻¹ := inv_pos.mpr hx
  rw [← Real.rpow_add hxi, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one,
    mul_inv_cancel₀ hx.ne']

/-- **The bandwidth floor of the tight scale is automatic**: `W^{-1/2} ≤ (scale_u)⁻¹^{1/2}`, from
`scale_u = W ℓ_u η_u ≤ W` (`RBM.Gauss.Grid.DriftPt.scale_le_W`). -/
theorem W_rpow_neg_half_le_scale_inv_rpow_half {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) := by
  have hx : 0 < (band d).scale E N u := (band d).scale_pos' hE N hu0 hu1
  have hW : (band d).scale E N u ≤ (d.W N : ℝ) := Grid.DriftPt.scale_le_W (band d) hE N hu0 hu1
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  rw [neg_div, Real.rpow_neg hw.le, ← Real.inv_rpow hw.le]
  exact Real.rpow_le_rpow (inv_nonneg.mpr hw.le) (inv_anti₀ hx hW) (by norm_num)

/-- `u ↦ W ℓ_u η_u` is antitone on `(-∞, 1]` (p. 24, `RBM.flowScale_antitoneOn`). -/
theorem band_scale_antitone {E : ℝ} {N : ℕ} {u v : ℝ} (huv : u ≤ v) (hv1 : v ≤ 1) :
    (band d).scale E N v ≤ (band d).scale E N u := by
  change flowScale ((band d).W N : ℝ) ((band d).L N) E v ≤
    flowScale ((band d).W N : ℝ) ((band d).L N) E u
  exact flowScale_antitoneOn (Nat.cast_nonneg _) _ _
    (Set.mem_Iic.mpr (le_trans huv hv1)) (Set.mem_Iic.mpr hv1) huv

/-- **The regime at an interior grid point, from (2.72).** Under `steps12_gauss`'s regularity
hypothesis `hreg`, at every `u_N ∈ [s_N, t_N]`, eventually `N^c ≤ W ℓ_{u_N} η_{u_N}` and
`N^{-1} ≤ η_{u_N}`. -/
theorem eventually_regime_of_hreg {E c : ℝ} {s t u : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ c ≤ (band d).scale E N (u N) ∧ (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (u N) := by
  filter_upwards [hreg, (band d).dim, eventually_ge_atTop 1] with N hN hdim hN1
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hηst : etaT E (t N) ≤ etaT E (s N) := by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [hst N]) hm.le
  have hr : 1 ≤ (etaT E (s N) / etaT E (t N)) ^ 30 := one_le_pow₀ ((one_le_div hηt).2 hηst)
  have hNc0 : 0 ≤ (N : ℝ) ^ c := Real.rpow_nonneg hn0.le _
  have hct : (N : ℝ) ^ c ≤ (band d).scale E N (t N) :=
    le_trans (le_mul_of_one_le_right hNc0 hr) hN
  have hut : (band d).scale E N (t N) ≤ (band d).scale E N (u N) :=
    band_scale_antitone d (hu N).2 (ht1 N).le
  refine ⟨hct.trans hut, ?_⟩
  have hNc1 : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hn1 hc0.le
  have hℓ : (band d).ell N (t N) ≤ (band d).L N := by
    rw [Band.ell, ellHat_ofReal _ (ht1 N)]
    exact min_le_right _ _
  have hWL : ((band d).W N : ℝ) * (band d).L N ≤ (N : ℝ) := by exact_mod_cast hdim.1
  have hsc : (band d).scale E N (t N) ≤ (N : ℝ) * etaT E (t N) := by
    calc
      (band d).scale E N (t N) =
          ((band d).W N : ℝ) * (band d).ell N (t N) * etaT E (t N) := rfl
      _ ≤ ((band d).W N : ℝ) * (band d).L N * etaT E (t N) := by gcongr
      _ ≤ (N : ℝ) * etaT E (t N) := by gcongr
  have h1 : 1 ≤ (N : ℝ) * etaT E (t N) := hNc1.trans (hct.trans hsc)
  have hηu : etaT E (t N) ≤ etaT E (u N) := by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [(hu N).2]) hm.le
  rw [Real.rpow_neg_one]
  refine le_trans ?_ hηu
  rw [inv_eq_one_div, div_le_iff₀ hn0]
  linarith

/-- The polynomial lower bound `N^c ≤ scale_u` gives `(scale_u)⁻¹^{1/2} ≤ N^{-c/2}`. -/
theorem scale_inv_rpow_half_le_of_rpow_le {E c : ℝ} {N : ℕ} {u : ℝ} (hN1 : 1 ≤ N)
    (h : (N : ℝ) ^ c ≤ (band d).scale E N u) :
    ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(c / 2)) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNc : 0 < (N : ℝ) ^ c := Real.rpow_pos_of_pos hn0 _
  have hx : 0 < (band d).scale E N u := hNc.trans_le h
  have h1 : ((band d).scale E N u)⁻¹ ≤ (N : ℝ) ^ (-c) := by
    rw [Real.rpow_neg hn0.le]
    exact inv_anti₀ hNc h
  calc
    ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) ^ (-c)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hx.le) h1 (by norm_num)
    _ = (N : ℝ) ^ (-(c / 2)) := by
      rw [← Real.rpow_mul hn0.le]
      ring_nf

/-- **(T1)** The sharp one-loop bound `Ξ^{(L-K)}_{u_N,1} ≺ 1` at a deterministic grid time `u_N`,
both charges, general `Dims`, from Step 2's local law at that single time. Composes (4.5)
(`lkErr_one_eq_norm_trace`) with the sharp block-average bound
(`detAvgIBP_stochDom_of_localLaw_complete`), at the tight pointwise scale
`Ψ_N := (scale_{u_N})⁻¹^{1/2}`, so that `scale_{u_N} · Ψ_N · Ψ_N = 1` exactly. -/
theorem stochDom_lkMax_one_of_localLaw {E κ : ℝ} {u : ℕ → ℝ} {a K : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨhi : ∀ᶠ N : ℕ in atTop,
      ((band d).scale E N (u N))⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIcc d E u u (fun N => ((band d).scale E N (u N))⁻¹ ^ (1 / 2 : ℝ))) :
    StochDom (P d)
      (fun N (_ : Unit) ω => (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1)
      (fun _ _ _ => (1 : ℝ)) := by
  have hE' : |E| < 2 := by linarith
  have hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ ((band d).scale E N (u N))⁻¹ ^ ((1 : ℝ) / 2) :=
    Eventually.of_forall fun N => W_rpow_neg_half_le_scale_inv_rpow_half d hE' (hu0 N) (hu1 N)
  set Ψ : ℕ → ℝ := fun N => ((band d).scale E N (u N))⁻¹ ^ ((1 : ℝ) / 2) with hΨdef
  have hbase := detAvgIBP_stochDom_of_localLaw_complete d hκ0 hκ1 hE hu0 hu1 ha hK hη hΨlo hΨhi
    hll
  have heq : (fun N (v : LoopData (d.L N) 1) ω => (sample d).lkErr E N (u N) ω v.idx)
      = fun N (v : LoopData (d.L N) 1) ω =>
          ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt E (u N))
            - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) (v.2 0))‖ := by
    funext N v ω
    exact lkErr_one_eq_norm_trace (sample d) v
  have hloop : StochDom (P d)
      (fun N (v : LoopData (d.L N) 1) ω => (sample d).lkErr E N (u N) ω v.idx)
      (fun N (_ : LoopData (d.L N) 1) _ => Ψ N * Ψ N) := by
    rw [heq]
    exact hbase.precomp_param (fun N (v : LoopData (d.L N) 1) => v.2 0)
  have hΨΨ1 : ∀ N, (band d).scale E N (u N) * (Ψ N * Ψ N) = 1 := fun N =>
    scale_mul_inv_rpow_half_sq d hE' (hu0 N) (hu1 N)
  intro τ hτ D hD
  filter_upwards [hloop τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  rintro ω ⟨_, hω⟩
  rw [mul_one] at hω
  have hxpos : 0 < (band d).scale E N (u N) := (band d).scale_pos' hE' N (hu0 N) (hu1 N)
  have hΨpos : 0 < Ψ N := Real.rpow_pos_of_pos (inv_pos.mpr hxpos) _
  have hpos : 0 < Ψ N * Ψ N := mul_pos hΨpos hΨpos
  have hω2 : (N : ℝ) ^ τ * (Ψ N * Ψ N)
      < (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1 * (Ψ N * Ψ N) :=
    mul_lt_mul_of_pos_right hω hpos
  have heq2 : (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1 * (Ψ N * Ψ N)
      = Sample.lkMax (sample d) E N (u N) ω 1 := by
    have hcomm : (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1 * (Ψ N * Ψ N)
        = ((band d).scale E N (u N) * (Ψ N * Ψ N)) * Sample.lkMax (sample d) E N (u N) ω 1 := by
      ring
    rw [hcomm, hΨΨ1 N, one_mul]
  rw [heq2] at hω2
  have hω3 : (N : ℝ) ^ τ * (Ψ N * Ψ N)
      < ⨆ v : LoopData (d.L N) 1, (sample d).lkErr E N (u N) ω v.idx := hω2
  obtain ⟨v, hv⟩ := exists_lt_of_lt_ciSup hω3
  exact ⟨v, hv⟩

/-- **A `LocalLawFlow` restricted to a singleton grid point `u_N ∈ [s_N,t_N]`.** Reindexes along
the (defeq) inclusion `TimeIcc u u N ↪ TimeIcc s t N`. -/
theorem localLawFlow_singleton_of_localLawFlow {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    {X : Sample B} {E : ℝ} {s t u : ℕ → ℝ}
    (h : RBM.LocalLawFlow X E s t) (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    RBM.LocalLawFlow X E u u := by
  have hprc := h.precomp_param (fun N (q : TimeIcc u u N × (B.Idx N × B.Idx N)) =>
    ((⟨q.1.1, by
        have hv : (q.1 : ℝ) = u N := le_antisymm q.1.2.2 q.1.2.1
        rw [hv]; exact hu N⟩ : TimeIcc s t N), q.2))
  exact hprc

/-- **(T2)** The sharp one-loop bound `Ξ^{(L-K)}_{u_N,1} ≺ 1` at any grid point
`u_N ∈ [s_N, t_N]`, both charges, general `Dims`, from exactly `RBM.Gauss.steps12_gauss`'s
hypothesis list (T1524, no `Hy`). The regime data of (T1) at `u` is derived from (2.72)
(`hreg`) with `a := c/2`, `K := 1` (`eventually_regime_of_hreg`). -/
theorem stochDom_lkMax_one_of_steps12 {κ E c : ℝ} {s t u : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    StochDom (P d)
      (fun N (_ : Unit) ω => (band d).scale E N (u N) * Sample.lkMax (sample d) E N (u N) ω 1)
      (fun _ _ _ => (1 : ℝ)) := by
  have hE' : |E| < 2 := by linarith
  have hu0 : ∀ N, 0 ≤ u N := fun N => (hs0 N).trans (hu N).1
  have hu1 : ∀ N, u N < 1 := fun N => lt_of_le_of_lt (hu N).2 (ht1 N)
  have hrg := eventually_regime_of_hreg d hE' hst ht1 hc0 hreg hu
  have hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (u N) := hrg.mono fun _ h => h.2
  have hΨhi : ∀ᶠ N : ℕ in atTop,
      ((band d).scale E N (u N))⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(c / 2)) := by
    filter_upwards [hrg, eventually_ge_atTop 1] with N h hN1
    exact scale_inv_rpow_half_le_of_rpow_le d hN1 h.1
  have hS := steps12_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg
  have hLLu : RBM.LocalLawFlow (sample d) E u u :=
    localLawFlow_singleton_of_localLawFlow hS.localLaw hu
  have hll : LocalLawUnifIcc d E u u (fun N => ((band d).scale E N (u N))⁻¹ ^ (1 / 2 : ℝ)) :=
    localLawUnifIcc_of_localLawFlow hLLu
      (Eventually.of_forall fun N v hv => by
        rw [le_antisymm hv.2 hv.1])
  exact stochDom_lkMax_one_of_localLaw d hκ0 hκ1 hEκ hu0 hu1 (half_pos hc0) zero_le_one hη hΨhi
    hll

end OneLoopSharpGrid

end RBM.Gauss

#print axioms RBM.Gauss.stochDom_lkMax_one_of_localLaw
#print axioms RBM.Gauss.stochDom_lkMax_one_of_steps12

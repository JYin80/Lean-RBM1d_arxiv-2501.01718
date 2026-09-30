/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridGoodSet
import RBM1D.EnergyN.Gauss.Step2QVEvent
import RBM1D.EnergyN.Gauss.Step2JGle
import RBM1D.EnergyN.Gauss.CenteredOneLoopAllTime
import RBM1D.EnergyN.Gauss.EntryBoundTime
import RBM1D.EnergyN.Gauss.GridJStar

set_option maxHeartbeats 1000000

/-!
# The grid good set with high probability, at an `N`-dependent energy

At an `N`-dependent energy `E : ℕ → ℝ`: with high probability, for all `u ∈ [s, t]`, the flow
`Hflow u` lies in each of the sets `qvSet`, `jgSet`, `h554Set`, `honeSet`
(`RBM.Gauss.Grid.highProb_flow_qvSetN`, `RBM.Gauss.Grid.highProb_flow_jgSetN`,
`RBM.Gauss.Grid.highProb_flow_h554SetN`, `RBM.Gauss.Grid.highProb_flow_honeSetN`) and in their
intersection `goodSet` (`RBM.Gauss.Grid.highProb_flow_goodSetN`); and the grid process lies in
`goodSet` at all grid times (`RBM.Gauss.Grid.highProb_grid_goodSetN`). None of the six fixes a
constant itself; several take the external `κ` of their callees.

`highProb_flow_qvSetN` calls `Step2.highProb_quadVar_diagShape_of_jSN` (`Step2QVEvent.lean`),
taking the external `κ` through it. `highProb_flow_jgSetN` calls `Step2.highProb_jG_le_jSN`.
`highProb_flow_h554SetN` is fully deterministic (`HighProb.of_eventually_univ`, no probability
estimate, no `κ`); it uses the generic (`E`-free) `Gauss.eventually_le_W`, the energy-free
`mem_h554Set_of_isHermitian`/`RBM.one_le_ellHat_of_nonneg`, and `Hflow_isHermitian`.
`highProb_flow_honeSetN` calls `step1Hyp_gauss_of_scale''N` and `highProb_centeredEventN`
(`CenteredOneLoopAllTime.lean`), taking the external `κ` through them. `highProb_flow_goodSetN`
is the conjunction of the four above and `highProb_flow_eq273N`/`highProb_flow_eq557N`
(`GridJStar.lean`). `highProb_grid_goodSetN` is the grid transfer of `highProb_flow_goodSetN`
via the generic (`E`-free) `highProb_grid_of_flow`. `qvSet`, `qvVal`, `jgSet`, `h554Set`,
`honeSet`, `goodSet`, `jGMat`, `jSMat`, their `measurableSet_…` lemmas, `jS_eq_jSMat`,
`jG_eq_jGMat`, and `Hflow_isHermitian` are energy-free or generic, used at `E N`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped Matrix.Norms.L2Operator

/-- **With high probability `Hflow u ∈ qvSet` for all `u ∈ [s, t]`.** No energy-dependent constant
is fixed here: it takes the external `κ` through `Step2.highProb_quadVar_diagShape_of_jSN`. -/
theorem highProb_flow_qvSetN (d : Dims) {s t : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {D : ℝ} (hD : 60 ≤ D)
    {τ : ℝ} (hτ : 0 < τ) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈ qvSet d (E N) N (u : ℝ) ((band d).ell N (s N)) τ D}) := by
  have hHP := RBM.Gauss.Step2.highProb_quadVar_diagShape_of_jSN d hκ hE hB hs0 hst ht1 hcond hc0
    hreg hD τ hτ
  refine hHP.mono ?_
  filter_upwards [eventually_ge_atTop (0 : ℕ)] with N _ ω hω u
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hMH : (Hflow d N (u : ℝ) ω).IsHermitian := Hflow_isHermitian d N (u : ℝ) ω
  intro _
  rw [← jS_eq_jSMat]
  intro hjS a
  have hval := hω u hjS a
  show qvVal d (E N) N (u : ℝ) a (Hflow d N (u : ℝ) ω) ≤ _
  unfold qvVal
  rw [dif_pos hMH]
  exact hval

/-- **With high probability `Hflow u ∈ jgSet` for all `u ∈ [s, t]`.** No energy-dependent constant
is fixed here: it uses `Step2.highProb_jG_le_jSN`. -/
theorem highProb_flow_jgSetN (d : Dims) {s t : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {D : ℝ} (hD : 0 ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈ jgSet d (E N) N (u : ℝ) ε D}) := by
  have hHP := RBM.Gauss.Step2.highProb_jG_le_jSN d hκ hE hB hs0 hst ht1 hcond hc0 hreg D hD ε hε
  refine hHP.mono ?_
  filter_upwards with N ω hω u
  show jGMat d (E N) N (u : ℝ) _ _ D (Hflow d N (u : ℝ) ω) ≤ _
  rw [← jG_eq_jGMat, ← jS_eq_jSMat]
  exact hω u

/-- **With high probability `Hflow u ∈ h554Set` for all `u ∈ [s, t]`.** No energy-dependent
constant is fixed here: fully deterministic transfer, no probability estimate, no `κ`. -/
theorem highProb_flow_h554SetN (d : Dims) {s t : ℕ → ℝ} {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (D : ℝ) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈ h554Set d (E N) N (u : ℝ) D}) := by
  refine HighProb.of_eventually_univ ?_
  filter_upwards [eventually_le_W d 3] with N hW3 ω u
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hW1 : Real.exp 1 ≤ (d.W N : ℝ) := by
    have h1 : (3 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast hW3
    have h2 : Real.exp 1 ≤ (3 : ℝ) := by
      have := Real.exp_one_lt_d9
      nlinarith
    linarith
  have hlogW : 1 ≤ Real.log (d.W N : ℝ) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (d.W N : ℝ) :=
      Real.log_le_log (Real.exp_pos 1) hW1
    rwa [Real.log_exp] at h1
  have hℓu1 : (1 : ℝ) ≤ (band d).ell N (u : ℝ) := by
    have h1 := RBM.one_le_ellHat_of_nonneg ((band d).one_le_L N) ((hs0 N).trans u.2.1) hu1
    show (1 : ℝ) ≤ RBM.ellHat ((band d).L N) ((u : ℝ) : ℂ); exact h1
  exact mem_h554Set_of_isHermitian d (hE N) N hu1 (by linarith) hlogW
    (Hflow_isHermitian d N (u : ℝ) ω)

/-- **With high probability `Hflow u ∈ honeSet` for all `u ∈ [s, t]`.** No energy-dependent
constant is fixed here: it takes the external `κ` (and `κ ≤ 1`) through
`highProb_centeredEventN`. -/
theorem highProb_flow_honeSetN (d : Dims) {s t : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {ζCtr : ℝ}
    (hζ : 0 < ζCtr) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈ honeSet d (E N) N (u : ℝ) ((band d).ell N (s N)) ζCtr}) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hStep : Step1.HypN (sample d) E s t :=
    step1Hyp_gauss_of_scale''N d hκ hE hB hs0 hst ht1 hcond hc0 hreg
  have hHP := RBM.CenteredOneLoopAllTime.highProb_centeredEventN d hκ hκ1 hE hs0 hst ht1
    hc0 hζ ⟨hcond, hreg⟩ hB hStep
  refine hHP.mono ?_
  filter_upwards with N ω hω u σ b
  have hmem : (u : ℝ) ∈ Set.Icc (s N) (t N) := u.2
  have hqExt := RBM.CenteredOneLoopAllTime.qExt_eq_q (d := d) (E := E N) (s := s)
    (t := t) (N := N) (u := (u : ℝ)) hmem
  have hb := hω (u, b) σ
  rw [hqExt] at hb
  have heq : (2 : ℝ) * RBM.CenteredOneLoopAllTime.q d (E N) s N (u : ℝ) =
      2 * ((band d).ell N (u : ℝ) / (band d).ell N (s N)) * ((band d).scale (E N) N (u : ℝ))⁻¹ := by
    unfold RBM.CenteredOneLoopAllTime.q; ring
  rw [heq] at hb
  exact hb

/-- **With high probability `Hflow u ∈ goodSet` for all `u ∈ [s, t]`**: the intersection of all six
pieces. -/
theorem highProb_flow_goodSetN (d : Dims) {s t : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {D : ℝ} (hD : 60 ≤ D)
    {τ ε ζCtr τ3 τ57 : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hζ : 0 < ζCtr) (hτ3 : 0 < τ3)
    (hτ57 : 0 < τ57) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      Hflow d N (u : ℝ) ω ∈
        goodSet d (E N) N (u : ℝ) ((band d).ell N (s N)) τ ε ζCtr τ3 τ57 D}) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have h1 := highProb_flow_qvSetN d hκ hE hB hs0 hst ht1 hcond hc0 hreg hD hτ
  have h2 := highProb_flow_jgSetN d hκ hE hB hs0 hst ht1 hcond hc0 hreg
    (by linarith : (0 : ℝ) ≤ D) hε
  have h3 := highProb_flow_h554SetN d hE2 hs0 ht1 D
  have h4 := highProb_flow_honeSetN d hκ hκ1 hE hB hs0 hst ht1 hcond hc0 hreg hζ
  have h5 := highProb_flow_eq273N d hκ hE hB hs0 hst ht1 hcond hc0 hreg 3 (by norm_num) τ3 hτ3
  have h6 := highProb_flow_eq557N d hκ hE hB hs0 hst ht1 hcond hc0 hreg τ57 hτ57
  have hcomb := ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6
  refine hcomb.mono ?_
  filter_upwards with N ω hω u
  obtain ⟨⟨⟨⟨⟨hω1, hω2⟩, hω3⟩, hω4⟩, hω5⟩, hω6⟩ := hω
  exact ⟨⟨⟨⟨⟨hω1 u, hω2 u⟩, hω3 u⟩, hω4 u⟩, hω5 u⟩, hω6 u⟩

/-- **`HighProb (Pg d) {∀ k, H_k ∈ goodSet(time k)}`**, for an arbitrary grid endpoint sequence
`u` with `s N ≤ u N ≤ t N` and polynomially many grid points. -/
theorem highProb_grid_goodSetN (d : Dims) {s t : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {D : ℝ} (hD : 60 ≤ D)
    {τ ε ζCtr τ3 τ57 : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hζ : 0 < ζCtr) (hτ3 : 0 < τ3)
    (hτ57 : 0 < τ57)
    {u : ℕ → ℝ} (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s u K N k ω ∈
        goodSet d (E N) N (time s u K N k) ((band d).ell N (s N)) τ ε ζCtr τ3 τ57 D}) := by
  have hFlowFull := highProb_flow_goodSetN d hκ hκ1 hE hB hs0 hst ht1 hcond hc0 hreg hD hτ hε hζ
    hτ3 hτ57
  have hFlow := highProb_flow_restrict d hut
    (fun N v => goodSet d (E N) N v ((band d).ell N (s N)) τ ε ζCtr τ3 τ57 D) hFlowFull
  exact highProb_grid_of_flow d s u K hs0 hsu hK0 hC0 hKcard
    (fun N v => goodSet d (E N) N v ((band d).ell N (s N)) τ ε ζCtr τ3 τ57 D)
    (fun N v => measurableSet_goodSet d (E N) N v ((band d).ell N (s N)) τ ε ζCtr τ3 τ57 D
      (by linarith [hE N]))
    hFlow

section Compat

end Compat

end RBM.Gauss.Grid

end

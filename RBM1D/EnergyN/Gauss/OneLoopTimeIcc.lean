/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.EnergyN.Gauss.OneLoopSharpGrid
import RBM1D.EnergyN.Gauss.Lemma514Holder

/-!
# The sharp one-loop bound on the time interval, at an `N`-dependent energy

`RBM.Gauss.flow_xiLK_one_le_plainN`: `Ξ^{(L-K)}_{u,1} ≺ 1` uniformly in `u ∈ [s, t]`, at an
`N`-dependent energy `E : ℕ → ℝ`. The two generic real-analysis facts of the file,
`RBM.Gauss.abs_ciSup_sub_ciSup_le` and `.mul_ciSup_pos`, are `E`-free.

## The external `κ`

No energy-dependent constant is fixed here: the proof uses
`stochDom_lkMax_one_of_steps12_plainN` (`EnergyN/Gauss/OneLoopSharpGrid.lean`),
`Grid.etaT_inv_le_of_plainN` (`EnergyN/Gauss/Step2Plain.lean`) and `hHol_flowN`/`hKb_flowN`
(`EnergyN/Gauss/Lemma514Holder.lean`; `hKb_flowN` takes its own `κ`).
`exists_highProb_normX`, `traceMomentBound_gauss`, `stochDom_timeIcc_of_unifDom_const` are
`E`-free generic helpers.

`Step3.flowXiLK` takes a fixed `E : ℝ`, so the conclusion is stated with its unfolded
definition `X.xiLK (E N) N u ω 1` (`X.xiLK E N u ω m := X.lkMax E N u ω m * B.scale E N u ^ m`,
`Hierarchy/Step3.lean`).
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter

variable (d : Dims)

/-- **`Ξ^{(L-K)}_{u,1} ≺ 1` uniformly in `u ∈ [s, t]`**, from (2.68)–(2.70) at `s` and the plain
pair. It uses `stochDom_lkMax_one_of_steps12_plainN`, `Grid.etaT_inv_le_of_plainN`, `hKb_flowN`
and `hHol_flowN`. -/
theorem flow_xiLK_one_le_plainN {κ c : ℝ} {E : ℕ → ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    StochDom (band d).P
      (fun N (u : TimeIcc s t N) ω => (sample d).xiLK (E N) N (u : ℝ) ω 1)
      (fun _ _ _ => 1) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  -- Steps 1–2: every terminal-time sequence, then the quantifier exchange.
  have h1 : UnifDomIcc (P d) s t
      (fun N (u : ℝ) (_ : Unit) ω =>
        (band d).scale (E N) N u * Sample.lkMax (sample d) (E N) N u ω 1)
      (fun N _ _ _ => (1 : ℝ)) :=
    unifDomIcc_of_forall_stochDom hst fun v hv =>
      stochDom_lkMax_one_of_steps12_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hv
  -- The regime at `t_N`, at exponent `1` (for `hKb_flowN`) and `2` (for `hHol_flowN`).
  have hη1 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [Grid.etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc] with N hN
    rwa [Real.rpow_one]
  have hη2 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [Grid.etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc, eventually_ge_atTop 1]
      with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    refine hN.trans ?_
    have h := Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.rpow_one] at h
  obtain ⟨Ξ, hΞ, hXΞ⟩ := exists_highProb_normX d (traceMomentBound_gauss d) (le_refl (2 : ℝ))
  have hKb0 := hKb_flowN (band d) hκ0 hκ1 hEκ ht1 (by norm_num : (0 : ℝ) ≤ 1) 1 hη1
  have hKb : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ 1 →
        ‖(band d).Kval (E N) N w J‖ ≤ (N : ℝ) ^ (2 : ℝ) := by
    have hexp : (1 : ℝ) * ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    filter_upwards [hKb0] with N hN w hw J hJ h2 hle
    rw [← hexp]
    exact hN w hw J hJ h2 hle
  have hHol0 := hHol_flowN d hE hs0 ht1 (c := 2) (by norm_num) (m := 1) (le_refl 1) hη2 hXΞ hKb
  -- Lift the per-loop modulus to the sup `Sample.lkMax`.
  have hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ _ : Unit, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ v ∈ Set.Icc (s N) (t N),
        |(band d).scale (E N) N u * Sample.lkMax (sample d) (E N) N u ω 1
            - (band d).scale (E N) N v * Sample.lkMax (sample d) (E N) N v ω 1|
          ≤ (N : ℝ) ^ (15 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
    filter_upwards [hHol0] with N hN ω hω _ u hu v hv
    have hu0 : 0 ≤ u := (hs0 N).trans hu.1
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hv0 : 0 ≤ v := (hs0 N).trans hv.1
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
    have hscu : 0 < (band d).scale (E N) N u := (band d).scale_pos' (hE N) N hu0 hu1
    have hscv : 0 < (band d).scale (E N) N v := (band d).scale_pos' (hE N) N hv0 hv1
    have hbddu : BddAbove (Set.range (fun q : LoopData ((band d).L N) 1 =>
        (sample d).lkErr (E N) N u ω q.idx)) := (Set.finite_range _).bddAbove
    have hbddv : BddAbove (Set.range (fun q : LoopData ((band d).L N) 1 =>
        (sample d).lkErr (E N) N v ω q.idx)) := (Set.finite_range _).bddAbove
    have hbddu' : BddAbove (Set.range (fun q : LoopData ((band d).L N) 1 =>
        (band d).scale (E N) N u * (sample d).lkErr (E N) N u ω q.idx)) :=
      (Set.finite_range _).bddAbove
    have hbddv' : BddAbove (Set.range (fun q : LoopData ((band d).L N) 1 =>
        (band d).scale (E N) N v * (sample d).lkErr (E N) N v ω q.idx)) :=
      (Set.finite_range _).bddAbove
    have hC : ∀ q : LoopData ((band d).L N) 1,
        |(band d).scale (E N) N u * (sample d).lkErr (E N) N u ω q.idx
          - (band d).scale (E N) N v * (sample d).lkErr (E N) N v ω q.idx|
        ≤ (N : ℝ) ^ (15 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
      intro q
      have h := hN ω hω q u hu v hv
      rw [SumZeroDyn.norm_lkT, SumZeroDyn.norm_lkT, pow_one, pow_one] at h
      have hexp : (2 : ℝ) * (3 * ((1 : ℕ) : ℝ) + 4) + 1 = 15 := by norm_num
      rwa [hexp] at h
    have hkey := abs_ciSup_sub_ciSup_le hbddu' hbddv' hC
    have hequ : (⨆ q : LoopData ((band d).L N) 1,
        (band d).scale (E N) N u * (sample d).lkErr (E N) N u ω q.idx)
        = (band d).scale (E N) N u * Sample.lkMax (sample d) (E N) N u ω 1 :=
      (mul_ciSup_pos hscu hbddu).symm
    have heqv : (⨆ q : LoopData ((band d).L N) 1,
        (band d).scale (E N) N v * (sample d).lkErr (E N) N v ω q.idx)
        = (band d).scale (E N) N v * Sample.lkMax (sample d) (E N) N v ω 1 :=
      (mul_ciSup_pos hscv hbddv).symm
    rwa [hequ, heqv] at hkey
  -- The index set `Unit` is trivially polynomial-size.
  have hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card Unit : ℝ) ≤ (N : ℝ) ^ (0 : ℝ) := by
    filter_upwards with N
    simp
  have hlen : ∀ N, t N - s N ≤ 1 := fun N => by
    have h1 := hs0 N; have h2 := ht1 N; linarith
  have h3 := stochDom_timeIcc_of_unifDom_const hcard hst hlen
    (by norm_num : (0 : ℝ) ≤ (15 : ℝ)) (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)
    (fun _ => zero_le_one) (Eventually.of_forall fun _ => le_refl (1 : ℝ)) hΞ hHol h1
  have h4 := h3.precomp_param (fun N (u : TimeIcc s t N) => (u, ()))
  have heq : (fun N (u : TimeIcc s t N) ω =>
      (band d).scale (E N) N (u : ℝ) * Sample.lkMax (sample d) (E N) N (u : ℝ) ω 1)
      = fun N (u : TimeIcc s t N) ω => (sample d).xiLK (E N) N (u : ℝ) ω 1 := by
    funext N u ω
    change (band d).scale (E N) N (u : ℝ) * Sample.lkMax (sample d) (E N) N (u : ℝ) ω 1
      = Sample.lkMax (sample d) (E N) N (u : ℝ) ω 1 * (band d).scale (E N) N (u : ℝ) ^ 1
    rw [pow_one, mul_comm]
  rw [heq] at h4
  exact h4

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OneLoopSharpGrid
import RBM1D.EnergyN.Gauss.OneLoopSharpGrid

/-!
# The sharp one-loop bound along the grid, at an `N`-dependent energy

`RBM.Gauss.highProb_grid_xiLK_one_plainN`: with high probability
`(W ℓ η) |L - K|_1 ≤ N^ε` at all grid times, at an `N`-dependent energy `E : ℕ → ℝ`.

## The external `κ`

No energy-dependent constant is fixed here: it uses `stochDom_lkMax_one_of_steps12_plainN`
(`EnergyN/Gauss/OneLoopSharpGrid.lean`) and the generic (`E`-free) helpers
`unifDomIcc_of_forall_stochDom`, `card_loopData_le`, `Grid.map_H_eq`, `Grid.mem_Icc_time`,
`measurable_lkErrMat`, `lkErr_eq_lkErrMat`, `Sample.lkErr_le_lkMax`, applied at `E N`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

variable (d : Dims)

/-- **With high probability `(W ℓ η) lkErrMat ≤ N^ε` for the loops of length 1 at all grid
times.** It uses `stochDom_lkMax_one_of_steps12_plainN`. -/
theorem highProb_grid_xiLK_one_plainN {κ : ℝ} {E : ℕ → ℝ} {c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    {ε : ℝ} (hε : 0 < ε) :
    HighProb (Grid.Pg d) (fun N => {ω | ∀ k : Fin (K N + 1), ∀ v : LoopData (d.L N) 1,
      (band d).scale (E N) N (Grid.time s t K N k)
        * lkErrMat d (E N) N (Grid.time s t K N k) (Grid.H d s t K N k ω) v.idx
      ≤ (N : ℝ) ^ ε}) := by
  have hE' : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  -- Step 1 + 2: the pointwise `StochDom` at every grid-valued sequence `v`, exchanged into a
  -- single threshold-uniform `UnifDomIcc` statement over `[s_N, t_N]`.
  have hunif : UnifDomIcc (P d) s t
      (fun N u (_ : Unit) ω => (band d).scale (E N) N u * Sample.lkMax (sample d) (E N) N u ω 1)
      (fun _ _ _ _ => (1 : ℝ)) :=
    unifDomIcc_of_forall_stochDom hst
      (fun v hv => stochDom_lkMax_one_of_steps12_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0
        hreg0 hAc hv)
  -- The combined index `(k, v)` is polynomially large.
  have hcardV := card_loopData_le (B := band d) 1
  have hcard2 : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (K N + 1) × LoopData (d.L N) 1) : ℝ) ≤ (N : ℝ) ^ (C + 2) := by
    filter_upwards [hKcard, hcardV, eventually_ge_atTop 1] with N h1 h2 hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hpow1 : (0 : ℝ) ≤ (N : ℝ) ^ C := Real.rpow_nonneg hN0.le _
    have hcardnn : (0 : ℝ) ≤ (Fintype.card (LoopData (d.L N) 1) : ℝ) := Nat.cast_nonneg _
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc ((K N + 1 : ℕ) : ℝ) * (Fintype.card (LoopData (d.L N) 1) : ℝ)
        ≤ (N : ℝ) ^ C * (N : ℝ) ^ (((1 : ℕ) : ℝ) + 1) := mul_le_mul h1 h2 hcardnn hpow1
      _ = (N : ℝ) ^ (C + 2) := by rw [← Real.rpow_add hN0]; norm_num
  -- Rewrite the goal event as an intersection over the combined index `(k, v)`.
  have hset : ∀ N, {ω : Grid.Ωg d | ∀ k : Fin (K N + 1), ∀ v : LoopData (d.L N) 1,
      (band d).scale (E N) N (Grid.time s t K N k)
        * lkErrMat d (E N) N (Grid.time s t K N k) (Grid.H d s t K N k ω) v.idx
      ≤ (N : ℝ) ^ ε}
    = ⋂ p : Fin (K N + 1) × LoopData (d.L N) 1,
        {ω | (band d).scale (E N) N (Grid.time s t K N p.1)
          * lkErrMat d (E N) N (Grid.time s t K N p.1) (Grid.H d s t K N p.1 ω) p.2.idx
          ≤ (N : ℝ) ^ ε} := by
    intro N
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Prod.forall]
  simp only [hset]
  refine HighProb.biInter (by linarith : (0 : ℝ) ≤ C + 2) hcard2 ?_
  intro D hD
  filter_upwards [hunif ε hε D hD] with N hN
  rintro ⟨k, v⟩
  dsimp only
  -- Step 3 + 4: transfer the fixed-grid-point bound from the flow measure to the grid measure.
  set uk : ℝ := Grid.time s t K N k with huk
  have hmemk : uk ∈ Set.Icc (s N) (t N) :=
    Grid.mem_Icc_time s t K N k (hs0 N) (hst N) (Nat.lt_succ_iff.mp k.isLt)
  have hu0k : 0 ≤ uk := (hs0 N).trans hmemk.1
  have hu1k : uk < 1 := lt_of_le_of_lt hmemk.2 (ht1 N)
  have hHmeas : Measurable (Grid.H d s t K N k) :=
    (Grid.H_measurable_filt d s t K N k).mono ((Grid.filt d).le k) le_rfl
  have hHflowmeas : Measurable (Hflow d N uk) := RBM.measurable_H (sample d) N uk
  set Sgood : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
    {M | (band d).scale (E N) N uk * lkErrMat d (E N) N uk M v.idx ≤ (N : ℝ) ^ ε} with hSgood
  have hSmeas : MeasurableSet Sgood :=
    measurableSet_le ((measurable_lkErrMat d (E N) N uk v.idx).const_mul _) measurable_const
  have hcompl_eq : (Grid.Pg d)
        {ω | (band d).scale (E N) N uk * lkErrMat d (E N) N uk (Grid.H d s t K N k ω) v.idx
          ≤ (N : ℝ) ^ ε}ᶜ
      = (P d)
        {ω' | (band d).scale (E N) N uk * lkErrMat d (E N) N uk (Hflow d N uk ω') v.idx
          ≤ (N : ℝ) ^ ε}ᶜ := by
    change (Grid.Pg d) ((Grid.H d s t K N k) ⁻¹' Sgood)ᶜ = (P d) ((Hflow d N uk) ⁻¹' Sgood)ᶜ
    rw [← Set.preimage_compl, ← Set.preimage_compl,
      ← Measure.map_apply hHmeas hSmeas.compl, ← Measure.map_apply hHflowmeas hSmeas.compl,
      Grid.map_H_eq s t K N k (hs0 N) (hst N) (hK0 N)]
  have hxpos : 0 < (band d).scale (E N) N uk := (band d).scale_pos' (hE' N) N hu0k hu1k
  have hsub : {ω' | (band d).scale (E N) N uk * lkErrMat d (E N) N uk (Hflow d N uk ω') v.idx
        ≤ (N : ℝ) ^ ε}ᶜ
      ⊆ {ω' | (N : ℝ) ^ ε * 1
          < (band d).scale (E N) N uk * Sample.lkMax (sample d) (E N) N uk ω' 1} := by
    intro ω' hω'
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω'
    have hlkeq : lkErrMat d (E N) N uk (Hflow d N uk ω') v.idx
        = (sample d).lkErr (E N) N uk ω' v.idx := (lkErr_eq_lkErrMat d (E N) N uk ω' v.idx).symm
    have hle : (band d).scale (E N) N uk * lkErrMat d (E N) N uk (Hflow d N uk ω') v.idx
        ≤ (band d).scale (E N) N uk * Sample.lkMax (sample d) (E N) N uk ω' 1 := by
      rw [hlkeq]
      exact mul_le_mul_of_nonneg_left (Sample.lkErr_le_lkMax (sample d) v) hxpos.le
    have hgt : (N : ℝ) ^ ε < (band d).scale (E N) N uk * Sample.lkMax (sample d) (E N) N uk ω' 1 :=
      lt_of_lt_of_le hω' hle
    simpa using hgt
  have hbound : (P d)
      {ω' | (band d).scale (E N) N uk * lkErrMat d (E N) N uk (Hflow d N uk ω') v.idx
        ≤ (N : ℝ) ^ ε}ᶜ
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
    le_trans (measure_mono hsub) (hN uk hmemk Unit.unit)
  rw [hcompl_eq]
  exact hbound

end RBM.Gauss

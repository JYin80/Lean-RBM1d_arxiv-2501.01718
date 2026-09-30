/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Gauss
import RBM1D.Gauss.GridStop

/-!
# The grid bootstrap: the stopping time does not fire, and `jSMat → lkErrMat`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3: the last step of Step 2 on the
discrete grid, assembling the discrete continuity argument with the deterministic
`jSMat → lkErrMat` conversion.

## Main results

* `firstHit_eq_of_below` — if the process stays below the threshold at every grid index up to
  `K`, the grid stopping time never fires: it equals `K`.
* `min_firstHit_eq_of_at` — the same at the random target `τ = min (firstHit …) (firstHit …)`:
  if the second process never reaches its level up to `K` and the first is below its threshold
  at `τ`, then `τ = K`.
* `lk_le_of_jS` — the deterministic, pointwise conversion of a `jSMat` bound into an
  `lkErrMat` bound with the decay profile, via `RBM.Step2.le_jStar_mul` (the tautological
  `f ≤ J* T`) and `RBM.Step2.tT_le_decayProf` (the `D`-shift).
* `pg_bad_eq_flow` — the per-`N` transfer of a bad-set probability from the grid, at the last
  grid step, to the flow.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### (T1): discrete continuity of the bootstrap step -/

/-- **(T1)** If `J` never reaches `θ` up to grid index `K`, the grid stopping time
`firstHit J θ K` never fires: it equals `K`. -/
theorem firstHit_eq_of_below {Ω' : Type*} (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {ω : Ω'}
    (h : ∀ j ≤ K, J j ω < θ) : firstHit J θ K ω = K := by
  by_contra hne
  have hlt : firstHit J θ K ω < K := lt_of_le_of_ne (firstHit_le J θ K ω) hne
  have hmem : θ ≤ J (firstHit J θ K ω) ω :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  exact absurd (h _ hlt.le) (not_lt.2 hmem)

/-! ### (T2): the deterministic pointwise bound from `jSMat` to `lkErrMat` -/

/-- **(T2)** Deterministic, pointwise: a bound `jSMat d E D' N u M ≤ Λ` at loss order
`D' ≥ D + 4`, together with the scale bracket `1 ≤ scale ≤ W²`, converts into the `lkErrMat`
bound with the decay profile at order `D`.  Route: `Step2.le_jStar_mul` (the tautological
`f ≤ J* T`, applied to `jSMat`'s own integrand), `Step2.tT_le_decayProf` (the `D`-shift), and
`Step2.idx_sigPM` (`σ = (+,-)`'s index is `pmLoop`) to identify the integrand with `lkErrMat`.
`M.IsHermitian` is carried for interface parity with `Grid.H` (T3's call site) but is not needed
by the proof: `jSMat`/`lkErrMat` are defined for a general matrix. -/
theorem lk_le_of_jS {E D D' Λ : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (hDD : D + 4 ≤ D')
    (hA1 : 1 ≤ (band d).scale E N u) (hAW : (band d).scale E N u ≤ ((band d).W N : ℝ) ^ 2)
    (hJ : jSMat d E D' N u M ≤ Λ) (a b : ZMod (d.L N)) :
    lkErrMat d E N u M (pmLoop a b)
      ≤ Λ * ((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b := by
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have h1 : (1 : ℝ) ≤ jSMat d E D' N u M :=
    RBM.Step2.one_le_jStar hW0 (fun c => norm_nonneg _)
  have hΛ0 : 0 ≤ Λ := le_trans (le_trans zero_le_one h1) hJ
  have hab0 : (![a, b] : LoopArg (d.L N) 2) 0 = a := by simp
  have hab1 : (![a, b] : LoopArg (d.L N) 2) 1 = b := by simp
  have h0 := RBM.Step2.le_jStar_mul
    (f := fun c => ‖gloop (d.L N) (d.W N) M (zt E u) (LoopData.idx (RBM.Step2.sigPM, c))
        - (band d).Kval E N u (LoopData.idx (RBM.Step2.sigPM, c))‖)
    (ℓu := (band d).ell N u) (ηu := etaT E u) (D := D') hW0 (![a, b] : LoopArg (d.L N) 2)
  simp only [RBM.Step2.idx_sigPM, hab0, hab1] at h0
  have hkey : lkErrMat d E N u M (pmLoop a b)
      ≤ jSMat d E D' N u M * RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) := h0
  have htT : RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b))
      ≤ ((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b :=
    RBM.Step2.tT_le_decayProf hDD hA1 hAW a b
  have htT0 : 0 ≤ RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) :=
    RBM.tailT_nonneg hW0.le _
  calc lkErrMat d E N u M (pmLoop a b)
      ≤ jSMat d E D' N u M * RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) := hkey
    _ ≤ Λ * RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) :=
        mul_le_mul_of_nonneg_right hJ htT0
    _ ≤ Λ * (((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b) :=
        mul_le_mul_of_nonneg_left htT hΛ0
    _ = Λ * ((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b := by ring

/-! ### (T4): the `HighProb` transfer of the bootstrap to the grid endpoint -/

/-- **The per-`N` transfer of a bad-set probability** from the grid (at the last grid step
`k = K N`) to the flow at `uR N`: both events are preimages of one measurable matrix set, and
`map_H_eq` at `k = K N` with `time_last` identifies the two image laws.  Only this single `N` is
involved, so `K` may depend on anything that does not depend on `ω`. -/
theorem pg_bad_eq_flow {E δ : ℝ} {s uR : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N)
    (hsu : s N ≤ uR N) (hK : K N ≠ 0) (ζ : ZMod (d.L N) × ZMod (d.L N) → ℝ) :
    Pg d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
        (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)}
      = RBM.Gauss.P d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
        (N : ℝ) ^ δ * ζ p < (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)} := by
  set S : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := {M | ∃ p : ZMod (d.L N) × ZMod (d.L N),
    (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} with hSdef
  have hS : MeasurableSet S := by
    have heq : S = ⋃ p : ZMod (d.L N) × ZMod (d.L N),
        {M | (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} := by
      ext M; simp [hSdef]
    rw [heq]
    exact MeasurableSet.iUnion fun p =>
      measurableSet_lt measurable_const (measurable_lkErrMat d E N (uR N) (pmLoop p.1 p.2))
  have hmap : (Pg d).map (H d s uR K N (K N)) = (RBM.Gauss.P d).map (Hflow d N (uR N)) := by
    have h := map_H_eq (d := d) s uR K N (K N) hs0 hsu hK
    rwa [time_last s uR K N hK] at h
  have hHm : Measurable (H d s uR K N (K N)) :=
    (H_measurable_filt d s uR K N (K N)).mono ((filt d).le (K N)) le_rfl
  have hFm : Measurable (Hflow d N (uR N)) := RBM.measurable_H (sample d) N (uR N)
  have e1 : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
      (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)}
      = H d s uR K N (K N) ⁻¹' S := rfl
  have e2 : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
      (N : ℝ) ^ δ * ζ p < (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)}
      = Hflow d N (uR N) ⁻¹' S := rfl
  rw [e1, e2, ← Measure.map_apply hHm hS, ← Measure.map_apply hFm hS, hmap]

/-! ### The bootstrap only at the random target `τ` -/

/-- **The bootstrap at the random target, deterministic core.** Let
`τ ω := min (firstHit (J − θ) 0 K ω) (firstHit J' θ' K ω)`.  If the second process never reaches its
level up to `K` and `J τ < θ τ` holds at the random target, then `τ ω = K`: otherwise the first
`firstHit` is `< K`, and the hitting property gives `J τ ≥ θ τ`. -/
theorem min_firstHit_eq_of_at {Ω' : Type*} (J J' : ℕ → Ω' → ℝ) (θ : ℕ → ℝ) (θ' : ℝ) (K : ℕ)
    {ω : Ω'} (hgood : ∀ j ≤ K, J' j ω < θ')
    (hat : J (min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω)) ω
      < θ (min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω))) :
    min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω) = K := by
  have hb : firstHit J' θ' K ω = K := firstHit_eq_of_below J' θ' K hgood
  have haK : firstHit (fun j ω => J j ω - θ j) 0 K ω ≤ K := firstHit_le _ _ _ _
  rw [hb, min_eq_left haK] at hat ⊢
  by_contra hne
  have hlt : firstHit (fun j ω => J j ω - θ j) 0 K ω < K := lt_of_le_of_ne haK hne
  have hmem : (0 : ℝ) ≤ J (firstHit (fun j ω => J j ω - θ j) 0 K ω) ω
      - θ (firstHit (fun j ω => J j ω - θ j) 0 K ω) :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  linarith

end RBM.Gauss.Grid

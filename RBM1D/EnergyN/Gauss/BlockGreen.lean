/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.BlockGreen
import RBM1D.EnergyN.Hierarchy.Step2
import RBM1D.EnergyN.Gauss.EntryBoundTime

/-!
# Block Green-function bounds of Step 2 at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`:
`RBM.BlockGreen.eventually_Lre_le_jS_mul_tailT_quarterN` and
`RBM.BlockGreen.highProb_jG_le_of_entryBoundFlowN`. Neither fixes an `E`-dependent constant
before `∀ᶠ N`; the only energy-dependent input is `Step2.eq530N`
(`RBM1D/EnergyN/Hierarchy/Step2.lean`).
-/

namespace RBM
namespace BlockGreen

open Finset Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Far from the diagonal, `Lre ≤ jS · tT`**: eventually, for `|x - y| ≥ ℓ*_u/4`, the entry
`Lre (G_u) x y` is at most `Step2.jS` times `Step2.tT` at `|x - y|`, uniformly in `u ∈ [s, t]`
and `ω`. No energy-dependent constant is fixed here (it uses `Step2.eq530N` only). -/
theorem eventually_Lre_le_jS_mul_tailT_quarterN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (X : Sample B) (hc : Cond272N B E s t) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : TimeIcc s t N) (ω : Ω)
      (x y : ZMod (B.L N)),
      ellStar (B.W N : ℝ) (B.ell N (u : ℝ)) / 4 ≤
          (zdist (B.L N) (x - y) : ℝ) →
      Lre (X.H N (u : ℝ) ω) (zt (E N) (u : ℝ)) x y ≤
        Step2.jS X (E N) D N (u : ℝ) ω *
          Step2.tT B (E N) N D (u : ℝ) (zdist (B.L N) (x - y)) := by
  filter_upwards [Step2.eq530N hE hs0 hst ht1 hc (δ := 1 / 4) (D := D)
    (by norm_num)] with N hK u ω x y hfar
  rw [← norm_gloop_pm_eq_Lre (X.hermitian N (u : ℝ) ω) x y]
  apply Step2FarInputs.norm_gloop_pm_le_jS_mul_tT X (E N) D N (u : ℝ) ω x y
  exact (Step2FarInputs.norm_Kval_pm_le_norm_Theta (hE N).le B N (u : ℝ) x y).trans
    ((hK u x y (by simpa [one_div, inv_mul_eq_div] using hfar)).1.trans
      (rpow_neg_le_tailT _))

/-- **`jG ≤ 1 + N^τ (9 e^{√3} jS + 2)` with high probability**, uniformly in `u ∈ [s, t]`, from
the entry bound `hEntry` and the good set `hGood`. No energy-dependent constant is fixed here. -/
theorem highProb_jG_le_of_entryBoundFlowN (d : Gauss.Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N (Gauss.band d) E s t)
    (D : ℝ) (hD : 0 ≤ D)
    (hEntry : Gauss.EntryBoundFlow'N d E s t (fun N => 2 * (N : ℝ) ^ (-D)))
    (hGood : HighProb (Gauss.P d) (fun N => Gauss.goodSetFlow d (E N) s t
      (fun N => Gauss.flowDelta d (E N) t N) N))
    {τ : ℝ} (hτ : 0 < τ) :
    HighProb (Gauss.P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      jG (Gauss.sample d) (E N) N (u : ℝ) ω
        ((Gauss.band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D ≤
      1 + (N : ℝ) ^ τ *
        (9 * Real.exp (Real.sqrt 3) * Step2.jS (Gauss.sample d) (E N) D N (u : ℝ) ω + 2)}) := by
  have hEntryHP := hEntry.highProb hτ
  have hBoth := hEntryHP.inter hGood
  refine hBoth.mono ?_
  filter_upwards [eventually_Lre_le_jS_mul_tailT_quarterN hE hs0 hst ht1 (Gauss.sample d) hc D,
    eventually_twelve_le_ellStar (B := Gauss.band d) hs0 ht1 hst,
    (Gauss.band d).dim, Filter.eventually_ge_atTop 1] with N hLre hstar hdim hN1 ω hω' u
  obtain ⟨hentryω, hgoodω⟩ := hω'
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hLpos : (1 : ℝ) ≤ (d.L N : ℝ) := by
    exact_mod_cast (Gauss.band d).one_le_L N
  have hWN : (d.W N : ℝ) ≤ N := by
    have hdim' : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hfloor : ∀ x y : ZMod (d.L N),
      2 * (N : ℝ) ^ (-D) ≤
        2 * Step2.tT (Gauss.band d) (E N) N D (u : ℝ) (zdist (d.L N) (x-y)) := by
    intro x y
    have hWD : (N : ℝ) ^ (-D) ≤ (d.W N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hWpos hWN (by linarith)
    have hT := rpow_neg_le_tailT (W := (d.W N : ℝ))
      (ℓu := (Gauss.band d).ell N (u : ℝ)) (ηu := etaT (E N) (u : ℝ))
      (D := D) (zdist (d.L N) (x-y))
    dsimp [Step2.tT]
    linarith
  have hℓ : 1 ≤ (Gauss.band d).ell N (u : ℝ) :=
    one_le_ellHat_of_nonneg ((Gauss.band d).one_le_L N)
      ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hentryPoint : ∀ (i j : ZMod (d.L N) × Fin (d.W N)), i ≠ j →
      ‖green ((Gauss.sample d).H N (u : ℝ) ω) (zt (E N) (u : ℝ)) i j‖ ^ 2 ≤
        (N : ℝ) ^ τ *
          ((∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
              Lre ((Gauss.sample d).H N (u : ℝ) ω) (zt (E N) (u : ℝ)) (j.1 + b) (i.1 + a)) +
           (if i.1 - j.1 ∈ sbSupport (d.L N) then (d.W N : ℝ)⁻¹ else 0) +
           2 * (N : ℝ) ^ (-D)) := by
    intro i j hij
    have hmem : ω ∈ goodSet (L := d.L) (W := d.W)
        (fun N ω => Gauss.Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ))
        (mE (E N)) (Gauss.flowDelta d (E N) t) N := hgoodω (u : ℝ) u.2
    have he := hentryω (u, (⟨(i,j), hij⟩ : OffPair d.L d.W N))
    simp only [Set.indicator_of_mem hmem] at he
    convert he using 1 <;> simp only [Gauss.sample_H, Gauss.band_L, Gauss.band_W]
    · rfl
  have hF0 : 0 ≤ (N : ℝ) ^ τ *
      (9 * Real.exp (Real.sqrt 3) * Step2.jS (Gauss.sample d) (E N) D N (u : ℝ) ω + 2) := by
    have hJ := Step2Moment.one_le_jS (Gauss.sample d) (E := E N) (D := D) N (u : ℝ) ω
    positivity
  apply jG_le_of_neighbor_green_sq (Gauss.sample d) (E N) N (u : ℝ) ω
    ((Gauss.band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D
    ((N : ℝ) ^ τ *
      (9 * Real.exp (Real.sqrt 3) * Step2.jS (Gauss.sample d) (E N) D N (u : ℝ) ω + 2))
    (by simpa only [Gauss.band_W] using hWpos) hF0
  intro x y x' hxy hxx' p q
  exact neighbor_green_sq_le_of_entry_event (Gauss.sample d) (E N) D τ N (u : ℝ) ω
    hℓ (hstar u) (hLre u ω) hentryPoint hfloor hxx' hxy p q

section Compat

end Compat

end BlockGreen
end RBM

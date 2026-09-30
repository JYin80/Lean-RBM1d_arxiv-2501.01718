/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarStop
import RBM1D.Gauss.GridFarQVConv

/-!
# The far martingale at the stopping level `thrFar`: the Azuma constants

## Main declarations

* `cZFar` — the label-dependent Azuma constants: at far labels `6ℓ*_{u_k} < d_a` the split form
  `Δ(√QnF·leak + √QfF·((1-u_{j+1})/(1-u_k))²·Ξ·T_{u_k}(a))² + ΔN^{-Cc}` (the residual summand is
  identically `0`: `qvSet` bounds `quadVar` by `diagShape'`, which has no residual); at near
  labels Step 2's `cZ`.
* `FarMart.cZFar_nonneg`, `FarMart.floor_le_cZFar` — nonnegativity, and the positive floor
  `ΔN^{-Cc}`.
* `FarMart.eventually_step_gridK_le` — the grid-fineness condition on the pinned grid.

The far martingale is stopped at `min k gridTauFar` (level `thrFar = N^δ(η_s/η_u)^{13/4}`) and
bounded through `stopped_duhamel_azuma_union` (`GridDuhamelTail.lean`) with `τ = gridTauFar`,
`hτmeas = lt_gridTauFar_measurableSet` and `c = cZFar`; at far labels the one-step bound
`quadVar_step_le` and `qv_conv_le` are replaced by a split one-step bound (near indicator kept)
and `qv_conv_le_far`.  `Step2.thr` enters only as the upper bound `thrFar ≤ thr`
(`thrFar_le_thr'`); it is never the localisation.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## The far Azuma constants -/

namespace FarMart

variable (d : Dims)

/-- Near coefficient `QnF_j = 2N^{τ₁}(diagNearRate(ℓ_{u_j}, ℓ_s, η_{u_j}) + 2·nearEpsilon(J_j))`
at the far cap `J_j = N^{2ε}·thrFar(u_j)`. -/
def QnF (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ' ε D τ₁ : ℝ) (N j : ℕ) : ℝ :=
  2 * (N : ℝ) ^ τ₁ *
    (QVEndpoint.diagNearRate (band d) N ((band d).ell N (time s u K N j))
        ((band d).ell N (s N)) (etaT E (time s u K N j))
      + 2 * EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
          ((band d).ell N (time s u K N j)) (etaT E (time s u K N j)) D
          ((N : ℝ) ^ (2 * ε) * thrFar E s δ' N (time s u K N j)))

/-- Far coefficient `QfF_j = 2N^{τ₁}·diagFarRate(ℓ_{u_j}, η_{u_j}, D, J_j, sDet(u_j, ℓ_s))`
plus the time-shift term `2 Csh(u_{j+1})² Δ² W^{2D}` of `Qprime`. -/
def QfF (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ' ε D τ₁ : ℝ) (N j : ℕ) : ℝ :=
  2 * (N : ℝ) ^ τ₁ *
      QVEndpoint.diagFarRate (band d) N ((band d).ell N (time s u K N j))
        (etaT E (time s u K N j)) D ((N : ℝ) ^ (2 * ε) * thrFar E s δ' N (time s u K N j))
        (EarlyQVRateEv.sDet (band d) E N (time s u K N j) ((band d).ell N (s N)))
    + 2 * qvTimeShiftConst d N E (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2
        * ((band d).W N : ℝ) ^ (2 * D)

/-- The near → far leakage factor of `qv_conv_le_far` from `u_{j+1}` to `u_k`. -/
def leak (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (N k j : ℕ) : ℝ :=
  tailT (d.W N : ℝ) (ellHat (d.L N) (time s u K N (j + 1) : ℂ))
      ((1 - time s u K N (j + 1)) * (mE E).im) D 0 *
    (128 * Real.exp 3 * ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2 *
      Real.exp (-(ellStar (d.W N : ℝ) (ellHat (d.L N) (time s u K N k : ℂ)) /
        ellHat (d.L N) (time s u K N k : ℂ) / 2)))

end FarMart

variable {d : Dims}

variable (d) in
/-- **Label-dependent Azuma constants**.  At far labels
`6ℓ*_{u_k} < d_a`:
`Δ·(√QnF_j·leak_{k,j} + √QfF_j·((1-u_{j+1})/(1-u_k))²·Ξ·T_{u_k}(a))² + Δ·N^{-Cc}`
(the residual summand `√QrF_j·(…)²` of the design comment is identically `0`, because `qvSet`
bounds `quadVar` by `diagShape'`, which has no residual term). At near labels: Step 2's `cZ`. -/
def cZFar (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ' ε D τ₁ Cc : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (j : ℕ) : ℝ :=
  if 6 * ellStar ((band d).W N : ℝ) ((band d).ell N (time s u K N k)) <
      (zdist (d.L N) (a 0 - a 1) : ℝ) then
    step s u K N * (Real.sqrt (FarMart.QnF d E s u K δ' ε D τ₁ N j) *
          FarMart.leak d E s u K D N k j
        + Real.sqrt (FarMart.QfF d E s u K δ' ε D τ₁ N j) *
          ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2 *
          Step2.xiK (d.L N) (d.W N) (mE E).im *
          Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))) ^ 2
      + step s u K N * (N : ℝ) ^ (-Cc)
  else cZ d E s u K δ' ε D τ₁ Cc N k a j

namespace FarMart

theorem cZFar_nonneg {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ' ε D τ₁ Cc : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) (j : ℕ) :
    0 ≤ cZFar d E s u K δ' ε D τ₁ Cc N k a j := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold cZFar
  split_ifs
  · have : 0 ≤ (N : ℝ) ^ (-Cc) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  · exact cZ_nonneg hsu k a j

theorem floor_le_cZFar {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ' ε D τ₁ Cc : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) (j : ℕ) :
    step s u K N * (N : ℝ) ^ (-Cc) ≤ cZFar d E s u K δ' ε D τ₁ Cc N k a j := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold cZFar
  split_ifs
  · have : 0 ≤ step s u K N * (Real.sqrt (QnF d E s u K δ' ε D τ₁ N j) *
          leak d E s u K D N k j
        + Real.sqrt (QfF d E s u K δ' ε D τ₁ N j) *
          ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2 *
          Step2.xiK (d.L N) (d.W N) (mE E).im *
          Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))) ^ 2 := by
      positivity
    linarith
  · exact floor_le_cZ hsu k a j

/-! ## The far `v_Ab` bound (`v_Ab_le` with `qv_conv_le_far`) -/

variable {N : ℕ}

/-! ## The split one-step QV bound (`quadVar_step_le` with the near indicator kept) -/

/-! ## The conditional sub-Gaussian constants at `gridTauFar` -/

/-! ## Exponent control for the far quadratic-variation sum (pure real arithmetic) -/

end FarMart

section Main

open FarMart

/-- The grid-fineness condition of the far quadratic-variation sum holds on the pinned grid
`gridK D (D₁ + 2)` (`C_K = D₁ + 2D + 82 ≥ D + 20`): its compiled satisfiability witness. -/
theorem FarMart.eventually_step_gridK_le {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {D D₁ : ℝ} (hD0 : 0 ≤ D) (hD₁ : 0 ≤ D₁) :
    ∀ᶠ N : ℕ in atTop, step s u (gridK D (D₁ + 2)) N ≤ (N : ℝ) ^ (-(D + 20)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hus : u N - s N ≤ 1 := by linarith [hs0 N, hut N, ht1 N]
  refine (step_gridK_le hN1 hus).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith)

end Main

end RBM.Gauss.Grid

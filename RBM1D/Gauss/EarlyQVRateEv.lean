/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Gauss.Step2Bootstrap
import RBM1D.Flow.Step1Producer

/-!
# T267: the probabilistic wrapper of `(S3)`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §2.7 (2.73), §5.2–§5.3, (5.22), (5.27), (5.28), (5.36), (5.46), (5.71)–(5.72).

T262 (`RBM1D/Gauss/EarlyQVRate.lean`) proved `(S3)` **pointwise in `(u, ω)`**:
`RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` bounds
`quadVar (M ↦ (L-K)_{u,σ,b}(M)) (H_u)` by the sharp right-hand side of (5.36), given the
a-priori Step-1 input `h273`, the far-field remainder `h564`, the decay `h42sq`, and the
structural witnesses `Gm`, `Gsq`, `Smax`.  This file supplies the missing half: the same
bound **simultaneously at every grid time `u_j`, `j ≤ n_N`, and at every label pair
`b ∈ (ℤ_L)²`**, on one event of probability `≥ 1 - N^{-D''}`.

## What is here

* `RBM.EarlyQVRateEv.gMax`, `sMax`, `jStar` — the three structural witnesses, as **finite
  maxima of the Green function and of the loops themselves**, not as hypotheses.  `Gm := gMax`
  (constant in `(x,y)`), `Gsq := gMax²`, `Smax := sMax`, `J := jStar`; the slots `hGm`,
  `hGm0`, `hGsq0`, `hGsq2`, `hrow`, `hSmax` and `h42sq` of
  `RBM.EEDef.ee_le_EEpath_sym` are then *theorems* (`norm_Gsig_le_gMax`,
  `re_gloop_four_le_sMax`, `gMax_sq_le_jStar_mul_tailT`).  `jStar` is literally `J_{u,D}` of
  (5.28) — a maximum of `Gsq / T_{u,D}` over the far pairs, plus `1` — which is why `h42sq`
  costs nothing; the paper's (5.36) carries `J*_{u,D}` on its right-hand side for the same
  reason.
* `RBM.EarlyQVRateEv.sMax_le` — the `Smax` slot bounded by (2.73) at `n = 4`, i.e. the
  paper's `μ ≺ r_u^{3/2} A_u^{-3/2}` (`μ = 2√Smax`).
* `RBM.EarlyQVRateEv.glueLD0`, `glueLD1`, `glueLD0_idx`, `glueLD1_idx`, `eeL6_two_le` —
  **`h273` is (2.73) at `n = 6`**: the two glued `6`-loops of Figure 14
  (`RBM.EEDef.glueIdx_two_zero` / `_two_one`) are `RBM.LoopData _ 6`, i.e. members of the
  family that `RBM.Step1.apriori` controls, and `∑_{b'} ‖S_{bb'}‖ = 1`
  (`RBM.sum_norm_SB_apply_row`), so a uniform bound `C` on the `6`-loops gives `eeL6 ≤ 2C`.
* `RBM.EarlyQVRateEv.rho0`, `s3Rhs`, `s3At`, `quadVar_le_s3Rhs`, `quadVar_le_mul_s3At` — the
  right-hand side of `(S3)`, and the pointwise bound with the (2.73) level `K` made explicit.
  The additive remainder `ρ` of `h564` is the (2.73) level itself, so **`h564` follows from
  `h273`** and is not a separate input.
* `RBM.EarlyQVRateEv.stochDom_quadVar_grid` — **the deliverable**, in `≺` form: with the
  index set `U N = {j ≤ n_N} × (Fin 2 → Bool) × (ℤ_L)²`,
  `quadVar (L-K)_{u_j,σ,b} ≺ (S3)-RHS`, uniformly over the index set.
* `RBM.EarlyQVRateEv.prob_exists_grid_le` — the same, unfolded:
  `∀ ε > 0, ∀ D'' > 0, ∃ N₀, ∀ N ≥ N₀, P(∃ j ≤ n_N, ∃ σ, ∃ b, quadVar > N^ε · RHS) ≤ N^{-D''}`.
* `RBM.EarlyQVRateEv.sat_stochDom_quadVar_grid` — satisfiability on a non-degenerate grid.
* `RBM.EarlyQVRateEv.sDet`, `s3Rhs_sqrt_le`, `s3AtDet`, `s3At_le_mul_s3AtDet`,
  `quadVar_le_mul_s3AtDet`, `s3GridDet`, `stochDom_quadVar_grid_det`,
  `sat_stochDom_quadVar_grid_det` — **T273a**: the same `≺` with `μ = 2√Smax` already
  evaluated at its (2.73) level `(ℓ_u/ℓ_s)^3(Wℓ_uη_u)^{-3}`, i.e. the paper's
  `μ ≺ r_u^{3/2}A_u^{-3/2}`.  `ζ` still does not depend on `τ`: the two a-priori levels are
  taken at `τ/4` and the loss `2N^{τ/4}√(N^{τ/4}) ≤ N^τ` goes into the `N^τ` of `RBM.StochDom`.

## Where the union bound comes from, and why no new hypothesis appears

`RBM.StochDom P ξ ζ` already *is* a union bound: its failure event is
`{ω | ∃ u ∈ U N, N^τ ζ < ξ}`, with the `∃` over the whole index set inside one probability.
Taking `U N = {j ≤ n_N} × … × (ℤ_L)²` therefore gives the union over the grid and over `b` at
one and the same `N₀`, which is exactly what `(S3)` asks for; the machinery is
`RBM.Step1.apriori` (which produces the `≺` at `n = 6` uniformly in `u ∈ [s,t]`, via
`RBM.Step1.NetLift` inside `RBM.Step1.Hyp`) plus `RBM.MomentDuhamelCut.netFinset_subset_Icc`
(every grid point lies in the window) and the level split `τ ↦ τ/2` with
`RBM.eventually_le_rpow`.

**No new named hypothesis is introduced.**  The hypothesis list of
`stochDom_quadVar_grid` is, verbatim, the hypothesis list of `RBM.Step1.apriori` — `0 < κ`,
`|E| ≤ 2-κ`, `RBM.BoundsCore`, `0 ≤ s`, `s ≤ t`, `t < 1`, `RBM.Cond272`, `0 < c`, the regime
`N^c ≤ W ℓ_t η_t`, and `RBM.Step1.Hyp` — together with `0 < mesh N`, which is the
non-degeneracy of the net of (5.46), not a statement about the random model.

## Quantifier order

`prob_exists_grid_le` reads `∀ ε > 0, ∀ D'' > 0, ∃ N₀, ∀ N ≥ N₀, …`: the thresholds are
chosen **before** `N₀`.  The forbidden `∀ N, ∃ …` shape would be satisfiable by a constant.
The time quantifier never leaves the window: the grid points are `u_j ∈ [s_N, t_N]` with
`0 ≤ s_N` and `t_N < 1`, so `z_u` stays regular.

## Vacuity check

The wrapper is an inequality **on an event**, not a pointwise inequality for all `ω`: the
statement is a `RBM.StochDom`, whose content is a measure bound.  The three witnesses
`gMax`, `sMax`, `jStar` are *defined* from `(N, u, ω)` — at `ω = 0` (`H = 0`, `G = -z⁻¹`) and
at "a large multiple of the identity" they are finite and the bound is a true, non-trivial
inequality, not a vacuous one.  `jStar ≥ 1` and `√sMax ≥ 0` are proved, so `J*` is never
taken to be `0`; `sat_stochDom_quadVar_grid` certifies in addition that the window does not
collapse (`u_0 < u_1`) and that **the grid does not collapse to a single point**
(`1 ≤ n_N` eventually), i.e. the union really runs over at least two times.

Nothing here is an `axiom` and nothing is `sorry`.
-/

namespace RBM

namespace EarlyQVRateEv

open Matrix Finset RBM.Gauss MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ### 1. The structural witnesses `Gm`, `Gsq`, `Smax`, `J*`, as finite maxima -/

/-- A point of `B.Idx N`; the block index type is never empty (`B.W_pos`, `B.three_le_L`). -/
def idx0 (B : Band Ω) (N : ℕ) : B.Idx N := (0, ⟨0, B.W_pos N⟩)

/-- `‖G_u‖_max` in the honest form the `hGm` slot of `RBM.EEDef.ee_le_EEpath_sym` asks for:
the maximum over both charges and all pairs of entries of `|G_u(σ)_{pq}|`. -/
noncomputable def gMax (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Bool × B.Idx N × B.Idx N)).sup'
    ⟨(true, idx0 B N, idx0 B N), Finset.mem_univ _⟩
    (fun q => ‖Gsig (X.H N u ω) (zt E u) q.1 q.2.1 q.2.2‖)

theorem norm_Gsig_le_gMax (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (s : Bool) (p q : B.Idx N) :
    ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ gMax X E N u ω :=
  Finset.le_sup' (f := fun q : Bool × B.Idx N × B.Idx N =>
    ‖Gsig (X.H N u ω) (zt E u) q.1 q.2.1 q.2.2‖) (Finset.mem_univ (s, p, q))

theorem gMax_nonneg (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    0 ≤ gMax X E N u ω :=
  le_trans (norm_nonneg _) (norm_Gsig_le_gMax X E N u ω true (idx0 B N) (idx0 B N))

/-- The `Smax` slot: the maximum of the real part of the `4`-loops of (5.66). -/
noncomputable def sMax (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Bool × ZMod (B.L N) × ZMod (B.L N) × ZMod (B.L N))).sup'
    ⟨(true, 0, 0, 0), Finset.mem_univ _⟩
    (fun q => (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[q.1, !q.1, q.1, !q.1], [q.2.1, q.2.2.1, q.2.1, q.2.2.2]⟩).re)

theorem re_gloop_four_le_sMax (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (s : Bool) (x y y' : ZMod (B.L N)) :
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ sMax X E N u ω :=
  Finset.le_sup' (f := fun q : Bool × ZMod (B.L N) × ZMod (B.L N) × ZMod (B.L N) =>
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[q.1, !q.1, q.1, !q.1], [q.2.1, q.2.2.1, q.2.1, q.2.2.2]⟩).re)
    (Finset.mem_univ (s, x, y, y'))

/-- **`J*_{u,D}` of (5.28)** for the squared `G`-pair: the maximum over the far pairs of
`Gsq / T_{u,D}`, plus `1`.  This is a *definition*, not a hypothesis: `h42sq` holds for it by
construction, and the paper's (5.36) carries `J*` on its right-hand side exactly so. -/
noncomputable def jStar (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) (ℓu ηu D : ℝ) : ℝ :=
  1 + (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
    ⟨(0, 0), Finset.mem_univ _⟩
    (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
      then gMax X E N u ω * gMax X E N u ω
        / tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
      else 0)

theorem one_le_jStar (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {ℓu ηu D : ℝ}
    (hW : (0 : ℝ) < (B.W N : ℝ)) : 1 ≤ jStar X E N u ω ℓu ηu D := by
  have h0 : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
        then gMax X E N u ω * gMax X E N u ω
          / tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ ((0 : ZMod (B.L N)), (0 : ZMod (B.L N)))))
    have hT := tailT_pos (W := (B.W N : ℝ)) (ℓu := ℓu) (ηu := ηu) (D := D) hW
      (zdist (B.L N) ((0 : ZMod (B.L N)) - 0) : ℝ)
    have hg := gMax_nonneg X E N u ω
    dsimp only
    split
    · positivity
    · exact le_rfl
  rw [jStar]; linarith

/-- **`h42sq` for the definitional `J*`.**  `Gsq = (‖G‖_max)²` and `J*` is the maximum of
`Gsq / T_{u,D}` over the far pairs, so the inequality is the defining one. -/
theorem gMax_sq_le_jStar_mul_tailT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    {ℓu ηu D : ℝ} (hW : (0 : ℝ) < (B.W N : ℝ)) (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ)) :
    gMax X E N u ω * gMax X E N u ω
      ≤ jStar X E N u ω ℓu ηu D * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
  have hT := tailT_pos (W := (B.W N : ℝ)) (ℓu := ℓu) (ηu := ηu) (D := D) hW
    ((zdist (B.L N) (x - y) : ℝ))
  have hle : gMax X E N u ω * gMax X E N u ω
      / tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))
      ≤ (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
        ⟨(0, 0), Finset.mem_univ _⟩
        (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
          then gMax X E N u ω * gMax X E N u ω
            / tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
          else 0) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (x, y)))
    dsimp only
    split
    · rfl
    · rename_i hcon; exact absurd hxy hcon
  have hd : gMax X E N u ω * gMax X E N u ω
      ≤ (1 + (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
          ⟨(0, 0), Finset.mem_univ _⟩
          (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
            then gMax X E N u ω * gMax X E N u ω
              / tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
            else 0))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
    have h1 : gMax X E N u ω * gMax X E N u ω
        / tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))
        = gMax X E N u ω * gMax X E N u ω := div_mul_cancel₀ _ hT.ne'
    nlinarith [hT, mul_le_mul_of_nonneg_right hle hT.le]
  simpa [jStar] using hd

/-- **The `Smax` slot from (2.73) at `n = 4`.**  `Smax` is a maximum of real parts of `4`-loops,
so any uniform bound on the `4`-loops at the time `u` — in particular the one
`RBM.Step1.apriori` gives at `n = 4`, `N^τ (ℓ_u/ℓ_s)^3 (Wℓ_uη_u)^{-3}` — bounds it.  This is
the `μ ≺ r_u^{3/2} A_u^{-3/2}` of the paper: `μ = 2√Smax`. -/
theorem sMax_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {C : ℝ}
    (hC : ∀ p : LoopData (B.L N) 4, ‖X.Lval E N u ω p.idx‖ ≤ C) :
    sMax X E N u ω ≤ C := by
  refine Finset.sup'_le _ _ (fun q _ => ?_)
  have h := hC (![q.1, !q.1, q.1, !q.1], ![q.2.1, q.2.2.1, q.2.1, q.2.2.2])
  have hidx : (LoopData.idx
      (![q.1, !q.1, q.1, !q.1], ![q.2.1, q.2.2.1, q.2.1, q.2.2.2]) : LoopIdx (ZMod (B.L N)))
      = ⟨[q.1, !q.1, q.1, !q.1], [q.2.1, q.2.2.1, q.2.1, q.2.2.2]⟩ := by
    simp [LoopData.idx, List.ofFn_succ]
  rw [hidx] at h
  exact le_trans (Complex.re_le_norm _) h

/-! ### 2. `h273`: the glued `6`-loops of (5.22) are `6`-loops of (2.73) -/

/-- The `k = 0` glued loop of Figure 14, as an element of `RBM.LoopData L 6`. -/
def glueLD0 {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    LoopData L 6 :=
  (![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)],
   ![EEBridge.leftArg c 0, EEBridge.leftArg c 1, b,
     EEBridge.rightArg c 1, EEBridge.rightArg c 0, b'])

/-- The `k = 1` glued loop of Figure 14, as an element of `RBM.LoopData L 6`. -/
def glueLD1 {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    LoopData L 6 :=
  (![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)],
   ![EEBridge.leftArg c 1, EEBridge.leftArg c 0, b,
     EEBridge.rightArg c 0, EEBridge.rightArg c 1, b'])

theorem glueLD0_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    (glueLD0 σ c b b').idx
      = EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c)) 0 b b' := by
  rw [EEDef.glueIdx_two_zero]
  simp [glueLD0, LoopData.idx, List.ofFn_succ]

theorem glueLD1_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    (glueLD1 σ c b b').idx
      = EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c)) 1 b b' := by
  rw [EEDef.glueIdx_two_one]
  simp [glueLD1, LoopData.idx, List.ofFn_succ]

/-- **`h273` from (2.73) at `n = 6`.**  Every glued `6`-loop of (5.22) is a `6`-loop of the
family that `RBM.Step1.apriori` controls, and `∑_{b'} ‖S_{bb'}‖ = 1`
(`RBM.sum_norm_SB_apply_row`), so a uniform bound `C` on the `6`-loops gives `eeL6 ≤ 2 C`. -/
theorem eeL6_two_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2)) (b : ZMod (B.L N)) {C : ℝ}
    (hC : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖ ≤ C) :
    EEDef.eeL6 X E N u ω σ c b ≤ 2 * C := by
  classical
  have hrow := sum_norm_SB_apply_row (B.L N) (B.three_le_L N) b
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (glueLD0 σ c b b))
  have key : ∀ k : ℕ, (∀ b' : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c))
          k b b')‖ ≤ C) → EEDef.eeL6k X E N u ω σ c k b ≤ C := by
    intro k hk
    have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
        ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
            (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c))
              k b b')‖ ≤ ‖SB (B.L N) b b'‖ * C :=
      fun b' _ => mul_le_mul_of_nonneg_left (hk b') (norm_nonneg _)
    calc EEDef.eeL6k X E N u ω σ c k b ≤ ∑ b' : ZMod (B.L N), ‖SB (B.L N) b b'‖ * C :=
          Finset.sum_le_sum hstep
      _ = C := by rw [← Finset.sum_mul, hrow, one_mul]
  have h0 : EEDef.eeL6k X E N u ω σ c 0 b ≤ C :=
    key 0 fun b' => by rw [← glueLD0_idx σ c b b']; exact hC _
  have h1 : EEDef.eeL6k X E N u ω σ c 1 b ≤ C :=
    key 1 fun b' => by rw [← glueLD1_idx σ c b b']; exact hC _
  rw [EEDef.eeL6_two_eq]
  linarith

/-! ### 3. The right-hand side of `(S3)`, and the pointwise bound on the Step-1 event -/

/-- The additive remainder `ρ` of `RBM.EEDef.ee_le_EEpath_sym`, at the level (2.73) gives:
`ρ = κ_near · (W ℓ_u η_u)^{-5}`, with `κ_near = (ℓ_u/ℓ_s)^5`. -/
noncomputable def rho0 (W ℓu ηu κn : ℝ) : ℝ :=
  κn * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((W * ℓu * ηu))⁻¹

/-- **The right-hand side of `(S3)`**, verbatim the conclusion of
`RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` with `(ℓ_u/ℓ_s)^5` abbreviated to `κn` and
`ρ = rho0`. -/
noncomputable def s3Rhs (W Lr ℓu ηu D κn J S d : ℝ) : ℝ :=
  2 * (ηu⁻¹ * (Lemma57.cNear2 W ℓu * κn * (if d ≤ 4 * ellStar W ℓu then 1 else 0)
        + Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * (2 * √S)))
        + 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D d ^ 2
      + (W * Lr * rho0 W ℓu ηu κn
        + 2 * W * Lr * W ^ (-D) * (2 * J) ^ 3 * tailT W ℓu ηu D d ^ 2))

theorem rho0_nonneg {W ℓu ηu κn : ℝ} (hW : 0 ≤ W) (hℓu : 0 ≤ ℓu) (hηu : 0 ≤ ηu)
    (hκn : 0 ≤ κn) : 0 ≤ rho0 W ℓu ηu κn := by
  have : (0 : ℝ) ≤ W * ℓu * ηu := by positivity
  unfold rho0; positivity

/-- `κn ↦ s3Rhs` is affine with non-negative coefficients, so inflating `κn` by `M ≥ 1`
inflates the whole right-hand side by at most `M`. -/
theorem s3Rhs_mul_le {W Lr ℓu ηu D κn J S d M : ℝ} (hW : 1 ≤ W) (hLr : 0 ≤ Lr)
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hJ : 1 ≤ J) (hM : 1 ≤ M) :
    s3Rhs W Lr ℓu ηu D (M * κn) J S d ≤ M * s3Rhs W Lr ℓu ηu D κn J S d := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hA : (0 : ℝ) < W * ℓu * ηu := by positivity
  have hT : 0 < tailT W ℓu ηu D d := tailT_pos hW0 d
  have hcN : 0 ≤ Lemma57.cNear2 W ℓu := Lemma57.cNear2_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar2 W ℓu := Lemma57.cFar2_nonneg hW hℓu
  have hind : (0 : ℝ) ≤ (if d ≤ 4 * ellStar W ℓu then 1 else 0) := by split <;> norm_num
  have hJ0 : (0 : ℝ) ≤ 2 * J := by linarith
  have hsq : (0 : ℝ) ≤ √S := Real.sqrt_nonneg S
  have hWD : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  -- the part of the right-hand side that does not involve `κn`
  set C₂ : ℝ := 2 * (ηu⁻¹ * (Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * (2 * √S)))
      + 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D d ^ 2
      + 2 * W * Lr * W ^ (-D) * (2 * J) ^ 3 * tailT W ℓu ηu D d ^ 2) with hC₂
  set C₁ : ℝ := 2 * (ηu⁻¹ * (Lemma57.cNear2 W ℓu * (if d ≤ 4 * ellStar W ℓu then 1 else 0))
      * tailT W ℓu ηu D d ^ 2
      + W * Lr * ((((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((W * ℓu * ηu))⁻¹)) with hC₁
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]; have : (0 : ℝ) ≤ ηu⁻¹ := by positivity
    have h1 : (0 : ℝ) ≤ (W * ℓu * ηu)⁻¹ := by positivity
    positivity
  have he₁ : s3Rhs W Lr ℓu ηu D (M * κn) J S d = (M * κn) * C₁ + C₂ := by
    rw [s3Rhs, rho0, hC₁, hC₂]; ring
  have he₂ : s3Rhs W Lr ℓu ηu D κn J S d = κn * C₁ + C₂ := by
    rw [s3Rhs, rho0, hC₁, hC₂]; ring
  rw [he₁, he₂]
  nlinarith [hC₂0, hM]

/-- **`(S3)`, pointwise on the Step-1 event.**  The structural witnesses `Gm`, `Gsq`, `Smax`
and `J*` are the finite maxima of §1 — they cost no hypothesis — and the additive remainder
`ρ` of the far field is the (2.73) level itself, so `h564` follows from `h273`.  The single
probabilistic input is `h273`. -/
theorem quadVar_le_s3Rhs (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω) (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ηu D κn : ℝ} (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu) (hκn : 0 < κn)
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ rho0 (B.W N : ℝ) ℓu ηu κn) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ s3Rhs (B.W N : ℝ) (B.L N : ℝ) ℓu ηu D κn (jStar X E N u ω ℓu ηu D)
          (sMax X E N u ω) (zdist (B.L N) (a 0 - a 1)) := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hℓu0 : (0 : ℝ) < ℓu := by linarith
  set ℓs : ℝ := ℓu / κn ^ ((1 : ℝ) / 5) with hℓs_def
  have hpow : (0 : ℝ) < κn ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hκn _
  have hℓs : 0 < ℓs := by rw [hℓs_def]; positivity
  have hratio : (ℓu / ℓs) ^ 5 = κn := by
    rw [hℓs_def, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hℓu0.ne', mul_one,
      ← Real.rpow_natCast (κn ^ ((1 : ℝ) / 5)) 5, ← Real.rpow_mul hκn.le]
    norm_num
  have hρ : 0 ≤ rho0 (B.W N : ℝ) ℓu ηu κn :=
    rho0_nonneg hW0.le hℓu0.le hηu.le hκn.le
  have h273' : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (((B.W N : ℝ) * ℓu * ηu))⁻¹ := by
    intro b; rw [hratio]; exact h273 b
  have hmain := EarlyQVRate.quadVar_lkFun_le_ee_sym X hE hu0 hu1 ω σ a
    (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) (D := D) (J := jStar X E N u ω ℓu ηu D)
    (Gm := fun _ _ => gMax X E N u ω)
    (Gsq := fun _ _ => gMax X E N u ω * gMax X E N u ω)
    (Smax := sMax X E N u ω) (ρ := rho0 (B.W N : ℝ) ℓu ηu κn)
    hℓu hℓs hηu (one_le_jStar X E N u ω hW0) hρ
    (fun _ _ => gMax_nonneg X E N u ω)
    (fun s x y p q _ _ => norm_Gsig_le_gMax X E N u ω s p q)
    (fun _ _ => mul_nonneg (gMax_nonneg X E N u ω) (gMax_nonneg X E N u ω))
    (fun _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (fun s x y y' => re_gloop_four_le_sMax X E N u ω s x y y')
    h273' (fun b _ => h273 b)
    (fun x y hxy => gMax_sq_le_jStar_mul_tailT X E N u ω hW0 x y hxy)
  refine hmain.trans (le_of_eq ?_)
  rw [s3Rhs, rho0, hratio]

/-! ### 4. `(S3)` at one time, from the a-priori bound (2.73) at `n = 6` -/

/-- The right-hand side of `(S3)` at a single time `u`, with the near coefficient
`(ℓ_u/ℓ_s)^5` of (2.73). -/
noncomputable def s3At (X : Sample B) (E : ℝ) (N : ℕ) (u ℓs D : ℝ) (ω : Ω)
    (a : LoopArg (B.L N) (0 + 2)) : ℝ :=
  s3Rhs (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D ((B.ell N u / ℓs) ^ 5)
    (jStar X E N u ω (B.ell N u) (etaT E u) D) (sMax X E N u ω)
    (zdist (B.L N) (a 0 - a 1))

/-- **`(S3)` at one time from (2.73) at `n = 6`.**  A bound `K · (ℓ_u/ℓ_s)^5 (Wℓ_uη_u)^{-5}`
on every `6`-loop at the time `u` — which is what `RBM.Step1.apriori` delivers at the level
`K = N^τ` — gives the quadratic-variation rate with the loss `2K`. -/
theorem quadVar_le_mul_s3At (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u ℓs : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hℓs : 0 < ℓs) (ω : Ω) (σ : Fin (0 + 2) → Bool)
    (a : LoopArg (B.L N) (0 + 2)) {D K : ℝ} (hK : 1 ≤ K)
    (hL : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖
      ≤ K * (B.ell N u / ℓs) ^ 5 * (B.scale E N u)⁻¹ ^ 5) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ (2 * K) * s3At X E N u ℓs D ω a := by
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓu : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hℓu0 : (0 : ℝ) < B.ell N u := by linarith
  have hηu : 0 < etaT E u := etaT_pos hE hu1
  have hA : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  have hA0 : (0 : ℝ) < B.scale E N u := by rw [hA]; positivity
  set κn₀ : ℝ := (B.ell N u / ℓs) ^ 5 with hκ0def
  have hκ0 : 0 < κn₀ := by rw [hκ0def]; positivity
  have hK0 : (0 : ℝ) < K := by linarith
  have hκn : 0 < (2 * K) * κn₀ := by positivity
  have hrho : rho0 (B.W N : ℝ) (B.ell N u) (etaT E u) ((2 * K) * κn₀)
      = 2 * (K * κn₀ * (B.scale E N u)⁻¹ ^ 5) := by
    rw [rho0, ← hA, ← inv_pow]
    ring
  have h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ rho0 (B.W N : ℝ) (B.ell N u) (etaT E u) ((2 * K) * κn₀) := by
    intro b
    rw [hrho]
    refine eeL6_two_le X E N u ω σ (Fin.append a a) b (fun p => ?_)
    have := hL p
    calc ‖X.Lval E N u ω p.idx‖ ≤ K * (B.ell N u / ℓs) ^ 5 * (B.scale E N u)⁻¹ ^ 5 := this
      _ = K * κn₀ * (B.scale E N u)⁻¹ ^ 5 := by rw [hκ0def]
  have hstep := quadVar_le_s3Rhs X hE hu0 hu1 ω σ a (D := D) hℓu hηu hκn h273
  refine hstep.trans ?_
  have hscale := s3Rhs_mul_le (W := (B.W N : ℝ)) (Lr := (B.L N : ℝ)) (ℓu := B.ell N u)
    (ηu := etaT E u) (D := D) (κn := κn₀) (J := jStar X E N u ω (B.ell N u) (etaT E u) D)
    (S := sMax X E N u ω) (d := (zdist (B.L N) (a 0 - a 1) : ℝ)) (M := 2 * K)
    hW1 (Nat.cast_nonneg _) hℓu0 hηu (one_le_jStar X E N u ω hW0) (by linarith)
  exact hscale

/-! ### 5. The union bound over the grid and over `b` -/

theorem s3Rhs_nonneg {W Lr ℓu ηu D κn J S d : ℝ} (hW : 1 ≤ W) (hLr : 0 ≤ Lr)
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hκn : 0 ≤ κn) (hJ : 1 ≤ J) :
    0 ≤ s3Rhs W Lr ℓu ηu D κn J S d := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hA : (0 : ℝ) < W * ℓu * ηu := by positivity
  have hT : 0 < tailT W ℓu ηu D d := tailT_pos hW0 d
  have hcN : 0 ≤ Lemma57.cNear2 W ℓu := Lemma57.cNear2_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar2 W ℓu := Lemma57.cFar2_nonneg hW hℓu
  have hind : (0 : ℝ) ≤ (if d ≤ 4 * ellStar W ℓu then 1 else 0) := by split <;> norm_num
  have hJ0 : (0 : ℝ) ≤ 2 * J := by linarith
  have hsq : (0 : ℝ) ≤ √S := Real.sqrt_nonneg S
  have hWD : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hAi : (0 : ℝ) ≤ (W * ℓu * ηu)⁻¹ := by positivity
  have hρ : 0 ≤ rho0 W ℓu ηu κn := rho0_nonneg hW0.le hℓu.le hηu.le hκn
  have hηi : (0 : ℝ) ≤ ηu⁻¹ := by positivity
  rw [s3Rhs]
  have h1 : (0 : ℝ) ≤ Lemma57.cNear2 W ℓu * κn * (if d ≤ 4 * ellStar W ℓu then 1 else 0) := by
    positivity
  have h2 : (0 : ℝ) ≤ Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * (2 * √S))) := by
    positivity
  have h3 : (0 : ℝ) ≤ 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹ := by positivity
  have h4 : (0 : ℝ) ≤ 2 * W * Lr * W ^ (-D) * (2 * J) ^ 3 * tailT W ℓu ηu D d ^ 2 := by
    positivity
  have h5 : (0 : ℝ) ≤ W * Lr * rho0 W ℓu ηu κn := by positivity
  have h6 : (0 : ℝ) ≤ ηu⁻¹ * (Lemma57.cNear2 W ℓu * κn * (if d ≤ 4 * ellStar W ℓu then 1 else 0)
      + Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * (2 * √S)))
      + 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D d ^ 2 := by
    have : (0 : ℝ) ≤ Lemma57.cNear2 W ℓu * κn * (if d ≤ 4 * ellStar W ℓu then 1 else 0)
      + Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * (2 * √S)))
      + 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹ := by linarith
    have hTT : (0 : ℝ) ≤ tailT W ℓu ηu D d ^ 2 := by positivity
    have := mul_nonneg (mul_nonneg hηi this) hTT
    linarith
  linarith

/-- The index set of the union bound: a grid time `u_j` with `j ≤ n_N`, a charge vector `σ`,
and the label pair `b = (b₁, b₂) ∈ (ℤ_L)²`. -/
abbrev GridIdx (B : Band Ω) (s t mesh : ℕ → ℝ) (N : ℕ) : Type :=
  {j : ℕ // j ≤ CutHypTheta.cutNetTop s t mesh N} × (Fin (0 + 2) → Bool)
    × LoopArg (B.L N) (0 + 2)

/-- The quadratic variation of `(L-K)_{u_j,σ,b}` at the grid time `u_j`. -/
noncomputable def qvGrid (X : Sample B) (E : ℝ) (s t mesh : ℕ → ℝ) :
    ∀ N, GridIdx B s t mesh N → Ω → ℝ :=
  fun N v ω => quadVar B.toDims N
    (fun M' => MomentDuhamel.lkFun B E N (CutHypTheta.cutNetPt s mesh N v.1.1) M' v.2.1 v.2.2)
    (X.H N (CutHypTheta.cutNetPt s mesh N v.1.1) ω)

/-- The right-hand side of `(S3)` at the grid time `u_j`, with `ℓ_s = ℓ_{s_N}`. -/
noncomputable def s3Grid (X : Sample B) (E : ℝ) (s t mesh : ℕ → ℝ) (D : ℝ) :
    ∀ N, GridIdx B s t mesh N → Ω → ℝ :=
  fun N v ω =>
    s3At X E N (CutHypTheta.cutNetPt s mesh N v.1.1) (B.ell N (s N)) D ω v.2.2

/-- **The probabilistic wrapper of `(S3)`.**  The Step-1 event of (2.73) is instantiated at
every grid time `u_j`, `j ≤ n_N`, at once, and the union bound over `j` and over
`b ∈ (ℤ_L)²` is the one `RBM.StochDom` already takes over its index set. -/
theorem stochDom_quadVar_grid (X : Sample B) {E : ℝ} {s t mesh : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (hHyp : Step1.Hyp X E s t) (hmesh : ∀ N, 0 < mesh N) (D : ℝ) :
    StochDom B.P (qvGrid X E s t mesh) (s3Grid X E s t mesh D) := by
  have hE2 : |E| < 2 := by
    have := abs_nonneg E; linarith
  have hap := Step1.apriori X hκ hE hB hs0 hst ht1 hc hc0 hreg hHyp 6 (by norm_num)
  intro τ hτ D' hD'
  filter_upwards [hap (τ / 2) (half_pos hτ) D' hD', eventually_le_rpow 2 (half_pos hτ),
    eventually_ge_atTop 1] with N hN h2N _hN1
  refine (measure_mono ?_).trans hN
  rintro ω ⟨v, hv⟩
  by_contra hcon
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  -- the grid time and its window membership
  set u : ℝ := CutHypTheta.cutNetPt s mesh N v.1.1 with hudef
  have humem : u ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N) (hmesh N) u
      (CutHypTheta.cutNetPt_mem_netFinset v.1.2)
  have hu0 : 0 ≤ u := le_trans (hs0 N) humem.1
  have hu1 : u < 1 := lt_of_le_of_lt humem.2 (ht1 N)
  have hℓs : 0 < B.ell N (s N) :=
    lt_of_lt_of_le zero_lt_one (one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N)
      (lt_of_le_of_lt (hst N) (ht1 N)))
  have hK : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by linarith
  have hL : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖
      ≤ (N : ℝ) ^ (τ / 2) * (B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5 := by
    intro p
    have := hcon ((⟨u, humem⟩ : TimeIcc s t N), p)
    simpa [mul_assoc] using this
  have hmain := quadVar_le_mul_s3At X hE2 hu0 hu1 hℓs ω v.2.1 v.2.2 (D := D) hK hL
  have hpos : 0 ≤ s3At X E N u (B.ell N (s N)) D ω v.2.2 := by
    have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
    have hℓu : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    exact s3Rhs_nonneg hW1 (Nat.cast_nonneg _) (by linarith) (etaT_pos hE2 hu1)
      (by positivity) (one_le_jStar X E N u ω hW0)
  have habs : (2 : ℝ) * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
    have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hid := UnifDetDom.rpow_half_mul_rpow_half N hτ
    nlinarith
  have : qvGrid X E s t mesh N v ω ≤ (N : ℝ) ^ τ * s3Grid X E s t mesh D N v ω := by
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_right habs hpos
  exact absurd hv (not_lt.2 this)

/-! ### 6. The wrapper in the `∀ ε D″, ∃ N₀, ∀ N ≥ N₀` shape -/

/-- **`(S3)`, uniformly over the grid and over `b`, with an explicit `N₀`.**

Note the quantifier order: `ε` and `D″` are chosen **first**, and `N₀` after them — the
forbidden `∀ N, ∃ …` shape would be satisfiable by a constant.  The failure event is the
union over *all* grid points `j ≤ n_N` and *all* label pairs `b ∈ (ℤ_L)²` at one and the same
`N₀`, which is what the statement of `(S3)` asks for. -/
theorem prob_exists_grid_le (X : Sample B) {E : ℝ} {s t mesh : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (hHyp : Step1.Hyp X E s t) (hmesh : ∀ N, 0 < mesh N) (D : ℝ) :
    ∀ ε > (0 : ℝ), ∀ D'' > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      B.P {ω : Ω | ∃ j ≤ CutHypTheta.cutNetTop s t mesh N, ∃ σ : Fin (0 + 2) → Bool,
          ∃ a : LoopArg (B.L N) (0 + 2),
          (N : ℝ) ^ ε
              * s3At X E N (CutHypTheta.cutNetPt s mesh N j) (B.ell N (s N)) D ω a
            < quadVar B.toDims N
                (fun M' => MomentDuhamel.lkFun B E N
                  (CutHypTheta.cutNetPt s mesh N j) M' σ a)
                (X.H N (CutHypTheta.cutNetPt s mesh N j) ω)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'')) := by
  intro ε hε D'' hD''
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (stochDom_quadVar_grid X hκ hE hB hs0 hst ht1 hc hc0 hreg hHyp hmesh D ε hε D'' hD'')
  refine ⟨N₀, fun N hN => ?_⟩
  refine le_trans (le_of_eq ?_) (hN₀ N hN)
  congr 1
  ext ω
  constructor
  · rintro ⟨j, hj, σ, a, hlt⟩
    exact ⟨(⟨j, hj⟩, σ, a), hlt⟩
  · rintro ⟨⟨⟨j, hj⟩, σ, a⟩, hlt⟩
    exact ⟨j, hj, σ, a, hlt⟩

/-! ### 8. `μ = 2√Smax` written into `ζ` -/

/-- **The deterministic level of `Smax`**: `(ℓ_u/ℓ_s)^3 (W ℓ_u η_u)^{-3}`, i.e. the square of
the paper's `μ ≺ r_u^{3/2} A_u^{-3/2}`, which is what (2.73) delivers at `n = 4`
(`RBM.Step1.apriori` with `n = 4`, whose `ζ` is exactly this). -/
noncomputable def sDet (B : Band Ω) (E : ℝ) (N : ℕ) (u ℓs : ℝ) : ℝ :=
  (B.ell N u / ℓs) ^ 3 * (B.scale E N u)⁻¹ ^ 3

theorem sDet_nonneg (B : Band Ω) (E : ℝ) (N : ℕ) {u ℓs : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hℓs : 0 < ℓs) : 0 ≤ sDet B E N u ℓs := by
  have hℓu : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hA : 0 ≤ B.scale E N u := B.scale_nonneg E N hu1.le
  exact mul_nonneg (pow_nonneg (div_nonneg (by linarith) hℓs.le) 3)
    (pow_nonneg (inv_nonneg.2 hA) 3)

/-- **`√S ↦ s3Rhs` is affine with non-negative coefficients.**  `S` enters
`RBM.EarlyQVRateEv.s3Rhs` only through the far-field factor `μ = 2√S`, with a non-negative
coefficient, so inflating `√S` by `M ≥ 1` inflates the whole right-hand side by at most `M`
— exactly the absorption `RBM.EarlyQVRateEv.s3Rhs_mul_le` performs for the near coefficient
`κn`. -/
theorem s3Rhs_sqrt_le {W Lr ℓu ηu D κn J S S₀ d M : ℝ} (hW : 1 ≤ W) (hLr : 0 ≤ Lr)
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hJ : 1 ≤ J) (hκn : 0 ≤ κn) (hM : 1 ≤ M)
    (hS : √S ≤ M * √S₀) :
    s3Rhs W Lr ℓu ηu D κn J S d ≤ M * s3Rhs W Lr ℓu ηu D κn J S₀ d := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hA : (0 : ℝ) < W * ℓu * ηu := by positivity
  have hT : 0 < tailT W ℓu ηu D d := tailT_pos hW0 d
  have hT2 : (0 : ℝ) ≤ tailT W ℓu ηu D d ^ 2 := by positivity
  have hcN : 0 ≤ Lemma57.cNear2 W ℓu := Lemma57.cNear2_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar2 W ℓu := Lemma57.cFar2_nonneg hW hℓu
  have hind : (0 : ℝ) ≤ (if d ≤ 4 * ellStar W ℓu then 1 else 0) := by split <;> norm_num
  have hJ0 : (0 : ℝ) ≤ 2 * J := by linarith
  have hJ2 : (0 : ℝ) ≤ (2 * J) ^ 2 := by positivity
  have hJ3 : (0 : ℝ) ≤ (2 * J) ^ 3 := by positivity
  have hWD : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hηi : (0 : ℝ) ≤ ηu⁻¹ := inv_nonneg.2 hηu.le
  have hAi : (0 : ℝ) ≤ (W * ℓu * ηu)⁻¹ := inv_nonneg.2 hA.le
  have hρ : 0 ≤ rho0 W ℓu ηu κn := rho0_nonneg hW0.le hℓu.le hηu.le hκn
  -- the coefficient of `√S`, and the part of the right-hand side that does not involve `S`
  set C₁ : ℝ := 2 * (ηu⁻¹ * (Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * 2)))
      * tailT W ℓu ηu D d ^ 2) with hC₁
  set C₂ : ℝ := 2 * (ηu⁻¹ * (Lemma57.cNear2 W ℓu * κn * (if d ≤ 4 * ellStar W ℓu then 1 else 0)
      + 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D d ^ 2
      + (W * Lr * rho0 W ℓu ηu κn
        + 2 * W * Lr * W ^ (-D) * (2 * J) ^ 3 * tailT W ℓu ηu D d ^ 2)) with hC₂
  have hC₁0 : 0 ≤ C₁ := by
    have h1 : (0 : ℝ) ≤ Lemma57.cFar2 W ℓu * ((2 * J) ^ 2 * ((W * ℓu * ηu) * 2)) :=
      mul_nonneg hcF (mul_nonneg hJ2 (by linarith))
    have h2 := mul_nonneg (mul_nonneg hηi h1) hT2
    rw [hC₁]; linarith
  have hC₂0 : 0 ≤ C₂ := by
    have h1 : (0 : ℝ) ≤ Lemma57.cNear2 W ℓu * κn
        * (if d ≤ 4 * ellStar W ℓu then 1 else 0) := mul_nonneg (mul_nonneg hcN hκn) hind
    have h2 : (0 : ℝ) ≤ 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹ :=
      mul_nonneg (by linarith) hAi
    have h3 := mul_nonneg (mul_nonneg hηi (by linarith : (0 : ℝ) ≤
      Lemma57.cNear2 W ℓu * κn * (if d ≤ 4 * ellStar W ℓu then 1 else 0)
        + 72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹)) hT2
    have h4 : (0 : ℝ) ≤ W * Lr * rho0 W ℓu ηu κn := mul_nonneg (mul_nonneg hW0.le hLr) hρ
    have h5 : (0 : ℝ) ≤ 2 * W * Lr * W ^ (-D) * (2 * J) ^ 3 * tailT W ℓu ηu D d ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hLr) hWD) hJ3) hT2
    rw [hC₂]; linarith
  have he₁ : s3Rhs W Lr ℓu ηu D κn J S d = C₁ * √S + C₂ := by
    rw [s3Rhs, hC₁, hC₂]; ring
  have he₂ : s3Rhs W Lr ℓu ηu D κn J S₀ d = C₁ * √S₀ + C₂ := by
    rw [s3Rhs, hC₁, hC₂]; ring
  rw [he₁, he₂]
  nlinarith [mul_le_mul_of_nonneg_left hS hC₁0, mul_nonneg (sub_nonneg.2 hM) hC₂0]

/-- The right-hand side of `(S3)` at a single time `u` with the `Smax` slot replaced by its
(2.73) level at `n = 4`: the `ζ` no longer contains `√Smax`.  The remaining `ω`-dependence is
`J*_{u,D}`, which the paper's own (5.36) carries as well. -/
noncomputable def s3AtDet (X : Sample B) (E : ℝ) (N : ℕ) (u ℓs D : ℝ) (ω : Ω)
    (a : LoopArg (B.L N) (0 + 2)) : ℝ :=
  s3Rhs (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D ((B.ell N u / ℓs) ^ 5)
    (jStar X E N u ω (B.ell N u) (etaT E u) D) (sDet B E N u ℓs)
    (zdist (B.L N) (a 0 - a 1))

/-- **`μ = 2√Smax` replaced by its (2.73) level**, at the cost of a factor `√K'`.  A uniform
bound `K' · (ℓ_u/ℓ_s)^3 (Wℓ_uη_u)^{-3}` on the `4`-loops at the time `u` — what
`RBM.Step1.apriori` delivers at `n = 4`, with `K' = N^τ` — bounds `Smax`
(`RBM.EarlyQVRateEv.sMax_le`), hence `√Smax ≤ √K' √(sDet)`, and the right-hand side is affine
in `√S` with non-negative coefficients. -/
theorem s3At_le_mul_s3AtDet (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u ℓs : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hℓs : 0 < ℓs) (ω : Ω) (a : LoopArg (B.L N) (0 + 2))
    {D K' : ℝ} (hK' : 1 ≤ K')
    (hL4 : ∀ p : LoopData (B.L N) 4, ‖X.Lval E N u ω p.idx‖ ≤ K' * sDet B E N u ℓs) :
    s3At X E N u ℓs D ω a ≤ √K' * s3AtDet X E N u ℓs D ω a := by
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓu : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hηu : 0 < etaT E u := etaT_pos hE hu1
  have hsm : sMax X E N u ω ≤ K' * sDet B E N u ℓs := sMax_le X E N u ω hL4
  have hsqrt : √(sMax X E N u ω) ≤ √K' * √(sDet B E N u ℓs) := by
    rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ K')]
    exact Real.sqrt_le_sqrt hsm
  exact s3Rhs_sqrt_le hW1 (Nat.cast_nonneg _) (by linarith) hηu
    (one_le_jStar X E N u ω hW0) (pow_nonneg (div_nonneg (by linarith) hℓs.le) 5)
    (Real.one_le_sqrt.2 hK') hsqrt

/-- **`(S3)` at one time, with `μ` already at its (2.73) level.**  The two levels are the
`n = 6` one of `RBM.EarlyQVRateEv.quadVar_le_mul_s3At` (the near coefficient) and the `n = 4`
one (the far-field `μ`); the total loss is `2 K √K'`, which `≺` absorbs. -/
theorem quadVar_le_mul_s3AtDet (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u ℓs : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hℓs : 0 < ℓs) (ω : Ω) (σ : Fin (0 + 2) → Bool)
    (a : LoopArg (B.L N) (0 + 2)) {D K K' : ℝ} (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (hL : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖
      ≤ K * (B.ell N u / ℓs) ^ 5 * (B.scale E N u)⁻¹ ^ 5)
    (hL4 : ∀ p : LoopData (B.L N) 4, ‖X.Lval E N u ω p.idx‖ ≤ K' * sDet B E N u ℓs) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ (2 * K * √K') * s3AtDet X E N u ℓs D ω a := by
  have h1 := quadVar_le_mul_s3At X hE hu0 hu1 hℓs ω σ a (D := D) hK hL
  have h2 := s3At_le_mul_s3AtDet X hE hu0 hu1 hℓs ω a (D := D) hK' hL4
  have hK0 : (0 : ℝ) ≤ 2 * K := by linarith
  refine h1.trans ?_
  refine (mul_le_mul_of_nonneg_left h2 hK0).trans (le_of_eq ?_)
  ring

/-- The right-hand side of `(S3)` at the grid time `u_j`, with `μ` at its (2.73) level. -/
noncomputable def s3GridDet (X : Sample B) (E : ℝ) (s t mesh : ℕ → ℝ) (D : ℝ) :
    ∀ N, GridIdx B s t mesh N → Ω → ℝ :=
  fun N v ω =>
    s3AtDet X E N (CutHypTheta.cutNetPt s mesh N v.1.1) (B.ell N (s N)) D ω v.2.2

/-- **The deliverable of `T267a`**: the same `≺` as `RBM.EarlyQVRateEv.stochDom_quadVar_grid`,
with `μ = 2√Smax` replaced in the `ζ` by its (2.73) level `(ℓ_u/ℓ_s)^3(Wℓ_uη_u)^{-3}`.

`ζ` does **not** depend on `τ`: both a-priori levels are taken at `τ/4`, and the total loss
`2 N^{τ/4} √(N^{τ/4}) ≤ 2 N^{τ/2} ≤ N^τ` is absorbed into the `N^τ` of `RBM.StochDom`, which
is where the `τ` of a `≺` is allowed to live.  The union of the two failure events (one at
`n = 6`, one at `n = 4`) is `RBM.StochDom.of_subset_union`. -/
theorem stochDom_quadVar_grid_det (X : Sample B) {E : ℝ} {s t mesh : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (hHyp : Step1.Hyp X E s t) (hmesh : ∀ N, 0 < mesh N) (D : ℝ) :
    StochDom B.P (qvGrid X E s t mesh) (s3GridDet X E s t mesh D) := by
  have hE2 : |E| < 2 := by
    have := abs_nonneg E; linarith
  have hap6 := Step1.apriori X hκ hE hB hs0 hst ht1 hc hc0 hreg hHyp 6 (by norm_num)
  have hap4 := Step1.apriori X hκ hE hB hs0 hst ht1 hc hc0 hreg hHyp 4 (by norm_num)
  refine StochDom.of_subset_union hap6 hap4 (fun τ hτ => ⟨τ / 4, by linarith, ?_⟩)
  filter_upwards [eventually_le_rpow 2 (half_pos hτ), eventually_ge_atTop 1] with N h2N hN1
  rintro ω ⟨v, hv⟩
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨h6, h4⟩ := hcon
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at h6 h4
  set u : ℝ := CutHypTheta.cutNetPt s mesh N v.1.1 with hudef
  have humem : u ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N) (hmesh N) u
      (CutHypTheta.cutNetPt_mem_netFinset v.1.2)
  have hu0 : 0 ≤ u := le_trans (hs0 N) humem.1
  have hu1 : u < 1 := lt_of_le_of_lt humem.2 (ht1 N)
  have hℓs : 0 < B.ell N (s N) :=
    lt_of_lt_of_le zero_lt_one (one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N)
      (lt_of_le_of_lt (hst N) (ht1 N)))
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hK : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := Real.one_le_rpow hNr1 (by linarith)
  have hL : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖
      ≤ (N : ℝ) ^ (τ / 4) * (B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5 := by
    intro p
    have := h6 ((⟨u, humem⟩ : TimeIcc s t N), p)
    simpa [mul_assoc] using this
  have hL4 : ∀ p : LoopData (B.L N) 4, ‖X.Lval E N u ω p.idx‖
      ≤ (N : ℝ) ^ (τ / 4) * sDet B E N u (B.ell N (s N)) := by
    intro p
    have := h4 ((⟨u, humem⟩ : TimeIcc s t N), p)
    simpa [sDet] using this
  have hmain := quadVar_le_mul_s3AtDet X hE2 hu0 hu1 hℓs ω v.2.1 v.2.2 (D := D) hK hK hL hL4
  have hpos : 0 ≤ s3AtDet X E N u (B.ell N (s N)) D ω v.2.2 := by
    have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
    have hℓu : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    exact s3Rhs_nonneg hW1 (Nat.cast_nonneg _) (by linarith) (etaT_pos hE2 hu1)
      (pow_nonneg (div_nonneg (by linarith) hℓs.le) 5) (one_le_jStar X E N u ω hW0)
  have hsplit : (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 4) = (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' (Nat.cast_nonneg N) (by linarith : (0 : ℝ) < τ / 4 + τ / 4).ne']
    congr 1
    ring
  have habs : 2 * (N : ℝ) ^ (τ / 4) * √((N : ℝ) ^ (τ / 4)) ≤ (N : ℝ) ^ τ := by
    have hsq : √((N : ℝ) ^ (τ / 4)) ≤ (N : ℝ) ^ (τ / 4) :=
      Real.sqrt_le_self_iff.2 (Or.inr hK)
    have h1 : 2 * (N : ℝ) ^ (τ / 4) * √((N : ℝ) ^ (τ / 4))
        ≤ 2 * (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 4) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 2 * (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 4) = 2 * (N : ℝ) ^ (τ / 2) := by
      rw [mul_assoc, hsplit]
    have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hid := UnifDetDom.rpow_half_mul_rpow_half N hτ
    nlinarith
  have : qvGrid X E s t mesh N v ω ≤ (N : ℝ) ^ τ * s3GridDet X E s t mesh D N v ω := by
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_right habs hpos
  exact absurd hv (not_lt.2 this)

/-! ### 7. Satisfiability, on a non-degenerate grid -/

section Witness

/-- The paper's right end of the flow, `t_N = 1 - N^{-1/2}` (p. 24). -/
noncomputable def satT (N : ℕ) : ℝ := 1 - (N : ℝ) ^ (-(1 : ℝ) / 2)

theorem satT_nonneg (N : ℕ) : 0 ≤ satT N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    rw [satT, Nat.cast_zero, Real.zero_rpow (by norm_num)]
    norm_num
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h0
    have := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : -(1 : ℝ) / 2 ≤ 0)
    rw [satT]; linarith

theorem satT_window : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - satT N := by
  refine Eventually.of_forall fun N => ?_
  rw [satT, show (-1 + (1 : ℝ) / 2) = -(1 : ℝ) / 2 by norm_num]
  linarith

theorem satT_pos : ∀ᶠ N : ℕ in atTop, 0 < satT N := by
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by norm_num : -(1 : ℝ) / 2 < 0)
  rw [satT]; linarith

/-- **The hypotheses of `stochDom_quadVar_grid` are jointly satisfiable, non-degenerately.**

The model is T202's `RBM.Gauss.Dims.exampleGrow` (`L ≍ N^{1/4}`, `W ≍ N^{3/4}`), the energy is
`E = 0` (`κ = 1`), and the window is the first cell `(u_0, u_1) = (0, min(1-W^{-τ'}, t_N))` of
the grid of p. 24 with `t_N = 1 - N^{-1/2}`, i.e. exactly the window of
`RBM.Gauss.step1Hyp_gauss_witness`.

Three non-degeneracy certificates come with it:
* the window does not collapse: `u_0 < u_1` eventually;
* the **grid does not collapse to a single point**: `1 ≤ n_N` eventually, so the union bound
  really runs over at least the two points `u_0`, `u_1` of the net;
* the mesh is positive at every `N`. -/
theorem sat_stochDom_quadVar_grid :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ mesh : ℕ → ℝ, (∀ N, 0 < mesh N) ∧
      StochDom (band Dims.exampleGrow).P
          (qvGrid (sample Dims.exampleGrow) 0
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0)
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1) mesh)
          (s3Grid (sample Dims.exampleGrow) 0
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0)
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1) mesh 60)
        ∧ (∀ᶠ N : ℕ in atTop,
            gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0
              < gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1)
        ∧ (∀ᶠ N : ℕ in atTop, 1 ≤ CutHypTheta.cutNetTop
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0)
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1) mesh N) := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain (band Dims.exampleGrow) (κ := 1) (τ := (1 : ℝ) / 2)
      one_pos (by norm_num)
  obtain ⟨-, hstep⟩ := hgrid 0 (by norm_num) satT satT_nonneg satT_window
  obtain ⟨hu0, huv, hv1, hcond⟩ := hstep 0
  set sS : ℕ → ℝ := fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0 with hsS
  set tT : ℕ → ℝ := fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1 with htT
  have htT0 : ∀ N, 0 ≤ tT N := fun N => le_trans (hu0 N) (huv N)
  have hmesh : ∀ N, 0 < (tT N)⁻¹ + 1 := by
    intro N
    have h : (0 : ℝ) ≤ (tT N)⁻¹ := inv_nonneg.2 (htT0 N)
    linarith
  refine ⟨τ', hτ'0, fun N => (tT N)⁻¹ + 1, hmesh, ?_, ?_, ?_⟩
  · have hB : BoundsCore (sample Dims.exampleGrow) 0 sS :=
      (BoundsCore_zero (sample Dims.exampleGrow) (by norm_num : |(0 : ℝ)| ≤ 2)).congr
        (sample Dims.exampleGrow)
        (Eventually.of_forall fun N => (gridT_zero (satT_nonneg N)).symm)
    exact stochDom_quadVar_grid (sample Dims.exampleGrow) one_pos (by norm_num) hB
      hu0 huv hv1 hcond.1 hc0 hcond.2
      (step1Hyp_gauss_of_scale'' Dims.exampleGrow one_pos (by norm_num) hB hu0 huv hv1
        hcond.1 hc0 hcond.2)
      hmesh 60
  · exact eventually_gridT_zero_lt_gridT_one (band Dims.exampleGrow) hτ'0 satT_pos
  · filter_upwards [eventually_gridT_zero_lt_gridT_one (band Dims.exampleGrow) hτ'0 satT_pos]
      with N hN
    have hs0N : sS N = 0 := gridT_zero (satT_nonneg N)
    have htpos : 0 < tT N := by rw [← hs0N]; exact hN
    have hkey : (1 : ℝ) ≤ (tT N - sS N) * ((tT N)⁻¹ + 1) := by
      rw [hs0N, sub_zero]
      have heq : tT N * ((tT N)⁻¹ + 1) = 1 + tT N := by field_simp
      rw [heq]; linarith
    exact Nat.le_floor (by exact_mod_cast hkey)

/-- **The hypotheses of `RBM.EarlyQVRateEv.stochDom_quadVar_grid_det` are jointly satisfiable,
non-degenerately.**  Same model, energy, window and grid as
`RBM.EarlyQVRateEv.sat_stochDom_quadVar_grid`, with the same two non-degeneracy certificates
(the window does not collapse, and the grid runs over at least two times); only the `ζ` is the
one whose `μ` slot has already been evaluated at the (2.73) level.  The `ζ` here is still
non-trivial: `sDet ≥ 0` and `jStar ≥ 1`, so no factor of the right-hand side is `0`. -/
theorem sat_stochDom_quadVar_grid_det :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ mesh : ℕ → ℝ, (∀ N, 0 < mesh N) ∧
      StochDom (band Dims.exampleGrow).P
          (qvGrid (sample Dims.exampleGrow) 0
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0)
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1) mesh)
          (s3GridDet (sample Dims.exampleGrow) 0
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0)
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1) mesh 60)
        ∧ (∀ᶠ N : ℕ in atTop,
            gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0
              < gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1)
        ∧ (∀ᶠ N : ℕ in atTop, 1 ≤ CutHypTheta.cutNetTop
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0)
            (fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1) mesh N) := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain (band Dims.exampleGrow) (κ := 1) (τ := (1 : ℝ) / 2)
      one_pos (by norm_num)
  obtain ⟨-, hstep⟩ := hgrid 0 (by norm_num) satT satT_nonneg satT_window
  obtain ⟨hu0, huv, hv1, hcond⟩ := hstep 0
  set sS : ℕ → ℝ := fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 0 with hsS
  set tT : ℕ → ℝ := fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (satT N) 1 with htT
  have htT0 : ∀ N, 0 ≤ tT N := fun N => le_trans (hu0 N) (huv N)
  have hmesh : ∀ N, 0 < (tT N)⁻¹ + 1 := by
    intro N
    have h : (0 : ℝ) ≤ (tT N)⁻¹ := inv_nonneg.2 (htT0 N)
    linarith
  refine ⟨τ', hτ'0, fun N => (tT N)⁻¹ + 1, hmesh, ?_, ?_, ?_⟩
  · have hB : BoundsCore (sample Dims.exampleGrow) 0 sS :=
      (BoundsCore_zero (sample Dims.exampleGrow) (by norm_num : |(0 : ℝ)| ≤ 2)).congr
        (sample Dims.exampleGrow)
        (Eventually.of_forall fun N => (gridT_zero (satT_nonneg N)).symm)
    exact stochDom_quadVar_grid_det (sample Dims.exampleGrow) one_pos (by norm_num) hB
      hu0 huv hv1 hcond.1 hc0 hcond.2
      (step1Hyp_gauss_of_scale'' Dims.exampleGrow one_pos (by norm_num) hB hu0 huv hv1
        hcond.1 hc0 hcond.2)
      hmesh 60
  · exact eventually_gridT_zero_lt_gridT_one (band Dims.exampleGrow) hτ'0 satT_pos
  · filter_upwards [eventually_gridT_zero_lt_gridT_one (band Dims.exampleGrow) hτ'0 satT_pos]
      with N hN
    have hs0N : sS N = 0 := gridT_zero (satT_nonneg N)
    have htpos : 0 < tT N := by rw [← hs0N]; exact hN
    have hkey : (1 : ℝ) ≤ (tT N - sS N) * ((tT N)⁻¹ + 1) := by
      rw [hs0N, sub_zero]
      have heq : tT N * ((tT N)⁻¹ + 1) = 1 + tT N := by field_simp
      rw [heq]; linarith
    exact Nat.le_floor (by exact_mod_cast hkey)

end Witness

/-! ### Deviations

**T267a** (deviation from the literal right-hand side of (5.36), inherited from
`RBM.EEDef.ee_le_EEpath_sym` and made explicit here).  The paper states (5.36) with the
far-field factor `μ ≺ r_u^{3/2} A_u^{-3/2}`, obtained from (2.73) at `n = 4`.  The Lean
right-hand side `RBM.EarlyQVRateEv.s3Rhs` keeps `μ = 2√Smax` with `Smax` the *defined*
maximum of the real parts of the `4`-loops (`RBM.EarlyQVRateEv.sMax`), and the step to the
paper's `μ` is the separate lemma `RBM.EarlyQVRateEv.sMax_le`, fed by
`RBM.Step1.apriori` at `n = 4`.  Two reasons: keeping `Smax` symbolic makes the
right-hand side `ω`-measurable without an event restriction, so the statement cannot become
vacuous; and it lets the consumer choose the level at which `μ` is evaluated.  Similarly the
factor `J*_{u,D}` of the far field is kept as the *definition* (5.28)
(`RBM.EarlyQVRateEv.jStar`), exactly as the paper's (5.36) does — it is bounded later, on the
support of the cut-off weight, by `J* ≤ c₀ N^{2δ} R^4`.

**T267b** (a loss of `N^τ`, absorbed by `≺`).  `RBM.EEDef.ee_le_EEpath_sym` asks for `h273`
in the exact shape `(ℓ_u/ℓ_s)^5 (Wℓ_uη_u)^{-5}`, while what (2.73) gives on the Step-1 event
is `N^τ` times that, and the `k`-sum of (5.22) at `n = 0` has two terms, for a further factor
`2`.  The near coefficient `(ℓ_u/ℓ_s)^5` is therefore carried as a free parameter `κn` of
`RBM.EarlyQVRateEv.s3Rhs`, which is affine in it with non-negative coefficients
(`s3Rhs_mul_le`), and the loss `2N^{τ/2}` is absorbed into the `N^τ` of `RBM.StochDom` — the
standard `≺` bookkeeping, no change to the paper's statement.

**T273a** (`T267a` discharged for the `μ` slot).  `RBM.EarlyQVRateEv.stochDom_quadVar_grid_det`
carries the paper's own `μ ≺ r_u^{3/2} A_u^{-3/2}` in its `ζ`: `Smax` is replaced there by
`RBM.EarlyQVRateEv.sDet = (ℓ_u/ℓ_s)^3 (W ℓ_u η_u)^{-3}`, which is literally the `ζ` of
`RBM.Step1.apriori` at `n = 4`, so `μ = 2√Smax ≤ 2√K' (ℓ_u/ℓ_s)^{3/2}(Wℓ_uη_u)^{-3/2}`.  The
step is an *affine absorption*: `RBM.EarlyQVRateEv.s3Rhs` is affine in `√S` with non-negative
coefficients (`RBM.EarlyQVRateEv.s3Rhs_sqrt_le`), exactly as it is affine in the near
coefficient `κn` (`s3Rhs_mul_le`), so the level `√K'` factors out of the whole right-hand
side.  Both a-priori levels are taken at `τ/4`, and the total loss
`2 N^{τ/4} √(N^{τ/4}) ≤ 2 N^{τ/2} ≤ N^τ` is absorbed into the `N^τ` of `RBM.StochDom`;
**`ζ` therefore does not depend on `τ`**, which is what `RBM.StochDom` requires.  The union of
the two failure events (`n = 6` for `κn`, `n = 4` for `μ`) is `RBM.StochDom.of_subset_union`.
The `J*_{u,D}` half of `T267a` is *not* discharged and should not be: the paper's (5.36)
carries `J*_{u,D}` on its right-hand side too.  No new named hypothesis: the hypothesis list of
`stochDom_quadVar_grid_det` is, verbatim, that of `stochDom_quadVar_grid`.

No other deviation: the far field is `RBM.Lemma57.ee_le`'s, i.e. (5.71)+(5.72) times the
factor `W` of (5.22), with `(J*)²` in place of the `(J*)³` of the *statement* (5.36) and with
**no** `W^{-1}` — see the module docstring of `RBM1D/Gauss/EarlyQVRate.lean` and its
deviation `T262a`. -/

end EarlyQVRateEv

end RBM

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2Near47

/-!
# A `u`-dependent truncation level for the truncated moment Duhamel (T210)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.29), (5.43), (5.47).

## The gap this file closes

`RBM.MomentDuhamelCut.CutHyp` (T197) carries a **constant** level `Θ : ℕ → ℝ`, used twice:
as the truncation level `N^{2δ}Θ_N` inside `moment`, and as the control `Θ_N` in the
conclusion.  T207 (`RBM.Step2Near47`) then showed that the sharp (5.47) needs only the
**blunt** prefix `J*_{u,D} ≤ N^{δ}(η_s/η_u)^4` — the level the first pass has already
established (`RBM.MomentDuhamelCut.jS_stochDom_cut`) — and that no second bootstrap is
required (`RBM.Step2Near47.phi_arith_second_pass`).  Read in the sharp normalization
`J₂ = J*/(η_s/η_u)²` of `RBM.Step2Near47.jSnorm2` that prefix level is

`N^{2δ} · (η_s/η_u)²`,

which **depends on `u`** and is therefore inexpressible against `CutHyp`.  T207 had to fall
back on `RBM.Step2Near47.MomentHypCutSharp`, which truncates `J₂` at the constant `N^{2δ}`
and re-runs the bootstrap from scratch.

This file separates the two roles of `Θ`:

* `lev : ℕ → ℝ → ℝ` — the **truncation level**, allowed to depend on `u`;
* `Θ : ℕ → ℝ` — the **control**, still constant in `u` (that is what `RBM.StochDom` against a
  `u`-independent bound means).

## Main definitions

* `RBM.CutHypTheta.CutHyp'` — `RBM.MomentDuhamelCut.CutHyp` with the truncation level
  `lev N u` in place of `Θ N`.  The field `lev_ge` asks `Θ_N ≤ lev_N(u)` **on the window
  only**: for the intended `lev N u = (η_s/η_u)²` the inequality is false off `[s_N, t_N]`
  (at `u > 1` the ratio is negative and its square is small), which is exactly the kind of
  literal-falsity this project keeps hitting, so the quantifier is restricted.
* `RBM.CutHypTheta.MomentHypCut2` — the **second-pass** interface for `jSnorm2`: a `CutHyp'`
  at the blunt level `(η_s/η_u)²` and control `1`.  It has **no `init` field**: the second
  pass consumes the first pass's conclusion instead of the initial condition.

## Main results

* `cutTrunc_mono_level`, `cutTrunc_level_smul` — `cutTrunc` is monotone in the level and
  homogeneous of degree one in `(level, argument)` jointly.  The second is why the two
  normalizations are interchangeable at matching levels: the *supports* of
  `χ(J₂/(N^{2δ}R²))` and of `χ(J₄/N^{2δ})` are literally the same set.
* `cutHyp'_of_cutHyp`, `cutHyp_of_cutHyp'`, `CutHyp'.mono_lev` — **the two-way relation,
  compiled**.  `CutHyp` is `CutHyp'` at the constant level, and a `CutHyp'` at a level
  above the control implies the `CutHyp` at that control.  The implication only goes that
  way: raising the level makes `cutTrunc` larger, hence the moment field *stronger*
  (`sat_level_strict` exhibits the strictness).
* `netTrunc_highProb` — the Markov-plus-union-bound core of `RBM.MomentDuhamelCut.hev_of_cutHyp`,
  with the prefix condition stripped out: `moment` alone controls the **truncated** functional
  at every net point with high probability.
* `stochDom_of_cutHyp'` — the bootstrap route, verbatim the conclusion of
  `RBM.MomentDuhamelCut.stochDom_of_cutHyp` but from the weaker `CutHyp'` data.
* `stochDom_of_cutHyp'_of_prefix` — **the second pass, with no bootstrap and no initial
  condition**.  Given the prefix as an external high-probability event — which is what the
  first pass delivers — the conclusion `J ≺ Θ` follows from `netTrunc_highProb` and the
  modulus alone.  This is `RBM.Step2Near47.phi_arith_second_pass`'s "no second bootstrap is
  needed" turned into a theorem about the interface.
* `prefix_of_stochDom` — the bridge that turns the first pass's `RBM.StochDom` into that
  external prefix event.
* `moment_of_conditional` — **the reduction the producer of `CutHyp.moment` needs** (step 0 of
  the ticket): the unconditional moment field follows from (i) the moment bound *restricted to
  the prefix event*, which is what a Duhamel computation can produce, and (ii) the prefix
  event holding with high probability.  Off the prefix event the truncation's own envelope
  `2·level` is what pays, and `HighProb`'s arbitrary `D` beats it at every order.
* `momentHypCutSharp_of_cut2` — `RBM.Step2Near47.MomentHypCutSharp`, T207's §3 hypothesis, is
  **no longer independent**: it follows from `MomentHypCut2` together with T197's
  `RBM.MomentDuhamelCut.MomentHypCut`.
* `jS_stochDom_sharp_of_cut2`, `jS_stochDom_sharp_of_cut2_of_momentHypCut` — (5.47) sharp,
  `J*_{u,D} ≺ (η_s/η_u)²`, from `MomentHypCut2` and the blunt first pass, with no second
  bootstrap and no second initial condition.

## Satisfiability (compiled, §7)

* `satCutHyp'` — a complete compiled `CutHyp'` at the **critical scale** `J ≡ Θ ≡ 1`, with a
  level `lev N u = (1-u)⁻¹` that is genuinely `u`-dependent and **unbounded as `u ↑ 1`**
  (`sat_lev_unbounded`), on a window `[0, 1 - (N+2)⁻¹]` whose right endpoint tends to `1`.
  So the generalization is not satisfied only by degenerate, constant levels.  As in
  `RBM.MomentDuhamelCut.satCutHyp` the mesh is taken at the flow's own scaling
  (`γ = 1/2`, `m_N ≍ N²`), where `mesh_fine` and `card_le` — the pair pulling in opposite
  directions — are met by the same witness.
* `sat_levSharp_ge` — the field `lev_ge` for the **intended** level `(η_s/η_u)²` is a theorem
  on the window (`RBM.Step2Moment.one_le_ratR`), so `MomentHypCut2` does not ask for
  something false.
* `sat_stochDom_of_cutHyp'`, `sat_prefix_of_cutHyp'` — the witness feeds both routes (the
  bootstrap one and the prefix one) and a `RBM.StochDom` comes out of each.
* `sat_level_strict` — raising the level really does raise `cutTrunc`, so `mono_lev` is not
  an equality in disguise.

## What is **not** here

The Gaussian discharge of the moment field itself.  `moment_of_conditional` reduces it to a
*conditional* moment bound on the prefix event; producing that is the truncated Duhamel
computation, which needs `RBM.MomentDuhamel.Hyp`'s three inputs (T212/T213/T214).  Nothing
here is an `axiom` and nothing is `sorry`.

## Deviations from the paper

* `T210a`.  (5.43) truncates with a stopping time, so the truncation level along the path is
  the *running* threshold `Λ(u) = N^δ(η_s/η_u)^4`, a function of `u`.  `CutHyp` flattened it
  to a constant by normalizing (`RBM.Step2Moment.jSnorm`); `CutHyp'` restores the
  `u`-dependence, which is what lets the *blunt* level be used while the *conclusion* is read
  in the sharp normalization.  This is closer to the paper than `CutHyp` is, not further.
  No renumbering.
-/

namespace RBM

namespace CutHypTheta

open MeasureTheory Filter Real MomentDuhamelCut

/-! ### 1. `cutTrunc` as a function of its level -/

section Level

/-- **`cutTrunc` is monotone in the truncation level.**  Raising the level enlarges the
support of the cutoff, so the truncated functional grows; consequently a moment bound at a
*higher* level is a *stronger* hypothesis.  This is the whole content of the direction
`CutHyp' → CutHyp` (`cutHyp_of_cutHyp'`). -/
theorem cutTrunc_mono_level {θ₁ θ₂ x : ℝ} (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) (hx : 0 ≤ x) :
    cutTrunc θ₁ x ≤ cutTrunc θ₂ x := by
  have hθ₂ : (0 : ℝ) < θ₂ := lt_of_lt_of_le hθ₁ hθ
  have hdiv : x / θ₂ ≤ x / θ₁ := by
    rw [div_le_div_iff₀ hθ₂ hθ₁]
    nlinarith
  exact mul_le_mul_of_nonneg_right (Cutoff.cutChi_antitone hdiv) hx

/-- **`cutTrunc` is jointly homogeneous**: `cutTrunc (c θ) (c x) = c · cutTrunc θ x`.

This is why the two normalizations of §5.3 are the *same* truncation.  With
`c = (η_s/η_u)²`, `x = J*/(η_s/η_u)^4` and `θ = N^{2δ}` it says

`cutTrunc (N^{2δ}(η_s/η_u)²) (jSnorm2) = (η_s/η_u)² · cutTrunc (N^{2δ}) (jSnorm)`,

i.e. truncating the sharply normalized `J*` at the blunt level is the blunt truncation,
rescaled — the supports coincide exactly. -/
theorem cutTrunc_level_smul {c θ x : ℝ} (hc : c ≠ 0) :
    cutTrunc (c * θ) (c * x) = c * cutTrunc θ x := by
  unfold cutTrunc
  rw [mul_div_mul_left _ _ hc]
  ring

end Level

/-! ### 2. The interface with a `u`-dependent truncation level -/

section Interface

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The truncated moment Duhamel interface with a `u`-dependent truncation level.**

Field for field this is `RBM.MomentDuhamelCut.CutHyp`, with one change: the truncation level
inside `moment` is `N^{2δ} · lev N ws` instead of `N^{2δ} · Θ N`.  The control of the
conclusion is still the constant `Θ N`, because that is what `RBM.StochDom` against a
`u`-independent bound means.

**`lev_ge` is restricted to the window.**  The intended level is `lev N u = (η_s/η_u)²`,
which is `≥ 1` only for `s_N ≤ u < 1`; at `u > 1` the ratio `η_s/η_u` is negative and its
square is *small*, so `∀ N u, Θ N ≤ lev N u` would be **false** for the object this
interface exists to carry.  `sat_levSharp_ge` checks the restricted form on the window. -/
structure CutHyp' (P : Measure Ω) (J : ℕ → ℝ → Ω → ℝ) (s t : ℕ → ℝ) (lev : ℕ → ℝ → ℝ)
    (Θ : ℕ → ℝ) where
  /-- The window is non-degenerate. -/
  window : ∀ N, s N ≤ t N
  /-- The range `0 < δ ≤ δ₀` of bootstrap margins. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  Θ_pos : ∀ N, 0 < Θ N
  /-- **The truncation level dominates the control, on the window.** -/
  lev_ge : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u
  /-- The state functional is nonnegative. -/
  J_nonneg : ∀ N u ω, 0 ≤ J N u ω
  meas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => J N u ω) P
  /-- The mesh of the net of (5.46). -/
  mesh : ℕ → ℝ
  mesh_pos : ∀ N, 0 < mesh N
  /-- The exponent of the deterministic modulus of continuity. -/
  Kmod : ℝ
  /-- Its Hölder exponent. -/
  γ : ℝ
  γ_pos : 0 < γ
  /-- The deterministic modulus of continuity, valid for **every** `ω`. -/
  modulus : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    |J N v ω - J N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ
  /-- The net is fine enough that one mesh of displacement costs at most `Θ_N`. -/
  mesh_fine : ∀ N : ℕ, (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ N
  /-- The exponent of the net's cardinality. -/
  Ccard : ℝ
  /-- The net is polynomially large, so the union bound is a `≺`-loss. -/
  card_le : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard
  /-- **The truncated one-step moment bound at the net points**, at the `u`-dependent
  truncation level `N^{2δ} lev_N(ws)`.  Quantifier order is that of
  `RBM.Gauss.MomentDom`: `δ`, then `ε`, then the order `p`, then `N → ∞`. -/
  moment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ netFinset s t mesh N,
      ∫ ω, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p))

namespace CutHyp'

variable {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- The truncation level is positive on the window. -/
theorem lev_pos (H : CutHyp' P J s t lev Θ) (N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    0 < lev N u :=
  lt_of_lt_of_le (H.Θ_pos N) (H.lev_ge N u hu)

/-- The truncation level is positive at every net point. -/
theorem lev_pos_net (H : CutHyp' P J s t lev Θ) (N : ℕ) {ws : ℝ}
    (hws : ws ∈ netFinset s t H.mesh N) : 0 < lev N ws :=
  H.lev_pos N (netFinset_subset_Icc (H.window N) (H.mesh_pos N) ws hws)

/-- The paths are continuous, by the modulus — so no separate `cont` field. -/
theorem continuousOn (H : CutHyp' P J s t lev Θ) (N : ℕ) (ω : Ω) :
    ContinuousOn (fun u => J N u ω) (Set.Icc (s N) (t N)) :=
  continuousOn_of_modulus H.γ_pos (H.modulus N ω)

/-- **`hclose`**: every time of the window has a net point to its left at which the functional
is smaller by at most `Θ_N`.  Verbatim `RBM.MomentDuhamelCut.CutHyp.hclose`; the level plays
no part in it. -/
theorem hclose (H : CutHyp' P J s t lev Θ) (N : ℕ) (ω : Ω) :
    ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      ws ∈ Set.Icc (s N) v ∧ J N v ω ≤ J N ws ω + Θ N := by
  intro v hv
  obtain ⟨ws, hwsF, hwsIcc, hgap⟩ := exists_mem_netFinset (t := t) (H.mesh_pos N) hv
  refine ⟨ws, Finset.mem_coe.2 hwsF, hwsIcc, ?_⟩
  have hwsb : ws ∈ Set.Icc (s N) (t N) := ⟨hwsIcc.1, hwsIcc.2.trans hv.2⟩
  have habs : |v - ws| ≤ 1 / H.mesh N := by
    rw [abs_of_nonneg (by linarith [hwsIcc.2])]
    exact hgap
  have h1 : |v - ws| ^ H.γ ≤ (1 / H.mesh N) ^ H.γ :=
    Real.rpow_le_rpow (abs_nonneg _) habs H.γ_pos.le
  have hK : (0 : ℝ) ≤ (N : ℝ) ^ H.Kmod := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (N : ℝ) ^ H.Kmod * |v - ws| ^ H.γ ≤ Θ N :=
    le_trans (mul_le_mul_of_nonneg_left h1 hK) (H.mesh_fine N)
  have h3 := (le_abs_self _).trans ((H.modulus N ω v hv ws hwsb).trans h2)
  linarith

end CutHyp'

end Interface

/-! ### 3. The two-way relation with `RBM.MomentDuhamelCut.CutHyp` -/

section Compare

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev lev' : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **`CutHyp` is `CutHyp'` at the constant level.**  One half of the two-way relation:
nothing is lost by moving to the generalized interface. -/
def cutHyp'_of_cutHyp (H : CutHyp P J s t Θ) : CutHyp' P J s t (fun N _ => Θ N) Θ where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  lev_ge := fun _ _ _ => le_rfl
  J_nonneg := H.J_nonneg
  meas := H.meas
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := H.modulus
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  moment := H.moment

/-- **Lowering the truncation level weakens the hypothesis.**  If `lev ≤ lev'` on the window
then a `CutHyp'` at `lev'` is a `CutHyp'` at `lev`: by `cutTrunc_mono_level` the integrand
only shrinks.

The integrability needed for `integral_mono` is free — `cutTrunc` has the deterministic
envelope `2·level` (`RBM.MomentDuhamelCut.integrable_cutTrunc_pow`). -/
def CutHyp'.mono_lev [IsFiniteMeasure P] (H : CutHyp' P J s t lev' Θ)
    (hlev0 : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u)
    (hlev : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), lev N u ≤ lev' N u) :
    CutHyp' P J s t lev Θ where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  lev_ge := hlev0
  J_nonneg := H.J_nonneg
  meas := H.meas
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := H.modulus
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  moment := by
    intro δ hδ0 hδ ε hε p
    obtain ⟨C, hC0, hCN⟩ := H.moment δ hδ0 hδ ε hε p
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hCN, eventually_ge_atTop 1] with N hN hN1 ws hws
    have hwsIcc : ws ∈ Set.Icc (s N) (t N) :=
      netFinset_subset_Icc (H.window N) (H.mesh_pos N) ws hws
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hN0 _
    have hl0 : 0 < lev N ws := lt_of_lt_of_le (H.Θ_pos N) (hlev0 N ws hwsIcc)
    have hl'0 : 0 < lev' N ws := lt_of_lt_of_le (H.Θ_pos N) (H.lev_ge N ws hwsIcc)
    have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N ws := by positivity
    have hθ'0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev' N ws := by positivity
    refine le_trans (integral_mono ?_ ?_ ?_) (hN ws hws)
    · exact integrable_cutTrunc_pow hθ0 (fun ω => H.J_nonneg N ws ω) (H.meas N ws) (2 * p)
    · exact integrable_cutTrunc_pow hθ'0 (fun ω => H.J_nonneg N ws ω) (H.meas N ws) (2 * p)
    · intro ω
      dsimp only
      have hmono : cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)
          ≤ cutTrunc ((N : ℝ) ^ (2 * δ) * lev' N ws) (J N ws ω) :=
        cutTrunc_mono_level hθ0
          (by have := hlev N ws hwsIcc; nlinarith) (H.J_nonneg N ws ω)
      have h1 : (0 : ℝ) ≤ cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) :=
        cutTrunc_nonneg (H.J_nonneg N ws ω)
      have h2 : (0 : ℝ) ≤ cutTrunc ((N : ℝ) ^ (2 * δ) * lev' N ws) (J N ws ω) :=
        cutTrunc_nonneg (H.J_nonneg N ws ω)
      rw [abs_of_nonneg h1, abs_of_nonneg h2]
      exact pow_le_pow_left₀ h1 hmono _

/-- **The other half: a `CutHyp'` above the control is a `CutHyp`.**

Together with `cutHyp'_of_cutHyp` this is the two-way relation the ticket asks for, and it is
one-directional on purpose: `CutHyp'` at a level `> Θ` is *strictly stronger* than `CutHyp`
(`sat_level_strict`), because `cutTrunc` grows with the level.  What is bought for that price
is `stochDom_of_cutHyp'_of_prefix`, which needs **no bootstrap and no initial condition**. -/
def cutHyp_of_cutHyp' [IsFiniteMeasure P] (H : CutHyp' P J s t lev Θ) : CutHyp P J s t Θ where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  J_nonneg := H.J_nonneg
  meas := H.meas
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := H.modulus
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  moment := (H.mono_lev (lev := fun N _ => Θ N) (fun _ _ _ => le_rfl)
    (fun N u hu => H.lev_ge N u hu)).moment

end Compare

/-! ### 4. The net bound, and the two routes to `≺` -/

section Hev

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **The Markov-plus-union-bound core, with the prefix condition stripped out.**

`RBM.MomentDuhamelCut.hev_of_cutHyp` bundles two independent steps: a moment estimate for the
*truncated* functional at the net points, and the de-truncation on the prefix event.  Only the
first uses `moment`, and it is unconditional.  Isolating it is what makes the second pass
possible: there the de-truncation is done against an **externally supplied** prefix event
(`stochDom_of_cutHyp'_of_prefix`) rather than against one manufactured by continuous
induction.

The order `p` is chosen so that `δp/2` beats the net's cardinality exponent `Ccard`, the
target decay `D`, and the constant `C`; the union bound over `N^{Ccard}` net points is the
only cost. -/
theorem netTrunc_highProb [IsProbabilityMeasure P] (H : CutHyp' P J s t lev Θ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ H.δ₀) :
    HighProb P fun N => {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
  intro D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + H.Ccard + 1) * 2 / δ)
  have hpδ : D + H.Ccard + 1 ≤ δ / 2 * p := by
    rw [div_le_iff₀ hδ0] at hp
    nlinarith
  have hexp : 0 < δ / 2 * (p : ℝ) - H.Ccard - D := by linarith
  obtain ⟨C, hC0, hCN⟩ := H.moment δ hδ0 hδ (δ / 2) (by positivity) p
  filter_upwards [hCN, H.card_le, eventually_ge_atTop 2, eventually_le_rpow C hexp,
    eventually_le_rpow (2 : ℝ) (half_pos hδ0)] with N hmomN hcardN hN2 hCle hhalf
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hΘ0 := H.Θ_pos N
  set a : ℝ := (N : ℝ) ^ (δ / 2) with ha_def
  have haa : (N : ℝ) ^ δ = a * a := by
    rw [ha_def, ← Real.rpow_add hN0]; congr 1; ring
  have hda : a ≤ (N : ℝ) ^ δ - 1 := by rw [haa]; nlinarith
  have hlv0 : (0 : ℝ) < ((N : ℝ) ^ δ - 1) * Θ N := by
    have : (0 : ℝ) < (N : ℝ) ^ δ - 1 := by linarith
    positivity
  -- Markov at a single net point, at that point's own truncation level
  have hpoint : ∀ ws ∈ netFinset s t H.mesh N,
      P {ω | ((N : ℝ) ^ δ - 1) * Θ N <
          cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard) := by
    intro ws hws
    have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hN0 _
    have hlpos := H.lev_pos_net N hws
    have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N ws := by positivity
    have hint := integrable_cutTrunc_pow (P := P) hθ0 (fun ω => H.J_nonneg N ws ω)
      (H.meas N ws) (2 * p)
    refine (Gauss.meas_gt_le_of_moment P hlv0 hint (hmomN ws hws)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hQ : (0 : ℝ) < Θ N ^ (2 * p) := by positivity
    have hR : (N : ℝ) ^ (δ * (p : ℝ)) ≤ ((N : ℝ) ^ δ - 1) ^ (2 * p) := by
      have h2 : a ^ (2 * p) = (N : ℝ) ^ (δ * (p : ℝ)) := by
        rw [ha_def, ← Real.rpow_natCast ((N : ℝ) ^ (δ / 2)) (2 * p), ← Real.rpow_mul hN0.le]
        congr 1; push_cast; ring
      rw [← h2]
      exact pow_le_pow_left₀ (by positivity) hda (2 * p)
    have hkey : C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) ≤ (N : ℝ) ^ (δ * (p : ℝ) - D - H.Ccard) := by
      calc C * (N : ℝ) ^ (δ / 2 * (p : ℝ))
          ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ) - H.Ccard - D) * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
            gcongr
        _ = (N : ℝ) ^ (δ * (p : ℝ) - D - H.Ccard) := by
            rw [← Real.rpow_add hN0]; congr 1; ring
    rw [div_le_iff₀ (by positivity)]
    have hexpand : (((N : ℝ) ^ δ - 1) * Θ N) ^ (2 * p)
        = ((N : ℝ) ^ δ - 1) ^ (2 * p) * Θ N ^ (2 * p) := mul_pow _ _ _
    have hsplit : (N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard = (N : ℝ) ^ (-D - H.Ccard) := by
      rw [Real.rpow_sub hN0]
    rw [hexpand, hsplit]
    calc C * ((N : ℝ) ^ (δ / 2 * (p : ℝ)) * Θ N ^ (2 * p))
        = (C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) * Θ N ^ (2 * p) := by ring
      _ ≤ (N : ℝ) ^ (δ * (p : ℝ) - D - H.Ccard) * Θ N ^ (2 * p) :=
          mul_le_mul_of_nonneg_right hkey hQ.le
      _ = (N : ℝ) ^ (-D - H.Ccard) * (N : ℝ) ^ (δ * (p : ℝ)) * Θ N ^ (2 * p) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
      _ ≤ (N : ℝ) ^ (-D - H.Ccard) * ((N : ℝ) ^ δ - 1) ^ (2 * p) * Θ N ^ (2 * p) := by
          gcongr
      _ = (N : ℝ) ^ (-D - H.Ccard) * (((N : ℝ) ^ δ - 1) ^ (2 * p) * Θ N ^ (2 * p)) := by ring
  -- the failure event sits inside the union of the Markov events
  have hsub : ({ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
        cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) ≤ ((N : ℝ) ^ δ - 1) * Θ N})ᶜ
      ⊆ ⋃ ws ∈ netFinset s t H.mesh N,
          {ω | ((N : ℝ) ^ δ - 1) * Θ N <
            cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_coe, not_forall, not_le] at hω
    obtain ⟨ws, hwsF, hgt⟩ := hω
    exact Set.mem_biUnion hwsF hgt
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hpoint) ?_
  have hr0 : (0 : ℝ) ≤ (N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard := by positivity
  have hcard : ((netFinset s t H.mesh N).card : ℝ) ≤ (N : ℝ) ^ H.Ccard :=
    (netFinset_card_le (H.window N) (H.mesh_pos N)).trans hcardN
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((netFinset s t H.mesh N).card : ℝ) * ((N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard)
      ≤ (N : ℝ) ^ H.Ccard * ((N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard) :=
        mul_le_mul_of_nonneg_right hcard hr0
    _ = (N : ℝ) ^ (-D) := by field_simp

/-- **De-truncation against the `u`-dependent prefix.**  On the event where the a priori
bound holds at the `u`-dependent level `N^{2δ} lev_N(u)` throughout the prefix, the truncated
bound of `netTrunc_highProb` is a bound on the functional itself — the truncation level is
exactly the prefix level, so `RBM.MomentDuhamelCut.cutTrunc_eq_self` applies with no
remainder. -/
theorem hev_of_cutHyp' [IsProbabilityMeasure P] (H : CutHyp' P J s t lev Θ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ H.δ₀) :
    HighProb P fun N => {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      ws ∈ Set.Icc (s N) (t N) →
      (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * lev N u) →
        J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
  intro D hD
  filter_upwards [netTrunc_highProb H hδ0 hδ D hD, eventually_ge_atTop 1] with N hN hN1
  refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hN
  intro ω hω ws hws hwsIcc hpre
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos (by linarith) _
  have hlpos : 0 < lev N ws := H.lev_pos N hwsIcc
  have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N ws := by positivity
  have heq : cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) = J N ws ω :=
    cutTrunc_eq_self hθ0 (hpre ws ⟨hwsIcc.1, le_rfl⟩)
  rw [← heq]
  exact hω ws hws

/-- The same, with the prefix read at the **constant** level `Θ`, which is what
`RBM.MomentDuhamelCut.stochDom_of_net` consumes.  The passage is `lev_ge`: a prefix bound at
the control is a prefix bound at the (larger) truncation level. -/
theorem hev_const_of_cutHyp' [IsProbabilityMeasure P] (H : CutHyp' P J s t lev Θ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ H.δ₀) :
    HighProb P fun N => {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      ws ∈ Set.Icc (s N) (t N) →
      (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
        J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
  intro D hD
  filter_upwards [hev_of_cutHyp' H hδ0 hδ D hD] with N hN
  refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hN
  intro ω hω ws hws hwsIcc hpre
  refine hω ws hws hwsIcc fun u hu => ?_
  have huIcc : u ∈ Set.Icc (s N) (t N) := ⟨hu.1, hu.2.trans hwsIcc.2⟩
  have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact (hpre u hu).trans (mul_le_mul_of_nonneg_left (H.lev_ge N u huIcc) hrp)

/-- **The bootstrap route**: exactly the conclusion of
`RBM.MomentDuhamelCut.stochDom_of_cutHyp`, from the generalized interface.  Nothing is lost by
the generalization. -/
theorem stochDom_of_cutHyp' [IsProbabilityMeasure P] (H : CutHyp' P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) :=
  stochDom_of_net H.δ₀_pos H.window H.Θ_pos hΘ1 H.continuousOn H.hclose
    (fun _δ hδ0 hδ => hev_const_of_cutHyp' H hδ0 hδ) hinit

/-- **The bridge from the previous pass to the prefix event.**

`K ≺ 1` uniformly on the window — the conclusion of the *first* pass — and a pointwise
comparison `J ≤ lev · K` give the prefix event that `stochDom_of_cutHyp'_of_prefix` consumes.
In the application `K = RBM.Step2Moment.jSnorm`, `J = RBM.Step2Near47.jSnorm2` and
`lev = (η_s/η_u)²`, and the comparison is an **equality** (`jSnorm2_eq_mul`). -/
theorem prefix_of_stochDom {K : ℕ → ℝ → Ω → ℝ}
    (hK : StochDom P (fun N (u : TimeIcc s t N) ω => K N (u : ℝ) ω) (fun _ _ _ => (1 : ℝ)))
    (hlev : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), 0 < lev N u)
    (hJK : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), ∀ ω, J N u ω ≤ lev N u * K N u ω)
    {δ : ℝ} (hδ : 0 < δ) :
    HighProb P fun N =>
      {ω | ∀ u ∈ Set.Icc (s N) (t N), J N u ω ≤ (N : ℝ) ^ (2 * δ) * lev N u} := by
  intro D hD
  filter_upwards [hK (2 * δ) (by linarith) D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨u, hu, hgt⟩ := hω
  refine ⟨⟨u, hu⟩, ?_⟩
  have hl := hlev N u hu
  have hcmp := hJK N u hu ω
  show (N : ℝ) ^ (2 * δ) * 1 < K N u ω
  nlinarith

/-- **The second pass: no bootstrap, no initial condition.**

`RBM.Step2Near47.phi_arith_second_pass` shows that the sharp one-step output already follows
from the *blunt* a priori level, so the sharp conclusion needs no bootstrap of its own.  This
is that statement at the level of the interface: given the prefix as an **external**
high-probability event — which is precisely what the first pass delivers, via
`prefix_of_stochDom` — the conclusion `J ≺ Θ` follows from `netTrunc_highProb` and the
modulus alone.

Compare `stochDom_of_cutHyp'`, which manufactures the prefix by continuous induction and
therefore needs `hinit` (the initial bound (2.68)/(2.69)) and `Θ ≥ 1`.  Neither appears
here. -/
theorem stochDom_of_cutHyp'_of_prefix [IsProbabilityMeasure P] (H : CutHyp' P J s t lev Θ)
    (hpre : ∀ δ, 0 < δ → δ ≤ H.δ₀ → HighProb P fun N =>
      {ω | ∀ u ∈ Set.Icc (s N) (t N), J N u ω ≤ (N : ℝ) ^ (2 * δ) * lev N u}) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) := by
  intro τ hτ D hD
  set δ : ℝ := min τ H.δ₀ with hδdef
  have hδ0 : (0 : ℝ) < δ := lt_min hτ H.δ₀_pos
  have hδτ : δ ≤ τ := min_le_left _ _
  filter_upwards [netTrunc_highProb H hδ0 (min_le_right _ _) (D + 1) (by linarith),
    hpre δ hδ0 (min_le_right _ _) (D + 1) (by linarith), eventually_ge_atTop 2] with N hA hB hN2
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hΘ0 := H.Θ_pos N
  have hmono : (N : ℝ) ^ δ ≤ (N : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1.le hδτ
  have hsub : badSet (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N) τ N ⊆
    ({ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
        cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) ≤ ((N : ℝ) ^ δ - 1) * Θ N})ᶜ ∪
    ({ω | ∀ u ∈ Set.Icc (s N) (t N), J N u ω ≤ (N : ℝ) ^ (2 * δ) * lev N u})ᶜ := by
    rintro ω ⟨v, hv⟩
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨hnet0, hprefix0⟩ := hno
    have hnet : ω ∈ {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
        cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
      by_contra hc; exact hnet0 hc
    have hprefix : ω ∈ {ω | ∀ u ∈ Set.Icc (s N) (t N),
        J N u ω ≤ (N : ℝ) ^ (2 * δ) * lev N u} := by
      by_contra hc; exact hprefix0 hc
    obtain ⟨ws, hwsS, hwsIcc, hwY⟩ := H.hclose N ω (v : ℝ) v.2
    have hwsb : ws ∈ Set.Icc (s N) (t N) := ⟨hwsIcc.1, hwsIcc.2.trans v.2.2⟩
    have hlpos : 0 < lev N ws := H.lev_pos N hwsb
    have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos (by linarith) _
    have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N ws := by positivity
    have heq : cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) = J N ws ω :=
      cutTrunc_eq_self hθ0 (hprefix ws hwsb)
    have hws : J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N := heq ▸ hnet ws hwsS
    have hle : J N (v : ℝ) ω ≤ (N : ℝ) ^ τ * Θ N := by
      calc J N (v : ℝ) ω ≤ J N ws ω + Θ N := hwY
        _ ≤ ((N : ℝ) ^ δ - 1) * Θ N + Θ N := by linarith
        _ = (N : ℝ) ^ δ * Θ N := by ring
        _ ≤ (N : ℝ) ^ τ * Θ N := mul_le_mul_of_nonneg_right hmono hΘ0.le
    exact absurd hv (not_lt.2 hle)
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  refine le_trans (add_le_add hA hB) ?_
  rw [← ENNReal.ofReal_add hp hp]
  refine ENNReal.ofReal_le_ofReal ?_
  have hkey : (2 : ℝ) * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
    have hN0 : (0 : ℝ) < N := by linarith
    have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hNR
    calc (2 : ℝ) * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(D + 1)) :=
          mul_le_mul_of_nonneg_right h2 hp
      _ = (N : ℝ) ^ (-D) := by rw [← Real.rpow_add hN0]; congr 1; ring
  linarith

end Hev

/-! ### 5. What a producer of the moment field has to supply -/

section Producer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **The reduction the producer of `moment` needs.**

`RBM.MomentDuhamelCut.CutHyp.moment` (and `CutHyp'.moment`) is an *unconditional* moment
bound, while a Duhamel computation only ever produces a bound **on the event where the a
priori bound holds along the whole prefix** — that event is what makes the intermediate
values of the loop hierarchy controllable, and the endpoint truncation `χ(J_{ws}/θ)` does not
supply it.  This theorem says the gap is exactly one high-probability input:

* `hcond` — the moment bound *restricted to* the prefix event `A N ws`.  This is what the
  truncated Duhamel of §5.3 gives.
* `hAhp` — the prefix event holds with probability `1 - O(N^{-D})` for **every** `D`, uniformly
  over the net.  For the second pass this is free: it is the conclusion of the first pass
  (`prefix_of_stochDom`).

Off the prefix event nothing is known about `J`, but the truncation's own envelope `2θ` is,
and `hlevpoly` says that envelope is polynomially bounded; `D` is then chosen after `p` to
beat it.  This is the one place where the arbitrary `D` of `RBM.HighProb` is used at an
order depending on `p`, which is why `hAhp` must be a genuine `HighProb`-style statement and
not a single fixed power.

Note the quantifier order: `D` is chosen **inside** `∀ p`, after `δ` and `ε`, exactly as
`RBM.Gauss.MomentDom` requires — writing `∀ p, ∀ N` or fixing `D` before `p` is the failure
mode recorded in `docs/STATUS.md` for T188. -/
theorem moment_of_conditional [IsFiniteMeasure P] {mesh : ℕ → ℝ} {δ₀ Clev : ℝ}
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω)
    (hmeas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => J N u ω) P)
    (hΘ0 : ∀ N, 0 < Θ N) (hClev : 0 ≤ Clev)
    (hlev0 : ∀ N, ∀ ws ∈ netFinset s t mesh N, 0 < lev N ws)
    (hlevpoly : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      2 * lev N ws ≤ (N : ℝ) ^ Clev * Θ N)
    (A : ℕ → ℝ → Set Ω) (hA : ∀ N ws, MeasurableSet (A N ws))
    (hAhp : ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      P (A N ws)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)))
    (hcond : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ netFinset s t mesh N,
        ∫ ω in A N ws, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
          ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p))) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ netFinset s t mesh N,
        ∫ ω, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
          ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)) := by
  intro δ hδ0 hδ ε hε p
  obtain ⟨C, hC0, hCN⟩ := hcond δ hδ0 hδ ε hε p
  -- the decay order, chosen **after** `p`
  set D : ℝ := (2 * δ + Clev) * (2 * p) + 1 with hDdef
  have hD0 : 0 < D := by
    have : (0 : ℝ) ≤ (2 * δ + Clev) * (2 * p) := by positivity
    linarith
  refine ⟨C + 1, by linarith, ?_⟩
  filter_upwards [hCN, hlevpoly, hAhp D hD0, eventually_ge_atTop 2] with
    N hcondN hlevN hAN hN2 ws hws
  have hb2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hb0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hb1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hΘ := hΘ0 N
  have hlp := hlev0 N ws hws
  have hX0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hb0 _
  have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N ws := by positivity
  have hint := integrable_cutTrunc_pow (P := P) hθ0 (fun ω => hJ0 N ws ω) (hmeas N ws) (2 * p)
  set M : ℝ := (2 * ((N : ℝ) ^ (2 * δ) * lev N ws)) ^ (2 * p) with hMdef
  have hM0 : (0 : ℝ) ≤ M := by positivity
  -- the deterministic envelope of the truncation is polynomially bounded
  have h2θ : 2 * ((N : ℝ) ^ (2 * δ) * lev N ws) ≤ (N : ℝ) ^ (2 * δ + Clev) * Θ N := by
    calc 2 * ((N : ℝ) ^ (2 * δ) * lev N ws) = (N : ℝ) ^ (2 * δ) * (2 * lev N ws) := by ring
      _ ≤ (N : ℝ) ^ (2 * δ) * ((N : ℝ) ^ Clev * Θ N) :=
          mul_le_mul_of_nonneg_left (hlevN ws hws) hX0.le
      _ = (N : ℝ) ^ (2 * δ + Clev) * Θ N := by rw [Real.rpow_add hb0]; ring
  have hMle : M ≤ (N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * Θ N ^ (2 * p) := by
    have h1 : M ≤ ((N : ℝ) ^ (2 * δ + Clev) * Θ N) ^ (2 * p) :=
      pow_le_pow_left₀ (by positivity) h2θ _
    refine h1.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (2 * δ + Clev)) (2 * p),
      ← Real.rpow_mul hb0.le]
    congr 2
    push_cast
    ring
  -- the tail of the prefix event costs `N^{-D}`, which `D`'s choice makes negligible
  have htail : M * (N : ℝ) ^ (-D) ≤ Θ N ^ (2 * p) := by
    have hpow : (0 : ℝ) < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hb0 _
    have hQ : (0 : ℝ) < Θ N ^ (2 * p) := by positivity
    have hcollapse : (N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * (N : ℝ) ^ (-D)
        = (N : ℝ) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hb0, hDdef]; congr 1; ring
    have hinv : (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hb0.le, Real.rpow_one]
      rw [inv_le_one_iff₀]
      right; linarith
    calc M * (N : ℝ) ^ (-D)
        ≤ ((N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * Θ N ^ (2 * p)) * (N : ℝ) ^ (-D) :=
          mul_le_mul_of_nonneg_right hMle hpow.le
      _ = ((N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * (N : ℝ) ^ (-D)) * Θ N ^ (2 * p) := by ring
      _ = (N : ℝ) ^ (-(1 : ℝ)) * Θ N ^ (2 * p) := by rw [hcollapse]
      _ ≤ 1 * Θ N ^ (2 * p) := mul_le_mul_of_nonneg_right hinv hQ.le
      _ = Θ N ^ (2 * p) := one_mul _
  -- split the integral at the prefix event
  have hsplit : ∫ ω, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
      = (∫ ω in A N ws, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P)
        + ∫ ω in (A N ws)ᶜ, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P :=
    (integral_add_compl (hA N ws) hint).symm
  have houter : ∫ ω in (A N ws)ᶜ,
      |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
      ≤ P.real (A N ws)ᶜ * M := by
    have h1 : ∫ ω in (A N ws)ᶜ,
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ ∫ _ω in (A N ws)ᶜ, M ∂P := by
      refine integral_mono hint.restrict (integrable_const M) fun ω => ?_
      dsimp only
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ0 (hJ0 N ws ω)) _
    simpa [MeasureTheory.setIntegral_const, smul_eq_mul] using h1
  have hPreal : P.real (A N ws)ᶜ ≤ (N : ℝ) ^ (-D) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hb0.le _) (hAN ws hws)
  have hεp : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hb1 (by positivity)
  have hQ0 : (0 : ℝ) < Θ N ^ (2 * p) := by positivity
  rw [hsplit]
  have hfin : P.real (A N ws)ᶜ * M ≤ Θ N ^ (2 * p) := by
    have h0 : (0 : ℝ) ≤ P.real (A N ws)ᶜ := measureReal_nonneg
    calc P.real (A N ws)ᶜ * M ≤ (N : ℝ) ^ (-D) * M :=
          mul_le_mul_of_nonneg_right hPreal hM0
      _ = M * (N : ℝ) ^ (-D) := by ring
      _ ≤ Θ N ^ (2 * p) := htail
  have hlast : Θ N ^ (2 * p) ≤ (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) := by
    nlinarith
  calc (∫ ω in A N ws, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P)
        + ∫ ω in (A N ws)ᶜ, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
      ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)) + P.real (A N ws)ᶜ * M :=
        add_le_add (hcondN ws hws) houter
    _ ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)) + (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) := by
        linarith
    _ = (C + 1) * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)) := by ring

end Producer

/-! ### 6. The second pass for `J*`: (5.47) sharp without a second bootstrap -/

section Sharp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The two normalizations differ by the level.**  `jSnorm2 = (η_s/η_u)² · jSnorm`, so by
`cutTrunc_level_smul` truncating `jSnorm2` at `N^{2δ}(η_s/η_u)²` is the *same* truncation as
truncating `jSnorm` at `N^{2δ}`: the supports are literally equal.  That is why the blunt
prefix is the right truncation level for the sharp functional. -/
theorem jSnorm2_eq_mul (X : Sample B) {D : ℝ} (hE : |E| < 2) {N : ℕ} (hs1 : s N < 1) {u : ℝ}
    (hu1 : u < 1) (ω : Ω) :
    Step2Near47.jSnorm2 X E D s N u ω
      = Step2Moment.ratR E s N u ^ 2 * Step2Moment.jSnorm X E D s N u ω := by
  have hR0 : 0 < Step2Moment.ratR E s N u := Step2Moment.ratR_pos hE hs1 hu1
  rw [Step2Near47.jSnorm2, Step2Moment.jSnorm]
  field_simp

/-- **The blunt a priori level of (5.43), read in the sharp normalization**: `(η_s/η_u)²`.
This is the function `CutHyp` cannot carry. -/
noncomputable def levSharp (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  Step2Moment.ratR E s N u ^ 2

/-- **The field `lev_ge` is satisfiable for the intended level** — on the window, and only
there.  `RBM.Step2Moment.one_le_ratR` needs `s_N ≤ u < 1`; at `u > 1` the ratio `η_s/η_u` is
negative and `levSharp` is *small*, so the unrestricted `∀ N u, Θ N ≤ lev N u` would be
false.  This is the check the ticket's item (a) asks for. -/
theorem sat_levSharp_ge (hE : |E| < 2) (ht1 : ∀ N, t N < 1) :
    ∀ N, ∀ u ∈ Set.Icc (s N) (t N), (1 : ℝ) ≤ levSharp E s N u := fun N _u hu =>
  one_le_pow₀ (Step2Moment.one_le_ratR (s := s) hE hu.1 (hu.2.trans_lt (ht1 N)))

/-- **The second-pass interface.**

A `CutHyp'` for the *sharply* normalized `J*` whose truncation level is the *blunt* one,
`(η_s/η_u)²` — the level the first pass has already established.

It has **no `init` field**.  `RBM.Step2Near47.MomentHypCutSharp` needs one because it re-runs
the bootstrap from the initial condition; here the prefix comes from the first pass instead
(`stochDom_jSnorm2_of_blunt`), which is `RBM.Step2Near47.phi_arith_second_pass`'s "no second
bootstrap" at the level of the interface. -/
structure MomentHypCut2 (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- The truncated moment Duhamel for `jSnorm2`, truncated at the blunt level. -/
  cut : CutHyp' B.P (fun N u ω => Step2Near47.jSnorm2 X E D s N u ω) s t (levSharp E s)
    (fun _ => 1)

variable {X : Sample B} {D : ℝ}

/-- **The second pass, for `J*`.**  From the first pass's conclusion `J*/(η_s/η_u)^4 ≺ 1`
(`RBM.MomentDuhamelCut.stochDom_jSnorm_cut`) and `MomentHypCut2`, the sharp normalization is
also `≺ 1` — with **no bootstrap and no initial condition**. -/
theorem stochDom_jSnorm2_of_blunt (H2 : MomentHypCut2 X E s t D) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    (hblunt : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2Moment.jSnorm X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2Near47.jSnorm2 X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  have := B.isProbabilityMeasure
  refine stochDom_of_cutHyp'_of_prefix H2.cut fun δ hδ0 _ => ?_
  refine prefix_of_stochDom hblunt (fun N u hu => ?_) (fun N u hu ω => ?_) hδ0
  · exact pow_pos (Step2Moment.ratR_pos hE ((H2.cut.window N).trans_lt (ht1 N))
      (hu.2.trans_lt (ht1 N))) 2
  · exact le_of_eq (jSnorm2_eq_mul X hE ((H2.cut.window N).trans_lt (ht1 N))
      (hu.2.trans_lt (ht1 N)) ω)

/-- **(5.47) sharp**, `J*_{u,D} ≺ (η_s/η_u)²`, in exactly the conclusion of
`RBM.Step2Near47.jS_stochDom_sharp` — but from `MomentHypCut2` plus the first pass, so the
sharp bound costs no second bootstrap and no second initial condition. -/
theorem jS_stochDom_sharp_of_cut2 (H2 : MomentHypCut2 X E s t D) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    (hblunt : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2Moment.jSnorm X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2) := by
  refine StochDom.of_subset (stochDom_jSnorm2_of_blunt H2 hE ht1 hblunt) fun τ hτ =>
    ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (H2.cut.window N).trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N (u : ℝ) ^ 2 :=
    pow_pos (Step2Moment.ratR_pos hE hs1 (u.2.2.trans_lt (ht1 N))) 2
  change (N : ℝ) ^ τ * 1 < Step2.jS X E D N (u : ℝ) ω / Step2Moment.ratR E s N (u : ℝ) ^ 2
  rw [mul_one, lt_div_iff₀ hR]
  exact hu

/-- **End to end**: the sharp (5.47) from T197's `RBM.MomentDuhamelCut.MomentHypCut` and
`MomentHypCut2` alone — the first pass supplies its own conclusion as the second pass's
prefix (`RBM.MomentDuhamelCut.stochDom_jSnorm_cut`), so the caller needs no extra input. -/
theorem jS_stochDom_sharp_of_cut2_of_momentHypCut (H2 : MomentHypCut2 X E s t D)
    (Hy : MomentDuhamelCut.MomentHypCut X E s t D) (hE : |E| < 2) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2) :=
  jS_stochDom_sharp_of_cut2 H2 hE ht1 (MomentDuhamelCut.stochDom_jSnorm_cut Hy)

/-- **T207 §3's hypothesis is no longer independent.**

`RBM.Step2Near47.MomentHypCutSharp` — the sharp interface expressible against the frozen
`RBM.MomentDuhamelCut.CutHyp`, and the last free assumption of that file — is *derived* here
from `MomentHypCut2` (its `cut` field, by `cutHyp_of_cutHyp'`: lowering the truncation level
from `(η_s/η_u)²` to `1` only weakens the moment bound) together with T197's
`RBM.MomentDuhamelCut.MomentHypCut` (its `init` field, which is literally the same statement
by `RBM.Step2Near47.jSnorm2_left`).

So the sharp route no longer adds an assumption of its own; what it adds is the `R^{-4p}`
gain inside `MomentHypCut2.cut`, which is the mathematical content of (5.47) and is exactly
what `RBM.Step2Near47.phi_arith_second_pass` establishes at the level of the one-step
arithmetic. -/
noncomputable def momentHypCutSharp_of_cut2 (H2 : MomentHypCut2 X E s t D)
    (Hy : MomentDuhamelCut.MomentHypCut X E s t D) (hE : |E| < 2) (ht1 : ∀ N, t N < 1) :
    Step2Near47.MomentHypCutSharp X E s t D := by
  haveI := B.isProbabilityMeasure
  refine { cut := cutHyp_of_cutHyp' H2.cut, init := ?_ }
  have hfun : (fun N (_ : Unit) (ω : Ω) => Step2Near47.jSnorm2 X E D s N (s N) ω)
      = fun N (_ : Unit) (ω : Ω) => Step2Moment.jSnorm X E D s N (s N) ω := by
    funext N _ ω
    exact Step2Near47.jSnorm2_left X hE ((H2.cut.window N).trans_lt (ht1 N)) ω
  rw [hfun]
  exact Hy.init

end Sharp

/-! ### 7. Satisfiability witnesses (compiled) -/

section Sat

/-- The witness's right endpoint `t_N = 1 - (N+2)⁻¹`, which tends to `1`: the window really
does reach the region where the level blows up. -/
noncomputable def satT (N : ℕ) : ℝ := 1 - ((N : ℝ) + 2)⁻¹

/-- The witness's `u`-dependent level `(1-u)⁻¹`, modelled on `(η_s/η_u)²` of `levSharp`
(`RBM.etaT` is `(1-u)·Im m`, so `η_s/η_u` is a constant times `(1-u)⁻¹`). -/
noncomputable def satLev (_N : ℕ) (u : ℝ) : ℝ := (1 - u)⁻¹

theorem satT_lt_one (N : ℕ) : satT N < 1 := by
  have : (0 : ℝ) < ((N : ℝ) + 2)⁻¹ := by positivity
  simp only [satT]; linarith

theorem satT_nonneg (N : ℕ) : (0 : ℝ) ≤ satT N := by
  have h0 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have h : ((N : ℝ) + 2)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; linarith
  simp only [satT]; linarith

/-- The witness's mesh, at the flow's own scaling `m_N ≍ N²` (so `mesh_fine` is *tight*, cf.
`RBM.MomentDuhamelCut.sat_mesh_card`). -/
noncomputable def satMesh (N : ℕ) : ℝ := ((N : ℝ) + 1) ^ (2 : ℝ)

theorem satMesh_pos (N : ℕ) : 0 < satMesh N := Real.rpow_pos_of_pos (by positivity) _

/-- On the window the level is at least the control: the field `lev_ge` holds. -/
theorem one_le_satLev {N : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (satT N)) :
    (1 : ℝ) ≤ satLev N u := by
  have hlt : u < 1 := lt_of_le_of_lt hu.2 (satT_lt_one N)
  have h1 : (0 : ℝ) < 1 - u := by linarith
  have h2 : (1 : ℝ) - u ≤ 1 := by linarith [hu.1]
  have h3 : (0 : ℝ) < (1 - u)⁻¹ := inv_pos.2 h1
  have h4 : (1 - u) * (1 - u)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  simp only [satLev]
  nlinarith

/-- **The generalization is not satisfied only by degenerate levels**: here the level is
unbounded on the window as its right endpoint approaches `1`, which is the regime
`levSharp = (η_s/η_u)²` actually lives in. -/
theorem sat_lev_unbounded (M : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∃ u ∈ Set.Icc (0 : ℝ) (satT N), M ≤ satLev N u := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop M] with N hN
  refine ⟨satT N, ⟨satT_nonneg N, le_rfl⟩, ?_⟩
  have h0 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hval : satLev N (satT N) = (N : ℝ) + 2 := by
    simp only [satLev, satT]
    rw [show (1 : ℝ) - (1 - ((N : ℝ) + 2)⁻¹) = ((N : ℝ) + 2)⁻¹ by ring, inv_inv]
  rw [hval]; linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A compiled `CutHyp'` at the critical scale `J ≡ Θ ≡ 1`, with a genuinely `u`-dependent
level.**

Deliberately *not* at `J ≡ 0` and *not* at a constant level: the functional sits exactly at
the level the interface propagates, and `satLev` is unbounded on the window
(`sat_lev_unbounded`).  `mesh_fine` and `card_le` — the pair that pulls in opposite
directions — are satisfied by the same witness, at the flow's own `γ = 1/2` and `m_N ≍ N²`. -/
noncomputable def satCutHyp' (P : Measure Ω) [IsProbabilityMeasure P] :
    CutHyp' P (fun _ _ _ => (1 : ℝ)) (fun _ => 0) satT satLev (fun _ => 1) where
  window := fun N => satT_nonneg N
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  lev_ge := fun _ _ hu => one_le_satLev hu
  J_nonneg := fun _ _ _ => zero_le_one
  meas := fun _ _ => aestronglyMeasurable_const
  mesh := satMesh
  mesh_pos := satMesh_pos
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := fun N _ v _ w _ => by
    simp only [sub_self, abs_zero]
    positivity
  mesh_fine := fun N => by
    have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : (1 / ((N : ℝ) + 1) ^ (2 : ℝ)) = ((N : ℝ) + 1) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg ha.le, one_div]
    have h2 : (-(2 : ℝ)) * ((1 : ℝ) / 2) = -1 := by norm_num
    simp only [satMesh]
    rw [h1, ← Real.rpow_mul ha.le, h2, Real.rpow_neg ha.le, Real.rpow_one, Real.rpow_one,
      ← div_eq_mul_inv, div_le_one ha]
    linarith
  Ccard := 3
  card_le := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h2 : ((N : ℝ) + 1) ^ (2 : ℝ) = ((N : ℝ) + 1) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((N : ℝ) + 1) 2]; norm_num
    have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast (N : ℝ) 3]; norm_num
    have ht0 : (0 : ℝ) ≤ satT N := satT_nonneg N
    have ht : satT N ≤ 1 := (satT_lt_one N).le
    have hsq : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (2 : ℕ) := by positivity
    have hkey : ((N : ℝ) + 1) ^ (2 : ℕ) + 2 ≤ (N : ℝ) ^ (3 : ℕ) := by nlinarith
    simp only [satMesh]
    rw [h2, h3]
    have hA : (satT N - 0) * ((N : ℝ) + 1) ^ (2 : ℕ) ≤ ((N : ℝ) + 1) ^ (2 : ℕ) := by
      nlinarith
    linarith
  moment := by
    intro δ hδ0 _ ε _ p
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN ws hws
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hwsIcc : ws ∈ Set.Icc (0 : ℝ) (satT N) :=
      netFinset_subset_Icc (satT_nonneg N) (satMesh_pos N) ws hws
    have hlev := one_le_satLev hwsIcc
    have hrp : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hN1 (by positivity)
    have hlv : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * satLev N ws := by nlinarith
    have hlv0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * satLev N ws := by linarith
    rw [cutTrunc_eq_self hlv0 hlv]
    have hεp : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1 (by positivity)
    simp only [abs_one, one_pow, one_mul]
    rw [MeasureTheory.integral_const]
    simpa using hεp

/-- The witness feeds the **bootstrap** route end to end. -/
theorem sat_stochDom_of_cutHyp' (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (_ : TimeIcc (fun _ => (0 : ℝ)) satT N) (_ : Ω) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_cutHyp' (satCutHyp' P) (Filter.Eventually.of_forall fun _ => le_rfl)
    (MomentDuhamelCut.sat_init P)

/-- The prefix event of the witness holds for every `ω` once `N ≥ 1`, so it is a `HighProb`
event: the `u`-dependent prefix is not an empty requirement made true by vacuity elsewhere. -/
theorem sat_prefix (P : Measure Ω) {δ : ℝ} (hδ : 0 < δ) :
    HighProb P fun N => {_ω : Ω | ∀ u ∈ Set.Icc ((fun _ => (0 : ℝ)) N) (satT N),
      (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * satLev N u} := by
  intro D hD
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hfull : ∀ ω : Ω, ω ∈ {_ω : Ω | ∀ u ∈ Set.Icc ((fun _ => (0 : ℝ)) N) (satT N),
      (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * satLev N u} := by
    intro _ u hu
    have hlev := one_le_satLev hu
    have hrp : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hN1 (by positivity)
    nlinarith
  calc P ({_ω : Ω | ∀ u ∈ Set.Icc ((fun _ => (0 : ℝ)) N) (satT N),
        (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * satLev N u})ᶜ
      ≤ P (∅ : Set Ω) := measure_mono fun ω hω => absurd (hfull ω) hω
    _ = 0 := measure_empty
    _ ≤ _ := bot_le

/-- The witness feeds the **prefix** route end to end — the one that uses neither the
bootstrap nor an initial condition. -/
theorem sat_stochDom_of_prefix (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (_ : TimeIcc (fun _ => (0 : ℝ)) satT N) (_ : Ω) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_cutHyp'_of_prefix (satCutHyp' P) fun _δ hδ _ => sat_prefix P hδ

/-- **Raising the level really raises `cutTrunc`.**  At `x = 3/2`, level `1` gives `3/4`
(T175's profile has `χ(3/2) = 1/2`) and level `2` gives `3/2`.  So `CutHyp'.mono_lev` is a
genuine one-way implication and `cutHyp_of_cutHyp'` really does *weaken* the hypothesis. -/
theorem sat_level_strict :
    cutTrunc 1 (3 / 2) = 3 / 4 ∧ cutTrunc 2 (3 / 2) = 3 / 2 := by
  constructor
  · have h : (3 : ℝ) / 2 / 1 = 3 / 2 := by norm_num
    rw [cutTrunc, h, Cutoff.cutChi_three_halves]; norm_num
  · rw [cutTrunc, Cutoff.cutChi_eq_one (by norm_num : (3 : ℝ) / 2 / 2 ≤ 1)]; norm_num

/-- **The degenerate window `s = t` is not a contradiction.**  The net collapses to the single
point `{s_N}`, so `moment` is asserted there and nowhere else, and `netFinset_subset_Icc`
still applies. -/
theorem sat_net_collapse (a m : ℕ → ℝ) (N : ℕ) : netFinset a a m N = {a N} := by
  unfold netFinset
  norm_num

end Sat

/-! ### 8. The stepwise bootstrap along the net (T222)

`RBM.MomentDuhamelCut.CutHyp.moment` is **unconditional**, while a truncated Duhamel
computation only ever produces a moment bound **on the event where the a priori bound holds
along the whole prefix** (§5 above).  `moment_of_conditional` reduced the gap to one
high-probability input; for the *second* pass that input is free (it is the first pass's
conclusion, `prefix_of_stochDom`), but for the *first* pass it is precisely what the
bootstrap is trying to prove.

This section removes the circularity.  The net of (5.46) is an arithmetic progression
`w_k = s_N + k/m_N`, so it can be walked **in order**: the prefix event needed at `w_k` is
implied by the *conclusion* at the net points `w_j`, `j < k`, through the modulus of
continuity alone (`CutHypCond.prefix_of_netGoodLt`).  Induction along `k` — in the form of a
"first bad index" decomposition (`Nat.find`, inside `netGood_highProb`) — therefore closes,
with the initial
condition (2.69) paying for `k = 0` and the union bound over the `N^{Ccard}` net points
costing a single `≺`-loss.

The conclusion `J ≺ Θ` then **implies the unconditional moment field back**
(`moment_of_stochDom`): the `∀ ε > 0` uniformity that `CutHyp.moment` asks for is exactly
what `RBM.StochDom` means, and off a `1 - N^{-D}` event the truncation's own envelope `2θ`
pays.  So `RBM.MomentDuhamelCut.CutHyp` — hence `MomentHypCut.cut`, hence `MomentHypCut2.cut`
— is produced from the **conditional** data alone.

Two consequences worth recording.

* `CutHyp.moment` is *equivalent* to its own conclusion given (2.69)
  (`moment_of_stochDom` one way, `RBM.MomentDuhamelCut.stochDom_of_cutHyp` the other).  It is
  therefore not a fiat: it is exactly as strong as what it is used to prove.
* The `∀ ε > 0` of `CutHyp.moment` can **not** come from the one-step arithmetic.  The output
  of `RBM.Step2MomentStep.phi_arith'` is `cStep' m · x² R⁴` with `x = N^{δ/8}`, i.e. a loss of
  `N^{δ/4}` per pass, not `N^{ε}`; see §10.  `CutHypCond.condMoment` therefore asks only for
  `N^{δ/2·p}`, which is what `x²` gives after raising to the `2p`-th power, and the `∀ ε`
  version is recovered afterwards from the conclusion.
-/

section Stepwise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **The prefix event**: the a priori bound at level `Λ` holds on all of `[s_N, ws]`.

This is the event on which the loop hierarchy of (5.39)–(5.44) is controlled at *every*
intermediate time, which is what a Duhamel computation at the endpoint `ws` needs and what
the endpoint truncation `χ(J_{ws}/θ)` does not supply. -/
def prefixEvent (J : ℕ → ℝ → Ω → ℝ) (s : ℕ → ℝ) (Λ : ℕ → ℝ → ℝ) (N : ℕ) (ws : ℝ) : Set Ω :=
  {ω | ∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ Λ N u}

omit [MeasurableSpace Ω] in
theorem mem_prefixEvent {Λ : ℕ → ℝ → ℝ} {N : ℕ} {ws : ℝ} {ω : Ω} :
    ω ∈ prefixEvent J s Λ N ws ↔ ∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ Λ N u := Iff.rfl

/-- The `k`-th point of the net of (5.46).  `RBM.MomentDuhamelCut.netFinset` is the image of
`Finset.range (cutNetTop + 1)` under this map (`netFinset_eq_image`), so the net can be walked
in order. -/
noncomputable def cutNetPt (s mesh : ℕ → ℝ) (N k : ℕ) : ℝ := s N + (k : ℝ) / mesh N

/-- The index of the last net point. -/
noncomputable def cutNetTop (s t mesh : ℕ → ℝ) (N : ℕ) : ℕ := ⌊(t N - s N) * mesh N⌋₊

theorem netFinset_eq_image (s t mesh : ℕ → ℝ) (N : ℕ) :
    netFinset s t mesh N
      = (Finset.range (cutNetTop s t mesh N + 1)).image (cutNetPt s mesh N) := rfl

theorem cutNetPt_zero (s mesh : ℕ → ℝ) (N : ℕ) : cutNetPt s mesh N 0 = s N := by
  simp [cutNetPt]

theorem cutNetPt_mem_netFinset {s t mesh : ℕ → ℝ} {N k : ℕ} (hk : k ≤ cutNetTop s t mesh N) :
    cutNetPt s mesh N k ∈ netFinset s t mesh N :=
  Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩

theorem exists_cutNetPt_eq {s t mesh : ℕ → ℝ} {N : ℕ} {ws : ℝ}
    (hws : ws ∈ netFinset s t mesh N) :
    ∃ k ≤ cutNetTop s t mesh N, ws = cutNetPt s mesh N k := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hws
  exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), rfl⟩

/-- **The walk is possible**: every point of `[a, a + k/m]` has a net point of index
**strictly** below `k` within one mesh of it, as soon as `k ≥ 1`.

This is the one combinatorial fact the stepwise bootstrap rests on, and the reason the
induction is well founded: the prefix needed at the `k`-th net point — *including* its own
endpoint — is controlled by the values at net points `j < k`, so no self-reference occurs.
`RBM.MomentDuhamelCut.exists_mem_netFinset` is not enough: at `v = a + k/m` it may return the
`k`-th point itself. -/
theorem exists_index_lt {a m v : ℝ} (hm : 0 < m) {k : ℕ} (hk : 1 ≤ k) (hav : a ≤ v)
    (hvk : v ≤ a + (k : ℝ) / m) :
    ∃ j < k, a + (j : ℝ) / m ≤ v ∧ v - (a + (j : ℝ) / m) ≤ 1 / m := by
  set y : ℝ := (v - a) * m with hy
  have hy0 : 0 ≤ y := by rw [hy]; have : (0 : ℝ) ≤ v - a := by linarith
                         positivity
  have hyk : y ≤ (k : ℝ) := by
    have h1 : v - a ≤ (k : ℝ) / m := by linarith
    rw [hy, ← le_div_iff₀ hm]
    exact h1
  refine ⟨min ⌊y⌋₊ (k - 1), ?_, ?_, ?_⟩
  · have := min_le_right ⌊y⌋₊ (k - 1); omega
  · have h1 : ((min ⌊y⌋₊ (k - 1) : ℕ) : ℝ) ≤ y := by
      have h2 : ((min ⌊y⌋₊ (k - 1) : ℕ) : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.cast_le.2 (min_le_left ⌊y⌋₊ (k - 1))
      exact h2.trans (Nat.floor_le hy0)
    have h3 : ((min ⌊y⌋₊ (k - 1) : ℕ) : ℝ) / m ≤ v - a := by
      rw [div_le_iff₀ hm]; rw [hy] at h1; exact h1
    linarith
  · have hA : y - 1 ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one y; linarith
    have hB : y - 1 ≤ ((k - 1 : ℕ) : ℝ) := by
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (1 : ℕ) ≤ k := hk
        push_cast [Nat.cast_sub this]; ring
      rw [hcast]; linarith
    have hmin : y - 1 ≤ ((min ⌊y⌋₊ (k - 1) : ℕ) : ℝ) := by
      rw [Nat.cast_min]; exact le_min hA hB
    have hdiv : (y - 1) / m ≤ ((min ⌊y⌋₊ (k - 1) : ℕ) : ℝ) / m := by gcongr
    have heq : (y - 1) / m = v - a - 1 / m := by rw [hy]; field_simp
    rw [heq] at hdiv
    linarith

/-- **The net-level good event**: the functional is below `c` at every net point of index
`< k`.  A *finite* intersection, hence null measurable for free — no continuity of the paths
is needed to condition on it. -/
def netGoodLt (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ) (c : ℝ) (N k : ℕ) : Set Ω :=
  {ω | ∀ j < k, J N (cutNetPt s mesh N j) ω ≤ c}

omit [MeasurableSpace Ω] in
theorem netGoodLt_zero (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    netGoodLt J s mesh c N 0 = Set.univ := by
  ext ω; simp [netGoodLt]

omit [MeasurableSpace Ω] in
theorem netGoodLt_antitone {mesh : ℕ → ℝ} {c : ℝ} {N k l : ℕ} (hkl : k ≤ l) :
    netGoodLt J s mesh c N l ⊆ netGoodLt J s mesh c N k :=
  fun _ hω j hj => hω j (lt_of_lt_of_le hj hkl)

end Stepwise

/-! ### 9. The conditional interface, and the producers it feeds -/

section Cond

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **The conditional truncated moment Duhamel interface.**

Field for field the deterministic half of `CutHyp'`, with `moment` replaced by `condMoment`:
the moment bound is asked for only **on the prefix event**, which is what §5.3's Duhamel
computation produces, and only at the single loss `N^{δ/2·p}`, which is what the one-step
arithmetic `RBM.Step2MomentStep.phi_arith'` gives (its output is `cStep' m · x² R⁴` with
`x = N^{δ/8}`; see §10).  `CutHyp'.moment` asks for both more than that — unconditionally,
and for *every* `ε > 0` — and both surpluses are recovered for free afterwards, the first by
`netGood_highProb` and the second by `moment_of_stochDom`.

The two extra fields `Clev`/`levpoly` say the truncation level is polynomially bounded
relative to the control; they are what pays for the part of the sample space where the a
priori bound fails, and for the constant level `lev = Θ` of the first pass `Clev = 1` does it
(`levpoly_const`).

**Quantifier order** (T188): `δ` first, then `p`, then `∃ C`, then `∀ᶠ N`.  `C` may depend on
`δ` and `p` — it has to: `C = (cStep' m)^{2p}` is the honest constant. -/
structure CutHypCond (P : Measure Ω) (J : ℕ → ℝ → Ω → ℝ) (s t : ℕ → ℝ) (lev : ℕ → ℝ → ℝ)
    (Θ : ℕ → ℝ) where
  /-- The window is non-degenerate. -/
  window : ∀ N, s N ≤ t N
  /-- The range `0 < δ ≤ δ₀` of bootstrap margins. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  Θ_pos : ∀ N, 0 < Θ N
  /-- The truncation level dominates the control, on the window. -/
  lev_ge : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u
  /-- The state functional is nonnegative. -/
  J_nonneg : ∀ N u ω, 0 ≤ J N u ω
  meas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => J N u ω) P
  /-- The mesh of the net of (5.46). -/
  mesh : ℕ → ℝ
  mesh_pos : ∀ N, 0 < mesh N
  /-- The exponent of the deterministic modulus of continuity. -/
  Kmod : ℝ
  /-- Its Hölder exponent. -/
  γ : ℝ
  γ_pos : 0 < γ
  /-- The deterministic modulus of continuity, valid for **every** `ω`. -/
  modulus : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    |J N v ω - J N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ
  /-- The net is fine enough that one mesh of displacement costs at most `Θ_N`. -/
  mesh_fine : ∀ N : ℕ, (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ N
  /-- The exponent of the net's cardinality. -/
  Ccard : ℝ
  /-- The net is polynomially large, so the union bound is a `≺`-loss. -/
  card_le : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard
  /-- The exponent bounding the truncation level against the control. -/
  Clev : ℝ
  Clev_nonneg : 0 ≤ Clev
  levpoly : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
    2 * lev N ws ≤ (N : ℝ) ^ Clev * Θ N
  /-- **The truncated one-step moment bound at the net points, on the prefix event.** -/
  condMoment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ netFinset s t mesh N,
      ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p))

namespace CutHypCond

theorem lev_pos (H : CutHypCond P J s t lev Θ) (N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (s N) (t N)) : 0 < lev N u :=
  lt_of_lt_of_le (H.Θ_pos N) (H.lev_ge N u hu)

theorem lev_pos_net (H : CutHypCond P J s t lev Θ) (N : ℕ) {ws : ℝ}
    (hws : ws ∈ netFinset s t H.mesh N) : 0 < lev N ws :=
  H.lev_pos N (netFinset_subset_Icc (H.window N) (H.mesh_pos N) ws hws)

theorem continuousOn (H : CutHypCond P J s t lev Θ) (N : ℕ) (ω : Ω) :
    ContinuousOn (fun u => J N u ω) (Set.Icc (s N) (t N)) :=
  continuousOn_of_modulus H.γ_pos (H.modulus N ω)

/-- Every time of the window has a net point to its left at which the functional is smaller by
at most `Θ_N`. -/
theorem hclose (H : CutHypCond P J s t lev Θ) (N : ℕ) (ω : Ω) :
    ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      ws ∈ Set.Icc (s N) v ∧ J N v ω ≤ J N ws ω + Θ N := by
  intro v hv
  obtain ⟨ws, hwsF, hwsIcc, hgap⟩ := exists_mem_netFinset (t := t) (H.mesh_pos N) hv
  refine ⟨ws, Finset.mem_coe.2 hwsF, hwsIcc, ?_⟩
  have hwsb : ws ∈ Set.Icc (s N) (t N) := ⟨hwsIcc.1, hwsIcc.2.trans hv.2⟩
  have habs : |v - ws| ≤ 1 / H.mesh N := by
    rw [abs_of_nonneg (by linarith [hwsIcc.2])]
    exact hgap
  have h1 : |v - ws| ^ H.γ ≤ (1 / H.mesh N) ^ H.γ :=
    Real.rpow_le_rpow (abs_nonneg _) habs H.γ_pos.le
  have hK : (0 : ℝ) ≤ (N : ℝ) ^ H.Kmod := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (N : ℝ) ^ H.Kmod * |v - ws| ^ H.γ ≤ Θ N :=
    le_trans (mul_le_mul_of_nonneg_left h1 hK) (H.mesh_fine N)
  have h3 := (le_abs_self _).trans ((H.modulus N ω v hv ws hwsb).trans h2)
  linarith

/-- **The step of the induction, deterministically.**

On the net-level good event `netGoodLt c N k` — the values at the net points of index `< k`
are below `c` — the a priori bound at level `c + Θ_N` holds **everywhere on `[s_N, w_k]`,
including the endpoint `w_k` itself**.  This is `exists_index_lt` plus the modulus, and it is
why the `k`-th step of the bootstrap can condition on the conclusions of the earlier steps
without circularity. -/
theorem prefix_of_netGoodLt (H : CutHypCond P J s t lev Θ) {N k : ℕ} (hk : 1 ≤ k)
    (hkT : k ≤ cutNetTop s t H.mesh N) {c : ℝ} {ω : Ω}
    (hω : ω ∈ netGoodLt J s H.mesh c N k) :
    ∀ v ∈ Set.Icc (s N) (cutNetPt s H.mesh N k), J N v ω ≤ c + Θ N := by
  intro v hv
  have hwkIcc : cutNetPt s H.mesh N k ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (H.window N) (H.mesh_pos N) _ (cutNetPt_mem_netFinset hkT)
  have hvIcc : v ∈ Set.Icc (s N) (t N) := ⟨hv.1, hv.2.trans hwkIcc.2⟩
  obtain ⟨j, hjk, hjle, hjgap⟩ :=
    exists_index_lt (a := s N) (m := H.mesh N) (H.mesh_pos N) hk hv.1 hv.2
  set wj : ℝ := s N + (j : ℝ) / H.mesh N with hwj
  have hwjIcc : wj ∈ Set.Icc (s N) (t N) := ⟨by
      have : (0 : ℝ) ≤ (j : ℝ) / H.mesh N :=
        div_nonneg (Nat.cast_nonneg j) (H.mesh_pos N).le
      rw [hwj]; linarith, hjle.trans hvIcc.2⟩
  have hJj : J N wj ω ≤ c := hω j hjk
  have habs : |v - wj| ≤ 1 / H.mesh N := by
    rw [abs_of_nonneg (by linarith)]
    exact hjgap
  have h1 : |v - wj| ^ H.γ ≤ (1 / H.mesh N) ^ H.γ :=
    Real.rpow_le_rpow (abs_nonneg _) habs H.γ_pos.le
  have hK : (0 : ℝ) ≤ (N : ℝ) ^ H.Kmod := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (N : ℝ) ^ H.Kmod * |v - wj| ^ H.γ ≤ Θ N :=
    le_trans (mul_le_mul_of_nonneg_left h1 hK) (H.mesh_fine N)
  have h3 := (le_abs_self _).trans ((H.modulus N ω v hvIcc wj hwjIcc).trans h2)
  linarith

end CutHypCond

/-- **⭐ The stepwise bootstrap along the net.**

The first pass closes *without* an unconditional moment bound.  The net of (5.46) is walked in
order: at the `k`-th point the conditional moment bound `CutHypCond.condMoment` is applied on
the event `netGoodLt c N k` that the improvement has already been achieved at the net points
of index `< k`, and `CutHypCond.prefix_of_netGoodLt` turns that event into the a priori bound
on the whole of `[s_N, w_k]` — the hypothesis the Duhamel needs.  The decomposition at the
**first bad index** turns the walk into a single union bound, and the initial condition (2.69)
pays for `k = 0`.

This is what `moment_of_conditional` could not do: there the prefix event was an input, and
for the first pass it is the conclusion.  Here it is supplied, step by step, by the
conclusion at the *earlier* steps, so no circularity occurs.  The cost is one extra
`≺`-loss in the union bound over the `N^{Ccard}` net points — the same one
`netTrunc_highProb` already pays. -/
theorem netGood_highProb [IsProbabilityMeasure P] (H : CutHypCond P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ)))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ H.δ₀) :
    HighProb P fun N => {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
  classical
  intro D hD
  set Cc : ℝ := |H.Ccard| with hCc
  have hCc0 : 0 ≤ Cc := abs_nonneg _
  have hCcge : H.Ccard ≤ Cc := le_abs_self _
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + Cc + 2) * 2 / δ)
  have hpδ : D + Cc + 2 ≤ δ / 2 * (p : ℝ) := by
    rw [div_le_iff₀ hδ0] at hp; nlinarith
  have hexp : 0 < δ / 2 * (p : ℝ) - Cc - D - 1 := by linarith
  obtain ⟨C, hC0, hCN⟩ := H.condMoment δ hδ0 hδ p
  filter_upwards [hCN, H.card_le, hΘ1,
    hinit (δ / 2) (half_pos hδ0) (D + Cc + 1) (by linarith),
    eventually_ge_atTop 2, eventually_le_rpow C hexp,
    eventually_le_rpow (2 : ℝ) (half_pos hδ0)] with
    N hcondN hcardN hΘ1N hinitN hN2 hCle hhalf
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hΘ0 := H.Θ_pos N
  set a : ℝ := (N : ℝ) ^ (δ / 2) with ha
  have ha2 : (2 : ℝ) ≤ a := hhalf
  have haa : (N : ℝ) ^ δ = a * a := by
    rw [ha, ← Real.rpow_add hN0]; congr 1; ring
  have hac : a ≤ (N : ℝ) ^ δ - 1 := by rw [haa]; nlinarith
  set c : ℝ := ((N : ℝ) ^ δ - 1) * Θ N with hc
  have hcge : a * Θ N ≤ c := by rw [hc]; nlinarith
  have hcpos : 0 < c := by nlinarith
  set n : ℕ := cutNetTop s t H.mesh N with hn
  -- the per-index bound
  have hstep : ∀ k ∈ Finset.range (n + 1),
      P (netGoodLt J s H.mesh c N k ∩ {ω | c < J N (cutNetPt s H.mesh N k) ω})
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + Cc + 1))) := by
    intro k hk
    have hkT : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- the initial step: (2.69) pays
      rw [netGoodLt_zero, Set.univ_inter]
      refine le_trans (measure_mono ?_) hinitN
      intro ω hω
      have hω' : c < J N (cutNetPt s H.mesh N 0) ω := hω
      rw [cutNetPt_zero] at hω'
      refine ⟨(), ?_⟩
      show (N : ℝ) ^ (δ / 2) * 1 < J N (s N) ω
      rw [mul_one, ← ha]
      nlinarith
    · -- the inductive step: the conditional moment on `netGoodLt`
      have hwkF : cutNetPt s H.mesh N k ∈ netFinset s t H.mesh N :=
        cutNetPt_mem_netFinset hkT
      have hwkIcc : cutNetPt s H.mesh N k ∈ Set.Icc (s N) (t N) :=
        netFinset_subset_Icc (H.window N) (H.mesh_pos N) _ hwkF
      have hlev0 : 0 < lev N (cutNetPt s H.mesh N k) := H.lev_pos N hwkIcc
      have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hN0 _
      have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k) := by positivity
      have hNδ : (0 : ℝ) < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hN0 _
      have hNδ2δ : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (2 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      -- on the good event the a priori bound holds on the whole prefix
      have hpre : ∀ ω ∈ netGoodLt J s H.mesh c N k,
          ∀ v ∈ Set.Icc (s N) (cutNetPt s H.mesh N k), J N v ω ≤ (N : ℝ) ^ δ * Θ N := by
        intro ω hω v hv
        have h1 := H.prefix_of_netGoodLt hk1 hkT hω v hv
        rw [hc] at h1
        nlinarith
      have hGsub : netGoodLt J s H.mesh c N k
          ⊆ prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N
              (cutNetPt s H.mesh N k) := by
        intro ω hω u hu
        have h1 := hpre ω hω u hu
        have huIcc : u ∈ Set.Icc (s N) (t N) := ⟨hu.1, hu.2.trans hwkIcc.2⟩
        have h2 := H.lev_ge N u huIcc
        have h3 : (N : ℝ) ^ δ * Θ N ≤ (N : ℝ) ^ (2 * δ) * lev N u := by nlinarith
        linarith
      have hint := integrable_cutTrunc_pow (P := P) hθ0
        (fun ω => H.J_nonneg N (cutNetPt s H.mesh N k) ω)
        (H.meas N (cutNetPt s H.mesh N k)) (2 * p)
      have hMG : ∫ ω in netGoodLt J s H.mesh c N k,
          |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k))
            (J N (cutNetPt s H.mesh N k) ω)| ^ (2 * p) ∂P
          ≤ C * ((N : ℝ) ^ (δ / 2 * (p : ℝ)) * Θ N ^ (2 * p)) := by
        refine le_trans (setIntegral_mono_set hint.restrict ?_ ?_) (hcondN _ hwkF)
        · exact Filter.Eventually.of_forall fun ω => by positivity
        · exact Filter.Eventually.of_forall fun ω hω => hGsub hω
      have : IsFiniteMeasure (P.restrict (netGoodLt J s H.mesh c N k)) :=
        ⟨lt_of_le_of_lt (Measure.restrict_apply_le _ _) (measure_lt_top P _)⟩
      have hmark := Gauss.meas_gt_le_of_moment (P.restrict (netGoodLt J s H.mesh c N k))
        hcpos hint.restrict hMG
      have hsubset : netGoodLt J s H.mesh c N k ∩
            {ω | c < J N (cutNetPt s H.mesh N k) ω}
          ⊆ {ω | c < cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k))
              (J N (cutNetPt s H.mesh N k) ω)} ∩ netGoodLt J s H.mesh c N k := by
        rintro ω ⟨hωG, hωB⟩
        refine ⟨?_, hωG⟩
        have hle : J N (cutNetPt s H.mesh N k) ω
            ≤ (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k) := by
          have h1 := hpre ω hωG (cutNetPt s H.mesh N k) ⟨hwkIcc.1, le_rfl⟩
          have h2 := H.lev_ge N (cutNetPt s H.mesh N k) hwkIcc
          nlinarith
        show c < cutTrunc _ _
        rw [cutTrunc_eq_self hθ0 hle]
        exact hωB
      refine le_trans (measure_mono hsubset) ?_
      refine le_trans (Measure.le_restrict_apply _ _) ?_
      refine le_trans hmark (ENNReal.ofReal_le_ofReal ?_)
      -- the arithmetic: `C N^{δp/2} Θ^{2p} / c^{2p} ≤ N^{-(D+Cc+1)}`
      have hcp : (0 : ℝ) < c ^ (2 * p) := by positivity
      rw [div_le_iff₀ hcp]
      have hapow : a ^ (2 * p) = (N : ℝ) ^ (δ * (p : ℝ)) := by
        rw [ha, ← Real.rpow_natCast ((N : ℝ) ^ (δ / 2)) (2 * p), ← Real.rpow_mul hN0.le]
        congr 1; push_cast; ring
      have hcpow : (N : ℝ) ^ (δ * (p : ℝ)) * Θ N ^ (2 * p) ≤ c ^ (2 * p) := by
        have h2 : (a * Θ N) ^ (2 * p) ≤ c ^ (2 * p) :=
          pow_le_pow_left₀ (by positivity) hcge _
        rwa [mul_pow, hapow] at h2
      have hkey : C * (N : ℝ) ^ (δ / 2 * (p : ℝ))
          ≤ (N : ℝ) ^ (-(D + Cc + 1)) * (N : ℝ) ^ (δ * (p : ℝ)) := by
        calc C * (N : ℝ) ^ (δ / 2 * (p : ℝ))
            ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ) - Cc - D - 1) * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
              gcongr
          _ = (N : ℝ) ^ (-(D + Cc + 1)) * (N : ℝ) ^ (δ * (p : ℝ)) := by
              rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
      have hQ0 : (0 : ℝ) ≤ Θ N ^ (2 * p) := by positivity
      have hDp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + Cc + 1)) := Real.rpow_nonneg hN0.le _
      calc C * ((N : ℝ) ^ (δ / 2 * (p : ℝ)) * Θ N ^ (2 * p))
          = (C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) * Θ N ^ (2 * p) := by ring
        _ ≤ ((N : ℝ) ^ (-(D + Cc + 1)) * (N : ℝ) ^ (δ * (p : ℝ))) * Θ N ^ (2 * p) := by
            exact mul_le_mul_of_nonneg_right hkey hQ0
        _ = (N : ℝ) ^ (-(D + Cc + 1)) * ((N : ℝ) ^ (δ * (p : ℝ)) * Θ N ^ (2 * p)) := by ring
        _ ≤ (N : ℝ) ^ (-(D + Cc + 1)) * c ^ (2 * p) :=
            mul_le_mul_of_nonneg_left hcpow hDp
  -- the first bad index
  have hsub : ({ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ), J N ws ω ≤ c})ᶜ
      ⊆ ⋃ k ∈ Finset.range (n + 1),
          (netGoodLt J s H.mesh c N k ∩ {ω | c < J N (cutNetPt s H.mesh N k) ω}) := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_coe, not_forall, not_le] at hω
    obtain ⟨ws, hwsF, hgt⟩ := hω
    obtain ⟨k₀, hk₀, rfl⟩ := exists_cutNetPt_eq hwsF
    have hex : ∃ k, k ≤ n ∧ c < J N (cutNetPt s H.mesh N k) ω := ⟨k₀, hk₀, hgt⟩
    obtain ⟨hkn, hkgt⟩ := Nat.find_spec hex
    refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hkn)) ⟨?_, hkgt⟩
    intro j hj
    by_contra hcon
    exact Nat.find_min hex hj ⟨le_of_lt (lt_of_lt_of_le hj hkn), not_le.1 hcon⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hstep) ?_
  have hr0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + Cc + 1)) := Real.rpow_nonneg hN0.le _
  -- the net is polynomially large
  have hnn : (0 : ℝ) ≤ (t N - s N) * H.mesh N := by
    have h1 : (0 : ℝ) ≤ t N - s N := by linarith [H.window N]
    have h2 := H.mesh_pos N
    positivity
  have hncard : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ Cc := by
    have h1 : ((n : ℕ) : ℝ) ≤ (t N - s N) * H.mesh N := by
      rw [hn]; exact Nat.floor_le hnn
    have h2 : (N : ℝ) ^ H.Ccard ≤ (N : ℝ) ^ Cc :=
      Real.rpow_le_rpow_of_exponent_le hN1 hCcge
    push_cast
    linarith
  rw [Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((n + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-(D + Cc + 1))
      ≤ (N : ℝ) ^ Cc * (N : ℝ) ^ (-(D + Cc + 1)) :=
        mul_le_mul_of_nonneg_right hncard hr0
    _ = (N : ℝ) ^ (-(D + 1)) := by rw [← Real.rpow_add hN0]; congr 1; ring
    _ ≤ (N : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- **`J ≺ Θ` from the conditional interface alone** — the conclusion of
`RBM.MomentDuhamelCut.stochDom_of_cutHyp`, with `CutHyp.moment` replaced by the conditional
`CutHypCond.condMoment`.

No continuous induction is needed any more: `netGood_highProb` already controls *every* net
point, and `CutHypCond.hclose` carries that to the whole window in one step. -/
theorem stochDom_of_condMoment [IsProbabilityMeasure P] (H : CutHypCond P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) := by
  intro τ hτ D hD
  set δ : ℝ := min τ H.δ₀ with hδdef
  have hδ0 : (0 : ℝ) < δ := lt_min hτ H.δ₀_pos
  have hδτ : δ ≤ τ := min_le_left _ _
  filter_upwards [netGood_highProb H hΘ1 hinit hδ0 (min_le_right _ _) D hD,
    eventually_ge_atTop 2] with N hN hN2
  refine le_trans (measure_mono ?_) hN
  rintro ω ⟨v, hv⟩
  by_contra hno
  have hgood : ω ∈ {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
    by_contra hc; exact hno hc
  obtain ⟨ws, hwsS, hwsIcc, hwY⟩ := H.hclose N ω (v : ℝ) v.2
  have hws := hgood ws hwsS
  have hΘ0 := H.Θ_pos N
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hmono : (N : ℝ) ^ δ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hN1 hδτ
  have hle : J N (v : ℝ) ω ≤ (N : ℝ) ^ τ * Θ N := by
    calc J N (v : ℝ) ω ≤ J N ws ω + Θ N := hwY
      _ ≤ ((N : ℝ) ^ δ - 1) * Θ N + Θ N := by linarith
      _ = (N : ℝ) ^ δ * Θ N := by ring
      _ ≤ (N : ℝ) ^ τ * Θ N := mul_le_mul_of_nonneg_right hmono hΘ0.le
  exact absurd hv (not_lt.2 hle)

/-- **⭐ The moment field follows from its own conclusion.**

`RBM.MomentDuhamelCut.CutHyp.moment` asks for the truncated `2p`-th moment to be
`≤ C N^{εp}Θ^{2p}` for **every** `ε > 0`.  That uniformity cannot come from the one-step
arithmetic — `RBM.Step2MomentStep.phi_arith'` outputs `cStep' m · x²R⁴` with `x = N^{δ/8}`,
a fixed power of `N` (§10).  It comes from the *conclusion*: `J ≺ Θ` says exactly that
`J ≤ N^{ε/2}Θ` off an event of probability `N^{-D}` for every `D`, and on that event the
truncation's own envelope `2·N^{2δ}lev` — polynomially bounded by `levpoly` — is beaten by
choosing `D` after `p`.

Two consequences.  First, `CutHyp.moment` is **equivalent** to its conclusion given the
initial condition (this direction here, the converse
`RBM.MomentDuhamelCut.stochDom_of_cutHyp`), so it is not a fiat: it is exactly as strong as
what it is used to prove.  Second, a producer only ever has to supply the *conditional*,
*single-`ε`* bound `CutHypCond.condMoment`; everything else is recovered.

No measurability of the a priori event is needed: `MeasureTheory.toMeasurable` replaces it by
a measurable superset of the same measure. -/
theorem moment_of_stochDom [IsProbabilityMeasure P] {mesh : ℕ → ℝ} {Clev : ℝ}
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω)
    (hmeas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => J N u ω) P)
    (hΘ0 : ∀ N, 0 < Θ N) (hClev : 0 ≤ Clev) (hst : ∀ N, s N ≤ t N) (hmesh : ∀ N, 0 < mesh N)
    (hlev0 : ∀ N, ∀ ws ∈ netFinset s t mesh N, 0 < lev N ws)
    (hlevpoly : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      2 * lev N ws ≤ (N : ℝ) ^ Clev * Θ N)
    (hSD : StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N))
    (δ : ℝ) (hδ0 : 0 < δ) (ε : ℝ) (hε : 0 < ε) (p : ℕ) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      ∫ ω, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)) := by
  set Dd : ℝ := (2 * δ + Clev) * (2 * p) + 1 with hDd
  have hD0 : 0 < Dd := by
    have : (0 : ℝ) ≤ (2 * δ + Clev) * (2 * p) := by positivity
    linarith
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [hSD (ε / 2) (half_pos hε) Dd hD0, hlevpoly, eventually_ge_atTop 2] with
    N hSDN hlevN hN2 ws hws
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hΘ := hΘ0 N
  have hlp := hlev0 N ws hws
  have hX0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hN0 _
  have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * lev N ws := by positivity
  have hint := integrable_cutTrunc_pow (P := P) hθ0 (fun ω => hJ0 N ws ω) (hmeas N ws) (2 * p)
  have hwsIcc : ws ∈ Set.Icc (s N) (t N) := netFinset_subset_Icc (hst N) (hmesh N) ws hws
  set Bad : Set Ω := badSet (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω)
    (fun N _ _ => Θ N) (ε / 2) N with hBad
  set B : Set Ω := toMeasurable P Bad with hB
  have hBmeas : MeasurableSet B := measurableSet_toMeasurable _ _
  have hBsub : Bad ⊆ B := subset_toMeasurable _ _
  have hBmeasure : P B ≤ ENNReal.ofReal ((N : ℝ) ^ (-Dd)) := by
    rw [hB, measure_toMeasurable]; exact hSDN
  set M : ℝ := (2 * ((N : ℝ) ^ (2 * δ) * lev N ws)) ^ (2 * p) with hM
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have h2θ : 2 * ((N : ℝ) ^ (2 * δ) * lev N ws) ≤ (N : ℝ) ^ (2 * δ + Clev) * Θ N := by
    calc 2 * ((N : ℝ) ^ (2 * δ) * lev N ws) = (N : ℝ) ^ (2 * δ) * (2 * lev N ws) := by ring
      _ ≤ (N : ℝ) ^ (2 * δ) * ((N : ℝ) ^ Clev * Θ N) :=
          mul_le_mul_of_nonneg_left (hlevN ws hws) hX0.le
      _ = (N : ℝ) ^ (2 * δ + Clev) * Θ N := by rw [Real.rpow_add hN0]; ring
  have hMle : M ≤ (N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * Θ N ^ (2 * p) := by
    have h1 : M ≤ ((N : ℝ) ^ (2 * δ + Clev) * Θ N) ^ (2 * p) :=
      pow_le_pow_left₀ (by positivity) h2θ _
    refine h1.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (2 * δ + Clev)) (2 * p),
      ← Real.rpow_mul hN0.le]
    congr 2
    push_cast
    ring
  have htail : M * (N : ℝ) ^ (-Dd) ≤ Θ N ^ (2 * p) := by
    have hpow : (0 : ℝ) < (N : ℝ) ^ (-Dd) := Real.rpow_pos_of_pos hN0 _
    have hQ : (0 : ℝ) < Θ N ^ (2 * p) := by positivity
    have hcollapse : (N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * (N : ℝ) ^ (-Dd)
        = (N : ℝ) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hN0, hDd]; congr 1; ring
    have hinv : (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hN0.le, Real.rpow_one, inv_le_one_iff₀]
      right; linarith
    calc M * (N : ℝ) ^ (-Dd)
        ≤ ((N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * Θ N ^ (2 * p)) * (N : ℝ) ^ (-Dd) :=
          mul_le_mul_of_nonneg_right hMle hpow.le
      _ = ((N : ℝ) ^ ((2 * δ + Clev) * (2 * p)) * (N : ℝ) ^ (-Dd)) * Θ N ^ (2 * p) := by ring
      _ = (N : ℝ) ^ (-(1 : ℝ)) * Θ N ^ (2 * p) := by rw [hcollapse]
      _ ≤ 1 * Θ N ^ (2 * p) := mul_le_mul_of_nonneg_right hinv hQ.le
      _ = Θ N ^ (2 * p) := one_mul _
  -- the bound on the good part
  have hgoodbd : ∀ ω ∈ Bᶜ,
      |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p)
        ≤ (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) := by
    intro ω hω
    have hnb : ω ∉ Bad := fun h => hω (hBsub h)
    have hJle : J N ws ω ≤ (N : ℝ) ^ (ε / 2) * Θ N := by
      by_contra hcon
      exact hnb ⟨⟨ws, hwsIcc⟩, not_le.1 hcon⟩
    have hc0 : (0 : ℝ) ≤ cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) :=
      cutTrunc_nonneg (hJ0 N ws ω)
    have hcle : cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω) ≤ (N : ℝ) ^ (ε / 2) * Θ N :=
      (cutTrunc_le_self (hJ0 N ws ω)).trans hJle
    rw [abs_of_nonneg hc0]
    have hexp : ((N : ℝ) ^ (ε / 2) * Θ N) ^ (2 * p) = (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)) (2 * p), ← Real.rpow_mul hN0.le]
      congr 2
      push_cast
      ring
    rw [← hexp]
    exact pow_le_pow_left₀ hc0 hcle _
  have hsplit : ∫ ω, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
      = (∫ ω in B, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P)
        + ∫ ω in Bᶜ, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P :=
    (integral_add_compl hBmeas hint).symm
  have houter : ∫ ω in B, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
      ≤ P.real B * M := by
    have h1 : ∫ ω in B, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ ∫ _ω in B, M ∂P := by
      refine integral_mono hint.restrict (integrable_const M) fun ω => ?_
      dsimp only
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ0 (hJ0 N ws ω)) _
    simpa [MeasureTheory.setIntegral_const, smul_eq_mul] using h1
  have hinner : ∫ ω in Bᶜ, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
      ≤ (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) := by
    have h1 : ∫ ω in Bᶜ, |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ ∫ _ω in Bᶜ, (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) ∂P := by
      refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
      · exact Filter.Eventually.of_forall fun ω => by positivity
      · filter_upwards [self_mem_ae_restrict hBmeas.compl] with ω hω using hgoodbd ω hω
    have h2 : ∫ _ω in Bᶜ, (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) ∂P
        = P.real Bᶜ * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)) := by
      simp [smul_eq_mul]
    rw [h2] at h1
    refine h1.trans ?_
    have hb : (0 : ℝ) ≤ (N : ℝ) ^ (ε * p) * Θ N ^ (2 * p) := by positivity
    nlinarith [measureReal_le_one (μ := P) (s := Bᶜ), measureReal_nonneg (μ := P) (s := Bᶜ)]
  have hPreal : P.real B ≤ (N : ℝ) ^ (-Dd) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hBmeasure
  have hfin : P.real B * M ≤ Θ N ^ (2 * p) := by
    calc P.real B * M ≤ (N : ℝ) ^ (-Dd) * M := mul_le_mul_of_nonneg_right hPreal hM0
      _ = M * (N : ℝ) ^ (-Dd) := by ring
      _ ≤ Θ N ^ (2 * p) := htail
  have hεp : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1 (by positivity)
  have hQ0 : (0 : ℝ) < Θ N ^ (2 * p) := by positivity
  rw [hsplit]
  nlinarith [houter, hinner, hfin]

/-- For the first pass the truncation level *is* the control, so `levpoly` holds with
`Clev = 1`: the field is not an extra assumption there. -/
theorem levpoly_const {mesh : ℕ → ℝ} (hΘ0 : ∀ N, 0 < Θ N) :
    ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      2 * (fun (N : ℕ) (_ : ℝ) => Θ N) N ws ≤ (N : ℝ) ^ (1 : ℝ) * Θ N := by
  filter_upwards [eventually_ge_atTop 2] with N hN2 ws _
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have := hΘ0 N
  rw [Real.rpow_one]
  nlinarith

/-- **⭐ The generalized interface, from the conditional one.**

`CutHyp'.moment` — unconditional and uniform in `ε` — is produced from
`CutHypCond.condMoment` — conditional and at the single loss `N^{δ/2·p}` — by going round
through the conclusion: `stochDom_of_condMoment` (the stepwise bootstrap) and then
`moment_of_stochDom`. -/
noncomputable def cutHyp'_of_condMoment [IsProbabilityMeasure P] (H : CutHypCond P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    CutHyp' P J s t lev Θ where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  lev_ge := H.lev_ge
  J_nonneg := H.J_nonneg
  meas := H.meas
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := H.modulus
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  moment := fun δ hδ0 _ ε hε p =>
    moment_of_stochDom H.J_nonneg H.meas H.Θ_pos H.Clev_nonneg H.window H.mesh_pos
      (fun N _ws hws => H.lev_pos_net N hws) H.levpoly
      (stochDom_of_condMoment H hΘ1 hinit) δ hδ0 ε hε p

/-- **`RBM.MomentDuhamelCut.CutHyp` itself, from the conditional interface.**  This is the
statement T210 left open: the frozen, unconditional interface is produced from data a Duhamel
computation can supply. -/
noncomputable def cutHyp_of_condMoment [IsProbabilityMeasure P] (H : CutHypCond P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    CutHyp P J s t Θ :=
  cutHyp_of_cutHyp' (cutHyp'_of_condMoment H hΘ1 hinit)

end Cond

/-! ### 9′. The two named hypotheses of Step 2, discharged -/

section NamedHyps

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **⭐ `RBM.MomentDuhamelCut.MomentHypCut` — the blunt (first) pass — from the conditional
interface.**

T197 left `MomentHypCut.cut` as a named hypothesis and T210 showed it cannot be produced
directly from a Duhamel computation, because it is unconditional.  It is produced here from
`CutHypCond`, whose only non-deterministic field is the **conditional** moment bound on the
prefix event — exactly what §5.3 computes. -/
noncomputable def momentHypCut_of_condMoment {X : Sample B} {D : ℝ}
    (H : CutHypCond B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    MomentHypCut X E s t D :=
  letI := B.isProbabilityMeasure
  { cut := cutHyp_of_condMoment H (Filter.Eventually.of_forall fun _ => le_rfl) hinit
    init := hinit }

/-- **⭐ `MomentHypCut2` — the sharp (second) pass — from the conditional interface.**

The truncation level is the *blunt* one, `(η_s/η_u)²` read in the sharp normalization, so the
prefix event the Duhamel conditions on is exactly the level the first pass establishes.  The
initial condition is the same (2.69) as the first pass (`RBM.Step2Near47.jSnorm2_left`). -/
noncomputable def momentHypCut2_of_condMoment {X : Sample B} {D : ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    (H : CutHypCond B.P (fun N u ω => Step2Near47.jSnorm2 X E D s N u ω) s t (levSharp E s)
      (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    MomentHypCut2 X E s t D :=
  letI := B.isProbabilityMeasure
  { cut := cutHyp'_of_condMoment H (Filter.Eventually.of_forall fun _ => le_rfl) (by
      have hfun : (fun N (_ : Unit) (ω : Ω) => Step2Near47.jSnorm2 X E D s N (s N) ω)
          = fun N (_ : Unit) (ω : Ω) => Step2Moment.jSnorm X E D s N (s N) ω := by
        funext N _ ω
        exact Step2Near47.jSnorm2_left X hE ((H.window N).trans_lt (ht1 N)) ω
      rw [hfun]
      exact hinit) }

/-- **End to end: (5.47) sharp from the conditional interfaces alone.**

`J*_{u,D} ≺ (η_s/η_u)²`, uniformly on the window, with **no** named moment hypothesis left:
both passes are supplied by `CutHypCond`, whose content is the conditional truncated Duhamel
moment bound on the prefix event. -/
theorem jS_stochDom_sharp_of_condMoment {X : Sample B} {D : ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    (H1 : CutHypCond B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (H2 : CutHypCond B.P (fun N u ω => Step2Near47.jSnorm2 X E D s N u ω) s t (levSharp E s)
      (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2) :=
  jS_stochDom_sharp_of_cut2_of_momentHypCut (momentHypCut2_of_condMoment hE ht1 H2 hinit)
    (momentHypCut_of_condMoment H1 hinit) hE ht1

/-- **(5.47) blunt, end to end** — `J*_{u,D} ≺ (η_s/η_u)^4` from the conditional interface. -/
theorem jS_stochDom_of_condMoment {X : Sample B} {D : ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (H1 : CutHypCond B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 4) :=
  MomentDuhamelCut.jS_stochDom_cut (momentHypCut_of_condMoment H1 hinit) hE hst ht1

end NamedHyps

/-! ### 11. Satisfiability of the conditional interface (compiled) -/

section SatCond

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On the window the witness's level is at most `N + 2`: `levpoly` is satisfiable with
`Clev = 3`.  (`satLev N u = (1-u)⁻¹` and the window stops at `1 - (N+2)⁻¹`.) -/
theorem satLev_le {N : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (satT N)) :
    satLev N u ≤ (N : ℝ) + 2 := by
  have hlt : u < 1 := lt_of_le_of_lt hu.2 (satT_lt_one N)
  have h1 : (0 : ℝ) < 1 - u := by linarith
  have h0 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hge : ((N : ℝ) + 2)⁻¹ ≤ 1 - u := by
    have := hu.2
    simp only [satT] at this
    linarith
  have hmul := mul_le_mul_of_nonneg_left hge h0.le
  rw [mul_inv_cancel₀ h0.ne'] at hmul
  simp only [satLev, ← one_div]
  rw [div_le_iff₀ h1]
  linarith

/-- **A compiled `CutHypCond` at the critical scale `J ≡ Θ ≡ 1`.**

The same witness as `satCutHyp'` — critical scale, `u`-dependent and unbounded level, the
opposing pair `mesh_fine`/`card_le` met by one set of parameters — now carrying the *new*
fields `Clev`/`levpoly` and, most importantly, `condMoment`.

The prefix event here is literally `Set.univ` (`sat_prefixEvent_eq_univ`), so `condMoment` is
**not** vacuously true by conditioning on an empty event: the integral it constrains is the
full integral.  That is the failure mode item (d) of the ticket warns about, and
`prefixEvent_ne_univ` shows the notion does restrict in general. -/
noncomputable def satCutHypCond (P : Measure Ω) [IsProbabilityMeasure P] :
    CutHypCond P (fun _ _ _ => (1 : ℝ)) (fun _ => 0) satT satLev (fun _ => 1) where
  window := (satCutHyp' P).window
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  lev_ge := fun _ _ hu => one_le_satLev hu
  J_nonneg := fun _ _ _ => zero_le_one
  meas := fun _ _ => aestronglyMeasurable_const
  mesh := satMesh
  mesh_pos := satMesh_pos
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := (satCutHyp' P).modulus
  mesh_fine := (satCutHyp' P).mesh_fine
  Ccard := 3
  card_le := (satCutHyp' P).card_le
  Clev := 3
  Clev_nonneg := by norm_num
  levpoly := by
    filter_upwards [eventually_ge_atTop 4] with N hN ws hws
    have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hwsIcc : ws ∈ Set.Icc (0 : ℝ) (satT N) :=
      netFinset_subset_Icc (satT_nonneg N) (satMesh_pos N) ws hws
    have hle := satLev_le hwsIcc
    have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast (N : ℝ) 3]; norm_num
    rw [h3, mul_one]
    have hsq : (16 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hcube : (16 : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
    nlinarith
  condMoment := by
    intro δ hδ0 _ p
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN ws hws
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hwsIcc : ws ∈ Set.Icc (0 : ℝ) (satT N) :=
      netFinset_subset_Icc (satT_nonneg N) (satMesh_pos N) ws hws
    have hlev := one_le_satLev hwsIcc
    have hrp : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hN1 (by positivity)
    have hlv : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * satLev N ws := by nlinarith
    have hlv0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * satLev N ws := by linarith
    have hδp : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2 * p) := Real.one_le_rpow hN1 (by positivity)
    have hcut : cutTrunc ((N : ℝ) ^ (2 * δ) * satLev N ws) 1 = 1 := cutTrunc_eq_self hlv0 hlv
    simp only [hcut, abs_one, one_pow, one_mul, mul_one]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact le_trans measureReal_le_one hδp

/-- **The prefix event of the witness is everything** — in particular non-empty and of
probability one, so `satCutHypCond.condMoment` constrains a genuine integral. -/
theorem sat_prefixEvent_eq_univ {Ω' : Type*} {δ : ℝ} {N : ℕ} (hN : 1 ≤ (N : ℝ)) {ws : ℝ}
    (hδ : 0 < δ) (hws : ws ∈ Set.Icc (0 : ℝ) (satT N)) :
    prefixEvent (fun _ _ (_ : Ω') => (1 : ℝ)) (fun _ => (0 : ℝ))
      (fun N u => (N : ℝ) ^ (2 * δ) * satLev N u) N ws = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  intro u hu
  have huIcc : u ∈ Set.Icc (0 : ℝ) (satT N) := ⟨hu.1, hu.2.trans hws.2⟩
  have hlev := one_le_satLev huIcc
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hN (by positivity)
  nlinarith

/-- **The prefix event does restrict, in general.**  A two-point sample space, one path above
the level and one below: the event is neither empty (so `condMoment` is not vacuous) nor
everything (so conditioning is not a no-op).  Without both halves the interface would be
uninformative. -/
theorem prefixEvent_ne_univ :
    prefixEvent (fun (_ : ℕ) (_ : ℝ) (ω : Bool) => if ω then (2 : ℝ) else 0)
        (fun _ => (0 : ℝ)) (fun _ _ => (1 : ℝ)) 0 0 = {false} := by
  ext ω
  cases ω <;> simp [prefixEvent]

/-- **The stepwise bootstrap runs on the witness**: `netGood_highProb` applied to
`satCutHypCond` gives a genuine `RBM.HighProb` statement, so the induction's start and step
are jointly satisfiable — the failure mode item (a) of the ticket warns about. -/
theorem sat_netGood_highProb (P : Measure Ω) [IsProbabilityMeasure P] {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1) :
    HighProb P fun N => {_ω : Ω | ∀ ws ∈ (↑(netFinset (fun _ => (0 : ℝ)) satT satMesh N) : Set ℝ),
      (1 : ℝ) ≤ ((N : ℝ) ^ δ - 1) * 1} :=
  netGood_highProb (satCutHypCond P) (Filter.Eventually.of_forall fun _ => le_rfl)
    (MomentDuhamelCut.sat_init P) hδ0 hδ

/-- **The whole machine on the witness**: conditional moment ⟹ `≺`.  Compare
`sat_stochDom_of_cutHyp'`, which needed the *unconditional* moment field. -/
theorem sat_stochDom_of_condMoment (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (_ : TimeIcc (fun _ => (0 : ℝ)) satT N) (_ : Ω) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_condMoment (satCutHypCond P) (Filter.Eventually.of_forall fun _ => le_rfl)
    (MomentDuhamelCut.sat_init P)

/-- **And the unconditional interface comes back out.**  `cutHyp_of_condMoment` on the witness
produces a `RBM.MomentDuhamelCut.CutHyp`, i.e. the frozen interface, from conditional data
only. -/
noncomputable def satCutHyp_of_condMoment (P : Measure Ω) [IsProbabilityMeasure P] :
    CutHyp P (fun _ _ _ => (1 : ℝ)) (fun _ => 0) satT (fun _ => 1) :=
  cutHyp_of_condMoment (satCutHypCond P) (Filter.Eventually.of_forall fun _ => le_rfl)
    (MomentDuhamelCut.sat_init P)

/-- **The degenerate window `s = t` does not break the walk**: the net is the single point
`{s_N}`, i.e. index `0` only, so only the initial step of `netGood_highProb` fires. -/
theorem sat_cutNetTop_collapse (a m : ℕ → ℝ) (N : ℕ) :
    cutNetTop a a m N = 0 := by
  simp only [cutNetTop, sub_self, zero_mul, Nat.floor_zero]

end SatCond

/-! ### 12. The one-step arithmetic, wired to `condMoment` (T222)

`RBM.Step2MomentStep.phi_arith'`, `RBM.Step2Near47.phi_arith_second_pass` and
`RBM.Step2MomentStep.integral_nearInt_le` — the accounting layer of (5.39)–(5.44) — had **no
consumer anywhere in the repository** (T207's audit).  What they were waiting for is
`CutHypCond.condMoment`, and this section connects them.

The connection is an *exponent* statement, and it is what makes `condMoment`'s shape
non-arbitrary.  The one-step output is `cStep' m · x² R⁴` with `x = N^{δ/8}` and `R = η_s/η_v`,
and the interface's functional is the **normalized** `RBM.Step2Moment.jSnorm`, i.e. `J*/R⁴`.
Dividing, the normalized one-step bound is `cStep' m · x²`, so its `2p`-th moment is

`(cStep' m)^{2p} · (x²)^{2p} = (cStep' m)^{2p} · N^{δ/2·p}`,

which is `condMoment` **to the letter** (`rpow_sq_pow` is an equality, not an inequality).  Had
the field been written with a smaller loss than `N^{δ/2·p}` it would have been unsatisfiable
by the actual arithmetic; with a larger one the bootstrap would not close against the
threshold `Λ = x⁸R⁴` (`RBM.Step2MomentStep.phi_lt_threshold` needs `cStep' m ≤ x⁶`).

The second pass is the same statement with `cSharp` and the sharp normalization `J*/R²`
(`RBM.Step2Near47.jSnorm2`), which is why it costs a different *constant* and not a different
exponent — the interface-level form of "no second bootstrap is needed".
-/

section Accounting

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- The left-hand side of `RBM.Step2MomentStep.phi_arith'`, verbatim: the seven terms of
(5.39)–(5.44) after the (2.73) reduction, for the **unnormalized** `J*`. -/
noncomputable def stepRhs (m x R Ξ A ε q β γ Jv : ℝ) : ℝ :=
  x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
    + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1

/-- The left-hand side of `RBM.Step2Near47.phi_arith_second_pass`, verbatim: the near field of
(5.41) enters as the *integrated* `qI` rather than through the coefficient `q`. -/
noncomputable def stepRhsSharp (m x R Ξ A ε qI β γ Jv : ℝ) : ℝ :=
  x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
    + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) + x * (R ^ 2 + 1) + 1

/-- The side conditions of `RBM.Step2MomentStep.phi_arith'`, verbatim. -/
structure StepSide (x R Ξ A ε q β γ Jv : ℝ) : Prop where
  /-- `R = η_s/η_v ≥ 1` on the window. -/
  R_ge : 1 ≤ R
  /-- (5.35)'s loss is a single `≺`-power. -/
  Ξ_nonneg : 0 ≤ Ξ
  /-- ditto. -/
  Ξ_le : Ξ ≤ x
  /-- the threshold `A_u` of (5.42). -/
  A_ge : x ^ 17 * R ^ 10 ≤ A
  /-- the far-field remainder of (5.40). -/
  ε_nonneg : 0 ≤ ε
  /-- ditto. -/
  ε_le : ε * x ^ 17 * R ^ 10 ≤ 1
  /-- the near-field coefficient `(ℓ_u/ℓ_s)³` of (5.41). -/
  q_nonneg : 0 ≤ q
  /-- its cap, `R²` after the (2.73) reduction. -/
  q_le : q ≤ R ^ 2
  /-- the linear far-field coefficient `r^{3/2}A^{-1/2}`. -/
  β_nonneg : 0 ≤ β
  /-- ditto. -/
  β_le : β * (x ^ 8 * R ^ 2) ≤ 1
  /-- the `3/2`-power far-field coefficient `r A⁻¹`. -/
  γ_nonneg : 0 ≤ γ
  /-- ditto. -/
  γ_le : γ * (x ^ 12 * R ^ 4) ≤ 1
  /-- the a priori level `Λ = x⁸R⁴` of (5.43). -/
  Jv_nonneg : 0 ≤ Jv
  /-- ditto. -/
  Jv_le : Jv ≤ x ^ 8 * R ^ 4

/-- The side conditions of `RBM.Step2Near47.phi_arith_second_pass`, verbatim.  Only the
near-field slot and the two far-field conditions differ from `StepSide`. -/
structure StepSideSharp (m x R Ξ A ε qI β γ Jv : ℝ) : Prop where
  /-- as in `StepSide`. -/
  R_ge : 1 ≤ R
  /-- as in `StepSide`. -/
  Ξ_nonneg : 0 ≤ Ξ
  /-- as in `StepSide`. -/
  Ξ_le : Ξ ≤ x
  /-- as in `StepSide`. -/
  A_ge : x ^ 17 * R ^ 10 ≤ A
  /-- as in `StepSide`. -/
  ε_nonneg : 0 ≤ ε
  /-- as in `StepSide`. -/
  ε_le : ε * x ^ 17 * R ^ 10 ≤ 1
  /-- the **integrated** near field of (5.44). -/
  qI_nonneg : 0 ≤ qI
  /-- its budget `2 m⁻¹ R²`, which `integral_nearInt_le` meets exactly. -/
  qI_le : qI ≤ 2 * m⁻¹ * R ^ 2
  /-- as in `StepSide`, one power of `R` weaker (`β* = 9.5`). -/
  β_nonneg : 0 ≤ β
  /-- ditto. -/
  β_le : β * (x ^ 8 * R ^ 4) ≤ 1
  /-- as in `StepSide`, one power of `R` weaker (`β* = 6.5`). -/
  γ_nonneg : 0 ≤ γ
  /-- ditto. -/
  γ_le : γ * (x ^ 12 * R ^ 6) ≤ 1
  /-- as in `StepSide`. -/
  Jv_nonneg : 0 ≤ Jv
  /-- ditto. -/
  Jv_le : Jv ≤ x ^ 8 * R ^ 4

/-- **`phi_arith'`, packaged.** -/
theorem stepRhs_le {m x R Ξ A ε q β γ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide x R Ξ A ε q β γ Jv) :
    stepRhs m x R Ξ A ε q β γ Jv ≤ Step2MomentStep.cStep' m * x ^ 2 * R ^ 4 :=
  Step2MomentStep.phi_arith' hx H.R_ge H.Ξ_nonneg H.Ξ_le hm H.A_ge H.ε_nonneg H.ε_le
    H.q_nonneg H.q_le H.β_nonneg H.β_le H.γ_nonneg H.γ_le H.Jv_nonneg H.Jv_le

/-- **`phi_arith_second_pass`, packaged.** -/
theorem stepRhsSharp_le {m x R Ξ A ε qI β γ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSideSharp m x R Ξ A ε qI β γ Jv) :
    stepRhsSharp m x R Ξ A ε qI β γ Jv ≤ Step2Near47.cSharp m * x ^ 2 * R ^ 2 :=
  Step2Near47.phi_arith_second_pass hx H.R_ge H.Ξ_nonneg H.Ξ_le hm H.A_ge H.ε_nonneg H.ε_le
    H.qI_nonneg H.qI_le H.β_nonneg H.β_le H.γ_nonneg H.γ_le H.Jv_nonneg H.Jv_le

/-- **In the blunt normalization `J*/R⁴`** (`RBM.Step2Moment.jSnorm`) the one-step output is
`cStep' m · x²`, with no `R` left — which is why the interface's control is the *constant*
`Θ ≡ 1`. -/
theorem stepRhs_div_le {m x R Ξ A ε q β γ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide x R Ξ A ε q β γ Jv) :
    stepRhs m x R Ξ A ε q β γ Jv / R ^ 4 ≤ Step2MomentStep.cStep' m * x ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith [H.R_ge]
  have hR0 : (0 : ℝ) < R ^ 4 := by positivity
  rw [div_le_iff₀ hR0]
  exact stepRhs_le hx hm H

/-- **In the sharp normalization `J*/R²`** (`RBM.Step2Near47.jSnorm2`) the second-pass output
is `cSharp m · x²` — the same exponent as the blunt pass, a larger constant. -/
theorem stepRhsSharp_div_le {m x R Ξ A ε qI β γ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSideSharp m x R Ξ A ε qI β γ Jv) :
    stepRhsSharp m x R Ξ A ε qI β γ Jv / R ^ 2 ≤ Step2Near47.cSharp m * x ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith [H.R_ge]
  have hR0 : (0 : ℝ) < R ^ 2 := by positivity
  rw [div_le_iff₀ hR0]
  exact stepRhsSharp_le hx hm H

/-- The one-step right-hand side is at least its own constant term `1`; in particular it is
nonnegative, so it can be raised to the `2p`-th power monotonically. -/
theorem one_le_stepRhs {m x R Ξ A ε q β γ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide x R Ξ A ε q β γ Jv) : 1 ≤ stepRhs m x R Ξ A ε q β γ Jv := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith [H.R_ge]
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) H.A_ge
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hAi : (0 : ℝ) < A⁻¹ := inv_pos.2 hA0
  have hin : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε := by
    have h36 : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ := by positivity
    have hεR : (0 : ℝ) ≤ R ^ 2 * ε := mul_nonneg (by positivity) H.ε_nonneg
    linarith
  have hT1 : (0 : ℝ) ≤ exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) :=
    mul_nonneg (by positivity) hin
  have hT2 : (0 : ℝ) ≤ x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv)) := by
    refine mul_nonneg (by positivity) ?_
    have h3 : (0 : ℝ) ≤ β * Jv := mul_nonneg H.β_nonneg H.Jv_nonneg
    have h4 : (0 : ℝ) ≤ γ * (Jv * √Jv) :=
      mul_nonneg H.γ_nonneg (mul_nonneg H.Jv_nonneg (Real.sqrt_nonneg _))
    linarith [H.q_nonneg]
  have h7 : (0 : ℝ) ≤ x * R ^ 2 * Ξ := mul_nonneg (by positivity) H.Ξ_nonneg
  have h8 : (0 : ℝ) ≤ Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) :=
    mul_nonneg H.Ξ_nonneg (by linarith)
  have h9 : (0 : ℝ) ≤ x * (R ^ 2 + 1) := by positivity
  unfold stepRhs
  linarith

/-- Same for the sharp shape. -/
theorem one_le_stepRhsSharp {m x R Ξ A ε qI β γ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSideSharp m x R Ξ A ε qI β γ Jv) : 1 ≤ stepRhsSharp m x R Ξ A ε qI β γ Jv := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith [H.R_ge]
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) H.A_ge
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hAi : (0 : ℝ) < A⁻¹ := inv_pos.2 hA0
  have hin : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε := by
    have h36 : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ := by positivity
    have hεR : (0 : ℝ) ≤ R ^ 2 * ε := mul_nonneg (by positivity) H.ε_nonneg
    linarith
  have hT1 : (0 : ℝ) ≤ exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) :=
    mul_nonneg (by positivity) hin
  have hTq : (0 : ℝ) ≤ x * qI := mul_nonneg hx0.le H.qI_nonneg
  have hT2 : (0 : ℝ) ≤ x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv)) := by
    refine mul_nonneg (by positivity) ?_
    have h3 : (0 : ℝ) ≤ β * Jv := mul_nonneg H.β_nonneg H.Jv_nonneg
    have h4 : (0 : ℝ) ≤ γ * (Jv * √Jv) :=
      mul_nonneg H.γ_nonneg (mul_nonneg H.Jv_nonneg (Real.sqrt_nonneg _))
    linarith
  have h7 : (0 : ℝ) ≤ x * R ^ 2 * Ξ := mul_nonneg (by positivity) H.Ξ_nonneg
  have h8 : (0 : ℝ) ≤ Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * qI + x * m⁻¹ * R ^ 2 * (β * Jv + γ * (Jv * √Jv))) :=
    mul_nonneg H.Ξ_nonneg (by linarith)
  have h9 : (0 : ℝ) ≤ x * (R ^ 2 + 1) := by positivity
  unfold stepRhsSharp
  linarith

/-- **The exponent identity the interface rests on**: `(x²)^{2p} = N^{δ/2·p}` for
`x = N^{δ/8}`.  An equality — `condMoment`'s loss is *exactly* the one-step output, neither
rounded up nor down. -/
theorem rpow_sq_pow {δ : ℝ} {N : ℕ} (hN : 1 ≤ (N : ℝ)) (p : ℕ) :
    (((N : ℝ) ^ (δ / 8)) ^ 2) ^ (2 * p) = (N : ℝ) ^ (δ / 2 * p) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [← Real.rpow_natCast (((N : ℝ) ^ (δ / 8)) ^ 2) (2 * p),
    ← Real.rpow_natCast ((N : ℝ) ^ (δ / 8)) 2, ← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le]
  congr 1
  push_cast
  ring

/-- **The bridge**: a one-step bound of the form `(c₀ x²)^{2p}` with `x = N^{δ/8}` *is* the
`condMoment` field of `CutHypCond`, with the honest constant `C = c₀^{2p}`. -/
theorem condMoment_of_sq_bound {mesh : ℕ → ℝ} {δ c₀ : ℝ} (hc₀ : 0 < c₀) (hΘ : ∀ N, Θ N = 1)
    (p : ℕ)
    (h : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ (c₀ * ((N : ℝ) ^ (δ / 8)) ^ 2) ^ (2 * p)) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p)) := by
  refine ⟨c₀ ^ (2 * p), pow_pos hc₀ _, ?_⟩
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1 ws hws
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  refine (hN ws hws).trans (le_of_eq ?_)
  rw [mul_pow, rpow_sq_pow hNR p, hΘ N, one_pow, mul_one]

/-- **⭐ `condMoment` from the blunt one-step arithmetic.**

The hypothesis is the *conditional* truncated Duhamel output of §5.3 — the moment of the
truncated functional on the prefix event, bounded by the seven terms of (5.39)–(5.44) read in
the blunt normalization `J*/R⁴`.  The conclusion is the `condMoment` field of `CutHypCond` to
the letter, with `C = (cStep' m)^{2p}`.

This is where `RBM.Step2MomentStep.phi_arith'` is used; it had no consumer before. -/
theorem condMoment_of_oneStep {mesh : ℕ → ℝ} {δ m : ℝ} (hδ0 : 0 ≤ δ) (hm : 0 < m)
    (hΘ : ∀ N, Θ N = 1) (p : ℕ)
    (h : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N, ∃ R Ξ A ε q β γ Jv : ℝ,
      StepSide ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ Jv ∧
        ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
          |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
          ≤ (stepRhs m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ Jv / R ^ 4) ^ (2 * p)) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p)) := by
  refine condMoment_of_sq_bound (Step2MomentStep.cStep'_pos hm) hΘ p ?_
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1 ws hws
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  obtain ⟨R, Ξ, A, ε, q, β, γ, Jv, hside, hmom⟩ := hN ws hws
  have hR0 : (0 : ℝ) < R ^ 4 := by
    have : (0 : ℝ) < R := by linarith [hside.R_ge]
    positivity
  have h0 : (0 : ℝ) ≤ stepRhs m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ Jv / R ^ 4 :=
    div_nonneg (le_trans zero_le_one (one_le_stepRhs hx hm hside)) hR0.le
  exact hmom.trans (pow_le_pow_left₀ h0 (stepRhs_div_le hx hm hside) _)

/-- **⭐ `condMoment` from the sharp one-step arithmetic** (`phi_arith_second_pass`), for the
second pass, in the sharp normalization `J*/R²` and with `C = (cSharp m)^{2p}`.  Same loss
exponent as the blunt pass — which is the interface-level reason `MomentHypCut2` needs no
second bootstrap. -/
theorem condMoment_of_oneStepSharp {mesh : ℕ → ℝ} {δ m : ℝ} (hδ0 : 0 ≤ δ) (hm : 0 < m)
    (hΘ : ∀ N, Θ N = 1) (p : ℕ)
    (h : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N, ∃ R Ξ A ε qI β γ Jv : ℝ,
      StepSideSharp m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ Jv ∧
        ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
          |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
          ≤ (stepRhsSharp m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ Jv / R ^ 2) ^ (2 * p)) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
      ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p)) := by
  refine condMoment_of_sq_bound (Step2Near47.cSharp_pos hm) hΘ p ?_
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1 ws hws
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  obtain ⟨R, Ξ, A, ε, qI, β, γ, Jv, hside, hmom⟩ := hN ws hws
  have hR0 : (0 : ℝ) < R ^ 2 := by
    have : (0 : ℝ) < R := by linarith [hside.R_ge]
    positivity
  have h0 : (0 : ℝ) ≤ stepRhsSharp m ((N : ℝ) ^ (δ / 8)) R Ξ A ε qI β γ Jv / R ^ 2 :=
    div_nonneg (le_trans zero_le_one (one_le_stepRhsSharp hx hm hside)) hR0.le
  exact hmom.trans (pow_le_pow_left₀ h0 (stepRhsSharp_div_le hx hm hside) _)

/-- **(5.44)'s integrated near field fills the `qI`-slot of `phi_arith_second_pass`, and the
`q`-slot of `phi_arith'`, exactly at the cap.**

`RBM.Step2MomentStep.integral_nearInt_le` gives
`∫_s^v η_u^{-1}(η_u/η_v)^4(η_s/η_u)^{5/2} du ≤ (Im m_E)^{-1}(η_s/η_v)^4`, and the near-field
summand of `phi_arith'` is `x m⁻¹ R² q` with the cap `q ≤ R²`.  So the slot is filled at
`q = R²` — **zero margin**, which is why T207's "bound the three factors separately" variant
(`RBM.Step2Near47.crude_exceeds_budget`) overshoots by `R^{5/2}`.

This is where `RBM.Step2MomentStep.integral_nearInt_le` is used; it had no consumer before. -/
theorem nearInt_fills_q_slot {E : ℝ} (hE : |E| < 2) {a v x : ℝ} (hav : a ≤ v) (hv1 : v < 1)
    (hx : 0 ≤ x) :
    ∃ q, 0 ≤ q ∧ q ≤ (etaT E a / etaT E v) ^ 2
      ∧ x * (∫ u in a..v, Step2MomentStep.nearInt E a v u)
          ≤ x * ((mE E).im)⁻¹ * (etaT E a / etaT E v) ^ 2 * q := by
  have hs1 : a < 1 := hav.trans_lt hv1
  have ha : 0 < etaT E a := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  refine ⟨(etaT E a / etaT E v) ^ 2, by positivity, le_rfl, ?_⟩
  have hint := Step2MomentStep.integral_nearInt_le hE hav hv1
  have heq : ((mE E).im)⁻¹ * (etaT E a / etaT E v) ^ 4
      = ((mE E).im)⁻¹ * (etaT E a / etaT E v) ^ 2 * (etaT E a / etaT E v) ^ 2 := by ring
  rw [heq] at hint
  calc x * (∫ u in a..v, Step2MomentStep.nearInt E a v u)
      ≤ x * (((mE E).im)⁻¹ * (etaT E a / etaT E v) ^ 2 * (etaT E a / etaT E v) ^ 2) :=
        mul_le_mul_of_nonneg_left hint hx
    _ = x * ((mE E).im)⁻¹ * (etaT E a / etaT E v) ^ 2 * (etaT E a / etaT E v) ^ 2 := by ring

/-- The side conditions of the one-step arithmetic are **jointly satisfiable** at every
`x ≥ 1` — with `Ξ` and `q` at their caps, so the witness is not the degenerate all-zero
point. -/
theorem sat_StepSide {x : ℝ} (hx : 1 ≤ x) : StepSide x 1 x (x ^ 17) 0 1 0 0 0 where
  R_ge := le_rfl
  Ξ_nonneg := by linarith
  Ξ_le := le_rfl
  A_ge := by norm_num
  ε_nonneg := le_rfl
  ε_le := by norm_num
  q_nonneg := zero_le_one
  q_le := by norm_num
  β_nonneg := le_rfl
  β_le := by norm_num
  γ_nonneg := le_rfl
  γ_le := by norm_num
  Jv_nonneg := le_rfl
  Jv_le := by positivity

end Accounting

/-! ### 13. Why the moment field has to be **conditional** (T222)

§9's `CutHypCond.condMoment` restricts the integral to the prefix event.  One would rather
have the *unconditional* integral with the prefix only as a high-probability **premise** —
that is the shape a Gaussian integration by parts can produce, since Stein's identity holds
against the full measure and not against a restriction of it.  **That shape does not close the
stepwise bootstrap, and it fails by a factor, not by a constant.**

Write `M` for the target `N^{δ/2·p}Θ^{2p}`, `c` for the threshold of the bad event at the net
points, `θ` for the truncation level and `C` for the moment constant.  Then

* what a step **delivers** is Chebyshev: `P(J_{w_k} > c) ≤ C·M/c^{2p} =: g`;
* what a step **needs** is that the de-truncation tail fit inside the target,
  `P(prefix fails)·(2θ)^{2p} ≤ M`, i.e. `P(prefix fails) ≤ M/(2θ)^{2p} =: r`;
* and the truncation must not annihilate the bad event, which forces `c < 2θ`
  (`lt_two_mul_of_lt_cutTrunc`: `cutTrunc θ` never exceeds `2θ`).

Those three are incompatible: `c < 2θ` makes `r < M/c^{2p} ≤ g`, so the premise a step needs
is *strictly stronger* than the conclusion it delivers — already before the union bound over
the `N^{Ccard}` net points is paid.  `no_unconditional_stepwise` states this for every
`n`, and it fails at `n = 0` too: the obstruction is the width `2θ` of the cutoff's support,
not the size of the net.

Conditioning, by contrast, pays **no** tail at all, which is why `netGood_highProb` closes.
So `condMoment`'s restricted integral is forced, and what remains open is the §5.3 Duhamel
*on the prefix event*: either integration by parts against the restricted measure, or a
smooth cutoff of the whole path — whose derivative terms are the paper's stopping time.  That
is the one gap this file does not close; see the T222 report.
-/

section NoGo

/-- **The truncation level cannot be below half the threshold.**  If the bad event `{J > c}`
is to survive the truncation at all then `c < 2θ`, because `cutTrunc θ` never exceeds `2θ`.
This is the constraint `netGood_highProb`'s Chebyshev step lives under. -/
theorem lt_two_mul_of_lt_cutTrunc {θ c x : ℝ} (hθ : 0 < θ) (hx : 0 ≤ x)
    (h : c < cutTrunc θ x) : c < 2 * θ :=
  lt_of_lt_of_le h (cutTrunc_le_two_mul hθ hx)

/-- **The de-truncation premise is strictly stronger than the Chebyshev conclusion.** -/
theorem premise_lt_gain {c θ M : ℝ} (hc : 0 < c) (hcθ : c < 2 * θ) (hM : 0 < M)
    {p : ℕ} (hp : 1 ≤ p) :
    M / (2 * θ) ^ (2 * p) < M / c ^ (2 * p) := by
  have h1 : c ^ (2 * p) < (2 * θ) ^ (2 * p) := by
    refine pow_lt_pow_left₀ hcθ hc.le ?_
    omega
  exact div_lt_div_of_pos_left hM (by positivity) h1

/-- **⭐ The unconditional variant of the stepwise bootstrap cannot close.**

`(n+1)·g ≤ r` — the union bound over `n + 1` net points of the Chebyshev output `g`, fitting
inside the premise `r` the next step needs — is **impossible**: for every threshold `c > 0`,
every truncation level `θ` with `c < 2θ` (which `lt_two_mul_of_lt_cutTrunc` forces), every
target `M > 0`, every constant `C ≥ 1` and every `p ≥ 1`.  It already fails at `n = 0`, i.e.
before the net's cardinality is paid. -/
theorem no_unconditional_stepwise {c θ M C : ℝ} (hc : 0 < c) (hcθ : c < 2 * θ) (hM : 0 < M)
    (hC : 1 ≤ C) {p n : ℕ} (hp : 1 ≤ p) :
    ¬ (((n : ℝ) + 1) * (C * M / c ^ (2 * p)) ≤ M / (2 * θ) ^ (2 * p)) := by
  intro h
  have hcp : (0 : ℝ) < c ^ (2 * p) := by positivity
  have hkey : M / (2 * θ) ^ (2 * p) < M / c ^ (2 * p) := premise_lt_gain hc hcθ hM hp
  have hMc : (0 : ℝ) < M / c ^ (2 * p) := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have heq : C * M / c ^ (2 * p) = C * (M / c ^ (2 * p)) := by ring
  rw [heq] at h
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * C := by nlinarith
  have h2 : M / c ^ (2 * p) ≤ ((n : ℝ) + 1) * (C * (M / c ^ (2 * p))) := by
    have hre : ((n : ℝ) + 1) * (C * (M / c ^ (2 * p)))
        = (((n : ℝ) + 1) * C) * (M / c ^ (2 * p)) := by ring
    rw [hre]
    nlinarith
  linarith

/-- The honest constant of the one-step arithmetic is `≥ 1`, so `no_unconditional_stepwise`
applies to it. -/
theorem one_le_cStep'_pow {m : ℝ} (hm : 0 < m) (p : ℕ) :
    (1 : ℝ) ≤ Step2MomentStep.cStep' m ^ (2 * p) := by
  refine one_le_pow₀ ?_
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  unfold Step2MomentStep.cStep'
  nlinarith

/-- **The no-go at the repository's own constant.** -/
theorem no_unconditional_stepwise_phi {c θ M m : ℝ} (hc : 0 < c) (hcθ : c < 2 * θ)
    (hM : 0 < M) (hm : 0 < m) {p n : ℕ} (hp : 1 ≤ p) :
    ¬ (((n : ℝ) + 1) * (Step2MomentStep.cStep' m ^ (2 * p) * M / c ^ (2 * p))
        ≤ M / (2 * θ) ^ (2 * p)) :=
  no_unconditional_stepwise hc hcθ hM (one_le_cStep'_pow hm p) hp

end NoGo

/-! ### 14. The §12 route on the §11 witness (compiled) -/

section SatAccounting

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The one-step hypothesis of `condMoment_of_oneStep` is satisfiable.**

On the §11 witness — critical scale `J ≡ Θ ≡ 1`, level `satLev N u = (1-u)⁻¹` genuinely
`u`-dependent and unbounded (`sat_lev_unbounded`) — the side conditions hold with `Ξ` and `q`
at their caps (`sat_StepSide`, not the degenerate zero), and the conditional integral is
bounded by the constant term `1` that the one-step right-hand side always carries
(`one_le_stepRhs`).  Together with `sat_prefixEvent_measure_one` this rules out both failure
modes: the hypothesis is neither vacuous (the prefix event is all of `Ω`, of probability one)
nor unsatisfiable. -/
theorem sat_oneStep (P : Measure Ω) [IsProbabilityMeasure P] {δ : ℝ} (hδ0 : 0 ≤ δ) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset (fun _ => (0 : ℝ)) satT satMesh N,
      ∃ R Ξ A ε q β γ Jv : ℝ, StepSide ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ Jv ∧
        ∫ _ω in prefixEvent (fun _ _ (_ : Ω) => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun N u => (N : ℝ) ^ (2 * δ) * satLev N u) N ws,
          |cutTrunc ((N : ℝ) ^ (2 * δ) * satLev N ws) (1 : ℝ)| ^ (2 * p) ∂P
          ≤ (stepRhs 1 ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ Jv / R ^ 4) ^ (2 * p) := by
  filter_upwards [eventually_ge_atTop 1] with N hN ws hws
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN1 (by linarith)
  refine ⟨1, (N : ℝ) ^ (δ / 8), ((N : ℝ) ^ (δ / 8)) ^ 17, 0, 1, 0, 0, 0, sat_StepSide hx, ?_⟩
  have hwsIcc : ws ∈ Set.Icc (0 : ℝ) (satT N) :=
    netFinset_subset_Icc (satT_nonneg N) (satMesh_pos N) ws hws
  have hlev := one_le_satLev hwsIcc
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hN1 (by linarith)
  have hlv : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * satLev N ws := by nlinarith
  have hlv0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * satLev N ws := by linarith
  have hcut : cutTrunc ((N : ℝ) ^ (2 * δ) * satLev N ws) 1 = 1 := cutTrunc_eq_self hlv0 hlv
  have hone : (1 : ℝ) ≤ stepRhs 1 ((N : ℝ) ^ (δ / 8)) 1 ((N : ℝ) ^ (δ / 8))
      (((N : ℝ) ^ (δ / 8)) ^ 17) 0 1 0 0 0 := one_le_stepRhs hx one_pos (sat_StepSide hx)
  simp only [hcut, abs_one, one_pow, one_pow, div_one]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  exact le_trans measureReal_le_one (one_le_pow₀ hone)

/-- **⭐ The §11 witness, with its `condMoment` supplied by the one-step arithmetic.**

Nothing is assumed at the moment slot any more: the field is `condMoment_of_oneStep` applied
to `sat_oneStep`, i.e. it comes out of `RBM.Step2MomentStep.phi_arith'`.  Everything §9 and
§9′ build on it therefore runs. -/
noncomputable def satCutHypCond_ofOneStep (P : Measure Ω) [IsProbabilityMeasure P] :
    CutHypCond P (fun _ _ _ => (1 : ℝ)) (fun _ => 0) satT satLev (fun _ => 1) :=
  { satCutHypCond P with
    condMoment := fun _δ hδ _ p =>
      condMoment_of_oneStep (mesh := satMesh) hδ.le one_pos (fun _ => rfl) p
        (sat_oneStep P hδ.le p) }

/-- The stepwise bootstrap runs on it. -/
theorem sat_stochDom_of_condMoment_ofOneStep (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (_ : TimeIcc (fun _ => (0 : ℝ)) satT N) (_ : Ω) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_condMoment (satCutHypCond_ofOneStep P)
    (Filter.Eventually.of_forall fun _ => le_rfl) (MomentDuhamelCut.sat_init P)

/-- And the frozen interface comes back out, with the moment slot discharged by the one-step
arithmetic rather than assumed. -/
noncomputable def satCutHyp_ofOneStep (P : Measure Ω) [IsProbabilityMeasure P] :
    CutHyp P (fun _ _ _ => (1 : ℝ)) (fun _ => 0) satT (fun _ => 1) :=
  cutHyp_of_condMoment (satCutHypCond_ofOneStep P)
    (Filter.Eventually.of_forall fun _ => le_rfl) (MomentDuhamelCut.sat_init P)

/-- **The prefix event of the witness has probability one** — so the conditional bound
`sat_oneStep` feeds to `condMoment_of_oneStep` constrains the *full* integral, and
`satCutHypCond_ofOneStep.condMoment` is not vacuously true by conditioning on a small (let
alone empty) event.  This is failure mode (d) of the T222 ticket, checked;
`prefixEvent_ne_univ` is the other half, that the notion does restrict in general. -/
theorem sat_prefixEvent_measure_one (P : Measure Ω) [IsProbabilityMeasure P] {δ : ℝ}
    (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ (N : ℝ)) {ws : ℝ} (hws : ws ∈ Set.Icc (0 : ℝ) (satT N)) :
    P (prefixEvent (fun _ _ (_ : Ω) => (1 : ℝ)) (fun _ => (0 : ℝ))
        (fun N u => (N : ℝ) ^ (2 * δ) * satLev N u) N ws) = 1 := by
  rw [sat_prefixEvent_eq_univ hN hδ hws, measure_univ]

end SatAccounting

end CutHypTheta

end RBM


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

end CutHypTheta

end RBM

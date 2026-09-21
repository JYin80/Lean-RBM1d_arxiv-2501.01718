/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.StochDom
import RBM1D.Defs.Dist
import RBM1D.Loop.GLoop
import RBM1D.Loop.KBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The random layer as explicit hypotheses (§2.4, §2.6, §2.7)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, pp. 15–25: the stochastic flow
(2.34)–(2.36), the loop estimates of Lemmas 2.18–2.20, Theorem 2.21 with its six steps
(2.73)–(2.80), and the distributional identities (2.39), (2.65), (2.66).

**Nothing here is an `axiom`.**  The Itô calculus is not formalized, so every statement whose
proof needs the random flow is recorded as a *field of a structure*.  Downstream files take such
a structure as a hypothesis; the axiom audit sees only `propext`, `Classical.choice`,
`Quot.sound`.

## Conventions

* **Probability space.**  As in `RBM1D/Defs/StochDom.lean`, the space `(Ω, P)` is fixed and the
  dependence on `N` is carried by the random variables.  `≺` is `RBM.StochDom` (Definition 2.1
  (i), uniform in the parameter, the union sits inside the probability); deterministic `≺` is
  `RBM.UnifDetDom` (Definition 2.1 (ii)).
* **Dimensions.**  `N` is the index of the families.  The matrices at index `N` are indexed by
  `ZMod (L N) × Fin (W N)` (`RBM.Band.Idx`, the block/offset index of `RBM1D/Defs/Model.lean`).
  Since `N = W L` cannot hold for every `N ∈ ℕ` (primes, `N < 3`), `RBM.Band` only asks
  `W L ≤ N ≤ 2 W L` eventually; the paper's `N` and our index differ by a factor `≤ 2`, which
  is invisible to `≺`.
* **Times** are sequences `s : ℕ → ℝ`: the times of the induction on p. 24,
  `1 - s_k = W^{-kτ'}`, depend on `N`.  A fixed time is `fun _ => s`.
* **Fixed `n`.**  "For each fixed `n`" (loop length) is a separate `≺` statement for each
  `n ≥ 1`; the maximum over `σ ∈ {+,-}ⁿ`, `a ∈ ℤ_Lⁿ` is the uniformity in the parameter
  `u ∈ LoopData (L N) n = (Fin n → Bool) × (Fin n → ZMod (L N))`.
* **Uniformity in `u ∈ [s, t]`** in Steps 1–6 is uniformity in the parameter: the parameter
  set is `Set.Icc (s N) (t N) × (…)`.

## The interface

* `RBM.Band Ω` — the probability measure, the dimensions `W, L`, and the bandwidth
  condition (2.2) `W ≥ N^{1/2+c}`.
* `RBM.Sample B` — (2.34)/(2.36): the matrix flow `H : ∀ N, ℝ → Ω → Matrix`, Hermitian,
  `H_0 = 0`, entrywise measurable.  The law of `H_t` (the matrix Brownian motion with variance
  profile `S`) is **not** encoded: everything that uses it is a field of one of the structures
  below.
* `RBM.Sample.G` (2.36), `RBM.Sample.Lval` (2.41, via `RBM.gloop`), `RBM.Band.Kval`
  (Definition 2.12, via `RBM.Kgen`), `RBM.Sample.ELval` (`E L_{t,σ,a}`), and the scale
  `RBM.Band.scale B E N t = W ℓ_t η_t` (the same expression as `RBM.flowScale` of
  `Flow/Scales.lean`, which this file does not import).
* `RBM.BoundsCore X E s` — (2.68)/(2.60), (2.69)/(2.63), (2.70)/(2.64) at time `s`;
  `RBM.Bounds X E s` adds (2.71)/(2.62).  These are the statements of Lemmas 2.18–2.20
  at time `s` and the hypotheses of Theorem 2.21.
* `RBM.Cond272 B E s t` — the step condition (2.72).
* `RBM.Thm221 X κ` — Theorem 2.21: `Bounds s → (2.72) → Bounds t`.
* `RBM.Steps X E s t` — the eight conclusions (2.73)–(2.80) of Steps 1–6 (Section 5).
* `RBM.Transfer X` — the band matrix `H` itself and (2.39)/(2.66) (equality in law) written as
  **transfer of `≺`-bounds** from `G_t` to `G(z)` (no pushforward measures).

## Sanity lemmas (checking that the interface fits together)

* `RBM.Bounds_of_Steps` — Steps (2.75), (2.78), (2.79), (2.80) at `u := t` give the conclusion
  of Theorem 2.21.  `RBM.BoundsCore_of_Steps` does the first three **without using Step 6**,
  which formalizes the remark on p. 25: Theorem 2.21 holds with (2.71) removed from both the
  hypothesis and the conclusion.
* `RBM.BoundsCore.stochDom_norm_Lval` — **(2.61)** from (2.68) and the proved (2.59)
  (`RBM.norm_Kgen_le`), for `3 ≤ n` (the range in which (2.59) is proved).
* `RBM.Transfer.green_sub_msc` — **(2.65)** from (2.39) and the proved (2.38)
  (`RBM.msc_eq_sqrt_mul_mE`).

## Deviations from the paper (to be recorded in `docs/paper-deltas.md`)

* The index `N` satisfies `W L ≤ N ≤ 2 W L` eventually rather than `N = W L` (see above).
* (2.71)/(2.80) use the Bochner integral `∫ ω, L ∂P` for `E L`; integrability is not
  demanded (in the paper `‖G_t‖ ≤ η_t^{-1}` makes it automatic).
* (2.72) and all `≺` statements are asymptotic in `N`; (2.72) is asked only eventually.
  Theorem 2.21 is stated for `s ≤ t` instead of `s < t` (for `s = t` it is trivial).
* The distance `|a₁ - a₂|` in (2.63)/(2.69)/(2.76)/(2.79) is the cyclic distance `RBM.zdist`.
* (2.39) and (2.66) are stated as transfers of bounds, for deterministic centerings and
  deterministic control parameters (the only form in which the paper uses them).
* (2.61) is derived only for `n ≥ 3` and under `1 ≤ W ℓ_s η_s` eventually (true in the regime
  `1 - s ≥ N^{-1+τ}` of Lemma 2.18, see `RBM.flowScale_ge` in `Flow/Scales.lean`).
-/

namespace RBM

open MeasureTheory Filter

/-! ### Two generic facts about `≺` -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Restricting (or reindexing) the parameter set preserves `≺`. -/
theorem StochDom.precomp_param {U V : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : StochDom P ξ ζ) (φ : ∀ N, V N → U N) :
    StochDom P (fun N v ω => ξ N (φ N v) ω) (fun N v ω => ζ N (φ N v) ω) :=
  fun τ hτ D hD => by
    filter_upwards [h τ hτ D hD] with N hN
    refine (measure_mono fun ω hω => ?_).trans hN
    obtain ⟨v, hv⟩ := hω
    exact ⟨φ N v, hv⟩

/-- A pointwise smaller family is dominated by whatever dominates the larger one. -/
theorem StochDom.of_le_left {U : ℕ → Type*} {ξ ξ' ζ : ∀ N, U N → Ω → ℝ}
    (hle : ∀ N u ω, ξ N u ω ≤ ξ' N u ω) (h : StochDom P ξ' ζ) : StochDom P ξ ζ :=
  StochDom.of_subset h fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun N ω ⟨u, hu⟩ => ⟨u, lt_of_lt_of_le hu (hle N u ω)⟩⟩

/-- Restricting (or reindexing) the parameter set preserves deterministic `≺`. -/
theorem UnifDetDom.precomp_param {U V : ℕ → Type*} {f g : ∀ N, U N → ℝ}
    (h : UnifDetDom f g) (φ : ∀ N, V N → U N) :
    UnifDetDom (fun N v => f N (φ N v)) (fun N v => g N (φ N v)) := fun τ hτ => by
  filter_upwards [h τ hτ] with N hN v
  exact hN (φ N v)

end Generic

/-! ### Loop index data of fixed length -/

/-- The index data `(σ, a) ∈ {+,-}ⁿ × ℤ_Lⁿ` of an `n`-loop, as a finite type. -/
abbrev LoopData (L n : ℕ) : Type := (Fin n → Bool) × (Fin n → ZMod L)

/-- The loop index of `(σ, a)`. -/
def LoopData.idx {L n : ℕ} (u : LoopData L n) : LoopIdx (ZMod L) :=
  ⟨List.ofFn u.1, List.ofFn u.2⟩

theorem LoopData.idx_wf {L n : ℕ} (u : LoopData L n) : u.idx.WF := by
  simp [LoopData.idx, LoopIdx.WF]

@[simp] theorem LoopData.idx_length {L n : ℕ} (u : LoopData L n) : u.idx.length = n := by
  simp [LoopData.idx, LoopIdx.length]

/-- The `2`-loop with charges `σ = (+, -)` and blocks `(a, b)`. -/
def pmLoop {L : ℕ} (a b : ZMod L) : LoopIdx (ZMod L) := ⟨[true, false], [a, b]⟩

/-! ### The model -/

/-- **The band model: dimensions, bandwidth (2.2), probability measure.**

At index `N` the matrix has `L N` blocks of size `W N`.  The paper's `N = W L` is replaced by
`W L ≤ N ≤ 2 W L` for large `N` (a relation that can hold for every large `N`, unlike
`N = W L`).  `bandwidth` is (2.2) `W ≥ N^{1/2 + c}`. -/
structure Band (Ω : Type*) [MeasurableSpace Ω] where
  /-- The probability measure. -/
  P : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- The block size `W = W(N)`. -/
  W : ℕ → ℕ
  /-- The number of blocks `L = L(N)`. -/
  L : ℕ → ℕ
  W_pos : ∀ N, 0 < W N
  three_le_L : ∀ N, 3 ≤ L N
  /-- `N = W L` up to a factor `2`. -/
  dim : ∀ᶠ N : ℕ in atTop, W N * L N ≤ N ∧ N ≤ 2 * (W N * L N)
  /-- The constant `c > 0` of (2.2). -/
  c : ℝ
  c_pos : 0 < c
  /-- **(2.2)** `W ≥ N^{1/2 + c}`. -/
  bandwidth : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 + c) ≤ W N

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

instance neZeroW (N : ℕ) : NeZero (B.W N) := ⟨(B.W_pos N).ne'⟩

instance neZeroL (N : ℕ) : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩

/-- The row index `ZMod L × Fin W` of the `N × N` matrices (block, offset). -/
abbrev Idx (N : ℕ) : Type := ZMod (B.L N) × Fin (B.W N)

/-- `ℓ_t = ℓ̂(t) = min((1-t)^{-1/2}, L)` (2.59). -/
noncomputable def ell (N : ℕ) (t : ℝ) : ℝ := ellHat (B.L N) (t : ℂ)

/-- **The scale `W ℓ_t η_t`** of Lemmas 2.18–2.20; `η_t = (1-t) Im m^{(E)}` (2.35).
Literally the expression `RBM.flowScale (W N) (L N) E t` of `Flow/Scales.lean`. -/
noncomputable def scale (E : ℝ) (N : ℕ) (t : ℝ) : ℝ := (B.W N : ℝ) * B.ell N t * etaT E t

/-- The primitive loop `K_{t,σ,a}` (Definition 2.12, tree representation `RBM.Kgen`). -/
noncomputable def Kval (E : ℝ) (N : ℕ) (t : ℝ) (I : LoopIdx (ZMod (B.L N))) : ℂ :=
  Kgen (B.L N) (B.W N) (mSigma E) t I

/-- The decay profile `exp(-(|a - b|/ℓ_t)^{1/2}) + W^{-D}` of (2.63), (2.69), (2.76), (2.79). -/
noncomputable def decayProf (N : ℕ) (t D : ℝ) (a b : ZMod (B.L N)) : ℝ :=
  Real.exp (-(((zdist (B.L N) (a - b) : ℝ) / B.ell N t) ^ ((1 : ℝ) / 2))) + (B.W N : ℝ) ^ (-D)

/-- **`W ℓ_t η_t > 0` for `0 ≤ t < 1`** — the `0 ≤ t` form of `RBM.Band.scale_pos`.

Strict positivity of `t` is not needed: `ℓ_t ≥ 1` already holds at `t = 0` (`ℓ_0 = min(1,L) = 1`),
which is `RBM.one_le_ellHat`.  This form is load-bearing for the assembly of Theorem 2.21:
`RBM.Thm221.step` quantifies over `0 ≤ s N`, and the grid of `RBM.Bounds_of_Thm221` really does
start at `s ≡ 0`. -/
theorem scale_pos' {E : ℝ} (hE : |E| < 2) (N : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < B.scale E N t := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ := one_le_ellHat (B.L N) (B.three_le_L N) ht0 ht1
  have hη := etaT_pos hE ht1
  unfold scale ell
  positivity

theorem scale_pos {E : ℝ} (hE : |E| < 2) (N : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < B.scale E N t :=
  B.scale_pos' hE N ht0.le ht1

end Band

/-- **The stochastic flow (2.34), per `N`.**  `H N t ω` is the matrix `H_t`; it is Hermitian,
`H_0 = 0` and entrywise measurable.  The law of the flow (a matrix Brownian motion with variance
profile `S`) is not formalized; its consequences are the fields of `RBM.Bounds`, `RBM.Thm221`,
`RBM.Steps` and `RBM.Transfer`. -/
structure Sample {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) where
  /-- The matrix flow `t ↦ H_t`. -/
  H : ∀ N, ℝ → Ω → Matrix (B.Idx N) (B.Idx N) ℂ
  hermitian : ∀ N t ω, Matrix.IsHermitian (H N t ω)
  /-- `H_0 = 0` (2.34). -/
  H_zero : ∀ N ω, H N 0 ω = 0
  measurable : ∀ N t i j, Measurable fun ω => H N t ω i j

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

/-- **(2.36)** `G_t = (H_t - z_t)⁻¹`, `z_t = E + (1-t) m^{(E)}` (Definition 2.7). -/
noncomputable def G (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) : Matrix (B.Idx N) (B.Idx N) ℂ :=
  green (X.H N t ω) (zt E t)

/-- **(2.41)** the `n`-`G` loop `L_{t,σ,a} = ⟨∏ G_t(σ_i) E_{a_i}⟩`. -/
noncomputable def Lval (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) : ℂ :=
  gloop (B.L N) (B.W N) (X.H N t ω) (zt E t) I

/-- The expectation `E L_{t,σ,a}`. -/
noncomputable def ELval (E : ℝ) (N : ℕ) (t : ℝ) (I : LoopIdx (ZMod (B.L N))) : ℂ :=
  ∫ ω, X.Lval E N t ω I ∂B.P

/-- `|L_{t,σ,a} - K_{t,σ,a}|`. -/
noncomputable def lkErr (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) : ℝ :=
  ‖X.Lval E N t ω I - B.Kval E N t I‖

/-- `|(G_t - m)_{ij}|`, the entries whose maximum is `‖G_t - m‖_max`. -/
noncomputable def llErr (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (ij : B.Idx N × B.Idx N) : ℝ :=
  ‖(X.G E N t ω - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖

/-- `|E L_{t,σ,a} - K_{t,σ,a}|`. -/
noncomputable def expErr (E : ℝ) (N : ℕ) (t : ℝ) (I : LoopIdx (ZMod (B.L N))) : ℝ :=
  ‖X.ELval E N t I - B.Kval E N t I‖

end Sample

/-! ### Lemmas 2.18–2.20 at a time `s`, Theorem 2.21 -/

section Bounds

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- (2.68), (2.69), (2.70) at the time `s`: the part of Lemmas 2.18–2.20 that Steps 1–5
propagate (p. 25: Theorem 2.21 holds with (2.71) removed). -/
structure BoundsCore (X : Sample B) (E : ℝ) (s : ℕ → ℝ) : Prop where
  /-- **(2.68) = (2.60)**: `max_{σ,a} |L_{s,σ,a} - K_{s,σ,a}| ≺ (W ℓ_s η_s)^{-n}`, `n ≥ 1`. -/
  LmK : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (u : LoopData (B.L N) n) ω => X.lkErr E N (s N) ω u.idx)
    (fun N _ _ => (B.scale E N (s N))⁻¹ ^ n)
  /-- **(2.69) = (2.63)**: for `σ = (+,-)` and every `D > 0`,
  `|L_{s,σ,a} - K_{s,σ,a}| ≺ (W ℓ_s η_s)^{-2} (exp(-(|a₁-a₂|/ℓ_s)^{1/2}) + W^{-D})`. -/
  decay : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (a : ZMod (B.L N) × ZMod (B.L N)) ω => X.lkErr E N (s N) ω (pmLoop a.1 a.2))
    (fun N a _ => (B.scale E N (s N))⁻¹ ^ 2 * B.decayProf N (s N) D a.1 a.2)
  /-- **(2.70) = (2.64)**: `‖G_s - m‖_max ≺ (W ℓ_s η_s)^{-1/2}`. -/
  localLaw : StochDom B.P
    (fun N (ij : B.Idx N × B.Idx N) ω => X.llErr E N (s N) ω ij)
    (fun N _ _ => (B.scale E N (s N))⁻¹ ^ ((1 : ℝ) / 2))

/-- **Lemmas 2.18, 2.19, 2.20 at the time `s`** = the hypotheses (2.68)–(2.71) of
Theorem 2.21. -/
structure Bounds (X : Sample B) (E : ℝ) (s : ℕ → ℝ) : Prop extends BoundsCore X E s where
  /-- **(2.71) = (2.62)**: `max_{σ ∈ {+,-}², a} |E L_{s,σ,a} - K_{s,σ,a}| ≺ (W ℓ_s η_s)^{-3}`
  (deterministic `≺`). -/
  expect : UnifDetDom
    (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
    (fun N _ => (B.scale E N (s N))⁻¹ ^ 3)

/-- **(2.72)**: `(W ℓ_t η_t)^{-1} ≤ ((1-t)/(1-s))^{30}` (for large `N`). -/
def Cond272 (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, (B.scale E N (t N))⁻¹ ≤ ((1 - t N) / (1 - s N)) ^ 30

/-- **Theorem 2.21** (as a hypothesis): for `|E| ≤ 2 - κ` and times `0 ≤ s ≤ t < 1` satisfying
(2.72), the bounds (2.68)–(2.71) at `s` imply them at `t`. -/
structure Thm221 (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
    (∀ N, t N < 1) → Cond272 B E s t → Bounds X E s → Bounds X E t

/-- The times `u ∈ [s, t]` at index `N`. -/
abbrev TimeIcc (s t : ℕ → ℝ) (N : ℕ) : Type := ↥(Set.Icc (s N) (t N))

/-! ### The individual conclusions of Steps 1–6, as standalone statements (T149)

`RBM.Steps` bundles the eight conclusions of §2.7.  The deterministic glue that *produces* the
later fields must not take the whole bundle as a hypothesis — that would make "Step 3 needs
(2.77)" a theorem, i.e. circular packaging (T147 §0a verified this with a compiled probe).  The
five statements below are, verbatim, the five fields of `RBM.Steps` that the glue actually
projects; every glue theorem takes these instead of the bundle, and the bundle-shaped statement
is kept as a one-line corollary.  The dependency order 1 → 2 → 3 → 4/5 → 6 is acyclic. -/

/-- **(2.73)** (Step 1): `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`, uniformly in
`u ∈ [s,t]`.  Verbatim the field `RBM.Steps.apriori`. -/
def AprioriFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
    (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1))

/-- **(2.75)** (Step 2): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`, uniformly in `u ∈ [s,t]`.
Verbatim the field `RBM.Steps.localLaw`. -/
def LocalLawFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2))

/-- **(2.76)** (Step 2): for `σ = (+,-)`, `|L_u - K_u| ≺ (η_s/η_u)^4 (W ℓ_u η_u)^{-2}
(exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`.  Verbatim the field `RBM.Steps.aprioriDecay`. -/
def AprioriDecayFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
      B.decayProf N p.1 D p.2.1 p.2.2)

/-- **(2.77)** (Step 3): `max_{σ,a} |L_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n+1}`, uniformly in `u ∈ [s,t]`.
Verbatim the field `RBM.Steps.sharpLoop`. -/
def SharpLoopFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1))

/-- **(2.78)** (Step 4): `max_{σ,a} |L_{u,σ,a} - K_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n}`, uniformly in
`u ∈ [s,t]`.  Verbatim the field `RBM.Steps.sharpLmK`. -/
def SharpLmKFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)

/-- **Steps 1–6 of the proof of Theorem 2.21** (§2.7, proved in Section 5), as hypotheses.
All bounds are uniform in `u ∈ [s, t]`. -/
structure Steps (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop where
  /-- **(2.73)** (Step 1): `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. -/
  apriori : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
    (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1))
  /-- **(2.74)** (Step 1): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/4}`. -/
  weakLaw : StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4))
  /-- **(2.75)** (Step 2): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`. -/
  localLaw : StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2))
  /-- **(2.76)** (Step 2): for `σ = (+,-)`, `|L_u - K_u| ≺ (η_s/η_u)^4 (W ℓ_u η_u)^{-2}
  (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`. -/
  aprioriDecay : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
      B.decayProf N p.1 D p.2.1 p.2.2)
  /-- **(2.77)** (Step 3): `max_{σ,a} |L_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n+1}`. -/
  sharpLoop : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1))
  /-- **(2.78)** (Step 4): `max_{σ,a} |L_{u,σ,a} - K_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n}`. -/
  sharpLmK : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)
  /-- **(2.79)** (Step 5): for `σ = (+,-)`,
  `|L_u - K_u| ≺ (W ℓ_u η_u)^{-2} (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`. -/
  sharpDecay : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)
  /-- **(2.80)** (Step 6): `max_{σ ∈ {+,-}², a} |E L_u - K_u| ≺ (W ℓ_t η_t)^{-3}` — note the
  right side is taken at the final time `t`, as in the paper. -/
  sharpExpect : UnifDetDom
    (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
    (fun N _ => (B.scale E N (t N))⁻¹ ^ 3)

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- The final time `t ∈ [s, t]`. -/
def TimeIcc.last (hst : ∀ N, s N ≤ t N) (N : ℕ) : TimeIcc s t N := ⟨t N, hst N, le_rfl⟩

/-- **Steps 2, 4, 5 at `u = t` give (2.68)–(2.70) at `t`** — without Step 6.  This is the
remark on p. 25: (2.71) is not needed for Steps 1–5, so Theorem 2.21 holds with (2.71) removed
from both its hypothesis and its conclusion. -/
theorem BoundsCore_of_Steps (h : Steps X E s t) (hst : ∀ N, s N ≤ t N) : BoundsCore X E t where
  LmK n hn := (h.sharpLmK n hn).precomp_param fun N u => (TimeIcc.last hst N, u)
  decay D hD := (h.sharpDecay D hD).precomp_param fun N a => (TimeIcc.last hst N, a)
  localLaw := h.localLaw.precomp_param fun N ij => (TimeIcc.last hst N, ij)

/-- **Steps 1–6 give the conclusion of Theorem 2.21** (take `u := t` in (2.75), (2.78), (2.79),
(2.80)). -/
theorem Bounds_of_Steps (h : Steps X E s t) (hst : ∀ N, s N ≤ t N) : Bounds X E t where
  toBoundsCore := BoundsCore_of_Steps h hst
  expect := h.sharpExpect.precomp_param fun N u => (TimeIcc.last hst N, u)

/-- **(2.61) from (2.68) and (2.59).**  `max_{σ,a} |L_{s,σ,a}| ≺ (W ℓ_s η_s)^{-n+1}`, since
`|L| ≤ |L - K| + |K|`, `|L - K| ≺ (W ℓ_s η_s)^{-n}` by (2.68) and `|K| ≤ C (W ℓ_s η_s)^{-n+1}` by
(2.59) (`RBM.norm_Kgen_le`, proved for `n ≥ 3`).  The comparison
`(W ℓ_s η_s)^{-n} ≤ (W ℓ_s η_s)^{-n+1}` uses `W ℓ_s η_s ≥ 1` for large `N`. -/
theorem BoundsCore.stochDom_norm_Lval (hB : BoundsCore X E s) {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hEk : |E| ≤ 2 - k) (hs0 : ∀ N, 0 < s N) (hs1 : ∀ N, s N < 1)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (s N)) {n : ℕ} (hn : 3 ≤ n) :
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (s N) ω u.idx‖)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ (n - 1)) := by
  have hE : |E| < 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := norm_Kgen_le hk0 hk1 hEk n
  set Y : ℕ → ℝ := fun N => (B.scale E N (s N))⁻¹ with hYdef
  have hY0 : ∀ N, 0 ≤ Y N := fun N => (inv_pos.2 (B.scale_pos hE N (hs0 N) (hs1 N))).le
  -- `|K| ≤ C Y^{n-1}`
  have hK : ∀ N (u : LoopData (B.L N) n),
      ‖B.Kval E N (s N) u.idx‖ ≤ C * Y N ^ (n - 1) := by
    intro N u
    have := hC (B.L N) (B.three_le_L N) (B.W N) (s N) (hs0 N) (hs1 N) u.idx u.idx_wf
      (by simp [hn]) (by simp)
    rw [LoopData.idx_length] at this
    refine this.trans (le_of_eq ?_)
    simp only [hYdef, Band.scale, Band.ell]
    ring_nf
  -- `|L - K| ≺ Y^{n-1}`
  have h1 : StochDom B.P (fun N (u : LoopData (B.L N) n) ω => X.lkErr E N (s N) ω u.idx)
      (fun N _ _ => Y N ^ (n - 1)) := by
    refine (hB.LmK n (by omega)).trans ?_
    refine StochDom.of_unifDetDom (f := fun N (_ : LoopData (B.L N) n) => Y N ^ n)
      (g := fun N _ => Y N ^ (n - 1)) ?_
    refine UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hY0 N) _) 1 ?_
    filter_upwards [hA] with N hN u
    have hY1 : Y N ≤ 1 := inv_le_one_of_one_le₀ hN
    have : Y N ^ n = Y N * Y N ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, one_mul]
    exact mul_le_of_le_one_left (pow_nonneg (hY0 N) _) hY1
  -- `|K| ≺ Y^{n-1}`
  have h2 : StochDom B.P (fun N (u : LoopData (B.L N) n) (_ : Ω) => ‖B.Kval E N (s N) u.idx‖)
      (fun N _ _ => Y N ^ (n - 1)) :=
    StochDom.of_unifDetDom (UnifDetDom.of_eventually_le_const_mul
      (fun N _ => pow_nonneg (hY0 N) _) C (Eventually.of_forall hK))
  have h3 : StochDom B.P (fun N (_ : LoopData (B.L N) n) (_ : Ω) => Y N ^ (n - 1) + Y N ^ (n - 1))
      (fun N _ _ => Y N ^ (n - 1)) := by
    refine StochDom.of_unifDetDom (f := fun N (_ : LoopData (B.L N) n) => Y N ^ (n - 1) +
      Y N ^ (n - 1)) (g := fun N _ => Y N ^ (n - 1)) ?_
    exact UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hY0 N) _) 2
      (Eventually.of_forall fun N _ => by linarith)
  refine StochDom.of_le_left (fun N u ω => ?_) ((h1.add h2).trans h3)
  have := norm_sub_norm_le (X.Lval E N (s N) ω u.idx) (B.Kval E N (s N) u.idx)
  simp only [Pi.add_apply, Sample.lkErr]
  linarith

end Bounds

/-! ### The distributional identities (2.39), (2.65), (2.66) -/

/-- **The band matrix and the identities in law (2.39), (2.66)** (Lemma 2.8, p. 22), written as
transfers of `≺`-bounds rather than equalities of laws.

For `Im z > 0` let `E = lemE z`, `t = lemT z` (Lemma 2.8, `RBM.lemE`, `RBM.lemT`; then
`z = t^{-1/2} z_t^{(E)}` and `m_sc(z) = t^{1/2} m^{(E)}` are proved in `Defs/Semicircle.lean`).
Since `H` and `t^{-1/2} H_t` have the same law, so do `G(z)` and `t^{1/2} G_t^{(E)}` (2.39), and
the loops `Tr G(z) E_a G(z) E_b`, `Tr G(z) E_a G(z)† E_b` and `t L_{t,(+,±),(a,b)}` (2.66).
Equality in law of finitely many measurable random variables transfers every bound of the form
`max_u |ξ(u) - c(u)| ≤ N^τ ζ(u)` with deterministic `c`, `ζ`; that is what is recorded.
Only the direction `G_t → G(z)` is used in the paper. -/
structure Transfer {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) where
  /-- The band matrix `H` of Section 2.1, one for each `N`. -/
  Hband : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ
  hermitian : ∀ N ω, Matrix.IsHermitian (Hband N ω)
  /-- **(2.39)** `G(z) ∼ t^{1/2} G_t^{(E)}`, entrywise, with deterministic centering `c`. -/
  green : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) →
    ∀ (c : ∀ N, B.Idx N × B.Idx N → ℂ) (ζ : ∀ N, B.Idx N × B.Idx N → ℝ),
    StochDom B.P
      (fun N ij ω => ‖(Real.sqrt (lemT (z N)) : ℂ) *
        X.G (lemE (z N)) N (lemT (z N)) ω ij.1 ij.2 - c N ij‖)
      (fun N ij _ => ζ N ij) →
    StochDom B.P (fun N ij ω => ‖RBM.green (Hband N ω) (z N) ij.1 ij.2 - c N ij‖)
      (fun N ij _ => ζ N ij)
  /-- **(2.66)** `Tr G(z) E_a G(z)^{(±)} E_b ∼ t L_{t,(+,±),(a,b)}`, with deterministic
  centering `c` (`σ₂ = true`: `G(z)`; `σ₂ = false`: `G(z)† = G(z̄)`). -/
  loop2 : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) → ∀ σ₂ : Bool,
    ∀ (c : ∀ N, ZMod (B.L N) × ZMod (B.L N) → ℂ) (ζ : ∀ N, ZMod (B.L N) × ZMod (B.L N) → ℝ),
    StochDom B.P
      (fun N ab ω => ‖(lemT (z N) : ℂ) *
        X.Lval (lemE (z N)) N (lemT (z N)) ω ⟨[true, σ₂], [ab.1, ab.2]⟩ - c N ab‖)
      (fun N ab _ => ζ N ab) →
    StochDom B.P
      (fun N ab ω => ‖gloop (B.L N) (B.W N) (Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ -
        c N ab‖)
      (fun N ab _ => ζ N ab)
  /-- **(2.66) in expectation** (used for (2.8), (2.9) together with (2.62)). -/
  loop2_expect : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) → ∀ (σ₂ : Bool) (N : ℕ)
    (a b : ZMod (B.L N)),
    ∫ ω, gloop (B.L N) (B.W N) (Hband N ω) (z N) ⟨[true, σ₂], [a, b]⟩ ∂B.P =
      (lemT (z N) : ℂ) * X.ELval (lemE (z N)) N (lemT (z N)) ⟨[true, σ₂], [a, b]⟩

namespace Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B}

/-- **(2.65)** `G(z) - m_sc(z) ∼ t^{1/2} (G_t^{(E)} - m^{(E)})`, as a transfer of the local law:
(2.39) with the centering `m_sc(z) δ_{ij} = t^{1/2} m^{(E)} δ_{ij}` (2.38). -/
theorem green_sub_msc (T : Transfer X) (z : ℕ → ℂ) (hz : ∀ N, 0 < (z N).im)
    (ζ : ∀ N, B.Idx N × B.Idx N → ℝ)
    (h : StochDom B.P
      (fun N ij ω => ‖((Real.sqrt (lemT (z N)) : ℂ) • (X.G (lemE (z N)) N (lemT (z N)) ω -
        mE (lemE (z N)) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ))) ij.1 ij.2‖)
      (fun N ij _ => ζ N ij)) :
    StochDom B.P
      (fun N ij ω => ‖(RBM.green (T.Hband N ω) (z N) -
        msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N ij _ => ζ N ij) := by
  have key := T.green z hz (fun N ij => if ij.1 = ij.2 then msc (z N) else 0) ζ (by
    convert h using 4 with N ij ω
    rw [msc_eq_sqrt_mul_mE (hz N)]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring_nf)
  convert key using 4 with N ij ω
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring_nf

end Transfer

end RBM

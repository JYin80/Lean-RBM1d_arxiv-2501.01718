/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelQ

/-!
# Back from `Q_v ∘ (L-K)_v` to `(L-K)_v`: the `P` half of (5.101) on the moment route (T218)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5, specifically **(5.101)**

> `A = Q_t ∘ A + (P ∘ A)_{a₁} ϑ_{t,a}`

and the slot-sum bound **(5.96)** that makes its second summand small.

After D14 the moment route goes through `RBM.MomentDuhamel.Hyp.momentDuhamelQ`, so
`RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` (T214) only controls `‖Q_v ∘ (L-K)_v‖`.
This file supplies the other half and composes the two into a bound on `‖(L-K)_v‖` itself.

## Main results

* §1 — `RBM.Gauss.stochDom_of_norm_Qop_add`: **(5.101) at the level of `≺`**, abstractly: a
  `≺` for the `Q_t` part and a `≺` for the `(P ∘ A) ϑ_t` part compose into a `≺` for `A`.
  `RBM.Gauss.stochDom_norm_lkT_qGood` is the same statement with the `QGood` guard that the
  flow's two halves actually carry.
* §2 — `RBM.Gauss.pHalfBound` and `RBM.Gauss.norm_Psum_lkT_mul_vartheta_le`: the `P` half
  along the flow, i.e. Ward's (5.96) (`RBM.SumZeroDyn.norm_Psum_lkT_le`) times the entrywise
  bound on `ϑ_v` of Lemma 5.13 (5.87) (`RBM.SumZeroDyn.norm_vartheta_real_le`).  It is stated
  **at a point of the good event**, never for all `ω`: its two premises are the (5.76) and
  (5.75) bounds, which are only true with high probability.
* §3 — `RBM.Gauss.momNorm_norm_lkT_le_of_event`: **the moment-norm form of (5.101) along the
  flow**, obtained from T201's good-event Minkowski `RBM.Gauss.momNorm_le_affine_on_event`
  with `c = 1`.  This is the shape the moment route consumes;
  `RBM.Gauss.momNorm_norm_lkT_le_of_hyp` is the same with both integrability premises
  discharged from `RBM.MomentDuhamel.Hyp.integrable` and `RBM.MomentDuhamel.QIntegrable`.
* §4 — `RBM.Gauss.eventually_env_mul_prob_rpow_le` and
  `RBM.Gauss.eventually_env_mul_prob_rpow_le_moment`: the *price* of the good-event split.
  The loss is `Env · P(Ξᶜ)^{1/q}` with `q = 2p` **fixed**, so it is only negligible when the
  complement is super-polynomially small — which is exactly `RBM.HighProb`.  The companion
  `RBM.Gauss.no_const_event_loss` shows that a *fixed* polynomial bound `P(Ξᶜ) ≤ N^{-D}` does
  **not** suffice: the loss then diverges as soon as `D < q · C_env`.
* §5 — `RBM.Gauss.stochDom_scale_norm_lkT_of_momentDuhamelQ` and
  `RBM.Gauss.stochDom_scale_norm_lkT_of_hyp`: the composition.  `Q` half from
  `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ`, `P` half from `RBM.SumZeroDyn.termP` (a
  theorem, not a new field), conclusion a `≺` for `(Wℓ_vη_v)^{n+2} |(L-K)_{v,σ,a}|`.
* §6 — `RBM.Gauss.qpWit` and `RBM.Gauss.qpWit_route_witness`: the satisfiability witness.
  Its `Q_v` part is **non-zero** (T201's `RBM.Gauss.witTensor`) and its `P` part is
  **exactly `1`**, so neither half of (5.101) is degenerate; the normalisation is the critical
  one, `A_v^{-(m+2)} = (κ_A (1-v) ℓ_v)^{-(m+2)}`, and `v ↑ 1` is allowed.

## Deviations from the paper

One, recorded in `docs/paper-deltas.md` as **`T218a`**: §3's conclusion carries an extra
summand `Env · P(Ξᶜ)^{1/q}` that (5.92)/(5.101) do not have.  The paper works with `≺`
throughout, where such a loss is absorbed by the definition of `≺`; a *moment-norm* form of
(5.101) whose premises are event-restricted cannot absorb it, and §4 is the accounting that
disposes of it (`RBM.HighProb`, with `q = 2p` fixed before `D`).  The `QGood` guard is **not**
a deviation: it is §5.5's own charge split, the same one `RBM.SumZeroDyn.termP` and
`RBM.SumZeroDyn.bound_qGood` already carry, and `RBM.Gauss.qGood_charge` shows it is not
vacuous.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open Filter MeasureTheory Real

/-! ### §1  (5.101) at the level of `≺`

`RBM.SumZeroDyn.norm_le_norm_Qop_add` is the pointwise identity `|A| ≤ |Q_t A| + |P A| |ϑ_t|`.
It is an algebraic identity, true at every `ω`, so turning it into a `≺` costs nothing beyond
`RBM.StochDom.add`.  The point of stating it here is that the moment route now has **two**
sources — `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` for the first summand and
`RBM.SumZeroDyn.termP` for the second — and nothing in the repository joined them. -/

section Compose

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **(5.101) for `≺`.**  A deterministic non-negative weight `c` (in the application
`(Wℓ_vη_v)^{n+2}`) is carried along, since that is the normalisation §5.5 states its bounds
in. -/
theorem stochDom_of_norm_Qop_add {U : ℕ → Type*} {Lf : ℕ → ℕ} [∀ N, NeZero (Lf N)] {n : ℕ}
    {c : ∀ N, U N → ℝ} (hc : ∀ N u, 0 ≤ c N u)
    {tt : ∀ N, U N → ℂ} {A : ∀ N, U N → Ω → LoopArg (Lf N) (n + 1) → ℂ}
    {a : ∀ N, U N → LoopArg (Lf N) (n + 1)} {ζQ ζP : ∀ N, U N → Ω → ℝ}
    (hQ : StochDom P (fun N u ω => c N u * ‖Qop (Lf N) (tt N u) (A N u ω) (a N u)‖) ζQ)
    (hP : StochDom P (fun N u ω => c N u
      * (‖Psum (Lf N) (A N u ω) (a N u 0)‖ * ‖vartheta (Lf N) (tt N u) (a N u)‖)) ζP) :
    StochDom P (fun N u ω => c N u * ‖A N u ω (a N u)‖) (ζQ + ζP) := by
  refine StochDom.of_le_left (fun N u ω => ?_) (hQ.add hP)
  simp only [Pi.add_apply]
  have h := SumZeroDyn.norm_le_norm_Qop_add (Lf N) (tt N u) (A N u ω) (a N u)
  have := mul_le_mul_of_nonneg_left h (hc N u)
  linarith [this, (by ring :
    c N u * (‖Qop (Lf N) (tt N u) (A N u ω) (a N u)‖
        + ‖Psum (Lf N) (A N u ω) (a N u 0)‖ * ‖vartheta (Lf N) (tt N u) (a N u)‖)
      = c N u * ‖Qop (Lf N) (tt N u) (A N u ω) (a N u)‖
        + c N u * (‖Psum (Lf N) (A N u ω) (a N u 0)‖
            * ‖vartheta (Lf N) (tt N u) (a N u)‖))]

end Compose

/-! ### §2  The `P` half along the flow: (5.96) times (5.87)

`RBM.SumZeroDyn.norm_Psum_lkT_le` is (5.96) — Ward's identity turns the slot sum of an
alternating `(L-K)_{u,σ}` into a difference of two slot sums of one loop less, gaining
`|κ_u| = (2Wη_u)^{-1}`.  `RBM.SumZeroDyn.norm_vartheta_real_le` is the entrywise half of
Lemma 5.13 (5.87).  Their product is the last term of (5.101).

**On the quantifiers.**  The two premises `hX` and `hdec` are the (5.76) and (5.75) bounds *at
the point `ω`*.  They are **not** asserted for all `ω`: on the flow they hold only on a
high-probability event, and asserting them everywhere would be false (e.g. they fail on the
event where the a priori bound on `Ξ^{(L-K)}` fails). -/

section PHalf

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The `P` half of (5.101), explicitly.**  `|κ_v| · 2 ((2e(ℓ_vK+1))^n K φ A_v^{-(n+1)}
+ L^n δ) · (C/ℓ_v)^{n+1}`: (5.96) for the slot sum, (5.87) for `ϑ_v`. -/
noncomputable def pHalfBound (B : Band Ω) (E : ℝ) (N : ℕ) (v : ℝ) (n : ℕ) (K φ δ : ℝ) : ℝ :=
  (2 * (B.W N : ℝ) * etaT E v)⁻¹
      * (2 * ((2 * exp 1 * (B.ell N v * K + 1)) ^ n * (K * φ * (B.scale E N v)⁻¹ ^ (n + 1))
          + (B.L N : ℝ) ^ n * δ))
    * (cTwo52 / B.ell N v) ^ (n + 1)

theorem pHalfBound_nonneg {E : ℝ} (hE : |E| < 2) (N : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (n : ℕ) {K φ δ : ℝ} (hK : 0 ≤ K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ) :
    0 ≤ pHalfBound B E N v n K φ δ := by
  have hη := etaT_pos hE hv1
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N v :=
    SumZeroDyn.ellHat_real_pos' (B.L N) (B.three_le_L N) hv0 hv1
  have hc := cTwo52_pos
  have hA : 0 < B.scale E N v := B.scale_pos' hE N hv0 hv1
  unfold pHalfBound
  positivity

/-- **`pHalfBound` is not identically zero.**  The degenerate reading of D14 ① would be one in
which the `P` half is bounded by `0` and the composition is vacuous; with a non-trivial a
priori bound `0 < φ` on `Ξ^{(L-K)}_{v,n+1}` it is strictly positive. -/
theorem pHalfBound_pos {E : ℝ} (hE : |E| < 2) (N : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (n : ℕ) {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 < φ) (hδ : 0 ≤ δ) :
    0 < pHalfBound B E N v n K φ δ := by
  have hη := etaT_pos hE hv1
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N v :=
    SumZeroDyn.ellHat_real_pos' (B.L N) (B.three_le_L N) hv0 hv1
  have hA : 0 < B.scale E N v := B.scale_pos' hE N hv0 hv1
  have hc := cTwo52_pos
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  have hL : (0 : ℝ) ≤ (B.L N : ℝ) ^ n := by positivity
  unfold pHalfBound
  have h1 : (0 : ℝ) < (2 * exp 1 * (B.ell N v * K + 1)) ^ n
      * (K * φ * (B.scale E N v)⁻¹ ^ (n + 1)) := by positivity
  have h2 : (0 : ℝ) ≤ (B.L N : ℝ) ^ n * δ := by positivity
  have h3 : (0 : ℝ) < 2 * ((2 * exp 1 * (B.ell N v * K + 1)) ^ n
      * (K * φ * (B.scale E N v)⁻¹ ^ (n + 1)) + (B.L N : ℝ) ^ n * δ) := by linarith
  have h4 : (0 : ℝ) < (2 * (B.W N : ℝ) * etaT E v)⁻¹ := by positivity
  have h5 : (0 : ℝ) < (cTwo52 / B.ell N v) ^ (n + 1) := by positivity
  exact mul_pos (mul_pos h4 h3) h5

/-- **(5.96) × (5.87)**: the last term of (5.101) at a point of the good event. -/
theorem norm_Psum_lkT_mul_vartheta_le (X : Sample B) {E : ℝ} (hE : |E| < 2) {n : ℕ}
    (hW : SumZeroDyn.WardP X E n) {N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hA0 : 0 < B.scale E N v) {ω : Ω} {σ : Fin (n + 2) → Bool} (hqg : SumZeroDyn.QGood σ)
    {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ)
    (hX : X.xiLK E N v ω (n + 1) ≤ K * φ)
    (hdec : ∀ (ρ : Fin (n + 1) → Bool) b,
      X.lkErr E N v ω (LoopData.idx (ρ, b)) * SumZeroDyn.farInd (B.L N) (B.ell N v * K) b ≤ δ)
    (a : LoopArg (B.L N) (n + 2)) :
    ‖Psum (B.L N) (SumZeroDyn.lkT X E N v ω σ) (a 0)‖ * ‖vartheta (B.L N) ((v : ℝ) : ℂ) a‖
      ≤ pHalfBound B E N v n K φ δ := by
  have hη := etaT_pos hE hv1
  have hWp : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N v :=
    SumZeroDyn.ellHat_real_pos' (B.L N) (B.three_le_L N) hv0 hv1
  have hc := cTwo52_pos
  have hP := SumZeroDyn.norm_Psum_lkT_le X hE hW hv0 hv1 hA0 hqg hK hφ hδ hX hdec (a 0)
  have hϑ := SumZeroDyn.norm_vartheta_real_le (B.L N) (B.three_le_L N) (n := n + 1) hv0 hv1 a
  have hrhs0 : (0 : ℝ) ≤ (2 * (B.W N : ℝ) * etaT E v)⁻¹
      * (2 * ((2 * exp 1 * (B.ell N v * K + 1)) ^ n * (K * φ * (B.scale E N v)⁻¹ ^ (n + 1))
          + (B.L N : ℝ) ^ n * δ)) := by
    have he : (0 : ℝ) < exp 1 := exp_pos 1
    positivity
  exact mul_le_mul hP hϑ (norm_nonneg _) hrhs0

end PHalf

/-! ### §3  The moment-norm form of (5.101) along the flow

T201's `RBM.Gauss.momNorm_le_affine_on_event` is Minkowski against `c Y + d` on a good event,
with the loss `Env · P(Ξᶜ)^{1/q}`.  Taking `c = 1`, `Y = |Q_v ∘ (L-K)_v|` and `d` the §2 bound
turns the pointwise (5.101) into a statement about `‖·‖_q`, which is what the moment route
consumes. -/

section MomentHalf

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

open RBM.MomentDuhamel

/-- **(5.101) in moment form, on the good event.**  The returning half of D14 ①:
`‖(L-K)_v‖_q ≤ ‖Q_v ∘ (L-K)_v‖_q + (P half) + Env · P(Ξᶜ)^{1/q}`.

`Ξ` is where (5.76) and (5.75) hold; `Env` is the deterministic envelope off it. -/
theorem momNorm_norm_lkT_le_of_event [IsProbabilityMeasure B.P] (X : Sample B) {E : ℝ}
    (hE : |E| < 2) {q : ℕ} (hq : q ≠ 0) {n : ℕ} (hW : SumZeroDyn.WardP X E n)
    {N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    {σ : Fin (n + 2) → Bool} (hqg : SumZeroDyn.QGood σ) (a : LoopArg (B.L N) (n + 2))
    {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} (hΞm : MeasurableSet Ξ)
    (hΞ1 : ∀ ω ∈ Ξ, X.xiLK E N v ω (n + 1) ≤ K * φ)
    (hΞ2 : ∀ ω ∈ Ξ, ∀ (ρ : Fin (n + 1) → Bool) b,
      X.lkErr E N v ω (LoopData.idx (ρ, b)) * SumZeroDyn.farInd (B.L N) (B.ell N v * K) b ≤ δ)
    {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hall : ∀ ω, ‖SumZeroDyn.lkT X E N v ω σ a‖ ≤ Env)
    (hPr : (B.P Ξᶜ).toReal ≤ pr)
    (hQint : Integrable
      (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖ ^ q) B.P)
    (hAint : Integrable (fun ω => |‖SumZeroDyn.lkT X E N v ω σ a‖| ^ q) B.P) :
    momNorm B.P q (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
      ≤ momNorm B.P q
          (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
        + pHalfBound B E N v n K φ δ + Env * pr ^ ((1 : ℝ) / q) := by
  have hd0 : 0 ≤ pHalfBound B E N v n K φ δ :=
    pHalfBound_nonneg hE N hv0 hv1 n hK.le hφ hδ
  have hA0 : 0 < B.scale E N v := B.scale_pos' hE N hv0 hv1
  have key := momNorm_le_affine_on_event (P := B.P) (q := q) hq
    (Y := fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
    (Z := fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
    (fun ω => norm_nonneg _) hQint hAint hΞm (c := 1) (d := pHalfBound B E N v n K φ δ)
    (Env := Env) (pr := pr) zero_le_one hd0 hEnv hpr (fun ω hω => ?_)
    (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hall ω) hPr
  · rwa [one_mul] at key
  · rw [abs_of_nonneg (norm_nonneg _), one_mul]
    have h1 := SumZeroDyn.norm_le_norm_Qop_add (B.L N) ((v : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N v ω σ) a
    have h2 := norm_Psum_lkT_mul_vartheta_le X hE hW hv0 hv1 hA0 hqg hK hφ hδ
      (hΞ1 ω hω) (hΞ2 ω hω) a
    linarith

/-- The same with both integrability premises discharged: `RBM.MomentDuhamel.Hyp.integrable`
gives the left-hand one and `RBM.MomentDuhamel.QIntegrable` (T214's field, a theorem on the
Gaussian model by `RBM.MomentDuhamel.qIntegrable_gauss`) the right-hand one.  The exponent is
the route's own `q = 2p`, with `p` fixed before `N`. -/
theorem momNorm_norm_lkT_le_of_hyp [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ}
    (hE : |E| < 2) {s t : ℕ → ℝ} {n : ℕ} (H : Hyp X E s t n) (hQint : QIntegrable X E s t n)
    {p : ℕ} (hp : 1 ≤ p) (hW : SumZeroDyn.WardP X E n)
    {N : ℕ} {v : ℝ} (hsv : s N ≤ v) (hvt : v ≤ t N) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {σ : Fin (n + 2) → Bool} (hqg : SumZeroDyn.QGood σ) (a : LoopArg (B.L N) (n + 2))
    {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} (hΞm : MeasurableSet Ξ)
    (hΞ1 : ∀ ω ∈ Ξ, X.xiLK E N v ω (n + 1) ≤ K * φ)
    (hΞ2 : ∀ ω ∈ Ξ, ∀ (ρ : Fin (n + 1) → Bool) b,
      X.lkErr E N v ω (LoopData.idx (ρ, b)) * SumZeroDyn.farInd (B.L N) (B.ell N v * K) b ≤ δ)
    {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hall : ∀ ω, ‖SumZeroDyn.lkT X E N v ω σ a‖ ≤ Env)
    (hPr : (B.P Ξᶜ).toReal ≤ pr) :
    momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
      ≤ momNorm B.P (2 * p)
          (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
        + pHalfBound B E N v n K φ δ + Env * pr ^ ((1 : ℝ) / (2 * p : ℕ)) := by
  have hQ' : Integrable
      (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖ ^ (2 * p)) B.P := by
    have h := hQint (2 * p) N v hsv hvt σ a
    simpa only [abs_norm] using h
  exact momNorm_norm_lkT_le_of_event X hE (by omega) hW hv0 hv1 hqg a hK hφ hδ hΞm hΞ1 hΞ2
    hEnv hpr hall hPr hQ' (H.integrable (2 * p) N v hsv hvt σ a)

end MomentHalf

/-! ### §4  The price of the good-event split

The loss of §3 is `Env · P(Ξᶜ)^{1/q}` with `q = 2p` **fixed** before `N → ∞`.  Taking the
`q`-th root turns a bound `N^{-D}` on the complement into `N^{-D/q}`, so a polynomial envelope
`Env ≤ N^{C_env}` is beaten only when `D > q C_env`.  `RBM.HighProb` gives *every* `D`, which
is exactly what is needed — and `RBM.Gauss.no_const_event_loss` shows nothing weaker is. -/

section EventPrice

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`HighProb` pays for the split.**  Quantifier order: `q` and `D` are fixed first, and the
`N`'s are eventual — never `∀ q N`. -/
theorem eventually_env_mul_prob_rpow_le [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ) {Env : ℕ → ℝ} {Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hEnvle : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Cenv)
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, Env N * ((P (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / q) ≤ (N : ℝ) ^ (-D) := by
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  have hDq : (0 : ℝ) < q * (D + Cenv) := by nlinarith
  filter_upwards [hΞ (q * (D + Cenv)) hDq, hEnvle, eventually_ge_atTop 1] with N hN hEN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-(q * (D + Cenv))) := Real.rpow_nonneg hN0.le _
  have hto : (P (Ξ N)ᶜ).toReal ≤ (N : ℝ) ^ (-(q * (D + Cenv))) :=
    ENNReal.toReal_le_of_le_ofReal hnn hN
  have hpow : ((P (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / q) ≤ (N : ℝ) ^ (-(D + Cenv)) := by
    refine (Real.rpow_le_rpow ENNReal.toReal_nonneg hto (by positivity)).trans (le_of_eq ?_)
    rw [← Real.rpow_mul hN0.le]
    congr 1
    field_simp
  calc Env N * ((P (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / q)
      ≤ (N : ℝ) ^ Cenv * (N : ℝ) ^ (-(D + Cenv)) := by
        refine mul_le_mul hEN hpow (Real.rpow_nonneg ENNReal.toReal_nonneg _) ?_
        exact Real.rpow_nonneg hN0.le _
    _ = (N : ℝ) ^ (-D) := by
        rw [← Real.rpow_add hN0]; congr 1; ring

/-- The same, with the quantifier order the moment route uses: the exponent is `q = 2p` and
`p` is fixed **before** `N → ∞` (`∀ p, ∀ᶠ N`, never `∀ p N`). -/
theorem eventually_env_mul_prob_rpow_le_moment [IsProbabilityMeasure P]
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ) {Env : ℕ → ℝ} {Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hEnvle : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Cenv) :
    ∀ p : ℕ, 1 ≤ p → ∀ D > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
        Env N * ((P (Ξ N)ᶜ).toReal) ^ ((1 : ℝ) / (2 * p : ℕ)) ≤ (N : ℝ) ^ (-D) :=
  fun p hp D hD =>
    eventually_env_mul_prob_rpow_le (q := 2 * p) (by omega) hΞ hCenv hEnvle hD

/-- **The split is not free.**  If the complement is only known to be `≤ N^{-D}` for a *fixed*
`D`, then with a polynomial envelope `N^{C_env}` the loss `Env · pr^{1/q}` has **no**
`N`-independent bound as soon as `D < q C_env`.  So the premise really has to be
`RBM.HighProb`, and `q = 2p` really has to be fixed before `D` is chosen. -/
theorem no_const_event_loss {q : ℕ} (hq : q ≠ 0) {Cenv D : ℝ}
    (hDq : D < q * Cenv) {C : ℝ}
    (h : ∀ N : ℕ, (N : ℝ) ^ Cenv * ((N : ℝ) ^ (-D)) ^ ((1 : ℝ) / q) ≤ C) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hexp : 0 < Cenv - D / q := by
    rw [sub_pos, div_lt_iff₀ hq0]
    linarith
  have htop : Tendsto (fun N : ℕ => (N : ℝ) ^ (Cenv - D / q)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN, hN0⟩ := ((htop.eventually_gt_atTop C).and (eventually_gt_atTop 0)).exists
  refine absurd (h N) (not_le.mpr ?_)
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hrw : (N : ℝ) ^ Cenv * ((N : ℝ) ^ (-D)) ^ ((1 : ℝ) / q)
      = (N : ℝ) ^ (Cenv - D / q) := by
    rw [← Real.rpow_mul hN0'.le, ← Real.rpow_add hN0']
    congr 1
    field_simp
    ring
  rw [hrw]
  exact hN

end EventPrice

/-! ### §5  The composition: `Q` half + `P` half ⇒ `‖(L-K)_v‖`

The two halves carry the shapes their producers give them: the `Q` half comes from
`RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` with no normalising weight, the `P` half from
`RBM.SumZeroDyn.termP` with the weight `(Wℓ_vη_v)^{n+2}` and the `QGood` guard of §5.5.  The
guard is the paper's own case split: §5.5 uses `Q_v` precisely for the charges where Ward's
identity applies; `RBM.SumZeroDyn.bound_nonAlt` is the other branch. -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

open RBM.MomentDuhamel

/-- **(5.101) for `≺`, with the flow's `QGood` guard and normalisation.**  This is §1 in the
shape the two producers deliver. -/
theorem stochDom_norm_lkT_qGood (X : Sample B) {E : ℝ} {n : ℕ} {v : ℕ → ℝ}
    {c : ℕ → ℝ} (hc : ∀ N, 0 ≤ c N)
    {ζQ ζP : ∀ N, LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hQ : StochDom B.P (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then
          c N * ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω w.1) w.2‖
        else 0) ζQ)
    (hP : StochDom B.P (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then
          c N * (‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω w.1) (w.2 0)‖
            * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) w.2‖)
        else 0) ζP) :
    StochDom B.P (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then c N * ‖SumZeroDyn.lkT X E N (v N) ω w.1 w.2‖ else 0)
      (ζQ + ζP) := by
  refine StochDom.of_le_left (fun N w ω => ?_) (hQ.add hP)
  simp only [Pi.add_apply]
  split_ifs with hqg
  · have h := SumZeroDyn.norm_le_norm_Qop_add (B.L N) ((v N : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N (v N) ω w.1) w.2
    nlinarith [mul_le_mul_of_nonneg_left h (hc N)]
  · rw [add_zero]

/-- **D14 ①, assembled.**  The `Q` half is the hypothesis `hQ` — in the application it is the
conclusion of `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ`; the `P` half is supplied here by
`RBM.SumZeroDyn.termP`, which is a **theorem** (Ward's (5.96) plus the a priori bounds), not a
new field.  The conclusion is a `≺` for the normalised `|(L-K)_{v,σ,a}|` itself. -/
theorem stochDom_scale_norm_lkT_of_momentDuhamelQ (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t) {n : ℕ} (hW : SumZeroDyn.WardP X E n)
    (hdec : SumZeroDyn.LKDecay X E s t) {Φ : ℕ → ℝ} (hΦ0 : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N))
    {v : ℕ → ℝ} (hv1 : ∀ N, s N ≤ v N) (hv2 : ∀ N, v N ≤ t N)
    {ΦQ : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hQ : StochDom B.P (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω w.1) w.2‖)
      (fun N w _ => ΦQ N w)) :
    StochDom B.P
      (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then
          B.scale E N (v N) ^ (n + 2) * ‖SumZeroDyn.lkT X E N (v N) ω w.1 w.2‖ else 0)
      ((fun N (w : LoopData (B.L N) (n + 2)) (_ : Ω) =>
          B.scale E N (v N) ^ (n + 2) * ΦQ N w)
        + fun N (_ : LoopData (B.L N) (n + 2)) (_ : Ω) => 1 + Φ N) := by
  classical
  have hsc : ∀ N, 0 ≤ B.scale E N (v N) ^ (n + 2) := fun N =>
    (pow_nonneg (B.scale_pos' hE N (((hs0 N).le).trans (hv1 N)) ((hv2 N).trans_lt (ht1 N))).le _)
  -- the `Q` half, normalised and guarded
  have hQw : StochDom B.P
      (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        B.scale E N (v N) ^ (n + 2)
          * ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω w.1) w.2‖)
      (fun N w (_ : Ω) => B.scale E N (v N) ^ (n + 2) * ΦQ N w) := by
    have hrefl : StochDom B.P
        (fun N (w : LoopData (B.L N) (n + 2)) (_ : Ω) => B.scale E N (v N) ^ (n + 2))
        (fun N (w : LoopData (B.L N) (n + 2)) (_ : Ω) => B.scale E N (v N) ^ (n + 2)) :=
      StochDom.refl fun N _ _ => hsc N
    exact StochDom.mul (fun N _ _ => norm_nonneg _) (fun N _ _ => hsc N) hrefl hQ
  have hQg : StochDom B.P
      (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then
          B.scale E N (v N) ^ (n + 2)
            * ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω w.1) w.2‖ else 0)
      (fun N w (_ : Ω) => B.scale E N (v N) ^ (n + 2) * ΦQ N w) := by
    refine StochDom.of_le_left (fun N w ω => ?_) hQw
    split_ifs with hqg
    · exact le_rfl
    · exact mul_nonneg (hsc N) (norm_nonneg _)
  -- the `P` half: `RBM.SumZeroDyn.termP`, restricted to the time `v N`
  have hPfull := SumZeroDyn.termP X hE hs0 hst ht1 hcond hW hdec hΦ0 hX
  have hPw := hPfull.precomp_param
    (V := fun N => LoopData (B.L N) (n + 2))
    (fun N w => ((⟨v N, hv1 N, hv2 N⟩ : TimeIcc s t N), w))
  exact stochDom_norm_lkT_qGood X hsc hQg hPw

/-- **D14 ① end to end.**  `RBM.MomentDuhamel.Hyp.momentDuhamelQ` (via T214's
`RBM.MomentDuhamel.stochDom_of_momentDuhamelQ`) on one side, Ward's (5.96) via
`RBM.SumZeroDyn.termP` on the other, and `‖(L-K)_v‖` on the left. -/
theorem stochDom_scale_norm_lkT_of_hyp [IsProbabilityMeasure B.P]
    {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t) {n : ℕ} (hW : SumZeroDyn.WardP X E n)
    (hdec : SumZeroDyn.LKDecay X E s t) {Φ : ℕ → ℝ} (hΦ0 : ∀ N, 0 ≤ Φ N)
    (hXi : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N))
    (H : Hyp X E s t n) (hQint : QIntegrable X E s t n)
    (v : ℕ → ℝ) (hv1 : ∀ N, s N ≤ v N) (hv2 : ∀ N, v N ≤ t N)
    {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {ΦQ : ∀ N, LoopData (B.L N) (n + 2) → ℝ} (hΦQ : ∀ N w, 0 < ΦQ N w)
    (hrhs : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ w : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) w.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω w.1)) w.2‖)
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) w.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) w.1)) w.2‖))
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) w.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) w.1) ((u : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N u ω w.1)) w.2‖))
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) w.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω w.1) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) w.2‖))
          + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E w.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) w.1))
                (Fin.append w.2 w.2)‖)) ^ ((1 : ℝ) / 2)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦQ N w)) :
    StochDom B.P
      (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then
          B.scale E N (v N) ^ (n + 2) * ‖SumZeroDyn.lkT X E N (v N) ω w.1 w.2‖ else 0)
      ((fun N (w : LoopData (B.L N) (n + 2)) (_ : Ω) =>
          B.scale E N (v N) ^ (n + 2) * ΦQ N w)
        + fun N (_ : LoopData (B.L N) (n + 2)) (_ : Ω) => 1 + Φ N) :=
  stochDom_scale_norm_lkT_of_momentDuhamelQ X hE hs0 hst ht1 hcond hW hdec hΦ0 hXi hv1 hv2
    (stochDom_of_momentDuhamelQ H hQint v hv1 hv2 hcard hΦQ hrhs)

end Assembly

/-! ### §6  Satisfiability: both halves of (5.101) are non-degenerate

Risk (a) of D14 ① is that the `P` half gets bounded by `0`, which would make the composition
say nothing beyond the `Q` half; the mirror risk is that `Q_v` kills everything, which T201's
`RBM.Gauss.witTensor` already rules out.  The witness below rules out both at once: it is
`witTensor + ϑ_v`, whose `Q_v` image is exactly `witTensor` (non-zero) and whose slot sums are
**exactly `1`** (`RBM.Psum_vartheta`).  Its scale is the critical one of
`RBM.Gauss.gridS_Q716_witness`, and `v ↑ 1` is allowed. -/

section Witness

/-- **The `QGood` guard of §5.5 is not vacuous.**  At every loop length the charge
`σ = (+, -, …, -)` is `QGood` (take `j` the last slot, where `σ_j = -` and `σ_{j+1} = σ_0 = +`),
so the guarded conclusions of §5 are not statements about the zero function. -/
theorem qGood_charge (n : ℕ) :
    SumZeroDyn.QGood (fun i : Fin (n + 2) => decide (i = 0)) := by
  have hne : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.last] at this
  refine ⟨Fin.last (n + 1), hne, ?_, ?_⟩
  · simp [hne]
  · rw [Fin.last_add_one]
    simp

variable (L : ℕ) [NeZero L]

/-- The witness for the composed (5.101) bound: T201's sum-zero `witTensor` plus the reference
tensor `ϑ_t` of Definition 5.12.  Neither half of (5.101) is trivial on it. -/
noncomputable def qpWit (m : ℕ) (κ : ℂ) (t : ℂ) : LoopArg L (m + 2) → ℂ :=
  fun b => witTensor L m κ b + vartheta L (n := m + 1) t b

/-- **The `P` half of the witness is exactly `1`** — not `0`. -/
theorem Psum_qpWit (hL : 3 ≤ L) {m : ℕ} (κ : ℂ) {t : ℂ} (ht : ‖t‖ < 1) (x : ZMod L) :
    Psum L (qpWit L m κ t) x = 1 := by
  have hsplit : Psum L (qpWit L m κ t) x
      = Psum L (witTensor L m κ) x + Psum L (vartheta L (n := m + 1) t) x := by
    simp only [Psum, qpWit]
    exact Finset.sum_add_distrib
  rw [hsplit, sumZero_witTensor L hL κ x, Psum_vartheta L hL ht x, zero_add]

/-- **The `Q` half of the witness is exactly `witTensor`** — hence non-zero. -/
theorem Qop_qpWit (hL : 3 ≤ L) {m : ℕ} (κ : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    Qop L t (qpWit L m κ t) = witTensor L m κ := by
  funext a
  rw [Qop, Psum_qpWit L hL κ ht, one_mul, qpWit]
  ring

theorem Qop_qpWit_ne_zero (hL : 3 ≤ L) {m : ℕ} {κ : ℂ} (hκ : κ ≠ 0) {t : ℂ} (ht : ‖t‖ < 1) :
    Qop L t (qpWit L m κ t) ≠ 0 := by
  rw [Qop_qpWit L hL κ ht]
  exact witTensor_ne_zero L hL hκ

end Witness

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- **The satisfiability witness for D14 ① (T218).**

At a time `v` of the window — `v ↑ 1` is allowed, only `0 ≤ v < 1` is used — and at the
**critical** normalisation `κ = (κ_A (1-v) ℓ_v)^{-(m+2)}` of `RBM.Gauss.gridS_Q716_witness`:

1. `Q_v` does **not** kill the witness (its image is T201's non-zero `witTensor`);
2. the `P` half is **exactly `1`**, so the second summand of (5.101) is genuinely present —
   the composition is not the `Q` half in disguise;
3. (5.101) in moment form holds on the nose, with the `ϑ_v` bound `(C/ℓ_v)^{m+1}` of (5.87)
   as the `P`-half cost and no good-event loss (`Ξ = univ`, `pr = 0`).

Conjunct 3 is the deterministic instance of `RBM.Gauss.momNorm_norm_lkT_le_of_event`: its
`P`-half constant is the same `RBM.SumZeroDyn.norm_vartheta_real_le` factor, so this pins down
that the composed bound is attained, not merely available. -/
theorem qpWit_route_witness [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {m : ℕ} {κA : ℝ} (hκA : 0 < κA) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (a : LoopArg L (m + 2)) :
    (Qop L ((v : ℝ) : ℂ)
        (qpWit L m (((κA * ((1 - v) * ellHat L ((v : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
          ((v : ℝ) : ℂ)) ≠ 0)
    ∧ (∀ x, Psum L (qpWit L m (((κA * ((1 - v) * ellHat L ((v : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
        ((v : ℝ) : ℂ)) x = 1)
    ∧ momNorm P q (fun _ω : Ω =>
        ‖qpWit L m (((κA * ((1 - v) * ellHat L ((v : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
          ((v : ℝ) : ℂ) a‖)
      ≤ momNorm P q (fun _ω : Ω =>
          ‖Qop L ((v : ℝ) : ℂ)
            (qpWit L m (((κA * ((1 - v) * ellHat L ((v : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
              ((v : ℝ) : ℂ)) a‖)
        + (cTwo52 / ellHat L ((v : ℝ) : ℂ)) ^ (m + 1) := by
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have hℓ : 0 < ellHat L ((v : ℝ) : ℂ) := SumZeroDyn.ellHat_real_pos' L hL hv0 hv1
  set c0 : ℝ := (κA * ((1 - v) * ellHat L ((v : ℝ) : ℂ)))⁻¹ ^ (m + 2) with hc0def
  have hc00 : 0 < c0 := by rw [hc0def]; positivity
  have hκ : ((c0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc00.ne'
  have ht : ‖((v : ℝ) : ℂ)‖ < 1 := SumZeroDyn.norm_ofReal_lt_one hv0 hv1
  refine ⟨Qop_qpWit_ne_zero L hL hκ ht, fun x => Psum_qpWit L hL _ ht x, ?_⟩
  -- the deterministic instance: both moment norms are constants
  have hd0 : (0 : ℝ) ≤ (cTwo52 / ellHat L ((v : ℝ) : ℂ)) ^ (m + 1) := by
    have := cTwo52_pos; positivity
  rw [momNorm_const hq (norm_nonneg _), momNorm_const hq (norm_nonneg _)]
  have h1 := SumZeroDyn.norm_le_norm_Qop_add L ((v : ℝ) : ℂ)
    (qpWit L m ((c0 : ℝ) : ℂ) ((v : ℝ) : ℂ)) a
  rw [Psum_qpWit L hL _ ht, norm_one, one_mul] at h1
  have h2 := SumZeroDyn.norm_vartheta_real_le L hL (n := m + 1) hv0 hv1 a
  linarith

end GridWitness

end RBM.Gauss

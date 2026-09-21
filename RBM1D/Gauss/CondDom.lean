/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.IBP
import RBM1D.Gauss.MinorReplace

/-!
# `≺` under the conditional expectation `E_k`, and the two inputs of `hIBP`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, p. 50.

## Why `≺` does not simply pass through `E_k`

Definition 2.1 (i) carries an **exceptional event**: `X ≺ Y` says only that
`P(|X| > N^τ Y) ≤ N^{-D}`, and says *nothing* about the size of `X` there.  Integrating over
row `k` does not make that event disappear — `E_k[1_{bad} X]` has no a priori smallness — so
"`X ≺ Y` implies `E_k[X] ≺ Y`" is **false as stated**.  Two things have to be added.

1. A **deterministic envelope** `‖X ω‖ ≤ Env N` valid on the *whole* space.  Along the flow
   `z_t` of (2.35) this is free: `Im z_t = η_t > 0`, so `‖G_t‖_op ≤ η_t⁻¹` pointwise in `ω`
   (`RBM.Gauss.norm_green_zt_le`, T77).  With it, the bad part of the row integral is at most
   `Env(N) · P(slice)`, where `slice` is the row-`k` section of the bad event.
2. A way to make `P(slice)` small.  For a *fixed* `ω` the section can have probability one;
   what is true is the Fubini identity
   `∫ P(slice_ω) dP(ω) = P(bad)` (`RBM.Gauss.lintegral_measure_rowSlice`, which is exactly
   `RBM.Gauss.measurePreserving_rowSplit` of T84), and then Markov moves the smallness of the
   *average* to smallness *outside a small set of `ω`*
   (`RBM.Gauss.meas_measure_rowSlice_ge`).

The same accounting as T77's `RBM1D/Gauss/Envelope.lean`: a good-event bound, plus an envelope
on the complement, plus a quantitative bound on the probability of the complement.

Finally, the control itself has to survive the row integral.  Writing `E_k` out as the exact
coordinate integral of T84 gives

  `‖E_k[X](ω)‖ ≤ N^τ · E_k[ζ](ω) + Env(N) · P(slice_ω)`,

so the natural conclusion is a bound by `E_k[ζ]`, not by `ζ`.  `RBM.Gauss.CondStable` names the
missing comparison `E_k[ζ] ≺ χ` (together with the integrability that makes `E_k[ζ]` an honest
integral); for a control that does not read row `k` — a minor observable, or a deterministic
`Ψ²` — it is trivially satisfied (`RBM.Gauss.CondStable.of_det`,
`RBM.Gauss.CondStable.of_finDepOffRow`).

## Main results

* `RBM.Gauss.condRowReal` — `E_k` of a real observable, the exact row integral of T84.
* `RBM.Gauss.lintegral_measure_rowSlice`, `RBM.Gauss.meas_measure_rowSlice_ge` — the Fubini
  identity for the row section of a set, and Markov applied to it.
* `RBM.Gauss.norm_condRow_le_split` — the pointwise good/bad split of the row integral.
* `RBM.Gauss.stochDom_condRow_of_envelope` — **the general tool**: `‖X‖ ≺ ζ`, a deterministic
  envelope of polynomial growth, `E_k[ζ] ≺ χ` and `N^{-B} ≺ χ` give `‖E_k[X]‖ ≺ χ`.
* `RBM.Gauss.CondStable.of_det`, `RBM.Gauss.CondStable.of_finDepOffRow` — the two cases in
  which the control comparison is automatic.
* `RBM.Gauss.stochDom_condRow_sub_self` — `‖E_k[X] - X‖ ≺ χ` from a row-`k`-independent
  surrogate `X'` with `‖X - X'‖ ≺ ζ`: the shape of the minor replacement (4.9).
* `RBM.Gauss.measurable_Lmax`, `RBM.Gauss.stochDom_rpow_neg_one_Lmax` — the two facts about the
  paper's control `RBM.Lmax` that the tool needs.
* `RBM.Gauss.hprod_of_localLaw` — `hprod` of `RBM.Gauss.condExpDiag_stochDom_of_pieces`, at its
  frozen signature.
* `RBM.Gauss.hminor_offdiag_of_repl` — `hminor`, **off the diagonal**.  On the diagonal the
  statement `E_i(G_{ii}-m) - (G_{ii}-m) ≺ Ψ²` is *false* (the left side is the fluctuation
  `-(1 - E_i)(G_{ii}-m)`, of size `Ψ`), so `RBM.Gauss.condExpDiag_stochDom_of_pieces` cannot be
  used as it stands; see `docs/paper-deltas.md`.
* `RBM.Gauss.norm_condExpDiag_sub_le_offdiag`, `RBM.Gauss.condExpDiag_stochDom_of_offdiag` — the
  weighted reduction that repairs this: the diagonal term carries the coefficient
  `S_{ii} ≤ 2 L_max`, so the deterministic envelope of `RBM.Gauss.ibpRem` suffices for it.
* `RBM.Gauss.condExpDiag_stochDom_of_localLaw` — **`hIBP`**, at the exact frozen signature of
  `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`; and
  `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom_of_localLaw`, the compile-time check that it
  really fits the slot.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

variable {d : Dims} {N : ℕ}

/-! ### `E_k` of a real observable -/

/-- **`E_k[f]` for a real-valued `f`**, the same exact coordinate integral as
`RBM.Gauss.condRow`: integrate the row-`k` coordinates out and freeze the others.  No
`MeasureTheory.condExp` is involved, and the identity is pointwise in `ω`. -/
noncomputable def condRowReal (d : Dims) (N : ℕ) (k : d.Idx N) (f : Ω d → ℝ) : Ω d → ℝ :=
  fun ω => ∫ ω', f (rowSplit d N k ω ω') ∂(P d)

theorem condRowReal_apply (k : d.Idx N) (f : Ω d → ℝ) (ω : Ω d) :
    condRowReal d N k f ω = ∫ ω', f (rowSplit d N k ω ω') ∂(P d) := rfl

theorem condRowReal_nonneg {k : d.Idx N} {f : Ω d → ℝ} (hf : ∀ ω, 0 ≤ f ω) (ω : Ω d) :
    0 ≤ condRowReal d N k f ω :=
  integral_nonneg fun _ => hf _

/-- A real observable that does not read row `k` is its own `E_k`. -/
theorem condRowReal_of_finDepOffRow {k : d.Idx N} {f : Ω d → ℝ}
    (h : FinDepOffRow d N k f) : condRowReal d N k f = f := by
  funext ω
  have hf : (fun ω' => f (rowSplit d N k ω ω')) = fun _ => f ω := by
    funext ω'; exact h.rowSplit_eq ω ω'
  simp [condRowReal, hf]

@[simp] theorem condRowReal_const (k : d.Idx N) (c : ℝ) :
    condRowReal d N k (fun _ => c) = fun _ => c := by
  funext ω; simp [condRowReal]

/-! ### The row section of a set, and its measure -/

/-- The **row-`k` section** of `S` at `ω`: the `ω'` for which the split point `rowSplit k ω ω'`
lands in `S`.  `E_k[1_S](ω)` is its probability. -/
def rowSlice (d : Dims) (N : ℕ) (k : d.Idx N) (S : Set (Ω d)) (ω : Ω d) : Set (Ω d) :=
  {ω' | rowSplit d N k ω ω' ∈ S}

theorem measurableSet_rowSlice {k : d.Idx N} {S : Set (Ω d)} (hS : MeasurableSet S) (ω : Ω d) :
    MeasurableSet (rowSlice d N k S ω) :=
  hS.preimage (measurable_rowSplit_right d N k ω)

theorem measurable_measure_rowSlice (d : Dims) (N : ℕ) (k : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) : Measurable fun ω => (P d) (rowSlice d N k S ω) := by
  have hpre : MeasurableSet ((fun p : Ω d × Ω d => rowSplit d N k p.1 p.2) ⁻¹' S) :=
    hS.preimage (measurable_rowSplit d N k)
  exact measurable_measure_prodMk_left hpre

/-- **The Fubini identity for the row section.**  Averaging the probability of the section over
the frozen coordinates returns the probability of the set itself.  This is
`RBM.Gauss.measurePreserving_rowSplit` of T84, and it is the reason the exceptional event of
Definition 2.1 (i) can be controlled *after* conditioning. -/
theorem lintegral_measure_rowSlice (d : Dims) (N : ℕ) (k : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) :
    ∫⁻ ω, (P d) (rowSlice d N k S ω) ∂(P d) = (P d) S := by
  have hmeas := measurable_rowSplit d N k
  have hpre : MeasurableSet ((fun p : Ω d × Ω d => rowSplit d N k p.1 p.2) ⁻¹' S) :=
    hS.preimage hmeas
  have h1 : (P d) S
      = ((P d).prod (P d)) ((fun p : Ω d × Ω d => rowSplit d N k p.1 p.2) ⁻¹' S) := by
    conv_lhs => rw [← (measurePreserving_rowSplit d N k).map_eq]
    exact Measure.map_apply hmeas hS
  rw [h1, Measure.prod_apply hpre]
  rfl

/-- **Markov for the row section.**  The set of frozen configurations whose section is not small
is itself small: `ε · P{ω : P(slice_ω) ≥ ε} ≤ P(S)`. -/
theorem meas_measure_rowSlice_ge (d : Dims) (N : ℕ) (k : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) (ε : ℝ≥0∞) :
    ε * (P d) {ω | ε ≤ (P d) (rowSlice d N k S ω)} ≤ (P d) S := by
  have h := mul_meas_ge_le_lintegral₀
    (μ := P d) (measurable_measure_rowSlice d N k hS).aemeasurable ε
  rwa [lintegral_measure_rowSlice d N k hS] at h

/-! ### The pointwise good/bad split of a row integral

This is T77's accounting (`RBM1D/Gauss/Envelope.lean`), transplanted from the integral over the
whole space to the integral over one row: on the good set the integrand obeys `‖X‖ ≤ c f`, and
on the bad set it obeys only the deterministic envelope, whose contribution is the envelope
times the probability of the row section. -/

/-- **The split.**  If `‖X‖ ≤ c f` off a set `S` and `‖X‖ ≤ Env` everywhere, then

  `‖E_k[X](ω)‖ ≤ c E_k[f](ω) + Env · P(slice of S at ω)`. -/
theorem norm_condRow_le_split {k : d.Idx N} {X : Ω d → ℂ} (hX : Measurable X)
    {f : Ω d → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hfint : ∀ ω : Ω d, Integrable (fun ω' => f (rowSplit d N k ω ω')) (P d))
    {Env c : ℝ} (hEnv : ∀ σ, ‖X σ‖ ≤ Env) (hc : 0 ≤ c)
    {S : Set (Ω d)} (hS : MeasurableSet S)
    (hgood : ∀ σ, σ ∉ S → ‖X σ‖ ≤ c * f σ) (ω : Ω d) :
    ‖condRow d N k X ω‖
      ≤ c * condRowReal d N k f ω + Env * (P d).real (rowSlice d N k S ω) := by
  have hsm := measurable_rowSplit_right d N k ω
  have hSω : MeasurableSet (rowSlice d N k S ω) := measurableSet_rowSlice hS ω
  have hXint : Integrable (fun ω' => X (rowSplit d N k ω ω')) (P d) :=
    Integrable.mono' (integrable_const Env) ((hX.comp hsm).aestronglyMeasurable)
      (Eventually.of_forall fun _ => hEnv _)
  have hindint : Integrable ((rowSlice d N k S ω).indicator fun _ => Env) (P d) :=
    (integrable_const Env).indicator hSω
  have hcf : Integrable (fun ω' => c * f (rowSplit d N k ω ω')) (P d) := (hfint ω).const_mul c
  have hpt : ∀ ω' : Ω d, ‖X (rowSplit d N k ω ω')‖
      ≤ c * f (rowSplit d N k ω ω')
        + (rowSlice d N k S ω).indicator (fun _ => Env) ω' := by
    intro ω'
    by_cases hω' : ω' ∈ rowSlice d N k S ω
    · rw [Set.indicator_of_mem hω']
      have h1 := hEnv (rowSplit d N k ω ω')
      have h2 : 0 ≤ c * f (rowSplit d N k ω ω') := mul_nonneg hc (hf0 _)
      linarith
    · rw [Set.indicator_of_notMem hω']
      have h1 := hgood (rowSplit d N k ω ω') hω'
      linarith
  rw [condRow_apply]
  calc ‖∫ ω', X (rowSplit d N k ω ω') ∂(P d)‖
      ≤ ∫ ω', ‖X (rowSplit d N k ω ω')‖ ∂(P d) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω', (c * f (rowSplit d N k ω ω')
        + (rowSlice d N k S ω).indicator (fun _ => Env) ω') ∂(P d) :=
        integral_mono hXint.norm (hcf.add hindint) hpt
    _ = c * condRowReal d N k f ω + Env * (P d).real (rowSlice d N k S ω) := by
        rw [integral_add hcf hindint, integral_const_mul,
          integral_indicator_const _ hSω, smul_eq_mul, mul_comm ((P d).real _) Env]
        rfl

/-! ### The general tool -/

section Tool

variable {U : ℕ → Type*}

/-- **The control survives the row integral.**  `E_k[X]` can only ever be dominated by something
that dominates `E_k[ζ]`, so the general tool needs this comparison as an input.  It is *not* a
consequence of `ζ ≺ ζ`: `ζ` may read row `k`.

Two cases where it is free: a **deterministic** control (`CondStable.of_det`, the paper's `Ψ²`)
and a control that does not read row `k` (`CondStable.of_finDepOffRow`, e.g. anything read off
the minor `H^{(k)}`). -/
structure CondStable (d : Dims) (U : ℕ → Type*) (k : ∀ N, U N → d.Idx N)
    (ζ χ : ∀ N, U N → Ω d → ℝ) : Prop where
  /-- `E_k[ζ]` is an honest integral: `ζ` is integrable along row `k` for every frozen `ω`. -/
  rowIntegrable : ∀ (N : ℕ) (u : U N) (ω : Ω d),
    Integrable (fun ω' => ζ N u (rowSplit d N (k N u) ω ω')) (P d)
  /-- `E_k[ζ] ≺ χ`. -/
  dom : StochDom (P d) (fun N u ω => condRowReal d N (k N u) (ζ N u) ω) χ

/-- A deterministic control is `E_k`-stable: `E_k` of a constant is that constant. -/
theorem CondStable.of_det (k : ∀ N, U N → d.Idx N) {Φ : ∀ N, U N → ℝ}
    (hΦ : ∀ N (u : U N), 0 ≤ Φ N u) :
    CondStable d U k (fun N u _ => Φ N u) (fun N u _ => Φ N u) where
  rowIntegrable := fun _ _ _ => integrable_const _
  dom := by
    have h : (fun N (u : U N) (ω : Ω d) => condRowReal d N (k N u) (fun _ => Φ N u) ω)
        = fun N (u : U N) (_ : Ω d) => Φ N u := by
      funext N u ω; simp [condRowReal]
    rw [h]
    exact StochDom.refl fun N u _ => hΦ N u

/-- A control that does not read row `k` is `E_k`-stable: `E_k` leaves it alone. -/
theorem CondStable.of_finDepOffRow {k : ∀ N, U N → d.Idx N} {ζ : ∀ N, U N → Ω d → ℝ}
    (hζ0 : ∀ N (u : U N) (ω : Ω d), 0 ≤ ζ N u ω)
    (hfd : ∀ (N : ℕ) (u : U N), FinDepOffRow d N (k N u) (ζ N u)) :
    CondStable d U k ζ ζ where
  rowIntegrable := fun N u ω => by
    have h : (fun ω' => ζ N u (rowSplit d N (k N u) ω ω')) = fun _ => ζ N u ω := by
      funext ω'; exact (hfd N u).rowSplit_eq ω ω'
    rw [h]; exact integrable_const _
  dom := by
    have h : (fun N (u : U N) ω => condRowReal d N (k N u) (ζ N u) ω) = ζ := by
      funext N u; exact condRowReal_of_finDepOffRow (hfd N u)
    rw [h]
    exact StochDom.refl hζ0

/-- **`≺` under the conditional expectation `E_k`.**

If

* `‖X‖ ≺ ζ` (Definition 2.1 (i)),
* `X` has a **deterministic envelope** of polynomial growth, `‖X(N,u,ω)‖ ≤ Env(N) ≤ N^{K}` for
  *every* `ω` — along the flow this is free, `‖G_t‖ ≤ η_t⁻¹` (`RBM.Gauss.norm_green_zt_le`),
* the control is `E_k`-stable, `E_k[ζ] ≺ χ` (`RBM.Gauss.CondStable`),
* and `χ` is not super-polynomially small, `N^{-B} ≺ χ`,

then `‖E_k[X]‖ ≺ χ`.

All four hypotheses are needed.  The first alone is not enough (the exceptional event of
Definition 2.1 (i) survives the row integral), the envelope alone is not enough (it is of size
`η_t⁻¹`, not of size `Ψ`), and the last two are what let the two error terms
`N^{τ} E_k[ζ]` and `Env(N) · P(slice)` be compared with `χ`.

The proof is the T77 accounting (`RBM1D/Gauss/Envelope.lean`) run one row at a time:
`RBM.Gauss.norm_condRow_le_split` splits the row integral, and
`RBM.Gauss.meas_measure_rowSlice_ge` — Fubini for `RBM.Gauss.rowSplit` followed by Markov —
says that the row section of the exceptional event is small outside a small set of `ω`. -/
theorem stochDom_condRow_of_envelope [∀ N, Fintype (U N)]
    {X : ∀ N, U N → Ω d → ℂ} {ζ χ : ∀ N, U N → Ω d → ℝ} {k : ∀ N, U N → d.Idx N}
    {Env : ℕ → ℝ} {Kenv B Ccard : ℝ} (hCcard : 0 ≤ Ccard)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (hXmeas : ∀ (N : ℕ) (u : U N), Measurable (X N u))
    (hζmeas : ∀ (N : ℕ) (u : U N), Measurable (ζ N u))
    (hζ0 : ∀ (N : ℕ) (u : U N) (ω : Ω d), 0 ≤ ζ N u ω)
    (hχ0 : ∀ (N : ℕ) (u : U N) (ω : Ω d), 0 ≤ χ N u ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω d), ‖X N u ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hlow : StochDom (P d) (fun N (_ : U N) (_ : Ω d) => (N : ℝ) ^ (-B)) χ)
    (hstab : CondStable d U k ζ χ)
    (hdom : StochDom (P d) (fun N u ω => ‖X N u ω‖) ζ) :
    StochDom (P d) (fun N u ω => ‖condRow d N (k N u) (X N u) ω‖) χ := by
  classical
  intro τ hτ D hD
  have hτ3 : 0 < τ / 3 := by linarith
  set M : ℝ := Kenv + B with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  set D₁ : ℝ := Ccard + M + D + 2 with hD₁def
  have hD₁0 : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hcard, hEnvpoly, hdom (τ / 3) hτ3 D₁ hD₁0,
    hstab.dom (τ / 3) hτ3 (D + 2) (by linarith),
    hlow (τ / 3) hτ3 (D + 2) (by linarith), eventually_ge_atTop 1,
    eventually_le_rpow 2 hτ3, eventually_two_mul_rpow_le (D + 1),
    eventually_two_mul_rpow_le D] with
    N hcardN hEnvN hbadN hstabN hlowN hN1 h2N hdbl1 hdbl2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- the exceptional set of `hdom`
  set S : Set (Ω d) := badSet (fun N (u : U N) ω => ‖X N u ω‖) ζ (τ / 3) N with hSdef
  have hSmeas : MeasurableSet S := by
    have hS : S = ⋃ u : U N, {ω | (N : ℝ) ^ (τ / 3) * ζ N u ω < ‖X N u ω‖} := by
      ext ω; simp [hSdef, badSet]
    rw [hS]
    exact MeasurableSet.iUnion fun u =>
      measurableSet_lt (measurable_const.mul (hζmeas N u)) ((hXmeas N u).norm)
  set ε : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ) ^ (-M)) with hεdef
  have hεpos : (0 : ℝ) < (N : ℝ) ^ (-M) := Real.rpow_pos_of_pos hNpos _
  have hε0 : ε ≠ 0 := by
    rw [hεdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hεpos
  -- the three exceptional sets
  set A1 : Set (Ω d) := {ω | ∃ u : U N, ε ≤ (P d) (rowSlice d N (k N u) S ω)} with hA1def
  set A2 : Set (Ω d) :=
    badSet (fun N (u : U N) ω => condRowReal d N (k N u) (ζ N u) ω) χ (τ / 3) N with hA2def
  set A3 : Set (Ω d) :=
    badSet (fun N (_ : U N) (_ : Ω d) => (N : ℝ) ^ (-B)) χ (τ / 3) N with hA3def
  -- `A1` is small: Fubini plus Markov for the row section
  have hA1small : (P d) A1 ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    have hslice : ∀ u : U N, (P d) {ω | ε ≤ (P d) (rowSlice d N (k N u) S ω)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (M - D₁)) := by
      intro u
      have h2 : ε * (P d) {ω | ε ≤ (P d) (rowSlice d N (k N u) S ω)}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) :=
        (meas_measure_rowSlice_ge d N (k N u) hSmeas ε).trans hbadN
      rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.ofReal_ne_top)] at h2
      refine h2.trans (le_of_eq ?_)
      rw [hεdef, ← ENNReal.ofReal_div_of_pos hεpos, ← Real.rpow_sub hNpos]
      congr 1
      ring
    have hset : A1 = ⋃ u : U N, {ω | ε ≤ (P d) (rowSlice d N (k N u) S ω)} := by
      rw [hA1def]; ext ω; simp
    rw [hset]
    have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (M - D₁) := Real.rpow_nonneg hNpos.le _
    calc (P d) (⋃ u : U N, {ω | ε ≤ (P d) (rowSlice d N (k N u) S ω)})
        ≤ ∑ u : U N, (P d) {ω | ε ≤ (P d) (rowSlice d N (k N u) S ω)} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _u : U N, ENNReal.ofReal ((N : ℝ) ^ (M - D₁)) :=
          Finset.sum_le_sum fun u _ => hslice u
      _ = ENNReal.ofReal ((Fintype.card (U N) : ℝ) * (N : ℝ) ^ (M - D₁)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ Ccard * (N : ℝ) ^ (M - D₁)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcardN hpow)
      _ = ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          rw [hD₁def]
          ring
  -- the failure event is contained in the union of the three
  have hsub : badSet (fun N (u : U N) ω => ‖condRow d N (k N u) (X N u) ω‖) χ τ N
      ⊆ A1 ∪ A2 ∪ A3 := by
    rintro ω ⟨u, hu⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    rw [hA1def] at h1
    simp only [Set.mem_ofPred_eq, not_exists, not_le] at h1
    rw [hA2def] at h2
    simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at h2
    rw [hA3def] at h3
    simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at h3
    -- the split
    have hgood : ∀ σ : Ω d, σ ∉ S → ‖X N u σ‖ ≤ (N : ℝ) ^ (τ / 3) * ζ N u σ := by
      intro σ hσ
      rw [hSdef] at hσ
      simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hσ
      exact hσ u
    have hsplit := norm_condRow_le_split (hXmeas N u) (hζ0 N u) (hstab.rowIntegrable N u)
      (henv N u) (Real.rpow_nonneg hNpos.le _) hSmeas hgood ω
    -- the section is small
    have hr1 : (P d).real (rowSlice d N (k N u) S ω) ≤ (N : ℝ) ^ (-M) :=
      ENNReal.toReal_le_of_le_ofReal hεpos.le (h1 u).le
    have hr0 : (0 : ℝ) ≤ (P d).real (rowSlice d N (k N u) S ω) := measureReal_nonneg
    -- the envelope contribution is at most `N^{-B}`
    have hEnvterm : Env N * (P d).real (rowSlice d N (k N u) S ω) ≤ (N : ℝ) ^ (-B) := by
      have hstep : Env N * (P d).real (rowSlice d N (k N u) S ω)
          ≤ (N : ℝ) ^ Kenv * (N : ℝ) ^ (-M) :=
        mul_le_mul hEnvN hr1 hr0 (Real.rpow_nonneg hNpos.le _)
      refine hstep.trans (le_of_eq ?_)
      rw [← Real.rpow_add hNpos, hMdef]
      congr 1
      ring
    -- assemble
    have hχu := hχ0 N u ω
    have hr3 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
    have hmono : (N : ℝ) ^ (τ / 3) ≤ (N : ℝ) ^ (2 * τ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hprod : (N : ℝ) ^ (τ / 3) * (N : ℝ) ^ (τ / 3) = (N : ℝ) ^ (2 * τ / 3) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hfin : (N : ℝ) ^ (τ / 3) * (N : ℝ) ^ (2 * τ / 3) = (N : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hchain : ‖condRow d N (k N u) (X N u) ω‖ ≤ (N : ℝ) ^ τ * χ N u ω := by
      have e1 : (N : ℝ) ^ (τ / 3) * condRowReal d N (k N u) (ζ N u) ω
          ≤ (N : ℝ) ^ (τ / 3) * ((N : ℝ) ^ (τ / 3) * χ N u ω) :=
        mul_le_mul_of_nonneg_left (h2 u) hr3
      have e2 : (N : ℝ) ^ (-B) ≤ (N : ℝ) ^ (τ / 3) * χ N u ω := h3 u
      have e3 : (N : ℝ) ^ (τ / 3) * χ N u ω ≤ (N : ℝ) ^ (2 * τ / 3) * χ N u ω :=
        mul_le_mul_of_nonneg_right hmono hχu
      have e4 : (N : ℝ) ^ (τ / 3) * ((N : ℝ) ^ (τ / 3) * χ N u ω)
          = (N : ℝ) ^ (2 * τ / 3) * χ N u ω := by rw [← mul_assoc, hprod]
      have e5 : (2 : ℝ) * ((N : ℝ) ^ (2 * τ / 3) * χ N u ω) ≤ (N : ℝ) ^ τ * χ N u ω := by
        have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (2 * τ / 3) * χ N u ω :=
          mul_nonneg (Real.rpow_nonneg hNpos.le _) hχu
        calc (2 : ℝ) * ((N : ℝ) ^ (2 * τ / 3) * χ N u ω)
            ≤ (N : ℝ) ^ (τ / 3) * ((N : ℝ) ^ (2 * τ / 3) * χ N u ω) :=
              mul_le_mul_of_nonneg_right h2N hnn
          _ = ((N : ℝ) ^ (τ / 3) * (N : ℝ) ^ (2 * τ / 3)) * χ N u ω :=
              (mul_assoc _ _ _).symm
          _ = (N : ℝ) ^ τ * χ N u ω := by rw [hfin]
      linarith
    exact absurd hchain (not_le.2 hu)
  -- add the three up
  have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
  refine (measure_mono hsub).trans ?_
  calc (P d) (A1 ∪ A2 ∪ A3) ≤ (P d) (A1 ∪ A2) + (P d) A3 := measure_union_le _ _
    _ ≤ ((P d) A1 + (P d) A2) + (P d) A3 := by gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
        + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
          add_le_add (add_le_add hA1small hstabN) hlowN
    _ = ENNReal.ofReal (3 * (N : ℝ) ^ (-(D + 2))) := by
        rw [show (3 : ℝ) * (N : ℝ) ^ (-(D + 2))
            = (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) by ring,
          ENNReal.ofReal_add (by positivity) hnn, ENNReal.ofReal_add hnn hnn]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : 2 * (N : ℝ) ^ (-(D + 1 + 1)) ≤ (N : ℝ) ^ (-(D + 1)) := hdbl1
        have e2 : 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := hdbl2
        have e3 : (N : ℝ) ^ (-(D + 1 + 1)) = (N : ℝ) ^ (-(D + 2)) := by congr 1; ring
        rw [e3] at e1
        linarith

/-- **The shape of the minor replacement (4.9).**  Let `X'` be a *surrogate* for `X` that does
not read row `k` — in the application, the same quantity built from the minor `H^{(k)}`.  Then

  `E_k[X] - X = E_k[X - X'] - (X - X')`

because `E_k[X'] = X'`, and both terms on the right are controlled by `‖X - X'‖ ≺ ζ`: the first
through `RBM.Gauss.stochDom_condRow_of_envelope`, the second directly.  This is how
`E_k(G_{kk} - m) - (G_{kk} - m) ≺ Ψ²` is proved, with `X' = G^{(k)}_{ll} - m`. -/
theorem stochDom_condRow_sub_self [∀ N, Fintype (U N)]
    {X X' : ∀ N, U N → Ω d → ℂ} {ζ χ : ∀ N, U N → Ω d → ℝ} {k : ∀ N, U N → d.Idx N}
    {Env : ℕ → ℝ} {Kenv B Ccard : ℝ} (hCcard : 0 ≤ Ccard)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (hXmeas : ∀ (N : ℕ) (u : U N), Measurable (X N u))
    (hX'meas : ∀ (N : ℕ) (u : U N), Measurable (X' N u))
    (hζmeas : ∀ (N : ℕ) (u : U N), Measurable (ζ N u))
    (hζ0 : ∀ (N : ℕ) (u : U N) (ω : Ω d), 0 ≤ ζ N u ω)
    (hχ0 : ∀ (N : ℕ) (u : U N) (ω : Ω d), 0 ≤ χ N u ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω d), ‖X N u ω - X' N u ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hlow : StochDom (P d) (fun N (_ : U N) (_ : Ω d) => (N : ℝ) ^ (-B)) χ)
    (hstab : CondStable d U k ζ χ) (hζχ : StochDom (P d) ζ χ)
    (hfd : ∀ (N : ℕ) (u : U N), FinDepOffRow d N (k N u) (X' N u))
    (hXint : ∀ (N : ℕ) (u : U N), RowIntegrable d N (k N u) (X N u))
    (hdiff : StochDom (P d) (fun N u ω => ‖X N u ω - X' N u ω‖) ζ) :
    StochDom (P d) (fun N u ω => ‖condRow d N (k N u) (X N u) ω - X N u ω‖) χ := by
  have hX'int : ∀ (N : ℕ) (u : U N), RowIntegrable d N (k N u) (X' N u) := by
    intro N u ω
    have h : (fun ω' => X' N u (rowSplit d N (k N u) ω ω')) = fun _ => X' N u ω := by
      funext ω'; exact (hfd N u).rowSplit_eq ω ω'
    rw [h]; exact integrable_const _
  have hid : ∀ (N : ℕ) (u : U N) (ω : Ω d),
      condRow d N (k N u) (X N u) ω - X N u ω
        = condRow d N (k N u) (fun η => X N u η - X' N u η) ω - (X N u ω - X' N u ω) := by
    intro N u ω
    have e1 := congrFun (condRow_sub (k N u) (hXint N u) (hX'int N u)) ω
    have e2 := congrFun (condRow_of_finDepOffRow (hfd N u)) ω
    rw [e1, e2]
    ring
  have hbound : ∀ (N : ℕ) (u : U N) (ω : Ω d),
      ‖condRow d N (k N u) (X N u) ω - X N u ω‖
        ≤ ‖condRow d N (k N u) (fun η => X N u η - X' N u η) ω‖
          + ‖X N u ω - X' N u ω‖ := by
    intro N u ω
    rw [hid N u ω]
    exact norm_sub_le _ _
  have htwo : StochDom (P d) (fun N (u : U N) ω => χ N u ω + χ N u ω) χ :=
    StochDom.of_le_left (fun N u ω => le_of_eq (by ring))
      (StochDom.const_mul_left (by norm_num : (0 : ℝ) ≤ 2) hχ0 (StochDom.refl hχ0))
  have htool : StochDom (P d)
      (fun N u ω => ‖condRow d N (k N u) (fun η => X N u η - X' N u η) ω‖) χ :=
    stochDom_condRow_of_envelope hCcard hcard
      (fun N u => (hXmeas N u).sub (hX'meas N u)) hζmeas hζ0 hχ0 hKenv hB henv hEnvpoly
      hlow hstab hdiff
  exact StochDom.of_le_left hbound ((htool.add (hdiff.trans hζχ)).trans htwo)

end Tool

/-! ### The paper's control `L_max`

Two facts about `RBM.Lmax` are needed to feed it into the tool: it is a measurable function of
`ω`, and it is not super-polynomially small.  The second holds on the event `Ω(t,c)` of (4.1),
where `W⁻¹ ≤ 4 L_max` (`RBM.inv_W_le_Lmax`); since `W ≤ N` this gives `N^{-1} ≺ L_max`. -/

section LmaxControl

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- `ω ↦ L_max(H_t(ω), z)` is measurable: `RBM.Lre_eq` writes each `(+,-)` `2`-loop as a finite
sum of squared Green function entries, and a finite `sup'` of measurable functions is
measurable. -/
theorem measurable_Lmax (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) :
    Measurable fun ω : Ω d => Lmax (Hflow d N u ω) z := by
  have hLre : ∀ a b : ZMod (d.L N), Measurable fun ω : Ω d => Lre (Hflow d N u ω) z a b := by
    intro a b
    have h : (fun ω : Ω d => Lre (Hflow d N u ω) z a b)
        = fun ω : Ω d => ((d.W N : ℝ)⁻¹) ^ 2
            * ∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
                ‖green (Hflow d N u ω) z (b, β) (a, α)‖ ^ 2 := by
      funext ω; exact Lre_eq (Hflow_isHermitian d N u ω) a b
    rw [h]
    exact measurable_const.mul (Finset.measurable_sum _ fun β _ =>
      Finset.measurable_sum _ fun α _ =>
        ((measurable_green_apply d N u z (b, β) (a, α)).norm).pow_const 2)
  have hfun : (fun ω : Ω d => Lmax (Hflow d N u ω) z)
      = (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N))).sup' Finset.univ_nonempty
          fun p => fun ω : Ω d => Lre (Hflow d N u ω) z p.1 p.2 := by
    funext ω
    rw [Finset.sup'_apply]
    rfl
  rw [hfun]
  exact Finset.measurable_sup' _ fun p _ => hLre p.1 p.2

/-- **`L_max` is not super-polynomially small**: `N^{-1} ≺ L_max`.

On the event `Ω(t,c)` of (4.1) the diagonal of `G` has modulus at least `1/2`, hence
`W⁻¹ ≤ 4 L_max` (`RBM.inv_W_le_Lmax`); and `W ≤ WL ≤ N`.  This is the input `N^{-B} ≺ χ` of
`RBM.Gauss.stochDom_condRow_of_envelope`, with `B = 1`. -/
theorem stochDom_rpow_neg_one_Lmax (d : Dims) (U : ℕ → Type*) (hE : |E| ≤ 2)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ)) :
    StochDom (P d) (fun N (_ : U N) (_ : Ω d) => (N : ℝ) ^ (-(1 : ℝ)))
      (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) := by
  intro τ hτ D hD
  filter_upwards [hΩ D hD, hδ, d.dim, eventually_le_rpow 4 hτ, eventually_ge_atTop 1]
    with N hΩN hδN hdimN h4N hN1
  refine (measure_mono ?_).trans hΩN
  rintro ω ⟨u, hu⟩
  simp only at hu
  refine Set.mem_compl fun hω => ?_
  have hGE : GoodEvent (green (Hflow d N t ω) (zt E t)) (mE E) (δ N) := hω
  have h1 := inv_W_le_Lmax (Hflow_isHermitian d N t ω) (norm_mE hE) hGE hδN
  have hWpos : (0 : ℝ) < (d.W N : ℕ) := by exact_mod_cast d.W_pos N
  have hWN : ((d.W N : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hL : 0 < d.L N := by have := d.three_le_L N; omega
    have h2 : d.W N ≤ d.W N * d.L N := Nat.le_mul_of_pos_right _ hL
    exact_mod_cast h2.trans hdimN.1
  have h2 : (N : ℝ)⁻¹ ≤ ((d.W N : ℕ) : ℝ)⁻¹ := inv_anti₀ hWpos hWN
  have hL0 := Lmax_nonneg (z := zt E t) (Hflow_isHermitian d N t ω)
  have h3 : 4 * Lmax (Hflow d N t ω) (zt E t)
      ≤ (N : ℝ) ^ τ * Lmax (Hflow d N t ω) (zt E t) :=
    mul_le_mul_of_nonneg_right h4N hL0
  rw [Real.rpow_neg_one] at hu
  linarith

end LmaxControl

/-! ### The two inputs of `hIBP` -/

section Pieces

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- `#(Idx × Idx) ≤ N²` eventually — the Definition 2.1 (i) cardinality bound for a pair of
indices. -/
theorem card_Idx_prod_le (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (d.Idx N × d.Idx N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  filter_upwards [card_Idx_le d, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [Real.rpow_one] at hN
  have h0 : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
  have hsq : (N : ℝ) * (N : ℝ) = (N : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [Fintype.card_prod]
  push_cast
  calc (Fintype.card (d.Idx N) : ℝ) * (Fintype.card (d.Idx N) : ℝ)
      ≤ (N : ℝ) * (N : ℝ) := mul_le_mul hN hN h0 hN0
    _ = (N : ℝ) ^ (2 : ℝ) := hsq

/-- `|G_{ii} - m| ≤ η_t⁻¹ + 1` on the whole space. -/
theorem norm_green_diag_sub_mE_le (hE : |E| < 2) (ht : t < 1) (u : ℝ) (i : d.Idx N) (ω : Ω d) :
    ‖green (Hflow d N u ω) (zt E t) i i - mE E‖ ≤ (etaT E t)⁻¹ + 1 :=
  norm_greenDiagCentered_le_env hE ht u i ω

/-- **`hprod`**, the first input of `RBM.Gauss.condExpDiag_stochDom_of_pieces`, at its frozen
signature:

  `E_i[(G_{ii} - m)(G_{kk} - m)] ≺ L_max`.

Each factor is `≺ Ψ` by the local law `hloc` (`RBM.Gauss.diag_bound_gauss` without its
indicator), so the product is `≺ Ψ² = L_max` by `ab ≤ (a² + b²)/2`; the passage through `E_i`
is `RBM.Gauss.stochDom_condRow_of_envelope`, with the deterministic envelope
`|G_{ii} - m| ≤ η_t⁻¹ + 1`. -/
theorem hprod_of_localLaw (d : Dims) (hE : |E| < 2) (ht : t < 1)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (hstab : CondStable d (fun N => d.Idx N × d.Idx N) (fun _ q => q.1)
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)))
    (hloc : StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖green (Hflow d N t ω) (zt E t) i i - mE E‖ ^ 2)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (q : d.Idx N × d.Idx N) ω =>
        ‖condRow d N q.1 (fun η => (green (Hflow d N t η) (zt E t) q.1 q.1 - mE E)
          * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have hL0 : ∀ (N : ℕ) (q : d.Idx N × d.Idx N) (ω : Ω d),
      0 ≤ Lmax (Hflow d N t ω) (zt E t) := fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)
  have htwo : StochDom (P d)
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)
        + Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)) :=
    StochDom.of_le_left (fun N q ω => le_of_eq (by ring))
      (StochDom.const_mul_left (by norm_num : (0 : ℝ) ≤ 2) hL0 (StochDom.refl hL0))
  have hdom : StochDom (P d)
      (fun N (q : d.Idx N × d.Idx N) ω =>
        ‖(green (Hflow d N t ω) (zt E t) q.1 q.1 - mE E)
          * (green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
    have h1 := hloc.precomp_param fun N (q : d.Idx N × d.Idx N) => q.1
    have h2 := hloc.precomp_param fun N (q : d.Idx N × d.Idx N) => q.2
    refine StochDom.of_le_left (fun N q ω => ?_)
      (StochDom.const_mul_left (by norm_num : (0 : ℝ) ≤ 1 / 2) hL0 ((h1.add h2).trans htwo))
    simp only [Pi.add_apply]
    rw [norm_mul]
    linarith [sq_nonneg (‖green (Hflow d N t ω) (zt E t) q.1 q.1 - mE E‖
      - ‖green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E‖)]
  refine stochDom_condRow_of_envelope (Ccard := 2) (by norm_num) (card_Idx_prod_le d)
    (fun N q => ((measurable_green_apply d N t (zt E t) q.1 q.1).sub measurable_const).mul
      ((measurable_green_apply d N t (zt E t) q.2 q.2).sub measurable_const))
    (fun N _ => measurable_Lmax d N t (zt E t)) hL0 hL0
    (Kenv := 1) (by norm_num) (B := 1) (by norm_num)
    (Env := fun _ => ((etaT E t)⁻¹ + 1) ^ 2) ?_ ?_
    (stochDom_rpow_neg_one_Lmax d _ hE.le hδ hΩ) hstab hdom
  · intro N q ω
    rw [norm_mul, sq]
    exact mul_le_mul (norm_green_diag_sub_mE_le hE ht t q.1 ω)
      (norm_green_diag_sub_mE_le hE ht t q.2 ω) (norm_nonneg _) (by positivity)
  · exact eventually_le_rpow (((etaT E t)⁻¹ + 1) ^ 2) one_pos

/-- **`hminor`, off the diagonal.**

  `E_i(G_{kk} - m) - (G_{kk} - m) ≺ L_max`  for `k ≠ i`.

`G^{(i)}_{kk}` does not read row `i` (`RBM.Gauss.finDepOffRow_greenMinorMat_apply`), so it is its
own `E_i`, and the whole quantity is `E_i[D] - D` with `D = (G_{kk}-m) - (G^{(i)}_{kk}-m)` the
replacement error (4.9) of T85 — the hypothesis `hrepl`.  `E_i[D] ≺ L_max` is
`RBM.Gauss.stochDom_condRow_of_envelope`, with the deterministic envelope `|D| ≤ 2 η_t⁻¹`.

The restriction `k ≠ i` is not an artefact: for `k = i` the quantity is `-(1 - E_i)(G_{ii} - m)`,
which is of size `Ψ`, not `Ψ²`, and no minor surrogate exists. -/
theorem hminor_offdiag_of_repl (d : Dims) (hE : |E| < 2) (ht : t < 1)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (hstab : CondStable d (fun N => OffPair d.L d.W N) (fun _ v => v.1.1)
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t)))
    (hrepl : StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        ‖greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω
          - greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        ‖condRow d N v.1.1 (greenDiagCentered d N t (zt E t) (mE E) v.1.2) ω
          - greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have hL0 : ∀ (N : ℕ) (v : OffPair d.L d.W N) (ω : Ω d),
      0 ≤ Lmax (Hflow d N t ω) (zt E t) := fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)
  have hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (OffPair d.L d.W N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [card_Idx_prod_le d] with N hN
    refine le_trans ?_ hN
    exact_mod_cast Fintype.card_subtype_le (fun p : d.Idx N × d.Idx N => p.1 ≠ p.2)
  refine stochDom_condRow_sub_self (Ccard := 2) (by norm_num) hcard
    (fun N v => measurable_greenDiagCentered d N t (zt E t) (mE E) v.1.2)
    (fun N v => measurable_greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 _)
    (fun N _ => measurable_Lmax d N t (zt E t)) hL0 hL0
    (Kenv := 1) (by norm_num) (B := 1) (by norm_num)
    (Env := fun _ => 2 * (etaT E t)⁻¹) ?_ ?_
    (stochDom_rpow_neg_one_Lmax d _ hE.le hδ hΩ) hstab (StochDom.refl hL0)
    (fun N v => (finDepOffRow_greenMinorMat_apply d N t (zt E t) v.1.1
      ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩).comp fun z => z - mE E)
    (fun N v => rowIntegrable_of_measurable_of_bound
      (measurable_greenDiagCentered d N t (zt E t) (mE E) v.1.2)
      (norm_greenDiagCentered_le_env hE ht t v.1.2))
    hrepl
  · intro N v ω
    have he : greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω
        - greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω
        = green (Hflow d N t ω) (zt E t) v.1.2 v.1.2
          - greenMinorMat d N t (zt E t) v.1.1 ω ⟨v.1.2, Ne.symm v.2⟩
            ⟨v.1.2, Ne.symm v.2⟩ := by
      simp only [greenDiagCentered, greenMinorDiagCentered]
      ring
    rw [he]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := norm_green_apply_le_etaT hE ht t v.1.2 v.1.2 ω
    have h2 := norm_greenMinorMat_apply_le_etaT (d := d) (N := N) hE ht t
      (κ := v.1.1) ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩ ω
    linarith
  · exact eventually_le_rpow (2 * (etaT E t)⁻¹) one_pos

/-! ### From the two inputs to `hIBP`

`RBM.Gauss.condExpDiag_stochDom_of_pieces` asks for `hminor` at **every** pair `(i, k)`,
including `k = i`; but at `k = i` the quantity `E_i(G_{ii} - m) - (G_{ii} - m)` is the
fluctuation `-(1 - E_i)(G_{ii} - m)`, of size `Ψ`, not `Ψ²`.  See the module note in
`docs/paper-deltas.md`.

The diagonal term does not have to be small, because it enters the sum
`∑_k S_{ik} · ibpRem(i,k)` with the coefficient `S_{ii} ≍ W⁻¹`, and on the event `Ω(t,c)` of
(4.1) one has `S_{ii} ≤ 2 L_max` (`RBM.Sblk_le_Lmax`).  Since `ibpRem` has a *deterministic*
envelope, the single diagonal term contributes `O(L_max)` by itself.  So the reduction below
replaces the uniform bound of `RBM.Gauss.norm_condExpDiag_sub_le` by a weighted one, and needs
`ibpRem ≺ L_max` **only off the diagonal**. -/

section Assembly

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- `‖E_k[X]‖ ≤ C` from a pointwise bound `‖X‖ ≤ C`: `P d` is a probability measure. -/
theorem norm_condRow_le_const {k : d.Idx N} {X : Ω d → ℂ} {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) (ω : Ω d) :
    ‖condRow d N k X ω‖ ≤ C := by
  have huniv : (P d).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have h := norm_integral_le_of_norm_le_const (μ := P d)
    (f := fun ω' => X (rowSplit d N k ω ω')) (C := C)
    (Filter.Eventually.of_forall fun ω' => hC _)
  rw [huniv, mul_one] at h
  exact h

/-- **The deterministic envelope of `RBM.Gauss.ibpRem`**: `|ibpRem| ≤ (η_t⁻¹ + 1)²` for every
`ω`, from `‖G_t‖ ≤ η_t⁻¹` and `‖m^{(E)}‖ = 1`. -/
theorem norm_ibpRem_le_env (hE : |E| < 2) (ht : t < 1) (q : d.Idx N × d.Idx N) (ω : Ω d) :
    ‖ibpRem d N E t q ω‖ ≤ ((etaT E t)⁻¹ + 1) * ((etaT E t)⁻¹ + 1) := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have h1 : ‖condRow d N q.1 (fun η => green (Hflow d N t η) (zt E t) q.1 q.1
      * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω‖
      ≤ (etaT E t)⁻¹ * ((etaT E t)⁻¹ + 1) := by
    refine norm_condRow_le_const (fun η => ?_) ω
    rw [norm_mul]
    exact mul_le_mul (norm_green_apply_le_etaT hE ht t q.1 q.1 η)
      (norm_green_diag_sub_mE_le hE ht t q.2 η) (norm_nonneg _) (by positivity)
  have h2 : ‖mE E * (green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E)‖ ≤ (etaT E t)⁻¹ + 1 := by
    rw [norm_mul, norm_mE hE.le, one_mul]
    exact norm_green_diag_sub_mE_le hE ht t q.2 ω
  simp only [ibpRem]
  calc ‖condRow d N q.1 (fun η => green (Hflow d N t η) (zt E t) q.1 q.1
          * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω
        - mE E * (green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E)‖
      ≤ ‖condRow d N q.1 (fun η => green (Hflow d N t η) (zt E t) q.1 q.1
          * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω‖
        + ‖mE E * (green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E)‖ := norm_sub_le _ _
    _ ≤ (etaT E t)⁻¹ * ((etaT E t)⁻¹ + 1) + ((etaT E t)⁻¹ + 1) := add_le_add h1 h2
    _ = ((etaT E t)⁻¹ + 1) * ((etaT E t)⁻¹ + 1) := by ring

/-- **The weighted reduction.**  `RBM.Gauss.norm_condExpDiag_sub_le` bounds the p. 50 remainder
by a *uniform* bound on `ibpRem d N E t (i, ·)`.  Here the diagonal term is kept separate, with
its own bound and its own coefficient `S_{ii}`: the row sums of `S` are one, so

  `‖p.50 remainder‖ ≤ A + S_{ii} · A_diag`

as soon as `‖ibpRem(i,k)‖ ≤ A` for `k ≠ i` and `‖ibpRem(i,i)‖ ≤ A_diag`. -/
theorem norm_condExpDiag_sub_le_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (i : d.Idx N) (ω : Ω d) {A Adiag : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ k : d.Idx N, k ≠ i → ‖ibpRem d N E t (i, k) ω‖ ≤ A)
    (hAd : ‖ibpRem d N E t (i, i) ω‖ ≤ Adiag) :
    ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖
      ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := by
  classical
  have hterm : ∀ k : d.Idx N, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω
      = (Sblk (d.L N) (d.W N) i k : ℂ) * condRow d N i
          (fun η => green (Hflow d N t η) (zt E t) i i
            * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
        - mE E * ((Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)) := by
    intro k
    simp only [ibpRem]
    ring
  have hkey : condExpDiag d N t (zt E t) (mE E) i ω
      - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
        * (green (Hflow d N t ω) (zt E t) k k - mE E)
      = (t : ℂ) * mE E * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω := by
    rw [condExpDiag_eq_sum_Sblk hG hE hE.le ht0 ht i ω,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hSrow := sum_Sblk_row (L := d.L N) (W := d.W N) (d.three_le_L N) i
  have hsum : ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
      ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := by
    have hstep : ∑ k, Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖
        ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun k => Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖) (Finset.mem_univ i)]
      have hdiagle : Sblk (d.L N) (d.W N) i i * ‖ibpRem d N E t (i, i) ω‖
          ≤ Sblk (d.L N) (d.W N) i i * Adiag :=
        mul_le_mul_of_nonneg_left hAd (Sblk_nonneg _ _)
      have hoffle : ∑ k ∈ Finset.univ.erase i,
            Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖ ≤ A := by
        calc ∑ k ∈ Finset.univ.erase i,
              Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖
            ≤ ∑ k ∈ Finset.univ.erase i, Sblk (d.L N) (d.W N) i k * A := by
              refine Finset.sum_le_sum fun k hk => ?_
              exact mul_le_mul_of_nonneg_left (hA k (Finset.ne_of_mem_erase hk))
                (Sblk_nonneg _ _)
          _ = (∑ k ∈ Finset.univ.erase i, Sblk (d.L N) (d.W N) i k) * A := by
              rw [Finset.sum_mul]
          _ ≤ (∑ k, Sblk (d.L N) (d.W N) i k) * A := by
              refine mul_le_mul_of_nonneg_right ?_ hA0
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                fun k _ _ => Sblk_nonneg _ _
          _ = A := by rw [hSrow, one_mul]
      linarith
    calc ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
        ≤ ∑ k, ‖(Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ := norm_sum_le _ _
      _ = ∑ k, Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Sblk_nonneg _ _)]
      _ ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := hstep
  rw [hkey, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mE hE.le, mul_one]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.le
  calc |t| * ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
      ≤ 1 * ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ := one_mul _
    _ ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := hsum

/-- **`hIBP` from the off-diagonal remainder only.**  With the weighted reduction above, the
hypothesis `hIBP` of `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom` follows — at its exact frozen
signature — from `‖ibpRem(i,k)‖ ≺ L_max` for `k ≠ i` together with (4.4).  The diagonal is
absorbed by `S_{ii} ≤ 2 L_max` and the deterministic envelope of `RBM.Gauss.ibpRem`. -/
theorem condExpDiag_stochDom_of_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (hoff : StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω => ‖ibpRem d N E t (v.1.1, v.1.2) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  set C : ℝ := ((etaT E t)⁻¹ + 1) * ((etaT E t)⁻¹ + 1) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine StochDom.of_indicator hΩ ?_
  refine StochDom.of_det hoff (fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)) hδ0 hc₀ hδc
    (ε₀ := 1 / 2) (by norm_num) (1 + 2 * C) 1 ?_
  intro N ω Φ hΦ1 _ hδε hAB i
  have hL0 := Lmax_nonneg (z := zt E t) (Hflow_isHermitian d N t ω)
  by_cases hω : ω ∈ goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ N
  · rw [Set.indicator_of_mem hω]
    have hGE : GoodEvent (green (Hflow d N t ω) (zt E t)) (mE E) (δ N) := hω
    have hS := Sblk_le_Lmax (Hflow_isHermitian d N t ω) (norm_mE hE.le) hGE hδε i i
    have hS0 := Sblk_nonneg (L := d.L N) (W := d.W N) i i
    have hA : ∀ k : d.Idx N, k ≠ i →
        ‖ibpRem d N E t (i, k) ω‖ ≤ Φ * Lmax (Hflow d N t ω) (zt E t) :=
      fun k hk => hAB ⟨(i, k), Ne.symm hk⟩
    have hbound := norm_condExpDiag_sub_le_offdiag hG hE ht0 ht i ω
      (mul_nonneg (by linarith) hL0) hA (norm_ibpRem_le_env hE ht (i, i) ω)
    refine hbound.trans ?_
    have h1 : Sblk (d.L N) (d.W N) i i * C ≤ 2 * Lmax (Hflow d N t ω) (zt E t) * C :=
      mul_le_mul_of_nonneg_right hS hC0
    have h2 : 2 * Lmax (Hflow d N t ω) (zt E t) * C
        ≤ Φ * (2 * C * Lmax (Hflow d N t ω) (zt E t)) := by
      have hkey : (0 : ℝ) ≤ (Φ - 1) * (2 * C * Lmax (Hflow d N t ω) (zt E t)) :=
        mul_nonneg (by linarith)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0) hL0)
      linarith [hkey]
    have h3 : (1 + 2 * C) * Φ ^ 1 * Lmax (Hflow d N t ω) (zt E t)
        = Φ * Lmax (Hflow d N t ω) (zt E t) + Φ * (2 * C * Lmax (Hflow d N t ω) (zt E t)) := by
      rw [pow_one]; ring
    rw [h3]
    linarith
  · rw [Set.indicator_of_notMem hω]
    have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
    positivity

/-- **The off-diagonal remainder, from the paper's two inputs.**  `RBM.Gauss.ibpRem_eq_add`
splits `ibpRem(i,k)` into `E_i[(G_{ii}-m)(G_{kk}-m)]` and `m(E_i(G_{kk}-m) - (G_{kk}-m))`; for
`k ≠ i` both are `≺ L_max`, by `RBM.Gauss.hprod_of_localLaw` and
`RBM.Gauss.hminor_offdiag_of_repl`. -/
theorem stochDom_ibpRem_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    (hprod : StochDom (P d)
      (fun N (q : d.Idx N × d.Idx N) ω =>
        ‖condRow d N q.1 (fun η => (green (Hflow d N t η) (zt E t) q.1 q.1 - mE E)
          * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hminor : StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        ‖condRow d N v.1.1 (greenDiagCentered d N t (zt E t) (mE E) v.1.2) ω
          - greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω => ‖ibpRem d N E t (v.1.1, v.1.2) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hL0 : ∀ (N : ℕ) (v : OffPair d.L d.W N) (ω : Ω d),
      0 ≤ Lmax (Hflow d N t ω) (zt E t) := fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)
  have htwo : StochDom (P d)
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t)
        + Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t)) :=
    StochDom.of_le_left (fun N v ω => le_of_eq (by ring))
      (StochDom.const_mul_left (by norm_num : (0 : ℝ) ≤ 2) hL0 (StochDom.refl hL0))
  have hp := hprod.precomp_param fun N (v : OffPair d.L d.W N) => (v.1.1, v.1.2)
  refine StochDom.of_le_left (fun N v ω => ?_) ((hp.add hminor).trans htwo)
  rw [ibpRem_eq_add hG hE ht v.1.1 v.1.2 ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE hE.le, one_mul]
  simp only [Pi.add_apply]
  exact le_rfl

/-- **`hIBP`, assembled**, at the exact frozen signature of the hypothesis `hIBP` of
`RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`.

The inputs are, in order:

* (4.4), the event `Ω(t,c)` of (4.1) with high probability (`hΩ`);
* `hstabP`, `hstabM`: the control `L_max` passes through `E_i` (`RBM.Gauss.CondStable`) — the
  one genuinely new probabilistic input this route exposes;
* `hloc`: the local law `|G_{ii} - m|² ≺ L_max`, i.e. (4.3) without its indicator
  (`RBM.Gauss.diag_bound_gauss` plus `RBM.StochDom.of_indicator`);
* `hrepl`: the minor replacement (4.9) of T85, `|G_{kk} - G^{(i)}_{kk}| ≺ L_max` for `k ≠ i`.

Everything else — the Gaussian integration by parts, the passage of `≺` through `E_i`, and the
weighted reduction that absorbs the diagonal — is proved. -/
theorem condExpDiag_stochDom_of_localLaw (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (hstabP : CondStable d (fun N => d.Idx N × d.Idx N) (fun _ q => q.1)
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)))
    (hstabM : CondStable d (fun N => OffPair d.L d.W N) (fun _ v => v.1.1)
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t)))
    (hloc : StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖green (Hflow d N t ω) (zt E t) i i - mE E‖ ^ 2)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hrepl : StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        ‖greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω
          - greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hδhalf : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2 := by
    filter_upwards [hδc, eventually_le_rpow 2 hc₀, eventually_ge_atTop 1] with N hN h2N hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h1 : (N : ℝ) ^ (-c₀) ≤ 1 / 2 := by
      rw [Real.rpow_neg hNpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hNpos _) (by norm_num)]
      simpa using h2N
    linarith
  exact condExpDiag_stochDom_of_offdiag hG hE ht0 ht hδ0 hc₀ hδc hΩ
    (stochDom_ibpRem_offdiag hG hE ht
      (hprod_of_localLaw d hE ht hδhalf hΩ hstabP hloc)
      (hminor_offdiag_of_repl d hE ht hδhalf hΩ hstabM hrepl))

/-- **(4.5) with `hIBP` discharged.**  This is `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom` with
its hypothesis `hIBP` replaced by `RBM.Gauss.condExpDiag_stochDom_of_localLaw`.  Its *only* role
is to check, at compile time, that what is proved above really does fit the frozen slot: no
signature in `RBM1D/Gauss/FlucAvg.lean`, `RBM1D/Gauss/IBP.lean` or
`RBM1D/Green/EntryBound.lean` is touched. -/
theorem trace_green_sub_mul_Eblk_stochDom_of_localLaw (d : Dims) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hG : GaussIBP d) (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (hstabP : CondStable d (fun N => d.Idx N × d.Idx N) (fun _ q => q.1)
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)))
    (hstabM : CondStable d (fun N => OffPair d.L d.W N) (fun _ v => v.1.1)
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : OffPair d.L d.W N) ω => Lmax (Hflow d N t ω) (zt E t)))
    (hloc : StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖green (Hflow d N t ω) (zt E t) i i - mE E‖ ^ 2)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hrepl : StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        ‖greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω
          - greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hFArow : StochDom (P d)
      (fun N (i : d.Idx N) ω =>
        ‖flucAvg d N t (zt E t) (mE E) (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hFAblk : StochDom (P d)
      (fun N (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N t (zt E t) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (a : ZMod (d.L N)) ω => ‖Matrix.trace ((green (Hflow d N t ω) (zt E t)
        - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) a)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) :=
  trace_green_sub_mul_Eblk_stochDom d hκ0 hκ1 hEκ ht0 ht1
    (condExpDiag_stochDom_of_localLaw hG (lt_of_le_of_lt hEκ (by linarith)) ht0 ht1 hδ0 hc₀ hδc
      hΩ hstabP hstabM hloc hrepl)
    hFArow hFAblk

end Assembly

end Pieces

end RBM.Gauss



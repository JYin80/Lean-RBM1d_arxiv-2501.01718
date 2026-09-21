/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelGauss

/-!
# A producer for `RBM.MomentDuhamel.Hyp` (T180)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  `RBM1D/Gauss/MomentDuhamel.lean` states the primed interface
`RBM.MomentDuhamel.Hyp` and `RBM.MomentDuhamel.stochDom_of_momentDuhamel` consumes it; T176
found that **nothing produced it**.  This file produces everything about it that is provable
today and names, as two `Prop`s, exactly what is not.

## What is produced

* `RBM.MomentDuhamel.drift_driftF` — **the field `drift`**, i.e. the pointwise identity
  (5.15), with `F := RBM.DriftDef.driftF`.  This is T58's `RBM.DriftDef.drift_split_gen` with
  its two side conditions (`Im z_u ≠ 0` and `‖u m(σ)m(σ')‖ < 1`) read off a window contained
  in `[0, 1)`.  **There is no `0 < u` seam here**: the derivative is of `v ↦ gloop(M, z_v)`
  and `v ↦ K_v` at a *frozen* matrix `M`, so the `√u` of the flow — the reason T152's
  closed-interval drift identity was unsatisfiable at `s = 0` — never enters.  The
  `example` after `momentIneqQ_body_self` checks the identity at `u = 0`.
* `RBM.MomentDuhamel.integrable_gauss` — **the field `integrable`** on the Gaussian model,
  from T132b's `RBM.Gauss.integrable_lkT_pow`.
* `RBM.MomentDuhamel.hypOfMoments`, `gaussHypOfMoments` — **the instance**, with `F` pinned to
  `RBM.DriftDef.driftF` and `cMD` the one acknowledged (and `N`-independent) degree of freedom.
* `RBM.MomentDuhamel.hypOfMoments_F`, `F_eq_driftF_of_window` — **the fiat audit**: the
  produced instance's drift is `driftF` by `rfl`, and in fact *every* `Hyp` over a window in
  `[0, 1)` has `F = driftF` (T58's `RBM.DriftDef.F_eq_driftF`), so `F` is not a degree of
  freedom of the interface at all.

## What is not produced, and exactly what is short

`RBM.MomentDuhamel.MomentIneq` and `MomentIneqQ` — the fields `momentDuhamel`,
`momentDuhamelQ`, **with `F` already substituted by `driftF`**, so that they are statements
about definitions and not about anything an instance may choose.  For these the file supplies
the *closing* half of T132b's chain and stops at the *generator* half:

* `RBM.MomentDuhamel.momNorm_le_of_integral_le` — T132a's
  `RBM.sqrt_le_of_integral_le` with `ψ = (E|Y|^{2p})^{1/p}` substituted, so that both sides are
  `RBM.MomentDuhamel.momNorm`s (`sqrt_momPow_eq_momNorm` is the substitution).
* `RBM.MomentDuhamel.momentDuhamel_body_of_integral_le`,
  `momentDuhamelQ_body_of_integral_le` — the bodies of the two fields at one
  `(p, N, σ, v, a)`, reduced to the **integrated differential inequality** `hdu` for
  `ψ_u = (E |(U_{u,v} ∘ (L-K)_u)_a|^{2p})^{1/p}`, plus integrability and a supremum
  (`exists_isLUB_Icc`).  `RBM.Uker_self` supplies `U_{v,v} = 1`, which is what makes the
  left-hand side of (5.20) the endpoint of that path.
* `RBM.MomentDuhamel.momentIneq_of_diffIneq` — the previous item **under the quantifiers of
  the field**, i.e. `MomentIneq` itself from a per-`(p, N, σ, v, a)` supply of that
  differential inequality.  So the whole gap is one statement about `ψ'`.
* What is left is `hdu` itself: Itô/Gaussian generator identity, then Hölder.  The identity
  with explicit time dependence is T132b's `RBM.Gauss.hasDerivAt_integral_Psi_pairs`, but it
  is stated for `RBM.Gauss.TestFunT`, and `Ψ(u, M) = |(U_{u,v} ∘ (L-K)(u, M))_a|^{2p}` is
  **not** in that class:

  - `bdd₀`, `bdd₁`, `bdd₂` quantify over *all* matrices `M`, and `(M - z_u)⁻¹` is unbounded
    off the Hermitian set;
  - `TestFunT.slice` feeds `RBM.Gauss.TestFun.contDiff`, a *global* `ContDiff ℝ 2`, and `Ψ`
    is not even continuous at a singular non-Hermitian `M` (Lean's `Ring.inverse` is `0`
    there).  The proof of `hasDerivAt_integral_Psi` uses that slice, through
    `continuous_coordD1` / `continuous_coordD2`, at every matrix.

  On the Hermitian set both would hold, with the same constants that give `integrable`
  (`‖G_u‖ ≤ |Im z_u|⁻¹`), and the whole argument stays there — the flow is Hermitian and so is
  every segment between flow values.  So there are two ways forward, and choosing between them
  is a design decision, not something to work around here:
  **(i)** relax `TestFun` / `TestFunT` from `∀ M` to `∀ M, M.IsHermitian →` — the same repair
  T145 made to `Hyp.drift` — which means reproving `hasDerivAt_integral_Psi` with the
  domination restricted to the flow; or **(ii)** cut `Ψ` off, i.e. the smooth-cutoff scheme of
  `RBM1D/Gauss/CutoffBounds.lean` (T158) with the three gaps recorded in `docs/STATUS.md`
  under "T132c 第 0 步 / 光滑截断方案：三个真实缺口".  Note that `Hyp.momentDuhamel` is a
  *structural* inequality — `F` and `E ⊗ E` appear on its right — so it does not by itself
  need the cutoff's size estimates; only the generator identity and Hölder.

  Two further seams on that route, recorded so they are not rediscovered:
  `hasDerivAt_integral_Psi` carries `0 < u` (the `√u` of the flow), so `hdu` can only be
  obtained from a derivative on the **open** interval plus continuity, exactly as in T161 and
  T173's `Uker_duhamel_Ioo`; and T72's `RBM.Gauss.genMomentPt_le`, the pointwise
  `|Φ|^{2p}` bound, likewise asks for a global `ContDiff ℝ 2`.

The derivation also fixes the constant: the generator gives
`ψ' ≤ 2 √ψ · ‖U ∘ F‖_{2p} + (2p-1) ‖(U ⊗ U) ∘ (E ⊗ E)‖_p`, so `cMD p = 2p - 1`.

## Satisfiability

* `drift` — satisfied on every window `[s_N, t_N] ⊆ [0, 1)`, including at `u = 0`
  (the `example` in the `Degenerate` section).  It is *not* satisfiable at `u = 1`, where
  `z_u` is real; that is the standing `t_N < 1` of the paper.
* `integrable` — satisfied on the Gaussian model on the same window, and for the same reason.
* `MomentIneq`, `MomentIneqQ` — `momentIneq_body_self`, `momentIneqQ_body_self` check the
  degenerate point `v = s_N`, where both time integrals vanish and `U_{s,s} = 1`: the
  inequality holds, with equality.  So neither field is vacuously false where the window
  collapses (the failure mode T164/T172 found elsewhere).
* `cMD` — free, but `ℕ → ℝ`, hence `N`-independent; see the fiat audit in
  `RBM1D/Gauss/MomentDuhamel.lean`.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM
namespace MomentDuhamel

open MeasureTheory Filter Real

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `√((∫|Y|^{2p})^{1/p}) = ‖Y‖_{2p}`. -/
theorem sqrt_momPow_eq_momNorm (P : Measure Ω) (p : ℕ) (Y : Ω → ℝ) :
    √((∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / p)) = momNorm P (2 * p) Y := by
  have h0 : (0 : ℝ) ≤ ∫ ω, |Y ω| ^ (2 * p) ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h0, momNorm]
  congr 1
  push_cast
  ring

/-- **The closing step in the interface's own vocabulary.**

`RBM.sqrt_le_of_integral_le` reads `ψ = (∫|Y|^{2p})^{1/p}`; this is that lemma with the
substitution performed, so that both sides are `RBM.MomentDuhamel.momNorm`s and the
conclusion is literally the shape of `RBM.MomentDuhamel.Hyp.momentDuhamel`. -/
theorem momNorm_le_of_integral_le {P : Measure Ω} {p : ℕ}
    {s v : ℝ} (hsv : s ≤ v) {Y : ℝ → Ω → ℝ} {ψ f g : ℝ → ℝ} {c M : ℝ}
    (hψ : ∀ u, ψ u = (∫ ω, |Y u ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / p))
    (hf0 : ∀ r ∈ Set.Icc s v, 0 ≤ f r) (hg0 : ∀ r ∈ Set.Icc s v, 0 ≤ g r) (hc0 : 0 ≤ c)
    (hM : IsLUB (ψ '' Set.Icc s v) M)
    (hintψf : ∀ u ∈ Set.Icc s v,
      IntervalIntegrable (fun r => momNorm P (2 * p) (Y r) * f r) volume s u)
    (hintf : IntervalIntegrable f volume s v)
    (hintg : IntervalIntegrable g volume s v)
    (hdu : ∀ u ∈ Set.Icc s v,
      ψ u ≤ ψ s + 2 * (∫ r in s..u, momNorm P (2 * p) (Y r) * f r) + c * ∫ r in s..u, g r) :
    momNorm P (2 * p) (Y v)
      ≤ momNorm P (2 * p) (Y s) + 2 * (∫ r in s..v, f r)
        + (c * ∫ r in s..v, g r) ^ ((1 : ℝ) / 2) := by
  have hsq : ∀ u, √(ψ u) = momNorm P (2 * p) (Y u) := by
    intro u; rw [hψ u]; exact sqrt_momPow_eq_momNorm P p (Y u)
  have hψ0 : ∀ u ∈ Set.Icc s v, 0 ≤ ψ u := by
    intro u _
    rw [hψ u]
    exact Real.rpow_nonneg (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) _
  have key := sqrt_le_of_integral_le hsv hψ0 hf0 hg0 hc0 hM
    (fun u hu => by simpa only [hsq] using hintψf u hu) hintf hintg
    (fun u hu => by simpa only [hsq] using hdu u hu)
  rw [hsq v, hsq s, Real.sqrt_eq_rpow] at key
  exact key

/-! ### The two moment inequalities, reduced to the integrated differential inequality -/

section Reduction

variable {X : Sample B} {E : ℝ}

/-- **`U_{v,v} = 1` along the flow.**  This is what makes the left-hand side of (5.20) the
value at `u = v` of the path `u ↦ U_{u,v} ∘ (L-K)_u` whose `2p`-th moment the generator
identity differentiates. -/
theorem uker_self_lkT (hE : |E| ≤ 2) {n N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (ω : Ω) :
    Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.lkT X E N v ω σ) a
      = SumZeroDyn.lkT X E N v ω σ a := by
  have hxi : ∀ i, ‖((v : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro i
    simp only [xiOf]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0,
      norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
    exact hv1
  exact congrFun (Uker_self (B.L N) (B.three_le_L N) hxi _) a

/-- The same for the `Q_t`-projected tensor of (5.91). -/
theorem uker_self_Qop_lkT (hE : |E| ≤ 2) {n N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (ω : Ω) :
    Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ)) a
      = Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a := by
  have hxi : ∀ i, ‖((v : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro i
    simp only [xiOf]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0,
      norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
    exact hv1
  exact congrFun (Uker_self (B.L N) (B.three_le_L N) hxi _) a

/-- **(5.20) + (5.24) in moment form, from the integrated differential inequality.**

This is the body of `RBM.MomentDuhamel.Hyp.momentDuhamel` at one `(p, N, σ, v, a)`, reduced to
the hypothesis `hdu` — the *integrated* form of the differential inequality for
`ψ_u = (E |(U_{u,v} ∘ (L-K)_u)_a|^{2p})^{1/p}` that the generator identity produces.  Nothing
but `hdu` (and the two integrability side conditions and the least upper bound) is left. -/
theorem momentDuhamel_body_of_integral_le (hE : |E| ≤ 2) {n N p : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    {s v : ℝ} (hsv : s ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {F : ∀ N, ℝ → Matrix (B.Idx N) (B.Idx N) ℂ → (Fin (n + 2) → Bool) →
      LoopArg (B.L N) (n + 2) → ℂ}
    {ψ f g : ℝ → ℝ} {c M : ℝ} (hc0 : 0 ≤ c)
    (hψ : ∀ u, ψ u = (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P) ^ ((1 : ℝ) / p))
    (hf : ∀ u, f u = momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (F N u (X.H N u ω) σ) a‖))
    (hg : ∀ u, g u = momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖))
    (hM : IsLUB (ψ '' Set.Icc s v) M)
    (hintψf : ∀ u ∈ Set.Icc s v, IntervalIntegrable (fun r =>
      momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N r ω σ) a‖) * f r) volume s u)
    (hintf : IntervalIntegrable f volume s v)
    (hintg : IntervalIntegrable g volume s v)
    (hdu : ∀ u ∈ Set.Icc s v, ψ u ≤ ψ s
      + 2 * (∫ r in s..u, momNorm B.P (2 * p) (fun ω =>
          ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (SumZeroDyn.lkT X E N r ω σ) a‖) * f r)
      + c * ∫ r in s..u, g r) :
    momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
      ≤ momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.lkT X E N s ω σ) a‖)
        + 2 * (∫ u in s..v, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (F N u (X.H N u ω) σ) a‖))
        + (c * ∫ u in s..v, momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖)) ^ ((1 : ℝ) / 2) := by
  have hf0 : ∀ r ∈ Set.Icc s v, 0 ≤ f r := by
    intro r _; rw [hf r]; exact momNorm_nonneg _ _ _
  have hg0 : ∀ r ∈ Set.Icc s v, 0 ≤ g r := by
    intro r _; rw [hg r]; exact momNorm_nonneg _ _ _
  have key := momNorm_le_of_integral_le (P := B.P) (p := p)
    (Y := fun u ω => ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N u ω σ) a‖)
    (ψ := ψ) (f := f) (g := g) (c := c) (M := M)
    hsv hψ hf0 hg0 hc0 hM hintψf hintf hintg hdu
  simpa only [hf, hg, uker_self_lkT hE hv0 hv1 σ a] using key

/-- **(5.91) + (5.103) in moment form, from the integrated differential inequality.**

The `Q_t` route has three drift terms rather than one; `hdu` carries their sum, and the
conclusion splits it again, which is why each of the three is assumed interval integrable. -/
theorem momentDuhamelQ_body_of_integral_le (hE : |E| ≤ 2) {n N p : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    {s v : ℝ} (hsv : s ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {F : ∀ N, ℝ → Matrix (B.Idx N) (B.Idx N) ℂ → (Fin (n + 2) → Bool) →
      LoopArg (B.L N) (n + 2) → ℂ}
    {ψ f₁ f₂ f₃ g : ℝ → ℝ} {c M : ℝ} (hc0 : 0 ≤ c)
    (hψ : ∀ u, ψ u = (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖| ^ (2 * p) ∂B.P)
        ^ ((1 : ℝ) / p))
    (hf₁ : ∀ u, f₁ u = momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (F N u (X.H N u ω) σ)) a‖))
    (hf₂ : ∀ u, f₂ u = momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω σ)) a‖))
    (hf₃ : ∀ u, f₃ u = momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
    (hg : ∀ u, g u = momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
        (Fin.append a a)‖))
    (hM : IsLUB (ψ '' Set.Icc s v) M)
    (hintψf : ∀ u ∈ Set.Icc s v, IntervalIntegrable (fun r =>
      momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (B.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT X E N r ω σ)) a‖)
      * (f₁ r + f₂ r + f₃ r)) volume s u)
    (hint₁ : IntervalIntegrable f₁ volume s v) (hint₂ : IntervalIntegrable f₂ volume s v)
    (hint₃ : IntervalIntegrable f₃ volume s v) (hintg : IntervalIntegrable g volume s v)
    (hdu : ∀ u ∈ Set.Icc s v, ψ u ≤ ψ s
      + 2 * (∫ r in s..u, momNorm B.P (2 * p) (fun ω =>
          ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (Qop (B.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT X E N r ω σ)) a‖)
        * (f₁ r + f₂ r + f₃ r))
      + c * ∫ r in s..u, g r) :
    momNorm B.P (2 * p)
        (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
      ≤ momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Qop (B.L N) ((s : ℝ) : ℂ) (SumZeroDyn.lkT X E N s ω σ)) a‖)
        + 2 * (∫ u in s..v, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Qop (B.L N) ((u : ℝ) : ℂ) (F N u (X.H N u ω) σ)) a‖))
        + 2 * (∫ u in s..v, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N u ω σ)) a‖))
        + 2 * (∫ u in s..v, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
        + (c * ∫ u in s..v, momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
              (Fin.append a a)‖)) ^ ((1 : ℝ) / 2) := by
  have hf0 : ∀ r ∈ Set.Icc s v, 0 ≤ f₁ r + f₂ r + f₃ r := by
    intro r _
    rw [hf₁ r, hf₂ r, hf₃ r]
    have h1 := momNorm_nonneg B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((r : ℝ) : ℂ) (F N r (X.H N r ω) σ)) a‖)
    have h2 := momNorm_nonneg B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N r ω σ)) a‖)
    have h3 := momNorm_nonneg B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N r ω σ) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) r b) a‖)
    linarith
  have hg0 : ∀ r ∈ Set.Icc s v, 0 ≤ g r := by
    intro r _; rw [hg r]; exact momNorm_nonneg _ _ _
  have key := momNorm_le_of_integral_le (P := B.P) (p := p)
    (Y := fun u ω => ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖)
    (ψ := ψ) (f := fun r => f₁ r + f₂ r + f₃ r) (g := g) (c := c) (M := M)
    hsv hψ hf0 hg0 hc0 hM hintψf ((hint₁.add hint₂).add hint₃) hintg hdu
  have hsplit : (∫ r in s..v, (f₁ r + f₂ r + f₃ r))
      = (∫ r in s..v, f₁ r) + (∫ r in s..v, f₂ r) + (∫ r in s..v, f₃ r) := by
    rw [intervalIntegral.integral_add (hint₁.add hint₂) hint₃,
      intervalIntegral.integral_add hint₁ hint₂]
  rw [hsplit] at key
  simp only [hf₁, hf₂, hf₃, hg, uker_self_Qop_lkT hE hv0 hv1 σ a] at key
  linarith [key]

/-- **The least upper bound of `RBM.sqrt_le_of_integral_le` exists** as soon as `ψ` is bounded
above on the window — on the Gaussian model by the deterministic envelope `‖G_u‖ ≤ |Im z_u|⁻¹`
that also gives `RBM.MomentDuhamel.Hyp.integrable`.  So `hM` below is not an extra
assumption of substance, only a name for the supremum. -/
theorem exists_isLUB_Icc {ψ : ℝ → ℝ} {s v : ℝ} (hsv : s ≤ v) {C : ℝ}
    (hC : ∀ u ∈ Set.Icc s v, ψ u ≤ C) : ∃ M, IsLUB (ψ '' Set.Icc s v) M := by
  refine Real.exists_isLUB ⟨ψ s, ⟨s, ⟨le_rfl, hsv⟩, rfl⟩⟩ ⟨C, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  exact hC u hu

end Reduction

/-! ### The instance, with `F` pinned to `RBM.DriftDef.driftF` -/

section Instance

/-- **The pointwise drift identity (5.15) holds with `F := RBM.DriftDef.driftF`**, on any
window contained in `[0, 1)`.

This is `RBM.DriftDef.drift_split_gen` with its two side conditions discharged from the
window: `Im z_u = (1-u) Im m_E ≠ 0` needs `u < 1`, and `‖u m(σ) m(σ')‖ < 1` needs `0 ≤ u < 1`
together with `‖m‖ = 1`.  Neither needs `0 < u`: the `u`-derivative here is of
`v ↦ gloop(M, z_v)` and `v ↦ K_v` at a **frozen** matrix `M`, so the `√u` of the flow — and
with it the `0 < u` seam of T152 — never appears. -/
theorem drift_driftF (B : Band Ω) (E : ℝ) (hE : |E| < 2) {n N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (hM : M.IsHermitian)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) :
    ∃ dv : ℂ, HasDerivAt (fun v : ℝ => lkFun B E N v M σ a) dv u ∧
      dv + genLK B E N u M σ a
        = SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (lkFun B E N u M σ) a
          + DriftDef.driftF B E N u M σ a := by
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  refine DriftDef.drift_split_gen B E N u hM hz σ a fun b b' => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0,
    norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
  exact hu1

/-- **The first outstanding obligation: (5.20) + (5.24) in moment form**, with the drift
already substituted by `RBM.DriftDef.driftF`.

This is the field `RBM.MomentDuhamel.Hyp.momentDuhamel` read with `F := driftF`.  It is a
`Prop` about objects all of which are definitions — `lkT`, `Uker`, `driftF`, `eeFun` — plus
the constant `cMD`; there is no datum in it that an instance could choose. -/
def MomentIneq (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) (cMD : ℕ → ℝ) : Prop :=
  ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ),
    s N ≤ v → v ≤ t N → ∀ a : LoopArg (B.L N) (n + 2),
      momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
        ≤ momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N (s N) ω σ) a‖)
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (DriftDef.driftF B E N u (X.H N u ω) σ) a‖))
          + (cMD p * ∫ u in (s N)..v, momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖)) ^ ((1 : ℝ) / 2)

/-- **The second outstanding obligation: (5.91) + (5.103) in moment form**, again with
`F := RBM.DriftDef.driftF`.  This is `RBM.MomentDuhamel.Hyp.momentDuhamelQ`. -/
def MomentIneqQ (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) (cMD : ℕ → ℝ) : Prop :=
  ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ),
    s N ≤ v → v ≤ t N → ∀ a : LoopArg (B.L N) (n + 2),
      momNorm B.P (2 * p)
          (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
        ≤ momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω σ)) a‖)
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖))
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N u ω σ)) a‖))
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
          + (cMD p * ∫ u in (s N)..v, momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
                (Fin.append a a)‖)) ^ ((1 : ℝ) / 2)

/-- **The `integrable` field, as a named obligation.**  On the Gaussian model it is
`RBM.Gauss.integrable_lkT_pow` (`integrable_gauss` below); over an arbitrary `RBM.Band` the
deterministic envelope `‖G‖ ≤ η⁻¹` is not available, so it is carried. -/
def LkIntegrable (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ (q N : ℕ) (u : ℝ), s N ≤ u → u ≤ t N → ∀ (σ : Fin (n + 2) → Bool) a,
    Integrable (fun ω => |‖SumZeroDyn.lkT X E N u ω σ a‖| ^ q) B.P

/-- **A producer for `RBM.MomentDuhamel.Hyp`.**

Five of the seven fields are discharged here and none of them is data the caller may choose:

* `F` is `RBM.DriftDef.driftF`, a definition in the Green function of the matrix (T58);
* `drift` is `RBM.DriftDef.drift_split_gen` (T58, generalising T163 from loop length `2`),
  with its two side conditions read off the window `[0, 1)`;
* `cMD`, `cMD_nonneg` are the one acknowledged degree of freedom, harmless because `cMD`'s
  type `ℕ → ℝ` forbids dependence on `N` and the same constant reappears in the consumer's
  own hypothesis (the fiat audit of `RBM1D/Gauss/MomentDuhamel.lean`);
* `integrable` is `RBM.MomentDuhamel.integrable_gauss` on the Gaussian model.

What is left are exactly the two moment inequalities, **with `F` already substituted**:
`MomentIneq` and `MomentIneqQ` are statements about `driftF`. -/
noncomputable def hypOfMoments (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (cMD : ℕ → ℝ) (hcMD : ∀ p, 0 ≤ cMD p)
    (hint : LkIntegrable X E s t n)
    (hmd : MomentIneq X E s t n cMD) (hmdQ : MomentIneqQ X E s t n cMD) :
    Hyp X E s t n where
  F := fun N u M σ a => DriftDef.driftF B E N u M σ a
  drift := fun N _u hsu hut M hM σ a =>
    drift_driftF B E hE (le_trans (hs0 N) hsu) (lt_of_le_of_lt hut (ht1 N)) M hM σ a
  cMD := cMD
  cMD_nonneg := hcMD
  integrable := hint
  momentDuhamel := hmd
  momentDuhamelQ := hmdQ

/-- **The fiat audit, on the produced instance**: its drift field is `RBM.DriftDef.driftF`,
by `rfl`.  There is nothing to choose. -/
theorem hypOfMoments_F (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (cMD : ℕ → ℝ) (hcMD : ∀ p, 0 ≤ cMD p) (hint : LkIntegrable X E s t n)
    (hmd : MomentIneq X E s t n cMD) (hmdQ : MomentIneqQ X E s t n cMD) :
    (hypOfMoments X E s t n hE hs0 ht1 cMD hcMD hint hmd hmdQ).F
      = fun N u M σ a => DriftDef.driftF B E N u M σ a := rfl

/-- **The fiat audit, on an arbitrary instance**: *every* `RBM.MomentDuhamel.Hyp` over a
window contained in `[0, 1)` has `F = driftF` at every Hermitian matrix.  So `F` is not a
degree of freedom of the interface at all — this is `RBM.DriftDef.F_eq_driftF` with the two
side conditions discharged from the window. -/
theorem F_eq_driftF_of_window {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (H : Hyp X E s t n) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {N : ℕ} {u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) :
    H.F N u M σ a = DriftDef.driftF B E N u M σ a := by
  have hu0 : 0 ≤ u := le_trans (hs0 N) hsu
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 N)
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  refine DriftDef.F_eq_driftF H hsu hut hM hz σ a fun b b' => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0,
    norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
  exact hu1

/-- **`LkIntegrable` on the Gaussian model**, from `RBM.Gauss.integrable_lkT_pow`: the
deterministic envelope `‖G_u‖ ≤ |Im z_u|⁻¹` makes every power integrable at every time of the
window, and the window's `t_N < 1` is exactly what keeps `Im z_u ≠ 0`. -/
theorem integrable_gauss (d : Gauss.Dims) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    LkIntegrable (Gauss.sample d) E s t n := by
  intro q N u hsu hut σ a
  have hu0 : 0 ≤ u := le_trans (hs0 N) hsu
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 N)
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  exact Gauss.integrable_lkT_pow d E N hz q (by omega) σ a

/-- **The Gaussian instance**: over the Gaussian model only the two moment inequalities are
left. -/
noncomputable def gaussHypOfMoments (d : Gauss.Dims) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (cMD : ℕ → ℝ) (hcMD : ∀ p, 0 ≤ cMD p)
    (hmd : MomentIneq (Gauss.sample d) E s t n cMD)
    (hmdQ : MomentIneqQ (Gauss.sample d) E s t n cMD) :
    Hyp (Gauss.sample d) E s t n :=
  hypOfMoments (Gauss.sample d) E s t n hE hs0 ht1 cMD hcMD
    (integrable_gauss d E s t n hE hs0 ht1) hmd hmdQ

/-! ### Satisfiability checks at the degenerate points -/

section Degenerate

/-- **`MomentIneq` at the left endpoint `v = s N`.**  Both time integrals are over a
degenerate interval and `U_{s,s} = 1`, so the inequality holds — with equality.  This is the
check T164/T172 found missing elsewhere: the field is *not* vacuously false where the window
collapses. -/
theorem momentIneq_body_self (X : Sample B) (E : ℝ) (hE : |E| ≤ 2) {n N p : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (c : ℝ) :
    momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N s ω σ a‖)
      ≤ momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (SumZeroDyn.lkT X E N s ω σ) a‖)
        + 2 * (∫ u in s..s, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (DriftDef.driftF B E N u (X.H N u ω) σ) a‖))
        + (c * ∫ u in s..s, momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖)) ^ ((1 : ℝ) / 2) := by
  simp only [uker_self_lkT hE hs0 hs1 σ a, intervalIntegral.integral_same, mul_zero,
    Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0), add_zero]
  exact le_rfl

/-- **`MomentIneqQ` at the left endpoint `v = s N`**, for the same reason. -/
theorem momentIneqQ_body_self (X : Sample B) (E : ℝ) (hE : |E| ≤ 2) {n N p : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (c : ℝ) :
    momNorm B.P (2 * p)
        (fun ω => ‖Qop (B.L N) ((s : ℝ) : ℂ) (SumZeroDyn.lkT X E N s ω σ) a‖)
      ≤ momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (Qop (B.L N) ((s : ℝ) : ℂ) (SumZeroDyn.lkT X E N s ω σ)) a‖)
        + 2 * (∫ u in s..s, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖))
        + 2 * (∫ u in s..s, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N u ω σ)) a‖))
        + 2 * (∫ u in s..s, momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
        + (c * ∫ u in s..s, momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((s : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
              (Fin.append a a)‖)) ^ ((1 : ℝ) / 2) := by
  simp only [uker_self_Qop_lkT hE hs0 hs1 σ a, intervalIntegral.integral_same, mul_zero,
    Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0), add_zero]
  exact le_rfl

/-- **No `0 < u` seam in `drift`.**  The identity is asserted at `u = 0` too, and holds there:
the `u`-derivative is of `v ↦ gloop(M, z_v)` and `v ↦ K_v` at a frozen matrix, so the `√u` of
the flow — the reason T152's closed-interval drift identity was unsatisfiable at `s = 0` —
does not occur.  (`H_0 = 0` is Hermitian, so the Hermitian restriction costs nothing here
either.) -/
example (E : ℝ) (hE : |E| < 2) {n N : ℕ}
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (hM : M.IsHermitian)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) :
    ∃ dv : ℂ, HasDerivAt (fun v : ℝ => lkFun B E N v M σ a) dv 0 ∧
      dv + genLK B E N 0 M σ a
        = SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((0 : ℝ) : ℂ) (lkFun B E N 0 M σ) a
          + DriftDef.driftF B E N 0 M σ a :=
  drift_driftF B E hE le_rfl one_pos M hM σ a

end Degenerate

end Instance


/-! ### The field, under its own quantifiers -/

section Wiring

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} {cMD : ℕ → ℝ}

/-- **`MomentIneq` from the integrated differential inequality.**

`momentDuhamel_body_of_integral_le` under the quantifiers of the field, with
`F := RBM.DriftDef.driftF` and `c := cMD p`.  The hypothesis is *exactly* what the Gaussian
generator identity followed by Hölder has to deliver, and nothing more: for each
`(p, N, σ, v, a)` the function `ψ_u = (E |(U_{u,v} ∘ (L-K)_u)_a|^{2p})^{1/p}`, its supremum on
the window (`exists_isLUB_Icc`), the two integrands, and the integrated inequality.

With `cMD p = 2p - 1` this is the closing of (5.20) + (5.24): the generator gives
`ψ' ≤ 2 √ψ ‖U ∘ F‖_{2p} + (2p-1) ‖(U ⊗ U) ∘ (E ⊗ E)‖_p`, whose integrated form is `hdu`.

The `Q_t` route is the same three lines over `momentDuhamelQ_body_of_integral_le`, with the
one drift integrand replaced by the three of (5.91). -/
theorem momentIneq_of_diffIneq (hE : |E| ≤ 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hc : ∀ p, 0 ≤ cMD p)
    (h : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
      ∀ a : LoopArg (B.L N) (n + 2), ∃ ψ f g : ℝ → ℝ, ∃ M : ℝ,
        (∀ u, ψ u = (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P) ^ ((1 : ℝ) / p))
        ∧ (∀ u, f u = momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (DriftDef.driftF B E N u (X.H N u ω) σ) a‖))
        ∧ (∀ u, g u = momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖))
        ∧ IsLUB (ψ '' Set.Icc (s N) v) M
        ∧ (∀ u ∈ Set.Icc (s N) v, IntervalIntegrable (fun r =>
              momNorm B.P (2 * p) (fun ω =>
                ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N r ω σ) a‖) * f r) volume (s N) u)
        ∧ IntervalIntegrable f volume (s N) v
        ∧ IntervalIntegrable g volume (s N) v
        ∧ (∀ u ∈ Set.Icc (s N) v, ψ u ≤ ψ (s N)
              + 2 * (∫ r in (s N)..u, momNorm B.P (2 * p) (fun ω =>
                  ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT X E N r ω σ) a‖) * f r)
              + cMD p * ∫ r in (s N)..u, g r)) :
    MomentIneq X E s t n cMD := by
  intro p hp N σ v hsv hvt a
  obtain ⟨ψ, f, g, M, hψ, hf, hg, hM, hintψf, hintf, hintg, hdu⟩ := h p hp N σ v hsv hvt a
  exact momentDuhamel_body_of_integral_le (X := X) (E := E)
    (F := fun N u M σ a => DriftDef.driftF B E N u M σ a)
    hE σ a hsv (le_trans (hs0 N) hsv) (lt_of_le_of_lt hvt (ht1 N)) (hc p)
    hψ hf hg hM hintψf hintf hintg hdu

end Wiring

end MomentDuhamel
end RBM



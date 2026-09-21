/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.LoopC2

/-!
# The Gaussian unloading of the moment Duhamel (T132b)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  `RBM1D/Gauss/MomentDuhamel.lean` (T132a, repaired by T145) states the primed
interface `RBM.MomentDuhamel.Hyp`; this file supplies the two analytic ingredients the ticket
names for discharging it on the Gaussian flow `H_u = √u • X`, and records precisely where the
discharge stops.

## Main results

* `RBM.Gauss.hasDerivAt_integral_Psi`, `RBM.Gauss.hasDerivAt_integral_Psi_pairs` —
  **the generator identity with explicit time dependence**:
  `∂_u E[Ψ(u, H_u)] = E[∂_1 Ψ(u, H_u)] + ½ ∑_{ij} S_ij E[∂_ij ∂_ji Ψ(u, ·)(H_u)]`.
  `RBM.Gauss.hasDerivAt_integral_Phi_pairs` (T71) is the special case `Ψ v = Φ`, where the
  first term drops out.  The proof is T71's, with two changes: the chain rule along the flow
  now produces the extra term `∂_1 Ψ` (`RBM.Gauss.hasDerivAt_Psi_Hflow`), and the domination
  of the difference quotients has to be uniform in the time as well as in `ω`.
* `RBM.Gauss.TestFunT` — the admissible class: `ContDiffAt ℝ 2` **jointly in `(u, M)`** at
  every `(u, M)` with `u` in a time window `T`, plus bounds on `Ψ`, `∂_M Ψ`, `∂²_M Ψ` and
  `∂_1 Ψ` that are uniform over `T`.  Its slices are T71's `RBM.Gauss.TestFun`
  (`RBM.Gauss.TestFunT.slice`).  The window is *not* cosmetic: the spectral parameter
  `z_u = E + (1 - u) m_E` has `Im z_u → 0` as `u → 1`, so no bound of this kind is available
  on all of `ℝ` (see `RBM.Gauss.contDiffAt_resH_zt`).
* `RBM.Gauss.contDiffAt_resH_path`, `RBM.Gauss.contDiff_resH_path`,
  `RBM.Gauss.contDiffAt_resH_zt` — **the `(z, M)`-joint `C²` regularity of the resolvent**,
  along an arbitrary `C²` spectral path, and then along the path `u ↦ z_u` of (2.33).
  T141's `RBM.Gauss.BddC1On` is the *first-order*, set-localised class; what is needed here is
  second-order and joint, and it turns out not to need a new bounded class at all: the joint
  `C²` statement is `RBM.Gauss.contDiff_resH`'s proof with the pair `(u, M)` in place of `M`,
  because `(u, M) ↦ (M + Mᴴ)/2 - z_u` is already jointly `C²` and `Ring.inverse` is `C^∞` at
  units.
* `RBM.Gauss.integrable_lkT_pow` — the field `RBM.MomentDuhamel.Hyp.integrable`, for the
  Gaussian sample, **at every time with `Im z_u ≠ 0`**, which is exactly what that field now
  asks for after T147's repair restricted it to the window `[s_N, t_N]`.
* `RBM.Gauss.genLK_eq` — `RBM.MomentDuhamel.genLK` *is* `½ ∑_{ij} Sblk_ij ∂_ij ∂_ji`, the
  generator whose weight the identity above carries.  (An earlier version of `genLK` divided
  `Sblk` by `W` a second time and was therefore `W⁻¹ 𝓛`; that is repaired, and this theorem is
  what pins the two together.)

## What this file does *not* do

The two moment inequalities `RBM.MomentDuhamel.Hyp.momentDuhamel` and `.momentDuhamelQ` are
not proved here; the chain from the identity above to them (pointwise expansion of `|Φ|^{2p}`
through T72's `RBM.Gauss.genMomentPt_le`, substitution of the drift, Hölder, and T132a's
`RBM.sqrt_le_of_integral_le`) is the remaining work of T132b, as is the Gaussian instance of
`RBM.MomentDuhamel.Hyp` itself.  Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-! ### The time derivative of a time-dependent test function -/

/-- `∂_1 Ψ`, the derivative of `Ψ` in the *time* slot at a frozen matrix. -/
noncomputable def timeD1 (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  deriv (fun s : ℝ => Ψ s M) u

/-- **The joint derivative splits**: `DΨ(u, M)[a, B] = a ∂_1 Ψ(u, M) + ∂_M Ψ(u, ·)[B]`.  This
is the only place where the two slots interact, and it is what turns the chain rule along the
flow into "explicit time derivative plus matrix derivative". -/
theorem fderiv_uncurry_apply (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (h : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M))
    (a : ℝ) (B : Matrix (d.Idx N) (d.Idx N) ℂ) :
    fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M) (a, B)
      = a • timeD1 Ψ u M + fderiv ℝ (Ψ u) M B := by
  have hright : fderiv ℝ (Ψ u) M B
      = fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)
          ((0 : ℝ), B) := by
    have hc : HasFDerivAt (Ψ u)
        ((fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Matrix (d.Idx N) (d.Idx N) ℂ))) M :=
      (h.hasFDerivAt).comp M (hasFDerivAt_prodMk_right (𝕜 := ℝ) u M)
    rw [hc.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hleft : fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)
      ((a : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ)) = a • timeD1 Ψ u M := by
    have hc : HasFDerivAt (fun s : ℝ => Ψ s M)
        ((fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)).comp
          (ContinuousLinearMap.inl ℝ ℝ (Matrix (d.Idx N) (d.Idx N) ℂ))) u := by
      have hh := (h.hasFDerivAt).comp u (hasFDerivAt_prodMk_left (𝕜 := ℝ) u M)
      exact hh
    have hd := hc.hasDerivAt
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at hd
    have hsm : ((a : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ))
        = a • ((1 : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ)) := by simp
    rw [hsm, map_smul, timeD1, hd.deriv]
  have hsplit : ((a : ℝ), B) = ((a : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ)) + ((0 : ℝ), B) := by
    simp
  rw [hsplit, map_add, hleft, hright]

/-- `∂_1 Ψ` read off the joint derivative. -/
theorem timeD1_eq_fderiv_uncurry (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (h : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)) :
    timeD1 Ψ u M
      = fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)
          ((1 : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ)) := by
  rw [fderiv_uncurry_apply u M h 1 0]
  simp

/-- **The chain rule along the Gaussian flow, with explicit time dependence.**
`d/du Ψ(u, √u X) = ∂_1 Ψ(u, H_u) + (2√u)⁻¹ ∂_X Ψ(u, ·)(H_u)`.  Compare
`RBM.Gauss.hasDerivAt_Phi_Hflow`, which is the case with no `u` in the first slot. -/
theorem hasDerivAt_Psi_Hflow {u : ℝ} (hu : 0 < u) (ω : Ω d)
    (h : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2)
      (u, Hflow d N u ω)) :
    HasDerivAt (fun s : ℝ => Ψ s (Hflow d N s ω))
      (timeD1 Ψ u (Hflow d N u ω)
        + (1 / (2 * Real.sqrt u)) • fderiv ℝ (Ψ u) (Hflow d N u ω) (Xmat d N ω)) u := by
  have hline : HasDerivAt (fun s : ℝ => Real.sqrt s • Xmat d N ω)
      ((1 / (2 * Real.sqrt u)) • Xmat d N ω) u :=
    (Real.hasDerivAt_sqrt hu.ne').smul_const _
  have hline' : HasDerivAt (fun s : ℝ => Hflow d N s ω)
      ((1 / (2 * Real.sqrt u)) • Xmat d N ω) u := by
    refine hline.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [Hflow_eq_realSmul]
  have hpath : HasDerivAt (fun s : ℝ => (s, Hflow d N s ω))
      ((1 : ℝ), (1 / (2 * Real.sqrt u)) • Xmat d N ω) u :=
    (hasDerivAt_id u).prodMk hline'
  have key : HasDerivAt (fun s : ℝ => Ψ s (Hflow d N s ω))
      (fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, Hflow d N u ω)
        ((1 : ℝ), (1 / (2 * Real.sqrt u)) • Xmat d N ω)) u := by
    have hh := (h.hasFDerivAt).comp_hasDerivAt u hpath
    exact hh
  rwa [fderiv_uncurry_apply u (Hflow d N u ω) h 1 _, map_smul, one_smul] at key

/-! ### The admissible class -/

/-- **The time-dependent test functions on the window `T`.**

`contDiffAt` is joint `C²` in `(u, M)`, asserted only for `u ∈ T`; the four bounds are the
ones of `RBM.Gauss.TestFun` plus one on the time derivative, all uniform over `T`.

Why the window.  On the application `Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}` every bound
is a power of `(Im z_u)⁻¹ = ((1 - u) Im m_E)⁻¹`, which blows up as `u → 1`; and at `u = 1` the
resolvent is not even defined.  So a globally-in-time version of this class is empty for the
functions we care about, whereas `T = Set.Iio t` with `t < 1` is exactly the paper's window. -/
structure TestFunT (d : Dims) (N : ℕ) (T : Set ℝ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) : Prop where
  /-- Joint `C²` in `(time, matrix)` over the window. -/
  contDiffAt : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)
  /-- `Ψ` is bounded, uniformly over the window. -/
  bdd₀ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖Ψ u M‖ ≤ C
  /-- `∂_M Ψ` is bounded, uniformly over the window. -/
  bdd₁ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖fderiv ℝ (Ψ u) M‖ ≤ C
  /-- `∂²_M Ψ` is bounded, uniformly over the window. -/
  bdd₂ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖fderiv ℝ (fderiv ℝ (Ψ u)) M‖ ≤ C
  /-- `∂_1 Ψ` is bounded, uniformly over the window. -/
  bddT : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖timeD1 Ψ u M‖ ≤ C

variable {T : Set ℝ}

/-- Each slice of a `RBM.Gauss.TestFunT` is a `RBM.Gauss.TestFun` of T71. -/
theorem TestFunT.slice (h : TestFunT d N T Ψ) {u : ℝ} (hu : u ∈ T) : TestFun d N (Ψ u) where
  contDiff := by
    rw [contDiff_iff_contDiffAt]
    intro M
    have hc := (h.contDiffAt u hu M).comp M
      ((contDiff_const.prodMk contDiff_id).contDiffAt (x := M))
    exact hc
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, hC u hu⟩
  bdd₁ := let ⟨C, hC⟩ := h.bdd₁; ⟨C, hC u hu⟩
  bdd₂ := let ⟨C, hC⟩ := h.bdd₂; ⟨C, hC u hu⟩

/-- `∂_1 Ψ(u, ·)` is continuous in the matrix, so its composition with the flow is a
measurable function of `ω`. -/
theorem continuous_timeD1 (h : TestFunT d N T Ψ) {u : ℝ} (hu : u ∈ T) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ => timeD1 Ψ u M := by
  rw [continuous_iff_continuousAt]
  intro M
  have hca : ContinuousAt
      (fderiv ℝ fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M) :=
    (h.contDiffAt u hu M).continuousAt_fderiv (by norm_num)
  have hp : ContinuousAt (fun M' : Matrix (d.Idx N) (d.Idx N) ℂ => (u, M')) M :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hmain : ContinuousAt (fun M' : Matrix (d.Idx N) (d.Idx N) ℂ =>
      fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M')
        ((1 : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ))) M :=
    (hca.comp hp).clm_apply continuousAt_const
  refine hmain.congr (Eventually.of_forall fun M' => ?_)
  exact (timeD1_eq_fderiv_uncurry u M'
    ((h.contDiffAt u hu M').differentiableAt (by norm_num))).symm

/-! ### The generator identity with explicit time dependence -/

/-- **The generator identity of the moment route, with explicit time dependence, coordinate
form.**

`∂_u E[Ψ(u, H_u)] = E[∂_1 Ψ(u, H_u)] + ½ ∑_α S_α E[∂_α ∂_α Ψ(u, ·)(H_u)]`.

`RBM.Gauss.hasDerivAt_integral_Phi` is the special case `Ψ v = Φ`, where `∂_1 Ψ = 0`.  The
proof is the same two steps — differentiate under the integral sign, then Stein's identity in
each coordinate — with the chain rule of `RBM.Gauss.hasDerivAt_Psi_Hflow` contributing the
extra first term, and with the domination taken uniformly over the window `T`. -/
theorem hasDerivAt_integral_Psi (hst : MatrixStein d) (h : TestFunT d N T Ψ)
    {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
          ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)) u := by
  classical
  have huT : u ∈ T := mem_of_mem_nhds hT
  obtain ⟨C₀, hC₀⟩ := h.bdd₀
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  obtain ⟨CT, hCT⟩ := h.bddT
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ u huT 0)
  have hu2 : (0 : ℝ) < u / 2 := by linarith
  have hS : T ∩ Set.Ioi (u / 2) ∈ nhds u := Filter.inter_mem hT (Ioi_mem_nhds (by linarith))
  have hcontF : ∀ x ∈ T, Continuous fun ω : Ω d => Ψ x (Hflow d N x ω) := fun x hx =>
    (h.slice hx).contDiff.continuous.comp (continuous_Hflow d N x)
  have hcontT : ∀ x ∈ T, Continuous fun ω : Ω d => timeD1 Ψ x (Hflow d N x ω) := fun x hx =>
    (continuous_timeD1 h hx).comp (continuous_Hflow d N x)
  have hcontS : ∀ x ∈ T, Continuous fun ω : Ω d =>
      (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p := by
    intro x hx
    have hsum : Continuous fun ω : Ω d => ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p :=
      continuous_finsetSum (usedCoord d N) fun p _ =>
        (continuous_apply (crd d N p)).smul (continuous_coordD1 (h.slice hx) x p)
    exact hsum.const_smul (1 / (2 * Real.sqrt x))
  have hcg' : ∀ p : d.Idx N × d.Idx N × Bool,
      Continuous fun ω : Ω d => Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p :=
    fun p => (continuous_coordD2 (h.slice huT) u p).const_smul (Real.sqrt u)
  have hdiff : ∀ᵐ ω ∂(P d), ∀ x ∈ T ∩ Set.Ioi (u / 2),
      HasDerivAt (fun s : ℝ => Ψ s (Hflow d N s ω))
        (timeD1 Ψ x (Hflow d N x ω) + (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p) x := by
    refine Eventually.of_forall fun ω x hx => ?_
    have hx0 : 0 < x := lt_trans hu2 hx.2
    have := hasDerivAt_Psi_Hflow hx0 ω
      ((h.contDiffAt x hx.1 (Hflow d N x ω)).differentiableAt (by norm_num))
    rwa [fderiv_apply_Xmat] at this
  have hbound : ∀ᵐ ω ∂(P d), ∀ x ∈ T ∩ Set.Ioi (u / 2),
      ‖timeD1 Ψ x (Hflow d N x ω) + (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p‖
        ≤ CT + (1 / (2 * Real.sqrt (u / 2))) * ∑ p ∈ usedCoord d N,
            |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
    refine Eventually.of_forall fun ω x hx => ?_
    have hx0 : 0 < x := lt_trans hu2 hx.2
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hs2 : 0 < Real.sqrt (u / 2) := Real.sqrt_pos.2 hu2
    have hmono : Real.sqrt (u / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (le_of_lt hx.2)
    refine le_trans (norm_add_le _ _) (add_le_add (hCT x hx.1 _) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hA : ‖∑ p ∈ usedCoord d N, ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p‖
        ≤ ∑ p ∈ usedCoord d N, |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD1_le (hC₁ x hx.1) _ p) (abs_nonneg _)
    have hB : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (u / 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    exact mul_le_mul hB hA (norm_nonneg _) (by positivity)
  have hbndint : Integrable (fun ω : Ω d => CT + (1 / (2 * Real.sqrt (u / 2))) *
      ∑ p ∈ usedCoord d N, |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)) (P d) :=
    (integrable_const CT).add (Integrable.const_mul (integrable_finsetSum _ fun p _ =>
      ((integrable_coord d (crd d N p)).abs).mul_const _) _)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P d) (𝕜 := ℝ)
    (F := fun (s : ℝ) (ω : Ω d) => Ψ s (Hflow d N s ω))
    (F' := fun (s : ℝ) (ω : Ω d) => timeD1 Ψ s (Hflow d N s ω)
      + (1 / (2 * Real.sqrt s)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ s) (Hflow d N s ω) p)
    (x₀ := u) (s := T ∩ Set.Ioi (u / 2)) hS
    (Filter.eventually_of_mem hS fun x hx => (hcontF x hx.1).aestronglyMeasurable)
    (integrable_of_continuous_of_bound (hcontF u huT) fun ω => hC₀ u huT _)
    (((hcontT u huT).add (hcontS u huT)).aestronglyMeasurable) hbound hbndint hdiff
  have hint : ∀ p ∈ usedCoord d N,
      Integrable (fun ω : Ω d => ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) (P d) := by
    intro p _
    exact (integrable_coord d (crd d N p)).smul_bdd (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)
      (continuous_coordD1 (h.slice huT) u p).aestronglyMeasurable
      (Eventually.of_forall fun ω => norm_coordD1_le (hC₁ u huT) _ p)
  have hstein : ∀ p ∈ usedCoord d N,
      ∫ ω, ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p ∂(P d)
        = (gvar d (crd d N p) : ℝ) •
            (Real.sqrt u • ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)) := by
    intro p hp
    rw [hst.stein (crd d N p) _ (fun ω => Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p)
        (continuous_coordD1 (h.slice huT) u p)
        (hcg' p)
        (finDep_of_Hflow d N u fun M => coordD1 d N (Ψ u) M p)
        (finDep_of_Hflow d N u fun M => Real.sqrt u • coordD2 d N (Ψ u) M p)
        (fun ω => hasDerivAt_coordD1_update (h.slice huT) u ω hp)
        ⟨C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖, fun ω => norm_coordD1_le (hC₁ u huT) _ p⟩
        ⟨|Real.sqrt u| * (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖),
          fun ω => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (norm_coordD2_le (hC₂ u huT) _ p) (abs_nonneg _)⟩,
      integral_smul]
  have hIcalc : ∫ ω, ((1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d)
      = (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d) := by
    rw [integral_smul, integral_finsetSum _ hint, Finset.sum_congr rfl hstein,
      Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [smul_smul]
    congr 1
    field_simp
  have hsplit : ∫ ω, (timeD1 Ψ u (Hflow d N u ω)
        + (1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d)
      = (∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + ∫ ω, ((1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
            ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d) :=
    integral_add (integrable_of_continuous_of_bound (hcontT u huT) fun ω => hCT u huT _)
      (Integrable.smul (1 / (2 * Real.sqrt u) : ℝ) (integrable_finsetSum _ hint))
  have hfin := hmain.2
  rwa [hsplit, hIcalc] at hfin

/-- **The generator identity with explicit time dependence, in the paper's `∑_{ij} S_ij` form.**

`∂_u E[Ψ(u, H_u)] = E[∂_1 Ψ(u, H_u)] + ½ ∑_i ∑_j S_ij E[∂_ij ∂_ji Ψ(u, ·)(H_u)]`.

This is the identity T132b's ticket asks for; `RBM.Gauss.hasDerivAt_integral_Phi_pairs` is the
case `Ψ v = Φ`.  Note the weight: it is `RBM.Sblk`, which already carries the `1/W` of
`S = S^{(B)} ⊗ S_W` — see `RBM.Gauss.genLK_eq` below. -/
theorem hasDerivAt_integral_Psi_pairs (hst : MatrixStein d) (h : TestFunT d N T Ψ)
    {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d)) u := by
  rw [← sum_used_eq_sum_pairs_coordD2 (h.slice (mem_of_mem_nhds hT)) u]
  exact hasDerivAt_integral_Psi hst h hu hT

/-! ### `(z, M)`-joint `C²` for the resolvent -/

section ResolventJoint

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The resolvent is jointly `C²` in `(time, matrix)` along a `C²` spectral path.**

This is the second ingredient T132b's ticket names.  T141's `RBM.Gauss.BddC1On` is first-order
and set-localised; the second-order joint statement needs no new class, because
`RBM.Gauss.resH` is `Ring.inverse` applied to `(u, M) ↦ (M + Mᴴ)/2 - z_u`, which is already
jointly `C^∞` when `z` is `C²`, and `Ring.inverse` is `C^∞` at units. -/
theorem contDiffAt_resH_path {z : ℝ → ℂ} {u : ℝ} (hz : ContDiffAt ℝ 2 z u)
    (hzim : (z u).im ≠ 0) (M : Matrix n n ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix n n ℂ => resH (z q.1) q.2) (u, M) := by
  have hsm : ContDiffAt ℝ 2 (fun q : ℝ × Matrix n n ℂ => z q.1 • (1 : Matrix n n ℂ)) (u, M) :=
    (hz.comp (u, M) contDiff_fst.contDiffAt).smul contDiffAt_const
  have hT : ContDiffAt ℝ 2
      (fun q : ℝ × Matrix n n ℂ => hermCLM n q.2 - z q.1 • (1 : Matrix n n ℂ)) (u, M) :=
    (((hermCLM n).contDiff.comp contDiff_snd).contDiffAt).sub hsm
  obtain ⟨v, hvs⟩ : ∃ v : (Matrix n n ℂ)ˣ,
      (v : Matrix n n ℂ) = hermCLM n M - z u • (1 : Matrix n n ℂ) :=
    ⟨(isUnit_resH_arg hzim M).unit, IsUnit.unit_spec _⟩
  have hg : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix n n ℂ))
      ((fun q : ℝ × Matrix n n ℂ => hermCLM n q.2 - z q.1 • (1 : Matrix n n ℂ)) (u, M)) := by
    show ContDiffAt ℝ 2 _ (hermCLM n M - z u • (1 : Matrix n n ℂ))
    rw [← hvs]
    exact contDiffAt_ringInverse ℝ v
  exact hg.comp (u, M) hT

/-- The global form of `RBM.Gauss.contDiffAt_resH_path`, when the path avoids the real axis at
every time. -/
theorem contDiff_resH_path {z : ℝ → ℂ} (hz : ContDiff ℝ 2 z) (hzim : ∀ u : ℝ, (z u).im ≠ 0) :
    ContDiff ℝ 2 (fun q : ℝ × Matrix n n ℂ => resH (z q.1) q.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨u, M⟩
  exact contDiffAt_resH_path hz.contDiffAt (hzim u) M

/-- **The resolvent along the spectral path `z_u = E + (1 - u) m_E` of (2.33) is jointly `C²`
in `(u, M)` at every `u` with `Im z_u ≠ 0`**, i.e. at every `u ≠ 1` when `|E| < 2`.

The hypothesis is stated as `(zt E u).im ≠ 0` rather than `u ≠ 1` so that the lemma does not
have to know `Im m_E ≠ 0`; on the paper's window `[s_N, t_N]` with `t_N < 1` and `|E| ≤ 2 - κ`
it is automatic. -/
theorem contDiffAt_resH_zt (Ev : ℝ) {u : ℝ} (hzim : (zt Ev u).im ≠ 0) (M : Matrix n n ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix n n ℂ => resH (zt Ev q.1) q.2) (u, M) := by
  refine contDiffAt_resH_path ?_ hzim M
  have hzC : ContDiff ℝ 2 fun s : ℝ => zt Ev s := by
    show ContDiff ℝ 2 fun s : ℝ => ((Ev : ℂ) + ((1 : ℂ) - (s : ℂ)) * mE Ev)
    exact contDiff_const.add
      ((contDiff_const.sub Complex.ofRealCLM.contDiff).mul contDiff_const)
  exact hzC.contDiffAt

end ResolventJoint

/-! ### `RBM.MomentDuhamel.genLK` is the generator of the Gaussian flow -/

/-- **`RBM.MomentDuhamel.genLK` *is* `𝓛 = ½ ∑_{ij} S_ij ∂_ij ∂_ji`**, with the weight
`RBM.Sblk` the Gaussian model actually has.

`RBM.Sblk L W i j = S^{(B)}_{ab} / W` is already the variance `E|X_ij|²` of the model
(`RBM.Gauss.gvar_diag`, `RBM.Gauss.gvar_offDiag`), and the generator of (2.34) weights
`∂_ij ∂_ji` by exactly that (`RBM.Gauss.hasDerivAt_integral_Phi_pairs`, `RBM.Gauss.genD`,
`RBM.Gauss.sumSblk_half_wirtPair`).  So the right-hand side below is the `𝓛` of (5.15), and
the identity says `genLK` is it — after the repair that removed a second division by `W` from
`RBM.MomentDuhamel.genLK`.  It is stated (rather than left implicit in the `rfl`) because it is
the bridge between the `Band`-level definition and the `Dims`-level generator identity
`hasDerivAt_integral_Psi_pairs` above, whose `½ ∑_i ∑_j Sblk_ij • ∫ wirtSecond` is literally
this expression. -/
theorem genLK_eq (d : Dims) (Ev : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (d.L N) m) :
    MomentDuhamel.genLK (band d) Ev N u M σ a
      = (2 : ℂ)⁻¹ * ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ)
          * wirtSecond d N (fun M' => MomentDuhamel.lkFun (band d) Ev N u M' σ a) M i j := rfl

/-! ### `RBM.MomentDuhamel.Hyp.integrable` for the Gaussian sample -/

/-- **The `integrable` field of `RBM.MomentDuhamel.Hyp`, for the Gaussian model.**

The deterministic envelope `‖G‖ ≤ η⁻¹` of T77 makes `(L - K)_{u,σ,a}` a bounded continuous
function of `ω`, so every power of its modulus is integrable.  The hypothesis
`(zt E u).im ≠ 0` is needed and cannot be dropped: at `u = 1` the spectral parameter is real,
`H_1 - E` is singular on a null set only, and no deterministic envelope exists.

`RBM.MomentDuhamel.Hyp.integrable` is now quantified over the window `[s N, t N]` only (T147
removed the over-quantification of `u` over all of `ℝ`, the same kind T145 had removed from
`drift`), so this theorem discharges that field verbatim once `(zt E u).im ≠ 0` is known on the
window — which is the paper's standing assumption `t_N < 1`, `|E| ≤ 2 - κ`. -/
theorem integrable_lkT_pow (d : Dims) (Ev : ℝ) (N : ℕ) {u : ℝ} (hzim : (zt Ev u).im ≠ 0)
    (q : ℕ) {m : ℕ} (hm : 1 ≤ m) (σ : Fin m → Bool) (a : LoopArg (d.L N) m) :
    Integrable (fun ω : Ω d =>
      |‖SumZeroDyn.lkT (sample d) Ev N u ω σ a‖| ^ q) ((band d).P) := by
  set I : LoopIdx (ZMod (d.L N)) := LoopData.idx ((σ, a) : LoopData (d.L N) m) with hI
  have hwf : I.WF := LoopData.idx_wf _
  have hlen : I.a.length = m := by
    simp [hI, LoopData.idx]
  have hn : 1 ≤ I.a.length := by rw [hlen]; exact hm
  have hη : (0 : ℝ) < |(zt Ev u).im| := abs_pos.2 hzim
  have h0 : Continuous fun ω : Ω d => SumZeroDyn.lkT (sample d) Ev N u ω σ a := by
    have hg := continuous_gloop_Hflow d N u hzim I
    exact hg.sub continuous_const
  have habs : (fun ω : Ω d => |‖SumZeroDyn.lkT (sample d) Ev N u ω σ a‖| ^ q)
      = fun ω : Ω d => ‖SumZeroDyn.lkT (sample d) Ev N u ω σ a‖ ^ q := by
    funext ω
    rw [abs_norm]
  rw [habs]
  refine integrable_of_continuous_of_bound (h0.norm.pow q)
    (C := (|(zt Ev u).im|⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1)
      + ‖(band d).Kval Ev N u I‖) ^ q) fun ω => ?_
  have hb : ‖SumZeroDyn.lkT (sample d) Ev N u ω σ a‖
      ≤ |(zt Ev u).im|⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1)
        + ‖(band d).Kval Ev N u I‖ := by
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ le_rfl)
    exact norm_gloop_le_of_le_abs_im (Hflow_isHermitian d N u ω) hη le_rfl I hwf hn
  have h1 : ‖‖SumZeroDyn.lkT (sample d) Ev N u ω σ a‖ ^ q‖
      = ‖SumZeroDyn.lkT (sample d) Ev N u ω σ a‖ ^ q := by
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
  rw [h1]
  exact pow_le_pow_left₀ (norm_nonneg _) hb q

end RBM.Gauss

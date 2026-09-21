/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import RBM1D.Gauss.MomentDuhamelHyp

/-!
# The time-dependent admissibility, at the order it is really used (T191)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  This file is step 0 of T191 together with the two analytic steps of the
"drift-and-Hölder chain" that are independent of it.

## Step 0: `RBM.Gauss.TestFunT` asks for one order in time too many

`RBM.Gauss.TestFunT.contDiffAt` asks for `ContDiffAt ℝ 2` of `(u, M) ↦ Ψ u M` **jointly**.
Reading the proof of `RBM.Gauss.hasDerivAt_integral_Psi` line by line, the joint hypothesis is
used exactly twice:

* `RBM.Gauss.hasDerivAt_Psi_Hflow` needs `DifferentiableAt ℝ (uncurry Ψ) (x, H_x ω)` — joint
  *first* order;
* `RBM.Gauss.continuous_timeD1` needs `M ↦ timeD1 Ψ u M` to be continuous, which it derives
  from the joint `ContDiffAt` via `ContDiffAt.continuousAt_fderiv`, and which is used only to
  make `ω ↦ ∂_1 Ψ(u, H_u ω)` measurable and (with `bddT`) integrable.

Everything else — `TestFunT.slice`, `continuous_coordD1`, `continuous_coordD2`,
`hasDerivAt_coordD1_update`, `sum_used_eq_sum_pairs_coordD2` — is about the **matrix** slice
`Ψ u`, where `C²` is genuinely needed.

`RBM.Gauss.TestFunT₁` below is therefore the same class with the joint field weakened to those
two consequences, and `RBM.Gauss.hasDerivAt_integral_Psi₁` / `…_pairs₁` are the generator
identity for it, with the **conclusion unchanged**.  `RBM.Gauss.TestFunT.toTestFunT₁` shows the
old class sits inside the new one, so every existing supply survives;
`RBM.Gauss.TestFunT₁.of_contDiffAt_one` is the convenient sufficient condition (joint `C¹` plus
`C²` in the matrix).

**The consequence for T191.**  The admissibility of
`Ψ(u, M) = |(U_{u,v} ∘ (L - K)(u, M))_a|^{2p}` no longer needs a *second* `u`-derivative of
`RBM.edgeKer` or of `RBM.Band.Kval`; the repository's first-order facts
(`RBM.hasDerivAt_edgeKer`, `RBM.hasDerivAt_Kgen_all`) are of the right order, and what is
missing is joint regularity, not a second time derivative.  See `docs/STATUS.md` under T191.

`RBM.Gauss.hasDerivAt_integral_Psi_pairs_of_herm₁` is the Hermitian form (T187's
`_of_herm`, with `TestFunT₁` in place of `TestFunT`), and the weakening is **strict**:
`RBM.Gauss.testFunT₁_kinkT` together with `RBM.Gauss.not_testFunT_kinkT` exhibits a `Ψ` that
is in the relaxed class and not in the old one.

## The two analytic steps of the chain

Independently of the admissibility, the last two steps of the route
"generator identity → `hdu` of `RBM.MomentDuhamel.momentIneq_of_diffIneq`" are proved here,
because neither depends on which test-function class delivers the derivative:

* `RBM.MomentDuhamel.integral_pow_sub_one_mul_le`,
  `RBM.MomentDuhamel.integral_pow_sub_two_mul_le` — **Hölder**, in the interface's own
  `momNorm` vocabulary: `E[|Y|^{2p-1} |Z|] ≤ (E|Y|^{2p})^{(2p-1)/(2p)} ‖Z‖_{2p}` and
  `E[|Y|^{2p-2} Q] ≤ (E|Y|^{2p})^{(p-1)/p} ‖Q‖_p`.  These are the two exponent bookkeepings
  that fix `cMD p = 2p - 1`.
* `RBM.MomentDuhamel.rpow_inv_le_of_deriv_le`, `…_Icc`, `RBM.MomentDuhamel.diffIneq_of_deriv_le`
  — **the division by `p ψ^{p-1}`, done safely at `ψ = 0`**: from a pointwise bound on
  `φ' = ∂_u E|Y_u|^{2p}` on the *open* interval to the integrated inequality `hdu` for
  `ψ = φ^{1/p}` that `RBM.MomentDuhamel.momentIneq_of_diffIneq` consumes — the last item is
  stated verbatim in that shape, `RBM.MomentDuhamel.momNorm` and all.  `φ^{1/p}` is not
  differentiable where `φ` vanishes, so the proof runs on `φ + ε` and lets `ε ↓ 0`; the
  `ε`-limit is elementary (`Real.rpow_add_le_add_rpow`), no dominated convergence is needed.
  The derivative is assumed only on `Set.Ioo`, which is what
  `RBM.Gauss.hasDerivAt_integral_Psi`'s `0 < u` forces.

Each of the three carries its own sharpness check, because each is a piece of exponent
bookkeeping and a mis-copied exponent would otherwise pass unnoticed:
`RBM.MomentDuhamel.holder_first_sharp` / `holder_second_sharp` (Hölder is an equality at
`Z = Y`, resp. `Q = |Y|²` — the exponents recombine to `1`), and
`RBM.MomentDuhamel.deriv_le_hyp_sharp_one` / `rpow_inv_le_of_deriv_le_sharp_one` /
`deriv_le_conclusion_sharp_one` (at `p = 1`, `φ u = u`, `f ≡ 0`, `g ≡ 1` the hypothesis holds
with equality and the conclusion reads `v ≤ v`, so the constant `2p - 1` cannot be lowered).

## The assembly

`RBM.MomentDuhamel.momentIneq_of_derivBound` and `momentIneqQ_of_derivBound` put the three
together with T180's `RBM.MomentDuhamel.momentIneq_of_diffIneq` (and with
`momentIneqQ_of_diffIneq`, the `Q_t` wiring that T180's docstring announces but does not
state): **both fields of `RBM.MomentDuhamel.Hyp` are reduced to a pointwise bound on
`∂_u E|(U_{u,v} ∘ (L-K)_u)_a|^{2p}` on the open window**, plus integrability side conditions.
Nothing analytic is left between the generator identity and the two fields.

The constant is `RBM.MomentDuhamel.cMDval p = max 0 (2p - 1)`, which is `2p - 1` wherever the
inequalities speak (`cMDval_of_one_le`).  **The `max` is not cosmetic**: the field
`RBM.MomentDuhamel.Hyp.cMD_nonneg` quantifies over all `p : ℕ`, and the literal `2p - 1` is
negative at `p = 0`, where neither inequality is asserted.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ} {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-! ### The class with one order in time -/

/-- **`RBM.Gauss.TestFunT` with the joint `C²` weakened to what the generator identity uses.**

Compare `RBM.Gauss.TestFunT`: the single field `contDiffAt` (joint `ContDiffAt ℝ 2`) is
replaced by the three fields `contDiffM`, `diffJoint`, `contT`.  The matrix regularity is
unchanged (`C²`, and now stated as the slice being `C²` rather than as a consequence of the
joint statement); in the *time* slot only first-order information is asked for.

The four bounds are those of `RBM.Gauss.TestFunT`, verbatim. -/
structure TestFunT₁ (d : Dims) (N : ℕ) (T : Set ℝ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) : Prop where
  /-- Each time slice is `C²` in the matrix — the same requirement `RBM.Gauss.TestFunT.slice`
  extracts from the joint hypothesis. -/
  contDiffM : ∀ u ∈ T, ContDiff ℝ 2 (Ψ u)
  /-- `Ψ` is jointly *differentiable* — first order, not second. -/
  diffJoint : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
    DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M)
  /-- `∂_1 Ψ(u, ·)` is continuous in the matrix.  Only measurability and integrability of
  `ω ↦ ∂_1 Ψ(u, H_u ω)` are drawn from it. -/
  contT : ∀ u ∈ T, Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ => timeD1 Ψ u M
  /-- `Ψ` is bounded, uniformly over the window. -/
  bdd₀ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖Ψ u M‖ ≤ C
  /-- `∂_M Ψ` is bounded, uniformly over the window. -/
  bdd₁ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖fderiv ℝ (Ψ u) M‖ ≤ C
  /-- `∂²_M Ψ` is bounded, uniformly over the window. -/
  bdd₂ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖fderiv ℝ (fderiv ℝ (Ψ u)) M‖ ≤ C
  /-- `∂_1 Ψ` is bounded, uniformly over the window. -/
  bddT : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖timeD1 Ψ u M‖ ≤ C

namespace TestFunT₁

/-- Each slice is a `RBM.Gauss.TestFun`, exactly as for the unprimed class. -/
theorem slice (h : TestFunT₁ d N T Ψ) {u : ℝ} (hu : u ∈ T) : TestFun d N (Ψ u) where
  contDiff := h.contDiffM u hu
  bdd₀ := let ⟨C, hC⟩ := h.bdd₀; ⟨C, hC u hu⟩
  bdd₁ := let ⟨C, hC⟩ := h.bdd₁; ⟨C, hC u hu⟩
  bdd₂ := let ⟨C, hC⟩ := h.bdd₂; ⟨C, hC u hu⟩

end TestFunT₁

/-- **The old class is contained in the new one**, so no existing supply of
`RBM.Gauss.TestFunT` is lost and `RBM.Gauss.TestFunT₁` is not vacuous. -/
theorem TestFunT.toTestFunT₁ (h : TestFunT d N T Ψ) : TestFunT₁ d N T Ψ where
  contDiffM := fun u hu => (h.slice hu).contDiff
  diffJoint := fun u hu M => (h.contDiffAt u hu M).differentiableAt (by norm_num)
  contT := fun u hu => continuous_timeD1 h hu
  bdd₀ := h.bdd₀
  bdd₁ := h.bdd₁
  bdd₂ := h.bdd₂
  bddT := h.bddT

/-- **Joint `C¹` plus `C²` in the matrix suffices.**  This is the shape in which the
admissibility of the moment route's `Ψ` will be checked: one `u`-derivative of `RBM.edgeKer`,
of `RBM.Band.Kval` and of the loop along `u ↦ z_u`, and two matrix derivatives. -/
theorem TestFunT₁.of_contDiffAt_one
    (hM : ∀ u ∈ T, ContDiff ℝ 2 (Ψ u))
    (hjoint : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ContDiffAt ℝ 1 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M))
    (h₀ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖Ψ u M‖ ≤ C)
    (h₁ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖fderiv ℝ (Ψ u) M‖ ≤ C)
    (h₂ : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖fderiv ℝ (fderiv ℝ (Ψ u)) M‖ ≤ C)
    (hT : ∃ C : ℝ, ∀ u ∈ T, ∀ M, ‖timeD1 Ψ u M‖ ≤ C) :
    TestFunT₁ d N T Ψ where
  contDiffM := hM
  diffJoint := fun u hu M => (hjoint u hu M).differentiableAt (by norm_num)
  contT := by
    intro u hu
    rw [continuous_iff_continuousAt]
    intro M
    have hca : ContinuousAt
        (fderiv ℝ fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M) :=
      (hjoint u hu M).continuousAt_fderiv (by norm_num)
    have hp : ContinuousAt (fun M' : Matrix (d.Idx N) (d.Idx N) ℂ => (u, M')) M :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hmain : ContinuousAt (fun M' : Matrix (d.Idx N) (d.Idx N) ℂ =>
        fderiv ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => Ψ q.1 q.2) (u, M')
          ((1 : ℝ), (0 : Matrix (d.Idx N) (d.Idx N) ℂ))) M :=
      (hca.comp hp).clm_apply continuousAt_const
    refine hmain.congr (Eventually.of_forall fun M' => ?_)
    exact (timeD1_eq_fderiv_uncurry u M'
      ((hjoint u hu M').differentiableAt (by norm_num))).symm
  bdd₀ := h₀
  bdd₁ := h₁
  bdd₂ := h₂
  bddT := hT

/-! ### The generator identity for the relaxed class -/

/-- **`RBM.Gauss.hasDerivAt_integral_Psi` under `RBM.Gauss.TestFunT₁`.**

The statement is verbatim that of `RBM.Gauss.hasDerivAt_integral_Psi`; only the hypothesis is
weaker.  The proof is the same dominated-convergence argument — this is the *verification* of
step 0: had the joint `C²` been used anywhere else, this proof would not compile. -/
theorem hasDerivAt_integral_Psi₁ (hst : MatrixStein d) (h : TestFunT₁ d N T Ψ)
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
  have hu2 : (0 : ℝ) < u / 2 := by linarith
  have hS : T ∩ Set.Ioi (u / 2) ∈ nhds u := Filter.inter_mem hT (Ioi_mem_nhds (by linarith))
  have hcontF : ∀ x ∈ T, Continuous fun ω : Ω d => Ψ x (Hflow d N x ω) := fun x hx =>
    (h.slice hx).contDiff.continuous.comp (continuous_Hflow d N x)
  have hcontT : ∀ x ∈ T, Continuous fun ω : Ω d => timeD1 Ψ x (Hflow d N x ω) := fun x hx =>
    (h.contT x hx).comp (continuous_Hflow d N x)
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
    have := hasDerivAt_Psi_Hflow hx0 ω (h.diffJoint x hx.1 (Hflow d N x ω))
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
    refine le_trans (norm_add_le _ _) (add_le_add (hCT x hx.1 _) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hA : ‖∑ p ∈ usedCoord d N, ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p‖
        ≤ ∑ p ∈ usedCoord d N, |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD1_le (hC₁ x hx.1) _ p) (abs_nonneg _)
    have hB : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (u / 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hmono : Real.sqrt (u / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (le_of_lt hx.2)
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

/-- **The paper's `∑_{ij} S_ij` form, under `RBM.Gauss.TestFunT₁`.** -/
theorem hasDerivAt_integral_Psi_pairs₁ (hst : MatrixStein d) (h : TestFunT₁ d N T Ψ)
    {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d)) u := by
  rw [← sum_used_eq_sum_pairs_coordD2 (h.slice (mem_of_mem_nhds hT)) u]
  exact hasDerivAt_integral_Psi₁ hst h hu hT

/-- **The Hermitian form of the relaxed identity**, the shape the moment route consumes:
`Ψ u` is `C²` at each Hermitian matrix, and the *regularisation* `hermFunT Ψ` is in the
relaxed class.  Compare `RBM.Gauss.hasDerivAt_integral_Psi_pairs_of_herm` (T187), which is
this statement with `RBM.Gauss.TestFunT` in place of `RBM.Gauss.TestFunT₁`. -/
theorem hasDerivAt_integral_Psi_pairs_of_herm₁ (hst : MatrixStein d)
    (hreg : ∀ u ∈ T, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ContDiffAt ℝ 2 (Ψ u) M)
    (hbd : TestFunT₁ d N T (hermFunT d N Ψ)) {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d)) u := by
  have huT : u ∈ T := mem_of_mem_nhds hT
  have key := hasDerivAt_integral_Psi_pairs₁ hst hbd hu hT
  have htime : ∫ ω, timeD1 (hermFunT d N Ψ) u (Hflow d N u ω) ∂(P d)
      = ∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d) :=
    integral_congr_ae (Eventually.of_forall fun ω =>
      timeD1_hermFunT Ψ u (Hflow_isHermitian d N u ω))
  have hsum : ∀ i : d.Idx N, ∀ _ : i ∈ Finset.univ,
      (∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (hermFunT d N Ψ u) (Hflow d N u ω) i j ∂(P d))
        = ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
            ∫ ω, wirtSecond d N (Ψ u) (Hflow d N u ω) i j ∂(P d) := by
    intro i _
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => wirtSecond_hermFun
      (Hflow_isHermitian d N u ω) (hreg u huT _ (Hflow_isHermitian d N u ω)) i j)
  rw [funext_integral_hermFunT_Hflow Ψ, htime, Finset.sum_congr rfl hsum] at key
  exact key


/-! ### Step 0 is a *strict* weakening: a `C¹`-in-time witness -/

section Step0Witness

/-- `y ↦ y |y|` is differentiable everywhere, with derivative `2 |y|`.  Its derivative is
`2 |·|`, which is not differentiable at `0`; so this is a `C¹` function that is not `C²`. -/
theorem hasDerivAt_mul_abs (x : ℝ) : HasDerivAt (fun y : ℝ => y * |y|) (2 * |x|) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hev : (fun y : ℝ => y * |y|) =ᶠ[nhds x] fun y : ℝ => -(y * y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [abs_of_neg hy]; ring
    have h : HasDerivAt (fun y : ℝ => -(y * y)) (-(1 * x + x * 1)) x :=
      ((hasDerivAt_id x).mul (hasDerivAt_id x)).neg
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_neg hx]; ring
  · subst hx
    have hz : (2 : ℝ) * |(0 : ℝ)| = 0 := by simp
    rw [hz, hasDerivAt_iff_tendsto_slope]
    have heq : ∀ y : ℝ, y ≠ 0 → slope (fun y : ℝ => y * |y|) 0 y = |y| := by
      intro y hy
      rw [slope_def_field]
      field_simp
      ring
    have htend : Filter.Tendsto (fun y : ℝ => |y|)
        (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds (0 : ℝ)) := by
      have h0 := (continuous_abs.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using h0
    refine Filter.Tendsto.congr' ?_ htend
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (heq y hy).symm
  · have hev : (fun y : ℝ => y * |y|) =ᶠ[nhds x] fun y : ℝ => y * y := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [abs_of_pos hy]
    have h : HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
      (hasDerivAt_id x).mul (hasDerivAt_id x)
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_pos hx]; ring

/-- `s ↦ (s - ½)|s - ½|` and its derivative `2 |s - ½|`. -/
theorem hasDerivAt_kink (s : ℝ) :
    HasDerivAt (fun r : ℝ => (r - 1 / 2) * |r - 1 / 2|) (2 * |s - 1 / 2|) s := by
  have h₁ : HasDerivAt (fun r : ℝ => r - 1 / 2) 1 s := (hasDerivAt_id s).sub_const _
  have h2 := (hasDerivAt_mul_abs (s - 1 / 2)).comp s h₁
  simpa [Function.comp_def] using h2

/-- The kink `(u - ½)|u - ½|`, as a time-dependent test function with no matrix dependence.
`C¹` in time, `C^∞` in the matrix, and **not** `C²` in time at `u = ½`. -/
noncomputable def kinkT (d : Dims) (N : ℕ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  fun u _ => ((((u - 1 / 2) * |u - 1 / 2| : ℝ)) : ℂ)

theorem kinkT_slice (u : ℝ) :
    kinkT d N u = fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ((((u - 1 / 2) * |u - 1 / 2| : ℝ)) : ℂ) := rfl

theorem timeD1_kinkT (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    timeD1 (kinkT d N) u M = (((2 * |u - 1 / 2| : ℝ)) : ℂ) :=
  (hasDerivAt_kink u).ofReal_comp.deriv

/-- **The kink is in the relaxed class.** -/
theorem testFunT₁_kinkT (d : Dims) (N : ℕ) :
    TestFunT₁ d N (Set.Ioo (0 : ℝ) 1) (kinkT d N) where
  contDiffM := fun _ _ => contDiff_const
  diffJoint := by
    intro u _ M
    have hstep : DifferentiableAt ℝ
        (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => q.1 - 1 / 2) (u, M) :=
      differentiableAt_fst.sub_const _
    have hmulabs : DifferentiableAt ℝ (fun y : ℝ => y * |y|) (u - 1 / 2) :=
      (hasDerivAt_mul_abs (u - 1 / 2)).differentiableAt
    have h2 := hmulabs.comp (u, M) hstep
    have h3 := (Complex.ofRealCLM.differentiableAt
      (x := (u - 1 / 2) * |u - 1 / 2|)).comp (u, M) h2
    exact h3
  contT := by
    intro u _
    simp only [timeD1_kinkT]
    exact continuous_const
  bdd₀ := by
    refine ⟨1, fun u hu M => ?_⟩
    have h1 : |u - 1 / 2| ≤ 1 := by
      rcases hu with ⟨h0, h1⟩
      rw [abs_le]; constructor <;> linarith
    have h0 : (0 : ℝ) ≤ |u - 1 / 2| := abs_nonneg _
    have hn : ‖kinkT d N u M‖ = |u - 1 / 2| * |u - 1 / 2| := by
      simp only [kinkT, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_abs]
    rw [hn]
    nlinarith
  bdd₁ := by
    refine ⟨0, fun u _ M => ?_⟩
    rw [kinkT_slice, fderiv_fun_const, Pi.zero_apply]
    exact le_of_eq ContinuousLinearMap.opNorm_zero
  bdd₂ := by
    refine ⟨0, fun u _ M => ?_⟩
    rw [kinkT_slice, fderiv_fun_const,
      show (0 : Matrix (d.Idx N) (d.Idx N) ℂ → (Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ))
        = fun _ => 0 from rfl, fderiv_fun_const, Pi.zero_apply]
    exact le_of_eq ContinuousLinearMap.opNorm_zero
  bddT := by
    refine ⟨2, fun u hu M => ?_⟩
    rw [timeD1_kinkT]
    have h1 : |u - 1 / 2| ≤ 1 := by
      rcases hu with ⟨h0, h1⟩
      rw [abs_le]; constructor <;> linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

/-- **The kink is not in `RBM.Gauss.TestFunT`.**  So `RBM.Gauss.TestFunT₁` is a *strict*
weakening: the joint `C²` field really does ask for a second `u`-derivative that the generator
identity never uses. -/
theorem not_testFunT_kinkT (d : Dims) (N : ℕ) :
    ¬ TestFunT d N (Set.Ioo (0 : ℝ) 1) (kinkT d N) := by
  intro h
  have hmem : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have h2 := h.contDiffAt (1 / 2) hmem 0
  have hpair : ContDiffAt ℝ 2
      (fun s : ℝ => (s, (0 : Matrix (d.Idx N) (d.Idx N) ℂ))) (1 / 2 : ℝ) :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hsl : ContDiffAt ℝ 2
      (fun s : ℝ => ((((s - 1 / 2) * |s - 1 / 2| : ℝ)) : ℂ)) (1 / 2 : ℝ) :=
    h2.comp (1 / 2 : ℝ) hpair
  have hfun : (⇑Complex.reCLM ∘ fun s : ℝ => ((((s - 1 / 2) * |s - 1 / 2| : ℝ)) : ℂ))
      = fun s : ℝ => (s - 1 / 2) * |s - 1 / 2| := by
    funext s
    rw [Function.comp_apply, Complex.reCLM_apply, Complex.ofReal_re]
  have hre : ContDiffAt ℝ 2 (fun s : ℝ => (s - 1 / 2) * |s - 1 / 2|) (1 / 2 : ℝ) := by
    have hc := (Complex.reCLM.contDiff.contDiffAt
      (x := ((((1 / 2 - 1 / 2 : ℝ)) * |(1 / 2 - 1 / 2 : ℝ)| : ℝ) : ℂ))).comp (1 / 2 : ℝ) hsl
    rwa [hfun] at hc
  have hderiv : deriv (fun s : ℝ => (s - 1 / 2) * |s - 1 / 2|)
      = fun s : ℝ => 2 * |s - 1 / 2| := funext fun s => (hasDerivAt_kink s).deriv
  have hd : DifferentiableAt ℝ (fun s : ℝ => 2 * |s - 1 / 2|) (1 / 2 : ℝ) := by
    have hdd := (hre.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rwa [hderiv] at hdd
  have h3 : DifferentiableAt ℝ (fun s : ℝ => |s - 1 / 2|) (1 / 2 : ℝ) := by
    refine (hd.const_mul (2⁻¹ : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)
    ring
  have hshift : DifferentiableAt ℝ (fun t : ℝ => t + 1 / 2) 0 :=
    differentiableAt_id.add_const _
  have h4 : DifferentiableAt ℝ (fun s : ℝ => |s - 1 / 2|) ((fun t : ℝ => t + 1 / 2) 0) := by
    simpa using h3
  have hfun2 : ((fun s : ℝ => |s - 1 / 2|) ∘ fun t : ℝ => t + 1 / 2) = fun t : ℝ => |t| := by
    funext t
    rw [Function.comp_apply]
    congr 1
    ring
  have h5 : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    have h6 := h4.comp 0 hshift
    rwa [hfun2] at h6
  exact not_differentiableAt_abs_zero h5

end Step0Witness

end Gauss

namespace MomentDuhamel

open MeasureTheory Filter Real Set

/-- **From a derivative bound on `φ_u = E|Y_u|^{2p}` to the integrated inequality for
`ψ = φ^{1/p}`** — the division by `p ψ^{p-1}` of the moment route, carried out safely where
`ψ` vanishes.

`φ^{1/p}` need not be differentiable where `φ = 0`, so the proof runs on `φ + ε` (where the
`rpow` chain rule applies), integrates on the closed window with the derivative assumed only on
`Set.Ioo s v` — which is what the `0 < u` of `RBM.Gauss.hasDerivAt_integral_Psi` forces — and
lets `ε ↓ 0`.  The `ε`-limit costs nothing: the subadditivity `(a + b)^θ ≤ a^θ + b^θ` for
`θ ≤ 1` (`Real.rpow_add_le_add_rpow`) turns the error into `ε^{1/p} + 2 ε^{1/(2p)} ∫ f`, so no
dominated convergence is needed.

The two exponents on the right are the ones the generator identity produces, and the constant
in front of `∫ g` is `2p - 1` — i.e. `RBM.MomentDuhamel.Hyp.cMD p = 2p - 1`. -/
theorem rpow_inv_le_of_deriv_le {s v : ℝ} (hsv : s ≤ v) {p : ℕ} (hp : 1 ≤ p)
    {φ φ' f g : ℝ → ℝ}
    (hφ0 : ∀ u ∈ Set.Icc s v, 0 ≤ φ u)
    (hcont : ContinuousOn φ (Set.Icc s v))
    (hderiv : ∀ u ∈ Set.Ioo s v, HasDerivAt φ (φ' u) u)
    (hφ'int : IntervalIntegrable φ' volume s v)
    (hf0 : ∀ u ∈ Set.Icc s v, 0 ≤ f u) (hg0 : ∀ u ∈ Set.Icc s v, 0 ≤ g u)
    (hfint : IntervalIntegrable f volume s v) (hgint : IntervalIntegrable g volume s v)
    (hbound : ∀ u ∈ Set.Ioo s v, φ' u
      ≤ 2 * (p : ℝ) * φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * f u
        + (p : ℝ) * (2 * (p : ℝ) - 1) * φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * g u) :
    φ v ^ ((1 : ℝ) / (p : ℝ))
      ≤ φ s ^ ((1 : ℝ) / (p : ℝ))
        + 2 * (∫ r in s..v, φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
        + (2 * (p : ℝ) - 1) * ∫ r in s..v, g r := by
  have hq1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have h2q0 : (0 : ℝ) < 2 * (p : ℝ) := by linarith
  have hα0 : (0 : ℝ) ≤ (2 * (p : ℝ) - 1) / (2 * (p : ℝ)) := div_nonneg (by linarith) h2q0.le
  have hβ0 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) := div_nonneg (by linarith) hq0.le
  have he1 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have he1' : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact hq1
  have he1p : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have he2 : (0 : ℝ) ≤ 1 / (2 * (p : ℝ)) := by positivity
  have he2' : 1 / (2 * (p : ℝ)) ≤ 1 := by rw [div_le_one h2q0]; linarith
  have he2p : (0 : ℝ) < 1 / (2 * (p : ℝ)) := by positivity
  have huIcc : Set.uIcc s v = Set.Icc s v := Set.uIcc_of_le hsv
  have hIfint : IntervalIntegrable
      (fun r => φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r) volume s v := by
    have heq : (fun r => φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
        = fun r => f r * φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) := by funext r; ring
    rw [heq]
    refine hfint.mul_continuousOn ?_
    rw [huIcc]
    exact hcont.rpow_const fun x _ => Or.inr he2
  have hIf0 : (0 : ℝ) ≤ ∫ r in s..v, f r := intervalIntegral.integral_nonneg hsv hf0
  -- the `ε`-regularised inequality
  have key : ∀ ε : ℝ, 0 < ε →
      φ v ^ ((1 : ℝ) / (p : ℝ))
        ≤ (φ s ^ ((1 : ℝ) / (p : ℝ))
            + 2 * (∫ r in s..v, φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
            + (2 * (p : ℝ) - 1) * ∫ r in s..v, g r)
          + (ε ^ ((1 : ℝ) / (p : ℝ))
            + 2 * (ε ^ ((1 : ℝ) / (2 * (p : ℝ))) * ∫ r in s..v, f r)) := by
    intro ε hε
    have hB0 : ∀ u ∈ Set.Icc s v, 0 < φ u + ε := by
      intro u hu; have := hφ0 u hu; linarith
    have hBcont : ContinuousOn (fun u => φ u + ε) (Set.Icc s v) := hcont.add continuousOn_const
    have hψcont : ContinuousOn (fun u => (φ u + ε) ^ ((1 : ℝ) / (p : ℝ))) (Set.Icc s v) :=
      hBcont.rpow_const fun x _ => Or.inr he1
    have hψderiv : ∀ u ∈ Set.Ioo s v,
        HasDerivAt (fun r => (φ r + ε) ^ ((1 : ℝ) / (p : ℝ)))
          (φ' u * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))) u := by
      intro u hu
      have hu' : u ∈ Set.Icc s v := Set.Ioo_subset_Icc_self hu
      have h := HasDerivAt.rpow_const (p := ((1 : ℝ) / (p : ℝ)))
        ((hderiv u hu).add_const ε) (Or.inl (ne_of_gt (hB0 u hu')))
      exact h.congr_deriv (by ring)
    have hDint : IntervalIntegrable
        (fun u => φ' u * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))) volume s v := by
      refine hφ'int.mul_continuousOn ?_
      rw [huIcc]
      exact continuousOn_const.mul (hBcont.rpow_const fun x hx => Or.inl (ne_of_gt (hB0 x hx)))
    have hBefint : IntervalIntegrable
        (fun r => (φ r + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r) volume s v := by
      have heq : (fun r => (φ r + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
          = fun r => f r * (φ r + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by funext r; ring
      rw [heq]
      refine hfint.mul_continuousOn ?_
      rw [huIcc]
      exact hBcont.rpow_const fun x _ => Or.inr he2
    have hGint : IntervalIntegrable
        (fun u => 2 * ((φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f u)
          + (2 * (p : ℝ) - 1) * g u) volume s v :=
      (hBefint.const_mul 2).add (hgint.const_mul _)
    have hDle : ∀ u ∈ Set.Ioo s v,
        φ' u * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))
          ≤ 2 * ((φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f u)
            + (2 * (p : ℝ) - 1) * g u := by
      intro u hu
      have hu' : u ∈ Set.Icc s v := Set.Ioo_subset_Icc_self hu
      have hBu : 0 < φ u + ε := hB0 u hu'
      have hBp0 : (0 : ℝ) < (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) :=
        Real.rpow_pos_of_pos hBu _
      have hc0 : (0 : ℝ) ≤ (1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) := by positivity
      have hfu : 0 ≤ f u := hf0 u hu'
      have hgu : 0 ≤ g u := hg0 u hu'
      have h2q1 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
      have step1 := mul_le_mul_of_nonneg_right (hbound u hu) hc0
      refine step1.trans ?_
      have hαle : φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
          ≤ (φ u + ε) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) :=
        Real.rpow_le_rpow (hφ0 u hu') (by linarith) hα0
      have hβle : φ u ^ (((p : ℝ) - 1) / (p : ℝ))
          ≤ (φ u + ε) ^ (((p : ℝ) - 1) / (p : ℝ)) :=
        Real.rpow_le_rpow (hφ0 u hu') (by linarith) hβ0
      have hpow1 : (φ u + ε) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)
          = (φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
        rw [← Real.rpow_add hBu]
        congr 1
        field_simp
        ring
      have hpow2 : (φ u + ε) ^ (((p : ℝ) - 1) / (p : ℝ))
            * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) = 1 := by
        rw [← Real.rpow_add hBu]
        have hz : ((p : ℝ) - 1) / (p : ℝ) + ((1 : ℝ) / (p : ℝ) - 1) = 0 := by
          field_simp
          ring
        rw [hz, Real.rpow_zero]
      have hX : φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)
          ≤ (φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
        calc φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)
            ≤ (φ u + ε) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) :=
              mul_le_mul_of_nonneg_right hαle hBp0.le
          _ = (φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) := hpow1
      have hY : φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)
          ≤ 1 := by
        calc φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)
            ≤ (φ u + ε) ^ (((p : ℝ) - 1) / (p : ℝ))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) :=
              mul_le_mul_of_nonneg_right hβle hBp0.le
          _ = 1 := hpow2
      have e1 : (2 * (p : ℝ) * φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * f u)
            * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))
          = 2 * (φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) * f u) := by
        field_simp
      have e2 : ((p : ℝ) * (2 * (p : ℝ) - 1) * φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * g u)
            * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))
          = (2 * (p : ℝ) - 1) * (φ u ^ (((p : ℝ) - 1) / (p : ℝ))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) * g u) := by
        field_simp
      have e1le : 2 * (φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) * f u)
          ≤ 2 * ((φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f u) := by
        have := mul_le_mul_of_nonneg_right hX hfu
        linarith
      have e2le : (2 * (p : ℝ) - 1) * (φ u ^ (((p : ℝ) - 1) / (p : ℝ))
              * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) * g u)
          ≤ (2 * (p : ℝ) - 1) * g u := by
        have hmul := mul_le_mul_of_nonneg_right hY hgu
        rw [one_mul] at hmul
        exact mul_le_mul_of_nonneg_left hmul h2q1
      calc (2 * (p : ℝ) * φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * f u
              + (p : ℝ) * (2 * (p : ℝ) - 1) * φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * g u)
            * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))
          = (2 * (p : ℝ) * φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * f u)
              * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1))
            + ((p : ℝ) * (2 * (p : ℝ) - 1) * φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * g u)
              * ((1 / (p : ℝ)) * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)) := by ring
        _ = 2 * (φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
                * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) * f u)
              + (2 * (p : ℝ) - 1) * (φ u ^ (((p : ℝ) - 1) / (p : ℝ))
                * (φ u + ε) ^ ((1 : ℝ) / (p : ℝ) - 1) * g u) := by rw [e1, e2]
        _ ≤ 2 * ((φ u + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f u)
              + (2 * (p : ℝ) - 1) * g u := add_le_add e1le e2le
    have hftc : (∫ y in s..v, φ' y * ((1 / (p : ℝ)) * (φ y + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)))
        = (φ v + ε) ^ ((1 : ℝ) / (p : ℝ)) - (φ s + ε) ^ ((1 : ℝ) / (p : ℝ)) :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hsv hψcont
        (fun x hx => (hψderiv x hx).hasDerivWithinAt) hDint
    have hmono : (∫ y in s..v, φ' y * ((1 / (p : ℝ)) * (φ y + ε) ^ ((1 : ℝ) / (p : ℝ) - 1)))
        ≤ ∫ y in s..v, (2 * ((φ y + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y)
            + (2 * (p : ℝ) - 1) * g y) := by
      refine intervalIntegral.integral_mono_ae_restrict hsv hDint hGint ?_
      have hres : (volume.restrict (Set.Icc s v)) = volume.restrict (Set.Ioo s v) :=
        MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm
      rw [hres]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu using hDle u hu
    have hGsplit : (∫ y in s..v, (2 * ((φ y + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y)
            + (2 * (p : ℝ) - 1) * g y))
        = 2 * (∫ y in s..v, (φ y + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y)
          + (2 * (p : ℝ) - 1) * ∫ y in s..v, g y := by
      rw [intervalIntegral.integral_add (hBefint.const_mul 2) (hgint.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hRint : IntervalIntegrable
        (fun y => (φ y ^ ((1 : ℝ) / (2 * (p : ℝ))) + ε ^ ((1 : ℝ) / (2 * (p : ℝ)))) * f y)
        volume s v := by
      have heq : (fun y => (φ y ^ ((1 : ℝ) / (2 * (p : ℝ)))
            + ε ^ ((1 : ℝ) / (2 * (p : ℝ)))) * f y)
          = fun y => φ y ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y
            + ε ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y := by funext y; ring
      rw [heq]
      exact hIfint.add (hfint.const_mul _)
    have hint2 : (∫ y in s..v, (φ y + ε) ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y)
        ≤ ∫ y in s..v, (φ y ^ ((1 : ℝ) / (2 * (p : ℝ)))
            + ε ^ ((1 : ℝ) / (2 * (p : ℝ)))) * f y := by
      refine intervalIntegral.integral_mono_on hsv hBefint hRint fun u hu => ?_
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_add_le_add_rpow (hφ0 u hu) hε.le he2 he2') (hf0 u hu)
    have hsplit2 : (∫ y in s..v, (φ y ^ ((1 : ℝ) / (2 * (p : ℝ)))
            + ε ^ ((1 : ℝ) / (2 * (p : ℝ)))) * f y)
        = (∫ y in s..v, φ y ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y)
          + ε ^ ((1 : ℝ) / (2 * (p : ℝ))) * ∫ y in s..v, f y := by
      have heq : (fun y => (φ y ^ ((1 : ℝ) / (2 * (p : ℝ)))
            + ε ^ ((1 : ℝ) / (2 * (p : ℝ)))) * f y)
          = fun y => φ y ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y
            + ε ^ ((1 : ℝ) / (2 * (p : ℝ))) * f y := by funext y; ring
      rw [heq, intervalIntegral.integral_add hIfint (hfint.const_mul _),
        intervalIntegral.integral_const_mul]
    have hv : φ v ^ ((1 : ℝ) / (p : ℝ)) ≤ (φ v + ε) ^ ((1 : ℝ) / (p : ℝ)) :=
      Real.rpow_le_rpow (hφ0 v ⟨hsv, le_rfl⟩) (by linarith) he1
    have hs : (φ s + ε) ^ ((1 : ℝ) / (p : ℝ))
        ≤ φ s ^ ((1 : ℝ) / (p : ℝ)) + ε ^ ((1 : ℝ) / (p : ℝ)) :=
      Real.rpow_add_le_add_rpow (hφ0 s ⟨le_rfl, hsv⟩) hε.le he1 he1'
    rw [hGsplit] at hmono
    rw [hftc] at hmono
    rw [hsplit2] at hint2
    linarith
  -- let `ε ↓ 0`
  have hzr1 : (0 : ℝ) ^ ((1 : ℝ) / (p : ℝ)) = 0 := Real.zero_rpow (ne_of_gt he1p)
  have hzr2 : (0 : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) = 0 := Real.zero_rpow (ne_of_gt he2p)
  have h1 : Filter.Tendsto (fun ε : ℝ => ε ^ ((1 : ℝ) / (p : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ ((1 : ℝ) / (p : ℝ))) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr he1)
    have hcw := hc.continuousWithinAt (s := Set.Ioi (0 : ℝ))
    rw [ContinuousWithinAt, hzr1] at hcw
    exact hcw
  have h2 : Filter.Tendsto (fun ε : ℝ => ε ^ ((1 : ℝ) / (2 * (p : ℝ))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ ((1 : ℝ) / (2 * (p : ℝ)))) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr he2)
    have hcw := hc.continuousWithinAt (s := Set.Ioi (0 : ℝ))
    rw [ContinuousWithinAt, hzr2] at hcw
    exact hcw
  have hconst : Filter.Tendsto
      (fun _ : ℝ => φ s ^ ((1 : ℝ) / (p : ℝ))
          + 2 * (∫ r in s..v, φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
          + (2 * (p : ℝ) - 1) * ∫ r in s..v, g r)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (φ s ^ ((1 : ℝ) / (p : ℝ))
          + 2 * (∫ r in s..v, φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
          + (2 * (p : ℝ) - 1) * ∫ r in s..v, g r)) := tendsto_const_nhds
  have h3 : Filter.Tendsto
      (fun ε : ℝ => 2 * (ε ^ ((1 : ℝ) / (2 * (p : ℝ))) * ∫ r in s..v, f r))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (h2.mul_const (∫ r in s..v, f r)).const_mul (2 : ℝ)
    simpa using h
  have h4 : Filter.Tendsto
      (fun ε : ℝ => ε ^ ((1 : ℝ) / (p : ℝ))
        + 2 * (ε ^ ((1 : ℝ) / (2 * (p : ℝ))) * ∫ r in s..v, f r))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := h1.add h3
    simpa using h
  have hlim := hconst.add h4
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε


/-- **The same on every prefix of the window** — the shape of the hypothesis `hdu` of
`RBM.MomentDuhamel.momentIneq_of_diffIneq`, which is quantified over `u ∈ [s, v]`. -/
theorem rpow_inv_le_of_deriv_le_Icc {s v : ℝ} (hsv : s ≤ v) {p : ℕ} (hp : 1 ≤ p)
    {φ φ' f g : ℝ → ℝ}
    (hφ0 : ∀ u ∈ Set.Icc s v, 0 ≤ φ u)
    (hcont : ContinuousOn φ (Set.Icc s v))
    (hderiv : ∀ u ∈ Set.Ioo s v, HasDerivAt φ (φ' u) u)
    (hφ'int : IntervalIntegrable φ' volume s v)
    (hf0 : ∀ u ∈ Set.Icc s v, 0 ≤ f u) (hg0 : ∀ u ∈ Set.Icc s v, 0 ≤ g u)
    (hfint : IntervalIntegrable f volume s v) (hgint : IntervalIntegrable g volume s v)
    (hbound : ∀ u ∈ Set.Ioo s v, φ' u
      ≤ 2 * (p : ℝ) * φ u ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * f u
        + (p : ℝ) * (2 * (p : ℝ) - 1) * φ u ^ (((p : ℝ) - 1) / (p : ℝ)) * g u) :
    ∀ u ∈ Set.Icc s v,
      φ u ^ ((1 : ℝ) / (p : ℝ))
        ≤ φ s ^ ((1 : ℝ) / (p : ℝ))
          + 2 * (∫ r in s..u, φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * f r)
          + (2 * (p : ℝ) - 1) * ∫ r in s..u, g r := by
  rintro u ⟨hsu, huv⟩
  have hsub : Set.Icc s u ⊆ Set.Icc s v := Set.Icc_subset_Icc le_rfl huv
  have hsubo : Set.Ioo s u ⊆ Set.Ioo s v := Set.Ioo_subset_Ioo le_rfl huv
  have hsubI : Set.uIcc s u ⊆ Set.uIcc s v := by
    rw [Set.uIcc_of_le hsu, Set.uIcc_of_le hsv]
    exact hsub
  exact rpow_inv_le_of_deriv_le hsu hp (fun r hr => hφ0 r (hsub hr)) (hcont.mono hsub)
    (fun r hr => hderiv r (hsubo hr)) (hφ'int.mono_set hsubI)
    (fun r hr => hf0 r (hsub hr)) (fun r hr => hg0 r (hsub hr))
    (hfint.mono_set hsubI) (hgint.mono_set hsubI) (fun r hr => hbound r (hsubo hr))

/-- `‖Y‖_{2p}` is `(E|Y|^{2p})^{1/(2p)}` with the exponent written as a real. -/
theorem momNorm_eq_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℕ) (Y : Ω → ℝ) :
    momNorm P (2 * p) Y = (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
  unfold momNorm
  congr 1
  push_cast
  ring

/-- **The integrated differential inequality `hdu`, exactly in the shape
`RBM.MomentDuhamel.momentIneq_of_diffIneq` consumes**, from a pointwise bound on
`∂_u E|Y_u|^{2p}` on the open window.

Together with `RBM.MomentDuhamel.momentIneq_of_diffIneq` (T180) this closes the chain
"pointwise derivative bound ⟹ `RBM.MomentDuhamel.MomentIneq`", with
`cMD p = 2p - 1` — the constant that appears here in front of `∫ g`. -/
theorem diffIneq_of_deriv_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s v : ℝ} (hsv : s ≤ v) {p : ℕ} (hp : 1 ≤ p) {Y : ℝ → Ω → ℝ} {φ' f g : ℝ → ℝ}
    (hcont : ContinuousOn (fun u => ∫ ω, |Y u ω| ^ (2 * p) ∂P) (Set.Icc s v))
    (hderiv : ∀ u ∈ Set.Ioo s v,
      HasDerivAt (fun r => ∫ ω, |Y r ω| ^ (2 * p) ∂P) (φ' u) u)
    (hφ'int : IntervalIntegrable φ' volume s v)
    (hf0 : ∀ u ∈ Set.Icc s v, 0 ≤ f u) (hg0 : ∀ u ∈ Set.Icc s v, 0 ≤ g u)
    (hfint : IntervalIntegrable f volume s v) (hgint : IntervalIntegrable g volume s v)
    (hbound : ∀ u ∈ Set.Ioo s v, φ' u
      ≤ 2 * (p : ℝ) * (∫ ω, |Y u ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * f u
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, |Y u ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ)) * g u) :
    ∀ u ∈ Set.Icc s v,
      (∫ ω, |Y u ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (p : ℝ))
        ≤ (∫ ω, |Y s ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (p : ℝ))
          + 2 * (∫ r in s..u, momNorm P (2 * p) (Y r) * f r)
          + (2 * (p : ℝ) - 1) * ∫ r in s..u, g r := by
  have key := rpow_inv_le_of_deriv_le_Icc (φ := fun u => ∫ ω, |Y u ω| ^ (2 * p) ∂P)
    hsv hp (fun u _ => integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _)
    hcont hderiv hφ'int hf0 hg0 hfint hgint hbound
  simpa only [momNorm_eq_rpow] using key

/-! ### Satisfiability and sharpness of the descent lemma -/

/-- **The hypothesis of `rpow_inv_le_of_deriv_le` is satisfied with equality** at `p = 1`,
`φ u = u`, `f ≡ 0`, `g ≡ 1`. -/
theorem deriv_le_hyp_sharp_one (u : ℝ) :
    (1 : ℝ) = 2 * ((1 : ℕ) : ℝ) * u ^ ((2 * ((1 : ℕ) : ℝ) - 1) / (2 * ((1 : ℕ) : ℝ))) * 0
      + ((1 : ℕ) : ℝ) * (2 * ((1 : ℕ) : ℝ) - 1)
          * u ^ ((((1 : ℕ) : ℝ) - 1) / ((1 : ℕ) : ℝ)) * 1 := by
  norm_num

/-- **The descent lemma, instantiated at that data.**  Its conclusion is `v ≤ v`
(`deriv_le_conclusion_sharp_one`), so neither the constant `2p - 1` nor the exponents have any
slack: this is the compiled check that the exponent bookkeeping was not mis-copied. -/
theorem rpow_inv_le_of_deriv_le_sharp_one {v : ℝ} (hv : 0 ≤ v) :
    (fun u : ℝ => u) v ^ ((1 : ℝ) / (((1 : ℕ)) : ℝ))
      ≤ (fun u : ℝ => u) 0 ^ ((1 : ℝ) / (((1 : ℕ)) : ℝ))
        + 2 * (∫ r in (0 : ℝ)..v, (fun u : ℝ => u) r ^ ((1 : ℝ) / (2 * (((1 : ℕ)) : ℝ)))
            * (fun _ : ℝ => (0 : ℝ)) r)
        + (2 * (((1 : ℕ)) : ℝ) - 1) * ∫ r in (0 : ℝ)..v, (fun _ : ℝ => (1 : ℝ)) r :=
  rpow_inv_le_of_deriv_le hv le_rfl (fun _ hu => hu.1) continuousOn_id
    (fun u _ => hasDerivAt_id u) intervalIntegrable_const (fun _ _ => le_rfl)
    (fun _ _ => zero_le_one) intervalIntegrable_const intervalIntegrable_const
    (fun u _ => le_of_eq (deriv_le_hyp_sharp_one u))

/-- **The conclusion at that data is an equality**: the right-hand side of
`rpow_inv_le_of_deriv_le_sharp_one` is `v`. -/
theorem deriv_le_conclusion_sharp_one (v : ℝ) :
    (fun u : ℝ => u) 0 ^ ((1 : ℝ) / (((1 : ℕ)) : ℝ))
        + 2 * (∫ r in (0 : ℝ)..v, (fun u : ℝ => u) r ^ ((1 : ℝ) / (2 * (((1 : ℕ)) : ℝ)))
            * (fun _ : ℝ => (0 : ℝ)) r)
        + (2 * (((1 : ℕ)) : ℝ) - 1) * ∫ r in (0 : ℝ)..v, (fun _ : ℝ => (1 : ℝ)) r
      = (fun u : ℝ => u) v ^ ((1 : ℝ) / (((1 : ℕ)) : ℝ)) := by
  norm_num [Real.rpow_one]

/-! ### Hölder, in the interface's `momNorm` vocabulary -/

section Holder

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`MemLp` from the integrability of `|F|^r`**, for a real exponent `r > 0`.  This is the
`hfin` computation of `RBM.MomentDuhamel.momNorm_le_momNorm_of_exponent_le`, isolated: the only
bridge this file needs between the raw integrals of the interface and Mathlib's `L^p`
machinery. -/
theorem memLp_ofReal_of_integrable_rpow {P : Measure Ω} {r : ℝ} (hr : 0 < r)
    {F : Ω → ℝ} (hFm : AEStronglyMeasurable F P)
    (hF : Integrable (fun ω => |F ω| ^ r) P) :
    MemLp F (ENNReal.ofReal r) P := by
  rw [memLp_iff]
  have h0 : ENNReal.ofReal r ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hr
  have htop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_eLpNorm' h0 htop hFm, eLpNorm'_eq_lintegral_enorm,
    ENNReal.toReal_ofReal hr.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have hfi := hF.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfi
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hfi)
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr.le,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]

/-- **Hölder for the first-order term**:
`E[|Y|^{2p-1} |Z|] ≤ (E|Y|^{2p})^{(2p-1)/(2p)} ‖Z‖_{2p}`.

This is the exponent bookkeeping behind the `2 √ψ ‖U ∘ F‖_{2p}` of the moment route: dividing
by `p ψ^{p-1}` turns `2p (E|Y|^{2p})^{(2p-1)/(2p)}` into `2 ψ^{1/(2p)} = 2 √ψ`. -/
theorem integral_pow_sub_one_mul_le {P : Measure Ω} {p : ℕ} (hp : 1 ≤ p) {Y Z : Ω → ℝ}
    (hYm : AEStronglyMeasurable Y P) (hZm : AEStronglyMeasurable Z P)
    (hY : Integrable (fun ω => |Y ω| ^ (2 * p)) P)
    (hZ : Integrable (fun ω => |Z ω| ^ (2 * p)) P) :
    (∫ ω, |Y ω| ^ (2 * p - 1) * |Z ω| ∂P)
      ≤ (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
          * momNorm P (2 * p) Z := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h2p1 : (0 : ℝ) < 2 * (p : ℝ) - 1 := by linarith
  have hcast : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ 2 * p := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hconj : Real.HolderConjugate (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) (2 * (p : ℝ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ h2p1]; linarith
    · field_simp
      ring
  have hrewY : ∀ ω : Ω,
      (|Y ω| ^ (2 * p - 1)) ^ (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) = |Y ω| ^ (2 * p) := by
    intro ω
    rw [← Real.rpow_natCast (|Y ω|) (2 * p - 1), ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_natCast (|Y ω|) (2 * p)]
    congr 1
    rw [hcast]
    field_simp
    push_cast
    ring
  have hrewZ : ∀ ω : Ω, |Z ω| ^ (2 * (p : ℝ)) = |Z ω| ^ (2 * p) := by
    intro ω
    rw [← Real.rpow_natCast (|Z ω|) (2 * p)]
    congr 1
    push_cast
    ring
  have hFm : AEStronglyMeasurable (fun ω => |Y ω| ^ (2 * p - 1)) P :=
    (continuous_pow _).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable hYm)
  have hGm : AEStronglyMeasurable (fun ω => |Z ω|) P :=
    continuous_abs.comp_aestronglyMeasurable hZm
  have hFmem : MemLp (fun ω => |Y ω| ^ (2 * p - 1))
      (ENNReal.ofReal (2 * (p : ℝ) / (2 * (p : ℝ) - 1))) P := by
    refine memLp_ofReal_of_integrable_rpow (by positivity) hFm ?_
    have heq : (fun ω => |(|Y ω| ^ (2 * p - 1))| ^ (2 * (p : ℝ) / (2 * (p : ℝ) - 1)))
        = fun ω => |Y ω| ^ (2 * p) := by
      funext ω
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), hrewY ω]
    rw [heq]
    exact hY
  have hGmem : MemLp (fun ω => |Z ω|) (ENNReal.ofReal (2 * (p : ℝ))) P := by
    refine memLp_ofReal_of_integrable_rpow (by positivity) hGm ?_
    have heq : (fun ω => |(|Z ω|)| ^ (2 * (p : ℝ))) = fun ω => |Z ω| ^ (2 * p) := by
      funext ω
      rw [abs_abs, hrewZ ω]
    rw [heq]
    exact hZ
  have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg (Y ω)) _)
    (Filter.Eventually.of_forall fun ω => abs_nonneg (Z ω)) hFmem hGmem
  simp only [hrewY, hrewZ] at key
  refine key.trans (le_of_eq ?_)
  have he1 : (1 : ℝ) / (2 * (p : ℝ) / (2 * (p : ℝ) - 1))
      = (2 * (p : ℝ) - 1) / (2 * (p : ℝ)) := by
    field_simp
  have he2 : momNorm P (2 * p) Z = (∫ ω, |Z ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
    rw [momNorm]
    congr 1
    push_cast
    ring
  rw [he1, he2]


/-- **Hölder for the second-order term**:
`E[|Y|^{2p-2} Q] ≤ (E|Y|^{2p})^{(p-1)/p} ‖Q‖_p` for `Q ≥ 0`.

This is the exponent bookkeeping behind the `(2p-1) ‖(U ⊗ U) ∘ (E ⊗ E)‖_p` of the moment
route: dividing by `p ψ^{p-1}` turns `p(2p-1) (E|Y|^{2p})^{(p-1)/p}` into the constant
`2p - 1`, i.e. `RBM.MomentDuhamel.Hyp.cMD p`.  Note the `p`-th moment norm on the right, not
the `2p`-th: that is Hölder's conjugate index here, and it is what the interface's third term
carries.

At `p = 1` there is no conjugate exponent (`p/(p-1)` is undefined); the statement is then
`E[Q] ≤ E[Q]` and is proved directly. -/
theorem integral_pow_sub_two_mul_le {P : Measure Ω} {p : ℕ} (hp : 1 ≤ p) {Y Q : Ω → ℝ}
    (hYm : AEStronglyMeasurable Y P) (hQm : AEStronglyMeasurable Q P)
    (hQ0 : ∀ ω, 0 ≤ Q ω)
    (hY : Integrable (fun ω => |Y ω| ^ (2 * p)) P)
    (hQ : Integrable (fun ω => |Q ω| ^ p) P) :
    (∫ ω, |Y ω| ^ (2 * p - 2) * Q ω ∂P)
      ≤ (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ)) * momNorm P p Q := by
  rcases Nat.lt_or_ge p 2 with hlt | hge
  · have hp1 : p = 1 := by omega
    subst hp1
    have habs : (fun ω => |Q ω|) = Q := funext fun ω => abs_of_nonneg (hQ0 ω)
    simp only [Nat.cast_one, sub_self, Real.rpow_zero, one_mul, momNorm,
      pow_one, Nat.cast_one, div_one, Real.rpow_one, habs]
    simp
  · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hge
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hcast : ((2 * p - 2 : ℕ) : ℝ) = 2 * (p : ℝ) - 2 := by
      have h1 : (2 : ℕ) ≤ 2 * p := by omega
      rw [Nat.cast_sub h1]
      push_cast
      ring
    have hconj : Real.HolderConjugate ((p : ℝ) / ((p : ℝ) - 1)) (p : ℝ) := by
      rw [Real.holderConjugate_iff]
      refine ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hpm1]; linarith
      · field_simp
        ring
    have hrewY : ∀ ω : Ω,
        (|Y ω| ^ (2 * p - 2)) ^ ((p : ℝ) / ((p : ℝ) - 1)) = |Y ω| ^ (2 * p) := by
      intro ω
      rw [← Real.rpow_natCast (|Y ω|) (2 * p - 2), ← Real.rpow_mul (abs_nonneg _),
        ← Real.rpow_natCast (|Y ω|) (2 * p)]
      congr 1
      rw [hcast]
      field_simp
      push_cast
      ring
    have hrewQ : ∀ ω : Ω, Q ω ^ ((p : ℝ)) = |Q ω| ^ p := by
      intro ω
      rw [← Real.rpow_natCast (|Q ω|) p, abs_of_nonneg (hQ0 ω)]
    have hFm : AEStronglyMeasurable (fun ω => |Y ω| ^ (2 * p - 2)) P :=
      (continuous_pow _).comp_aestronglyMeasurable
        (continuous_abs.comp_aestronglyMeasurable hYm)
    have hFmem : MemLp (fun ω => |Y ω| ^ (2 * p - 2))
        (ENNReal.ofReal ((p : ℝ) / ((p : ℝ) - 1))) P := by
      refine memLp_ofReal_of_integrable_rpow (by positivity) hFm ?_
      have heq : (fun ω => |(|Y ω| ^ (2 * p - 2))| ^ ((p : ℝ) / ((p : ℝ) - 1)))
          = fun ω => |Y ω| ^ (2 * p) := by
        funext ω
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), hrewY ω]
      rw [heq]
      exact hY
    have hQmem : MemLp Q (ENNReal.ofReal ((p : ℝ))) P := by
      refine memLp_ofReal_of_integrable_rpow hp0 hQm ?_
      have heq : (fun ω => |Q ω| ^ ((p : ℝ))) = fun ω => |Q ω| ^ p := by
        funext ω
        rw [← hrewQ ω, abs_of_nonneg (hQ0 ω)]
      rw [heq]
      exact hQ
    have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hconj
      (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg (Y ω)) _)
      (Filter.Eventually.of_forall hQ0) hFmem hQmem
    simp only [hrewY, hrewQ] at key
    refine key.trans (le_of_eq ?_)
    have he1 : (1 : ℝ) / ((p : ℝ) / ((p : ℝ) - 1)) = ((p : ℝ) - 1) / (p : ℝ) := by
      field_simp
    have he2 : momNorm P p Q = (∫ ω, |Q ω| ^ p ∂P) ^ ((1 : ℝ) / (p : ℝ)) := rfl
    rw [he1, he2]


/-! ### Sharpness of the two Hölder steps -/

/-- **`integral_pow_sub_one_mul_le` is an equality at `Z = Y`.**  The two exponents
`(2p-1)/(2p)` and `1/(2p)` recombine to `1`, so nothing is lost: a mis-copied exponent would
break this identity. -/
theorem holder_first_sharp {P : Measure Ω} {p : ℕ} (hp : 1 ≤ p) (Y : Ω → ℝ) :
    (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
        * momNorm P (2 * p) Y
      = ∫ ω, |Y ω| ^ (2 * p) ∂P := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h0 : (0 : ℝ) ≤ ∫ ω, |Y ω| ^ (2 * p) ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have he2 : momNorm P (2 * p) Y = (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
    rw [momNorm]
    congr 1
    push_cast
    ring
  have hsum : (2 * (p : ℝ) - 1) / (2 * (p : ℝ)) + (1 : ℝ) / (2 * (p : ℝ)) = 1 := by
    field_simp
    ring
  rw [he2, ← Real.rpow_add' h0 (by rw [hsum]; norm_num), hsum, Real.rpow_one]

omit [MeasurableSpace Ω] in
/-- **The left-hand side of `integral_pow_sub_one_mul_le` at `Z = Y` is the same integral.** -/
theorem holder_first_lhs_self {p : ℕ} (hp : 1 ≤ p) (Y : Ω → ℝ) :
    (fun ω => |Y ω| ^ (2 * p - 1) * |Y ω|) = fun ω => |Y ω| ^ (2 * p) := by
  funext ω
  rw [← pow_succ]
  congr 1
  omega

/-- **`integral_pow_sub_two_mul_le` is an equality at `Q = |Y|²`**, for the same reason. -/
theorem holder_second_sharp {P : Measure Ω} {p : ℕ} (hp : 1 ≤ p) (Y : Ω → ℝ) :
    (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ))
        * momNorm P p (fun ω => |Y ω| ^ 2)
      = ∫ ω, |Y ω| ^ (2 * p) ∂P := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h0 : (0 : ℝ) ≤ ∫ ω, |Y ω| ^ (2 * p) ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have hfun : (fun ω => |(|Y ω| ^ 2)| ^ p) = fun ω => |Y ω| ^ (2 * p) := by
    funext ω
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 2), ← pow_mul]
  have he2 : momNorm P p (fun ω => |Y ω| ^ 2)
      = (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (p : ℝ)) := by
    rw [momNorm, hfun]
  have hsum : ((p : ℝ) - 1) / (p : ℝ) + (1 : ℝ) / (p : ℝ) = 1 := by
    field_simp
    ring
  rw [he2, ← Real.rpow_add' h0 (by rw [hsum]; norm_num), hsum, Real.rpow_one]

omit [MeasurableSpace Ω] in
/-- **The left-hand side of `integral_pow_sub_two_mul_le` at `Q = |Y|²` is the same
integral.** -/
theorem holder_second_lhs_self {p : ℕ} (hp : 1 ≤ p) (Y : Ω → ℝ) :
    (fun ω => |Y ω| ^ (2 * p - 2) * |Y ω| ^ 2) = fun ω => |Y ω| ^ (2 * p) := by
  funext ω
  rw [← pow_add]
  congr 1
  omega

end Holder

/-! ### The assembly: `MomentIneq` from a pointwise derivative bound -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The constant of the moment route, made total: `2p - 1` for `p ≥ 1`, and `0` at `p = 0`.

The field `RBM.MomentDuhamel.Hyp.cMD_nonneg` quantifies over **all** `p : ℕ`, while
`2p - 1` is negative at `p = 0`; the two moment inequalities are only ever asserted for
`1 ≤ p`, where `cMDval p = 2p - 1` (`cMDval_of_one_le`). -/
noncomputable def cMDval (p : ℕ) : ℝ := max 0 (2 * (p : ℝ) - 1)

theorem cMDval_nonneg (p : ℕ) : 0 ≤ cMDval p := le_max_left _ _

theorem cMDval_of_one_le {p : ℕ} (hp : 1 ≤ p) : cMDval p = 2 * (p : ℝ) - 1 := by
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact max_eq_right (by linarith)

/-- **`RBM.MomentDuhamel.MomentIneq` from a pointwise bound on
`∂_u E |(U_{u,v} ∘ (L - K)_u)_a|^{2p}`.**

This is T180's `RBM.MomentDuhamel.momentIneq_of_diffIneq` composed with
`RBM.MomentDuhamel.diffIneq_of_deriv_le`: **every analytic step between the generator identity
and the field `RBM.MomentDuhamel.Hyp.momentDuhamel` is discharged here**, and what remains in
the hypothesis `h` is, for each `(p, N, σ, v, a)`:

* a bound on `ψ` over the window (only to name its supremum — `exists_isLUB_Icc`);
* the `u`-derivative `φ'` of the `2p`-th moment on the **open** window `(s_N, v)`, which is
  where `RBM.Gauss.hasDerivAt_integral_Psi`'s `0 < u` lets it exist;
* four integrability side conditions;
* **the pointwise inequality** the generator identity followed by Hölder produces — the shape
  is exactly `RBM.MomentDuhamel.integral_pow_sub_one_mul_le` plus
  `integral_pow_sub_two_mul_le` applied to
  `∂_1 Ψ + 𝓛 Ψ`, with the drift substituted by `RBM.MomentDuhamel.Hyp.drift`.

The constant is pinned: `cMD = RBM.MomentDuhamel.cMDval`, which is `2p - 1` wherever the
inequalities speak. -/
theorem momentIneq_of_derivBound {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| ≤ 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
      ∀ a : LoopArg (B.L N) (n + 2), ∃ φ' : ℝ → ℝ, ∃ C : ℝ,
        (∀ u ∈ Set.Icc (s N) v,
            (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P) ^ ((1 : ℝ) / p) ≤ C)
        ∧ ContinuousOn (fun u => ∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
              ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P)
            (Set.Icc (s N) v)
        ∧ (∀ u ∈ Set.Ioo (s N) v, HasDerivAt
              (fun r => ∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N r ω σ) a‖| ^ (2 * p) ∂B.P) (φ' u) u)
        ∧ IntervalIntegrable φ' volume (s N) v
        ∧ IntervalIntegrable (fun u => momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (DriftDef.driftF B E N u (X.H N u ω) σ) a‖)) volume (s N) v
        ∧ IntervalIntegrable (fun u => momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖)) volume (s N) v
        ∧ (∀ u ∈ Set.Icc (s N) v, IntervalIntegrable (fun r =>
              momNorm B.P (2 * p) (fun ω =>
                ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N r ω σ) a‖)
              * momNorm B.P (2 * p) (fun ω =>
                ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (DriftDef.driftF B E N r (X.H N r ω) σ) a‖)) volume (s N) u)
        ∧ (∀ u ∈ Set.Ioo (s N) v, φ' u
            ≤ 2 * (p : ℝ)
                * (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P)
                  ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
                * momNorm B.P (2 * p) (fun ω =>
                    ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (DriftDef.driftF B E N u (X.H N u ω) σ) a‖)
              + (p : ℝ) * (2 * (p : ℝ) - 1)
                * (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P)
                  ^ (((p : ℝ) - 1) / (p : ℝ))
                * momNorm B.P p (fun ω =>
                    ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖))) :
    MomentIneq X E s t n cMDval := by
  refine momentIneq_of_diffIneq hE hs0 ht1 cMDval_nonneg ?_
  intro p hp N σ v hsv hvt a
  obtain ⟨φ', C, hCb, hcont, hderiv, hφ'int, hfint, hgint, hintψf, hbound⟩ :=
    h p hp N σ v hsv hvt a
  obtain ⟨M, hM⟩ := exists_isLUB_Icc (ψ := fun u =>
    (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P) ^ ((1 : ℝ) / p)) hsv hCb
  refine ⟨fun u => (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) ∂B.P) ^ ((1 : ℝ) / p),
    fun u => momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (DriftDef.driftF B E N u (X.H N u ω) σ) a‖),
    fun u => momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖),
    M, fun _ => rfl, fun _ => rfl, fun _ => rfl, hM, hintψf, hfint, hgint, ?_⟩
  rw [cMDval_of_one_le hp]
  exact diffIneq_of_deriv_le (Y := fun u ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.lkT X E N u ω σ) a‖)
    hsv hp hcont hderiv hφ'int
    (fun _ _ => momNorm_nonneg _ _ _) (fun _ _ => momNorm_nonneg _ _ _)
    hfint hgint hbound


/-- **`RBM.MomentDuhamel.MomentIneqQ` from the integrated differential inequality.**

The `Q_t` analogue of T180's `RBM.MomentDuhamel.momentIneq_of_diffIneq`, which that file's
docstring announces ("the same three lines over `momentDuhamelQ_body_of_integral_le`, with the
one drift integrand replaced by the three of (5.91)") but does not state.  The `ψ` here is the
`2p`-th moment of the `Q_t`-projected tensor, and the single drift integrand of (5.20) is
replaced by the sum `f₁ + f₂ + f₃` of (5.91). -/
theorem momentIneqQ_of_diffIneq {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} {cMD : ℕ → ℝ}
    (hE : |E| ≤ 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hc : ∀ p, 0 ≤ cMD p)
    (h : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
      ∀ a : LoopArg (B.L N) (n + 2), ∃ ψ f₁ f₂ f₃ g : ℝ → ℝ, ∃ M : ℝ,
        (∀ u, ψ u = (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖| ^ (2 * p) ∂B.P)
                ^ ((1 : ℝ) / p))
        ∧ (∀ u, f₁ u = momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖))
        ∧ (∀ u, f₂ u = momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N u ω σ)) a‖))
        ∧ (∀ u, f₃ u = momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
        ∧ (∀ u, g u = momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
                (Fin.append a a)‖))
        ∧ IsLUB (ψ '' Set.Icc (s N) v) M
        ∧ (∀ u ∈ Set.Icc (s N) v, IntervalIntegrable (fun r =>
              momNorm B.P (2 * p) (fun ω =>
                ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (Qop (B.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT X E N r ω σ)) a‖)
              * (f₁ r + f₂ r + f₃ r)) volume (s N) u)
        ∧ IntervalIntegrable f₁ volume (s N) v
        ∧ IntervalIntegrable f₂ volume (s N) v
        ∧ IntervalIntegrable f₃ volume (s N) v
        ∧ IntervalIntegrable g volume (s N) v
        ∧ (∀ u ∈ Set.Icc (s N) v, ψ u ≤ ψ (s N)
              + 2 * (∫ r in (s N)..u, momNorm B.P (2 * p) (fun ω =>
                  ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (Qop (B.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT X E N r ω σ)) a‖)
                * (f₁ r + f₂ r + f₃ r))
              + cMD p * ∫ r in (s N)..u, g r)) :
    MomentIneqQ X E s t n cMD := by
  intro p hp N σ v hsv hvt a
  obtain ⟨ψ, f₁, f₂, f₃, g, M, hψ, hf₁, hf₂, hf₃, hg, hM, hintψf, hint₁, hint₂, hint₃,
    hintg, hdu⟩ := h p hp N σ v hsv hvt a
  exact momentDuhamelQ_body_of_integral_le (X := X) (E := E)
    (F := fun N u M σ a => DriftDef.driftF B E N u M σ a)
    hE σ a hsv (le_trans (hs0 N) hsv) (lt_of_le_of_lt hvt (ht1 N)) (hc p)
    hψ hf₁ hf₂ hf₃ hg hM hintψf hint₁ hint₂ hint₃ hintg hdu


/-- **`RBM.MomentDuhamel.MomentIneqQ` from a pointwise bound on
`∂_u E |(U_{u,v} ∘ Q_u (L - K)_u)_a|^{2p}`** — the `Q_t` twin of
`RBM.MomentDuhamel.momentIneq_of_derivBound`, with the same constant `cMDval` and the single
drift integrand replaced by the sum of the three of (5.91). -/
theorem momentIneqQ_of_derivBound {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| ≤ 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
      ∀ a : LoopArg (B.L N) (n + 2), ∃ φ' : ℝ → ℝ, ∃ C : ℝ,
        (∀ u ∈ Set.Icc (s N) v,
            (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖| ^ (2 * p) ∂B.P)
              ^ ((1 : ℝ) / p) ≤ C)
        ∧ ContinuousOn (fun u => ∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
              ((v : ℝ) : ℂ) (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖|
                ^ (2 * p) ∂B.P) (Set.Icc (s N) v)
        ∧ (∀ u ∈ Set.Ioo (s N) v, HasDerivAt
              (fun r => ∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT X E N r ω σ)) a‖| ^ (2 * p) ∂B.P)
              (φ' u) u)
        ∧ IntervalIntegrable φ' volume (s N) v
        ∧ IntervalIntegrable (fun u => momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖))
            volume (s N) v
        ∧ IntervalIntegrable (fun u => momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N u ω σ)) a‖)) volume (s N) v
        ∧ IntervalIntegrable (fun u => momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a‖)) volume (s N) v
        ∧ IntervalIntegrable (fun u => momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
                (Fin.append a a)‖)) volume (s N) v
        ∧ (∀ u ∈ Set.Icc (s N) v, IntervalIntegrable (fun r =>
              momNorm B.P (2 * p) (fun ω =>
                ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (Qop (B.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT X E N r ω σ)) a‖)
              * (momNorm B.P (2 * p) (fun ω =>
                  ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (Qop (B.L N) ((r : ℝ) : ℂ) (DriftDef.driftF B E N r (X.H N r ω) σ)) a‖)
                + momNorm B.P (2 * p) (fun ω =>
                    ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ)
                        (SumZeroDyn.lkT X E N r ω σ)) a‖)
                + momNorm B.P (2 * p) (fun ω =>
                    ‖Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N r ω σ) (b 0)
                        * SumZeroDyn.varthetaDot (B.L N) r b) a‖))) volume (s N) u)
        ∧ (∀ u ∈ Set.Ioo (s N) v, φ' u
            ≤ 2 * (p : ℝ)
                * (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖|
                      ^ (2 * p) ∂B.P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
                * (momNorm B.P (2 * p) (fun ω =>
                    ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖)
                  + momNorm B.P (2 * p) (fun ω =>
                      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                          (SumZeroDyn.lkT X E N u ω σ)) a‖)
                  + momNorm B.P (2 * p) (fun ω =>
                      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                        (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                          * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
              + (p : ℝ) * (2 * (p : ℝ) - 1)
                * (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖|
                      ^ (2 * p) ∂B.P) ^ (((p : ℝ) - 1) / (p : ℝ))
                * momNorm B.P p (fun ω =>
                    ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
                      (Fin.append a a)‖))) :
    MomentIneqQ X E s t n cMDval := by
  refine momentIneqQ_of_diffIneq hE hs0 ht1 cMDval_nonneg ?_
  intro p hp N σ v hsv hvt a
  obtain ⟨φ', C, hCb, hcont, hderiv, hφ'int, hint₁, hint₂, hint₃, hgint, hintψf, hbound⟩ :=
    h p hp N σ v hsv hvt a
  obtain ⟨M, hM⟩ := exists_isLUB_Icc (ψ := fun u =>
    (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖| ^ (2 * p) ∂B.P)
        ^ ((1 : ℝ) / p)) hsv hCb
  refine ⟨fun u => (∫ ω, |‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖| ^ (2 * p) ∂B.P)
          ^ ((1 : ℝ) / p),
    fun u => momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖),
    fun u => momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω σ)) a‖),
    fun u => momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) u b) a‖),
    fun u => momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
        (Fin.append a a)‖),
    M, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, hM, hintψf,
    hint₁, hint₂, hint₃, hgint, ?_⟩
  rw [cMDval_of_one_le hp]
  exact diffIneq_of_deriv_le (Y := fun u ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖)
    hsv hp hcont hderiv hφ'int
    (fun _ _ => add_nonneg (add_nonneg (momNorm_nonneg _ _ _) (momNorm_nonneg _ _ _))
      (momNorm_nonneg _ _ _)) (fun _ _ => momNorm_nonneg _ _ _)
    ((hint₁.add hint₂).add hint₃) hgint hbound

end Assembly

end MomentDuhamel

end RBM

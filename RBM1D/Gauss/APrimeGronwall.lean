/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelTime

/-!
# Route (A′): the weighted generator identity (★) and the weighted Minkowski closure (G)

This file supplies the two analytic bricks (S1) and (S4) of the repaired route (A′)
(referee report V548, §6).

## (S1) The generator identity with a fixed `ω`-weight

`RBM.Gauss.hasDerivAt_integral_Psi₁` differentiates `s ↦ E[Ψ_s(H_s)]`.  Route (A′) needs the
same identity for `s ↦ E[w · Ψ_s(H_s)]` with a **fixed** (time-independent) weight `w` on the
sample space.  Putting `w` inside `Ψ` is not an option — see the referee's Appendix D: the
joint object `w(M/√u)·F_u(M)` has no `bddT` bound, and even if it had, a second application of
Stein's identity would be needed to recombine the terms.  So the identity is proved directly:

* `RBM.Gauss.WeightC1` — the regularity the weight actually needs.  **First order only**, and
  only along the coordinates of `RBM.Gauss.usedCoord`: continuity, finite dependence, a
  one-sided coordinate derivative `wD`, and global bounds on `w` and `wD`.  No second
  derivative of `w` appears anywhere, which is why the card-free bound on `∇²χ` is not on the
  critical path.
* `RBM.Gauss.hasDerivAt_integral_weighted` — **(★)**:
  `∂_s E[w·Ψ_s(H_s)]|_{s=u} = E[w·∂_1Ψ] + ½∑_q S_q E[w·∂_q²Ψ] + (2√u)⁻¹ ∑_q S_q E[(∂_q w)·∂_qΨ]`.
  The last sum is the cross term `C_u` of the referee's (★); it is the *only* place the weight
  is differentiated.

## (S4) The weighted Minkowski closure

`RBM.MomentDuhamel.rpow_inv_le_of_deriv_le_Icc` (T191) is already abstract in `φ`, so the
weighted moment `φ u = E[W·|Y_u|^{2p}]` feeds it unchanged.  What is added here:

* `RBM.MomentDuhamel.momNormW` — the weighted moment norm `(E[W|Y|^{2p}])^{1/(2p)}`.
* `RBM.MomentDuhamel.weightedMinkowski_of_deriv_le` — **(G)**:
  `‖Y_v‖_{W,2p} ≤ ‖Y_s‖_{W,2p} + 2∫_s^v (A + B) + √((2p-1)∫_s^v g)`
  from the differential inequality
  `φ' ≤ 2p·φ^{1-1/(2p)}·(A+B) + p(2p-1)·φ^{1-1/p}·g` on the **open** window.
  `A` is the weighted drift norm and `B = ‖D̃_u‖_{2p}` the cross term of (★).
  The Grönwall factor is `1`: this is a Minkowski-type closure, not an exponential one.

The left endpoint may be `0` (the hypothesis is only asked for on `Set.Ioo s v`), which is what
route (A′)'s first cell needs.
-/

namespace RBM

open MeasureTheory Filter Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal

variable {d : Dims} {N : ℕ} {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
  {w : Ω d → ℝ} {wD : (d.Idx N × d.Idx N × Bool) → Ω d → ℝ}

/-! ### 1. The regularity of the weight

Only what the proof of `RBM.Gauss.hasDerivAt_integral_weighted` consumes is asked for.  In
particular the weight is differentiated **once**, along one Gaussian coordinate at a time. -/

/-- **`w` is `C¹` along the used Gaussian coordinates, with `w` and `∂_q w` bounded.**

`cont`/`contD` and `finDep`/`finDepD` are the measurability and finite-dependence hypotheses of
`RBM.Gauss.MatrixStein.stein`; `hasDeriv` is the coordinate derivative; `bdd`/`bddD` are the
two uniform bounds.  There is deliberately **no** field for a second derivative of `w`. -/
structure WeightC1 (d : Dims) (N : ℕ) (w : Ω d → ℝ)
    (wD : (d.Idx N × d.Idx N × Bool) → Ω d → ℝ) : Prop where
  /-- The weight is continuous. -/
  cont : Continuous w
  /-- Each coordinate derivative is continuous. -/
  contD : ∀ p ∈ usedCoord d N, Continuous (wD p)
  /-- The weight reads finitely many coordinates. -/
  finDep : FinDep d w
  /-- Each coordinate derivative reads finitely many coordinates. -/
  finDepD : ∀ p ∈ usedCoord d N, FinDep d (wD p)
  /-- `wD p` **is** the derivative of `w` along the coordinate `crd p`. -/
  hasDeriv : ∀ p ∈ usedCoord d N, ∀ ω : Ω d,
    HasDerivAt (fun t : ℝ => w (Function.update ω (crd d N p) t)) (wD p ω) (ω (crd d N p))
  /-- `w` is bounded. -/
  bdd : ∃ C : ℝ, ∀ ω, |w ω| ≤ C
  /-- `∂_q w` is bounded, uniformly in the coordinate. -/
  bddD : ∃ C : ℝ, ∀ p ∈ usedCoord d N, ∀ ω, |wD p ω| ≤ C

/-! ### 2. Finite dependence is closed under the two operations the proof uses -/

/-- A real multiple of a finitely-dependent function is finitely dependent. -/
theorem finDep_smul_real {V : Type*} [SMul ℝ V] {f : Ω d → ℝ} {g : Ω d → V}
    (hf : FinDep d f) (hg : FinDep d g) : FinDep d fun ω => f ω • g ω := by
  classical
  obtain ⟨I, hI⟩ := hf
  obtain ⟨J, hJ⟩ := hg
  refine ⟨I ∪ J, fun ω ω' hagree => ?_⟩
  change f ω • g ω = f ω' • g ω'
  rw [hI ω ω' fun e he => hagree e (Finset.mem_union_left _ he),
    hJ ω ω' fun e he => hagree e (Finset.mem_union_right _ he)]

/-- A sum of finitely-dependent functions is finitely dependent. -/
theorem finDep_add' {V : Type*} [Add V] {f g : Ω d → V}
    (hf : FinDep d f) (hg : FinDep d g) : FinDep d fun ω => f ω + g ω := by
  classical
  obtain ⟨I, hI⟩ := hf
  obtain ⟨J, hJ⟩ := hg
  refine ⟨I ∪ J, fun ω ω' hagree => ?_⟩
  change f ω + g ω = f ω' + g ω'
  rw [hI ω ω' fun e he => hagree e (Finset.mem_union_left _ he),
    hJ ω ω' fun e he => hagree e (Finset.mem_union_right _ he)]

/-! ### 3. (S1): the generator identity with a fixed `ω`-weight -/

/-- **⭐⭐ (★), the weighted generator identity.**

`∂_s E[w·Ψ_s(H_s)]` at `s = u > 0` equals

`E[w·∂_1Ψ_u] + ½ ∑_q S_q E[w·∂_q²Ψ_u] + (2√u)⁻¹ ∑_q S_q E[(∂_q w)·∂_qΨ_u]`.

The first two terms are `RBM.Gauss.hasDerivAt_integral_Psi₁` with `w` carried along; the third
is the **cross term** `C_u`, produced by the single application of Stein's identity to
`ω_q ↦ w·∂_qΨ` — the weight is differentiated exactly once, and never twice. -/
theorem hasDerivAt_integral_weighted (hst : MatrixStein d) (h : TestFunT₁ d N T Ψ)
    (hw : WeightC1 d N w wD) {u : ℝ} (hu : 0 < u) (hT : T ∈ nhds u) :
    HasDerivAt (fun s : ℝ => ∫ ω, w ω • Ψ s (Hflow d N s ω) ∂(P d))
      ((∫ ω, w ω • timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + ((1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
              ∫ ω, w ω • coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)
            + (1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
              ∫ ω, wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p ∂(P d))) u := by
  classical
  have huT : u ∈ T := mem_of_mem_nhds hT
  obtain ⟨C₀, hC₀⟩ := h.bdd₀
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  obtain ⟨CT, hCT⟩ := h.bddT
  obtain ⟨Cw, hCw⟩ := hw.bdd
  obtain ⟨CwD, hCwD⟩ := hw.bddD
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans (abs_nonneg _) (hCw 0)
  have hu2 : (0 : ℝ) < u / 2 := by linarith
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
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
  -- the `s`-derivative of the weighted integrand, pointwise in `ω`
  have hdiff : ∀ᵐ ω ∂(P d), ∀ x ∈ T ∩ Set.Ioi (u / 2),
      HasDerivAt (fun s : ℝ => w ω • Ψ s (Hflow d N s ω))
        (w ω • (timeD1 Ψ x (Hflow d N x ω) + (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p)) x := by
    refine Eventually.of_forall fun ω x hx => ?_
    have hx0 : 0 < x := lt_trans hu2 hx.2
    have hd := hasDerivAt_Psi_Hflow hx0 ω (h.diffJoint x hx.1 (Hflow d N x ω))
    rw [fderiv_apply_Xmat] at hd
    exact hd.const_smul (w ω)
  have hbound : ∀ᵐ ω ∂(P d), ∀ x ∈ T ∩ Set.Ioi (u / 2),
      ‖w ω • (timeD1 Ψ x (Hflow d N x ω) + (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p)‖
        ≤ Cw * (CT + (1 / (2 * Real.sqrt (u / 2))) * ∑ p ∈ usedCoord d N,
            |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)) := by
    refine Eventually.of_forall fun ω x hx => ?_
    have hx0 : 0 < x := lt_trans hu2 hx.2
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hs2 : 0 < Real.sqrt (u / 2) := Real.sqrt_pos.2 hu2
    have hinner : ‖timeD1 Ψ x (Hflow d N x ω) + (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ x) (Hflow d N x ω) p‖
        ≤ CT + (1 / (2 * Real.sqrt (u / 2))) * ∑ p ∈ usedCoord d N,
            |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
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
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hCw ω) hinner (norm_nonneg _) hCw0
  have hbndint : Integrable (fun ω : Ω d => Cw * (CT + (1 / (2 * Real.sqrt (u / 2))) *
      ∑ p ∈ usedCoord d N, |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖))) (P d) :=
    Integrable.const_mul ((integrable_const CT).add (Integrable.const_mul
      (integrable_finsetSum _ fun p _ =>
        ((integrable_coord d (crd d N p)).abs).mul_const _) _)) _
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P d) (𝕜 := ℝ)
    (F := fun (s : ℝ) (ω : Ω d) => w ω • Ψ s (Hflow d N s ω))
    (F' := fun (s : ℝ) (ω : Ω d) => w ω • (timeD1 Ψ s (Hflow d N s ω)
      + (1 / (2 * Real.sqrt s)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ s) (Hflow d N s ω) p))
    (x₀ := u) (s := T ∩ Set.Ioi (u / 2)) hS
    (Filter.eventually_of_mem hS fun x hx => (hw.cont.smul (hcontF x hx.1)).aestronglyMeasurable)
    (integrable_of_continuous_of_bound (hw.cont.smul (hcontF u huT)) fun ω => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hCw ω) (hC₀ u huT _) (norm_nonneg _) hCw0)
    ((hw.cont.smul ((hcontT u huT).add (hcontS u huT))).aestronglyMeasurable)
    hbound hbndint hdiff
  -- rewrite the value of the derivative
  have hcd1 : ∀ p ∈ usedCoord d N,
      Continuous fun ω : Ω d => w ω • coordD1 d N (Ψ u) (Hflow d N u ω) p :=
    fun p _ => hw.cont.smul (continuous_coordD1 (h.slice huT) u p)
  have hbd1 : ∀ p : d.Idx N × d.Idx N × Bool, ∀ ω : Ω d,
      ‖w ω • coordD1 d N (Ψ u) (Hflow d N u ω) p‖
        ≤ Cw * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
    intro p ω
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hCw ω) (norm_coordD1_le (hC₁ u huT) _ p) (norm_nonneg _) hCw0
  have hint : ∀ p ∈ usedCoord d N,
      Integrable (fun ω : Ω d => ω (crd d N p) • (w ω • coordD1 d N (Ψ u) (Hflow d N u ω) p))
        (P d) := fun p hp =>
    (integrable_coord d (crd d N p)).smul_bdd (Cw * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖))
      (hcd1 p hp).aestronglyMeasurable (Eventually.of_forall fun ω => hbd1 p ω)
  have hintD : ∀ p ∈ usedCoord d N,
      Integrable (fun ω : Ω d => wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p) (P d) := by
    intro p hp
    refine integrable_of_continuous_of_bound
      ((hw.contD p hp).smul (continuous_coordD1 (h.slice huT) u p))
      (C := CwD * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)) fun ω => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hCwD p hp ω) (norm_coordD1_le (hC₁ u huT) _ p) (norm_nonneg _)
      (le_trans (abs_nonneg _) (hCwD p hp 0))
  have hintQ : ∀ p ∈ usedCoord d N,
      Integrable (fun ω : Ω d =>
        w ω • (Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p)) (P d) := by
    intro p _
    refine integrable_of_continuous_of_bound
      (hw.cont.smul ((continuous_coordD2 (h.slice huT) u p).const_smul (Real.sqrt u)))
      (C := Cw * (|Real.sqrt u| *
        (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖))) fun ω => ?_
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul (hCw ω) ?_ (norm_nonneg _) hCw0
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_coordD2_le (hC₂ u huT) _ p) (abs_nonneg _)
  -- Stein's identity, applied once, to `ω_q ↦ w · ∂_q Ψ`
  have hstein : ∀ p ∈ usedCoord d N,
      ∫ ω, ω (crd d N p) • (w ω • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d)
        = (gvar d (crd d N p) : ℝ) •
            ((∫ ω, wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p ∂(P d))
              + Real.sqrt u • ∫ ω, w ω • coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)) := by
    intro p hp
    have hderiv : ∀ ω : Ω d, HasDerivAt
        (fun t : ℝ => w (Function.update ω (crd d N p) t) •
          coordD1 d N (Ψ u) (Hflow d N u (Function.update ω (crd d N p) t)) p)
        (wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p
          + w ω • (Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p))
        (ω (crd d N p)) := by
      intro ω
      have hprod := (hw.hasDeriv p hp ω).smul
        (hasDerivAt_coordD1_update (h.slice huT) u ω hp)
      rw [Function.update_eq_self] at hprod
      exact hprod.congr_deriv (add_comm _ _)
    have hg' : Continuous fun ω : Ω d => wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p
        + w ω • (Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p) :=
      ((hw.contD p hp).smul (continuous_coordD1 (h.slice huT) u p)).add
        (hw.cont.smul ((continuous_coordD2 (h.slice huT) u p).const_smul (Real.sqrt u)))
    have hfd : FinDep d fun ω : Ω d => w ω • coordD1 d N (Ψ u) (Hflow d N u ω) p :=
      finDep_smul_real hw.finDep (finDep_of_Hflow d N u fun M => coordD1 d N (Ψ u) M p)
    have hfd' : FinDep d fun ω : Ω d => wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p
        + w ω • (Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p) :=
      finDep_add'
        (finDep_smul_real (hw.finDepD p hp)
          (finDep_of_Hflow d N u fun M => coordD1 d N (Ψ u) M p))
        (finDep_smul_real hw.finDep
          (finDep_of_Hflow d N u fun M => Real.sqrt u • coordD2 d N (Ψ u) M p))
    have hbnd' : ∃ C : ℝ, ∀ ω : Ω d,
        ‖wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p
          + w ω • (Real.sqrt u • coordD2 d N (Ψ u) (Hflow d N u ω) p)‖ ≤ C := by
      refine ⟨CwD * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) + Cw * (|Real.sqrt u| *
        (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖)), fun ω => ?_⟩
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hCwD p hp ω) (norm_coordD1_le (hC₁ u huT) _ p) (norm_nonneg _)
          (le_trans (abs_nonneg _) (hCwD p hp 0))
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul (hCw ω) ?_ (norm_nonneg _) hCw0
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_coordD2_le (hC₂ u huT) _ p) (abs_nonneg _)
    rw [hst.stein (crd d N p) _ _ (hcd1 p hp) hg' hfd hfd' hderiv
        ⟨Cw * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖), fun ω => hbd1 p ω⟩ hbnd']
    congr 1
    rw [integral_add (hintD p hp) (hintQ p hp)]
    congr 1
    rw [← integral_smul]
    exact integral_congr_ae (Eventually.of_forall fun ω => (smul_comm _ _ _))
  -- assemble
  have hpt : ∀ ω : Ω d, w ω • ((1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p)
      = (1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • (w ω • coordD1 d N (Ψ u) (Hflow d N u ω) p) := by
    intro ω
    rw [smul_comm, Finset.smul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    exact smul_comm _ _ _
  have hIcalc : ∫ ω, w ω • ((1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d)
      = (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
            ∫ ω, w ω • coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)
        + (1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
            ∫ ω, wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p ∂(P d) := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_smul,
      integral_finsetSum _ hint, Finset.sum_congr rfl hstein]
    rw [Finset.smul_sum]
    have hexp : ∀ p ∈ usedCoord d N,
        (1 / (2 * Real.sqrt u)) • ((gvar d (crd d N p) : ℝ) •
            ((∫ ω, wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p ∂(P d))
              + Real.sqrt u • ∫ ω, w ω • coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d)))
          = (1 / 2 : ℝ) • ((gvar d (crd d N p) : ℝ) •
              ∫ ω, w ω • coordD2 d N (Ψ u) (Hflow d N u ω) p ∂(P d))
            + (1 / (2 * Real.sqrt u)) • ((gvar d (crd d N p) : ℝ) •
              ∫ ω, wD p ω • coordD1 d N (Ψ u) (Hflow d N u ω) p ∂(P d)) := by
      intro p _
      have hne : Real.sqrt u ≠ 0 := ne_of_gt hsu
      simp only [smul_add, smul_smul]
      rw [add_comm]
      congr 2
      field_simp
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.smul_sum,
      ← Finset.smul_sum]
  have hsplit : ∫ ω, w ω • (timeD1 Ψ u (Hflow d N u ω)
        + (1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d)
      = (∫ ω, w ω • timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + ∫ ω, w ω • ((1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
            ω (crd d N p) • coordD1 d N (Ψ u) (Hflow d N u ω) p) ∂(P d) := by
    rw [← integral_add]
    · exact integral_congr_ae (Eventually.of_forall fun ω => smul_add (w ω) _ _)
    · refine integrable_of_continuous_of_bound (hw.cont.smul (hcontT u huT))
        (C := Cw * CT) fun ω => ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hCw ω) (hCT u huT _) (norm_nonneg _) hCw0
    · refine (Integrable.congr ?_ (Eventually.of_forall fun ω => (hpt ω).symm))
      exact Integrable.smul (1 / (2 * Real.sqrt u) : ℝ) (integrable_finsetSum _ hint)
  have hfin := hmain.2
  rwa [hsplit, hIcalc] at hfin

end Gauss

namespace MomentDuhamel

open MeasureTheory Real Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### 4. (S4): the weighted Minkowski closure (G) -/

/-- **The weighted moment norm** `‖Y‖_{W,2p} = (E[W·|Y|^{2p}])^{1/(2p)}`.  With `W ≡ 1` this is
`RBM.MomentDuhamel.momNorm P (2p)` (`momNormW_one`). -/
noncomputable def momNormW (P : Measure Ω) (W : Ω → ℝ) (p : ℕ) (Y : Ω → ℝ) : ℝ :=
  (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ)))

theorem momNormW_one (P : Measure Ω) (p : ℕ) (Y : Ω → ℝ) :
    momNormW P (fun _ => (1 : ℝ)) p Y = momNorm P (2 * p) Y := by
  rw [momNormW, momNorm_eq_rpow]
  simp

theorem momNormW_nonneg (P : Measure Ω) {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (p : ℕ)
    (Y : Ω → ℝ) : 0 ≤ momNormW P W p Y :=
  Real.rpow_nonneg
    (integral_nonneg fun ω => mul_nonneg (hW0 ω) (pow_nonneg (abs_nonneg _) _)) _

/-- `√(φ^{1/p}) = φ^{1/(2p)}` for `φ ≥ 0` — the bridge between the exponent
`RBM.MomentDuhamel.rpow_inv_le_of_deriv_le_Icc` produces and the one
`RBM.sqrt_le_of_integral_le` consumes. -/
theorem sqrt_rpow_inv {φ : ℝ} (hφ : 0 ≤ φ) {p : ℕ} (hp : 1 ≤ p) :
    √(φ ^ ((1 : ℝ) / (p : ℝ))) = φ ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
  have hq1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hφ]
  congr 1
  field_simp

/-- **⭐⭐ (G), the weighted Minkowski closure.**

From the *differential* inequality on the **open** window `Ioo s v`

`φ'(u) ≤ 2p·φ(u)^{1-1/(2p)}·(A u + B u) + p(2p-1)·φ(u)^{1-1/p}·g u`,  `φ u = E[W·|Y_u|^{2p}]`,

one gets the Minkowski-type bound

`‖Y_v‖_{W,2p} ≤ ‖Y_s‖_{W,2p} + 2∫_s^v (A + B) + √((2p-1)·∫_s^v g)`.

`A` is the weighted drift norm `‖U_{u,v}F_u/T‖_{W,2p}` and `B = ‖D̃_u‖_{2p}` is the cross term
of the weighted generator identity `RBM.Gauss.hasDerivAt_integral_weighted`; the two enter the
hypothesis in exactly the same place, which is the point of the `χ^{2p}` weight.

**The Grönwall factor is `1`** — there is no exponential: this is Minkowski, not Grönwall, so
no `e^{C(t-s)}` multiplies the initial datum.

The derivative is asked for only on `Set.Ioo s v`, so the **left endpoint may be `0`**, which is
what route (A′)'s first cell needs. -/
theorem weightedMinkowski_of_deriv_le {P : Measure Ω} {s v : ℝ} (hsv : s ≤ v) {p : ℕ}
    (hp : 1 ≤ p) {W : Ω → ℝ} {Y : ℝ → Ω → ℝ} {φ' A B g : ℝ → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hcont : ContinuousOn (fun u => ∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P) (Set.Icc s v))
    (hderiv : ∀ u ∈ Set.Ioo s v,
      HasDerivAt (fun r => ∫ ω, W ω * |Y r ω| ^ (2 * p) ∂P) (φ' u) u)
    (hφ'int : IntervalIntegrable φ' volume s v)
    (hA0 : ∀ u ∈ Set.Icc s v, 0 ≤ A u) (hB0 : ∀ u ∈ Set.Icc s v, 0 ≤ B u)
    (hg0 : ∀ u ∈ Set.Icc s v, 0 ≤ g u)
    (hABint : IntervalIntegrable (fun r => A r + B r) volume s v)
    (hgint : IntervalIntegrable g volume s v)
    (hintψf : ∀ u ∈ Set.Icc s v, IntervalIntegrable
      (fun r => momNormW P W p (Y r) * (A r + B r)) volume s u)
    (hbound : ∀ u ∈ Set.Ioo s v, φ' u
      ≤ 2 * (p : ℝ) * (∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P)
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (A u + B u)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ)) * g u) :
    momNormW P W p (Y v)
      ≤ momNormW P W p (Y s) + 2 * (∫ r in s..v, (A r + B r))
        + √ ((2 * (p : ℝ) - 1) * ∫ r in s..v, g r) := by
  have hq1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  set φ : ℝ → ℝ := fun u => ∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P with hφdef
  have hφ0 : ∀ u, 0 ≤ φ u := fun u =>
    integral_nonneg fun ω => mul_nonneg (hW0 ω) (pow_nonneg (abs_nonneg _) _)
  set ψ : ℝ → ℝ := fun u => φ u ^ ((1 : ℝ) / (p : ℝ)) with hψdef
  have hψ0 : ∀ u ∈ Set.Icc s v, 0 ≤ ψ u := fun u _ => Real.rpow_nonneg (hφ0 u) _
  have hsqrtψ : ∀ u, √ (ψ u) = φ u ^ ((1 : ℝ) / (2 * (p : ℝ))) :=
    fun u => sqrt_rpow_inv (hφ0 u) hp
  have hmomφ : ∀ u, momNormW P W p (Y u) = φ u ^ ((1 : ℝ) / (2 * (p : ℝ))) := fun u => rfl
  -- the integrated form (T191)
  have hdu := rpow_inv_le_of_deriv_le_Icc (φ := φ) (φ' := φ') (f := fun r => A r + B r) (g := g)
    hsv hp (fun u _ => hφ0 u) hcont hderiv hφ'int
    (fun u hu => add_nonneg (hA0 u hu) (hB0 u hu)) hg0 hABint hgint hbound
  -- a supremum exists, because `φ` is continuous on the compact window
  obtain ⟨Cb, hCb⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn hcont
  have hψle : ∀ u ∈ Set.Icc s v, ψ u ≤ Cb ^ ((1 : ℝ) / (p : ℝ)) := by
    intro u hu
    have : φ u ≤ Cb := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hCb u hu)
    exact Real.rpow_le_rpow (hφ0 u) this (by positivity)
  obtain ⟨M, hM⟩ := exists_isLUB_Icc hsv hψle
  have hkey := sqrt_le_of_integral_le (ψ := ψ) (f := fun r => A r + B r) (g := g)
    (c := 2 * (p : ℝ) - 1) (M := M) hsv hψ0
    (fun r hr => add_nonneg (hA0 r hr) (hB0 r hr)) hg0 (by linarith) hM
    (by
      intro u hu
      refine (hintψf u hu).congr fun r _ => ?_
      rw [hmomφ r, hsqrtψ r])
    hABint hgint
    (by
      intro u hu
      have h := hdu u hu
      have hrw : ∀ r, √ (ψ r) * (A r + B r)
          = φ r ^ ((1 : ℝ) / (2 * (p : ℝ))) * (A r + B r) := fun r => by rw [hsqrtψ r]
      simp only [hrw]
      exact h)
  rw [hmomφ, hmomφ, ← hsqrtψ v, ← hsqrtψ s]
  exact hkey

/-- **A compiled satisfiability witness for (G).**  Everything degenerate: `W ≡ 1`, `Y ≡ 0`,
`A = B = g = 0`, `φ' = 0`.  All hypotheses hold and the conclusion is `0 ≤ 0`; in particular
the hypothesis set is not self-contradictory, and it is satisfied at `s = 0` (the left endpoint
route (A′) needs) and for **every** `p ≥ 1`. -/
theorem sat_weightedMinkowski (P : Measure Ω) [IsFiniteMeasure P] {p : ℕ} (hp : 1 ≤ p) :
    momNormW P (fun _ => (1 : ℝ)) p (fun _ => (0 : ℝ))
      ≤ momNormW P (fun _ => (1 : ℝ)) p (fun _ => (0 : ℝ))
        + 2 * (∫ _r in (0 : ℝ)..1, ((0 : ℝ) + 0))
        + √ ((2 * (p : ℝ) - 1) * ∫ _r in (0 : ℝ)..1, (0 : ℝ)) := by
  refine weightedMinkowski_of_deriv_le (P := P) (W := fun _ => (1 : ℝ))
    (Y := fun _ _ => (0 : ℝ)) (φ' := fun _ => 0) (A := fun _ => 0) (B := fun _ => 0)
    (g := fun _ => 0) zero_le_one hp (fun _ => zero_le_one) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h2p : 2 * p ≠ 0 := by omega
    have hz : (fun u : ℝ => ∫ _ω, (1 : ℝ) * |(0 : ℝ)| ^ (2 * p) ∂P) = fun _ : ℝ => (0 : ℝ) := by
      funext r
      simp [h2p]
    rw [hz]
    exact continuousOn_const
  · intro u _
    have h2p : 2 * p ≠ 0 := by omega
    have hz : (fun r : ℝ => ∫ _ω, (1 : ℝ) * |(0 : ℝ)| ^ (2 * p) ∂P) = fun _ : ℝ => (0 : ℝ) := by
      funext r
      simp [h2p]
    rw [hz]
    exact hasDerivAt_const u 0
  · exact intervalIntegrable_const
  · exact fun _ _ => le_rfl
  · exact fun _ _ => le_rfl
  · exact fun _ _ => le_rfl
  · exact intervalIntegrable_const
  · exact intervalIntegrable_const
  · intro u _
    simp
  · intro u hu
    simp

/-- **A non-degenerate witness for (G)**: `p = 1`, `W ≡ 1`, `Y_u ≡ √u`, `A = B = 0`, `g ≡ 1`.

Here `φ u = E[|Y_u|²] = u`, the differential hypothesis holds **with equality** (`1 ≤ 1`, the
sharp case already recorded as `RBM.MomentDuhamel.deriv_le_hyp_sharp_one`), and the conclusion
is `1 ≤ 0 + 0 + √1`, again an equality.  So the hypothesis bundle of
`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le` is satisfiable by an instance in which the
moment, the derivative and the quadratic-variation term are all **nonzero**, and the conclusion
is attained — it is neither vacuous nor slack. -/
theorem sat_weightedMinkowski_sharp (P : Measure Ω) [IsProbabilityMeasure P] :
    momNormW P (fun _ => (1 : ℝ)) 1 (fun _ => √(1 : ℝ))
      ≤ momNormW P (fun _ => (1 : ℝ)) 1 (fun _ => √(0 : ℝ))
        + 2 * (∫ _r in (0 : ℝ)..1, ((0 : ℝ) + 0))
        + √ ((2 * ((1 : ℕ) : ℝ) - 1) * ∫ _r in (0 : ℝ)..1, (1 : ℝ)) := by
  have hsq : (fun u : ℝ => ∫ _ω, (1 : ℝ) * |√u| ^ (2 * 1) ∂P) = fun u : ℝ => |√u| ^ 2 := by
    funext u
    simp
  refine weightedMinkowski_of_deriv_le (P := P) (W := fun _ => (1 : ℝ))
    (Y := fun u _ => √u) (φ' := fun _ => 1) (A := fun _ => 0) (B := fun _ => 0)
    (g := fun _ => 1) zero_le_one le_rfl (fun _ => zero_le_one) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsq]
    exact (Real.continuous_sqrt.abs.pow 2).continuousOn
  · intro u hu
    rw [hsq]
    have hev : (fun u : ℝ => |√u| ^ 2) =ᶠ[nhds u] fun r : ℝ => r := by
      filter_upwards [Ioi_mem_nhds hu.1] with r hr
      rw [abs_of_nonneg (Real.sqrt_nonneg r), Real.sq_sqrt (le_of_lt hr)]
    exact (hasDerivAt_id u).congr_of_eventuallyEq hev
  · exact intervalIntegrable_const
  · exact fun _ _ => le_rfl
  · exact fun _ _ => le_rfl
  · exact fun _ _ => zero_le_one
  · exact intervalIntegrable_const
  · exact intervalIntegrable_const
  · intro u _
    simp
  · intro u _
    norm_num

end MomentDuhamel

end RBM

/-!
## Deviations from the paper

**T264a** (§5.3, (5.39)–(5.48); the generator/Stein step of §5.2).

1. *The paper's stopped Duhamel is replaced by a fixed `ω`-weight.*  (5.43) is stated with a
   stopping time `T`; route (A′) integrates against a smooth prefix weight instead, which is
   the deviation already recorded as `T230a` in `RBM1D/Gauss/APrimeTestFun.lean`.  The present
   file only supplies the analytic identity that the replacement needs, so nothing is
   renumbered.  What is new here is that the weight produces a **third** term in the generator
   identity — the cross term `(2√u)⁻¹ ∑_q S_q E[(∂_q w)·∂_qΨ]` — which has no counterpart in
   the paper's display, because the paper's indicator is not differentiated at all.  The term
   is genuine, not an artefact: it is the price of removing the stopping time.
2. *The weight's regularity is first order only.*  `RBM.Gauss.WeightC1` asks for one
   coordinate derivative of `w` and for bounds on `w` and `∂_q w`; it deliberately does **not**
   ask for `∂_q² w`.  This is not a deviation from the paper (which has no weight) but a
   deliberately minimal hypothesis, per the repository's rule that a class must require only
   the order actually used.
3. *The closure is Minkowski, not Grönwall.*  `RBM.MomentDuhamel.weightedMinkowski_of_deriv_le`
   reproduces the paper's (5.20)+(5.24) closure with the weight carried through, and its
   Grönwall factor is `1`.  The constant in front of `∫ g` is `2p - 1`, i.e.
   `RBM.MomentDuhamel.Hyp.cMD p`, unchanged.  No statement of the paper is altered.
-/

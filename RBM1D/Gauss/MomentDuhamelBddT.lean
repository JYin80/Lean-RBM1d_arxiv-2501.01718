/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelTime

/-!
# `RBM.Gauss.TestFunT₁` for the moment route's `Ψ` (T196)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  T191 reduced both fields of `RBM.MomentDuhamel.Hyp` to a pointwise
derivative bound plus the admissibility of

  `Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}`   (`RBM.Gauss.momentObsT`)

in the relaxed class `RBM.Gauss.TestFunT₁`, and left four items short: `contDiffM`,
`diffJoint`, `contT` and `bddT`.  **`RBM.Gauss.testFunT₁_momentObsT` closes all seven fields**;
the capstone `RBM.Gauss.hasDerivAt_integral_momentObsT` is T132b's generator identity at this
`Ψ` with no hypothesis left on `Ψ`.

## `bddT`: the point T187 and T191 make

`RBM.Gauss.bddC1On` (T141) bounds the derivative of the loop observable **in the matrix**,
uniformly over a ball of spectral parameters.  That is not a bound on the derivative **in the
spectral parameter**, which is what `bddT` asks for, because the running time `u` enters `Ψ`
through `z_u = E + (1-u) m_E`.  The `z`-derivative does exist in the repository —
`RBM.Gauss.hasDerivAt_gloop_zt` (T134) with the deterministic envelope
`RBM.Gauss.norm_zMotion_le` — so the content is not the resolvent identity `∂_z G = G²` but
the *assembly*: `u` occurs in `Ψ` in three places at once (the spectral parameter, the
propagator's running time, and `K_u`), all three have to be differentiated
(`RBM.Gauss.hasDerivAt_momentObsT`) and bounded uniformly over the window
(`RBM.Gauss.bddT_momentObsT`).

## `diffJoint`

`RBM.Gauss.contDiffAt_gloopProd_zt_pair` is the pair-variable form of
`RBM.EGDef.contDiffAt_gloopProd_matrix`, by induction over the `n` factors of (2.41) on top of
`RBM.Gauss.contDiffAt_resH_path`.  It is `C²`, so only the first order that T191 showed to be
enough is used.

## `bdd₀`, `bdd₁`, `bdd₂`

T133's `RBM.Gauss.testFun_momentFun_ukerObs` gives these at a *fixed* `u` and the class wants
them uniformly over the window, so the existential constants have to be named:
`RBM.Gauss.exists_bddC2C_momentFun` is `RBM.Gauss.bddC2_momentFun` with constants that do not
depend on the function, obtained from `RBM.Gauss.BddC2C`'s closure under products
(`bddC2C_mul_cx`) and powers (`exists_bddC2C_pow`).  After that the only `u`-dependence left
is `RBM.Gauss.ukerRow`, a continuous function of `u` alone, which the compact window bounds.

## What is **not** here

The remainder of T191's programme: the *identification* of `φ'` (cancelling `∫ ∂₁Ψ` against
`genS` through `RBM.MomentDuhamel.Hyp.drift`, the second-order term through
`genMomentPt_le'`, the quadratic variation through `quadVarPairs_Uker`), the interval
integrability side conditions, and hence the two fields of `RBM.MomentDuhamel.Hyp` themselves.
Also absent is the bridge `RBM.Gauss.momentObsT ↔ RBM.SumZeroDyn.lkT` along the flow.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ}

/-! ### `bddT` from a uniform bound on the time derivative

`RBM.Gauss.timeD1` is a `deriv`, so a `HasDerivAt` witness identifies it and the field is
exactly a uniform bound on that witness. -/

/-- `RBM.Gauss.timeD1` read off a `HasDerivAt` witness. -/
theorem timeD1_eq_of_hasDerivAt {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {u : ℝ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} {D : ℂ} (h : HasDerivAt (fun s : ℝ => Ψ s M) D u) :
    timeD1 Ψ u M = D := h.deriv

/-- **The shape of the field `RBM.Gauss.TestFunT₁.bddT`**: a derivative witness plus a bound
on it, both uniform over the window and over the matrix. -/
theorem bddT_of_hasDerivAt {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {D : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C : ℝ}
    (hd : ∀ u ∈ T, ∀ M, HasDerivAt (fun s : ℝ => Ψ s M) (D u M) u)
    (hb : ∀ u ∈ T, ∀ M, ‖D u M‖ ≤ C) :
    ∃ C' : ℝ, ∀ u ∈ T, ∀ M, ‖timeD1 Ψ u M‖ ≤ C' :=
  ⟨C, fun u hu M => by
    rw [timeD1_eq_of_hasDerivAt (hd u hu M)]
    exact hb u hu M⟩

/-! ### `|F|^{2p}` along a path

`RBM.Gauss.momentFun F p = (F · conj F)^p`.  Conjugation is `ℝ`-linear (not `ℂ`-linear), so a
real path through `ℂ` may be differentiated through it; this is the only place the real
structure is used. -/

/-- Conjugation is `ℝ`-differentiable: `∂(conj ∘ f) = conj ∂f`. -/
theorem hasDerivAt_starRingEnd_comp {f : ℝ → ℂ} {c : ℂ} {u : ℝ} (h : HasDerivAt f c u) :
    HasDerivAt (fun s : ℝ => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) c) u := by
  have h2 : (fun s : ℝ => (starRingEnd ℂ) (f s))
      = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap ∘ f := rfl
  rw [h2]
  have h3 := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u h
  simpa [Complex.conjCLE_apply] using h3

/-- **`∂_u |f(u)|^{2p}`**, written in the `RBM.Gauss.momentFun` form `(f · conj f)^p` so that
no absolute value is differentiated (the formula is valid at `f(u) = 0` too, and at `p = 0`
the leading `(p : ℂ)` kills the nat-subtraction `p - 1`). -/
theorem hasDerivAt_momentFun_path {f : ℝ → ℂ} {c : ℂ} {u : ℝ} (h : HasDerivAt f c u) (p : ℕ) :
    HasDerivAt (fun s : ℝ => (f s * (starRingEnd ℂ) (f s)) ^ p)
      ((p : ℂ) * (f u * (starRingEnd ℂ) (f u)) ^ (p - 1)
        * (c * (starRingEnd ℂ) (f u) + f u * (starRingEnd ℂ) c)) u := by
  have hg : HasDerivAt (fun s : ℝ => f s * (starRingEnd ℂ) (f s))
      (c * (starRingEnd ℂ) (f u) + f u * (starRingEnd ℂ) c) u :=
    h.mul (hasDerivAt_starRingEnd_comp h)
  exact hg.pow p

/-- The bound that goes with `RBM.Gauss.hasDerivAt_momentFun_path`:
`‖∂_u |f|^{2p}‖ ≤ 2p ‖f‖^{2p-1} ‖∂_u f‖`, written so that the nat subtraction never has to be
simplified. -/
theorem norm_deriv_momentFun_path_le {f : ℝ → ℂ} {c : ℂ} {u : ℝ} {Ca Cc : ℝ} (hCa : 0 ≤ Ca)
    (ha : ‖f u‖ ≤ Ca) (hc : ‖c‖ ≤ Cc) (p : ℕ) :
    ‖(p : ℂ) * (f u * (starRingEnd ℂ) (f u)) ^ (p - 1)
        * (c * (starRingEnd ℂ) (f u) + f u * (starRingEnd ℂ) c)‖
      ≤ (p : ℝ) * Ca ^ (2 * (p - 1)) * (2 * Cc * Ca) := by
  have hCc : 0 ≤ Cc := le_trans (norm_nonneg _) hc
  have hsq : ‖f u * (starRingEnd ℂ) (f u)‖ = ‖f u‖ ^ 2 := by
    rw [norm_mul, RCLike.norm_conj, sq]
  have h1 : ‖(f u * (starRingEnd ℂ) (f u)) ^ (p - 1)‖ ≤ Ca ^ (2 * (p - 1)) := by
    rw [norm_pow, hsq, ← pow_mul, mul_comm 2 (p - 1)]
    exact pow_le_pow_left₀ (norm_nonneg _) ha _
  have h2 : ‖c * (starRingEnd ℂ) (f u) + f u * (starRingEnd ℂ) c‖ ≤ 2 * Cc * Ca := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    have hx : ‖c‖ * ‖f u‖ ≤ Cc * Ca :=
      mul_le_mul hc ha (norm_nonneg _) hCc
    have hy : ‖f u‖ * ‖c‖ ≤ Cc * Ca := by
      rw [mul_comm]; exact hx
    linarith
  calc ‖(p : ℂ) * (f u * (starRingEnd ℂ) (f u)) ^ (p - 1)
          * (c * (starRingEnd ℂ) (f u) + f u * (starRingEnd ℂ) c)‖
      = ‖(p : ℂ)‖ * ‖(f u * (starRingEnd ℂ) (f u)) ^ (p - 1)‖
          * ‖c * (starRingEnd ℂ) (f u) + f u * (starRingEnd ℂ) c‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (p : ℝ) * Ca ^ (2 * (p - 1)) * (2 * Cc * Ca) := by
        have hp : ‖(p : ℂ)‖ = (p : ℝ) := by
          simp
        rw [hp]
        have hleft : (p : ℝ) * ‖(f u * (starRingEnd ℂ) (f u)) ^ (p - 1)‖
            ≤ (p : ℝ) * Ca ^ (2 * (p - 1)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg p)
        exact mul_le_mul hleft h2 (norm_nonneg _) (by positivity)

/-! ### The spectral parameter moves

`RBM.Gauss.loopObs` is `RBM.gloop` precomposed with `RBM.Gauss.hermCLM`, so its argument is
Hermitian **at every matrix**, and T134's `z`-motion applies with no side condition on `M`.
This is what makes the `∀ M` of `RBM.Gauss.TestFunT₁.bddT` non-vacuous here: the bound below
is uniform in `M` because the resolvent envelope `‖G‖ ≤ η⁻¹` holds at `hermCLM M` for every
`M`, Hermitian or not. -/

/-- **`∂_u L_{σ,a}(z_u)` for the regularised loop observable.**  T134's
`RBM.Gauss.hasDerivAt_gloop_zt` at the Hermitian matrix `hermCLM M`. -/
theorem hasDerivAt_loopObs_zt (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    HasDerivAt (fun s : ℝ => loopObs d N (zt Ev s) I M)
      (zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u) I) u :=
  hasDerivAt_gloop_zt (isHermitian_hermCLM M) hz I hwf

/-- The deterministic envelope for `∂_u L_{σ,a}(z_u)`, **uniform in the matrix**: T134's
`RBM.Gauss.norm_zMotion_le` at `hermCLM M`.  The only thing the spectral parameter
contributes is the lower bound `η ≤ |Im z|`, so the bound is uniform over any window on
which that holds. -/
theorem norm_zMotion_hermCLM_le {η : ℝ} (hη : 0 < η) {z : ℂ} (hzη : η ≤ |z.im|) (Ev : ℝ)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) z I‖
      ≤ (I.length : ℝ) * (max ‖mSigma Ev true‖ ‖mSigma Ev false‖ *
          ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) *
            (η⁻¹ ^ (I.length + 1) * ((d.W N : ℝ))⁻¹ ^ I.length)))) :=
  norm_zMotion_le (isHermitian_hermCLM M) hη hzη (mSigma Ev) I hwf

/-! ### The propagator's running time moves as well -/

/-- `u ↦ (U_{u,v})_{xy}` is continuous — it is affine in `u`, `RBM.hasDerivAt_edgeKer`. -/
theorem continuous_edgeKer_time {L : ℕ} [NeZero L] (ξ t : ℂ) (x y : ZMod L) :
    Continuous fun r : ℝ => edgeKer L ξ (r : ℂ) t x y :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_edgeKer L ξ t x y r).continuousAt

/-- **Leibniz for `RBM.Uker` with a *moving* argument.**  `RBM.hasDerivAt_Uker_apply` moves
the running time inside the kernel only; on the moment route the function the kernel is
applied to, `(L - K)_u`, moves with `u` too. -/
theorem hasDerivAt_Uker_arg {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (A : ℝ → LoopArg L n → ℂ) (A' : LoopArg L n → ℂ) {u : ℝ}
    (hA : ∀ b, HasDerivAt (fun r : ℝ => A r b) (A' b) u) (a : LoopArg L n) :
    HasDerivAt (fun r : ℝ => Uker L ξ (r : ℂ) t (A r) a)
      (∑ b : LoopArg L n,
        ((∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b j))
            * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) * A u b
          + (∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)) * A' b)) u := by
  simp only [Uker]
  refine HasDerivAt.fun_sum (fun b _ => ?_)
  have hprod : HasDerivAt (fun r : ℝ => ∏ i : Fin n, edgeKer L (ξ i) (r : ℂ) t (a i) (b i))
      (∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b j))
        * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) u := by
    have h := HasDerivAt.fun_finsetProd
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        hasDerivAt_edgeKer L (ξ i) t (a i) (b i) u)
    simpa only [smul_eq_mul] using h
  exact hprod.mul (hA b)

/-- The `ℓ¹` size of the two kernels appearing in `RBM.Gauss.hasDerivAt_Uker_arg`.  It does
**not** involve the matrix, so the window-uniformity of the bound on `∂_u Ψ` reduces to the
continuity of this one function of `u`. -/
noncomputable def ukerCoefBd {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) : ℝ :=
  ∑ b : LoopArg L n,
    (‖∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b j))
        * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))‖
      + ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)‖)

theorem ukerCoefBd_nonneg {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) : 0 ≤ ukerCoefBd ξ t a u :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_ukerCoefBd {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) : Continuous (ukerCoefBd ξ t a) := by
  refine continuous_finsetSum _ fun b _ => ?_
  refine Continuous.add ?_ ?_
  · refine Continuous.norm (continuous_finsetSum _ fun i _ => ?_)
    exact (continuous_finsetProd _ fun j _ => continuous_edgeKer_time _ _ _ _).mul
      continuous_const
  · exact Continuous.norm (continuous_finsetProd _ fun i _ => continuous_edgeKer_time _ _ _ _)

/-- The bound that goes with `RBM.Gauss.hasDerivAt_Uker_arg`. -/
theorem norm_deriv_Uker_arg_le {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (A A' : LoopArg L n → ℂ) {C : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ C) (hA' : ∀ b, ‖A' b‖ ≤ C) :
    ‖∑ b : LoopArg L n,
        ((∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b j))
            * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) * A b
          + (∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)) * A' b)‖
      ≤ ukerCoefBd ξ t a u * C := by
  refine le_trans (norm_sum_le _ _) ?_
  rw [ukerCoefBd, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  refine le_trans (norm_add_le _ _) ?_
  rw [add_mul, norm_mul, norm_mul]
  gcongr
  · exact hA b
  · exact hA' b

/-- The value of `RBM.Uker` is controlled by the same `ℓ¹` size. -/
theorem norm_Uker_le_ukerCoefBd {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (A : LoopArg L n → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ b, ‖A b‖ ≤ C) :
    ‖Uker L ξ (u : ℂ) t A a‖ ≤ ukerCoefBd ξ t a u * C := by
  simp only [Uker]
  refine le_trans (norm_sum_le _ _) ?_
  rw [ukerCoefBd, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [norm_mul, add_mul]
  have h1 : ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)‖ * ‖A b‖
      ≤ ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)‖ * C :=
    mul_le_mul_of_nonneg_left (hA b) (norm_nonneg _)
  have h2 : (0 : ℝ)
      ≤ ‖∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b j))
          * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))‖ * C := by
    positivity
  linarith

/-! ### The moment route's `Ψ`, and its `bddT`

`Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}` has the running time in **three** places: the
spectral parameter `z_u` inside the loop, the running time of the propagator `U_{u,v}`, and
the primitive `K_u`.  `RBM.Gauss.ukerObsT` is the inner observable with all three moving. -/

/-- `(U_{u,v} ∘ (L - K)_u)_a` as a function of the running time and the matrix. -/
noncomputable def ukerObsT (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ukerObs d N (zt Ev u) σ ξ (u : ℂ) t (K u) a M

/-- `Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}`, in the `RBM.Gauss.momentFun` form. -/
noncomputable def momentObsT (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  fun u M => momentFun (ukerObsT d N Ev σ ξ t K a u) p M

/-- `∂_u (U_{u,v} ∘ (L - K)_u)_a`: the propagator's own time derivative applied to `(L-K)_u`,
plus the propagator applied to `∂_u (L - K)_u`, the second summand carrying the `z`-motion
`RBM.Gauss.zMotion`. -/
noncomputable def ukerObsTDeriv (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ∑ b : LoopArg (d.L N) m,
    ((∑ i : Fin m, (∏ j ∈ Finset.univ.erase i,
          edgeKer (d.L N) (ξ j) (u : ℂ) t (a j) (b j))
        * (-(ξ i * (SB (d.L N) * Theta (d.L N) (t * ξ i)) (a i) (b i))))
        * (loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b)
      + (∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i))
        * (zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
            ⟨σ, List.ofFn b⟩ - K' u b))

/-- **The time derivative of the moment route's inner observable.** -/
theorem hasDerivAt_ukerObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    HasDerivAt (fun s : ℝ => ukerObsT d N Ev σ ξ t K a s M)
      (ukerObsTDeriv d N Ev σ ξ t K K' a u M) u := by
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hA : ∀ b : LoopArg (d.L N) m,
      HasDerivAt (fun r : ℝ => loopObs d N (zt Ev r) ⟨σ, List.ofFn b⟩ M - K r b)
        (zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
            ⟨σ, List.ofFn b⟩ - K' u b) u := fun b =>
    (hasDerivAt_loopObs_zt Ev hz _ (hwf b) M).sub (hK b)
  exact hasDerivAt_Uker_arg ξ t
    (fun r b => loopObs d N (zt Ev r) ⟨σ, List.ofFn b⟩ M - K r b) _ hA a

/-- The bound on `RBM.Gauss.ukerObsTDeriv`, uniform in the matrix: the whole matrix dependence
sits in `(L - K)_u` and in its `z`-motion, and both are controlled by the deterministic
envelope. -/
theorem norm_ukerObsTDeriv_le (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) {C : ℝ}
    (hval : ∀ b : LoopArg (d.L N) m,
      ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C)
    (hder : ∀ b : LoopArg (d.L N) m,
      ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
          ⟨σ, List.ofFn b⟩ - K' u b‖ ≤ C) :
    ‖ukerObsTDeriv d N Ev σ ξ t K K' a u M‖ ≤ ukerCoefBd ξ t a u * C :=
  norm_deriv_Uker_arg_le ξ t a u _ _ hval hder

/-- The matching bound on the value. -/
theorem norm_ukerObsT_le (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hval : ∀ b : LoopArg (d.L N) m,
      ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C) :
    ‖ukerObsT d N Ev σ ξ t K a u M‖ ≤ ukerCoefBd ξ t a u * C :=
  norm_Uker_le_ukerCoefBd ξ t a u _ hC hval

/-- `Ψ` written out.  Stated (rather than left to `rfl`) because the definitional unfolding
runs through `RBM.LoopArg`, where `whnf` times out — the same trap T187 records for
`RBM.Gauss.hermFun_momentFun_ukerRaw`. -/
theorem momentObsT_eq (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    momentObsT d N Ev σ ξ t K a p u M
      = (ukerObsT d N Ev σ ξ t K a u M
          * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)) ^ p := by
  simp only [momentObsT, momentFun]

/-- **The time derivative of `Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}`.** -/
theorem hasDerivAt_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    HasDerivAt (fun s : ℝ => momentObsT d N Ev σ ξ t K a p s M)
      ((p : ℂ) * (ukerObsT d N Ev σ ξ t K a u M
            * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)) ^ (p - 1)
        * (ukerObsTDeriv d N Ev σ ξ t K K' a u M
              * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)
            + ukerObsT d N Ev σ ξ t K a u M
              * (starRingEnd ℂ) (ukerObsTDeriv d N Ev σ ξ t K K' a u M))) u := by
  have hfun : (fun s : ℝ => momentObsT d N Ev σ ξ t K a p s M)
      = fun s : ℝ => (ukerObsT d N Ev σ ξ t K a s M
          * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a s M)) ^ p :=
    funext fun s => momentObsT_eq Ev σ ξ t K a p s M
  rw [hfun]
  exact hasDerivAt_momentFun_path (hasDerivAt_ukerObsT Ev hσ ξ t K K' a hz hK M) p

/-- **`bddT` for the moment route's `Ψ`.**

`Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}` has `∂_u Ψ` bounded uniformly over the window
`[u₀, u₁]` **and over all matrices**.  The three inputs are:

* the deterministic envelope `‖G‖ ≤ η⁻¹` for the loop and, through `RBM.Gauss.zMotion`, for
  its `z`-derivative — this is the part T187 and T191 identify as missing, and it is uniform
  in `M` because `RBM.Gauss.loopObs` carries `RBM.Gauss.hermCLM`;
* the propagator's own time dependence, which is affine (`RBM.hasDerivAt_edgeKer`) and whose
  `ℓ¹` size `RBM.Gauss.ukerCoefBd` is a continuous function of `u` alone, hence bounded on the
  compact window;
* bounds on `K_u` and on `∂_u K_u`, which are hypotheses here: they contain no matrix and no
  resolvent, and on the Gaussian model they come from `RBM.hasDerivAt_Kgen_all` together with
  `RBM.norm_primRhs_le` (see `RBM.norm_Kgen_sub_le`).

The window enters only through `hzim`, `η ≤ |Im z_u|`, which on `[s_N, t_N]` with `t_N < 1`
is `RBM.le_zt_im`. -/
theorem bddT_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖timeD1 (momentObsT d N Ev σ ξ t K a p) u M‖ ≤ C := by
  classical
  set Cloop : ℝ := η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) with hCloop
  set CzM : ℝ := (m : ℝ) * (max ‖mSigma Ev true‖ ‖mSigma Ev false‖ *
      ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) *
        (η⁻¹ ^ (m + 1) * ((d.W N : ℝ))⁻¹ ^ m)))) with hCzM
  set C₀ : ℝ := max (Cloop + cK) (CzM + cK) with hC₀
  have hCloop0 : 0 ≤ Cloop := by positivity
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (le_max_left _ _)
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hlen : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).a.length = m := fun b => by
    show (List.ofFn b).length = m
    rw [List.length_ofFn]
  -- the pointwise bound, with the only `u`-dependence in `ukerCoefBd`
  set Q : ℝ → ℝ := fun u => ukerCoefBd ξ t a u * C₀ with hQ
  have hQ0 : ∀ u, 0 ≤ Q u := fun u => mul_nonneg (ukerCoefBd_nonneg ξ t a u) hC₀0
  have hpt : ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖timeD1 (momentObsT d N Ev σ ξ t K a p) u M‖
        ≤ (p : ℝ) * Q u ^ (2 * (p - 1)) * (2 * Q u * Q u) := by
    intro u hu M
    have hz : (zt Ev u).im ≠ 0 := by
      have := lt_of_lt_of_le hη (hzim u hu)
      exact fun h => by simp [h] at this
    have hval : ∀ b : LoopArg (d.L N) m,
        ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C₀ := by
      intro b
      have h : ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ ≤ Cloop := by
        have h0 := norm_loopObs_le hη (hzim u hu) _ (hwf b) (by rw [hlen b]; exact hm) M
        rw [hlen b] at h0
        exact h0
      calc ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖
          ≤ ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ + ‖K u b‖ := norm_sub_le _ _
        _ ≤ Cloop + cK := add_le_add h (hKb u hu b)
        _ ≤ C₀ := le_max_left _ _
    have hder : ∀ b : LoopArg (d.L N) m,
        ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
            ⟨σ, List.ofFn b⟩ - K' u b‖ ≤ C₀ := by
      intro b
      have h : ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
          ⟨σ, List.ofFn b⟩‖ ≤ CzM := by
        have h0 := norm_zMotion_hermCLM_le hη (hzim u hu) Ev _ (hwf b) M
        have hl : (LoopIdx.mk σ (List.ofFn b)).length = m := hlen b
        rw [hl] at h0
        exact h0
      calc ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
              ⟨σ, List.ofFn b⟩ - K' u b‖
          ≤ ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
              ⟨σ, List.ofFn b⟩‖ + ‖K' u b‖ := norm_sub_le _ _
        _ ≤ CzM + cK := add_le_add h (hK'b u hu b)
        _ ≤ C₀ := le_max_right _ _
    rw [timeD1_eq_of_hasDerivAt
      (hasDerivAt_momentObsT Ev hσ ξ t K K' a p hz (fun b => hK u hu b) M)]
    exact norm_deriv_momentFun_path_le
      (f := fun s : ℝ => ukerObsT d N Ev σ ξ t K a s M)
      (c := ukerObsTDeriv d N Ev σ ξ t K K' a u M) (hQ0 u)
      (norm_ukerObsT_le Ev σ ξ t K a u M hC₀0 hval)
      (norm_ukerObsTDeriv_le Ev σ ξ t K K' a u M hval hder) p
  -- the window is compact and the bound is continuous on it
  have hQc : Continuous Q := (continuous_ukerCoefBd ξ t a).mul continuous_const
  have hgc : Continuous fun u : ℝ => (p : ℝ) * Q u ^ (2 * (p - 1)) * (2 * Q u * Q u) :=
    (continuous_const.mul (hQc.pow _)).mul ((continuous_const.mul hQc).mul hQc)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨C, fun u hu M => le_trans (hpt u hu M) ?_⟩
  exact le_trans (le_abs_self _) (hC u hu)

/-! ### `contT`: `∂_1 Ψ(u, ·)` is continuous in the matrix

`RBM.Gauss.hasDerivAt_momentObsT` gives `∂_1 Ψ` in *closed form*, so its continuity in the
matrix is the continuity of the loop observable and of its `z`-motion, both of which are
finite combinations of `RBM.Gauss.loopObs`. -/

theorem continuous_loopObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) : Continuous (loopObs d N z I) :=
  (bddC2_loopObs hz hη hzη hwf).contDiff.continuous

theorem continuous_zMotion_hermCLM {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) (Ev : ℝ) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) z I := by
  simp only [zMotion]
  refine continuous_finsetSum _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun b _ => ?_))
  exact continuous_loopObs hz hη hzη
    (LoopIdx.WF.cutGlue (b := b) (k := k + 1) hwf (by omega) (by omega))

theorem continuous_ukerObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0) (hzη : η ≤ |(zt Ev u).im|) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ => ukerObsT d N Ev σ ξ t K a u M := by
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  simp only [ukerObsT, ukerObs, Uker]
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_const.mul ((continuous_loopObs hz hη hzη (hwf b)).sub continuous_const)

theorem continuous_ukerObsTDeriv (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0) (hzη : η ≤ |(zt Ev u).im|) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ukerObsTDeriv d N Ev σ ξ t K K' a u M := by
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  simp only [ukerObsTDeriv]
  refine continuous_finsetSum _ fun b _ => ?_
  refine Continuous.add ?_ ?_
  · exact continuous_const.mul ((continuous_loopObs hz hη hzη (hwf b)).sub continuous_const)
  · exact continuous_const.mul
      ((continuous_zMotion_hermCLM hz hη hzη Ev (hwf b)).sub continuous_const)

/-- `∂_1 Ψ` in closed form. -/
theorem timeD1_momentObsT_eq (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    timeD1 (momentObsT d N Ev σ ξ t K a p) u M
      = (p : ℂ) * (ukerObsT d N Ev σ ξ t K a u M
            * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)) ^ (p - 1)
        * (ukerObsTDeriv d N Ev σ ξ t K K' a u M
              * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)
            + ukerObsT d N Ev σ ξ t K a u M
              * (starRingEnd ℂ) (ukerObsTDeriv d N Ev σ ξ t K K' a u M)) :=
  timeD1_eq_of_hasDerivAt (hasDerivAt_momentObsT Ev hσ ξ t K K' a p hz hK M)

/-- **The field `RBM.Gauss.TestFunT₁.contT` for the moment route's `Ψ`.** -/
theorem continuous_timeD1_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hzη : η ≤ |(zt Ev u).im|)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      timeD1 (momentObsT d N Ev σ ξ t K a p) u M := by
  have hfun : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      timeD1 (momentObsT d N Ev σ ξ t K a p) u M)
      = fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        (p : ℂ) * (ukerObsT d N Ev σ ξ t K a u M
              * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)) ^ (p - 1)
          * (ukerObsTDeriv d N Ev σ ξ t K K' a u M
                * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)
              + ukerObsT d N Ev σ ξ t K a u M
                * (starRingEnd ℂ) (ukerObsTDeriv d N Ev σ ξ t K K' a u M)) :=
    funext fun M => timeD1_momentObsT_eq Ev hσ ξ t K K' a p hz hK M
  rw [hfun]
  have hA : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ukerObsT d N Ev σ ξ t K a u M := continuous_ukerObsT Ev hσ ξ t K a hη hz hzη
  have hD : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ukerObsTDeriv d N Ev σ ξ t K K' a u M :=
    continuous_ukerObsTDeriv Ev hσ ξ t K K' a hη hz hzη
  have hAc : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M) := Complex.continuous_conj.comp hA
  have hDc : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (starRingEnd ℂ) (ukerObsTDeriv d N Ev σ ξ t K K' a u M) := Complex.continuous_conj.comp hD
  exact (continuous_const.mul ((hA.mul hAc).pow _)).mul ((hD.mul hAc).add (hA.mul hDc))

/-! ### The two fields that come from T133 -/

/-- Each time slice of `Ψ` is T133's test function, verbatim. -/
theorem momentObsT_apply (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    (u : ℝ) :
    momentObsT d N Ev σ ξ t K a p u
      = momentFun (ukerObs d N (zt Ev u) σ ξ (u : ℂ) t (K u) a) p := by
  funext M
  simp only [momentObsT, momentFun, ukerObsT]

/-- **The field `RBM.Gauss.TestFunT₁.contDiffM`**: T133's `testFun_momentFun_ukerObs`. -/
theorem contDiff_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    {η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0) (hzη : η ≤ |(zt Ev u).im|) :
    ContDiff ℝ 2 (momentObsT d N Ev σ ξ t K a p u) := by
  rw [momentObsT_apply]
  exact (testFun_momentFun_ukerObs hz hη hzη hσ ξ (u : ℂ) t (K u) a p).contDiff

/-- **The field `RBM.Gauss.TestFunT₁.bdd₀`**, uniform over the window: the same compactness
argument as `RBM.Gauss.bddT_momentObsT`, applied to the value rather than to the derivative.
(T133's `bdd₀` is per-`u`; the class asks for uniformity.) -/
theorem bdd₀_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖momentObsT d N Ev σ ξ t K a p u M‖ ≤ C := by
  classical
  set Cloop : ℝ := η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) with hCloop
  set C₀ : ℝ := Cloop + cK with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hlen : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).a.length = m := fun b => by
    show (List.ofFn b).length = m
    rw [List.length_ofFn]
  set Q : ℝ → ℝ := fun u => ukerCoefBd ξ t a u * C₀ with hQ
  have hQ0 : ∀ u, 0 ≤ Q u := fun u => mul_nonneg (ukerCoefBd_nonneg ξ t a u) hC₀0
  have hpt : ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖momentObsT d N Ev σ ξ t K a p u M‖ ≤ Q u ^ (2 * p) := by
    intro u hu M
    have hval : ∀ b : LoopArg (d.L N) m,
        ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C₀ := by
      intro b
      have h : ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ ≤ Cloop := by
        have h0 := norm_loopObs_le hη (hzim u hu) _ (hwf b) (by rw [hlen b]; exact hm) M
        rw [hlen b] at h0
        exact h0
      calc ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖
          ≤ ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ + ‖K u b‖ := norm_sub_le _ _
        _ ≤ Cloop + cK := add_le_add h (hKb u hu b)
    have hA : ‖ukerObsT d N Ev σ ξ t K a u M‖ ≤ Q u :=
      norm_ukerObsT_le Ev σ ξ t K a u M hC₀0 hval
    rw [momentObsT_eq, norm_pow, norm_mul, RCLike.norm_conj, ← sq, ← pow_mul, mul_comm 2 p]
    exact pow_le_pow_left₀ (norm_nonneg _) hA _
  have hQc : Continuous Q := (continuous_ukerCoefBd ξ t a).mul continuous_const
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn
    (f := fun u => Q u ^ (2 * p)) (hQc.pow _).continuousOn
  exact ⟨C, fun u hu M => le_trans (hpt u hu M) (le_trans (le_abs_self _) (hC u hu))⟩

/-! ### `diffJoint`: joint regularity in `(time, matrix)`

This is T191's second missing item.  `RBM.Gauss.contDiffAt_resH_path` already has the
resolvent jointly `C²` along a `C²` path of spectral parameters; what was missing is the
induction over the `n` factors of (2.41) **in the pair variable**, the pair version of
`RBM.EGDef.contDiffAt_gloopProd_matrix`.  Since `RBM.Gauss.loopObs` carries
`RBM.Gauss.hermCLM`, the statement holds at *every* matrix, with no Hermitian side condition
— which is what the class asks for. -/

/-- `(u, M) ↦ G(σ)(hermCLM M, z_u)` is jointly `C²`. -/
theorem contDiffAt_Gsig_zt_pair (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0) (σ : Bool)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Gsig (hermCLM (d.Idx N) q.2) (zt Ev q.1) σ) (u, M) := by
  have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Gsig (hermCLM (d.Idx N) q.2) (zt Ev q.1) σ)
      = fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        resH ((Ev : ℂ) + (1 - (q.1 : ℂ)) * mSigma Ev σ) q.2 := by
    funext q
    rw [Gsig_zt, resH_eq_green]
  rw [hfun]
  refine contDiffAt_resH_path (z := fun s : ℝ => (Ev : ℂ) + (1 - (s : ℂ)) * mSigma Ev σ)
    ?_ (ztSig_im_ne_zero hz σ) M
  exact (contDiff_const.add
    ((contDiff_const.sub Complex.ofRealCLM.contDiff).mul contDiff_const)).contDiffAt

/-- **The pair version of `RBM.EGDef.contDiffAt_gloopProd_matrix`.** -/
theorem contDiffAt_gloopProd_zt_pair (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∀ (σ : List Bool) (a : List (ZMod (d.L N))),
      ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1) ⟨σ, a⟩) (u, M) := by
  intro σ
  induction σ with
  | nil => intro a; exact contDiffAt_const
  | cons σ₀ σ ih =>
      intro a
      cases a with
      | nil => exact contDiffAt_const
      | cons c a' =>
          have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
              gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1)
                (⟨σ₀ :: σ, c :: a'⟩ : LoopIdx (ZMod (d.L N))))
              = fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
                Gsig (hermCLM (d.Idx N) q.2) (zt Ev q.1) σ₀ * Eblk (d.L N) (d.W N) c
                  * gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1)
                      ⟨σ, a'⟩ := rfl
          rw [hfun]
          exact ((contDiffAt_Gsig_zt_pair Ev hz σ₀ M).mul contDiffAt_const).mul (ih a')

/-- **`(u, M) ↦ L_{σ,a}(z_u, M)` is jointly `C²`**, at every matrix. -/
theorem contDiffAt_loopObs_zt_pair (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      loopObs d N (zt Ev q.1) I q.2) (u, M) := by
  set T : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (d.Idx N) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => loopObs d N (zt Ev q.1) I q.2)
      = T ∘ fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
          gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1) I := rfl
  rw [hfun]
  exact (T.contDiff (n := 2)).contDiffAt.comp (u, M)
    (contDiffAt_gloopProd_zt_pair Ev hz M I.σ I.a)

/-- A function of the time alone is jointly differentiable. -/
theorem differentiableAt_pair_fst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → ℂ} {u : ℝ} {M : F} (h : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun q : ℝ × F => f q.1) (u, M) :=
  h.comp (u, M) (differentiableAt_fst : DifferentiableAt ℝ (fun q : ℝ × F => q.1) (u, M))

/-- **The field `RBM.Gauss.TestFunT₁.diffJoint` for the inner observable.**  Only first order
is needed, which is why the `u`-dependence of `RBM.edgeKer` and of `K` enters through
`HasDerivAt` alone. -/
theorem differentiableAt_ukerObsT_pair (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, DifferentiableAt ℝ (fun r : ℝ => K r b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      ukerObsT d N Ev σ ξ t K a q.1 q.2) (u, M) := by
  simp only [ukerObsT, ukerObs, Uker]
  refine DifferentiableAt.fun_sum fun b _ => ?_
  have h1 : DifferentiableAt ℝ
      (fun r : ℝ => ∏ i : Fin m, edgeKer (d.L N) (ξ i) (r : ℂ) t (a i) (b i)) u :=
    (HasDerivAt.fun_finsetProd
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
        hasDerivAt_edgeKer (d.L N) (ξ i) t (a i) (b i) u)).differentiableAt
  have hE : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      ∏ i : Fin m, edgeKer (d.L N) (ξ i) (q.1 : ℂ) t (a i) (b i)) (u, M) :=
    differentiableAt_pair_fst h1
  have hL : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      loopObs d N (zt Ev q.1) ⟨σ, List.ofFn b⟩ q.2) (u, M) :=
    (contDiffAt_loopObs_zt_pair Ev hz _ M).differentiableAt (by norm_num)
  have hKq : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => K q.1 b) (u, M) :=
    differentiableAt_pair_fst (hK b)
  exact hE.mul (hL.sub hKq)

/-- **The field `RBM.Gauss.TestFunT₁.diffJoint` for `Ψ = |·|^{2p}`.** -/
theorem differentiableAt_momentObsT_pair (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, DifferentiableAt ℝ (fun r : ℝ => K r b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      momentObsT d N Ev σ ξ t K a p q.1 q.2) (u, M) := by
  have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      momentObsT d N Ev σ ξ t K a p q.1 q.2)
      = fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (ukerObsT d N Ev σ ξ t K a q.1 q.2
          * (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a q.1 q.2)) ^ p :=
    funext fun q => momentObsT_eq Ev σ ξ t K a p q.1 q.2
  rw [hfun]
  have hA : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      ukerObsT d N Ev σ ξ t K a q.1 q.2) (u, M) :=
    differentiableAt_ukerObsT_pair Ev ξ t K a hz hK M
  have hAc : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a q.1 q.2)) (u, M) := by
    have h2 : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a q.1 q.2))
        = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap ∘
          fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
            ukerObsT d N Ev σ ξ t K a q.1 q.2 := rfl
    rw [h2]
    exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.differentiableAt.comp (u, M) hA
  exact (hA.mul hAc).pow p

/-! ### `bdd₀`, `bdd₁`, `bdd₂`, *uniformly over the window*

T133's `RBM.Gauss.testFun_momentFun_ukerObs` gives the three matrix bounds at a **fixed** `u`;
the class asks for them uniformly over the window.  The route is `RBM.Gauss.BddC2C`, which
carries its constants explicitly: the loop's constants depend on `u` only through
`η ≤ |Im z_u|`, so the only `u`-dependence left is the propagator's row `ℓ¹` size
`RBM.Gauss.ukerRow`, a continuous function of `u` alone, which the compact window bounds.

The last step, `|·|^{2p}`, needs `RBM.Gauss.BddC2C` to be closed under products and under
`p`-th powers with *named* constants; `RBM.Gauss.bddC2_momentFun` is stated with existential
ones, and existentials cannot be pulled out of the `u`-quantifier. -/

/-- Products, for `ℂ`-valued functions. -/
theorem bddC2C_mul_cx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G : E → ℂ}
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (hF : BddC2C F a₀ a₁ a₂) (hG : BddC2C G b₀ b₁ b₂) :
    BddC2C (fun M => F M * G M) (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) := by
  have hF' : BddC2C (fun M => (ContinuousLinearMap.mul ℝ ℂ) (F M)) a₀ a₁ a₂ := by
    refine (bddC2C_clm_comp (ContinuousLinearMap.mul ℝ ℂ) hF).mono ?_ ?_ ?_ <;>
      nlinarith [hF.nonneg₀, hF.nonneg₁, hF.nonneg₂,
        norm_nonneg (ContinuousLinearMap.mul ℝ ℂ), ContinuousLinearMap.opNorm_mul_le ℝ ℂ]
  exact bddC2C_clm_apply hF' hG

/-- Conjugation is an isometry, so it changes no constant. -/
theorem bddC2C_conj_cx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℂ}
    {a₀ a₁ a₂ : ℝ} (hF : BddC2C F a₀ a₁ a₂) :
    BddC2C (fun M => (starRingEnd ℂ) (F M)) a₀ a₁ a₂ := by
  have hc : ‖(Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp
  refine (bddC2C_clm_comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap hF).mono
    ?_ ?_ ?_ <;>
    nlinarith [hF.nonneg₀, hF.nonneg₁, hF.nonneg₂, hc,
      norm_nonneg (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap]

/-- Multiplication by a constant. -/
theorem bddC2C_const_mul_cx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℂ}
    {a₀ a₁ a₂ : ℝ} (c : ℂ) (hF : BddC2C F a₀ a₁ a₂) :
    BddC2C (fun M => c * F M) (‖c‖ * a₀) (‖c‖ * a₁) (‖c‖ * a₂) := by
  refine (bddC2C_mul_cx (bddC2C_const (E := E) c) hF).mono ?_ ?_ ?_ <;>
    nlinarith [hF.nonneg₀, hF.nonneg₁, hF.nonneg₂, norm_nonneg c]

/-- Powers, with the constants existentially quantified **but independent of the function**:
this is what lets the same constant serve every `u` in the window. -/
theorem exists_bddC2C_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c₀ c₁ c₂ : ℝ) (p : ℕ) :
    ∃ D₀ D₁ D₂ : ℝ, ∀ G : E → ℂ, BddC2C G c₀ c₁ c₂ → BddC2C (fun M => G M ^ p) D₀ D₁ D₂ := by
  induction p with
  | zero => exact ⟨1, 0, 0, fun G _ => by simpa using bddC2C_const (E := E) (1 : ℂ)⟩
  | succ p ih =>
      obtain ⟨D₀, D₁, D₂, hD⟩ := ih
      refine ⟨c₀ * D₀, c₀ * D₁ + c₁ * D₀, c₀ * D₂ + 2 * (c₁ * D₁) + c₂ * D₀, fun G hG => ?_⟩
      have hfun : (fun M => G M ^ (p + 1)) = fun M => G M * G M ^ p := by
        funext M
        rw [pow_succ']
      rw [hfun]
      exact bddC2C_mul_cx hG (hD G hG)

/-- `RBM.Gauss.bddC2_momentFun` with constants that do not depend on `F`. -/
theorem exists_bddC2C_momentFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c₀ c₁ c₂ : ℝ) (p : ℕ) :
    ∃ D₀ D₁ D₂ : ℝ, ∀ F : E → ℂ, BddC2C F c₀ c₁ c₂ → BddC2C (momentFun F p) D₀ D₁ D₂ := by
  obtain ⟨D₀, D₁, D₂, hD⟩ := exists_bddC2C_pow (E := E)
    (c₀ * c₀) (c₀ * c₁ + c₁ * c₀) (c₀ * c₂ + 2 * (c₁ * c₁) + c₂ * c₀) p
  exact ⟨D₀, D₁, D₂, fun F hF => hD _ (bddC2C_mul_cx hF (bddC2C_conj_cx hF))⟩

/-- The `ℓ¹` size of the propagator's row — the only `u`-dependent constant left. -/
noncomputable def ukerRow {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) : ℝ :=
  ∑ b : LoopArg L n, ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)‖

theorem ukerRow_nonneg {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) : 0 ≤ ukerRow ξ t a u :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_ukerRow {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) : Continuous (ukerRow ξ t a) :=
  continuous_finsetSum _ fun _ _ =>
    Continuous.norm (continuous_finsetProd _ fun _ _ => continuous_edgeKer_time _ _ _ _)

/-- **`RBM.Gauss.BddC2C` for `(U_{u,v} ∘ (L - K)_u)_a` with named constants.** -/
theorem bddC2C_ukerObsT {Ev : ℝ} {η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hzη : η ≤ |(zt Ev u).im|) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {cK : ℝ} (hK : ∀ b, ‖K u b‖ ≤ cK) :
    BddC2C (ukerObsT d N Ev σ ξ t K a u)
      (ukerRow ξ t a u * ((Fintype.card (d.Idx N) : ℝ) * (2 * (1 + η⁻¹) ^ 3) ^ m + cK))
      (ukerRow ξ t a u
        * ((Fintype.card (d.Idx N) : ℝ) * ((m : ℝ) * (2 * (1 + η⁻¹) ^ 3) ^ m)))
      (ukerRow ξ t a u
        * ((Fintype.card (d.Idx N) : ℝ) * ((m : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ m))) := by
  classical
  obtain ⟨hB1, hB2, hB3⟩ := le_two_mul_one_add_inv_cube hη
  set B : ℝ := 2 * (1 + η⁻¹) ^ 3 with hB
  set Cd : ℝ := (Fintype.card (d.Idx N) : ℝ) with hCd
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hP : ∀ b : LoopArg (d.L N) m, (0 : ℝ)
      ≤ ‖∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)‖ := fun b => norm_nonneg _
  have hfun : ukerObsT d N Ev σ ξ t K a u
      = fun M => ∑ b : LoopArg (d.L N) m,
          ((∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i))
              * loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M
            + -((∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)) * K u b)) := by
    funext M
    simp only [ukerObsT, ukerObs, Uker]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hfun]
  have hterm : ∀ b : LoopArg (d.L N) m, BddC2C
      (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        (∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i))
            * loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M
          + -((∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)) * K u b))
      (‖∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)‖ * (Cd * B ^ m + cK))
      (‖∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)‖ * (Cd * ((m : ℝ) * B ^ m)))
      (‖∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)‖
        * (Cd * ((m : ℝ) ^ 2 * B ^ m))) := by
    intro b
    have hloop0 := bddC2C_loopObs (d := d) (N := N) (B := B) hz hη hzη hB1 hB2 hB3 (hwf b)
    have hlen : (LoopIdx.mk σ (List.ofFn b)).a.length = m := by
      show (List.ofFn b).length = m
      rw [List.length_ofFn]
    rw [hlen] at hloop0
    have hmul := bddC2C_const_mul_cx
      (∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)) hloop0
    have hsum := bddC2C_add hmul (bddC2C_const (E := Matrix (d.Idx N) (d.Idx N) ℂ)
      (-((∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)) * K u b)))
    refine hsum.mono ?_ ?_ ?_
    · have hk : ‖-((∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)) * K u b)‖
          ≤ ‖∏ i : Fin m, edgeKer (d.L N) (ξ i) (u : ℂ) t (a i) (b i)‖ * cK := by
        rw [norm_neg, norm_mul]
        exact mul_le_mul_of_nonneg_left (hK b) (hP b)
      nlinarith [hP b, hk]
    · simp [hCd]
    · simp [hCd]
  have hbig := bddC2C_sum (Finset.univ : Finset (LoopArg (d.L N) m)) fun b _ => hterm b
  rw [ukerRow, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  exact hbig

/-- **`bdd₀`, `bdd₁`, `bdd₂` and `contDiffM`, all four uniform over the window.** -/
theorem exists_bddC2C_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK) :
    ∃ D₀ D₁ D₂ : ℝ, ∀ u ∈ Set.Icc u₀ u₁,
      BddC2C (momentObsT d N Ev σ ξ t K a p u) D₀ D₁ D₂ := by
  classical
  set B : ℝ := 2 * (1 + η⁻¹) ^ 3 with hB
  set Cd : ℝ := (Fintype.card (d.Idx N) : ℝ) with hCd
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn
    (f := ukerRow ξ t a) (continuous_ukerRow ξ t a).continuousOn
  have hRle : ∀ u ∈ Set.Icc u₀ u₁, ukerRow ξ t a u ≤ R := fun u hu =>
    le_trans (le_abs_self _) (hR u hu)
  obtain ⟨D₀, D₁, D₂, hD⟩ := exists_bddC2C_momentFun
    (E := Matrix (d.Idx N) (d.Idx N) ℂ)
    (R * (Cd * B ^ m + cK)) (R * (Cd * ((m : ℝ) * B ^ m)))
    (R * (Cd * ((m : ℝ) ^ 2 * B ^ m))) p
  refine ⟨D₀, D₁, D₂, fun u hu => ?_⟩
  have hz : (zt Ev u).im ≠ 0 := by
    have hlt := lt_of_lt_of_le hη (hzim u hu)
    exact fun h => by simp [h] at hlt
  have hcK : 0 ≤ cK := le_trans (norm_nonneg _) (hKb u hu (fun _ => 0))
  have hB0 : (0 : ℝ) < B := by positivity
  have hbase := bddC2C_ukerObsT (d := d) (N := N) hη hz (hzim u hu) hσ ξ t K a
    (fun b => hKb u hu b)
  have hmono : BddC2C (ukerObsT d N Ev σ ξ t K a u) (R * (Cd * B ^ m + cK))
      (R * (Cd * ((m : ℝ) * B ^ m))) (R * (Cd * ((m : ℝ) ^ 2 * B ^ m))) := by
    have hCd0 : (0 : ℝ) ≤ Cd := Nat.cast_nonneg _
    have hBm : (0 : ℝ) ≤ B ^ m := by positivity
    refine hbase.mono ?_ ?_ ?_ <;>
      exact mul_le_mul_of_nonneg_right (hRle u hu) (by positivity)
  have hfin := hD _ hmono
  have heq : momentObsT d N Ev σ ξ t K a p u
      = momentFun (ukerObsT d N Ev σ ξ t K a u) p := rfl
  rw [heq]
  exact hfin

/-! ### The class itself -/

/-- `Im z_u ≠ 0` from a uniform lower bound. -/
theorem im_zt_ne_zero_of_le {Ev η u : ℝ} (hη : 0 < η) (h : η ≤ |(zt Ev u).im|) :
    (zt Ev u).im ≠ 0 := by
  have hlt := lt_of_lt_of_le hη h
  exact fun h0 => by simp [h0] at hlt

/-- **`RBM.Gauss.TestFunT₁` for the moment route's `Ψ`, all seven fields.**

`Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}` is admissible on the window `[u₀, u₁]` provided
only that the spectral parameter stays off the real axis there (`hzim`, which is
`RBM.le_zt_im` on the paper's window) and that the primitive `K` is differentiable in `u` with
`K` and `∂_u K` bounded (`hK`, `hKb`, `hK'b` — no matrix and no resolvent occur in them).

T191's four outstanding items are the fields `contDiffM`, `diffJoint`, `contT`, `bddT`; the
three uniform bounds `bdd₀`, `bdd₁`, `bdd₂` come with `contDiffM` from
`RBM.Gauss.exists_bddC2C_momentObsT`. -/
theorem testFunT₁_momentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    TestFunT₁ d N (Set.Icc u₀ u₁) (momentObsT d N Ev σ ξ t K a p) := by
  obtain ⟨D₀, D₁, D₂, hD⟩ := exists_bddC2C_momentObsT Ev hσ ξ t K a p hη hzim hKb
  refine ⟨fun u hu => (hD u hu).contDiff, ?_, ?_,
    ⟨D₀, fun u hu M => (hD u hu).bdd₀ M⟩,
    ⟨D₁, fun u hu M => (hD u hu).bdd₁ M⟩,
    ⟨D₂, fun u hu M => (hD u hu).bdd₂ M⟩,
    bddT_momentObsT Ev hσ hm ξ t K K' a p hη hcK hzim hK hKb hK'b⟩
  · intro u hu M
    exact differentiableAt_momentObsT_pair Ev ξ t K a p
      (im_zt_ne_zero_of_le hη (hzim u hu)) (fun b => (hK u hu b).differentiableAt) M
  · intro u hu
    exact continuous_timeD1_momentObsT Ev hσ ξ t K K' a p hη
      (im_zt_ne_zero_of_le hη (hzim u hu)) (hzim u hu) (fun b => hK u hu b)

/-- **The generator identity at the moment route's `Ψ`, with no hypothesis left on `Ψ`.**

This is T191's `φ'`-existence slot: `RBM.Gauss.hasDerivAt_integral_Psi_pairs₁` consumed by
`RBM.Gauss.testFunT₁_momentObsT`.  What remains of T191's programme after it is the
*identification* of this right-hand side — cancelling `∫ ∂₁Ψ` against the `genS` term through
`RBM.MomentDuhamel.Hyp.drift`, the second-order term through `RBM.Gauss.genMomentPt_le'`, and
its quadratic variation through `RBM.Gauss.quadVarPairs_Uker` — together with the interval
integrability side conditions.  None of that is done here. -/
theorem hasDerivAt_integral_momentObsT (hst : MatrixStein d) (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (hσ : σ.length = m) (hm : 1 ≤ m) (ξ : Fin m → ℂ) (t : ℂ)
    (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK)
    {u : ℝ} (hu : 0 < u) (hlo : u₀ < u) (hhi : u < u₁) :
    HasDerivAt (fun s : ℝ => ∫ ω, momentObsT d N Ev σ ξ t K a p s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 (momentObsT d N Ev σ ξ t K a p) u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (momentObsT d N Ev σ ξ t K a p u)
            (Hflow d N u ω) i j ∂(P d)) u :=
  hasDerivAt_integral_Psi_pairs₁ hst
    (testFunT₁_momentObsT Ev hσ hm ξ t K K' a p hη hcK hzim hK hKb hK'b) hu
    (Icc_mem_nhds hlo hhi)

/-! ### Satisfiability

Three checks, all compiled.  The first shows the hypotheses are not vacuous — they are
discharged from the paper's standing assumptions with no free data.  The other two are the
check T180's incident makes mandatory: the field `bddT` quantifies over **all** matrices, so
the bound has to be tested at a non-Hermitian matrix at which the *raw* resolvent degenerates.
It survives there for one reason only, that `RBM.Gauss.loopObs` factors through
`RBM.Gauss.hermCLM`. -/

/-- On a window ending strictly before `1` the spectral parameter stays off the real axis,
with the explicit `η = (1 - u₁) Im m_E`.  This is what discharges `hzim`. -/
theorem le_abs_im_zt_of_le {Ev : ℝ} (hE : |Ev| < 2) {u₁ : ℝ} (hu₁ : u₁ < 1) {u : ℝ}
    (hu : u ≤ u₁) : (1 - u₁) * (mE Ev).im ≤ |(zt Ev u).im| := by
  have hm := mE_im_pos hE
  have h1 : (0 : ℝ) < 1 - u₁ := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  have hzu : (zt Ev u).im = (1 - u) * (mE Ev).im := zt_im Ev u
  have hpos : 0 < (zt Ev u).im := by rw [hzu]; positivity
  rw [abs_of_pos hpos, hzu]
  exact mul_le_mul_of_nonneg_right (by linarith) hm.le

/-- **Check 1: the class is inhabited with no free data.**  With `K = 0` every hypothesis of
`RBM.Gauss.testFunT₁_momentObsT` is discharged from `|E| < 2` and `u₁ < 1` alone. -/
theorem testFunT₁_momentObsT_zero {Ev : ℝ} (hE : |Ev| < 2) {σ : List Bool} {m : ℕ}
    (hσ : σ.length = m) (hm : 1 ≤ m) (ξ : Fin m → ℂ) (t : ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    {u₀ u₁ : ℝ} (hu₁ : u₁ < 1) :
    TestFunT₁ d N (Set.Icc u₀ u₁)
      (momentObsT d N Ev σ ξ t (fun _ _ => 0) a p) := by
  have hηpos : 0 < (1 - u₁) * (mE Ev).im := by
    have := mE_im_pos hE
    have h1 : (0 : ℝ) < 1 - u₁ := by linarith
    positivity
  exact testFunT₁_momentObsT Ev hσ hm ξ t (fun _ _ => 0) (fun _ _ => 0) a p
    (η := (1 - u₁) * (mE Ev).im) (cK := 0) hηpos le_rfl
    (fun u hu => le_abs_im_zt_of_le hE hu₁ hu.2)
    (fun u _ b => hasDerivAt_const u 0)
    (fun u _ b => by simp) (fun u _ b => by simp)

/-- **A non-Hermitian matrix at which the raw resolvent degenerates.**  `M = z + S` with `S`
a single off-diagonal `1`: `M - z` is singular, so `RBM.green M z = 0` — the raw object
carries no information at all there, and no envelope `‖G‖ ≤ η⁻¹` is being used. -/
theorem exists_not_isHermitian_green_eq_zero (d : Dims) (N : ℕ) (z : ℂ) :
    ∃ M : Matrix (d.Idx N) (d.Idx N) ℂ, ¬ M.IsHermitian ∧ green M z = 0 := by
  classical
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hfact : Fact (1 < d.L N) := ⟨by omega⟩
  have hW : 0 < d.W N := d.W_pos N
  set i : d.Idx N := ((0 : ZMod (d.L N)), (⟨0, hW⟩ : Fin (d.W N))) with hi
  set j : d.Idx N := ((1 : ZMod (d.L N)), (⟨0, hW⟩ : Fin (d.W N))) with hj
  have hij : i ≠ j := by
    intro h
    exact (zero_ne_one (α := ZMod (d.L N))) (congrArg Prod.fst h)
  have hji : j ≠ i := fun h => hij h.symm
  set S : Matrix (d.Idx N) (d.Idx N) ℂ :=
    Matrix.of (fun x y => if x = i ∧ y = j then (1 : ℂ) else 0) with hS
  refine ⟨z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) + S, ?_, ?_⟩
  · intro hH
    have h := congrFun (congrFun hH i) j
    rw [Matrix.conjTranspose_apply] at h
    have hji0 : (z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) + S) j i = 0 := by
      simp [hS, Matrix.add_apply, Matrix.smul_apply, hji]
    have hij1 : (z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) + S) i j = 1 := by
      simp [hS, Matrix.add_apply, Matrix.smul_apply, hij]
    rw [hji0, hij1] at h
    simp at h
  · have hsub : z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) + S
        - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) = S := by
      abel
    have hdet : S.det = 0 := by
      refine Matrix.det_eq_zero_of_row_eq_zero j fun y => ?_
      simp [hS, hji]
    show (z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) + S
        - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))⁻¹ = 0
    rw [hsub]
    refine Matrix.nonsing_inv_apply_not_isUnit S ?_
    rw [hdet]
    simp

/-- **`Ψ` factors through the Hermitian projection.**  This is the reason the `∀ M` of
`RBM.Gauss.TestFunT₁` is harmless here, and the precise sense in which the bound is *not* a
statement about the raw resolvent. -/
theorem ukerObsT_hermCLM (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin m → ℂ) (t : ℂ)
    (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ukerObsT d N Ev σ ξ t K a u (hermCLM (d.Idx N) M)
      = ukerObsT d N Ev σ ξ t K a u M := by
  have hidem : hermCLM (d.Idx N) (hermCLM (d.Idx N) M) = hermCLM (d.Idx N) M :=
    hermCLM_of_isHermitian (isHermitian_hermCLM M)
  simp only [ukerObsT, ukerObs, Uker, loopObs, hidem]

/-- **Check 2 and 3: the uniform bound of `RBM.Gauss.bddT_momentObsT` really is evaluated at a
non-Hermitian matrix at which the raw resolvent has collapsed to `0`.**  So the `∀ M` is not a
disguised `∀ M, M.IsHermitian →`, and the statement is not vacuous there. -/
theorem bddT_momentObsT_at_singular (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (hm : 1 ≤ m) (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ)
    (a : LoopArg (d.L N) m) (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK)
    {v : ℝ} (hv : v ∈ Set.Icc u₀ u₁) :
    ∃ C : ℝ, ∃ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ¬ M.IsHermitian ∧ green M (zt Ev v) = 0
        ∧ ‖timeD1 (momentObsT d N Ev σ ξ t K a p) v M‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    bddT_momentObsT Ev hσ hm ξ t K K' a p hη hcK hzim hK hKb hK'b
  obtain ⟨M, hM, hg⟩ := exists_not_isHermitian_green_eq_zero d N (zt Ev v)
  exact ⟨C, M, hM, hg, hC v hv M⟩

end Gauss

end RBM


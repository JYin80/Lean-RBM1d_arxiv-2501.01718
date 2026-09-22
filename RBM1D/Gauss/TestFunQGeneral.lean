/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelQ

/-!
# `RBM.Gauss.TestFunT₁` for a deterministic coefficient family (T225)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2 and §5.5, equations (5.20), (5.91), (5.103).

T196 proved the seven fields of `RBM.Gauss.TestFunT₁` for `RBM.Gauss.momentObsT`, the plain
route's `Ψ = |(U_{u,v} ∘ (L-K)_u)_a|^{2p}`, and T214 asked for the same seven for the `Q_t`
route's `Ψ^Q = |(U_{u,v} ∘ Q_u (L-K)_u)_a|^{2p}`.  Writing them twice is unnecessary: by
`RBM.Gauss.qUkerObsT_eq_coefObsT`,

  `U_{u,v} ∘ Q_u A = ∑_b (ker(a,b) - w_u(b 0)) · A b`,  `w_u(x) = ∑_{b' : b'₀ = x} ker(a,b') ϑ_u(b')`,

so **both routes are the same object** — a finite linear combination of the loop observables
`(L - K)_u(b)` with *deterministic* coefficients — and the only thing that changes between
them is the coefficient family.  This file proves the seven fields once, for an arbitrary
family that is `C¹` in the time and bounded on the window, and then specialises.

## Main results

* `RBM.Gauss.coefObsT`, `RBM.Gauss.coefMomentObsT` — the class;
  `RBM.Gauss.ukerObsT_eq_coefObsT` (by `rfl`) and `RBM.Gauss.qUkerObsT_eq_coefObsT` show both
  routes are members.
* `RBM.Gauss.testFunT₁_coefMomentObsT` — **the seven fields**, for any `C¹` bounded family;
  `RBM.Gauss.hasDerivAt_integral_coefMomentObsT` — the generator identity at it, with no
  hypothesis left on `Ψ`.
* `RBM.Gauss.testFunT₁_momentObsT_of_coef` and its four siblings — T196's five lemmas, each
  derived in one line.  The five `example … := rfl` after them check that the derivations have
  **the same type** as the originals, so nothing was reshaped.
* `RBM.Gauss.testFunT₁_qMomentObsT`, `RBM.Gauss.hasDerivAt_integral_qMomentObsT` — the `Q_t`
  route, by instantiating at `RBM.Gauss.qCoefFam`.
* `RBM.Gauss.hasDerivAt_integral_psiQ_gauss` — **the derivative slot of
  `RBM.MomentDuhamel.momentIneqQ_of_derivBound`, discharged unconditionally**, with `φ'` the
  pinned `RBM.Gauss.phiCoefDeriv`.
* `RBM.Gauss.hbound_qMomentObsT_gauss`, `RBM.Gauss.hbound_qMomentObsT_gauss_one` — **the
  `hbound` slot**: `RBM.Gauss.phiCoefDeriv_eq_integral` identifies `φ'` with
  `∫ (∂_u + 𝓛)Ψ^Q`, T214's pointwise `RBM.Gauss.timeD1_add_genMomentPt_le_driftFQ_flow`
  bounds the integrand, and `RBM.Gauss.integral_le_holder_sum_of_bdd` integrates it.  What is
  carried is exactly T226's two items — see the section head before them, and the `cq` warning
  there (paper-delta `T225a`).

## Satisfiability

* the class is **not empty**: both routes are members, by theorems, not by fiat;
* the time regularity asked of the coefficient family is `C¹`, used **once**
  (`RBM.Gauss.hasDerivAt_coefObsT`).  `RBM.Gauss.testFunT₁_coefMomentObsT_kink` together with
  `RBM.Gauss.not_differentiableAt_kinkCoefFam'` shows the order is strict — asking `C²` would
  exclude a `Ψ` the theorem covers, which is T191's accident;
* no `∀ M` is a disguised `∀ M, M.IsHermitian → …`: `RBM.Gauss.loopObs` carries
  `RBM.Gauss.hermCLM`, exactly as T196 checked.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ}

/-- `Ψ₁(u, M) = ∑_b c_u(b) · (L_{σ,b}(z_u, M) − K_u(b))`. -/
noncomputable def coefObsT (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ∑ b : LoopArg (d.L N) m, c u b * (loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b)

/-- `Ψ(u, M) = |Ψ₁(u, M)|^{2p}`. -/
noncomputable def coefMomentObsT (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  fun u M => momentFun (coefObsT d N Ev σ c K u) p M

/-- The coefficient family of the plain route: the propagator's row. -/
noncomputable def ukerCoefFam {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (b : LoopArg L n) : ℂ :=
  ∏ i : Fin n, edgeKer L (ξ i) ((u : ℝ) : ℂ) t (a i) (b i)

/-- `Ψ₁` of the plain route is `RBM.Gauss.coefObsT` at `RBM.Gauss.ukerCoefFam`. -/
theorem ukerObsT_eq_coefObsT (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin m → ℂ) (t : ℂ)
    (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ukerObsT d N Ev σ ξ t K a u M = coefObsT d N Ev σ (ukerCoefFam ξ t a) K u M := rfl

theorem momentObsT_eq_coefMomentObsT (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin m → ℂ) (t : ℂ)
    (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ) :
    momentObsT d N Ev σ ξ t K a p = coefMomentObsT d N Ev σ (ukerCoefFam ξ t a) K p := rfl

/-! ### The `Q_t` route is the same class

`U_{u,v} ∘ Q_u A = ∑_b (ker(a,b) − w_u(b₀)) A b` with `w_u(x) = ∑_{b' : b'₀ = x} ker(a,b') ϑ_u(b')`
— `Q_u` is a deterministic linear operator on the tensor slot, so composing it with the
propagator only changes the coefficient family. -/

/-- The re-indexing behind `RBM.Gauss.qUkerObsT_eq_coefObsT`: the `RBM.Psum` inside `RBM.Qop`
is summed against the propagator row by the bijection `(x, q) ↦ Fin.cons x q`. -/
theorem sum_ker_Psum_vartheta {L : ℕ} [NeZero L] {n : ℕ} (ker : LoopArg L (n + 1) → ℂ)
    (r : ℂ) (A : LoopArg L (n + 1) → ℂ) :
    ∑ b : LoopArg L (n + 1), ker b * (Psum L A (b 0) * vartheta L r b)
      = ∑ b : LoopArg L (n + 1),
          (∑ q : LoopArg L n, ker (Fin.cons (b 0) q) * vartheta L r (Fin.cons (b 0) q))
            * A b := by
  classical
  rw [SumZeroDyn.sum_loopArg_succ, SumZeroDyn.sum_loopArg_succ]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Fin.cons_zero]
  have hl : ∑ q : LoopArg L n, ker (Fin.cons x q) * (Psum L A x * vartheta L r (Fin.cons x q))
      = (∑ q : LoopArg L n, ker (Fin.cons x q) * vartheta L r (Fin.cons x q))
          * Psum L A x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hr : ∑ q : LoopArg L n,
        (∑ q' : LoopArg L n, ker (Fin.cons x q') * vartheta L r (Fin.cons x q'))
          * A (Fin.cons x q)
      = (∑ q' : LoopArg L n, ker (Fin.cons x q') * vartheta L r (Fin.cons x q'))
          * Psum L A x := by
    rw [← Finset.mul_sum]
    rfl
  rw [hl, hr]

/-- `w_u(x) = ∑_{b' : b'₀ = x} ker(a, b') ϑ_u(b')`, the weight `Q_u` adds to the propagator
row.  (The fibre `{b' : b'₀ = x}` is written as a sum over the tail.) -/
noncomputable def qWeight {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ)
    (a : LoopArg L (n + 1)) (u : ℝ) (x : ZMod L) : ℂ :=
  ∑ q : LoopArg L n,
    ukerCoefFam ξ t a u (Fin.cons x q) * vartheta L ((u : ℝ) : ℂ) (Fin.cons x q)

/-- The coefficient family of the `Q_t` route: `ker(a, b) − w_u(b₀)`. -/
noncomputable def qCoefFam {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ)
    (a : LoopArg L (n + 1)) (u : ℝ) (b : LoopArg L (n + 1)) : ℂ :=
  ukerCoefFam ξ t a u b - qWeight ξ t a u (b 0)

/-- **`Ψ^Q₁` is `RBM.Gauss.coefObsT` at `RBM.Gauss.qCoefFam`** — the two routes differ only in
the deterministic coefficient family. -/
theorem qUkerObsT_eq_coefObsT (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin (m + 1) → ℂ) (t : ℂ)
    (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ) (a : LoopArg (d.L N) (m + 1)) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    qUkerObsT d N Ev σ ξ t K a u M = coefObsT d N Ev σ (qCoefFam ξ t a) K u M := by
  classical
  set A : LoopArg (d.L N) (m + 1) → ℂ :=
    fun b => loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b with hA
  have hL : qUkerObsT d N Ev σ ξ t K a u M
      = ∑ b : LoopArg (d.L N) (m + 1), ukerCoefFam ξ t a u b * A b
        - ∑ b : LoopArg (d.L N) (m + 1),
            ukerCoefFam ξ t a u b * (Psum (d.L N) A (b 0) * vartheta (d.L N) ((u : ℝ) : ℂ) b) := by
    show Uker (d.L N) ξ ((u : ℝ) : ℂ) t (Qop (d.L N) ((u : ℝ) : ℂ) A) a = _
    rw [Uker_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      simp only [Qop, ukerCoefFam]
      ring
  rw [hL, sum_ker_Psum_vartheta, coefObsT, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by
    simp only [qCoefFam, qWeight]
    ring

theorem qMomentObsT_eq_coefMomentObsT (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin (m + 1) → ℂ)
    (t : ℂ) (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ) (a : LoopArg (d.L N) (m + 1)) (p : ℕ) :
    qMomentObsT d N Ev σ ξ t K a p = coefMomentObsT d N Ev σ (qCoefFam ξ t a) K p := by
  funext u M
  simp only [qMomentObsT, coefMomentObsT, momentFun]
  rw [qUkerObsT_eq_coefObsT]

/-! ### The derivative in the time, and the two bounds it needs -/

/-- `∂_u Ψ₁`: the coefficient family moves, and so does `(L − K)_u` (through the spectral
parameter `z_u` and through the primitive). -/
noncomputable def coefObsTDeriv (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ∑ b : LoopArg (d.L N) m,
    (c' u b * (loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b)
      + c u b * (zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
          ⟨σ, List.ofFn b⟩ - K' u b))

theorem wf_of_length {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (b : LoopArg (d.L N) m) : (LoopIdx.mk σ (List.ofFn b)).WF := by
  show σ.length = (List.ofFn b).length
  rw [hσ, List.length_ofFn]

theorem len_of_length {σ : List Bool} {m : ℕ} (b : LoopArg (d.L N) m) :
    (LoopIdx.mk σ (List.ofFn b)).a.length = m := by
  show (List.ofFn b).length = m
  rw [List.length_ofFn]

/-- **`∂_u Ψ₁` exists** as soon as the coefficient family and the primitive are differentiable
in `u` — first order only, which is all `RBM.Gauss.TestFunT₁` asks for. -/
theorem hasDerivAt_coefObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hc : ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    HasDerivAt (fun s : ℝ => coefObsT d N Ev σ c K s M)
      (coefObsTDeriv d N Ev σ c c' K K' u M) u := by
  refine HasDerivAt.fun_sum fun b _ => ?_
  exact (hc b).mul ((hasDerivAt_loopObs_zt Ev hz _ (wf_of_length hσ b) M).sub (hK b))

/-- The value bound, uniform in the matrix. -/
theorem norm_coefObsT_le (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {cc C : ℝ} (hcc : 0 ≤ cc) (hcb : ∀ b, ‖c u b‖ ≤ cc)
    (hval : ∀ b : LoopArg (d.L N) m,
      ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C) :
    ‖coefObsT d N Ev σ c K u M‖
      ≤ (Fintype.card (LoopArg (d.L N) m) : ℝ) * (cc * C) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ b ∈ (Finset.univ : Finset (LoopArg (d.L N) m)),
      ‖c u b * (loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b)‖ ≤ cc * C := by
    intro b _
    rw [norm_mul]
    exact mul_le_mul (hcb b) (hval b) (norm_nonneg _) hcc
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The derivative bound, uniform in the matrix. -/
theorem norm_coefObsTDeriv_le (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {cc C : ℝ} (hcc : 0 ≤ cc) (hcb : ∀ b, ‖c u b‖ ≤ cc) (hc'b : ∀ b, ‖c' u b‖ ≤ cc)
    (hval : ∀ b : LoopArg (d.L N) m,
      ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C)
    (hder : ∀ b : LoopArg (d.L N) m,
      ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
          ⟨σ, List.ofFn b⟩ - K' u b‖ ≤ C) :
    ‖coefObsTDeriv d N Ev σ c c' K K' u M‖
      ≤ (Fintype.card (LoopArg (d.L N) m) : ℝ) * (2 * (cc * C)) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ b ∈ (Finset.univ : Finset (LoopArg (d.L N) m)),
      ‖c' u b * (loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b)
        + c u b * (zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
            ⟨σ, List.ofFn b⟩ - K' u b)‖ ≤ 2 * (cc * C) := by
    intro b _
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖c' u b‖ * ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ cc * C :=
      mul_le_mul (hc'b b) (hval b) (norm_nonneg _) hcc
    have h2 : ‖c u b‖ * ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
        ⟨σ, List.ofFn b⟩ - K' u b‖ ≤ cc * C :=
      mul_le_mul (hcb b) (hder b) (norm_nonneg _) hcc
    linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem coefMomentObsT_eq (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    coefMomentObsT d N Ev σ c K p u M
      = (coefObsT d N Ev σ c K u M
          * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)) ^ p := by
  simp only [coefMomentObsT, momentFun]

/-- **`∂_u |Ψ₁|^{2p}`.** -/
theorem hasDerivAt_coefMomentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hc : ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    HasDerivAt (fun s : ℝ => coefMomentObsT d N Ev σ c K p s M)
      ((p : ℂ) * (coefObsT d N Ev σ c K u M
            * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)) ^ (p - 1)
        * (coefObsTDeriv d N Ev σ c c' K K' u M
              * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)
            + coefObsT d N Ev σ c K u M
              * (starRingEnd ℂ) (coefObsTDeriv d N Ev σ c c' K K' u M))) u := by
  have hfun : (fun s : ℝ => coefMomentObsT d N Ev σ c K p s M)
      = fun s : ℝ => (coefObsT d N Ev σ c K s M
          * (starRingEnd ℂ) (coefObsT d N Ev σ c K s M)) ^ p :=
    funext fun s => coefMomentObsT_eq Ev σ c K p s M
  rw [hfun]
  exact hasDerivAt_momentFun_path (hasDerivAt_coefObsT Ev hσ c c' K K' hz hc hK M) p

/-! ### The window envelope

Both `(L − K)_u` and its `z`-motion are bounded on the window by the deterministic resolvent
envelope, uniformly in the matrix — `RBM.Gauss.loopObs` carries `RBM.Gauss.hermCLM`, so no
Hermitian side condition on `M` is needed and the `∀ M` of `RBM.Gauss.TestFunT₁` is not a
disguised `∀ M, M.IsHermitian → …`. -/

/-- The envelope constant: `η⁻ᵐ W^{-(m-1)} + c_K` for the value, and the `z`-motion's own
envelope plus `c_K` for the derivative. -/
noncomputable def lkEnvelope (d : Dims) (N : ℕ) (Ev : ℝ) (m : ℕ) (η cK : ℝ) : ℝ :=
  max (η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) + cK)
    ((m : ℝ) * (max ‖mSigma Ev true‖ ‖mSigma Ev false‖ *
        ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) *
          (η⁻¹ ^ (m + 1) * ((d.W N : ℝ))⁻¹ ^ m)))) + cK)

theorem lkEnvelope_nonneg (d : Dims) (N : ℕ) (Ev : ℝ) (m : ℕ) {η cK : ℝ} (hη : 0 < η)
    (hcK : 0 ≤ cK) : 0 ≤ lkEnvelope d N Ev m η cK := by
  refine le_trans ?_ (le_max_left _ _)
  have : (0 : ℝ) ≤ η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) := by positivity
  linarith

theorem norm_lk_sub_le (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (K : ℝ → LoopArg (d.L N) m → ℂ) {u η cK : ℝ} (hη : 0 < η) (hzη : η ≤ |(zt Ev u).im|)
    (hKb : ∀ b, ‖K u b‖ ≤ cK) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (b : LoopArg (d.L N) m) :
    ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ lkEnvelope d N Ev m η cK := by
  have h : ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖
      ≤ η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) := by
    have h0 := norm_loopObs_le hη hzη _ (wf_of_length hσ b)
      (by rw [len_of_length (σ := σ) b]; exact hm) M
    rw [len_of_length (σ := σ) b] at h0
    exact h0
  calc ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖
      ≤ ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ + ‖K u b‖ := norm_sub_le _ _
    _ ≤ η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) + cK := add_le_add h (hKb b)
    _ ≤ lkEnvelope d N Ev m η cK := le_max_left _ _

theorem norm_zMotion_sub_le (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (K' : ℝ → LoopArg (d.L N) m → ℂ) {u η cK : ℝ} (hη : 0 < η) (hzη : η ≤ |(zt Ev u).im|)
    (hK'b : ∀ b, ‖K' u b‖ ≤ cK) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (b : LoopArg (d.L N) m) :
    ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
        ⟨σ, List.ofFn b⟩ - K' u b‖ ≤ lkEnvelope d N Ev m η cK := by
  have h : ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
      ⟨σ, List.ofFn b⟩‖
      ≤ (m : ℝ) * (max ‖mSigma Ev true‖ ‖mSigma Ev false‖ *
          ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) *
            (η⁻¹ ^ (m + 1) * ((d.W N : ℝ))⁻¹ ^ m)))) := by
    have h0 := norm_zMotion_hermCLM_le hη hzη Ev _ (wf_of_length hσ b) M
    have hl : (LoopIdx.mk σ (List.ofFn b)).length = m := len_of_length (σ := σ) b
    rw [hl] at h0
    exact h0
  calc ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
          ⟨σ, List.ofFn b⟩ - K' u b‖
      ≤ ‖zMotion (d.L N) (d.W N) (mSigma Ev) (hermCLM (d.Idx N) M) (zt Ev u)
          ⟨σ, List.ofFn b⟩‖ + ‖K' u b‖ := norm_sub_le _ _
    _ ≤ _ + cK := add_le_add h (hK'b b)
    _ ≤ lkEnvelope d N Ev m η cK := le_max_right _ _

/-! ### The seven fields, for an arbitrary `C¹`, bounded coefficient family -/

/-- **The field `RBM.Gauss.TestFunT₁.bddT`.**  Unlike the plain route's
`RBM.Gauss.bddT_momentObsT`, no compactness of the window is used: the coefficient family's
own bound is a hypothesis, so the bound on `∂_u Ψ` is a constant. -/
theorem bddT_coefMomentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {u₀ u₁ η cK cc : ℝ}
    (hη : 0 < η) (hcK : 0 ≤ cK) (hcc : 0 ≤ cc)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hc : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hcb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c u b‖ ≤ cc)
    (hc'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c' u b‖ ≤ cc)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖timeD1 (coefMomentObsT d N Ev σ c K p) u M‖ ≤ C := by
  classical
  set C₀ : ℝ := lkEnvelope d N Ev m η cK with hC₀
  have hC₀0 : 0 ≤ C₀ := lkEnvelope_nonneg d N Ev m hη hcK
  set Q : ℝ := (Fintype.card (LoopArg (d.L N) m) : ℝ) * (2 * (cc * C₀)) with hQ
  have hQ0 : 0 ≤ Q := by
    have : (0 : ℝ) ≤ cc * C₀ := mul_nonneg hcc hC₀0
    have hcard : (0 : ℝ) ≤ (Fintype.card (LoopArg (d.L N) m) : ℝ) := Nat.cast_nonneg _
    rw [hQ]; positivity
  refine ⟨(p : ℝ) * Q ^ (2 * (p - 1)) * (2 * Q * Q), fun u hu M => ?_⟩
  have hz : (zt Ev u).im ≠ 0 := im_zt_ne_zero_of_le hη (hzim u hu)
  have hval := fun b => norm_lk_sub_le Ev hσ hm K hη (hzim u hu) (hKb u hu) M b
  have hder := fun b => norm_zMotion_sub_le Ev hσ K' hη (hzim u hu) (hK'b u hu) M b
  have hA : ‖coefObsT d N Ev σ c K u M‖ ≤ Q := by
    refine le_trans (norm_coefObsT_le Ev σ c K u M hcc (hcb u hu) hval) ?_
    have hcard : (0 : ℝ) ≤ (Fintype.card (LoopArg (d.L N) m) : ℝ) := Nat.cast_nonneg _
    have : cc * C₀ ≤ 2 * (cc * C₀) := by nlinarith [mul_nonneg hcc hC₀0]
    exact mul_le_mul_of_nonneg_left this hcard
  have hD : ‖coefObsTDeriv d N Ev σ c c' K K' u M‖ ≤ Q :=
    norm_coefObsTDeriv_le Ev σ c c' K K' u M hcc (hcb u hu) (hc'b u hu) hval hder
  rw [timeD1_eq_of_hasDerivAt
    (hasDerivAt_coefMomentObsT Ev hσ c c' K K' p hz (fun b => hc u hu b)
      (fun b => hK u hu b) M)]
  exact norm_deriv_momentFun_path_le
    (f := fun s : ℝ => coefObsT d N Ev σ c K s M)
    (c := coefObsTDeriv d N Ev σ c c' K K' u M) hQ0 hA hD p

/-- **`RBM.Gauss.BddC2C` for `Ψ₁` with named constants** — `contDiffM`, `bdd₀`, `bdd₁`, `bdd₂`
at once.  The constants do not depend on `u`, so the window quantifier passes through them
with no compactness argument. -/
theorem bddC2C_coefObsT {Ev η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hzη : η ≤ |(zt Ev u).im|) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c K : ℝ → LoopArg (d.L N) m → ℂ) {cc cK : ℝ} (hcc : 0 ≤ cc)
    (hcb : ∀ b, ‖c u b‖ ≤ cc) (hKb : ∀ b, ‖K u b‖ ≤ cK) :
    BddC2C (coefObsT d N Ev σ c K u)
      ((Fintype.card (LoopArg (d.L N) m) : ℝ)
        * (cc * ((Fintype.card (d.Idx N) : ℝ) * (2 * (1 + η⁻¹) ^ 3) ^ m + cK)))
      ((Fintype.card (LoopArg (d.L N) m) : ℝ)
        * (cc * ((Fintype.card (d.Idx N) : ℝ) * ((m : ℝ) * (2 * (1 + η⁻¹) ^ 3) ^ m))))
      ((Fintype.card (LoopArg (d.L N) m) : ℝ)
        * (cc * ((Fintype.card (d.Idx N) : ℝ)
            * ((m : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ m)))) := by
  classical
  obtain ⟨hB1, hB2, hB3⟩ := le_two_mul_one_add_inv_cube hη
  set B : ℝ := 2 * (1 + η⁻¹) ^ 3 with hB
  set Cd : ℝ := (Fintype.card (d.Idx N) : ℝ) with hCd
  have hCd0 : (0 : ℝ) ≤ Cd := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B ^ m := by positivity
  have hfun : coefObsT d N Ev σ c K u
      = fun M => ∑ b : LoopArg (d.L N) m,
          (c u b * loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M + -(c u b * K u b)) := by
    funext M
    simp only [coefObsT]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hfun]
  have hterm : ∀ b : LoopArg (d.L N) m, BddC2C
      (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        c u b * loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M + -(c u b * K u b))
      (cc * (Cd * B ^ m + cK)) (cc * (Cd * ((m : ℝ) * B ^ m)))
      (cc * (Cd * ((m : ℝ) ^ 2 * B ^ m))) := by
    intro b
    have hloop0 := bddC2C_loopObs (d := d) (N := N) (B := B) hz hη hzη hB1 hB2 hB3
      (wf_of_length hσ b)
    rw [len_of_length (σ := σ) b] at hloop0
    have hmul := bddC2C_const_mul_cx (c u b) hloop0
    have hsum := bddC2C_add hmul
      (bddC2C_const (E := Matrix (d.Idx N) (d.Idx N) ℂ) (-(c u b * K u b)))
    refine hsum.mono ?_ ?_ ?_
    · have hk : ‖-(c u b * K u b)‖ ≤ cc * cK := by
        rw [norm_neg, norm_mul]
        exact mul_le_mul (hcb b) (hKb b) (norm_nonneg _) hcc
      have h1 : ‖c u b‖ * (Cd * B ^ m) ≤ cc * (Cd * B ^ m) :=
        mul_le_mul_of_nonneg_right (hcb b) (by positivity)
      nlinarith [hk, h1]
    · have h1 : ‖c u b‖ * (Cd * ((m : ℝ) * B ^ m)) ≤ cc * (Cd * ((m : ℝ) * B ^ m)) :=
        mul_le_mul_of_nonneg_right (hcb b) (by positivity)
      linarith [h1]
    · have h1 : ‖c u b‖ * (Cd * ((m : ℝ) ^ 2 * B ^ m))
          ≤ cc * (Cd * ((m : ℝ) ^ 2 * B ^ m)) :=
        mul_le_mul_of_nonneg_right (hcb b) (by positivity)
      linarith [h1]
  have hbig := bddC2C_sum (Finset.univ : Finset (LoopArg (d.L N) m)) fun b _ => hterm b
  refine hbig.mono ?_ ?_ ?_ <;>
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`contDiffM`, `bdd₀`, `bdd₁`, `bdd₂`, all four uniform over the window.** -/
theorem exists_bddC2C_coefMomentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {u₀ u₁ η cc cK : ℝ} (hη : 0 < η)
    (hcc : 0 ≤ cc)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hcb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c u b‖ ≤ cc)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK) :
    ∃ D₀ D₁ D₂ : ℝ, ∀ u ∈ Set.Icc u₀ u₁,
      BddC2C (coefMomentObsT d N Ev σ c K p u) D₀ D₁ D₂ := by
  classical
  set B : ℝ := 2 * (1 + η⁻¹) ^ 3 with hB
  set Cd : ℝ := (Fintype.card (d.Idx N) : ℝ) with hCd
  set R : ℝ := (Fintype.card (LoopArg (d.L N) m) : ℝ) with hR
  obtain ⟨D₀, D₁, D₂, hD⟩ := exists_bddC2C_momentFun
    (E := Matrix (d.Idx N) (d.Idx N) ℂ)
    (R * (cc * (Cd * B ^ m + cK))) (R * (cc * (Cd * ((m : ℝ) * B ^ m))))
    (R * (cc * (Cd * ((m : ℝ) ^ 2 * B ^ m)))) p
  refine ⟨D₀, D₁, D₂, fun u hu => ?_⟩
  have hz : (zt Ev u).im ≠ 0 := im_zt_ne_zero_of_le hη (hzim u hu)
  have hbase := bddC2C_coefObsT (d := d) (N := N) hη hz (hzim u hu) hσ c K hcc
    (hcb u hu) (hKb u hu)
  have heq : coefMomentObsT d N Ev σ c K p u = momentFun (coefObsT d N Ev σ c K u) p := rfl
  rw [heq]
  exact hD _ hbase

/-! ### `diffJoint` and `contT` -/

/-- **The field `RBM.Gauss.TestFunT₁.diffJoint` for `Ψ₁`.** -/
theorem differentiableAt_coefObsT_pair (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hc : ∀ b, DifferentiableAt ℝ (fun r : ℝ => c r b) u)
    (hK : ∀ b, DifferentiableAt ℝ (fun r : ℝ => K r b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefObsT d N Ev σ c K q.1 q.2) (u, M) := by
  simp only [coefObsT]
  refine DifferentiableAt.fun_sum fun b _ => ?_
  have hcq : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => c q.1 b) (u, M) :=
    differentiableAt_pair_fst (hc b)
  have hL : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      loopObs d N (zt Ev q.1) ⟨σ, List.ofFn b⟩ q.2) (u, M) :=
    (contDiffAt_loopObs_zt_pair Ev hz _ M).differentiableAt (by norm_num)
  have hKq : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => K q.1 b) (u, M) :=
    differentiableAt_pair_fst (hK b)
  exact hcq.mul (hL.sub hKq)

theorem differentiableAt_coefMomentObsT_pair (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {u : ℝ}
    (hz : (zt Ev u).im ≠ 0)
    (hc : ∀ b, DifferentiableAt ℝ (fun r : ℝ => c r b) u)
    (hK : ∀ b, DifferentiableAt ℝ (fun r : ℝ => K r b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefMomentObsT d N Ev σ c K p q.1 q.2) (u, M) := by
  have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefMomentObsT d N Ev σ c K p q.1 q.2)
      = fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (coefObsT d N Ev σ c K q.1 q.2
          * (starRingEnd ℂ) (coefObsT d N Ev σ c K q.1 q.2)) ^ p :=
    funext fun q => coefMomentObsT_eq Ev σ c K p q.1 q.2
  rw [hfun]
  have hA : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefObsT d N Ev σ c K q.1 q.2) (u, M) :=
    differentiableAt_coefObsT_pair Ev σ c K hz hc hK M
  have hAc : DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      (starRingEnd ℂ) (coefObsT d N Ev σ c K q.1 q.2)) (u, M) := by
    have h2 : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (starRingEnd ℂ) (coefObsT d N Ev σ c K q.1 q.2))
        = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap ∘
          fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => coefObsT d N Ev σ c K q.1 q.2 := rfl
    rw [h2]
    exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.differentiableAt.comp (u, M) hA
  exact (hA.mul hAc).pow p

theorem continuous_coefObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c K : ℝ → LoopArg (d.L N) m → ℂ) {η : ℝ} (hη : 0 < η) {u : ℝ}
    (hz : (zt Ev u).im ≠ 0) (hzη : η ≤ |(zt Ev u).im|) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ => coefObsT d N Ev σ c K u M := by
  simp only [coefObsT]
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_const.mul
    ((continuous_loopObs hz hη hzη (wf_of_length hσ b)).sub continuous_const)

theorem continuous_coefObsTDeriv (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) {η : ℝ} (hη : 0 < η) {u : ℝ}
    (hz : (zt Ev u).im ≠ 0) (hzη : η ≤ |(zt Ev u).im|) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefObsTDeriv d N Ev σ c c' K K' u M := by
  simp only [coefObsTDeriv]
  refine continuous_finsetSum _ fun b _ => ?_
  refine Continuous.add ?_ ?_
  · exact continuous_const.mul
      ((continuous_loopObs hz hη hzη (wf_of_length hσ b)).sub continuous_const)
  · exact continuous_const.mul
      ((continuous_zMotion_hermCLM hz hη hzη Ev (wf_of_length hσ b)).sub continuous_const)

theorem timeD1_coefMomentObsT_eq (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hc : ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    timeD1 (coefMomentObsT d N Ev σ c K p) u M
      = (p : ℂ) * (coefObsT d N Ev σ c K u M
            * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)) ^ (p - 1)
        * (coefObsTDeriv d N Ev σ c c' K K' u M
              * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)
            + coefObsT d N Ev σ c K u M
              * (starRingEnd ℂ) (coefObsTDeriv d N Ev σ c c' K K' u M)) :=
  timeD1_eq_of_hasDerivAt (hasDerivAt_coefMomentObsT Ev hσ c c' K K' p hz hc hK M)

/-- **The field `RBM.Gauss.TestFunT₁.contT`.** -/
theorem continuous_timeD1_coefMomentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {η : ℝ} (hη : 0 < η) {u : ℝ}
    (hz : (zt Ev u).im ≠ 0) (hzη : η ≤ |(zt Ev u).im|)
    (hc : ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      timeD1 (coefMomentObsT d N Ev σ c K p) u M := by
  have hfun : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      timeD1 (coefMomentObsT d N Ev σ c K p) u M)
      = fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
        (p : ℂ) * (coefObsT d N Ev σ c K u M
              * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)) ^ (p - 1)
          * (coefObsTDeriv d N Ev σ c c' K K' u M
                * (starRingEnd ℂ) (coefObsT d N Ev σ c K u M)
              + coefObsT d N Ev σ c K u M
                * (starRingEnd ℂ) (coefObsTDeriv d N Ev σ c c' K K' u M)) :=
    funext fun M => timeD1_coefMomentObsT_eq Ev hσ c c' K K' p hz hc hK M
  rw [hfun]
  have hA : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefObsT d N Ev σ c K u M := continuous_coefObsT Ev hσ c K hη hz hzη
  have hD : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      coefObsTDeriv d N Ev σ c c' K K' u M :=
    continuous_coefObsTDeriv Ev hσ c c' K K' hη hz hzη
  have hAc : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (starRingEnd ℂ) (coefObsT d N Ev σ c K u M) := Complex.continuous_conj.comp hA
  have hDc : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (starRingEnd ℂ) (coefObsTDeriv d N Ev σ c c' K K' u M) :=
    Complex.continuous_conj.comp hD
  exact (continuous_const.mul ((hA.mul hAc).pow _)).mul ((hD.mul hAc).add (hA.mul hDc))

/-- **`RBM.Gauss.TestFunT₁` for `Ψ = |∑_b c_u(b)(L−K)_u(b)|^{2p}`, all seven fields.**

The coefficient family enters through exactly three hypotheses: it is differentiable in `u` on
the window (`hc` — **first order only**, T191's point), and it and its derivative are bounded
there (`hcb`, `hc'b`).  Nothing else about `c` is used; in particular no second time
derivative and no continuity of `u ↦ c u b` beyond what `hc` already gives. -/
theorem testFunT₁_coefMomentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (hm : 1 ≤ m) (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {u₀ u₁ η cc cK : ℝ}
    (hη : 0 < η) (hcc : 0 ≤ cc) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hc : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hcb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c u b‖ ≤ cc)
    (hc'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c' u b‖ ≤ cc)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    TestFunT₁ d N (Set.Icc u₀ u₁) (coefMomentObsT d N Ev σ c K p) := by
  obtain ⟨D₀, D₁, D₂, hD⟩ :=
    exists_bddC2C_coefMomentObsT Ev hσ c K p hη hcc hzim hcb hKb
  refine ⟨fun u hu => (hD u hu).contDiff, ?_, ?_,
    ⟨D₀, fun u hu M => (hD u hu).bdd₀ M⟩,
    ⟨D₁, fun u hu M => (hD u hu).bdd₁ M⟩,
    ⟨D₂, fun u hu M => (hD u hu).bdd₂ M⟩,
    bddT_coefMomentObsT Ev hσ hm c c' K K' p hη hcK hcc hzim hc hcb hc'b hK hKb hK'b⟩
  · intro u hu M
    exact differentiableAt_coefMomentObsT_pair Ev σ c K p
      (im_zt_ne_zero_of_le hη (hzim u hu)) (fun b => (hc u hu b).differentiableAt)
      (fun b => (hK u hu b).differentiableAt) M
  · intro u hu
    exact continuous_timeD1_coefMomentObsT Ev hσ c c' K K' p hη
      (im_zt_ne_zero_of_le hη (hzim u hu)) (hzim u hu) (fun b => hc u hu b)
      (fun b => hK u hu b)

/-- **The generator identity at this `Ψ`, with no hypothesis left on `Ψ`** — the generalised
`RBM.Gauss.hasDerivAt_integral_momentObsT`. -/
theorem hasDerivAt_integral_coefMomentObsT (hst : MatrixStein d) (Ev : ℝ) {σ : List Bool}
    {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m) (c c' K K' : ℝ → LoopArg (d.L N) m → ℂ)
    (p : ℕ) {u₀ u₁ η cc cK : ℝ} (hη : 0 < η) (hcc : 0 ≤ cc) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hc : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => c r b) (c' u b) u)
    (hcb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c u b‖ ≤ cc)
    (hc'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖c' u b‖ ≤ cc)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK)
    {u : ℝ} (hu : 0 < u) (hlo : u₀ < u) (hhi : u < u₁) :
    HasDerivAt (fun s : ℝ => ∫ ω, coefMomentObsT d N Ev σ c K p s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (coefMomentObsT d N Ev σ c K p u)
            (Hflow d N u ω) i j ∂(P d)) u :=
  hasDerivAt_integral_Psi_pairs₁ hst
    (testFunT₁_coefMomentObsT Ev hσ hm c c' K K' p hη hcc hcK hzim hc hcb hc'b hK hKb hK'b)
    hu (Icc_mem_nhds hlo hhi)

/-! ### The plain route is the special case `c = RBM.Gauss.ukerCoefFam`

Each of T196's five `momentObsT`-specific lemmas is restated here **verbatim** and proved from
the generalised version, so the generalisation loses nothing. -/

/-- `∂_u` of the propagator row, as a family. -/
noncomputable def ukerCoefFam' {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (b : LoopArg L n) : ℂ :=
  ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) ((u : ℝ) : ℂ) t (a j) (b j))
    * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))

theorem hasDerivAt_ukerCoefFam {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (b : LoopArg L n) :
    HasDerivAt (fun r : ℝ => ukerCoefFam ξ t a r b) (ukerCoefFam' ξ t a u b) u := by
  have h := HasDerivAt.fun_finsetProd
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      hasDerivAt_edgeKer L (ξ i) t (a i) (b i) u)
  simpa only [smul_eq_mul, ukerCoefFam, ukerCoefFam'] using h

theorem norm_ukerCoefFam_le {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (b : LoopArg L n) :
    ‖ukerCoefFam ξ t a u b‖ ≤ ukerCoefBd ξ t a u := by
  classical
  have hmem := Finset.single_le_sum
    (f := fun b' : LoopArg L n =>
      ‖∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b' j))
          * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b' i)))‖
        + ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b' i)‖)
    (fun b' _ => by positivity) (Finset.mem_univ b)
  rw [← ukerCoefBd] at hmem
  refine le_trans ?_ hmem
  have h0 : (0 : ℝ) ≤ ‖∑ i : Fin n,
      (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b j))
        * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))‖ := norm_nonneg _
  simp only [ukerCoefFam]
  linarith

theorem norm_ukerCoefFam'_le {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u : ℝ) (b : LoopArg L n) :
    ‖ukerCoefFam' ξ t a u b‖ ≤ ukerCoefBd ξ t a u := by
  classical
  have hmem := Finset.single_le_sum
    (f := fun b' : LoopArg L n =>
      ‖∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (u : ℂ) t (a j) (b' j))
          * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b' i)))‖
        + ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b' i)‖)
    (fun b' _ => by positivity) (Finset.mem_univ b)
  rw [← ukerCoefBd] at hmem
  refine le_trans ?_ hmem
  have h0 : (0 : ℝ) ≤ ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) t (a i) (b i)‖ := norm_nonneg _
  simp only [ukerCoefFam']
  linarith

/-- The window bound on the plain route's coefficient family and its derivative, by
compactness (this is where T196's `RBM.Gauss.ukerCoefBd` continuity is used). -/
theorem exists_bound_ukerCoefFam {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (u₀ u₁ : ℝ) :
    ∃ cc : ℝ, 0 ≤ cc
      ∧ (∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖ukerCoefFam ξ t a u b‖ ≤ cc)
      ∧ (∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖ukerCoefFam' ξ t a u b‖ ≤ cc) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn
    (f := ukerCoefBd ξ t a) (continuous_ukerCoefBd ξ t a).continuousOn
  have hle : ∀ u ∈ Set.Icc u₀ u₁, ukerCoefBd ξ t a u ≤ C := fun u hu =>
    le_trans (le_abs_self _) (hC u hu)
  refine ⟨max C 0, le_max_right _ _, fun u hu b => ?_, fun u hu b => ?_⟩
  · exact le_trans (le_trans (norm_ukerCoefFam_le ξ t a u b) (hle u hu)) (le_max_left _ _)
  · exact le_trans (le_trans (norm_ukerCoefFam'_le ξ t a u b) (hle u hu)) (le_max_left _ _)

/-- **Probe 1**: `RBM.Gauss.testFunT₁_momentObsT`, verbatim, from the generalised class. -/
theorem testFunT₁_momentObsT_of_coef (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (hm : 1 ≤ m) (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ)
    (a : LoopArg (d.L N) m) (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    TestFunT₁ d N (Set.Icc u₀ u₁) (momentObsT d N Ev σ ξ t K a p) := by
  obtain ⟨cc, hcc, hcb, hc'b⟩ := exists_bound_ukerCoefFam ξ t a u₀ u₁
  rw [momentObsT_eq_coefMomentObsT]
  exact testFunT₁_coefMomentObsT Ev hσ hm _ (ukerCoefFam' ξ t a) K K' p hη hcc hcK hzim
    (fun u _ b => hasDerivAt_ukerCoefFam ξ t a u b) hcb hc'b hK hKb hK'b

/-- **Probe 2**: `RBM.Gauss.exists_bddC2C_momentObsT`, verbatim. -/
theorem exists_bddC2C_momentObsT_of_coef (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK) :
    ∃ D₀ D₁ D₂ : ℝ, ∀ u ∈ Set.Icc u₀ u₁,
      BddC2C (momentObsT d N Ev σ ξ t K a p u) D₀ D₁ D₂ := by
  obtain ⟨cc, hcc, hcb, -⟩ := exists_bound_ukerCoefFam ξ t a u₀ u₁
  rw [momentObsT_eq_coefMomentObsT]
  exact exists_bddC2C_coefMomentObsT Ev hσ _ K p hη hcc hzim hcb hKb

/-- **Probe 3**: `RBM.Gauss.bddT_momentObsT`, verbatim. -/
theorem bddT_momentObsT_of_coef (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (hm : 1 ≤ m) (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ)
    (a : LoopArg (d.L N) m) (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖timeD1 (momentObsT d N Ev σ ξ t K a p) u M‖ ≤ C := by
  obtain ⟨cc, hcc, hcb, hc'b⟩ := exists_bound_ukerCoefFam ξ t a u₀ u₁
  rw [momentObsT_eq_coefMomentObsT]
  exact bddT_coefMomentObsT Ev hσ hm _ (ukerCoefFam' ξ t a) K K' p hη hcK hcc hzim
    (fun u _ b => hasDerivAt_ukerCoefFam ξ t a u b) hcb hc'b hK hKb hK'b

/-- **Probe 4**: `RBM.Gauss.differentiableAt_momentObsT_pair`, verbatim. -/
theorem differentiableAt_momentObsT_pair_of_coef (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m) (p : ℕ)
    {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, DifferentiableAt ℝ (fun r : ℝ => K r b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    DifferentiableAt ℝ (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      momentObsT d N Ev σ ξ t K a p q.1 q.2) (u, M) := by
  rw [momentObsT_eq_coefMomentObsT]
  exact differentiableAt_coefMomentObsT_pair Ev σ _ K p hz
    (fun b => (hasDerivAt_ukerCoefFam ξ t a u b).differentiableAt) hK M

/-- **Probe 5**: `RBM.Gauss.continuous_timeD1_momentObsT`, verbatim. -/
theorem continuous_timeD1_momentObsT_of_coef (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (hσ : σ.length = m) (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ)
    (a : LoopArg (d.L N) m) (p : ℕ) {η : ℝ} (hη : 0 < η) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hzη : η ≤ |(zt Ev u).im|)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      timeD1 (momentObsT d N Ev σ ξ t K a p) u M := by
  rw [momentObsT_eq_coefMomentObsT]
  exact continuous_timeD1_coefMomentObsT Ev hσ _ (ukerCoefFam' ξ t a) K K' p hη hz hzη
    (fun b => hasDerivAt_ukerCoefFam ξ t a u b) hK

/-! #### The generalisation loses nothing: the five have the *same type*

Each `…_of_coef` above is `RBM.Gauss.testFunT₁_coefMomentObsT` (etc.) specialised at
`RBM.Gauss.ukerCoefFam`, in one line.  The five `rfl`s below are the acceptance check that
the restatements are not reshaped versions of T196's lemmas but *literally the same
statements*: each pair of theorems is definitionally equal as a term, hence interchangeable
at every call site. -/

example : @testFunT₁_momentObsT = @testFunT₁_momentObsT_of_coef := rfl
example : @exists_bddC2C_momentObsT = @exists_bddC2C_momentObsT_of_coef := rfl
example : @bddT_momentObsT = @bddT_momentObsT_of_coef := rfl
example : @differentiableAt_momentObsT_pair = @differentiableAt_momentObsT_pair_of_coef := rfl
example : @continuous_timeD1_momentObsT = @continuous_timeD1_momentObsT_of_coef := rfl

/-! ### The `Q_t` route: the coefficient family `RBM.Gauss.qCoefFam` is `C¹` and bounded

Only **one** time derivative of `ϑ_u` is used — `RBM.SumZeroDyn.hasDerivAt_vartheta`.  T191's
lesson applies verbatim: asking for `C²` in the time would be an over-requirement, and
`RBM.SumZeroDyn.varthetaDot` is not differentiated anywhere below. -/

theorem continuous_ukerCoefFam {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (b : LoopArg L n) :
    Continuous fun u : ℝ => ukerCoefFam ξ t a u b :=
  continuous_finsetProd _ fun _ _ => continuous_edgeKer_time _ _ _ _

theorem continuous_ukerCoefFam' {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (a : LoopArg L n) (b : LoopArg L n) :
    Continuous fun u : ℝ => ukerCoefFam' ξ t a u b := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_finsetProd _ fun j _ => continuous_edgeKer_time _ _ _ _).mul continuous_const

/-- `u ↦ (Θ_u)_{xy}` is continuous on any window inside `[0, 1)`
(`RBM.SumZeroDyn.hasDerivAt_Theta_real`). -/
theorem continuousOn_Theta_ofReal (L : ℕ) [NeZero L] (hL : 3 ≤ L) {u₀ u₁ : ℝ}
    (h0 : 0 ≤ u₀) (h1 : u₁ < 1) (x y : ZMod L) :
    ContinuousOn (fun u : ℝ => Theta L ((u : ℝ) : ℂ) x y) (Set.Icc u₀ u₁) := fun _ hu =>
  ((SumZeroDyn.hasDerivAt_Theta_real L hL (le_trans h0 hu.1)
    (lt_of_le_of_lt hu.2 h1) x y).continuousAt).continuousWithinAt

theorem continuousOn_ThetaSBTheta_apply (L : ℕ) [NeZero L] (hL : 3 ≤ L) {u₀ u₁ : ℝ}
    (h0 : 0 ≤ u₀) (h1 : u₁ < 1) (x y : ZMod L) :
    ContinuousOn (fun u : ℝ =>
      (Theta L ((u : ℝ) : ℂ) * SB L * Theta L ((u : ℝ) : ℂ)) x y) (Set.Icc u₀ u₁) := by
  have hT := continuousOn_Theta_ofReal L hL h0 h1
  simp only [Matrix.mul_apply]
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact (continuousOn_finsetSum _ fun j _ => (hT x j).mul continuousOn_const).mul (hT k y)

theorem continuousOn_vartheta_ofReal (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u₀ u₁ : ℝ}
    (h0 : 0 ≤ u₀) (h1 : u₁ < 1) (a : LoopArg L (n + 1)) :
    ContinuousOn (fun u : ℝ => vartheta L ((u : ℝ) : ℂ) a) (Set.Icc u₀ u₁) := fun _ hu =>
  ((SumZeroDyn.hasDerivAt_vartheta L hL (le_trans h0 hu.1)
    (lt_of_le_of_lt hu.2 h1) a).continuousAt).continuousWithinAt

theorem continuousOn_varthetaDot (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u₀ u₁ : ℝ}
    (h0 : 0 ≤ u₀) (h1 : u₁ < 1) (a : LoopArg L (n + 1)) :
    ContinuousOn (fun u : ℝ => SumZeroDyn.varthetaDot L u a) (Set.Icc u₀ u₁) := by
  have hT := continuousOn_Theta_ofReal L hL h0 h1
  have hTS := continuousOn_ThetaSBTheta_apply L hL h0 h1
  have hone : ContinuousOn (fun u : ℝ => (1 : ℂ) - ((u : ℝ) : ℂ)) (Set.Icc u₀ u₁) :=
    continuousOn_const.sub Complex.continuous_ofReal.continuousOn
  simp only [SumZeroDyn.varthetaDot]
  refine ContinuousOn.add ?_ ?_
  · exact (continuousOn_const.mul (hone.pow _)).mul
      (continuousOn_finsetProd _ fun i _ => hT _ _)
  · refine (hone.pow _).mul (continuousOn_finsetSum _ fun i _ => ?_)
    exact (continuousOn_finsetProd _ fun j _ => hT _ _).mul (hTS _ _)

/-- `∂_u w_u(x)`: the propagator row moves and so does `ϑ_u`. -/
noncomputable def qWeight' {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ)
    (a : LoopArg L (n + 1)) (u : ℝ) (x : ZMod L) : ℂ :=
  ∑ q : LoopArg L n,
    (ukerCoefFam' ξ t a u (Fin.cons x q) * vartheta L ((u : ℝ) : ℂ) (Fin.cons x q)
      + ukerCoefFam ξ t a u (Fin.cons x q) * SumZeroDyn.varthetaDot L u (Fin.cons x q))

/-- `∂_u` of the `Q_t` route's coefficient family. -/
noncomputable def qCoefFam' {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ)
    (a : LoopArg L (n + 1)) (u : ℝ) (b : LoopArg L (n + 1)) : ℂ :=
  ukerCoefFam' ξ t a u b - qWeight' ξ t a u (b 0)

theorem hasDerivAt_qCoefFam (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} (ξ : Fin (n + 1) → ℂ)
    (t : ℂ) (a : LoopArg L (n + 1)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (b : LoopArg L (n + 1)) :
    HasDerivAt (fun r : ℝ => qCoefFam ξ t a r b) (qCoefFam' ξ t a u b) u := by
  have hw : HasDerivAt (fun r : ℝ => qWeight ξ t a r (b 0)) (qWeight' ξ t a u (b 0)) u := by
    refine HasDerivAt.fun_sum fun q _ => ?_
    exact (hasDerivAt_ukerCoefFam ξ t a u (Fin.cons (b 0) q)).mul
      (SumZeroDyn.hasDerivAt_vartheta L hL hu0 hu1 (Fin.cons (b 0) q))
  exact (hasDerivAt_ukerCoefFam ξ t a u b).sub hw

theorem continuousOn_qCoefFam (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} (ξ : Fin (n + 1) → ℂ)
    (t : ℂ) (a : LoopArg L (n + 1)) {u₀ u₁ : ℝ} (h0 : 0 ≤ u₀) (h1 : u₁ < 1)
    (b : LoopArg L (n + 1)) :
    ContinuousOn (fun u : ℝ => qCoefFam ξ t a u b) (Set.Icc u₀ u₁) := by
  simp only [qCoefFam, qWeight]
  refine (continuous_ukerCoefFam ξ t a b).continuousOn.sub
    (continuousOn_finsetSum _ fun q _ => ?_)
  exact (continuous_ukerCoefFam ξ t a _).continuousOn.mul
    (continuousOn_vartheta_ofReal L hL h0 h1 _)

theorem continuousOn_qCoefFam' (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} (ξ : Fin (n + 1) → ℂ)
    (t : ℂ) (a : LoopArg L (n + 1)) {u₀ u₁ : ℝ} (h0 : 0 ≤ u₀) (h1 : u₁ < 1)
    (b : LoopArg L (n + 1)) :
    ContinuousOn (fun u : ℝ => qCoefFam' ξ t a u b) (Set.Icc u₀ u₁) := by
  simp only [qCoefFam', qWeight']
  refine (continuous_ukerCoefFam' ξ t a b).continuousOn.sub
    (continuousOn_finsetSum _ fun q _ => ?_)
  refine ContinuousOn.add ?_ ?_
  · exact (continuous_ukerCoefFam' ξ t a _).continuousOn.mul
      (continuousOn_vartheta_ofReal L hL h0 h1 _)
  · exact (continuous_ukerCoefFam ξ t a _).continuousOn.mul
      (continuousOn_varthetaDot L hL h0 h1 _)

/-- The window bound on the `Q_t` route's coefficient family and its derivative. -/
theorem exists_bound_qCoefFam (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} (ξ : Fin (n + 1) → ℂ)
    (t : ℂ) (a : LoopArg L (n + 1)) {u₀ u₁ : ℝ} (h0 : 0 ≤ u₀) (h1 : u₁ < 1) :
    ∃ cc : ℝ, 0 ≤ cc
      ∧ (∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖qCoefFam ξ t a u b‖ ≤ cc)
      ∧ (∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖qCoefFam' ξ t a u b‖ ≤ cc) := by
  classical
  set F : ℝ → ℝ := fun u => ∑ b : LoopArg L (n + 1),
    (‖qCoefFam ξ t a u b‖ + ‖qCoefFam' ξ t a u b‖) with hF
  have hFc : ContinuousOn F (Set.Icc u₀ u₁) :=
    continuousOn_finsetSum _ fun b _ =>
      (continuousOn_qCoefFam L hL ξ t a h0 h1 b).norm.add
        (continuousOn_qCoefFam' L hL ξ t a h0 h1 b).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn hFc
  have hle : ∀ u ∈ Set.Icc u₀ u₁, F u ≤ C := fun u hu => le_trans (le_abs_self _) (hC u hu)
  refine ⟨max C 0, le_max_right _ _, fun u hu b => ?_, fun u hu b => ?_⟩ <;>
    [skip; skip] <;>
    · have hsingle := Finset.single_le_sum
        (f := fun b' : LoopArg L (n + 1) => ‖qCoefFam ξ t a u b'‖ + ‖qCoefFam' ξ t a u b'‖)
        (fun b' _ => by positivity) (Finset.mem_univ b)
      have hsum : ‖qCoefFam ξ t a u b‖ + ‖qCoefFam' ξ t a u b‖ ≤ F u := hsingle
      have h1' : F u ≤ max C 0 := le_trans (hle u hu) (le_max_left _ _)
      have h2' : (0 : ℝ) ≤ ‖qCoefFam ξ t a u b‖ := norm_nonneg _
      have h3' : (0 : ℝ) ≤ ‖qCoefFam' ξ t a u b‖ := norm_nonneg _
      linarith [hsum]

/-! ### `RBM.Gauss.TestFunT₁` and the generator identity for the `Q_t` route -/

/-- **`RBM.Gauss.TestFunT₁` for `Ψ^Q = |(U_{u,v} ∘ Q_u (L−K)_u)_a|^{2p}`** — the `Q_t` twin of
T196's `RBM.Gauss.testFunT₁_momentObsT`, obtained by instantiating the generalised class at
`RBM.Gauss.qCoefFam`.  The extra hypotheses over the plain route are exactly `0 ≤ u₀` and
`u₁ < 1`, which is what `RBM.SumZeroDyn.hasDerivAt_vartheta` needs. -/
theorem testFunT₁_qMomentObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m + 1)
    (ξ : Fin (m + 1) → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) (m + 1) → ℂ)
    (a : LoopArg (d.L N) (m + 1)) (p : ℕ) {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ < 1)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK) :
    TestFunT₁ d N (Set.Icc u₀ u₁) (qMomentObsT d N Ev σ ξ t K a p) := by
  obtain ⟨cc, hcc, hcb, hc'b⟩ :=
    exists_bound_qCoefFam (d.L N) (d.three_le_L N) ξ t a hu₀ hu₁
  rw [qMomentObsT_eq_coefMomentObsT]
  exact testFunT₁_coefMomentObsT Ev hσ (by omega) _ (qCoefFam' ξ t a) K K' p hη hcc hcK hzim
    (fun u hu b => hasDerivAt_qCoefFam (d.L N) (d.three_le_L N) ξ t a
      (le_trans hu₀ hu.1) (lt_of_le_of_lt hu.2 hu₁) b) hcb hc'b hK hKb hK'b

/-- **The generator identity at `Ψ^Q`, with no hypothesis left on `Ψ^Q`** — the bridge from
T214's *pointwise* integrand to the *expectation* form that
`RBM.MomentDuhamel.momentIneqQ_of_derivBound` integrates. -/
theorem hasDerivAt_integral_qMomentObsT (hst : MatrixStein d) (Ev : ℝ) {σ : List Bool}
    {m : ℕ} (hσ : σ.length = m + 1) (ξ : Fin (m + 1) → ℂ) (t : ℂ)
    (K K' : ℝ → LoopArg (d.L N) (m + 1) → ℂ) (a : LoopArg (d.L N) (m + 1)) (p : ℕ)
    {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK) (hu₀ : 0 ≤ u₀) (hu₁ : u₁ < 1)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hK : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K' u b‖ ≤ cK)
    {u : ℝ} (hu : 0 < u) (hlo : u₀ < u) (hhi : u < u₁) :
    HasDerivAt (fun s : ℝ => ∫ ω, qMomentObsT d N Ev σ ξ t K a p s (Hflow d N s ω) ∂(P d))
      ((∫ ω, timeD1 (qMomentObsT d N Ev σ ξ t K a p) u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N (qMomentObsT d N Ev σ ξ t K a p u)
            (Hflow d N u ω) i j ∂(P d)) u :=
  hasDerivAt_integral_Psi_pairs₁ hst
    (testFunT₁_qMomentObsT Ev hσ ξ t K K' a p hη hcK hu₀ hu₁ hzim hK hKb hK'b) hu
    (Icc_mem_nhds hlo hhi)

/-! ### From the generator expression to `∫ (∂_u + 𝓛)`

The derivative slot of `RBM.MomentDuhamel.momentIneqQ_of_derivBound` is existential, so `φ'`
may be *chosen*; choosing it to be the generator expression turns the `hbound` slot into an
inequality between two integrals, whose integrand is exactly T214's pointwise
`RBM.Gauss.timeD1_add_genMomentPt_le_driftFQ`. -/

/-- `φ'` in the shape `RBM.Gauss.hasDerivAt_integral_Psi₁` produces it. -/
noncomputable def phiCoefDeriv (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) (u : ℝ) : ℝ :=
  ((∫ ω, timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω) ∂(P d))
      + (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
          ∫ ω, coordD2 d N (coefMomentObsT d N Ev σ c K p u) (Hflow d N u ω) q ∂(P d)).re

/-- **`φ' = E[(∂_u + 𝓛)Ψ]`.**  The pointwise integrand of T206/T214 is exactly the integrand
here, so the two sides of `hbound` are an integral of the pointwise inequality. -/
theorem phiCoefDeriv_eq_integral (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (c K : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {T : Set ℝ}
    (h : TestFunT₁ d N T (coefMomentObsT d N Ev σ c K p)) {u : ℝ} (hu : u ∈ T)
    (hC2 : ContDiff ℝ 2 (coefObsT d N Ev σ c K u)) :
    phiCoefDeriv d N Ev σ c K p u
      = ∫ ω, ((timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω)).re
          + genMomentPt d N (coefObsT d N Ev σ c K u) p (Hflow d N u ω)) ∂(P d) := by
  classical
  obtain ⟨CT, hCT⟩ := h.bddT
  have hslice : TestFun d N (momentFun (coefObsT d N Ev σ c K u) p) := h.slice hu
  have hcontT : Continuous fun ω : Ω d =>
      timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω) :=
    (h.contT u hu).comp (continuous_Hflow d N u)
  have hintT : Integrable (fun ω : Ω d =>
      timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω)) (P d) :=
    integrable_of_continuous_of_bound hcontT fun ω => hCT u hu _
  have hB : ((∫ ω, genMomentPt d N (coefObsT d N Ev σ c K u) p (Hflow d N u ω) ∂(P d) : ℝ) : ℂ)
      = (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
          ∫ ω, coordD2 d N (coefMomentObsT d N Ev σ c K p u) (Hflow d N u ω) q ∂(P d) := by
    rw [← integral_complex_ofReal]
    have hpt : (fun ω : Ω d =>
        ((genMomentPt d N (coefObsT d N Ev σ c K u) p (Hflow d N u ω) : ℝ) : ℂ))
        = fun ω : Ω d => (2⁻¹ : ℝ) • ∑ q ∈ usedCoord d N,
            (gvar d (crd d N q) : ℝ)
              • coordD2 d N (momentFun (coefObsT d N Ev σ c K u) p) (Hflow d N u ω) q :=
      funext fun ω => ofReal_genMomentPt hC2 p _
    have hint : ∀ q ∈ usedCoord d N, Integrable
        (fun ω : Ω d => (gvar d (crd d N q) : ℝ)
          • coordD2 d N (momentFun (coefObsT d N Ev σ c K u) p) (Hflow d N u ω) q) (P d) :=
      fun q _ => (integrable_coordD2 hslice u q).smul ((gvar d (crd d N q) : ℝ))
    rw [hpt, integral_smul, integral_finsetSum _ hint]
    simp only [integral_smul, one_div]
    rfl
  have hre : (∫ ω, timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω) ∂(P d)).re
      = ∫ ω, (timeD1 (coefMomentObsT d N Ev σ c K p) u (Hflow d N u ω)).re ∂(P d) := by
    have h0 := integral_re (𝕜 := ℂ) hintT
    simpa using h0.symm
  rw [phiCoefDeriv, ← hB, Complex.add_re, Complex.ofReal_re, hre]
  exact (integral_add hintT.re (integrable_genMomentPt hslice u)).symm

/-! ### Hölder, for the three drift integrands of (5.91) at once

`RBM.MomentDuhamel.integral_pow_sub_one_mul_le` and
`RBM.MomentDuhamel.integral_pow_sub_two_mul_le` (T191) applied three and one time; the only
new content is the bookkeeping that keeps the three first-order terms under **one**
`(E|Ψ|^{2p})^{(2p-1)/(2p)}`, which is what `RBM.MomentDuhamel.momentIneqQ_of_derivBound`
asks for. -/

theorem integral_le_holder_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ}
    (hp : 1 ≤ p) {Φ Y G₁ G₂ G₃ Qd : Ω → ℝ}
    (hYm : AEStronglyMeasurable Y P) (hG₁m : AEStronglyMeasurable G₁ P)
    (hG₂m : AEStronglyMeasurable G₂ P) (hG₃m : AEStronglyMeasurable G₃ P)
    (hQm : AEStronglyMeasurable Qd P) (hQ0 : ∀ ω, 0 ≤ Qd ω)
    (hYi : Integrable (fun ω => |Y ω| ^ (2 * p)) P)
    (hG₁i : Integrable (fun ω => |G₁ ω| ^ (2 * p)) P)
    (hG₂i : Integrable (fun ω => |G₂ ω| ^ (2 * p)) P)
    (hG₃i : Integrable (fun ω => |G₃ ω| ^ (2 * p)) P)
    (hQi : Integrable (fun ω => |Qd ω| ^ p) P)
    (hΦi : Integrable Φ P)
    (hm₁ : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |G₁ ω|) P)
    (hm₂ : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |G₂ ω|) P)
    (hm₃ : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |G₃ ω|) P)
    (hm₄ : Integrable (fun ω => |Y ω| ^ (2 * p - 2) * Qd ω) P)
    (hle : ∀ ω, Φ ω ≤ 2 * (p : ℝ) * (|Y ω| ^ (2 * p - 1) * |G₁ ω|
          + |Y ω| ^ (2 * p - 1) * |G₂ ω| + |Y ω| ^ (2 * p - 1) * |G₃ ω|)
        + (p : ℝ) * (2 * (p : ℝ) - 1) * (|Y ω| ^ (2 * p - 2) * Qd ω)) :
    ∫ ω, Φ ω ∂P
      ≤ 2 * (p : ℝ) * (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (MomentDuhamel.momNorm P (2 * p) G₁ + MomentDuhamel.momNorm P (2 * p) G₂
              + MomentDuhamel.momNorm P (2 * p) G₃)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ))
            * MomentDuhamel.momNorm P p Qd := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2p : (0 : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hc : (0 : ℝ) ≤ (p : ℝ) * (2 * (p : ℝ) - 1) := by nlinarith
  have h12 : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |G₁ ω|
      + |Y ω| ^ (2 * p - 1) * |G₂ ω|) P := hm₁.add hm₂
  have hsum3 : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |G₁ ω|
      + |Y ω| ^ (2 * p - 1) * |G₂ ω| + |Y ω| ^ (2 * p - 1) * |G₃ ω|) P := h12.add hm₃
  have hRi : Integrable (fun ω => 2 * (p : ℝ) * (|Y ω| ^ (2 * p - 1) * |G₁ ω|
        + |Y ω| ^ (2 * p - 1) * |G₂ ω| + |Y ω| ^ (2 * p - 1) * |G₃ ω|)
      + (p : ℝ) * (2 * (p : ℝ) - 1) * (|Y ω| ^ (2 * p - 2) * Qd ω)) P :=
    (hsum3.const_mul _).add (hm₄.const_mul _)
  have hInt : ∫ ω, (2 * (p : ℝ) * (|Y ω| ^ (2 * p - 1) * |G₁ ω|
          + |Y ω| ^ (2 * p - 1) * |G₂ ω| + |Y ω| ^ (2 * p - 1) * |G₃ ω|)
        + (p : ℝ) * (2 * (p : ℝ) - 1) * (|Y ω| ^ (2 * p - 2) * Qd ω)) ∂P
      = 2 * (p : ℝ) * ((∫ ω, |Y ω| ^ (2 * p - 1) * |G₁ ω| ∂P)
            + (∫ ω, |Y ω| ^ (2 * p - 1) * |G₂ ω| ∂P)
            + ∫ ω, |Y ω| ^ (2 * p - 1) * |G₃ ω| ∂P)
        + (p : ℝ) * (2 * (p : ℝ) - 1) * ∫ ω, |Y ω| ^ (2 * p - 2) * Qd ω ∂P := by
    rw [integral_add (hsum3.const_mul _) (hm₄.const_mul _), integral_const_mul,
      integral_const_mul, integral_add h12 hm₃, integral_add hm₁ hm₂]
  have hI₁ := MomentDuhamel.integral_pow_sub_one_mul_le (P := P) hp hYm hG₁m hYi hG₁i
  have hI₂ := MomentDuhamel.integral_pow_sub_one_mul_le (P := P) hp hYm hG₂m hYi hG₂i
  have hI₃ := MomentDuhamel.integral_pow_sub_one_mul_le (P := P) hp hYm hG₃m hYi hG₃i
  have hI₄ := MomentDuhamel.integral_pow_sub_two_mul_le (P := P) hp hYm hQm hQ0 hYi hQi
  calc ∫ ω, Φ ω ∂P
      ≤ ∫ ω, (2 * (p : ℝ) * (|Y ω| ^ (2 * p - 1) * |G₁ ω|
            + |Y ω| ^ (2 * p - 1) * |G₂ ω| + |Y ω| ^ (2 * p - 1) * |G₃ ω|)
          + (p : ℝ) * (2 * (p : ℝ) - 1) * (|Y ω| ^ (2 * p - 2) * Qd ω)) ∂P :=
        integral_mono hΦi hRi hle
    _ = 2 * (p : ℝ) * ((∫ ω, |Y ω| ^ (2 * p - 1) * |G₁ ω| ∂P)
            + (∫ ω, |Y ω| ^ (2 * p - 1) * |G₂ ω| ∂P)
            + ∫ ω, |Y ω| ^ (2 * p - 1) * |G₃ ω| ∂P)
        + (p : ℝ) * (2 * (p : ℝ) - 1) * ∫ ω, |Y ω| ^ (2 * p - 2) * Qd ω ∂P := hInt
    _ ≤ 2 * (p : ℝ) * ((∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * MomentDuhamel.momNorm P (2 * p) G₁
            + (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * MomentDuhamel.momNorm P (2 * p) G₂
            + (∫ ω, |Y ω| ^ (2 * p) ∂P) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
              * MomentDuhamel.momNorm P (2 * p) G₃)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * ((∫ ω, |Y ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ))
              * MomentDuhamel.momNorm P p Qd) :=
        add_le_add (mul_le_mul_of_nonneg_left (by linarith) h2p)
          (mul_le_mul_of_nonneg_left hI₄ hc)
    _ = _ := by ring


/-! ### The fifteen integrability slots of the Hölder step, from continuity and an envelope

`RBM.Gauss.integral_le_holder_sum` asks for fifteen integrability facts.  On the Gaussian
model every one of the six integrands is continuous in the sample point and bounded there by
the deterministic resolvent envelope, so all fifteen come from two elementary lemmas. -/

/-- Continuity plus a bound gives every integrability `integral_le_holder_sum` asks for. -/
theorem integrable_abs_pow_of_bdd {f : Ω d → ℝ} (hf : Continuous f) {C : ℝ}
    (hb : ∀ ω, |f ω| ≤ C) (q : ℕ) :
    Integrable (fun ω : Ω d => |f ω| ^ q) (P d) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb 0)
  refine integrable_of_continuous_of_bound (hf.abs.pow q) (C := C ^ q) fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) q)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) q

theorem integrable_abs_pow_mul_of_bdd {f g : Ω d → ℝ} (hf : Continuous f) (hg : Continuous g)
    {C D : ℝ} (hb : ∀ ω, |f ω| ≤ C) (hd : ∀ ω, |g ω| ≤ D) (q : ℕ) :
    Integrable (fun ω : Ω d => |f ω| ^ q * |g ω|) (P d) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hb 0)
  have hD0 : (0 : ℝ) ≤ D := le_trans (abs_nonneg _) (hd 0)
  refine integrable_of_continuous_of_bound ((hf.abs.pow q).mul hg.abs)
    (C := C ^ q * D) fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb ω) q) (hd ω) (abs_nonneg _)
    (by positivity)

theorem integrable_abs_pow_mul_nonneg_of_bdd {f g : Ω d → ℝ} (hf : Continuous f)
    (hg : Continuous g) {C D : ℝ} (hb : ∀ ω, |f ω| ≤ C) (hg0 : ∀ ω, 0 ≤ g ω)
    (hd : ∀ ω, g ω ≤ D) (q : ℕ) :
    Integrable (fun ω : Ω d => |f ω| ^ q * g ω) (P d) := by
  have h := integrable_abs_pow_mul_of_bdd hf hg hb (D := D)
    (fun ω => by rw [abs_of_nonneg (hg0 ω)]; exact hd ω) q
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [abs_of_nonneg (hg0 ω)]

/-- **Hölder for the four drift integrands of (5.91) from continuity and envelopes.**
`RBM.Gauss.integral_le_holder_sum` with its fifteen integrability hypotheses discharged, and
with the quadratic variation replaced by its `E ⊗ E` majorant `cq · g`. -/
theorem integral_le_holder_sum_of_bdd {p : ℕ} (hp : 1 ≤ p)
    {Φ Y G₁ G₂ G₃ Qd g : Ω d → ℝ} {CY CG cq : ℝ}
    (hΦi : Integrable Φ (P d)) (hYc : Continuous Y) (hG₁c : Continuous G₁)
    (hG₂c : Continuous G₂)
    (hG₃c : Continuous G₃) (hQc : Continuous Qd) (hgc : Continuous g)
    (hYb : ∀ ω, |Y ω| ≤ CY) (hG₁b : ∀ ω, |G₁ ω| ≤ CG)
    (hG₂b : ∀ ω, |G₂ ω| ≤ CG) (hG₃b : ∀ ω, |G₃ ω| ≤ CG) (hgb : ∀ ω, |g ω| ≤ CG)
    (hQ0 : ∀ ω, 0 ≤ Qd ω) (hcq : 0 ≤ cq) (hQg : ∀ ω, Qd ω ≤ cq * g ω)
    (hle : ∀ ω, Φ ω ≤ 2 * (p : ℝ) * (|Y ω| ^ (2 * p - 1) * |G₁ ω|
          + |Y ω| ^ (2 * p - 1) * |G₂ ω| + |Y ω| ^ (2 * p - 1) * |G₃ ω|)
        + (p : ℝ) * (2 * (p : ℝ) - 1) * (|Y ω| ^ (2 * p - 2) * Qd ω)) :
    ∫ ω, Φ ω ∂(P d)
      ≤ 2 * (p : ℝ) * (∫ ω, |Y ω| ^ (2 * p) ∂(P d)) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (MomentDuhamel.momNorm (P d) (2 * p) G₁
              + MomentDuhamel.momNorm (P d) (2 * p) G₂
              + MomentDuhamel.momNorm (P d) (2 * p) G₃)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, |Y ω| ^ (2 * p) ∂(P d)) ^ (((p : ℝ) - 1) / (p : ℝ))
            * (cq * MomentDuhamel.momNorm (P d) p g) := by
  have hCG0 : (0 : ℝ) ≤ CG := le_trans (abs_nonneg _) (hgb 0)
  have hQb : ∀ ω, Qd ω ≤ cq * CG := fun ω =>
    le_trans (hQg ω) (mul_le_mul_of_nonneg_left
      (le_trans (le_abs_self _) (hgb ω)) hcq)
  have hkey := integral_le_holder_sum (P := P d) hp
    (Φ := Φ) (Y := Y) (G₁ := G₁) (G₂ := G₂) (G₃ := G₃) (Qd := Qd)
    hYc.aestronglyMeasurable hG₁c.aestronglyMeasurable hG₂c.aestronglyMeasurable
    hG₃c.aestronglyMeasurable hQc.aestronglyMeasurable hQ0
    (integrable_abs_pow_of_bdd hYc hYb (2 * p))
    (integrable_abs_pow_of_bdd hG₁c hG₁b (2 * p))
    (integrable_abs_pow_of_bdd hG₂c hG₂b (2 * p))
    (integrable_abs_pow_of_bdd hG₃c hG₃b (2 * p))
    (integrable_abs_pow_of_bdd hQc (fun ω => by
      rw [abs_of_nonneg (hQ0 ω)]; exact hQb ω) p)
    hΦi
    (integrable_abs_pow_mul_of_bdd hYc hG₁c hYb hG₁b (2 * p - 1))
    (integrable_abs_pow_mul_of_bdd hYc hG₂c hYb hG₂b (2 * p - 1))
    (integrable_abs_pow_mul_of_bdd hYc hG₃c hYb hG₃b (2 * p - 1))
    (integrable_abs_pow_mul_nonneg_of_bdd hYc hQc hYb hQ0 hQb (2 * p - 2))
    hle
  refine hkey.trans (add_le_add le_rfl ?_)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) * (2 * (p : ℝ) - 1) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  have hY0 : (0 : ℝ) ≤ (∫ ω, |Y ω| ^ (2 * p) ∂(P d)) ^ (((p : ℝ) - 1) / (p : ℝ)) :=
    Real.rpow_nonneg (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) _
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hmono : MomentDuhamel.momNorm (P d) p Qd
      ≤ MomentDuhamel.momNorm (P d) p (fun ω => cq * g ω) := by
    refine momNorm_mono ?_ fun ω => ?_
    · exact integrable_abs_pow_of_bdd (f := fun ω : Ω d => cq * g ω)
        (continuous_const.mul hgc) (C := cq * CG) (fun ω => by
        rw [abs_mul, abs_of_nonneg hcq]
        exact mul_le_mul_of_nonneg_left (hgb ω) hcq) p
    · rw [abs_of_nonneg (hQ0 ω), abs_mul, abs_of_nonneg hcq]
      exact le_trans (hQg ω) (mul_le_mul_of_nonneg_left (le_abs_self _) hcq)
  rw [momNorm_const_mul (Nat.one_le_iff_ne_zero.mp hp) hcq g] at hmono
  exact hmono

/-! ### The derivative slot of `RBM.MomentDuhamel.momentIneqQ_of_derivBound`

`RBM.Gauss.hasDerivAt_integral_qMomentObsT` gives `∂_u E Ψ^Q` in the `RBM.Gauss.Hflow`
language; the slot of `RBM.MomentDuhamel.momentIneqQ_of_derivBound` speaks about the *real*
integral `u ↦ E |(U_{u,v} ∘ Q_u (L-K)_u)_a|^{2p}`.  The bridge is
`RBM.Gauss.qMomentObsT_flow` (T214) plus `Complex.reCLM`; nothing else is needed, and the
resulting `φ'` is the pinned `RBM.Gauss.phiCoefDeriv`, **not** a caller's choice.

This discharges the derivative slot **unconditionally** — the plain route
(`RBM.Gauss.momentIneq_of_derivBound_gauss`) leaves its twin to the caller. -/


theorem hasDerivAt_integral_psiQ_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (p : ℕ) {u : ℝ} (hu : u ∈ Set.Ioo s v) :
    HasDerivAt (fun r : ℝ =>
        ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (d.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖| ^ (2 * p)
          ∂(band d).P)
      (phiCoefDeriv d N E (List.ofFn σ)
        (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p u) u := by
  classical
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    exists_bdd_Kval_Kprim (d := d) E N hE.le hs0 hv1 (v := v) σ
  have hT₁ : TestFunT₁ d N (Set.Icc s v)
      (qMomentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p) :=
    testFunT₁_qMomentObsT E (m := n + 1) (List.length_ofFn) (xiOf (mSigma E) σ)
      ((v : ℝ) : ℂ) (fun r b => (band d).Kval E N r (LoopData.idx (σ, b)))
      (Kprim (band d) E N σ) a p (window_eta_pos hE hv1) hcK hs0 hv1
      (window_le_abs_im hE hv1)
      (fun r hr b => hasDerivAt_Kval_Kprim (band d) E N
        (window_norm_mul_lt hE.le hs0 hv1 r hr) σ b) hKb hK'b
  set Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    qMomentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p with hΨ
  set φ : ℝ → ℝ := fun r : ℝ =>
    ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop (d.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖| ^ (2 * p)
      ∂(band d).P with hφ
  have hΦφ : (fun r : ℝ => ∫ ω, Ψ r (Hflow d N r ω) ∂(P d))
      = fun r : ℝ => ((φ r : ℝ) : ℂ) := by
    funext r
    have hpt : ∀ ω : Ω d, Ψ r (Hflow d N r ω)
        = ((|‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Qop (d.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖|
                ^ (2 * p) : ℝ) : ℂ) := fun ω =>
      qMomentObsT_flow (band d) (sample d) E N σ a ((v : ℝ) : ℂ) (fun _ _ => rfl) p r ω
    rw [show (fun ω : Ω d => Ψ r (Hflow d N r ω))
        = fun ω : Ω d => ((|‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Qop (d.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖|
                ^ (2 * p) : ℝ) : ℂ) from funext hpt]
    exact integral_complex_ofReal
  have hu0 : 0 < u := lt_of_le_of_lt hs0 hu.1
  have hD := hasDerivAt_integral_Psi₁ (matrixStein d) hT₁ hu0 (Icc_mem_nhds hu.1 hu.2)
  rw [hΦφ] at hD
  have hre : HasDerivAt (fun r : ℝ => (((φ r : ℝ) : ℂ)).re)
      (Complex.reCLM ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
          ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d))) u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hD
  simp only [Complex.ofReal_re, Complex.reCLM_apply] at hre
  have hΨeq : Ψ = coefMomentObsT d N E (List.ofFn σ)
      (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p :=
    qMomentObsT_eq_coefMomentObsT E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p
  rw [hΨeq] at hre
  exact hre

/-! ### The `hbound` slot of `RBM.MomentDuhamel.momentIneqQ_of_derivBound`

The chain is: `RBM.Gauss.phiCoefDeriv_eq_integral` identifies `φ'` with `∫ (∂_u + 𝓛)Ψ^Q`;
T214's pointwise `RBM.Gauss.timeD1_add_genMomentPt_le_driftFQ_flow` bounds the integrand;
`RBM.Gauss.integral_le_holder_sum_of_bdd` integrates and applies Hölder.

What is **not** supplied here, because it belongs to T226 and lives in files this ticket may
not write, is exactly two things, and they enter as the named hypotheses below:

* the continuity in `ω` and the window envelope of the three drift integrands of (5.91) and
  of the `E ⊗ E` term (T226 item 1) — `hG₁c`/`hG₁b`, `hG₂c`/`hG₂b`, `hG₃c`/`hG₃b`,
  `hgc`/`hgb`;
* the quadratic-variation bridge (5.103) (T226 item 2) — `hQV`, **with its constant `cq`**.

⚠ **The constant `cq` is not cosmetic.**  The bridge that T226 is producing
(`RBM.EEUker.quadVar_qUkerObsT_le_norm_QQ_eeFun`, and already its plain twin
`RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun`) carries a factor `n + 2` — the Cauchy–Schwarz
over the `n+2` edges of the chain rule `E^{(M)}(α) = ∑_m E^{(M)}(α, m)` of §5.2 — while the
`hbound` slot of `RBM.MomentDuhamel.momentIneqQ_of_derivBound` (and of
`momentIneq_of_derivBound`) hard-codes `RBM.MomentDuhamel.cMDval p = max 0 (2p-1)`, which
cannot depend on `n`.  Keeping `cq` explicit is what makes the theorem below usable in both
readings: at `cq = 1` its conclusion is the frozen slot verbatim
(`RBM.Gauss.hbound_qMomentObsT_gauss_one`), and at `cq = n + 2` it is what the bridge actually
proves.  See the report's paper-delta `T225a`. -/


theorem hbound_qMomentObsT_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) {p : ℕ} (hp : 1 ≤ p) {u : ℝ} (hu : u ∈ Set.Ioo s v)
    {cq CG : ℝ} (hcq : 0 ≤ cq)
    (hG₁c : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖)
    (hG₁b : ∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖ ≤ CG)
    (hG₂c : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)
    (hG₂b : ∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖ ≤ CG)
    (hG₃c : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) u b) a‖)
    (hG₃b : ∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) u b) a‖ ≤ CG)
    (hgc : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)) (Fin.append a a)‖)
    (hgb : ∀ ω : Ω d, ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
          (Fin.append a a)‖ ≤ CG)
    (hQV : ∀ ω : Ω d, quadVar d N (qUkerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
          ((v : ℝ) : ℂ) (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a u)
          (Hflow d N u ω)
        ≤ cq * ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
            (Fin.append a a)‖) :
    phiCoefDeriv d N E (List.ofFn σ)
          (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p u
      ≤ 2 * (p : ℝ)
            * (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
                  ^ (2 * p) ∂(P d)) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (MomentDuhamel.momNorm (P d) (2 * p) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (Qop (d.L N) ((u : ℝ) : ℂ)
                      (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖)
              + MomentDuhamel.momNorm (P d) (2 * p) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                      (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)
              + MomentDuhamel.momNorm (P d) (2 * p) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
                      * SumZeroDyn.varthetaDot (d.L N) u b) a‖))
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
                  ^ (2 * p) ∂(P d)) ^ (((p : ℝ) - 1) / (p : ℝ))
            * (cq * MomentDuhamel.momNorm (P d) p (fun ω =>
                ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
                    (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
                  (Fin.append a a)‖)) := by
  classical
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    exists_bdd_Kval_Kprim (d := d) E N hE.le hs0 hv1 (v := v) σ
  have hmemI : u ∈ Set.Icc s v := ⟨hu.1.le, hu.2.le⟩
  have hz : (zt E u).im ≠ 0 := window_im_ne_zero hE hv1 u hmemI
  have hT₁ : TestFunT₁ d N (Set.Icc s v)
      (qMomentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p) :=
    testFunT₁_qMomentObsT E (m := n + 1) (List.length_ofFn) (xiOf (mSigma E) σ)
      ((v : ℝ) : ℂ) (fun r b => (band d).Kval E N r (LoopData.idx (σ, b)))
      (Kprim (band d) E N σ) a p (window_eta_pos hE hv1) hcK hs0 hv1
      (window_le_abs_im hE hv1)
      (fun r hr b => hasDerivAt_Kval_Kprim (band d) E N
        (window_norm_mul_lt hE.le hs0 hv1 r hr) σ b) hKb hK'b
  have hΨeq : qMomentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p
      = coefMomentObsT d N E (List.ofFn σ)
          (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p :=
    qMomentObsT_eq_coefMomentObsT E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p
  obtain ⟨cc, hcc, hcb, hc'b⟩ :=
    exists_bound_qCoefFam (d.L N) (d.three_le_L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a
      hs0 hv1
  have hbdd := bddC2C_coefObsT (d := d) (N := N) (window_eta_pos hE hv1) hz
    (window_le_abs_im hE hv1 u hmemI) (σ := List.ofFn σ) (m := n + 2) (List.length_ofFn)
    (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
    (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) hcc (hcb u hmemI) (hKb u hmemI)
  rw [hΨeq] at hT₁
  have hphi := phiCoefDeriv_eq_integral E
    (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
    (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p hT₁ hmemI hbdd.contDiff
  have hQc : Continuous fun ω : Ω d =>
      quadVar d N (coefObsT d N E (List.ofFn σ)
        (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) u) (Hflow d N u ω) :=
    continuous_quadVar_Hflow hbdd.bddC2 u
  -- the two forms of `Ψ^Q₁`
  have hfun : (qUkerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a u)
      = coefObsT d N E (List.ofFn σ) (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) u :=
    funext fun M => qUkerObsT_eq_coefObsT E (List.ofFn σ) (xiOf (mSigma E) σ)
      ((v : ℝ) : ℂ) (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a u M
  have hY : ∀ ω : Ω d, Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a
      = coefObsT d N E (List.ofFn σ) (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) u (Hflow d N u ω) :=
    fun ω =>
      ((qUkerObsT_flow (band d) (sample d) E N σ a ((v : ℝ) : ℂ)
        (fun _ _ => rfl) u ω).symm).trans (congrFun hfun (Hflow d N u ω))
  have hYc : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖ := by
    have hrw : (fun ω : Ω d => ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)
        = fun ω : Ω d => ‖coefObsT d N E (List.ofFn σ)
            (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
            (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) u (Hflow d N u ω)‖ :=
      funext fun ω => by rw [hY ω]
    rw [hrw]
    exact (hbdd.contDiff.continuous.comp (continuous_Hflow d N u)).norm
  -- `Φ` is integrable
  have hcontT : Continuous fun ω : Ω d =>
      timeD1 (coefMomentObsT d N E (List.ofFn σ)
        (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
        (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p) u (Hflow d N u ω) :=
    (hT₁.contT u hmemI).comp (continuous_Hflow d N u)
  obtain ⟨CT, hCT⟩ := hT₁.bddT
  have hintT := integrable_of_continuous_of_bound hcontT (C := CT)
    fun ω => hCT u hmemI (Hflow d N u ω)
  have hslice := hT₁.slice hmemI
  rw [hphi]
  rw [hfun] at hQV
  refine integral_le_holder_sum_of_bdd (d := d) hp (CG := CG) (cq := cq)
    (hintT.re.add (integrable_genMomentPt hslice u))
    hYc hG₁c hG₂c hG₃c hQc hgc
    (fun ω => by rw [abs_norm, hY ω]; exact hbdd.bdd₀ _)
    (fun ω => by rw [abs_norm]; exact hG₁b ω)
    (fun ω => by rw [abs_norm]; exact hG₂b ω) (fun ω => by rw [abs_norm]; exact hG₃b ω)
    (fun ω => by rw [abs_norm]; exact hgb ω)
    (fun ω => quadVar_nonneg _ _) hcq hQV ?_
  have hring : ∀ A B₁ B₂ B₃ Q : ℝ,
      2 * (p : ℝ) * (A ^ (2 * p - 1) * B₁ + A ^ (2 * p - 1) * B₂ + A ^ (2 * p - 1) * B₃)
          + (p : ℝ) * (2 * (p : ℝ) - 1) * (A ^ (2 * p - 2) * Q)
        = 2 * (p : ℝ) * A ^ (2 * p - 1) * (B₁ + B₂ + B₃)
          + (p : ℝ) * (2 * (p : ℝ) - 1) * A ^ (2 * p - 2) * Q :=
    fun A B₁ B₂ B₃ Q => by ring
  intro ω
  simp only [abs_norm]
  rw [← hfun, ← hΨeq, hring]
  exact timeD1_add_genMomentPt_le_driftFQ_flow (band d) (sample d) E N hE
    (hs0.trans hu.1.le) (hu.2.trans hv1) (hs0.trans (hu.1.trans hu.2).le) hv1 σ a ω hp

/-- **The `hbound` slot verbatim**, i.e. `RBM.Gauss.hbound_qMomentObsT_gauss` at `cq = 1`:
the right-hand side is now literally the one
`RBM.MomentDuhamel.momentIneqQ_of_derivBound` asks for, with no constant in front of the
`E ⊗ E` moment norm. -/
theorem hbound_qMomentObsT_gauss_one (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) {p : ℕ} (hp : 1 ≤ p) {u : ℝ} (hu : u ∈ Set.Ioo s v)
    {CG : ℝ}
    (hG₁c : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖)
    (hG₁b : ∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖ ≤ CG)
    (hG₂c : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)
    (hG₂b : ∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖ ≤ CG)
    (hG₃c : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) u b) a‖)
    (hG₃b : ∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) u b) a‖ ≤ CG)
    (hgc : Continuous fun ω : Ω d =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)) (Fin.append a a)‖)
    (hgb : ∀ ω : Ω d, ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
          (Fin.append a a)‖ ≤ CG)
    (hQV : ∀ ω : Ω d, quadVar d N (qUkerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
          ((v : ℝ) : ℂ) (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a u)
          (Hflow d N u ω)
        ≤ ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
            (Fin.append a a)‖) :
    phiCoefDeriv d N E (List.ofFn σ)
          (qCoefFam (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a)
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) p u
      ≤ 2 * (p : ℝ)
            * (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
                  ^ (2 * p) ∂(P d)) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
            * (MomentDuhamel.momNorm (P d) (2 * p) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (Qop (d.L N) ((u : ℝ) : ℂ)
                      (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖)
              + MomentDuhamel.momNorm (P d) (2 * p) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                      (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)
              + MomentDuhamel.momNorm (P d) (2 * p) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
                      * SumZeroDyn.varthetaDot (d.L N) u b) a‖))
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
                  ^ (2 * p) ∂(P d)) ^ (((p : ℝ) - 1) / (p : ℝ))
            * MomentDuhamel.momNorm (P d) p (fun ω =>
                ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
                    (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
                  (Fin.append a a)‖) := by
  have h := hbound_qMomentObsT_gauss E N hE hs0 hv1 σ a hp hu (cq := 1) (CG := CG)
    zero_le_one hG₁c hG₁b hG₂c hG₂b hG₃c hG₃b hgc hgb
    (fun ω => by rw [one_mul]; exact hQV ω)
  rwa [one_mul] at h


/-! ### Satisfiability: how much time regularity the coefficient family really needs

The coefficient family enters `RBM.Gauss.testFunT₁_coefMomentObsT` through exactly three
hypotheses — `hc` (one `HasDerivAt` in `u`), `hcb` and `hc'b` (bounds on it and on that one
derivative).  **One** time derivative, used **once**, in `RBM.Gauss.hasDerivAt_coefObsT`; the
second derivative of the family appears nowhere, and neither does continuity of `u ↦ c u b`
beyond what `hc` already gives.  T191 showed that asking `RBM.Gauss.TestFunT` for a *second*
time derivative was an over-requirement; the same accident on the coefficient family is ruled
out here, and compiled:

* `RBM.Gauss.testFunT₁_coefMomentObsT_kink` — the class **contains** the family
  `c_u = (u - ½)|u - ½|`;
* `RBM.Gauss.not_differentiableAt_kinkCoefFam'` — that family is **not** `C²` in the time.

Together they show the `C¹` order is strict: a `C²` version of
`RBM.Gauss.testFunT₁_coefMomentObsT` would be a theorem about a strictly smaller class, and
`RBM.Gauss.qCoefFam` itself is only ever differentiated once
(`RBM.SumZeroDyn.hasDerivAt_vartheta`; `RBM.SumZeroDyn.varthetaDot` is nowhere
differentiated).

The **positive** witnesses that the class is not empty are `RBM.Gauss.ukerObsT_eq_coefObsT`
and `RBM.Gauss.qUkerObsT_eq_coefObsT`: both routes are genuine members, the first by `rfl`.
No `∀ M` here is a disguised `∀ M, M.IsHermitian → …`: `RBM.Gauss.loopObs` carries
`RBM.Gauss.hermCLM`, so the envelope of `RBM.Gauss.norm_lk_sub_le` is attained at
non-Hermitian matrices too, exactly as T196 checked. -/

/-- A coefficient family that is `C¹` in the time and **not** `C²`. -/
noncomputable def kinkCoefFam (d : Dims) (N : ℕ) (m : ℕ) :
    ℝ → LoopArg (d.L N) m → ℂ :=
  fun u _ => (((u - 1 / 2) * |u - 1 / 2| : ℝ) : ℂ)

/-- Its (only) time derivative. -/
noncomputable def kinkCoefFam' (d : Dims) (N : ℕ) (m : ℕ) :
    ℝ → LoopArg (d.L N) m → ℂ :=
  fun u _ => (((2 * |u - 1 / 2| : ℝ)) : ℂ)

theorem hasDerivAt_kinkCoefFam (m : ℕ) (u : ℝ) (b : LoopArg (d.L N) m) :
    HasDerivAt (fun r : ℝ => kinkCoefFam d N m r b) (kinkCoefFam' d N m u b) u :=
  (hasDerivAt_kink u).ofReal_comp

theorem norm_kinkCoefFam_le {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (m : ℕ)
    (b : LoopArg (d.L N) m) : ‖kinkCoefFam d N m u b‖ ≤ 1 := by
  have h1 : |u - 1 / 2| ≤ 1 := by
    rcases hu with ⟨h0, h1⟩; rw [abs_le]; constructor <;> linarith
  have h0 : (0 : ℝ) ≤ |u - 1 / 2| := abs_nonneg _
  simp only [kinkCoefFam, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_abs]
  nlinarith

theorem norm_kinkCoefFam'_le {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (m : ℕ)
    (b : LoopArg (d.L N) m) : ‖kinkCoefFam' d N m u b‖ ≤ 2 := by
  have h1 : |u - 1 / 2| ≤ 1 := by
    rcases hu with ⟨h0, h1⟩; rw [abs_le]; constructor <;> linarith
  simp only [kinkCoefFam', Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  linarith

/-- **The derivative of the kinked family is not differentiable at `u = ½`**: the family is
`C¹` and not `C²` in the time. -/
theorem not_differentiableAt_kinkCoefFam' (m : ℕ) (b : LoopArg (d.L N) m) :
    ¬ DifferentiableAt ℝ (fun r : ℝ => kinkCoefFam' d N m r b) (1 / 2) := by
  intro h
  have hre : DifferentiableAt ℝ (fun r : ℝ => 2 * |r - 1 / 2|) (1 / 2) := by
    have h2 := (Complex.reCLM.differentiableAt).comp (1 / 2 : ℝ) h
    simpa [kinkCoefFam', Function.comp_def] using h2
  have habs : DifferentiableAt ℝ (fun r : ℝ => |r - 1 / 2|) (1 / 2) := by
    have := hre.const_mul (2 : ℝ)⁻¹
    refine this.congr_of_eventuallyEq ?_
    filter_upwards with r using by ring
  have h0 : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    have hadd : DifferentiableAt ℝ (fun y : ℝ => y + 1 / 2) 0 :=
      differentiableAt_id.add_const _
    have hcomp : DifferentiableAt ℝ
        ((fun r : ℝ => |r - 1 / 2|) ∘ (fun y : ℝ => y + 1 / 2)) 0 :=
      DifferentiableAt.comp 0 (by simpa using habs) hadd
    have heq : (abs : ℝ → ℝ) = (fun r : ℝ => |r - 1 / 2|) ∘ (fun y : ℝ => y + 1 / 2) := by
      funext y; simp
    rw [heq]; exact hcomp
  exact not_differentiableAt_abs_zero h0

/-- **The generalised class contains the kinked family** — so the `C¹` hypothesis `hc` of
`RBM.Gauss.testFunT₁_coefMomentObsT` is the right order: asking the coefficient family for a
*second* time derivative would already exclude this `Ψ`, which the theorem covers. -/
theorem testFunT₁_coefMomentObsT_kink (E : ℝ) (N : ℕ) (hE : |E| < 2) {v : ℝ} (hv1 : v < 1)
    {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (K K' : ℝ → LoopArg (d.L N) m → ℂ) (p : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hK : ∀ u ∈ Set.Icc (0 : ℝ) v, ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (hKb : ∀ u ∈ Set.Icc (0 : ℝ) v, ∀ b, ‖K u b‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc (0 : ℝ) v, ∀ b, ‖K' u b‖ ≤ cK) :
    TestFunT₁ d N (Set.Icc (0 : ℝ) v) (coefMomentObsT d N E σ (kinkCoefFam d N m) K p) :=
  testFunT₁_coefMomentObsT E hσ hm _ (kinkCoefFam' d N m) K K' p
    (window_eta_pos hE hv1) (by norm_num : (0 : ℝ) ≤ 2) hcK (window_le_abs_im hE hv1)
    (fun u _ b => hasDerivAt_kinkCoefFam m u b)
    (fun u hu b => le_trans (norm_kinkCoefFam_le ⟨hu.1, hu.2.trans hv1.le⟩ m b)
      (by norm_num))
    (fun u hu b => norm_kinkCoefFam'_le ⟨hu.1, hu.2.trans hv1.le⟩ m b)
    hK hKb hK'b

end Gauss

end RBM

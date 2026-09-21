/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelHypGauss
import RBM1D.Gauss.Lemma514Q716

/-!
# The `Q_t` route of (5.91): the drift side of `MomentIneqQ` (T214)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5, equations (5.88)–(5.91), (5.99), (5.100).

`RBM.MomentDuhamel.MomentIneqQ` is the second outstanding obligation of
`RBM.MomentDuhamel.Hyp`.  Its drift side needs `∂_u Q_u`, which produces the two extra terms
`RBM.SumZeroDyn.commS` (5.99) and `RBM.SumZeroDyn.varthetaDot` (5.100) that the plain route
(5.20) does not have.  This file supplies that drift side, in the same pinned form in which
T206 (`RBM1D/Gauss/MomentDuhamelHypGauss.lean`) supplied the drift side of
`RBM.MomentDuhamel.MomentIneq`.

## Correction to the T214 ticket (and to `MomentDuhamelHypGauss`'s docstring, item 3)

The ticket says "the repository contains nothing that differentiates `RBM.Qop` in the time"
and that `RBM.SumZeroDyn.hasDerivAt_Qop_hierarchy` "differentiates in the hierarchy, not in
`u`".  **Both claims are false.**  `RBM1D/Hierarchy/SumZeroDyn.lean` already has

* `RBM.SumZeroDyn.hasDerivAt_Qop` — `∂_t (Q_t ∘ A_t) = Q_t ∘ ∂_tA_t - (P ∘ A_t) ϑ̇_t`, literally
  `HasDerivAt (fun u : ℝ => Qop L (u : ℂ) (A u) a) … t`;
* `RBM.SumZeroDyn.hasDerivAt_Qop_hierarchy` — **(5.88)**, the same statement fed with
  `∂_tD_t = Θ_{t,σ}D_t + F_t`, whose derivative already displays `commS` and `varthetaDot`.

What was genuinely missing is the **propagator-conjugated, matrix-generator** form: the `Q_t`
twin of `RBM.Gauss.hasDerivAt_ukerObsT_drift`, i.e. the identity satisfied by
`Ψ^Q(u, M) = (U_{u,v} ∘ Q_u (L - K)_u)_a` under `∂_u + 𝓛`.  That is what this file adds.

## Main results

* `RBM.Gauss.genD_Qop`, `RBM.Gauss.genD_Uker_Qop` — `𝓛` passes through `Q_u` and through
  `U_{u,v} ∘ Q_u`, both being finite ℂ-linear combinations with matrix-independent
  coefficients.  (T206's `RBM.Gauss.genD_finsetSum` is the engine.)
* `RBM.Gauss.qUkerObsT` — `Ψ^Q(u, M) = (U_{u,v} ∘ Q_u (L - K)_u)_a`, with the running time in
  **four** places now: the spectral parameter `z_u`, the propagator `U_{u,v}`, the primitive
  `K_u` and the projector `Q_u` itself.
* `RBM.Gauss.hasDerivAt_qUkerObsT_drift` — **the drift identity of (5.91)**:

    `(∂_u + 𝓛) Ψ^Q = (U ∘ Q_uF_u)_a + (U ∘ [Q_u, Θ_{u,σ}](L-K)_u)_a
                        - (U ∘ (P(L-K)_u)_{b₀} ϑ̇_{u,b})_a`,

  with `F = RBM.DriftDef.driftF` pinned by T58 — the three drift integrands of
  `RBM.MomentDuhamel.MomentIneqQ`, in that order, and nothing else.
* `RBM.Gauss.timeD1_add_genMomentPt_le_driftFQ` — the pointwise integrand of (5.91):

    `∂_u|Ψ^Q|^{2p} + 𝓛|Ψ^Q|^{2p} ≤ 2p|Ψ^Q|^{2p-1}(‖U∘Q_uF‖ + ‖U∘commS‖ + ‖U∘Pϑ̇‖)
        + p(2p-1)|Ψ^Q|^{2p-2} quadVar(Ψ^Q)`,

  the shape `RBM.MomentDuhamel.momentIneqQ_of_derivBound` integrates.  As in T206 the two
  first-order terms are added **before** the modulus is taken: bounding `∂_uΨ^Q` and `𝓛Ψ^Q`
  separately would leave `U ∘ Θ_u(Q_u(L-K))`, which is not small.
* `RBM.MomentDuhamel.QIntegrable`, `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` — the `Q_t`
  twin of `RBM.MomentDuhamel.stochDom_of_momentDuhamel`: the consumer that makes the field
  `RBM.MomentDuhamel.Hyp.momentDuhamelQ` (which T195/T201 found had **none**) produce a `≺`.
  `RBM.MomentDuhamel.qIntegrable_gauss` discharges its one extra hypothesis on the Gaussian
  model.

## Satisfiability

* the drift is **pinned**: `RBM.DriftDef.driftF`, `RBM.SumZeroDyn.commS` and
  `RBM.SumZeroDyn.varthetaDot` are definitions, `K` is `RBM.Band.Kval` by the hypothesis
  `hKdef` and `∂_uK` is `RBM.Gauss.Kprim`.  Nothing on either side is data a caller chooses;
* `RBM.Gauss.hasDerivAt_qUkerObsT_drift_flow` discharges every side condition from the paper's
  standing assumptions `|E| < 2`, `0 ≤ u < 1`, `0 ≤ v < 1` at the flow matrix, the critical
  scaling with `v ↑ 1` allowed;
* `RBM.Gauss.hasDerivAt_qUkerObsT_drift_at_zero` is the mandatory `ω = 0` degenerate check;
* `RBM.MomentDuhamel.Qop_ne_zero_witness` shows `Q_u` is **not** the zero operator on the
  tensors the five terms speak about, so the bounds are not vacuously about `0` (it is T201's
  `RBM.Gauss.witTensor`, which `Q_u` fixes).

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ}

/-! ### `𝓛` passes through `Q_u`

`Q_t A b = A b - (∑_r A (Fin.cons (b 0) r)) ϑ_{t,b}` is a finite ℂ-linear combination of the
values of `A` with coefficients that do not depend on the matrix, so `RBM.Gauss.genD` goes
through it exactly as it goes through `RBM.Uker` (T206's `RBM.Gauss.genD_finsetSum`).  The
index set of the combination is `Option (LoopArg L n)`: `none` carries the value at `b`
itself, `some r` the `r`-th summand of `RBM.Psum`. -/

/-- The coefficients of `Q_t` at the slot `b`, as a function on `Option (LoopArg L n)`. -/
private noncomputable def qCoef (L : ℕ) [NeZero L] {n : ℕ} (t : ℂ) (b : LoopArg L (n + 1)) :
    Option (LoopArg L n) → ℂ
  | none => 1
  | some _ => -vartheta L t b

/-- The tensors of `Q_t` at the slot `b`, as a function on `Option (LoopArg L n)`. -/
private def qArg {L : ℕ} [NeZero L] {n : ℕ} {α : Type*} (Y : α → LoopArg L (n + 1) → ℂ)
    (b : LoopArg L (n + 1)) : Option (LoopArg L n) → α → ℂ
  | none => fun M' => Y M' b
  | some r => fun M' => Y M' (Fin.cons (b 0) r)

private theorem qop_eq_sum {L : ℕ} [NeZero L] {n : ℕ} {α : Type*} (t : ℂ)
    (Y : α → LoopArg L (n + 1) → ℂ) (b : LoopArg L (n + 1)) (M' : α) :
    ∑ i : Option (LoopArg L n), qCoef L t b i * qArg Y b i M' = Qop L t (Y M') b := by
  classical
  rw [Fintype.sum_option]
  have h1 : ∑ r : LoopArg L n, qCoef L t b (some r) * qArg Y b (some r) M'
      = -(vartheta L t b * Psum L (Y M') (b 0)) := by
    simp only [qCoef, qArg, Psum, Finset.mul_sum, ← Finset.sum_neg_distrib, neg_mul]
  have h0 : qCoef L t b none * qArg Y b none M' = Y M' b := by
    simp only [qCoef, qArg, one_mul]
  rw [h0, h1]
  show _ = Y M' b - Psum L (Y M') (b 0) * vartheta L t b
  ring

/-- `Q_t` of a family of `C²` functions of the matrix is `C²`. -/
theorem contDiff_Qop {n : ℕ} (t : ℂ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ → LoopArg (d.L N) (n + 1) → ℂ)
    (hY : ∀ b, ContDiff ℝ 2 (fun M' => Y M' b)) (b : LoopArg (d.L N) (n + 1)) :
    ContDiff ℝ 2 (fun M' => Qop (d.L N) t (Y M') b) := by
  classical
  have hfun : (fun M' => Qop (d.L N) t (Y M') b)
      = fun M' => ∑ i : Option (LoopArg (d.L N) n),
          qCoef (d.L N) t b i * qArg Y b i M' :=
    funext fun M' => (qop_eq_sum t Y b M').symm
  rw [hfun]
  refine ContDiff.sum fun i _ => contDiff_const.mul ?_
  cases i with
  | none => exact hY b
  | some r => exact hY (Fin.cons (b 0) r)

/-- **`RBM.Gauss.genD` through `RBM.Qop`.**  `Q_t` is a deterministic linear operator on the
tensor slot, so the matrix generator does not see it. -/
theorem genD_Qop {n : ℕ} (t : ℂ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ → LoopArg (d.L N) (n + 1) → ℂ)
    (hY : ∀ b, ContDiff ℝ 2 (fun M' => Y M' b))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (b : LoopArg (d.L N) (n + 1)) :
    genD d N (fun M' => Qop (d.L N) t (Y M') b) M
      = Qop (d.L N) t (fun b' => genD d N (fun M' => Y M' b') M) b := by
  classical
  have hfun : (fun M' => Qop (d.L N) t (Y M') b)
      = fun M' => ∑ i ∈ (Finset.univ : Finset (Option (LoopArg (d.L N) n))),
          qCoef (d.L N) t b i * qArg Y b i M' :=
    funext fun M' => (qop_eq_sum t Y b M').symm
  have hC2 : ∀ i ∈ (Finset.univ : Finset (Option (LoopArg (d.L N) n))),
      ContDiff ℝ 2 (qArg Y b i) := by
    intro i _
    cases i with
    | none => exact hY b
    | some r => exact hY (Fin.cons (b 0) r)
  rw [hfun, genD_finsetSum _ _ _ hC2 M]
  have hstep : ∀ i : Option (LoopArg (d.L N) n),
      qCoef (d.L N) t b i * genD d N (qArg Y b i) M
        = qCoef (d.L N) t b i
            * qArg (fun (_ : Matrix (d.Idx N) (d.Idx N) ℂ) b' =>
                genD d N (fun M'' => Y M'' b') M) b i M := by
    intro i; cases i <;> rfl
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  exact qop_eq_sum t (fun (_ : Matrix (d.Idx N) (d.Idx N) ℂ) b' =>
    genD d N (fun M'' => Y M'' b') M) b M

/-- **`RBM.Gauss.genD` through `U_{u,v} ∘ Q_u`**, the composite that (5.91) puts under the
moment.  Both operators are deterministic and linear in the tensor. -/
theorem genD_Uker_Qop {n : ℕ} (ξ : Fin (n + 1) → ℂ) (s r : ℂ) (t : ℂ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ → LoopArg (d.L N) (n + 1) → ℂ)
    (hY : ∀ b, ContDiff ℝ 2 (fun M' => Y M' b))
    (a : LoopArg (d.L N) (n + 1)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genD d N (fun M' => Uker (d.L N) ξ s r (Qop (d.L N) t (Y M')) a) M
      = Uker (d.L N) ξ s r (Qop (d.L N) t (fun b => genD d N (fun M' => Y M' b) M)) a := by
  classical
  have hfun : (fun M' => Uker (d.L N) ξ s r (Qop (d.L N) t (Y M')) a)
      = fun M' => ∑ b : LoopArg (d.L N) (n + 1),
          (∏ i, edgeKer (d.L N) (ξ i) s r (a i) (b i)) * Qop (d.L N) t (Y M') b := rfl
  rw [hfun, genD_finsetSum _ _ _ (fun b _ => contDiff_Qop t Y hY b) M, Uker_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [genD_Qop t Y hY M b]


/-! ### The `Q_t`-projected observable

`Ψ^Q(u, M) = (U_{u,v} ∘ Q_u (L - K)_u)_a` has the running time in **four** places: the
spectral parameter `z_u` inside the loop, the running time of the propagator `U_{u,v}`, the
primitive `K_u`, and — new in the `Q_t` route — the projector `Q_u` itself, through
`RBM.vartheta`.  The fourth is the source of the `ϑ̇` term of (5.100). -/

/-- `(U_{u,v} ∘ Q_u (L - K)_u)_a` as a function of the running time and the matrix. -/
noncomputable def qUkerObsT (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin (m + 1) → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ)
    (a : LoopArg (d.L N) (m + 1)) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Uker (d.L N) ξ ((u : ℝ) : ℂ) t
    (Qop (d.L N) ((u : ℝ) : ℂ)
      (fun b => loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b)) a

/-- `Ψ^Q(u, M) = |(U_{u,v} ∘ Q_u (L - K)_u)_a|^{2p}`, in the `RBM.Gauss.momentFun` form. -/
noncomputable def qMomentObsT (d : Dims) (N : ℕ) (Ev : ℝ) (σ : List Bool) {m : ℕ}
    (ξ : Fin (m + 1) → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ)
    (a : LoopArg (d.L N) (m + 1)) (p : ℕ) :
    ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  fun u M => momentFun (qUkerObsT d N Ev σ ξ t K a u) p M

theorem qMomentObsT_eq (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin (m + 1) → ℂ) (t : ℂ)
    (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ) (a : LoopArg (d.L N) (m + 1)) (p : ℕ)
    (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    qMomentObsT d N Ev σ ξ t K a p u M
      = (qUkerObsT d N Ev σ ξ t K a u M
          * (starRingEnd ℂ) (qUkerObsT d N Ev σ ξ t K a u M)) ^ p := by
  simp only [qMomentObsT, momentFun]

/-- `Ψ^Q` is `C²` in the matrix: it is a finite `ℂ`-linear combination of loop observables. -/
theorem contDiff_qUkerObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m + 1)
    (ξ : Fin (m + 1) → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ)
    (a : LoopArg (d.L N) (m + 1)) {u : ℝ} (hz : (zt Ev u).im ≠ 0) :
    ContDiff ℝ 2 (qUkerObsT d N Ev σ ξ t K a u) := by
  classical
  have hwf : ∀ b : LoopArg (d.L N) (m + 1), (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hY : ∀ b : LoopArg (d.L N) (m + 1),
      ContDiff ℝ 2 (fun M' => loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M' - K u b) :=
    fun b => (bddC2_loopObs hz (abs_pos.mpr hz) le_rfl (hwf b)).contDiff.sub contDiff_const
  have hfun : qUkerObsT d N Ev σ ξ t K a u
      = fun M' => ∑ b : LoopArg (d.L N) (m + 1),
          (∏ i, edgeKer (d.L N) (ξ i) ((u : ℝ) : ℂ) t (a i) (b i))
            * Qop (d.L N) ((u : ℝ) : ℂ)
                (fun b' => loopObs d N (zt Ev u) ⟨σ, List.ofFn b'⟩ M' - K u b') b := rfl
  rw [hfun]
  exact ContDiff.sum fun b _ => contDiff_const.mul (contDiff_Qop _ _ hY b)

/-- **`RBM.Gauss.genD` of `Ψ^Q`**: the generator passes through both `U_{u,v}` and `Q_u`. -/
theorem genD_qUkerObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m + 1)
    (ξ : Fin (m + 1) → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ)
    (a : LoopArg (d.L N) (m + 1)) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genD d N (qUkerObsT d N Ev σ ξ t K a u) M
      = Uker (d.L N) ξ ((u : ℝ) : ℂ) t
          (Qop (d.L N) ((u : ℝ) : ℂ) (fun b =>
            genD d N (fun M' => loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M' - K u b) M)) a := by
  classical
  have hwf : ∀ b : LoopArg (d.L N) (m + 1), (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hY : ∀ b : LoopArg (d.L N) (m + 1),
      ContDiff ℝ 2 (fun M' => loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M' - K u b) :=
    fun b => (bddC2_loopObs hz (abs_pos.mpr hz) le_rfl (hwf b)).contDiff.sub contDiff_const
  have hfun : qUkerObsT d N Ev σ ξ t K a u
      = fun M' => Uker (d.L N) ξ ((u : ℝ) : ℂ) t
          (Qop (d.L N) ((u : ℝ) : ℂ)
            (fun b => loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M' - K u b)) a := rfl
  rw [hfun]
  exact genD_Uker_Qop ξ _ _ _ _ hY a M

/-! ### The propagator-conjugated drift identity of (5.91)

`(∂_u + 𝓛) Ψ^Q` is read off three inputs, exactly as in T206:

* `RBM.hasDerivAt_Uker_path` gives `∂_u(U ∘ Y_u) = U ∘ (Y'_u - Θ_u Y_u)`;
* `RBM.SumZeroDyn.hasDerivAt_Qop` gives `∂_u(Q_u ∘ A_u) = Q_u ∘ A'_u - (P ∘ A_u) ϑ̇_u`, which is
  where (5.100) comes from;
* `RBM.DriftDef.drift_split_gen` (T58) gives `(L-K)' + 𝓛(L-K) = Θ_u(L-K) + F`.

`Q_u` does **not** commute with `Θ_{u,σ}`; the defect is `RBM.SumZeroDyn.commS`, which is
(5.99).  That is the only difference from the plain route. -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A pointwise identity between tensors is inherited by `U_{s,t}`, in the exact three-on-three
shape the drift identity produces. -/
private theorem uker_comb6 (L : ℕ) [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ)
    (Z₁ Z₂ Z₃ Z₄ Z₅ Z₆ : LoopArg L n → ℂ) (a : LoopArg L n)
    (h : ∀ b, Z₁ b - Z₂ b + Z₃ b = Z₄ b + Z₅ b - Z₆ b) :
    Uker L ξ s t Z₁ a - Uker L ξ s t Z₂ a + Uker L ξ s t Z₃ a
      = Uker L ξ s t Z₄ a + Uker L ξ s t Z₅ a - Uker L ξ s t Z₆ a := by
  simp only [Uker_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by
    linear_combination (∏ i, edgeKer L (ξ i) s t (a i) (b i)) * h b

/-- **The bridge `RBM.Gauss.qUkerObsT ↔ U ∘ Q_u ∘ RBM.MomentDuhamel.lkFun`**, at a Hermitian
matrix, where the regularisation inside `RBM.Gauss.loopObs` is the identity. -/
theorem qUkerObsT_eq_Uker_Qop_lkFun (B : Band Ω) (E : ℝ) (N : ℕ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (r : ℝ) :
    qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a r M
      = Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
          (Qop (B.L N) ((r : ℝ) : ℂ) (MomentDuhamel.lkFun B E N r M σ)) a := by
  have hval : (fun b : LoopArg (B.L N) (n + 2) =>
        loopObs B.toDims N (zt E r) ⟨List.ofFn σ, List.ofFn b⟩ M - K r b)
      = MomentDuhamel.lkFun B E N r M σ := by
    funext b
    have h : loopObs B.toDims N (zt E r) (LoopData.idx (σ, b)) M
        = gloop (B.L N) (B.W N) M (zt E r) (LoopData.idx (σ, b)) :=
      loopObs_of_isHermitian hM
    rw [hKdef r b]
    exact congrArg (fun x => x - B.Kval E N r (LoopData.idx (σ, b))) h
  change Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
      (Qop (B.L N) ((r : ℝ) : ℂ) (fun b =>
        loopObs B.toDims N (zt E r) ⟨List.ofFn σ, List.ofFn b⟩ M - K r b)) a = _
  rw [hval]

/-- **The bridge along the flow.** -/
theorem qUkerObsT_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (u : ℝ) (ω : Ω) :
    qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u (X.H N u ω)
      = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
          (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a :=
  qUkerObsT_eq_Uker_Qop_lkFun B E N σ a t hKdef (X.hermitian N u ω) u

/-- **`Ψ^Q` along the flow is `|(U_{u,v} ∘ Q_u (L-K)_u)_a|^{2p}`**, the integrand of
`RBM.MomentDuhamel.MomentIneqQ`. -/
theorem qMomentObsT_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (p : ℕ) (u : ℝ) (ω : Ω) :
    qMomentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a p u (X.H N u ω)
      = ((|‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
            (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖| ^ (2 * p) : ℝ) : ℂ) := by
  have h0 : qMomentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a p u (X.H N u ω)
      = (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u (X.H N u ω)
          * (starRingEnd ℂ)
              (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u
                (X.H N u ω))) ^ p :=
    qMomentObsT_eq _ _ _ _ _ _ _ _ _
  rw [h0, qUkerObsT_flow B X E N σ a t hKdef u ω, mul_conj_eq,
    ← Complex.ofReal_pow, ← pow_mul, abs_norm]

/-- **The drift identity of (5.91).**

`Ψ^Q(u, M) = (U_{u,v} ∘ Q_u (L - K)_u)_a` satisfies

  `(∂_u + 𝓛) Ψ^Q = (U ∘ Q_uF_u)_a + (U ∘ [Q_u, Θ_{u,σ}](L-K)_u)_a
      - (U ∘ (P(L-K)_u)_{b₀} ϑ̇_{u,b})_a`,

with `F = RBM.DriftDef.driftF` — the three drift integrands of
`RBM.MomentDuhamel.MomentIneqQ`, in order.  Nothing on either side is data a caller may
choose: `K` is pinned to `RBM.Band.Kval` by `hKdef`, `F` by T58, and `commS` / `varthetaDot`
are definitions. -/
theorem hasDerivAt_qUkerObsT_drift (B : Band Ω) (E : ℝ) (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (hv : ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (ht : ∀ i, ‖t * xiOf (mSigma E) σ i‖ < 1) :
    ∃ D : ℂ,
      HasDerivAt (fun r : ℝ =>
          qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a r M) D u
        ∧ D + genD B.toDims N
              (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u) M
          = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u M σ)) a
            + Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (MomentDuhamel.lkFun B E N u M σ)) a
            - Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                (fun b => Psum (B.L N) (MomentDuhamel.lkFun B E N u M σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a := by
  classical
  set ξ : Fin (n + 2) → ℂ := xiOf (mSigma E) σ with hξ
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hlen : (List.ofFn σ).length = n + 2 := List.length_ofFn
  -- at a Hermitian matrix the regularised observable is the raw `Q_u ∘ (L - K)`
  have hEq : ∀ r : ℝ,
      qUkerObsT B.toDims N E (List.ofFn σ) ξ t K a r M
        = Uker (B.L N) ξ ((r : ℝ) : ℂ) t
            (Qop (B.L N) ((r : ℝ) : ℂ) (MomentDuhamel.lkFun B E N r M σ)) a :=
    fun r => qUkerObsT_eq_Uker_Qop_lkFun B E N σ a t hKdef hM r
  -- T58: the pointwise drift identity, with `F = driftF`
  choose dv hdv hdveq using fun b : LoopArg (B.L N) (n + 2) =>
    DriftDef.drift_split_gen B E N u hM hz σ b hm
  -- (5.88): the time derivative of `Q_u ∘ (L - K)_u`
  have hQd : ∀ b : LoopArg (B.L N) (n + 2),
      HasDerivAt (fun r : ℝ => Qop (B.L N) ((r : ℝ) : ℂ) (MomentDuhamel.lkFun B E N r M σ) b)
        (Qop (B.L N) ((u : ℝ) : ℂ) dv b
          - Psum (B.L N) (MomentDuhamel.lkFun B E N u M σ) (b 0)
              * SumZeroDyn.varthetaDot (B.L N) u b) u :=
    fun b => SumZeroDyn.hasDerivAt_Qop (B.L N) hL3 hu0 hu1 hdv b
  have hpath := hasDerivAt_Uker_path (B.L N) hL3 hv ht (Y := fun r =>
    Qop (B.L N) ((r : ℝ) : ℂ) (MomentDuhamel.lkFun B E N r M σ))
    (Y' := fun b => Qop (B.L N) ((u : ℝ) : ℂ) dv b
      - Psum (B.L N) (MomentDuhamel.lkFun B E N u M σ) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) u b) hQd a
  -- the generator term, pushed through `U` and `Q`
  have hgen : genD B.toDims N (qUkerObsT B.toDims N E (List.ofFn σ) ξ t K a u) M
      = Uker (B.L N) ξ ((u : ℝ) : ℂ) t
          (Qop (B.L N) ((u : ℝ) : ℂ) (MomentDuhamel.genLK B E N u M σ)) a := by
    rw [genD_qUkerObsT E hlen ξ t K a hz M]
    refine congrArg (fun Z => Uker (B.L N) ξ ((u : ℝ) : ℂ) t Z a) ?_
    refine congrArg (fun Z => Qop (B.L N) ((u : ℝ) : ℂ) Z) ?_
    funext b
    exact genD_loopObs_eq_genLK B E N u hM hz σ b (K u b)
  refine ⟨_, hpath.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hEq r), ?_⟩
  rw [hgen]
  -- the algebra: `Q_u(dv + 𝓛(L-K)) = Q_u(Θ_u(L-K) + F)` and `[Q_u, Θ_u]` is the defect
  refine uker_comb6 (B.L N) ξ _ t _ _ _ _ _ _ a fun b => ?_
  have hQsum : Qop (B.L N) ((u : ℝ) : ℂ) dv b
        + Qop (B.L N) ((u : ℝ) : ℂ) (MomentDuhamel.genLK B E N u M σ) b
      = Qop (B.L N) ((u : ℝ) : ℂ)
            (ThetaOp (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ)) b
        + Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u M σ) b := by
    have hfun : (dv + MomentDuhamel.genLK B E N u M σ : LoopArg (B.L N) (n + 2) → ℂ)
        = ThetaOp (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ)
          + DriftDef.driftF B E N u M σ := by
      funext b'
      have hb := hdveq b'
      have hgs : SumZeroDyn.genS (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ) b'
          = ThetaOp (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ) b' := rfl
      rw [hgs] at hb
      simpa only [Pi.add_apply] using hb
    have h2 := congrArg (fun Z => Qop (B.L N) ((u : ℝ) : ℂ) Z) hfun
    simp only [SumZeroDyn.Qop_add] at h2
    exact congrFun h2 b
  have hcomm : SumZeroDyn.commS (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ) b
      = Qop (B.L N) ((u : ℝ) : ℂ)
            (ThetaOp (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ)) b
        - ThetaOp (B.L N) ξ ((u : ℝ) : ℂ)
            (Qop (B.L N) ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ)) b := rfl
  rw [hcomm]
  linear_combination hQsum

end Band


/-! ### The time derivative of `Ψ^Q = |Ψ^Q₁|^{2p}`, in the real first-order form -/

/-- `RBM.Gauss.timeD1` of the `Q_t` route's `Ψ`, written as `2p‖Ψ^Q₁‖^{2p-2} Re(Ψ̄^Q₁ ∂_uΨ^Q₁)`
— the shape that pairs with `RBM.Gauss.genMomentPt_le_re`. -/
theorem timeD1_qMomentObsT_re (Ev : ℝ) (σ : List Bool) {m : ℕ} (ξ : Fin (m + 1) → ℂ) (t : ℂ)
    (K : ℝ → LoopArg (d.L N) (m + 1) → ℂ) (a : LoopArg (d.L N) (m + 1)) (p : ℕ) {u : ℝ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} {D : ℂ}
    (hD : HasDerivAt (fun r : ℝ => qUkerObsT d N Ev σ ξ t K a r M) D u) :
    timeD1 (qMomentObsT d N Ev σ ξ t K a p) u M
      = ((2 * (p : ℝ) * ‖qUkerObsT d N Ev σ ξ t K a u M‖ ^ (2 * p - 2)
          * ((starRingEnd ℂ) (qUkerObsT d N Ev σ ξ t K a u M) * D).re : ℝ) : ℂ) := by
  have hfun : (fun s : ℝ => qMomentObsT d N Ev σ ξ t K a p s M)
      = fun s : ℝ => (qUkerObsT d N Ev σ ξ t K a s M
          * (starRingEnd ℂ) (qUkerObsT d N Ev σ ξ t K a s M)) ^ p :=
    funext fun s => qMomentObsT_eq Ev σ ξ t K a p s M
  have hd : HasDerivAt (fun s : ℝ => qMomentObsT d N Ev σ ξ t K a p s M)
      ((p : ℂ) * (qUkerObsT d N Ev σ ξ t K a u M
            * (starRingEnd ℂ) (qUkerObsT d N Ev σ ξ t K a u M)) ^ (p - 1)
        * (D * (starRingEnd ℂ) (qUkerObsT d N Ev σ ξ t K a u M)
            + qUkerObsT d N Ev σ ξ t K a u M * (starRingEnd ℂ) D)) u := by
    rw [hfun]; exact hasDerivAt_momentFun_path hD p
  rw [timeD1_eq_of_hasDerivAt hd]
  set Ψ := qUkerObsT d N Ev σ ξ t K a u M with hΨ
  rw [mul_conj_eq Ψ, add_conj_mul D Ψ]
  have hpow : (((‖Ψ‖ ^ 2 : ℝ) : ℂ)) ^ (p - 1) = (((‖Ψ‖ ^ (2 * p - 2) : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_pow, ← pow_mul]
    congr 2
    omega
  rw [hpow]
  push_cast
  ring

section Band2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The pointwise integrand of (5.91), with the drift pinned.**

At a Hermitian matrix, with `Ψ^Q₁ = (U_{u,v} ∘ Q_u (L-K)_u)_a`,

  `∂_u|Ψ^Q₁|^{2p} + 𝓛|Ψ^Q₁|^{2p}
      ≤ 2p|Ψ^Q₁|^{2p-1}(‖U∘Q_uF‖ + ‖U∘[Q_u,Θ_{u,σ}](L-K)‖ + ‖U∘(P(L-K))ϑ̇‖)
        + p(2p-1)|Ψ^Q₁|^{2p-2} ∑_α S_α ‖∂_αΨ^Q₁‖²`,

the three first summands being exactly the three drift integrands of
`RBM.MomentDuhamel.MomentIneqQ`.  As in T206 the two first-order terms are added **before**
the modulus is taken; that is what makes the `Θ` of the propagator cancel against the `genS`
of the drift identity, leaving only the commutator `RBM.SumZeroDyn.commS`. -/
theorem timeD1_add_genMomentPt_le_driftFQ (B : Band Ω) (E : ℝ) (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    {p : ℕ} (hp : 1 ≤ p)
    (hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (hv : ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (ht : ∀ i, ‖t * xiOf (mSigma E) σ i‖ < 1) :
    (timeD1 (qMomentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a p) u M).re
        + genMomentPt B.toDims N
            (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u) p M
      ≤ 2 * (p : ℝ)
            * ‖qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u M‖ ^ (2 * p - 1)
            * (‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                  (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u M σ)) a‖
              + ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                  (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                    (MomentDuhamel.lkFun B E N u M σ)) a‖
              + ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                  (fun b => Psum (B.L N) (MomentDuhamel.lkFun B E N u M σ) (b 0)
                    * SumZeroDyn.varthetaDot (B.L N) u b) a‖)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * ‖qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u M‖ ^ (2 * p - 2)
            * quadVar B.toDims N
                (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u) M := by
  classical
  set ξ : Fin (n + 2) → ℂ := xiOf (mSigma E) σ with hξ
  have hlen : (List.ofFn σ).length = n + 2 := List.length_ofFn
  set Ψ := qUkerObsT B.toDims N E (List.ofFn σ) ξ t K a u M with hΨ
  set G₁ := Uker (B.L N) ξ ((u : ℝ) : ℂ) t
      (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u M σ)) a with hG₁
  set G₂ := Uker (B.L N) ξ ((u : ℝ) : ℂ) t
      (SumZeroDyn.commS (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ)) a with hG₂
  set G₃ := Uker (B.L N) ξ ((u : ℝ) : ℂ) t
      (fun b => Psum (B.L N) (MomentDuhamel.lkFun B E N u M σ) (b 0)
        * SumZeroDyn.varthetaDot (B.L N) u b) a with hG₃
  obtain ⟨D, hD, hDeq⟩ :=
    hasDerivAt_qUkerObsT_drift B E N hu0 hu1 hM hz σ a t hKdef hm hv ht
  have hC2 : ContDiff ℝ 2 (qUkerObsT B.toDims N E (List.ofFn σ) ξ t K a u) :=
    contDiff_qUkerObsT E hlen ξ t K a hz
  have h1 : (timeD1 (qMomentObsT B.toDims N E (List.ofFn σ) ξ t K a p) u M).re
      = 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * ((starRingEnd ℂ) Ψ * D).re := by
    rw [timeD1_qMomentObsT_re E (List.ofFn σ) ξ t K a p hD, Complex.ofReal_re]
  have h2 := genMomentPt_le_re (F := qUkerObsT B.toDims N E (List.ofFn σ) ξ t K a u) hC2 hp M
  have hadd : ((starRingEnd ℂ) Ψ * D).re
      + ((starRingEnd ℂ) Ψ
          * genD B.toDims N (qUkerObsT B.toDims N E (List.ofFn σ) ξ t K a u) M).re
      = ((starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)).re := by
    rw [← Complex.add_re, ← mul_add, hDeq]
  have hnorm : ‖G₁ + G₂ - G₃‖ ≤ ‖G₁‖ + ‖G₂‖ + ‖G₃‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have hre : ((starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)).re ≤ ‖Ψ‖ * (‖G₁‖ + ‖G₂‖ + ‖G₃‖) := by
    calc ((starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)).re
        ≤ |((starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)).re| := le_abs_self _
      _ ≤ ‖(starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)‖ := Complex.abs_re_le_norm _
      _ = ‖Ψ‖ * ‖G₁ + G₂ - G₃‖ := by rw [norm_mul, RCLike.norm_conj]
      _ ≤ ‖Ψ‖ * (‖G₁‖ + ‖G₂‖ + ‖G₃‖) :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
  have hpow : ‖Ψ‖ ^ (2 * p - 2) * ‖Ψ‖ = ‖Ψ‖ ^ (2 * p - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hcoef : (0 : ℝ) ≤ 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) := by positivity
  have hstep : 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * ((starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)).re
      ≤ 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 1) * (‖G₁‖ + ‖G₂‖ + ‖G₃‖) := by
    calc 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * ((starRingEnd ℂ) Ψ * (G₁ + G₂ - G₃)).re
        ≤ 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * (‖Ψ‖ * (‖G₁‖ + ‖G₂‖ + ‖G₃‖)) :=
          mul_le_mul_of_nonneg_left hre hcoef
      _ = 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 1) * (‖G₁‖ + ‖G₂‖ + ‖G₃‖) := by rw [← hpow]; ring
  rw [h1]
  nlinarith [h2, hadd, hstep]

end Band2


/-! ### Satisfiability

The identity above is asserted at a Hermitian matrix with `K` **pinned** to `RBM.Band.Kval`,
so nothing in it is data a caller may choose.  What has to be checked is the opposite failure
mode: that the hypotheses can all hold at once at the paper's own scaling. -/

section Band3

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem qdrift_side_conditions (E : ℝ) {u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (zt E u).im ≠ 0 ∧ ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := by
  refine ⟨?_, ?_⟩
  · rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  · intro s s'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hu1

private theorem qdrift_xi_lt_one (E : ℝ) (hE : |E| < 2) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (i : Fin (n + 2)) :
    ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
  rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
    norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
  exact hr1

/-- **Every side condition of `RBM.Gauss.hasDerivAt_qUkerObsT_drift` discharged from the
paper's standing assumptions**, at the flow matrix.  Nothing is chosen: `E` is the spectral
parameter of Theorem 2.6, `u` and `v` are two times of the window `[0, 1)`, `K` is
`RBM.Band.Kval`, and the three drift tensors are the pinned `RBM.DriftDef.driftF`,
`RBM.SumZeroDyn.commS` and `RBM.SumZeroDyn.varthetaDot`.  `v ↑ 1` is allowed. -/
theorem hasDerivAt_qUkerObsT_drift_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ)
    {u v : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (ω : Ω) :
    ∃ D : ℂ,
      HasDerivAt (fun r : ℝ =>
          qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a r (X.H N u ω)) D u
        ∧ D + genD B.toDims N
              (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) (X.H N u ω)
          = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ)
                  (DriftDef.driftF B E N u (X.H N u ω) σ)) a
            + Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (MomentDuhamel.lkFun B E N u (X.H N u ω) σ)) a
            - Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (fun b => Psum (B.L N) (MomentDuhamel.lkFun B E N u (X.H N u ω) σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a := by
  obtain ⟨hz, hm⟩ := qdrift_side_conditions E hE hu0 hu1
  exact hasDerivAt_qUkerObsT_drift B E N hu0 hu1 (X.hermitian N u ω) hz σ a ((v : ℝ) : ℂ)
    (fun _ _ => rfl) hm (qdrift_xi_lt_one E hE σ u hu0 hu1) (qdrift_xi_lt_one E hE σ v hv0 hv1)

/-- **Degenerate check: `ω = 0`.**  At the sample point where the flow matrix is `0` the
identity still has content — `0` is Hermitian, the resolvent is `-z⁻¹`, and every hypothesis
is discharged exactly as above (T164's rule). -/
theorem hasDerivAt_qUkerObsT_drift_at_zero (B : Band Ω) (E : ℝ) (N : ℕ)
    {u v : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) :
    ∃ D : ℂ,
      HasDerivAt (fun r : ℝ =>
          qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a r 0) D u
        ∧ D + genD B.toDims N
              (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) 0
          = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (DriftDef.driftF B E N u 0 σ)) a
            + Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (MomentDuhamel.lkFun B E N u 0 σ)) a
            - Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (fun b => Psum (B.L N) (MomentDuhamel.lkFun B E N u 0 σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a := by
  obtain ⟨hz, hm⟩ := qdrift_side_conditions E hE hu0 hu1
  exact hasDerivAt_qUkerObsT_drift B E N hu0 hu1 Matrix.isHermitian_zero hz σ a ((v : ℝ) : ℂ)
    (fun _ _ => rfl) hm (qdrift_xi_lt_one E hE σ u hu0 hu1) (qdrift_xi_lt_one E hE σ v hv0 hv1)

/-- **The pointwise integrand bound of (5.91) with every hypothesis discharged**, at the flow
matrix and the paper's scaling: `RBM.Gauss.timeD1_add_genMomentPt_le_driftFQ` with no free
data left except `p ≥ 1`. -/
theorem timeD1_add_genMomentPt_le_driftFQ_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ)
    {u v : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (ω : Ω)
    {p : ℕ} (hp : 1 ≤ p) :
    (timeD1 (qMomentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
          (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a p) u (X.H N u ω)).re
        + genMomentPt B.toDims N
            (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
              (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) p (X.H N u ω)
      ≤ 2 * (p : ℝ)
            * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖ ^ (2 * p - 1)
            * (‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (Qop (B.L N) ((u : ℝ) : ℂ)
                    (DriftDef.driftF B E N u (X.H N u ω) σ)) a‖
              + ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                    (SumZeroDyn.lkT X E N u ω σ)) a‖
              + ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                    * SumZeroDyn.varthetaDot (B.L N) u b) a‖)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ)) a‖ ^ (2 * p - 2)
            * quadVar B.toDims N
                (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                  (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) (X.H N u ω) := by
  obtain ⟨hz, hm⟩ := qdrift_side_conditions E hE hu0 hu1
  have hbr := qUkerObsT_flow B X E N σ a ((v : ℝ) : ℂ) (K := fun r b =>
    B.Kval E N r (LoopData.idx (σ, b))) (fun _ _ => rfl) u ω
  have hmain := timeD1_add_genMomentPt_le_driftFQ B E N hu0 hu1 (X.hermitian N u ω) hz σ a
    ((v : ℝ) : ℂ) (K := fun r b => B.Kval E N r (LoopData.idx (σ, b))) (fun _ _ => rfl) hp hm
    (qdrift_xi_lt_one E hE σ u hu0 hu1) (qdrift_xi_lt_one E hE σ v hv0 hv1)
  rwa [hbr] at hmain

end Band3

end Gauss


namespace MomentDuhamel

open Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ### The consumer of `Hyp.momentDuhamelQ`

T195/T201 found that `RBM.MomentDuhamel.Hyp.momentDuhamelQ` — the whole `Q_t` route — had
**no consumer** in the repository: `RBM.MomentDuhamel.stochDom_of_momentDuhamel` uses only the
plain field.  This is the missing twin.  Its conclusion is a `≺` for `Q_v ∘ (L-K)_v`, which is
what §5.5 of the paper actually bounds; returning from it to `(L-K)_v` is (5.101),
`RBM.SumZeroDyn.norm_le_norm_Qop_add`.

One hypothesis is genuinely new: `Hyp.integrable` speaks about `‖(L-K)‖` and says nothing
about the *complex* tensor, so it cannot produce the measurability of the finite linear
combination `Q_u ∘ (L-K)`.  `QIntegrable` is the exact analogue of the field, and
`qIntegrable_gauss` discharges it on the Gaussian model from the same deterministic
envelope. -/

/-- **Integrability of the `Q_t`-projected tensor**, the `Q` analogue of the field
`RBM.MomentDuhamel.Hyp.integrable`, restricted to the same window and for the same reason. -/
def QIntegrable (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ (q N : ℕ) (u : ℝ), s N ≤ u → u ≤ t N → ∀ (σ : Fin (n + 2) → Bool) a,
    Integrable (fun ω =>
      |‖Qop (B.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT X E N u ω σ) a‖| ^ q) B.P

/-- **The `Q_t` route's consumer: `RBM.MomentDuhamel.Hyp.momentDuhamelQ` produces a `≺`.**

Given the primed interface and a `‖·‖_{2p}` bound on each of the **five** terms on the right
of (5.91) + (5.103), the `Q_t`-projected loop difference is `≺ Φ`.  This is
`RBM.MomentDuhamel.stochDom_of_momentDuhamel` verbatim, with `momentDuhamel` replaced by
`momentDuhamelQ`; T201's `RBM.Gauss.momNorm_Uker_Qop_le`, `…_commS_le`,
`…_PsumVarthetaDot_le` and `…_QQ_le` are the five estimates that supply `hrhs`, and in each of
them the sum-zero premise of (7.16) is a theorem rather than an assumption — which is the
whole point of the `Q_t` route. -/
theorem stochDom_of_momentDuhamelQ [IsProbabilityMeasure (B.P)]
    {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} (H : Hyp X E s t n)
    (hQint : QIntegrable X E s t n)
    (v : ℕ → ℝ) (hv1 : ∀ N, s N ≤ v N) (hv2 : ∀ N, v N ≤ t N)
    {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {Φ : ∀ N, LoopData (B.L N) (n + 2) → ℝ} (hΦ : ∀ N q, 0 < Φ N q)
    (hrhs : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖)
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖))
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N u ω q.1)) q.2‖))
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) q.2‖))
          + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
                (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N q)) :
    StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω q.1) q.2‖)
      (fun N q _ => Φ N q) := by
  refine Gauss.stochDom_of_momentDom hcard hΦ (fun p N q => ?_) ?_
  · exact hQint (2 * p) N (v N) (hv1 N) (hv2 N) q.1 q.2
  refine momentDom_of_momNorm_le (fun N q => (hΦ N q).le) fun ε hε p hp => ?_
  obtain ⟨C, hC0, hN⟩ := hrhs ε hε p hp
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hN] with N hNq q
  exact (H.momentDuhamelQ p hp N q.1 (v N) (hv1 N) (hv2 N) q.2).trans (hNq q)

end MomentDuhamel


namespace MomentDuhamel

open Gauss

/-- **Non-vacuity of the `Q_u` projection (risk (a) of the T214 ticket).**

`Q_u` is not the zero operator on the tensors the five terms speak about: T201's explicit
witness `RBM.Gauss.witTensor` is sum-zero, so `Q_u` fixes it (`RBM.Qop_of_sumZero`), and it is
not `0`.  Hence the bounds of `RBM.MomentDuhamel.MomentIneqQ` are not statements about the
zero tensor. -/
theorem Qop_ne_zero_witness (L : ℕ) [NeZero L] (hL : 3 ≤ L) {m : ℕ} {κ : ℂ} (hκ : κ ≠ 0)
    (t : ℂ) : Qop L t (Gauss.witTensor L m κ) ≠ 0 := by
  rw [Gauss.Qop_witTensor L hL κ t]
  exact Gauss.witTensor_ne_zero L hL hκ

/-- **`QIntegrable` on the Gaussian model**, from the same deterministic envelope
`‖G_u‖ ≤ |Im z_u|⁻¹` that gives `RBM.MomentDuhamel.integrable_gauss`: `Q_u ∘ (L-K)_u` is a
finite `ℂ`-linear combination of the entries of `(L-K)_u`, hence continuous in `ω` and
bounded, and the window's `t_N < 1` is what keeps `Im z_u ≠ 0`. -/
theorem qIntegrable_gauss (d : Gauss.Dims) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    QIntegrable (Gauss.sample d) E s t n := by
  classical
  intro q N u hsu hut σ a
  have hu0 : 0 ≤ u := le_trans (hs0 N) hsu
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 N)
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  have hη : (0 : ℝ) < |(zt E u).im| := abs_pos.2 hz
  have hlk : ∀ b : LoopArg (d.L N) (n + 2),
      Continuous fun ω : Gauss.Ω d => SumZeroDyn.lkT (Gauss.sample d) E N u ω σ b :=
    fun b => (Gauss.continuous_gloop_Hflow d N u hz (LoopData.idx (σ, b))).sub continuous_const
  set Cg : ℝ := |(zt E u).im|⁻¹ ^ (n + 2) * ((d.W N : ℝ))⁻¹ ^ (n + 1) with hCgdef
  set CK : ℝ := ∑ b : LoopArg (d.L N) (n + 2),
      ‖(Gauss.band d).Kval E N u (LoopData.idx (σ, b))‖ with hCKdef
  have hbnd : ∀ (ω : Gauss.Ω d) (b : LoopArg (d.L N) (n + 2)),
      ‖SumZeroDyn.lkT (Gauss.sample d) E N u ω σ b‖ ≤ Cg + CK := by
    intro ω b
    have hwf : (LoopData.idx ((σ, b) : LoopData (d.L N) (n + 2))).WF := LoopData.idx_wf _
    have hlen : (LoopData.idx ((σ, b) : LoopData (d.L N) (n + 2))).a.length = n + 2 := by
      simp [LoopData.idx]
    have hn1 : 1 ≤ (LoopData.idx ((σ, b) : LoopData (d.L N) (n + 2))).a.length := by
      rw [hlen]; omega
    have hg := norm_gloop_le_of_le_abs_im (Gauss.Hflow_isHermitian d N u ω) hη le_rfl
      (LoopData.idx ((σ, b) : LoopData (d.L N) (n + 2))) hwf hn1
    rw [hlen] at hg
    have hK : ‖(Gauss.band d).Kval E N u (LoopData.idx ((σ, b) : LoopData (d.L N) (n + 2)))‖
        ≤ CK :=
      Finset.single_le_sum
        (f := fun b' : LoopArg (d.L N) (n + 2) =>
          ‖(Gauss.band d).Kval E N u (LoopData.idx ((σ, b') : LoopData (d.L N) (n + 2)))‖)
        (fun b' _ => norm_nonneg _) (Finset.mem_univ b)
    exact le_trans (norm_sub_le _ _) (add_le_add hg hK)
  have hcont : Continuous fun ω : Gauss.Ω d =>
      Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a := by
    have h2 : Continuous fun ω : Gauss.Ω d =>
        Psum (d.L N) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) (a 0) := by
      show Continuous fun ω : Gauss.Ω d => ∑ r : LoopArg (d.L N) (n + 1),
        SumZeroDyn.lkT (Gauss.sample d) E N u ω σ (Fin.cons (a 0) r)
      exact continuous_finsetSum _ fun r _ => hlk _
    show Continuous fun ω : Gauss.Ω d =>
      SumZeroDyn.lkT (Gauss.sample d) E N u ω σ a
        - Psum (d.L N) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) (a 0)
          * vartheta (d.L N) ((u : ℝ) : ℂ) a
    exact (hlk a).sub (h2.mul continuous_const)
  set Cb : ℝ := (Cg + CK)
      + ((Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ) * (Cg + CK))
        * ‖vartheta (d.L N) ((u : ℝ) : ℂ) a‖ with hCbdef
  have hQb : ∀ ω : Gauss.Ω d,
      ‖Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a‖ ≤ Cb := by
    intro ω
    have h1 : ‖SumZeroDyn.lkT (Gauss.sample d) E N u ω σ a‖ ≤ Cg + CK := hbnd ω a
    have h2 : ‖Psum (d.L N) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) (a 0)‖
        ≤ (Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ) * (Cg + CK) := by
      have hsum : ‖Psum (d.L N) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) (a 0)‖
          = ‖∑ r : LoopArg (d.L N) (n + 1),
              SumZeroDyn.lkT (Gauss.sample d) E N u ω σ (Fin.cons (a 0) r)‖ := rfl
      rw [hsum]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ r : LoopArg (d.L N) (n + 1),
              ‖SumZeroDyn.lkT (Gauss.sample d) E N u ω σ (Fin.cons (a 0) r)‖
          ≤ ∑ _r : LoopArg (d.L N) (n + 1), (Cg + CK) :=
            Finset.sum_le_sum fun r _ => hbnd ω _
        _ = (Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ) * (Cg + CK) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hϑ0 : (0 : ℝ) ≤ ‖vartheta (d.L N) ((u : ℝ) : ℂ) a‖ := norm_nonneg _
    refine (norm_Qop_apply_le (d.L N) _ a).trans ?_
    rw [hCbdef]
    exact add_le_add h1 (mul_le_mul_of_nonneg_right h2 hϑ0)
  have habs : (fun ω : Gauss.Ω d =>
        |‖Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a‖| ^ q)
      = fun ω : Gauss.Ω d =>
        ‖Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a‖ ^ q := by
    funext ω; rw [abs_norm]
  show Integrable (fun ω : Gauss.Ω d =>
    |‖Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a‖| ^ q)
    ((Gauss.band d).P)
  rw [habs]
  refine Gauss.integrable_of_continuous_of_bound (hcont.norm.pow q) (C := Cb ^ q) fun ω => ?_
  have h1 : ‖‖Qop (d.L N) ((u : ℝ) : ℂ)
        (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a‖ ^ q‖
      = ‖Qop (d.L N) ((u : ℝ) : ℂ)
        (SumZeroDyn.lkT (Gauss.sample d) E N u ω σ) a‖ ^ q := by
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
  rw [h1]
  exact pow_le_pow_left₀ (norm_nonneg _) (hQb ω) q

end MomentDuhamel

end RBM


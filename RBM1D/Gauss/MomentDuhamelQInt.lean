/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelQ
import RBM1D.Gauss.EEUker

/-!
# The two twin gaps of the `Q_t` route: the `E ⊗ E` bridge and the side conditions (T226)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2 and §5.5, equations (5.22), (5.24), (5.25), (5.91), (5.103), (5.104).

T214 (`RBM1D/Gauss/MomentDuhamelQ.lean`) closed the *drift* side of
`RBM.MomentDuhamel.MomentIneqQ` and handed out two twin gaps: the `Q_t` analogue of T213's
quadratic-variation bridge and the `Q_t` analogue of T212's interval-integrability side
conditions.

## What is here

* **The quadratic-variation bridge (5.103), complete.**
  `RBM.EEUker.sum_Qop_mul_conj_Qop` is (5.104) read backwards — the `α`-sum of
  `(Q_uA_α) ⊗ conj(Q_uA_α)` is `(Q_u ⊗ Q_u)` of the `α`-sum of `A_α ⊗ conj A_α`, true because
  `ϑ_u` is **real** at real times (`RBM.EEUker.conj_vartheta`).  Composed with T213's
  `RBM.EEUker.sum_Uker_mul_conj_Uker` it gives
  `RBM.EEUker.quadVar_qUkerObsT_le_norm_QQ_eeFun'`, whose only hypotheses are the window and
  `M` Hermitian (T224 discharges the chain rule), and whose right-hand side is the fifth
  right-hand term of `RBM.MomentDuhamel.Hyp.momentDuhamelQ` **verbatim**, with the doubled edge
  parameters `RBM.SumZeroDyn.xi2` as corrected by T223.
* **The window package of the four integrands of (5.91)/(5.103).**  Envelope, continuity in the
  sample point and continuity in the time for
  `Q_u(L-K)_u`, `[Q_u,Θ_{u,σ}](L-K)_u`, `(P(L-K)_u)ϑ̇_u` and `(Q_u ⊗ Q_u)(E⊗E)_u`, hence items
  1, 2, 6, 7, 8 of `RBM.MomentDuhamel.momentIneqQ_of_derivBound`'s side conditions.  These are
  exactly the `hG₂c/hG₂b`, `hG₃c/hG₃b`, `hgc/hgb` and `hQV` slots of T225's
  `RBM.Gauss.hbound_qMomentObsT_gauss`.
* **The `φ'` slot, abstracted.**  `RBM.Gauss.intervalIntegrable_phi'_of_testFunT₁` is T212's
  `RBM.Gauss.intervalIntegrable_phi'_gauss` with the particular observable abstracted away, so
  it serves the `Q_t` route as soon as a `RBM.Gauss.TestFunT₁` for
  `RBM.Gauss.qMomentObsT` is available (T225's `RBM.Gauss.testFunT₁_qMomentObsT`).

## ⚠ What is **not** here

The first drift integrand `Q_uF_u` needs a **pointwise deterministic envelope for
`RBM.DriftDef.driftF`**, which the repository does not have: T212's route through
`RBM.Gauss.uker_driftF_eq` bounds only `(U ∘ F_u)_a`, and `Q_u` reads `F_u` at `L^{n+1}` other
loop arguments through `RBM.Psum`, so the identity does not transfer.  It enters
`RBM.Gauss.exists_bdd_uker_Qop_driftF` and its three consequences as the named hypothesis
`hFb`, the same shape `RBM.Gauss.hGd_Qop_driftF` uses.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real Set

open scoped Matrix.Norms.L2Operator NNReal

/-! ## Part 1.  `Q_t` is linear, and it is real at real times -/

section QopLinear

variable (L : ℕ) [NeZero L]

/-- `RBM.Psum` commutes with a finite sum of tensors. -/
theorem Psum_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → LoopArg L (n + 1) → ℂ) (x : ZMod L) :
    Psum L (fun b => ∑ k ∈ s, A k b) x = ∑ k ∈ s, Psum L (A k) x := by
  show (∑ r : LoopArg L n, ∑ k ∈ s, A k (Fin.cons x r)) = _
  exact Finset.sum_comm

/-- **`RBM.Qop` is linear**: it commutes with a finite sum of tensors. -/
theorem Qop_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι) (t : ℂ)
    (A : ι → LoopArg L (n + 1) → ℂ) (a : LoopArg L (n + 1)) :
    Qop L t (fun b => ∑ k ∈ s, A k b) a = ∑ k ∈ s, Qop L t (A k) a := by
  show (∑ k ∈ s, A k a) - Psum L (fun b => ∑ k ∈ s, A k b) (a 0) * vartheta L t a = _
  rw [Psum_finsetSum L s A (a 0), Finset.sum_mul, ← Finset.sum_sub_distrib]
  rfl

/-- **`(Q_t ⊗ Q_t)` of (5.104) is linear**, for the same reason. -/
theorem QQ_finsetSum {k : ℕ} {ι : Type*} (s : Finset ι) (t : ℂ)
    (B : ι → LoopArg L ((k + 1) + (k + 1)) → ℂ) (c : LoopArg L ((k + 1) + (k + 1))) :
    SumZeroDyn.QQ L t (fun c' => ∑ i ∈ s, B i c') c
      = ∑ i ∈ s, SumZeroDyn.QQ L t (B i) c := by
  classical
  have hstep : ∀ (i : ι) (a b : LoopArg L (k + 1)),
      SumZeroDyn.QQ L t (B i) (Fin.append a b)
        = Qop₁ L t (Qop₂ L t (fun a' b' => B i (Fin.append a' b'))) a b := by
    intro i a b
    show Qop₁ L t (Qop₂ L t (fun a' b' => B i (Fin.append a' b')))
        (SumZeroDyn.spl1 L (Fin.append a b)) (SumZeroDyn.spl2 L (Fin.append a b)) = _
    rw [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append]
  have hsum : ∀ a b : LoopArg L (k + 1),
      SumZeroDyn.QQ L t (fun c' => ∑ i ∈ s, B i c') (Fin.append a b)
        = Qop₁ L t (Qop₂ L t (fun a' b' => ∑ i ∈ s, B i (Fin.append a' b'))) a b := by
    intro a b
    show Qop₁ L t (Qop₂ L t (fun a' b' => ∑ i ∈ s, B i (Fin.append a' b')))
        (SumZeroDyn.spl1 L (Fin.append a b)) (SumZeroDyn.spl2 L (Fin.append a b)) = _
    rw [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append]
  rw [← SumZeroDyn.append_spl L c, hsum, Finset.sum_congr rfl fun i _ => hstep i _ _]
  -- both sides are now `Qop₁ (Qop₂ ·)` of a finite sum of two-slot tensors
  have h2 : ∀ (a b : LoopArg L (k + 1)),
      Qop₂ L t (fun a' b' => ∑ i ∈ s, B i (Fin.append a' b')) a b
        = ∑ i ∈ s, Qop₂ L t (fun a' b' => B i (Fin.append a' b')) a b := by
    intro a b
    exact Qop_finsetSum L s t (fun i b' => B i (Fin.append a b')) b
  have h1 : Qop₁ L t (Qop₂ L t (fun a' b' => ∑ i ∈ s, B i (Fin.append a' b')))
        (SumZeroDyn.spl1 L c) (SumZeroDyn.spl2 L c)
      = Qop₁ L t (fun a' b' => ∑ i ∈ s, Qop₂ L t (fun a'' b'' => B i (Fin.append a'' b'')) a' b')
        (SumZeroDyn.spl1 L c) (SumZeroDyn.spl2 L c) := by
    refine congrArg (fun Z => Qop₁ L t Z (SumZeroDyn.spl1 L c) (SumZeroDyn.spl2 L c)) ?_
    funext a b
    exact h2 a b
  rw [h1]
  exact Qop_finsetSum L s t
    (fun i a' => Qop₂ L t (fun a'' b'' => B i (Fin.append a'' b'')) a' (SumZeroDyn.spl2 L c))
    (SumZeroDyn.spl1 L c)

/-- **`ϑ_{t,a}` is real at real times**: `RBM.Theta` is the inverse of `1 - t S^{(B)}` and
`S^{(B)}` is a real matrix, so conjugation acts on `RBM.vartheta` only through `t`. -/
theorem conj_vartheta (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht : |t| < 1)
    (a : LoopArg L (n + 1)) :
    (starRingEnd ℂ) (vartheta L ((t : ℝ) : ℂ) a) = vartheta L ((t : ℝ) : ℂ) a := by
  have hnorm : ‖((t : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact ht
  rw [vartheta, map_mul, map_pow, map_sub, map_one, Complex.conj_ofReal, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    rw [ChargeReduce.conj_Theta_apply L hL hnorm, Complex.conj_ofReal]

/-- **`conj (Q_t A) = Q_t (conj A)` at real times**, the only place the reality of `ϑ_t`
is used. -/
theorem conj_Qop (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht : |t| < 1)
    (A : LoopArg L (n + 1) → ℂ) (a : LoopArg L (n + 1)) :
    (starRingEnd ℂ) (Qop L ((t : ℝ) : ℂ) A a)
      = Qop L ((t : ℝ) : ℂ) (fun b => (starRingEnd ℂ) (A b)) a := by
  show (starRingEnd ℂ) (A a - Psum L A (a 0) * vartheta L ((t : ℝ) : ℂ) a)
      = (starRingEnd ℂ) (A a)
        - Psum L (fun b => (starRingEnd ℂ) (A b)) (a 0) * vartheta L ((t : ℝ) : ℂ) a
  rw [map_sub, map_mul, conj_vartheta L hL ht]
  congr 2
  exact map_sum (starRingEnd ℂ) (fun r : LoopArg L n => A (Fin.cons (a 0) r)) Finset.univ

end QopLinear

namespace EEUker

/-! ## Part 2.  The quadratic-variation bridge of the `Q_t` route

T213 proved the `U`-conjugated bilinear gluing `RBM.EEUker.sum_Uker_mul_conj_Uker` for an
**arbitrary** family `Ef : ι → LoopArg L m → ℂ`.  Feeding it the family `Q_u ∘ E^{(M)}(α)`
produces `U ⊗ U_{σ̄}` applied to `∑_α (Q_uE(α)) ⊗ conj (Q_uE(α))`, and the one thing left to
see is that the latter tensor is `(Q_u ⊗ Q_u)` of `∑_α E(α) ⊗ conj E(α)` — which is (5.104)
read backwards, and is true because `ϑ_u` is real. -/

section QQBilinear

variable (L : ℕ) [NeZero L]

/-- **(5.104) read backwards**: the `α`-sum of `(Q_tA_α) ⊗ conj (Q_tA_α)` is `(Q_t ⊗ Q_t)` of
the `α`-sum of `A_α ⊗ conj A_α`.  At real `t` the four terms of
`RBM.Qop₁_Qop₂_apply` match the four terms of the expanded product one by one. -/
theorem sum_Qop_mul_conj_Qop (hL : 3 ≤ L) {k : ℕ} {ι : Type*} [Fintype ι] {t : ℝ}
    (ht : |t| < 1) (A : ι → LoopArg L (k + 1) → ℂ)
    (c : LoopArg L ((k + 1) + (k + 1))) :
    ∑ α : ι, Qop L ((t : ℝ) : ℂ) (A α) (SumZeroDyn.spl1 L c)
        * (starRingEnd ℂ) (Qop L ((t : ℝ) : ℂ) (A α) (SumZeroDyn.spl2 L c))
      = SumZeroDyn.QQ L ((t : ℝ) : ℂ)
          (fun c' => ∑ α : ι, A α (SumZeroDyn.spl1 L c')
            * (starRingEnd ℂ) (A α (SumZeroDyn.spl2 L c'))) c := by
  classical
  set x : LoopArg L (k + 1) := SumZeroDyn.spl1 L c with hx
  set y : LoopArg L (k + 1) := SumZeroDyn.spl2 L c with hy
  set ϑx : ℂ := vartheta L ((t : ℝ) : ℂ) x with hϑx
  set ϑy : ℂ := vartheta L ((t : ℝ) : ℂ) y with hϑy
  -- the right-hand side, expanded by (5.104)
  have hQQ : SumZeroDyn.QQ L ((t : ℝ) : ℂ)
        (fun c' => ∑ α : ι, A α (SumZeroDyn.spl1 L c')
          * (starRingEnd ℂ) (A α (SumZeroDyn.spl2 L c'))) c
      = Qop₁ L ((t : ℝ) : ℂ) (Qop₂ L ((t : ℝ) : ℂ)
          (fun a b => ∑ α : ι, A α a * (starRingEnd ℂ) (A α b))) x y := by
    show Qop₁ L ((t : ℝ) : ℂ) (Qop₂ L ((t : ℝ) : ℂ)
        (fun a b => ∑ α : ι, A α (SumZeroDyn.spl1 L (Fin.append a b))
          * (starRingEnd ℂ) (A α (SumZeroDyn.spl2 L (Fin.append a b))))) x y = _
    refine congrArg (fun Z => Qop₁ L ((t : ℝ) : ℂ) (Qop₂ L ((t : ℝ) : ℂ) Z) x y) ?_
    funext a b
    rw [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append]
  rw [hQQ, Qop₁_Qop₂_apply]
  -- the three slot sums of the bilinear tensor
  have h1 : Psum₁ L (fun (a b : LoopArg L (k + 1)) =>
        ∑ α : ι, A α a * (starRingEnd ℂ) (A α b)) (x 0) y
      = ∑ α : ι, Psum L (A α) (x 0) * (starRingEnd ℂ) (A α y) := by
    show (∑ r : LoopArg L k, ∑ α : ι, A α (Fin.cons (x 0) r) * (starRingEnd ℂ) (A α y)) = _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    show _ = (∑ r : LoopArg L k, A α (Fin.cons (x 0) r)) * (starRingEnd ℂ) (A α y)
    rw [Finset.sum_mul]
  have h2 : Psum₂ L (fun (a b : LoopArg L (k + 1)) =>
        ∑ α : ι, A α a * (starRingEnd ℂ) (A α b)) x (y 0)
      = ∑ α : ι, A α x * (starRingEnd ℂ) (Psum L (A α) (y 0)) := by
    show (∑ s : LoopArg L k, ∑ α : ι, A α x * (starRingEnd ℂ) (A α (Fin.cons (y 0) s))) = _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    show _ = A α x * (starRingEnd ℂ) (∑ s : LoopArg L k, A α (Fin.cons (y 0) s))
    rw [map_sum, Finset.mul_sum]
  have h3 : Psum₁₂ L (fun (a b : LoopArg L (k + 1)) =>
        ∑ α : ι, A α a * (starRingEnd ℂ) (A α b)) (x 0) (y 0)
      = ∑ α : ι, Psum L (A α) (x 0) * (starRingEnd ℂ) (Psum L (A α) (y 0)) := by
    show (∑ r : LoopArg L k, ∑ s : LoopArg L k,
        ∑ α : ι, A α (Fin.cons (x 0) r) * (starRingEnd ℂ) (A α (Fin.cons (y 0) s))) = _
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun s (_ : s ∈ (Finset.univ : Finset (LoopArg L k))) =>
      Finset.sum_comm (s := (Finset.univ : Finset (LoopArg L k)))
        (t := (Finset.univ : Finset ι))
        (f := fun (r : LoopArg L k) (α : ι) =>
          A α (Fin.cons (x 0) r) * (starRingEnd ℂ) (A α (Fin.cons (y 0) s)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    show (∑ s : LoopArg L k, ∑ r : LoopArg L k,
        A α (Fin.cons (x 0) r) * (starRingEnd ℂ) (A α (Fin.cons (y 0) s)))
      = (∑ r : LoopArg L k, A α (Fin.cons (x 0) r))
          * (starRingEnd ℂ) (∑ s : LoopArg L k, A α (Fin.cons (y 0) s))
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  rw [h1, h2, h3]
  -- the left-hand side, expanded term by term
  have hL2 : ∀ α : ι, Qop L ((t : ℝ) : ℂ) (A α) x
        * (starRingEnd ℂ) (Qop L ((t : ℝ) : ℂ) (A α) y)
      = A α x * (starRingEnd ℂ) (A α y)
        - Psum L (A α) (x 0) * (starRingEnd ℂ) (A α y) * ϑx
        - A α x * (starRingEnd ℂ) (Psum L (A α) (y 0)) * ϑy
        + Psum L (A α) (x 0) * (starRingEnd ℂ) (Psum L (A α) (y 0)) * (ϑx * ϑy) := by
    intro α
    have hq : Qop L ((t : ℝ) : ℂ) (A α) x = A α x - Psum L (A α) (x 0) * ϑx := rfl
    have hqc : (starRingEnd ℂ) (Qop L ((t : ℝ) : ℂ) (A α) y)
        = (starRingEnd ℂ) (A α y) - (starRingEnd ℂ) (Psum L (A α) (y 0)) * ϑy := by
      rw [conj_Qop L hL ht]
      show (starRingEnd ℂ) (A α y)
          - Psum L (fun b => (starRingEnd ℂ) (A α b)) (y 0) * ϑy = _
      congr 2
      exact (map_sum (starRingEnd ℂ) (fun r : LoopArg L k => A α (Fin.cons (y 0) r))
        Finset.univ).symm
    rw [hq, hqc]; ring
  rw [Finset.sum_congr rfl fun α _ => hL2 α, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-- **The `Q_t` twin of `RBM.EEUker.sum_Uker_mul_conj_Uker`.**

`∑_α (U_{s,t,σ} ∘ Q_s A_α)_a · conj ((U_{s,t,σ} ∘ Q_s A_α)_{a'})
  = [(U_{s,t,σ} ⊗ U_{s,t,σ̄}) ∘ (Q_s ⊗ Q_s) ∘ (∑_α A_α ⊗ conj A_α)]_{a,a'}`.

The projector's time is the propagator's *starting* time, which is what (5.91) and (5.103)
have: `U_{u,v,σ}` conjugating `Q_u`. -/
theorem sum_Uker_Qop_mul_conj_Uker_Qop (hL : 3 ≤ L) {k : ℕ} {ι : Type*} [Fintype ι]
    {ξ : Fin (k + 1) → ℂ} {s t : ℝ} (hs : |s| < 1)
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (A : ι → LoopArg L (k + 1) → ℂ)
    (a a' : LoopArg L (k + 1)) :
    ∑ α : ι, Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Qop L ((s : ℝ) : ℂ) (A α)) a
        * (starRingEnd ℂ)
            (Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Qop L ((s : ℝ) : ℂ) (A α)) a')
      = Uker L (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i))) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (SumZeroDyn.QQ L ((s : ℝ) : ℂ)
            (fun c => ∑ α : ι, A α (SumZeroDyn.spl1 L c)
              * (starRingEnd ℂ) (A α (SumZeroDyn.spl2 L c))))
          (Fin.append a a') := by
  rw [sum_Uker_mul_conj_Uker L hL ht (fun α => Qop L ((s : ℝ) : ℂ) (A α)) a a']
  refine congrArg (fun Z => Uker L (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
    ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) Z (Fin.append a a')) ?_
  funext c
  exact sum_Qop_mul_conj_Qop L hL hs A c

end QQBilinear

/-! ### The bilinear identity at `E^{(M)}` and at `E^{(M)}(·, k)` -/

section QSpec

open Gauss

variable {d : Gauss.Dims} {N k : ℕ}

/-- **The `Q_t` bilinear identity at `Ef = E^{(M)}`.** -/
theorem sum_emart_Uker_Qop_mul_conj (hL : 3 ≤ d.L N) (σ : Fin (k + 1) → Bool)
    {ξ : Fin (k + 1) → ℂ} {s t : ℝ} (hs : |s| < 1)
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a a' : LoopArg (d.L N) (k + 1)) :
    ∑ i : d.Idx N, ∑ j : d.Idx N,
        Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Qop (d.L N) ((s : ℝ) : ℂ) (fun b => emart d N z (toIdx σ b) M i j)) a
          * (starRingEnd ℂ) (Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (Qop (d.L N) ((s : ℝ) : ℂ) (fun b => emart d N z (toIdx σ b) M i j)) a')
      = Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) (eeRawArg d N z M σ)) (Fin.append a a') := by
  have hkey := sum_Uker_Qop_mul_conj_Uker_Qop (d.L N) hL (ι := d.Idx N × d.Idx N) (s := s)
    hs ht (fun α b => emart d N z (toIdx σ b) M α.1 α.2) a a'
  rw [Fintype.sum_prod_type] at hkey
  refine hkey.trans ?_
  refine congrArg (fun Z => Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
    ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) Z)
      (Fin.append a a')) ?_
  funext c
  rw [eeRawArg, eeRaw, Fintype.sum_prod_type]
  rfl

/-- **The `Q_t` bilinear identity at `Ef = E^{(M)}(·, k)`** — (5.22) conjugated by
`(U ⊗ Ū) ∘ (Q ⊗ Q)`. -/
theorem sum_emartEdge_Uker_Qop_mul_conj (hL : 3 ≤ d.L N) (σ : Fin (k + 1) → Bool)
    {ξ : Fin (k + 1) → ℂ} {s t : ℝ} (hs : |s| < 1)
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (m : ℕ) (a a' : LoopArg (d.L N) (k + 1)) :
    ∑ i : d.Idx N, ∑ j : d.Idx N,
        Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Qop (d.L N) ((s : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M m i j)) a
          * (starRingEnd ℂ) (Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (Qop (d.L N) ((s : ℝ) : ℂ)
                (fun b => emartEdge d N z (toIdx σ b) M m i j)) a')
      = Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) (eeEdgeArg d N z M σ m))
          (Fin.append a a') := by
  have hkey := sum_Uker_Qop_mul_conj_Uker_Qop (d.L N) hL (ι := d.Idx N × d.Idx N) (s := s)
    hs ht (fun α b => emartEdge d N z (toIdx σ b) M m α.1 α.2) a a'
  rw [Fintype.sum_prod_type] at hkey
  refine hkey.trans ?_
  refine congrArg (fun Z => Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
    ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) Z)
      (Fin.append a a')) ?_
  funext c
  rw [eeEdgeArg, eeEdge, Fintype.sum_prod_type]
  rfl

end QSpec

/-! ### `E^{(M)}` passes through `U_{u,v} ∘ Q_u`

`EmartCoeff` is a first-order derivative in the matrix, so it commutes with the deterministic
linear operators `Q_u` and `U_{u,v}` exactly as `RBM.Gauss.genD` does in
`RBM1D/Gauss/MomentDuhamelQ.lean`.  (The two `Option`-indexed helpers below repeat the
`private` ones of that file, which cannot be imported; they should be merged when the two
files are next touched.) -/

section EmartQop

open Gauss

variable {d : Gauss.Dims} {N : ℕ}

private noncomputable def qCoefE (L : ℕ) [NeZero L] {n : ℕ} (t : ℂ) (b : LoopArg L (n + 1)) :
    Option (LoopArg L n) → ℂ
  | none => 1
  | some _ => -vartheta L t b

private def qArgE {L : ℕ} [NeZero L] {n : ℕ} {α : Type*} (Y : α → LoopArg L (n + 1) → ℂ)
    (b : LoopArg L (n + 1)) : Option (LoopArg L n) → α → ℂ
  | none => fun M' => Y M' b
  | some r => fun M' => Y M' (Fin.cons (b 0) r)

private theorem qopE_eq_sum {L : ℕ} [NeZero L] {n : ℕ} {α : Type*} (t : ℂ)
    (Y : α → LoopArg L (n + 1) → ℂ) (b : LoopArg L (n + 1)) (M' : α) :
    ∑ q : Option (LoopArg L n), qCoefE L t b q * qArgE Y b q M' = Qop L t (Y M') b := by
  classical
  rw [Fintype.sum_option]
  have h1 : ∑ r : LoopArg L n, qCoefE L t b (some r) * qArgE Y b (some r) M'
      = -(vartheta L t b * Psum L (Y M') (b 0)) := by
    simp only [qCoefE, qArgE, Psum, Finset.mul_sum, ← Finset.sum_neg_distrib, neg_mul]
  have h0 : qCoefE L t b none * qArgE Y b none M' = Y M' b := by
    simp only [qCoefE, qArgE, one_mul]
  rw [h0, h1]
  show _ = Y M' b - Psum L (Y M') (b 0) * vartheta L t b
  ring

private theorem differentiableAt_Qop_arg {n : ℕ} (t : ℂ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ → LoopArg (d.L N) (n + 1) → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hY : ∀ b, DifferentiableAt ℝ (fun M' => Y M' b) M) (b : LoopArg (d.L N) (n + 1)) :
    DifferentiableAt ℝ (fun M' => Qop (d.L N) t (Y M') b) M := by
  classical
  have hfun : (fun M' => Qop (d.L N) t (Y M') b)
      = fun M' => ∑ q : Option (LoopArg (d.L N) n), qCoefE (d.L N) t b q * qArgE Y b q M' :=
    funext fun M' => (qopE_eq_sum t Y b M').symm
  rw [hfun]
  refine DifferentiableAt.fun_sum fun q _ => ?_
  cases q with
  | none => exact (hY b).const_mul _
  | some r => exact (hY (Fin.cons (b 0) r)).const_mul _

/-- **`E^{(M)}` through `RBM.Qop`.** -/
theorem emartCoeff_Qop {n : ℕ} (t : ℂ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ → LoopArg (d.L N) (n + 1) → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hY : ∀ b, DifferentiableAt ℝ (fun M' => Y M' b) M)
    (b : LoopArg (d.L N) (n + 1)) (i j : d.Idx N) :
    EmartCoeff d N (fun M' => Qop (d.L N) t (Y M') b) M i j
      = Qop (d.L N) t (fun b' => EmartCoeff d N (fun M' => Y M' b') M i j) b := by
  classical
  have hfun : (fun M' => Qop (d.L N) t (Y M') b)
      = fun M' => ∑ q ∈ (Finset.univ : Finset (Option (LoopArg (d.L N) n))),
          qCoefE (d.L N) t b q * qArgE Y b q M' :=
    funext fun M' => (qopE_eq_sum t Y b M').symm
  have hd : ∀ q ∈ (Finset.univ : Finset (Option (LoopArg (d.L N) n))),
      DifferentiableAt ℝ (qArgE Y b q) M := by
    intro q _
    cases q with
    | none => exact hY b
    | some r => exact hY (Fin.cons (b 0) r)
  rw [hfun, EmartCoeff_sum _ _ _ _ hd i j]
  have hstep : ∀ q : Option (LoopArg (d.L N) n),
      qCoefE (d.L N) t b q * EmartCoeff d N (qArgE Y b q) M i j
        = qCoefE (d.L N) t b q
            * qArgE (fun (_ : Matrix (d.Idx N) (d.Idx N) ℂ) b' =>
                EmartCoeff d N (fun M'' => Y M'' b') M i j) b q M := by
    intro q; cases q <;> rfl
  rw [Finset.sum_congr rfl fun q _ => hstep q]
  exact qopE_eq_sum t (fun (_ : Matrix (d.Idx N) (d.Idx N) ℂ) b' =>
    EmartCoeff d N (fun M'' => Y M'' b') M i j) b M

/-- **`E^{(M)}` through `U_{s,t} ∘ Q_r`**, the composite that (5.91) puts under the moment. -/
theorem emartCoeff_Uker_Qop {n : ℕ} (ξ : Fin (n + 1) → ℂ) (s r t : ℂ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ → LoopArg (d.L N) (n + 1) → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hY : ∀ b, DifferentiableAt ℝ (fun M' => Y M' b) M)
    (a : LoopArg (d.L N) (n + 1)) (i j : d.Idx N) :
    EmartCoeff d N (fun M' => Uker (d.L N) ξ s t (Qop (d.L N) r (Y M')) a) M i j
      = Uker (d.L N) ξ s t
          (Qop (d.L N) r (fun b => EmartCoeff d N (fun M' => Y M' b) M i j)) a := by
  classical
  have hfun : (fun M' => Uker (d.L N) ξ s t (Qop (d.L N) r (Y M')) a)
      = fun M' => ∑ b : LoopArg (d.L N) (n + 1),
          (∏ e, edgeKer (d.L N) (ξ e) s t (a e) (b e)) * Qop (d.L N) r (Y M') b := rfl
  rw [hfun, EmartCoeff_sum _ _ _ _
    (fun b _ => differentiableAt_Qop_arg r Y M hY b) i j, Uker_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [emartCoeff_Qop r Y M hY b i j]

/-- A constant shift of the observable does not change `E^{(M)}`: `K_u` is deterministic. -/
theorem emartCoeff_sub_const (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (c : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    EmartCoeff d N (fun M' => F M' - c) M i j = EmartCoeff d N F M i j := by
  have hc : ∀ q : d.Idx N × d.Idx N × Bool,
      coordD1 d N (fun M' => F M' - c) M q = coordD1 d N F M q := by
    intro q
    show fderiv ℝ (fun M' => F M' - c) M (Bmat d N q.1 q.2.1 q.2.2)
        = fderiv ℝ F M (Bmat d N q.1 q.2.1 q.2.2)
    rw [fderiv_sub_const (𝕜 := ℝ) (f := F) (x := M) c]
  simp only [EmartCoeff, wirtFirst, hc]

/-- **The left-hand side of the `Q_t` route's (5.25)**: the quadratic variation of
`Ψ^Q₁ = (U_{u,v,σ} ∘ Q_u (L-K)_u)_a` is `∑_α |(U ∘ Q_u E^{(M)}(α))_a|²`. -/
theorem quadVarPairs_Uker_Qop {k : ℕ} (σ : Fin (k + 1) → Bool) (ξ : Fin (k + 1) → ℂ)
    (s r t z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (aa : LoopArg (d.L N) (k + 1))
    (K : LoopArg (d.L N) (k + 1) → ℂ)
    (hdiff : ∀ b : LoopArg (d.L N) (k + 1),
      DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M) :
    quadVarPairs d N (fun M' => Uker (d.L N) ξ s t
        (Qop (d.L N) r (fun b => loopObs d N z (toIdx σ b) M' - K b)) aa) M
      = ∑ i : d.Idx N, ∑ j : d.Idx N,
          ‖Uker (d.L N) ξ s t
            (Qop (d.L N) r (fun b => emart d N z (toIdx σ b) M i j)) aa‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [emartCoeff_Uker_Qop ξ s r t (fun M' b => loopObs d N z (toIdx σ b) M' - K b) M
    (by intro b; exact (hdiff b).sub_const (K b)) aa i j]
  refine congrArg (fun Z => Uker (d.L N) ξ s t (Qop (d.L N) r Z) aa) ?_
  funext b
  exact emartCoeff_sub_const _ _ M i j

end EmartQop

/-! ### (5.25) on the `Q_t` route -/

section QuadVarQ

open Gauss

variable {d : Gauss.Dims} {N k : ℕ}

/-- `(Q ⊗ Q) ∘ (E⊗E) = ∑_m (Q ⊗ Q) ∘ (E⊗E)^{(m)}` under `U ⊗ Ū`: both operators are
linear. -/
theorem sum_Uker_QQ_eeEdgeArg (ξ2 : Fin ((k + 1) + (k + 1)) → ℂ) (s r t : ℂ) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (σ : Fin (k + 1) → Bool)
    (c : LoopArg (d.L N) ((k + 1) + (k + 1))) :
    ∑ m ∈ Finset.range (k + 1),
        Uker (d.L N) ξ2 s t (SumZeroDyn.QQ (d.L N) r (eeEdgeArg d N z M σ m)) c
      = Uker (d.L N) ξ2 s t
          (SumZeroDyn.QQ (d.L N) r (EEBridge.eeArg d N z M σ)) c := by
  rw [Uker_sum (d.L N)]
  refine congrArg (fun Z => Uker (d.L N) ξ2 s t Z c) ?_
  funext c'
  rw [← QQ_finsetSum (d.L N) (Finset.range (k + 1)) r (fun m => eeEdgeArg d N z M σ m) c']
  refine congrArg (fun Z => SumZeroDyn.QQ (d.L N) r Z c') ?_
  funext c''
  exact (eeArg_eq_sum_eeEdgeArg z M σ c'').symm

/-- **(5.25) for the `Q_t` route.**  The quadratic variation of
`Ψ^Q₁ = (U_{u,v,σ} ∘ Q_u (L-K)_u)_a` is at most `(k+1)` times
`‖[(U_{u,v,σ} ⊗ U_{u,v,σ̄}) ∘ (Q_u ⊗ Q_u) ∘ (E ⊗ E)_u]_{a,a}‖`, which is the fifth right-hand
term of `RBM.MomentDuhamel.Hyp.momentDuhamelQ` and of (5.103) verbatim.

`hsplit` is the paper's chain rule `E^{(M)}(α) = ∑_m E^{(M)}(α, m)` of §5.2, the same
hypothesis `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` carries (T224). -/
theorem quadVarPairs_Uker_Qop_le_norm_QQ_eeArg (hL : 3 ≤ d.L N) (σ : Fin (k + 1) → Bool)
    {ξ : Fin (k + 1) → ℂ} {s t : ℝ} (hs : |s| < 1)
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (aa : LoopArg (d.L N) (k + 1))
    (K : LoopArg (d.L N) (k + 1) → ℂ)
    (hdiff : ∀ b : LoopArg (d.L N) (k + 1),
      DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M)
    (hsplit : ∀ (b : LoopArg (d.L N) (k + 1)) (i j : d.Idx N),
      emart d N z (toIdx σ b) M i j
        = ∑ m ∈ Finset.range (k + 1), emartEdge d N z (toIdx σ b) M m i j) :
    quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
        (Qop (d.L N) ((s : ℝ) : ℂ)
          (fun b => loopObs d N z (toIdx σ b) M' - K b)) aa) M
      ≤ ((k : ℝ) + 1)
          * ‖Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
              ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) (EEBridge.eeArg d N z M σ))
              (Fin.append aa aa)‖ := by
  classical
  set ξ2 : Fin ((k + 1) + (k + 1)) → ℂ :=
    Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)) with hξ2
  set rr : ℕ → ℝ := fun m => ∑ i : d.Idx N, ∑ j : d.Idx N,
    ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
      (Qop (d.L N) ((s : ℝ) : ℂ)
        (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2 with hrr
  have hr0 : ∀ m, 0 ≤ rr m := fun m =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hrC : ∀ m, ((rr m : ℝ) : ℂ)
      = Uker (d.L N) ξ2 ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) (eeEdgeArg d N z M σ m))
          (Fin.append aa aa) := by
    intro m
    rw [hrr, Complex.ofReal_sum,
      ← sum_emartEdge_Uker_Qop_mul_conj hL σ hs ht z M m aa aa]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_conj_eq _).symm
  have hsum : ((∑ m ∈ Finset.range (k + 1), rr m : ℝ) : ℂ)
      = Uker (d.L N) ξ2 ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) (EEBridge.eeArg d N z M σ))
          (Fin.append aa aa) := by
    rw [Complex.ofReal_sum,
      ← sum_Uker_QQ_eeEdgeArg ξ2 ((s : ℝ) : ℂ) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) z M σ
        (Fin.append aa aa)]
    exact Finset.sum_congr rfl fun m _ => hrC m
  have hnorm : ∑ m ∈ Finset.range (k + 1), rr m
      = ‖Uker (d.L N) ξ2 ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) (EEBridge.eeArg d N z M σ))
          (Fin.append aa aa)‖ := by
    rw [← hsum, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun m _ => hr0 m)]
  -- the Schwarz step, coordinate by coordinate
  have hsplitU : ∀ i j : d.Idx N,
      Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (Qop (d.L N) ((s : ℝ) : ℂ) (fun b => emart d N z (toIdx σ b) M i j)) aa
        = ∑ m ∈ Finset.range (k + 1), Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Qop (d.L N) ((s : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa := by
    intro i j
    rw [Uker_sum (d.L N)]
    refine congrArg (fun Z => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) Z aa) ?_
    funext b
    rw [← Qop_finsetSum (d.L N) (Finset.range (k + 1)) ((s : ℝ) : ℂ)
      (fun m b' => emartEdge d N z (toIdx σ b') M m i j) b]
    refine congrArg (fun Z => Qop (d.L N) ((s : ℝ) : ℂ) Z b) ?_
    funext b'
    exact hsplit b' i j
  have hkey : ∀ i j : d.Idx N,
      ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (Qop (d.L N) ((s : ℝ) : ℂ) (fun b => emart d N z (toIdx σ b) M i j)) aa‖ ^ 2
        ≤ ((k : ℝ) + 1) * ∑ m ∈ Finset.range (k + 1),
            ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (Qop (d.L N) ((s : ℝ) : ℂ)
                (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2 := by
    intro i j
    have h1 : ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (Qop (d.L N) ((s : ℝ) : ℂ) (fun b => emart d N z (toIdx σ b) M i j)) aa‖
        ≤ ∑ m ∈ Finset.range (k + 1), ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Qop (d.L N) ((s : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ := by
      rw [hsplitU i j]
      exact norm_sum_le _ _
    have h2 : (∑ m ∈ Finset.range (k + 1), ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (Qop (d.L N) ((s : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖) ^ 2
        ≤ ((Finset.range (k + 1)).card : ℝ) * ∑ m ∈ Finset.range (k + 1),
            ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (Qop (d.L N) ((s : ℝ) : ℂ)
                (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_range] at h2
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h2
    refine le_trans ?_ h2
    gcongr
  rw [quadVarPairs_Uker_Qop σ ξ _ _ _ z M aa K hdiff, ← hnorm]
  calc ∑ i : d.Idx N, ∑ j : d.Idx N,
        ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (Qop (d.L N) ((s : ℝ) : ℂ) (fun b => emart d N z (toIdx σ b) M i j)) aa‖ ^ 2
      ≤ ∑ i : d.Idx N, ∑ j : d.Idx N, (((k : ℝ) + 1) * ∑ m ∈ Finset.range (k + 1),
          ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Qop (d.L N) ((s : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hkey i j
    _ = ((k : ℝ) + 1) * ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ m ∈ Finset.range (k + 1),
          ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (Qop (d.L N) ((s : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ((k : ℝ) + 1) * ∑ m ∈ Finset.range (k + 1), rr m := by
        rw [hrr]
        congr 1
        calc ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ m ∈ Finset.range (k + 1),
                ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
                  (Qop (d.L N) ((s : ℝ) : ℂ)
                    (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2
            = ∑ i : d.Idx N, ∑ m ∈ Finset.range (k + 1), ∑ j : d.Idx N,
                ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
                  (Qop (d.L N) ((s : ℝ) : ℂ)
                    (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2 :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ m ∈ Finset.range (k + 1), ∑ i : d.Idx N, ∑ j : d.Idx N,
                ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
                  (Qop (d.L N) ((s : ℝ) : ℂ)
                    (fun b => emartEdge d N z (toIdx σ b) M m i j)) aa‖ ^ 2 := Finset.sum_comm

end QuadVarQ

/-! ### The `E ⊗ E` term of `RBM.MomentDuhamel.MomentIneqQ`, supplied by a theorem -/

section QBandForm

open Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The `E ⊗ E` term of `RBM.MomentDuhamel.Hyp.momentDuhamelQ` and of (5.103).**

At a time `u` of the window and a running time `v ∈ [0, 1)`, the quadratic variation of
`Ψ^Q₁ = (U_{u,v,σ} ∘ Q_u (L - K)_u)_a` — the quantity
`RBM.Gauss.timeD1_add_genMomentPt_le_driftFQ` leaves on the right of (5.91) — is at most
`(n+2)` times

`‖[(U_{u,v,σ} ⊗ U_{u,v,σ̄}) ∘ (Q_u ⊗ Q_u) ∘ (E ⊗ E)_{u,σ}]_{a,a}‖`,

which is the fifth right-hand term of `momentDuhamelQ` verbatim, with the doubled edge
parameters `RBM.SumZeroDyn.xi2` of Lemma 5.5 (since T223 these *are* the paper's `(ξ, ξ̄)`).

`hsplit` is the chain rule `E^{(M)}(α) = ∑_m E^{(M)}(α, m)` of §5.2, the same hypothesis
`RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` carries (T224); nothing else is assumed. -/
theorem quadVarPairs_Uker_Qop_le_norm_QQ_eeFun {E : ℝ} (hE : |E| ≤ 2) {N n : ℕ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (hz : (zt E u).im ≠ 0)
    (σ : Fin (n + 2) → Bool) {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (a : LoopArg (B.L N) (n + 2)) (K : LoopArg (B.toDims.L N) (n + 2) → ℂ)
    (hsplit : ∀ (b : LoopArg (B.L N) (n + 2)) (i j : B.Idx N),
      emart B.toDims N (zt E u) (toIdx σ b) M i j
        = ∑ m ∈ Finset.range (n + 2), emartEdge B.toDims N (zt E u) (toIdx σ b) M m i j) :
    quadVarPairs B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (B.L N) ((u : ℝ) : ℂ)
            (fun b => loopObs B.toDims N (zt E u) (toIdx σ b) M' - K b)) a) M
      ≤ ((n : ℝ) + 2)
          * ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
                (MomentDuhamel.eeFun B E N u M σ)) (Fin.append a a)‖ := by
  have hs : |u| < 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have ht : ∀ i : Fin (n + 2), ‖((v : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := fun i =>
    norm_mul_mSigma_lt_one hE hv0 hv1 (σ i) (σ (i + 1))
  have hdiff : ∀ b : LoopArg (B.L N) (n + 2),
      DifferentiableAt ℝ (loopObs B.toDims N (zt E u) (toIdx σ b)) M := by
    intro b
    have hbd : BddC2 (loopObs B.toDims N (zt E u) (toIdx σ b)) :=
      bddC2_loopObs hz (abs_pos.mpr hz) le_rfl (toIdx_wf σ b)
    exact hbd.contDiff.differentiable (by norm_num) M
  have hkey := quadVarPairs_Uker_Qop_le_norm_QQ_eeArg (d := B.toDims) (N := N) (k := n + 1)
    (B.three_le_L N) σ (ξ := xiOf (mSigma E) σ) (s := u) (t := v) hs ht (zt E u) M a K
    hdiff hsplit
  have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hkey
  rw [xi2_eq_append_conj E σ]
  exact hkey

/-- **The same, in the `RBM.Gauss.qUkerObsT` / `RBM.Gauss.quadVar` shape the generator identity
uses.**  `RBM.Gauss.secondOrder_eq_quadVar` is T72's identification of the generator's
second-order coefficient with the quadratic-variation sum of (5.25), and
`RBM.Gauss.qUkerObsT` is `Ψ^Q₁` by definition. -/
theorem quadVar_qUkerObsT_le_norm_QQ_eeFun {E : ℝ} (hE : |E| ≤ 2) {N n : ℕ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (hz : (zt E u).im ≠ 0)
    (σ : Fin (n + 2) → Bool) {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (a : LoopArg (B.L N) (n + 2)) (K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ)
    (hsplit : ∀ (b : LoopArg (B.L N) (n + 2)) (i j : B.Idx N),
      emart B.toDims N (zt E u) (toIdx σ b) M i j
        = ∑ m ∈ Finset.range (n + 2), emartEdge B.toDims N (zt E u) (toIdx σ b) M m i j) :
    quadVar B.toDims N
        (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) K a u) M
      ≤ ((n : ℝ) + 2)
          * ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
                (MomentDuhamel.eeFun B E N u M σ)) (Fin.append a a)‖ :=
  (secondOrder_eq_quadVar
      (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) K a u) M).trans_le
    (quadVarPairs_Uker_Qop_le_norm_QQ_eeFun hE hu0 hu1 hv0 hv1 hz σ a (K u) hsplit)

/-- **(5.103)'s `E ⊗ E` term with `hsplit` discharged.**  Since T224 the chain rule
`E^{(M)}(α) = ∑_m E^{(M)}(α, m)` is a theorem (`RBM.Gauss.emart_eq_sum_emartEdge'`); it needs
`M` Hermitian, which in §5.2 is `M = H_u`. -/
theorem quadVarPairs_Uker_Qop_le_norm_QQ_eeFun' {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (σ : Fin (n + 2) → Bool) {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (a : LoopArg (B.L N) (n + 2)) (K : LoopArg (B.toDims.L N) (n + 2) → ℂ) :
    quadVarPairs B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (B.L N) ((u : ℝ) : ℂ)
            (fun b => loopObs B.toDims N (zt E u) (toIdx σ b) M' - K b)) a) M
      ≤ ((n : ℝ) + 2)
          * ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
                (MomentDuhamel.eeFun B E N u M σ)) (Fin.append a a)‖ := by
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  refine quadVarPairs_Uker_Qop_le_norm_QQ_eeFun hE.le hu0 hu1 hv0 hv1 hz σ a K (fun b i j => ?_)
  exact emart_eq_sum_emartEdge' (d := B.toDims) (N := N) (m := n + 2) hz hM (toIdx_wf σ b)
    (show (toIdx σ b).a.length = n + 2 from toIdx_length σ b) i j

/-- **The `E ⊗ E` slot of the `Q_t` route, hypothesis-free on the flow.**  This is the shape
`RBM.Gauss.hbound_qMomentObsT_gauss` consumes (`hQV`, with `cq = n + 2`): at `M = H_u` the
chain rule and the differentiability are theorems, so the only hypotheses left are the
window. -/
theorem quadVar_qUkerObsT_le_norm_QQ_eeFun' {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (σ : Fin (n + 2) → Bool) {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (a : LoopArg (B.L N) (n + 2)) (K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ) :
    quadVar B.toDims N
        (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) K a u) M
      ≤ ((n : ℝ) + 2)
          * ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
                (MomentDuhamel.eeFun B E N u M σ)) (Fin.append a a)‖ :=
  (secondOrder_eq_quadVar
      (qUkerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) K a u) M).trans_le
    (quadVarPairs_Uker_Qop_le_norm_QQ_eeFun' hE hu0 hu1 hv0 hv1 σ hM a (K u))

end QBandForm

/-! ### The numerical self-consistency check for `RBM.EEUker.sum_Qop_mul_conj_Qop`

An identity between `Q_u`-conjugated bilinear forms compiles just as happily when the four
terms of (5.104) are mis-assigned or when a conjugation is dropped, so both sides are
evaluated independently at `L = 3`, loops of length **two** (`k = 1`; at `k = 0` the statement
is degenerate — `ϑ ≡ 1` and `Q_t ≡ 0`), `t = 0` (where `Θ_0 = 1`, so `ϑ_{0,a} = δ_{a_1 a_2}`),
`x = (0,0)` and `y = (1,1)`, both of which have `ϑ = 1`, so that **all four** terms of
`RBM.Qop₁_Qop₂_apply` are present.  The family is complex-valued, so the common value has a
nonzero imaginary part.

Neither evaluation uses any theorem of `RBM.EEUker`.  The two discriminating checks are
`RBM.EEUker.sanityQ_cross_term_matters` (dropping the `P ⊗ P` cross term changes the number)
and `RBM.EEUker.sanityQ_conj_matters` (with a **non-real** `ϑ` the product of the two `Q`'s is
*not* the four-term form — which is exactly why
`RBM.EEUker.sum_Qop_mul_conj_Qop` is stated at real times and uses
`RBM.EEUker.conj_vartheta`). -/

section SanityQ

/-- The two-element family of the check, indexed by `Bool`; every value is an explicit
complex constant, and the two members are not proportional. -/
noncomputable def sanityQA (α : Bool) (b : LoopArg 3 (1 + 1)) : ℂ :=
  if α then (if b 0 = 0 then 1 + Complex.I else 3)
  else (if b 1 = 0 then 1 else (if b 1 = 1 then Complex.I else 2))

/-- `x = (0, 0)`, so `ϑ_{0,x} = 1`. -/
def sanityQx : LoopArg 3 (1 + 1) := fun _ => 0

/-- `y = (1, 1)`, so `ϑ_{0,y} = 1` too: all four terms of (5.104) are present. -/
def sanityQy : LoopArg 3 (1 + 1) := fun _ => 1

theorem cons_apply_zero {L : ℕ} (x : ZMod L) (r : LoopArg L 1) :
    (Fin.cons x r : LoopArg L (1 + 1)) (0 : Fin (1 + 1)) = x := rfl

theorem cons_apply_one {L : ℕ} (x : ZMod L) (r : LoopArg L 1) :
    (Fin.cons x r : LoopArg L (1 + 1)) (1 : Fin (1 + 1)) = r 0 := rfl

/-- `ϑ_{0,a} = δ_{a_1 a_2}` : `Θ_0 = 1` (`RBM.Theta_zero`) and `(1 - 0)^1 = 1`. -/
theorem vartheta_three_zero (a : LoopArg 3 (1 + 1)) :
    vartheta 3 ((0 : ℝ) : ℂ) a = if a 0 = a 1 then 1 else 0 := by
  rw [vartheta, Complex.ofReal_zero, Theta_zero, Fin.prod_univ_one, sub_zero, one_pow, one_mul]
  exact Matrix.one_apply

/-- `(P ∘ A)_x = ∑_y A_{(x,y)}`, written out at `L = 3`. -/
theorem Psum_three_two (A : LoopArg 3 (1 + 1) → ℂ) (x : ZMod 3) :
    Psum 3 A x = A (Fin.cons x (fun _ => 0)) + A (Fin.cons x (fun _ => 1))
      + A (Fin.cons x (fun _ => 2)) :=
  sum_loopArg_three_one (fun r => A (Fin.cons x r))

/-- The left-hand side of `RBM.EEUker.sum_Qop_mul_conj_Qop` at the sanity point, computed from
scratch: `(-2-i)·conj(-3) + (-2-2i)·conj(-6) = 18 + 15i`. -/
theorem sanityQ_lhs :
    ∑ α : Bool, Qop 3 ((0 : ℝ) : ℂ) (sanityQA α) sanityQx
        * (starRingEnd ℂ) (Qop 3 ((0 : ℝ) : ℂ) (sanityQA α) sanityQy)
      = 18 + 15 * Complex.I := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [Fintype.sum_bool]
  simp only [Qop, Psum_three_two, vartheta_three_zero, sanityQA, sanityQx, sanityQy,
    cons_apply_zero, cons_apply_one]
  norm_num [Complex.ext_iff, h01, h02, h10, h12, h20, h21]

/-- The right-hand side of `RBM.EEUker.sum_Qop_mul_conj_Qop` at the sanity point, computed
from scratch through the four terms of (5.104):
`(3+2i) - (10+6i) - (12+8i) + (37+27i) = 18 + 15i`. -/
theorem sanityQ_rhs :
    SumZeroDyn.QQ 3 ((0 : ℝ) : ℂ)
        (fun c => ∑ α : Bool, sanityQA α (SumZeroDyn.spl1 3 c)
          * (starRingEnd ℂ) (sanityQA α (SumZeroDyn.spl2 3 c)))
        (Fin.append sanityQx sanityQy)
      = 18 + 15 * Complex.I := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [show SumZeroDyn.QQ 3 ((0 : ℝ) : ℂ)
        (fun c => ∑ α : Bool, sanityQA α (SumZeroDyn.spl1 3 c)
          * (starRingEnd ℂ) (sanityQA α (SumZeroDyn.spl2 3 c)))
        (Fin.append sanityQx sanityQy)
      = _ from Qop₁_Qop₂_apply 3
        (fun a b => ∑ α : Bool, sanityQA α (SumZeroDyn.spl1 3 (Fin.append a b))
          * (starRingEnd ℂ) (sanityQA α (SumZeroDyn.spl2 3 (Fin.append a b))))
        (SumZeroDyn.spl1 3 (Fin.append sanityQx sanityQy))
        (SumZeroDyn.spl2 3 (Fin.append sanityQx sanityQy))]
  simp only [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append, Psum₁, Psum₂, Psum₁₂,
    Psum_three_two, vartheta_three_zero, Fintype.sum_bool, sanityQA, sanityQx, sanityQy,
    cons_apply_zero, cons_apply_one]
  norm_num [Complex.ext_iff, h01, h02, h10, h12, h20, h21]

/-- **The check**: the two independently computed values agree. -/
theorem sanityQ_lhs_eq_rhs :
    (∑ α : Bool, Qop 3 ((0 : ℝ) : ℂ) (sanityQA α) sanityQx
        * (starRingEnd ℂ) (Qop 3 ((0 : ℝ) : ℂ) (sanityQA α) sanityQy))
      = SumZeroDyn.QQ 3 ((0 : ℝ) : ℂ)
          (fun c => ∑ α : Bool, sanityQA α (SumZeroDyn.spl1 3 c)
            * (starRingEnd ℂ) (sanityQA α (SumZeroDyn.spl2 3 c)))
          (Fin.append sanityQx sanityQy) := by
  rw [sanityQ_lhs, sanityQ_rhs]

/-- The common value is nonzero and has a nonzero imaginary part. -/
theorem sanityQ_value_ne_zero : (18 + 15 * Complex.I : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- **Discriminating check 1: the `P ⊗ P` cross term of (5.104) is not decoration.**  Dropping
it from the right-hand side gives `-19 - 12i` instead of `18 + 15i` at the same point. -/
theorem sanityQ_cross_term_matters :
    (SumZeroDyn.QQ 3 ((0 : ℝ) : ℂ)
        (fun c => ∑ α : Bool, sanityQA α (SumZeroDyn.spl1 3 c)
          * (starRingEnd ℂ) (sanityQA α (SumZeroDyn.spl2 3 c)))
        (Fin.append sanityQx sanityQy))
      ≠ (∑ α : Bool, sanityQA α sanityQx * (starRingEnd ℂ) (sanityQA α sanityQy))
        - Psum₁ 3 (fun a b => ∑ α : Bool, sanityQA α a * (starRingEnd ℂ) (sanityQA α b))
            (sanityQx 0) sanityQy * vartheta 3 ((0 : ℝ) : ℂ) sanityQx
        - Psum₂ 3 (fun a b => ∑ α : Bool, sanityQA α a * (starRingEnd ℂ) (sanityQA α b))
            sanityQx (sanityQy 0) * vartheta 3 ((0 : ℝ) : ℂ) sanityQy := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [sanityQ_rhs]
  simp only [Psum₁, Psum₂, Psum_three_two, vartheta_three_zero, Fintype.sum_bool,
    sanityQA, sanityQx, sanityQy, cons_apply_zero, cons_apply_one]
  norm_num [Complex.ext_iff, h01, h02, h10, h12, h20, h21]

/-- **Discriminating check 2: the reality of `ϑ_u` is load-bearing.**  With `A = A' = 1`,
`(P∘A) = (P∘A') = 1` and a *non-real* pair `ϑ_x = 2i`, `ϑ_y = 3i`, the actual product
`(A - (P∘A)ϑ_x) · conj(A' - (P∘A')ϑ_y)` is `7 + i` while the four-term form of (5.104) — which
carries `ϑ_x ϑ_y` **unconjugated** — gives `-5 - 5i`.  The two agree for every family exactly
because `RBM.EEUker.conj_vartheta` makes `conj ϑ_y = ϑ_y` at real times, which is where
`|t| < 1` and `3 ≤ L` enter `RBM.EEUker.sum_Qop_mul_conj_Qop`. -/
theorem sanityQ_conj_matters :
    ((1 : ℂ) - 1 * (2 * Complex.I)) * (starRingEnd ℂ) ((1 : ℂ) - 1 * (3 * Complex.I))
      ≠ (1 : ℂ) * (starRingEnd ℂ) 1 - 1 * (starRingEnd ℂ) 1 * (2 * Complex.I)
        - 1 * (starRingEnd ℂ) 1 * (3 * Complex.I)
        + 1 * (starRingEnd ℂ) 1 * ((2 * Complex.I) * (3 * Complex.I)) := by
  norm_num [Complex.ext_iff]

end SanityQ

end EEUker

/-! ## Part 3.  The window package of the `Q_t` route (T226 item 1)

The three drift integrands of (5.91) and the `E ⊗ E` term of (5.103) have to be bounded and
continuous in the sample point (for measurability and for the Hölder step) and continuous in
the time (for interval integrability).  All four are `U_{u,v,σ}` applied to a *deterministic*
operator — `Q_u`, `[Q_u, Θ_{u,σ}]`, `(P·)ϑ̇_u`, `Q_u ⊗ Q_u` — acting on one of the three
tensors whose envelope and path-continuity T212 already established
(`RBM.MomentDuhamel.lkFun`, `RBM.DriftDef.driftF`, `RBM.MomentDuhamel.eeFun`).

So no new size estimate on the tensors is needed: each of the four operators is a *finite*
linear combination with coefficients built from `RBM.Theta` and `RBM.vartheta`, and on a
window `[u₀, u₁] ⊆ [0, 1)` those coefficients are bounded (`|ϑ_u| ≤ 1`) and continuous. -/

namespace Gauss

open MomentDuhamel

/-! ### Generic max-norm bounds for `P`, `ϑ_u`, `Q_u` and `Q_u ⊗ Q_u` -/

section GenericBounds

variable (L : ℕ) [NeZero L]

/-- **`|ϑ_{u,a}| ≤ 1` at real times of `[0, 1)`.**  The `(1-u)^n` prefactor of Definition 5.12
exactly cancels the `n` propagator entries, each `|Θ_u| ≤ (1-u)^{-1}`. -/
theorem norm_vartheta_ofReal_le_one (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : LoopArg L (n + 1)) : ‖vartheta L ((u : ℝ) : ℂ) a‖ ≤ 1 := by
  have h := norm_vartheta_le L hL (SumZeroDyn.norm_ofReal_lt_one hu0 hu1) a
  rw [norm_one_sub_ofReal hu1.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu0] at h
  refine h.trans (le_of_eq ?_)
  rw [← mul_pow, mul_inv_cancel₀ (by linarith : (1 : ℝ) - u ≠ 0), one_pow]

/-- **`P` costs at most the cardinality of the summed block.** -/
theorem norm_Psum_le_of_bdd {n : ℕ} (A : LoopArg L (n + 1) → ℂ) {C : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ C) (x : ZMod L) :
    ‖Psum L A x‖ ≤ (Fintype.card (LoopArg L n) : ℝ) * C := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r : LoopArg L n, ‖A (Fin.cons x r)‖ ≤ ∑ _r : LoopArg L n, C :=
        Finset.sum_le_sum fun r _ => hA _
    _ = (Fintype.card (LoopArg L n) : ℝ) * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`Q_u` is bounded in the max norm on the window** — Lemma 5.13 (5.87) with the explicit
real-time constant. -/
theorem norm_Qop_ofReal_le_of_bdd (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (A : LoopArg L (n + 1) → ℂ) {C : ℝ} (hA : ∀ b, ‖A b‖ ≤ C)
    (a : LoopArg L (n + 1)) :
    ‖Qop L ((u : ℝ) : ℂ) A a‖ ≤ (1 + (Fintype.card (LoopArg L n) : ℝ)) * C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hA a)
  refine (norm_Qop_apply_le L A a).trans ?_
  have hmul : ‖Psum L A (a 0)‖ * ‖vartheta L ((u : ℝ) : ℂ) a‖
      ≤ ((Fintype.card (LoopArg L n) : ℝ) * C) * 1 :=
    mul_le_mul (norm_Psum_le_of_bdd L A hA (a 0))
      (norm_vartheta_ofReal_le_one L hL hu0 hu1 a) (norm_nonneg _) (by positivity)
  calc ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L ((u : ℝ) : ℂ) a‖
      ≤ C + ((Fintype.card (LoopArg L n) : ℝ) * C) * 1 := add_le_add (hA a) hmul
    _ = (1 + (Fintype.card (LoopArg L n) : ℝ)) * C := by ring

/-- **`Q_u ⊗ Q_u` of (5.104) is bounded in the max norm on the window**, with the square of
the `Q_u` constant: the four terms of `RBM.Qop₁_Qop₂_apply` are `1`, `card`, `card` and
`card²` copies of the tensor's own bound. -/
theorem norm_QQ_ofReal_le_of_bdd (hL : 3 ≤ L) {k : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (Bt : LoopArg L ((k + 1) + (k + 1)) → ℂ) {C : ℝ} (hB : ∀ c, ‖Bt c‖ ≤ C)
    (c : LoopArg L ((k + 1) + (k + 1))) :
    ‖SumZeroDyn.QQ L ((u : ℝ) : ℂ) Bt c‖
      ≤ (1 + (Fintype.card (LoopArg L k) : ℝ)) ^ 2 * C := by
  classical
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hB c)
  set card : ℝ := (Fintype.card (LoopArg L k) : ℝ) with hcard
  have hcard0 : 0 ≤ card := Nat.cast_nonneg _
  set A : LoopArg L (k + 1) → LoopArg L (k + 1) → ℂ :=
    fun a b => Bt (Fin.append a b) with hA
  set x : LoopArg L (k + 1) := SumZeroDyn.spl1 L c with hx
  set y : LoopArg L (k + 1) := SumZeroDyn.spl2 L c with hy
  have hAb : ∀ a b, ‖A a b‖ ≤ C := fun a b => hB _
  have hϑx : ‖vartheta L ((u : ℝ) : ℂ) x‖ ≤ 1 := norm_vartheta_ofReal_le_one L hL hu0 hu1 x
  have hϑy : ‖vartheta L ((u : ℝ) : ℂ) y‖ ≤ 1 := norm_vartheta_ofReal_le_one L hL hu0 hu1 y
  have h1 : ‖Psum₁ L A (x 0) y‖ ≤ card * C :=
    norm_Psum_le_of_bdd L (fun a => A a y) (fun a => hAb a y) (x 0)
  have h2 : ‖Psum₂ L A x (y 0)‖ ≤ card * C :=
    norm_Psum_le_of_bdd L (fun b => A x b) (fun b => hAb x b) (y 0)
  have h12 : ‖Psum₁₂ L A (x 0) (y 0)‖ ≤ card * (card * C) :=
    norm_Psum_le_of_bdd L (fun a => Psum L (fun b => A a b) (y 0))
      (fun a => norm_Psum_le_of_bdd L (fun b => A a b) (fun b => hAb a b) (y 0)) (x 0)
  have hexp : SumZeroDyn.QQ L ((u : ℝ) : ℂ) Bt c
      = A x y - Psum₁ L A (x 0) y * vartheta L ((u : ℝ) : ℂ) x
        - Psum₂ L A x (y 0) * vartheta L ((u : ℝ) : ℂ) y
        + Psum₁₂ L A (x 0) (y 0)
            * (vartheta L ((u : ℝ) : ℂ) x * vartheta L ((u : ℝ) : ℂ) y) :=
    Qop₁_Qop₂_apply L A x y
  rw [hexp]
  have hstep : ‖A x y - Psum₁ L A (x 0) y * vartheta L ((u : ℝ) : ℂ) x
        - Psum₂ L A x (y 0) * vartheta L ((u : ℝ) : ℂ) y
        + Psum₁₂ L A (x 0) (y 0)
            * (vartheta L ((u : ℝ) : ℂ) x * vartheta L ((u : ℝ) : ℂ) y)‖
      ≤ C + card * C * 1 + card * C * 1 + card * (card * C) * (1 * 1) := by
    refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_sub_le _ _)
      (add_le_add (le_trans (norm_sub_le _ _) (add_le_add (hAb x y) ?_)) ?_)) ?_)
    · rw [norm_mul]; exact mul_le_mul h1 hϑx (norm_nonneg _) (by positivity)
    · rw [norm_mul]; exact mul_le_mul h2 hϑy (norm_nonneg _) (by positivity)
    · rw [norm_mul, norm_mul]
      exact mul_le_mul h12 (mul_le_mul hϑx hϑy (norm_nonneg _) zero_le_one)
        (by positivity) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  ring

end GenericBounds

/-! ### Path continuity of the coefficients: `Θ`, `ϑ_u`, `ϑ̇_u`, `𝒢_{u,σ}`

Each is continuous along any continuous path `τ` that stays in `[0, 1)`.  Instantiated at
`τ = id` these give the *time* continuity that the interval integrabilities need; instantiated
at a constant `τ` they are trivially true and the tensor's own continuity in the sample point
carries everything, which is why the same lemma serves both. -/

section PathCoef

variable (L : ℕ) [NeZero L] {X : Type*} [TopologicalSpace X]

/-- `x ↦ (Θ_{τ(x)})_{x'y}` is continuous, `RBM.SumZeroDyn.hasDerivAt_Theta_real`. -/
theorem continuousOn_Theta_ofReal_path (hL : 3 ≤ L) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (x' y : ZMod L) :
    ContinuousOn (fun x => Theta L ((τ x : ℝ) : ℂ) x' y) S := fun x hx =>
  ((SumZeroDyn.hasDerivAt_Theta_real L hL (h0 x hx) (h1 x hx) x'
    y).continuousAt).comp_continuousWithinAt (hτ x hx)

/-- `x ↦ (Θ_{τ(x)ξ})_{x'y}` is continuous for `‖ξ‖ ≤ 1`, `RBM.hasDerivAt_Theta_apply`. -/
theorem continuousOn_Theta_mul_path (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {S : Set X}
    {τ : X → ℝ} (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (x' y : ZMod L) :
    ContinuousOn (fun x => Theta L (((τ x : ℝ) : ℂ) * ξ) x' y) S := by
  intro x hx
  have hlt : ‖((τ x : ℝ) : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt_one (h0 x hx) (h1 x hx) hξ
  have hf : ContinuousWithinAt (fun x' : X => ((τ x' : ℝ) : ℂ) * ξ) S x :=
    (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hτ x hx)).mul
      continuousWithinAt_const
  have hg : ContinuousAt (fun ζ : ℂ => Theta L ζ x' y) (((τ x : ℝ) : ℂ) * ξ) :=
    (hasDerivAt_Theta_apply L hL hlt x' y).continuousAt
  exact hg.comp_continuousWithinAt_of_eq hf rfl

/-- `x ↦ (Θ_{τ(x)} S^{(B)} Θ_{τ(x)})_{x'y}` is continuous. -/
theorem continuousOn_ThetaSBTheta_path (hL : 3 ≤ L) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (x' y : ZMod L) :
    ContinuousOn (fun x =>
      (Theta L ((τ x : ℝ) : ℂ) * SB L * Theta L ((τ x : ℝ) : ℂ)) x' y) S := by
  have hT := continuousOn_Theta_ofReal_path L hL hτ h0 h1
  simp only [Matrix.mul_apply]
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact (continuousOn_finsetSum _ fun j _ => (hT x' j).mul continuousOn_const).mul (hT k y)

/-- `x ↦ ϑ_{τ(x),a}` is continuous, `RBM.SumZeroDyn.hasDerivAt_vartheta`. -/
theorem continuousOn_vartheta_path (hL : 3 ≤ L) {n : ℕ} {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (a : LoopArg L (n + 1)) :
    ContinuousOn (fun x => vartheta L ((τ x : ℝ) : ℂ) a) S := fun x hx =>
  ((SumZeroDyn.hasDerivAt_vartheta L hL (h0 x hx) (h1 x hx)
    a).continuousAt).comp_continuousWithinAt (hτ x hx)

/-- `x ↦ ϑ̇_{τ(x),a}` is continuous: it is the explicit expression of Definition 5.12's
derivative, a finite algebraic combination of `RBM.Theta` entries. -/
theorem continuousOn_varthetaDot_path (hL : 3 ≤ L) {n : ℕ} {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (a : LoopArg L (n + 1)) :
    ContinuousOn (fun x => SumZeroDyn.varthetaDot L (τ x) a) S := by
  have hT := continuousOn_Theta_ofReal_path L hL hτ h0 h1
  have hTS := continuousOn_ThetaSBTheta_path L hL hτ h0 h1
  have hone : ContinuousOn (fun x => (1 : ℂ) - ((τ x : ℝ) : ℂ)) S :=
    continuousOn_const.sub (Complex.continuous_ofReal.comp_continuousOn hτ)
  simp only [SumZeroDyn.varthetaDot]
  refine ContinuousOn.add ?_ ?_
  · exact (continuousOn_const.mul (hone.pow _)).mul
      (continuousOn_finsetProd _ fun i _ => hT _ _)
  · refine (hone.pow _).mul (continuousOn_finsetSum _ fun i _ => ?_)
    exact (continuousOn_finsetProd _ fun j _ => hT _ _).mul (hTS _ _)

/-- `x ↦ 𝒢_{τ(x),σ}` entrywise: the generator's kernel `ξ_i Θ^{(B)}_{τ(x)ξ_i} S^{(B)}` is
continuous. -/
theorem continuousOn_genSM_path (hL : 3 ≤ L) {m : ℕ} {ξ : Fin m → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (i : Fin m) (x' c : ZMod L) :
    ContinuousOn (fun x => SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ) i x' c) S := by
  simp only [SumZeroDyn.genSM, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => ?_)
  exact (continuousOn_Theta_mul_path L hL (hξ i) hτ h0 h1 x' j).mul continuousOn_const

end PathCoef

/-! ### Path continuity of the four operators applied to a moving tensor -/

section PathOp

variable (L : ℕ) [NeZero L] {X : Type*} [TopologicalSpace X]

/-- **`U_{τ(x),t,σ}` applied to a moving tensor is continuous.**  This is the common core of
T212's `RBM.Gauss.continuousOn_uker_lkFun_path`, `continuousOn_uker_driftF_path` and
`continuousOn_uker_eeFun_path`: the propagator's coefficients are affine in the starting time
(`RBM.Gauss.continuous_edgeKer_time`) and do not see the tensor at all. -/
theorem continuousOn_Uker_of_tensor {m : ℕ} (ξ : Fin m → ℂ) (t : ℂ) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (A : X → LoopArg L m → ℂ)
    (hA : ∀ b, ContinuousOn (fun x => A x b) S) (a : LoopArg L m) :
    ContinuousOn (fun x => Uker L ξ ((τ x : ℝ) : ℂ) t (A x) a) S := by
  simp only [Uker]
  refine continuousOn_finsetSum _ fun b _ => ?_
  refine ContinuousOn.mul ?_ (hA b)
  exact (continuous_finsetProd _ fun i _ =>
    continuous_edgeKer_time (ξ i) t (a i) (b i)).comp_continuousOn hτ

/-- **`P` applied to a moving tensor is continuous** — it is a finite sum. -/
theorem continuousOn_Psum_of_tensor {n : ℕ} {S : Set X} (A : X → LoopArg L (n + 1) → ℂ)
    (hA : ∀ b, ContinuousOn (fun x => A x b) S) (y : ZMod L) :
    ContinuousOn (fun x => Psum L (A x) y) S :=
  continuousOn_finsetSum _ fun _ _ => hA _

/-- **`Q_{τ(x)}` applied to a moving tensor is continuous.** -/
theorem continuousOn_Qop_of_tensor (hL : 3 ≤ L) {n : ℕ} {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (A : X → LoopArg L (n + 1) → ℂ) (hA : ∀ b, ContinuousOn (fun x => A x b) S)
    (b : LoopArg L (n + 1)) :
    ContinuousOn (fun x => Qop L ((τ x : ℝ) : ℂ) (A x) b) S := by
  show ContinuousOn (fun x => A x b - Psum L (A x) (b 0) * vartheta L ((τ x : ℝ) : ℂ) b) S
  exact (hA b).sub ((continuousOn_Psum_of_tensor L A hA (b 0)).mul
    (continuousOn_vartheta_path L hL hτ h0 h1 b))

/-- **`(P · )ϑ̇_{τ(x)}`, the third drift integrand of (5.91), applied to a moving tensor.** -/
theorem continuousOn_PsumVarthetaDot_of_tensor (hL : 3 ≤ L) {n : ℕ} {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (A : X → LoopArg L (n + 1) → ℂ) (hA : ∀ b, ContinuousOn (fun x => A x b) S)
    (b : LoopArg L (n + 1)) :
    ContinuousOn (fun x => Psum L (A x) (b 0) * SumZeroDyn.varthetaDot L (τ x) b) S :=
  (continuousOn_Psum_of_tensor L A hA (b 0)).mul
    (continuousOn_varthetaDot_path L hL hτ h0 h1 b)

/-- **`𝒢_{τ(x),σ}` applied to a moving tensor is continuous** — a finite sum with continuous
kernel. -/
theorem continuousOn_genS_of_tensor (hL : 3 ≤ L) {m : ℕ} {ξ : Fin m → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (A : X → LoopArg L m → ℂ) (hA : ∀ b, ContinuousOn (fun x => A x b) S)
    (a : LoopArg L m) :
    ContinuousOn (fun x =>
      SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ)) (A x) a) S := by
  simp only [SumZeroDyn.genOp]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun c _ => ?_
  exact (continuousOn_genSM_path L hL hξ hτ h0 h1 i (a i) c).mul (hA _)

/-- **`[Q_{τ(x)}, Θ_{τ(x),σ}]`, the second drift integrand of (5.91), applied to a moving
tensor.**  (5.99) writes the commutator as `𝒢 ∘ ((P∘A)ϑ) - (P∘(𝒢∘A))ϑ`
(`RBM.SumZeroDyn.commOp_eq`), and every block of that is one of the lemmas above. -/
theorem continuousOn_commS_of_tensor (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (A : X → LoopArg L (n + 1) → ℂ) (hA : ∀ b, ContinuousOn (fun x => A x b) S)
    (a : LoopArg L (n + 1)) :
    ContinuousOn (fun x => SumZeroDyn.commS L ξ ((τ x : ℝ) : ℂ) (A x) a) S := by
  have hkey : ∀ x : X, SumZeroDyn.commS L ξ ((τ x : ℝ) : ℂ) (A x) a
      = SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ))
            (fun b => Psum L (A x) (b 0) * vartheta L ((τ x : ℝ) : ℂ) b) a
        - Psum L (SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ)) (A x)) (a 0)
            * vartheta L ((τ x : ℝ) : ℂ) a := by
    intro x
    have h := SumZeroDyn.commOp_eq L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ))
      ((τ x : ℝ) : ℂ) (A x)
    exact congrFun h a
  rw [show (fun x => SumZeroDyn.commS L ξ ((τ x : ℝ) : ℂ) (A x) a)
      = fun x => SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ))
            (fun b => Psum L (A x) (b 0) * vartheta L ((τ x : ℝ) : ℂ) b) a
        - Psum L (SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ)) (A x)) (a 0)
            * vartheta L ((τ x : ℝ) : ℂ) a from funext hkey]
  refine ContinuousOn.sub ?_ ?_
  · exact continuousOn_genS_of_tensor L hL hξ hτ h0 h1
      (fun x b => Psum L (A x) (b 0) * vartheta L ((τ x : ℝ) : ℂ) b)
      (fun b => (continuousOn_Psum_of_tensor L A hA (b 0)).mul
        (continuousOn_vartheta_path L hL hτ h0 h1 b)) a
  · exact (continuousOn_Psum_of_tensor L
      (fun x => SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((τ x : ℝ) : ℂ)) (A x))
      (fun b => continuousOn_genS_of_tensor L hL hξ hτ h0 h1 A hA b) (a 0)).mul
      (continuousOn_vartheta_path L hL hτ h0 h1 a)

/-- **`Q_{τ(x)} ⊗ Q_{τ(x)}` of (5.104) applied to a moving tensor.** -/
theorem continuousOn_QQ_of_tensor (hL : 3 ≤ L) {k : ℕ} {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S) (h0 : ∀ x ∈ S, 0 ≤ τ x) (h1 : ∀ x ∈ S, τ x < 1)
    (Bt : X → LoopArg L ((k + 1) + (k + 1)) → ℂ)
    (hB : ∀ c, ContinuousOn (fun x => Bt x c) S) (c : LoopArg L ((k + 1) + (k + 1))) :
    ContinuousOn (fun x => SumZeroDyn.QQ L ((τ x : ℝ) : ℂ) (Bt x) c) S := by
  have hexp : ∀ x : X, SumZeroDyn.QQ L ((τ x : ℝ) : ℂ) (Bt x) c
      = Bt x (Fin.append (SumZeroDyn.spl1 L c) (SumZeroDyn.spl2 L c))
        - Psum₁ L (fun a b => Bt x (Fin.append a b)) (SumZeroDyn.spl1 L c 0)
            (SumZeroDyn.spl2 L c) * vartheta L ((τ x : ℝ) : ℂ) (SumZeroDyn.spl1 L c)
        - Psum₂ L (fun a b => Bt x (Fin.append a b)) (SumZeroDyn.spl1 L c)
            (SumZeroDyn.spl2 L c 0) * vartheta L ((τ x : ℝ) : ℂ) (SumZeroDyn.spl2 L c)
        + Psum₁₂ L (fun a b => Bt x (Fin.append a b)) (SumZeroDyn.spl1 L c 0)
            (SumZeroDyn.spl2 L c 0)
            * (vartheta L ((τ x : ℝ) : ℂ) (SumZeroDyn.spl1 L c)
              * vartheta L ((τ x : ℝ) : ℂ) (SumZeroDyn.spl2 L c)) := fun x =>
    Qop₁_Qop₂_apply L (fun a b => Bt x (Fin.append a b)) _ _
  rw [show (fun x => SumZeroDyn.QQ L ((τ x : ℝ) : ℂ) (Bt x) c) = _ from funext hexp]
  have hϑ1 := continuousOn_vartheta_path L hL hτ h0 h1 (SumZeroDyn.spl1 L c)
  have hϑ2 := continuousOn_vartheta_path L hL hτ h0 h1 (SumZeroDyn.spl2 L c)
  refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.sub (hB _) ?_) ?_) ?_
  · exact (continuousOn_finsetSum _ fun _ _ => hB _).mul hϑ1
  · exact (continuousOn_finsetSum _ fun _ _ => hB _).mul hϑ2
  · exact (continuousOn_finsetSum _ fun _ _ =>
      continuousOn_finsetSum _ fun _ _ => hB _).mul (hϑ1.mul hϑ2)

end PathOp

/-! ### Crude window bounds for `[Q_u, Θ_{u,σ}]` and `ϑ̇_u`

The sharp bounds `RBM.SumZeroDyn.norm_commS_le` (5.99) and `RBM.SumZeroDyn.norm_varthetaDot_le`
carry the decay length `ℓ̂_u`, which is not what the interval integrabilities need; all they
need is *some* window-uniform constant.  For the commutator that is `RBM.SumZeroDyn.commOp_eq`
plus the row `ℓ¹` bound `RBM.SumZeroDyn.sum_norm_genSM_row_le_real`; for `ϑ̇_u` it is
continuity on a compact window. -/

section CrudeBounds

variable (L : ℕ) [NeZero L]

/-- **`[Q_u, Θ_{u,σ}]` is bounded in the max norm on the window**, with the crude constant
`2(n+1)(1-u)^{-1}` times the block cardinality. -/
theorem norm_commS_ofReal_le_of_bdd (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {ξ : Fin (n + 1) → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    (A : LoopArg L (n + 1) → ℂ) {C : ℝ} (hA : ∀ b, ‖A b‖ ≤ C) (a : LoopArg L (n + 1)) :
    ‖SumZeroDyn.commS L ξ ((u : ℝ) : ℂ) A a‖
      ≤ (2 * ((n : ℝ) + 1) * (1 - u)⁻¹) * ((Fintype.card (LoopArg L n) : ℝ) * C) := by
  classical
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hA a)
  have h1u : (0 : ℝ) < 1 - u := by linarith
  set card : ℝ := (Fintype.card (LoopArg L n) : ℝ) with hcard
  have hcard0 : 0 ≤ card := Nat.cast_nonneg _
  have hρ : ∀ (i : Fin (n + 1)) (x : ZMod L),
      ∑ c, ‖SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ) i x c‖ ≤ (1 - u)⁻¹ :=
    fun i x => SumZeroDyn.sum_norm_genSM_row_le_real L hL hu0 hu1 (hξ i) x
  have hB1 : ∀ b : LoopArg L (n + 1),
      ‖Psum L A (b 0) * vartheta L ((u : ℝ) : ℂ) b‖ ≤ card * C := by
    intro b
    rw [norm_mul]
    calc ‖Psum L A (b 0)‖ * ‖vartheta L ((u : ℝ) : ℂ) b‖ ≤ (card * C) * 1 :=
          mul_le_mul (norm_Psum_le_of_bdd L A hA (b 0))
            (norm_vartheta_ofReal_le_one L hL hu0 hu1 b) (norm_nonneg _) (by positivity)
      _ = card * C := mul_one _
  have h1 := SumZeroDyn.norm_genOp_le L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ))
    (B := fun b => Psum L A (b 0) * vartheta L ((u : ℝ) : ℂ) b) (by positivity) hB1 hρ a
  have hgA : ∀ b : LoopArg L (n + 1),
      ‖SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ)) A b‖
        ≤ ((n : ℝ) + 1) * (1 - u)⁻¹ * C := by
    intro b
    have h := SumZeroDyn.norm_genOp_le L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ)) hC hA hρ b
    refine h.trans (le_of_eq ?_)
    push_cast
    ring
  have h2 : ‖Psum L (SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ)) A) (a 0)‖
      ≤ card * (((n : ℝ) + 1) * (1 - u)⁻¹ * C) :=
    norm_Psum_le_of_bdd L _ hgA (a 0)
  have hmul : ‖Psum L (SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ)) A) (a 0)‖
        * ‖vartheta L ((u : ℝ) : ℂ) a‖
      ≤ (card * (((n : ℝ) + 1) * (1 - u)⁻¹ * C)) * 1 :=
    mul_le_mul h2 (norm_vartheta_ofReal_le_one L hL hu0 hu1 a) (norm_nonneg _) (by positivity)
  have heq : SumZeroDyn.commS L ξ ((u : ℝ) : ℂ) A a
      = SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ))
            (fun b => Psum L A (b 0) * vartheta L ((u : ℝ) : ℂ) b) a
        - Psum L (SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ)) A) (a 0)
            * vartheta L ((u : ℝ) : ℂ) a :=
    congrFun (SumZeroDyn.commOp_eq L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ))
      ((u : ℝ) : ℂ) A) a
  have hmul2 : ‖Psum L (SumZeroDyn.genOp L (SumZeroDyn.genSM L ξ ((u : ℝ) : ℂ)) A) (a 0)
        * vartheta L ((u : ℝ) : ℂ) a‖
      ≤ (card * (((n : ℝ) + 1) * (1 - u)⁻¹ * C)) * 1 := by
    rw [norm_mul]; exact hmul
  rw [heq]
  refine (norm_sub_le _ _).trans ((add_le_add h1 hmul2).trans (le_of_eq ?_))
  push_cast
  ring

/-- **`ϑ̇_u` is bounded on any window inside `[0, 1)`**, uniformly in the loop argument: it is
continuous and the window is compact, and there are only finitely many arguments. -/
theorem exists_bdd_varthetaDot (hL : 3 ≤ L) {n : ℕ} {u₀ u₁ : ℝ} (h0 : 0 ≤ u₀) (h1 : u₁ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc u₀ u₁, ∀ a : LoopArg L (n + 1),
      ‖SumZeroDyn.varthetaDot L u a‖ ≤ C := by
  classical
  set F : ℝ → ℝ := fun u => ∑ a : LoopArg L (n + 1), ‖SumZeroDyn.varthetaDot L u a‖ with hF
  have hFc : ContinuousOn F (Set.Icc u₀ u₁) :=
    continuousOn_finsetSum _ fun a _ =>
      (continuousOn_varthetaDot_path L hL (τ := id) continuousOn_id
        (fun u hu => le_trans h0 hu.1) (fun u hu => lt_of_le_of_lt hu.2 h1) a).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn hFc
  refine ⟨|C|, abs_nonneg _, fun u hu a => ?_⟩
  have hle : ‖SumZeroDyn.varthetaDot L u a‖ ≤ F u :=
    Finset.single_le_sum (f := fun a' : LoopArg L (n + 1) => ‖SumZeroDyn.varthetaDot L u a'‖)
      (fun a' _ => norm_nonneg _) (Finset.mem_univ a)
  exact hle.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

end CrudeBounds

/-! ### `(L - K)_u` along the Gaussian flow: envelope and continuity -/

section LkWindow

variable {d : Dims}

/-- **The pointwise envelope of `(L - K)_u` on the window**, uniform in the sample point:
`RBM.norm_gloop_le_of_le_abs_im` at the Hermitian `H_u` plus the primitive's own window
bound. -/
theorem exists_bdd_lkT_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d, ∀ b : LoopArg (d.L N) (n + 2),
      ‖SumZeroDyn.lkT (sample d) E N u ω σ b‖ ≤ C := by
  have hη0 : 0 < (1 - v) * (mE E).im := window_eta_pos hE hv1
  refine ⟨((1 - v) * (mE E).im)⁻¹ ^ (n + 2) * ((d.W N : ℝ))⁻¹ ^ (n + 1) + cK,
    by positivity, fun u hu ω b => ?_⟩
  have hlen : (toIdx σ b).a.length = n + 2 := toIdx_length σ b
  have hg := norm_gloop_le_of_le_abs_im (Hflow_isHermitian d N u ω) hη0
    (window_le_abs_im hE hv1 u hu) (toIdx σ b) (toIdx_wf σ b) (by rw [hlen]; omega)
  rw [hlen, show n + 2 - 1 = n + 1 from rfl] at hg
  show ‖gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (LoopData.idx (σ, b))
      - (band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hg (hKb u hu b))

/-- `ω ↦ (L - K)_u(H_u ω)` is continuous, hence measurable. -/
theorem continuous_lkT_omega (E : ℝ) (N : ℕ) {u : ℝ} (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {m : ℕ} (σ : Fin m → Bool) (b : LoopArg (d.L N) m) :
    Continuous fun ω : Ω d => SumZeroDyn.lkT (sample d) E N u ω σ b := by
  rw [← continuousOn_univ]
  exact continuousOn_lkFun_path (X := Ω d) d N E (τ := fun _ => u)
    (Mt := fun ω => Hflow d N u ω) continuousOn_const
    (continuous_Hflow d N u).continuousOn (fun ω => Hflow_isHermitian d N u ω)
    (fun _ _ => hz) (fun _ _ => hm) σ b

/-- `u ↦ (L - K)_u(H_u ω)` is continuous on the window. -/
theorem continuousOn_lkT_time (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {m : ℕ} (σ : Fin m → Bool) (b : LoopArg (d.L N) m) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => SumZeroDyn.lkT (sample d) E N u ω σ b) (Set.Icc s v) :=
  continuousOn_lkFun_path (X := ℝ) d N E (τ := id) (Mt := fun u => Hflow d N u ω)
    continuousOn_id (continuous_Hflow_time d N ω).continuousOn
    (fun u => Hflow_isHermitian d N u ω)
    (fun u hu => window_im_ne_zero hE hv1 u hu)
    (fun u hu => window_norm_mul_lt hE.le hs0 hv1 u hu) σ b

end LkWindow

/-! ### The four integrands of (5.91)/(5.103): envelope, sample continuity, time continuity

Every statement in this section is one of the two hypothesis families that
`RBM.Gauss.hbound_qMomentObsT_gauss` (T225) leaves open, or one of the interval
integrabilities of `RBM.MomentDuhamel.momentIneqQ_of_derivBound`. -/

section QIntegrands

variable {d : Dims}

/-! #### `Ψ^Q₁ = (U_{u,v,σ} ∘ Q_u (L-K)_u)_a` -/

/-- **The envelope of `Ψ^Q₁` on the window**, uniform in the sample point. -/
theorem exists_bdd_uker_Qop_lkT (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (ξ : Fin (n + 2) → ℂ)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) ξ ((u : ℝ) : ℂ) t
        (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖ ≤ C := by
  classical
  obtain ⟨Clk, hClk0, hClk⟩ := exists_bdd_lkT_gauss E N hE hv1 σ hcK hKb
  set Cq : ℝ := (1 + (Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ)) * Clk with hCq
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := fun u : ℝ => ukerRow ξ t a u * Cq)
    ((continuous_ukerRow ξ t a).mul continuous_const).continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu ω => ?_⟩
  have hb := norm_Uker_apply_le_ukerRow ξ t u
    (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a (C := Cq)
    (fun b => norm_Qop_ofReal_le_of_bdd (d.L N) (d.three_le_L N) (hs0.trans hu.1)
      (lt_of_le_of_lt hu.2 hv1) (SumZeroDyn.lkT (sample d) E N u ω σ)
      (fun b' => hClk u hu ω b') b)
  exact hb.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

/-- `Ψ^Q₁` is continuous in the sample point, hence measurable. -/
theorem continuous_uker_Qop_lkT_omega (E : ℝ) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (ξ : Fin (n + 2) → ℂ)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) ξ ((u : ℝ) : ℂ) t
      (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a := by
  rw [← continuousOn_univ]
  refine continuousOn_Uker_of_tensor (d.L N) ξ t (τ := fun _ : Ω d => u) continuousOn_const
    (fun ω => Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) (fun b => ?_) a
  exact continuousOn_Qop_of_tensor (d.L N) (d.three_le_L N) (τ := fun _ : Ω d => u)
    continuousOn_const (fun _ _ => hu0) (fun _ _ => hu1)
    (fun ω => SumZeroDyn.lkT (sample d) E N u ω σ)
    (fun b' => (continuous_lkT_omega E N hz hm σ b').continuousOn) b

/-- `u ↦ Ψ^Q₁` is continuous on the window. -/
theorem continuousOn_uker_Qop_lkT_time (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (ξ : Fin (n + 2) → ℂ)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => Uker (d.L N) ξ ((u : ℝ) : ℂ) t
      (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a) (Set.Icc s v) := by
  refine continuousOn_Uker_of_tensor (d.L N) ξ t (τ := id) continuousOn_id
    (fun u => Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) (fun b => ?_) a
  exact continuousOn_Qop_of_tensor (d.L N) (d.three_le_L N) (τ := id) continuousOn_id
    (fun u hu => hs0.trans hu.1) (fun u hu => lt_of_le_of_lt hu.2 hv1)
    (fun u => SumZeroDyn.lkT (sample d) E N u ω σ)
    (fun b' => continuousOn_lkT_time E N hE hs0 hv1 σ b' ω) b

/-- **Item 1 of the `Q_t` route: `ψ_u = (E|Ψ^Q₁|^{2p})^{1/p}` is bounded on the window.** -/
theorem exists_bdd_psiQ_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (p : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc s v,
      (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
          (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
            ^ (2 * p) ∂(band d).P) ^ ((1 : ℝ) / p) ≤ C := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ :=
    exists_bdd_uker_Qop_lkT E N hE hs0 hv1 σ (xiOf (mSigma E) σ) a t hcK hKb
  refine ⟨(C ^ (2 * p)) ^ ((1 : ℝ) / p), fun u hu => ?_⟩
  have hcont := continuous_uker_Qop_lkT_omega E N (hs0.trans hu.1)
    (lt_of_le_of_lt hu.2 hv1) (window_im_ne_zero hE hv1 u hu)
    (window_norm_mul_lt hE.le hs0 hv1 u hu) σ (xiOf (mSigma E) σ) a t
  have hint : Integrable (fun ω : Ω d =>
      |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖| ^ (2 * p))
      (band d).P := by
    refine integrable_of_continuous_of_bound (hcont.norm.abs.pow (2 * p))
      (C := C ^ (2 * p)) fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_norm]; exact hC u hu ω) _
  have hle : (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖| ^ (2 * p)
        ∂(band d).P) ≤ C ^ (2 * p) := by
    have h := integral_mono hint (integrable_const (C ^ (2 * p))) (fun ω => by
      rw [abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC u hu ω) _)
    simpa using h
  exact Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) hle
    (by positivity)

/-- **Item 2 of the `Q_t` route: `u ↦ E|Ψ^Q₁|^{2p}` is continuous on the window.** -/
theorem continuousOn_integral_psiQ_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (p : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ContinuousOn (fun u : ℝ => ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
        ^ (2 * p) ∂(band d).P) (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ :=
    exists_bdd_uker_Qop_lkT E N hE hs0 hv1 σ (xiOf (mSigma E) σ) a t hcK hKb
  refine continuousOn_integral_abs_pow_of_envelope (C := C) (2 * p) ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_Qop_lkT_omega E N (hs0.trans hu.1) (lt_of_le_of_lt hu.2 hv1)
      (window_im_ne_zero hE hv1 u hu) (window_norm_mul_lt hE.le hs0 hv1 u hu) σ
      (xiOf (mSigma E) σ) a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · exact fun ω => (continuousOn_uker_Qop_lkT_time E N hE hs0 hv1 σ
      (xiOf (mSigma E) σ) a t ω).norm

/-- `u ↦ ‖Ψ^Q₁‖_q` is continuous on the window. -/
theorem continuousOn_momNorm_Qop_lkT_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ContinuousOn (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖))
      (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ :=
    exists_bdd_uker_Qop_lkT E N hE hs0 hv1 σ (xiOf (mSigma E) σ) a t hcK hKb
  refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_Qop_lkT_omega E N (hs0.trans hu.1) (lt_of_le_of_lt hu.2 hv1)
      (window_im_ne_zero hE hv1 u hu) (window_norm_mul_lt hE.le hs0 hv1 u hu) σ
      (xiOf (mSigma E) σ) a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · exact fun ω => (continuousOn_uker_Qop_lkT_time E N hE hs0 hv1 σ
      (xiOf (mSigma E) σ) a t ω).norm

/-! #### `[Q_u, Θ_{u,σ}](L-K)_u`, the second drift integrand of (5.91) -/

/-- **The envelope of `(U ∘ [Q_u,Θ_{u,σ}](L-K)_u)_a` on the window.** -/
theorem exists_bdd_uker_commS_lkT (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖ ≤ C := by
  classical
  obtain ⟨Clk, hClk0, hClk⟩ := exists_bdd_lkT_gauss E N hE hv1 σ hcK hKb
  set Cc : ℝ := (2 * ((n : ℝ) + 2) * (1 - v)⁻¹)
    * ((Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ) * Clk) with hCc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := fun u : ℝ => ukerRow (xiOf (mSigma E) σ) t a u * Cc)
    ((continuous_ukerRow (xiOf (mSigma E) σ) t a).mul continuous_const).continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu ω => ?_⟩
  have hu0 : 0 ≤ u := hs0.trans hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 hv1
  have hmono : (1 - u)⁻¹ ≤ (1 - v)⁻¹ :=
    inv_anti₀ (by linarith) (by linarith [hu.2])
  have hpt : ∀ b : LoopArg (d.L N) (n + 2),
      ‖SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
        (SumZeroDyn.lkT (sample d) E N u ω σ) b‖ ≤ Cc := by
    intro b
    refine (norm_commS_ofReal_le_of_bdd (d.L N) (d.three_le_L N) hu0 hu1
      (ξ := xiOf (mSigma E) σ) (fun i => le_of_eq (norm_xiOf_mSigma hE.le σ i))
      (SumZeroDyn.lkT (sample d) E N u ω σ) (fun b' => hClk u hu ω b') b).trans ?_
    rw [hCc]
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    have hkey : (2 * (((n + 1 : ℕ) : ℝ) + 1) * (1 - u)⁻¹)
        ≤ (2 * ((n : ℝ) + 2) * (1 - v)⁻¹) := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    exact mul_le_mul_of_nonneg_right hkey
      (mul_nonneg (Nat.cast_nonneg _) hClk0)
  have hb := norm_Uker_apply_le_ukerRow (xiOf (mSigma E) σ) t u _ a (C := Cc) hpt
  exact hb.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

/-- The second drift integrand is continuous in the sample point. -/
theorem continuous_uker_commS_lkT_omega (E : ℝ) (N : ℕ) (hE : |E| ≤ 2) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
        (SumZeroDyn.lkT (sample d) E N u ω σ)) a := by
  rw [← continuousOn_univ]
  refine continuousOn_Uker_of_tensor (d.L N) (xiOf (mSigma E) σ) t
    (τ := fun _ : Ω d => u) continuousOn_const _ (fun b => ?_) a
  exact continuousOn_commS_of_tensor (d.L N) (d.three_le_L N)
    (ξ := xiOf (mSigma E) σ) (fun i => le_of_eq (norm_xiOf_mSigma hE σ i))
    (τ := fun _ : Ω d => u) continuousOn_const (fun _ _ => hu0) (fun _ _ => hu1)
    (fun ω => SumZeroDyn.lkT (sample d) E N u ω σ)
    (fun b' => (continuous_lkT_omega E N hz hm σ b').continuousOn) b

/-- The second drift integrand is continuous in the time, on the window. -/
theorem continuousOn_uker_commS_lkT_time (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
        (SumZeroDyn.lkT (sample d) E N u ω σ)) a) (Set.Icc s v) := by
  refine continuousOn_Uker_of_tensor (d.L N) (xiOf (mSigma E) σ) t (τ := id) continuousOn_id
    _ (fun b => ?_) a
  exact continuousOn_commS_of_tensor (d.L N) (d.three_le_L N)
    (ξ := xiOf (mSigma E) σ) (fun i => le_of_eq (norm_xiOf_mSigma hE.le σ i))
    (τ := id) continuousOn_id (fun u hu => hs0.trans hu.1)
    (fun u hu => lt_of_le_of_lt hu.2 hv1)
    (fun u => SumZeroDyn.lkT (sample d) E N u ω σ)
    (fun b' => continuousOn_lkT_time E N hE hs0 hv1 σ b' ω) b

/-- **The second drift integrand's interval integrability.** -/
theorem intervalIntegrable_momNorm_commS_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)) volume s v := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_commS_lkT E N hE hs0 hv1 σ a t hcK hKb
  refine intervalIntegrable_momNorm_of_envelope hsv (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_commS_lkT_omega E N hE.le (hs0.trans hu.1)
      (lt_of_le_of_lt hu.2 hv1) (window_im_ne_zero hE hv1 u hu)
      (window_norm_mul_lt hE.le hs0 hv1 u hu) σ a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · exact fun ω => (continuousOn_uker_commS_lkT_time E N hE hs0 hv1 σ a t ω).norm

/-! #### `(P(L-K)_u)ϑ̇_u`, the third drift integrand of (5.91) -/

/-- **The envelope of `(U ∘ (P(L-K)_u)ϑ̇_u)_a` on the window.** -/
theorem exists_bdd_uker_PsumVarthetaDot_lkT (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) u b) a‖ ≤ C := by
  classical
  obtain ⟨Clk, hClk0, hClk⟩ := exists_bdd_lkT_gauss E N hE hv1 σ hcK hKb
  obtain ⟨Cd, hCd0, hCd⟩ :=
    exists_bdd_varthetaDot (d.L N) (n := n + 1) (d.three_le_L N) hs0 hv1
  set Cp : ℝ := ((Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ) * Clk) * Cd with hCp
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := fun u : ℝ => ukerRow (xiOf (mSigma E) σ) t a u * Cp)
    ((continuous_ukerRow (xiOf (mSigma E) σ) t a).mul continuous_const).continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu ω => ?_⟩
  have hpt : ∀ b : LoopArg (d.L N) (n + 2),
      ‖Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
        * SumZeroDyn.varthetaDot (d.L N) u b‖ ≤ Cp := by
    intro b
    rw [norm_mul, hCp]
    exact mul_le_mul
      (norm_Psum_le_of_bdd (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ)
        (fun b' => hClk u hu ω b') (b 0))
      (hCd u hu b) (norm_nonneg _) (by positivity)
  have hb := norm_Uker_apply_le_ukerRow (xiOf (mSigma E) σ) t u _ a (C := Cp) hpt
  exact hb.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

/-- The third drift integrand is continuous in the sample point. -/
theorem continuous_uker_PsumVarthetaDot_lkT_omega (E : ℝ) (N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
        * SumZeroDyn.varthetaDot (d.L N) u b) a := by
  rw [← continuousOn_univ]
  refine continuousOn_Uker_of_tensor (d.L N) (xiOf (mSigma E) σ) t
    (τ := fun _ : Ω d => u) continuousOn_const _ (fun b => ?_) a
  exact continuousOn_PsumVarthetaDot_of_tensor (d.L N) (d.three_le_L N)
    (τ := fun _ : Ω d => u) continuousOn_const (fun _ _ => hu0) (fun _ _ => hu1)
    (fun ω => SumZeroDyn.lkT (sample d) E N u ω σ)
    (fun b' => (continuous_lkT_omega E N hz hm σ b').continuousOn) b

/-- The third drift integrand is continuous in the time, on the window. -/
theorem continuousOn_uker_PsumVarthetaDot_lkT_time (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
        * SumZeroDyn.varthetaDot (d.L N) u b) a) (Set.Icc s v) := by
  refine continuousOn_Uker_of_tensor (d.L N) (xiOf (mSigma E) σ) t (τ := id) continuousOn_id
    _ (fun b => ?_) a
  exact continuousOn_PsumVarthetaDot_of_tensor (d.L N) (d.three_le_L N) (τ := id)
    continuousOn_id (fun u hu => hs0.trans hu.1) (fun u hu => lt_of_le_of_lt hu.2 hv1)
    (fun u => SumZeroDyn.lkT (sample d) E N u ω σ)
    (fun b' => continuousOn_lkT_time E N hE hs0 hv1 σ b' ω) b

/-- **The third drift integrand's interval integrability.** -/
theorem intervalIntegrable_momNorm_PsumVarthetaDot_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2)
    {s v : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) u b) a‖)) volume s v := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_PsumVarthetaDot_lkT E N hE hs0 hv1 σ a t hcK hKb
  refine intervalIntegrable_momNorm_of_envelope hsv (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_PsumVarthetaDot_lkT_omega E N (hs0.trans hu.1)
      (lt_of_le_of_lt hu.2 hv1) (window_im_ne_zero hE hv1 u hu)
      (window_norm_mul_lt hE.le hs0 hv1 u hu) σ a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · exact fun ω => (continuousOn_uker_PsumVarthetaDot_lkT_time E N hE hs0 hv1 σ a t ω).norm

/-! #### `(Q_u ⊗ Q_u)(E ⊗ E)_u`, the quadratic-variation integrand of (5.103) -/

/-- **The envelope of `((U⊗U) ∘ (Q_u⊗Q_u) ∘ (E⊗E)_u)_{a,a}` on the window.** -/
theorem exists_bdd_uker_QQ_eeFun (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) t
        (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
          (Fin.append a a)‖ ≤ C := by
  classical
  have hη0 : 0 < (1 - v) * (mE E).im := window_eta_pos hE hv1
  set Mee : ℝ := ((n + 2 : ℕ) : ℝ) * ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ)
    * (((1 - v) * (mE E).im)⁻¹ ^ (2 * (n + 2) + 2)
      * ((d.W N : ℝ))⁻¹ ^ (2 * (n + 2) + 1)))) with hMee
  have hMee0 : 0 ≤ Mee := by
    rw [hMee]; positivity
  set Cq : ℝ := (1 + (Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ)) ^ 2 * Mee with hCq
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := fun u : ℝ => ukerRow (SumZeroDyn.xi2 E σ) t (Fin.append a a) u * Cq)
    ((continuous_ukerRow (SumZeroDyn.xi2 E σ) t (Fin.append a a)).mul
      continuous_const).continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu ω => ?_⟩
  have hee : ∀ c : LoopArg (d.L N) ((n + 2) + (n + 2)),
      ‖MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ c‖ ≤ Mee := fun c =>
    norm_eeFun_herm_le d N E hη0 (window_le_abs_im hE hv1 u hu)
      (Hflow_isHermitian d N u ω) σ c
  have hqq : ∀ c : LoopArg (d.L N) ((n + 2) + (n + 2)),
      ‖SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
        (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ) c‖ ≤ Cq := fun c =>
    norm_QQ_ofReal_le_of_bdd (d.L N) (k := n + 1) (d.three_le_L N) (hs0.trans hu.1)
      (lt_of_le_of_lt hu.2 hv1) _ hee c
  have hb := norm_Uker_apply_le_ukerRow (SumZeroDyn.xi2 E σ) t u _ (Fin.append a a)
    (C := Cq) hqq
  exact hb.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

/-- The quadratic-variation integrand is continuous in the sample point. -/
theorem continuous_uker_QQ_eeFun_omega (E : ℝ) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hz : (zt E u).im ≠ 0) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
        (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)) (Fin.append a a) := by
  rw [← continuousOn_univ]
  refine continuousOn_Uker_of_tensor (d.L N) (SumZeroDyn.xi2 E σ) t
    (τ := fun _ : Ω d => u) continuousOn_const _ (fun c => ?_) (Fin.append a a)
  refine continuousOn_QQ_of_tensor (d.L N) (k := n + 1) (d.three_le_L N)
    (τ := fun _ : Ω d => u) continuousOn_const (fun _ _ => hu0) (fun _ _ => hu1)
    (fun ω => MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ) (fun c' => ?_) c
  exact continuousOn_eeFun_path (X := Ω d) d N E (τ := fun _ => u)
    (Mt := fun ω => Hflow d N u ω) continuousOn_const
    (continuous_Hflow d N u).continuousOn (fun ω => Hflow_isHermitian d N u ω)
    (fun _ _ => hz) σ c'

/-- The quadratic-variation integrand is continuous in the time, on the window. -/
theorem continuousOn_uker_QQ_eeFun_time (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
        (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)) (Fin.append a a))
      (Set.Icc s v) := by
  refine continuousOn_Uker_of_tensor (d.L N) (SumZeroDyn.xi2 E σ) t (τ := id)
    continuousOn_id _ (fun c => ?_) (Fin.append a a)
  refine continuousOn_QQ_of_tensor (d.L N) (k := n + 1) (d.three_le_L N) (τ := id)
    continuousOn_id (fun u hu => hs0.trans hu.1) (fun u hu => lt_of_le_of_lt hu.2 hv1)
    (fun u => MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ) (fun c' => ?_) c
  exact continuousOn_eeFun_path (X := ℝ) d N E (τ := id)
    (Mt := fun u => Hflow d N u ω) continuousOn_id
    (continuous_Hflow_time d N ω).continuousOn (fun u => Hflow_isHermitian d N u ω)
    (fun u hu => window_im_ne_zero hE hv1 u hu) σ c'

/-- **The quadratic-variation integrand's interval integrability.** -/
theorem intervalIntegrable_momNorm_QQ_eeFun_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) :
    IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) t
        (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
          (Fin.append a a)‖)) volume s v := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_QQ_eeFun E N hE hs0 hv1 σ a t
  refine intervalIntegrable_momNorm_of_envelope hsv (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_QQ_eeFun_omega E N (hs0.trans hu.1) (lt_of_le_of_lt hu.2 hv1)
      (window_im_ne_zero hE hv1 u hu) σ a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · exact fun ω => (continuousOn_uker_QQ_eeFun_time E N hE hs0 hv1 σ a t ω).norm

/-! #### `Q_u F_u`, the first drift integrand of (5.91)

⚠ This is the **only** one of the four that is not unconditional here.  `Q_u` is not a
composition of propagators, so `RBM.Gauss.uker_driftF_eq` — the identity by which T212 avoided
ever bounding `RBM.DriftDef.driftF` pointwise — does not apply: `(U ∘ Q_u F_u)_a` reads `F_u`
at `L^{n+1}` *different* loop arguments through `RBM.Psum`, so a **pointwise** envelope for
`F_u` is needed.  The repository does not have one (T212's route bounds only
`(U ∘ F_u)_a`; `RBM.DriftBound.norm_driftF_le` is (5.77), which is the stochastic-domination
statement, not a deterministic envelope), and it is taken here as the named hypothesis `hFb` —
the same shape `RBM.Gauss.hGd_Qop_driftF` of `RBM1D/Gauss/FastDecayFlow.lean` uses.  See the
report: closing `hFb` means the crude versions of `RBM.Decay.norm_eG_le`,
`norm_couplingLen_le` and `norm_primBil_sub_le` at `A = 1`, plus a window bound on
`RBM.Band.Kval` at **every** loop length `≤ n + 3`. -/

/-- **The envelope of `(U ∘ Q_u F_u)_a` on the window, from a pointwise envelope of `F_u`.** -/
theorem exists_bdd_uker_Qop_driftF (E : ℝ) (N : ℕ) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) {cF : ℝ}
    (hFb : ∀ u ∈ Set.Icc s v, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ∀ b : LoopArg (d.L N) (n + 2), ‖DriftDef.driftF (band d) E N u M σ b‖ ≤ cF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖ ≤ C := by
  classical
  set Cq : ℝ := (1 + (Fintype.card (LoopArg (d.L N) (n + 1)) : ℝ)) * cF with hCq
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := fun u : ℝ => ukerRow (xiOf (mSigma E) σ) t a u * Cq)
    ((continuous_ukerRow (xiOf (mSigma E) σ) t a).mul continuous_const).continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu ω => ?_⟩
  have hb := norm_Uker_apply_le_ukerRow (xiOf (mSigma E) σ) t u _ a (C := Cq)
    (fun b => norm_Qop_ofReal_le_of_bdd (d.L N) (d.three_le_L N) (hs0.trans hu.1)
      (lt_of_le_of_lt hu.2 hv1) (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)
      (fun b' => hFb u hu _ (Hflow_isHermitian d N u ω) b') b)
  exact hb.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

/-- The first drift integrand is continuous in the sample point. -/
theorem continuous_uker_Qop_driftF_omega (E : ℝ) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (Qop (d.L N) ((u : ℝ) : ℂ)
        (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a := by
  rw [← continuousOn_univ]
  refine continuousOn_Uker_of_tensor (d.L N) (xiOf (mSigma E) σ) t
    (τ := fun _ : Ω d => u) continuousOn_const _ (fun b => ?_) a
  refine continuousOn_Qop_of_tensor (d.L N) (d.three_le_L N) (τ := fun _ : Ω d => u)
    continuousOn_const (fun _ _ => hu0) (fun _ _ => hu1)
    (fun ω => DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) (fun b' => ?_) b
  exact continuousOn_driftF_path (X := Ω d) d N E (τ := fun _ => u)
    (Mt := fun ω => Hflow d N u ω) continuousOn_const
    (continuous_Hflow d N u).continuousOn (fun ω => Hflow_isHermitian d N u ω)
    (fun _ _ => hz) (fun _ _ => hm) σ b'

/-- The first drift integrand is continuous in the time, on the window. -/
theorem continuousOn_uker_Qop_driftF_time (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (Qop (d.L N) ((u : ℝ) : ℂ)
        (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a) (Set.Icc s v) := by
  refine continuousOn_Uker_of_tensor (d.L N) (xiOf (mSigma E) σ) t (τ := id) continuousOn_id
    _ (fun b => ?_) a
  refine continuousOn_Qop_of_tensor (d.L N) (d.three_le_L N) (τ := id) continuousOn_id
    (fun u hu => hs0.trans hu.1) (fun u hu => lt_of_le_of_lt hu.2 hv1)
    (fun u => DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) (fun b' => ?_) b
  exact continuousOn_driftF_path (X := ℝ) d N E (τ := id)
    (Mt := fun u => Hflow d N u ω) continuousOn_id
    (continuous_Hflow_time d N ω).continuousOn (fun u => Hflow_isHermitian d N u ω)
    (fun u hu => window_im_ne_zero hE hv1 u hu)
    (fun u hu => window_norm_mul_lt hE.le hs0 hv1 u hu) σ b'

/-- `u ↦ ‖(U ∘ Q_u F_u)_a‖_q` is continuous on the window. -/
theorem continuousOn_momNorm_Qop_driftF_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) {cF : ℝ}
    (hFb : ∀ u ∈ Set.Icc s v, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ∀ b : LoopArg (d.L N) (n + 2), ‖DriftDef.driftF (band d) E N u M σ b‖ ≤ cF) :
    ContinuousOn (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖)) (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_Qop_driftF E N hs0 hv1 σ a t hFb
  refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_Qop_driftF_omega E N (hs0.trans hu.1) (lt_of_le_of_lt hu.2 hv1)
      (window_im_ne_zero hE hv1 u hu) (window_norm_mul_lt hE.le hs0 hv1 u hu) σ a
      t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · exact fun ω => (continuousOn_uker_Qop_driftF_time E N hE hs0 hv1 σ a t ω).norm

/-- **The first drift integrand's interval integrability.** -/
theorem intervalIntegrable_momNorm_Qop_driftF_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) {cF : ℝ}
    (hFb : ∀ u ∈ Set.Icc s v, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ∀ b : LoopArg (d.L N) (n + 2), ‖DriftDef.driftF (band d) E N u M σ b‖ ≤ cF) :
    IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (Qop (d.L N) ((u : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖)) volume s v :=
  (continuousOn_momNorm_Qop_driftF_gauss E N hE hs0 hv1 σ a t q
    hFb).intervalIntegrable_of_Icc hsv

/-- **The product `ψ · f` of the `Q_t` route**, on every initial segment of the window: the
three drift integrands of (5.91) are summed *before* the product, exactly as
`RBM.MomentDuhamel.momentIneqQ_of_derivBound` writes it. -/
theorem intervalIntegrable_psiQ_mul_driftQ_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (q : ℕ) {cK cF : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK)
    (hFb : ∀ u ∈ Set.Icc s v, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, M.IsHermitian →
      ∀ b : LoopArg (d.L N) (n + 2), ‖DriftDef.driftF (band d) E N u M σ b‖ ≤ cF) :
    ∀ u ∈ Set.Icc s v, IntervalIntegrable (fun r : ℝ =>
      MomentDuhamel.momNorm (band d).P q (fun ω =>
        ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
          (Qop (d.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖)
      * (MomentDuhamel.momNorm (band d).P q (fun ω =>
          ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
            (Qop (d.L N) ((r : ℝ) : ℂ)
              (DriftDef.driftF (band d) E N r ((sample d).H N r ω) σ)) a‖)
        + MomentDuhamel.momNorm (band d).P q (fun ω =>
            ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
              (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ)
                (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖)
        + MomentDuhamel.momNorm (band d).P q (fun ω =>
            ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
              (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N r ω σ) (b 0)
                * SumZeroDyn.varthetaDot (d.L N) r b) a‖))) volume s u := by
  classical
  have hprob := (band d).isProbabilityMeasure
  intro u hu
  have hmono : Set.Icc s u ⊆ Set.Icc s v := Set.Icc_subset_Icc le_rfl hu.2
  refine ContinuousOn.intervalIntegrable_of_Icc hu.1 ?_
  have hψ := continuousOn_momNorm_Qop_lkT_gauss E N hE hs0 hv1 σ a t q hcK hKb
  have h1 := continuousOn_momNorm_Qop_driftF_gauss E N hE hs0 hv1 σ a t q hFb
  have h2 : ContinuousOn (fun r : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
        (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖)) (Set.Icc s v) := by
    obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_commS_lkT E N hE hs0 hv1 σ a t hcK hKb
    refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
    · intro r hr
      exact (continuous_uker_commS_lkT_omega E N hE.le (hs0.trans hr.1)
        (lt_of_le_of_lt hr.2 hv1) (window_im_ne_zero hE hv1 r hr)
        (window_norm_mul_lt hE.le hs0 hv1 r hr) σ a t).norm.aestronglyMeasurable
    · intro r hr ω'
      rw [abs_norm]
      exact hC r hr ω'
    · exact fun ω' => (continuousOn_uker_commS_lkT_time E N hE hs0 hv1 σ a t ω').norm
  have h3 : ContinuousOn (fun r : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
        (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N r ω σ) (b 0)
          * SumZeroDyn.varthetaDot (d.L N) r b) a‖)) (Set.Icc s v) := by
    obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_PsumVarthetaDot_lkT E N hE hs0 hv1 σ a t hcK hKb
    refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
    · intro r hr
      exact (continuous_uker_PsumVarthetaDot_lkT_omega E N (hs0.trans hr.1)
        (lt_of_le_of_lt hr.2 hv1) (window_im_ne_zero hE hv1 r hr)
        (window_norm_mul_lt hE.le hs0 hv1 r hr) σ a t).norm.aestronglyMeasurable
    · intro r hr ω'
      rw [abs_norm]
      exact hC r hr ω'
    · exact fun ω' => (continuousOn_uker_PsumVarthetaDot_lkT_time E N hE hs0 hv1 σ a t ω').norm
  exact ((hψ.mul ((h1.add h2).add h3)).mono hmono)

end QIntegrands

/-! ### The `φ'` slot: interval integrability from the test-function class (T226 item 3)

The derivative slot of `RBM.MomentDuhamel.momentIneqQ_of_derivBound` is **existential**, so the
integrability has to hold for whatever witness the caller supplies.  It does, because a
derivative is unique: on the open window `φ'` is forced to be the generator expression of
`RBM.Gauss.hasDerivAt_integral_Psi₁`, which `RBM.Gauss.TestFunT₁`'s `bddT` and `bdd₂` bound
uniformly, and measurability is then `Mathlib.measurable_deriv`.

The statement below is T212's `RBM.Gauss.intervalIntegrable_phi'_gauss` with the *particular*
observable `RBM.Gauss.momentObsT` abstracted away: it applies verbatim to the `Q_t` route's
`RBM.Gauss.qMomentObsT`, whose `TestFunT₁` is T225's `RBM.Gauss.testFunT₁_qMomentObsT`.  (The
plain-route lemma should become a one-line specialisation of this one; see the report.) -/

section PhiPrime

variable {d : Dims} {N : ℕ}

theorem intervalIntegrable_phi'_of_testFunT₁ {s v : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v)
    {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hT₁ : TestFunT₁ d N (Set.Icc s v) Ψ)
    {φ φ' : ℝ → ℝ}
    (hΦφ : (fun r : ℝ => ∫ ω, Ψ r (Hflow d N r ω) ∂(P d)) = fun r : ℝ => ((φ r : ℝ) : ℂ))
    (hφ' : ∀ u ∈ Set.Ioo s v, HasDerivAt φ (φ' u) u) :
    IntervalIntegrable φ' volume s v := by
  classical
  obtain ⟨CT, hCT⟩ := hT₁.bddT
  obtain ⟨C₂, hC₂⟩ := hT₁.bdd₂
  set Cb : ℝ := CT + (1 / 2 : ℝ) * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
      * (C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖) with hCb
  have hkey : ∀ u ∈ Set.Ioo s v, |φ' u| ≤ Cb := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hs0 hu.1
    have hmem : Set.Icc s v ∈ nhds u := Icc_mem_nhds hu.1 hu.2
    have hmemI : u ∈ Set.Icc s v := ⟨hu.1.le, hu.2.le⟩
    have hD := hasDerivAt_integral_Psi₁ (matrixStein d) hT₁ hu0 hmem
    rw [hΦφ] at hD
    have hre : HasDerivAt (fun r : ℝ => (((φ r : ℝ) : ℂ)).re)
        (Complex.reCLM ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
          + (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
            ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d))) u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hD
    simp only [Complex.ofReal_re, Complex.reCLM_apply] at hre
    have heq : φ' u = ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
          ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d)).re :=
      (hφ' u hu).unique hre
    have hb1 : ‖∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d)‖ ≤ CT := by
      have h := norm_integral_le_of_norm_le_const (μ := P d) (C := CT)
        (Filter.Eventually.of_forall fun ω => hCT u hmemI (Hflow d N u ω))
      simpa using h
    have hb2 : ‖(1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
        ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d)‖
        ≤ (1 / 2 : ℝ) * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
          * (C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
      have h := norm_integral_le_of_norm_le_const (μ := P d)
        (C := C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖)
        (Filter.Eventually.of_forall fun ω =>
          norm_coordD2_le (fun M => hC₂ u hmemI M) (Hflow d N u ω) q)
      simpa using h
    rw [heq]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
  have hderiv : ∀ u ∈ Set.Ioo s v, deriv φ u = φ' u := fun u hu => (hφ' u hu).deriv
  have hae : deriv φ =ᵐ[volume.restrict (Set.Ioo s v)] φ' := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu using hderiv u hu
  have hmeas : AEStronglyMeasurable φ' (volume.restrict (Set.Ioo s v)) :=
    ((measurable_deriv φ).aestronglyMeasurable).congr hae
  have hintOo : IntegrableOn φ' (Set.Ioo s v) := by
    refine Integrable.mono' (integrable_const Cb) hmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs]
    exact hkey u hu
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hsv]
  exact hintOo.congr_set_ae Ioo_ae_eq_Ioc.symm

end PhiPrime

/-! ### Satisfiability

* `RBM.Gauss.sideConditionsQ_gauss_window_zero` is the **positive** witness: at the critical
  scaling — the **full open window** `s = 0`, `0 ≤ v < 1`, with `v` universally quantified and
  allowed to run up to `1`, and no constant that degenerates as it does (the T195 accident) —
  all the side conditions this ticket closes hold **simultaneously**, for an arbitrary Gaussian
  model, an arbitrary charge vector, an arbitrary loop argument and an arbitrary `p`, with **no
  free data**: the primitive's window bound is itself produced by
  `RBM.Gauss.exists_bdd_Kval_Kprim`.
* `RBM.Gauss.quadVar_qUkerObsT_le_at_zero` is the degenerate check the T164 rule asks for: at
  the sample point `ω = 0` (`H_u = 0`, `G = -z⁻¹`) the quadratic-variation bridge is asserted
  and the right-hand side is the pinned `(Q_u ⊗ Q_u)(E ⊗ E)`, not a free tensor. -/

section SatisfiabilityQ

variable {d : Dims}

/-- **Positive satisfiability witness: the side conditions this ticket closes hold together on
the full open window `[0, v]`, `v < 1`, with no free data.** -/
theorem sideConditionsQ_gauss_window_zero (E : ℝ) (N : ℕ) (hE : |E| < 2) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (p : ℕ) :
    (∃ C : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) v,
        (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
            ^ (2 * p) ∂(band d).P) ^ ((1 : ℝ) / p) ≤ C)
      ∧ ContinuousOn (fun u : ℝ =>
          ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (Qop (d.L N) ((u : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖|
              ^ (2 * p) ∂(band d).P) (Set.Icc 0 v)
      ∧ IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P (2 * p) (fun ω =>
          ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
              (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖)) volume 0 v
      ∧ IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P (2 * p) (fun ω =>
          ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
              * SumZeroDyn.varthetaDot (d.L N) u b) a‖)) volume 0 v
      ∧ IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P p (fun ω =>
          ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
              (Fin.append a a)‖)) volume 0 v := by
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    exists_bdd_Kval_Kprim (d := d) E N hE.le (le_refl (0 : ℝ)) hv1 (v := v) σ
  exact ⟨exists_bdd_psiQ_gauss E N hE le_rfl hv1 σ a ((v : ℝ) : ℂ) p hcK hKb,
    continuousOn_integral_psiQ_gauss E N hE le_rfl hv1 σ a ((v : ℝ) : ℂ) p hcK hKb,
    intervalIntegrable_momNorm_commS_gauss E N hE le_rfl hv0 hv1 σ a ((v : ℝ) : ℂ)
      (2 * p) hcK hKb,
    intervalIntegrable_momNorm_PsumVarthetaDot_gauss E N hE le_rfl hv0 hv1 σ a
      ((v : ℝ) : ℂ) (2 * p) hcK hKb,
    intervalIntegrable_momNorm_QQ_eeFun_gauss E N hE le_rfl hv0 hv1 σ a ((v : ℝ) : ℂ) p⟩

/-- **Degenerate check at `ω = 0`.**  The quadratic-variation bridge holds at `H = 0`, where
`G = -z^{-1}`, and its right-hand side is the pinned `(Q_u ⊗ Q_u)(E ⊗ E)_u`. -/
theorem quadVar_qUkerObsT_le_at_zero {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2))
    (K : ℝ → LoopArg (d.L N) (n + 2) → ℂ) :
    quadVar d N (qUkerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) K a u) 0
      ≤ ((n : ℝ) + 2)
          * ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
                (MomentDuhamel.eeFun (band d) E N u 0 σ)) (Fin.append a a)‖ :=
  EEUker.quadVar_qUkerObsT_le_norm_QQ_eeFun' (B := band d) hE hu0 hu1 hv0 hv1 σ
    Matrix.isHermitian_zero a K

end SatisfiabilityQ

end Gauss

end RBM



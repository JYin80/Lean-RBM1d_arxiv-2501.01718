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
conditions.  This file closes both.

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

end QBandForm

end EEUker

end RBM

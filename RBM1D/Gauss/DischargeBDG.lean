/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentGronwall
import RBM1D.Gauss.Hierarchy
import RBM1D.Gauss.Envelope
import RBM1D.Hierarchy.Kernel
import Mathlib.Algebra.Order.Chebyshev

/-!
# Definition 5.4 and (5.25)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: Definition 5.4 (`E ⊗ E`), the gluing identity (5.22), and the left-hand side
of the quadratic-variation computation (5.25).

This file builds on `RBM1D/Gauss/MomentGronwall.lean`, whose `RBM.Gauss.secondOrder_eq_quadVar`
identifies the second-order term of the generator identity with `∑_α |E^{(M)}(α)|²`.

## What is proved

**Definition 5.4 as a definition.**

* `RBM.Gauss.emart` is `E^{(M)}_{σ,a}(α) = (S_ij)^{1/2} ∂_{(H)_ij} L_{σ,a}` of §5.2, for the
  loop observable `RBM.Gauss.loopObs`, in the Wirtinger convention of
  `RBM1D/Gauss/MomentGronwall.lean` (it is literally
  `RBM.Gauss.EmartCoeff` at `F = loopObs`);
* `RBM.Gauss.emartEdge` is `E^{(M)}_{σ,a}(α,k)`, the term in which the derivative hits the
  `k`-th `G`-edge, written out through the cut block `RBM.Gauss.loopCut`;
* `RBM.Gauss.eeEdge`, `RBM.Gauss.eeTens` are `(E⊗E)^{(k)}` and `E⊗E` of (5.22).

**The bridge `LoopArg ↔ LoopIdx`** is
`RBM.Gauss.toIdx` together with `RBM.Gauss.emart_Uker` and `RBM.Gauss.quadVarPairs_Uker`: the
paper's step "since `U_{u,t,σ}` is a deterministic linear operator" is the linearity of the
Wirtinger derivative, `RBM.Gauss.EmartCoeff_sum`, and `RBM.Uker` is exactly such a finite
deterministic combination.

**(5.22)** is `RBM.Gauss.eeEdge_eq_sum_SB`, resting on the purely algebraic gluing identity
`RBM.Gauss.sum_Sblk_mul_conj`:
`∑_{ij} S_ij R_{ji} conj(R'_{ji}) = W ∑_{b,b'} S^{(B)}_{b b'} ⟨E_{b'} R E_b (R')ᴴ⟩`.
The factor `W` of (5.22) comes out of `S = S^{(B)}/W` and `E_a = W^{-1}P_a` and is not put in
by hand.

## Hypotheses (nothing here is an `axiom`)

* `hdiff` in `emart_Uker` — differentiability of the loop observable.  Discharged by
  `RBM.Gauss.differentiableAt_loopObs`, with no Hermitian requirement.

## The glued loop

* The glued loop of (5.23) is given as the explicit trace `RBM.Gauss.glueLoop`; that it equals
  `gloop` of a `LoopIdx` of length `2n+2` with the charges and labels displayed in (5.23) is
  proved in `RBM1D/Hierarchy/EEBridge.lean` (it needs `L_{σ̄,a'} = conj L_{σ,a'}` up to a
  cyclic reversal).
* The second factor of `E ⊗ E` is read as a complex conjugate rather than as the `σ̄`-loop;
  `RBM1D/Hierarchy/EEBridge.lean` justifies this reading.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.L2Operator

/-! ### The gluing identity behind Definition 5.4 -/

section Glue

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The glued loop of (5.23), written with the two cut resolvent blocks `R`, `R'`:
`⟨E_b · R · E_a · (R')ᴴ⟩`. -/
noncomputable def glueLoop (R R' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (a b : ZMod L) : ℂ :=
  Matrix.trace (Eblk L W b * R * Eblk L W a * R'ᴴ)

variable {L W}

/-- **The gluing identity (5.22).** -/
theorem sum_Sblk_mul_conj (R R' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) :
    ∑ i : ZMod L × Fin W, ∑ j : ZMod L × Fin W,
        (Sblk L W i j : ℂ) * (R j i * (starRingEnd ℂ) (R' j i))
      = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          SB L a b * glueLoop L W R R' a b := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  -- the entries of `E_b · R · E_a`
  have hX : ∀ (a b : ZMod L) (p r : ZMod L × Fin W),
      (Eblk L W b * R * Eblk L W a) p r
        = (if p.1 = b then (W : ℂ)⁻¹ else 0) * R p r * (if r.1 = a then (W : ℂ)⁻¹ else 0) := by
    intro a b p r
    rw [Eblk, Eblk, Matrix.mul_diagonal, Matrix.diagonal_mul]
  -- the glued loop as an explicit double sum
  have htr : ∀ a b : ZMod L, glueLoop L W R R' a b
      = ∑ p : ZMod L × Fin W, ∑ r : ZMod L × Fin W,
          ((if p.1 = b then (W : ℂ)⁻¹ else 0) * R p r * (if r.1 = a then (W : ℂ)⁻¹ else 0))
            * (starRingEnd ℂ) (R' p r) := by
    intro a b
    rw [glueLoop, Matrix.trace]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hX, Matrix.conjTranspose_apply, RCLike.star_def]
  -- a four-fold reordering of finite sums
  have hswap : ∀ f : ZMod L → ZMod L → (ZMod L × Fin W) → (ZMod L × Fin W) → ℂ,
      ∑ a, ∑ b, ∑ p, ∑ r, f a b p r = ∑ p, ∑ r, ∑ a, ∑ b, f a b p r := by
    intro f
    calc ∑ a, ∑ b, ∑ p, ∑ r, f a b p r
        = ∑ a, ∑ p, ∑ b, ∑ r, f a b p r :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p, ∑ a, ∑ b, ∑ r, f a b p r := Finset.sum_comm
      _ = ∑ p, ∑ a, ∑ r, ∑ b, f a b p r :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p, ∑ r, ∑ a, ∑ b, f a b p r :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hrhs : (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L, SB L a b * glueLoop L W R R' a b
      = ∑ p : ZMod L × Fin W, ∑ r : ZMod L × Fin W,
          ((W : ℂ)⁻¹ * SB L r.1 p.1) * (R p r * (starRingEnd ℂ) (R' p r)) := by
    have h1 : ∑ a : ZMod L, ∑ b : ZMod L, SB L a b * glueLoop L W R R' a b
        = ∑ a : ZMod L, ∑ b : ZMod L, ∑ p : ZMod L × Fin W, ∑ r : ZMod L × Fin W,
            SB L a b * (((if p.1 = b then (W : ℂ)⁻¹ else 0) * R p r
              * (if r.1 = a then (W : ℂ)⁻¹ else 0)) * (starRingEnd ℂ) (R' p r)) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [htr a b, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => Finset.mul_sum _ _ _
    rw [h1, hswap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hs : ∀ c : ℂ, ∑ a : ZMod L, ∑ b : ZMod L,
        SB L a b * (if p.1 = b then c else 0) * (if r.1 = a then c else 0)
          = SB L r.1 p.1 * c * c := by
      intro c
      have e1 : ∀ a : ZMod L, ∑ b : ZMod L,
          SB L a b * (if p.1 = b then c else 0) * (if r.1 = a then c else 0)
            = (if r.1 = a then SB L a p.1 * c * c else 0) := by
        intro a
        have hb : ∀ b : ZMod L,
            SB L a b * (if p.1 = b then c else 0) * (if r.1 = a then c else 0)
              = (if p.1 = b then SB L a b * c * (if r.1 = a then c else 0) else 0) := by
          intro b; split_ifs <;> ring
        rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
    have hinner : ∑ a : ZMod L, ∑ b : ZMod L,
        SB L a b * (((if p.1 = b then (W : ℂ)⁻¹ else 0) * R p r
          * (if r.1 = a then (W : ℂ)⁻¹ else 0)) * (starRingEnd ℂ) (R' p r))
        = (SB L r.1 p.1 * (W : ℂ)⁻¹ * (W : ℂ)⁻¹) * (R p r * (starRingEnd ℂ) (R' p r)) := by
      rw [← hs (W : ℂ)⁻¹, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hinner]
    field_simp
  rw [hrhs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [Sblk, SB_eq_ofReal]
  push_cast
  field_simp

end Glue

/-! ### `E^{(M)}` and Definition 5.4 -/

section Emart

variable (d : Dims) (N : ℕ)

/-- **`E^{(M)}_{σ,a}(α)` of §5.2** at `α = (i,j)`, for the loop observable of `RBM1D/Gauss/Hierarchy.lean`:
`(S_ij)^{1/2} ∂_{(H)_ij} L_{σ,a}`, with the Wirtinger convention of `RBM.Gauss.wirtFirst`. -/
noncomputable def emart (z : ℂ) (I : LoopIdx (ZMod (d.L N)))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) : ℂ :=
  EmartCoeff d N (loopObs d N z I) M i j

variable {d N}

end Emart

/-! ### The Schwarz split of (5.25) and `(E ⊗ E)^{(k)}` of (5.22) -/

section Split

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The loop product over an explicit list of `(charge, label)` pairs; `RBM.gloopProd` is the
case of the zipped lists of a `LoopIdx`. -/
noncomputable def prodList (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (l : List (Bool × ZMod L)) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  l.foldr (fun p X => Gsig M z p.1 * Eblk L W p.2 * X) 1

omit [NeZero W] in
theorem gloopProd_eq_prodList (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : gloopProd L W M z I = prodList L W M z (I.σ.zip I.a) := rfl

/-- **The cut block `R_k` of the `k`-th edge** (`k` counted from `0`):
`R_k = G(σ_k) E_{a_k} · ∏_{i > k} G(σ_i)E_{a_i} · ∏_{i < k} G(σ_i)E_{a_i} · G(σ_k)`.

It is the matrix through which the paper's `E^{(M)}(α,k)` is expressed:
`∂_{M_ij}(M - z)⁻¹ = -(M-z)⁻¹ e_{ij} (M-z)⁻¹` turns
`L_{σ,a}|_{G_k → ∂_{M_ij}G_k}` into `-(R_k)_{ji}` (cyclicity of the trace). -/
noncomputable def loopCut (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) (k : ℕ) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  Gsig M z ((I.σ.zip I.a).getD k (true, 0)).1
    * Eblk L W ((I.σ.zip I.a).getD k (true, 0)).2
    * prodList L W M z ((I.σ.zip I.a).drop (k + 1))
    * prodList L W M z ((I.σ.zip I.a).take k)
    * Gsig M z ((I.σ.zip I.a).getD k (true, 0)).1

end Split

section SplitEmart

variable (d : Dims) (N : ℕ)

/-- **`E^{(M)}_{σ,a}(α,k)` of §5.2**: `(S_ij)^{1/2} · L_{σ,a}|_{G_k → ∂_{(H)_ij}G_k}`, written
out through `RBM.Gauss.loopCut`. -/
noncomputable def emartEdge (z : ℂ) (I : LoopIdx (ZMod (d.L N)))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (k : ℕ) (i j : d.Idx N) : ℂ :=
  -(Real.sqrt (Sblk (d.L N) (d.W N) i j) : ℂ) * loopCut (d.L N) (d.W N) M z I k j i

/-- **`(E ⊗ E)^{(k)}` of Definition 5.4**: `∑_α E^{(M)}_{σ,a}(α,k) · E^{(M)}_{σ̄,a'}(α,k)`. -/
noncomputable def eeEdge (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) (k : ℕ) : ℂ :=
  ∑ i : d.Idx N, ∑ j : d.Idx N,
    emartEdge d N z I M k i j * (starRingEnd ℂ) (emartEdge d N z I' M k i j)

/-- **`(E ⊗ E)` of Definition 5.4**, `∑_{k} (E⊗E)^{(k)}` over the `n` edges of the loop. -/
noncomputable def eeTens (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) : ℂ :=
  ∑ k ∈ Finset.range I.length, eeEdge d N z M I I' k

variable {d N}

/-- **(5.22)**: `(E⊗E)^{(k)}_{σ,a,a'} = W ∑_{b,b'} S^{(B)}_{b b'} · ⟨glued loop⟩`, the glued loop
being the `(2n+2)`-loop of (5.23) — here in the form `⟨E_{b'} R_k E_b (R'_k)ᴴ⟩` in which the
two cut loops are joined through the two new labels `b`, `b'`. -/
theorem eeEdge_eq_sum_SB (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) (k : ℕ) :
    eeEdge d N z M I I' k
      = (d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N), SB (d.L N) a b
          * glueLoop (d.L N) (d.W N) (loopCut (d.L N) (d.W N) M z I k)
              (loopCut (d.L N) (d.W N) M z I' k) a b := by
  rw [← sum_Sblk_mul_conj (L := d.L N) (W := d.W N)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : ((Real.sqrt (Sblk (d.L N) (d.W N) i j) : ℂ))
      * ((Real.sqrt (Sblk (d.L N) (d.W N) i j) : ℂ)) = ((Sblk (d.L N) (d.W N) i j : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Sblk_nonneg i j)]
  rw [emartEdge, emartEdge]
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  rw [← hs]
  ring

end SplitEmart

/-! ### (5.25): the Schwarz step, and the linearity of `E^{(M)}` in the loop -/

section Schwarz

variable {d : Dims} {N : ℕ}

/-- **"Since `U` is a deterministic linear operator"** (the step of (5.25) that moves the
evolution kernel through `E^{(M)}`): the Wirtinger derivative, hence `E^{(M)}`, of a finite
deterministic linear combination of loop observables is that combination of the `E^{(M)}`'s.
`RBM.Uker` is exactly such a combination (`Uker_apply`). -/
theorem EmartCoeff_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hdiff : ∀ b ∈ s, DifferentiableAt ℝ (f b) M) (i j : d.Idx N) :
    EmartCoeff d N (fun M' => ∑ b ∈ s, c b * f b M') M i j
      = ∑ b ∈ s, c b * EmartCoeff d N (f b) M i j := by
  have hd1 : ∀ b ∈ s, DifferentiableAt ℝ (fun M' => c b * f b M') M :=
    fun b hb => (differentiableAt_const (c b)).mul (hdiff b hb)
  have hcoord : ∀ q : d.Idx N × d.Idx N × Bool,
      coordD1 d N (fun M' => ∑ b ∈ s, c b * f b M') M q
        = ∑ b ∈ s, c b * coordD1 d N (f b) M q := by
    intro q
    simp only [coordD1]
    rw [fderiv_fun_sum hd1]
    rw [Finset.sum_congr rfl fun b hb => fderiv_const_mul (hdiff b hb) (c b)]
    simp
  have hw : wirtFirst d N (fun M' => ∑ b ∈ s, c b * f b M') M i j
      = ∑ b ∈ s, c b * wirtFirst d N (f b) M i j := by
    unfold wirtFirst
    rcases eq_or_ne i j with rfl | hij
    · simp only [ite_eq_left]
      exact hcoord _
    · simp only [ite_eq_right hij]
      rw [hcoord, hcoord, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
  rw [EmartCoeff, hw, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [EmartCoeff]; ring

end Schwarz

/-! ### The representation bridge `LoopArg ↔ LoopIdx`, and `U` as a deterministic operator -/

section Bridge

variable {d : Dims} {N : ℕ}

/-- **The representation bridge**: a charge vector `σ : Fin n → Bool` together
with labels `a : LoopArg L n` (the `Fin n` representation used by `Uker`, `ThetaOp`, `Qop`)
gives the `LoopIdx` of `RBM1D/Loop/Index.lean` (the `List` representation used by `gloop`,
`primRhs`, `cutGlue`).  This is `RBM.LoopData.idx` under a name that says what it is. -/
abbrev toIdx {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) : LoopIdx (ZMod L) :=
  LoopData.idx (σ, a)

theorem toIdx_wf {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) : (toIdx σ a).WF :=
  LoopData.idx_wf _

@[simp] theorem toIdx_length {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) :
    (toIdx σ a).length = n := LoopData.idx_length _

/-- **"Since `U_{u,t,σ}` is a deterministic linear operator"** — the step of (5.25) that pulls
the evolution kernel of (5.17) out of `E^{(M)}`:

`E^{(M)}` of the loop tensor `U_{s,t,σ} ∘ L_{σ,·}` at the label `a` is `U_{s,t,σ}` applied to
the tensor `b ↦ E^{(M)}_{σ,b}(α)`.  This is the bridge between the matrix-function side
(`EmartCoeff`, `quadVar`) and the `LoopArg` side (`Uker`). -/
theorem emart_Uker {n : ℕ} (σ : Fin n → Bool) (ξ : Fin n → ℂ) (s t z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (aa : LoopArg (d.L N) n)
    (hdiff : ∀ b : LoopArg (d.L N) n,
      DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M) (i j : d.Idx N) :
    EmartCoeff d N
        (fun M' => Uker (d.L N) ξ s t (fun b => loopObs d N z (toIdx σ b) M') aa) M i j
      = Uker (d.L N) ξ s t (fun b => emart d N z (toIdx σ b) M i j) aa := by
  have hfun : (fun M' => Uker (d.L N) ξ s t (fun b => loopObs d N z (toIdx σ b) M') aa)
      = fun M' => ∑ b : LoopArg (d.L N) n,
          (∏ i, edgeKer (d.L N) (ξ i) s t (aa i) (b i)) * loopObs d N z (toIdx σ b) M' := rfl
  rw [hfun, EmartCoeff_sum _ _ _ _ (fun b _ => hdiff b), Uker_apply]
  rfl

/-- **The left-hand side of (5.25)**: the quadratic variation of the `U`-conjugated loop is
`∑_α |(U_{u,t,σ} ∘ E^{(M)}_{u,σ}(α))_a|²`. -/
theorem quadVarPairs_Uker {n : ℕ} (σ : Fin n → Bool) (ξ : Fin n → ℂ) (s t z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (aa : LoopArg (d.L N) n)
    (hdiff : ∀ b : LoopArg (d.L N) n,
      DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M) :
    quadVarPairs d N
        (fun M' => Uker (d.L N) ξ s t (fun b => loopObs d N z (toIdx σ b) M') aa) M
      = ∑ i : d.Idx N, ∑ j : d.Idx N,
          ‖Uker (d.L N) ξ s t (fun b => emart d N z (toIdx σ b) M i j) aa‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [emart_Uker σ ξ s t z M aa hdiff i j]

end Bridge

/-! ### The moment-route replacement for the BDG inequality (Lemma 5.5) -/

section MomentBDG

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {p : ℕ}

end MomentBDG

/-! ### `≺` in, `≺` out: the pipeline of the moment route -/

section Pipeline

variable {d : Dims} {U : ℕ → Type*}

end Pipeline

end RBM.Gauss

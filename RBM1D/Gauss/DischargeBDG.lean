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
# Definition 5.4, (5.25), and the moment route in place of BDG (T74)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, pp. 54–55: Definition 5.4 (`E ⊗ E`), the quadratic-variation computation
(5.25), and Lemma 5.5 (the martingale term).

This file sits on top of T72 (`RBM1D/Gauss/MomentGronwall.lean`), whose fulcrum
`RBM.Gauss.secondOrder_eq_quadVar` identifies the second-order term of the generator identity
with `∑_α |E^{(M)}(α)|²`.  T72 reported two gaps between that fulcrum and the repository's BDG
interface; both are addressed here, and the third — whether `RBM.SumZeroDyn.Hierarchy.bdg` can
be turned from a hypothesis into a theorem *at its present signature* — is answered in the
negative, with reasons, below.

## What is proved

**Definition 5.4 acquires a definition.**  Nothing in the repository defined
`RBM.SumZeroDyn.Hierarchy.EE`; it was an uninterpreted structure field.  Here

* `RBM.Gauss.emart` is `E^{(M)}_{σ,a}(α) = (S_ij)^{1/2} ∂_{(H)_ij} L_{σ,a}` of §5.2, for the
  loop observable `RBM.Gauss.loopObs` of T76, in T72's Wirtinger convention (it is literally
  `RBM.Gauss.EmartCoeff` at `F = loopObs`);
* `RBM.Gauss.eeRaw` is `∑_α E^{(M)}_{σ,a}(α) · E^{(M)}_{σ̄,a'}(α)`, `E ⊗ E` *before* the
  Schwarz split;
* `RBM.Gauss.emartEdge` is `E^{(M)}_{σ,a}(α,k)`, the term in which the derivative hits the
  `k`-th `G`-edge, written out through the cut block `RBM.Gauss.loopCut`;
* `RBM.Gauss.eeEdge`, `RBM.Gauss.eeTens` are `(E⊗E)^{(k)}` and `E⊗E` of (5.22).

**The bridge to T72's fulcrum** (T72's gap 1) is `RBM.Gauss.eeRaw_self_eq_quadVar`: the
diagonal `(E⊗E)_{σ,a,a}` *is* `RBM.Gauss.quadVar`, the coefficient of `|L|^{2p-2}` in
`d/du E|L(H_u)|^{2p}`.  This is the equation that could not be stated before.

**The bridge `LoopArg ↔ LoopIdx`** (T72's gap 2, the T58 note in `docs/STATUS.md`) is
`RBM.Gauss.toIdx` together with `RBM.Gauss.emart_Uker` and `RBM.Gauss.quadVarPairs_Uker`: the
paper's step "since `U_{u,t,σ}` is a deterministic linear operator" is the linearity of the
Wirtinger derivative, `RBM.Gauss.EmartCoeff_sum`, and `RBM.Uker` is exactly such a finite
deterministic combination.

**(5.22)** is `RBM.Gauss.eeEdge_eq_sum_SB`, resting on the purely algebraic gluing identity
`RBM.Gauss.sum_Sblk_mul_conj`:
`∑_{ij} S_ij R_{ji} conj(R'_{ji}) = W ∑_{b,b'} S^{(B)}_{b b'} ⟨E_{b'} R E_b (R')ᴴ⟩`.
The factor `W` of (5.22) comes out of `S = S^{(B)}/W` and `E_a = W^{-1}P_a` and is not put in
by hand.

**(5.25)** is `RBM.Gauss.quadVarPairs_le_of_split`: the Schwarz step
`∑_α |∑_k E(α,k)|² ≤ n ∑_k ∑_α |E(α,k)|²`.

**The moment route in place of BDG.**  `RBM.Gauss.momentIntegral_le_of_quadVar` and
`RBM.Gauss.momentIntegral_le_exp`: for an observable `F` of the matrix with vanishing generator
drift (`𝓛F = 0`, the moment route's stand-in for "this term is a martingale"),

  `E|F(H_v)|^{2p} ≤ (E|F(H_a)|^{2p} + sup_u E[(∑_α |E^{(M)}(α)|²)^p]) · e^{p(2p-1)(v-a)}`,

which is (5.24) with `C_{n,p}` replaced by `e^{p(2p-1)(v-a)}`.  `RBM.Gauss.momentDom_of_quadVar`
and `RBM.Gauss.stochDom_of_quadVar` package this as the intended pipeline
`≺ in → moments (T77) → Grönwall (T72) → ≺ out (T73)`: a `≺`-bound on the quadratic variation
`((U⊗U)∘(E⊗E))_{a,a}` in, a `≺`-bound on the observable out.

## Why `RBM.SumZeroDyn.Hierarchy.bdg` is *not* a theorem here

`bdg` / `bdgQ` are **fields of a structure whose data fields `EE`, `mart`, `martQ`, `F` are
unconstrained**.  A theorem "at the existing signature" must therefore first *define* `mart`
and `EE`.  Three obstructions, in increasing order of seriousness:

1. *`duhamel` is satisfiable by fiat, and that makes `bdg` the whole content.*  Defining
   `mart := (L-K)_v − U_{s,v}∘(L-K)_s − ∫_s^v U_{u,v}∘F_u du` makes `duhamel` true by
   construction for **any** `F`.  Everything that BDG actually asserts then sits in `bdg`
   alone.  (Choosing `F` so that this residual vanishes identically would make `bdg` vacuous
   while falsifying `RBM.SumZeroDyn.Lemma510`; that is a fabrication, not a proof, and is not
   done here.)

2. *The residual is not a function of `H_v`.*  `∫_s^v U_{u,v}∘F_u(H_u) du` depends on the whole
   path.  With `H_u = √u · X` one may substitute `X = H_v/√v`, but the resulting `Ψ_v` then
   depends on `v` through two arguments, and `d/dv E[Ψ_v(H_v)]` needs a partial derivative in
   `v` that T71's generator identity does not supply.  This is the same wall T76 hit for the
   moving spectral parameter `z_u`, and Mathlib has no directly usable "continuous partials ⟹
   differentiable" lemma for it.

3. *Nothing makes the residual driftless.*  `RBM.Gauss.momentIntegral_le_of_quadVar` needs
   `𝓛F = 0`; for a genuine Itô martingale this is automatic, and it is precisely what
   `H_u = √u · X` does not provide — the flow is not a martingale and has no filtration
   (paper-delta #49).  The hypothesis `𝓛F = 0` is therefore the honest moment-route
   *replacement* for "`M` is a martingale", not a consequence of the setup.

Conclusion: `bdg` and `bdgQ` **stay hypotheses**.  What this file delivers instead is the
statement they are used for, in the moment route's own vocabulary and with the same input and
the same output (`≺` in, `≺` out): `RBM.Gauss.stochDom_of_quadVar`.  Consumers in `Hierarchy/`
are untouched, exactly as the "keep the paper's `≺` interface" rule demands.

## Hypotheses (nothing here is an `axiom`)

* `RBM.Gauss.MatrixStein d` — Cowork's T70, still owed, carried through unchanged.
* `RBM.Gauss.BddC2 F` — `C²` with globally bounded value and first two derivatives.  T72
  discharges it for resolvent observables (`bddC2_greenObs`); for a general loop observable it
  is still open (T76: the `List.foldr` Leibniz rule).
* `hdrift : 𝓛F = 0` — see obstruction 3 above.
* `hsplit` in `quadVarPairs_le_of_split` — the chain rule `E(α) = ∑_k E(α,k)` of §5.2, which
  needs the same Leibniz rule and is not proved here.
* `hdiff` in `emart_Uker` — differentiability of the loop observable, likewise.

## What is not done

* `E^{(M)}(α,k)` is *defined* through `RBM.Gauss.loopCut`; that this definition agrees with
  `∂_{(H)_ij}` acting on the `k`-th edge (the chain rule, and hence `∑_k E(α,k) = E(α)`) is not
  proved.
* The glued loop of (5.23) is given as the explicit trace `RBM.Gauss.glueLoop`; that it equals
  `gloop` of a `LoopIdx` of length `2n+2` with the charges and labels displayed in (5.23) is
  not proved (it needs `L_{σ̄,a'} = conj L_{σ,a'}` up to a cyclic reversal).
* The second factor of `E ⊗ E` is read as a complex conjugate rather than as the `σ̄`-loop;
  see `docs/paper-deltas.md`.
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

/-- **`E ⊗ E` before the Schwarz split of (5.25)**: `∑_α E^{(M)}_{σ,a}(α) · E^{(M)}_{σ̄,a'}(α)`,
the second factor read (as everywhere below) as the complex conjugate of the `σ`-factor. -/
noncomputable def eeRaw (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) : ℂ :=
  ∑ i : d.Idx N, ∑ j : d.Idx N,
    emart d N z I M i j * (starRingEnd ℂ) (emart d N z I' M i j)

variable {d N}

/-- **The diagonal of `E ⊗ E` is the quadratic-variation integrand of (5.25).** -/
theorem eeRaw_self (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (I : LoopIdx (ZMod (d.L N))) :
    eeRaw d N z M I I = ((quadVarPairs d N (loopObs d N z I) M : ℝ) : ℂ) := by
  rw [eeRaw, quadVarPairs, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => mul_conj_eq _

/-- **The diagonal of `E ⊗ E` is the second-order term of the generator identity.**

This is T72's fulcrum `RBM.Gauss.secondOrder_eq_quadVar` read through Definition 5.4: the
coefficient of `|L|^{2p-2}` in `d/du E|L(H_u)|^{2p}` is `(E⊗E)_{u,σ,a,a}`.  It is the
identification that `RBM.SumZeroDyn.Hierarchy.EE` was missing. -/
theorem eeRaw_self_eq_quadVar (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I : LoopIdx (ZMod (d.L N))) :
    eeRaw d N z M I I = ((quadVar d N (loopObs d N z I) M : ℝ) : ℂ) := by
  rw [eeRaw_self, secondOrder_eq_quadVar]

theorem eeRaw_self_nonneg (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I : LoopIdx (ZMod (d.L N))) : 0 ≤ (eeRaw d N z M I I).re := by
  rw [eeRaw_self_eq_quadVar, Complex.ofReal_re]
  exact quadVar_nonneg _ _

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

/-- The diagonal of `(E⊗E)^{(k)}` is `∑_α |E^{(M)}(α,k)|²`, a nonnegative real. -/
theorem eeEdge_self (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (I : LoopIdx (ZMod (d.L N)))
    (k : ℕ) :
    eeEdge d N z M I I k
      = ((∑ i : d.Idx N, ∑ j : d.Idx N, ‖emartEdge d N z I M k i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [eeEdge, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => mul_conj_eq _

end SplitEmart

/-! ### (5.25): the Schwarz step, and the linearity of `E^{(M)}` in the loop -/

section Schwarz

variable {d : Dims} {N : ℕ}

/-- **(5.25)**: after the Schwarz inequality that expands the square of the `n`-term chain rule,
the quadratic-variation integrand `∑_α |E^{(M)}(α)|²` is bounded by `n ∑_k ∑_α |E^{(M)}(α,k)|²`,
i.e. by `n · (E⊗E)^{(·)}` summed over the edges.

The splitting hypothesis `hsplit` is the chain rule
`E^{(M)}(α) = ∑_{k} E^{(M)}(α,k)` of §5.2, which this file does not prove (it needs the Leibniz
rule for the `List.foldr` product of resolvents; see the module docstring). -/
theorem quadVarPairs_le_of_split {n : ℕ} (z : ℂ) (I : LoopIdx (ZMod (d.L N)))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hsplit : ∀ i j, emart d N z I M i j
      = ∑ k ∈ Finset.range n, emartEdge d N z I M k i j) :
    quadVarPairs d N (loopObs d N z I) M
      ≤ (n : ℝ) * ∑ k ∈ Finset.range n, ∑ i : d.Idx N, ∑ j : d.Idx N,
          ‖emartEdge d N z I M k i j‖ ^ 2 := by
  have key : ∀ i j : d.Idx N, ‖emart d N z I M i j‖ ^ 2
      ≤ (n : ℝ) * ∑ k ∈ Finset.range n, ‖emartEdge d N z I M k i j‖ ^ 2 := by
    intro i j
    have h1 : ‖emart d N z I M i j‖
        ≤ ∑ k ∈ Finset.range n, ‖emartEdge d N z I M k i j‖ := by
      rw [hsplit i j]; exact norm_sum_le _ _
    have h2 : (∑ k ∈ Finset.range n, ‖emartEdge d N z I M k i j‖) ^ 2
        ≤ ((Finset.range n).card : ℝ) * ∑ k ∈ Finset.range n,
            ‖emartEdge d N z I M k i j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    rw [Finset.card_range] at h2
    refine le_trans ?_ h2
    gcongr
  have hsum : ∑ i : d.Idx N, ∑ j : d.Idx N,
        ((n : ℝ) * ∑ k ∈ Finset.range n, ‖emartEdge d N z I M k i j‖ ^ 2)
      = (n : ℝ) * ∑ k ∈ Finset.range n, ∑ i : d.Idx N, ∑ j : d.Idx N,
          ‖emartEdge d N z I M k i j‖ ^ 2 := by
    have e1 : ∀ i : d.Idx N, ∑ j : d.Idx N,
        ((n : ℝ) * ∑ k ∈ Finset.range n, ‖emartEdge d N z I M k i j‖ ^ 2)
        = (n : ℝ) * ∑ j : d.Idx N, ∑ k ∈ Finset.range n,
            ‖emartEdge d N z I M k i j‖ ^ 2 := fun i => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl fun i _ => e1 i, ← Finset.mul_sum]
    congr 1
    calc ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ k ∈ Finset.range n,
            ‖emartEdge d N z I M k i j‖ ^ 2
        = ∑ i : d.Idx N, ∑ k ∈ Finset.range n, ∑ j : d.Idx N,
            ‖emartEdge d N z I M k i j‖ ^ 2 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k ∈ Finset.range n, ∑ i : d.Idx N, ∑ j : d.Idx N,
            ‖emartEdge d N z I M k i j‖ ^ 2 := Finset.sum_comm
  calc quadVarPairs d N (loopObs d N z I) M
      = ∑ i : d.Idx N, ∑ j : d.Idx N, ‖emart d N z I M i j‖ ^ 2 := rfl
    _ ≤ ∑ i : d.Idx N, ∑ j : d.Idx N,
          ((n : ℝ) * ∑ k ∈ Finset.range n, ‖emartEdge d N z I M k i j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = _ := hsum

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

/-- **The representation bridge of the T58 note**: a charge vector `σ : Fin n → Bool` together
with labels `a : LoopArg L n` (the `Fin n` representation used by `Uker`, `ThetaOp`, `Qop`)
gives the `LoopIdx` of `RBM1D/Loop/Index.lean` (the `List` representation used by `gloop`,
`primRhs`, `cutGlue`).  This is `RBM.LoopData.idx` under a name that says what it is. -/
abbrev toIdx {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) : LoopIdx (ZMod L) :=
  LoopData.idx (σ, a)

theorem toIdx_wf {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) : (toIdx σ a).WF :=
  LoopData.idx_wf _

@[simp] theorem toIdx_length {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) :
    (toIdx σ a).length = n := LoopData.idx_length _

@[simp] theorem toIdx_get {L n : ℕ} (σ : Fin n → Bool) (a : LoopArg L n) (i : Fin n) :
    (toIdx σ a).a.get (Fin.cast (by simp [LoopData.idx]) i) = a i := by
  simp [LoopData.idx]

/-- **"Since `U_{u,t,σ}` is a deterministic linear operator"** — the step of (5.25) that pulls
the evolution kernel of (5.17) out of `E^{(M)}`:

`E^{(M)}` of the loop tensor `U_{s,t,σ} ∘ L_{σ,·}` at the label `a` is `U_{s,t,σ}` applied to
the tensor `b ↦ E^{(M)}_{σ,b}(α)`.  This is the bridge between the matrix-function side
(T72: `EmartCoeff`, `quadVar`) and the `LoopArg` side (`Uker`, `RBM.SumZeroDyn.Hierarchy.EE`). -/
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

/-- The elementary inequality that replaces Young's: `x^{p-1} y ≤ x^p + y^p`. -/
theorem pow_pred_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {p : ℕ} (hp : 1 ≤ p) :
    x ^ (p - 1) * y ≤ x ^ p + y ^ p := by
  rcases le_total y x with hyx | hxy
  · have h1 : x ^ (p - 1) * y ≤ x ^ (p - 1) * x :=
      mul_le_mul_of_nonneg_left hyx (pow_nonneg hx _)
    have h2 : x ^ (p - 1) * x = x ^ p := by
      rw [← pow_succ]; congr 1; omega
    calc x ^ (p - 1) * y ≤ x ^ (p - 1) * x := h1
      _ = x ^ p := h2
      _ ≤ x ^ p + y ^ p := le_add_of_nonneg_right (pow_nonneg hy _)
  · have h1 : x ^ (p - 1) * y ≤ y ^ (p - 1) * y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy _) hy
    have h2 : y ^ (p - 1) * y = y ^ p := by
      rw [← pow_succ]; congr 1; omega
    calc x ^ (p - 1) * y ≤ y ^ (p - 1) * y := h1
      _ = y ^ p := h2
      _ ≤ x ^ p + y ^ p := le_add_of_nonneg_left (pow_nonneg hx _)

/-- `RBM.Gauss.BddC2` for a matrix observable is `RBM.Gauss.TestFun` for it. -/
theorem TestFun.of_bddC2' (h : BddC2 F) : TestFun d N F :=
  ⟨h.contDiff, h.bdd₀, h.bdd₁, h.bdd₂⟩

theorem continuous_quadVar_Hflow (h : BddC2 F) (u : ℝ) :
    Continuous fun ω : Ω d => quadVar d N F (Hflow d N u ω) := by
  refine continuous_finsetSum _ fun q _ => ?_
  exact continuous_const.mul
    (((continuous_coordD1 (TestFun.of_bddC2' h) u q).norm).pow 2)

/-- The quadratic variation is globally bounded — an instance of the "the envelope is free"
principle of T77: it is a finite sum of squares of first derivatives, all globally bounded. -/
theorem exists_quadVar_bound (h : BddC2 F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M, quadVar d N F M ≤ C := by
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  have hC₁0 : (0 : ℝ) ≤ C₁ := le_trans (norm_nonneg _) (hC₁ 0)
  refine ⟨∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
      * (C₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖) ^ 2, ?_, fun M => ?_⟩
  · exact Finset.sum_nonneg fun q _ => by positivity
  · refine Finset.sum_le_sum fun q _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_coordD1_le hC₁ M q) 2

theorem integrable_quadVar_pow (h : BddC2 F) (u : ℝ) (m : ℕ) :
    Integrable (fun ω : Ω d => quadVar d N F (Hflow d N u ω) ^ m) (P d) := by
  obtain ⟨C, hC0, hC⟩ := exists_quadVar_bound h
  refine integrable_of_continuous_of_bound
    ((continuous_quadVar_Hflow h u).pow m) (C := C ^ m) fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (quadVar_nonneg _ _) m)]
  exact pow_le_pow_left₀ (quadVar_nonneg _ _) (hC _) m

theorem integrable_norm_pow_Hflow (h : BddC2 F) (u : ℝ) (m : ℕ) :
    Integrable (fun ω : Ω d => ‖F (Hflow d N u ω)‖ ^ m) (P d) := by
  obtain ⟨C, hC⟩ := h.bdd₀
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine integrable_of_continuous_of_bound
    (((h.contDiff.continuous.comp (continuous_Hflow d N u)).norm).pow m)
    (C := C ^ m) fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) m)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC _) m

/-- **The driftless Grönwall input.**  For an observable with vanishing generator drift
(`𝓛F = 0` — the moment-route stand-in for "the term is a martingale"), the generator applied to
`|F|^{2p}` is bounded by `p(2p-1)` times `|F|^{2p}` plus the `p`-th power of the quadratic
variation of (5.25). -/
theorem genMomentPt_le_driftless (hF : ContDiff ℝ 2 F) (hp : 1 ≤ p)
    (hdrift : ∀ M, genD d N F M = 0) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genMomentPt d N F p M
      ≤ ((p : ℝ) * (2 * p - 1)) * (‖F M‖ ^ (2 * p) + quadVarPairs d N F M ^ p) := by
  have hK : (0 : ℝ) ≤ (p : ℝ) * (2 * p - 1) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  have hx : ‖F M‖ ^ (2 * p - 2) = (‖F M‖ ^ 2) ^ (p - 1) := by
    rw [← pow_mul]; congr 1; omega
  have hxp : (‖F M‖ ^ 2) ^ p = ‖F M‖ ^ (2 * p) := (pow_mul _ 2 p).symm
  have hyoung : ‖F M‖ ^ (2 * p - 2) * quadVar d N F M
      ≤ ‖F M‖ ^ (2 * p) + quadVar d N F M ^ p := by
    rw [hx, ← hxp]
    exact pow_pred_mul_le (by positivity) (quadVar_nonneg _ _) hp
  have hbase := genMomentPt_le hF hp M
  rw [hdrift M, norm_zero, mul_zero, zero_add] at hbase
  refine hbase.trans ?_
  rw [secondOrder_eq_quadVar F M] at hyoung ⊢
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hyoung hK

/-- **The moment-route replacement for Lemma 5.5.**

`E|F(H_v)|^{2p} ≤ gronwallBound` with the quadratic variation of (5.25) as the inhomogeneous
term.  The hypothesis `hQ` is exactly the *input* of the paper's BDG step — a bound on
`∫ ((U⊗U)∘(E⊗E))_{a,a}` — and the conclusion is its *output*, in moment form.  No martingale,
no stochastic integral: `RBM.Gauss.secondOrder_eq_quadVar` says the generator's second-order
term is the same quadratic variation that BDG uses. -/
theorem momentIntegral_le_of_quadVar (hst : MatrixStein d) (h : BddC2 F) (hp : 1 ≤ p)
    (hdrift : ∀ M, genD d N F M = 0) {a b δ Q : ℝ} (ha : 0 < a)
    (hδ : momentIntegral d N F p a ≤ δ)
    (hQ : ∀ u ∈ Set.Ico a b,
      (∫ ω, quadVarPairs d N F (Hflow d N u ω) ^ p ∂(P d)) ≤ Q) :
    ∀ v ∈ Set.Icc a b, momentIntegral d N F p v
      ≤ gronwallBound δ ((p : ℝ) * (2 * p - 1)) ((p : ℝ) * (2 * p - 1) * Q) (v - a) := by
  have hK : (0 : ℝ) ≤ (p : ℝ) * (2 * p - 1) := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  refine momentIntegral_le_gronwallBound hst h.contDiff (TestFun.of_bddC2 h p) ha hδ ?_
  intro u hu
  have hqv : ∀ ω : Ω d, quadVarPairs d N F (Hflow d N u ω)
      = quadVar d N F (Hflow d N u ω) := fun ω => (secondOrder_eq_quadVar F _).symm
  have hint1 : Integrable (fun ω : Ω d => ‖F (Hflow d N u ω)‖ ^ (2 * p)) (P d) :=
    integrable_norm_pow_Hflow h u (2 * p)
  have hint2 : Integrable
      (fun ω : Ω d => quadVarPairs d N F (Hflow d N u ω) ^ p) (P d) := by
    simpa only [hqv] using integrable_quadVar_pow (F := F) h u p
  have hintG : Integrable (fun ω : Ω d => ((p : ℝ) * (2 * p - 1))
      * (‖F (Hflow d N u ω)‖ ^ (2 * p) + quadVarPairs d N F (Hflow d N u ω) ^ p)) (P d) :=
    (hint1.add hint2).const_mul _
  have hmono : (∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d))
      ≤ ∫ ω, ((p : ℝ) * (2 * p - 1))
          * (‖F (Hflow d N u ω)‖ ^ (2 * p)
            + quadVarPairs d N F (Hflow d N u ω) ^ p) ∂(P d) :=
    integral_mono (integrable_genMomentPt (TestFun.of_bddC2 h p) u) hintG
      fun ω => genMomentPt_le_driftless h.contDiff hp hdrift _
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add hint1 hint2]
  have : (∫ ω, quadVarPairs d N F (Hflow d N u ω) ^ p ∂(P d)) ≤ Q := hQ u hu
  have hmi : momentIntegral d N F p u = ∫ ω, ‖F (Hflow d N u ω)‖ ^ (2 * p) ∂(P d) := rfl
  rw [hmi, mul_add]
  have hstep := mul_le_mul_of_nonneg_left this hK
  linarith

/-- **The same bound in closed form**: `E|F(H_v)|^{2p} ≤ (δ + Q)·e^{p(2p-1)(v-a)}`.

Read against the paper: `δ` is the initial `2p`-th moment, `Q` the supremum over `u` of the
`p`-th moment of the quadratic variation `((U⊗U)∘(E⊗E))_{a,a}`, so the right side is the
`(Γ ∫ w)^p` of (5.24) up to the `e^{K(v-a)}` that the moment route pays instead of BDG's
constant `C_{n,p}`. -/
theorem momentIntegral_le_exp (hst : MatrixStein d) (h : BddC2 F) (hp : 1 ≤ p)
    (hdrift : ∀ M, genD d N F M = 0) {a b δ Q : ℝ} (ha : 0 < a) (hQ0 : 0 ≤ Q)
    (hδ : momentIntegral d N F p a ≤ δ)
    (hQ : ∀ u ∈ Set.Ico a b,
      (∫ ω, quadVarPairs d N F (Hflow d N u ω) ^ p ∂(P d)) ≤ Q)
    {v : ℝ} (hv : v ∈ Set.Icc a b) :
    momentIntegral d N F p v ≤ (δ + Q) * Real.exp ((p : ℝ) * (2 * p - 1) * (v - a)) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hKpos : (0 : ℝ) < (p : ℝ) * (2 * p - 1) := by nlinarith
  have hmain := momentIntegral_le_of_quadVar hst h hp hdrift ha hδ hQ v hv
  refine hmain.trans ?_
  rw [gronwallBound, ite_eq_right hKpos.ne']
  have hdiv : (p : ℝ) * (2 * p - 1) * Q / ((p : ℝ) * (2 * p - 1)) = Q := by
    rw [mul_comm ((p : ℝ) * (2 * p - 1)) Q, mul_div_assoc, div_self hKpos.ne', mul_one]
  rw [hdiv]
  nlinarith [hQ0, Real.exp_pos ((p : ℝ) * (2 * p - 1) * (v - a))]

end MomentBDG

/-! ### `≺` in, `≺` out: the pipeline of the moment route -/

section Pipeline

variable {d : Dims} {U : ℕ → Type*}

/-- **The moment-route pipeline in moment form.**

Input: the initial `2p`-th moment and the `p`-th moment of the quadratic variation of (5.25)
are `≼ N^{εp} Φ^{2p}` (this is what T77's `momentDom_of_stochDom` produces from a `≺` input).
Output: `MomentDom`, i.e. the same bound for the observable itself — which T73's
`stochDom_of_momentDom` turns back into `≺ Φ`.

This is the moment-route substitute for the BDG step of Lemma 5.5: the conclusion has the
shape of (5.24), with `Φ = (Γ ∫ w)^{1/2}`. -/
theorem momentDom_of_quadVar (hst : MatrixStein d)
    (F : ∀ N, U N → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (tm : ∀ N, U N → ℝ) (a : ℕ → ℝ) (Φ : ∀ N, U N → ℝ) (T : ℝ)
    (hbdd : ∀ N q, BddC2 (F N q))
    (hdrift : ∀ N q M, genD d N (F N q) M = 0)
    (ha : ∀ N, 0 < a N) (htm : ∀ N q, a N ≤ tm N q) (hT : ∀ N q, tm N q - a N ≤ T)
    (hinit : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q : U N,
      momentIntegral d N (F N q) p (a N) ≤ C * ((N : ℝ) ^ (ε * p) * Φ N q ^ (2 * p)))
    (hqv : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q : U N,
      ∀ u ∈ Set.Ico (a N) (tm N q),
        (∫ ω, quadVarPairs d N (F N q) (Hflow d N u ω) ^ p ∂(P d))
          ≤ C * ((N : ℝ) ^ (ε * p) * Φ N q ^ (2 * p))) :
    MomentDom (P d) (fun N (q : U N) ω => ‖F N q (Hflow d N (tm N q) ω)‖) Φ := by
  intro ε hε p
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨1, one_pos, Eventually.of_forall fun N q => ?_⟩
    simp [Real.rpow_zero]
  · obtain ⟨C₁, hC₁, hN₁⟩ := hinit ε hε p
    obtain ⟨C₂, hC₂, hN₂⟩ := hqv ε hε p
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hK : (0 : ℝ) ≤ (p : ℝ) * (2 * p - 1) := by nlinarith
    refine ⟨(C₁ + C₂) * Real.exp ((p : ℝ) * (2 * p - 1) * T), by positivity, ?_⟩
    filter_upwards [hN₁, hN₂] with N h1 h2 q
    set Φ2 : ℝ := (N : ℝ) ^ (ε * p) * Φ N q ^ (2 * p) with hΦ2
    have hΦ2nn : 0 ≤ Φ2 := by
      refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_
      rw [show 2 * p = 2 * p from rfl, pow_mul]
      positivity
    have hQ0 : 0 ≤ C₂ * Φ2 := mul_nonneg hC₂.le hΦ2nn
    have hbound := momentIntegral_le_exp hst (hbdd N q) hp (hdrift N q) (ha N) hQ0
      (h1 q) (fun u hu => h2 q u hu) (v := tm N q) ⟨htm N q, le_rfl⟩
    have hexp : Real.exp ((p : ℝ) * (2 * p - 1) * (tm N q - a N))
        ≤ Real.exp ((p : ℝ) * (2 * p - 1) * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hT N q) hK)
    have hrw : (∫ ω, |‖F N q (Hflow d N (tm N q) ω)‖| ^ (2 * p) ∂(P d))
        = momentIntegral d N (F N q) p (tm N q) := by
      simp only [momentIntegral, abs_norm]
    rw [hrw]
    refine hbound.trans ?_
    have hsum : (0 : ℝ) ≤ C₁ * Φ2 + C₂ * Φ2 :=
      add_nonneg (mul_nonneg hC₁.le hΦ2nn) hQ0
    calc (C₁ * Φ2 + C₂ * Φ2) * Real.exp ((p : ℝ) * (2 * p - 1) * (tm N q - a N))
        ≤ (C₁ * Φ2 + C₂ * Φ2) * Real.exp ((p : ℝ) * (2 * p - 1) * T) :=
          mul_le_mul_of_nonneg_left hexp hsum
      _ = (C₁ + C₂) * Real.exp ((p : ℝ) * (2 * p - 1) * T) * Φ2 := by ring

/-- **`≺` in, `≺` out.**  The same statement with the conclusion in the vocabulary of
Definition 2.1 (i): `‖F(H_{tm})‖ ≺ Φ`.  Composition of `RBM.Gauss.momentDom_of_quadVar` with
T73's `RBM.Gauss.stochDom_of_momentDom`. -/
theorem stochDom_of_quadVar [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (hst : MatrixStein d)
    (F : ∀ N, U N → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (tm : ∀ N, U N → ℝ) (a : ℕ → ℝ) (Φ : ∀ N, U N → ℝ) (T : ℝ)
    (hΦ : ∀ N q, 0 < Φ N q)
    (hbdd : ∀ N q, BddC2 (F N q))
    (hdrift : ∀ N q M, genD d N (F N q) M = 0)
    (ha : ∀ N, 0 < a N) (htm : ∀ N q, a N ≤ tm N q) (hT : ∀ N q, tm N q - a N ≤ T)
    (hinit : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q : U N,
      momentIntegral d N (F N q) p (a N) ≤ C * ((N : ℝ) ^ (ε * p) * Φ N q ^ (2 * p)))
    (hqv : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q : U N,
      ∀ u ∈ Set.Ico (a N) (tm N q),
        (∫ ω, quadVarPairs d N (F N q) (Hflow d N u ω) ^ p ∂(P d))
          ≤ C * ((N : ℝ) ^ (ε * p) * Φ N q ^ (2 * p))) :
    StochDom (P d) (fun N (q : U N) ω => ‖F N q (Hflow d N (tm N q) ω)‖)
      (fun N q _ => Φ N q) := by
  refine stochDom_of_momentDom (P := P d) hcard hΦ (fun m N q => ?_)
    (momentDom_of_quadVar hst F tm a Φ T hbdd hdrift ha htm hT hinit hqv)
  have := integrable_norm_pow_Hflow (F := F N q) (hbdd N q) (tm N q) (2 * m)
  simpa only [abs_norm] using this

end Pipeline

end RBM.Gauss

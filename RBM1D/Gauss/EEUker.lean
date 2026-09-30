/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.LoopLeibniz
import RBM1D.Hierarchy.ChargeReduce

/-!
# The `U`-conjugated **bilinear** form of (5.22), i.e. `(U ⊗ U) ∘ (E ⊗ E)`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, Definition 5.4 (5.22)–(5.23) and Lemma 5.5 (5.24)–(5.25).

The quadratic-variation term of Lemma 5.5 is the quantity

`‖U_{u,v} ⊗ U_{u,v} ∘ (E ⊗ E)_{u,σ}‖` at `(a, a)`,

written as one `RBM.Uker` on a **doubled** loop.  The ingredients are

* `RBM.Gauss.quadVarPairs_Uker` — `quadVar(Ψ₁) = ∑_{i,j} ‖(U ∘ E^{(M)}(i,j))_a‖²`, and
* for a **single** loop, the gluing (5.22) `RBM.Gauss.eeEdge_eq_sum_SB`.

This file supplies the **bilinear, `U`-conjugated** step that glues the two.

## `E^{(M)}`, `eeArg`/`eeFun` and `RBM.SumZeroDyn.xi2` against Lemma 5.5

Lemma 5.5 spells the operator out:

`[(U_{u,t,σ} ⊗ U_{u,t,σ̄}) ∘ A]_{a,a'} = ∑_{b,b'}`
   `∏_i ((1-u m_i m_{i+1} S)/(1-t m_i m_{i+1} S))_{a_i b_i}`
   `· ∏_i ((1-u m̄_i m̄_{i+1} S)/(1-t m̄_i m̄_{i+1} S))_{a'_i b'_i} · A_{b,b'}`,

"where `σ̄` is the conjugate sign vector of `σ`", and the glued loop (5.23) carries the charges
`(σ_k, …, σ_k, σ̄_k, …, σ̄_k)`.  The second factor therefore runs with the edge parameters
`m̄_i m̄_{i+1} = conj (m_i m_{i+1})`.

`RBM.SumZeroDyn.xi2 E σ` is this doubled vector `(ξ, ξ̄)`; `RBM.EEUker.xi2bar` is the same vector
under a second name (`RBM.EEUker.xi2_eq_xi2bar`).  Since `‖xiOf (mSigma E) σ i‖ = 1` for
`|E| ≤ 2` (`RBM.norm_xiOf_mSigma`, for *every* charge vector), the *estimates* that go through
`xi2` (`RBM.SumZeroDyn.norm_xi2_le`, and all of §7.1) see only the entrywise norms; the
**identity** below needs the conjugation, since `(ξ, ξ̄)` differs from `(ξ, ξ)` as soon as `ξ` is
not real.

The other two ingredients match the paper:

* `RBM.Gauss.emart`/`RBM.Gauss.emartEdge` are `(S_ij)^{1/2} ∂_{ij} L` and its `k`-th edge
  piece, verbatim as in §5.2;
* `RBM.EEBridge.eeArg` (hence `RBM.MomentDuhamel.eeFun`) is `∑_k ∑_{i,j} E^{(M)}_{σ,a}(i,j,k)
  · conj E^{(M)}_{σ,a'}(i,j,k)`, which is Definition 5.4 under the convention that the second
  factor is read as a complex conjugate (justified in `RBM1D/Hierarchy/EEBridge.lean`).  The factor
  `W ∑_{b,b'} S^{(B)}_{b b'}` of (5.22) is already discharged by `RBM.Gauss.eeEdge_eq_sum_SB`;
  nothing here touches it.

## Main results

* `RBM.EEUker.sum_Uker_mul_conj_Uker` — **the bilinear identity**, for an arbitrary family
  `Ef` indexed by the coordinates `α`:
  `∑_α (U ∘ Ef α)_a · conj (U ∘ Ef α)_{a'} = (U ⊗ Ū) ∘ (∑_α Ef α ⊗ conj (Ef α))` at
  `(a, a')`, with `U ⊗ Ū = Uker` at the doubled parameters `Fin.append ξ (conj ∘ ξ)`.
  Purely algebraic; the only hypotheses are `3 ≤ L` and `‖t ξ_i‖ < 1` (needed because
  `RBM.Theta` is `Ring.inverse`).
* `RBM.EEUker.sum_emartEdge_Uker_mul_conj` — the same at `Ef = E^{(M)}(·, k)`.
* `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` — **(5.25)**: with the chain rule
  `E^{(M)}(α) = ∑_k E^{(M)}(α, k)` (the paper's "using the chain rule and the structure of
  `L`", hypothesis `hsplit`), the quadratic variation is at most `n · ‖(U ⊗ Ū) ∘ (E ⊗ E)‖` at
  `(a, a)` — the `E ⊗ E` term of Lemma 5.5.
* `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun` — the same on a `RBM.Band`, with
  `RBM.MomentDuhamel.eeFun` on the right.

## The side hypotheses `hdiff` and `hsplit` (discharged)

`RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` and `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun`
carry the chain rule `hsplit` and the differentiability `hdiff` as hypotheses.  Both are
theorems (`RBM1D/Gauss/LoopLeibniz.lean`), and `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun'`
has the two hypotheses discharged: besides the window `0 ≤ v < 1` it needs only `|E| < 2`,
`u < 1` and `M` Hermitian.  The last is needed by `RBM.Gauss.emart_eq_sum_emartEdge'`
(`RBM.Gauss.emart` reads `M` through the Hermitian projection while `RBM.Gauss.emartEdge` reads it
raw) and is no restriction in §5.2, where `M = H_u`.

Nothing here is an `axiom` and nothing is `sorry`.
-/

namespace RBM

namespace EEUker

open Matrix Finset RBM.Gauss

/-! ### 1. Complex conjugation of the evolution kernel -/

section Conj

variable (L : ℕ) [NeZero L]

/-- **`conj (edgeKer_ξ)_{xy} = (edgeKer_{conj ξ})_{xy}`** at real times.  `S^{(B)}` is real and
`Θ_ξ = (1 - ξ S^{(B)})⁻¹`, so conjugation acts on (5.17)'s single-edge factor only through
`ξ` (`RBM.ChargeReduce.conj_Theta_apply`). -/
theorem conj_edgeKer (hL : 3 ≤ L) {ξ : ℂ} {s t : ℝ} (ht : ‖((t : ℝ) : ℂ) * ξ‖ < 1)
    (x y : ZMod L) :
    (starRingEnd ℂ) (edgeKer L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) x y)
      = edgeKer L ((starRingEnd ℂ) ξ) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) x y := by
  have harg : (starRingEnd ℂ) (((t : ℝ) : ℂ) * ξ) = ((t : ℝ) : ℂ) * (starRingEnd ℂ) ξ := by
    rw [map_mul, Complex.conj_ofReal]
  have hfirst : ∀ c : ZMod L,
      (starRingEnd ℂ) ((1 - (((s : ℝ) : ℂ) * ξ) • SB L) x c)
        = (1 - (((s : ℝ) : ℂ) * (starRingEnd ℂ) ξ) • SB L) x c := by
    intro c
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
      Complex.conj_ofReal, ChargeReduce.conj_SB_apply, Matrix.one_apply,
      apply_ite (starRingEnd ℂ), map_one, map_zero]
  rw [edgeKer, edgeKer, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, hfirst c, ChargeReduce.conj_Theta_apply L hL ht, harg]

theorem conj_prod_edgeKer (hL : 3 ≤ L) {m : ℕ} {ξ : Fin m → ℂ} {s t : ℝ}
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (a b : LoopArg L m) :
    (starRingEnd ℂ) (∏ i, edgeKer L (ξ i) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (a i) (b i))
      = ∏ i, edgeKer L ((starRingEnd ℂ) (ξ i)) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (a i) (b i) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => conj_edgeKer L hL (ht i) (a i) (b i)

/-- **`conj (U_{s,t,σ} ∘ A)_a = (U_{s,t,σ̄} ∘ conj A)_a`**: the conjugate of the evolution
kernel of (5.17) is the evolution kernel of the conjugate charges. -/
theorem conj_Uker_apply (hL : 3 ≤ L) {m : ℕ} {ξ : Fin m → ℂ} {s t : ℝ}
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (A : LoopArg L m → ℂ) (a : LoopArg L m) :
    (starRingEnd ℂ) (Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) A a)
      = Uker L (fun i => (starRingEnd ℂ) (ξ i)) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => (starRingEnd ℂ) (A b)) a := by
  rw [Uker, Uker, map_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [map_mul, conj_prod_edgeKer L hL ht a b]

end Conj

/-! ### 2. The evolution kernel on a doubled loop -/

section Doubled

variable (L : ℕ) [NeZero L]

/-- **`U ⊗ U'` is `RBM.Uker` at the appended edge parameters**, in the explicit form Lemma 5.5
writes it: the doubled kernel factorizes into the two halves of the doubled loop. -/
theorem Uker_append_apply {m m' : ℕ} (ξ : Fin m → ℂ) (ξ' : Fin m' → ℂ) (s t : ℂ)
    (A : LoopArg L (m + m') → ℂ) (a : LoopArg L m) (a' : LoopArg L m') :
    Uker L (Fin.append ξ ξ') s t A (Fin.append a a')
      = ∑ b : LoopArg L m, ∑ b' : LoopArg L m',
          ((∏ i, edgeKer L (ξ i) s t (a i) (b i))
            * (∏ i, edgeKer L (ξ' i) s t (a' i) (b' i))) * A (Fin.append b b') := by
  rw [Uker, SumZeroDyn.sum_append L]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 1
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- `RBM.Uker` is linear in the tensor it acts on. -/
theorem Uker_sum {ι : Type*} (S : Finset ι) {m : ℕ} (ξ : Fin m → ℂ) (s t : ℂ)
    (A : ι → LoopArg L m → ℂ) (a : LoopArg L m) :
    ∑ k ∈ S, Uker L ξ s t (A k) a = Uker L ξ s t (fun c => ∑ k ∈ S, A k c) a := by
  simp only [Uker]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]

end Doubled

/-! ### 3. The bilinear identity -/

section Bilinear

variable (L : ℕ) [NeZero L]

/-- **The `U`-conjugated bilinear gluing.**

`∑_α (U_{s,t,σ} ∘ Ef α)_a · conj ((U_{s,t,σ} ∘ Ef α)_{a'})
   = [(U_{s,t,σ} ⊗ U_{s,t,σ̄}) ∘ (∑_α Ef α ⊗ conj (Ef α))]_{a,a'}`,

with `U ⊗ U_{σ̄}` read, as in Lemma 5.5, as one `RBM.Uker` on the doubled loop with edge
parameters `Fin.append ξ (conj ∘ ξ)`.

There is no analytic content: the only hypotheses are `3 ≤ L` and `‖t ξ_i‖ < 1`, both needed
solely because `RBM.Theta` is a `Ring.inverse` and `RBM.ChargeReduce.conj_Theta_apply` is
stated where that inverse exists. -/
theorem sum_Uker_mul_conj_Uker (hL : 3 ≤ L) {m : ℕ} {ι : Type*} [Fintype ι]
    {ξ : Fin m → ℂ} {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1)
    (Ef : ι → LoopArg L m → ℂ) (a a' : LoopArg L m) :
    ∑ α : ι, Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Ef α) a
        * (starRingEnd ℂ) (Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Ef α) a')
      = Uker L (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i))) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun c => ∑ α : ι, Ef α (SumZeroDyn.spl1 L c)
              * (starRingEnd ℂ) (Ef α (SumZeroDyn.spl2 L c)))
          (Fin.append a a') := by
  set P : LoopArg L m → LoopArg L m → ℂ := fun x y =>
    ∏ i, edgeKer L (ξ i) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (x i) (y i) with hP
  set Pc : LoopArg L m → LoopArg L m → ℂ := fun x y =>
    ∏ i, edgeKer L ((starRingEnd ℂ) (ξ i)) ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (x i) (y i) with hPc
  have hconj : ∀ α : ι, (starRingEnd ℂ) (Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Ef α) a')
      = ∑ b' : LoopArg L m, Pc a' b' * (starRingEnd ℂ) (Ef α b') := by
    intro α
    rw [conj_Uker_apply L hL ht, Uker]
  have hleft : ∀ α : ι, Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Ef α) a
      = ∑ b : LoopArg L m, P a b * Ef α b := fun _ => rfl
  calc ∑ α : ι, Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Ef α) a
          * (starRingEnd ℂ) (Uker L ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (Ef α) a')
      = ∑ α : ι, ∑ b : LoopArg L m, ∑ b' : LoopArg L m,
          (P a b * Ef α b) * (Pc a' b' * (starRingEnd ℂ) (Ef α b')) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hleft α, hconj α, Finset.sum_mul_sum]
    _ = ∑ b : LoopArg L m, ∑ b' : LoopArg L m, ∑ α : ι,
          (P a b * Ef α b) * (Pc a' b' * (starRingEnd ℂ) (Ef α b')) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b : LoopArg L m, ∑ b' : LoopArg L m, (P a b * Pc a' b')
          * ∑ α : ι, Ef α b * (starRingEnd ℂ) (Ef α b') := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun α _ => by ring
    _ = _ := by
        rw [Uker_append_apply L]
        simp only [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append, hP, hPc]

end Bilinear

/-! ### 4. The doubled edge parameters of (5.23): `(ξ, ξ̄)`, not `(ξ, ξ)` -/

section Xi2

/-- **The doubled edge parameters of Lemma 5.5**: `σ` on the first half, the conjugate charge
vector `σ̄` on the second, exactly as in (5.23).

This is *definitionally* `RBM.SumZeroDyn.xi2` (`RBM.EEUker.xi2_eq_xi2bar`). -/
noncomputable def xi2bar (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    Fin ((n + 2) + (n + 2)) → ℂ :=
  Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) (fun i => !(σ i)))

/-- `RBM.SumZeroDyn.xi2` *is* the doubled parameter vector `(ξ, ξ̄)` of Lemma 5.5.

It is `rfl`, so every `xi2bar` in this file may be replaced by `SumZeroDyn.xi2`. -/
theorem xi2_eq_xi2bar (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    SumZeroDyn.xi2 E σ = xi2bar E σ := rfl

/-- `m(σ̄) = conj m(σ)` (the paper's (2.42), `RBM.mSigma`).

`RBM.mSigma_not` in `RBM1D/Gauss/Step6DriftEG.lean` is the same statement; that file is not
imported here. -/
theorem mSigma_not (E : ℝ) (b : Bool) : mSigma E (!b) = (starRingEnd ℂ) (mSigma E b) := by
  cases b <;> simp [mSigma]

theorem xiOf_not (E : ℝ) {n : ℕ} [NeZero n] (σ : Fin n → Bool) (i : Fin n) :
    xiOf (mSigma E) (fun j => !(σ j)) i = (starRingEnd ℂ) (xiOf (mSigma E) σ i) := by
  rw [xiOf, xiOf, map_mul, mSigma_not, mSigma_not]

/-- `xi2bar` is `Fin.append ξ (conj ∘ ξ)`, the shape the bilinear identity produces. -/
theorem xi2bar_eq_append_conj (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    xi2bar E σ
      = Fin.append (xiOf (mSigma E) σ)
          (fun i => (starRingEnd ℂ) (xiOf (mSigma E) σ i)) := by
  rw [xi2bar]
  congr 1
  funext i
  exact xiOf_not E σ i

end Xi2

/-! ### 5. `E ⊗ E` in the doubled-argument shape, and (5.22) under `U ⊗ Ū` -/

/-- **`(E ⊗ E)^{(k)}` of (5.22)**, in the doubled-argument shape. -/
noncomputable def eeEdgeArg (d : Gauss.Dims) (N : ℕ) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {n : ℕ} (σ : Fin n → Bool) (k : ℕ)
    (c : LoopArg (d.L N) (n + n)) : ℂ :=
  eeEdge d N z M (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c)) k

section Spec

variable {d : Gauss.Dims} {N n : ℕ}

/-- **The bilinear identity at `Ef = E^{(M)}(·, k)`** — this is (5.22) conjugated by `U ⊗ Ū`. -/
theorem sum_emartEdge_Uker_mul_conj (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (k : ℕ) (a a' : LoopArg (d.L N) n) :
    ∑ i : d.Idx N, ∑ j : d.Idx N,
        Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M k i j) a
          * (starRingEnd ℂ) (Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M k i j) a')
      = Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeEdgeArg d N z M σ k) (Fin.append a a') := by
  have hkey := sum_Uker_mul_conj_Uker (d.L N) hL (ι := d.Idx N × d.Idx N) (s := s) ht
    (fun α b => emartEdge d N z (toIdx σ b) M k α.1 α.2) a a'
  rw [Fintype.sum_prod_type] at hkey
  refine hkey.trans ?_
  congr 1
  funext c
  rw [eeEdgeArg, eeEdge, Fintype.sum_prod_type]
  rfl

/-- `E ⊗ E` is the sum of its `n` edge pieces, in the doubled-argument shape. -/
theorem eeArg_eq_sum_eeEdgeArg (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (σ : Fin n → Bool)
    (c : LoopArg (d.L N) (n + n)) :
    EEBridge.eeArg d N z M σ c = ∑ k ∈ Finset.range n, eeEdgeArg d N z M σ k c := by
  rw [EEBridge.eeArg, eeTens, toIdx_length]
  rfl

/-- Summing (5.22) over the `n` edges: `∑_k (U ⊗ Ū) ∘ (E⊗E)^{(k)} = (U ⊗ Ū) ∘ (E⊗E)`. -/
theorem sum_Uker_eeEdgeArg (ξ2 : Fin (n + n) → ℂ) (s t : ℂ) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) :
    ∑ k ∈ Finset.range n, Uker (d.L N) ξ2 s t (eeEdgeArg d N z M σ k) c
      = Uker (d.L N) ξ2 s t (EEBridge.eeArg d N z M σ) c := by
  rw [Uker_sum (d.L N)]
  congr 1
  funext c'
  exact (eeArg_eq_sum_eeEdgeArg z M σ c').symm

end Spec

/-! ### 6. The quadratic variation of `Ψ₁ = (U ∘ L)_a` -/

section QuadVar

variable {d : Gauss.Dims} {N n : ℕ}

/-- **(5.25)**: the quadratic variation of `Ψ₁` is at most `n · [(U ⊗ Ū) ∘ (E ⊗ E)]_{a,a}`,
with `E ⊗ E` the `E ⊗ E` of Definition 5.4 (`RBM.EEBridge.eeArg`).

`hsplit` is the paper's chain rule `E^{(M)}(α) = ∑_{k=1}^n E^{(M)}(α, k)`; it is a theorem for
Hermitian `M` (`RBM.Gauss.emart_eq_sum_emartEdge'`, from the Leibniz rule for the `List.foldr`
product of resolvents). -/
theorem quadVarPairs_Uker_le_norm_eeArg (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n)
    (hdiff : ∀ b : LoopArg (d.L N) n, DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M)
    (hsplit : ∀ (b : LoopArg (d.L N) n) (i j : d.Idx N), emart d N z (toIdx σ b) M i j
      = ∑ k ∈ Finset.range n, emartEdge d N z (toIdx σ b) M k i j) :
    quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
        (fun b => loopObs d N z (toIdx σ b) M') a) M
      ≤ (n : ℝ) * ‖Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (EEBridge.eeArg d N z M σ) (Fin.append a a)‖ := by
  set ξ2 : Fin (n + n) → ℂ := Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)) with hξ2
  -- the `k`-th edge contribution, as a nonnegative real
  set r : ℕ → ℝ := fun k => ∑ i : d.Idx N, ∑ j : d.Idx N,
    ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
      (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2 with hr
  have hr0 : ∀ k, 0 ≤ r k := fun k =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hrC : ∀ k, ((r k : ℝ) : ℂ)
      = Uker (d.L N) ξ2 ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeEdgeArg d N z M σ k)
          (Fin.append a a) := by
    intro k
    rw [hr, Complex.ofReal_sum, ← sum_emartEdge_Uker_mul_conj hL σ ht z M k a a]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_conj_eq _).symm
  have hsum : ((∑ k ∈ Finset.range n, r k : ℝ) : ℂ)
      = Uker (d.L N) ξ2 ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (EEBridge.eeArg d N z M σ)
          (Fin.append a a) := by
    rw [Complex.ofReal_sum, ← sum_Uker_eeEdgeArg ξ2 _ _ z M σ (Fin.append a a)]
    exact Finset.sum_congr rfl fun k _ => hrC k
  have hnorm : ∑ k ∈ Finset.range n, r k
      = ‖Uker (d.L N) ξ2 ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (EEBridge.eeArg d N z M σ)
          (Fin.append a a)‖ := by
    rw [← hsum, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun k _ => hr0 k)]
  -- the Schwarz step, coordinate by coordinate
  have hsplitU : ∀ i j : d.Idx N,
      Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => emart d N z (toIdx σ b) M i j) a
        = ∑ k ∈ Finset.range n, Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M k i j) a := by
    intro i j
    rw [Uker_sum (d.L N)]
    congr 1
    funext b
    exact hsplit b i j
  have hkey : ∀ i j : d.Idx N,
      ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => emart d N z (toIdx σ b) M i j) a‖ ^ 2
        ≤ (n : ℝ) * ∑ k ∈ Finset.range n,
            ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2 := by
    intro i j
    have h1 : ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => emart d N z (toIdx σ b) M i j) a‖
        ≤ ∑ k ∈ Finset.range n, ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ := by
      rw [hsplitU i j]
      exact norm_sum_le _ _
    have h2 : (∑ k ∈ Finset.range n, ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖) ^ 2
        ≤ ((Finset.range n).card : ℝ) * ∑ k ∈ Finset.range n,
            ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
              (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_range] at h2
    refine le_trans ?_ h2
    gcongr
  -- assemble
  rw [quadVarPairs_Uker σ ξ _ _ z M a hdiff, ← hnorm]
  calc ∑ i : d.Idx N, ∑ j : d.Idx N,
        ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => emart d N z (toIdx σ b) M i j) a‖ ^ 2
      ≤ ∑ i : d.Idx N, ∑ j : d.Idx N, ((n : ℝ) * ∑ k ∈ Finset.range n,
          ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hkey i j
    _ = (n : ℝ) * ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ k ∈ Finset.range n,
          ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (n : ℝ) * ∑ k ∈ Finset.range n, r k := by
        rw [hr]
        congr 1
        calc ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ k ∈ Finset.range n,
                ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
                  (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2
            = ∑ i : d.Idx N, ∑ k ∈ Finset.range n, ∑ j : d.Idx N,
                ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
                  (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2 :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ k ∈ Finset.range n, ∑ i : d.Idx N, ∑ j : d.Idx N,
                ‖Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
                  (fun b => emartEdge d N z (toIdx σ b) M k i j) a‖ ^ 2 := Finset.sum_comm

end QuadVar

/-! ### 7. The same on a `RBM.Band`, with `RBM.MomentDuhamel.eeFun` -/

section BandForm

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The `E ⊗ E` term of Lemma 5.5 on a `RBM.Band`.**

At a time `u` of the window and a running time `v ∈ [0, 1)`, the quadratic variation of
`Ψ₁ = (U_{u,v,σ} ∘ L_{u,σ,·})_a` is at most `(n+2)` times

`‖U_{u,v,σ} ⊗ U_{u,v,σ̄} ∘ (E ⊗ E)_{u,σ}‖` at `(a, a)`,

where the doubled edge parameters `RBM.SumZeroDyn.xi2` *are* the paper's `(ξ, ξ̄)`
(`RBM.EEUker.xi2_eq_xi2bar`), so `RBM.EEUker.xi2bar` below may be replaced by
`RBM.SumZeroDyn.xi2`. -/
theorem quadVarPairs_Uker_le_norm_eeFun {E : ℝ} (hE : |E| ≤ 2) {N n : ℕ} {u v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (σ : Fin (n + 2) → Bool)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (a : LoopArg (B.L N) (n + 2))
    (hdiff : ∀ b : LoopArg (B.L N) (n + 2),
      DifferentiableAt ℝ (loopObs B.toDims N (zt E u) (toIdx σ b)) M)
    (hsplit : ∀ (b : LoopArg (B.L N) (n + 2)) (i j : B.Idx N),
      emart B.toDims N (zt E u) (toIdx σ b) M i j
        = ∑ k ∈ Finset.range (n + 2), emartEdge B.toDims N (zt E u) (toIdx σ b) M k i j) :
    quadVarPairs B.toDims N (fun M' => Uker (B.L N) (xiOf (mSigma E) σ)
        ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => loopObs B.toDims N (zt E u) (toIdx σ b) M') a) M
      ≤ ((n : ℝ) + 2) * ‖Uker (B.L N) (xi2bar E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (MomentDuhamel.eeFun B E N u M σ) (Fin.append a a)‖ := by
  have ht : ∀ i : Fin (n + 2), ‖((v : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := fun i =>
    norm_mul_mSigma_lt_one hE hv0 hv1 (σ i) (σ (i + 1))
  have hkey := quadVarPairs_Uker_le_norm_eeArg (d := B.toDims) (N := N) (B.three_le_L N) σ
    (ξ := xiOf (mSigma E) σ) (s := u) (t := v) ht (zt E u) M a hdiff hsplit
  rw [xi2bar_eq_append_conj E σ]
  have hcast : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hkey
  exact hkey

/-- **(5.25) on a `RBM.Band`, with both side hypotheses discharged.**  Strictly inside the
flow (`|E| < 2`, `u < 1`) the spectral parameter `z_u` is off the real axis, so
`RBM.Gauss.differentiableAt_loopObs` and `RBM.Gauss.emart_eq_sum_emartEdge'` supply the
hypotheses `hdiff` and `hsplit` (the chain rule) of `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun`;
only `M` Hermitian remains, and in §5.2 `M = H_u`. -/
theorem quadVarPairs_Uker_le_norm_eeFun' {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u v : ℝ}
    (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (σ : Fin (n + 2) → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (a : LoopArg (B.L N) (n + 2)) :
    quadVarPairs B.toDims N (fun M' => Uker (B.L N) (xiOf (mSigma E) σ)
        ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => loopObs B.toDims N (zt E u) (toIdx σ b) M') a) M
      ≤ ((n : ℝ) + 2) * ‖Uker (B.L N) (xi2bar E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (MomentDuhamel.eeFun B E N u M σ) (Fin.append a a)‖ := by
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  refine quadVarPairs_Uker_le_norm_eeFun hE.le hv0 hv1 σ M a
    (fun b => differentiableAt_loopObs (d := B.toDims) (N := N) hz (toIdx_wf σ b) M)
    (fun b i j => ?_)
  exact emart_eq_sum_emartEdge' (d := B.toDims) (N := N) (m := n + 2) hz hM (toIdx_wf σ b)
    (show (toIdx σ b).a.length = n + 2 from toIdx_length σ b) i j

end BandForm

/-! ### 8. The numerical self-consistency check

`L = 3`, one edge, one coordinate `α`, `ξ = i`, `s = 1`, `t = 0`.  At `t = 0` the propagator
is `Θ_0 = 1` (`RBM.Theta_zero`), so the edge factor of (5.17) is the completely explicit
matrix `1 - ξ S^{(B)}`, and `S^{(B)}` on `ZMod 3` is the constant `1/3`.  Both sides are then
finite sums of explicit complex numbers, and **neither evaluation below uses any theorem of
this file**. -/

section Sanity

end Sanity

end EEUker

end RBM

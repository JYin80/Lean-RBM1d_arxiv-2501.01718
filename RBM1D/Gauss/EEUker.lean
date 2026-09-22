/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.LoopLeibniz
import RBM1D.Hierarchy.ChargeReduce

/-!
# T213: the `U`-conjugated **bilinear** form of (5.22), i.e. `(U ⊗ U) ∘ (E ⊗ E)`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, Definition 5.4 (5.22)–(5.23) and Lemma 5.5 (5.24)–(5.25).

`RBM.MomentDuhamel.Hyp.momentDuhamel` carries on its right-hand side the quantity

`‖U_{u,v} ⊗ U_{u,v} ∘ (E ⊗ E)_{u,σ}‖` at `(a, a)`,

written in the repository as one `RBM.Uker` on a **doubled** loop.  What existed before this
file was

* `RBM.Gauss.quadVarPairs_Uker` — `quadVar(Ψ₁) = ∑_{i,j} ‖(U ∘ E^{(M)}(i,j))_a‖²`, and
* for a **single** loop, `RBM.Gauss.eeRaw_self` and the gluing (5.22)
  `RBM.Gauss.eeEdge_eq_sum_SB`.

Missing was the **bilinear, `U`-conjugated** step that glues the two: this file supplies it.

## The step-0 audit: `E^{(M)}`, `eeArg`/`eeFun` and `RBM.SumZeroDyn.xi2`

**They did not match, and the mismatch was exactly one complex conjugation on the second half
of the doubled edge-parameter vector.  T223 (2026-09-21) repaired the definition in place; this
section records what the defect was and what now discharges it.**

Lemma 5.5 (p. 55) spells the operator out:

`[(U_{u,t,σ} ⊗ U_{u,t,σ̄}) ∘ A]_{a,a'} = ∑_{b,b'}`
   `∏_i ((1-u m_i m_{i+1} S)/(1-t m_i m_{i+1} S))_{a_i b_i}`
   `· ∏_i ((1-u m̄_i m̄_{i+1} S)/(1-t m̄_i m̄_{i+1} S))_{a'_i b'_i} · A_{b,b'}`,

"where `σ̄` is the conjugate sign vector of `σ`", and the glued loop (5.23) carries the charges
`(σ_k, …, σ_k, σ̄_k, …, σ̄_k)`.  The second factor therefore runs with the edge parameters
`m̄_i m̄_{i+1} = conj (m_i m_{i+1})`.

Before T223, `RBM.SumZeroDyn.xi2 E σ` was `Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) σ)`,
which repeats the **unconjugated** vector.  Since `‖xiOf (mSigma E) σ i‖ = 1` for `|E| ≤ 2` and
`RBM.norm_xiOf_mSigma` holds for *every* charge vector, every *estimate* in the repository that
goes through `xi2` (`RBM.SumZeroDyn.norm_xi2_le`, `RBM.SumZeroDyn.xi2_ne_zero`,
`RBM.Gauss.norm_xi2_mSigma`, and all of §7.1) was blind to the difference — but the **identity**
below is false for the old vector and true for the corrected one.  `RBM.EEUker.xi2bar` is that
corrected vector; `RBM.EEUker.xi2_eq_xi2bar` now identifies it with `RBM.SumZeroDyn.xi2`,
`RBM.EEUker.norm_xi2bar` records that the entrywise norms did not move (so no downstream
estimate had to change), and `RBM.EEUker.xi2bar_ne_xi2` exhibits a concrete `(E, σ)` at which
the corrected vector differs from the **pre-T223** one, so the correction is not vacuous.

The other two sides of the audit **do** match:

* `RBM.Gauss.emart`/`RBM.Gauss.emartEdge` are `(S_ij)^{1/2} ∂_{ij} L` and its `k`-th edge
  piece, verbatim as on p. 55;
* `RBM.EEBridge.eeArg` (hence `RBM.MomentDuhamel.eeFun`) is `∑_k ∑_{i,j} E^{(M)}_{σ,a}(i,j,k)
  · conj E^{(M)}_{σ,a'}(i,j,k)`, which is Definition 5.4 under the repository's standing
  convention that the second factor is read as a complex conjugate
  (`docs/paper-deltas.md` #102).  The factor `W ∑_{b,b'} S^{(B)}_{b b'}` of (5.22) is already
  discharged by `RBM.Gauss.eeEdge_eq_sum_SB`; nothing here touches it.

## Main results

* `RBM.EEUker.sum_Uker_mul_conj_Uker` — **the bilinear identity**, for an arbitrary family
  `Ef` indexed by the coordinates `α`:
  `∑_α (U ∘ Ef α)_a · conj (U ∘ Ef α)_{a'} = (U ⊗ Ū) ∘ (∑_α Ef α ⊗ conj (Ef α))` at
  `(a, a')`, with `U ⊗ Ū = Uker` at the doubled parameters `Fin.append ξ (conj ∘ ξ)`.
  Purely algebraic; the only hypotheses are `3 ≤ L` and `‖t ξ_i‖ < 1` (needed because
  `RBM.Theta` is `Ring.inverse`).
* `RBM.EEUker.sum_emart_Uker_mul_conj`, `RBM.EEUker.sum_emartEdge_Uker_mul_conj` — the same
  at `Ef = E^{(M)}`, resp. `E^{(M)}(·, k)`.
* `RBM.EEUker.quadVarPairs_Uker_eq_norm_eeRawArg` — **exact**: the quadratic variation of
  `Ψ₁ = (U ∘ L)_a` *equals* `‖(U ⊗ Ū) ∘ (E ⊗ E)^{raw}‖` at `(a, a)`.
* `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` — **(5.25)**: with the chain rule
  `E^{(M)}(α) = ∑_k E^{(M)}(α, k)` (the paper's "using the chain rule and the structure of
  `L`", which `RBM1D/Gauss/DischargeBDG.lean` also carries as a hypothesis), the quadratic
  variation is at most `n · ‖(U ⊗ Ū) ∘ (E ⊗ E)‖` at `(a, a)` — literally the `E ⊗ E` term of
  `RBM.MomentDuhamel.Hyp.momentDuhamel`, with `RBM.EEUker.xi2bar` in place of `xi2`.
* `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun` — the same on a `RBM.Band`, with
  `RBM.MomentDuhamel.eeFun` on the right.

## The numerical self-consistency check

An identity compiles just as happily when a factor `W`, `L` or `S^{(B)}` is misplaced, so
the last section evaluates **both sides independently** at `L = 3`, one edge (`m = 1`), one
coordinate `α`, `ξ = i`, `s = 1`, `t = 0` (where `Θ_0 = 1`, so the edge kernel is the explicit
matrix `1 - ξ S^{(B)}`), `a = (0)`, `a' = (1)`:

* `RBM.EEUker.sanity_lhs` and `RBM.EEUker.sanity_rhs` both evaluate to `8/9 - (4/3) i`;
* `RBM.EEUker.sanity_lhs_diag` and `RBM.EEUker.sanity_rhs_diag` both evaluate to `26/9`.

Neither evaluation uses any theorem of this file, so the agreement is a genuine check; both
values are **nonzero** (off-diagonal and diagonal witness), and the off-diagonal value has a
nonzero imaginary part, which is exactly what discriminates `Fin.append ξ (conj ∘ ξ)` from
`Fin.append ξ ξ` (`RBM.EEUker.sanity_rhs_xi2_wrong` computes the latter and gets a different
number).

## The side hypotheses `hdiff` and `hsplit` (T224, discharged)

The unprimed statements carry the chain rule `hsplit` and the differentiability `hdiff` as
hypotheses, exactly as `RBM.Gauss.quadVarPairs_le_of_split` and `RBM.Gauss.quadVarPairs_Uker`
do.  Since T224 both are theorems (`RBM1D/Gauss/LoopLeibniz.lean`), so each statement also has
a primed version with the two slots discharged:

* `RBM.EEUker.quadVarPairs_Uker_eq_eeRawArg'`, `RBM.EEUker.quadVarPairs_Uker_eq_norm_eeRawArg'`
  — hypothesis `Im z ≠ 0` only (`RBM.Gauss.differentiableAt_loopObs`);
* `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg'`,
  `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun'`,
  `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun_xi2'` — `Im z ≠ 0` and `M` Hermitian; the latter
  is needed by `RBM.Gauss.emart_eq_sum_emartEdge'` (T224: `RBM.Gauss.emart` reads `M` through
  the Hermitian projection while `RBM.Gauss.emartEdge` reads it raw) and is no restriction in
  §5.2, where `M = H_u`.

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

Since T223 this is *definitionally* `RBM.SumZeroDyn.xi2` (`RBM.EEUker.xi2_eq_xi2bar`); it is
kept as a separate name because the module docstring, the non-vacuity witness
`RBM.EEUker.xi2bar_ne_xi2` and the numerical check of §8 all speak about the correction itself.
Downstream consumers should use `RBM.SumZeroDyn.xi2`. -/
noncomputable def xi2bar (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    Fin ((n + 2) + (n + 2)) → ℂ :=
  Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) (fun i => !(σ i)))

/-- **T223**: `RBM.SumZeroDyn.xi2` *is* the doubled parameter vector `(ξ, ξ̄)` of Lemma 5.5.

This is the statement the correction of `RBM.SumZeroDyn.xi2` was made to produce; it is now
`rfl`, and every `xi2bar` in this file may be replaced by `SumZeroDyn.xi2` (see
`RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun_xi2`). -/
theorem xi2_eq_xi2bar (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    SumZeroDyn.xi2 E σ = xi2bar E σ := rfl

/-- `m(σ̄) = conj m(σ)` (the paper's (2.42), `RBM.mSigma`).

**Duplicate.**  `RBM.mSigma_not` in `RBM1D/Gauss/Step6DriftEG.lean` is the same statement with
the same proof; that file is not in this file's import closure and adding it would drag the
whole `Step6` chain in for a one-line lemma.  It should be sunk to `RBM1D/Defs/` and both
copies replaced (see `docs/STATUS.md`). -/
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

/-- The same for `RBM.SumZeroDyn.xi2` itself: it is `Fin.append ξ (conj ∘ ξ)`, the shape the
bilinear identity `RBM.EEUker.sum_Uker_mul_conj_Uker` produces. -/
theorem xi2_eq_append_conj (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    SumZeroDyn.xi2 E σ
      = Fin.append (xiOf (mSigma E) σ)
          (fun i => (starRingEnd ℂ) (xiOf (mSigma E) σ i)) :=
  (xi2_eq_xi2bar E σ).trans (xi2bar_eq_append_conj E σ)

/-- **The correction was invisible to every norm bound**: the pre-T223 `xi2`, which repeated
the unconjugated vector, had the same entrywise norms as the corrected one, which is why
`RBM.SumZeroDyn.norm_xi2_le`, `RBM.SumZeroDyn.xi2_ne_zero` and `RBM.Gauss.norm_xi2_mSigma`
transferred verbatim and no downstream estimate had to move. -/
theorem norm_xi2bar (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))) :
    ‖xi2bar E σ i‖
      = ‖Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) σ) i‖ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [xi2bar, Fin.append_left, Fin.append_left]
  · rw [xi2bar, Fin.append_right, Fin.append_right, xiOf_not, Complex.norm_conj]

/-- **…but the correction is not vacuous**: at `E = 1` with all charges `+`, the corrected
doubled parameter vector differs from the **pre-T223** one (`Fin.append ξ ξ`).  (They agree
exactly when every `ξ_i` is real, e.g. at `E = 0` with constant charges, or at any alternating
charge vector, where `ξ_i = |m|² = 1`.)

Before T223 the right-hand side below was literally `RBM.SumZeroDyn.xi2`; after the repair
`SumZeroDyn.xi2 = xi2bar` (`RBM.EEUker.xi2_eq_xi2bar`), so the *content* of this witness — that
the conjugation actually changes the vector — is preserved only by spelling the old definition
body out. -/
theorem xi2bar_ne_xi2 :
    xi2bar 1 (fun _ : Fin (0 + 2) => true)
      ≠ Fin.append (xiOf (mSigma 1) (fun _ : Fin (0 + 2) => true))
          (xiOf (mSigma 1) (fun _ : Fin (0 + 2) => true)) := by
  intro h
  have hi := congrFun h (Fin.natAdd (0 + 2) (0 : Fin (0 + 2)))
  rw [xi2bar, Fin.append_right, Fin.append_right, xiOf_not] at hi
  have him := congrArg Complex.im hi
  rw [Complex.conj_im] at him
  have hxi : (xiOf (mSigma 1) (fun _ : Fin (0 + 2) => true) (0 : Fin (0 + 2))).im
      = 2 * ((mE 1).re * (mE 1).im) := by
    rw [xiOf, mSigma_true, Complex.mul_im]
    ring
  rw [hxi, mE_re, mE_im] at him
  have hs : (0 : ℝ) < Real.sqrt (4 - (1 : ℝ) ^ 2) := Real.sqrt_pos.2 (by norm_num)
  set S := Real.sqrt (4 - (1 : ℝ) ^ 2) with hSdef
  linarith

end Xi2

/-! ### 5. `E ⊗ E` in the doubled-argument shape, and (5.22) under `U ⊗ Ū` -/

/-- **`E ⊗ E` before the edge split**, `∑_{i,j} E^{(M)}_{σ,b}(i,j) · conj E^{(M)}_{σ,b'}(i,j)`,
in the doubled-argument shape of `RBM.EEBridge.eeArg`.  This is the *exact* quadratic
variation; Definition 5.4's `E ⊗ E` is its `k`-diagonal part, and (5.25) is the Schwarz step
between the two. -/
noncomputable def eeRawArg (d : Gauss.Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {n : ℕ} (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) : ℂ :=
  eeRaw d N z M (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c))

/-- **`(E ⊗ E)^{(k)}` of (5.22)**, in the doubled-argument shape. -/
noncomputable def eeEdgeArg (d : Gauss.Dims) (N : ℕ) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {n : ℕ} (σ : Fin n → Bool) (k : ℕ)
    (c : LoopArg (d.L N) (n + n)) : ℂ :=
  eeEdge d N z M (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c)) k

section Spec

variable {d : Gauss.Dims} {N n : ℕ}

/-- **The bilinear identity at `Ef = E^{(M)}`.** -/
theorem sum_emart_Uker_mul_conj (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ} {s t : ℝ}
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a a' : LoopArg (d.L N) n) :
    ∑ i : d.Idx N, ∑ j : d.Idx N,
        Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emart d N z (toIdx σ b) M i j) a
          * (starRingEnd ℂ) (Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
            (fun b => emart d N z (toIdx σ b) M i j) a')
      = Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeRawArg d N z M σ) (Fin.append a a') := by
  have hkey := sum_Uker_mul_conj_Uker (d.L N) hL (ι := d.Idx N × d.Idx N) (s := s) ht
    (fun α b => emart d N z (toIdx σ b) M α.1 α.2) a a'
  rw [Fintype.sum_prod_type] at hkey
  refine hkey.trans ?_
  congr 1
  funext c
  rw [eeRawArg, eeRaw, Fintype.sum_prod_type]
  rfl

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

/-- **Exact form**: the quadratic variation of `Ψ₁ = (U_{s,t,σ} ∘ L_{σ,·})_a` is
`[(U ⊗ Ū) ∘ (E ⊗ E)^{raw}]_{a,a}`, with `(E⊗E)^{raw}` the *unsplit* second moment
`∑_{i,j} E^{(M)}(i,j) ⊗ conj E^{(M)}(i,j)`.  No Schwarz step and no chain rule. -/
theorem quadVarPairs_Uker_eq_eeRawArg (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n)
    (hdiff : ∀ b : LoopArg (d.L N) n, DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M) :
    ((quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => loopObs d N z (toIdx σ b) M') a) M : ℝ) : ℂ)
      = Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeRawArg d N z M σ) (Fin.append a a) := by
  rw [quadVarPairs_Uker σ ξ _ _ z M a hdiff, Complex.ofReal_sum]
  rw [← sum_emart_Uker_mul_conj hL σ ht z M a a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => (mul_conj_eq _).symm

theorem quadVarPairs_Uker_eq_norm_eeRawArg (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) (z : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n)
    (hdiff : ∀ b : LoopArg (d.L N) n, DifferentiableAt ℝ (loopObs d N z (toIdx σ b)) M) :
    quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
        (fun b => loopObs d N z (toIdx σ b) M') a) M
      = ‖Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeRawArg d N z M σ) (Fin.append a a)‖ := by
  rw [← quadVarPairs_Uker_eq_eeRawArg hL σ ht z M a hdiff, Complex.norm_real,
    Real.norm_of_nonneg]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/-- **The same with `hdiff` discharged** (T224's `RBM.Gauss.differentiableAt_loopObs`): off the
real axis the loop observable is differentiable in the matrix at *every* `M`, with no
Hermitian and no invertibility hypothesis. -/
theorem quadVarPairs_Uker_eq_eeRawArg' (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) {z : ℂ} (hz : z.im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n) :
    ((quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
          (fun b => loopObs d N z (toIdx σ b) M') a) M : ℝ) : ℂ)
      = Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeRawArg d N z M σ) (Fin.append a a) :=
  quadVarPairs_Uker_eq_eeRawArg hL σ ht z M a
    fun b => differentiableAt_loopObs hz (toIdx_wf σ b) M

/-- `RBM.EEUker.quadVarPairs_Uker_eq_norm_eeRawArg` with `hdiff` discharged. -/
theorem quadVarPairs_Uker_eq_norm_eeRawArg' (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) {z : ℂ} (hz : z.im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n) :
    quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
        (fun b => loopObs d N z (toIdx σ b) M') a) M
      = ‖Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (eeRawArg d N z M σ) (Fin.append a a)‖ :=
  quadVarPairs_Uker_eq_norm_eeRawArg hL σ ht z M a
    fun b => differentiableAt_loopObs hz (toIdx_wf σ b) M

/-- **(5.25)**: the quadratic variation of `Ψ₁` is at most `n · [(U ⊗ Ū) ∘ (E ⊗ E)]_{a,a}`,
with `E ⊗ E` the `E ⊗ E` of Definition 5.4 (`RBM.EEBridge.eeArg`).

`hsplit` is the paper's chain rule `E^{(M)}(α) = ∑_{k=1}^n E^{(M)}(α, k)`; it is the same
hypothesis `RBM.Gauss.quadVarPairs_le_of_split` carries, and it is not proved anywhere in the
repository (it needs the Leibniz rule for the `List.foldr` product of resolvents). -/
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

/-- **(5.25) with both side hypotheses discharged.**  T224's
`RBM.Gauss.differentiableAt_loopObs` gives `hdiff` and `RBM.Gauss.emart_eq_sum_emartEdge'`
gives the chain rule `hsplit`; the latter needs `M` Hermitian, because `RBM.Gauss.emart` reads
`M` through the Hermitian projection while `RBM.Gauss.emartEdge` reads it raw (T224), which is
no restriction in §5.2, where `M = H_u` throughout. -/
theorem quadVarPairs_Uker_le_norm_eeArg' (hL : 3 ≤ d.L N) (σ : Fin n → Bool) {ξ : Fin n → ℂ}
    {s t : ℝ} (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1) {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (a : LoopArg (d.L N) n) :
    quadVarPairs d N (fun M' => Uker (d.L N) ξ ((s : ℝ) : ℂ) ((t : ℝ) : ℂ)
        (fun b => loopObs d N z (toIdx σ b) M') a) M
      ≤ (n : ℝ) * ‖Uker (d.L N) (Fin.append ξ (fun i => (starRingEnd ℂ) (ξ i)))
          ((s : ℝ) : ℂ) ((t : ℝ) : ℂ) (EEBridge.eeArg d N z M σ) (Fin.append a a)‖ :=
  quadVarPairs_Uker_le_norm_eeArg hL σ ht z M a
    (fun b => differentiableAt_loopObs hz (toIdx_wf σ b) M)
    fun b i j => emart_eq_sum_emartEdge' hz hM (toIdx_wf σ b)
      (show (toIdx σ b).a.length = n from toIdx_length σ b) i j

end QuadVar

/-! ### 7. The same on a `RBM.Band`, with `RBM.MomentDuhamel.eeFun` -/

section BandForm

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The `E ⊗ E` term of `RBM.MomentDuhamel.Hyp.momentDuhamel`, supplied by a theorem.**

At a time `u` of the window and a running time `v ∈ [0, 1)`, the quadratic variation of
`Ψ₁ = (U_{u,v,σ} ∘ L_{u,σ,·})_a` is at most `(n+2)` times

`‖U_{u,v,σ} ⊗ U_{u,v,σ̄} ∘ (E ⊗ E)_{u,σ}‖` at `(a, a)`,

which is the third right-hand term of `momentDuhamel` verbatim: since T223 the doubled edge
parameters `RBM.SumZeroDyn.xi2` *are* the paper's `(ξ, ξ̄)` (`RBM.EEUker.xi2_eq_xi2bar`), so
`RBM.EEUker.xi2bar` below may be replaced by `RBM.SumZeroDyn.xi2` — see
`RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun_xi2`. -/
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

/-- **The same statement with `RBM.SumZeroDyn.xi2` on the right**, i.e. with the doubled edge
parameters exactly as `RBM.MomentDuhamel.Hyp.momentDuhamel` and `RBM.SumZeroDyn.Hierarchy.bdg`
spell them.  This is the T223 acceptance check: after the repair of `RBM.SumZeroDyn.xi2` no
`xi2bar` is needed to state the `E ⊗ E` term. -/
theorem quadVarPairs_Uker_le_norm_eeFun_xi2 {E : ℝ} (hE : |E| ≤ 2) {N n : ℕ} {u v : ℝ}
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
      ≤ ((n : ℝ) + 2) * ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (MomentDuhamel.eeFun B E N u M σ) (Fin.append a a)‖ := by
  rw [xi2_eq_xi2bar E σ]
  exact quadVarPairs_Uker_le_norm_eeFun hE hv0 hv1 σ M a hdiff hsplit

/-- **(5.25) on a `RBM.Band`, with both side hypotheses discharged.**  Strictly inside the
flow (`|E| < 2`, `u < 1`) the spectral parameter `z_u` is off the real axis, so T224's
`RBM.Gauss.differentiableAt_loopObs` and `RBM.Gauss.emart_eq_sum_emartEdge'` supply `hdiff`
and the chain rule `hsplit`; only `M` Hermitian remains, and in §5.2 `M = H_u`. -/
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

/-- **The `E ⊗ E` right-hand side of `RBM.MomentDuhamel.Hyp.momentDuhamel`, produced by a
theorem whose only remaining hypotheses are the window and `M` Hermitian.**  This is the
`RBM.SumZeroDyn.xi2` form (T223) of `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun'`. -/
theorem quadVarPairs_Uker_le_norm_eeFun_xi2' {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u v : ℝ}
    (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (σ : Fin (n + 2) → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (a : LoopArg (B.L N) (n + 2)) :
    quadVarPairs B.toDims N (fun M' => Uker (B.L N) (xiOf (mSigma E) σ)
        ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b => loopObs B.toDims N (zt E u) (toIdx σ b) M') a) M
      ≤ ((n : ℝ) + 2) * ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (MomentDuhamel.eeFun B E N u M σ) (Fin.append a a)‖ := by
  rw [xi2_eq_xi2bar E σ]
  exact quadVarPairs_Uker_le_norm_eeFun' hE hu1 hv0 hv1 σ hM a

/-- The bare form of the acceptance check demanded by the T223 ticket: the `E ⊗ E` term of
`RBM.MomentDuhamel.Hyp.momentDuhamel`, written with `RBM.SumZeroDyn.xi2`, is literally the one
the bilinear identity of §3 produces. -/
example {E : ℝ} {N n : ℕ} {u v : ℝ} (σ : Fin (n + 2) → Bool)
    (A : LoopArg (B.L N) ((n + 2) + (n + 2)) → ℂ)
    (c : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ) A c
      = Uker (B.L N) (Fin.append (xiOf (mSigma E) σ)
          (fun i => (starRingEnd ℂ) (xiOf (mSigma E) σ i)))
          ((u : ℝ) : ℂ) ((v : ℝ) : ℂ) A c := by
  rw [xi2_eq_append_conj E σ]

end BandForm

/-! ### 8. The numerical self-consistency check

`L = 3`, one edge, one coordinate `α`, `ξ = i`, `s = 1`, `t = 0`.  At `t = 0` the propagator
is `Θ_0 = 1` (`RBM.Theta_zero`), so the edge factor of (5.17) is the completely explicit
matrix `1 - ξ S^{(B)}`, and `S^{(B)}` on `ZMod 3` is the constant `1/3`.  Both sides are then
finite sums of explicit complex numbers, and **neither evaluation below uses any theorem of
this file**. -/

section Sanity

theorem sum_univ_zmod_three (g : ZMod 3 → ℂ) : ∑ x : ZMod 3, g x = g 0 + g 1 + g 2 := by
  have h : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

theorem sum_loopArg_three_one (g : LoopArg 3 1 → ℂ) :
    ∑ b : LoopArg 3 1, g b = g (fun _ => 0) + g (fun _ => 1) + g (fun _ => 2) := by
  rw [← (Equiv.funUnique (Fin 1) (ZMod 3)).symm.sum_comp g, sum_univ_zmod_three]
  rfl

theorem SB_three_apply (x y : ZMod 3) : SB 3 x y = (3 : ℂ)⁻¹ := by
  rw [SB_apply, sbKernel, ite_eq_left (by revert x y; decide)]

theorem prod_fin_one_add_one {M : Type*} [CommMonoid M] (f : Fin (1 + 1) → M) :
    ∏ i, f i = f 0 * f 1 := Fin.prod_univ_two f

theorem append_one_zero {α : Type*} (f g : Fin 1 → α) :
    Fin.append f g (0 : Fin (1 + 1)) = f 0 := by
  simp [Fin.append, Fin.addCases]

theorem append_one_one {α : Type*} (f g : Fin 1 → α) :
    Fin.append f g (1 : Fin (1 + 1)) = g 0 := by
  simp [Fin.append, Fin.addCases]

/-- The `ZMod 3` disequalities the evaluations below need. -/
theorem zmod_three_facts :
    ((1 : ZMod 3) ≠ 0) ∧ ((2 : ZMod 3) ≠ 0) ∧ ((0 : ZMod 3) ≠ 1) ∧ ((0 : ZMod 3) ≠ 2) ∧
      ((1 : ZMod 3) ≠ 2) ∧ ((2 : ZMod 3) ≠ 1) := by decide

/-- The edge factor of (5.17) at `t = 0`: `Θ_0 = 1`, so it is `1 - (s ξ) S^{(B)}`. -/
theorem edgeKer_three_zero (ξ s : ℂ) (x y : ZMod 3) :
    edgeKer 3 ξ s 0 x y = (if x = y then (1 : ℂ) else 0) - s * ξ / 3 := by
  rw [edgeKer, zero_mul, Theta_zero, Matrix.mul_one]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, SB_three_apply]
  ring_nf

/-- The single edge parameter of the check: `ξ = i` (genuinely non-real, so the conjugation of
the second half is visible). -/
noncomputable def sanityXi : Fin 1 → ℂ := fun _ => Complex.I

/-- The single coordinate family of the check: `E(0) = 1`, `E(1) = E(2) = i`. -/
noncomputable def sanityEf : Fin 1 → LoopArg 3 1 → ℂ :=
  fun _ b => if b 0 = 0 then 1 else Complex.I

/-- `a = (0)`. -/
def sanityA : LoopArg 3 1 := fun _ => 0

/-- `a' = (1)`, so that the check is genuinely off-diagonal. -/
def sanityA' : LoopArg 3 1 := fun _ => 1

theorem sanity_Uker_A :
    Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf 0) sanityA
      = 5 / 3 - Complex.I / 3 := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [Uker, sum_loopArg_three_one]
  simp only [Fin.prod_univ_one, sanityXi, sanityA, sanityEf, Complex.ofReal_one,
    Complex.ofReal_zero, edgeKer_three_zero, h10, h20, h01, h02]
  norm_num [Complex.ext_iff, map_ofNat]

theorem sanity_Uker_A' :
    Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf 0) sanityA'
      = 2 / 3 + (2 / 3) * Complex.I := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [Uker, sum_loopArg_three_one]
  simp only [Fin.prod_univ_one, sanityXi, sanityA', sanityEf, Complex.ofReal_one,
    Complex.ofReal_zero, edgeKer_three_zero, h10, h20, h12]
  norm_num [Complex.ext_iff, map_ofNat]

/-- The left side of the bilinear identity at the sanity point, computed from scratch. -/
theorem sanity_lhs :
    ∑ α : Fin 1, Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA
        * (starRingEnd ℂ) (Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA')
      = 8 / 9 - (4 / 3) * Complex.I := by
  rw [Fin.sum_univ_one, sanity_Uker_A, sanity_Uker_A']
  norm_num [Complex.ext_iff, map_ofNat]

/-- The right side of the bilinear identity at the sanity point, computed from scratch. -/
theorem sanity_rhs :
    Uker 3 (Fin.append sanityXi (fun i => (starRingEnd ℂ) (sanityXi i)))
        ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        (fun c => ∑ α : Fin 1, sanityEf α (SumZeroDyn.spl1 3 c)
          * (starRingEnd ℂ) (sanityEf α (SumZeroDyn.spl2 3 c)))
        (Fin.append sanityA sanityA')
      = 8 / 9 - (4 / 3) * Complex.I := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [Uker, SumZeroDyn.sum_append 3]
  simp only [sum_loopArg_three_one, prod_fin_one_add_one, SumZeroDyn.spl1_append,
    SumZeroDyn.spl2_append, Fin.sum_univ_one, append_one_zero, append_one_one,
    sanityXi, sanityA, sanityA', sanityEf, Complex.conj_I, Complex.ofReal_one,
    Complex.ofReal_zero, edgeKer_three_zero, h10, h20, h01, h02, h12]
  norm_num [Complex.ext_iff, map_ofNat]

/-- **The check**: the two sides agree, and the common value is nonzero — the off-diagonal
witness `a ≠ a'` demanded by the satisfiability discipline. -/
theorem sanity_lhs_eq_rhs :
    (∑ α : Fin 1, Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA
        * (starRingEnd ℂ) (Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA'))
      = Uker 3 (Fin.append sanityXi (fun i => (starRingEnd ℂ) (sanityXi i)))
          ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
          (fun c => ∑ α : Fin 1, sanityEf α (SumZeroDyn.spl1 3 c)
            * (starRingEnd ℂ) (sanityEf α (SumZeroDyn.spl2 3 c)))
          (Fin.append sanityA sanityA') := by
  rw [sanity_lhs, sanity_rhs]

/-- **The satisfiability witness for `RBM.EEUker.sum_Uker_mul_conj_Uker`**: at the sanity
point the two hypotheses hold (`3 ≤ 3` and `‖0 · i‖ < 1`), and running the theorem forwards
reproduces the value computed independently in `RBM.EEUker.sanity_rhs`.  Together with
`RBM.EEUker.sanity_lhs` this is the check that the identity is *true*, not merely provable
from an unsatisfiable hypothesis. -/
theorem sanity_instance_of_theorem :
    (∑ α : Fin 1, Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA
        * (starRingEnd ℂ) (Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA'))
      = 8 / 9 - (4 / 3) * Complex.I := by
  rw [sum_Uker_mul_conj_Uker 3 (by norm_num) (ξ := sanityXi) (s := (1 : ℝ)) (t := (0 : ℝ))
    (by intro i; simp [sanityXi]) sanityEf sanityA sanityA']
  exact sanity_rhs

theorem sanity_value_ne_zero : (8 / 9 - (4 / 3) * Complex.I) ≠ 0 := by
  simp [Complex.ext_iff]

/-- The diagonal witness `a = a'`: both sides evaluate to `26/9 ≠ 0`, which is the value the
quadratic variation of `Ψ₁` takes at the sanity point. -/
theorem sanity_lhs_diag :
    ∑ α : Fin 1, Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA
        * (starRingEnd ℂ) (Uker 3 sanityXi ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) (sanityEf α) sanityA)
      = 26 / 9 := by
  rw [Fin.sum_univ_one, sanity_Uker_A]
  norm_num [Complex.ext_iff, map_ofNat]

theorem sanity_rhs_diag :
    Uker 3 (Fin.append sanityXi (fun i => (starRingEnd ℂ) (sanityXi i)))
        ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        (fun c => ∑ α : Fin 1, sanityEf α (SumZeroDyn.spl1 3 c)
          * (starRingEnd ℂ) (sanityEf α (SumZeroDyn.spl2 3 c)))
        (Fin.append sanityA sanityA)
      = 26 / 9 := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [Uker, SumZeroDyn.sum_append 3]
  simp only [sum_loopArg_three_one, prod_fin_one_add_one, SumZeroDyn.spl1_append,
    SumZeroDyn.spl2_append, Fin.sum_univ_one, append_one_zero, append_one_one,
    sanityXi, sanityA, sanityEf, Complex.conj_I, Complex.ofReal_one,
    Complex.ofReal_zero, edgeKer_three_zero, h10, h20, h01, h02]
  norm_num [Complex.ext_iff, map_ofNat]

/-- **The check discriminates**: repeating `ξ` on the second half — which is what
`RBM.SumZeroDyn.xi2` did **before T223** — gives a *different* number at the same point, so the
conjugation the repaired `RBM.SumZeroDyn.xi2` carries is not a cosmetic choice.  (`sanityXi` is
`ξ = i`, so `Fin.append sanityXi sanityXi` is literally the old definition body at this point,
while `Fin.append sanityXi (conj ∘ sanityXi)` — used in `RBM.EEUker.sanity_rhs` — is the new
one.) -/
theorem sanity_rhs_xi2_wrong :
    Uker 3 (Fin.append sanityXi sanityXi) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        (fun c => ∑ α : Fin 1, sanityEf α (SumZeroDyn.spl1 3 c)
          * (starRingEnd ℂ) (sanityEf α (SumZeroDyn.spl2 3 c)))
        (Fin.append sanityA sanityA')
      ≠ 8 / 9 - (4 / 3) * Complex.I := by
  obtain ⟨h10, h20, h01, h02, h12, h21⟩ := zmod_three_facts
  rw [Uker, SumZeroDyn.sum_append 3]
  simp only [sum_loopArg_three_one, prod_fin_one_add_one, SumZeroDyn.spl1_append,
    SumZeroDyn.spl2_append, Fin.sum_univ_one, append_one_zero, append_one_one,
    sanityXi, sanityA, sanityA', sanityEf, Complex.ofReal_one,
    Complex.ofReal_zero, edgeKer_three_zero, h10, h20, h01, h02, h12]
  norm_num [Complex.ext_iff, map_ofNat]

end Sanity

end EEUker

end RBM

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridStepDecompC
import RBM1D.Gauss.EEUker
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Gauss.LoopDecayFixed
import RBM1D.Gauss.Q716Pointwise
import RBM1D.Hierarchy.EEBridge
import RBM1D.Flow.Initial

/-!
# The Hermitian `E ⊗ E` tensor: loop expansion, joint decay, (5.81), (5.105)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2 (5.22)–(5.25), §5.4 (5.74)–(5.81), §5.5 (5.93), (5.103)–(5.105), for the
Hermitian tensor `RBM.Gauss.Grid.eeHerm` (`eeHerm Φ b b' M = vH (gradMat Φ_b M) (gradMat Φ_b' M)`,
conjugation on the second slot) and the complex conditional variance `vC`.

## Route

* `gradMat (loopObs I) M = −∑_k R_k` (`gradMat_loopObs`): `gradMat` is the transposed `wirtFirst`,
  and `RBM.Gauss.wirtFirst_loopObs_eq` holds for Hermitian `M`, `Im z ≠ 0`, well-formed `I`
  — no reality hypothesis, no `emart`.
* `vH A A' = ∑_{i,j} S_ij A_ij conj A'_ij` (`vH_eq_sum_Sblk`, the coordinate identity).
* (5.22) `sum_Sblk_mul_conj` and the two-chain gluing `RBM.EEBridge.glueLoop_prodList` give the
  `(2n+2)`-loops `glueIdx2 I I' k k' β β'`, cross terms `k ≠ k'` included.

## Main results

* `eeHerm_eq_loop` (a sum of `n² L²` loop terms); `eeHerm_linComb` (any `Q`), `eeHerm_Qop_eq_QQ`
  (`Q_t` real at real `t`).
* `fastDecay_eeHerm`, `eeHerm_fastDecay`: joint fast decay of the `2n`-tensor on `decaySet`.
* `norm_eeHerm_le`, `eeHerm_le` ((5.81)).
* `vC_sum_ukerMatC_eq` (the quadratic variation is `(U_σ ⊗ U_σ̄) ∘ T` at `(a,a)`, doubled
  edge vector `(ξ, ξ̄)`); `qv_kernel_le_sumZero`, `qv_kernel_le_nonAlt` (one application of
  Lemma 7.3 at length `2n`); `scale_ratio_pow`, `W_mul_ell_div_scale_le` ((5.93));
  `qv_contraction_le_sumZero`, `qv_contraction_le_nonAlt`, and the grid form
  `step_mul_vC_AbC_le_nonAlt`.

## Deviations

* `norm_eeHerm_le` carries the decay set of Definition 5.8 as an input: the paper's `ℓ_u` in (5.81)
  comes from summing a label "restricted to a range `ℓ_u`" by Lemma 5.9's decay. With the Ξ-bound
  alone the factor would be `L`.
* The kernel theorems are the general-`ξ` lemmas `RBM.norm_Uker_fastDecay_le_sumZero` /
  `RBM.norm_Uker_fastDecay_le_short` (which `Q716.uker_decay_le_sumZero` / `uker_decay_le_nonAlt`
  specialise), because the doubled vector is `(ξ, ξ̄)` (Lemma 5.5), which is `xiOf (σ,σ)` only for
  real `ξ`.
* As in `Q716Pointwise.lean`, the `W^{-D}` tails are kept explicit
  (`n² W L W^{-D}`, `qqErr`, and the exponentially small `qqCoefTail`), not a bare `W^{-D+C}`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory Filter Matrix RBM
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-! ### 1. `vH` in matrix entries -/

section Coord

variable {d : Dims} {N : ℕ}

/-- The raw coordinate direction `Xmat(e_c)` at `c = crd p`: `Bmat p` on a used coordinate,
`0` otherwise. -/
theorem Xmat_single_crd (p : d.Idx N × d.Idx N × Bool) :
    Xmat d N (Pi.single (crd d N p) 1)
      = if p ∈ usedCoord d N then Bmat d N p.1 p.2.1 p.2.2 else 0 := by
  classical
  rw [Xmat_eq_sum]
  split_ifs with hp
  · rw [Finset.sum_eq_single p]
    · rw [Pi.single_apply, if_pos rfl, one_smul]
    · intro q _ hqp
      have hne : crd d N q ≠ crd d N p := fun he => hqp (crd_injective d N he)
      rw [Pi.single_apply, if_neg hne, zero_smul]
    · intro hpn
      exact absurd hp hpn
  · refine Finset.sum_eq_zero fun q hq => ?_
    have hne : crd d N q ≠ crd d N p := fun he => hp (crd_injective d N he ▸ hq)
    rw [Pi.single_apply, if_neg hne, zero_smul]

/-- **The coordinate identity behind `eeHerm`**: for arbitrary matrices,
`vH N A A' = ∑_{i,j} S_ij · A_ij · conj (A'_ij)`, the sum over **ordered** pairs.

The two off-diagonal coordinates of a pair `idxKey i < idxKey j` carry `S_ij/2` each and read
`A_ji + A_ij` resp. `i A_ji − i A_ij`; together they give `S_ij (A_ij conj A'_ij + A_ji conj A'_ji)`.
The diagonal real coordinate gives `S_ii A_ii conj A'_ii`; all other raw coordinates read `0`. -/
theorem vH_eq_sum_Sblk (A A' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    vH N A A' = ∑ i : d.Idx N, ∑ j : d.Idx N,
      (Sblk (d.L N) (d.W N) i j : ℂ) * A i j * conj (A' i j) := by
  classical
  set F : d.Idx N → d.Idx N → ℂ := fun i j =>
    (Sblk (d.L N) (d.W N) i j : ℂ) * A i j * conj (A' i j) with hF
  set g : d.Idx N × d.Idx N × Bool → ℂ := fun p =>
    ((gvar d (crd d N p) : ℝ) : ℂ) * Matrix.trace (A * Xmat d N (Pi.single (crd d N p) 1))
      * conj (Matrix.trace (A' * Xmat d N (Pi.single (crd d N p) 1))) with hg
  have hre : vH N A A' = ∑ p : d.Idx N × d.Idx N × Bool, g p := by
    unfold vH coordFinset
    rw [Finset.sum_map]
    rfl
  -- the two tags of a pair
  have hpair : ∀ i j : d.Idx N, g (i, j, true) + g (i, j, false)
      = (if idxKey d N i < idxKey d N j then F i j + F j i else 0)
        + (if i = j then F i i else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      have hu : ∀ b : Bool, (i, j, b) ∈ usedCoord d N := fun b => mem_usedCoord.2 (Or.inl h)
      have htr : ∀ (B : Matrix (d.Idx N) (d.Idx N) ℂ) (b : Bool),
          Matrix.trace (B * Xmat d N (Pi.single (crd d N (i, j, b)) 1))
            = (if b then (1 : ℂ) else Complex.I) * B j i
              + (if b then (1 : ℂ) else -Complex.I) * B i j := by
        intro B b
        rw [Xmat_single_crd, if_pos (hu b), Matrix.trace_mul_comm]
        exact trace_Bmat_mul_of_ne hij b B
      have hgv : ∀ b : Bool, ((gvar d (crd d N (i, j, b)) : ℝ) : ℂ)
          = (Sblk (d.L N) (d.W N) i j : ℂ) / 2 := by
        intro b
        rw [gvar_crd, if_neg hij]
        push_cast
        ring
      rw [if_pos h, if_neg hij, add_zero]
      simp only [hg, htr, hgv, hF, if_true, Bool.false_eq_true, if_false, one_mul]
      rw [Sblk_comm (d.L N) (d.W N) j i]
      simp only [map_add, map_mul, map_neg, Complex.conj_I]
      linear_combination (-((Sblk (d.L N) (d.W N) i j : ℂ) / 2) * (A j i - A i j)
        * (conj (A' j i) - conj (A' i j))) * Complex.I_sq
    · subst h
      have hu : (i, i, true) ∈ usedCoord d N := mem_usedCoord.2 (Or.inr ⟨rfl, rfl⟩)
      have hnu : (i, i, false) ∉ usedCoord d N := by
        rw [mem_usedCoord]
        rintro (h | h)
        · exact lt_irrefl _ h
        · exact Bool.false_ne_true h.2
      have h1 : g (i, i, false) = 0 := by
        simp only [hg]
        rw [Xmat_single_crd, if_neg hnu]
        simp
      have h2 : g (i, i, true) = F i i := by
        simp only [hg, hF]
        rw [Xmat_single_crd, if_pos hu, Matrix.trace_mul_comm, trace_Bmat_mul_diag,
          Matrix.trace_mul_comm, trace_Bmat_mul_diag, gvar_crd, if_pos rfl]
      rw [h1, h2, if_neg (lt_irrefl _), if_pos rfl]
      ring
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      have hnu : ∀ b : Bool, (i, j, b) ∉ usedCoord d N := by
        intro b hb
        rcases mem_usedCoord.1 hb with h' | h'
        · exact lt_asymm h h'
        · exact hij h'.1
      have h0 : ∀ b : Bool, g (i, j, b) = 0 := by
        intro b
        simp only [hg]
        rw [Xmat_single_crd, if_neg (hnu b)]
        simp
      rw [h0, h0, if_neg (lt_asymm h), if_neg hij]
  have hsum : ∑ p : d.Idx N × d.Idx N × Bool, g p
      = ∑ i : d.Idx N, ∑ j : d.Idx N, (g (i, j, true) + g (i, j, false)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
  rw [hre, hsum]
  simp only [hpair]
  -- trichotomy
  have hswap : ∑ i : d.Idx N, ∑ j : d.Idx N,
      (if idxKey d N i < idxKey d N j then F j i else 0)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, (if idxKey d N j < idxKey d N i then F i j else 0) :=
    Finset.sum_comm
  have hsplit : ∀ i j : d.Idx N,
      (if idxKey d N i < idxKey d N j then F i j + F j i else 0) + (if i = j then F i i else 0)
        = ((if idxKey d N i < idxKey d N j then F i j else 0)
          + (if i = j then F i i else 0))
          + (if idxKey d N i < idxKey d N j then F j i else 0) := by
    intro i j
    split_ifs <;> ring
  set X : d.Idx N → d.Idx N → ℂ := fun i j =>
    (if idxKey d N i < idxKey d N j then F i j else 0) + (if i = j then F i i else 0) with hX
  have hstep : ∑ i : d.Idx N, ∑ j : d.Idx N,
      ((if idxKey d N i < idxKey d N j then F i j + F j i else 0) + (if i = j then F i i else 0))
      = ∑ i : d.Idx N, ∑ j : d.Idx N, X i j + ∑ i : d.Idx N, ∑ j : d.Idx N,
          (if idxKey d N i < idxKey d N j then F j i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hsplit i j
  rw [hstep, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hX]
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [if_pos h, if_neg (fun he : i = j => absurd (he ▸ h) (lt_irrefl _)), if_neg (lt_asymm h)]
    simp only [hF]
    ring
  · subst h
    rw [if_neg (lt_irrefl _), if_pos rfl]
    simp only [hF]
    ring
  · rw [if_neg (lt_asymm h), if_neg (fun he : i = j => absurd (he ▸ h) (lt_irrefl _)), if_pos h]
    simp only [hF]
    ring

/-- `vH` is invariant under negating both arguments. -/
theorem vH_neg_neg (A A' : Matrix (d.Idx N) (d.Idx N) ℂ) : vH N (-A) (-A') = vH N A A' := by
  unfold vH
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_neg, map_neg]
  ring

end Coord

/-! ### 2. `gradMat` of loop observables and of linear combinations -/

section GradMatLoop

variable {d : Dims} {N : ℕ}

/-- `gradMat` depends on `Φ` only through `fderiv ℝ Φ M`. -/
theorem gradMat_congr_fderiv {Φ Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (h : fderiv ℝ Φ M = fderiv ℝ Ψ M) :
    gradMat Φ M = gradMat Ψ M := by
  ext i j
  simp only [gradMat, Matrix.of_apply, wirtFirst, coordD1, h]

/-- Subtracting a deterministic constant (the `K`-part of `L − K`) does not change `gradMat`. -/
theorem gradMat_sub_const (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (c : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    gradMat (fun M' => Φ M' - c) M = gradMat Φ M :=
  gradMat_congr_fderiv (fderiv_sub_const c)

/-- **`gradMat` is `ℂ`-linear** on functions differentiable at `M`. -/
theorem gradMat_linComb {ι : Type*} (s : Finset ι) (q : ι → ℂ)
    (Φ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (Φ i) M) :
    gradMat (fun M' => ∑ i ∈ s, q i * Φ i M') M = ∑ i ∈ s, q i • gradMat (Φ i) M := by
  have hfd : fderiv ℝ (fun M' => ∑ i ∈ s, q i * Φ i M') M = ∑ i ∈ s, q i • fderiv ℝ (Φ i) M := by
    rw [fderiv_fun_sum fun i hi => (h i hi).const_mul (q i)]
    exact Finset.sum_congr rfl fun i hi => fderiv_const_mul (h i hi) (q i)
  ext a b
  simp only [gradMat, Matrix.of_apply, wirtFirst, coordD1, hfd, Matrix.sum_apply,
    Matrix.smul_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **The gradient of a loop observable** is minus the sum of its cut blocks:
`gradMat (L_{σ,a}) M = −∑_k R_k`, `R_k = loopCut M z I k`. This is `wirtFirst_loopObs_eq`
(`LoopLeibniz.lean`) read through the transposition in the definition of `gradMat`; no reality
hypothesis is involved. -/
theorem gradMat_loopObs {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    gradMat (loopObs d N z I) M
      = -∑ k ∈ Finset.range I.a.length, loopCut (d.L N) (d.W N) M z I k := by
  ext i j
  rw [gradMat, Matrix.of_apply, wirtFirst_loopObs_eq hz hM hwf j i, Matrix.neg_apply,
    Matrix.sum_apply]

end GradMatLoop

/-! ### 3. Gluing with two independent cut edges `k`, `k'` -/

section Glue2

variable {L : ℕ}

/-- **The glued `(2n+2)`-loop with independent cut edges.** Cut the `k`-th `G` edge of `I` and
the `k'`-th `G` edge of `I'`, reverse and flip the second chain, and close the two new ends with
`E_b` and `E_{b'}`. For `k = k'` this is `RBM.EEBridge.glueIdx`; the terms
`k ≠ k'` are the cross terms of the full Hermitian tensor `eeHerm`, absent from the paper's
`(E ⊗ E)^{(k)}` blocks of (5.22). -/
def glueIdx2 (I I' : LoopIdx (ZMod L)) (k k' : ℕ) (b b' : ZMod L) : LoopIdx (ZMod L) :=
  EEBridge.ofPairs (EEBridge.cutPairs I k ++ ((EEBridge.pairAt I k).1, b) ::
    EEBridge.rflip (!(EEBridge.pairAt I' k').1) (EEBridge.cutPairs I' k') b')

theorem glueIdx2_wf (I I' : LoopIdx (ZMod L)) (k k' : ℕ) (b b' : ZMod L) :
    (glueIdx2 I I' k k' b b').WF := EEBridge.ofPairs_wf _

theorem glueIdx2_length {I I' : LoopIdx (ZMod L)} (hI : I.WF) (hI' : I'.WF) {n n' k k' : ℕ}
    (hn : I.length = n) (hn' : I'.length = n') (hk : k < n) (hk' : k' < n') (b b' : ZMod L) :
    (glueIdx2 I I' k k' b b').length = n + n' + 2 := by
  rw [glueIdx2, EEBridge.ofPairs_length, List.length_append, List.length_cons,
    EEBridge.rflip_length, EEBridge.cutPairs_length hI (by omega),
    EEBridge.cutPairs_length hI' (by omega), hn, hn']
  omega

theorem mem_glueIdx2 (I I' : LoopIdx (ZMod L)) (k k' : ℕ) (b b' : ZMod L) :
    b ∈ (glueIdx2 I I' k k' b b').a := by
  simp [glueIdx2]

/-- The label `a_k` of the cut edge of `I` occurs in every glued loop, independently of `b, b'`. -/
theorem anchor_mem_glueIdx2 (I I' : LoopIdx (ZMod L)) (k k' : ℕ) (b b' : ZMod L) :
    (EEBridge.pairAt I k).2 ∈ (glueIdx2 I I' k k' b b').a := by
  have := EEBridge.anchor_mem_cutPairs I k
  simp only [glueIdx2, EEBridge.ofPairs_a, List.map_append, List.mem_append]
  exact Or.inl this

/-- **Every label of either factor occurs in the glued loop** (this is what carries the decay of
the `G`-loops through the gluing, for the joint `2n`-tensor). -/
theorem mem_glueIdx2_of_mem {I I' : LoopIdx (ZMod L)} (hI : I.WF) (hI' : I'.WF) {k k' : ℕ}
    (hk : k < I.length) (hk' : k' < I'.length) (b b' : ZMod L) {x : ZMod L}
    (hx : x ∈ I.a ∨ x ∈ I'.a) : x ∈ (glueIdx2 I I' k k' b b').a := by
  rw [glueIdx2, EEBridge.ofPairs_a, List.map_append]
  rcases hx with hx | hx
  · exact List.mem_append.2 (Or.inl (FastDecayFlow.mem_cutPairs_of_mem hI hk hx))
  · refine List.mem_append.2 (Or.inr ?_)
    rw [List.map_cons]
    exact List.mem_cons_of_mem _
      (FastDecayFlow.mem_rflip _ _ (Or.inl (FastDecayFlow.mem_cutPairs_of_mem hI' hk' hx)))

end Glue2

/-! ### 4. (T1) `eeHerm` as an explicit combination of `(2n+2)`-loops -/

section EEHermLoop

variable {d : Dims} {N : ℕ}

/-- The gluing identity (5.22) for two arbitrary matrices, in `(i,j)` order. -/
theorem sum_Sblk_mul_conj' (R R' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ) * R i j * conj (R' i j)
      = (d.W N : ℂ) * ∑ β : ZMod (d.L N), ∑ β' : ZMod (d.L N),
          SB (d.L N) β β' * glueLoop (d.L N) (d.W N) R R' β β' := by
  rw [← sum_Sblk_mul_conj, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Sblk_comm (d.L N) (d.W N) j i]
  ring

/-- `vH` of two matrices is the `S^{(B)}`-weighted glued trace (5.22). -/
theorem vH_eq_glue (R R' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    vH N R R' = (d.W N : ℂ) * ∑ β : ZMod (d.L N), ∑ β' : ZMod (d.L N),
      SB (d.L N) β β' * glueLoop (d.L N) (d.W N) R R' β β' := by
  rw [vH_eq_sum_Sblk, sum_Sblk_mul_conj']

/-- `vH` is additive in its first slot. -/
theorem vH_finsetSum_left {κ : Type*} (s : Finset κ) (R : κ → Matrix (d.Idx N) (d.Idx N) ℂ)
    (A' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    vH N (∑ k ∈ s, R k) A' = ∑ k ∈ s, vH N (R k) A' := by
  unfold vH
  simp only [Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- `vH` is additive in its second slot. -/
theorem vH_finsetSum_right {κ : Type*} (s : Finset κ) (A : Matrix (d.Idx N) (d.Idx N) ℂ)
    (R' : κ → Matrix (d.Idx N) (d.Idx N) ℂ) :
    vH N A (∑ k ∈ s, R' k) = ∑ k ∈ s, vH N A (R' k) := by
  unfold vH
  simp only [Matrix.sum_mul, Matrix.trace_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- The glued trace of two cut blocks with independent cut edges is the `(2n+2)`-loop of
`glueIdx2` (Hermitian `M`: `G(σ)ᴴ = G(!σ)` at the same `z`). -/
theorem glueLoop_loopCut2 {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (I I' : LoopIdx (ZMod (d.L N))) (k k' : ℕ) (β β' : ZMod (d.L N)) :
    glueLoop (d.L N) (d.W N) (loopCut (d.L N) (d.W N) M z I k)
        (loopCut (d.L N) (d.W N) M z I' k') β β'
      = gloop (d.L N) (d.W N) M z (glueIdx2 I I' k k' β β') := by
  rw [EEBridge.loopCut_eq, EEBridge.loopCut_eq, EEBridge.glueLoop_prodList hM, glueIdx2]

/-- **`eeHerm_eq_loop`.** For the label family `Φ_b = L_{I_b} − K_b` (loop observables at
`z`, minus deterministic constants — the paper's `(L − K)_{u,σ,b}`), at a Hermitian `M`,

`eeHerm Φ b b' M = W ∑_{k<|I_b|} ∑_{k'<|I_{b'}|} ∑_{β,β'} S^{(B)}_{ββ'} L_{glueIdx2 (I_b) (I_{b'}) k k' β β'}(M)`,

every summand a `(|I_b| + |I_{b'}| + 2)`-loop (`glueIdx2_length`); the cross terms `k ≠ k'` are
included. The number of summands is `|I_b|·|I_{b'}|·L²`. The only
hypotheses are those of `RBM.Gauss.wirtFirst_loopObs_eq`; no reality hypothesis. -/
theorem eeHerm_eq_loop {ι : Type*} {z : ℂ} (hz : z.im ≠ 0) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (I : ι → LoopIdx (ZMod (d.L N))) (hI : ∀ b, (I b).WF) (Kc : ι → ℂ)
    (b b' : ι) :
    eeHerm (fun b M' => loopObs d N z (I b) M' - Kc b) b b' M
      = (d.W N : ℂ) * ∑ k ∈ Finset.range (I b).a.length, ∑ k' ∈ Finset.range (I b').a.length,
          ∑ β : ZMod (d.L N), ∑ β' : ZMod (d.L N),
            SB (d.L N) β β' * gloop (d.L N) (d.W N) M z (glueIdx2 (I b) (I b') k k' β β') := by
  simp only [eeHerm]
  rw [gradMat_sub_const, gradMat_sub_const, gradMat_loopObs hz (hI b) hM,
    gradMat_loopObs hz (hI b') hM, vH_neg_neg, vH_finsetSum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vH_finsetSum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [vH_eq_glue]
  simp only [glueLoop_loopCut2 hM]

/-- **`eeHerm` of a `Q`-transformed family** (e.g. `Q_u ∘ (L − K)`): for any finite matrix `Q`
and a family differentiable at `M`,
`eeHerm (QΦ) b b' = ∑_{c,c'} Q_{bc} conj(Q_{b'c'}) eeHerm Φ c c'`. -/
theorem eeHerm_linComb {ι κ : Type*} [Fintype κ] (Q : ι → κ → ℂ)
    (Φ : κ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hΦ : ∀ c, DifferentiableAt ℝ (Φ c) M) (b b' : ι) :
    eeHerm (fun b M' => ∑ c : κ, Q b c * Φ c M') b b' M
      = ∑ c : κ, ∑ c' : κ, Q b c * conj (Q b' c') * eeHerm Φ c c' M := by
  simp only [eeHerm]
  rw [gradMat_linComb Finset.univ (Q b) Φ M (fun c _ => hΦ c),
    gradMat_linComb Finset.univ (Q b') Φ M (fun c _ => hΦ c)]
  exact vH_sum N (Q b) (Q b') _ _

end EEHermLoop

/-! ### 5. (T2), (T3): joint fast decay and the (5.81) bound -/

section Bounds

variable {d : Dims} {N : ℕ}

/-- The index shift `Icc 1 n ∋ k ↦ min (k-1) (n-1) ∈ range n` of `Decay.eTens`. -/
theorem sum_Icc_clamp (n : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 n, F (min (k - 1) (n - 1)) = ∑ k ∈ Finset.range n, F k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k hk => ?_
  have hk' : k < n := by simpa using hk
  congr 1
  omega

/-- **`eeHerm` as `n` copies of the abstract `E ⊗ E` of (5.22)**, one for each cut edge `k'` of
the second loop: for fixed `k'`, the gluing `J_{k'} k β β' = glueIdx2 I I' (k-1) k' β β'` has the
three properties `RBM.Decay.norm_eTens_le` asks for. -/
theorem eeHerm_eq_sum_eTens {ι : Type*} {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (I : ι → LoopIdx (ZMod (d.L N)))
    (hI : ∀ b, (I b).WF) (Kc : ι → ℂ) {n : ℕ} (hlen : ∀ b, (I b).length = n) (b b' : ι) :
    eeHerm (fun b M' => loopObs d N z (I b) M' - Kc b) b b' M
      = ∑ k' ∈ Finset.range n, Decay.eTens (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) n
          (fun k β β' => glueIdx2 (I b) (I b') (min (k - 1) (n - 1)) k' β β') := by
  have h : ∀ c, (I c).a.length = n := fun c => hlen c
  rw [eeHerm_eq_loop hz hM I hI Kc b b', h b, h b', Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  have hF := sum_Icc_clamp n (fun k => ∑ β : ZMod (d.L N), ∑ β' : ZMod (d.L N),
    SB (d.L N) β β' * gloop (d.L N) (d.W N) M z (glueIdx2 (I b) (I b') k k' β β'))
  beta_reduce at hF
  simp only [Decay.eTens]
  rw [hF]

/-- **(T3), deterministic core — (5.81) for the full Hermitian tensor.** If every `G`-loop of
length `2n+2` is at most `Φ A^{-(2n+1)}` (i.e. `Ξ^{(L)}_{2n+2} ≤ Φ`, (5.76)) and the `G`-loops
of length `2n+2` have the `(ℓ, δ)` decay of Definition 5.8, then
`‖eeHerm_{b,b'}‖ ≤ n · (2e n Φ (W(ℓ+1)/A) A^{-2n} + n W L δ)`.
The factor `ℓ + 1` is the paper's `ℓ_u` ("all `ℓ_u` factors come from summing an index restricted
to a range `ℓ_u`"); the extra factor `n` counts the second cut edge `k'` (cross terms). -/
theorem norm_eeHerm_le {ι : Type*} {z : ℂ} (hz : z.im ≠ 0) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (I : ι → LoopIdx (ZMod (d.L N))) (hI : ∀ b, (I b).WF) (Kc : ι → ℂ)
    {n : ℕ} (hn1 : 1 ≤ n) (hlen : ∀ b, (I b).length = n) {A ℓ δ Φ : ℝ} (hA : 1 ≤ A)
    (hℓ : 0 < ℓ) (hδ : 0 ≤ δ)
    (hY : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length = 2 * n + 2 →
      ‖gloop (d.L N) (d.W N) M z J‖ ≤ Φ * A⁻¹ ^ (2 * n + 1))
    (hYd : Decay.LoopDecay (d.L N) (2 * n + 2) ℓ δ (gloop (d.L N) (d.W N) M z)) (b b' : ι) :
    ‖eeHerm (fun b M' => loopObs d N z (I b) M' - Kc b) b b' M‖
      ≤ n * (2 * Real.exp 1 * n * Φ * ((d.W N : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ (2 * n)
        + n * (d.W N : ℝ) * (d.L N : ℝ) * δ) := by
  rw [eeHerm_eq_sum_eTens hz hM I hI Kc hlen b b']
  refine (norm_sum_le _ _).trans ?_
  have hclamp : ∀ k : ℕ, min (k - 1) (n - 1) < n := fun k => by
    have : min (k - 1) (n - 1) ≤ n - 1 := min_le_right _ _
    omega
  have key : ∀ k' ∈ Finset.range n,
      ‖Decay.eTens (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) n
          (fun k β β' => glueIdx2 (I b) (I b') (min (k - 1) (n - 1)) k' β β')‖
        ≤ 2 * Real.exp 1 * n * Φ * ((d.W N : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ (2 * n)
          + n * (d.W N : ℝ) * (d.L N : ℝ) * δ := by
    intro k' hk'
    have hk'n : k' < n := Finset.mem_range.1 hk'
    refine Decay.norm_eTens_le (d.L N) (d.three_le_L N) (d.W N) n hA hℓ hδ
      (fun k β β' => ⟨glueIdx2_wf _ _ _ _ _ _, ?_⟩)
      (fun k β β' => mem_glueIdx2 _ _ _ _ _ _)
      (fun k => ⟨(EEBridge.pairAt (I b) (min (k - 1) (n - 1))).2,
        fun β β' => anchor_mem_glueIdx2 _ _ _ _ _ _⟩) hY hYd
    rw [glueIdx2_length (hI b) (hI b') (hlen b) (hlen b') (hclamp k) hk'n]
    ring
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **(T2), deterministic core — joint fast decay (7.13) of the `2n`-tensor `eeHerm`.** With the
`(ℓ, δ)` decay of the `G`-loops of length `2n+2`, the tensor
`c ↦ eeHerm Φ (c_{1..n}) (c_{n+1..2n})` on `LoopArg L (n+n)` is `(ℓ, n·W n L δ)`-fast-decaying:
a far pair anywhere in `c` — inside `b`, inside `b'`, or straddling them — is a far pair of every
glued loop. -/
theorem fastDecay_eeHerm {n : ℕ} (σ : Fin n → Bool) {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (Kc : LoopArg (d.L N) n → ℂ)
    {ℓ δ : ℝ} (hYd : Decay.LoopDecay (d.L N) (2 * n + 2) ℓ δ (gloop (d.L N) (d.W N) M z)) :
    FastDecay (d.L N) ℓ (n * ((d.W N : ℝ) * n * ((d.L N : ℝ) * δ)))
      (fun c : LoopArg (d.L N) (n + n) =>
        eeHerm (fun b M' => loopObs d N z (toIdx σ b) M' - Kc b)
          (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M) := by
  intro c hc
  obtain ⟨i, j, hij⟩ := hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd i.isLt (by omega)
    · exact h
  set I : LoopIdx (ZMod (d.L N)) := toIdx σ (SumZeroDyn.spl1 (d.L N) c) with hIdef
  set I' : LoopIdx (ZMod (d.L N)) := toIdx σ (SumZeroDyn.spl2 (d.L N) c) with hI'def
  have hIwf : I.WF := toIdx_wf _ _
  have hI'wf : I'.WF := toIdx_wf _ _
  have hIl : I.length = n := toIdx_length _ _
  have hI'l : I'.length = n := toIdx_length _ _
  have hmemI : ∀ p : Fin (n + n), c p ∈ I.a ∨ c p ∈ I'.a := by
    intro p
    refine Fin.addCases (motive := fun p => c p ∈ I.a ∨ c p ∈ I'.a) (fun p₁ => ?_)
      (fun p₂ => ?_) p
    · exact Or.inl (List.mem_ofFn.2 ⟨p₁, rfl⟩)
    · exact Or.inr (List.mem_ofFn.2 ⟨p₂, rfl⟩)
  have hclamp : ∀ k : ℕ, min (k - 1) (n - 1) < n := fun k => by
    have : min (k - 1) (n - 1) ≤ n - 1 := min_le_right _ _
    omega
  change ‖eeHerm (fun b M' => loopObs d N z (toIdx σ b) M' - Kc b)
      (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M‖ ≤ _
  rw [eeHerm_eq_sum_eTens hz hM (fun b => toIdx σ b) (fun b => toIdx_wf σ b) Kc
    (fun b => toIdx_length σ b)]
  refine (norm_sum_le _ _).trans ?_
  have key : ∀ k' ∈ Finset.range n,
      ‖Decay.eTens (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) n
          (fun k β β' => glueIdx2 I I' (min (k - 1) (n - 1)) k' β β')‖
        ≤ (d.W N : ℝ) * n * ((d.L N : ℝ) * δ) := by
    intro k' hk'
    have hk'n : k' < n := Finset.mem_range.1 hk'
    refine Decay.norm_eTens_le_of_far (d.L N) (d.three_le_L N) (d.W N) n
      (fun k β β' => ⟨glueIdx2_wf _ _ _ _ _ _, ?_⟩) hYd (fun k β β' => ?_)
    · rw [glueIdx2_length hIwf hI'wf hIl hI'l (hclamp k) hk'n]
      ring
    · have hkI : min (k - 1) (n - 1) < I.length := by rw [hIl]; exact hclamp k
      have hkI' : k' < I'.length := by rw [hI'l]; exact hk'n
      exact ⟨c i, mem_glueIdx2_of_mem hIwf hI'wf hkI hkI' β β' (hmemI i),
        c j, mem_glueIdx2_of_mem hIwf hI'wf hkI hkI' β β' (hmemI j), hij⟩
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `Ξ^{(L)}_m ≤ Φ` (`RBM.loopXi`, (5.76)) bounds every `G`-loop of length `m` by `Φ A^{-(m-1)}`. -/
theorem norm_gloop_le_of_loopXi_le {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ} {A Φ : ℝ}
    (hA : 0 < A) {m : ℕ} (hΞ : loopXi (d.L N) (d.W N) M z A m ≤ Φ)
    (J : LoopIdx (ZMod (d.L N))) (hJ : J.WF) (hlen : J.length = m) :
    ‖gloop (d.L N) (d.W N) M z J‖ ≤ Φ * A⁻¹ ^ (m - 1) := by
  have hσ : J.σ.length = m := by rw [show J.σ.length = J.a.length from hJ]; exact hlen
  refine (norm_gloop_le_loopMax J hσ hlen).trans ?_
  have hpow : 0 < A ^ (m - 1) := pow_pos hA _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpow]
  exact hΞ

/-- The decay radius `ℓ_u W^τ` of `decaySet` is positive. -/
theorem ellHat_mul_rpow_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (τ : ℝ) :
    0 < ellHat (d.L N) (u : ℂ) * (d.W N : ℝ) ^ τ := by
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hξ : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have hell : (1 : ℝ) / 2 ≤ ellHat (d.L N) (u : ℂ) := half_le_ellHat (d.L N) (d.three_le_L N) hξ
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos hW τ)

/-- **`eeHerm_fastDecay`** — on the fixed-time decay set of Definition 5.8 (`decaySet`) with loops
of length `≤ 2n+2`, the `2n`-tensor `eeHerm` of `(L − K)_{u,σ}` at `z_u` is
`(ℓ_u W^τ, n² W L W^{-D})`-fast-decaying. (`n² W L W^{-D} ≤ n² W^{-D+3}` once `L ≤ W²`.) -/
theorem eeHerm_fastDecay {E u τ D : ℝ} (hE : |E| < 2) (hu1 : u < 1) {n : ℕ}
    (σ : Fin n → Bool) (Kc : LoopArg (d.L N) n → ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (hdec : M ∈ decaySet d E N (2 * n + 2) u τ D) :
    FastDecay (d.L N) (ellHat (d.L N) (u : ℂ) * (d.W N : ℝ) ^ τ)
      ((n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D))
      (fun c : LoopArg (d.L N) (n + n) =>
        eeHerm (fun b M' => loopObs d N (zt E u) (toIdx σ b) M' - Kc b)
          (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M) := by
  have h := fastDecay_eeHerm σ (zt_im_ne_zero_of_lt_one hE hu1) hM Kc hdec
  intro c hc
  refine (h c hc).trans (le_of_eq ?_)
  ring

/-- **`eeHerm_le` — (5.81).** On `{Ξ^{(L)}_{u,2n+2}(M) ≤ Φ} ∩ decaySet` (Hermitian `M`,
scale `A ≥ 1`, e.g. `A = Wℓ_uη_u`), the full Hermitian tensor of `(L − K)_{u,σ}` satisfies
`‖eeHerm_{b,b'}‖ ≤ n (2e n Φ (W(ℓ_u W^τ + 1)/A) A^{-2n} + n W L W^{-D})`,
i.e. `≺ Ξ^{(L)}_{u,2n+2} · W ℓ_u · (Wℓ_uη_u)^{-2n-1}` with `A = Wℓ_uη_u`, `Φ = N^εΛ`, `W^τ ≺ 1`. -/
theorem eeHerm_le {E u τ D : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) {n : ℕ} (hn1 : 1 ≤ n)
    (σ : Fin n → Bool) (Kc : LoopArg (d.L N) n → ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {A Φ : ℝ} (hA : 1 ≤ A)
    (hΞ : loopXi (d.L N) (d.W N) M (zt E u) A (2 * n + 2) ≤ Φ)
    (hdec : M ∈ decaySet d E N (2 * n + 2) u τ D) (b b' : LoopArg (d.L N) n) :
    ‖eeHerm (fun b M' => loopObs d N (zt E u) (toIdx σ b) M' - Kc b) b b' M‖
      ≤ n * (2 * Real.exp 1 * n * Φ
          * ((d.W N : ℝ) * (ellHat (d.L N) (u : ℂ) * (d.W N : ℝ) ^ τ + 1) / A) * A⁻¹ ^ (2 * n)
        + n * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D)) := by
  refine norm_eeHerm_le (zt_im_ne_zero_of_lt_one hE hu1) hM (fun b => toIdx σ b)
    (fun b => toIdx_wf σ b) Kc hn1 (fun b => toIdx_length σ b) hA
    (ellHat_mul_rpow_pos hu0 hu1 τ) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun J hJ hlen => ?_) hdec b b'
  have := norm_gloop_le_of_loopXi_le (by linarith) hΞ J hJ hlen
  simpa using this

end Bounds

/-! ### 6. (T4) the joint `2n`-tensor of the quadratic variation -/

section Joint

variable {d : Dims} {N : ℕ}

/-- **The matrix of `Q_t`** (Definition 5.12): `(Q_t A)_a = ∑_b Qmat t a b · A_b`,
`Qmat t a b = δ_{ab} − 1(b₁ = a₁) ϑ_{t,a}`. -/
noncomputable def Qmat (L : ℕ) [NeZero L] {k : ℕ} (t : ℂ) (a b : LoopArg L (k + 1)) : ℂ :=
  (if b = a then 1 else 0) - (if b 0 = a 0 then vartheta L t a else 0)

theorem Qop_eq_sum_Qmat (L : ℕ) [NeZero L] {k : ℕ} (t : ℂ) (A : LoopArg L (k + 1) → ℂ)
    (a : LoopArg L (k + 1)) :
    Qop L t A a = ∑ b : LoopArg L (k + 1), Qmat L t a b * A b := by
  classical
  simp only [Qmat, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Qop, Psum, SumZeroDyn.sum_loopArg_succ]
  simp only [Fin.cons_zero]
  rw [Finset.sum_eq_single (a 0) (fun y _ hy => by simp [hy]) (by simp)]
  simp only [if_true]
  rw [Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun r _ => by ring

/-- At a real time `0 ≤ t < 1` the matrix of `Q_t` is real (`S^{(B)}` is real, so is `Θ_t`). -/
theorem conj_Qmat (L : ℕ) [NeZero L] (hL : 3 ≤ L) {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : LoopArg L (k + 1)) : conj (Qmat L (t : ℂ) a b) = Qmat L (t : ℂ) a b := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1
  have hθ : conj (vartheta L (t : ℂ) a) = vartheta L (t : ℂ) a := by
    rw [vartheta, map_mul, map_pow, map_prod, map_sub, map_one, Complex.conj_ofReal]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ChargeReduce.conj_Theta_apply L hL hξ, Complex.conj_ofReal]
  simp only [Qmat, map_sub, apply_ite (starRingEnd ℂ), map_one, map_zero, hθ]

/-- **`eeHerm` of `Q_t ∘ Φ` is `(Q_t ⊗ Q_t)` of `eeHerm Φ`**, as `2n`-tensors (5.103)–(5.104):
the conjugation on the second slot of `eeHerm` is invisible because `Q_t` is real. -/
theorem eeHerm_Qop_eq_QQ {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Φ : LoopArg (d.L N) (k + 1) → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hΦ : ∀ c, DifferentiableAt ℝ (Φ c) M) :
    (fun c : LoopArg (d.L N) ((k + 1) + (k + 1)) =>
        eeHerm (fun b M' => Qop (d.L N) (t : ℂ) (fun c' => Φ c' M') b)
          (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M)
      = SumZeroDyn.QQ (d.L N) (t : ℂ)
          (fun c => eeHerm Φ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M) := by
  funext c
  have hfam : (fun b M' => Qop (d.L N) (t : ℂ) (fun c' => Φ c' M') b)
      = fun b M' => ∑ c' : LoopArg (d.L N) (k + 1), Qmat (d.L N) (t : ℂ) b c' * Φ c' M' := by
    funext b M'
    exact Qop_eq_sum_Qmat (d.L N) (t : ℂ) _ b
  rw [hfam, eeHerm_linComb _ Φ M hΦ]
  simp only [conj_Qmat (d.L N) (d.three_le_L N) ht0 ht1]
  rw [← SumZeroDyn.append_spl (d.L N) c]
  simp only [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append]
  rw [SumZeroDyn.QQ]
  simp only [Qop₁, Qop₂, Fin.append_left, Fin.append_right]
  rw [Qop_eq_sum_Qmat]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Qop_eq_sum_Qmat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  simp only [SumZeroDyn.spl1_append, SumZeroDyn.spl2_append]
  ring

/-- **The quadratic variation as one kernel on the doubled loop** (Lemma 5.5, (5.24)): for
`U = ukerMatC ξ s t` (the matrix of `U_{s,t,σ}`, output label first),
`vC(∑_b U(a,b) gradMat(Ψ_b) M) = [(U_{s,t,σ} ⊗ U_{s,t,σ̄}) ∘ T^Ψ]_{(a,a)}`,
`T^Ψ(c) = eeHerm Ψ (c_{1..n}) (c_{n+1..2n})`, with doubled edge vector `(ξ, ξ̄)`. -/
theorem vC_sum_ukerMatC_eq {n : ℕ} (ξ : Fin n → ℂ) {s t : ℝ}
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1)
    (Ψ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n) :
    (vC N (∑ b : LoopArg (d.L N) n, ukerMatC ξ s t a b • gradMat (Ψ b) M) : ℂ)
      = Uker (d.L N) (Fin.append ξ (fun i => conj (ξ i))) (s : ℂ) (t : ℂ)
          (fun c => eeHerm Ψ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M)
          (Fin.append a a) := by
  rw [vC_sum_eq_eeHerm, EEUker.Uker_append_apply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  have hc := EEUker.conj_prod_edgeKer (d.L N) (d.three_le_L N) (s := s) ht a b'
  simp only [ukerMatC, SumZeroDyn.spl1_append, SumZeroDyn.spl2_append]
  rw [hc]

/-- The same, read as a norm: `vC ≥ 0`. -/
theorem vC_sum_ukerMatC_eq_norm {n : ℕ} (ξ : Fin n → ℂ) {s t : ℝ}
    (ht : ∀ i, ‖((t : ℝ) : ℂ) * ξ i‖ < 1)
    (Ψ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) n) :
    vC N (∑ b : LoopArg (d.L N) n, ukerMatC ξ s t a b • gradMat (Ψ b) M)
      = ‖Uker (d.L N) (Fin.append ξ (fun i => conj (ξ i))) (s : ℂ) (t : ℂ)
          (fun c => eeHerm Ψ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M)
          (Fin.append a a)‖ := by
  rw [← vC_sum_ukerMatC_eq ξ ht Ψ M a, Complex.norm_real, Real.norm_of_nonneg (vC_nonneg N _)]

/-- The doubled edge vector `(ξ, ξ̄)` of the paper's `ξ = xiOf (mSigma E) σ` has entries of
modulus `1`. -/
theorem norm_xi2C {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| ≤ 2) (σ : Fin n → Bool)
    (i : Fin (n + n)) :
    ‖Fin.append (xiOf (mSigma E) σ) (fun j => conj (xiOf (mSigma E) σ j)) i‖ = 1 := by
  refine Fin.addCases (motive := fun i =>
    ‖Fin.append (xiOf (mSigma E) σ) (fun j => conj (xiOf (mSigma E) σ j)) i‖ = 1)
    (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact norm_xiOf_mSigma hE σ j
  · rw [Fin.append_right, Complex.norm_conj]; exact norm_xiOf_mSigma hE σ j

theorem norm_t_mul_xiOf_lt {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| ≤ 2) (σ : Fin n → Bool)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (i : Fin n) :
    ‖((t : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
  rw [norm_mul, norm_xiOf_mSigma hE σ i, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]
  exact ht1

end Joint

/-! ### 7. (T4) one application of Lemma 7.3 at length `2n` -/

section Kernel

variable {d : Dims} {N : ℕ}

/-- **(T4), Case 2 of (7.16) — sum-zero, any `σ`.** For `Ψ = Q_s ∘ Φ` (the paper's
`Q_{u_{j+1}}`, `s = u_{j+1}`), `T^Φ` bounded by `e` and `(ℓ_s K, δ)`-fast-decaying as a joint
`2n`-tensor, the quadratic-variation density of the `a`-th component of
`U_{s,t,σ} ∘ Q_s ∘ Φ` is bounded by **one** application of Lemma 7.3 (7.16) Case 2 at length
`2n` to `(Q_s ⊗ Q_s) T^Φ` (sum-zero by (5.104), fast-decaying by Lemma 5.13):
`vC ≤ C_{2n} (4K)^{4n} R^{2n} M_Q + C'_{2n} L^{2n} ((1-s)/(1-t))^{2n} qqErr`,
`R = (1-s)ℓ_s/((1-t)ℓ_t)`, `M_Q` the size of `(Q_s ⊗ Q_s) T^Φ` after the two blocks. -/
theorem qv_kernel_le_sumZero {E : ℝ} (hE : |E| < 2) {k : ℕ} (σ : Fin (k + 1) → Bool) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (Φ : LoopArg (d.L N) (k + 1) → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hΦ : ∀ c, DifferentiableAt ℝ (Φ c) M)
    {K e δ : ℝ} (hK : 1 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hTe : ∀ c, ‖eeHerm Φ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M‖ ≤ e)
    (hTd : FastDecay (d.L N) (ellHat (d.L N) (s : ℂ) * K) δ
      (fun c => eeHerm Φ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M))
    (a : LoopArg (d.L N) (k + 1)) :
    vC N (∑ b : LoopArg (d.L N) (k + 1), ukerMatC (xiOf (mSigma E) σ) s t a b
        • gradMat (fun M' => Qop (d.L N) (s : ℂ) (fun c => Φ c M') b) M)
      ≤ cKerSumZero ((k + 1) + (k + 1)) * (4 * K) ^ (2 * ((k + 1) + (k + 1)))
          * ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)))
              ^ ((k + 1) + (k + 1))
          * FastDecayFlow.qBlockSize (d.L N) k (ellHat (d.L N) (s : ℂ))
              (2 * (ellHat (d.L N) (s : ℂ) * K))
              (FastDecayFlow.qBlockSize (d.L N) k (ellHat (d.L N) (s : ℂ))
                (ellHat (d.L N) (s : ℂ) * K) e δ)
              (FastDecayFlow.qBlockErr (d.L N) k (ellHat (d.L N) (s : ℂ))
                (ellHat (d.L N) (s : ℂ) * K) e δ)
        + cKerSumZeroErr ((k + 1) + (k + 1)) * (d.L N : ℝ) ^ ((k + 1) + (k + 1))
          * ((1 - s) / (1 - t)) ^ ((k + 1) + (k + 1))
          * FastDecayFlow.qqErr (d.L N) k (ellHat (d.L N) (s : ℂ)) K e δ := by
  have hL := d.three_le_L N
  have hs1 : s < 1 := hst.trans_lt ht1
  have ht0 : 0 ≤ t := hs0.trans hst
  set T : LoopArg (d.L N) ((k + 1) + (k + 1)) → ℂ :=
    fun c => eeHerm Φ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M with hT
  set ℓr := ellHat (d.L N) (s : ℂ) with hℓr
  have hℓ : (0 : ℝ) < ℓr := lt_of_lt_of_le (by norm_num) (half_le_ellHat_real (d.L N) hL hs0 hs1)
  have hR : 0 < ℓr * K := mul_pos hℓ (by linarith)
  have hR2 : 0 < 2 * (ℓr * K) := by positivity
  set e₂ := FastDecayFlow.qBlockSize (d.L N) k ℓr (ℓr * K) e δ with he₂
  set δ₂ := FastDecayFlow.qBlockErr (d.L N) k ℓr (ℓr * K) e δ with hδ₂
  have he₂0 : 0 ≤ e₂ := FastDecayFlow.qBlockSize_nonneg (d.L N) k hℓ hR.le he hδ
  have hδ₂0 : 0 ≤ δ₂ := FastDecayFlow.qBlockErr_nonneg (d.L N) k hℓ hR.le he hδ
  have h2max : ∀ c, ‖SumZeroDyn.Q2 (d.L N) ((s : ℝ) : ℂ) T c‖ ≤ e₂ := fun c =>
    SumZeroDyn.norm_Q2_le (d.L N) hL hs0 hs1 hR he hδ hTe hTd c
  have h2dec : FastDecay (d.L N) (2 * (ℓr * K)) δ₂ (SumZeroDyn.Q2 (d.L N) ((s : ℝ) : ℂ) T) := by
    simpa [δ₂, ℓr, FastDecayFlow.qBlockErr] using
      SumZeroDyn.fastDecay_Q2 (d.L N) hL hs0 hs1 hR he hδ hTe hTd
  have hMQ0 : 0 ≤ FastDecayFlow.qBlockSize (d.L N) k ℓr (2 * (ℓr * K)) e₂ δ₂ :=
    FastDecayFlow.qBlockSize_nonneg (d.L N) k hℓ hR2.le he₂0 hδ₂0
  have hAM : ∀ c, ‖SumZeroDyn.QQ (d.L N) ((s : ℝ) : ℂ) T c‖
      ≤ FastDecayFlow.qBlockSize (d.L N) k ℓr (2 * (ℓr * K)) e₂ δ₂ := by
    intro c
    have h3 := SumZeroDyn.norm_Q1_le (d.L N) hL hs0 hs1 hR2 he₂0 hδ₂0 h2max h2dec c
    rw [← SumZeroDyn.QQ_eq] at h3
    simpa [e₂, δ₂, ℓr, FastDecayFlow.qBlockSize] using h3
  have hAd := FastDecayFlow.fastDecay_QQ (d.L N) hL hs0 hs1 hK he hδ hTe hTd
  have hξs : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs0]; exact hs1
  have hz := SumZeroDyn.sumZeroAt_QQ (d.L N) hL hξs T
  have hqq0 : 0 ≤ FastDecayFlow.qqErr (d.L N) k ℓr K e δ :=
    FastDecayFlow.qqErr_nonneg (d.L N) k hℓ (by linarith) he hδ
  rw [vC_sum_ukerMatC_eq_norm _ (fun i => norm_t_mul_xiOf_lt hE.le σ ht0 ht1 i),
    eeHerm_Qop_eq_QQ hs0 hs1 Φ hΦ]
  exact norm_Uker_fastDecay_le_sumZero (d.L N) (by omega) hL hs0 hst ht0 ht1
    (fun i h0 => by have := norm_xi2C hE.le σ i; rw [h0, norm_zero] at this; exact zero_ne_one this)
    (fun i => (norm_xi2C hE.le σ i).le) (by linarith) hMQ0 hqq0 hAM hAd hz (Fin.append a a)

/-- **(T4), Case 1 of (7.16) — a repeated charge `σ_k = σ_{k+1}`, `Q := I`.** One application of
Lemma 7.3 Case 1 at length `2n`, with the short edge `i₀ = k` of the first copy of `ξ`:
`vC ≤ C_{2n,κ} K^{2n} R^{2n} e + ((1-s)/(1-t))^{2n} δ`, `κ = min(2 − |E|, 1)`. -/
theorem qv_kernel_le_nonAlt {E : ℝ} (hE : |E| < 2) {n : ℕ} [NeZero n] {σ : Fin n → Bool}
    {k : Fin n} (hk : σ k = σ (k + 1)) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {K e δ : ℝ} (hK : 1 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hTe : ∀ c, ‖eeHerm Φ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M‖ ≤ e)
    (hTd : FastDecay (d.L N) (ellHat (d.L N) (s : ℂ) * K) δ
      (fun c => eeHerm Φ (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M))
    (a : LoopArg (d.L N) n) :
    vC N (∑ b : LoopArg (d.L N) n, ukerMatC (xiOf (mSigma E) σ) s t a b • gradMat (Φ b) M)
      ≤ cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * K ^ (n + n)
          * ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))) ^ (n + n) * e
        + ((1 - s) / (1 - t)) ^ (n + n) * δ := by
  have hL := d.three_le_L N
  have ht0 : 0 ≤ t := hs0.trans hst
  have hκ0 : (0 : ℝ) < min (2 - |E|) 1 := lt_min (by linarith) one_pos
  have hκ1 : min (2 - |E|) 1 ≤ 1 := min_le_right _ _
  have hEκ : |E| ≤ 2 - min (2 - |E|) 1 := by
    have := min_le_left (2 - |E|) (1 : ℝ); linarith
  have hκt : Real.sqrt (min (2 - |E|) 1)
      ≤ ‖1 - ((t : ℝ) : ℂ) * Fin.append (xiOf (mSigma E) σ)
          (fun j => conj (xiOf (mSigma E) σ j)) (Fin.castAdd n k)‖ := by
    rw [Fin.append_left]
    exact sqrt_le_norm_one_sub_xiOf hκ0 hκ1 hEκ ht0 ht1.le hk
  rw [vC_sum_ukerMatC_eq_norm _ (fun i => norm_t_mul_xiOf_lt hE.le σ ht0 ht1 i)]
  exact norm_Uker_fastDecay_le_short (d.L N) hL hs0 hst ht1 (fun i => (norm_xi2C hE.le σ i).le)
    (Real.sqrt_pos.2 hκ0) (Fin.castAdd n k) hκt hK he hδ hTe hTd (Fin.append a a)

end Kernel

/-! ### 8. The (5.93) scale combination and the size of `(Q ⊗ Q) T` -/

section Scales

variable {d : Dims} {N : ℕ}

/-- **(5.93)'s combination**: with `A_u = Wℓ_uη_u` and `R = (1-s)ℓ_s/((1-t)ℓ_t)`, `R = A_s/A_t`
exactly (`η_u = (1-u) Im m`), so `R^m A_s^{-m} = A_t^{-m}`:
`(ℓ_sη_s/ℓ_tη_t)^{2n} (Wℓ_sη_s)^{-2n} = (Wℓ_tη_t)^{-2n}`. The cap `ℓ ≤ L` of `ellHat` (the
saturated segment) is kept: nothing here uses the uncapped `(1-u)^{-1/2}`. -/
theorem scale_ratio_pow {E s t : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (m : ℕ) :
    ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))) ^ m
        * ((band d).scale E N s)⁻¹ ^ m
      = ((band d).scale E N t)⁻¹ ^ m := by
  have hℓs : 0 < ellHat (d.L N) (s : ℂ) :=
    lt_of_lt_of_le (by norm_num) (half_le_ellHat_real (d.L N) (d.three_le_L N) hs0 hs1)
  have hℓt : 0 < ellHat (d.L N) (t : ℂ) :=
    lt_of_lt_of_le (by norm_num) (half_le_ellHat_real (d.L N) (d.three_le_L N) ht0 ht1)
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hηt : 0 < etaT E t := etaT_pos_of_lt_one hE ht1
  have hc : 0 < (mE E).im := by
    have h1t : 0 < 1 - t := by linarith
    have : etaT E t = (1 - t) * (mE E).im := rfl
    rw [this] at hηt
    exact pos_of_mul_pos_right hηt h1t.le
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have h1t : (0 : ℝ) < 1 - t := by linarith
  rw [← mul_pow]
  congr 1
  change (1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))
      * ((d.W N : ℝ) * ellHat (d.L N) (s : ℂ) * ((1 - s) * (mE E).im))⁻¹
    = ((d.W N : ℝ) * ellHat (d.L N) (t : ℂ) * ((1 - t) * (mE E).im))⁻¹
  field_simp

/-- The prefactor of (5.81) against the scale: `W(ℓ_sK + 1)/A_s ≤ 3K/η_s` (`ℓ_s ≥ 1/2`, `K ≥ 1`).
This turns `W ℓ_u (Wℓ_uη_u)^{-2n-1}` of (5.81) into `η_u^{-1} (Wℓ_uη_u)^{-2n}` of (5.77). -/
theorem W_mul_ell_div_scale_le {E s K : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hK : 1 ≤ K) :
    (d.W N : ℝ) * (ellHat (d.L N) (s : ℂ) * K + 1) / (band d).scale E N s
      ≤ 3 * K * (etaT E s)⁻¹ := by
  have hℓ : (1 : ℝ) / 2 ≤ ellHat (d.L N) (s : ℂ) :=
    half_le_ellHat_real (d.L N) (d.three_le_L N) hs0 hs1
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hη : 0 < etaT E s := etaT_pos_of_lt_one hE hs1
  have hℓ0 : 0 < ellHat (d.L N) (s : ℂ) := by linarith
  change (d.W N : ℝ) * (ellHat (d.L N) (s : ℂ) * K + 1)
      / ((d.W N : ℝ) * ellHat (d.L N) (s : ℂ) * etaT E s) ≤ 3 * K * (etaT E s)⁻¹
  rw [div_le_iff₀ (by positivity)]
  have : (d.W N : ℝ) * (ellHat (d.L N) (s : ℂ) * K + 1)
      ≤ (d.W N : ℝ) * (3 * K * ellHat (d.L N) (s : ℂ)) := by
    apply mul_le_mul_of_nonneg_left _ hW.le
    nlinarith
  calc (d.W N : ℝ) * (ellHat (d.L N) (s : ℂ) * K + 1)
      ≤ (d.W N : ℝ) * (3 * K * ellHat (d.L N) (s : ℂ)) := this
    _ = 3 * K * (etaT E s)⁻¹ * ((d.W N : ℝ) * ellHat (d.L N) (s : ℂ) * etaT E s) := by
        field_simp

/-- The `N`-free, `K`-polynomial part of the `e`-coefficient of the size of `(Q_s ⊗ Q_s) T`. -/
noncomputable def qqCoefPoly (k : ℕ) (K : ℝ) : ℝ :=
  (1 + (6 * Real.exp 1 * cTwo52 * K) ^ k) * (1 + (8 * Real.exp 1 * cTwo52 * K) ^ k)

/-- The exponentially small part of the `e`-coefficient: the second `Q` block acting on the first
block's decay error, `(2cL)^k (6ecK)^k e^{-c₀K}` (negligible for `K = W^τ`, like `W^{-D}`). -/
noncomputable def qqCoefTail (L k : ℕ) (K : ℝ) : ℝ :=
  (2 * cTwo52 * L) ^ k * (6 * Real.exp 1 * cTwo52 * K) ^ k * Real.exp (-(cZero * K))

/-- The `e`-coefficient of the size of `(Q_s ⊗ Q_s) T` (two `Q` blocks, (5.87)/(5.103)). -/
noncomputable def qqCoefE (L k : ℕ) (K : ℝ) : ℝ := qqCoefPoly k K + qqCoefTail L k K

/-- The `δ`-coefficient of the size of `(Q_s ⊗ Q_s) T`. -/
noncomputable def qqCoefD (L k : ℕ) (K : ℝ) : ℝ :=
  (2 * cTwo52 * L) ^ k * (2 + (8 * Real.exp 1 * cTwo52 * K) ^ k + 2 * (2 * cTwo52 * L) ^ k)

/-- **The size of `(Q_s ⊗ Q_s) T` is linear in `(e, δ)` with `ℓ`-free coefficients**
(`ℓ ≥ 1/2`, `K ≥ 1`). -/
theorem qqMax_le (L k : ℕ) {ℓr K e δ : ℝ} (hℓ : 1 / 2 ≤ ℓr) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) :
    FastDecayFlow.qBlockSize L k ℓr (2 * (ℓr * K)) (FastDecayFlow.qBlockSize L k ℓr (ℓr * K) e δ)
        (FastDecayFlow.qBlockErr L k ℓr (ℓr * K) e δ)
      ≤ qqCoefE L k K * e + qqCoefD L k K * δ := by
  have hc := cTwo52_pos
  have hℓ0 : 0 < ℓr := by linarith
  set x := cTwo52 / ℓr with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 2 * cTwo52 := by
    rw [hx, div_le_iff₀ hℓ0]; nlinarith
  set p1 := (2 * Real.exp 1 * (ℓr * K + 1)) ^ k * x ^ k with hp1
  set p2 := (2 * Real.exp 1 * (2 * (ℓr * K) + 1)) ^ k * x ^ k with hp2
  set lx := (L : ℝ) ^ k * x ^ k with hlx
  set X1 := Real.exp (-(cZero * (ℓr * K) / ℓr)) with hX1
  have hX1e : X1 = Real.exp (-(cZero * K)) := by
    rw [hX1]; congr 1; field_simp
  have hid : FastDecayFlow.qBlockSize L k ℓr (2 * (ℓr * K))
        (FastDecayFlow.qBlockSize L k ℓr (ℓr * K) e δ)
        (FastDecayFlow.qBlockErr L k ℓr (ℓr * K) e δ)
      = e * ((1 + p1) * (1 + p2) + lx * p1 * X1)
        + δ * (lx * (1 + p2) + lx * (1 + lx * X1 + lx)) := by
    simp only [FastDecayFlow.qBlockSize, FastDecayFlow.qBlockErr, hp1, hp2, hlx, hX1, hx]
    ring
  have he1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h2K : cTwo52 / ℓr ≤ 2 * cTwo52 * K := by
    have : cTwo52 / ℓr ≤ 2 * cTwo52 := hx2
    nlinarith
  have hbase1 : 2 * Real.exp 1 * (ℓr * K + 1) * x ≤ 6 * Real.exp 1 * cTwo52 * K := by
    have h : (ℓr * K + 1) * x = cTwo52 * K + cTwo52 / ℓr := by rw [hx]; field_simp
    calc 2 * Real.exp 1 * (ℓr * K + 1) * x = 2 * Real.exp 1 * ((ℓr * K + 1) * x) := by ring
      _ = 2 * Real.exp 1 * (cTwo52 * K + cTwo52 / ℓr) := by rw [h]
      _ ≤ 2 * Real.exp 1 * (cTwo52 * K + 2 * cTwo52 * K) := by gcongr
      _ = 6 * Real.exp 1 * cTwo52 * K := by ring
  have hbase2 : 2 * Real.exp 1 * (2 * (ℓr * K) + 1) * x ≤ 8 * Real.exp 1 * cTwo52 * K := by
    have h : (2 * (ℓr * K) + 1) * x = 2 * cTwo52 * K + cTwo52 / ℓr := by rw [hx]; field_simp
    calc 2 * Real.exp 1 * (2 * (ℓr * K) + 1) * x
        = 2 * Real.exp 1 * ((2 * (ℓr * K) + 1) * x) := by ring
      _ = 2 * Real.exp 1 * (2 * cTwo52 * K + cTwo52 / ℓr) := by rw [h]
      _ ≤ 2 * Real.exp 1 * (2 * cTwo52 * K + 2 * cTwo52 * K) := by gcongr
      _ = 8 * Real.exp 1 * cTwo52 * K := by ring
  have hp1b : p1 ≤ (6 * Real.exp 1 * cTwo52 * K) ^ k := by
    rw [hp1, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hbase1 k
  have hp2b : p2 ≤ (8 * Real.exp 1 * cTwo52 * K) ^ k := by
    rw [hp2, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hbase2 k
  have hlxb : lx ≤ (2 * cTwo52 * L) ^ k := by
    rw [hlx, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) L]) k
  have hp10 : 0 ≤ p1 := by positivity
  have hp20 : 0 ≤ p2 := by positivity
  have hlx0 : 0 ≤ lx := by positivity
  have hX10 : 0 ≤ X1 := (Real.exp_pos _).le
  have hX11 : X1 ≤ 1 := by rw [hX1e]; exact Real.exp_le_one_iff.2 (by nlinarith [cZero_pos])
  rw [hid, mul_comm (qqCoefE L k K) e, mul_comm (qqCoefD L k K) δ]
  unfold qqCoefE qqCoefPoly qqCoefTail qqCoefD
  rw [← hX1e]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ he
    gcongr
  · apply mul_le_mul_of_nonneg_left _ hδ
    have hl2 : lx * (1 + lx * X1 + lx) ≤ (2 * cTwo52 * L) ^ k * (1 + 2 * (2 * cTwo52 * L) ^ k) := by
      have : lx * X1 ≤ lx := by nlinarith
      have hB : 0 ≤ (2 * cTwo52 * L) ^ k := by positivity
      calc lx * (1 + lx * X1 + lx) ≤ lx * (1 + 2 * lx) := by nlinarith
        _ ≤ (2 * cTwo52 * L) ^ k * (1 + 2 * (2 * cTwo52 * L) ^ k) := by gcongr
    have hl1 : lx * (1 + p2) ≤ (2 * cTwo52 * L) ^ k * (1 + (8 * Real.exp 1 * cTwo52 * K) ^ k) := by
      gcongr
    nlinarith

end Scales

/-! ### 9. (T4) The quadratic-variation contraction: (5.105) → `c_j` -/

section Contraction

variable {d : Dims} {N : ℕ}

/-- The (T3) bound of `eeHerm` at scale `A`, decay radius `ρ = ℓ_u W^τ`, decay error `W^{-D}`. -/
noncomputable def eeHermBd (d : Dims) (N n : ℕ) (Φ A ρ D : ℝ) : ℝ :=
  n * (2 * Real.exp 1 * n * Φ * ((d.W N : ℝ) * (ρ + 1) / A) * A⁻¹ ^ (2 * n)
    + n * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D))

/-- The (T2) decay error of `eeHerm`, `n² W L W^{-D}`. -/
noncomputable def eeHermErr (d : Dims) (N n : ℕ) (D : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D)

theorem eeHermErr_nonneg (d : Dims) (N n : ℕ) (D : ℝ) : 0 ≤ eeHermErr d N n D := by
  unfold eeHermErr
  have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) (-D)
  positivity

theorem eeHermBd_nonneg (d : Dims) (N n : ℕ) {Φ A ρ D : ℝ} (hΦ : 0 ≤ Φ) (hA : 0 < A)
    (hρ : 0 ≤ ρ) : 0 ≤ eeHermBd d N n Φ A ρ D := by
  unfold eeHermBd
  have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) (-D)
  positivity

/-- **The (5.93) combination applied to the (T3) bound**:
`R^{2n} · eeHermBd ≤ 6e n² K Φ η_s^{-1} (Wℓ_tη_t)^{-2n} + R^{2n} · n² W L W^{-D}`. -/
theorem ratio_pow_mul_eeHermBd_le {E s t K Φ D : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht1 : t < 1) (hK : 1 ≤ K) (hΦ : 0 ≤ Φ) (n : ℕ) :
    ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))) ^ (n + n)
        * eeHermBd d N n Φ ((band d).scale E N s) (ellHat (d.L N) (s : ℂ) * K) D
      ≤ 6 * Real.exp 1 * (n : ℝ) ^ 2 * K * Φ * (etaT E s)⁻¹ * ((band d).scale E N t)⁻¹ ^ (2 * n)
        + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))) ^ (n + n)
          * eeHermErr d N n D := by
  have hs1 : s < 1 := hst.trans_lt ht1
  have ht0 : 0 ≤ t := hs0.trans hst
  set R := (1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)) with hR
  set As := (band d).scale E N s with hAs
  set At := (band d).scale E N t with hAt
  have hratio : R ^ (n + n) * As⁻¹ ^ (2 * n) = At⁻¹ ^ (2 * n) := by
    rw [two_mul]; exact scale_ratio_pow hE hs0 hs1 ht0 ht1 (n + n)
  have hX := W_mul_ell_div_scale_le (d := d) (N := N) hE hs0 hs1 hK
  have hAt0 : 0 ≤ At⁻¹ ^ (2 * n) := by
    have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht1
    have hℓ : 0 < ellHat (d.L N) (t : ℂ) :=
      lt_of_lt_of_le (by norm_num) (half_le_ellHat_real (d.L N) (d.three_le_L N) ht0 ht1)
    have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    have : 0 < At := by
      rw [hAt]; change 0 < (d.W N : ℝ) * ellHat (d.L N) (t : ℂ) * etaT E t; positivity
    positivity
  have hsplit : R ^ (n + n) * eeHermBd d N n Φ As (ellHat (d.L N) (s : ℂ) * K) D
      = 2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ
          * ((d.W N : ℝ) * (ellHat (d.L N) (s : ℂ) * K + 1) / As) * (R ^ (n + n) * As⁻¹ ^ (2 * n))
        + R ^ (n + n) * eeHermErr d N n D := by
    unfold eeHermBd eeHermErr; ring
  rw [hsplit, hratio]
  refine add_le_add ?_ le_rfl
  have hc : 0 ≤ 2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ := by positivity
  calc 2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ * ((d.W N : ℝ) * (ellHat (d.L N) (s : ℂ) * K + 1) / As)
        * At⁻¹ ^ (2 * n)
      ≤ 2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ * (3 * K * (etaT E s)⁻¹) * At⁻¹ ^ (2 * n) := by gcongr
    _ = 6 * Real.exp 1 * (n : ℝ) ^ 2 * K * Φ * (etaT E s)⁻¹ * At⁻¹ ^ (2 * n) := by ring

theorem cKerShort_nonneg (n : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ cKerShort n κ := by
  unfold cKerShort
  have := cWin_nonneg; have := cShort_nonneg
  positivity

theorem cKerSumZero_nonneg (n : ℕ) : 0 ≤ cKerSumZero n := by
  unfold cKerSumZero
  have := cWin_nonneg; have := cLip_nonneg
  positivity

theorem qqCoefE_nonneg (L k : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ qqCoefE L k K := by
  unfold qqCoefE qqCoefPoly qqCoefTail; have := cTwo52_pos; positivity

theorem qqCoefD_nonneg (L k : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ qqCoefD L k K := by
  unfold qqCoefD; have := cTwo52_pos; positivity

/-- `Ξ ≤ Φ` forces `Φ ≥ 0`. -/
theorem nonneg_of_loopXi_le {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ} {A Φ : ℝ} (hA : 0 ≤ A)
    {m : ℕ} (hΞ : loopXi (d.L N) (d.W N) M z A m ≤ Φ) : 0 ≤ Φ :=
  le_trans (mul_nonneg (loopMax_nonneg m) (pow_nonneg hA _)) hΞ

/-- **The quadratic-variation contraction, Case 1 (non-alternating `σ`, `Q := I`)** — (5.105) →
`c_j`.

At a Hermitian `M` (on the grid: `H_j`) with `Ξ^{(L)}_{s,2n+2}(M) ≤ Φ` and `M ∈ decaySet` at
time `s = u_{j+1}`, for `U = U_{s,t,σ}` and `Φ_b = (L − K)_{s,σ,b}`:
`vC(∑_b U(a,b) gradMat(Φ_b) M)`
`≤ C_{2n,κ} K^{2n} (6e n² K Φ η_s^{-1} (Wℓ_tη_t)^{-2n} + R^{2n} n² W L W^{-D}) + (η_s/η_t)^{2n} n² W L W^{-D}`,
`K = W^τ`. With `Φ = N^εΛ` this is `C N^{ε+Cτ} Λ (Wℓ_tη_t)^{-2n} η_s^{-1}` plus explicit
`W^{-D}` tails. The joint route: one application of Lemma 7.3 at length `2n`. -/
theorem qv_contraction_le_nonAlt {E : ℝ} (hE : |E| < 2) {n : ℕ} [NeZero n] {σ : Fin n → Bool}
    {k : Fin n} (hk : σ k = σ (k + 1)) {s t τ D : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (hτ : 0 ≤ τ) (Kc : LoopArg (d.L N) n → ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {Φ : ℝ} (hA : 1 ≤ (band d).scale E N s)
    (hΞ : loopXi (d.L N) (d.W N) M (zt E s) ((band d).scale E N s) (2 * n + 2) ≤ Φ)
    (hdec : M ∈ decaySet d E N (2 * n + 2) s τ D) (a : LoopArg (d.L N) n) :
    vC N (∑ b : LoopArg (d.L N) n, ukerMatC (xiOf (mSigma E) σ) s t a b
        • gradMat (fun M' => loopObs d N (zt E s) (toIdx σ b) M' - Kc b) M)
      ≤ cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ) ^ (n + n)
          * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * Φ * (etaT E s)⁻¹
              * ((band d).scale E N t)⁻¹ ^ (2 * n)
            + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))) ^ (n + n)
              * eeHermErr d N n D)
        + ((1 - s) / (1 - t)) ^ (n + n) * eeHermErr d N n D := by
  have hs1 : s < 1 := hst.trans_lt ht1
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hK : 1 ≤ (d.W N : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  have hΦ0 : 0 ≤ Φ := nonneg_of_loopXi_le (by linarith) hΞ
  have hTe : ∀ c : LoopArg (d.L N) (n + n),
      ‖eeHerm (fun b M' => loopObs d N (zt E s) (toIdx σ b) M' - Kc b)
        (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M‖
        ≤ eeHermBd d N n Φ ((band d).scale E N s) (ellHat (d.L N) (s : ℂ) * (d.W N : ℝ) ^ τ) D :=
    fun c => eeHerm_le hE hs0 hs1 hn1 σ Kc hM hA hΞ hdec _ _
  have hTd := eeHerm_fastDecay hE hs1 σ Kc hM hdec
  have he := eeHermBd_nonneg d N n (D := D) hΦ0 (by linarith : (0 : ℝ) < (band d).scale E N s)
    (ellHat_mul_rpow_pos (d := d) (N := N) hs0 hs1 τ).le
  have key := qv_kernel_le_nonAlt hE hk hs0 hst ht1 _ M hK he (eeHermErr_nonneg d N n D) hTe
    hTd a
  refine key.trans (add_le_add ?_ le_rfl)
  have hC : 0 ≤ cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ) ^ (n + n) :=
    mul_nonneg (cKerShort_nonneg _ (Real.sqrt_nonneg _)) (by positivity)
  rw [mul_assoc (cKerShort (n + n) _ * _)]
  exact mul_le_mul_of_nonneg_left (ratio_pow_mul_eeHermBd_le hE hs0 hst ht1 hK hΦ0 n) hC

/-- **The quadratic-variation contraction, Case 2 (any `σ`, with `Q_s`)** — (5.105) → `c_j`.

For `Ψ_b = (Q_s ∘ (L − K)_{s,σ})_b` (`n = k + 1`), `U = U_{s,t,σ}`, on
`{Ξ^{(L)}_{s,2n+2} ≤ Φ} ∩ decaySet` (Hermitian `M`, on the grid `H_j`):
`vC(∑_b U(a,b) gradMat(Ψ_b) M) ≤ C_{2n}(4K)^{4n} [α_E (6e n² K Φ η_s^{-1}(Wℓ_tη_t)^{-2n} + R^{2n} δ₁)
  + R^{2n} α_D δ₁] + C'_{2n} L^{2n} (η_s/η_t)^{2n} qqErr(e, δ₁)`,
`K = W^τ`, `δ₁ = n² W L W^{-D}`, `e` the (T3) bound, `α_E = qqCoefE`, `α_D = qqCoefD`.
The main term is `C N^{ε+Cτ} Λ (Wℓ_tη_t)^{-2n} η_s^{-1}` (`Φ = N^εΛ`); `α_E` carries, besides a
polynomial in `K`, the term `(2cL)^k (6ecK)^k e^{-c₀K}`, negligible for `K = W^τ`. -/
theorem qv_contraction_le_sumZero {E : ℝ} (hE : |E| < 2) {k : ℕ} (σ : Fin (k + 1) → Bool)
    {s t τ D : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (hτ : 0 ≤ τ)
    (Kc : LoopArg (d.L N) (k + 1) → ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {Φ : ℝ} (hA : 1 ≤ (band d).scale E N s)
    (hΞ : loopXi (d.L N) (d.W N) M (zt E s) ((band d).scale E N s) (2 * (k + 1) + 2) ≤ Φ)
    (hdec : M ∈ decaySet d E N (2 * (k + 1) + 2) s τ D) (a : LoopArg (d.L N) (k + 1)) :
    vC N (∑ b : LoopArg (d.L N) (k + 1), ukerMatC (xiOf (mSigma E) σ) s t a b
        • gradMat (fun M' => Qop (d.L N) (s : ℂ)
            (fun c => loopObs d N (zt E s) (toIdx σ c) M' - Kc c) b) M)
      ≤ cKerSumZero ((k + 1) + (k + 1)) * (4 * (d.W N : ℝ) ^ τ) ^ (2 * ((k + 1) + (k + 1)))
          * (qqCoefE (d.L N) k ((d.W N : ℝ) ^ τ)
              * (6 * Real.exp 1 * ((k + 1 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * Φ * (etaT E s)⁻¹
                  * ((band d).scale E N t)⁻¹ ^ (2 * (k + 1))
                + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)))
                    ^ ((k + 1) + (k + 1)) * eeHermErr d N (k + 1) D)
            + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)))
                ^ ((k + 1) + (k + 1))
              * (qqCoefD (d.L N) k ((d.W N : ℝ) ^ τ) * eeHermErr d N (k + 1) D))
        + cKerSumZeroErr ((k + 1) + (k + 1)) * (d.L N : ℝ) ^ ((k + 1) + (k + 1))
          * ((1 - s) / (1 - t)) ^ ((k + 1) + (k + 1))
          * FastDecayFlow.qqErr (d.L N) k (ellHat (d.L N) (s : ℂ)) ((d.W N : ℝ) ^ τ)
              (eeHermBd d N (k + 1) Φ ((band d).scale E N s)
                (ellHat (d.L N) (s : ℂ) * (d.W N : ℝ) ^ τ) D)
              (eeHermErr d N (k + 1) D) := by
  have hs1 : s < 1 := hst.trans_lt ht1
  have ht0 : 0 ≤ t := hs0.trans hst
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  set K := (d.W N : ℝ) ^ τ with hKdef
  have hK : 1 ≤ K := Real.one_le_rpow hW1 hτ
  have hΦ0 : 0 ≤ Φ := nonneg_of_loopXi_le (by linarith) hΞ
  have hz : (zt E s).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hs1
  set Φf : LoopArg (d.L N) (k + 1) → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    fun b M' => loopObs d N (zt E s) (toIdx σ b) M' - Kc b with hΦf
  have hdiff : ∀ c, DifferentiableAt ℝ (Φf c) M := fun c =>
    (differentiableAt_loopObs hz (toIdx_wf σ c) M).sub_const (Kc c)
  set e := eeHermBd d N (k + 1) Φ ((band d).scale E N s) (ellHat (d.L N) (s : ℂ) * K) D with he
  set δ₁ := eeHermErr d N (k + 1) D with hδ₁
  have hTe : ∀ c : LoopArg (d.L N) ((k + 1) + (k + 1)),
      ‖eeHerm Φf (SumZeroDyn.spl1 (d.L N) c) (SumZeroDyn.spl2 (d.L N) c) M‖ ≤ e :=
    fun c => eeHerm_le hE hs0 hs1 (by omega) σ Kc hM hA hΞ hdec _ _
  have hTd := eeHerm_fastDecay hE hs1 σ Kc hM hdec
  have he0 : 0 ≤ e := eeHermBd_nonneg d N (k + 1) hΦ0 (by linarith) (ellHat_mul_rpow_pos (d := d) (N := N) hs0 hs1 τ).le
  have hδ0 : 0 ≤ δ₁ := eeHermErr_nonneg d N (k + 1) D
  have key := qv_kernel_le_sumZero hE σ hs0 hst ht1 Φf hdiff hK he0 hδ0 hTe hTd a
  refine key.trans (add_le_add ?_ le_rfl)
  have hℓ : (1 : ℝ) / 2 ≤ ellHat (d.L N) (s : ℂ) :=
    half_le_ellHat_real (d.L N) (d.three_le_L N) hs0 hs1
  have hMQ := qqMax_le (d.L N) k hℓ hK he0 hδ0
  set R := (1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)) with hR
  have hR0 : 0 ≤ R := by
    have hℓs : 0 < ellHat (d.L N) (s : ℂ) := by linarith
    have hℓt : 0 < ellHat (d.L N) (t : ℂ) :=
      lt_of_lt_of_le (by norm_num) (half_le_ellHat_real (d.L N) (d.three_le_L N) ht0 ht1)
    have : 0 < 1 - s := by linarith
    have : 0 < 1 - t := by linarith
    positivity
  have hmain := ratio_pow_mul_eeHermBd_le (d := d) (N := N) (D := D) hE hs0 hst ht1 hK hΦ0 (k + 1)
  have hC : 0 ≤ cKerSumZero ((k + 1) + (k + 1)) * (4 * K) ^ (2 * ((k + 1) + (k + 1))) :=
    mul_nonneg (cKerSumZero_nonneg _) (by positivity)
  have hRp : 0 ≤ R ^ ((k + 1) + (k + 1)) := pow_nonneg hR0 _
  have hE0 := qqCoefE_nonneg (d.L N) k (by linarith : (0 : ℝ) ≤ K)
  calc cKerSumZero ((k + 1) + (k + 1)) * (4 * K) ^ (2 * ((k + 1) + (k + 1)))
        * R ^ ((k + 1) + (k + 1))
        * FastDecayFlow.qBlockSize (d.L N) k (ellHat (d.L N) (s : ℂ))
            (2 * (ellHat (d.L N) (s : ℂ) * K))
            (FastDecayFlow.qBlockSize (d.L N) k (ellHat (d.L N) (s : ℂ))
              (ellHat (d.L N) (s : ℂ) * K) e δ₁)
            (FastDecayFlow.qBlockErr (d.L N) k (ellHat (d.L N) (s : ℂ))
              (ellHat (d.L N) (s : ℂ) * K) e δ₁)
      ≤ cKerSumZero ((k + 1) + (k + 1)) * (4 * K) ^ (2 * ((k + 1) + (k + 1)))
          * (qqCoefE (d.L N) k K * (R ^ ((k + 1) + (k + 1)) * e)
            + R ^ ((k + 1) + (k + 1)) * (qqCoefD (d.L N) k K * δ₁)) := by
        rw [mul_assoc (cKerSumZero _ * _)]
        refine mul_le_mul_of_nonneg_left ?_ hC
        calc R ^ ((k + 1) + (k + 1)) * _
            ≤ R ^ ((k + 1) + (k + 1)) * (qqCoefE (d.L N) k K * e + qqCoefD (d.L N) k K * δ₁) :=
              mul_le_mul_of_nonneg_left hMQ hRp
          _ = _ := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hC
        exact mul_le_mul_of_nonneg_left hmain hE0

end Contraction

/-! ### 10. (T4) on the grid -/

section GridForm

variable {d : Dims} {N : ℕ}

/-- The right-hand side of `qv_contraction_le_nonAlt`. -/
noncomputable def qvBdNonAlt (d : Dims) (N : ℕ) (E : ℝ) (n : ℕ) (s t τ D Φ : ℝ) : ℝ :=
  cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ) ^ (n + n)
      * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * Φ * (etaT E s)⁻¹
          * ((band d).scale E N t)⁻¹ ^ (2 * n)
        + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ))) ^ (n + n)
          * eeHermErr d N n D)
    + ((1 - s) / (1 - t)) ^ (n + n) * eeHermErr d N n D

/-- The right-hand side of `qv_contraction_le_sumZero`. -/
noncomputable def qvBdSumZero (d : Dims) (N : ℕ) (E : ℝ) (k : ℕ) (s t τ D Φ : ℝ) : ℝ :=
  cKerSumZero ((k + 1) + (k + 1)) * (4 * (d.W N : ℝ) ^ τ) ^ (2 * ((k + 1) + (k + 1)))
      * (qqCoefE (d.L N) k ((d.W N : ℝ) ^ τ)
          * (6 * Real.exp 1 * ((k + 1 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * Φ * (etaT E s)⁻¹
              * ((band d).scale E N t)⁻¹ ^ (2 * (k + 1))
            + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)))
                ^ ((k + 1) + (k + 1)) * eeHermErr d N (k + 1) D)
        + ((1 - s) * ellHat (d.L N) (s : ℂ) / ((1 - t) * ellHat (d.L N) (t : ℂ)))
            ^ ((k + 1) + (k + 1))
          * (qqCoefD (d.L N) k ((d.W N : ℝ) ^ τ) * eeHermErr d N (k + 1) D))
    + cKerSumZeroErr ((k + 1) + (k + 1)) * (d.L N : ℝ) ^ ((k + 1) + (k + 1))
      * ((1 - s) / (1 - t)) ^ ((k + 1) + (k + 1))
      * FastDecayFlow.qqErr (d.L N) k (ellHat (d.L N) (s : ℂ)) ((d.W N : ℝ) ^ τ)
          (eeHermBd d N (k + 1) Φ ((band d).scale E N s)
            (ellHat (d.L N) (s : ℂ) * (d.W N : ℝ) ^ τ) D)
          (eeHermErr d N (k + 1) D)

/-- **(T4) on the grid, Case 1** (`σ_k = σ_{k+1}`, `Q := I`). -/
theorem step_mul_vC_AbC_le_nonAlt (sg tg : ℕ → ℝ) (Kg : ℕ → ℕ) (j : ℕ)
    (hΔ : 0 ≤ step sg tg Kg N) {E : ℝ} (hE : |E| < 2) {n : ℕ} [NeZero n] {σ : Fin n → Bool}
    {k : Fin n} (hk : σ k = σ (k + 1)) {v w τ D : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    (hτ : 0 ≤ τ) (Kc : LoopArg (d.L N) n → ℂ) (ω : Ωg d) {Φ : ℝ}
    (hA : 1 ≤ (band d).scale E N v)
    (hΞ : loopXi (d.L N) (d.W N) (H d sg tg Kg N j ω) (zt E v) ((band d).scale E N v)
      (2 * n + 2) ≤ Φ)
    (hdec : H d sg tg Kg N j ω ∈ decaySet d E N (2 * n + 2) v τ D) (b : LoopArg (d.L N) n) :
    step sg tg Kg N * vC N (AbC d sg tg Kg N j n
        (fun b M' => loopObs d N (zt E v) (toIdx σ b) M' - Kc b)
        (ukerMatC (xiOf (mSigma E) σ) v w) b ω)
      ≤ step sg tg Kg N * qvBdNonAlt d N E n v w τ D Φ :=
  mul_le_mul_of_nonneg_left (qv_contraction_le_nonAlt hE hk hv0 hvw hw1 hτ Kc
    (H_isHermitian d sg tg Kg N j ω) hA hΞ hdec b) hΔ

end GridForm

/-! ### 11. Satisfiability of the hypotheses of (T2)–(T4) -/

section Witness

variable {d : Dims} {N : ℕ}

end Witness

/-! ### 12. (T5) pilots -/

section BandEval

variable {d : Dims} {N : ℕ}

/-- The family `Φ_a = (L − K)_{s,σ,a}` is `ΦgridG` on the Gaussian band. -/
theorem ΦgridG_band_eq (E s : ℝ) {n : ℕ} (σ : Fin n → Bool) (a : LoopArg (d.L N) n) :
    ΦgridG (band d) E N s σ a
      = fun M => loopObs d N (zt E s) (toIdx σ a) M - (band d).Kval E N s (toIdx σ a) := rfl

end BandEval

end RBM.Gauss.Grid

end

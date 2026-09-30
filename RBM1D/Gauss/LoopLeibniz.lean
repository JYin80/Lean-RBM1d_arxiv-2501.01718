/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DischargeBDG
import RBM1D.Gauss.LoopIto
import RBM1D.Gauss.IBP
import RBM1D.Gauss.DimsExample

/-!
# The chain rule `E^{(M)}(α) = ∑_k E^{(M)}(α,k)`, and the differentiability of the loop

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, Definition 5.4 and the line of (5.25) that splits `E^{(M)}(α)` over the `n`
`G`-edges of the loop.

The quadratic-variation bounds of `RBM1D/Gauss/DischargeBDG.lean` and `RBM1D/Gauss/EEUker.lean`
carry two hypotheses:

* `hsplit` in `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` — the chain rule
  `E^{(M)}_{σ,a}(α) = ∑_{k} E^{(M)}_{σ,a}(α,k)`;
* `hdiff` in `RBM.Gauss.emart_Uker` / `RBM.Gauss.quadVarPairs_Uker` — differentiability of
  the loop observable in the matrix.

Both are theorems here.

## The `List.foldr` Leibniz rule

`RBM.Gauss.hasDerivAt_gprodM` (`RBM1D/Gauss/LoopIto.lean`) is the Leibniz rule for the
`List.foldr` product of resolvents:

  `∂_s ∏_i G(σ_i)(M + sB) A_i = - ∑_k ∏ with G(σ_k) ↦ G(σ_k) B G(σ_k)`,

at a Hermitian `M` along a Hermitian direction `B`.  Mathlib's own `HasFDerivAt.list_prod'`
(`Mathlib/Analysis/Calculus/FDeriv/Mul.lean`) is the general normed-algebra statement, but it
is not needed: `hasDerivAt_gprodM` is already in the exact `foldr` shape of `RBM.gloopProd`,
and the line-wise form is what `RBM.Gauss.coordD1` consumes.  This file supplies what comes
downstream of it:

1. the purely algebraic identification of the inserted product with the cut block
   `RBM.Gauss.loopCut` (a trace rotation) — `RBM.Gauss.trace_gprodG_insB`;
2. the first coordinate derivative of `RBM.Gauss.loopObs` in that form —
   `RBM.Gauss.coordD1_loopObs_eq`;
3. the Wirtinger combination `∂_{ij} = (∂_a - i ∂_b)/2` of the two coordinate derivatives,
   which selects the `(j,i)` entry — `RBM.Gauss.wirtFirst_loopObs_eq`.

## Main results

* `RBM.Gauss.emart_eq_sum_emartEdge` — **the chain rule**, i.e. `hsplit`.
* `RBM.Gauss.differentiableAt_loopObs` — **`hdiff`**.
* `RBM.Gauss.emart_eq_sum_emartEdge'`, `RBM.Gauss.differentiableAt_loopObs` — the hypotheses
  `hsplit` and `hdiff` of `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg` and its siblings, in the
  exact shape those theorems ask for.

## The one added hypothesis: `M` is Hermitian

`RBM.Gauss.emart` is the derivative of `RBM.Gauss.loopObs`, which pre-composes with the
Hermitian projection `RBM.Gauss.hermCLM` (the device for global definedness), whereas
`RBM.Gauss.emartEdge` is written through `RBM.Gauss.loopCut` at the **raw** matrix `M`.  Off
the Hermitian locus the two sides are not even functions of the same argument — the left-hand
side reads only `(M + Mᴴ)/2` — so there is no reason for them to agree there, and no consumer
needs them to: every consumer evaluates at `M = RBM.Gauss.Hflow d N u ω`, which is Hermitian,
and the paper's `H_t` is Hermitian throughout §5.2.

## What is not restated here

The sign and the `-G B G` shape of `∂_{M} G` come from `RBM.Gauss.hasDerivAt_gprodM`, which is a
theorem of `RBM1D/Gauss/LoopIto.lean` and is not restated here.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ### 1. The `foldr` product with an arbitrary family of "resolvents"

Nothing in step 1 uses that `G(σ)` is a resolvent, so it is stated for an arbitrary family
`g : Bool → Matrix n n ℂ`.  That is what makes it checkable by `norm_num`. -/

section GenProd

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `RBM.Gauss.gprodM` with the resolvent family `RBM.Gsig M z` replaced by an arbitrary
`g : Bool → Matrix n n ℂ`. -/
noncomputable def gprodG (g : Bool → Matrix n n ℂ) (l : List (Bool × Matrix n n ℂ)) :
    Matrix n n ℂ :=
  l.foldr (fun p X => g p.1 * p.2 * X) 1

@[simp] theorem gprodG_nil (g : Bool → Matrix n n ℂ) :
    gprodG g ([] : List (Bool × Matrix n n ℂ)) = 1 := rfl

@[simp] theorem gprodG_cons (g : Bool → Matrix n n ℂ) (p : Bool × Matrix n n ℂ)
    (l : List (Bool × Matrix n n ℂ)) :
    gprodG g (p :: l) = g p.1 * p.2 * gprodG g l := rfl

theorem gprodM_eq_gprodG (z : ℂ) (l : List (Bool × Matrix n n ℂ)) (M : Matrix n n ℂ) :
    gprodM z l M = gprodG (Gsig M z) l := rfl

theorem gprodG_append (g : Bool → Matrix n n ℂ) (l₁ l₂ : List (Bool × Matrix n n ℂ)) :
    gprodG g (l₁ ++ l₂) = gprodG g l₁ * gprodG g l₂ := by
  induction l₁ with
  | nil => simp
  | cons p l ih => simp only [List.cons_append, gprodG_cons, ih, Matrix.mul_assoc]

/-- **The `k`-th cut block**, for a general family `g`: `G(σ_k) A_k · ∏_{i>k} · ∏_{i<k} ·
G(σ_k)`.  `RBM.Gauss.loopCut` is the case `g = RBM.Gsig M z`, `A_i = E_{a_i}`
(`RBM.Gauss.loopCut_eq_cutG`). -/
noncomputable def cutG (g : Bool → Matrix n n ℂ) (l : List (Bool × Matrix n n ℂ)) (k : ℕ) :
    Matrix n n ℂ :=
  g (l.getD k (true, 0)).1 * (l.getD k (true, 0)).2
    * gprodG g (l.drop (k + 1)) * gprodG g (l.take k) * g (l.getD k (true, 0)).1

/-- Insertion of `B` in front of the `k`-th factor, written out. -/
theorem gprodG_insB (g : Bool → Matrix n n ℂ) (B : Matrix n n ℂ)
    {k : ℕ} {l : List (Bool × Matrix n n ℂ)} (hk : k < l.length) :
    gprodG g (insB B k l)
      = gprodG g (l.take k) * (g (l.getD k (true, 0)).1 * B)
        * (g (l.getD k (true, 0)).1 * (l.getD k (true, 0)).2 * gprodG g (l.drop (k + 1))) := by
  have hd : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hk
  have hg : l.getD k (true, 0) = l[k] := List.getD_eq_getElem _ _ hk
  rw [insB, gprodG_append, gprodG_cons, hd, gprodG_cons, hg]
  simp only [Matrix.mul_assoc]

/-- **The trace rotation.**  Differentiating the `k`-th factor and rotating the trace turns the
inserted product into `⟨B · (cut block)⟩`. -/
theorem trace_gprodG_insB (g : Bool → Matrix n n ℂ) (B : Matrix n n ℂ)
    {k : ℕ} {l : List (Bool × Matrix n n ℂ)} (hk : k < l.length) :
    Matrix.trace (gprodG g (insB B k l)) = Matrix.trace (B * cutG g l k) := by
  set s := (l.getD k (true, 0)).1 with hs
  set A := (l.getD k (true, 0)).2 with hA
  have h1 : gprodG g (insB B k l)
      = (gprodG g (l.take k) * g s) * (B * (g s * A * gprodG g (l.drop (k + 1)))) := by
    rw [gprodG_insB g B hk, ← hs, ← hA]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, cutG, ← hs, ← hA]
  simp only [Matrix.mul_assoc]

end GenProd

/-! ### 2. The numerical anchor for the trace rotation -/

section Sanity

open scoped ComplexOrder

end Sanity

/-! ### 3. Specialising to the loop: `RBM.Gauss.loopCut` is `RBM.Gauss.cutG` -/

section Bridge

variable {L W : ℕ} [NeZero L]

/-- The list of `(charge, block)` pairs of a loop, with the blocks turned into matrices. -/
private noncomputable abbrev embEblk (L W : ℕ) :
    Bool × ZMod L → Bool × Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  Prod.map id (Eblk L W)

theorem gprodG_map_Eblk (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (l : List (Bool × ZMod L)) :
    gprodG (Gsig M z) (l.map (embEblk L W)) = prodList L W M z l := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.map_cons, gprodG_cons, ih]; rfl

omit [NeZero L] in
theorem zip_map_Eblk (I : LoopIdx (ZMod L)) :
    I.σ.zip (I.a.map (Eblk L W)) = (I.σ.zip I.a).map (embEblk L W) :=
  List.zip_map_right

/-- **`RBM.Gauss.loopCut` is `RBM.Gauss.cutG`** of the corresponding list of matrices. -/
theorem loopCut_eq_cutG (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) {k : ℕ} (hk : k < (I.σ.zip I.a).length) :
    loopCut L W M z I k = cutG (Gsig M z) ((I.σ.zip I.a).map (embEblk L W)) k := by
  set lp := I.σ.zip I.a with hlp
  have hkm : k < (lp.map (embEblk L W)).length := by rwa [List.length_map]
  have hg : (lp.map (embEblk L W)).getD k (true, 0) = embEblk L W (lp.getD k (true, 0)) := by
    rw [List.getD_eq_getElem _ _ hkm, List.getD_eq_getElem _ _ hk, List.getElem_map]
  rw [loopCut, cutG, hg]
  simp only [embEblk, Prod.map_fst, Prod.map_snd, id_eq]
  rw [← List.map_drop, ← List.map_take, gprodG_map_Eblk, gprodG_map_Eblk]

end Bridge

/-! ### 4. The first coordinate derivative of the loop observable -/

section CoordD1

variable {d : Dims} {N : ℕ}

/-- **The hypothesis `hdiff` of `RBM.Gauss.emart_Uker`**: the loop observable is differentiable
in the matrix, everywhere (it
pre-composes with the Hermitian projection, so no invertibility hypothesis is needed). -/
theorem differentiableAt_loopObs {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (ZMod (d.L N))}
    (hwf : I.WF) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    DifferentiableAt ℝ (loopObs d N z I) M :=
  ((bddC2_loopObs hz (abs_pos.mpr hz) le_rfl hwf).contDiff.differentiable
    (by norm_num)).differentiableAt

/-- **The first coordinate derivative of the loop observable**, Leibniz over the `n` `G`-edges:
the `k`-th summand is `⟨B_{ij,b} · R_k⟩` with `R_k` the cut block `RBM.Gauss.loopCut`. -/
theorem coordD1_loopObs_eq {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hz : z.im ≠ 0) (hM : M.IsHermitian) (hwf : I.WF)
    (i j : d.Idx N) (b : Bool) (hb : i ≠ j ∨ b = true) :
    coordD1 d N (loopObs d N z I) M (i, j, b)
      = -∑ k ∈ Finset.range I.a.length,
          Matrix.trace (Bmat d N i j b * loopCut (d.L N) (d.W N) M z I k) := by
  have hB : (Bmat d N i j b).IsHermitian := isHermitian_Bmat_of i j b hb
  set Bm := Bmat d N i j b with hBm
  set lp := I.σ.zip I.a with hlp
  set l0 := lp.map (embEblk (d.L N) (d.W N)) with hl0
  have hlplen : lp.length = I.a.length := by
    rw [hlp, List.length_zip, hwf, min_self]
  have hlen : l0.length = I.a.length := by rw [hl0, List.length_map, hlplen]
  have hzip : I.σ.zip (I.a.map (Eblk (d.L N) (d.W N))) = l0 := zip_map_Eblk I
  have hC : ContDiff ℝ 1 (loopObs d N z I) :=
    (bddC2_loopObs hz (abs_pos.mpr hz) le_rfl hwf).contDiff.of_le (by norm_num)
  have hfd : FiniteDimensional ℝ (Matrix (d.Idx N) (d.Idx N) ℂ) := by infer_instance
  set T : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (d.Idx N) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hTapp : ∀ X, T X = Matrix.trace X := fun _ => rfl
  -- the observable along the line is the traced loop product
  have hloop : (fun s : ℝ => loopObs d N z I (M + s • Bm))
      = fun s : ℝ => Matrix.trace (gprodM z l0 (M + s • Bm)) := by
    funext s
    rw [loopObs_of_isHermitian (isHermitian_add_smul hM hB s), gloop,
      ← gprodM_zip_map_eq_gloopProd, hzip]
  have ha : HasDerivAt (fun s : ℝ => loopObs d N z I (M + s • Bm))
      (fderiv ℝ (loopObs d N z I) (M + (0 : ℝ) • Bm) Bm) 0 := hasDerivAt_dir hC M Bm 0
  have hb2 : HasDerivAt (fun s : ℝ => Matrix.trace (gprodM z l0 (M + s • Bm)))
      (Matrix.trace (-∑ k ∈ Finset.range l0.length,
        gprodM z (insB Bm k l0) (M + (0 : ℝ) • Bm))) 0 := by
    have h := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_gprodM hM hB hz l0 0)
    simpa only [hTapp, Function.comp_def] using h
  rw [hloop] at ha
  have hkey := ha.unique hb2
  have hzero : M + (0 : ℝ) • Bm = M := by simp
  rw [hzero] at hkey
  have hgoal : coordD1 d N (loopObs d N z I) M (i, j, b)
      = fderiv ℝ (loopObs d N z I) M Bm := rfl
  rw [hgoal, hkey, Matrix.trace_neg, Matrix.trace_sum, hlen]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < lp.length := by rw [hlplen]; exact Finset.mem_range.mp hk
  have hk0 : k < l0.length := by rw [hlen, ← hlplen]; exact hk'
  rw [gprodM_eq_gprodG, trace_gprodG_insB _ _ hk0, ← loopCut_eq_cutG M z I hk']

end CoordD1

/-! ### 5. The Wirtinger combination selects the `(j,i)` entry -/

section TraceBmat

variable {d : Dims} {N : ℕ}

/-- `⟨B_{ij,b} R⟩` off the diagonal: two entries of `R`, transposed. -/
theorem trace_Bmat_mul_of_ne {i j : d.Idx N} (hij : i ≠ j) (b : Bool)
    (R : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Matrix.trace (Bmat d N i j b * R)
      = (if b then (1 : ℂ) else Complex.I) * R j i
        + (if b then (1 : ℂ) else -Complex.I) * R i j := by
  have h : ∀ a : d.Idx N, (Bmat d N i j b * R) a a
      = (if b then (1 : ℂ) else Complex.I)
          * ((1 : Matrix (d.Idx N) (d.Idx N) ℂ) a i * R j a)
        + (if b then (1 : ℂ) else -Complex.I)
          * ((1 : Matrix (d.Idx N) (d.Idx N) ℂ) a j * R i a) := by
    intro a
    have hx := mul_Bmat_mul_apply_of_ne (M := (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) (M' := R)
      hij b a a
    rwa [Matrix.one_mul] at hx
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, h, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite,
    mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j]
  simp

/-- `⟨B_{ii,+} R⟩` on the diagonal. -/
theorem trace_Bmat_mul_diag (i : d.Idx N) (R : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Matrix.trace (Bmat d N i i true * R) = R i i := by
  have h : ∀ a : d.Idx N, (Bmat d N i i true * R) a a
      = (1 : Matrix (d.Idx N) (d.Idx N) ℂ) a i * R i a := by
    intro a
    have hx := mul_Bmat_mul_apply_diag (M := (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) (M' := R) i a a
    rwa [Matrix.one_mul] at hx
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, h, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp

/-- **The Wirtinger derivative of the loop observable**: `∂_{(H)_ij} L_{σ,a}` is minus the sum,
over the `n` `G`-edges, of the `(j,i)` entry of the cut block `RBM.Gauss.loopCut`.

The transposition `(j,i)` is not a decoration: the `(i,j)` entry is in general a different
number. -/
theorem wirtFirst_loopObs_eq {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hz : z.im ≠ 0) (hM : M.IsHermitian) (hwf : I.WF)
    (i j : d.Idx N) :
    wirtFirst d N (loopObs d N z I) M i j
      = -∑ k ∈ Finset.range I.a.length, loopCut (d.L N) (d.W N) M z I k j i := by
  rw [wirtFirst]
  split_ifs with hij
  · subst hij
    rw [coordD1_loopObs_eq hz hM hwf i i true (Or.inr rfl)]
    congr 1
    exact Finset.sum_congr rfl fun k _ => trace_Bmat_mul_diag i _
  · rw [coordD1_loopObs_eq hz hM hwf i j true (Or.inl hij),
      coordD1_loopObs_eq hz hM hwf i j false (Or.inl hij)]
    have ht : ∀ k : ℕ, Matrix.trace (Bmat d N i j true * loopCut (d.L N) (d.W N) M z I k)
        = loopCut (d.L N) (d.W N) M z I k j i + loopCut (d.L N) (d.W N) M z I k i j := by
      intro k
      rw [trace_Bmat_mul_of_ne hij true _]
      norm_num
    have hf : ∀ k : ℕ, Matrix.trace (Bmat d N i j false * loopCut (d.L N) (d.W N) M z I k)
        = Complex.I * loopCut (d.L N) (d.W N) M z I k j i
          + -Complex.I * loopCut (d.L N) (d.W N) M z I k i j := by
      intro k
      rw [trace_Bmat_mul_of_ne hij false _]
      norm_num
    simp only [ht, hf]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (2⁻¹ * loopCut (d.L N) (d.W N) M z I k j i
      - 2⁻¹ * loopCut (d.L N) (d.W N) M z I k i j) * hI

end TraceBmat

/-! ### 6. The chain rule, and the three hypothesis slots of `RBM1D/Gauss/DischargeBDG.lean` -/

section Split

variable {d : Dims} {N : ℕ}

/-- **The chain rule `E^{(M)}_{σ,a}(α) = ∑_{k=1}^{n} E^{(M)}_{σ,a}(α,k)` of §5.2.**

This is the hypothesis `hsplit` of `RBM.EEUker.quadVarPairs_Uker_le_norm_eeArg`, discharged.
The hypothesis `hM` is needed and cannot be dropped: `RBM.Gauss.emart` reads `M` through the
Hermitian projection and `RBM.Gauss.emartEdge` reads it raw. -/
theorem emart_eq_sum_emartEdge {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hz : z.im ≠ 0) (hM : M.IsHermitian) (hwf : I.WF)
    (i j : d.Idx N) :
    emart d N z I M i j = ∑ k ∈ Finset.range I.a.length, emartEdge d N z I M k i j := by
  rw [emart, EmartCoeff, wirtFirst_loopObs_eq hz hM hwf i j, mul_neg, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [emartEdge]
  ring

/-- The same with the number of edges given as an arbitrary `n` matching the loop length, the
shape the hypothesis slots are written in. -/
theorem emart_eq_sum_emartEdge' {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hz : z.im ≠ 0) (hM : M.IsHermitian) (hwf : I.WF)
    {m : ℕ} (hm : I.a.length = m) (i j : d.Idx N) :
    emart d N z I M i j = ∑ k ∈ Finset.range m, emartEdge d N z I M k i j := by
  rw [← hm]; exact emart_eq_sum_emartEdge hz hM hwf i j

end Split

/-! ### 7. Satisfiability of the hypotheses -/

section Consistent

end Consistent

end RBM.Gauss


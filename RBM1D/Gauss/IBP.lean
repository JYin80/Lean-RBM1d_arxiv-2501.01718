/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucAvg
import RBM1D.Gauss.MomentGronwall
import RBM1D.Gauss.IBPPoly
import RBM1D.Gauss.Hierarchy
import RBM1D.Gauss.SteinMatrix

/-!
# T83: the Gaussian integration-by-parts display of p. 50

The target is the hypothesis `hIBP` of `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`
(T88, `RBM1D/Gauss/FlucAvg.lean`), i.e. the display on p. 50 of the paper:

  `E_i(G_ii - m) = E_i[m(-H - tm)G]_ii = t m² ∑_k S_ik (G_kk - m) + O≺(Ψ²)`.

It splits into three steps.

1. **The algebraic identity** `G - m = m(-H - tm)G`, which rests on `m = -(tm + z_t)⁻¹`.
   That is this file's first section, and it is pure matrix algebra: no probability.
2. **Gaussian integration by parts** for each entry `H_ik`, i.e. the matrix Stein identity
   `RBM.Gauss.matrixStein` of T70 (`RBM1D/Gauss/SteinMatrix.lean`), which replaces `ω_α` by
   `gvar α · ∂_α`.  The derivative of a resolvent entry is again a product of resolvent
   entries, and `‖G‖ ≤ η⁻¹` is a *deterministic global* bound (T77's envelope), so the
   global boundedness hypotheses of `MatrixStein` are met without any cutoff.
3. **Removing the minor superscript** with (4.9), i.e. `E_i(G_kk - m) = G_kk - m + O≺(Ψ²)`,
   which is T85 (`RBM1D/Gauss/MinorReplace.lean`).

**Do not change** the statement `hIBP` is consumed at: `RBM1D/Green/EntryBound.lean` and
`RBM1D/Gauss/FlucAvg.lean` are both frozen interfaces.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix.Norms.L2Operator NNReal

/-! ### Step 1: the algebraic identity `G - m = m(-H - tm)G`

Everything here is deterministic. -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `t·m + z_t = m + E`: the flow keeps the self-consistent equation in the form of
`RBM.mE_mul`. -/
theorem smul_add_zt (E t : ℝ) : (t : ℂ) * mE E + zt E t = mE E + E := by
  simp only [zt]
  ring

/-- **`m = -(t m + z_t)⁻¹`**, the self-consistent equation along the flow.  This is the one
fact the identity of this section rests on. -/
theorem mE_mul_smul_add_zt {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    mE E * ((t : ℂ) * mE E + zt E t) = -1 := by
  rw [smul_add_zt]
  exact mE_mul hE

/-- **The identity `G - m = m(-H - tm)G` of p. 50.**  Taking the `ii` entry of this and
applying `E_i` is the first step of the integration-by-parts display. -/
theorem green_sub_smul_one_eq {H : Matrix n n ℂ} (hH : H.IsHermitian) {E t : ℝ}
    (hE : |E| ≤ 2) (hz : (zt E t).im ≠ 0) :
    green H (zt E t) - mE E • (1 : Matrix n n ℂ)
      = mE E • ((-H - ((t : ℂ) * mE E) • (1 : Matrix n n ℂ)) * green H (zt E t)) := by
  have hGH : (H - (zt E t) • (1 : Matrix n n ℂ)) * green H (zt E t) = 1 :=
    sub_mul_green_of_im hH hz
  have hkey : mE E * ((t : ℂ) * mE E + zt E t) = -1 := mE_mul_smul_add_zt hE t
  have hsplit : (-H - ((t : ℂ) * mE E) • (1 : Matrix n n ℂ))
      = -(H - (zt E t) • (1 : Matrix n n ℂ))
        - (((t : ℂ) * mE E + zt E t) • (1 : Matrix n n ℂ)) := by
    rw [add_smul]
    abel
  rw [hsplit, sub_mul, neg_mul, hGH, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_neg,
    smul_smul, hkey, neg_smul, one_smul]
  abel

end Algebra

/-! ### Step 2a: moving one Gaussian coordinate

Stein's identity replaces `ω_c` by `gvar_c · ∂_c`, so the display needs the derivative of a
resolvent entry along a single Gaussian coordinate.  Both lemmas below are pathwise: no
integration yet. -/

section Deriv

variable {d : Dims} {N : ℕ}

/-- **Moving the Gaussian coordinate `p` moves `H_u` along `√u · B_p`.**  This is extracted
from the proof of `RBM.Gauss.hasDerivAt_coordD1_update`, which states it only for a test
function; the integration-by-parts display needs it for the resolvent. -/
theorem hasDerivAt_Hflow_update (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    HasDerivAt (fun t : ℝ => Hflow d N u (Function.update ω (crd d N p) t))
      (Real.sqrt u • Bmat d N p.1 p.2.1 p.2.2) (ω (crd d N p)) := by
  set c := crd d N p with hc
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Hflow d N u (Function.update ω c t)
      = Hflow d N u ω + (Real.sqrt u * (t - ω c)) • B := by
    intro t
    rw [Hflow_eq_realSmul, Hflow_eq_realSmul, Xmat_update d N ω hp t, smul_add, smul_smul]
  have hscal : HasDerivAt (fun t : ℝ => Real.sqrt u * (t - ω c)) (Real.sqrt u) (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul (Real.sqrt u)
  have h1 : HasDerivAt (fun t : ℝ => Hflow d N u ω + (Real.sqrt u * (t - ω c)) • B)
      (Real.sqrt u • B) (ω c) := (hscal.smul_const B).const_add _
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hline t)

/-- **The coordinate derivative of the resolvent**: `∂_c G_u = -√u · G_u B_c G_u`.
The derivative of a resolvent is again a product of resolvents, which is why the global
bound `‖G‖ ≤ η⁻¹` makes every Stein hypothesis free. -/
theorem hasDerivAt_green_Hflow_update (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Ω d) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    HasDerivAt (fun t : ℝ => green (Hflow d N u (Function.update ω (crd d N p) t)) z)
      (-(Real.sqrt u) • (green (Hflow d N u ω) z * Bmat d N p.1 p.2.1 p.2.2
        * green (Hflow d N u ω) z)) (ω (crd d N p)) := by
  set c := crd d N p with hc
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  set G := green (Hflow d N u ω) z with hG
  have hBherm : B.IsHermitian := Bmat_isHermitian hp
  have hres : ∀ t : ℝ, resH z (Hflow d N u (Function.update ω c t))
      = green (Hflow d N u (Function.update ω c t)) z :=
    fun t => resH_of_isHermitian (Hflow_isHermitian d N u _)
  have hMG : resH z (Hflow d N u ω) = G := resH_of_isHermitian (Hflow_isHermitian d N u ω)
  have hpath := hasDerivAt_Hflow_update d N u ω hp
  have hself : Hflow d N u (Function.update ω c (ω c)) = Hflow d N u ω := by
    rw [Function.update_eq_self]
  have key := (hasFDerivAt_resH hz
    (Hflow d N u (Function.update ω c (ω c)))).comp_hasDerivAt (ω c) hpath
  rw [hself] at key
  have hval : (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix (d.Idx N) (d.Idx N) ℂ)
      (resH z (Hflow d N u ω)) (resH z (Hflow d N u ω))).comp (hermCLM (d.Idx N))))
        (Real.sqrt u • B) = -(Real.sqrt u) • (G * B * G) := by
    simp only [_root_.neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, map_smul, hermCLM_of_isHermitian hBherm,
      ContinuousLinearMap.mulLeftRight_apply, hMG]
    rw [smul_neg, neg_smul]
  rw [hval] at key
  exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hres t).symm)

end Deriv

/-! ### Step 2b: the sandwich collapses to two entries

`B_p` has at most two nonzero entries, so `G B_p G` is a sum of two products of resolvent
entries.  This is the Lean form of the paper's `∂_{H_ij} G_ac = -G_ai G_jc`. -/

section Sandwich

variable {d : Dims} {N : ℕ}

/-- Off the diagonal, `M B_{ij,b} M'` has exactly two terms. -/
theorem mul_Bmat_mul_apply_of_ne {M M' : Matrix (d.Idx N) (d.Idx N) ℂ} {i j : d.Idx N}
    (hij : i ≠ j) (b : Bool) (a c : d.Idx N) :
    (M * Bmat d N i j b * M') a c
      = (if b then (1 : ℂ) else Complex.I) * (M a i * M' j c)
        + (if b then (1 : ℂ) else -Complex.I) * (M a j * M' i c) := by
  have hrow : ∀ l : d.Idx N, (M * Bmat d N i j b) a l
      = (if l = j then (if b then (1 : ℂ) else Complex.I) * M a i else 0)
        + (if l = i then (if b then (1 : ℂ) else -Complex.I) * M a j else 0) := by
    intro l
    rw [Matrix.mul_apply]
    by_cases hlj : l = j
    · have hli : ¬ l = i := fun h => hij (h ▸ hlj)
      rw [if_pos hlj, if_neg hli, add_zero]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [Bmat_apply, if_neg (fun h => hk h.1), if_neg (fun h => hli h.2), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · rw [Bmat_apply, if_pos ⟨rfl, hlj⟩, mul_comm]
    · by_cases hli : l = i
      · rw [if_neg hlj, if_pos hli, zero_add]
        refine (Finset.sum_eq_single j ?_ ?_).trans ?_
        · intro k _ hk
          rw [Bmat_apply, if_neg (fun h => hlj h.2), if_neg (fun h => hk h.1), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ j) h
        · rw [Bmat_apply, if_neg (fun h => hlj h.2), if_pos ⟨rfl, hli⟩, mul_comm]
      · rw [if_neg hlj, if_neg hli, add_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Bmat_apply, if_neg (fun h => hlj h.2), if_neg (fun h => hli h.2), mul_zero]
  rw [Matrix.mul_apply]
  simp only [hrow, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i,
    if_pos (Finset.mem_univ j), if_pos (Finset.mem_univ i)]
  ring

/-- On the diagonal the real tag gives a single entry.  (`⟨N, i, i, false⟩` is never a used
coordinate, so the imaginary tag does not occur there.) -/
theorem mul_Bmat_mul_apply_diag {M M' : Matrix (d.Idx N) (d.Idx N) ℂ} (i a c : d.Idx N) :
    (M * Bmat d N i i true * M') a c = M a i * M' i c := by
  have hrow : ∀ l : d.Idx N, (M * Bmat d N i i true) a l = (if l = i then M a i else 0) := by
    intro l
    rw [Matrix.mul_apply]
    by_cases hli : l = i
    · rw [if_pos hli]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [Bmat_apply, if_neg (fun h => hk h.1), if_neg (fun h => hk h.1), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · rw [Bmat_apply, if_pos ⟨rfl, hli⟩]
        simp
    · refine (Finset.sum_eq_zero fun k _ => ?_).trans (if_neg hli).symm
      rw [Bmat_apply, if_neg (fun h => hli h.2), if_neg (fun h => hli h.2), mul_zero]
  rw [Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

end Sandwich

/-! ### Step 2c: resolvent entries are tame

T104's `RBM.Gauss.gaussIBP` is Stein's identity for *polynomially bounded* test functions
(`RBM.Gauss.Tame`), which is the version the display needs: its integrand carries a factor
`H_ik`, so it is never globally bounded.  Resolvent entries themselves are tame for the
cheapest possible reason — the deterministic envelope `‖G‖ ≤ η_t⁻¹`. -/

section Tame

variable {d : Dims} {N : ℕ} {E t : ℝ}

/-- `Im z_t ≠ 0` strictly inside the flow. -/
theorem zt_im_ne_zero_of_lt_one (hE : |E| < 2) (ht : t < 1) : (zt E t).im ≠ 0 := by
  rw [← etaT_eq_zt_im]
  exact ne_of_gt (etaT_pos_of_lt_one hE ht)

/-- **Every resolvent entry is tame.**  No polynomial is needed: the entry is bounded by
`η_t⁻¹` on the whole space, so the dominating polynomial can be taken constant. -/
theorem tame_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ) (a b : d.Idx N) :
    Tame d (fun ω : Ω d => green (Hflow d N u ω) (zt E t) a b) := by
  refine ⟨?_, finDep_of_Hflow d N u (fun M => green M (zt E t) a b),
    ⟨∅, 0, (etaT E t)⁻¹, fun ω => ?_⟩⟩
  · exact Continuous.matrix_elem
      (continuous_green_comp (continuous_Hflow d N u) (Hflow_isHermitian d N u)
        (zt_im_ne_zero_of_lt_one hE ht)) a b
  · simpa using norm_green_apply_le_etaT hE ht u a b ω

end Tame

/-! ### Step 2d: reading off one entry

Stein's identity is applied to scalar test functions, so the matrix-valued derivative of
step 2a has to be pushed through the evaluation map.  For the L2 operator norm that map is
bounded with constant one (`norm_apply_le_l2_opNorm`), hence a continuous linear map. -/

section Entry

/-- Reading off the `(a, b)` entry, as a bounded `ℝ`-linear map. -/
noncomputable def entryCLM (n : Type*) [Fintype n] [DecidableEq n] (a b : n) :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun M => by
      show ‖M a b‖ ≤ 1 * ‖M‖
      simpa using norm_apply_le_l2_opNorm M a b)

@[simp] theorem entryCLM_apply {n : Type*} [Fintype n] [DecidableEq n] (a b : n)
    (M : Matrix n n ℂ) : entryCLM n a b M = M a b := rfl

variable {d : Dims} {N : ℕ}

/-- **The coordinate derivative of a resolvent entry.**  This is the scalar statement Stein's
identity consumes. -/
theorem hasDerivAt_green_apply_update (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Ω d) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) (a b : d.Idx N) :
    HasDerivAt
      (fun t : ℝ => green (Hflow d N u (Function.update ω (crd d N p) t)) z a b)
      (-(Real.sqrt u) • (green (Hflow d N u ω) z * Bmat d N p.1 p.2.1 p.2.2
        * green (Hflow d N u ω) z) a b) (ω (crd d N p)) := by
  have h := hasDerivAt_green_Hflow_update d N u hz ω hp
  have h2 := (entryCLM (d.Idx N) a b).hasFDerivAt.comp_hasDerivAt (ω (crd d N p)) h
  simp only [Function.comp_def, entryCLM_apply] at h2
  exact h2

end Entry

/-! ### Step 2e: the integration step

This is where the display stops being pathwise.  `RBM.Gauss.gaussIBP` (T104) replaces the
Gaussian coordinate `ω_c` by `gvar_c · ∂_c`, and `∂_c` of a resolvent entry is the sandwich
of step 2a.  The only thing to check is that both sides are tame, and for the derivative
that follows by writing the sandwich as a double sum of entries. -/

section Integral

variable {d : Dims} {N : ℕ} {E t : ℝ}

/-- A resolvent sandwich is tame: expand it as a double sum of products of entries. -/
theorem tame_green_mul_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a b : d.Idx N) :
    Tame d (fun ω : Ω d => (green (Hflow d N u ω) (zt E t) * B
      * green (Hflow d N u ω) (zt E t)) a b) := by
  have hfun : (fun ω : Ω d => (green (Hflow d N u ω) (zt E t) * B
      * green (Hflow d N u ω) (zt E t)) a b)
      = fun ω : Ω d => ∑ l : d.Idx N, ∑ k : d.Idx N,
        green (Hflow d N u ω) (zt E t) a k * B k l
          * green (Hflow d N u ω) (zt E t) l b := by
    funext ω
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [hfun]
  exact Tame.sum _ fun l _ => Tame.sum _ fun k _ =>
    ((tame_green_apply hE ht u a k).mul (Tame.const _)).mul (tame_green_apply hE ht u l b)

/-- **Gaussian integration by parts for one resolvent entry.**  `E[ω_c · G_ab]` becomes
`gvar_c · E[∂_c G_ab]`, and the derivative is the sandwich `-√u · (G B_c G)_ab`.  This is the
step where the `H_ik` factor of the p. 50 display is eliminated. -/
theorem integral_coord_mul_green_apply (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) (a b : d.Idx N) :
    ∫ ω, (ω (crd d N p) : ℂ) * green (Hflow d N u ω) (zt E t) a b ∂(P d)
      = (gvar d (crd d N p) : ℝ) * ∫ ω, -((Real.sqrt u : ℂ)
          * (green (Hflow d N u ω) (zt E t) * Bmat d N p.1 p.2.1 p.2.2
            * green (Hflow d N u ω) (zt E t)) a b) ∂(P d) := by
  refine hG.stein (crd d N p) _ _ (tame_green_apply hE ht u a b) ?_ ?_
  · exact ((Tame.const (d := d) (Real.sqrt u : ℂ)).mul
      (tame_green_mul_mul_green_apply hE ht u _ a b)).neg
  · intro ω
    have h := hasDerivAt_green_apply_update d N u (zt_im_ne_zero_of_lt_one hE ht) ω hp a b
    simpa [Complex.real_smul] using h

end Integral

/-! ### Step 2f: from one coordinate to a whole row

One matrix entry of `H` is carried by a *pair* of Gaussian coordinates (real and imaginary
tag), and the two tags have variance `S_ij/2` each.  Summing the one-coordinate identity of
step 2e over `usedCoord` therefore rebuilds `S_ij` exactly, while the two squared off-diagonal
terms — the ones carrying `c_b² = ±1` — cancel between the tags.  What survives is the paper's

  `E[(H_u G)_{aa}] = -u ∑_k S_{ak} E[G_{aa} G_{kk}]`. -/

section Row

variable {d : Dims} {N : ℕ}

/-- `(B_p (G B_p G))_{aa}` is `(1 · B_p · (G B_p G))_{aa}`, the shape
`mul_Bmat_mul_apply_of_ne` consumes. -/
theorem Bmat_mul_sandwich_diag_of_ne (G : Matrix (d.Idx N) (d.Idx N) ℂ) {x y : d.Idx N}
    (hxy : x ≠ y) (b : Bool) (a : d.Idx N) :
    (Bmat d N x y b * (G * Bmat d N x y b * G)) a a
      = (if b then (1 : ℂ) else Complex.I) * ((1 : Matrix (d.Idx N) (d.Idx N) ℂ) a x
          * (G * Bmat d N x y b * G) y a)
        + (if b then (1 : ℂ) else -Complex.I) * ((1 : Matrix (d.Idx N) (d.Idx N) ℂ) a y
          * (G * Bmat d N x y b * G) x a) := by
  have h := mul_Bmat_mul_apply_of_ne (M := (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
    (M' := G * Bmat d N x y b * G) hxy b a a
  rw [Matrix.one_mul] at h
  exact h

/-- **The two tags of an off-diagonal coordinate.**  The squared off-diagonal terms carry
opposite signs and cancel; twice `G_{xx} G_{yy}` survives. -/
theorem Bmat_sandwich_diag_add_of_ne (G : Matrix (d.Idx N) (d.Idx N) ℂ) {x y : d.Idx N}
    (hxy : x ≠ y) (a : d.Idx N) :
    (Bmat d N x y true * (G * Bmat d N x y true * G)) a a
      + (Bmat d N x y false * (G * Bmat d N x y false * G)) a a
      = 2 * ((if a = x then G x x * G y y else 0) + (if a = y then G x x * G y y else 0)) := by
  have ht := Bmat_mul_sandwich_diag_of_ne G hxy true a
  have hf := Bmat_mul_sandwich_diag_of_ne G hxy false a
  have hKt := fun (p q : d.Idx N) => mul_Bmat_mul_apply_of_ne (M := G) (M' := G) hxy true p q
  have hKf := fun (p q : d.Idx N) => mul_Bmat_mul_apply_of_ne (M := G) (M' := G) hxy false p q
  rw [ht, hf, hKt, hKt, hKf, hKf]
  simp only [Bool.false_eq_true, reduceIte]
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := hxy
    rw [Matrix.one_apply_eq, Matrix.one_apply_ne hay, ite_eq_left rfl, ite_eq_right hay]
    ring_nf
    rw [Complex.I_sq]
    ring
  · by_cases hay : a = y
    · subst hay
      rw [Matrix.one_apply_eq, Matrix.one_apply_ne hax, ite_eq_left rfl, ite_eq_right hax]
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [Matrix.one_apply_ne hax, Matrix.one_apply_ne hay, ite_eq_right hax,
        ite_eq_right hay]
      ring

/-- **The diagonal coordinate.**  `B_{ii,true} = E_{ii}`, so the sandwich is a single square. -/
theorem Bmat_sandwich_diag_diag (G : Matrix (d.Idx N) (d.Idx N) ℂ) (x a : d.Idx N) :
    (Bmat d N x x true * (G * Bmat d N x x true * G)) a a
      = if a = x then G x x * G x x else 0 := by
  have h := mul_Bmat_mul_apply_diag (M := (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
    (M' := G * Bmat d N x x true * G) x a a
  rw [Matrix.one_mul] at h
  rw [h, mul_Bmat_mul_apply_diag]
  by_cases hax : a = x
  · subst hax
    simp
  · simp [hax]

/-- The sandwich at a diagonal entry is symmetric under swapping the two indices of the
coordinate: it is quadratic in `B_p`, and the swap changes `B_p` by at most a sign. -/
theorem Bmat_sandwich_diag_swap (G : Matrix (d.Idx N) (d.Idx N) ℂ) (x y : d.Idx N) (b : Bool)
    (a : d.Idx N) :
    (Bmat d N x y b * (G * Bmat d N x y b * G)) a a
      = (Bmat d N y x b * (G * Bmat d N y x b * G)) a a := by
  by_cases hxy : x = y
  · rw [hxy]
  · cases b with
    | true => rw [Bmat_swap_true d N x y]
    | false =>
      rw [Bmat_swap_false d N hxy]
      simp

/-- **The coordinate sum of the integration-by-parts display collapses to a row of `S`.**

`∑_{p ∈ usedCoord} gvar_p (B_p G B_p G)_{aa} = ∑_k S_{ak} G_{aa} G_{kk}`: the two tags of an
off-diagonal coordinate each contribute `gvar = S/2`, the squared off-diagonal terms cancel
between them, and the diagonal coordinate (real tag only, `gvar = S`) supplies `S_{aa}G_{aa}²`. -/
theorem sum_gvar_Bmat_sandwich_diag (d : Dims) (N : ℕ) (G : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a : d.Idx N) :
    ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        (Bmat d N p.1 p.2.1 p.2.2 * (G * Bmat d N p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (Sblk (d.L N) (d.W N) a k : ℂ) * (G a a * G k k) := by
  classical
  set f : d.Idx N × d.Idx N × Bool → ℂ :=
    fun p => (Bmat d N p.1 p.2.1 p.2.2 * (G * Bmat d N p.1 p.2.1 p.2.2 * G)) a a with hf
  have hgv : ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • f p
      = ∑ p ∈ usedCoord d N,
        (if p.1 = p.2.1 then Sblk (d.L N) (d.W N) p.1 p.2.1
         else Sblk (d.L N) (d.W N) p.1 p.2.1 / 2) • f p :=
    Finset.sum_congr rfl fun p _ => by rw [gvar_crd]
  rw [hgv, show usedCoord d N = Finset.univ.filter
      (fun p : d.Idx N × d.Idx N × Bool =>
        idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
    sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N) (Sblk (d.L N) (d.W N))
      (Sblk_comm (d.L N) (d.W N)) f
      (fun x y => Bmat_sandwich_diag_swap G x y true a)
      (fun x y => Bmat_sandwich_diag_swap G x y false a)]
  -- The term at `(x, y)` splits into the `x = a` half and the `y = a` half.
  have hterm : ∀ x y : d.Idx N,
      (Sblk (d.L N) (d.W N) x y : ℝ) •
          (if x = y then f (x, x, true) else (1 / 4 : ℝ) • (f (x, y, true) + f (x, y, false)))
        = (if x = a then (2 : ℂ)⁻¹ * ((Sblk (d.L N) (d.W N) a y : ℂ) * (G a a * G y y)) else 0)
          + (if y = a then (2 : ℂ)⁻¹ * ((Sblk (d.L N) (d.W N) x a : ℂ) * (G x x * G a a))
              else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [hf, ite_true, Bmat_sandwich_diag_diag G x a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        simp only [ite_true]
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        simp only [ite_eq_right hax, ite_eq_right hxa]
        ring
    · simp only [hf, ite_eq_right hxy, Bmat_sandwich_diag_add_of_ne G hxy a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        have hya : ¬ (y = a) := fun h => hxy h.symm
        simp only [ite_true, ite_eq_right hxy, ite_eq_right hya]
        push_cast
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        by_cases hay : a = y
        · subst hay
          simp only [ite_true, ite_eq_right hax, ite_eq_right hxa]
          push_cast
          ring
        · have hya : ¬ (y = a) := fun h => hay h.symm
          simp only [ite_eq_right hax, ite_eq_right hay, ite_eq_right hxa, ite_eq_right hya]
          push_cast
          ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y : d.Idx N =>
      if x = a then (2 : ℂ)⁻¹ * ((Sblk (d.L N) (d.W N) a y : ℂ) * (G a a * G y y)) else 0)]
  simp only [Finset.sum_ite_eq' Finset.univ a, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sblk_comm (d.L N) (d.W N) k a]
  ring

end Row


section IntegralRow

variable {d : Dims} {N : ℕ} {E t : ℝ}

/-- Multiplying on the left by a **constant** matrix is a finite linear combination of entries,
so it passes through the integral. -/
theorem integral_const_matrix_mul_apply {F : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    {g : Ω d → ℂ} (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a : d.Idx N)
    (hint : ∀ l, Integrable (fun ω => g ω * F ω l a) (P d)) :
    ∫ ω, g ω * (B * F ω) a a ∂(P d) = ∑ l, B a l * ∫ ω, g ω * F ω l a ∂(P d) := by
  have hpt : ∀ ω, g ω * (B * F ω) a a = ∑ l, B a l * (g ω * F ω l a) := by
    intro ω
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [hpt]
  rw [MeasureTheory.integral_finsetSum _ (fun l _ => (hint l).const_mul (B a l))]
  exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _

/-- **Integration by parts for a whole row.**  `E[ω_p (B_p G)_{aa}]` collapses to the
`gvar`-weighted sandwich `(B_p G B_p G)_{aa}`: the two entries of `B_p` are handled by
`integral_coord_mul_green_apply` one at a time and recombined. -/
theorem integral_coord_mul_Bmat_mul_green_diag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    (u : ℝ) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) (a : d.Idx N) :
    ∫ ω, (ω (crd d N p) : ℂ)
        * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t)) a a ∂(P d)
      = (gvar d (crd d N p) : ℝ) * ∫ ω, -((Real.sqrt u : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u ω) (zt E t)
            * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t))) a a) ∂(P d) := by
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  have hint1 : ∀ l : d.Idx N, Integrable
      (fun ω : Ω d => (ω (crd d N p) : ℂ) * green (Hflow d N u ω) (zt E t) l a) (P d) :=
    fun l => ((Tame.coord (crd d N p)).mul (tame_green_apply hE ht u l a)).integrable hG
  have hint2 : ∀ l : d.Idx N, Integrable
      (fun ω : Ω d => (1 : ℂ) * (green (Hflow d N u ω) (zt E t) * B
        * green (Hflow d N u ω) (zt E t)) l a) (P d) :=
    fun l => ((Tame.const (d := d) 1).mul
      (tame_green_mul_mul_green_apply hE ht u B l a)).integrable hG
  rw [integral_const_matrix_mul_apply B a hint1]
  have hstep : ∀ l : d.Idx N,
      ∫ ω, (ω (crd d N p) : ℂ) * green (Hflow d N u ω) (zt E t) l a ∂(P d)
        = (gvar d (crd d N p) : ℝ) * -((Real.sqrt u : ℂ)
            * ∫ ω, (green (Hflow d N u ω) (zt E t) * B
              * green (Hflow d N u ω) (zt E t)) l a ∂(P d)) := by
    intro l
    rw [integral_coord_mul_green_apply hG hE ht u hp l a, integral_neg, integral_const_mul]
  simp only [hstep]
  have hrev : ∫ ω, (1 : ℂ) * (B * (green (Hflow d N u ω) (zt E t) * B
      * green (Hflow d N u ω) (zt E t))) a a ∂(P d)
      = ∑ l, B a l * ∫ ω, (1 : ℂ) * (green (Hflow d N u ω) (zt E t) * B
        * green (Hflow d N u ω) (zt E t)) l a ∂(P d) :=
    integral_const_matrix_mul_apply B a hint2
  simp only [one_mul] at hrev
  rw [integral_neg, integral_const_mul, hrev, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `(B G)_{ac}` is tame for a constant `B`. -/
theorem tame_const_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a c : d.Idx N) :
    Tame d (fun ω : Ω d => (B * green (Hflow d N u ω) (zt E t)) a c) := by
  have hfun : (fun ω : Ω d => (B * green (Hflow d N u ω) (zt E t)) a c)
      = fun ω : Ω d => ∑ l, B a l * green (Hflow d N u ω) (zt E t) l c := by
    funext ω
    rw [Matrix.mul_apply]
  rw [hfun]
  exact Tame.sum _ fun l _ => (Tame.const _).mul (tame_green_apply hE ht u l c)

/-- `(B (G B G))_{ac}` is tame for a constant `B`. -/
theorem tame_const_mul_sandwich_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a c : d.Idx N) :
    Tame d (fun ω : Ω d => (B * (green (Hflow d N u ω) (zt E t) * B
      * green (Hflow d N u ω) (zt E t))) a c) := by
  have hfun : (fun ω : Ω d => (B * (green (Hflow d N u ω) (zt E t) * B
      * green (Hflow d N u ω) (zt E t))) a c)
      = fun ω : Ω d => ∑ l, B a l * (green (Hflow d N u ω) (zt E t) * B
        * green (Hflow d N u ω) (zt E t)) l c := by
    funext ω
    rw [Matrix.mul_apply]
  rw [hfun]
  exact Tame.sum _ fun l _ =>
    (Tame.const _).mul (tame_green_mul_mul_green_apply hE ht u B l c)

/-- The complex form of `sum_gvar_Bmat_sandwich_diag`. -/
theorem sum_gvar_Bmat_sandwich_diag_mul (d : Dims) (N : ℕ)
    (G : Matrix (d.Idx N) (d.Idx N) ℂ) (a : d.Idx N) :
    ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ) *
        (Bmat d N p.1 p.2.1 p.2.2 * (G * Bmat d N p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (Sblk (d.L N) (d.W N) a k : ℂ) * (G a a * G k k) := by
  rw [← sum_gvar_Bmat_sandwich_diag d N G a]
  exact Finset.sum_congr rfl fun p _ => Complex.real_smul.symm

/-- **Step (a): the whole row.**  `E[(H_u G)_{aa}] = -u ∑_k S_{ak} E[G_{aa} G_{kk}]`.

This is the p. 50 display `E[∑_k H_{ak} G_{ka}]` after Gaussian integration by parts: the
coordinate decomposition of `H_u` turns the left side into a sum over `usedCoord`, each term is
integrated by parts by `integral_coord_mul_Bmat_mul_green_diag`, and the resulting
`gvar`-weighted sandwiches recombine into a row of `S` by `sum_gvar_Bmat_sandwich_diag`. -/
theorem integral_Hflow_mul_green_diag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : 0 ≤ u) (a : d.Idx N) :
    ∫ ω, (Hflow d N u ω * green (Hflow d N u ω) (zt E t)) a a ∂(P d)
      = -((u : ℂ) * ∑ k, (Sblk (d.L N) (d.W N) a k : ℂ)
          * ∫ ω, green (Hflow d N u ω) (zt E t) a a
              * green (Hflow d N u ω) (zt E t) k k ∂(P d)) := by
  classical
  have hsq : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
  -- the coordinate decomposition of `H_u`
  have h1 : ∀ ω : Ω d, (Hflow d N u ω * green (Hflow d N u ω) (zt E t)) a a
      = ∑ p ∈ usedCoord d N, (Real.sqrt u : ℂ) * ((ω (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t)) a a) := by
    intro ω
    rw [Hflow_eq_realSmul, Xmat_eq_sum, Matrix.smul_mul, Finset.sum_mul]
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
      Finset.mul_sum]
  -- each summand is integrable
  have hintp : ∀ p ∈ usedCoord d N, Integrable
      (fun ω : Ω d => (Real.sqrt u : ℂ) * ((ω (crd d N p) : ℂ)
        * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t)) a a)) (P d) :=
    fun p _ => ((Tame.const (d := d) (Real.sqrt u : ℂ)).mul
      ((Tame.coord (crd d N p)).mul
        (tame_const_mul_green_apply hE ht u (Bmat d N p.1 p.2.1 p.2.2) a a))).integrable hG
  simp only [h1]
  rw [MeasureTheory.integral_finsetSum _ hintp]
  -- integrate by parts coordinate by coordinate
  have hstep : ∀ p ∈ usedCoord d N,
      ∫ ω, (Real.sqrt u : ℂ) * ((ω (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t)) a a) ∂(P d)
        = -((u : ℂ) * (((gvar d (crd d N p) : ℝ) : ℂ)
            * ∫ ω, (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u ω) (zt E t)
              * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t))) a a ∂(P d))) := by
    intro p hp
    rw [integral_const_mul, integral_coord_mul_Bmat_mul_green_diag hG hE ht u hp a,
      integral_neg, integral_const_mul, ← hsq]
    ring
  rw [Finset.sum_congr rfl hstep]
  -- pull the constant out and recombine the coordinate sum
  have hintq : ∀ p ∈ usedCoord d N, Integrable
      (fun ω : Ω d => ((gvar d (crd d N p) : ℝ) : ℂ)
        * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u ω) (zt E t)
          * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t))) a a) (P d) :=
    fun p _ => ((Tame.const (d := d) ((gvar d (crd d N p) : ℝ) : ℂ)).mul
      (tame_const_mul_sandwich_apply hE ht u (Bmat d N p.1 p.2.1 p.2.2) a a)).integrable hG
  have hintk : ∀ k ∈ (Finset.univ : Finset (d.Idx N)), Integrable
      (fun ω : Ω d => (Sblk (d.L N) (d.W N) a k : ℂ)
        * (green (Hflow d N u ω) (zt E t) a a * green (Hflow d N u ω) (zt E t) k k)) (P d) :=
    fun k _ => ((Tame.const (d := d) ((Sblk (d.L N) (d.W N) a k : ℝ) : ℂ)).mul
      ((tame_green_apply hE ht u a a).mul (tame_green_apply hE ht u k k))).integrable hG
  have hcollapse : ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ)
        * ∫ ω, (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u ω) (zt E t)
          * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t))) a a ∂(P d)
      = ∑ k, (Sblk (d.L N) (d.W N) a k : ℂ)
        * ∫ ω, green (Hflow d N u ω) (zt E t) a a
            * green (Hflow d N u ω) (zt E t) k k ∂(P d) := by
    have hL : ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ)
          * ∫ ω, (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u ω) (zt E t)
            * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t))) a a ∂(P d)
        = ∫ ω, ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ)
            * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u ω) (zt E t)
              * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u ω) (zt E t))) a a ∂(P d) := by
      rw [MeasureTheory.integral_finsetSum _ hintq]
      exact Finset.sum_congr rfl fun p _ => (integral_const_mul _ _).symm
    have hR : ∑ k, (Sblk (d.L N) (d.W N) a k : ℂ)
          * ∫ ω, green (Hflow d N u ω) (zt E t) a a
              * green (Hflow d N u ω) (zt E t) k k ∂(P d)
        = ∫ ω, ∑ k, (Sblk (d.L N) (d.W N) a k : ℂ)
            * (green (Hflow d N u ω) (zt E t) a a
              * green (Hflow d N u ω) (zt E t) k k) ∂(P d) := by
      rw [MeasureTheory.integral_finsetSum _ hintk]
      exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    rw [hL, hR]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      sum_gvar_Bmat_sandwich_diag_mul d N (green (Hflow d N u ω) (zt E t)) a)
  rw [← hcollapse, Finset.sum_neg_distrib, ← Finset.mul_sum]

end IntegralRow

/-! ### Step 2g: the same, inside `E_i`

The p. 50 display is a statement about `E_i`, not about `E`.  That costs nothing extra: `E_i`
is *itself* an integral against `P d` of the integrand composed with `RBM.Gauss.rowSplit`
(T84), and `rowSplit` commutes with updating a row-`i` coordinate, so `gaussIBP` applies to it
verbatim.  The only new input is that tameness survives freezing the coordinates off row `i`. -/

section CondIBP

variable {d : Dims} {N : ℕ} {E t : ℝ}

/-- Updating a **row-`k`** coordinate commutes with the splitting: `rowSplit` reads that
coordinate from its second argument. -/
theorem rowSplit_update (k : d.Idx N) (ω ω' : Ω d) {c : Coord d} (hc : IsRowCoord d N k c)
    (s : ℝ) :
    rowSplit d N k ω (Function.update ω' c s) = Function.update (rowSplit d N k ω ω') c s := by
  funext e
  by_cases hec : e = c
  · subst hec
    rw [rowSplit_apply_of_isRowCoord k ω _ hc, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hec]
    unfold rowSplit
    split_ifs with h
    · rw [Function.update_of_ne hec]
    · rfl

/-- `ω' ↦ rowSplit k ω ω'` is continuous: every coordinate is either a projection or a
constant. -/
theorem continuous_rowSplit_right (d : Dims) (N : ℕ) (k : d.Idx N) (ω : Ω d) :
    Continuous fun ω' : Ω d => rowSplit d N k ω ω' := by
  refine continuous_pi fun c => ?_
  unfold rowSplit
  by_cases h : IsRowCoord d N k c
  · simpa [h] using continuous_apply c
  · simpa [h] using continuous_const (y := ω c)

/-- `polyW` of a split point is bounded by the product of the two `polyW`s. -/
theorem polyW_rowSplit_le (k : d.Idx N) (I : Finset (Coord d)) (ω ω' : Ω d) :
    polyW I (rowSplit d N k ω ω') ≤ polyW I ω * polyW I ω' := by
  have hb : ∀ c ∈ I, |rowSplit d N k ω ω' c| ≤ |ω c| + |ω' c| := by
    intro c _
    unfold rowSplit
    split_ifs with h
    · have : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      linarith
    · have : (0 : ℝ) ≤ |ω' c| := abs_nonneg _
      linarith
  have hsum : ∑ c ∈ I, |rowSplit d N k ω ω' c| ≤ (∑ c ∈ I, |ω c|) + ∑ c ∈ I, |ω' c| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hb
  have hA : (0 : ℝ) ≤ ∑ c ∈ I, |ω c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB : (0 : ℝ) ≤ ∑ c ∈ I, |ω' c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold polyW
  nlinarith

/-- **Tameness is preserved by freezing the coordinates off row `k`.** -/
theorem Tame.comp_rowSplit {f : Ω d → ℂ} (hf : Tame d f) (k : d.Idx N) (ω : Ω d) :
    Tame d (fun ω' : Ω d => f (rowSplit d N k ω ω')) := by
  obtain ⟨I, n, C, hb⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  refine ⟨hf.cont.comp (continuous_rowSplit_right d N k ω), ⟨J, fun ω' ω'' h => ?_⟩,
    ⟨I, n, C * polyW I ω ^ n, fun ω' => ?_⟩⟩
  · refine hJ _ _ fun e he => ?_
    unfold rowSplit
    split_ifs with hrow
    · exact h e he
    · rfl
  · have hC : 0 ≤ C := by
      have hp : (0 : ℝ) < polyW I (fun _ => 0) ^ n := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f fun _ => 0), hb fun _ => 0]
    have hle : polyW I (rowSplit d N k ω ω') ^ n ≤ polyW I ω ^ n * polyW I ω' ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (le_of_lt (polyW_pos _ _)) (polyW_rowSplit_le k I ω ω') n
    calc ‖f (rowSplit d N k ω ω')‖ ≤ C * polyW I (rowSplit d N k ω ω') ^ n :=
          hb (rowSplit d N k ω ω')
      _ ≤ C * (polyW I ω ^ n * polyW I ω' ^ n) := mul_le_mul_of_nonneg_left hle hC
      _ = C * polyW I ω ^ n * polyW I ω' ^ n := by ring

/-- **Gaussian integration by parts inside `E_k`.**  For a coordinate of row `k`, `E_k` is an
integral against the *same* product measure in the split variable, so T104's `gaussIBP` applies
verbatim once the integrand is composed with `rowSplit`. -/
theorem condRow_coord_mul (hG : GaussIBP d) (k : d.Idx N) {c : Coord d}
    (hc : IsRowCoord d N k c) (g g' : Ω d → ℂ) (hg : Tame d g) (hg' : Tame d g')
    (hd : ∀ η : Ω d, HasDerivAt (fun s : ℝ => g (Function.update η c s)) (g' η) (η c))
    (ω : Ω d) :
    condRow d N k (fun η => (η c : ℂ) * g η) ω = (gvar d c : ℝ) * condRow d N k g' ω := by
  rw [condRow_apply, condRow_apply]
  have hlhs : ∀ ω' : Ω d,
      ((rowSplit d N k ω ω' c : ℝ) : ℂ) * g (rowSplit d N k ω ω')
        = (ω' c : ℂ) * g (rowSplit d N k ω ω') := by
    intro ω'
    rw [rowSplit_apply_of_isRowCoord k ω ω' hc]
  simp only [hlhs]
  refine hG.stein c _ _ (hg.comp_rowSplit k ω) (hg'.comp_rowSplit k ω) fun ω' => ?_
  have hup : ∀ s : ℝ, g (rowSplit d N k ω (Function.update ω' c s))
      = g (Function.update (rowSplit d N k ω ω') c s) := by
    intro s
    rw [rowSplit_update k ω ω' hc s]
  have h := hd (rowSplit d N k ω ω')
  rw [rowSplit_apply_of_isRowCoord k ω ω' hc] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hup s)

/-! ### `E_k` is linear -/

theorem condRow_const_mul (k : d.Idx N) (c : ℂ) (X : Ω d → ℂ) (ω : Ω d) :
    condRow d N k (fun η => c * X η) ω = c * condRow d N k X ω := by
  rw [condRow_apply, condRow_apply]
  exact integral_const_mul _ _

theorem condRow_neg_const_mul (k : d.Idx N) (c : ℂ) (X : Ω d → ℂ) (ω : Ω d) :
    condRow d N k (fun η => -(c * X η)) ω = -(c * condRow d N k X ω) := by
  rw [condRow_apply, condRow_apply, integral_neg, integral_const_mul]

theorem condRow_finsetSum (hG : GaussIBP d) (k : d.Idx N) {ι : Type*} (s : Finset ι)
    (F : ι → Ω d → ℂ) (hF : ∀ p ∈ s, Tame d (F p)) (ω : Ω d) :
    condRow d N k (fun η => ∑ p ∈ s, F p η) ω = ∑ p ∈ s, condRow d N k (F p) ω := by
  simp only [condRow_apply]
  exact MeasureTheory.integral_finsetSum _
    fun p hp => ((hF p hp).comp_rowSplit k ω).integrable hG

theorem condRow_zero_apply (k : d.Idx N) (ω : Ω d) :
    condRow d N k (fun _ => (0 : ℂ)) ω = 0 := by
  rw [condRow_apply, integral_zero]

/-! ### The coordinates that do not touch row `i` drop out -/

/-- `B_{xy,b}` has no entry in row `i` unless `i` is `x` or `y`. -/
theorem Bmat_mul_apply_diag_of_ne {x y i : d.Idx N} (hx : ¬ i = x) (hy : ¬ i = y) (b : Bool)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : (Bmat d N x y b * M) i i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Bmat_apply, ite_eq_right (fun h => hx h.1), ite_eq_right (fun h => hy h.1), zero_mul]

/-! ### The conditional derivative of a row of the resolvent -/

/-- The coordinate derivative of `(B G)_{ac}` for a constant `B`. -/
theorem hasDerivAt_const_mul_green_apply_update (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (η : Ω d) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N)
    (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a c : d.Idx N) :
    HasDerivAt
      (fun s : ℝ => (B * green (Hflow d N u (Function.update η (crd d N p) s)) z) a c)
      (-((Real.sqrt u : ℂ) * (B * (green (Hflow d N u η) z * Bmat d N p.1 p.2.1 p.2.2
        * green (Hflow d N u η) z)) a c)) (η (crd d N p)) := by
  have hterm : ∀ l : d.Idx N, HasDerivAt
      (fun s : ℝ => B a l * green (Hflow d N u (Function.update η (crd d N p) s)) z l c)
      (B a l * -((Real.sqrt u : ℂ) * (green (Hflow d N u η) z * Bmat d N p.1 p.2.1 p.2.2
        * green (Hflow d N u η) z) l c)) (η (crd d N p)) := by
    intro l
    have h := hasDerivAt_green_apply_update d N u hz η hp l c
    refine HasDerivAt.const_mul (B a l) ?_
    simpa [Complex.real_smul] using h
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (d.Idx N)))
    (A := fun l (s : ℝ) => B a l * green (Hflow d N u (Function.update η (crd d N p) s)) z l c)
    (A' := fun l => B a l * -((Real.sqrt u : ℂ)
      * (green (Hflow d N u η) z * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) z) l c))
    (fun l _ => hterm l)
  have hval : ∑ l : d.Idx N, B a l * -((Real.sqrt u : ℂ)
      * (green (Hflow d N u η) z * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) z) l c)
      = -((Real.sqrt u : ℂ) * (B * (green (Hflow d N u η) z * Bmat d N p.1 p.2.1 p.2.2
        * green (Hflow d N u η) z)) a c) := by
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mul_apply (M := B)
    (N := green (Hflow d N u (Function.update η (crd d N p) s)) z) (i := a) (k := c)).symm

/-! ### Step (b): the conditional integration by parts, one coordinate at a time -/

/-- **`E_i[ω_p (B_p G)_{ii}] = gvar_p E_i[-√u (B_p G B_p G)_{ii}]`.**  For a coordinate of row
`i` this is `condRow_coord_mul`; for any other coordinate both sides vanish identically,
because `B_p` has no entry in row `i`. -/
theorem condRow_coord_mul_Bmat_mul_green_diag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    (u : ℝ) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) (i : d.Idx N) (ω : Ω d) :
    condRow d N i (fun η => (η (crd d N p) : ℂ)
        * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t)) i i) ω
      = (gvar d (crd d N p) : ℝ) * condRow d N i (fun η => -((Real.sqrt u : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u η) (zt E t)
            * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t))) i i)) ω := by
  obtain ⟨x, y, b⟩ := p
  by_cases hrow : IsRowCoord d N i (crd d N (x, y, b))
  · refine condRow_coord_mul hG i hrow _ _
      (tame_const_mul_green_apply hE ht u (Bmat d N x y b) i i)
      (((Tame.const (d := d) (Real.sqrt u : ℂ)).mul
        (tame_const_mul_sandwich_apply hE ht u (Bmat d N x y b) i i)).neg) (fun η => ?_) ω
    exact hasDerivAt_const_mul_green_apply_update d N u
      (zt_im_ne_zero_of_lt_one hE ht) η hp (Bmat d N x y b) i i
  · rw [isRowCoord_mk] at hrow
    have hx : ¬ i = x := fun h => hrow (Or.inl h.symm)
    have hy : ¬ i = y := fun h => hrow (Or.inr h.symm)
    have hz1 : ∀ η : Ω d, (η (crd d N (x, y, b)) : ℂ)
        * (Bmat d N x y b * green (Hflow d N u η) (zt E t)) i i = 0 := by
      intro η
      rw [Bmat_mul_apply_diag_of_ne hx hy b, mul_zero]
    have hz2 : ∀ η : Ω d, -((Real.sqrt u : ℂ)
        * (Bmat d N x y b * (green (Hflow d N u η) (zt E t) * Bmat d N x y b
          * green (Hflow d N u η) (zt E t))) i i) = 0 := by
      intro η
      rw [Bmat_mul_apply_diag_of_ne hx hy b, mul_zero, neg_zero]
    simp only [hz1, hz2, condRow_zero_apply, mul_zero]

/-- **Step (b): the conditional row identity.**

`E_i[(H_u G)_{ii}] = -u ∑_k S_{ik} E_i[G_{ii} G_{kk}]` — the whole-row Gaussian integration by
parts of p. 50, taken inside the conditional expectation `E_i` of §4.  Only the coordinates of
row `i` occur (the others annihilate `B_p` in row `i`), and those are exactly the ones `E_i`
integrates out, so `condRow_coord_mul` applies to every surviving term. -/
theorem condRow_Hflow_mul_green_diag (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : 0 ≤ u) (i : d.Idx N) (ω : Ω d) :
    condRow d N i (fun η => (Hflow d N u η * green (Hflow d N u η) (zt E t)) i i) ω
      = -((u : ℂ) * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * condRow d N i (fun η => green (Hflow d N u η) (zt E t) i i
              * green (Hflow d N u η) (zt E t) k k) ω) := by
  classical
  have hsq : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
  have h1 : ∀ η : Ω d, (Hflow d N u η * green (Hflow d N u η) (zt E t)) i i
      = ∑ p ∈ usedCoord d N, (Real.sqrt u : ℂ) * ((η (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t)) i i) := by
    intro η
    rw [Hflow_eq_realSmul, Xmat_eq_sum, Matrix.smul_mul, Finset.sum_mul]
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
      Finset.mul_sum]
  have htamep : ∀ p ∈ usedCoord d N, Tame d
      (fun η : Ω d => (Real.sqrt u : ℂ) * ((η (crd d N p) : ℂ)
        * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t)) i i)) :=
    fun p _ => (Tame.const (d := d) (Real.sqrt u : ℂ)).mul
      ((Tame.coord (crd d N p)).mul
        (tame_const_mul_green_apply hE ht u (Bmat d N p.1 p.2.1 p.2.2) i i))
  simp only [h1]
  rw [condRow_finsetSum hG i _ _ htamep]
  have hstep : ∀ p ∈ usedCoord d N,
      condRow d N i (fun η => (Real.sqrt u : ℂ) * ((η (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t)) i i)) ω
        = -((u : ℂ) * (((gvar d (crd d N p) : ℝ) : ℂ)
            * condRow d N i (fun η => (Bmat d N p.1 p.2.1 p.2.2
              * (green (Hflow d N u η) (zt E t) * Bmat d N p.1 p.2.1 p.2.2
                * green (Hflow d N u η) (zt E t))) i i) ω)) := by
    intro p hp
    rw [condRow_const_mul, condRow_coord_mul_Bmat_mul_green_diag hG hE ht u hp i ω,
      condRow_neg_const_mul, ← hsq]
    ring
  rw [Finset.sum_congr rfl hstep]
  have htameq : ∀ p ∈ usedCoord d N, Tame d
      (fun η : Ω d => ((gvar d (crd d N p) : ℝ) : ℂ)
        * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u η) (zt E t)
          * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t))) i i) :=
    fun p _ => (Tame.const (d := d) ((gvar d (crd d N p) : ℝ) : ℂ)).mul
      (tame_const_mul_sandwich_apply hE ht u (Bmat d N p.1 p.2.1 p.2.2) i i)
  have htamek : ∀ k ∈ (Finset.univ : Finset (d.Idx N)), Tame d
      (fun η : Ω d => (Sblk (d.L N) (d.W N) i k : ℂ)
        * (green (Hflow d N u η) (zt E t) i i * green (Hflow d N u η) (zt E t) k k)) :=
    fun k _ => (Tame.const (d := d) ((Sblk (d.L N) (d.W N) i k : ℝ) : ℂ)).mul
      ((tame_green_apply hE ht u i i).mul (tame_green_apply hE ht u k k))
  have hcollapse : ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ)
        * condRow d N i (fun η => (Bmat d N p.1 p.2.1 p.2.2
          * (green (Hflow d N u η) (zt E t) * Bmat d N p.1 p.2.1 p.2.2
            * green (Hflow d N u η) (zt E t))) i i) ω
      = ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
        * condRow d N i (fun η => green (Hflow d N u η) (zt E t) i i
            * green (Hflow d N u η) (zt E t) k k) ω := by
    have hL : ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ)
          * condRow d N i (fun η => (Bmat d N p.1 p.2.1 p.2.2
            * (green (Hflow d N u η) (zt E t) * Bmat d N p.1 p.2.1 p.2.2
              * green (Hflow d N u η) (zt E t))) i i) ω
        = condRow d N i (fun η => ∑ p ∈ usedCoord d N, ((gvar d (crd d N p) : ℝ) : ℂ)
            * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N u η) (zt E t)
              * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N u η) (zt E t))) i i) ω := by
      rw [condRow_finsetSum hG i _ _ htameq]
      exact Finset.sum_congr rfl fun p _ => (condRow_const_mul _ _ _ _).symm
    have hR : ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * condRow d N i (fun η => green (Hflow d N u η) (zt E t) i i
              * green (Hflow d N u η) (zt E t) k k) ω
        = condRow d N i (fun η => ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u η) (zt E t) i i
              * green (Hflow d N u η) (zt E t) k k)) ω := by
      rw [condRow_finsetSum hG i _ _ htamek]
      exact Finset.sum_congr rfl fun k _ => (condRow_const_mul _ _ _ _).symm
    rw [hL, hR]
    simp only [sum_gvar_Bmat_sandwich_diag_mul d N _ i]
  rw [← hcollapse, Finset.sum_neg_distrib, ← Finset.mul_sum]

end CondIBP

/-! ### Step 3: the display of p. 50, as an identity

Putting step 1 and step 2g together at the entry `(i,i)` gives the p. 50 display with **no**
error term:

  `E_i(G_ii - m) = t m ∑_k S_ik E_i[G_ii (G_kk - m)]`.

Everything that is `O≺(Ψ²)` in the paper is the difference between this and the form `hIBP`
asks for, namely `t m² ∑_k S_ik (G_kk - m)`; that difference is isolated in the next section. -/

section CondDisplay

variable {d : Dims} {N : ℕ} {E t : ℝ}

/-- The coordinate decomposition of `H_u M`, for an arbitrary right factor. -/
theorem Hflow_mul_apply_eq_sum (d : Dims) (N : ℕ) (u : ℝ) (η : Ω d)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a c : d.Idx N) :
    (Hflow d N u η * M) a c
      = ∑ p ∈ usedCoord d N, (Real.sqrt u : ℂ)
          * ((η (crd d N p) : ℂ) * (Bmat d N p.1 p.2.1 p.2.2 * M) a c) := by
  rw [Hflow_eq_realSmul, Xmat_eq_sum, Matrix.smul_mul, Finset.sum_mul]
  simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
    Finset.mul_sum]

/-- `(H_u G)_{ac}` is tame. -/
theorem tame_Hflow_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ) (a c : d.Idx N) :
    Tame d (fun η : Ω d => (Hflow d N u η * green (Hflow d N u η) (zt E t)) a c) := by
  have hfun : (fun η : Ω d => (Hflow d N u η * green (Hflow d N u η) (zt E t)) a c)
      = fun η : Ω d => ∑ p ∈ usedCoord d N, (Real.sqrt u : ℂ)
          * ((η (crd d N p) : ℂ) * (Bmat d N p.1 p.2.1 p.2.2
            * green (Hflow d N u η) (zt E t)) a c) := by
    funext η
    exact Hflow_mul_apply_eq_sum d N u η _ a c
  rw [hfun]
  exact Tame.sum _ fun p _ => (Tame.const (d := d) (Real.sqrt u : ℂ)).mul
    ((Tame.coord (crd d N p)).mul
      (tame_const_mul_green_apply hE ht u (Bmat d N p.1 p.2.1 p.2.2) a c))

theorem condRow_tame_add (hG : GaussIBP d) (k : d.Idx N) {X Y : Ω d → ℂ}
    (hX : Tame d X) (hY : Tame d Y) (ω : Ω d) :
    condRow d N k (fun η => X η + Y η) ω = condRow d N k X ω + condRow d N k Y ω := by
  simp only [condRow_apply]
  exact integral_add ((hX.comp_rowSplit k ω).integrable hG)
    ((hY.comp_rowSplit k ω).integrable hG)

theorem condRow_tame_sub (hG : GaussIBP d) (k : d.Idx N) {X Y : Ω d → ℂ}
    (hX : Tame d X) (hY : Tame d Y) (ω : Ω d) :
    condRow d N k (fun η => X η - Y η) ω = condRow d N k X ω - condRow d N k Y ω := by
  simp only [condRow_apply]
  exact integral_sub ((hX.comp_rowSplit k ω).integrable hG)
    ((hY.comp_rowSplit k ω).integrable hG)

/-- **The p. 50 display, exactly.**

`E_i(G_{ii} - m) = t m ∑_k S_{ik} E_i[G_{ii}(G_{kk} - m)]`.  This is an *identity*: no error
term, no stochastic domination.  It is `green_sub_smul_one_eq` at the entry `(i,i)`, the
conditional row integration by parts `condRow_Hflow_mul_green_diag`, and `∑_k S_{ik} = 1`. -/
theorem condExpDiag_eq_sum_Sblk (hG : GaussIBP d) (hE : |E| < 2) (hE2 : |E| ≤ 2)
    (ht0 : 0 ≤ t) (ht : t < 1) (i : d.Idx N) (ω : Ω d) :
    condExpDiag d N t (zt E t) (mE E) i ω
      = (t : ℂ) * mE E * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i
              * (green (Hflow d N t η) (zt E t) k k - mE E)) ω := by
  classical
  have hz := zt_im_ne_zero_of_lt_one (E := E) (t := t) hE ht
  -- the algebraic identity at the entry `(i, i)`
  have hpt : ∀ η : Ω d, greenDiagCentered d N t (zt E t) (mE E) i η
      = (-(mE E)) * (Hflow d N t η * green (Hflow d N t η) (zt E t)) i i
        + (-((t : ℂ) * mE E ^ 2)) * green (Hflow d N t η) (zt E t) i i := by
    intro η
    have h := green_sub_smul_one_eq (Hflow_isHermitian d N t η) hE2 hz
    have hij := congrFun (congrFun h i) i
    rw [sub_smul_one_apply, ite_eq_left rfl] at hij
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul] at hij
    show green (Hflow d N t η) (zt E t) i i - mE E = _
    rw [hij]
    ring
  -- `E_i` is linear
  have htame1 : Tame d
      (fun η : Ω d => (-(mE E)) * (Hflow d N t η * green (Hflow d N t η) (zt E t)) i i) :=
    (Tame.const (d := d) (-(mE E))).mul (tame_Hflow_mul_green_apply hE ht t i i)
  have htame2 : Tame d
      (fun η : Ω d => (-((t : ℂ) * mE E ^ 2)) * green (Hflow d N t η) (zt E t) i i) :=
    (Tame.const (d := d) (-((t : ℂ) * mE E ^ 2))).mul (tame_green_apply hE ht t i i)
  have hlin : condExpDiag d N t (zt E t) (mE E) i ω
      = (-(mE E)) * condRow d N i
          (fun η => (Hflow d N t η * green (Hflow d N t η) (zt E t)) i i) ω
        + (-((t : ℂ) * mE E ^ 2)) * condRow d N i
          (fun η => green (Hflow d N t η) (zt E t) i i) ω := by
    show condRow d N i (greenDiagCentered d N t (zt E t) (mE E) i) ω = _
    have : (greenDiagCentered d N t (zt E t) (mE E) i)
        = fun η => (-(mE E)) * (Hflow d N t η * green (Hflow d N t η) (zt E t)) i i
          + (-((t : ℂ) * mE E ^ 2)) * green (Hflow d N t η) (zt E t) i i := funext hpt
    rw [this, condRow_tame_add hG i htame1 htame2, condRow_const_mul, condRow_const_mul]
  rw [hlin, condRow_Hflow_mul_green_diag hG hE ht ht0 i ω]
  -- `∑_k S_ik = 1` turns the lone `E_i[G_ii]` into a row sum
  have hrow : ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, sum_Sblk_row (d.three_le_L N) i, Complex.ofReal_one]
  have hsplit : ∀ k : d.Idx N,
      condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i
          * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
        = condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i
            * green (Hflow d N t η) (zt E t) k k) ω
          - mE E * condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i) ω := by
    intro k
    have hA : Tame d (fun η : Ω d => green (Hflow d N t η) (zt E t) i i
        * green (Hflow d N t η) (zt E t) k k) :=
      (tame_green_apply hE ht t i i).mul (tame_green_apply hE ht t k k)
    have hB : Tame d (fun η : Ω d => mE E * green (Hflow d N t η) (zt E t) i i) :=
      (Tame.const (d := d) (mE E)).mul (tame_green_apply hE ht t i i)
    have hfun : (fun η : Ω d => green (Hflow d N t η) (zt E t) i i
        * (green (Hflow d N t η) (zt E t) k k - mE E))
        = fun η : Ω d => green (Hflow d N t η) (zt E t) i i
            * green (Hflow d N t η) (zt E t) k k
          - mE E * green (Hflow d N t η) (zt E t) i i := by
      funext η; ring
    rw [hfun, condRow_tame_sub hG i hA hB, condRow_const_mul]
  have hsum : ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
        * condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i
            * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
      = (∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i
              * green (Hflow d N t η) (zt E t) k k) ω)
        - mE E * condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i) ω := by
    simp only [hsplit]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
  rw [hsum]
  ring

end CondDisplay

/-! ### Step 4: the `≺` bookkeeping, landing on `hIBP`

What is left is the difference between the identity of step 3 and the shape `hIBP` asks for.
It is isolated as `RBM.Gauss.ibpRem`, and `RBM.Gauss.condExpDiag_stochDom_of_ibpRem` /
`RBM.Gauss.condExpDiag_stochDom_of_pieces` produce the hypothesis `hIBP` of
`RBM.Gauss.trace_green_sub_mul_Eblk_stochDom` — verbatim, at its frozen signature — from a
`≺ L_max` bound on it.  The reduction is lossless: `S` is non-negative with unit row sums and
`‖m‖ = 1`. -/

section Remainder

variable {d : Dims} {N : ℕ} {E t : ℝ}

/-- **The remainder of the p. 50 display** at the pair `(i, k)`:

  `E_i[G_{ii}(G_{kk} - m)] - m(G_{kk} - m)`.

This is the *only* thing between the identity `condExpDiag_eq_sum_Sblk` and the hypothesis
`hIBP` of `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`.  The paper bounds it by `Ψ²` in two
pieces: `E_i[(G_{ii}-m)(G_{kk}-m)]`, a product of two `Ψ`'s, and `m(E_i(G_{kk}-m) - (G_{kk}-m))`,
the minor-replacement error of T85. -/
noncomputable def ibpRem (d : Dims) (N : ℕ) (E t : ℝ) (q : d.Idx N × d.Idx N) (ω : Ω d) : ℂ :=
  condRow d N q.1 (fun η => green (Hflow d N t η) (zt E t) q.1 q.1
      * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω
    - mE E * (green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E)

/-- **The deterministic reduction of `hIBP` to the remainder.**  A uniform bound on
`ibpRem d N E t (i, ·)` is a bound on the quantity `hIBP` controls, with no loss: the
coefficients `S_{ik}` are non-negative and sum to one. -/
theorem norm_condExpDiag_sub_le (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht : t < 1)
    (i : d.Idx N) (ω : Ω d) {A : ℝ} (hA : ∀ k : d.Idx N, ‖ibpRem d N E t (i, k) ω‖ ≤ A) :
    ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖ ≤ A := by
  classical
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA i)
  have hterm : ∀ k : d.Idx N, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω
      = (Sblk (d.L N) (d.W N) i k : ℂ) * condRow d N i
          (fun η => green (Hflow d N t η) (zt E t) i i
            * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
        - mE E * ((Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)) := by
    intro k
    simp only [ibpRem]
    ring
  have hkey : condExpDiag d N t (zt E t) (mE E) i ω
      - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
        * (green (Hflow d N t ω) (zt E t) k k - mE E)
      = (t : ℂ) * mE E * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω := by
    rw [condExpDiag_eq_sum_Sblk hG hE hE.le ht0 ht i ω,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hkey, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mE hE.le, mul_one]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.le
  have hsum : ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ ≤ A := by
    calc ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
        ≤ ∑ k, ‖(Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k, Sblk (d.L N) (d.W N) i k * A := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Sblk_nonneg _ _)]
          exact mul_le_mul_of_nonneg_left (hA k) (Sblk_nonneg _ _)
      _ = A := by rw [← Finset.sum_mul, sum_Sblk_row (d.three_le_L N) i, one_mul]
  calc |t| * ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
      ≤ 1 * A := mul_le_mul ht1 hsum (norm_nonneg _) zero_le_one
    _ = A := one_mul A

/-- **`hIBP`, reduced to a bound on the remainder.**  Feeding this theorem a `≺ L_max` bound on
`RBM.Gauss.ibpRem` discharges the hypothesis `hIBP` of
`RBM.Gauss.trace_green_sub_mul_Eblk_stochDom` at its exact frozen signature. -/
theorem condExpDiag_stochDom_of_ibpRem (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1)
    (hrem : StochDom (P d) (fun N (q : d.Idx N × d.Idx N) ω => ‖ibpRem d N E t q ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  refine StochDom.of_subset_union hrem hrem fun τ hτ =>
    ⟨τ, hτ, Filter.Eventually.of_forall fun N ω hω => ?_⟩
  obtain ⟨i, hi⟩ := hω
  by_contra hcon
  rw [Set.mem_union] at hcon
  push Not at hcon
  obtain ⟨h1, -⟩ := hcon
  have hall : ∀ k : d.Idx N, ‖ibpRem d N E t (i, k) ω‖
      ≤ (N : ℝ) ^ τ * Lmax (Hflow d N t ω) (zt E t) := by
    intro k
    by_contra hk
    exact h1 ⟨(i, k), lt_of_not_ge hk⟩
  exact absurd (norm_condExpDiag_sub_le hG hE ht0 ht i ω hall) (not_le.2 hi)

/-- **The remainder splits into the paper's two `Ψ²` inputs.**

`E_i[G_{ii}(G_{kk}-m)] - m(G_{kk}-m) = E_i[(G_{ii}-m)(G_{kk}-m)] + m(E_i(G_{kk}-m) - (G_{kk}-m))`.

The first summand is a product of two entries of `G - m`; the second is the minor-replacement
error of T85 (`RBM1D/Gauss/MinorReplace.lean`), since `G^{(i)}_{kk}` is `E_i`-invariant. -/
theorem ibpRem_eq_add (hG : GaussIBP d) (hE : |E| < 2) (ht : t < 1) (i k : d.Idx N) (ω : Ω d) :
    ibpRem d N E t (i, k) ω
      = condRow d N i (fun η => (green (Hflow d N t η) (zt E t) i i - mE E)
          * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
        + mE E * (condRow d N i (greenDiagCentered d N t (zt E t) (mE E) k) ω
          - (green (Hflow d N t ω) (zt E t) k k - mE E)) := by
  have hA : Tame d (fun η : Ω d => (green (Hflow d N t η) (zt E t) i i - mE E)
      * (green (Hflow d N t η) (zt E t) k k - mE E)) :=
    ((tame_green_apply hE ht t i i).sub (Tame.const _)).mul
      ((tame_green_apply hE ht t k k).sub (Tame.const _))
  have hB : Tame d (fun η : Ω d => mE E * (green (Hflow d N t η) (zt E t) k k - mE E)) :=
    (Tame.const (d := d) (mE E)).mul ((tame_green_apply hE ht t k k).sub (Tame.const _))
  have hfun : (fun η : Ω d => green (Hflow d N t η) (zt E t) i i
      * (green (Hflow d N t η) (zt E t) k k - mE E))
      = fun η : Ω d => (green (Hflow d N t η) (zt E t) i i - mE E)
          * (green (Hflow d N t η) (zt E t) k k - mE E)
        + mE E * (green (Hflow d N t η) (zt E t) k k - mE E) := by
    funext η
    ring
  have hgdc : (fun η : Ω d => mE E * (green (Hflow d N t η) (zt E t) k k - mE E))
      = fun η : Ω d => mE E * greenDiagCentered d N t (zt E t) (mE E) k η := rfl
  show condRow d N i (fun η => green (Hflow d N t η) (zt E t) i i
      * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
      - mE E * (green (Hflow d N t ω) (zt E t) k k - mE E) = _
  rw [hfun, condRow_tame_add hG i hA hB, hgdc, condRow_const_mul]
  ring

/-- **`hIBP` from the paper's own two inputs.**  This is
`RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`'s hypothesis `hIBP`, at its exact frozen
signature, reduced to

* `hprod`: `E_i[(G_{ii}-m)(G_{kk}-m)] ≺ L_max` — the local law, squared;
* `hminor`: `E_i(G_{kk}-m) - (G_{kk}-m) ≺ L_max` — the minor replacement (4.9) of T85.

Nothing else is missing: `condExpDiag_eq_sum_Sblk` is an identity. -/
theorem condExpDiag_stochDom_of_pieces (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1)
    (hprod : StochDom (P d) (fun N (q : d.Idx N × d.Idx N) ω =>
        ‖condRow d N q.1 (fun η => (green (Hflow d N t η) (zt E t) q.1 q.1 - mE E)
          * (green (Hflow d N t η) (zt E t) q.2 q.2 - mE E)) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hminor : StochDom (P d) (fun N (q : d.Idx N × d.Idx N) ω =>
        ‖condRow d N q.1 (greenDiagCentered d N t (zt E t) (mE E) q.2) ω
          - (green (Hflow d N t ω) (zt E t) q.2 q.2 - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hL0 : ∀ (N : ℕ) (q : d.Idx N × d.Idx N) (ω : Ω d),
      0 ≤ Lmax (Hflow d N t ω) (zt E t) :=
    fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)
  have htwo : StochDom (P d)
      (fun N (q : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)
        + Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : d.Idx N × d.Idx N) ω => Lmax (Hflow d N t ω) (zt E t)) :=
    StochDom.of_le_left (fun N q ω => le_of_eq (by ring))
      (StochDom.const_mul_left (by norm_num : (0 : ℝ) ≤ 2) hL0 (StochDom.refl hL0))
  refine condExpDiag_stochDom_of_ibpRem hG hE ht0 ht
    (StochDom.of_le_left (fun N q ω => ?_) ((hprod.add hminor).trans htwo))
  obtain ⟨i, k⟩ := q
  rw [ibpRem_eq_add hG hE ht i k ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE hE.le, one_mul]
  simp only [Pi.add_apply]
  exact le_rfl

end Remainder

end RBM.Gauss


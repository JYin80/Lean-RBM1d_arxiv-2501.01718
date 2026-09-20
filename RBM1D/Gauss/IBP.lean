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

end RBM.Gauss

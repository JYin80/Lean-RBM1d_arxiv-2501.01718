/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucAvg
import RBM1D.Gauss.MomentGronwall
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

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothPrefix
import RBM1D.Gauss.APrimeWeight
import RBM1D.Gauss.APrimeDuhamel

/-!
# T333: actual finite smooth-prefix weight

The cutoff is formed from the regularized, normalized two-loop observable at
each preceding net point.  The Gaussian sample at distinct net points is
always obtained from the same base matrix.
-/

namespace RBM
namespace APrimeSmoothWeightActual

open Real Step2Bootstrap MomentDuhamelCut CutHypTheta Cutoff
open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

section Regularization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private theorem abs_fderiv_reg_apply_le {F : V → ℂ} (hF : ContDiff ℝ 1 F)
    {ε : ℝ} (hε : 0 < ε) (M B : V) :
    |fderiv ℝ (fun X => √(‖F X‖ ^ 2 + ε ^ 2)) M B| ≤
      ‖fderiv ℝ F M B‖ := by
  have hd : HasFDerivAt F (fderiv ℝ F M) M :=
    (hF.differentiable (by norm_num) M).hasFDerivAt
  have hsq := hd.norm_sq
  have hpos : 0 < ‖F M‖ ^ 2 + ε ^ 2 := by
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    positivity
  have hr := (hsq.add_const (ε ^ 2)).sqrt hpos.ne'
  have hfd : fderiv ℝ (fun X => √(‖F X‖ ^ 2 + ε ^ 2)) M =
      (1 / (2 * √(‖F M‖ ^ 2 + ε ^ 2))) •
        (2 • (innerSL ℝ (F M)).comp (fderiv ℝ F M)) := hr.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    nsmul_eq_mul, smul_eq_mul]
  have hroot : 0 < √(‖F M‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have hnorm : ‖F M‖ ≤ √(‖F M‖ ^ 2 + ε ^ 2) := by
    have h := Real.sqrt_le_sqrt
      (show ‖F M‖ ^ 2 ≤ ‖F M‖ ^ 2 + ε ^ 2 by nlinarith [sq_nonneg ε])
    simpa [Real.sqrt_sq (norm_nonneg (F M))] using h
  have hinner := abs_real_inner_le_norm (F M) (fderiv ℝ F M B)
  simp only [abs_mul, abs_of_nonneg
    (by positivity : (0 : ℝ) ≤ 1 / (2 * √(‖F M‖ ^ 2 + ε ^ 2))),
    Nat.cast_ofNat]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc (1 / (2 * √(‖F M‖ ^ 2 + ε ^ 2))) * (2 * |inner ℝ (F M) (fderiv ℝ F M B)|)
      ≤ (1 / (2 * √(‖F M‖ ^ 2 + ε ^ 2))) *
          (2 * (‖F M‖ * ‖fderiv ℝ F M B‖)) := by gcongr
    _ = (‖F M‖ / √(‖F M‖ ^ 2 + ε ^ 2)) * ‖fderiv ℝ F M B‖ := by ring
    _ ≤ ‖fderiv ℝ F M B‖ := by
      have hratio : ‖F M‖ / √(‖F M‖ ^ 2 + ε ^ 2) ≤ 1 :=
        (div_le_one hroot).2 hnorm
      nlinarith [norm_nonneg (fderiv ℝ F M B)]

end Regularization

private theorem contDiff_reg {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {F : V → ℂ}
    (hF : ContDiff ℝ 1 F) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fun X => √(‖F X‖ ^ 2 + ε ^ 2)) := by
  have hsq : ContDiff ℝ 1 (fun X : V => ‖F X‖ ^ 2 + ε ^ 2) :=
    ((contDiff_norm_sq ℂ).comp hF).add contDiff_const
  exact hsq.sqrt (fun X => (by
    have hp : 0 < ε ^ 2 := sq_pos_of_pos hε
    have h : 0 < ‖F X‖ ^ 2 + ε ^ 2 := by positivity
    exact h.ne'))

private theorem sqrt_quadVar_reg_le (d : Gauss.Dims) (N : ℕ)
    {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    {ε : ℝ} (hε : 0 < ε) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (fun X => ((√(‖F X‖ ^ 2 + ε ^ 2) : ℝ) : ℂ)) M) ≤
      √(Gauss.quadVar d N F M) := by
  have hreg := contDiff_reg hF hε
  have happly : ∀ q ∈ Gauss.usedCoord d N,
      ‖Gauss.coordD1 d N
        (fun X => ((√(‖F X‖ ^ 2 + ε ^ 2) : ℝ) : ℂ)) M q‖ ≤
        1 * ‖Gauss.coordD1 d N F M q‖ := by
    intro q _
    rw [Gauss.norm_coordD1_ofReal (hreg.differentiable (by norm_num) M) q]
    simpa only [one_mul, Gauss.coordD1] using
      abs_fderiv_reg_apply_le hF hε M (Gauss.Bmat d N q.1 q.2.1 q.2.2)
  simpa only [one_mul] using
    (Gauss.sqrt_quadVar_le_of_apply_le (d := d) (N := N)
      (F := fun X => ((√(‖F X‖ ^ 2 + ε ^ 2) : ℝ) : ℂ))
      (G := F) (M := M) (L := 1) (by norm_num) happly)

private theorem norm_coordD1_pullback (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (q : d.Idx N × d.Idx N × Bool) :
    ‖Gauss.coordD1 d N (fun X => F ((Real.sqrt u : ℂ) • X)) M q‖ =
      Real.sqrt u * ‖Gauss.coordD1 d N F ((Real.sqrt u : ℂ) • M) q‖ := by
  change ‖fderiv ℝ (fun X => F ((Real.sqrt u : ℂ) • X)) M
      (Gauss.Bmat d N q.1 q.2.1 q.2.2)‖ = _
  rw [show (fun X : Matrix (d.Idx N) (d.Idx N) ℂ => F ((Real.sqrt u : ℂ) • X)) =
      (fun X => F (Real.sqrt u • X)) from rfl]
  rw [fderiv_comp_smul]
  simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u)]
  rfl

private theorem sqrt_quadVar_pullback (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (fun X => F ((Real.sqrt u : ℂ) • X)) M) =
      Real.sqrt u * √(Gauss.quadVar d N F ((Real.sqrt u : ℂ) • M)) := by
  have hq : Gauss.quadVar d N (fun X => F ((Real.sqrt u : ℂ) • X)) M =
      (Real.sqrt u) ^ 2 * Gauss.quadVar d N F ((Real.sqrt u : ℂ) • M) := by
    unfold Gauss.quadVar
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [norm_coordD1_pullback d N F u M q]
    ring
  rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg u)]

private theorem sqrt_quadVar_smoothMaxOf_le (d : Gauss.Dims) (N : ℕ)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (c : ι → ℝ)
    (ε : ℝ) (m : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (K : ℝ)
    (hm : 1 ≤ m) (hε : 0 < ε) (hc : ∀ a, 0 < c a)
    (hF : ∀ a, ContDiff ℝ 1 (F a))
    (hK : ∀ a, √(Gauss.quadVar d N (F a) M) / c a ≤ K) :
    √(Gauss.quadVar d N
      (fun X => ((APrimeSmoothPrefix.smoothMaxOf m F c ε X : ℝ) : ℂ)) M) ≤
      ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ)))) * K := by
  classical
  let G : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    fun a X => ((√(‖F a X‖ ^ 2 + ε ^ 2) : ℝ) : ℂ)
  have hG : ∀ a ∈ (Finset.univ : Finset ι), ContDiff ℝ 1 (G a) := by
    intro a _
    exact Complex.ofRealCLM.contDiff.comp (contDiff_reg (hF a) hε)
  have hY : 0 < ∑ a ∈ (Finset.univ : Finset ι), (‖G a M‖ / c a) ^ (2 * m) := by
    obtain ⟨a⟩ := ‹Nonempty ι›
    have hterm : 0 < (‖G a M‖ / c a) ^ (2 * m) := by
      apply pow_pos
      apply div_pos _ (hc a)
      simp only [G, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      apply Real.sqrt_pos.2
      have hp : 0 < ε ^ 2 := sq_pos_of_pos hε
      positivity
    have hsum : (‖G a M‖ / c a) ^ (2 * m) ≤
        ∑ b ∈ (Finset.univ : Finset ι), (‖G b M‖ / c b) ^ (2 * m) :=
      Finset.single_le_sum (s := (Finset.univ : Finset ι))
        (fun b _ => pow_nonneg (div_nonneg (norm_nonneg (G b M)) (hc b).le) (2 * m))
        (Finset.mem_univ a)
    exact lt_of_lt_of_le hterm hsum
  have hKG : ∀ a ∈ (Finset.univ : Finset ι),
      √(Gauss.quadVar d N (G a) M) / c a ≤ K := by
    intro a _
    exact (div_le_div_of_nonneg_right
      (sqrt_quadVar_reg_le d N (hF a) hε M) (hc a).le).trans (hK a)
  have hgrad := Gauss.sqrt_quadVar_softMax_le (d := d) (N := N)
    (S := (Finset.univ : Finset ι)) (f := G) (c := c) (r := m)
    (K := K) hm (fun a _ => hc a) hG M hY hKG
  have heq : (fun X => ((APrimeSmoothPrefix.smoothMaxOf m F c ε X : ℝ) : ℂ)) =
      (fun X => ((softMax m Finset.univ (fun a => ‖G a X‖ / c a) : ℝ) : ℂ)) := by
    funext X
    congr 1
    apply congrArg
      (fun z : ι → ℝ => softMax m Finset.univ z)
    funext a
    simp [G, APrimeSmoothPrefix.regularized, Complex.norm_real,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [heq]
  simpa only [Finset.card_univ] using hgrad

private theorem sqrt_quadVar_one_add_div (d : Gauss.Dims) (N : ℕ)
    {g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    {c : ℝ} (hc : 0 < c) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (fun X => (((1 + g X) / c : ℝ) : ℂ)) M) =
      c⁻¹ * √(Gauss.quadVar d N (fun X => ((g X : ℝ) : ℂ)) M) := by
  have hder : ∀ q ∈ Gauss.usedCoord d N,
      ‖Gauss.coordD1 d N (fun X => (((1 + g X) / c : ℝ) : ℂ)) M q‖ =
        c⁻¹ * ‖Gauss.coordD1 d N (fun X => ((g X : ℝ) : ℂ)) M q‖ := by
    intro q _
    have h1 : DifferentiableAt ℝ (fun X => (1 + g X) / c) M :=
      ((contDiff_const.add hg).div_const c).differentiable (by norm_num) M
    rw [Gauss.norm_coordD1_ofReal h1 q,
      Gauss.norm_coordD1_ofReal (hg.differentiable (by norm_num) M) q]
    have hfd : fderiv ℝ (fun X => (1 + g X) / c) M =
        c⁻¹ • fderiv ℝ g M := by
      have heq : (fun X => (1 + g X) / c) = fun X => c⁻¹ • (1 + g X) := by
        funext X; simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
      rw [heq]
      change fderiv ℝ (c⁻¹ • (fun X => 1 + g X)) M = _
      rw [fderiv_const_smul_field, Pi.smul_apply, fderiv_const_add]
    rw [hfd, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hc.le)]
  have hq : Gauss.quadVar d N (fun X => (((1 + g X) / c : ℝ) : ℂ)) M =
      c⁻¹ ^ 2 * Gauss.quadVar d N (fun X => ((g X : ℝ) : ℂ)) M := by
    unfold Gauss.quadVar
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hder q hq]
    ring
  rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hc.le)]

private theorem abs_fderiv_softMax_le_of_bound {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (S : Finset ι) (f : ι → V → ℂ) (c : ι → ℝ)
    (m : ℕ) (hm : 1 ≤ m) (hc : ∀ i ∈ S, 0 < c i)
    (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i)) (M B : V)
    (hY : 0 < ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ i ∈ S, ‖fderiv ℝ (f i) M B‖ / c i ≤ K) :
    |fderiv ℝ (fun X => softMax m S (fun i => ‖f i X‖ / c i)) M B| ≤
      (S.card : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) * K := by
  let Y : ℝ := ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m)
  let a : ℝ := (1 : ℝ) / (2 * (m : ℝ))
  have hbase := Gauss.abs_fderiv_softMax_apply_le S hm hc hf M B hY
  have hpow : ∀ i ∈ S, 0 ≤ (‖f i M‖ / c i) ^ (2 * m - 1) := by
    intro i hi
    exact pow_nonneg (div_nonneg (norm_nonneg _) (hc i hi).le) _
  have hsum : ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m - 1) *
      (‖fderiv ℝ (f i) M B‖ / c i) ≤
      K * ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hK i hi) (hpow i hi)
  have hholder := Step2Bootstrap.sum_abs_pow_pred_le
    (S := S) (ρ := fun i => ‖f i M‖ / c i) hm
  have hholder' : ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m - 1) ≤
      (S.card : ℝ) ^ a * Y ^ (1 - a) := by
    have heq : (∑ i ∈ S, |‖f i M‖ / c i| ^ (2 * m - 1)) =
        ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (hc i hi).le)]
    rw [heq] at hholder
    simpa [Y, a] using hholder
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hYa : 0 < Y ^ (a - 1) := Real.rpow_pos_of_pos hY _
  calc |fderiv ℝ (fun X => softMax m S (fun i => ‖f i X‖ / c i)) M B|
      ≤ Y ^ (a - 1) *
          ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m - 1) *
            (‖fderiv ℝ (f i) M B‖ / c i) := hbase
    _ ≤ Y ^ (a - 1) * (K * ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * m - 1)) :=
      mul_le_mul_of_nonneg_left hsum hYa.le
    _ ≤ Y ^ (a - 1) * (K * ((S.card : ℝ) ^ a * Y ^ (1 - a))) := by
      gcongr
    _ = (S.card : ℝ) ^ a * K := by
      have hmul : Y ^ (a - 1) * Y ^ (1 - a) = 1 := by
        rw [← Real.rpow_add hY]
        have he : a - 1 + (1 - a) = 0 := by ring
        rw [he, Real.rpow_zero]
      rw [show Y ^ (a - 1) * (K * ((S.card : ℝ) ^ a * Y ^ (1 - a))) =
          (Y ^ (a - 1) * Y ^ (1 - a)) * ((S.card : ℝ) ^ a * K) by ring,
        hmul, one_mul]

private theorem norm_fderiv_ofReal_apply {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : V → ℝ}
    (M : V) (hg : DifferentiableAt ℝ g M) (B : V) :
    ‖fderiv ℝ (fun X => ((g X : ℝ) : ℂ)) M B‖ = |fderiv ℝ g M B| := by
  have hd : fderiv ℝ (fun X => ((g X : ℝ) : ℂ)) M =
      Complex.ofRealCLM.comp (fderiv ℝ g M) :=
    (Complex.ofRealCLM.hasFDerivAt.comp M hg.hasFDerivAt).fderiv
  rw [hd]
  simp [Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_fderiv_smoothMaxOf_le {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [Fintype ι] [Nonempty ι]
    (F : ι → V → ℂ) (c : ι → ℝ) (ε : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hε : 0 < ε) (hc : ∀ i, 0 < c i)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i M, ‖fderiv ℝ (F i) M‖ / c i ≤ C) (M : V) :
    ‖fderiv ℝ (APrimeSmoothPrefix.smoothMaxOf m F c ε) M‖ ≤
      (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) * C := by
  classical
  let g : ι → V → ℝ := fun i X => √(‖F i X‖ ^ 2 + ε ^ 2)
  let G : ι → V → ℂ := fun i X => ((g i X : ℝ) : ℂ)
  have hg : ∀ i, ContDiff ℝ 1 (g i) := fun i => contDiff_reg (hF i) hε
  have hG : ∀ i ∈ (Finset.univ : Finset ι), ContDiff ℝ 1 (G i) := by
    intro i _
    exact Complex.ofRealCLM.contDiff.comp (hg i)
  have hY : 0 < ∑ i ∈ (Finset.univ : Finset ι),
      (‖G i M‖ / c i) ^ (2 * m) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hgi : 0 < g i M := Real.sqrt_pos.2 (by
      have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
      positivity)
    have hi : 0 < (‖G i M‖ / c i) ^ (2 * m) := by
      apply pow_pos
      apply div_pos _ (hc i)
      simpa [G, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgi] using hgi
    exact hi.trans_le (Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun j => (‖G j M‖ / c j) ^ (2 * m))
      (fun j _ => pow_nonneg (div_nonneg (norm_nonneg _) (hc j).le) _)
      (Finset.mem_univ i))
  have heq : APrimeSmoothPrefix.smoothMaxOf m F c ε =
      fun X => softMax m Finset.univ (fun i => ‖G i X‖ / c i) := by
    funext X
    unfold APrimeSmoothPrefix.smoothMaxOf APrimeSmoothPrefix.smoothMax
      APrimeSmoothPrefix.regularized
    congr 1
    funext i
    simp [G, g, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [heq]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun B => ?_)
  rw [Real.norm_eq_abs]
  have hK : ∀ i ∈ (Finset.univ : Finset ι),
      ‖fderiv ℝ (G i) M B‖ / c i ≤ C * ‖B‖ := by
    intro i _
    have hdir : ‖fderiv ℝ (G i) M B‖ ≤ ‖fderiv ℝ (F i) M B‖ := by
      rw [norm_fderiv_ofReal_apply M ((hg i).differentiable (by norm_num) M) B]
      exact abs_fderiv_reg_apply_le (hF i) hε M B
    calc
      ‖fderiv ℝ (G i) M B‖ / c i ≤ ‖fderiv ℝ (F i) M B‖ / c i :=
        div_le_div_of_nonneg_right hdir (hc i).le
      _ ≤ (‖fderiv ℝ (F i) M‖ * ‖B‖) / c i :=
        div_le_div_of_nonneg_right ((fderiv ℝ (F i) M).le_opNorm B) (hc i).le
      _ = (‖fderiv ℝ (F i) M‖ / c i) * ‖B‖ := by ring
      _ ≤ C * ‖B‖ := mul_le_mul_of_nonneg_right (hC i M) (norm_nonneg _)
  have h := abs_fderiv_softMax_le_of_bound Finset.univ G c m hm
    (fun i _ => hc i) hG M B hY (C * ‖B‖)
    (mul_nonneg hC0 (norm_nonneg _)) hK
  simpa only [Finset.card_univ, mul_assoc] using h

noncomputable def epsilon (d : Gauss.Dims) (D : ℝ) (N : ℕ) : ℝ :=
  (d.W N : ℝ) ^ (-D) * (N : ℝ) ^ (-(10 : ℝ))

noncomputable def threshold (δ : ℝ) (N : ℕ) : ℝ :=
  8 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (2 * δ)

/-- The actual prefix, expressed as a function of the common base matrix. -/
noncomputable def prefixMatrix (d : Gauss.Dims) (E D : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  softMax m (Finset.range k) (fun j =>
    APrimeSmoothPrefix.smoothJSMatrix d E D s N
      (cutNetPt s mesh N j) (epsilon d D N) m
      ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M))

noncomputable def prefixSample (d : Gauss.Dims) (E D : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (ω : Gauss.Ω d) : ℝ :=
  prefixMatrix d E D s mesh N k m (Gauss.Xmat d N ω)

noncomputable def cutoff (d : Gauss.Dims) (E D δ : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (ω : Gauss.Ω d) : ℝ :=
  cutChi (prefixSample d E D s mesh N k m ω / threshold δ N)

noncomputable def cutoffMatrix (d : Gauss.Dims) (E D δ : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  cutChi (prefixMatrix d E D s mesh N k m M / threshold δ N)

/-- The inactive branch agrees with the existing hard-prefix convention. -/
noncomputable def weight (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N k m : ℕ) (ω : Gauss.Ω d) : ℝ :=
  if k ≤ cutNetTop s t mesh N ∧ N₀ ≤ N then
    (cutoff d E D δ s mesh N k m ω) ^ (2 * p)
  else 1

noncomputable def weightMatrix (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N k m : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  if k ≤ cutNetTop s t mesh N ∧ N₀ ≤ N then
    (cutoffMatrix d E D δ s mesh N k m M) ^ (2 * p)
  else 1

noncomputable def weightD (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N k m : ℕ) (q : d.Idx N × d.Idx N × Bool) (ω : Gauss.Ω d) : ℝ :=
  fderiv ℝ (weightMatrix d E D δ s t mesh N₀ p N k m)
    (Gauss.Xmat d N ω) (Gauss.Bmat d N q.1 q.2.1 q.2.2)

theorem weight_eq_matrix (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N k m : ℕ) (ω : Gauss.Ω d) :
    weight d E D δ s t mesh N₀ p N k m ω =
      weightMatrix d E D δ s t mesh N₀ p N k m (Gauss.Xmat d N ω) := rfl

theorem epsilon_pos (d : Gauss.Dims) (D : ℝ) {N : ℕ} (hN : 0 < N) :
    0 < epsilon d D N := by
  unfold epsilon
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast (Gauss.band d).W_pos N) _)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)

theorem threshold_pos {δ : ℝ} {N : ℕ} (hN : 0 < N) :
    0 < threshold δ N := by
  unfold threshold
  positivity

theorem prefixSample_zero (d : Gauss.Dims) (E D : ℝ) (s mesh : ℕ → ℝ)
    (N m : ℕ) (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    prefixSample d E D s mesh N 0 m ω = 0 := by
  simp only [prefixSample, prefixMatrix, softMax, Finset.range_zero, Finset.sum_empty]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < 1 / (2 * (m : ℝ))))

theorem weight_zero_prefix (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N m : ℕ) (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    weight d E D δ s t mesh N₀ p N 0 m ω = 1 := by
  unfold weight
  split_ifs
  · simp [cutoff, prefixSample_zero d E D s mesh N m hm,
      cutChi_eq_one (show (0 : ℝ) ≤ 1 by norm_num)]
  · rfl

theorem weight_nonneg (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N k m : ℕ) (ω : Gauss.Ω d) :
    0 ≤ weight d E D δ s t mesh N₀ p N k m ω := by
  unfold weight
  split_ifs
  · exact pow_nonneg (cutChi_nonneg _) _
  · norm_num

theorem weight_le_one (d : Gauss.Dims) (E D δ : ℝ) (s t mesh : ℕ → ℝ)
    (N₀ p N k m : ℕ) (ω : Gauss.Ω d) :
    weight d E D δ s t mesh N₀ p N k m ω ≤ 1 := by
  unfold weight
  split_ifs
  · exact pow_le_one₀ (cutChi_nonneg _) (cutChi_le_one _)
  · norm_num

private theorem contDiff_softMax_of_pos {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (S : Finset ι) (hS : S.Nonempty) (m : ℕ) (hm : 1 ≤ m)
    (f : ι → V → ℝ) (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i))
    (hpos : ∀ i ∈ S, ∀ x, 0 < f i x) :
    ContDiff ℝ 1 (fun x => softMax m S (fun i => f i x)) := by
  classical
  let A : V → ℝ := fun x => ∑ i ∈ S, f i x ^ (2 * m)
  have hA : ContDiff ℝ 1 A := by
    exact ContDiff.sum (fun i hi => (hf i hi).pow (2 * m))
  have hApos : ∀ x, 0 < A x := by
    intro x
    obtain ⟨i, hi⟩ := hS
    have hterm : 0 < f i x ^ (2 * m) := pow_pos (hpos i hi x) _
    have hsum : f i x ^ (2 * m) ≤ A x :=
      Finset.single_le_sum (fun j hj => pow_nonneg (hpos j hj x).le _) hi
    exact lt_of_lt_of_le hterm hsum
  change ContDiff ℝ 1 (fun x => A x ^ ((1 : ℝ) / (2 * (m : ℝ))))
  exact hA.rpow_const_of_ne (fun x => (hApos x).ne')

theorem contDiff_prefixMatrix (d : Gauss.Dims) {E D : ℝ} {s mesh : ℕ → ℝ}
    {N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    ContDiff ℝ 1 (prefixMatrix d E D s mesh N k m) := by
  classical
  by_cases hk : k = 0
  · subst hk
    have hzero : prefixMatrix d E D s mesh N 0 m = fun _ => (0 : ℝ) := by
      funext M
      simp only [prefixMatrix, softMax, Finset.range_zero, Finset.sum_empty]
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < 1 / (2 * (m : ℝ))))
    rw [hzero]
    exact contDiff_const
  · have hnonempty : (Finset.range k).Nonempty := by
      exact ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)⟩
    let f : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ := fun j M =>
      APrimeSmoothPrefix.smoothJSMatrix d E D s N
        (cutNetPt s mesh N j) (epsilon d D N) m
        ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)
    have hf : ∀ j ∈ Finset.range k, ContDiff ℝ 1 (f j) := by
      intro j hj
      have hbase := APrimeSmoothPrefix.contDiff_smoothJSMatrix d
        (E := E) (D := D) (u := cutNetPt s mesh N j)
        (ε := epsilon d D N) (s := s) (N := N) (m := m)
        hE hs (hu j (Finset.mem_range.mp hj)) (epsilon_pos d D hN) hm
      have hline : ContDiff ℝ 1
          (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
            (Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) := by
        have hc : ContDiff ℝ 1
            (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
              Real.sqrt (cutNetPt s mesh N j)) := contDiff_const
        have hi : ContDiff ℝ 1
            (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => M) := contDiff_id
        convert (hc.smul hi) using 1
      exact hbase.comp hline
    have hpos : ∀ j ∈ Finset.range k, ∀ M, 0 < f j M := by
      intro j hj M
      have hR : 0 < (Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4 :=
        pow_pos (Step2Moment.ratR_pos hE hs (hu j (Finset.mem_range.mp hj))) _
      have hsoft : 0 ≤ APrimeSmoothPrefix.smoothMaxOf m
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j))
          (fun a : LoopArg (d.L N) 2 =>
            Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
              (zdist (d.L N) (a 0 - a 1))) (epsilon d D N)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) :=
        softMax_nonneg _ _ _
      exact div_pos (by linarith) hR
    change ContDiff ℝ 1 (fun M => softMax m (Finset.range k) (fun j => f j M))
    exact contDiff_softMax_of_pos _ hnonempty m hm f hf hpos

private theorem smoothJSMatrix_pos (d : Gauss.Dims) {E D u ε : ℝ}
    {s : ℕ → ℝ} {N m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hu : u < 1) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    0 < APrimeSmoothPrefix.smoothJSMatrix d E D s N u ε m M := by
  have hR : 0 < (Step2Moment.ratR E s N u) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs hu) _
  have hsoft : 0 ≤ APrimeSmoothPrefix.smoothMaxOf m
      (APrimeSmoothPrefix.coordFun d E N u)
      (fun a : LoopArg (d.L N) 2 =>
        Step2.tT (Gauss.band d) E N D u
          (zdist (d.L N) (a 0 - a 1))) ε M :=
    softMax_nonneg _ _ _
  exact div_pos (by linarith) hR

theorem sqrt_quadVar_smoothJSMatrix_le (d : Gauss.Dims) {E D u ε : ℝ}
    {s : ℕ → ℝ} {N m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hu : u < 1) (hε : 0 < ε) (hm : 1 ≤ m)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (K : ℝ)
    (hK : ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M) /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)) ≤ K) :
    √(Gauss.quadVar d N
      (fun X => ((APrimeSmoothPrefix.smoothJSMatrix d E D s N u ε m X : ℝ) : ℂ)) M) ≤
      ((Step2Moment.ratR E s N u) ^ 4)⁻¹ *
        (((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ)))) * K) := by
  let F : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    APrimeSmoothPrefix.coordFun d E N u
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  let g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    APrimeSmoothPrefix.smoothMaxOf m F c ε
  have hc : ∀ a, 0 < c a := by
    intro a
    exact tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
  have hF : ∀ a, ContDiff ℝ 1 (F a) :=
    APrimeSmoothPrefix.contDiff_coordFun d hE hu N
  have hg : ContDiff ℝ 1 g :=
    APrimeSmoothPrefix.contDiff_smoothMaxOf hm hF hc hε
  have hR : 0 < (Step2Moment.ratR E s N u) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs hu) _
  have h1 := sqrt_quadVar_one_add_div d N hg hR M
  have h2 := sqrt_quadVar_smoothMaxOf_le d N F c ε m M K hm hε hc hF hK
  change √(Gauss.quadVar d N
    (fun X => ((((1 + g X) / (Step2Moment.ratR E s N u) ^ 4 : ℝ) : ℂ))) M) ≤ _
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hR.le)

theorem sqrt_quadVar_smoothJSMatrix_pullback_le (d : Gauss.Dims)
    {E D u ε : ℝ} {s : ℕ → ℝ} {N m : ℕ}
    (hE : |E| < 2) (hs : s N < 1) (hu : u < 1)
    (hε : 0 < ε) (hm : 1 ≤ m)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (K : ℝ)
    (hK : ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a)
        ((Real.sqrt u : ℂ) • M)) /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)) ≤ K) :
    √(Gauss.quadVar d N
      (fun X => ((APrimeSmoothPrefix.smoothJSMatrix d E D s N u ε m
        ((Real.sqrt u : ℂ) • X) : ℝ) : ℂ)) M) ≤
      Real.sqrt u * (((Step2Moment.ratR E s N u) ^ 4)⁻¹ *
        (((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ)))) * K)) := by
  have hpull := sqrt_quadVar_pullback d N
    (fun X => ((APrimeSmoothPrefix.smoothJSMatrix d E D s N u ε m X : ℝ) : ℂ)) u M
  rw [hpull]
  exact mul_le_mul_of_nonneg_left
    (sqrt_quadVar_smoothJSMatrix_le d hE hs hu hε hm
      ((Real.sqrt u : ℂ) • M) K hK) (Real.sqrt_nonneg u)

theorem sqrt_quadVar_prefixMatrix_le (d : Gauss.Dims)
    {E D : ℝ} {s mesh : ℕ → ℝ} {N k m : ℕ}
    (hE : |E| < 2) (hs : s N < 1) (hN : 0 < N)
    (hm : 1 ≤ m) (hu : ∀ j < k, cutNetPt s mesh N j < 1)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (Kraw : ℕ → ℝ) (K : ℝ)
    (hKraw : ∀ j < k, ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)) /
        Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
          (zdist (d.L N) (a 0 - a 1)) ≤ Kraw j)
    (hK : ∀ j < k,
      Real.sqrt (cutNetPt s mesh N j) *
        (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ * Kraw j) ≤ K) :
    √(Gauss.quadVar d N
      (fun X => ((prefixMatrix d E D s mesh N k m X : ℝ) : ℂ)) M) ≤
      (k : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) *
      (((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) * K) := by
  classical
  by_cases hk : k = 0
  · subst hk
    have hzero : (fun X => ((prefixMatrix d E D s mesh N 0 m X : ℝ) : ℂ)) =
        fun _ => (0 : ℂ) := by
      funext X
      have hz : prefixMatrix d E D s mesh N 0 m X = 0 := by
        simp only [prefixMatrix, softMax, Finset.range_zero, Finset.sum_empty]
        exact Real.zero_rpow (ne_of_gt (by positivity :
          (0 : ℝ) < 1 / (2 * (m : ℝ))))
      simp [hz]
    rw [hzero]
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hexp : (0 : ℝ) ^ (((m : ℝ)⁻¹) * (2 : ℝ)⁻¹) = 0 :=
      Real.zero_rpow (ne_of_gt (by positivity :
        (0 : ℝ) < ((m : ℝ)⁻¹) * (2 : ℝ)⁻¹))
    simp [Gauss.quadVar, Gauss.coordD1, hexp]
  · let f : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun j X =>
      ((APrimeSmoothPrefix.smoothJSMatrix d E D s N
        (cutNetPt s mesh N j) (epsilon d D N) m
        ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • X) : ℝ) : ℂ)
    have hf : ∀ j ∈ Finset.range k, ContDiff ℝ 1 (f j) := by
      intro j hj
      have hbase := APrimeSmoothPrefix.contDiff_smoothJSMatrix d
        (E := E) (D := D) (u := cutNetPt s mesh N j)
        (ε := epsilon d D N) (s := s) (N := N) (m := m)
        hE hs (hu j (Finset.mem_range.mp hj)) (epsilon_pos d D hN) hm
      have hline : ContDiff ℝ 1
          (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
            (Real.sqrt (cutNetPt s mesh N j) : ℂ) • X) := by
        have hc : ContDiff ℝ 1
            (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
              Real.sqrt (cutNetPt s mesh N j)) := contDiff_const
        have hi : ContDiff ℝ 1
            (fun X : Matrix (d.Idx N) (d.Idx N) ℂ => X) := contDiff_id
        convert (hc.smul hi) using 1
      exact Complex.ofRealCLM.contDiff.comp (hbase.comp hline)
    have hY : 0 < ∑ j ∈ Finset.range k, (‖f j M‖ / (1 : ℝ)) ^ (2 * m) := by
      have hj0 : 0 < k := Nat.pos_of_ne_zero hk
      have hfj : 0 < ‖f 0 M‖ / (1 : ℝ) := by
        simp only [div_one, f, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (smoothJSMatrix_pos d hE hs (hu 0 hj0) _)]
        exact smoothJSMatrix_pos d hE hs (hu 0 hj0) _
      have hterm : 0 < (‖f 0 M‖ / (1 : ℝ)) ^ (2 * m) := pow_pos hfj _
      have hsum : (‖f 0 M‖ / (1 : ℝ)) ^ (2 * m) ≤
          ∑ j ∈ Finset.range k, (‖f j M‖ / (1 : ℝ)) ^ (2 * m) :=
        Finset.single_le_sum (s := Finset.range k)
          (f := fun j : ℕ => (‖f j M‖ / (1 : ℝ)) ^ (2 * m))
          (fun j _ => pow_nonneg (div_nonneg (norm_nonneg _) (by norm_num)) _)
          (Finset.mem_range.mpr hj0)
      exact lt_of_lt_of_le hterm hsum
    have hKouter : ∀ j ∈ Finset.range k,
        √(Gauss.quadVar d N (f j) M) / (1 : ℝ) ≤
          ((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
            ((1 : ℝ) / (2 * (m : ℝ)))) * K := by
      intro j hj
      have hinner := sqrt_quadVar_smoothJSMatrix_pullback_le d hE hs
        (hu j (Finset.mem_range.mp hj)) (epsilon_pos d D hN) hm M
        (Kraw j) (hKraw j (Finset.mem_range.mp hj))
      have hscale := hK j (Finset.mem_range.mp hj)
      have hcard : 0 ≤ (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ))) := by positivity
      dsimp [f]
      simp only [div_one]
      calc _ ≤ Real.sqrt (cutNetPt s mesh N j) *
          (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ *
            (((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
              ((1 : ℝ) / (2 * (m : ℝ)))) * Kraw j)) := hinner
        _ = ((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
              ((1 : ℝ) / (2 * (m : ℝ)))) *
            (Real.sqrt (cutNetPt s mesh N j) *
              (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ * Kraw j)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale hcard
    let C : ℝ := (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
      ((1 : ℝ) / (2 * (m : ℝ)))
    have houter := Gauss.sqrt_quadVar_softMax_le (d := d) (N := N)
      (S := Finset.range k) (f := f) (c := fun _ => (1 : ℝ))
      (r := m) (K := C * K) hm (by intro j hj; norm_num)
      hf M hY hKouter
    have heq : (fun X => ((prefixMatrix d E D s mesh N k m X : ℝ) : ℂ)) =
        (fun X => ((softMax m (Finset.range k) (fun j => ‖f j X‖ / 1) : ℝ) : ℂ)) := by
      funext X
      congr 1
      unfold prefixMatrix softMax
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [div_one, f, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (smoothJSMatrix_pos d hE hs
        (hu j (Finset.mem_range.mp hj)) _)]
    rw [heq]
    simpa only [Finset.card_range] using houter

theorem sqrt_quadVar_prefixMatrix_le_exp (d : Gauss.Dims)
    {E D : ℝ} {s mesh : ℕ → ℝ} {N k m : ℕ}
    (hE : |E| < 2) (hs : s N < 1) (hN : 0 < N)
    (hm : 1 ≤ m) (hu : ∀ j < k, cutNetPt s mesh N j < 1)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (Kraw : ℕ → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hcal : ((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1 : ℝ) / (2 * (m : ℝ))) ≤ Real.exp 1)
    (hKraw : ∀ j < k, ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)) /
        Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
          (zdist (d.L N) (a 0 - a 1)) ≤ Kraw j)
    (hK : ∀ j < k,
      Real.sqrt (cutNetPt s mesh N j) *
        (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ * Kraw j) ≤ K) :
    √(Gauss.quadVar d N
      (fun X => ((prefixMatrix d E D s mesh N k m X : ℝ) : ℂ)) M) ≤
      Real.exp 1 * K := by
  have h := sqrt_quadVar_prefixMatrix_le d hE hs hN hm hu M Kraw K hKraw hK
  calc _ ≤ (k : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) *
        (((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ)))) * K) := h
    _ = ((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ))) * K := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring
    _ ≤ Real.exp 1 * K := mul_le_mul_of_nonneg_right hcal hK0

/-- The rate is the actual nested maximum of the raw two-loop coordinate rates,
with the exact `√u_j` pullback and `R_j⁻⁴` normalization. -/
theorem sqrt_quadVar_prefixMatrix_le_exp_max (d : Gauss.Dims)
    {E D : ℝ} {s mesh : ℕ → ℝ} {N k m : ℕ}
    (hE : |E| < 2) (hs : s N < 1) (hN : 0 < N)
    (hk : 0 < k) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1)
    (hcal : ((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1 : ℝ) / (2 * (m : ℝ))) ≤ Real.exp 1)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N
      (fun X => ((prefixMatrix d E D s mesh N k m X : ℝ) : ℂ)) M) ≤
      Real.exp 1 *
        ((Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
          Real.sqrt (cutNetPt s mesh N j) *
            (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ *
              ((Finset.univ : Finset (LoopArg (d.L N) 2)).sup'
                Finset.univ_nonempty (fun a =>
                  √(Gauss.quadVar d N
                    (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
                    ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)) /
                    Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
                      (zdist (d.L N) (a 0 - a 1))))))) := by
  classical
  let Kraw : ℕ → ℝ := fun j =>
    (Finset.univ : Finset (LoopArg (d.L N) 2)).sup' Finset.univ_nonempty
      (fun a =>
        √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)) /
          Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
            (zdist (d.L N) (a 0 - a 1)))
  let K : ℝ := (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩
    (fun j => Real.sqrt (cutNetPt s mesh N j) *
      (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ * Kraw j))
  have hKraw : ∀ j < k, ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)) /
        Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
          (zdist (d.L N) (a 0 - a 1)) ≤ Kraw j := by
    intro j _ a
    simpa only [Kraw] using (Finset.le_sup'
      (fun b : LoopArg (d.L N) 2 =>
        √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) b)
          ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)) /
          Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N j)
            (zdist (d.L N) (b 0 - b 1))) (Finset.mem_univ a))
  have hK : ∀ j < k,
      Real.sqrt (cutNetPt s mesh N j) *
        (((Step2Moment.ratR E s N (cutNetPt s mesh N j)) ^ 4)⁻¹ * Kraw j) ≤ K := by
    intro j hj
    simpa only [K] using (Finset.le_sup'
      (fun i => Real.sqrt (cutNetPt s mesh N i) *
        (((Step2Moment.ratR E s N (cutNetPt s mesh N i)) ^ 4)⁻¹ * Kraw i))
      (Finset.mem_range.mpr hj))
  have hK0 : 0 ≤ K := by
    have hraw : 0 ≤ Kraw 0 := by
      let a : LoopArg (d.L N) 2 := Classical.choice inferInstance
      have hterm : 0 ≤ √(Gauss.quadVar d N
            (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N 0) a)
            ((Real.sqrt (cutNetPt s mesh N 0) : ℂ) • M)) /
          Step2.tT (Gauss.band d) E N D (cutNetPt s mesh N 0)
            (zdist (d.L N) (a 0 - a 1)) := by
        exact div_nonneg (Real.sqrt_nonneg _) (tailT_pos
          (by exact_mod_cast (Gauss.band d).W_pos N) _).le
      exact hterm.trans (hKraw 0 hk a)
    have hR : 0 < (Step2Moment.ratR E s N (cutNetPt s mesh N 0)) ^ 4 :=
      pow_pos (Step2Moment.ratR_pos hE hs (hu 0 hk)) _
    exact (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (inv_nonneg.mpr hR.le) hraw)).trans (hK 0 hk)
  simpa only [K, Kraw] using
    sqrt_quadVar_prefixMatrix_le_exp d hE hs hN hm hu M Kraw K hK0 hcal hKraw hK

theorem contDiff_cutoffMatrix (d : Gauss.Dims) {E D δ : ℝ} {s mesh : ℕ → ℝ}
    {N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    ContDiff ℝ 1 (cutoffMatrix d E D δ s mesh N k m) := by
  change ContDiff ℝ 1 (fun M =>
    cutChi (prefixMatrix d E D s mesh N k m M / threshold δ N))
  exact (contDiff_cutChi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp
    ((contDiff_prefixMatrix d hE hs hN hm hu).div_const _)

theorem continuous_cutoff (d : Gauss.Dims) {E D δ : ℝ} {s mesh : ℕ → ℝ}
    {N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    Continuous (cutoff d E D δ s mesh N k m) := by
  have hmatrix := (contDiff_cutoffMatrix d (E := E) (D := D) (δ := δ)
    (s := s) (mesh := mesh) (N := N) (k := k) (m := m) hE hs hN hm hu).continuous
  exact hmatrix.comp (Gauss.continuous_Xmat d N)

theorem contDiff_weightMatrix (d : Gauss.Dims) {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    {N₀ p N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    ContDiff ℝ 1 (weightMatrix d E D δ s t mesh N₀ p N k m) := by
  unfold weightMatrix
  split_ifs
  · exact (contDiff_cutoffMatrix d (E := E) (D := D) (δ := δ)
      (s := s) (mesh := mesh) (N := N) (k := k) (m := m)
      hE hs hN hm hu).pow (2 * p)
  · exact contDiff_const

theorem continuous_weight (d : Gauss.Dims) {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    {N₀ p N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    Continuous (weight d E D δ s t mesh N₀ p N k m) := by
  rw [show weight d E D δ s t mesh N₀ p N k m =
      fun ω => weightMatrix d E D δ s t mesh N₀ p N k m (Gauss.Xmat d N ω) from rfl]
  exact (contDiff_weightMatrix d (E := E) (D := D) (δ := δ)
    (s := s) (t := t) (mesh := mesh) (N₀ := N₀) (p := p)
    (N := N) (k := k) (m := m) hE hs hN hm hu).continuous.comp
    (Gauss.continuous_Xmat d N)

private theorem exists_coordFun_fderiv_bound (d : Gauss.Dims)
    {E u : ℝ} (hE : |E| < 2) (hu : u < 1) (N : ℕ)
    (a : LoopArg (d.L N) 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M,
      ‖fderiv ℝ (APrimeSmoothPrefix.coordFun d E N u a) M‖ ≤ C := by
  let η := etaT E u
  let B := 2 * (1 + η⁻¹) ^ 3
  have hη : 0 < η := Step2.etaT_pos' hE hu
  have hz : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact hη.ne'
  have hzη : η ≤ |(zt E u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  obtain ⟨hBa, hBb, hBc⟩ := Gauss.le_two_mul_one_add_inv_cube hη
  have hbdd := Gauss.bddC2C_loopObs_sub (d := d) (N := N)
    hz hη hzη hBa hBb hBc
    (LoopData.idx_wf ((Step2.sigPM, a) : LoopData (d.L N) 2))
    ((Gauss.band d).Kval E N u
      (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)))
  refine ⟨(Fintype.card (d.Idx N) : ℝ) *
    (((LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length : ℝ) *
      B ^ (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length) + 0,
    hbdd.nonneg₁, ?_⟩
  intro M
  exact hbdd.bdd₁ M

private theorem exists_smoothJSMatrix_fderiv_bound (d : Gauss.Dims)
    {E D u ε : ℝ} {s : ℕ → ℝ} {N m : ℕ}
    (hE : |E| < 2) (hs : s N < 1) (hu : u < 1)
    (hε : 0 < ε) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M,
      ‖fderiv ℝ (APrimeSmoothPrefix.smoothJSMatrix d E D s N u ε m) M‖ ≤ C := by
  classical
  let F : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    APrimeSmoothPrefix.coordFun d E N u
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  let g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    APrimeSmoothPrefix.smoothMaxOf m F c ε
  have hc : ∀ a, 0 < c a := by
    intro a
    exact tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
  have hF : ∀ a, ContDiff ℝ 1 (F a) :=
    APrimeSmoothPrefix.contDiff_coordFun d hE hu N
  let Ca : LoopArg (d.L N) 2 → ℝ := fun a =>
    Classical.choose (exists_coordFun_fderiv_bound d hE hu N a)
  have hCa0 : ∀ a, 0 ≤ Ca a := by
    intro a
    exact (Classical.choose_spec (exists_coordFun_fderiv_bound d hE hu N a)).1
  have hCa : ∀ a M, ‖fderiv ℝ (F a) M‖ ≤ Ca a := by
    intro a M
    exact (Classical.choose_spec (exists_coordFun_fderiv_bound d hE hu N a)).2 M
  obtain ⟨K, hK⟩ := Finset.exists_le
    ((Finset.univ : Finset (LoopArg (d.L N) 2)).image (fun a => Ca a / c a))
  have hK0 : 0 ≤ K := by
    let a : LoopArg (d.L N) 2 := Classical.choice inferInstance
    exact (div_nonneg (hCa0 a) (hc a).le).trans
      (hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hbound : ∀ a M, ‖fderiv ℝ (F a) M‖ / c a ≤ K := by
    intro a M
    exact (div_le_div_of_nonneg_right (hCa a M) (hc a).le).trans
      (hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hg : ContDiff ℝ 1 g :=
    APrimeSmoothPrefix.contDiff_smoothMaxOf hm hF hc hε
  have hR : 0 < (Step2Moment.ratR E s N u) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs hu) _
  refine ⟨((Step2Moment.ratR E s N u) ^ 4)⁻¹ *
    ((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
      ((1 : ℝ) / (2 * (m : ℝ))) * K), by positivity, ?_⟩
  intro M
  have hfd : fderiv ℝ (APrimeSmoothPrefix.smoothJSMatrix d E D s N u ε m) M =
      ((Step2Moment.ratR E s N u) ^ 4)⁻¹ • fderiv ℝ g M := by
    change fderiv ℝ (fun X => (1 + g X) / (Step2Moment.ratR E s N u) ^ 4) M = _
    rw [show (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
        (1 + g X) / (Step2Moment.ratR E s N u) ^ 4) =
        fun X => ((Step2Moment.ratR E s N u) ^ 4)⁻¹ • (1 + g X) from by
          funext X; simp [div_eq_mul_inv, smul_eq_mul, mul_comm]]
    change fderiv ℝ (((Step2Moment.ratR E s N u) ^ 4)⁻¹ •
      (fun X : Matrix (d.Idx N) (d.Idx N) ℂ => 1 + g X)) M = _
    rw [fderiv_const_smul_field, Pi.smul_apply, fderiv_const_add]
  rw [hfd, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  exact mul_le_mul_of_nonneg_left
    (norm_fderiv_smoothMaxOf_le F c ε m hm hε hc hF K hK0 hbound M)
    (inv_nonneg.mpr hR.le)

private theorem exists_prefixMatrix_fderiv_bound (d : Gauss.Dims)
    {E D : ℝ} {s mesh : ℕ → ℝ} {N k m : ℕ}
    (hE : |E| < 2) (hs : s N < 1) (hN : 0 < N)
    (hm : 1 ≤ m) (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M,
      ‖fderiv ℝ (prefixMatrix d E D s mesh N k m) M‖ ≤ C := by
  classical
  by_cases hk : k = 0
  · subst hk
    refine ⟨0, le_rfl, ?_⟩
    intro M
    have hz : prefixMatrix d E D s mesh N 0 m = fun _ => (0 : ℝ) := by
      funext X
      simp only [prefixMatrix, softMax, Finset.range_zero, Finset.sum_empty]
      exact Real.zero_rpow (ne_of_gt (by positivity :
        (0 : ℝ) < 1 / (2 * (m : ℝ))))
    simp [hz]
  · let f : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun j X =>
      ((APrimeSmoothPrefix.smoothJSMatrix d E D s N
        (cutNetPt s mesh N j) (epsilon d D N) m
        ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • X) : ℝ) : ℂ)
    let Cj : ℕ → ℝ := fun j =>
      if hj : j < k then Classical.choose
        (exists_smoothJSMatrix_fderiv_bound d (E := E) (D := D)
          (u := cutNetPt s mesh N j) (ε := epsilon d D N) (s := s) (N := N) (m := m)
          hE hs (hu j hj)
          (epsilon_pos d D hN) hm) else 0
    have hCj0 : ∀ j < k, 0 ≤ Cj j := by
      intro j hj
      simp only [Cj, dif_pos hj]
      exact (Classical.choose_spec
        (exists_smoothJSMatrix_fderiv_bound d (E := E) (D := D)
          (u := cutNetPt s mesh N j) (ε := epsilon d D N) (s := s) (N := N) (m := m)
          hE hs (hu j hj)
          (epsilon_pos d D hN) hm)).1
    have hCj : ∀ j < k, ∀ X,
        ‖fderiv ℝ (APrimeSmoothPrefix.smoothJSMatrix d E D s N
          (cutNetPt s mesh N j) (epsilon d D N) m) X‖ ≤ Cj j := by
      intro j hj X
      simpa only [Cj, dif_pos hj] using
        (Classical.choose_spec
          (exists_smoothJSMatrix_fderiv_bound d (E := E) (D := D)
            (u := cutNetPt s mesh N j) (ε := epsilon d D N) (s := s) (N := N) (m := m)
            hE hs (hu j hj)
            (epsilon_pos d D hN) hm)).2 X
    obtain ⟨K, hK⟩ := Finset.exists_le
      ((Finset.range k).image (fun j => Real.sqrt (cutNetPt s mesh N j) * Cj j))
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hK0 : 0 ≤ K := by
      exact (mul_nonneg (Real.sqrt_nonneg _) (hCj0 0 hk0)).trans
        (hK _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk0)))
    have hf : ∀ j ∈ Finset.range k, ContDiff ℝ 1 (f j) := by
      intro j hj
      have hbase := APrimeSmoothPrefix.contDiff_smoothJSMatrix d
        (E := E) (D := D) (u := cutNetPt s mesh N j)
        (ε := epsilon d D N) (s := s) (N := N) (m := m)
        hE hs (hu j (Finset.mem_range.mp hj)) (epsilon_pos d D hN) hm
      have hline : ContDiff ℝ 1
          (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
            (Real.sqrt (cutNetPt s mesh N j) : ℂ) • X) := by
        have hc : ContDiff ℝ 1
            (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
              Real.sqrt (cutNetPt s mesh N j)) := contDiff_const
        exact (hc.smul contDiff_id : ContDiff ℝ 1
          (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
            Real.sqrt (cutNetPt s mesh N j) • X))
      exact Complex.ofRealCLM.contDiff.comp (hbase.comp hline)
    have hY : ∀ M, 0 < ∑ j ∈ Finset.range k, (‖f j M‖ / (1 : ℝ)) ^ (2 * m) := by
      intro M
      have hfj : 0 < ‖f 0 M‖ / (1 : ℝ) := by
        simp only [div_one, f, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (smoothJSMatrix_pos d hE hs (hu 0 hk0) _)]
        exact smoothJSMatrix_pos d hE hs (hu 0 hk0) _
      exact (pow_pos hfj _).trans_le (Finset.single_le_sum
        (s := Finset.range k) (f := fun j => (‖f j M‖ / (1 : ℝ)) ^ (2 * m))
        (fun j _ => pow_nonneg (div_nonneg (norm_nonneg _) (by norm_num)) _)
        (Finset.mem_range.mpr hk0))
    have hdir : ∀ j ∈ Finset.range k, ∀ M B,
        ‖fderiv ℝ (f j) M B‖ / (1 : ℝ) ≤ K * ‖B‖ := by
      intro j hj M B
      have hjk := Finset.mem_range.mp hj
      let g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
        APrimeSmoothPrefix.smoothJSMatrix d E D s N
          (cutNetPt s mesh N j) (epsilon d D N) m
      have hbase := APrimeSmoothPrefix.contDiff_smoothJSMatrix d
        (E := E) (D := D) (u := cutNetPt s mesh N j)
        (ε := epsilon d D N) (s := s) (N := N) (m := m)
        hE hs (hu j hjk) (epsilon_pos d D hN) hm
      have hdiff : DifferentiableAt ℝ
          (fun X => g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • X)) M := by
        exact (hbase.comp (by fun_prop : ContDiff ℝ 1
          (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
            (Real.sqrt (cutNetPt s mesh N j) : ℂ) • X))).differentiable
            (by norm_num) M
      have heq : ‖fderiv ℝ (f j) M B‖ =
          |fderiv ℝ (fun X => g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • X)) M B| := by
        exact norm_fderiv_ofReal_apply M hdiff B
      rw [div_one, heq]
      have hpull : fderiv ℝ
          (fun X => g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • X)) M =
          Real.sqrt (cutNetPt s mesh N j) •
            fderiv ℝ g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) := by
        rw [show (fun X : Matrix (d.Idx N) (d.Idx N) ℂ =>
            g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • X)) =
            (fun X => g (Real.sqrt (cutNetPt s mesh N j) • X)) from rfl]
        rw [fderiv_comp_smul]
        congr 1
      rw [hpull]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hroot : 0 ≤ Real.sqrt (cutNetPt s mesh N j) := Real.sqrt_nonneg _
      have hnorm :
          |Real.sqrt (cutNetPt s mesh N j) *
            fderiv ℝ g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) B| ≤
          Cj j * (Real.sqrt (cutNetPt s mesh N j) * ‖B‖) := by
        calc
          _ = Real.sqrt (cutNetPt s mesh N j) *
              ‖fderiv ℝ g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M) B‖ := by
                simp [abs_mul, abs_of_nonneg hroot, Real.norm_eq_abs]
          _ ≤ Real.sqrt (cutNetPt s mesh N j) *
              (‖fderiv ℝ g ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • M)‖ * ‖B‖) :=
              mul_le_mul_of_nonneg_left ((fderiv ℝ g _).le_opNorm B) hroot
          _ ≤ Cj j * (Real.sqrt (cutNetPt s mesh N j) * ‖B‖) := by
              calc
                _ ≤ Real.sqrt (cutNetPt s mesh N j) * (Cj j * ‖B‖) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right (hCj j hjk _) (norm_nonneg B)) hroot
                _ = _ := by ring
      exact hnorm.trans (by
        calc Cj j * (Real.sqrt (cutNetPt s mesh N j) * ‖B‖) =
            (Real.sqrt (cutNetPt s mesh N j) * Cj j) * ‖B‖ := by ring
          _ ≤ K * ‖B‖ := mul_le_mul_of_nonneg_right
            (hK _ (Finset.mem_image_of_mem _ hj)) (norm_nonneg _))
    have heq : prefixMatrix d E D s mesh N k m =
        fun X => softMax m (Finset.range k) (fun j => ‖f j X‖ / 1) := by
      funext X
      unfold prefixMatrix softMax
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [div_one, f, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (smoothJSMatrix_pos d hE hs
        (hu j (Finset.mem_range.mp hj)) _)]
    refine ⟨(k : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) * K, by positivity, ?_⟩
    intro M
    rw [heq]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun B => ?_)
    rw [Real.norm_eq_abs]
    have h := abs_fderiv_softMax_le_of_bound (Finset.range k) f
      (fun _ => (1 : ℝ)) m hm (by intro j hj; norm_num) hf M B
      (hY M) (K * ‖B‖) (mul_nonneg hK0 (norm_nonneg _))
      (by intro j hj; simpa only [div_one] using hdir j hj M B)
    simpa only [Finset.card_range, mul_assoc] using h

private theorem norm_fderiv_cutChi_pow_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : V → ℝ) (hg : ContDiff ℝ 1 g) (Θ : ℝ) (hΘ : 0 < Θ)
    (p : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ M, ‖fderiv ℝ g M‖ ≤ C) (M : V) :
    ‖fderiv ℝ (fun X => cutChi (g X / Θ) ^ (2 * p)) M‖ ≤
      ((2 * p : ℕ) : ℝ) * ((15 / 8) / Θ) * C := by
  let w : V → ℝ := fun X => cutChi (g X / Θ)
  have hdiv : HasFDerivAt (fun X => g X / Θ)
      (Θ⁻¹ • fderiv ℝ g M) M := by
    have hd := ((hg.differentiable (by norm_num) M).hasFDerivAt).const_mul (Θ⁻¹ : ℝ)
    simpa [div_eq_inv_mul] using hd
  have hw : HasFDerivAt w
      (cutChiD (g M / Θ) • (Θ⁻¹ • fderiv ℝ g M)) M := by
    simpa only [w, Function.comp_def] using
      (hasDerivAt_cutChi (g M / Θ)).comp_hasFDerivAt M hdiv
  have hwp := hw.pow (2 * p)
  have hχ0 : 0 ≤ w M := cutChi_nonneg _
  have hχ1 : w M ≤ 1 := cutChi_le_one _
  have hχpow : w M ^ (2 * p - 1) ≤ 1 := pow_le_one₀ hχ0 hχ1
  have hχd : |cutChiD (g M / Θ)| ≤ 15 / 8 := abs_cutChiD_le _
  have hΘinv : 0 ≤ Θ⁻¹ := inv_nonneg.mpr hΘ.le
  have hcast : 0 ≤ ((2 * p : ℕ) : ℝ) := by positivity
  change ‖fderiv ℝ (fun X => w X ^ (2 * p)) M‖ ≤ _
  rw [hwp.fderiv, norm_smul, Real.norm_eq_abs, nsmul_eq_mul,
    abs_of_nonneg (mul_nonneg hcast (pow_nonneg hχ0 _))]
  calc
    ((2 * p : ℕ) : ℝ) * w M ^ (2 * p - 1) *
        ‖cutChiD (g M / Θ) • (Θ⁻¹ • fderiv ℝ g M)‖
      ≤ ((2 * p : ℕ) : ℝ) *
        ((15 / 8) * (Θ⁻¹ * C)) := by
          rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hΘinv]
          have hinner : ‖fderiv ℝ g M‖ ≤ C := hC M
          have hχpow0 : 0 ≤ w M ^ (2 * p - 1) := pow_nonneg hχ0 _
          have hbound : w M ^ (2 * p - 1) *
              (|cutChiD (g M / Θ)| * (Θ⁻¹ * ‖fderiv ℝ g M‖)) ≤
              (15 / 8) * (Θ⁻¹ * C) := by
            have ha : Θ⁻¹ * ‖fderiv ℝ g M‖ ≤ Θ⁻¹ * C :=
              mul_le_mul_of_nonneg_left hinner hΘinv
            have hb : |cutChiD (g M / Θ)| * (Θ⁻¹ * ‖fderiv ℝ g M‖) ≤
                (15 / 8) * (Θ⁻¹ * C) :=
              mul_le_mul hχd ha (by positivity) (by norm_num)
            calc
              _ ≤ w M ^ (2 * p - 1) * ((15 / 8) * (Θ⁻¹ * C)) :=
                mul_le_mul_of_nonneg_left hb hχpow0
              _ ≤ 1 * ((15 / 8) * (Θ⁻¹ * C)) :=
                mul_le_mul_of_nonneg_right hχpow (by positivity)
              _ = _ := by ring
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hcast
    _ = ((2 * p : ℕ) : ℝ) * ((15 / 8) / Θ) * C := by
      rw [div_eq_mul_inv]
      ring

private theorem weightC1_of_matrix (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ)
    (hF : ContDiff ℝ 1 F) (hval : ∀ M, |F M| ≤ 1)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ M, ‖fderiv ℝ F M‖ ≤ C) :
    Gauss.WeightC1 d N (fun ω => F (Gauss.Xmat d N ω))
      (fun q ω => fderiv ℝ F (Gauss.Xmat d N ω)
        (Gauss.Bmat d N q.1 q.2.1 q.2.2)) := by
  classical
  obtain ⟨C, hC0, hC⟩ := hbd
  let I : Finset (Gauss.Coord d) :=
    (Gauss.usedCoord d N).image (Gauss.crd d N)
  have hcongr : ∀ ω ω' : Gauss.Ω d,
      (∀ e ∈ I, ω e = ω' e) →
      Gauss.Xmat d N ω = Gauss.Xmat d N ω' := by
    intro ω ω' h
    have hh := Gauss.Hflow_congr_of_agree d N 1 ω ω' h
    simpa [Gauss.Hflow_eq_realSmul] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF.continuous.comp (Gauss.continuous_Xmat d N)
  · intro q _
    exact ((hF.continuous_fderiv (by norm_num)).comp (Gauss.continuous_Xmat d N)).clm_apply
      continuous_const
  · exact ⟨I, fun ω ω' h => congrArg F (hcongr ω ω' h)⟩
  · intro q _
    exact ⟨I, fun ω ω' h => congrArg
      (fun M => fderiv ℝ F M (Gauss.Bmat d N q.1 q.2.1 q.2.2))
      (hcongr ω ω' h)⟩
  · intro q hq ω
    have hpath := Gauss.hasDerivAt_Hflow_update d N 1 ω hq
    have hpath' : HasDerivAt
        (fun t : ℝ => Gauss.Xmat d N (Function.update ω (Gauss.crd d N q) t))
        (Gauss.Bmat d N q.1 q.2.1 q.2.2) (ω (Gauss.crd d N q)) := by
      simpa [Gauss.Hflow_eq_realSmul] using hpath
    have hself : Gauss.Xmat d N
        (Function.update ω (Gauss.crd d N q) (ω (Gauss.crd d N q))) =
          Gauss.Xmat d N ω := by simp
    have hcomp := ((hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt
      (ω (Gauss.crd d N q)) hpath')
    rw [hself] at hcomp
    change HasDerivAt (fun t => F (Gauss.Xmat d N
      (Function.update ω (Gauss.crd d N q) t)))
      (fderiv ℝ F (Gauss.Xmat d N ω)
        (Gauss.Bmat d N q.1 q.2.1 q.2.2)) (ω (Gauss.crd d N q))
    exact hcomp
  · exact ⟨1, fun ω => hval _⟩
  · obtain ⟨B, hB⟩ := Finset.exists_le
      ((Gauss.usedCoord d N).image
        (fun q => ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖))
    refine ⟨C * B, ?_⟩
    intro q hq ω
    have hBq : ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ ≤ B :=
      hB _ (Finset.mem_image_of_mem _ hq)
    have h1 : |fderiv ℝ F (Gauss.Xmat d N ω)
        (Gauss.Bmat d N q.1 q.2.1 q.2.2)| ≤
        ‖fderiv ℝ F (Gauss.Xmat d N ω)‖ *
          ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ := by
      simpa [Real.norm_eq_abs] using
        (fderiv ℝ F (Gauss.Xmat d N ω)).le_opNorm
          (Gauss.Bmat d N q.1 q.2.1 q.2.2)
    calc _ ≤ ‖fderiv ℝ F (Gauss.Xmat d N ω)‖ *
          ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ := h1
      _ ≤ C * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ :=
        mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      _ ≤ C * B := mul_le_mul_of_nonneg_left hBq hC0

/-- The actual Gaussian finite-prefix cutoff has the seven `WeightC1` fields.
The uniform derivative constant comes from resolvent bounds, finite coordinate
maxima, regularization contraction and the bounded cutoff derivative. -/
theorem weightC1 (d : Gauss.Dims) {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    {N₀ p N k m : ℕ} (hE : |E| < 2) (hs : s N < 1)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1) :
    Gauss.WeightC1 d N (weight d E D δ s t mesh N₀ p N k m)
      (weightD d E D δ s t mesh N₀ p N k m) := by
  let F := weightMatrix d E D δ s t mesh N₀ p N k m
  have hF : ContDiff ℝ 1 F :=
    contDiff_weightMatrix d hE hs hN hm hu
  have hval : ∀ M, |F M| ≤ 1 := by
    intro M
    dsimp [F, weightMatrix]
    split_ifs
    · let x := cutoffMatrix d E D δ s mesh N k m M
      have hx0 : 0 ≤ x := cutChi_nonneg _
      have hx1 : x ≤ 1 := cutChi_le_one _
      rw [abs_of_nonneg (pow_nonneg hx0 _)]
      exact pow_le_one₀ hx0 hx1
    · norm_num
  obtain ⟨C, hC0, hC⟩ := exists_prefixMatrix_fderiv_bound d
    (E := E) (D := D) (s := s) (mesh := mesh) (N := N) (k := k) (m := m)
    hE hs hN hm hu
  have hbd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ M, ‖fderiv ℝ F M‖ ≤ C' := by
    refine ⟨((2 * p : ℕ) : ℝ) * ((15 / 8) / threshold δ N) * C,
      by have hΘ := threshold_pos (δ := δ) hN; positivity, ?_⟩
    intro M
    dsimp only [F]
    unfold weightMatrix
    split_ifs
    · exact norm_fderiv_cutChi_pow_le
        (prefixMatrix d E D s mesh N k m)
        (contDiff_prefixMatrix d hE hs hN hm hu)
        (threshold δ N) (threshold_pos hN) p C hC0 hC M
    · have hΘ := threshold_pos (δ := δ) hN
      simp
      positivity
  change Gauss.WeightC1 d N (fun ω => F (Gauss.Xmat d N ω))
    (fun q ω => fderiv ℝ F (Gauss.Xmat d N ω)
      (Gauss.Bmat d N q.1 q.2.1 q.2.2))
  exact weightC1_of_matrix d N F hF hval hbd

/-- The inner regularized maximum is controlled by the actual normalized hard
observable, with only its label-cardinality factor and the explicit smoothing
error. -/
theorem smoothJS_le_card_mul_jSnorm_add (d : Gauss.Dims)
    {E D u : ℝ} {s : ℕ → ℝ} {N m : ℕ}
    (hE : |E| < 2) (hsu : s N ≤ u) (hu : u < 1)
    (hN : 0 < N) (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    APrimeSmoothPrefix.smoothJS d E D s N u (epsilon d D N) m ω ≤
      ((Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) *
      (Step2Moment.jSnorm (Gauss.sample d) E D s N u ω +
        (N : ℝ) ^ (-(10 : ℝ))) := by
  let A : ℝ := (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
    ((1 : ℝ) / (2 * (m : ℝ)))
  let R : ℝ := (Step2Moment.ratR E s N u) ^ 4
  let H : ℝ := (Finset.univ : Finset (LoopArg (d.L N) 2)).sup'
    Finset.univ_nonempty (fun a =>
      ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)))
  have hR1 : 1 ≤ R := one_le_pow₀ (Step2Moment.one_le_ratR hE hsu hu)
  have hR0 : 0 < R := by linarith
  have hA1 : 1 ≤ A := by
    have hcard : (1 : ℝ) ≤ Fintype.card (LoopArg (d.L N) 2) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.one_le_rpow hcard (by positivity)
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast (Gauss.band d).W_pos N
  have hH0 : 0 ≤ H := by
    let a : LoopArg (d.L N) 2 := Classical.choice inferInstance
    have hc : 0 < Step2.tT (Gauss.band d) E N D u
        (zdist (d.L N) (a 0 - a 1)) := tailT_pos hW _
    have ht : 0 ≤ ‖Step2.lk (Gauss.sample d) E N u ω a‖ /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)) :=
      div_nonneg (norm_nonneg _) hc.le
    exact ht.trans (by simpa only [H] using (Finset.le_sup'
      (fun b : LoopArg (d.L N) 2 =>
        ‖Step2.lk (Gauss.sample d) E N u ω b‖ /
          Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (b 0 - b 1)))
      (Finset.mem_univ a)))
  have hJ : Step2Moment.jSnorm (Gauss.sample d) E D s N u ω = (H + 1) / R := by
    change Step2.jS (Gauss.sample d) E D N u ω / R = _
    congr 1
  have hε : 0 < epsilon d D N := epsilon_pos d D hN
  have hεratio : epsilon d D N / (d.W N : ℝ) ^ (-D) =
      (N : ℝ) ^ (-(10 : ℝ)) := by
    unfold epsilon
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hW _)]
  have hsm := APrimeSmoothPrefix.smoothJS_le_hard d
    (E := E) (D := D) (u := u) (ε := epsilon d D N) (s := s) (N := N) (m := m)
    hE (hsu.trans_lt hu) hu hε.le hm ω
  rw [hεratio] at hsm
  have hsm' : APrimeSmoothPrefix.smoothJS d E D s N u (epsilon d D N) m ω ≤
      (1 + A * (H + (N : ℝ) ^ (-(10 : ℝ)))) / R := by
    simpa only [A, R, H, Finset.card_univ] using hsm
  have hn10 : 0 ≤ (N : ℝ) ^ (-(10 : ℝ)) := by positivity
  have hn10R : (N : ℝ) ^ (-(10 : ℝ)) / R ≤ (N : ℝ) ^ (-(10 : ℝ)) := by
    apply (div_le_iff₀ hR0).2
    nlinarith [mul_nonneg hn10 (sub_nonneg.mpr hR1)]
  rw [hJ]
  change APrimeSmoothPrefix.smoothJS d E D s N u (epsilon d D N) m ω ≤
    A * ((H + 1) / R + (N : ℝ) ^ (-(10 : ℝ)))
  calc
    _ ≤ (1 + A * (H + (N : ℝ) ^ (-(10 : ℝ)))) / R := hsm'
    _ ≤ (A * (1 + H + (N : ℝ) ^ (-(10 : ℝ)))) / R := by
      apply div_le_div_of_nonneg_right _ hR0.le
      nlinarith
    _ = A * ((H + 1) / R + (N : ℝ) ^ (-(10 : ℝ)) / R) := by ring
    _ ≤ A * ((H + 1) / R + (N : ℝ) ^ (-(10 : ℝ))) := by gcongr

/-- Two calibrated smooth maxima cost one combined cardinal factor. -/
theorem prefixSample_le_of_jSnorm_bound (d : Gauss.Dims)
    {E D B : ℝ} {s t mesh : ℕ → ℝ} {N k m : ℕ}
    (hE : |E| < 2) (hst : s N ≤ t N) (ht : t N < 1)
    (hmesh : 0 < mesh N) (hN : 0 < N) (hm : 1 ≤ m)
    (hk : k ≤ cutNetTop s t mesh N) (hB0 : 0 ≤ B)
    (ω : Gauss.Ω d)
    (hJ : ∀ j < k, Step2Moment.jSnorm (Gauss.sample d) E D s N
      (cutNetPt s mesh N j) ω ≤ B) :
    prefixSample d E D s mesh N k m ω ≤
      (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
        ((1 : ℝ) / (2 * (m : ℝ)))) *
      (B + (N : ℝ) ^ (-(10 : ℝ))) := by
  classical
  let A : ℝ := (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
    ((1 : ℝ) / (2 * (m : ℝ)))
  have hA0 : 0 ≤ A := by positivity
  have hJsm : ∀ j ∈ Finset.range k,
      APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N j)
        (epsilon d D N) m ω ≤ A * (B + (N : ℝ) ^ (-(10 : ℝ))) := by
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have huIcc : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
      netFinset_subset_Icc hst hmesh _
        (cutNetPt_mem_netFinset (hjk.le.trans hk))
    have hinner := smoothJS_le_card_mul_jSnorm_add d
      (E := E) (D := D) (u := cutNetPt s mesh N j) (s := s) (N := N) (m := m)
      hE huIcc.1 (huIcc.2.trans_lt ht) hN hm ω
    calc
      _ ≤ A * (Step2Moment.jSnorm (Gauss.sample d) E D s N
          (cutNetPt s mesh N j) ω + (N : ℝ) ^ (-(10 : ℝ))) := hinner
      _ ≤ A * (B + (N : ℝ) ^ (-(10 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [add_comm] using
          (add_le_add_right (hJ j hjk) ((N : ℝ) ^ (-(10 : ℝ))))) hA0
  have hM0 : 0 ≤ A * (B + (N : ℝ) ^ (-(10 : ℝ))) := by positivity
  have heq : prefixSample d E D s mesh N k m ω =
      softMax m (Finset.range k) (fun j =>
        APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N j)
          (epsilon d D N) m ω) := by
    change softMax m (Finset.range k) (fun j =>
      APrimeSmoothPrefix.smoothJSMatrix d E D s N (cutNetPt s mesh N j)
        (epsilon d D N) m
        ((Real.sqrt (cutNetPt s mesh N j) : ℂ) • Gauss.Xmat d N ω)) = _
    apply congrArg (fun f : ℕ → ℝ => softMax m (Finset.range k) f)
    funext j
    have hflow := APrimeSmoothPrefix.smoothJSMatrix_flow d E D s N
      (cutNetPt s mesh N j) (epsilon d D N) m ω
    rw [Gauss.Hflow_eq_realSmul] at hflow
    exact hflow
  rw [heq]
  have houter := softMax_le hm hM0 (S := Finset.range k)
    (ρ := fun j => APrimeSmoothPrefix.smoothJS d E D s N
      (cutNetPt s mesh N j) (epsilon d D N) m ω) (M := A * (B + (N : ℝ) ^ (-(10 : ℝ))))
    (by
      intro j hj
      have huIcc : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
        netFinset_subset_Icc hst hmesh _
          (cutNetPt_mem_netFinset ((Finset.mem_range.mp hj).le.trans hk))
      rw [abs_of_pos (APrimeSmoothPrefix.smoothJS_pos d hE
        (huIcc.1.trans_lt (huIcc.2.trans_lt ht)) (huIcc.2.trans_lt ht)
        m ω)]
      exact hJsm j hj)
  calc
    _ ≤ (k : ℝ) ^ ((1 : ℝ) / (2 * (m : ℝ))) *
        (A * (B + (N : ℝ) ^ (-(10 : ℝ)))) := by
          simpa only [Finset.card_range] using houter
    _ = (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
          ((1 : ℝ) / (2 * (m : ℝ)))) *
          (B + (N : ℝ) ^ (-(10 : ℝ))) := by
            rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
            ring

/-- A finite explicit smoothing order satisfies the joint net/label calibration
for every prefix of this net. -/
noncomputable def canonicalM (d : Gauss.Dims) (s t mesh : ℕ → ℝ) (N : ℕ) : ℕ :=
  cutNetTop s t mesh N * Fintype.card (LoopArg (d.L N) 2) + 1

theorem canonicalM_pos (d : Gauss.Dims) (s t mesh : ℕ → ℝ) (N : ℕ) :
    1 ≤ canonicalM d s t mesh N := by
  unfold canonicalM
  omega

theorem canonicalM_calibration (d : Gauss.Dims) (s t mesh : ℕ → ℝ)
    (N k : ℕ) (hk : k ≤ cutNetTop s t mesh N) :
    (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1 : ℝ) / (2 * (canonicalM d s t mesh N : ℝ)))) ≤ Real.exp 1 := by
  unfold canonicalM
  exact APrimeWeight.card_calib_top
    (cutNetTop s t mesh N * Fintype.card (LoopArg (d.L N) 2))
    (k * Fintype.card (LoopArg (d.L N) 2))
    (Nat.mul_le_mul_right _ hk)

/-- The literal widened old prefix weight is pointwise bounded by the actual
smooth Gaussian weight at the enlarged threshold `8e²N^(2δ)`. All branches,
including `p=0`, `k=0`, and `N<2`, use the same sample and net times. -/
theorem widenedW_le_weight (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ} (m : ℕ → ℕ)
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    (N p k : ℕ) (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hm : 2 ≤ N → 1 ≤ m N)
    (hcal : 2 ≤ N → k ≤ cutNetTop s t mesh N →
      (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
        ((1 : ℝ) / (2 * (m N : ℝ)))) ≤ Real.exp 1) :
    APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω ≤
      weight d E D δ s t mesh 2 p N k (m N) ω := by
  let J : ℕ → ℝ → Gauss.Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω
  by_cases hnew : k ≤ cutNetTop s t mesh N ∧ 2 ≤ N
  · have hN2 : 2 ≤ N := hnew.2
    have hN : 0 < N := by omega
    have hold : k ≤ cutNetTop s t mesh N ∧ 1 ≤ N := ⟨hnew.1, by omega⟩
    by_cases hp : p = 0
    · subst p
      simp [APrimeWeight.widenedW, weight, hold, hnew]
    by_cases hk : k = 0
    · subst k
      exact (APrimeWeight.widenedW_le_one
        (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N 0 ω).trans
        (by rw [weight_zero_prefix d E D δ s t mesh 2 p N (m N) (hm hN2) ω])
    let θ : ℝ := 2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N
    have hθ : 0 < θ := by
      dsimp [θ]
      exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
        (APrimePrior.priorLevel_pos (by omega) (by norm_num))
    by_cases hsw : APrimeWeight.prefixSoftW (APrimeWeight.canonicalR s t mesh N)
        J s mesh N k θ ω = 0
    · have hOldZero : APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
          J s t mesh δ p N k ω = 0 := by
        rw [APrimeWeight.widenedW, if_pos hold]
        change (APrimeWeight.prefixSoftW (APrimeWeight.canonicalR s t mesh N)
          J s mesh N k θ ω) ^ (2 * p) = 0
        rw [hsw]
        exact zero_pow (by omega : 2 * p ≠ 0)
      rw [hOldZero]
      exact weight_nonneg d E D δ s t mesh 2 p N k (m N) ω
    · have hJbound : ∀ j < k,
          Step2Moment.jSnorm (Gauss.sample d) E D s N
            (cutNetPt s mesh N j) ω ≤
          4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) := by
        intro j hj
        have habs := abs_le_two_mul_of_softW_ne_zero
          (r := APrimeWeight.canonicalR s t mesh N)
          (S := Finset.range k) (ρ := fun j => J N (cutNetPt s mesh N j) ω)
          (Θ := θ) (by simp [APrimeWeight.canonicalR]) hθ hsw
          (Finset.mem_range.mpr hj)
        calc
          _ ≤ |J N (cutNetPt s mesh N j) ω| := le_abs_self _
          _ ≤ 2 * θ := habs
          _ = 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) := by
            simp [θ, APrimePrior.priorLevel]
            ring
      have hNcast : (1 : ℝ) ≤ N := by
        have hN1 : 1 ≤ N := by omega
        exact_mod_cast hN1
      have hpow1 : 1 ≤ (N : ℝ) ^ (2 * δ) :=
        Real.one_le_rpow hNcast (by linarith)
      have hpow0 : 0 ≤ (N : ℝ) ^ (2 * δ) := by positivity
      have hn10 : (N : ℝ) ^ (-(10 : ℝ)) ≤ (N : ℝ) ^ (2 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hNcast (by linarith)
      have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have he2 : Real.exp 1 ≤ (Real.exp 1) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr he1) he0]
      have hB0 : 0 ≤ 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) := by positivity
      have hprefix := prefixSample_le_of_jSnorm_bound d
        (E := E) (D := D) (B := 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ))
        (s := s) (t := t) (mesh := mesh) (N := N) (k := k) (m := m N)
        hE hst ht hmesh hN (hm hN2) hnew.1 hB0 ω hJbound
      have hcap : prefixSample d E D s mesh N k (m N) ω ≤ threshold δ N := by
        calc
          _ ≤ (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
              ((1 : ℝ) / (2 * (m N : ℝ)))) *
              (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) +
                (N : ℝ) ^ (-(10 : ℝ))) := hprefix
          _ ≤ Real.exp 1 * (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) +
                (N : ℝ) ^ (-(10 : ℝ))) :=
                  mul_le_mul_of_nonneg_right (hcal hN2 hnew.1) (by positivity)
          _ ≤ Real.exp 1 * (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) +
                (N : ℝ) ^ (2 * δ)) :=
                  mul_le_mul_of_nonneg_left (by simpa only [add_comm] using
                    (add_le_add_left hn10 (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ)))) he0
          _ = 4 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (2 * δ) +
                Real.exp 1 * (N : ℝ) ^ (2 * δ) := by ring
          _ ≤ 5 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (2 * δ) := by
                nlinarith [mul_le_mul_of_nonneg_right he2 hpow0]
          _ ≤ threshold δ N := by
                unfold threshold
                nlinarith [sq_nonneg (Real.exp 1)]
      have hcut : cutoff d E D δ s mesh N k (m N) ω = 1 := by
        unfold cutoff
        exact cutChi_eq_one ((div_le_one (threshold_pos hN)).2 hcap)
      have hnewOne : weight d E D δ s t mesh 2 p N k (m N) ω = 1 := by
        rw [weight, if_pos hnew]
        simp [hcut]
      rw [hnewOne]
      exact APrimeWeight.widenedW_le_one
        (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N k ω
  · have hnewOne : weight d E D δ s t mesh 2 p N k (m N) ω = 1 := by
      rw [weight, if_neg hnew]
    rw [hnewOne]
    exact APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N k ω

/-- The comparison has a concrete smoothing order for every finite net. -/
theorem widenedW_le_weight_canonical (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    (N p k : ℕ) (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N) :
    APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω ≤
      weight d E D δ s t mesh 2 p N k
        (canonicalM d s t mesh N) ω := by
  exact widenedW_le_weight d (canonicalM d s t mesh) hE hδ N p k ω
    hst ht hmesh (fun _ => canonicalM_pos d s t mesh N)
    (fun _ hk => canonicalM_calibration d s t mesh N k hk)

#print axioms sqrt_quadVar_prefixMatrix_le_exp_max
#print axioms weightC1
#print axioms prefixSample_le_of_jSnorm_bound
#print axioms widenedW_le_weight
#print axioms widenedW_le_weight_canonical

end APrimeSmoothWeightActual
end RBM

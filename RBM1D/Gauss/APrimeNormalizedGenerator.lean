/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftTimeFamily

/-!
# The fixed-scale normalized generator comparison

The endpoint scale is positive and independent of the running time and matrix.
Consequently the raw Gaussian generator comparison scales by its `2p`-th
inverse power, with the drift coordinate and evolved quadratic variation
scaled by the first and second powers respectively.
-/

namespace RBM.APrimeNormalizedGenerator

open RBM.Gauss RBM.APrimeDriftTimeFamily
open scoped Matrix.Norms.L2Operator

private theorem timeD1_const_smul {d : Gauss.Dims} {N : ℕ}
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (k : ℝ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Gauss.timeD1 (fun r M => k • Ψ r M) u M = k • Gauss.timeD1 Ψ u M := by
  unfold Gauss.timeD1
  exact deriv_fun_const_smul_field k (fun r => Ψ r M)

private theorem coordD1_const_smul (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (k : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    Gauss.coordD1 d N (fun M => k • F M) M q =
      k • Gauss.coordD1 d N F M q := by
  change (fderiv ℝ (k • F) M) (Gauss.Bmat d N q.1 q.2.1 q.2.2) = _
  rw [congrFun (fderiv_const_smul_field (f := F) k) M]
  rfl

private theorem coordD2_const_smul (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (k : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    Gauss.coordD2 d N (fun M => k • F M) M q =
      k • Gauss.coordD2 d N F M q := by
  change ((fderiv ℝ (fderiv ℝ (k • F)) M)
    (Gauss.Bmat d N q.1 q.2.1 q.2.2)) (Gauss.Bmat d N q.1 q.2.1 q.2.2) = _
  rw [fderiv_const_smul_field (f := F) k,
    congrFun (fderiv_const_smul_field (f := fderiv ℝ F) k) M]
  rfl

private theorem genPt_const_smul (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (k : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    APrimeDuhamelModel.genPt d N (fun M => k • F M) M =
      k * APrimeDuhamelModel.genPt d N F M := by
  unfold APrimeDuhamelModel.genPt
  simp_rw [coordD2_const_smul]
  simp only [Complex.smul_re, Finset.mul_sum]
  congr 1
  funext q
  ring

private theorem quadVar_const_smul (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (k : ℝ) (hk : 0 ≤ k)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Gauss.quadVar d N (fun M => k • F M) M =
      k ^ 2 * Gauss.quadVar d N F M := by
  unfold Gauss.quadVar
  simp_rw [coordD1_const_smul]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

private theorem momentAt_eq_const_smul (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v) :
    APrimeDriftTimeFamily.momentAt d E D N p σ a s v =
      fun r M => ((APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ ^ (2 * p)) •
        Gauss.momentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) (v : ℂ)
          (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a p r M := by
  funext r M
  unfold APrimeDriftTimeFamily.momentAt APrimeDriftTimeFamily.coordAt Gauss.momentObsT
  rw [Gauss.momentFun_eq, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc]
  simp only [div_eq_mul_inv, mul_pow, Complex.ofReal_mul, Complex.real_smul]
  ring

private theorem coordAt_eq_const_smul (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ) :
    APrimeDriftTimeFamily.coordAt d E D N σ a s v r =
      fun M => (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ •
        Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) (v : ℂ)
          (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r M := by
  funext M
  simp only [APrimeDriftTimeFamily.coordAt, Complex.real_smul, div_eq_mul_inv,
    Complex.ofReal_inv]
  ring

private theorem qvAt_eq_const_smul (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v)
    (r : ℝ) (ω : Gauss.Ω d) :
    APrimeDriftTimeFamily.qvAt d E D N σ a s v r ω =
      (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ ^ 2 *
        Gauss.quadVar d N
          (Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) (v : ℂ)
            (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r)
          (Gauss.Hflow d N r ω) := by
  unfold APrimeDriftTimeFamily.qvAt
  rw [coordAt_eq_const_smul]
  exact quadVar_const_smul d N _ _ (inv_nonneg.mpr hc.le) _


/-- The normalized `(G)` generator comparison for the actual Gaussian flow.
The fixed endpoint denominator is constant in running time and matrix. -/
theorem normalizedGeneratorBridge (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v r : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsr : s ≤ r) (hrv : r ≤ v)
    (hv1 : v < 1) (hp : 1 ≤ p) :
    APrimeDriftTimeFamily.NormalizedGeneratorBridge d E D N p σ a s v r := by
  intro ω
  have hsv : s ≤ v := hsr.trans hrv
  have hr0 : 0 ≤ r := hs0.trans hsr
  have hr1 : r < 1 := hrv.trans_lt hv1
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d hE hsv hv1 N a
  let k : ℝ := (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹
  have hk : 0 ≤ k := inv_nonneg.mpr hc.le
  let rawF : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) (v : ℂ)
      (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r
  let rawΨ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    Gauss.momentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) (v : ℂ)
      (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a p
  let M := Gauss.Hflow d N r ω
  let Y : ℝ := ‖Uker (d.L N) (xiOf (mSigma E) σ) (r : ℂ) (v : ℂ)
    (SumZeroDyn.lkT (Gauss.sample d) E N r ω σ) a‖
  let G : ℝ := ‖Uker (d.L N) (xiOf (mSigma E) σ) (r : ℂ) (v : ℂ)
    (DriftDef.driftF (Gauss.band d) E N r M σ) a‖
  let Q : ℝ := Gauss.quadVar d N rawF M
  have hraw := Gauss.timeD1_add_genMomentPt_le_driftF_flow
    (Gauss.band d) (Gauss.sample d) E N hE hr0 hr1 hv0 hv1 σ a ω hp
  have hraw' : (Gauss.timeD1 rawΨ r M).re +
      Gauss.genMomentPt d N rawF p M ≤
      2 * (p : ℝ) * (Y ^ (2 * p - 1) * G) +
        (p : ℝ) * (2 * (p : ℝ) - 1) * (Y ^ (2 * p - 2) * Q) := by
    change (Gauss.timeD1 rawΨ r M).re + Gauss.genMomentPt d N rawF p M ≤
      2 * (p : ℝ) * Y ^ (2 * p - 1) * G +
        (p : ℝ) * (2 * (p : ℝ) - 1) * Y ^ (2 * p - 2) * Q at hraw
    convert hraw using 1 <;> ring
  have hΨ := momentAt_eq_const_smul d E D N p σ a hc
  have htime :
      (Gauss.timeD1 (APrimeDriftTimeFamily.momentAt d E D N p σ a s v) r M).re =
        k ^ (2 * p) * (Gauss.timeD1 rawΨ r M).re := by
    rw [hΨ]
    change (Gauss.timeD1 (fun r M => k ^ (2 * p) • rawΨ r M) r M).re = _
    rw [timeD1_const_smul]
    simp only [Complex.smul_re, smul_eq_mul]
  have hgen :
      APrimeDuhamelModel.genPt d N
          (APrimeDriftTimeFamily.momentAt d E D N p σ a s v r) M =
        k ^ (2 * p) * Gauss.genMomentPt d N rawF p M := by
    rw [hΨ]
    change APrimeDuhamelModel.genPt d N
      (fun M => k ^ (2 * p) • rawΨ r M) M = _
    rw [genPt_const_smul]
    congr 1
  have hY : |APrimeDuhamelModel.flowY d N
      (APrimeDriftTimeFamily.coordAt d E D N σ a s v) r ω| = k * Y := by
    rw [APrimeDriftTimeFamily.flowY_coordAt d E D N σ a hE hsv hv1]
    have hY0 : 0 ≤ Y := norm_nonneg _
    rw [abs_of_nonneg (div_nonneg hY0 hc.le)]
    dsimp [k, Y]
    ring
  have hG : |APrimeDriftTimeFamily.driftAt d E D N σ a s v r ω| = k * G := by
    have hG0 : 0 ≤ G := norm_nonneg _
    have hdrift : APrimeDriftTimeFamily.driftAt d E D N σ a s v r ω =
        G / APrimeDriftTimeFamily.driftScale d E D N a s v := rfl
    rw [hdrift, abs_of_nonneg (div_nonneg hG0 hc.le)]
    dsimp [k]
    ring
  have hQ : APrimeDriftTimeFamily.qvAt d E D N σ a s v r ω = k ^ 2 * Q := by
    exact qvAt_eq_const_smul d E D N σ a hc r ω
  have hpow1 : (k * Y) ^ (2 * p - 1) * (k * G) =
      k ^ (2 * p) * (Y ^ (2 * p - 1) * G) := by
    calc
      _ = (k ^ (2 * p - 1) * k) * (Y ^ (2 * p - 1) * G) := by
        rw [mul_pow]
        ring
      _ = _ := by
        rw [← pow_succ, show 2 * p - 1 + 1 = 2 * p by omega]
  have hpow2 : (k * Y) ^ (2 * p - 2) * (k ^ 2 * Q) =
      k ^ (2 * p) * (Y ^ (2 * p - 2) * Q) := by
    calc
      _ = (k ^ (2 * p - 2) * k ^ 2) * (Y ^ (2 * p - 2) * Q) := by
        rw [mul_pow]
        ring
      _ = _ := by
        rw [← pow_add, show 2 * p - 2 + 2 = 2 * p by omega]
  have hscaled := mul_le_mul_of_nonneg_left hraw' (pow_nonneg hk (2 * p))
  change (Gauss.timeD1 (APrimeDriftTimeFamily.momentAt d E D N p σ a s v) r M).re +
    APrimeDuhamelModel.genPt d N
      (APrimeDriftTimeFamily.momentAt d E D N p σ a s v r) M ≤ _
  rw [htime, hgen]
  rw [hY, hG, hQ, hpow1, hpow2]
  convert hscaled using 1 <;> ring

/-- The comparison holds on a strictly positive first cell with positive
endpoint normalization, for every Gaussian sample. -/
theorem first_cell_normalizedGeneratorBridge (d : Gauss.Dims) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    0 < APrimeDriftTimeFamily.driftScale d 0 0 N a 0 (1 / 2) ∧
      (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 / 2 ∧
      APrimeDriftTimeFamily.NormalizedGeneratorBridge
        d 0 0 N 1 σ a 0 (1 / 2) (1 / 4) := by
  refine ⟨APrimeDriftTimeFamily.driftScale_pos d (D := 0)
    (by norm_num) (by norm_num) (by norm_num) N a,
    by norm_num, by norm_num, ?_⟩
  exact normalizedGeneratorBridge d 0 0 N 1 σ a
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms RBM.APrimeNormalizedGenerator.normalizedGeneratorBridge
#print axioms RBM.APrimeNormalizedGenerator.first_cell_normalizedGeneratorBridge

end RBM.APrimeNormalizedGenerator

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVEndpoint
import RBM1D.Gauss.APrimeDriftTimeFamily

/-!
# T300: the fixed-scale evolved QV bridge

The normalization is fixed at the right endpoint and is independent of the
matrix variable and running time. The event-level endpoint hypotheses are
kept pointwise; this file makes no claim about their joint probability.
-/

namespace RBM.APrimeQVBridge

open RBM.Gauss RBM.APrimeDriftTimeFamily
open scoped Matrix.Norms.L2Operator

private theorem coordD1_const_smul (d : Gauss.Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (k : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    Gauss.coordD1 d N (fun M => k • F M) M q =
      k • Gauss.coordD1 d N F M q := by
  change (fderiv ℝ (k • F) M) (Gauss.Bmat d N q.1 q.2.1 q.2.2) = _
  rw [congrFun (fderiv_const_smul_field (f := F) k) M]
  rfl

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

private theorem coordAt_eq_const_smul (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v u : ℝ) :
    coordAt d E D N Step2.sigPM a s v u =
      fun M => (driftScale d E D N a s v)⁻¹ •
        Gauss.ukerObsT d N E (List.ofFn Step2.sigPM)
          (xiOf (mSigma E) Step2.sigPM) (v : ℂ)
          (fun r b => (Gauss.band d).Kval E N r (LoopData.idx (Step2.sigPM, b))) a u M := by
  funext M
  simp only [coordAt, Complex.real_smul, div_eq_mul_inv, Complex.ofReal_inv]
  ring

/-- Exact quadratic variation of T292's actual normalized coordinate. -/
theorem qvAt_eq_raw (d : Gauss.Dims) {E D s v u : ℝ}
    (hE : |E| < 2) (hsv : s ≤ v) (hv1 : v < 1)
    (N : ℕ) (a : LoopArg (d.L N) 2) (ω : Gauss.Ω d) :
    qvAt d E D N Step2.sigPM a s v u ω =
      (driftScale d E D N a s v)⁻¹ ^ 2 *
        Gauss.quadVar d N
          (Gauss.ukerObsT d N E (List.ofFn Step2.sigPM)
            (xiOf (mSigma E) Step2.sigPM) (v : ℂ)
            (fun r b => (Gauss.band d).Kval E N r (LoopData.idx (Step2.sigPM, b))) a u)
          (Gauss.Hflow d N u ω) := by
  have hc := driftScale_pos d (D := D) hE hsv hv1 N a
  unfold qvAt
  rw [coordAt_eq_const_smul]
  exact quadVar_const_smul d N _ _ (inv_nonneg.mpr hc.le) _

/-- T277 identifies the unnormalized rate with the propagated loop
observable; the primitive K drops out of its matrix derivative. -/
theorem qvAt_eq_evolved_loopObs (d : Gauss.Dims) {E D s v u : ℝ}
    (hE : |E| < 2) (hsv : s ≤ v) (hv1 : v < 1)
    (N : ℕ) (a : LoopArg (d.L N) 2) (ω : Gauss.Ω d) :
    qvAt d E D N Step2.sigPM a s v u ω =
      (driftScale d E D N a s v)⁻¹ ^ 2 *
        Gauss.quadVar d N
          (fun M' => Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
            (u : ℂ) (v : ℂ)
            (fun b => Gauss.loopObs d N (zt E u)
              (Gauss.toIdx Step2.sigPM b) M') a)
          (Gauss.Hflow d N u ω) := by
  rw [qvAt_eq_raw d hE hsv hv1 N a ω]
  congr 1
  have h := APrimeQVEndpoint.quadVar_ukerObsT_eq_evolved_loopObs
    (Gauss.band d) E N u v a (Gauss.Hflow d N u ω)
  cases d
  simpa [Gauss.band, Band.toDims] using h

/-- Square-root form of the same fixed-scale equality. -/
theorem sqrt_qvAt_eq_evolved_loopObs (d : Gauss.Dims) {E D s v u : ℝ}
    (hE : |E| < 2) (hsv : s ≤ v) (hv1 : v < 1)
    (N : ℕ) (a : LoopArg (d.L N) 2) (ω : Gauss.Ω d) :
    √(qvAt d E D N Step2.sigPM a s v u ω) =
      (driftScale d E D N a s v)⁻¹ *
        √(Gauss.quadVar d N
          (fun M' => Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
            (u : ℂ) (v : ℂ)
            (fun b => Gauss.loopObs d N (zt E u)
              (Gauss.toIdx Step2.sigPM b) M') a)
          (Gauss.Hflow d N u ω)) := by
  rw [qvAt_eq_evolved_loopObs d hE hsv hv1 N a ω]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr (driftScale_pos d (D := D) hE hsv hv1 N a))]

/-- T277's pointwise endpoint bound for T292's actual normalized QV. The
only new factor is the reciprocal fixed endpoint normalization. -/
theorem sqrt_qvAt_le_endpoint (d : Gauss.Dims) {E D s u v : ℝ}
    (hE : |E| < 2) (hsu : s ≤ u) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (N : ℕ) (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (ω : Gauss.Ω d) (a : LoopArg (d.L N) 2)
    {ℓs J Smax ρ : ℝ} (hℓs : 0 < ℓs) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hAu : 1 ≤ (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u)
    (hlog : (4 * D) ^ 2 ≤ Real.log (d.W N : ℝ))
    (hρ : 0 ≤ ρ)
    {Gm Gsq : ZMod (d.L N) → ZMod (d.L N) → ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (b : Bool) (x y : ZMod (d.L N))
        (p q : ZMod (d.L N) × Fin (d.W N)),
      p.1 = x → q.1 = y →
        ‖Gsig ((Gauss.sample d).H N u ω) (zt E u) b p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (d.L N), SB (d.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (b : Bool) (x y y' : ZMod (d.L N)),
      (gloop (d.L N) (d.W N) ((Gauss.sample d).H N u ω) (zt E u)
        ⟨[b, !b, b, !b], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ c b, EEDef.eeL6 (Gauss.sample d) E N u ω Step2.sigPM
        (Fin.append c c) b ≤
      ((Gauss.band d).ell N u / ℓs) ^ 5 *
        ((((d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u) ^ 2)⁻¹) ^ 2 *
        ((d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u)⁻¹)
    (h564 : ∀ c b, Lemma57.ellStarStar (d.W N : ℝ)
        ((Gauss.band d).ell N u) < (zdist (d.L N) (c 0 - b) : ℝ) →
      EEDef.eeL6 (Gauss.sample d) E N u ω Step2.sigPM
        (Fin.append c c) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (d.L N),
      ellStar (d.W N : ℝ) ((Gauss.band d).ell N u) / 2 ≤
        (zdist (d.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * Step2.tT (Gauss.band d) E N D u
        (zdist (d.L N) (x - y))) :
    √(qvAt d E D N Step2.sigPM a s v u ω) ≤
      (driftScale d E D N a s v)⁻¹ *
        (√(APrimeQVEndpoint.diagNearRate (Gauss.band d) N
              ((Gauss.band d).ell N u) ℓs (etaT E u)) *
            ((((1 - u) / (1 - v)) ^ 2 *
                Step2.xiK (d.L N) (d.W N : ℝ) (mE E).im *
                Step2.tT (Gauss.band d) E N D v (zdist (d.L N) (a 0 - a 1))) *
              (if (zdist (d.L N) (a 0 - a 1) : ℝ) ≤
                  6 * ellStar (d.W N : ℝ) ((Gauss.band d).ell N v) then 1 else 0)
            + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
                (d.W N : ℝ) ^ (-D) *
                Step2.tT (Gauss.band d) E N D v (zdist (d.L N) (a 0 - a 1)))
          + √(APrimeQVEndpoint.diagFarRate (Gauss.band d) N
              ((Gauss.band d).ell N u) (etaT E u) D J Smax) *
            (((1 - u) / (1 - v)) ^ 2 *
              Step2.xiK (d.L N) (d.W N : ℝ) (mE E).im *
              Step2.tT (Gauss.band d) E N D v (zdist (d.L N) (a 0 - a 1)))
          + √(APrimeQVEndpoint.diagResidual (Gauss.band d) N ρ) *
              ((1 - u) / (1 - v)) ^ 2) := by
  have hc := driftScale_pos d (D := D) hE (hsu.trans huv) hv1 N a
  rw [sqrt_qvAt_eq_evolved_loopObs d hE (hsu.trans huv) hv1 N a ω]
  gcongr
  have h := APrimeQVEndpoint.sqrt_evolvedQV_le_endpoint
    (Gauss.sample d) hE hu0 huv hv1 hW ω a hℓs hJ hD hAu hlog
    hρ hGm0 hGm hGsq0 hGsq2 hrow hSmax h273 h564 h42sq
  cases d
  convert h using 1 <;> rfl

/-- The fixed normalization is nonzero on the positive-length first cell,
including its left endpoint `u=s=0`. -/
theorem first_cell_driftScale_pos (d : Gauss.Dims) (N : ℕ)
    (a : LoopArg (d.L N) 2) :
    0 < driftScale d 0 0 N a 0 (1 / 2) ∧
      (0 : ℝ) < 1 / 2 := by
  exact ⟨driftScale_pos d (D := 0) (by norm_num) (by norm_num)
    (by norm_num) N a, by norm_num⟩

#print axioms qvAt_eq_raw
#print axioms qvAt_eq_evolved_loopObs
#print axioms sqrt_qvAt_eq_evolved_loopObs
#print axioms sqrt_qvAt_le_endpoint
#print axioms first_cell_driftScale_pos

end RBM.APrimeQVBridge

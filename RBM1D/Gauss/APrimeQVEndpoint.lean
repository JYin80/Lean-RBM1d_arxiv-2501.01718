/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimePrior
import RBM1D.Gauss.APrimeDuhamel
import RBM1D.Gauss.MomentDuhamelHypGauss
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Gauss.TestFunQGeneral

/-!
# T277: the doubled evolution kernel in the endpoint quadratic variation

The first bridge below applies Lemma 7.1 to the actual `E ⊗ E` tensor, with the
correct conjugated second copy of the charge.  Its input is an explicit finite
sum of the tensor entries, rather than an assumed bound on the evolved tensor.
The sharp spatial estimate (5.42) requires a separate weighted convolution
bound for that sum.
-/

namespace RBM
namespace APrimeQVEndpoint

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- An unconditional endpoint bound for the doubled `E ⊗ E` tensor.  It is
pointwise at one matrix and uses the exact finite tensor, so its hypotheses
contain no random size estimate. -/
theorem norm_Uker_eeFun_le_sum {E : ℝ} {N : ℕ} {u v : ℝ}
    (σ : Fin (0 + 2) → Bool) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    (a : LoopArg (B.L N) ((0 + 2) + (0 + 2))) :
    ‖Uker (B.L N) (EEUker.xi2bar E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (MomentDuhamel.eeFun B E N u M σ) a‖
      ≤ Gauss.ukerRow (EEUker.xi2bar E σ) (v : ℂ) a u *
        ∑ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
          ‖MomentDuhamel.eeFun B E N u M σ b‖ := by
  classical
  apply Gauss.norm_Uker_apply_le_ukerRow
  intro b
  exact Finset.single_le_sum (fun c _ => norm_nonneg _) (Finset.mem_univ b)

/-- The endpoint kernel row has the expected fourth power of the time ratio.
This is the expansion factor in (5.42), before spatial decay is used. -/
theorem norm_Uker_eeFun_le_ratio {E : ℝ} (hE : |E| < 2) {N : ℕ} {u v : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (σ : Fin (0 + 2) → Bool) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    (a : LoopArg (B.L N) ((0 + 2) + (0 + 2))) :
    ‖Uker (B.L N) (EEUker.xi2bar E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (MomentDuhamel.eeFun B E N u M σ) a‖
      ≤ ((1 - u) / (1 - v)) ^ 4 *
        ∑ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
          ‖MomentDuhamel.eeFun B E N u M σ b‖ := by
  classical
  have hv0 : 0 ≤ v := hu0.trans huv
  have hden : 0 < 1 - v := by linarith
  have hξ : ∀ i : Fin ((0 + 2) + (0 + 2)), ‖EEUker.xi2bar E σ i‖ ≤ 1 := by
    intro i
    rw [← EEUker.xi2_eq_xi2bar]
    exact SumZeroDyn.norm_xi2_le hE σ i
  have ht : ∀ i : Fin ((0 + 2) + (0 + 2)),
      ‖((v : ℝ) : ℂ) * EEUker.xi2bar E σ i‖ < 1 := by
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0]
    have h := hξ i
    nlinarith [norm_nonneg (EEUker.xi2bar E σ i)]
  have hC : ∀ i : Fin ((0 + 2) + (0 + 2)),
      1 + ‖(((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * EEUker.xi2bar E σ i‖ *
          (1 - ‖((v : ℝ) : ℂ) * EEUker.xi2bar E σ i‖)⁻¹
        ≤ (1 - u) / (1 - v) := by
    intro i
    have hx := hξ i
    have hnormv : ‖((v : ℝ) : ℂ) * EEUker.xi2bar E σ i‖
        = v * ‖EEUker.xi2bar E σ i‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0]
    have hnormd : ‖(((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * EEUker.xi2bar E σ i‖
        = (v - u) * ‖EEUker.xi2bar E σ i‖ := by
      rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    rw [hnormv, hnormd]
    have hdenx : 0 < 1 - v * ‖EEUker.xi2bar E σ i‖ := by
      nlinarith [norm_nonneg (EEUker.xi2bar E σ i)]
    rw [← div_eq_mul_inv]
    have heq : 1 + (v - u) * ‖EEUker.xi2bar E σ i‖ /
        (1 - v * ‖EEUker.xi2bar E σ i‖)
        = (1 - u * ‖EEUker.xi2bar E σ i‖) /
          (1 - v * ‖EEUker.xi2bar E σ i‖) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ hdenx hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hx)]
  have hsum : (0 : ℝ) ≤
      ∑ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
        ‖MomentDuhamel.eeFun B E N u M σ b‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : ∀ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
      ‖MomentDuhamel.eeFun B E N u M σ b‖ ≤
        ∑ c : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
          ‖MomentDuhamel.eeFun B E N u M σ c‖ := by
    intro b
    exact Finset.single_le_sum (fun c _ => norm_nonneg _) (Finset.mem_univ b)
  simpa using norm_Uker_apply_le (B.L N) (B.three_le_L N) ht hsum hC hA a

/-- The actual endpoint quadratic variation is bounded by a finite sum of the
unevolved `E ⊗ E` tensor.  This is the `U`-dependent counterpart of T262's
`U = id` bridge; the sharp bound (5.42) has to estimate this weighted sum. -/
theorem quadVarPairs_Uker_le_sum (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (ω : Ω) (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2)) :
    Gauss.quadVarPairs B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ)
          ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b) M') a)
        (X.H N u ω)
      ≤ 2 * (Gauss.ukerRow (EEUker.xi2bar E σ) (v : ℂ) (Fin.append a a) u *
        ∑ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
          ‖MomentDuhamel.eeFun B E N u (X.H N u ω) σ b‖) := by
  have hbridge := EEUker.quadVarPairs_Uker_le_norm_eeFun' hE hu1 hv0 hv1 σ
    (X.hermitian N u ω) a
  have hsum := norm_Uker_eeFun_le_sum (B := B) (E := E) (N := N) (u := u) (v := v)
    σ (X.H N u ω) (Fin.append a a)
  simpa using hbridge.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- (5.42) through the kernel row expansion: the remaining finite sum is the
precise spatial convolution that has to be estimated to obtain the near/far
indicator and the `T_{t,D}²` factor. -/
theorem quadVarPairs_Uker_le_ratio_sum (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (ω : Ω) (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2)) :
    Gauss.quadVarPairs B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ)
          ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b) M') a)
        (X.H N u ω)
      ≤ 2 * (((1 - u) / (1 - v)) ^ 4 *
        ∑ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
          ‖MomentDuhamel.eeFun B E N u (X.H N u ω) σ b‖) := by
  have hbridge := EEUker.quadVarPairs_Uker_le_norm_eeFun' hE (huv.trans_lt hv1)
    (hu0.trans huv) hv1 σ (X.hermitian N u ω) a
  have hsum := norm_Uker_eeFun_le_ratio (B := B) hE hu0 huv hv1 σ
    (X.H N u ω) (Fin.append a a)
  simpa using hbridge.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- A genuinely positive-duration instance of the endpoint propagation bound:
`u = 0`, `v = 1/2`, and the kernel expansion is exactly `16`. -/
theorem ratio_witness (X : Sample B) (N : ℕ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2)) :
    Gauss.quadVarPairs B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma 0) σ)
          ((0 : ℝ) : ℂ) (((1 / 2 : ℝ)) : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt 0 0) (Gauss.toIdx σ b) M') a)
        (X.H N 0 ω)
      ≤ 32 * ∑ b : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
          ‖MomentDuhamel.eeFun B 0 N 0 (X.H N 0 ω) σ b‖ := by
  have h := quadVarPairs_Uker_le_ratio_sum X (E := 0) (u := 0) (v := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ω σ a
  norm_num at h ⊢
  nlinarith only [h]

/-- Minkowski for the quadratic variation of a finite, deterministic kernel
applied to matrix observables.  Only the diagonal rates of the input
observables occur on the right. -/
theorem sqrt_quadVar_Uker_le (d : Gauss.Dims) (N : ℕ) {n : ℕ}
    (ξ : Fin n → ℂ) (u v : ℝ) (a : LoopArg (d.L N) n)
    (F : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (hF : ∀ b, Differentiable ℝ (F b))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N
        (fun M' => Uker (d.L N) ξ (u : ℂ) (v : ℂ) (fun b => F b M') a) M)
      ≤ ∑ b : LoopArg (d.L N) n,
          ‖∏ i : Fin n, edgeKer (d.L N) (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)‖ *
            √(Gauss.quadVar d N (F b) M) := by
  classical
  let K : LoopArg (d.L N) n → ℂ :=
    fun b => ∏ i : Fin n, edgeKer (d.L N) (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)
  let g : LoopArg (d.L N) n → d.Idx N × d.Idx N × Bool → ℝ :=
    fun b q => ‖K b‖ * ‖Gauss.coordD1 d N (F b) M q‖
  have hfd (q : d.Idx N × d.Idx N × Bool) :
      Gauss.coordD1 d N
          (fun M' => Uker (d.L N) ξ (u : ℂ) (v : ℂ) (fun b => F b M') a) M q
        = ∑ b : LoopArg (d.L N) n, K b * Gauss.coordD1 d N (F b) M q := by
    change (fderiv ℝ (fun M' => ∑ b : LoopArg (d.L N) n, K b * F b M') M)
      (Gauss.Bmat d N q.1 q.2.1 q.2.2) = _
    exact Gauss.fderiv_finsetSum_const_mul_apply (Finset.univ : Finset (LoopArg (d.L N) n))
      K F (fun b _ => hF b) M (Gauss.Bmat d N q.1 q.2.1 q.2.2)
  have hpt (q : d.Idx N × d.Idx N × Bool) :
      ‖Gauss.coordD1 d N
          (fun M' => Uker (d.L N) ξ (u : ℂ) (v : ℂ) (fun b => F b M') a) M q‖
        ≤ ∑ b : LoopArg (d.L N) n, g b q := by
    rw [hfd q]
    simpa only [g, norm_mul] using
      (norm_sum_le (Finset.univ : Finset (LoopArg (d.L N) n))
        (fun b => K b * Gauss.coordD1 d N (F b) M q))
  have hquad : Gauss.quadVar d N
      (fun M' => Uker (d.L N) ξ (u : ℂ) (v : ℂ) (fun b => F b M') a) M
      ≤ ∑ q ∈ Gauss.usedCoord d N,
          (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (∑ b : LoopArg (d.L N) n, g b q) ^ 2 := by
    rw [Gauss.quadVar]
    refine Finset.sum_le_sum fun q _ => ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hpt q) 2) (Gauss.gvar d (Gauss.crd d N q)).2
  have hmink := Gauss.sqrt_wsum_sum_le (Gauss.usedCoord d N)
    (Finset.univ : Finset (LoopArg (d.L N) n))
    (fun q => (Gauss.gvar d (Gauss.crd d N q) : ℝ))
    (fun q _ => (Gauss.gvar d (Gauss.crd d N q)).2) g
  have hterm (b : LoopArg (d.L N) n) :
      √(∑ q ∈ Gauss.usedCoord d N,
          (Gauss.gvar d (Gauss.crd d N q) : ℝ) * g b q ^ 2)
        = ‖K b‖ * √(Gauss.quadVar d N (F b) M) := by
    have hrw : (∑ q ∈ Gauss.usedCoord d N,
          (Gauss.gvar d (Gauss.crd d N q) : ℝ) * g b q ^ 2)
        = ‖K b‖ ^ 2 * Gauss.quadVar d N (F b) M := by
      rw [Gauss.quadVar, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [g]
      ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  calc
    √(Gauss.quadVar d N
        (fun M' => Uker (d.L N) ξ (u : ℂ) (v : ℂ) (fun b => F b M') a) M)
        ≤ √(∑ q ∈ Gauss.usedCoord d N,
            (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
              (∑ b : LoopArg (d.L N) n, g b q) ^ 2) := Real.sqrt_le_sqrt hquad
    _ ≤ ∑ b : LoopArg (d.L N) n,
          √(∑ q ∈ Gauss.usedCoord d N,
            (Gauss.gvar d (Gauss.crd d N q) : ℝ) * g b q ^ 2) := hmink
    _ = ∑ b : LoopArg (d.L N) n,
          ‖K b‖ * √(Gauss.quadVar d N (F b) M) :=
        Finset.sum_congr rfl fun b _ => hterm b
    _ = _ := rfl

/-- The evolved loop observable has a quadratic-variation bound involving only
the diagonal quadratic variations of the unevolved loops. -/
theorem sqrt_quadVar_Uker_loopObs_le (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2)) :
    √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b) M') a)
        (X.H N u ω))
      ≤ ∑ b : LoopArg (B.L N) (0 + 2),
          ‖∏ i : Fin (0 + 2), edgeKer (B.L N) (xiOf (mSigma E) σ i)
              (u : ℂ) (v : ℂ) (a i) (b i)‖ *
            √(Gauss.quadVar B.toDims N
              (fun M' => MomentDuhamel.lkFun B E N u M' σ b) (X.H N u ω)) := by
  classical
  have hz : (zt E u).im ≠ 0 := Gauss.zt_im_ne_zero_of_lt_one hE hu1
  have hd (b : LoopArg (B.L N) (0 + 2)) :
      Differentiable ℝ (Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b)) :=
    fun M' => Gauss.differentiableAt_loopObs hz (Gauss.toIdx_wf σ b) M'
  have hmink := sqrt_quadVar_Uker_le B.toDims N
    (xiOf (mSigma E) σ) u v a
    (fun b M' => Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b) M') hd
    (X.H N u ω)
  have hq (b : LoopArg (B.L N) (0 + 2)) :
      Gauss.quadVar B.toDims N
          (Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b)) (X.H N u ω)
        = Gauss.quadVar B.toDims N
          (fun M' => MomentDuhamel.lkFun B E N u M' σ b) (X.H N u ω) :=
    (EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs hz σ
      (X.hermitian N u ω) b).symm
  have hsum :
      (∑ b : LoopArg (B.L N) (0 + 2),
          ‖∏ i : Fin (0 + 2), edgeKer (B.L N) (xiOf (mSigma E) σ i)
              (u : ℂ) (v : ℂ) (a i) (b i)‖ *
            √(Gauss.quadVar B.toDims N
              (Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b)) (X.H N u ω)))
        = ∑ b : LoopArg (B.L N) (0 + 2),
          ‖∏ i : Fin (0 + 2), edgeKer (B.L N) (xiOf (mSigma E) σ i)
              (u : ℂ) (v : ℂ) (a i) (b i)‖ *
            √(Gauss.quadVar B.toDims N
              (fun M' => MomentDuhamel.lkFun B E N u M' σ b) (X.H N u ω)) := by
    exact Finset.sum_congr rfl fun b _ => by rw [hq b]
  exact hmink.trans_eq hsum

/-- The exact diagonal right-hand side of T262, before propagation by `U`. -/
noncomputable def diagShape (B : Band Ω) (N : ℕ) (ℓu ℓs ηu D J Smax ρ : ℝ)
    (b : LoopArg (B.L N) (0 + 2)) : ℝ :=
  2 * (ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
            then 1 else 0)
        + Lemma57.cFar2 (B.W N : ℝ) ℓu
          * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2
      + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
        + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2))

/-- T262 is applied at every input loop *after* Minkowski, so its use is
strictly diagonal. -/
theorem sqrt_quadVar_Uker_le_diagShape (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ c b, EEDef.eeL6 X E N u ω σ (Fin.append c c) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2
        * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ c b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (c 0 - b) : ℝ) →
        EEDef.eeL6 X E N u ω σ (Fin.append c c) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u) (Gauss.toIdx σ b) M') a)
        (X.H N u ω))
      ≤ ∑ b : LoopArg (B.L N) (0 + 2),
          ‖∏ i : Fin (0 + 2), edgeKer (B.L N) (xiOf (mSigma E) σ i)
              (u : ℂ) (v : ℂ) (a i) (b i)‖ *
            √(diagShape B N ℓu ℓs ηu D J Smax ρ b) := by
  have hmink := sqrt_quadVar_Uker_loopObs_le X hE (u := u) (v := v) hu1 ω σ a
  refine hmink.trans (Finset.sum_le_sum fun b _ => ?_)
  have hdiag : Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' σ b) (X.H N u ω)
      ≤ diagShape B N ℓu ℓs ηu D J Smax ρ b := by
    exact EarlyQVRate.quadVar_lkFun_le_ee_sym X hE hu0 hu1 ω σ b
      hℓu hℓs hηu hJ hρ hGm0 hGm hGsq0 hGsq2 hrow hSmax
      (h273 b) (h564 b) h42sq
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdiag) (norm_nonneg _)

private noncomputable def kernelPhase (z : ℂ) : ℂ :=
  if z = 0 then 0 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

private theorem norm_kernelPhase_le_one (z : ℂ) : ‖kernelPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [kernelPhase, hz]
  · simp only [kernelPhase, if_neg hz, norm_div, RCLike.norm_conj,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

private theorem mul_kernelPhase (z : ℂ) : z * kernelPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [kernelPhase, hz]
  · simp only [kernelPhase, if_neg hz]
    rw [← mul_div_assoc, Gauss.mul_conj_eq, Complex.ofReal_pow]
    have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    field_simp

/-- Choosing the phase of every input separately realizes the absolute kernel
convolution as the norm of one `Uker` output. -/
private theorem weightedKernelSum_eq_norm_Uker (L n : ℕ) [NeZero L]
    (ξ : Fin n → ℂ) (u v : ℝ) (a : LoopArg L n)
    (w : LoopArg L n → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : LoopArg L n,
        ‖∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)‖ * w b)
      = ‖Uker L ξ (u : ℂ) (v : ℂ)
          (fun b => kernelPhase
            (∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)) * (w b : ℂ)) a‖ := by
  classical
  set K : LoopArg L n → ℂ :=
    fun b => ∏ i : Fin n, edgeKer L (ξ i) (u : ℂ) (v : ℂ) (a i) (b i)
  have hsum : (0 : ℝ) ≤ ∑ b : LoopArg L n, ‖K b‖ * w b :=
    Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hw b)
  have hval : Uker L ξ (u : ℂ) (v : ℂ)
      (fun b => kernelPhase (K b) * (w b : ℂ)) a
        = ((∑ b : LoopArg L n, ‖K b‖ * w b) : ℂ) := by
    rw [Uker_apply]
    exact Finset.sum_congr rfl fun b _ => by
      change K b * (kernelPhase (K b) * (w b : ℂ)) = (‖K b‖ : ℂ) * (w b : ℂ)
      rw [← mul_assoc, mul_kernelPhase]
  change (∑ b : LoopArg L n, ‖K b‖ * w b) = _
  rw [hval]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg hsum]

/-- The absolute two-loop kernel convolved with the tail, obtained from the
existing (5.39) propagation estimate by a phase choice at each input loop. -/
theorem weightedKernel_tail_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u v : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) {W D : ℝ}
    (hW : Real.exp 1 ≤ W)
    (hAuv : W * ellHat L (v : ℂ) * ((1 - v) * m)
      ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    (a : LoopArg L 2) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ *
          tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (b 0 - b 1)))
      ≤ ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
        tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (a 0 - a 1)) := by
  classical
  let w : LoopArg L 2 → ℝ := fun b =>
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (b 0 - b 1))
  let K : LoopArg L 2 → ℂ :=
    fun b => ∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)
  let A : LoopArg L 2 → ℂ := fun b => kernelPhase (K b) * (w b : ℂ)
  have hW0 : 0 ≤ W := le_trans (Real.exp_nonneg 1) hW
  have hw (b : LoopArg L 2) : 0 ≤ w b := tailT_nonneg hW0 _
  have hA (b : LoopArg L 2) : ‖A b‖ ≤ w b := by
    rw [show A b = kernelPhase (K b) * (w b : ℂ) from rfl,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw b)]
    calc ‖kernelPhase (K b)‖ * w b ≤ 1 * w b :=
          mul_le_mul_of_nonneg_right (norm_kernelPhase_le_one _) (hw b)
      _ = w b := one_mul _
  have hprop := Step2.norm_Uker_le_of_tail hL hm0 hm1 hu0 huv
    (hu0.trans huv) hv1 hW (by norm_num : (0 : ℝ) ≤ 1) hAuv
    (A := A) (fun b => by simpa only [one_mul] using hA b) a
  have hsum := weightedKernelSum_eq_norm_Uker L 2 (fun _ => 1) u v a w hw
  change (∑ b : LoopArg L 2, ‖K b‖ * w b) ≤ _
  rw [hsum]
  simpa only [one_mul, mul_one] using hprop

/-- Absolute kernel mass carried from a diagonal band into a separated pair. -/
theorem weightedKernel_supp_far_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {ρ Δ : ℝ} (hΔ : 0 < Δ) (a : LoopArg L 2)
    (hd : ρ + 2 * Δ ≤ (zdist L (a 0 - a 1) : ℝ)) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ *
          (if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then 1 else 0))
      ≤ 128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
        Real.exp (-(Δ / ellHat L (v : ℂ) / 2)) := by
  classical
  let w : LoopArg L 2 → ℝ := fun b =>
    if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then 1 else 0
  let K : LoopArg L 2 → ℂ :=
    fun b => ∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)
  let A : LoopArg L 2 → ℂ := fun b => kernelPhase (K b) * (w b : ℂ)
  have hw (b : LoopArg L 2) : 0 ≤ w b := by simp only [w]; split_ifs <;> norm_num
  have hA (b : LoopArg L 2) : ‖A b‖ ≤ w b := by
    rw [show A b = kernelPhase (K b) * (w b : ℂ) from rfl,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw b)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (norm_kernelPhase_le_one (K b)) (hw b)
  have hprop := Step2MomentStep.norm_Uker_supp_far_le L hL hu0 huv hv1
    (by norm_num : (0 : ℝ) ≤ 1) hΔ (A := A)
    (fun b => by simpa only [one_mul] using hA b) a hd
  have hsum := weightedKernelSum_eq_norm_Uker L 2 (fun _ => 1) u v a w hw
  change (∑ b : LoopArg L 2, ‖K b‖ * w b) ≤ _
  rw [hsum]
  simpa only [one_mul, mul_one] using hprop

/-- A near-diagonal input band of radius `4ℓ*_u` reaches beyond `6ℓ*_v`
only through the exponentially decaying part of the two-loop kernel. -/
theorem weightedKernel_near_tail_far_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {m : ℝ} (_hm0 : 0 < m) (_hm1 : m ≤ 1)
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {W D : ℝ} (hW : Real.exp 1 ≤ W)
    (a : LoopArg L 2)
    (hd : 6 * ellStar W (ellHat L (v : ℂ))
      ≤ (zdist L (a 0 - a 1) : ℝ)) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ *
          (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
              (zdist L (b 0 - b 1)) *
            (if (zdist L (b 0 - b 1) : ℝ)
                ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0)))
      ≤ tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
          (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
            Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
              ellHat L (v : ℂ) / 2))) := by
  classical
  have hu1 : u < 1 := huv.trans_lt hv1
  have hv0 : 0 ≤ v := hu0.trans huv
  have hℓu : 0 < ellHat L (u : ℂ) := by
    have := one_le_ellHat_of_nonneg (L := L) (by omega : 1 ≤ L) hu0 hu1
    linarith
  have hℓv : 0 < ellHat L (v : ℂ) := by
    have := one_le_ellHat_of_nonneg (L := L) (by omega : 1 ≤ L) hv0 hv1
    linarith
  have hlog : 0 ≤ Real.log W :=
    Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hW)
  have hp : 0 ≤ Real.log W ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hlog _
  have hstar : ellStar W (ellHat L (u : ℂ))
      ≤ ellStar W (ellHat L (v : ℂ)) := by
    unfold ellStar
    exact mul_le_mul_of_nonneg_left (Step3.ellHat_mono (L := L) huv hv1) hp
  have hΔ : 0 < ellStar W (ellHat L (v : ℂ)) := by
    unfold ellStar
    have hlog1 : 1 ≤ Real.log W := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hW
    have : 0 < Real.log W ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hd' : 4 * ellStar W (ellHat L (u : ℂ)) +
      2 * ellStar W (ellHat L (v : ℂ))
        ≤ (zdist L (a 0 - a 1) : ℝ) := by linarith
  have hsup := weightedKernel_supp_far_le L hL hu0 huv hv1 hΔ a hd'
  have hW0 : 0 ≤ W := le_trans (Real.exp_nonneg 1) hW
  have hT0 : 0 ≤ tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 :=
    tailT_nonneg hW0 _
  let T : ℝ := tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0
  let K : LoopArg L 2 → ℝ := fun b =>
    ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖
  let χ : LoopArg L 2 → ℝ := fun b =>
    if (zdist L (b 0 - b 1) : ℝ)
      ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0
  have hpt (b : LoopArg L 2) :
      K b * (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
          (zdist L (b 0 - b 1)) * χ b) ≤ T * (K b * χ b) := by
    have htail : tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
        (zdist L (b 0 - b 1)) ≤ T :=
      tailT_antitone hℓu (Nat.cast_nonneg _)
    have hχ : 0 ≤ χ b := by simp only [χ]; split_ifs <;> norm_num
    nlinarith [mul_nonneg (norm_nonneg
      (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i))) hχ]
  calc
    (∑ b : LoopArg L 2, K b *
        (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
          (zdist L (b 0 - b 1)) * χ b))
      ≤ ∑ b : LoopArg L 2, T * (K b * χ b) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = T * ∑ b : LoopArg L 2, K b * χ b := by rw [Finset.mul_sum]
    _ ≤ T * (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
        Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
          ellHat L (v : ℂ) / 2))) :=
        mul_le_mul_of_nonneg_left hsup hT0

/-- Lemma 7.1's row expansion for the absolute two-loop kernel. -/
theorem weightedKernel_row_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {u v : ℝ} (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (a : LoopArg L 2) :
    (∑ b : LoopArg L 2,
      ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖)
        ≤ ((1 - u) / (1 - v)) ^ 2 := by
  let f : Fin 2 → ZMod L → ℝ :=
    fun i c => ‖edgeKer L 1 (u : ℂ) (v : ℂ) (a i) c‖
  have h0 : ∀ i : Fin 2, 0 ≤ ∑ c : ZMod L, f i c :=
    fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hle : ∀ i : Fin 2,
      ∑ c : ZMod L, f i c ≤ (1 - u) / (1 - v) :=
    fun i => Step2MomentStep.sum_norm_edgeKer_one_row_le L hL huv hv0 hv1 (a i)
  calc
    (∑ b : LoopArg L 2,
      ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖)
      = ∑ b : LoopArg L 2, ∏ i : Fin 2, f i (b i) := by
        exact Finset.sum_congr rfl fun b _ => by simp [f]
    _ = ∏ i : Fin 2, ∑ c : ZMod L, f i c := sum_prod_pi L f
    _ ≤ ∏ _i : Fin 2, (1 - u) / (1 - v) :=
      Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => hle i)
    _ = ((1 - u) / (1 - v)) ^ 2 := by simp [div_pow]

/-- The near coefficient after propagation: a tail bound inside `6ℓ*_v`,
and exponential leakage outside. -/
noncomputable def nearConvBd (L : ℕ) (m u v W D : ℝ) (a : LoopArg L 2) : ℝ :=
  if (zdist L (a 0 - a 1) : ℝ) ≤ 6 * ellStar W (ellHat L (v : ℂ)) then
    ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
      tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (a 0 - a 1))
  else
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
      (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
        Real.exp (-(ellStar W (ellHat L (v : ℂ)) / ellHat L (v : ℂ) / 2)))

/-- The propagated near term has the exact endpoint indicator plus an
explicit exponentially small leakage term. -/
theorem nearConvBd_le_indicator (L : ℕ) {m u v W D : ℝ}
    (hW : 0 ≤ W) (a : LoopArg L 2) :
    nearConvBd L m u v W D a ≤
      ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
        tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
          (zdist L (a 0 - a 1)) *
        (if (zdist L (a 0 - a 1) : ℝ)
          ≤ 6 * ellStar W (ellHat L (v : ℂ)) then 1 else 0)
      + tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
          (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
            Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
              ellHat L (v : ℂ) / 2))) := by
  by_cases ha : (zdist L (a 0 - a 1) : ℝ)
      ≤ 6 * ellStar W (ellHat L (v : ℂ))
  · simp only [nearConvBd, if_pos ha, mul_one]
    have hT : 0 ≤ tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 :=
      tailT_nonneg hW _
    have hε : 0 ≤ 128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
        Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
          ellHat L (v : ℂ) / 2)) := by positivity
    nlinarith
  · simp only [nearConvBd, if_neg ha, mul_zero, zero_add, le_refl]

/-- The leakage scale is smaller than every fixed power of `W` once the
standard large-`W` logarithmic threshold is reached. -/
theorem exp_neg_half_ellStar_le_rpow_neg {W D : ℝ}
    (hW : Real.exp 1 ≤ W) (hD : 0 ≤ D)
    (hlog : (4 * D) ^ 2 ≤ Real.log W) :
    Real.exp (-(Real.log W ^ ((3 : ℝ) / 2) / 2)) ≤ W ^ (-2 * D) := by
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hl1 : 1 ≤ Real.log W := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hW
  have hl0 : 0 < Real.log W := by linarith
  have hsplit : Real.log W ^ ((3 : ℝ) / 2)
      = Real.log W * √(Real.log W) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hl0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsq : 4 * D ≤ √(Real.log W) := by
    have h := Real.sqrt_le_sqrt hlog
    rwa [Real.sqrt_sq (by positivity)] at h
  have hkey : 2 * D * Real.log W
      ≤ Real.log W ^ ((3 : ℝ) / 2) / 2 := by
    rw [hsplit]
    nlinarith [Real.sqrt_nonneg (Real.log W)]
  rw [Real.rpow_def_of_pos hW0]
  exact Real.exp_le_exp.2 (by nlinarith)

theorem tailT_zero_le_two {W ℓ η D : ℝ}
    (hW : 1 ≤ W) (hD : 0 ≤ D) (hA : 1 ≤ W * ℓ * η) :
    tailT W ℓ η D 0 ≤ 2 := by
  have hA2 : 1 ≤ (W * ℓ * η) ^ 2 := by nlinarith
  have hA2pos : 0 < (W * ℓ * η) ^ 2 := by linarith
  have hinv : ((W * ℓ * η) ^ 2)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hA2pos).2
    exact hA2
  have hpow : W ^ (-D) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
  simp only [tailT, zero_div, Real.sqrt_zero, neg_zero, Real.exp_zero, mul_one]
  linarith

/-- Under the usual large-`W` and bulk-scale assumptions, the near-band
leakage is a tail-sized far-field term. -/
theorem nearLeak_le_farTail (L : ℕ) {m u v W D : ℝ}
    (hW : Real.exp 1 ≤ W) (hD : 0 ≤ D)
    (hAu : 1 ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    (hℓv : 0 < ellHat L (v : ℂ))
    (hlog : (4 * D) ^ 2 ≤ Real.log W)
    (a : LoopArg L 2) :
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0 *
        (128 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
          Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
            ellHat L (v : ℂ) / 2)))
      ≤ 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 * W ^ (-D) *
        tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
          (zdist L (a 0 - a 1)) := by
  let Tu : ℝ := tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D 0
  let Tv : ℝ := tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
    (zdist L (a 0 - a 1))
  let ε : ℝ := W ^ (-D)
  let e : ℝ := Real.exp (-(ellStar W (ellHat L (v : ℂ)) /
    ellHat L (v : ℂ) / 2))
  let R2 : ℝ := ((1 - u) / (1 - v)) ^ 2
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hTu : Tu ≤ 2 := tailT_zero_le_two hW1 hD hAu
  have hTu0 : 0 ≤ Tu := tailT_nonneg hW0.le _
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hW0.le _
  have hTv : ε ≤ Tv := rpow_neg_le_tailT _
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hratio : ellStar W (ellHat L (v : ℂ)) /
      ellHat L (v : ℂ) / 2 = Real.log W ^ ((3 : ℝ) / 2) / 2 := by
    unfold ellStar
    field_simp
  have he : e ≤ ε ^ 2 := by
    have hp := exp_neg_half_ellStar_le_rpow_neg hW hD hlog
    have hpow : W ^ (-2 * D) = (W ^ (-D)) ^ 2 := by
      rw [show -2 * D = -D * 2 by ring, Real.rpow_mul hW0.le]
      norm_cast
    simpa only [e, hratio, ε, hpow] using hp
  have h1 : Tu * e ≤ 2 * ε ^ 2 :=
    mul_le_mul hTu he he0 (by norm_num)
  have h2 : ε ^ 2 ≤ ε * Tv := by
    nlinarith [mul_le_mul_of_nonneg_left hTv hε0]
  have h3 : Tu * e ≤ 2 * ε * Tv := by linarith
  have hc : 0 ≤ 128 * Real.exp 3 * R2 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  change Tu * (128 * Real.exp 3 * R2 * e) ≤
    256 * Real.exp 3 * R2 * ε * Tv
  nlinarith only [h4]

theorem nearConvBd_le_indicator_farTail (L : ℕ) {m u v W D : ℝ}
    (hW : Real.exp 1 ≤ W) (hD : 0 ≤ D)
    (hAu : 1 ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    (hℓv : 0 < ellHat L (v : ℂ))
    (hlog : (4 * D) ^ 2 ≤ Real.log W)
    (a : LoopArg L 2) :
    nearConvBd L m u v W D a ≤
      ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
        tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
          (zdist L (a 0 - a 1)) *
        (if (zdist L (a 0 - a 1) : ℝ)
          ≤ 6 * ellStar W (ellHat L (v : ℂ)) then 1 else 0)
      + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 * W ^ (-D) *
          tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
            (zdist L (a 0 - a 1)) := by
  have h1 := nearConvBd_le_indicator L (m := m) (u := u) (v := v)
    (W := W) (D := D) (le_trans (Real.exp_nonneg 1) hW) a
  have h2 := nearLeak_le_farTail L hW hD hAu hℓv hlog a
  linarith

/-- Propagation of a diagonal square-root rate with a near term, a tail
term, and a distance-independent residual.  The near support enlarges from
`4ℓ*_u` to `6ℓ*_v`; the far leakage is explicit. -/
theorem weightedKernel_three_le (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {W D : ℝ} (hW : Real.exp 1 ≤ W)
    (hAuv : W * ellHat L (v : ℂ) * ((1 - v) * m)
      ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    {Cn Cf Cr : ℝ} (hCn : 0 ≤ Cn) (hCf : 0 ≤ Cf) (hCr : 0 ≤ Cr)
    (f : LoopArg L 2 → ℝ)
    (hf : ∀ b, f b ≤ Cn *
        (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
            (zdist L (b 0 - b 1)) *
          (if (zdist L (b 0 - b 1) : ℝ)
            ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0))
        + Cf * tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D
            (zdist L (b 0 - b 1)) + Cr)
    (a : LoopArg L 2) :
    (∑ b : LoopArg L 2,
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖ * f b)
      ≤ Cn * nearConvBd L m u v W D a
        + Cf * (((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
            tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
              (zdist L (a 0 - a 1)))
        + Cr * ((1 - u) / (1 - v)) ^ 2 := by
  classical
  let K : LoopArg L 2 → ℝ := fun b =>
    ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)‖
  let T : LoopArg L 2 → ℝ := fun b =>
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (b 0 - b 1))
  let χ : LoopArg L 2 → ℝ := fun b =>
    if (zdist L (b 0 - b 1) : ℝ)
      ≤ 4 * ellStar W (ellHat L (u : ℂ)) then 1 else 0
  have hW0 : 0 ≤ W := le_trans (Real.exp_nonneg 1) hW
  have hT0 (b : LoopArg L 2) : 0 ≤ T b := tailT_nonneg hW0 _
  have hnear : (∑ b : LoopArg L 2, K b * (T b * χ b))
      ≤ nearConvBd L m u v W D a := by
    by_cases ha : (zdist L (a 0 - a 1) : ℝ)
        ≤ 6 * ellStar W (ellHat L (v : ℂ))
    · rw [nearConvBd, if_pos ha]
      calc
        (∑ b : LoopArg L 2, K b * (T b * χ b))
          ≤ ∑ b : LoopArg L 2, K b * T b := by
            refine Finset.sum_le_sum fun b _ => ?_
            have hχ : χ b ≤ 1 := by simp only [χ]; split_ifs <;> norm_num
            calc K b * (T b * χ b) = (K b * T b) * χ b := by ring
              _ ≤ (K b * T b) * 1 :=
                mul_le_mul_of_nonneg_left hχ
                  (mul_nonneg (norm_nonneg _) (hT0 b))
              _ = K b * T b := by ring
        _ ≤ _ := weightedKernel_tail_le L hL hm0 hm1 hu0 huv hv1 hW hAuv a
    · rw [nearConvBd, if_neg ha]
      have hd : 6 * ellStar W (ellHat L (v : ℂ))
          ≤ (zdist L (a 0 - a 1) : ℝ) := le_of_lt (lt_of_not_ge ha)
      exact weightedKernel_near_tail_far_le L hL hm0 hm1 hu0 huv hv1 hW a hd
  have htail : (∑ b : LoopArg L 2, K b * T b)
      ≤ ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
          tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D
            (zdist L (a 0 - a 1)) :=
    weightedKernel_tail_le L hL hm0 hm1 hu0 huv hv1 hW hAuv a
  have hrow : (∑ b : LoopArg L 2, K b)
      ≤ ((1 - u) / (1 - v)) ^ 2 :=
    weightedKernel_row_le L hL huv (hu0.trans huv) hv1 a
  calc
    (∑ b : LoopArg L 2, K b * f b)
      ≤ ∑ b : LoopArg L 2,
          K b * (Cn * (T b * χ b) + Cf * T b + Cr) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf b) (norm_nonneg _)
    _ = Cn * (∑ b : LoopArg L 2, K b * (T b * χ b))
        + Cf * (∑ b : LoopArg L 2, K b * T b)
        + Cr * (∑ b : LoopArg L 2, K b) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ _ := by
      have hn := mul_le_mul_of_nonneg_left hnear hCn
      have hf' := mul_le_mul_of_nonneg_left htail hCf
      have hr := mul_le_mul_of_nonneg_left hrow hCr
      linarith

private theorem sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  have hxy : 0 ≤ √x * √y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt (add_nonneg hx hy), Real.sqrt_nonneg x,
    Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y)]

private theorem sqrt_three_le {A B C T χ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hχ : χ = 0 ∨ χ = 1) :
    √((A * χ + B) * T ^ 2 + C)
      ≤ √A * (T * χ) + √B * T + √C := by
  rcases hχ with rfl | rfl
  · simp only [mul_zero, zero_add, mul_zero, zero_add]
    calc
      √(B * T ^ 2 + C) ≤ √(B * T ^ 2) + √C :=
        sqrt_add_le _ _ (mul_nonneg hB (sq_nonneg _)) hC
      _ = √B * T + √C := by rw [Real.sqrt_mul hB, Real.sqrt_sq hT]
  · simp only [mul_one]
    have hAB : 0 ≤ A * T ^ 2 + B * T ^ 2 :=
      add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _))
    have heq : (A + B) * T ^ 2 + C = (A * T ^ 2 + B * T ^ 2) + C := by ring
    rw [heq]
    calc
      √(A * T ^ 2 + B * T ^ 2 + C)
        ≤ √(A * T ^ 2 + B * T ^ 2) + √C := sqrt_add_le _ _ hAB hC
      _ ≤ (√(A * T ^ 2) + √(B * T ^ 2)) + √C := by
        gcongr
        exact sqrt_add_le _ _ (mul_nonneg hA (sq_nonneg _))
          (mul_nonneg hB (sq_nonneg _))
      _ = √A * T + √B * T + √C := by
        rw [Real.sqrt_mul hA, Real.sqrt_mul hB, Real.sqrt_sq hT]

noncomputable def diagNearRate (B : Band Ω) (N : ℕ) (ℓu ℓs ηu : ℝ) : ℝ :=
  2 * ηu⁻¹ * Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5

noncomputable def diagFarRate (B : Band Ω) (N : ℕ)
    (ℓu ηu D J Smax : ℝ) : ℝ :=
  2 * ηu⁻¹ *
      (Lemma57.cFar2 (B.W N : ℝ) ℓu *
          ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
        + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    + 4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3

noncomputable def diagResidual (B : Band Ω) (N : ℕ) (ρ : ℝ) : ℝ :=
  2 * (B.W N : ℝ) * (B.L N : ℝ) * ρ

/-- T262's diagonal shape splits into a supported near coefficient, a tail
coefficient, and the Step-1 residual. -/
theorem sqrt_diagShape_le_three (B : Band Ω) (N : ℕ)
    {ℓu ℓs ηu D J Smax ρ : ℝ}
    (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hJ : 1 ≤ J) (hρ : 0 ≤ ρ)
    (b : LoopArg (B.L N) (0 + 2)) :
    √(diagShape B N ℓu ℓs ηu D J Smax ρ b)
      ≤ √(diagNearRate B N ℓu ℓs ηu) *
          (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) *
            (if (zdist (B.L N) (b 0 - b 1) : ℝ)
              ≤ 4 * ellStar (B.W N : ℝ) ℓu then 1 else 0))
        + √(diagFarRate B N ℓu ηu D J Smax) *
          tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1))
        + √(diagResidual B N ρ) := by
  let T : ℝ := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1))
  let χ : ℝ := if (zdist (B.L N) (b 0 - b 1) : ℝ)
    ≤ 4 * ellStar (B.W N : ℝ) ℓu then 1 else 0
  let An : ℝ := diagNearRate B N ℓu ℓs ηu
  let Af : ℝ := diagFarRate B N ℓu ηu D J Smax
  let Ar : ℝ := diagResidual B N ρ
  have hnear0 : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) ℓu :=
    Lemma57.cNear2_nonneg hW hℓu
  have hfar0 : 0 ≤ Lemma57.cFar2 (B.W N : ℝ) ℓu :=
    Lemma57.cFar2_nonneg hW hℓu
  have hAn : 0 ≤ An := by dsimp [An, diagNearRate]; positivity
  have hAf : 0 ≤ Af := by dsimp [Af, diagFarRate]; positivity
  have hAr : 0 ≤ Ar := by dsimp [Ar, diagResidual]; positivity
  have hT : 0 ≤ T := tailT_nonneg (by linarith : (0 : ℝ) ≤ B.W N) _
  have hχ : χ = 0 ∨ χ = 1 := by simp only [χ]; split_ifs <;> simp
  have hshape : diagShape B N ℓu ℓs ηu D J Smax ρ b
      = (An * χ + Af) * T ^ 2 + Ar := by
    dsimp [diagShape, An, Af, Ar, diagNearRate, diagFarRate,
      diagResidual, T, χ]
    ring
  rw [hshape]
  exact sqrt_three_le hAn hAf hAr hT hχ

set_option maxHeartbeats 2000000 in
-- The endpoint statement elaborates a large pointwise T262 hypothesis bundle.
/-- Endpoint propagation of T262's *diagonal* bound for the alternating
two-loop observable.  The near term is confined to `6ℓ*_v` up to explicit
exponential leakage; the far term is the sharp T262 coefficient containing
`(J*)²`.  All random estimates enter pointwise at `(u, ω)`. -/
theorem sqrt_evolvedQV_le_endpoint (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (hW : Real.exp 1 ≤ (B.W N : ℝ)) (ω : Ω)
    (a : LoopArg (B.L N) 2)
    {ℓs D J : ℝ} (hℓs : 0 < ℓs) (hJ : 1 ≤ J)
    (hD : 0 ≤ D)
    (hAu : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u)
    (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N))
        (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ c b, EEDef.eeL6 X E N u ω Step2.sigPM (Fin.append c c) b
      ≤ (B.ell N u / ℓs) ^ 5 *
        ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹) ^ 2 *
        ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (h564 : ∀ c b, Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u)
      < (zdist (B.L N) (c 0 - b) : ℝ) →
        EEDef.eeL6 X E N u ω Step2.sigPM (Fin.append c c) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2
        ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * Step2.tT B E N D u (zdist (B.L N) (x - y))) :
    √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
          (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u)
            (Gauss.toIdx Step2.sigPM b) M') a)
        (X.H N u ω))
      ≤ √(diagNearRate B N (B.ell N u) ℓs (etaT E u)) *
          ((((1 - u) / (1 - v)) ^ 2 *
              Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
              Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) *
            (if (zdist (B.L N) (a 0 - a 1) : ℝ)
                ≤ 6 * ellStar (B.W N : ℝ) (B.ell N v) then 1 else 0)
          + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
              (B.W N : ℝ) ^ (-D) *
              Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))
        + √(diagFarRate B N (B.ell N u) (etaT E u) D J Smax) *
          (((1 - u) / (1 - v)) ^ 2 *
            Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
            Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))
        + √(diagResidual B N ρ) * ((1 - u) / (1 - v)) ^ 2 := by
  classical
  have hu1 : u < 1 := huv.trans_lt hv1
  have hL1 : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hℓu : 1 ≤ B.ell N u :=
    one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hW0 : 0 ≤ (B.W N : ℝ) := by positivity
  have hW1 : 1 ≤ (B.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hW
  have hℓv : 0 < ellHat (B.L N) (v : ℂ) := by
    have := one_le_ellHat_of_nonneg hL1 (hu0.trans huv) hv1
    linarith
  have hAuv : (B.W N : ℝ) * ellHat (B.L N) (v : ℂ) *
      ((1 - v) * (mE E).im) ≤
      (B.W N : ℝ) * ellHat (B.L N) (u : ℂ) *
      ((1 - u) * (mE E).im) := by
    have h := flowScale_antitoneOn hW0 (B.L N) E
      (Set.mem_Iic.2 (huv.trans hv1.le)) (Set.mem_Iic.2 hv1.le) huv
    exact h
  have hdiag := sqrt_quadVar_Uker_le_diagShape X hE (u := u) (v := v) hu0 hu1 ω
    Step2.sigPM a hℓu hℓs hηu hJ hρ hGm0 hGm hGsq0 hGsq2
    hrow hSmax h273 h564 (by simpa only [Step2.tT] using h42sq)
  have hthree := weightedKernel_three_le (B.L N) (B.three_le_L N)
    (mE_im_pos hE) (mE_im_le_one hE)
    hu0 huv hv1 hW hAuv
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun b : LoopArg (B.L N) 2 =>
      √(diagShape B N (B.ell N u) ℓs (etaT E u) D J Smax ρ b))
    (fun b => sqrt_diagShape_le_three B N
      hW1 (by linarith : 0 < B.ell N u)
      hℓs hηu hJ hρ b) a
  rw [Step2.sigPM_xi hE.le] at hdiag
  have hAu' : 1 ≤ (B.W N : ℝ) * ellHat (B.L N) (u : ℂ) *
      ((1 - u) * (mE E).im) := by
    simpa only [Band.ell, Step2.etaT_eq] using hAu
  have hnear := nearConvBd_le_indicator_farTail (B.L N)
    (m := (mE E).im) (u := u) (v := v)
    (W := (B.W N : ℝ)) (D := D) hW hD hAu' hℓv hlog a
  have hmul := mul_le_mul_of_nonneg_left hnear (Real.sqrt_nonneg
    (diagNearRate B N (B.ell N u) ℓs (etaT E u)))
  have hmain := hdiag.trans hthree
  have hfinal :
      √(Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u)
            (Gauss.toIdx Step2.sigPM b) M') a) (X.H N u ω))
        ≤ √(diagNearRate B N (B.ell N u) ℓs (etaT E u)) *
            (((1 - u) / (1 - v)) ^ 2 * Step2.xiK (B.L N) (B.W N : ℝ)
              (mE E).im *
              tailT (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                ((1 - v) * (mE E).im) D (zdist (B.L N) (a 0 - a 1)) *
              (if (zdist (B.L N) (a 0 - a 1) : ℝ)
                  ≤ 6 * ellStar (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                then 1 else 0)
            + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
                (B.W N : ℝ) ^ (-D) *
                tailT (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                  ((1 - v) * (mE E).im) D
                  (zdist (B.L N) (a 0 - a 1)))
          + √(diagFarRate B N (B.ell N u) (etaT E u) D J Smax) *
            (((1 - u) / (1 - v)) ^ 2 * Step2.xiK (B.L N) (B.W N : ℝ)
              (mE E).im *
              tailT (B.W N : ℝ) (ellHat (B.L N) (v : ℂ))
                ((1 - v) * (mE E).im) D (zdist (B.L N) (a 0 - a 1)))
          + √(diagResidual B N ρ) * ((1 - u) / (1 - v)) ^ 2 := by
    linarith only [hmain, hmul]
  rw [Step2.sigPM_xi hE.le, Step2.tT, Band.ell, Step2.etaT_eq]
  exact hfinal

/-- Squaring an endpoint square-root estimate gives the corresponding
quadratic-variation estimate; no sign assumption on the proposed bound is
needed, since it is already above `√QV`. -/
theorem quadVar_le_sq_of_sqrt_le {Q R : ℝ} (hQ : 0 ≤ Q) (h : √Q ≤ R) :
    Q ≤ R ^ 2 := by
  nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg Q]

/-- Four separately propagated square-root contributions give a sum-shaped
quadratic-variation envelope with a fixed numerical constant. -/
theorem quadVar_le_four_terms {Q a b c d : ℝ} (hQ : 0 ≤ Q)
    (h : √Q ≤ a + b + c + d) :
    Q ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have hs := quadVar_le_sq_of_sqrt_le hQ h
  nlinarith only [hs, sq_nonneg (a - b), sq_nonneg (a - c),
    sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (c - d)]

/-- Positive-duration, nondegenerate witness for the deterministic scale
conditions used when the near-band leakage is absorbed into the far tail. -/
theorem endpoint_scale_witness :
    ∃ W u v D : ℝ, 0 ≤ u ∧ u < v ∧ v < 1 ∧
      Real.exp 1 ≤ W ∧ 0 ≤ D ∧
      1 ≤ W * ellHat 3 (u : ℂ) * ((1 - u) * (1 : ℝ)) ∧
      (4 * D) ^ 2 ≤ Real.log W := by
  refine ⟨Real.exp 16, 0, 1 / 2, 1, by norm_num, by norm_num,
    by norm_num, ?_, by norm_num, ?_, ?_⟩
  · exact Real.exp_le_exp.2 (by norm_num)
  · have hW : 1 ≤ Real.exp 16 := Real.one_le_exp (by norm_num)
    have hℓ : 1 ≤ ellHat 3 ((0 : ℝ) : ℂ) :=
      one_le_ellHat_of_nonneg (by norm_num) (by norm_num) (by norm_num)
    have hp : 1 ≤ Real.exp 16 * ellHat 3 ((0 : ℝ) : ℂ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hW) (sub_nonneg.mpr hℓ)]
    simpa using hp
  · norm_num [Real.log_exp]

/-- The quadratic variation in the endpoint theorem is exactly the rate of
the evolved `(L-K)` test function used by the Duhamel model.  The primitive
`K` disappears from the matrix derivative. -/
theorem quadVar_ukerObsT_eq_evolved_loopObs (B : Band Ω) (E : ℝ) (N : ℕ)
    (u v : ℝ) (a : LoopArg (B.L N) 2)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) :
    Gauss.quadVar B.toDims N
        (Gauss.ukerObsT B.toDims N E (List.ofFn Step2.sigPM)
          (xiOf (mSigma E) Step2.sigPM) (v : ℂ)
          (fun r b => B.Kval E N r (LoopData.idx (Step2.sigPM, b))) a u) M
      = Gauss.quadVar B.toDims N
        (fun M' => Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
          (u : ℂ) (v : ℂ)
          (fun b => Gauss.loopObs B.toDims N (zt E u)
            (Gauss.toIdx Step2.sigPM b) M') a) M := by
  have h := Gauss.quadVar_ukerObsT_eq_quadVarPairs
    (d := B.toDims) (N := N) E Step2.sigPM
    (xiOf (mSigma E) Step2.sigPM) (v : ℂ)
    (fun r b => B.Kval E N r (LoopData.idx (Step2.sigPM, b))) a u M
  exact h.trans (Gauss.secondOrder_eq_quadVar _ _).symm

end APrimeQVEndpoint
end RBM

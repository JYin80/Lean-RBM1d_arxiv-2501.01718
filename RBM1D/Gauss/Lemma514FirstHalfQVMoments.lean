/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514FirstCellLKDecay
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Gauss.MomentDuhamelQInt
import RBM1D.Gauss.Lemma514QRoute
import RBM1D.Gauss.LkGoodMeasurable
import RBM1D.Gauss.Step6Sample

/-!
# T1387: actual first-half all-order QV envelope moments

The envelope is built from the concrete `E ⊗ E` tensor and its `Q_u ⊗ Q_u`
image on the actual `Dims.exampleGrow` Gaussian model.  Its loop-label maximum
is a finite supremum; charges remain the actual `LoopData` charges.
-/

namespace RBM.Gauss.Lemma514FirstHalfQVMoments

open Filter MeasureTheory Real Set RBM.MomentDuhamel

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

private noncomputable def eeDetBound (n N : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ) * ((B.W N : ℝ) *
    ((Fintype.card (ZMod (B.L N)) : ℝ) *
      ((1 / 2 : ℝ)⁻¹ ^ (2 * (n + 2) + 2) *
        ((B.W N : ℝ)⁻¹) ^ (2 * (n + 2) + 1))))

private noncomputable def qqDetBound (n N : ℕ) : ℝ :=
  (1 + (Fintype.card (LoopArg (B.L N) (n + 1)) : ℝ)) ^ 2 * eeDetBound n N

private noncomputable def detEnvelopeBound (n N : ℕ) (u : ℝ) : ℝ :=
  |B.scale 0 N u| ^ (2 * (n + 2)) * (eeDetBound n N + qqDetBound n N)

private theorem eeDetBound_nonneg (n N : ℕ) : 0 ≤ eeDetBound n N := by
  unfold eeDetBound
  positivity

private theorem qqDetBound_nonneg (n N : ℕ) : 0 ≤ qqDetBound n N := by
  unfold qqDetBound
  exact mul_nonneg (sq_nonneg _) (eeDetBound_nonneg n N)

private theorem detEnvelopeBound_nonneg (n N : ℕ) (u : ℝ) :
    0 ≤ detEnvelopeBound n N u := by
  unfold detEnvelopeBound
  exact mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (add_nonneg (eeDetBound_nonneg n N) (qqDetBound_nonneg n N))

private theorem xiL_first_half_le_two_pow {m N : ℕ} {u : ℝ}
    (hm : 1 ≤ m) (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (ω : Gauss.Ω d) :
    (Gauss.sample d).xiL 0 N u ω m ≤ (2 : ℝ) ^ m := by
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have heta : etaT 0 u = 1 - u := by
    rw [Step2.etaT_eq, mE_zero]
    norm_num
  have heta0 : 0 < etaT 0 u := by rw [heta]; linarith
  have hetaInv : (etaT 0 u)⁻¹ ≤ 2 := by
    rw [heta]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - u := by linarith [hu.2]
    calc
      (1 - u)⁻¹ = 1 / (1 - u) := by rw [one_div]
      _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hhalf
      _ = 2 := by norm_num
  have hell : B.ell N u ≤ 2 := by
    change ellHat (B.L N) ((u : ℝ) : ℂ) ≤ 2
    calc
      ellHat (B.L N) ((u : ℝ) : ℂ) ≤ 1 / √(1 - u) :=
        ellHat_real_le_inv_sqrt (L := B.L N) hu1
      _ ≤ 2 := by
        have hsqrt : (1 / 2 : ℝ) ≤ √(1 - u) := by
          apply (Real.le_sqrt (by positivity) (by positivity)).2
          nlinarith [hu.2]
        exact (one_div_le_one_div_of_le (by norm_num) hsqrt).trans_eq (by norm_num)
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := by
    exact_mod_cast (show 1 ≤ B.W N by have := B.W_pos N; omega)
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hscale : B.scale 0 N u = (B.W N : ℝ) * B.ell N u * etaT 0 u := rfl
  have hscalePos : 0 < B.scale 0 N u :=
    B.scale_pos' (E := 0) (by norm_num) N hu.1 hu1
  have hdet := Gauss.loopXi_le_det ((Gauss.sample d).hermitian N u ω)
    (E := 0) (t := u) (A := B.scale 0 N u) (n := m)
    (by norm_num : |(0 : ℝ)| < 2) hu1 hscalePos.le hm
  have hpowEq : (etaT 0 u)⁻¹ ^ m * ((B.W N : ℝ)⁻¹) ^ (m - 1)
      * B.scale 0 N u ^ (m - 1) = (etaT 0 u)⁻¹ * (B.ell N u) ^ (m - 1) := by
    rw [hscale]
    let k := m - 1
    have hm' : m = k + 1 := by dsimp [k]; omega
    have hmk : m - 1 = k := by rfl
    rw [hmk, hm', pow_succ, mul_pow, mul_pow]
    have hwc : ((B.W N : ℝ)⁻¹) ^ k * (B.W N : ℝ) ^ k = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hW0.ne']
      simp
    have hetac : (etaT 0 u)⁻¹ ^ k * (etaT 0 u) ^ k = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ heta0.ne']
      simp
    calc
      _ = ((etaT 0 u)⁻¹ ^ k * (etaT 0 u) ^ k) * (etaT 0 u)⁻¹ *
          (((B.W N : ℝ)⁻¹) ^ k * (B.W N : ℝ) ^ k) * (B.ell N u) ^ k := by ring
      _ = (etaT 0 u)⁻¹ * (B.ell N u) ^ k := by rw [hetac, hwc]; ring
  rw [hpowEq] at hdet
  have hell0 : 0 ≤ B.ell N u := by
    change 0 ≤ ellHat (B.L N) ((u : ℝ) : ℂ)
    have hL1 : 1 ≤ B.L N := le_trans (by norm_num) (B.three_le_L N)
    exact le_trans (by norm_num) (one_le_ellHat_of_nonneg hL1 hu.1 hu1)
  rw [Sample.xiL]
  calc
    loopXi (B.L N) (B.W N) ((Gauss.sample d).H N u ω) (zt 0 u) (B.scale 0 N u) m
        ≤ (etaT 0 u)⁻¹ * (B.ell N u) ^ (m - 1) := by simpa [B, d] using hdet
    _ ≤ 2 * (2 : ℝ) ^ (m - 1) := mul_le_mul hetaInv
      (pow_le_pow_left₀ hell0 hell (m - 1)) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (m - 1 + 1) := by rw [pow_succ]; ring
    _ = (2 : ℝ) ^ m := by congr 1; exact Nat.sub_add_cancel hm

/-- The first-half Lemma 5.14 QV envelope: the actual `E ⊗ E` tensor and its
`Q_u ⊗ Q_u` image, maximised over the finite doubled-loop label set. -/
noncomputable def qvEnvelope (n N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) : Gauss.Ω d → ℝ := fun ω =>
  if u ∈ Set.Icc (0 : ℝ) (1 / 2) then
    (B.scale 0 N u) ^ (2 * (n + 2)) *
      Finset.univ.sup' Finset.univ_nonempty (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
          ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖)
  else 0

/-- The finite maximum majorises the actual `E ⊗ E` tensor on the first half. -/
theorem eeFun_norm_le_qvEnvelope {n N : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (q : LoopData (B.L N) (n + 2))
    (ω : Gauss.Ω d) (b : LoopArg (B.L N) ((n + 2) + (n + 2)))
    (hscale : 0 ≤ B.scale 0 N u) :
    (B.scale 0 N u) ^ (2 * (n + 2)) *
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖
      ≤ qvEnvelope n N u q ω := by
  classical
  unfold qvEnvelope
  rw [if_pos hu]
  have hpow : 0 ≤ (B.scale 0 N u) ^ (2 * (n + 2)) := pow_nonneg hscale _
  have hle : ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ ≤
      Finset.univ.sup' Finset.univ_nonempty (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
          ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖) :=
    le_trans (le_add_of_nonneg_right (norm_nonneg _))
      (Finset.le_sup' (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
          ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖)
        (Finset.mem_univ b))
  exact mul_le_mul_of_nonneg_left hle hpow

/-- The finite maximum majorises the actual projected QV tensor on the first half. -/
theorem qq_norm_le_qvEnvelope {n N : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (q : LoopData (B.L N) (n + 2))
    (ω : Gauss.Ω d) (b : LoopArg (B.L N) ((n + 2) + (n + 2)))
    (hscale : 0 ≤ B.scale 0 N u) :
    (B.scale 0 N u) ^ (2 * (n + 2)) *
        ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖
      ≤ qvEnvelope n N u q ω := by
  classical
  unfold qvEnvelope
  rw [if_pos hu]
  have hpow : 0 ≤ (B.scale 0 N u) ^ (2 * (n + 2)) := pow_nonneg hscale _
  have hle : ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
        (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖ ≤
      Finset.univ.sup' Finset.univ_nonempty (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
          ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖) :=
    le_trans (le_add_of_nonneg_left (norm_nonneg _))
      (Finset.le_sup' (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
          ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖)
        (Finset.mem_univ b))
  exact mul_le_mul_of_nonneg_left hle hpow

private theorem eeFun_continuous {n N : ℕ} (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    Continuous (fun ω : Gauss.Ω d =>
      MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) σ b) := by
  rw [← continuousOn_univ]
  exact continuousOn_eeFun_path d N 0
    (τ := fun _ : Gauss.Ω d => u) (Mt := fun ω => Gauss.Hflow d N u ω)
    continuousOn_const (Gauss.continuous_Hflow d N u).continuousOn
    (fun ω => Gauss.Hflow_isHermitian d N u ω)
    (fun _ _ => Gauss.zt_im_ne_zero_of_lt_one (by norm_num) hu1) σ b

private theorem qq_eeFun_continuous {n N : ℕ} (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    Continuous (fun ω : Gauss.Ω d =>
      SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
        (fun c => MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) σ c) b) := by
  rw [← continuousOn_univ]
  refine continuousOn_QQ_of_tensor (B.L N) (k := n + 1)
    (d.three_le_L N) (τ := fun _ : Gauss.Ω d => u) continuousOn_const
    (fun _ _ => hu0) (fun _ _ => hu1)
    (fun ω c => MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) σ c)
    (fun c => ?_) b
  exact (eeFun_continuous u hu0 hu1 σ c).continuousOn

private theorem norm_QQ_le_twoProjection {L k : ℕ} [NeZero L] {u R e δ : ℝ}
    (hL : 3 ≤ L) (hu0 : 0 ≤ u) (hu1 : u < 1) (hR : 0 < R)
    (he : 0 ≤ e) (hδ : 0 ≤ δ)
    {A : LoopArg L ((k + 1) + (k + 1)) → ℂ}
    (hAe : ∀ c, ‖A c‖ ≤ e) (hAd : FastDecay L R δ A) (c : LoopArg L ((k + 1) + (k + 1))) :
    ‖SumZeroDyn.QQ L ((u : ℝ) : ℂ) A c‖ ≤
      FastDecayFlow.qBlockSize L k (ellHat L ((u : ℝ) : ℂ)) (2 * R)
        (FastDecayFlow.qBlockSize L k (ellHat L ((u : ℝ) : ℂ)) R e δ)
        (FastDecayFlow.qBlockErr L k (ellHat L ((u : ℝ) : ℂ)) R e δ) := by
  let ℓr := ellHat L ((u : ℝ) : ℂ)
  let e₂ := FastDecayFlow.qBlockSize L k ℓr R e δ
  let δ₂ := FastDecayFlow.qBlockErr L k ℓr R e δ
  have hℓ : 0 < ℓr := by
    dsimp [ℓr]
    exact lt_of_lt_of_le (by norm_num) (half_le_ellHat_real L hL hu0 hu1)
  have hR2 : 0 < 2 * R := by positivity
  have he₂0 : 0 ≤ e₂ := by
    dsimp [e₂, ℓr]
    exact FastDecayFlow.qBlockSize_nonneg L k (by linarith) (by linarith) he hδ
  have hδ₂0 : 0 ≤ δ₂ := by
    dsimp [δ₂, ℓr]
    exact FastDecayFlow.qBlockErr_nonneg L k (by linarith) (by linarith) he hδ
  have h2max : ∀ c, ‖SumZeroDyn.Q2 L ((u : ℝ) : ℂ) A c‖ ≤ e₂ := by
    intro c
    exact SumZeroDyn.norm_Q2_le L hL hu0 hu1 hR he hδ hAe hAd c
  have h2dec : FastDecay L (2 * R) δ₂ (SumZeroDyn.Q2 L ((u : ℝ) : ℂ) A) := by
    simpa [δ₂, ℓr, FastDecayFlow.qBlockErr] using
      SumZeroDyn.fastDecay_Q2 L hL hu0 hu1 hR he hδ hAe hAd
  have h3 := SumZeroDyn.norm_Q1_le L hL hu0 hu1 hR2 he₂0 hδ₂0 h2max h2dec c
  rw [← SumZeroDyn.QQ_eq] at h3
  simpa [e₂, δ₂, ℓr, FastDecayFlow.qBlockSize] using h3

private noncomputable def eeGoodBound (n N : ℕ) (u τ D : ℝ) : ℝ :=
  2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
      ((B.scale 0 N u)⁻¹ ^ (2 * (n + 2)) * (etaT 0 u)⁻¹ *
        (2 : ℝ) ^ (2 * (n + 2) + 2))
    + (n + 2) * (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D)

private noncomputable def qqGoodBound (n N : ℕ) (u τ D : ℝ) : ℝ :=
  FastDecayFlow.qBlockSize (B.L N) (n + 1) (B.ell N u) (2 * (B.ell N u * (N : ℝ) ^ τ)
    )
    (FastDecayFlow.qBlockSize (B.L N) (n + 1) (B.ell N u) (B.ell N u * (N : ℝ) ^ τ)
      (eeGoodBound n N u τ D)
      ((B.W N : ℝ) * (n + 2) * ((B.L N : ℝ) * (N : ℝ) ^ (-D))))
    (FastDecayFlow.qBlockErr (B.L N) (n + 1) (B.ell N u) (B.ell N u * (N : ℝ) ^ τ)
      (eeGoodBound n N u τ D)
      ((B.W N : ℝ) * (n + 2) * ((B.L N : ℝ) * (N : ℝ) ^ (-D))))

private noncomputable def qGoodX (n N : ℕ) (u τ : ℝ) : ℝ :=
  (2 * exp 1 * (B.ell N u * (N : ℝ) ^ τ + 1)) ^ (n + 1) *
    (RBM.cTwo52 / B.ell N u) ^ (n + 1)

private noncomputable def qGoodY (n N : ℕ) (u τ : ℝ) : ℝ :=
  (2 * exp 1 * (2 * (B.ell N u * (N : ℝ) ^ τ) + 1)) ^ (n + 1) *
    (RBM.cTwo52 / B.ell N u) ^ (n + 1)

private noncomputable def qGoodZ (n N : ℕ) (u : ℝ) : ℝ :=
  (B.L N : ℝ) ^ (n + 1) * (RBM.cTwo52 / B.ell N u) ^ (n + 1)

private noncomputable def qGoodH (N : ℕ) (u τ : ℝ) : ℝ :=
  exp (-(RBM.cZero * (B.ell N u * (N : ℝ) ^ τ) / B.ell N u))

private noncomputable def qGoodDelta (n N : ℕ) (D : ℝ) : ℝ :=
  (B.W N : ℝ) * (n + 2) * ((B.L N : ℝ) * (N : ℝ) ^ (-D))

/-- The nested projection costs expand exactly as the two q-block formulae prescribe. -/
private theorem qqGoodBound_expand (n N : ℕ) (u τ D : ℝ) :
    qqGoodBound n N u τ D =
      ((1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) +
          qGoodZ n N u * qGoodX n N u τ * qGoodH N u τ) * eeGoodBound n N u τ D +
        (qGoodZ n N u * (2 + qGoodY n N u τ) +
          qGoodZ n N u ^ 2 * (1 + qGoodH N u τ)) * qGoodDelta n N D := by
  unfold qqGoodBound eeGoodBound qGoodX qGoodY qGoodZ qGoodH qGoodDelta
  unfold FastDecayFlow.qBlockSize FastDecayFlow.qBlockErr
  ring_nf

private noncomputable def qGoodCx (n : ℕ) : ℝ :=
  (6 * exp 1 * RBM.cTwo52) ^ (n + 1)

private noncomputable def qGoodCy (n : ℕ) : ℝ :=
  (10 * exp 1 * RBM.cTwo52) ^ (n + 1)

private noncomputable def qGoodCz (n : ℕ) : ℝ := RBM.cTwo52 ^ (n + 1)

private noncomputable def qGoodEeCoeff (n : ℕ) : ℝ :=
  12 * exp 1 * (n + 2) * (2 : ℝ) ^ (2 * (n + 2) + 2)

private noncomputable def qGoodMainCoeff (n : ℕ) : ℝ :=
  1 + (1 + qGoodCx n) * (1 + qGoodCy n)

private noncomputable def qGoodExpCoeff (n : ℕ) : ℝ := qGoodCz n * qGoodCx n

private noncomputable def qGoodTotalCoeff (n : ℕ) : ℝ :=
  qGoodMainCoeff n + qGoodExpCoeff n + qGoodCz n * (2 + qGoodCy n) +
    2 * qGoodCz n ^ 2

private theorem qGood_factors_le {n N : ℕ} {u τ : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hN : 1 ≤ (N : ℝ))
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    qGoodX n N u τ ≤ qGoodCx n * ((N : ℝ) ^ τ) ^ (n + 1) ∧
    qGoodY n N u τ ≤ qGoodCy n * ((N : ℝ) ^ τ) ^ (n + 1) ∧
    qGoodZ n N u ≤ qGoodCz n * (B.L N : ℝ) ^ (n + 1) := by
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have hK1 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN hτ.le
  have hK0 : 0 ≤ (N : ℝ) ^ τ := by positivity
  have hL1 : 1 ≤ B.L N := by
    have := B.three_le_L N
    omega
  have hell1 : 1 ≤ B.ell N u := by
    change 1 ≤ ellHat (B.L N) ((u : ℝ) : ℂ)
    exact one_le_ellHat_of_nonneg hL1 hu.1 (hu.2.trans_lt (by norm_num))
  have hell2 : B.ell N u ≤ 2 := by
    change ellHat (B.L N) ((u : ℝ) : ℂ) ≤ 2
    calc
      ellHat (B.L N) ((u : ℝ) : ℂ) ≤ 1 / √(1 - u) :=
        ellHat_real_le_inv_sqrt (L := B.L N) hu1
      _ ≤ 2 := by
        have hsqrt : (1 / 2 : ℝ) ≤ √(1 - u) := by
          apply (Real.le_sqrt (by positivity) (by positivity)).2
          nlinarith [hu.2]
        exact (one_div_le_one_div_of_le (by norm_num) hsqrt).trans_eq (by norm_num)
  have hellpos : 0 < B.ell N u := by linarith
  have hcpos := RBM.cTwo52_pos
  have hcx : 2 * exp 1 * (B.ell N u * (N : ℝ) ^ τ + 1) *
        (RBM.cTwo52 / B.ell N u) ≤ 6 * exp 1 * RBM.cTwo52 * (N : ℝ) ^ τ := by
    have hA : B.ell N u * (N : ℝ) ^ τ + 1 ≤ 3 * (N : ℝ) ^ τ := by
      nlinarith [mul_le_mul_of_nonneg_right hell2 hK0]
    have hB : RBM.cTwo52 / B.ell N u ≤ RBM.cTwo52 := by
      rw [div_le_iff₀ hellpos]
      nlinarith [mul_le_mul_of_nonneg_left hell1 hcpos.le]
    calc
      _ ≤ 2 * exp 1 * (3 * (N : ℝ) ^ τ) * RBM.cTwo52 := by
        gcongr
      _ = _ := by ring
  have hcy : 2 * exp 1 * (2 * (B.ell N u * (N : ℝ) ^ τ) + 1) *
        (RBM.cTwo52 / B.ell N u) ≤ 10 * exp 1 * RBM.cTwo52 * (N : ℝ) ^ τ := by
    have hA : 2 * (B.ell N u * (N : ℝ) ^ τ) + 1 ≤ 5 * (N : ℝ) ^ τ := by
      nlinarith [mul_le_mul_of_nonneg_right hell2 hK0]
    have hB : RBM.cTwo52 / B.ell N u ≤ RBM.cTwo52 := by
      rw [div_le_iff₀ hellpos]
      nlinarith [mul_le_mul_of_nonneg_left hell1 hcpos.le]
    calc
      _ ≤ 2 * exp 1 * (5 * (N : ℝ) ^ τ) * RBM.cTwo52 := by
        gcongr
      _ = _ := by ring
  have hcz : RBM.cTwo52 / B.ell N u ≤ RBM.cTwo52 := by
    rw [div_le_iff₀ hellpos]
    nlinarith [mul_le_mul_of_nonneg_left hell1 hcpos.le]
  constructor
  · unfold qGoodX qGoodCx
    calc
      _ = (2 * exp 1 * (B.ell N u * (N : ℝ) ^ τ + 1) *
          (RBM.cTwo52 / B.ell N u)) ^ (n + 1) := by rw [← mul_pow]
      _ ≤ (6 * exp 1 * RBM.cTwo52 * (N : ℝ) ^ τ) ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) hcx (n + 1)
      _ = (6 * exp 1 * RBM.cTwo52) ^ (n + 1) * ((N : ℝ) ^ τ) ^ (n + 1) := by
        rw [mul_pow]
  constructor
  · unfold qGoodY qGoodCy
    calc
      _ = (2 * exp 1 * (2 * (B.ell N u * (N : ℝ) ^ τ) + 1) *
          (RBM.cTwo52 / B.ell N u)) ^ (n + 1) := by rw [← mul_pow]
      _ ≤ (10 * exp 1 * RBM.cTwo52 * (N : ℝ) ^ τ) ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) hcy (n + 1)
      _ = (10 * exp 1 * RBM.cTwo52) ^ (n + 1) * ((N : ℝ) ^ τ) ^ (n + 1) := by
        rw [mul_pow]
  · unfold qGoodZ qGoodCz
    calc
      _ = ((B.L N : ℝ) * (RBM.cTwo52 / B.ell N u)) ^ (n + 1) := by rw [← mul_pow]
      _ = (B.L N : ℝ) ^ (n + 1) * (RBM.cTwo52 / B.ell N u) ^ (n + 1) := by rw [mul_pow]
      _ ≤ (B.L N : ℝ) ^ (n + 1) * RBM.cTwo52 ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hcz (n + 1)) (by positivity)
      _ = RBM.cTwo52 ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) := by ring

private theorem scale_le_twoW {N : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    B.scale 0 N u ≤ 2 * (B.W N : ℝ) := by
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have heta : etaT 0 u = 1 - u := by rw [Step2.etaT_eq, mE_zero]; norm_num
  have heta1 : etaT 0 u ≤ 1 := by rw [heta]; linarith [hu.1]
  have heta0 : 0 ≤ etaT 0 u := by rw [heta]; linarith [hu.2]
  have hell : B.ell N u ≤ 2 := by
    change ellHat (B.L N) ((u : ℝ) : ℂ) ≤ 2
    calc
      ellHat (B.L N) ((u : ℝ) : ℂ) ≤ 1 / √(1 - u) :=
        ellHat_real_le_inv_sqrt (L := B.L N) hu1
      _ ≤ 2 := by
        have hsqrt : (1 / 2 : ℝ) ≤ √(1 - u) := by
          apply (Real.le_sqrt (by positivity) (by positivity)).2
          nlinarith [hu.2]
        exact (one_div_le_one_div_of_le (by norm_num) hsqrt).trans_eq (by norm_num)
  have hW0 : 0 ≤ (B.W N : ℝ) := by positivity
  change (B.W N : ℝ) * B.ell N u * etaT 0 u ≤ _
  calc
    (B.W N : ℝ) * B.ell N u * etaT 0 u ≤
        (B.W N : ℝ) * 2 * 1 := by gcongr
    _ = 2 * (B.W N : ℝ) := by ring

private theorem qGoodScaleDelta_le {n N : ℕ} {u D : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hN : 1 ≤ (N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ)) :
    (B.scale 0 N u) ^ (2 * (n + 2)) * qGoodDelta n N D ≤
      (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
        (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1 - D) := by
  have hW1 : 1 ≤ (B.W N : ℝ) := by
    have hw : 1 ≤ B.W N := by have := B.W_pos N; omega
    exact_mod_cast hw
  have hL1 : 1 ≤ (B.L N : ℝ) := by
    have hl : 1 ≤ B.L N := by have := B.three_le_L N; omega
    exact_mod_cast hl
  have hWle : (B.W N : ℝ) ≤ (N : ℝ) := by
    calc
      (B.W N : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := by nlinarith [hL1, hW1]
      _ ≤ (N : ℝ) := hWL
  have hscale := scale_le_twoW (N := N) hu
  have hscale0 : 0 ≤ B.scale 0 N u :=
    (B.scale_pos' (by norm_num) N hu.1 (hu.2.trans_lt (by norm_num))).le
  have hscalePow : (B.scale 0 N u) ^ (2 * (n + 2)) ≤
      (2 * (B.W N : ℝ)) ^ (2 * (n + 2)) :=
    pow_le_pow_left₀ hscale0 hscale _
  have hWpow : (B.W N : ℝ) ^ (2 * (n + 2)) ≤
      (N : ℝ) ^ (2 * (n + 2) : ℝ) := by
    have hp := SumZeroDyn.natCast_pow_le_rpow (by positivity) hWle (2 * (n + 2))
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hp
  have hNpos : 0 < (N : ℝ) := by linarith
  have hpow1 : (N : ℝ) ^ (2 * (n + 2) : ℝ) * (N : ℝ) =
      (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1) := by
    calc
      (N : ℝ) ^ (2 * (n + 2) : ℝ) * (N : ℝ) =
      (N : ℝ) ^ (2 * (n + 2) : ℝ) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1) := by
        rw [← Real.rpow_add hNpos]
  have hpow2 : (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1) * (N : ℝ) ^ (-D) =
      (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1 - D) := by
    calc
      (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1) * (N : ℝ) ^ (-D) =
          (N : ℝ) ^ (((2 * (n + 2) : ℝ) + 1) + (-D)) := by
        rw [← Real.rpow_add hNpos]
      _ = (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1 - D) := by congr 1 <;> ring
  unfold qGoodDelta
  calc
    (B.scale 0 N u) ^ (2 * (n + 2)) *
        ((B.W N : ℝ) * (n + 2) * ((B.L N : ℝ) * (N : ℝ) ^ (-D)))
      = (B.scale 0 N u) ^ (2 * (n + 2)) * (n + 2) *
          ((B.W N : ℝ) * (B.L N : ℝ)) * (N : ℝ) ^ (-D) := by push_cast; ring
    _ ≤ (2 * (B.W N : ℝ)) ^ (2 * (n + 2)) * (n + 2) *
          (N : ℝ) * (N : ℝ) ^ (-D) := by gcongr
    _ = (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          (B.W N : ℝ) ^ (2 * (n + 2)) * (N : ℝ) * (N : ℝ) ^ (-D) := by
        rw [mul_pow]
        ring
    _ ≤ (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          (N : ℝ) ^ (2 * (n + 2) : ℝ) * (N : ℝ) * (N : ℝ) ^ (-D) := by gcongr
    _ = (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          ((N : ℝ) ^ (2 * (n + 2) : ℝ) * (N : ℝ)) * (N : ℝ) ^ (-D) := by ring
    _ = (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1) * (N : ℝ) ^ (-D) := by rw [hpow1]
    _ = (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          ((N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1) * (N : ℝ) ^ (-D)) := by ring
    _ = (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1 - D) := by rw [hpow2]

private theorem eeGoodBound_scaled_le {n N : ℕ} {u τ D : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hK1 : 1 ≤ (N : ℝ) ^ τ) :
    (B.scale 0 N u) ^ (2 * (n + 2)) * eeGoodBound n N u τ D ≤
      qGoodEeCoeff n * (N : ℝ) ^ τ +
        (B.scale 0 N u) ^ (2 * (n + 2)) * qGoodDelta n N D := by
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have heta : etaT 0 u = 1 - u := by rw [Step2.etaT_eq, mE_zero]; norm_num
  have heta0 : 0 < etaT 0 u := by rw [heta]; linarith [hu.2]
  have hetaInv : (etaT 0 u)⁻¹ ≤ 2 := by
    rw [heta]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - u := by linarith [hu.2]
    calc
      (1 - u)⁻¹ = 1 / (1 - u) := by rw [one_div]
      _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hhalf
      _ = 2 := by norm_num
  have hApos : 0 < B.scale 0 N u := B.scale_pos' (by norm_num) N hu.1 hu1
  have hcan : (B.scale 0 N u) ^ (2 * (n + 2)) *
        (B.scale 0 N u)⁻¹ ^ (2 * (n + 2)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hApos.ne', one_pow]
  have hKadd : (N : ℝ) ^ τ + 2 ≤ 3 * (N : ℝ) ^ τ := by nlinarith [hK1]
  unfold eeGoodBound
  calc
    (B.scale 0 N u) ^ (2 * (n + 2)) *
        (2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
          ((B.scale 0 N u)⁻¹ ^ (2 * (n + 2)) * (etaT 0 u)⁻¹ *
            (2 : ℝ) ^ (2 * (n + 2) + 2)) +
          (n + 2) * (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D))
      = 2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
          ((etaT 0 u)⁻¹ * (2 : ℝ) ^ (2 * (n + 2) + 2)) *
          ((B.scale 0 N u) ^ (2 * (n + 2)) *
            (B.scale 0 N u)⁻¹ ^ (2 * (n + 2))) +
          (B.scale 0 N u) ^ (2 * (n + 2)) * qGoodDelta n N D := by
        unfold qGoodDelta
        ring
    _ = 2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
          ((etaT 0 u)⁻¹ * (2 : ℝ) ^ (2 * (n + 2) + 2)) +
          (B.scale 0 N u) ^ (2 * (n + 2)) * qGoodDelta n N D := by rw [hcan]; ring
    _ ≤ qGoodEeCoeff n * (N : ℝ) ^ τ +
          (B.scale 0 N u) ^ (2 * (n + 2)) * qGoodDelta n N D := by
        have hmain : 2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
              ((etaT 0 u)⁻¹ * (2 : ℝ) ^ (2 * (n + 2) + 2)) ≤
            qGoodEeCoeff n * (N : ℝ) ^ τ := by
          unfold qGoodEeCoeff
          calc
            _ ≤ 2 * exp 1 * (n + 2) * (3 * (N : ℝ) ^ τ) *
                (2 * (2 : ℝ) ^ (2 * (n + 2) + 2)) := by gcongr
            _ = _ := by ring
        exact add_le_add hmain le_rfl

set_option maxHeartbeats 0 in
private theorem qGood_coeff_bounds {n N : ℕ} {u τ : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hN : 1 ≤ (N : ℝ))
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ)) :
    let K := (N : ℝ) ^ τ
    let NP := (N : ℝ) ^ (n + 1)
    (1 + (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) ≤
      qGoodMainCoeff n * (K ^ (n + 1)) ^ 2) ∧
    (qGoodZ n N u * qGoodX n N u τ * qGoodH N u τ ≤
      qGoodExpCoeff n * (B.L N : ℝ) ^ (n + 1) * K ^ (n + 1) *
        Real.exp (-(RBM.cZero * K))) ∧
    (1 + (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) +
        qGoodZ n N u * qGoodX n N u τ * qGoodH N u τ +
        qGoodZ n N u * (2 + qGoodY n N u τ) +
        qGoodZ n N u ^ 2 * (1 + qGoodH N u τ) ≤
      qGoodTotalCoeff n * NP ^ 2) := by
  dsimp
  let K : ℝ := (N : ℝ) ^ τ
  let NP : ℝ := (N : ℝ) ^ (n + 1)
  have hK1 : 1 ≤ K := by dsimp [K]; exact Real.one_le_rpow hN hτ.le
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKleN : K ≤ (N : ℝ) := by
    dsimp [K]
    calc
      (N : ℝ) ^ τ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN hτ1
      _ = (N : ℝ) := by rw [Real.rpow_one]
  have hL1 : 1 ≤ (B.L N : ℝ) := by
    have h : 1 ≤ B.L N := by have := B.three_le_L N; omega
    exact_mod_cast h
  have hW1 : 1 ≤ (B.W N : ℝ) := by
    have h : 1 ≤ B.W N := by have := B.W_pos N; omega
    exact_mod_cast h
  have hLleN : (B.L N : ℝ) ≤ (N : ℝ) := by
    calc
      (B.L N : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := by nlinarith [hL1, hW1]
      _ ≤ (N : ℝ) := hWL
  have hellpos : 0 < B.ell N u := by
    change 0 < ellHat (B.L N) ((u : ℝ) : ℂ)
    exact lt_of_lt_of_le (by norm_num)
      (half_le_ellHat_real (B.L N) (B.three_le_L N) hu.1 (hu.2.trans_lt (by norm_num)))
  have hKpow1 : 1 ≤ K ^ (n + 1) := by
    exact one_le_pow₀ hK1
  have hNP1 : 1 ≤ NP := by
    dsimp [NP]
    exact one_le_pow₀ hN
  have hX := qGood_factors_le (n := n) (N := N) hu hN hτ hτ1
  have hXK : qGoodX n N u τ ≤ qGoodCx n * K ^ (n + 1) := by
    simpa [K] using hX.1
  have hYK : qGoodY n N u τ ≤ qGoodCy n * K ^ (n + 1) := by
    simpa [K] using hX.2.1
  have hZL : qGoodZ n N u ≤ qGoodCz n * (B.L N : ℝ) ^ (n + 1) := hX.2.2
  have hcpos := RBM.cTwo52_pos
  have hexpPos : 0 < Real.exp 1 := Real.exp_pos 1
  have hCxn : 0 ≤ qGoodCx n := by
    unfold qGoodCx
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le) RBM.cTwo52_pos.le
  have hCyn : 0 ≤ qGoodCy n := by
    unfold qGoodCy
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le) RBM.cTwo52_pos.le
  have hCzn : 0 ≤ qGoodCz n := by
    unfold qGoodCz
    exact pow_nonneg RBM.cTwo52_pos.le _
  have hX0 : 0 ≤ qGoodX n N u τ := by unfold qGoodX; positivity
  have hY0 : 0 ≤ qGoodY n N u τ := by unfold qGoodY; positivity
  have hZ0 : 0 ≤ qGoodZ n N u := by unfold qGoodZ; positivity
  have hXNP : qGoodX n N u τ ≤ qGoodCx n * NP := by
    have hpow : K ^ (n + 1) ≤ NP := by
      dsimp [K, NP]
      exact pow_le_pow_left₀ (by positivity) hKleN _
    exact hXK.trans (mul_le_mul_of_nonneg_left hpow hCxn)
  have hYNP : qGoodY n N u τ ≤ qGoodCy n * NP := by
    have hpow : K ^ (n + 1) ≤ NP := by
      dsimp [K, NP]
      exact pow_le_pow_left₀ (by positivity) hKleN _
    exact hYK.trans (mul_le_mul_of_nonneg_left hpow hCyn)
  have hZNP : qGoodZ n N u ≤ qGoodCz n * NP := by
    have hpow : (B.L N : ℝ) ^ (n + 1) ≤ NP := by
      dsimp [NP]
      exact pow_le_pow_left₀ (by positivity) hLleN _
    exact hZL.trans (mul_le_mul_of_nonneg_left hpow hCzn)
  have hH : qGoodH N u τ = Real.exp (-(RBM.cZero * K)) := by
    have hcancel : RBM.cZero * (B.ell N u * K) / B.ell N u = RBM.cZero * K := by
      field_simp [hellpos.ne']
    unfold qGoodH
    rw [hcancel]
  have hHle : qGoodH N u τ ≤ 1 := by
    rw [hH]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg RBM.cZero_pos.le hK0)
  have h1XK : 1 + qGoodX n N u τ ≤ (1 + qGoodCx n) * K ^ (n + 1) := by
    calc
      1 + qGoodX n N u τ ≤ 1 + qGoodCx n * K ^ (n + 1) := add_le_add le_rfl hXK
      _ ≤ (1 + qGoodCx n) * K ^ (n + 1) := by nlinarith [hKpow1, hCxn]
  have h1YK : 1 + qGoodY n N u τ ≤ (1 + qGoodCy n) * K ^ (n + 1) := by
    calc
      1 + qGoodY n N u τ ≤ 1 + qGoodCy n * K ^ (n + 1) := add_le_add le_rfl hYK
      _ ≤ (1 + qGoodCy n) * K ^ (n + 1) := by nlinarith [hKpow1, hCyn]
  have hmainK : 1 + (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) ≤
      qGoodMainCoeff n * (K ^ (n + 1)) ^ 2 := by
    have h1X0 : 0 ≤ 1 + qGoodX n N u τ := by positivity
    have h1Y0 : 0 ≤ 1 + qGoodY n N u τ := by positivity
    have hCY0 : 0 ≤ (1 + qGoodCy n) * K ^ (n + 1) := by positivity
    have hprod : (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) ≤
        ((1 + qGoodCy n) * K ^ (n + 1)) * ((1 + qGoodCx n) * K ^ (n + 1)) :=
      mul_le_mul h1YK h1XK h1X0 hCY0
    have hKsq : 1 ≤ (K ^ (n + 1)) ^ 2 := by nlinarith [hKpow1]
    have hCprod : 0 ≤ (1 + qGoodCx n) * (1 + qGoodCy n) := by positivity
    unfold qGoodMainCoeff
    calc
      1 + (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) ≤
          1 + ((1 + qGoodCy n) * (1 + qGoodCx n)) * (K ^ (n + 1)) ^ 2 := by
        calc
          _ ≤ 1 + (((1 + qGoodCy n) * K ^ (n + 1)) *
              ((1 + qGoodCx n) * K ^ (n + 1))) :=
            add_le_add_right hprod 1
          _ = _ := by ring
      _ ≤ (1 + (1 + qGoodCx n) * (1 + qGoodCy n)) * (K ^ (n + 1)) ^ 2 := by
        calc
          _ ≤ (K ^ (n + 1)) ^ 2 +
              ((1 + qGoodCx n) * (1 + qGoodCy n)) * (K ^ (n + 1)) ^ 2 := by
            calc
              _ = 1 + ((1 + qGoodCy n) * (1 + qGoodCx n)) *
                  (K ^ (n + 1)) ^ 2 := by ring
              _ ≤ (K ^ (n + 1)) ^ 2 +
                  ((1 + qGoodCy n) * (1 + qGoodCx n)) * (K ^ (n + 1)) ^ 2 :=
                add_le_add_left hKsq _
              _ = _ := by ring
          _ = _ := by ring
  have hLpowN : (B.L N : ℝ) ^ (n + 1) ≤ NP := by
    dsimp [NP]
    exact pow_le_pow_left₀ (by positivity) hLleN _
  have hKpowN : K ^ (n + 1) ≤ NP := by
    dsimp [K, NP]
    exact pow_le_pow_left₀ (by positivity) hKleN _
  have hExp : qGoodZ n N u * qGoodX n N u τ * qGoodH N u τ ≤
      qGoodExpCoeff n * (B.L N : ℝ) ^ (n + 1) * K ^ (n + 1) *
        Real.exp (-(RBM.cZero * K)) := by
    rw [hH]
    unfold qGoodExpCoeff
    calc
      qGoodZ n N u * qGoodX n N u τ * Real.exp (-(RBM.cZero * K)) ≤
          ((RBM.cTwo52 ^ (n + 1)) * (B.L N : ℝ) ^ (n + 1)) *
            (qGoodCx n * K ^ (n + 1)) * Real.exp (-(RBM.cZero * K)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hZL hXK hX0 (by positivity)) (by positivity)
      _ = _ := by unfold qGoodCz; ring
  have htotal :
      1 + (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) +
        qGoodZ n N u * qGoodX n N u τ * qGoodH N u τ +
        qGoodZ n N u * (2 + qGoodY n N u τ) +
        qGoodZ n N u ^ 2 * (1 + qGoodH N u τ) ≤
      qGoodTotalCoeff n * NP ^ 2 := by
    have h1XN : 1 + qGoodX n N u τ ≤ (1 + qGoodCx n) * NP := by
      calc
        1 + qGoodX n N u τ ≤ 1 + qGoodCx n * NP := add_le_add le_rfl hXNP
        _ ≤ (1 + qGoodCx n) * NP := by
          calc
            _ ≤ NP + qGoodCx n * NP :=
              add_le_add_left hNP1 (qGoodCx n * NP)
            _ = _ := by ring
    have h1YN : 1 + qGoodY n N u τ ≤ (1 + qGoodCy n) * NP := by
      calc
        1 + qGoodY n N u τ ≤ 1 + qGoodCy n * NP := add_le_add le_rfl hYNP
        _ ≤ (1 + qGoodCy n) * NP := by
          calc
            _ ≤ NP + qGoodCy n * NP :=
              add_le_add_left hNP1 (qGoodCy n * NP)
            _ = _ := by ring
    have h2YN : 2 + qGoodY n N u τ ≤ (2 + qGoodCy n) * NP := by
      calc
        2 + qGoodY n N u τ ≤ 2 + qGoodCy n * NP := add_le_add le_rfl hYNP
        _ ≤ (2 + qGoodCy n) * NP := by
          calc
            _ ≤ 2 * NP + qGoodCy n * NP :=
              add_le_add_left (by nlinarith [hNP1]) (qGoodCy n * NP)
            _ = _ := by ring
    have htermMain : (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) ≤
        (1 + qGoodCy n) * (1 + qGoodCx n) * NP ^ 2 := by
      calc
        _ ≤ ((1 + qGoodCy n) * NP) * ((1 + qGoodCx n) * NP) :=
          mul_le_mul h1YN h1XN (by positivity) (by positivity)
        _ = _ := by ring
    have htermExp : qGoodZ n N u * qGoodX n N u τ * qGoodH N u τ ≤
        qGoodExpCoeff n * NP ^ 2 := by
      have hH0 : 0 ≤ qGoodH N u τ := by rw [hH]; positivity
      have hpow : (B.L N : ℝ) ^ (n + 1) * K ^ (n + 1) ≤ NP * NP :=
        mul_le_mul hLpowN hKpowN (by positivity) (by positivity)
      have hexp1 : Real.exp (-(RBM.cZero * K)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg RBM.cZero_pos.le hK0)
      have hcoef0 : 0 ≤ qGoodExpCoeff n := by unfold qGoodExpCoeff; positivity
      calc
        _ ≤ qGoodCz n * (B.L N : ℝ) ^ (n + 1) *
            (qGoodCx n * K ^ (n + 1)) * qGoodH N u τ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul hZL hXK hX0 (by positivity)) hH0
        _ ≤ qGoodExpCoeff n * NP ^ 2 := by
              rw [hH]
              calc
                _ = qGoodExpCoeff n *
                    ((B.L N : ℝ) ^ (n + 1) * K ^ (n + 1)) *
                    Real.exp (-(RBM.cZero * K)) := by
                      unfold qGoodExpCoeff
                      ring
                _ ≤ qGoodExpCoeff n * (NP * NP) *
                    Real.exp (-(RBM.cZero * K)) := by
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hpow hcoef0) (Real.exp_nonneg _)
                _ ≤ qGoodExpCoeff n * (NP * NP) * 1 := by
                      exact mul_le_mul_of_nonneg_left hexp1
                        (by positivity)
                _ = _ := by ring
    have htermZY : qGoodZ n N u * (2 + qGoodY n N u τ) ≤
        qGoodCz n * (2 + qGoodCy n) * NP ^ 2 := by
      calc
        _ ≤ (qGoodCz n * NP) * ((2 + qGoodCy n) * NP) :=
          mul_le_mul hZNP h2YN (by positivity) (by positivity)
        _ = _ := by ring
    have htermZ2 : qGoodZ n N u ^ 2 * (1 + qGoodH N u τ) ≤
        2 * qGoodCz n ^ 2 * NP ^ 2 := by
      have hH0 : 0 ≤ qGoodH N u τ := by rw [hH]; positivity
      have hzsq : qGoodZ n N u ^ 2 ≤ (qGoodCz n * NP) ^ 2 :=
        pow_le_pow_left₀ hZ0 hZNP 2
      have h1H : 1 + qGoodH N u τ ≤ 2 := by linarith [hHle]
      calc
        _ ≤ (qGoodCz n * NP) ^ 2 * 2 :=
          mul_le_mul hzsq h1H (add_nonneg (by norm_num) hH0)
            (sq_nonneg (qGoodCz n * NP))
        _ = _ := by ring
    have hNPsq1 : 1 ≤ NP ^ 2 := one_le_pow₀ hNP1
    have hmainNP : 1 + (1 + qGoodY n N u τ) * (1 + qGoodX n N u τ) ≤
        qGoodMainCoeff n * NP ^ 2 := by
      have hprod := htermMain
      unfold qGoodMainCoeff
      calc
        _ ≤ 1 + ((1 + qGoodCy n) * (1 + qGoodCx n)) * NP ^ 2 :=
          add_le_add_right hprod 1
        _ ≤ _ := by
          calc
            _ ≤ NP ^ 2 + ((1 + qGoodCy n) * (1 + qGoodCx n)) * NP ^ 2 := by
              exact add_le_add_left hNPsq1
                (((1 + qGoodCy n) * (1 + qGoodCx n)) * NP ^ 2)
            _ = _ := by ring
    calc
      _ ≤ qGoodMainCoeff n * NP ^ 2 + qGoodExpCoeff n * NP ^ 2 +
          qGoodCz n * (2 + qGoodCy n) * NP ^ 2 +
          2 * qGoodCz n ^ 2 * NP ^ 2 := by
        linarith [hmainNP, htermExp, htermZY, htermZ2]
      _ = qGoodTotalCoeff n * NP ^ 2 := by
        unfold qGoodTotalCoeff qGoodExpCoeff
        ring
  simpa [K, NP, B, d] using ⟨hmainK, hExp, htotal⟩

set_option maxHeartbeats 0 in
private theorem goodBound_le_smallLoss_profile {n N : ℕ} {u τ D : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hN : 1 ≤ (N : ℝ))
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ)) :
    (B.scale 0 N u) ^ (2 * (n + 2)) *
        (eeGoodBound n N u τ D + qqGoodBound n N u τ D) ≤
      qGoodMainCoeff n * qGoodEeCoeff n * ((N : ℝ) ^ τ) ^ (2 * n + 3) +
        qGoodExpCoeff n * qGoodEeCoeff n * (B.L N : ℝ) ^ (n + 1) *
          ((N : ℝ) ^ τ) ^ (n + 2) * Real.exp (-(RBM.cZero * (N : ℝ) ^ τ)) +
        qGoodTotalCoeff n * (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
          (N : ℝ) ^ (((4 * n + 7 : ℕ) : ℝ) - D) := by
  let K : ℝ := (N : ℝ) ^ τ
  let NP : ℝ := (N : ℝ) ^ (n + 1)
  let U : ℝ := (B.scale 0 N u) ^ (2 * (n + 2))
  let X : ℝ := qGoodX n N u τ
  let Y : ℝ := qGoodY n N u τ
  let Z : ℝ := qGoodZ n N u
  let H : ℝ := qGoodH N u τ
  let M : ℝ := (1 + Y) * (1 + X)
  let E : ℝ := Z * X * H
  let R : ℝ := Z * (2 + Y) + Z ^ 2 * (1 + H)
  let S : ℝ := 1 + M + E + R
  let δ : ℝ := qGoodDelta n N D
  have hK1 : 1 ≤ K := by dsimp [K]; exact Real.one_le_rpow hN hτ.le
  have hCoeff := qGood_coeff_bounds (n := n) (N := N) hu hN hτ hτ1 hWL
  have hMain : 1 + M ≤ qGoodMainCoeff n * (K ^ (n + 1)) ^ 2 := by
    simpa [M, X, Y, K] using hCoeff.1
  have hExp : E ≤ qGoodExpCoeff n * (B.L N : ℝ) ^ (n + 1) *
      K ^ (n + 1) * Real.exp (-(RBM.cZero * K)) := by
    simpa [E, Z, X, H, K] using hCoeff.2.1
  have hTotal : S ≤ qGoodTotalCoeff n * NP ^ 2 := by
    simpa [S, M, E, R, X, Y, Z, H, NP, K, add_assoc] using hCoeff.2.2
  have hEe := eeGoodBound_scaled_le (n := n) (N := N) (u := u) (τ := τ) (D := D)
    hu hK1
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have hScale0 : 0 ≤ B.scale 0 N u :=
    (B.scale_pos' (by norm_num) N hu.1 hu1).le
  have hU0 : 0 ≤ U := by dsimp [U]; exact pow_nonneg hScale0 _
  have hδ0 : 0 ≤ δ := by dsimp [δ, qGoodDelta]; positivity
  have hEeCoeff0 : 0 ≤ qGoodEeCoeff n := by unfold qGoodEeCoeff; positivity
  have hexpPos : 0 < Real.exp 1 := Real.exp_pos 1
  have hCxn : 0 ≤ qGoodCx n := by
    unfold qGoodCx
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le) RBM.cTwo52_pos.le
  have hCyn : 0 ≤ qGoodCy n := by
    unfold qGoodCy
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le) RBM.cTwo52_pos.le
  have hCzn : 0 ≤ qGoodCz n := by
    unfold qGoodCz
    exact pow_nonneg RBM.cTwo52_pos.le _
  have hMainCoeff0 : 0 ≤ qGoodMainCoeff n := by
    unfold qGoodMainCoeff
    positivity
  have hExpCoeff0 : 0 ≤ qGoodExpCoeff n := mul_nonneg hCzn hCxn
  have hTotalCoeff0 : 0 ≤ qGoodTotalCoeff n := by
    unfold qGoodTotalCoeff
    exact add_nonneg (add_nonneg (add_nonneg hMainCoeff0 hExpCoeff0)
      (mul_nonneg hCzn (by positivity))) (mul_nonneg (by norm_num) (sq_nonneg (qGoodCz n)))
  have hCeK0 : 0 ≤ qGoodEeCoeff n * K := mul_nonneg hEeCoeff0 (by positivity)
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK1
  have hellpos : 0 < B.ell N u := by
    change 0 < ellHat (B.L N) ((u : ℝ) : ℂ)
    exact lt_of_lt_of_le (by norm_num)
      (half_le_ellHat_real (B.L N) (by have := B.three_le_L N; omega)
        hu.1 hu1)
  have hX0 : 0 ≤ X := by
    dsimp [X, qGoodX]
    apply mul_nonneg
    · apply pow_nonneg
      exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le)
        (add_nonneg (mul_nonneg hellpos.le hK0) (by norm_num))
    · apply pow_nonneg
      exact div_nonneg RBM.cTwo52_pos.le hellpos.le
  have hY0 : 0 ≤ Y := by
    dsimp [Y, qGoodY]
    apply mul_nonneg
    · apply pow_nonneg
      exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le)
        (add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hellpos.le hK0)) (by norm_num))
    · apply pow_nonneg
      exact div_nonneg RBM.cTwo52_pos.le hellpos.le
  have hZ0 : 0 ≤ Z := by
    dsimp [Z, qGoodZ]
    apply mul_nonneg
    · positivity
    · apply pow_nonneg
      exact div_nonneg RBM.cTwo52_pos.le hellpos.le
  have hH0 : 0 ≤ H := by dsimp [H, qGoodH]; positivity
  have hME0 : 0 ≤ 1 + M + E := by dsimp [M, E]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hUδ0 : 0 ≤ U * δ := mul_nonneg hU0 hδ0
  have hScaleDelta := qGoodScaleDelta_le (n := n) (N := N) (u := u) (D := D)
    hu hN hWL
  have hSplit : U * (eeGoodBound n N u τ D + qqGoodBound n N u τ D) ≤
      (1 + M + E) * (qGoodEeCoeff n * K) + S * (U * δ) := by
    calc
      _ = (1 + M + E) * (U * eeGoodBound n N u τ D) + R * (U * δ) := by
        rw [qqGoodBound_expand]
        dsimp [U, M, E, R, X, Y, Z, H, δ]
        ring
      _ ≤ (1 + M + E) * (qGoodEeCoeff n * K + U * δ) + R * (U * δ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by simpa [U, δ, K] using hEe) hME0) le_rfl
      _ = (1 + M + E) * (qGoodEeCoeff n * K) + S * (U * δ) := by
        dsimp [S]
        ring
  have hFactor : (1 + M + E) * (qGoodEeCoeff n * K) ≤
      qGoodMainCoeff n * qGoodEeCoeff n * K ^ (2 * n + 3) +
        qGoodExpCoeff n * qGoodEeCoeff n * (B.L N : ℝ) ^ (n + 1) *
          K ^ (n + 2) * Real.exp (-(RBM.cZero * K)) := by
    have hKMain : (K ^ (n + 1)) ^ 2 * K = K ^ (2 * n + 3) := by
      calc
        _ = K ^ ((n + 1) * 2 + 1) := by rw [← pow_mul, ← pow_succ]
        _ = K ^ (2 * n + 3) := by congr 1 <;> omega
    have hKExp : K ^ (n + 1) * K = K ^ (n + 2) := by
      calc
        _ = K ^ ((n + 1) + 1) := by rw [← pow_succ]
        _ = K ^ (n + 2) := by congr 1 <;> omega
    calc
      _ = (1 + M) * (qGoodEeCoeff n * K) + E * (qGoodEeCoeff n * K) := by ring
      _ ≤ (qGoodMainCoeff n * (K ^ (n + 1)) ^ 2) *
            (qGoodEeCoeff n * K) +
          (qGoodExpCoeff n * (B.L N : ℝ) ^ (n + 1) * K ^ (n + 1) *
            Real.exp (-(RBM.cZero * K))) * (qGoodEeCoeff n * K) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hMain hCeK0)
          (mul_le_mul_of_nonneg_right hExp hCeK0)
      _ = _ := by
        calc
          _ = qGoodMainCoeff n * qGoodEeCoeff n *
              ((K ^ (n + 1)) ^ 2 * K) +
            qGoodExpCoeff n * qGoodEeCoeff n * (B.L N : ℝ) ^ (n + 1) *
              (K ^ (n + 1) * K) * Real.exp (-(RBM.cZero * K)) := by ring
          _ = _ := by rw [hKMain, hKExp]
  have hNPpow : NP ^ 2 = (N : ℝ) ^ (2 * (n + 1)) := by
    dsimp [NP]
    calc
      _ = (N : ℝ) ^ ((n + 1) * 2) := by rw [← pow_mul]
      _ = (N : ℝ) ^ (2 * (n + 1)) := by congr 1 <;> omega
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN
  have hErrPow : NP ^ 2 * (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1 - D) =
      (N : ℝ) ^ (((4 * n + 7 : ℕ) : ℝ) - D) := by
    rw [hNPpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have hError : S * (U * δ) ≤
      qGoodTotalCoeff n * (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
        (N : ℝ) ^ (((4 * n + 7 : ℕ) : ℝ) - D) := by
    calc
      _ ≤ (qGoodTotalCoeff n * NP ^ 2) * (U * δ) :=
        mul_le_mul_of_nonneg_right hTotal hUδ0
      _ ≤ (qGoodTotalCoeff n * NP ^ 2) *
          ((2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
            (N : ℝ) ^ ((2 * (n + 2) : ℝ) + 1 - D)) :=
        mul_le_mul_of_nonneg_left hScaleDelta
          (mul_nonneg hTotalCoeff0 (sq_nonneg NP))
      _ = _ := by rw [← hErrPow]; ring
  calc
    _ ≤ (1 + M + E) * (qGoodEeCoeff n * K) + S * (U * δ) := hSplit
    _ ≤ qGoodMainCoeff n * qGoodEeCoeff n * K ^ (2 * n + 3) +
          qGoodExpCoeff n * qGoodEeCoeff n * (B.L N : ℝ) ^ (n + 1) *
            K ^ (n + 2) * Real.exp (-(RBM.cZero * K)) +
          qGoodTotalCoeff n * (2 : ℝ) ^ (2 * (n + 2)) * (n + 2) *
            (N : ℝ) ^ (((4 * n + 7 : ℕ) : ℝ) - D) :=
      add_le_add hFactor hError
    _ = _ := by simpa [K, B, d]

private theorem qvEnvelope_le_goodBound {n N : ℕ} {u τ D : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hτ : 0 < τ) (hD : 0 < D)
    (hN1 : 1 ≤ N) (hNτ : 1 ≤ (N : ℝ) ^ τ) (hscale1 : 1 ≤ B.scale 0 N u)
    (q : LoopData (B.L N) (n + 2)) (ω : Gauss.Ω d)
    (hdec : Decay.LoopDecay (B.L N) (2 * (n + 2) + 2)
      (B.ell N u * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
      (gloop (B.L N) (B.W N) ((Gauss.sample d).H N u ω) (zt 0 u))) :
    qvEnvelope n N u q ω ≤ (B.scale 0 N u) ^ (2 * (n + 2)) *
      (eeGoodBound n N u τ D + qqGoodBound n N u τ D) := by
  classical
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have heta : etaT 0 u = 1 - u := by rw [Step2.etaT_eq, mE_zero]; norm_num
  have heta0 : 0 < etaT 0 u := by rw [heta]; linarith
  have hellhalf : 1 / 2 ≤ B.ell N u := by
    change 1 / 2 ≤ ellHat (B.L N) ((u : ℝ) : ℂ)
    exact half_le_ellHat_real (B.L N) (B.three_le_L N) hu0 hu1
  have hellpos : 0 < B.ell N u := lt_of_lt_of_le (by norm_num) hellhalf
  have hKpos : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) _
  have hK1 : 1 ≤ (N : ℝ) ^ τ := hNτ
  have hδ0 : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
  have hXi := xiL_first_half_le_two_pow (m := 2 * (n + 2) + 2) (N := N) (by omega) hu ω
  have hmain :
      2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
          ((B.scale 0 N u)⁻¹ ^ (2 * (n + 2)) * (etaT 0 u)⁻¹ *
            (Gauss.sample d).xiL 0 N u ω (2 * (n + 2) + 2))
        ≤ 2 * exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2) *
          ((B.scale 0 N u)⁻¹ ^ (2 * (n + 2)) * (etaT 0 u)⁻¹ *
            (2 : ℝ) ^ (2 * (n + 2) + 2)) := by
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left hXi
      positivity
    · positivity
  have hEE : ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)),
      ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ ≤ eeGoodBound n N u τ D := by
    intro b
    have hEEb := EEBridge.norm_eeField_le (Gauss.sample d) (E := 0) (n := n) (N := N)
      (u := u) (ω := ω) q.1 b hNτ hscale1 heta0 hellhalf hdec
    rw [← MomentDuhamel.eeFun_H] at hEEb
    unfold eeGoodBound
    dsimp [eeGoodBound] at hEEb ⊢
    exact hEEb.trans (add_le_add hmain le_rfl)
  have hdecEE : FastDecay (B.L N) (B.ell N u * (N : ℝ) ^ τ)
      ((B.W N : ℝ) * (n + 2) * ((B.L N : ℝ) * (N : ℝ) ^ (-D)))
      (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) := by
    simpa [B, d] using FastDecayFlow.fastDecay_eeFun B 0 N u
      ((Gauss.sample d).hermitian N u ω) q.1 hdec
  have hQQ : ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)),
      ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
        (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖ ≤ qqGoodBound n N u τ D := by
    intro b
    have hRpos : 0 < B.ell N u * (N : ℝ) ^ τ := mul_pos hellpos hKpos
    have he0 : 0 ≤ eeGoodBound n N u τ D := by
      unfold eeGoodBound
      positivity
    have hδpos : 0 ≤ (B.W N : ℝ) * (n + 2) *
        ((B.L N : ℝ) * (N : ℝ) ^ (-D)) := by positivity
    have hraw := norm_QQ_le_twoProjection (L := B.L N) (k := n + 1) (u := u)
      (R := B.ell N u * (N : ℝ) ^ τ) (e := eeGoodBound n N u τ D)
      (δ := (B.W N : ℝ) * (n + 2) * ((B.L N : ℝ) * (N : ℝ) ^ (-D)))
      (B.three_le_L N) hu0 hu1 hRpos he0 hδpos hEE hdecEE b
    simpa [qqGoodBound, Band.ell, B, d] using hraw
  have hsup : Finset.univ.sup' Finset.univ_nonempty
      (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
          ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖)
      ≤ eeGoodBound n N u τ D + qqGoodBound n N u τ D := by
    apply Finset.sup'_le
    intro b hb
    exact add_le_add (hEE b) (hQQ b)
  simp only [qvEnvelope, if_pos hu]
  exact mul_le_mul_of_nonneg_left hsup (pow_nonneg (B.scale_pos' (by norm_num) N hu0 hu1).le _)

/-- The exact first-half event estimate delivered by the actual all-charge loop-decay source.
The statement is uniform in the time and the actual loop charge; only the pointwise scalar
power-counting absorption remains separate. -/
theorem eventually_qvEnvelope_le_goodBound {n : ℕ} {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
        ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
          ∀ q : LoopData (B.L N) (n + 2),
            qvEnvelope n N u q ω ≤ (B.scale 0 N u) ^ (2 * (n + 2)) *
              (eeGoodBound n N u τ D + qqGoodBound n N u τ D) := by
  have hdecEv := Lemma514FirstCellLKDecay.eventually_loopDecay_pair_on_first_half_good
    (2 * (n + 2) + 2) (by omega) hτ hD
  have hWlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ B.W N := by
    simpa [B, d, Dims.exampleGrow_W] using Dims.tendsto_growW.eventually_ge_atTop 2
  filter_upwards [hdecEv, hWlarge, B.dim, eventually_ge_atTop 1] with
    N hdec hW hdim hN ω hω u hu q
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
  have heta : etaT 0 u = 1 - u := by rw [Step2.etaT_eq, mE_zero]; norm_num
  have hetaHalf : (1 / 2 : ℝ) ≤ etaT 0 u := by rw [heta]; linarith [hu.2]
  have hell : 1 ≤ B.ell N u := by
    change 1 ≤ ellHat (B.L N) ((u : ℝ) : ℂ)
    exact one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega) hu0 hu1
  have hWreal : (2 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast hW
  have hscale1 : 1 ≤ B.scale 0 N u := by
    change 1 ≤ (B.W N : ℝ) * B.ell N u * etaT 0 u
    nlinarith [mul_le_mul hWreal hell (by norm_num) (by norm_num), hetaHalf]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNτ : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hpair := hdec ω hω u hu
  exact qvEnvelope_le_goodBound hu hτ hD hN hNτ hscale1 q ω hpair.1

/-- For each requested loss, choose the decay scale after that loss.  The actual all-time
first-half good event then gives a uniform-in-time and uniform-in-charge deterministic bound. -/
theorem eventually_qvEnvelope_le_smallLoss {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
          ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
            ∀ q : LoopData (B.L N) (n + 2),
              qvEnvelope n N u q ω ≤ C * (N : ℝ) ^ ε := by
  let a : ℝ := ((2 * n + 3 : ℕ) : ℝ)
  let τ : ℝ := min (1 / 8) (ε / (2 * a))
  let D : ℝ := ((4 * n + 9 : ℕ) : ℝ)
  let Cmain : ℝ := qGoodMainCoeff n * qGoodEeCoeff n
  let Cexp : ℝ := qGoodExpCoeff n * qGoodEeCoeff n
  let Cerr : ℝ := qGoodTotalCoeff n * (2 : ℝ) ^ (2 * (n + 2)) * (n + 2)
  let C : ℝ := Cmain + 1 + Cerr
  have ha : 0 < a := by dsimp [a]; positivity
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    exact (min_le_left _ _).trans (by norm_num)
  have hτexp : τ * a ≤ ε / 2 := by
    dsimp [τ]
    calc
      min (1 / 8) (ε / (2 * a)) * a ≤ (ε / (2 * a)) * a :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) ha.le
      _ = ε / 2 := by field_simp [ha.ne']
  have hD : 0 < D := by dsimp [D]; positivity
  have hDexp : ((4 * n + 7 : ℕ) : ℝ) - D = -2 := by
    dsimp [D]
    push_cast
    ring
  have hexpPos : 0 < Real.exp 1 := Real.exp_pos 1
  have hCx : 0 ≤ qGoodCx n := by
    unfold qGoodCx
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le) RBM.cTwo52_pos.le
  have hCy : 0 ≤ qGoodCy n := by
    unfold qGoodCy
    apply pow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hexpPos.le) RBM.cTwo52_pos.le
  have hCz : 0 ≤ qGoodCz n := by
    unfold qGoodCz
    exact pow_nonneg RBM.cTwo52_pos.le _
  have hEe : 0 ≤ qGoodEeCoeff n := by unfold qGoodEeCoeff; positivity
  have hMain : 0 ≤ qGoodMainCoeff n := by unfold qGoodMainCoeff; positivity
  have hExp : 0 ≤ qGoodExpCoeff n := mul_nonneg hCz hCx
  have hTotal : 0 ≤ qGoodTotalCoeff n := by
    unfold qGoodTotalCoeff
    exact add_nonneg (add_nonneg (add_nonneg hMain hExp)
      (mul_nonneg hCz (by positivity))) (mul_nonneg (by norm_num) (sq_nonneg _))
  have hCmain : 0 ≤ Cmain := by dsimp [Cmain]; exact mul_nonneg hMain hEe
  have hCexp : 0 ≤ Cexp := by dsimp [Cexp]; exact mul_nonneg hExp hEe
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr]; positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hExpSmall := SumZeroDyn.eventually_exp_small Cexp
    (((n + 1 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) * τ)
    RBM.cZero RBM.cZero_pos hτ
  have hGoodBound := eventually_qvEnvelope_le_goodBound (n := n) hτ hD
  have hEventual : ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
        ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
          ∀ q : LoopData (B.L N) (n + 2),
            qvEnvelope n N u q ω ≤ C * (N : ℝ) ^ ε := by
    filter_upwards [hExpSmall, hGoodBound, B.dim, eventually_ge_atTop 1] with
      N hExpN hGoodN hdim hN ω hω u hu q
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hW1 : 1 ≤ (B.W N : ℝ) := by
      have h : 1 ≤ B.W N := by have := B.W_pos N; omega
      exact_mod_cast h
    have hL1 : 1 ≤ (B.L N : ℝ) := by
      have h : 1 ≤ B.L N := by have := B.three_le_L N; omega
      exact_mod_cast h
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hdim.1
    have hLleN : (B.L N : ℝ) ≤ (N : ℝ) := by
      calc
        (B.L N : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := by nlinarith [hW1, hL1]
        _ ≤ (N : ℝ) := hWL
    have hprofile := goodBound_le_smallLoss_profile (n := n) (N := N) (u := u)
      (τ := τ) (D := D) hu hNreal hτ hτ1 hWL
    have hPowerExp : ((N : ℝ) ^ τ) ^ (n + 2) =
        (N : ℝ) ^ (τ * ((n + 2 : ℕ) : ℝ)) :=
      SumZeroDyn.rpow_pow_eq N τ (n + 2)
    have hPowNat : (N : ℝ) ^ (n + 1) =
        (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast]
    have hPowerExpFull : (N : ℝ) ^ (n + 1) *
        ((N : ℝ) ^ τ) ^ (n + 2) =
        (N : ℝ) ^ (((n + 1 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) * τ) := by
      calc
        _ = (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) *
            (N : ℝ) ^ (τ * ((n + 2 : ℕ) : ℝ)) := by rw [hPowNat, hPowerExp]
        _ = (N : ℝ) ^ (((n + 1 : ℕ) : ℝ) +
            τ * ((n + 2 : ℕ) : ℝ)) := by
          rw [← Real.rpow_add (by linarith : 0 < (N : ℝ))]
        _ = _ := by congr 1 <;> ring
    have hPowerExpFullCast : (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) *
        ((N : ℝ) ^ τ) ^ (n + 2) =
        (N : ℝ) ^ (((n + 1 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) * τ) := by
      calc
        _ = (N : ℝ) ^ (n + 1) * ((N : ℝ) ^ τ) ^ (n + 2) := by rw [hPowNat]
        _ = _ := hPowerExpFull
    have hProfileExp : Cexp * (B.L N : ℝ) ^ (n + 1) *
          ((N : ℝ) ^ τ) ^ (n + 2) * Real.exp (-(RBM.cZero * (N : ℝ) ^ τ)) ≤ 1 := by
      calc
        _ ≤ Cexp * (N : ℝ) ^ (n + 1) *
            ((N : ℝ) ^ τ) ^ (n + 2) * Real.exp (-(RBM.cZero * (N : ℝ) ^ τ)) := by
          gcongr
        _ = Cexp * (N : ℝ) ^ (((n + 1 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) * τ) *
            Real.exp (-(RBM.cZero * (N : ℝ) ^ τ)) := by
          calc
            _ = Cexp * ((N : ℝ) ^ ((n + 1 : ℕ) : ℝ) *
                ((N : ℝ) ^ τ) ^ (n + 2)) *
                Real.exp (-(RBM.cZero * (N : ℝ) ^ τ)) := by
              rw [hPowNat]
              ac_rfl
            _ = _ := by rw [hPowerExpFullCast]
        _ ≤ 1 := hExpN
    have hPowerMain : ((N : ℝ) ^ τ) ^ (2 * n + 3) ≤ (N : ℝ) ^ ε := by
      rw [SumZeroDyn.rpow_pow_eq N τ (2 * n + 3)]
      exact Real.rpow_le_rpow_of_exponent_le hNreal
        (by dsimp [a] at hτexp; nlinarith)
    have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNreal hε.le
    have hNneg2 : (N : ℝ) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hNreal (by norm_num)
    have hMainTerm : Cmain * ((N : ℝ) ^ τ) ^ (2 * n + 3) ≤
        Cmain * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left hPowerMain hCmain
    have hErrTerm : Cerr * (N : ℝ) ^ (((4 * n + 7 : ℕ) : ℝ) - D) ≤ Cerr := by
      rw [hDexp]
      simpa using mul_le_mul_of_nonneg_left hNneg2 hCerr
    have hGoodPoint := hGoodN ω hω u hu q
    calc
      qvEnvelope n N u q ω ≤ (B.scale 0 N u) ^ (2 * (n + 2)) *
          (eeGoodBound n N u τ D + qqGoodBound n N u τ D) := hGoodPoint
      _ ≤ Cmain * ((N : ℝ) ^ τ) ^ (2 * n + 3) +
            Cexp * (B.L N : ℝ) ^ (n + 1) * ((N : ℝ) ^ τ) ^ (n + 2) *
              Real.exp (-(RBM.cZero * (N : ℝ) ^ τ)) +
            Cerr * (N : ℝ) ^ (((4 * n + 7 : ℕ) : ℝ) - D) := hprofile
      _ ≤ Cmain * (N : ℝ) ^ ε + 1 + Cerr := by
        exact add_le_add (add_le_add hMainTerm hProfileExp) hErrTerm
      _ ≤ C * (N : ℝ) ^ ε := by
        dsimp [C]
        nlinarith [hNε, hCmain, hCerr]
  exact ⟨τ, hτ, hτ1, C, hC, hEventual⟩

private theorem qvEnvelope_continuous {n N : ℕ} (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) :
    Continuous (qvEnvelope n N u q) := by
  classical
  by_cases hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)
  · unfold qvEnvelope
    simp only [if_pos hu]
    apply continuous_const.mul
    exact Continuous.finset_sup'_apply Finset.univ_nonempty fun b _ =>
      (eeFun_continuous u hu.1 (hu.2.trans_lt (by norm_num)) q.1 b).norm.add
        (qq_eeFun_continuous u hu.1 (hu.2.trans_lt (by norm_num)) q.1 b).norm
  · unfold qvEnvelope
    simp only [if_neg hu]
    exact continuous_const

private theorem qvEnvelope_nonneg {n N : ℕ} {u : ℝ}
    (q : LoopData (B.L N) (n + 2)) (ω : Gauss.Ω d) :
    0 ≤ qvEnvelope n N u q ω := by
  classical
  by_cases hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)
  · simp only [qvEnvelope, if_pos hu]
    have hscale : 0 ≤ B.scale 0 N u :=
      (B.scale_pos' (by norm_num) N hu.1 (hu.2.trans_lt (by norm_num))).le
    have hb : 0 ≤ (Finset.univ.sup' Finset.univ_nonempty
        (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
          ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
            ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖)) := by
      let b : LoopArg (B.L N) ((n + 2) + (n + 2)) := default
      have hsup :
          ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
            ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖ ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
              ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
                ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
                  (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖) := by
        exact Finset.le_sup' (fun c : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
          ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 c‖ +
            ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) c‖)
          (Finset.mem_univ b)
      exact le_trans (add_nonneg (norm_nonneg _) (norm_nonneg _)) hsup
    exact mul_nonneg (pow_nonneg hscale _) hb
  · unfold qvEnvelope
    simp only [if_neg hu]
    exact le_rfl

private theorem qvEnvelope_le_detEnvelopeBound {n N : ℕ} {u : ℝ}
    (q : LoopData (B.L N) (n + 2)) (ω : Gauss.Ω d) :
    qvEnvelope n N u q ω ≤ detEnvelopeBound n N u := by
  classical
  by_cases hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)
  · have hu1 : u < 1 := hu.2.trans_lt (by norm_num)
    have hη : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have him : (1 / 2 : ℝ) ≤ |(zt 0 u).im| := by
      have hzt : (zt 0 u).im = 1 - u := by
        rw [zt_im, mE_zero]
        norm_num
      rw [hzt, abs_of_nonneg (by linarith : 0 ≤ 1 - u)]
      linarith [hu.2]
    have hscale : 0 ≤ B.scale 0 N u :=
      (B.scale_pos' (by norm_num) N hu.1 hu1).le
    have hee : ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)),
        ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ ≤ eeDetBound n N := by
      intro b
      have h := norm_eeFun_herm_le d N 0 hη him
        (Gauss.Hflow_isHermitian d N u ω) q.1 b
      change ‖MomentDuhamel.eeFun (Gauss.band d) 0 N u
        (Gauss.Hflow d N u ω) q.1 b‖ ≤ _
      exact h
    have hqq : ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)),
        ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
          (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖ ≤ qqDetBound n N := by
      intro b
      simpa [B, d, qqDetBound] using norm_QQ_ofReal_le_of_bdd (B.L N) (k := n + 1)
        (d.three_le_L N) hu.1 hu1 _ hee b
    have hmax : Finset.univ.sup' Finset.univ_nonempty
        (fun b : LoopArg (B.L N) ((n + 2) + (n + 2)) =>
          ‖MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1 b‖ +
            ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
              (MomentDuhamel.eeFun B 0 N u ((Gauss.sample d).H N u ω) q.1) b‖)
        ≤ eeDetBound n N + qqDetBound n N := by
      apply Finset.sup'_le
      intro b hb
      exact add_le_add (hee b) (hqq b)
    simp only [qvEnvelope, if_pos hu, detEnvelopeBound, abs_of_nonneg hscale]
    exact mul_le_mul_of_nonneg_left hmax (pow_nonneg hscale _)
  · unfold qvEnvelope
    simp only [if_neg hu]
    exact detEnvelopeBound_nonneg n N u

private theorem detEnvelopeBound_le_polynomial {n N : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hN : 1 ≤ (N : ℝ))
    (hdim : B.W N * B.L N ≤ N) :
    detEnvelopeBound n N u ≤
      (5 * ((n + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ (4 * (n + 2) + 2)) * (N : ℝ) ^ (4 * n + 7) := by
  let W : ℝ := (B.W N : ℝ)
  let L : ℝ := (B.L N : ℝ)
  let r : ℕ := 2 * (n + 2)
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact_mod_cast (show 1 ≤ B.W N by have := B.W_pos N; omega)
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast (show 1 ≤ B.L N by have := B.three_le_L N; omega)
  have hWL : W * L ≤ (N : ℝ) := by
    dsimp [W, L]
    exact_mod_cast hdim
  have hWleN : W ≤ (N : ℝ) := by
    nlinarith [hWL, hL1]
  have hLleN : L ≤ (N : ℝ) := by
    nlinarith [hWL, hW1]
  have hWinv : W⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < W)).2 hW1
  have hWinvPow : (W⁻¹) ^ (r + 1) ≤ 1 := by
    calc
      (W⁻¹) ^ (r + 1) ≤ (1 : ℝ) ^ (r + 1) :=
        pow_le_pow_left₀ (by positivity) hWinv _
      _ = 1 := by simp
  haveI : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  have hZmod : (Fintype.card (ZMod (B.L N)) : ℝ) = L := by
    dsimp [L]
    norm_cast
    exact ZMod.card (B.L N)
  have hEeEq : eeDetBound n N =
      ((n + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ (2 * (n + 2) + 2) * (W * L) * (W⁻¹) ^ (r + 1) := by
    unfold eeDetBound
    rw [hZmod]
    norm_num
    dsimp [r, W, L]
    ring
  have hEe : eeDetBound n N ≤
      (((n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (n + 2) + 2)) * (N : ℝ) := by
    rw [hEeEq]
    have hCoeff : 0 ≤ ((n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (n + 2) + 2) := by positivity
    calc
      _ ≤ (((n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (n + 2) + 2)) *
          (N : ℝ) * 1 := by
            gcongr
      _ = _ := by ring
  have hEe0 : 0 ≤ eeDetBound n N := eeDetBound_nonneg n N
  have hCardNat : Fintype.card (LoopArg (B.L N) (n + 1)) =
      (B.L N) ^ (n + 1) := by
    simpa only [Finset.card_univ] using
      (RBM.card_loopArg (L := B.L N) (n := n + 1))
  have hLnat : B.L N ≤ N := by
    have hWLnat : B.W N * B.L N ≤ N := hdim
    have hWnat : 1 ≤ B.W N := by have := B.W_pos N; omega
    have hmul : B.L N ≤ B.W N * B.L N := by
      calc
        B.L N = 1 * B.L N := by simp
        _ ≤ B.W N * B.L N := Nat.mul_le_mul_right _ hWnat
    exact hmul.trans hWLnat
  have hCard : (Fintype.card (LoopArg (B.L N) (n + 1)) : ℝ) ≤
      (N : ℝ) ^ (n + 1) := by
    rw [hCardNat]
    exact_mod_cast (Nat.pow_le_pow_left hLnat (n + 1))
  have hNPow1 : 1 ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hN
  have hCardFactor :
      (1 + (Fintype.card (LoopArg (B.L N) (n + 1)) : ℝ)) ^ 2 ≤
        4 * (N : ℝ) ^ (2 * (n + 1)) := by
    have hSum : 1 + (Fintype.card (LoopArg (B.L N) (n + 1)) : ℝ) ≤
        2 * (N : ℝ) ^ (n + 1) := by nlinarith [hCard, hNPow1]
    calc
      _ ≤ (2 * (N : ℝ) ^ (n + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hSum 2
      _ = 4 * (N : ℝ) ^ (2 * (n + 1)) := by
        rw [mul_pow]
        norm_num
        rw [← pow_mul]
        congr 1
        omega
  have hCardPow1 : 1 ≤ (N : ℝ) ^ (2 * (n + 1)) :=
    one_le_pow₀ hN
  have hQFactor :
      1 + (1 + (Fintype.card (LoopArg (B.L N) (n + 1)) : ℝ)) ^ 2 ≤
        5 * (N : ℝ) ^ (2 * (n + 1)) := by
    nlinarith [hCardFactor, hCardPow1]
  have hInner : eeDetBound n N + qqDetBound n N ≤
      (5 * (((n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (n + 2) + 2))) *
        (N : ℝ) * (N : ℝ) ^ (2 * (n + 1)) := by
    have hEq : eeDetBound n N + qqDetBound n N =
        eeDetBound n N *
          (1 + (1 + (Fintype.card (LoopArg (B.L N) (n + 1)) : ℝ)) ^ 2) := by
      unfold qqDetBound
      ring
    rw [hEq]
    calc
      _ ≤ eeDetBound n N * (5 * (N : ℝ) ^ (2 * (n + 1))) :=
        mul_le_mul_of_nonneg_left hQFactor hEe0
      _ ≤ (((n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (n + 2) + 2)) *
          (N : ℝ) * (5 * (N : ℝ) ^ (2 * (n + 1))) :=
        mul_le_mul_of_nonneg_right hEe (by positivity)
      _ = _ := by ring
  have hScale : B.scale 0 N u ≤ 2 * (N : ℝ) := by
    exact (scale_le_twoW hu).trans (by nlinarith [hWleN])
  have hScale0 : 0 ≤ B.scale 0 N u :=
    (B.scale_pos' (by norm_num) N hu.1 (hu.2.trans_lt (by norm_num))).le
  have hScalePow :
      (B.scale 0 N u) ^ r ≤ (2 : ℝ) ^ r * (N : ℝ) ^ r := by
    calc
      (B.scale 0 N u) ^ r ≤ (2 * (N : ℝ)) ^ r := pow_le_pow_left₀ hScale0 hScale _
      _ = (2 : ℝ) ^ r * (N : ℝ) ^ r := by rw [mul_pow]
  have hNpow :
      (N : ℝ) ^ r * (N : ℝ) * (N : ℝ) ^ (2 * (n + 1)) =
        (N : ℝ) ^ (4 * n + 7) := by
    calc
      _ = (N : ℝ) ^ (r + 1) * (N : ℝ) ^ (2 * (n + 1)) := by rw [← pow_succ]
      _ = (N : ℝ) ^ (r + 1 + 2 * (n + 1)) := by rw [← pow_add]
      _ = (N : ℝ) ^ (4 * n + 7) := by congr 1 <;> dsimp [r] <;> omega
  have hInner0 : 0 ≤ eeDetBound n N + qqDetBound n N :=
    add_nonneg hEe0 (qqDetBound_nonneg n N)
  unfold detEnvelopeBound
  rw [abs_of_nonneg hScale0]
  calc
    _ ≤ ((2 : ℝ) ^ r * (N : ℝ) ^ r) * (eeDetBound n N + qqDetBound n N) :=
      mul_le_mul_of_nonneg_right hScalePow hInner0
    _ ≤ ((2 : ℝ) ^ r * (N : ℝ) ^ r) *
        ((5 * (((n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (n + 2) + 2))) *
          (N : ℝ) * (N : ℝ) ^ (2 * (n + 1))) :=
      mul_le_mul_of_nonneg_left hInner (by positivity)
    _ = (5 * ((n + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ (4 * (n + 2) + 2)) * (N : ℝ) ^ (4 * n + 7) := by
      calc
        _ = (5 * ((n + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ (2 * (n + 2) + 2 + r)) *
            ((N : ℝ) ^ r * (N : ℝ) * (N : ℝ) ^ (2 * (n + 1))) := by
              dsimp [r]
              ring
        _ = _ := by
          rw [hNpow]
          have hr : 2 * (n + 2) + 2 + r = 4 * (n + 2) + 2 := by
            dsimp [r]
            omega
          rw [hr]

/-- At every fixed first-half time and loop order, the concrete actual envelope has moments of
all natural orders.  The bound is the deterministic resolvent estimate of the same `E ⊗ E`
source, followed by the finite-dimensional `QQ` operator bound. -/
theorem integrable_qvEnvelope_pow {n N p : ℕ} (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) :
    Integrable (fun ω : Gauss.Ω d => qvEnvelope n N u q ω ^ p) (Gauss.P d) := by
  have hC0 : 0 ≤ detEnvelopeBound n N u := detEnvelopeBound_nonneg n N u
  have hcont : Continuous (fun ω : Gauss.Ω d => qvEnvelope n N u q ω ^ p) :=
    (qvEnvelope_continuous u q).pow p
  refine Gauss.integrable_of_continuous_of_bound hcont (C := detEnvelopeBound n N u ^ p)
    (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (qvEnvelope_nonneg q ω) p)]
  exact pow_le_pow_left₀ (qvEnvelope_nonneg q ω)
    (qvEnvelope_le_detEnvelopeBound q ω) p

/-- For every fixed moment order, the actual first-half QV envelope has arbitrarily small
polynomial loss, uniformly over first-half time and the actual loop charges.  The moment order
is fixed before the eventual size bound. -/
theorem eventually_momNorm_qvEnvelope_le_smallLoss {n p : ℕ} (hp : 1 ≤ p) :
    ∀ ε > (0 : ℝ), ∃ C ≥ 0, ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        ∀ q : LoopData (B.L N) (n + 2),
          momNorm (Gauss.P d) p (fun ω => qvEnvelope n N u q ω) ≤
            C * (N : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨τ, hτ, hτ1, Cgood, hCgood, hGood⟩ :=
    eventually_qvEnvelope_le_smallLoss (n := n) (hε := hε)
  let K : ℝ := ((4 * n + 8 : ℕ) : ℝ)
  let Env : ℕ → ℝ := fun N => (N : ℝ) ^ K
  let Cdet : ℝ := 5 * ((n + 2 : ℕ) : ℝ) *
    (2 : ℝ) ^ (4 * (n + 2) + 2)
  have hKpos : 0 ≤ K := by dsimp [K]; positivity
  have hKprev : ((4 * n + 7 : ℕ) : ℝ) < K := by
    dsimp [K]
    exact_mod_cast (show 4 * n + 7 < 4 * n + 8 by omega)
  have hdetAbsorb := SumZeroDyn.eventually_const_mul_rpow_le Cdet hKprev
  have hdetPoly : ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), detEnvelopeBound n N u ≤ Env N := by
    filter_upwards [hdetAbsorb, B.dim, eventually_ge_atTop 1] with N hAbs hdim hN u hu
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hpoly := detEnvelopeBound_le_polynomial (n := n) hu hNreal hdim.1
    have hNpowCast : (N : ℝ) ^ (4 * n + 7) =
        (N : ℝ) ^ ((4 * n + 7 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast]
    have hpoly' : detEnvelopeBound n N u ≤
        Cdet * (N : ℝ) ^ ((4 * n + 7 : ℕ) : ℝ) := by
      calc
        detEnvelopeBound n N u ≤ Cdet * (N : ℝ) ^ (4 * n + 7) := hpoly
        _ = Cdet * (N : ℝ) ^ ((4 * n + 7 : ℕ) : ℝ) := by rw [hNpowCast]
    exact hpoly'.trans (by simpa [Env, K] using hAbs)
  have hEnvNonneg : ∀ N, 0 ≤ Env N := by
    intro N
    exact Real.rpow_nonneg (Nat.cast_nonneg N) K
  have hEnvle : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ K := by
    exact Filter.Eventually.of_forall fun _ => le_rfl
  letI := Gauss.isProbabilityMeasure_P d
  have htail := eventually_env_mul_prob_rpow_le (P := Gauss.P d) (q := p)
    (by omega) Lemma514FirstCellLKDecay.highProb_first_half_good
    (Env := Env) (Cenv := K) hKpos hEnvle
    (D := 1) (by norm_num)
  have hEventual : ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        ∀ q : LoopData (B.L N) (n + 2),
          momNorm (Gauss.P d) p (fun ω => qvEnvelope n N u q ω) ≤
            (Cgood + 1) * (N : ℝ) ^ ε := by
    filter_upwards [hGood, hdetPoly, htail, eventually_ge_atTop 1]
      with N hGoodN hdetN htailN hN u hu q
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hEnv : 0 ≤ Env N := hEnvNonneg N
    have hZint : Integrable
        (fun ω : Gauss.Ω d => |qvEnvelope n N u q ω| ^ p) (Gauss.P d) := by
      have hpow := integrable_qvEnvelope_pow (n := n) (N := N) (p := p) u q
      have heq : (fun ω : Gauss.Ω d => |qvEnvelope n N u q ω| ^ p) =
          (fun ω => qvEnvelope n N u q ω ^ p) := by
        funext ω
        rw [abs_of_nonneg (qvEnvelope_nonneg q ω)]
      rw [heq]
      exact hpow
    have hZall : ∀ ω : Gauss.Ω d,
        |qvEnvelope n N u q ω| ≤ Env N := by
      intro ω
      rw [abs_of_nonneg (qvEnvelope_nonneg q ω)]
      exact (qvEnvelope_le_detEnvelopeBound q ω).trans (hdetN u hu)
    have hGoodEnv : ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
        |qvEnvelope n N u q ω| ≤ Cgood * (N : ℝ) ^ ε := by
      intro ω hω
      rw [abs_of_nonneg (qvEnvelope_nonneg q ω)]
      exact hGoodN ω hω u hu q
    have hsplit := momNorm_le_affine_on_event (P := Gauss.P d) (q := p)
      (by omega : p ≠ 0) (Y := fun _ : Gauss.Ω d => (0 : ℝ))
      (Z := fun ω => qvEnvelope n N u q ω)
      (by intro ω; norm_num)
      (by simpa [zero_pow (by omega : p ≠ 0)] using
        (integrable_const (0 : ℝ) : Integrable
          (fun _ : Gauss.Ω d => (0 : ℝ)) (Gauss.P d)))
      hZint (APrimeFirstCellJGAllTime.measurableSet_good N)
      (c := 0) (d := Cgood * (N : ℝ) ^ ε) (Env := Env N)
      (pr := ((Gauss.P d) (APrimeFirstCellJGAllTime.good N)ᶜ).toReal)
      (by norm_num) (mul_nonneg hCgood (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      hEnv ENNReal.toReal_nonneg (by intro ω hω; simpa using hGoodEnv ω hω) hZall le_rfl
    have htailN' : Env N * (((Gauss.P d) (APrimeFirstCellJGAllTime.good N)ᶜ).toReal) ^
        ((1 : ℝ) / p) ≤ (N : ℝ) ^ (-1 : ℝ) := by
      simpa [Env] using htailN
    have hNinv : (N : ℝ) ^ (-1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hNreal (by norm_num)
    have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNreal hε.le
    have hsplit' : momNorm (Gauss.P d) p (fun ω => qvEnvelope n N u q ω) ≤
        Cgood * (N : ℝ) ^ ε +
          Env N * (((Gauss.P d) (APrimeFirstCellJGAllTime.good N)ᶜ).toReal) ^
            ((1 : ℝ) / p) := by
      simpa [zero_mul, zero_add] using hsplit
    calc
      momNorm (Gauss.P d) p (fun ω => qvEnvelope n N u q ω) ≤
          Cgood * (N : ℝ) ^ ε +
            Env N * (((Gauss.P d) (APrimeFirstCellJGAllTime.good N)ᶜ).toReal) ^
              ((1 : ℝ) / p) := hsplit'
      _ ≤ Cgood * (N : ℝ) ^ ε + (N : ℝ) ^ (-1 : ℝ) :=
        add_le_add_right htailN' _
      _ ≤ (Cgood + 1) * (N : ℝ) ^ ε := by nlinarith [hCgood, hNinv, hNε]
  exact ⟨Cgood + 1, by linarith, hEventual⟩

#print axioms eeFun_norm_le_qvEnvelope
#print axioms qq_norm_le_qvEnvelope
#print axioms eventually_qvEnvelope_le_goodBound
#print axioms eventually_qvEnvelope_le_smallLoss
#print axioms integrable_qvEnvelope_pow
#print axioms eventually_momNorm_qvEnvelope_le_smallLoss

end RBM.Gauss.Lemma514FirstHalfQVMoments

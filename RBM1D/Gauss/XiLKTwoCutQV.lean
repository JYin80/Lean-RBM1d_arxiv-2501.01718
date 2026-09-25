/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.XiLKTwoCutInitial
import RBM1D.Gauss.XiLKTwoCutModulus
import RBM1D.Gauss.MomentDuhamelHypGauss
import RBM1D.Gauss.Lemma514NonAlt
import RBM1D.Gauss.Step2Bootstrap
import RBM1D.Flow.Step1Producer
import RBM1D.Hierarchy.EEDef

/-!
# The actual all-charge two-cut quadratic-variation integral (T1341)

This file estimates the literal third summand of the two-coordinate Gaussian moment-Duhamel
formula.  It uses the length-six Step-1 loop bound and the actual `E ⊗ E` field.  The endpoint
normalization and the doubled conjugated charge are retained in the statement.
-/

namespace RBM.Gauss.XiLKTwoCutQV

open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
open RBM.MomentDuhamel RBM.MomentDuhamelCut

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private def glueLD0 {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) : LoopData L 6 :=
  (![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)],
   ![EEBridge.leftArg c 0, EEBridge.leftArg c 1, b,
     EEBridge.rightArg c 1, EEBridge.rightArg c 0, b'])

private def glueLD1 {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) : LoopData L 6 :=
  (![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)],
   ![EEBridge.leftArg c 1, EEBridge.leftArg c 0, b,
     EEBridge.rightArg c 0, EEBridge.rightArg c 1, b'])

private theorem glueLD0_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) :
    (glueLD0 σ c b b').idx = EEBridge.glueIdx
      (toIdx σ (EEBridge.leftArg c))
      (toIdx σ (EEBridge.rightArg c)) 0 b b' := by
  rw [EEDef.glueIdx_two_zero]
  simp [glueLD0, LoopData.idx, List.ofFn_succ]

private theorem glueLD1_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) :
    (glueLD1 σ c b b').idx = EEBridge.glueIdx
      (toIdx σ (EEBridge.leftArg c))
      (toIdx σ (EEBridge.rightArg c)) 1 b b' := by
  rw [EEDef.glueIdx_two_one]
  simp [glueLD1, LoopData.idx, List.ofFn_succ]

private def glueLD {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (k : Fin 2) (b b' : ZMod L) : LoopData L 6 :=
  if k = 0 then glueLD0 σ c b b' else glueLD1 σ c b b'

private theorem glueLD_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (k : Fin 2) (b b' : ZMod L) :
    (glueLD σ c k b b').idx = EEBridge.glueIdx
      (toIdx σ (EEBridge.leftArg c))
      (toIdx σ (EEBridge.rightArg c)) k b b' := by
  fin_cases k
  · simp [glueLD, glueLD0_idx]
  · simp [glueLD, glueLD1_idx]

private theorem sixLoopMomNormDom
    {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore (sample d) E s) :
    MomNormDom B.P
      (fun N (p : TimeIcc s t N × LoopData (d.L N) 6) ω =>
        ‖(sample d).Lval E N p.1 ω p.2.idx‖)
      (fun N p => (B.ell N p.1 / B.ell N (s N)) ^ 5 *
        (B.scale E N p.1)⁻¹ ^ 5) := by
  letI := B.isProbabilityMeasure
  let κ : ℝ := (2 - |E|) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith [abs_lt.mp hE]
  have hEκ : |E| ≤ 2 - κ := by dsimp [κ]; linarith [abs_lt.mp hE]
  have hStep1 : Step1.Hyp (sample d) E s t :=
    step1Hyp_slot d hκ E hEκ s t hs0 hst ht1 c hc hreg hB
  have hdom := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1 hreg.1 hc hreg.2 hStep1
    6 (by norm_num : 1 ≤ 6)
  let Φ : ∀ N, TimeIcc s t N × LoopData (d.L N) 6 → ℝ := fun N p =>
    (B.ell N p.1 / B.ell N (s N)) ^ 5 * (B.scale E N p.1)⁻¹ ^ 5
  let Env : ℕ → ℝ := fun N =>
    (etaT E (t N))⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5
  refine momNormDom_of_stochDom (P := B.P)
    (Y := fun N (p : TimeIcc s t N × LoopData (d.L N) 6) ω =>
      ‖(sample d).Lval E N p.1 ω p.2.idx‖)
    (Φ := Φ) (Env := Env) (Kenv := 6) (Blow := 5) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro N p
    have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    exact (continuous_gloop_Hflow d N p.1 (zt_im_ne_zero_of_lt_one hE hu1)
      (p.2.idx)).norm.measurable
  · intro r N p
    have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have hη : 0 < etaT E (p.1 : ℝ) := etaT_pos hE hu1
    have hJ : p.2.idx.WF := LoopData.idx_wf _
    have hlen : p.2.idx.a.length = 6 := by simp [LoopData.idx]
    have hbound : ∀ ω : Ω d,
        ‖(sample d).Lval E N (p.1 : ℝ) ω p.2.idx‖ ≤
          (etaT E (p.1 : ℝ))⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5 := by
      intro ω
      rw [sample_Lval]
      have hh := norm_gloop_le_det (Hflow_isHermitian d N (p.1 : ℝ) ω)
        hE hu1 p.2.idx hJ (by omega)
      have hsub : p.2.idx.a.length - 1 = 5 := by rw [hlen]
      simpa only [hlen, hsub] using hh
    have hcont := (continuous_gloop_Hflow d N (p.1 : ℝ)
      (zt_im_ne_zero_of_lt_one hE hu1) p.2.idx).norm
    have hintAbs : Integrable
        (fun ω : Ω d => |‖(sample d).Lval E N (p.1 : ℝ) ω p.2.idx‖| ^ (2 * r)) B.P := by
      refine integrable_of_continuous_of_bound (hcont.abs.pow (2 * r))
        (C := ((etaT E (p.1 : ℝ))⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5) ^ (2 * r)) ?_
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_norm]; exact hbound ω) _
    simpa only [abs_norm] using hintAbs
  · intro N p
    have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have hratio : 1 ≤ B.ell N (p.1 : ℝ) / B.ell N (s N) := by
      exact Step1.one_le_ell_div p.1.2.1 hu1
    have hA : 0 < B.scale E N (p.1 : ℝ) := B.scale_pos' hE N hu0 hu1
    exact mul_pos (by positivity) (by positivity)
  · norm_num
  · filter_upwards [d.dim, Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2,
      eventually_ge_atTop 1] with N hdim hsf hN1 p
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hApos : 0 < B.scale E N (p.1 : ℝ) := B.scale_pos' hE N
      ((hs0 N).trans p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
    have hAle : B.scale E N (p.1 : ℝ) ≤ N := by
      have hW : (0 : ℝ) ≤ (d.W N : ℝ) := Nat.cast_nonneg _
      have hL : B.ell N (p.1 : ℝ) ≤ (d.L N : ℝ) := by
        exact min_le_right _ _
      have hη0 : 0 ≤ etaT E (p.1 : ℝ) :=
        etaT_nonneg E (p.1.2.2.trans (ht1 N).le)
      have hη : etaT E (p.1 : ℝ) ≤ 1 :=
        etaT_le_one hE ((hs0 N).trans p.1.2.1)
      have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
      unfold Band.scale
      calc (d.W N : ℝ) * B.ell N (p.1 : ℝ) * etaT E (p.1 : ℝ)
          ≤ ((d.W N : ℝ) * (d.L N : ℝ)) * etaT E (p.1 : ℝ) := by gcongr
        _ ≤ ((d.W N : ℝ) * (d.L N : ℝ)) * 1 := by gcongr
        _ ≤ N := by simpa using hWL
    have hInv : ((N : ℝ)⁻¹) ≤ (B.scale E N (p.1 : ℝ))⁻¹ :=
      inv_anti₀ hApos hAle
    have hInv5 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹) hInv 5
    have hratio : 1 ≤ B.ell N (p.1 : ℝ) / B.ell N (s N) :=
      Step1.one_le_ell_div p.1.2.1 (p.1.2.2.trans_lt (ht1 N))
    have hratio5 : 1 ≤ (B.ell N (p.1 : ℝ) / B.ell N (s N)) ^ 5 := by
      calc
        1 = (1 : ℝ) ^ 5 := by norm_num
        _ ≤ (B.ell N (p.1 : ℝ) / B.ell N (s N)) ^ 5 :=
          pow_le_pow_left₀ (by norm_num) hratio 5
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hN5 : (N : ℝ) ^ (-(5 : ℝ)) = ((N : ℝ)⁻¹) ^ 5 := by
      rw [show (-(5 : ℝ)) = -(5 : ℕ) by norm_num,
        Real.rpow_neg hN0, Real.rpow_natCast, inv_pow]
    rw [hN5]
    change ((N : ℝ)⁻¹) ^ 5 ≤ Φ N p
    dsimp [Φ]
    calc
      ((N : ℝ)⁻¹) ^ 5 ≤ ((N : ℝ)⁻¹) ^ 5 *
          (B.ell N (p.1 : ℝ) / B.ell N (s N)) ^ 5 :=
        le_mul_of_one_le_right (by positivity) hratio5
      _ ≤ (B.ell N (p.1 : ℝ) / B.ell N (s N)) ^ 5 *
          (B.scale E N (p.1 : ℝ))⁻¹ ^ 5 := by
        calc
          _ ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ 5 *
              (B.ell N (p.1 : ℝ) / B.ell N (s N)) ^ 5 :=
            mul_le_mul_of_nonneg_right hInv5 (pow_nonneg (by linarith) 5)
          _ = _ := by ring
      _ = _ := by ring
  · intro N
    dsimp [Env]
    positivity
  · norm_num
  · intro N p ω
    have hhu0 : 0 ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hhu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have hη : 0 < etaT E (p.1 : ℝ) := etaT_pos hE hhu1
    have hbound : ‖(sample d).Lval E N (p.1 : ℝ) ω p.2.idx‖ ≤
        (etaT E (p.1 : ℝ))⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5 := by
      rw [sample_Lval]
      have hlen : p.2.idx.a.length = 6 := by simp [LoopData.idx]
      have hh := norm_gloop_le_det (Hflow_isHermitian d N (p.1 : ℝ) ω)
        hE hhu1 p.2.idx (LoopData.idx_wf _) (by omega)
      rw [hlen] at hh
      have hsub : p.2.idx.a.length - 1 = 5 := by rw [hlen]
      simpa only [hlen, hsub] using hh
    have hηmono : etaT E (t N) ≤ etaT E (p.1 : ℝ) :=
      etaT_le_of_le hE p.1.2.2
    have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
    have hηinv : (etaT E (p.1 : ℝ))⁻¹ ≤ (etaT E (t N))⁻¹ :=
      inv_anti₀ hηt hηmono
    have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hW1 : 1 ≤ (d.W N : ℝ) := by exact_mod_cast (B.W_pos N)
    have hWInv : ((d.W N : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr hW1
    have hEta6 : (etaT E (p.1 : ℝ))⁻¹ ^ 6 ≤ (etaT E (t N))⁻¹ ^ 6 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hη.le) hηinv 6
    have hEnvBound : (etaT E (p.1 : ℝ))⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5 ≤ Env N := by
      dsimp [Env]
      exact mul_le_mul_of_nonneg_right hEta6 (by positivity)
    rw [abs_norm]
    exact hbound.trans hEnvBound
  · filter_upwards [d.dim, Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2,
      eventually_ge_atTop 1] with N hdim hsf hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hηfloor : (N : ℝ)⁻¹ ≤ etaT E (t N) := by
      have hL : B.ell N (t N) ≤ (d.L N : ℝ) := min_le_right _ _
      have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
      have hηt0 : 0 ≤ etaT E (t N) := etaT_nonneg E (ht1 N).le
      have hscaleη : B.scale E N (t N) ≤ N * etaT E (t N) := by
        unfold Band.scale
        calc (d.W N : ℝ) * B.ell N (t N) * etaT E (t N)
            ≤ ((d.W N : ℝ) * (d.L N : ℝ)) * etaT E (t N) := by gcongr
          _ ≤ N * etaT E (t N) := mul_le_mul_of_nonneg_right hWL
            hηt0
      have hscale1 : 1 ≤ B.scale E N (t N) := by
        exact (Real.one_le_rpow (by exact_mod_cast hN1) hc.le).trans
          (hsf ⟨t N, hst N, le_rfl⟩).1
      rw [inv_eq_one_div, div_le_iff₀ hNpos]
      nlinarith [mul_comm (N : ℝ) (etaT E (t N))]
    have hηinv : (etaT E (t N))⁻¹ ≤ (N : ℝ) := by
      have hNinvpos : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
      simpa using inv_anti₀ hNinvpos hηfloor
    have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hW1 : 1 ≤ (d.W N : ℝ) := by exact_mod_cast B.W_pos N
    have hWInv : ((d.W N : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr hW1
    have hEta6 : (etaT E (t N))⁻¹ ^ 6 ≤ (N : ℝ) ^ 6 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (etaT_pos hE (ht1 N)).le) hηinv 6
    have hW5 : ((d.W N : ℝ))⁻¹ ^ 5 ≤ 1 := by
      simpa using pow_le_pow_left₀ (inv_nonneg.mpr hWpos.le) hWInv 5
    have hW5' : ((Dims.growW N : ℝ))⁻¹ ^ 5 ≤ 1 := by
      simpa [d] using hW5
    dsimp [Env]
    calc
      _ ≤ (N : ℝ) ^ 6 * ((Dims.growW N : ℝ)⁻¹) ^ 5 :=
        mul_le_mul_of_nonneg_right hEta6 (by positivity)
      _ ≤ (N : ℝ) ^ 6 * 1 :=
        mul_le_mul_of_nonneg_left hW5' (by positivity)
      _ = (N : ℝ) ^ (6 : ℝ) := by rw [mul_one, ← Real.rpow_natCast]; norm_num
  · have hdom' : StochDom B.P
        (fun N (p : TimeIcc s t N × LoopData (d.L N) 6) ω =>
          |‖(sample d).Lval E N p.1 ω p.2.idx‖|)
        (fun N p _ => Φ N p) := by
      refine StochDom.of_le_left (fun N p ω => ?_) hdom
      exact le_of_eq (abs_of_nonneg (norm_nonneg _))
    simpa [Φ, Nat.sub_one] using hdom'

-- The finite charge and loop-label expansion is normalized through the full EE glue identity.
set_option maxHeartbeats 800000 in
private theorem eeFun_momNorm_le
    {E : ℝ} {s t : ℕ → ℝ} {N P : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) (2 + 2))
    (hP : 1 ≤ P)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q : LoopData (d.L N) 6,
      momNorm B.P (2 * P) (fun ω => ‖(sample d).Lval E N u ω q.idx‖) ≤ M) :
    momNorm B.P P (fun ω => ‖eeFun B E N u ((sample d).H N u ω) σ a‖)
      ≤ (2 * (d.W N : ℝ) * (d.L N : ℝ)) * M := by
  classical
  letI : IsProbabilityMeasure B.P := B.isProbabilityMeasure
  let ι := ZMod (d.L N) × Fin 2 × ZMod (d.L N)
  let weight : ι → ℝ := fun i => (d.W N : ℝ) * ‖SB (d.L N) i.1 i.2.2‖
  let Y : ι → Ω d → ℝ := fun i ω =>
    ‖gloop (d.L N) (d.W N) ((sample d).H N u ω) (zt E u)
      (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg a))
        (toIdx σ (EEBridge.rightArg a)) i.2.1.val i.1 i.2.2)‖
  have hYnonneg : ∀ i ω, 0 ≤ Y i ω := fun _ _ => norm_nonneg _
  have hweight : ∀ i, 0 ≤ weight i := fun _ => by positivity
  have hDet : 0 ≤ (etaT E u)⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5 := by positivity
  have hYbound : ∀ i ω, Y i ω ≤
      (etaT E u)⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5 := by
    intro i ω
    let q := glueLD σ a i.2.1 i.1 i.2.2
    have hidx : q.idx = EEBridge.glueIdx (toIdx σ (EEBridge.leftArg a))
        (toIdx σ (EEBridge.rightArg a)) i.2.1 i.1 i.2.2 := by
      simpa [q] using glueLD_idx σ a i.2.1 i.1 i.2.2
    have hlen : q.idx.a.length = 6 := by simp [LoopData.idx]
    have hDetQ := norm_gloop_le_det (Hflow_isHermitian d N u ω) hE hu1 q.idx
      (LoopData.idx_wf q) (by rw [hlen]; norm_num)
    have hglueLen : (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg a))
        (toIdx σ (EEBridge.rightArg a)) i.2.1 i.1 i.2.2).a.length = 6 := by
      rw [← hidx]
      exact hlen
    rw [hlen] at hDetQ
    rw [hidx] at hDetQ
    norm_num at hDetQ
    simpa [Y] using hDetQ
  have hint : ∀ i, Integrable (fun ω => Y i ω ^ P) B.P := by
    intro i
    have hi := (continuous_gloop_Hflow d N u
      (zt_im_ne_zero_of_lt_one hE hu1)
      (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg a))
        (toIdx σ (EEBridge.rightArg a)) i.2.1.val i.1 i.2.2)).norm
    refine integrable_of_continuous_of_bound (hi.pow P)
      (C := ((etaT E u)⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5) ^ P) ?_
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hYnonneg i ω) _)]
    exact pow_le_pow_left₀ (hYnonneg i ω) (hYbound i ω) P
  have hintEven : ∀ i, Integrable (fun ω => Y i ω ^ (2 * P)) B.P := by
    intro i
    have hi := (continuous_gloop_Hflow d N u
      (zt_im_ne_zero_of_lt_one hE hu1)
      (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg a))
        (toIdx σ (EEBridge.rightArg a)) i.2.1.val i.1 i.2.2)).norm
    refine integrable_of_continuous_of_bound (hi.pow (2 * P))
      (C := ((etaT E u)⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5) ^ (2 * P)) ?_
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hYnonneg i ω) _)]
    exact pow_le_pow_left₀ (hYnonneg i ω) (hYbound i ω) (2 * P)
  have hMY : ∀ i, momNorm B.P P (Y i) ≤ M := by
    intro i
    have hp0 : P ≠ 0 := by omega
    have hpq : P ≤ 2 * P := by nlinarith
    let q6 : LoopData (d.L N) 6 := glueLD σ a i.2.1 i.1 i.2.2
    have hMsource : momNorm B.P (2 * P)
        (fun ω => ‖(sample d).Lval E N u ω q6.idx‖) ≤ M := hM q6
    have hEqAbs : (fun ω => |Y i ω| ^ (2 * P)) = fun ω => Y i ω ^ (2 * P) := by
      funext ω
      rw [abs_of_nonneg (hYnonneg i ω)]
    have hintAbs : Integrable (fun ω => |Y i ω| ^ (2 * P)) B.P := by
      rw [hEqAbs]
      exact hintEven i
    have hi := momNorm_le_momNorm_of_exponent_le hp0 hpq hintAbs
    have hq : Y i = fun ω => ‖(sample d).Lval E N u ω q6.idx‖ := by
      funext ω
      change ‖gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u)
        (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg a))
          (toIdx σ (EEBridge.rightArg a)) i.2.1 i.1 i.2.2)‖ = _
      rw [sample_Lval, ← glueLD_idx]
    have hqMom : momNorm B.P (2 * P) (Y i) =
        momNorm B.P (2 * P) (fun ω => ‖(sample d).Lval E N u ω q6.idx‖) :=
      congrArg (momNorm B.P (2 * P)) hq
    calc
      momNorm B.P P (Y i) ≤ momNorm B.P (2 * P) (Y i) := hi
      _ = momNorm B.P (2 * P) (fun ω => ‖(sample d).Lval E N u ω q6.idx‖) := hqMom
      _ ≤ M := hMsource
  have hZ : ∀ ω, |‖eeFun B E N u ((sample d).H N u ω) σ a‖|
      ≤ ∑ i : ι, weight i * Y i ω := by
    intro ω
    have hsum := EEDef.norm_eeFun_le_W_sum (sample d) E N u ω σ a
    have hsum' : ‖eeFun B E N u ((sample d).H N u ω) σ a‖ ≤
        (d.W N : ℝ) * ∑ b : ZMod (d.L N), EEDef.eeL6 (sample d) E N u ω σ a b := by
      exact hsum
    rw [abs_norm]
    calc
      ‖eeFun B E N u ((sample d).H N u ω) σ a‖ ≤
          (d.W N : ℝ) * ∑ b : ZMod (d.L N), EEDef.eeL6 (sample d) E N u ω σ a b := hsum'
      _ = ∑ i : ι, weight i * Y i ω := by
        simp only [EEDef.eeL6]
        simp_rw [Finset.mul_sum]
        conv_rhs => simp only [ι, Fintype.sum_prod_type]
        simp only [Finset.sum_range_succ, Finset.range_zero,
          Finset.sum_empty, add_zero, zero_add]
        simp [weight, Y, EEDef.glueIdx_two_zero, EEDef.glueIdx_two_one,
          Fin.sum_univ_two, toIdx, mul_assoc, mul_left_comm, mul_comm]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
  have hweightSum : ∑ i : ι, weight i =
      (2 * (d.W N : ℝ) * (d.L N : ℝ)) := by
    classical
    change (∑ i : ZMod (d.L N) × Fin 2 × ZMod (d.L N),
      (d.W N : ℝ) * ‖SB (d.L N) i.1 i.2.2‖) = _
    calc
      _ = ∑ b : ZMod (d.L N), ∑ k : Fin 2, ∑ b' : ZMod (d.L N),
          (d.W N : ℝ) * ‖SB (d.L N) b b'‖ := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ b : ZMod (d.L N), ∑ k : Fin 2, (d.W N : ℝ) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, RBM.sum_norm_SB_apply_row
          (d.L N) (d.three_le_L N) b, mul_one]
      _ = ∑ b : ZMod (d.L N), (2 * (d.W N : ℝ)) := by
        congr 1
        simp [Fin.sum_univ_two, mul_comm]
      _ = 2 * (d.W N : ℝ) * (d.L N : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        push_cast
        ring
  have hsum := momNorm_le_of_le_weighted_sum (P := B.P) (q := P) (by omega)
    hweight hYnonneg hint (by positivity) hMY hZ
  simpa [hweightSum, Y] using hsum

-- Measurability and integrability pass through the actual Gaussian flow and Uker moment norm.
set_option maxHeartbeats 800000 in
/-- The displayed QV integrand is interval integrable on every actual segment below time one.
This is the concrete Gaussian integrand from (5.24), with the doubled charge and doubled label. -/
theorem intervalIntegrable_actual_qv_integrand
    {E : ℝ} {N : ℕ} {s v : ℝ} (hE : |E| < 2) (hsv : s ≤ v) (hv1 : v < 1)
    (q : LoopData (d.L N) 2) (P : ℕ) :
    IntervalIntegrable (fun u : ℝ => momNorm (band d).P P (fun ω =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (eeFun (band d) E N u ((sample d).H N u ω) q.1) (Fin.append q.2 q.2)‖))
      volume s v := by
  exact RBM.Gauss.intervalIntegrable_momNorm_eeFun_gauss
    (d := d) E N hE hsv hv1 q.1 q.2 P

private theorem eventually_growL_sq_le_growW :
    ∀ᶠ N : ℕ in atTop,
      (RBM.Gauss.Dims.growL N : ℝ) ^ 2 ≤ (RBM.Gauss.Dims.growW N : ℝ) := by
  filter_upwards [eventually_ge_atTop 81] with N hN
  have hLpos : 0 < RBM.Gauss.Dims.growL N := by
    unfold RBM.Gauss.Dims.growL
    omega
  have hL4 := RBM.Gauss.Dims.growL_pow_le N hN
  have hL3 : RBM.Gauss.Dims.growL N ^ 3 ≤ N / RBM.Gauss.Dims.growL N :=
    (Nat.le_div_iff_mul_le hLpos).2 (by
      calc RBM.Gauss.Dims.growL N ^ 3 * RBM.Gauss.Dims.growL N =
            RBM.Gauss.Dims.growL N ^ 4 := by ring
        _ ≤ N := hL4)
  rw [RBM.Gauss.Dims.growW_eq N hN]
  have hL2 : RBM.Gauss.Dims.growL N ^ 2 ≤ RBM.Gauss.Dims.growL N ^ 3 := by
    calc
      _ = RBM.Gauss.Dims.growL N ^ 2 * 1 := by simp
      _ ≤ RBM.Gauss.Dims.growL N ^ 2 * RBM.Gauss.Dims.growL N :=
        Nat.mul_le_mul_left _ (by unfold RBM.Gauss.Dims.growL; omega)
      _ = _ := by ring
  exact_mod_cast hL2.trans hL3

/-- At the left endpoint, the spatial factor is paid by the scale and the exampleGrow relation
`L^2 ≤ W`.  The proof separates the saturated and unsaturated branches of `ellHat`. -/
private theorem ell_left_ratio_le_sqrt_scale
    {E : ℝ} {N : ℕ} {s : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hAs : 1 ≤ B.scale E N s) (hLW : (d.L N : ℝ) ^ 2 ≤ (d.W N : ℝ)) :
    (B.L N : ℝ) / B.ell N s ≤
      Real.sqrt ((mE E).im⁻¹ * B.scale E N s) := by
  have hLW' : (B.L N : ℝ) ^ 2 ≤ (B.W N : ℝ) := hLW
  have hμ : 0 < (mE E).im := mE_im_pos hE
  have hμ1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hell : 1 ≤ B.ell N s :=
    one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1
  have hAspos : 0 < B.scale E N s := by linarith
  have hratio0 : 0 ≤ (B.L N : ℝ) / B.ell N s := by positivity
  have hellForm : B.ell N s = min (1 / Real.sqrt (1 - s)) (B.L N : ℝ) := by
    change ellHat (B.L N) (s : ℂ) = _
    rw [ellHat_ofReal (B.L N) hs1]
  rcases le_total (B.L N : ℝ) (1 / Real.sqrt (1 - s)) with hsat | hunsat
  · have hEll : B.ell N s = (B.L N : ℝ) := by
      rw [hellForm, min_eq_right hsat]
    have hLpos : (0 : ℝ) < (B.L N : ℝ) := by
      exact_mod_cast (show 0 < B.L N by have := B.three_le_L N; omega)
    have hratio : (B.L N : ℝ) / B.ell N s = 1 := by
      rw [hEll]
      field_simp [hLpos.ne']
    rw [hratio]
    have hμinv : 1 ≤ (mE E).im⁻¹ := (one_le_inv₀ hμ).2 hμ1
    have hprod : 1 ≤ (mE E).im⁻¹ * B.scale E N s :=
      one_le_mul_of_one_le_of_one_le hμinv hAs
    exact Real.one_le_sqrt.2 hprod
  · have hEll : B.ell N s = 1 / Real.sqrt (1 - s) := by
      rw [hellForm, min_eq_left hunsat]
    have hsqrt : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 (by linarith)
    have hEllSq : B.ell N s ^ 2 * (1 - s) = 1 := by
      rw [hEll, div_pow, Real.sq_sqrt (by linarith)]
      field_simp [ne_of_gt (show (0 : ℝ) < 1 - s by linarith)]
    have hell0 : 0 < B.ell N s := by positivity
    have hAsEq : B.scale E N s =
        (B.W N : ℝ) * (mE E).im / B.ell N s := by
      rw [Band.scale, Step2.etaT_eq E s]
      have hEllInv : B.ell N s * (1 - s) = (B.ell N s)⁻¹ := by
        have hh := hEllSq
        field_simp [hell0.ne'] at hh ⊢
        nlinarith
      calc
        (B.W N : ℝ) * B.ell N s * ((1 - s) * (mE E).im) =
            (B.W N : ℝ) * (mE E).im * (B.ell N s * (1 - s)) := by ring
        _ = (B.W N : ℝ) * (mE E).im * (B.ell N s)⁻¹ := by rw [hEllInv]
        _ = (B.W N : ℝ) * (mE E).im / B.ell N s := by rw [div_eq_mul_inv]
    have hsq : ((B.L N : ℝ) / B.ell N s) ^ 2 ≤ (mE E).im⁻¹ * B.scale E N s := by
      rw [hAsEq]
      have hW0 : 0 ≤ (B.W N : ℝ) := Nat.cast_nonneg _
      have hLsq : (B.L N : ℝ) ^ 2 ≤ (B.W N : ℝ) * B.ell N s :=
        hLW'.trans (by nlinarith [mul_le_mul_of_nonneg_left (hell : 1 ≤ B.ell N s) hW0])
      have hell0 : 0 < B.ell N s := by positivity
      have hμ0 : (mE E).im ≠ 0 := hμ.ne'
      field_simp [hell0.ne', hμ0]
      nlinarith
    exact Real.le_sqrt_of_sq_le hsq

-- The deterministic six-loop envelope is pushed through the finite Gaussian moment norm.
set_option maxHeartbeats 800000 in
private theorem eeFun_loop_moment_integrable
    {E : ℝ} {N P : ℕ} {u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 4) :
    Integrable (fun ω : Ω d =>
      ‖eeFun (band d) E N u ((sample d).H N u ω) σ a‖ ^ P) (band d).P := by
  letI := (band d).isProbabilityMeasure
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hcont : Continuous (fun ω : Ω d =>
      eeFun (band d) E N u ((sample d).H N u ω) σ a) := by
    rw [← continuousOn_univ]
    exact RBM.Gauss.continuousOn_eeFun_path d N E (τ := fun _ => u)
      continuousOn_const (continuous_Hflow d N u).continuousOn
      (fun ω => Hflow_isHermitian d N u ω)
      (fun _ _ => by rw [← etaT_eq_zt_im]; exact hη.ne') σ a
  let Cdet : ℝ := (2 : ℝ) * (d.W N : ℝ) *
    (Fintype.card (ZMod (d.L N)) : ℝ) *
      (etaT E u)⁻¹ ^ 6 * ((d.W N : ℝ))⁻¹ ^ 5
  have himpos : 0 < (zt E u).im := by simpa only [etaT_eq_zt_im] using hη
  have hηabs : etaT E u ≤ |(zt E u).im| := by
    rw [etaT_eq_zt_im E u, abs_of_pos himpos]
  have hbound : ∀ ω : Ω d,
      ‖eeFun (band d) E N u ((sample d).H N u ω) σ a‖ ≤ Cdet := by
    intro ω
    have h := RBM.Gauss.norm_eeFun_herm_le d N E hη hηabs
      (Hflow_isHermitian d N u ω) σ a
    simpa [Cdet, pow_succ, mul_assoc] using h
  refine integrable_of_continuous_of_bound ((hcont.norm).pow P)
    (C := Cdet ^ P) ?_
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound ω) P

private theorem qv_momNorm_profile
    {E : ℝ} {N P : ℕ} {s u v : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (huv : u ≤ v) (hv1 : v < 1)
    (hP : 1 ≤ P) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q : LoopData (d.L N) 6,
      momNorm B.P (2 * P)
        (fun ω => ‖(sample d).Lval E N u ω q.idx‖) ≤ M)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 4) :
    momNorm B.P P (fun ω =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (eeFun B E N u ((sample d).H N u ω) σ) a‖) ≤
      ((1 - u) / (1 - v)) ^ 4 * (2 * (d.W N : ℝ) * (d.L N : ℝ)) * M := by
  letI := B.isProbabilityMeasure
  have hv0 : 0 ≤ v := hu0.trans huv
  have hxi : ∀ i : Fin 4, ‖SumZeroDyn.xi2 E σ i‖ ≤ 1 :=
    fun i => SumZeroDyn.norm_xi2_le hE σ i
  have ht : ∀ i : Fin 4,
      ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ < 1 := by
    intro i
    have hmul : ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ ≤ v := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0]
      exact (mul_le_mul_of_nonneg_left (hxi i) hv0).trans_eq (by ring)
    exact hmul.trans_lt hv1
  have hC : ∀ i : Fin 4,
      1 + ‖((((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i)‖ *
          (1 - ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤
        (1 - u) / (1 - v) := by
    intro i
    have h1v : 0 < 1 - v := by linarith
    have hnum : ‖(((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) *
        SumZeroDyn.xi2 E σ i‖ ≤ v - u := by
      rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (by linarith : u - v ≤ 0)]
      exact (mul_le_mul_of_nonneg_left (hxi i) (by linarith)).trans_eq (by ring)
    have hvnorm : ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ ≤ v := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0]
      exact (mul_le_mul_of_nonneg_left (hxi i) hv0).trans_eq (by ring)
    have hden : 0 < 1 - ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ := by
      linarith [ht i]
    have hinv : (1 - ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤
        (1 - v)⁻¹ := inv_anti₀ h1v (by linarith)
    have hprod : ‖(((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i‖ *
          (1 - ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤ (v - u) * (1 - v)⁻¹ :=
      mul_le_mul hnum hinv (inv_nonneg.mpr hden.le) (by linarith)
    calc
      1 + ‖(((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i‖ *
            (1 - ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ =
          ‖(((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i‖ *
            (1 - ‖((v : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ + 1 := by ring
      _ ≤ (v - u) * (1 - v)⁻¹ + 1 := by linarith [hprod]
      _ = (1 - u) / (1 - v) := by field_simp [h1v.ne']; ring
  have hMfun : ∀ b : LoopArg (d.L N) 4,
      momNorm B.P P (fun ω => ‖eeFun B E N u ((sample d).H N u ω) σ b‖) ≤
        2 * (d.W N : ℝ) * (d.L N : ℝ) * M := by
    intro b
    exact eeFun_momNorm_le (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
      hE (fun _ => by norm_num) (fun _ => by norm_num)
      (fun _ => by norm_num) hu0 hu1 σ b hP hM0 hM
  have hUk := RBM.Gauss.momNorm_Uker_apply_le
      (P := B.P) (L := d.L N) (hL := by have := d.three_le_L N; exact this)
      (q := P) (hq := by omega) (n := 4)
      (ξ := SumZeroDyn.xi2 E σ) (s := ((u : ℝ) : ℂ)) (t := ((v : ℝ) : ℂ))
      (ht := ht) (C := (1 - u) / (1 - v)) (hC := hC)
      (A := fun ω b => eeFun B E N u ((sample d).H N u ω) σ b)
      (hint := fun b => eeFun_loop_moment_integrable hE hu1 σ b)
      (M := 2 * (d.W N : ℝ) * (d.L N : ℝ) * M) (hM0 := by positivity)
      (hM := by intro b; simpa [mul_assoc] using hMfun b) a
  simpa [mul_assoc] using hUk

-- The moving-window proof combines Step-1 transfer, kernel transport, time integration and
-- the square-root endpoint normalization in one uniformly quantified estimate.
set_option maxHeartbeats 1600000 in
/-- Uniform moving-window estimate for the actual doubled-charge QV summand in (5.24).
The source length-six Step-1 bound is converted to the actual `E ⊗ E` field, then transported
through the four-edge kernel before the time integral is taken. -/
theorem actual_qv_integral_bound
    {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ v ∈ Set.Icc (s N) (t N), ∀ q : LoopData (d.L N) 2,
          B.scale E N v ^ 2 *
            (cMDval' P 0 * ∫ u in (s N)..v, momNorm B.P P (fun ω =>
              ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (eeFun B E N u ((sample d).H N u ω) q.1)
                (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
              ≤ C * (N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 3) := by
  intro ε hε P hP
  obtain ⟨C₀, hC₀, hMom⟩ :=
    sixLoopMomNormDom hE hs0 hst ht1 hc hreg hB ε hε P hP
  have h30 := hreg.1.pow_thirty_le hE hst ht1
  have hcMDpos : 0 < cMDval' P 0 := by
    rw [cMDval'_of_one_le hP]
    have hp1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith [hp1]
  have hμmain : 0 < (mE E).im := mE_im_pos hE
  have hμinvmain : 0 < (mE E).im⁻¹ := inv_pos.mpr hμmain
  have hCqvMain : 0 < 2 * C₀ * (mE E).im⁻¹ * Real.sqrt ((mE E).im⁻¹) := by
    positivity
  refine ⟨1 + cMDval' P 0 *
      (2 * C₀ * (mE E).im⁻¹ * Real.sqrt ((mE E).im⁻¹)), by positivity, ?_⟩
  filter_upwards [hMom, h30, eventually_growL_sq_le_growW, hreg.2,
      eventually_ge_atTop (1 : ℕ)] with N hMomN h30N hLW hregN hN1
  intro v hv q
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hcCast : (0 : ℝ) < c := hc
  have hNc : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hNreal hcCast.le
  have hAtLower : (N : ℝ) ^ c ≤ B.scale E N (t N) := hregN
  have hW0 : 0 ≤ (B.W N : ℝ) := by positivity
  have hAvAt : B.scale E N (t N) ≤ B.scale E N v := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW0 (B.L N) E
      (Set.mem_Iic.mpr (hv.2.trans_lt (ht1 N)).le)
      (Set.mem_Iic.mpr (ht1 N).le) hv.2
  have hAvAs : B.scale E N v ≤ B.scale E N (s N) := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW0 (B.L N) E
      (Set.mem_Iic.mpr hs1.le) (Set.mem_Iic.mpr hv1.le) hv.1
  have hAs1 : 1 ≤ B.scale E N (s N) := by
    exact hNc.trans (hAtLower.trans (hAvAt.trans hAvAs))
  have hAspos : 0 < B.scale E N (s N) := by linarith
  have hAvpos : 0 < B.scale E N v := by
    exact lt_of_lt_of_le (by norm_num) (hNc.trans (hAtLower.trans hAvAt))
  have hR30sub := h30N ⟨v, hv⟩
  have hR30 : ((1 - s N) / (1 - v)) ^ 30 ≤ B.scale E N v := by
    rw [Step2.etaT_ratio hE (s N) v] at hR30sub
    exact hR30sub
  let R : ℝ := (1 - s N) / (1 - v)
  have h1v : 0 < 1 - v := by linarith
  have h1s : 0 < 1 - s N := by linarith
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact (le_div_iff₀ h1v).2 (by nlinarith [hv.1])
  have hR30' : R ^ 30 ≤ B.scale E N v := by simpa [R] using hR30
  have hR5 : R ^ 5 ≤ (B.scale E N v) ^ ((1 : ℝ) / 6) := by
    have hp := Real.rpow_le_rpow (x := R ^ 30) (y := B.scale E N v)
      (pow_nonneg hRpos.le 30) hR30' (by norm_num : 0 ≤ (1 : ℝ) / 6)
    have hpow : (R ^ 30) ^ ((1 : ℝ) / 6) = R ^ 5 := by
      calc
        (R ^ 30) ^ ((1 : ℝ) / 6) = (R ^ (30 : ℝ)) ^ ((1 : ℝ) / 6) := by
          exact congrArg (fun x : ℝ => x ^ ((1 : ℝ) / 6))
            (Real.rpow_natCast R 30).symm
        _ = R ^ ((30 : ℝ) * ((1 : ℝ) / 6)) := by
          exact (Real.rpow_mul hRpos.le (30 : ℝ) ((1 : ℝ) / 6)).symm
        _ = R ^ 5 := by
          rw [show (30 : ℝ) * ((1 : ℝ) / 6) = 5 by norm_num]
          exact Real.rpow_natCast R 5
    rw [hpow] at hp
    exact hp
  have hR5As : R ^ 5 ≤ B.scale E N (s N) ^ ((1 : ℝ) / 6) :=
    hR5.trans (Real.rpow_le_rpow (by positivity) hAvAs (by norm_num))
  have hμ : 0 < (mE E).im := mE_im_pos hE
  have hμinv : 0 < (mE E).im⁻¹ := inv_pos.mpr hμ
  have hμinv0 : 0 ≤ (mE E).im⁻¹ := hμinv.le
  have hlog : Real.log R ≤ R := by
    have hh := Real.log_le_sub_one_of_pos hRpos
    linarith
  have hratioEll : B.ell N v / B.ell N (s N) ≤ R := by
    have hEll := Step3.ellHat_le_sqrt_mul (L := B.L N) (s := s N) (t := v) hv.1 hv1
    have hEll' : B.ell N v ≤ Real.sqrt R * B.ell N (s N) := by
      simpa [Band.ell, R] using hEll
    have hEllsPos : 0 < B.ell N (s N) :=
      lt_of_lt_of_le zero_lt_one (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1)
    have hsqrtR : Real.sqrt R ≤ R := by
      have h1sqrt : 1 ≤ Real.sqrt R := Real.one_le_sqrt.2 hR1
      have hsquare := Real.sq_sqrt hRpos.le
      nlinarith
    calc
      B.ell N v / B.ell N (s N) ≤ Real.sqrt R := (div_le_iff₀ hEllsPos).2 hEll'
      _ ≤ R := hsqrtR
  have hEllsPos : 0 < B.ell N (s N) :=
    lt_of_lt_of_le zero_lt_one (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1)
  have hEllvPosGlobal : 0 < B.ell N v :=
    lt_of_lt_of_le zero_lt_one (one_le_ellHat_of_nonneg (B.one_le_L N) hv0 hv1)
  have hLratio := ell_left_ratio_le_sqrt_scale hE (hs0 N) hs1 hAs1 hLW
  have hLratio' : (B.L N : ℝ) / B.ell N (s N) ≤
      Real.sqrt ((mE E).im⁻¹ * B.scale E N (s N)) := hLratio
  have hAsPower : Real.sqrt (B.scale E N (s N)) *
      B.scale E N (s N) ^ ((1 : ℝ) / 6) =
        B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hAspos]
  have hAsPowerSq :
      (B.scale E N (s N) ^ ((1 : ℝ) / 3)) ^ 2 =
        B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  let Cqv : ℝ := 2 * C₀ * (mE E).im⁻¹ * Real.sqrt ((mE E).im⁻¹)
  have hCqv0 : 0 ≤ Cqv := by positivity
  have hCqvDom : cMDval' P 0 * Cqv ≤ (1 + cMDval' P 0 * Cqv) ^ 2 := by
    have hcMD : 0 ≤ cMDval' P 0 := cMDval'_nonneg P 0
    have hx : 0 ≤ cMDval' P 0 * Cqv := mul_nonneg hcMD hCqv0
    nlinarith [sq_nonneg (cMDval' P 0 * Cqv)]
  have hIntActual := intervalIntegrable_actual_qv_integrand (N := N) (s := s N) (v := v)
    hE hv.1 hv1 q P
  let f : ℝ → ℝ := fun u => momNorm B.P P (fun ω =>
    ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (eeFun B E N u ((sample d).H N u ω) q.1) (Fin.append q.2 q.2)‖)
  have hInt : IntervalIntegrable f volume (s N) v := by simpa [f, B] using hIntActual
  have hIntInv : IntervalIntegrable (fun u : ℝ => (1 - u)⁻¹) volume (s N) v := by
    have hcont : ContinuousOn (fun u : ℝ => (1 - u)⁻¹) (Set.uIcc (s N) v) := by
      refine (continuousOn_const.sub continuousOn_id).inv₀ ?_
      intro u hu
      rw [Set.uIcc_of_le hv.1] at hu
      exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hu.2 hv1))
    exact hcont.intervalIntegrable
  let Mbase : ℝ := C₀ * (N : ℝ) ^ (ε / 2)
  have hMbase : 0 ≤ Mbase := by positivity
  have hMsource : ∀ u : ℝ, u ∈ Set.Icc (s N) v →
      ∀ q₆ : LoopData (d.L N) 6,
        momNorm B.P (2 * P) (fun ω => ‖(sample d).Lval E N u ω q₆.idx‖) ≤
          Mbase * (B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5 := by
    intro u hu q₆
    let uT : TimeIcc s t N := ⟨u, hu.1, le_trans hu.2 hv.2⟩
    have h := hMomN (uT, q₆)
    calc
      momNorm B.P (2 * P) (fun ω => ‖(sample d).Lval E N u ω q₆.idx‖) ≤
          C₀ * ((N : ℝ) ^ (ε / 2) *
            ((B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5)) := h
      _ = Mbase * (B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5 := by
        dsimp [Mbase]
        ring
  have hIntUpper : B.scale E N v ^ 4 * ∫ u in (s N)..v, f u ≤
      Cqv * (N : ℝ) ^ (ε / 2) * B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by
    have hprofile : ∀ u ∈ Set.Icc (s N) v,
        B.scale E N v ^ 4 * f u ≤
          2 * C₀ * (N : ℝ) ^ (ε / 2) *
            (B.L N : ℝ) / B.ell N (s N) *
              (B.ell N v / B.ell N (s N)) ^ 4 * (etaT E u)⁻¹ := by
      intro u hu
      have hu0 : 0 ≤ u := (hs0 N).trans hu.1
      have hu1 : u < 1 := hu.2.trans_lt hv1
      have hAuPos : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
      have hElluPos : 0 < B.ell N u :=
        lt_of_lt_of_le zero_lt_one
          (one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1)
      have hEllvPos : 0 < B.ell N v :=
        lt_of_lt_of_le zero_lt_one
          (one_le_ellHat_of_nonneg (B.one_le_L N) hv0 hv1)
      have hM0' : 0 ≤ Mbase * (B.ell N u / B.ell N (s N)) ^ 5 *
          (B.scale E N u)⁻¹ ^ 5 := by positivity
      have hU := qv_momNorm_profile (s := s N) hE hu0 hu1 hu.2 hv1 hP
        hM0' (hMsource u hu) q.1 (Fin.append q.2 q.2)
      have hAscaleId : B.scale E N v ^ 4 *
          (((1 - u) / (1 - v)) ^ 4 * (2 * (d.W N : ℝ) * (d.L N : ℝ)) *
            (Mbase * (B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5)) =
            2 * C₀ * (N : ℝ) ^ (ε / 2) *
              (B.L N : ℝ) / B.ell N (s N) *
                (B.ell N v / B.ell N (s N)) ^ 4 * (etaT E u)⁻¹ := by
        have hWcast : (B.W N : ℝ) = (d.W N : ℝ) := rfl
        have hLcast : (B.L N : ℝ) = (d.L N : ℝ) := rfl
        have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
        rw [Band.scale, Band.scale, Step2.etaT_eq E u,
          Step2.etaT_eq E v]
        rw [hWcast, hLcast]
        field_simp [hAuPos.ne', (etaT_pos hE hu1).ne',
          (etaT_pos hE hv1).ne', hElluPos.ne', hEllvPos.ne', hEllsPos.ne',
          (show (1 - u) ≠ 0 by linarith), (show (1 - v) ≠ 0 by linarith)]
        dsimp [Mbase]
        rw [show ε / 2 = ε * (1 / 2) by ring]
        field_simp [hWpos.ne']
      calc
        B.scale E N v ^ 4 * f u ≤ B.scale E N v ^ 4 *
            (((1 - u) / (1 - v)) ^ 4 * (2 * (d.W N : ℝ) * (d.L N : ℝ)) *
              (Mbase * (B.ell N u / B.ell N (s N)) ^ 5 * (B.scale E N u)⁻¹ ^ 5)) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
        _ = _ := hAscaleId
    have hprofile' : ∀ u ∈ Set.Icc (s N) v,
        B.scale E N v ^ 4 * f u ≤
          (2 * C₀ * (N : ℝ) ^ (ε / 2) *
            (B.L N : ℝ) / B.ell N (s N) *
              (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹) * (1 - u)⁻¹ := by
      intro u hu
      have hu1 : u < 1 := hu.2.trans_lt hv1
      have hEta : (etaT E u)⁻¹ = (mE E).im⁻¹ * (1 - u)⁻¹ := by
        rw [Step2.etaT_eq]
        field_simp [hμ.ne', (show 1 - u ≠ 0 by linarith)]
      have hp := hprofile u hu
      rw [hEta] at hp
      simpa only [mul_assoc] using hp
    have hmono := intervalIntegral.integral_mono_on hv.1
      (hInt.const_mul (B.scale E N v ^ 4))
      (hIntInv.const_mul
        (2 * C₀ * (N : ℝ) ^ (ε / 2) * (B.L N : ℝ) / B.ell N (s N) *
          (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹))
      (by intro u hu; simpa [f] using hprofile' u hu)
    have hIntComp : B.scale E N v ^ 4 * ∫ u in (s N)..v, f u ≤
        2 * C₀ * (N : ℝ) ^ (ε / 2) * (B.L N : ℝ) / B.ell N (s N) *
          (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ * Real.log R := by
      calc
        B.scale E N v ^ 4 * ∫ u in (s N)..v, f u =
            ∫ u in (s N)..v, B.scale E N v ^ 4 * f u :=
              (intervalIntegral.integral_const_mul _ _).symm
        _ ≤ ∫ u in (s N)..v,
            (2 * C₀ * (N : ℝ) ^ (ε / 2) * (B.L N : ℝ) / B.ell N (s N) *
              (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹) * (1 - u)⁻¹ := hmono
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, SumZeroDyn.integral_inv_one_sub_eq hv.1 hv1]
    have hIntRed :
        2 * C₀ * (N : ℝ) ^ (ε / 2) * (B.L N : ℝ) / B.ell N (s N) *
          (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ * Real.log R ≤
            Cqv * (N : ℝ) ^ (ε / 2) *
              B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by
      have hratio4 : (B.ell N v / B.ell N (s N)) ^ 4 ≤ R ^ 4 :=
        pow_le_pow_left₀ (div_nonneg hEllvPosGlobal.le hEllsPos.le) hratioEll 4
      have hmulR : (B.L N : ℝ) / B.ell N (s N) *
          (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ * Real.log R ≤
            (B.L N : ℝ) / B.ell N (s N) * R ^ 5 * (mE E).im⁻¹ := by
        have hA : 0 ≤ (B.L N : ℝ) / B.ell N (s N) := by positivity
        have hB' : 0 ≤ (mE E).im⁻¹ := hμinv0
        have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR1
        have hstep : (B.L N : ℝ) / B.ell N (s N) *
            (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ ≤
              (B.L N : ℝ) / B.ell N (s N) * R ^ 4 * (mE E).im⁻¹ := by
          calc
            _ = ((B.L N : ℝ) / B.ell N (s N) *
                (B.ell N v / B.ell N (s N)) ^ 4) * (mE E).im⁻¹ := by ring
            _ ≤ ((B.L N : ℝ) / B.ell N (s N) * R ^ 4) * (mE E).im⁻¹ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hratio4 hA) hB'
            _ = _ := by ring
        calc
          _ = ((B.L N : ℝ) / B.ell N (s N) *
                (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹) * Real.log R := by ring
          _ ≤ ((B.L N : ℝ) / B.ell N (s N) * R ^ 4 * (mE E).im⁻¹) * Real.log R :=
            mul_le_mul_of_nonneg_right hstep hlog0
          _ ≤ ((B.L N : ℝ) / B.ell N (s N) * R ^ 4 * (mE E).im⁻¹) * R := by
            exact mul_le_mul_of_nonneg_left hlog
              (mul_nonneg (mul_nonneg hA (pow_nonneg hRpos.le 4)) hB')
          _ = _ := by ring
      have hLbound : (B.L N : ℝ) / B.ell N (s N) * R ^ 5 * (mE E).im⁻¹ ≤
          Real.sqrt ((mE E).im⁻¹ * B.scale E N (s N)) *
            B.scale E N (s N) ^ ((1 : ℝ) / 6) * (mE E).im⁻¹ := by
        have hprod : (B.L N : ℝ) / B.ell N (s N) * R ^ 5 ≤
            Real.sqrt ((mE E).im⁻¹ * B.scale E N (s N)) *
              B.scale E N (s N) ^ ((1 : ℝ) / 6) :=
          mul_le_mul hLratio' hR5As (pow_nonneg hRpos.le 5)
            (Real.sqrt_nonneg _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hprod hμinv0
      have hLbound' : (B.L N : ℝ) / B.ell N (s N) * R ^ 5 * (mE E).im⁻¹ ≤
          Real.sqrt ((mE E).im⁻¹) *
            B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) * (mE E).im⁻¹ := by
        calc
          _ ≤ Real.sqrt ((mE E).im⁻¹ * B.scale E N (s N)) *
              B.scale E N (s N) ^ ((1 : ℝ) / 6) * (mE E).im⁻¹ := hLbound
          _ = _ := by
            rw [Real.sqrt_mul hμinv0]
            simpa [mul_assoc] using
              congrArg (fun x : ℝ => Real.sqrt ((mE E).im⁻¹) * x *
                (mE E).im⁻¹) hAsPower
      have hmain :
          2 * C₀ * (B.L N : ℝ) / B.ell N (s N) *
            (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ * Real.log R ≤
            Cqv * B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by
        dsimp [Cqv]
        calc
          _ = 2 * C₀ * ((B.L N : ℝ) / B.ell N (s N) *
              (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ * Real.log R) := by
            field_simp [hEllsPos.ne']
            dsimp [B]
            ring
          _ ≤ 2 * C₀ * ((B.L N : ℝ) / B.ell N (s N) * R ^ 5 * (mE E).im⁻¹) := by
            have hcoeff : 0 ≤ 2 * C₀ := by positivity
            exact mul_le_mul_of_nonneg_left hmulR hcoeff
          _ ≤ 2 * C₀ * (Real.sqrt ((mE E).im⁻¹) *
              B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) *
              (mE E).im⁻¹) := by
            exact mul_le_mul_of_nonneg_left hLbound' (by positivity)
          _ = 2 * C₀ * (mE E).im⁻¹ * Real.sqrt ((mE E).im⁻¹) *
              B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by ring
      calc
        _ = (N : ℝ) ^ (ε / 2) *
            (2 * C₀ * (B.L N : ℝ) / B.ell N (s N) *
              (B.ell N v / B.ell N (s N)) ^ 4 * (mE E).im⁻¹ * Real.log R) := by ring
        _ ≤ (N : ℝ) ^ (ε / 2) *
            (Cqv * B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6)) := by
              gcongr
        _ = _ := by ring
    exact hIntComp.trans hIntRed
  have hcMD0 : 0 ≤ cMDval' P 0 := cMDval'_nonneg P 0
  have hQnonneg : 0 ≤ cMDval' P 0 * ∫ u in (s N)..v, f u := by
    apply mul_nonneg hcMD0
    exact intervalIntegral.integral_nonneg hv.1 (fun u _ => momNorm_nonneg _ _ _)
  have hQbound : B.scale E N v ^ 4 *
      (cMDval' P 0 * ∫ u in (s N)..v, f u) ≤
        (1 + cMDval' P 0 * Cqv) ^ 2 *
          ((N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [show B.scale E N v ^ 4 *
        (cMDval' P 0 * ∫ u in (s N)..v, f u) =
        cMDval' P 0 * (B.scale E N v ^ 4 * ∫ u in (s N)..v, f u) by ring]
    have hcoef : cMDval' P 0 * Cqv ≤ (1 + cMDval' P 0 * Cqv) ^ 2 := hCqvDom
    have hcoef0 : 0 ≤ cMDval' P 0 := hcMD0
    have hpowN : ((N : ℝ) ^ (ε / 4)) ^ 2 = (N : ℝ) ^ (ε / 2) := by
      calc
        ((N : ℝ) ^ (ε / 4)) ^ 2 = ((N : ℝ) ^ (ε / 4)) ^ (2 : ℝ) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (ε / 4)) 2]
          rfl
        _ = (N : ℝ) ^ ((ε / 4) * (2 : ℝ)) := by
          rw [← Real.rpow_mul (by positivity)]
        _ = (N : ℝ) ^ (ε / 2) := by rw [show (ε / 4) * (2 : ℝ) = ε / 2 by ring]
    have hpowA : (B.scale E N (s N) ^ ((1 : ℝ) / 3)) ^ 2 =
        B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := hAsPowerSq
    have hfactor : 0 ≤ (N : ℝ) ^ (ε / 2) *
        B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6) := by positivity
    calc
      cMDval' P 0 * (B.scale E N v ^ 4 * ∫ u in (s N)..v, f u) ≤
          cMDval' P 0 * (Cqv * ((N : ℝ) ^ (ε / 2) *
            B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6))) :=
        by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hIntUpper hcMD0
      _ = (cMDval' P 0 * Cqv) * ((N : ℝ) ^ (ε / 2) *
          B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6)) := by ring
      _ ≤ (1 + cMDval' P 0 * Cqv) ^ 2 * ((N : ℝ) ^ (ε / 2) *
          B.scale E N (s N) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_right hcoef hfactor
      _ = (1 + cMDval' P 0 * Cqv) ^ 2 *
          ((N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 3)) ^ 2 := by
        rw [mul_pow, hpowN, hpowA]
  have hTnonneg : 0 ≤ (1 + cMDval' P 0 * Cqv) *
      ((N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 3)) := by positivity
  have hleftnonneg : 0 ≤ B.scale E N v ^ 2 *
      Real.sqrt (cMDval' P 0 * ∫ u in (s N)..v, f u) := by positivity
  have hleftSq : (B.scale E N v ^ 2 *
      Real.sqrt (cMDval' P 0 * ∫ u in (s N)..v, f u)) ^ 2 ≤
        ((1 + cMDval' P 0 * Cqv) *
          ((N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 3))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQnonneg]
    nlinarith [hQbound]
  have hfinal := (sq_le_sq₀ hleftnonneg hTnonneg).1 hleftSq
  simpa [f, Cqv, Real.sqrt_eq_rpow, mul_assoc] using hfinal

/-- The actual all-charge QV bound on the prescribed `meshK 21 (1/2)` net.  The endpoint
`v = s N` is included, and the scale exponent is raised from `1/3` to `1/2` using the eventual
lower bound `A_s ≥ 1` from (2.72). -/
theorem actual_qv_integral_bound_net
    {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N, ∀ q : LoopData (d.L N) 2,
          B.scale E N v ^ 2 *
            (cMDval' P 0 * ∫ u in (s N)..v, momNorm B.P P (fun ω =>
              ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (eeFun B E N u ((sample d).H N u ω) q.1)
                (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
              ≤ C * (N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 2) := by
  intro ε hε P hP
  obtain ⟨C, hC, hN⟩ :=
    actual_qv_integral_bound hE hs0 hst ht1 hc hreg hB ε hε P hP
  have hAsEvent : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (s N) := by
    filter_upwards [hreg.2, eventually_ge_atTop (1 : ℕ)] with N hregN hN1
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNc : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hNreal hc.le
    have hW0 : 0 ≤ (B.W N : ℝ) := by positivity
    have hAtAs : B.scale E N (t N) ≤ B.scale E N (s N) := by
      rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
      exact flowScale_antitoneOn hW0 (B.L N) E
        (Set.mem_Iic.mpr ((hst N).trans_lt (ht1 N)).le)
        (Set.mem_Iic.mpr (ht1 N).le) (hst N)
    exact hNc.trans (hregN.trans hAtAs)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hN, hAsEvent] with N hN hAs1
  intro v hv q
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hst N) (meshK_pos 21 ((1 : ℝ) / 2) N) v hv
  have hbase := hN v hvIcc q
  have hpow : B.scale E N (s N) ^ ((1 : ℝ) / 3) ≤
      B.scale E N (s N) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hAs1 (by norm_num)
  calc
    _ ≤ C * (N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 3) := hbase
    _ ≤ C * (N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Explicit left-endpoint specialization of the net theorem.  This records directly that the
closed net includes `s N`; it does not require a positive Duhamel interval. -/
theorem actual_qv_integral_bound_at_left
    {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ q : LoopData (d.L N) 2,
          B.scale E N (s N) ^ 2 *
            (cMDval' P 0 * ∫ u in (s N)..s N, momNorm B.P P (fun ω =>
              ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((s N : ℝ) : ℂ)
                (eeFun B E N u ((sample d).H N u ω) q.1)
                (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
              ≤ C * (N : ℝ) ^ (ε / 4) * B.scale E N (s N) ^ ((1 : ℝ) / 2) := by
  intro ε hε P hP
  obtain ⟨C, hC, hN⟩ :=
    actual_qv_integral_bound_net hE hs0 hst ht1 hc hreg hB ε hε P hP
  refine ⟨C, hC, hN.mono fun N hN q => ?_⟩
  have hsMem : s N ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N := by
    simpa [CutHypTheta.cutNetPt_zero] using
      (CutHypTheta.cutNetPt_mem_netFinset (s := s) (t := t)
        (mesh := meshK 21 ((1 : ℝ) / 2)) (N := N) (k := 0) (Nat.zero_le _))
  simpa using hN (s N) hsMem q

/-- The full T1341 family and its actual interval-integrability premise are simultaneously
satisfiable on the noncollapsed exampleGrow window with incoming Gaussian `BoundsCore`.  The
positive net endpoint is retained from the same window witness. -/
theorem actual_qv_joint_window_witness :
    ∃ s t : ℕ → ℝ, ∃ c : ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      0 < c ∧ Cond272Reg B 0 s t c ∧ BoundsCore (sample d) 0 s ∧
      (∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
        ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
          ∀ v ∈ Set.Icc (s N) (t N), ∀ q : LoopData (d.L N) 2,
            B.scale 0 N v ^ 2 *
              (cMDval' P 0 * ∫ u in (s N)..v, momNorm B.P P (fun ω =>
                ‖Uker (d.L N) (SumZeroDyn.xi2 0 q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (eeFun B 0 N u ((sample d).H N u ω) q.1)
                  (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
                ≤ C * (N : ℝ) ^ (ε / 4) * B.scale 0 N (s N) ^ ((1 : ℝ) / 3)) ∧
      (∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
        ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
          ∀ v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N, ∀ q : LoopData (d.L N) 2,
            B.scale 0 N v ^ 2 *
              (cMDval' P 0 * ∫ u in (s N)..v, momNorm B.P P (fun ω =>
                ‖Uker (d.L N) (SumZeroDyn.xi2 0 q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                  (eeFun B 0 N u ((sample d).H N u ω) q.1)
                  (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
                ≤ C * (N : ℝ) ^ (ε / 4) * B.scale 0 N (s N) ^ ((1 : ℝ) / 2)) ∧
      (∀ N, ∀ v ∈ Set.Icc (s N) (t N), ∀ q : LoopData (d.L N) 2, ∀ P : ℕ,
        IntervalIntegrable (fun u : ℝ => momNorm B.P P (fun ω =>
          ‖Uker (d.L N) (SumZeroDyn.xi2 0 q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (eeFun B 0 N u ((sample d).H N u ω) q.1) (Fin.append q.2 q.2)‖))
          volume (s N) v) ∧
      (∀ᶠ N : ℕ in atTop,
        ∃ v ∈ netFinset s t (meshK 21 ((1 : ℝ) / 2)) N, s N < v) ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ᶠ N : ℕ in atTop, 0 < Step3.flowAs B 0 s N ^ ((1 : ℝ) / 2)) ∧
      HighProb B.P
        (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}) ∧
      ∀ᶠ N : ℕ in atTop,
        {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}.Nonempty := by
  obtain ⟨s, t, c, hs0, hst, ht1, hc, hreg, hB, hlen, hnet, htheta, hHP, hnonempty⟩ :=
    XiLKTwoCutModulus.exampleGrow_joint_window_witness
  have hfamily := actual_qv_integral_bound (E := (0 : ℝ)) (by norm_num)
    hs0 hst ht1 hc hreg hB
  have hnetFamily := actual_qv_integral_bound_net (E := (0 : ℝ)) (by norm_num)
    hs0 hst ht1 hc hreg hB
  have hint : ∀ N, ∀ v ∈ Set.Icc (s N) (t N), ∀ q : LoopData (d.L N) 2, ∀ P : ℕ,
      IntervalIntegrable (fun u : ℝ => momNorm B.P P (fun ω =>
        ‖Uker (d.L N) (SumZeroDyn.xi2 0 q.1) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (eeFun B 0 N u ((sample d).H N u ω) q.1) (Fin.append q.2 q.2)‖))
        volume (s N) v := by
    intro N v hv q P
    exact intervalIntegrable_actual_qv_integrand (N := N) (s := s N) (v := v)
      (by norm_num) hv.1 (hv.2.trans_lt (ht1 N)) q P
  exact ⟨s, t, c, hs0, hst, ht1, hc, hreg, hB, hfamily, hnetFamily,
    hint, hnet, hlen, htheta, hHP, hnonempty⟩

#print axioms intervalIntegrable_actual_qv_integrand
#print axioms actual_qv_integral_bound
#print axioms actual_qv_integral_bound_net
#print axioms actual_qv_integral_bound_at_left
#print axioms actual_qv_joint_window_witness

end
end RBM.Gauss.XiLKTwoCutQV

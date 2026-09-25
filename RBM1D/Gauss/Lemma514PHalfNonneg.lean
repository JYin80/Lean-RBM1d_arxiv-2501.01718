/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514QAssembly
import RBM1D.Gauss.DimsExample

/-!
# The nonnegative-start P half of Lemma 5.14

This file removes the surplus strict-start condition from the Ward/P-half route while retaining
the `QGood` charge guard. Its deterministic input is (5.96), its random input is precisely the
`m = n + 1` lower-order clause of `Lemma514Premises`, and its endpoint estimate is (5.101).
-/

namespace RBM

open MeasureTheory Filter

namespace SumZeroDyn

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The (5.101) P term, from Ward's identity (5.96) and the `m=n+1` slot, with a
nonnegative start time. -/
theorem termP_nonneg (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hW : WardP X E n) (hdec : LKDecay X E s t)
    {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N)) :
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      if QGood p.2.1 then B.scale E N p.1 ^ (n + 2)
        * (‖Psum (B.L N) (lkT X E N p.1 ω p.2.1) (p.2.2 0)‖
          * ‖vartheta (B.L N) ((p.1 : ℝ) : ℂ) p.2.2‖)
      else 0) (fun N _ _ => 1 + Φ N) := by
  classical
  refine stochDom_of_good fun τ hτ => ?_
  set τ₁ := τ / (2 * (n + 2)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  set D : ℝ := 2 * n + 3 + τ₁ with hD
  have hG1 := good_of_stochDom hX hτ₁0
  have hG2 := good_of_stochDom (hdec (n + 1) (by omega) τ₁ hτ₁0 D (by positivity)) hτ₁0
  refine ⟨_, hG1.inter hG2, ?_⟩
  have ha : τ₁ * (n + 1) < τ := by
    rw [hτ₁, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hfin := eventually_finish ((6 * Real.exp 1) ^ n * cTwo52 ^ (n + 1))
    (2 ^ n * cTwo52 ^ (n + 1)) ha
    (show (2 * n + 1 : ℝ) + τ₁ < D by rw [hD]; linarith)
  filter_upwards [flow_crude hE hs0 hst ht1 hc, hfin] with N
    ⟨hLN, hWN, hN1, hu⟩ ⟨hf1, hf2⟩
  intro ω ⟨hω1, hω2⟩ p
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNτ : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hNτ₁ : 1 ≤ (N : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  split_ifs with hq
  · obtain ⟨σ', σ'', hw⟩ := hW p.2.1 hq
    set u : ℝ := (p.1 : ℝ) with hudef
    have hu0 : 0 ≤ u := (hs0 N).trans p.1.2.1
    have hu1 : u < 1 := p.1.2.2.trans_lt (ht1 N)
    obtain ⟨hA1, hAN, -⟩ := hu p.1
    have hA0 : 0 < B.scale E N u := by linarith
    have hL3 := B.three_le_L N
    have hℓ := half_le_ellHat_real (B.L N) hL3 hu0 hu1
    have hℓ0 : 0 < B.ell N u := by
      change 0 < ellHat (B.L N) (u : ℂ)
      linarith
    have hbd : ∀ (ρ : Fin (n + 1) → Bool) b,
        ‖lkT X E N u ω ρ b‖ ≤ (N : ℝ) ^ τ₁ * Φ N * (B.scale E N u)⁻¹ ^ (n + 1) :=
      fun ρ b => norm_lkT_le_of_xiLK X ρ b hA0 (hω1 p.1)
    have hfd : ∀ ρ : Fin (n + 1) → Bool,
        FastDecay (B.L N) (B.ell N u * (N : ℝ) ^ τ₁)
          ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) (lkT X E N u ω ρ) :=
      fun ρ => fastDecay_of_farInd fun b => hω2 (p.1, (ρ, b))
    have hΦN := hΦ N
    have hP := norm_Psum_le_of_ward (B.L N)
      (hw N u hu0 hu1 ω (p.2.2 0)) (mul_pos hℓ0 (by positivity))
      (by positivity) (by positivity)
      (hbd σ') (hbd σ'') (hfd σ') (hfd σ'')
    rw [norm_wardKappa (B.W N) hE hu1] at hP
    have hϑ := norm_vartheta_real_le (B.L N) hL3 hu0 hu1 p.2.2
    have hη := etaT_pos hE hu1
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have key := scalarP (n := n) (A := B.scale E N u) (W := B.W N) (η := etaT E u)
      (ℓ := B.ell N u) (Lr := B.L N) (K := (N : ℝ) ^ τ₁)
      (Φ := Φ N) (δ := (N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) rfl hW0 hη hℓ
      hNτ₁ hΦN (by positivity) cTwo52_pos.le (Nat.cast_nonneg _)
    have hpos : 0 ≤ B.scale E N u ^ (n + 2) := by positivity
    calc B.scale E N u ^ (n + 2) *
          (‖Psum (B.L N) (lkT X E N u ω p.2.1) (p.2.2 0)‖ *
            ‖vartheta (B.L N) (u : ℂ) p.2.2‖)
        ≤ B.scale E N u ^ (n + 2) *
          (((2 * (B.W N : ℝ) * etaT E u)⁻¹ *
            (2 * ((2 * Real.exp 1 * (B.ell N u * (N : ℝ) ^ τ₁ + 1)) ^ n *
                ((N : ℝ) ^ τ₁ * Φ N * (B.scale E N u)⁻¹ ^ (n + 1)) +
              (B.L N : ℝ) ^ n * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D))))) *
            (cTwo52 / B.ell N u) ^ (n + 1)) := by
              refine mul_le_mul_of_nonneg_left
                (mul_le_mul hP hϑ (norm_nonneg _) ?_) hpos
              positivity
      _ ≤ (6 * Real.exp 1) ^ n * cTwo52 ^ (n + 1) *
            ((N : ℝ) ^ τ₁) ^ (n + 1) * Φ N +
          2 ^ n * cTwo52 ^ (n + 1) * B.scale E N u ^ (n + 1) *
            (B.L N : ℝ) ^ n * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) := key
      _ ≤ (N : ℝ) ^ τ * Φ N + 1 := by
          refine add_le_add ?_ ?_
          · rw [rpow_pow_eq]
            have : ((6 * Real.exp 1) ^ n * cTwo52 ^ (n + 1) *
                (N : ℝ) ^ (τ₁ * ((n + 1 : ℕ) : ℝ))) ≤ (N : ℝ) ^ τ := by
              push_cast
              exact hf1
            exact mul_le_mul_of_nonneg_right this hΦN
          · have h1 := natCast_pow_le_rpow hA0.le hAN (n + 1)
            have h2 := natCast_pow_le_rpow (Nat.cast_nonneg _) hLN n
            have hc0 : 0 ≤ 2 ^ n * cTwo52 ^ (n + 1) := by
              have := cTwo52_pos
              positivity
            have e : (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) *
                (N : ℝ) ^ ((n : ℕ) : ℝ) * (N : ℝ) ^ τ₁ =
                (N : ℝ) ^ ((2 * n + 1 : ℝ) + τ₁) := by
              rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
              congr 1
              push_cast
              ring
            calc 2 ^ n * cTwo52 ^ (n + 1) * B.scale E N u ^ (n + 1) *
                  (B.L N : ℝ) ^ n * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D))
                ≤ 2 ^ n * cTwo52 ^ (n + 1) * (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) *
                  (N : ℝ) ^ ((n : ℕ) : ℝ) * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) := by
                    gcongr
              _ = 2 ^ n * cTwo52 ^ (n + 1) *
                    ((N : ℝ) ^ ((n + 1 : ℕ) : ℝ) * (N : ℝ) ^ ((n : ℕ) : ℝ) *
                      (N : ℝ) ^ τ₁) * (N : ℝ) ^ (-D) := by ring
              _ = 2 ^ n * cTwo52 ^ (n + 1) *
                    (N : ℝ) ^ ((2 * n + 1 : ℝ) + τ₁) * (N : ℝ) ^ (-D) := by rw [e]
              _ ≤ 1 := hf2
      _ ≤ (N : ℝ) ^ τ * (1 + Φ N) := by nlinarith
  · have := hΦ N
    positivity

end SumZeroDyn

namespace Gauss

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

omit [IsProbabilityMeasure B.P] in
/-- The QGood-guarded terminal-time estimate (5.101), with its nonnegative-start hypothesis. -/
theorem stochDom_Psum_vartheta_qGood_nonneg (X : Sample B) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t) (hW : SumZeroDyn.WardP X E n)
    (hdec : SumZeroDyn.LKDecay X E s t) {Λ Φ : ℕ → ℝ}
    (hΛ0 : ∀ N, 0 ≤ Λ N) (hΦ0 : ∀ N, 0 ≤ Φ N)
    (hΛ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Λ N)
    (hXi : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N))
    (v : ℕ → ℝ) (hv : ∀ N, v N ∈ Set.Icc (s N) (t N)) :
    StochDom B.P
      (fun N (w : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood w.1 then
          ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω w.1) (w.2 0)‖ *
          ‖vartheta (B.L N) ((v N : ℝ) : ℂ) w.2‖
        else 0)
      (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) *
        (B.scale E N (v N) ^ (n + 2))⁻¹) := by
  classical
  have hA : ∀ N, 0 < B.scale E N (v N) ^ (n + 2) := fun N =>
    pow_pos (B.scale_pos' hE N ((hs0 N).trans (hv N).1) ((hv N).2.trans_lt (ht1 N))) _
  have hPw := (SumZeroDyn.termP_nonneg X hE hs0 hst ht1 hcond hW hdec hΦ0 hXi).precomp_param
    (V := fun N => LoopData (B.L N) (n + 2))
    (fun N w => ((⟨v N, (hv N).1, (hv N).2⟩ : TimeIcc s t N), w))
  have hsc := stochDom_scale (c := fun N (_ : LoopData (B.L N) (n + 2)) =>
      (B.scale E N (v N) ^ (n + 2))⁻¹) (fun N _ => inv_pos.2 (hA N)) hPw
  refine StochDom.of_le_left (fun N w ω => ?_)
    (Step3.stochDom_mono (fun N w ω => ?_) 1 ?_ hsc)
  · split_ifs with h
    · rw [← mul_assoc, inv_mul_cancel₀ (hA N).ne', one_mul]
    · rw [mul_zero]
  · have h1 : (0 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 N) _
    have := hΦ0 N
    have := hA N
    positivity
  · filter_upwards [hΛ1] with N hN w ω
    have h1 : (1 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have h2 : (0 : ℝ) < (B.scale E N (v N) ^ (n + 2))⁻¹ := inv_pos.2 (hA N)
    have h3 : (1 : ℝ) + Φ N ≤ Λ N ^ ((1 : ℝ) / 2) + Φ N := by linarith
    calc (B.scale E N (v N) ^ (n + 2))⁻¹ * (1 + Φ N)
        ≤ (B.scale E N (v N) ^ (n + 2))⁻¹ *
          (Λ N ^ ((1 : ℝ) / 2) + Φ N) := mul_le_mul_of_nonneg_left h3 h2.le
      _ = 1 * ((Λ N ^ ((1 : ℝ) / 2) + Φ N) *
          (B.scale E N (v N) ^ (n + 2))⁻¹) := by ring

omit [IsProbabilityMeasure B.P] in
/-- The nonnegative-start P-half consumer in the exact `PHalf514` shape. -/
theorem pHalf514_of_wardP_nonneg (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hW : SumZeroDyn.WardP X E n) (hdec : SumZeroDyn.LKDecay X E s t) :
    PHalf514 X E s t n := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  exact stochDom_Psum_vartheta_qGood_nonneg X hE hs0 hst ht1 hcond hW hdec
    hΛ0 hΦ0 hΛ1 (hprem.2.1 (n + 1) (by omega) (by omega)) v hv

/-- The actual Gaussian specialization: Ward's premise is supplied by `wardP_holds`. -/
theorem pHalf514_of_gaussian_wardP_nonneg (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t)
    (hdec : SumZeroDyn.LKDecay (sample d) E s t) :
    PHalf514 (sample d) E s t n := by
  letI : IsProbabilityMeasure (band d).P := by rw [band_P]; infer_instance
  exact pHalf514_of_wardP_nonneg (sample d) hE hs0 hst ht1 hcond
    (SumZeroDyn.wardP_holds (sample d) hE n) hdec

/-! ### An actual fixed-block witness for all inputs of `PHalf514` -/

noncomputable def t1347WitnessD : Dims := Dims.«example»
noncomputable def t1347WitnessB : Band (RBM.Gauss.Ω t1347WitnessD) :=
  band t1347WitnessD
noncomputable def t1347WitnessX : Sample t1347WitnessB := sample t1347WitnessD

/-- The positive-length interval used in the satisfiability witness. -/
noncomputable def t1347WitnessS : ℕ → ℝ := fun _ => 0

/-- The positive-length interval used in the satisfiability witness. -/
noncomputable def t1347WitnessT : ℕ → ℝ := fun _ => 1 / 2

/-- An interior endpoint of the nonempty witness interval. -/
noncomputable def t1347WitnessV : ℕ → ℝ := fun _ => 1 / 4

/-- Explicit constant envelope for the length-eight Gaussian loop moment. -/
noncomputable def t1347WitnessLambda : ℕ → ℝ := fun _ => 5000

noncomputable def t1347WitnessK : ℝ :=
  Classical.choose (exists_norm_Kval_le_upto_one t1347WitnessB
    (by norm_num : |(0 : ℝ)| < 2) 3)

private theorem t1347WitnessK_nonneg : 0 ≤ t1347WitnessK :=
  (Classical.choose_spec (exists_norm_Kval_le_upto_one t1347WitnessB
    (by norm_num : |(0 : ℝ)| < 2) 3)).1

private theorem t1347WitnessK_bound :
    ∀ (N : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
      ∀ J : LoopIdx (ZMod (t1347WitnessB.L N)), J.WF →
        1 ≤ J.length → J.length ≤ 3 →
          ‖t1347WitnessB.Kval 0 N u J‖ ≤
            t1347WitnessK * (t1347WitnessB.scale 0 N u)⁻¹ ^ (J.length - 1) :=
  (Classical.choose_spec (exists_norm_Kval_le_upto_one t1347WitnessB
    (by norm_num : |(0 : ℝ)| < 2) 3)).2

/-- Explicit positive polynomial envelope for the three lower-order `L-K` clauses. -/
noncomputable def t1347WitnessPhi (N : ℕ) : ℝ :=
  10000 * (1 + t1347WitnessK) ^ 2 *
    ((N : ℝ) + 1) ^ 2

private theorem t1347WitnessEta (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    etaT 0 u = 1 - u ∧ (1 / 2 : ℝ) ≤ etaT 0 u ∧ etaT 0 u ≤ 1 := by
  have he : etaT 0 u = 1 - u := by
    rw [etaT, mE_im]
    rw [show (4 : ℝ) - (0 : ℝ) ^ 2 = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  constructor
  · exact he
  constructor
  · rw [he]
    linarith
  · rw [he]
    linarith

private theorem t1347Witness_scale_eq (N : ℕ) (u : ℝ) :
    t1347WitnessB.scale 0 N u =
      (t1347WitnessB.W N : ℝ) * ellHat 3 (u : ℂ) * etaT 0 u := by
  calc
    t1347WitnessB.scale 0 N u =
        (t1347WitnessB.W N : ℝ) * t1347WitnessB.ell N u * etaT 0 u := rfl
    _ = (t1347WitnessB.W N : ℝ) * ellHat 3 (u : ℂ) * etaT 0 u := by
      simp [t1347WitnessB, t1347WitnessD, band_L, Dims.example_L, Band.ell]

private theorem t1347Witness_window_bounds (N : ℕ)
    (p : TimeIcc t1347WitnessS t1347WitnessT N) :
    0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 1 / 2 ∧
      1 ≤ ellHat 3 ((p : ℝ) : ℂ) ∧ ellHat 3 ((p : ℝ) : ℂ) ≤ 3 ∧
      (1 / 2 : ℝ) ≤ etaT 0 (p : ℝ) ∧ etaT 0 (p : ℝ) ≤ 1 := by
  have hu0 : 0 ≤ (p : ℝ) := p.2.1
  have hu1 : (p : ℝ) ≤ 1 / 2 := p.2.2
  have hu1' : (p : ℝ) < 1 := lt_of_le_of_lt hu1 (by norm_num)
  have hη := t1347WitnessEta (p : ℝ) hu0 hu1
  refine ⟨hu0, hu1, ?_, ?_, hη.2.1, hη.2.2⟩
  · exact one_le_ellHat_of_nonneg (by norm_num) hu0 hu1'
  · exact (SumZeroDyn.ellHat_real_le_L hu1').trans_eq (by norm_num)

/-- On the actual Gaussian model with `L=3`, the resolvent loop moment is deterministically
bounded on the whole first half-window. This uses only Hermitian resolvent bounds. -/
private theorem t1347Witness_xiL_bound (m : ℕ) (hm : 1 ≤ m) :
    ∀ N (p : TimeIcc t1347WitnessS t1347WitnessT N)
      (ω : RBM.Gauss.Ω t1347WitnessD),
      Step3.flowXiL t1347WitnessX 0 t1347WitnessS t1347WitnessT m N p ω
        ≤ 2 * 3 ^ (m - 1) := by
  intro N p ω
  let u : ℝ := (p : ℝ)
  have hu0 : 0 ≤ u := p.2.1
  have hu1h : u ≤ 1 / 2 := p.2.2
  have hu1 : u < 1 := lt_of_le_of_lt hu1h (by norm_num)
  have ⟨_, _, hℓlo, hℓhi, hηlo, hηhi⟩ := t1347Witness_window_bounds N p
  have hη : 0 < etaT 0 u := by linarith
  have hW : (1 : ℝ) ≤ (t1347WitnessB.W N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (t1347WitnessB.W_pos N).ne')
  have hscale := t1347Witness_scale_eq N u
  have hscale0 : 0 < t1347WitnessB.scale 0 N u := by rw [hscale]; positivity
  have hLoop := loopXi_le_det (t1347WitnessX.hermitian N u ω)
    (by norm_num : |(0 : ℝ)| < 2) hu1 hscale0.le hm
  have hηinv : (etaT 0 u)⁻¹ ≤ 2 := by
    calc (etaT 0 u)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by linarith) hηlo
      _ = 2 := by norm_num
  have hℓpow : ellHat 3 (u : ℂ) ^ (m - 1) ≤ (3 : ℝ) ^ (m - 1) :=
    pow_le_pow_left₀ (by positivity) hℓhi _
  have hsimple :
      (etaT 0 u)⁻¹ ^ m * (t1347WitnessB.W N : ℝ)⁻¹ ^ (m - 1) *
          t1347WitnessB.scale 0 N u ^ (m - 1) =
        (etaT 0 u)⁻¹ * ellHat 3 (u : ℂ) ^ (m - 1) := by
    rw [hscale]
    have hm' : m = (m - 1) + 1 := by omega
    rw [hm', pow_succ]
    rw [mul_pow, mul_pow]
    have hWpos : (0 : ℝ) < (t1347WitnessB.W N : ℝ) := by
      exact_mod_cast t1347WitnessB.W_pos N
    field_simp [ne_of_gt hWpos, ne_of_gt hη]
    rw [show (m - 1) + 1 - 1 = m - 1 by omega]
    rw [← mul_pow, ← mul_pow]
    simp only [one_div]
    change (((etaT 0 u)⁻¹ * (t1347WitnessB.W N : ℝ)⁻¹ *
        (t1347WitnessB.W N : ℝ)) ^ (m - 1)) *
      ellHat 3 (u : ℂ) ^ (m - 1) * etaT 0 u ^ (m - 1) =
        ellHat 3 (u : ℂ) ^ (m - 1)
    have hWpos : (0 : ℝ) < (t1347WitnessB.W N : ℝ) := by
      exact_mod_cast t1347WitnessB.W_pos N
    have hbase : (etaT 0 u)⁻¹ * (t1347WitnessB.W N : ℝ)⁻¹ *
        (t1347WitnessB.W N : ℝ) = (etaT 0 u)⁻¹ := by
      rw [mul_assoc, inv_mul_cancel₀ hWpos.ne', mul_one]
    rw [hbase]
    calc (etaT 0 u)⁻¹ ^ (m - 1) * ellHat 3 (u : ℂ) ^ (m - 1) * etaT 0 u ^ (m - 1)
        = (etaT 0 u)⁻¹ ^ (m - 1) * etaT 0 u ^ (m - 1) *
            ellHat 3 (u : ℂ) ^ (m - 1) := by ring
      _ = ((etaT 0 u)⁻¹ * etaT 0 u) ^ (m - 1) *
            ellHat 3 (u : ℂ) ^ (m - 1) := by rw [← mul_pow]
      _ = ellHat 3 (u : ℂ) ^ (m - 1) := by
            rw [inv_mul_cancel₀ hη.ne', one_pow, one_mul]
  change loopXi (t1347WitnessB.L N) (t1347WitnessB.W N)
      (t1347WitnessX.H N u ω) (zt 0 u) (t1347WitnessB.scale 0 N u) m ≤ _
  calc loopXi (t1347WitnessB.L N) (t1347WitnessB.W N)
        (t1347WitnessX.H N u ω) (zt 0 u) (t1347WitnessB.scale 0 N u) m
      ≤ (etaT 0 u)⁻¹ ^ m * (t1347WitnessB.W N : ℝ)⁻¹ ^ (m - 1) *
          t1347WitnessB.scale 0 N u ^ (m - 1) := hLoop
    _ = (etaT 0 u)⁻¹ * ellHat 3 (u : ℂ) ^ (m - 1) := hsimple
    _ ≤ 2 * 3 ^ (m - 1) := by
      exact mul_le_mul hηinv hℓpow (by positivity) (by positivity)

private theorem t1347Witness_pointwise_stochDom
    {U : ℕ → Type*} {ξ ζ : ∀ N, U N → RBM.Gauss.Ω t1347WitnessD → ℝ}
    (hle : ∀ N u ω, ξ N u ω ≤ ζ N u ω)
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω) :
    StochDom t1347WitnessB.P ξ ζ :=
  StochDom.of_le_left hle (StochDom.refl hζ)

private theorem t1347Witness_scale_bounds (N : ℕ)
    (p : TimeIcc t1347WitnessS t1347WitnessT N) :
    (1 / 2 : ℝ) ≤ t1347WitnessB.scale 0 N (p : ℝ) ∧
      t1347WitnessB.scale 0 N (p : ℝ) ≤ 3 * ((N : ℝ) + 1) := by
  have ⟨_, _, hℓlo, hℓhi, hηlo, hηhi⟩ := t1347Witness_window_bounds N p
  have hWlo : (1 : ℝ) ≤ (t1347WitnessB.W N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (t1347WitnessB.W_pos N).ne')
  have hWnat : t1347WitnessB.W N ≤ N + 1 := by
    simp [t1347WitnessB, t1347WitnessD, Dims.example_W]
    omega
  have hWhi : (t1347WitnessB.W N : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hWnat
  rw [t1347Witness_scale_eq]
  constructor
  · calc (1 / 2 : ℝ) = 1 * 1 * (1 / 2) := by ring
      _ ≤ (t1347WitnessB.W N : ℝ) * ellHat 3 ((p : ℝ) : ℂ) * etaT 0 (p : ℝ) := by
        gcongr
  · calc (t1347WitnessB.W N : ℝ) * ellHat 3 ((p : ℝ) : ℂ) * etaT 0 (p : ℝ)
        ≤ ((N : ℝ) + 1) * 3 * 1 := by gcongr
      _ = 3 * ((N : ℝ) + 1) := by ring

private theorem t1347Witness_xiLK_bound (m : ℕ) (hm : 1 ≤ m) (hm3 : m ≤ 3) :
    ∀ N (p : TimeIcc t1347WitnessS t1347WitnessT N)
      (ω : RBM.Gauss.Ω t1347WitnessD),
      Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT m N p ω ≤
        54 * (1 + t1347WitnessK) * ((N : ℝ) + 1) := by
  intro N p ω
  let u : ℝ := (p : ℝ)
  have hscale0 : 0 < t1347WitnessB.scale 0 N u := by
    exact lt_of_lt_of_le (by norm_num) (t1347Witness_scale_bounds N p).1
  have hxiL := t1347Witness_xiL_bound m hm N p ω
  have hK : ∀ q : LoopData (t1347WitnessB.L N) m,
      ‖t1347WitnessB.Kval 0 N u q.idx‖ ≤
        t1347WitnessK * (t1347WitnessB.scale 0 N u)⁻¹ ^ (m - 1) := by
    intro q
    have hu1 : (p : ℝ) < 1 := lt_of_le_of_lt p.2.2 (by norm_num [t1347WitnessT])
    simpa only [LoopData.idx_length] using
      (t1347WitnessK_bound N u p.2.1 hu1 q.idx q.idx_wf
        (by simpa using hm) (by simpa using hm3))
  have hraw := t1347WitnessX.xiLK_le_mul (E := 0) (N := N) (t := u)
    (ω := ω) (m := m) hscale0 hm hK
  have hscaleHi := (t1347Witness_scale_bounds N p).2
  have hxiL18 : t1347WitnessX.xiL 0 N u ω m ≤ 18 := by
    have h := t1347Witness_xiL_bound m hm N p ω
    have hxi : t1347WitnessX.xiL 0 N u ω m ≤ 2 * 3 ^ (m - 1) := by
      simpa [Step3.flowXiL, u] using h
    interval_cases m <;> norm_num at hm hxi ⊢ <;> linarith
  have hmain : t1347WitnessX.xiLK 0 N u ω m ≤
      3 * ((N : ℝ) + 1) * (18 + t1347WitnessK) := by
    calc t1347WitnessX.xiLK 0 N u ω m
        ≤ t1347WitnessB.scale 0 N u * (t1347WitnessX.xiL 0 N u ω m + t1347WitnessK) := hraw
      _ ≤ 3 * ((N : ℝ) + 1) * (18 + t1347WitnessK) := by
        have hK0 := t1347WitnessK_nonneg
        have hfactor : 0 ≤ t1347WitnessX.xiL 0 N u ω m + t1347WitnessK := by
          exact add_nonneg (t1347WitnessX.xiL_nonneg hscale0.le) hK0
        exact mul_le_mul (t1347Witness_scale_bounds N p).2
          (add_le_add hxiL18 (le_refl t1347WitnessK)) hfactor (by positivity)
  have hcoeff : 3 * (18 + t1347WitnessK) ≤ 54 * (1 + t1347WitnessK) := by
    nlinarith [t1347WitnessK_nonneg]
  have hN : 0 ≤ (N : ℝ) + 1 := by positivity
  have hfinal : 3 * ((N : ℝ) + 1) * (18 + t1347WitnessK) ≤
      54 * (1 + t1347WitnessK) * ((N : ℝ) + 1) := by nlinarith
  change t1347WitnessX.xiLK 0 N u ω m ≤ _
  exact hmain.trans hfinal

private theorem t1347Witness_Phi_nonneg (N : ℕ) : 0 ≤ t1347WitnessPhi N := by
  have hK0 := t1347WitnessK_nonneg
  have hN : 0 ≤ (N : ℝ) + 1 := by positivity
  dsimp [t1347WitnessPhi]
  positivity

private theorem t1347Witness_Phi_dominates_xiLK (m : ℕ) (hm : 1 ≤ m) (hm3 : m ≤ 3) :
    ∀ N (p : TimeIcc t1347WitnessS t1347WitnessT N)
      (ω : RBM.Gauss.Ω t1347WitnessD),
      Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT m N p ω ≤
        t1347WitnessPhi N := by
  intro N p ω
  have h := t1347Witness_xiLK_bound m hm hm3 N p ω
  have hK0 := t1347WitnessK_nonneg
  dsimp [t1347WitnessPhi]
  have hY : 1 ≤ (1 + t1347WitnessK) * ((N : ℝ) + 1) := by
    have hN : 1 ≤ (N : ℝ) + 1 := by
      have hn : 1 ≤ N + 1 := by omega
      exact_mod_cast hn
    nlinarith
  have hY' : 54 * ((1 + t1347WitnessK) * ((N : ℝ) + 1)) ≤
      10000 * ((1 + t1347WitnessK) * ((N : ℝ) + 1)) ^ 2 := by
    nlinarith [sq_nonneg ((1 + t1347WitnessK) * ((N : ℝ) + 1) - 1)]
  nlinarith [hY', hY]

private theorem t1347Witness_xiLK_product_dom :
    StochDom t1347WitnessB.P
      (fun N (p : TimeIcc t1347WitnessS t1347WitnessT N) ω =>
        Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 2 N p ω *
          Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 3 N p ω *
            (Step3.flowA t1347WitnessB 0 t1347WitnessS t1347WitnessT N p)⁻¹)
      (fun N _ _ => t1347WitnessPhi N) := by
  apply t1347Witness_pointwise_stochDom
  · intro N p ω
    have h2 := t1347Witness_xiLK_bound 2 (by omega) (by omega) N p ω
    have h3 := t1347Witness_xiLK_bound 3 (by omega) (by omega) N p ω
    have hscale := t1347Witness_scale_bounds N p
    have hscalePos : 0 < t1347WitnessB.scale 0 N (p : ℝ) := by
      exact lt_of_lt_of_le (by norm_num) hscale.1
    have hinv : (t1347WitnessB.scale 0 N (p : ℝ))⁻¹ ≤ 2 := by
      calc (t1347WitnessB.scale 0 N (p : ℝ))⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) hscale.1
        _ = 2 := by norm_num
    have hinv0 : 0 ≤ (t1347WitnessB.scale 0 N (p : ℝ))⁻¹ := inv_nonneg.mpr hscalePos.le
    have hK0 := t1347WitnessK_nonneg
    have hC0 : 0 ≤ 54 * (1 + t1347WitnessK) * ((N : ℝ) + 1) := by positivity
    have hxi3nn : 0 ≤ Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 3 N p ω := by
      simpa [Step3.flowXiLK] using t1347WitnessX.xiLK_nonneg (E := 0) hscalePos.le
    let C : ℝ := 54 * (1 + t1347WitnessK) * ((N : ℝ) + 1)
    have h2C : Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 2 N p ω ≤ C := by
      simpa [C] using h2
    have h3C : Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 3 N p ω ≤ C := by
      simpa [C] using h3
    have hfirst :
        Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 2 N p ω *
          Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 3 N p ω ≤ C * C :=
      mul_le_mul h2C h3C hxi3nn (by simpa [C] using hC0)
    have hCC : 0 ≤ C * C := mul_nonneg hC0 hC0
    have hprod :
        Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 2 N p ω *
          Step3.flowXiLK t1347WitnessX 0 t1347WitnessS t1347WitnessT 3 N p ω *
            (t1347WitnessB.scale 0 N (p : ℝ))⁻¹ ≤
          5832 * (1 + t1347WitnessK) ^ 2 * ((N : ℝ) + 1) ^ 2 := by
      calc _ ≤ C * C * (t1347WitnessB.scale 0 N (p : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hfirst hinv0
        _ ≤ C * C * 2 := mul_le_mul_of_nonneg_left hinv hCC
        _ = 5832 * (1 + t1347WitnessK) ^ 2 * ((N : ℝ) + 1) ^ 2 := by
            dsimp [C]
            ring
    have hscaleEq : Step3.flowA t1347WitnessB 0 t1347WitnessS t1347WitnessT N p =
        t1347WitnessB.scale 0 N (p : ℝ) := rfl
    rw [hscaleEq]
    dsimp [t1347WitnessPhi]
    calc _ ≤ 5832 * (1 + t1347WitnessK) ^ 2 * ((N : ℝ) + 1) ^ 2 := hprod
      _ ≤ 10000 * (1 + t1347WitnessK) ^ 2 * ((N : ℝ) + 1) ^ 2 := by
        have hnonneg : 0 ≤ (1 + t1347WitnessK) ^ 2 * ((N : ℝ) + 1) ^ 2 := by positivity
        nlinarith
  · intro N p ω
    exact t1347Witness_Phi_nonneg N

private theorem t1347Witness_premises :
    Lemma514Premises t1347WitnessX 0 t1347WitnessS t1347WitnessT 3
      t1347WitnessLambda t1347WitnessPhi := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply t1347Witness_pointwise_stochDom
    · intro N p ω
      have h := t1347Witness_xiL_bound 8 (by omega) N p ω
      dsimp [t1347WitnessLambda]
      norm_num at h ⊢
      linarith
    · intro N p ω
      dsimp [t1347WitnessLambda]
      norm_num
  · intro m hm hm3
    apply t1347Witness_pointwise_stochDom
    · exact t1347Witness_Phi_dominates_xiLK m hm (Nat.le_of_lt hm3)
    · intro N p ω
      exact t1347Witness_Phi_nonneg N
  · intro m hm hm3
    have hmcases : m = 2 ∨ m = 3 := by omega
    rcases hmcases with h2 | h3
    · subst m
      simpa using t1347Witness_xiLK_product_dom
    · subst m
      simpa [mul_comm, mul_left_comm, mul_assoc] using t1347Witness_xiLK_product_dom
  · apply t1347Witness_pointwise_stochDom
    · intro N p ω
      have h := t1347Witness_xiL_bound 4 (by omega) N p ω
      have hY : 1 ≤ (1 + t1347WitnessK) * ((N : ℝ) + 1) := by
        have hn : 1 ≤ N + 1 := by omega
        have hN : 1 ≤ (N : ℝ) + 1 := by exact_mod_cast hn
        nlinarith [t1347WitnessK_nonneg]
      have hphi : 54 ≤ t1347WitnessPhi N := by
        dsimp [t1347WitnessPhi]
        nlinarith [hY, sq_nonneg ((1 + t1347WitnessK) * ((N : ℝ) + 1) - 1)]
      have h54 : 2 * (3 : ℝ) ^ (4 - 1) = 54 := by norm_num
      rw [h54] at h
      exact h.trans hphi
    · intro N p ω
      exact t1347Witness_Phi_nonneg N

private theorem t1347Witness_cond272 : Cond272 t1347WitnessB 0
    t1347WitnessS t1347WitnessT := by
  unfold Cond272
  filter_upwards [eventually_ge_atTop (3 * 2 ^ 31)] with N hN
  have hWnat : 2 ^ 31 ≤ t1347WitnessB.W N := by
    simp [t1347WitnessB, t1347WitnessD, Dims.example_W]
    omega
  have hW : (2 ^ 31 : ℝ) ≤ (t1347WitnessB.W N : ℝ) := by exact_mod_cast hWnat
  have hℓ : (1 : ℝ) ≤ ellHat 3 ((1 / 2 : ℝ) : ℂ) :=
      one_le_ellHat_of_nonneg (by norm_num : (1 : ℕ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hη : etaT 0 (1 / 2 : ℝ) = 1 / 2 := by
    rw [(t1347WitnessEta (1 / 2 : ℝ) (by norm_num) (by norm_num)).1]
    norm_num
  have hscale := t1347Witness_scale_eq N (1 / 2 : ℝ)
  have hA : (2 ^ 30 : ℝ) ≤ t1347WitnessB.scale 0 N (1 / 2) := by
    rw [hscale, hη]
    calc (2 ^ 30 : ℝ) = (2 ^ 31 : ℝ) * 1 * (1 / 2) := by norm_num
      _ ≤ (t1347WitnessB.W N : ℝ) * ellHat 3 ((1 / 2 : ℝ) : ℂ) * (1 / 2) := by gcongr
  have hInv := inv_anti₀ (by norm_num : (0 : ℝ) < 2 ^ 30) hA
  have hRhs : (2 ^ 30 : ℝ)⁻¹ = (1 / 2 : ℝ) ^ 30 := by norm_num
  have hbound : (t1347WitnessB.scale 0 N (t1347WitnessT N))⁻¹ ≤ (1 / 2 : ℝ) ^ 30 := by
    simpa [t1347WitnessT] using hInv.trans_eq hRhs
  calc (t1347WitnessB.scale 0 N (t1347WitnessT N))⁻¹ ≤ (1 / 2 : ℝ) ^ 30 := hbound
    _ = ((1 - t1347WitnessT N) / (1 - t1347WitnessS N)) ^ 30 := by
      norm_num [t1347WitnessT, t1347WitnessS]

private theorem t1347Witness_lkDecay :
    SumZeroDyn.LKDecay t1347WitnessX 0 t1347WitnessS t1347WitnessT := by
  intro m hm τ hτ D hD
  apply StochDom.of_eventually_empty
  intro τ' hτ'
  filter_upwards [eventually_le_rpow (2 : ℝ) hτ, eventually_ge_atTop 1] with N h2 hN
  ext ω
  simp only [badSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro p
  have hEll := (t1347Witness_window_bounds N p.1).2.2.1
  have hR : (2 : ℝ) ≤ ellHat 3 ((p.1 : ℝ) : ℂ) * (N : ℝ) ^ τ := by
    calc (2 : ℝ) = 1 * 2 := by ring
      _ ≤ ellHat 3 ((p.1 : ℝ) : ℂ) * (N : ℝ) ^ τ := by gcongr
  have hFar : SumZeroDyn.farInd (t1347WitnessB.L N)
      (t1347WitnessB.ell N (p.1 : ℝ) * (N : ℝ) ^ τ) p.2.2 = 0 := by
    change SumZeroDyn.farInd 3
      (ellHat 3 ((p.1 : ℝ) : ℂ) * (N : ℝ) ^ τ) p.2.2 = 0
    unfold SumZeroDyn.farInd
    split_ifs with h
    · obtain ⟨i, j, hij⟩ := h
      have hdist := zdist_le_half (p.2.2 i - p.2.2 j)
      change (zdist 3 (p.2.2 i - p.2.2 j) : ℝ) ≤ 3 / 2 at hdist
      have hcontra : (2 : ℝ) ≤ 3 / 2 := hR.trans (hij.trans hdist)
      norm_num at hcontra
    · rfl
  rw [hFar, mul_zero]
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ')
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-D))

theorem t1347_fixed_block_witness :
    (∀ N, 0 ≤ t1347WitnessS N) ∧
    (∀ N, t1347WitnessS N ≤ t1347WitnessT N) ∧
    (∀ N, t1347WitnessT N < 1) ∧
    (∀ N, t1347WitnessS N < t1347WitnessT N) ∧
    (∀ N, t1347WitnessV N ∈ Set.Icc (t1347WitnessS N) (t1347WitnessT N)) ∧
    Lemma514Premises t1347WitnessX 0 t1347WitnessS t1347WitnessT 3
      t1347WitnessLambda t1347WitnessPhi ∧
    SumZeroDyn.WardP t1347WitnessX 0 3 ∧
    Cond272 t1347WitnessB 0 t1347WitnessS t1347WitnessT ∧
    SumZeroDyn.LKDecay t1347WitnessX 0 t1347WitnessS t1347WitnessT ∧
    PHalf514 t1347WitnessX 0 t1347WitnessS t1347WitnessT 1 ∧
    (∃ i j : t1347WitnessD.Idx 1,
      0 < Sblk (t1347WitnessD.L 1) (t1347WitnessD.W 1) i j) := by
  letI : IsProbabilityMeasure t1347WitnessB.P := by
    rw [t1347WitnessB, band_P]
    infer_instance
  refine ⟨?_, ?_, ?_, ?_, ?_, t1347Witness_premises,
    SumZeroDyn.wardP_holds t1347WitnessX (by norm_num) 3,
    t1347Witness_cond272, t1347Witness_lkDecay, ?_, ?_⟩
  · intro N
    norm_num [t1347WitnessS]
  · intro N
    norm_num [t1347WitnessS, t1347WitnessT]
  · intro N
    norm_num [t1347WitnessT]
  · intro N
    norm_num [t1347WitnessS, t1347WitnessT]
  · intro N
    norm_num [t1347WitnessS, t1347WitnessT, t1347WitnessV]
  · exact pHalf514_of_gaussian_wardP_nonneg t1347WitnessD
      (by norm_num : |(0 : ℝ)| < 2)
      (by intro N; norm_num [t1347WitnessS])
      (by intro N; norm_num [t1347WitnessS, t1347WitnessT])
      (by intro N; norm_num [t1347WitnessT])
      t1347Witness_cond272 t1347Witness_lkDecay
  · let i : t1347WitnessD.Idx 1 :=
      (0, ⟨0, by have h := t1347WitnessD.W_pos 1; omega⟩)
    obtain ⟨j, hj⟩ := Dims.exists_Sblk_pos t1347WitnessD 1 i
    exact ⟨i, j, hj⟩

end Gauss

end RBM

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingHighQK0Repair
import RBM1D.Gauss.APrimeGeneralMovingLoopModulus
import RBM1D.Gauss.APrimeGeneralMovingGoodMesh
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1117: the selected high moment on the early good-event mesh

On the same Gaussian sample, the T475 general-moving half-Hölder modulus and
the target mesh control every active endpoint `2 ≤ k ≤ N^4` by a constant.
The globally Lipschitz cutoff transfers the initial T1097 moment to the
literal order-`q` widened-weight integral on the good event.
-/

namespace RBM.APrimeGeneralMovingHighQEarlyGood

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private noncomputable def cutProfile (x : ℝ) : ℝ := Cutoff.cutChi x * x

private theorem cutProfile_hasDerivAt (x : ℝ) :
    HasDerivAt cutProfile (Cutoff.cutChiD x * x + Cutoff.cutChi x) x := by
  change HasDerivAt (Cutoff.cutChi * id)
    (Cutoff.cutChiD x * x + Cutoff.cutChi x) x
  simpa only [id_eq, mul_one] using
    (Cutoff.hasDerivAt_cutChi x).mul (hasDerivAt_id x)

private theorem cutProfile_deriv_abs_le (x : ℝ) :
    |deriv cutProfile x| ≤ 19 / 4 := by
  have hderiv := (cutProfile_hasDerivAt x).deriv
  by_cases hx1 : x ≤ 1
  · rw [hderiv, Cutoff.cutChiD_eq_zero_left hx1, Cutoff.cutChi_eq_one hx1]
    norm_num
  · by_cases hx2 : 2 ≤ x
    · rw [hderiv, Cutoff.cutChiD_eq_zero_right hx2, Cutoff.cutChi_eq_zero hx2]
      norm_num
    · have hxlow : 1 ≤ x := le_of_not_ge hx1
      have hxhigh : x ≤ 2 := le_of_not_ge hx2
      have hxabs : |x| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
      have hD := Cutoff.abs_cutChiD_le x
      have hχ0 := Cutoff.cutChi_nonneg x
      have hχ1 := Cutoff.cutChi_le_one x
      rw [hderiv]
      calc
        |Cutoff.cutChiD x * x + Cutoff.cutChi x|
            ≤ |Cutoff.cutChiD x * x| + |Cutoff.cutChi x| := abs_add_le _ _
        _ ≤ (15 / 8) * 2 + 1 := by
          apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul hD hxabs (abs_nonneg x) (by positivity)
          · rw [abs_of_nonneg hχ0]
            exact hχ1
        _ = 19 / 4 := by norm_num

private theorem cutProfile_lipschitz (x y : ℝ) :
    |cutProfile x - cutProfile y| ≤ 19 / 4 * |x - y| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := cutProfile)
    (f' := fun z => Cutoff.cutChiD z * z + Cutoff.cutChi z)
    (C := 19 / 4)
    (fun z _ => (cutProfile_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => by
      rw [← (cutProfile_hasDerivAt z).deriv]
      simpa [Real.norm_eq_abs] using cutProfile_deriv_abs_le z)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

private theorem abs_cutTrunc_sub_le {θ x y : ℝ} (hθ : 0 < θ) :
    |cutTrunc θ x - cutTrunc θ y| ≤ 19 / 4 * |x - y| := by
  have hx : cutTrunc θ x = θ * cutProfile (x / θ) := by
    unfold MomentDuhamelCut.cutTrunc cutProfile
    field_simp
  have hy : cutTrunc θ y = θ * cutProfile (y / θ) := by
    unfold MomentDuhamelCut.cutTrunc cutProfile
    field_simp
  rw [hx, hy]
  have hdiff : θ * cutProfile (x / θ) - θ * cutProfile (y / θ) =
      θ * (cutProfile (x / θ) - cutProfile (y / θ)) := by ring
  rw [hdiff, abs_mul, abs_of_pos hθ]
  have hprof := cutProfile_lipschitz (x / θ) (y / θ)
  have hdiv : |x / θ - y / θ| = |x - y| / θ := by
    rw [show x / θ - y / θ = (x - y) / θ by ring, abs_div, abs_of_pos hθ]
  calc
    θ * |cutProfile (x / θ) - cutProfile (y / θ)|
        ≤ θ * (19 / 4 * |x / θ - y / θ|) :=
          mul_le_mul_of_nonneg_left hprof hθ.le
    _ = 19 / 4 * |x - y| := by rw [hdiv]; field_simp

private theorem pow_add_le_two_pow_mul_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) :
    (a + b) ^ n ≤ (2 : ℝ) ^ n * (a ^ n + b ^ n) := by
  have hab : a + b ≤ 2 * max a b := by
    have ha' := le_max_left a b
    have hb' := le_max_right a b
    linarith
  have hpow := pow_le_pow_left₀ (add_nonneg ha hb) hab n
  have hmax : (max a b) ^ n ≤ a ^ n + b ^ n := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      nlinarith [pow_nonneg ha n]
    · rw [max_eq_left h]
      nlinarith [pow_nonneg hb n]
  calc
    (a + b) ^ n ≤ (2 * max a b) ^ n := hpow
    _ = (2 : ℝ) ^ n * (max a b) ^ n := by rw [mul_pow]
    _ ≤ (2 : ℝ) ^ n * (a ^ n + b ^ n) :=
      mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)

private theorem endpoint_mesh_error_le_one {D : ℝ} {N k : ℕ}
    (hN : 1 ≤ N) (hk : k ≤ N ^ 4)
    (hmesh : 0 < APrimeGeneralMovingMesh.targetMesh D N)
    (hfine : (N : ℝ) ^ (2 * D + 7) *
      (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) ≤
        (N : ℝ) ^ (-2 : ℝ)) :
    (N : ℝ) ^ (2 * D + 7) *
      ((k : ℝ) / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hkcast : (k : ℝ) ≤ (N : ℝ) ^ 4 := by exact_mod_cast hk
  have hmesh0 : 0 ≤ APrimeGeneralMovingMesh.targetMesh D N := hmesh.le
  have hdiv : (k : ℝ) / APrimeGeneralMovingMesh.targetMesh D N ≤
      (N : ℝ) ^ 4 / APrimeGeneralMovingMesh.targetMesh D N :=
    div_le_div_of_nonneg_right hkcast hmesh0
  have hroot : ((k : ℝ) / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) ≤
      (N : ℝ) ^ 2 *
        (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow ((k : ℝ) / APrimeGeneralMovingMesh.targetMesh D N),
      ← Real.sqrt_eq_rpow
        (1 / APrimeGeneralMovingMesh.targetMesh D N)]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hsqrt := Real.sq_sqrt
      (show 0 ≤ 1 / APrimeGeneralMovingMesh.targetMesh D N by positivity)
    have hNpow : (N : ℝ) ^ 4 = ((N : ℝ) ^ 2) ^ 2 := by ring
    rw [mul_pow, hsqrt, ← hNpow]
    simpa [div_eq_mul_inv] using hdiv
  have hN2nonneg : 0 ≤ (N : ℝ) ^ 2 := by positivity
  have hcancel : (N : ℝ) ^ 2 * (N : ℝ) ^ (-2 : ℝ) = 1 := by
    calc
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-2 : ℝ) =
          (N : ℝ) ^ (2 + (-2 : ℝ)) := by
            rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hNpos]
            norm_num
      _ = 1 := by simp
  calc
    (N : ℝ) ^ (2 * D + 7) *
        ((k : ℝ) / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2)
      ≤ (N : ℝ) ^ (2 * D + 7) *
          ((N : ℝ) ^ 2 *
            (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ 2 *
          ((N : ℝ) ^ (2 * D + 7) *
            (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2)) := by ring
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hfine hN2nonneg
    _ = 1 := hcancel

-- The dependent good-event integral and the same-sample endpoint transfer
-- require more reduction steps than the project default heartbeat allowance.
set_option maxHeartbeats 1000000 in
-- The all-index dependent integral and its measurable weight require the higher heartbeat limit.
/-- The literal T999 selected-order expectation restricted to the norm-good
event, uniformly over active `2 ≤ k ≤ N^4`.  We select `q = p`; the only
stochastic input is T1097's initial law under `BoundsCore`. -/
theorem eventually_selected_high_early_good {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) (δ₀ : ℝ) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop,
          ∀ k : ℕ, 2 ≤ k → k ≤ N ^ 4 →
            k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
            ∫ ω in APrimeGeneralMovingGoodMesh.good N,
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh D)) 1
                (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω)
                s t (APrimeGeneralMovingMesh.targetMesh D) δ q N k ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (sample d) E D s N
                  (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^
                (2 * q) ∂B.P ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (sample d) E D s N u ω
  let r := APrimeWeight.canonicalR s t mesh
  let Good := APrimeGeneralMovingGoodMesh.good
  intro δ hδ hδ₀ p hp
  classical
  letI := B.isProbabilityMeasure
  obtain ⟨q, hq, C₀, hC₀, hbase⟩ :=
    APrimeGeneralMovingHighQK0Repair.eventually_selected_high_k0
      hE hD hs0 hst ht1 hc hreg hB δ₀ δ hδ hδ₀ p hp
  let θ : ℕ → ℝ := fun N => (N : ℝ) ^ (2 * δ)
  let n : ℕ := 2 * q
  let expon : ℝ := δ / 2 * (q : ℝ)
  let K : ℝ := (2 : ℝ) ^ n
  let err : ℝ := 19 / 4
  let errC : ℝ := err ^ n
  let C : ℝ := K * (C₀ + errC)
  have hC : 0 < C := by
    dsimp [C, K, errC, err]
    positivity
  have hmod := APrimeGeneralMovingLoopModulus.eventually_jSnorm_modulus
    (E := E) (D := D) (c := c) (s := s) (t := t)
    hE hD hs0 hst ht1 hc hreg
  have hfine := APrimeGeneralMovingMesh.eventually_target_mesh_fine (D := D)
  refine ⟨q, hq, C, hC, ?_⟩
  filter_upwards [hbase, hmod, hfine, eventually_ge_atTop 1]
    with N hbaseN hmodN hfineN hN
  intro k hklo hkhi hactive
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have hmesh : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos D N
  have hEndpoint : ∀ k, k ≤ cutNetTop s t mesh N →
      cutNetPt s mesh N k ∈ Set.Icc (s N) (t N) := by
    intro k hk
    exact netFinset_subset_Icc (hst N) hmesh _ (cutNetPt_mem_netFinset hk)
  have hsWindow : s N ∈ Set.Icc (s N) (t N) := ⟨le_rfl, hst N⟩
  have hmodAt : ∀ k, k ≤ N ^ 4 → k ≤ cutNetTop s t mesh N →
      ∀ ω ∈ Good N,
        |J N (cutNetPt s mesh N k) ω - J N (s N) ω| ≤ 1 := by
    intro k hkhi hkactive ω hω
    have h1 := hmodN ω
      (by simpa [Good, APrimeGeneralMovingGoodMesh.good] using hω)
      (cutNetPt s mesh N k) (hEndpoint k hkactive) (s N) hsWindow
    have hdist : |cutNetPt s mesh N k - s N| =
        (k : ℝ) / mesh N := by
      rw [CutHypTheta.cutNetPt]
      rw [show s N + (k : ℝ) / mesh N - s N = (k : ℝ) / mesh N by ring]
      exact abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hmesh.le)
    have hmeshError := endpoint_mesh_error_le_one hN hkhi hmesh hfineN.1
    rw [hdist] at h1
    exact h1.trans hmeshError
  have hθ : 0 < θ N := Real.rpow_pos_of_pos hNpos _
  have hJm : ∀ u, Measurable (J N u) := fun u =>
    APrimeSlotFields.measurable_jSnorm (sample d) E D s N u
  have hInitJ0 : ∀ ω, 0 ≤ J N (s N) ω := by
    intro ω
    exact Step2Moment.jSnorm_nonneg (sample d) hE
      ((hst N).trans_lt (ht1 N)) ((hst N).trans_lt (ht1 N)) ω
  have hW0 : ∀ ω, 0 ≤ APrimeWeight.widenedW r 1 J s t mesh δ q N k ω :=
    APrimeWeight.widenedW_nonneg r 1 J s t mesh δ q N k
  have hW1 : ∀ ω, APrimeWeight.widenedW r 1 J s t mesh δ q N k ω ≤ 1 :=
    APrimeWeight.widenedW_le_one r 1 J s t mesh δ q N k
  have hWm : AEStronglyMeasurable
      (APrimeWeight.widenedW r 1 J s t mesh δ q N k) B.P :=
    APrimeWeight.widenedW_meas r 1 J s t mesh
      (fun n u => APrimeSlotFields.measurable_jSnorm (sample d) E D s n u)
      q δ N k
  have hGoodMeas : MeasurableSet (Good N) := by
    simpa [Good] using APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hEndJ0 : ∀ ω, 0 ≤ J N (cutNetPt s mesh N k) ω := by
    intro ω
    exact Step2Moment.jSnorm_nonneg (sample d) hE
      ((hst N).trans_lt (ht1 N))
      ((hEndpoint k hactive).2.trans_lt (ht1 N)) ω
  have hEndInt : Integrable
      (fun ω => APrimeWeight.widenedW r 1 J s t mesh δ q N k ω *
        |cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω)| ^ n) B.P := by
    exact Step2Bootstrap.integrable_weight_mul hθ hW0 hW1 hWm
      hEndJ0 (hJm _).aestronglyMeasurable n
  let endIntegrand : Ω d → ℝ := fun ω =>
    APrimeWeight.widenedW r 1 J s t mesh δ q N k ω *
      |cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω)| ^ n
  let initPow : Ω d → ℝ := fun ω =>
    |cutTrunc (θ N) (J N (s N) ω)| ^ n
  have hInitInt : Integrable initPow B.P := by
    dsimp [initPow]
    exact integrable_cutTrunc_pow hθ hInitJ0
      (hJm (s N)).aestronglyMeasurable n
  have hRhsInt : Integrable
      (fun ω => K * (initPow ω + err ^ n)) B.P :=
    (hInitInt.add (integrable_const (err ^ n))).const_mul K
  have hIndicatorInt : Integrable ((Good N).indicator endIntegrand) B.P :=
    hEndInt.indicator hGoodMeas
  have hPoint : ∀ ω,
      (Good N).indicator endIntegrand ω ≤ K * (initPow ω + err ^ n) := by
    intro ω
    by_cases hω : ω ∈ Good N
    · change (if ω ∈ Good N then endIntegrand ω else 0) ≤ _
      rw [if_pos hω]
      have hJdiff := hmodAt k hkhi hactive ω hω
      have hcutdiff := abs_cutTrunc_sub_le (θ := θ N)
        (x := J N (cutNetPt s mesh N k) ω) (y := J N (s N) ω) hθ
      have hcut : cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω) ≤
          cutTrunc (θ N) (J N (s N) ω) + err := by
        have hle := (abs_le.mp hcutdiff).2
        have herr := mul_le_mul_of_nonneg_left hJdiff
          (by norm_num : (0 : ℝ) ≤ 19 / 4)
        dsimp [err]
        linarith
      have hcut0 : 0 ≤ cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω) :=
        cutTrunc_nonneg (hEndJ0 ω)
      have hinitCut0 : 0 ≤ cutTrunc (θ N) (J N (s N) ω) :=
        cutTrunc_nonneg (hInitJ0 ω)
      have herr0 : 0 ≤ err := by dsimp [err]; positivity
      have hpow := pow_add_le_two_pow_mul_sum hinitCut0 herr0 n
      have hpow' : |cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω)| ^ n ≤
          K * (initPow ω + err ^ n) := by
        have hInitPow : initPow ω =
            (cutTrunc (θ N) (J N (s N) ω)) ^ n := by
          dsimp [initPow]
          rw [abs_of_nonneg hinitCut0]
        rw [abs_of_nonneg hcut0]
        change cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω) ^ n ≤
          (2 : ℝ) ^ n * (initPow ω + err ^ n)
        calc
          cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω) ^ n
              ≤ (cutTrunc (θ N) (J N (s N) ω) + err) ^ n :=
                pow_le_pow_left₀ hcut0 hcut n
          _ ≤ (2 : ℝ) ^ n *
              (cutTrunc (θ N) (J N (s N) ω) ^ n + err ^ n) := hpow
          _ = (2 : ℝ) ^ n * (initPow ω + err ^ n) := by rw [← hInitPow]
      have hpow0 : 0 ≤ |cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω)| ^ n :=
        pow_nonneg (abs_nonneg _) n
      calc
        APrimeWeight.widenedW r 1 J s t mesh δ q N k ω *
            |cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω)| ^ n
            ≤ |cutTrunc (θ N) (J N (cutNetPt s mesh N k) ω)| ^ n :=
              mul_le_of_le_one_left hpow0 (hW1 ω)
        _ ≤ K * (initPow ω + err ^ n) := hpow'
    · change (if ω ∈ Good N then endIntegrand ω else 0) ≤ _
      rw [if_neg hω]
      have hinit0 : 0 ≤ initPow ω := by positivity
      positivity
  have hIntegral := integral_mono hIndicatorInt hRhsInt hPoint
  have hSetEq :
      ∫ ω in Good N, endIntegrand ω ∂B.P =
        ∫ ω, (Good N).indicator endIntegrand ω ∂B.P :=
    (integral_indicator hGoodMeas).symm
  have hInitBound :
      ∫ ω, initPow ω ∂B.P ≤ C₀ * (N : ℝ) ^ expon := by
    have hWzero : ∀ ω, APrimeWeight.widenedW r 1 J s t mesh δ q N 0 ω = 1 := by
      intro ω
      rw [APrimeWeight.widenedW]
      have hactive0 : 0 ≤ cutNetTop s t mesh N ∧ 1 ≤ N := ⟨Nat.zero_le _, hN⟩
      rw [if_pos hactive0]
      have hr : 0 < r N := by simp [r, APrimeWeight.canonicalR]
      have hz : softMax (r N) (Finset.range 0)
          (fun j => J N (cutNetPt s mesh N j) ω) = 0 := by
        simp only [softMax, Finset.range_zero, Finset.sum_empty]
        exact Real.zero_rpow (ne_of_gt (by positivity :
          (0 : ℝ) < 1 / (2 * (r N : ℝ))))
      unfold APrimeWeight.prefixSoftW softW
      rw [hz]
      simp [Cutoff.cutChi_eq_one]
    convert hbaseN using 1
    · apply integral_congr_ae
      filter_upwards [] with ω
      change initPow ω = APrimeWeight.widenedW r 1 J s t mesh δ q N 0 ω *
        |cutTrunc (θ N) (J N (cutNetPt s mesh N 0) ω)| ^ n
      rw [hWzero ω]
      simp [initPow, cutNetPt_zero]
  have hNexp : 1 ≤ (N : ℝ) ^ expon := by
    have hexpon : 0 < expon := by
      dsimp [expon]
      have hqpos : 0 < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans hp hq))
      positivity
    exact Real.one_le_rpow hNreal hexpon.le
  have hEval :
      ∫ ω, K * (initPow ω + err ^ n) ∂B.P =
        K * (∫ ω, initPow ω ∂B.P + err ^ n) := by
    rw [integral_const_mul, integral_add hInitInt (integrable_const (err ^ n)), integral_const]
    simp [B, Gauss.band]
  have hfinal :
      ∫ ω, K * (initPow ω + err ^ n) ∂B.P ≤ C * (N : ℝ) ^ expon := by
    rw [hEval]
    have herrC0 : 0 ≤ errC := by positivity
    have hsum :
        ∫ ω, initPow ω ∂B.P + err ^ n ≤ (C₀ + errC) * (N : ℝ) ^ expon := by
      calc
        ∫ ω, initPow ω ∂B.P + err ^ n ≤ C₀ * (N : ℝ) ^ expon + errC :=
          add_le_add hInitBound (by dsimp [errC]; exact le_rfl)
        _ ≤ C₀ * (N : ℝ) ^ expon + errC * (N : ℝ) ^ expon := by
          simpa only [mul_one] using add_le_add_right
            (mul_le_mul_of_nonneg_left hNexp herrC0)
            (C₀ * (N : ℝ) ^ expon)
        _ = (C₀ + errC) * (N : ℝ) ^ expon := by ring
    calc
      K * (∫ ω, initPow ω ∂B.P + err ^ n) ≤
          K * ((C₀ + errC) * (N : ℝ) ^ expon) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = C * (N : ℝ) ^ expon := by simp [C, K]; ring
  rw [hSetEq]
  exact hIntegral.trans hfinal

/-- The T995 Gaussian model has a resident in the same moving good event at an
active second target-mesh point.  The explicit first-cell window is eventually
`[0,1/2]`, so its `N^(4D+18)` mesh contains `k=2`; common-event residents lie
inside the spectral-norm good event. -/
theorem positive_length_k2_good_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (sample d) 0 s ∧
      (∀ᶠ N : ℕ in atTop,
        2 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N) ∧
      (∀ᶠ N : ℕ in atTop,
        ∃ ω ∈ APrimeGeneralMovingGoodMesh.good N,
          2 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N) := by
  obtain ⟨τ, hτ, c, hc, hsEq, hs0, hst, ht1, hreg, hB, _hpos, htHalf⟩ :=
    APrimeGeneralMovingInitialHinit.positive_length_hinit_witness'
  let s := firstCellS τ
  let t := firstCellT τ
  change (∀ N, s N = 0) at hsEq
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  change BoundsCore (sample d) 0 s at hB
  have hδ : 0 < min 1 (c / 100) / 2 := by positivity
  have hδsmall : min 1 (c / 100) / 2 ≤ min 1 (c / 100) := by linarith
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  rcases hroom with ⟨_hdw, _hxi, _hcap, htau, hsrc, hctr, _hbuffer,
      _hsrcTau, _htauCap, _hcapC, _hcapRoom, _, _⟩
  have hHP := APrimeGeneralMovingCommonSources.highProb_commonEvent
    (E := 0) (D := 60) (c := c) (by norm_num) (by norm_num)
    hs0 hst ht1 hc hreg hB
    (APrimeGeneralMovingSlotLossSchedule.zetaSrc (min 1 (c / 100) / 2))
    (APrimeGeneralMovingSlotLossSchedule.zetaCtr (min 1 (c / 100) / 2))
    (APrimeGeneralMovingSlotLossSchedule.tauG (min 1 (c / 100) / 2))
    (by simpa [APrimeGeneralMovingSlotLossSchedule.zetaSrc] using hsrc)
    (by simpa [APrimeGeneralMovingSlotLossSchedule.zetaCtr] using hctr)
    (by simpa [APrimeGeneralMovingSlotLossSchedule.tauG] using htau)
  have hcommon : ∀ᶠ N : ℕ in atTop,
      (APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc (min 1 (c / 100) / 2))
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr (min 1 (c / 100) / 2))
        (APrimeGeneralMovingSlotLossSchedule.tauG (min 1 (c / 100) / 2)) N).Nonempty :=
    hHP.nonempty (by simp)
  have htop : ∀ᶠ N : ℕ in atTop,
      2 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N := by
    filter_upwards [htHalf, APrimeGeneralMovingMesh.eventually_targetMesh_eq 60,
      eventually_ge_atTop 4] with N ht hmeshEq hN
    have hsN : s N = 0 := hsEq N
    have htN : t N = 1 / 2 := by simpa [t, firstCellT] using ht
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hNreal4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp : (1 : ℝ) ≤ 4 * (60 : ℝ) + 18 := by norm_num
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ (4 * (60 : ℝ) + 18) := by
      calc
        (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (4 * (60 : ℝ) + 18) :=
          Real.rpow_le_rpow_of_exponent_le hNreal hexp
    have hmeshLower : (4 : ℝ) ≤ APrimeGeneralMovingMesh.targetMesh 60 N := by
      rw [hmeshEq]
      exact hNreal4.trans hNle
    have hactive : 2 ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh 60) N := by
      change 2 ≤ ⌊(t N - s N) *
        APrimeGeneralMovingMesh.targetMesh 60 N⌋₊
      apply Nat.le_floor
      rw [htN, hsN]
      nlinarith [hmeshLower]
    exact hactive
  have hgoodWitness : ∀ᶠ N : ℕ in atTop,
      ∃ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        2 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N := by
    filter_upwards [hcommon, htop] with N hNcommon hNtop
    obtain ⟨ω, hω⟩ := hNcommon
    have hcarrier := APrimeGeneralMovingCommonSources.commonEvent_subset_rawCarrier
      0 60 s t
      (APrimeGeneralMovingSlotLossSchedule.zetaSrc (min 1 (c / 100) / 2))
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr (min 1 (c / 100) / 2))
      (APrimeGeneralMovingSlotLossSchedule.tauG (min 1 (c / 100) / 2)) N hω
    rcases hcarrier with ⟨⟨⟨hsource, _⟩, _⟩, _⟩
    have hgood := APrimeGeneralMovingRawSources.sourceGood_subset_good
      0 s t
      (APrimeGeneralMovingSlotLossSchedule.zetaSrc (min 1 (c / 100) / 2)) N hsource
    exact ⟨ω, hgood, hNtop⟩
  exact ⟨c, hc, s, t, hs0, hst, ht1, hreg, hB, htop, hgoodWitness⟩

#print axioms eventually_selected_high_early_good
#print axioms positive_length_k2_good_witness

end
end RBM.APrimeGeneralMovingHighQEarlyGood

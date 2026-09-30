/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.DBMInputNorm

/-!
# Step 1 of Theorem 2.6 for the band model, at unit density

`step1_band'`: for `τ_* ∈ (0,1)`, `t_* = M^{-1+τ_*}` (`M = L W`), bulk `|E₀| ≤ 2 - κ`, every `k`
and test function `O`, the correlation pairing of the fixed-time OU marginal `H_{t_*}` of (2.19)
at `E₀` is asymptotically the GUE pairing at energy `0` with the test function dilated by
`ρ_sc(0)/ρ_sc(E₀)` (`gue0Ref'`). Both sides are probability-marginal pairings (`corrPairing`),
with no extra `ρ^k` factor. The only external input is `LSY22'` (`h51`,
`docs/PAPER-VS-LEAN.md` §4).

## Route
1. Conditioning on the band matrix (`ouPairing_eq_integral`): the inner pairing is the DBM pairing
   `F_N(ω)` started at `v = e^{-t_*/2} λ(H(ω)) - E₀`, at energy `0`, time `ζ = 1 - e^{-t_*}`.
2. Along a sequence in the good event (`eventually_step1Good`), `h51` at `E = 0` with the test
   function `O(ρ_sc(E₀)⁻¹ ·)` gives `corrPairing(dbm, O((ρ_N/ρ₁)·)) - gue0Ref' → 0`. The dilation
   `r_N = ρ_N/ρ₁ → 1` (rate `M^{-3τ_*/8}`) is removed with `scaledPairing_lipschitz` via
   `scaledPairing = r^k · corrPairing(O(r·))` and `|r^k - 1| ≤ k 2^{k-1} |r - 1|`; the counts are
   bounded through `h51` (dominating test function) and `hG`.
3. Worst-sequence uniformity and the bad event.
-/

open MeasureTheory Filter Matrix Topology

namespace RBM.Gauss

/-! ### Size facts (copied from `Step1BandNorm.lean`) -/

private theorem Step1BandNorm.card_eq (d : Dims) (N : ℕ) :
    ((Fintype.card (d.Idx N) : ℕ) : ℝ) = msize d N := by
  unfold msize ouMatrixSize
  norm_cast
  simp [ZMod.card]

private theorem Step1BandNorm.msize_ge_three (d : Dims) (N : ℕ) : (3 : ℝ) ≤ msize d N := by
  have hL := d.three_le_L N
  have hW := d.W_pos N
  have h3 : (3 : ℕ) ≤ ouMatrixSize d N := by
    unfold ouMatrixSize
    calc (3 : ℕ) ≤ d.L N := hL
      _ ≤ d.L N * d.W N := Nat.le_mul_of_pos_right _ hW
  unfold msize
  exact_mod_cast h3

private theorem Step1BandNorm.msize_pos (d : Dims) (N : ℕ) : 0 < msize d N := by
  linarith [Step1BandNorm.msize_ge_three d N]

private theorem Step1BandNorm.msize_le_N (d : Dims) : ∀ᶠ N : ℕ in atTop, msize d N ≤ (N : ℝ) := by
  filter_upwards [d.dim] with N hdim
  have h1 : d.W N * d.L N ≤ N := hdim.1
  have hM : msize d N = ((d.W N * d.L N : ℕ) : ℝ) := by
    unfold msize ouMatrixSize; push_cast; ring
  rw [hM]; exact_mod_cast h1

private theorem Step1BandNorm.N_le_two_msize (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ 2 * msize d N := by
  filter_upwards [d.dim] with N hdim
  have h2 : N ≤ 2 * (d.W N * d.L N) := hdim.2
  have hM : msize d N = ((d.W N * d.L N : ℕ) : ℝ) := by
    unfold msize ouMatrixSize; push_cast; ring
  rw [hM]; exact_mod_cast h2

private theorem Step1BandNorm.msize_tendsto (d : Dims) :
    Tendsto (fun N : ℕ => msize d N) atTop atTop := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [Step1BandNorm.N_le_two_msize d] with N hN
  linarith

private theorem Step1BandNorm.rpow_tendsto_zero (d : Dims) {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => msize d N ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp (Step1BandNorm.msize_tendsto d)
  simpa [Function.comp_def] using h

private theorem Step1BandNorm.rhoSc_pos {E : ℝ} (hE : |E| < 2) : 0 < rhoSc E := by
  unfold rhoSc
  simp only [hE.le, ↓reduceIte]
  apply div_pos (Real.sqrt_pos.mpr ?_) (by positivity)
  have h1 : |E| ^ 2 < 2 ^ 2 := by
    have := abs_nonneg E
    nlinarith
  rw [sq_abs] at h1
  linarith

/-! ### `ouZeta` bounds -/

private theorem Step1BandNorm.ouZeta_le {t : ℝ} : ouZeta t ≤ t := by
  have h := Real.add_one_le_exp (-t)
  unfold ouZeta; linarith

private theorem Step1BandNorm.ouZeta_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ouZeta t := by
  unfold ouZeta
  have : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith

private theorem Step1BandNorm.ouZeta_ge_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ ouZeta t := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have htpos : (0 : ℝ) < 1 + t := by linarith
  have h2 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ htpos h1
  have h4 : (1 + t)⁻¹ ≤ 1 - t / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ htpos]
    nlinarith
  unfold ouZeta
  linarith

/-! ### Generic facts about `corrPairing` and `scaledPairing` -/

/-- A crude deterministic bound: `|corrPairing| ≤ M^{2k} sup|P|`. -/
private theorem Step1BandNorm.abs_corrPairing_le {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} {B : ℝ}
    (hB : ∀ x, |P x| ≤ B) (E : ℝ) :
    |RBM.corrPairing Pm Hm hH k P E| ≤ (Fintype.card n : ℝ) ^ (2 * k) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  unfold RBM.corrPairing
  set M : ℕ := Fintype.card n
  have hfac : ((M - k).factorial : ℝ) ≤ (M.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le M k)
  have hMf : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos M
  have hpref0 : 0 ≤ (M : ℝ) ^ k * (((M - k).factorial : ℝ) / (M.factorial : ℝ)) := by positivity
  have hpref : (M : ℝ) ^ k * (((M - k).factorial : ℝ) / (M.factorial : ℝ)) ≤ (M : ℝ) ^ k := by
    have : ((M - k).factorial : ℝ) / (M.factorial : ℝ) ≤ 1 := (div_le_one hMf).mpr hfac
    calc _ ≤ (M : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  have hemb : ((Fintype.card (Fin k ↪ n) : ℕ) : ℝ) ≤ (M : ℝ) ^ k := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    exact_mod_cast Nat.descFactorial_le_pow M k
  have hint : |∫ ω, ∑ f : Fin k ↪ n, P (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E)) ∂Pm|
      ≤ (M : ℝ) ^ k * B := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := (Fintype.card (Fin k ↪ n) : ℝ) * B)
      (Eventually.of_forall fun ω => ?_)).trans ?_
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => B)
        fun f _ => (Real.norm_eq_abs _).le.trans (hB _)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · rw [probReal_univ, mul_one]
      exact mul_le_mul_of_nonneg_right hemb hB0
  rw [abs_mul, abs_of_nonneg hpref0]
  calc _ ≤ (M : ℝ) ^ k * ((M : ℝ) ^ k * B) := mul_le_mul hpref hint (abs_nonneg _) (by positivity)
    _ = (M : ℝ) ^ (2 * k) * B := by rw [two_mul, pow_add]; ring

private theorem Step1BandNorm.corrPairing_nonneg {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} (hP : 0 ≤ P) (E : ℝ) :
    0 ≤ RBM.corrPairing Pm Hm hH k P E := by
  unfold RBM.corrPairing
  exact mul_nonneg (by positivity) (integral_nonneg fun ω => Finset.sum_nonneg fun f _ => hP _)

/-- Integrability of a correlation sum (bounded continuous test function). -/
private theorem Step1BandNorm.integrable_corrSum {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) {B : ℝ} (hB : ∀ x, ‖O x‖ ≤ B) (c E : ℝ) :
    Integrable (fun ω => ∑ f : Fin k ↪ n, O (fun j => c * ((hH ω).eigenvalues (f j) - E))) Pm := by
  refine Integrable.of_bound (measurable_corrSum hm hH k hO c E).aestronglyMeasurable
    ((Finset.univ : Finset (Fin k ↪ n)).card * B) (Eventually.of_forall fun ω => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun f _ => hB _).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- A dilate of a test function is a test function. -/
private theorem Step1BandNorm.isTestFun_dilate {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : RBM.IsTestFun O)
    {a : ℝ} (ha : a ≠ 0) : RBM.IsTestFun (fun β : Fin k → ℝ => O (fun j => a * β j)) := by
  have heq : (fun β : Fin k → ℝ => O (fun j => a * β j)) =
      O ∘ (Homeomorph.smulOfNeZero a ha : (Fin k → ℝ) ≃ₜ (Fin k → ℝ)) := by
    funext β; rfl
  refine ⟨?_, ?_⟩
  · have : ContDiff ℝ (⊤ : ℕ∞) (fun β : Fin k → ℝ => a • β) := contDiff_id.const_smul a
    exact hO.1.comp this
  · rw [heq]; exact hO.2.comp_homeomorph _

private theorem Step1BandNorm.scaledPairing_one {Ω' : Type*} [MeasurableSpace Ω']
    {n : Type*} [Fintype n] [DecidableEq n] (Pm : Measure Ω') (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    scaledPairing Pm Hm hH k O E 1 = RBM.corrPairing Pm Hm hH k O E := by
  unfold scaledPairing
  simp

/-- Measurability of `dbmMatrix` in the GUE sample. -/
private theorem Step1BandNorm.measurable_dbm (d : Dims) (N : ℕ) (v : d.Idx N → ℝ) (t : ℝ) :
    Measurable (dbmMatrix d N v t) := by
  have hcont : Continuous (fun Y : Matrix (d.Idx N) (d.Idx N) ℂ =>
      Matrix.diagonal (fun i => (v i : ℂ)) + (Real.sqrt t : ℂ) • Y) := by fun_prop
  exact hcont.measurable.comp (measurable_Xmat d N)

/-! ### Eigenvalues: measurability, Stieltjes transform, counting -/

/-- Measurability of a single eigenvalue along a measurable Hermitian matrix map (Weyl's bound
`eigenvalues₀_abs_sub_le`; the analogous helpers of `EigenMeasurable`/`Step1Rescale` are
private). -/
private theorem Step1BandNorm.measurable_eigenvalue {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*}
    [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (i : n) : Measurable (fun ω => (hH ω).eigenvalues i) := by
  have hcont : Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      x.2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)) := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ _)
      (𝓝 x) (𝓝 (x.2.eigenvalues₀ _))
    rw [tendsto_iff_dist_tendsto_zero]
    have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
    have hc : Continuous (fun A : Matrix n n ℂ =>
        Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
      Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
        continuous_finsetSum Finset.univ fun b _ =>
          (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
    have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
        (𝓝 x.1) (𝓝 0) := by
      have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
      have := hc.continuousAt (x := x.1)
      rwa [ContinuousAt, hval] at this
    have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
        Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
      h0.comp (continuous_subtype_val.continuousAt (x := x))
    refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
    rw [Real.dist_eq]
    exact eigenvalues₀_abs_sub_le y.2 x.2 _
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have := hcont.measurable.comp hφ
  simpa [Matrix.IsHermitian.eigenvalues, Function.comp_def] using this

/-- `stieltjes` is the finite sum over the eigenvalues. -/
private theorem Step1BandNorm.stieltjes_eq {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    RBM.stieltjes H z = stieltjesVec hH.eigenvalues z := by
  have hzne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := fun l h => by
    have h2 : (0 : ℝ) = z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  unfold RBM.stieltjes stieltjesVec
  congr 1
  rw [RBM.green_eq_spectral hH hzne]
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_comm (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) (star U),
    ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]

/-- **Counting by the Stieltjes transform**: `#{i : |λ_i| ≤ η} ≤ 2 n η Im m(iη)`. -/
private theorem Step1BandNorm.count_le_im {n : Type*} [Fintype n] (lam : n → ℝ) {η : ℝ}
    (hη : 0 < η) :
    (((Finset.univ : Finset n).filter (fun i => |lam i| ≤ η)).card : ℝ) ≤
      2 * (Fintype.card n : ℝ) * η * (stieltjesVec lam ⟨0, η⟩).im := by
  have hterm : ∀ i, (((lam i : ℂ) - ⟨0, η⟩)⁻¹).im = η / (lam i ^ 2 + η ^ 2) := by
    intro i
    rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.sub_re, Complex.ofReal_re]
    ring
  have him : (stieltjesVec lam ⟨0, η⟩).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ i, η / (lam i ^ 2 + η ^ 2) := by
    unfold stieltjesVec
    have hc : ((Fintype.card n : ℂ))⁻¹ = (((Fintype.card n : ℝ))⁻¹ : ℝ) := by simp
    rw [hc, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [hterm]
  set S := (Finset.univ : Finset n).filter (fun i => |lam i| ≤ η) with hS
  have hsum : (S.card : ℝ) / (2 * η) ≤ ∑ i, η / (lam i ^ 2 + η ^ 2) := by
    calc (S.card : ℝ) / (2 * η) = ∑ _i ∈ S, 1 / (2 * η) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ S, η / (lam i ^ 2 + η ^ 2) := Finset.sum_le_sum fun i hi => by
          have hi' : |lam i| ≤ η := (Finset.mem_filter.mp hi).2
          have h2 : lam i ^ 2 ≤ η ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi' 2
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ ∑ i, η / (lam i ^ 2 + η ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => by positivity)
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have hempty : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    have : S = ∅ := by
      rw [hS]; exact Finset.eq_empty_of_forall_notMem fun i => (hempty.false i).elim
    simp [this]
  · have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    rw [him]
    have e : 2 * (Fintype.card n : ℝ) * η * ((Fintype.card n : ℝ)⁻¹ *
        ∑ i, η / (lam i ^ 2 + η ^ 2)) = 2 * η * ∑ i, η / (lam i ^ 2 + η ^ 2) := by
      field_simp
    rw [e]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * η)).mp hsum
    linarith

/-! ### The GUE count at scale `M^{-1+step1CountEps}` -/

/-- **GUE count**: for a nonnegative test function `Q`, `M^{-3τ_*/8} · corrPairing_GUE(Q, 0) → 0`.
The pairing is bounded by `E[#{i : |λ_i| ≤ R/M}^k]`, and on the `hG` good event at
`z = i M^{-1+a}`, `a = step1CountEps τs k`, the count is `≤ 6 M^a`; the bad event costs
`M^k N^{-(k+1)} ≤ 1`.  Slack: `3τ_*/8 - k a > τ_*/4`. -/
private theorem Step1BandNorm.gue_count (d : Dims) (hG : GUELocalLaw d) {τs : ℝ} (h0 : 0 < τs)
    (h1 : τs < 1) (k : ℕ) {Q : (Fin k → ℝ) → ℝ} (hQ : RBM.IsTestFun Q) (hQ0 : 0 ≤ Q) :
    Tendsto (fun N => msize d N ^ (-step1Rate τs) *
      RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k Q 0) atTop (𝓝 0) := by
  obtain ⟨B, R, hB, hR, hQR⟩ := Step1Rescale.exists_le_indicator hQ
  set a : ℝ := step1CountEps τs k with ha_def
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have ha : 0 < a := by rw [ha_def]; unfold step1CountEps; positivity
  have ha1 : a ≤ 1 := by
    rw [ha_def]; unfold step1CountEps
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 8 * ((k : ℝ) + 1) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  have hka : a * k + -step1Rate τs < 0 := by
    rw [ha_def]; unfold step1CountEps step1Rate
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : τs / (8 * ((k : ℝ) + 1)) * k ≤ τs / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hr : -step1Rate τs < 0 := by unfold step1Rate; linarith
  let z : ℕ → ℂ := fun N => ⟨0, msize d N ^ (-1 + a)⟩
  have hz0 : ∀ N, 0 < (z N).im := fun N => Real.rpow_pos_of_pos (Step1BandNorm.msize_pos d N) _
  have hz1 : ∀ N, (z N).im ≤ 1 := fun N =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Step1BandNorm.msize_ge_three d N])
      (by linarith)
  have hzre : ∀ N, |(z N).re| ≤ 2 - 1 := fun N => by simp [z]
  have hzge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + a) ≤ (z N).im := by
    filter_upwards [Step1BandNorm.msize_le_N d] with N hN
    exact Real.rpow_le_rpow_of_nonpos (Step1BandNorm.msize_pos d N) hN (by linarith)
  have hGN := hG 1 one_pos a ha z hz0 hz1 hzre hzge a ha ((k + 1 : ℕ) : ℝ) (by positivity)
  -- eventually `R ≤ M^a` and `2k ≤ M`
  have hRM : ∀ᶠ N : ℕ in atTop, R ≤ msize d N ^ a :=
    ((tendsto_rpow_atTop ha).comp (Step1BandNorm.msize_tendsto d)).eventually_ge_atTop R
  have hkM : ∀ᶠ N : ℕ in atTop, 2 * (k : ℝ) + 1 ≤ msize d N :=
    (Step1BandNorm.msize_tendsto d).eventually_ge_atTop _
  have hbound : ∀ᶠ N : ℕ in atTop,
      RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k Q 0 ≤
        B * 2 ^ k * ((6 * msize d N ^ a) ^ k + 1) := by
    filter_upwards [hGN, Step1BandNorm.msize_le_N d, Step1BandNorm.N_le_two_msize d, hRM, hkM,
      eventually_ge_atTop 1] with N hGb hMN hNM hRMN hkMN hN1
    have hMpos := Step1BandNorm.msize_pos d N
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hcard := Step1BandNorm.card_eq d N
    have hk : k < Fintype.card (d.Idx N) := by
      have : (k : ℝ) < (Fintype.card (d.Idx N) : ℝ) := by rw [hcard]; linarith
      exact_mod_cast this
    have h1 := Step1Rescale.corrPairing_le_count_smul (gueMeasure d N) (Xmat d N)
      (measurable_Xmat d N) (Xmat_isHermitian d N) k hk hQ0 hB hQR 0
    rw [hcard] at h1
    refine h1.trans ?_
    -- the prefactor
    have hMk : (0 : ℝ) < msize d N - k := by linarith
    have hX : (msize d N / (msize d N - k)) ^ k ≤ 2 ^ k := by
      refine pow_le_pow_left₀ (div_nonneg hMpos.le hMk.le) ?_ k
      rw [div_le_iff₀ hMk]; linarith
    -- the count moment
    set η : ℝ := msize d N ^ (-1 + a) with hη_def
    have hηpos : 0 < η := Real.rpow_pos_of_pos hMpos _
    have hMη : msize d N * η = msize d N ^ a := by
      rw [hη_def]
      calc msize d N * msize d N ^ (-1 + a) = msize d N ^ (1 : ℝ) * msize d N ^ (-1 + a) := by
            rw [Real.rpow_one]
        _ = msize d N ^ ((1 : ℝ) + (-1 + a)) := (Real.rpow_add hMpos _ _).symm
        _ = msize d N ^ a := by congr 1; ring
    have hRη : R / msize d N ≤ η := by
      rw [div_le_iff₀ hMpos, mul_comm, hMη]; exact hRMN
    have hNa : (N : ℝ) ^ a ≤ 2 * msize d N ^ a := by
      calc (N : ℝ) ^ a ≤ (2 * msize d N) ^ a :=
            Real.rpow_le_rpow (Nat.cast_nonneg N) hNM ha.le
        _ = 2 ^ a * msize d N ^ a := Real.mul_rpow (by norm_num) hMpos.le
        _ ≤ 2 * msize d N ^ a := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hMpos.le _)
            calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
              _ = 2 := Real.rpow_one 2
    set bad : Set (Ω d) := {ω | (N : ℝ) ^ a * (msize d N * (z N).im)⁻¹ <
      ‖RBM.stieltjes (Xmat d N ω) (z N) - msc (z N)‖} with hbad
    set T := toMeasurable (gueMeasure d N) bad with hT_def
    have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
    have hsubT : bad ⊆ T := subset_toMeasurable _ _
    have hμT : gueMeasure d N T = gueMeasure d N bad := measure_toMeasurable _
    set cnt : Ω d → ℝ := fun ω => (((Finset.univ : Finset (d.Idx N)).filter
      (fun i => |(Xmat_isHermitian d N ω).eigenvalues i - 0| ≤ R / msize d N)).card : ℝ)
      with hcnt
    have hcnt0 : ∀ ω, 0 ≤ cnt ω := fun ω => Nat.cast_nonneg _
    have hcntM : ∀ ω, cnt ω ≤ msize d N := fun ω => by
      rw [← hcard]
      have := Finset.card_filter_le (Finset.univ : Finset (d.Idx N))
        (fun i => |(Xmat_isHermitian d N ω).eigenvalues i - 0| ≤ R / msize d N)
      rw [Finset.card_univ] at this
      simp only [hcnt]
      exact_mod_cast this
    have hcntgood : ∀ ω, ω ∉ bad → cnt ω ≤ 6 * msize d N ^ a := by
      intro ω hω
      have hle : ‖RBM.stieltjes (Xmat d N ω) (z N) - msc (z N)‖ ≤
          (N : ℝ) ^ a * (msize d N * (z N).im)⁻¹ := not_lt.mp hω
      have him : (z N).im = η := rfl
      rw [him, hMη] at hle
      set lam := (Xmat_isHermitian d N ω).eigenvalues
      have hsubset : (Finset.univ : Finset (d.Idx N)).filter
          (fun i => |lam i - 0| ≤ R / msize d N) ⊆
          (Finset.univ : Finset (d.Idx N)).filter (fun i => |lam i| ≤ η) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_zero] at hi ⊢
        exact hi.trans hRη
      have hc1 : cnt ω ≤ (((Finset.univ : Finset (d.Idx N)).filter
          (fun i => |lam i| ≤ η)).card : ℝ) := by
        simp only [hcnt]
        exact_mod_cast Finset.card_le_card hsubset
      have hc2 := Step1BandNorm.count_le_im lam hηpos
      rw [hcard] at hc2
      have hst : stieltjesVec lam ⟨0, η⟩ = RBM.stieltjes (Xmat d N ω) (z N) :=
        (Step1BandNorm.stieltjes_eq (Xmat_isHermitian d N ω) (hz0 N)).symm
      rw [hst] at hc2
      have hIm : (RBM.stieltjes (Xmat d N ω) (z N)).im ≤
          1 + (N : ℝ) ^ a * (msize d N ^ a)⁻¹ := by
        have h1 := Complex.im_le_norm (RBM.stieltjes (Xmat d N ω) (z N))
        have h2 := norm_msc_lt_one (hz0 N)
        have h3 := norm_le_insert' (RBM.stieltjes (Xmat d N ω) (z N)) (msc (z N))
        linarith
      have hMa : 0 < msize d N ^ a := Real.rpow_pos_of_pos hMpos _
      calc cnt ω ≤ 2 * msize d N * η * (RBM.stieltjes (Xmat d N ω) (z N)).im := hc1.trans hc2
        _ ≤ 2 * msize d N * η * (1 + (N : ℝ) ^ a * (msize d N ^ a)⁻¹) :=
            mul_le_mul_of_nonneg_left hIm (by positivity)
        _ = 2 * msize d N ^ a + 2 * (N : ℝ) ^ a := by
            rw [mul_assoc 2, hMη]; field_simp
        _ ≤ 6 * msize d N ^ a := by linarith
    have hg : Integrable (fun ω => (6 * msize d N ^ a) ^ k +
        T.indicator (fun _ => msize d N ^ k) ω) (gueMeasure d N) :=
      (integrable_const _).add ((integrable_const _).indicator hTm)
    have hpt : ∀ ω, cnt ω ^ k ≤
        (6 * msize d N ^ a) ^ k + T.indicator (fun _ => msize d N ^ k) ω := by
      intro ω
      by_cases hω : ω ∈ bad
      · rw [Set.indicator_of_mem (hsubT hω)]
        have : cnt ω ^ k ≤ msize d N ^ k := pow_le_pow_left₀ (hcnt0 ω) (hcntM ω) k
        have : 0 ≤ (6 * msize d N ^ a) ^ k := by positivity
        linarith
      · have h1 : cnt ω ^ k ≤ (6 * msize d N ^ a) ^ k :=
          pow_le_pow_left₀ (hcnt0 ω) (hcntgood ω hω) k
        have h2 : 0 ≤ T.indicator (fun _ => msize d N ^ k) ω :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        linarith
    have hint : ∫ ω, cnt ω ^ k ∂(gueMeasure d N) ≤ (6 * msize d N ^ a) ^ k + 1 := by
      refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (hcnt0 ω) k) hg
        (Eventually.of_forall hpt)).trans ?_
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm),
        integral_const, integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
      have hTreal : (gueMeasure d N).real T ≤ (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ)) := by
        rw [measureReal_def, hμT]
        exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg N) _) hGb
      have hNpow : (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ)) * msize d N ^ k ≤ 1 := by
        rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast,
          inv_mul_le_iff₀ (by positivity), mul_one]
        calc msize d N ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ hMpos.le hMN k
          _ ≤ (N : ℝ) ^ (k + 1) := pow_le_pow_right₀ hN1' (Nat.le_succ k)
      have := mul_le_mul_of_nonneg_right hTreal (pow_nonneg hMpos.le k)
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hX hB.le) hint
      (integral_nonneg fun ω => pow_nonneg (hcnt0 ω) k) (by positivity)
  -- conclude
  have hlim : Tendsto (fun N => msize d N ^ (-step1Rate τs) *
      (B * 2 ^ k * ((6 * msize d N ^ a) ^ k + 1))) atTop (𝓝 0) := by
    have e : ∀ N, msize d N ^ (-step1Rate τs) * (B * 2 ^ k * ((6 * msize d N ^ a) ^ k + 1)) =
        B * 2 ^ k * 6 ^ k * msize d N ^ (a * k + -step1Rate τs) +
          B * 2 ^ k * msize d N ^ (-step1Rate τs) := by
      intro N
      rw [Real.rpow_add (Step1BandNorm.msize_pos d N),
        Real.rpow_mul_natCast (Step1BandNorm.msize_pos d N).le, mul_pow]
      ring
    simp_rw [e]
    have hsum := ((Step1BandNorm.rpow_tendsto_zero d hka).const_mul (B * 2 ^ k * 6 ^ k)).add
      ((Step1BandNorm.rpow_tendsto_zero d hr).const_mul (B * 2 ^ k))
    simpa using hsum
  have hnn : ∀ N, 0 ≤ msize d N ^ (-step1Rate τs) *
      RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k Q 0 := fun N =>
    mul_nonneg (Real.rpow_nonneg (Step1BandNorm.msize_pos d N).le _)
      (Step1BandNorm.corrPairing_nonneg _ _ _ k hQ0 0)
  have hle : ∀ᶠ N in atTop, msize d N ^ (-step1Rate τs) *
      RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k Q 0 ≤
        msize d N ^ (-step1Rate τs) * (B * 2 ^ k * ((6 * msize d N ^ a) ^ k + 1)) := by
    filter_upwards [hbound] with N hN
    exact mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg (Step1BandNorm.msize_pos d N).le _)
  exact squeeze_zero' (Eventually.of_forall hnn) hle hlim


/-! ### The good event and the conditional pairing -/

/-- The good event of `eventually_step1Good`. -/
private def Step1BandNorm.good (d : Dims) (κ τs E₀ : ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | IsRegular51 (vOU d N τs E₀ ω) (msize d N ^ (-1 + step1Eps τs))
        (msize d N ^ (-step1Sig τs)) (cBulk κ) 2 1 ∧
      ∃ ρ, Tendsto (fun η : ℝ => (freeConvST (vOU d N τs E₀ ω)
          (ouZeta ((Gauss.band d).tPow τs N)) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        |ρ - rhoSc E₀| ≤ msize d N ^ (-step1Rate τs)}

/-- The conditional (DBM) pairing given the band matrix. -/
private noncomputable def Step1BandNorm.F (d : Dims) (τs E₀ : ℝ) (N k : ℕ) (O : (Fin k → ℝ) → ℝ)
    (ω : Ω d) : ℝ :=
  RBM.corrPairing (gueMeasure d N)
    (dbmMatrix d N (vOU d N τs E₀ ω) (ouZeta ((Gauss.band d).tPow τs N)))
    (dbmMatrix_isHermitian _ _ _ _) k O 0

private theorem Step1BandNorm.tPow_eq (d : Dims) (τs : ℝ) (N : ℕ) :
    (Gauss.band d).tPow τs N = msize d N ^ (-1 + τs) := rfl

/-! ### Absolute-value domination of a pairing -/

private theorem Step1BandNorm.corrPairing_neg {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) (P : (Fin k → ℝ) → ℝ) (E : ℝ) :
    RBM.corrPairing Pm Hm hH k (fun β => -P β) E = -RBM.corrPairing Pm Hm hH k P E := by
  unfold RBM.corrPairing
  simp only [Finset.sum_neg_distrib, integral_neg, mul_neg]

/-- `|corrPairing P| ≤ corrPairing Q` when `|P| ≤ Q` pointwise (bounded continuous `P`, `Q`). -/
private theorem Step1BandNorm.abs_corrPairing_le_of_abs_le {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {P Q : (Fin k → ℝ) → ℝ} (hP : RBM.IsTestFun P) (hQ : RBM.IsTestFun Q)
    (hPQ : ∀ β, |P β| ≤ Q β) (E : ℝ) :
    |RBM.corrPairing Pm Hm hH k P E| ≤ RBM.corrPairing Pm Hm hH k Q E := by
  obtain ⟨BP, hBP⟩ := hP.1.continuous.bounded_above_of_compact_support hP.2
  obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hIP := Step1BandNorm.integrable_corrSum Pm hm hH k hP.1.continuous hBP
    (Fintype.card n : ℝ) E
  have hIQ := Step1BandNorm.integrable_corrSum Pm hm hH k hQ.1.continuous hBQ
    (Fintype.card n : ℝ) E
  have hIP' : Integrable (fun ω => ∑ f : Fin k ↪ n,
      (fun β => -P β) (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E))) Pm := by
    refine hIP.neg.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
  have h1 := corrPairing_mono Pm hH k (fun β => (le_abs_self (P β)).trans (hPQ β)) E hIP hIQ
  have h2 := corrPairing_mono Pm hH k (O := fun β => -P β)
    (fun β => (neg_le_abs (P β)).trans (hPQ β)) E hIP' hIQ
  rw [Step1BandNorm.corrPairing_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- A nonnegative test function dominating `|O|`. -/
private theorem Step1BandNorm.exists_abs_dominating {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : RBM.IsTestFun O) :
    ∃ Qa : (Fin k → ℝ) → ℝ, RBM.IsTestFun Qa ∧ 0 ≤ Qa ∧ ∀ β, |O β| ≤ Qa β := by
  have hO' : RBM.IsTestFun (fun β => -O β) := ⟨hO.1.neg, hO.2.neg⟩
  obtain ⟨Q1, hQ1, hQ10, h1⟩ := exists_dominating_testFun hO 1 1
  obtain ⟨Q2, hQ2, hQ20, h2⟩ := exists_dominating_testFun hO' 1 1
  refine ⟨fun β => Q1 β + Q2 β, ⟨hQ1.1.add hQ2.1, hQ1.2.add hQ2.2⟩,
    fun β => add_nonneg (hQ10 β) (hQ20 β), fun β => ?_⟩
  have e : (fun j => (1 : ℝ) * β j) = β := by funext j; simp
  have a1 := h1 1 ⟨le_rfl, le_rfl⟩ β
  have a2 := h2 1 ⟨le_rfl, le_rfl⟩ β
  rw [e] at a1 a2
  have b1 : 0 ≤ Q1 β := hQ10 β
  have b2 : 0 ≤ Q2 β := hQ20 β
  change |O β| ≤ Q1 β + Q2 β
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### The worst-sequence core: `LSY22'` along one sequence in the good event -/

/-- **Worst-sequence core**: along any sequence `ω_N` eventually in the good event, `h51`
(`LSY22'`) applies to `v_N = e^{-t_*/2} λ(H(ω_N)) - E₀` at energy `0`, and the conditional
pairing is close to `gue0Ref'`. -/
private theorem Step1BandNorm.core (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ)
    (hG : GUELocalLaw d) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ)
    (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : RBM.IsTestFun O) (ω : ℕ → Ω d)
    (hω : ∀ᶠ N in atTop, ω N ∈ Step1BandNorm.good d κ τs E₀ N) :
    Tendsto (fun N => Step1BandNorm.F d τs E₀ N k O (ω N) - gue0Ref' d N k O E₀) atTop
      (𝓝 0) := by
  classical
  set ρ₁ := rhoSc E₀ with hρ₁
  set ρ₀ := rhoSc 0 with hρ₀
  have hρ₁pos : 0 < ρ₁ := Step1BandNorm.rhoSc_pos (by linarith)
  have hρ₀pos : 0 < ρ₀ := Step1BandNorm.rhoSc_pos (by norm_num)
  set σ := step1Sig τs with hσ
  have hσpos : 0 < σ := lt_min (by positivity) (by linarith)
  have hσ1 : σ ≤ τs / 4 := min_le_left _ _
  have hσ2 : σ ≤ (1 - τs) / 3 := min_le_right _ _
  have hrate : 0 < step1Rate τs := by unfold step1Rate; positivity
  -- the data fed to `[51]`
  let v : ∀ N, d.Idx N → ℝ := fun N => vOU d N τs E₀ (ω N)
  let tt : ℕ → ℝ := fun N => ouZeta ((Gauss.band d).tPow τs N)
  let g : ℕ → ℝ := fun N => msize d N ^ (-1 + step1Eps τs)
  let G : ℕ → ℝ := fun N => msize d N ^ (-σ)
  let m : ℕ → ℂ → ℂ := fun N => freeConvST (v N) (tt N)
  let PP : ℕ → Prop := fun N => ∃ ρ, Tendsto (fun η : ℝ => (m N ⟨0, η⟩).im / Real.pi)
    (𝓝[>] 0) (𝓝 ρ) ∧ |ρ - ρ₁| ≤ msize d N ^ (-step1Rate τs)
  let ρs : ℕ → ℝ := fun N => if h : PP N then Classical.choose h else ρ₁
  have hgood : ∀ᶠ N in atTop, IsRegular51 (v N) (g N) (G N) (cBulk κ) 2 1 ∧
      Tendsto (fun η : ℝ => (m N ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρs N)) ∧
      |ρs N - ρ₁| ≤ msize d N ^ (-step1Rate τs) := by
    filter_upwards [hω] with N hN
    obtain ⟨hreg, hex⟩ := hN
    have hP : PP N := hex
    have hspec := Classical.choose_spec hP
    have hρsN : ρs N = Classical.choose hP := by simp only [ρs, hP, ↓reduceDIte]
    rw [hρsN]
    exact ⟨hreg, hspec⟩
  -- eventual size facts
  have hM2 : ∀ᶠ N : ℕ in atTop, 2 ≤ msize d N ^ (τs / 2) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τs / 2)).comp
      (Step1BandNorm.msize_tendsto d)).eventually_ge_atTop 2
  -- the premises of `[51]`
  have hprem : ∀ᶠ N in atTop,
      msize d N ^ σ / msize d N ≤ g N ∧ g N ≤ msize d N ^ (-σ) ∧ G N ≤ msize d N ^ (-σ) ∧
      g N * msize d N ^ σ ≤ tt N ∧ tt N ≤ msize d N ^ (-σ) * G N ^ 2 ∧
      |(fun _ : ℕ => (0 : ℝ)) N| ≤ 1 / 2 * G N ∧
      IsRegular51 (v N) (g N) (G N) (cBulk κ) 2 1 ∧ IsFreeConv51 (v N) (tt N) (m N) ∧
      Tendsto (fun η : ℝ => (m N ⟨(fun _ : ℕ => (0 : ℝ)) N, η⟩).im / Real.pi) (𝓝[>] 0)
        (𝓝 (ρs N)) := by
    filter_upwards [hgood, hM2] with N hN hM2N
    have hM := Step1BandNorm.msize_pos d N
    have hM1 : 1 ≤ msize d N := by linarith [Step1BandNorm.msize_ge_three d N]
    have hε : step1Eps τs = τs / 4 := rfl
    have ht : (Gauss.band d).tPow τs N = msize d N ^ (-1 + τs) := Step1BandNorm.tPow_eq d τs N
    have ht0 : 0 ≤ msize d N ^ (-1 + τs) := Real.rpow_nonneg hM.le _
    have ht1 : msize d N ^ (-1 + τs) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
    refine ⟨?_, ?_, le_rfl, ?_, ?_, ?_, hN.1, ?_, hN.2.1⟩
    · change msize d N ^ σ / msize d N ≤ msize d N ^ (-1 + step1Eps τs)
      rw [← Real.rpow_sub_one hM.ne', hε]
      exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    · change msize d N ^ (-1 + step1Eps τs) ≤ msize d N ^ (-σ)
      rw [hε]
      exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    · change msize d N ^ (-1 + step1Eps τs) * msize d N ^ σ ≤ ouZeta ((Gauss.band d).tPow τs N)
      rw [hε, ← Real.rpow_add hM, ht]
      refine le_trans ?_ (Step1BandNorm.ouZeta_ge_half ht0 ht1)
      have hsplit : msize d N ^ (-1 + τs) = msize d N ^ (-1 + τs / 2) * msize d N ^ (τs / 2) := by
        rw [← Real.rpow_add hM]; congr 1; ring
      have hle : msize d N ^ (-1 + τs / 4 + σ) ≤ msize d N ^ (-1 + τs / 2) :=
        Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      have hpos : 0 ≤ msize d N ^ (-1 + τs / 2) := Real.rpow_nonneg hM.le _
      rw [hsplit]
      nlinarith
    · change ouZeta ((Gauss.band d).tPow τs N) ≤ msize d N ^ (-σ) * (msize d N ^ (-σ)) ^ 2
      rw [← Real.rpow_mul_natCast hM.le, ← Real.rpow_add hM, ht]
      refine Step1BandNorm.ouZeta_le.trans ?_
      exact Real.rpow_le_rpow_of_exponent_le hM1 (by push_cast; linarith)
    · change |(0 : ℝ)| ≤ 1 / 2 * msize d N ^ (-σ)
      rw [abs_zero]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hM.le _)
    · exact isFreeConv51_freeConvST (v N)
        (Step1BandNorm.ouZeta_nonneg (by rw [ht]; exact ht0))
  have hL : ∀ P : (Fin k → ℝ) → ℝ, RBM.IsTestFun P →
      Tendsto (fun N => RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N))
          (dbmMatrix_isHermitian d N (v N) (tt N)) k (fun β => P (fun j => ρs N * β j)) 0 -
        RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
          (fun β => P (fun j => ρ₀ * β j)) 0) atTop (𝓝 0) := fun P hP =>
    h51 σ σ (1 / 2) (cBulk κ) 2 1 hσpos hσpos (by norm_num) (by norm_num)
      (Step1Regularity.cBulk_pos hκ) g G tt (fun _ => 0) v m ρs hprem k P hP
  -- `ρs → ρ₁` at rate `M^{-3τ_*/8}`
  have hclose : ∀ᶠ N : ℕ in atTop, msize d N ^ (-step1Rate τs) < ρ₁ / 2 :=
    (Step1BandNorm.rpow_tendsto_zero d (by linarith)).eventually (gt_mem_nhds (by positivity))
  -- step (i): `h51` with `Õ = O(ρ₁⁻¹ ·)`
  have hOt : RBM.IsTestFun (fun β : Fin k → ℝ => O (fun j => ρ₁⁻¹ * β j)) :=
    Step1BandNorm.isTestFun_dilate hO (inv_ne_zero hρ₁pos.ne')
  let A : ℕ → ℝ := fun N => RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N))
    (dbmMatrix_isHermitian d N (v N) (tt N)) k (fun β => O (fun j => ρs N / ρ₁ * β j)) 0
  have hA : Tendsto (fun N => A N - gue0Ref' d N k O E₀) atTop (𝓝 0) := by
    refine (hL _ hOt).congr fun N => ?_
    have e1 : (fun β : Fin k → ℝ => O (fun j => ρ₁⁻¹ * (ρs N * β j))) =
        (fun β : Fin k → ℝ => O (fun j => ρs N / ρ₁ * β j)) := by
      funext β; congr 1; funext j; field_simp
    have e2 : (fun β : Fin k → ℝ => O (fun j => ρ₁⁻¹ * (ρ₀ * β j))) =
        (fun β : Fin k → ℝ => O (fun j => ρ₀ / ρ₁ * β j)) := by
      funext β; congr 1; funext j; field_simp
    simp only [A, gue0Ref', e1, e2]
    rfl
  -- step (ii): Lipschitz in the scale
  obtain ⟨Q, hQ, hQ0, C, hC⟩ := scaledPairing_lipschitz hO (ρmin := 1 / 2) (ρmax := 2)
    (by norm_num) (by norm_num)
  -- step (iii): domination and the counts
  obtain ⟨Q', hQ', hQ'0, hdom⟩ := exists_dominating_testFun hQ (ρ₁ / 2) (2 * ρ₁)
  have hQ'1 : ∀ᶠ N in atTop,
      RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N))
          (dbmMatrix_isHermitian d N (v N) (tt N)) k (fun β => Q' (fun j => ρs N * β j)) 0 -
        RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
          (fun β => Q' (fun j => ρ₀ * β j)) 0 < 1 :=
    (hL Q' hQ').eventually (gt_mem_nhds one_pos)
  obtain ⟨Qa, hQa, hQa0, hQaO⟩ := Step1BandNorm.exists_abs_dominating hO
  have hc0 : ρ₀ / ρ₁ ≠ 0 := (div_pos hρ₀pos hρ₁pos).ne'
  have hGc := Step1BandNorm.gue_count d hG h0 h1 k
    (Q := fun β => Q' (fun j => ρ₀ * β j)) (Step1BandNorm.isTestFun_dilate hQ' hρ₀pos.ne')
    (fun β => hQ'0 (fun j => ρ₀ * β j))
  have hGa := Step1BandNorm.gue_count d hG h0 h1 k
    (Q := fun β => Qa (fun j => ρ₀ / ρ₁ * β j)) (Step1BandNorm.isTestFun_dilate hQa hc0)
    (fun β => hQa0 (fun j => ρ₀ / ρ₁ * β j))
  set L : ℝ := k * 2 ^ (k - 1) / ρ₁ with hL_def
  have hL0 : 0 ≤ L := by positivity
  set GQ : ℕ → ℝ := fun N => RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
    (fun β => Q' (fun j => ρ₀ * β j)) 0 with hGQ
  set Ga : ℕ → ℝ := fun N => RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
    (fun β => Qa (fun j => ρ₀ / ρ₁ * β j)) 0 with hGa_def
  set mr : ℕ → ℝ := fun N => msize d N ^ (-step1Rate τs) with hmr
  have hbound : ∀ᶠ N in atTop,
      ‖Step1BandNorm.F d τs E₀ N k O (ω N) - gue0Ref' d N k O E₀‖ ≤
        |A N - gue0Ref' d N k O E₀| * (1 + L * mr N) + |C| / ρ₁ * (mr N * GQ N + mr N) +
          L * (mr N * Ga N) := by
    filter_upwards [hgood, hclose, hQ'1] with N hN hcl hQ'N
    have hMr : 0 ≤ mr N := Real.rpow_nonneg (Step1BandNorm.msize_pos d N).le _
    have hdist : |ρs N - ρ₁| < ρ₁ / 2 := lt_of_le_of_lt hN.2.2 hcl
    have hρsI : ρs N ∈ Set.Icc (ρ₁ / 2) (2 * ρ₁) := by
      rw [abs_lt] at hdist; constructor <;> linarith
    have hρspos : 0 < ρs N := by linarith [hρsI.1]
    set r : ℝ := ρs N / ρ₁ with hr_def
    have hrI : r ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      rw [abs_lt] at hdist
      constructor
      · rw [hr_def, le_div_iff₀ hρ₁pos]; linarith
      · rw [hr_def, div_le_iff₀ hρ₁pos]; linarith
    have hmeas := Step1BandNorm.measurable_dbm d N (v N) (tt N)
    set Hh := dbmMatrix_isHermitian d N (v N) (tt N)
    have hF : Step1BandNorm.F d τs E₀ N k O (ω N) =
        RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N)) Hh k O 0 := rfl
    set Fv := RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N)) Hh k O 0 with hFv
    set sr := scaledPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N)) Hh k O 0 r with hsr
    have hsrA : sr = r ^ k * A N := scaledPairing_eq_pow_mul _ _ _ k O 0 r
    set g' := gue0Ref' d N k O E₀ with hg'
    set D := A N - g' with hD
    -- `|r - 1| ≤ M^{-rate}/ρ₁`
    have hr1 : |r - 1| ≤ mr N / ρ₁ := by
      rw [show r - 1 = (ρs N - ρ₁) / ρ₁ by rw [hr_def]; field_simp, abs_div, abs_of_pos hρ₁pos]
      exact div_le_div_of_nonneg_right hN.2.2 hρ₁pos.le
    -- the Lipschitz term
    set corrQ := RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N)) Hh k Q 0
    have hcorrQ0 : 0 ≤ corrQ := Step1BandNorm.corrPairing_nonneg _ _ _ k hQ0 0
    obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
    obtain ⟨BQ', hBQ'⟩ := hQ'.1.continuous.bounded_above_of_compact_support hQ'.2
    have hcont' : Continuous (fun β : Fin k → ℝ => Q' (fun j => ρs N * β j)) :=
      hQ'.1.continuous.comp (continuous_pi fun j => continuous_const.mul (continuous_apply j))
    have hmono : corrQ ≤ RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (tt N)) Hh k
        (fun β => Q' (fun j => ρs N * β j)) 0 :=
      corrPairing_mono _ Hh k (fun β => hdom (ρs N) hρsI β) 0
        (Step1BandNorm.integrable_corrSum _ hmeas Hh k hQ.1.continuous hBQ _ 0)
        (Step1BandNorm.integrable_corrSum _ hmeas Hh k hcont' (fun β => hBQ' _) _ 0)
    have hcorrQ : corrQ ≤ GQ N + 1 := by
      have : corrQ < GQ N + 1 := by
        have := hQ'N
        simp only [hGQ]
        linarith
      exact this.le
    have hGQ0 : 0 ≤ GQ N :=
      Step1BandNorm.corrPairing_nonneg _ _ _ k (fun β => hQ'0 (fun j => ρ₀ * β j)) 0
    have hlip := hC (gueMeasure d N) (dbmMatrix d N (v N) (tt N)) hmeas Hh 0 1 r
      ⟨by norm_num, by norm_num⟩ hrI
    rw [Step1BandNorm.scaledPairing_one] at hlip
    have hT1 : |Fv - sr| ≤ |C| * (mr N / ρ₁) * (GQ N + 1) := by
      refine hlip.trans ?_
      rw [abs_sub_comm 1 r]
      calc C * |r - 1| * corrQ ≤ |C| * |r - 1| * corrQ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C)
              (abs_nonneg _)) hcorrQ0
        _ ≤ |C| * (mr N / ρ₁) * (GQ N + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr1 (abs_nonneg C)) hcorrQ hcorrQ0
              (by positivity)
    -- `|r^k - 1| ≤ L M^{-rate}`
    have hT2 : |r ^ k - 1| ≤ L * mr N := by
      have h := _root_.abs_pow_sub_pow_le (a := r) (b := 1) (n := k)
      rw [one_pow] at h
      have hmax : max |r| |(1 : ℝ)| ≤ 2 := by
        rw [abs_of_pos (by linarith [hrI.1] : (0 : ℝ) < r), abs_one]
        exact max_le hrI.2 (by norm_num)
      have hpow : max |r| |(1 : ℝ)| ^ (k - 1) ≤ 2 ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_right (abs_nonneg _)) hmax _
      refine h.trans ?_
      calc |r - 1| * k * max |r| |(1 : ℝ)| ^ (k - 1) ≤ (mr N / ρ₁) * k * 2 ^ (k - 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg k)) hpow
              (by positivity) (by positivity)
        _ = L * mr N := by rw [hL_def]; ring
    -- the reference is bounded by a count
    have hT3 : |g'| ≤ Ga N := by
      rw [hg']
      exact Step1BandNorm.abs_corrPairing_le_of_abs_le _ (measurable_Xmat d N)
        (Xmat_isHermitian d N) k (Step1BandNorm.isTestFun_dilate hO hc0)
        (Step1BandNorm.isTestFun_dilate hQa hc0) (fun β => hQaO _) 0
    -- assemble
    have hsplit : Fv - g' = (Fv - sr) + (r ^ k - 1) * (D + g') + D := by
      rw [hsrA, hD]; ring
    have hmul : |(r ^ k - 1) * (D + g')| ≤ (L * mr N) * (|D| + Ga N) := by
      rw [abs_mul]
      exact mul_le_mul hT2 ((abs_add_le D g').trans (by linarith)) (abs_nonneg _)
        (by positivity)
    have heq : |C| * (mr N / ρ₁) * (GQ N + 1) + (L * mr N) * (|D| + Ga N) + |D| =
        |D| * (1 + L * mr N) + |C| / ρ₁ * (mr N * GQ N + mr N) + L * (mr N * Ga N) := by
      field_simp; ring
    rw [Real.norm_eq_abs, hF, hsplit]
    have h3 := abs_add_three (Fv - sr) ((r ^ k - 1) * (D + g')) D
    linarith
  have hU : Tendsto (fun N =>
      |A N - gue0Ref' d N k O E₀| * (1 + L * mr N) + |C| / ρ₁ * (mr N * GQ N + mr N) +
        L * (mr N * Ga N)) atTop (𝓝 0) := by
    have hm0 : Tendsto mr atTop (𝓝 0) :=
      Step1BandNorm.rpow_tendsto_zero d (by linarith : -step1Rate τs < 0)
    have h := ((hA.abs.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hm0.const_mul L))).add
      ((hGc.add hm0).const_mul (|C| / ρ₁))).add (hGa.const_mul L)
    simpa using h
  exact squeeze_zero_norm' hbound hU

/-! ### Uniformity over the good event, measurability, and the assembly -/

/-- The conditional pairing is measurable in the band sample. -/
private theorem Step1BandNorm.measurable_F (d : Dims) (τs E₀ : ℝ) (N k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) :
    Measurable (Step1BandNorm.F d τs E₀ N k O) := by
  set t := ouZeta ((Gauss.band d).tPow τs N)
  have heig : Measurable (fun ω : Ω d => fun i => (Xmat_isHermitian d N ω).eigenvalues i) :=
    measurable_pi_iff.mpr fun i =>
      Step1BandNorm.measurable_eigenvalue (measurable_Xmat d N) (Xmat_isHermitian d N) i
  have hv : Measurable (fun ω : Ω d => vOU d N τs E₀ ω) := by
    unfold vOU
    exact measurable_pi_iff.mpr fun i =>
      (((measurable_pi_apply i).comp heig).const_mul _).sub_const _
  have hGc : Continuous (fun q : (d.Idx N → ℝ) × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Matrix.diagonal (fun i => (q.1 i : ℂ)) + (Real.sqrt t : ℂ) • q.2) := by
    refine Continuous.add ?_ (continuous_snd.const_smul ((Real.sqrt t : ℂ)))
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst))
  have hm : Measurable (fun p : Ω d × Ω d => dbmMatrix d N (vOU d N τs E₀ p.1) t p.2) :=
    hGc.measurable.comp ((hv.comp measurable_fst).prodMk ((measurable_Xmat d N).comp
      measurable_snd))
  have hf := measurable_corrSum hm (fun p => dbmMatrix_isHermitian d N (vOU d N τs E₀ p.1) t p.2)
    k hO (Fintype.card (d.Idx N) : ℝ) 0
  have hint := hf.stronglyMeasurable.integral_prod_right' (ν := gueMeasure d N)
  exact hint.measurable.const_mul _

/-- **Uniformity over the good event** (worst-sequence argument). -/
private theorem Step1BandNorm.uniform (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ)
    (hLL : BandTracialLocalLaw d (κ / 2)) (hG : GUELocalLaw d) {τs : ℝ} (h0 : 0 < τs)
    (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : RBM.IsTestFun O) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ ω ∈ Step1BandNorm.good d κ τs E₀ N,
      |Step1BandNorm.F d τs E₀ N k O ω - gue0Ref' d N k O E₀| ≤ ε := by
  classical
  have hex := Step1Regularity.eventually_exists_step1Good d hκ hLL h0 h1 hE₀
  let b : ℕ → Ω d := fun N =>
    if h : (Step1BandNorm.good d κ τs E₀ N).Nonempty then h.some else fun _ => 0
  have hb1 : ∀ᶠ N in atTop, b N ∈ Step1BandNorm.good d κ τs E₀ N := by
    filter_upwards [hex] with N hN
    have hne : (Step1BandNorm.good d κ τs E₀ N).Nonempty := hN
    have hbN : b N = hne.some := by simp only [b, hne, ↓reduceDIte]
    rw [hbN]; exact hne.some_mem
  have h := RBM.eventually_forall_of_forall_sequences (fun _ _ => True)
    (fun N ω => ω ∈ Step1BandNorm.good d κ τs E₀ N)
    (fun N ω => |Step1BandNorm.F d τs E₀ N k O ω - gue0Ref' d N k O E₀| ≤ ε) b
    (fun _ => trivial) hb1
    (fun f _ hf => by
      have hc := Step1BandNorm.core d h51 hκ hG h0 h1 hE₀ k hO f hf
      filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with N hN
      rw [Real.dist_eq, sub_zero] at hN
      exact hN.le)
  filter_upwards [h] with N hN ω hω using hN ω trivial hω

/-- **Step 1 (2.21)** for the band model at the corrected normalization:
for `τ_* ∈ (0,1)`, `t_* = M^{-1+τ_*}`, bulk `|E₀| ≤ 2 - κ`, every `k` and test function `O`,
`corrPairing(H_{t_*}, O, E₀) - corrPairing(GUE, O((ρ_sc(0)/ρ_sc(E₀)) ·), 0) → 0`
(`ouPairing - gue0Ref'`). Inputs: `LSY22'` (`h51`, corrected [51, Theorem 2.2], the only external
input), the averaged band local law `hLL` (Theorem 2.3) and the averaged GUE local law `hG`. -/
theorem step1_band' (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ)
    (hLL : BandTracialLocalLaw d (κ / 2)) (hG : GUELocalLaw d) {τs : ℝ} (h0 : 0 < τs)
    (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : RBM.IsTestFun O) :
    Tendsto (fun N => ouPairing d N ((Gauss.band d).tPow τs N) k O E₀ -
      gue0Ref' d N k O E₀) atTop (𝓝 0) := by
  set ρ₁ := rhoSc E₀ with hρ₁
  set ρ₀ := rhoSc 0 with hρ₀
  obtain ⟨BO, hBO⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  have hBO' : ∀ x, |O x| ≤ BO := fun x => by simpa [Real.norm_eq_abs] using hBO x
  have hBO0 : 0 ≤ BO := (abs_nonneg _).trans (hBO' 0)
  set K0 : ℝ := 2 * BO with hK0
  have hK00 : 0 ≤ K0 := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hunif := Step1BandNorm.uniform d h51 hκ hLL hG h0 h1 hE₀ k hO (ε / 2) (half_pos hε)
  have hbadP := eventually_step1Good d hκ hLL h0 h1 hE₀ ((2 * k + 1 : ℕ) : ℝ)
  have hsmall : ∀ᶠ N : ℕ in atTop, K0 / (N : ℝ) < ε / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat K0).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hunif, hbadP, hsmall, Step1BandNorm.msize_le_N d, eventually_ge_atTop 1]
    with N hU hB hS hMN hN1
  have hMpos := Step1BandNorm.msize_pos d N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero]
  have htpos : 0 ≤ (Gauss.band d).tPow τs N := by
    rw [Step1BandNorm.tPow_eq]; exact Real.rpow_nonneg hMpos.le _
  rw [ouPairing_eq_integral d N htpos k hO E₀]
  change |∫ ω, Step1BandNorm.F d τs E₀ N k O ω ∂(P d) - gue0Ref' d N k O E₀| < ε
  set c := gue0Ref' d N k O E₀ with hc_def
  have hFb : ∀ ω, |Step1BandNorm.F d τs E₀ N k O ω| ≤ msize d N ^ (2 * k) * BO := fun ω => by
    have h := Step1BandNorm.abs_corrPairing_le (gueMeasure d N) _
      (dbmMatrix_isHermitian d N (vOU d N τs E₀ ω) (ouZeta ((Gauss.band d).tPow τs N))) k
      hBO' 0
    rwa [Step1BandNorm.card_eq] at h
  have hc : |c| ≤ msize d N ^ (2 * k) * BO := by
    have h := Step1BandNorm.abs_corrPairing_le (gueMeasure d N) (Xmat d N)
      (Xmat_isHermitian d N) k (P := fun β => O (fun j => ρ₀ / ρ₁ * β j))
      (fun x => hBO' _) 0
    rwa [Step1BandNorm.card_eq] at h
  have hFint : Integrable (Step1BandNorm.F d τs E₀ N k O) (P d) :=
    Integrable.of_bound
      (Step1BandNorm.measurable_F d τs E₀ N k hO.1.continuous).aestronglyMeasurable
      (msize d N ^ (2 * k) * BO) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hFb ω)
  have hsplit : ∫ ω, Step1BandNorm.F d τs E₀ N k O ω ∂(P d) - c =
      ∫ ω, (Step1BandNorm.F d τs E₀ N k O ω - c) ∂(P d) := by
    rw [integral_sub hFint (integrable_const c), integral_const, probReal_univ, one_smul]
  rw [hsplit]
  refine abs_integral_le_integral_abs.trans_lt ?_
  set T := toMeasurable (P d) (Step1BandNorm.good d κ τs E₀ N)ᶜ with hT_def
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hsubT : (Step1BandNorm.good d κ τs E₀ N)ᶜ ⊆ T := subset_toMeasurable _ _
  set X : ℝ := msize d N ^ (2 * k) * BO + |c| with hX
  have hX0 : 0 ≤ X := by positivity
  have hpt : ∀ ω, |Step1BandNorm.F d τs E₀ N k O ω - c| ≤ ε / 2 + T.indicator (fun _ => X) ω := by
    intro ω
    by_cases hω : ω ∈ Step1BandNorm.good d κ τs E₀ N
    · have h2 : 0 ≤ T.indicator (fun _ => X) ω := Set.indicator_nonneg (fun _ _ => hX0) _
      linarith [hU ω hω]
    · rw [Set.indicator_of_mem (hsubT hω)]
      have := abs_sub (Step1BandNorm.F d τs E₀ N k O ω) c
      linarith [hFb ω]
  have hint : ∫ ω, |Step1BandNorm.F d τs E₀ N k O ω - c| ∂(P d) ≤ ε / 2 + (P d).real T * X := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
      ((integrable_const _).add ((integrable_const _).indicator hTm))
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm), integral_const,
      integral_indicator_const _ hTm, probReal_univ, one_smul, smul_eq_mul]
  have hTreal : (P d).real T ≤ (N : ℝ) ^ (-((2 * k + 1 : ℕ) : ℝ)) := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg N) _) hB
  have hXle : X ≤ K0 * msize d N ^ (2 * k) := by
    have e : K0 * msize d N ^ (2 * k) = msize d N ^ (2 * k) * BO + msize d N ^ (2 * k) * BO := by
      rw [hK0]; ring
    rw [hX, e]; linarith
  have hfinal : (P d).real T * X ≤ K0 / N := by
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast] at hTreal
    have hT0 : 0 ≤ (P d).real T := measureReal_nonneg
    calc (P d).real T * X ≤ ((N : ℝ) ^ (2 * k + 1))⁻¹ * (K0 * msize d N ^ (2 * k)) :=
          mul_le_mul hTreal hXle hX0 (by positivity)
      _ ≤ ((N : ℝ) ^ (2 * k + 1))⁻¹ * (K0 * (N : ℝ) ^ (2 * k)) := by
          gcongr
      _ = K0 / N := by
          rw [pow_succ]; field_simp
  linarith

/-! ### Nondegenerate instance -/

end RBM.Gauss

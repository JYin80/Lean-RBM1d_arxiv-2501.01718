/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step1Hyp
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.EnergyN.Loop.ContinuityAssembly
import RBM1D.Flow.EnergyUniform

/-!
# The hypotheses of Step 1 for the Gaussian flow, at an `N`-dependent energy

Five statements at an `N`-dependent energy `E : ℕ → ℝ`: continuity of `llMax` in time with high
probability (`RBM.Gauss.cont_gaussN`), a lower bound on the a priori right side
(`RBM.Gauss.rpow_neg_le_aprioriRhsN`), (5.8) with a threshold `C₀` (`RBM.Gauss.eq58_seq_thrN`),
the net lift (`RBM.Gauss.netLift_gaussN`), and `N^{-1} ≤ 1 - t` from the regime
(`RBM.Gauss.rpow_neg_one_le_one_sub_of_scale_geN`).

## The external `κ`

`eq58_seq_thrN` needs a bound on `(2/(mE (E N)).im)^n`, and `netLift_gaussN` uses
`(mE (E N)).im` as the smallness scale of `eventually_master_small`, as in
`Step1.eq52_halfN`/`.eq58_seqN`. Both take an explicit external `κ`
(`hE : ∀ N, |E N| ≤ 2 - κ`) and use the uniform `(2/mκ)^n`, `mκ := √(2κ')/2 ≤ (mE (E N)).im` for
every `N` (`κ' := min κ 1`, `mE_im_ge`). `eq58_seq_thrN` is the threshold-`C₀` generalization of
`Step1.eq58_seqN`; `netLift_gaussN` needs only `0 < κ` (no upper bound `κ ≤ 1`), as
`RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecayN`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

open scoped Matrix.Norms.L2Operator

variable {d : Dims}

/-- **With high probability `u ↦ llMax_u` is continuous on `[s, t]`.** No energy-dependent
constant is fixed here: `continuousOn_llMax` (energy-free) is applied at `E N` for each fixed
`N`. -/
theorem cont_gaussN (d : Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    HighProb (P d) (fun N => {ω | ContinuousOn
      (fun u => Step1.llMax (sample d) (E N) N u ω) (Set.Icc (s N) (t N))}) := by
  intro D _
  filter_upwards with N
  have huniv : {ω : Ω d | ContinuousOn
      (fun u => Step1.llMax (sample d) (E N) N u ω) (Set.Icc (s N) (t N))} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact continuousOn_llMax d N (hE N) (hs0 N) (ht1 N) ω
  rw [huniv, Set.compl_univ, measure_empty]
  exact zero_le

/-- **`N^{-(n-1)} ≤ aprioriRhs`** eventually, at every time and loop. No energy-dependent constant
is fixed here: all `E`-uses are pointwise, per fixed `N`, inside the `filter_upwards`. -/
theorem rpow_neg_le_aprioriRhsN {Ωb : Type*} [MeasurableSpace Ωb] (B : Band Ωb) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × LoopData (B.L N) n) (ω : Ωb),
      (N : ℝ) ^ (-((n : ℝ) - 1)) ≤ Step1.aprioriRhs B (E N) s t n N p ω := by
  filter_upwards [B.dim, eventually_ge_atTop 1] with N hdim hN1
  intro p ω
  have hsu : s N ≤ (p.1 : ℝ) := p.1.2.1
  have hut : (p.1 : ℝ) ≤ t N := p.1.2.2
  have hu0 : (0 : ℝ) ≤ (p.1 : ℝ) := (hs0 N).trans hsu
  have hu1 : (p.1 : ℝ) < 1 := hut.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓu : 0 < B.ell N (p.1 : ℝ) := Step3.ellHat_pos_of_lt_one hL1 hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hη : 0 < etaT (E N) (p.1 : ℝ) := etaT_pos_of_lt_one' (hE N) hu1
  rw [aprioriRhs_eq (E N) s t n N p ω hℓu hℓs hW hη]
  set Q : ℝ := B.ell N (s N) * (B.W N : ℝ) * etaT (E N) (p.1 : ℝ) with hQdef
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  have hQN : Q ≤ (N : ℝ) := by
    have h1 : B.ell N (s N) ≤ (B.L N : ℝ) := min_le_right _ _
    have h2 : etaT (E N) (p.1 : ℝ) ≤ 1 := RBM.etaT_le_one (hE N) hu0
    have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
    calc Q ≤ (B.L N : ℝ) * (B.W N : ℝ) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hW.le) h2 hη.le (by positivity)
      _ = (B.W N : ℝ) * B.L N := by ring
      _ ≤ (N : ℝ) := hWL
  have hcast : -((n : ℝ) - 1) = -(((n - 1 : ℕ) : ℝ)) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub this]
      ring
    rw [this]
  rw [hcast, Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_pow]
  exact inv_anti₀ (pow_pos hQ0 _) (pow_le_pow_left₀ hQ0.le hQN _)

variable {Ωb : Type*} [MeasurableSpace Ωb] {B : Band Ωb}

/-- **(5.8) with a threshold `C₀`, along a time sequence `u N ∈ [s N, t N]`**:
`loopIndThr ≺ aprioriRhs`, from (2.68)–(2.70) at `s`, (2.72) and the loop scaling (6.1). -/
theorem eq58_seq_thrN (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ} {κ C₀ : ℝ} (hκ : 0 < κ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (hC₀ : 0 ≤ C₀) (hB : BoundsCoreN X E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScalingN X E t₁ t₂)
    (u : ∀ N, RBM.TimeIcc s t N) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω => loopIndThr X (E N) s t C₀ n N (u N, v) ω)
      (fun N (v : LoopData (B.L N) n) ω => Step1.aprioriRhs B (E N) s t n N (u N, v) ω) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have h1 : ∀ N, 1 / 2 ≤ Step1.startTime s N := fun N => le_max_right _ _
  have h12 : ∀ N, Step1.startTime s N ≤ max (u N : ℝ) (Step1.startTime s N) := fun N =>
    le_max_right _ _
  have h2 : ∀ N, max (u N : ℝ) (Step1.startTime s N) < 1 := fun N =>
    max_lt ((u N).2.2.trans_lt (ht1 N)) (max_lt ((hst N).trans_lt (ht1 N)) (by norm_num))
  have h51 := lemma_5_1'_thrN X hκ hE (c := 1 / 2) (by norm_num) hC₀ h1 h12 h2
    (hS _ _ h1 h12 h2) (Step1.eq55N X hκ hE hB hs0 hst ht1 hc) n hn
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have hm : ∀ N, Real.sqrt (2 * κ') / 2 ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hmpos : 0 < Real.sqrt (2 * κ') / 2 := by positivity
  set C : ℝ := (2 / (Real.sqrt (2 * κ') / 2)) ^ n with hC
  have hC0 : 0 ≤ C := by positivity
  have hu0 : ∀ N, (0 : ℝ) ≤ (u N : ℝ) := fun N => (hs0 N).trans (u N).2.1
  have hu1 : ∀ N, (u N : ℝ) < 1 := fun N => (u N).2.2.trans_lt (ht1 N)
  have hζ0 : ∀ N, 0 ≤ (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
      (B.scale (E N) N (u N))⁻¹ ^ (n - 1) := fun N => by
    have h := Step1.one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N)
    have := (B.scale_pos' (hE2 N) N (hu0 N) (hu1 N))
    positivity
  have hdet : StochDom B.P
      (fun N (_ : LoopData (B.L N) n) (_ : Ωb) => C * ((B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale (E N) N (u N))⁻¹ ^ (n - 1)))
      (fun N _ _ => (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale (E N) N (u N))⁻¹ ^ (n - 1)) :=
    Step1.stochDom_of_le_const_mul (fun N _ _ => mul_nonneg hC0 (hζ0 N)) (fun N _ _ => hζ0 N) C
      fun _ _ _ => le_rfl
  refine Step1.stochDom_of_forall_or h51 hdet fun N v ω => ?_
  by_cases h : Step1.startTime s N ≤ u N
  · left
    have ht2 : max (u N : ℝ) (Step1.startTime s N) = u N := max_eq_left h
    refine ⟨by simp only [loopIndThr, gmaxEventThr_eq, ht2, le_refl], ?_⟩
    simp only [Step1.aprioriRhs, ht2]
    have hL : 1 ≤ B.L N := B.one_le_L N
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hℓs := Step3.ellHat_pos_of_lt_one (L := B.L N) hL hs1
    have hℓu := Step3.ellHat_pos_of_lt_one (L := B.L N) hL (hu1 N)
    have hmono : ellHat (B.L N) ((s N : ℝ) : ℂ) ≤ ellHat (B.L N) ((Step1.startTime s N : ℝ) : ℂ) :=
      Step3.ellHat_mono (le_max_left _ _) (h.trans_lt (hu1 N))
    have hA := (B.scale_pos' (hE2 N) N (hu0 N) (hu1 N))
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (div_nonneg hℓu.le (hℓs.trans_le hmono).le) ?_ _
    simp only [Band.ell]
    exact div_le_div_of_nonneg_left hℓu.le hℓs hmono
  · right
    push Not at h
    have hhalf : (u N : ℝ) ≤ 1 / 2 := by
      rcases lt_max_iff.1 h with h' | h'
      · exact absurd (u N).2.1 (not_le.2 h')
      · exact h'.le
    refine ⟨?_, le_rfl⟩
    have hind : loopIndThr X (E N) s t C₀ n N (u N, v) ω ≤ ‖X.Lval (E N) N (u N) ω v.idx‖ :=
      Set.indicator_le_self' (fun _ _ => norm_nonneg _) ω
    refine hind.trans ((Step1.norm_Lval_le_of_le_half X (hE2 N) N (hu0 N) hhalf ω hn v).trans ?_)
    have hR := one_le_pow₀ (n := n - 1) (Step1.one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N))
    have hA := (B.scale_pos' (hE2 N) N (hu0 N) (hu1 N))
    have hA' : 0 ≤ (B.scale (E N) N (u N))⁻¹ ^ (n - 1) := by positivity
    have hbound : (2 / (mE (E N)).im) ^ n ≤ C := by
      rw [hC]
      have h1 : (2 : ℝ) / (mE (E N)).im ≤ 2 / (Real.sqrt (2 * κ') / 2) :=
        div_le_div_of_nonneg_left (by norm_num) hmpos (hm N)
      exact pow_le_pow_left₀ (div_nonneg (by norm_num) (hmpos.trans_le (hm N)).le) h1 n
    have h2 := mul_le_mul_of_nonneg_right hR hA'
    rw [one_mul] at h2
    calc (2 / (mE (E N)).im) ^ n * (B.scale (E N) N (u N))⁻¹ ^ (n - 1)
        ≤ C * (B.scale (E N) N (u N))⁻¹ ^ (n - 1) := mul_le_mul_of_nonneg_right hbound hA'
      _ ≤ C * ((B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
          (B.scale (E N) N (u N))⁻¹ ^ (n - 1)) := mul_le_mul_of_nonneg_left h2 hC0

/-- **The net lift of Step 1 for the Gaussian flow**: from `loopIndThr ≺ aprioriRhs` along every
time sequence, the bound `loopInd ≺ aprioriRhs` uniformly in time (`Step1.NetLift`). It takes
`κ, hκ0 : 0 < κ` and uses the uniform `mκ := √(2κ')/2 ≤ (mE (E N)).im` as the `m0` of
`eventually_master_small`. -/
theorem netLift_gaussN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ 1 - t N)
    {n : ℕ} (hn : 1 ≤ n)
    (hrel : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom (P d) (fun N v ω => loopIndThr (sample d) (E N) s t 3 n N (u N, v) ω)
        (fun N v ω => Step1.aprioriRhs (band d) (E N) s t n N (u N, v) ω)) :
    Step1.NetLift (P d) s t (fun N p ω => Step1.loopInd (sample d) (E N) s t n N p ω)
      (fun N p ω => Step1.aprioriRhs (band d) (E N) s t n N p ω) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hm : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hmκpos : 0 < mκ := by rw [hmκdef]; positivity
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set A : ℝ := 2 * (c * ((n : ℝ) + 1) + (n : ℝ) + 3) with hAdef
  have hA2 : A / 2 = c * ((n : ℝ) + 1) + (n : ℝ) + 3 := by rw [hAdef]; ring
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hAc : -A < -c := by rw [hAdef]; nlinarith
  refine netLift_of_relaxed (P := P d) (s := s) (t := t) hst (T := 1) one_pos
    (fun N => by linarith [hs0 N, ht1 N]) (A := A) (B := (n : ℝ) - 1) hA0 hrel
    (highProb_norm_Xmat_le d) (rpow_neg_le_aprioriRhsN (band d) hE2 hs0 hst ht1 hn) ?_
  filter_upwards [hreg, eventually_master_small (n := n) (c := c) (m0 := mκ) hmκpos hA2,
    eventually_const_mul_rpow_le_rpow (2 * ((n - 1 : ℕ) : ℝ)) hAc, eventually_ge_atTop 1]
    with N hregN hmaster hκ2 hN1
  intro ω hω u u' hd v
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ht0 : (0 : ℝ) ≤ t N := le_trans (hs0 N) (hst N)
  have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE2 N) (ht1 N)
  set q : ℝ := (etaT (E N) (t N))⁻¹ with hqdef
  have hq1 : (1 : ℝ) ≤ q := one_le_inv_etaT (hE2 N) ht0 (ht1 N)
  have hq0 : (0 : ℝ) < q := by linarith
  -- (2): slow variation of the right side
  have hsv : Step1.aprioriRhs (band d) (E N) s t n N (u', v) ω
      ≤ 2 * Step1.aprioriRhs (band d) (E N) s t n N (u, v) ω := by
    refine aprioriRhs_le_two_mul (band d) (hE2 N) hs0 hst ht1 hn (ε := (N : ℝ) ^ (-A)) ?_ u u' hd v ω
    exact hκ2.trans hregN
  refine ⟨?_, hsv⟩
  -- the master bound at `η = η_{t_N}`, uniform via `mκ ≤ (mE (E N)).im`
  have hηlow : (N : ℝ) ^ (-c) * mκ ≤ etaT (E N) (t N) := by
    show _ ≤ (1 - t N) * (mE (E N)).im
    have h1 : (N : ℝ) ^ (-c) * mκ ≤ (N : ℝ) ^ (-c) * (mE (E N)).im :=
      mul_le_mul_of_nonneg_left (hm N) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right hregN (mE_im_nonneg (E N))
  have hMB := hmaster (etaT (E N) (t N)) hηt hηlow
  rw [← hqdef] at hMB
  -- `√|u-u'| ≤ N^{-A/2}`
  have hsqrt : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-(A / 2)) := by
    refine (Real.sqrt_le_sqrt hd).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  set X : ℝ := ‖Xmat d N ω‖ with hXdef
  have hXN : X ≤ (N : ℝ) := hω
  set Δ : ℝ := q * q * (X + 1) * Real.sqrt |(u : ℝ) - (u' : ℝ)| with hΔdef
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; positivity
  have hΔle : Δ ≤ q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by
    rw [hΔdef]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hsqrt
      (Real.sqrt_nonneg _) (by positivity)
  have hqq : q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))
      ≤ (n : ℝ) * q ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by
    have hpow : q * q ≤ (n : ℝ) * q ^ (n + 1) := by
      have h1 : q ^ 2 ≤ q ^ (n + 1) := pow_le_pow_right₀ hq1 (by omega)
      have h2 : q ^ 2 = q * q := by ring
      nlinarith [pow_nonneg hq0.le (n + 1)]
    have hrest : (0 : ℝ) ≤ ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by positivity
    calc q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))
        = (q * q) * (((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) := by ring
      _ ≤ ((n : ℝ) * q ^ (n + 1)) * (((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) :=
          mul_le_mul_of_nonneg_right hpow hrest
      _ = (n : ℝ) * q ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by ring
  have hΔsmall : Δ ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := (hΔle.trans hqq).trans hMB
  have hNn1 : (N : ℝ) ^ (-((n : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hΔ1 : Δ ≤ 1 := hΔsmall.trans hNn1
  -- the entrywise modulus of the resolvent
  have hGop : ‖green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ))
      - green (Hflow d N (u' : ℝ) ω) (zt (E N) (u' : ℝ))‖ ≤ Δ :=
    norm_green_flow_sub_le_sqrt d N (hE2 N) (hs0 N) (ht1 N) ω u.2 u'.2
  have hexp : -(((n : ℝ) - 1) + 2) = -((n : ℝ) + 1) := by ring
  rw [hexp]
  by_cases hωu : ω ∈ Step1.gEv (sample d) (E N) N (u : ℝ)
  · have hmem' : ω ∈ gEvThr (sample d) (E N) N (u' : ℝ) 3 := by
      intro i j
      have h1 : ‖green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) i j
          - green (Hflow d N (u' : ℝ) ω) (zt (E N) (u' : ℝ)) i j‖ ≤ Δ := by
        refine le_trans ?_ hGop
        exact norm_apply_le_l2_opNorm (green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ))
          - green (Hflow d N (u' : ℝ) ω) (zt (E N) (u' : ℝ))) i j
      have h3 : ‖green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) i j‖ ≤ 2 := hωu i j
      have h5 := norm_sub_le (green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) i j)
        (green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) i j
          - green (Hflow d N (u' : ℝ) ω) (zt (E N) (u' : ℝ)) i j)
      rw [sub_sub_cancel] at h5
      show ‖green (Hflow d N (u' : ℝ) ω) (zt (E N) (u' : ℝ)) i j‖ ≤ 3
      linarith
    rw [Step1.loopInd, Set.indicator_of_mem hωu, loopIndThr, Set.indicator_of_mem hmem']
    have hL := norm_Lval_sub_le_sqrt d N (hE2 N) (hs0 N) (ht1 N) ω u.2 u'.2 hn v
    have hLsub : ‖(sample d).Lval (E N) N (u : ℝ) ω v.idx‖
        - ‖(sample d).Lval (E N) N (u' : ℝ) ω v.idx‖ ≤ (n : ℝ) * (Δ * q ^ (n - 1)) := by
      refine le_trans (norm_sub_norm_le _ _) ?_
      rw [← hqdef, ← hXdef] at hL
      exact hL
    have hfin : (n : ℝ) * (Δ * q ^ (n - 1)) ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := by
      refine le_trans ?_ hMB
      have hqs : q ^ (n - 1) * (q * q) = q ^ (n + 1) := by
        rw [show q * q = q ^ 2 by ring, ← pow_add]
        congr 1
        omega
      calc (n : ℝ) * (Δ * q ^ (n - 1))
          ≤ (n : ℝ) * ((q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) * q ^ (n - 1)) := by
            have := mul_le_mul_of_nonneg_right hΔle (pow_nonneg hq0.le (n - 1))
            exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
        _ = (n : ℝ) * (q ^ (n - 1) * (q * q)) * (((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) := by
            ring
        _ = (n : ℝ) * q ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by
            rw [hqs]; ring
    linarith
  · rw [Step1.loopInd, Set.indicator_of_notMem hωu]
    have h1 : 0 ≤ loopIndThr (sample d) (E N) s t 3 n N (u', v) ω :=
      loopIndThr_nonneg _ _ _ _ _ _ _ _ _
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := Real.rpow_nonneg hN0.le _
    linarith

/-- **`N^{-1} ≤ 1 - t` eventually**, from `N^c ≤ W ℓ_t η_t` eventually. No energy-dependent
constant is fixed here: `(mE (E N)).im` is computed after `N` is fixed, inside
`filter_upwards`. -/
theorem rpow_neg_one_le_one_sub_of_scale_geN {Ωb : Type*} [MeasurableSpace Ωb] (B : Band Ωb)
    {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 - t N := by
  filter_upwards [hreg, B.dim, eventually_ge_atTop 1] with N hregN hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
  have hℓL : B.ell N (t N) ≤ (B.L N : ℝ) := min_le_right _ _
  have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
  have hscale : B.scale (E N) N (t N) ≤ (N : ℝ) * etaT (E N) (t N) := by
    rw [Band.scale]
    calc (B.W N : ℝ) * B.ell N (t N) * etaT (E N) (t N)
        ≤ (B.W N : ℝ) * (B.L N : ℝ) * etaT (E N) (t N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓL hW.le) hη.le
      _ ≤ (N : ℝ) * etaT (E N) (t N) := mul_le_mul_of_nonneg_right hWL hη.le
  have hkey : (N : ℝ) ^ (c - 1) ≤ etaT (E N) (t N) := by
    have h1 := hregN.trans hscale
    have he : (N : ℝ) ^ (c - 1) = (N : ℝ) ^ c / (N : ℝ) := by
      rw [show c - 1 = c + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one,
        div_eq_mul_inv]
    rw [he, div_le_iff₀ hN0]
    linarith
  have hmono : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (c - 1) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hm1 : (mE (E N)).im ≤ 1 := RBM.mE_im_le_one (hE N)
  have hm0 : 0 < (mE (E N)).im := mE_im_pos (hE N)
  have hlast : etaT (E N) (t N) ≤ 1 - t N := by
    show (1 - t N) * (mE (E N)).im ≤ 1 - t N
    nlinarith [ht1 N]
  linarith

end RBM.Gauss

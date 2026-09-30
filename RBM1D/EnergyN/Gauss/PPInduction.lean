/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PPInduction
import RBM1D.EnergyN.Gauss.PPGoodEvent
import RBM1D.EnergyN.Gauss.GridAssembly
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Unif.Gauss.Lemma514Holder

/-!
# The `(+,+)` induction on the grid at an `N`-dependent energy

Five statements at an `N`-dependent energy `E : ℕ → ℝ`: the pathwise grid assembly
(`grid_assembly_pathwiseN`), the zone bound `ev_zoneN` and its consequence `ev_Lg_leN`, the
bound on `JPP` along the grid on a high-probability event (`pp_grid_bound_plainN`), and the bound
`JPP ≺ 1 + R² + R^{5/2}` at every time (`pp_endpoint_seq_plainN`). The three statements of the
uniform `(+,+)` bound are in `RBM1D/EnergyN/Gauss/PPUniform.lean`.

## The external `κ`

`ev_zoneN` (and, through it, `ev_Lg_leN`): the constant `K' := (mE (E N)).im⁻¹ * (8/c) + 1`
must be fixed before `∀ᶠ N`, and `(mE (E N)).im` has no uniform-in-`N` lower bound from
`∀ N, |E N| < 2` alone. So they take `{κ : ℝ} (hκ0 : 0 < κ)` and
`(hEκ : ∀ N, |E N| ≤ 2 - κ)`, set `κ' := min κ 1`, `mκ := √(2κ')/2`, use
`mE_im_ge hκ'0 hκ'2 (hEκ' N) : mκ ≤ (mE (E N)).im` for every `N` (as in `eventually_constsN` of
`RBM1D/EnergyN/Gauss/GridSharp47.lean`), and fix `K' := mκ⁻¹ * (8/c) + 1` once, uniform in `N`.

`pp_grid_bound_plainN` obtains its kernel constant `Bk` from
`RBM.Gauss.exists_norm_Kval_le_upto_unif (band d) hκ0 hκ1 2`, which takes `κ` directly and gives
`∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - κ → ∀ N w, …`; `Bk` is obtained once (uniform in `N`) and then
applied pointwise at `(E N) (hEκ N)` inside the `∀ᶠ N` block.

Energy-dependent dependencies: `highProb_grid_goodSetPP_plainN`, `highProb_init_ppN`
(`Gauss/PPGoodEvent.lean`), `etaT_inv_le_of_plainN`, `sum_step_div_eta_le_plainN`
(`Gauss/Step2Plain.lean` / `Gauss/GridAssembly.lean`), `exists_norm_Kval_le_upto_unif`
(`RBM1D/EnergyN/Unif/Gauss/Lemma514Holder.lean`), `plain_endpointN`, `scale_endpointN`
(`Gauss/Step2Plain.lean`). Every other callee (`PPAssemblyHyp.toPW`,
`grid_assembly_stopped_pathwise`, `KPP`/`KPP_ne_zero`/`KPP_ge`/`KPP_le`/`KPP_card`, `ev_moments`,
`ev_natpow`, `step_KPP_le`, `H_eq_zero_of_step`, `measure_le_ofReal_of_real`,
`pp_closure_fixedN_plain`, `hsmall_of`, `htail_of`, `hqv_pp`, `ppHyp_real`, `scale_le_N_pp`,
`scale_anti_pp`, `rpow_neg_W_le`, `PPP`/`PPP_nonneg`/`PPP_le`, `vPP_le`, `wPP_le`,
`measurableSet_lt_tauPP'`, `stronglyMeasurable_gridZC`, `gridΦG_testFun`, `goodEvent_pp_imp`,
`H_measurable_filt`, `map_H_eq`, `time_last`, `App`, `Ast`, `Dpp`, `Zpp`, `Ypp`, `Rpp`, `dPP`,
`cPPnn`, `errPP`, `hX2_of`, `hX4_of`, `hqvtail_of`, `hRt_of`, `sq_rpow_five_halves`) is
energy-free or a generic helper, applied at the concrete real `E N`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Finset MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### The pathwise grid assembly -/

section InstantiationN

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- **The pathwise grid assembly**: given the assembly hypothesis `PPAssemblyHyp` and conditional
sub-Gaussian bounds for the martingale increments, there is an event `G` with
`μ(Gᶜ) ≤ N^{-D₁}` on which `‖A_k‖` is bounded by the initial, drift, martingale, `N^{-D}` and
step-error terms, for all `k ≤ K`. No energy-dependent constant is fixed here: only the
substitution `E ↦ E N` inside the `∀ᶠ N` body. -/
theorem grid_assembly_pathwiseN {ε : ℝ} (hε : 0 < ε) (D D₁ C_L C_P C_K : ℝ) (hCK0 : 0 ≤ C_K)
    (hCK : D₁ + 4 * D + 2 * C_L + 2 * C_P + 8 ≤ C_K) {κ : ℝ} {E : ℕ → ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) :
    ∀ᶠ N : ℕ in atTop, ∀ (K L : ℕ) [NeZero L], 1 ≤ K → K ≤ ⌈(N : ℝ) ^ C_K⌉₊ →
      (L : ℝ) ≤ (N : ℝ) ^ C_L →
      ∀ (u : ℕ → ℝ) (τ : Ω' → ℕ) (Δ : ℝ) (A0 : Ω' → LoopArg L 2 → ℂ)
        (A Dr Z Y R : ℕ → Ω' → LoopArg L 2 → ℂ) (dDrift : ℕ → Ω' → ℝ)
        (c : ℕ → LoopArg L 2 → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      Δ ≤ (N : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 → 0 ≤ P → P ≤ (N : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) →
      (∀ i, StronglyMeasurable[ℱ i] (Z i)) →
      (∀ k ≤ K, ∀ (a : LoopArg L 2) (j : ℕ), j < k →
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L (xiPP (E N)) (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).re)
            (c k a j) μ ∧
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L (xiPP (E N)) (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).im)
            (c k a j) μ) →
      PPAssemblyHyp μ ℱ L (E N) u τ Δ K A0 A Dr Z Y R dDrift c v w stepErr →
      ∃ G : Set Ω', μ.real Gᶜ ≤ (N : ℝ) ^ (-D₁)
        ∧ ∀ ω ∈ G, 0 < τ ω → ∀ k ≤ K, ∀ a : LoopArg L 2,
          ‖A k ω a‖ ≤ CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
            + Δ * ∑ j ∈ range k, CU κ ^ 2 * dDrift j ω
            + (N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k, (c k a j : ℝ))
            + (N : ℝ) ^ (-D)
            + ∑ j ∈ range k, (1 + (1 - u k)⁻¹) ^ 2 * stepErr j := by
  have hCK' : D₁ + 4 * D + ((2 : ℕ) : ℝ) * C_L + 2 * C_P + 8 ≤ C_K := by
    push_cast; linarith
  filter_upwards [grid_assembly_stopped_pathwise (μ := μ) (ℱ := ℱ) 2 hε D D₁ C_L C_P C_K hCK0
    hCK'] with N hN
  intro K L _ hK1 hK hL u τ Δ A0 A Dr Z Y R dDrift c v w stepErr P hΔ hKΔ hP0 hP hv hw hτmeas
    hZmeas hqv h
  obtain ⟨G, hG, hbd⟩ := hN K L hK1 hK hL (xiPP (E N)) u τ Δ (L : ℝ) false A0 A Dr Z Y R
    (fun _ _ => CU κ ^ 2) (fun _ _ => 0) 0 dDrift (fun _ _ => 0) c v w stepErr P hΔ hKΔ hP0 hP
    hv hw hτmeas hZmeas hqv (h.toPW hκ0 hκ1 (hEκ N))
  refine ⟨G, hG, fun ω hω hτ k hk a => ?_⟩
  have := hbd ω hω hτ k hk a
  simpa using this

end InstantiationN

/-! ### The zone bounds `ev_zoneN`, `ev_Lg_leN` -/

/-- **`A · LgPP² ≤ N^{c/2}` eventually.** The constant `K' := (mE (E N)).im⁻¹ * (8/c) + 1` is
bounded by the uniform `K' := mκ⁻¹ * (8/c) + 1`, `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N`
(`κ' := min κ 1`, `mE_im_ge`). -/
theorem ev_zoneN {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hEκ : ∀ N, |E N| ≤ 2 - κ) {c A : ℝ}
    (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, A * LgPP (E N) N ^ 2 ≤ (N : ℝ) ^ (c / 2) := by
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'2 : κ' ≤ 2 := (min_le_right κ 1).trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hEκ N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκ0 : 0 < mκ := by positivity
  have hm : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  set K' : ℝ := mκ⁻¹ * (8 / c) + 1 with hK'
  have hK'0 : 0 ≤ K' := by rw [hK']; have := inv_nonneg.2 hmκ0.le; positivity
  filter_upwards [eventually_const_mul_rpow_le_rpow (|A| * K' ^ 2)
    (show c / 4 < c / 2 by linarith), eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hlog := Real.log_le_rpow_div hN0 (show 0 < c / 8 by linarith)
  have hδ1 : 1 ≤ (N : ℝ) ^ (c / 8) := Real.one_le_rpow hN1' (by linarith)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1'
  have hinv : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκ0 (hm N)
  have hLg : LgPP (E N) N ≤ K' * (N : ℝ) ^ (c / 8) := by
    unfold LgPP
    rw [hK']
    have h1 : (mE (E N)).im⁻¹ * Real.log N ≤ mκ⁻¹ * ((N : ℝ) ^ (c / 8) / (c / 8)) := by
      calc (mE (E N)).im⁻¹ * Real.log N ≤ mκ⁻¹ * Real.log N :=
            mul_le_mul_of_nonneg_right hinv hlog0
        _ ≤ mκ⁻¹ * ((N : ℝ) ^ (c / 8) / (c / 8)) :=
            mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hmκ0.le)
    have h2 : mκ⁻¹ * ((N : ℝ) ^ (c / 8) / (c / 8)) = mκ⁻¹ * (8 / c) * (N : ℝ) ^ (c / 8) := by
      field_simp
    nlinarith
  have hLg0 : 0 ≤ LgPP (E N) N := by
    unfold LgPP
    have h0 : 0 ≤ (mE (E N)).im⁻¹ := inv_nonneg.2 (hmκ0.trans_le (hm N)).le
    positivity
  have hsq : LgPP (E N) N ^ 2 ≤ K' ^ 2 * (N : ℝ) ^ (c / 4) := by
    have := pow_le_pow_left₀ hLg0 hLg 2
    have e1 : ((N : ℝ) ^ (c / 8)) ^ 2 = (N : ℝ) ^ (c / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num; ring_nf
    have e : (K' * (N : ℝ) ^ (c / 8)) ^ 2 = K' ^ 2 * (N : ℝ) ^ (c / 4) := by
      rw [mul_pow, e1]
    linarith
  calc A * LgPP (E N) N ^ 2 ≤ |A| * LgPP (E N) N ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    _ ≤ |A| * (K' ^ 2 * (N : ℝ) ^ (c / 4)) := mul_le_mul_of_nonneg_left hsq (abs_nonneg A)
    _ = |A| * K' ^ 2 * (N : ℝ) ^ (c / 4) := by ring
    _ ≤ (N : ℝ) ^ (c / 2) := hN

/-- **`A · LgPP ≤ N^δ` eventually.** It takes the same `κ, hEκ` as `ev_zoneN`, of which it is a
direct one-line consumer. -/
theorem ev_Lg_leN {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hEκ : ∀ N, |E N| ≤ 2 - κ) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, A * LgPP (E N) N ≤ (N : ℝ) ^ δ := by
  filter_upwards [ev_zoneN hκ0 hEκ (A := A) (show 0 < 2 * δ by linarith), eventually_ge_atTop 1]
    with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hE : |E N| < 2 := by linarith [hEκ N]
  have hLg1 : 1 ≤ LgPP (E N) N := by
    unfold LgPP
    have := mul_nonneg (inv_nonneg.2 (mE_im_pos hE).le) (Real.log_nonneg hN1')
    linarith
  have hsq : LgPP (E N) N ≤ LgPP (E N) N ^ 2 := by nlinarith
  calc A * LgPP (E N) N ≤ A * LgPP (E N) N ^ 2 := mul_le_mul_of_nonneg_left hsq hA
    _ ≤ (N : ℝ) ^ (2 * δ / 2) := hN
    _ = (N : ℝ) ^ δ := by ring_nf

/-! ### The bound on `JPP` along the grid -/

set_option maxHeartbeats 4000000 in
-- long chain of `filter_upwards`/`set`-bound real quantities
/-- **`JPP ≤ 2 cPrimePP` along the grid on a high-probability event**: eventually there is
`G ⊆ goodEventPP` with `P(Gᶜ) ≤ N^{-D₁}` on which the bound holds at all grid times. The kernel
constant `Bk` comes from `exists_norm_Kval_le_upto_unif (band d) hκ0 hκ1 2`, taking `κ` directly;
it is obtained once (uniform in `N`) and applied pointwise at `(E N) (hEκ N)`. -/
theorem pp_grid_bound_plainN (d : Dims) {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c / 8) {D₁ : ℝ} (hD₁ : 0 < D₁) :
    ∀ᶠ N : ℕ in atTop, ∃ G : Set (Ωg d), (Pg d) Gᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) ∧
      G ⊆ goodEventPP d (E N) ε ((band d).ell N (s N)) 20 s t (KPP D₁) N ∧
      ∀ ω ∈ G, ∀ k ≤ KPP D₁ N,
        JPP d (E N) N (time s t (KPP D₁) N k) (H d s t (KPP D₁) N k ω)
          ≤ 2 * cPrimePP d κ (E N) ε s t N := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  obtain ⟨Bk, hBk0, hBkC⟩ := exists_norm_Kval_le_upto_unif (band d) hκ0 hκ1 2
  obtain ⟨C₄, C₈, hC₄, hC₈, hmom⟩ := ev_moments d
  have hK0 : ∀ N, KPP D₁ N ≠ 0 := KPP_ne_zero D₁
  have H1 := highProb_grid_goodSetPP_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hcond hc0 hreg0 hAc
    (KPP D₁) hK0
    (by linarith : (0 : ℝ) ≤ D₁ + 101) (KPP_card D₁ hD₁) hε (by norm_num : (0 : ℝ) < 20)
  have H2 := highProb_init_ppN d hE hB hs0 hst ht1 (KPP D₁) hK0 hε
  have HT1 := grid_assembly_pathwiseN (μ := Pg d) (ℱ := filt d) hε 3 (D₁ + 1) 1 20 (D₁ + 100)
    (by linarith) (by linarith) hκ0 hκ1 hEκ
  have hW1c := d.c_pos
  have hbandW : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    filter_upwards [eventually_const_mul_rpow_le_rpow (2 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)]
      with N hN
    simpa using hN
  filter_upwards [H1 (D₁ + 1) (by linarith), H2 (D₁ + 1) (by linarith), HT1, d.dim,
    d.bandwidth, etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc,
    sum_step_div_eta_le_plainN d hE hs0 hst ht1 hc0 hreg0 hAc (KPP D₁) hK0, hreg0, hAc, hmom,
    eventually_ge_atTop 3, hbandW,
    ev_natpow (CU κ ^ 2 * 6 * Real.exp 1 * (1 + Bk)) (show 6 < 10 by norm_num),
    ev_natpow (CU κ ^ 2 * 12 * Real.exp 1) (show 3 < 10 by norm_num),
    ev_natpow ((CU κ ^ 2) ^ 2 * 4) (show 5 < 9 by norm_num),
    ev_natpow (6 : ℝ) (show 14 < 100 by norm_num),
    ev_natpow (6 : ℝ) (show 29 < 100 by norm_num),
    ev_natpow (2 ^ 19 * (1 + Bk) ^ 4) (show 19 < 50 by norm_num),
    ev_natpow ((CU κ ^ 2) ^ 2 * 262144 * (2 * C₄ + 8 * C₈ + 11)) (show 18 < 20 by norm_num),
    ev_zoneN hκ0 hEκ (A := 72 * Real.exp 1 * CU κ ^ 2 * C0PP κ) (half_pos hc0)]
    with N hNgood hNinit hNT1 hdim hband hηt hsum hreg0N hAcN hmomN hN3 hsqrt2 hG1 hG2 hG3 hG4
      hG5 hG6 hG8 hG9
  -- basic facts at `N`
  set K := KPP D₁ with hKdef
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hWL : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hL1 : (1 : ℝ) ≤ d.L N := by
    have := d.three_le_L N; exact_mod_cast (show 1 ≤ d.L N by omega)
  have hWN : (d.W N : ℝ) ≤ N := by nlinarith
  have hLN : (d.L N : ℝ) ≤ N := by nlinarith
  have hWsqrt : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N := by
    refine le_trans ?_ hband
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hW2 : (2 : ℝ) ≤ d.W N := hsqrt2.trans hWsqrt
  have hs0N := hs0 N
  have hstN := hst N
  have ht1N := ht1 N
  have hηt0 : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) ht1N
  have hNc1 : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1 hc0.le
  have hAt1 : 1 ≤ (band d).scale (E N) N (t N) := hNc1.trans hAcN
  have hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval (E N) N w J‖ ≤ Bk := by
    intro w hw J hJ h2 h2'
    have hw1 : w < 1 := lt_of_le_of_lt hw.2 ht1N
    have hlen : J.length = 2 := le_antisymm h2' h2
    have h := hBkC (E N) (hEκ N) N w hw.1 hw1 J hJ h2 h2'
    rw [hlen] at h
    have hA : 1 ≤ (band d).scale (E N) N w := hAt1.trans (scale_anti_pp hw.2 ht1N)
    have hAinv : ((band d).scale (E N) N w)⁻¹ ^ (2 - 1) ≤ 1 := by
      simpa using inv_le_one_of_one_le₀ hA
    calc ‖(band d).Kval (E N) N w J‖ ≤ Bk * ((band d).scale (E N) N w)⁻¹ ^ (2 - 1) := h
      _ ≤ Bk * 1 := mul_le_mul_of_nonneg_left hAinv hBk0
      _ = Bk := mul_one _
  have hNε : (N : ℝ) ^ ε ≤ N := by
    have hc1 : (N : ℝ) ^ c ≤ N := by
      have h1 : (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N) := hAcN
      exact h1.trans (scale_le_N_pp (hE N) hWL (hs0N.trans hstN) ht1N)
    have hεc' : ε ≤ c := by linarith
    calc (N : ℝ) ^ ε ≤ (N : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hN1 hεc'
      _ ≤ N := hc1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hc'0 : 0 ≤ cPrimePP d κ (E N) ε s t N := by
    unfold cPrimePP C0PP LgPP
    have := RPP_nonneg d s t N
    have := Real.rpow_nonneg (RPP_nonneg d s t N) (5 / 2 : ℝ)
    have := inv_nonneg.2 (mE_im_pos (hE N)).le
    have := Real.rpow_nonneg hN0.le ε
    positivity
  have hJ0c : ∀ ω, JPP d (E N) N (time s t K N 0) (H d s t K N 0 ω) ≤ (N : ℝ) ^ ε →
      JPP d (E N) N (time s t K N 0) (H d s t K N 0 ω) ≤ 2 * cPrimePP d κ (E N) ε s t N := by
    intro ω h
    refine h.trans ?_
    have h1 : (N : ℝ) ^ ε ≤ cPrimePP d κ (E N) ε s t N := by
      unfold cPrimePP C0PP
      have hLg1 : 1 ≤ LgPP (E N) N := by
        unfold LgPP
        have := mul_nonneg (inv_nonneg.2 (mE_im_pos (hE N)).le) hlog
        linarith
      exact one_le_cprime (sq_nonneg _) (Real.one_le_rpow hN1 hε.le) (RPP_nonneg d s t N)
        (Real.rpow_nonneg (RPP_nonneg d s t N) _) hLg1
    linarith
  -- the probability of the good event
  set Good := goodEventPP d (E N) ε ((band d).ell N (s N)) 20 s t K N with hGood
  have hGoodc : (Pg d) Goodᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))
      + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) := by
    have hsub : Goodᶜ ⊆ ({ω | ∀ k : Fin (K N + 1), H d s t K N k ω ∈
          goodSetPP d (E N) N (time s t K N k) ε ((band d).ell N (s N)) 20}ᶜ ∪
        {ω | JPP d (E N) N (time s t K N 0) (H d s t K N 0 ω) ≤ (N : ℝ) ^ ε}ᶜ) := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
      exact hω ⟨hcon.1, hcon.2⟩
    calc (Pg d) Goodᶜ ≤ (Pg d) _ := measure_mono hsub
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add hNgood hNinit)
  have hprob3 : ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))
      + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
    have h0 : 0 ≤ (N : ℝ) ^ (-(D₁ + 1)) := Real.rpow_nonneg hN0.le _
    rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have h1 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have h3 : 3 * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN3'
    nlinarith
  by_cases hstr : s N < t N
  · -- the main case
    set τ := tauPP' d (E N) ε 20 s t K N with hτdef
    have hK1 : 1 ≤ K N := Nat.one_le_iff_ne_zero.mpr (hK0 N)
    have hKle : K N ≤ ⌈(N : ℝ) ^ (D₁ + 100)⌉₊ := KPP_le D₁ (by exact_mod_cast hN1)
    have hL : (d.L N : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hLN
    have hΔ : step s t K N ≤ (N : ℝ) ^ (-(D₁ + 100)) := step_KPP_le D₁ hN1 hs0N hstN ht1N
    have hΔ0 : 0 ≤ step s t K N := step_nonneg' s t K N hstN
    have hKΔ : (K N : ℝ) * step s t K N ≤ 1 := by
      unfold step
      rw [mul_div_cancel₀ _ (by exact_mod_cast hK0 N)]
      linarith
    have hΔ1 : step s t K N ≤ 1 := by
      refine hΔ.trans ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hΔN : step s t K N * N ≤ 1 := by
      have h1 : (N : ℝ) ^ (-(D₁ + 100)) * N ≤ 1 := by
        rw [show (N : ℝ) ^ (-(D₁ + 100)) * N = (N : ℝ) ^ (-(D₁ + 100)) * (N : ℝ) ^ (1 : ℝ) by
          rw [Real.rpow_one], ← Real.rpow_add hN0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      calc step s t K N * N ≤ (N : ℝ) ^ (-(D₁ + 100)) * N := mul_le_mul_of_nonneg_right hΔ hN0.le
        _ ≤ 1 := h1
    obtain ⟨hm4, hm8, hm2⟩ := hmomN
    have hP0 := PPP_nonneg d κ (E N) t N
    have hP : PPP d κ (E N) t N ≤ (N : ℝ) ^ (20 : ℝ) := by
      have h := PPP_le d κ (E N) hC₄ hC₈ hN1 hWL hηt0 hηt hm4 hm8 hm2
      rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact h.trans hG8
    have hφ6nn : 0 ≤ phi6PP d ε s t N := by
      unfold phi6PP; have := Real.rpow_nonneg hN0.le ε; positivity
    have hφ6 : (N : ℝ) ^ ε * ((band d).ell N (t N) / (band d).ell N (s N)) ^ 5 + 1
        ≤ phi6PP d ε s t N := by
      unfold phi6PP
      rw [sq_rpow_five_halves (RPP_nonneg d s t N)]
      exact le_rfl
    have hsmall := hsmall_of (Kf := K) d (hE N) hs0N hstN ht1N hN1 hD₁.le hWL hηt hΔ
      (by exact_mod_cast hG4)
    have htail := htail_of (Kf := K) d (hE N) hstN ht1N hN1 hD₁.le hWL hWN hW2 hηt hΔ
      (by exact_mod_cast hG5)
    have hqv := hqv_pp (d := d) (s := s) (t := t) (Kf := K) (N := N) hκ0 hκ1 (hEκ N) hs0N hstN
      ht1N (hK0 N) hε.le (D₀ := 20) (D₂ := 19) hAt1 hφ6 hsmall htail
    have h := ppHyp_real (d := d) (s := s) (t := t) (Kf := K) (N := N) hκ0 hκ1 (hEκ N) hs0N hstr
      ht1N (hK0 N) hBk0 hBk hε.le (D₀ := 20) (D₂ := 19) hφ6nn
    obtain ⟨G1, hG1prob, hbd⟩ := hNT1 (K N) (d.L N) hK1 hKle hL (time s t K N) τ (step s t K N)
      (App d (E N) s t K N 0) (Ast d (E N) s t K N τ) (Dpp d (E N) s t K N) (Zpp d (E N) s t K N)
      (Ypp d (E N) s t K N) (Rpp d (E N) s t K N Bk)
      (dPP d (E N) s t K N ε 20 ((band d).ell N (s N)))
      (fun _ _ j => cPPnn d κ (E N) s t K N ε 19 (phi6PP d ε s t N) j)
      (fun _ => vPP d κ (E N) s t K N)
      (fun _ => wPP d κ (E N) s t K N) (errPP d (E N) s t K N Bk) (PPP d κ (E N) t N) hΔ hKΔ hP0 hP
      (fun _ _ => vPP_le d κ (E N) s t K N) (fun _ _ => wPP_le d κ (E N) s t K N)
      (measurableSet_lt_tauPP' d (E N) ε 20 s t K N)
      (stronglyMeasurable_gridZC s t K N 2 (Φpp d (E N) s t K N)
        (gridΦG_testFun d (hE N) hstN ht1N (hK0 N) (by norm_num) sigmaPP)) hqv h
    refine ⟨G1 ∩ Good, ?_, Set.inter_subset_right, ?_⟩
    · rw [Set.compl_inter]
      calc (Pg d) (G1ᶜ ∪ Goodᶜ) ≤ (Pg d) G1ᶜ + (Pg d) Goodᶜ := measure_union_le _ _
        _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))
            + (ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))) :=
          add_le_add (measure_le_ofReal_of_real hG1prob) hGoodc
        _ = _ := by ring
        _ ≤ _ := hprob3
    · intro ω ⟨hω1, hω2⟩
      have hW20 : (d.W N : ℝ) ^ (-(20 : ℝ)) ≤ (N : ℝ) ^ (-(10 : ℝ)) := by
        have h := rpow_neg_W_le hN1 hWsqrt (by norm_num : (0 : ℝ) ≤ 20)
        rwa [show -((20 : ℝ) / 2) = -(10 : ℝ) by norm_num] at h
      have hW19 : (d.W N : ℝ) ^ (-(19 : ℝ)) ≤ (N : ℝ) ^ (-(9 : ℝ)) := by
        have h := rpow_neg_W_le hN1 hWsqrt (by norm_num : (0 : ℝ) ≤ 19)
        exact h.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
      obtain ⟨_hgoodall, hτK, hJ0⟩ := goodEvent_pp_imp d hω2
      have hτK' : τ ω = K N := hτK
      have hτpos : 0 < τ ω := by rw [hτK']; exact Nat.pos_of_ne_zero (hK0 N)
      have hbd' := hbd ω hω1 hτpos
      exact pp_closure_fixedN_plain (d := d) (s := s) (t := t) (Kf := K) (N := N) hκ0 (hE N) hs0N
        hstN ht1N (hK0 N) hε.le (by linarith) hBk0 hBk hN1 hWL hWN hηt hAt1 hreg0N hAcN hsum hlog
        hKΔ hΔN hΔ1
        (hX2_of (sq_nonneg _) hBk0 hN1 hW1 (by linarith) hWL hLN hW20 hG1)
        (hX4_of (sq_nonneg _) hN1 (by linarith) (by linarith) hWL (Real.rpow_nonneg hN0.le _)
          hNε hW20 hG2)
        (hqvtail_of (sq_nonneg _) hN1 (by linarith) (by linarith) hWL hW19 hG3)
        (hRt_of hBk0 hN1 hD₁.le hΔ0 hΔ hG6) (by rw [show c / 4 = c / 2 / 2 by ring]; exact hG9) τ ω
        hτK' hJ0 hbd'
  · -- the degenerate grid `s_N = t_N`
    have heq : s N = t N := le_antisymm hstN (not_lt.mp hstr)
    refine ⟨Good, ?_, le_rfl, ?_⟩
    · refine hGoodc.trans (le_trans ?_ hprob3)
      exact self_le_add_right _ _
    · intro ω hω k _
      obtain ⟨_, _, hJ0⟩ := goodEvent_pp_imp d hω
      obtain ⟨hH, htime⟩ := H_eq_zero_of_step (Kf := K) (d := d) heq k ω
      rw [hH, htime]
      exact hJ0c ω hJ0

/-! ### The bound on `JPP` at every time -/

/-- **`JPP_u ≺ 1 + R² + R^{5/2}` at every time sequence `u N ∈ [s N, t N]`.** It uses
`pp_grid_bound_plainN`, `ev_Lg_leN`, and `plain_endpointN`/`scale_endpointN`. -/
theorem pp_endpoint_seq_plainN (d : Dims) {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (u : ℕ → ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    StochDom (P d) (fun N (_ : Unit) ω => JPP d (E N) N (u N) (Hflow d N (u N) ω))
      (fun N _ _ => 1 + RPP d s t N ^ 2 + RPP d s t N ^ (5 / 2 : ℝ)) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hu1 : ∀ N, u N < 1 := fun N => (hut N).trans_lt (ht1 N)
  -- the hypotheses of `pp_grid_bound_plainN` for the pair `(s, u)`
  have hcond' : Cond272N (band d) E s u := by
    filter_upwards [hcond] with N hN
    have hAt0 : 0 < (band d).scale (E N) N (t N) :=
      (band d).scale_pos' (hE N) N ((hs0 N).trans (hst N)) (ht1 N)
    have hAut : (band d).scale (E N) N (t N) ≤ (band d).scale (E N) N (u N) :=
      scale_anti_pp (hut N) (ht1 N)
    have h1s : 0 < 1 - s N := by linarith [hst N, ht1 N]
    calc ((band d).scale (E N) N (u N))⁻¹ ≤ ((band d).scale (E N) N (t N))⁻¹ :=
          inv_anti₀ hAt0 hAut
      _ ≤ ((1 - t N) / (1 - s N)) ^ 30 := hN
      _ ≤ ((1 - u N) / (1 - s N)) ^ 30 := by
          have h0 : 0 ≤ (1 - t N) / (1 - s N) := div_nonneg (by linarith [ht1 N]) h1s.le
          exact pow_le_pow_left₀ h0 (div_le_div_of_nonneg_right (by linarith [hut N]) h1s.le) 30
  have hreg0' : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (u N)) ^ 30 ≤
      (band d).scale (E N) N (u N) :=
    plain_endpointN (band d) hE ht1 hreg0 (fun N => ⟨u N, hsu N, hut N⟩)
  have hAc' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (u N) :=
    scale_endpointN (band d) ht1 hAc (fun N => ⟨u N, hsu N, hut N⟩)
  intro τ' hτ' D hD
  set ε : ℝ := min (c / 8) (τ' / 8) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεc : ε ≤ c / 8 := min_le_left _ _
  have hετ : ε ≤ τ' / 8 := min_le_right _ _
  have hT3 := pp_grid_bound_plainN d hκ0 hκ1 hEκ hB hs0 hsu hu1 hcond' hc0 hreg0' hAc' hε hεc hD
  filter_upwards [hT3, ev_Lg_leN hκ0 hEκ (A := 2 * C0PP κ)
      (by unfold C0PP; positivity) (show 0 < 5 * τ' / 8 by linarith),
    eventually_ge_atTop 1] with N hN hLg hN1
  obtain ⟨G, hG, _, hbd⟩ := hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set K := KPP D with hKdef
  have hK0 : K N ≠ 0 := KPP_ne_zero D N
  -- `2c′_{(s,u)} ≤ N^{τ'} (1 + R² + R^{5/2})`
  have hRsu : RPP d s u N ≤ RPP d s t N := by
    unfold RPP
    have hℓs : 0 < (band d).ell N (s N) := lt_of_lt_of_le zero_lt_one
      (one_le_ellHat (d.L N) (d.three_le_L N) (hs0 N) ((hst N).trans_lt (ht1 N)))
    exact div_le_div_of_nonneg_right (RBM.Step3.ellHat_mono (hut N) (ht1 N)) hℓs.le
  have hRsu0 := RPP_nonneg d s u N
  have hP : 1 + RPP d s u N ^ 2 + RPP d s u N ^ (5 / 2 : ℝ)
      ≤ 1 + RPP d s t N ^ 2 + RPP d s t N ^ (5 / 2 : ℝ) := by
    have h2 := pow_le_pow_left₀ hRsu0 hRsu 2
    have h52 := Real.rpow_le_rpow hRsu0 hRsu (by norm_num : (0 : ℝ) ≤ 5 / 2)
    linarith
  have hc'le : 2 * cPrimePP d κ (E N) ε s u N
      ≤ (N : ℝ) ^ τ' * (1 + RPP d s t N ^ 2 + RPP d s t N ^ (5 / 2 : ℝ)) := by
    unfold cPrimePP
    have hn3 : ((N : ℝ) ^ ε) ^ 3 ≤ (N : ℝ) ^ (3 * τ' / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
    have hsplit : (N : ℝ) ^ τ' = (N : ℝ) ^ (3 * τ' / 8) * (N : ℝ) ^ (5 * τ' / 8) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hP0 : 0 ≤ 1 + RPP d s u N ^ 2 + RPP d s u N ^ (5 / 2 : ℝ) := by
      have := Real.rpow_nonneg hRsu0 (5 / 2 : ℝ); positivity
    have hC0 : 0 ≤ C0PP κ := by unfold C0PP; positivity
    have hLg0 : 0 ≤ LgPP (E N) N := by
      unfold LgPP
      have := mul_nonneg (inv_nonneg.2 (mE_im_pos (hE N)).le) (Real.log_nonneg hN1')
      linarith
    have hn30 : 0 ≤ ((N : ℝ) ^ ε) ^ 3 := by have := Real.rpow_nonneg hN0.le ε; positivity
    calc 2 * (C0PP κ * ((N : ℝ) ^ ε) ^ 3 * (1 + RPP d s u N ^ 2 + RPP d s u N ^ (5 / 2 : ℝ))
          * LgPP (E N) N)
        = ((N : ℝ) ^ ε) ^ 3 * (2 * C0PP κ * LgPP (E N) N)
          * (1 + RPP d s u N ^ 2 + RPP d s u N ^ (5 / 2 : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ (3 * τ' / 8) * (N : ℝ) ^ (5 * τ' / 8)
          * (1 + RPP d s t N ^ 2 + RPP d s t N ^ (5 / 2 : ℝ)) := by
          gcongr
      _ = _ := by rw [hsplit]
  -- the bad event is contained in the transferred complement of `G`
  have hSmeas : MeasurableSet {M : Matrix (d.Idx N) (d.Idx N) ℂ |
      2 * cPrimePP d κ (E N) ε s u N < JPP d (E N) N (u N) M} :=
    measurableSet_lt measurable_const (measurable_JPP d (E N) N (u N))
  have hsub : badSet (fun N (_ : Unit) ω => JPP d (E N) N (u N) (Hflow d N (u N) ω))
      (fun N _ _ => 1 + RPP d s t N ^ 2 + RPP d s t N ^ (5 / 2 : ℝ)) τ' N
      ⊆ (Hflow d N (u N)) ⁻¹' {M | 2 * cPrimePP d κ (E N) ε s u N < JPP d (E N) N (u N) M} := by
    rintro ω ⟨_, hω⟩
    exact lt_of_le_of_lt hc'le hω
  have htr : (P d) ((Hflow d N (u N)) ⁻¹'
      {M | 2 * cPrimePP d κ (E N) ε s u N < JPP d (E N) N (u N) M})
      = (Pg d) ((H d s u K N (K N)) ⁻¹'
        {M | 2 * cPrimePP d κ (E N) ε s u N < JPP d (E N) N (u N) M}) := by
    have hHmeas : Measurable (H d s u K N (K N)) :=
      (H_measurable_filt d s u K N (K N)).mono ((filt d).le (K N)) le_rfl
    have hHflowmeas : Measurable (Hflow d N (u N)) := RBM.measurable_H (sample d) N (u N)
    rw [← Measure.map_apply hHflowmeas hSmeas, ← Measure.map_apply hHmeas hSmeas,
      map_H_eq s u K N (K N) (hs0 N) (hsu N) hK0, time_last s u K N hK0]
  have hsub2 : (H d s u K N (K N)) ⁻¹' {M | 2 * cPrimePP d κ (E N) ε s u N < JPP d (E N) N (u N) M}
      ⊆ Gᶜ := by
    intro ω hω hωG
    have h := hbd ω hωG (K N) le_rfl
    rw [time_last s u K N hK0] at h
    exact absurd h (not_le.mpr hω)
  calc (P d) (badSet _ _ τ' N) ≤ (P d) ((Hflow d N (u N)) ⁻¹'
        {M | 2 * cPrimePP d κ (E N) ε s u N < JPP d (E N) N (u N) M}) := measure_mono hsub
    _ = _ := htr
    _ ≤ (Pg d) Gᶜ := measure_mono hsub2
    _ ≤ _ := hG

section CompatN

end CompatN

end RBM.Gauss.Grid

end


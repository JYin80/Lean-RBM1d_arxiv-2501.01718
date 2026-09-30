/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridDuhamelTail
import RBM1D.Gauss.GridStopFilt
import RBM1D.Gauss.GridNetLift
import RBM1D.Gauss.GridGoodEvent
import RBM1D.Gauss.GridBootstrap
import RBM1D.Gauss.GridStepDecompC

/-!
# The fixed-endpoint grid assembly: the probability budget and the linear increment

The discrete Duhamel expansion of `GridDuhamelTail.lean` is assembled, with a kernel bound, a
drift bound, a paired conditional sub-Gaussian bound on the linear increment, a second-moment
bound on the second-order increment and a deterministic remainder bound, into a single "for all
grid targets `k ≤ K` simultaneously" high-probability norm bound.  This file supplies the
probability budget of that assembly and the linear increment in the `vC` form.

## Main declarations

* `assembly_prob_budget` : the probability budget (satisfiability).
* `gridZC`, `hqv_of_vC` : the exactly-linear grid increment `stepZC` as a label vector, and the
  passage from the `vC(AbC …)` form of h-qv to a paired conditional sub-Gaussian bound.
* `gridΦG`, `gridΦG_testFun` : the general-`σ` label family at the grid times, and its
  `TestFun` property at every grid time `u_i < 1`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Finset MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal

/-! ### A fixed-target Chebyshev tail (needed alongside the mandatory fixed-target Azuma tail) -/

section ChebFixed

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

end ChebFixed

/-! ### The hypothesis bundle and the single-scale core -/

section Assembly

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-! ### The probability budget (the satisfiability check) -/

/-- **The Azuma budget**: for every `n`, every `ε > 0`, every `D₁`, every `C_K ≥ 0` and every
`C_L`, eventually in `N`: `N ≥ 2` and, uniformly over `K ≤ ⌈N^{C_K}⌉₊` and `L ≤ N^{C_L}`,
`4 K L^n exp(-(N^ε)²/4) ≤ N^{-D₁}/2`. -/
theorem assembly_prob_budget (n : ℕ) {ε : ℝ} (hε : 0 < ε) (D₁ C_K C_L : ℝ) (hCK : 0 ≤ C_K) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ N ∧ ∀ K L : ℕ, K ≤ ⌈(N : ℝ) ^ C_K⌉₊ →
      (L : ℝ) ≤ (N : ℝ) ^ C_L →
        4 * (K : ℝ) * (L : ℝ) ^ n * Real.exp (-((N : ℝ) ^ ε) ^ 2 / 4) ≤ (N : ℝ) ^ (-D₁) / 2 := by
  filter_upwards [SumZeroDyn.eventually_exp_small 16 (C_K + n * C_L + D₁) (1 / 4) (by norm_num)
    (by linarith : (0 : ℝ) < 2 * ε), eventually_ge_atTop 2] with N hexp hN2
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨hN2', fun K L hK hL => ?_⟩
  have hNCK : 1 ≤ (N : ℝ) ^ C_K := Real.one_le_rpow (by linarith) hCK
  have hK' : (K : ℝ) ≤ 2 * (N : ℝ) ^ C_K := by
    have h1 : (K : ℝ) ≤ (⌈(N : ℝ) ^ C_K⌉₊ : ℝ) := by exact_mod_cast hK
    have h2 : (⌈(N : ℝ) ^ C_K⌉₊ : ℝ) < (N : ℝ) ^ C_K + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hL' : (L : ℝ) ^ n ≤ (N : ℝ) ^ ((n : ℝ) * C_L) := by
    rw [mul_comm, Real.rpow_mul hN0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Nat.cast_nonneg L) hL n
  have hsq : ((N : ℝ) ^ ε) ^ 2 = (N : ℝ) ^ (2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    ring_nf
  rw [hsq]
  set ex : ℝ := Real.exp (-(N : ℝ) ^ (2 * ε) / 4) with hexdef
  have hex_eq : Real.exp (-(1 / 4 * (N : ℝ) ^ (2 * ε))) = ex := by
    rw [hexdef]; congr 1; ring
  rw [hex_eq] at hexp
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  have hsplit : (N : ℝ) ^ (C_K + (n : ℝ) * C_L + D₁)
      = (N : ℝ) ^ C_K * (N : ℝ) ^ ((n : ℝ) * C_L) * (N : ℝ) ^ D₁ := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hD : (N : ℝ) ^ D₁ * (N : ℝ) ^ (-D₁) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  have hr : 0 < (N : ℝ) ^ (-D₁) := Real.rpow_pos_of_pos hN0 _
  rw [hsplit] at hexp
  have hmul := mul_le_mul_of_nonneg_right hexp hr.le
  have e1 : 16 * ((N : ℝ) ^ C_K * (N : ℝ) ^ ((n : ℝ) * C_L) * (N : ℝ) ^ D₁) * ex
        * (N : ℝ) ^ (-D₁)
      = 16 * ((N : ℝ) ^ C_K * (N : ℝ) ^ ((n : ℝ) * C_L) * ex)
        * ((N : ℝ) ^ D₁ * (N : ℝ) ^ (-D₁)) := by ring
  rw [e1, hD, mul_one, one_mul] at hmul
  have hKL : 4 * (K : ℝ) * (L : ℝ) ^ n * ex
      ≤ 4 * (2 * (N : ℝ) ^ C_K) * (N : ℝ) ^ ((n : ℝ) * C_L) * ex := by
    gcongr
  linarith

end Assembly

/-! ### The quadratic-variation hypothesis h-qv in the `vC` form -/

section VC

variable {d : Dims}

/-- **`gridZC`**: the exactly-linear grid increment as a label vector, cut to the grid range:
for `1 ≤ i ≤ K N`, `gridZC i ω a = stepZC d s t K N (i-1) n (Φ i) δ a ω` (the first-order term of
the step from `H_{i-1}` to `H_i`, with the label family `Φ i = Φ_{u_i}` differentiated at
`H_{i-1}`); `0` otherwise. -/
def gridZC (d : Dims) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N n : ℕ)
    (Φ : ℕ → LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (i : ℕ) (ω : Ωg d) :
    LoopArg (d.L N) n → ℂ :=
  fun a => if 1 ≤ i ∧ i ≤ Kf N then
    stepZC d s t Kf N (i - 1) n (Φ i) (gridDeltaC (d.L N) n) a ω else 0

theorem gridZC_succ (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N n : ℕ)
    (Φ : ℕ → LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) {j : ℕ} (hj : j < Kf N)
    (ω : Ωg d) :
    gridZC d s t Kf N n Φ (j + 1) ω
      = fun a => stepZC d s t Kf N j n (Φ (j + 1)) (gridDeltaC (d.L N) n) a ω := by
  funext a
  unfold gridZC
  have hc : 1 ≤ j + 1 ∧ j + 1 ≤ Kf N := ⟨by omega, by omega⟩
  simp only [hc, and_self, ↓reduceIte, Nat.add_sub_cancel]

/-- `stepZC` at step `j` is `filt d (j+1)`-measurable (general loop length `n`, complex `U`). -/
theorem measurable_stepZC_filt (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Measurable[filt d (j + 1)] (fun ω => stepZC d s t Kf N j n Φ U b ω) := by
  have hA : Measurable[filt d (j + 1)] (fun ω => AbC d s t Kf N j n Φ U b ω) :=
    (measurable_AbC d s t Kf N j n hΦ U b).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have hAI : Measurable[filt d (j + 1)]
      (fun ω => (-Complex.I) • AbC d s t Kf N j n Φ U b ω) :=
    ((measurable_AbC d s t Kf N j n hΦ U b).const_smul (-Complex.I)).mono
      ((filt d).mono (Nat.le_succ j)) le_rfl
  have hX : Measurable[filt d (j + 1)] (fun ω : Ωg d => Xmat d N (ω (j + 1))) :=
    (measurable_Xmat d N).comp (measurable_coord_filt le_rfl)
  have hre : Measurable[filt d (j + 1)] (fun ω => stepZC_re d s t Kf N j n Φ U b ω) := by
    have hL := (measurable_lin (d := d) N).comp (hA.prodMk hX)
    change Measurable[filt d (j + 1)] (fun ω : Ωg d => Real.sqrt (step s t Kf N) *
      lin N (AbC d s t Kf N j n Φ U b ω) (Xmat d N (ω (j + 1))))
    exact hL.const_mul _
  have him : Measurable[filt d (j + 1)] (fun ω => stepZC_im d s t Kf N j n Φ U b ω) := by
    have hL := (measurable_lin (d := d) N).comp (hAI.prodMk hX)
    change Measurable[filt d (j + 1)] (fun ω : Ωg d => Real.sqrt (step s t Kf N) *
      lin N ((-Complex.I) • AbC d s t Kf N j n Φ U b ω) (Xmat d N (ω (j + 1))))
    exact hL.const_mul _
  change Measurable[filt d (j + 1)] (fun ω => (stepZC_re d s t Kf N j n Φ U b ω : ℂ)
    + Complex.I * (stepZC_im d s t Kf N j n Φ U b ω : ℂ))
  exact (Complex.measurable_ofReal.comp hre).add
    (measurable_const.mul (Complex.measurable_ofReal.comp him))

/-- `gridZC i` is `filt d i`-strongly measurable (the `hZmeas` of
`RBM.Gauss.Grid.grid_assembly_stopped_core_pw`). -/
theorem stronglyMeasurable_gridZC (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N n : ℕ)
    (Φ : ℕ → LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (hΦ : ∀ i, 1 ≤ i → i ≤ Kf N → ∀ a, TestFun d N (Φ i a)) (i : ℕ) :
    StronglyMeasurable[filt d i] (gridZC d s t Kf N n Φ i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ Kf N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hfun : gridZC d s t Kf N n Φ (j + 1)
        = fun ω a => stepZC d s t Kf N j n (Φ (j + 1)) (gridDeltaC (d.L N) n) a ω := by
      funext ω
      exact gridZC_succ s t Kf N n Φ (by omega) ω
    rw [hfun]
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact measurable_stepZC_filt s t Kf N j n (hΦ (j + 1) hi.1 hi.2) _ a
  · have : gridZC d s t Kf N n Φ i = fun _ _ => 0 := by
      funext ω a
      unfold gridZC
      simp only [hi, ↓reduceIte]
    rw [this]
    exact stronglyMeasurable_const

/-- **The `vC` form of h-qv implies the paired conditional sub-Gaussian bound on the linear
increment**: a bound `Δ·vC(Σ_b U_{j+1,k}(a,b)·gradMat(Φ_{u_{j+1},b})(H_j)) ≤ c k a j`
on `{j < τ}`, i.e. `step·vC N (AbC … (Φ (j+1)) (ukerMatC ξ u_{j+1} u_k) a ω) ≤ c k a j`, gives the
paired `HasCondSubgaussianMGF` of the real and imaginary parts of the stopped, kernel-transported
increment `(U_{j+1,k} gridZC_{j+1})(a)`. Route: `stepZC_ukerMatC_eq_Uker` and
`stepDecompC_ZC_subG_vC` (which uses `v_le_vC`, `v_neg_I_le_vC`). -/
theorem hqv_of_vC (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N n : ℕ) (ξ : Fin n → ℂ) (τ : Ωg d → ℕ)
    (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    (Φ : ℕ → LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (hΦ : ∀ i, 1 ≤ i → i ≤ Kf N → ∀ a, TestFun d N (Φ i a)) (hΔ : 0 ≤ step s t Kf N)
    (c : ℕ → LoopArg (d.L N) n → ℕ → ℝ≥0)
    (hqvC : ∀ k ≤ Kf N, ∀ (a : LoopArg (d.L N) n) (j : ℕ), j < k → ∀ ω, j < τ ω →
      step s t Kf N * vC N (AbC d s t Kf N j n (Φ (j + 1))
        (ukerMatC ξ (time s t Kf N (j + 1)) (time s t Kf N k)) a ω) ≤ c k a j) :
    ∀ k ≤ Kf N, ∀ (a : LoopArg (d.L N) n) (j : ℕ), j < k →
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker (d.L N) ξ (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
            (gridZC d s t Kf N n Φ (j + 1) ω') a) ω).re) (c k a j) (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker (d.L N) ξ (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
            (gridZC d s t Kf N n Φ (j + 1) ω') a) ω).im) (c k a j) (Pg d) := by
  intro k hk a j hj
  have hjK : j < Kf N := lt_of_lt_of_le hj hk
  obtain ⟨h1, h2⟩ := stepDecompC_ZC_subG_vC d s t Kf N j n (hΦ (j + 1) (by omega) (by omega))
    (ukerMatC ξ (time s t Kf N (j + 1)) (time s t Kf N k)) a {ω | j < τ ω} (hτmeas j)
    (c k a j) (c k a j).2 hΔ (fun ω hω => hqvC k hk a j hj ω hω)
  have hU : ∀ ω', Uker (d.L N) ξ (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
      (gridZC d s t Kf N n Φ (j + 1) ω') a
      = stepZC d s t Kf N j n (Φ (j + 1))
          (ukerMatC ξ (time s t Kf N (j + 1)) (time s t Kf N k)) a ω' := by
    intro ω'
    rw [gridZC_succ s t Kf N n Φ hjK ω', stepZC_ukerMatC_eq_Uker]
  have heqRe : (fun ω => ({ω' | j < τ ω'}.indicator
      (fun ω' => Uker (d.L N) ξ (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
        (gridZC d s t Kf N n Φ (j + 1) ω') a) ω).re)
      = fun ω => {ω | j < τ ω}.indicator (fun ω => stepZC_re d s t Kf N j n (Φ (j + 1))
          (ukerMatC ξ (time s t Kf N (j + 1)) (time s t Kf N k)) a ω) ω := by
    funext ω
    by_cases hω : j < τ ω
    · have hm : ω ∈ {ω' | j < τ ω'} := hω
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, hU]
      simp [stepZC]
    · have hm : ω ∉ {ω' | j < τ ω'} := hω
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, Complex.zero_re]
  have heqIm : (fun ω => ({ω' | j < τ ω'}.indicator
      (fun ω' => Uker (d.L N) ξ (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
        (gridZC d s t Kf N n Φ (j + 1) ω') a) ω).im)
      = fun ω => {ω | j < τ ω}.indicator (fun ω => stepZC_im d s t Kf N j n (Φ (j + 1))
          (ukerMatC ξ (time s t Kf N (j + 1)) (time s t Kf N k)) a ω) ω := by
    funext ω
    by_cases hω : j < τ ω
    · have hm : ω ∈ {ω' | j < τ ω'} := hω
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, hU]
      simp [stepZC]
    · have hm : ω ∉ {ω' | j < τ ω'} := hω
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, Complex.zero_im]
  rw [heqRe, heqIm]
  exact ⟨h1, h2⟩

end VC

/-! ### (T3): the "trivial log N" grid time-sum -/

section LogSum

variable (d : Dims)

end LogSum

/-! ### (T4): instantiation with the real grid objects, and a satisfiability witness -/

section T4Examples

/-- The general-σ label family at the grid times: `Φ_i = ΦgridG (band d) E N u_i σ`. -/
def gridΦG (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) {n : ℕ} (σ : Fin n → Bool)
    (i : ℕ) (a : LoopArg (d.L N) n) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ΦgridG (band d) E N (time s t Kf N i) σ a M

/-- `Φ_i` is a `TestFun` at every grid time `u_i`, `i ≤ K N` (since `u_i ≤ t < 1`). -/
theorem gridΦG_testFun (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {Kf : ℕ → ℕ} {N : ℕ}
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (σ : Fin n → Bool) :
    ∀ i, 1 ≤ i → i ≤ Kf N → ∀ a, TestFun d N (gridΦG d E s t Kf N σ i a) := by
  intro i _ hi a
  have hu1 : time s t Kf N i < 1 := by
    have h := time_mono_of_le (K := Kf) hst hi
    rw [time_last s t Kf N hK0] at h
    exact h.trans_lt ht1
  exact ΦgridG_testFun (band d) hE N hu1 hn σ a

/-! #### The satisfiability witness -/

end T4Examples

end RBM.Gauss.Grid

end


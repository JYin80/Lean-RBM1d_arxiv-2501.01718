/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridAssembly
import RBM1D.Gauss.Q716Pointwise

/-!
# The fixed generic grid assembly interface

Theorems next to `GridAssembly.lean`.  Paper: Lemma 5.14, (5.91)–(5.105), with (7.16)
(Lemma 7.3) as the kernel input.

## The restricted kernel

A kernel hypothesis `‖U_{i,k}X‖ ≤ κ_{i,k}‖X‖` for **all** `X` is not available: the sharp (7.16)
bound holds only on fast-decaying (Case 2: also sum-zero) inputs and carries an additive
`ε_{i,k}δ`. Here `hker` is stated on `KerClass` only, the kernel is applied with the sharp weight
only to `A0` (on `{0 < τ}`) and to the drift (on `{j < τ}`), and the remainder `R` uses the coarse
row-sum weight `(1+(1-u_k)⁻¹)^n`, which is **derived** (`norm_Uker_coarse`), not assumed.

## The Y tail

The Chebyshev Y tail `(K+1)L^nΣe_j/x²` does not shrink with `K`. Here the propagated
second-order increments are controlled by a fourth moment (`p = 2` Burkholder, elementary:
`mart_moment4`), `E|Σ U Y|⁴ ≤ 44(ΔP)²`, and the union over the `K+1` targets costs
`88 L^n P² Δ / x⁴`, paid by `Δ ≤ N^{-C_K}`.

## Main declarations

* `mart_moment4`, `stopped_duhamel_moment4`, `stopped_duhamel_moment4_union`,
  `moment4_budget_le`, `Ytail_budget`.
* `KerClass`, `GridAssemblyHypPW` (pathwise drift), `norm_Uker_coarse`,
  `grid_assembly_stopped_core_pw`.
* `grid_assembly_stopped_pathwise`, `grid_assembly_at_tau'`.
* Producers of the kernel hypothesis: `hker_of_Q716_nonAlt`, `hker_of_Q716_sumZero` (from
  `Q716.uker_decay_le_nonAlt` / `Q716.uker_decay_le_sumZero`).
-/

noncomputable section

namespace RBM.Gauss.Grid

open Finset MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal

/-! ### The fourth-moment bound for real martingale differences (the `p = 2` Burkholder bound) -/

section Moment4

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

private lemma abs_le_B1 (a b : ℝ) : |a| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2),
      sq_nonneg (b ^ 2)]

private lemma abs_mul_le_B (a b : ℝ) : |a * b| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - 1 / 2),
      sq_nonneg (b ^ 2 - 1 / 2), sq_nonneg (a ^ 2 - b ^ 2)]

private lemma abs_sq_le_B (a b : ℝ) : |a ^ 2| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_of_nonneg (sq_nonneg a)]
  nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (b ^ 2)]

private lemma abs_cube_mul_le_B (a b : ℝ) : |a ^ 3 * b| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  have h1 : |a ^ 3 * b| = a ^ 2 * |a * b| := by
    rw [show a ^ 3 * b = a ^ 2 * (a * b) by ring, abs_mul, abs_of_nonneg (sq_nonneg a)]
  have h2 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  rw [h1]
  have h3 : a ^ 2 * |a * b| ≤ a ^ 2 * ((a ^ 2 + b ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg a, sq_nonneg b]

private lemma abs_sq_mul_sq_le_B (a b : ℝ) : |a ^ 2 * b ^ 2| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

private lemma pow4_add_le (a b : ℝ) :
    (a + b) ^ 4 ≤ a ^ 4 + 4 * (a ^ 3 * b) + 8 * (a ^ 2 * b ^ 2) + 3 * b ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (a - b))]

private lemma pow4_add_le_eight (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b)), sq_nonneg (a * b),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - b))]

/-- One step of the fourth-moment recursion: for an `ℱ m`-measurable `S` and a martingale
difference `d` with `E[d | ℱ m] = 0`, `E[d² | ℱ m] ≤ v`:
`E(S+d)² ≤ E S² + v` and `E(S+d)⁴ ≤ E S⁴ + 8 v E S² + 3 E d⁴`. -/
private lemma moment4_step (m : ℕ) {S d : Ω' → ℝ} (hS : StronglyMeasurable[ℱ m] S)
    (hd : StronglyMeasurable d) (hS4 : Integrable (fun ω => S ω ^ 4) μ)
    (hd4 : Integrable (fun ω => d ω ^ 4) μ) (hmean : μ[d | ℱ m] =ᵐ[μ] 0) {v : ℝ}
    (hcond : μ[fun ω => d ω ^ 2 | ℱ m] ≤ᵐ[μ] fun _ => v) :
    Integrable (fun ω => (S ω + d ω) ^ 4) μ
      ∧ ∫ ω, (S ω + d ω) ^ 2 ∂μ ≤ ∫ ω, S ω ^ 2 ∂μ + v
      ∧ ∫ ω, (S ω + d ω) ^ 4 ∂μ
          ≤ ∫ ω, S ω ^ 4 ∂μ + 8 * v * ∫ ω, S ω ^ 2 ∂μ + 3 * ∫ ω, d ω ^ 4 ∂μ := by
  have hS0 : StronglyMeasurable S := hS.mono (ℱ.le m)
  set B : Ω' → ℝ := fun ω => 1 + 2 * (S ω ^ 4 + d ω ^ 4) with hBdef
  have hB : Integrable B μ := (integrable_const 1).add ((hS4.add hd4).const_mul 2)
  have hint : ∀ f : Ω' → ℝ, StronglyMeasurable f → (∀ ω, |f ω| ≤ B ω) → Integrable f μ :=
    fun f hf hfB => hB.mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB ω)
  have hid : Integrable d μ := hint d hd fun ω => by
    have := abs_le_B1 (d ω) (S ω); simp only [hBdef]; linarith
  have hid2 : Integrable (fun ω => d ω ^ 2) μ :=
    hint _ (hd.pow 2) fun ω => by
      have := abs_sq_le_B (d ω) (S ω); simp only [hBdef]; linarith
  have hiS2 : Integrable (fun ω => S ω ^ 2) μ :=
    hint _ (hS0.pow 2) fun ω => abs_sq_le_B (S ω) (d ω)
  have hiSd : Integrable (fun ω => S ω * d ω) μ :=
    hint _ (hS0.mul hd) fun ω => abs_mul_le_B (S ω) (d ω)
  have hiS3d : Integrable (fun ω => S ω ^ 3 * d ω) μ :=
    hint _ ((hS0.pow 3).mul hd) fun ω => abs_cube_mul_le_B (S ω) (d ω)
  have hiS2d2 : Integrable (fun ω => S ω ^ 2 * d ω ^ 2) μ :=
    hint _ ((hS0.pow 2).mul (hd.pow 2)) fun ω => abs_sq_mul_sq_le_B (S ω) (d ω)
  have hiSum4 : Integrable (fun ω => (S ω + d ω) ^ 4) μ := by
    refine ((hS4.add hd4).const_mul 8).mono' ((hS0.add hd).pow 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow4_add_le_eight (S ω) (d ω)
  -- `E[S^p d] = 0` for an `ℱ m`-measurable `S^p`
  have hzero : ∀ p : ℕ, Integrable (fun ω => S ω ^ p * d ω) μ →
      ∫ ω, S ω ^ p * d ω ∂μ = 0 := by
    intro p hp
    have h1 : μ[(fun ω => S ω ^ p) * d | ℱ m] =ᵐ[μ] (fun ω => S ω ^ p) * μ[d | ℱ m] :=
      condExp_mul_of_stronglyMeasurable_left (hS.pow p) hp hid
    calc ∫ ω, S ω ^ p * d ω ∂μ = ∫ ω, (μ[(fun ω => S ω ^ p) * d | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, ((fun ω => S ω ^ p) * μ[d | ℱ m]) ω ∂μ := integral_congr_ae h1
      _ = ∫ _ω, (0 : ℝ) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hmean] with ω hω
          simp [hω]
      _ = 0 := integral_zero _ _
  have hSd0 : ∫ ω, S ω * d ω ∂μ = 0 := by
    have := hzero 1 (by simpa using hiSd)
    simpa using this
  have hS3d0 : ∫ ω, S ω ^ 3 * d ω ∂μ = 0 := hzero 3 hiS3d
  -- `E[d²] ≤ v`
  have hd2v : ∫ ω, d ω ^ 2 ∂μ ≤ v := by
    calc ∫ ω, d ω ^ 2 ∂μ = ∫ ω, (μ[fun ω => d ω ^ 2 | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ ≤ ∫ _ω, v ∂μ := integral_mono_ae integrable_condExp (integrable_const v) hcond
      _ = v := by simp
  -- `E[S² d²] ≤ v E[S²]`
  have hS2d2 : ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ ≤ v * ∫ ω, S ω ^ 2 ∂μ := by
    have h1 : μ[(fun ω => S ω ^ 2) * (fun ω => d ω ^ 2) | ℱ m]
        =ᵐ[μ] (fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m] :=
      condExp_mul_of_stronglyMeasurable_left (hS.pow 2) hiS2d2 hid2
    have hi1 : Integrable ((fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m]) μ :=
      (integrable_condExp (μ := μ) (m := ℱ m)
        (f := (fun ω => S ω ^ 2) * (fun ω => d ω ^ 2))).congr h1
    calc ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ
        = ∫ ω, (μ[(fun ω => S ω ^ 2) * (fun ω => d ω ^ 2) | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, ((fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m]) ω ∂μ := integral_congr_ae h1
      _ ≤ ∫ ω, v * S ω ^ 2 ∂μ := by
          refine integral_mono_ae hi1 (hiS2.const_mul v) ?_
          filter_upwards [hcond] with ω hω
          simp only [Pi.mul_apply]
          nlinarith [sq_nonneg (S ω)]
      _ = v * ∫ ω, S ω ^ 2 ∂μ := integral_const_mul v _
  refine ⟨hiSum4, ?_, ?_⟩
  · have heq : (fun ω => (S ω + d ω) ^ 2)
        = fun ω => S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2 := by funext ω; ring
    rw [heq, integral_add (f := fun ω => S ω ^ 2 + 2 * (S ω * d ω))
        (hiS2.add (hiSd.const_mul 2)) hid2,
      integral_add (f := fun ω => S ω ^ 2) hiS2 (hiSd.const_mul 2), integral_const_mul, hSd0]
    linarith
  · calc ∫ ω, (S ω + d ω) ^ 4 ∂μ
        ≤ ∫ ω, (S ω ^ 4 + 4 * (S ω ^ 3 * d ω) + 8 * (S ω ^ 2 * d ω ^ 2) + 3 * d ω ^ 4) ∂μ :=
          integral_mono hiSum4
            (((hS4.add (hiS3d.const_mul 4)).add (hiS2d2.const_mul 8)).add (hd4.const_mul 3))
            fun ω => pow4_add_le (S ω) (d ω)
      _ = ∫ ω, S ω ^ 4 ∂μ + 4 * ∫ ω, S ω ^ 3 * d ω ∂μ + 8 * ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ
            + 3 * ∫ ω, d ω ^ 4 ∂μ := by
          rw [integral_add
              (f := fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * d ω) + 8 * (S ω ^ 2 * d ω ^ 2))
              ((hS4.add (hiS3d.const_mul 4)).add (hiS2d2.const_mul 8)) (hd4.const_mul 3),
            integral_add (f := fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * d ω))
              (hS4.add (hiS3d.const_mul 4)) (hiS2d2.const_mul 8),
            integral_add (f := fun ω => S ω ^ 4) hS4 (hiS3d.const_mul 4), integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by rw [hS3d0]; nlinarith [hS2d2]

/-- **The `p = 2` Burkholder bound for real martingale differences** (elementary). For
`d_j` `ℱ (j+1)`-measurable with `E[d_j | ℱ j] = 0`, `d_j⁴` integrable, `E[d_j² | ℱ j] ≤ v_j` a.s.
(`v_j ≥ 0`) and `E d_j⁴ ≤ w_j`, the partial sum `S_m = Σ_{j<m} d_j` satisfies
`E S_m² ≤ Σ_{j<m} v_j` and `E S_m⁴ ≤ 8 (Σ_{j<m} v_j)² + 3 Σ_{j<m} w_j`. -/
theorem mart_moment4 (d : ℕ → Ω' → ℝ) (v w : ℕ → ℝ) (m : ℕ)
    (hd : ∀ j, StronglyMeasurable[ℱ (j + 1)] (d j))
    (hmean : ∀ j < m, μ[d j | ℱ j] =ᵐ[μ] 0)
    (hint : ∀ j < m, Integrable (fun ω => d j ω ^ 4) μ)
    (hcond : ∀ j < m, μ[fun ω => d j ω ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (hv0 : ∀ j < m, 0 ≤ v j)
    (hw : ∀ j < m, ∫ ω, d j ω ^ 4 ∂μ ≤ w j) :
    Integrable (fun ω => (∑ j ∈ range m, d j ω) ^ 4) μ
      ∧ ∫ ω, (∑ j ∈ range m, d j ω) ^ 2 ∂μ ≤ ∑ j ∈ range m, v j
      ∧ ∫ ω, (∑ j ∈ range m, d j ω) ^ 4 ∂μ
          ≤ 8 * (∑ j ∈ range m, v j) ^ 2 + 3 * ∑ j ∈ range m, w j := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hI, h2, h4⟩ := ih (fun j hj => hmean j (by omega)) (fun j hj => hint j (by omega))
      (fun j hj => hcond j (by omega)) (fun j hj => hv0 j (by omega)) (fun j hj => hw j (by omega))
    have hSm : StronglyMeasurable[ℱ m] (fun ω => ∑ j ∈ range m, d j ω) := by
      refine Finset.stronglyMeasurable_fun_sum (range m) (fun j hj => (hd j).mono (ℱ.mono ?_))
      have := Finset.mem_range.mp hj; omega
    have hdm : StronglyMeasurable (d m) := (hd m).mono (ℱ.le (m + 1))
    obtain ⟨hI', h2', h4'⟩ := moment4_step (μ := μ) m hSm hdm hI (hint m (by omega))
      (hmean m (by omega)) (hcond m (by omega))
    have hsum : ∀ ω, ∑ j ∈ range (m + 1), d j ω = (∑ j ∈ range m, d j ω) + d m ω := fun ω =>
      Finset.sum_range_succ _ _
    simp only [hsum]
    have hV0 : 0 ≤ ∑ j ∈ range m, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hvm := hv0 m (by omega)
    have hwm := hw m (by omega)
    have hS2nn : 0 ≤ ∫ ω, (∑ j ∈ range m, d j ω) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    refine ⟨hI', ?_, ?_⟩
    · rw [Finset.sum_range_succ]; linarith
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h8 : 8 * v m * ∫ ω, (∑ j ∈ range m, d j ω) ^ 2 ∂μ
          ≤ 8 * v m * ∑ j ∈ range m, v j :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [mul_nonneg hvm hV0, sq_nonneg (v m)]

end Moment4

/-! ### The fourth-moment Y tail for the propagated, stopped second-order increments -/

section YMoment

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

private lemma card_loopArg_eq_pow (L n : ℕ) [NeZero L] : Fintype.card (LoopArg L n) = L ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma stronglyMeasurable_Uker_apply_of_adapted {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ)
    (s t : ℂ) {i : ℕ} {W : Ω' → LoopArg L n → ℂ} (hW : StronglyMeasurable[ℱ i] W)
    (b : LoopArg L n) :
    StronglyMeasurable[ℱ i] (fun ω => Uker L ξ s t (W ω) b) := by
  have hcont : Continuous (fun A : LoopArg L n → ℂ => Uker L ξ s t A b) := by
    have heq : (fun A : LoopArg L n → ℂ => Uker L ξ s t A b)
        = fun A => ∑ c : LoopArg L n, (∏ p, edgeKer L (ξ p) s t (b p) (c p)) * A c := by
      funext A; exact Uker_apply L ξ s t A b
    rw [heq]
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `stoppedEdge … b j` is `ℱ (j+1)`-strongly measurable. -/
theorem stronglyMeasurable_stoppedEdge_succ {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → LoopArg L n → ℂ}
    (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i)) (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    (b : LoopArg L n) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (stoppedEdge L ξ u t' τ Z b j) := by
  have hset : MeasurableSet[ℱ (j + 1)] {ω | j < τ ω} := (ℱ.mono (Nat.le_succ j)) _ (hτmeas j)
  exact (stronglyMeasurable_Uker_apply_of_adapted L ξ _ _ (hZ (j + 1)) b).indicator hset

private lemma norm_pow4_le_re_im (z : ℂ) : ‖z‖ ^ 4 ≤ 2 * (z.re ^ 4 + z.im ^ 4) := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  have h4 : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by rw [← h]; ring
  rw [h4]
  nlinarith [sq_nonneg (z.re ^ 2 - z.im ^ 2)]

/-- **The per-target fourth moment of the propagated, stopped Y sum** (`p = 2` in
`E|Σ_{j<k} U_{j+1,k} Y_{j+1}|^{2p} ≤ C_p (ΔP)^p`): with, for both real and imaginary parts of
the stopped edge `stoppedEdge … b j`, conditional mean zero, integrable fourth power, conditional
second moment `≤ v_j` and fourth moment `≤ w_j`,
`E‖(Σ_{j<k∧τ} U_{j+1,t'} Y_{j+1})_b‖⁴ ≤ 4 (8 (Σ_{j<k} v_j)² + 3 Σ_{j<k} w_j)`; the fourth power
is integrable. -/
theorem stopped_duhamel_moment4 (L : ℕ) [NeZero L] {n : ℕ} {ξ : Fin n → ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Y : ℕ → Ω' → LoopArg L n → ℂ} (hY : ∀ i, StronglyMeasurable[ℱ i] (Y i))
    (k : ℕ) (t' : ℝ) (b : LoopArg L n) {v w : ℕ → ℝ}
    (hmeanRe : ∀ j < k, μ[fun ω => (stoppedEdge L ξ u t' τ Y b j ω).re | ℱ j] =ᵐ[μ] 0)
    (hmeanIm : ∀ j < k, μ[fun ω => (stoppedEdge L ξ u t' τ Y b j ω).im | ℱ j] =ᵐ[μ] 0)
    (hintRe : ∀ j < k, Integrable (fun ω => (stoppedEdge L ξ u t' τ Y b j ω).re ^ 4) μ)
    (hintIm : ∀ j < k, Integrable (fun ω => (stoppedEdge L ξ u t' τ Y b j ω).im ^ 4) μ)
    (hcondRe : ∀ j < k,
      μ[fun ω => (stoppedEdge L ξ u t' τ Y b j ω).re ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (hcondIm : ∀ j < k,
      μ[fun ω => (stoppedEdge L ξ u t' τ Y b j ω).im ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (hv0 : ∀ j < k, 0 ≤ v j)
    (h4Re : ∀ j < k, ∫ ω, (stoppedEdge L ξ u t' τ Y b j ω).re ^ 4 ∂μ ≤ w j)
    (h4Im : ∀ j < k, ∫ ω, (stoppedEdge L ξ u t' τ Y b j ω).im ^ 4 ∂μ ≤ w j) :
    Integrable (fun ω => ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4) μ
      ∧ ∫ ω, ‖(∑ j ∈ range (min k (τ ω)),
          Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4 ∂μ
        ≤ 4 * (8 * (∑ j ∈ range k, v j) ^ 2 + 3 * ∑ j ∈ range k, w j) := by
  set W : ℕ → Ω' → ℂ := stoppedEdge L ξ u t' τ Y b with hWdef
  have hsum : ∀ ω, (∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b = ∑ j ∈ range k, W j ω := by
    intro ω
    rw [Finset.sum_apply]
    exact sum_stopped (fun j' ω' => Uker L ξ (u j' : ℂ) (t' : ℂ) (Y j' ω') b) τ k ω
  have hWm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (W j) := fun j =>
    stronglyMeasurable_stoppedEdge_succ L ξ u t' hY hτmeas b j
  have hre := mart_moment4 (μ := μ) (ℱ := ℱ) (fun j ω => (W j ω).re) v w k
    (fun j => Complex.continuous_re.comp_stronglyMeasurable (hWm j)) hmeanRe hintRe hcondRe hv0
    h4Re
  have him := mart_moment4 (μ := μ) (ℱ := ℱ) (fun j ω => (W j ω).im) v w k
    (fun j => Complex.continuous_im.comp_stronglyMeasurable (hWm j)) hmeanIm hintIm hcondIm hv0
    h4Im
  have hpt : ∀ ω, ‖(∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4
        ≤ 2 * ((∑ j ∈ range k, (W j ω).re) ^ 4 + (∑ j ∈ range k, (W j ω).im) ^ 4) := by
    intro ω
    rw [hsum ω]
    have := norm_pow4_le_re_im (∑ j ∈ range k, W j ω)
    rwa [Complex.re_sum, Complex.im_sum] at this
  have hsm : StronglyMeasurable (fun ω => ‖(∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4) := by
    have heq : (fun ω => ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4)
        = fun ω => ‖∑ j ∈ range k, W j ω‖ ^ 4 := funext fun ω => by rw [hsum ω]
    rw [heq]
    refine (Finset.stronglyMeasurable_fun_sum (range k) fun j _ =>
      (hWm j).mono (ℱ.le (j + 1))).norm.pow 4
  have hdom : Integrable (fun ω =>
      2 * ((∑ j ∈ range k, (W j ω).re) ^ 4 + (∑ j ∈ range k, (W j ω).im) ^ 4)) μ :=
    (hre.1.add him.1).const_mul 2
  have hint : Integrable (fun ω => ‖(∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4) μ :=
    hdom.mono' hsm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖(∑ j ∈ range (min k (τ ω)),
          Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Y (j + 1) ω)) b‖ ^ 4 ∂μ
      ≤ ∫ ω, 2 * ((∑ j ∈ range k, (W j ω).re) ^ 4 + (∑ j ∈ range k, (W j ω).im) ^ 4) ∂μ :=
        integral_mono hint hdom hpt
    _ = 2 * (∫ ω, (∑ j ∈ range k, (W j ω).re) ^ 4 ∂μ
          + ∫ ω, (∑ j ∈ range k, (W j ω).im) ^ 4 ∂μ) := by
        rw [integral_const_mul, integral_add hre.1 him.1]
    _ ≤ 4 * (8 * (∑ j ∈ range k, v j) ^ 2 + 3 * ∑ j ∈ range k, w j) := by
        linarith [hre.2.2, him.2.2]

/-- **Markov + union (the moment Y tail)**: the fourth-moment version of the Chebyshev union
bound. Over all targets `k ≤ K` and all labels,
`μ{∃ k ≤ K, ∃ a, x ≤ ‖Σ_{j<k∧τ} U_{j+1,k} Y_{j+1}‖} ≤ (K+1) L^n · 4 (8 V² + 3 W) / x⁴` with
`V = Σ_{j<K} v_j`, `W = Σ_{j<K} w_j`. -/
theorem stopped_duhamel_moment4_union (L : ℕ) [NeZero L] {n : ℕ} {ξ : Fin n → ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Y : ℕ → Ω' → LoopArg L n → ℂ} (hY : ∀ i, StronglyMeasurable[ℱ i] (Y i))
    (K : ℕ) {v w : ℕ → ℝ} (hv0 : ∀ j < K, 0 ≤ v j) (hw0 : ∀ j < K, 0 ≤ w j)
    (hmeanRe : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).re | ℱ j] =ᵐ[μ] 0)
    (hmeanIm : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).im | ℱ j] =ᵐ[μ] 0)
    (hintRe : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      Integrable (fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).re ^ 4) μ)
    (hintIm : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      Integrable (fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).im ^ 4) μ)
    (hcondRe : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).re ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (hcondIm : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).im ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (h4Re : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      ∫ ω, (stoppedEdge L ξ u (u k) τ Y b j ω).re ^ 4 ∂μ ≤ w j)
    (h4Im : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      ∫ ω, (stoppedEdge L ξ u (u k) τ Y b j ω).im ^ 4 ∂μ ≤ w j)
    {x : ℝ} (hx : 0 < x) :
    μ.real {ω | ∃ k ≤ K, ∃ a, x ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Y (j + 1) ω)) a‖} ≤
      (K + 1 : ℝ) * (L : ℝ) ^ n
        * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j)) / x ^ 4 := by
  set F : ℕ → LoopArg L n → Ω' → ℝ := fun k a ω => ‖(∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Y (j + 1) ω)) a‖ with hFdef
  set Bd : ℝ := 4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j) with hBd
  have hx4 : 0 < x ^ 4 := by positivity
  have hone : ∀ k ≤ K, ∀ a, μ.real {ω | x ≤ F k a ω} ≤ Bd / x ^ 4 := by
    intro k hk a
    obtain ⟨hI, hM⟩ := stopped_duhamel_moment4 (μ := μ) L hτmeas hY k (u k) a
      (fun j hj => hmeanRe k hk a j hj) (fun j hj => hmeanIm k hk a j hj)
      (fun j hj => hintRe k hk a j hj) (fun j hj => hintIm k hk a j hj)
      (fun j hj => hcondRe k hk a j hj) (fun j hj => hcondIm k hk a j hj)
      (fun j hj => hv0 j (by omega)) (fun j hj => h4Re k hk a j hj)
      (fun j hj => h4Im k hk a j hj)
    have hV : ∑ j ∈ range k, v j ≤ ∑ j ∈ range K, v j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun j hj _ => hv0 j (Finset.mem_range.mp hj))
    have hV0 : 0 ≤ ∑ j ∈ range k, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hW : ∑ j ∈ range k, w j ≤ ∑ j ∈ range K, w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun j hj _ => hw0 j (Finset.mem_range.mp hj))
    have hMk : ∫ ω, F k a ω ^ 4 ∂μ ≤ Bd := by
      refine hM.trans ?_
      rw [hBd]
      have : (∑ j ∈ range k, v j) ^ 2 ≤ (∑ j ∈ range K, v j) ^ 2 :=
        pow_le_pow_left₀ hV0 hV 2
      linarith
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => by positivity) hI (x ^ 4)
    have hset : {ω | x ≤ F k a ω} = {ω | x ^ 4 ≤ F k a ω ^ 4} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h; exact pow_le_pow_left₀ hx.le h 4
      · intro h
        exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp h
    rw [hset, le_div_iff₀ hx4]
    calc μ.real {ω | x ^ 4 ≤ F k a ω ^ 4} * x ^ 4
        = x ^ 4 * μ.real {ω | x ^ 4 ≤ F k a ω ^ 4} := by ring
      _ ≤ ∫ ω, F k a ω ^ 4 ∂μ := hmark
      _ ≤ Bd := hMk
  have hincl : {ω | ∃ k ≤ K, ∃ a, x ≤ F k a ω}
      ⊆ ⋃ k ∈ range (K + 1), ⋃ a : LoopArg L n, {ω | x ≤ F k a ω} := by
    rintro ω ⟨k, hk, a, ha⟩
    simp only [Set.mem_iUnion]
    exact ⟨k, Finset.mem_range.mpr (by omega), a, ha⟩
  calc μ.real {ω | ∃ k ≤ K, ∃ a, x ≤ F k a ω}
      ≤ μ.real (⋃ k ∈ range (K + 1), ⋃ a : LoopArg L n, {ω | x ≤ F k a ω}) :=
        measureReal_mono hincl (measure_ne_top μ _)
    _ ≤ ∑ k ∈ range (K + 1), μ.real (⋃ a : LoopArg L n, {ω | x ≤ F k a ω}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ range (K + 1), ∑ a : LoopArg L n, μ.real {ω | x ≤ F k a ω} :=
        Finset.sum_le_sum fun k _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k ∈ range (K + 1), ∑ _a : LoopArg L n, Bd / x ^ 4 := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => ?_
        exact hone k (by have := Finset.mem_range.mp hk; omega) a
    _ = (K + 1 : ℝ) * (L : ℝ) ^ n * Bd / x ^ 4 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, card_loopArg_eq_pow L n,
          Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

/-- The `ΔP`-form of the moment bound: under `v_j ≤ Δ²P`, `w_j ≤ Δ⁴P²`, `KΔ ≤ 1`, `Δ ≤ 1`,
`P ≥ 0`, the fourth-moment budget `4 (8 V² + 3 W)` is at most `44 (ΔP)²` (the form
`C_p (ΔP)^p` with `p = 2`), and `(K+1)·4(8V²+3W) ≤ 88 Δ P²` when `1 ≤ K`. -/
theorem moment4_budget_le {K : ℕ} {Δ P : ℝ} (hΔ0 : 0 ≤ Δ) (hP0 : 0 ≤ P)
    (hKΔ : (K : ℝ) * Δ ≤ 1) (hK1 : 1 ≤ K) {v w : ℕ → ℝ} (hv0 : ∀ j < K, 0 ≤ v j)
    (hw0 : ∀ j < K, 0 ≤ w j) (hv : ∀ j < K, v j ≤ Δ ^ 2 * P) (hw : ∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) :
    4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j) ≤ 44 * (Δ * P) ^ 2
      ∧ (K + 1 : ℝ) * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j))
          ≤ 88 * Δ * P ^ 2 := by
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hΔ1 : Δ ≤ 1 := by nlinarith
  have hV : ∑ j ∈ range K, v j ≤ (K : ℝ) * (Δ ^ 2 * P) := by
    have := Finset.sum_le_sum (s := range K) fun j hj => hv j (Finset.mem_range.mp hj)
    simpa using this
  have hV0 : 0 ≤ ∑ j ∈ range K, v j := Finset.sum_nonneg fun j hj => hv0 j (Finset.mem_range.mp hj)
  have hW : ∑ j ∈ range K, w j ≤ (K : ℝ) * (Δ ^ 4 * P ^ 2) := by
    have := Finset.sum_le_sum (s := range K) fun j hj => hw j (Finset.mem_range.mp hj)
    simpa using this
  have hKΔ0 : 0 ≤ (K : ℝ) * Δ := by positivity
  -- `V ≤ Δ P`, `V² ≤ (ΔP)²`
  have hV' : ∑ j ∈ range K, v j ≤ Δ * P := by
    calc ∑ j ∈ range K, v j ≤ (K : ℝ) * (Δ ^ 2 * P) := hV
      _ = ((K : ℝ) * Δ) * (Δ * P) := by ring
      _ ≤ 1 * (Δ * P) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = Δ * P := one_mul _
  have hV2 : (∑ j ∈ range K, v j) ^ 2 ≤ (Δ * P) ^ 2 := pow_le_pow_left₀ hV0 hV' 2
  -- `W ≤ Δ³P² ≤ (ΔP)²`
  have hW' : ∑ j ∈ range K, w j ≤ Δ ^ 3 * P ^ 2 := by
    calc ∑ j ∈ range K, w j ≤ (K : ℝ) * (Δ ^ 4 * P ^ 2) := hW
      _ = ((K : ℝ) * Δ) * (Δ ^ 3 * P ^ 2) := by ring
      _ ≤ 1 * (Δ ^ 3 * P ^ 2) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = Δ ^ 3 * P ^ 2 := one_mul _
  have hΔ3 : Δ ^ 3 * P ^ 2 ≤ (Δ * P) ^ 2 := by
    have : Δ ^ 3 ≤ Δ ^ 2 := pow_le_pow_of_le_one hΔ0 hΔ1 (by norm_num)
    have h2 : Δ ^ 3 * P ^ 2 ≤ Δ ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg P)
    nlinarith [h2]
  have hA : 4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j) ≤ 44 * (Δ * P) ^ 2 := by
    nlinarith
  refine ⟨hA, ?_⟩
  -- `(K+1)·(ΔP)²·44 ≤ 2K·44 Δ² P² ≤ 88 Δ P²`
  have hK2 : (K + 1 : ℝ) ≤ 2 * K := by linarith
  calc (K + 1 : ℝ) * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j))
      ≤ (2 * K) * (44 * (Δ * P) ^ 2) := by
        have hW0 : 0 ≤ ∑ j ∈ range K, w j :=
          Finset.sum_nonneg fun j hj => hw0 j (Finset.mem_range.mp hj)
        refine mul_le_mul hK2 hA (by positivity) (by positivity)
    _ = 88 * ((K : ℝ) * Δ) * Δ * P ^ 2 := by ring
    _ ≤ 88 * 1 * Δ * P ^ 2 := by
        have : 0 ≤ Δ * P ^ 2 := by positivity
        nlinarith
    _ = 88 * Δ * P ^ 2 := by ring

end YMoment

/-! ### The restricted kernel class and the hypothesis bundles -/

section Assembly

/-- **The class on which the sharp kernel bound (7.16) is available**: `(ℓ_{u_i}·Kd, δ)`-fast
decay at the kernel's start time `u_i` ((7.13), the input of `Q716.uker_decay_le_nonAlt`), and,
in Case 2 (`sz = true`), the sum-zero property (7.15) at the paper's `a₁` (the extra input of
`Q716.uker_decay_le_sumZero`). -/
def KerClass (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (u : ℕ → ℝ) (Kd : ℝ) (sz : Bool) (δ : ℝ)
    (i : ℕ) (X : LoopArg L n → ℂ) : Prop :=
  FastDecay L (ellHat L ((u i : ℝ) : ℂ) * Kd) δ X ∧ (sz = true → SumZeroAt L 0 X)

/-- **The analytic hypotheses of the fixed assembly, pathwise drift form**.
Compared with an assembly hypothesis with an unrestricted kernel bound:
* the kernel hypothesis `hker` is **class-restricted** with an additive error: only for inputs in
  `KerClass … δ i` does `‖U_{i,k} X‖ ≤ κ_{i,k}‖X‖_max + ε_{i,k} δ` hold (the shape of
  `Q716.uker_decay_le_nonAlt` / `Q716.uker_decay_le_sumZero`); there is **no** unrestricted
  kernel hypothesis — the coarse row-sum bound used for `R` is derived from `‖ξ_p‖ ≤ 1`,
  `u_i ∈ [0,1)`, `3 ≤ L`;
* the kernel is only applied to inputs in the class: `A0` on `{0 < τ}` and the drift `Dr j` on
  `{j < τ}` (for Case 2 the consumer passes the `Q`-transformed process and drift);
* the drift bound `d_j(ω)` and its decay error `δD_j(ω)` are pathwise;
* the second-order increment `Y` enters through conditional second and fourth moments
  (the input of the fourth-moment tail `stopped_duhamel_moment4_union`), not through a
  Chebyshev second moment. -/
structure GridAssemblyHypPW {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    (ℱ : Filtration ℕ mΩ') (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (ξ : Fin n → ℂ) (u : ℕ → ℝ)
    (τ : Ω' → ℕ) (Δ : ℝ) (K : ℕ) (Kd : ℝ) (sz : Bool) (A0 : Ω' → LoopArg L n → ℂ)
    (A Dr Z Y R : ℕ → Ω' → LoopArg L n → ℂ) (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ)
    (dDrift δD : ℕ → Ω' → ℝ) (c : ℕ → LoopArg L n → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) :
    Prop where
  hL3 : 3 ≤ L
  hξ : ∀ p, ‖ξ p‖ ≤ 1
  hu0 : ∀ i ≤ K, 0 ≤ u i
  hu1 : ∀ i ≤ K, u i < 1
  hΔ0 : 0 ≤ Δ
  /-- **h-exp**, as in `GridAssembly.lean` (fixed target `u k`, sum cut at `τ`). -/
  hexp : ∀ k ≤ K, ∀ᵐ ω ∂μ, A k ω = Uker L ξ (u 0 : ℂ) (u k : ℂ) (A0 ω)
      + ∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
          ((Δ : ℂ) • Dr j ω + Z (j + 1) ω + Y (j + 1) ω + R j ω)
  hκ0 : ∀ i k, i ≤ k → k ≤ K → 0 ≤ κ i k
  hε0 : ∀ i k, i ≤ k → k ≤ K → 0 ≤ εK i k
  /-- **h-ker′**, the class-restricted kernel bound with additive error. -/
  hker : ∀ i k, i ≤ k → k ≤ K → ∀ (X : LoopArg L n → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → KerClass L u Kd sz δ i X →
      ∀ a, ‖Uker L ξ (u i : ℂ) (u k : ℂ) X a‖ ≤ κ i k * M + εK i k * δ
  hδ0 : 0 ≤ δ0
  /-- The initial datum is in the class on `{0 < τ}` (the good event at the initial time). -/
  hA0cls : ∀ ω, 0 < τ ω → KerClass L u Kd sz δ0 0 (A0 ω)
  hdDrift0 : ∀ ω j, j < K → 0 ≤ dDrift j ω
  hδD0 : ∀ ω j, j < K → 0 ≤ δD j ω
  /-- **h-drift**, pathwise, on `{j < τ}`. -/
  hdrift : ∀ ω j, j < K → j < τ ω → ∀ b, ‖Dr j ω b‖ ≤ dDrift j ω
  /-- The drift is in the class of the kernel `U_{j+1,·}` on `{j < τ}`. -/
  hDcls : ∀ ω j, j < K → j < τ ω → KerClass L u Kd sz (δD j ω) (j + 1) (Dr j ω)
  hc_pos : ∀ k, 1 ≤ k → k ≤ K → ∀ a, 0 < ∑ j ∈ range k, (c k a j : ℝ)
  hYmeas : ∀ i, StronglyMeasurable[ℱ i] (Y i)
  hv0 : ∀ j < K, 0 ≤ v j
  hw0 : ∀ j < K, 0 ≤ w j
  /-- **h-Y′**: conditional mean zero, `L⁴`, conditional second moment `≤ v_j`, fourth moment
  `≤ w_j`, for the real and imaginary parts of the stopped, propagated increment. -/
  hYmeanRe : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).re | ℱ j] =ᵐ[μ] 0
  hYmeanIm : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).im | ℱ j] =ᵐ[μ] 0
  hYintRe : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      Integrable (fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).re ^ 4) μ
  hYintIm : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      Integrable (fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).im ^ 4) μ
  hYcondRe : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).re ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j
  hYcondIm : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L ξ u (u k) τ Y b j ω).im ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j
  hY4Re : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      ∫ ω, (stoppedEdge L ξ u (u k) τ Y b j ω).re ^ 4 ∂μ ≤ w j
  hY4Im : ∀ k ≤ K, ∀ (b : LoopArg L n) (j : ℕ), j < k →
      ∫ ω, (stoppedEdge L ξ u (u k) τ Y b j ω).im ^ 4 ∂μ ≤ w j
  hstepErr0 : ∀ j < K, 0 ≤ stepErr j
  /-- **h-R** on `{j < τ}`. -/
  hR : ∀ ω j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j

/-- **The coarse row-sum kernel bound** (Lemma 7.1, `norm_Uker_apply_le`), derived — not
assumed — from `3 ≤ L`, `‖ξ_p‖ ≤ 1`, `u_i, u_k ∈ [0,1)`: `‖U_{i,k} X‖ ≤ (1+(1-u_k)⁻¹)^n ‖X‖`.
Used only for the remainder `R`. -/
theorem norm_Uker_coarse (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ p, ‖ξ p‖ ≤ 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {X : LoopArg L n → ℂ} {M : ℝ} (hM : 0 ≤ M) (hX : ∀ b, ‖X b‖ ≤ M) (a : LoopArg L n) :
    ‖Uker L ξ (s : ℂ) (t : ℂ) X a‖ ≤ (1 + (1 - t)⁻¹) ^ n * M := by
  have hpos : 0 < 1 - t := by linarith
  have hb : ∀ p, ‖((t : ℝ) : ℂ) * ξ p‖ ≤ t := by
    intro p
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    nlinarith [hξ p, norm_nonneg (ξ p)]
  have ht : ∀ p, ‖((t : ℝ) : ℂ) * ξ p‖ < 1 := fun p => (hb p).trans_lt ht1
  have hC : ∀ p, 1 + ‖(((s : ℝ) : ℂ) - ((t : ℝ) : ℂ)) * ξ p‖
      * (1 - ‖((t : ℝ) : ℂ) * ξ p‖)⁻¹ ≤ 1 + (1 - t)⁻¹ := by
    intro p
    have hst : |s - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have ha : ‖(((s : ℝ) : ℂ) - ((t : ℝ) : ℂ)) * ξ p‖ ≤ 1 := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [hξ p, norm_nonneg (ξ p), abs_nonneg (s - t)]
    have hinv : (1 - ‖((t : ℝ) : ℂ) * ξ p‖)⁻¹ ≤ (1 - t)⁻¹ :=
      inv_anti₀ hpos (by linarith [hb p])
    have hinv0 : 0 ≤ (1 - ‖((t : ℝ) : ℂ) * ξ p‖)⁻¹ := inv_nonneg.mpr (by linarith [hb p])
    have := mul_le_mul ha hinv hinv0 zero_le_one
    linarith
  exact norm_Uker_apply_le L hL ht hM hC hX a

private lemma sum_Uker_four_apply_eq {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (s : ℕ → ℂ)
    (t : ℂ) (m : ℕ) (Δ : ℂ) (Dr Z Y R : ℕ → LoopArg L n → ℂ) (a : LoopArg L n) :
    (∑ j ∈ range m, Uker L ξ (s j) t (Δ • Dr j + Z j + Y j + R j)) a
      = Δ * (∑ j ∈ range m, Uker L ξ (s j) t (Dr j) a)
        + (∑ j ∈ range m, Uker L ξ (s j) t (Z j) a)
        + (∑ j ∈ range m, Uker L ξ (s j) t (Y j) a)
        + (∑ j ∈ range m, Uker L ξ (s j) t (R j) a) := by
  rw [Finset.sum_apply]
  have hterm : ∀ j, Uker L ξ (s j) t (Δ • Dr j + Z j + Y j + R j) a
      = Δ * Uker L ξ (s j) t (Dr j) a + Uker L ξ (s j) t (Z j) a
        + Uker L ξ (s j) t (Y j) a + Uker L ξ (s j) t (R j) a := by
    intro j
    have h1 : Uker L ξ (s j) t (Δ • Dr j + Z j + Y j + R j)
        = Uker L ξ (s j) t (Δ • Dr j) + Uker L ξ (s j) t (Z j)
          + Uker L ξ (s j) t (Y j) + Uker L ξ (s j) t (R j) := by
      rw [Uker_add, Uker_add, Uker_add]
    rw [h1]
    simp only [Pi.add_apply, Uker_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.mul_sum]

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- **The single-scale core of `grid_assembly_stopped_pathwise`** (pathwise drift), with free
thresholds `λ` (Azuma, for
the linear increment `Z`) and `x_Y > 0` (fourth-moment tail, for the second-order increment `Y`).
The sharp restricted `κ, ε` act only on `A0` and the drift; the remainder uses the derived coarse
`(1+(1-u_k)⁻¹)^n`. -/
theorem grid_assembly_stopped_core_pw (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] {ξ : Fin n → ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} {Δ : ℝ} {K : ℕ} {Kd : ℝ} {sz : Bool}
    {A0 : Ω' → LoopArg L n → ℂ} {A Dr Z Y R : ℕ → Ω' → LoopArg L n → ℂ} {κ εK : ℕ → ℕ → ℝ}
    {δ0 : ℝ} {dDrift δD : ℕ → Ω' → ℝ} {c : ℕ → LoopArg L n → ℕ → ℝ≥0} {v w stepErr : ℕ → ℝ}
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    (hZmeas : ∀ i, StronglyMeasurable[ℱ i] (Z i))
    (hqv : ∀ k ≤ K, ∀ (a : LoopArg L n) (j : ℕ), j < k →
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    (h : GridAssemblyHypPW μ ℱ L ξ u τ Δ K Kd sz A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr)
    {lam : ℝ} (hlam : 0 ≤ lam) {xY : ℝ} (hxY : 0 < xY) :
    ∃ G : Set Ω', μ.real Gᶜ ≤ 4 * (K : ℝ) * (L : ℝ) ^ n * Real.exp (-lam ^ 2 / 4)
        + (K + 1 : ℝ) * (L : ℝ) ^ n
          * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j)) / xY ^ 4
      ∧ ∀ ω ∈ G, 0 < τ ω → ∀ k ≤ K, ∀ a : LoopArg L n,
          ‖A k ω a‖ ≤ κ 0 k * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
            + εK 0 k * δ0
            + Δ * ∑ j ∈ range k, (κ (j + 1) k * dDrift j ω + εK (j + 1) k * δD j ω)
            + lam * Real.sqrt (∑ j ∈ range k, (c k a j : ℝ))
            + xY
            + ∑ j ∈ range k, (1 + (1 - u k)⁻¹) ^ n * stepErr j := by
  -- the Azuma event (as in `GridAssembly.lean`)
  set xZ : ℕ → LoopArg L n → ℝ :=
    fun k a => if k = 0 then 1 else lam * Real.sqrt (∑ j ∈ range k, (c k a j : ℝ)) with hxZdef
  have hxZnn : ∀ k ≤ K, ∀ a, 0 ≤ xZ k a := by
    intro k _ a
    by_cases hk : k = 0
    · simp [hxZdef, hk]
    · simp only [hxZdef, hk, ↓reduceIte]; positivity
  have hxZ0 : ∀ a, 0 < xZ 0 a := fun a => by simp [hxZdef]
  have hZunion := stopped_duhamel_azuma_union L hτmeas hZmeas K (c := c)
    (fun k hk a j hj => hqv k hk a j hj) hxZnn hxZ0
  have hZbound : (∑ k ∈ Finset.Icc 1 K, ∑ a : LoopArg L n,
        4 * Real.exp (-(xZ k a) ^ 2 / (4 * ∑ j ∈ range k, (c k a j : ℝ))))
      = 4 * (K : ℝ) * (L : ℝ) ^ n * Real.exp (-lam ^ 2 / 4) := by
    have hterm : ∀ k ∈ Finset.Icc 1 K, ∀ a : LoopArg L n,
        4 * Real.exp (-(xZ k a) ^ 2 / (4 * ∑ j ∈ range k, (c k a j : ℝ)))
          = 4 * Real.exp (-lam ^ 2 / 4) := by
      intro k hk a
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
      have hcpos : 0 < ∑ j ∈ range k, (c k a j : ℝ) := h.hc_pos k hk1 hkK a
      have hk0 : k ≠ 0 := by omega
      have hxsq : (xZ k a) ^ 2 = lam ^ 2 * ∑ j ∈ range k, (c k a j : ℝ) := by
        simp only [hxZdef, hk0, ↓reduceIte]
        rw [mul_pow, Real.sq_sqrt hcpos.le]
      rw [hxsq]
      congr 2
      field_simp
    rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun a _ => hterm k hk a]
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Finset.card_univ, card_loopArg_eq_pow L n]
    have hcard : K + 1 - 1 = K := by omega
    rw [hcard, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  set GZc : Set Ω' := {ω | ∃ k ≤ K, ∃ a, xZ k a ≤ ‖(∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖} with hGZcdef
  have hGZcbound : μ.real GZc ≤ 4 * (K : ℝ) * (L : ℝ) ^ n * Real.exp (-lam ^ 2 / 4) :=
    hZunion.trans hZbound.le
  -- the fourth-moment Y event
  set GYc : Set Ω' := {ω | ∃ k ≤ K, ∃ a, xY ≤ ‖(∑ j ∈ range (min k (τ ω)),
      Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Y (j + 1) ω)) a‖} with hGYcdef
  have hGYcbound : μ.real GYc ≤ (K + 1 : ℝ) * (L : ℝ) ^ n
      * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j)) / xY ^ 4 :=
    stopped_duhamel_moment4_union L hτmeas h.hYmeas K h.hv0 h.hw0 h.hYmeanRe h.hYmeanIm
      h.hYintRe h.hYintIm h.hYcondRe h.hYcondIm h.hY4Re h.hY4Im hxY
  -- the full-measure h-exp event
  have hexpAll : ∀ᵐ ω ∂μ, ∀ k, k ≤ K → A k ω = Uker L ξ (u 0 : ℂ) (u k : ℂ) (A0 ω)
      + ∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
          ((Δ : ℂ) • Dr j ω + Z (j + 1) ω + Y (j + 1) ω + R j ω) := by
    refine ae_all_iff.mpr fun k => ?_
    by_cases hk : k ≤ K
    · filter_upwards [h.hexp k hk] with ω hω _ using hω
    · exact ae_of_all _ fun ω hk' => absurd hk' hk
  set Ω0c : Set Ω' := {ω | ¬ ∀ k, k ≤ K → A k ω = Uker L ξ (u 0 : ℂ) (u k : ℂ) (A0 ω)
      + ∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
          ((Δ : ℂ) • Dr j ω + Z (j + 1) ω + Y (j + 1) ω + R j ω)} with hΩ0cdef
  have hΩ0cnull : μ.real Ω0c = 0 := by
    have h0 : μ Ω0c = 0 := (MeasureTheory.ae_iff).mp hexpAll
    simp [Measure.real, h0]
  refine ⟨(GZc ∪ GYc ∪ Ω0c)ᶜ, ?_, ?_⟩
  · rw [compl_compl]
    calc μ.real (GZc ∪ GYc ∪ Ω0c)
        ≤ μ.real (GZc ∪ GYc) + μ.real Ω0c := measureReal_union_le _ _
      _ ≤ (μ.real GZc + μ.real GYc) + μ.real Ω0c := by
          have h1 := measureReal_union_le (μ := μ) GZc GYc
          linarith
      _ ≤ _ := by rw [hΩ0cnull]; linarith
  · intro ω hω hτpos k hkK a
    have hωGZ : ω ∉ GZc := fun h' => hω (Or.inl (Or.inl h'))
    have hωGY : ω ∉ GYc := fun h' => hω (Or.inl (Or.inr h'))
    have hωΩ0 : ω ∉ Ω0c := fun h' => hω (Or.inr h')
    have hAll : ∀ k, k ≤ K → A k ω = Uker L ξ (u 0 : ℂ) (u k : ℂ) (A0 ω)
        + ∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
            ((Δ : ℂ) • Dr j ω + Z (j + 1) ω + Y (j + 1) ω + R j ω) := by
      by_contra hc
      exact hωΩ0 hc
    set INIT : ℂ := Uker L ξ (u 0 : ℂ) (u k : ℂ) (A0 ω) a with hINITdef
    set S1 : ℂ := (∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Dr j ω) a)
      with hS1def
    set S2 : ℂ := (∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω) a)
      with hS2def
    set S3 : ℂ := (∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Y (j + 1) ω) a)
      with hS3def
    set S4 : ℂ := (∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (R j ω) a)
      with hS4def
    have hAeq : A k ω a = INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4) := by
      rw [hAll k hkK, Pi.add_apply]
      congr 1
      exact sum_Uker_four_apply_eq L ξ (fun j => (u (j + 1) : ℂ)) (u k : ℂ) (min k (τ ω))
        (Δ : ℂ) (fun j => Dr j ω) (fun j => Z (j + 1) ω) (fun j => Y (j + 1) ω)
        (fun j => R j ω) a
    have hINITle : ‖INIT‖
        ≤ κ 0 k * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) + εK 0 k * δ0 := by
      obtain ⟨b0⟩ := (inferInstance : Nonempty (LoopArg L n))
      have hA0nn : (0:ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖) :=
        le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b0))
      exact h.hker 0 k (Nat.zero_le k) hkK (A0 ω) _ δ0 hA0nn h.hδ0
        (fun b => Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b)) (h.hA0cls ω hτpos) a
    have hS1le : ‖S1‖ ≤ ∑ j ∈ range k, (κ (j + 1) k * dDrift j ω + εK (j + 1) k * δD j ω) := by
      have h2 : ∀ j ∈ range (min k (τ ω)),
          ‖Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Dr j ω) a‖
            ≤ κ (j + 1) k * dDrift j ω + εK (j + 1) k * δD j ω := by
        intro j hj
        have hjk : j < k := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact h.hker (j + 1) k hjk hkK (Dr j ω) (dDrift j ω) (δD j ω)
          (h.hdDrift0 ω j (by omega)) (h.hδD0 ω j (by omega)) (h.hdrift ω j (by omega) hjτ)
          (h.hDcls ω j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjk : j < k := Finset.mem_range.mp hj
      exact add_nonneg (mul_nonneg (h.hκ0 (j + 1) k hjk hkK) (h.hdDrift0 ω j (by omega)))
        (mul_nonneg (h.hε0 (j + 1) k hjk hkK) (h.hδD0 ω j (by omega)))
    have hS1le' : ‖(Δ : ℂ) * S1‖
        ≤ Δ * ∑ j ∈ range k, (κ (j + 1) k * dDrift j ω + εK (j + 1) k * δD j ω) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h.hΔ0]
      exact mul_le_mul_of_nonneg_left hS1le h.hΔ0
    have hS2le : ‖S2‖ ≤ lam * Real.sqrt (∑ j ∈ range k, (c k a j : ℝ)) := by
      by_cases hk0 : k = 0
      · subst hk0
        simp [hS2def]
      · have hlt : ‖S2‖ < xZ k a := by
          by_contra hc
          push Not at hc
          exact hωGZ ⟨k, hkK, a, by rw [Finset.sum_apply]; exact hc⟩
        simpa [hxZdef, hk0] using hlt.le
    have hS3le : ‖S3‖ ≤ xY := by
      by_contra hc
      push Not at hc
      exact hωGY ⟨k, hkK, a, by rw [Finset.sum_apply]; exact hc.le⟩
    have hS4le : ‖S4‖ ≤ ∑ j ∈ range k, (1 + (1 - u k)⁻¹) ^ n * stepErr j := by
      have hk0 := h.hu0 k hkK
      have hk1 := h.hu1 k hkK
      have h2 : ∀ j ∈ range (min k (τ ω)),
          ‖Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (R j ω) a‖ ≤ (1 + (1 - u k)⁻¹) ^ n * stepErr j := by
        intro j hj
        have hjk : j < k := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact norm_Uker_coarse L h.hL3 h.hξ (h.hu0 (j + 1) (by omega)) (h.hu1 (j + 1) (by omega))
          hk0 hk1 (h.hstepErr0 j (by omega)) (h.hR ω j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjk : j < k := Finset.mem_range.mp hj
      have hpos : 0 < 1 - u k := by linarith
      exact mul_nonneg (by positivity) (h.hstepErr0 j (by omega))
    rw [hAeq]
    calc ‖INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4)‖
        ≤ ‖INIT‖ + ‖(Δ : ℂ) * S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ := by
          have e1 := norm_add_le INIT ((Δ : ℂ) * S1 + S2 + S3 + S4)
          have e2 := norm_add_le ((Δ : ℂ) * S1 + S2 + S3) S4
          have e3 := norm_add_le ((Δ : ℂ) * S1 + S2) S3
          have e4 := norm_add_le ((Δ : ℂ) * S1) S2
          linarith
      _ ≤ _ := by linarith

end Assembly

/-! ### The probability budget and the N-level statements -/

section Budget

/-- **The fourth-moment Y budget** (deterministic): for `N ≥ 2`, `L ≤ N^{C_L}`,
`0 ≤ Δ ≤ N^{-C_K}`, `0 ≤ P ≤ N^{C_P}` and `C_K ≥ D₁ + 4D + n C_L + 2 C_P + 8`,
`L^n · 88 Δ P² / (N^{-D})⁴ ≤ N^{-D₁}/2`. -/
theorem Ytail_budget {N : ℕ} (hN2 : (2 : ℝ) ≤ N) (n : ℕ) {D D₁ C_L C_P C_K : ℝ}
    (hCK : D₁ + 4 * D + n * C_L + 2 * C_P + 8 ≤ C_K) {L : ℕ}
    (hL : (L : ℝ) ≤ (N : ℝ) ^ C_L) {Δ P : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ (N : ℝ) ^ (-C_K))
    (hP0 : 0 ≤ P) (hP : P ≤ (N : ℝ) ^ C_P) :
    (L : ℝ) ^ n * (88 * Δ * P ^ 2) / ((N : ℝ) ^ (-D)) ^ 4 ≤ (N : ℝ) ^ (-D₁) / 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hLn : (L : ℝ) ^ n ≤ (N : ℝ) ^ ((n : ℝ) * C_L) := by
    rw [mul_comm, Real.rpow_mul hN0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Nat.cast_nonneg L) hL n
  have hP2 : P ^ 2 ≤ (N : ℝ) ^ (2 * C_P) := by
    have h1 : P ^ 2 ≤ ((N : ℝ) ^ C_P) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    have h2 : ((N : ℝ) ^ C_P) ^ 2 = (N : ℝ) ^ (2 * C_P) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    linarith
  have hx : ((N : ℝ) ^ (-D)) ^ 4 = (N : ℝ) ^ (-(4 * D)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hxpos : 0 < ((N : ℝ) ^ (-D)) ^ 4 := by positivity
  have key : (L : ℝ) ^ n * (88 * Δ * P ^ 2)
      ≤ 88 * (N : ℝ) ^ ((n : ℝ) * C_L + -C_K + 2 * C_P) := by
    calc (L : ℝ) ^ n * (88 * Δ * P ^ 2) = 88 * ((L : ℝ) ^ n * Δ * P ^ 2) := by ring
      _ ≤ 88 * ((N : ℝ) ^ ((n : ℝ) * C_L) * (N : ℝ) ^ (-C_K) * (N : ℝ) ^ (2 * C_P)) := by
          gcongr
      _ = 88 * (N : ℝ) ^ ((n : ℝ) * C_L + -C_K + 2 * C_P) := by
          rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hexp : (n : ℝ) * C_L + -C_K + 2 * C_P ≤ -D₁ + -(4 * D) + -8 := by linarith
  have hmono : (N : ℝ) ^ ((n : ℝ) * C_L + -C_K + 2 * C_P) ≤ (N : ℝ) ^ (-D₁ + -(4 * D) + -8) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have h8 : 88 * (N : ℝ) ^ (-8 : ℝ) ≤ 1 / 2 := by
    have hN8 : (256 : ℝ) ≤ (N : ℝ) ^ (8 : ℝ) := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ (N : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hN2 8
    rw [Real.rpow_neg hN0.le]
    have hpos : 0 < (N : ℝ) ^ (8 : ℝ) := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  rw [div_le_iff₀ hxpos, hx]
  have hsplit : (N : ℝ) ^ (-D₁ + -(4 * D) + -8)
      = (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(4 * D)) * (N : ℝ) ^ (-8 : ℝ) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hA : 0 ≤ (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(4 * D)) := by positivity
  calc (L : ℝ) ^ n * (88 * Δ * P ^ 2)
      ≤ 88 * (N : ℝ) ^ (-D₁ + -(4 * D) + -8) := key.trans (by linarith)
    _ = ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(4 * D))) * (88 * (N : ℝ) ^ (-8 : ℝ)) := by
        rw [hsplit]; ring
    _ ≤ ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(4 * D))) * (1 / 2) :=
        mul_le_mul_of_nonneg_left h8 hA
    _ = (N : ℝ) ^ (-D₁) / 2 * (N : ℝ) ^ (-(4 * D)) := by ring

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

variable [StandardBorelSpace Ω']

/-- **`grid_assembly_stopped_pathwise`.** The assembled bound with a
**pathwise** drift bound `‖Dr_j(ω)‖ ≤ d_j(ω)` on `{j < τ}` (the input the PP Bihari variant needs).
For every `n`, `ε > 0`, `D`, `D₁`, `C_L`, `C_P` and every
`C_K ≥ max(0, D₁ + 4D + n C_L + 2 C_P + 8)`, eventually in `N`, uniformly over `1 ≤ K ≤ ⌈N^{C_K}⌉₊`,
`L ≤ N^{C_L}`, grid steps `Δ ≤ N^{-C_K}` with `KΔ ≤ 1`, and all data satisfying `GridAssemblyHypPW`
with Y moments `v_j ≤ Δ²P`, `w_j ≤ Δ⁴P²`, `0 ≤ P ≤ N^{C_P}`: one event `G` with `μ(Gᶜ) ≤ N^{-D₁}` on
which, for `0 < τ(ω)`, for all `k ≤ K` simultaneously and all labels `a`,
`‖A_k a‖ ≤ κ_{0,k}‖A0‖ + ε_{0,k}δ0 + Δ Σ_{j<k}(κ_{j+1,k} d_j(ω) + ε_{j+1,k} δD_j(ω))
  + N^ε (Σ_{j<k} c k a j)^{1/2} + N^{-D} + Σ_{j<k} (1+(1-u_k)⁻¹)^n stepErr_j`.
The proof is pathwise, so `d_j` need not be measurable (any `F_j`-measurable `d_j` is allowed). -/
theorem grid_assembly_stopped_pathwise (n : ℕ) [NeZero n] {ε : ℝ} (hε : 0 < ε)
    (D D₁ C_L C_P C_K : ℝ) (hCK0 : 0 ≤ C_K)
    (hCK : D₁ + 4 * D + n * C_L + 2 * C_P + 8 ≤ C_K) :
    ∀ᶠ N : ℕ in atTop, ∀ (K L : ℕ) [NeZero L], 1 ≤ K → K ≤ ⌈(N : ℝ) ^ C_K⌉₊ →
      (L : ℝ) ≤ (N : ℝ) ^ C_L →
      ∀ (ξ : Fin n → ℂ) (u : ℕ → ℝ) (τ : Ω' → ℕ) (Δ Kd : ℝ) (sz : Bool)
        (A0 : Ω' → LoopArg L n → ℂ) (A Dr Z Y R : ℕ → Ω' → LoopArg L n → ℂ)
        (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → Ω' → ℝ)
        (c : ℕ → LoopArg L n → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      Δ ≤ (N : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 → 0 ≤ P → P ≤ (N : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) →
      (∀ i, StronglyMeasurable[ℱ i] (Z i)) →
      (∀ k ≤ K, ∀ (a : LoopArg L n) (j : ℕ), j < k →
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).im) (c k a j) μ) →
      GridAssemblyHypPW μ ℱ L ξ u τ Δ K Kd sz A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      ∃ G : Set Ω', μ.real Gᶜ ≤ (N : ℝ) ^ (-D₁)
        ∧ ∀ ω ∈ G, 0 < τ ω → ∀ k ≤ K, ∀ a : LoopArg L n,
          ‖A k ω a‖ ≤ κ 0 k * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
            + εK 0 k * δ0
            + Δ * ∑ j ∈ range k, (κ (j + 1) k * dDrift j ω + εK (j + 1) k * δD j ω)
            + (N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k, (c k a j : ℝ))
            + (N : ℝ) ^ (-D)
            + ∑ j ∈ range k, (1 + (1 - u k)⁻¹) ^ n * stepErr j := by
  filter_upwards [assembly_prob_budget n hε D₁ C_K C_L hCK0] with N hNb
  obtain ⟨hN2, hbudZ⟩ := hNb
  intro K L _ hK1 hK hL ξ u τ Δ Kd sz A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hΔ hKΔ hP0
    hP hv hw hτmeas hZmeas hqv h
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨G, hG, hbd⟩ := grid_assembly_stopped_core_pw L hτmeas hZmeas hqv h
    (Real.rpow_nonneg hN0.le ε) hx
  refine ⟨G, hG.trans ?_, hbd⟩
  have hZ := hbudZ K L hK hL
  have hbud := (moment4_budget_le h.hΔ0 hP0 hKΔ hK1 h.hv0 h.hw0 hv hw).2
  have hY := Ytail_budget hN2 n hCK hL h.hΔ0 hΔ hP0 hP
  have hLn : (0 : ℝ) ≤ (L : ℝ) ^ n := by positivity
  have hx4 : 0 < ((N : ℝ) ^ (-D)) ^ 4 := by positivity
  have hYle : (K + 1 : ℝ) * (L : ℝ) ^ n
      * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j)) / ((N : ℝ) ^ (-D)) ^ 4
      ≤ (N : ℝ) ^ (-D₁) / 2 := by
    refine le_trans ?_ hY
    rw [show (K + 1 : ℝ) * (L : ℝ) ^ n
        * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j))
        = (L : ℝ) ^ n * ((K + 1 : ℝ)
          * (4 * (8 * (∑ j ∈ range K, v j) ^ 2 + 3 * ∑ j ∈ range K, w j))) by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbud hLn) hx4.le
  have hsq : ((N : ℝ) ^ ε) ^ 2 = (N : ℝ) ^ (2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  rw [hsq] at hZ ⊢
  linarith

/-- **The pathwise assembly at the random target `k = τ(ω)`** (given `1 ≤ τ ≤ K`); at this target
h-exp is the true stopped expansion. -/
theorem grid_assembly_at_tau' (n : ℕ) [NeZero n] {ε : ℝ} (hε : 0 < ε)
    (D D₁ C_L C_P C_K : ℝ) (hCK0 : 0 ≤ C_K)
    (hCK : D₁ + 4 * D + n * C_L + 2 * C_P + 8 ≤ C_K) :
    ∀ᶠ N : ℕ in atTop, ∀ (K L : ℕ) [NeZero L], 1 ≤ K → K ≤ ⌈(N : ℝ) ^ C_K⌉₊ →
      (L : ℝ) ≤ (N : ℝ) ^ C_L →
      ∀ (ξ : Fin n → ℂ) (u : ℕ → ℝ) (τ : Ω' → ℕ) (Δ Kd : ℝ) (sz : Bool)
        (A0 : Ω' → LoopArg L n → ℂ) (A Dr Z Y R : ℕ → Ω' → LoopArg L n → ℂ)
        (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → Ω' → ℝ)
        (c : ℕ → LoopArg L n → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      Δ ≤ (N : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 → 0 ≤ P → P ≤ (N : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) →
      (∀ i, StronglyMeasurable[ℱ i] (Z i)) →
      (∀ k ≤ K, ∀ (a : LoopArg L n) (j : ℕ), j < k →
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
        HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
          (fun ω => ({ω' | j < τ ω'}.indicator
            (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).im) (c k a j) μ) →
      GridAssemblyHypPW μ ℱ L ξ u τ Δ K Kd sz A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      (∀ ω, τ ω ≤ K) →
      ∃ G : Set Ω', μ.real Gᶜ ≤ (N : ℝ) ^ (-D₁)
        ∧ ∀ ω ∈ G, 0 < τ ω → ∀ a : LoopArg L n,
          ‖A (τ ω) ω a‖
            ≤ κ 0 (τ ω) * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
              + εK 0 (τ ω) * δ0
              + Δ * ∑ j ∈ range (τ ω),
                  (κ (j + 1) (τ ω) * dDrift j ω + εK (j + 1) (τ ω) * δD j ω)
              + (N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range (τ ω), (c (τ ω) a j : ℝ))
              + (N : ℝ) ^ (-D)
              + ∑ j ∈ range (τ ω), (1 + (1 - u (τ ω))⁻¹) ^ n * stepErr j := by
  filter_upwards [grid_assembly_stopped_pathwise (μ := μ) (ℱ := ℱ) n hε D D₁ C_L C_P C_K hCK0
    hCK] with N hN
  intro K L _ hK1 hK hL ξ u τ Δ Kd sz A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hΔ hKΔ hP0
    hP hv hw hτmeas hZmeas hqv h hτK
  obtain ⟨G, hG, hbd⟩ := hN K L hK1 hK hL ξ u τ Δ Kd sz A0 A Dr Z Y R κ εK δ0 dDrift δD c v w
    stepErr P hΔ hKΔ hP0 hP hv hw hτmeas hZmeas hqv h
  exact ⟨G, hG, fun ω hω hτ a => hbd ω hω hτ (τ ω) (hτK ω) a⟩

end Budget

/-! ### (T5) Nondegenerate witnesses on the grid space -/

section Witness

variable (d : Dims)

variable {d}

end Witness

/-! #### The two concrete witnesses: the kernel hypothesis is (7.16) itself -/

section WitnessConcrete

variable {d : Dims}

end WitnessConcrete

section NonVacuity

variable {d : Dims}

end NonVacuity

/-! ### Producers of `hker′` from (7.16), and the n = 3 case -/

section Producers

/-- **`hker′` is produced by (7.16) Case 1** (`Q716.uker_decay_le_nonAlt`) for any cyclically
non-alternating charge, on any monotone grid in `[0,1)`, with `κ_{i,k} = cKerShort·Kd^n
((1-u_i)ℓ_{u_i}/((1-u_k)ℓ_{u_k}))^n` and `ε_{i,k} = ((1-u_i)/(1-u_k))^n`. -/
theorem hker_of_Q716_nonAlt (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} [NeZero n] {E : ℝ}
    (hE : |E| < 2) {σ : Fin n → Bool} {k0 : Fin n} (hk0 : σ k0 = σ (k0 + 1)) {u : ℕ → ℝ} {K : ℕ}
    (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i k, i ≤ k → k ≤ K → u i ≤ u k)
    (hu1 : ∀ i ≤ K, u i < 1) {Kd : ℝ} (hKd : 1 ≤ Kd) :
    ∀ i k, i ≤ k → k ≤ K → ∀ (X : LoopArg L n → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → KerClass L u Kd false δ i X →
      ∀ a, ‖Uker L (xiOf (mSigma E) σ) (u i : ℂ) (u k : ℂ) X a‖
        ≤ (cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n
            * ((1 - u i) * ellHat L ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat L ((u k : ℝ) : ℂ))) ^ n)
            * M + ((1 - u i) / (1 - u k)) ^ n * δ := by
  intro i k hik hk X M δ hM hδ hX hc a
  exact Q716.uker_decay_le_nonAlt L hL hE hk0 (hu0 i (hik.trans hk)) (hmono i k hik hk) (hu1 k hk)
    hKd hM hδ hX hc.1 a

/-- **`hker′` (Case 2 class) is produced by (7.16) Case 2** (`Q716.uker_decay_le_sumZero`), for
any charge and `n ≥ 2`. -/
theorem hker_of_Q716_sumZero (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {E : ℝ} (hE : |E| < 2) (σ : Fin n → Bool) {u : ℕ → ℝ} {K : ℕ}
    (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i k, i ≤ k → k ≤ K → u i ≤ u k)
    (hu1 : ∀ i ≤ K, u i < 1) {Kd : ℝ} (hKd : 1 ≤ Kd) :
    ∀ i k, i ≤ k → k ≤ K → ∀ (X : LoopArg L n → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → KerClass L u Kd true δ i X →
      ∀ a, ‖Uker L (xiOf (mSigma E) σ) (u i : ℂ) (u k : ℂ) X a‖
        ≤ (cKerSumZero n * Kd ^ (2 * n)
            * ((1 - u i) * ellHat L ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat L ((u k : ℝ) : ℂ))) ^ n)
            * M + (cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - u i) / (1 - u k)) ^ n) * δ := by
  intro i k hik hk X M δ hM hδ hX hc a
  exact Q716.uker_decay_le_sumZero L hn hL hE σ (hu0 i (hik.trans hk)) (hmono i k hik hk)
    (hu0 k hk) (hu1 k hk) hKd hM hδ hX hc.1 (hc.2 rfl) a

end Producers

end RBM.Gauss.Grid

end

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseProc
import RBM1D.Flow.GUEPhaseDuhamel
import RBM1D.Flow.GUEPhaseMarkov
import RBM1D.Hierarchy.GUEPhaseG
import RBM1D.Flow.EnergyUniform

/-!
# (7.45)G and (7.46)G for the frozen, interpolated GUE-phase processes

The two hypotheses `h745` of
`GUEPhase.eq727GE` (even lengths `2 ≤ m ≤ 2n₀`) and `h746` of `GUEPhase.eq728G`
(`1 ≤ n ≤ n₀`) for the frozen, tent-interpolated processes `gueLproc`, `gueDproc` of
`Flow/GUEPhaseProc.lean`, uniformly over the whole interval `[t₁, t₀]`.

Route:
* a good event, the finite intersection of: the step-`0` input (`hB.LmK`, transferred by
  `map_gueH_zero`), the unstopped loop-Duhamel martingale bound `gueGrid_loop_duhamel`,
  and, for `h745`, the entry bound `gueGrid_entry_bound` with `δ = N^{-τU/4}`;
* on it, pathwise, the discrete Duhamel formula at every grid time `k ≤ σ` (`σ = gueStop`),
  with the bilinear term (`primRhsGUE_sub`, `norm_primBilGUE_le`), the `E^{(G)}` term
  (`norm_eGtermGUE_le`, with `ε ≤ ‖G - m‖_max` + the entry bound + A3 + `L_{2l+1} ≤ √L₂ L_{2l}`
  for `h745`, `ε ≤ D₁` for `h746`), and the deterministic discretization error of `K̃`;
* off the grid, the exact linear interpolation of the affine prefactor `u_k - t₁` and the
  concavity of `√·` (no jump comparison is needed).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.Gauss.GUEGrid

/-! ### Real-analysis helpers (private) -/

section GueHypReal

/-- Concavity of `√·` on two points. -/
private theorem gueHyp_sqrt_convex {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (1 - θ) * Real.sqrt a + θ * Real.sqrt b ≤ Real.sqrt ((1 - θ) * a + θ * b) := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have h0a := Real.sqrt_nonneg a
  have h0b := Real.sqrt_nonneg b
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have hkey : 0 ≤ θ * (1 - θ) * (Real.sqrt a - Real.sqrt b) ^ 2 :=
    mul_nonneg (mul_nonneg hθ0 (by linarith)) (sq_nonneg _)
  nlinarith [hkey]

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}

private theorem gueHyp_step_nonneg (ht10 : t1 N ≤ t0 N) : 0 ≤ Grid.step t1 t0 K N :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

private theorem gueHyp_time_mono (ht10 : t1 N ≤ t0 N) {i j : ℕ} (hij : i ≤ j) :
    Grid.time t1 t0 K N i ≤ Grid.time t1 t0 K N j := by
  unfold Grid.time
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith [gueHyp_step_nonneg (K := K) ht10]

private theorem gueHyp_time_sub (k : ℕ) :
    Grid.time t1 t0 K N k - t1 N = (k : ℝ) * Grid.step t1 t0 K N := by
  unfold Grid.time; ring

private theorem gueHyp_time_ge (ht10 : t1 N ≤ t0 N) (k : ℕ) : t1 N ≤ Grid.time t1 t0 K N k := by
  have := gueHyp_time_mono (K := K) ht10 (Nat.zero_le k)
  rwa [Grid.time_zero] at this

private theorem gueHyp_time_le (ht10 : t1 N ≤ t0 N) (hK : K N ≠ 0) {k : ℕ} (hk : k ≤ K N) :
    Grid.time t1 t0 K N k ≤ t0 N := by
  have := gueHyp_time_mono (K := K) ht10 hk
  rwa [Grid.time_last t1 t0 K N hK] at this

private theorem gueHyp_time_mem (ht10 : t1 N ≤ t0 N) (hK : K N ≠ 0) {k : ℕ} (hk : k ≤ K N) :
    Grid.time t1 t0 K N k ∈ Set.Icc (t1 N) (t0 N) :=
  ⟨gueHyp_time_ge ht10 k, gueHyp_time_le ht10 hK hk⟩

/-- The tent weights at a point of `[u_k, u_{k+1}]`. -/
private theorem gueHyp_tent_eq (hΔ : 0 < Grid.step t1 t0 K N) {k : ℕ} {t : ℝ}
    (h1 : Grid.time t1 t0 K N k ≤ t) (h2 : t ≤ Grid.time t1 t0 K N (k + 1)) (j : ℕ) :
    gueTent t1 t0 K N j t =
      if j = k then 1 - (t - Grid.time t1 t0 K N k) / Grid.step t1 t0 K N
      else if j = k + 1 then (t - Grid.time t1 t0 K N k) / Grid.step t1 t0 K N else 0 := by
  set Δ := Grid.step t1 t0 K N with hΔdef
  set θ := (t - Grid.time t1 t0 K N k) / Δ with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hΔ.le
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hΔ]
    have : Grid.time t1 t0 K N (k + 1) = Grid.time t1 t0 K N k + Δ := by
      unfold Grid.time; push_cast; ring
    linarith
  have hval : (t - Grid.time t1 t0 K N j) / Δ = θ + ((k : ℝ) - (j : ℝ)) := by
    rw [hθdef]; unfold Grid.time; rw [← hΔdef]; field_simp; ring
  have habs : |t - Grid.time t1 t0 K N j| / Δ = |θ + ((k : ℝ) - (j : ℝ))| := by
    rw [← hval, abs_div, abs_of_pos hΔ]
  show max 0 (1 - |t - Grid.time t1 t0 K N j| / Δ) = _
  rw [habs]
  by_cases hjk : j = k
  · subst hjk
    simp only [sub_self, add_zero, ite_true, abs_of_nonneg hθ0]
    exact max_eq_right (by linarith)
  · by_cases hjk1 : j = k + 1
    · subst hjk1
      simp only [hjk, ite_false, ite_true]
      push_cast
      rw [show θ + ((k : ℝ) - ((k : ℝ) + 1)) = θ - 1 by ring, abs_of_nonpos (by linarith)]
      rw [max_eq_right (by linarith)]
      ring
    · simp only [hjk, hjk1, ite_false]
      apply max_eq_left
      rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
      · have : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (k : ℝ) + 2 ≤ (j : ℝ) := by
          have : k + 2 ≤ j := by omega
          exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]; linarith

/-- On `[u_k, u_{k+1}]`, `k < K`, the interpolation is `(1-θ) f_k + θ f_{k+1}`. -/
private theorem gueHyp_interp_eq (f : ℕ → ℝ) (hΔ : 0 < Grid.step t1 t0 K N) {k : ℕ}
    (hk : k < K N) {t : ℝ} (h1 : Grid.time t1 t0 K N k ≤ t)
    (h2 : t ≤ Grid.time t1 t0 K N (k + 1)) :
    gueInterp t1 t0 K N f t =
      (1 - (t - Grid.time t1 t0 K N k) / Grid.step t1 t0 K N) * f k +
        (t - Grid.time t1 t0 K N k) / Grid.step t1 t0 K N * f (k + 1) := by
  unfold gueInterp
  simp only [hΔ.ne', ite_false]
  simp_rw [gueHyp_tent_eq hΔ h1 h2]
  rw [Finset.sum_eq_add_of_mem k (k + 1) (Finset.mem_range.2 (by omega))
    (Finset.mem_range.2 (by omega)) (by omega)]
  · simp only [ite_true, show k + 1 ≠ k by omega, ite_false]
    ring
  · intro c _ hc
    simp [hc.1, hc.2]

/-- For `t ∈ [t₁, t₀]` and `Δ > 0` there is a grid cell `[u_k, u_{k+1}]`, `k < K`, containing
`t`. -/
private theorem gueHyp_exists_cell (hΔ : 0 < Grid.step t1 t0 K N) (hK : K N ≠ 0) {t : ℝ}
    (ht : t ∈ Set.Icc (t1 N) (t0 N)) :
    ∃ k : ℕ, k < K N ∧ Grid.time t1 t0 K N k ≤ t ∧ t ≤ Grid.time t1 t0 K N (k + 1) := by
  set Δ := Grid.step t1 t0 K N with hΔdef
  set s := (t - t1 N) / Δ with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hΔ.le
  have hts : t = t1 N + s * Δ := by rw [hsdef]; field_simp; ring
  refine ⟨min ⌊s⌋₊ (K N - 1), by omega, ?_, ?_⟩
  · have h1 : ((min ⌊s⌋₊ (K N - 1) : ℕ) : ℝ) ≤ s :=
      le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le hs0)
    unfold Grid.time
    rw [← hΔdef]
    nlinarith
  · by_cases hc : ⌊s⌋₊ ≤ K N - 1
    · rw [min_eq_left hc]
      have h2 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
      unfold Grid.time
      rw [← hΔdef]
      push_cast
      nlinarith
    · rw [min_eq_right (by omega), show K N - 1 + 1 = K N by omega,
        Grid.time_last t1 t0 K N hK]
      exact ht.2

/-- **Interpolation of a grid bound with an affine and a square-root prefactor.** If the grid
values `f k`, `k ≤ σ`, obey `f k ≤ P + Q λ(u_k) + A (u_k - t₁) + B √(u_k - t₁)` whenever all
earlier grid times are `≤ t`, then the frozen interpolant at `t` obeys the same bound with
`u_k` replaced by `t` (and `λ(u_k)` by `C λ(t)`). -/
private theorem gueHyp_interp_bound (f : ℕ → ℝ) {σ : ℕ} (hσ : σ ≤ K N) (hK : K N ≠ 0)
    (ht10 : t1 N ≤ t0 N) {t : ℝ} (ht : t ∈ Set.Icc (t1 N) (t0 N)) (lam : ℝ → ℝ)
    {P Q A B C : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlam : ∀ k ≤ K N, Grid.time t1 t0 K N k ≤ t + Grid.step t1 t0 K N →
      lam (Grid.time t1 t0 K N k) ≤ C * lam t)
    (hgrid : ∀ k ≤ σ, (∀ j < k, Grid.time t1 t0 K N j ≤ t) →
      f k ≤ P + Q * lam (Grid.time t1 t0 K N k) + A * (Grid.time t1 t0 K N k - t1 N)
        + B * Real.sqrt (Grid.time t1 t0 K N k - t1 N)) :
    gueInterp t1 t0 K N (fun k => f (min k σ)) t ≤
      P + Q * (C * lam t) + A * (t - t1 N) + B * Real.sqrt (t - t1 N) := by
  have hΔ0 := gueHyp_step_nonneg (K := K) ht10
  rcases hΔ0.lt_or_eq with hΔ | hΔ
  · obtain ⟨k, hkK, hk1, hk2⟩ := gueHyp_exists_cell hΔ hK ht
    rw [gueHyp_interp_eq _ hΔ hkK hk1 hk2]
    set Δ := Grid.step t1 t0 K N with hΔdef
    set θ := (t - Grid.time t1 t0 K N k) / Δ with hθdef
    have hsucc : Grid.time t1 t0 K N (k + 1) = Grid.time t1 t0 K N k + Δ := by
      unfold Grid.time; rw [← hΔdef]; push_cast; ring
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hΔ.le
    have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hΔ]; linarith
    have hge := gueHyp_time_ge (K := K) ht10 k
    by_cases hσk : σ ≤ k
    · simp only [min_eq_right hσk, min_eq_right (le_trans hσk (Nat.le_succ k))]
      have hσt : Grid.time t1 t0 K N σ ≤ t := le_trans (gueHyp_time_mono ht10 hσk) hk1
      have hf := hgrid σ le_rfl fun j hj =>
        le_trans (gueHyp_time_mono ht10 (le_of_lt (lt_of_lt_of_le hj hσk))) hk1
      have hl := hlam σ hσ (by linarith)
      have hgeσ := gueHyp_time_ge (K := K) ht10 σ
      have hsq : Real.sqrt (Grid.time t1 t0 K N σ - t1 N) ≤ Real.sqrt (t - t1 N) :=
        Real.sqrt_le_sqrt (by linarith)
      have e1 : Q * lam (Grid.time t1 t0 K N σ) ≤ Q * (C * lam t) :=
        mul_le_mul_of_nonneg_left hl hQ
      have e2 : A * (Grid.time t1 t0 K N σ - t1 N) ≤ A * (t - t1 N) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      have e3 := mul_le_mul_of_nonneg_left hsq hB
      linarith
    · push Not at hσk
      simp only [min_eq_left hσk.le, min_eq_left (Nat.succ_le_of_lt hσk)]
      have hfk := hgrid k hσk.le fun j hj => le_trans (gueHyp_time_mono ht10 hj.le) hk1
      have hfk1 := hgrid (k + 1) (Nat.succ_le_of_lt hσk) fun j hj =>
        le_trans (gueHyp_time_mono ht10 (Nat.lt_succ_iff.1 hj)) hk1
      have hlk := hlam k hkK.le (by linarith)
      have hlk1 := hlam (k + 1) hkK (by linarith)
      have hsq := gueHyp_sqrt_convex (a := Grid.time t1 t0 K N k - t1 N)
        (b := Grid.time t1 t0 K N (k + 1) - t1 N) (by linarith) (by linarith) hθ0 hθ1
      have hθΔ : θ * Δ = t - Grid.time t1 t0 K N k := by rw [hθdef]; field_simp
      have haff : (1 - θ) * (Grid.time t1 t0 K N k - t1 N) +
          θ * (Grid.time t1 t0 K N (k + 1) - t1 N) = t - t1 N := by
        rw [hsucc]; linear_combination hθΔ
      rw [haff] at hsq
      have h1θ : 0 ≤ 1 - θ := by linarith
      have a1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlk hQ) h1θ
      have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlk1 hQ) hθ0
      have eS := mul_le_mul_of_nonneg_left hsq hB
      have c1 := mul_le_mul_of_nonneg_left hfk h1θ
      have c2 := mul_le_mul_of_nonneg_left hfk1 hθ0
      have eA : (1 - θ) * (A * (Grid.time t1 t0 K N k - t1 N)) +
          θ * (A * (Grid.time t1 t0 K N (k + 1) - t1 N)) = A * (t - t1 N) := by
        rw [← haff]; ring
      have eB : (1 - θ) * (B * Real.sqrt (Grid.time t1 t0 K N k - t1 N)) +
          θ * (B * Real.sqrt (Grid.time t1 t0 K N (k + 1) - t1 N)) =
          B * ((1 - θ) * Real.sqrt (Grid.time t1 t0 K N k - t1 N) +
            θ * Real.sqrt (Grid.time t1 t0 K N (k + 1) - t1 N)) := by ring
      have eQ : (1 - θ) * (Q * (C * lam t)) + θ * (Q * (C * lam t)) = Q * (C * lam t) := by ring
      have eP : (1 - θ) * P + θ * P = P := by ring
      nlinarith
  · -- `Δ = 0`: the interval is a point
    have hstep0 : Grid.step t1 t0 K N = 0 := hΔ.symm
    have ht10' : t0 N = t1 N := by
      have hKR : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
      have := hstep0
      unfold Grid.step at this
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · linarith
      · exact absurd h hKR
    have htt1 : t = t1 N := le_antisymm (ht10' ▸ ht.2) ht.1
    unfold gueInterp
    simp only [hstep0, ite_true, Nat.zero_min]
    have hf := hgrid 0 (Nat.zero_le _) fun j hj => absurd hj (Nat.not_lt_zero j)
    have hl := hlam 0 (Nat.zero_le _) (by rw [Grid.time_zero, hstep0, htt1]; linarith)
    rw [Grid.time_zero, sub_self, Real.sqrt_zero, mul_zero, mul_zero, add_zero,
      add_zero] at hf
    rw [Grid.time_zero] at hl
    rw [htt1, sub_self, Real.sqrt_zero, mul_zero, mul_zero, add_zero, add_zero]
    rw [htt1] at hl
    nlinarith [mul_le_mul_of_nonneg_left hl hQ]

end GueHypReal

/-! ### Loop-level helpers (private) -/

section GueHypLoop

/-- Products of measurable matrix-valued maps are measurable. -/
private theorem gueHyp_meas_mul {α n : Type*} [MeasurableSpace α] [Fintype n]
    {A B : α → Matrix n n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x => A x * B x) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

/-- `M ↦ gloop(M, z, I)` is measurable. -/
private theorem gueHyp_meas_gloop {L W : ℕ} [NeZero L] [NeZero W] (z : ℂ)
    (I : LoopIdx (ZMod L)) :
    Measurable fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ => gloop L W M z I := by
  have hG : ∀ s : Bool, Measurable fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ =>
      Gsig M z s := fun s =>
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => by
      simp only [Gsig]
      exact gueEntry_meas_green _ i j
  have hlist : ∀ l : List (Bool × ZMod L),
      Measurable fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ =>
        l.foldr (fun p A => Gsig M z p.1 * Eblk L W p.2 * A) 1 := by
    intro l
    induction l with
    | nil => exact measurable_const
    | cons p l ih =>
      simp only [List.foldr_cons]
      exact gueHyp_meas_mul (gueHyp_meas_mul (hG p.1) measurable_const) ih
  unfold gloop Matrix.trace
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp (hlist _))

/-- Every well-formed loop index is the index of a `LoopData` (private copy of the pattern of
`Hierarchy/DriftBound.lean`'s `exists_loopData`, which is not in this file's import closure). -/
private theorem gueHyp_exists_loopData {L : ℕ} (J : LoopIdx (ZMod L)) (hJ : J.WF) :
    ∃ y : LoopData L J.length, y.idx = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [LoopIdx.length]
  refine ⟨(fun i => σ.get (Fin.cast hJ.symm i), fun i => a.get i), ?_⟩
  have hσ' : List.ofFn (fun i : Fin a.length => σ.get (Fin.cast hJ.symm i)) = σ := by
    apply List.ext_get <;> simp [hJ]
  have ha' : List.ofFn (fun i : Fin a.length => a.get i) = a := List.ofFn_get a
  simp only [LoopData.idx, hσ', ha']

/-- `∑_p |(E_a)_{pp}| = 1`: the diagonal of `E_a = W⁻¹ 1_{block a}` sums to one. -/
private theorem gueHyp_sum_Eblk_diag {L W : ℕ} [NeZero L] [NeZero W] (a : ZMod L) :
    ∑ p : ZMod L × Fin W, (if p.1 = a then ((W : ℂ))⁻¹ else 0) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_eq_single a]
  · simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
    field_simp
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ a) h

private theorem gueHyp_trace_mul_Eblk {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a : ZMod L) :
    Matrix.trace (M * Eblk L W a) =
      ∑ p : ZMod L × Fin W, M p p * (if p.1 = a then ((W : ℂ))⁻¹ else 0) := by
  unfold Eblk Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_diagonal]

/-- `|⟨M E_a⟩| ≤ max_p |M_{pp}|`. -/
private theorem gueHyp_norm_trace_Eblk_le {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a : ZMod L) {c : ℝ}
    (hc : ∀ p, ‖M p p‖ ≤ c) : ‖Matrix.trace (M * Eblk L W a)‖ ≤ c := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (0, ⟨0, Nat.pos_of_ne_zero (NeZero.ne W)⟩))
  rw [gueHyp_trace_mul_Eblk]
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  calc ‖∑ p : ZMod L × Fin W, M p p * (if p.1 = a then ((W : ℂ))⁻¹ else 0)‖
      ≤ ∑ p : ZMod L × Fin W, ‖M p p * (if p.1 = a then ((W : ℂ))⁻¹ else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p : ZMod L × Fin W, c * (if p.1 = a then ((W : ℝ))⁻¹ else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul]
        by_cases hp : p.1 = a
        · simp only [hp, ite_true, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_right (hc p) (by positivity)
        · simp [hp]
    _ = c := by
        rw [← Finset.mul_sum]
        have h1 : ∑ p : ZMod L × Fin W, (if p.1 = a then ((W : ℝ))⁻¹ else 0) = 1 := by
          have := gueHyp_sum_Eblk_diag (L := L) (W := W) a
          have h2 : ((∑ p : ZMod L × Fin W, (if p.1 = a then ((W : ℝ))⁻¹ else 0) : ℝ) : ℂ)
              = 1 := by
            rw [← this, Complex.ofReal_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            split_ifs <;> simp
          exact_mod_cast h2
        rw [h1, mul_one]

/-- `⟨E_a⟩ = 1`. -/
private theorem gueHyp_trace_Eblk {L W : ℕ} [NeZero L] [NeZero W] (a : ZMod L) :
    Matrix.trace (Eblk L W a) = 1 := by
  have := gueHyp_trace_mul_Eblk (L := L) (W := W) 1 a
  rw [Matrix.one_mul] at this
  rw [this, ← gueHyp_sum_Eblk_diag (L := L) (W := W) a]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

/-- **`ε ≤ ‖G - m‖_max`**: the `E^{(G)}` weight `⟨(G_σ - m_σ) E_a⟩` is a block average of the
diagonal of `G - m` (for `σ = -`, of its complex conjugate). -/
private theorem gueHyp_eps_le_dev {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) (E : ℝ) (z : ℂ)
    {c : ℝ} (hc : ∀ p, ‖(green H z - mE E • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      p p‖ ≤ c) (σ : Bool) (a : ZMod L) :
    ‖Matrix.trace ((Gsig H z σ - mSigma E σ •
      (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)‖ ≤ c := by
  refine gueHyp_norm_trace_Eblk_le _ a fun p => ?_
  cases σ
  · have hconj : Gsig H z false = Matrix.conjTranspose (Gsig H z true) :=
      (Gsig_conjTranspose hH z true).symm
    have e : (Gsig H z false - mSigma E false •
        (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) p p =
        star ((green H z - mE E • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) p p) := by
      rw [hconj]
      simp [mSigma, Matrix.sub_apply, Matrix.conjTranspose_apply]
    rw [e, norm_star]
    exact hc p
  · simpa [mSigma] using hc p

/-- `⟨(G_σ - m_σ) E_a⟩ = L_{(σ),(a)} - m_σ`. -/
private theorem gueHyp_trace_eq_gloop_one {L W : ℕ} [NeZero L] [NeZero W]
    (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (m : Bool → ℂ) (σ : Bool)
    (a : ZMod L) :
    Matrix.trace ((Gsig H z σ - m σ •
      (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a) =
      gloop L W H z ⟨[σ], [a]⟩ - m σ := by
  have hg : gloop L W H z ⟨[σ], [a]⟩ = Matrix.trace (Gsig H z σ * Eblk L W a) := by
    simp [gloop, gloopProd_cons, gloopProd_nil]
  rw [hg, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, gueHyp_trace_Eblk, smul_eq_mul, mul_one]

/-- An `(n+1)`-loop obtained by cutting and gluing is bounded by `L^{(n+1)}`. -/
private theorem gueHyp_cutGlue_le {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {I : LoopIdx (ZMod L)}
    (hI : I.WF) {k : ℕ} (hk : k ∈ Finset.Icc 1 I.length) (b : ZMod L) :
    ‖gloop L W H z (I.cutGlue k b)‖ ≤ loopMax L W H z (I.length + 1) := by
  rw [Finset.mem_Icc] at hk
  have hwf := LoopIdx.WF.cutGlue b hI hk.1 hk.2
  have hlen := LoopIdx.length_cutGlue I b hk.2
  exact norm_gloop_le_loopMax _ (by rw [hwf]; exact hlen) hlen

end GueHypLoop

/-! ### The deterministic `K̃` (rows K1, R2; private) -/

section GueHypKt

/-- Nonnegativity of the deterministic `K̃` scale (private copy of a helper of
`Flow/GUEPhaseProc.lean`). -/
private theorem gueHyp_pow_nonneg (W : ℕ) (e : ℝ) (L : ℕ) (t : ℝ) (ht1 : t < 1) (k : ℕ) :
    (0 : ℝ) ≤ ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ k := by
  have hetaT_nonneg : 0 ≤ etaT e t := by
    unfold etaT
    have h2 : 0 ≤ (mE e).im := by rw [mE_im]; positivity
    nlinarith
  have hellHat_nonneg : 0 ≤ ellHat L (t : ℂ) := by rw [ellHat_ofReal L ht1]; positivity
  have hX_nonneg : 0 ≤ (W : ℝ) * (etaT e t * ellHat L (t : ℂ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hetaT_nonneg hellHat_nonneg)
  exact pow_nonneg (inv_nonneg.2 hX_nonneg) _

/-- A uniform-in-length constant for `norm_Kgen_le_unif`, `1 ≤ n ≤ Nmax` (private copy of
`Flow/GUEPhaseProc.lean`'s helper of the same content). -/
private theorem gueHyp_uniform_C_Kgen {κ : ℝ} (hκ : 0 < κ) (Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n → n ≤ Nmax → ∀ e : ℝ, |e| ≤ 2 - κ → ∀ (L : ℕ) [NeZero L],
      3 ≤ L → ∀ (W : ℕ) [NeZero W], ∀ t : ℝ, 0 < t → t < 1 → ∀ I : LoopIdx (ZMod L), I.WF →
        I.length = n →
        ‖Kgen L W (mSigma e) t I‖ ≤ C * ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ (n - 1) := by
  have hk0 : 0 < min κ 1 := lt_min hκ (by norm_num)
  have hk1 : min κ 1 ≤ 1 := min_le_right _ _
  induction Nmax with
  | zero => exact ⟨0, le_rfl, fun n hn1 hn0 => by omega⟩
  | succ M ih =>
    obtain ⟨C1, hC10, h1⟩ := ih
    obtain ⟨C2, hC20, h2⟩ := norm_Kgen_le_unif hk0 hk1 (M + 1) (by omega)
    refine ⟨C1 + C2, by positivity, fun n hn1 hnM e hE L _ hL W _ t ht0' ht1' I hI hlen => ?_⟩
    have hE'' : |e| ≤ 2 - min κ 1 := by have := min_le_left κ 1; linarith
    rcases Nat.lt_or_ge n (M + 1) with hlt | hge
    · have hb := h1 n hn1 (by omega) e hE L hL W t ht0' ht1' I hI hlen
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_right _ (gueHyp_pow_nonneg W e L t ht1' (n - 1))
      linarith
    · obtain rfl : n = M + 1 := by omega
      have hb := h2 e hE'' L hL W t ht0' ht1' I hI hlen
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_right _ (gueHyp_pow_nonneg W e L t ht1' (M + 1 - 1))
      linarith

variable (d : Dims)

/-- **Row K1**: `‖K̃_t(J)‖ ≺ (S η_t)^{-|J|+1}`, uniformly in `t ∈ [t₁, t₀]` and the
well-formed loops `2 ≤ |J| ≤ 2n₀` (`eq736_detDom` with `λ = S η`; the argument of
`Flow/GUEPhaseProc.lean`'s `gueKproc_unifDetDom`, before interpolation). -/
private theorem gueHyp_Kt_detDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (h730 : ∀ᶠ N : ℕ in atTop, t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N))
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t) :
    UnifDetDom (fun N (p : TimeIcc t1 t0 N × GUEPhase.LoopSet (d.L N) (2 * n0)) =>
        ‖Kt N p.1 p.2.1‖)
      (fun N p => (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) p.1)⁻¹ ^ ((p.2.1).length - 1)) := by
  set lam : ℕ → ℝ → ℝ := fun N t => ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t with hlamdef
  have hlam_pos : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < lam N t := by
    intro N t ht
    have h1 : t < 1 := lt_of_le_of_lt ht.2 (ht0 N)
    have h2 : |E N| < 2 := lt_of_le_of_lt (hE N) (by linarith)
    have h3 : 0 < (mE (E N)).im := mE_im_pos h2
    have h4 : (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := by
      have hW := d.W_pos N; have hL := d.three_le_L N
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    have h5 : (0 : ℝ) < 1 - t := by linarith
    rw [hlamdef]
    show 0 < ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t
    unfold etaT
    positivity
  have hlam_anti : ∀ N, ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t →
      lam N t ≤ lam N u := by
    intro N u _hu t _ht hut
    rw [hlamdef]
    show ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t ≤ ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u
    unfold etaT
    have hM : (0 : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (mE (E N)).im := by rw [mE_im]; positivity
    have hMim : 0 ≤ ((d.L N * d.W N : ℕ) : ℝ) * (mE (E N)).im := mul_nonneg hM h2
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 - t) ≤ (1 - u)) hMim]
  have hlam_cont : ∀ N, ContinuousOn (lam N) (Set.Icc (t1 N) (t0 N)) := by
    intro N
    have heq : lam N = fun t => ((d.L N * d.W N : ℕ) : ℝ) * ((1 - t) * (mE (E N)).im) := by
      funext t; rw [hlamdef]; unfold etaT; ring
    rw [heq]
    fun_prop
  have h732 : UnifDetDom (fun N (I : GUEPhase.LoopSet (d.L N) (2 * n0)) => ‖Kt N (t1 N) I.1‖)
      (fun N I => (lam N (t1 N))⁻¹ ^ (I.1.length - 1)) := by
    obtain ⟨C, hC0, hC⟩ := gueHyp_uniform_C_Kgen hκ (2 * n0)
    apply UnifDetDom.of_eventually_le_const_mul
      (fun N I => pow_nonneg (inv_nonneg.2
        (hlam_pos N (t1 N) ⟨le_refl _, ht10 N⟩).le) _) C
    filter_upwards [hell] with N hellN I
    have hL3 := d.three_le_L N
    have ht1lt1 : t1 N < 1 := lt_of_le_of_lt (ht10 N) (ht0 N)
    have ht1pos : 0 < t1 N := by
      have hLR : (3 : ℝ) ≤ (d.L N : ℝ) := by exact_mod_cast hL3
      nlinarith [hellN]
    obtain ⟨hIWF, hI2, hI2n0⟩ := I.2
    have hKeq : Kt N (t1 N) I.1 = Kgen (d.L N) (d.W N) (mSigma (E N)) (t1 N) I.1 := hKinit N I.1
    rw [hKeq]
    have hbound := hC I.1.length (by omega) hI2n0 (E N) (hE N) (d.L N) hL3 (d.W N) (t1 N)
      ht1pos ht1lt1 I.1 hIWF rfl
    have hellHatL : ellHat (d.L N) (t1 N : ℂ) = (d.L N : ℝ) :=
      GUEPhase.ellHat_eq_L ht1lt1 hellN
    rw [hellHatL] at hbound
    have hXeq : (d.W N : ℝ) * (etaT (E N) (t1 N) * (d.L N : ℝ)) = lam N (t1 N) := by
      rw [hlamdef]; push_cast; ring
    rw [hXeq] at hbound
    exact hbound
  have hetaAnti : ∀ e : ℝ, ∀ u t : ℝ, u ≤ t → etaT e t ≤ etaT e u := by
    intro e u t hut
    unfold etaT
    have h2 : 0 ≤ (mE e).im := by rw [mE_im]; positivity
    nlinarith
  have h730' : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      ((d.W N * d.L N : ℕ) : ℝ) * (t - t1 N) ≤ (N : ℝ) ^ (-τU) * lam N t := by
    filter_upwards [h730] with N h730N t ht
    have h1 : t - t1 N ≤ t0 N - t1 N := by linarith [ht.2]
    have h2 : etaT (E N) (t0 N) ≤ etaT (E N) t := hetaAnti (E N) t (t0 N) ht.2
    have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (-τU) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h3 : t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) t :=
      le_trans h730N (mul_le_mul_of_nonneg_left h2 hNpow)
    have h4 : t - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) t := le_trans h1 h3
    have hWL : (0 : ℝ) ≤ ((d.W N * d.L N : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((d.W N * d.L N : ℕ) : ℝ) * (t - t1 N)
        ≤ ((d.W N * d.L N : ℕ) : ℝ) * ((N : ℝ) ^ (-τU) * etaT (E N) t) :=
          mul_le_mul_of_nonneg_left h4 hWL
      _ = (N : ℝ) ^ (-τU) * lam N t := by rw [hlamdef]; push_cast; ring
  exact GUEPhase.eq736_detDom d.L d.W Kt (2 * n0) t1 t0 ht10 lam hlam_pos hlam_anti
    hlam_cont (fun N t ht I hWF h2 hlen => hK N t ht I hWF (by omega) (by omega)) hτU h730' h732

/-- `F = primRhsGUE` vanishes on loops of length `1`. -/
private theorem gueHyp_primRhs_one {L W : ℕ} [NeZero L] (K : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hI : I.length = 1) : GUEPhase.primRhsGUE L W K I = 0 := by
  unfold GUEPhase.primRhsGUE GUEPhase.primBilGUE
  rw [hI]
  simp

/-- At length `1`, `K̃_t = m_σ` on `[t₁, t₀]` (the primitive equation has zero right side). -/
private theorem gueHyp_Kt_one {E t1 t0 : ℕ → ℝ} (n0 : ℕ) (hn0 : 1 ≤ n0)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (t1 N) (t0 N)) (s : Bool) (a : ZMod (d.L N)) :
    Kt N u ⟨[s], [a]⟩ = mSigma (E N) s := by
  have hI : (⟨[s], [a]⟩ : LoopIdx (ZMod (d.L N))).length = 1 := rfl
  have hWF : (⟨[s], [a]⟩ : LoopIdx (ZMod (d.L N))).WF := rfl
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r => Kt N r ⟨[s], [a]⟩)
    (f' := fun r => GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N r) ⟨[s], [a]⟩) (C := 0)
    (fun r hr => hK N r hr _ hWF (by rw [hI]) (by rw [hI]; omega))
    (fun r _ => by rw [gueHyp_primRhs_one _ _ hI, norm_zero]) u hu
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hmvt
  rw [hmvt, hKinit]
  show Kgen (d.L N) (d.W N) (mSigma (E N)) (t1 N) ⟨[s], [a]⟩ = mSigma (E N) s
  exact Kgen_one _ _ _ _ _

/-- `n² S ∑_{j=2}^n x ≤ M³ S x` for `n ≤ M`, `x ≥ 0`. -/
private theorem gueHyp_card_bound {n M : ℕ} (hnM : n ≤ M) {S x : ℝ} (hS : 0 ≤ S) (hx : 0 ≤ x) :
    (n : ℝ) ^ 2 * S * ∑ _j ∈ Finset.Icc 2 n, x ≤ (M : ℝ) ^ 3 * S * x := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have h1 : ((n + 1 - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n + 1 - 2 ≤ n)
  have h2 : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h3 : (n : ℝ) ^ 2 * ((n + 1 - 2 : ℕ) : ℝ) ≤ (M : ℝ) ^ 3 := by
    calc (n : ℝ) ^ 2 * ((n + 1 - 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 * n :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (n : ℝ) ^ 3 := by ring
      _ ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ hn0 h2 3
  have := mul_le_mul_of_nonneg_right h3 (mul_nonneg hS hx)
  nlinarith [this]

/-- **Row R2, one step**: `‖K̃_v − K̃_u − (v−u) F(K̃_u)‖ ≤ 3 M⁶ S² (v−u)²` on a sub-interval
`[u, v]`, if `‖K̃‖ ≤ 1` on loops of length `2..M` and `M³ S (v−u) ≤ 1`. -/
private theorem gueHyp_Kt_step {L W : ℕ} [NeZero L] (Kt : ℝ → LoopIdx (ZMod L) → ℂ) {M : ℕ}
    {u v : ℝ} (huv : u ≤ v)
    (hK : ∀ t ∈ Set.Icc u v, ∀ I : LoopIdx (ZMod L), I.WF → 1 ≤ I.length → I.length ≤ M →
      HasDerivWithinAt (fun s => Kt s I) (GUEPhase.primRhsGUE L W (Kt t) I) (Set.Icc u v) t)
    (hbd : ∀ t ∈ Set.Icc u v, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ M →
      ‖Kt t J‖ ≤ 1)
    (hsmall : (M : ℝ) ^ 3 * ((W * L : ℕ) : ℝ) * (v - u) ≤ 1)
    (I : LoopIdx (ZMod L)) (hI : I.WF) (hI1 : 1 ≤ I.length) (hIM : I.length ≤ M) :
    ‖Kt v I - Kt u I - ((v - u : ℝ) : ℂ) * GUEPhase.primRhsGUE L W (Kt u) I‖ ≤
      3 * (M : ℝ) ^ 6 * ((W * L : ℕ) : ℝ) ^ 2 * (v - u) ^ 2 := by
  set S : ℝ := ((W * L : ℕ) : ℝ) with hSdef
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have huv' : 0 ≤ v - u := by linarith
  -- step A: `‖K̃_r − K̃_u‖ ≤ M³ S (r − u)` on loops of length `2..M`
  have hA : ∀ r ∈ Set.Icc u v, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ M →
      ‖Kt r J - Kt u J‖ ≤ (M : ℝ) ^ 3 * S * (r - u) := by
    intro r hr J hJ hJ2 hJM
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => Kt s J) (f' := fun s => GUEPhase.primRhsGUE L W (Kt s) J)
      (C := (M : ℝ) ^ 3 * S)
      (fun s hs => hK s hs J hJ (by omega) hJM)
      (fun s hs => by
        have hs' : s ∈ Set.Icc u v := Set.Ico_subset_Icc_self hs
        have h := GUEPhase.norm_primRhsGUE_le L W (Kt s) (fun _ => 1) J hJ
          (fun J' hJ' h2 hJ'J => hbd s hs' J' hJ' h2 (hJ'J.trans hJM)) (fun _ => zero_le_one)
        refine h.trans ?_
        have := gueHyp_card_bound (n := J.length) (M := M) hJM hS zero_le_one
        simp only [mul_one] at this ⊢
        exact this) r hr
    simpa using hmvt
  -- step B: the derivative of `φ(r) = K̃_r − (r − u) F(K̃_u)` is `F(K̃_r) − F(K̃_u)`
  set e : ℝ := (M : ℝ) ^ 3 * S * (v - u) with hedef
  have he0 : 0 ≤ e := by positivity
  have hbil : ∀ r ∈ Set.Ico u v,
      ‖GUEPhase.primRhsGUE L W (Kt r) I - GUEPhase.primRhsGUE L W (Kt u) I‖ ≤
        3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) := by
    intro r hr
    have hr' : r ∈ Set.Icc u v := Set.Ico_subset_Icc_self hr
    have hu' : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
    rw [GUEPhase.primRhsGUE_sub]
    have hD : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖(Kt r - Kt u) J‖ ≤ e := by
      intro J hJ hJ2 hJI
      rw [Pi.sub_apply]
      refine (hA r hr' J hJ hJ2 (hJI.trans hIM)).trans ?_
      rw [hedef]
      exact mul_le_mul_of_nonneg_left (by linarith [hr'.2]) (by positivity)
    have hB1 : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖Kt u J‖ ≤ 1 := fun J hJ h2 hJI => hbd u hu' J hJ h2 (hJI.trans hIM)
    have b1 := GUEPhase.norm_primBilGUE_le L W (Kt u) (Kt r - Kt u) (fun _ => 1) (fun _ => e)
      I hI hB1 hD (fun _ => zero_le_one) (fun _ => he0)
    have b2 := GUEPhase.norm_primBilGUE_le L W (Kt r - Kt u) (Kt u) (fun _ => e) (fun _ => 1)
      I hI hD hB1 (fun _ => he0) (fun _ => zero_le_one)
    have b3 := GUEPhase.norm_primBilGUE_le L W (Kt r - Kt u) (Kt r - Kt u) (fun _ => e)
      (fun _ => e) I hI hD hD (fun _ => he0) (fun _ => he0)
    have c1 := gueHyp_card_bound (n := I.length) (M := M) hIM hS (x := 1 * e) (by positivity)
    have c2 := gueHyp_card_bound (n := I.length) (M := M) hIM hS (x := e * 1) (by positivity)
    have c3 := gueHyp_card_bound (n := I.length) (M := M) hIM hS (x := e * e) (by positivity)
    have hWL : ((W * L : ℕ) : ℝ) = S := rfl
    rw [hWL] at b1 b2 b3
    have he1 : e ≤ 1 := by rw [hedef]; linarith [hsmall]
    have hee : e * e ≤ e := by nlinarith
    have c3' : (M : ℝ) ^ 3 * S * (e * e) ≤ (M : ℝ) ^ 3 * S * e :=
      mul_le_mul_of_nonneg_left hee (by positivity)
    have hfin : (M : ℝ) ^ 3 * S * (1 * e) + (M : ℝ) ^ 3 * S * (e * 1) + (M : ℝ) ^ 3 * S * e
        = 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) := by rw [hedef]; ring
    calc ‖GUEPhase.primBilGUE L W (Kt u) (Kt r - Kt u) I +
            GUEPhase.primBilGUE L W (Kt r - Kt u) (Kt u) I +
            GUEPhase.primBilGUE L W (Kt r - Kt u) (Kt r - Kt u) I‖
        ≤ ‖GUEPhase.primBilGUE L W (Kt u) (Kt r - Kt u) I‖ +
            ‖GUEPhase.primBilGUE L W (Kt r - Kt u) (Kt u) I‖ +
            ‖GUEPhase.primBilGUE L W (Kt r - Kt u) (Kt r - Kt u) I‖ := norm_add₃_le
      _ ≤ (M : ℝ) ^ 3 * S * (1 * e) + (M : ℝ) ^ 3 * S * (e * 1) + (M : ℝ) ^ 3 * S * e := by
          gcongr
          · exact b1.trans c1
          · exact b2.trans c2
          · exact (b3.trans c3).trans c3'
      _ = 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) := hfin
  have hderiv : ∀ r ∈ Set.Icc u v, HasDerivWithinAt
      (fun s => Kt s I - ((s - u : ℝ) : ℂ) * GUEPhase.primRhsGUE L W (Kt u) I)
      (GUEPhase.primRhsGUE L W (Kt r) I - GUEPhase.primRhsGUE L W (Kt u) I) (Set.Icc u v) r := by
    intro r hr
    have h1 := hK r hr I hI hI1 hIM
    have h2 : HasDerivAt (fun s : ℝ => ((s - u : ℝ) : ℂ)) ((1 : ℝ) : ℂ) r :=
      ((hasDerivAt_id r).sub_const u).ofReal_comp
    have h3 := (h2.mul_const (GUEPhase.primRhsGUE L W (Kt u) I)).hasDerivWithinAt
      (s := Set.Icc u v)
    simp only [Complex.ofReal_one, one_mul] at h3
    exact h1.sub h3
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbil v ⟨huv, le_rfl⟩
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmvt
  calc ‖Kt v I - Kt u I - ((v - u : ℝ) : ℂ) * GUEPhase.primRhsGUE L W (Kt u) I‖
      = ‖Kt v I - ((v - u : ℝ) : ℂ) * GUEPhase.primRhsGUE L W (Kt u) I - Kt u I‖ := by
        congr 1; ring
    _ ≤ 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) * (v - u) := hmvt
    _ = 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) ^ 2 := by ring

end GueHypKt

/-! ### Row R2 on the grid and the discrete Duhamel formula (private) -/

section GueHypDuhamel

variable (d : Dims)

/-- **Row R2**: the discretization error of `K̃` along the grid,
`‖K̃_{u_k} − K̃_{u_0} − Δ ∑_{j<k} F(K̃_{u_j})‖ ≤ 3 M⁶ S² Δ (t₀ − t₁)`. -/
private theorem gueHyp_Kt_disc {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N M : ℕ}
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (ht10 : t1 N ≤ t0 N) (hK0 : K N ≠ 0)
    (hK : ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ M →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (hbd : ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length →
      J.length ≤ M → ‖Kt N t J‖ ≤ 1)
    (hsmall : (M : ℝ) ^ 3 * ((d.W N * d.L N : ℕ) : ℝ) * Grid.step t1 t0 K N ≤ 1)
    {k : ℕ} (hk : k ≤ K N) (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hI1 : 1 ≤ I.length)
    (hIM : I.length ≤ M) :
    ‖Kt N (Grid.time t1 t0 K N k) I - Kt N (Grid.time t1 t0 K N 0) I -
        (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
          GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) I‖ ≤
      3 * (M : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Grid.step t1 t0 K N *
        (t0 N - t1 N) := by
  set Δ := Grid.step t1 t0 K N with hΔdef
  have hΔ0 : 0 ≤ Δ := gueHyp_step_nonneg ht10
  set a : ℕ → ℂ := fun j => Kt N (Grid.time t1 t0 K N j) I with hadef
  set F : ℕ → ℂ := fun j =>
    GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) I with hFdef
  have hsucc : ∀ j : ℕ, Grid.time t1 t0 K N (j + 1) - Grid.time t1 t0 K N j = Δ := by
    intro j; unfold Grid.time; rw [← hΔdef]; push_cast; ring
  have hstep : ∀ j, j < K N → ‖a (j + 1) - a j - (Δ : ℂ) * F j‖ ≤
      3 * (M : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ ^ 2 := by
    intro j hj
    have hsub : Set.Icc (Grid.time t1 t0 K N j) (Grid.time t1 t0 K N (j + 1)) ⊆
        Set.Icc (t1 N) (t0 N) :=
      Set.Icc_subset_Icc (gueHyp_time_ge ht10 j) (gueHyp_time_le ht10 hK0 (by omega))
    have huv : Grid.time t1 t0 K N j ≤ Grid.time t1 t0 K N (j + 1) :=
      gueHyp_time_mono ht10 (Nat.le_succ j)
    have h := gueHyp_Kt_step (L := d.L N) (W := d.W N) (Kt N) (M := M) huv
      (fun t ht I' hI' h1 hM => (hK t (hsub ht) I' hI' h1 hM).mono hsub)
      (fun t ht J hJ h2 hJM => hbd t (hsub ht) J hJ h2 hJM)
      (by rw [hsucc j]; exact hsmall) I hI hI1 hIM
    rw [hsucc j] at h
    exact h
  have hid : a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, F j =
      ∑ j ∈ Finset.range k, (a (j + 1) - a j - (Δ : ℂ) * F j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub, Finset.mul_sum]
  show ‖a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, F j‖ ≤ _
  rw [hid]
  have hKΔ : (K N : ℝ) * Δ = t0 N - t1 N := by
    rw [hΔdef]; unfold Grid.step
    have : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK0
    field_simp
  calc ‖∑ j ∈ Finset.range k, (a (j + 1) - a j - (Δ : ℂ) * F j)‖
      ≤ ∑ j ∈ Finset.range k, ‖a (j + 1) - a j - (Δ : ℂ) * F j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, 3 * (M : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ ^ 2 :=
        Finset.sum_le_sum fun j hj => hstep j (by rw [Finset.mem_range] at hj; omega)
    _ = (k : ℝ) * (3 * (M : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (K N : ℝ) * (3 * (M : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
    _ = 3 * (M : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ * (t0 N - t1 N) := by
        rw [← hKΔ]; ring

/-- The discrete Duhamel formula, in norm:
`a_k − b_k = (a_0 − b_0) + (a_k − a_0 − Δ∑(e+f)) + Δ∑(e + (f − g)) − (b_k − b_0 − Δ∑g)`. -/
private theorem gueHyp_duhamel_norm (a b e f g : ℕ → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ) (k : ℕ) :
    ‖a k - b k‖ ≤ ‖a 0 - b 0‖ + ‖a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j)‖ +
      Δ * ∑ j ∈ Finset.range k, (‖e j‖ + ‖f j - g j‖) +
      ‖b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j‖ := by
  have hid : a k - b k = (a 0 - b 0) + (a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j))
      + (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))
      - (b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hid]
  have h3 : ‖(Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))‖ ≤
      Δ * ∑ j ∈ Finset.range k, (‖e j‖ + ‖f j - g j‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hΔ
    exact Finset.sum_le_sum fun j _ => norm_add_le _ _
  calc _ ≤ ‖(a 0 - b 0) + (a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j))
          + (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))‖
        + ‖b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j‖ := norm_sub_le _ _
    _ ≤ ‖a 0 - b 0‖ + ‖a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j)‖
          + ‖(Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))‖
        + ‖b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j‖ := by
        gcongr
        exact norm_add₃_le
    _ ≤ _ := by linarith [h3]

/-- `g(u) ≤ sup_{[t₁,t]} g` for a function continuous on `[t₁,t₀]` and `u ∈ [t₁,t] ⊆ [t₁,t₀]`. -/
private theorem gueHyp_le_supOn {g : ℝ → ℝ} {a b c u : ℝ} (hg : ContinuousOn g (Set.Icc a c))
    (hbc : b ≤ c) (hu : u ∈ Set.Icc a b) : g u ≤ GUEPhase.supOn g a b := by
  have hsub : Set.Icc a b ⊆ Set.Icc a c := Set.Icc_subset_Icc le_rfl hbc
  have hbdd : BddAbove (g '' Set.Icc a b) :=
    IsCompact.bddAbove_image isCompact_Icc (hg.mono hsub)
  have hbdd' : BddAbove (Set.range fun v : Set.Icc a b => g v) := by
    rw [← Set.image_eq_range] at *
    simpa [Set.image] using hbdd
  exact le_ciSup hbdd' ⟨u, hu⟩

/-- **The grid bound at `k ≤ σ`** (pathwise): the discrete Duhamel formula
with the initial term, the martingale remainder (`hM`, `hq`), the drift (`hF`, `heG`) and the
`K̃` discretization (`hdisc`), for every `t` that dominates all earlier grid times. -/
private theorem gueHyp_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N n : ℕ) (ω : Grid.Ωg d)
    (g1 g3 g4 : ℝ → ℝ) {c Cf Ce err Λ0 : ℝ}
    (ht10 : t1 N ≤ t0 N) (hc : 0 ≤ c) (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce)
    (hg1 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g1 u) (hg3 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g3 u)
    (hg4 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g4 u)
    (hg1c : ContinuousOn g1 (Set.Icc (t1 N) (t0 N)))
    (hg3c : ContinuousOn g3 (Set.Icc (t1 N) (t0 N)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 N) (t0 N)))
    (h0 : ∀ x : LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) (zt (E N) (Grid.time t1 t0 K N 0)) x.idx -
        Kt N (Grid.time t1 t0 K N 0) x.idx‖ ≤ c * Λ0)
    (hM : ∀ k ≤ K N, ∀ x : LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) x.idx
          - gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω)
            (zt (E N) (Grid.time t1 t0 K N 0)) x.idx
          - (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
              loopDriftGUE d (E N) (Grid.time t1 t0 K N j) N x.idx (gueH d t1 t0 K N j ω)‖ ≤
        c * (Real.sqrt (Grid.time t1 t0 K N k - t1 N) *
          (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 K N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
              (zt (E N) (Grid.time t1 t0 K N j)) (2 * n)))
          + (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ n))
    (hq : ∀ j < gueStop d E t1 t0 K δ N ω,
      Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ * (etaT (E N) (Grid.time t1 t0 K N j))⁻¹ ^ 2 *
        loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j))
          (2 * n)) ≤ g4 (Grid.time t1 t0 K N j))
    (hF : ∀ j < gueStop d E t1 t0 K δ N ω, ∀ x : LoopData (d.L N) n,
      ‖GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j))) x.idx -
        GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) x.idx‖ ≤
        Cf * g1 (Grid.time t1 t0 K N j))
    (heG : ∀ j < gueStop d E t1 t0 K δ N ω, ∀ x : LoopData (d.L N) n,
      ‖eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j)) x.idx‖ ≤ Ce * g3 (Grid.time t1 t0 K N j))
    (hdisc : ∀ k ≤ K N, ∀ x : LoopData (d.L N) n,
      ‖Kt N (Grid.time t1 t0 K N k) x.idx - Kt N (Grid.time t1 t0 K N 0) x.idx -
        (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
          GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) x.idx‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 N) (t0 N)) {k : ℕ} (hkσ : k ≤ gueStop d E t1 t0 K δ N ω)
    (hkt : ∀ j < k, Grid.time t1 t0 K N j ≤ t) :
    gueDmax d E t1 t0 K Kt N n k ω ≤ (c * Λ0 + err) +
      c * (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ n +
      (Cf * GUEPhase.supOn g1 (t1 N) t + Ce * GUEPhase.supOn g3 (t1 N) t) *
        (Grid.time t1 t0 K N k - t1 N) +
      (c * GUEPhase.supOn g4 (t1 N) t) * Real.sqrt (Grid.time t1 t0 K N k - t1 N) := by
  set σ := gueStop d E t1 t0 K δ N ω with hσdef
  have hσK : σ ≤ K N := Grid.firstHit_le _ _ _ ω
  have hkK : k ≤ K N := hkσ.trans hσK
  set Δ := Grid.step t1 t0 K N with hΔdef
  have hΔ0 : 0 ≤ Δ := gueHyp_step_nonneg ht10
  have hkΔ : (k : ℝ) * Δ = Grid.time t1 t0 K N k - t1 N := (gueHyp_time_sub k).symm
  have hjmem : ∀ j < k, Grid.time t1 t0 K N j ∈ Set.Icc (t1 N) t :=
    fun j hj => ⟨gueHyp_time_ge ht10 j, hkt j hj⟩
  set S1 := GUEPhase.supOn g1 (t1 N) t
  set S3 := GUEPhase.supOn g3 (t1 N) t
  set S4 := GUEPhase.supOn g4 (t1 N) t
  have hS1 : ∀ j < k, g1 (Grid.time t1 t0 K N j) ≤ S1 := fun j hj =>
    gueHyp_le_supOn hg1c ht.2 (hjmem j hj)
  have hS3 : ∀ j < k, g3 (Grid.time t1 t0 K N j) ≤ S3 := fun j hj =>
    gueHyp_le_supOn hg3c ht.2 (hjmem j hj)
  have hS4 : ∀ j < k, g4 (Grid.time t1 t0 K N j) ≤ S4 := fun j hj =>
    gueHyp_le_supOn hg4c ht.2 (hjmem j hj)
  have hS4n : 0 ≤ S4 := GUEPhase.supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS1n : 0 ≤ S1 := GUEPhase.supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := GUEPhase.supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  unfold gueDmax
  refine ciSup_le fun x => ?_
  have hD := gueHyp_duhamel_norm
    (a := fun j => gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
      (zt (E N) (Grid.time t1 t0 K N j)) x.idx)
    (b := fun j => Kt N (Grid.time t1 t0 K N j) x.idx)
    (e := fun j => eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
      (zt (E N) (Grid.time t1 t0 K N j)) x.idx)
    (f := fun j => GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N)
      (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j))) x.idx)
    (g := fun j => GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) x.idx)
    hΔ0 k
  have hM' := hM k hkK x
  simp only [loopDriftGUE] at hM'
  have hsup : (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
      (etaT (E N) (Grid.time t1 t0 K N j))⁻¹ ^ 2 *
      loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
        (zt (E N) (Grid.time t1 t0 K N j)) (2 * n))) ≤ S4 :=
    Real.iSup_le (fun j => (hq j (lt_of_lt_of_le j.2 hkσ)).trans (hS4 j j.2)) hS4n
  have hsum : ∑ j ∈ Finset.range k,
      (‖eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j)) x.idx‖ +
        ‖GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j))) x.idx -
          GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) x.idx‖) ≤
      (k : ℝ) * (Cf * S1 + Ce * S3) := by
    calc _ ≤ ∑ _j ∈ Finset.range k, (Cf * S1 + Ce * S3) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          have hjσ : j < σ := lt_of_lt_of_le hj hkσ
          have e1 := (heG j hjσ x).trans (mul_le_mul_of_nonneg_left (hS3 j hj) hCe)
          have e2 := (hF j hjσ x).trans (mul_le_mul_of_nonneg_left (hS1 j hj) hCf)
          linarith
      _ = (k : ℝ) * (Cf * S1 + Ce * S3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hΛ0 := h0 x
  have hdk := hdisc k hkK x
  have hsqrt0 : 0 ≤ Real.sqrt (Grid.time t1 t0 K N k - t1 N) := Real.sqrt_nonneg _
  have hMb : c * (Real.sqrt (Grid.time t1 t0 K N k - t1 N) *
      (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
        (etaT (E N) (Grid.time t1 t0 K N j))⁻¹ ^ 2 *
        loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j)) (2 * n)))
      + (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ n) ≤
      c * (Real.sqrt (Grid.time t1 t0 K N k - t1 N) * S4
        + (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ n) := by
    gcongr
  have hsumΔ := mul_le_mul_of_nonneg_left hsum hΔ0
  have hfin : Δ * ((k : ℝ) * (Cf * S1 + Ce * S3)) =
      (Cf * S1 + Ce * S3) * (Grid.time t1 t0 K N k - t1 N) := by
    rw [← hkΔ]; ring
  have hM'' := hM'.trans hMb
  linarith

end GueHypDuhamel

/-! ### Drift bounds and the pathwise assembly (private) -/

section GueHypPath

/-- `∑_{j=2}^n h(n-j+2) = ∑_{j=2}^n h(j)`. -/
private theorem gueHyp_sum_reflect (n : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 2 n, h (n - j + 2) = ∑ j ∈ Finset.Icc 2 n, h j := by
  refine Finset.sum_nbij' (fun j => n - j + 2) (fun j => n - j + 2) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a _; rfl

/-- **The bilinear drift** ((7.39), (7.40)): with `|K̃(J)| ≤ c λ^{|J|-1}` and `|L(J) - K̃(J)| ≤
D_{|J|}`, `|F(L) - F(K̃)| ≤ 3 n² c N ∑_{i=2}^n (λ^{i-1} + D_i) D_{n-i+2}`. -/
private theorem gueHyp_bil {L W : ℕ} [NeZero L] (Lf K : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hI : I.WF) (Dv : ℕ → ℝ) {lam c : ℝ} (hc : 1 ≤ c) (hlam : 0 ≤ lam)
    (hDv0 : ∀ i, 0 ≤ Dv i)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖Lf J - K J‖ ≤ Dv J.length)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ c * lam ^ (J.length - 1)) :
    ‖GUEPhase.primRhsGUE L W Lf I - GUEPhase.primRhsGUE L W K I‖ ≤
      3 * (I.length : ℝ) ^ 2 * c * ((W * L : ℕ) : ℝ) *
        ∑ i ∈ Finset.Icc 2 I.length, (lam ^ (i - 1) + Dv i) * Dv (I.length - i + 2) := by
  set n := I.length with hn
  set T := ∑ i ∈ Finset.Icc 2 n, (lam ^ (i - 1) + Dv i) * Dv (n - i + 2) with hT
  set S : ℝ := ((W * L : ℕ) : ℝ) with hS
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by linarith
  have hBk0 : ∀ i, 0 ≤ c * lam ^ (i - 1) := fun i => mul_nonneg hc0 (pow_nonneg hlam _)
  have hD' : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(Lf - K) J‖ ≤ Dv J.length := fun J h1 h2 h3 => by rw [Pi.sub_apply]; exact hD J h1 h2 h3
  rw [GUEPhase.primRhsGUE_sub]
  have b1 := GUEPhase.norm_primBilGUE_le L W K (Lf - K) (fun i => c * lam ^ (i - 1)) Dv I hI
    hK hD' hBk0 hDv0
  have b2 := GUEPhase.norm_primBilGUE_le L W (Lf - K) K Dv (fun i => c * lam ^ (i - 1)) I hI
    hD' hK hDv0 hBk0
  have b3 := GUEPhase.norm_primBilGUE_le L W (Lf - K) (Lf - K) Dv Dv I hI hD' hD' hDv0 hDv0
  have hterm : ∀ i ∈ Finset.Icc 2 n, 0 ≤ (lam ^ (i - 1) + Dv i) * Dv (n - i + 2) :=
    fun i _ => mul_nonneg (add_nonneg (pow_nonneg hlam _) (hDv0 i)) (hDv0 _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg hterm
  -- the three sums against `c T`
  have s2 : ∑ j ∈ Finset.Icc 2 n, Dv (n - j + 2) * (c * lam ^ (j - 1)) ≤ c * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_nonneg (mul_nonneg hc0 (hDv0 i)) (hDv0 (n - i + 2))
    nlinarith
  have s1 : ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv j ≤ c * T := by
    have hre := gueHyp_sum_reflect n (fun j => c * lam ^ (j - 1) * Dv (n - j + 2))
    have hre' : ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv j =
        ∑ j ∈ Finset.Icc 2 n, c * lam ^ (n - j + 2 - 1) * Dv (n - (n - j + 2) + 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      rw [show n - (n - j + 2) + 2 = j by omega]
    rw [hre', hre]
    refine le_trans (le_of_eq ?_) s2
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have s3 : ∑ j ∈ Finset.Icc 2 n, Dv (n - j + 2) * Dv j ≤ c * T := by
    refine le_trans ?_ (le_mul_of_one_le_left hT0 hc)
    rw [hT]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hDv0 (n - i + 2)
    have := pow_nonneg hlam (i - 1)
    nlinarith [hDv0 i]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * S := by positivity
  calc ‖GUEPhase.primBilGUE L W K (Lf - K) I + GUEPhase.primBilGUE L W (Lf - K) K I +
          GUEPhase.primBilGUE L W (Lf - K) (Lf - K) I‖
      ≤ ‖GUEPhase.primBilGUE L W K (Lf - K) I‖ + ‖GUEPhase.primBilGUE L W (Lf - K) K I‖ +
          ‖GUEPhase.primBilGUE L W (Lf - K) (Lf - K) I‖ := norm_add₃_le
    _ ≤ (n : ℝ) ^ 2 * S * (c * T) + (n : ℝ) ^ 2 * S * (c * T) + (n : ℝ) ^ 2 * S * (c * T) := by
        gcongr
        · exact b1.trans (mul_le_mul_of_nonneg_left s1 hn2)
        · exact b2.trans (mul_le_mul_of_nonneg_left s2 hn2)
        · exact b3.trans (mul_le_mul_of_nonneg_left s3 hn2)
    _ = 3 * (n : ℝ) ^ 2 * c * S * T := by ring

variable (d : Dims)

/-- `|L_k(J) - K̃_{u_k}(J)| ≤ D^{(|J|)}_k` for every well-formed `J`. -/
private theorem gueHyp_le_Dmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N k : ℕ) (ω : Grid.Ωg d)
    (J : LoopIdx (ZMod (d.L N))) (hJ : J.WF) :
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) J -
      Kt N (Grid.time t1 t0 K N k) J‖ ≤ gueDmax d E t1 t0 K Kt N J.length k ω := by
  obtain ⟨y, hy⟩ := gueHyp_exists_loopData J hJ
  unfold gueDmax
  have h := le_ciSup (f := fun y' : LoopData (d.L N) J.length =>
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) y'.idx -
      Kt N (Grid.time t1 t0 K N k) y'.idx‖) (Set.finite_range _).bddAbove y
  simp only [hy] at h
  exact h

/-- `S η_u > 0` on `[t₁, t₀]`. -/
private theorem gueHyp_scale_pos {E t0 : ℕ → ℝ} {N : ℕ} (hE : |E N| < 2)
    (ht0 : t0 N < 1) {u : ℝ} (hu : u ≤ t0 N) : 0 < gueScale d E N u := by
  unfold gueScale
  have hS : (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos N)
  have hη : 0 < etaT (E N) u := by
    unfold etaT
    have := mE_im_pos hE
    have : 0 < 1 - u := by linarith
    positivity
  positivity

/-- **The pathwise bound at one length `n`**: on the good event, the frozen
interpolated `D_n(t)` is bounded by a constant times `N^{τ'}` times the right side
`N(t-t₁) sup g₁ + (Nη_t)^{-n} + N(t-t₁) sup g₃ + √(t-t₁) sup g₄`, for all `t ∈ [t₁, t₀]`. -/
private theorem gueHyp_path (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N n : ℕ) (ω : Grid.Ωg d)
    (g3 g4 : ℝ → ℝ) {c Ce err : ℝ}
    (hE : |E N| < 2) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hK0 : K N ≠ 0)
    (hc : 1 ≤ c) (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * (n : ℝ) ^ 2 * c * ((d.L N * d.W N : ℕ) : ℝ))
    (hΔ : Grid.step t1 t0 K N ≤ 1 - t0 N)
    (herr : ∀ t ∈ Set.Icc (t1 N) (t0 N), err ≤ (gueScale d E N t)⁻¹ ^ n)
    (hg3 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 N) (t0 N)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 N) (t0 N)))
    (h0 : ∀ x : LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) (zt (E N) (Grid.time t1 t0 K N 0)) x.idx -
        Kt N (Grid.time t1 t0 K N 0) x.idx‖ ≤ c * (gueScale d E N (t1 N))⁻¹ ^ n)
    (hM : ∀ k ≤ K N, ∀ x : LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) x.idx
          - gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω)
            (zt (E N) (Grid.time t1 t0 K N 0)) x.idx
          - (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
              loopDriftGUE d (E N) (Grid.time t1 t0 K N j) N x.idx (gueH d t1 t0 K N j ω)‖ ≤
        c * (Real.sqrt (Grid.time t1 t0 K N k - t1 N) *
          (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 K N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
              (zt (E N) (Grid.time t1 t0 K N j)) (2 * n)))
          + (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ n))
    (hq : ∀ j < gueStop d E t1 t0 K δ N ω,
      Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ * (etaT (E N) (Grid.time t1 t0 K N j))⁻¹ ^ 2 *
        loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j))
          (2 * n)) ≤ g4 (Grid.time t1 t0 K N j))
    (hKt : ∀ j ≤ K N, ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖Kt N (Grid.time t1 t0 K N j) J‖ ≤ c * (gueScale d E N (Grid.time t1 t0 K N j))⁻¹ ^
        (J.length - 1))
    (heG : ∀ j < gueStop d E t1 t0 K δ N ω, ∀ x : LoopData (d.L N) n,
      ‖eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j)) x.idx‖ ≤ Ce * g3 (Grid.time t1 t0 K N j))
    (hdisc : ∀ k ≤ K N, ∀ x : LoopData (d.L N) n,
      ‖Kt N (Grid.time t1 t0 K N k) x.idx - Kt N (Grid.time t1 t0 K N 0) x.idx -
        (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
          GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) x.idx‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 N) (t0 N)) :
    gueDproc d E t1 t0 K δ Kt N n t ω ≤ c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) *
      (((d.L N * d.W N : ℕ) : ℝ) * (t - t1 N) * GUEPhase.supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
          ((((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u)⁻¹ ^ (k - 1) +
            gueDproc d E t1 t0 K δ Kt N k u ω) * gueDproc d E t1 t0 K δ Kt N (n - k + 2) u ω)
          (t1 N) t
        + (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t)⁻¹ ^ n
        + ((d.L N * d.W N : ℕ) : ℝ) * (t - t1 N) * GUEPhase.supOn g3 (t1 N) t
        + Real.sqrt (t - t1 N) * GUEPhase.supOn g4 (t1 N) t) := by
  set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := by
    have : 0 < d.L N * d.W N := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne (d.L N))) (d.W_pos N)
    rw [hSdef]; exact_mod_cast this
  set σ := gueStop d E t1 t0 K δ N ω with hσdef
  have hσK : σ ≤ K N := Grid.firstHit_le _ _ _ ω
  have hc0 : 0 ≤ c := by linarith
  have hscale_eq : ∀ u, gueScale d E N u = S * etaT (E N) u := fun u => rfl
  have hηpos : ∀ u, u ≤ t0 N → 0 < etaT (E N) u := by
    intro u hu
    unfold etaT
    have := mE_im_pos hE
    have : 0 < 1 - u := by linarith
    positivity
  set g1 : ℝ → ℝ := fun u => ∑ k ∈ Finset.Icc 2 n,
    ((S * etaT (E N) u)⁻¹ ^ (k - 1) + gueDproc d E t1 t0 K δ Kt N k u ω) *
      gueDproc d E t1 t0 K δ Kt N (n - k + 2) u ω with hg1def
  have hg1 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g1 u := by
    intro u hu
    refine Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (pow_nonneg (inv_nonneg.2
      (mul_nonneg hS0.le (hηpos u hu.2).le)) _) (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _))
      (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
  have hηc : Continuous fun u => etaT (E N) u := by unfold etaT; fun_prop
  have hg1c : ContinuousOn g1 (Set.Icc (t1 N) (t0 N)) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.mul (ContinuousOn.add ?_ (gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _))
      (gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _)
    refine ContinuousOn.pow (ContinuousOn.inv₀ (continuous_const.mul hηc).continuousOn
      fun u hu => (mul_pos hS0 (hηpos u hu.2)).ne') _
  -- the bilinear drift, `Cf = 3 n² c S`
  have hF : ∀ j < σ, ∀ x : LoopData (d.L N) n,
      ‖GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
          (zt (E N) (Grid.time t1 t0 K N j))) x.idx -
        GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 K N j)) x.idx‖ ≤
        (3 * (n : ℝ) ^ 2 * c * S) * g1 (Grid.time t1 t0 K N j) := by
    intro j hj x
    have hjK : j ≤ K N := (le_of_lt hj).trans hσK
    have hmin : min j σ = j := min_eq_left hj.le
    have hDp : ∀ i, gueDproc d E t1 t0 K δ Kt N i (Grid.time t1 t0 K N j) ω =
        gueDmax d E t1 t0 K Kt N i j ω := by
      intro i; rw [gueDproc_time d E t1 t0 K δ Kt N i j ht10 hjK ω, ← hσdef, hmin]
    have hlen : x.idx.length = n := LoopData.idx_length x
    have hb := gueHyp_bil (W := d.W N)
      (gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j)))
      (Kt N (Grid.time t1 t0 K N j)) x.idx (LoopData.idx_wf x)
      (fun i => gueDproc d E t1 t0 K δ Kt N i (Grid.time t1 t0 K N j) ω)
      (lam := (S * etaT (E N) (Grid.time t1 t0 K N j))⁻¹) hc
      (inv_nonneg.2 (mul_nonneg hS0.le (hηpos _ (gueHyp_time_le ht10 hK0 hjK)).le))
      (fun i => gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (fun J hJ _ _ => by rw [hDp]; exact gueHyp_le_Dmax d E t1 t0 K Kt N j ω J hJ)
      (fun J hJ h2 hJn => by rw [hlen] at hJn; exact hKt j hjK J hJ h2 hJn)
    rw [hlen] at hb
    have hWL : ((d.W N * d.L N : ℕ) : ℝ) = S := by rw [hSdef, Nat.mul_comm]
    rw [hWL] at hb
    refine hb.trans (le_of_eq ?_)
    rw [hg1def]
  have hCf0 : 0 ≤ 3 * (n : ℝ) ^ 2 * c * S := by positivity
  set Λ0 := (gueScale d E N (t1 N))⁻¹ ^ n with hΛ0def
  set S1 := GUEPhase.supOn g1 (t1 N) t with hS1def
  set S3 := GUEPhase.supOn g3 (t1 N) t with hS3def
  set S4 := GUEPhase.supOn g4 (t1 N) t with hS4def
  have hS1n : 0 ≤ S1 := GUEPhase.supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := GUEPhase.supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS4n : 0 ≤ S4 := GUEPhase.supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hlam : ∀ k ≤ K N, Grid.time t1 t0 K N k ≤ t + Grid.step t1 t0 K N →
      (fun u => (gueScale d E N u)⁻¹ ^ n) (Grid.time t1 t0 K N k) ≤
        2 ^ n * (fun u => (gueScale d E N u)⁻¹ ^ n) t := by
    intro k hk hkt
    simp only
    have hmem := gueHyp_time_mem (K := K) ht10 hK0 hk
    have him := mE_im_pos hE
    have hηk : etaT (E N) t ≤ 2 * etaT (E N) (Grid.time t1 t0 K N k) := by
      unfold etaT
      have h1 : (Grid.time t1 t0 K N k - t) * (mE (E N)).im ≤
          Grid.step t1 t0 K N * (mE (E N)).im :=
        mul_le_mul_of_nonneg_right (by linarith) him.le
      have h2 : Grid.step t1 t0 K N * (mE (E N)).im ≤ (1 - t0 N) * (mE (E N)).im :=
        mul_le_mul_of_nonneg_right hΔ him.le
      have h3 : (1 - t0 N) * (mE (E N)).im ≤ (1 - Grid.time t1 t0 K N k) * (mE (E N)).im :=
        mul_le_mul_of_nonneg_right (by linarith [hmem.2]) him.le
      nlinarith
    have hpk := gueHyp_scale_pos d (E := E) hE ht0 hmem.2
    have hpt := gueHyp_scale_pos d (E := E) hE ht0 ht.2
    have hinv : (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ≤ 2 * (gueScale d E N t)⁻¹ := by
      rw [show (2 : ℝ) * (gueScale d E N t)⁻¹ = 2 / gueScale d E N t by ring, inv_eq_one_div,
        div_le_div_iff₀ hpk hpt]
      rw [hscale_eq, hscale_eq]
      nlinarith
    calc (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ n ≤ (2 * (gueScale d E N t)⁻¹) ^ n :=
          pow_le_pow_left₀ (inv_nonneg.2 hpk.le) hinv n
      _ = 2 ^ n * (gueScale d E N t)⁻¹ ^ n := by rw [mul_pow]
  have hint := gueHyp_interp_bound (f := fun k => gueDmax d E t1 t0 K Kt N n k ω) hσK hK0 ht10
    ht (fun u => (gueScale d E N u)⁻¹ ^ n) (P := c * Λ0 + err) (Q := c)
    (A := 3 * (n : ℝ) ^ 2 * c * S * S1 + Ce * S3) (B := c * S4) (C := 2 ^ n) hc0
    (by positivity) (by positivity) hlam
    (fun k hk hkt => gueHyp_grid d E t1 t0 K δ Kt N n ω g1 g3 g4 ht10 hc0 hCf0 hCe0 hg1 hg3
      hg4 hg1c hg3c hg4c h0 hM hq hF heG hdisc ht hk hkt)
  have hLHS : gueDproc d E t1 t0 K δ Kt N n t ω =
      gueInterp t1 t0 K N (fun k => gueDmax d E t1 t0 K Kt N n (min k σ) ω) t := rfl
  rw [hLHS]
  refine hint.trans ?_
  set X2 := (gueScale d E N t)⁻¹ ^ n with hX2def
  have hX2eq : (S * etaT (E N) t)⁻¹ ^ n = X2 := rfl
  rw [hX2eq]
  have hpt := gueHyp_scale_pos d (E := E) hE ht0 ht.2
  have hX2n : 0 ≤ X2 := pow_nonneg (inv_nonneg.2 hpt.le) _
  have hΛ0le : Λ0 ≤ X2 := by
    have hp1 := gueHyp_scale_pos d (E := E) hE ht0 ht10
    have hle : gueScale d E N t ≤ gueScale d E N (t1 N) := by
      rw [hscale_eq, hscale_eq]
      refine mul_le_mul_of_nonneg_left ?_ hS0.le
      unfold etaT
      have := mE_im_pos hE
      nlinarith [ht.1]
    exact pow_le_pow_left₀ (inv_nonneg.2 hp1.le) (inv_anti₀ hpt hle) n
  have herr' := herr t ht
  have htt : 0 ≤ t - t1 N := by linarith [ht.1]
  have hsq : 0 ≤ Real.sqrt (t - t1 N) := Real.sqrt_nonneg _
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hX1 : 0 ≤ S * (t - t1 N) * S1 := by positivity
  have hX3 : 0 ≤ S * (t - t1 N) * S3 := by positivity
  have hX4 : 0 ≤ Real.sqrt (t - t1 N) * S4 := by positivity
  have e1 : c * Λ0 + err + c * (2 ^ n * X2) ≤ c * (2 + 2 ^ n) * X2 := by
    have := mul_le_mul_of_nonneg_left hΛ0le hc0
    have : err ≤ c * X2 := herr'.trans (le_mul_of_one_le_left hX2n hc)
    nlinarith
  have e2 : (3 * (n : ℝ) ^ 2 * c * S * S1 + Ce * S3) * (t - t1 N) ≤
      c * (7 * (n : ℝ) ^ 2) * (S * (t - t1 N) * S1 + S * (t - t1 N) * S3) := by
    have hCe' : Ce * S3 * (t - t1 N) ≤ 4 * (n : ℝ) ^ 2 * c * S * S3 * (t - t1 N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe hS3n) htt
    have ha : 0 ≤ c * (n : ℝ) ^ 2 * (S * (t - t1 N) * S1) := by positivity
    have hb : 0 ≤ c * (n : ℝ) ^ 2 * (S * (t - t1 N) * S3) := by positivity
    nlinarith
  have e3 : c * S4 * Real.sqrt (t - t1 N) ≤
      c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) * (Real.sqrt (t - t1 N) * S4) := by
    have hK1 : (1 : ℝ) ≤ 2 + 2 ^ n + 7 * (n : ℝ) ^ 2 := by linarith
    have hX : 0 ≤ c * (Real.sqrt (t - t1 N) * S4) := by positivity
    have h := mul_le_mul_of_nonneg_left hK1 hX
    calc c * S4 * Real.sqrt (t - t1 N) = c * (Real.sqrt (t - t1 N) * S4) * 1 := by ring
      _ ≤ c * (Real.sqrt (t - t1 N) * S4) * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) := h
      _ = c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) * (Real.sqrt (t - t1 N) * S4) := by ring
  have hfin : c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) *
      (S * (t - t1 N) * S1 + X2 + S * (t - t1 N) * S3 + Real.sqrt (t - t1 N) * S4) =
      c * (2 + 2 ^ n) * X2 + c * (7 * (n : ℝ) ^ 2) *
        (S * (t - t1 N) * S1 + S * (t - t1 N) * S3) +
      c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) * (Real.sqrt (t - t1 N) * S4) +
      (c * (2 + 2 ^ n) * (S * (t - t1 N) * S1 + S * (t - t1 N) * S3) +
        c * (7 * (n : ℝ) ^ 2) * X2) := by ring
  have hextra : 0 ≤ c * (2 + 2 ^ n) * (S * (t - t1 N) * S1 + S * (t - t1 N) * S3) +
      c * (7 * (n : ℝ) ^ 2) * X2 := by positivity
  rw [hfin]
  linarith

end GueHypPath

/-! ### The random inputs (private) -/

section GueHypInputs

variable (d : Dims)

/-- **Step 1**: the step-`0` input `D^{(n)}_0 ≺ (Sη_{t₁})^{-n}`, from `hB.LmK n`
transferred to `Pgue` by the one-time law `map_gueH_zero` (the failure event is the preimage of
a measurable set of matrices under `H_0`), with `K̃_{t₁} = K_{t₁}` (`hKinit`) and `ℓ_{t₁} = L`
(`hell`). -/
private theorem gueHyp_init {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hB : BoundsCoreN (sample d) E t1) (n : ℕ) (hn : 1 ≤ n) :
    StochDom (Pgue d)
      (fun N (x : LoopData (d.L N) n) ω =>
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) (zt (E N) (Grid.time t1 t0 K N 0)) x.idx -
          Kt N (Grid.time t1 t0 K N 0) x.idx‖)
      (fun N _ _ => (gueScale d E N (t1 N))⁻¹ ^ n) := by
  intro τ hτ D hD
  filter_upwards [hB.LmK n hn τ hτ D hD, hell] with N hN hellN
  have ht1lt : t1 N < 1 := lt_of_le_of_lt (ht10 N) (ht0 N)
  have hscale : (band d).scale (E N) N (t1 N) = gueScale d E N (t1 N) := by
    unfold RBM.Band.scale RBM.Band.ell gueScale
    rw [band_W, band_L, GUEPhase.ellHat_eq_L ht1lt hellN]
    push_cast; ring
  set c : ℝ := (N : ℝ) ^ τ * (gueScale d E N (t1 N))⁻¹ ^ n with hcdef
  set A : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := ⋃ x : LoopData (d.L N) n,
    {M | c < ‖gloop (d.L N) (d.W N) M (zt (E N) (t1 N)) x.idx -
      (band d).Kval (E N) N (t1 N) x.idx‖} with hAdef
  have hA : MeasurableSet A :=
    MeasurableSet.iUnion fun x => measurableSet_lt measurable_const
      ((gueHyp_meas_gloop (L := d.L N) (W := d.W N) _ _).sub_const _).norm
  have h1 : badSet (fun N (x : LoopData (d.L N) n) ω =>
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) (zt (E N) (Grid.time t1 t0 K N 0)) x.idx -
          Kt N (Grid.time t1 t0 K N 0) x.idx‖)
      (fun N _ _ => (gueScale d E N (t1 N))⁻¹ ^ n) τ N = gueH d t1 t0 K N 0 ⁻¹' A := by
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_preimage, hAdef, Set.mem_iUnion,
      Grid.time_zero, hKinit, hcdef]
  have h2 : badSet (fun N (u : LoopData ((band d).L N) n) ω =>
        (sample d).lkErr (E N) N (t1 N) ω u.idx)
      (fun N _ _ => ((band d).scale (E N) N (t1 N))⁻¹ ^ n) τ N = Hflow d N (t1 N) ⁻¹' A := by
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_preimage, hAdef, Set.mem_iUnion, hscale,
      hcdef]
    rfl
  have hmeasH : Measurable (Hflow d N (t1 N)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Hflow d N (t1 N) i j
  rw [h1, ← Measure.map_apply (gueH_measurable d t1 t0 K N 0) hA,
    map_gueH_zero d t1 t0 K N (ht1 N), Measure.map_apply hmeasH hA, ← h2]
  exact hN

/-- **The entry bound at the stopped grid times, with A3**: on the entry-bound event (at level `c`),
for `j < σ` every diagonal entry of `G_j - m` is at most `√(13 c L₂)`. -/
private theorem gueHyp_entry_le {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} {τU : ℝ}
    (hE : ∀ N, |E N| ≤ 2 - κ) (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1) (N : ℕ)
    (hellN : (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1) (hδN : gueDelta τU N ≤ (mE (E N)).im / 2)
    (ω : Grid.Ωg d) {c : ℝ} (hc : 0 ≤ c)
    (hD4 : ∀ p : Fin (gueGridK n0 N + 1) × (d.Idx N × d.Idx N),
      {ω' | ∀ i j, ‖(green (gueH d t1 t0 (gueGridK n0) N p.1 ω')
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤ gueDelta τU N}.indicator
        (fun ω' => ‖(green (gueH d t1 t0 (gueGridK n0) N p.1 ω')
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) p.2.1 p.2.2‖ ^ 2) ω ≤
      c * (9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) 2 + 2 * ((d.W N : ℕ) : ℝ)⁻¹))
    {j : ℕ} (hj : j < gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω) (q : d.Idx N) :
    ‖(green (gueH d t1 t0 (gueGridK n0) N j ω) (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) q q‖ ≤
      Real.sqrt (13 * c * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2) := by
  have hσK : gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω ≤ gueGridK n0 N :=
    Grid.firstHit_le _ _ _ ω
  have hjK : j < gueGridK n0 N + 1 := by omega
  have hj' : j < Grid.firstHit (fun k ω' => gueDev d E t1 t0 (gueGridK n0) N k ω')
      (gueDelta τU N) (gueGridK n0 N) ω := hj
  have hdev : gueDev d E t1 t0 (gueGridK n0) N j ω < gueDelta τU N :=
    Grid.lt_firstHit_imp (fun k ω' => gueDev d E t1 t0 (gueGridK n0) N k ω') (gueDelta τU N)
      (gueGridK n0 N) hj'
  have hentry : ∀ i i', ‖(green (gueH d t1 t0 (gueGridK n0) N j ω)
      (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) -
      mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i i'‖ ≤ gueDelta τU N := by
    intro i i'
    refine le_trans ?_ hdev.le
    unfold gueDev
    exact le_ciSup (f := fun ij : d.Idx N × d.Idx N =>
      ‖(green (gueH d t1 t0 (gueGridK n0) N j ω) (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖)
      (Set.finite_range _).bddAbove (i, i')
  have h4 := hD4 (⟨j, hjK⟩, (q, q))
  simp only at h4
  rw [Set.indicator_of_mem (show ω ∈ {ω' | ∀ i j', ‖(green (gueH d t1 t0 (gueGridK n0) N j ω')
      (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) -
      mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j'‖ ≤ gueDelta τU N} from hentry)] at h4
  -- A3: `W⁻¹ ≤ 2 L₂` on the a-priori event
  have hEN : |E N| < 2 := lt_of_le_of_lt (hE N) (by linarith)
  have hu1 : Grid.time t1 t0 (gueGridK n0) N j < 1 :=
    lt_of_le_of_lt (gueHyp_time_le (ht10 N) (gueGridK_ne_zero n0 N) (by omega)) (ht0 N)
  have hellj : (d.L N : ℝ) ^ 2 * (1 - Grid.time t1 t0 (gueGridK n0) N j) ≤ 1 := by
    have h1 := gueHyp_time_ge (K := gueGridK n0) (ht10 N) j
    have hL : (0 : ℝ) ≤ (d.L N : ℝ) ^ 2 := sq_nonneg _
    have h2 : 1 - Grid.time t1 t0 (gueGridK n0) N j ≤ 1 - t1 N := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hL) hellN
  have hW := gue_inv_W_le_loopMax (L := d.L N) (W := d.W N)
    (gueH_isHermitian d t1 t0 (gueGridK n0) N j ω) hEN hu1 hellj (gueEntry_goodEvent hentry) hδN
  have hL0 := loopMax_nonneg (L := d.L N) (W := d.W N) (H := gueH d t1 t0 (gueGridK n0) N j ω)
    (z := zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2
  apply Real.le_sqrt_of_sq_le
  calc _ ≤ c * (9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2 + 2 * ((d.W N : ℕ) : ℝ)⁻¹) := h4
    _ ≤ c * (9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2 + 2 * (2 * loopMax (d.L N) (d.W N)
          (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2)) := by
        gcongr
    _ = 13 * c * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2 := by ring

end GueHypInputs

/-! ### The `E^{(G)}` and martingale lines of the two targets (private) -/

section GueHypLines

variable (d : Dims)

/-- **Row E2** (h745E, even `n = 2l`): `|Ẽ| ≤ 4 n c S L₂ L_n` from `ε ≤ √(13 c L₂)` (entry bound +
A3) and `L_{2l+1} ≤ √L₂ L_{2l}` (`gueLoopMax_odd_succ_le`). -/
private theorem gueHyp_eG_745 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (N j : ℕ) (ω : Grid.Ωg d)
    {c : ℝ} (hc : 1 ≤ c) {l : ℕ} (hl : 1 ≤ l)
    (hdiag : ∀ q : d.Idx N, ‖(green (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) q q‖ ≤
      Real.sqrt (13 * c * loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω)
        (zt (E N) (Grid.time t1 t0 K N j)) 2))
    (x : LoopData (d.L N) (2 * l)) :
    ‖eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
        (zt (E N) (Grid.time t1 t0 K N j)) x.idx‖ ≤
      (4 * ((2 * l : ℕ) : ℝ) * c * ((d.L N * d.W N : ℕ) : ℝ)) *
        (loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j)) 2 *
          loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j))
            (2 * l)) := by
  set H := gueH d t1 t0 K N j ω with hHdef
  set z := zt (E N) (Grid.time t1 t0 K N j) with hzdef
  have hH : H.IsHermitian := gueH_isHermitian d t1 t0 K N j ω
  set L2 := loopMax (d.L N) (d.W N) H z 2 with hL2
  set Ln := loopMax (d.L N) (d.W N) H z (2 * l) with hLn
  have hL20 : 0 ≤ L2 := loopMax_nonneg _
  have hLn0 : 0 ≤ Ln := loopMax_nonneg _
  have hlen : x.idx.length = 2 * l := LoopData.idx_length x
  have hb := norm_eGtermGUE_le (d.L N) (d.W N) (mSigma (E N)) H z x.idx
    (ε := Real.sqrt (13 * c * L2)) (B := Real.sqrt L2 * Ln)
    (gueHyp_eps_le_dev hH (E N) z hdiag)
    (fun k hk b => (gueHyp_cutGlue_le (LoopData.idx_wf x) hk b).trans (by
      rw [hlen]; exact gueLoopMax_odd_succ_le hH z hl))
  rw [hlen] at hb
  refine hb.trans ?_
  have hc0 : 0 ≤ c := by linarith
  have hs : Real.sqrt (13 * c * L2) * (Real.sqrt L2 * Ln) = Real.sqrt (13 * c) * (L2 * Ln) := by
    rw [Real.sqrt_mul (by positivity) L2]
    have := Real.mul_self_sqrt hL20
    calc Real.sqrt (13 * c) * Real.sqrt L2 * (Real.sqrt L2 * Ln)
        = Real.sqrt (13 * c) * (Real.sqrt L2 * Real.sqrt L2) * Ln := by ring
      _ = Real.sqrt (13 * c) * (L2 * Ln) := by rw [this]; ring
  have h13 : Real.sqrt (13 * c) ≤ 4 * c := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hS : (0 : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((2 * l : ℕ) : ℝ) * ((d.L N * d.W N : ℕ) : ℝ) * Real.sqrt (13 * c * L2) *
        (Real.sqrt L2 * Ln)
      = ((2 * l : ℕ) : ℝ) * ((d.L N * d.W N : ℕ) : ℝ) * (Real.sqrt (13 * c) * (L2 * Ln)) := by
        rw [← hs]; ring
    _ ≤ ((2 * l : ℕ) : ℝ) * ((d.L N * d.W N : ℕ) : ℝ) * (4 * c * (L2 * Ln)) := by
        gcongr
    _ = _ := by ring

/-- **Row E3** (h746): `|Ẽ| ≤ n S D₁ L_{n+1}`, from `ε ≤ D^{(1)}` (`K̃ = m_σ` at length `1`). -/
private theorem gueHyp_eG_746 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (N j n : ℕ) (hu : Grid.time t1 t0 K N j ∈ Set.Icc (t1 N) (t0 N)) (ω : Grid.Ωg d)
    (x : LoopData (d.L N) n) :
    ‖eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
        (zt (E N) (Grid.time t1 t0 K N j)) x.idx‖ ≤
      ((n : ℝ) * ((d.L N * d.W N : ℕ) : ℝ)) *
        (gueDmax d E t1 t0 K Kt N 1 j ω *
          loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j))
            (n + 1)) := by
  have hlen : x.idx.length = n := LoopData.idx_length x
  have hε : ∀ (σ : Bool) (a : ZMod (d.L N)), ‖Matrix.trace ((Gsig (gueH d t1 t0 K N j ω)
      (zt (E N) (Grid.time t1 t0 K N j)) σ - mSigma (E N) σ •
      (1 : Matrix (ZMod (d.L N) × Fin (d.W N)) (ZMod (d.L N) × Fin (d.W N)) ℂ)) *
      Eblk (d.L N) (d.W N) a)‖ ≤ gueDmax d E t1 t0 K Kt N 1 j ω := by
    intro σ a
    rw [gueHyp_trace_eq_gloop_one, ← gueHyp_Kt_one d n0 hn0 Kt hKinit hK N hu σ a]
    exact gueHyp_le_Dmax d E t1 t0 K Kt N j ω ⟨[σ], [a]⟩ rfl
  have hb := norm_eGtermGUE_le (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N j ω)
    (zt (E N) (Grid.time t1 t0 K N j)) x.idx hε
    (fun k hk b => gueHyp_cutGlue_le (LoopData.idx_wf x) hk b)
  rw [hlen] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- The martingale line of h745E: `√(S⁻¹η⁻² L_{4l}) ≤ √(S⁻¹η⁻²) L_{2l}`, from `L_{4l} ≤ L_{2l}²`
(`gueLoopMax_four_mul_le`). -/
private theorem gueHyp_q_745 {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) (z : ℂ) {a : ℝ}
    (ha : 0 ≤ a) {l : ℕ} (hl : 1 ≤ l) :
    Real.sqrt (a * loopMax L W H z (2 * (2 * l))) ≤ Real.sqrt a * loopMax L W H z (2 * l) := by
  have h := gueLoopMax_four_mul_le hH z hl
  rw [show 2 * (2 * l) = 4 * l by ring]
  calc Real.sqrt (a * loopMax L W H z (4 * l))
      ≤ Real.sqrt (a * loopMax L W H z (2 * l) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h ha)
    _ = Real.sqrt a * loopMax L W H z (2 * l) := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq (loopMax_nonneg _)]

end GueHypLines

/-! ### Eventual deterministic facts (private) -/

section GueHypEventually

/-- The grid is fine enough for rows R2 (`M³ N Δ ≤ 1`) and for the absorption of the
discretization error into `N^{-2n₀}`. -/
private theorem gueHyp_ev_grid (n0 : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((2 * n0 : ℕ) : ℝ) ^ 3 * (N : ℝ) * ((gueGridK n0 N : ℝ))⁻¹ ≤ 1 ∧
      3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * (N : ℝ) ^ 2 * ((gueGridK n0 N : ℝ))⁻¹ ≤
        ((N : ℝ)⁻¹) ^ (2 * n0) := by
  filter_upwards [eventually_ge_atTop (3 * (2 * n0) ^ 6 + (2 * n0) ^ 3 + 1)] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hKpos : (0 : ℝ) < (gueGridK n0 N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (gueGridK_ne_zero n0 N)
  have hKge : (N : ℝ) ^ (2 * n0 + 3) ≤ (gueGridK n0 N : ℝ) := by
    unfold gueGridK
    push_cast
    calc (N : ℝ) ^ (2 * n0 + 3) ≤ (N : ℝ) ^ (32 * n0 + 64) :=
          pow_le_pow_right₀ hNR (by omega)
      _ ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) := pow_le_pow_left₀ hN0.le (by linarith) _
  have hA : ((3 * (2 * n0) ^ 6 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  have hB : (((2 * n0) ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  push_cast at hA hB
  push_cast
  constructor
  · rw [← div_eq_mul_inv, div_le_one hKpos]
    calc ((2 * (n0 : ℝ))) ^ 3 * (N : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hB hN0.le
      _ = (N : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) ^ (2 * n0 + 3) := pow_le_pow_right₀ hNR (by omega)
      _ ≤ _ := hKge
  · rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hKpos]
    have hpow : (0 : ℝ) < (N : ℝ) ^ (2 * n0) := pow_pos hN0 _
    rw [← div_eq_inv_mul, le_div_iff₀ hpow]
    calc 3 * (2 * (n0 : ℝ)) ^ 6 * (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n0)
        ≤ (N : ℝ) * (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n0) := by gcongr
      _ = (N : ℝ) ^ (2 * n0 + 3) := by ring
      _ ≤ _ := hKge

/-- `Im m ≥ √(2κ)/2` for `|E| ≤ 2 - κ`, hence `δ_N = N^{-τU/4} ≤ Im m / 2` eventually. -/
private theorem gueHyp_ev_delta {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| ≤ 2 - κ) :
    ∀ᶠ N : ℕ in atTop, gueDelta τU N ≤ (mE (E N)).im / 2 := by
  have hκ2 : κ ≤ 2 := by have := hE 0; have := abs_nonneg (E 0); linarith
  have hlow : ∀ N, Real.sqrt (2 * κ) / 2 ≤ (mE (E N)).im := by
    intro N
    rw [mE_im]
    have hsq : E N ^ 2 ≤ (2 - κ) ^ 2 := by
      have h := hE N
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have : 2 * κ ≤ 4 - E N ^ 2 := by nlinarith
    gcongr
  have hc : 0 < Real.sqrt (2 * κ) / 4 := by positivity
  filter_upwards [eventually_le_rpow (Real.sqrt (2 * κ) / 4)⁻¹ (by positivity : 0 < τU / 4),
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  unfold gueDelta
  rw [Real.rpow_neg hN0.le]
  have hpos : 0 < (N : ℝ) ^ (τU / 4) := Real.rpow_pos_of_pos hN0 _
  calc ((N : ℝ) ^ (τU / 4))⁻¹ ≤ Real.sqrt (2 * κ) / 4 := by
        rw [inv_le_comm₀ hpos hc]; exact hN
    _ ≤ (mE (E N)).im / 2 := by linarith [hlow N]

end GueHypEventually

/-! ### Finitely many high-probability events (private) -/

private theorem gueHyp_highProb_range {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (M : ℕ)
    (Ξ : ℕ → ℕ → Set Ω) (h : ∀ n, 1 ≤ n → n ≤ M → HighProb P (Ξ n)) :
    HighProb P (fun N => {ω | ∀ n, 1 ≤ n → n ≤ M → ω ∈ Ξ n N}) := by
  induction M with
  | zero =>
    exact HighProb.of_eventually_univ (Eventually.of_forall fun N ω n h1 h2 => by omega)
  | succ M ih =>
    have h1 := ih fun n hn1 hn2 => h n hn1 (by omega)
    have h2 := h (M + 1) (by omega) le_rfl
    refine (HighProb.inter h1 h2).mono (Eventually.of_forall fun N ω hω n hn1 hn2 => ?_)
    rcases Nat.lt_or_ge n (M + 1) with hlt | hge
    · exact hω.1 n hn1 (by omega)
    · obtain rfl : n = M + 1 := by omega
      exact hω.2

/-! ### The pathwise bound at a fixed `N` with the exponent bookkeeping (private) -/

section GueHypFixed

variable (d : Dims)

/-- **One length, one `N`, one sample point**: all the eventual deterministic facts and the good
event at level `N^{τ/2}` give `D_n(t) ≤ N^τ · rhs(t)` for every `t ∈ [t₁, t₀]` (rows K1 and R2,
the interpolation between grid times, and the final absorption). -/
private theorem gueHyp_fixed {τ : ℝ} (hτ : 0 < τ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (τU : ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (N n : ℕ) (ω : Grid.Ωg d) (g3 g4 : ℝ → ℝ) {Ce : ℝ}
    (hEb : |E N| < 2) (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hN1 : 1 ≤ N)
    (hn1 : 1 ≤ n) (hn : n ≤ 2 * n0) (hdim : d.W N * d.L N ≤ N)
    (hΔ : Grid.step t1 t0 (gueGridK n0) N ≤ 1 - t0 N)
    (hgrid1 : ((2 * n0 : ℕ) : ℝ) ^ 3 * (N : ℝ) * ((gueGridK n0 N : ℝ))⁻¹ ≤ 1)
    (hgrid2 : 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * (N : ℝ) ^ 2 * ((gueGridK n0 N : ℝ))⁻¹ ≤
      ((N : ℝ)⁻¹) ^ (2 * n0))
    (hbd : ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt N t J‖ ≤ 1)
    (hKtc : ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt N t J‖ ≤ (N : ℝ) ^ (τ / 2) * (gueScale d E N t)⁻¹ ^ (J.length - 1))
    (hbig : 2 + 2 ^ (2 * n0) + 7 * ((2 * n0 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (τ / 2))
    (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * (n : ℝ) ^ 2 * (N : ℝ) ^ (τ / 2) * ((d.L N * d.W N : ℕ) : ℝ))
    (hg3 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 N) (t0 N)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 N) (t0 N)))
    (h0 : ∀ x : LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N 0 ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N 0)) x.idx -
        Kt N (Grid.time t1 t0 (gueGridK n0) N 0) x.idx‖ ≤
        (N : ℝ) ^ (τ / 2) * (gueScale d E N (t1 N))⁻¹ ^ n)
    (hM : ∀ k ≤ gueGridK n0 N, ∀ x : LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) x.idx
          - gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N 0 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N 0)) x.idx
          - (Grid.step t1 t0 (gueGridK n0) N : ℂ) * ∑ j ∈ Finset.range k,
              loopDriftGUE d (E N) (Grid.time t1 t0 (gueGridK n0) N j) N x.idx
                (gueH d t1 t0 (gueGridK n0) N j ω)‖ ≤
        (N : ℝ) ^ (τ / 2) * (Real.sqrt (Grid.time t1 t0 (gueGridK n0) N k - t1 N) *
          (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
              (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)))
          + (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ n))
    (hq : ∀ j < gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω,
      Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
        (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
        loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)) ≤
        g4 (Grid.time t1 t0 (gueGridK n0) N j))
    (heG : ∀ j < gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω, ∀ x : LoopData (d.L N) n,
      ‖eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) x.idx‖ ≤
        Ce * g3 (Grid.time t1 t0 (gueGridK n0) N j))
    {t : ℝ} (ht : t ∈ Set.Icc (t1 N) (t0 N)) :
    gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N n t ω ≤ (N : ℝ) ^ τ *
      (((d.L N * d.W N : ℕ) : ℝ) * (t - t1 N) * GUEPhase.supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
          ((((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u)⁻¹ ^ (k - 1) +
            gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N k u ω) *
            gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N (n - k + 2) u ω)
          (t1 N) t
        + (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t)⁻¹ ^ n
        + ((d.L N * d.W N : ℕ) : ℝ) * (t - t1 N) * GUEPhase.supOn g3 (t1 N) t
        + Real.sqrt (t - t1 N) * GUEPhase.supOn g4 (t1 N) t) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set c := (N : ℝ) ^ (τ / 2) with hcdef
  have hc : 1 ≤ c := Real.one_le_rpow hNR (by positivity)
  have hK0 : gueGridK n0 N ≠ 0 := gueGridK_ne_zero n0 N
  have hKR : (1 : ℝ) ≤ (gueGridK n0 N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hK0
  set Δ := Grid.step t1 t0 (gueGridK n0) N with hΔdef
  have hΔ0 : 0 ≤ Δ := gueHyp_step_nonneg ht10
  have hΔK : Δ ≤ ((gueGridK n0 N : ℝ))⁻¹ := by
    rw [hΔdef]; unfold Grid.step
    rw [div_eq_mul_inv]
    have : t0 N - t1 N ≤ 1 := by linarith
    have hKi : 0 ≤ ((gueGridK n0 N : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
    have h0 : 0 ≤ t0 N - t1 N := by linarith
    calc (t0 N - t1 N) * ((gueGridK n0 N : ℝ))⁻¹ ≤ 1 * ((gueGridK n0 N : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right this hKi
      _ = ((gueGridK n0 N : ℝ))⁻¹ := one_mul _
  have hWL : (((d.W N * d.L N : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast hdim
  have hWL0 : (0 : ℝ) ≤ ((d.W N * d.L N : ℕ) : ℝ) := Nat.cast_nonneg _
  -- row R2
  have hsmall : ((2 * n0 : ℕ) : ℝ) ^ 3 * ((d.W N * d.L N : ℕ) : ℝ) * Δ ≤ 1 := by
    calc ((2 * n0 : ℕ) : ℝ) ^ 3 * ((d.W N * d.L N : ℕ) : ℝ) * Δ
        ≤ ((2 * n0 : ℕ) : ℝ) ^ 3 * (N : ℝ) * ((gueGridK n0 N : ℝ))⁻¹ := by
          have hM0 : (0 : ℝ) ≤ ((2 * n0 : ℕ) : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
          exact mul_le_mul (mul_le_mul_of_nonneg_left hWL hM0) hΔK hΔ0
            (mul_nonneg hM0 hN0.le)
      _ ≤ 1 := hgrid1
  have hK' : ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t := fun t ht I hI h1 h2 => hK N t ht I hI h1 (by omega)
  set err := 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ * (t0 N - t1 N)
    with herrdef
  have hdisc : ∀ k ≤ gueGridK n0 N, ∀ x : LoopData (d.L N) n,
      ‖Kt N (Grid.time t1 t0 (gueGridK n0) N k) x.idx -
          Kt N (Grid.time t1 t0 (gueGridK n0) N 0) x.idx -
        (Δ : ℂ) * ∑ j ∈ Finset.range k,
          GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N (Grid.time t1 t0 (gueGridK n0) N j))
            x.idx‖ ≤ err := fun k hk x =>
    gueHyp_Kt_disc d Kt ht10 hK0 hK' hbd hsmall hk x.idx (LoopData.idx_wf x)
      (by rw [LoopData.idx_length]; exact hn1) (by rw [LoopData.idx_length]; exact hn)
  have herr : ∀ t' ∈ Set.Icc (t1 N) (t0 N), err ≤ (gueScale d E N t')⁻¹ ^ n := by
    intro t' ht'
    have hsc := gueHyp_scale_pos d (E := E) hEb ht0 ht'.2
    have hsN : gueScale d E N t' ≤ N := by
      unfold gueScale
      have hη1 : etaT (E N) t' ≤ 1 := by
        unfold etaT
        have hm1 : (mE (E N)).im ≤ 1 := by
          have h1 := Complex.abs_im_le_norm (mE (E N))
          rw [norm_mE hEb.le] at h1
          exact (abs_le.mp h1).2
        have hm0 := (mE_im_pos hEb).le
        have : 1 - t' ≤ 1 := by linarith [ht'.1]
        have : 0 ≤ 1 - t' := by linarith [ht'.2]
        nlinarith
      have hLW : ((d.L N * d.W N : ℕ) : ℝ) ≤ N := by rw [Nat.mul_comm]; exact hWL
      have hη0 : 0 ≤ etaT (E N) t' := by
        unfold etaT; have := (mE_im_pos hEb).le; nlinarith [ht'.2]
      nlinarith
    have hinv : (N : ℝ)⁻¹ ≤ (gueScale d E N t')⁻¹ := inv_anti₀ hsc hsN
    have hNi1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
    have hNi0 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN0.le
    calc err ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * (N : ℝ) ^ 2 * ((gueGridK n0 N : ℝ))⁻¹ := by
          rw [herrdef]
          have h1 : t0 N - t1 N ≤ 1 := by linarith
          have h2 : 0 ≤ t0 N - t1 N := by linarith
          have h3 : ((d.W N * d.L N : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
            pow_le_pow_left₀ hWL0 hWL 2
          have h4 : Δ * (t0 N - t1 N) ≤ ((gueGridK n0 N : ℝ))⁻¹ := by
            calc Δ * (t0 N - t1 N) ≤ Δ * 1 := mul_le_mul_of_nonneg_left h1 hΔ0
              _ ≤ _ := by rw [mul_one]; exact hΔK
          have h5 : (0 : ℝ) ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 :=
            mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)
          calc 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 * Δ * (t0 N - t1 N)
              = 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((d.W N * d.L N : ℕ) : ℝ) ^ 2 *
                  (Δ * (t0 N - t1 N)) := by ring
            _ ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * (N : ℝ) ^ 2 * ((gueGridK n0 N : ℝ))⁻¹ := by
                exact mul_le_mul (mul_le_mul_of_nonneg_left h3 h5) h4
                  (mul_nonneg hΔ0 h2) (mul_nonneg h5 (sq_nonneg _))
      _ ≤ ((N : ℝ)⁻¹) ^ (2 * n0) := hgrid2
      _ ≤ ((N : ℝ)⁻¹) ^ n := pow_le_pow_of_le_one hNi0 hNi1 hn
      _ ≤ (gueScale d E N t')⁻¹ ^ n := pow_le_pow_left₀ hNi0 hinv n
  -- row K1 on the grid
  have hKt : ∀ j ≤ gueGridK n0 N, ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length →
      J.length ≤ n → ‖Kt N (Grid.time t1 t0 (gueGridK n0) N j) J‖ ≤
        c * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ (J.length - 1) :=
    fun j hj J hJ h2 hJn => hKtc _ (gueHyp_time_mem ht10 hK0 hj) J hJ h2 (hJn.trans hn)
  have hn2 : (n : ℝ) ^ 2 ≤ ((2 * n0 : ℕ) : ℝ) ^ 2 := by
    have : (n : ℝ) ≤ ((2 * n0 : ℕ) : ℝ) := by exact_mod_cast hn
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hpath := gueHyp_path d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N n ω g3 g4 (c := c)
    (Ce := Ce) (err := err) hEb ht10 ht0 hK0 hc hCe0 hCe hΔ herr hg3 hg4 hg3c hg4c h0 hM hq
    hKt heG hdisc ht
  set R := ((d.L N * d.W N : ℕ) : ℝ) * (t - t1 N) * GUEPhase.supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
          ((((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u)⁻¹ ^ (k - 1) +
            gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N k u ω) *
            gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N (n - k + 2) u ω)
          (t1 N) t
        + (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t)⁻¹ ^ n
        + ((d.L N * d.W N : ℕ) : ℝ) * (t - t1 N) * GUEPhase.supOn g3 (t1 N) t
        + Real.sqrt (t - t1 N) * GUEPhase.supOn g4 (t1 N) t with hRdef
  have hK0' : (0 : ℝ) < 2 + 2 ^ n + 7 * (n : ℝ) ^ 2 := by positivity
  have hDp0 := gueDproc_nonneg d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N n t ω
  have hR0 : 0 ≤ R := by
    by_contra hneg
    push Not at hneg
    have : c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) * R < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have hKn : 2 + 2 ^ n + 7 * (n : ℝ) ^ 2 ≤ c := by
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ (2 * n0) := pow_le_pow_right₀ (by norm_num) hn
    rw [hcdef]
    linarith
  have hNτ : (N : ℝ) ^ τ = c * c := by
    rw [hcdef, ← Real.rpow_add hN0]; ring_nf
  calc gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N n t ω
      ≤ c * (2 + 2 ^ n + 7 * (n : ℝ) ^ 2) * R := hpath
    _ ≤ c * c * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKn (by linarith)) hR0
    _ = (N : ℝ) ^ τ * R := by rw [hNτ]

end GueHypFixed

/-! ### Two more eventual facts at a fixed `N` (private) -/

section GueHypFacts

variable (d : Dims)

/-- The input of the interpolation between grid times: `Δ ≤ t₀ − t₁ ≤ N^{-τU} η_{t₀} ≤ 1 − t₀`. -/
private theorem gueHyp_step_le {E t1 t0 : ℕ → ℝ} {τU : ℝ} (n0 N : ℕ) (hEb : |E N| < 2)
    (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hN1 : 1 ≤ N)
    (h730 : t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N)) (hτU : 0 < τU) :
    Grid.step t1 t0 (gueGridK n0) N ≤ 1 - t0 N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hKR : (1 : ℝ) ≤ (gueGridK n0 N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (gueGridK_ne_zero n0 N)
  have hm1 : (mE (E N)).im ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (mE (E N))
    rw [norm_mE hEb.le] at h1
    exact (abs_le.mp h1).2
  have hm0 := (mE_im_pos hEb).le
  have hη0 : 0 ≤ etaT (E N) (t0 N) := by unfold etaT; nlinarith
  have hη1 : etaT (E N) (t0 N) ≤ 1 - t0 N := by unfold etaT; nlinarith
  have hNp : (N : ℝ) ^ (-τU) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hstep : Grid.step t1 t0 (gueGridK n0) N ≤ t0 N - t1 N := by
    unfold Grid.step
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc Grid.step t1 t0 (gueGridK n0) N ≤ t0 N - t1 N := hstep
    _ ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N) := h730
    _ ≤ 1 * etaT (E N) (t0 N) := mul_le_mul_of_nonneg_right hNp hη0
    _ ≤ 1 - t0 N := by rw [one_mul]; exact hη1

/-- `‖K̃_t(J)‖ ≤ 1` on `[t₁, t₀]` for `2 ≤ |J| ≤ 2n₀`, from row K1 at `τU/2` and
`(S η_t)^{-1} ≤ N^{-τU}`. -/
private theorem gueHyp_Kt_le_one {E t1 t0 : ℕ → ℝ} {τU : ℝ} (hτU : 0 < τU) (n0 N : ℕ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (hEb : |E N| < 2) (ht0 : t0 N < 1)
    (hN1 : 1 ≤ N)
    (hK1 : ∀ p : TimeIcc t1 t0 N × GUEPhase.LoopSet (d.L N) (2 * n0), ‖Kt N p.1 p.2.1‖ ≤
      (N : ℝ) ^ (τU / 2) *
        (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) p.1)⁻¹ ^ ((p.2.1).length - 1))
    (hscale : (gueScale d E N (t0 N))⁻¹ ≤ (N : ℝ) ^ (-τU)) :
    ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt N t J‖ ≤ 1 := by
  intro t ht J hJ h2 hJn
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h := hK1 (⟨t, ht⟩, ⟨J, hJ, h2, hJn⟩)
  simp only at h
  have hst := gueHyp_scale_pos d (E := E) hEb ht0 ht.2
  have hs0 := gueHyp_scale_pos d (E := E) hEb ht0 (le_refl (t0 N))
  have hle : gueScale d E N (t0 N) ≤ gueScale d E N t := by
    unfold gueScale
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold etaT
    have := (mE_im_pos hEb).le
    nlinarith [ht.2]
  have hinv : (gueScale d E N t)⁻¹ ≤ (N : ℝ) ^ (-τU) :=
    (inv_anti₀ hs0 hle).trans hscale
  have hNp1 : (N : ℝ) ^ (-τU) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hNp0 : 0 ≤ (N : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
  have hpow : (gueScale d E N t)⁻¹ ^ (J.length - 1) ≤ (N : ℝ) ^ (-τU) := by
    calc (gueScale d E N t)⁻¹ ^ (J.length - 1) ≤ ((N : ℝ) ^ (-τU)) ^ (J.length - 1) :=
          pow_le_pow_left₀ (inv_nonneg.2 hst.le) hinv _
      _ ≤ ((N : ℝ) ^ (-τU)) ^ 1 := pow_le_pow_of_le_one hNp0 hNp1 (by omega)
      _ = (N : ℝ) ^ (-τU) := pow_one _
  have hcomb : (N : ℝ) ^ (τU / 2) * (N : ℝ) ^ (-τU) ≤ 1 := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  calc ‖Kt N t J‖ ≤ (N : ℝ) ^ (τU / 2) * (gueScale d E N t)⁻¹ ^ (J.length - 1) := h
    _ ≤ (N : ℝ) ^ (τU / 2) * (N : ℝ) ^ (-τU) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hN0.le _)
    _ ≤ 1 := hcomb

/-- Grid values of the frozen processes before the stopping index. -/
private theorem gueHyp_Lproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N m j : ℕ)
    (ω : Grid.Ωg d) (ht10 : t1 N ≤ t0 N) (hj : j < gueStop d E t1 t0 K δ N ω) :
    gueLproc d E t1 t0 K δ N m (Grid.time t1 t0 K N j) ω =
      loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt (E N) (Grid.time t1 t0 K N j)) m := by
  have hσK : gueStop d E t1 t0 K δ N ω ≤ K N := Grid.firstHit_le _ _ _ ω
  rw [gueLproc_time d E t1 t0 K δ N m j ht10 (by omega) ω, min_eq_left hj.le]
  rfl

private theorem gueHyp_Dproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m j : ℕ)
    (ω : Grid.Ωg d) (ht10 : t1 N ≤ t0 N) (hj : j < gueStop d E t1 t0 K δ N ω) :
    gueDproc d E t1 t0 K δ Kt N m (Grid.time t1 t0 K N j) ω = gueDmax d E t1 t0 K Kt N m j ω := by
  have hσK : gueStop d E t1 t0 K δ N ω ≤ K N := Grid.firstHit_le _ _ _ ω
  rw [gueDproc_time d E t1 t0 K δ Kt N m j ht10 (by omega) ω, min_eq_left hj.le]

/-- Continuity of `u ↦ √(S⁻¹ η_u⁻²)` on `[t₁, t₀]`. -/
private theorem gueHyp_sqrt_cont {E t1 t0 : ℕ → ℝ} (N : ℕ) (hEb : |E N| < 2) (ht0 : t0 N < 1) :
    ContinuousOn (fun u => Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ * (etaT (E N) u)⁻¹ ^ 2))
      (Set.Icc (t1 N) (t0 N)) := by
  have hηc : Continuous fun u => etaT (E N) u := by unfold etaT; fun_prop
  have hη : ∀ u ∈ Set.Icc (t1 N) (t0 N), etaT (E N) u ≠ 0 := by
    intro u hu
    unfold etaT
    have := mE_im_pos hEb
    have : 0 < 1 - u := by linarith [hu.2]
    exact (mul_pos this (mE_im_pos hEb)).ne'
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul ((hηc.continuousOn.inv₀ hη).pow 2))

end GueHypFacts

/-! ### The main statements -/

variable (d : Dims)

/-- **(7.45)G at even lengths `2 ≤ m ≤ 2n₀`** for the frozen, interpolated processes: the `h745`
of `eq727GE` (with `n₀' = 2 n₀`), over the whole interval `[t₁, t₀]`. -/
theorem gueBds_h745E {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (h730 : ∀ᶠ N : ℕ in atTop, t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N))
    (hscale : ∀ᶠ N : ℕ in atTop, (gueScale d E N (t0 N))⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (hB : BoundsCoreN (sample d) E t1) :
    StochDom (Pgue d)
      (fun N (p : TimeIcc t1 t0 N × {m : ℕ // m ∈ Set.Icc 2 (2 * n0) ∧ Even m}) ω =>
        gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N p.2.1 p.1 ω)
      (fun N p ω => GUEPhase.rhs745G (((d.L N * d.W N : ℕ) : ℝ)) (etaT (E N)) (t1 N)
        (fun m t => gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N m t ω)
        (fun m t => gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N m t ω) p.2.1 p.1) := by
  have hEb : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hI := fun n (hn : 1 ≤ n) =>
    gueHyp_init d (gueGridK n0) ht1 ht10 ht0 hell Kt hKinit hB (t0 := t0) n hn
  have hKtd := gueHyp_Kt_detDom d hκ hτU n0 hE ht10 ht0 h730 hell Kt hKinit hK
  have hD4 := gueGrid_entry_bound d hκ hτU n0 hE ht1 ht10 ht0 h730 (δ := gueDelta τU)
    (fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun N => le_of_eq rfl)
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := gueHyp_highProb_range (P := Pgue d) (2 * n0) _
    (fun n h1 _ => (hI n h1).highProb hτ2)
  have hG2 := gueHyp_highProb_range (P := Pgue d) (2 * n0) _
    (fun n h1 h2 => (gueGrid_loop_duhamel d hκ hτU n0 hE ht1 ht10 ht0 hscale n h1 h2).highProb
      hτ2)
  have hG3 := hD4.highProb hτ2
  filter_upwards [((hG1.inter hG2).inter hG3) D hD, hKtd (τ / 2) hτ2,
    hKtd (τU / 2) (by positivity), hell, hscale, h730, d.dim, gueHyp_ev_grid n0,
    gueHyp_ev_delta hκ hτU hE,
    eventually_le_rpow (2 + 2 ^ (2 * n0) + 7 * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2,
    eventually_ge_atTop 1] with N hGN hKtN hKt1N hellN hscaleN h730N hdimN hgridN hδN hbigN hN1
  refine (measure_mono ?_).trans hGN
  rintro ω ⟨⟨⟨t, ht⟩, ⟨n, ⟨hn2, hn⟩, heven⟩⟩, hp⟩ hω
  obtain ⟨⟨hω1, hω2⟩, hω3⟩ := hω
  obtain ⟨l, hl⟩ := heven
  have hnl : n = 2 * l := by omega
  subst hnl
  have hl1 : 1 ≤ l := by omega
  refine absurd hp (not_lt.2 ?_)
  have hω1' := hω1 (2 * l) (by omega) hn
  have hω2' := hω2 (2 * l) (by omega) hn
  simp only [Set.mem_ofPred_eq] at hω1' hω2' hω3
  set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
  have hc1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) :=
    Real.one_le_rpow (by exact_mod_cast hN1) hτ2.le
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  exact gueHyp_fixed d hτ n0 τU Kt hK N (2 * l) ω
    (fun u => gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N 2 u ω *
      gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N (2 * l) u ω)
    (fun u => Real.sqrt (S⁻¹ * (etaT (E N) u)⁻¹ ^ 2) *
      gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N (2 * l) u ω)
    (Ce := 4 * ((2 * l : ℕ) : ℝ) * (N : ℝ) ^ (τ / 2) * S)
    (hEb N) (ht1 N) (ht10 N) (ht0 N) hN1 (by omega) hn hdimN.1
    (gueHyp_step_le n0 N (hEb N) (ht10 N) (ht0 N) hN1 h730N hτU) hgridN.1 hgridN.2
    (gueHyp_Kt_le_one d hτU n0 N Kt (hEb N) (ht0 N) hN1 hKt1N hscaleN)
    (fun t ht J hJ h2 hJn => hKtN (⟨t, ht⟩, ⟨J, hJ, h2, hJn⟩)) hbigN
    (by positivity)
    (by
      have hl' : (1 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * l)
      have hc0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by linarith
      have : ((2 * l : ℕ) : ℝ) ≤ ((2 * l : ℕ) : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right this (mul_nonneg hc0 hS0)
      nlinarith)
    (fun u _ => mul_nonneg (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _)
      (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    ((gueLproc_continuousOn _ _ _ _ _ _ _ _ _).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    ((gueHyp_sqrt_cont d N (hEb N) (ht0 N)).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun j hj => by
      rw [gueHyp_Lproc_grid d E t1 t0 (gueGridK n0) (gueDelta τU) N (2 * l) j ω (ht10 N) hj]
      exact gueHyp_q_745 (gueH_isHermitian d t1 t0 (gueGridK n0) N j ω) _
        (by positivity) hl1)
    (fun j hj x => by
      rw [gueHyp_Lproc_grid d E t1 t0 (gueGridK n0) (gueDelta τU) N 2 j ω (ht10 N) hj,
        gueHyp_Lproc_grid d E t1 t0 (gueGridK n0) (gueDelta τU) N (2 * l) j ω (ht10 N) hj]
      exact gueHyp_eG_745 d (gueGridK n0) N j ω hc1 hl1
        (gueHyp_entry_le d hκ n0 hE ht10 ht0 N hellN hδN ω (by linarith) hω3 hj) x)
    ht

/-- **(7.46)G at lengths `1 ≤ n ≤ n₀`** for the frozen, interpolated processes: the `h746` of
`eq728G`, over the whole interval `[t₁, t₀]`. -/
theorem gueBds_h746 {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (h730 : ∀ᶠ N : ℕ in atTop, t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N))
    (hscale : ∀ᶠ N : ℕ in atTop, (gueScale d E N (t0 N))⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (hB : BoundsCoreN (sample d) E t1) :
    StochDom (Pgue d)
      (fun N (p : TimeIcc t1 t0 N × Set.Icc 1 n0) ω =>
        gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N p.2 p.1 ω)
      (fun N p ω => GUEPhase.rhs746G (((d.L N * d.W N : ℕ) : ℝ)) (etaT (E N)) (t1 N)
        (fun m t => gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N m t ω)
        (fun m t => gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N m t ω) p.2 p.1) := by
  have hEb : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hI := fun n (hn : 1 ≤ n) =>
    gueHyp_init d (gueGridK n0) ht1 ht10 ht0 hell Kt hKinit hB (t0 := t0) n hn
  have hKtd := gueHyp_Kt_detDom d hκ hτU n0 hE ht10 ht0 h730 hell Kt hKinit hK
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := gueHyp_highProb_range (P := Pgue d) (2 * n0) _
    (fun n h1 _ => (hI n h1).highProb hτ2)
  have hG2 := gueHyp_highProb_range (P := Pgue d) (2 * n0) _
    (fun n h1 h2 => (gueGrid_loop_duhamel d hκ hτU n0 hE ht1 ht10 ht0 hscale n h1 h2).highProb
      hτ2)
  filter_upwards [(hG1.inter hG2) D hD, hKtd (τ / 2) hτ2,
    hKtd (τU / 2) (by positivity), hscale, h730, d.dim, gueHyp_ev_grid n0,
    eventually_le_rpow (2 + 2 ^ (2 * n0) + 7 * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2,
    eventually_ge_atTop 1] with N hGN hKtN hKt1N hscaleN h730N hdimN hgridN hbigN hN1
  refine (measure_mono ?_).trans hGN
  rintro ω ⟨⟨⟨t, ht⟩, ⟨n, hnmem⟩⟩, hp⟩ hω
  obtain ⟨hn1, hn⟩ := hnmem
  obtain ⟨hω1, hω2⟩ := hω
  refine absurd hp (not_lt.2 ?_)
  have hn' : n ≤ 2 * n0 := by omega
  have hω1' := hω1 n hn1 hn'
  have hω2' := hω2 n hn1 hn'
  set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
  have hc1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) :=
    Real.one_le_rpow (by exact_mod_cast hN1) hτ2.le
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  exact gueHyp_fixed d hτ n0 τU Kt hK N n ω
    (fun u => gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N 1 u ω *
      gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N (n + 1) u ω)
    (fun u => Real.sqrt (S⁻¹ * (etaT (E N) u)⁻¹ ^ 2) *
      Real.sqrt (gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N (2 * n) u ω))
    (Ce := (n : ℝ) * S)
    (hEb N) (ht1 N) (ht10 N) (ht0 N) hN1 hn1 hn' hdimN.1
    (gueHyp_step_le n0 N (hEb N) (ht10 N) (ht0 N) hN1 h730N hτU) hgridN.1 hgridN.2
    (gueHyp_Kt_le_one d hτU n0 N Kt (hEb N) (ht0 N) hN1 hKt1N hscaleN)
    (fun t ht J hJ h2 hJn => hKtN (⟨t, ht⟩, ⟨J, hJ, h2, hJn⟩)) hbigN
    (by positivity)
    (by
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hc0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by linarith
      have h1 : (n : ℝ) ≤ 4 * (n : ℝ) ^ 2 * (N : ℝ) ^ (τ / 2) := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 hS0)
    (fun u _ => mul_nonneg (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    ((gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    ((gueHyp_sqrt_cont d N (hEb N) (ht0 N)).mul
      (Real.continuous_sqrt.comp_continuousOn (gueLproc_continuousOn _ _ _ _ _ _ _ _ _)))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun j hj => by
      rw [gueHyp_Lproc_grid d E t1 t0 (gueGridK n0) (gueDelta τU) N (2 * n) j ω (ht10 N) hj,
        ← Real.sqrt_mul (by positivity)])
    (fun j hj x => by
      rw [gueHyp_Dproc_grid d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N 1 j ω (ht10 N) hj,
        gueHyp_Lproc_grid d E t1 t0 (gueGridK n0) (gueDelta τU) N (n + 1) j ω (ht10 N) hj]
      exact gueHyp_eG_746 d (gueGridK n0) n0 (by omega) Kt hKinit hK N j n
        (gueHyp_time_mem (ht10 N) (gueGridK_ne_zero n0 N)
          ((le_of_lt hj).trans (Grid.firstHit_le _ _ _ ω))) ω x)
    ht

end RBM.Gauss.GUEGrid

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseStep
import RBM1D.Flow.GUEPhaseEntry
import RBM1D.Flow.GUEPhaseKTilde
import RBM1D.Gauss.GridStop

/-!
# The GUE-phase random layer's process definitions and structural lemmas

Frozen, interpolated versions of the loop maxima `L^{(m)}`, deviations `D^{(m)}`, and the
deterministic running maximum `K̄^{(m)}` of §7.2's random layer, together with the deterministic
structural facts (the hypotheses `hLDK`, `hDLK`, `hodd` of `RBM.GUEPhase.eq727GE`), the uniform
deterministic bound on `K̃` (`hK`), one auxiliary jump bound on `gueDev`, the `E^{(G)}` norm bound
for the GUE profile, the two consequences of (5.117)/(6.4) used at odd lengths (R6a/R6b), and the
Ward lower bound on `W⁻¹` (A3).
-/

noncomputable section

namespace RBM.Gauss.GUEGrid

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable (d : Dims)

/-! ### Definitions -/

/-- The a-priori threshold `δ_N = N^{-τU/4}` of the stopping. -/
def gueDelta (τU : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(τU / 4))

/-- The tent function at the grid time `u_k`. -/
def gueTent (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (t : ℝ) : ℝ :=
  max 0 (1 - |t - Grid.time t1 t0 K N k| / Grid.step t1 t0 K N)

/-- Piecewise-linear interpolation of grid values `f 0, …, f (K N)` (`f 0` if `Δ = 0`). -/
def gueInterp (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  if Grid.step t1 t0 K N = 0 then f 0
  else ∑ k ∈ Finset.range (K N + 1), f k * gueTent t1 t0 K N k t

/-- `max_{i,j} |(G_k - m)_{ij}|` at the grid step `k`. -/
def gueDev (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d) : ℝ :=
  ⨆ ij : d.Idx N × d.Idx N, ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) -
      mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖

/-- The freezing index: the first grid step with `gueDev ≥ δ_N` (else `K N`). -/
def gueStop (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N : ℕ) (ω : Grid.Ωg d) : ℕ :=
  Grid.firstHit (fun k ω' => gueDev d E t1 t0 K N k ω') (δ N) (K N) ω

/-- `L^{(m)}_k = max_{σ,a} |L_{σ,a}|` at the grid step `k`. -/
def gueLmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N m k : ℕ) (ω : Grid.Ωg d) : ℝ :=
  loopMax (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) m

/-- `D^{(m)}_k = max_{x} |L_x - K̃_x|` at the grid step `k`. -/
def gueDmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (N m k : ℕ) (ω : Grid.Ωg d) : ℝ :=
  ⨆ x : LoopData (d.L N) m, ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω)
      (zt (E N) (Grid.time t1 t0 K N k)) x.idx - Kt N (Grid.time t1 t0 K N k) x.idx‖

/-- `K̄^{(m)}_k = max_{j ≤ k} max_x |K̃(u_j, x)|` (deterministic running maximum). -/
def gueKbar (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (N m k : ℕ) : ℝ :=
  ⨆ j : Fin (k + 1), ⨆ x : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N j) x.idx‖

/-- The frozen, interpolated `Lm` fed to `eq727GE`/`eq728G`. -/
def gueLproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N m : ℕ) (t : ℝ)
    (ω : Grid.Ωg d) : ℝ :=
  gueInterp t1 t0 K N (fun k => gueLmax d E t1 t0 K N m (min k (gueStop d E t1 t0 K δ N ω)) ω) t

/-- The frozen, interpolated `Dm` fed to `eq727GE`/`eq728G`. -/
def gueDproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m : ℕ) (t : ℝ) (ω : Grid.Ωg d) : ℝ :=
  gueInterp t1 t0 K N
    (fun k => gueDmax d E t1 t0 K Kt N m (min k (gueStop d E t1 t0 K δ N ω)) ω) t

/-- The deterministic `Km` fed to `eq727GE`. -/
def gueKproc (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (N m : ℕ) (t : ℝ) : ℝ :=
  gueInterp t1 t0 K N (fun k => gueKbar d t1 t0 K Kt N m k) t

/-! ### Generic helpers for `gueInterp` (private, mirroring a standard tent-function
interpolation pattern). -/

section GueInterpHelpers

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}

private theorem gueTent_nonneg (k : ℕ) (t : ℝ) : 0 ≤ gueTent t1 t0 K N k t :=
  le_max_left _ _

private theorem gueInterp_add (f g : ℕ → ℝ) (t : ℝ) :
    gueInterp t1 t0 K N (fun k => f k + g k) t
      = gueInterp t1 t0 K N f t + gueInterp t1 t0 K N g t := by
  unfold gueInterp
  split_ifs with h0
  · rfl
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

private theorem gueInterp_mono {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) (t : ℝ) :
    gueInterp t1 t0 K N f t ≤ gueInterp t1 t0 K N g t := by
  unfold gueInterp
  split_ifs with h0
  · exact h 0
  · exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k) (gueTent_nonneg k t)

private theorem gueInterp_nonneg {f : ℕ → ℝ} (h : ∀ k, 0 ≤ f k) (t : ℝ) :
    0 ≤ gueInterp t1 t0 K N f t := by
  unfold gueInterp
  split_ifs with h0
  · exact h 0
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (h k) (gueTent_nonneg k t)

private theorem gueTent_continuous (j : ℕ) : Continuous (gueTent t1 t0 K N j) := by
  unfold gueTent
  fun_prop

private theorem gueInterp_continuousOn (f : ℕ → ℝ) :
    ContinuousOn (fun t => gueInterp t1 t0 K N f t) (Set.Icc (t1 N) (t0 N)) := by
  unfold gueInterp
  by_cases h0 : Grid.step t1 t0 K N = 0
  · simp only [if_pos h0]
    exact continuousOn_const
  · simp only [if_neg h0]
    exact (continuous_finset_sum _ fun k _ => continuous_const.mul (gueTent_continuous k)).continuousOn

private theorem gueInterp_sqrt_mul_le {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (t : ℝ) :
    gueInterp t1 t0 K N (fun k => Real.sqrt (a k * b k)) t
      ≤ Real.sqrt (gueInterp t1 t0 K N a t * gueInterp t1 t0 K N b t) := by
  unfold gueInterp
  split_ifs with h0
  · exact le_refl _
  · have hw : ∀ k, 0 ≤ gueTent t1 t0 K N k t := fun k => gueTent_nonneg k t
    rw [Real.sqrt_mul (Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (hw k))]
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.range (K N + 1))
      (f := fun k => a k * gueTent t1 t0 K N k t) (g := fun k => b k * gueTent t1 t0 K N k t)
      (fun k => mul_nonneg (ha k) (hw k)) (fun k => mul_nonneg (hb k) (hw k))
    have heq : ∀ k, Real.sqrt (a k * gueTent t1 t0 K N k t)
        * Real.sqrt (b k * gueTent t1 t0 K N k t)
        = Real.sqrt (a k * b k) * gueTent t1 t0 K N k t := by
      intro k
      rw [← Real.sqrt_mul (mul_nonneg (ha k) (hw k)),
        show a k * gueTent t1 t0 K N k t * (b k * gueTent t1 t0 K N k t)
          = (a k * b k) * (gueTent t1 t0 K N k t) ^ 2 by ring,
        Real.sqrt_mul (mul_nonneg (ha k) (hb k)), Real.sqrt_sq (hw k)]
    calc ∑ k ∈ Finset.range (K N + 1), Real.sqrt (a k * b k) * gueTent t1 t0 K N k t
        = ∑ k ∈ Finset.range (K N + 1),
            Real.sqrt (a k * gueTent t1 t0 K N k t) * Real.sqrt (b k * gueTent t1 t0 K N k t) :=
          Finset.sum_congr rfl fun k _ => (heq k).symm
      _ ≤ Real.sqrt (∑ k ∈ Finset.range (K N + 1), a k * gueTent t1 t0 K N k t) *
            Real.sqrt (∑ k ∈ Finset.range (K N + 1), b k * gueTent t1 t0 K N k t) := hcs

/-- Tent functions form a Kronecker delta at grid points, provided the grid is nondegenerate
(`Δ ≠ 0`) and `t1 N ≤ t0 N` (so `Δ ≥ 0`). -/
private theorem gueTent_time_eq (ht10 : t1 N ≤ t0 N) (hstep : Grid.step t1 t0 K N ≠ 0) (j k : ℕ) :
    gueTent t1 t0 K N j (Grid.time t1 t0 K N k) = if j = k then 1 else 0 := by
  have hK0 : (K N : ℝ) ≠ 0 := by
    intro hc
    apply hstep
    unfold Grid.step
    rw [hc, div_zero]
  have hKpos : (0:ℝ) < (K N : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hK0)
  have hΔ0 : 0 ≤ Grid.step t1 t0 K N := by
    unfold Grid.step
    exact div_nonneg (by linarith) hKpos.le
  have hΔpos : 0 < Grid.step t1 t0 K N := hΔ0.lt_of_ne (Ne.symm hstep)
  have hdiff : Grid.time t1 t0 K N k - Grid.time t1 t0 K N j
      = ((k : ℝ) - (j : ℝ)) * Grid.step t1 t0 K N := by
    unfold Grid.time; ring
  have habs : |Grid.time t1 t0 K N k - Grid.time t1 t0 K N j|
      = |(k : ℝ) - (j : ℝ)| * Grid.step t1 t0 K N := by
    rw [hdiff, abs_mul, abs_of_pos hΔpos]
  unfold gueTent
  rw [habs, mul_div_assoc, div_self hΔpos.ne', mul_one]
  by_cases hjk : j = k
  · simp [hjk]
  · have h1 : (1 : ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
      have hne : (k : ℝ) ≠ (j : ℝ) := by
        intro hc; exact hjk (by exact_mod_cast hc.symm)
      rcases lt_or_gt_of_ne hne with h | h
      · rw [abs_of_neg (by linarith)]
        have : (1:ℝ) ≤ (j:ℝ) - (k:ℝ) := by
          have hlt : (k:ℕ) < (j:ℕ) := by exact_mod_cast (by linarith : (k:ℝ) < (j:ℝ))
          have : (k:ℕ) + 1 ≤ (j:ℕ) := hlt
          have := (Nat.cast_le (α := ℝ)).2 this
          push_cast at this
          linarith
        linarith
      · rw [abs_of_pos (by linarith)]
        have hlt : (j:ℕ) < (k:ℕ) := by exact_mod_cast (by linarith : (j:ℝ) < (k:ℝ))
        have hle : (j:ℕ) + 1 ≤ (k:ℕ) := hlt
        have := (Nat.cast_le (α := ℝ)).2 hle
        push_cast at this
        linarith
    simp only [hjk, if_false]
    have : 1 - |(k:ℝ) - (j:ℝ)| ≤ 0 := by linarith
    rw [max_eq_left_iff.2 this]

private theorem gueInterp_time {f : ℕ → ℝ} (hconst : Grid.step t1 t0 K N = 0 → ∀ k', f k' = f 0)
    (ht10 : t1 N ≤ t0 N) {k : ℕ} (hk : k ≤ K N) :
    gueInterp t1 t0 K N f (Grid.time t1 t0 K N k) = f k := by
  unfold gueInterp
  split_ifs with h0
  · exact (hconst h0 k).symm
  · rw [Finset.sum_eq_single k]
    · rw [gueTent_time_eq ht10 h0 k k, if_pos rfl, mul_one]
    · intro j hj hjk
      rw [gueTent_time_eq ht10 h0 j k, if_neg hjk, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.2 (by omega)) hk'

end GueInterpHelpers

/-! ### Constancy of the grid processes when `Δ = 0` -/

section GueConstZero

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}

private theorem gueTime_const_of_step_zero (h0 : Grid.step t1 t0 K N = 0) (k : ℕ) :
    Grid.time t1 t0 K N k = t1 N := by
  unfold Grid.time; rw [h0]; ring

private theorem gueH_const_of_step_zero (h0 : Grid.step t1 t0 K N = 0) (k : ℕ) (ω : Grid.Ωg d) :
    gueH d t1 t0 K N k ω = gueH d t1 t0 K N 0 ω := by
  unfold gueH
  rw [h0, zero_div, Real.sqrt_zero]
  simp

variable {E : ℕ → ℝ}

private theorem gueLmax_const_of_step_zero (h0 : Grid.step t1 t0 K N = 0) (m k : ℕ)
    (ω : Grid.Ωg d) :
    gueLmax d E t1 t0 K N m k ω = gueLmax d E t1 t0 K N m 0 ω := by
  unfold gueLmax
  rw [gueH_const_of_step_zero d h0 k ω, gueTime_const_of_step_zero h0 k,
    gueTime_const_of_step_zero h0 0]

private theorem gueDmax_const_of_step_zero (h0 : Grid.step t1 t0 K N = 0)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (m k : ℕ) (ω : Grid.Ωg d) :
    gueDmax d E t1 t0 K Kt N m k ω = gueDmax d E t1 t0 K Kt N m 0 ω := by
  unfold gueDmax
  rw [gueH_const_of_step_zero d h0 k ω, gueTime_const_of_step_zero h0 k,
    gueTime_const_of_step_zero h0 0]

end GueConstZero

/-! ### Pointwise triangle-inequality helpers -/

section GueTriangle

private theorem norm_le_norm_sub_add_norm {α : Type*} [SeminormedAddGroup α] (a b : α) :
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  calc ‖a‖ = ‖a - b + b‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _

private theorem le_ciSup_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ j, f j :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) i

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {E : ℕ → ℝ}

private theorem gueLmax_le_gueDmax_add_gueKbar (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (N m k' k : ℕ) (hk' : k' ≤ k) (ω : Grid.Ωg d) :
    gueLmax d E t1 t0 K N m k' ω ≤ gueDmax d E t1 t0 K Kt N m k' ω + gueKbar d t1 t0 K Kt N m k := by
  unfold gueLmax gueDmax gueKbar loopMax
  apply ciSup_le
  intro x
  have h1 := norm_le_norm_sub_add_norm
    (gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω) (zt (E N) (Grid.time t1 t0 K N k'))
      (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N))))
    (Kt N (Grid.time t1 t0 K N k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N))))
  have h2 : ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω) (zt (E N) (Grid.time t1 t0 K N k'))
        (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N)))
      - Kt N (Grid.time t1 t0 K N k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N)))‖
      ≤ ⨆ y : LoopData (d.L N) m, ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω)
          (zt (E N) (Grid.time t1 t0 K N k')) y.idx - Kt N (Grid.time t1 t0 K N k') y.idx‖ :=
    le_ciSup_finite (fun y : LoopData (d.L N) m => ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω)
        (zt (E N) (Grid.time t1 t0 K N k')) y.idx - Kt N (Grid.time t1 t0 K N k') y.idx‖)
      (⟨x.1, x.2⟩ : LoopData (d.L N) m)
  have h3 : ‖Kt N (Grid.time t1 t0 K N k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N)))‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N j) y.idx‖ := by
    have hjk : (⟨k', by omega⟩ : Fin (k + 1)) = (⟨k', by omega⟩ : Fin (k + 1)) := rfl
    calc ‖Kt N (Grid.time t1 t0 K N k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N)))‖
        ≤ ⨆ y : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N k') y.idx‖ :=
          le_ciSup_finite (fun y : LoopData (d.L N) m => ‖Kt N (Grid.time t1 t0 K N k') y.idx‖)
            (⟨x.1, x.2⟩ : LoopData (d.L N) m)
      _ ≤ ⨆ j : Fin (k + 1), ⨆ y : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N j) y.idx‖ :=
          le_ciSup_finite (fun j : Fin (k + 1) => ⨆ y : LoopData (d.L N) m,
              ‖Kt N (Grid.time t1 t0 K N j) y.idx‖)
            (⟨k', by omega⟩ : Fin (k + 1))
  linarith [h1, h2, h3]

private theorem gueDmax_le_gueLmax_add_gueKbar (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (N m k' k : ℕ) (hk' : k' ≤ k) (ω : Grid.Ωg d) :
    gueDmax d E t1 t0 K Kt N m k' ω ≤ gueLmax d E t1 t0 K N m k' ω + gueKbar d t1 t0 K Kt N m k := by
  unfold gueDmax gueLmax loopMax gueKbar
  apply ciSup_le
  intro x
  have h1 := norm_sub_le
    (gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω) (zt (E N) (Grid.time t1 t0 K N k')) x.idx)
    (Kt N (Grid.time t1 t0 K N k') x.idx)
  have h2 : ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω) (zt (E N) (Grid.time t1 t0 K N k'))
        x.idx‖
      ≤ ⨆ y : (Fin m → Bool) × (Fin m → ZMod (d.L N)),
          ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω) (zt (E N) (Grid.time t1 t0 K N k'))
            ⟨List.ofFn y.1, List.ofFn y.2⟩‖ :=
    le_ciSup_finite (fun y : (Fin m → Bool) × (Fin m → ZMod (d.L N)) =>
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k' ω) (zt (E N) (Grid.time t1 t0 K N k'))
          ⟨List.ofFn y.1, List.ofFn y.2⟩‖)
      (⟨x.1, x.2⟩ : (Fin m → Bool) × (Fin m → ZMod (d.L N)))
  have h3 : ‖Kt N (Grid.time t1 t0 K N k') x.idx‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N j) y.idx‖ := by
    calc ‖Kt N (Grid.time t1 t0 K N k') x.idx‖
        ≤ ⨆ y : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N k') y.idx‖ :=
          le_ciSup_finite (fun y : LoopData (d.L N) m => ‖Kt N (Grid.time t1 t0 K N k') y.idx‖) x
      _ ≤ ⨆ j : Fin (k + 1), ⨆ y : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N j) y.idx‖ :=
          le_ciSup_finite (fun j : Fin (k + 1) => ⨆ y : LoopData (d.L N) m,
              ‖Kt N (Grid.time t1 t0 K N j) y.idx‖)
            (⟨k', by omega⟩ : Fin (k + 1))
  linarith [h1, h2, h3]

private theorem gueLmax_odd_sq_le (N l k : ℕ) (hl : 1 ≤ l) (ω : Grid.Ωg d) :
    gueLmax d E t1 t0 K N (2 * l + 1) k ω ≤
      Real.sqrt (gueLmax d E t1 t0 K N (2 * l) k ω * gueLmax d E t1 t0 K N (2 * l + 2) k ω) := by
  unfold gueLmax
  exact Real.le_sqrt_of_sq_le (loopMax_odd_sq_le (gueH_isHermitian d t1 t0 K N k ω) hl)

end GueTriangle

/-! ### Main theorems -/

theorem gueLproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N m : ℕ) (t : ℝ)
    (ω : Grid.Ωg d) : 0 ≤ gueLproc d E t1 t0 K δ N m t ω := by
  unfold gueLproc
  exact gueInterp_nonneg (fun k => by unfold gueLmax; exact loopMax_nonneg m) t

theorem gueDproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m : ℕ) (t : ℝ) (ω : Grid.Ωg d) :
    0 ≤ gueDproc d E t1 t0 K δ Kt N m t ω := by
  unfold gueDproc
  exact gueInterp_nonneg
    (fun k => by unfold gueDmax; exact Real.iSup_nonneg fun _ => norm_nonneg _) t

theorem gueLproc_continuousOn (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N m : ℕ)
    (ω : Grid.Ωg d) :
    ContinuousOn (fun t => gueLproc d E t1 t0 K δ N m t ω) (Set.Icc (t1 N) (t0 N)) := by
  unfold gueLproc
  exact gueInterp_continuousOn _

theorem gueDproc_continuousOn (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m : ℕ) (ω : Grid.Ωg d) :
    ContinuousOn (fun t => gueDproc d E t1 t0 K δ Kt N m t ω) (Set.Icc (t1 N) (t0 N)) := by
  unfold gueDproc
  exact gueInterp_continuousOn _

/-- The hypothesis `hLDK` of `RBM.GUEPhase.eq727GE` for the frozen processes: `L ≤ D + K̄` at
every `t` and every `ω`. -/
theorem gueLproc_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m : ℕ) (t : ℝ) (ω : Grid.Ωg d) :
    gueLproc d E t1 t0 K δ N m t ω ≤ gueDproc d E t1 t0 K δ Kt N m t ω + gueKproc d t1 t0 K Kt N m t := by
  unfold gueLproc gueDproc gueKproc
  rw [← gueInterp_add]
  exact gueInterp_mono
    (fun k => gueLmax_le_gueDmax_add_gueKbar d Kt N m (min k (gueStop d E t1 t0 K δ N ω)) k
      (min_le_left _ _) ω) t

/-- The hypothesis `hDLK` of `RBM.GUEPhase.eq727GE` for the frozen processes: `D ≤ L + K̄` at
every `t` and every `ω`. -/
theorem gueDproc_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m : ℕ) (t : ℝ) (ω : Grid.Ωg d) :
    gueDproc d E t1 t0 K δ Kt N m t ω ≤ gueLproc d E t1 t0 K δ N m t ω + gueKproc d t1 t0 K Kt N m t := by
  unfold gueDproc gueLproc gueKproc
  rw [← gueInterp_add]
  exact gueInterp_mono
    (fun k => gueDmax_le_gueLmax_add_gueKbar d Kt N m (min k (gueStop d E t1 t0 K δ N ω)) k
      (min_le_left _ _) ω) t

/-- The hypothesis `hodd` of `RBM.GUEPhase.eq727GE` for the frozen processes: (6.4) at the grid,
Cauchy–Schwarz for the tent weights. -/
theorem gueLproc_odd (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N l : ℕ) (hl : 1 ≤ l) (t : ℝ)
    (ω : Grid.Ωg d) :
    gueLproc d E t1 t0 K δ N (2 * l + 1) t ω ≤
      Real.sqrt (gueLproc d E t1 t0 K δ N (2 * l) t ω * gueLproc d E t1 t0 K δ N (2 * l + 2) t ω) := by
  unfold gueLproc
  set σ := gueStop d E t1 t0 K δ N ω with hσ
  calc gueInterp t1 t0 K N (fun k => gueLmax d E t1 t0 K N (2 * l + 1) (min k σ) ω) t
      ≤ gueInterp t1 t0 K N (fun k => Real.sqrt (gueLmax d E t1 t0 K N (2 * l) (min k σ) ω *
          gueLmax d E t1 t0 K N (2 * l + 2) (min k σ) ω)) t :=
        gueInterp_mono (fun k => gueLmax_odd_sq_le d N l (min k σ) hl ω) t
    _ ≤ Real.sqrt (gueInterp t1 t0 K N (fun k => gueLmax d E t1 t0 K N (2 * l) (min k σ) ω) t *
          gueInterp t1 t0 K N (fun k => gueLmax d E t1 t0 K N (2 * l + 2) (min k σ) ω) t) :=
        gueInterp_sqrt_mul_le (fun k => by unfold gueLmax; exact loopMax_nonneg _)
          (fun k => by unfold gueLmax; exact loopMax_nonneg _) t

/-- Grid values of `gueLproc`. -/
theorem gueLproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (N m k : ℕ)
    (ht10 : t1 N ≤ t0 N) (hk : k ≤ K N) (ω : Grid.Ωg d) :
    gueLproc d E t1 t0 K δ N m (Grid.time t1 t0 K N k) ω =
      gueLmax d E t1 t0 K N m (min k (gueStop d E t1 t0 K δ N ω)) ω := by
  unfold gueLproc
  refine gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [gueLmax_const_of_step_zero d h0 m (min k' (gueStop d E t1 t0 K δ N ω)) ω, Nat.zero_min]

/-- Grid values of `gueDproc`. -/
theorem gueDproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N m k : ℕ) (ht10 : t1 N ≤ t0 N) (hk : k ≤ K N)
    (ω : Grid.Ωg d) :
    gueDproc d E t1 t0 K δ Kt N m (Grid.time t1 t0 K N k) ω =
      gueDmax d E t1 t0 K Kt N m (min k (gueStop d E t1 t0 K δ N ω)) ω := by
  unfold gueDproc
  refine gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [gueDmax_const_of_step_zero d h0 Kt m (min k' (gueStop d E t1 t0 K δ N ω)) ω, Nat.zero_min]

/-! ### `d`-free structural facts (R6a/R6b, A3, `norm_eGtermGUE_le`, `gueDev_succ_le`) -/

/-- **(R6a)**: for even length `2l`, `L_{2l+1} ≤ √L₂ · L_{2l}` ((6.4) + (5.117)). -/
theorem gueLoopMax_odd_succ_le {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    loopMax L W H z (2 * l + 1) ≤ Real.sqrt (loopMax L W H z 2) * loopMax L W H z (2 * l) := by
  have h0 := loopMax_two_mul_add_le (z := z) hH hl (le_refl 1)
  have h1 : loopMax L W H z (2 * l + 2) ≤ loopMax L W H z (2 * l) * loopMax L W H z 2 := by
    have e1 : 2 * (l + 1) = 2 * l + 2 := by ring
    have e2 : 2 * 1 = 2 := by norm_num
    rwa [e1, e2] at h0
  have h2 := loopMax_odd_sq_le (z := z) hH hl
  have h3 : loopMax L W H z (2 * l + 1) ^ 2
      ≤ loopMax L W H z (2 * l) * (loopMax L W H z (2 * l) * loopMax L W H z 2) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (loopMax_nonneg _))
  have h4 : loopMax L W H z (2 * l + 1) ^ 2
      ≤ (loopMax L W H z (2 * l)) ^ 2 * loopMax L W H z 2 := by nlinarith [h3]
  calc loopMax L W H z (2 * l + 1)
      ≤ Real.sqrt ((loopMax L W H z (2 * l)) ^ 2 * loopMax L W H z 2) :=
        Real.le_sqrt_of_sq_le h4
    _ = Real.sqrt (loopMax L W H z 2 * (loopMax L W H z (2 * l)) ^ 2) := by rw [mul_comm]
    _ = Real.sqrt (loopMax L W H z 2) * Real.sqrt ((loopMax L W H z (2 * l)) ^ 2) :=
        Real.sqrt_mul (loopMax_nonneg _) _
    _ = Real.sqrt (loopMax L W H z 2) * loopMax L W H z (2 * l) := by
        rw [Real.sqrt_sq (loopMax_nonneg _)]

/-- **(R6b)**: for even length `2l`, `L_{4l} ≤ L_{2l}²` ((5.117)). -/
theorem gueLoopMax_four_mul_le {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    loopMax L W H z (4 * l) ≤ loopMax L W H z (2 * l) ^ 2 := by
  have h := loopMax_two_mul_add_le (z := z) hH hl hl
  have e : 4 * l = 2 * (l + l) := by ring
  rw [e, sq]
  exact h

/-- **A3**: the Ward lower bound turns `W⁻¹` into `2 L₂` on the a-priori event (with `hell`). -/
theorem gue_inv_W_le_loopMax {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) {E u : ℝ}
    (hE : |E| < 2) (hu : u < 1) (hell : (L : ℝ) ^ 2 * (1 - u) ≤ 1) {δ : ℝ}
    (hΩ : GoodEvent (green H (zt E u)) (mE E) δ) (hδ : δ ≤ (mE E).im / 2) :
    ((W : ℕ) : ℝ)⁻¹ ≤ 2 * loopMax L W H (zt E u) 2 := by
  have him : 0 < (mE E).im := mE_im_pos hE
  have hzeq : (zt E u).im = (1 - u) * (mE E).im := zt_im E u
  have h1u : 0 < 1 - u := by linarith
  have hzim : 0 < (zt E u).im := by rw [hzeq]; exact mul_pos h1u him
  have hward := gueEntry_inv_Meta_le hH hzim him hΩ hδ
  have hLmax := gueEntry_Lmax_le_loopMax (H := H) (zt E u)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hstep : (1 : ℝ) / (((L * W : ℕ) : ℝ) * (zt E u).im)
      ≤ 2 / (mE E).im * loopMax L W H (zt E u) 2 := by
    refine hward.trans ?_
    exact mul_le_mul_of_nonneg_left hLmax (by positivity)
  have hmulpos : 0 < (L : ℝ) * (1 - u) * (mE E).im := by positivity
  have heq1 : (L : ℝ) * (1 - u) * (mE E).im * (1 / (((L * W : ℕ) : ℝ) * (zt E u).im))
      = ((W : ℕ) : ℝ)⁻¹ := by
    rw [hzeq]; push_cast; field_simp
  have heq2 : (L : ℝ) * (1 - u) * (mE E).im * (2 / (mE E).im * loopMax L W H (zt E u) 2)
      = 2 * (L : ℝ) * (1 - u) * loopMax L W H (zt E u) 2 := by
    field_simp
  have key : ((W : ℕ) : ℝ)⁻¹ ≤ 2 * (L : ℝ) * (1 - u) * loopMax L W H (zt E u) 2 := by
    calc ((W : ℕ) : ℝ)⁻¹
        = (L : ℝ) * (1 - u) * (mE E).im * (1 / (((L * W : ℕ) : ℝ) * (zt E u).im)) := heq1.symm
      _ ≤ (L : ℝ) * (1 - u) * (mE E).im * (2 / (mE E).im * loopMax L W H (zt E u) 2) :=
          mul_le_mul_of_nonneg_left hstep hmulpos.le
      _ = 2 * (L : ℝ) * (1 - u) * loopMax L W H (zt E u) 2 := heq2
  have hLL2 : (L : ℝ) * (1 - u) ≤ (L : ℝ) ^ 2 * (1 - u) :=
    mul_le_mul_of_nonneg_right (by nlinarith) h1u.le
  have hfin : (L : ℝ) * (1 - u) ≤ 1 := hLL2.trans hell
  calc ((W : ℕ) : ℝ)⁻¹ ≤ 2 * (L : ℝ) * (1 - u) * loopMax L W H (zt E u) 2 := key
    _ ≤ 2 * 1 * loopMax L W H (zt E u) 2 := by
        apply mul_le_mul_of_nonneg_right _ (loopMax_nonneg _)
        nlinarith
    _ = 2 * loopMax L W H (zt E u) 2 := by ring

/-- **E^{(G)} of the GUE profile** (`SBgue = 1/L`): `|Ẽ_GUE(x)| ≤ n · (L W) · ε · B`. -/
theorem norm_eGtermGUE_le (L W : ℕ) [NeZero L] [NeZero W] (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) {ε B : ℝ}
    (hε : ∀ (σ : Bool) (a : ZMod L), ‖Matrix.trace ((Gsig M z σ -
      m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)‖ ≤ ε)
    (hB : ∀ k ∈ Finset.Icc 1 I.length, ∀ b : ZMod L, ‖gloop L W M z (I.cutGlue k b)‖ ≤ B) :
    ‖eGtermGUE L W m M z I‖ ≤ (I.length : ℝ) * ((L * W : ℕ) : ℝ) * ε * B := by
  rcases Nat.eq_zero_or_pos I.length with hn0 | hn1
  · have hSempty : Finset.Icc 1 I.length = (∅ : Finset ℕ) := by
      rw [hn0]; exact Finset.Icc_eq_empty (by omega)
    unfold eGtermGUE
    rw [hSempty]
    simp [hn0]
  · have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε true 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (Finset.mem_Icc.2 ⟨le_refl 1, hn1⟩) 0)
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ a b : ZMod L,
        ‖Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖
        ≤ ε * (L : ℝ)⁻¹ * B := by
      intro k hk a b
      rw [norm_mul, norm_mul]
      have h1 := hε (I.σ.getD (k - 1) true) a
      have h2 : ‖GUEPhase.SBgue L a b‖ = (L : ℝ)⁻¹ := by
        rw [GUEPhase.SBgue_apply, norm_inv, Complex.norm_natCast]
      have h3 := hB k hk b
      rw [h2]
      have e1 : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
      calc ‖Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
              - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a)‖ * (L : ℝ)⁻¹ * ‖gloop L W M z (I.cutGlue k b)‖
          ≤ ε * (L : ℝ)⁻¹ * ‖gloop L W M z (I.cutGlue k b)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 e1) (norm_nonneg _)
        _ ≤ ε * (L : ℝ)⁻¹ * B := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hTk : ∀ k ∈ Finset.Icc 1 I.length,
        ‖∑ a : ZMod L, ∑ b : ZMod L, Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖
        ≤ (L : ℝ) * ((L : ℝ) * (ε * (L : ℝ)⁻¹ * B)) := by
      intro k hk
      calc ‖∑ a : ZMod L, ∑ b : ZMod L, Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
              - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖
          ≤ ∑ a : ZMod L, ‖∑ b : ZMod L, Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
              - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _a : ZMod L, (L : ℝ) * (ε * (L : ℝ)⁻¹ * B) := by
            apply Finset.sum_le_sum
            intro a _
            calc ‖∑ b : ZMod L, Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
                    - m (I.σ.getD (k - 1) true)
                      • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
                  * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖
                ≤ ∑ b : ZMod L, ‖Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
                    - m (I.σ.getD (k - 1) true)
                      • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
                  * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ b : ZMod L, ε * (L : ℝ)⁻¹ * B := Finset.sum_le_sum fun b _ => hterm k hk a b
              _ = (L : ℝ) * (ε * (L : ℝ)⁻¹ * B) := by
                  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        _ = (L : ℝ) * ((L : ℝ) * (ε * (L : ℝ)⁻¹ * B)) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    unfold eGtermGUE
    rw [norm_mul, Complex.norm_natCast]
    calc (W : ℝ) * ‖∑ k ∈ Finset.Icc 1 I.length, ∑ a : ZMod L, ∑ b : ZMod L,
            Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
                - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
              * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖
        ≤ (W : ℝ) * ∑ k ∈ Finset.Icc 1 I.length, ‖∑ a : ZMod L, ∑ b : ZMod L,
            Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
                - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
              * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
      _ ≤ (W : ℝ) * ∑ _k ∈ Finset.Icc 1 I.length, (L : ℝ) * ((L : ℝ) * (ε * (L : ℝ)⁻¹ * B)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hTk) (Nat.cast_nonneg _)
      _ = (W : ℝ) * ((I.length : ℝ) * ((L : ℝ) * ((L : ℝ) * (ε * (L : ℝ)⁻¹ * B)))) := by
          have hcard : (Finset.Icc 1 I.length).card = I.length := by
            rw [Nat.card_Icc]; omega
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = (I.length : ℝ) * ((L * W : ℕ) : ℝ) * ε * B := by
          push_cast
          field_simp

/-- The `ℓ²`-operator norm of any complex matrix is bounded by its entrywise `ℓ¹` sum
(a private consequence of `RBM.Gauss.l2_opNorm_sq_le_frobSq`). -/
private theorem opNorm_le_sum_norm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ‖A‖ ≤ ∑ i : n, ∑ j : n, ‖A i j‖ := by
  have hfrob := RBM.Gauss.l2_opNorm_sq_le_frobSq A
  have hrow : ∀ i : n, ∑ j : n, ‖A i j‖ ^ 2 ≤ (∑ j : n, ‖A i j‖) ^ 2 :=
    fun i => Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
  have hcol : ∑ i : n, (∑ j : n, ‖A i j‖) ^ 2 ≤ (∑ i : n, ∑ j : n, ‖A i j‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hfrobsum : RBM.Gauss.frobSq A ≤ (∑ i : n, ∑ j : n, ‖A i j‖) ^ 2 := by
    unfold RBM.Gauss.frobSq
    exact (Finset.sum_le_sum fun i _ => hrow i).trans hcol
  have h2 : ‖A‖ ^ 2 ≤ (∑ i : n, ∑ j : n, ‖A i j‖) ^ 2 := hfrob.trans hfrobsum
  have hsum_nonneg : (0 : ℝ) ≤ ∑ i : n, ∑ j : n, ‖A i j‖ := by positivity
  have := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg A), Real.sqrt_sq hsum_nonneg] at this

/-- **One-step change of the entry deviation** (row J2): resolvent identity,
`‖G' - G‖ ≤ η'^{-1} η^{-1} (√(Δ/S) ‖X_{k+1}‖ + |z' - z|)`, `η ≥ η_{t₀}`. -/
theorem gueDev_succ_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (hE : |E N| < 2)
    (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hk : k < K N) (ω : Grid.Ωg d) :
    gueDev d E t1 t0 K N (k + 1) ω ≤ gueDev d E t1 t0 K N k ω +
      (etaT (E N) (t0 N))⁻¹ ^ 2 * (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) *
        ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ + Grid.step t1 t0 K N) := by
  have hKne : K N ≠ 0 := by omega
  have hstep0 : 0 ≤ Grid.step t1 t0 K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have htimemono : ∀ {i j : ℕ}, i ≤ j → Grid.time t1 t0 K N i ≤ Grid.time t1 t0 K N j := by
    intro i j hij
    unfold Grid.time
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith [hstep0]
  have htimeK : Grid.time t1 t0 K N (K N) = t0 N := Grid.time_last t1 t0 K N hKne
  have htk : Grid.time t1 t0 K N k ≤ t0 N := htimeK ▸ htimemono (by omega : k ≤ K N)
  have htk1 : Grid.time t1 t0 K N (k + 1) ≤ t0 N := htimeK ▸ htimemono (by omega : k + 1 ≤ K N)
  have him : 0 < (mE (E N)).im := mE_im_pos hE
  have hetak : etaT (E N) (t0 N) ≤ etaT (E N) (Grid.time t1 t0 K N k) := by
    unfold etaT; nlinarith [htk]
  have hetak1 : etaT (E N) (t0 N) ≤ etaT (E N) (Grid.time t1 t0 K N (k + 1)) := by
    unfold etaT; nlinarith [htk1]
  have het0pos : 0 < etaT (E N) (t0 N) := by unfold etaT; nlinarith [ht0]
  have hzkim : (zt (E N) (Grid.time t1 t0 K N k)).im = etaT (E N) (Grid.time t1 t0 K N k) :=
    zt_im (E N) (Grid.time t1 t0 K N k)
  have hzk1im : (zt (E N) (Grid.time t1 t0 K N (k + 1))).im
      = etaT (E N) (Grid.time t1 t0 K N (k + 1)) := zt_im (E N) (Grid.time t1 t0 K N (k + 1))
  have hzkim0 : (zt (E N) (Grid.time t1 t0 K N k)).im ≠ 0 := by rw [hzkim]; linarith
  have hzk1im0 : (zt (E N) (Grid.time t1 t0 K N (k + 1))).im ≠ 0 := by rw [hzk1im]; linarith
  have hHk := gueH_isHermitian d t1 t0 K N k ω
  have hHk1 := gueH_isHermitian d t1 t0 K N (k + 1) ω
  have hetakpos : 0 < etaT (E N) (Grid.time t1 t0 K N k) := lt_of_lt_of_le het0pos hetak
  have hetak1pos : 0 < etaT (E N) (Grid.time t1 t0 K N (k + 1)) := lt_of_lt_of_le het0pos hetak1
  have hGk_le : ‖green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))‖
      ≤ (etaT (E N) (t0 N))⁻¹ :=
    RBM.Gauss.norm_green_le hHk het0pos (by rw [hzkim, abs_of_pos hetakpos]; exact hetak)
  have hGk1_le : ‖green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))‖
      ≤ (etaT (E N) (t0 N))⁻¹ :=
    RBM.Gauss.norm_green_le hHk1 het0pos (by rw [hzk1im, abs_of_pos hetak1pos]; exact hetak1)
  have hHdiff : gueH d t1 t0 K N (k + 1) ω - gueH d t1 t0 K N k ω
      = (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ) • Xmat d N (ω (k + 1)) := by
    unfold gueH
    have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp), smul_add]
    abel
  have hHnorm : ‖gueH d t1 t0 K N (k + 1) ω - gueH d t1 t0 K N k ω‖
      ≤ Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ))
        * ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ := by
    rw [hHdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (opNorm_le_sum_norm _) (Real.sqrt_nonneg _)
  have hzdiff : zt (E N) (Grid.time t1 t0 K N (k + 1)) - zt (E N) (Grid.time t1 t0 K N k)
      = (-(Grid.step t1 t0 K N : ℂ)) * mE (E N) := by
    unfold zt Grid.time
    push_cast
    ring
  have hznorm : ‖zt (E N) (Grid.time t1 t0 K N (k + 1)) - zt (E N) (Grid.time t1 t0 K N k)‖
      = Grid.step t1 t0 K N := by
    rw [hzdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hstep0,
      norm_mE (by linarith [abs_lt.mp hE]), mul_one]
  have hAZ : ‖gueH d t1 t0 K N (k + 1) ω - gueH d t1 t0 K N k ω‖
        + ‖zt (E N) (Grid.time t1 t0 K N (k + 1)) - zt (E N) (Grid.time t1 t0 K N k)‖
      ≤ Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) *
          ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ + Grid.step t1 t0 K N := by
    rw [hznorm]; exact add_le_add hHnorm (le_refl _)
  have hAZ0 : 0 ≤ ‖gueH d t1 t0 K N (k + 1) ω - gueH d t1 t0 K N k ω‖
        + ‖zt (E N) (Grid.time t1 t0 K N (k + 1)) - zt (E N) (Grid.time t1 t0 K N k)‖ := by
    positivity
  have hRHS0 : 0 ≤ Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) *
      ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ + Grid.step t1 t0 K N := by
    have : (0:ℝ) ≤ ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ := by positivity
    positivity
  have hGdiff := norm_green_sub_le hHk1 hHk hzk1im0 hzkim0
  have hop : ‖green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
        - green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))‖
      ≤ (etaT (E N) (t0 N))⁻¹ ^ 2 *
        (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) *
          ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ + Grid.step t1 t0 K N) := by
    have hη0 : 0 ≤ (etaT (E N) (t0 N))⁻¹ := by positivity
    calc ‖green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
            - green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))‖
        ≤ ‖green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))‖
            * (‖gueH d t1 t0 K N (k + 1) ω - gueH d t1 t0 K N k ω‖
              + ‖zt (E N) (Grid.time t1 t0 K N (k + 1)) - zt (E N) (Grid.time t1 t0 K N k)‖)
            * ‖green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))‖ := hGdiff
      _ ≤ (etaT (E N) (t0 N))⁻¹
            * (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) *
                ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ + Grid.step t1 t0 K N)
            * (etaT (E N) (t0 N))⁻¹ := by
          apply mul_le_mul (mul_le_mul hGk1_le hAZ hAZ0 hη0) hGk_le (norm_nonneg _)
          positivity
      _ = (etaT (E N) (t0 N))⁻¹ ^ 2 *
            (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) *
              ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N (ω (k + 1)) i j‖ + Grid.step t1 t0 K N) := by
          ring
  unfold gueDev
  apply ciSup_le
  intro ij
  have heq : (green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
        - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2
      = (green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
          - green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))) ij.1 ij.2
        + (green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))
            - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2 := by
    simp only [Matrix.sub_apply]
    ring
  have hE1 : ‖(green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
        - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖
      ≤ ‖(green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
          - green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))) ij.1 ij.2‖
        + ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))
            - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖ := by
    rw [heq]; exact norm_add_le _ _
  have hE2 : ‖(green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
        - green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))) ij.1 ij.2‖
      ≤ ‖green (gueH d t1 t0 K N (k + 1) ω) (zt (E N) (Grid.time t1 t0 K N (k + 1)))
          - green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))‖ :=
    norm_apply_le_l2_opNorm _ ij.1 ij.2
  have hE3 : ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))
        - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖
      ≤ ⨆ ij' : d.Idx N × d.Idx N, ‖(green (gueH d t1 t0 K N k ω)
          (zt (E N) (Grid.time t1 t0 K N k))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij'.1 ij'.2‖ :=
    le_ciSup_finite (fun ij' : d.Idx N × d.Idx N =>
        ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij'.1 ij'.2‖) ij
  linarith [hE1, hE2, hE3, hop]

/-! ### `gueKproc_unifDetDom`: the deterministic bound on `K̃`, interpolated -/

section GueKprocDom

/-- Two nearby continuum points give comparable values of the (affine, decreasing) scale
`lam N t = M (1 - t) (Im m)`, provided the gap is dominated by the value at the right endpoint
`t0` (a private real-analysis fact, the algebraic core of the interpolation between grid
times). -/
private theorem gueLam_near_le {M im0 t t' t0 Δ : ℝ} (hM : 0 ≤ M) (him0 : 0 ≤ im0)
    (him1 : im0 ≤ 1) (ht' : t' ≤ t0) (hclose : |t - t'| ≤ Δ)
    (hsmall : M * Δ ≤ M * (1 - t0) * im0) :
    M * (1 - t) * im0 ≤ 2 * (M * (1 - t') * im0) := by
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hclose
  have hMim0 : 0 ≤ M * im0 := mul_nonneg hM him0
  have hLt0t' : M * (1 - t0) * im0 ≤ M * (1 - t') * im0 := by
    have h : M * im0 * (t0 - t') ≥ 0 := mul_nonneg hMim0 (by linarith)
    nlinarith [h]
  have habs1 := abs_le.mp hclose
  have hb0 : M * im0 * (t - t') ≤ M * im0 * Δ := mul_le_mul_of_nonneg_left habs1.2 hMim0
  have hb1 : M * im0 * (t - t') ≤ M * Δ := by
    have hstep : M * im0 * Δ ≤ M * Δ := by
      have hle : M * im0 ≤ M * 1 := mul_le_mul_of_nonneg_left him1 hM
      nlinarith [mul_le_mul_of_nonneg_right hle hΔ0]
    linarith [hb0, hstep]
  nlinarith [hb1, hsmall, hLt0t']

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}

/-- At most two grid tents are nonzero at a continuum point, and each is `≤ 1`, so the whole
partition of unity is `≤ 2` (a private consequence of the tent construction). -/
private theorem gueTent_sum_le_two (t : ℝ) (hstep : 0 < Grid.step t1 t0 K N)
    (ht1 : t1 N ≤ t) :
    ∑ k ∈ Finset.range (K N + 1), gueTent t1 t0 K N k t ≤ 2 := by
  set Δ := Grid.step t1 t0 K N with hΔdef
  set s := (t - t1 N) / Δ with hsdef
  set k0 : ℕ := ⌊s⌋₊ with hk0def
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hstep.le
  have hzero : ∀ k ∈ Finset.range (K N + 1), k ≠ k0 → k ≠ k0 + 1 →
      gueTent t1 t0 K N k t = 0 := by
    intro k _ hk1 hk2
    unfold gueTent Grid.time
    rw [← hΔdef]
    have hval : t - (t1 N + (k : ℝ) * Δ) = Δ * (s - k) := by rw [hsdef]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos hstep]
    have hkcase : k < k0 ∨ k0 + 1 < k := by omega
    rcases hkcase with hlt | hgt
    · have h1 : (k : ℝ) + 1 ≤ (k0 : ℝ) := by exact_mod_cast hlt
      have h2 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have habsk : |s - (k : ℝ)| = s - (k : ℝ) := abs_of_nonneg (by linarith)
      have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
      rw [mul_div_cancel_left₀ _ hstep.ne']
      exact max_eq_left hgoal
    · have h1 : (k0 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgt
      have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
      have habsk : |s - (k : ℝ)| = (k : ℝ) - s := by
        rw [abs_of_neg (by linarith : s - (k : ℝ) < 0)]; ring
      have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
      rw [mul_div_cancel_left₀ _ hstep.ne']
      exact max_eq_left hgoal
  have hsub : ((Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1))
      ⊆ Finset.range (K N + 1) := Finset.filter_subset _ _
  have heq : ∑ k ∈ Finset.range (K N + 1), gueTent t1 t0 K N k t
      = ∑ k ∈ (Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1),
          gueTent t1 t0 K N k t := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k hk hk'
    simp only [Finset.mem_filter, not_and, not_or] at hk'
    exact hzero k hk (hk' hk).1 (hk' hk).2
  rw [heq]
  have hcard : ((Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card ≤ 2 := by
    calc ((Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card
        ≤ ({k0, k0 + 1} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro k hk
          simp only [Finset.mem_filter] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hk.2
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  calc ∑ k ∈ (Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1), gueTent t1 t0 K N k t
      ≤ ∑ _k ∈ (Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        unfold gueTent
        exact max_le (by norm_num)
          (by linarith [div_nonneg (abs_nonneg (t - Grid.time t1 t0 K N k)) hstep.le])
    _ = ((Finset.range (K N + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 := by exact_mod_cast hcard

/-- `b⁻¹ ≤ 2a⁻¹` from `a ≤ 2b` (elementary real-analysis helper). -/
private theorem inv_le_two_inv_of_le_two_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ 2 * b) :
    b⁻¹ ≤ 2 * a⁻¹ := by
  rw [show (2 : ℝ) * a⁻¹ = 2 / a by ring, inv_eq_one_div, div_le_div_iff₀ hb ha]
  linarith

/-- Monotonicity of `Grid.time` in the grid index, given a nonnegative step. -/
private theorem gueTime_mono (hstep0 : 0 ≤ Grid.step t1 t0 K N) {i j : ℕ} (hij : i ≤ j) :
    Grid.time t1 t0 K N i ≤ Grid.time t1 t0 K N j := by
  unfold Grid.time
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith [hstep0]

/-- `gueKbar` is nondecreasing in the grid index (a running maximum). -/
private theorem gueKbar_mono (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (m : ℕ) {k k' : ℕ}
    (hkk' : k ≤ k') :
    gueKbar d t1 t0 K Kt N m k ≤ gueKbar d t1 t0 K Kt N m k' := by
  unfold gueKbar
  apply ciSup_le
  intro j
  exact le_ciSup_finite
    (fun j' : Fin (k' + 1) => ⨆ x : LoopData (d.L N) m, ‖Kt N (Grid.time t1 t0 K N j') x.idx‖)
    ⟨j, by omega⟩

/-- Every grid time with index `≤ K N` lies in `[t1 N, t0 N]`. -/
private theorem gueTime_mem_Icc (ht10' : t1 N ≤ t0 N) (hKne : K N ≠ 0) {k : ℕ} (hk : k ≤ K N) :
    Grid.time t1 t0 K N k ∈ Set.Icc (t1 N) (t0 N) := by
  have hstep0 : 0 ≤ Grid.step t1 t0 K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  refine ⟨?_, ?_⟩
  · have h0 := gueTime_mono (t1 := t1) (t0 := t0) (K := K) (N := N) hstep0 (Nat.zero_le k)
    rwa [Grid.time_zero] at h0
  · have h1 := gueTime_mono (t1 := t1) (t0 := t0) (K := K) (N := N) hstep0 hk
    rwa [Grid.time_last t1 t0 K N hKne] at h1

/-- There is a grid index `kstar ≤ K N` within one step of any `t ∈ [t1 N, t0 N]`, which
dominates (in index) every grid index whose tent is nonzero at `t`. -/
private theorem gueTime_kstar_near (hstep : 0 < Grid.step t1 t0 K N) (ht10' : t1 N ≤ t0 N)
    (t : ℝ) (htlo : t1 N ≤ t) (hthi : t ≤ t0 N) (hKne : K N ≠ 0) :
    ∃ kstar : ℕ, kstar ≤ K N ∧ |t - Grid.time t1 t0 K N kstar| ≤ Grid.step t1 t0 K N ∧
      ∀ k : ℕ, k ≤ K N → gueTent t1 t0 K N k t > 0 → k ≤ kstar := by
  set Δ := Grid.step t1 t0 K N with hΔdef
  set s := (t - t1 N) / Δ with hsdef
  set k0 : ℕ := ⌊s⌋₊ with hk0def
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hstep.le
  have hKNne0 : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hKne
  have hΔKN : Δ * (K N : ℝ) = t0 N - t1 N := by
    rw [hΔdef]; unfold Grid.step; field_simp
  have hsKN : s ≤ (K N : ℝ) := by
    rw [hsdef, div_le_iff₀ hstep]
    linarith [hΔKN, hthi]
  have hk0KN : k0 ≤ K N := by
    have := Nat.floor_le hs0
    have hle : (k0 : ℝ) ≤ (K N : ℝ) := le_trans this hsKN
    exact_mod_cast hle
  refine ⟨min (k0 + 1) (K N), min_le_right _ _, ?_, ?_⟩
  · by_cases hcase : k0 + 1 ≤ K N
    · rw [min_eq_left hcase]
      have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
      have h1 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have htimeeq : Grid.time t1 t0 K N (k0 + 1) - t = Δ * ((k0 : ℝ) + 1 - s) := by
        unfold Grid.time; rw [← hΔdef, hsdef]; push_cast; field_simp; ring
      have hnn : 0 ≤ (k0 : ℝ) + 1 - s := by linarith
      have hle1 : (k0 : ℝ) + 1 - s ≤ 1 := by linarith
      rw [abs_sub_comm, htimeeq, abs_of_nonneg (by positivity)]
      nlinarith [hstep.le]
    · have hk0eq : k0 = K N := by omega
      rw [min_eq_right (by omega : K N ≤ k0 + 1)]
      have h1 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have h1' : (K N : ℝ) ≤ s := by rw [← hk0eq]; exact h1
      have hseq : s = (K N : ℝ) := le_antisymm hsKN h1'
      have hts : t - t1 N = Δ * (K N : ℝ) := by
        rw [hsdef] at hseq; field_simp at hseq; linarith
      have htimeeq : Grid.time t1 t0 K N (K N) = t1 N + Δ * (K N : ℝ) := by
        unfold Grid.time; rw [← hΔdef]; ring
      rw [htimeeq]
      have hteq : t = t1 N + Δ * (K N : ℝ) := by linarith
      rw [hteq]
      simp [hstep.le]
  · intro k hkKN hkpos
    by_contra hcon
    push_neg at hcon
    have hgt : k0 + 1 < k := by omega
    apply absurd hkpos (not_lt.2 (le_of_eq ?_))
    unfold gueTent Grid.time
    rw [← hΔdef]
    have hval : t - (t1 N + (k : ℝ) * Δ) = Δ * (s - k) := by rw [hsdef]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos hstep]
    have h1 : (k0 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgt
    have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
    have habsk : |s - (k : ℝ)| = (k : ℝ) - s := by
      rw [abs_of_neg (by linarith : s - (k : ℝ) < 0)]; ring
    have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
    rw [mul_div_cancel_left₀ _ hstep.ne']
    exact max_eq_left hgoal

/-- Nonnegativity of the deterministic `K̃` scale (private, used to compare inverses
of the scale at different times). -/
private theorem gue_pow_nonneg (W : ℕ) (e : ℝ) (L : ℕ) (t : ℝ) (ht1 : t < 1) (k : ℕ) :
    (0 : ℝ) ≤ ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ k := by
  have hetaT_nonneg : 0 ≤ etaT e t := by
    unfold etaT
    have h2 : 0 ≤ (mE e).im := by rw [mE_im]; positivity
    nlinarith
  have hellHat_nonneg : 0 ≤ ellHat L (t : ℂ) := by rw [ellHat_ofReal L ht1]; positivity
  have hX_nonneg : 0 ≤ (W : ℝ) * (etaT e t * ellHat L (t : ℂ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hetaT_nonneg hellHat_nonneg)
  exact pow_nonneg (inv_nonneg.2 hX_nonneg) _

/-- A uniform-in-length constant for `norm_Kgen_le_unif`, `1 ≤ n ≤ Nmax` (mirrors
`Loop/KBound.lean`'s `exists_uniform`). -/
private theorem exists_uniform_C_Kgen {κ : ℝ} (hκ : 0 < κ) (Nmax : ℕ) :
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
      calc ‖Kgen L W (mSigma e) t I‖ ≤ C1 * ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ (n - 1) :=
            hb
        _ ≤ (C1 + C2) * ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ (n - 1) := by
            apply mul_le_mul_of_nonneg_right _ (gue_pow_nonneg W e L t ht1' (n - 1))
            linarith
    · obtain rfl : n = M + 1 := by omega
      have hb := h2 e hE'' L hL W t ht0' ht1' I hI hlen
      calc ‖Kgen L W (mSigma e) t I‖
            ≤ C2 * ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ (M + 1 - 1) := hb
        _ ≤ (C1 + C2) * ((W : ℝ) * (etaT e t * ellHat L (t : ℂ)))⁻¹ ^ (M + 1 - 1) := by
            apply mul_le_mul_of_nonneg_right _ (gue_pow_nonneg W e L t ht1' (M + 1 - 1))
            linarith

/-- The per-grid-index bound on `gueKbar` obtained from an `eq736_detDom`-style bound `hbaseN`
at a fixed `N`, using that the bound is monotone increasing in the grid index (factored
out of `gueKproc_unifDetDom` as a separate declaration to keep each elaboration problem small). -/
private theorem gueKbar_le_of_hbase (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N n0 m : ℕ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (lam : ℕ → ℝ → ℝ) (τ' : ℝ)
    (ht10N : t1 N ≤ t0 N) (hKne : K N ≠ 0)
    (hlam_pos : ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < lam N t)
    (hlam_anti : ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t →
      lam N t ≤ lam N u)
    (hbaseN : ∀ p : TimeIcc t1 t0 N × GUEPhase.LoopSet (d.L N) (2 * n0),
      ‖Kt N p.1 p.2.1‖ ≤ (N : ℝ) ^ τ' * (lam N p.1)⁻¹ ^ ((p.2.1).length - 1))
    (hm2 : 2 ≤ m) (hm2n0 : m ≤ 2 * n0) (k : ℕ) (hk : k ≤ K N) :
    gueKbar d t1 t0 K Kt N m k ≤ (N : ℝ) ^ τ' * (lam N (Grid.time t1 t0 K N k))⁻¹ ^ (m - 1) := by
  unfold gueKbar
  apply ciSup_le
  intro j
  apply ciSup_le
  intro x
  have hjk : (j : ℕ) ≤ k := by omega
  have htimej_mem : Grid.time t1 t0 K N j ∈ Set.Icc (t1 N) (t0 N) :=
    gueTime_mem_Icc ht10N hKne (by omega)
  have htimek_mem : Grid.time t1 t0 K N k ∈ Set.Icc (t1 N) (t0 N) :=
    gueTime_mem_Icc ht10N hKne hk
  have hxlen2 : 2 ≤ x.idx.length := by rw [LoopData.idx_length]; omega
  have hxlen2n0 : x.idx.length ≤ 2 * n0 := by rw [LoopData.idx_length]; omega
  have hbound := hbaseN
    ⟨⟨Grid.time t1 t0 K N j, htimej_mem⟩, ⟨x.idx, LoopData.idx_wf x, hxlen2, hxlen2n0⟩⟩
  simp only [LoopData.idx_length] at hbound
  refine hbound.trans ?_
  have hstep0 : 0 ≤ Grid.step t1 t0 K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hle : lam N (Grid.time t1 t0 K N k) ≤ lam N (Grid.time t1 t0 K N j) :=
    hlam_anti _ htimej_mem _ htimek_mem (gueTime_mono hstep0 hjk)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) ^ τ' := by positivity
  have hinvle : (lam N (Grid.time t1 t0 K N j))⁻¹ ^ (m - 1)
      ≤ (lam N (Grid.time t1 t0 K N k))⁻¹ ^ (m - 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 (hlam_pos _ htimej_mem).le)
      (inv_anti₀ (hlam_pos _ htimek_mem) hle) (m - 1)
  exact mul_le_mul_of_nonneg_left hinvle hNnn

/-- `hK` for `gueKproc`: `K̃ ≺ Λ^{m-1}` on the grid, interpolated. -/
theorem gueKproc_unifDetDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
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
        (Set.Icc (t1 N) (t0 N)) t) :
    UnifDetDom (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) =>
        gueKproc d t1 t0 (gueGridK n0) Kt N p.2 p.1)
      (fun N p => (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) := by
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
    obtain ⟨C, hC0, hC⟩ := exists_uniform_C_Kgen hκ (2 * n0)
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
    have hellHatL : ellHat (d.L N) (t1 N : ℂ) = (d.L N : ℝ) := by
      rw [ellHat_ofReal (d.L N) ht1lt1]
      have hLpos : (0 : ℝ) < (d.L N : ℝ) := by exact_mod_cast (by omega : 0 < d.L N)
      have h1mt1pos : 0 < 1 - t1 N := by linarith
      have hsqrt_le : Real.sqrt (1 - t1 N) ≤ 1 / (d.L N : ℝ) := by
        rw [show (1 : ℝ) / (d.L N : ℝ) = Real.sqrt ((1 / (d.L N : ℝ)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
        nlinarith [hellN]
      have hinv_ge : (d.L N : ℝ) ≤ 1 / Real.sqrt (1 - t1 N) := by
        rw [le_div_iff₀ (Real.sqrt_pos.2 h1mt1pos)]
        calc (d.L N : ℝ) * Real.sqrt (1 - t1 N) ≤ (d.L N : ℝ) * (1 / (d.L N : ℝ)) :=
              mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
          _ = 1 := by field_simp
      exact min_eq_right hinv_ge
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
  have hbase := GUEPhase.eq736_detDom d.L d.W Kt (2 * n0) t1 t0 ht10 lam hlam_pos hlam_anti
    hlam_cont (fun N t ht I hWF h2 hlen => hK N t ht I hWF (by omega) (by omega)) hτU h730' h732
  have hstepsmall : ∀ᶠ N : ℕ in atTop, Grid.step t1 t0 (gueGridK n0) N ≤ etaT (E N) (t0 N) := by
    filter_upwards [h730, eventually_ge_atTop 1] with N h730N hN1
    have hetat0nonneg : 0 ≤ etaT (E N) (t0 N) := by
      unfold etaT
      have h2 : 0 ≤ (mE (E N)).im := by rw [mE_im]; positivity
      nlinarith [ht0 N]
    have hK1 : (1 : ℝ) ≤ (gueGridK n0 N : ℝ) := by
      have hge1 : 1 ≤ gueGridK n0 N := Nat.one_le_iff_ne_zero.2 (gueGridK_ne_zero n0 N)
      exact_mod_cast hge1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNpow_le1 : (N : ℝ) ^ (-τU) ≤ 1 := by
      calc (N : ℝ) ^ (-τU) ≤ (N : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
        _ = 1 := Real.rpow_zero _
    unfold Grid.step
    have hK0 : (0 : ℝ) < (gueGridK n0 N : ℝ) := by linarith
    rw [div_le_iff₀ hK0]
    calc t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N) := h730N
      _ ≤ 1 * etaT (E N) (t0 N) := mul_le_mul_of_nonneg_right hNpow_le1 hetat0nonneg
      _ = etaT (E N) (t0 N) := one_mul _
      _ ≤ etaT (E N) (t0 N) * (gueGridK n0 N : ℝ) := by nlinarith [hK1, hetat0nonneg]
  intro τ hτ
  have hE2 : ∀ N, |E N| ≤ 2 := fun N => by have := hE N; have := hκ; linarith
  clear hK hKinit hscale hell h730
  have hτ'0 : 0 < τ / 2 := by positivity
  filter_upwards [hbase (τ / 2) hτ'0, hstepsmall, eventually_le_rpow ((2 : ℝ) ^ (2 * n0 + 1)) hτ'0,
    eventually_ge_atTop 1] with N hbaseN hstepN h2pow hN1
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  simp only [Set.mem_Icc] at hm ht
  show gueKproc d t1 t0 (gueGridK n0) Kt N m t ≤ (N : ℝ) ^ τ * (lam N t)⁻¹ ^ (m - 1)
  have hKne : gueGridK n0 N ≠ 0 := gueGridK_ne_zero n0 N
  have hperk : ∀ k : ℕ, k ≤ gueGridK n0 N →
      gueKbar d t1 t0 (gueGridK n0) Kt N m k ≤
        (N : ℝ) ^ (τ / 2) * (lam N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ (m - 1) :=
    fun k hk => gueKbar_le_of_hbase d t1 t0 (gueGridK n0) N n0 m Kt lam (τ / 2) (ht10 N) hKne
      (hlam_pos N) (hlam_anti N) hbaseN hm.1 hm.2 k hk
  clear hbaseN hbase h732 hstepsmall h730' hetaAnti hlam_cont hlam_anti hτ'0
  by_cases hstep0 : Grid.step t1 t0 (gueGridK n0) N = 0
  · have ht1t0eq : t1 N = t0 N := by
      by_contra hne
      apply hne
      have hKR : (gueGridK n0 N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hKne
      have := hstep0
      unfold Grid.step at this
      field_simp at this
      linarith [this]
    have hteq : t = t1 N := le_antisymm (by rw [ht1t0eq]; exact ht.2) ht.1
    have hgoal_eq : gueKproc d t1 t0 (gueGridK n0) Kt N m t
        = gueKbar d t1 t0 (gueGridK n0) Kt N m 0 := by
      unfold gueKproc gueInterp
      rw [if_pos hstep0]
    rw [hgoal_eq, hteq]
    have h0 := hperk 0 (Nat.zero_le _)
    rw [Grid.time_zero] at h0
    refine h0.trans ?_
    have hnn : (0 : ℝ) ≤ (lam N (t1 N))⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos N (t1 N) ⟨le_refl _, ht10 N⟩).le) _
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)) hnn
  · have hstepPos : 0 < Grid.step t1 t0 (gueGridK n0) N :=
      lt_of_le_of_ne (div_nonneg (by linarith [ht10 N]) (Nat.cast_nonneg _)) (Ne.symm hstep0)
    obtain ⟨kstar, hkstarKN, hknear, hkdom⟩ :=
      gueTime_kstar_near hstepPos (ht10 N) t ht.1 ht.2 hKne
    have htimekstar_mem : Grid.time t1 t0 (gueGridK n0) N kstar ∈ Set.Icc (t1 N) (t0 N) :=
      gueTime_mem_Icc (ht10 N) hKne hkstarKN
    have hlamnear : lam N t ≤ 2 * lam N (Grid.time t1 t0 (gueGridK n0) N kstar) := by
      have hM : (0 : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := Nat.cast_nonneg _
      have him1 : (mE (E N)).im ≤ 1 := by
        have h1 := Complex.abs_im_le_norm (mE (E N))
        rw [norm_mE (hE2 N)] at h1
        exact (abs_le.mp h1).2
      have him0 : 0 ≤ (mE (E N)).im := by rw [mE_im]; positivity
      have hsmall : ((d.L N * d.W N : ℕ) : ℝ) * Grid.step t1 t0 (gueGridK n0) N ≤
          ((d.L N * d.W N : ℕ) : ℝ) * (1 - t0 N) * (mE (E N)).im := by
        have hstepmul := mul_le_mul_of_nonneg_left hstepN hM
        rw [show ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (t0 N)
          = ((d.L N * d.W N : ℕ) : ℝ) * (1 - t0 N) * (mE (E N)).im by unfold etaT; ring] at hstepmul
        exact hstepmul
      have hkey := gueLam_near_le hM him0 him1 htimekstar_mem.2 hknear hsmall
      rw [hlamdef]
      show ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t
          ≤ 2 * (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N kstar))
      unfold etaT
      linarith [hkey, mul_assoc ((d.L N * d.W N : ℕ) : ℝ) (1 - t) (mE (E N)).im,
        mul_assoc ((d.L N * d.W N : ℕ) : ℝ) (1 - Grid.time t1 t0 (gueGridK n0) N kstar)
          (mE (E N)).im]
    have hinvnear : (lam N (Grid.time t1 t0 (gueGridK n0) N kstar))⁻¹ ≤ 2 * (lam N t)⁻¹ :=
      inv_le_two_inv_of_le_two_mul (hlam_pos N t ht) (hlam_pos N _ htimekstar_mem) hlamnear
    have hkstarbound : gueKbar d t1 t0 (gueGridK n0) Kt N m kstar ≤
        (N : ℝ) ^ (τ / 2) * (2 ^ (2 * n0) * (lam N t)⁻¹ ^ (m - 1)) := by
      refine (hperk kstar hkstarKN).trans ?_
      have hNnn2 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by positivity
      apply mul_le_mul_of_nonneg_left _ hNnn2
      have hkstarinv_nn : (0 : ℝ) ≤ (lam N (Grid.time t1 t0 (gueGridK n0) N kstar))⁻¹ :=
        inv_nonneg.2 (hlam_pos N _ htimekstar_mem).le
      have htinv_nn : (0 : ℝ) ≤ (lam N t)⁻¹ ^ (m - 1) :=
        pow_nonneg (inv_nonneg.2 (hlam_pos N t ht).le) _
      calc (lam N (Grid.time t1 t0 (gueGridK n0) N kstar))⁻¹ ^ (m - 1)
          ≤ (2 * (lam N t)⁻¹) ^ (m - 1) :=
            pow_le_pow_left₀ hkstarinv_nn hinvnear (m - 1)
        _ = 2 ^ (m - 1) * (lam N t)⁻¹ ^ (m - 1) := by rw [mul_pow]
        _ ≤ 2 ^ (2 * n0) * (lam N t)⁻¹ ^ (m - 1) := by
            apply mul_le_mul_of_nonneg_right _ htinv_nn
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hgueKproc_le : gueKproc d t1 t0 (gueGridK n0) Kt N m t
        ≤ 2 * gueKbar d t1 t0 (gueGridK n0) Kt N m kstar := by
      unfold gueKproc gueInterp
      rw [if_neg hstep0]
      have hdomle : ∀ k, k ∈ Finset.range (gueGridK n0 N + 1) →
          gueKbar d t1 t0 (gueGridK n0) Kt N m k * gueTent t1 t0 (gueGridK n0) N k t
            ≤ gueKbar d t1 t0 (gueGridK n0) Kt N m kstar * gueTent t1 t0 (gueGridK n0) N k t := by
        intro k hk
        by_cases hpos : 0 < gueTent t1 t0 (gueGridK n0) N k t
        swap
        · have htent0 : gueTent t1 t0 (gueGridK n0) N k t = 0 :=
            le_antisymm (not_lt.1 hpos) (gueTent_nonneg k t)
          rw [htent0, mul_zero, mul_zero]
        · have hkkstar : k ≤ kstar :=
            hkdom k (by simpa using (Finset.mem_range.mp hk : k < gueGridK n0 N + 1)) hpos
          exact mul_le_mul_of_nonneg_right (gueKbar_mono d Kt m hkkstar)
            (gueTent_nonneg k t)
      calc ∑ k ∈ Finset.range (gueGridK n0 N + 1),
            gueKbar d t1 t0 (gueGridK n0) Kt N m k * gueTent t1 t0 (gueGridK n0) N k t
          ≤ ∑ k ∈ Finset.range (gueGridK n0 N + 1),
              gueKbar d t1 t0 (gueGridK n0) Kt N m kstar * gueTent t1 t0 (gueGridK n0) N k t :=
            Finset.sum_le_sum hdomle
        _ = gueKbar d t1 t0 (gueGridK n0) Kt N m kstar *
              ∑ k ∈ Finset.range (gueGridK n0 N + 1), gueTent t1 t0 (gueGridK n0) N k t := by
            rw [Finset.mul_sum]
        _ ≤ gueKbar d t1 t0 (gueGridK n0) Kt N m kstar * 2 := by
            have hkbar_nonneg : (0 : ℝ) ≤ gueKbar d t1 t0 (gueGridK n0) Kt N m kstar := by
              unfold gueKbar
              exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
            apply mul_le_mul_of_nonneg_left (gueTent_sum_le_two t hstepPos ht.1) hkbar_nonneg
        _ = 2 * gueKbar d t1 t0 (gueGridK n0) Kt N m kstar := by ring
    have hcomb : gueKproc d t1 t0 (gueGridK n0) Kt N m t
        ≤ 2 * ((N : ℝ) ^ (τ / 2) * (2 ^ (2 * n0) * (lam N t)⁻¹ ^ (m - 1))) := by
      refine hgueKproc_le.trans ?_
      exact mul_le_mul_of_nonneg_left hkstarbound (by norm_num)
    refine hcomb.trans ?_
    have hfin : 2 * ((N : ℝ) ^ (τ / 2) * (2 ^ (2 * n0) * (lam N t)⁻¹ ^ (m - 1)))
        = (2 ^ (2 * n0 + 1)) * (N : ℝ) ^ (τ / 2) * (lam N t)⁻¹ ^ (m - 1) := by ring
    rw [hfin]
    have hpow2N : (2 : ℝ) ^ (2 * n0 + 1) ≤ (N : ℝ) ^ (τ / 2) := h2pow
    have hNpow_split : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add (by exact_mod_cast hN1 : (0:ℝ) < N)]; ring_nf
    rw [hNpow_split]
    have htinv_nn' : (0 : ℝ) ≤ (lam N t)⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos N t ht).le) _
    apply mul_le_mul_of_nonneg_right _ htinv_nn'
    calc (2 : ℝ) ^ (2 * n0 + 1) * (N : ℝ) ^ (τ / 2)
        ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_right hpow2N (by positivity)
      _ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := rfl

end GueKprocDom

end RBM.Gauss.GUEGrid

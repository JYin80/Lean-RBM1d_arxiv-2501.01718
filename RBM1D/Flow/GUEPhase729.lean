/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseStep
import RBM1D.Flow.GUEPhaseOneLoop
import RBM1D.Flow.GUEPhaseKTilde
import RBM1D.Flow.EnergyUniformReg

/-!
# (7.29) at `t₀` on the GUE-phase grid

For `σ = (+, σ₂)` and every `δ > 0`, eventually
in `N`,
`|E L̃_{t₀,σ,(a,b)} - K̃_{t₀,σ,(a,b)}| ≤ W^δ (N η_{t₀})^{-3}` (paper (7.29), §7.2, at `t = t₀`),
where `L̃` is the GUE-phase grid path `gueH` at its last step under `Pgue d` and `K̃` is the
GUE-phase 2-loop primitive `kTwoGUE`.

## Route

The proof runs entirely on the GUE-phase grid carrier `Pgue d`; the only transfer between
carriers is the one-time law `map_gueH_zero` at step `0`.

* **Duhamel in expectation.**  Integrating the one-step conditional drift of
  `Flow/GUEPhaseStep.lean` (`condExp_loop_drift_gue`) gives
  `E L_{k+1} = E L_k + Δ E[loopDriftGUE_k] + O(Δ^{3/2})`; the martingale part has mean exactly `0`
  (every loop is deterministically bounded by `η^{-n}`).
* **Split of the drift** (`primRhsGUE_sub`, 2-loops only): the linear coupling acts on
  `e_k = E L_k - K̃_{u_k}` (the expectation passes through the deterministic factor `K̃`), the
  quadratic term is bounded by `hP.lk 2` (row Q2), the `E^{(G)}` term by Lemma 5.15 for the
  GUE-phase profile (`Flow/GUEPhaseOneLoop.lean`), `hP.lk 1`, `hP.lk 3` and `K̃₃ ≺ Λ²` from
  `eq736_detDom` (row Q3).
* **Crude Grönwall** (row P) with rate `2 M ρ Λ`, `∫ rate ≤ 2 ρ (t₀ - t₁)/η_{t₀} ≤ 2`.
* **Initial term** (row Q1) from `BoundsN.expect` via `map_gueH_zero`; **discretization** (row
  Q4) from the grid size `gueGridK n0`; **`≺ → W^δ`** (row Q5) from `W ≥ N^{1/2}`.
-/

noncomputable section

open Filter MeasureTheory

namespace RBM.Gauss.GUEGrid

/-! ### Algebra of 2-loops -/

section Algebra

/-- The primitive bilinear form on a 2-loop: only the cut `(k, l) = (1, 2)` contributes. -/
private theorem p729_primBil2 (L W : ℕ) [NeZero L] (K K' : LoopIdx (ZMod L) → ℂ)
    (s1 s2 : Bool) (a1 a2 : ZMod L) :
    GUEPhase.primBilGUE L W K K' ⟨[s1, s2], [a1, a2]⟩ =
      (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        K ⟨[s1, s2], [a, a2]⟩ * GUEPhase.SBgue L a b * K' ⟨[s1, s2], [a1, b]⟩ := by
  unfold GUEPhase.primBilGUE
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (ZMod L))) = {1, 2} := by
    rfl
  have h2 : ∀ k, Finset.Ioc k (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (ZMod L)))
      = Finset.Ioc k 2 := fun k => rfl
  rw [h1]
  simp only [h2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    show Finset.Ioc 1 2 = {2} from rfl, show Finset.Ioc 2 2 = ∅ from rfl, Finset.sum_singleton,
    Finset.sum_empty, add_zero]
  rfl

/-- The `E^{(G)}` term on a 2-loop, written with 1-loops and 3-loops. -/
private theorem p729_eG2 (L W : ℕ) [NeZero L] [NeZero W] (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (s1 s2 : Bool) (a1 a2 : ZMod L) :
    eGtermGUE L W m M z ⟨[s1, s2], [a1, a2]⟩ =
      (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        ((gloop L W M z ⟨[s1], [a]⟩ - m s1) * GUEPhase.SBgue L a b *
            gloop L W M z ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (gloop L W M z ⟨[s2], [a]⟩ - m s2) * GUEPhase.SBgue L a b *
            gloop L W M z ⟨[s1, s2, s2], [a1, b, a2]⟩) := by
  unfold eGtermGUE
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s1, s2], [a1, a2]⟩ : LoopIdx (ZMod L))) = {1, 2} := by
    rfl
  have htr : ∀ (s : Bool) (a : ZMod L), Matrix.trace ((Gsig M z s - m s •
        (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)
      = gloop L W M z ⟨[s], [a]⟩ - m s := by
    intro s a
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      trace_Eblk, smul_eq_mul, mul_one]
    simp [gloop, gloopProd]
  rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [htr]
  rw [← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  rfl

/-- `‖W ∑_{a,b} A_a (1/L) B_b‖ ≤ (L W) α β`. -/
private theorem p729_norm_WsumSB_le (L W : ℕ) [NeZero L] (A B : ZMod L → ℂ) {α β : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ α) (hB : ∀ y, ‖B y‖ ≤ β) :
    ‖(W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L, A a * GUEPhase.SBgue L a b * B b‖
      ≤ ((L * W : ℕ) : ℝ) * α * β := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hα : 0 ≤ α := (norm_nonneg _).trans (hA 0)
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hB 0)
  have hterm : ∀ a b : ZMod L, ‖A a * GUEPhase.SBgue L a b * B b‖ ≤ α * (L : ℝ)⁻¹ * β := by
    intro a b
    rw [norm_mul, norm_mul, GUEPhase.SBgue_apply, norm_inv, Complex.norm_natCast]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hA a) (by positivity)) (hB b) (norm_nonneg _)
      (by positivity)
  calc ‖(W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L, A a * GUEPhase.SBgue L a b * B b‖
      ≤ (W : ℝ) * ∑ a : ZMod L, ∑ b : ZMod L, ‖A a * GUEPhase.SBgue L a b * B b‖ := by
        rw [norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ (W : ℝ) * ∑ _a : ZMod L, ∑ _b : ZMod L, α * (L : ℝ)⁻¹ * β := by
        gcongr with a _ b _
        exact hterm a b
    _ = ((L * W : ℕ) : ℝ) * α * β := by
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        push_cast
        field_simp

private theorem p729_norm_primBil2_le (L W : ℕ) [NeZero L] (K K' : LoopIdx (ZMod L) → ℂ)
    (s1 s2 : Bool) (a1 a2 : ZMod L) {α β : ℝ} (hA : ∀ x, ‖K ⟨[s1, s2], [x, a2]⟩‖ ≤ α)
    (hB : ∀ y, ‖K' ⟨[s1, s2], [a1, y]⟩‖ ≤ β) :
    ‖GUEPhase.primBilGUE L W K K' ⟨[s1, s2], [a1, a2]⟩‖ ≤ ((L * W : ℕ) : ℝ) * α * β := by
  rw [p729_primBil2]
  exact p729_norm_WsumSB_le L W (fun x => K ⟨[s1, s2], [x, a2]⟩)
    (fun y => K' ⟨[s1, s2], [a1, y]⟩) hA hB

/-- `primRhsGUE` of a 1-loop is an empty sum. -/
private theorem p729_primRhs_one (L W : ℕ) [NeZero L] (K : LoopIdx (ZMod L) → ℂ) (s : Bool)
    (a : ZMod L) : GUEPhase.primRhsGUE L W K ⟨[s], [a]⟩ = 0 := by
  unfold GUEPhase.primRhsGUE GUEPhase.primBilGUE
  have h1 : Finset.Icc 1 (LoopIdx.length (⟨[s], [a]⟩ : LoopIdx (ZMod L))) = {1} := rfl
  have h2 : Finset.Ioc 1 (LoopIdx.length (⟨[s], [a]⟩ : LoopIdx (ZMod L))) = ∅ := rfl
  rw [h1, Finset.sum_singleton, h2, Finset.sum_empty, mul_zero]

/-- The `-` 1-loop is the conjugate of the `+` 1-loop (Hermitian `H`). -/
private theorem p729_gloop_one_false {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) (z : ℂ) (a : ZMod L) :
    gloop L W H z ⟨[false], [a]⟩ = (starRingEnd ℂ) (gloop L W H z ⟨[true], [a]⟩) := by
  simp only [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]
  rw [show Gsig H z false = (Gsig H z true).conjTranspose from
    (RBM.Gsig_conjTranspose hH z true).symm]
  change Matrix.trace ((Gsig H z true).conjTranspose * Eblk L W a)
    = star (Matrix.trace (Gsig H z true * Eblk L W a))
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Eblk_conjTranspose,
    Matrix.trace_mul_comm]

end Algebra

/-! ### Bounded measurable functions and expectations on a good event -/

section Measure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bounded and a.e.-strongly measurable. -/
private def p729BM (μ : Measure Ω) (f : Ω → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∃ C, ∀ ω, ‖f ω‖ ≤ C

private theorem p729BM_const (c : ℂ) : p729BM μ (fun _ => c) :=
  ⟨aestronglyMeasurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem p729BM.add {f g : Ω → ℂ} (hf : p729BM μ f) (hg : p729BM μ g) :
    p729BM μ (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.add hgm, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem p729BM.sub {f g : Ω → ℂ} (hf : p729BM μ f) (hg : p729BM μ g) :
    p729BM μ (fun ω => f ω - g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem p729BM.mul {f g : Ω → ℂ} (hf : p729BM μ f) (hg : p729BM μ g) :
    p729BM μ (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hCg ω) (norm_nonneg _) ((norm_nonneg _).trans (hCf ω))

private theorem p729BM.sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℂ}
    (hf : ∀ i ∈ s, p729BM μ (f i)) : p729BM μ (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using p729BM_const (μ := μ) 0
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using h1.add h2

private theorem p729BM.integrable [IsFiniteMeasure μ] {f : Ω → ℂ} (hf : p729BM μ f) :
    Integrable f μ := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact Integrable.of_bound hfm C (Eventually.of_forall hC)

/-- **Expectation on a good event**: `‖E f‖ ≤ g + C p` if `‖f‖ ≤ g` off `B`, `‖f‖ ≤ C`
everywhere, and `μ B ≤ p`. -/
private theorem p729_norm_integral_le [IsProbabilityMeasure μ] {f : Ω → ℂ} (hf : Integrable f μ)
    {B : Set Ω} {g C p : ℝ} (hg : 0 ≤ g) (hC : 0 ≤ C) (hp : μ B ≤ ENNReal.ofReal p)
    (hp0 : 0 ≤ p) (hgood : ∀ ω ∉ B, ‖f ω‖ ≤ g) (hall : ∀ ω, ‖f ω‖ ≤ C) :
    ‖∫ ω, f ω ∂μ‖ ≤ g + C * p := by
  set T := toMeasurable μ B with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable μ B
  have hpt : ∀ ω, ‖f ω‖ ≤ g + T.indicator (fun _ => C) ω := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω]; linarith [hall ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact hgood ω fun h => hω (subset_toMeasurable μ B h)
  have hint : Integrable (fun ω => g + T.indicator (fun _ => C) ω) μ :=
    (integrable_const g).add ((integrable_const C).indicator hTm)
  have hμT : μ.real T ≤ p := by
    rw [Measure.real, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hp0 hp
  calc ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (g + T.indicator (fun _ => C) ω) ∂μ := integral_mono hf.norm hint hpt
    _ = g + μ.real T * C := by
        rw [integral_add (integrable_const g) ((integrable_const C).indicator hTm),
          integral_const, integral_indicator_const C hTm]
        simp
    _ ≤ g + C * p := by nlinarith

/-- `‖∫ W ∑_{a,b} f_{ab}‖ ≤ W ∑_{a,b} ‖∫ f_{ab}‖`. -/
private theorem p729_norm_integral_Wsum_le {ι : Type*} [Fintype ι] (W : ℕ) (f : ι → ι → Ω → ℂ)
    (hf : ∀ a b, Integrable (f a b) μ) :
    ‖∫ ω, (W : ℂ) * ∑ a, ∑ b, f a b ω ∂μ‖ ≤ (W : ℝ) * ∑ a, ∑ b, ‖∫ ω, f a b ω ∂μ‖ := by
  rw [integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hf a b]
  simp_rw [integral_finsetSum _ fun b _ => hf _ b]
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  exact Finset.sum_le_sum fun a _ => norm_sum_le _ _

end Measure

/-! ### The GUE-phase grid at a fixed size parameter -/

section GridFacts

open scoped Matrix.Norms.L2Operator

variable (d : Dims)

/-- The loop `L_{u_k}` of the GUE-phase grid path at grid step `k`. -/
private def p729F (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (N k : ℕ) (ω : Grid.Ωg d)
    (I : LoopIdx (ZMod (d.L N))) : ℂ :=
  gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) I

variable {d}

private theorem p729_step_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (ht10 : t1 N ≤ t0 N) :
    0 ≤ Grid.step t1 t0 K N :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

private theorem p729_time_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    Grid.time t1 t0 K N (k + 1) = Grid.time t1 t0 K N k + Grid.step t1 t0 K N := by
  unfold Grid.time; push_cast; ring

private theorem p729_KΔ {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hK : K N ≠ 0) :
    (K N : ℝ) * Grid.step t1 t0 K N = t0 N - t1 N := by
  unfold Grid.step
  have : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  field_simp

private theorem p729_time_mem {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} (ht10 : t1 N ≤ t0 N)
    (hK : K N ≠ 0) (hk : k ≤ K N) :
    Grid.time t1 t0 K N k ∈ Set.Icc (t1 N) (t0 N) := by
  have hΔ := p729_step_nonneg (K := K) ht10
  have hkK : (k : ℝ) ≤ K N := by exact_mod_cast hk
  have h1 : (k : ℝ) * Grid.step t1 t0 K N ≤ K N * Grid.step t1 t0 K N :=
    mul_le_mul_of_nonneg_right hkK hΔ
  rw [p729_KΔ hK] at h1
  constructor
  · unfold Grid.time; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · unfold Grid.time; linarith

private theorem p729_eta_pos {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) : 0 < etaT E u := by
  unfold etaT; exact mul_pos (by linarith) (mE_im_pos hE)

private theorem p729_eta_le {E : ℝ} (hE : |E| < 2) {u t : ℝ} (hut : u ≤ t) :
    etaT E t ≤ etaT E u := by
  unfold etaT; exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hE).le

private theorem p729_zt_im (E u : ℝ) : (zt E u).im = etaT E u := (etaT_eq_zt_im E u).symm

private theorem p729_loop_aesm {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    AEStronglyMeasurable (fun ω => gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) z I) (Pgue d) := by
  have hTF := testFun_loopObs_of_im_le (d := d) (N := N) hz (abs_pos.2 hz) le_rfl hwf hn
  have he : (fun ω => gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) z I)
      = fun ω => loopObs d N z I (gueH d t1 t0 K N k ω) := by
    funext ω; rw [loopObs_of_isHermitian (gueH_isHermitian d t1 t0 K N k ω)]
  rw [he]
  exact (hTF.contDiff.continuous.measurable.comp
    (gueH_measurable d t1 t0 K N k)).aestronglyMeasurable

private theorem p729_loop_bound {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) (ω : Grid.Ωg d) :
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) z I‖ ≤ (|z.im|)⁻¹ ^ I.a.length := by
  have h := norm_gloop_le_of_le_abs_im (L := d.L N) (W := d.W N)
    (gueH_isHermitian d t1 t0 K N k ω) (abs_pos.2 hz) le_rfl I hwf hn
  refine h.trans ?_
  have hW : ((d.W N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast d.W_pos N)
  have hW0 : 0 ≤ ((d.W N : ℝ))⁻¹ := by positivity
  calc |z.im|⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1)
      ≤ |z.im|⁻¹ ^ I.a.length * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hW0 hW) (by positivity)
    _ = _ := mul_one _

private theorem p729_loop_BM {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    p729BM (Pgue d) (fun ω => gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) z I) :=
  ⟨p729_loop_aesm hz hwf hn, _, p729_loop_bound hz hwf hn⟩

end GridFacts

/-! ### One step of the Duhamel formula in expectation -/

section Duhamel

variable (d : Dims)

/-- **Duhamel in expectation** (the one-step drift, integrated): the martingale part has mean `0`.
-/
private theorem p729_duhamel {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {N : ℕ} (hE : |E N| < 2)
    (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1) {k : ℕ} (hk : k < K N)
    {J : LoopIdx (ZMod (d.L N))} (hwf : J.WF) (hn : 1 ≤ J.a.length)
    (hdrift : Integrable (fun ω => loopDriftGUE d (E N) (Grid.time t1 t0 K N k) N J
      (gueH d t1 t0 K N k ω)) (Pgue d)) :
    ‖(∫ ω, p729F d t1 t0 K E N (k + 1) ω J ∂(Pgue d)) - (∫ ω, p729F d t1 t0 K E N k ω J ∂(Pgue d))
        - (Grid.step t1 t0 K N : ℂ) * ∫ ω, loopDriftGUE d (E N) (Grid.time t1 t0 K N k) N J
            (gueH d t1 t0 K N k ω) ∂(Pgue d)‖
      ≤ (2 : ℝ) ^ (4 * J.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (J.length + 4) *
          (1 + ((zt (E N) (Grid.time t1 t0 K N (k + 1))).im)⁻¹) ^ (J.length + 4) *
          Grid.step t1 t0 K N ^ ((3 : ℝ) / 2) := by
  have h := condExp_loop_drift_gue d t1 t0 K N k (E N) hE hwf hn ht1 ht10 ht0 hk
  have hu : ∀ j, j ≤ K N → Grid.time t1 t0 K N j < 1 := fun j hj =>
    lt_of_le_of_lt (p729_time_mem ht10 (by omega) hj).2 ht0
  have hz : ∀ j, j ≤ K N → (zt (E N) (Grid.time t1 t0 K N j)).im ≠ 0 := fun j hj => by
    rw [p729_zt_im]; exact (p729_eta_pos hE (hu j hj)).ne'
  set f' : Grid.Ωg d → ℂ := fun ω' => loopObs d N (zt (E N) (Grid.time t1 t0 K N (k + 1))) J
    (gueH d t1 t0 K N (k + 1) ω') with hf'
  set f : Grid.Ωg d → ℂ := fun ω' => loopObs d N (zt (E N) (Grid.time t1 t0 K N k)) J
    (gueH d t1 t0 K N k ω') with hf
  have hf'eq : f' = fun ω => p729F d t1 t0 K E N (k + 1) ω J := by
    funext ω; change loopObs d N _ J _ = _
    rw [loopObs_of_isHermitian (gueH_isHermitian d t1 t0 K N (k + 1) ω)]; rfl
  have hfeq : f = fun ω => p729F d t1 t0 K E N k ω J := by
    funext ω; change loopObs d N _ J _ = _
    rw [loopObs_of_isHermitian (gueH_isHermitian d t1 t0 K N k ω)]; rfl
  have hf'i : Integrable f' (Pgue d) := by
    rw [hf'eq]; exact (p729_loop_BM (hz (k + 1) hk) hwf hn).integrable
  have hfi : Integrable f (Pgue d) := by
    rw [hfeq]; exact (p729_loop_BM (hz k hk.le) hwf hn).integrable
  have hbound := norm_integral_le_of_norm_le_const h
  rw [probReal_univ, mul_one] at hbound
  set ce : Grid.Ωg d → ℂ := (Pgue d)[f' | Grid.filt d k] with hce_def
  have hce : Integrable ce (Pgue d) := integrable_condExp
  have hid : (∫ x, (ce x - f x - (Grid.step t1 t0 K N : ℂ) •
        loopDriftGUE d (E N) (Grid.time t1 t0 K N k) N J (gueH d t1 t0 K N k x)) ∂(Pgue d))
      = (∫ x, f' x ∂(Pgue d)) - (∫ x, f x ∂(Pgue d)) - (Grid.step t1 t0 K N : ℂ) *
        ∫ ω, loopDriftGUE d (E N) (Grid.time t1 t0 K N k) N J (gueH d t1 t0 K N k ω) ∂(Pgue d) := by
    rw [integral_sub, integral_sub, integral_smul, hce_def, integral_condExp ((Grid.filt d).le k),
      smul_eq_mul]
    · exact hce
    · exact hfi
    · exact hce.sub hfi
    · exact hdrift.smul (Grid.step t1 t0 K N : ℂ)
  rw [hid, hf'eq, hfeq] at hbound
  exact hbound

end Duhamel

/-! ### Abstract expectation bounds for the drift terms on 2-loops -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {L : ℕ} [NeZero L] (W : ℕ)

private theorem p729_sum_const (γ : ℝ) :
    (W : ℝ) * ∑ _a : ZMod L, ∑ _b : ZMod L, γ * (L : ℝ)⁻¹ = ((L * W : ℕ) : ℝ) * γ := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  push_cast
  field_simp

omit [IsProbabilityMeasure μ] in
/-- `‖∫ W ∑_{a,b} f_{ab}‖ ≤ (L W) γ` if every `‖∫ f_{ab}‖ ≤ γ/L`. -/
private theorem p729_norm_integral_Wsum_le' (f : ZMod L → ZMod L → Ω → ℂ)
    (hf : ∀ a b, Integrable (f a b) μ) {γ : ℝ} (hγ : ∀ a b, ‖∫ ω, f a b ω ∂μ‖ ≤ γ * (L : ℝ)⁻¹) :
    ‖∫ ω, (W : ℂ) * ∑ a, ∑ b, f a b ω ∂μ‖ ≤ ((L * W : ℕ) : ℝ) * γ := by
  refine (p729_norm_integral_Wsum_le W f hf).trans ?_
  rw [← p729_sum_const W γ]
  gcongr with a _ b _
  exact hγ a b

omit [IsProbabilityMeasure μ] in
/-- The expectation passes through the deterministic left factor. -/
private theorem p729_integral_primBil_left (K : LoopIdx (ZMod L) → ℂ)
    (G : Ω → LoopIdx (ZMod L) → ℂ) (e : LoopIdx (ZMod L) → ℂ) (s1 s2 : Bool) (a1 a2 : ZMod L)
    (hG : ∀ y, Integrable (fun ω => G ω ⟨[s1, s2], [a1, y]⟩) μ)
    (he : ∀ y, ∫ ω, G ω ⟨[s1, s2], [a1, y]⟩ ∂μ = e ⟨[s1, s2], [a1, y]⟩) :
    ∫ ω, GUEPhase.primBilGUE L W K (G ω) ⟨[s1, s2], [a1, a2]⟩ ∂μ
      = GUEPhase.primBilGUE L W K e ⟨[s1, s2], [a1, a2]⟩ := by
  simp_rw [p729_primBil2]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hG b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hG b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, he]

omit [IsProbabilityMeasure μ] in
/-- The expectation passes through the deterministic right factor. -/
private theorem p729_integral_primBil_right (K : LoopIdx (ZMod L) → ℂ)
    (G : Ω → LoopIdx (ZMod L) → ℂ) (e : LoopIdx (ZMod L) → ℂ) (s1 s2 : Bool) (a1 a2 : ZMod L)
    (hG : ∀ x, Integrable (fun ω => G ω ⟨[s1, s2], [x, a2]⟩) μ)
    (he : ∀ x, ∫ ω, G ω ⟨[s1, s2], [x, a2]⟩ ∂μ = e ⟨[s1, s2], [x, a2]⟩) :
    ∫ ω, GUEPhase.primBilGUE L W (G ω) K ⟨[s1, s2], [a1, a2]⟩ ∂μ
      = GUEPhase.primBilGUE L W e K ⟨[s1, s2], [a1, a2]⟩ := by
  simp_rw [p729_primBil2]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((hG a).mul_const (GUEPhase.SBgue L a b)).mul_const (K ⟨[s1, s2], [a1, b]⟩)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ =>
    ((hG a).mul_const (GUEPhase.SBgue L a b)).mul_const (K ⟨[s1, s2], [a1, b]⟩)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_mul_const, he]

/-- **Row Q2**: the quadratic term `E[(L-K) ∼ (L-K)]` on a 2-loop. -/
private theorem p729_quad (D : Ω → LoopIdx (ZMod L) → ℂ) (s1 s2 : Bool) (a1 a2 : ZMod L)
    (hD : ∀ x y, p729BM μ (fun ω => D ω ⟨[s1, s2], [x, y]⟩)) {B : Set Ω} {g C p : ℝ}
    (hg : 0 ≤ g) (hC : 0 ≤ C) (hp : μ B ≤ ENNReal.ofReal p) (hp0 : 0 ≤ p)
    (hgood : ∀ ω ∉ B, ∀ x y, ‖D ω ⟨[s1, s2], [x, y]⟩‖ ≤ g)
    (hall : ∀ ω x y, ‖D ω ⟨[s1, s2], [x, y]⟩‖ ≤ C) :
    ‖∫ ω, GUEPhase.primBilGUE L W (D ω) (D ω) ⟨[s1, s2], [a1, a2]⟩ ∂μ‖
      ≤ ((L * W : ℕ) : ℝ) * (g * g + C * C * p) := by
  simp_rw [p729_primBil2]
  refine p729_norm_integral_Wsum_le' W _ (fun a b =>
    (((hD a a2).mul (p729BM_const _)).mul (hD a1 b)).integrable) fun a b => ?_
  have hL : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
  have hSB : ‖GUEPhase.SBgue L a b‖ = (L : ℝ)⁻¹ := by
    rw [GUEPhase.SBgue_apply, norm_inv, Complex.norm_natCast]
  have key := p729_norm_integral_le (μ := μ)
    ((((hD a a2).mul (p729BM_const (GUEPhase.SBgue L a b))).mul (hD a1 b)).integrable)
    (g := g * g * (L : ℝ)⁻¹) (C := C * C * (L : ℝ)⁻¹) (by positivity) (by positivity) hp hp0
    (fun ω hω => by
      rw [norm_mul, norm_mul, hSB]
      have h1 := hgood ω hω a a2
      have h2 := hgood ω hω a1 b
      calc ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * (L : ℝ)⁻¹ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖
          = ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖ * (L : ℝ)⁻¹ := by ring
        _ ≤ g * g * (L : ℝ)⁻¹ := by gcongr)
    (fun ω => by
      rw [norm_mul, norm_mul, hSB]
      have h1 := hall ω a a2
      have h2 := hall ω a1 b
      calc ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * (L : ℝ)⁻¹ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖
          = ‖D ω ⟨[s1, s2], [a, a2]⟩‖ * ‖D ω ⟨[s1, s2], [a1, b]⟩‖ * (L : ℝ)⁻¹ := by ring
        _ ≤ C * C * (L : ℝ)⁻¹ := by gcongr)
  refine key.trans (le_of_eq ?_)
  ring

/-- One `E^{(G)}` pair: `‖E[X (1/L) T]‖ ≤ (αβ + g₁g₃ + C₁C₃ p)/L`, from `E T = κ + E(T - κ)`. -/
private theorem p729_pair (X T : Ω → ℂ) (κ c : ℂ) (hX : p729BM μ X) (hT : p729BM μ T)
    {B : Set Ω} {α β g1 g3 C1 C3 p : ℝ} (hα : ‖∫ ω, X ω ∂μ‖ ≤ α) (hκ : ‖κ‖ ≤ β)
    (hg1 : 0 ≤ g1) (hg3 : 0 ≤ g3) (hC1 : 0 ≤ C1) (hC3 : 0 ≤ C3) (hc : 0 ≤ ‖c‖)
    (hp : μ B ≤ ENNReal.ofReal p) (hp0 : 0 ≤ p)
    (hgood : ∀ ω ∉ B, ‖X ω‖ ≤ g1 ∧ ‖T ω - κ‖ ≤ g3)
    (hall : ∀ ω, ‖X ω‖ ≤ C1 ∧ ‖T ω - κ‖ ≤ C3) :
    ‖∫ ω, X ω * c * T ω ∂μ‖ ≤ (α * β + (g1 * g3 + C1 * C3 * p)) * ‖c‖ := by
  have hα0 : 0 ≤ α := (norm_nonneg _).trans hα
  have hXi := hX.integrable
  have hTκ : p729BM μ (fun ω => T ω - κ) := hT.sub (p729BM_const κ)
  have hsplit : (fun ω => X ω * c * T ω) = fun ω => c * (X ω * κ + X ω * (T ω - κ)) := by
    funext ω; ring
  have hint2 : Integrable (fun ω => X ω * (T ω - κ)) μ := (hX.mul hTκ).integrable
  rw [hsplit, integral_const_mul, integral_add (hXi.mul_const κ) hint2, integral_mul_const,
    norm_mul]
  have h2 := p729_norm_integral_le (μ := μ) hint2 (g := g1 * g3) (C := C1 * C3)
    (by positivity) (by positivity) hp hp0
    (fun ω hω => by
      rw [norm_mul]; exact mul_le_mul (hgood ω hω).1 (hgood ω hω).2 (norm_nonneg _) hg1)
    (fun ω => by rw [norm_mul]; exact mul_le_mul (hall ω).1 (hall ω).2 (norm_nonneg _) hC1)
  have h1 : ‖(∫ ω, X ω ∂μ) * κ‖ ≤ α * β := by
    rw [norm_mul]; exact mul_le_mul hα hκ (norm_nonneg _) hα0
  calc ‖c‖ * ‖(∫ ω, X ω ∂μ) * κ + ∫ ω, X ω * (T ω - κ) ∂μ‖
      ≤ ‖c‖ * (α * β + (g1 * g3 + C1 * C3 * p)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) hc
    _ = _ := by ring

end Abstract

/-! ### Row Q4, primitive side: one grid step of `K̃` on 2-loops -/

section KDisc

variable {L W : ℕ} [NeZero L]

/-- `primRhsGUE` on a 2-loop is bounded by `(L W) b²`. -/
private theorem p729_norm_primRhs2_le (K : LoopIdx (ZMod L) → ℂ) {b : ℝ}
    (hb : ∀ s1 s2 x y, ‖K ⟨[s1, s2], [x, y]⟩‖ ≤ b) (s1 s2 : Bool) (a1 a2 : ZMod L) :
    ‖GUEPhase.primRhsGUE L W K ⟨[s1, s2], [a1, a2]⟩‖ ≤ ((L * W : ℕ) : ℝ) * b * b :=
  p729_norm_primBil2_le L W K K s1 s2 a1 a2 (fun x => hb s1 s2 x a2) (fun y => hb s1 s2 a1 y)

/-- **One grid step of the primitive 2-loop**: `‖K̃_u + Δ·(d/dt K̃)_u - K̃_{u+Δ}‖ ≤ 3 M² Δ²`. -/
private theorem p729_Kdisc (Kf : ℝ → LoopIdx (ZMod L) → ℂ) {t1 t0 u Δ b2 : ℝ}
    (hu : u ∈ Set.Icc t1 t0) (hu' : u + Δ ∈ Set.Icc t1 t0) (hΔ : 0 ≤ Δ) (hb2 : b2 ≤ 1)
    (hMΔ : ((L * W : ℕ) : ℝ) * Δ ≤ 1)
    (hKb : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, ‖Kf s ⟨[s1, s2], [x, y]⟩‖ ≤ b2)
    (hKd : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kf s ⟨[s1, s2], [x, y]⟩)
      (GUEPhase.primRhsGUE L W (Kf s) ⟨[s1, s2], [x, y]⟩) (Set.Icc t1 t0) s)
    (s1 s2 : Bool) (a1 a2 : ZMod L) :
    ‖Kf u ⟨[s1, s2], [a1, a2]⟩ + (Δ : ℂ) * GUEPhase.primRhsGUE L W (Kf u) ⟨[s1, s2], [a1, a2]⟩
        - Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩‖ ≤ 3 * ((L * W : ℕ) : ℝ) ^ 2 * Δ ^ 2 := by
  set M : ℝ := ((L * W : ℕ) : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hb20 : 0 ≤ b2 := (norm_nonneg _).trans (hKb u hu true true 0 0)
  set S : Set ℝ := Set.Icc u (u + Δ) with hS
  have hSsub : S ⊆ Set.Icc t1 t0 := fun s hs => ⟨hu.1.trans hs.1, hs.2.trans hu'.2⟩
  have hSconv : Convex ℝ S := convex_Icc _ _
  have huS : u ∈ S := ⟨le_rfl, by linarith⟩
  have hu'S : u + Δ ∈ S := ⟨by linarith, le_rfl⟩
  -- (a) the derivative is bounded by `M`
  have hder : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y,
      ‖GUEPhase.primRhsGUE L W (Kf s) ⟨[s1, s2], [x, y]⟩‖ ≤ M := by
    intro s hs s1 s2 x y
    refine (p729_norm_primRhs2_le (Kf s) (hKb s hs) s1 s2 x y).trans ?_
    calc M * b2 * b2 ≤ M * 1 * 1 := by gcongr
      _ = M := by ring
  -- (b) `‖K̃_s - K̃_u‖ ≤ M Δ` on `[u, u + Δ]`
  have hmove : ∀ s ∈ S, ∀ s1 s2 x y,
      ‖Kf s ⟨[s1, s2], [x, y]⟩ - Kf u ⟨[s1, s2], [x, y]⟩‖ ≤ M * Δ := by
    intro s hs s1 s2 x y
    have h := hSconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => Kf s ⟨[s1, s2], [x, y]⟩)
      (f' := fun s => GUEPhase.primRhsGUE L W (Kf s) ⟨[s1, s2], [x, y]⟩)
      (fun r hr => (hKd r (hSsub hr) s1 s2 x y).mono hSsub)
      (fun r hr => hder r (hSsub hr) s1 s2 x y) huS hs
    refine h.trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
    exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM0
  have hδ1 : M * Δ ≤ 1 := hMΔ
  have hδ0 : 0 ≤ M * Δ := mul_nonneg hM0 hΔ
  -- (c) the derivative moves by at most `3 M² Δ`
  have hgmove : ∀ s ∈ S, ‖GUEPhase.primRhsGUE L W (Kf s) ⟨[s1, s2], [a1, a2]⟩
      - GUEPhase.primRhsGUE L W (Kf u) ⟨[s1, s2], [a1, a2]⟩‖ ≤ 3 * M ^ 2 * Δ := by
    intro s hs
    rw [GUEPhase.primRhsGUE_sub]
    have hdiff : ∀ s1 s2 x y, ‖(Kf s - Kf u) ⟨[s1, s2], [x, y]⟩‖ ≤ M * Δ := fun s1 s2 x y => by
      rw [Pi.sub_apply]; exact hmove s hs s1 s2 x y
    have e1 := p729_norm_primBil2_le L W (Kf u) (Kf s - Kf u) s1 s2 a1 a2
      (fun x => hKb u hu s1 s2 x a2) (fun y => hdiff s1 s2 a1 y)
    have e2 := p729_norm_primBil2_le L W (Kf s - Kf u) (Kf u) s1 s2 a1 a2
      (fun x => hdiff s1 s2 x a2) (fun y => hKb u hu s1 s2 a1 y)
    have e3 := p729_norm_primBil2_le L W (Kf s - Kf u) (Kf s - Kf u) s1 s2 a1 a2
      (fun x => hdiff s1 s2 x a2) (fun y => hdiff s1 s2 a1 y)
    have h1 : M * b2 * (M * Δ) ≤ M * (M * Δ) := by
      have := mul_le_mul_of_nonneg_right hb2 hδ0; nlinarith
    have h2 : M * (M * Δ) * b2 ≤ M * (M * Δ) := by
      have := mul_le_mul_of_nonneg_right hb2 hδ0; nlinarith
    have h3 : M * (M * Δ) * (M * Δ) ≤ M * (M * Δ) := by
      have := mul_le_mul_of_nonneg_left hδ1 hδ0; nlinarith
    calc _ ≤ ‖GUEPhase.primBilGUE L W (Kf u) (Kf s - Kf u) ⟨[s1, s2], [a1, a2]⟩‖
          + ‖GUEPhase.primBilGUE L W (Kf s - Kf u) (Kf u) ⟨[s1, s2], [a1, a2]⟩‖
          + ‖GUEPhase.primBilGUE L W (Kf s - Kf u) (Kf s - Kf u) ⟨[s1, s2], [a1, a2]⟩‖ :=
          norm_add₃_le
      _ ≤ M * (M * Δ) + M * (M * Δ) + M * (M * Δ) := by linarith
      _ = 3 * M ^ 2 * Δ := by ring
  -- (d) the mean value inequality for `φ(s) = K̃_s - (s - u) (d/dt K̃)_u`
  set c : ℂ := GUEPhase.primRhsGUE L W (Kf u) ⟨[s1, s2], [a1, a2]⟩ with hc
  have hφ : ∀ r ∈ S, HasDerivWithinAt
      (fun s => Kf s ⟨[s1, s2], [a1, a2]⟩ - ((s - u : ℝ) : ℂ) * c)
      (GUEPhase.primRhsGUE L W (Kf r) ⟨[s1, s2], [a1, a2]⟩ - ((1 : ℝ) : ℂ) * c) S r := by
    intro r hr
    have h1 := (hKd r (hSsub hr) s1 s2 a1 a2).mono hSsub
    have h2 : HasDerivAt (fun s : ℝ => ((s - u : ℝ) : ℂ) * c) (((1 : ℝ) : ℂ) * c) r :=
      (((hasDerivAt_id r).sub_const u).ofReal_comp).mul_const c
    exact h1.sub h2.hasDerivWithinAt
  have hmvt := hSconv.norm_image_sub_le_of_norm_hasDerivWithin_le hφ
    (fun r hr => by
      rw [Complex.ofReal_one, one_mul]; exact hgmove r hr) huS hu'S
  have heq : Kf u ⟨[s1, s2], [a1, a2]⟩ + (Δ : ℂ) * c - Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩
      = -((Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩ - ((u + Δ - u : ℝ) : ℂ) * c)
          - (Kf u ⟨[s1, s2], [a1, a2]⟩ - ((u - u : ℝ) : ℂ) * c)) := by
    push_cast; ring
  rw [heq, norm_neg]
  refine hmvt.trans (le_of_eq ?_)
  rw [show u + Δ - u = Δ by ring, Real.norm_eq_abs, abs_of_nonneg hΔ]
  ring

end KDisc

/-! ### One step of the recursion for `e_k = E L_{u_k} - K̃_{u_k}` on 2-loops -/

section OneStep

open scoped Matrix.Norms.L2Operator

/-- `e_k(I) = E L_{u_k}(I) - K̃_{u_k}(I)`. -/
private def p729e (d : Dims) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N k : ℕ) (I : LoopIdx (ZMod (d.L N))) : ℂ :=
  (∫ ω, p729F d t1 t0 K E N k ω I ∂(Pgue d)) - Kt N (Grid.time t1 t0 K N k) I

/-- The additive error of one step (rows Q2, Q3, Q4). -/
private def p729c (M ρ Λ p Δ : ℝ) : ℝ :=
  Δ * (M * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * M ^ 2) * (2 * M ^ 2) * p)
      + M * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * M) * (2 * M ^ 3) * p))))
    + (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * M ^ 2 * Δ ^ 2

set_option maxHeartbeats 1000000 in
-- a long but linear assembly of the per-step identity and its bounds
/-- **One step** of the recursion (rows P, Q2, Q3, Q4 at a single grid step). -/
private theorem p729_one_step (d : Dims) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {N : ℕ}
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hE : |E N| < 2) (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1)
    {Λ ρ p Bk : ℝ}
    (hΛ : Λ = (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (t0 N))⁻¹) (hΛ1 : Λ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p)
    (hMΔ : ((d.L N * d.W N : ℕ) : ℝ) * Grid.step t1 t0 K N ≤ 1)
    (hK2b : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 x y,
      ‖Kt N s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ)
    (hK3b : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 s3 x y w,
      ‖Kt N s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2)
    (hKd : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt N s ⟨[s1, s2], [x, y]⟩)
        (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 N) (t0 N)) s)
    {k : ℕ} (hk : k < K N)
    (hX : ∀ a, ‖(∫ ω, p729F d t1 t0 K E N k ω ⟨[true], [a]⟩ ∂(Pgue d)) - mE (E N)‖ ≤ ρ * Λ ^ 2)
    {B : Set (Grid.Ωg d)} (hB : Pgue d B ≤ ENNReal.ofReal p)
    (hg1 : ∀ ω ∉ B, ∀ σ a, ‖p729F d t1 t0 K E N k ω ⟨[σ], [a]⟩ - mSigma (E N) σ‖ ≤ ρ * Λ)
    (hg2 : ∀ ω ∉ B, ∀ s1 s2 x y, ‖p729F d t1 t0 K E N k ω ⟨[s1, s2], [x, y]⟩
      - Kt N (Grid.time t1 t0 K N k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2)
    (hg3 : ∀ ω ∉ B, ∀ s1 s2 s3 x y w, ‖p729F d t1 t0 K E N k ω ⟨[s1, s2, s3], [x, y, w]⟩
      - Kt N (Grid.time t1 t0 K N k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3)
    (hBk : ∀ s1 s2 x y, ‖p729e d t1 t0 K E Kt N k ⟨[s1, s2], [x, y]⟩‖ ≤ Bk)
    (s1 s2 : Bool) (a1 a2 : ZMod (d.L N)) :
    ‖p729e d t1 t0 K E Kt N (k + 1) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      (1 + Grid.step t1 t0 K N * (2 * ((d.L N * d.W N : ℕ) : ℝ) * (ρ * Λ))) * Bk
        + p729c ((d.L N * d.W N : ℕ) : ℝ) ρ Λ p (Grid.step t1 t0 K N) := by
  classical
  set M : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hM
  set Δ : ℝ := Grid.step t1 t0 K N with hΔ
  set u : ℝ := Grid.time t1 t0 K N k with hu_def
  set z : ℂ := zt (E N) u with hz_def
  set J : LoopIdx (ZMod (d.L N)) := ⟨[s1, s2], [a1, a2]⟩ with hJ
  have hKN : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := p729_step_nonneg ht10
  have hu : u ∈ Set.Icc (t1 N) (t0 N) := p729_time_mem ht10 hKN hk.le
  have hu' : u + Δ ∈ Set.Icc (t1 N) (t0 N) := by
    rw [hu_def, hΔ, ← p729_time_succ]; exact p729_time_mem ht10 hKN hk
  have hM1 : 1 ≤ M := by
    rw [hM]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (ouMatrixSize_pos d N).ne'
  have hM0 : 0 ≤ M := by linarith
  -- the scale: `η_u⁻¹ ≤ M` on `[t₁, t₀]`
  have hη0 : 0 < etaT (E N) (t0 N) := p729_eta_pos hE ht0
  have hΛpos : 0 < Λ := by rw [hΛ]; positivity
  have hΛ0 : 0 ≤ Λ := hΛpos.le
  have hηM : ∀ r ∈ Set.Icc (t1 N) (t0 N), |(zt (E N) r).im|⁻¹ ≤ M := by
    intro r hr
    rw [p729_zt_im]
    have hr1 : etaT (E N) (t0 N) ≤ etaT (E N) r := p729_eta_le hE hr.2
    rw [abs_of_pos (hη0.trans_le hr1)]
    have hMη : 1 ≤ M * etaT (E N) (t0 N) := by
      have : (M * etaT (E N) (t0 N))⁻¹ ≤ 1 := by rw [← hΛ]; exact hΛ1
      have hpos : 0 < M * etaT (E N) (t0 N) := by positivity
      rwa [inv_le_one₀ hpos] at this
    rw [inv_le_iff_one_le_mul₀ (hη0.trans_le hr1)]
    nlinarith
  have hzne : z.im ≠ 0 := by
    rw [hz_def, p729_zt_im]; exact (p729_eta_pos hE (lt_of_le_of_lt hu.2 ht0)).ne'
  have hηz : |z.im|⁻¹ ≤ M := hηM u hu
  -- loops at step `k`: bounded and measurable
  have hFBM : ∀ I : LoopIdx (ZMod (d.L N)), I.WF → 1 ≤ I.a.length →
      p729BM (Pgue d) (fun ω => p729F d t1 t0 K E N k ω I) := fun I h1 h2 =>
    p729_loop_BM hzne h1 h2
  have hFb : ∀ I : LoopIdx (ZMod (d.L N)), I.WF → 1 ≤ I.a.length → ∀ ω,
      ‖p729F d t1 t0 K E N k ω I‖ ≤ M ^ I.a.length := fun I h1 h2 ω =>
    (p729_loop_bound hzne h1 h2 ω).trans (pow_le_pow_left₀ (by positivity) hηz _)
  have hFBM1 : ∀ σ a, p729BM (Pgue d) (fun ω => p729F d t1 t0 K E N k ω ⟨[σ], [a]⟩) :=
    fun σ a => hFBM _ rfl (by simp)
  have hFBM2 : ∀ σ₁ σ₂ x y,
      p729BM (Pgue d) (fun ω => p729F d t1 t0 K E N k ω ⟨[σ₁, σ₂], [x, y]⟩) :=
    fun σ₁ σ₂ x y => hFBM _ rfl (by simp)
  have hFBM3 : ∀ σ₁ σ₂ σ₃ x y w,
      p729BM (Pgue d) (fun ω => p729F d t1 t0 K E N k ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩) :=
    fun σ₁ σ₂ σ₃ x y w => hFBM _ rfl (by simp)
  set Kk : LoopIdx (ZMod (d.L N)) → ℂ := Kt N u with hKk
  set F : Grid.Ωg d → LoopIdx (ZMod (d.L N)) → ℂ := fun ω I => p729F d t1 t0 K E N k ω I with hF
  set e : LoopIdx (ZMod (d.L N)) → ℂ := p729e d t1 t0 K E Kt N k with he
  -- the drift, pointwise
  have hdrift_eq : ∀ ω, loopDriftGUE d (E N) u N J (gueH d t1 t0 K N k ω)
      = eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N k ω) z J
        + GUEPhase.primRhsGUE (d.L N) (d.W N) (F ω) J := fun ω => rfl
  have heG_eq : ∀ ω, eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N k ω) z J
      = (d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
        ((F ω ⟨[s1], [a]⟩ - mSigma (E N) s1) * GUEPhase.SBgue (d.L N) a b *
            F ω ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (F ω ⟨[s2], [a]⟩ - mSigma (E N) s2) * GUEPhase.SBgue (d.L N) a b *
            F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) := fun ω =>
    p729_eG2 (d.L N) (d.W N) (mSigma (E N)) _ z s1 s2 a1 a2
  have hBMeG : p729BM (Pgue d)
      (fun ω => eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N k ω) z J) := by
    simp_rw [heG_eq]
    refine (p729BM_const _).mul (p729BM.sum _ fun a _ => p729BM.sum _ fun b _ => ?_)
    exact ((((hFBM1 s1 a).sub (p729BM_const _)).mul (p729BM_const _)).mul
      (hFBM3 s1 s1 s2 b a1 a2)).add
      ((((hFBM1 s2 a).sub (p729BM_const _)).mul (p729BM_const _)).mul (hFBM3 s1 s2 s2 a1 b a2))
  have hBMprim : p729BM (Pgue d) (fun ω => GUEPhase.primRhsGUE (d.L N) (d.W N) (F ω) J) := by
    simp_rw [GUEPhase.primRhsGUE, hJ, p729_primBil2]
    exact (p729BM_const _).mul (p729BM.sum _ fun a _ => p729BM.sum _ fun b _ =>
      ((hFBM2 s1 s2 a a2).mul (p729BM_const _)).mul (hFBM2 s1 s2 a1 b))
  have hdrift_int : Integrable (fun ω => loopDriftGUE d (E N) u N J (gueH d t1 t0 K N k ω))
      (Pgue d) := by
    simp_rw [hdrift_eq]; exact (hBMeG.add hBMprim).integrable
  -- (R1) Duhamel in expectation
  have hR1 := p729_duhamel d K hE ht1 ht10 ht0 hk (J := J) rfl (by simp [hJ]) hdrift_int
  -- (R2) the primitive side
  have hR2 := p729_Kdisc (W := d.W N) (Kt N) hu hu' hΔ0 hρΛ hMΔ hK2b hKd s1 s2 a1 a2
  have htime : Grid.time t1 t0 K N (k + 1) = u + Δ := p729_time_succ t1 t0 K N k
  -- split of the drift in expectation
  set D : Grid.Ωg d → LoopIdx (ZMod (d.L N)) → ℂ := fun ω => F ω - Kk with hD
  have hDBM2 : ∀ x y, p729BM (Pgue d) (fun ω => D ω ⟨[s1, s2], [x, y]⟩) := fun x y =>
    (hFBM2 s1 s2 x y).sub (p729BM_const _)
  have hDint : ∀ x y, ∫ ω, D ω ⟨[s1, s2], [x, y]⟩ ∂(Pgue d) = e ⟨[s1, s2], [x, y]⟩ := by
    intro x y
    simp only [hD, Pi.sub_apply]
    rw [integral_sub (hFBM2 s1 s2 x y).integrable (integrable_const _), integral_const,
      probReal_univ, one_smul]
    rfl
  have hprim_split : ∀ ω, GUEPhase.primRhsGUE (d.L N) (d.W N) (F ω) J
      = GUEPhase.primRhsGUE (d.L N) (d.W N) Kk J
        + GUEPhase.primBilGUE (d.L N) (d.W N) Kk (D ω) J
        + GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) Kk J
        + GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) (D ω) J := by
    intro ω
    have := GUEPhase.primRhsGUE_sub (d.L N) (d.W N) (F ω) Kk J
    simp only [hD]
    linear_combination this
  have hBMbilL : p729BM (Pgue d) (fun ω => GUEPhase.primBilGUE (d.L N) (d.W N) Kk (D ω) J) := by
    simp_rw [hJ, p729_primBil2]
    exact (p729BM_const _).mul (p729BM.sum _ fun a _ => p729BM.sum _ fun b _ =>
      ((p729BM_const _).mul (p729BM_const _)).mul (hDBM2 a1 b))
  have hBMbilR : p729BM (Pgue d) (fun ω => GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) Kk J) := by
    simp_rw [hJ, p729_primBil2]
    exact (p729BM_const _).mul (p729BM.sum _ fun a _ => p729BM.sum _ fun b _ =>
      ((hDBM2 a a2).mul (p729BM_const _)).mul (p729BM_const _))
  have hBMbilQ : p729BM (Pgue d) (fun ω => GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) (D ω) J) := by
    simp_rw [hJ, p729_primBil2]
    exact (p729BM_const _).mul (p729BM.sum _ fun a _ => p729BM.sum _ fun b _ =>
      ((hDBM2 a a2).mul (p729BM_const _)).mul (hDBM2 a1 b))
  have hprim_int : ∫ ω, GUEPhase.primRhsGUE (d.L N) (d.W N) (F ω) J ∂(Pgue d)
      = GUEPhase.primRhsGUE (d.L N) (d.W N) Kk J
        + GUEPhase.primBilGUE (d.L N) (d.W N) Kk e J
        + GUEPhase.primBilGUE (d.L N) (d.W N) e Kk J
        + ∫ ω, GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) (D ω) J ∂(Pgue d) := by
    simp_rw [hprim_split]
    have i1 : Integrable (fun ω => GUEPhase.primRhsGUE (d.L N) (d.W N) Kk J
        + GUEPhase.primBilGUE (d.L N) (d.W N) Kk (D ω) J) (Pgue d) :=
      (integrable_const _).add hBMbilL.integrable
    have i2 : Integrable (fun ω => GUEPhase.primRhsGUE (d.L N) (d.W N) Kk J
        + GUEPhase.primBilGUE (d.L N) (d.W N) Kk (D ω) J
        + GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) Kk J) (Pgue d) :=
      i1.add hBMbilR.integrable
    rw [integral_add i2 hBMbilQ.integrable, integral_add i1 hBMbilR.integrable,
      integral_add (integrable_const _) hBMbilL.integrable, integral_const, probReal_univ,
      one_smul,
      p729_integral_primBil_left (d.W N) Kk D e s1 s2 a1 a2
        (fun y => (hDBM2 a1 y).integrable) (fun y => hDint a1 y),
      p729_integral_primBil_right (d.W N) Kk D e s1 s2 a1 a2
        (fun x => (hDBM2 x a2).integrable) (fun x => hDint x a2)]
  have hdrift_int_eq : ∫ ω, loopDriftGUE d (E N) u N J (gueH d t1 t0 K N k ω) ∂(Pgue d)
      = (∫ ω, eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N k ω) z J ∂(Pgue d))
        + ∫ ω, GUEPhase.primRhsGUE (d.L N) (d.W N) (F ω) J ∂(Pgue d) := by
    simp_rw [hdrift_eq]
    exact integral_add hBMeG.integrable hBMprim.integrable
  -- the exact identity
  set R1 : ℂ := (∫ ω, p729F d t1 t0 K E N (k + 1) ω J ∂(Pgue d))
      - (∫ ω, p729F d t1 t0 K E N k ω J ∂(Pgue d))
      - (Δ : ℂ) * ∫ ω, loopDriftGUE d (E N) u N J (gueH d t1 t0 K N k ω) ∂(Pgue d) with hR1def
  set R2 : ℂ := Kk J + (Δ : ℂ) * GUEPhase.primRhsGUE (d.L N) (d.W N) Kk J - Kt N (u + Δ) J
    with hR2def
  set IeG : ℂ := ∫ ω, eGtermGUE (d.L N) (d.W N) (mSigma (E N)) (gueH d t1 t0 K N k ω) z J ∂(Pgue d)
    with hIeG
  set IQ : ℂ := ∫ ω, GUEPhase.primBilGUE (d.L N) (d.W N) (D ω) (D ω) J ∂(Pgue d) with hIQ
  set lin : ℂ := GUEPhase.primBilGUE (d.L N) (d.W N) Kk e J
    + GUEPhase.primBilGUE (d.L N) (d.W N) e Kk J with hlin
  have hident : p729e d t1 t0 K E Kt N (k + 1) J
      = (e J + (Δ : ℂ) * lin) + (Δ : ℂ) * IQ + (Δ : ℂ) * IeG + R1 + R2 := by
    have h1 : p729e d t1 t0 K E Kt N (k + 1) J
        = (∫ ω, p729F d t1 t0 K E N (k + 1) ω J ∂(Pgue d)) - Kt N (u + Δ) J := by
      rw [p729e, htime]
    have h2 : e J = (∫ ω, p729F d t1 t0 K E N k ω J ∂(Pgue d)) - Kk J := rfl
    rw [h1, h2, hR1def, hR2def, hdrift_int_eq, hprim_int]
    ring
  -- bounds
  have hΔn : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ0]
  have hlinb : ‖lin‖ ≤ 2 * M * (ρ * Λ) * Bk := by
    have e1 := p729_norm_primBil2_le (d.L N) (d.W N) Kk e s1 s2 a1 a2
      (fun x => hK2b u hu s1 s2 x a2) (fun y => hBk s1 s2 a1 y)
    have e2 := p729_norm_primBil2_le (d.L N) (d.W N) e Kk s1 s2 a1 a2
      (fun x => hBk s1 s2 x a2) (fun y => hK2b u hu s1 s2 a1 y)
    calc ‖lin‖ ≤ _ + _ := norm_add_le _ _
      _ ≤ M * (ρ * Λ) * Bk + M * Bk * (ρ * Λ) := add_le_add e1 e2
      _ = 2 * M * (ρ * Λ) * Bk := by ring
  have hBk0 : 0 ≤ Bk := (norm_nonneg _).trans (hBk s1 s2 a1 a2)
  have hlead : ‖e J + (Δ : ℂ) * lin‖ ≤ (1 + Δ * (2 * M * (ρ * Λ))) * Bk := by
    calc ‖e J + (Δ : ℂ) * lin‖ ≤ ‖e J‖ + Δ * ‖lin‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, hΔn]
      _ ≤ Bk + Δ * (2 * M * (ρ * Λ) * Bk) :=
          add_le_add (hBk s1 s2 a1 a2) (mul_le_mul_of_nonneg_left hlinb hΔ0)
      _ = (1 + Δ * (2 * M * (ρ * Λ))) * Bk := by ring
  -- row Q2
  have hρΛ2 : ρ * Λ ^ 2 ≤ 1 := by
    calc ρ * Λ ^ 2 = (ρ * Λ) * Λ := by ring
      _ ≤ 1 * 1 := mul_le_mul hρΛ hΛ1 hΛ0 zero_le_one
      _ = 1 := by ring
  have hQ : ‖IQ‖ ≤ M * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * M ^ 2) * (2 * M ^ 2) * p) := by
    have := p729_quad (μ := Pgue d) (d.W N) D s1 s2 a1 a2 hDBM2 (g := ρ * Λ ^ 2)
      (C := 2 * M ^ 2) (by positivity) (by positivity) hB hp0
      (fun ω hω x y => hg2 ω hω s1 s2 x y)
      (fun ω x y => by
        simp only [hD, Pi.sub_apply]
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖F ω ⟨[s1, s2], [x, y]⟩‖ ≤ M ^ 2 := hFb ⟨[s1, s2], [x, y]⟩ rfl (by simp) ω
        have h2 : ‖Kk ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ := hK2b u hu s1 s2 x y
        have : M ^ 2 ≥ 1 := one_le_pow₀ hM1
        nlinarith)
    simpa [hM] using this
  -- row Q3
  have hXall : ∀ σ a, ‖∫ ω, (F ω ⟨[σ], [a]⟩ - mSigma (E N) σ) ∂(Pgue d)‖ ≤ ρ * Λ ^ 2 := by
    intro σ a
    have htrue : ∫ ω, (F ω ⟨[true], [a]⟩ - mSigma (E N) true) ∂(Pgue d)
        = (∫ ω, p729F d t1 t0 K E N k ω ⟨[true], [a]⟩ ∂(Pgue d)) - mE (E N) := by
      rw [integral_sub (hFBM1 true a).integrable (integrable_const _), integral_const,
        probReal_univ, one_smul]
      rfl
    cases σ with
    | true => rw [htrue]; exact hX a
    | false =>
      have hconj : (fun ω => F ω ⟨[false], [a]⟩ - mSigma (E N) false)
          = fun ω => (starRingEnd ℂ) (F ω ⟨[true], [a]⟩ - mSigma (E N) true) := by
        funext ω
        simp only [hF, p729F, mSigma_false, mSigma_true, map_sub]
        rw [p729_gloop_one_false (gueH_isHermitian d t1 t0 K N k ω)]
      rw [hconj, integral_conj, RCLike.norm_conj, htrue]
      exact hX a
  have hSBn : ∀ a b : ZMod (d.L N), ‖GUEPhase.SBgue (d.L N) a b‖ = ((d.L N : ℝ))⁻¹ := by
    intro a b; rw [GUEPhase.SBgue_apply, norm_inv, Complex.norm_natCast]
  have hXb : ∀ σ a ω, ‖F ω ⟨[σ], [a]⟩ - mSigma (E N) σ‖ ≤ 2 * M := by
    intro σ a ω
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F ω ⟨[σ], [a]⟩‖ ≤ M ^ 1 := hFb ⟨[σ], [a]⟩ rfl (by simp) ω
    rw [pow_one] at h1
    rw [norm_mSigma hE.le]
    linarith
  have hTb : ∀ σ₁ σ₂ σ₃ x y w ω, ‖F ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩ - Kk ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖
      ≤ 2 * M ^ 3 := by
    intro σ₁ σ₂ σ₃ x y w ω
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F ω ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖ ≤ M ^ 3 :=
      hFb ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩ rfl (by simp) ω
    have h2 : ‖Kk ⟨[σ₁, σ₂, σ₃], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2 := hK3b u hu σ₁ σ₂ σ₃ x y w
    have : M ^ 3 ≥ 1 := one_le_pow₀ hM1
    nlinarith
  have hpair : ∀ (σ : Bool) (a : ZMod (d.L N)) (T : Grid.Ωg d → ℂ) (κ : ℂ) (c : ℂ),
      p729BM (Pgue d) T → ‖κ‖ ≤ ρ * Λ ^ 2 → ‖c‖ = ((d.L N : ℝ))⁻¹ →
      (∀ ω ∉ B, ‖T ω - κ‖ ≤ ρ * Λ ^ 3) → (∀ ω, ‖T ω - κ‖ ≤ 2 * M ^ 3) →
      ‖∫ ω, (F ω ⟨[σ], [a]⟩ - mSigma (E N) σ) * c * T ω ∂(Pgue d)‖
        ≤ ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * M) * (2 * M ^ 3) * p))
          * ((d.L N : ℝ))⁻¹ := by
    intro σ a T κ c hT hκ hc hTg hTa
    have := p729_pair (μ := Pgue d) (fun ω => F ω ⟨[σ], [a]⟩ - mSigma (E N) σ) T κ c
      ((hFBM1 σ a).sub (p729BM_const _)) hT (hXall σ a) hκ (by positivity) (by positivity)
      (by positivity) (by positivity) (norm_nonneg _) hB hp0
      (fun ω hω => ⟨hg1 ω hω σ a, hTg ω hω⟩) (fun ω => ⟨hXb σ a ω, hTa ω⟩)
    rwa [hc] at this
  have heG : ‖IeG‖ ≤ M * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2)
      + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * M) * (2 * M ^ 3) * p))) := by
    rw [hIeG]
    simp_rw [heG_eq]
    have hint : ∀ a b, Integrable (fun ω =>
        (F ω ⟨[s1], [a]⟩ - mSigma (E N) s1) * GUEPhase.SBgue (d.L N) a b *
            F ω ⟨[s1, s1, s2], [b, a1, a2]⟩ +
          (F ω ⟨[s2], [a]⟩ - mSigma (E N) s2) * GUEPhase.SBgue (d.L N) a b *
            F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) (Pgue d) := fun a b =>
      (((((hFBM1 s1 a).sub (p729BM_const _)).mul (p729BM_const _)).mul
        (hFBM3 s1 s1 s2 b a1 a2)).add
        ((((hFBM1 s2 a).sub (p729BM_const _)).mul (p729BM_const _)).mul
          (hFBM3 s1 s2 s2 a1 b a2))).integrable
    refine p729_norm_integral_Wsum_le' (d.W N) _ hint fun a b => ?_
    have hi1 : Integrable (fun ω => (F ω ⟨[s1], [a]⟩ - mSigma (E N) s1) *
        GUEPhase.SBgue (d.L N) a b * F ω ⟨[s1, s1, s2], [b, a1, a2]⟩) (Pgue d) :=
      ((((hFBM1 s1 a).sub (p729BM_const _)).mul (p729BM_const _)).mul
        (hFBM3 s1 s1 s2 b a1 a2)).integrable
    have hi2 : Integrable (fun ω => (F ω ⟨[s2], [a]⟩ - mSigma (E N) s2) *
        GUEPhase.SBgue (d.L N) a b * F ω ⟨[s1, s2, s2], [a1, b, a2]⟩) (Pgue d) :=
      ((((hFBM1 s2 a).sub (p729BM_const _)).mul (p729BM_const _)).mul
        (hFBM3 s1 s2 s2 a1 b a2)).integrable
    rw [integral_add hi1 hi2]
    have p1 := hpair s1 a (fun ω => F ω ⟨[s1, s1, s2], [b, a1, a2]⟩)
      (Kk ⟨[s1, s1, s2], [b, a1, a2]⟩) (GUEPhase.SBgue (d.L N) a b) (hFBM3 s1 s1 s2 b a1 a2)
      (hK3b u hu s1 s1 s2 b a1 a2) (hSBn a b) (fun ω hω => hg3 ω hω s1 s1 s2 b a1 a2)
      (fun ω => hTb s1 s1 s2 b a1 a2 ω)
    have p2 := hpair s2 a (fun ω => F ω ⟨[s1, s2, s2], [a1, b, a2]⟩)
      (Kk ⟨[s1, s2, s2], [a1, b, a2]⟩) (GUEPhase.SBgue (d.L N) a b) (hFBM3 s1 s2 s2 a1 b a2)
      (hK3b u hu s1 s2 s2 a1 b a2) (hSBn a b) (fun ω hω => hg3 ω hω s1 s2 s2 a1 b a2)
      (fun ω => hTb s1 s2 s2 a1 b a2 ω)
    refine (norm_add_le _ _).trans ?_
    linarith
  -- assembly
  have hR1b : ‖R1‖ ≤ (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2) := by
    refine hR1.trans ?_
    have hlen : J.length = 2 := rfl
    rw [hlen]
    have hηk1 : ((zt (E N) (Grid.time t1 t0 K N (k + 1))).im)⁻¹ ≤ M := by
      have := hηM _ (p729_time_mem ht10 hKN hk)
      rwa [abs_of_pos] at this
      rw [p729_zt_im]
      exact p729_eta_pos hE (lt_of_le_of_lt (p729_time_mem ht10 hKN hk).2 ht0)
    have hpos : 0 ≤ ((zt (E N) (Grid.time t1 t0 K N (k + 1))).im)⁻¹ := by
      rw [p729_zt_im]
      exact (inv_pos.2 (p729_eta_pos hE (lt_of_le_of_lt (p729_time_mem ht10 hKN hk).2 ht0))).le
    have hMS : ((ouMatrixSize d N : ℕ) : ℝ) = M := rfl
    rw [hMS]
    have hΔr : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    have h6 : (1 + ((zt (E N) (Grid.time t1 t0 K N (k + 1))).im)⁻¹) ^ (2 + 4) ≤ (1 + M) ^ 6 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc (2 : ℝ) ^ (4 * 2 + 8) * M ^ (2 + 4) *
          (1 + ((zt (E N) (Grid.time t1 t0 K N (k + 1))).im)⁻¹) ^ (2 + 4) * Δ ^ ((3 : ℝ) / 2)
        ≤ (2 : ℝ) ^ (4 * 2 + 8) * M ^ (2 + 4) * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2) := by gcongr
      _ = (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2) := by norm_num
  have hR2b : ‖R2‖ ≤ 3 * M ^ 2 * Δ ^ 2 := hR2
  rw [hident]
  have hQn : ‖(Δ : ℂ) * IQ‖
      ≤ Δ * (M * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * M ^ 2) * (2 * M ^ 2) * p)) := by
    rw [norm_mul, hΔn]; exact mul_le_mul_of_nonneg_left hQ hΔ0
  have hGn : ‖(Δ : ℂ) * IeG‖ ≤ Δ * (M * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2)
      + ((ρ * Λ) * (ρ * Λ ^ 3) + (2 * M) * (2 * M ^ 3) * p)))) := by
    rw [norm_mul, hΔn]; exact mul_le_mul_of_nonneg_left heG hΔ0
  have htri : ‖(e J + (Δ : ℂ) * lin) + (Δ : ℂ) * IQ + (Δ : ℂ) * IeG + R1 + R2‖
      ≤ ‖e J + (Δ : ℂ) * lin‖ + ‖(Δ : ℂ) * IQ‖ + ‖(Δ : ℂ) * IeG‖ + ‖R1‖ + ‖R2‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  refine htri.trans ?_
  unfold p729c
  linarith

end OneStep

/-! ### Row P: the crude Grönwall at a fixed size parameter -/

section PerN

private theorem p729c_nonneg {M ρ Λ p Δ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hΛ : 0 ≤ Λ) (hp : 0 ≤ p)
    (hΔ : 0 ≤ Δ) : 0 ≤ p729c M ρ Λ p Δ := by
  unfold p729c
  have : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ _
  positivity

/-- **The recursion closed by a discrete Grönwall** (row P): at the last grid step,
`‖e_K‖ ≤ exp((t₀ - t₁)·2MρΛ) (e₀ + K c)`. -/
private theorem p729_perN (d : Dims) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {N : ℕ}
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hE : |E N| < 2) (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hKN : K N ≠ 0)
    {Λ ρ p B0 : ℝ}
    (hΛ : Λ = (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (t0 N))⁻¹) (hΛ1 : Λ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p)
    (hMΔ : ((d.L N * d.W N : ℕ) : ℝ) * Grid.step t1 t0 K N ≤ 1)
    (hK2b : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 x y,
      ‖Kt N s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ)
    (hK3b : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 s3 x y w,
      ‖Kt N s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2)
    (hKd : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt N s ⟨[s1, s2], [x, y]⟩)
        (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 N) (t0 N)) s)
    (hX : ∀ k < K N, ∀ a,
      ‖(∫ ω, p729F d t1 t0 K E N k ω ⟨[true], [a]⟩ ∂(Pgue d)) - mE (E N)‖ ≤ ρ * Λ ^ 2)
    {B : Set (Grid.Ωg d)} (hB : Pgue d B ≤ ENNReal.ofReal p)
    (hg1 : ∀ ω ∉ B, ∀ k < K N, ∀ σ a,
      ‖p729F d t1 t0 K E N k ω ⟨[σ], [a]⟩ - mSigma (E N) σ‖ ≤ ρ * Λ)
    (hg2 : ∀ ω ∉ B, ∀ k < K N, ∀ s1 s2 x y, ‖p729F d t1 t0 K E N k ω ⟨[s1, s2], [x, y]⟩
      - Kt N (Grid.time t1 t0 K N k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2)
    (hg3 : ∀ ω ∉ B, ∀ k < K N, ∀ s1 s2 s3 x y w,
      ‖p729F d t1 t0 K E N k ω ⟨[s1, s2, s3], [x, y, w]⟩
        - Kt N (Grid.time t1 t0 K N k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3)
    (hinit : ∀ s1 s2 x y, ‖p729e d t1 t0 K E Kt N 0 ⟨[s1, s2], [x, y]⟩‖ ≤ B0)
    (s1 s2 : Bool) (a1 a2 : ZMod (d.L N)) :
    ‖p729e d t1 t0 K E Kt N (K N) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      Real.exp ((t0 N - t1 N) * (2 * ((d.L N * d.W N : ℕ) : ℝ) * (ρ * Λ))) *
        (B0 + (K N : ℝ) * p729c ((d.L N * d.W N : ℕ) : ℝ) ρ Λ p (Grid.step t1 t0 K N)) := by
  set M : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hM
  set Δ : ℝ := Grid.step t1 t0 K N with hΔ
  set r : ℝ := 2 * M * (ρ * Λ) with hr
  set c : ℝ := p729c M ρ Λ p Δ with hc
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hΔ0 : 0 ≤ Δ := p729_step_nonneg ht10
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]; exact inv_nonneg.2 (mul_nonneg hM0 (p729_eta_pos hE ht0).le)
  have hr0 : 0 ≤ r := by positivity
  have hc0 : 0 ≤ c := p729c_nonneg hM0 hρ0 hΛ0 hp0 hΔ0
  have hB00 : 0 ≤ B0 := (norm_nonneg _).trans (hinit true true 0 0)
  have hq1 : 1 ≤ 1 + Δ * r := by nlinarith
  have claim : ∀ k, k ≤ K N → ∀ s1 s2 x y,
      ‖p729e d t1 t0 K E Kt N k ⟨[s1, s2], [x, y]⟩‖ ≤ (1 + Δ * r) ^ k * (B0 + k * c) := by
    intro k
    induction k with
    | zero =>
      intro _ s1 s2 x y
      simpa using hinit s1 s2 x y
    | succ k ih =>
      intro hk s1 s2 x y
      have hk' : k < K N := hk
      have hstep := p729_one_step d K Kt hE ht1 ht10 ht0 hΛ hΛ1 hρ0 hρΛ hp0 hMΔ hK2b hK3b hKd
        hk' (hX k hk') hB (fun ω hω => hg1 ω hω k hk') (fun ω hω => hg2 ω hω k hk')
        (fun ω hω => hg3 ω hω k hk') (ih hk'.le) s1 s2 x y
      refine hstep.trans ?_
      have hpow : 1 ≤ (1 + Δ * r) ^ (k + 1) := one_le_pow₀ hq1
      have hA : 0 ≤ B0 + k * c := by positivity
      rw [Nat.cast_succ]
      calc (1 + Δ * r) * ((1 + Δ * r) ^ k * (B0 + k * c)) + c
          = (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + c := by ring
        _ ≤ (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + (1 + Δ * r) ^ (k + 1) * c := by
            gcongr; exact le_mul_of_one_le_left hc0 hpow
        _ = (1 + Δ * r) ^ (k + 1) * (B0 + (k + 1) * c) := by ring
  refine (claim (K N) le_rfl s1 s2 a1 a2).trans ?_
  have hexp : (1 + Δ * r) ^ (K N) ≤ Real.exp ((t0 N - t1 N) * r) := by
    have h1 : 1 + Δ * r ≤ Real.exp (Δ * r) := by linarith [Real.add_one_le_exp (Δ * r)]
    calc (1 + Δ * r) ^ (K N) ≤ Real.exp (Δ * r) ^ (K N) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp ((K N : ℝ) * (Δ * r)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp ((t0 N - t1 N) * r) := by rw [← mul_assoc, hΔ, p729_KΔ hKN]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

end PerN

/-! ### Inputs at the size parameter `N`: `K̃` on 1-, 2-, 3-loops and the initial term -/

section Inputs

open scoped Matrix.Norms.L2Operator

variable (d : Dims)

/-- `K̃` on 1-loops is the constant `m(σ)`: `primRhsGUE` of a 1-loop vanishes. -/
private theorem p729_Kt_one {E t1 t0 : ℕ → ℝ} (n0 : ℕ) (hn0 : 3 ≤ n0) (N : ℕ)
    (ht10 : t1 N ≤ t0 N)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t) :
    ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ σ a, Kt N s ⟨[σ], [a]⟩ = mSigma (E N) σ := by
  intro s hs σ a
  have h := (convex_Icc (t1 N) (t0 N)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => Kt N s ⟨[σ], [a]⟩)
    (f' := fun s => GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N s) ⟨[σ], [a]⟩) (C := 0)
    (fun r hr => hK N r hr _ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega))
    (fun r _ => by rw [p729_primRhs_one, norm_zero]) ⟨le_rfl, ht10⟩ hs
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  rw [h, hKinit]
  exact Kgen_one _ _ _ σ a

private theorem p729_gueScale_pos {E : ℕ → ℝ} {N : ℕ} (hE : |E N| < 2) {t : ℝ} (ht : t < 1) :
    0 < gueScale d E N t := by
  unfold gueScale
  have : (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N)
  exact mul_pos this (p729_eta_pos hE ht)

private theorem p729_gueScale_anti {E : ℕ → ℝ} {N : ℕ} (hE : |E N| < 2) {u t : ℝ} (hut : u ≤ t) :
    gueScale d E N t ≤ gueScale d E N u := by
  unfold gueScale
  exact mul_le_mul_of_nonneg_left (p729_eta_le hE hut) (Nat.cast_nonneg _)

private theorem p729_inv_scale_le {E : ℕ → ℝ} {N : ℕ} (hE : |E N| < 2) {u t : ℝ} (hut : u ≤ t)
    (ht : t < 1) : (gueScale d E N u)⁻¹ ≤ (gueScale d E N t)⁻¹ :=
  inv_anti₀ (p729_gueScale_pos d hE ht) (p729_gueScale_anti d hE hut)

/-- **(7.36)** for lengths `2, 3`: `K̃ ≺ (N η_s)^{-|I|+1}` uniformly on `[t₁, t₀]`. -/
private theorem p729_K_bounds {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 3 ≤ n0)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht10 : ∀ N, t1 N ≤ t0 N)
    (ht0 : ∀ N, t0 N < 1)
    (h730 : ∀ᶠ N : ℕ in atTop, t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N))
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ s ∈ Set.Icc (t1 N) (t0 N),
      (∀ s1 s2 x y, ‖Kt N s ⟨[s1, s2], [x, y]⟩‖ ≤ (N : ℝ) ^ τ * (gueScale d E N s)⁻¹) ∧
      (∀ s1 s2 s3 x y w, ‖Kt N s ⟨[s1, s2, s3], [x, y, w]⟩‖
        ≤ (N : ℝ) ^ τ * (gueScale d E N s)⁻¹ ^ 2) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  set κ' := min κ 1 with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hE' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  obtain ⟨C2, hC20, hC2⟩ := norm_Kgen_le_unif hκ'0 hκ'1 2 (by norm_num)
  obtain ⟨C3, hC30, hC3⟩ := norm_Kgen_le_unif hκ'0 hκ'1 3 (by norm_num)
  have hlam : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < gueScale d E N t := fun N t ht =>
    p729_gueScale_pos d (hE2 N) (lt_of_le_of_lt ht.2 (ht0 N))
  have hanti : ∀ N, ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t →
      gueScale d E N t ≤ gueScale d E N u := fun N u _ t _ hut =>
    p729_gueScale_anti d (hE2 N) hut
  have hlamc : ∀ N, ContinuousOn (gueScale d E N) (Set.Icc (t1 N) (t0 N)) := by
    intro N
    have : Continuous (gueScale d E N) := by
      unfold gueScale etaT; fun_prop
    exact this.continuousOn
  have hK' : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      2 ≤ I.length → I.length ≤ 3 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t := fun N t ht I hI h2 h3 =>
    hK N t ht I hI (by omega) (by omega)
  have h730' : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      ((d.W N * d.L N : ℕ) : ℝ) * (t - t1 N) ≤ (N : ℝ) ^ (-τU) * gueScale d E N t := by
    filter_upwards [h730] with N hN t ht
    unfold gueScale
    have he : etaT (E N) (t0 N) ≤ etaT (E N) t := p729_eta_le (hE2 N) ht.2
    have hM0 : (0 : ℝ) ≤ ((d.W N * d.L N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc : ((d.L N * d.W N : ℕ) : ℝ) = ((d.W N * d.L N : ℕ) : ℝ) := by rw [Nat.mul_comm]
    rw [hc]
    have hNr : 0 ≤ (N : ℝ) ^ (-τU) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    calc ((d.W N * d.L N : ℕ) : ℝ) * (t - t1 N)
        ≤ ((d.W N * d.L N : ℕ) : ℝ) * ((N : ℝ) ^ (-τU) * etaT (E N) t) := by
          apply mul_le_mul_of_nonneg_left _ hM0
          have := mul_le_mul_of_nonneg_left he hNr
          linarith [ht.2]
      _ = (N : ℝ) ^ (-τU) * (((d.W N * d.L N : ℕ) : ℝ) * etaT (E N) t) := by ring
  have h732 : UnifDetDom (fun N (I : GUEPhase.LoopSet (d.L N) 3) => ‖Kt N (t1 N) I.1‖)
      (fun N I => (gueScale d E N (t1 N))⁻¹ ^ (I.1.length - 1)) := by
    intro τ hτ
    filter_upwards [hell, eventually_le_rpow (max C2 C3) hτ] with N hellN hCN
    rintro ⟨I, hWF, h2, h3⟩
    have hL3 : (3 : ℝ) ≤ d.L N := by exact_mod_cast d.three_le_L N
    have ht1pos : 0 < t1 N := by nlinarith
    have ht1lt : t1 N < 1 := lt_of_le_of_lt (ht10 N) (ht0 N)
    have hell' : ellHat (d.L N) (t1 N : ℂ) = d.L N := GUEPhase.ellHat_eq_L ht1lt hellN
    have hscale : ((d.W N : ℝ) * (etaT (E N) (t1 N) * ellHat (d.L N) (t1 N : ℂ)))
        = gueScale d E N (t1 N) := by
      rw [hell']; unfold gueScale; push_cast; ring
    have hx : 0 ≤ (gueScale d E N (t1 N))⁻¹ :=
      (inv_pos.2 (p729_gueScale_pos d (hE2 N) ht1lt)).le
    change ‖Kt N (t1 N) I‖ ≤ (N : ℝ) ^ τ * (gueScale d E N (t1 N))⁻¹ ^ (I.length - 1)
    rw [hKinit]
    change ‖Kgen (d.L N) (d.W N) (mSigma (E N)) (t1 N) I‖ ≤ _
    rcases (show I.length = 2 ∨ I.length = 3 by omega) with hl | hl
    · have := hC2 (E N) (hE' N) (d.L N) (d.three_le_L N) (d.W N) (t1 N) ht1pos ht1lt I hWF hl
      rw [hscale] at this
      rw [hl]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hCN) (pow_nonneg hx _)
    · have := hC3 (E N) (hE' N) (d.L N) (d.three_le_L N) (d.W N) (t1 N) ht1pos ht1lt I hWF hl
      rw [hscale] at this
      rw [hl]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hCN) (pow_nonneg hx _)
  have key := GUEPhase.eq736_detDom d.L d.W Kt 3 t1 t0 ht10 (gueScale d E) hlam hanti hlamc hK'
    hτU h730' h732
  intro τ hτ
  filter_upwards [key τ hτ] with N hN s hs
  refine ⟨fun s1 s2 x y => ?_, fun s1 s2 s3 x y w => ?_⟩
  · have := hN (⟨s, hs⟩, ⟨⟨[s1, s2], [x, y]⟩, rfl, by simp [LoopIdx.length],
      by simp [LoopIdx.length]⟩)
    simpa [LoopIdx.length] using this
  · have := hN (⟨s, hs⟩, ⟨⟨[s1, s2, s3], [x, y, w]⟩, rfl, by simp [LoopIdx.length],
      by simp [LoopIdx.length]⟩)
    simpa [LoopIdx.length] using this

/-- **R7**: the only transfer between carriers, the one-time law at step `0` (`map_gueH_zero`). -/
private theorem p729_transfer (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ht1 : 0 ≤ t1 N) {z : ℂ}
    (hz : z.im ≠ 0) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) z I ∂(Pgue d)
      = ∫ ω, gloop (d.L N) (d.W N) (Hflow d N (t1 N) ω) z I ∂(P d) := by
  have hc := (testFun_loopObs_of_im_le (d := d) (N := N) hz (abs_pos.2 hz) le_rfl hwf
    hn).contDiff.continuous
  have hHf : Measurable (Hflow d N (t1 N)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Hflow d N (t1 N) i j
  calc ∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) z I ∂(Pgue d)
      = ∫ ω, loopObs d N z I (gueH d t1 t0 K N 0 ω) ∂(Pgue d) := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact (loopObs_of_isHermitian (gueH_isHermitian d t1 t0 K N 0 ω)).symm
    _ = ∫ M, loopObs d N z I M ∂((Pgue d).map (gueH d t1 t0 K N 0)) :=
        (integral_map (gueH_measurable d t1 t0 K N 0).aemeasurable hc.aestronglyMeasurable).symm
    _ = ∫ M, loopObs d N z I M ∂((P d).map (Hflow d N (t1 N))) := by
        rw [map_gueH_zero d t1 t0 K N ht1]
    _ = ∫ ω, loopObs d N z I (Hflow d N (t1 N) ω) ∂(P d) :=
        integral_map hHf.aemeasurable hc.aestronglyMeasurable
    _ = ∫ ω, gloop (d.L N) (d.W N) (Hflow d N (t1 N) ω) z I ∂(P d) := by
        simp only [loopObs_Hflow]

end Inputs

/-! ### Rows Q4, Q5: the final normalization -/

section Arith

/-- `exp 2 < 7.4`. -/
private theorem p729_exp_two_lt : Real.exp 2 < 7.4 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- **The final normalization** (rows P, Q1–Q4 summed): `≤ 56 ρ Λ³`. -/
private theorem p729_arith {N : ℕ} (hN : 4 ≤ N) {M ρ Λ E0 Δ Kr : ℝ} (A : ℕ) (hA : 80 ≤ A)
    (hKr : Kr = ((N : ℝ) + 1) ^ (2 * A)) (hM1 : 1 ≤ M) (hMN : M ≤ N) (hρ : 1 ≤ ρ)
    (hΛ0 : 0 < Λ) (hΛN : 1 ≤ N * Λ) (hE0 : 0 ≤ E0) (hE01 : E0 ≤ 1) (hKΔ : Kr * Δ = E0)
    (hΔ0 : 0 ≤ Δ) (hθ : E0 * M * Λ * ρ ≤ 1) :
    Real.exp (E0 * (2 * M * (ρ * Λ))) *
        (ρ * Λ ^ 3 + Kr * p729c M ρ Λ (3 / (N : ℝ) ^ 12) Δ) ≤ 56 * ρ * Λ ^ 3 := by
  set x : ℝ := (N : ℝ) with hx
  have hx4 : 4 ≤ x := by rw [hx]; exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x + 1 := by linarith
  have hKr0 : 0 < Kr := by rw [hKr]; positivity
  have hM0 : 0 ≤ M := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hΛ3 : 1 / x ^ 3 ≤ Λ ^ 3 := by
    have h1 : 1 / x ≤ Λ := by rw [div_le_iff₀ hx0]; linarith
    calc 1 / x ^ 3 = (1 / x) ^ 3 := by rw [one_div_pow]
      _ ≤ Λ ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  -- the exponential factor
  have hexp : Real.exp (E0 * (2 * M * (ρ * Λ))) ≤ 7.4 := by
    have : E0 * (2 * M * (ρ * Λ)) ≤ 2 := by
      have e : E0 * (2 * M * (ρ * Λ)) = 2 * (E0 * M * Λ * ρ) := by ring
      rw [e]; linarith
    exact ((Real.exp_le_exp.2 this).trans p729_exp_two_lt.le)
  -- the three pieces of `K c`
  have hsqrt : Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hΔ0 (by norm_num), Real.rpow_one]
  have hΔK : Δ ≤ 1 / Kr := by
    rw [le_div_iff₀ hKr0]; linarith [mul_comm Kr Δ]
  have hsqrtΔ : Real.sqrt Δ ≤ 1 / (x + 1) ^ A := by
    have h1 : Real.sqrt (1 / Kr) = 1 / (x + 1) ^ A := by
      rw [hKr, pow_mul', one_div, Real.sqrt_inv, Real.sqrt_sq (by positivity), one_div]
    rw [← h1]; exact Real.sqrt_le_sqrt hΔK
  have hpow80 : (x + 1) ^ 80 ≤ (x + 1) ^ A := pow_le_pow_right₀ hx1 hA
  -- piece Q2 + Q3 (main)
  set X : ℝ := M * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + (2 * M ^ 2) * (2 * M ^ 2) * (3 / x ^ 12))
      + M * (2 * ((ρ * Λ ^ 2) * (ρ * Λ ^ 2) + ((ρ * Λ) * (ρ * Λ ^ 3)
        + (2 * M) * (2 * M ^ 3) * (3 / x ^ 12)))) with hX
  have hXeq : X = 5 * M * ρ ^ 2 * Λ ^ 4 + 36 * M ^ 5 / x ^ 12 := by rw [hX]; ring
  have hmain : E0 * (5 * M * ρ ^ 2 * Λ ^ 4) ≤ 5 * ρ * Λ ^ 3 := by
    have h : E0 * (5 * M * ρ ^ 2 * Λ ^ 4) = 5 * ρ * Λ ^ 3 * (E0 * M * Λ * ρ) := by ring
    rw [h]
    have : 0 ≤ 5 * ρ * Λ ^ 3 := by positivity
    exact mul_le_of_le_one_right this hθ
  have hbad : E0 * (36 * M ^ 5 / x ^ 12) ≤ 1 / (3 * x ^ 3) := by
    have hM5 : M ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ hM0 hMN 5
    have h1 : E0 * (36 * M ^ 5 / x ^ 12) ≤ 36 * x ^ 5 / x ^ 12 := by
      have : 0 ≤ 36 * M ^ 5 / x ^ 12 := by positivity
      calc E0 * (36 * M ^ 5 / x ^ 12) ≤ 1 * (36 * M ^ 5 / x ^ 12) :=
            mul_le_mul_of_nonneg_right hE01 this
        _ ≤ 36 * x ^ 5 / x ^ 12 := by rw [one_mul]; gcongr
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hx4' : (256 : ℝ) ≤ x ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hx4 4
      norm_num at this; linarith
    have h8 : 0 < x ^ 8 := by positivity
    calc 36 * x ^ 5 * (3 * x ^ 3) = 108 * x ^ 8 := by ring
      _ ≤ 256 * x ^ 8 := by linarith
      _ ≤ x ^ 4 * x ^ 8 := mul_le_mul_of_nonneg_right hx4' h8.le
      _ = 1 * x ^ 12 := by ring
  -- piece Q4, Taylor
  have htaylor : Kr * ((2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2))
      ≤ 1 / (3 * x ^ 3) := by
    rw [hsqrt]
    have hsΔ0 : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
    have e : Kr * ((2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * (Δ * Real.sqrt Δ))
        = (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * (Kr * Δ) * Real.sqrt Δ := by ring
    rw [e, hKΔ]
    have hM6 : M ^ 6 * (1 + M) ^ 6 ≤ x ^ 6 * (1 + x) ^ 6 :=
      mul_le_mul (pow_le_pow_left₀ hM0 hMN 6) (pow_le_pow_left₀ (by linarith) (by linarith) 6)
        (by positivity) (by positivity)
    have h1 : (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * E0 * Real.sqrt Δ
        ≤ (2 : ℝ) ^ 16 * (x ^ 6 * (1 + x) ^ 6) * 1 * (1 / (x + 1) ^ A) := by
      have : (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * E0 * Real.sqrt Δ
          = (2 : ℝ) ^ 16 * (M ^ 6 * (1 + M) ^ 6) * E0 * Real.sqrt Δ := by ring
      rw [this]
      gcongr
    refine h1.trans ?_
    rw [mul_one, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- `3 · 2^16 x^9 (1+x)^6 ≤ (x+1)^A`
    have hx9 : x ^ 9 ≤ (x + 1) ^ 9 := pow_le_pow_left₀ hx0.le (by linarith) 9
    have h5 : (3 * 2 ^ 16 : ℝ) ≤ (x + 1) ^ 65 := by
      calc (3 * 2 ^ 16 : ℝ) ≤ 5 ^ 8 := by norm_num
        _ ≤ (x + 1) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
        _ ≤ (x + 1) ^ 65 := pow_le_pow_right₀ hx1 (by norm_num)
    have hA' : (2 : ℝ) ^ 16 * (x ^ 6 * (1 + x) ^ 6) * (3 * x ^ 3)
        = (3 * 2 ^ 16) * x ^ 9 * (x + 1) ^ 6 := by ring
    rw [hA']
    calc (3 * 2 ^ 16 : ℝ) * x ^ 9 * (x + 1) ^ 6 ≤ (x + 1) ^ 65 * (x + 1) ^ 9 * (x + 1) ^ 6 := by
          gcongr
      _ = (x + 1) ^ 80 := by rw [← pow_add, ← pow_add]
      _ ≤ (x + 1) ^ A := hpow80
      _ = 1 * (x + 1) ^ A := (one_mul _).symm
  -- piece Q4, primitive side
  have hkdisc : Kr * (3 * M ^ 2 * Δ ^ 2) ≤ 1 / (3 * x ^ 3) := by
    have e : Kr * (3 * M ^ 2 * Δ ^ 2) = 3 * M ^ 2 * (Kr * Δ) * Δ := by ring
    rw [e, hKΔ]
    have hM2 : M ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hM0 hMN 2
    have h1 : 3 * M ^ 2 * E0 * Δ ≤ 3 * x ^ 2 * 1 * (1 / Kr) := by gcongr
    refine h1.trans ?_
    rw [mul_one, mul_one_div, div_le_div_iff₀ hKr0 (by positivity), hKr]
    have hx5 : x ^ 5 ≤ (x + 1) ^ 5 := pow_le_pow_left₀ hx0.le (by linarith) 5
    have h9 : (9 : ℝ) ≤ (x + 1) ^ 155 := by
      calc (9 : ℝ) ≤ 5 ^ 2 := by norm_num
        _ ≤ (x + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
        _ ≤ (x + 1) ^ 155 := pow_le_pow_right₀ hx1 (by norm_num)
    have h160 : (x + 1) ^ 160 ≤ (x + 1) ^ (2 * A) := pow_le_pow_right₀ hx1 (by omega)
    calc 3 * x ^ 2 * (3 * x ^ 3) = 9 * x ^ 5 := by ring
      _ ≤ (x + 1) ^ 155 * (x + 1) ^ 5 := by gcongr
      _ = (x + 1) ^ 160 := by rw [← pow_add]
      _ ≤ (x + 1) ^ (2 * A) := h160
      _ = 1 * (x + 1) ^ (2 * A) := (one_mul _).symm
  -- assembly
  have hKc : Kr * p729c M ρ Λ (3 / x ^ 12) Δ ≤ 5 * ρ * Λ ^ 3 + Λ ^ 3 := by
    unfold p729c
    rw [← hX, hXeq]
    have e : Kr * (Δ * (5 * M * ρ ^ 2 * Λ ^ 4 + 36 * M ^ 5 / x ^ 12)
        + (2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2) + 3 * M ^ 2 * Δ ^ 2)
        = (Kr * Δ) * (5 * M * ρ ^ 2 * Λ ^ 4) + (Kr * Δ) * (36 * M ^ 5 / x ^ 12)
          + Kr * ((2 : ℝ) ^ 16 * M ^ 6 * (1 + M) ^ 6 * Δ ^ ((3 : ℝ) / 2))
          + Kr * (3 * M ^ 2 * Δ ^ 2) := by ring
    rw [e, hKΔ]
    have hsum : 1 / (3 * x ^ 3) + 1 / (3 * x ^ 3) + 1 / (3 * x ^ 3) = 1 / x ^ 3 := by
      field_simp; ring
    linarith
  have hin : 0 ≤ ρ * Λ ^ 3 + Kr * p729c M ρ Λ (3 / x ^ 12) Δ := by
    have := p729c_nonneg hM0 hρ0 hΛ0.le (by positivity : (0 : ℝ) ≤ 3 / x ^ 12) hΔ0
    positivity
  have hρΛ3 : Λ ^ 3 ≤ ρ * Λ ^ 3 := le_mul_of_one_le_left (by positivity) hρ
  calc Real.exp (E0 * (2 * M * (ρ * Λ))) * (ρ * Λ ^ 3 + Kr * p729c M ρ Λ (3 / x ^ 12) Δ)
      ≤ 7.4 * (ρ * Λ ^ 3 + Kr * p729c M ρ Λ (3 / x ^ 12) Δ) :=
        mul_le_mul_of_nonneg_right hexp hin
    _ ≤ 7.4 * (7 * (ρ * Λ ^ 3)) := by gcongr; linarith
    _ = 51.8 * (ρ * Λ ^ 3) := by ring
    _ ≤ 56 * (ρ * Λ ^ 3) := by
        have : 0 ≤ ρ * Λ ^ 3 := by positivity
        linarith
    _ = 56 * ρ * Λ ^ 3 := by ring

end Arith

/-! ### The bad events of `GUEPathBounds.lk` -/

section Bad

variable (d : Dims)

/-- The failure event of `hP.lk n` at level `τ`, size parameter `N`. -/
private def p729Bad (E t1 t0 : ℕ → ℝ) (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (n0 n N : ℕ)
    (τ : ℝ) : Set (Grid.Ωg d) :=
  {ω | ∃ p : Fin (gueGridK n0 N + 1) × LoopData (d.L N) n,
    (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹ ^ n <
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) p.2.idx
        - Kt N (Grid.time t1 t0 (gueGridK n0) N p.1) p.2.idx‖}

private theorem p729_not_bad {E t1 t0 : ℕ → ℝ} {Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ}
    {n0 n N : ℕ} {τ : ℝ} {ω : Grid.Ωg d} (hω : ω ∉ p729Bad d E t1 t0 Kt n0 n N τ) {k : ℕ}
    (hk : k ≤ gueGridK n0 N) (u : LoopData (d.L N) n) :
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) u.idx
        - Kt N (Grid.time t1 t0 (gueGridK n0) N k) u.idx‖
      ≤ (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ n := by
  by_contra h
  exact hω ⟨(⟨k, Nat.lt_succ_of_le hk⟩, u), lt_of_not_ge h⟩

end Bad

/-! ### The main statement -/

variable (d : Dims)

/-- **(7.29) at `t₀`** on the GUE-phase grid (§5.8 with Lemma 5.15), `σ = (+, σ₂)`. -/
theorem gueGrid_eq729 {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 3 ≤ n0)
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
    (hK2 : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ (σ₁ σ₂ : Bool) (a b : ZMod (d.L N)),
      Kt N t ⟨[σ₁, σ₂], [a, b]⟩ =
        GUEPhase.kTwoGUE (d.L N) (d.W N) (mSigma (E N)) (t1 N) t σ₁ σ₂ a b)
    (hB : BoundsN (sample d) E t1) (hP : GUEPathBounds d E t1 t0 (gueGridK n0) n0 Kt) :
    ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (σ₂ : Bool) (a b : ZMod (d.L N)),
      ‖(∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N (gueGridK n0 N) ω)
            (zt (E N) (t0 N)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue d)) -
        GUEPhase.kTwoGUE (d.L N) (d.W N) (mSigma (E N)) (t1 N) (t0 N) true σ₂ a b‖ ≤
      (d.W N : ℝ) ^ δ * (((d.L N * d.W N : ℕ) : ℝ) * (zt (E N) (t0 N)).im)⁻¹ ^ 3 := by
  intro δ hδ
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  set τ : ℝ := min (δ / 4) τU with hτdef
  have hτ : 0 < τ := lt_min (by positivity) hτU
  have hττU : τ ≤ τU := min_le_right _ _
  have hτδ : τ ≤ δ / 4 := min_le_left _ _
  have hKone : ∀ N, ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ σ a, Kt N s ⟨[σ], [a]⟩ = mSigma (E N) σ :=
    fun N => p729_Kt_one d n0 hn0 N (ht10 N) Kt hKinit hK
  have hKmem : ∀ N k, k ≤ gueGridK n0 N →
      Grid.time t1 t0 (gueGridK n0) N k ∈ Set.Icc (t1 N) (t0 N) := fun N k hk =>
    p729_time_mem (ht10 N) (gueGridK_ne_zero n0 N) hk
  -- the D4b input, from `hP.lk 1` (the `+` 1-loops, `K̃ = m`)
  have h1 : StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × ZMod (d.L N)) ω =>
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) ⟨[true], [p.2]⟩ - mE (E N)‖)
      (fun N p _ => (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹) := by
    intro τ' hτ' D hD
    filter_upwards [hP.lk 1 le_rfl (by omega) τ' hτ' D hD] with N hN
    refine le_trans (measure_mono ?_) hN
    rintro ω ⟨⟨k, a⟩, hlt⟩
    refine ⟨(k, (fun _ => true, fun _ => a)), ?_⟩
    have hk : (k : ℕ) ≤ gueGridK n0 N := Nat.lt_succ_iff.1 k.isLt
    have hKt := hKone N _ (hKmem N k hk) true a
    change (N : ℝ) ^ τ' * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ 1 <
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) ⟨[true], [a]⟩
        - Kt N (Grid.time t1 t0 (gueGridK n0) N k) ⟨[true], [a]⟩‖
    rw [hKt, pow_one, mSigma_true]
    exact hlt
  have hX := gueGrid_expect_oneLoop d hκ n0 hE ht1 ht10 ht0 h1 τ hτ
  have hKb := p729_K_bounds d hκ hτU n0 hn0 hE ht10 ht0 h730 hell Kt hKinit hK τ hτ
  have hb1 := hP.lk 1 le_rfl (by omega) τ hτ 12 (by norm_num)
  have hb2 := hP.lk 2 (by norm_num) (by omega) τ hτ 12 (by norm_num)
  have hb3 := hP.lk 3 (by norm_num) hn0 τ hτ 12 (by norm_num)
  have hin := hB.expect τ hτ
  filter_upwards [d.dim, d.bandwidth, h730, hscale, hell, hKb, hX, hb1, hb2, hb3, hin,
    eventually_ge_atTop 4, eventually_le_rpow 56 hτ] with N hdim hbw h730N hscaleN hellN hKbN
    hXN hb1N hb2N hb3N hinN hN4 hN56
  intro σ₂ a b
  -- the size parameter `N`: scales
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set M : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hM
  have hLW1 : 1 ≤ d.L N * d.W N :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N)).ne'
  have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast hLW1
  have hMN : M ≤ N := by
    rw [hM, Nat.mul_comm]; exact_mod_cast hdim.1
  set η0 : ℝ := etaT (E N) (t0 N) with hη0
  have hη0pos : 0 < η0 := p729_eta_pos (hE2 N) (ht0 N)
  have hη01 : η0 ≤ 1 := by
    rw [hη0]; unfold etaT
    have him : (mE (E N)).im ≤ 1 := by
      have := Complex.im_le_norm (mE (E N)); rwa [norm_mE (hE2 N).le] at this
    have h0 : 0 ≤ 1 - t0 N := by linarith [ht0 N]
    have h1' : 1 - t0 N ≤ 1 := by linarith [ht1 N, ht10 N]
    have hm0 : 0 ≤ (mE (E N)).im := (mE_im_pos (hE2 N)).le
    calc (1 - t0 N) * (mE (E N)).im ≤ 1 * 1 := mul_le_mul h1' him hm0 zero_le_one
      _ = 1 := one_mul 1
  set Λ : ℝ := (M * η0)⁻¹ with hΛ
  have hΛpos : 0 < Λ := by positivity
  have hΛτ : Λ ≤ (N : ℝ) ^ (-τU) := hscaleN
  have hΛ1 : Λ ≤ 1 := hΛτ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  set ρ : ℝ := (N : ℝ) ^ τ with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hN1 hτ.le
  have hρ0 : 0 ≤ ρ := by linarith
  have hρτ : ρ * (N : ℝ) ^ (-τU) ≤ 1 := by
    rw [hρ, ← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hρΛ : ρ * Λ ≤ 1 := (mul_le_mul_of_nonneg_left hΛτ hρ0).trans hρτ
  have hinvs : ∀ s ∈ Set.Icc (t1 N) (t0 N), (gueScale d E N s)⁻¹ ≤ Λ := fun s hs =>
    p729_inv_scale_le d (hE2 N) hs.2 (ht0 N)
  have hinvs0 : ∀ s ∈ Set.Icc (t1 N) (t0 N), 0 ≤ (gueScale d E N s)⁻¹ := fun s hs =>
    (inv_pos.2 (p729_gueScale_pos d (hE2 N) (lt_of_le_of_lt hs.2 (ht0 N)))).le
  have hinvsn : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ n : ℕ, (gueScale d E N s)⁻¹ ^ n ≤ Λ ^ n :=
    fun s hs n => pow_le_pow_left₀ (hinvs0 s hs) (hinvs s hs) n
  -- `K̃` on 2- and 3-loops
  have hK2b : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 x y,
      ‖Kt N s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ := fun s hs s1 s2 x y =>
    ((hKbN s hs).1 s1 s2 x y).trans (mul_le_mul_of_nonneg_left (hinvs s hs) hρ0)
  have hK3b : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 s3 x y w,
      ‖Kt N s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2 := fun s hs s1 s2 s3 x y w =>
    ((hKbN s hs).2 s1 s2 s3 x y w).trans (mul_le_mul_of_nonneg_left (hinvsn s hs 2) hρ0)
  have hKd : ∀ s ∈ Set.Icc (t1 N) (t0 N), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt N s ⟨[s1, s2], [x, y]⟩)
        (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N s) ⟨[s1, s2], [x, y]⟩)
        (Set.Icc (t1 N) (t0 N)) s := fun s hs s1 s2 x y =>
    hK N s hs _ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
  -- D4b at the grid times
  have hX' : ∀ k < gueGridK n0 N, ∀ a,
      ‖(∫ ω, p729F d t1 t0 (gueGridK n0) E N k ω ⟨[true], [a]⟩ ∂(Pgue d)) - mE (E N)‖
        ≤ ρ * Λ ^ 2 := by
    intro k hk a
    have := hXN (⟨k, by omega⟩, a)
    exact this.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem N k hk.le) 2) hρ0)
  -- the bad event
  set B : Set (Grid.Ωg d) := p729Bad d E t1 t0 Kt n0 1 N τ ∪ p729Bad d E t1 t0 Kt n0 2 N τ
    ∪ p729Bad d E t1 t0 Kt n0 3 N τ with hBdef
  have hNrpow : (N : ℝ) ^ (-(12 : ℝ)) = 1 / (N : ℝ) ^ 12 := by
    rw [Real.rpow_neg hN0.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  have hBm : Pgue d B ≤ ENNReal.ofReal (3 / (N : ℝ) ^ 12) := by
    have h12 : Pgue d (p729Bad d E t1 t0 Kt n0 1 N τ ∪ p729Bad d E t1 t0 Kt n0 2 N τ)
        ≤ Pgue d (p729Bad d E t1 t0 Kt n0 1 N τ) + Pgue d (p729Bad d E t1 t0 Kt n0 2 N τ) :=
      measure_union_le _ _
    have h123 : Pgue d B ≤ Pgue d (p729Bad d E t1 t0 Kt n0 1 N τ ∪ p729Bad d E t1 t0 Kt n0 2 N τ)
        + Pgue d (p729Bad d E t1 t0 Kt n0 3 N τ) := measure_union_le _ _
    refine (h123.trans (add_le_add h12 le_rfl)).trans ?_
    refine (add_le_add (add_le_add hb1N hb2N) hb3N).trans (le_of_eq ?_)
    rw [hNrpow, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have hg1 : ∀ ω ∉ B, ∀ k < gueGridK n0 N, ∀ σ a,
      ‖p729F d t1 t0 (gueGridK n0) E N k ω ⟨[σ], [a]⟩ - mSigma (E N) σ‖ ≤ ρ * Λ := by
    intro ω hω k hk σ a
    have hω1 : ω ∉ p729Bad d E t1 t0 Kt n0 1 N τ := fun h => hω (Or.inl (Or.inl h))
    have h : ‖p729F d t1 t0 (gueGridK n0) E N k ω ⟨[σ], [a]⟩
        - Kt N (Grid.time t1 t0 (gueGridK n0) N k) ⟨[σ], [a]⟩‖
        ≤ (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ 1 :=
      p729_not_bad d hω1 hk.le ((fun _ => σ), (fun _ => a))
    rw [hKone N _ (hKmem N k hk.le) σ a] at h
    refine h.trans ?_
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (hinvs _ (hKmem N k hk.le)) hρ0
  have hg2 : ∀ ω ∉ B, ∀ k < gueGridK n0 N, ∀ s1 s2 x y,
      ‖p729F d t1 t0 (gueGridK n0) E N k ω ⟨[s1, s2], [x, y]⟩
        - Kt N (Grid.time t1 t0 (gueGridK n0) N k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2 := by
    intro ω hω k hk s1 s2 x y
    have hω2 : ω ∉ p729Bad d E t1 t0 Kt n0 2 N τ := fun h => hω (Or.inl (Or.inr h))
    have h := p729_not_bad d hω2 hk.le (![s1, s2], ![x, y])
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem N k hk.le) 2) hρ0)
  have hg3 : ∀ ω ∉ B, ∀ k < gueGridK n0 N, ∀ s1 s2 s3 x y w,
      ‖p729F d t1 t0 (gueGridK n0) E N k ω ⟨[s1, s2, s3], [x, y, w]⟩
        - Kt N (Grid.time t1 t0 (gueGridK n0) N k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3 := by
    intro ω hω k hk s1 s2 s3 x y w
    have hω3 : ω ∉ p729Bad d E t1 t0 Kt n0 3 N τ := fun h => hω (Or.inr h)
    have h := p729_not_bad d hω3 hk.le (![s1, s2, s3], ![x, y, w])
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem N k hk.le) 3) hρ0)
  -- row Q1: the initial term
  have ht1mem : t1 N ∈ Set.Icc (t1 N) (t0 N) := ⟨le_rfl, ht10 N⟩
  have hL3 : (3 : ℝ) ≤ d.L N := by exact_mod_cast d.three_le_L N
  have ht1lt : t1 N < 1 := lt_of_le_of_lt (ht10 N) (ht0 N)
  have hinit : ∀ s1 s2 x y,
      ‖p729e d t1 t0 (gueGridK n0) E Kt N 0 ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 3 := by
    intro s1 s2 x y
    have hz : (zt (E N) (t1 N)).im ≠ 0 := by
      rw [p729_zt_im]; exact (p729_eta_pos (hE2 N) ht1lt).ne'
    have he : p729e d t1 t0 (gueGridK n0) E Kt N 0 ⟨[s1, s2], [x, y]⟩
        = (sample d).ELval (E N) N (t1 N) ⟨[s1, s2], [x, y]⟩
          - (band d).Kval (E N) N (t1 N) ⟨[s1, s2], [x, y]⟩ := by
      unfold p729e p729F
      rw [Grid.time_zero, hKinit, p729_transfer d t1 t0 (gueGridK n0) N (ht1 N) hz
        (I := ⟨[s1, s2], [x, y]⟩) rfl (by simp)]
      rfl
    have h := hinN (![s1, s2], ![x, y])
    have hsc : (band d).scale (E N) N (t1 N) = gueScale d E N (t1 N) := by
      change (d.W N : ℝ) * ellHat (d.L N) (t1 N : ℂ) * etaT (E N) (t1 N) = _
      rw [GUEPhase.ellHat_eq_L ht1lt hellN]
      unfold gueScale; push_cast; ring
    rw [he]
    refine h.trans ?_
    rw [hsc]
    exact mul_le_mul_of_nonneg_left (hinvsn _ ht1mem 3) hρ0
  -- `M Δ ≤ 1`
  have hKge : (N : ℝ) + 1 ≤ (gueGridK n0 N : ℝ) := by
    unfold gueGridK; push_cast
    exact le_self_pow₀ (by linarith) (by omega)
  have hKpos : (0 : ℝ) < (gueGridK n0 N : ℝ) := by linarith
  have hE0 : 0 ≤ t0 N - t1 N := by linarith [ht10 N]
  have hE01 : t0 N - t1 N ≤ 1 := by linarith [ht1 N, ht0 N]
  have hMΔ : M * Grid.step t1 t0 (gueGridK n0) N ≤ 1 := by
    unfold Grid.step
    rw [mul_div_assoc']
    rw [div_le_one hKpos]
    nlinarith
  -- rows P, Q1–Q4 at `N`
  have hper := p729_perN d (gueGridK n0) Kt (hE2 N) (ht1 N) (ht10 N) (ht0 N)
    (gueGridK_ne_zero n0 N) (Λ := Λ) (ρ := ρ) (p := 3 / (N : ℝ) ^ 12) (B0 := ρ * Λ ^ 3) rfl hΛ1
    hρ0 hρΛ (by positivity) hMΔ hK2b hK3b hKd hX' hBm hg1 hg2 hg3 hinit true σ₂ a b
  have hΛN : 1 ≤ (N : ℝ) * Λ := by
    rw [hΛ, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    calc M * η0 ≤ (N : ℝ) * 1 := mul_le_mul hMN hη01 hη0pos.le hN0.le
      _ = N := mul_one _
  have hθ : (t0 N - t1 N) * M * Λ * ρ ≤ 1 := by
    have h1 : (t0 N - t1 N) * M * Λ = (t0 N - t1 N) / η0 := by
      rw [hΛ]; field_simp
    have h2 : (t0 N - t1 N) / η0 ≤ (N : ℝ) ^ (-τU) := by
      rw [div_le_iff₀ hη0pos]; exact h730N
    rw [h1]
    calc (t0 N - t1 N) / η0 * ρ ≤ (N : ℝ) ^ (-τU) * ρ :=
          mul_le_mul_of_nonneg_right h2 hρ0
      _ ≤ 1 := by linarith
  have hKr : ((gueGridK n0 N : ℕ) : ℝ) = ((N : ℝ) + 1) ^ (2 * (16 * n0 + 32)) := by
    unfold gueGridK; push_cast; ring_nf
  have harith := p729_arith (N := N) hN4 (M := M) (ρ := ρ) (Λ := Λ) (E0 := t0 N - t1 N)
    (Δ := Grid.step t1 t0 (gueGridK n0) N) (Kr := (gueGridK n0 N : ℝ)) (16 * n0 + 32)
    (by omega) hKr hM1 hMN hρ1 hΛpos hΛN hE0 hE01 (p729_KΔ (gueGridK_ne_zero n0 N))
    (p729_step_nonneg (ht10 N)) hθ
  -- row Q5: `56 N^τ ≤ W^δ`
  have hW : 56 * ρ ≤ (d.W N : ℝ) ^ δ := by
    have h1 : 56 * ρ ≤ (N : ℝ) ^ (δ / 2) := by
      calc 56 * ρ ≤ (N : ℝ) ^ τ * (N : ℝ) ^ τ := mul_le_mul_of_nonneg_right hN56 hρ0
        _ = (N : ℝ) ^ (τ + τ) := (Real.rpow_add hN0 _ _).symm
        _ ≤ (N : ℝ) ^ (δ / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N := by
      refine le_trans ?_ hbw
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [d.c_pos])
    calc 56 * ρ ≤ (N : ℝ) ^ (δ / 2) := h1
      _ = ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ δ := by
          rw [← Real.rpow_mul hN0.le]; ring_nf
      _ ≤ (d.W N : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h2 hδ.le
  -- the left side is `e_K`
  have hlhs : (∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N (gueGridK n0 N) ω)
        (zt (E N) (t0 N)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue d)) -
      GUEPhase.kTwoGUE (d.L N) (d.W N) (mSigma (E N)) (t1 N) (t0 N) true σ₂ a b
      = p729e d t1 t0 (gueGridK n0) E Kt N (gueGridK n0 N) ⟨[true, σ₂], [a, b]⟩ := by
    unfold p729e p729F
    rw [Grid.time_last t1 t0 (gueGridK n0) N (gueGridK_ne_zero n0 N),
      hK2 N (t0 N) ⟨ht10 N, le_rfl⟩ true σ₂ a b]
  have hrhs : (((d.L N * d.W N : ℕ) : ℝ) * (zt (E N) (t0 N)).im)⁻¹ = Λ := by
    rw [p729_zt_im]
  rw [hlhs, hrhs]
  calc ‖p729e d t1 t0 (gueGridK n0) E Kt N (gueGridK n0 N) ⟨[true, σ₂], [a, b]⟩‖
      ≤ 56 * ρ * Λ ^ 3 := hper.trans harith
    _ ≤ (d.W N : ℝ) ^ δ * Λ ^ 3 :=
        mul_le_mul_of_nonneg_right hW (by positivity)

end RBM.Gauss.GUEGrid

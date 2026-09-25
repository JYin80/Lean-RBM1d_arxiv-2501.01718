/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.GridMarkov
import RBM1D.Gauss.GridOneStep
import RBM1D.Gauss.GridDriftLip
import RBM1D.Gauss.GridStopFilt
import RBM1D.Gauss.LoopIto
import RBM1D.Gauss.LoopC2
import RBM1D.Gauss.MomentDuhamelHypGauss

/-!
# T1503 — the one-step drift identity of the 2-loop on the grid (discrete (2.45))

Formalization of `docs/claude-team/pilot-P4P5-paper.md` §3 (the discrete integrated hierarchy),
A5 core part 1.  Combines the merged grid infrastructure (T1481 `RBM.Gauss.Grid.H`, T1482
`RBM.Gauss.Grid.condExp_freeze`, T1486 `RBM.Gauss.oneStep_error_le`/`RBM.Gauss.Grid.genPt`,
T1487 `RBM.Gauss.Grid.loopDrift`/`RBM.Gauss.Grid.norm_loopDrift_sub_le`) with the deterministic
drift identity `RBM.Gauss.generator_add_zMotion_gauss` (`Gauss/LoopIto.lean`) to produce the
one-step conditional drift bound for the loop observable on the grid.

## Main results

* `RBM.Gauss.Grid.condExp_loop_step` (T1) : `condExp_freeze`, lifted to the complex-valued loop
  observable via `RBM.Gauss.Grid.condExp_freezeC` (a straightforward real/imaginary-part
  generalisation of the existing real-valued `condExp_freeze`, since none of its ingredients are
  specific to `ℝ`).
* `RBM.Gauss.Grid.loop_step_space_err` (T2) : `oneStep_error_le` specialised to `Φ = loopObs`,
  with the Lipschitz constant of `genPt Φ_u` built from `driftLip` (T1487) and a new
  `zMotionLip` (the `M`-Lipschitz bound for `zMotion`, via `norm_gloop_sub_le`), combined through
  the identity `genPt_eq_loopDrift_sub_zMotion`.
* `RBM.Gauss.Grid.loop_step_time_err` (T3) : the quadratic-remainder bound for the loop as a
  function of the moving spectral parameter `z_u`, via the exact FTC identity
  `g(u') - g(u) = ∫_u^{u'} zMotion(M, z_v, I) dv` (`RBM.Gauss.hasDerivAt_gloop_zt`) and a new
  `z`-Lipschitz bound for `zMotion` at fixed `M` (`norm_green_sub_le`, `norm_gloop_sub_le`).
* `RBM.Gauss.Grid.condExp_loop_drift` (T4) : combines (T1)-(T3). To avoid needing a
  `z`-Lipschitz bound for `loopDrift`/`genPt` itself (not available and not needed), the
  decomposition compares `Φ_{u_{k+1}}` and `Φ_{u_k}` **inside** the integral over the fresh
  increment (via (T3), pointwise in the increment) rather than comparing `genPt(Φ_{u_{k+1}})`
  and `genPt(Φ_{u_k})` directly; (T2) is then only ever invoked at the single time `u_k`.

## Step 0 (read-only checks, recorded)

* `testFun_loopObs_of_im_le` (`Gauss/LoopC2.lean:541`) supplies `TestFun d N (loopObs d N z I)`
  from `z.im ≠ 0`, `hwf : I.WF`, `hn : 1 ≤ I.a.length` — no restriction on `Dims`.
* `generator_add_zMotion_gauss` (`Gauss/LoopIto.lean:2580`), `zMotion` (`:392`), `loopDrift_eq`
  (`Gauss/GridDriftLip.lean`), `oneStep_error_le` (`Gauss/GridOneStep.lean`), `condExp_freeze`
  (`Gauss/GridMarkov.lean:40`), `H` (`Gauss/GridPath.lean:65`), `time`, `step` (`:47,51`) — all
  checked in place as they are invoked below.
* `RBM.Gauss.Grid.H_measurable_filt` (`Gauss/GridStopFilt.lean:36`) already supplies the
  matrix-level (not just entrywise) `filt d k`-measurability of `H`; this is an already-merged
  result (T1489, root-imported) and is reused rather than re-derived.
* No hypothesis beyond `(zt E u).im ≠ 0` (at the relevant times), `u_k, u_{k+1} ∈ [0,1)` and
  `|E| < 2` (needed only for (T3)/(T4), to control `Im z_v` uniformly over the window `[u_k,
  u_{k+1}]`, via `zt_im`/`mE_im_pos`) is used; none restricts `Dims`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {d : Dims}

/-! ### §0 : the grid-path recursion `H_{k+1} = H_k + √Δ • X_{k+1}` -/

/-- **The grid path one-step recursion.** Immediate from the definition of `H`: the extra term
in the `Icc 1 (k+1)` sum over the `Icc 1 k` sum is the new draw `ω (k+1)`. -/
theorem H_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Ωg d) :
    H d s t K N (k + 1) ω = H d s t K N k ω + Hflow d N (step s t K N) (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  change H d s t K N (k + 1) ω
      = H d s t K N k ω + (Real.sqrt (step s t K N) : ℂ) • Xmat d N (ω (k + 1))
  unfold H
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

/-! ### §0 : continuity of `gloop`/`zMotion`, generalised away from `Hflow`

`RBM.Gauss.continuous_gloop_Hflow`/`continuous_zMotion_Hflow` (`Gauss/Hierarchy.lean`,
`Gauss/LoopIto.lean`) are stated only for the raw flow `Hflow d N u ω`. Both directions below
are needed: (A) continuity in the *matrix* argument along an arbitrary continuous Hermitian
path (for the integrability of the shifted `zMotion` used in (T4)); (B) continuity in the
*spectral parameter* `z = zt E v` at a fixed matrix (for the interval-integrability of the
`z`-derivative used in (T3)). Both reduce to `RBM.Gauss.continuous_green_comp` resp. a
`z`-analogue of it, exactly as the `_Hflow` versions do. -/

section ContinuityComp

variable {N : ℕ}

/-- A finite sum of functions `ContinuousAt` a point is itself `ContinuousAt` that point. -/
private theorem continuousAt_finset_sum' {ι : Type*} (s : Finset ι) {g : ι → ℂ → ℂ} {z : ℂ}
    (hg : ∀ i ∈ s, ContinuousAt (g i) z) :
    ContinuousAt (fun w => ∑ i ∈ s, g i w) z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousAt_const
  | insert a s ha ih =>
      rw [show (fun w => ∑ i ∈ insert a s, g i w) = fun w => g a w + ∑ i ∈ s, g i w from
        funext fun w => Finset.sum_insert ha]
      exact (hg a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- (A0) The `z`-analogue of `RBM.Gauss.continuous_green_comp`: at a fixed Hermitian `M`,
`w ↦ green M w` is continuous at every `z` with `z.im ≠ 0`. -/
private theorem continuousAt_green_z {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousAt (fun w : ℂ => green M w) z := by
  have hU : IsUnit (M - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hM hz
  have hspec : ((hU.unit : (Matrix (d.Idx N) (d.Idx N) ℂ)ˣ) : Matrix (d.Idx N) (d.Idx N) ℂ)
      = M - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
      (M - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun w : ℂ => M - w • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) z :=
    continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
  have := ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
    (f := fun w : ℂ => M - w • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) h1 h2
  simpa [green, Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

/-- (A1) `w ↦ Gsig M w σ` is continuous at `z`, both charges. -/
private theorem continuousAt_Gsig_z {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    ContinuousAt (fun w : ℂ => Gsig M w σ) z := by
  cases σ with
  | false =>
      have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
      have hcomp := (continuousAt_green_z hM hz').comp
        (Complex.continuous_conj.continuousAt (x := z))
      simpa [Gsig, Function.comp_def] using hcomp
  | true => simpa [Gsig] using continuousAt_green_z hM hz

/-- (A2) The loop product, as a function of `w` alone at a fixed Hermitian `M` and a fixed
finite list of `(charge, label)` pairs, is continuous at `z`. -/
private theorem continuousAt_foldr_z {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × ZMod (d.L N))) :
    ContinuousAt (fun w : ℂ =>
      l.foldr (fun p A => Gsig M w p.1 * Eblk (d.L N) (d.W N) p.2 * A)
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) z := by
  induction l with
  | nil => exact continuousAt_const
  | cons p l ih => exact ((continuousAt_Gsig_z hM hz p.1).mul continuousAt_const).mul ih

private theorem continuousAt_gloopProd_z {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (ZMod (d.L N))) :
    ContinuousAt (fun w : ℂ => gloopProd (d.L N) (d.W N) M w I) z :=
  continuousAt_foldr_z hM hz (I.σ.zip I.a)

/-- (A3) `w ↦ gloop M w I` is continuous at `z`, at a fixed Hermitian `M`. -/
private theorem continuousAt_gloop_z {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (ZMod (d.L N))) :
    ContinuousAt (fun w : ℂ => gloop (d.L N) (d.W N) M w I) z :=
  continuous_matrixTrace.continuousAt.comp (continuousAt_gloopProd_z hM hz I)

/-- (A4) `w ↦ zMotion m M w I` is continuous at `z`, at a fixed Hermitian `M`. -/
private theorem continuousAt_zMotion_z {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (m : Bool → ℂ) (I : LoopIdx (ZMod (d.L N))) :
    ContinuousAt (fun w : ℂ => zMotion (d.L N) (d.W N) m M w I) z := by
  simp only [zMotion]
  refine continuousAt_finset_sum' _ fun k _ => continuousAt_const.mul ?_
  exact continuousAt_const.mul
    (continuousAt_finset_sum' _ fun b _ => continuousAt_gloop_z hM hz _)

/-- (B1) `zMotion` is continuous, as a function of the matrix argument, along any continuous
path into the Hermitian matrices, at a fixed `z, m, I`. -/
private theorem continuous_Gsig_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω => Gsig (f ω) z σ := by
  cases σ with
  | false => exact continuous_green_comp hf hherm (by simpa using hz)
  | true => exact continuous_green_comp hf hherm hz

private theorem continuous_foldr_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × ZMod (d.L N))) :
    Continuous fun ω => l.foldr (fun p A => Gsig (f ω) z p.1 * Eblk (d.L N) (d.W N) p.2 * A)
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih => exact ((continuous_Gsig_comp hf hherm hz p.1).mul continuous_const).mul ih

private theorem continuous_gloopProd_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω => gloopProd (d.L N) (d.W N) (f ω) z I :=
  continuous_foldr_comp hf hherm hz (I.σ.zip I.a)

private theorem continuous_gloop_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω => gloop (d.L N) (d.W N) (f ω) z I :=
  continuous_matrixTrace.comp (continuous_gloopProd_comp hf hherm hz I)

private theorem continuous_zMotion_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (m : Bool → ℂ)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω => zMotion (d.L N) (d.W N) m (f ω) z I := by
  simp only [zMotion]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact continuous_const.mul
    (continuous_finsetSum _ fun b _ => continuous_gloop_comp hf hherm hz _)

end ContinuityComp

/-! ### §1 : the complex-valued freezing lemma, and (T1) -/

section FreezeC

variable {N : ℕ}

/-- **The complex-valued freezing lemma.** `RBM.Gauss.Grid.condExp_freeze` is stated only for
real-valued `F` (`GridMarkov.lean`); none of its ingredients are specific to `ℝ`, but rather than
duplicate its ~70-line proof for a generic Banach target, this derives the complex-valued case
from the real one via the real/imaginary decomposition and
`ContinuousLinearMap.comp_condExp_comm` (conditional expectation commutes with continuous
`ℝ`-linear maps, in particular `RCLike.reCLM`/`RCLike.imCLM`), reconstructing the complex value
from its two real parts via `RBM.Gauss.integral_re`/`integral_im`-style factorisation
(`MeasureTheory.integral_re`/`integral_im`, applied pointwise using `hFInt`). -/
theorem condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : Ωg d → β} (hY : Measurable[filt d k] Y)
    {F : β → Ω d → ℂ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (P d))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pg d)) :
    (Pg d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pg d] fun ω => ∫ x, F (Y ω) x ∂ (P d) := by
  classical
  set f : Ωg d → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Ω d → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Ω d → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Ω d => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Ω d => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (Pg d) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (Pg d) := hInt.im
  have hfreezeRe := condExp_freeze k hY hFre hIntRe
  have hfreezeIm := condExp_freeze k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hReComb : (fun ω => RCLike.re ((Pg d)[f | filt d k] ω))
      =ᵐ[Pg d] fun ω => ∫ x, Fre (Y ω) x ∂ (P d) := by
    have hRe' : (fun ω => RCLike.re ((Pg d)[f | filt d k] ω))
        =ᵐ[Pg d] (Pg d)[fun ω => Fre (Y ω) (ω (k + 1)) | filt d k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((Pg d)[f | filt d k] ω))
      =ᵐ[Pg d] fun ω => ∫ x, Fim (Y ω) x ∂ (P d) := by
    have hIm' : (fun ω => RCLike.im ((Pg d)[f | filt d k] ω))
        =ᵐ[Pg d] (Pg d)[fun ω => Fim (Y ω) (ω (k + 1)) | filt d k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂ (P d) = RCLike.re (∫ x, F p x ∂ (P d)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂ (P d) = RCLike.im (∫ x, F p x ∂ (P d)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((Pg d)[f | filt d k] ω) = RCLike.re (∫ x, F (Y ω) x ∂ (P d))
    rw [hωre, hreEq]
  · change RCLike.im ((Pg d)[f | filt d k] ω) = RCLike.im (∫ x, F (Y ω) x ∂ (P d))
    rw [hωim, himEq]

end FreezeC

/-! ### §2 : integrability helpers, and (T1) -/

section T1

variable {N : ℕ}

/-- A bounded measurable function into a finite-dimensional (in particular second-countable)
normed space is integrable against a finite measure. -/
private theorem integrable_of_measurable_bound {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {f : Ω' → E} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)).integrable le_top

/-- **`Φ` remains integrable after a shift by any fixed matrix and a Gaussian rescaling.** -/
private theorem integrable_Phi_shift {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : TestFun d N Φ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (w : ℝ) :
    Integrable (fun ω : Ω d => Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω)) (P d) := by
  obtain ⟨C₀, hC₀⟩ := h.bdd₀
  have hsqrtConst : Continuous fun _ : Ω d => (Real.sqrt w : ℂ) := continuous_const
  have hcont : Continuous fun ω : Ω d => Φ (M + (Real.sqrt w : ℂ) • Xmat d N ω) :=
    h.contDiff.continuous.comp (continuous_const.add (hsqrtConst.smul (continuous_Xmat d N)))
  exact integrable_of_continuous_of_bound hcont fun ω => hC₀ _

/-- **(T1)**: the freezing lemma applied to the one-step grid recursion `H_{k+1} = H_k +
√Δ • X_{k+1}` (`H_succ`), for the loop observable `Φ_{u_{k+1}} := loopObs d N (zt E u_{k+1}) I`.
-/
theorem condExp_loop_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (hz : (zt E (time s t K N (k + 1))).im ≠ 0) :
    (Pg d)[fun ω : Ωg d => loopObs d N (zt E (time s t K N (k + 1))) I
          (H d s t K N (k + 1) ω) | filt d k]
      =ᵐ[Pg d] fun ω => ∫ x, loopObs d N (zt E (time s t K N (k + 1))) I
        (H d s t K N k ω + Hflow d N (step s t K N) x) ∂ (P d) := by
  have hTF : TestFun d N (loopObs d N (zt E (time s t K N (k + 1))) I) :=
    testFun_loopObs_of_im_le hz (abs_pos.mpr hz) le_rfl hwf hn
  obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
  have hYmeas : Measurable[filt d k] (fun ω => H d s t K N k ω) := H_measurable_filt d s t K N k
  have hHk1meas : Measurable (fun ω : Ωg d => H d s t K N (k + 1) ω) :=
    (H_measurable_filt d s t K N (k + 1)).mono ((filt d).le (k + 1)) le_rfl
  have hFmeas : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      loopObs d N (zt E (time s t K N (k + 1))) I (p.1 + Hflow d N (step s t K N) p.2)) :=
    (hTF.contDiff.continuous.comp
      (continuous_fst.add ((continuous_Hflow d N (step s t K N)).comp continuous_snd))).measurable
  have hFInt : ∀ p : Matrix (d.Idx N) (d.Idx N) ℂ,
      Integrable (fun x => loopObs d N (zt E (time s t K N (k + 1))) I
        (p + Hflow d N (step s t K N) x)) (P d) :=
    fun p => integrable_Phi_shift hTF p (step s t K N)
  have hIntTarget : Integrable
      (fun ω : Ωg d => loopObs d N (zt E (time s t K N (k + 1))) I
        (H d s t K N (k + 1) ω)) (Pg d) :=
    integrable_of_measurable_bound (hTF.contDiff.continuous.measurable.comp hHk1meas)
      fun ω => hC₀ _
  have hEq : (fun ω : Ωg d => loopObs d N (zt E (time s t K N (k + 1))) I
        (H d s t K N (k + 1) ω))
      = fun ω => loopObs d N (zt E (time s t K N (k + 1))) I
          (H d s t K N k ω + Hflow d N (step s t K N) (ω (k + 1))) := by
    funext ω; rw [H_succ]
  rw [hEq] at hIntTarget ⊢
  exact condExp_freezeC k hYmeas hFmeas hFInt hIntTarget

end T1

/-! ### §3 : the `zMotion` Lipschitz bound (both `M` and `z` may move), and (T2) -/

section ZMotionLip

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The general `zMotion` Lipschitz bound**, allowing both the matrix and the spectral
parameter to move (mirrors `RBM.norm_gloop_sub_le`, which already supports both moving).
Specialised below to `M`-only movement (for (T2)) and `z`-only movement (for (T3)). -/
theorem norm_zMotion_sub_le_mz (m : Bool → ℂ)
    {M₁ M₂ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z₁ z₂ : ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian)
    {K : ℝ} (hK : 1 ≤ K) (hG₁ : ‖green M₁ z₁‖ ≤ K) (hG₂ : ‖green M₂ z₂‖ ≤ K)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hsub : ‖green M₁ z₁ - green M₂ z₂‖ ≤ Δ)
    (I : LoopIdx (ZMod L)) (hwf : I.WF) :
    ‖zMotion L W m M₁ z₁ I - zMotion L W m M₂ z₂ I‖
      ≤ (I.length : ℝ) * (max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
          ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ)) := by
  classical
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hmAbs0 : (0 : ℝ) ≤ max ‖m true‖ ‖m false‖ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hcst : (0:ℝ) ≤ (L:ℝ)*(W:ℝ)*((I.length:ℝ)+1)*K^(I.length+1)*Δ := by positivity
  change ‖(∑ k ∈ Finset.range I.length,
        (-(m (I.σ.getD k true))) * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₁ z₁ (I.cutGlue (k+1) b)))
      - (∑ k ∈ Finset.range I.length,
        (-(m (I.σ.getD k true))) * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₂ z₂ (I.cutGlue (k+1) b)))‖
      ≤ (I.length : ℝ) * (max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
          ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ))
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range I.length,
      ‖(-(m (I.σ.getD k true))) * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₁ z₁ (I.cutGlue (k+1) b))
        - (-(m (I.σ.getD k true))) * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₂ z₂ (I.cutGlue (k+1) b))‖
      ≤ max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
          ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hsubb : ∀ b : ZMod L,
        ‖gloop L W M₁ z₁ (I.cutGlue (k+1) b) - gloop L W M₂ z₂ (I.cutGlue (k+1) b)‖
          ≤ (L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ := by
      intro b
      have hwfcg : (I.cutGlue (k+1) b).WF := hwf.cutGlue b (by omega) (by omega)
      have hlen1 : (I.cutGlue (k+1) b).σ.length = I.length + 1 := by
        have h1 : (I.cutGlue (k+1) b).σ.length = (I.cutGlue (k+1) b).length := hwfcg
        rw [h1, LoopIdx.length_cutGlue I b (by omega)]
      have hbound := norm_gloop_sub_le hK hΔ hM₁ hM₂ hG₁ hG₂ hsub (I.cutGlue (k+1) b) hwfcg
      rw [hlen1] at hbound
      push_cast at hbound ⊢
      linarith [hbound]
    have hsumb : ‖(∑ b : ZMod L, gloop L W M₁ z₁ (I.cutGlue (k+1) b))
          - ∑ b : ZMod L, gloop L W M₂ z₂ (I.cutGlue (k+1) b)‖
        ≤ (L : ℝ) * ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ) := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b : ZMod L, ‖gloop L W M₁ z₁ (I.cutGlue (k+1) b)
              - gloop L W M₂ z₂ (I.cutGlue (k+1) b)‖
          ≤ ∑ _b : ZMod L, (L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ :=
            Finset.sum_le_sum fun b _ => hsubb b
        _ = (L : ℝ) * ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hmb : ‖(-(m (I.σ.getD k true))) * (W : ℂ)‖ ≤ max ‖m true‖ ‖m false‖ * (W : ℝ) := by
      rw [norm_mul, norm_neg, Complex.norm_natCast]
      gcongr
      cases I.σ.getD k true <;> simp
    calc ‖(-(m (I.σ.getD k true)))
              * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₁ z₁ (I.cutGlue (k+1) b))
          - (-(m (I.σ.getD k true)))
              * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₂ z₂ (I.cutGlue (k+1) b))‖
        = ‖(-(m (I.σ.getD k true))) * (W : ℂ)‖ *
            ‖(∑ b : ZMod L, gloop L W M₁ z₁ (I.cutGlue (k+1) b))
              - ∑ b : ZMod L, gloop L W M₂ z₂ (I.cutGlue (k+1) b)‖ := by
          rw [← mul_assoc, ← mul_assoc, ← mul_sub, norm_mul]
      _ ≤ (max ‖m true‖ ‖m false‖ * (W : ℝ)) *
            ((L : ℝ) * ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ)) :=
          mul_le_mul hmb hsumb (norm_nonneg _) (by positivity)
      _ = max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
            ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ) := by ring
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.range I.length,
        ‖(-(m (I.σ.getD k true)))
              * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₁ z₁ (I.cutGlue (k+1) b))
          - (-(m (I.σ.getD k true)))
              * ((W : ℂ) * ∑ b : ZMod L, gloop L W M₂ z₂ (I.cutGlue (k+1) b))‖
      ≤ ∑ _k ∈ Finset.range I.length, max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
          ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ) :=
        Finset.sum_le_sum hterm
    _ = (I.length : ℝ) * (max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
          ((L : ℝ) * (W : ℝ) * ((I.length : ℝ) + 1) * K ^ (I.length + 1) * Δ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ZMotionLip

/-! ### §4 : the two specialisations of `norm_zMotion_sub_le_mz`, and their explicit constants -/

section ZMotionLipSpecial

variable {N : ℕ}

/-- **The explicit `M`-Lipschitz constant for `zMotion`** at fixed `z`, with `η = |z.im|`. -/
noncomputable def zMotionLip (L W n : ℕ) (η : ℝ) (m : Bool → ℂ) : ℝ :=
  (n : ℝ) * (max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
      ((L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (1 + η⁻¹) ^ (n + 1))) * η⁻¹ ^ 2

/-- **The `M`-Lipschitz bound for `zMotion`**, at fixed `E, u`. -/
theorem norm_zMotion_sub_le_ofM {E u : ℝ} (hz : (zt E u).im ≠ 0)
    {M₁ M₂ : Matrix (d.Idx N) (d.Idx N) ℂ} (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    ‖zMotion (d.L N) (d.W N) (mSigma E) M₁ (zt E u) I
        - zMotion (d.L N) (d.W N) (mSigma E) M₂ (zt E u) I‖
      ≤ zMotionLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E) * ‖M₁ - M₂‖ := by
  have hzpos : (0 : ℝ) < |(zt E u).im| := abs_pos.mpr hz
  set K : ℝ := 1 + |(zt E u).im|⁻¹ with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith [inv_nonneg.mpr hzpos.le]
  have hG₁ : ‖green M₁ (zt E u)‖ ≤ K :=
    (norm_green_le hM₁ hzpos le_rfl).trans (by rw [hKdef]; linarith)
  have hG₂ : ‖green M₂ (zt E u)‖ ≤ K :=
    (norm_green_le hM₂ hzpos le_rfl).trans (by rw [hKdef]; linarith)
  have hΔgreen : ‖green M₁ (zt E u) - green M₂ (zt E u)‖ ≤ |(zt E u).im|⁻¹ ^ 2 * ‖M₁ - M₂‖ :=
    norm_green_sub_le_of_herm hM₁ hM₂ hz
  have hΔ0 : (0 : ℝ) ≤ |(zt E u).im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by positivity
  have hlenEq : I.length = I.σ.length := hwf.symm
  have hb := norm_zMotion_sub_le_mz (mSigma E) hM₁ hM₂ hK1 hG₁ hG₂ hΔ0 hΔgreen I hwf
  rw [hlenEq] at hb
  refine hb.trans (le_of_eq ?_)
  unfold zMotionLip
  rw [hKdef]
  ring

/-- **The explicit `z`-Lipschitz constant for `zMotion`** at fixed `M`, with a uniform lower
bound `η` on `|Im z|` for both spectral parameters. -/
noncomputable def zMotionZLip (L W n : ℕ) (η : ℝ) (m : Bool → ℂ) : ℝ :=
  (n : ℝ) * (max ‖m true‖ ‖m false‖ * (W : ℝ) * (L : ℝ) *
      ((L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (1 + η⁻¹) ^ (n + 1))) * (1 + η⁻¹) ^ 2

/-- **The `z`-Lipschitz bound for `zMotion`**, at fixed `M`, `m`, `I`, uniformly over any two
spectral parameters `z₁, z₂` with `|Im z_i| ≥ η > 0`. -/
theorem norm_zMotion_sub_le_ofZ {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ |z₁.im|) (hη₂ : η ≤ |z₂.im|) (m : Bool → ℂ) {I : LoopIdx (ZMod (d.L N))}
    (hwf : I.WF) :
    ‖zMotion (d.L N) (d.W N) m M z₁ I - zMotion (d.L N) (d.W N) m M z₂ I‖
      ≤ zMotionZLip (d.L N) (d.W N) I.σ.length η m * ‖z₁ - z₂‖ := by
  set K : ℝ := 1 + η⁻¹ with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith [inv_nonneg.mpr hη.le]
  have hG₁ : ‖green M z₁‖ ≤ K :=
    (norm_green_le hM hη hη₁).trans (by rw [hKdef]; linarith)
  have hG₂ : ‖green M z₂‖ ≤ K :=
    (norm_green_le hM hη hη₂).trans (by rw [hKdef]; linarith)
  have hΔgreen : ‖green M z₁ - green M z₂‖ ≤ K ^ 2 * ‖z₁ - z₂‖ := by
    have hbase := norm_green_sub_le hM hM hz₁ hz₂
    rw [sub_self, norm_zero, zero_add] at hbase
    refine hbase.trans ?_
    have h1 : ‖green M z₁‖ * ‖z₁ - z₂‖ * ‖green M z₂‖ ≤ K * ‖z₁ - z₂‖ * K :=
      mul_le_mul (mul_le_mul_of_nonneg_right hG₁ (norm_nonneg _)) hG₂ (norm_nonneg _)
        (by positivity)
    calc ‖green M z₁‖ * ‖z₁ - z₂‖ * ‖green M z₂‖ ≤ K * ‖z₁ - z₂‖ * K := h1
      _ = K ^ 2 * ‖z₁ - z₂‖ := by ring
  have hΔ0 : (0 : ℝ) ≤ K ^ 2 * ‖z₁ - z₂‖ := by positivity
  have hlenEq : I.length = I.σ.length := hwf.symm
  have hb := norm_zMotion_sub_le_mz m hM hM hK1 hG₁ hG₂ hΔ0 hΔgreen I hwf
  rw [hlenEq] at hb
  refine hb.trans (le_of_eq ?_)
  unfold zMotionZLip
  rw [hKdef]
  ring

end ZMotionLipSpecial

/-! ### §5 : the `genPt`/`loopDrift`/`zMotion` identity, and (T2) -/

section T2

variable {N : ℕ}

/-- **The explicit Lipschitz constant for `genPt (loopObs d N (zt E u) I)`.** -/
noncomputable def genPtLip (L W n : ℕ) (η : ℝ) (m : Bool → ℂ) : ℝ :=
  driftLip L W n η m + zMotionLip L W n η m

/-- **The bridge identity**: `genPt (loopObs d N (zt E u) I) M` is the deterministic generator
value of `generator_add_zMotion_gauss`, minus the `z`-motion term. `genD` is `genPt` up to the
notational difference `1/2` vs `2⁻¹`, and `genD_eq_sum_pairs` rewrites the coordinate sum as
the paper's index-pair sum, which is exactly the left summand of `generator_add_zMotion_gauss`. -/
theorem genPt_eq_loopDrift_sub_zMotion (E u : ℝ) (hz : (zt E u).im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    genPt d N (loopObs d N (zt E u) I) M
      = loopDrift E u I M - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I := by
  have hgen := generator_add_zMotion_gauss hz M hM I hwf hn
  have h12 : (1 / 2 : ℝ) = (2⁻¹ : ℝ) := by norm_num
  rw [h12] at hgen
  have hgd : genPt d N (loopObs d N (zt E u) I) M = genD d N (loopObs d N (zt E u) I) M := by
    unfold genPt genD
    rw [h12]
  rw [hgd, genD_eq_sum_pairs, loopDrift_eq, eq_sub_iff_add_eq]
  exact hgen

/-- **(T2)**: `RBM.Gauss.Grid.loop_step_space_err`. `RBM.Gauss.Grid.oneStep_error_le`
specialised to `Φ = loopObs d N (zt E u) I`, with the Lipschitz constant of `genPt Φ` built from
`driftLip`/`norm_loopDrift_sub_le` (T1487) and `zMotionLip`/`norm_zMotion_sub_le_ofM` (§4),
combined through the identity above. -/
theorem loop_step_space_err (E u : ℝ) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF)
    (hn : 1 ≤ I.a.length) (hz : (zt E u).im ≠ 0) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ‖(∫ ω, loopObs d N (zt E u) I (M + (Real.sqrt Δ : ℂ) • Xmat d N ω) ∂ (P d))
        - loopObs d N (zt E u) I M
        - (Δ : ℂ) • genPt d N (loopObs d N (zt E u) I) M‖
      ≤ (2 / 3) * genPtLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E)
          * Δ ^ (3 / 2 : ℝ) * (∫ ω, ‖Xmat d N ω‖ ∂ (P d)) := by
  refine oneStep_error_le (testFun_loopObs_of_im_le hz (abs_pos.mpr hz) le_rfl hwf hn) hM
    (Λ := genPtLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E))
    (fun A A' hA hA' => ?_) hΔ
  rw [genPt_eq_loopDrift_sub_zMotion E u hz hA hwf hn,
    genPt_eq_loopDrift_sub_zMotion E u hz hA' hwf hn]
  have hrearr : (loopDrift E u I A - zMotion (d.L N) (d.W N) (mSigma E) A (zt E u) I)
      - (loopDrift E u I A' - zMotion (d.L N) (d.W N) (mSigma E) A' (zt E u) I)
      = (loopDrift E u I A - loopDrift E u I A')
        - (zMotion (d.L N) (d.W N) (mSigma E) A (zt E u) I
          - zMotion (d.L N) (d.W N) (mSigma E) A' (zt E u) I) := by ring
  rw [hrearr]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_loopDrift_sub_le hz hA hA' hwf hn
  have h2 := norm_zMotion_sub_le_ofM hz hA hA' hwf
  calc ‖loopDrift E u I A - loopDrift E u I A'‖
        + ‖zMotion (d.L N) (d.W N) (mSigma E) A (zt E u) I
          - zMotion (d.L N) (d.W N) (mSigma E) A' (zt E u) I‖
      ≤ driftLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E) * ‖A - A'‖
        + zMotionLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E) * ‖A - A'‖ :=
      add_le_add h1 h2
    _ = genPtLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E) * ‖A - A'‖ := by
        unfold genPtLip; ring

end T2

/-! ### §6 : (T3), the quadratic-remainder bound for the moving spectral parameter -/

section T3

variable {N : ℕ}

private theorem continuous_zt (E : ℝ) : Continuous (fun t : ℝ => zt E t) := by
  unfold zt; fun_prop

/-- **(T3)**: `RBM.Gauss.Grid.loop_step_time_err`. `z_u` is affine in `u` (`zt`), so the exact
FTC identity `g(u') - g(u) = ∫_u^{u'} zMotion(M, z_v, I) dv` (`hasDerivAt_gloop_zt`) turns the
quadratic remainder into the interval integral of `zMotion(z_v) - zMotion(z_u)`, bounded
pointwise by the `z`-Lipschitz constant `zMotionZLip` (§4) times `‖z_v - z_u‖ = ‖mE E‖ (v - u)`.
-/
theorem loop_step_time_err (E : ℝ) (hEb : |E| < 2) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) {u u' : ℝ} (_hu0 : 0 ≤ u)
    (huu' : u < u') (hu'1 : u' < 1) :
    ‖loopObs d N (zt E u') I M - loopObs d N (zt E u) I M
        - (u' - u) • zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I‖
      ≤ zMotionZLip (d.L N) (d.W N) I.σ.length ((1 - u') * (mE E).im) (mSigma E)
          * ‖mE E‖ * (u' - u) ^ 2 / 2 := by
  have hmEim : 0 < (mE E).im := mE_im_pos hEb
  set η : ℝ := (1 - u') * (mE E).im with hηdef
  have hη : 0 < η := mul_pos (by linarith) hmEim
  have hzim : ∀ v ∈ Set.Icc u u', (zt E v).im ≠ 0 := by
    intro v hv
    exact zt_im_ne_zero_of_lt_one hEb (lt_of_le_of_lt hv.2 hu'1)
  have hηbound : ∀ v ∈ Set.Icc u u', η ≤ |(zt E v).im| := by
    intro v hv
    have hpos : (0:ℝ) < 1 - v := by linarith [hv.2]
    rw [zt_im, abs_of_pos (mul_pos hpos hmEim)]
    exact mul_le_mul_of_nonneg_right (by linarith [hv.2] : (1 - u') ≤ (1 - v)) hmEim.le
  have hmemu : u ∈ Set.Icc u u' := ⟨le_refl u, huu'.le⟩
  have hcontOn : ContinuousOn
      (fun v : ℝ => zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I) (Set.uIcc u u') := by
    rw [Set.uIcc_of_le huu'.le]
    intro v hv
    exact ((continuousAt_zMotion_z hM (hzim v hv) (mSigma E) I).comp
      (continuous_zt E).continuousAt).continuousWithinAt
  have hgint : IntervalIntegrable
      (fun v : ℝ => zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I) MeasureTheory.volume u u' :=
    hcontOn.intervalIntegrable
  have hderiv : ∀ v ∈ Set.uIcc u u',
      HasDerivAt (fun s : ℝ => gloop (d.L N) (d.W N) M (zt E s) I)
        (zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I) v := by
    rw [Set.uIcc_of_le huu'.le]
    intro v hv
    exact hasDerivAt_gloop_zt hM (hzim v hv) I hwf
  have hFTC : (∫ v in u..u', zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I)
      = gloop (d.L N) (d.W N) M (zt E u') I - gloop (d.L N) (d.W N) M (zt E u) I :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hgint
  have hconstInt : (∫ _v in u..u', zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I)
      = (u' - u) • zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I :=
    intervalIntegral.integral_const _
  have hgconstInt : IntervalIntegrable
      (fun _v : ℝ => zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I) MeasureTheory.volume u u' :=
    intervalIntegrable_const
  have hdiff : (gloop (d.L N) (d.W N) M (zt E u') I - gloop (d.L N) (d.W N) M (zt E u) I)
      - (u' - u) • zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I
      = ∫ v in u..u', (zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I
          - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I) := by
    rw [intervalIntegral.integral_sub hgint hgconstInt, hFTC, hconstInt]
  rw [loopObs_of_isHermitian hM, loopObs_of_isHermitian hM, hdiff]
  have hzmzt : ∀ v : ℝ, zt E v - zt E u = ((u - v : ℝ) : ℂ) * mE E := by
    intro v; unfold zt; push_cast; ring
  have hbound : ∀ v ∈ Set.uIcc u u',
      ‖zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I
          - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I‖
        ≤ zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ * (v - u) := by
    rw [Set.uIcc_of_le huu'.le]
    intro v hv
    have hb := norm_zMotion_sub_le_ofZ hM (hzim v hv) (hzim u hmemu) hη
      (hηbound v hv) (hηbound u hmemu) (mSigma E) hwf
    have heq : ‖zt E v - zt E u‖ = ‖mE E‖ * (v - u) := by
      rw [hzmzt v, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [hv.1] : u - v ≤ 0)]
      ring
    calc ‖zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I
            - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I‖
        ≤ zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖zt E v - zt E u‖ := hb
      _ = zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ * (v - u) := by
          rw [heq]; ring
  have hnormNonneg : (0:ℝ) ≤ zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ := by
    unfold zMotionZLip; positivity
  have hcontOnNorm : ContinuousOn
      (fun v : ℝ => ‖zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I
        - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I‖) (Set.uIcc u u') :=
    (hcontOn.sub continuousOn_const).norm
  have hcontOnRHS : ContinuousOn
      (fun v : ℝ => zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ * (v - u))
      (Set.uIcc u u') :=
    ((continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  calc ‖∫ v in u..u', (zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I
          - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I)‖
      ≤ ∫ v in u..u', ‖zMotion (d.L N) (d.W N) (mSigma E) M (zt E v) I
          - zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I‖ :=
        intervalIntegral.norm_integral_le_integral_norm huu'.le
    _ ≤ ∫ v in u..u', zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ * (v - u) := by
        refine intervalIntegral.integral_mono_on huu'.le
          (hcontOnNorm.intervalIntegrable) (hcontOnRHS.intervalIntegrable) ?_
        intro v hv
        exact hbound v (Set.uIcc_of_le huu'.le ▸ hv)
    _ = zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ * (u' - u) ^ 2 / 2 := by
        have hconst : (fun v : ℝ =>
            zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖ * (v - u))
            = fun v : ℝ =>
              (zMotionZLip (d.L N) (d.W N) I.σ.length η (mSigma E) * ‖mE E‖) * (v - u) := by
          funext v; ring
        rw [hconst, intervalIntegral.integral_const_mul]
        have hshift :=
          intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) u (a := u) (b := u')
        simp only [sub_self] at hshift
        rw [hshift, integral_id]
        ring

end T3

/-! ### §7 : (T4), assembling (T1)-(T3) -/

section T4

variable {N : ℕ}

private theorem time_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    time s t K N (k + 1) = time s t K N k + step s t K N := by
  unfold time; push_cast; ring

/-- A bound `‖f x‖ ≤ C` valid for **every** `x` bounds the integral, since `P d` is a
probability measure. -/
private theorem norm_integral_le_of_forall_norm_le {f : Ω d → ℂ} (hf : Integrable f (P d))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : ‖∫ x, f x ∂ (P d)‖ ≤ C := by
  have huniv : (P d).real Set.univ = 1 := by simp
  calc ‖∫ x, f x ∂ (P d)‖ ≤ ∫ x, ‖f x‖ ∂ (P d) := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, C ∂ (P d) := integral_mono hf.norm (integrable_const C) hC
    _ = C := by rw [integral_const, huniv, one_smul]

set_option maxHeartbeats 1000000 in
-- the `set`-introduced local abbreviations (`Δ, uk, uk1, Φk1, Φk, A, B, Z, z0`) and the many
-- integrability/Lipschitz side lemmas they interact with push the default elaboration budget
-- past its limit; this mirrors existing practice elsewhere in the repo (e.g.
-- `RBM1D/Hierarchy/DriftBound.lean`).
/-- **The deterministic core of (T4)**, at a fixed Hermitian `M`: no probability enters,
`Pg d` has not appeared yet. The decomposition compares `Φ_{u_{k+1}}` and `Φ_{u_k}` *inside*
the integral over the fresh increment (via (T3), pointwise in the increment), so (T2) is only
ever invoked at the single time `u_k`; see the module docstring. -/
private theorem norm_loop_step_drift_le (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    (hEb : |E| < 2) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (hst : s N < t N) (hk : k < K N) (hu0 : 0 ≤ time s t K N k)
    (hu1 : time s t K N (k + 1) < 1) (hzk : (zt E (time s t K N k)).im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    ‖(∫ x, loopObs d N (zt E (time s t K N (k + 1))) I
          (M + (Real.sqrt (step s t K N) : ℂ) • Xmat d N x) ∂ (P d))
        - loopObs d N (zt E (time s t K N k)) I M
        - (step s t K N : ℂ) • loopDrift E (time s t K N k) I M‖
      ≤ zMotionZLip (d.L N) (d.W N) I.σ.length
            ((1 - time s t K N (k + 1)) * (mE E).im) (mSigma E) * ‖mE E‖
            * (step s t K N) ^ 2 / 2
        + (zMotionLip (d.L N) (d.W N) I.σ.length |(zt E (time s t K N k)).im| (mSigma E)
            + (2 / 3) * genPtLip (d.L N) (d.W N) I.σ.length |(zt E (time s t K N k)).im|
                (mSigma E))
          * (step s t K N) ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
  set Δ : ℝ := step s t K N with hΔdef
  set uk : ℝ := time s t K N k with hukdef
  set uk1 : ℝ := time s t K N (k + 1) with huk1def
  have hKpos : 0 < K N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hΔpos : 0 < Δ := by
    rw [hΔdef]; unfold step; exact div_pos (by linarith) (by exact_mod_cast hKpos)
  have huk1eq : uk1 = uk + Δ := time_succ s t K N k
  have hzk1 : (zt E uk1).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  set Φk1 : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := loopObs d N (zt E uk1) I with hΦk1def
  set Φk : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := loopObs d N (zt E uk) I with hΦkdef
  have hTFk1 : TestFun d N Φk1 := testFun_loopObs_of_im_le hzk1 (abs_pos.mpr hzk1) le_rfl hwf hn
  have hTFk : TestFun d N Φk := testFun_loopObs_of_im_le hzk (abs_pos.mpr hzk) le_rfl hwf hn
  -- Hermitian-ness of the shifted matrix, for every `x`.
  have hHermx : ∀ x : Ω d, (M + (Real.sqrt Δ : ℂ) • Xmat d N x).IsHermitian :=
    fun x => hM.add (Hflow_isHermitian d N Δ x)
  -- Integrability facts.
  have hIntK1 : Integrable (fun x => Φk1 (M + (Real.sqrt Δ : ℂ) • Xmat d N x)) (P d) :=
    integrable_Phi_shift hTFk1 M Δ
  have hIntK : Integrable (fun x => Φk (M + (Real.sqrt Δ : ℂ) • Xmat d N x)) (P d) :=
    integrable_Phi_shift hTFk M Δ
  have hcontZshift : Continuous fun x : Ω d => M + (Real.sqrt Δ : ℂ) • Xmat d N x := by
    have hsqrtConst : Continuous fun _ : Ω d => (Real.sqrt Δ : ℂ) := continuous_const
    exact continuous_const.add (hsqrtConst.smul (continuous_Xmat d N))
  obtain ⟨η', hη', hzη'⟩ : ∃ η' : ℝ, 0 < η' ∧ η' ≤ |(zt E uk).im| :=
    ⟨|(zt E uk).im|, abs_pos.mpr hzk, le_rfl⟩
  have hIntZM : Integrable
      (fun x => zMotion (d.L N) (d.W N) (mSigma E) (M + (Real.sqrt Δ : ℂ) • Xmat d N x)
        (zt E uk) I) (P d) :=
    integrable_of_continuous_of_bound
      (continuous_zMotion_comp hcontZshift hHermx hzk (mSigma E) I)
      (fun x => norm_zMotion_le (hHermx x) hη' hzη' (mSigma E) I hwf)
  have hIntBracketInner : Integrable
      (fun x => (Φk1 (M + (Real.sqrt Δ : ℂ) • Xmat d N x)
          - Φk (M + (Real.sqrt Δ : ℂ) • Xmat d N x))
        - Δ • zMotion (d.L N) (d.W N) (mSigma E)
            (M + (Real.sqrt Δ : ℂ) • Xmat d N x) (zt E uk) I) (P d) :=
    (hIntK1.sub hIntK).sub (hIntZM.smul Δ)
  -- (T2) at `u_k`.
  have hII := loop_step_space_err E uk hwf hn hzk hM hΔpos.le
  -- The bridge identity, rearranged: `loopDrift(u_k)(M) = genPt(Φ_k)(M) + zMotion(M, z_k, I)`.
  have hld : loopDrift E uk I M
      = genPt d N Φk M + zMotion (d.L N) (d.W N) (mSigma E) M (zt E uk) I := by
    have h := genPt_eq_loopDrift_sub_zMotion E uk hzk hM hwf hn
    rw [h]; ring
  -- The pointwise (T3) bound, at the shifted matrix.
  have hT3 : ∀ x : Ω d,
      ‖Φk1 (M + (Real.sqrt Δ : ℂ) • Xmat d N x) - Φk (M + (Real.sqrt Δ : ℂ) • Xmat d N x)
          - Δ • zMotion (d.L N) (d.W N) (mSigma E)
              (M + (Real.sqrt Δ : ℂ) • Xmat d N x) (zt E uk) I‖
        ≤ zMotionZLip (d.L N) (d.W N) I.σ.length ((1 - uk1) * (mE E).im) (mSigma E)
            * ‖mE E‖ * Δ ^ 2 / 2 := by
    intro x
    have hsub : uk1 - uk = Δ := by rw [huk1eq]; ring
    have hlt : uk < uk1 := by rw [huk1eq]; linarith
    have := loop_step_time_err (u := uk) (u' := uk1) E hEb hwf (hHermx x) hu0 hlt hu1
    rwa [hsub] at this
  -- The `M`-Lipschitz bound for `zMotion`, at the shifted matrix.
  have hzMLip : ∀ x : Ω d,
      ‖zMotion (d.L N) (d.W N) (mSigma E) (M + (Real.sqrt Δ : ℂ) • Xmat d N x) (zt E uk) I
          - zMotion (d.L N) (d.W N) (mSigma E) M (zt E uk) I‖
        ≤ zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
            * (Real.sqrt Δ * ‖Xmat d N x‖) := by
    intro x
    have hb := norm_zMotion_sub_le_ofM hzk (hHermx x) hM hwf
    have heq : M + (Real.sqrt Δ : ℂ) • Xmat d N x - M = (Real.sqrt Δ : ℂ) • Xmat d N x := by abel
    rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg Δ)] at hb
    exact hb
  -- The real/complex bridge: `r • z = (r : ℂ) * z`.
  have hΔsmul : ∀ z : ℂ, Δ • z = (Δ : ℂ) * z := fun _ => Complex.real_smul
  -- The pieces of the decomposition, named.
  set A : Ω d → ℂ := fun x => Φk1 (M + (Real.sqrt Δ : ℂ) • Xmat d N x) with hAdef
  set B : Ω d → ℂ := fun x => Φk (M + (Real.sqrt Δ : ℂ) • Xmat d N x) with hBdef
  set Z : Ω d → ℂ := fun x =>
    zMotion (d.L N) (d.W N) (mSigma E) (M + (Real.sqrt Δ : ℂ) • Xmat d N x) (zt E uk) I with hZdef
  set z0 : ℂ := zMotion (d.L N) (d.W N) (mSigma E) M (zt E uk) I with hz0def
  have hR1int : Integrable (fun x => (A x - B x) - (Δ : ℂ) * Z x) (P d) := by
    have h := hIntBracketInner
    simp only [hΔsmul] at h
    exact h
  have hR1bound : ‖∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d)‖
      ≤ zMotionZLip (d.L N) (d.W N) I.σ.length ((1 - uk1) * (mE E).im) (mSigma E)
          * ‖mE E‖ * Δ ^ 2 / 2 := by
    refine norm_integral_le_of_forall_norm_le hR1int fun x => ?_
    have h := hT3 x
    rwa [hΔsmul] at h
  have hz0const : (∫ _x : Ω d, z0 ∂ (P d)) = z0 := integral_const_P d z0
  have hbracketeq : (∫ x, (Z x - z0) ∂ (P d)) = (∫ x, Z x ∂ (P d)) - z0 := by
    rw [integral_sub hIntZM (integrable_const z0), hz0const]
  have hbracketbound : ‖(∫ x, Z x ∂ (P d)) - z0‖
      ≤ zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E) * Real.sqrt Δ
          * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
    rw [← hbracketeq]
    calc ‖∫ x, (Z x - z0) ∂ (P d)‖
        ≤ ∫ x, ‖Z x - z0‖ ∂ (P d) := norm_integral_le_integral_norm _
      _ ≤ ∫ x, zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
            * (Real.sqrt Δ * ‖Xmat d N x‖) ∂ (P d) :=
          integral_mono (hIntZM.sub (integrable_const z0)).norm
            (((integrable_norm_Xmat d N).const_mul (Real.sqrt Δ)).const_mul _) hzMLip
      _ = zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E) * Real.sqrt Δ
            * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
          have heq2 : (fun x => zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
                * (Real.sqrt Δ * ‖Xmat d N x‖))
              = fun x => (zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
                * Real.sqrt Δ) * ‖Xmat d N x‖ := by funext x; ring
          rw [heq2, integral_const_mul]
  -- The main algebraic identity: `E = R1 + Δ • bracket + (II)`.
  have hIIbound : ‖(∫ x, B x ∂ (P d)) - Φk M - Δ • genPt d N Φk M‖
      ≤ (2 / 3) * genPtLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
          * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := hII
  have hR1val : (∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d))
      = (∫ x, A x ∂ (P d)) - (∫ x, B x ∂ (P d)) - (Δ : ℂ) * (∫ x, Z x ∂ (P d)) := by
    have hAB : Integrable (fun x => A x - B x) (P d) := hIntK1.sub hIntK
    have hZc : Integrable (fun x => (Δ : ℂ) * Z x) (P d) := hIntZM.const_mul (Δ : ℂ)
    have step1 : (∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d))
        = (∫ x, (A x - B x) ∂ (P d)) - (∫ x, (Δ : ℂ) * Z x ∂ (P d)) := integral_sub hAB hZc
    rw [step1, integral_sub hIntK1 hIntK, integral_const_mul]
  have hident : (∫ x, A x ∂ (P d)) - Φk M - Δ • loopDrift E uk I M
      = (∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d))
        + (Δ : ℂ) * ((∫ x, Z x ∂ (P d)) - z0)
        + ((∫ x, B x ∂ (P d)) - Φk M - Δ • genPt d N Φk M) := by
    rw [hR1val, hΔsmul, hΔsmul, hld]
    ring
  have hrpow : Δ * Real.sqrt Δ = Δ ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hΔpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hbracketmul : Δ * ‖(∫ x, Z x ∂ (P d)) - z0‖
      ≤ zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E) * Δ ^ (3 / 2 : ℝ)
          * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
    have h := mul_le_mul_of_nonneg_left hbracketbound hΔpos.le
    calc Δ * ‖(∫ x, Z x ∂ (P d)) - z0‖
        ≤ Δ * (zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E) * Real.sqrt Δ
            * (∫ x, ‖Xmat d N x‖ ∂ (P d))) := h
      _ = zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E) * Δ ^ (3 / 2 : ℝ)
            * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by rw [← hrpow]; ring
  have step_outer := norm_add_le
    ((∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d)) + (Δ : ℂ) * ((∫ x, Z x ∂ (P d)) - z0))
    ((∫ x, B x ∂ (P d)) - Φk M - Δ • genPt d N Φk M)
  have step_inner := norm_add_le (∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d))
    ((Δ : ℂ) * ((∫ x, Z x ∂ (P d)) - z0))
  have step_normmul : ‖(Δ : ℂ) * ((∫ x, Z x ∂ (P d)) - z0)‖ = Δ * ‖(∫ x, Z x ∂ (P d)) - z0‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔpos]
  rw [step_normmul] at step_inner
  calc ‖(∫ x, A x ∂ (P d)) - Φk M - Δ • loopDrift E uk I M‖
      = ‖(∫ x, ((A x - B x) - (Δ : ℂ) * Z x) ∂ (P d))
          + (Δ : ℂ) * ((∫ x, Z x ∂ (P d)) - z0)
          + ((∫ x, B x ∂ (P d)) - Φk M - Δ • genPt d N Φk M)‖ := by rw [hident]
    _ ≤ zMotionZLip (d.L N) (d.W N) I.σ.length ((1 - uk1) * (mE E).im) (mSigma E)
          * ‖mE E‖ * Δ ^ 2 / 2
        + zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
          * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d))
        + (2 / 3) * genPtLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
          * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
        linarith [hR1bound, hbracketmul, hIIbound, step_outer, step_inner]
    _ = zMotionZLip (d.L N) (d.W N) I.σ.length ((1 - uk1) * (mE E).im) (mSigma E)
          * ‖mE E‖ * Δ ^ 2 / 2
        + (zMotionLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E)
            + (2 / 3) * genPtLip (d.L N) (d.W N) I.σ.length |(zt E uk).im| (mSigma E))
          * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by ring

/-- **(T4)**: `RBM.Gauss.Grid.condExp_loop_drift`. Combines (T1) (the freezing lemma applied to
the one-step grid recursion) with the deterministic bound `norm_loop_step_drift_le` above,
applied pointwise at `M := H_k(ω)` (Hermitian for every `ω`, `RBM.Gauss.Grid.H_isHermitian`). -/
theorem condExp_loop_drift (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ) (hEb : |E| < 2)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) (hst : s N < t N)
    (hk : k < K N) (hu0 : 0 ≤ time s t K N k) (hu1 : time s t K N (k + 1) < 1)
    (hzk : (zt E (time s t K N k)).im ≠ 0)
    (hzk1 : (zt E (time s t K N (k + 1))).im ≠ 0) :
    ∀ᵐ ω ∂ (Pg d),
      ‖(Pg d)[fun ω' : Ωg d => loopObs d N (zt E (time s t K N (k + 1))) I
            (H d s t K N (k + 1) ω') | filt d k] ω
          - loopObs d N (zt E (time s t K N k)) I (H d s t K N k ω)
          - (step s t K N : ℂ) • loopDrift E (time s t K N k) I (H d s t K N k ω)‖
        ≤ zMotionZLip (d.L N) (d.W N) I.σ.length
              ((1 - time s t K N (k + 1)) * (mE E).im) (mSigma E) * ‖mE E‖
              * (step s t K N) ^ 2 / 2
          + (zMotionLip (d.L N) (d.W N) I.σ.length |(zt E (time s t K N k)).im| (mSigma E)
              + (2 / 3) * genPtLip (d.L N) (d.W N) I.σ.length |(zt E (time s t K N k)).im|
                  (mSigma E))
            * (step s t K N) ^ (3 / 2 : ℝ) * (∫ ω', ‖Xmat d N ω'‖ ∂ (P d)) := by
  have hT1 := condExp_loop_step s t K N k E hwf hn hzk1
  filter_upwards [hT1] with ω hω
  rw [hω]
  exact norm_loop_step_drift_le s t K N k E hEb hwf hn hst hk hu0 hu1 hzk
    (H_isHermitian d s t K N k ω)

end T4

/-! ### §8 : a compiled satisfiability witness for (T4)'s hypotheses -/

/-- **A concrete, non-degenerate instantiation** of every hypothesis of `condExp_loop_drift`
holding simultaneously: `Dims.exampleGrow`, `E = 0`, a single grid step of size `1/8` inside the
window `[1/4, 3/8] ⊆ [0, 1)`, and the shortest well-formed loop `⟨[true], [0]⟩` (length `1`).
None of the hypotheses collapses the statement (no `N = 0` grid, no empty index set, no
astronomically large parameter is used). -/
example :
    ∃ (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ), |E| < 2 ∧
      ∃ I : LoopIdx (ZMod ((Dims.exampleGrow).L N)), I.WF ∧ 1 ≤ I.a.length ∧
        s N < t N ∧ k < K N ∧ 0 ≤ time s t K N k ∧ time s t K N (k + 1) < 1 ∧
        (zt E (time s t K N k)).im ≠ 0 ∧ (zt E (time s t K N (k + 1))).im ≠ 0 := by
  refine ⟨fun _ => 1 / 4, fun _ => 1 / 2, fun _ => 2, 0, 0, 0, by norm_num,
    ⟨[true], [0]⟩, rfl, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · unfold time step; norm_num
  · unfold time step; norm_num
  · exact zt_im_ne_zero_of_lt_one (by norm_num) (by unfold time step; norm_num)
  · exact zt_im_ne_zero_of_lt_one (by norm_num) (by unfold time step; norm_num)

end RBM.Gauss.Grid

end

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelBddT
import RBM1D.Gauss.Step6HierarchyGauss
import RBM1D.Gauss.DischargeBDG
import RBM1D.Gauss.SteinMatrix
import RBM1D.Gauss.EEUker

/-!
# The moment route's drift integrand: the pointwise generator and path continuity

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  The drift on the right of (5.20) is the *definition* `RBM.DriftDef.driftF`
(the drift of (5.15), pinned — **not** a free tensor), a finite algebraic expression in the
loops `L_{u,J}`, the spectral edge `G(σ) - m(σ)` and the primitive `K_u`.  The moment route
needs, at every Hermitian matrix,

  `∂_u Ψ₁ + 𝓛 Ψ₁ = (U_{u,t} ∘ F_u)_a`,  `Ψ₁(u, M) = (U_{u,t} ∘ (L - K)_u)_a`,  `F = driftF`,

and the two first-order terms have to be added before the modulus is taken: bounding `∂_uΨ₁`
and `𝓛Ψ₁` separately leaves `U ∘ Θ(L-K)`, which is not small.  This file supplies the pointwise
form of the generator `𝓛` and the continuity statements that the integrability side conditions
of the moment inequality are built from.

## Main results

* `RBM.Gauss.sum_used_eq_sum_pairs_coordD2_pt`, `RBM.Gauss.genD_eq_sum_pairs` — `𝓛` in the
  paper's index-pair form `∑_{ij} S_ij ∂_ij∂_ji`, pointwise and with no regularity hypothesis.
* `RBM.Gauss.continuous_Hflow_time` — `u ↦ H_u(ω) = √u X(ω)` is continuous at every `u`,
  including `u = 0`.
* `RBM.Gauss.continuousOn_gloop_path`, `RBM.Gauss.continuousOn_Gsig_path`,
  `RBM.Gauss.continuousOn_Kval_path`, `RBM.Gauss.continuousOn_primBil`,
  `RBM.Gauss.continuousOn_eGterm_path` — the ingredients of the pinned drift and of `E ⊗ E`
  are continuous along a continuous path of (time, Hermitian matrix).
* `RBM.Gauss.window_le_abs_im`, `RBM.Gauss.window_eta_pos`, `RBM.Gauss.window_im_ne_zero` — on
  the window `[s, v] ⊆ [0, 1)` the spectral parameter stays off the real axis, with the explicit
  `η = (1-v) Im m_E`, so the deterministic envelope `‖G‖ ≤ (Im z_u)⁻¹` is uniform there (and
  **not** on `[0, 1)` itself, where it does not exist).
* `RBM.Gauss.window_norm_mul_lt` — `‖u m(σ) m(σ')‖ < 1` on the window.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ}

/-! ### The second directional derivative of a finite deterministic linear combination

`RBM.Uker` is a finite `ℂ`-linear combination with matrix-independent coefficients
(`RBM.Uker_apply`), so `RBM.Gauss.coordD2` — and hence `RBM.Gauss.genD` — passes through it.
This is the second-order companion of `RBM.Gauss.EmartCoeff_sum`, which does the same for the
first derivative. -/

/-! ### `𝓛` in the paper's index-pair form, pointwise

`RBM.Gauss.sum_used_eq_sum_pairs_coordD2` is stated under the integral sign and needs a
`RBM.Gauss.TestFun`.  The passage from the coordinate sum to the index-pair sum is purely
combinatorial (`RBM.Gauss.sum_used_eq_sum_pairs` with the symmetry `coordD2_swap`), so it
holds pointwise and with no regularity hypothesis at all. -/

/-- **`∑_{α ∈ usedCoord} S_α ∂_α² Φ = ∑_{ij} S_ij ∂_ij∂_ji Φ`, pointwise.** -/
theorem sum_used_eq_sum_pairs_coordD2_pt (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • coordD2 d N Φ M p
      = ∑ i : d.Idx N, ∑ j : d.Idx N,
          Sblk (d.L N) (d.W N) i j • wirtSecond d N Φ M i j := by
  have hlhs : ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • coordD2 d N Φ M p
      = ∑ p ∈ usedCoord d N,
        (if p.1 = p.2.1 then Sblk (d.L N) (d.W N) p.1 p.2.1
         else Sblk (d.L N) (d.W N) p.1 p.2.1 / 2) • coordD2 d N Φ M p :=
    Finset.sum_congr rfl fun p _ => by rw [gvar_crd]
  rw [hlhs, show usedCoord d N = Finset.univ.filter
      (fun p : d.Idx N × d.Idx N × Bool =>
        idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
    sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N) (Sblk (d.L N) (d.W N))
      (Sblk_comm (d.L N) (d.W N)) _ (fun i j => coordD2_swap Φ M i j true)
      (fun i j => coordD2_swap Φ M i j false)]
  rfl

/-- **`RBM.Gauss.genD` in the index-pair form.** -/
theorem genD_eq_sum_pairs (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genD d N Φ M
      = (2⁻¹ : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
          Sblk (d.L N) (d.W N) i j • wirtSecond d N Φ M i j := by
  rw [genD, sum_used_eq_sum_pairs_coordD2_pt Φ M]

section Band

variable {Ω : Type*} [MeasurableSpace Ω]

end Band

/-! ### The time derivative of `Ψ = |Ψ₁|^{2p}`, in the real first-order form -/

section Band2

variable {Ω : Type*} [MeasurableSpace Ω]

end Band2

/-! ### Interval integrability from a deterministic envelope

The moment inequality asks, per `(p, N, σ, v, a)`, for five side conditions besides the
derivative and the pointwise inequality: a window bound on `ψ`, the `ContinuousOn` of
`u ↦ E|Ψ₁|^{2p}`, and the interval integrability of `φ'`, of the two drift integrands, and of
the product `ψ · f`.  All of them are instances of one statement: a family
of random variables that is **continuous in the time at each sample point** and **bounded by a
deterministic constant over the window** has continuous — hence interval integrable — moments.

The constant is the envelope `‖G‖ ≤ (Im z_u)⁻¹`, which on the paper's window
`[s_N, v] ⊆ [0, 1)` is uniform because `Im z_u = (1-u) Im m_E ≥ (1-v) Im m_E > 0`.  Nothing
here quantifies `u` over all of `ℝ`: at `u = 1` no envelope exists. -/

section Envelope

variable {Ω : Type*} [MeasurableSpace Ω]

end Envelope

/-! ### The time-continuity of the flow, and of the moment route's `Ψ₁` along it -/

section FlowTime

/-- `u ↦ H_u(ω) = √u X(ω)` is continuous — at **every** `u`, including `u = 0`, because
`Real.sqrt` is.  (Differentiability in `u` fails at `0`; only continuity is used here, which is
why the window `[s_N, v]` is allowed to start at `s_N = 0`.) -/
theorem continuous_Hflow_time (d : Dims) (N : ℕ) (ω : Ω d) :
    Continuous fun u : ℝ => Hflow d N u ω := by
  have hfun : (fun u : ℝ => Hflow d N u ω)
      = fun u : ℝ => ((Real.sqrt u : ℝ) : ℂ) • Xmat d N ω := by
    funext u
    ext i j
    simp [Hflow, Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).smul continuous_const

end FlowTime

section DriftEnvelope

variable {Ω : Type*} [MeasurableSpace Ω]

end DriftEnvelope

/-! ### `𝓛F` from a uniform second-derivative bound -/

/-! ### The uniform envelope of the drift integrand of (5.20) -/

section DriftBound

variable {Ω : Type*} [MeasurableSpace Ω]

end DriftBound

/-! ### Continuity of the pinned drift and of `E ⊗ E` along a path

The envelope above is a *size* statement; interval integrability needs a *measurability*
statement too.  `RBM.DriftDef.driftF` and `RBM.MomentDuhamel.eeFun` are finite algebraic
expressions in three ingredients — the loops `L_{u,J}`, the spectral edge `G(σ) - m(σ)` and
the primitive `K_u` — and each of the three is continuous.

Everything is stated along an arbitrary continuous path `x ↦ (τ x, M x)` of (time, Hermitian
matrix), because the moment route needs it twice: with `x = u` and `M = H_u(ω)` for the
**time**-continuity that interval integrability asks for, and with `x = ω` and `τ` constant
for the **sample**-measurability that the Bochner integral asks for.  Doing it once avoids
proving the same chain twice. -/

section PathContinuity

variable {X : Type*} [TopologicalSpace X]

/-- **Every loop is continuous along a continuous Hermitian path.**  Joint `C²` in `(u, M)`
(`RBM.Gauss.contDiffAt_loopObs_zt_pair`) composed with the path; at a Hermitian matrix
`RBM.Gauss.loopObs` *is* `RBM.gloop`. -/
theorem continuousOn_gloop_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    ContinuousOn (fun x => gloop (d.L N) (d.W N) (Mt x) (zt E (τ x)) I) S := by
  have hEq : (fun x => gloop (d.L N) (d.W N) (Mt x) (zt E (τ x)) I)
      = fun x => loopObs d N (zt E (τ x)) I (Mt x) := by
    funext x
    exact (loopObs_of_isHermitian (hherm x)).symm
  rw [hEq]
  intro x hx
  have hjoint : ContinuousAt (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      loopObs d N (zt E q.1) I q.2) (τ x, Mt x) :=
    (contDiffAt_loopObs_zt_pair E (hzim x hx) I _).continuousAt
  have hcomp := ContinuousAt.comp_continuousWithinAt (s := S) (x := x)
    (g := fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => loopObs d N (zt E q.1) I q.2)
    (f := fun y : X => ((τ y, Mt y) : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ))
    hjoint ((hτ x hx).prodMk (hMt x hx))
  rw [Function.comp_def] at hcomp
  exact hcomp

/-- **The spectral edge `G^{(σ)}` is continuous along a continuous Hermitian path.** -/
theorem continuousOn_Gsig_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0) (sgn : Bool) :
    ContinuousOn (fun x => Gsig (Mt x) (zt E (τ x)) sgn) S := by
  have hEq : (fun x => Gsig (Mt x) (zt E (τ x)) sgn)
      = fun x => Gsig (hermCLM (d.Idx N) (Mt x)) (zt E (τ x)) sgn := by
    funext x
    rw [hermCLM_of_isHermitian (hherm x)]
  rw [hEq]
  intro x hx
  have hjoint : ContinuousAt (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Gsig (hermCLM (d.Idx N) q.2) (zt E q.1) sgn) (τ x, Mt x) :=
    (contDiffAt_Gsig_zt_pair E (hzim x hx) sgn _).continuousAt
  have hcomp := ContinuousAt.comp_continuousWithinAt (s := S) (x := x)
    (g := fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Gsig (hermCLM (d.Idx N) q.2) (zt E q.1) sgn)
    (f := fun y : X => ((τ y, Mt y) : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ))
    hjoint ((hτ x hx).prodMk (hMt x hx))
  rw [Function.comp_def] at hcomp
  exact hcomp

section KvalCont

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The primitive `K_u` is continuous in the time at every well-formed index.**

Loops of length `≥ 2` are differentiable in the time (`RBM.hasDerivAt_Kgen_all`); loops
of length `0` or `1` do not move at all (`RBM.Kgen` is `0` resp. `m(σ₁)` there). -/
theorem continuousOn_Kval_path (B : Band Ω) (E : ℝ) (N : ℕ) {S : Set X} {τ : X → ℝ}
    (hτ : ContinuousOn τ S)
    (hm : ∀ x ∈ S, ∀ s s' : Bool, ‖((τ x : ℝ) : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (I : LoopIdx (ZMod (B.L N))) (hI : I.WF) :
    ContinuousOn (fun x => B.Kval E N (τ x) I) S := by
  rcases Nat.lt_or_ge I.length 2 with h | h
  · have hconst : ∀ r : ℝ, B.Kval E N r I = B.Kval E N 0 I := by
      intro r
      show Kgen (B.L N) (B.W N) (mSigma E) r I = Kgen (B.L N) (B.W N) (mSigma E) 0 I
      unfold Kgen
      split_ifs <;> first | rfl | omega
    exact continuousOn_const.congr fun x _ => hconst (τ x)
  · intro x hx
    have hd : ContinuousAt (fun r : ℝ => B.Kval E N r I) (τ x) :=
      (hasDerivAt_Kgen_all (L := B.L N) (B.W N) (mSigma E) (B.three_le_L N)
        (hm x hx) I hI h).continuousAt
    exact hd.comp_continuousWithinAt (hτ x hx)

end KvalCont

/-! #### The three bilinear blocks of (5.15) -/

section Bilinear

variable {L : ℕ} [NeZero L]

/-- `primBil` is continuous when both tensors are. -/
theorem continuousOn_primBil (W : ℕ) {S : Set X} {Y Z : X → LoopIdx (ZMod L) → ℂ}
    (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Y x J) S)
    (hZ : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Z x J) S) :
    ContinuousOn (fun x => primBil L W (Y x) (Z x) I) S := by
  simp only [primBil]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun k hk => ?_)
  refine continuousOn_finsetSum _ fun l hl => ?_
  refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  exact ((hY _ (hI.cutGlueL a hk.1 hl.1 hl.2)).mul continuousOn_const).mul
    (hZ _ (hI.cutGlueR b hk.1 hl.1 hl.2))

end Bilinear

/-- `RBM.Gauss.eGterm` is continuous along a continuous Hermitian path. -/
theorem continuousOn_eGterm_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    ContinuousOn (fun x => eGterm (d.L N) (d.W N) (mSigma E) (Mt x) (zt E (τ x)) I) S := by
  simp only [eGterm]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun k _ => ?_)
  refine continuousOn_finsetSum _ fun c _ => continuousOn_finsetSum _ fun b _ => ?_
  have htr : Continuous (fun A : Matrix (d.Idx N) (d.Idx N) ℂ =>
      Matrix.trace (A * Eblk (d.L N) (d.W N) c)) :=
    continuous_matrixTrace.comp (continuous_id.matrix_mul continuous_const)
  have hA : ContinuousOn (fun x =>
      Gsig (Mt x) (zt E (τ x)) (I.σ.getD (k - 1) true)
        - mSigma E (I.σ.getD (k - 1) true) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) S :=
    (continuousOn_Gsig_path d N E hτ hMt hherm hzim _).sub continuousOn_const
  exact ((htr.comp_continuousOn hA).mul continuousOn_const).mul
    (continuousOn_gloop_path d N E hτ hMt hherm hzim _)

/-! #### `L - K` along the path -/

/-! #### `E ⊗ E` along the path -/

end PathContinuity




/-! ### The window of the five side conditions

For the Gaussian sample, on the paper's window `[s, v] ⊆ [0, 1)`, all envelopes are the
deterministic `‖G‖ ≤ (Im z_u)⁻¹`. -/

section SideConditions

/-! #### The window package -/

/-- On `[s, v]` with `v < 1` and `|E| < 2` the spectral parameter stays off the real axis, with
the explicit `η = (1-v) Im m_E`. -/
theorem window_le_abs_im {E : ℝ} (hE : |E| < 2) {s v : ℝ} (hv1 : v < 1) :
    ∀ u ∈ Set.Icc s v, (1 - v) * (mE E).im ≤ |(zt E u).im| :=
  fun _ hu => le_abs_im_zt_of_le hE hv1 hu.2

theorem window_eta_pos {E : ℝ} (hE : |E| < 2) {v : ℝ} (hv1 : v < 1) :
    0 < (1 - v) * (mE E).im := mul_pos (by linarith) (mE_im_pos hE)

theorem window_im_ne_zero {E : ℝ} (hE : |E| < 2) {s v : ℝ} (hv1 : v < 1) :
    ∀ u ∈ Set.Icc s v, (zt E u).im ≠ 0 :=
  fun u hu => im_zt_ne_zero_of_le (window_eta_pos hE hv1) (window_le_abs_im hE hv1 u hu)

theorem window_norm_mul_lt {E : ℝ} (hE : |E| ≤ 2) {s v : ℝ} (hs0 : 0 ≤ s) (hv1 : v < 1) :
    ∀ u ∈ Set.Icc s v, ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1 := by
  intro u hu x y
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hs0.trans hu.1), norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
  exact lt_of_le_of_lt hu.2 hv1

/-! #### The three integrands along the Gaussian flow -/

variable (d : Dims)

/-! #### The bridge and the three envelopes on the window -/

variable {d}

/-! #### Item 1: the window bound on `ψ` -/

/-! #### Item 2: `ContinuousOn` of `u ↦ E|Ψ₁|^{2p}` -/

/-! #### The envelope of the quadratic-variation integrand -/

/-! #### Items 3–5: the interval integrabilities -/

/-! #### Items 4 and 5 -/

/-! #### The primitive's own window bound, from compactness

`K_u` and `∂_u K_u` are continuous in `u` and the loop arguments range over a *finite* type, so
on the compact window `[s, v] ⊆ [0, 1)` they are bounded — no hypothesis needed.  (The bound
does blow up as `v ↑ 1`; that is why it is taken on `[s, v]` and not on `[0, 1)`, which would
be unsatisfiable.) -/

end SideConditions

end Gauss

namespace MomentDuhamel

section CnpAssembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ### Sharpness and the discriminating check -/

end CnpAssembly

end MomentDuhamel

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

end Gauss

end RBM

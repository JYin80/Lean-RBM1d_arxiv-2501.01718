/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Hierarchy
import RBM1D.Hierarchy.Dynamics
import RBM1D.Flow.Initial
import RBM1D.Gauss.MomentGronwall
import RBM1D.Gauss.LoopC2
import RBM1D.Hierarchy.Decay

/-!
# The moving spectral parameter and the drift of `L - K` (T134, T140)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 2.11 / (2.45)-(2.47) (pp. 17-19) and (5.12)-(5.19) (pp. 52-53).

**T140 closes the cut-and-glue algebra.**  `RBM.Gauss.LoopIto` — the one deterministic
hypothesis T76 left open — is now a theorem (`RBM.Gauss.loopItoFrozen`), so Lemma 2.11 in
moment form (`RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss`) rests only on
`RBM.Gauss.MatrixStein` (T70) and the joint differentiability `hjoint` (T141).

`RBM1D/Gauss/Hierarchy.lean` (T76) differentiates `v ↦ E[L(H_v, z_u)]` with the spectral
parameter **frozen** at `z_u`.  This file removes the freeze and computes exactly what the
motion of `z_t` contributes.

## The answer: the `-m` of (2.47) *is* the motion of `z_t`

Since `z_t = E + (1-t) m^{(E)}` and `∂_z (H - z)^{-1} = G²`, each `G(σ_k)` in the loop
contributes `-m(σ_k) G(σ_k)²`; summing the glue index with `W ∑_b E_b = 1` turns the doubled
`G(σ_k)` into `W ∑_b L_{G^{(b)}_k(σ,a)}` of Definition 2.10 (1).  The upshot
(`RBM.Gauss.eGterm_sub_eGterm`) is

  `∂_u L_{σ,a}(M, z_u) = Ẽ_{σ,a}[G - m] - Ẽ_{σ,a}[G]`,

with `Ẽ` the `RBM.Gauss.eGterm` of T76.  **So the identity of T76 does hold in the stated
shape, but only after the extra term is added**: `LoopIto.second` produces (2.47) with `G` in
place of `G̃`, and the `z`-motion supplies precisely the missing `-m(σ_k)⟨E_a⟩` piece.  The
pointwise statement is `RBM.Gauss.generator_add_zMotion`:

  `(𝓛 + ∂_u) L_{σ,a} = Ẽ_{σ,a}[G - m] + W ∑_{k<l} (G^L ∘ L) S^(B) (G^R ∘ L)`,

at every Hermitian matrix, with `𝓛 = ½ ∑_{ij} S_ij ∂_ij ∂_ji`.

## Joint differentiability by composition

The chain rule `d/du f(u,u) = ∂₁f + ∂₂f` is `RBM.Gauss.hasDerivAt_comp_diag`, obtained from
joint Fréchet differentiability and `HasFDerivAt.comp_hasDerivAt`.  The joint smoothness of
the *integrand* is obtained by composition, as the ticket prescribes
(`RBM.Gauss.contDiffAt_green_comp` → `contDiffAt_Gsig_flow` → `contDiffAt_gloopProd_flow` →
`contDiffAt_gloop_flow`): `Ring.inverse` is `C^∞` at every unit (`contDiffAt_ringInverse`),
`√·` is `C^∞` away from `0`, and the loop product is a finite product of those.  Nothing here
uses "continuous partials ⟹ differentiable", which Mathlib does not have.

## (5.16) as printed omits an `S^(B)` (T140)

(5.19) identifies the `l_K = 2` part of the coupling of (5.15) with the generator `Θ_{t,σ}`
of (5.16).  Carrying that identification out (`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`)
shows that the kernel it produces is

  `ξ_i · Θ^{(B)}_{t ξ_i} · S^(B)`,   `ξ_i = m(σ_i) m(σ_{i+1})`,

whereas (5.16) — and `RBM.ThetaOp`, which transcribes it literally — has `ξ_i Θ^{(B)}_{t ξ_i}`
with **no** `S^(B)`.  The missing factor is not an artefact of this formalization: the paper's
own Example 2.16 (p. 21) writes the `n = 3` primitive equation with the kernel
`(m_i m_{i+1} Θ^{(B)}_{t m_i m_{i+1}} · S^(B))_{a_i c_i}`, and the same factor is forced by
`∂_t U_{s,t,σ} = Θ_{t,σ} ∘ U_{s,t,σ}` through (5.18).  So (5.16) has a typo.  The corrected
operator is `RBM.Gauss.thetaGenLoop`, and `RBM.Gauss.thetaGenLoop_kernel_eq` records the exact
relation to the printed one: `ξ Θ_{tξ} S^(B) = t⁻¹ (Θ_{tξ} - 1)`.  See `docs/paper-deltas.md`.

## Main definitions

* `RBM.Gauss.zMotion` — `∑_k (-m(σ_k)) · W ∑_b L_{G^{(b)}_k(σ,a)}`, the contribution of the
  motion of `z_t` to `∂_t L_{t,σ,a}`.
* `RBM.Gauss.gprodM`, `RBM.Gauss.insB` — the loop product with *arbitrary* inserted matrices,
  and the insertion of one extra matrix in front of the `k`-th factor.  `insB` with `E_b`
  inserted is Definition 2.10 (1) (`RBM.LoopIdx.cutGlue`), and `insB` with a Hermitian
  direction `B` inserted is what one differentiation of `L_{σ,a}` in `H` produces.
* `RBM.Gauss.xiLoop`, `RBM.Gauss.thetaGenLoop` — the edge parameter `ξ_i = m(σ_i)m(σ_{i+1})`
  read cyclically off a `LoopIdx`, and the generator (5.16) *with the missing `S^(B)`*.

## Main results

**The `z`-motion.**

* `RBM.Gauss.hasDerivAt_green_path` : `∂_u G(M, ζ_u) = ζ'_u G²`, needing invertibility only
  *at the point* (the path `u ↦ z_u` hits the real axis at `u = 1`, so the whole-line
  hypothesis of `RBM.Gauss.hasDerivAt_lineInverse` is unavailable).
* `RBM.Gauss.hasDerivAt_Gsig_zt` : `∂_u G(σ)(M, z_u) = -m(σ) G(σ)²`, both charges.
* `RBM.Gauss.hasDerivAt_gloopProd_zt` : Leibniz over the `n` factors of (2.41).
* `RBM.Gauss.eGterm_sub_eGterm` : `Ẽ[G-m] - Ẽ[G] = zMotion`, the identification above.
* `RBM.Gauss.hasDerivAt_gloop_zt_eGterm` : the two combined.
* `RBM.Gauss.norm_zMotion_le` : the deterministic envelope, (5.2) one slot longer.

**In expectation.**

* `RBM.Gauss.hasDerivAt_integral_gloop_zt` : differentiation under the integral in `z` alone,
  with *no* hypotheses beyond a uniform `η ≤ |Im z_s|` on a ball (the envelope is
  deterministic, so the dominating function is a constant).
* `RBM.Gauss.hasDerivAt_integral_gloop_hierarchy_movingZ`,
  `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy` : **the moment form of Lemma 2.11 with both
  arguments moving.**  The differentiated function is literally `v ↦ E L_{v,σ,a}`
  (`RBM.Sample.ELval`), not its frozen-`z` surrogate, and the drift carries the paper's
  `G̃ = G - m`.

**The drift of `L - K`.**

* `RBM.Gauss.generator_add_zMotion` : the pointwise drift identity.
* `RBM.Gauss.hasDerivAt_sub_prim`, `RBM.Gauss.hasDerivAt_sub_prim_of_isPrimitive` :
  `∂_u (L - K) = Ẽ + [K ~ (L-K)] + E^{((L-K)×(L-K))}`, i.e. (5.12)-(5.14), by subtracting
  the primitive equation (2.48) and polarizing the shared quadratic term
  (`RBM.primRhs_sub`, `RBM1D/Hierarchy/Dynamics.lean`).

**The cut-and-glue identity itself (T140).**

* `RBM.Gauss.loopIto_second_frozen` : `½ ∑_{ij} S_ij ∂_ij ∂_ji L_{σ,a} = Ẽ_{σ,a}[G] + W ∑_{k<l}
  (G^L ∘ L) S^(B) (G^R ∘ L)`, i.e. (2.47) with `G` in place of `G̃`.  **No boundary term.**
* `RBM.Gauss.loopItoFrozen` : the `RBM.Gauss.LoopIto` instance, so T76's hypothesis is gone.
* `RBM.Gauss.generator_add_zMotion_gauss`,
  `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` : Lemma 2.11 pointwise and in moment
  form with `hito`, `hEG` and `TestFun` all discharged.

**(5.19), the `l_K = 2` coupling (T140).**

* `RBM.Gauss.cutGlueL_succ_eq`, `RBM.Gauss.cutGlueR_succ_eq`, `RBM.Gauss.cutGlueL_one_eq`,
  `RBM.Gauss.cutGlueR_one_eq` : the explicit shape of the two chains at the `n` cuts that
  produce a 2-loop.  For the adjacent cuts `(k, k+1)` the `K`-loop is the right chain
  `⟨G(σ_k) E_{a_k} G(σ_{k+1}) E_b⟩` and the `(L-K)`-loop is `a` with `a_k` replaced; at the
  wrap-around cut `(1, n)` the two roles are exchanged.
* `RBM.Gauss.primBilLen_two_eq`, `RBM.Gauss.primBilLenR_two_eq` : *which* cuts survive the
  grading `l_K = 2` — exactly `(1, n)` on the left and `(k, k+1)` on the right, the `n` terms
  of the `i`-sum of (5.16).
* `RBM.Gauss.couplingLen_two_eq_thetaGenLoop` : **(5.19)**,
  `[K ∼ (L-K)]^{l_K = 2} = Θ_{t,σ} ∘ (L-K)`, with `K` the rank-2 primitive `RBM.kTwo` of
  (2.57) and `Θ_{t,σ}` the corrected generator `RBM.Gauss.thetaGenLoop` (see above).
* `RBM.Gauss.thetaGenOp`, `RBM.Gauss.thetaGenLoop_ofFn` : the same operator in the `LoopArg`
  (tensor) representation of `RBM.Uker`/`RBM.ThetaOp`, and the bridge between the two
  representations — the one `docs/STATUS.md` leaves for whoever proves (5.19).  The bridge is
  `fun v => D ⟨σ, List.ofFn v⟩`, and the combinatorial content is
  `RBM.Gauss.set_ofFn_eq_ofFn_update` (`List.set` on `List.ofFn` is `Function.update`).
* `RBM.Gauss.smul_thetaGenOp_eq` : `t · (Θ_{t,σ} ∘ A)_a = ∑_i ∑_c (Θ^{(B)}_{tξ_i})_{a_i c}
  A_{a^{(i)}} - n A_a`, the corrected generator written without `S^(B)`.
* `RBM.Gauss.hasDerivAt_sub_prim_thetaGen` : **(5.15)** in the form §5.3 consumes,
  `∂_u (L-K) = Ẽ + Θ_{t,σ} ∘ (L-K) + ∑_{l_K > 2} [K ∼ (L-K)]^{l_K} + E^{((L-K)×(L-K))}`.

**The cut-and-glue algebra of `LoopIto.second` (T140).**

* `RBM.Gauss.traceBB_wirtPair`, `RBM.Gauss.sumSblk_half_wirtPair` : the generator's
  `½ ∑_{ij} S_ij ∂_ij ∂_ji` applied to a trace of the shape `⟨A B_{ij} C B_{ij}⟩` is the block
  bilinear form `½ W ∑_{ab} ⟨A E_a⟩ S^(B)_{ab} ⟨C E_b⟩` — this is where the `E_a`'s of
  Definition 2.10 come from, and it is uniform in `i, j` (the diagonal included).
* `RBM.Gauss.hasDerivAt_gprodM`, `RBM.Gauss.hasDerivAt_gprodM_second` : the first and second
  derivatives of the loop product in the matrix argument, Leibniz over the factors, as sums of
  loop products with `B` inserted (once, resp. twice).
* `RBM.Gauss.coordD2_loopObs_eq` : the two combined — `∂_ij ∂_ji L_{σ,a}` as an explicit double
  sum over the two insertion slots.

## Hypotheses (nothing here is an `axiom`)

* `RBM.Gauss.LoopIto d N (zt E u)` together with `hEG : hito.EG = eGterm … 0 …` — the
  deterministic cut-and-glue algebra of Lemma 2.11, owed by T76.  **No longer a hypothesis**:
  `RBM.Gauss.loopItoFrozen` builds the instance and `hEG` is `rfl`.  T134's observation that
  the *frozen* form suffices is what makes this affordable — the `G̃` of (2.47) is supplied by
  the motion of `z_t`.
* `RBM.Gauss.TestFun` — **no longer a hypothesis** either, by T133's
  `RBM.Gauss.testFun_loopObs_of_im_le`.
* `RBM.Gauss.MatrixStein` — T70, as in `RBM1D/Gauss/Hierarchy.lean`.  Still open.
* `hjoint` — joint differentiability of `(v, w) ↦ E[L(H_v, z_w)]` at `(u,u)`.  Pointwise in
  `ω` this is `RBM.Gauss.contDiffAt_gloop_flow`; passing it under the integral needs a
  dominating bound on the joint derivative that is uniform in `z` on a ball, which is T141.
  Still open.

So the only remaining inputs of Lemma 2.11 in this file are `MatrixStein` (T70) and `hjoint`
(T141); (5.19) needs in addition that `K` agrees with `RBM.kTwo` on 2-loops, and the
`‖t ξ‖ < 1` of `RBM.Theta`.
-/

namespace RBM.Gauss

open MeasureTheory Matrix Filter
open scoped Matrix.Norms.L2Operator

section GreenPath

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The resolvent along a real path of spectral parameters.**  If `ζ : ℝ → ℂ` has
derivative `c` at `w` and `M - ζ w` is invertible, then `s ↦ G(M, ζ s)` has derivative
`c • G²`.  Only invertibility *at the point* is needed (`Ring.inverse` is differentiable at
every unit), which is why `RBM.Gauss.hasDerivAt_lineInverse` — whose hypothesis is
invertibility along the whole line — cannot be used: the path `ζ = z_·` hits the real axis
at `u = 1`. -/
theorem hasDerivAt_green_path {M : Matrix n n ℂ} {ζ : ℝ → ℂ} {c : ℂ} {w : ℝ}
    (hζ : HasDerivAt ζ c w) (hU : IsUnit (M - ζ w • (1 : Matrix n n ℂ))) :
    HasDerivAt (fun s : ℝ => green M (ζ s)) (c • (green M (ζ w) * green M (ζ w))) w := by
  set U : (Matrix n n ℂ)ˣ := hU.unit with hUdef
  have hus : (U : Matrix n n ℂ) = M - ζ w • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have hinv : ((U⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = green M (ζ w) := by
    rw [green, Matrix.nonsing_inv_eq_ringInverse, ← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
      (M - ζ w • (1 : Matrix n n ℂ)) := by
    rw [← hus]; exact hasFDerivAt_ringInverse U
  have hpath : HasDerivAt (fun s : ℝ => M - ζ s • (1 : Matrix n n ℂ))
      (-(c • (1 : Matrix n n ℂ))) w := by
    simpa using (hζ.smul_const (1 : Matrix n n ℂ)).const_sub M
  have hcomp := hF.comp_hasDerivAt w hpath
  have hval : (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
      (-(c • (1 : Matrix n n ℂ))) = c • (green M (ζ w) * green M (ζ w)) := by
    simp [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinv, mul_neg, neg_mul]

  rw [hval] at hcomp
  have hfun : (fun s : ℝ => green M (ζ s))
      = (Ring.inverse (M₀ := Matrix n n ℂ)) ∘ (fun s : ℝ => M - ζ s • (1 : Matrix n n ℂ)) := by
    funext s
    simp [green, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  exact hcomp

/-- `z_u` read through the charge `σ`: `G(σ)` at `z_u` is the resolvent at
`E + (1-u) m(σ)`.  For `σ = -` this is the conjugate path, and its `u`-derivative is
`-m(-) = -conj m^{(E)}`, which is why the `-m(σ_k)` subtraction of (2.47) comes out with the
*right* charge. -/
theorem zt_charge (E w : ℝ) (σ : Bool) :
    (if σ then zt E w else (starRingEnd ℂ) (zt E w)) = (E : ℂ) + (1 - (w : ℂ)) * mSigma E σ := by
  cases σ with
  | false => simp [zt, mSigma, Complex.conj_ofReal]
  | true => simp [zt, mSigma]

theorem Gsig_zt (M : Matrix n n ℂ) (E w : ℝ) (σ : Bool) :
    Gsig M (zt E w) σ = green M ((E : ℂ) + (1 - (w : ℂ)) * mSigma E σ) := by
  rw [Gsig, zt_charge]

theorem ztSig_im_ne_zero {E w : ℝ} (hz : (zt E w).im ≠ 0) (σ : Bool) :
    ((E : ℂ) + (1 - (w : ℂ)) * mSigma E σ).im ≠ 0 := by
  rw [← zt_charge]
  cases σ <;> simpa using hz

theorem hasDerivAt_ztSig (E w : ℝ) (σ : Bool) :
    HasDerivAt (fun s : ℝ => (E : ℂ) + (1 - (s : ℂ)) * mSigma E σ) (-(mSigma E σ)) w := by
  have h : HasDerivAt (fun s : ℝ => s • (-(mSigma E σ) : ℂ)) (-(mSigma E σ)) w := by
    simpa using (hasDerivAt_id w).smul_const (-(mSigma E σ) : ℂ)
  have h2 := h.const_add ((E : ℂ) + mSigma E σ)
  have hfe : (fun s : ℝ => (E : ℂ) + (1 - (s : ℂ)) * mSigma E σ)
      = fun s : ℝ => ((E : ℂ) + mSigma E σ) + s • (-(mSigma E σ) : ℂ) := by
    funext s
    simp only [Complex.real_smul]
    ring
  rw [hfe]
  exact h2

/-- **The motion of the spectral parameter, one resolvent at a time.**
`∂_u G(σ)(H, z_u) = -m(σ) G(σ)²`. -/
theorem hasDerivAt_Gsig_zt {M : Matrix n n ℂ} (hM : M.IsHermitian) {E w : ℝ}
    (hz : (zt E w).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gsig M (zt E s) σ)
      ((-(mSigma E σ)) • (Gsig M (zt E w) σ * Gsig M (zt E w) σ)) w := by
  have hU : IsUnit (M - ((E : ℂ) + (1 - (w : ℂ)) * mSigma E σ) • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hM (ztSig_im_ne_zero hz σ)
  have h := hasDerivAt_green_path (M := M) (hasDerivAt_ztSig E w σ) hU
  simpa only [← Gsig_zt] using h

end GreenPath

/-! ### Leibniz over the loop product -/

section LoopPath

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- `W ∑_b E_b = 1`: summing the glue index of Definition 2.10 (1) closes the cut. -/
theorem smul_sum_Eblk :
    (W : ℂ) • ∑ b : ZMod L, Eblk L W b
      = (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  rw [sum_Eblk, smul_smul, mul_inv_cancel₀ hW, one_smul]

variable {L W}

omit [NeZero L] in
/-- `G^{(b)}_1` on a loop whose head is `(σ₀, c)`. -/
theorem cutGlue_cons_one (σ₀ : Bool) (σ : List Bool) (c b : ZMod L) (a : List (ZMod L)) :
    (⟨σ₀ :: σ, c :: a⟩ : LoopIdx (ZMod L)).cutGlue 1 b = ⟨σ₀ :: σ₀ :: σ, b :: c :: a⟩ := by
  simp [LoopIdx.cutGlue]

omit [NeZero L] in
/-- `G^{(b)}_{k+2}` on a loop whose head is `(σ₀, c)` leaves the head alone. -/
theorem cutGlue_cons_succ (σ₀ : Bool) (σ : List Bool) (c b : ZMod L) (a : List (ZMod L))
    (k : ℕ) :
    (⟨σ₀ :: σ, c :: a⟩ : LoopIdx (ZMod L)).cutGlue (k + 1 + 1) b
      = ⟨σ₀ :: ((⟨σ, a⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b).σ,
          c :: ((⟨σ, a⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b).a⟩ := by
  simp [LoopIdx.cutGlue]

/-- **The loop product moves with the spectral parameter.**  Leibniz over the `n` factors of
(2.41): the `k`-th summand is the loop with `G(σ_k)` doubled, and Definition 2.10 (1) writes
that doubling as `W ∑_b (·)_{G^{(b)}_k(σ,a)}` because `W ∑_b E_b = 1`. -/
theorem hasDerivAt_gloopProd_zt {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {E w : ℝ} (hz : (zt E w).im ≠ 0) :
    ∀ (σ : List Bool) (a : List (ZMod L)), σ.length = a.length →
      HasDerivAt (fun s : ℝ => gloopProd L W M (zt E s) ⟨σ, a⟩)
        (∑ k ∈ Finset.range a.length,
          (-(mSigma E (σ.getD k true))) •
            ((W : ℂ) • ∑ b : ZMod L,
              gloopProd L W M (zt E w) ((⟨σ, a⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b))) w := by
  have hglue : ∀ A X : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ,
      (W : ℂ) • ∑ b : ZMod L, A * Eblk L W b * X = A * X := by
    intro A X
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.smul_mul, ← Matrix.mul_smul,
      smul_sum_Eblk, Matrix.mul_one]
  have hpull : ∀ (A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (r : ℂ)
      (f : ZMod L → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ),
      r • ((W : ℂ) • ∑ b : ZMod L, A * f b) = A * (r • ((W : ℂ) • ∑ b : ZMod L, f b)) := by
    intro A r f
    simp [Finset.mul_sum]
  intro σ
  induction σ with
  | nil =>
      intro a hlen
      obtain rfl : a = [] := List.eq_nil_of_length_eq_zero hlen.symm
      simpa using hasDerivAt_const w (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
  | cons σ₀ σ ih =>
      intro a hlen
      obtain ⟨c, a', rfl⟩ : ∃ c a', a = c :: a' := by
        cases a with
        | nil => simp at hlen
        | cons c a' => exact ⟨c, a', rfl⟩
      have hlen' : σ.length = a'.length := by simpa using hlen
      have hG := hasDerivAt_Gsig_zt (M := M) hM hz σ₀
      have hP := ih a' hlen'
      have hfun :
          (fun t : ℝ => gloopProd L W M (zt E t) (⟨σ₀ :: σ, c :: a'⟩ : LoopIdx (ZMod L)))
            = fun t : ℝ =>
              Gsig M (zt E t) σ₀ * Eblk L W c * gloopProd L W M (zt E t) ⟨σ, a'⟩ := rfl
      rw [hfun]
      refine HasDerivAt.congr_deriv ((hG.mul_const (Eblk L W c)).mul hP) ?_
      simp only [List.length_cons, Finset.sum_range_succ', zero_add, List.getD_cons_zero,
        List.getD_cons_succ, cutGlue_cons_one, cutGlue_cons_succ]
      have hhead : ∀ b : ZMod L,
          gloopProd L W M (zt E w) (⟨σ₀ :: σ₀ :: σ, b :: c :: a'⟩ : LoopIdx (ZMod L))
            = Gsig M (zt E w) σ₀ * Eblk L W b
                * (Gsig M (zt E w) σ₀ * Eblk L W c
                    * gloopProd L W M (zt E w) ⟨σ, a'⟩) := fun _ => rfl
      have htail : ∀ (k : ℕ) (b : ZMod L),
          gloopProd L W M (zt E w)
              (⟨σ₀ :: ((⟨σ, a'⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b).σ,
                c :: ((⟨σ, a'⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b).a⟩ : LoopIdx (ZMod L))
            = (Gsig M (zt E w) σ₀ * Eblk L W c)
                * gloopProd L W M (zt E w) ((⟨σ, a'⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b) :=
        fun _ _ => rfl
      have tail_eq : (∑ k ∈ Finset.range a'.length,
            (-(mSigma E (σ.getD k true))) • ((W : ℂ) • ∑ b : ZMod L,
              gloopProd L W M (zt E w)
                (⟨σ₀ :: ((⟨σ, a'⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b).σ,
                  c :: ((⟨σ, a'⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b).a⟩ : LoopIdx (ZMod L))))
          = Gsig M (zt E w) σ₀ * Eblk L W c *
            (∑ k ∈ Finset.range a'.length,
              (-(mSigma E (σ.getD k true))) • ((W : ℂ) • ∑ b : ZMod L,
                gloopProd L W M (zt E w)
                  ((⟨σ, a'⟩ : LoopIdx (ZMod L)).cutGlue (k + 1) b))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [htail]
        exact hpull _ _ _
      have head_eq : (-(mSigma E σ₀)) • ((W : ℂ) • ∑ b : ZMod L,
            gloopProd L W M (zt E w) (⟨σ₀ :: σ₀ :: σ, b :: c :: a'⟩ : LoopIdx (ZMod L)))
          = ((-(mSigma E σ₀)) • (Gsig M (zt E w) σ₀ * Gsig M (zt E w) σ₀))
              * Eblk L W c * gloopProd L W M (zt E w) ⟨σ, a'⟩ := by
        simp only [hhead]
        rw [hglue]
        simp [mul_assoc]
      rw [tail_eq, head_eq, add_comm]


/-- Reindex `∑_{k=1}^{n}` as `∑_{k=0}^{n-1}`, the bridge between the `Finset.range`
bookkeeping of the Leibniz rule and the `Finset.Icc 1 n` bookkeeping of (2.47). -/
theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- **The `z`-motion term of a loop**: `∑_k (-m(σ_k)) · W ∑_b L_{G^{(b)}_k(σ,a)}`, i.e.
`∑_k (-m(σ_k)) ·` (the loop with `G(σ_k)` doubled at slot `k`).  This is what the motion of
`z_t` contributes to `∂_t L_{t,σ,a}`, and `RBM.Gauss.eGterm_sub_eGterm` identifies it with
the `-m` subtraction of (2.47). -/
noncomputable def zMotion (L W : ℕ) [NeZero L] [NeZero W] (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  ∑ k ∈ Finset.range I.length,
    (-(m (I.σ.getD k true))) *
      ((W : ℂ) * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b))

/-- **The `n`-loop moves with the spectral parameter**, raw form. -/
theorem hasDerivAt_gloop_zt {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {E w : ℝ} (hz : (zt E w).im ≠ 0) (I : LoopIdx (ZMod L)) (hwf : I.WF) :
    HasDerivAt (fun s : ℝ => gloop L W M (zt E s) I)
      (zMotion L W (mSigma E) M (zt E w) I) w := by
  simp only [zMotion]
  have hfd : FiniteDimensional ℝ (Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) := by
    infer_instance
  set T : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (ZMod L × Fin W) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hTapp : ∀ X, T X = Matrix.trace X := fun _ => rfl
  have h := hasDerivAt_gloopProd_zt (L := L) (W := W) hM hz I.σ I.a hwf
  have hcomp := T.hasFDerivAt.comp_hasDerivAt w h
  simp only [hTapp] at hcomp
  refine HasDerivAt.congr_deriv hcomp ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sum]
  simp [gloop]

/-- **The `z`-motion is exactly the `-m` subtraction of (2.47).**

`∂_u L_{σ,a}(H, z_u) = Ẽ_{σ,a}[G - m] - Ẽ_{σ,a}[G]`, where `Ẽ[·]` is `RBM.Gauss.eGterm`.
The two sides differ only by the `m(σ_k) ⟨E_a⟩` term, and `⟨E_a⟩ = 1`, `∑_a S^(B)_{ab} = 1`,
`W ∑_b E_b = 1` collapse it to the loop with `G(σ_k)` doubled. -/
theorem eGterm_sub_eGterm (hL : 3 ≤ L) (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) :
    eGterm L W m M z I - eGterm L W 0 M z I = zMotion L W m M z I := by
  simp only [zMotion]
  have hcol : ∀ b : ZMod L, ∑ a : ZMod L, SB L a b = 1 := by
    intro b
    have hsymm : ∀ a : ZMod L, SB L a b = SB L b a := fun a =>
      (congrFun (congrFun (SB_transpose L) a) b).symm
    simp only [hsymm]
    exact sum_SB_row L hL b
  simp only [eGterm, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [sum_Icc_one_eq_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : k + 1 - 1 = k := by omega
  simp only [hk]
  have hexp : ∀ a : ZMod L,
      Matrix.trace ((Gsig M z (I.σ.getD k true)
            - m (I.σ.getD k true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)
        - Matrix.trace ((Gsig M z (I.σ.getD k true)
            - (0 : Bool → ℂ) (I.σ.getD k true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)
        = -(m (I.σ.getD k true)) := by
    intro a
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, trace_Eblk]
    simp
  calc (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        (Matrix.trace ((Gsig M z (I.σ.getD k true)
            - m (I.σ.getD k true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a) * SB L a b * gloop L W M z (I.cutGlue (k + 1) b)
          - Matrix.trace ((Gsig M z (I.σ.getD k true)
            - (0 : Bool → ℂ) (I.σ.getD k true)
              • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a) * SB L a b * gloop L W M z (I.cutGlue (k + 1) b))
      = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          (-(m (I.σ.getD k true))) * (SB L a b * gloop L W M z (I.cutGlue (k + 1) b)) := by
        refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
        rw [← sub_mul, ← sub_mul, hexp a]
        ring
    _ = (-(m (I.σ.getD k true)))
          * ((W : ℂ) * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b)) := by
        have hinner : ∑ a : ZMod L, ∑ b : ZMod L,
            (-(m (I.σ.getD k true))) * (SB L a b * gloop L W M z (I.cutGlue (k + 1) b))
              = (-(m (I.σ.getD k true)))
                * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b) := by
          simp only [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_mul, hcol b, one_mul]
        rw [hinner]
        ring


/-- **The deterministic envelope of the `z`-motion term** (the (5.2) bound one slot longer).
The constant does not depend on the matrix, so it discharges `bound_integrable` in the
parametric-integral lemma. -/
theorem norm_zMotion_le {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : η ≤ |z.im|) (m : Bool → ℂ) (I : LoopIdx (ZMod L))
    (hwf : I.WF) :
    ‖zMotion L W m M z I‖
      ≤ (I.length : ℝ) * (max ‖m true‖ ‖m false‖ *
          ((W : ℝ) * ((Fintype.card (ZMod L) : ℝ) *
            (η⁻¹ ^ (I.length + 1) * (W : ℝ)⁻¹ ^ I.length)))) := by
  simp only [zMotion]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range I.length,
      ‖(-(m (I.σ.getD k true))) *
          ((W : ℂ) * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b))‖
        ≤ max ‖m true‖ ‖m false‖ *
            ((W : ℝ) * ((Fintype.card (ZMod L) : ℝ) *
              (η⁻¹ ^ (I.length + 1) * (W : ℝ)⁻¹ ^ I.length))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hb : ∀ b : ZMod L, ‖gloop L W M z (I.cutGlue (k + 1) b)‖
        ≤ η⁻¹ ^ (I.length + 1) * (W : ℝ)⁻¹ ^ I.length := by
      intro b
      have hwf' : (I.cutGlue (k + 1) b).WF :=
        LoopIdx.WF.cutGlue (b := b) (k := k + 1) hwf (by omega) (by omega)
      have hlen : (I.cutGlue (k + 1) b).a.length = I.length + 1 :=
        LoopIdx.length_cutGlue I b (by omega)
      have h := norm_gloop_le_of_le_abs_im (L := L) (W := W) (H := M) (z := z) hM hη hz
        (I.cutGlue (k + 1) b) hwf' (by rw [hlen]; omega)
      rw [hlen] at h
      simpa using h
    have h2 : ‖∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b)‖
        ≤ (Fintype.card (ZMod L) : ℝ)
            * (η⁻¹ ^ (I.length + 1) * (W : ℝ)⁻¹ ^ I.length) := by
      refine (norm_sum_le _ _).trans ?_
      have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (ZMod L))
        (fun b => ‖gloop L W M z (I.cutGlue (k + 1) b)‖)
        (η⁻¹ ^ (I.length + 1) * (W : ℝ)⁻¹ ^ I.length) (fun b _ => hb b)
      simpa [Finset.card_univ, nsmul_eq_mul] using hsum
    have h1 : ‖m (I.σ.getD k true)‖ ≤ max ‖m true‖ ‖m false‖ := by
      cases I.σ.getD k true <;> simp
    have h0 : (0 : ℝ) ≤ max ‖m true‖ ‖m false‖ := le_trans (norm_nonneg _) (le_max_left _ _)
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_natCast]
    gcongr
  have hfin := Finset.sum_le_card_nsmul (Finset.range I.length)
    (fun k => ‖(-(m (I.σ.getD k true))) *
      ((W : ℂ) * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b))‖) _ hterm
  simpa [Finset.card_range, nsmul_eq_mul] using hfin

/-- **The moving spectral parameter, in the vocabulary of (2.47).** -/
theorem hasDerivAt_gloop_zt_eGterm (hL : 3 ≤ L)
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {E w : ℝ} (hz : (zt E w).im ≠ 0) (I : LoopIdx (ZMod L)) (hwf : I.WF) :
    HasDerivAt (fun s : ℝ => gloop L W M (zt E s) I)
      (eGterm L W (mSigma E) M (zt E w) I - eGterm L W 0 M (zt E w) I) w := by
  rw [eGterm_sub_eGterm hL]
  exact hasDerivAt_gloop_zt hM hz I hwf


/-! ### The moving spectral parameter, in expectation -/

section MovingZ

/-- The `z`-motion term of a loop is a continuous function of the sample point. -/
theorem continuous_zMotion_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (m : Bool → ℂ) (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω : Ω d => zMotion (d.L N) (d.W N) m (Hflow d N u ω) z I := by
  simp only [zMotion]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact continuous_const.mul
    (continuous_finsetSum _ fun b _ => continuous_gloop_Hflow d N u hz _)

/-- The `z`-motion term is integrable along the flow. -/
theorem integrable_zMotion_Hflow (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (m : Bool → ℂ) (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) :
    Integrable (fun ω : Ω d => zMotion (d.L N) (d.W N) m (Hflow d N u ω) z I) (P d) :=
  integrable_of_continuous_of_bound
    (continuous_zMotion_Hflow d N u (abs_pos.mp (hη.trans_le hz)) m I)
    (fun ω => norm_zMotion_le (Hflow_isHermitian d N u ω) hη hz m I hwf)

/-- **Differentiating the expectation of a loop in the spectral parameter alone.**
The matrix argument is frozen at `H_u`; the derivative is the `z`-motion term, i.e. exactly
the `-m` subtraction of (2.47) (`RBM.Gauss.eGterm_sub_eGterm`). -/
theorem hasDerivAt_integral_gloop_zt (d : Dims) (N : ℕ) (u : ℝ) {E w η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hball : ∀ s ∈ Metric.ball w ε, η ≤ |(zt E s).im|)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    HasDerivAt (fun s : ℝ => ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E s) I ∂(P d))
      (∫ ω, zMotion (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E w) I ∂(P d)) w := by
  have hw : w ∈ Metric.ball w ε := Metric.mem_ball_self hε
  have hzim : ∀ s ∈ Metric.ball w ε, (zt E s).im ≠ 0 := fun s hs =>
    abs_pos.mp (hη.trans_le (hball s hs))
  refine (_root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s (ω : Ω d) => gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E s) I)
    (F' := fun s (ω : Ω d) =>
      zMotion (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E s) I)
    (bound := fun _ : Ω d => (I.length : ℝ) * (max ‖mSigma E true‖ ‖mSigma E false‖ *
      ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) *
        (η⁻¹ ^ (I.length + 1) * ((d.W N : ℝ))⁻¹ ^ I.length)))))
    (Metric.ball_mem_nhds w hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds w hε) fun s hs =>
      (continuous_gloop_Hflow d N u (hzim s hs) I).aestronglyMeasurable)
    (integrable_gloop_Hflow d N u hη (hball w hw) I hwf hn)
    (continuous_zMotion_Hflow d N u (hzim w hw) _ I).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω s hs =>
      norm_zMotion_le (Hflow_isHermitian d N u ω) hη (hball s hs) _ I hwf)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω s hs =>
      hasDerivAt_gloop_zt (Hflow_isHermitian d N u ω) (hzim s hs) I hwf)).2

end MovingZ

end LoopPath




/-! ### The diagonal chain rule and the moving-`z` hierarchy -/

section Diagonal

/-- **The two-variable chain rule along the diagonal.**  This is the step T76 recorded as
missing.  It is obtained from joint (Fréchet) differentiability and `HasFDerivAt.comp`, not
from "continuous partials ⟹ differentiable", which Mathlib does not provide. -/
theorem hasDerivAt_comp_diag {f : ℝ × ℝ → ℂ} {f' : (ℝ × ℝ) →L[ℝ] ℂ} {u : ℝ}
    (hf : HasFDerivAt f f' (u, u)) :
    HasDerivAt (fun v : ℝ => f (v, v)) (f' (1, 0) + f' (0, 1)) u := by
  have hd : HasDerivAt (fun v : ℝ => (v, v)) ((1 : ℝ), (1 : ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_id u)
  have hcomp : HasDerivAt (f ∘ fun v : ℝ => (v, v)) (f' ((1 : ℝ), (1 : ℝ))) u :=
    hf.comp_hasDerivAt_of_eq u hd rfl
  have hlin : f' ((1 : ℝ), (1 : ℝ)) = f' (1, 0) + f' (0, 1) := by
    rw [← map_add]
    norm_num
  rw [hlin] at hcomp
  simpa [Function.comp_def] using hcomp

/-- The `v`-slice of a two-variable map. -/
theorem hasDerivAt_fst_slice {f : ℝ × ℝ → ℂ} {f' : (ℝ × ℝ) →L[ℝ] ℂ} {u : ℝ}
    (hf : HasFDerivAt f f' (u, u)) :
    HasDerivAt (fun v : ℝ => f (v, u)) (f' (1, 0)) u := by
  have hd : HasDerivAt (fun v : ℝ => (v, u)) ((1 : ℝ), (0 : ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u u)
  have hcomp : HasDerivAt (f ∘ fun v : ℝ => (v, u)) (f' ((1 : ℝ), (0 : ℝ))) u :=
    hf.comp_hasDerivAt_of_eq u hd rfl
  simpa [Function.comp_def] using hcomp

/-- The `w`-slice of a two-variable map. -/
theorem hasDerivAt_snd_slice {f : ℝ × ℝ → ℂ} {f' : (ℝ × ℝ) →L[ℝ] ℂ} {u : ℝ}
    (hf : HasFDerivAt f f' (u, u)) :
    HasDerivAt (fun w : ℝ => f (u, w)) (f' (0, 1)) u := by
  have hd : HasDerivAt (fun w : ℝ => (u, w)) ((0 : ℝ), (1 : ℝ)) u :=
    (hasDerivAt_const u u).prodMk (hasDerivAt_id u)
  have hcomp : HasDerivAt (f ∘ fun w : ℝ => (u, w)) (f' ((0 : ℝ), (1 : ℝ))) u :=
    hf.comp_hasDerivAt_of_eq u hd rfl
  simpa [Function.comp_def] using hcomp

variable {d : Dims} {N : ℕ}

/-- **Lemma 2.11 in moment form, with the spectral parameter moving** — the literal
expectation of (2.45)–(2.47).

Given

* the deterministic cut-and-glue identity `RBM.Gauss.LoopIto` of T76, instantiated with the
  *frozen* `Ẽ` term `RBM.Gauss.eGterm … 0 …` (that is, (2.47) with `G` in place of `G̃`), and
* joint differentiability of `(v, w) ↦ E[L(H_v, z_w)]` at `(u,u)`,

the derivative of `u ↦ E[L_{u,σ,a}]` along the *true* flow — matrix **and** spectral
parameter both moving — is `E[Ẽ] + E[primRhs L_u]` with `Ẽ` now carrying the paper's
`G̃ = G - m` subtraction.  The `-m` is produced entirely by the motion of `z_u`
(`RBM.Gauss.eGterm_sub_eGterm`). -/
theorem hasDerivAt_integral_gloop_hierarchy_movingZ (hst : MatrixStein d)
    {E u η ε : ℝ} (hu : 0 < u) (hη : 0 < η) (hε : 0 < ε)
    (hball : ∀ s ∈ Metric.ball u ε, η ≤ |(zt E s).im|)
    (hito : LoopIto d N (zt E u))
    (hEG : ∀ M I, hito.EG M I = eGterm (d.L N) (d.W N) 0 M (zt E u) I)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (h : TestFun d N (loopObs d N (zt E u) I))
    {Ψ' : (ℝ × ℝ) →L[ℝ] ℂ}
    (hjoint : HasFDerivAt (fun p : ℝ × ℝ =>
        ∫ ω, gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I ∂(P d)) Ψ' (u, u)) :
    HasDerivAt (fun v : ℝ => ∫ ω, gloop (d.L N) (d.W N) (Hflow d N v ω) (zt E v) I ∂(P d))
      (∫ ω, (eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u) I
        + primRhs (d.L N) (d.W N)
            (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u)) I) ∂(P d)) u := by
  have hu' : u ∈ Metric.ball u ε := Metric.mem_ball_self hε
  have hzu : η ≤ |(zt E u).im| := hball u hu'
  -- the frozen-`z` half, from T71 + `LoopIto`
  have h1 := hasDerivAt_integral_gloop_hierarchy (N := N) hst hito hwf hn h hu
  have heq1 : Ψ' (1, 0)
      = ∫ ω, (hito.EG (Hflow d N u ω) I
          + primRhs (d.L N) (d.W N)
              (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u)) I) ∂(P d) :=
    HasDerivAt.unique (hasDerivAt_fst_slice hjoint) h1
  -- the `z`-motion half
  have h2 := hasDerivAt_integral_gloop_zt d N u hη hε hball I hwf hn
  have heq2 : Ψ' (0, 1)
      = ∫ ω, zMotion (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u) I ∂(P d) :=
    HasDerivAt.unique (hasDerivAt_snd_slice hjoint) h2
  -- integrability of the two summands
  have hbase : Integrable (fun ω : Ω d => (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
      Sblk (d.L N) (d.W N) i j •
        wirtSecond d N (loopObs d N (zt E u) I) (Hflow d N u ω) i j) (P d) :=
    (Integrable.smul ((1 : ℝ) / 2)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (Integrable.smul (Sblk (d.L N) (d.W N) i j) (integrable_wirtSecond h u i j) :
          Integrable (fun ω : Ω d => Sblk (d.L N) (d.W N) i j •
            wirtSecond d N (loopObs d N (zt E u) I) (Hflow d N u ω) i j) (P d))) :
      Integrable (fun ω : Ω d => (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
        Sblk (d.L N) (d.W N) i j •
          wirtSecond d N (loopObs d N (zt E u) I) (Hflow d N u ω) i j) (P d))
  have hfint : Integrable (fun ω : Ω d => hito.EG (Hflow d N u ω) I
      + primRhs (d.L N) (d.W N)
          (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u)) I) (P d) :=
    hbase.congr (Filter.Eventually.of_forall fun ω =>
      hito.second _ (Hflow_isHermitian d N u ω) I hwf hn)
  have hgint : Integrable (fun ω : Ω d =>
      zMotion (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u) I) (P d) :=
    integrable_zMotion_Hflow d N u hη hzu _ I hwf
  -- assemble
  have hdiag := hasDerivAt_comp_diag hjoint
  refine hdiag.congr_deriv ?_
  rw [heq1, heq2, ← integral_add hfint hgint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hz := eGterm_sub_eGterm (L := d.L N) (W := d.W N) (d.three_le_L N) (mSigma E)
    (Hflow d N u ω) (zt E u) I
  simp only [hEG, ← hz]
  ring


/-- **The moving-`z` hierarchy in the vocabulary of `RBM1D/Flow/Hypotheses.lean`.**

Unlike `RBM.Gauss.hasDerivAt_integral_Lval_hierarchy`, whose differentiated function agrees
with `RBM.Sample.ELval` only *at the base point*, the function differentiated here **is**
`v ↦ E L_{v,σ,a}`: both the matrix and the spectral parameter move.  This closes the
"spectral parameter is frozen" deviation of T76 (paper-deltas #52), at the price of the
joint-differentiability input `hjoint`. -/
theorem hasDerivAt_sample_ELval_hierarchy (hst : MatrixStein d)
    {E u η ε : ℝ} (hu : 0 < u) (hη : 0 < η) (hε : 0 < ε)
    (hball : ∀ s ∈ Metric.ball u ε, η ≤ |(zt E s).im|)
    (hito : LoopIto d N (zt E u))
    (hEG : ∀ M I, hito.EG M I = eGterm (d.L N) (d.W N) 0 M (zt E u) I)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (h : TestFun d N (loopObs d N (zt E u) I))
    {Ψ' : (ℝ × ℝ) →L[ℝ] ℂ}
    (hjoint : HasFDerivAt (fun p : ℝ × ℝ =>
        ∫ ω, gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I ∂(P d)) Ψ' (u, u)) :
    HasDerivAt (fun v : ℝ => (sample d).ELval E N v I)
      (∫ ω, (eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u) I
        + primRhs (d.L N) (d.W N) ((sample d).Lval E N u ω) I) ∂(P d)) u :=
  hasDerivAt_integral_gloop_hierarchy_movingZ hst hu hη hε hball hito hEG hwf hn h hjoint

end Diagonal



/-! ### Joint smoothness in `(u, z)` -/

section JointSmooth

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The resolvent is jointly smooth in its two arguments**, by *composition*: `v ↦ A v - ζ v`
is `C^k` and `Ring.inverse` is `C^k` at every unit (`contDiffAt_ringInverse`).  This is the
route T134 takes instead of "continuous partials ⟹ differentiable", which Mathlib lacks. -/
theorem contDiffAt_green_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : V → Matrix n n ℂ} {ζ : V → ℂ} {x : V} {k : WithTop ℕ∞}
    (hA : ContDiffAt ℝ k A x) (hζ : ContDiffAt ℝ k ζ x)
    (hU : IsUnit (A x - ζ x • (1 : Matrix n n ℂ))) :
    ContDiffAt ℝ k (fun v => green (A v) (ζ v)) x := by
  have hsub : ContDiffAt ℝ k (fun v => A v - ζ v • (1 : Matrix n n ℂ)) x :=
    hA.sub (hζ.smul contDiffAt_const)
  have hinv : ContDiffAt ℝ k (Ring.inverse (M₀ := Matrix n n ℂ))
      (A x - ζ x • (1 : Matrix n n ℂ)) := by
    have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := k) hU.unit
    rwa [IsUnit.unit_spec] at h
  have hcomp := hinv.comp x hsub
  have hfun : (fun v => green (A v) (ζ v))
      = (Ring.inverse (M₀ := Matrix n n ℂ)) ∘ fun v => A v - ζ v • (1 : Matrix n n ℂ) := by
    funext v
    simp [green, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  exact hcomp

/-- `(v, w) ↦ G(σ)(H_v, z_w)` is `C^k` at `(u, u)` for `u > 0`. -/
theorem contDiffAt_Gsig_flow (d : Dims) (N : ℕ) (ω : Ω d) {E u : ℝ} {k : WithTop ℕ∞}
    (hu : 0 < u) (hz : (zt E u).im ≠ 0) (σ : Bool) :
    ContDiffAt ℝ k (fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt E p.2) σ) (u, u) := by
  have hsq : ContDiffAt ℝ k (fun p : ℝ × ℝ => Real.sqrt p.1) (u, u) :=
    (Real.contDiffAt_sqrt hu.ne').comp (u, u) contDiff_fst.contDiffAt
  have hflow : ContDiffAt ℝ k (fun p : ℝ × ℝ => Hflow d N p.1 ω) (u, u) := by
    have h := hsq.smul (contDiffAt_const (c := Xmat d N ω) (x := ((u : ℝ), (u : ℝ))))
    have heq : ((fun p : ℝ × ℝ => Real.sqrt p.1) • fun _ : ℝ × ℝ => Xmat d N ω)
        = fun p : ℝ × ℝ => Hflow d N p.1 ω := by
      funext p
      show Real.sqrt p.1 • Xmat d N ω = Hflow d N p.1 ω
      rw [Hflow_eq_realSmul]
    rwa [heq] at h
  have hre : ContDiffAt ℝ k (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) (u, u) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (u, u) contDiff_snd.contDiffAt
  have hzeta : ContDiffAt ℝ k
      (fun p : ℝ × ℝ => (E : ℂ) + (1 - ((p.2 : ℝ) : ℂ)) * mSigma E σ) (u, u) :=
    contDiffAt_const.add ((contDiffAt_const.sub hre).mul contDiffAt_const)
  have hU : IsUnit (Hflow d N u ω
      - ((E : ℂ) + (1 - (u : ℂ)) * mSigma E σ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (Hflow_isHermitian d N u ω) (ztSig_im_ne_zero hz σ)
  have h := contDiffAt_green_comp hflow hzeta hU
  simpa only [← Gsig_zt] using h

/-- `(v, w) ↦ ∏_i G(σ_i)(H_v, z_w) E_{a_i}` is `C^k` at `(u, u)`. -/
theorem contDiffAt_gloopProd_flow (d : Dims) (N : ℕ) (ω : Ω d) {E u : ℝ} {k : WithTop ℕ∞}
    (hu : 0 < u) (hz : (zt E u).im ≠ 0) :
    ∀ (σ : List Bool) (a : List (ZMod (d.L N))),
      ContDiffAt ℝ k (fun p : ℝ × ℝ =>
        gloopProd (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) ⟨σ, a⟩) (u, u) := by
  intro σ
  induction σ with
  | nil => intro a; exact contDiffAt_const
  | cons σ₀ σ ih =>
      intro a
      cases a with
      | nil => exact contDiffAt_const
      | cons c a' =>
          have hfun : (fun p : ℝ × ℝ => gloopProd (d.L N) (d.W N) (Hflow d N p.1 ω)
                (zt E p.2) (⟨σ₀ :: σ, c :: a'⟩ : LoopIdx (ZMod (d.L N))))
              = fun p : ℝ × ℝ => Gsig (Hflow d N p.1 ω) (zt E p.2) σ₀
                  * Eblk (d.L N) (d.W N) c
                  * gloopProd (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) ⟨σ, a'⟩ := rfl
          rw [hfun]
          exact ((contDiffAt_Gsig_flow d N ω hu hz σ₀).mul
            contDiffAt_const).mul (ih a')

/-- **The loop observable is jointly `C^k` in the flow time and the spectral time.**
The `HasFDerivAt` this yields at `(u, u)` is the pointwise half of the moving-`z` chain rule;
what is still needed to differentiate the *expectation* jointly is a dominating bound on the
joint derivative (the `TestFun` gap, T133). -/
theorem contDiffAt_gloop_flow (d : Dims) (N : ℕ) (ω : Ω d) {E u : ℝ} {k : WithTop ℕ∞}
    (hu : 0 < u) (hz : (zt E u).im ≠ 0) (I : LoopIdx (ZMod (d.L N))) :
    ContDiffAt ℝ k (fun p : ℝ × ℝ =>
      gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I) (u, u) := by
  set T : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (d.Idx N) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hT : ∀ X, T X = Matrix.trace X := fun _ => rfl
  have hfun : (fun p : ℝ × ℝ => gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I)
      = T ∘ fun p : ℝ × ℝ =>
        gloopProd (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I := rfl
  rw [hfun]
  exact (T.contDiff (n := k)).contDiffAt.comp (u, u)
    (contDiffAt_gloopProd_flow d N ω hu hz I.σ I.a)

/-- The pointwise joint derivative, the form the parametric-integral lemmas consume. -/
theorem differentiableAt_gloop_flow (d : Dims) (N : ℕ) (ω : Ω d) {E u : ℝ}
    (hu : 0 < u) (hz : (zt E u).im ≠ 0) (I : LoopIdx (ZMod (d.L N))) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ =>
      gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I) (u, u) :=
  (contDiffAt_gloop_flow (k := 1) d N ω hu hz I).differentiableAt one_ne_zero

end JointSmooth

/-! ### The drift of `L - K`: (5.12)-(5.15) -/

section Drift

/-- **The pointwise drift identity for a loop.**  Adding the `z`-motion to the frozen
second-order term of `RBM.Gauss.LoopIto` turns the `Ẽ` term into the paper's (2.47), with
`G̃ = G - m`:

`(∂_u + 𝓛) L_{σ,a} = Ẽ_{σ,a} + W ∑_{k<l} (G^L ∘ L) S^(B) (G^R ∘ L)`.

Here `𝓛` is the second-order operator `½ ∑_{ij} S_ij ∂_ij ∂_ji` of T71's generator identity
and `∂_u` is the motion of the spectral parameter; the identity holds at every Hermitian
matrix, with no expectation taken. -/
theorem generator_add_zMotion {d : Dims} {N : ℕ} {E u : ℝ} (hito : LoopIto d N (zt E u))
    (hEG : ∀ M I, hito.EG M I = eGterm (d.L N) (d.W N) 0 M (zt E u) I)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          wirtSecond d N (loopObs d N (zt E u) I) M i j
        + zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I
      = eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
        + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M (zt E u)) I := by
  have hz := eGterm_sub_eGterm (L := d.L N) (W := d.W N) (d.three_le_L N) (mSigma E) M
    (zt E u) I
  rw [hito.second M hM I hwf hn, hEG, ← hz]
  ring

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero W] in
/-- **(5.12)-(5.14) as a derivative statement.**  If a loop function obeys the hierarchy
`∂_u L = Ẽ + primRhs L` and the primitive `K` obeys (2.48), then the difference obeys

`∂_u (L - K) = Ẽ + [K ~ (L-K)] + E^{((L-K)×(L-K))}`,

the coupling `[K ~ (L-K)] = primBil K (L-K) + primBil (L-K) K` being the linear part whose
`l_K = 2` grading (`RBM.primBilLen`) is what (5.19) identifies with the generator
`Theta_{t,sigma}`.  Nothing here is stochastic: the quadratic terms of the two equations are
the *same* bilinear form, which is why they polarize. -/
theorem hasDerivAt_sub_prim {Lf K : ℝ → LoopIdx (ZMod L) → ℂ} {u : ℝ}
    {I : LoopIdx (ZMod L)} {EG : ℂ}
    (hLf : HasDerivAt (fun v : ℝ => Lf v I) (EG + primRhs L W (Lf u) I) u)
    (hK : HasDerivAt (fun v : ℝ => K v I) (primRhs L W (K u) I) u) :
    HasDerivAt (fun v : ℝ => Lf v I - K v I)
      (EG + (primBil L W (K u) (Lf u - K u) I + primBil L W (Lf u - K u) (K u) I
        + primBil L W (Lf u - K u) (Lf u - K u) I)) u := by
  refine (hLf.sub hK).congr_deriv ?_
  rw [← primRhs_sub L W (Lf u) (K u) I]
  ring

omit [NeZero W] in
/-- The same, taking the primitive equation from `RBM.IsPrimitive` (Definition 2.12). -/
theorem hasDerivAt_sub_prim_of_isPrimitive {Lf K : ℝ → LoopIdx (ZMod L) → ℂ} {m : Bool → ℂ}
    {T : Set ℝ} {u : ℝ} (hu : u ∈ T) (hprim : IsPrimitive L W m T K)
    {I : LoopIdx (ZMod L)} (hwf : I.WF) (h2 : 2 ≤ I.length) {EG : ℂ}
    (hLf : HasDerivAt (fun v : ℝ => Lf v I) (EG + primRhs L W (Lf u) I) u) :
    HasDerivAt (fun v : ℝ => Lf v I - K v I)
      (EG + (primBil L W (K u) (Lf u - K u) I + primBil L W (Lf u - K u) (K u) I
        + primBil L W (Lf u - K u) (Lf u - K u) I)) u :=
  hasDerivAt_sub_prim L W hLf (hprim.1 u hu I hwf h2)

end Drift


/-! ### The variance contraction of the generator on a `tr(A B C B)` pattern -/

section Contraction

variable {d : Dims} {N : ℕ}


/-! #### The elementary trace identity

`tr(A E_pq C E_rs) = A_{sp} C_{qr}`, with the two scalar weights pulled out. -/

/-- `tr(A · (c·E_pq) · C · (e·E_rs)) = c e A_{sp} C_{qr}`. -/
theorem traceBB_trace_single_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℂ) (p q r s : ι) (c e : ℂ) :
    Matrix.trace (A * Matrix.single p q c * C * Matrix.single r s e)
      = c * e * (A s p * C q r) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  ring

/-! #### The two shapes of `Bmat` -/

/-- On the diagonal `Bmat d N i i b` is a *single* elementary matrix: `E_ii` for the real tag
and `I·E_ii` for the imaginary tag.  (The `else` branch of `Bmat` is unreachable at `i = j`.) -/
theorem traceBB_Bmat_diag (i : d.Idx N) (b : Bool) :
    Bmat d N i i b = Matrix.single i i (if b then 1 else Complex.I) := by
  ext k l
  rw [Bmat_apply, Matrix.single_apply]
  by_cases h : k = i ∧ l = i
  · simp [h.1, h.2]
  · have e : ¬ (i = k ∧ i = l) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
    simp [h, e]

/-- Off the diagonal `Bmat d N i j b` splits as a sum of two elementary matrices. -/
theorem traceBB_Bmat_eq_add {i j : d.Idx N} (hij : i ≠ j) (b : Bool) :
    Bmat d N i j b
      = Matrix.single i j (if b then 1 else Complex.I)
        + Matrix.single j i (if b then 1 else -Complex.I) := by
  ext k l
  rw [Bmat_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : k = i ∧ l = j
  · obtain ⟨hk, hl⟩ := h1
    simp [hk, hl, hij, Ne.symm hij]
  · by_cases h2 : k = j ∧ l = i
    · obtain ⟨hk, hl⟩ := h2
      simp [hk, hl, hij, Ne.symm hij]
    · have e1 : ¬ (i = k ∧ j = l) := fun hh => h1 ⟨hh.1.symm, hh.2.symm⟩
      have e2 : ¬ (j = k ∧ i = l) := fun hh => h2 ⟨hh.1.symm, hh.2.symm⟩
      simp [h1, h2, e1, e2]

/-- `B^{(t)}_{ij} = E_ij + E_ji` for `i ≠ j`. -/
theorem traceBB_Bmat_true_eq {i j : d.Idx N} (hij : i ≠ j) :
    Bmat d N i j true = Matrix.single i j 1 + Matrix.single j i 1 := by
  rw [traceBB_Bmat_eq_add hij true]; simp

/-- `B^{(f)}_{ij} = I·E_ij − I·E_ji` for `i ≠ j`. -/
theorem traceBB_Bmat_false_eq {i j : d.Idx N} (hij : i ≠ j) :
    Bmat d N i j false
      = Matrix.single i j Complex.I + Matrix.single j i (-Complex.I) := by
  rw [traceBB_Bmat_eq_add hij false]; simp

/-! #### The two trace patterns

Note the hypothesis `i ≠ j` in `traceBB_true` / `traceBB_false`: on the diagonal `Bmat` is
`E_ii` (resp. `I·E_ii`), *not* `E_ii + E_ii`, so the four-term formulas below genuinely fail
at `i = j`.  The diagonal case is `traceBB_diag_true`, and the combination that the Wirtinger
second derivative actually uses (`traceBB_wirtPair`) is uniform in `i, j`. -/

/-- `tr(A B^{(t)}_{ij} C B^{(t)}_{ij}) = A_{ji}C_{ji} + A_{ii}C_{jj} + A_{jj}C_{ii} + A_{ij}C_{ij}`
for `i ≠ j`. -/
theorem traceBB_true (A C : Matrix (d.Idx N) (d.Idx N) ℂ) {i j : d.Idx N} (hij : i ≠ j) :
    Matrix.trace (A * Bmat d N i j true * C * Bmat d N i j true)
      = A j i * C j i + A i i * C j j + A j j * C i i + A i j * C i j := by
  rw [traceBB_Bmat_true_eq hij]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    traceBB_trace_single_mul_single]
  ring

/-- `tr(A B^{(f)}_{ij} C B^{(f)}_{ij}) = −A_{ji}C_{ji} + A_{ii}C_{jj} + A_{jj}C_{ii} − A_{ij}C_{ij}`
for `i ≠ j`. -/
theorem traceBB_false (A C : Matrix (d.Idx N) (d.Idx N) ℂ) {i j : d.Idx N} (hij : i ≠ j) :
    Matrix.trace (A * Bmat d N i j false * C * Bmat d N i j false)
      = -(A j i * C j i) + A i i * C j j + A j j * C i i - A i j * C i j := by
  rw [traceBB_Bmat_false_eq hij]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    traceBB_trace_single_mul_single]
  linear_combination
    (A j i * C j i - A i i * C j j - A j j * C i i + A i j * C i j) * Complex.I_mul_I

/-- The diagonal case: `tr(A E_ii C E_ii) = A_{ii} C_{ii}`. -/
theorem traceBB_diag_true (A C : Matrix (d.Idx N) (d.Idx N) ℂ) (i : d.Idx N) :
    Matrix.trace (A * Bmat d N i i true * C * Bmat d N i i true) = A i i * C i i := by
  rw [traceBB_Bmat_diag, traceBB_trace_single_mul_single]
  norm_num

/-! #### The Wirtinger pattern -/

/-- **The `wirtSecond` pattern on a trace of shape `tr(A · B · C · B)`.**  Uniformly in `i, j`
(diagonal included) the Wirtinger combination collapses to `(A_{ii}C_{jj} + A_{jj}C_{ii})/2`. -/
theorem traceBB_wirtPair (A C : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    (if i = j then Matrix.trace (A * Bmat d N i i true * C * Bmat d N i i true)
     else (1/4 : ℝ) • (Matrix.trace (A * Bmat d N i j true * C * Bmat d N i j true)
                      + Matrix.trace (A * Bmat d N i j false * C * Bmat d N i j false)))
      = (A i i * C j j + A j j * C i i) / 2 := by
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, traceBB_diag_true]
    ring
  · rw [ite_eq_right h, traceBB_true A C h, traceBB_false A C h, Complex.real_smul]
    push_cast
    ring

/-! #### The contraction against the variance profile -/

/-- `⟨A E_a⟩ = W⁻¹ ∑_α A_{(a,α),(a,α)}`. -/
theorem sumSblk_trace_mul_Eblk (A : Matrix (d.Idx N) (d.Idx N) ℂ) (a : ZMod (d.L N)) :
    Matrix.trace (A * Eblk (d.L N) (d.W N) a)
      = (d.W N : ℂ)⁻¹ * ∑ α : Fin (d.W N), A (a, α) (a, α) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Eblk, Matrix.mul_diagonal]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', Finset.mul_sum, mul_comm]

/-- The variance profile is symmetric. -/
theorem sumSblk_symm (L W : ℕ) (i j : ZMod L × Fin W) :
    Sblk L W i j = Sblk L W j i := by
  rw [Sblk, Sblk, ← sbKre_neg (i.1 - j.1), neg_sub]

/-- **The block collapse of the diagonal contraction.**  `S_{ij}` depends only on the blocks of
`i` and `j`, so `∑_{ij} S_{ij} A_{ii} C_{jj}` is a `S^{(B)}`-weighted sum of block averages. -/
theorem sumSblk_diag_mul (A C : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ) * (A i i * C j j)
      = (d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
          Matrix.trace (A * Eblk (d.L N) (d.W N) a) * SB (d.L N) a b
            * Matrix.trace (C * Eblk (d.L N) (d.W N) b) := by
  have hW : (d.W N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (d.W_pos N).ne'
  have expand : ∀ (c : ℂ) (f g : Fin (d.W N) → ℂ),
      ∑ α, ∑ β, c * (f α * g β) = c * ((∑ α, f α) * (∑ β, g β)) := by
    intro c f g
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
  simp only [sumSblk_trace_mul_Eblk, SB_eq_ofReal, Sblk, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  rw [expand]
  field_simp

/-- **The assembled variance contraction.**  The `½ ∑_{ij} S_{ij} ∂_ij ∂_ji` pattern of the
generator, applied to a trace of shape `tr(A · B_{ij} · C · B_{ij})`, is the block bilinear form
`½ W ∑_{ab} ⟨A E_a⟩ S^{(B)}_{ab} ⟨C E_b⟩`. -/
theorem sumSblk_half_wirtPair (A C : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (1/2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        (if i = j then Matrix.trace (A * Bmat d N i i true * C * Bmat d N i i true)
         else (1/4 : ℝ) • (Matrix.trace (A * Bmat d N i j true * C * Bmat d N i j true)
                          + Matrix.trace (A * Bmat d N i j false * C * Bmat d N i j false)))
      = (1/2 : ℂ) * ((d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
            Matrix.trace (A * Eblk (d.L N) (d.W N) a) * SB (d.L N) a b
              * Matrix.trace (C * Eblk (d.L N) (d.W N) b)) := by
  have h1 : ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ) * (A j j * C i i)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ) * (A i i * C j j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sumSblk_symm]
  have e : ∀ i j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ)
        * ((A i i * C j j + A j j * C i i) / 2)
      = ((Sblk (d.L N) (d.W N) i j : ℂ) * (A i i * C j j)) / 2
        + ((Sblk (d.L N) (d.W N) i j : ℂ) * (A j j * C i i)) / 2 := by
    intro i j; ring
  have key : ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ)
        * ((A i i * C j j + A j j * C i i) / 2)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, (Sblk (d.L N) (d.W N) i j : ℂ) * (A i i * C j j) := by
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [h1]
    ring
  rw [← sumSblk_diag_mul A C, ← key]
  simp only [traceBB_wirtPair]
  simp only [Complex.real_smul]
  push_cast
  ring

end Contraction

/-! ### The loop product with inserted matrices, and its matrix derivatives -/

section GprodM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The loop product with **arbitrary inserted matrices**: `∏_i G(σ_i) A_i`. -/
noncomputable def gprodM (z : ℂ)
    (l : List (Bool × Matrix n n ℂ)) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  l.foldr (fun p X => Gsig M z p.1 * p.2 * X) 1

@[simp] theorem gprodM_nil (z : ℂ) (M : Matrix n n ℂ) :
    gprodM z ([] : List (Bool × Matrix n n ℂ)) M = 1 := rfl

@[simp] theorem gprodM_cons (z : ℂ) (p : Bool × Matrix n n ℂ) (l : List (Bool × Matrix n n ℂ))
    (M : Matrix n n ℂ) :
    gprodM z (p :: l) M = Gsig M z p.1 * p.2 * gprodM z l M := rfl

/-- Insert `B` just before the `k`-th factor, duplicating its charge. -/
def insB (B : Matrix n n ℂ) (k : ℕ) (l : List (Bool × Matrix n n ℂ)) :
    List (Bool × Matrix n n ℂ) :=
  l.take k ++ ((l.getD k (true, 0)).1, B) :: l.drop k

omit [Fintype n] [DecidableEq n] in
@[simp] theorem insB_zero_cons (B : Matrix n n ℂ) (p : Bool × Matrix n n ℂ)
    (l : List (Bool × Matrix n n ℂ)) :
    insB B 0 (p :: l) = (p.1, B) :: p :: l := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem insB_succ_cons (B : Matrix n n ℂ) (k : ℕ) (p : Bool × Matrix n n ℂ)
    (l : List (Bool × Matrix n n ℂ)) :
    insB B (k + 1) (p :: l) = p :: insB B k l := rfl

omit [Fintype n] [DecidableEq n] in
theorem length_insB (B : Matrix n n ℂ) {k : ℕ} {l : List (Bool × Matrix n n ℂ)}
    (hk : k ≤ l.length) : (insB B k l).length = l.length + 1 := by
  simp only [insB, List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

end GprodM

section Bridge

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
/-- `gprodM` with the inserted matrices read off the loop index is the loop product. -/
theorem gprodM_zip_map_eq_gloopProd
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) :
    gprodM z (I.σ.zip (I.a.map (Eblk L W))) M = gloopProd L W M z I := by
  obtain ⟨σ, a⟩ := I
  show gprodM z (σ.zip (a.map (Eblk L W))) M
    = (σ.zip a).foldr (fun p X => Gsig M z p.1 * Eblk L W p.2 * X) 1
  induction σ generalizing a with
  | nil => rfl
  | cons s σ ih =>
      cases a with
      | nil => rfl
      | cons b a =>
          simp only [List.map_cons, List.zip_cons_cons, List.foldr_cons, gprodM_cons]
          rw [ih a]

end Bridge

section HermLine

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- `M + t • B` is Hermitian when `M` and `B` are and `t` is real. -/
theorem isHermitian_add_smul {M B : Matrix n n ℂ} (hM : M.IsHermitian) (hB : B.IsHermitian)
    (t : ℝ) : (M + t • B).IsHermitian := by
  show (M + t • B)ᴴ = M + t • B
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, hM.eq, hB.eq]

/-- The `σ`-charged spectral parameter has nonzero imaginary part. -/
theorem im_charge_ne_zero {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
  cases σ <;> simpa using hz

/-- **The resolvent moves with the matrix.**  `∂_s G(σ)(M + s B) = -G(σ) B G(σ)`. -/
theorem hasDerivAt_Gsig_dir {M B : Matrix n n ℂ} (hM : M.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gsig (M + s • B) z σ)
      (-(Gsig (M + t • B) z σ * B * Gsig (M + t • B) z σ)) t := by
  set ζ : ℂ := if σ then z else (starRingEnd ℂ) z with hζ
  have hU : IsUnit ((M + t • B) - ζ • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_smul hM hB t) (im_charge_ne_zero hz σ)
  set U : (Matrix n n ℂ)ˣ := hU.unit with hUdef
  have hus : (U : Matrix n n ℂ) = (M + t • B) - ζ • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have hinv : ((U⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = Gsig (M + t • B) z σ := by
    rw [Gsig, ← hζ, green, Matrix.nonsing_inv_eq_ringInverse, ← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
      ((M + t • B) - ζ • (1 : Matrix n n ℂ)) := by
    rw [← hus]; exact hasFDerivAt_ringInverse U
  have hline : HasDerivAt (fun s : ℝ => M + s • B) B t := by
    simpa using ((hasDerivAt_id t).smul_const B).const_add M
  have hpath : HasDerivAt (fun s : ℝ => (M + s • B) - ζ • (1 : Matrix n n ℂ)) B t :=
    hline.sub_const _
  have hcomp := hF.comp_hasDerivAt t hpath
  have hval : (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹) B
      = -(Gsig (M + t • B) z σ * B * Gsig (M + t • B) z σ) := by
    simp [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinv]
  rw [hval] at hcomp
  have hfun : (fun s : ℝ => Gsig (M + s • B) z σ)
      = (Ring.inverse (M₀ := Matrix n n ℂ))
          ∘ (fun s : ℝ => (M + s • B) - ζ • (1 : Matrix n n ℂ)) := by
    funext s
    simp [Gsig, ← hζ, green, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  exact hcomp

/-- **The first derivative of the loop product in the matrix argument.**  Leibniz over the
factors: the `k`-th summand is the product with `G(σ_k)` replaced by `G(σ_k) B G(σ_k)`,
which is `gprodM z (insB B k l)`. -/
theorem hasDerivAt_gprodM {M B : Matrix n n ℂ} (hM : M.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Matrix n n ℂ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gprodM z l (M + s • B))
      (-(∑ k ∈ Finset.range l.length, gprodM z (insB B k l) (M + t • B))) t := by
  induction l with
  | nil => simpa using hasDerivAt_const t (1 : Matrix n n ℂ)
  | cons p l ih =>
      have hG := hasDerivAt_Gsig_dir hM hB hz p.1 t
      have hfun : (fun s : ℝ => gprodM z (p :: l) (M + s • B))
          = fun s : ℝ => (Gsig (M + s • B) z p.1 * p.2) * gprodM z l (M + s • B) := by
        funext s; simp [gprodM_cons]
      rw [hfun]
      refine HasDerivAt.congr_deriv ((hG.mul_const p.2).mul ih) ?_
      set G := Gsig (M + t • B) z p.1
      set P := gprodM z l (M + t • B)
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [insB_zero_cons, insB_succ_cons, gprodM_cons]
      have htail : ∑ k ∈ Finset.range l.length,
            G * p.2 * gprodM z (insB B k l) (M + t • B)
          = G * p.2 * ∑ k ∈ Finset.range l.length, gprodM z (insB B k l) (M + t • B) := by
        rw [Finset.mul_sum]
      rw [htail]
      simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_add]
      abel

/-- **The second derivative**, obtained by differentiating each summand of the first. -/
theorem hasDerivAt_gprodM_second {M B : Matrix n n ℂ} (hM : M.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (l : List (Bool × Matrix n n ℂ)) :
    HasDerivAt (fun s : ℝ => -(∑ k ∈ Finset.range l.length, gprodM z (insB B k l) (M + s • B)))
      (∑ k ∈ Finset.range l.length, ∑ j ∈ Finset.range (l.length + 1),
          gprodM z (insB B j (insB B k l)) M) 0 := by
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ k ∈ Finset.range l.length, gprodM z (insB B k l) (M + s • B))
      (∑ k ∈ Finset.range l.length,
        -(∑ j ∈ Finset.range (insB B k l).length,
          gprodM z (insB B j (insB B k l)) (M + (0 : ℝ) • B))) 0 :=
    HasDerivAt.fun_sum fun k _ => hasDerivAt_gprodM hM hB hz (insB B k l) 0
  have hlen : ∀ k ∈ Finset.range l.length, (insB B k l).length = l.length + 1 := by
    intro k hk
    exact length_insB B (le_of_lt (Finset.mem_range.mp hk))
  have := hsum.neg
  refine HasDerivAt.congr_deriv this ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [neg_neg, hlen k hk]
  simp

end HermLine

section CoordD2

/-- **The second coordinate derivative of the loop observable**, as a double sum of loop
products with `B = Bmat` inserted twice. -/
theorem coordD2_loopObs_eq {d : Dims} {N : ℕ} {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hC : ContDiff ℝ 2 (loopObs d N z I)) (hM : M.IsHermitian) (hz : z.im ≠ 0)
    (hwf : I.WF) (i j : d.Idx N) (b : Bool) (hB : (Bmat d N i j b).IsHermitian) :
    coordD2 d N (loopObs d N z I) M (i, j, b)
      = ∑ k ∈ Finset.range I.a.length, ∑ jj ∈ Finset.range (I.a.length + 1),
          Matrix.trace (gprodM z (insB (Bmat d N i j b) jj (insB (Bmat d N i j b) k
            (I.σ.zip (I.a.map (Eblk (d.L N) (d.W N)))))) M) := by
  set Bm := Bmat d N i j b with hBm
  set l0 := I.σ.zip (I.a.map (Eblk (d.L N) (d.W N))) with hl0
  have hlen : l0.length = I.a.length := by
    rw [hl0, List.length_zip, List.length_map, hwf]
    omega
  have hfd : FiniteDimensional ℝ (Matrix (d.Idx N) (d.Idx N) ℂ) := by infer_instance
  set T : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (d.Idx N) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hTapp : ∀ X, T X = Matrix.trace X := fun _ => rfl
  -- the observable along the line is the traced loop product
  have hloop : (fun s : ℝ => loopObs d N z I (M + s • Bm))
      = fun s : ℝ => Matrix.trace (gprodM z l0 (M + s • Bm)) := by
    funext s
    rw [loopObs_of_isHermitian (isHermitian_add_smul hM hB s), gloop,
      ← gprodM_zip_map_eq_gloopProd]
  -- first derivative, identified with the `fderiv`
  have hfd1 : ∀ t : ℝ, fderiv ℝ (loopObs d N z I) (M + t • Bm) Bm
      = Matrix.trace (-(∑ k ∈ Finset.range l0.length, gprodM z (insB Bm k l0) (M + t • Bm))) := by
    intro t
    have ha : HasDerivAt (fun s : ℝ => loopObs d N z I (M + s • Bm))
        (fderiv ℝ (loopObs d N z I) (M + t • Bm) Bm) t :=
      hasDerivAt_dir (hC.of_le (by norm_num)) M Bm t
    have hb : HasDerivAt (fun s : ℝ => Matrix.trace (gprodM z l0 (M + s • Bm)))
        (Matrix.trace (-(∑ k ∈ Finset.range l0.length,
          gprodM z (insB Bm k l0) (M + t • Bm)))) t := by
      have h := T.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_gprodM hM hB hz l0 t)
      simpa only [hTapp, Function.comp_def] using h
    rw [hloop] at ha
    exact ha.unique hb
  -- second derivative
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ (loopObs d N z I) (M + t • Bm) Bm)
      (fderiv ℝ (fderiv ℝ (loopObs d N z I)) M Bm Bm) 0 := hasDerivAt_dir2' hC M Bm Bm
  have hrw : (fun t : ℝ => fderiv ℝ (loopObs d N z I) (M + t • Bm) Bm)
      = fun t : ℝ => Matrix.trace
          (-(∑ k ∈ Finset.range l0.length, gprodM z (insB Bm k l0) (M + t • Bm))) := by
    funext t; exact hfd1 t
  rw [hrw] at h2
  have h3 : HasDerivAt (fun t : ℝ => Matrix.trace
        (-(∑ k ∈ Finset.range l0.length, gprodM z (insB Bm k l0) (M + t • Bm))))
      (Matrix.trace (∑ k ∈ Finset.range l0.length, ∑ jj ∈ Finset.range (l0.length + 1),
        gprodM z (insB Bm jj (insB Bm k l0)) M)) 0 := by
    have h := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_gprodM_second hM hB hz l0)
    simpa only [hTapp, Function.comp_def] using h
  have hkey := h2.unique h3
  have hgoal : coordD2 d N (loopObs d N z I) M (i, j, b)
      = (fderiv ℝ (fderiv ℝ (loopObs d N z I)) M) Bm Bm := rfl
  rw [hgoal, hkey, hlen]
  simp only [Matrix.trace_sum]

end CoordD2

/-! ### (5.19): the `l_K = 2` coupling is the generator `Theta_{t,sigma}` -/

section Eq519

variable {L : ℕ} [NeZero L]


theorem take_one_drop {α : Type*} (l : List α) (d : α) {m : ℕ} (h : m < l.length) :
    (l.drop m).take 1 = [l.getD m d] := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
  rfl

theorem take_two_drop {α : Type*} (l : List α) (d : α) {m m' : ℕ} (hm : m + 1 = m')
    (h : m' < l.length) : (l.drop m).take 2 = [l.getD m d, l.getD m' d] := by
  subst hm
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h]
  rfl

theorem drop_last {α : Type*} (l : List α) (d : α) {m : ℕ} (h : m + 1 = l.length) :
    l.drop m = [l.getD m d] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega),
    List.getD_eq_getElem _ _ (by omega)]

omit [NeZero L] in
theorem cutGlueL_succ_eq (I : LoopIdx (ZMod L)) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k + 1 ≤ I.length) (a : ZMod L) :
    I.cutGlueL k (k + 1) a = ⟨I.σ, I.a.set (k - 1) a⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hkm : k - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · show I.σ.take k ++ I.σ.drop (k + 1 - 1) = I.σ
    simp
  · show I.a.take (k - 1) ++ a :: I.a.drop (k + 1 - 1) = I.a.set (k - 1) a
    rw [List.set_eq_take_cons_drop a hkm, show k + 1 - 1 = k - 1 + 1 by omega]

omit [NeZero L] in
theorem cutGlueR_succ_eq (I : LoopIdx (ZMod L)) (hwf : I.WF) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k + 1 ≤ I.length) (b : ZMod L) :
    I.cutGlueR k (k + 1) b
      = ⟨[I.σ.getD (k - 1) true, I.σ.getD k true], [I.a.getD (k - 1) 0, b]⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have h2 : k < I.σ.length := by rw [hσ]; omega
  have h1' : k - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · show (I.σ.drop (k - 1)).take (k + 1 - k + 1) = _
    rw [show k + 1 - k + 1 = 2 by omega, take_two_drop I.σ true (by omega : k - 1 + 1 = k) h2]
  · show (I.a.drop (k - 1)).take (k + 1 - k) ++ [b] = _
    rw [show k + 1 - k = 1 by omega, take_one_drop I.a 0 h1']
    rfl

omit [NeZero L] in
theorem cutGlueL_one_eq (I : LoopIdx (ZMod L)) (hwf : I.WF) (hn : 2 ≤ I.length) (a : ZMod L) :
    I.cutGlueL 1 I.length a
      = ⟨[I.σ.getD 0 true, I.σ.getD (I.length - 1) true], [a, I.a.getD (I.length - 1) 0]⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have h0 : 0 < I.σ.length := by rw [hσ]; omega
  have hm : I.length - 1 + 1 = I.σ.length := by rw [hσ]; omega
  have hm' : I.length - 1 + 1 = I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · show I.σ.take 1 ++ I.σ.drop (I.length - 1) = _
    rw [drop_last I.σ true hm, show I.σ.take 1 = (I.σ.drop 0).take 1 by simp,
      take_one_drop I.σ true h0]
    rfl
  · show I.a.take 0 ++ a :: I.a.drop (I.length - 1) = _
    rw [drop_last I.a 0 hm']
    rfl

omit [NeZero L] in
theorem cutGlueR_one_eq (I : LoopIdx (ZMod L)) (hwf : I.WF) (hn : 2 ≤ I.length) (b : ZMod L) :
    I.cutGlueR 1 I.length b = ⟨I.σ, I.a.set (I.length - 1) b⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have hm' : I.length - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · show (I.σ.drop 0).take (I.length - 1 + 1) = I.σ
    rw [List.drop_zero, show I.length - 1 + 1 = I.length by omega,
      List.take_of_length_le (by rw [hσ])]
  · show (I.a.drop 0).take (I.length - 1) ++ [b] = _
    rw [List.drop_zero, List.set_eq_take_cons_drop b hm',
      show I.length - 1 + 1 = I.length by omega,
      List.drop_eq_nil_of_le (by rw [hlen])]



/-- Only the wrap-around cut `(k,l) = (1,n)` has a left chain of length 2. -/
theorem primBilLen_two_eq (W : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    (hn : 2 ≤ I.length) :
    primBilLen L W 2 K D I
      = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          K (I.cutGlueL 1 I.length a) * SB L a b * D (I.cutGlueR 1 I.length b) := by
  have hlenL : ∀ (k l : ℕ) (a : ZMod L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueL k l a).length = k + I.length - l + 1 :=
    fun k l a h1 h2 h3 => LoopIdx.length_cutGlueL I a h1 h2 h3
  rw [primBilLen]
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (by simp [Finset.mem_Icc]; omega)]
  · rw [Finset.sum_eq_single_of_mem I.length (by simp [Finset.mem_Ioc]; omega)]
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ite_eq_left (by rw [hlenL 1 I.length a le_rfl (by omega) le_rfl]; omega)]
    · intro l hl hne
      rw [Finset.mem_Ioc] at hl
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right (by rw [hlenL 1 l a le_rfl hl.1 hl.2]; omega)]
  · intro k hk hne
    rw [Finset.mem_Icc] at hk
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (by rw [hlenL k l a hk.1 hl.1 hl.2]; omega)]

/-- Only the adjacent cuts `(k, k+1)` have a right chain of length 2. -/
theorem primBilLenR_two_eq (W : ℕ) (F G : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    (hn : 2 ≤ I.length) :
    Decay.primBilLenR L W 2 F G I
      = (W : ℂ) * ∑ k ∈ Finset.Icc 1 (I.length - 1), ∑ a : ZMod L, ∑ b : ZMod L,
          F (I.cutGlueL k (k + 1) a) * SB L a b * G (I.cutGlueR k (k + 1) b) := by
  have hlenR : ∀ (k l : ℕ) (b : ZMod L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueR k l b).length = l - k + 1 :=
    fun k l b h1 h2 h3 => LoopIdx.length_cutGlueR I b h1 h2 h3
  rw [Decay.primBilLenR]
  congr 1
  have key : ∀ k ∈ Finset.Icc 1 I.length,
      (∑ l ∈ Finset.Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
        (if (I.cutGlueR k l b).length = 2 then
          F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0))
      = if k ∈ Finset.Icc 1 (I.length - 1) then
          (∑ a : ZMod L, ∑ b : ZMod L,
            F (I.cutGlueL k (k + 1) a) * SB L a b * G (I.cutGlueR k (k + 1) b)) else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hlt : k < I.length
    · rw [ite_eq_left (by rw [Finset.mem_Icc]; omega)]
      rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [Finset.mem_Ioc]; omega)]
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [ite_eq_left (by rw [hlenR k (k + 1) b hk.1 (by omega) (by omega)]; omega)]
      · intro l hl hne
        rw [Finset.mem_Ioc] at hl
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right (by rw [hlenR k l b hk.1 hl.1 hl.2]; omega)]
    · have hkn : k = I.length := by omega
      subst hkn
      rw [ite_eq_right (by rw [Finset.mem_Icc]; omega), Finset.Ioc_self, Finset.sum_empty]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (by intro x hx; rw [Finset.mem_Icc] at *; omega)]



noncomputable def xiLoop (m : Bool → ℂ) (I : LoopIdx (ZMod L)) (i : ℕ) : ℂ :=
  m (I.σ.getD i true) * m (I.σ.getD ((i + 1) % I.length) true)

noncomputable def thetaGenLoop (L : ℕ) [NeZero L] (m : Bool → ℂ) (t : ℝ)
    (D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  ∑ i ∈ Finset.range I.length, ∑ c : ZMod L,
    xiLoop m I i * (Theta L ((t : ℂ) * xiLoop m I i) * SB L) (I.a.getD i 0) c
      * D ⟨I.σ, I.a.set i c⟩

section
variable (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ) (K D : LoopIdx (ZMod L) → ℂ)

theorem thetaR_term (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo L W m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (ZMod L)) (hwf : I.WF) {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ I.length) :
    (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        D (I.cutGlueL k (k + 1) a) * SB L a b * K (I.cutGlueR k (k + 1) b)
      = ∑ c : ZMod L,
          xiLoop m I (k - 1)
            * (Theta L ((t : ℂ) * xiLoop m I (k - 1)) * SB L) (I.a.getD (k - 1) 0) c
            * D ⟨I.σ, I.a.set (k - 1) c⟩ := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hxi : xiLoop m I (k - 1) = m (I.σ.getD (k - 1) true) * m (I.σ.getD k true) := by
    rw [xiLoop, show (k - 1 + 1) % I.length = k by
      rw [show k - 1 + 1 = k by omega, Nat.mod_eq_of_lt (by omega)]]
  have hinner : ∀ b : ZMod L, K (I.cutGlueR k (k + 1) b)
      = (W : ℂ)⁻¹ * xiLoop m I (k - 1)
          * Theta L ((t : ℂ) * xiLoop m I (k - 1)) (I.a.getD (k - 1) 0) b := by
    intro b
    rw [cutGlueR_succ_eq I hwf hk hk', hK, kTwo, hxi]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cutGlueL_succ_eq I hk hk', Finset.mul_sum]
  calc ∑ b : ZMod L, (W : ℂ) * (D ⟨I.σ, I.a.set (k - 1) a⟩ * SB L a b
          * K (I.cutGlueR k (k + 1) b))
      = ∑ b : ZMod L, (Theta L ((t : ℂ) * xiLoop m I (k - 1)) (I.a.getD (k - 1) 0) b
            * SB L b a) * (xiLoop m I (k - 1) * D ⟨I.σ, I.a.set (k - 1) a⟩) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hinner b, show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
        field_simp
    _ = xiLoop m I (k - 1)
          * (Theta L ((t : ℂ) * xiLoop m I (k - 1)) * SB L) (I.a.getD (k - 1) 0) a
          * D ⟨I.σ, I.a.set (k - 1) a⟩ := by
        rw [← Finset.sum_mul, Matrix.mul_apply]
        ring


theorem thetaL_term (hL : 3 ≤ L)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo L W m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (ZMod L)) (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * xiLoop m I (I.length - 1)‖ < 1) :
    (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        K (I.cutGlueL 1 I.length a) * SB L a b * D (I.cutGlueR 1 I.length b)
      = ∑ c : ZMod L,
          xiLoop m I (I.length - 1)
            * (Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) * SB L)
                (I.a.getD (I.length - 1) 0) c
            * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hxi : m (I.σ.getD 0 true) * m (I.σ.getD (I.length - 1) true)
      = xiLoop m I (I.length - 1) := by
    rw [xiLoop, show (I.length - 1 + 1) % I.length = 0 by
      rw [show I.length - 1 + 1 = I.length by omega, Nat.mod_self]]
    ring
  have hsym : ∀ p q : ZMod L, Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) p q
      = Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) q p := fun p q =>
    congrFun (congrFun (Theta_transpose L hL hξ) q) p
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cutGlueR_one_eq I hwf hn]
  have step : ∀ a : ZMod L,
      (W : ℂ) * (K (I.cutGlueL 1 I.length a) * SB L a b * D ⟨I.σ, I.a.set (I.length - 1) b⟩)
        = (Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) (I.a.getD (I.length - 1) 0) a
            * SB L a b) * (xiLoop m I (I.length - 1) * D ⟨I.σ, I.a.set (I.length - 1) b⟩) := by
    intro a
    rw [cutGlueL_one_eq I hwf hn, hK, kTwo, hxi, hsym a (I.a.getD (I.length - 1) 0)]
    field_simp
  rw [Finset.sum_congr rfl fun a _ => step a, ← Finset.sum_mul, Matrix.mul_apply]
  ring


theorem couplingLen_two_eq_thetaGenLoop (hL : 3 ≤ L)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo L W m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (ZMod L)) (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * xiLoop m I (I.length - 1)‖ < 1) :
    Decay.couplingLen L W 2 K D I = thetaGenLoop L m t D I := by
  have hR : Decay.primBilLenR L W 2 D K I
      = ∑ i ∈ Finset.range (I.length - 1), ∑ c : ZMod L,
          xiLoop m I i * (Theta L ((t : ℂ) * xiLoop m I i) * SB L) (I.a.getD i 0) c
            * D ⟨I.σ, I.a.set i c⟩ := by
    rw [primBilLenR_two_eq W D K I hn, Finset.mul_sum,
      sum_Icc_one_eq_range (I.length - 1)
        (fun k => (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          D (I.cutGlueL k (k + 1) a) * SB L a b * K (I.cutGlueR k (k + 1) b))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [thetaR_term W m t K D hK I hwf (by omega : 1 ≤ i + 1) (by omega)]
    simp
  have hL2 : primBilLen L W 2 K D I
      = ∑ c : ZMod L,
          xiLoop m I (I.length - 1)
            * (Theta L ((t : ℂ) * xiLoop m I (I.length - 1)) * SB L)
                (I.a.getD (I.length - 1) 0) c
            * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
    rw [primBilLen_two_eq W K D I hn, thetaL_term W m t K D hL hK I hwf hn hξ]
  rw [Decay.couplingLen, hR, hL2, thetaGenLoop,
    show I.length = (I.length - 1) + 1 by omega, Finset.sum_range_succ]
  exact add_comm _ _


end

theorem smul_Theta_mul_SB (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    ξ • (Theta L ξ * SB L) = Theta L ξ - 1 := by
  have h : Theta L ξ - ξ • (SB L * Theta L ξ) = 1 := by
    have h0 := mul_Theta L hL hξ
    rwa [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at h0
  rw [(Theta_commute_SB L hL hξ).eq]
  refine eq_sub_of_add_eq ?_
  rw [← h]
  abel

theorem thetaGenLoop_kernel_eq (hL : 3 ≤ L) {t : ℝ} (ht : (t : ℂ) ≠ 0) {ξ : ℂ}
    (hξ : ‖(t : ℂ) * ξ‖ < 1) (x c : ZMod L) :
    ξ * (Theta L ((t : ℂ) * ξ) * SB L) x c
      = (t : ℂ)⁻¹ * (Theta L ((t : ℂ) * ξ) x c - (1 : Matrix (ZMod L) (ZMod L) ℂ) x c) := by
  have h := congrFun (congrFun (smul_Theta_mul_SB hL hξ) x) c
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at h
  rw [← h]
  field_simp

/-! #### The `LoopIdx` / `LoopArg` representation bridge

`RBM.Uker` and `RBM.ThetaOp` act on tensors `A : (Fin n) → ZMod L → ℂ` while the loop
layer uses `RBM.LoopIdx` (two lists).  `docs/STATUS.md` asks whoever proves (5.19) to fix
the bridge; it is `fun v => D ⟨σ, List.ofFn v⟩` for a fixed charge list `σ`, and the only
combinatorial fact needed is that `List.set` on `List.ofFn` is `Function.update`. -/

/-- `List.set` on a `List.ofFn` is `Function.update`. -/
theorem set_ofFn_eq_ofFn_update {α : Type*} {n : ℕ} (a : Fin n → α) (i : Fin n) (c : α) :
    (List.ofFn a).set (i : ℕ) c = List.ofFn (Function.update a i c) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.length_set, List.length_ofFn] at h1
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  by_cases hij : (i : ℕ) = j
  · subst hij
    simp [Function.update_self]
  · rw [ite_eq_right hij, Function.update_apply,
      ite_eq_right (by simp only [Fin.ext_iff]; omega)]

/-- **(5.16), corrected**, in the `LoopArg` (tensor) representation used by `RBM.Uker` and
`RBM.ThetaOp`. -/
noncomputable def thetaGenOp (L : ℕ) [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun a => ∑ i : Fin n, ∑ c : ZMod L,
    ξ i * (Theta L (t * ξ i) * SB L) (a i) c * A (Function.update a i c)

/-- **The representation bridge.**  On a loop whose labels come from a tensor index, the
`LoopIdx`-side generator `RBM.Gauss.thetaGenLoop` is the `LoopArg`-side one. -/
theorem thetaGenLoop_ofFn {n : ℕ} (m : Bool → ℂ) (t : ℝ) (D : LoopIdx (ZMod L) → ℂ)
    (σ : List Bool) (a : LoopArg L n) :
    thetaGenLoop L m t D ⟨σ, List.ofFn a⟩
      = thetaGenOp L (fun i : Fin n => m (σ.getD (i : ℕ) true)
            * m (σ.getD (((i : ℕ) + 1) % n) true)) (t : ℂ) (fun v => D ⟨σ, List.ofFn v⟩) a := by
  have hlen : (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)).length = n := List.length_ofFn
  rw [thetaGenLoop, thetaGenOp, hlen,
    Finset.sum_range fun i : ℕ => ∑ c : ZMod L,
      xiLoop m (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)) i
        * (Theta L ((t : ℂ) * xiLoop m (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)) i) * SB L)
            ((List.ofFn a).getD i 0) c
        * D ⟨σ, (List.ofFn a).set i c⟩]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  have hx : xiLoop m (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)) (i : ℕ)
      = m (σ.getD (i : ℕ) true) * m (σ.getD (((i : ℕ) + 1) % n) true) := by
    rw [xiLoop, hlen]
  rw [hx, set_ofFn_eq_ofFn_update,
    List.getD_eq_getElem (List.ofFn a) (0 : ZMod L) (by simp), List.getElem_ofFn]

theorem smul_thetaGenOp_eq (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {t : ℂ}
    (hξ : ∀ i, ‖t * ξ i‖ < 1) (A : LoopArg L n → ℂ) (a : LoopArg L n) :
    t * thetaGenOp L ξ t A a
      = (∑ i : Fin n, ∑ c : ZMod L, Theta L (t * ξ i) (a i) c * A (Function.update a i c))
        - (n : ℂ) * A a := by
  have hker : ∀ (i : Fin n) (x c : ZMod L),
      t * (ξ i * (Theta L (t * ξ i) * SB L) x c)
        = Theta L (t * ξ i) x c - (1 : Matrix (ZMod L) (ZMod L) ℂ) x c := by
    intro i x c
    have h := congrFun (congrFun (smul_Theta_mul_SB hL (hξ i)) x) c
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at h
    rw [← h]
    ring
  have hone : ∀ i : Fin n,
      ∑ c : ZMod L, (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c * A (Function.update a i c)
        = A a := by
    intro i
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, Function.update_eq_self, ite_true]
  rw [thetaGenOp, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => (by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, hker i (a i) c, sub_mul] :
      t * ∑ c : ZMod L, ξ i * (Theta L (t * ξ i) * SB L) (a i) c * A (Function.update a i c)
        = ∑ c : ZMod L, (Theta L (t * ξ i) (a i) c * A (Function.update a i c)
            - (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c * A (Function.update a i c)))]
  simp only [Finset.sum_sub_distrib, hone]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-- **Index check against Example 2.16 (p. 21).**  At `n = 3` the corrected generator is
literally the three-term display of the paper, with edge parameters `m₁m₂`, `m₂m₃`, `m₃m₁` and
kernels `m_i m_{i+1} Θ^{(B)}_{t m_i m_{i+1}} · S^(B)` — the `S^(B)` that (5.16) drops. -/
theorem thetaGenLoop_three (m : Bool → ℂ) (t : ℝ) (D : LoopIdx (ZMod L) → ℂ)
    (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    thetaGenLoop L m t D ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩
      = (∑ c : ZMod L, (m σ₁ * m σ₂)
            * (Theta L ((t : ℂ) * (m σ₁ * m σ₂)) * SB L) a₁ c * D ⟨[σ₁, σ₂, σ₃], [c, a₂, a₃]⟩)
        + (∑ c : ZMod L, (m σ₂ * m σ₃)
            * (Theta L ((t : ℂ) * (m σ₂ * m σ₃)) * SB L) a₂ c * D ⟨[σ₁, σ₂, σ₃], [a₁, c, a₃]⟩)
        + (∑ c : ZMod L, (m σ₃ * m σ₁)
            * (Theta L ((t : ℂ) * (m σ₃ * m σ₁)) * SB L) a₃ c
              * D ⟨[σ₁, σ₂, σ₃], [a₁, a₂, c]⟩) := by
  simp [thetaGenLoop, xiLoop, LoopIdx.length, Finset.sum_range_succ, List.getD]


/-- **The missing `S^(B)` is invisible to every row-sum argument.**  `S^(B)` is row-stochastic
(`RBM.sum_SB_row`), so `Θ^{(B)}_ξ S^(B)` and `Θ^{(B)}_ξ` have the same row sums.  Hence
`RBM.sum_ThetaOp_row` and everything built on it (`RBM.SumZero_ThetaOp`, the `ℓ^∞` bounds)
survive the correction of (5.16) unchanged; what does *not* survive is the identity (5.19)
itself. -/
theorem sum_Theta_mul_SB_row (hL : 3 ≤ L) {ξ : ℂ} (x : ZMod L) :
    ∑ c : ZMod L, (Theta L ξ * SB L) x c = ∑ y : ZMod L, Theta L ξ x y := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, sum_SB_row L hL y, mul_one]

end Eq519


/-! ### (5.15) with the generator in front -/

section Eq515

variable {L : ℕ} [NeZero L]

/-- **(5.15), with the `l_K = 2` coupling replaced by the generator `Θ_{t,σ}`.**  This is the
form §5.3 consumes: the drift of `L - K` is `Θ_{t,σ} ∘ (L-K)` plus the higher-rank couplings,
plus the quadratic term (5.13), plus `Ẽ`.  The only input beyond (5.12)-(5.14) is that `K` is
the rank-2 primitive (2.57) on 2-loops, which is `RBM.kTwoLoop` (and `rfl` for it). -/
theorem hasDerivAt_sub_prim_thetaGen (W : ℕ) [NeZero W] (hL : 3 ≤ L) (m : Bool → ℂ) (t : ℝ)
    {Lf K : ℝ → LoopIdx (ZMod L) → ℂ} {u : ℝ} {I : LoopIdx (ZMod L)} {EG : ℂ}
    (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * xiLoop m I (I.length - 1)‖ < 1)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K u ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo L W m t σ₁ σ₂ a₁ a₂)
    {n : ℕ} (hn' : I.length + 2 ≤ n) (h2 : 2 ∈ Finset.range n)
    (hLf : HasDerivAt (fun v : ℝ => Lf v I) (EG + primRhs L W (Lf u) I) u)
    (hKd : HasDerivAt (fun v : ℝ => K v I) (primRhs L W (K u) I) u) :
    HasDerivAt (fun v : ℝ => Lf v I - K v I)
      (EG + (thetaGenLoop L m t (Lf u - K u) I
        + ∑ lK ∈ (Finset.range n).erase 2, Decay.couplingLen L W lK (K u) (Lf u - K u) I
        + primBil L W (Lf u - K u) (Lf u - K u) I)) u := by
  refine (hasDerivAt_sub_prim L W hLf hKd).congr_deriv ?_
  have hsplit : primBil L W (K u) (Lf u - K u) I + primBil L W (Lf u - K u) (K u) I
      = Decay.couplingLen L W 2 (K u) (Lf u - K u) I
        + ∑ lK ∈ (Finset.range n).erase 2, Decay.couplingLen L W lK (K u) (Lf u - K u) I := by
    rw [← Decay.sum_couplingLen L W (K u) (Lf u - K u) I hn', ← Finset.add_sum_erase _ _ h2]
  rw [hsplit, couplingLen_two_eq_thetaGenLoop W m t (K u) (Lf u - K u) hL hK I hwf hn hξ]

end Eq515


/-! ### Step 0: `take`/`drop`/`getD` through `List.zip` -/

section ListZip

variable {α β : Type*}

theorem take_zip_eq (l₁ : List α) (l₂ : List β) (k : ℕ) :
    (l₁.zip l₂).take k = (l₁.take k).zip (l₂.take k) := by
  induction k generalizing l₁ l₂ with
  | zero => simp
  | succ k ih =>
      cases l₁ with
      | nil => simp
      | cons x xs =>
          cases l₂ with
          | nil => simp
          | cons y ys => simp [ih]

theorem drop_zip_eq (l₁ : List α) (l₂ : List β) (k : ℕ) :
    (l₁.zip l₂).drop k = (l₁.drop k).zip (l₂.drop k) := by
  induction k generalizing l₁ l₂ with
  | zero => simp
  | succ k ih =>
      cases l₁ with
      | nil => simp
      | cons x xs =>
          cases l₂ with
          | nil => simp
          | cons y ys => simp [ih]

theorem charge_getD_zip (l₁ : List α) (l₂ : List β) (da : α) (db : β) {k : ℕ}
    (h₁ : k < l₁.length) (h₂ : k < l₂.length) :
    ((l₁.zip l₂).getD k (da, db)).1 = l₁.getD k da := by
  have hk : k < (l₁.zip l₂).length := by
    rw [List.length_zip]; omega
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ h₁, List.getElem_zip]

end ListZip

/-! ### Step 2: `gprodM` over an append -/

section GprodAppend

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gprodM_append (z : ℂ) (l₁ l₂ : List (Bool × Matrix n n ℂ)) (M : Matrix n n ℂ) :
    gprodM z (l₁ ++ l₂) M = gprodM z l₁ M * gprodM z l₂ M := by
  induction l₁ with
  | nil => simp
  | cons p l ih => simp only [List.cons_append, gprodM_cons, ih, Matrix.mul_assoc]

end GprodAppend

/-! ### Step 1: `insB` with an `Eblk` is `cutGlue` -/

section CutGlueDict

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
theorem insB_zip_eq_cutGlue (I : LoopIdx (ZMod L)) (hwf : I.WF) {k : ℕ}
    (hk : k < I.a.length) (b : ZMod L) :
    insB (Eblk L W b) k (I.σ.zip (I.a.map (Eblk L W)))
      = (I.cutGlue (k + 1) b).σ.zip ((I.cutGlue (k + 1) b).a.map (Eblk L W)) := by
  have hσ : k < I.σ.length := by rw [hwf]; exact hk
  have hσ' : I.σ.take (k + 1) = I.σ.take k ++ [I.σ.getD k true] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hσ, List.getD_eq_getElem _ _ hσ]
    rfl
  show insB (Eblk L W b) k (I.σ.zip (I.a.map (Eblk L W)))
      = (I.σ.take (k + 1) ++ I.σ.drop (k + 1 - 1)).zip
          ((I.a.take (k + 1 - 1) ++ b :: I.a.drop (k + 1 - 1)).map (Eblk L W))
  rw [Nat.add_sub_cancel, hσ', List.map_append, List.map_cons, List.append_assoc,
    List.singleton_append,
    List.zip_append (by simp only [List.length_take, List.length_map]; omega),
    List.zip_cons_cons]
  show (I.σ.zip (I.a.map (Eblk L W))).take k
      ++ (((I.σ.zip (I.a.map (Eblk L W))).getD k (true, 0)).1, Eblk L W b)
        :: (I.σ.zip (I.a.map (Eblk L W))).drop k = _
  rw [take_zip_eq, drop_zip_eq, ← List.map_take, ← List.map_drop,
    charge_getD_zip I.σ (I.a.map (Eblk L W)) true 0 hσ (by simpa using hk)]

omit [NeZero W] in
theorem trace_gprodM_insB_zip (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) (hwf : I.WF) {k : ℕ} (hk : k < I.a.length) (b : ZMod L) :
    Matrix.trace (gprodM z (insB (Eblk L W b) k (I.σ.zip (I.a.map (Eblk L W)))) M)
      = gloop L W M z (I.cutGlue (k + 1) b) := by
  rw [insB_zip_eq_cutGlue I hwf hk b, gprodM_zip_map_eq_gloopProd, gloop]

end CutGlueDict

/-! ### Step 3: the two shapes of a double insertion -/

section DoubleIns

variable {α : Type*}

theorem getD_drop_list (l : List α) (da : α) (k m : ℕ) :
    (l.drop k).getD m da = l.getD (k + m) da := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
      cases l with
      | nil => simp
      | cons p l =>
          rw [List.drop_succ_cons, ih, show k + 1 + m = (k + m) + 1 by omega,
            List.getD_cons_succ]

theorem getD_take_list (l : List α) (da : α) {k m : ℕ} (h : m < k) :
    (l.take k).getD m da = l.getD m da := by
  by_cases hm : m < l.length
  · have h1 : m < (l.take k).length := by simp only [List.length_take]; omega
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hm, List.getElem_take]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_take]; omega),
      List.getD_eq_default _ _ (by omega)]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `B` inserted **twice at the same slot** `k`. -/
def dblB (B : Matrix n n ℂ) (k : ℕ) (l : List (Bool × Matrix n n ℂ)) :
    List (Bool × Matrix n n ℂ) :=
  l.take k ++ ((l.getD k (true, 0)).1, B) :: ((l.getD k (true, 0)).1, B) :: l.drop k

/-- `B` inserted at **two distinct slots** `p < q`. -/
def ins2B (B : Matrix n n ℂ) (p q : ℕ) (l : List (Bool × Matrix n n ℂ)) :
    List (Bool × Matrix n n ℂ) :=
  l.take p ++ ((l.getD p (true, 0)).1, B)
    :: ((l.drop p).take (q - p) ++ ((l.getD q (true, 0)).1, B) :: l.drop q)

omit [Fintype n] [DecidableEq n]

variable (B : Matrix n n ℂ) {k jj : ℕ} {l : List (Bool × Matrix n n ℂ)}

theorem length_take_insB (hk : k ≤ l.length) : (l.take k).length = k := by
  simp only [List.length_take]; omega

theorem insB_eq_append :
    insB B k l = (l.take k ++ [((l.getD k (true, 0)).1, B)]) ++ l.drop k := by
  rw [insB, List.append_assoc, List.singleton_append]

theorem take_insB_self (hk : k ≤ l.length) : (insB B k l).take k = l.take k :=
  List.take_left' (length_take_insB hk)

theorem drop_insB_self (hk : k ≤ l.length) :
    (insB B k l).drop k = ((l.getD k (true, 0)).1, B) :: l.drop k :=
  List.drop_left' (length_take_insB hk)

theorem take_insB_succ (hk : k ≤ l.length) :
    (insB B k l).take (k + 1) = l.take k ++ [((l.getD k (true, 0)).1, B)] := by
  rw [insB_eq_append]
  exact List.take_left'
    (by rw [List.length_append, List.length_singleton, length_take_insB hk])

theorem drop_insB_succ (hk : k ≤ l.length) : (insB B k l).drop (k + 1) = l.drop k := by
  rw [insB_eq_append]
  exact List.drop_left'
    (by rw [List.length_append, List.length_singleton, length_take_insB hk])

theorem take_insB_of_le (h : jj ≤ k) (hk : k ≤ l.length) :
    (insB B k l).take jj = l.take jj := by
  rw [insB, List.take_append_of_le_length (by rw [length_take_insB hk]; exact h),
    List.take_take, min_eq_left h]

theorem drop_insB_of_le (h : jj ≤ k) (hk : k ≤ l.length) :
    (insB B k l).drop jj
      = (l.drop jj).take (k - jj) ++ ((l.getD k (true, 0)).1, B) :: l.drop k := by
  rw [insB, List.drop_append_of_le_length (by rw [length_take_insB hk]; exact h),
    List.drop_take]

theorem getD_insB_self (hk : k ≤ l.length) :
    (insB B k l).getD k (true, 0) = ((l.getD k (true, 0)).1, B) := by
  rw [insB, List.getD_append_right _ _ _ _ (le_of_eq (length_take_insB hk)),
    length_take_insB hk, Nat.sub_self, List.getD_cons_zero]

theorem getD_insB_of_lt (h : jj < k) (hk : k ≤ l.length) :
    (insB B k l).getD jj (true, 0) = l.getD jj (true, 0) := by
  have hjl : jj < (l.take k).length := by rw [length_take_insB hk]; exact h
  rw [insB, List.getD_append _ _ _ jj hjl, getD_take_list l (true, 0) h]

theorem getD_insB_of_gt (h : k < jj) (hk : k ≤ l.length) :
    (insB B k l).getD jj (true, 0) = l.getD (jj - 1) (true, 0) := by
  rw [insB, List.getD_append_right _ _ _ _ (by rw [length_take_insB hk]; omega),
    length_take_insB hk, show jj - k = (jj - k - 1) + 1 by omega, List.getD_cons_succ,
    getD_drop_list l (true, 0) k (jj - k - 1), show k + (jj - k - 1) = jj - 1 by omega]

theorem insB_insB_self_eq_dblB (hk : k ≤ l.length) :
    insB B k (insB B k l) = dblB B k l := by
  have h0 : insB B k (insB B k l)
      = (insB B k l).take k ++ (((insB B k l).getD k (true, 0)).1, B)
          :: (insB B k l).drop k := rfl
  rw [h0, take_insB_self B hk, drop_insB_self B hk, getD_insB_self B hk]
  rfl

theorem insB_succ_insB_eq_dblB (hk : k ≤ l.length) :
    insB B (k + 1) (insB B k l) = dblB B k l := by
  have h0 : insB B (k + 1) (insB B k l)
      = (insB B k l).take (k + 1) ++ (((insB B k l).getD (k + 1) (true, 0)).1, B)
          :: (insB B k l).drop (k + 1) := rfl
  rw [h0, take_insB_succ B hk, drop_insB_succ B hk,
    getD_insB_of_gt B (by omega : k < k + 1) hk, Nat.add_sub_cancel, dblB,
    List.append_assoc, List.singleton_append]

theorem insB_insB_of_lt (h : jj < k) (hk : k ≤ l.length) :
    insB B jj (insB B k l) = ins2B B jj k l := by
  have h0 : insB B jj (insB B k l)
      = (insB B k l).take jj ++ (((insB B k l).getD jj (true, 0)).1, B)
          :: (insB B k l).drop jj := rfl
  rw [h0, take_insB_of_le B (le_of_lt h) hk, drop_insB_of_le B (le_of_lt h) hk,
    getD_insB_of_lt B h hk, ins2B]

theorem insB_insB_of_gt (h : k + 2 ≤ jj) (hk : k ≤ l.length) :
    insB B jj (insB B k l) = ins2B B k (jj - 1) l := by
  have h0 : insB B jj (insB B k l)
      = (insB B k l).take jj ++ (((insB B k l).getD jj (true, 0)).1, B)
          :: (insB B k l).drop jj := rfl
  have hsplit : jj = (k + 1) + (jj - k - 1) := by omega
  have htake : (insB B k l).take jj
      = (l.take k ++ [((l.getD k (true, 0)).1, B)]) ++ (l.drop k).take (jj - k - 1) := by
    conv_lhs => rw [hsplit]
    rw [List.take_add, take_insB_succ B hk, drop_insB_succ B hk]
  have hdrop : (insB B k l).drop jj = l.drop (jj - 1) := by
    conv_lhs => rw [hsplit]
    rw [← List.drop_drop, drop_insB_succ B hk, List.drop_drop,
      show k + (jj - k - 1) = jj - 1 by omega]
  rw [h0, htake, hdrop, getD_insB_of_gt B (by omega) hk, ins2B,
    show jj - 1 - k = jj - k - 1 by omega]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

end DoubleIns

/-! ### Step 4: reorganizing the double insertion sum -/

section SumSplit

theorem sum_range_triangle_comm {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → ℕ → M) :
    ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range k, g p k
      = ∑ p ∈ Finset.range n, ∑ q ∈ Finset.Ioo p n, g p q := by
  have hlt : ∀ k : ℕ, k ≤ n →
      (Finset.range n).filter (fun p => p < k) = Finset.range k := by
    intro k hk
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hgt : ∀ p : ℕ, (Finset.range n).filter (fun q => p < q) = Finset.Ioo p n := by
    intro p
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  have hL : ∀ k ∈ Finset.range n, ∑ p ∈ Finset.range k, g p k
      = ∑ p ∈ Finset.range n, if p < k then g p k else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← Finset.sum_filter, hlt k (le_of_lt hk)]
  have hR : ∀ p ∈ Finset.range n, ∑ q ∈ Finset.Ioo p n, g p q
      = ∑ q ∈ Finset.range n, if p < q then g p q else 0 := by
    intro p _
    rw [← Finset.sum_filter, hgt p]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_comm]

theorem Ico_succ_eq_Ioo (a b : ℕ) : Finset.Ico (a + 1) b = Finset.Ioo a b := by
  ext q
  simp only [Finset.mem_Ico, Finset.mem_Ioo]
  omega

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- **The `(k, jj)` insertion pairs sorted into diagonal and off-diagonal.**  The two
insertion slots either coincide (`jj ∈ {k, k+1}`, giving `dblB`, each twice) or are
distinct (giving `ins2B`, each ordered pair twice). -/
theorem sum_insB_insB_eq {M : Type*} [AddCommMonoid M] (B : Matrix n n ℂ)
    (l : List (Bool × Matrix n n ℂ)) (f : List (Bool × Matrix n n ℂ) → M) :
    ∑ k ∈ Finset.range l.length, ∑ jj ∈ Finset.range (l.length + 1),
        f (insB B jj (insB B k l))
      = 2 • (∑ k ∈ Finset.range l.length, f (dblB B k l))
        + 2 • (∑ p ∈ Finset.range l.length, ∑ q ∈ Finset.Ioo p l.length,
            f (ins2B B p q l)) := by
  set N := l.length with hN
  have hrow : ∀ k ∈ Finset.range N, ∑ jj ∈ Finset.range (N + 1), f (insB B jj (insB B k l))
      = (∑ p ∈ Finset.range k, f (ins2B B p k l))
        + (f (dblB B k l) + f (dblB B k l))
        + ∑ q ∈ Finset.Ioo k N, f (ins2B B k q l) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkl : k ≤ l.length := by omega
    have hsplit : ∑ jj ∈ Finset.range (N + 1), f (insB B jj (insB B k l))
        = ∑ jj ∈ Finset.range (k + 2), f (insB B jj (insB B k l))
          + ∑ jj ∈ Finset.Ico (k + 2) (N + 1), f (insB B jj (insB B k l)) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
    rw [hsplit]
    congr 1
    · have hS : ∑ p ∈ Finset.range k, f (insB B p (insB B k l))
          = ∑ p ∈ Finset.range k, f (ins2B B p k l) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_range] at hp
        rw [insB_insB_of_lt B hp hkl]
      rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        insB_insB_self_eq_dblB B hkl, insB_succ_insB_eq_dblB B hkl, hS, add_assoc]
    · rw [← Ico_succ_eq_Ioo, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
        show N + 1 - (k + 2) = N - (k + 1) by omega]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [insB_insB_of_gt B (by omega) hkl, show k + 2 + i - 1 = k + 1 + i by omega]
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_range_triangle_comm]
  generalize (∑ p ∈ Finset.range N, ∑ q ∈ Finset.Ioo p N, f (ins2B B p q l)) = X
  generalize (∑ k ∈ Finset.range N, f (dblB B k l)) = Y
  rw [two_nsmul, two_nsmul]
  abel

end SumSplit

/-! ### Step 5: the `tr(A · B · C · B)` factorizations -/

section TraceFactor

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (z : ℂ) (B M : Matrix n n ℂ) (l : List (Bool × Matrix n n ℂ))

/-- A chain cut open at `p` and closed up again at `q`, cycled so that `B` sits last. -/
theorem trace_gprodM_cut (p q : ℕ) :
    Matrix.trace (gprodM z (l.take p ++ ((l.getD p (true, 0)).1, B) :: l.drop q) M)
      = Matrix.trace (gprodM z (l.drop q) M * gprodM z (l.take p) M
          * Gsig M z (l.getD p (true, 0)).1 * B) := by
  have key : gprodM z (l.take p ++ ((l.getD p (true, 0)).1, B) :: l.drop q) M
      = gprodM z (l.take p) M * Gsig M z (l.getD p (true, 0)).1 * B
          * gprodM z (l.drop q) M := by
    simp only [gprodM_append, gprodM_cons, Matrix.mul_assoc]
  rw [key, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- A single insertion, cycled so that the inserted `B` sits last. -/
theorem trace_gprodM_insB (k : ℕ) :
    Matrix.trace (gprodM z (insB B k l) M)
      = Matrix.trace (gprodM z (l.drop k) M * gprodM z (l.take k) M
          * Gsig M z (l.getD k (true, 0)).1 * B) :=
  trace_gprodM_cut z B M l k k

/-- The middle segment of a double cut, with `B` glued on at the end. -/
theorem trace_gprodM_seg (p q : ℕ) :
    Matrix.trace (gprodM z ((l.drop p).take (q - p)
        ++ [((l.getD q (true, 0)).1, B)]) M)
      = Matrix.trace (gprodM z ((l.drop p).take (q - p)) M
          * Gsig M z (l.getD q (true, 0)).1 * B) := by
  have key : gprodM z ((l.drop p).take (q - p) ++ [((l.getD q (true, 0)).1, B)]) M
      = gprodM z ((l.drop p).take (q - p)) M * Gsig M z (l.getD q (true, 0)).1 * B := by
    simp only [gprodM_append, gprodM_cons, gprodM_nil, Matrix.mul_one, Matrix.mul_assoc]
  rw [key]

/-- A double insertion at the **same** slot. -/
theorem trace_gprodM_dblB (k : ℕ) :
    Matrix.trace (gprodM z (dblB B k l) M)
      = Matrix.trace ((gprodM z (l.drop k) M * gprodM z (l.take k) M
            * Gsig M z (l.getD k (true, 0)).1) * B
          * Gsig M z (l.getD k (true, 0)).1 * B) := by
  have key : gprodM z (dblB B k l) M
      = gprodM z (l.take k) M * Gsig M z (l.getD k (true, 0)).1 * B
            * Gsig M z (l.getD k (true, 0)).1 * B
          * gprodM z (l.drop k) M := by
    simp only [dblB, gprodM_append, gprodM_cons, Matrix.mul_assoc]
  rw [key, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- A double insertion at **two distinct** slots. -/
theorem trace_gprodM_ins2B (p q : ℕ) :
    Matrix.trace (gprodM z (ins2B B p q l) M)
      = Matrix.trace ((gprodM z (l.drop q) M * gprodM z (l.take p) M
            * Gsig M z (l.getD p (true, 0)).1) * B
          * (gprodM z ((l.drop p).take (q - p)) M
            * Gsig M z (l.getD q (true, 0)).1) * B) := by
  have key : gprodM z (ins2B B p q l) M
      = gprodM z (l.take p) M * Gsig M z (l.getD p (true, 0)).1 * B
            * (gprodM z ((l.drop p).take (q - p)) M
              * Gsig M z (l.getD q (true, 0)).1) * B
          * gprodM z (l.drop q) M := by
    simp only [ins2B, gprodM_append, gprodM_cons, Matrix.mul_assoc]
  rw [key, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end TraceFactor

/-! ### Step 6: the block traces are the cut-and-glue loops -/

section BlockTrace

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
theorem take_append_drop_zip_eq_cutGlueL (I : LoopIdx (ZMod L)) (hwf : I.WF) {p q : ℕ}
    (hpq : p < q) (hq : q < I.a.length) (a : ZMod L) :
    (I.σ.zip (I.a.map (Eblk L W))).take p
        ++ (((I.σ.zip (I.a.map (Eblk L W))).getD p (true, 0)).1, Eblk L W a)
          :: (I.σ.zip (I.a.map (Eblk L W))).drop q
      = (I.cutGlueL (p + 1) (q + 1) a).σ.zip
          ((I.cutGlueL (p + 1) (q + 1) a).a.map (Eblk L W)) := by
  have hσ : p < I.σ.length := by rw [hwf]; omega
  have hσ' : I.σ.take (p + 1) = I.σ.take p ++ [I.σ.getD p true] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hσ, List.getD_eq_getElem _ _ hσ]
    rfl
  show _ = (I.σ.take (p + 1) ++ I.σ.drop (q + 1 - 1)).zip
      ((I.a.take (p + 1 - 1) ++ a :: I.a.drop (q + 1 - 1)).map (Eblk L W))
  simp only [Nat.add_sub_cancel]
  rw [hσ', List.map_append, List.map_cons, List.append_assoc,
    List.singleton_append,
    List.zip_append (by simp only [List.length_take, List.length_map]; omega),
    List.zip_cons_cons, take_zip_eq, drop_zip_eq, ← List.map_take, ← List.map_drop,
    charge_getD_zip I.σ (I.a.map (Eblk L W)) true 0 hσ (by simpa using (by omega : p < I.a.length))]

omit [NeZero L] [NeZero W] in
theorem take_drop_zip_eq_cutGlueR (I : LoopIdx (ZMod L)) (hwf : I.WF) {p q : ℕ}
    (hpq : p < q) (hq : q < I.a.length) (b : ZMod L) :
    ((I.σ.zip (I.a.map (Eblk L W))).drop p).take (q - p)
        ++ [(((I.σ.zip (I.a.map (Eblk L W))).getD q (true, 0)).1, Eblk L W b)]
      = (I.cutGlueR (p + 1) (q + 1) b).σ.zip
          ((I.cutGlueR (p + 1) (q + 1) b).a.map (Eblk L W)) := by
  have hσq : q < I.σ.length := by rw [hwf]; omega
  have hdl : q - p < (I.σ.drop p).length := by simp only [List.length_drop]; omega
  have hσ' : (I.σ.drop p).take (q - p + 1)
      = (I.σ.drop p).take (q - p) ++ [(I.σ.drop p).getD (q - p) true] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hdl, List.getD_eq_getElem _ _ hdl]
    rfl
  show _ = ((I.σ.drop (p + 1 - 1)).take (q + 1 - (p + 1) + 1)).zip
      (((I.a.drop (p + 1 - 1)).take (q + 1 - (p + 1)) ++ [b]).map (Eblk L W))
  simp only [Nat.add_sub_cancel, show q + 1 - (p + 1) = q - p by omega]
  rw [hσ', List.map_append,
    List.map_cons, List.map_nil,
    List.zip_append (by simp only [List.length_take, List.length_map, List.length_drop]; omega),
    drop_zip_eq, take_zip_eq]
  simp only [← List.map_drop, ← List.map_take]
  rw [charge_getD_zip I.σ (I.a.map (Eblk L W)) true 0 hσq (by simpa using hq),
    getD_drop_list I.σ true p (q - p), show p + (q - p) = q by omega]
  rfl


variable (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)

omit [NeZero W] in
/-- The diagonal block trace is the single cut-and-glue loop `G^{(a)}_{k+1}`. -/
theorem trace_block_cutGlue (I : LoopIdx (ZMod L)) (hwf : I.WF) {k : ℕ}
    (hk : k < I.a.length) (a : ZMod L) :
    Matrix.trace (gprodM z ((I.σ.zip (I.a.map (Eblk L W))).drop k) M
        * gprodM z ((I.σ.zip (I.a.map (Eblk L W))).take k) M
        * Gsig M z ((I.σ.zip (I.a.map (Eblk L W))).getD k (true, 0)).1 * Eblk L W a)
      = gloop L W M z (I.cutGlue (k + 1) a) := by
  rw [← trace_gprodM_insB z (Eblk L W a) M (I.σ.zip (I.a.map (Eblk L W))) k,
    trace_gprodM_insB_zip M z I hwf hk a]

omit [NeZero W] in
/-- The left block trace is the left cut-and-glue loop `G^{(a),L}_{p+1,q+1}`. -/
theorem trace_block_cutGlueL (I : LoopIdx (ZMod L)) (hwf : I.WF) {p q : ℕ}
    (hpq : p < q) (hq : q < I.a.length) (a : ZMod L) :
    Matrix.trace (gprodM z ((I.σ.zip (I.a.map (Eblk L W))).drop q) M
        * gprodM z ((I.σ.zip (I.a.map (Eblk L W))).take p) M
        * Gsig M z ((I.σ.zip (I.a.map (Eblk L W))).getD p (true, 0)).1 * Eblk L W a)
      = gloop L W M z (I.cutGlueL (p + 1) (q + 1) a) := by
  rw [← trace_gprodM_cut z (Eblk L W a) M (I.σ.zip (I.a.map (Eblk L W))) p q,
    take_append_drop_zip_eq_cutGlueL I hwf hpq hq a, gprodM_zip_map_eq_gloopProd, gloop]

omit [NeZero W] in
/-- The right block trace is the right cut-and-glue loop `G^{(b),R}_{p+1,q+1}`. -/
theorem trace_block_cutGlueR (I : LoopIdx (ZMod L)) (hwf : I.WF) {p q : ℕ}
    (hpq : p < q) (hq : q < I.a.length) (b : ZMod L) :
    Matrix.trace (gprodM z (((I.σ.zip (I.a.map (Eblk L W))).drop p).take (q - p)) M
        * Gsig M z ((I.σ.zip (I.a.map (Eblk L W))).getD q (true, 0)).1 * Eblk L W b)
      = gloop L W M z (I.cutGlueR (p + 1) (q + 1) b) := by
  rw [← trace_gprodM_seg z (Eblk L W b) M (I.σ.zip (I.a.map (Eblk L W))) p q,
    take_drop_zip_eq_cutGlueR I hwf hpq hq b, gprodM_zip_map_eq_gloopProd, gloop]

end BlockTrace

/-! ### Step 7a: the Wirtinger combination as a linear operator -/

section WirtCombine

variable {d : Dims} {N : ℕ}

/-- The `∂_ij ∂_ji` combination of a tag-indexed family: the real tag on the diagonal,
the average of the two tags off it.  `RBM.Gauss.wirtSecond` is this applied to `coordD2`. -/
noncomputable def wirtCombine (d : Dims) (N : ℕ) (i j : d.Idx N) (F : Bool → ℂ) : ℂ :=
  if i = j then F true else (1 / 4 : ℝ) • (F true + F false)

/-- The Wirtinger pattern of a trace `tr(A · B_{ij} · C · B_{ij})`. -/
noncomputable def wirtPairTr (d : Dims) (N : ℕ) (A C : Matrix (d.Idx N) (d.Idx N) ℂ)
    (i j : d.Idx N) : ℂ :=
  wirtCombine d N i j fun b =>
    Matrix.trace (A * Bmat d N i j b * C * Bmat d N i j b)

theorem wirtSecond_eq_wirtCombine (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    wirtSecond d N Φ M i j = wirtCombine d N i j fun b => coordD2 d N Φ M (i, j, b) := by
  by_cases h : i = j
  · subst h; simp only [wirtSecond, wirtCombine]
  · simp only [wirtSecond, wirtCombine, ite_eq_right h]

/-- `wirtPairTr` in the shape consumed by `RBM.Gauss.sumSblk_half_wirtPair`. -/
theorem wirtPairTr_eq (A C : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    wirtPairTr d N A C i j
      = if i = j then Matrix.trace (A * Bmat d N i i true * C * Bmat d N i i true)
        else (1 / 4 : ℝ) • (Matrix.trace (A * Bmat d N i j true * C * Bmat d N i j true)
          + Matrix.trace (A * Bmat d N i j false * C * Bmat d N i j false)) := by
  by_cases h : i = j
  · subst h; simp only [wirtPairTr, wirtCombine]
  · simp only [wirtPairTr, wirtCombine, ite_eq_right h]

theorem wirtCombine_add (i j : d.Idx N) (F G : Bool → ℂ) :
    wirtCombine d N i j (fun b => F b + G b)
      = wirtCombine d N i j F + wirtCombine d N i j G := by
  by_cases h : i = j
  · simp only [wirtCombine, ite_eq_left h]
  · simp only [wirtCombine, ite_eq_right h, smul_add]
    abel

theorem wirtCombine_mul_left (i j : d.Idx N) (c : ℂ) (F : Bool → ℂ) :
    wirtCombine d N i j (fun b => c * F b) = c * wirtCombine d N i j F := by
  by_cases h : i = j
  · simp only [wirtCombine, ite_eq_left h]
  · simp only [wirtCombine, ite_eq_right h, ← mul_add, mul_smul_comm]

theorem wirtCombine_congr (i j : d.Idx N) (F G : Bool → ℂ) (ht : F true = G true)
    (hf : i ≠ j → F false = G false) :
    wirtCombine d N i j F = wirtCombine d N i j G := by
  by_cases hij : i = j
  · simp only [wirtCombine, ite_eq_left hij, ht]
  · simp only [wirtCombine, ite_eq_right hij, ht, hf hij]

theorem wirtCombine_sum {ι : Type*} (i j : d.Idx N) (s : Finset ι) (F : ι → Bool → ℂ) :
    wirtCombine d N i j (fun b => ∑ x ∈ s, F x b) = ∑ x ∈ s, wirtCombine d N i j (F x) := by
  by_cases h : i = j
  · simp only [wirtCombine, ite_eq_left h]
  · simp only [wirtCombine, ite_eq_right h]
    rw [← Finset.sum_add_distrib, ← Finset.smul_sum]

end WirtCombine

/-! ### Step 7b: the `½ ∑ S_ij` contraction is linear -/

section SblkLinear

variable {d : Dims} {N : ℕ}

theorem sumSblk_half_add (F G : d.Idx N → d.Idx N → ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
        Sblk (d.L N) (d.W N) i j • (F i j + G i j)
      = (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j • F i j
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j • G i j := by
  simp only [smul_add, Finset.sum_add_distrib]

theorem sumSblk_half_mul (c : ℂ) (F : d.Idx N → d.Idx N → ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j • (c * F i j)
      = c * ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
          Sblk (d.L N) (d.W N) i j • F i j) := by
  simp only [← mul_smul_comm, ← Finset.mul_sum]

theorem sumSblk_half_sum {ι : Type*} (s : Finset ι) (F : ι → d.Idx N → d.Idx N → ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
        Sblk (d.L N) (d.W N) i j • (∑ x ∈ s, F x i j)
      = ∑ x ∈ s, (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
          Sblk (d.L N) (d.W N) i j • F x i j := by
  have step : ∀ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j • (∑ x ∈ s, F x i j)
      = ∑ x ∈ s, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j • F x i j := by
    intro i
    simp only [Finset.smul_sum]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm, ← Finset.smul_sum]

end SblkLinear

/-! ### Step 7c: index reindexing for `primRhs` -/

theorem sum_Ioc_succ_eq_Ioo {M : Type*} [AddCommMonoid M] (p q : ℕ) (f : ℕ → M) :
    ∑ l ∈ Finset.Ioc (p + 1) q, f l = ∑ r ∈ Finset.Ioo p q, f (r + 1) := by
  have h1 : Finset.Ioc (p + 1) q = Finset.Ico (p + 2) (q + 1) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [h1, ← Ico_succ_eq_Ioo, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show q + 1 - (p + 2) = q - (p + 1) by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  omega

/-! ### Step 7d: the generic contraction -/

section Generic

variable {d : Dims} {N : ℕ}

/-- Every direction the Wirtinger second derivative actually reads is Hermitian: the two
tags off the diagonal, and the real tag on it.  (`Bmat d N i i false` is the one
non-Hermitian direction, and `wirtSecond` never reads it.) -/
theorem isHermitian_Bmat_of (i j : d.Idx N) (b : Bool) (h : i ≠ j ∨ b = true) :
    (Bmat d N i j b).IsHermitian := by
  rcases eq_or_ne i j with rfl | hij
  · have hb : b = true := h.resolve_left fun hne => hne rfl
    subst hb
    exact Bmat_isHermitian (p := (i, i, true)) (mem_usedCoord.2 (Or.inr ⟨rfl, rfl⟩))
  · rcases idxKey_lt_or_eq_or_lt d N i j with hlt | heq | hgt
    · exact Bmat_isHermitian (p := (i, j, b)) (mem_usedCoord.2 (Or.inl hlt))
    · exact absurd heq hij
    · have hji : (Bmat d N j i b).IsHermitian :=
        Bmat_isHermitian (p := (j, i, b)) (mem_usedCoord.2 (Or.inl hgt))
      cases b with
      | true => rwa [Bmat_swap_true] at hji
      | false =>
          rw [Bmat_swap_false d N hij] at hji
          have hneg := hji.neg
          rwa [neg_neg] at hneg

/-- `RBM.Gauss.sumSblk_half_wirtPair` in the `wirtPairTr` vocabulary. -/
theorem sumSblk_half_wirtPairTr (A C : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        wirtPairTr d N A C i j
      = (1 / 2 : ℂ) * ((d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
          Matrix.trace (A * Eblk (d.L N) (d.W N) a) * SB (d.L N) a b
            * Matrix.trace (C * Eblk (d.L N) (d.W N) b)) := by
  simp only [wirtPairTr_eq]
  exact sumSblk_half_wirtPair A C

/-- **The generator's second-order term of an observable whose `∂_ij ∂_ji` is a sum of
`tr(A · B_{ij} · C · B_{ij})`.**  This is the whole `½ ∑ S_ij` contraction, done once and
for all; the loop observable supplies the hypothesis through `coordD2_loopObs_eq`. -/
theorem sumSblk_half_wirtSecond_eq {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (nn : ℕ)
    (A C : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ)
    (A' C' : ℕ → ℕ → Matrix (d.Idx N) (d.Idx N) ℂ)
    (h : ∀ (i j : d.Idx N) (b : Bool), i ≠ j ∨ b = true → coordD2 d N Φ M (i, j, b)
      = 2 * (∑ k ∈ Finset.range nn,
            Matrix.trace (A k * Bmat d N i j b * C k * Bmat d N i j b))
        + 2 * (∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn,
            Matrix.trace (A' p q * Bmat d N i j b * C' p q * Bmat d N i j b))) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        wirtSecond d N Φ M i j
      = 2 * ∑ k ∈ Finset.range nn, (1 / 2 : ℂ) * ((d.W N : ℂ) *
            ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
              Matrix.trace (A k * Eblk (d.L N) (d.W N) a) * SB (d.L N) a b
                * Matrix.trace (C k * Eblk (d.L N) (d.W N) b))
        + 2 * ∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn, (1 / 2 : ℂ) * ((d.W N : ℂ) *
            ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
              Matrix.trace (A' p q * Eblk (d.L N) (d.W N) a) * SB (d.L N) a b
                * Matrix.trace (C' p q * Eblk (d.L N) (d.W N) b)) := by
  have hw : ∀ i j : d.Idx N, wirtSecond d N Φ M i j
      = 2 * (∑ k ∈ Finset.range nn, wirtPairTr d N (A k) (C k) i j)
        + 2 * (∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn,
            wirtPairTr d N (A' p q) (C' p q) i j) := by
    intro i j
    rw [wirtSecond_eq_wirtCombine,
      wirtCombine_congr i j (fun b => coordD2 d N Φ M (i, j, b))
        (fun b => 2 * (∑ k ∈ Finset.range nn,
              Matrix.trace (A k * Bmat d N i j b * C k * Bmat d N i j b))
          + 2 * (∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn,
              Matrix.trace (A' p q * Bmat d N i j b * C' p q * Bmat d N i j b)))
        (h i j true (Or.inr rfl)) (fun hne => h i j false (Or.inl hne)),
      wirtCombine_add, wirtCombine_mul_left, wirtCombine_mul_left,
      wirtCombine_sum, wirtCombine_sum]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [wirtCombine_sum]
    rfl
  simp only [hw]
  rw [sumSblk_half_add, sumSblk_half_mul, sumSblk_half_mul, sumSblk_half_sum,
    sumSblk_half_sum]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun k _ => sumSblk_half_wirtPairTr (A k) (C k)
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sumSblk_half_sum]
    exact Finset.sum_congr rfl fun q _ => sumSblk_half_wirtPairTr (A' p q) (C' p q)

end Generic

/-! ### Step 7e: `eGterm` and `primRhs` in `Finset.range` bookkeeping -/

section RangeForm

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
theorem primRhs_range_eq (K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primRhs L W K I
      = ∑ p ∈ Finset.range I.a.length, ∑ q ∈ Finset.Ioo p I.a.length,
          (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
            K (I.cutGlueL (p + 1) (q + 1) a) * SB L a b
              * K (I.cutGlueR (p + 1) (q + 1) b) := by
  rw [primRhs, sum_Icc_one_eq_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_Ioc_succ_eq_Ioo, Finset.mul_sum]
  rfl

theorem eGterm_zero_range_eq (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) :
    eGterm L W 0 M z I
      = ∑ k ∈ Finset.range I.a.length, (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          Matrix.trace (Gsig M z (I.σ.getD k true) * Eblk L W a) * SB L a b
            * gloop L W M z (I.cutGlue (k + 1) b) := by
  rw [eGterm, sum_Icc_one_eq_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.zero_apply, zero_smul, sub_zero, Nat.add_sub_cancel]

end RangeForm

/-! ### The frozen cut-and-glue identity -/

section Frozen

variable {d : Dims} {N : ℕ}

/-- **Lemma 2.11, (2.45)–(2.47), with the spectral parameter frozen.**  The generator's
second-order term `½ ∑_{ij} S_ij ∂_ij ∂_ji L_{σ,a}` splits into the single cut-and-glue
term `Ẽ` of (2.47) (at `m = 0`, i.e. with `G` in place of `G̃`) and the quadratic term
`primRhs` of (2.48). -/
theorem loopIto_second_frozen {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hC : ContDiff ℝ 2 (loopObs d N z I)) (hM : M.IsHermitian) (hz : z.im ≠ 0)
    (hwf : I.WF) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        wirtSecond d N (loopObs d N z I) M i j
      = eGterm (d.L N) (d.W N) 0 M z I
        + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) I := by
  set l := I.σ.zip (I.a.map (Eblk (d.L N) (d.W N))) with hl
  have hlen : l.length = I.a.length := by
    rw [hl, List.length_zip, List.length_map, hwf, Nat.min_self]
  have hsplit : ∀ (i j : d.Idx N) (bb : Bool), i ≠ j ∨ bb = true →
      coordD2 d N (loopObs d N z I) M (i, j, bb)
        = 2 * (∑ k ∈ Finset.range I.a.length,
              Matrix.trace ((gprodM z (l.drop k) M * gprodM z (l.take k) M
                  * Gsig M z (l.getD k (true, 0)).1) * Bmat d N i j bb
                * Gsig M z (l.getD k (true, 0)).1 * Bmat d N i j bb))
          + 2 * (∑ p ∈ Finset.range I.a.length, ∑ q ∈ Finset.Ioo p I.a.length,
              Matrix.trace ((gprodM z (l.drop q) M * gprodM z (l.take p) M
                  * Gsig M z (l.getD p (true, 0)).1) * Bmat d N i j bb
                * (gprodM z ((l.drop p).take (q - p)) M
                  * Gsig M z (l.getD q (true, 0)).1) * Bmat d N i j bb)) := by
    intro i j bb hb
    rw [coordD2_loopObs_eq hC hM hz hwf i j bb (isHermitian_Bmat_of i j bb hb), ← hl,
      ← hlen, sum_insB_insB_eq (Bmat d N i j bb) l fun ll => Matrix.trace (gprodM z ll M),
      hlen]
    simp only [trace_gprodM_dblB, trace_gprodM_ins2B, nsmul_eq_mul, Nat.cast_ofNat]
  rw [sumSblk_half_wirtSecond_eq I.a.length
      (fun k => gprodM z (l.drop k) M * gprodM z (l.take k) M
        * Gsig M z (l.getD k (true, 0)).1)
      (fun k => Gsig M z (l.getD k (true, 0)).1)
      (fun p q => gprodM z (l.drop q) M * gprodM z (l.take p) M
        * Gsig M z (l.getD p (true, 0)).1)
      (fun p q => gprodM z ((l.drop p).take (q - p)) M
        * Gsig M z (l.getD q (true, 0)).1)
      hsplit,
    eGterm_zero_range_eq, primRhs_range_eq]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hch : (l.getD k (true, 0)).1 = I.σ.getD k true := by
      rw [hl]
      exact charge_getD_zip I.σ (I.a.map (Eblk (d.L N) (d.W N))) true 0
        (by rw [hwf]; exact hk) (by simpa using hk)
    have hAtr : ∀ a : ZMod (d.L N),
        Matrix.trace (gprodM z (l.drop k) M * gprodM z (l.take k) M
            * Gsig M z (l.getD k (true, 0)).1 * Eblk (d.L N) (d.W N) a)
          = gloop (d.L N) (d.W N) M z (I.cutGlue (k + 1) a) := by
      intro a
      rw [hl]
      exact trace_block_cutGlue M z I hwf hk a
    have hsum : (∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
          gloop (d.L N) (d.W N) M z (I.cutGlue (k + 1) a) * SB (d.L N) a b
            * Matrix.trace (Gsig M z (I.σ.getD k true) * Eblk (d.L N) (d.W N) b))
        = ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
            Matrix.trace (Gsig M z (I.σ.getD k true) * Eblk (d.L N) (d.W N) a)
              * SB (d.L N) a b * gloop (d.L N) (d.W N) M z (I.cutGlue (k + 1) b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show SB (d.L N) b a = SB (d.L N) a b from
        congrFun (congrFun (SB_transpose (d.L N)) a) b]
      ring
    simp only [hAtr]
    rw [hch, hsum]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_Ioo] at hq
    have hLtr : ∀ a : ZMod (d.L N),
        Matrix.trace (gprodM z (l.drop q) M * gprodM z (l.take p) M
            * Gsig M z (l.getD p (true, 0)).1 * Eblk (d.L N) (d.W N) a)
          = gloop (d.L N) (d.W N) M z (I.cutGlueL (p + 1) (q + 1) a) := by
      intro a
      rw [hl]
      exact trace_block_cutGlueL M z I hwf hq.1 hq.2 a
    have hRtr : ∀ b : ZMod (d.L N),
        Matrix.trace (gprodM z ((l.drop p).take (q - p)) M
            * Gsig M z (l.getD q (true, 0)).1 * Eblk (d.L N) (d.W N) b)
          = gloop (d.L N) (d.W N) M z (I.cutGlueR (p + 1) (q + 1) b) := by
      intro b
      rw [hl]
      exact trace_block_cutGlueR M z I hwf hq.1 hq.2 b
    simp only [hLtr, hRtr]
    ring

/-- The same identity with no smoothness hypothesis: `RBM.Gauss.bddC2_loopObs` supplies
`C²` for the loop observable unconditionally. -/
theorem loopIto_second_frozen_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        wirtSecond d N (loopObs d N z I) M i j
      = eGterm (d.L N) (d.W N) 0 M z I
        + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) I :=
  loopIto_second_frozen
    (bddC2_loopObs hz (abs_pos.mpr hz) le_rfl hwf).contDiff hM hz hwf

/-- **The hypothesis `RBM.Gauss.LoopIto` is discharged**, with the `Ẽ` term of (2.47)
instantiated at `m = 0`, i.e. with `G` in place of `G̃`.  (`RBM.Gauss.eGterm_sub_eGterm`
turns this into the `G̃` form once the motion of `z_t` is added.) -/
noncomputable def loopItoFrozen {z : ℂ} (hz : z.im ≠ 0) : LoopIto d N z where
  EG M I := eGterm (d.L N) (d.W N) 0 M z I
  second M hM I hwf _ := loopIto_second_frozen_of_im_ne_zero hz M hM I hwf

end Frozen


/-! ### Lemma 2.11 in moment form, with no cut-and-glue hypothesis left -/

section Closed

variable {d : Dims} {N : ℕ}

/-- **The pointwise drift identity of `RBM.Gauss.generator_add_zMotion`, unconditionally.**
`RBM.Gauss.loopItoFrozen` discharges the `LoopIto` hypothesis and `hEG` is `rfl`:

`(∂_u + 𝓛) L_{σ,a} = Ẽ_{σ,a}[G - m] + W ∑_{k<l} (G^L ∘ L) S^(B) (G^R ∘ L)`

at every Hermitian matrix, with `Ẽ` carrying the paper's `G̃ = G - m` of (2.47). -/
theorem generator_add_zMotion_gauss {E u : ℝ} (hz : (zt E u).im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          wirtSecond d N (loopObs d N (zt E u) I) M i j
        + zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I
      = eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
        + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M (zt E u)) I :=
  generator_add_zMotion (loopItoFrozen hz) (fun _ _ => rfl) M hM I hwf hn

/-- **Lemma 2.11 in moment form, with both arguments moving and *no* cut-and-glue hypothesis.**

This is `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy` with `hito`, `hEG` and `TestFun` all
discharged — by `RBM.Gauss.loopItoFrozen` (T140) and `RBM.Gauss.testFun_loopObs_of_im_le`
(T133) respectively.  What is left is `RBM.Gauss.MatrixStein` (T70) and the joint
differentiability `hjoint` (T141). -/
theorem hasDerivAt_sample_ELval_hierarchy_gauss (hst : MatrixStein d)
    {E u η ε : ℝ} (hu : 0 < u) (hη : 0 < η) (hε : 0 < ε)
    (hball : ∀ s ∈ Metric.ball u ε, η ≤ |(zt E s).im|)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    {Ψ' : (ℝ × ℝ) →L[ℝ] ℂ}
    (hjoint : HasFDerivAt (fun p : ℝ × ℝ =>
        ∫ ω, gloop (d.L N) (d.W N) (Hflow d N p.1 ω) (zt E p.2) I ∂(P d)) Ψ' (u, u)) :
    HasDerivAt (fun v : ℝ => (sample d).ELval E N v I)
      (∫ ω, (eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u) I
        + primRhs (d.L N) (d.W N) ((sample d).Lval E N u ω) I) ∂(P d)) u := by
  have hzu : η ≤ |(zt E u).im| := hball u (Metric.mem_ball_self hε)
  have hz : (zt E u).im ≠ 0 := abs_pos.mp (hη.trans_le hzu)
  exact hasDerivAt_sample_ELval_hierarchy hst hu hη hε hball (loopItoFrozen hz)
    (fun _ _ => rfl) hwf hn (testFun_loopObs_of_im_le hz hη hzu hwf hn) hjoint

end Closed

end RBM.Gauss

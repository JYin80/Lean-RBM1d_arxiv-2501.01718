/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Hierarchy
import RBM1D.Hierarchy.Dynamics
import RBM1D.Flow.Initial

/-!
# The moving spectral parameter and the drift of `L - K` (T134)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 2.11 / (2.45)-(2.47) (pp. 17-19) and (5.12)-(5.15) (pp. 52-53).

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

## Main definitions

* `RBM.Gauss.zMotion` — `∑_k (-m(σ_k)) · W ∑_b L_{G^{(b)}_k(σ,a)}`, the contribution of the
  motion of `z_t` to `∂_t L_{t,σ,a}`.

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
  (`RBM.primRhs_sub`, `RBM1D/Hierarchy/Dynamics.lean`).  The identification of the `l_K = 2`
  part of the coupling with `RBM.ThetaOp` is (5.19) and is **not** done here.

## Hypotheses (nothing here is an `axiom`)

* `RBM.Gauss.LoopIto d N (zt E u)` together with `hEG : hito.EG = eGterm … 0 …` — the
  deterministic cut-and-glue algebra of Lemma 2.11, still owed (T76).  This file shows that
  it is enough to prove it with the *frozen* `Ẽ`; the `G̃` of (2.47) then comes for free.
* `RBM.Gauss.MatrixStein`, `RBM.Gauss.TestFun` — as in `RBM1D/Gauss/Hierarchy.lean`.
* `hjoint` — joint differentiability of `(v, w) ↦ E[L(H_v, z_w)]` at `(u,u)`.  Pointwise in
  `ω` this is `RBM.Gauss.contDiffAt_gloop_flow`; passing it under the integral needs a
  dominating bound on the joint derivative, which is the `TestFun` gap of T133.
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

end RBM.Gauss

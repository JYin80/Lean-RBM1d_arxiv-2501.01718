/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelBddT
import RBM1D.Gauss.Step6HierarchyGauss
import RBM1D.Gauss.DischargeBDG

/-!
# The identification of `φ'` with the pinned drift (T206)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  T196 (`RBM1D/Gauss/MomentDuhamelBddT.lean`) closed all seven fields of
`RBM.Gauss.TestFunT₁` for the moment route's `Ψ`, so the generator identity
`RBM.Gauss.hasDerivAt_integral_momentObsT` holds with no hypothesis on `Ψ`; what it leaves
open is the **identification** of its right-hand side.  That identification is the point of
this file, and it is the step that makes `RBM.MomentDuhamel.MomentIneq` a statement with
content: if the drift on the right of (5.20) were a free tensor, the inequality would be
satisfiable by fiat (T74's obstruction 1).

## The identification (item (1) of T206)

`RBM.Gauss.hasDerivAt_ukerObsT_drift`.  Write `Ψ₁(u, M) = (U_{u,t} ∘ (L - K)_u)_a`.  Then at
every Hermitian `M`

  `∂_u Ψ₁ + 𝓛 Ψ₁ = (U_{u,t} ∘ F_u)_a`,  `F = RBM.DriftDef.driftF`.

Three inputs, and the whole content is that they line up:

* `RBM.hasDerivAt_Uker_path` (variation of constants) gives
  `∂_u Ψ₁ = U ∘ (L-K)' - U ∘ Θ_u(L-K)`;
* `RBM.DriftDef.drift_split_gen` — T58's (5.15), the field `RBM.MomentDuhamel.Hyp.drift` —
  gives `(L-K)' + 𝓛(L-K) = genS_u(L-K) + F` with `F` the **definition** `driftF`;
* `RBM.SumZeroDyn.genS` is `RBM.ThetaOp` (definitionally), so the two `Θ`'s cancel.

`𝓛` passes through `U` because `U` is a finite deterministic linear combination: that is
`RBM.Gauss.genD_finsetSum`, built on `RBM.Gauss.coordD2_finsetSum`, the second-order companion
of `RBM.Gauss.EmartCoeff_sum`.  `RBM.Gauss.genD_loopObs_eq_genLK` then identifies `𝓛` of the
*regularised* loop (globally `C²`, which is what makes the linearity argument cheap) with
`RBM.MomentDuhamel.genLK` at Hermitian matrices, via `RBM.EGDef.wirtSecond_gloop_eq`.

**The two first-order terms have to be added before the modulus is taken.**  Bounding `∂_uΨ₁`
and `𝓛Ψ₁` separately leaves `U ∘ Θ(L-K)`, which is not small; this is why
`RBM.Gauss.genMomentPt_le` (which spends `Re(F̄ 𝓛F) ≤ ‖F‖‖𝓛F‖` one step too early) is
replaced here by `RBM.Gauss.genMomentPt_le_re`.  The resulting **pointwise integrand of
(5.20)** is `RBM.Gauss.timeD1_add_genMomentPt_le_driftF`:

  `∂_u|Ψ₁|^{2p} + 𝓛|Ψ₁|^{2p} ≤ 2p|Ψ₁|^{2p-1}|(U ∘ F_u)_a| + p(2p-1)|Ψ₁|^{2p-2}·quadVar(Ψ₁)`,

the constants being exactly the `2p` and `p(2p-1)` that fix `RBM.MomentDuhamel.cMDval`.

## The bridge (item (3) of T206)

`RBM.Gauss.ukerObsT_flow` and `RBM.Gauss.momentObsT_flow`: along a flow (Hermitian by
`RBM.Sample.hermitian`) the moment route's `Ψ` **is** `|(U_{u,t} ∘ lkT)_a|^{2p}`, the integrand
of `RBM.MomentDuhamel.MomentIneq`.  It is an equation with a one-line proof, not a hypothesis.

## Satisfiability

`K` is pinned to `RBM.Band.Kval` by the hypothesis `hKdef` and `∂_uK` to `RBM.Gauss.Kprim`
(= `RBM.primRhs`, by `RBM.hasDerivAt_Kgen_all`), so nothing on either side of the identity is
data a caller may choose.  `RBM.Gauss.hasDerivAt_ukerObsT_drift_flow` and
`RBM.Gauss.timeD1_add_genMomentPt_le_driftF_flow` discharge every hypothesis from the paper's
standing assumptions `|E| < 2`, `0 ≤ u < 1`, `0 ≤ v < 1` at the flow matrix — the *critical*
scaling, with `v ↑ 1` allowed, not a degenerate point.
`RBM.Gauss.hasDerivAt_ukerObsT_drift_at_zero` is the mandatory degenerate check at `ω = 0`
(flow matrix `0`): the identity is asserted there too and is not vacuous.

## What is **not** here (item (2) of T206, and two items T206 did not list)

`RBM.MomentDuhamel.momentIneq_of_derivBound` consumes eight things per `(p, N, σ, v, a)`.
This file supplies the pointwise inequality (its last item) and the bridge.  Still missing:

1. **The interval integrability and continuity side conditions** — item (2) of T206.  Five of
   them: a window bound on `ψ`, `ContinuousOn` of `u ↦ E|Ψ₁|^{2p}`, and interval integrability
   of `φ'`, of `u ↦ ‖U ∘ F_u‖_{2p}`, of `u ↦ ‖(U⊗U) ∘ (E⊗E)‖_p`, and of the product `ψ·f`.
   All should follow from the deterministic envelope `‖G‖ ≤ (Im z_u)⁻¹` by dominated
   convergence, as `RBM.Gauss.integrable_lkT_pow` does at a fixed time; none is done.
2. **The quadratic variation is not yet the interface's `E ⊗ E`.**  `RBM.MomentDuhamel.MomentIneq`
   has `‖(U⊗U) ∘ (E⊗E)_{a,a}‖_p` on the right, i.e. `RBM.Uker` at the doubled charges
   `RBM.SumZeroDyn.xi2` applied to `RBM.MomentDuhamel.eeFun`.  What exists is
   `RBM.Gauss.quadVarPairs_Uker` (`quadVar(Ψ₁) = ∑_{ij} ‖(U ∘ E^{(M)}(i,j))_a‖²`) and, for a
   *single* loop, `RBM.Gauss.eeRaw_self_eq_quadVarPairs` plus the gluing (5.22)
   `RBM.Gauss.eeEdge_eq_sum_SB`.  The **bilinear, `U`-conjugated** form of that gluing —
   `∑_{ij} (U ∘ E^{(M)}(i,j))_a · conj((U ∘ E^{(M)}(i,j))_{a'}) = (U⊗U ∘ eeArg)_{a,a'}` — is
   not in the repository (`RBM1D/Hierarchy/EEBridge.lean` contains no `RBM.Uker`).
3. **The `Q_t` route (`MomentIneqQ`) is untouched.**  Its drift identity needs `∂_u Q_u`, which
   produces the two extra terms `RBM.SumZeroDyn.commS` and `RBM.SumZeroDyn.varthetaDot` of
   (5.91); nothing here differentiates `RBM.Qop` in the time.

Consequently `momentDuhamelHyp_gauss` still does not exist, and this file does not create it.

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

/-- `fderiv` of a finite `ℂ`-linear combination, **evaluated** at a fixed direction, so that
every object in sight is scalar-valued. -/
theorem fderiv_finsetSum_const_mul_apply {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (hf : ∀ b ∈ s, Differentiable ℝ (f b))
    (M B : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (fderiv ℝ (fun M' => ∑ b ∈ s, c b * f b M') M) B
      = ∑ b ∈ s, c b * (fderiv ℝ (f b) M) B := by
  have hd : ∀ b ∈ s, DifferentiableAt ℝ (fun M'' => c b * f b M'') M :=
    fun b hb => (differentiableAt_const (c b)).mul (hf b hb M)
  rw [fderiv_fun_sum hd]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun b hb => by
    rw [fderiv_const_mul (hf b hb M) (c b)]; simp

/-- `coordD2` with the inner evaluation moved inside the outer `fderiv`, so that the object
differentiated a second time is scalar-valued. -/
theorem coordD2_eq_fderiv_eval {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (h : DifferentiableAt ℝ (fderiv ℝ Φ) M)
    (q : d.Idx N × d.Idx N × Bool) :
    coordD2 d N Φ M q
      = fderiv ℝ (fun M' => (fderiv ℝ Φ M') (Bmat d N q.1 q.2.1 q.2.2)) M
          (Bmat d N q.1 q.2.1 q.2.2) := by
  set B := Bmat d N q.1 q.2.1 q.2.2 with hB
  have hev : HasFDerivAt (fun M' => (fderiv ℝ Φ M') B)
      ((ContinuousLinearMap.apply ℝ ℂ B).comp (fderiv ℝ (fderiv ℝ Φ) M)) M :=
    (ContinuousLinearMap.apply ℝ ℂ B).hasFDerivAt.comp M h.hasFDerivAt
  rw [hev.fderiv]
  rfl

/-- **`coordD2` through a finite deterministic linear combination.** -/
theorem coordD2_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (hf : ∀ b ∈ s, ContDiff ℝ 2 (f b))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    coordD2 d N (fun M' => ∑ b ∈ s, c b * f b M') M q
      = ∑ b ∈ s, c b * coordD2 d N (f b) M q := by
  classical
  set B := Bmat d N q.1 q.2.1 q.2.2 with hB
  have hdiff : ∀ b ∈ s, Differentiable ℝ (f b) := fun b hb =>
    (hf b hb).differentiable (by norm_num)
  have hd2 : ∀ b ∈ s, DifferentiableAt ℝ (fderiv ℝ (f b)) M := fun b hb => by
    have h := ((hf b hb).fderiv_right (m := 1) (by norm_num))
    exact h.differentiable (by norm_num) M
  -- the evaluated first derivative of each summand is differentiable at `M`
  have hev : ∀ b ∈ s, DifferentiableAt ℝ (fun M' => (fderiv ℝ (f b) M') B) M := by
    intro b hb
    exact HasFDerivAt.differentiableAt
      ((ContinuousLinearMap.apply ℝ ℂ B).hasFDerivAt.comp M (hd2 b hb).hasFDerivAt)
  -- the sum is `C²` too, so its own first derivative is differentiable at `M`
  have hfsum : ContDiff ℝ 2 (fun M' => ∑ b ∈ s, c b * f b M') :=
    ContDiff.sum fun b hb => contDiff_const.mul (hf b hb)
  have hd2sum : DifferentiableAt ℝ (fderiv ℝ fun M'' => ∑ b ∈ s, c b * f b M'') M := by
    have h := (hfsum.fderiv_right (m := 1) (by norm_num))
    exact h.differentiable (by norm_num) M
  rw [coordD2_eq_fderiv_eval hd2sum q, ← hB]
  have h1 : (fun M' => (fderiv ℝ (fun M'' => ∑ b ∈ s, c b * f b M'') M') B)
      = fun M' => ∑ b ∈ s, c b * (fderiv ℝ (f b) M') B :=
    funext fun M' => fderiv_finsetSum_const_mul_apply s c f hdiff M' B
  rw [h1, fderiv_fun_sum (fun b hb => (hev b hb).const_mul (c b))]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [fderiv_const_mul (hev b hb) (c b)]
  simp [coordD2_eq_fderiv_eval (hd2 b hb) q, ← hB]

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

/-- **`RBM.Gauss.genD` through a finite deterministic linear combination**, hence through
`RBM.Uker` — this is the "since `U` is a deterministic linear operator" of §5.2, at second
order (`RBM.Gauss.EmartCoeff_sum` is the first-order form).  It is used inside
`RBM.Gauss.hasDerivAt_ukerObsT_drift`. -/
theorem genD_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (hf : ∀ b ∈ s, ContDiff ℝ 2 (f b))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genD d N (fun M' => ∑ b ∈ s, c b * f b M') M = ∑ b ∈ s, c b * genD d N (f b) M := by
  have h : ∀ q ∈ usedCoord d N,
      (gvar d (crd d N q) : ℝ) • coordD2 d N (fun M' => ∑ b ∈ s, c b * f b M') M q
        = ∑ b ∈ s, c b * ((gvar d (crd d N q) : ℝ) • coordD2 d N (f b) M q) := by
    intro q _
    rw [coordD2_finsetSum s c f hf M q, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      simp only [Complex.real_smul]; ring
  have hinner : ∑ q ∈ usedCoord d N,
        (gvar d (crd d N q) : ℝ) • coordD2 d N (fun M' => ∑ b ∈ s, c b * f b M') M q
      = ∑ b ∈ s, c b * ∑ q ∈ usedCoord d N,
          (gvar d (crd d N q) : ℝ) • coordD2 d N (f b) M q := by
    rw [Finset.sum_congr rfl h, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
  conv_lhs => rw [genD, hinner]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [genD]; exact (mul_smul_comm _ _ _).symm

/-! ### `𝓛(|F|^{2p})` with the first-order term kept unbounded

`RBM.Gauss.genMomentPt_le` replaces `Re(F̄ 𝓛F)` by `‖F‖‖𝓛F‖` in its last step.  That is one
step too early for the moment route: the *time* derivative of `|F|^{2p}` contributes a second
first-order term `Re(F̄ ∂_uF)`, and the two have to be **added before** the modulus is taken —
that addition is precisely where `∂_uF + 𝓛F = (U ∘ driftF)_a` (`hasDerivAt_ukerObsT_drift`)
applies.  Bounding them separately would leave `U ∘ Θ(L-K)`, which is not small. -/

/-- **`RBM.Gauss.genMomentPt_le` with `Re(F̄ 𝓛F)` kept.** -/
theorem genMomentPt_le_re {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hF : ContDiff ℝ 2 F)
    {p : ℕ} (hp : 1 ≤ p) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genMomentPt d N F p M
      ≤ 2 * p * ‖F M‖ ^ (2 * p - 2) * ((starRingEnd ℂ) (F M) * genD d N F M).re
        + p * (2 * p - 1) * ‖F M‖ ^ (2 * p - 2) * quadVar d N F M := by
  set a : ℝ := ‖F M‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hkey : ∀ q : d.Idx N × d.Idx N × Bool,
      (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2) * ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
        ≤ (((p - 1 : ℕ)) : ℝ) * a ^ (p - 1) * ‖coordD1 d N F M q‖ ^ 2 := by
    intro q
    rcases Nat.lt_or_ge p 2 with hlt | hge
    · have h0 : p - 1 = 0 := by omega
      rw [h0]; simp
    · have hsq : ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
          ≤ a * ‖coordD1 d N F M q‖ ^ 2 := by
        have h1 : |((starRingEnd ℂ) (F M) * coordD1 d N F M q).re|
            ≤ ‖(starRingEnd ℂ) (F M) * coordD1 d N F M q‖ := Complex.abs_re_le_norm _
        have h2 : ‖(starRingEnd ℂ) (F M) * coordD1 d N F M q‖
            = ‖F M‖ * ‖coordD1 d N F M q‖ := by rw [norm_mul, RCLike.norm_conj]
        rw [h2] at h1
        have h3 : ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
            ≤ (‖F M‖ * ‖coordD1 d N F M q‖) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        calc ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
            ≤ (‖F M‖ * ‖coordD1 d N F M q‖) ^ 2 := h3
          _ = a * ‖coordD1 d N F M q‖ ^ 2 := by rw [ha]; ring
      have hpow : a ^ (p - 2) * a = a ^ (p - 1) := by
        rw [← pow_succ]; congr 1; omega
      have hc : (0 : ℝ) ≤ (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2) := by positivity
      calc (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2)
              * ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
          ≤ (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2) * (a * ‖coordD1 d N F M q‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hc
        _ = (((p - 1 : ℕ)) : ℝ) * a ^ (p - 1) * ‖coordD1 d N F M q‖ ^ 2 := by
            rw [← hpow]; ring
  have hstep : genMomentPt d N F p M
      ≤ (2⁻¹ : ℝ) * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
          ((p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * a ^ (p - 1)
              * (4 * ‖coordD1 d N F M q‖ ^ 2)
            + a ^ (p - 1) * (2 * ‖coordD1 d N F M q‖ ^ 2
              + 2 * ((starRingEnd ℂ) (F M) * coordD2 d N F M q).re))) := by
    rw [genMomentPt]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (gvar d (crd d N q)).2
    rw [coordD2_momentFun_ofReal hF p M q, Complex.ofReal_re, ← ha]
    have h4 := hkey q
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    nlinarith [h4, hp0]
  refine le_trans hstep ?_
  have hsum : ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
      ((p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * a ^ (p - 1) * (4 * ‖coordD1 d N F M q‖ ^ 2)
        + a ^ (p - 1) * (2 * ‖coordD1 d N F M q‖ ^ 2
          + 2 * ((starRingEnd ℂ) (F M) * coordD2 d N F M q).re)))
      = (p : ℝ) * a ^ (p - 1) * (4 * (((p - 1 : ℕ)) : ℝ) + 2) * quadVar d N F M
        + (p : ℝ) * a ^ (p - 1) * 2 * (2 * ((starRingEnd ℂ) (F M) * genD d N F M).re) := by
    rw [← sum_gvar_re_coordD2 (F := F) M]
    simp only [quadVar, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsum]
  have hp1 : a ^ (p - 1) = ‖F M‖ ^ (2 * p - 2) := by
    rw [ha, ← pow_mul]; congr 1; omega
  have hcast : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp, Nat.cast_one]
  rw [hp1, hcast]
  ring_nf
  nlinarith [le_refl (0 : ℝ)]

/-! ### The identification of `φ'` with the pinned drift

The generator identity of T196 produces `∫ ∂₁Ψ + ½ ∑ S ∫ ∂∂Ψ` and leaves both terms abstract.
Here they are identified: for the *inner* observable `Ψ₁ = (U_{u,v} ∘ (L - K)_u)_a` the two
first-order pieces combine, the `Θ` of `RBM.hasDerivAt_Uker_path` cancels against the `genS`
of `RBM.MomentDuhamel.Hyp.drift`, and what is left is `U_{u,v} ∘ F` with
`F = RBM.DriftDef.driftF` — the drift pinned by T58, **not** a free tensor.

This is the reason `RBM.MomentDuhamel.MomentIneq` is not vacuous: its right-hand side is a
statement about a definition in the Green function of the matrix. -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`𝓛` of the regularised loop observable is `RBM.MomentDuhamel.genLK`**, at a Hermitian
matrix.  The projection `RBM.Gauss.hermCLM` inside `RBM.Gauss.loopObs` is what makes the
observable globally `C²`; at a Hermitian point it has the same Wirtinger second derivatives as
the raw `RBM.gloop` (`RBM.EGDef.wirtSecond_gloop_eq`), so `𝓛` does not see it. -/
theorem genD_loopObs_eq_genLK (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {m : ℕ} (σ : Fin m → Bool) (b : LoopArg (B.L N) m) (c : ℂ) :
    genD B.toDims N
        (fun M' => loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - c) M
      = MomentDuhamel.genLK B E N u M σ b := by
  have hW : ∀ i j : B.Idx N,
      wirtSecond B.toDims N
          (fun M' => loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - c) M i j
        = wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ b) M i j := by
    intro i j
    calc wirtSecond B.toDims N
          (fun M' => loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - c) M i j
        = wirtSecond B.toDims N
            (loopObs B.toDims N (zt E u) (LoopData.idx (σ, b))) M i j :=
          EGDef.wirtSecond_sub_const _ _ _ _ _
      _ = wirtSecond B.toDims N
            (fun M' => gloop (B.L N) (B.W N) M' (zt E u) (LoopData.idx (σ, b))) M i j :=
          EGDef.wirtSecond_gloop_eq hz hM _ _ _
      _ = wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ b) M i j :=
          (EGDef.wirtSecond_sub_const _ _ _ _ _).symm
  have h1 : genD B.toDims N
        (fun M' => loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - c) M
      = (2⁻¹ : ℝ) • ∑ i : B.Idx N, ∑ j : B.Idx N,
          Sblk (B.L N) (B.W N) i j • wirtSecond B.toDims N
            (fun M' => loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - c) M i j :=
    genD_eq_sum_pairs _ _
  have h2 : MomentDuhamel.genLK B E N u M σ b
      = (2 : ℂ)⁻¹ * ∑ i : B.Idx N, ∑ j : B.Idx N, ((Sblk (B.L N) (B.W N) i j : ℝ) : ℂ)
          * wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ b) M i j := rfl
  rw [h1, h2]
  have hstep : ∑ i : B.Idx N, ∑ j : B.Idx N,
        Sblk (B.L N) (B.W N) i j • wirtSecond B.toDims N
          (fun M' => loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - c) M i j
      = ∑ i : B.Idx N, ∑ j : B.Idx N, ((Sblk (B.L N) (B.W N) i j : ℝ) : ℂ)
          * wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ b) M i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hW i j, Complex.real_smul]
  rw [hstep, Complex.real_smul]
  norm_num

/-- **The bridge `RBM.Gauss.ukerObsT ↔ RBM.Uker ∘ RBM.MomentDuhamel.lkFun`.**

At a Hermitian matrix the regularisation `RBM.Gauss.hermCLM` inside `RBM.Gauss.loopObs` is the
identity, so the moment route's inner observable is literally `(U_{r,t} ∘ (L-K)_r)_a`. -/
theorem ukerObsT_eq_Uker_lkFun (B : Band Ω) (E : ℝ) (N : ℕ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (r : ℝ) :
    ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a r M
      = Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
          (MomentDuhamel.lkFun B E N r M σ) a := by
  have hval : ∀ b : LoopArg (B.L N) (n + 2),
      loopObs B.toDims N (zt E r) ⟨List.ofFn σ, List.ofFn b⟩ M - K r b
        = MomentDuhamel.lkFun B E N r M σ b := by
    intro b
    have h : loopObs B.toDims N (zt E r) (LoopData.idx (σ, b)) M
        = gloop (B.L N) (B.W N) M (zt E r) (LoopData.idx (σ, b)) :=
      loopObs_of_isHermitian hM
    rw [hKdef r b]
    exact congrArg (fun x => x - B.Kval E N r (LoopData.idx (σ, b))) h
  change Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t
      (fun b => loopObs B.toDims N (zt E r) ⟨List.ofFn σ, List.ofFn b⟩ M - K r b) a = _
  exact congrArg
    (fun Y => Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) t Y a) (funext hval)

/-- **The bridge along the flow**: `RBM.Gauss.ukerObsT` at the flow matrix is
`U_{u,t} ∘ RBM.SumZeroDyn.lkT`, the object the two fields of `RBM.MomentDuhamel.Hyp` speak
about.  Hermiticity of the flow is `RBM.Sample.hermitian`, so there is no side condition. -/
theorem ukerObsT_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (u : ℝ) (ω : Ω) :
    ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u (X.H N u ω)
      = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
          (SumZeroDyn.lkT X E N u ω σ) a :=
  ukerObsT_eq_Uker_lkFun B E N σ a t hKdef (X.hermitian N u ω) u

/-- **`Ψ` along the flow is `|(U_{u,t} ∘ (L-K)_u)_a|^{2p}`**, in the exact shape the two
fields of `RBM.MomentDuhamel.Hyp` (via `RBM.MomentDuhamel.momentIneq_of_derivBound`) integrate.
This is item (3) of T206: the bridge is an equation, proved, not an assumption. -/
theorem momentObsT_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (p : ℕ) (u : ℝ) (ω : Ω) :
    momentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a p u (X.H N u ω)
      = ((|‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
            (SumZeroDyn.lkT X E N u ω σ) a‖| ^ (2 * p) : ℝ) : ℂ) := by
  have h0 : momentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a p u (X.H N u ω)
      = (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u (X.H N u ω)
          * (starRingEnd ℂ) (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u
              (X.H N u ω))) ^ p :=
    momentObsT_eq _ _ _ _ _ _ _ _ _
  rw [h0, ukerObsT_flow B X E N σ a t hKdef u ω, mul_conj_eq, ← Complex.ofReal_pow,
    ← pow_mul, abs_norm]

/-- **The propagator-conjugated drift identity.**

`Ψ₁(u, M) = (U_{u,t} ∘ (L - K)_u)_a` satisfies `(∂_u + 𝓛) Ψ₁ = (U_{u,t} ∘ F_u)_a` with
`F = RBM.DriftDef.driftF`.  Read term by term: `RBM.hasDerivAt_Uker_path` contributes
`U ∘ (L-K)' - U ∘ Θ(L-K)`, `RBM.MomentDuhamel.Hyp.drift` (i.e. T58's
`RBM.DriftDef.drift_split_gen`) says `(L-K)' + 𝓛(L-K) = genS (L-K) + F`, and
`RBM.SumZeroDyn.genS` is `RBM.ThetaOp`, so the two `Θ`'s cancel. -/
theorem hasDerivAt_ukerObsT_drift (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (hv : ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (ht : ∀ i, ‖t * xiOf (mSigma E) σ i‖ < 1) :
    ∃ D : ℂ,
      HasDerivAt (fun r : ℝ =>
          ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a r M) D u
        ∧ D + genD B.toDims N
              (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u) M
          = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
              (DriftDef.driftF B E N u M σ) a := by
  classical
  set ξ : Fin (n + 2) → ℂ := xiOf (mSigma E) σ with hξ
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  -- at a Hermitian matrix the regularised observable is the raw `(L - K)`
  have hEq : ∀ r : ℝ,
      ukerObsT B.toDims N E (List.ofFn σ) ξ t K a r M
        = Uker (B.L N) ξ ((r : ℝ) : ℂ) t (MomentDuhamel.lkFun B E N r M σ) a :=
    fun r => ukerObsT_eq_Uker_lkFun B E N σ a t hKdef hM r
  -- T58: the pointwise drift identity, with `F = driftF`
  choose dv hdv hdveq using fun b : LoopArg (B.L N) (n + 2) =>
    DriftDef.drift_split_gen B E N u hM hz σ b hm
  -- the time derivative, by variation of constants
  have hpath := hasDerivAt_Uker_path (B.L N) hL3 hv ht (Y := fun r =>
    MomentDuhamel.lkFun B E N r M σ) (Y' := dv) hdv a
  -- the generator term, pushed through the propagator
  have hC2 : ∀ b : LoopArg (B.L N) (n + 2),
      ContDiff ℝ 2 (fun M' =>
        loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - K u b) := by
    intro b
    have hwf : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
    exact (bddC2_loopObs hz (abs_pos.mpr hz) le_rfl hwf).contDiff.sub contDiff_const
  have hgen : genD B.toDims N (ukerObsT B.toDims N E (List.ofFn σ) ξ t K a u) M
      = Uker (B.L N) ξ ((u : ℝ) : ℂ) t (MomentDuhamel.genLK B E N u M σ) a := by
    have hfun : (ukerObsT B.toDims N E (List.ofFn σ) ξ t K a u)
        = fun M' => ∑ b : LoopArg (B.L N) (n + 2),
            (∏ i, edgeKer (B.L N) (ξ i) ((u : ℝ) : ℂ) t (a i) (b i))
              * (loopObs B.toDims N (zt E u) (LoopData.idx (σ, b)) M' - K u b) := rfl
    rw [hfun, genD_finsetSum Finset.univ _ _ (fun b _ => hC2 b) M, Uker_apply]
    exact Finset.sum_congr rfl fun b _ => by
      rw [genD_loopObs_eq_genLK B E N u hM hz σ b (K u b)]
  refine ⟨Uker (B.L N) ξ ((u : ℝ) : ℂ) t dv a
      - Uker (B.L N) ξ ((u : ℝ) : ℂ) t
          (ThetaOp (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ)) a,
    hpath.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hEq r), ?_⟩
  rw [hgen]
  -- the two `Θ`'s cancel and `driftF` is what is left
  rw [Uker_apply, Uker_apply, Uker_apply, Uker_apply, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := hdveq b
  have hgs : SumZeroDyn.genS (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ) b
      = ThetaOp (B.L N) ξ ((u : ℝ) : ℂ) (MomentDuhamel.lkFun B E N u M σ) b := rfl
  rw [hgs] at hb
  linear_combination (∏ i, edgeKer (B.L N) (ξ i) ((u : ℝ) : ℂ) t (a i) (b i)) * hb

end Band

/-! ### The time derivative of `Ψ = |Ψ₁|^{2p}`, in the real first-order form -/

/-- `RBM.Gauss.timeD1` of the moment route's `Ψ`, written as
`2p ‖Ψ₁‖^{2p-2} Re(Ψ̄₁ ∂_uΨ₁)` — the shape that pairs with `RBM.Gauss.genMomentPt_le_re`. -/
theorem timeD1_momentObsT_re (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m)
    (ξ : Fin m → ℂ) (t : ℂ) (K K' : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    (p : ℕ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    timeD1 (momentObsT d N Ev σ ξ t K a p) u M
      = ((2 * (p : ℝ) * ‖ukerObsT d N Ev σ ξ t K a u M‖ ^ (2 * p - 2)
          * ((starRingEnd ℂ) (ukerObsT d N Ev σ ξ t K a u M)
              * ukerObsTDeriv d N Ev σ ξ t K K' a u M).re : ℝ) : ℂ) := by
  rw [timeD1_eq_of_hasDerivAt (hasDerivAt_momentObsT Ev hσ ξ t K K' a p hz hK M)]
  set Ψ := ukerObsT d N Ev σ ξ t K a u M with hΨ
  set D := ukerObsTDeriv d N Ev σ ξ t K K' a u M with hD
  rw [mul_conj_eq Ψ, add_conj_mul D Ψ]
  have hpow : (((‖Ψ‖ ^ 2 : ℝ) : ℂ)) ^ (p - 1) = (((‖Ψ‖ ^ (2 * p - 2) : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_pow, ← pow_mul]
    congr 2
    omega
  rw [hpow]
  push_cast
  ring

section Band2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The pointwise integrand of (5.20), with the drift pinned.**

At a Hermitian matrix,

  `∂_u |Ψ₁|^{2p} + 𝓛 |Ψ₁|^{2p} ≤ 2p |Ψ₁|^{2p-1} |(U_{u,t} ∘ F_u)_a|
        + p(2p-1) |Ψ₁|^{2p-2} ∑_α S_α ‖∂_α Ψ₁‖²`,

`Ψ₁ = (U_{u,t} ∘ (L-K)_u)_a` and `F = RBM.DriftDef.driftF`.  The two first-order terms are
added *before* the modulus is taken, which is what makes the `Θ` of the propagator cancel
against the `genS` of the drift identity; that cancellation is
`RBM.Gauss.hasDerivAt_ukerObsT_drift`. -/
theorem timeD1_add_genMomentPt_le_driftF (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {K K' : ℝ → LoopArg (B.toDims.L N) (n + 2) → ℂ}
    (hKdef : ∀ (r : ℝ) (b : LoopArg (B.L N) (n + 2)),
      K r b = B.Kval E N r (LoopData.idx (σ, b)))
    (hK : ∀ b, HasDerivAt (fun r : ℝ => K r b) (K' u b) u)
    {p : ℕ} (hp : 1 ≤ p)
    (hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (hv : ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (ht : ∀ i, ‖t * xiOf (mSigma E) σ i‖ < 1) :
    (timeD1 (momentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a p) u M).re
        + genMomentPt B.toDims N
            (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u) p M
      ≤ 2 * (p : ℝ)
            * ‖ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u M‖ ^ (2 * p - 1)
            * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
                (DriftDef.driftF B E N u M σ) a‖
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * ‖ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u M‖ ^ (2 * p - 2)
            * quadVar B.toDims N
                (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t K a u) M := by
  classical
  set ξ : Fin (n + 2) → ℂ := xiOf (mSigma E) σ with hξ
  have hlen : (List.ofFn σ).length = n + 2 := List.length_ofFn
  set Ψ := ukerObsT B.toDims N E (List.ofFn σ) ξ t K a u M with hΨ
  set D := ukerObsTDeriv B.toDims N E (List.ofFn σ) ξ t K K' a u M with hD
  set G := Uker (B.L N) ξ ((u : ℝ) : ℂ) t (DriftDef.driftF B E N u M σ) a with hG
  -- the drift identity, with the derivative identified
  obtain ⟨D₀, hD₀, hD₀eq⟩ :=
    hasDerivAt_ukerObsT_drift B E N u hM hz σ a t hKdef hm hv ht
  have hDD : D₀ = D :=
    hD₀.unique (hasDerivAt_ukerObsT E hlen ξ t K K' a hz hK M)
  rw [hDD] at hD₀eq
  -- the two first-order terms
  have hC2 : ContDiff ℝ 2 (ukerObsT B.toDims N E (List.ofFn σ) ξ t K a u) :=
    (bddC2_ukerObs hz (abs_pos.mpr hz) le_rfl hlen ξ ((u : ℝ) : ℂ) t (K u) a).contDiff
  have h1 : (timeD1 (momentObsT B.toDims N E (List.ofFn σ) ξ t K a p) u M).re
      = 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * ((starRingEnd ℂ) Ψ * D).re := by
    rw [timeD1_momentObsT_re E hlen ξ t K K' a p hz hK M, Complex.ofReal_re]
  have h2 := genMomentPt_le_re (F := ukerObsT B.toDims N E (List.ofFn σ) ξ t K a u) hC2 hp M
  -- the first-order terms add before the modulus is taken
  have hadd : ((starRingEnd ℂ) Ψ * D).re
      + ((starRingEnd ℂ) Ψ
          * genD B.toDims N (ukerObsT B.toDims N E (List.ofFn σ) ξ t K a u) M).re
      = ((starRingEnd ℂ) Ψ * G).re := by
    rw [← Complex.add_re, ← mul_add, hD₀eq]
  have hre : ((starRingEnd ℂ) Ψ * G).re ≤ ‖Ψ‖ * ‖G‖ := by
    calc ((starRingEnd ℂ) Ψ * G).re ≤ |((starRingEnd ℂ) Ψ * G).re| := le_abs_self _
      _ ≤ ‖(starRingEnd ℂ) Ψ * G‖ := Complex.abs_re_le_norm _
      _ = ‖Ψ‖ * ‖G‖ := by rw [norm_mul, RCLike.norm_conj]
  have hpow : ‖Ψ‖ ^ (2 * p - 2) * ‖Ψ‖ = ‖Ψ‖ ^ (2 * p - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hcoef : (0 : ℝ) ≤ 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) := by positivity
  have hstep : 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * ((starRingEnd ℂ) Ψ * G).re
      ≤ 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 1) * ‖G‖ := by
    calc 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * ((starRingEnd ℂ) Ψ * G).re
        ≤ 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 2) * (‖Ψ‖ * ‖G‖) :=
          mul_le_mul_of_nonneg_left hre hcoef
      _ = 2 * (p : ℝ) * ‖Ψ‖ ^ (2 * p - 1) * ‖G‖ := by rw [← hpow]; ring
  rw [h1]
  nlinarith [h2, hadd, hstep]

/-! ### Satisfiability

The two statements above are asserted at a Hermitian matrix with `K` **pinned** to
`RBM.Band.Kval` (`hKdef`), so neither the drift nor the primitive is data a caller may choose.
What has to be checked is the opposite failure mode: that the hypotheses can all hold at once,
at the paper's own scaling rather than at a degenerate point.

`Kprim` is the `u`-derivative of `K`, also pinned — it is `RBM.primRhs`, not a free tensor. -/

/-- `∂_u K_u`, pinned to `RBM.primRhs` (T58's `RBM.hasDerivAt_Kgen_all`). -/
noncomputable def Kprim (B : Band Ω) (E : ℝ) (N : ℕ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (r : ℝ) (b : LoopArg (B.toDims.L N) (n + 2)) : ℂ :=
  primRhs (B.L N) (B.W N) (B.Kval E N r) (LoopData.idx (σ, b))

/-- `RBM.Band.Kval` is differentiable in the time with derivative `RBM.Gauss.Kprim`. -/
theorem hasDerivAt_Kval_Kprim (B : Band Ω) (E : ℝ) (N : ℕ) {u : ℝ}
    (hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (b : LoopArg (B.toDims.L N) (n + 2)) :
    HasDerivAt (fun r : ℝ => B.Kval E N r (LoopData.idx (σ, b))) (Kprim B E N σ u b) u :=
  hasDerivAt_Kgen_all (L := B.L N) (B.W N) (mSigma E) (B.three_le_L N) hm
    (LoopData.idx (σ, b)) (LoopData.idx_wf _) (by rw [LoopData.idx_length]; omega)

/-- **The two side conditions of `RBM.Gauss.hasDerivAt_ukerObsT_drift` discharged from the
paper's standing assumptions**, at the flow matrix.  Nothing is chosen: `E` is the spectral
parameter of Theorem 2.6, `u` and `v` are two times of the window `[0, 1)`, `K` is
`RBM.Band.Kval`, `∂_uK` is `RBM.Gauss.Kprim`, and the drift is `RBM.DriftDef.driftF`.

This is the positive satisfiability witness: the hypotheses hold **simultaneously** at the
critical scaling `t = v ↑ 1`, not only at a degenerate point.  The degenerate points are
checked separately below. -/
theorem hasDerivAt_ukerObsT_drift_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ)
    {u v : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (ω : Ω) :
    ∃ D : ℂ,
      HasDerivAt (fun r : ℝ =>
          ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a r (X.H N u ω)) D u
        ∧ D + genD B.toDims N
              (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) (X.H N u ω)
          = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (DriftDef.driftF B E N u (X.H N u ω) σ) a := by
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  have hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := by
    intro s s'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hu1
  have hxi : ∀ (r : ℝ), 0 ≤ r → r < 1 → ∀ i, ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro r hr0 hr1 i
    rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hr1
  exact hasDerivAt_ukerObsT_drift B E N u (X.hermitian N u ω) hz σ a ((v : ℝ) : ℂ)
    (fun _ _ => rfl) hm (hxi u hu0 hu1) (hxi v hv0 hv1)

/-- **Degenerate check: `ω = 0`.**  At the sample point where the flow matrix is `0` the
identity still has content — `0` is Hermitian, the resolvent is `-z⁻¹`, and every hypothesis
is discharged exactly as above.  (This is the check the T164 incident makes mandatory: a
statement quantified over matrices must be tested where the matrix degenerates.) -/
theorem hasDerivAt_ukerObsT_drift_at_zero (B : Band Ω) (E : ℝ) (N : ℕ)
    {u v : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) :
    ∃ D : ℂ,
      HasDerivAt (fun r : ℝ =>
          ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a r 0) D u
        ∧ D + genD B.toDims N
              (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) 0
          = Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (DriftDef.driftF B E N u 0 σ) a := by
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  have hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := by
    intro s s'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hu1
  have hxi : ∀ (r : ℝ), 0 ≤ r → r < 1 → ∀ i, ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro r hr0 hr1 i
    rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hr1
  exact hasDerivAt_ukerObsT_drift B E N u Matrix.isHermitian_zero hz σ a ((v : ℝ) : ℂ)
    (fun _ _ => rfl) hm (hxi u hu0 hu1) (hxi v hv0 hv1)

/-- **The pointwise integrand bound with every hypothesis discharged**, at the flow matrix and
the paper's scaling: this is `RBM.Gauss.timeD1_add_genMomentPt_le_driftF` with no free data
left except `p ≥ 1`.  Both `K` and `∂_uK` are pinned (`RBM.Band.Kval`, `RBM.Gauss.Kprim`). -/
theorem timeD1_add_genMomentPt_le_driftF_flow (B : Band Ω) (X : Sample B) (E : ℝ) (N : ℕ)
    {u v : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (ω : Ω)
    {p : ℕ} (hp : 1 ≤ p) :
    (timeD1 (momentObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
          (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a p) u (X.H N u ω)).re
        + genMomentPt B.toDims N
            (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
              (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) p (X.H N u ω)
      ≤ 2 * (p : ℝ)
            * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N u ω σ) a‖ ^ (2 * p - 1)
            * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (DriftDef.driftF B E N u (X.H N u ω) σ) a‖
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N u ω σ) a‖ ^ (2 * p - 2)
            * quadVar B.toDims N
                (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                  (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) (X.H N u ω) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  have hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := by
    intro s s'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hu1
  have hxi : ∀ (r : ℝ), 0 ≤ r → r < 1 → ∀ i, ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro r hr0 hr1 i
    rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
    exact hr1
  have hbr := ukerObsT_flow B X E N σ a ((v : ℝ) : ℂ) (K := fun r b =>
    B.Kval E N r (LoopData.idx (σ, b))) (fun _ _ => rfl) u ω
  have hmain := timeD1_add_genMomentPt_le_driftF B E N u (X.hermitian N u ω) hz σ a
    ((v : ℝ) : ℂ) (K := fun r b => B.Kval E N r (LoopData.idx (σ, b)))
    (K' := Kprim B E N σ) (fun _ _ => rfl)
    (fun b => hasDerivAt_Kval_Kprim B E N hm σ b) hp hm (hxi u hu0 hu1) (hxi v hv0 hv1)
  rwa [hbr] at hmain

end Band2

end Gauss

end RBM

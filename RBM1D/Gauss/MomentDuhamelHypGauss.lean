/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelBddT
import RBM1D.Gauss.Step6HierarchyGauss
import RBM1D.Gauss.DischargeBDG
import RBM1D.Gauss.SteinMatrix

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

## The five side conditions (T212)

`RBM.MomentDuhamel.momentIneq_of_derivBound` consumes eight things per `(p, N, σ, v, a)`.
T206 supplied the pointwise inequality (its last item) and the bridge; **T212 supplies the
five integrability side conditions**, so that
`RBM.Gauss.momentIneq_of_derivBound_gauss` — the Gaussian form of that theorem — asks only for
the derivative on the *open* window and for the pointwise inequality.  The five are

1. the window bound on `ψ` (`RBM.Gauss.exists_bdd_psi_gauss`),
2. `ContinuousOn` of `u ↦ E|Ψ₁|^{2p}` (`RBM.Gauss.continuousOn_integral_psi_gauss`),
3. the interval integrability of `φ'` (`RBM.Gauss.intervalIntegrable_phi'_gauss`),
4. that of `u ↦ ‖U ∘ F_u‖_{2p}` and of `u ↦ ‖(U⊗U) ∘ (E⊗E)‖_p`
   (`RBM.Gauss.intervalIntegrable_momNorm_driftF_gauss`,
   `RBM.Gauss.intervalIntegrable_momNorm_eeFun_gauss`),
5. that of the product `ψ · f` (`RBM.Gauss.intervalIntegrable_psi_mul_driftF_gauss`),

and all five come from one mechanism: the deterministic envelope `‖G‖ ≤ (Im z_u)⁻¹` of T77 —
uniform on the window `[s_N, v] ⊆ [0, 1)`, **not** on `[0, 1)` itself, where it does not exist
(T154) — plus dominated convergence, which is the timed version of the argument
`RBM.Gauss.integrable_lkT_pow` runs at a fixed time.  The drift integrand needs no new size
estimate: `RBM.Gauss.uker_driftF_eq` turns `(U ∘ F_u)_a` into `∂_u Ψ₁ + 𝓛 Ψ₁`, both of which
T196's `RBM.Gauss.norm_ukerObsTDeriv_le` and `RBM.Gauss.bddC2C_ukerObsT` already bound.  The
primitive's own window bound is a theorem too (`RBM.Gauss.exists_bdd_Kval_Kprim`: `K` and
`∂_u K` are continuous and the loop arguments form a finite type), so no `cK` is assumed.

## What is still **not** here (two items T206 did not list)

1. **The quadratic variation is not yet the interface's `E ⊗ E`.**  `RBM.MomentDuhamel.MomentIneq`
   has `‖(U⊗U) ∘ (E⊗E)_{a,a}‖_p` on the right, i.e. `RBM.Uker` at the doubled charges
   `RBM.SumZeroDyn.xi2` applied to `RBM.MomentDuhamel.eeFun`.  What exists is
   `RBM.Gauss.quadVarPairs_Uker` (`quadVar(Ψ₁) = ∑_{ij} ‖(U ∘ E^{(M)}(i,j))_a‖²`) and, for a
   *single* loop, `RBM.Gauss.eeRaw_self_eq_quadVarPairs` plus the gluing (5.22)
   `RBM.Gauss.eeEdge_eq_sum_SB`.  The **bilinear, `U`-conjugated** form of that gluing —
   `∑_{ij} (U ∘ E^{(M)}(i,j))_a · conj((U ∘ E^{(M)}(i,j))_{a'}) = (U⊗U ∘ eeArg)_{a,a'}` — is
   not in the repository (`RBM1D/Hierarchy/EEBridge.lean` contains no `RBM.Uker`).
2. **The `Q_t` route (`MomentIneqQ`) is untouched.**  Its drift identity needs `∂_u Q_u`, which
   produces the two extra terms `RBM.SumZeroDyn.commS` and `RBM.SumZeroDyn.varthetaDot` of
   (5.91); nothing here differentiates `RBM.Qop` in the time.  (T214 has since opened
   `RBM1D/Gauss/MomentDuhamelQ.lean` for it.)

Consequently `momentDuhamelHyp_gauss` still does not exist, and this file does not create it:
what is missing is the `U`-conjugated bilinear form of (5.22) (T213) and the `Q_t` route
(T214), not the integrability.

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

/-! ### Interval integrability from a deterministic envelope (T212)

`RBM.MomentDuhamel.momentIneq_of_derivBound` asks, per `(p, N, σ, v, a)`, for five side
conditions besides the derivative and the pointwise inequality: a window bound on `ψ`, the
`ContinuousOn` of `u ↦ E|Ψ₁|^{2p}`, and the interval integrability of `φ'`, of the two drift
integrands, and of the product `ψ · f`.  All of them are instances of one statement: a family
of random variables that is **continuous in the time at each sample point** and **bounded by a
deterministic constant over the window** has continuous — hence interval integrable — moments.

The constant is the envelope `‖G‖ ≤ (Im z_u)⁻¹` of T77, which on the paper's window
`[s_N, v] ⊆ [0, 1)` is uniform because `Im z_u = (1-u) Im m_E ≥ (1-v) Im m_E > 0`.  Nothing
here quantifies `u` over all of `ℝ`: at `u = 1` no envelope exists (T154). -/

section Envelope

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A moment is continuous in the time, under a deterministic envelope.**

Dominated convergence (`MeasureTheory.continuousOn_of_dominated`) with the *constant*
dominating function `|C|^q`, which is integrable because the measure is finite.  This is the
timed version of the argument `RBM.Gauss.integrable_lkT_pow` runs at a fixed time. -/
theorem continuousOn_integral_abs_pow_of_envelope {P : Measure Ω} [IsFiniteMeasure P]
    {S : Set ℝ} {f : ℝ → Ω → ℝ} {C : ℝ} (q : ℕ)
    (hmeas : ∀ u ∈ S, AEStronglyMeasurable (f u) P)
    (hbd : ∀ u ∈ S, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) S) :
    ContinuousOn (fun u => ∫ ω, |f u ω| ^ q ∂P) S := by
  refine MeasureTheory.continuousOn_of_dominated (bound := fun _ : Ω => |C| ^ q) ?_ ?_
    (integrable_const _) ?_
  · intro u hu
    have h := ((hmeas u hu).norm).pow q
    have he : ((fun ω => ‖f u ω‖) ^ q) = fun ω => |f u ω| ^ q := by
      funext ω; simp [Real.norm_eq_abs]
    rwa [he] at h
  · refine fun u hu => Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) q)]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hbd u hu ω).trans (le_abs_self C)) q
  · exact Filter.Eventually.of_forall fun ω => ((hcont ω).abs).pow q

/-- **`RBM.MomentDuhamel.momNorm` is continuous in the time, under a deterministic
envelope.** -/
theorem continuousOn_momNorm_of_envelope {P : Measure Ω} [IsFiniteMeasure P]
    {S : Set ℝ} {f : ℝ → Ω → ℝ} {C : ℝ} (q : ℕ)
    (hmeas : ∀ u ∈ S, AEStronglyMeasurable (f u) P)
    (hbd : ∀ u ∈ S, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) S) :
    ContinuousOn (fun u => MomentDuhamel.momNorm P q (f u)) S := by
  have hb : ContinuousOn (fun u => ∫ ω, |f u ω| ^ q ∂P) S :=
    continuousOn_integral_abs_pow_of_envelope q hmeas hbd hcont
  exact hb.rpow_const fun _ _ => Or.inr (by positivity)

/-- **The interval integrability the two drift integrands of (5.20) need**, from the same
envelope.  The window is the closed `[a, b]` the inequality speaks on. -/
theorem intervalIntegrable_momNorm_of_envelope {P : Measure Ω} [IsFiniteMeasure P]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → Ω → ℝ} {C : ℝ} (q : ℕ)
    (hmeas : ∀ u ∈ Set.Icc a b, AEStronglyMeasurable (f u) P)
    (hbd : ∀ u ∈ Set.Icc a b, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) (Set.Icc a b)) :
    IntervalIntegrable (fun u => MomentDuhamel.momNorm P q (f u)) volume a b :=
  (continuousOn_momNorm_of_envelope q hmeas hbd hcont).intervalIntegrable_of_Icc hab

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

/-- The pair map `u ↦ (u, H_u(ω))` the joint regularity statements are composed with. -/
theorem continuous_pair_Hflow (d : Dims) (N : ℕ) (ω : Ω d) :
    Continuous fun u : ℝ => ((u, Hflow d N u ω) : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ) :=
  continuous_id.prodMk (continuous_Hflow_time d N ω)

/-- **`u ↦ (U_{u,t} ∘ (L - K)_u)_a(H_u ω)` is continuous on the window.**

`RBM.Gauss.differentiableAt_ukerObsT_pair` (T196) is joint differentiability in `(u, M)`; the
flow is continuous in `u` by `RBM.Gauss.continuous_Hflow_time`, so the composite is continuous.
No Hermitian side condition is needed: `RBM.Gauss.loopObs` carries `RBM.Gauss.hermCLM`. -/
theorem continuousOn_ukerObsT_flow (Ev : ℝ) {σ : List Bool} {m : ℕ}
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {S : Set ℝ} (hzim : ∀ u ∈ S, (zt Ev u).im ≠ 0)
    (hK : ∀ u ∈ S, ∀ b, DifferentiableAt ℝ (fun r : ℝ => K r b) u) (ω : Ω d) :
    ContinuousOn (fun u : ℝ => ukerObsT d N Ev σ ξ t K a u (Hflow d N u ω)) S := by
  intro u hu
  have hjoint : ContinuousAt (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      ukerObsT d N Ev σ ξ t K a q.1 q.2) (u, Hflow d N u ω) :=
    (differentiableAt_ukerObsT_pair Ev ξ t K a (hzim u hu) (hK u hu) _).continuousAt
  have hcomp := ContinuousAt.comp (x := u)
    (g := fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => ukerObsT d N Ev σ ξ t K a q.1 q.2)
    (f := fun r : ℝ => ((r, Hflow d N r ω) : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ))
    hjoint ((continuous_pair_Hflow d N ω).continuousAt)
  rw [Function.comp_def] at hcomp
  exact hcomp.continuousWithinAt

/-- **The value bound on `(U_{u,t} ∘ (L - K)_u)_a`, uniform over the window and over all
matrices** — the `bdd₀` of `RBM.Gauss.bddC2C_ukerObsT` with the `u`-dependence removed by
compactness of the window, exactly as `RBM.Gauss.bdd₀_momentObsT` does for `|·|^{2p}`. -/
theorem exists_bdd₀_ukerObsT (Ev : ℝ) {σ : List Bool} {m : ℕ} (hσ : σ.length = m) (hm : 1 ≤ m)
    (ξ : Fin m → ℂ) (t : ℂ) (K : ℝ → LoopArg (d.L N) m → ℂ) (a : LoopArg (d.L N) m)
    {u₀ u₁ η cK : ℝ} (hη : 0 < η) (hcK : 0 ≤ cK)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt Ev u).im|)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b, ‖K u b‖ ≤ cK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖ukerObsT d N Ev σ ξ t K a u M‖ ≤ C := by
  classical
  set Cloop : ℝ := η⁻¹ ^ m * ((d.W N : ℝ))⁻¹ ^ (m - 1) with hCloop
  set C₀ : ℝ := Cloop + cK with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hwf : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).WF := fun b => by
    show σ.length = (List.ofFn b).length
    rw [hσ, List.length_ofFn]
  have hlen : ∀ b : LoopArg (d.L N) m, (LoopIdx.mk σ (List.ofFn b)).a.length = m := fun b => by
    show (List.ofFn b).length = m
    rw [List.length_ofFn]
  set Q : ℝ → ℝ := fun u => ukerCoefBd ξ t a u * C₀ with hQ
  have hpt : ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖ukerObsT d N Ev σ ξ t K a u M‖ ≤ Q u := by
    intro u hu M
    have hval : ∀ b : LoopArg (d.L N) m,
        ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖ ≤ C₀ := by
      intro b
      have h : ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ ≤ Cloop := by
        have h0 := norm_loopObs_le hη (hzim u hu) _ (hwf b) (by rw [hlen b]; exact hm) M
        rw [hlen b] at h0
        exact h0
      calc ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M - K u b‖
          ≤ ‖loopObs d N (zt Ev u) ⟨σ, List.ofFn b⟩ M‖ + ‖K u b‖ := norm_sub_le _ _
        _ ≤ Cloop + cK := add_le_add h (hKb u hu b)
    exact norm_ukerObsT_le Ev σ ξ t K a u M hC₀0 hval
  have hQc : Continuous Q := (continuous_ukerCoefBd ξ t a).mul continuous_const
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn
    (f := Q) hQc.continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu M => ?_⟩
  exact le_trans (hpt u hu M)
    (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

end FlowTime

/-! ### The envelope of the drift integrand

`RBM.Gauss.hasDerivAt_ukerObsT_drift` says `(U ∘ F_u)_a = ∂_u Ψ₁ + 𝓛 Ψ₁`, and both summands
on the right are **already** bounded uniformly over the window by T196's machinery
(`RBM.Gauss.norm_ukerObsTDeriv_le` and `RBM.Gauss.bddC2C_ukerObsT`'s `bdd₂` through
`RBM.Gauss.norm_coordD2_le`).  So the drift integrand of (5.20) needs no new size estimate:
the envelope `‖G‖ ≤ (Im z_u)⁻¹` that bounds `Ψ₁` bounds `U ∘ F_u` too. -/

section DriftEnvelope

/-- `‖U_{u,t} ∘ A‖ ≤ ukerRow · sup‖A‖` — the row `ℓ¹` bound of the propagator, with the same
row size `RBM.Gauss.ukerRow` that T196's uniform bounds are organised around. -/
theorem norm_Uker_apply_le_ukerRow {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) (u : ℝ)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) {C : ℝ} (hA : ∀ b, ‖A b‖ ≤ C) :
    ‖Uker L ξ ((u : ℝ) : ℂ) t A a‖ ≤ ukerRow ξ t a u * C := by
  rw [Uker_apply, ukerRow, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hA b) (norm_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`(U_{u,t} ∘ F_u)_a = ∂_u(U ∘ (L-K))_a + 𝓛(U ∘ (L-K))_a`, with both sides pinned.**

The drift identity `RBM.Gauss.hasDerivAt_ukerObsT_drift` produces the derivative
existentially; `RBM.Gauss.hasDerivAt_ukerObsT` identifies it with the *definition*
`RBM.Gauss.ukerObsTDeriv`, so the identity becomes an equation between two explicit
expressions.  This is what turns the drift integrand's size and continuity into statements
about `Ψ₁` alone. -/
theorem uker_driftF_eq (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    (hm : ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (hv : ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (ht : ∀ i, ‖t * xiOf (mSigma E) σ i‖ < 1) :
    Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t (DriftDef.driftF B E N u M σ) a
      = ukerObsTDeriv B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t
            (fun r b => B.Kval E N r (LoopData.idx (σ, b))) (Kprim B E N σ) a u M
        + genD B.toDims N
            (ukerObsT B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t
              (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a u) M := by
  obtain ⟨D, hD, hDeq⟩ :=
    hasDerivAt_ukerObsT_drift B E N u hM hz σ a t (fun _ _ => rfl) hm hv ht
  have hσlen : (List.ofFn σ).length = n + 2 := List.length_ofFn
  have hD2 := hasDerivAt_ukerObsT (d := B.toDims) (N := N) E hσlen
    (xiOf (mSigma E) σ) t (fun r b => B.Kval E N r (LoopData.idx (σ, b)))
    (Kprim B E N σ) a hz (fun b => hasDerivAt_Kval_Kprim B E N hm σ b) M
  rw [← hDeq, hD.unique hD2]
  rfl

end DriftEnvelope

/-! ### `𝓛F` from a uniform second-derivative bound -/

/-- `‖𝓛F‖ ≤ ‖∂²F‖ · ½∑_α S_α ‖B_α‖²`, the crude bound the drift integrand needs. -/
theorem norm_genD_le {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C : ℝ}
    (hC : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, ‖fderiv ℝ (fderiv ℝ F) M‖ ≤ C)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖genD d N F M‖
      ≤ C * ((2 : ℝ)⁻¹ * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
          * (‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖)) := by
  have hstep : ‖genD d N F M‖
      ≤ (2 : ℝ)⁻¹ * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
          * (C * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖) := by
    rw [genD, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_coordD2_le hC M q) (NNReal.coe_nonneg _)
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-! ### The uniform envelope of the drift integrand of (5.20) -/

section DriftBound

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`u ↦ ‖(U_{u,t} ∘ F_u)_a(M)‖` is bounded on the window, uniformly in the Hermitian
matrix.**

Everything comes from `RBM.Gauss.uker_driftF_eq`: the drift integrand is
`∂_u Ψ₁ + 𝓛 Ψ₁`, the first summand bounded by `RBM.Gauss.norm_ukerObsTDeriv_le` (through the
envelope `RBM.norm_loopObs_le` for the value and `RBM.Gauss.norm_zMotion_le` for the
`z`-motion), the second by `RBM.Gauss.norm_genD_le` on `RBM.Gauss.bddC2C_ukerObsT`'s `bdd₂`.
The only `u`-dependence left is in `RBM.Gauss.ukerCoefBd` and `RBM.Gauss.ukerRow`, continuous
functions of `u` alone, which the compact window bounds. -/
theorem exists_bdd_uker_driftF (B : Band Ω) (E : ℝ) (N : ℕ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) (t : ℂ)
    {u₀ u₁ η cK : ℝ} (hη : 0 < η)
    (hzim : ∀ u ∈ Set.Icc u₀ u₁, η ≤ |(zt E u).im|)
    (hKb : ∀ u ∈ Set.Icc u₀ u₁, ∀ b : LoopArg (B.toDims.L N) (n + 2),
      ‖B.Kval E N u (LoopData.idx (σ, b))‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc u₀ u₁, ∀ b : LoopArg (B.toDims.L N) (n + 2),
      ‖Kprim B E N σ u b‖ ≤ cK)
    (hmw : ∀ u ∈ Set.Icc u₀ u₁, ∀ s s' : Bool, ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    (hvw : ∀ u ∈ Set.Icc u₀ u₁, ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (ht : ∀ i, ‖t * xiOf (mSigma E) σ i‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc u₀ u₁, ∀ M : Matrix (B.Idx N) (B.Idx N) ℂ, M.IsHermitian →
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t (DriftDef.driftF B E N u M σ) a‖ ≤ C := by
  classical
  have hσlen : (List.ofFn σ).length = n + 2 := List.length_ofFn
  have hwf : ∀ b : LoopArg (B.toDims.L N) (n + 2),
      (LoopIdx.mk (List.ofFn σ) (List.ofFn b)).WF := fun b => by
    show (List.ofFn σ).length = (List.ofFn b).length
    rw [hσlen, List.length_ofFn]
  have hlen : ∀ b : LoopArg (B.toDims.L N) (n + 2),
      (LoopIdx.mk (List.ofFn σ) (List.ofFn b)).length = n + 2 := fun b => by
    show (List.ofFn b).length = n + 2
    rw [List.length_ofFn]
  -- the two deterministic envelopes
  set Cloop : ℝ := η⁻¹ ^ (n + 2) * ((B.toDims.W N : ℝ))⁻¹ ^ (n + 2 - 1) with hCloop
  set Czm : ℝ := ((n + 2 : ℕ) : ℝ) * (max ‖mSigma E true‖ ‖mSigma E false‖ *
      ((B.toDims.W N : ℝ) * ((Fintype.card (ZMod (B.toDims.L N)) : ℝ) *
        (η⁻¹ ^ (n + 2 + 1) * ((B.toDims.W N : ℝ))⁻¹ ^ (n + 2))))) with hCzm
  set Cbig : ℝ := max (Cloop + cK) (Czm + cK) with hCbig
  set G : ℝ → ℝ := fun u =>
    ukerCoefBd (xiOf (mSigma E) σ) t a u * Cbig
      + ukerRow (xiOf (mSigma E) σ) t a u
          * ((Fintype.card (B.toDims.Idx N) : ℝ)
              * (((n + 2 : ℕ) : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ (n + 2)))
        * ((2 : ℝ)⁻¹ * ∑ q ∈ usedCoord B.toDims N,
            (gvar B.toDims (crd B.toDims N q) : ℝ)
              * (‖Bmat B.toDims N q.1 q.2.1 q.2.2‖
                  * ‖Bmat B.toDims N q.1 q.2.1 q.2.2‖)) with hG
  have hGc : Continuous G :=
    ((continuous_ukerCoefBd (xiOf (mSigma E) σ) t a).mul continuous_const).add
      (((continuous_ukerRow (xiOf (mSigma E) σ) t a).mul continuous_const).mul continuous_const)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := u₀) (b := u₁)).exists_bound_of_continuousOn
    (f := G) hGc.continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu M hM => ?_⟩
  have hz : (zt E u).im ≠ 0 := im_zt_ne_zero_of_le hη (hzim u hu)
  have hval : ∀ b : LoopArg (B.toDims.L N) (n + 2),
      ‖loopObs B.toDims N (zt E u) ⟨List.ofFn σ, List.ofFn b⟩ M
        - B.Kval E N u (LoopData.idx (σ, b))‖ ≤ Cbig := by
    intro b
    have h : ‖loopObs B.toDims N (zt E u) ⟨List.ofFn σ, List.ofFn b⟩ M‖ ≤ Cloop := by
      have h0 := norm_loopObs_le hη (hzim u hu) _ (hwf b) (by rw [show
        (LoopIdx.mk (List.ofFn σ) (List.ofFn b)).a.length = n + 2 from hlen b]; omega) M
      rw [show (LoopIdx.mk (List.ofFn σ) (List.ofFn b)).a.length = n + 2 from hlen b] at h0
      exact h0
    refine le_trans (le_trans (norm_sub_le _ _) (add_le_add h (hKb u hu b))) ?_
    exact le_max_left _ _
  have hder : ∀ b : LoopArg (B.toDims.L N) (n + 2),
      ‖zMotion (B.toDims.L N) (B.toDims.W N) (mSigma E) (hermCLM (B.Idx N) M) (zt E u)
          ⟨List.ofFn σ, List.ofFn b⟩ - Kprim B E N σ u b‖ ≤ Cbig := by
    intro b
    have h : ‖zMotion (B.toDims.L N) (B.toDims.W N) (mSigma E) (hermCLM (B.Idx N) M) (zt E u)
        ⟨List.ofFn σ, List.ofFn b⟩‖ ≤ Czm := by
      have h0 := norm_zMotion_le (L := B.toDims.L N) (W := B.toDims.W N)
        (isHermitian_hermCLM M) hη (hzim u hu) (mSigma E) _ (hwf b)
      rw [hlen b] at h0
      exact h0
    refine le_trans (le_trans (norm_sub_le _ _) (add_le_add h (hK'b u hu b))) ?_
    exact le_max_right _ _
  have hbase := bddC2C_ukerObsT (d := B.toDims) (N := N) hη hz (hzim u hu) hσlen
    (xiOf (mSigma E) σ) t (fun r b => B.Kval E N r (LoopData.idx (σ, b))) a
    (fun b => hKb u hu b)
  have h1 : ‖ukerObsTDeriv B.toDims N E (List.ofFn σ) (xiOf (mSigma E) σ) t
        (fun r b => B.Kval E N r (LoopData.idx (σ, b))) (Kprim B E N σ) a u M‖
      ≤ ukerCoefBd (xiOf (mSigma E) σ) t a u * Cbig :=
    norm_ukerObsTDeriv_le (d := B.toDims) (N := N) (C := Cbig) E (List.ofFn σ)
      (xiOf (mSigma E) σ) t (fun r b => B.Kval E N r (LoopData.idx (σ, b)))
      (Kprim B E N σ) a u M hval hder
  have h2 := norm_genD_le (fun M' => hbase.bdd₂ M') M
  have hsum : ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (DriftDef.driftF B E N u M σ) a‖ ≤ G u := by
    rw [uker_driftF_eq B E N u hM hz σ a t (hmw u hu) (hvw u hu) ht]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  exact hsum.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

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

Loops of length `≥ 2` are differentiable in the time (`RBM.hasDerivAt_Kgen_all`, T58); loops
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

/-- `primBilLen` is continuous when both tensors are. -/
theorem continuousOn_primBilLen (W lK : ℕ) {S : Set X} {Y Z : X → LoopIdx (ZMod L) → ℂ}
    (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Y x J) S)
    (hZ : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Z x J) S) :
    ContinuousOn (fun x => primBilLen L W lK (Y x) (Z x) I) S := by
  simp only [primBilLen]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun k hk => ?_)
  refine continuousOn_finsetSum _ fun l hl => ?_
  refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  split_ifs with hc
  · exact ((hY _ (hI.cutGlueL a hk.1 hl.1 hl.2)).mul continuousOn_const).mul
      (hZ _ (hI.cutGlueR b hk.1 hl.1 hl.2))
  · exact continuousOn_const

/-- `RBM.Decay.primBilLenR` is continuous when both tensors are. -/
theorem continuousOn_primBilLenR (W lK : ℕ) {S : Set X} {Y Z : X → LoopIdx (ZMod L) → ℂ}
    (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Y x J) S)
    (hZ : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Z x J) S) :
    ContinuousOn (fun x => Decay.primBilLenR L W lK (Y x) (Z x) I) S := by
  simp only [Decay.primBilLenR]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun k hk => ?_)
  refine continuousOn_finsetSum _ fun l hl => ?_
  refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  split_ifs with hc
  · exact ((hY _ (hI.cutGlueL a hk.1 hl.1 hl.2)).mul continuousOn_const).mul
      (hZ _ (hI.cutGlueR b hk.1 hl.1 hl.2))
  · exact continuousOn_const

/-- `RBM.Decay.couplingLen` is continuous when both tensors are. -/
theorem continuousOn_couplingLen (W lK : ℕ) {S : Set X} {Y Z : X → LoopIdx (ZMod L) → ℂ}
    (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Y x J) S)
    (hZ : ∀ J : LoopIdx (ZMod L), J.WF → ContinuousOn (fun x => Z x J) S) :
    ContinuousOn (fun x => Decay.couplingLen L W lK (Y x) (Z x) I) S :=
  (continuousOn_primBilLen W lK I hI hY hZ).add (continuousOn_primBilLenR W lK I hI hZ hY)

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

/-- **The pinned drift is continuous along a continuous Hermitian path.**  (5.15)'s `F` is
`eGterm + ∑ couplingLen + primBil`, and all three blocks are finite algebraic expressions in
the loops and the primitive. -/
theorem continuousOn_driftF_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    (hm : ∀ x ∈ S, ∀ s s' : Bool, ‖((τ x : ℝ) : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (b : LoopArg (d.L N) (n + 2)) :
    ContinuousOn (fun x => DriftDef.driftF (band d) E N (τ x) (Mt x) σ b) S := by
  have hwf : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hK : ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      ContinuousOn (fun x => (band d).Kval E N (τ x) J) S :=
    fun J hJ => continuousOn_Kval_path (band d) E N hτ hm J hJ
  have hD : ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      ContinuousOn (fun x =>
        (gloop ((band d).L N) ((band d).W N) (Mt x) (zt E (τ x))
          - (band d).Kval E N (τ x)) J) S := by
    intro J hJ
    simp only [Pi.sub_apply]
    exact (continuousOn_gloop_path d N E hτ hMt hherm hzim J).sub (hK J hJ)
  simp only [DriftDef.driftF]
  refine ((continuousOn_eGterm_path d N E hτ hMt hherm hzim _).add
    (continuousOn_finsetSum _ fun lK _ => ?_)).add ?_
  · exact continuousOn_couplingLen (L := (band d).L N) ((band d).W N) lK _ hwf hK hD
  · exact continuousOn_primBil (L := (band d).L N) ((band d).W N) _ hwf hD hD

/-- **The drift integrand of (5.20) is continuous along a continuous Hermitian path**, in the
time variable of the propagator as well as in the matrix. -/
theorem continuousOn_uker_driftF_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    (hm : ∀ x ∈ S, ∀ s s' : Bool, ‖((τ x : ℝ) : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    ContinuousOn (fun x => Uker (d.L N) (xiOf (mSigma E) σ) ((τ x : ℝ) : ℂ) t
      (DriftDef.driftF (band d) E N (τ x) (Mt x) σ) a) S := by
  simp only [Uker]
  refine continuousOn_finsetSum _ fun b _ => ?_
  refine ContinuousOn.mul ?_ (continuousOn_driftF_path d N E hτ hMt hherm hzim hm σ b)
  exact (continuous_finsetProd _ fun i _ =>
    continuous_edgeKer_time (xiOf (mSigma E) σ i) t (a i) (b i)).comp_continuousOn hτ


/-! #### `L - K` along the path -/

/-- `L - K` is continuous along a continuous Hermitian path. -/
theorem continuousOn_lkFun_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    (hm : ∀ x ∈ S, ∀ s s' : Bool, ‖((τ x : ℝ) : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    {m : ℕ} (σ : Fin m → Bool) (b : LoopArg (d.L N) m) :
    ContinuousOn (fun x => MomentDuhamel.lkFun (band d) E N (τ x) (Mt x) σ b) S := by
  simp only [MomentDuhamel.lkFun]
  exact (continuousOn_gloop_path d N E hτ hMt hherm hzim _).sub
    (continuousOn_Kval_path (band d) E N hτ hm _ (LoopData.idx_wf _))

/-- **`Ψ₁ = (U_{u,t} ∘ (L-K)_u)_a` is continuous along a continuous Hermitian path.** -/
theorem continuousOn_uker_lkFun_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    (hm : ∀ x ∈ S, ∀ s s' : Bool, ‖((τ x : ℝ) : ℂ) * (mSigma E s * mSigma E s')‖ < 1)
    {m : ℕ} (σ : Fin m → Bool) (ξ : Fin m → ℂ) (a : LoopArg (d.L N) m) (t : ℂ) :
    ContinuousOn (fun x => Uker (d.L N) ξ ((τ x : ℝ) : ℂ) t
      (MomentDuhamel.lkFun (band d) E N (τ x) (Mt x) σ) a) S := by
  simp only [Uker]
  refine continuousOn_finsetSum _ fun b _ => ?_
  refine ContinuousOn.mul ?_ (continuousOn_lkFun_path d N E hτ hMt hherm hzim hm σ b)
  exact (continuous_finsetProd _ fun i _ =>
    continuous_edgeKer_time (ξ i) t (a i) (b i)).comp_continuousOn hτ

/-! #### `E ⊗ E` along the path -/

/-- **(5.22) along the path**: `E ⊗ E` is `∑_k W ∑_{b,b'} S^{(B)}_{bb'} L_{glue}`. -/
theorem eeArg_herm_eq (d : Dims) (N : ℕ) (z : ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {n : ℕ} (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) :
    EEBridge.eeArg d N z M σ c
      = ∑ k ∈ Finset.range n, ((d.W N : ℂ) * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
          SB (d.L N) b b' * gloop (d.L N) (d.W N) M z
            (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c))
              k b b')) := by
  rw [EEBridge.eeArg, eeTens, toIdx_length]
  exact Finset.sum_congr rfl fun k _ => EEBridge.eeEdge_eq_sum_gloop hM _ _ k

/-- **`E ⊗ E` is continuous along a continuous Hermitian path.** -/
theorem continuousOn_eeFun_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    {n : ℕ} (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) :
    ContinuousOn (fun x => MomentDuhamel.eeFun (band d) E N (τ x) (Mt x) σ c) S := by
  have hEq : (fun x => MomentDuhamel.eeFun (band d) E N (τ x) (Mt x) σ c)
      = fun x => ∑ k ∈ Finset.range n, ((d.W N : ℂ)
          * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
            SB (d.L N) b b' * gloop (d.L N) (d.W N) (Mt x) (zt E (τ x))
              (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
                (toIdx σ (EEBridge.rightArg c)) k b b')) := by
    funext x
    exact eeArg_herm_eq d N (zt E (τ x)) (hherm x) σ c
  rw [hEq]
  refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
  refine continuousOn_finsetSum _ fun b _ => continuousOn_finsetSum _ fun b' _ => ?_
  exact continuousOn_const.mul (continuousOn_gloop_path d N E hτ hMt hherm hzim _)

/-- **The quadratic-variation integrand of (5.20) is continuous along the path.** -/
theorem continuousOn_uker_eeFun_path (d : Dims) (N : ℕ) (E : ℝ) {S : Set X} {τ : X → ℝ}
    {Mt : X → Matrix (d.Idx N) (d.Idx N) ℂ} (hτ : ContinuousOn τ S) (hMt : ContinuousOn Mt S)
    (hherm : ∀ x, (Mt x).IsHermitian) (hzim : ∀ x ∈ S, (zt E (τ x)).im ≠ 0)
    {n : ℕ} (σ : Fin n → Bool) (ξ : Fin (n + n) → ℂ) (c : LoopArg (d.L N) (n + n)) (t : ℂ) :
    ContinuousOn (fun x => Uker (d.L N) ξ ((τ x : ℝ) : ℂ) t
      (MomentDuhamel.eeFun (band d) E N (τ x) (Mt x) σ) c) S := by
  simp only [Uker]
  refine continuousOn_finsetSum _ fun b _ => ?_
  refine ContinuousOn.mul ?_ (continuousOn_eeFun_path d N E hτ hMt hherm hzim σ b)
  exact (continuous_finsetProd _ fun i _ =>
    continuous_edgeKer_time (ξ i) t (c i) (b i)).comp_continuousOn hτ

/-- **The deterministic envelope of `E ⊗ E`**, from (5.2) on the glued `(2n+2)`-loop and the
row `ℓ¹` normalisation `∑_{b'} ‖S^{(B)}_{bb'}‖ = 1`. -/
theorem norm_eeFun_herm_le (d : Dims) (N : ℕ) (E : ℝ) {η : ℝ} (hη : 0 < η) {u : ℝ}
    (hz : η ≤ |(zt E u).im|) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {n : ℕ} (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) :
    ‖MomentDuhamel.eeFun (band d) E N u M σ c‖
      ≤ (n : ℝ) * ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ)
          * (η⁻¹ ^ (2 * n + 2) * ((d.W N : ℝ))⁻¹ ^ (2 * n + 1)))) := by
  classical
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  set Glue : ℝ := η⁻¹ ^ (2 * n + 2) * ((d.W N : ℝ))⁻¹ ^ (2 * n + 1) with hGlue
  have hkey : ∀ k ∈ Finset.range n,
      ‖(d.W N : ℂ) * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
          SB (d.L N) b b' * gloop (d.L N) (d.W N) M (zt E u)
            (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
              (toIdx σ (EEBridge.rightArg c)) k b b')‖
        ≤ (d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) * Glue) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hgl : ∀ b b' : ZMod (d.L N),
        ‖gloop (d.L N) (d.W N) M (zt E u)
            (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
              (toIdx σ (EEBridge.rightArg c)) k b b')‖ ≤ Glue := by
      intro b b'
      have hlen : (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
          (toIdx σ (EEBridge.rightArg c)) k b b').a.length = 2 * n + 2 :=
        EEBridge.glueIdx_length (toIdx_wf _ _) (toIdx_wf _ _) (toIdx_length _ _)
          (toIdx_length _ _) hk b b'
      have h0 := norm_gloop_le_of_le_abs_im hM hη hz
        (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
          (toIdx σ (EEBridge.rightArg c)) k b b') (EEBridge.glueIdx_wf _ _ _ _ _)
        (by rw [hlen]; omega)
      rwa [hlen] at h0
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    have hrow : ∀ b : ZMod (d.L N),
        ‖∑ b' : ZMod (d.L N), SB (d.L N) b b'
            * gloop (d.L N) (d.W N) M (zt E u)
              (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
                (toIdx σ (EEBridge.rightArg c)) k b b')‖ ≤ Glue := by
      intro b
      refine (norm_sum_le _ _).trans ?_
      have hb : ∀ b' : ZMod (d.L N),
          ‖SB (d.L N) b b' * gloop (d.L N) (d.W N) M (zt E u)
              (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c))
                (toIdx σ (EEBridge.rightArg c)) k b b')‖
            ≤ ‖SB (d.L N) b b'‖ * Glue := by
        intro b'
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hgl b b') (norm_nonneg _)
      refine (Finset.sum_le_sum fun b' _ => hb b').trans ?_
      rw [← Finset.sum_mul, sum_norm_SB_apply_row (d.L N) hL3 b, one_mul]
    refine (Finset.sum_le_sum fun b _ => hrow b).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : ‖MomentDuhamel.eeFun (band d) E N u M σ c‖
      ≤ ∑ _k ∈ Finset.range n, ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ) * Glue)) := by
    rw [show MomentDuhamel.eeFun (band d) E N u M σ c
        = EEBridge.eeArg d N (zt E u) M σ c from rfl, eeArg_herm_eq d N (zt E u) hM σ c]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hkey)
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end PathContinuity




/-! ### The five side conditions of `RBM.MomentDuhamel.momentIneq_of_derivBound` (T212)

For the Gaussian sample, on the paper's window `[s, v] ⊆ [0, 1)`.  Each of the five is the
generic envelope lemma of the previous section applied to one of the three tensors, and all
three envelopes are the deterministic `‖G‖ ≤ (Im z_u)⁻¹` of T77. -/

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

theorem window_norm_xi_lt {E : ℝ} (hE : |E| ≤ 2) {s v : ℝ} (hs0 : 0 ≤ s) (hv1 : v < 1)
    {m : ℕ} [NeZero m] (σ : Fin m → Bool) :
    ∀ u ∈ Set.Icc s v, ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
  intro u hu i
  rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hs0.trans hu.1), norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
  exact lt_of_le_of_lt hu.2 hv1

/-! #### The three integrands along the Gaussian flow -/

variable (d : Dims)

/-- `Ψ₁` along the Gaussian flow, in the shape the interface uses. -/
theorem uker_lkT_eq_path (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (ξ : Fin m → ℂ) (a : LoopArg (d.L N) m) (t : ℂ) (u : ℝ) (ω : Ω d) :
    Uker (d.L N) ξ ((u : ℝ) : ℂ) t (SumZeroDyn.lkT (sample d) E N u ω σ) a
      = Uker (d.L N) ξ ((u : ℝ) : ℂ) t
          (MomentDuhamel.lkFun (band d) E N u (Hflow d N u ω) σ) a := rfl

/-- `Ψ₁` is continuous in the sample point, hence measurable. -/
theorem continuous_uker_lkT_omega (E : ℝ) (N : ℕ) {u : ℝ} (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {m : ℕ} (σ : Fin m → Bool) (ξ : Fin m → ℂ) (a : LoopArg (d.L N) m) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) ξ ((u : ℝ) : ℂ) t
      (SumZeroDyn.lkT (sample d) E N u ω σ) a := by
  rw [← continuousOn_univ]
  refine ContinuousOn.congr ?_ fun ω _ => uker_lkT_eq_path d E N σ ξ a t u ω
  exact continuousOn_uker_lkFun_path (X := Ω d) d N E (τ := fun _ => u)
    (Mt := fun ω => Hflow d N u ω) continuousOn_const
    (continuous_Hflow d N u).continuousOn (fun ω => Hflow_isHermitian d N u ω)
    (fun _ _ => hz) (fun _ _ => hm) σ ξ a t

/-- The drift integrand is continuous in the sample point, hence measurable. -/
theorem continuous_uker_driftF_omega (E : ℝ) (N : ℕ) {u : ℝ} (hz : (zt E u).im ≠ 0)
    (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) a := by
  rw [← continuousOn_univ]
  exact continuousOn_uker_driftF_path (X := Ω d) d N E (τ := fun _ => u)
    (Mt := fun ω => Hflow d N u ω) continuousOn_const
    (continuous_Hflow d N u).continuousOn (fun ω => Hflow_isHermitian d N u ω)
    (fun _ _ => hz) (fun _ _ => hm) σ a t

/-- The quadratic-variation integrand is continuous in the sample point, hence measurable. -/
theorem continuous_uker_eeFun_omega (E : ℝ) (N : ℕ) {u : ℝ} (hz : (zt E u).im ≠ 0)
    {m : ℕ} (σ : Fin m → Bool) (ξ : Fin (m + m) → ℂ) (c : LoopArg (d.L N) (m + m)) (t : ℂ) :
    Continuous fun ω : Ω d => Uker (d.L N) ξ ((u : ℝ) : ℂ) t
      (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ) c := by
  rw [← continuousOn_univ]
  exact continuousOn_uker_eeFun_path (X := Ω d) d N E (τ := fun _ => u)
    (Mt := fun ω => Hflow d N u ω) continuousOn_const
    (continuous_Hflow d N u).continuousOn (fun ω => Hflow_isHermitian d N u ω)
    (fun _ _ => hz) σ ξ c t

/-! #### The bridge and the three envelopes on the window -/

/-- `Ψ₁` along the Gaussian flow is T196's `RBM.Gauss.ukerObsT`, with `K` pinned. -/
theorem uker_lkT_eq_ukerObsT (E : ℝ) (N : ℕ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (t : ℂ) (u : ℝ) (ω : Ω d) :
    Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t (SumZeroDyn.lkT (sample d) E N u ω σ) a
      = ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) t
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a u (Hflow d N u ω) :=
  (ukerObsT_flow (band d) (sample d) E N σ a t (fun _ _ => rfl) u ω).symm

variable {d}

/-- **The envelope of `Ψ₁` on the window**, uniform in the sample point. -/
theorem exists_bdd_uker_lkT (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ)
    {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (SumZeroDyn.lkT (sample d) E N u ω σ) a‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bdd₀_ukerObsT (d := d) (N := N) E
    (σ := List.ofFn σ) (List.length_ofFn) (by omega) (xiOf (mSigma E) σ) t
    (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a
    (window_eta_pos hE hv1) hcK (window_le_abs_im hE hv1) hKb
  exact ⟨C, hC0, fun u hu ω => by
    rw [uker_lkT_eq_ukerObsT d E N σ a t u ω]; exact hC u hu _⟩

/-! #### Item 1: the window bound on `ψ` -/

/-- **`ψ_u = (E|Ψ₁|^{2p})^{1/p}` is bounded on the window** — the first of the five side
conditions of `RBM.MomentDuhamel.momentIneq_of_derivBound`. -/
theorem exists_bdd_psi_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ)
    (p : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc s v,
      (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
          (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P) ^ ((1 : ℝ) / p)
        ≤ C := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_lkT E N hE hv1 σ a t hcK hKb
  refine ⟨(C ^ (2 * p)) ^ ((1 : ℝ) / p), fun u hu => ?_⟩
  have hz : (zt E u).im ≠ 0 := window_im_ne_zero hE hv1 u hu
  have hmu : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1 :=
    window_norm_mul_lt hE.le hs0 hv1 u hu
  have hcont := continuous_uker_lkT_omega d E N hz hmu σ (xiOf (mSigma E) σ) a t
  have hint : Integrable (fun ω : Ω d => |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p)) (band d).P := by
    refine integrable_of_continuous_of_bound (hcont.norm.abs.pow (2 * p))
      (C := C ^ (2 * p)) fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_norm]; exact hC u hu ω) _
  have hle : (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P) ≤ C ^ (2 * p) := by
    have h := integral_mono hint (integrable_const (C ^ (2 * p))) (fun ω => by
      rw [abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC u hu ω) _)
    simpa using h
  exact Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) hle
    (by positivity)

/-! #### Item 2: `ContinuousOn` of `u ↦ E|Ψ₁|^{2p}` -/

/-- **The `2p`-th moment of `Ψ₁` is continuous on the window** — the second side condition. -/
theorem continuousOn_integral_psi_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ)
    (p : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ContinuousOn (fun u : ℝ => ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
      (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P) (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_lkT E N hE hv1 σ a t hcK hKb
  refine continuousOn_integral_abs_pow_of_envelope (C := C) (2 * p) ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_lkT_omega d E N (window_im_ne_zero hE hv1 u hu)
      (window_norm_mul_lt hE.le hs0 hv1 u hu) σ (xiOf (mSigma E) σ) a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · intro ω
    refine ContinuousOn.norm ?_
    refine ContinuousOn.congr ?_ fun u hu => uker_lkT_eq_path d E N σ (xiOf (mSigma E) σ) a t u ω
    exact continuousOn_uker_lkFun_path (X := ℝ) d N E (τ := id)
      (Mt := fun u => Hflow d N u ω) continuousOn_id
      (continuous_Hflow_time d N ω).continuousOn (fun u => Hflow_isHermitian d N u ω)
      (fun u hu => window_im_ne_zero hE hv1 u hu)
      (fun u hu => window_norm_mul_lt hE.le hs0 hv1 u hu) σ (xiOf (mSigma E) σ) a t

/-! #### The envelope of the quadratic-variation integrand -/

/-- **The envelope of `(U⊗U) ∘ (E⊗E)` on the window**, uniform in the sample point: the
`(2n+2)`-loop bound of (5.2) carried through the propagator's row `ℓ¹` size. -/
theorem exists_bdd_uker_eeFun (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hv1 : v < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d,
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) t
        (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ) (Fin.append a a)‖ ≤ C := by
  classical
  set η : ℝ := (1 - v) * (mE E).im with hη
  have hη0 : 0 < η := window_eta_pos hE hv1
  set Mee : ℝ := ((n + 2 : ℕ) : ℝ) * ((d.W N : ℝ) * ((Fintype.card (ZMod (d.L N)) : ℝ)
    * (η⁻¹ ^ (2 * (n + 2) + 2) * ((d.W N : ℝ))⁻¹ ^ (2 * (n + 2) + 1)))) with hMee
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := fun u : ℝ => ukerRow (SumZeroDyn.xi2 E σ) t (Fin.append a a) u * Mee)
    (((continuous_ukerRow (SumZeroDyn.xi2 E σ) t (Fin.append a a)).mul
      continuous_const)).continuousOn
  refine ⟨|C|, abs_nonneg _, fun u hu ω => ?_⟩
  have hb := norm_Uker_apply_le_ukerRow (SumZeroDyn.xi2 E σ) t u
    (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ) (Fin.append a a)
    (C := Mee) (fun b => norm_eeFun_herm_le d N E hη0 (window_le_abs_im hE hv1 u hu)
      (Hflow_isHermitian d N u ω) σ b)
  exact hb.trans (le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _))

/-! #### Items 3–5: the interval integrabilities -/

/-- `u ↦ ‖Ψ₁‖_{2p}` is continuous on the window. -/
theorem continuousOn_momNorm_lkT_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) (t : ℂ)
    (q : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK) :
    ContinuousOn (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) t
        (SumZeroDyn.lkT (sample d) E N u ω σ) a‖)) (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_lkT E N hE hv1 σ a t hcK hKb
  refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_lkT_omega d E N (window_im_ne_zero hE hv1 u hu)
      (window_norm_mul_lt hE.le hs0 hv1 u hu) σ (xiOf (mSigma E) σ) a t).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · intro ω
    refine ContinuousOn.norm ?_
    refine ContinuousOn.congr ?_ fun u hu => uker_lkT_eq_path d E N σ (xiOf (mSigma E) σ) a t u ω
    exact continuousOn_uker_lkFun_path (X := ℝ) d N E (τ := id)
      (Mt := fun u => Hflow d N u ω) continuousOn_id
      (continuous_Hflow_time d N ω).continuousOn (fun u => Hflow_isHermitian d N u ω)
      (fun u hu => window_im_ne_zero hE hv1 u hu)
      (fun u hu => window_norm_mul_lt hE.le hs0 hv1 u hu) σ (xiOf (mSigma E) σ) a t

/-- `u ↦ ‖(U ∘ F_u)_a‖_{2p}` is continuous on the window. -/
theorem continuousOn_momNorm_driftF_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (q : ℕ) {cK : ℝ}
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg ((band d).toDims.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg ((band d).toDims.L N) (n + 2),
      ‖Kprim (band d) E N σ u b‖ ≤ cK) :
    ContinuousOn (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) a‖)) (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_driftF (band d) E N σ a ((v : ℝ) : ℂ)
    (window_eta_pos hE hv1) (window_le_abs_im hE hv1) hKb hK'b
    (window_norm_mul_lt hE.le hs0 hv1) (window_norm_xi_lt hE.le hs0 hv1 σ)
    (fun i => by
      rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hs0.trans hsv),
        norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
      exact hv1)
  refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_driftF_omega d E N (window_im_ne_zero hE hv1 u hu)
      (window_norm_mul_lt hE.le hs0 hv1 u hu) σ a ((v : ℝ) : ℂ)).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu _ (Hflow_isHermitian d N u ω)
  · intro ω
    refine ContinuousOn.norm ?_
    exact continuousOn_uker_driftF_path (X := ℝ) d N E (τ := id)
      (Mt := fun u => Hflow d N u ω) continuousOn_id
      (continuous_Hflow_time d N ω).continuousOn (fun u => Hflow_isHermitian d N u ω)
      (fun u hu => window_im_ne_zero hE hv1 u hu)
      (fun u hu => window_norm_mul_lt hE.le hs0 hv1 u hu) σ a ((v : ℝ) : ℂ)

/-- `u ↦ ‖(U⊗U) ∘ (E⊗E)_{a,a}‖_p` is continuous on the window. -/
theorem continuousOn_momNorm_eeFun_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (q : ℕ) :
    ContinuousOn (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)
          (Fin.append a a)‖)) (Set.Icc s v) := by
  classical
  have hprob := (band d).isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bdd_uker_eeFun E N hE hv1 σ a ((v : ℝ) : ℂ)
  refine continuousOn_momNorm_of_envelope (C := C) q ?_ ?_ ?_
  · intro u hu
    exact (continuous_uker_eeFun_omega d E N (window_im_ne_zero hE hv1 u hu) σ
      (SumZeroDyn.xi2 E σ) (Fin.append a a) ((v : ℝ) : ℂ)).norm.aestronglyMeasurable
  · intro u hu ω
    rw [abs_norm]
    exact hC u hu ω
  · intro ω
    refine ContinuousOn.norm ?_
    exact continuousOn_uker_eeFun_path (X := ℝ) d N E (τ := id)
      (Mt := fun u => Hflow d N u ω) continuousOn_id
      (continuous_Hflow_time d N ω).continuousOn (fun u => Hflow_isHermitian d N u ω)
      (fun u hu => window_im_ne_zero hE hv1 u hu) σ (SumZeroDyn.xi2 E σ)
      (Fin.append a a) ((v : ℝ) : ℂ)

/-- **Item 3: `φ'` is interval integrable.**

The derivative slot of `RBM.MomentDuhamel.momentIneq_of_derivBound` is existential, so the
integrability has to hold for *whatever* witness the caller supplies.  It does, because a
derivative is unique: on the open window `φ'` is forced to be the generator expression of
`RBM.Gauss.hasDerivAt_integral_Psi₁`, which T196's `bddT` and `bdd₂` bound uniformly.
Measurability is `Mathlib.measurable_deriv`.  Only the **open** interval is used, which is
also the only place `0 < u` — needed by the Gaussian generator identity — is available. -/
theorem intervalIntegrable_phi'_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ} (hs0 : 0 ≤ s)
    (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (p : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖Kprim (band d) E N σ u b‖ ≤ cK)
    {φ' : ℝ → ℝ}
    (hφ' : ∀ u ∈ Set.Ioo s v, HasDerivAt (fun r : ℝ =>
        ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N r ω σ) a‖| ^ (2 * p) ∂(band d).P) (φ' u) u) :
    IntervalIntegrable φ' volume s v := by
  classical
  set φ : ℝ → ℝ := fun r : ℝ =>
    ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (SumZeroDyn.lkT (sample d) E N r ω σ) a‖| ^ (2 * p) ∂(band d).P with hφ
  set Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    momentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p with hΨ
  have hT₁ : TestFunT₁ d N (Set.Icc s v) Ψ :=
    testFunT₁_momentObsT E (List.length_ofFn) (by omega) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) (Kprim (band d) E N σ) a p
      (window_eta_pos hE hv1) hcK (window_le_abs_im hE hv1)
      (fun u hu b => hasDerivAt_Kval_Kprim (band d) E N
        (window_norm_mul_lt hE.le hs0 hv1 u hu) σ b) hKb hK'b
  obtain ⟨CT, hCT⟩ := hT₁.bddT
  obtain ⟨C₂, hC₂⟩ := hT₁.bdd₂
  set Cb : ℝ := CT + (1 / 2 : ℝ) * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
      * (C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖) with hCb
  have hΦφ : (fun r : ℝ => ∫ ω, Ψ r (Hflow d N r ω) ∂(P d)) = fun r : ℝ => ((φ r : ℝ) : ℂ) := by
    funext r
    have hpt : ∀ ω : Ω d, Ψ r (Hflow d N r ω)
        = ((|‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.lkT (sample d) E N r ω σ) a‖| ^ (2 * p) : ℝ) : ℂ) := fun ω =>
      momentObsT_flow (band d) (sample d) E N σ a ((v : ℝ) : ℂ) (fun _ _ => rfl) p r ω
    rw [show (fun ω : Ω d => Ψ r (Hflow d N r ω))
        = fun ω : Ω d => ((|‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.lkT (sample d) E N r ω σ) a‖| ^ (2 * p) : ℝ) : ℂ) from funext hpt]
    exact integral_complex_ofReal
  have hkey : ∀ u ∈ Set.Ioo s v, |φ' u| ≤ Cb := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hs0 hu.1
    have hmem : Set.Icc s v ∈ nhds u := Icc_mem_nhds hu.1 hu.2
    have hmemI : u ∈ Set.Icc s v := ⟨hu.1.le, hu.2.le⟩
    have hD := hasDerivAt_integral_Psi₁ (matrixStein d) hT₁ hu0 hmem
    rw [hΦφ] at hD
    have hre : HasDerivAt (fun r : ℝ => (((φ r : ℝ) : ℂ)).re)
        (Complex.reCLM ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
          + (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
            ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d))) u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hD
    simp only [Complex.ofReal_re, Complex.reCLM_apply] at hre
    have heq : φ' u = ((∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d))
        + (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
          ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d)).re :=
      (hφ' u hu).unique hre
    have hb1 : ‖∫ ω, timeD1 Ψ u (Hflow d N u ω) ∂(P d)‖ ≤ CT := by
      have h := norm_integral_le_of_norm_le_const (μ := P d) (C := CT)
        (Filter.Eventually.of_forall fun ω => hCT u hmemI (Hflow d N u ω))
      simpa using h
    have hb2 : ‖(1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
        ∫ ω, coordD2 d N (Ψ u) (Hflow d N u ω) q ∂(P d)‖
        ≤ (1 / 2 : ℝ) * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ)
          * (C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
      have h := norm_integral_le_of_norm_le_const (μ := P d)
        (C := C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖)
        (Filter.Eventually.of_forall fun ω =>
          norm_coordD2_le (fun M => hC₂ u hmemI M) (Hflow d N u ω) q)
      simpa using h
    rw [heq]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
  -- measurability from uniqueness of the derivative, integrability from the bound
  have hderiv : ∀ u ∈ Set.Ioo s v, deriv φ u = φ' u := fun u hu => (hφ' u hu).deriv
  have hae : deriv φ =ᵐ[volume.restrict (Set.Ioo s v)] φ' := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu using hderiv u hu
  have hmeas : AEStronglyMeasurable φ' (volume.restrict (Set.Ioo s v)) :=
    ((measurable_deriv φ).aestronglyMeasurable).congr hae
  have hintOo : IntegrableOn φ' (Set.Ioo s v) := by
    refine Integrable.mono' (integrable_const Cb) hmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs]
    exact hkey u hu
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hsv]
  exact hintOo.congr_set_ae Ioo_ae_eq_Ioc.symm

/-! #### Items 4 and 5 -/

/-- **Item 4, first half**: `u ↦ ‖(U ∘ F_u)_a‖_{2p}` is interval integrable on the window. -/
theorem intervalIntegrable_momNorm_driftF_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (q : ℕ) {cK : ℝ}
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg ((band d).toDims.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg ((band d).toDims.L N) (n + 2),
      ‖Kprim (band d) E N σ u b‖ ≤ cK) :
    IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) a‖)) volume s v :=
  (continuousOn_momNorm_driftF_gauss E N hE hs0 hsv hv1 σ a q hKb
    hK'b).intervalIntegrable_of_Icc hsv

/-- **Item 4, second half**: `u ↦ ‖(U⊗U) ∘ (E⊗E)_{a,a}‖_p` is interval integrable. -/
theorem intervalIntegrable_momNorm_eeFun_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (q : ℕ) :
    IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P q (fun ω =>
      ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)
          (Fin.append a a)‖)) volume s v :=
  (continuousOn_momNorm_eeFun_gauss E N hE hv1 σ a q).intervalIntegrable_of_Icc hsv

/-- **Item 5**: the product `ψ · f` is interval integrable on every initial segment. -/
theorem intervalIntegrable_psi_mul_driftF_gauss (E : ℝ) (N : ℕ) (hE : |E| < 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (q : ℕ) {cK : ℝ} (hcK : 0 ≤ cK)
    (hKb : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ cK)
    (hK'b : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖Kprim (band d) E N σ u b‖ ≤ cK) :
    ∀ u ∈ Set.Icc s v, IntervalIntegrable (fun r : ℝ =>
      MomentDuhamel.momNorm (band d).P q (fun ω =>
        ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N r ω σ) a‖)
      * MomentDuhamel.momNorm (band d).P q (fun ω =>
        ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (DriftDef.driftF (band d) E N r ((sample d).H N r ω) σ) a‖)) volume s u := by
  intro u hu
  have hmono : Set.Icc s u ⊆ Set.Icc s v := Set.Icc_subset_Icc le_rfl hu.2
  refine ContinuousOn.intervalIntegrable_of_Icc hu.1 ?_
  exact (((continuousOn_momNorm_lkT_gauss E N hE hs0 hv1 σ a ((v : ℝ) : ℂ) q hcK hKb).mul
    (continuousOn_momNorm_driftF_gauss E N hE hs0 hsv hv1 σ a q hKb hK'b)).mono hmono)

/-! #### The primitive's own window bound, from compactness

`K_u` and `∂_u K_u` are continuous in `u` and the loop arguments range over a *finite* type, so
on the compact window `[s, v] ⊆ [0, 1)` they are bounded — no hypothesis needed.  (The bound
does blow up as `v ↑ 1`; that is why it is taken on `[s, v]` and not on `[0, 1)`, which would
be unsatisfiable.) -/

/-- `∂_u K_u` is continuous in the time — `RBM.Gauss.Kprim` is `RBM.primRhs`, i.e. `primBil`
of the primitive with itself. -/
theorem continuousOn_Kprim (E : ℝ) (N : ℕ) {S : Set ℝ}
    (hm : ∀ u ∈ S, ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (b : LoopArg ((band d).toDims.L N) (n + 2)) :
    ContinuousOn (fun u : ℝ => Kprim (band d) E N σ u b) S := by
  have hK : ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      ContinuousOn (fun u : ℝ => (band d).Kval E N u J) S :=
    fun J hJ => continuousOn_Kval_path (band d) E N continuousOn_id hm J hJ
  simpa only [Kprim, ← primBil_self] using
    continuousOn_primBil (X := ℝ) (L := (band d).L N) ((band d).W N)
      (LoopData.idx (σ, b)) (LoopData.idx_wf _) hK hK

/-- **The window bound on `K` and `∂_u K` is a theorem, not a hypothesis.** -/
theorem exists_bdd_Kval_Kprim (E : ℝ) (N : ℕ) (hE : |E| ≤ 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool) :
    ∃ c : ℝ, 0 ≤ c
      ∧ (∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
          ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ ≤ c)
      ∧ (∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
          ‖Kprim (band d) E N σ u b‖ ≤ c) := by
  classical
  have hm := window_norm_mul_lt (E := E) hE (s := s) (v := v) hs0 hv1
  set g : ℝ → ℝ := fun u => ∑ b : LoopArg (d.L N) (n + 2),
    (‖(band d).Kval E N u (LoopData.idx (σ, b))‖ + ‖Kprim (band d) E N σ u b‖) with hg
  have hgc : ContinuousOn g (Set.Icc s v) := by
    refine continuousOn_finsetSum _ fun b _ => ContinuousOn.add ?_ ?_
    · exact (continuousOn_Kval_path (band d) E N continuousOn_id hm _
        (LoopData.idx_wf _)).norm
    · exact (continuousOn_Kprim E N hm σ b).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn hgc
  have hnn : ∀ u, 0 ≤ g u := fun u => Finset.sum_nonneg fun _ _ => by positivity
  have hle : ∀ u ∈ Set.Icc s v, ∀ b : LoopArg (d.L N) (n + 2),
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ + ‖Kprim (band d) E N σ u b‖ ≤ |C| := by
    intro u hu b
    refine le_trans (Finset.single_le_sum (f := fun b : LoopArg (d.L N) (n + 2) =>
      ‖(band d).Kval E N u (LoopData.idx (σ, b))‖ + ‖Kprim (band d) E N σ u b‖)
      (fun _ _ => by positivity) (Finset.mem_univ b)) ?_
    exact le_trans (le_trans (le_abs_self _) (hC u hu)) (le_abs_self _)
  exact ⟨|C|, abs_nonneg _,
    fun u hu b => le_trans (by linarith [norm_nonneg (Kprim (band d) E N σ u b)])
      (hle u hu b),
    fun u hu b => le_trans
      (by linarith [norm_nonneg ((band d).Kval E N u (LoopData.idx (σ, b)))]) (hle u hu b)⟩

/-! #### The assembly: `RBM.MomentDuhamel.MomentIneq` with the five side conditions gone -/

/-- **T212's deliverable: `RBM.MomentDuhamel.momentIneq_of_derivBound` for the Gaussian
sample, with all five integrability side conditions discharged.**

What is left in the hypothesis `h` is exactly the two items that carry mathematics: the
existence of the `u`-derivative of `u ↦ E|Ψ₁|^{2p}` on the **open** window, and the pointwise
inequality (5.20) that the generator identity of
`RBM.Gauss.timeD1_add_genMomentPt_le_driftF_flow` (T206) followed by Hölder produces.  The
five that this file removes —

1. the window bound on `ψ` (`RBM.Gauss.exists_bdd_psi_gauss`),
2. the `ContinuousOn` of `u ↦ E|Ψ₁|^{2p}` (`RBM.Gauss.continuousOn_integral_psi_gauss`),
3. the interval integrability of `φ'` (`RBM.Gauss.intervalIntegrable_phi'_gauss`),
4. the interval integrability of the two drift integrands
   (`RBM.Gauss.intervalIntegrable_momNorm_driftF_gauss`,
   `RBM.Gauss.intervalIntegrable_momNorm_eeFun_gauss`),
5. the interval integrability of the product `ψ · f`
   (`RBM.Gauss.intervalIntegrable_psi_mul_driftF_gauss`)

— all follow from the deterministic envelope `‖G‖ ≤ (Im z_u)⁻¹` of T77, which on the window
`[s_N, v] ⊆ [0, 1)` is uniform.  The primitive's own window bound is a theorem too
(`RBM.Gauss.exists_bdd_Kval_Kprim`), so no `cK` appears here either.

The drift is **pinned**: `RBM.DriftDef.driftF`, T58's definition, not a free tensor. -/
theorem momentIneq_of_derivBound_gauss (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
      ∀ a : LoopArg ((band d).L N) (n + 2), ∃ φ' : ℝ → ℝ,
        (∀ u ∈ Set.Ioo (s N) v, HasDerivAt
              (fun r => ∫ ω, |‖Uker ((band d).L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ)
                ((v : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ) a‖| ^ (2 * p)
                  ∂(band d).P) (φ' u) u)
        ∧ (∀ u ∈ Set.Ioo (s N) v, φ' u
            ≤ 2 * (p : ℝ)
                * (∫ ω, |‖Uker ((band d).L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P)
                  ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ)))
                * MomentDuhamel.momNorm (band d).P (2 * p) (fun ω =>
                    ‖Uker ((band d).L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) a‖)
              + (p : ℝ) * (2 * (p : ℝ) - 1)
                * (∫ ω, |‖Uker ((band d).L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P)
                  ^ (((p : ℝ) - 1) / (p : ℝ))
                * MomentDuhamel.momNorm (band d).P p (fun ω =>
                    ‖Uker ((band d).L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                      (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)
                        (Fin.append a a)‖))) :
    MomentDuhamel.MomentIneq (sample d) E s t n MomentDuhamel.cMDval := by
  refine MomentDuhamel.momentIneq_of_derivBound hE.le hs0 ht1 ?_
  intro p hp N σ v hsv hvt a
  obtain ⟨φ', hd, hb⟩ := h p hp N σ v hsv hvt a
  have hv1 : v < 1 := lt_of_le_of_lt hvt (ht1 N)
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    exists_bdd_Kval_Kprim (d := d) E N hE.le (hs0 N) hv1 (v := v) σ
  obtain ⟨C, hC⟩ := exists_bdd_psi_gauss E N hE (hs0 N) hv1 σ a ((v : ℝ) : ℂ) p hcK hKb
  exact ⟨φ', C, hC,
    continuousOn_integral_psi_gauss E N hE (hs0 N) hv1 σ a ((v : ℝ) : ℂ) p hcK hKb,
    hd,
    intervalIntegrable_phi'_gauss E N hE (hs0 N) hsv hv1 σ a p hcK hKb hK'b hd,
    intervalIntegrable_momNorm_driftF_gauss E N hE (hs0 N) hsv hv1 σ a (2 * p) hKb hK'b,
    intervalIntegrable_momNorm_eeFun_gauss E N hE hsv hv1 σ a p,
    intervalIntegrable_psi_mul_driftF_gauss E N hE (hs0 N) hsv hv1 σ a (2 * p) hcK hKb hK'b,
    hb⟩

/-! #### Satisfiability

Two checks, both compiled.

* `RBM.Gauss.sideConditions_gauss_window_zero` is the **positive** witness: at the critical
  scaling — the full open window `s = 0`, `0 ≤ v < 1`, with `v` allowed to run up to `1` and
  no constant that degenerates as it does (the T195 accident) — all five side conditions hold
  **simultaneously**, for an arbitrary Gaussian model, an arbitrary charge vector and an
  arbitrary `p`, with **no free data**: the primitive's window bound is itself produced by
  `RBM.Gauss.exists_bdd_Kval_Kprim`.
* `RBM.Gauss.uker_driftF_eq_at_zero` is the **degenerate** check the T164 rule demands: at the
  sample point `ω = 0` (`H_u = 0`, `G = -z⁻¹`) the drift identity, and hence the envelope built
  on it, is asserted and has content.  The drift there is the pinned `RBM.DriftDef.driftF`,
  not a free tensor and not zero by fiat. -/

/-- **Degenerate check at `ω = 0`.** -/
theorem uker_driftF_eq_at_zero (E : ℝ) (N : ℕ) {u v : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (d.L N) (n + 2)) :
    Uker ((band d).L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (DriftDef.driftF (band d) E N u 0 σ) a
      = ukerObsTDeriv d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) (Kprim (band d) E N σ) a u 0
        + genD d N (ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
              (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a u) 0 := by
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]; exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  refine uker_driftF_eq (band d) E N u Matrix.isHermitian_zero hz σ a ((v : ℝ) : ℂ) ?_ ?_ ?_
  · exact fun x y => window_norm_mul_lt hE.le hu0 hu1 u ⟨le_rfl, le_rfl⟩ x y
  · exact fun i => window_norm_xi_lt hE.le hu0 hu1 σ u ⟨le_rfl, le_rfl⟩ i
  · exact fun i => window_norm_xi_lt hE.le hv0 hv1 σ v ⟨le_rfl, le_rfl⟩ i

/-- **Positive satisfiability witness: the five side conditions hold together on the full
open window `[0, v]`, `v < 1`, with no free data.** -/
theorem sideConditions_gauss_window_zero (E : ℝ) (N : ℕ) (hE : |E| < 2) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (d.L N) (n + 2)) (p : ℕ) :
    (∃ C : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) v,
        (∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P) ^ ((1 : ℝ) / p) ≤ C)
      ∧ ContinuousOn (fun u : ℝ =>
          ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (SumZeroDyn.lkT (sample d) E N u ω σ) a‖| ^ (2 * p) ∂(band d).P) (Set.Icc 0 v)
      ∧ IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P (2 * p) (fun ω =>
          ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ) a‖)) volume 0 v
      ∧ IntervalIntegrable (fun u : ℝ => MomentDuhamel.momNorm (band d).P p (fun ω =>
          ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ)
              (Fin.append a a)‖)) volume 0 v
      ∧ (∀ u ∈ Set.Icc (0 : ℝ) v, IntervalIntegrable (fun r : ℝ =>
          MomentDuhamel.momNorm (band d).P (2 * p) (fun ω =>
            ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.lkT (sample d) E N r ω σ) a‖)
          * MomentDuhamel.momNorm (band d).P (2 * p) (fun ω =>
            ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (DriftDef.driftF (band d) E N r ((sample d).H N r ω) σ) a‖)) volume 0 u) := by
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    exists_bdd_Kval_Kprim (d := d) E N hE.le (le_refl (0 : ℝ)) hv1 (v := v) σ
  exact ⟨exists_bdd_psi_gauss E N hE le_rfl hv1 σ a ((v : ℝ) : ℂ) p hcK hKb,
    continuousOn_integral_psi_gauss E N hE le_rfl hv1 σ a ((v : ℝ) : ℂ) p hcK hKb,
    intervalIntegrable_momNorm_driftF_gauss E N hE le_rfl hv0 hv1 σ a (2 * p) hKb hK'b,
    intervalIntegrable_momNorm_eeFun_gauss E N hE hv0 hv1 σ a p,
    intervalIntegrable_psi_mul_driftF_gauss E N hE le_rfl hv0 hv1 σ a (2 * p) hcK hKb hK'b⟩

end SideConditions

end Gauss

end RBM

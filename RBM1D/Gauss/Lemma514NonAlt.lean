/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.MomentDuhamelQ
import RBM1D.Gauss.Lemma514QRoute

/-!
# Lemma 5.14, the non-alternating charges: (5.20) + (7.16) Case 1 on the moment route (T236)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5 — (5.20), (5.82)–(5.85), (5.101) — and §7, Lemma 7.3, **Case 1** of (7.16).

## Why this file exists

`RBM1D/Gauss/Lemma514QAssembly.lean` reaches `RBM.Step3.Lemma514` on the `Q_u` route modulo one
branch.  The `Q_u` half of (5.101) holds for **every** charge (the field
`RBM.MomentDuhamel.Hyp.momentDuhamelQ` is quantified over `∀ σ`), and the `P` half holds on
`QGood` charges (T218, `RBM.Gauss.pHalf514_of_wardP`).  Off `QGood` the `P` half is not merely
unproved but **unsatisfiable**: T218's `RBM.Gauss.pow_card_le_of_norm_Psum_le` shows that a
constant `C` with `‖(P ∘ A)_x‖ ≤ C · sup ‖A‖` for every tensor `A` satisfies `L^n ≤ C`, with
equality at the constant tensor, while the normalisation `A_v^{-(n+2)}` that the two halves of
(5.101) share carries no positive power of `L`.

The paper does not use (5.101) there.  By `RBM.SumZeroDyn.eq_zero_of_not_nonAlt_not_qGood`
every charge that is not `QGood` is non-alternating (`RBM.SumZeroDyn.NonAlt`, a repeated sign
`σ_k = σ_{k+1}`) except for `σ = (-,+)` at length `2`, and on non-alternating charges §5.5 runs
(5.20) — the **unprojected** Duhamel formula — through **Case 1** of (7.16), where the short
edge `|1 - v ξ_k| ≥ √κ` supplies the contraction that sum-zero supplies in Case 2.  Neither
`Q_u`, nor Ward's identity, nor the sum-zero property is used.

The repository had that estimate only inside `RBM.SumZeroDyn.lemma514_flow`
(`RBM.SumZeroDyn.bound_nonAlt`, `term1I`/`term1F`/`term1M`), whose inputs are the
`RBM.SumZeroDyn.Hierarchy` + `RBM.SumZeroDyn.Lemma510` package — forbidden on the moment route
since T118, because its `mart` residual is a fiat.  This file redoes it from
`RBM.MomentDuhamel.Hyp.momentDuhamel`, exactly as `RBM1D/Gauss/Lemma514Q716.lean` +
`RBM1D/Gauss/Lemma514QAssembly.lean` do the `Q_u` half from `momentDuhamelQ`.

## Main results

* §1 — **(7.16) Case 1 in moment form**, the twin of
  `RBM.Gauss.momNorm_Uker_sumZero_scale_le`:
  `RBM.Gauss.norm_Uker_short_scale_le'` (arbitrary edge parameter, needed for the `E ⊗ E`
  charge `RBM.SumZeroDyn.xi2`, which is a `Fin.append` and not a `xiOf`),
  `RBM.Gauss.momNorm_Uker_short_scale_le'`, and the two specialisations
  `RBM.Gauss.momNorm_Uker_short_sigma_le` (charge `xiOf (mSigma E) σ`) and
  `RBM.Gauss.momNorm_Uker_short_xi2_le` (charge `xi2 E σ`).  The main term carries **no**
  `(η_s/η_v)` prefactor: the `r^m` of (7.14) has been cancelled against the change of
  normalisation `A_u^{-m} → A_v^{-m}`, precisely as in Case 2, and the difference to Case 2 is
  only `K^m` in place of `K^{2m}` and a `κ`-dependent constant `cKerShort m √κ` in place of
  `cKerSumZero m`.  `RBM.Gauss.momNorm_Uker_short_scale_le_on_event` is the event-restricted
  form, for when (7.13) is only available with high probability.
* §2 — `RBM.Gauss.RhsNonAltAt`, the three right-hand terms of
  `RBM.MomentDuhamel.Hyp.momentDuhamel` **guarded by `NonAlt`**, and
  `RBM.Gauss.stochDom_lkT_nonAlt_of_momentDuhamel`, the guarded consumer: on non-alternating
  charges the unprojected moment Duhamel inequality alone gives `≺`.  The guard is what makes
  the slot satisfiable — on an *alternating* charge Case 1 does not apply and no replacement
  exists, which is why the unguarded `RBM.MomentDuhamel.stochDom_of_momentDuhamel` cannot be
  used here.
* §3 — `RBM.Gauss.rhsNonAltAt_of_kernel_inputs`, the producer of §2's hypothesis out of §1,
  the size envelopes and the (7.13) fast decay; `RBM.Gauss.rhsNonAltAt_of_kernel_inputs_zero_err`
  with the numeric row discharged.
* §4 — `RBM.Gauss.stochDom_lkT_of_qGood_nonAlt'`, §5.5's charge split with the length-`2`
  exception `σ = (-,+)` folded in by rotation (`RBM.SumZeroDyn.lkT_swap2`,
  `RBM.SumZeroDyn.qGood_swap2`).  This is what lets
  `RBM.Gauss.lemma514_of_momentDuhamelQ` drop `RBM.Gauss.NonAlt514`.
* §5 — satisfiability: `RBM.Gauss.nonAlt_const` (the guard is inhabited),
  `RBM.Gauss.norm_Uker_witTensor_self_ne_zero` (the estimated object is not `0`),
  `RBM.Gauss.gridS_short_witness` on the paper's own p. 24 grid (`RBM.gridS`,
  `1 - s_k = W^{-kτ'}`), with a **non-zero** tensor, a **non-alternating** charge, `ζ = δ = 0`
  and an `N`-independent constant; and `RBM.Gauss.hnum_le_of_zero_err_short` /
  `RBM.Gauss.gridS_cNum716Short_le`, which discharge the numeric row uniformly along the grid.

## Deviations from the paper

One, to be recorded in `docs/paper-deltas.md` as **`T236a`**: the `hEnv…`/`hDec…` rows of §3
are quantified over every sample point `ω` (restricted to non-alternating charges and to the
window), whereas the paper's (7.13) and the a priori bounds behind (7.16) hold on a
high-probability event.  This is the *same* deviation as T219a on the `Q` side, inherited from
the shape of T201's `hGM`/`hGd` slots, and the event-restricted replacement route is the same
one (`RBM.Gauss.momNorm_le_affine_on_event`).  Nothing else deviates: (7.16) Case 1 is used
verbatim through `RBM.norm_Uker_fastDecay_le_short`, and the charge classification is
`RBM.SumZeroDyn.NonAlt` verbatim.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel

/-! ### §1  Case 1 of (7.16) in moment form

`RBM.SumZeroDyn.norm_Uker_short_scale_le` is Case 1 in the normalisation the hierarchy uses,
but only for the charge `ξ = (m(σᵢ) m(σᵢ₊₁))ᵢ` of Definition 5.2.  The `E ⊗ E` term of (5.24)
carries `RBM.SumZeroDyn.xi2`, a `Fin.append` of two such families, so — exactly as on the Case-2
side, where `RBM.Gauss.norm_Uker_sumZero_scale_le'` had to be produced for the same reason — the
arbitrary-`ξ` form is needed.  Case 1 of (7.16) (`RBM.norm_Uker_fastDecay_le_short`) needs only
`‖ξᵢ‖ ≤ 1` and one **short** edge `κ ≤ ‖1 - v ξ_{i₀}‖`, so the primed statement covers both. -/

section Short716

/-- **(5.84)/(7.16) Case 1, for an arbitrary edge parameter, in scale form** — the Case-1 twin
of `RBM.Gauss.norm_Uker_sumZero_scale_le'`, and the arbitrary-`ξ` form of
`RBM.SumZeroDyn.norm_Uker_short_scale_le`.

`κg` is the gap of the short edge at the *terminal* time `v` (for the paper's charge it is
`√κ`, `RBM.sqrt_le_norm_one_sub_xiOf`).  The main term carries no `(η_u/η_v)` factor: the `r^m`
of (7.14) has been absorbed by the change of normalisation `A_u^{-m} → A_v^{-m}`. -/
theorem norm_Uker_short_scale_le' (L : ℕ) [NeZero L] (hL : 3 ≤ L) {m : ℕ}
    {ξ : Fin m → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {κg : ℝ} (hκg : 0 < κg)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (i₀ : Fin m) (hκt : κg ≤ ‖1 - (v : ℂ) * ξ i₀‖)
    {κA : ℝ} (hκA : 0 < κA) {K ψ ζ δ : ℝ} (hK : 1 ≤ K) (hψ : 0 ≤ ψ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : LoopArg L m → ℂ}
    (hGM : ∀ b, ‖G b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ + ζ)
    (hG : FastDecay L (ellHat L (u : ℂ) * K) δ G) (a : LoopArg L m) :
    ‖Uker L ξ (u : ℂ) (v : ℂ) G a‖
      ≤ cKerShort m κg * K ^ m * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * ψ
        + (cKerShort m κg * K ^ m * ((1 - s) / (1 - v)) ^ m * ζ
          + ((1 - s) / (1 - v)) ^ m * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓu := SumZeroDyn.ellHat_real_pos' L hL hu0 hu1
  have hℓv := SumZeroDyn.ellHat_real_pos' L hL (hu0.trans huv) hv1
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have hM0 : 0 ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ + ζ := by positivity
  have key := norm_Uker_fastDecay_le_short L hL hu0 huv hv1 hξ hκg i₀ hκt hK hM0 hδ hGM hG a
  refine key.trans ?_
  set r := (1 - u) * ellHat L (u : ℂ) / ((1 - v) * ellHat L (v : ℂ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrρ : r ≤ (1 - s) / (1 - v) := SumZeroDyn.ratio_le L hL hs0 hsu huv hv1
  have hq : (1 - u) / (1 - v) ≤ (1 - s) / (1 - v) := SumZeroDyn.one_sub_div_le hsu hv1
  have hcancel : r ^ m * (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m
      = (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m := by
    rw [← mul_pow]; congr 1; rw [hr]; field_simp
  have hc := SumZeroDyn.cKerShort_nonneg m hκg
  have hK0 : (0 : ℝ) ≤ K ^ m := by positivity
  have e1 : cKerShort m κg * K ^ m * r ^ m
      * ((κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ + ζ)
      = cKerShort m κg * K ^ m * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * ψ
        + cKerShort m κg * K ^ m * r ^ m * ζ := by
    rw [← hcancel]; ring
  rw [e1, add_assoc]
  refine add_le_add le_rfl (add_le_add ?_ ?_)
  · gcongr
  · gcongr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **(7.16) Case 1 in moment form, for an arbitrary edge parameter.**

For a tensor `G(ω)` which is, for every `ω`, `(ℓ_u K, δ)`-fast-decaying with
`|G(ω)_b| ≤ A_u^{-m} ψ(ω) + ζ`, and for a charge with one short edge at the terminal time,

`‖(U_{u,v,ξ} ∘ G(ω))_a‖_q ≤ C_m(κg) K^m A_v^{-m} ‖ψ‖_q + (error)`.

This is the Case-1 twin of `RBM.Gauss.momNorm_Uker_sumZero_scale_le'`, and the only analytic
input beyond the pathwise estimate of §1 is Minkowski against an affine majorant
(`RBM.Gauss.momNorm_le_affine`), because the pathwise bound is affine in `ψ(ω)`.

**No sum-zero premise.**  That is the whole point: on non-alternating charges the paper's
estimate is Case 1, and `RBM.SumZeroDyn.lkT` is not sum-zero. -/
theorem momNorm_Uker_short_scale_le' [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {m : ℕ}
    {ξ : Fin m → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {κg : ℝ} (hκg : 0 < κg)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (i₀ : Fin m) (hκt : κg ≤ ‖1 - (v : ℂ) * ξ i₀‖)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : Ω → LoopArg L m → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖G ω b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (G ω)) (a : LoopArg L m) :
    momNorm P q (fun ω => ‖Uker L ξ (u : ℂ) (v : ℂ) (G ω) a‖)
      ≤ cKerShort m κg * K ^ m * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * momNorm P q ψ
        + (cKerShort m κg * K ^ m * ((1 - s) / (1 - v)) ^ m * ζ
          + ((1 - s) / (1 - v)) ^ m * δ) := by
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith [hsu.trans huv]
  have hv0 : (0 : ℝ) ≤ v := (hs0.trans hsu).trans huv
  have hℓv : 0 < ellHat L (v : ℂ) := SumZeroDyn.ellHat_real_pos' L hL hv0 hv1
  have hc := SumZeroDyn.cKerShort_nonneg m hκg
  set ρ : ℝ := (1 - s) / (1 - v) with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρdef]; positivity
  have hmain0 : (0 : ℝ) ≤ cKerShort m κg * K ^ m
      * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m := by positivity
  have herr0 : (0 : ℝ) ≤ cKerShort m κg * K ^ m * ρ ^ m * ζ + ρ ^ m * δ := by positivity
  refine momNorm_le_affine hq hψ0 hint hmain0 herr0 (fun ω => ?_)
  rw [abs_of_nonneg (norm_nonneg _)]
  have hpt := norm_Uker_short_scale_le' L hL hξ hκg hs0 hsu huv hv1 i₀ hκt hκA hK
    (hψ0 ω) hζ hδ (hGM ω) (hGd ω) a
  refine hpt.trans (le_of_eq ?_)
  rw [hρdef]

/-- **(7.16) Case 1 in moment form, on a good event.**

The event-restricted replacement for `RBM.Gauss.momNorm_Uker_short_scale_le'`: the envelope and
the (7.13) fast decay are assumed **only on `Ξ`**, a crude deterministic envelope `Env` holds
everywhere, and the complement is paid for by Markov, exactly as
`RBM.Gauss.momNorm_le_affine_on_event` prescribes.

This is the shape the project's satisfiability discipline asks for — a deterministic decay
bound cannot hold at a "large constant times the identity" sample point with a small `δ`, so a
`∀ ω` decay row is a real strengthening.  It is stated here so that the Case-1 branch has its
event-restricted form available from the start: §3's producer still takes the `∀ ω` rows (the
same shape as T201's `hGd`/T219's `hDec…`, paper-delta `T236a`), because rewiring **either**
half to events needs `MeasurableSet` for the good set, which T220 records as not proved; when
it is, both halves rewire through this lemma and its Case-2 twin. -/
theorem momNorm_Uker_short_scale_le_on_event [IsProbabilityMeasure P] (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0) {m : ℕ}
    {ξ : Fin m → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {κg : ℝ} (hκg : 0 < κg)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (i₀ : Fin m) (hκt : κg ≤ ‖1 - (v : ℂ) * ξ i₀‖)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : Ω → LoopArg L m → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    {Ξ : Set Ω} (hΞm : MeasurableSet Ξ)
    (hGM : ∀ ω ∈ Ξ, ∀ b, ‖G ω b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ ω + ζ)
    (hGd : ∀ ω ∈ Ξ, FastDecay L (ellHat L (u : ℂ) * K) δ (G ω))
    (a : LoopArg L m) {Env pr : ℝ} (hEnv0 : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZint : Integrable (fun ω => |‖Uker L ξ (u : ℂ) (v : ℂ) (G ω) a‖| ^ q) P)
    (hZall : ∀ ω, ‖Uker L ξ (u : ℂ) (v : ℂ) (G ω) a‖ ≤ Env)
    (hP : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q (fun ω => ‖Uker L ξ (u : ℂ) (v : ℂ) (G ω) a‖)
      ≤ (cKerShort m κg * K ^ m * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * momNorm P q ψ
          + (cKerShort m κg * K ^ m * ((1 - s) / (1 - v)) ^ m * ζ
            + ((1 - s) / (1 - v)) ^ m * δ))
        + Env * pr ^ ((1 : ℝ) / q) := by
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith [hsu.trans huv]
  have hv0 : (0 : ℝ) ≤ v := (hs0.trans hsu).trans huv
  have hℓv : 0 < ellHat L (v : ℂ) := SumZeroDyn.ellHat_real_pos' L hL hv0 hv1
  have hc := SumZeroDyn.cKerShort_nonneg m hκg
  set ρ : ℝ := (1 - s) / (1 - v) with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρdef]; positivity
  have hmain0 : (0 : ℝ) ≤ cKerShort m κg * K ^ m
      * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m := by positivity
  have herr0 : (0 : ℝ) ≤ cKerShort m κg * K ^ m * ρ ^ m * ζ + ρ ^ m * δ := by positivity
  refine momNorm_le_affine_on_event hq hψ0 hint hZint hΞm hmain0 herr0 hEnv0 hpr
    (fun ω hω => ?_) (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hZall ω) hP
  rw [abs_of_nonneg (norm_nonneg _)]
  have hpt := norm_Uker_short_scale_le' L hL hξ hκg hs0 hsu huv hv1 i₀ hκt hκA hK
    (hψ0 ω) hζ hδ (hGM ω hω) (hGd ω hω) a
  refine hpt.trans (le_of_eq ?_)
  rw [hρdef]

/-- **(7.16) Case 1 in moment form at the paper's charge** `ξ = (m(σᵢ) m(σᵢ₊₁))ᵢ`, the short
edge being supplied by a repeated sign `σ_k = σ_{k+1}` and the bulk condition `|E| ≤ 2 - κ`
(`RBM.sqrt_le_norm_one_sub_xiOf`): the gap is `√κ`.

This is the estimate the initial datum and the drift of (5.20) are put through. -/
theorem momNorm_Uker_short_sigma_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    {σ : Fin (n + 2) → Bool} {k : Fin (n + 2)} (hk : σ k = σ (k + 1))
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖G ω b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (G ω)) (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G ω) a‖)
      ≤ cKerShort (n + 2) √κ * K ^ (n + 2)
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerShort (n + 2) √κ * K ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + ((1 - s) / (1 - v)) ^ (n + 2) * δ) := by
  have hE2 : |E| ≤ 2 := hEκ.trans (by linarith)
  have hv0 : (0 : ℝ) ≤ v := ((hs0.trans hsu).trans huv)
  exact momNorm_Uker_short_scale_le' L hL hq
    (fun i => (norm_xiOf_mSigma hE2 σ i).le) (Real.sqrt_pos.2 hκ0) hs0 hsu huv hv1 k
    (sqrt_le_norm_one_sub_xiOf hκ0 hκ1 hEκ hv0 hv1.le hk) hκA hK hζ hδ hψ0 hint hGM hGd a

/-- **(7.16) Case 1 in moment form at the doubled charge** `RBM.SumZeroDyn.xi2`, whose first
half is `xiOf (mSigma E) σ` (`RBM.SumZeroDyn.xi2`, T223), so a repeated sign of `σ` gives a
short edge of the doubled loop at `Fin.castAdd (n+2) k` — exactly the step
`RBM.SumZeroDyn.QV1_stochDom` takes for the quadratic variation of (5.86).

This is the estimate the `E ⊗ E` term of (5.24) is put through. -/
theorem momNorm_Uker_short_xi2_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    {σ : Fin (n + 2) → Bool} {k : Fin (n + 2)} (hk : σ k = σ (k + 1))
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : Ω → LoopArg L ((n + 2) + (n + 2)) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖G ω b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (G ω))
    (a : LoopArg L ((n + 2) + (n + 2))) :
    momNorm P q (fun ω => ‖Uker L (SumZeroDyn.xi2 E σ) (u : ℂ) (v : ℂ) (G ω) a‖)
      ≤ cKerShort ((n + 2) + (n + 2)) √κ * K ^ ((n + 2) + (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * momNorm P q ψ
        + (cKerShort ((n + 2) + (n + 2)) √κ * K ^ ((n + 2) + (n + 2))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2)) * ζ
          + ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2)) * δ) := by
  have hE : |E| < 2 := by
    have : |E| ≤ 2 - κ := hEκ
    linarith
  have hv0 : (0 : ℝ) ≤ v := ((hs0.trans hsu).trans huv)
  have hκt : √κ ≤ ‖1 - (v : ℂ) * SumZeroDyn.xi2 E σ (Fin.castAdd (n + 2) k)‖ := by
    rw [SumZeroDyn.xi2, Fin.append_left]
    exact sqrt_le_norm_one_sub_xiOf hκ0 hκ1 hEκ hv0 hv1.le hk
  exact momNorm_Uker_short_scale_le' L hL hq
    (SumZeroDyn.norm_xi2_le hE σ) (Real.sqrt_pos.2 hκ0) hs0 hsu huv hv1
    (Fin.castAdd (n + 2) k) hκt hκA hK hζ hδ hψ0 hint hGM hGd a

end Short716

/-! ### §2  The guarded right-hand side of (5.20), and its consumer

`RBM.MomentDuhamel.stochDom_of_momentDuhamel` is the unguarded consumer of
`RBM.MomentDuhamel.Hyp.momentDuhamel`: it asks its `hrhs` on **every** charge.  That cannot be
supplied — on an alternating charge Case 1 of (7.16) does not apply (there is no short edge) and
Case 2 does not apply either (`RBM.SumZeroDyn.lkT` is not sum-zero), so the unguarded slot has
no producer.  The guarded version below asks `hrhs` only on non-alternating charges, and
concludes only about them; that is exactly the half of §5.5's charge split that (5.101) does not
reach. -/

section Consumer

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The `hrhs` slot of `RBM.Gauss.stochDom_lkT_nonAlt_of_momentDuhamel`**: the three
right-hand terms of `RBM.MomentDuhamel.Hyp.momentDuhamel` — (5.20)'s initial datum, its drift,
and (5.24)'s `E ⊗ E` term under the square root — at the terminal time `v` and the control
`c_N (W ℓ_v η_v)^{-(n+2)}`, **restricted to non-alternating charges**.

Compare `RBM.Gauss.Rhs514QAt`: there are three terms instead of five, no tensor carries a
`Q_u`, and there is a guard.  Written out once as a `def` so that the producer of §3 and the
consumer below cannot drift apart. -/
def RhsNonAltAt (H : MomentDuhamel.Hyp X E s t n) (c v : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ q : LoopData (B.L N) (n + 2), SumZeroDyn.NonAlt q.1 →
      momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖)
        + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (H.F N u (X.H N u ω) q.1) q.2‖))
        + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
        ≤ C * ((N : ℝ) ^ (ε / 2) * (c N * (B.scale E N (v N) ^ (n + 2))⁻¹))

/-- **(5.20) on non-alternating charges gives `≺` directly.**

The guarded twin of `RBM.MomentDuhamel.stochDom_of_momentDuhamel`.  On a non-alternating charge
the conclusion is `‖(L-K)_{v,σ,a}‖ ≺ c_N A_v^{-(n+2)}`; on an alternating charge the family is
`0`, whose every moment norm vanishes, so nothing is claimed there.

**No `Q_u`, no Ward identity, no `RBM.SumZeroDyn.Hierarchy`**: the only random input is the
field `RBM.MomentDuhamel.Hyp.momentDuhamel`, which is (5.20) + (5.24) in moment form. -/
theorem stochDom_lkT_nonAlt_of_momentDuhamel (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (H : MomentDuhamel.Hyp X E s t n)
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Cv)
    {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N)
    (v : ℕ → ℝ) (hv : ∀ N, v N ∈ Set.Icc (s N) (t N)) (hrhs : RhsNonAltAt H c v) :
    StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.NonAlt q.1 then ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0)
      (fun N _ _ => c N * (B.scale E N (v N) ^ (n + 2))⁻¹) := by
  classical
  have hscale : ∀ N : ℕ, 0 < B.scale E N (v N) ^ (n + 2) := fun N =>
    pow_pos (B.scale_pos' hE N ((hs0 N).trans (hv N).1) ((hv N).2.trans_lt (ht1 N))) _
  have hΦ : ∀ (N : ℕ) (_q : LoopData (B.L N) (n + 2)),
      0 < c N * (B.scale E N (v N) ^ (n + 2))⁻¹ := fun N _ =>
    mul_pos (hc0 N) (inv_pos.2 (hscale N))
  refine stochDom_of_momentDom hcard hΦ (fun p N q => ?_) ?_
  · by_cases h : SumZeroDyn.NonAlt q.1
    · simpa [h] using H.integrable (2 * p) N (v N) (hv N).1 (hv N).2 q.1 q.2
    · simp [h]
  refine momentDom_of_momNorm_le (fun N q => (hΦ N q).le) fun ε hε p hp => ?_
  obtain ⟨C, hC0, hN⟩ := hrhs ε hε p hp
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hN, eventually_gt_atTop 0] with N hNq hN0 q
  have hNr : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  by_cases h : SumZeroDyn.NonAlt q.1
  · simp only [h, ite_true]
    exact (H.momentDuhamel p hp N q.1 (v N) (hv N).1 (hv N).2 q.2).trans (hNq q h)
  · simp only [h, ite_false]
    rw [momNorm_const (by omega : 2 * p ≠ 0) (le_refl (0 : ℝ))]
    have := (hΦ N q).le
    positivity

omit [IsProbabilityMeasure B.P] in
/-- **`RBM.Gauss.RhsNonAltAt` is monotone in its control, up to a constant.**  This is the
bridge between the producer of §3 — whose output control is `RBM.Gauss.cNum716Short`, bounded
uniformly along the paper's grid by `RBM.Gauss.gridS_cNum716Short_le` — and the shape
`lemma514_of_momentDuhamelQ` consumes, `max (Λ^{1/2} + Φ) 1`. -/
theorem RhsNonAltAt.of_le {H : MomentDuhamel.Hyp X E s t n} {c c' v : ℕ → ℝ} {C0 : ℝ}
    (hC0 : 0 < C0) (hle : ∀ᶠ N : ℕ in atTop, c N ≤ C0 * c' N)
    (hsc : ∀ N, (0 : ℝ) < B.scale E N (v N) ^ (n + 2))
    (h : RhsNonAltAt H c v) : RhsNonAltAt H c' v := by
  intro ε hε p hp
  obtain ⟨C, hC, hN⟩ := h ε hε p hp
  refine ⟨C * C0, by positivity, ?_⟩
  filter_upwards [hN, hle] with N h1 h2 q hna
  refine (h1 q hna).trans ?_
  have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hinv : (0 : ℝ) ≤ (B.scale E N (v N) ^ (n + 2))⁻¹ := (inv_pos.2 (hsc N)).le
  calc C * ((N : ℝ) ^ (ε / 2) * (c N * (B.scale E N (v N) ^ (n + 2))⁻¹))
      ≤ C * ((N : ℝ) ^ (ε / 2) * (C0 * c' N * (B.scale E N (v N) ^ (n + 2))⁻¹)) := by
        gcongr
    _ = C * C0 * ((N : ℝ) ^ (ε / 2) * (c' N * (B.scale E N (v N) ^ (n + 2))⁻¹)) := by ring

omit [IsProbabilityMeasure B.P] in
/-- **The producer's output lands in the assembly's slot.**  An `N`-independent bound on the
control is enough, because the control the assembly asks for, `max (Λ^{1/2} + Φ) 1`, is at
least `1`.  This is the compiled satisfiability chain for `hrhsNA`:
`RBM.Gauss.rhsNonAltAt_of_kernel_inputs_zero_err` → `RBM.Gauss.gridS_cNum716Short_le` → here. -/
theorem RhsNonAltAt.to_max {H : MomentDuhamel.Hyp X E s t n} {c v : ℕ → ℝ} {C0 : ℝ}
    (hC0 : 0 < C0) (hle : ∀ᶠ N : ℕ in atTop, c N ≤ C0)
    (hsc : ∀ N, (0 : ℝ) < B.scale E N (v N) ^ (n + 2)) (Λ Φ : ℕ → ℝ)
    (h : RhsNonAltAt H c v) :
    RhsNonAltAt H (fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1) v := by
  refine h.of_le hC0 ?_ hsc
  filter_upwards [hle] with N hN
  have h1 : (1 : ℝ) ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := le_max_right _ _
  nlinarith

end Consumer

/-! ### §3  The producer: (7.16) Case 1 on the three terms of (5.20) + (5.24)

The Case-1 twin of §5 of `RBM1D/Gauss/Lemma514QAssembly.lean`.  Hypothesis table, with the
owner of each row:

| row | what | owner |
|---|---|---|
| `hEnvI`, `hEnvF`, `hEnvE` | the size envelope of (7.16) | Step 2's a priori bounds |
| `hDecI`, `hDecF`, `hDecE` | the fast decay (7.13) | T220 (`FastDecayFlow`) |
| `hMψ`, `hMψE` | `‖ψ_u‖_{2p} ≺ Φ` on the window | the drift / `E⊗E` moment bounds |
| `hnum` | the arithmetic of (5.24) | **discharged**, §5 below |

Every row is restricted to non-alternating charges, because that is all the conclusion speaks
about; and `hκ0`/`hκ1`/`hEκ` are the bulk condition `|E| ≤ 2 - κ` that makes the repeated edge
*short*.  There is no `hkerC`/`hker2C` row, and no `(η_s/η_v)` prefactor on the main term. -/

section Producer

/-- `C_m(κg) K^m`, the multiplicative constant of (7.16) **Case 1** at loop length `m`.
Compare `RBM.Gauss.cKer716`: Case 1 spends `K^m`, Case 2 spends `K^{2m}`, and the constant
depends on the short-edge gap `κg`. -/
noncomputable def cKer716Short (m : ℕ) (κg Kd : ℝ) : ℝ := cKerShort m κg * Kd ^ m

/-- The additive error of (7.16) Case 1 at loop length `m`: the offset `ζ` of the size envelope
and the error `δ` of the fast decay (7.13), each carried across the window by `((1-s)/(1-v))^m`.
Compare `RBM.Gauss.errKer716`: the `δ` term of Case 1 carries **no** factor `L^m`. -/
noncomputable def errKer716Short (m : ℕ) (κg Kd ζ δ s v : ℝ) : ℝ :=
  cKerShort m κg * Kd ^ m * ((1 - s) / (1 - v)) ^ m * ζ + ((1 - s) / (1 - v)) ^ m * δ

theorem cKer716Short_nonneg (m : ℕ) {κg Kd : ℝ} (hκg : 0 < κg) (hKd : 0 ≤ Kd) :
    0 ≤ cKer716Short m κg Kd :=
  mul_nonneg (SumZeroDyn.cKerShort_nonneg m hκg) (pow_nonneg hKd _)

theorem errKer716Short_nonneg (m : ℕ) {κg Kd ζ δ s v : ℝ} (hκg : 0 < κg) (hKd : 0 ≤ Kd)
    (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ) (hsv : s ≤ v) (hv1 : v < 1) :
    0 ≤ errKer716Short m κg Kd ζ δ s v := by
  have h1 : (0 : ℝ) < 1 - v := by linarith
  have h2 : (0 : ℝ) ≤ (1 - s) / (1 - v) := div_nonneg (by linarith) h1.le
  have hr : (0 : ℝ) ≤ ((1 - s) / (1 - v)) ^ m := pow_nonneg h2 m
  have hc := SumZeroDyn.cKerShort_nonneg m hκg
  have hKm : (0 : ℝ) ≤ Kd ^ m := pow_nonneg hKd _
  have t1 : (0 : ℝ) ≤ cKerShort m κg * Kd ^ m * ((1 - s) / (1 - v)) ^ m * ζ :=
    mul_nonneg (mul_nonneg (mul_nonneg hc hKm) hr) hζ
  have t2 : (0 : ℝ) ≤ ((1 - s) / (1 - v)) ^ m * δ := mul_nonneg hr hδ
  unfold errKer716Short
  linarith

/-- `C M a + e ≤ (C+1) M (a+e)` for `M ≥ 1`: the additive error of (7.16) is absorbed into
the same constant as the main term, without touching the `N^{ε/2}` factor.

Shared by this file's Case-1 producer and `RBM.Gauss.rhs514QAt_of_kernel_inputs` (Case 2), where
it used to live; moved here by T236 rather than copied, since the two producers use it
verbatim. -/
theorem affine_absorb {a e C M : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hC : 0 ≤ C) (hM : 1 ≤ M) :
    C * (M * a) + e ≤ (C + 1) * (M * (a + e)) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have h1 : (0 : ℝ) ≤ M * a := mul_nonneg hM0 ha
  have hCM : (1 : ℝ) ≤ (C + 1) * M := by nlinarith
  have h2 : 1 * e ≤ ((C + 1) * M) * e := mul_le_mul_of_nonneg_right hCM he
  linarith [h1, h2]

/-- **`κ_A (1-w) ℓ̂_w = W ℓ_w η_w`.**  The free constant `κ_A` of (7.16) is fixed once and for
all to `W Im m^{(E)}`, and then the normalization of (7.16) is *literally* the scale
`RBM.Band.scale` of Lemmas 2.18–2.20.  Nothing is lost or gained: `η_w = (1-w) Im m^{(E)}`.

Shared by the Case-1 and Case-2 producers; moved here by T236 from
`RBM1D/Gauss/Lemma514QAssembly.lean`, not copied. -/
theorem scale_eq_kappaA {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (E : ℝ) (N : ℕ) (w : ℝ) :
    ((B.W N : ℝ) * (mE E).im) * ((1 - w) * ellHat (B.L N) ((w : ℝ) : ℂ))
      = B.scale E N w := by
  simp only [Band.scale, Band.ell, etaT]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The producer of `RBM.Gauss.RhsNonAltAt` out of §1's two Case-1 kernel estimates.** -/
theorem rhsNonAltAt_of_kernel_inputs {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {Kd ζ δ : ℝ} (hKd : 1 ≤ Kd) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 →
      ∀ (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + ζ)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 →
      ∀ (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖H.F N u (X.H N u ω) q.1 b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 →
      ∀ (ω : Ω) (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖eeFun B E N u (X.H N u ω) q.1 b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + ζ)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 → ∀ ω : Ω,
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd) δ
        (SumZeroDyn.lkT X E N (s N) ω q.1))
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 → ∀ ω : Ω,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) δ (H.F N u (X.H N u ω) q.1))
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 → ∀ ω : Ω,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) δ
        (eeFun B E N u (X.H N u ω) q.1))
    {Phi PhiE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hPhi0 : ∀ N q, 0 ≤ Phi N q) (hPhiE0 : ∀ N q, 0 ≤ PhiE N q)
    (hMψ : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N q))
    (hMψE : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P p (ψE N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * PhiE N q))
    {c : ℕ → ℝ}
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
      (cKer716Short (n + 2) √κ Kd * (B.scale E N (v N))⁻¹ ^ (n + 2) * Phi N q
          + errKer716Short (n + 2) √κ Kd ζ δ (s N) (v N)) * (1 + 2 * (v N - s N))
        + ((v N - s N) * (cKer716Short ((n + 2) + (n + 2)) √κ Kd
              * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * PhiE N q
            + errKer716Short ((n + 2) + (n + 2)) √κ Kd ζ δ (s N) (v N))) ^ ((1 : ℝ) / 2)
        ≤ c N * (B.scale E N (v N) ^ (n + 2))⁻¹) :
    RhsNonAltAt H c v := by
  have hE : |E| < 2 := by linarith
  have hκg : (0 : ℝ) < √κ := Real.sqrt_pos.2 hκ0
  intro ε hε p hp
  obtain ⟨C1, hC10, hA1⟩ := hMψ ε hε p hp
  obtain ⟨C3, hC30, hA3⟩ := hMψE ε hε p hp
  have hcMD := H.cMD_nonneg p
  have hKd0 : (0 : ℝ) ≤ Kd := by linarith
  set Csq : ℝ := (H.cMD p * (C3 + 1)) ^ ((1 : ℝ) / 2) with hCsqdef
  have hCsq0 : 0 ≤ Csq := Real.rpow_nonneg (by positivity) _
  refine ⟨C1 + Csq + 1, by positivity, ?_⟩
  filter_upwards [hA1, hA3, hnum, eventually_ge_atTop 1] with N h1 h3 hnumN hNge q hna
  obtain ⟨k, hk⟩ := hna
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have h2p : 2 * p ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  set Np : ℝ := (N : ℝ) ^ (ε / 2) with hNpdef
  have hNp1 : (1 : ℝ) ≤ Np := Real.one_le_rpow hNge1 (by positivity)
  have hNp0 : (0 : ℝ) < Np := lt_of_lt_of_le one_pos hNp1
  have hs0N := hs0 N
  have hsvN := hsv N
  have hv1 : v N < 1 := lt_of_le_of_lt (hvt N) (ht1 N)
  have hv0 : (0 : ℝ) ≤ v N := hs0N.trans hsvN
  have hκA : (0 : ℝ) < (B.W N : ℝ) * (mE E).im := by
    have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have := mE_im_pos hE
    positivity
  have hbr : ∀ w : ℝ, ((B.W N : ℝ) * (mE E).im) * ((1 - w) * ellHat (B.L N) ((w : ℝ) : ℂ))
      = B.scale E N w := fun w => scale_eq_kappaA B E N w
  set Av : ℝ := (B.scale E N (v N))⁻¹ ^ (n + 2) with hAvdef
  set Av2 : ℝ := (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) with hAv2def
  set Eb : ℝ := errKer716Short (n + 2) √κ Kd ζ δ (s N) (v N) with hEbdef
  set Eb2 : ℝ := errKer716Short ((n + 2) + (n + 2)) √κ Kd ζ δ (s N) (v N) with hEb2def
  have hEb0 : (0 : ℝ) ≤ Eb := errKer716Short_nonneg _ hκg hKd0 hζ hδ hsvN hv1
  have hEb20 : (0 : ℝ) ≤ Eb2 := errKer716Short_nonneg _ hκg hKd0 hζ hδ hsvN hv1
  have hscale : (0 : ℝ) < B.scale E N (v N) := B.scale_pos' hE N hv0 hv1
  have hAv0 : (0 : ℝ) ≤ Av := by rw [hAvdef]; positivity
  have hAv20 : (0 : ℝ) ≤ Av2 := by rw [hAv2def]; positivity
  have hcK0 : (0 : ℝ) ≤ cKer716Short (n + 2) √κ Kd := cKer716Short_nonneg _ hκg hKd0
  have hcK20 : (0 : ℝ) ≤ cKer716Short ((n + 2) + (n + 2)) √κ Kd :=
    cKer716Short_nonneg _ hκg hKd0
  set Kmain : ℝ := cKer716Short (n + 2) √κ Kd * Av * Phi N q + Eb with hKmaindef
  set K3 : ℝ := (v N - s N) * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q + Eb2)
    with hK3def
  have hKmain0 : (0 : ℝ) ≤ Kmain := by
    rw [hKmaindef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716Short (n + 2) √κ Kd * Av * Phi N q := by positivity
    linarith
  have hvs : (0 : ℝ) ≤ v N - s N := by linarith
  have hK30 : (0 : ℝ) ≤ K3 := by
    rw [hK3def]
    have hPE := hPhiE0 N q
    have : (0 : ℝ) ≤ cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q := by positivity
    exact mul_nonneg hvs (by linarith)
  set Mb : ℝ := cKer716Short (n + 2) √κ Kd * Av * (C1 * (Np * Phi N q)) + Eb with hMbdef
  have hMb0 : (0 : ℝ) ≤ Mb := by
    rw [hMbdef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716Short (n + 2) √κ Kd * Av * (C1 * (Np * Phi N q)) := by positivity
    linarith
  have hMbK : Mb ≤ (C1 + 1) * (Np * Kmain) := by
    rw [hMbdef, hKmaindef]
    have e1 : cKer716Short (n + 2) √κ Kd * Av * (C1 * (Np * Phi N q))
        = C1 * (Np * (cKer716Short (n + 2) √κ Kd * Av * Phi N q)) := by ring
    rw [e1]
    exact affine_absorb (mul_nonneg (mul_nonneg hcK0 hAv0) (hPhi0 N q)) hEb0 hC10.le hNp1
  have hnn : (0 : ℝ) ≤ cKerShort (n + 2) √κ * Kd ^ (n + 2)
      * (B.scale E N (v N))⁻¹ ^ (n + 2) :=
    mul_nonneg (mul_nonneg (SumZeroDyn.cKerShort_nonneg _ hκg) (pow_nonneg hKd0 _))
      (pow_nonneg (inv_nonneg.2 hscale.le) _)
  -- Term 1: the initial datum of (5.20)
  have hT1 : momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖) ≤ Mb := by
    have key := momNorm_Uker_short_sigma_le (P := B.P) (B.L N) hL3 h2p hκ0 hκ1 hEκ hk
      (s := s N) (u := s N) (v := v N) hs0N le_rfl hsvN hv1 hκA hKd hζ hδ
      (G := fun ω => SumZeroDyn.lkT X E N (s N) ω q.1) (ψ := ψ N (s N) q)
      (fun ω => hψ0 N (s N) q ω) (hψint (2 * p) N (s N) q)
      (fun ω b => by rw [hbr]; exact hEnvI N q ⟨k, hk⟩ ω b)
      (fun ω => hDecI N q ⟨k, hk⟩ ω) q.2
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hstep := mul_le_mul_of_nonneg_left (h1 (s N) le_rfl hsvN q) hnn
    rw [hMbdef, hAvdef, cKer716Short, hEbdef, errKer716Short]
    linarith [hstep]
  -- Term 2: the drift of (5.20)
  have hI2 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (H.F N u (X.H N u ω) q.1) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_short_sigma_le (P := B.P) (B.L N) hL3 h2p hκ0 hκ1 hEκ hk
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv1 hκA hKd hζ hδ
      (G := fun ω => H.F N u (X.H N u ω) q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvF N u hu.1 hu.2 q ⟨k, hk⟩ ω b)
      (fun ω => hDecF N u hu.1 hu.2 q ⟨k, hk⟩ ω) q.2
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hstep := mul_le_mul_of_nonneg_left (h1 u hu.1 hu.2 q) hnn
    rw [hMbdef, hAvdef, cKer716Short, hEbdef, errKer716Short]
    linarith [hstep]
  -- Term 3: the `E ⊗ E` term of (5.24), under the square root
  have hI3nn : (0 : ℝ) ≤ ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖) :=
    intervalIntegral.integral_nonneg hsvN fun u _ => momNorm_nonneg _ _ _
  have hI3 : (∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖))
      ≤ (C3 + 1) * (Np * K3) := by
    have hconst : ∀ u ∈ Set.Icc (s N) (v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)
        ≤ cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2 := by
      intro u hu
      have key := momNorm_Uker_short_xi2_le (P := B.P) (B.L N) hL3 hp0 hκ0 hκ1 hEκ hk
        (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv1 hκA hKd hζ hδ
        (G := fun ω => eeFun B E N u (X.H N u ω) q.1) (ψ := ψE N u q)
        (fun ω => hψE0 N u q ω) (hψEint p N u q)
        (fun ω b => by rw [hbr]; exact hEnvE N u hu.1 hu.2 q ⟨k, hk⟩ ω b)
        (fun ω => hDecE N u hu.1 hu.2 q ⟨k, hk⟩ ω) (Fin.append q.2 q.2)
      rw [hbr (v N)] at key
      refine key.trans ?_
      have hnn2 : (0 : ℝ) ≤ cKerShort ((n + 2) + (n + 2)) √κ * Kd ^ ((n + 2) + (n + 2))
          * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) :=
        mul_nonneg (mul_nonneg (SumZeroDyn.cKerShort_nonneg _ hκg) (pow_nonneg hKd0 _))
          (pow_nonneg (inv_nonneg.2 hscale.le) _)
      have hstep := mul_le_mul_of_nonneg_left (h3 u hu.1 hu.2 q) hnn2
      rw [hAv2def, cKer716Short, hEb2def, errKer716Short]
      linarith [hstep]
    have hbase : (0 : ℝ) ≤ cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q :=
      mul_nonneg (mul_nonneg hcK20 hAv20) (hPhiE0 N q)
    have hfac : cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2
        ≤ (C3 + 1) * (Np * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q + Eb2)) := by
      have e1 : cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q)) := by ring
      rw [e1]
      exact affine_absorb hbase hEb20 hC30.le hNp1
    have hMnn : (0 : ℝ)
        ≤ cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2 := by
      have h0 : (0 : ℝ)
          ≤ C3 * (Np * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q)) :=
        mul_nonneg hC30.le (mul_nonneg hNp0.le hbase)
      have e1 : cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q)) := by ring
      rw [e1]
      linarith
    refine (intervalIntegral_le_of_le_const hsvN hMnn hconst).trans ?_
    rw [hK3def]
    calc (v N - s N)
          * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2)
        ≤ (v N - s N) * ((C3 + 1)
            * (Np * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q + Eb2))) :=
          mul_le_mul_of_nonneg_left hfac hvs
      _ = (C3 + 1) * (Np * ((v N - s N)
            * (cKer716Short ((n + 2) + (n + 2)) √κ Kd * Av2 * PhiE N q + Eb2))) := by ring
  have hT3 : (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
      ≤ Csq * (Np * K3 ^ ((1 : ℝ) / 2)) := by
    have hstep : (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
          ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
            (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
        ≤ ((H.cMD p * (C3 + 1)) * (Np * K3)) ^ ((1 : ℝ) / 2) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc H.cMD p * _ ≤ H.cMD p * ((C3 + 1) * (Np * K3)) :=
            mul_le_mul_of_nonneg_left hI3 hcMD
        _ = (H.cMD p * (C3 + 1)) * (Np * K3) := by ring
    refine hstep.trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hNp0.le hK30, ← hCsqdef]
    have hhalf : Np ^ ((1 : ℝ) / 2) ≤ Np := by
      calc Np ^ ((1 : ℝ) / 2) ≤ Np ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hNp1 (by norm_num)
        _ = Np := Real.rpow_one Np
    have hK3s : (0 : ℝ) ≤ K3 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hK30 _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhalf hK3s) hCsq0
  -- assemble
  have hK3s : (0 : ℝ) ≤ K3 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hK30 _
  have htwo : Mb + 2 * ((v N - s N) * Mb)
      ≤ (C1 + 1) * (Np * (Kmain * (1 + 2 * (v N - s N)))) := by
    have h6 : Mb * (1 + 2 * (v N - s N))
        ≤ ((C1 + 1) * (Np * Kmain)) * (1 + 2 * (v N - s N)) :=
      mul_le_mul_of_nonneg_right hMbK (by linarith)
    linarith [h6]
  have hmain : Mb + 2 * ((v N - s N) * Mb) + Csq * (Np * K3 ^ ((1 : ℝ) / 2))
      ≤ (C1 + Csq + 1) * (Np * (Kmain * (1 + 2 * (v N - s N)) + K3 ^ ((1 : ℝ) / 2))) := by
    have hpos : (0 : ℝ) ≤ Np * (Kmain * (1 + 2 * (v N - s N))) :=
      mul_nonneg hNp0.le (mul_nonneg hKmain0 (by linarith))
    have t1 : (0 : ℝ) ≤ Csq * (Np * (Kmain * (1 + 2 * (v N - s N)))) := mul_nonneg hCsq0 hpos
    have t2 : (0 : ℝ) ≤ (C1 + 1) * (Np * K3 ^ ((1 : ℝ) / 2)) :=
      mul_nonneg (by linarith) (mul_nonneg hNp0.le hK3s)
    linarith [htwo, t1, t2]
  refine le_trans (by linarith [hT1, hI2, hT3]) (hmain.trans ?_)
  have hfin := hnumN q
  rw [← hKmaindef, ← hK3def] at hfin
  have hC : (0 : ℝ) ≤ C1 + Csq + 1 := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin hNp0.le) hC

end Producer

/-! ### §4  §5.5's charge split, with the `(-,+)` exception folded in

`RBM.Gauss.stochDom_lkT_of_qGood_nonAlt` splits `Ξ^{(L-K)}` into `QGood` and `¬ QGood`.  That
is not quite the split the two *producers* deliver: (5.101) covers `QGood` and (5.20) + (7.16)
Case 1 covers `NonAlt`, and by `RBM.SumZeroDyn.eq_zero_of_not_nonAlt_not_qGood` the two classes
exhaust everything **except** `σ = (-,+)` at length `2`.

That one charge is handled here exactly as `RBM.SumZeroDyn.lemma514_flow` handles it: rotating
a `2`-loop leaves `L - K` unchanged (`RBM.SumZeroDyn.lkT_swap2`) and turns `(-,+)` into the
`QGood` charge `(+,-)` (`RBM.SumZeroDyn.qGood_swap2`), so the `QGood` bound applies to it after
a reindexing of the parameter set (`RBM.StochDom.precomp_param`) — which costs nothing, because
`RBM.StochDom` quantifies over the index *inside* the probability. -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **The two producers' charge classes cover every charge.**

`QGood` (where (5.101) applies) plus `NonAlt` (where (5.20) + (7.16) Case 1 applies) exhaust
`{+,-}^{n+2}` up to the single charge `(-,+)` at length `2`, which the `QGood` bound reaches
after one rotation.  Hence the price is `2 c₁ + c₂`, not `c₁ + c₂`: the `QGood` control is used
twice, once at `q` and once at the rotated `q`.

Compare `RBM.Gauss.stochDom_lkT_of_qGood_nonAlt`, whose second input is the complement
`¬ QGood`.  That statement is the one this file cannot supply: off `QGood` the charge is
non-alternating *or* exceptional, and (7.16) Case 1 says nothing about the exceptional one. -/
theorem stochDom_lkT_of_qGood_nonAlt' (hE : |E| < 2) {n : ℕ} {v : ℕ → ℝ}
    (hv0 : ∀ N, 0 ≤ v N) (hv1 : ∀ N, v N < 1) {c1 c2 : ℕ → ℝ}
    (h1 : StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood q.1 then ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0)
      (fun N _ _ => c1 N))
    (h2 : StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.NonAlt q.1 then ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0)
      (fun N _ _ => c2 N)) :
    StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
      (fun N _ _ => c1 N + c1 N + c2 N) := by
  classical
  have hrot := h1.precomp_param (fun (N : ℕ) (q : LoopData (B.L N) (n + 2)) =>
    (((fun i => q.1 (i + 1)), (fun i => q.2 (i + 1))) : LoopData (B.L N) (n + 2)))
  refine StochDom.of_le_left (fun N q ω => ?_) ((h1.add hrot).add h2)
  simp only [Pi.add_apply]
  by_cases hq : SumZeroDyn.QGood q.1
  · have h0 : (0 : ℝ) ≤ (if SumZeroDyn.QGood (fun i => q.1 (i + 1)) then
        ‖SumZeroDyn.lkT X E N (v N) ω (fun i => q.1 (i + 1)) (fun i => q.2 (i + 1))‖ else 0) := by
      split_ifs <;> positivity
    have h0' : (0 : ℝ) ≤ (if SumZeroDyn.NonAlt q.1 then
        ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0) := by
      split_ifs <;> positivity
    simp only [hq, ite_true]
    linarith
  · by_cases hna : SumZeroDyn.NonAlt q.1
    · have h0 : (0 : ℝ) ≤ (if SumZeroDyn.QGood (fun i => q.1 (i + 1)) then
          ‖SumZeroDyn.lkT X E N (v N) ω (fun i => q.1 (i + 1)) (fun i => q.2 (i + 1))‖
          else 0) := by
        split_ifs <;> positivity
      simp only [hq, hna, ite_true, ite_false]
      linarith
    · obtain rfl := SumZeroDyn.eq_zero_of_not_nonAlt_not_qGood hna hq
      have hqr : SumZeroDyn.QGood (fun i => q.1 (i + 1)) :=
        SumZeroDyn.qGood_swap2 q.1 hna hq
      have heq := SumZeroDyn.lkT_swap2 X hE (hv0 N) (hv1 N) ω q.1 q.2
      have h0' : (0 : ℝ) ≤ (if SumZeroDyn.NonAlt q.1 then
          ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0) := by
        split_ifs; positivity
      simp only [hq, hqr, ite_true, ite_false]
      rw [← heq]
      linarith

end Split

/-! ### §5  Satisfiability

Four things have to be checked of the Case-1 bundle, and all four are checked here by compiled
statements rather than by prose.

1. **The guard is not empty.**  If no charge were non-alternating, everything in §2–§4 would be
   vacuously true.  `RBM.Gauss.nonAlt_const`: every constant charge is non-alternating.
2. **The estimated object is not `0`.**  `RBM.Gauss.norm_Uker_witTensor_self_ne_zero`: on the
   degenerate window `u = v` the left-hand side of §1 is `‖G_a‖`, and at the origin the witness
   tensor takes the value `κ ≠ 0`.  So the Case-1 estimate is not a statement about `0` — the
   analogue, on this side, of the `Q_u`-fixes-it clause of `RBM.Gauss.gridS_Q716_witness`
   (there is no projection here, so there is nothing that could have collapsed).
3. **The (7.16) Case-1 tier really is available on the window the six-step construction
   uses.**  `RBM.Gauss.gridS_short_witness`, on the paper's own p. 24 grid `1 - s_k = W^{-kτ'}`
   (`RBM.gridS`), with `ζ = 0`, the (7.13) error `δ = 0`, `K = 3` and a constant that depends on
   neither `N`, nor `W`, nor `τ'`, nor the grid index `k`.  **No short-window hypothesis** is
   used (`hτ'` is only `0 ≤ τ'`, `W` is arbitrary) and `v ↑ 1` is allowed.  Contrast
   `RBM.Gauss.no_const_hkerC_on_gridS`, where the constant is `(W^{τ'})^{m+2}`.
4. **The numeric row of §3 needs no owner.**  `RBM.Gauss.hnum_le_of_zero_err_short` shows it
   holds with *equality* at `RBM.Gauss.cNum716Short` once the two errors vanish, and
   `RBM.Gauss.gridS_cNum716Short_le` bounds that constant uniformly along the grid. -/

section Satisfiability

/-- **The `NonAlt` guard of §2–§4 is satisfiable**: a constant charge repeats every sign, so it
is non-alternating at `k = 0`.  Without this the guarded statements would be vacuous. -/
theorem nonAlt_const {m : ℕ} (b : Bool) : SumZeroDyn.NonAlt (fun _ : Fin (m + 2) => b) :=
  ⟨0, rfl⟩

/-- The constant of (5.24) at which the `hnum` row of §3 holds with equality once `ζ = δ = 0`:
the main term of (7.16) Case 1 at loop length `m`, carried across the window by `1 + 2(v-s)`,
plus the square root of the `E ⊗ E` term at loop length `2m`.  The Case-1 twin of
`RBM.Gauss.cNum716`. -/
noncomputable def cNum716Short (m : ℕ) (κg Kd Phi PhiE s v : ℝ) : ℝ :=
  cKer716Short m κg Kd * Phi * (1 + 2 * (v - s))
    + ((v - s) * (cKer716Short (m + m) κg Kd * PhiE)) ^ ((1 : ℝ) / 2)

theorem cNum716Short_nonneg (m : ℕ) {κg Kd Phi PhiE s v : ℝ} (hκg : 0 < κg) (hKd : 0 ≤ Kd)
    (hPhi : 0 ≤ Phi) (hPhiE : 0 ≤ PhiE) (hsv : s ≤ v) :
    0 ≤ cNum716Short m κg Kd Phi PhiE s v := by
  have hvs : (0 : ℝ) ≤ v - s := by linarith
  have h1 : (0 : ℝ) ≤ cKer716Short m κg Kd * Phi * (1 + 2 * (v - s)) :=
    mul_nonneg (mul_nonneg (cKer716Short_nonneg m hκg hKd) hPhi) (by linarith)
  have h2 : (0 : ℝ) ≤ ((v - s) * (cKer716Short (m + m) κg Kd * PhiE)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (mul_nonneg hvs (mul_nonneg (cKer716Short_nonneg (m + m) hκg hKd) hPhiE)) _
  rw [cNum716Short]; linarith

/-- **`RBM.Gauss.cNum716Short` is uniform on any window of length at most `1`.**  The bound
mentions neither `L` nor the window, so in particular it is independent of the grid index. -/
theorem cNum716Short_le (m : ℕ) {κg Kd Phi PhiE s v : ℝ} (hκg : 0 < κg) (hKd : 0 ≤ Kd)
    (hPhi : 0 ≤ Phi) (hPhiE : 0 ≤ PhiE) (hsv : s ≤ v) (hvs1 : v - s ≤ 1) :
    cNum716Short m κg Kd Phi PhiE s v
      ≤ 3 * (cKer716Short m κg Kd * Phi) + (cKer716Short (m + m) κg Kd * PhiE) ^ ((1 : ℝ) / 2) := by
  have hvs : (0 : ℝ) ≤ v - s := by linarith
  have hcK := cKer716Short_nonneg m hκg hKd
  have hcK2 := cKer716Short_nonneg (m + m) hκg hKd
  have h1 : cKer716Short m κg Kd * Phi * (1 + 2 * (v - s)) ≤ 3 * (cKer716Short m κg Kd * Phi) := by
    have hb : (0 : ℝ) ≤ cKer716Short m κg Kd * Phi := mul_nonneg hcK hPhi
    nlinarith
  have h2 : ((v - s) * (cKer716Short (m + m) κg Kd * PhiE)) ^ ((1 : ℝ) / 2)
      ≤ (cKer716Short (m + m) κg Kd * PhiE) ^ ((1 : ℝ) / 2) := by
    refine Real.rpow_le_rpow (mul_nonneg hvs (mul_nonneg hcK2 hPhiE)) ?_ (by norm_num)
    have hb : (0 : ℝ) ≤ cKer716Short (m + m) κg Kd * PhiE := mul_nonneg hcK2 hPhiE
    nlinarith
  rw [cNum716Short]; linarith

/-- **`RBM.Gauss.cNum716Short` on the paper's p. 24 grid**, uniformly in the index `k`, in `W`
and in `τ'`. -/
theorem gridS_cNum716Short_le (m : ℕ) {κg Kd Phi PhiE : ℝ} (hκg : 0 < κg) (hKd : 0 ≤ Kd)
    (hPhi : 0 ≤ Phi) (hPhiE : 0 ≤ PhiE) {W τ' : ℝ} (hW : 1 ≤ W) (hτ' : 0 ≤ τ') (k : ℕ) :
    cNum716Short m κg Kd Phi PhiE (gridS W τ' k) (gridS W τ' (k + 1))
      ≤ 3 * (cKer716Short m κg Kd * Phi)
        + (cKer716Short (m + m) κg Kd * PhiE) ^ ((1 : ℝ) / 2) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  exact cNum716Short_le m hκg hKd hPhi hPhiE (gridS_mono hW hτ' (Nat.le_succ k))
    (by have := gridS_nonneg hW hτ' k; have := gridS_lt_one (τ' := τ') hW0 (k + 1); linarith)

/-- **The arithmetic of (5.24) at zero error, once and for all.**

The shared core of `RBM.Gauss.hnum_le_of_zero_err` (Case 2) and
`RBM.Gauss.hnum_le_of_zero_err_short` (Case 1): with the two errors gone, the whole `hnum` row
is the single algebraic identity `A^{-m} · (…) + (A^{-2m} · (…))^{1/2} = A^{-m} · (… + …^{1/2})`,
i.e. the square root of the `E ⊗ E` term at loop length `2m` lands on the **same** power
`A_v^{-m}` as the main term.  T236 factored it out rather than copying the script a second
time; the two cases differ only in which constant and which window weight they feed it. -/
theorem num_zero_err_aux (m : ℕ) {cK cK2 A Phi PhiE w : ℝ} (hcK2 : 0 ≤ cK2) (hA : 0 < A)
    (hPhiE : 0 ≤ PhiE) :
    cK * A⁻¹ ^ m * Phi * w + (cK2 * A⁻¹ ^ (m + m) * PhiE) ^ ((1 : ℝ) / 2)
      ≤ (cK * Phi * w + (cK2 * PhiE) ^ ((1 : ℝ) / 2)) * (A ^ m)⁻¹ := by
  have hz : (0 : ℝ) ≤ A⁻¹ ^ m := by positivity
  have hy : (0 : ℝ) ≤ cK2 * PhiE := mul_nonneg hcK2 hPhiE
  have hsplit : cK2 * A⁻¹ ^ (m + m) * PhiE = (cK2 * PhiE) * (A⁻¹ ^ m) ^ 2 := by
    rw [pow_add]; ring
  have hsq : ((A⁻¹ ^ m) ^ 2) ^ ((1 : ℝ) / 2) = A⁻¹ ^ m := by
    rw [← Real.rpow_natCast (A⁻¹ ^ m) 2, ← Real.rpow_mul hz]
    norm_num
  rw [hsplit, Real.mul_rpow hy (by positivity), hsq, inv_pow]
  ring_nf
  exact le_rfl

/-- **The `hnum` row of `RBM.Gauss.rhsNonAltAt_of_kernel_inputs` holds with equality** once the
offset `ζ` of the envelope and the error `δ` of (7.13) vanish.  Note where the `(1-s)/(1-v)`
factors went: they sit *only* inside `RBM.Gauss.errKer716Short`, so at `ζ = δ = 0` the estimate
carries **no** `η_s/η_v` prefactor — which is what (5.92) demands. -/
theorem hnum_le_of_zero_err_short (m : ℕ) {κg Kd A Phi PhiE s v : ℝ} (hκg : 0 < κg)
    (hKd : 0 ≤ Kd) (hA : 0 < A) (hPhiE : 0 ≤ PhiE) (hsv : s ≤ v) :
    (cKer716Short m κg Kd * A⁻¹ ^ m * Phi + errKer716Short m κg Kd 0 0 s v) * (1 + 2 * (v - s))
        + ((v - s) * (cKer716Short (m + m) κg Kd * A⁻¹ ^ (m + m) * PhiE
            + errKer716Short (m + m) κg Kd 0 0 s v)) ^ ((1 : ℝ) / 2)
      ≤ cNum716Short m κg Kd Phi PhiE s v * (A ^ m)⁻¹ := by
  have herr : ∀ j : ℕ, errKer716Short j κg Kd 0 0 s v = 0 := by intro j; simp [errKer716Short]
  have hvs : (0 : ℝ) ≤ v - s := by linarith
  have hre : (v - s) * (cKer716Short (m + m) κg Kd * A⁻¹ ^ (m + m) * PhiE)
      = cKer716Short (m + m) κg Kd * A⁻¹ ^ (m + m) * ((v - s) * PhiE) := by ring
  have hre2 : (v - s) * (cKer716Short (m + m) κg Kd * PhiE)
      = cKer716Short (m + m) κg Kd * ((v - s) * PhiE) := by ring
  rw [herr, herr, add_zero, add_zero, hre, cNum716Short, hre2]
  have key := num_zero_err_aux m (cK := cKer716Short m κg Kd)
    (cK2 := cKer716Short (m + m) κg Kd) (A := A) (Phi := Phi)
    (PhiE := (v - s) * PhiE) (w := 1 + 2 * (v - s))
    (cKer716Short_nonneg (m + m) hκg hKd) hA (mul_nonneg hvs hPhiE)
  calc (cKer716Short m κg Kd * A⁻¹ ^ m * Phi) * (1 + 2 * (v - s))
        + (cKer716Short (m + m) κg Kd * A⁻¹ ^ (m + m) * ((v - s) * PhiE)) ^ ((1 : ℝ) / 2)
      = cKer716Short m κg Kd * A⁻¹ ^ m * Phi * (1 + 2 * (v - s))
        + (cKer716Short (m + m) κg Kd * A⁻¹ ^ (m + m) * ((v - s) * PhiE)) ^ ((1 : ℝ) / 2) := by
        ring_nf
    _ ≤ _ := key

section WitnessModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **`RBM.Gauss.rhsNonAltAt_of_kernel_inputs` with the `hnum` row discharged.**

Same producer, with `ζ = δ = 0` and the two moment controls constant in the charge — which is
the shape `RBM.Step3.Lemma514` hands down, its controls being `Λ N` and `Φ N`.  The output
control is `RBM.Gauss.cNum716Short`, bounded uniformly along the paper's grid by
`RBM.Gauss.gridS_cNum716Short_le`. -/
theorem rhsNonAltAt_of_kernel_inputs_zero_err {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1) {Kd : ℝ} (hKd : 1 ≤ Kd)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 →
      ∀ (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + 0)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 →
      ∀ (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖H.F N u (X.H N u ω) q.1 b‖ ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + 0)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 →
      ∀ (ω : Ω) (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖eeFun B E N u (X.H N u ω) q.1 b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + 0)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 → ∀ ω : Ω,
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd) 0
        (SumZeroDyn.lkT X E N (s N) ω q.1))
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 → ∀ ω : Ω,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) 0 (H.F N u (X.H N u ω) q.1))
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), SumZeroDyn.NonAlt q.1 → ∀ ω : Ω,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) 0 (eeFun B E N u (X.H N u ω) q.1))
    {Phi PhiE : ℕ → ℝ} (hPhi0 : ∀ N, 0 ≤ Phi N) (hPhiE0 : ∀ N, 0 ≤ PhiE N)
    (hMψ : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N))
    (hMψE : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P p (ψE N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * PhiE N)) :
    RhsNonAltAt H
      (fun N => cNum716Short (n + 2) √κ Kd (Phi N) (PhiE N) (s N) (v N)) v := by
  have hE : |E| < 2 := by linarith
  refine rhsNonAltAt_of_kernel_inputs hκ0 hκ1 hEκ H hs0 hsv hvt ht1 hKd le_rfl le_rfl
    hψ0 hψE0 hψint hψEint hEnvI hEnvF hEnvE hDecI hDecF hDecE
    (Phi := fun N _ => Phi N) (PhiE := fun N _ => PhiE N)
    (fun N _ => hPhi0 N) (fun N _ => hPhiE0 N) hMψ hMψE ?_
  refine Eventually.of_forall fun N q => ?_
  have hv0 : (0 : ℝ) ≤ v N := (hs0 N).trans (hsv N)
  have hv1 : v N < 1 := lt_of_le_of_lt (hvt N) (ht1 N)
  exact hnum_le_of_zero_err_short (n + 2) (Real.sqrt_pos.2 hκ0) (by linarith)
    (B.scale_pos' hE N hv0 hv1) (hPhiE0 N) (hsv N)

end WitnessModel

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The object the Case-1 estimate bounds is not `0`.**  On the degenerate window `u = v` the
evolution kernel is the identity (`RBM.Uker_self`), so the left-hand side of §1 at the origin is
`|κ| ≠ 0`.  Together with `RBM.Gauss.nonAlt_const` this is the anti-vacuity pair for the
non-alternating branch: the guard is inhabited and the estimated quantity is non-zero. -/
theorem norm_Uker_witTensor_self_ne_zero (L : ℕ) [NeZero L] (hL : 3 ≤ L) {m : ℕ} {E : ℝ}
    (hE : |E| ≤ 2) (σ : Fin (m + 2) → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {κ : ℂ}
    (hκ : κ ≠ 0) :
    ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((u : ℝ) : ℂ) (witTensor L m κ)
        (fun _ => 0)‖ ≠ 0 := by
  have ht : ∀ i, ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro i
    rw [norm_mul, norm_xiOf_mSigma hE σ i, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu0]
    exact hu1
  rw [Uker_self L hL ht, witTensor_zero_arg L hL]
  simpa using hκ

/-- **The satisfiability witness for (7.16) Case 1, on the paper's own p. 24 grid.**

One window `s_N = s_k`, `v_N = s_{k+1}` of the grid `1 - s_j = W^{-jτ'}` — the window the
six-step construction actually uses, and on which `RBM.Gauss.no_const_hkerC_on_gridS` shows the
(7.1) tier has **no** `N`-independent constant.  Every premise of
`RBM.Gauss.momNorm_Uker_short_sigma_le` is met there, with

* a **non-alternating** charge (the constant charge, `RBM.Gauss.nonAlt_const`) — so the guard of
  §2–§4 is exercised, not circumvented;
* a tensor that is **not zero** (`RBM.Gauss.witTensor_ne_zero`), and whose evolved kernel is
  non-zero on the degenerate window (`RBM.Gauss.norm_Uker_witTensor_self_ne_zero`);
* `ζ = 0` and the (7.13) error `δ = 0` — the witness is exactly supported in a ball of radius
  `1`;
* `ψ ≡ 1`, `K = 3`, both independent of `N`;

and the conclusion is the **time-`v_N`** normalisation times `cKerShort (m+2) √κ · 3^{m+2}`,
which depends on neither `N`, nor `W`, nor `τ'`, nor `k`.

**No short-window hypothesis is used**: `hτ'` is only `0 ≤ τ'`, and `W` is arbitrary. -/
theorem gridS_short_witness [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {m : ℕ} {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    {W τ' : ℝ} (hW : 1 ≤ W) (hτ' : 0 ≤ τ') (k : ℕ) {κA : ℝ} (hκA : 0 < κA)
    (a : LoopArg L (m + 2)) :
    (witTensor L m
        (((κA * ((1 - gridS W τ' k) * ellHat L ((gridS W τ' k : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
      ≠ 0)
    ∧ SumZeroDyn.NonAlt (fun _ : Fin (m + 2) => true)
    ∧ momNorm P q (fun _ω : Ω =>
        ‖Uker L (xiOf (mSigma E) (fun _ => true)) ((gridS W τ' k : ℝ) : ℂ)
          ((gridS W τ' (k + 1) : ℝ) : ℂ)
          (witTensor L m
            (((κA * ((1 - gridS W τ' k) * ellHat L ((gridS W τ' k : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ))
          a‖)
        ≤ cKerShort (m + 2) √κ * 3 ^ (m + 2)
            * (κA * ((1 - gridS W τ' (k + 1))
                * ellHat L ((gridS W τ' (k + 1) : ℝ) : ℂ)))⁻¹ ^ (m + 2) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  set s : ℝ := gridS W τ' k with hsdef
  set v : ℝ := gridS W τ' (k + 1) with hvdef
  have hs0 : 0 ≤ s := gridS_nonneg hW hτ' k
  have hsv : s ≤ v := gridS_mono hW hτ' (Nat.le_succ k)
  have hv1 : v < 1 := gridS_lt_one hW0 (k + 1)
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hℓs : (1 : ℝ) / 2 ≤ ellHat L (s : ℂ) := half_le_ellHat_real L hL hs0 hs1
  have hℓs0 : (0 : ℝ) < ellHat L (s : ℂ) := by linarith
  have h1s : (0 : ℝ) < 1 - s := by linarith
  set c0 : ℝ := (κA * ((1 - s) * ellHat L (s : ℂ)))⁻¹ ^ (m + 2) with hc0def
  have hc00 : 0 < c0 := by rw [hc0def]; positivity
  refine ⟨witTensor_ne_zero L hL (by exact_mod_cast hc00.ne'), nonAlt_const true, ?_⟩
  have hdec : FastDecay L (ellHat L (s : ℂ) * 3) 0 (witTensor L m ((c0 : ℝ) : ℂ)) :=
    fastDecay_witTensor L hL _ (by linarith)
  have henv : ∀ (ω : Ω) (b : LoopArg L (m + 2)),
      ‖witTensor L m ((c0 : ℝ) : ℂ) b‖
        ≤ (κA * ((1 - s) * ellHat L (s : ℂ)))⁻¹ ^ (m + 2) * (1 : ℝ) + 0 := by
    intro ω b
    have h := norm_witTensor_le L (m := m) (κ := ((c0 : ℝ) : ℂ)) b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc00.le] at h
    rw [← hc0def]; linarith
  have hint : Integrable (fun _ω : Ω => (1 : ℝ) ^ q) P := by simp
  have key := momNorm_Uker_short_sigma_le (P := P) L hL hq (n := m) hκ0 hκ1 hEκ
    (σ := fun _ => true) (k := 0) rfl hs0 (le_refl s) hsv hv1 hκA
    (K := 3) (ζ := 0) (δ := 0) (by norm_num) le_rfl le_rfl
    (G := fun _ω : Ω => witTensor L m ((c0 : ℝ) : ℂ)) (ψ := fun _ω : Ω => (1 : ℝ))
    (fun _ => zero_le_one) hint henv (fun _ => hdec) a
  rw [momNorm_const hq (zero_le_one : (0 : ℝ) ≤ 1)] at key
  simpa using key

end GridWitness

end Satisfiability

end RBM.Gauss

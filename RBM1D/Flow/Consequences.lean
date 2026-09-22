/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Iteration

/-!
# Theorems 2.3 and 2.4 from Lemmas 2.18–2.20 (§2.6, p. 22)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, "Proof of Theorems 2.3 and 2.4" on
p. 22: the local semicircle law (2.3), (2.4) (Theorem 2.3) and quantum diffusion (2.6)–(2.9)
(Theorem 2.4) follow from Lemmas 2.18–2.20 at the time `t` of Lemma 2.8, through the identities
in law (2.39)/(2.65)/(2.66), (2.38), (2.57) and the scale dictionary `η_t ∼ η`, `ℓ_t ∼ ℓ(z)`.

The random layer enters only through hypotheses: `RBM.Bounds` (Lemmas 2.18–2.20), `RBM.Thm221`
(Theorem 2.21, which gives `RBM.Bounds` by `RBM.Bounds_of_Thm221`), `RBM.Transfer` ((2.39),
(2.66)) and `RBM.TransferLoop1` ((2.39) for the 1-loop, defined here).  No axiom.

## Correspondence (p. 22)

Each item: the paper equation, where it comes from, the `≺` form, the paper (`W^τ`) form.

* (2.3) ← (2.64), (2.65): `localLaw_of_bounds`, `localLaw_prob_of_bounds`.
* (2.4) ← (2.60) for `n = 1` and `K_{t,+,a} = m`: `loop1_of_bounds`, `partialTrace_of_bounds`,
  `partialTrace_prob_of_bounds`.
* the tracial law (after (2.9)) ← (2.4) averaged over `a`: `trace_of_bounds`.
* (2.6), (2.7) ← (2.60) for `n = 2`, (2.66), (2.57): `loop2_of_bounds`,
  `quantumDiffusion_pm_of_bounds`, `quantumDiffusion_pp_of_bounds`,
  `quantumDiffusion_pm_prob_of_bounds`, `quantumDiffusion_pp_prob_of_bounds`.
* (2.8), (2.9) ← (2.62), (2.66) in expectation, (2.57): `expect_loop2_of_bounds`,
  `expect_quantumDiffusion_pm_of_bounds`, `expect_quantumDiffusion_pp_of_bounds`,
  `expect_quantumDiffusion_pm_W_of_bounds`, `expect_quantumDiffusion_pp_W_of_bounds`.

The assembled statements are `RBM.localSemicircleLaw_of_Thm221` (**Theorem 2.3**) and
`RBM.quantumDiffusion_of_Thm221` (**Theorem 2.4**), assuming Theorem 2.21.

## (2.71) is used only by (2.8), (2.9) and Theorem 2.5 (T211)

Everything above except the `expect_*` items uses only `RBM.BoundsCore` — (2.68)–(2.70) — so it
survives the paper's remark on p. 25 that Theorem 2.21 holds with (2.71) removed.  The
`RBM.BoundsCore` forms are `RBM.localLaw_of_boundsCore`, `RBM.loop1_of_boundsCore`,
`RBM.partialTrace_of_boundsCore`, `RBM.loop2_of_boundsCore`,
`RBM.quantumDiffusion_pm/pp_of_boundsCore`, `RBM.trace_of_boundsCore`,
`RBM.localLaw_prob_of_boundsCore`, `RBM.partialTrace_prob_of_boundsCore`,
`RBM.quantumDiffusion_pm/pp_prob_of_boundsCore`, `RBM.localSemicircleLaw_of_boundsCore`
(**Theorem 2.3 entire**) and `RBM.quantumDiffusion_pm_pp_of_boundsCore` (**(2.6), (2.7)**); the
`RBM.Bounds` names above are one-line corollaries of them, and the `rfl`-probes at the end of the
file check that no conclusion changed.  `RBM.expect_loop2_of_bounds`,
`RBM.expect_quantumDiffusion_pm/pp_of_bounds` and `RBM.expect_quantumDiffusion_pm/pp_W_of_bounds`
— (2.8), (2.9), and through them Theorem 2.5 — do use `RBM.Bounds.expect` = (2.71) and are
deliberately left on `RBM.Bounds` (T205).

## Ingredients proved here

* `RBM.Band.zScale B N z = W ℓ(z) η` and `RBM.Band.scale_inv_le`:
  `(W ℓ_t η_t)⁻¹ ≤ C_κ (W ℓ(z) η)⁻¹` for `E, t` of Lemma 2.8 (from `RBM.lemma28_scales`).
* `RBM.SpecSeq.bounds`: Lemmas 2.18–2.20 at `t = lemT z` (with `τ/2`), from Theorem 2.21, since
  `1 - t ≥ η/16 ≥ N^{-1+τ}/16` (`RBM.one_sub_lemT_ge`).
* `RBM.Band.lemT_mul_Kval_pm`, `RBM.Band.lemT_mul_Kval_pp` — (2.57) at the spectral parameter of
  Lemma 2.8: `t K_{t,(+,-),(a,b)} = W⁻¹ |m|² Θ_{|m|²}(a,b)` and
  `t K_{t,(+,+),(a,b)} = W⁻¹ m² Θ_{m²}(a,b)`, `m = m_sc(z)`, `Θ_ξ = (1 - ξ S^{(B)})⁻¹`.
* `RBM.gloop_one_eq`, `RBM.gloop_pm_eq`, `RBM.gloop_pp_eq` — the loops as the traces of the paper.
* `RBM.StochDom.average` (averaging over a finite index), `RBM.Band.prob_le_of_stochDom` and
  `RBM.Band.le_W_rpow_of_unifDetDom` (`≺` in the `W^τ` form of the theorems, using `W ≥ N^{1/2+c}`).

## Deviations from the paper

* **Fixed energy slice.**  `RBM.Bounds X E s` (T54) has a fixed real `E`; Lemmas 2.18–2.20 are
  therefore available only for `E` independent of `N`.  So Theorems 2.3/2.4 are proved for
  spectral parameters `z_N` whose Lemma 2.8 energy `lemE z_N = E` does not depend on `N`
  (`RBM.SpecSeq`), not uniformly over the whole domain `|Re z| ≤ 2 - κ`,
  `N^{-1+τ} ≤ Im z ≤ 1`.  (Every fixed `z` is on such a slice; within a slice, "for every
  sequence `z_N`" gives "uniformly in `z`" by the usual subsequence argument.)  Uniformity in
  `E` would need `RBM.Bounds` / `RBM.Thm221` with an `N`-dependent energy.
* **(2.4) needs `RBM.TransferLoop1`** ((2.39) for `Tr G(z) E_a`), an extra hypothesis:
  `RBM.Transfer.green` only transfers entrywise bounds, which cannot give the averaged (2.4).
* The spectral parameter is a sequence `z : ℕ → ℂ` (the transfers of `RBM.Transfer` are stated
  for sequences); the max over `x, y` (resp. `a`, `(a, b)`) is the uniformity in the parameter.
* "`P(bound holds) ≥ 1 - N^{-D}`" is written "`P(bound fails) ≤ N^{-D}`" (`P` is a probability
  measure).  `N` is the index of `RBM.Band` (`W L ≤ N ≤ 2 W L`); the tracial law uses the
  matrix size `L W` for the paper's `N`.
* `G† = G(z)ᴴ`; in loop form it is `G(z̄)` (`RBM.Gsig`), equal for Hermitian `H`.
* The `W^{τ'}` forms are derived from `≺` (with `N^τ`) using `W ≥ N^{1/2+c}` (2.2).
-/

namespace RBM

open MeasureTheory Filter

/-! ### The scale `W ℓ(z) η` of Theorems 2.3 and 2.4 -/

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- The scale `W ℓ(z) η`, `η = Im z`, `ℓ(z) = min(η^{-1/2}, L) + 1` (2.1), of (2.3)–(2.9). -/
noncomputable def zScale (N : ℕ) (z : ℂ) : ℝ := (B.W N : ℝ) * ellZ (B.L N) z * z.im

theorem one_le_ellZ (L : ℕ) (z : ℂ) : 1 ≤ ellZ L z := by
  have : 0 ≤ min (1 / Real.sqrt z.im) (L : ℝ) :=
    le_min (by have := Real.sqrt_nonneg z.im; positivity) (Nat.cast_nonneg L)
  rw [ellZ, ellOf]
  linarith

theorem zScale_pos (N : ℕ) {z : ℂ} (hz : 0 < z.im) : 0 < B.zScale N z := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have := one_le_ellZ (B.L N) z
  unfold zScale
  positivity

end Band

/-- The constant of `(W ℓ_t η_t)⁻¹ ≤ C_κ (W ℓ(z) η)⁻¹`, `C_κ = 128 √(2/√(2κ))`. -/
noncomputable def cScale (κ : ℝ) : ℝ := 128 * Real.sqrt (2 / Real.sqrt (2 * κ))

theorem cScale_pos {κ : ℝ} (hκ : 0 < κ) : 0 < cScale κ := by
  have : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  have : 0 < Real.sqrt (2 / Real.sqrt (2 * κ)) := Real.sqrt_pos.2 (by positivity)
  unfold cScale
  positivity

/-- `1 - t ≥ Im z / 16` for the time `t` of Lemma 2.8. -/
theorem one_sub_lemT_ge {κ : ℝ} (hκ0 : 0 < κ) {z : ℂ} (hz0 : 0 < z.im) (hz1 : z.im ≤ 1)
    (hκ : |z.re| ≤ 2 - κ) : (1 / 16 : ℝ) * z.im ≤ 1 - lemT z := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  obtain ⟨-, h2, h3, -⟩ := lemma28_scales hκ0 hκ2 hz0 hz1 hκ (le_refl 1)
  linarith

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- **The scale dictionary for Theorems 2.3/2.4**: with `E, t` from Lemma 2.8,
`W ℓ(z) η ≤ C_κ W ℓ_t η_t`, i.e. `(W ℓ_t η_t)⁻¹ ≤ C_κ (W ℓ(z) η)⁻¹` (p. 22:
`η_t ∼ η`, `ℓ_t ∼ ℓ(z)`). -/
theorem scale_inv_le {κ : ℝ} (hκ0 : 0 < κ) {z : ℂ} (hz0 : 0 < z.im) (hz1 : z.im ≤ 1)
    (hκ : |z.re| ≤ 2 - κ) (N : ℕ) :
    (B.scale (lemE z) N (lemT z))⁻¹ ≤ cScale κ * (B.zScale N z)⁻¹ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  obtain ⟨-, -, h3, -, -, -, -, -, -, h10⟩ :=
    lemma28_scales hκ0 hκ2 hz0 hz1 hκ (B.one_le_L N)
  have hE : |lemE z| < 2 := abs_lemE_lt_two hz0
  have ht0 : 0 < lemT z := lemT_pos hz0
  have ht1 : lemT z < 1 := lemT_lt_one hz0
  have hs : 0 < B.scale (lemE z) N (lemT z) := B.scale_pos hE N ht0 ht1
  have hzs : 0 < B.zScale N z := B.zScale_pos N hz0
  have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have hle : B.zScale N z ≤ cScale κ * B.scale (lemE z) N (lemT z) := by
    have hη : (zt (lemE z) (lemT z)).im = etaT (lemE z) (lemT z) := (etaT_eq_zt_im _ _).symm
    rw [hη] at h3
    have hℓ0 : 0 ≤ ellZ (B.L N) z := (zero_le_one).trans (one_le_ellZ _ _)
    have hz' : z.im ≤ 16 * etaT (lemE z) (lemT z) := by linarith
    unfold zScale scale cScale ell
    calc (B.W N : ℝ) * ellZ (B.L N) z * z.im
        ≤ (B.W N : ℝ) * (8 * Real.sqrt (2 / Real.sqrt (2 * κ)) * ellHat (B.L N) (lemT z : ℂ)) *
          (16 * etaT (lemE z) (lemT z)) := by
          gcongr
          exact mul_nonneg hW (hℓ0.trans h10)
      _ = _ := by ring
  calc (B.scale (lemE z) N (lemT z))⁻¹
      = (B.scale (lemE z) N (lemT z))⁻¹ * B.zScale N z * (B.zScale N z)⁻¹ := by
        field_simp
    _ ≤ (B.scale (lemE z) N (lemT z))⁻¹ * (cScale κ * B.scale (lemE z) N (lemT z)) *
          (B.zScale N z)⁻¹ := by gcongr
    _ = cScale κ * (B.zScale N z)⁻¹ := by field_simp

end Band

/-! ### The spectral parameters of Theorems 2.3/2.4 -/

/-- **The spectral parameters of Theorems 2.3 and 2.4**, one for each `N`:
`z_N = E_N + iη_N` with `|E_N| ≤ 2 - κ`, `N^{-1+τ} ≤ η_N ≤ 1` (the first for large `N`), and
**on a fixed energy slice of Lemma 2.8**: the energy `E = lemE z_N` of Lemma 2.8 does not depend
on `N`.  The slice condition is forced by the interface `RBM.Bounds X E s` of
`Flow/Hypotheses.lean`, in which `E` is a fixed real number (see the module docstring). -/
structure SpecSeq (κ τ E : ℝ) (z : ℕ → ℂ) : Prop where
  im_pos : ∀ N, 0 < (z N).im
  im_le_one : ∀ N, (z N).im ≤ 1
  abs_re_le : ∀ N, |(z N).re| ≤ 2 - κ
  /-- `η ≥ N^{-1+τ}` (for large `N`). -/
  im_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im
  /-- The energy of Lemma 2.8 is `E` for every `N`. -/
  lemE_eq : ∀ N, lemE (z N) = E

namespace SpecSeq

variable {κ τ E : ℝ} {z : ℕ → ℂ} (hz : SpecSeq κ τ E z)
include hz

/-- `|E| ≤ 2 - κ` (Lemma 2.8: `|E| ≤ |Re z|`). -/
theorem abs_E_le (hκ : 0 < κ) : |E| ≤ 2 - κ := by
  rw [← hz.lemE_eq 0]
  exact (lemma28_quant hκ (hz.im_pos 0) (hz.im_le_one 0) (hz.abs_re_le 0)).1

theorem lemT_nonneg (N : ℕ) : 0 ≤ lemT (z N) := (lemT_pos (hz.im_pos N)).le

theorem lemT_lt_one' (N : ℕ) : lemT (z N) < 1 := lemT_lt_one (hz.im_pos N)

/-- The time `t = lemT z` of Lemma 2.8 satisfies `1 - t ≥ N^{-1+τ/2}` for large `N`
(`1 - t ≥ Im z_t ≥ η/16`, p. 22), so Lemmas 2.18–2.20 apply at `t` with `τ/2` in place of `τ`. -/
theorem eventually_rpow_le_one_sub (hκ : 0 < κ) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ / 2) ≤ 1 - lemT (z N) := by
  filter_upwards [hz.im_ge, eventually_le_rpow 16 (half_pos hτ), eventually_ge_atTop 1]
    with N h1 h16 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have h := one_sub_lemT_ge hκ (hz.im_pos N) (hz.im_le_one N) (hz.abs_re_le N)
  have hsplit : (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (-1 + τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hp : 0 ≤ (N : ℝ) ^ (-1 + τ / 2) := Real.rpow_nonneg hN0.le _
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Lemmas 2.18–2.20 at the time `t = lemT z` of Lemma 2.8**, from Theorem 2.21. -/
theorem bounds (X : Sample B) (hκ : 0 < κ) (hT : Thm221 X κ) (hτ : 0 < τ) :
    Bounds X E (fun N => lemT (z N)) :=
  Bounds_of_Thm221 X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

theorem scale_inv_le (hκ : 0 < κ) (N : ℕ) :
    (B.scale E N (lemT (z N)))⁻¹ ≤ cScale κ * (B.zScale N (z N))⁻¹ := by
  rw [← hz.lemE_eq N]
  exact B.scale_inv_le hκ (hz.im_pos N) (hz.im_le_one N) (hz.abs_re_le N) N

theorem scale_inv_nonneg (N : ℕ) : 0 ≤ (B.scale E N (lemT (z N)))⁻¹ :=
  inv_nonneg.2 (B.scale_nonneg E N (hz.lemT_lt_one' N).le)

theorem zScale_inv_nonneg (N : ℕ) : 0 ≤ (B.zScale N (z N))⁻¹ :=
  inv_nonneg.2 (B.zScale_pos N (hz.im_pos N)).le

/-- `(W ℓ_t η_t)^{-n} ≺ (W ℓ(z) η)^{-n}` (deterministic). -/
theorem unifDetDom_pow (hκ : 0 < κ) {U : ℕ → Type*} (n : ℕ) :
    UnifDetDom (fun N (_ : U N) => (B.scale E N (lemT (z N)))⁻¹ ^ n)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ n) :=
  UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hz.zScale_inv_nonneg N) n)
    (cScale κ ^ n) (Eventually.of_forall fun N _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hz.scale_inv_nonneg N) (hz.scale_inv_le hκ N) n)

/-- `(W ℓ_t η_t)^{-p} ≺ (W ℓ(z) η)^{-p}` for real `p ≥ 0` (deterministic). -/
theorem unifDetDom_rpow (hκ : 0 < κ) {U : ℕ → Type*} {p : ℝ} (hp : 0 ≤ p) :
    UnifDetDom (fun N (_ : U N) => (B.scale E N (lemT (z N)))⁻¹ ^ p)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ p) :=
  UnifDetDom.of_eventually_le_const_mul
    (fun N _ => Real.rpow_nonneg (hz.zScale_inv_nonneg N) p)
    (cScale κ ^ p) (Eventually.of_forall fun N _ => by
      rw [← Real.mul_rpow (cScale_pos hκ).le (hz.zScale_inv_nonneg N)]
      exact Real.rpow_le_rpow (hz.scale_inv_nonneg N) (hz.scale_inv_le hκ N) hp)

end SpecSeq

/-! ### Two generic facts about `≺` -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Averaging**: if `|Y_v - c| ≺ ζ` uniformly in `v` (finite, nonempty), then
`|(#V)⁻¹ ∑_v Y_v - c| ≺ ζ`. -/
theorem StochDom.average {P : Measure Ω} {V : ℕ → Type*} [∀ N, Fintype (V N)]
    [∀ N, Nonempty (V N)] {Y : ∀ N, V N → Ω → ℂ} {c : ℕ → ℂ} {ζ : ℕ → ℝ}
    (h : StochDom P (fun N v ω => ‖Y N v ω - c N‖) (fun N _ _ => ζ N)) :
    StochDom P (fun N (_ : Unit) ω => ‖(Fintype.card (V N) : ℂ)⁻¹ * ∑ v, Y N v ω - c N‖)
      (fun N _ _ => ζ N) := by
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  intro ω hω
  obtain ⟨_, hu⟩ := hω
  by_contra hno
  simp only [Set.mem_union, or_self, badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  refine absurd hu (not_lt.2 ?_)
  have hcard : (0 : ℝ) < Fintype.card (V N) := by exact_mod_cast Fintype.card_pos
  have hcardC : (Fintype.card (V N) : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
  have heq : (Fintype.card (V N) : ℂ)⁻¹ * ∑ v, Y N v ω - c N =
      (Fintype.card (V N) : ℂ)⁻¹ * ∑ v, (Y N v ω - c N) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  show ‖(Fintype.card (V N) : ℂ)⁻¹ * ∑ v, Y N v ω - c N‖ ≤ (N : ℝ) ^ τ * ζ N
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card (V N) : ℝ)⁻¹ * ‖∑ v, (Y N v ω - c N)‖
      ≤ (Fintype.card (V N) : ℝ)⁻¹ * ∑ v, ‖Y N v ω - c N‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card (V N) : ℝ)⁻¹ * ∑ _v : V N, (N : ℝ) ^ τ * ζ N := by
        gcongr with v; exact hno v
    _ = (N : ℝ) ^ τ * ζ N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- `N^{τ/2} ≤ W^τ` for large `N` (from `W ≥ N^{1/2+c}`). -/
theorem Band.eventually_rpow_half_le_W (B : Band Ω) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (τ / 2) ≤ (B.W N : ℝ) ^ τ := by
  filter_upwards [B.bandwidth, eventually_ge_atTop 1] with N hbw hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  calc (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ ((1 / 2 + B.c) * τ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [B.c_pos])
    _ = ((N : ℝ) ^ (1 / 2 + B.c)) ^ τ := Real.rpow_mul (by linarith) _ _
    _ ≤ (B.W N : ℝ) ^ τ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hbw hτ.le

/-- **`≺` in the `W^τ` form of Theorems 2.3 and 2.4**: for the band model (`W ≥ N^{1/2+c}`),
`ξ ≺ ζ` gives `P(∃ u, ξ(u) > W^τ ζ(u)) ≤ N^{-D}` for large `N`, for every `τ, D > 0`. -/
theorem Band.prob_le_of_stochDom (B : Band Ω) {U : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom B.P ξ ζ) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ u, (B.W N : ℝ) ^ τ * ζ N u ω < ξ N u ω} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  filter_upwards [h (τ / 2) (half_pos hτ) D hD, B.eventually_rpow_half_le_W hτ] with N hP hNW
  refine (measure_mono fun ω hω => ?_).trans hP
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hNW (hζ N u ω)) hu⟩

/-- **Deterministic `≺` in the `W^τ` form of (2.8), (2.9)**: `f ≺ g` gives `f ≤ W^τ g` for
large `N`, for every `τ > 0`. -/
theorem Band.le_W_rpow_of_unifDetDom (B : Band Ω) {U : ℕ → Type*} {f g : ∀ N, U N → ℝ}
    (hg : ∀ N u, 0 ≤ g N u) (h : UnifDetDom f g) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ (B.W N : ℝ) ^ τ * g N u := by
  filter_upwards [h (τ / 2) (half_pos hτ), B.eventually_rpow_half_le_W hτ] with N hN hNW u
  exact (hN u).trans (mul_le_mul_of_nonneg_right hNW (hg N u))

end Generic

/-! ### The deterministic identities -/

section Identities

open scoped Matrix

variable {L W : ℕ} [NeZero L]

/-- The 1-loop is the partial trace: `L_{+,a} = Tr G E_a = W⁻¹ ∑_{x ∈ I_a} G_{xx}`. -/
theorem gloop_one_eq [NeZero W] (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (a : ZMod L) :
    gloop L W H z ⟨[true], [a]⟩ = (W : ℂ)⁻¹ * ∑ x : Fin W, green H z (a, x) (a, x) := by
  rw [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true]
  simp only [Matrix.trace, Matrix.diag, Eblk, Matrix.mul_diagonal]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp [Finset.mul_sum, mul_comm]
  · intro b _ hb; simp [hb]
  · simp

/-- The 2-loop `L_{(+,-),(a,b)}` is `Tr G E_a G† E_b` for Hermitian `H`. -/
theorem gloop_pm_eq [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (a b : ZMod L) :
    gloop L W H z ⟨[true, false], [a, b]⟩ =
      (green H z * Eblk L W a * (green H z)ᴴ * Eblk L W b).trace := by
  have h := Gsig_conjTranspose hH z true
  simp only [Bool.not_true, Gsig_true] at h
  rw [gloop_two, ← h, Gsig_true, Matrix.mul_assoc (green H z * Eblk L W a)]

/-- The 2-loop `L_{(+,+),(a,b)}` is `Tr G E_a G E_b`. -/
theorem gloop_pp_eq [NeZero W] (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (a b : ZMod L) :
    gloop L W H z ⟨[true, true], [a, b]⟩ =
      (green H z * Eblk L W a * green H z * Eblk L W b).trace := by
  rw [gloop_two, Gsig_true, Matrix.mul_assoc (green H z * Eblk L W a)]

/-- The loop index of `((s₁, s₂), (a, b))` is `⟨[s₁, s₂], [a, b]⟩`. -/
theorem LoopData.idx_two {L : ℕ} (s₁ s₂ : Bool) (a b : ZMod L) :
    LoopData.idx ((![s₁, s₂], ![a, b]) : LoopData L 2) = ⟨[s₁, s₂], [a, b]⟩ := by
  simp [LoopData.idx, List.ofFn_succ]

end Identities

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- **(2.57) at the spectral parameter of Lemma 2.8, `σ = (+,-)`** (p. 22):
`t K_{t,(+,-),(a,b)} = W⁻¹ |m_sc(z)|² ((1 - |m_sc(z)|² S^{(B)})⁻¹)_{ab}`. -/
theorem lemT_mul_Kval_pm (N : ℕ) {z : ℂ} (hz : 0 < z.im) (a b : ZMod (B.L N)) :
    (lemT z : ℂ) * B.Kval (lemE z) N (lemT z) ⟨[true, false], [a, b]⟩ =
      (B.W N : ℂ)⁻¹ * ((‖msc z‖ ^ 2 : ℝ) : ℂ) * Theta (B.L N) ((‖msc z‖ ^ 2 : ℝ) : ℂ) a b := by
  rw [Kval, Kgen_two, kTwo, mSigma_mul_of_ne (abs_lemE_lt_two hz).le (by decide), mul_one,
    mul_one, lemT]
  ring

/-- **(2.57) at the spectral parameter of Lemma 2.8, `σ = (+,+)`** (p. 22):
`t K_{t,(+,+),(a,b)} = W⁻¹ m_sc(z)² ((1 - m_sc(z)² S^{(B)})⁻¹)_{ab}`. -/
theorem lemT_mul_Kval_pp (N : ℕ) {z : ℂ} (hz : 0 < z.im) (a b : ZMod (B.L N)) :
    (lemT z : ℂ) * B.Kval (lemE z) N (lemT z) ⟨[true, true], [a, b]⟩ =
      (B.W N : ℂ)⁻¹ * msc z ^ 2 * Theta (B.L N) (msc z ^ 2) a b := by
  have h : msc z ^ 2 = (lemT z : ℂ) * (mE (lemE z) * mE (lemE z)) := by
    rw [msc_eq_sqrt_mul_mE hz, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (lemT_pos hz).le]
    ring
  rw [Kval, Kgen_two, kTwo, h]
  simp only [mSigma, ite_true]
  ring

end Band

/-! ### (2.39) for the 1-loop -/

/-- **(2.39) for the 1-`G` loop**: `Tr G(z) E_a ∼ t^{1/2} L_{t,+,a}` (with `E`, `t` from
Lemma 2.8), as a transfer of `≺`-bounds with deterministic centering, in the form of the fields of
`RBM.Transfer`.

This is what the paper uses on p. 22 for (2.4) ("(2.4) follows from (2.60) for the 1-`G`-loop").
It is a consequence of the equality in law `G(z) ∼ t^{1/2} G_t^{(E)}` of the whole matrices
(2.39), but `RBM.Transfer.green` only records the entrywise consequence, which cannot give the
averaged bound (2.4) (the averaging gains a factor `(W ℓ η)^{-1/2}` over the entrywise (2.3)).
So it is recorded here as a separate hypothesis, never an axiom. -/
structure TransferLoop1 {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B}
    (T : Transfer X) : Prop where
  loop1 : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) →
    ∀ (c : ∀ N, ZMod (B.L N) → ℂ) (ζ : ∀ N, ZMod (B.L N) → ℝ),
    StochDom B.P
      (fun N a ω => ‖(Real.sqrt (lemT (z N)) : ℂ) *
        X.Lval (lemE (z N)) N (lemT (z N)) ω ⟨[true], [a]⟩ - c N a‖)
      (fun N a _ => ζ N a) →
    StochDom B.P
      (fun N a ω => ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - c N a‖)
      (fun N a _ => ζ N a)

/-! ### Theorems 2.3 and 2.4 -/

section Main

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ E : ℝ} {z : ℕ → ℂ}

/-! #### The `RBM.BoundsCore` versions (T211)

Every statement of this section except (2.8)/(2.9) and Theorem 2.5 uses only `RBM.Bounds.LmK`
and `RBM.Bounds.localLaw`, i.e. only the `RBM.BoundsCore` part of `RBM.Bounds`: (2.71) is not
needed (p. 25, after Step 6).  The theorems below are those statements with `RBM.Bounds`
weakened to `RBM.BoundsCore`; the `RBM.Bounds` versions are one-line corollaries, and a
`rfl`-probe at the end of the file checks that not a single conclusion changed (T107's
technique).  Four of the seven are themselves one-line corollaries of the shared scripts of the
next subsection (T221); the other three — (2.6)/(2.7) and the 2-loop — are needed at a fixed
energy only, so they carry their script here.

T204 had put verbatim copies of these seven in `Flow/Thm221NoEL.lean`, which is **downstream** of
this file (`Thm221NoEL → Thm221Bare → ⋯ → Consequences`), so T211 had to park them in a
temporary namespace `RBM.Core` here.  **T221** deleted the downstream copies and dropped the
prefix: each of the seven scripts now exists exactly once, here. -/

/-! #### The shared scripts (T221)

The four theorems of this subsection are the only place in the repository where (2.64)/(2.65) is
turned into (2.3)/(2.4).  They take the *fields* they use rather than a bundle, and the energy as
a sequence `EN : ℕ → ℝ`, so that the fixed-energy statements of this file (`RBM.SpecSeq`,
`RBM.BoundsCore`) and the `N`-dependent ones of `Flow/EnergyUniform.lean` (`RBM.SpecSeqN`,
`RBM.BoundsCoreN`) are **both** one-line corollaries: neither bundle is upstream of the other, so
without this factoring the same script has to be written twice.  T211 found three copies of it
(here, `Flow/Thm221NoEL.lean`, `Flow/EnergyUniform.lean`); this is the single one. -/

/-- **Theorem 2.3, (2.3)**, from (2.64) and (2.65), in field form: the script shared by
`RBM.localLaw_of_boundsCore` and `RBM.localLaw_of_boundsCoreN`. -/
theorem localLaw_of_fields (T : Transfer X) (EN : ℕ → ℝ) (him_pos : ∀ N, 0 < (z N).im)
    (hlemE : ∀ N, lemE (z N) = EN N)
    (hudd : UnifDetDom (fun N (_ : B.Idx N × B.Idx N) =>
        (B.scale (EN N) N (lemT (z N)))⁻¹ ^ ((1 : ℝ) / 2))
      (fun N _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)))
    (hll : StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω => X.llErr (EN N) N (lemT (z N)) ω ij)
      (fun N _ _ => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ ((1 : ℝ) / 2))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) := by
  have h1 := hll.trans (StochDom.of_unifDetDom hudd)
  refine T.green_sub_msc z him_pos _ (StochDom.of_le_left (fun N ij ω => ?_) h1)
  rw [hlemE N, Matrix.smul_apply, norm_smul, Sample.llErr]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (lemT_lt_one (him_pos N)).le

/-- **Theorem 2.3, (2.4)** in loop form, from (2.60) for `n = 1`, in field form: the script
shared by `RBM.loop1_of_boundsCore` and `RBM.loop1_of_boundsCoreN`. -/
theorem loop1_of_fields (T : Transfer X) (T1 : TransferLoop1 T) (EN : ℕ → ℝ)
    (him_pos : ∀ N, 0 < (z N).im) (hlemE : ∀ N, lemE (z N) = EN N)
    (hudd : UnifDetDom (fun N (_ : LoopData (B.L N) 1) => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ 1)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 1))
    (hLmK : StochDom B.P
      (fun N (u : LoopData (B.L N) 1) ω => X.lkErr (EN N) N (lemT (z N)) ω u.idx)
      (fun N _ _ => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ 1)) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  have h1 := (hLmK.trans (StochDom.of_unifDetDom hudd)).precomp_param
    (fun N (a : ZMod (B.L N)) => ((fun _ => true, fun _ => a) : LoopData (B.L N) 1))
  have h2 := T1.loop1 z him_pos (fun N _ => msc (z N)) (fun N _ => (B.zScale N (z N))⁻¹ ^ 1)
    (StochDom.of_le_left (fun N a ω => ?_) h1)
  · simpa only [pow_one] using h2
  have hidx : LoopData.idx ((fun _ => true, fun _ => a) : LoopData (B.L N) 1) =
      ⟨[true], [a]⟩ := by simp [LoopData.idx]
  rw [hidx, Sample.lkErr, Band.Kval, Kgen_one, msc_eq_sqrt_mul_mE (him_pos N), hlemE N,
    ← mul_sub, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (lemT_lt_one (him_pos N)).le

/-- **Theorem 2.3, (2.4)** (partial tracial local law), in field form. -/
theorem partialTrace_of_fields (T : Transfer X) (T1 : TransferLoop1 T) (EN : ℕ → ℝ)
    (him_pos : ∀ N, 0 < (z N).im) (hlemE : ∀ N, lemE (z N) = EN N)
    (hudd : UnifDetDom (fun N (_ : LoopData (B.L N) 1) => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ 1)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 1))
    (hLmK : StochDom B.P
      (fun N (u : LoopData (B.L N) 1) ω => X.lkErr (EN N) N (lemT (z N)) ω u.idx)
      (fun N _ _ => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ 1)) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  refine StochDom.of_le_left (fun N a ω => le_of_eq ?_)
    (loop1_of_fields T T1 EN him_pos hlemE hudd hLmK)
  rw [gloop_one_eq]

/-- **Theorem 2.3, the tracial local law** (stated after (2.9)), in field form. -/
theorem trace_of_fields (T : Transfer X) (T1 : TransferLoop1 T) (EN : ℕ → ℝ)
    (him_pos : ∀ N, 0 < (z N).im) (hlemE : ∀ N, lemE (z N) = EN N)
    (hudd : UnifDetDom (fun N (_ : LoopData (B.L N) 1) => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ 1)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 1))
    (hLmK : StochDom B.P
      (fun N (u : LoopData (B.L N) 1) ω => X.lkErr (EN N) N (lemT (z N)) ω u.idx)
      (fun N _ _ => (B.scale (EN N) N (lemT (z N)))⁻¹ ^ 1)) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  have h := StochDom.average (V := fun N => ZMod (B.L N)) (c := fun N => msc (z N))
    (ζ := fun N => (B.zScale N (z N))⁻¹)
    (partialTrace_of_fields T T1 EN him_pos hlemE hudd hLmK)
  refine StochDom.of_le_left (fun N _ ω => le_of_eq ?_) h
  have hW : (B.W N : ℂ) ≠ 0 := by exact_mod_cast (B.W_pos N).ne'
  have hL : (B.L N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (B.L N))
  simp only [ZMod.card, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, ← Finset.mul_sum]
  push_cast
  field_simp

/-- **Theorem 2.3, (2.3)** (local semicircle law), from (2.64) and (2.65), on `RBM.BoundsCore`. -/
theorem localLaw_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) :=
  localLaw_of_fields T (fun _ => E) hz.im_pos hz.lemE_eq
    (hz.unifDetDom_rpow hκ (by norm_num : (0 : ℝ) ≤ 1 / 2)) hB.localLaw

/-- **Theorem 2.3, (2.4)** in loop form, from (2.60) for `n = 1`, on `RBM.BoundsCore`. -/
theorem loop1_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  loop1_of_fields T T1 (fun _ => E) hz.im_pos hz.lemE_eq (hz.unifDetDom_pow hκ 1)
    (hB.LmK 1 le_rfl)

/-- **Theorem 2.3, (2.4)** (partial tracial local law), on `RBM.BoundsCore`. -/
theorem partialTrace_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  partialTrace_of_fields T T1 (fun _ => E) hz.im_pos hz.lemE_eq (hz.unifDetDom_pow hκ 1)
    (hB.LmK 1 le_rfl)

/-- **Theorem 2.4, (2.6)/(2.7)** in loop form, from (2.60) for `n = 2` and (2.66),
on `RBM.BoundsCore`. -/
theorem loop2_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) (σ₂ : Bool) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ -
          (lemT (z N) : ℂ) * B.Kval E N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  have h1 := ((hB.LmK 2 (by norm_num)).trans
    (StochDom.of_unifDetDom (hz.unifDetDom_pow hκ 2))).precomp_param
    (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
      ((![true, σ₂], ![ab.1, ab.2]) : LoopData (B.L N) 2))
  refine T.loop2 z hz.im_pos σ₂
    (fun N ab => (lemT (z N) : ℂ) * B.Kval E N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩) _
    (StochDom.of_le_left (fun N ab ω => ?_) h1)
  rw [LoopData.idx_two, hz.lemE_eq N, Sample.lkErr, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hz.lemT_nonneg N)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz.lemT_lt_one' N).le

/-- **Theorem 2.4, (2.6)**, on `RBM.BoundsCore`. -/
theorem quantumDiffusion_pm_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  refine StochDom.of_le_left (fun N ab ω => le_of_eq ?_) (loop2_of_boundsCore T hκ hz hB false)
  rw [gloop_pm_eq (T.hermitian N ω), ← hz.lemE_eq N, B.lemT_mul_Kval_pm N (hz.im_pos N)]

/-- **Theorem 2.4, (2.7)**, on `RBM.BoundsCore`. -/
theorem quantumDiffusion_pp_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  refine StochDom.of_le_left (fun N ab ω => le_of_eq ?_) (loop2_of_boundsCore T hκ hz hB true)
  rw [gloop_pp_eq, ← hz.lemE_eq N, B.lemT_mul_Kval_pp N (hz.im_pos N)]

/-- **Theorem 2.3, the tracial local law** (stated after (2.9)), on `RBM.BoundsCore`. -/
theorem trace_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  trace_of_fields T T1 (fun _ => E) hz.im_pos hz.lemE_eq (hz.unifDetDom_pow hκ 1)
    (hB.LmK 1 le_rfl)

/-- **Theorem 2.3, (2.3)** (local semicircle law), from (2.64) and (2.65):
`max_{x,y} |(G(z) - m(z))_{xy}| ≺ (W ℓ(z) η)^{-1/2}`. -/
theorem localLaw_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) :=
  localLaw_of_boundsCore T hκ hz hB.toBoundsCore

/-- **Theorem 2.3, (2.4)** in loop form, from (2.60) for `n = 1` and `K_{t,+,a} = m^{(E)}`:
`max_a |L_{+,a}(z) - m(z)| ≺ (W ℓ(z) η)^{-1}` with `L_{+,a}(z) = Tr G(z) E_a`. -/
theorem loop1_of_bounds (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  loop1_of_boundsCore T T1 hκ hz hB.toBoundsCore

/-- **Theorem 2.3, (2.4)** (partial tracial local law):
`max_a |W⁻¹ ∑_{x ∈ I_a} G_{xx}(z) - m(z)| ≺ (W ℓ(z) η)^{-1}`. -/
theorem partialTrace_of_bounds (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  partialTrace_of_boundsCore T T1 hκ hz hB.toBoundsCore

/-- **Theorem 2.4, (2.6)/(2.7)** in loop form, from (2.60) for `n = 2` and (2.66):
`max_{a,b} |L_{(+,σ₂),(a,b)}(z) - t K_{t,(+,σ₂),(a,b)}| ≺ (W ℓ(z) η)^{-2}`. -/
theorem loop2_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) (σ₂ : Bool) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ -
          (lemT (z N) : ℂ) * B.Kval E N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) :=
  loop2_of_boundsCore T hκ hz hB.toBoundsCore σ₂

/-- **Theorem 2.4, (2.6)**: `max_{a,b} |Tr G E_a G† E_b - W⁻¹ (|m|²/(1 - |m|² S^{(B)}))_{ab}|
≺ (W ℓ(z) η)^{-2}`, `G = G(z)`, `m = m(z)`. -/
theorem quantumDiffusion_pm_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) :=
  quantumDiffusion_pm_of_boundsCore T hκ hz hB.toBoundsCore

/-- **Theorem 2.4, (2.7)**: `max_{a,b} |Tr G E_a G E_b - W⁻¹ (m²/(1 - m² S^{(B)}))_{ab}|
≺ (W ℓ(z) η)^{-2}`, `G = G(z)`, `m = m(z)`. -/
theorem quantumDiffusion_pp_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) :=
  quantumDiffusion_pp_of_boundsCore T hκ hz hB.toBoundsCore

/-- **Theorem 2.4, (2.8)/(2.9)** in loop form, from (2.62) and (2.66) in expectation:
`max_{a,b} |E L_{(+,σ₂),(a,b)}(z) - t K_{t,(+,σ₂),(a,b)}| ≺ (W ℓ(z) η)^{-3}` (deterministic). -/
theorem expect_loop2_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) (σ₂ : Bool) :
    UnifDetDom (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
        ‖(∫ ω, gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ ∂B.P) -
          (lemT (z N) : ℂ) * B.Kval E N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩‖)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 3) := by
  have h1 := (hB.expect.precomp_param
    (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
      ((![true, σ₂], ![ab.1, ab.2]) : LoopData (B.L N) 2))).trans (hz.unifDetDom_pow hκ 3)
  refine UnifDetDom.mono_left (Eventually.of_forall fun N ab => ?_) h1
  rw [T.loop2_expect z hz.im_pos σ₂ N ab.1 ab.2, LoopData.idx_two, hz.lemE_eq N, Sample.expErr,
    ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hz.lemT_nonneg N)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz.lemT_lt_one' N).le

/-- **Theorem 2.4, (2.8)**: `max_{a,b} |E Tr G E_a G† E_b - W⁻¹ (|m|²/(1 - |m|² S^{(B)}))_{ab}|
≺ (W ℓ(z) η)^{-3}` (deterministic `≺`, Definition 2.1 (ii)). -/
theorem expect_quantumDiffusion_pm_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    UnifDetDom (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
        ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 3) := by
  refine UnifDetDom.mono_left (Eventually.of_forall fun N ab => le_of_eq ?_)
    (expect_loop2_of_bounds T hκ hz hB false)
  have hfun : (fun ω => (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
      (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace) =
      fun ω => gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, false], [ab.1, ab.2]⟩ :=
    funext fun ω => (gloop_pm_eq (T.hermitian N ω) _ _ _).symm
  rw [hfun, ← hz.lemE_eq N, B.lemT_mul_Kval_pm N (hz.im_pos N)]

/-- **Theorem 2.4, (2.9)**: `max_{a,b} |E Tr G E_a G E_b - W⁻¹ (m²/(1 - m² S^{(B)}))_{ab}|
≺ (W ℓ(z) η)^{-3}` (deterministic `≺`, Definition 2.1 (ii)). -/
theorem expect_quantumDiffusion_pp_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    UnifDetDom (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
        ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 3) := by
  refine UnifDetDom.mono_left (Eventually.of_forall fun N ab => le_of_eq ?_)
    (expect_loop2_of_bounds T hκ hz hB true)
  have hfun : (fun ω => (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
      green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace) =
      fun ω => gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, true], [ab.1, ab.2]⟩ :=
    funext fun ω => (gloop_pp_eq _ _ _ _).symm
  rw [hfun, ← hz.lemE_eq N, B.lemT_mul_Kval_pp N (hz.im_pos N)]

/-- **Theorem 2.3, the tracial local law** (stated after (2.9); it follows from (2.4) by
averaging over `a`): `|N⁻¹ Tr G(z) - m(z)| ≺ (W ℓ(z) η)^{-1}`, with `N = L W` the size of the
matrix. -/
theorem trace_of_bounds (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  trace_of_boundsCore T T1 hκ hz hB.toBoundsCore

/-! #### The `W^τ` form of Theorems 2.3 and 2.4 -/

/-- **Theorem 2.3, (2.3), paper form**, on `RBM.BoundsCore`: for `τ', D > 0` and large `N`,
`P(max_{x,y} |(G - m)_{xy}| > W^{τ'} (W ℓ η)^{-1/2}) ≤ N^{-D}`. -/
theorem localLaw_prob_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ij : B.Idx N × B.Idx N,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  B.prob_le_of_stochDom (fun N _ _ => Real.rpow_nonneg (hz.zScale_inv_nonneg N) _)
    (localLaw_of_boundsCore T hκ hz hB) hτ' hD

/-- **Theorem 2.3, (2.3), paper form**: for `τ', D > 0` and large `N`,
`P(max_{x,y} |(G - m)_{xy}| > W^{τ'} (W ℓ η)^{-1/2}) ≤ N^{-D}`. -/
theorem localLaw_prob_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ij : B.Idx N × B.Idx N,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  localLaw_prob_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD

/-- **Theorem 2.3, (2.4), paper form**, on `RBM.BoundsCore`: for `τ', D > 0` and large `N`,
`P(max_a |W⁻¹ ∑_{x ∈ I_a} G_{xx} - m| > W^{τ'} (W ℓ η)^{-1}) ≤ N^{-D}`. -/
theorem partialTrace_prob_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ a : ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
    (partialTrace_of_boundsCore T T1 hκ hz hB) hτ' hD

/-- **Theorem 2.3, (2.4), paper form**: for `τ', D > 0` and large `N`,
`P(max_a |W⁻¹ ∑_{x ∈ I_a} G_{xx} - m| > W^{τ'} (W ℓ η)^{-1}) ≤ N^{-D}`. -/
theorem partialTrace_prob_of_bounds (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ a : ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  partialTrace_prob_of_boundsCore T T1 hκ hz hB.toBoundsCore hτ' hD

/-- **Theorem 2.4, (2.6), paper form**, on `RBM.BoundsCore`: for `τ', D > 0` and large `N`,
`P(max_{a,b} |Tr G E_a G† E_b - W⁻¹ (|m|²/(1 - |m|² S^{(B)}))_{ab}| > W^{τ'} (W ℓ η)^{-2})
≤ N^{-D}`. -/
theorem quantumDiffusion_pm_prob_of_boundsCore (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  B.prob_le_of_stochDom (fun N _ _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (quantumDiffusion_pm_of_boundsCore T hκ hz hB) hτ' hD

/-- **Theorem 2.4, (2.6), paper form**: for `τ', D > 0` and large `N`,
`P(max_{a,b} |Tr G E_a G† E_b - W⁻¹ (|m|²/(1 - |m|² S^{(B)}))_{ab}| > W^{τ'} (W ℓ η)^{-2})
≤ N^{-D}`. -/
theorem quantumDiffusion_pm_prob_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  quantumDiffusion_pm_prob_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD

/-- **Theorem 2.4, (2.7), paper form**, on `RBM.BoundsCore`: for `τ', D > 0` and large `N`,
`P(max_{a,b} |Tr G E_a G E_b - W⁻¹ (m²/(1 - m² S^{(B)}))_{ab}| > W^{τ'} (W ℓ η)^{-2})
≤ N^{-D}`. -/
theorem quantumDiffusion_pp_prob_of_boundsCore (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  B.prob_le_of_stochDom (fun N _ _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (quantumDiffusion_pp_of_boundsCore T hκ hz hB) hτ' hD

/-- **Theorem 2.4, (2.7), paper form**: for `τ', D > 0` and large `N`,
`P(max_{a,b} |Tr G E_a G E_b - W⁻¹ (m²/(1 - m² S^{(B)}))_{ab}| > W^{τ'} (W ℓ η)^{-2})
≤ N^{-D}`. -/
theorem quantumDiffusion_pp_prob_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  quantumDiffusion_pp_prob_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD

/-- **Theorem 2.4, (2.8), paper form**: for `τ' > 0` and large `N`,
`max_{a,b} |E Tr G E_a G† E_b - W⁻¹ (|m|²/(1 - |m|² S^{(B)}))_{ab}| ≤ (W ℓ η)^{-3} W^{τ'}`. -/
theorem expect_quantumDiffusion_pm_W_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3 :=
  B.le_W_rpow_of_unifDetDom (fun N _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (expect_quantumDiffusion_pm_of_bounds T hκ hz hB) hτ'

/-- **Theorem 2.4, (2.9), paper form**: for `τ' > 0` and large `N`,
`max_{a,b} |E Tr G E_a G E_b - W⁻¹ (m²/(1 - m² S^{(B)}))_{ab}| ≤ (W ℓ η)^{-3} W^{τ'}`. -/
theorem expect_quantumDiffusion_pp_W_of_bounds (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3 :=
  B.le_W_rpow_of_unifDetDom (fun N _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (expect_quantumDiffusion_pp_of_bounds T hκ hz hB) hτ'

/-! #### Assembled: Theorems 2.3 and 2.4 from Theorem 2.21 -/

/-- **Theorem 2.3 (local semicircle law)**, assuming Theorem 2.21 (`RBM.Thm221`) and the
identities in law (2.39)/(2.65) (`RBM.Transfer`, `RBM.TransferLoop1`): for `τ', D > 0` and large
`N`, with probability `≥ 1 - N^{-D}` (each event below has probability `≤ N^{-D}`),
(2.3) `max_{x,y} |(G - m)_{xy}| ≤ W^{τ'} (W ℓ η)^{-1/2}`,
(2.4) `max_a |W⁻¹ ∑_{x ∈ I_a} G_{xx} - m| ≤ W^{τ'} (W ℓ η)^{-1}`, and the tracial law
`|N⁻¹ Tr G - m| ≤ W^{τ'} (W ℓ η)^{-1}`. -/
theorem localSemicircleLaw_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ij : B.Idx N × B.Idx N,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ a : ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ _u : Unit,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  ⟨localLaw_prob_of_boundsCore T hκ hz hB hτ' hD,
    partialTrace_prob_of_boundsCore T T1 hκ hz hB hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (trace_of_boundsCore T T1 hκ hz hB) hτ' hD⟩

/-- **Theorem 2.3 (local semicircle law)**, assuming Theorem 2.21 (`RBM.Thm221`) and the
identities in law (2.39)/(2.65) (`RBM.Transfer`, `RBM.TransferLoop1`): for `τ', D > 0` and large
`N`, with probability `≥ 1 - N^{-D}` (each event below has probability `≤ N^{-D}`),
(2.3) `max_{x,y} |(G - m)_{xy}| ≤ W^{τ'} (W ℓ η)^{-1/2}`,
(2.4) `max_a |W⁻¹ ∑_{x ∈ I_a} G_{xx} - m| ≤ W^{τ'} (W ℓ η)^{-1}`, and the tracial law
`|N⁻¹ Tr G - m| ≤ W^{τ'} (W ℓ η)^{-1}`. -/
theorem localSemicircleLaw_of_Thm221 (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221 X κ) (hτ : 0 < τ) (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ij : B.Idx N × B.Idx N,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ a : ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ _u : Unit,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  localSemicircleLaw_of_boundsCore T T1 hκ hz (hz.bounds X hκ hT hτ).toBoundsCore hτ' hD

/-- **(2.6) and (2.7) of Theorem 2.4** on `RBM.BoundsCore`: the first two conjuncts of
`RBM.quantumDiffusion_of_Thm221`, which need only (2.68)–(2.70).  The last two conjuncts of that
theorem are (2.8) and (2.9); they need (2.71) (`RBM.Bounds.expect`), so they stay on
`RBM.Bounds`. -/
theorem quantumDiffusion_pm_pp_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  ⟨quantumDiffusion_pm_prob_of_boundsCore T hκ hz hB hτ' hD,
    quantumDiffusion_pp_prob_of_boundsCore T hκ hz hB hτ' hD⟩

/-- **Theorem 2.4 (quantum diffusion)**, assuming Theorem 2.21 (`RBM.Thm221`) and the identities
in law (2.66) (`RBM.Transfer`): for `τ', D > 0` and large `N`, (2.6), (2.7) hold with probability
`≥ 1 - N^{-D}` and (2.8), (2.9) hold, with `G = G(z)`, `m = m(z)`,
`Θ_ξ = (1 - ξ S^{(B)})⁻¹`. -/
theorem quantumDiffusion_of_Thm221 (T : Transfer X) (hκ : 0 < κ) (hT : Thm221 X κ) (hτ : 0 < τ)
    (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3) := by
  have hB := hz.bounds X hκ hT hτ
  exact ⟨(quantumDiffusion_pm_pp_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD).1,
    (quantumDiffusion_pm_pp_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD).2,
    expect_quantumDiffusion_pm_W_of_bounds T hκ hz hB hτ',
    expect_quantumDiffusion_pp_W_of_bounds T hκ hz hB hτ'⟩

/-! #### `rfl`-probes: nothing was weakened (T211)

`Eq` forces both sides to have the same type, so each `example` below type-checks only if the two
conclusions are **definitionally equal** (T107's technique).  Only the hypothesis moved from
`RBM.Bounds` to `RBM.BoundsCore`; not a character of any statement changed. -/

section Probes

variable (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
  (hB : Bounds X E (fun N => lemT (z N))) (hT : Thm221 X κ) (hτ : 0 < τ) {τ' D : ℝ}
  (hτ' : 0 < τ') (hD : 0 < D)

example : localLaw_of_bounds T hκ hz hB = localLaw_of_boundsCore T hκ hz hB.toBoundsCore :=
  rfl

example : loop1_of_bounds T T1 hκ hz hB = loop1_of_boundsCore T T1 hκ hz hB.toBoundsCore :=
  rfl

example : partialTrace_of_bounds T T1 hκ hz hB =
    partialTrace_of_boundsCore T T1 hκ hz hB.toBoundsCore := rfl

example (σ₂ : Bool) :
    loop2_of_bounds T hκ hz hB σ₂ = loop2_of_boundsCore T hκ hz hB.toBoundsCore σ₂ := rfl

example : quantumDiffusion_pm_of_bounds T hκ hz hB =
    quantumDiffusion_pm_of_boundsCore T hκ hz hB.toBoundsCore := rfl

example : quantumDiffusion_pp_of_bounds T hκ hz hB =
    quantumDiffusion_pp_of_boundsCore T hκ hz hB.toBoundsCore := rfl

example : trace_of_bounds T T1 hκ hz hB = trace_of_boundsCore T T1 hκ hz hB.toBoundsCore :=
  rfl

example : localLaw_prob_of_bounds T hκ hz hB hτ' hD =
    localLaw_prob_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD := rfl

example : partialTrace_prob_of_bounds T T1 hκ hz hB hτ' hD =
    partialTrace_prob_of_boundsCore T T1 hκ hz hB.toBoundsCore hτ' hD := rfl

example : quantumDiffusion_pm_prob_of_bounds T hκ hz hB hτ' hD =
    quantumDiffusion_pm_prob_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD := rfl

example : quantumDiffusion_pp_prob_of_bounds T hκ hz hB hτ' hD =
    quantumDiffusion_pp_prob_of_boundsCore T hκ hz hB.toBoundsCore hτ' hD := rfl

example : localSemicircleLaw_of_Thm221 T T1 hκ hT hτ hz hτ' hD =
    localSemicircleLaw_of_boundsCore T T1 hκ hz (hz.bounds X hκ hT hτ).toBoundsCore hτ' hD := rfl

/-- The first conjunct of Theorem 2.4 — (2.6) — is unchanged. -/
example : (quantumDiffusion_of_Thm221 T hκ hT hτ hz hτ' hD).1 =
    (quantumDiffusion_pm_pp_of_boundsCore T hκ hz (hz.bounds X hκ hT hτ).toBoundsCore hτ' hD).1 :=
  rfl

/-- The second conjunct of Theorem 2.4 — (2.7) — is unchanged. -/
example : (quantumDiffusion_of_Thm221 T hκ hT hτ hz hτ' hD).2.1 =
    (quantumDiffusion_pm_pp_of_boundsCore T hκ hz (hz.bounds X hκ hT hτ).toBoundsCore hτ' hD).2 :=
  rfl

/-- (2.8) and (2.9) — the last two conjuncts — still require (2.71) (`RBM.Bounds.expect`), and
are **not** on `RBM.BoundsCore`: this is T205. -/
example : (quantumDiffusion_of_Thm221 T hκ hT hτ hz hτ' hD).2.2.1 =
    expect_quantumDiffusion_pm_W_of_bounds T hκ hz (hz.bounds X hκ hT hτ) hτ' := rfl

example : (quantumDiffusion_of_Thm221 T hκ hT hτ hz hτ' hD).2.2.2 =
    expect_quantumDiffusion_pp_W_of_bounds T hκ hz (hz.bounds X hκ hT hτ) hτ' := rfl

end Probes

end Main

end RBM

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.CutoffChi
import RBM1D.Hierarchy.Step2Moment
import RBM1D.Hierarchy.Step2MomentStep

/-!
# The truncated moment Duhamel, and `MomentHypCut` (T197)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.47): the **truncated** moment route.

## Why a truncated interface exists at all

T132c (`RBM1D/Hierarchy/Step2MomentStep.lean`) delivered the reduction of
`RBM.Step2PP.BootPP.step` to finitely many fixed times and the near/far split of (5.48), and
*proved* — as compiled theorems, not as an argument — that `RBM.Step2Moment.MomentHyp.step`
is **not provable in its frozen shape**:

* `RBM.Step2MomentStep.bnd_poly_excludes_pow` : the field `bnd_poly` forbids `bnd` from
  carrying any power of `N`, while the union bound for the max over `L²` loop arguments inside
  `J*` costs `L² ≍ N²` at every order;
* `RBM.Step2MomentStep.detrunc_remainder_ge_thr`, `detrunc_order_needed` : de-truncating
  *inside the moment* leaves a Markov remainder no smaller than the threshold itself, removable
  only by multiplying the order by `(K + δ)/δ`.

So `MomentHyp.step` is frozen and untouched, and this file adds the truncated replacement.  Its
whole point is that de-truncation happens at the **probability** level: on the event where the
prefix bound holds, the truncated and the untruncated functional are *equal*
(`cutTrunc_eq_of_prefix`), so no remainder is produced at all, and the only price is a union
bound over the **polynomially many** net points of (5.46).

`RBM1D/Gauss/MomentDuhamel*.lean` is not touched: `RBM.MomentDuhamel.Hyp` remains the
untruncated interface (the decision recorded as D10 in `docs/STATUS.md`, ruled (a) by Cowork).

## Main definitions

* `RBM.MomentDuhamelCut.cutTrunc Θ x = χ(x/Θ) · x` — the truncated functional, with T175's
  concrete quintic `RBM.Cutoff.cutChi`.  Mathlib's bumps are unusable here: they carry no
  derivative bound (see `RBM1D/Gauss/CutoffChi.lean`).
* `RBM.MomentDuhamelCut.netFinset` — the net `{s_N + k/m_N}` of (5.46) as a **`Finset`**,
  which is what the union bound needs; `RBM.Step2MomentStep.netSet` is the same net as a `Set`.
* `RBM.MomentDuhamelCut.CutHyp` — **the truncated moment Duhamel interface**: a deterministic
  modulus of continuity, a polynomial net, and the moment bound for the *truncated* functional
  at the net points, in the `RBM.Gauss.MomentDom` shape (`ε` outside `p`, `N → ∞` innermost).
* `RBM.MomentDuhamelCut.MomentHypCut` — the replacement for `RBM.Step2Moment.MomentHyp`: a
  `CutHyp` for the normalized `J*` together with the initial bound of (2.69).

## Main results

* `cutTrunc_eq_self`, `cutTrunc_le_two_mul`, `cutTrunc_eq_of_prefix` — the two facts the whole
  scheme rests on: below the threshold the truncation is invisible, above `2Θ` it is zero, and
  on a prefix event the truncated and untruncated paths coincide **at the net point**.
* `cut_sq_le`, `cut_sesq_le`, `cut_cube_le`, `cut_self_quadratic_le`, `cut_contraction` —
  **the linearization on the support**, i.e. T132c's `RBM.Step2MomentStep.linearize_on_support`
  transported through the cutoff.  `cut_contraction` is the exact counterpart of
  `RBM.Step2MomentStep.no_finite_pass`: the self-quadratic term `θ²/A` of (5.83) is *not* a
  contraction at `θ ≥ A`, but `χ(θ/Θ) θ²/A` is one as soon as `4Θ ≤ A`.
* `hev_of_cutHyp` — **the heart**: the truncated moment bound plus the coincidence on the
  prefix event give exactly the fixed-time input `hev` of
  `RBM.Step2MomentStep.bootPP_of_net`.  Markov at order `2p` with `p` chosen from `D`, then a
  union bound over the net.
* `stochDom_of_net`, `stochDom_of_cutHyp` — the generic pathwise bootstrap: `hev` on the net
  plus the modulus give `J ≺ Θ` uniformly in `u ∈ [s, t]`.  This is
  `RBM.Step2PP.xiLK_two_le` with the loop functional abstracted out.
* `bootPP_of_cutHyp` — **`hΘ`**: `RBM.Step2PP.BootPP` produced from a `CutHyp` for
  `Ξ^{(L-K)}_{u,2}`.
* `jS_stochDom_cut` — **(5.47)**, in *exactly* the conclusion of
  `RBM.Step2Moment.jS_stochDom`, from `MomentHypCut` instead of the unprovable `MomentHyp`.
* `aprioriDecay_cut`, `step2_cut` — **(2.75) and (2.76)**, in exactly the shapes of the fields
  `RBM.Steps.localLaw` and `RBM.Steps.aprioriDecay`.  These are `RBM.Step2Moment.aprioriDecay`
  and `RBM.Step2Moment.step2` verbatim with `MomentHyp` swapped for `MomentHypCut`, and they
  are the ticket's acceptance criterion: the whole of Step 2 is now reachable without the
  frozen `MomentHyp.step`.

## Satisfiability (compiled, §7)

The project's dominant defect is a vacuous hypothesis, so every bundle introduced here carries
a compiled witness:

* `satCutHyp` — a **complete, compiled `CutHyp`**, at the **critical scale** `J ≡ Θ` (not at
  `J ≡ 0`): the interface is not secretly asking for `J ≪ Θ`.  It is taken at the flow's own
  parameters — Hölder exponent `γ = 1/2` and a genuinely fine net `m_N ≍ N²` — so the two
  conditions `mesh_fine` and `card_le`, which pull in opposite directions (a fine net makes the
  net displacement small, a coarse net keeps the union bound cheap) and are therefore the pair
  most at risk of being jointly unsatisfiable, are satisfied *simultaneously and by the same
  witness*.  The window `[0,1]` is non-degenerate, so `TimeIcc` is inhabited.
* `sat_stochDom_of_cutHyp` — the **end-to-end** check: that witness really feeds
  `stochDom_of_cutHyp` and a `RBM.StochDom` comes out.
* `sat_mesh_card` — `mesh_fine` is **tight**: at `Θ ≡ 1`, `Kmod = 1`, `γ = 1/2` and `m_N = N²`
  it holds with *equality*, so the mesh cannot be coarsened by the argument used.
* `sat_hev_target_pos` — the improvement `(N^δ - 1)Θ_N` of `hev` is positive for large `N`.  It
  is *negative* for small `N`, where `hev` would be false rather than vacuous; `HighProb`'s
  `∀ᶠ N` is what puts the statement on the right side of that.
* `sat_cut_sq_nonvacuous` — the linearization has content on the gap: at `J = 3Θ/2`, where
  `χ(3/2) = 1/2`, both sides of `cut_sq_le` are nonzero.

Quantifier order is the paper's: in `CutHyp.moment`, `δ` and `ε` are fixed *before* `p`, and
`N → ∞` is innermost, exactly as in `RBM.Gauss.MomentDom`.  Reading it as `∀ p ∀ N` would be
the error that made an end-to-end theorem vacuous once before (`docs/STATUS.md`, T145).

## What is **not** here

* the far half `hfar` of (5.48) — the one-step bound carrying the three indicators of
  (5.39)/(5.41)/(5.44).  That is T198, and it is built *on* this file's interface.
* the sharpened `(η_s/η_u)²` prefactor of `RBM.Step2MomentStep.flowEq548_of_near_far`'s `hnear`:
  the repository's (5.47), and `jS_stochDom_cut` below, give `(η_s/η_u)^4`.
* the Gaussian discharge of `CutHyp.moment` itself, i.e. the truncated Duhamel computation.
  Nothing here is an `axiom` and nothing is `sorry`.

## Deviations from the paper

* The paper truncates with the stopping time (5.43); here the truncation is the smooth cutoff
  `χ(J/Θ)` and the de-truncation is the crossing argument of
  `RBM.Step2MomentStep.le_of_gap_net`.  Already recorded for T158/T175.
* `hev`'s improvement factor is `N^δ - 1` rather than `N^δ`: the missing `1` is the net error,
  paid once (`RBM.Step2MomentStep.bootPP_step_of_net`).
-/

namespace RBM

namespace MomentDuhamelCut

open MeasureTheory Filter Real

/-! ### 1. The truncated functional and its algebra -/

section Trunc

/-- **The truncated functional** `J ↦ χ(J/Θ) · J`, with T175's concrete quintic Hermite
profile `RBM.Cutoff.cutChi`.

Two properties make it the right object, and they pull against each other in the way the
scheme needs: it is *equal* to `J` below the threshold (`cutTrunc_eq_self`) and *bounded by
`2Θ` everywhere* (`cutTrunc_le_two_mul`).  The first is what makes de-truncation free on a
prefix event; the second is what makes every moment of it finite for free. -/
noncomputable def cutTrunc (Θ x : ℝ) : ℝ := Cutoff.cutChi (x / Θ) * x

theorem cutTrunc_nonneg {Θ x : ℝ} (hx : 0 ≤ x) : 0 ≤ cutTrunc Θ x :=
  mul_nonneg (Cutoff.cutChi_nonneg _) hx

theorem cutTrunc_le_self {Θ x : ℝ} (hx : 0 ≤ x) : cutTrunc Θ x ≤ x := by
  have h := Cutoff.cutChi_le_one (x / Θ)
  rw [cutTrunc]
  nlinarith [Cutoff.cutChi_nonneg (x / Θ)]

/-- **Below the threshold the truncation is invisible.**  This is the half that makes the
de-truncation free: no Markov remainder is produced, in contrast with
`RBM.Step2MomentStep.detrunc_remainder_ge_thr`. -/
theorem cutTrunc_eq_self {Θ x : ℝ} (hΘ : 0 < Θ) (hx : x ≤ Θ) : cutTrunc Θ x = x := by
  have : x / Θ ≤ 1 := by rw [div_le_one hΘ]; exact hx
  rw [cutTrunc, Cutoff.cutChi_eq_one this, one_mul]

/-- **Above `2Θ` the truncation kills everything.** -/
theorem cutTrunc_eq_zero {Θ x : ℝ} (hΘ : 0 < Θ) (hx : 2 * Θ ≤ x) : cutTrunc Θ x = 0 := by
  have : (2 : ℝ) ≤ x / Θ := by rw [le_div_iff₀ hΘ]; linarith
  rw [cutTrunc, Cutoff.cutChi_eq_zero this, zero_mul]

/-- **The truncated functional has a deterministic envelope `2Θ`.**  Every moment of it is
therefore finite on a probability space, with no integrability hypothesis
(`integrable_cutTrunc_pow`). -/
theorem cutTrunc_le_two_mul {Θ x : ℝ} (hΘ : 0 < Θ) (hx : 0 ≤ x) : cutTrunc Θ x ≤ 2 * Θ := by
  rcases le_or_gt x (2 * Θ) with h | h
  · exact (cutTrunc_le_self hx).trans h
  · rw [cutTrunc_eq_zero hΘ h.le]; positivity

theorem abs_cutTrunc_le {Θ x : ℝ} (hΘ : 0 < Θ) (hx : 0 ≤ x) : |cutTrunc Θ x| ≤ 2 * Θ := by
  rw [abs_of_nonneg (cutTrunc_nonneg hx)]
  exact cutTrunc_le_two_mul hΘ hx

theorem continuous_cutTrunc (Θ : ℝ) : Continuous (cutTrunc Θ) := by
  unfold cutTrunc
  exact (Cutoff.differentiable_cutChi.continuous.comp (continuous_id.div_const Θ)).mul
    continuous_id

/-! #### The linearization on the support

On `{χ(J/Θ) ≠ 0}` one has `J ≤ 2Θ`, and there every super-linear power of `J` that
(5.34)/(5.35)/(5.36) produce is linear.  These are T132c's
`RBM.Step2MomentStep.linearize_on_support` multiplied by the cutoff, so that they hold
*unconditionally* in `J` — off the support both sides vanish. -/

/-- The support statement: a nonzero cutoff forces `J ≤ 2Θ`. -/
theorem le_two_mul_of_cutChi_ne_zero {Θ x : ℝ} (hΘ : 0 < Θ) (h : Cutoff.cutChi (x / Θ) ≠ 0) :
    x ≤ 2 * Θ := by
  by_contra hc
  exact h (Cutoff.cutChi_eq_zero (by rw [le_div_iff₀ hΘ]; linarith [not_le.1 hc]))

/-- **`J² ≤ 2Θ J` on the support**, unconditionally after multiplying by the cutoff. -/
theorem cut_sq_le {Θ x : ℝ} (hΘ : 0 < Θ) (hx : 0 ≤ x) :
    Cutoff.cutChi (x / Θ) * x ^ 2 ≤ 2 * Θ * cutTrunc Θ x := by
  rcases eq_or_ne (Cutoff.cutChi (x / Θ)) 0 with h | h
  · rw [cutTrunc, h]; simp
  · have hx2 : x ≤ 2 * Θ := le_two_mul_of_cutChi_ne_zero hΘ h
    have hlin := (Step2MomentStep.linearize_on_support hx hΘ.le hx2).1
    rw [cutTrunc]
    calc Cutoff.cutChi (x / Θ) * x ^ 2
        ≤ Cutoff.cutChi (x / Θ) * (2 * Θ * x) :=
          mul_le_mul_of_nonneg_left hlin (Cutoff.cutChi_nonneg _)
      _ = 2 * Θ * (Cutoff.cutChi (x / Θ) * x) := by ring

/-- **`J^{3/2} ≤ √(2Θ) J` on the support** — the `γ`-term of the (2.73)-reduced (5.35). -/
theorem cut_sesq_le {Θ x : ℝ} (hΘ : 0 < Θ) (hx : 0 ≤ x) :
    Cutoff.cutChi (x / Θ) * (x * √x) ≤ √(2 * Θ) * cutTrunc Θ x := by
  rcases eq_or_ne (Cutoff.cutChi (x / Θ)) 0 with h | h
  · rw [cutTrunc, h]; simp
  · have hx2 : x ≤ 2 * Θ := le_two_mul_of_cutChi_ne_zero hΘ h
    have hlin := (Step2MomentStep.linearize_on_support hx hΘ.le hx2).2.1
    rw [cutTrunc]
    calc Cutoff.cutChi (x / Θ) * (x * √x)
        ≤ Cutoff.cutChi (x / Θ) * (√(2 * Θ) * x) :=
          mul_le_mul_of_nonneg_left hlin (Cutoff.cutChi_nonneg _)
      _ = √(2 * Θ) * (Cutoff.cutChi (x / Θ) * x) := by ring

/-- **`J³ ≤ 4Θ² J` on the support** — the paper's cubic drift term of (5.36). -/
theorem cut_cube_le {Θ x : ℝ} (hΘ : 0 < Θ) (hx : 0 ≤ x) :
    Cutoff.cutChi (x / Θ) * x ^ 3 ≤ 4 * Θ ^ 2 * cutTrunc Θ x := by
  rcases eq_or_ne (Cutoff.cutChi (x / Θ)) 0 with h | h
  · rw [cutTrunc, h]; simp
  · have hx2 : x ≤ 2 * Θ := le_two_mul_of_cutChi_ne_zero hΘ h
    have hlin := (Step2MomentStep.linearize_on_support hx hΘ.le hx2).2.2
    rw [cutTrunc]
    calc Cutoff.cutChi (x / Θ) * x ^ 3
        ≤ Cutoff.cutChi (x / Θ) * (4 * Θ ^ 2 * x) :=
          mul_le_mul_of_nonneg_left hlin (Cutoff.cutChi_nonneg _)
      _ = 4 * Θ ^ 2 * (Cutoff.cutChi (x / Θ) * x) := by ring

/-- **The self-quadratic term of (5.83), linearized.**  `χ(J/Θ) J²/A ≤ (2Θ/A) · χ(J/Θ) J`. -/
theorem cut_self_quadratic_le {Θ A x : ℝ} (hΘ : 0 < Θ) (hA : 0 < A) (hx : 0 ≤ x) :
    Cutoff.cutChi (x / Θ) * (x ^ 2 / A) ≤ (2 * Θ / A) * cutTrunc Θ x := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : (0 : ℝ) ≤ A⁻¹ := by positivity
  calc Cutoff.cutChi (x / Θ) * (x ^ 2 * A⁻¹)
      = (Cutoff.cutChi (x / Θ) * x ^ 2) * A⁻¹ := by ring
    _ ≤ (2 * Θ * cutTrunc Θ x) * A⁻¹ := mul_le_mul_of_nonneg_right (cut_sq_le hΘ hx) hinv
    _ = 2 * Θ * A⁻¹ * cutTrunc Θ x := by ring

/-- **The contraction the cutoff buys, stated against `RBM.Step2MomentStep.no_finite_pass`.**

`no_finite_pass` is the compiled negative result that `θ ↦ c + θ²/A` is *not* a contraction on
`θ ≥ A`, so the `(+,+)` bootstrap cannot be replaced by finitely many `≺`-passes.  After the
cutoff the same term is `≤ ½ χ(J/Θ) J` as soon as `4Θ ≤ A`, i.e. the map *is* a contraction on
the support — which is precisely why the truncated one-step improvement closes at the **same**
moment order. -/
theorem cut_contraction {Θ A x : ℝ} (hΘ : 0 < Θ) (hA : 4 * Θ ≤ A) (hx : 0 ≤ x) :
    Cutoff.cutChi (x / Θ) * (x ^ 2 / A) ≤ (1 / 2) * cutTrunc Θ x := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (by linarith) hA
  refine (cut_self_quadratic_le hΘ hA0 hx).trans ?_
  have hc : 2 * Θ / A ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hA0 (by norm_num)]
    linarith
  exact mul_le_mul_of_nonneg_right hc (cutTrunc_nonneg hx)

end Trunc

/-! ### 2. Coincidence on the prefix event -/

section Prefix

variable {Ω : Type*}

/-- **On the prefix event the truncated and the untruncated functional coincide.**

This is the statement the whole probability-level de-truncation rests on.  `hpre` is the
prefix hypothesis of `RBM.Step2PP.BootPP.step` and of
`RBM.Step2MomentStep.bootPP_step_of_net` — the a priori bound on `[s, ws]` — and `ws` is the
right endpoint of that prefix, so the hypothesis applies to it. -/
theorem cutTrunc_eq_of_prefix {J : ℝ → ℝ} {a ws Θ : ℝ} (hΘ : 0 < Θ) (haw : a ≤ ws)
    (hpre : ∀ u ∈ Set.Icc a ws, J u ≤ Θ) : cutTrunc Θ (J ws) = J ws :=
  cutTrunc_eq_self hΘ (hpre ws ⟨haw, le_rfl⟩)

/-- The event form: on the prefix event, a bound on the *truncated* functional is a bound on
the untruncated one.  No remainder — contrast `RBM.Step2MomentStep.detrunc_remainder_ge_thr`,
which is the cost of doing this inside the moment instead. -/
theorem le_of_cutTrunc_le_of_prefix {J : ℝ → ℝ} {a ws Θ c : ℝ} (hΘ : 0 < Θ) (haw : a ≤ ws)
    (hpre : ∀ u ∈ Set.Icc a ws, J u ≤ Θ) (h : cutTrunc Θ (J ws) ≤ c) : J ws ≤ c := by
  rwa [cutTrunc_eq_of_prefix hΘ haw hpre] at h

end Prefix

/-! ### 3. The net of (5.46) as a `Finset`, and the modulus of continuity -/

section Net

/-- **The net `{s_N + k/m_N}` of (5.46) inside the window, as a `Finset`.**

`RBM.Step2MomentStep.netSet` is the same family as a `Set`; the union bound of
`hev_of_cutHyp` needs it to be finite, and its cardinality to be polynomial in `N`, so it is
recorded here as a `Finset`. -/
noncomputable def netFinset (s t m : ℕ → ℝ) (N : ℕ) : Finset ℝ :=
  Finset.image (fun k : ℕ => s N + (k : ℝ) / m N)
    (Finset.range (⌊(t N - s N) * m N⌋₊ + 1))

/-- **Every net point lies in the window.**  The index is cut at `⌊(t_N - s_N) m_N⌋`, not at
the ceiling, precisely so that this holds: the union bound of `hev_of_cutHyp` runs over the
whole `Finset`, and the moment hypothesis is only ever asserted inside the window. -/
theorem netFinset_subset_Icc {s t m : ℕ → ℝ} {N : ℕ} (hst : s N ≤ t N) (hm : 0 < m N) :
    ∀ ws ∈ netFinset s t m N, ws ∈ Set.Icc (s N) (t N) := by
  intro ws hws
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hws
  have hkle : k ≤ ⌊(t N - s N) * m N⌋₊ := by
    have := Finset.mem_range.1 hk; omega
  have hnn : (0 : ℝ) ≤ (t N - s N) * m N := by
    have : (0 : ℝ) ≤ t N - s N := by linarith
    positivity
  have h1 : (k : ℝ) ≤ (t N - s N) * m N :=
    le_trans (by exact_mod_cast Nat.cast_le.2 hkle) (Nat.floor_le hnn)
  have h2 : (k : ℝ) / m N ≤ t N - s N := by rw [div_le_iff₀ hm]; exact h1
  have h3 : (0 : ℝ) ≤ (k : ℝ) / m N := div_nonneg (Nat.cast_nonneg k) hm.le
  exact ⟨by linarith, by linarith⟩

/-- **The net is polynomially large** as soon as the mesh is: its cardinality is at most
`(t_N - s_N) m_N + 2`.  This is what keeps the union bound of `hev_of_cutHyp` cheap, and it is
the condition that pulls against `CutHyp.mesh_fine` (see `sat_mesh_card`). -/
theorem netFinset_card_le {s t m : ℕ → ℝ} {N : ℕ} (hst : s N ≤ t N) (hm : 0 < m N) :
    ((netFinset s t m N).card : ℝ) ≤ (t N - s N) * m N + 2 := by
  have hnn : (0 : ℝ) ≤ (t N - s N) * m N := by
    have : (0 : ℝ) ≤ t N - s N := by linarith
    positivity
  have h1 : (netFinset s t m N).card ≤ ⌊(t N - s N) * m N⌋₊ + 1 := by
    refine le_trans Finset.card_image_le ?_
    simp
  have h2 : ((⌊(t N - s N) * m N⌋₊ : ℕ) : ℝ) ≤ (t N - s N) * m N := Nat.floor_le hnn
  calc ((netFinset s t m N).card : ℝ) ≤ ((⌊(t N - s N) * m N⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ((⌊(t N - s N) * m N⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (t N - s N) * m N + 2 := by linarith

/-- **Every `v` in the window has a net point to its left, within one mesh.**  This is
`RBM.Step2MomentStep.exists_netPoint_le` with the index bounded, so that the net point lands
in the `Finset`. -/
theorem exists_mem_netFinset {s t m : ℕ → ℝ} {N : ℕ} (hm : 0 < m N) {v : ℝ}
    (hv : v ∈ Set.Icc (s N) (t N)) :
    ∃ ws ∈ netFinset s t m N, ws ∈ Set.Icc (s N) v ∧ v - ws ≤ 1 / m N := by
  obtain ⟨k, hk1, hk2⟩ := Step2MomentStep.exists_netPoint_le (a := s N) hm hv.1
  have hkle : (k : ℝ) ≤ (t N - s N) * m N := by
    have h1 : (k : ℝ) / m N ≤ t N - s N := by linarith [hv.2]
    rw [div_le_iff₀ hm] at h1
    exact h1
  have hkr : k < ⌊(t N - s N) * m N⌋₊ + 1 := by
    have : k ≤ ⌊(t N - s N) * m N⌋₊ := Nat.le_floor hkle
    omega
  refine ⟨s N + (k : ℝ) / m N, ?_, ⟨?_, hk1⟩, hk2⟩
  · exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hkr, rfl⟩
  · have : (0 : ℝ) ≤ (k : ℝ) / m N := div_nonneg (Nat.cast_nonneg k) hm.le
    linarith

/-- **A Hölder modulus of continuity gives continuity on the window.**  So the pathwise
bootstrap `RBM.le_of_bootstrap_prefix` needs no separate continuity field: the modulus that the
net of (5.46) already requires implies it. -/
theorem continuousOn_of_modulus {a b C γ : ℝ} (hγ : 0 < γ) {Y : ℝ → ℝ}
    (hmod : ∀ v ∈ Set.Icc a b, ∀ w ∈ Set.Icc a b, |Y v - Y w| ≤ C * |v - w| ^ γ) :
    ContinuousOn Y (Set.Icc a b) := by
  have hC1 : (0 : ℝ) < |C| + 1 := by positivity
  intro w hw
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨(ε / (|C| + 1)) ^ (1 / γ), Real.rpow_pos_of_pos (by positivity) _, fun x hx hdist => ?_⟩
  have hxw := hmod x hx w hw
  have hlt : |x - w| ^ γ < ((ε / (|C| + 1)) ^ (1 / γ)) ^ γ := by
    refine Real.rpow_lt_rpow (abs_nonneg _) ?_ hγ
    simpa [Real.dist_eq] using hdist
  have hpow : ((ε / (|C| + 1)) ^ (1 / γ)) ^ γ = ε / (|C| + 1) := by
    rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hγ.ne', Real.rpow_one]
  have hCle : C * |x - w| ^ γ ≤ (|C| + 1) * |x - w| ^ γ := by
    have : C ≤ |C| + 1 := by linarith [le_abs_self C]
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (abs_nonneg _) _)
  rw [Real.dist_eq]
  calc |Y x - Y w| ≤ C * |x - w| ^ γ := hxw
    _ ≤ (|C| + 1) * |x - w| ^ γ := hCle
    _ < (|C| + 1) * (ε / (|C| + 1)) := by
        refine mul_lt_mul_of_pos_left ?_ hC1
        rwa [hpow] at hlt
    _ = ε := by field_simp

end Net

/-! ### 4. The truncated moment Duhamel interface -/

section Interface

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Every moment of the truncated functional is finite, for free.**

This is the first dividend of the cutoff: `cutTrunc θ` has the deterministic envelope `2θ`
(`cutTrunc_le_two_mul`), so on a finite measure no integrability hypothesis is needed.  The
untruncated interface has to assume it (`RBM.MomentDuhamel.Hyp.integrable`,
`RBM.Step2Moment.MomentHyp.env`). -/
theorem integrable_cutTrunc_pow {P : Measure Ω} [IsFiniteMeasure P] {θ : ℝ} (hθ : 0 < θ)
    {Y : Ω → ℝ} (hY0 : ∀ ω, 0 ≤ Y ω) (hY : AEStronglyMeasurable Y P) (q : ℕ) :
    Integrable (fun ω => |cutTrunc θ (Y ω)| ^ q) P := by
  refine Integrable.mono' (g := fun _ => (2 * θ) ^ q) (integrable_const _) ?_ ?_
  · exact ((continuous_abs.comp (continuous_cutTrunc θ)).pow q).comp_aestronglyMeasurable hY
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ (hY0 ω)) q

/-- **The truncated moment Duhamel interface.**

`J` is the state functional the bootstrap runs on — `Ξ^{(L-K)}_{u,2}` for the `(+,+)` charge of
§5.3, or `RBM.Step2Moment.jSnorm` for the `(+,-)` charge of (5.29) — and `Θ` is the bound the
bootstrap propagates.  Compare `RBM.Step2Moment.MomentHyp`:

* the fields `env`, `env_le` are **gone**: the deterministic envelope is `2Θ` and it is a
  theorem (`cutTrunc_le_two_mul`), not a hypothesis;
* the fields `bnd`, `thr`, `bnd_lt_thr`, `bnd_poly`, `init`, `step` are replaced by the single
  field `moment`, which asks for a moment bound on the **truncated** functional and only at
  the **net points**.  This is the change that makes the interface provable at all:
  `RBM.Step2MomentStep.bnd_poly_excludes_pow` shows the frozen `bnd_poly` forbids `bnd` from
  carrying the `N²` that a max over `L²` loops costs, whereas here the `N^{εp}` of `moment` is
  a `≺`-loss that absorbs any fixed power of `N` at large enough order;
* the field `cont` is **gone**: `modulus` implies it (`continuousOn_of_modulus`).

**Quantifier order in `moment`** (the failure mode of T145): `δ` is fixed first, then `ε`,
then the order `p`, and only then `N → ∞`.  This is `RBM.Gauss.MomentDom`'s order — `ε` may be
taken as small as one likes *for each fixed `p`* — and it is *not* `∀ p ∀ N`.

**The absolute value in `moment`** is redundant (`cutTrunc` of a nonnegative argument is
nonnegative, `cutTrunc_nonneg`); it is written so that `RBM.Gauss.meas_gt_le_of_moment` applies
verbatim.

**Why this is not fiat.**  The data fields are `δ₀`, `mesh`, `Kmod`, `γ`, `Ccard`, and all five
are *constrained*: `mesh_fine` forces the mesh to be fine (large `mesh`), `card_le` forces it
to be coarse (small `mesh`), and the two together are a genuine constraint — `sat_mesh_card`
exhibits a solution with `mesh_fine` at equality.  `moment` cannot be satisfied by taking
anything large: the bound on its right is `Θ_N^{2p}` and `Θ` is the *conclusion*'s control, so
weakening `moment` weakens the conclusion by exactly as much. -/
structure CutHyp (P : Measure Ω) (J : ℕ → ℝ → Ω → ℝ) (s t Θ : ℕ → ℝ) where
  /-- The window is non-degenerate. -/
  window : ∀ N, s N ≤ t N
  /-- The range `0 < δ ≤ δ₀` of bootstrap margins, as in `RBM.Step2PP.BootPP.δ₀`. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  Θ_pos : ∀ N, 0 < Θ N
  /-- The state functional is nonnegative. -/
  J_nonneg : ∀ N u ω, 0 ≤ J N u ω
  meas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => J N u ω) P
  /-- The mesh of the net of (5.46). -/
  mesh : ℕ → ℝ
  mesh_pos : ∀ N, 0 < mesh N
  /-- The exponent of the deterministic modulus of continuity. -/
  Kmod : ℝ
  /-- Its Hölder exponent (`1/2` for the flow `H_u = √u X`, `RBM.Gauss.abs_sqrt_sub_sqrt_le`). -/
  γ : ℝ
  γ_pos : 0 < γ
  /-- The deterministic modulus of continuity, valid for **every** `ω`. -/
  modulus : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    |J N v ω - J N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ
  /-- The net is fine enough that one mesh of displacement costs at most `Θ_N`. -/
  mesh_fine : ∀ N : ℕ, (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ N
  /-- The exponent of the net's cardinality. -/
  Ccard : ℝ
  /-- The net is polynomially large, so the union bound is a `≺`-loss. -/
  card_le : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard
  /-- **The truncated one-step moment bound at the net points.**  The truncation level is the
  a priori threshold `N^{2δ}Θ_N` of the bootstrap, and the control is `Θ_N` itself. -/
  moment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ netFinset s t mesh N,
      ∫ ω, |cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N) (J N ws ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p))

namespace CutHyp

variable {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t Θ : ℕ → ℝ}

/-- The paths are continuous, by the modulus — so no separate `cont` field. -/
theorem continuousOn (H : CutHyp P J s t Θ) (N : ℕ) (ω : Ω) :
    ContinuousOn (fun u => J N u ω) (Set.Icc (s N) (t N)) :=
  continuousOn_of_modulus H.γ_pos (H.modulus N ω)

/-- **`hclose` of `RBM.Step2MomentStep.bootPP_of_net`, from the modulus.**  Every time of the
window has a net point to its left at which the functional is smaller by at most `Θ_N`. -/
theorem hclose (H : CutHyp P J s t Θ) (N : ℕ) (ω : Ω) :
    ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      ws ∈ Set.Icc (s N) v ∧ J N v ω ≤ J N ws ω + Θ N := by
  intro v hv
  obtain ⟨ws, hwsF, hwsIcc, hgap⟩ := exists_mem_netFinset (t := t) (H.mesh_pos N) hv
  refine ⟨ws, Finset.mem_coe.2 hwsF, hwsIcc, ?_⟩
  have hwsb : ws ∈ Set.Icc (s N) (t N) := ⟨hwsIcc.1, hwsIcc.2.trans hv.2⟩
  have habs : |v - ws| ≤ 1 / H.mesh N := by
    rw [abs_of_nonneg (by linarith [hwsIcc.2])]
    exact hgap
  have h1 : |v - ws| ^ H.γ ≤ (1 / H.mesh N) ^ H.γ :=
    Real.rpow_le_rpow (abs_nonneg _) habs H.γ_pos.le
  have hK : (0 : ℝ) ≤ (N : ℝ) ^ H.Kmod := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (N : ℝ) ^ H.Kmod * |v - ws| ^ H.γ ≤ Θ N :=
    le_trans (mul_le_mul_of_nonneg_left h1 hK) (H.mesh_fine N)
  have h3 := (le_abs_self _).trans ((H.modulus N ω v hv ws hwsb).trans h2)
  linarith

end CutHyp

end Interface

/-! ### 5. De-truncation at the probability level: the fixed-time input `hev` -/

section Hev

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t Θ : ℕ → ℝ}

/-- **The heart of the truncated route.**

The truncated moment bound at the net points, together with the coincidence of the truncated
and the untruncated functional on the prefix event, gives *exactly* the fixed-time hypothesis
`hev` of `RBM.Step2MomentStep.bootPP_of_net`: at each net point, conditional on the a priori
bound `N^{2δ}Θ` holding on the whole prefix, the improved bound `(N^δ - 1)Θ` holds with high
probability.

**Where the de-truncation happens, and why it is free.**  The prefix hypothesis applied at
`u = ws` says `J_{ws} ≤ N^{2δ}Θ_N`, which is the truncation level; so
`cutTrunc (N^{2δ}Θ_N) J_{ws} = J_{ws}` there (`cutTrunc_eq_of_prefix`) and the Markov estimate
for the truncated functional *is* a Markov estimate for the untruncated one **on that event**.
No remainder is produced.  Compare `RBM.Step2MomentStep.detrunc_remainder_ge_thr`: doing the
same inside the moment leaves a remainder at least as large as the threshold, removable only by
multiplying the order by `(K + δ)/δ`.

**The cost is one union bound over the net**, `RBM.MomentDuhamelCut.netFinset_card_le`, which
is `N^{Ccard}` — a fixed power of `N`, absorbed by taking the order `p` large.  This is the
step that `RBM.Step2Moment.MomentHyp.step` cannot afford: `bnd_poly` pins `bnd` to `N^{o(1)}`
at *every* order (`RBM.Step2MomentStep.bnd_poly_excludes_pow`). -/
theorem hev_of_cutHyp [IsProbabilityMeasure P] (H : CutHyp P J s t Θ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ H.δ₀) :
    HighProb P fun N => {ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ),
      ws ∈ Set.Icc (s N) (t N) →
      (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
        J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
  intro D hD
  -- the order: `δ p / 2` has to beat the net's cardinality exponent, the target decay, and `C`
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + H.Ccard + 1) * 2 / δ)
  have hpδ : D + H.Ccard + 1 ≤ δ / 2 * p := by
    rw [div_le_iff₀ hδ0] at hp
    nlinarith
  have hexp : 0 < δ / 2 * (p : ℝ) - H.Ccard - D := by linarith
  obtain ⟨C, hC0, hCN⟩ := H.moment δ hδ0 hδ (δ / 2) (by positivity) p
  filter_upwards [hCN, H.card_le, eventually_ge_atTop 2, eventually_le_rpow C hexp,
    eventually_le_rpow (2 : ℝ) (half_pos hδ0)] with N hmomN hcardN hN2 hCle hhalf
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hΘ0 := H.Θ_pos N
  set a : ℝ := (N : ℝ) ^ (δ / 2) with ha_def
  -- `N^δ - 1 ≥ N^{δ/2} ≥ 2`, so the improved level is positive
  have haa : (N : ℝ) ^ δ = a * a := by
    rw [ha_def, ← Real.rpow_add hN0]; congr 1; ring
  have hda : a ≤ (N : ℝ) ^ δ - 1 := by rw [haa]; nlinarith
  have hlev0 : (0 : ℝ) < ((N : ℝ) ^ δ - 1) * Θ N := by
    have : (0 : ℝ) < (N : ℝ) ^ δ - 1 := by linarith
    positivity
  have hθ0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * Θ N := by
    have : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hN0 _
    positivity
  -- Markov at a single net point
  have hpoint : ∀ ws ∈ netFinset s t H.mesh N,
      P {ω | ((N : ℝ) ^ δ - 1) * Θ N <
          cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N) (J N ws ω)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard) := by
    intro ws hws
    have hint := integrable_cutTrunc_pow (P := P) hθ0 (fun ω => H.J_nonneg N ws ω)
      (H.meas N ws) (2 * p)
    refine (Gauss.meas_gt_le_of_moment P hlev0 hint (hmomN ws hws)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    -- the exponent bookkeeping
    have hQ : (0 : ℝ) < Θ N ^ (2 * p) := by positivity
    have hR : (N : ℝ) ^ (δ * (p : ℝ)) ≤ ((N : ℝ) ^ δ - 1) ^ (2 * p) := by
      have h2 : a ^ (2 * p) = (N : ℝ) ^ (δ * (p : ℝ)) := by
        rw [ha_def, ← Real.rpow_natCast ((N : ℝ) ^ (δ / 2)) (2 * p), ← Real.rpow_mul hN0.le]
        congr 1; push_cast; ring
      rw [← h2]
      exact pow_le_pow_left₀ (by positivity) hda (2 * p)
    have hkey : C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) ≤ (N : ℝ) ^ (δ * (p : ℝ) - D - H.Ccard) := by
      calc C * (N : ℝ) ^ (δ / 2 * (p : ℝ))
          ≤ (N : ℝ) ^ (δ / 2 * (p : ℝ) - H.Ccard - D) * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
            gcongr
        _ = (N : ℝ) ^ (δ * (p : ℝ) - D - H.Ccard) := by
            rw [← Real.rpow_add hN0]; congr 1; ring
    rw [div_le_iff₀ (by positivity)]
    have hexpand : (((N : ℝ) ^ δ - 1) * Θ N) ^ (2 * p)
        = ((N : ℝ) ^ δ - 1) ^ (2 * p) * Θ N ^ (2 * p) := mul_pow _ _ _
    have hsplit : (N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard = (N : ℝ) ^ (-D - H.Ccard) := by
      rw [Real.rpow_sub hN0]
    rw [hexpand, hsplit]
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-D - H.Ccard) := Real.rpow_pos_of_pos hN0 _
    calc C * ((N : ℝ) ^ (δ / 2 * (p : ℝ)) * Θ N ^ (2 * p))
        = (C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) * Θ N ^ (2 * p) := by ring
      _ ≤ (N : ℝ) ^ (δ * (p : ℝ) - D - H.Ccard) * Θ N ^ (2 * p) := by
          exact mul_le_mul_of_nonneg_right hkey hQ.le
      _ = (N : ℝ) ^ (-D - H.Ccard) * (N : ℝ) ^ (δ * (p : ℝ)) * Θ N ^ (2 * p) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
      _ ≤ (N : ℝ) ^ (-D - H.Ccard) * ((N : ℝ) ^ δ - 1) ^ (2 * p) * Θ N ^ (2 * p) := by
          gcongr
      _ = (N : ℝ) ^ (-D - H.Ccard) * (((N : ℝ) ^ δ - 1) ^ (2 * p) * Θ N ^ (2 * p)) := by ring
  -- the failure event sits inside the union of the Markov events
  have hsub : ({ω | ∀ ws ∈ (↑(netFinset s t H.mesh N) : Set ℝ), ws ∈ Set.Icc (s N) (t N) →
        (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
          J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N})ᶜ
      ⊆ ⋃ ws ∈ netFinset s t H.mesh N,
          {ω | ((N : ℝ) ^ δ - 1) * Θ N <
            cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N) (J N ws ω)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_coe, not_forall, not_le] at hω
    obtain ⟨ws, hwsF, hwsIcc, hpre, hgt⟩ := hω
    refine Set.mem_biUnion hwsF ?_
    have heq : cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N) (J N ws ω) = J N ws ω :=
      cutTrunc_eq_of_prefix (J := fun u => J N u ω) hθ0 hwsIcc.1 hpre
    simpa only [Set.mem_ofPred_eq, heq] using hgt
  -- the union bound
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hpoint) ?_
  have hr0 : (0 : ℝ) ≤ (N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard := by positivity
  have hcard : ((netFinset s t H.mesh N).card : ℝ) ≤ (N : ℝ) ^ H.Ccard :=
    (netFinset_card_le (H.window N) (H.mesh_pos N)).trans hcardN
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((netFinset s t H.mesh N).card : ℝ) * ((N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard)
      ≤ (N : ℝ) ^ H.Ccard * ((N : ℝ) ^ (-D) / (N : ℝ) ^ H.Ccard) :=
        mul_le_mul_of_nonneg_right hcard hr0
    _ = (N : ℝ) ^ (-D) := by
        field_simp

end Hev

/-! ### 6. The producers: the pathwise bootstrap, `BootPP`, and `MomentHypCut` -/

section Producers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {s t : ℕ → ℝ}

/-- **The pathwise bootstrap, with the loop functional abstracted out.**

This is `RBM.Step2PP.xiLK_two_le` for a general nonnegative path family: the net input `hev`
(conditional on the prefix, at the net points only) plus the deterministic closeness `hclose`
give the continuum improvement, and continuous induction
(`RBM.le_of_bootstrap_prefix`) turns it into `J ≺ Θ` uniformly in `u ∈ [s, t]`.

`RBM.Step2MomentStep.bootPP_step_of_net` is the `Ξ^{(L-K)}_{·,2}` instance of the first half;
it cannot be reused here because it is phrased for that functional, and
`RBM1D/Hierarchy/Step2MomentStep.lean` is frozen. -/
theorem stochDom_of_net [IsProbabilityMeasure P] {J : ℕ → ℝ → Ω → ℝ} {Θ : ℕ → ℝ}
    {S : ℕ → Set ℝ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hst : ∀ N, s N ≤ t N)
    (hΘ0 : ∀ N, 0 < Θ N) (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hcont : ∀ (N : ℕ) (ω : Ω), ContinuousOn (fun u => J N u ω) (Set.Icc (s N) (t N)))
    (hclose : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∃ ws ∈ S N,
      ws ∈ Set.Icc (s N) v ∧ J N v ω ≤ J N ws ω + Θ N)
    (hev : ∀ δ, 0 < δ → δ ≤ δ₀ → HighProb P fun N => {ω | ∀ ws ∈ S N,
      ws ∈ Set.Icc (s N) (t N) →
      (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
        J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N})
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) := by
  intro τ hτ D hD
  set δ : ℝ := min (τ / 2) δ₀ with hδdef
  have hδ : (0 : ℝ) < δ := lt_min (half_pos hτ) hδ₀
  have hδτ : δ ≤ τ / 2 := min_le_left _ _
  filter_upwards [hev δ hδ (min_le_right _ _) (D + 1) (by linarith),
    hinit δ hδ (D + 1) (by linarith), hΘ1, eventually_ge_atTop 2] with N hA hB htgt hN2
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hT0 : 0 < Θ N := hΘ0 N
  have hhalf : (N : ℝ) ^ δ < (N : ℝ) ^ τ :=
    (Real.rpow_lt_rpow_left_iff hN1).2 (by linarith)
  have hsub : badSet (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N) τ N ⊆
    ({ω | ∀ ws ∈ S N, ws ∈ Set.Icc (s N) (t N) →
      (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
        J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N})ᶜ ∪
    badSet (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ)) δ N := by
    rintro ω ⟨u, hu⟩
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨hev0, hbad⟩ := hno
    have hevω : ω ∈ {ω | ∀ ws ∈ S N, ws ∈ Set.Icc (s N) (t N) →
        (∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
          J N ws ω ≤ ((N : ℝ) ^ δ - 1) * Θ N} := by
      by_contra hc
      exact hev0 hc
    have hs2 : J N (s N) ω ≤ (N : ℝ) ^ δ * 1 := by
      by_contra hc
      exact hbad ⟨(), not_le.1 hc⟩
    -- the continuum improvement, from the net point to its left
    have hstep : ∀ v ∈ Set.Icc (s N) (t N),
        (∀ u ∈ Set.Icc (s N) v, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N) →
          J N v ω ≤ (N : ℝ) ^ δ * Θ N := by
      intro v hv hprefix
      obtain ⟨ws, hwsS, hwsIcc, hwY⟩ := hclose N ω v hv
      have hwsb : ws ∈ Set.Icc (s N) (t N) := ⟨hwsIcc.1, hwsIcc.2.trans hv.2⟩
      have hpre : ∀ u ∈ Set.Icc (s N) ws, J N u ω ≤ (N : ℝ) ^ (2 * δ) * Θ N :=
        fun u hu => hprefix u ⟨hu.1, hu.2.trans hwsIcc.2⟩
      have := hevω ws hwsS hwsb hpre
      calc J N v ω ≤ J N ws ω + Θ N := hwY
        _ ≤ ((N : ℝ) ^ δ - 1) * Θ N + Θ N := by linarith
        _ = (N : ℝ) ^ δ * Θ N := by ring
    have hkey : ∀ v ∈ Set.Icc (s N) (t N), J N v ω ≤ (N : ℝ) ^ δ * Θ N := by
      refine le_of_bootstrap_prefix (C := (N : ℝ) ^ (2 * δ) * Θ N) (hst N) (hcont N ω) ?_ ?_ ?_
      · exact mul_lt_mul_of_pos_right
          ((Real.rpow_lt_rpow_left_iff hN1).2 (by linarith)) hT0
      · calc J N (s N) ω ≤ (N : ℝ) ^ δ * 1 := hs2
          _ ≤ (N : ℝ) ^ δ * Θ N := by
              have : (0 : ℝ) ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (by linarith) _
              nlinarith
      · exact hstep
    have hle := hkey (u : ℝ) u.2
    have hmono : (N : ℝ) ^ δ * Θ N ≤ (N : ℝ) ^ τ * Θ N :=
      mul_le_mul_of_nonneg_right hhalf.le hT0.le
    exact absurd hu (not_lt.2 (hle.trans hmono))
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  refine le_trans (add_le_add hA hB) ?_
  rw [← ENNReal.ofReal_add hp hp]
  refine ENNReal.ofReal_le_ofReal ?_
  have hkey : (2 : ℝ) * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
    have hN0 : (0 : ℝ) < N := by linarith
    have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hN2'
    calc (2 : ℝ) * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(D + 1)) := by
          exact mul_le_mul_of_nonneg_right h2 hp
      _ = (N : ℝ) ^ (-D) := by rw [← Real.rpow_add hN0]; congr 1; ring
  linarith

variable {B : Band Ω} {E : ℝ}

/-- **`J ≺ Θ` from the truncated interface**: `stochDom_of_net` with every deterministic
input read off `CutHyp`.  The only hypotheses left are `Θ ≥ 1` (so that the initial `≺ 1`
implies `≺ Θ`) and the initial bound at `u = s_N`, which is (2.68)/(2.69). -/
theorem stochDom_of_cutHyp [IsProbabilityMeasure P] {J : ℕ → ℝ → Ω → ℝ} {Θ : ℕ → ℝ}
    (H : CutHyp P J s t Θ) (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) :=
  stochDom_of_net H.δ₀_pos H.window H.Θ_pos hΘ1 H.continuousOn H.hclose
    (fun _δ hδ0 hδ => hev_of_cutHyp H hδ0 hδ) hinit

/-- **`RBM.Step2PP.BootPP` from the truncated interface** — the `(+,+)` bootstrap structure,
whose only non-routine field `step` is discharged by `hev_of_cutHyp` through T132c's
`RBM.Step2MomentStep.bootPP_of_net`.

This is the producer T176's probe P1 lists as missing for `hΘ`. -/
noncomputable def bootPP_of_cutHyp (X : Sample B) {Θ : ℕ → ℝ}
    (H : CutHyp B.P (fun N u ω => X.xiLK E N u ω 2) s t Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N) :
    Step2PP.BootPP X E s t :=
  letI := B.isProbabilityMeasure
  Step2MomentStep.bootPP_of_net X H.Θ_pos hΘ1 H.continuousOn H.δ₀_pos H.hclose
    (fun _δ hδ0 hδ => hev_of_cutHyp H hδ0 hδ)

/-- **`hΘ` itself**: `Ξ^{(L-K)}_{u,2} ≺ Θ` uniformly in `u ∈ [s, t]`, in exactly the shape the
consumers of `RBM.Step2PP.xiLK_two_le` want. -/
theorem xiLK_two_stochDom_of_cutHyp (X : Sample B) {Θ : ℕ → ℝ}
    (H : CutHyp B.P (fun N u ω => X.xiLK E N u ω 2) s t Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom B.P (fun N (_ : Unit) ω => X.xiLK E N (s N) ω 2)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N) :=
  Step2PP.xiLK_two_le X (bootPP_of_cutHyp X H hΘ1) H.window hinit

/-- **`MomentHypCut`: the replacement for `RBM.Step2Moment.MomentHyp`.**

`MomentHyp` is frozen and unprovable in that shape (T132c, §9 of
`RBM1D/Hierarchy/Step2MomentStep.lean`).  This is what takes its place: a truncated interface
for the *normalized* `J*` of (5.29) — normalized so that the threshold is the constant `1`,
exactly as `RBM.Step2Moment.jSnorm` is — plus the initial bound of (2.69).

Everything `MomentHyp` asks for and this does not: `env`/`env_le` (the envelope is `2Θ`, a
theorem), `cont` (implied by `modulus`), `bnd`/`thr`/`bnd_lt_thr`/`bnd_poly` (the `N^{εp}` of
`CutHyp.moment` replaces them), and `step` itself. -/
structure MomentHypCut (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- The truncated moment Duhamel for the normalized `J*_{u,D}`, with threshold `1`. -/
  cut : CutHyp B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t (fun _ => 1)
  /-- **(2.69)**: the initial bound `J*_{s,D} ≺ 1`. -/
  init : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
    (fun _ _ _ => (1 : ℝ))

/-- `J*_{u,D}/(η_s/η_u)^4 ≺ 1`, uniformly in `u ∈ [s, t]` — the conclusion of
`RBM.Step2Moment.stochDom_jSnorm`, from the truncated interface. -/
theorem stochDom_jSnorm_cut {X : Sample B} {D : ℝ} (Hy : MomentHypCut X E s t D) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2Moment.jSnorm X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  have := B.isProbabilityMeasure
  exact stochDom_of_cutHyp Hy.cut (Filter.Eventually.of_forall fun _ => le_rfl) Hy.init

/-- **(5.47)**: `J*_{u,D} ≺ (η_s/η_u)^4`, uniformly in `u ∈ [s, t]`, in *exactly* the
conclusion of `RBM.Step2Moment.jS_stochDom` — but from `MomentHypCut`, whose fields are not
the unprovable `RBM.Step2Moment.MomentHyp.step`.

The last step is the same de-normalization as there; the content is `stochDom_jSnorm_cut`. -/
theorem jS_stochDom_cut {X : Sample B} {D : ℝ} (Hy : MomentHypCut X E s t D) (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 4) := by
  refine StochDom.of_subset (stochDom_jSnorm_cut Hy) fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N (u : ℝ) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs1 (u.2.2.trans_lt (ht1 N))) 4
  show (N : ℝ) ^ τ * 1 < Step2.jS X E D N (u : ℝ) ω / Step2Moment.ratR E s N (u : ℝ) ^ 4
  rw [mul_one, lt_div_iff₀ hR]
  exact hu

end Producers

/-! ### 7. Satisfiability witnesses (compiled) -/

section Sat

/-- **`hev`'s improved level is positive for large `N`.**  `(N^δ - 1)Θ_N` is negative for small
`N`, where `hev` would be *false* rather than vacuous (the functional is nonnegative); it is
positive from `N^δ ≥ 2` on, which is where `HighProb`'s `∀ᶠ N` puts it.  So the conclusion of
`hev_of_cutHyp` has content. -/
theorem sat_hev_target_pos {δ : ℝ} (hδ : 0 < δ) {Θ : ℕ → ℝ} (hΘ : ∀ N, 0 < Θ N) :
    ∀ᶠ N : ℕ in atTop, 0 < ((N : ℝ) ^ δ - 1) * Θ N := by
  filter_upwards [eventually_le_rpow (2 : ℝ) hδ] with N hN
  have := hΘ N
  nlinarith

/-- **The two net conditions are jointly satisfiable, and `mesh_fine` is tight.**

`CutHyp.mesh_fine` wants the mesh *fine* (`m_N ≥ (N^{Kmod}/Θ_N)^{1/γ}`) and `CutHyp.card_le`
wants it *coarse* (`(t_N - s_N)m_N + 2 ≤ N^{Ccard}`); a pair of hypotheses pulling in opposite
directions is exactly the shape in which one can be unsatisfiable, so it is checked here at the
parameters of the flow: `γ = 1/2` (`RBM.Gauss.abs_sqrt_sub_sqrt_le` for `H_u = √u X`),
`Kmod = 1`, `Θ ≡ 1`, `t - s = 1` and the mesh `m_N = N²`, for which **`mesh_fine` holds with
equality** and `card_le` holds with `Ccard = 3`. -/
theorem sat_mesh_card {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ (1 : ℝ) * (1 / (N : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 1 ∧
      ((1 : ℝ) - 0) * (N : ℝ) ^ (2 : ℝ) + 2 ≤ (N : ℝ) ^ (3 : ℝ) := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  constructor
  · have h1 : (1 / (N : ℝ) ^ (2 : ℝ)) = (N : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hN0.le, one_div]
    rw [h1, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    norm_num
  · have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (N : ℝ) 2]; norm_num
    have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast (N : ℝ) 3]; norm_num
    rw [h2, h3]; nlinarith

/-- **The linearization has content on the gap.**  At `J = 3Θ/2`, where T175's profile takes
the value `χ(3/2) = 1/2` (`RBM.Cutoff.cutChi_three_halves`), *both* sides of `cut_sq_le` are
nonzero — `(9/8)Θ²` and `(3/2)Θ²` — so the lemma is not the trivial `0 ≤ 0` it degenerates to
off the support. -/
theorem sat_cut_sq_nonvacuous {Θ : ℝ} (hΘ : 0 < Θ) :
    Cutoff.cutChi ((3 * Θ / 2) / Θ) * (3 * Θ / 2) ^ 2 = 9 / 8 * Θ ^ 2 ∧
      2 * Θ * cutTrunc Θ (3 * Θ / 2) = 3 / 2 * Θ ^ 2 := by
  have h : (3 * Θ / 2) / Θ = 3 / 2 := by field_simp
  refine ⟨?_, ?_⟩
  · rw [h, Cutoff.cutChi_three_halves]; ring
  · rw [cutTrunc, h, Cutoff.cutChi_three_halves]; ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The degenerate order `p = 0` of `CutHyp.moment` is a constraint, not a contradiction.**

At `p = 0` both sides degenerate: on a probability measure the integral is `1`, and the bound
is `C · (N⁰ · Θ⁰) = C`, so the field asks for `1 ≤ C` there — satisfiable, and never used:
`hev_of_cutHyp` picks `p ≥ 2(D + Ccard + 1)/δ`, and `CutHyp.card_le` forces `Ccard > 0`
(its left side is at least `2`), so that order is `≥ 1`.

This is checked because it is the exact shape of the trap T191 hit, where `cMD p = 2p - 1`
goes *negative* at `p = 0`.  Nothing here does. -/
theorem sat_moment_at_zero (P : Measure Ω) [IsProbabilityMeasure P] {θ : ℝ} {Y : Ω → ℝ} :
    ∫ ω, |cutTrunc θ (Y ω)| ^ (2 * 0) ∂P = 1 := by
  simp

/-- **A compiled `CutHyp`, at the critical scale `J ≡ Θ`.**

This is the satisfiability check the spec asks for, and it is deliberately *not* taken at
`J ≡ 0`: the functional sits exactly at the level `Θ` that the bootstrap propagates, so the
interface is not secretly asking for `J ≪ Θ`.  The truncation is genuinely at work — the
truncation level is `N^{2δ}Θ_N ≥ Θ_N = J`, so `cutTrunc` is the identity here
(`cutTrunc_eq_self`), which is the regime the whole scheme lives in.

The window `[0, 1]` is non-degenerate, so `TimeIcc` is inhabited and the conclusion of
`stochDom_of_cutHyp` quantifies over something (`sat_stochDom_of_cutHyp`). -/
noncomputable def satCutHyp (P : Measure Ω) [IsProbabilityMeasure P] :
    CutHyp P (fun _ _ _ => (1 : ℝ)) (fun _ => 0) (fun _ => 1) (fun _ => 1) where
  window := fun _ => zero_le_one
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  J_nonneg := fun _ _ _ => zero_le_one
  meas := fun _ _ => aestronglyMeasurable_const
  mesh := fun N => ((N : ℝ) + 1) ^ (2 : ℝ)
  mesh_pos := fun N => Real.rpow_pos_of_pos (by positivity) _
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := fun N _ v _ w _ => by
    simp only [sub_self, abs_zero]
    positivity
  mesh_fine := fun N => by
    have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : (1 / ((N : ℝ) + 1) ^ (2 : ℝ)) = ((N : ℝ) + 1) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg ha.le, one_div]
    have h2 : (-(2 : ℝ)) * ((1 : ℝ) / 2) = -1 := by norm_num
    rw [h1, ← Real.rpow_mul ha.le, h2, Real.rpow_neg ha.le, Real.rpow_one, Real.rpow_one,
      ← div_eq_mul_inv, div_le_one ha]
    linarith
  Ccard := 3
  card_le := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h2 : ((N : ℝ) + 1) ^ (2 : ℝ) = ((N : ℝ) + 1) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((N : ℝ) + 1) 2]; norm_num
    have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast (N : ℝ) 3]; norm_num
    rw [h2, h3]
    nlinarith
  moment := by
    intro δ hδ0 _ ε _ p
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN _ _
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlev : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * 1 := by
      rw [mul_one]
      exact Real.one_le_rpow hN1 (by positivity)
    have hlev0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * 1 := by linarith
    rw [cutTrunc_eq_self hlev0 hlev]
    have hεp : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1 (by positivity)
    simp only [abs_one, one_pow, one_mul]
    rw [MeasureTheory.integral_const]
    simpa using hεp

/-- The initial bound of `stochDom_of_cutHyp` for the witness `satCutHyp`: `1 ≺ 1`. -/
theorem sat_init (P : Measure Ω) :
    StochDom P (fun (_ : ℕ) (_ : Unit) (_ : Ω) => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) := by
  intro τ hτ D hD
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsub : badSet (fun (_ : ℕ) (_ : Unit) (_ : Ω) => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) τ N
      ⊆ (∅ : Set Ω) := by
    rintro ω ⟨_, hu⟩
    exact absurd hu (not_lt.2 (by
      rw [mul_one]
      exact Real.one_le_rpow hN1 hτ.le))
  calc P (badSet (fun (_ : ℕ) (_ : Unit) (_ : Ω) => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) τ N)
      ≤ P (∅ : Set Ω) := measure_mono hsub
    _ = 0 := measure_empty
    _ ≤ _ := bot_le

/-- **The whole chain is non-vacuous**: `satCutHyp` really does feed `stochDom_of_cutHyp`, and
the conclusion is a `≺` over a non-degenerate window.  This is the compiled end-to-end check —
interface in, `RBM.StochDom` out — for the truncated route. -/
theorem sat_stochDom_of_cutHyp (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (_ : TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) N) (_ : Ω) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_cutHyp (satCutHyp P) (Filter.Eventually.of_forall fun _ => le_rfl) (sat_init P)

end Sat

/-! ### 8. The downstream consumers, with `MomentHyp` removed -/

section Consumers

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **(2.76) along the truncated route**, in exactly the shape of the field
`RBM.Steps.aprioriDecay`.

This is `RBM.Step2Moment.aprioriDecay` verbatim, with `RBM.Step2Moment.MomentHyp` replaced by
`MomentHypCut`; the passage from (5.47) to (2.76) is route-independent
(`RBM.Step2Moment.aprioriDecay_of_jS`) and is reused unchanged. -/
theorem aprioriDecay_cut (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCut X E s t D) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  Step2Moment.aprioriDecay_of_jS X hE hs0 hst ht1 hc0 hreg
    fun D hD => jS_stochDom_cut (Hy D hD) hE hst ht1

/-- **Step 2 of Theorem 2.21 along the truncated route**: (2.75) and (2.76), in exactly the
shapes of the fields `RBM.Steps.localLaw` and `RBM.Steps.aprioriDecay`.

This is the acceptance criterion of the ticket: the conclusion is *literally* that of
`RBM.Step2Moment.step2`, and the hypothesis `∀ D ≥ 60, MomentHyp X E s t D` — whose field
`step` T132c proved unprovable in its frozen shape — has been replaced by
`∀ D ≥ 60, MomentHypCut X E s t D`.  Everything else in the chain is unchanged and shared with
the untruncated route. -/
theorem step2_cut {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCut X E s t D) (h1 : Step1.Hyp X E s t)
    (hB : BoundsCore X E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : |E| < 2 := by linarith
  have h276 := aprioriDecay_cut X Hy hE hs0 hst ht1 hc0 hreg
  have hc272 := Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := B) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have h274 := Step1.weakLaw X hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hreg' h1
  exact ⟨Step2.localLaw X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg h276 h274 h1.lemma41, h276⟩

end Consumers

end MomentDuhamelCut

end RBM




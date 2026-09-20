/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Domination
import RBM1D.Loop.Split
import RBM1D.Loop.Ward
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The reverse bridge `≺ ⟹ moments`, and the deterministic envelope of a loop

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.1 (i) and (5.2).

`RBM1D/Gauss/Domination.lean` has the **forward** bridge of the moment route:
`RBM.Gauss.MomentDom ⟹ RBM.StochDom` by Markov.  This file has the **reverse** one, so that an
interface of the shape "`≺` in, `≺` out" can be *proved* without reshaping its signature:
lift the `≺` hypothesis to moments here, run the generator identity and the Grönwall argument on
moments, and come back down with `RBM.Gauss.stochDom_of_momentDom`.

## The reverse bridge

`≺` alone never implies a moment bound: the exceptional set has probability `≤ N^{-D}` but the
random variable is unconstrained there.  What closes the gap is a **deterministic envelope**: a
bound `|Y(N,u,ω)| ≤ Env(N)` valid for *every* `ω`, with `Env` of polynomial growth.  Then, for
fixed `ε > 0` and `p`, split the space at the threshold `N^{ε/2} Φ(N,u)`:

* on `{|Y| ≤ N^{ε/2} Φ}` the integrand `|Y|^{2p}` is at most `N^{εp} Φ^{2p}`;
* the complement has probability `≤ N^{-D'}` by Definition 2.1 (i), and there `|Y|^{2p}` is at
  most `Env(N)^{2p} ≤ N^{2pK}`.  Taking `D' := 2p(K + B) + 1`, where `N^{-B} ≤ Φ` is a
  (super-polynomially non-degenerate) lower bound on the control, the second piece is at most
  `N^{-2pB - 1} ≤ Φ^{2p} ≤ N^{εp} Φ^{2p}`.

The total is `(P(Ω) + 1) · N^{εp} Φ^{2p}`, which is `RBM.Gauss.MomentDom` with the **same**
quantifier order as `RBM1D/Gauss/Domination.lean` (`ε` outside `p`, constant `C = C(ε,p)`), so
the two bridges compose.

## The deterministic envelope

Along the flow `z_t = E + (1 - t) m^{(E)}` of (2.35) one has `Im z_t = η_t > 0` for `|E| < 2`,
`t < 1`, hence `‖G_t‖_op ≤ η_t⁻¹` on the **whole space** — not with high probability, but
pointwise in `ω`, because Hermiticity of `H` is a pointwise fact.  A loop is the trace of a
product of `G`'s and `E_a`'s (`RBM.gloop`), so (5.2) gives the pointwise bound
`|L_{t,σ,a}| ≤ η_t^{-n} W^{-n+1}` for every `n`-loop.  This is the reusable ingredient: every
dominated-convergence hypothesis and every envelope downstream is an instance of it.

## Main results

* `RBM.Gauss.momentDom_of_stochDom` — **the reverse bridge**: `≺` together with a deterministic
  envelope of polynomial growth gives `RBM.Gauss.MomentDom`.
* `RBM.Gauss.momentDom_of_stochDom_of_nonneg`, `RBM.Gauss.momentDom_of_normStochDom` — the two
  shapes in which the hypothesis actually occurs (`bdg` / `bdgQ` dominate a `‖·‖`).
* `RBM.Gauss.norm_green_zt_le` — `‖G_t‖_op ≤ η_t⁻¹` on the whole space.
* `RBM.Gauss.norm_gloop_le_det` — **the deterministic envelope of a loop**, `(5.2)` along the
  flow: `|L_{t,σ,a}| ≤ η_t^{-n} W^{-n+1}` for every `ω`.
* `RBM.Gauss.loopMax_le_det`, `RBM.Gauss.loopXi_le_det`, `RBM.Gauss.norm_gloop_sub_le_det` — the
  same envelope for `max_{σ,a}|L|`, for `Ξ^{(L)}` and for a difference `L - K` (hence for
  `L - K` and, via `RBM.jStar_le`, for `J*`).
* `RBM.Gauss.det_envelope_le_rpow` — the envelope is of polynomial growth as soon as
  `N^{-c} ≤ η_t` and `1 ≤ W`; this is the `Env` input of `momentDom_of_stochDom`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-! ### The reverse bridge: `≺` + deterministic envelope ⟹ moments -/

section Reverse

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **The reverse bridge.**

Let `Y(N,u)` be dominated by a positive deterministic control `Φ(N,u)` in the sense of
Definition 2.1 (i), `|Y| ≺ Φ`, and assume

* `Φ` is not super-polynomially small: `N^{-B} ≤ Φ(N,u)` eventually, uniformly in `u`;
* `Y` has a **deterministic envelope**: `|Y(N,u,ω)| ≤ Env(N)` for *every* `ω`, with `Env ≥ 0`
  of polynomial growth `Env(N) ≤ N^{Kenv}` eventually.

Then all moments of `Y` are bounded relative to `Φ` in the sense of `RBM.Gauss.MomentDom`, with
the quantifier order of `RBM1D/Gauss/Domination.lean` (`ε` outside `p`).

Together with `RBM.Gauss.stochDom_of_momentDom` this makes the round trip
`≺ → moments → (generator identity, Grönwall) → moments → ≺` available without changing the
shape of any `≺`-valued interface. -/
theorem momentDom_of_stochDom {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), |Y N u ω| ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u)) :
    MomentDom P Y Φ := by
  intro ε hε p
  have hPuniv : (0 : ℝ) ≤ P.real Set.univ := measureReal_nonneg
  refine ⟨P.real Set.univ + 1, by linarith, ?_⟩
  set τ : ℝ := ε / 2 with hτ_def
  have hτ : 0 < τ := half_pos hε
  set D' : ℝ := 2 * p * (Kenv + B) + 1 with hD'_def
  have hD'0 : 0 < D' := by
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hKB : (0 : ℝ) ≤ 2 * (p : ℝ) * (Kenv + B) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hD'_def]; linarith
  filter_upwards [hΦlow, hEnvpoly, hdom τ hτ D' hD'0, eventually_ge_atTop 1] with
    N hΦN hEN hbad hN1
  intro u
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- the threshold and the exceptional set for this single `u`
  set c : ℝ := (N : ℝ) ^ τ * Φ N u with hc_def
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos hNpos τ) (hΦ N u)
  set S : Set Ω := {ω | c < |Y N u ω|} with hS_def
  have habs : Measurable fun ω => |Y N u ω| := by
    simpa [Real.norm_eq_abs] using (hmeas N u).norm
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const habs
  have hSsub : S ⊆ badSet (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u) τ N := fun ω hω => ⟨u, hω⟩
  have hPS : P.real S ≤ (N : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc (P S).toReal ≤ (ENNReal.ofReal ((N : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hSsub).trans hbad)
      _ = (N : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)
  -- the pointwise split
  have hEnvpow : (0 : ℝ) ≤ Env N ^ (2 * p) := pow_nonneg (hEnv0 N) _
  have hcpow : (0 : ℝ) ≤ c ^ (2 * p) := pow_nonneg hc0.le _
  have hpt : ∀ ω, |Y N u ω| ^ (2 * p)
      ≤ c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 : |Y N u ω| ^ (2 * p) ≤ Env N ^ (2 * p) :=
        pow_le_pow_left₀ (abs_nonneg _) (henv N u ω) _
      linarith
    · rw [Set.indicator_of_notMem hω]
      have h1 : |Y N u ω| ≤ c := not_lt.1 hω
      have h2 : |Y N u ω| ^ (2 * p) ≤ c ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) h1 _
      linarith
  have hRHSint : Integrable
      (fun ω => c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hSmeas)
  have hle := integral_mono (hint p N u) hRHSint hpt
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hSmeas), integral_const,
    integral_indicator_const _ hSmeas, smul_eq_mul, smul_eq_mul] at hle
  -- the main part is exactly `N^{εp} Φ^{2p}`
  have hmain : c ^ (2 * p) = (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    rw [hc_def, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 2
    rw [hτ_def]
    push_cast
    ring
  -- the exceptional part is negligible
  have hΦpow : (N : ℝ) ^ (-(B * (2 * p))) ≤ Φ N u ^ (2 * p) := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) (hΦN u) (2 * p)
    refine le_trans (le_of_eq ?_) h
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-B)) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  have htail : P.real S * Env N ^ (2 * p) ≤ (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    have h1 : Env N ^ (2 * p) ≤ ((N : ℝ) ^ Kenv) ^ (2 * p) :=
      pow_le_pow_left₀ (hEnv0 N) hEN _
    have h2 : ((N : ℝ) ^ Kenv) ^ (2 * p) = (N : ℝ) ^ (Kenv * (2 * p)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ Kenv) (2 * p), ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    have hStep : P.real S * Env N ^ (2 * p) ≤ (N : ℝ) ^ (-D') * (N : ℝ) ^ (Kenv * (2 * p)) := by
      refine mul_le_mul hPS (h2 ▸ h1) hEnvpow (Real.rpow_nonneg hNpos.le _)
    have hExp : (N : ℝ) ^ (-D') * (N : ℝ) ^ (Kenv * (2 * p))
        = (N : ℝ) ^ (-(B * (2 * p)) + -1) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      rw [hD'_def]
      ring
    have hDrop : (N : ℝ) ^ (-(B * (2 * p)) + -1) ≤ (N : ℝ) ^ (-(B * (2 * p))) := by
      refine Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hεp : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow hNge1 (mul_nonneg hε.le (Nat.cast_nonneg p))
    have hΦ2p : (0 : ℝ) ≤ Φ N u ^ (2 * p) := pow_nonneg (hΦ N u).le _
    calc P.real S * Env N ^ (2 * p) ≤ (N : ℝ) ^ (-(B * (2 * p))) := by
          rw [hExp] at hStep; exact hStep.trans hDrop
      _ ≤ Φ N u ^ (2 * p) := hΦpow
      _ ≤ (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by nlinarith
  -- assemble
  have hmainpos : (0 : ℝ) ≤ (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (pow_nonneg (hΦ N u).le _)
  calc ∫ ω, |Y N u ω| ^ (2 * p) ∂P
      ≤ P.real Set.univ * c ^ (2 * p) + P.real S * Env N ^ (2 * p) := hle
    _ ≤ P.real Set.univ * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))
        + (N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
          rw [hmain]; linarith
    _ = (P.real Set.univ + 1) * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p)) := by ring

/-- **The reverse bridge for a non-negative family.**  This is the shape in which the hypothesis
actually occurs in the paper's interfaces (`bdg`, `bdgQ`, …): what is dominated is already
non-negative, so `|Y| = Y`. -/
theorem momentDom_of_stochDom_of_nonneg {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hY0 : ∀ N (u : U N) (ω : Ω), 0 ≤ Y N u ω)
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), Y N u ω ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P Y (fun N u _ => Φ N u)) :
    MomentDom P Y Φ := by
  have habs : (fun N (u : U N) (ω : Ω) => |Y N u ω|) = Y := by
    funext N u ω; exact abs_of_nonneg (hY0 N u ω)
  refine momentDom_of_stochDom hmeas hint hΦ hB hΦlow hEnv0 hKenv ?_ hEnvpoly ?_
  · intro N u ω; rw [abs_of_nonneg (hY0 N u ω)]; exact henv N u ω
  · rw [habs]; exact hdom

/-- **The reverse bridge for `RBM.NormStochDom`** (Definition 2.1 (iii)): `‖A‖ ≺ Φ` plus a
deterministic envelope for `‖A‖` gives moment bounds for `‖A‖`. -/
theorem momentDom_of_normStochDom {U : ℕ → Type*} {V : Type*} [NormedAddCommGroup V]
    {A : ∀ N, U N → Ω → V} {Φ : ∀ N, U N → ℝ} {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable fun ω => ‖A N u ω‖)
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |‖A N u ω‖| ^ (2 * p)) P)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), ‖A N u ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : NormStochDom P A (fun N u _ => Φ N u)) :
    MomentDom P (fun N u ω => ‖A N u ω‖) Φ :=
  momentDom_of_stochDom_of_nonneg (fun _ _ _ => norm_nonneg _) hmeas hint hΦ hB hΦlow hEnv0 hKenv
    henv hEnvpoly hdom

end Reverse

/-! ### The deterministic envelope of a loop -/

section Envelope

/-- `η_t = (1 - t) Im m^{(E)} > 0` in the bulk, for `t < 1`. -/
theorem etaT_pos_of_lt_one {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht : t < 1) : 0 < etaT E t := by
  have hm := mE_im_pos hE
  have ht' : (0 : ℝ) < 1 - t := by linarith
  simpa [etaT] using mul_pos ht' hm

/-- `|Im z_t| = η_t`. -/
theorem abs_im_zt (E : ℝ) {t : ℝ} (hE : |E| < 2) (ht : t < 1) : |(zt E t).im| = etaT E t := by
  rw [← etaT_eq_zt_im, abs_of_pos (etaT_pos_of_lt_one hE ht)]

open scoped Matrix.Norms.L2Operator in
/-- **`‖G_t‖_op ≤ η_t⁻¹` on the whole space.**  For `z_t = E + (1 - t) m^{(E)}` of (2.35) with
`|E| < 2` and `t < 1` one has `Im z_t = η_t > 0`, so the Green function of *any* Hermitian `H` is
bounded by `η_t⁻¹` — pointwise in `ω`, with no exceptional set.  This is the input of (5.2) and
the reason every dominated-convergence hypothesis downstream is a constant. -/
theorem norm_green_zt_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) :
    ‖green H (zt E t)‖ ≤ (etaT E t)⁻¹ := by
  have hη := etaT_pos_of_lt_one hE ht
  have him : (zt E t).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact hη.ne'
  simpa [abs_im_zt E hE ht] using norm_green_le hH him

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

/-- **The deterministic envelope of a loop**, i.e. (5.2) along the flow `z_t` of (2.35).

Every `n`-loop of *any* Hermitian `H` satisfies `|L_{t,σ,a}| ≤ η_t^{-n} W^{-n+1}`.  There is no
exceptional set and no probability here: a loop is the trace of a product of `n` Green functions
(each of operator norm `≤ η_t⁻¹`, `norm_green_zt_le`) and `n` block projections (each of
operator norm `≤ W⁻¹`, one of which is free under the trace), and Hermiticity of `H` holds for
every `ω`.

This is the reusable envelope: it supplies the `Env` hypothesis of
`RBM.Gauss.momentDom_of_stochDom` and every dominated-convergence hypothesis of the Grönwall
argument. -/
theorem norm_gloop_le_det (hH : H.IsHermitian) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (I : LoopIdx (ZMod L)) (hwf : I.σ.length = I.a.length) (hn : 1 ≤ I.a.length) :
    ‖gloop L W H (zt E t) I‖
      ≤ (etaT E t)⁻¹ ^ I.a.length * (W : ℝ)⁻¹ ^ (I.a.length - 1) :=
  norm_gloop_le_of_le_abs_im hH (etaT_pos_of_lt_one hE ht) (abs_im_zt E hE ht).ge I hwf hn

/-- The deterministic envelope for `max_{σ,a} |L_{t,σ,a}|` (`RBM.loopMax`). -/
theorem loopMax_le_det (hH : H.IsHermitian) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {n : ℕ}
    (hn : 1 ≤ n) :
    loopMax L W H (zt E t) n ≤ (etaT E t)⁻¹ ^ n * (W : ℝ)⁻¹ ^ (n - 1) :=
  loopMax_le fun I hσ ha => by
    have := norm_gloop_le_det hH hE ht I (by rw [hσ, ha]) (by rw [ha]; exact hn)
    rwa [ha] at this

/-- The deterministic envelope for `Ξ^{(L)}_{t,n} = max_{σ,a}|L_{t,σ,a}| · A^{n-1}`
(`RBM.loopXi`, (2.82)/(5.76)), for any non-negative scale `A`. -/
theorem loopXi_le_det (hH : H.IsHermitian) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {A : ℝ}
    (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n) :
    loopXi L W H (zt E t) A n ≤ (etaT E t)⁻¹ ^ n * (W : ℝ)⁻¹ ^ (n - 1) * A ^ (n - 1) :=
  mul_le_mul_of_nonneg_right (loopMax_le_det hH hE ht hn) (by positivity)

/-- The deterministic envelope for a **difference** `L - K`: if the subtracted family has its own
pointwise bound `BK` (for `K` of (3.46) this is `RBM.norm_Kgen_le`), then `L - K` inherits the
sum of the two envelopes.  The same shape covers `Ξ^{(L-K)}` and, through `RBM.jStar_le`, the
ratio `J*` of (5.29). -/
theorem norm_gloop_sub_le_det (hH : H.IsHermitian) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    {K : LoopIdx (ZMod L) → ℂ} {BK : ℝ} (hK : ∀ I, ‖K I‖ ≤ BK)
    (I : LoopIdx (ZMod L)) (hwf : I.σ.length = I.a.length) (hn : 1 ≤ I.a.length) :
    ‖gloop L W H (zt E t) I - K I‖
      ≤ (etaT E t)⁻¹ ^ I.a.length * (W : ℝ)⁻¹ ^ (I.a.length - 1) + BK :=
  (norm_sub_le _ _).trans (add_le_add (norm_gloop_le_det hH hE ht I hwf hn) (hK I))

/-- **The envelope is of polynomial growth.**  If `η_t` is not super-polynomially small,
`N^{-c} ≤ η_t`, and `1 ≤ W`, then `η_t^{-n} W^{-n+1} ≤ N^{cn}`.  This is what turns
`norm_gloop_le_det` into the `Env` / `Kenv` hypotheses of
`RBM.Gauss.momentDom_of_stochDom`. -/
theorem det_envelope_le_rpow {η : ℝ} (hη : 0 < η) {c : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hηN : (N : ℝ) ^ (-c) ≤ η) {W : ℕ} (hW : 1 ≤ W) (n : ℕ) :
    η⁻¹ ^ n * (W : ℝ)⁻¹ ^ (n - 1) ≤ (N : ℝ) ^ (c * n) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hWge1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have h1 : η⁻¹ ≤ (N : ℝ) ^ c := by
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hNpos _
    have h := inv_anti₀ hpos hηN
    rwa [Real.rpow_neg hNpos.le, inv_inv] at h
  have h2 : η⁻¹ ^ n ≤ ((N : ℝ) ^ c) ^ n :=
    pow_le_pow_left₀ (by positivity) h1 n
  have h3 : ((N : ℝ) ^ c) ^ n = (N : ℝ) ^ (c * n) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ c) n, ← Real.rpow_mul hNpos.le]
  have h4 : (W : ℝ)⁻¹ ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [inv_le_one_iff₀]; right; exact hWge1)
  calc η⁻¹ ^ n * (W : ℝ)⁻¹ ^ (n - 1) ≤ η⁻¹ ^ n * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = η⁻¹ ^ n := mul_one _
    _ ≤ ((N : ℝ) ^ c) ^ n := h2
    _ = (N : ℝ) ^ (c * n) := h3

/-- **The loop envelope in the shape required by the reverse bridge.**  If `η_t` is not
super-polynomially small, `N^{-c} ≤ η_t`, then every `n`-loop of every Hermitian `H` satisfies
`|L_{t,σ,a}| ≤ N^{cn}` for every `ω`: a deterministic envelope of polynomial growth, which is
exactly the `Env` / `Kenv` input of `RBM.Gauss.momentDom_of_stochDom`. -/
theorem norm_gloop_le_rpow (hH : H.IsHermitian) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {c : ℝ}
    {N : ℕ} (hN : 1 ≤ N) (hηN : (N : ℝ) ^ (-c) ≤ etaT E t) (I : LoopIdx (ZMod L))
    (hwf : I.σ.length = I.a.length) (hn : 1 ≤ I.a.length) :
    ‖gloop L W H (zt E t) I‖ ≤ (N : ℝ) ^ (c * I.a.length) :=
  (norm_gloop_le_det hH hE ht I hwf hn).trans
    (det_envelope_le_rpow (etaT_pos_of_lt_one hE ht) hN hηN
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne W)) _)

end Envelope

end RBM.Gauss

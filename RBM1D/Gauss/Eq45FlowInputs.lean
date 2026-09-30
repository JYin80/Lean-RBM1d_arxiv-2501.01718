/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45Flow
import RBM1D.Gauss.DominationHolder
import RBM1D.Gauss.CondStableInst
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.TraceMoment
import RBM1D.Gauss.FlucIter
import RBM1D.Gauss.GoodSetFlowCore

/-!
# Fixed-time domination uniform in the time, and the net theorem with a random control

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Definition 2.1 (i) and Lemma 4.1 (4.5).

The inputs of (4.5) are proved at a fixed time; along the flow they are needed with the time
inside the index set of `≺`, i.e. with an existential over `u ∈ [s_N, t_N]` **inside the
probability** (`RBM.badSet`, `RBM1D/Defs/StochDom.lean`).  That union is uncountable, so a time
net is unavoidable.

## The net engine

Every net theorem of `RBM1D/Gauss/DominationHolder.lean` takes a control `Φ : ℕ → ℝ` or
`Φ : ℕ → ℝ → ℝ` that is **deterministic**.  The control of the inputs of (4.5) is `L^max_u(ω)`,
which is random *and* time-dependent.  `RBM.Gauss.stochDom_timeIcc_of_unifDom` is the net
theorem for that case: it transports a fixed-time domination that is uniform in `u`
(`RBM.Gauss.UnifDomIcc`) to the `TimeIcc` index set, given

* a Hölder-`γ` modulus for the dominated quantity on a high-probability event,
* a polynomial lower bound `N^{-B} ≤ ζ` on that event, and
* **slow variation of the control**, `ζ(v) ≤ N^ε ζ(u)` at net separation.

## The `L^max ≍ W^{-1}` sandwich

The two-sided sandwich `W^{-1}/4 ≤ L^max_u ≤ η_u^{-2} W^{-1}` gives slow variation of the
control only up to a factor `4 η_v^{-2}`, which is **not** `≤ N^ε` in the regime `t_N → 1` in
which §4 is used.  Slow variation therefore needs a genuine modulus of `L^max` in the time, whose
loss is the net spacing `T N^{-(K+B+1)/γ}`; the caller controls it, since `K` is free.  Only the
**lower** half `W^{-1}/4 ≤ L^max_u` of the sandwich survives at every time of the flow interval.

## Markov without a net

`RBM.Gauss.UnifDomIcc` bounds the failure probability *per index and per time*, so Markov
applies verbatim, with no cardinality hypothesis (`RBM.Gauss.unifDomIcc_of_moment`); what has to
be uniform in `u` is only the threshold in `N`.

## Main definitions

* `RBM.Gauss.UnifDomIcc` — a fixed-time domination, uniform over `u ∈ [s_N, t_N]`.

## Main results

* `RBM.Gauss.stochDom_timeIcc_of_unifDom` — the net theorem with a random, time-dependent
  control.
* `RBM.Gauss.UnifDomIcc.trans` — transitivity, with the `τ/2` split of `RBM.StochDom.trans`.
* `RBM.Gauss.unifDomIcc_of_moment` — Markov's inequality, uniformly in the time.
* `RBM.Gauss.W_le_self` — `W ≤ N` eventually.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

/-! ### A fixed-time domination, uniform in the time -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **Definition 2.1 (i) at each fixed time, uniformly in the time and in the index.**

This is what a fixed-time proof gives when its constants do not depend on the time: for every
`τ, D > 0`, eventually in `N`, *every* `u ∈ [s_N, t_N]` and every index `a` has
`P{N^τ ζ < ξ} ≤ N^{-D}`.  It is strictly weaker than `≺` on `TimeIcc s t N × V N`, which puts
the union over `u` inside the probability. -/
def UnifDomIcc (P : Measure Ω) {V : ℕ → Type*} (s t : ℕ → ℝ)
    (ξ ζ : ∀ N, ℝ → V N → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N), ∀ a : V N,
    P {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ N u a ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

omit [IsFiniteMeasure P] in
/-- **The net theorem with a random, time-dependent control.**

`RBM1D/Gauss/DominationHolder.lean` has five net theorems, all with a deterministic
control; this is the one the (4.5) inputs need, whose control `ζ(N, u, a, ω)` is random and
time-dependent.  The moment input is replaced by `RBM.Gauss.UnifDomIcc` — the fixed-time
domination, uniform in `u` — which is what the fixed-time producers actually deliver.

The three extra hypotheses are exactly the price of the net:

* `hHol`, a Hölder-`γ` modulus for `ξ` with the deterministic constant `N^K`, valid on a
  high-probability event `Ξ` (use `RBM.StochDom.highProb` on `‖X‖ ≺ 1` to put a random constant
  there);
* `hζlow`, `N^{-B} ≤ ζ` on `Ξ` — the control is not super-polynomially small;
* `hslow`, slow variation of the control at separation `δ N`, where `hδ` says `δ N` is at
  least the spacing `T·N^{-(K+B+1)/γ}` of the net the proof builds.  `K` is free, so the caller
  may always make the net finer. -/
theorem stochDom_timeIcc_of_unifDom {V : ℕ → Type*} [∀ N, Fintype (V N)] {Cv : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ Cv)
    {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T)
    {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ)
    {ξ ζ : ∀ N, ℝ → V N → Ω → ℝ} (hζ0 : ∀ N u a ω, 0 ≤ ζ N u a ω)
    {δ : ℕ → ℝ} (hδ : ∀ᶠ N : ℕ in atTop, T / (N : ℝ) ^ ((K + B + 1) / γ) ≤ δ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ a : V N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ v ∈ Set.Icc (s N) (t N), |ξ N u a ω - ξ N v a ω| ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hζlow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ a : V N, ∀ u ∈ Set.Icc (s N) (t N),
      (N : ℝ) ^ (-B) ≤ ζ N u a ω)
    (hslow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ a : V N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N), |u - v| ≤ δ N →
        ζ N v a ω ≤ (N : ℝ) ^ ε * ζ N u a ω)
    (hfix : UnifDomIcc P s t ξ ζ) :
    StochDom P (U := fun N => RBM.TimeIcc s t N × V N)
      (fun N p ω => ξ N (p.1 : ℝ) p.2 ω) (fun N p ω => ζ N (p.1 : ℝ) p.2 ω) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1: the domination on the net, by a union bound over polynomially many points
  have hnet : StochDom P (U := fun N => Fin (netSize A N + 1) × V N)
      (fun N p ω => ξ N (netTime s t T A N p.1) p.2 ω)
      (fun N p ω => ζ N (netTime s t T A N p.1) p.2 ω) := by
    refine StochDom.of_forall_le (C := (A + 1) + Cv) ?_ ?_
    · filter_upwards [card_net_le hA, hcard, eventually_ge_atTop 1] with N h1 h2 hN1
      have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add hNpos]
      have h0 : (0 : ℝ) ≤ (Fintype.card (V N) : ℝ) := Nat.cast_nonneg _
      have hpos : (0 : ℝ) < (N : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos _
      calc ((Fintype.card (Fin (netSize A N + 1)) : ℕ) : ℝ) * (Fintype.card (V N) : ℝ)
          ≤ (N : ℝ) ^ (A + 1) * (Fintype.card (V N) : ℝ) :=
            mul_le_mul_of_nonneg_right h1 h0
        _ ≤ (N : ℝ) ^ (A + 1) * (N : ℝ) ^ Cv := mul_le_mul_of_nonneg_left h2 hpos.le
    · intro τ hτ D hD
      filter_upwards [hfix τ hτ D hD] with N hN p
      exact hN _ (netTime_mem hst hT.le A N p.1) p.2
  -- step 2: transfer from the net to the whole interval, on `Ξ`
  refine stochDom_of_subset_highProb hnet hΞ fun τ hτ => ⟨τ / 4, by linarith, ?_⟩
  have hτ4 : (0 : ℝ) < τ / 4 := by linarith
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  filter_upwards [hHol, hζlow, hslow (τ / 4) hτ4, hδ, eventually_ge_atTop 1,
    eventually_le_rpow (T ^ γ) one_pos, eventually_le_rpow 2 (show (0:ℝ) < τ / 4 by linarith)]
    with N hHolN hζlowN hslowN hδN hN1 hNT hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hTN : T ^ γ ≤ (N : ℝ) := by rwa [Real.rpow_one] at hNT
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hmge : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := rpow_le_netSize A N
  have hNA : (0 : ℝ) < (N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
  -- the spacing of the net, and the size of the net error
  have hspace : T / (netSize A N : ℝ) ≤ T / (N : ℝ) ^ A :=
    div_le_div_of_nonneg_left hT.le hNA hmge
  have herr : (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ ≤ (N : ℝ) ^ (-B) := by
    have hstep1 : (T / (netSize A N : ℝ)) ^ γ ≤ (T / (N : ℝ) ^ A) ^ γ :=
      Real.rpow_le_rpow (div_pos hT hm).le hspace hγ.le
    have hKpos : (0 : ℝ) < (N : ℝ) ^ K := Real.rpow_pos_of_pos hNpos K
    have hpowA : ((N : ℝ) ^ A) ^ γ = (N : ℝ) ^ (K + B + 1) := by
      rw [← Real.rpow_mul hNpos.le, hAγ]
    have hdiv : (T / (N : ℝ) ^ A) ^ γ = T ^ γ / (N : ℝ) ^ (K + B + 1) := by
      rw [Real.div_rpow hT.le hNA.le, hpowA]
    have hexp : K - (K + B + 1) = -B + -1 := by ring
    have hKA : (N : ℝ) ^ K / (N : ℝ) ^ (K + B + 1) = (N : ℝ) ^ (-B) * (N : ℝ)⁻¹ := by
      rw [← Real.rpow_sub hNpos, ← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hNpos, hexp]
    have hstep3 : (N : ℝ) ^ K * (T / (N : ℝ) ^ A) ^ γ
        = T ^ γ * ((N : ℝ) ^ (-B) * (N : ℝ)⁻¹) := by
      rw [hdiv, ← hKA]; ring
    have hBpos : (0 : ℝ) < (N : ℝ) ^ (-B) := Real.rpow_pos_of_pos hNpos _
    have hTinv : T ^ γ * (N : ℝ)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hNpos, one_mul]; exact hTN
    calc (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ
        ≤ (N : ℝ) ^ K * (T / (N : ℝ) ^ A) ^ γ := mul_le_mul_of_nonneg_left hstep1 hKpos.le
      _ = (T ^ γ * (N : ℝ)⁻¹) * (N : ℝ) ^ (-B) := by rw [hstep3]; ring
      _ ≤ 1 * (N : ℝ) ^ (-B) := mul_le_mul_of_nonneg_right hTinv hBpos.le
      _ = (N : ℝ) ^ (-B) := one_mul _
  -- `N^{τ/2} + 1 ≤ N^τ`
  have hsplit2 : (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have h2N : (2 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := hN2
  have hy4 : (4 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by rw [hsplit2]; nlinarith [h2N]
  have hdouble : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by
    rw [hsplit]; nlinarith [hy4]
  rintro ω ⟨⟨⟨⟨u, hu⟩, a⟩, hbad⟩, hωΞ⟩
  simp only at hbad
  obtain ⟨k, hk⟩ := exists_netTime_close hT hlen A N hu
  set v : ℝ := netTime s t T A N k with hv_def
  have hvmem : v ∈ Set.Icc (s N) (t N) := netTime_mem hst hT.le A N k
  have huv : |u - v| ≤ δ N := le_trans (hk.trans hspace) hδN
  have hζu0 : (0 : ℝ) ≤ ζ N u a ω := hζ0 N u a ω
  -- the net error is at most `ζ(u)`
  have hmod : |ξ N u a ω - ξ N v a ω| ≤ ζ N u a ω := by
    refine (hHolN ω hωΞ a u hu v hvmem).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le) (Real.rpow_pos_of_pos hNpos K).le) ?_
    exact herr.trans (hζlowN ω hωΞ a u hu)
  have hξv : ((N : ℝ) ^ τ - 1) * ζ N u a ω < ξ N v a ω := by
    have h1 : ξ N u a ω - ξ N v a ω ≤ ζ N u a ω := (le_abs_self _).trans hmod
    have h2 : (N : ℝ) ^ τ * ζ N u a ω < ξ N u a ω := hbad
    nlinarith
  have hζv : ζ N v a ω ≤ (N : ℝ) ^ (τ / 4) * ζ N u a ω := hslowN ω hωΞ a u hu v hvmem huv
  refine ⟨(k, a), ?_⟩
  show (N : ℝ) ^ (τ / 4) * ζ N v a ω < ξ N v a ω
  have hp4 : (0 : ℝ) < (N : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hNpos _
  calc (N : ℝ) ^ (τ / 4) * ζ N v a ω
      ≤ (N : ℝ) ^ (τ / 4) * ((N : ℝ) ^ (τ / 4) * ζ N u a ω) :=
        mul_le_mul_of_nonneg_left hζv hp4.le
    _ = (N : ℝ) ^ (τ / 2) * ζ N u a ω := by rw [hsplit2]; ring
    _ ≤ ((N : ℝ) ^ τ - 1) * ζ N u a ω := by nlinarith
    _ < ξ N v a ω := hξv

end Engine

/-! ### The control `L^max_u`: the three hypotheses of the engine -/

section Lmax

open Matrix

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {δ : ℕ → ℝ} {N : ℕ}


/-- `W(N) ≤ N` eventually, from `W L ≤ N` and `3 ≤ L`. -/
theorem W_le_self (d : Dims) : ∀ᶠ N : ℕ in atTop, d.W N ≤ N := by
  filter_upwards [d.dim] with N hN
  have h3 := d.three_le_L N
  nlinarith [hN.1, Nat.zero_le (d.W N)]

/-! #### The modulus of `L^max` in the time

The sandwich `W^{-1}/4 ≤ L^max_u ≤ η_u^{-2} W^{-1}` would give slow variation only up to the
factor `4 η^{-2}`, which is polynomially large in the regime `t_N → 1` where §4 is used.  The
estimate below is a genuine modulus, and the loss it produces is the *net spacing*, which the
caller controls. -/

end Lmax

/-! ### The three inputs of (4.5), along the flow -/

section Inputs

variable {d : Dims} {E : ℝ} {s t δ : ℕ → ℝ} {K : ℝ}

end Inputs

/-! ### Transitivity and Markov's inequality, uniformly in the time -/

section Fixed

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
/-- **`RBM.Gauss.UnifDomIcc` is transitive**, with the same `τ/2` split as
`RBM.StochDom.trans`.  This is what composes a domination by a deterministic control with the
comparison of that control against the random `L^max_u`. -/
theorem UnifDomIcc.trans {V : ℕ → Type*} {s t : ℕ → ℝ} {ξ ζ χ : ∀ N, ℝ → V N → Ω → ℝ}
    (h₁ : UnifDomIcc P s t ξ ζ) (h₂ : UnifDomIcc P s t ζ χ) : UnifDomIcc P s t ξ χ := by
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := half_pos hτ
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  filter_upwards [h₁ (τ / 2) hτ2 (D + 1) hD1, h₂ (τ / 2) hτ2 (D + 1) hD1,
    eventually_two_mul_rpow_le D] with N h1 h2 h3 u hu a
  have hsub : {ω | (N : ℝ) ^ τ * χ N u a ω < ξ N u a ω}
      ⊆ {ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ N u a ω}
        ∪ {ω | (N : ℝ) ^ (τ / 2) * χ N u a ω < ζ N u a ω} := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hno
    simp only [Set.mem_ofPred_eq] at hω
    have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hcalc : ξ N u a ω ≤ (N : ℝ) ^ τ * χ N u a ω :=
      calc ξ N u a ω ≤ (N : ℝ) ^ (τ / 2) * ζ N u a ω := hno.1
        _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * χ N u a ω) :=
            mul_le_mul_of_nonneg_left hno.2 hpos
        _ = (N : ℝ) ^ τ * χ N u a ω := by
            rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]
    linarith
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P {ω | (N : ℝ) ^ τ * χ N u a ω < ξ N u a ω}
      ≤ P ({ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ N u a ω}
          ∪ {ω | (N : ℝ) ^ (τ / 2) * χ N u a ω < ζ N u a ω}) := measure_mono hsub
    _ ≤ P {ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ N u a ω}
          + P {ω | (N : ℝ) ^ (τ / 2) * χ N u a ω < ζ N u a ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add (h1 u hu a) (h2 u hu a)
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- **Markov's inequality, uniformly in the time.**  The moment version of
`RBM.Gauss.UnifDomIcc`, and the reason the fixed-time inputs of (4.5) do *not* need a net:
`RBM.Gauss.UnifDomIcc` asks for the failure probability at each index and each time
separately, so no union bound — and hence no cardinality hypothesis, in contrast with
`RBM.Gauss.stochDom_of_momentDom` — is taken.  What must be uniform in `u` is only the
threshold in `N`. -/
theorem unifDomIcc_of_moment {V : ℕ → Type*} {s t : ℕ → ℝ} {ξ : ∀ N, ℝ → V N → Ω → ℝ}
    {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N), ∀ a : V N,
      Integrable (fun ω => |ξ N u a ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ a : V N,
        ∫ ω, |ξ N u a ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N ^ (2 * p))) :
    UnifDomIcc P s t ξ (fun N _ _ _ => Φ N) := by
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + 1) / τ)
  have hDp : D + 1 ≤ τ * (p : ℝ) := by rw [div_le_iff₀ hτ] at hp; linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - D := by linarith
  filter_upwards [hCN, eventually_ge_atTop 1, eventually_le_rpow C hexp]
    with N hN hN1 hCle u hu a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hrp : (0 : ℝ) < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNpos τ
  have hthr : 0 < (N : ℝ) ^ τ * Φ N := mul_pos hrp (hΦ N)
  refine (meas_gt_le_of_moment P hthr (hint p N u hu a) (hN u hu a)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set A : ℝ := (N : ℝ) ^ (τ * (p : ℝ)) with hA_def
  have hA : 0 < A := Real.rpow_pos_of_pos hNpos _
  have hΦN0 : (0 : ℝ) < Φ N := hΦ N
  have hb : (0 : ℝ) < Φ N ^ (2 * p) := by positivity
  have h1 : ((N : ℝ) ^ τ * Φ N) ^ (2 * p) = A * A * Φ N ^ (2 * p) := by
    rw [mul_pow, hA_def, ← Real.rpow_natCast ((N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le,
      ← Real.rpow_add hNpos]
    push_cast
    ring_nf
  have h2 : C * (A * Φ N ^ (2 * p)) / (A * A * Φ N ^ (2 * p)) = C * A⁻¹ := by field_simp
  have h3 : A⁻¹ = (N : ℝ) ^ (-(τ * (p : ℝ))) := by rw [hA_def, Real.rpow_neg hNpos.le]
  rw [h1, h2]
  calc C * A⁻¹ ≤ (N : ℝ) ^ (τ * (p : ℝ) - D) * A⁻¹ :=
        mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 hA.le)
    _ = (N : ℝ) ^ (-D) := by
        rw [h3, ← Real.rpow_add hNpos]
        congr 1
        ring

end Fixed

/-! #### The fluctuation averaging inputs, from the iterated route -/

section FlucFix

open Filter

variable {E : ℝ} {s t : ℕ → ℝ}

end FlucFix

section FlucEnv

open Filter

variable {E : ℝ} {s t : ℕ → ℝ}

end FlucEnv

/-! ### Split threshold and mesh for the time net -/

open scoped Matrix.Norms.L2Operator

end RBM.Gauss

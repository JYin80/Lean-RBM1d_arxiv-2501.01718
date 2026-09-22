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

/-!
# The three time-indexed inputs of (4.5) — T124

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.5) and the fluctuation averaging (4.12).

`RBM1D/Gauss/Eq45Flow.lean` (T121) discharges `RBM.StepGlue.Eq45Flow` from three inputs with
the time inside the index set — `RBM.Gauss.IBPFlow`, `RBM.Gauss.FlucRowFlow`,
`RBM.Gauss.FlucBlkFlow`.  This file produces those three from their fixed-time forms.

## Step 0: these are **T116's** case, not T108's — the time net is unavoidable

T121 and T108 lift a domination *whose hypothesis already carries the time in its index set*;
there the index set is inert and no net is needed.  Here the situation is the opposite one:
the fixed-time statements control, for each `N`, **one time at a time**, while the conclusion
needs `RBM.badSet` with an existential over `u ∈ [s_N, t_N]` **inside the probability**
(`RBM1D/Defs/StochDom.lean`).  That union is uncountable.  Concretely, all three fixed-time
producers factor through a step that *requires a finite index set*:

* `RBM.Gauss.stochDom_flucAvg` (T88) — hence `RBM.Gauss.stochDom_flucAvg_Sblk` and
  `RBM.Gauss.stochDom_flucAvg_blockAvg`, the fixed-time `FlucRowFlow`/`FlucBlkFlow` — goes
  through `RBM.Gauss.stochDom_of_momentDom`, whose hypothesis `hcard` is a **polynomial bound
  on `Fintype.card (U N)`**.  `RBM.TimeIcc s t N` is not a `Fintype`.
* `RBM.Gauss.condExpDiag_stochDom_of_highProb` (T119) — the fixed-time `IBPFlow` — goes
  through `RBM.Gauss.stochDom_condRow_of_envelope` (T112), which carries the same
  `[∀ N, Fintype (U N)]` and `hcard`; and its remaining hypothesis `hΩ` is a `HighProb`
  statement about the good event (4.1) **at one time**.

So this is exactly `RBM.Gauss.NetLift` (T116), not `RBM.Step1.Lemma41Flow` (T108), and T101's
net engines plus `‖X‖ ≺ 1` (T109) are what is needed — as T121 predicted.

## What the net engine has to be able to do that `RBM1D/Gauss/DominationHolder.lean` cannot

Every net theorem of T101 takes a control `Φ : ℕ → ℝ` or `Φ : ℕ → ℝ → ℝ` that is
**deterministic**.  The control of all three inputs is `L^max_u(ω)`, which is random *and*
time-dependent.  `RBM.Gauss.stochDom_timeIcc_of_unifDom` below is the net theorem for that
case: it transports a fixed-time domination that is uniform in `u` to the `TimeIcc` index set,
given

* a Hölder-`γ` modulus for the dominated quantity on a high-probability event,
* a polynomial lower bound `N^{-B} ≤ ζ` on that event, and
* **slow variation of the control**, `ζ(v) ≤ N^ε ζ(u)` at net separation.

## The `L^max ≍ W^{-1}` caveat of T119, addressed

T119 proves `W^{-1}/4 ≤ L^max_u ≤ η_t^{-2} W^{-1}` and notes that the resulting comparison is
**fixed-time**: when `t_N → 1` the factor `η^{-2}` is polynomially large and
`RBM.Gauss.stochDom_Lmax_inv_W` stops being a `≺`.  That caveat applies verbatim to the slow
variation of the control: deducing `L^max_v ≤ N^ε L^max_u` from the two-sided sandwich costs a
factor `4 η_v^{-2}`, which is **not** `≤ N^ε` in the regime §4 is used in.

The route taken here therefore avoids the sandwich for slow variation and uses a genuine
modulus instead: `RBM.Gauss.Lmax_flow_le_add` is a deterministic estimate of the variation of
`L^max` in the time, with constant `(η_u^{-1} + η_v^{-1})‖G_u - G_v‖`, and
`RBM.Gauss.Lmax_flow_slow_of_net` converts it into slow variation *because the caller may make
the net as fine as it likes* (the net spacing is `T N^{-(K+B+1)/γ}` and `K` is a free
parameter).  Only the **lower** half of the sandwich, `W^{-1}/4 ≤ L^max_u`, is used, and that
half is the one that survives at every time of the flow interval.

## What is still open

The three producers below carry two hypotheses each, and neither is discharged here:

* `hfix`, the fixed-time input as a `RBM.Gauss.UnifDomIcc` — the existing fixed-time producers
  (`RBM.Gauss.condExpDiag_stochDom_of_highProb`, `RBM.Gauss.stochDom_flucAvg_Sblk`,
  `RBM.Gauss.stochDom_flucAvg_blockAvg`) are themselves conditional, on (4.4) and on the
  *sizes* of the `RBM.Gauss.FlucBound` parameters respectively;
* `hHol`, the modulus of the dominated quantity in the time.  For the Green's function part
  this is `RBM.Gauss.norm_green_flow_sub_le` (T106); for the conditional expectation `E_k` it
  is not, and that is the genuinely new estimate the three inputs still need.

`hΩ`, the flow good event, is the `u`-uniform version of the `hΩ` T119 leaves open.

## Main definitions

* `RBM.Gauss.UnifDomIcc` — a fixed-time domination, uniform over `u ∈ [s_N, t_N]`.
* `RBM.Gauss.goodSetFlow` — the good event (4.1) **uniformly in `u ∈ [s_N, t_N]`**; the flow
  analogue of the `hΩ` that T119 leaves open.
* `RBM.Gauss.flowNetEvent` — `goodSetFlow` together with `‖X‖ ≤ N`.

## Main results

* `RBM.Gauss.stochDom_timeIcc_of_unifDom` — the net theorem with a random, time-dependent
  control.
* `RBM.Gauss.Lmax_flow_le_add`, `RBM.Gauss.inv_W_le_Lmax_flow`,
  `RBM.Gauss.rpow_neg_le_Lmax_flow`, `RBM.Gauss.Lmax_flow_slow_of_net` — the three hypotheses
  of the engine, for the control `L^max_u`.
* `RBM.Gauss.highProb_flowNetEvent` — the net event has high probability, given the flow good
  event; the second half is `‖X‖ ≺ 1` (T109).
* `RBM.Gauss.ibpFlow_of_unifDom`, `RBM.Gauss.flucRowFlow_of_unifDom`,
  `RBM.Gauss.flucBlkFlow_of_unifDom` — the three inputs of (4.5) along the flow.
* `RBM.Gauss.eq45Flow_of_unifDom` — `RBM.StepGlue.Eq45Flow` for `RBM.Gauss.sample d`,
  assembled; this is the compile-time check that the three producers fill the three slots of
  `RBM.Gauss.eq45Flow_gauss` with no coercion and no `convert`.
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

`RBM1D/Gauss/DominationHolder.lean` (T101) has five net theorems, all with a deterministic
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

/-- **The good event (4.1) uniformly in `u ∈ [s_N, t_N]`.**

`RBM.goodSet` pins one time in the matrix *and* in the spectral parameter; the `hΩ` that T119
leaves open is that set's `HighProb`.  Along the flow both times move together and the event
must hold at every `u` simultaneously — this is the flow analogue, and it is what the net lift
of the three (4.5) inputs consumes. -/
def goodSetFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (δ : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ∀ u ∈ Set.Icc (s N) (t N), GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) (δ N)}

/-- **`W⁻¹ ≤ 4 L^max_u` at every time of the flow interval.**  This is `RBM.inv_W_le_Lmax` —
the *lower* half of T119's sandwich, the half that does not cost a power of `η⁻¹`. -/
theorem inv_W_le_Lmax_flow (hE : |E| ≤ 2) (hδ : δ N ≤ 1 / 2) {ω : Ω d}
    (hω : ω ∈ goodSetFlow d E s t δ N) {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    ((d.W N : ℕ) : ℝ)⁻¹ ≤ 4 * Lmax (Hflow d N u ω) (zt E u) :=
  inv_W_le_Lmax (Hflow_isHermitian d N u ω) (norm_mE hE) (hω u hu) hδ

/-- `W(N) ≤ N` eventually, from `W L ≤ N` and `3 ≤ L`. -/
theorem W_le_self (d : Dims) : ∀ᶠ N : ℕ in atTop, d.W N ≤ N := by
  filter_upwards [d.dim] with N hN
  have h3 := d.three_le_L N
  nlinarith [hN.1, Nat.zero_le (d.W N)]

/-- **`N^{-2} ≤ L^max_u`, uniformly on the flow interval.**  The control of (4.5) is not
super-polynomially small: this is `hζlow` of `RBM.Gauss.stochDom_timeIcc_of_unifDom`. -/
theorem rpow_neg_le_Lmax_flow (d : Dims) (hE : |E| ≤ 2)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ goodSetFlow d E s t δ N, ∀ u ∈ Set.Icc (s N) (t N),
      (N : ℝ) ^ (-(2 : ℝ)) ≤ Lmax (Hflow d N u ω) (zt E u) := by
  filter_upwards [hδ, W_le_self d, eventually_ge_atTop 4] with N hδN hWN hN4 ω hω u hu
  have hW0 : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
  have hWle : ((d.W N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hWN
  have hN4' : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlow := inv_W_le_Lmax_flow (δ := δ) hE hδN hω hu
  have hkey : (N : ℝ) ^ (-(2 : ℝ)) ≤ ((d.W N : ℕ) : ℝ)⁻¹ / 4 := by
    have hrw : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hNpos.le, ← Real.rpow_natCast (N : ℝ) 2]
      norm_num
    rw [hrw, div_eq_mul_inv, ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-! #### The modulus of `L^max` in the time

The sandwich `W^{-1}/4 ≤ L^max_u ≤ η_u^{-2} W^{-1}` of T119 would give slow variation only up
to the factor `4 η^{-2}`, which is polynomially large in the regime `t_N → 1` where §4 is used
— T119's own warning.  The estimate below is a genuine modulus, and the loss it produces is
the *net spacing*, which the caller controls. -/

/-- Each `L_{(+,-),(a,b)}` moves by at most `(η_u⁻¹ + η_v⁻¹)‖G_u - G_v‖` between two times. -/
theorem Lre_flow_le_add (d : Dims) (N : ℕ) (hE : |E| < 2) {u v : ℝ} (hu1 : u < 1) (hv1 : v < 1)
    (ω : Ω d) (a b : ZMod (d.L N)) :
    Lre (Hflow d N v ω) (zt E v) a b
      ≤ Lre (Hflow d N u ω) (zt E u) a b
        + ((etaT E u)⁻¹ + (etaT E v)⁻¹)
          * ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖ := by
  set C : ℝ := ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hW0 : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
  have hentry : ∀ β α : Fin (d.W N),
      ‖green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ ^ 2
        ≤ ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)‖ ^ 2
          + ((etaT E u)⁻¹ + (etaT E v)⁻¹) * C := by
    intro β α
    set x : ℝ := ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)‖ with hx
    set y : ℝ := ‖green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ with hy
    have hx0 : 0 ≤ x := norm_nonneg _
    have hy0 : 0 ≤ y := norm_nonneg _
    have hxb : x ≤ (etaT E u)⁻¹ := norm_green_apply_le_etaT hE hu1 u (b, β) (a, α) ω
    have hyb : y ≤ (etaT E v)⁻¹ := norm_green_apply_le_etaT hE hv1 v (b, β) (a, α) ω
    have hdiff : |y - x| ≤ C := by
      have h1 : |y - x| = |x - y| := abs_sub_comm _ _
      have h2 : |x - y| ≤ ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)
          - green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ := by
        rw [hx, hy]; exact abs_norm_sub_norm_le _ _
      have h3 : ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)
          - green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ ≤ C := by
        rw [hC]
        simpa using norm_apply_le_l2_opNorm
          (green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)) (b, β) (a, α)
      rw [h1]; linarith
    have hdiff' : y - x ≤ C := (le_abs_self _).trans hdiff
    nlinarith [hx0, hy0, hxb, hyb, hdiff']
  have hsum : (∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
        ‖green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ ^ 2)
      ≤ (∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
          ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)‖ ^ 2)
        + ((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * (((etaT E u)⁻¹ + (etaT E v)⁻¹) * C)) := by
    have hinner : ∀ β : Fin (d.W N),
        (∑ α : Fin (d.W N), ‖green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ ^ 2)
          ≤ (∑ α : Fin (d.W N), ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)‖ ^ 2)
            + ((d.W N : ℕ) : ℝ) * (((etaT E u)⁻¹ + (etaT E v)⁻¹) * C) := by
      intro β
      have h := Finset.sum_le_sum (fun α (_ : α ∈ (Finset.univ : Finset (Fin (d.W N)))) =>
        hentry β α)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h
      exact h
    have h := Finset.sum_le_sum (fun β (_ : β ∈ (Finset.univ : Finset (Fin (d.W N)))) =>
      hinner β)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    exact h
  rw [Lre_eq (Hflow_isHermitian d N v ω), Lre_eq (Hflow_isHermitian d N u ω)]
  have hfac : (((d.W N : ℕ) : ℝ)⁻¹) ^ 2
      * (((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * (((etaT E u)⁻¹ + (etaT E v)⁻¹) * C)))
      = ((etaT E u)⁻¹ + (etaT E v)⁻¹) * C := by
    field_simp
  have hpos : (0 : ℝ) ≤ (((d.W N : ℕ) : ℝ)⁻¹) ^ 2 := by positivity
  calc (((d.W N : ℕ) : ℝ)⁻¹) ^ 2 * ∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
        ‖green (Hflow d N v ω) (zt E v) (b, β) (a, α)‖ ^ 2
      ≤ (((d.W N : ℕ) : ℝ)⁻¹) ^ 2 * ((∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
          ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)‖ ^ 2)
        + ((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * (((etaT E u)⁻¹ + (etaT E v)⁻¹) * C))) :=
        mul_le_mul_of_nonneg_left hsum hpos
    _ = (((d.W N : ℕ) : ℝ)⁻¹) ^ 2 * ∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
          ‖green (Hflow d N u ω) (zt E u) (b, β) (a, α)‖ ^ 2
        + ((etaT E u)⁻¹ + (etaT E v)⁻¹) * C := by rw [mul_add, hfac]

/-- **`L^max` moves by at most `(η_u⁻¹ + η_v⁻¹)‖G_u - G_v‖`.**  Deterministic; no good event
and no local law. -/
theorem Lmax_flow_le_add (d : Dims) (N : ℕ) (hE : |E| < 2) {u v : ℝ} (hu1 : u < 1) (hv1 : v < 1)
    (ω : Ω d) :
    Lmax (Hflow d N v ω) (zt E v)
      ≤ Lmax (Hflow d N u ω) (zt E u)
        + ((etaT E u)⁻¹ + (etaT E v)⁻¹)
          * ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖ := by
  refine Finset.sup'_le _ _ fun p _ => ?_
  have h1 := Lre_flow_le_add d N hE hu1 hv1 ω p.1 p.2
  have h2 : Lre (Hflow d N u ω) (zt E u) p.1 p.2 ≤ Lmax (Hflow d N u ω) (zt E u) :=
    Lre_le_Lmax p.1 p.2
  linarith

/-- The event the net argument runs on: the good event (4.1) at **every** time of the flow
interval, together with `‖X‖ ≤ N`. -/
def flowNetEvent (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (δ : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  goodSetFlow d E s t δ N ∩ {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- `RBM.Gauss.flowNetEvent` has high probability as soon as the flow good event does: the
second half is `‖X‖ ≺ 1` (T109, `RBM.Gauss.stochDom_norm_Xmat_gauss`) at `τ = 1`. -/
theorem highProb_flowNetEvent (d : Dims) {E : ℝ} {s t δ : ℕ → ℝ}
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) :
    HighProb (P d) (flowNetEvent d E s t δ) := by
  refine hΩ.inter ?_
  refine ((stochDom_norm_Xmat_gauss d).highProb one_pos).mono
    (Eventually.of_forall fun N ω hω => ?_)
  have h := hω ()
  simpa [Real.rpow_one] using h

/-- **Slow variation of the control `L^max_u` at the net spacing.**

This is `hslow` of `RBM.Gauss.stochDom_timeIcc_of_unifDom` for `ζ = L^max`.  It does **not**
go through T119's `L^max ≍ W^{-1}` sandwich, whose upper half costs `η^{-2}` and therefore
fails when `t_N → 1`; only the lower half `W^{-1}/4 ≤ L^max_u` is used, through
`RBM.Gauss.rpow_neg_le_Lmax_flow`.  The variation is controlled by the genuine modulus
`RBM.Gauss.Lmax_flow_le_add`, and the hypothesis `hfine` says the net is fine enough for the
resulting error to be below `N^{-2}`.  Since the engine only asks `T·N^{-(K+B+1)/γ} ≤ δ N` and
`K` is free, `hfine` and that constraint are simultaneously satisfiable whenever `η_{t_N}` is
bounded below by a power of `N` — which is exactly the standing regime `W ℓ_u η_u ≥ 1`. -/
theorem Lmax_flow_slow_of_net {V : ℕ → Type*} (d : Dims) {E : ℝ} {s t δ : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hδ0 : ∀ N, 0 ≤ δ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ _a : V N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N), |u - v| ≤ δ N →
        Lmax (Hflow d N v ω) (zt E v) ≤ (N : ℝ) ^ ε * Lmax (Hflow d N u ω) (zt E u) := by
  intro ε hε
  filter_upwards [hδ1, hfine, rpow_neg_le_Lmax_flow (E := E) (s := s) (t := t) d hE.le hδ1,
    eventually_le_rpow 2 hε, eventually_ge_atTop 1]
    with N hδN hfineN hlowN h2N hN1 ω hω _a u hu v hv huv
  obtain ⟨hωΩ, hωX⟩ := hω
  set η : ℝ := etaT E (t N) with hη_def
  have hηpos : 0 < η := etaT_pos_of_lt_one' hE (ht1 N)
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
  have hu0 : (0 : ℝ) ≤ u := (hs0 N).trans hu.1
  have hv0 : (0 : ℝ) ≤ v := (hs0 N).trans hv.1
  have hiu : (etaT E u)⁻¹ ≤ η⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hηpos (etaT_le_of_le hE hu.2)
  have hiv : (etaT E v)⁻¹ ≤ η⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hηpos (etaT_le_of_le hE hv.2)
  have hiu0 : (0 : ℝ) < (etaT E u)⁻¹ := by
    have := etaT_pos_of_lt_one' hE hu1; positivity
  have hiv0 : (0 : ℝ) < (etaT E v)⁻¹ := by
    have := etaT_pos_of_lt_one' hE hv1; positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set dh : ℝ := δ N ^ ((1 : ℝ) / 2) with hdh_def
  have hdh0 : (0 : ℝ) ≤ dh := Real.rpow_nonneg (hδ0 N) _
  -- the middle factor of the resolvent modulus
  have hmid : |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v| ≤ 2 * (N : ℝ) * dh := by
    have hd1 : |u - v| ≤ 1 := huv.trans (by linarith)
    have h1 : |Real.sqrt u - Real.sqrt v| ≤ |u - v| ^ ((1 : ℝ) / 2) := by
      have h := RBM.abs_sqrt_sub_sqrt_le hu0 hv0
      rwa [show Real.sqrt |u - v| = |u - v| ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow _] at h
    have h2 : |u - v| ≤ |u - v| ^ ((1 : ℝ) / 2) := self_le_rpow_half (abs_nonneg _) hd1
    have h3 : |u - v| ^ ((1 : ℝ) / 2) ≤ dh :=
      Real.rpow_le_rpow (abs_nonneg _) huv (by norm_num)
    have hX0 : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
    have hXN : ‖Xmat d N ω‖ ≤ (N : ℝ) := hωX
    nlinarith [h1, h2, h3, hX0, hXN, hdh0]
  have hm0 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v| := by
    have h1 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ := by positivity
    linarith [abs_nonneg (u - v)]
  -- the resolvent modulus, with every `η_u` replaced by `η`
  have hΔ : ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖
      ≤ η⁻¹ * (2 * (N : ℝ) * dh) * η⁻¹ := by
    refine (norm_green_flow_sub_le d N hE hu1 hv1 ω).trans ?_
    gcongr
  have hΔ0 : (0 : ℝ) ≤ ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖ :=
    norm_nonneg _
  -- the total error
  have herr : Lmax (Hflow d N v ω) (zt E v)
      ≤ Lmax (Hflow d N u ω) (zt E u) + 4 * (η⁻¹) ^ 3 * (N : ℝ) * dh := by
    refine (Lmax_flow_le_add d N hE hu1 hv1 ω).trans ?_
    have hfirst : (etaT E u)⁻¹ + (etaT E v)⁻¹ ≤ 2 * η⁻¹ := by linarith
    have h2η : (0 : ℝ) ≤ 2 * η⁻¹ := by positivity
    have hstep : ((etaT E u)⁻¹ + (etaT E v)⁻¹)
        * ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖
        ≤ (2 * η⁻¹) * (η⁻¹ * (2 * (N : ℝ) * dh) * η⁻¹) :=
      mul_le_mul hfirst hΔ hΔ0 h2η
    have heq : (2 * η⁻¹) * (η⁻¹ * (2 * (N : ℝ) * dh) * η⁻¹) = 4 * (η⁻¹) ^ 3 * (N : ℝ) * dh := by
      ring
    linarith [hstep, heq ▸ hstep]
  -- the error is below `N^{-2} ≤ L^max_u`
  have hNsq : (0 : ℝ) < (N : ℝ) ^ (2 : ℕ) := by positivity
  have hprod : (4 * (η⁻¹) ^ 3 * (N : ℝ) * dh) * (N : ℝ) ^ (2 : ℕ) ≤ 1 := by
    calc (4 * (η⁻¹) ^ 3 * (N : ℝ) * dh) * (N : ℝ) ^ (2 : ℕ)
        = 4 * (η⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * dh := by ring
      _ ≤ 1 := hfineN
  have hsmall : 4 * (η⁻¹) ^ 3 * (N : ℝ) * dh ≤ ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hprod (le_of_lt (inv_pos.2 hNsq))
    rwa [mul_assoc, mul_inv_cancel₀ hNsq.ne', mul_one, one_mul] at hstep
  have hlow : ((N : ℝ) ^ (2 : ℕ))⁻¹ ≤ Lmax (Hflow d N u ω) (zt E u) := by
    have h := hlowN ω hωΩ u hu
    have hrw : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hNpos.le, ← Real.rpow_natCast (N : ℝ) 2]
      norm_num
    rwa [hrw] at h
  have hL0 : 0 ≤ Lmax (Hflow d N u ω) (zt E u) := Lmax_nonneg (Hflow_isHermitian d N u ω)
  nlinarith [herr, hsmall, hlow, hL0, h2N]

end Lmax

/-! ### The three inputs of (4.5), along the flow -/

section Inputs

variable {d : Dims} {E : ℝ} {s t δ : ℕ → ℝ} {K : ℝ}

/-- **The engine at the control `L^max_u`.**  `RBM.Gauss.stochDom_timeIcc_of_unifDom` with
`γ = 1/2` (the Hölder exponent the flow produces), `B = 2` (`RBM.Gauss.rpow_neg_le_Lmax_flow`),
`T = 1` (the flow interval sits inside `[0,1]`) and `Ξ = RBM.Gauss.flowNetEvent`. -/
theorem stochDom_timeIcc_Lmax_of_unifDom {V : ℕ → Type*} [∀ N, Fintype (V N)] (d : Dims)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ))
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {ξ : ∀ N, ℝ → V N → Ω d → ℝ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : V N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |ξ N u a ω - ξ N v a ω| ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t ξ (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × V N)
      (fun N p ω => ξ N (p.1 : ℝ) p.2 ω)
      (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))) := by
  refine stochDom_timeIcc_of_unifDom hcard hst one_pos ?_ hK (by norm_num : (0:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) < (1:ℝ)/2) ?_ hδnet (highProb_flowNetEvent d hΩ) hHol ?_
    (Lmax_flow_slow_of_net (V := V) d hE hs0 ht1 hδ0 hδ1 hfine) hfix
  · intro N; have h1 := hs0 N; have h2 := (ht1 N).le; linarith
  · intro N u a ω; exact Lmax_nonneg (Hflow_isHermitian d N u ω)
  · filter_upwards [rpow_neg_le_Lmax_flow (E := E) (s := s) (t := t) d hE.le hδ1]
      with N hN ω hω a u hu
    exact hN ω hω.1 u hu

/-- **`RBM.Gauss.IBPFlow`** — the Gaussian integration-by-parts display of p. 50 with the time
in the index set — from its fixed-time form plus the net data. -/
theorem ibpFlow_of_unifDom (d : Dims)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖y N u ω i - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖y N v ω i - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖y N u ω i - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    IBPFlow (sample d) E s t (fun N u ω i => y N (u : ℝ) ω i) :=
  stochDom_timeIcc_Lmax_of_unifDom d (card_Idx_le d) hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
    hHol hfix

/-- **`RBM.Gauss.FlucRowFlow`** — (4.12) for `t_k = S_{ik}` with the time in the index set. -/
theorem flucRowFlow_of_unifDom (d : Dims)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E) - y N v ω k)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    FlucRowFlow (sample d) E s t (fun N u ω i => y N (u : ℝ) ω i) :=
  stochDom_timeIcc_Lmax_of_unifDom d (card_Idx_le d) hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
    hHol hfix

/-- **`RBM.Gauss.FlucBlkFlow`** — (4.12) for `t_k = W⁻¹ 1(k ∈ I_a)` with the time in the index
set. -/
theorem flucBlkFlow_of_unifDom (d : Dims)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E) - y N v ω k)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    FlucBlkFlow (sample d) E s t (fun N u ω i => y N (u : ℝ) ω i) :=
  stochDom_timeIcc_Lmax_of_unifDom d (card_ZMod_L_le d) hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
    hHol hfix

/-- **`RBM.StepGlue.Eq45Flow` for the Gaussian model, from the fixed-time inputs.**

Everything T121 left open is routed through the net: the three `UnifDomIcc` hypotheses are the
fixed-time (4.5) inputs (`RBM.Gauss.condExpDiag_stochDom_of_highProb`,
`RBM.Gauss.stochDom_flucAvg_Sblk`, `RBM.Gauss.stochDom_flucAvg_blockAvg`) restated uniformly in
the time, the three `hHol` are their moduli in the time, and `hΩ` is (4.4) along the whole flow
interval. -/
theorem eq45Flow_of_unifDom (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖y N u ω i - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖y N v ω i - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfixIBP : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖y N u ω i - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E) - y N v ω k)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfixRow : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E) - y N v ω k)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfixBlk : UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    StepGlue.Eq45Flow (sample d) E s t :=
  eq45Flow_gauss hκ0 hκ1 hEκ hs0 ht1
    (ibpFlow_of_unifDom d (by linarith [abs_nonneg E]) hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
      hHolIBP hfixIBP)
    (flucRowFlow_of_unifDom d (by linarith [abs_nonneg E]) hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
      hHolRow hfixRow)
    (flucBlkFlow_of_unifDom d (by linarith [abs_nonneg E]) hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
      hHolBlk hfixBlk)

end Inputs

/-! ### The fixed-time inputs `hfix` — T128

The three `RBM.Gauss.UnifDomIcc` hypotheses above are the *fixed-time* content of (4.5),
uniformly in the time.  This section supplies two of the three and says exactly what the
third is missing.

**Which chain.**  T88's `RBM.Gauss.stochDom_flucAvg_Sblk` /
`RBM.Gauss.stochDom_flucAvg_blockAvg` are *not* used: their hypothesis `hsmall` is an
arithmetic statement about the sizes of the `RBM.Gauss.FlucBound` parameters which T87 showed
the deterministic envelope cannot give, and T94 showed is false as stated.  The route taken
here is T94's iterated one — `RBM.Gauss.integral_norm_flucAvg_pow_le_iter` — whose only input
is `RBM.Gauss.FlucGain`, restated at every time of the flow interval with `N`-dependent but
`u`-independent parameters.  That restatement is free: the iterated moment bound is a
*per-`N`, per-`u` deterministic inequality* whose eventual-in-`N` part (`hcardA`, a statement
about `#supp t_k`) does not see the time at all.

**Why a moment argument suffices here although `RBM.Gauss.stochDom_timeIcc_of_unifDom` needs a
net.**  `RBM.Gauss.UnifDomIcc` bounds the probability *per index and per time*; the union over
the uncountably many `u` is taken only by `RBM.StochDom`, which is what the net engine above
produces.  So Markov applies verbatim, with no cardinality hypothesis at all
(`RBM.Gauss.unifDomIcc_of_moment`); what has to be uniform in `u` is the *threshold in `N`*,
and that is exactly what the iterated bound delivers.

**The control.**  The iteration controls the fluctuation average by the deterministic `ρ B`,
while (4.5) asks for the random `L^max_u`.  The bridge is `RBM.Gauss.unifDomIcc_const_Lmax`:
on the flow good event `W^{-1}/4 ≤ L^max_u` at every time (the *lower* half of T119's
sandwich, the half that survives `t_N → 1`), so the comparison holds as soon as `W ρ B` is
`N^{o(1)}` — which is the paper's size `ρ B ≍ Ψ² ≍ W^{-1}`.  This is the `Ψ² → L^max` step
T88/T119 left open, and on the good event it is free.

**What is still missing, precisely.**

* `hfixRow`, `hfixBlk`: discharged from `RBM.Gauss.FlucGain` at `ρ ≤ 1`, uniformly in
  `u ∈ [s_N, t_N]` (`RBM.Gauss.unifDomIcc_flucRow_condExpDiag`,
  `RBM.Gauss.unifDomIcc_flucBlk_condExpDiag`).  `FlucGain` at the paper's `ρ ≍ Ψ` is *not* a
  theorem: T110 reduces it to `RBM.Gauss.MinorDiffGain` and T113 proves the latter's estimate
  only for words of **bounded length** (`RBM.Gauss.integral_prod_applyOps_minorDiff_le`, with
  a constant `minorDiffC M` that grows in the length bound `M`), and shows the unbounded form
  cannot hold.  The bounded-length estimate cannot currently be threaded into this file,
  because `RBM.Gauss.norm_integral_prod_epsHom_flucDiag_le` and
  `RBM.Gauss.integral_norm_flucAvg_pow_le_iter` consume `RBM.Gauss.FlucGain` for *all* words
  even though the words they build have length at most `2p`.  Closing that gap is an edit to
  `RBM1D/Gauss/FlucIter.lean` (a length-indexed gain interface), not to this file.
* `hfixIBP`: **not** discharged.  Its fixed-time producer
  `RBM.Gauss.condExpDiag_stochDom_of_highProb` is a `RBM.StochDom` at one time whose
  eventual-in-`N` threshold is not known to be uniform in that time (it runs through
  `RBM.Gauss.stochDom_condRow_of_envelope`, `RBM.Gauss.condStable_Lmax` and
  `RBM.Gauss.stochDom_normSq_green_diag_sub_Lmax`, each of which quantifies `∀ᶠ N` after
  fixing `t`), and it still carries `hΩ` at that time.  A `RBM.Gauss.UnifDomIcc` version of
  it is what the IBP slot needs; the `hΩ` half is T130.
-/

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

/-- **(4.12) at every time of the flow interval**, as a `RBM.Gauss.UnifDomIcc` with the
deterministic control `ρ B`.

This is `RBM.Gauss.stochDom_flucAvg_iter` (T94) made uniform in `u ∈ [s_N, t_N]`, with the
spectral parameter moving with the time (`z = z_u`, as the flow requires).  Nothing but the
`FlucGain` hypothesis has to be restated: the iterated moment estimate
`RBM.Gauss.integral_norm_flucAvg_pow_le_iter` is a deterministic inequality at each `(N, u)`,
and the only eventually-in-`N` hypothesis, `hcardA`, does not mention the time. -/
theorem unifDomIcc_flucAvg_iter {V : ℕ → Type*} (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Tw : ∀ N, V N → d.Idx N → ℝ} {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (d.Idx N)}
    {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1) (hcρ : ∀ N, cw N ≤ ep N ^ 2)
    (hw : ∀ N (a : V N), UniformWeight (Tw N a) (cw N) (Aw N a))
    (hcardA : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ a : V N, 2 * p ≤ (Aw N a).card) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖)
      (fun N _ _ _ => ep N * Bp N) := by
  refine unifDomIcc_of_moment (fun N => hpos N) (fun p N u hu a => ?_) ?_
  · exact integrable_norm_flucAvg_pow
      (flucBound_env hE (lt_of_le_of_lt hu.2 (ht1 N)) d N u).flucDiag_le p
  · intro ε hε p
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1)) ^ (2 * p) + 1,
      by positivity, ?_⟩
    filter_upwards [hcardA p, eventually_ge_atTop 1] with N h2 hN1 u hu a
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hrw : (fun ω => |‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖| ^ (2 * p))
        = fun ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) := by
      funext ω; rw [abs_norm]
    rw [hrw]
    have hmain := integral_norm_flucAvg_pow_le_iter hE hu1 (hg N u hu) (hρ1 N) (hcρ N)
      (hw N a) (h2 a)
    have hNe : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
    have hBρ : (0 : ℝ) ≤ ep N * Bp N :=
      mul_nonneg (hg N u hu).rho_nonneg (hg N u hu).B_nonneg
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1)) ^ (2 * p) := by positivity
    have hsplit : ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp N) ^ (2 * p)
        = ((2 : ℝ) ^ (2 * p - 1)) ^ (2 * p) * (ep N * Bp N) ^ (2 * p) := by
      rw [← mul_pow]; ring_nf
    rw [hsplit] at hmain
    have hstep : ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
          * (((2 : ℝ) ^ (2 * p - 1)) ^ (2 * p) * (ep N * Bp N) ^ (2 * p))
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) * ((2 : ℝ) ^ (2 * p - 1)) ^ (2 * p) + 1)
          * ((N : ℝ) ^ (ε * p) * (ep N * Bp N) ^ (2 * p)) := by
      have hpow : (0 : ℝ) ≤ (ep N * Bp N) ^ (2 * p) := pow_nonneg hBρ _
      nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]
    refine le_trans (le_trans hmain (le_of_eq ?_)) hstep
    ring

/-- **(4.12) for the block average `t_k = W⁻¹ 1(k ∈ I_a)`, at every time of the flow
interval.** -/
theorem unifDomIcc_flucAvg_blockAvg_iter (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ _ _ => ep N * Bp N) :=
  unifDomIcc_flucAvg_iter (V := fun N => ZMod (d.L N)) d hE ht1 hg hpos hρ1 hcρ
    (fun N a => uniformWeight_blockAvg a)
    (fun p => by
      filter_upwards [eventually_le_W d (2 * p)] with N hN a
      rw [card_blockAvg_support]; exact hN)

/-- **(4.12) for the variance-profile row `t_k = S_{ik}`, at every time of the flow
interval.** -/
theorem unifDomIcc_flucAvg_Sblk_iter (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ _ _ => ep N * Bp N) :=
  unifDomIcc_flucAvg_iter (V := fun N => d.Idx N) d hE ht1 hg hpos hρ1 hcρ
    (fun N i => uniformWeight_Sblk i)
    (fun p => by
      filter_upwards [eventually_le_W d (2 * p)] with N hN i
      rw [card_Sblk_support]
      omega)

/-- **The `Ψ² → L^max` bridge, uniformly in the time.**

The iteration controls the fluctuation average by a *deterministic* `Φ = ρ B`, while (4.5) asks
for the random `L^max_u`.  On the flow good event the lower half of T119's sandwich,
`W^{-1}/4 ≤ L^max_u` (`RBM.Gauss.inv_W_le_Lmax_flow`), holds at **every** time, and it costs no
power of `η^{-1}`; so the comparison is free as soon as `W Φ` is sub-polynomial, which is the
hypothesis `hΦW`.  At the paper's size `Φ = ρ B ≍ Ψ² ≍ W^{-1}` the product `W Φ` is bounded.

Note that the *upper* half `L^max_u ≤ η^{-2} W^{-1}` is not used, exactly as in the rest of
this file: it is the half that fails when `t_N → 1`. -/
theorem unifDomIcc_const_Lmax {V : ℕ → Type*} (d : Dims) {δ : ℕ → ℝ} {Φ : ℕ → ℝ}
    (hE : |E| ≤ 2) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, 4 * ((d.W N : ℕ) : ℝ) * Φ N ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t (fun N _ (_ : V N) _ => Φ N)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
  intro τ hτ D hD
  filter_upwards [hΩ D hD, hΦW τ hτ, hδ1, eventually_ge_atTop 1] with N hΩN hΦN hδN hN1 u hu a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpow : (0 : ℝ) < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNpos τ
  have hW0 : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
  have hsub : {ω | (N : ℝ) ^ τ * Lmax (Hflow d N u ω) (zt E u) < Φ N}
      ⊆ (goodSetFlow d E s t δ N)ᶜ := by
    intro ω hω hgood
    simp only [Set.mem_ofPred_eq] at hω
    have hlow := inv_W_le_Lmax_flow (δ := δ) hE hδN hgood hu
    have h1 : (1 : ℝ) ≤ 4 * Lmax (Hflow d N u ω) (zt E u) * ((d.W N : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hlow hW0.le
      rwa [inv_mul_cancel₀ hW0.ne'] at h
    have h2 : (N : ℝ) ^ τ
        ≤ (N : ℝ) ^ τ * (4 * Lmax (Hflow d N u ω) (zt E u) * ((d.W N : ℕ) : ℝ)) := by
      nlinarith
    nlinarith [hΦN.trans h2, hW0]
  exact (measure_mono hsub).trans hΩN

/-- **`hfixRow`**: the fixed-time input of `RBM.Gauss.FlucRowFlow`, uniformly in the time, in
exactly the shape `RBM.Gauss.flucRowFlow_of_unifDom` consumes, with the conditional expectation
`RBM.Gauss.condExpDiag` in the `y` slot. -/
theorem unifDomIcc_flucRow_condExpDiag (d : Dims) {δ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bp N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) :=
  (unifDomIcc_flucAvg_Sblk_iter d hE ht1 hg hpos hρ1 hcρ).trans
    (unifDomIcc_const_Lmax (V := fun N => d.Idx N) d hE.le hδ1 hΩ hΦW)

/-- **`hfixBlk`**: the fixed-time input of `RBM.Gauss.FlucBlkFlow`, uniformly in the time. -/
theorem unifDomIcc_flucBlk_condExpDiag (d : Dims) {δ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bp N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) :=
  (unifDomIcc_flucAvg_blockAvg_iter d hE ht1 hg hpos hρ1 hcρ).trans
    (unifDomIcc_const_Lmax (V := fun N => ZMod (d.L N)) d hE.le hδ1 hΩ hΦW)

/-- **`RBM.Gauss.FlucRowFlow` from the gain interface.**

The probe that the fixed-time input produced above really fills the `hfix` slot of
`RBM.Gauss.flucRowFlow_of_unifDom`: no `convert`, no coercion, and the `y` of (4.5) is the
conditional expectation `RBM.Gauss.condExpDiag`, as in T88's fixed-time assembly.  What is left
is `hHol` (the modulus in the time, T129) and `hΩ` (T130); the fixed-time content is now the
single hypothesis `hg`. -/
theorem flucRowFlow_of_gain (d : Dims) {δ : ℕ → ℝ} {K : ℝ} (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bp N) ≤ (N : ℝ) ^ τ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                  - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                  - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    FlucRowFlow (sample d) E s t
      (fun N u ω i => condExpDiag d N (u : ℝ) (zt E (u : ℝ)) (mE E) i ω) :=
  flucRowFlow_of_unifDom (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
    d hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hHol
    (unifDomIcc_flucRow_condExpDiag d hE ht1 hg hpos hρ1 hcρ hδ1 hΩ hΦW)

/-- **`RBM.Gauss.FlucBlkFlow` from the gain interface.**  The block-average half of
`RBM.Gauss.flucRowFlow_of_gain`; the size hypothesis on the gain is `W⁻¹ ≤ ρ²` instead of
`(3W)⁻¹ ≤ ρ²`. -/
theorem flucBlkFlow_of_gain (d : Dims) {δ : ℕ → ℝ} {K : ℝ} (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bp N) ≤ (N : ℝ) ^ τ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                  - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                  - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    FlucBlkFlow (sample d) E s t
      (fun N u ω i => condExpDiag d N (u : ℝ) (zt E (u : ℝ)) (mE E) i ω) :=
  flucBlkFlow_of_unifDom (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
    d hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hHol
    (unifDomIcc_flucBlk_condExpDiag d hE ht1 hg hpos hρ1 hcρ hδ1 hΩ hΦW)


/-! #### The same inputs, against the **graded** gain interface — T151

`RBM.Gauss.FlucGain` at the paper's size `ρ ≍ Ψ` is *not* a theorem, and T137/T142 do not
prove it: what they prove is the word-length-graded `RBM.Gauss.FlucGainUpTo … M`
(`RBM.Gauss.flucGainUpTo_of_minorDiff'`, with `ρ = 2Ψ` and `B = 2Ψ + 2 minorDiffC(M) Ψ`).  The
producers above consume the ungraded interface, so they currently have no supply.  This block
re-derives them from the graded one, following `RBM.Gauss.momentDom_flucAvg_iter_graded`: the
`2p`-th moment of (4.12) only ever builds words of length `≤ 2p`
(`RBM.Gauss.OpsOkOut.length_le`), so a gain valid up to `M = 2p` at each `p` is enough, and the
grade-dependence of `B` is confined to a factor `Kp p` — which the constant of
`RBM.Gauss.unifDomIcc_of_moment`, allowed to depend on `p`, absorbs.  The control is the
`p`-independent `ep N * Bm N`.

Nothing is weakened: the conclusions are literally those of the unprimed versions, and the
unprimed ones remain available through `RBM.Gauss.FlucGain.upTo`.

`RBM.Gauss.eq45Flow_of_localLaw_gain` (`RBM1D/Gauss/CondStableFlow.lean`) touches its `hg`
**only** through `RBM.Gauss.unifDomIcc_flucRow_condExpDiag` and
`RBM.Gauss.unifDomIcc_flucBlk_condExpDiag`, and the intermediate
`RBM.Gauss.eq45Flow_of_unifDom_ibp` takes those two as plain `RBM.Gauss.UnifDomIcc`
hypotheses.  So the primed producers below plug into that intermediate verbatim, and the
primed consumer is the three-line composition — it lives in `CondStableFlow.lean` only
because that is where `eq45Flow_of_unifDom_ibp` is.
-/

/-- **(4.12) at every time of the flow interval, from the graded gain.**  The primed form of
`RBM.Gauss.unifDomIcc_flucAvg_iter`: only `FlucGainUpTo … (2 * p)` is asked for at each `p`,
with the grade-dependent size factored as `Bp p N ≤ Kp p * Bm N`. -/
theorem unifDomIcc_flucAvg_iter' {V : ℕ → Type*} (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Tw : ∀ N, V N → d.Idx N → ℝ} {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (d.Idx N)}
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1) (hcρ : ∀ N, cw N ≤ ep N ^ 2)
    (hw : ∀ N (a : V N), UniformWeight (Tw N a) (cw N) (Aw N a))
    (hcardA : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ a : V N, 2 * p ≤ (Aw N a).card) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖)
      (fun N _ _ _ => ep N * Bm N) := by
  refine unifDomIcc_of_moment (fun N => hpos N) (fun p N u hu a => ?_) ?_
  · exact integrable_norm_flucAvg_pow
      (flucBound_env hE (lt_of_le_of_lt hu.2 (ht1 N)) d N u).flucDiag_le p
  · intro ε hε p
    have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) :=
      pow_nonneg (mul_nonneg (by positivity) (hKp p)) _
    have hc1 : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) := by positivity
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) := mul_nonneg hc1 hK0
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
      * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [hcardA p, eventually_ge_atTop 1] with N h2 hN1 u hu a
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hrw : (fun ω => |‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖| ^ (2 * p))
        = fun ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) := by
      funext ω; rw [abs_norm]
    rw [hrw]
    have hmain := integral_norm_flucAvg_pow_le_iter_graded hE hu1 (hg p N u hu) le_rfl
      (hρ1 N) (hcρ N) (hw N a) (h2 a)
    have hep0 : (0 : ℝ) ≤ ep N := (hg p N u hu).rho_nonneg
    have hBp0 : (0 : ℝ) ≤ Bp p N := (hg p N u hu).B_nonneg
    have hstep1 : ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
        ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N
          ≤ (2 : ℝ) ^ (2 * p - 1) * ep N * (Kp p * Bm N) :=
            mul_le_mul_of_nonneg_left (hBK p N) (by positivity)
        _ = ((2 : ℝ) ^ (2 * p - 1) * Kp p) * (ep N * Bm N) := by ring
    have hmain2 : ∫ ω, ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) ∂(P d)
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
            * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p)) * (ep N * Bm N) ^ (2 * p) := by
      refine le_trans hmain ?_
      calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * (((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p)) :=
            mul_le_mul_of_nonneg_left hstep1 hc1
        _ = _ := by ring
    have hNe : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
    have hpow : (0 : ℝ) ≤ (ep N * Bm N) ^ (2 * p) :=
      pow_nonneg (mul_nonneg hep0 (hBm N)) _
    refine le_trans hmain2 ?_
    nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]

/-- **(4.12) for the block average, from the graded gain, at every time of the flow.** -/
theorem unifDomIcc_flucAvg_blockAvg_iter' (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ _ _ => ep N * Bm N) :=
  unifDomIcc_flucAvg_iter' (V := fun N => ZMod (d.L N)) d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ
    (fun N a => uniformWeight_blockAvg a)
    (fun p => by
      filter_upwards [eventually_le_W d (2 * p)] with N hN a
      rw [card_blockAvg_support]; exact hN)

/-- **(4.12) for the variance-profile row, from the graded gain, at every time of the
flow.** -/
theorem unifDomIcc_flucAvg_Sblk_iter' (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ _ _ => ep N * Bm N) :=
  unifDomIcc_flucAvg_iter' (V := fun N => d.Idx N) d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ
    (fun N i => uniformWeight_Sblk i)
    (fun p => by
      filter_upwards [eventually_le_W d (2 * p)] with N hN i
      rw [card_Sblk_support]
      omega)

/-- **`hfixRow` from the graded gain.**  The primed form of
`RBM.Gauss.unifDomIcc_flucRow_condExpDiag`; the conclusion is literally the same. -/
theorem unifDomIcc_flucRow_condExpDiag' (d : Dims) {δ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bm N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) :=
  (unifDomIcc_flucAvg_Sblk_iter' d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ).trans
    (unifDomIcc_const_Lmax (V := fun N => d.Idx N) d hE.le hδ1 hΩ hΦW)

/-- **`hfixBlk` from the graded gain.**  The primed form of
`RBM.Gauss.unifDomIcc_flucBlk_condExpDiag`. -/
theorem unifDomIcc_flucBlk_condExpDiag' (d : Dims) {δ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bm N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) :=
  (unifDomIcc_flucAvg_blockAvg_iter' d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ).trans
    (unifDomIcc_const_Lmax (V := fun N => ZMod (d.L N)) d hE.le hδ1 hΩ hΦW)

/-! ##### The numeric bundles at the paper's size `ρ B ≍ Ψ²`

T142 brings the graded gain to `ρ = 2Ψ`, `B ≤ Kp p · Ψ`, hence to the control
`Φ = ρ B = 2 Ψ²`.  At that size the two numeric side conditions of the block above are no
longer independent hypotheses:

* `hΦW` (`4 W Φ ≤ N^τ`) **follows from** `hΨW` (`4 W Ψ² ≤ N^τ`), which
  `RBM.Gauss.eq45Flow_of_localLaw_gain` already assumes — one `τ/2` split and `2 ≤ N^{τ/2}`;
* `hcρ` at both sizes `W⁻¹` and `(3W)⁻¹` follows from the single `W⁻¹ ≤ 4 Ψ²`, because
  `ρ² = 4Ψ²`.

So the re-derivation asked for by T147 §6(b)④ is a *net removal* of hypotheses, not a
replacement: this is the "negative cost to producers" T142 reports, seen from the consumer
side. -/

/-- **`hΦW` at the paper's size, from `hΨW`.**  With `ρ B = 2 Ψ²` the sub-polynomial bound on
`W ρ B` needed by `RBM.Gauss.unifDomIcc_const_Lmax` is the one on `W Ψ²` that (4.5) already
carries. -/
theorem flucPhiW_of_psiW (d : Dims) {Ψ : ℕ → ℝ}
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (2 * Ψ N * Ψ N) ≤ (N : ℝ) ^ τ := by
  intro τ hτ
  have hτ2 : (0 : ℝ) < τ / 2 := half_pos hτ
  filter_upwards [hΨW (τ / 2) hτ2, eventually_le_rpow 2 hτ2, eventually_ge_atTop 1]
    with N hN h2 hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc 4 * ((d.W N : ℕ) : ℝ) * (2 * Ψ N * Ψ N)
      = 2 * (4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N)) := by ring
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        exact mul_le_mul h2 hN (by nlinarith [hN, h2]) hnn
    _ = (N : ℝ) ^ τ := hsplit

/-- **`hfixRow` at the paper's size.**  `RBM.Gauss.unifDomIcc_flucRow_condExpDiag'` with
T142's parameters `ρ = 2Ψ`, `Bm = Ψ`: the control is `2Ψ²`, `hΦW` is gone (it is
`RBM.Gauss.flucPhiW_of_psiW` applied to the `hΨW` of (4.5)), and the two `hcρ` conditions
collapse to `W⁻¹ ≤ 4Ψ²`. -/
theorem unifDomIcc_flucRow_condExpDiag_psi (d : Dims) {δ Ψ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨlow : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
  have hW : ∀ N, (0 : ℝ) < (d.W N : ℝ) := fun N => by exact_mod_cast d.W_pos N
  have hpos : ∀ N, (0 : ℝ) < 2 * Ψ N * Ψ N := fun N => by nlinarith [hΨpos N]
  have hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ (2 * Ψ N) ^ 2 := by
    intro N
    have h3 : ((3 * d.W N : ℝ))⁻¹ ≤ ((d.W N : ℝ))⁻¹ := by
      have hw := hW N
      rw [inv_le_inv₀ (by linarith) hw]
      linarith
    have hl := hΨlow N
    nlinarith [hl, h3]
  have hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (2 * Ψ N * Ψ N) ≤ (N : ℝ) ^ τ := flucPhiW_of_psiW d hΨW
  exact unifDomIcc_flucRow_condExpDiag' (Bm := Ψ) (Kp := Kp) (ep := fun N => 2 * Ψ N)
    d hE ht1 hg hKp (fun N => (hΨpos N).le) hBK hpos hΨhalf hcρ hδ1 hΩ hΦW

/-- **`hfixBlk` at the paper's size.**  The block-average half of
`RBM.Gauss.unifDomIcc_flucRow_condExpDiag_psi`. -/
theorem unifDomIcc_flucBlk_condExpDiag_psi (d : Dims) {δ Ψ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨlow : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
  have hpos : ∀ N, (0 : ℝ) < 2 * Ψ N * Ψ N := fun N => by nlinarith [hΨpos N]
  have hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ (2 * Ψ N) ^ 2 := fun N => by nlinarith [hΨlow N]
  have hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (2 * Ψ N * Ψ N) ≤ (N : ℝ) ^ τ := flucPhiW_of_psiW d hΨW
  exact unifDomIcc_flucBlk_condExpDiag' (Bm := Ψ) (Kp := Kp) (ep := fun N => 2 * Ψ N)
    d hE ht1 hg hKp (fun N => (hΨpos N).le) hBK hpos hΨhalf hcρ hδ1 hΩ hΦW

/-- **`RBM.Gauss.FlucRowFlow` from the graded gain.**  The primed form of
`RBM.Gauss.flucRowFlow_of_gain`. -/
theorem flucRowFlow_of_gain' (d : Dims) {δ : ℕ → ℝ} {K : ℝ} (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bm N) ≤ (N : ℝ) ^ τ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                  - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                  - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    FlucRowFlow (sample d) E s t
      (fun N u ω i => condExpDiag d N (u : ℝ) (zt E (u : ℝ)) (mE E) i ω) :=
  flucRowFlow_of_unifDom (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
    d hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hHol
    (unifDomIcc_flucRow_condExpDiag' d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ hδ1 hΩ hΦW)

/-- **`RBM.Gauss.FlucBlkFlow` from the graded gain.**  The primed form of
`RBM.Gauss.flucBlkFlow_of_gain`. -/
theorem flucBlkFlow_of_gain' (d : Dims) {δ : ℕ → ℝ} {K : ℝ} (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bm N) ≤ (N : ℝ) ^ τ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                  - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                  - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    FlucBlkFlow (sample d) E s t
      (fun N u ω i => condExpDiag d N (u : ℝ) (zt E (u : ℝ)) (mE E) i ω) :=
  flucBlkFlow_of_unifDom (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
    d hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hHol
    (unifDomIcc_flucBlk_condExpDiag' d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ hδ1 hΩ hΦW)


end FlucFix

section FlucEnv

open Filter

variable {E : ℝ} {s t : ℕ → ℝ}

/-! #### The gain hypothesis at `ρ ≤ 1` is inhabited

`RBM.Gauss.flucGain_env` gives `RBM.Gauss.FlucGain` unconditionally, but at `ρ = 2`, which
`RBM.Gauss.unifDomIcc_flucAvg_iter` cannot use (`hρ1` asks for `ρ ≤ 1`).  The three statements
below show that the `ρ ≤ 1` interface is nevertheless inhabited, by moving the whole loss into
`B`: since the rows of a word are distinct, a word carries at most `#Idx(N)` conditional
fluctuations, so the envelope bound `2^{#Q}` is at most `2^{#Idx(N)}` and `ρ = 1` is legitimate
with `B = B_env 2^{#Idx(N)}`.

The resulting control is exponentially large, so the `Ψ² → L^max` bridge
`RBM.Gauss.unifDomIcc_const_Lmax` does **not** apply to it: this is a non-vacuity witness for
the interface, in the sense of `RBM.Gauss.stochDom_flucAvg_blockAvg_env`, and nothing more.  The
content of §4 is the same statement with `ρ ≍ Ψ`. -/

/-- `RBM.Gauss.FlucGain` is monotone in `B`. -/
theorem FlucGain.mono_B {d : Dims} {N : ℕ} {u : ℝ} {z m : ℂ} {B B' ρ : ℝ}
    (h : FlucGain d N u z m B ρ) (hBB : B ≤ B') : FlucGain d N u z m B' ρ := by
  refine ⟨h.B_nonneg.trans hBB, h.rho_nonneg, fun ι _ k L h1 h2 => ?_⟩
  exact (h.gain ι k L h1 h2).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.B_nonneg hBB _)
      (pow_nonneg h.rho_nonneg _))

/-- **The `ρ ≤ 1` gain interface is inhabited**: the deterministic envelope gives it with
`ρ = 1` and `B = 2(η_u⁻¹ + 1) 2^{#Idx(N)}`, because a word with distinct rows carries at most
`#Idx(N)` letters. -/
theorem flucGain_one_env (d : Dims) (N : ℕ) (hE : |E| < 2) {u : ℝ} (hu : u < 1) :
    FlucGain d N u (zt E u) (mE E)
      (2 * ((etaT E u)⁻¹ + 1) * 2 ^ Fintype.card (d.Idx N)) 1 := by
  classical
  have hη : 0 < etaT E u := etaT_pos_of_lt_one hE hu
  set Benv : ℝ := 2 * ((etaT E u)⁻¹ + 1) with hBenv
  have hBenv0 : 0 ≤ Benv := by rw [hBenv]; positivity
  refine ⟨by positivity, zero_le_one, fun ι _ k L h1 h2 => ?_⟩
  have hb : ∀ (i : ι) (ω : Ω d),
      ‖applyOps d N (L i) (flucDiag d N u (zt E u) (mE E) (k i)) ω‖
        ≤ Benv * 2 ^ Fintype.card (d.Idx N) := by
    intro i ω
    have h := norm_applyOps_le (L i)
      (fun ω' => norm_flucDiag_le (norm_greenDiagCentered_le_env hE hu u (k i)) ω') ω
    have hlen : numQ (L i) ≤ Fintype.card (d.Idx N) := by
      refine le_trans List.countP_le_length ?_
      have hn := (h1 i).length_le_card
      rwa [List.length_map] at hn
    have hpow : (2 : ℝ) ^ numQ (L i) ≤ 2 ^ Fintype.card (d.Idx N) :=
      pow_le_pow_right₀ one_le_two hlen
    calc ‖applyOps d N (L i) (flucDiag d N u (zt E u) (mE E) (k i)) ω‖
        ≤ 2 ^ numQ (L i) * Benv := h
      _ ≤ 2 ^ Fintype.card (d.Idx N) * Benv := mul_le_mul_of_nonneg_right hpow hBenv0
      _ = Benv * 2 ^ Fintype.card (d.Idx N) := by ring
  refine le_trans (integral_prod_norm_le_of_bounds
    (b := fun _ : ι => Benv * 2 ^ Fintype.card (d.Idx N))
    (fun i => (bddMeas_flucDiag hE hu u (k i)).applyOps (L i)) hb) (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, one_pow, mul_one]

/-- `RBM.Gauss.flucGain_one_env` with a time-independent `B`, i.e. in the shape the `hg` of
`RBM.Gauss.unifDomIcc_flucAvg_iter` asks for.  `η_u ≥ η_{t_N}` on the flow interval, so the
envelope at the right endpoint dominates. -/
theorem flucGain_one_env_flow (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1) (N : ℕ) :
    ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E)
      (2 * ((etaT E (t N))⁻¹ + 1) * 2 ^ Fintype.card (d.Idx N)) 1 := by
  intro u hu
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  refine (flucGain_one_env d N hE hu1).mono_B ?_
  have h1 : etaT E (t N) ≤ etaT E u := etaT_le_of_le hE hu.2
  have h2 : 0 < etaT E (t N) := etaT_pos_of_lt_one hE (ht1 N)
  have h3 : (etaT E u)⁻¹ ≤ (etaT E (t N))⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le h2 h1
  have h4 : (0 : ℝ) < 2 ^ Fintype.card (d.Idx N) := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith) h4.le

/-- **The `u`-uniform (4.12) is not vacuous**: unconditionally, the block average is dominated
uniformly on the flow interval — by an exponentially large constant.  Its only role is the one
`RBM.Gauss.stochDom_flucAvg_blockAvg_env` plays for T88: every step of
`RBM.Gauss.unifDomIcc_flucAvg_blockAvg_iter` is a theorem, and what the paper's (4.12) needs on
top of it is the *size* of the gain, `ρ ≍ Ψ`. -/
theorem unifDomIcc_flucAvg_blockAvg_env (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ _ _ =>
        1 * (2 * ((etaT E (t N))⁻¹ + 1) * 2 ^ Fintype.card (d.Idx N))) :=
  unifDomIcc_flucAvg_blockAvg_iter d hE ht1 (flucGain_one_env_flow d hE ht1)
    (fun N => by
      have hη : 0 < etaT E (t N) := etaT_pos_of_lt_one hE (ht1 N)
      positivity)
    (fun _ => le_refl 1)
    (fun N => by
      have hW : (1 : ℝ) ≤ ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
      rw [one_pow, inv_le_one₀ (by linarith)]
      exact hW)

end FlucEnv

/-! ### Split threshold and mesh for the time net — T279 -/

open scoped Matrix.Norms.L2Operator

/-- The primed slow-variation estimate uses `δ` only for the good-event threshold and
`μ` only for the time spacing.  The old declaration is kept unchanged. -/
theorem Lmax_flow_slow_of_net' {V : ℕ → Type*} (d : Dims) {E : ℝ} {s t δ μ : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hμ0 : ∀ N, 0 ≤ μ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hμ1 : ∀ᶠ N : ℕ in atTop, μ N ≤ 1)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ _a : V N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N), |u - v| ≤ μ N →
        Lmax (Hflow d N v ω) (zt E v) ≤ (N : ℝ) ^ ε * Lmax (Hflow d N u ω) (zt E u) := by
  intro ε hε
  filter_upwards [hδ1, hμ1, hfine, rpow_neg_le_Lmax_flow (E := E) (s := s) (t := t) d hE.le hδ1,
    eventually_le_rpow 2 hε, eventually_ge_atTop 1]
    with N hδN hμN hfineN hlowN h2N hN1 ω hω _a u hu v hv huv
  obtain ⟨hωΩ, hωX⟩ := hω
  set η : ℝ := etaT E (t N) with hη_def
  have hηpos : 0 < η := etaT_pos_of_lt_one' hE (ht1 N)
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
  have hu0 : (0 : ℝ) ≤ u := (hs0 N).trans hu.1
  have hv0 : (0 : ℝ) ≤ v := (hs0 N).trans hv.1
  have hiu : (etaT E u)⁻¹ ≤ η⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hηpos (etaT_le_of_le hE hu.2)
  have hiv : (etaT E v)⁻¹ ≤ η⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hηpos (etaT_le_of_le hE hv.2)
  have hiu0 : (0 : ℝ) < (etaT E u)⁻¹ := by
    have := etaT_pos_of_lt_one' hE hu1; positivity
  have hiv0 : (0 : ℝ) < (etaT E v)⁻¹ := by
    have := etaT_pos_of_lt_one' hE hv1; positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set dh : ℝ := μ N ^ ((1 : ℝ) / 2) with hdh_def
  have hdh0 : (0 : ℝ) ≤ dh := Real.rpow_nonneg (hμ0 N) _
  -- the middle factor of the resolvent modulus
  have hmid : |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v| ≤ 2 * (N : ℝ) * dh := by
    have hd1 : |u - v| ≤ 1 := huv.trans hμN
    have h1 : |Real.sqrt u - Real.sqrt v| ≤ |u - v| ^ ((1 : ℝ) / 2) := by
      have h := RBM.abs_sqrt_sub_sqrt_le hu0 hv0
      rwa [show Real.sqrt |u - v| = |u - v| ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow _] at h
    have h2 : |u - v| ≤ |u - v| ^ ((1 : ℝ) / 2) := self_le_rpow_half (abs_nonneg _) hd1
    have h3 : |u - v| ^ ((1 : ℝ) / 2) ≤ dh :=
      Real.rpow_le_rpow (abs_nonneg _) huv (by norm_num)
    have hX0 : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
    have hXN : ‖Xmat d N ω‖ ≤ (N : ℝ) := hωX
    nlinarith [h1, h2, h3, hX0, hXN, hdh0]
  have hm0 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v| := by
    have h1 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ := by positivity
    linarith [abs_nonneg (u - v)]
  -- the resolvent modulus, with every `η_u` replaced by `η`
  have hΔ : ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖
      ≤ η⁻¹ * (2 * (N : ℝ) * dh) * η⁻¹ := by
    refine (norm_green_flow_sub_le d N hE hu1 hv1 ω).trans ?_
    gcongr
  have hΔ0 : (0 : ℝ) ≤ ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖ :=
    norm_nonneg _
  -- the total error
  have herr : Lmax (Hflow d N v ω) (zt E v)
      ≤ Lmax (Hflow d N u ω) (zt E u) + 4 * (η⁻¹) ^ 3 * (N : ℝ) * dh := by
    refine (Lmax_flow_le_add d N hE hu1 hv1 ω).trans ?_
    have hfirst : (etaT E u)⁻¹ + (etaT E v)⁻¹ ≤ 2 * η⁻¹ := by linarith
    have h2η : (0 : ℝ) ≤ 2 * η⁻¹ := by positivity
    have hstep : ((etaT E u)⁻¹ + (etaT E v)⁻¹)
        * ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖
        ≤ (2 * η⁻¹) * (η⁻¹ * (2 * (N : ℝ) * dh) * η⁻¹) :=
      mul_le_mul hfirst hΔ hΔ0 h2η
    have heq : (2 * η⁻¹) * (η⁻¹ * (2 * (N : ℝ) * dh) * η⁻¹) = 4 * (η⁻¹) ^ 3 * (N : ℝ) * dh := by
      ring
    linarith [hstep, heq ▸ hstep]
  -- the error is below `N^{-2} ≤ L^max_u`
  have hNsq : (0 : ℝ) < (N : ℝ) ^ (2 : ℕ) := by positivity
  have hprod : (4 * (η⁻¹) ^ 3 * (N : ℝ) * dh) * (N : ℝ) ^ (2 : ℕ) ≤ 1 := by
    calc (4 * (η⁻¹) ^ 3 * (N : ℝ) * dh) * (N : ℝ) ^ (2 : ℕ)
        = 4 * (η⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * dh := by ring
      _ ≤ 1 := hfineN
  have hsmall : 4 * (η⁻¹) ^ 3 * (N : ℝ) * dh ≤ ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hprod (le_of_lt (inv_pos.2 hNsq))
    rwa [mul_assoc, mul_inv_cancel₀ hNsq.ne', mul_one, one_mul] at hstep
  have hlow : ((N : ℝ) ^ (2 : ℕ))⁻¹ ≤ Lmax (Hflow d N u ω) (zt E u) := by
    have h := hlowN ω hωΩ u hu
    have hrw : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hNpos.le, ← Real.rpow_natCast (N : ℝ) 2]
      norm_num
    rwa [hrw] at h
  have hL0 : 0 ≤ Lmax (Hflow d N u ω) (zt E u) := Lmax_nonneg (Hflow_isHermitian d N u ω)
  nlinarith [herr, hsmall, hlow, hL0, h2N]


/-- The `Lmax` net engine with independent good-event threshold `δ` and time spacing `μ`. -/
theorem stochDom_timeIcc_Lmax_of_unifDom' {V : ℕ → Type*} [∀ N, Fintype (V N)] (d : Dims)
    {E : ℝ} {s t δ μ : ℕ → ℝ} {K : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ))
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hμ0 : ∀ N, 0 ≤ μ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hμ1 : ∀ᶠ N : ℕ in atTop, μ N ≤ 1)
    (hμnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ μ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {ξ : ∀ N, ℝ → V N → Ω d → ℝ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : V N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |ξ N u a ω - ξ N v a ω| ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t ξ (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × V N)
      (fun N p ω => ξ N (p.1 : ℝ) p.2 ω)
      (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))) := by
  refine stochDom_timeIcc_of_unifDom (δ := μ) hcard hst one_pos ?_ hK (by norm_num : (0:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) < (1:ℝ)/2) ?_ hμnet (highProb_flowNetEvent d hΩ) hHol ?_
    (Lmax_flow_slow_of_net' (V := V) d hE hs0 ht1 hμ0 hδ1 hμ1 hfine) hfix
  · intro N; have h1 := hs0 N; have h2 := (ht1 N).le; linarith
  · intro N u a ω; exact Lmax_nonneg (Hflow_isHermitian d N u ω)
  · filter_upwards [rpow_neg_le_Lmax_flow (E := E) (s := s) (t := t) d hE.le hδ1]
      with N hN ω hω a u hu
    exact hN ω hω.1 u hu


/-- The three flow inputs with the time mesh `μ` separated from the event threshold `δ`. -/
theorem ibpFlow_of_unifDom' (d : Dims)
    {E : ℝ} {s t δ μ : ℕ → ℝ} {K : ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hμ0 : ∀ N, 0 ≤ μ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hμ1 : ∀ᶠ N : ℕ in atTop, μ N ≤ 1)
    (hμnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ μ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖y N u ω i - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖y N v ω i - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖y N u ω i - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    IBPFlow (sample d) E s t (fun N u ω i => y N (u : ℝ) ω i) :=
  stochDom_timeIcc_Lmax_of_unifDom' d (card_Idx_le d) hE hs0 ht1 hst hK hμ0 hδ1 hμ1 hμnet hfine hΩ
    hHol hfix

/-- **`RBM.Gauss.FlucRowFlow`** — (4.12) for `t_k = S_{ik}` with the time in the index set. -/
theorem flucRowFlow_of_unifDom' (d : Dims)
    {E : ℝ} {s t δ μ : ℕ → ℝ} {K : ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hμ0 : ∀ N, 0 ≤ μ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hμ1 : ∀ᶠ N : ℕ in atTop, μ N ≤ 1)
    (hμnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ μ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E) - y N v ω k)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    FlucRowFlow (sample d) E s t (fun N u ω i => y N (u : ℝ) ω i) :=
  stochDom_timeIcc_Lmax_of_unifDom' d (card_Idx_le d) hE hs0 ht1 hst hK hμ0 hδ1 hμ1 hμnet hfine hΩ
    hHol hfix

/-- **`RBM.Gauss.FlucBlkFlow`** — (4.12) for `t_k = W⁻¹ 1(k ∈ I_a)` with the time in the index
set. -/
theorem flucBlkFlow_of_unifDom' (d : Dims)
    {E : ℝ} {s t δ μ : ℕ → ℝ} {K : ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hμ0 : ∀ N, 0 ≤ μ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hμ1 : ∀ᶠ N : ℕ in atTop, μ N ≤ 1)
    (hμnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ μ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    {y : ∀ N, ℝ → Ω d → d.Idx N → ℂ}
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E) - y N v ω k)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfix : UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E) - y N u ω k)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    FlucBlkFlow (sample d) E s t (fun N u ω i => y N (u : ℝ) ω i) :=
  stochDom_timeIcc_Lmax_of_unifDom' d (card_ZMod_L_le d) hE hs0 ht1 hst hK hμ0 hδ1
    hμ1 hμnet hfine hΩ hHol hfix


end RBM.Gauss

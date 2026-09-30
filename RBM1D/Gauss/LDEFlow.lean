/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowInputs
import RBM1D.Gauss.LDEHyp

/-!
# The large deviation estimates (4.2) along the flow: the net engine and the fixed-time input

The large deviation bounds (4.2) are needed with the time *inside* the index set of
`RBM.StochDom`:

`|∑_{k≠i} (H_u)_{ik} G^{(i)}_{kj}(u)|² ≺ ∑_{k≠i} S_{ik} |G^{(i)}_{kj}(u)|²`,

uniformly in `u ∈ [s_N, t_N]` and in `i ≠ j`.

## The obstruction

The net engine `RBM.Gauss.stochDom_timeIcc_of_unifDom` absorbs the net error into
the control through a *polynomial lower bound* `N^{-B} ≤ ζ` (its `hζlow`).  The control of
(4.2), `RBM.ldeRowRHS`, has no such bound: it is a sum of squared entries of a minor Green
function and can be arbitrarily small — indeed it vanishes identically wherever the
corresponding minor entries do.

This file removes that obstruction from the engine and isolates what is left.

## What is here

* `RBM.Gauss.stochDom_timeIcc_of_unifDom_relative` — **a net engine with no lower bound on the
  control.**  The absolute Hölder modulus `hHol` and the lower bound `hζlow` of
  `RBM.Gauss.stochDom_timeIcc_of_unifDom` are replaced by a single *relative* comparison
  `hclose`: at net spacing, `ξ(u) ≤ ξ(v) + ζ(u)` and `ζ(v) ≤ 2 ζ(u)`.  That engine is the special
  case in which `hclose` is deduced from `hHol` and `hζlow`, so nothing is lost.

* `RBM.Gauss.unifDomIcc_rowSum_general`, `RBM.Gauss.unifDomIcc_sq_of_rowSum` — **the row-sum
  input of (4.2) at every fixed time of the flow interval, unconditionally.**  As in
  `RBM1D/Gauss/Eq45FlowInputs.lean`, `RBM.Gauss.UnifDomIcc` takes no union over the index set, so
  the Gaussian row-sum moment bound (`RBM.Gauss.integral_norm_rowSum_norm_pow_le'`, whose
  constant `2(2p-1)!!` does not depend on the time) goes through `RBM.Gauss.unifDomIcc_of_moment`
  with **no cardinality hypothesis and no good event**.

## The remaining input: the relative net comparison for (4.2)

The relative comparison `hclose` for (4.2) is, after Cauchy–Schwarz, a statement about the
*normalised* minor Green column
`w(u) = (G^{(i)}_{· j}(u))|_{band(i)} / ‖·‖`: the Gaussian row `i` is independent of the minor,
so conditionally `ξ(u)/ζ(u) = u |⟨g, w(u)⟩|²` with `⟨g, w(u)⟩` of variance one for every `u`,
and the uniform statement is the supremum of a Gaussian process along the curve `{w(u)}`.  The
crude bound over the whole unit sphere is `∑_k |X_{ik}|²/S_{ik} ≍ W`, which is a power of `N`
too lossy; a chaining argument needs the curve to have polynomially bounded length, i.e.

`‖∂_u (G^{(i)}_{· j}(u))|_{band(i)}‖ ≤ N^K ‖(G^{(i)}_{· j}(u))|_{band(i)}‖`.

The resolvent derivative gives `‖∂_u G^{(i)} e_j‖ ≤ N^K ‖G^{(i)} e_j‖` in the **full** norm at
once, but `ζ` only weighs the band of `i`, and `‖G^{(i)} e_j‖ ≍ η^{-1/2}` while the restriction
to a band far from `j` is exponentially small.  Converting the full-norm bound into the
restricted one is exactly an off-diagonal decay statement for the minor Green function — the
(2.76)/(4.3) input — and is a genuinely separate piece of mathematics, not an accounting step.
So it is not proved here (see `RBM1D/Gauss/LDENetClose.lean` for the floored form).
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset Matrix

/-! ### A net engine that needs no lower bound on the control -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
/-- **The net theorem with a relative comparison in place of a lower bound on the control.**

`RBM.Gauss.stochDom_timeIcc_of_unifDom` pays for the passage from a net of times to the
whole interval with two hypotheses: an absolute Hölder modulus for `ξ`, and a polynomial lower
bound `N^{-B} ≤ ζ` that lets the net error be absorbed into the control.  When the control can
vanish — as `RBM.ldeRowRHS` does — the second is unavailable.

Here both are replaced by `hclose`, which asks only for the *relative* comparison that the
absorption step actually uses: at net spacing `δ N`,

* `ξ N u a ω ≤ ξ N v a ω + ζ N u a ω` (the net error is at most the control at `u`), and
* `ζ N v a ω ≤ 2 * ζ N u a ω` (the control does not grow across one net step).

`A` governs the spacing of the net (`T / N^A`) and is free, so the caller may make the net as
fine as needed. -/
theorem stochDom_timeIcc_of_unifDom_relative {V : ℕ → Type*} [∀ N, Fintype (V N)] {Cv : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ Cv)
    {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T)
    {A : ℝ} (hA : 0 ≤ A) {ξ ζ : ∀ N, ℝ → V N → Ω → ℝ}
    (hζ0 : ∀ N u a ω, 0 ≤ ζ N u a ω)
    {δ : ℕ → ℝ} (hδ : ∀ᶠ N : ℕ in atTop, T / (N : ℝ) ^ A ≤ δ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ a : V N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ v ∈ Set.Icc (s N) (t N), |u - v| ≤ δ N →
        ξ N u a ω ≤ ξ N v a ω + ζ N u a ω ∧ ζ N v a ω ≤ 2 * ζ N u a ω)
    (hfix : UnifDomIcc P s t ξ ζ) :
    StochDom P (U := fun N => RBM.TimeIcc s t N × V N)
      (fun N p ω => ξ N (p.1 : ℝ) p.2 ω) (fun N p ω => ζ N (p.1 : ℝ) p.2 ω) := by
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
  refine stochDom_of_subset_highProb hnet hΞ fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [hclose, hδ, eventually_ge_atTop 1, eventually_le_rpow 3 hτ2]
    with N hcloseN hδN hN1 hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hmge : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := rpow_le_netSize A N
  have hNA : (0 : ℝ) < (N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
  have hspace : T / (netSize A N : ℝ) ≤ T / (N : ℝ) ^ A :=
    div_le_div_of_nonneg_left hT.le hNA hmge
  -- `N^τ ≥ 2 N^{τ/2} + 1`
  have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hgap : 2 * (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by rw [hsplit]; nlinarith [hN3]
  rintro ω ⟨⟨⟨⟨u, hu⟩, a⟩, hbad⟩, hωΞ⟩
  simp only at hbad
  obtain ⟨k, hk⟩ := exists_netTime_close hT hlen A N hu
  set v : ℝ := netTime s t T A N k with hv_def
  have hvmem : v ∈ Set.Icc (s N) (t N) := netTime_mem hst hT.le A N k
  have huv : |u - v| ≤ δ N := le_trans (hk.trans hspace) hδN
  obtain ⟨hξ, hζ⟩ := hcloseN ω hωΞ a u hu v hvmem huv
  refine ⟨(k, a), ?_⟩
  show (N : ℝ) ^ (τ / 2) * ζ N v a ω < ξ N v a ω
  have hζu : (0 : ℝ) ≤ ζ N u a ω := hζ0 N u a ω
  have hζv : (0 : ℝ) ≤ ζ N v a ω := hζ0 N v a ω
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  nlinarith [hbad, hξ, hζ]

end Engine

section Special

variable {Ω : Type*} {V : ℕ → Type*} {s t : ℕ → ℝ} {ξ ζ : ∀ N, ℝ → V N → Ω → ℝ}
variable {δ : ℕ → ℝ} {N : ℕ} {ω : Ω} {a : V N}

end Special

/-! ### (4.2) at every fixed time of the flow interval

The fixed-time half of (4.2) needs neither a net nor a good event: `RBM.Gauss.UnifDomIcc` asks
for the failure probability at each time and each index *separately*, so the only thing that
has to be uniform in `u` is the threshold in `N` — and the Gaussian row-sum moment bound
`RBM.Gauss.integral_norm_rowSum_norm_pow_le'` has the constant `2 (2p-1)!!` at every time. -/

section Fixed

variable {d : Dims} {s t : ℕ → ℝ} {E : ℝ}

/-- **The normalised Gaussian row sums are `≺ 1` at every time of the flow interval.**  The time
is universally quantified, and — because `RBM.Gauss.UnifDomIcc` takes no union — no cardinality
hypothesis is needed.  The coefficients are allowed to depend on the time, as they must: they are
entries of `G^{(i)}_u`. -/
theorem unifDomIcc_rowSum_general (hs0 : ∀ N, 0 ≤ s N) {U : ℕ → Type*}
    (row : ∀ N, U N → d.Idx N) (C : ∀ N, ℝ → U N → Ω d → d.Idx N → ℂ)
    (hCmeas : ∀ N u q, Measurable (C N u q))
    (hC : ∀ N u q (ω ω' : Ω d),
      (∀ c ∈ offRowCoord d N (row N q), ω c = ω' c) → C N u q ω = C N u q ω') :
    UnifDomIcc (P d) s t
      (fun N u q ω => ‖rowSum d N u (row N q) (rowCoeffNorm d N u (row N q) (C N u q)) ω‖)
      (fun _ _ _ _ => 1) := by
  refine unifDomIcc_of_moment (fun _ => zero_lt_one) ?_ ?_
  · intro p N u hu q
    have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
    have := integrable_norm_rowSum_norm_pow (d := d) (N := N) (u := u) (i := row N q)
      (p := p) hu0 (C N u q) (hCmeas N u q) (fun ω ω' h => hC N u q ω ω' h)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [abs_norm]
  · intro ε hε p
    have hd0 : (0 : ℝ) ≤ dfac p := by unfold dfac; positivity
    refine ⟨2 * dfac p + 1, by linarith, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1 u hu q
    have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hbound := integral_norm_rowSum_norm_pow_le' (d := d) (N := N) (u := u)
      (i := row N q) (p := p) hu0 (C N u q) (hCmeas N u q) (fun ω ω' h => hC N u q ω ω' h)
    have habs : ∫ ω, |‖rowSum d N u (row N q)
          (rowCoeffNorm d N u (row N q) (C N u q)) ω‖| ^ (2 * p) ∂(P d)
        = ∫ ω, ‖rowSum d N u (row N q)
            (rowCoeffNorm d N u (row N q) (C N u q)) ω‖ ^ (2 * p) ∂(P d) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [abs_norm]
    rw [habs]
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1' (by positivity)
    have : (2 * dfac p) ≤ (2 * dfac p + 1) * ((N : ℝ) ^ (ε * p) * 1 ^ (2 * p)) := by
      rw [one_pow, mul_one]
      nlinarith [hpow, hd0]
    linarith [hbound, this]

/-- **Squared row sums, uniformly in the time.**  If `A` is the squared row
sum and the conditional variance is `u · B` with `0 ≤ u ≤ 1` and `B ≥ 0`, then `A ≺ B` at every
`u ∈ [s_N, t_N]`, with a threshold in `N` that does not depend on `u`.

The degenerate fibres `B = 0` are the place where a lower bound on the control would otherwise
be needed; they are handled exactly as at a fixed time, by the almost-sure vanishing
`RBM.Gauss.rowSum_ae_eq_zero_of_varSum_eq_zero`, which costs nothing because at this level the
null set may depend on `(N, u, q)`. -/
theorem unifDomIcc_sq_of_rowSum (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N ≤ 1) {U : ℕ → Type*}
    (row : ∀ N, U N → d.Idx N) (C : ∀ N, ℝ → U N → Ω d → d.Idx N → ℂ)
    (hCmeas : ∀ N u q, Measurable (C N u q))
    (hC : ∀ N u q (ω ω' : Ω d),
      (∀ c ∈ offRowCoord d N (row N q), ω c = ω' c) → C N u q ω = C N u q ω')
    {V : ℕ → Type*} (f : ∀ N, V N → U N) (Aq Bq : ∀ N, ℝ → V N → Ω d → ℝ)
    (hB : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), ∀ (q : V N) (ω : Ω d), 0 ≤ Bq N u q ω)
    (hA : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), ∀ (q : V N) (ω : Ω d),
      Aq N u q ω = ‖rowSum d N u (row N (f N q)) (C N u (f N q)) ω‖ ^ 2)
    (hVar : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), ∀ (q : V N) (ω : Ω d),
      rowVarSum d N u (row N (f N q)) (C N u (f N q)) ω = u * Bq N u q ω) :
    UnifDomIcc (P d) s t Aq Bq := by
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [unifDomIcc_rowSum_general (s := s) (t := t) hs0 row C hCmeas hC
    (τ / 2) hτ2 D hD, Filter.eventually_ge_atTop 1] with N hN hN1 u hu q
  have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
  have hu1 : u ≤ 1 := le_trans hu.2 (ht1 N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- the almost sure statement at this `(N, u, q)`
  set i : d.Idx N := row N (f N q) with hi
  set Cq : Ω d → d.Idx N → ℂ := C N u (f N q) with hCq
  have hae : ∀ᵐ ω ∂(P d), rowVarSum d N u i Cq ω = 0 → rowSum d N u i Cq ω = 0 :=
    rowSum_ae_eq_zero_of_varSum_eq_zero hu0 Cq (hCmeas N u (f N q))
      (fun ω ω' h => hC N u (f N q) ω ω' h)
  set S : Set (Ω d) := {ω | rowVarSum d N u i Cq ω = 0 → rowSum d N u i Cq ω = 0} with hS
  have hSc : (P d) Sᶜ = 0 := by
    have : (P d) {ω | ¬ (rowVarSum d N u i Cq ω = 0 → rowSum d N u i Cq ω = 0)} = 0 := by
      simpa [MeasureTheory.ae_iff] using hae
    rw [hS, Set.compl_ofPred]
    exact this
  have hsub : {ω | (N : ℝ) ^ τ * Bq N u q ω < Aq N u q ω} ∩ S
      ⊆ {ω | (N : ℝ) ^ (τ / 2) * 1
          < ‖rowSum d N u i (rowCoeffNorm d N u i Cq) ω‖} := by
    rintro ω ⟨hbad, hω⟩
    simp only [Set.mem_ofPred_eq] at hbad hω ⊢
    have hV0 : 0 ≤ rowVarSum d N u i Cq ω := rowVarSum_nonneg hu0 Cq ω
    have hAeq : Aq N u q ω = ‖rowSum d N u i Cq ω‖ ^ 2 := hA N u hu q ω
    have hVeq : rowVarSum d N u i Cq ω = u * Bq N u q ω := hVar N u hu q ω
    rcases eq_or_lt_of_le hV0 with hV | hV
    · exfalso
      have hz : rowSum d N u i Cq ω = 0 := hω hV.symm
      rw [hAeq, hz] at hbad
      simp only [norm_zero] at hbad
      nlinarith [hB N u hu q ω, Real.rpow_nonneg hNpos.le τ]
    · have hs : (0 : ℝ) < Real.sqrt (rowVarSum d N u i Cq ω) := Real.sqrt_pos.2 hV
      rw [rowSum_rowCoeffNorm Cq hV, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs.le]
      rw [mul_one,
        show (Real.sqrt (rowVarSum d N u i Cq ω))⁻¹ * ‖rowSum d N u i Cq ω‖
          = ‖rowSum d N u i Cq ω‖ / Real.sqrt (rowVarSum d N u i Cq ω) by ring,
        lt_div_iff₀ hs]
      · have hVle : rowVarSum d N u i Cq ω ≤ Bq N u q ω := by
          rw [hVeq]; nlinarith [hB N u hu q ω]
        have hsq : Real.sqrt (rowVarSum d N u i Cq ω) ^ 2 = rowVarSum d N u i Cq ω :=
          Real.sq_sqrt hV0
        have hZ0 : (0 : ℝ) ≤ ‖rowSum d N u i Cq ω‖ := norm_nonneg _
        have hp2 : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
        have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
          rw [← Real.rpow_add hNpos]; congr 1; ring
        have hkey : ((N : ℝ) ^ (τ / 2) * Real.sqrt (rowVarSum d N u i Cq ω)) ^ 2
            < ‖rowSum d N u i Cq ω‖ ^ 2 := by
          rw [mul_pow, hsq]
          calc ((N : ℝ) ^ (τ / 2)) ^ 2 * rowVarSum d N u i Cq ω
              ≤ ((N : ℝ) ^ (τ / 2)) ^ 2 * Bq N u q ω := by nlinarith
            _ = (N : ℝ) ^ τ * Bq N u q ω := by rw [hsplit]; ring
            _ < ‖rowSum d N u i Cq ω‖ ^ 2 := by rw [← hAeq]; exact hbad
        nlinarith [hkey, hZ0, mul_pos hp2 hs]
  calc (P d) {ω | (N : ℝ) ^ τ * Bq N u q ω < Aq N u q ω}
      ≤ (P d) (({ω | (N : ℝ) ^ τ * Bq N u q ω < Aq N u q ω} ∩ S) ∪ Sᶜ) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωS : ω ∈ S
        · exact Or.inl ⟨hω, hωS⟩
        · exact Or.inr hωS
    _ ≤ (P d) ({ω | (N : ℝ) ^ τ * Bq N u q ω < Aq N u q ω} ∩ S) + (P d) Sᶜ :=
        measure_union_le _ _
    _ ≤ (P d) {ω | (N : ℝ) ^ (τ / 2) * 1
          < ‖rowSum d N u i (rowCoeffNorm d N u i Cq) ω‖} + 0 :=
        add_le_add (measure_mono hsub) hSc.le
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        rw [add_zero]; exact hN u hu (f N q)

end Fixed

/-! ### (4.2) with the time inside the index set -/

section Flow

variable {d : Dims} {s t : ℕ → ℝ} {E : ℝ}

end Flow

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Consequences

/-!
# Theorem 2.21 and Lemmas 2.18–2.20 at an `N`-dependent energy (T194, route (i))

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

`RBM.Bounds X E s` and `RBM.Thm221 X κ` of `Flow/Hypotheses.lean` carry a **fixed** real energy
`E`, so Theorems 2.3/2.4 were available only on a fixed energy slice (`RBM.SpecSeq.lemE_eq`).
The probabilistic half of Theorem 2.2 needs the local law at the *random* spectral parameter
`z = λ_k(ω) + iη`, hence at energies that move with `N`, so the slice has to go.

T153 verified with a compiled probe that above `RBM.Thm221` the energy is **purely parametric**:
every proof script of `Flow/Iteration.lean` and of the local-law half of `Flow/Consequences.lean`
goes through verbatim with `E N` in place of `E`.  This file carries that out.  The uniformity
is not an accident of the scripts; it is visible in two places:

* `RBM.flow_grid_2_72` and `RBM.flow_grid_2_72_gain` choose `W₀` **before** `E`, with constants
  depending on `κ` alone (`Flow/Scales.lean`);
* `RBM.Band.eventually_flow_grid`'s four `∀ᶠ N` inputs (`eventually_le_W`, `eventually_L_le_W`,
  `eventually_rpow_WL_le`, the hypothesis on `t`) mention no `E` at all.

**Nothing existing is changed**: every declaration here is new, and the fixed-energy statements
are recovered by specializing to a constant sequence (`RBM.Thm221N.toThm221`,
`RBM.BoundsN.toBounds`, …).

## Which variant is mirrored

Both.  T179 split Theorem 2.21 into `RBM.Thm221` (the paper-literal (2.72), `RBM.Cond272`) and
`RBM.Thm221'` (the (2.72) *with* the `N^c` gain, `RBM.Cond272'`, which is what the six steps of
§2.7 consume, see `docs/paper-deltas.md` #47/#54/#73).  Since the `N`-dependent energy is
orthogonal to the gain, both are mirrored — `RBM.Thm221N` and `RBM.Thm221N'` — and, exactly as
in `Flow/Iteration.lean`, the primed one is the load-bearing one: it is the weaker hypothesis
(`RBM.Thm221N.toThm221N'`), and the grid of p. 24 supplies the gain by itself
(`RBM.Band.eventually_flow_gridN'`).  `RBM.BoundsN_of_Thm221N` is the corollary of
`RBM.BoundsN_of_Thm221N'` along `RBM.Thm221N.toThm221N'`.

## Main results

* `RBM.BoundsCoreN`, `RBM.BoundsN`, `RBM.Cond272N`, `RBM.Cond272N'`, `RBM.Thm221N`,
  `RBM.Thm221N'` — the `E : ℕ → ℝ` versions, with `RBM.Thm221N.toThm221` etc. back to the
  fixed-energy ones.
* `RBM.BoundsN_zero`, `RBM.BoundsN.congr`, `RBM.Band.eventually_flow_gridN`,
  `RBM.Band.eventually_flow_gridN'` — the four iteration lemmas.
* `RBM.BoundsN_of_Thm221N`, `RBM.BoundsN_of_Thm221N'` — **Lemmas 2.18–2.20 at an `N`-dependent
  energy**.
* `RBM.SpecSeqN` — the spectral parameters **without the energy-slice condition**:
  `RBM.SpecSeqN.of_z` produces one for *every* sequence `z` with `|Re z| ≤ 2 - κ`,
  `N^{-1+τ} ≤ Im z ≤ 1`, by taking `E N := lemE (z N)`.
* `RBM.localLaw_of_boundsN`, `RBM.localSemicircleLaw_of_Thm221N`,
  `RBM.localSemicircleLaw_of_Thm221N'` — **Theorem 2.3** ((2.3), (2.4), the tracial law) at an
  `N`-dependent energy, and `RBM.localSemicircleLaw_of_Thm221N_of_z`,
  `RBM.localSemicircleLaw_of_Thm221N'_of_z` — the same for an **arbitrary** sequence of spectral
  parameters, with no energy parameter left in the statement.  This is what route (ii) needs.

Theorem 2.4 (`RBM.quantumDiffusion_of_Thm221`) is *not* mirrored here: the probabilistic half of
Theorem 2.2 only uses the local law (`RBM.sq_norm_eigenvector_le_of_norm_green_le` of
`Delocalization.lean` needs a bound on `G_xx`).  Its `N`-dependent version is the same verbatim
copy of `Flow/Consequences.lean`, on top of `RBM.BoundsN_of_Thm221N'`.

## Deviations from the paper

None new: `RBM.Thm221N` is the paper's Theorem 2.21 with the energy allowed to depend on `N`,
which the paper's proof does uniformly in `|E| ≤ 2 - κ` anyway.  It **retires** the "fixed energy
slice" deviation (`docs/paper-deltas.md` #38) for everything proved here.
-/

namespace RBM

open MeasureTheory Filter

/-! ### Lemmas 2.18–2.20 and Theorem 2.21 with `E : ℕ → ℝ` -/

section BoundsN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- (2.68), (2.69), (2.70) at the time `s` and the **`N`-dependent** energy `E`.  Verbatim
`RBM.BoundsCore` with `E N` in place of `E`. -/
structure BoundsCoreN (X : Sample B) (E : ℕ → ℝ) (s : ℕ → ℝ) : Prop where
  /-- **(2.68) = (2.60)**: `max_{σ,a} |L_{s,σ,a} - K_{s,σ,a}| ≺ (W ℓ_s η_s)^{-n}`, `n ≥ 1`. -/
  LmK : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (u : LoopData (B.L N) n) ω => X.lkErr (E N) N (s N) ω u.idx)
    (fun N _ _ => (B.scale (E N) N (s N))⁻¹ ^ n)
  /-- **(2.69) = (2.63)**: for `σ = (+,-)` and every `D > 0`,
  `|L_{s,σ,a} - K_{s,σ,a}| ≺ (W ℓ_s η_s)^{-2} (exp(-(|a₁-a₂|/ℓ_s)^{1/2}) + W^{-D})`. -/
  decay : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (a : ZMod (B.L N) × ZMod (B.L N)) ω => X.lkErr (E N) N (s N) ω (pmLoop a.1 a.2))
    (fun N a _ => (B.scale (E N) N (s N))⁻¹ ^ 2 * B.decayProf N (s N) D a.1 a.2)
  /-- **(2.70) = (2.64)**: `‖G_s - m‖_max ≺ (W ℓ_s η_s)^{-1/2}`. -/
  localLaw : StochDom B.P
    (fun N (ij : B.Idx N × B.Idx N) ω => X.llErr (E N) N (s N) ω ij)
    (fun N _ _ => (B.scale (E N) N (s N))⁻¹ ^ ((1 : ℝ) / 2))

/-- **Lemmas 2.18, 2.19, 2.20 at the time `s`** with an `N`-dependent energy.  Verbatim
`RBM.Bounds` with `E N` in place of `E`. -/
structure BoundsN (X : Sample B) (E : ℕ → ℝ) (s : ℕ → ℝ) : Prop extends BoundsCoreN X E s where
  /-- **(2.71) = (2.62)**: `max_{σ ∈ {+,-}², a} |E L_{s,σ,a} - K_{s,σ,a}| ≺ (W ℓ_s η_s)^{-3}`. -/
  expect : UnifDetDom
    (fun N (u : LoopData (B.L N) 2) => X.expErr (E N) N (s N) u.idx)
    (fun N _ => (B.scale (E N) N (s N))⁻¹ ^ 3)

/-- **(2.72)** at an `N`-dependent energy. -/
def Cond272N (B : Band Ω) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, (B.scale (E N) N (t N))⁻¹ ≤ ((1 - t N) / (1 - s N)) ^ 30

/-- **(2.72) with the `N^c` gain** (T179) at an `N`-dependent energy. -/
def Cond272N' (B : Band Ω) (E : ℕ → ℝ) (s t : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ c * (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N)

/-- **Theorem 2.21 at an `N`-dependent energy** (as a hypothesis).  Verbatim `RBM.Thm221`, with
`E : ℕ → ℝ` and `|E N| ≤ 2 - κ` for every `N`.  It is strictly stronger than `RBM.Thm221`
(`RBM.Thm221N.toThm221`); the paper's proof of Theorem 2.21 is uniform in `|E| ≤ 2 - κ`, so the
burden is entirely on the future producer (the six steps of §2.7). -/
structure Thm221N (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
    (∀ N, t N < 1) → Cond272N B E s t → BoundsN X E s → BoundsN X E t

/-- **Theorem 2.21 with the gained (2.72), at an `N`-dependent energy.**  Verbatim
`RBM.Thm221'`; this is the variant the six steps of §2.7 can actually produce, and the one
`RBM.BoundsN_of_Thm221N'` uses. -/
structure Thm221N' (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
    (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272N' B E s t c → BoundsN X E s → BoundsN X E t

/-! #### Specialization to a constant energy: nothing existing is weakened -/

variable {X : Sample B} {E : ℝ} {s : ℕ → ℝ}

theorem BoundsCore.toBoundsCoreN (h : BoundsCore X E s) : BoundsCoreN X (fun _ => E) s :=
  ⟨h.LmK, h.decay, h.localLaw⟩

theorem BoundsCoreN.toBoundsCore (h : BoundsCoreN X (fun _ => E) s) : BoundsCore X E s :=
  ⟨h.LmK, h.decay, h.localLaw⟩

theorem Bounds.toBoundsN (h : Bounds X E s) : BoundsN X (fun _ => E) s :=
  ⟨h.toBoundsCore.toBoundsCoreN, h.expect⟩

theorem BoundsN.toBounds (h : BoundsN X (fun _ => E) s) : Bounds X E s :=
  ⟨h.toBoundsCoreN.toBoundsCore, h.expect⟩

theorem Cond272.toCond272N {t : ℕ → ℝ} (h : Cond272 B E s t) : Cond272N B (fun _ => E) s t := h

theorem Cond272N.toCond272 {t : ℕ → ℝ} (h : Cond272N B (fun _ => E) s t) : Cond272 B E s t := h

theorem Cond272'.toCond272N' {t : ℕ → ℝ} {c : ℝ} (h : Cond272' B E s t c) :
    Cond272N' B (fun _ => E) s t c := h

theorem Cond272N'.toCond272' {t : ℕ → ℝ} {c : ℝ} (h : Cond272N' B (fun _ => E) s t c) :
    Cond272' B E s t c := h

/-- The `N`-dependent Theorem 2.21 is **stronger**: specializing to a constant energy sequence
recovers `RBM.Thm221`. -/
theorem Thm221N.toThm221 {κ : ℝ} (h : Thm221N X κ) : Thm221 X κ where
  step E hE s t hs0 hst ht1 hcond hB :=
    (h.step (fun _ => E) (fun _ => hE) s t hs0 hst ht1 hcond.toCond272N hB.toBoundsN).toBounds

/-- Same for the gained form. -/
theorem Thm221N'.toThm221' {κ : ℝ} (h : Thm221N' X κ) : Thm221' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    (h.step (fun _ => E) (fun _ => hE) c hc0 s t hs0 hst ht1 hcond.toCond272N'
      hB.toBoundsN).toBounds

end BoundsN

/-! ### The four iteration lemmas of `Flow/Iteration.lean`, at an `N`-dependent energy -/

section Iteration

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℕ → ℝ}

/-- **(2.67)** at an `N`-dependent energy: Lemmas 2.18, 2.19, 2.20 hold at `t = 0` with no error
(`L_0 = K_0`, `G_0 = m`, `E L_0 = K_0`).  Verbatim `RBM.Bounds_zero`. -/
theorem BoundsN_zero (hE : ∀ N, |E N| ≤ 2) : BoundsN X E (fun _ => 0) := by
  have hY : ∀ N, 0 ≤ (B.scale (E N) N 0)⁻¹ := fun N =>
    inv_nonneg.2 (B.scale_nonneg (E N) N zero_le_one)
  refine ⟨⟨fun n hn => ?_, fun D hD => ?_, ?_⟩, ?_⟩
  · exact StochDom.of_eq_zero
      (fun N u ω => X.lkErr_zero (hE N) N ω u.idx u.idx_wf (by simpa using hn))
      (fun N _ _ => pow_nonneg (hY N) n)
  · refine StochDom.of_eq_zero
      (fun N a ω => X.lkErr_zero (hE N) N ω _ (pmLoop_wf a.1 a.2) (by simp [pmLoop_length]))
      (fun N a _ => mul_nonneg (pow_nonneg (hY N) 2) ?_)
    unfold Band.decayProf
    positivity
  · exact StochDom.of_eq_zero (fun N ij ω => X.llErr_zero (hE N) N ω ij)
      (fun N _ _ => Real.rpow_nonneg (hY N) _)
  · intro τ hτ
    refine Eventually.of_forall fun N u => ?_
    simp only
    rw [X.expErr_zero (hE N) N u.idx u.idx_wf (by simp)]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (pow_nonneg (hY N) 3)

/-- The bounds at a time sequence only depend on it for large `N`.  Verbatim
`RBM.Bounds.congr`. -/
theorem BoundsN.congr {s t : ℕ → ℝ} (h : BoundsN X E s) (hst : ∀ᶠ N : ℕ in atTop, s N = t N) :
    BoundsN X E t where
  LmK n hn := (h.LmK n hn).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  decay D hD := (h.decay D hD).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  localLaw := h.localLaw.congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  expect := h.expect.congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- **The grid of p. 24 for the band model, uniformly in an `N`-dependent energy.**  Verbatim
`RBM.Band.eventually_flow_grid` with `E N` in place of `E`.

The point of the statement is the **quantifier order**: `τ'` and `n₀` are produced *before* `E`,
because `RBM.flow_grid_2_72` picks `W₀` before `E` with constants depending on `κ` alone. -/
theorem eventually_flow_gridN {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ n₀ : ℕ, ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ t : ℕ → ℝ,
      (∀ N, 0 ≤ t N) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      ∀ᶠ N : ℕ in atTop, gridT (B.W N) τ' (t N) n₀ = t N ∧ 1 ≤ B.scale (E N) N (t N) ∧
        t N < 1 ∧ ∀ k : ℕ, (B.scale (E N) N (gridT (B.W N) τ' (t N) (k + 1)))⁻¹ ≤
          ((1 - gridT (B.W N) τ' (t N) (k + 1)) / (1 - gridT (B.W N) τ' (t N) k)) ^ 30 := by
  set τ₀ := min τ 1 / 2 with hτ₀
  have hτ₀0 : 0 < τ₀ := by have := lt_min hτ one_pos; rw [hτ₀]; linarith
  have hτ₀1 : τ₀ ≤ 1 := by have := min_le_right τ 1; rw [hτ₀]; linarith
  have hτ₀τ : τ₀ ≤ τ / 2 := by have := min_le_left τ 1; rw [hτ₀]; linarith
  set τ' := τ₀ / 120 with hτ'
  have hτ'0 : 0 < τ' := by rw [hτ']; positivity
  set n₀ := ⌈2 / τ'⌉₊ with hn₀
  have hn : 2 ≤ (n₀ : ℝ) * τ' := (div_le_iff₀ hτ'0).1 (Nat.le_ceil _)
  obtain ⟨W₀, -, hW⟩ := flow_grid_2_72 hκ hτ₀0.le hτ'0 (by rw [hτ']; linarith) hn
  refine ⟨τ', hτ'0, n₀, fun E hE t ht0 ht => ?_⟩
  filter_upwards [B.eventually_le_W W₀, B.eventually_L_le_W,
    B.eventually_rpow_WL_le hτ hτ₀0.le hτ₀1 hτ₀τ, ht, eventually_ge_atTop 1]
    with N hWN hLW hWL htN hN1
  have hEN := hE N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have ht1 : t N < 1 := by have := Real.rpow_pos_of_pos hN0 (-1 + τ); linarith
  obtain ⟨-, hgrid, -, hA, hstep⟩ :=
    hW (B.W N) hWN (B.L N) (B.one_le_L N) hLW (E N) hEN (t N) (ht0 N) (hWL.trans htN)
  have hE2 : |E N| < 2 := by linarith
  have hpos : 0 < B.scale (E N) N (t N) :=
    flowScale_pos (by linarith [B.one_le_W N]) (B.one_le_L N) hE2 ht1
  have hA1 : (B.scale (E N) N (t N))⁻¹ ≤ 1 :=
    hA.trans (Real.rpow_le_one_of_one_le_of_nonpos (B.one_le_W N) (by linarith))
  exact ⟨hgrid, (inv_le_one₀ hpos).1 hA1, ht1, hstep⟩

/-- **The grid of p. 24 with the `N^c` gain, uniformly in an `N`-dependent energy.**  Verbatim
`RBM.Band.eventually_flow_grid'` with `E N` in place of `E`; `τ'`, `c` and `n₀` are again
produced before `E`. -/
theorem eventually_flow_gridN' {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) →
      ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      ∀ᶠ N : ℕ in atTop, gridT (B.W N) τ' (t N) n₀ = t N ∧ 1 ≤ B.scale (E N) N (t N) ∧
        t N < 1 ∧ ∀ k : ℕ, (N : ℝ) ^ c * ((1 - gridT (B.W N) τ' (t N) k) /
            (1 - gridT (B.W N) τ' (t N) (k + 1))) ^ 30 ≤
          B.scale (E N) N (gridT (B.W N) τ' (t N) (k + 1)) := by
  set τ₀ := min τ 1 / 2 with hτ₀
  have hτ₀0 : 0 < τ₀ := by have := lt_min hτ one_pos; rw [hτ₀]; linarith
  have hτ₀1 : τ₀ ≤ 1 := by have := min_le_right τ 1; rw [hτ₀]; linarith
  have hτ₀τ : τ₀ ≤ τ / 2 := by have := min_le_left τ 1; rw [hτ₀]; linarith
  set τ' := τ₀ / 120 with hτ'
  have hτ'0 : 0 < τ' := by rw [hτ']; positivity
  set n₀ := ⌈2 / τ'⌉₊ with hn₀
  have hn : 2 ≤ (n₀ : ℝ) * τ' := (div_le_iff₀ hτ'0).1 (Nat.le_ceil _)
  obtain ⟨W₀, -, hW⟩ := flow_grid_2_72_gain hκ hτ₀0.le hτ'0 (by rw [hτ']; linarith) hn
  have hexp : τ₀ / 4 - 15 * τ' = τ₀ / 8 := by rw [hτ']; ring
  refine ⟨τ', hτ'0, τ₀ / 16, by positivity, n₀, fun E hE t ht0 ht => ?_⟩
  filter_upwards [B.eventually_le_W W₀, B.eventually_L_le_W,
    B.eventually_rpow_WL_le hτ hτ₀0.le hτ₀1 hτ₀τ, ht, eventually_ge_atTop 1, B.bandwidth]
    with N hWN hLW hWL htN hN1 hbw
  have hEN := hE N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ht1 : t N < 1 := by have := Real.rpow_pos_of_pos hN0 (-1 + τ); linarith
  obtain ⟨-, hgrid, -, hA, hstep⟩ :=
    hW (B.W N) hWN (B.L N) (B.one_le_L N) hLW (E N) hEN (t N) (ht0 N) (hWL.trans htN)
  have hE2 : |E N| < 2 := by linarith
  have hpos : 0 < B.scale (E N) N (t N) :=
    flowScale_pos (by linarith [B.one_le_W N]) (B.one_le_L N) hE2 ht1
  have hA1 : (B.scale (E N) N (t N))⁻¹ ≤ 1 :=
    hA.trans (Real.rpow_le_one_of_one_le_of_nonpos (B.one_le_W N) (by linarith))
  have hNW : (N : ℝ) ^ (τ₀ / 16) ≤ (B.W N : ℝ) ^ (τ₀ / 8) := by
    have hhalf : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (B.W N : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [B.c_pos])).trans hbw
    calc (N : ℝ) ^ (τ₀ / 16) = ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (τ₀ / 8) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
      _ ≤ (B.W N : ℝ) ^ (τ₀ / 8) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hhalf (by positivity)
  refine ⟨hgrid, (inv_le_one₀ hpos).1 hA1, ht1, fun k => ?_⟩
  have hk := hstep k
  rw [hexp] at hk
  have hr0 : 0 ≤ (1 - gridT (B.W N) τ' (t N) k) / (1 - gridT (B.W N) τ' (t N) (k + 1)) := by
    have h1 := gridT_le (W := (B.W N : ℝ)) (τ' := τ') (t N) k
    have h2 := gridT_le (W := (B.W N : ℝ)) (τ' := τ') (t N) (k + 1)
    exact div_nonneg (by linarith) (by linarith)
  calc (N : ℝ) ^ (τ₀ / 16) * ((1 - gridT (B.W N) τ' (t N) k) /
          (1 - gridT (B.W N) τ' (t N) (k + 1))) ^ 30
      ≤ (B.W N : ℝ) ^ (τ₀ / 8) * ((1 - gridT (B.W N) τ' (t N) k) /
          (1 - gridT (B.W N) τ' (t N) (k + 1))) ^ 30 :=
        mul_le_mul_of_nonneg_right hNW (pow_nonneg hr0 30)
    _ ≤ _ := hk

end Band

/-- **The gained (2.72) implies the bare (2.72)** at an `N`-dependent energy.  Verbatim
`RBM.Cond272'.toCond272`. -/
theorem Cond272N'.toCond272N {s t : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 ≤ c) (h : Cond272N' B E s t c) :
    Cond272N B E s t := by
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  rw [etaT_div_etaT (hE N)] at hN
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith
  have hR0 : 0 < (1 - s N) / (1 - t N) := div_pos h1s h1t
  have hc : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0
  have hpos : 0 < ((1 - s N) / (1 - t N)) ^ 30 := pow_pos hR0 30
  have h1 : ((1 - s N) / (1 - t N)) ^ 30 ≤ B.scale (E N) N (t N) := by nlinarith
  calc (B.scale (E N) N (t N))⁻¹ ≤ (((1 - s N) / (1 - t N)) ^ 30)⁻¹ := inv_anti₀ hpos h1
    _ = ((1 - t N) / (1 - s N)) ^ 30 := by rw [← inv_pow, inv_div]

/-- **`RBM.Thm221N` implies its gained form.**  Verbatim `RBM.Thm221.toThm221'`. -/
theorem Thm221N.toThm221N' {X : Sample B} {κ : ℝ} (hκ : 0 < κ) (hT : Thm221N X κ) :
    Thm221N' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    hT.step E hE s t hs0 hst ht1
      (hcond.toCond272N (fun N => by linarith [abs_nonneg (E N), hE N]) hst ht1 hc0.le) hB

/-- **Lemmas 2.18, 2.19 and 2.20 (p. 24) at an `N`-dependent energy, from the gained
Theorem 2.21.**  Verbatim `RBM.Bounds_of_Thm221'` with `E N` in place of `E`.

The grid of p. 24 supplies the gained (2.72) by itself (`RBM.Band.eventually_flow_gridN'`), and
its `τ'`, `c`, `n₀` are chosen before `E`, so the number of grid steps is uniform in the energy
sequence. -/
theorem BoundsN_of_Thm221N' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221N' X κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsN X E t := by
  obtain ⟨τ', hτ', c, hc0, n₀, hgrid⟩ := B.eventually_flow_gridN' hκ hτ
  have hg := hgrid E hE t ht0 ht
  have hE2 : ∀ N, |E N| ≤ 2 := fun N => by linarith [hE N]
  have hE2' : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  let u : ℕ → ℕ → ℝ := fun k N => gridT (B.W N) τ' (t N) k
  have key : ∀ k, BoundsN X E (u k) := by
    intro k
    induction k with
    | zero =>
      have h0 : u 0 = fun _ => 0 := funext fun N => gridT_zero (ht0 N)
      rw [h0]
      exact BoundsN_zero X hE2
    | succ k ih =>
      refine hT.step E hE c hc0 (u k) (u (k + 1)) (fun N => ?_) (fun N => ?_) (fun N => ?_) ?_ ih
      · exact le_min (gridS_nonneg (B.one_le_W N) hτ'.le k) (ht0 N)
      · exact gridT_mono (B.one_le_W N) hτ'.le (t N) (Nat.le_succ k)
      · exact (min_le_left _ _).trans_lt (gridS_lt_one (by linarith [B.one_le_W N]) _)
      · filter_upwards [hg] with N hN
        rw [etaT_div_etaT (hE2' N)]
        exact hN.2.2.2 k
  exact (key n₀).congr X (by filter_upwards [hg] with N hN; exact hN.1)

/-- **Lemmas 2.18, 2.19 and 2.20 at an `N`-dependent energy, from `RBM.Thm221N`.**  The
corollary of `RBM.BoundsN_of_Thm221N'` along `RBM.Thm221N.toThm221N'`. -/
theorem BoundsN_of_Thm221N {κ : ℝ} (hκ : 0 < κ) (hT : Thm221N X κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsN X E t :=
  BoundsN_of_Thm221N' X hκ (hT.toThm221N' hκ) hE hτ ht0 ht

end Iteration

/-! ### The spectral parameters, **without the energy-slice condition** -/

/-- **The spectral parameters of Theorems 2.3/2.4 with an `N`-dependent Lemma 2.8 energy.**
Verbatim `RBM.SpecSeq`, except that the last field now reads `lemE (z N) = E N`.

⭐ That field is no longer a *condition*: `RBM.SpecSeqN.of_z` builds one for **every** sequence
`z` with `|Re z| ≤ 2 - κ` and `N^{-1+τ} ≤ Im z ≤ 1`, by taking `E N := lemE (z N)`, and then
`lemE_eq` is `rfl`.  `RBM.SpecSeq`'s slice condition `lemE (z N) = E` (a fixed real) is what
restricted Theorems 2.3/2.4 to one energy slice (`docs/paper-deltas.md` #38). -/
structure SpecSeqN (κ τ : ℝ) (E : ℕ → ℝ) (z : ℕ → ℂ) : Prop where
  im_pos : ∀ N, 0 < (z N).im
  im_le_one : ∀ N, (z N).im ≤ 1
  abs_re_le : ∀ N, |(z N).re| ≤ 2 - κ
  /-- `η ≥ N^{-1+τ}` (for large `N`). -/
  im_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im
  /-- The energy of Lemma 2.8 at `z N` is `E N`. -/
  lemE_eq : ∀ N, lemE (z N) = E N

/-- ⭐ **The energy-slice condition disappears**: every sequence of spectral parameters in the
domain of Theorems 2.3/2.4 is a `RBM.SpecSeqN`, with `E N := lemE (z N)`. -/
theorem SpecSeqN.of_z {κ τ : ℝ} {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im)
    (him_le_one : ∀ N, (z N).im ≤ 1) (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) :
    SpecSeqN κ τ (fun N => lemE (z N)) z :=
  ⟨him_pos, him_le_one, habs_re, him_ge, fun _ => rfl⟩

/-- A fixed-energy `RBM.SpecSeq` is a constant-energy `RBM.SpecSeqN`. -/
theorem SpecSeq.toSpecSeqN {κ τ E : ℝ} {z : ℕ → ℂ} (hz : SpecSeq κ τ E z) :
    SpecSeqN κ τ (fun _ => E) z :=
  ⟨hz.im_pos, hz.im_le_one, hz.abs_re_le, hz.im_ge, hz.lemE_eq⟩

namespace SpecSeqN

variable {κ τ : ℝ} {E : ℕ → ℝ} {z : ℕ → ℂ} (hz : SpecSeqN κ τ E z)
include hz

/-- `|E N| ≤ 2 - κ` (Lemma 2.8: `|E| ≤ |Re z|`).  Verbatim `RBM.SpecSeq.abs_E_le`. -/
theorem abs_E_le (hκ : 0 < κ) (N : ℕ) : |E N| ≤ 2 - κ := by
  rw [← hz.lemE_eq N]
  exact (lemma28_quant hκ (hz.im_pos N) (hz.im_le_one N) (hz.abs_re_le N)).1

theorem lemT_nonneg (N : ℕ) : 0 ≤ lemT (z N) := (lemT_pos (hz.im_pos N)).le

theorem lemT_lt_one' (N : ℕ) : lemT (z N) < 1 := lemT_lt_one (hz.im_pos N)

/-- `1 - lemT z ≥ N^{-1+τ/2}` for large `N`.  Verbatim
`RBM.SpecSeq.eventually_rpow_le_one_sub`. -/
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

/-- **Lemmas 2.18–2.20 at the time `t = lemT z`**, from `RBM.Thm221N'`. -/
theorem boundsN' (X : Sample B) (hκ : 0 < κ) (hT : Thm221N' X κ) (hτ : 0 < τ) :
    BoundsN X E (fun N => lemT (z N)) :=
  BoundsN_of_Thm221N' X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

/-- **Lemmas 2.18–2.20 at the time `t = lemT z`**, from `RBM.Thm221N`. -/
theorem boundsN (X : Sample B) (hκ : 0 < κ) (hT : Thm221N X κ) (hτ : 0 < τ) :
    BoundsN X E (fun N => lemT (z N)) :=
  BoundsN_of_Thm221N X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

theorem scale_inv_le (hκ : 0 < κ) (N : ℕ) :
    (B.scale (E N) N (lemT (z N)))⁻¹ ≤ cScale κ * (B.zScale N (z N))⁻¹ := by
  rw [← hz.lemE_eq N]
  exact B.scale_inv_le hκ (hz.im_pos N) (hz.im_le_one N) (hz.abs_re_le N) N

theorem scale_inv_nonneg (N : ℕ) : 0 ≤ (B.scale (E N) N (lemT (z N)))⁻¹ :=
  inv_nonneg.2 (B.scale_nonneg (E N) N (hz.lemT_lt_one' N).le)

theorem zScale_inv_nonneg (N : ℕ) : 0 ≤ (B.zScale N (z N))⁻¹ :=
  inv_nonneg.2 (B.zScale_pos N (hz.im_pos N)).le

/-- `(W ℓ_t η_t)^{-n} ≺ (W ℓ(z) η)^{-n}` (deterministic). -/
theorem unifDetDom_pow (hκ : 0 < κ) {U : ℕ → Type*} (n : ℕ) :
    UnifDetDom (fun N (_ : U N) => (B.scale (E N) N (lemT (z N)))⁻¹ ^ n)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ n) :=
  UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hz.zScale_inv_nonneg N) n)
    (cScale κ ^ n) (Eventually.of_forall fun N _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hz.scale_inv_nonneg N) (hz.scale_inv_le hκ N) n)

/-- `(W ℓ_t η_t)^{-p} ≺ (W ℓ(z) η)^{-p}` for real `p ≥ 0` (deterministic). -/
theorem unifDetDom_rpow (hκ : 0 < κ) {U : ℕ → Type*} {p : ℝ} (hp : 0 ≤ p) :
    UnifDetDom (fun N (_ : U N) => (B.scale (E N) N (lemT (z N)))⁻¹ ^ p)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ p) :=
  UnifDetDom.of_eventually_le_const_mul
    (fun N _ => Real.rpow_nonneg (hz.zScale_inv_nonneg N) p)
    (cScale κ ^ p) (Eventually.of_forall fun N _ => by
      rw [← Real.mul_rpow (cScale_pos hκ).le (hz.zScale_inv_nonneg N)]
      exact Real.rpow_le_rpow (hz.scale_inv_nonneg N) (hz.scale_inv_le hκ N) hp)

end SpecSeqN

/-! ### Theorem 2.3 at an `N`-dependent energy -/

section Main

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ : ℝ} {E : ℕ → ℝ}
  {z : ℕ → ℂ}

/-- **Theorem 2.3, (2.3)** (local semicircle law) at an `N`-dependent energy, from (2.64) and
(2.65): `max_{x,y} |(G(z) - m(z))_{xy}| ≺ (W ℓ(z) η)^{-1/2}`.  Verbatim
`RBM.localLaw_of_bounds`. -/
theorem localLaw_of_boundsN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) := by
  have h1 := hB.localLaw.trans
    (StochDom.of_unifDetDom (hz.unifDetDom_rpow hκ (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  refine T.green_sub_msc z hz.im_pos _ (StochDom.of_le_left (fun N ij ω => ?_) h1)
  rw [hz.lemE_eq N, Matrix.smul_apply, norm_smul, Sample.llErr]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (hz.lemT_lt_one' N).le

/-- **Theorem 2.3, (2.4)** in loop form at an `N`-dependent energy.  Verbatim
`RBM.loop1_of_bounds`. -/
theorem loop1_of_boundsN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  have h1 := ((hB.LmK 1 le_rfl).trans
    (StochDom.of_unifDetDom (hz.unifDetDom_pow hκ 1))).precomp_param
    (fun N (a : ZMod (B.L N)) => ((fun _ => true, fun _ => a) : LoopData (B.L N) 1))
  have h2 := T1.loop1 z hz.im_pos (fun N _ => msc (z N)) (fun N _ => (B.zScale N (z N))⁻¹ ^ 1)
    (StochDom.of_le_left (fun N a ω => ?_) h1)
  · simpa only [pow_one] using h2
  have hidx : LoopData.idx ((fun _ => true, fun _ => a) : LoopData (B.L N) 1) =
      ⟨[true], [a]⟩ := by simp [LoopData.idx]
  rw [hidx, Sample.lkErr, Band.Kval, Kgen_one, msc_eq_sqrt_mul_mE (hz.im_pos N), hz.lemE_eq N,
    ← mul_sub, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (hz.lemT_lt_one' N).le

/-- **Theorem 2.3, (2.4)** (partial tracial local law) at an `N`-dependent energy.  Verbatim
`RBM.partialTrace_of_bounds`. -/
theorem partialTrace_of_boundsN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  refine StochDom.of_le_left (fun N a ω => le_of_eq ?_) (loop1_of_boundsN T T1 hκ hz hB)
  rw [gloop_one_eq]

/-- **Theorem 2.3, the tracial local law** at an `N`-dependent energy.  Verbatim
`RBM.trace_of_bounds`. -/
theorem trace_of_boundsN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  have h := StochDom.average (V := fun N => ZMod (B.L N)) (c := fun N => msc (z N))
    (ζ := fun N => (B.zScale N (z N))⁻¹) (partialTrace_of_boundsN T T1 hκ hz hB)
  refine StochDom.of_le_left (fun N _ ω => le_of_eq ?_) h
  have hW : (B.W N : ℂ) ≠ 0 := by exact_mod_cast (B.W_pos N).ne'
  have hL : (B.L N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (B.L N))
  simp only [ZMod.card, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, ← Finset.mul_sum]
  push_cast
  field_simp

/-- **Theorem 2.3 (local semicircle law) at an `N`-dependent energy**, from `RBM.Thm221N'`.
Verbatim `RBM.localSemicircleLaw_of_Thm221'`, with `RBM.SpecSeqN` in place of `RBM.SpecSeq`. -/
theorem localSemicircleLaw_of_Thm221N' (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221N' X κ) (hτ : 0 < τ) (hz : SpecSeqN κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
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
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) := by
  have hB := hz.boundsN' X hκ hT hτ
  refine ⟨B.prob_le_of_stochDom (fun N _ _ => Real.rpow_nonneg (hz.zScale_inv_nonneg N) _)
      (localLaw_of_boundsN T hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (partialTrace_of_boundsN T T1 hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (trace_of_boundsN T T1 hκ hz hB) hτ' hD⟩

/-- **Theorem 2.3 at an `N`-dependent energy**, from `RBM.Thm221N`. -/
theorem localSemicircleLaw_of_Thm221N (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221N X κ) (hτ : 0 < τ) (hz : SpecSeqN κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
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
  localSemicircleLaw_of_Thm221N' T T1 hκ (hT.toThm221N' hκ) hτ hz hτ' hD

/-- ⭐ **Theorem 2.3 for an arbitrary sequence of spectral parameters** — no energy parameter
occurs in the statement at all.

This is what route (ii) of the probabilistic half of Theorem 2.2 needs: the local law at
`z_N = λ_k(ω_N) + iη_N`, whose Lemma 2.8 energy moves with `N`.  The only hypotheses on `z` are
the paper's domain conditions `|Re z| ≤ 2 - κ`, `N^{-1+τ} ≤ Im z ≤ 1`; the energy slice
`RBM.SpecSeq.lemE_eq` is gone (`RBM.SpecSeqN.of_z`). -/
theorem localSemicircleLaw_of_Thm221N_of_z (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221N X κ) (hτ : 0 < τ) {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im)
    (him_le_one : ∀ N, (z N).im ≤ 1) (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
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
  localSemicircleLaw_of_Thm221N T T1 hκ hT hτ
    (SpecSeqN.of_z him_pos him_le_one habs_re him_ge) hτ' hD

/-- The same for `RBM.Thm221N'`. -/
theorem localSemicircleLaw_of_Thm221N'_of_z (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221N' X κ) (hτ : 0 < τ) {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im)
    (him_le_one : ∀ N, (z N).im ≤ 1) (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
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
  localSemicircleLaw_of_Thm221N' T T1 hκ hT hτ
    (SpecSeqN.of_z him_pos him_le_one habs_re him_ge) hτ' hD

end Main

/-! ### Satisfiability probes

Seven vacuous-hypothesis incidents on this project; the hypotheses introduced here are checked
rather than assumed to be inhabited. -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The hypotheses of `RBM.Thm221N.step` are jointly satisfiable, for every energy sequence**:
at `s = t ≡ 0`, (2.72) holds (because the grid of p. 24 gives `W ℓ_0 η_0 ≥ 1` uniformly in `E`)
and `RBM.BoundsN` holds unconditionally by (2.67).  So `step` is not a vacuous implication, and
the `∀ E : ℕ → ℝ` in front of it is not a vacuous quantifier. -/
example (X : Sample B) {κ : ℝ} (hκ : 0 < κ) (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ) :
    Cond272N B E (fun _ => 0) (fun _ => 0) ∧ BoundsN X E (fun _ => 0) := by
  obtain ⟨τ', hτ', n₀, hgrid⟩ := B.eventually_flow_gridN hκ (by norm_num : (0 : ℝ) < 1 / 2)
  have ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + (1 / 2 : ℝ)) ≤ 1 - (fun _ : ℕ => (0 : ℝ)) N := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hg := hgrid E hE (fun _ => 0) (fun _ => le_rfl) ht
  refine ⟨?_, BoundsN_zero X fun N => by linarith [hE N]⟩
  filter_upwards [hg] with N hN
  have h1 : (1 : ℝ) ≤ B.scale (E N) N 0 := hN.2.1
  have hpos : (0 : ℝ) < B.scale (E N) N 0 := by linarith
  have : (B.scale (E N) N 0)⁻¹ ≤ 1 := (inv_le_one₀ hpos).2 h1
  simpa using this

/-- **`RBM.SpecSeqN` is inhabited with a genuinely `N`-dependent energy.**  Any sequence `z` in
the domain works, e.g. a moving real part; the energy `E N = lemE (z N)` then moves with `N`.
(`RBM.SpecSeq` would force `lemE (z N)` to be one fixed real.) -/
example {κ τ : ℝ} {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) :
    ∃ E : ℕ → ℝ, SpecSeqN κ τ E z :=
  ⟨_, SpecSeqN.of_z him_pos him_le_one habs_re him_ge⟩

end Satisfiable

end RBM

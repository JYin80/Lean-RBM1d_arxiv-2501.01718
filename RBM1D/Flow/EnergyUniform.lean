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

* `RBM.Thm221NoELN`, `RBM.Thm221NoELN'`, `RBM.BoundsCoreN_zero`, `RBM.BoundsCoreN.congr`,
  `RBM.BoundsCoreN_of_Thm221NoELN'`, `RBM.BoundsCoreN_of_Thm221NoELN`,
  `RBM.SpecSeqN.boundsCoreN'`, `RBM.SpecSeqN.boundsCoreN` — **T235**: the `N`-dependent
  version of `Flow/Thm221NoEL.lean`'s p. 25 variant, i.e. Theorem 2.21 with (2.71) removed
  from both sides.  Theorem 2.2 runs on it.
* `RBM.boundsGrid_of_fields` — **T235**: the induction of p. 24 as a *single* script, taking
  the bundle as a parameter `P : (ℕ → ℝ) → Prop` and the three facts it needs of `P`
  (`hzero`, `hcongr`, `hstep`) as fields.  `RBM.BoundsN_of_Thm221N'`,
  `RBM.BoundsCoreN_of_Thm221NoELN'` and `RBM.BoundsCore_of_Thm221NoEL'` are its three
  one-line specializations; there is no second copy of the induction anywhere.
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
* `RBM.localLaw_of_boundsCoreN`, `RBM.loop1_of_boundsCoreN`, `RBM.partialTrace_of_boundsCoreN`,
  `RBM.trace_of_boundsCoreN`, `RBM.localSemicircleLaw_of_boundsCoreN`,
  `RBM.localSemicircleLaw_of_boundsCoreN_of_z` — **Theorem 2.3** ((2.3), (2.4), the tracial law)
  at an `N`-dependent energy, on `RBM.BoundsCoreN`: **(2.71) is not used** (T221; the paper's
  remark on p. 25).  `RBM.localLaw_of_boundsN` etc. are the `RBM.BoundsN` corollaries, and
  `RBM.localSemicircleLaw_of_Thm221N`, `RBM.localSemicircleLaw_of_Thm221N'` the assembled forms,
  with `RBM.localSemicircleLaw_of_Thm221N_of_z`, `RBM.localSemicircleLaw_of_Thm221N'_of_z` for an
  **arbitrary** sequence of spectral parameters, with no energy parameter left in the statement.
  This is what route (ii) needs.

  **T221**: the proof scripts are *not* repeated here.  They are
  `RBM.localLaw_of_fields`, `RBM.loop1_of_fields`, `RBM.partialTrace_of_fields`,
  `RBM.trace_of_fields` of `Flow/Consequences.lean`, which take the fields they use and an
  energy *sequence*, so that the fixed-energy statements there and the `N`-dependent ones here
  are both one-line corollaries of one script (`rfl`-probes at the end of §`Main`).

* `RBM.StochDom.of_forall_seq` — `≺` with the union over a polynomially small `N`-dependent
  index set *inside* the probability, from a `≺`-bound along every sequence of indices (T199).
* `RBM.netDen`, `RBM.bulkNet`, `RBM.exists_bulkNet_close`, `RBM.card_bulkNet_le`,
  `RBM.netDen_inv_div_rpow_le` — the energy net of `[-2+κ, 2-κ]` and the three facts about it.
* `RBM.Band.rpow_le_zScale` — `W ℓ(z) η ≥ N^θ/2` at `η = N^{-1+θ}`, `θ ≤ c` (this is where
  (2.2) enters).
* `RBM.delocalization_of_Thm221N'`, `RBM.delocalization_of_Thm221N` — **Theorem 2.2**.
  **T235**: their hypothesis is `RBM.Thm221NoELN'` / `RBM.Thm221NoELN`, so (2.71) = (2.62) —
  and with it every Step 6 datum — does not occur in Theorem 2.2's hypothesis table.

Theorem 2.4 (`RBM.quantumDiffusion_of_Thm221`) is *not* mirrored here: the probabilistic half of
Theorem 2.2 only uses the local law (`RBM.sq_norm_eigenvector_le_of_norm_green_le_near` of
`Delocalization.lean` needs a bound on `G_xx`).

## Deviations from the paper

`RBM.Thm221N` is the paper's Theorem 2.21 with the energy allowed to depend on `N`, which the
paper's proof does uniformly in `|E| ≤ 2 - κ` anyway.  It **retires** the "fixed energy slice"
deviation (`docs/paper-deltas.md` #38) for everything proved here.

For Theorem 2.2 see `docs/paper-deltas.md` (T199): the paper's `η = N^{-1+τ}` uses the same `τ`
for the scale and for the conclusion and then writes `|ψ_k|² ≤ Cη ≤ N^{-1+τ}`; we take
`η = N^{-1+θ}` with `θ = min(τ, min(c,1))/2 < τ`, so that the constant is absorbed.  The
hypothesis is an `N`-dependent-energy Theorem 2.21 rather than `RBM.Thm221'`/`RBM.Thm221`,
because the local law has to be evaluated at a moving energy.

**T235a** — *Theorem 2.2's Theorem 2.21 hypothesis is the (2.71)-free variant.*
① Paper position: Theorem 2.2 (§2.1) is deduced from Theorem 2.21 (§2.7); the p. 25 remark
after Theorem 2.21 is that Steps 1–5 never use (2.62) = (2.71).
② The paper is **not** changed: the paper's Theorem 2.21 carries (2.62) in both hypothesis and
conclusion, and its Theorem 2.2 is deduced from that.  We deduce Theorem 2.2 from the strictly
smaller hypothesis table of the p. 25 remark instead — `RBM.delocalization_of_Thm221N'` now
takes `RBM.Thm221NoELN'` where it used to take `RBM.Thm221N'`, and
`RBM.delocalization_of_Thm221N` takes `RBM.Thm221NoELN` where it used to take `RBM.Thm221N`.
③ Lines: two hypothesis slots (the conclusion is unchanged — `rfl`-probe in §`Deloc`).
④ Not renumbered.

Note that `RBM.Thm221NoELN'` is **incomparable** with `RBM.Thm221N'`, not weaker as a `Prop`:
its `step` neither consumes nor produces (2.71), so a bare `RBM.Thm221N'` (whose `step` demands
`RBM.BoundsN` as *input*) no longer suffices for Theorem 2.2.  What justifies the swap is that
`Flow/Thm221NoEL.lean` §5b produces the (2.71)-free form directly from Steps 1–5, so the
replacement hypothesis is the one the repository can actually discharge.
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

/-- **Theorem 2.21, p. 25 variant, at an `N`-dependent energy**: (2.71) removed from both the
assumption and the statement.  Verbatim `RBM.Thm221NoEL` with `E : ℕ → ℝ` and `|E N| ≤ 2 - κ`
for every `N`; `RBM.Thm221NoELN.toThm221NoEL` specializes it back (T235).

As for `RBM.Thm221NoEL` versus `RBM.Thm221`, this is **incomparable** with `RBM.Thm221N`:
it neither demands nor produces (2.71).  The p. 25 remark — Steps 1–5 never use (2.71) — is
what justifies it, and `Flow/Thm221NoEL.lean` §5b produces it from the steps. -/
structure Thm221NoELN (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
    (∀ N, t N < 1) → Cond272N B E s t → BoundsCoreN X E s → BoundsCoreN X E t

/-- **Theorem 2.21 without (2.71), with the gained (2.72), at an `N`-dependent energy.**
Verbatim `RBM.Thm221NoEL'`; this is the variant the six steps of §2.7 can actually produce, and
the one `RBM.BoundsCoreN_of_Thm221NoELN'` uses. -/
structure Thm221NoELN' (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
    (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272N' B E s t c →
    BoundsCoreN X E s → BoundsCoreN X E t

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

/-- **(2.67) with (2.71) removed**, at an `N`-dependent energy: (2.68)–(2.70) hold at `t = 0`
with no error.  The forgetful corollary of `RBM.BoundsN_zero`; `RBM.BoundsCore_zero` is its
constant-energy specialization (T235). -/
theorem BoundsCoreN_zero (hE : ∀ N, |E N| ≤ 2) : BoundsCoreN X E (fun _ => 0) :=
  (BoundsN_zero X hE).toBoundsCoreN

/-- (2.68)–(2.70) at a time sequence only depend on it for large `N`.  Verbatim
`RBM.BoundsN.congr` with the `expect` line deleted; `RBM.BoundsCore.congr` is its
constant-energy specialization (T235). -/
theorem BoundsCoreN.congr {s t : ℕ → ℝ} (h : BoundsCoreN X E s)
    (hst : ∀ᶠ N : ℕ in atTop, s N = t N) : BoundsCoreN X E t where
  LmK n hn := (h.LmK n hn).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  decay D hD := (h.decay D hD).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  localLaw := h.localLaw.congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
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
theorem boundsGrid_of_fields {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {P : (ℕ → ℝ) → Prop} (hzero : P (fun _ => 0))
    (hcongr : ∀ u v : ℕ → ℝ, P u → (∀ᶠ N : ℕ in atTop, u N = v N) → P v)
    (hstep : ∀ c : ℝ, 0 < c → ∀ u v : ℕ → ℝ, (∀ N, 0 ≤ u N) → (∀ N, u N ≤ v N) →
      (∀ N, v N < 1) → Cond272N' B E u v c → P u → P v)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : P t := by
  obtain ⟨τ', hτ', c, hc0, n₀, hgrid⟩ := B.eventually_flow_gridN' hκ hτ
  have hg := hgrid E hE t ht0 ht
  have hE2' : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  let u : ℕ → ℕ → ℝ := fun k N => gridT (B.W N) τ' (t N) k
  have key : ∀ k, P (u k) := by
    intro k
    induction k with
    | zero =>
      have h0 : u 0 = fun _ => 0 := funext fun N => gridT_zero (ht0 N)
      rw [h0]
      exact hzero
    | succ k ih =>
      refine hstep c hc0 (u k) (u (k + 1)) (fun N => ?_) (fun N => ?_) (fun N => ?_) ?_ ih
      · exact le_min (gridS_nonneg (B.one_le_W N) hτ'.le k) (ht0 N)
      · exact gridT_mono (B.one_le_W N) hτ'.le (t N) (Nat.le_succ k)
      · exact (min_le_left _ _).trans_lt (gridS_lt_one (by linarith [B.one_le_W N]) _)
      · filter_upwards [hg] with N hN
        rw [etaT_div_etaT (hE2' N)]
        exact hN.2.2.2 k
  exact hcongr (u n₀) t (key n₀) (by filter_upwards [hg] with N hN; exact hN.1)

/-- **Lemmas 2.18, 2.19 and 2.20 (p. 24) at an `N`-dependent energy, from the gained
Theorem 2.21.**  Verbatim `RBM.Bounds_of_Thm221'` with `E N` in place of `E`; the one-line
specialization of `RBM.boundsGrid_of_fields` at `P := fun s => BoundsN X E s`. -/
theorem BoundsN_of_Thm221N' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221N' X κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsN X E t :=
  boundsGrid_of_fields hκ hE (BoundsN_zero X fun N => by linarith [hE N])
    (fun _ _ h hst => h.congr X hst)
    (fun c hc0 u v hu0 huv hv1 hcond h => hT.step E hE c hc0 u v hu0 huv hv1 hcond h) hτ ht0 ht

/-- **Lemmas 2.18, 2.19 and 2.20 at an `N`-dependent energy, from `RBM.Thm221N`.**  The
corollary of `RBM.BoundsN_of_Thm221N'` along `RBM.Thm221N.toThm221N'`. -/
theorem BoundsN_of_Thm221N {κ : ℝ} (hκ : 0 < κ) (hT : Thm221N X κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsN X E t :=
  BoundsN_of_Thm221N' X hκ (hT.toThm221N' hκ) hE hτ ht0 ht

/-- **`RBM.Thm221NoELN` implies its gained form.**  Verbatim `RBM.Thm221NoEL.toThm221NoEL'`. -/
theorem Thm221NoELN.toThm221NoELN' {X : Sample B} {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoELN X κ) :
    Thm221NoELN' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    hT.step E hE s t hs0 hst ht1
      (hcond.toCond272N (fun N => by linarith [abs_nonneg (E N), hE N]) hst ht1 hc0.le) hB

/-- **Lemmas 2.18 (2.60), 2.19 (2.63) and 2.20 (2.64) — everything except (2.62) — from the
(2.71)-free Theorem 2.21, at an `N`-dependent energy.**

Verbatim `RBM.BoundsCore_of_Thm221NoEL'` with `E N` in place of `E`, and verbatim
`RBM.BoundsN_of_Thm221N'` with `RBM.BoundsCoreN` in place of `RBM.BoundsN`: both are one-line
specializations of the same script `RBM.boundsGrid_of_fields`, which is the induction of p. 24
along the truncated grid `u_k = min(1 - W^{-kτ'}, t)` started at (2.67).  **No step of the
induction sees (2.71)** — the bundle `P` is a parameter of the script, and the three facts the
script needs of it are passed as fields (`hzero`, `hcongr`, `hstep`). -/
theorem BoundsCoreN_of_Thm221NoELN' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoELN' X κ)
    (hE : ∀ N, |E N| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsCoreN X E t :=
  boundsGrid_of_fields hκ hE (BoundsCoreN_zero X fun N => by linarith [hE N])
    (fun _ _ h hst => h.congr X hst)
    (fun c hc0 u v hu0 huv hv1 hcond h => hT.step E hE c hc0 u v hu0 huv hv1 hcond h) hτ ht0 ht

/-- **Lemmas 2.18–2.20 without (2.62), from `RBM.Thm221NoELN`** — the corollary of
`RBM.BoundsCoreN_of_Thm221NoELN'` along `RBM.Thm221NoELN.toThm221NoELN'`. -/
theorem BoundsCoreN_of_Thm221NoELN {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoELN X κ)
    (hE : ∀ N, |E N| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsCoreN X E t :=
  BoundsCoreN_of_Thm221NoELN' X hκ (hT.toThm221NoELN' hκ) hE hτ ht0 ht

/-! #### `rfl`-probe: the induction of p. 24 is unchanged (T235)

`RBM.BoundsN_of_Thm221N'` is now the one-line specialization of the shared script
`RBM.boundsGrid_of_fields`; the probe type-checks only if the two sides are proofs of the same
`Prop`, i.e. only if nothing about Lemmas 2.18–2.20 changed. -/
example {κ : ℝ} (hκ : 0 < κ) (hT : Thm221N' X κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) :
    BoundsN_of_Thm221N' X hκ hT hE hτ ht0 ht =
      boundsGrid_of_fields hκ hE (BoundsN_zero X fun N => by linarith [hE N])
        (fun _ _ h hst => h.congr X hst)
        (fun c hc0 u v hu0 huv hv1 hcond h =>
          hT.step E hE c hc0 u v hu0 huv hv1 hcond h) hτ ht0 ht := rfl

example {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoELN' X κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) :
    BoundsCoreN_of_Thm221NoELN' X hκ hT hE hτ ht0 ht =
      boundsGrid_of_fields hκ hE (BoundsCoreN_zero X fun N => by linarith [hE N])
        (fun _ _ h hst => h.congr X hst)
        (fun c hc0 u v hu0 huv hv1 hcond h =>
          hT.step E hE c hc0 u v hu0 huv hv1 hcond h) hτ ht0 ht := rfl

end Iteration

/-! ### The spectral parameters, **without the energy-slice condition**

`RBM.SpecSeqN`, `RBM.SpecSeqN.of_z`, `RBM.SpecSeq.toSpecSeqN` and the nine basic facts about
`RBM.SpecSeqN` moved to `Flow/Consequences.lean` (T235): they were duplicated there as
`RBM.SpecSeq.abs_E_le`, …, `RBM.SpecSeq.unifDetDom_rpow`, and those nine are now one-line
corollaries through `RBM.SpecSeq.toSpecSeqN`.  What stays here is the pair that needs
`RBM.BoundsN`, which is defined in this file. -/

namespace SpecSeqN

variable {κ τ : ℝ} {E : ℕ → ℝ} {z : ℕ → ℂ} (hz : SpecSeqN κ τ E z)
include hz

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

/-- **(2.68)–(2.70) at the time `t = lemT z`**, from `RBM.Thm221NoELN'` — the (2.71)-free
route (T235). -/
theorem boundsCoreN' (X : Sample B) (hκ : 0 < κ) (hT : Thm221NoELN' X κ) (hτ : 0 < τ) :
    BoundsCoreN X E (fun N => lemT (z N)) :=
  BoundsCoreN_of_Thm221NoELN' X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

/-- **(2.68)–(2.70) at the time `t = lemT z`**, from `RBM.Thm221NoELN`. -/
theorem boundsCoreN (X : Sample B) (hκ : 0 < κ) (hT : Thm221NoELN X κ) (hτ : 0 < τ) :
    BoundsCoreN X E (fun N => lemT (z N)) :=
  BoundsCoreN_of_Thm221NoELN X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

end SpecSeqN

/-! ### Theorem 2.3 at an `N`-dependent energy -/

section Main

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ : ℝ} {E : ℕ → ℝ}
  {z : ℕ → ℂ}

/-- **Theorem 2.3, (2.3)** (local semicircle law) at an `N`-dependent energy, from (2.64) and
(2.65): `max_{x,y} |(G(z) - m(z))_{xy}| ≺ (W ℓ(z) η)^{-1/2}`, on `RBM.BoundsCoreN` — (2.71) is
not used (T221).  Verbatim `RBM.localLaw_of_boundsCore`, through the shared script
`RBM.localLaw_of_fields`. -/
theorem localLaw_of_boundsCoreN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsCoreN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) :=
  localLaw_of_fields T E hz.im_pos hz.lemE_eq
    (hz.unifDetDom_rpow hκ (by norm_num : (0 : ℝ) ≤ 1 / 2)) hB.localLaw

/-- **Theorem 2.3, (2.3)** at an `N`-dependent energy.  Verbatim `RBM.localLaw_of_bounds`. -/
theorem localLaw_of_boundsN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) :=
  localLaw_of_boundsCoreN T hκ hz hB.toBoundsCoreN

/-- **Theorem 2.3, (2.4)** in loop form at an `N`-dependent energy, on `RBM.BoundsCoreN`.
Verbatim `RBM.loop1_of_boundsCore`, through `RBM.loop1_of_fields`. -/
theorem loop1_of_boundsCoreN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsCoreN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  loop1_of_fields T T1 E hz.im_pos hz.lemE_eq (hz.unifDetDom_pow hκ 1) (hB.LmK 1 le_rfl)

/-- **Theorem 2.3, (2.4)** in loop form at an `N`-dependent energy.  Verbatim
`RBM.loop1_of_bounds`. -/
theorem loop1_of_boundsN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  loop1_of_boundsCoreN T T1 hκ hz hB.toBoundsCoreN

/-- **Theorem 2.3, (2.4)** (partial tracial local law) at an `N`-dependent energy, on
`RBM.BoundsCoreN`.  Verbatim `RBM.partialTrace_of_boundsCore`, through
`RBM.partialTrace_of_fields`. -/
theorem partialTrace_of_boundsCoreN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsCoreN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  partialTrace_of_fields T T1 E hz.im_pos hz.lemE_eq (hz.unifDetDom_pow hκ 1) (hB.LmK 1 le_rfl)

/-- **Theorem 2.3, (2.4)** (partial tracial local law) at an `N`-dependent energy.  Verbatim
`RBM.partialTrace_of_bounds`. -/
theorem partialTrace_of_boundsN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  partialTrace_of_boundsCoreN T T1 hκ hz hB.toBoundsCoreN

/-- **Theorem 2.3, the tracial local law** at an `N`-dependent energy, on `RBM.BoundsCoreN`.
Verbatim `RBM.trace_of_boundsCore`, through `RBM.trace_of_fields`. -/
theorem trace_of_boundsCoreN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsCoreN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  trace_of_fields T T1 E hz.im_pos hz.lemE_eq (hz.unifDetDom_pow hκ 1) (hB.LmK 1 le_rfl)

/-- **Theorem 2.3, the tracial local law** at an `N`-dependent energy.  Verbatim
`RBM.trace_of_bounds`. -/
theorem trace_of_boundsN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) :=
  trace_of_boundsCoreN T T1 hκ hz hB.toBoundsCoreN

/-- **Theorem 2.3 (local semicircle law) at an `N`-dependent energy**, on `RBM.BoundsCoreN`:
(2.71) is not used (T221).  Verbatim `RBM.localSemicircleLaw_of_boundsCore`. -/
theorem localSemicircleLaw_of_boundsCoreN (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsCoreN X E (fun N => lemT (z N))) {τ' D : ℝ}
    (hτ' : 0 < τ') (hD : 0 < D) :
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
  ⟨B.prob_le_of_stochDom (fun N _ _ => Real.rpow_nonneg (hz.zScale_inv_nonneg N) _)
      (localLaw_of_boundsCoreN T hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (partialTrace_of_boundsCoreN T T1 hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (trace_of_boundsCoreN T T1 hκ hz hB) hτ' hD⟩

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
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  localSemicircleLaw_of_boundsCoreN T T1 hκ hz (hz.boundsN' X hκ hT hτ).toBoundsCoreN hτ' hD

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

/-- **Theorem 2.3 for an arbitrary sequence of spectral parameters, on `RBM.BoundsCoreN`** —
no energy parameter and no (2.71).  `RBM.SpecSeqN.of_z` supplies the spectral data, with
`E N := lemE (z N)`. -/
theorem localSemicircleLaw_of_boundsCoreN_of_z (T : Transfer X) (T1 : TransferLoop1 T)
    (hκ : 0 < κ) {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im)
    (hB : BoundsCoreN X (fun N => lemE (z N)) (fun N => lemT (z N))) {τ' D : ℝ} (hτ' : 0 < τ')
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
  localSemicircleLaw_of_boundsCoreN T T1 hκ (SpecSeqN.of_z him_pos him_le_one habs_re him_ge) hB
    hτ' hD

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

/-! #### `rfl`-probes: the merge of T221 changed no statement

`Eq` forces both sides to have the same type, so each `example` type-checks only if the two
conclusions are **definitionally equal** (T107's technique).  The first five check the merge
*across files*: the fixed-energy statements of `Flow/Consequences.lean` are literally the
constant-energy case of the `N`-dependent ones here, which is why both can be one-line
corollaries of the single script (`RBM.localLaw_of_fields`, …).  The last one checks the same
for the assembled Theorem 2.3. -/

section Probes

variable (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) {E₀ : ℝ}
  (hz : SpecSeq κ τ E₀ z) (hB : BoundsCore X E₀ (fun N => lemT (z N))) {τ' D : ℝ}
  (hτ' : 0 < τ') (hD : 0 < D)

example : localLaw_of_boundsCore T hκ hz hB =
    localLaw_of_boundsCoreN T hκ hz.toSpecSeqN hB.toBoundsCoreN := rfl

example : loop1_of_boundsCore T T1 hκ hz hB =
    loop1_of_boundsCoreN T T1 hκ hz.toSpecSeqN hB.toBoundsCoreN := rfl

example : partialTrace_of_boundsCore T T1 hκ hz hB =
    partialTrace_of_boundsCoreN T T1 hκ hz.toSpecSeqN hB.toBoundsCoreN := rfl

example : trace_of_boundsCore T T1 hκ hz hB =
    trace_of_boundsCoreN T T1 hκ hz.toSpecSeqN hB.toBoundsCoreN := rfl

example : localSemicircleLaw_of_boundsCore T T1 hκ hz hB hτ' hD =
    localSemicircleLaw_of_boundsCoreN T T1 hκ hz.toSpecSeqN hB.toBoundsCoreN hτ' hD := rfl

example (hT : Thm221N X κ) (hτ : 0 < τ) :
    localSemicircleLaw_of_Thm221 T T1 hκ hT.toThm221 hτ hz hτ' hD =
      localSemicircleLaw_of_Thm221N T T1 hκ hT hτ hz.toSpecSeqN hτ' hD := rfl

end Probes

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


/-! ## The probabilistic half of Theorem 2.2 (T199)

Theorem 2.3 controls `G(z)` at a **deterministic** sequence of spectral parameters, while
(2.10) has to be read at `z = λ_k(ω) + iη`, whose energy is *random*.  The paper closes the gap
in one sentence ("Following a standard delocalization argument … Applying (2.3) and the fact
that `ℓ ∼ L`, we obtain `G - m ≪ 1`", p. 9); in Lean it costs three ingredients:

1. an **energy net** `RBM.bulkNet κ N` of `4(N+1)^4 + 1` points of `[-2+κ, 2-κ]`, whose union
   bound sits *inside* the probability — this is what `RBM.StochDom.of_forall_seq` provides,
   from the local law along *every sequence* of net points (`RBM.localLaw_of_boundsN` at the
   `N`-dependent energies of this file, which is exactly why route (i) had to come first);
2. the **deterministic Lipschitz continuity of `G` in the energy**,
   `RBM.im_green_lipschitz_energy` of `RBM1D/Delocalization.lean`
   (`|Im G_xx(E+iη) - Im G_xx(E'+iη)| ≤ |E-E'| η^{-2}`), which transports the net bound to the
   random energy `λ_k(ω)`;
3. the lower bound `RBM.Band.rpow_le_zScale`: at `η = N^{-1+θ}` with `θ ≤ c` the scale
   `W ℓ(z) η` is at least `N^θ/2`, which is the paper's "`ℓ ∼ L`" step and is where (2.2) is
   used.

No probabilistic modulus of continuity is needed: a choice of one net point per `N` *is* a
sequence, and the `ω`-dependence of `λ_k(ω)` is handled pointwise on the good event.

### A `≺`-bound along every sequence of net points

`RBM.StochDom.of_forall_seq` is the energy analogue of `RBM.Gauss.stochDom_reindex_of_forall_seq`
(`RBM1D/Gauss/Step1Hyp.lean`), which cannot be imported here: `Gauss/` sits *below* `Flow/`.
The generic version should be sunk to `RBM1D/Defs/` once a ticket owns that file. -/

section NetEngine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A bound along every sequence of indices is eventually a bound at every index.**  If for
every choice function `j : ∀ N, J N` the family `ξ(N, j N, ·) ≺ ζ(N, j N, ·)`, then for large
`N` the failure probability is below `N^{-D}` *simultaneously for all* `j ∈ J(N)` — the point
being that `N₀` does not depend on `j`.  The proof is the contrapositive: a bad `j` for
infinitely many `N` assembles (by choice) into a bad sequence. -/
theorem eventually_forall_measure_index_le {J V : ℕ → Type*} [∀ N, Nonempty (J N)]
    {ξ ζ : ∀ N, J N × V N → Ω → ℝ}
    (h : ∀ j : ∀ N, J N, StochDom P (fun N v ω => ξ N (j N, v) ω) (fun N v ω => ζ N (j N, v) ω))
    {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ j : J N,
      P {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (j, v) ω < ξ N (j, v) ω}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set bad : ℕ → Prop := fun N => ∃ j : J N,
    ¬ (P {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (j, v) ω < ξ N (j, v) ω}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) with hbad_def
  have hcon' : ∃ᶠ N : ℕ in atTop, bad N := by
    refine hcon.mono fun N hN => ?_
    simpa only [hbad_def, not_forall] using hN
  set u : ∀ N, J N := fun N => if hN : bad N then hN.choose else Classical.arbitrary (J N)
    with hu_def
  have hseq := h u τ hτ D hD
  obtain ⟨N, hNbad, hNgood⟩ := (hcon'.and_eventually hseq).exists
  have huN : u N = hNbad.choose := by rw [hu_def]; exact dite_eq_left hNbad
  refine hNbad.choose_spec ?_
  rw [← huN]
  exact hNgood

/-- **`≺` from a `≺`-bound along every sequence of indices**, with the union over a
polynomially small index set `J(N)` *inside* the probability. -/
theorem StochDom.of_forall_seq {J V : ℕ → Type*} [∀ N, Fintype (J N)] [∀ N, Nonempty (J N)]
    {ξ ζ : ∀ N, J N × V N → Ω → ℝ}
    (h : ∀ j : ∀ N, J N, StochDom P (fun N v ω => ξ N (j N, v) ω) (fun N v ω => ζ N (j N, v) ω))
    {C : ℝ} (hC : 0 ≤ C)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (J N) : ℝ) ≤ (N : ℝ) ^ C) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hcard, eventually_forall_measure_index_le h hτ (by linarith : 0 < D + C),
    eventually_ge_atTop 1] with N hcardN hslice hN1
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + C)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hset : badSet ξ ζ τ N
      = ⋃ j : J N, {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (j, v) ω < ξ N (j, v) ω} := by
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_iUnion, Prod.exists]
  calc P (badSet ξ ζ τ N)
      ≤ ∑ j : J N, P {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (j, v) ω < ξ N (j, v) ω} := by
        rw [hset]; exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _j : J N, ENNReal.ofReal ((N : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun j _ => hslice j
    _ = ENNReal.ofReal (Fintype.card (J N) * (N : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ C * (N : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcardN hp)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by rw [rpow_mul_rpow_neg_add hN1]

end NetEngine

/-! ### The energy net

`RBM.bulkNet κ N` is the arithmetic net of `[-2+κ, 2-κ]` of mesh `(N+1)^{-4}`, clamped to the
interval.  The two requirements on a net pull in opposite directions and both are **proved**
here, for one and the same net, rather than assumed (`RBM.exists_bulkNet_close`: fine enough;
`RBM.card_bulkNet_le`: coarse enough for the union bound; `RBM.netDen_inv_div_rpow_le`: fine
enough for the Lipschitz step at `η = N^{-1+θ}`). -/

/-- The reciprocal mesh `(N+1)^4` of the energy net of Theorem 2.2. -/
def netDen (N : ℕ) : ℕ := (N + 1) ^ 4

theorem netDen_pos (N : ℕ) : 0 < netDen N := pow_pos N.succ_pos 4

theorem netDen_cast_pos (N : ℕ) : (0 : ℝ) < (netDen N : ℝ) := by exact_mod_cast netDen_pos N

/-- The energy net of the bulk `[-2+κ, 2-κ]`, of mesh `(N+1)^{-4}`. -/
noncomputable def bulkNet (κ : ℝ) (N : ℕ) (j : Fin (4 * netDen N + 1)) : ℝ :=
  min (2 - κ) (-2 + κ + (j : ℕ) / (netDen N : ℝ))

/-- Every net point lies in the bulk. -/
theorem abs_bulkNet_le {κ : ℝ} (hκ : κ ≤ 2) (N : ℕ) (j : Fin (4 * netDen N + 1)) :
    |bulkNet κ N j| ≤ 2 - κ := by
  have hd := netDen_cast_pos N
  have hj : (0 : ℝ) ≤ (j : ℕ) / (netDen N : ℝ) := by positivity
  rw [abs_le]
  refine ⟨?_, min_le_left _ _⟩
  rw [bulkNet, le_min_iff]
  exact ⟨by linarith, by linarith⟩

/-- **The net is `(N+1)^{-4}`-dense in the bulk.** -/
theorem exists_bulkNet_close {κ : ℝ} (hκ0 : 0 ≤ κ) (N : ℕ) {E : ℝ}
    (hE : |E| ≤ 2 - κ) :
    ∃ j : Fin (4 * netDen N + 1), |E - bulkNet κ N j| ≤ 1 / (netDen N : ℝ) := by
  have hd := netDen_cast_pos N
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hd0 : (0 : ℝ) ≤ E + 2 - κ := by linarith
  have hmle : (⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ : ℝ) ≤ (E + 2 - κ) * (netDen N : ℝ) :=
    Nat.floor_le (by positivity)
  have hmlt : (E + 2 - κ) * (netDen N : ℝ) < (⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hmbound : ⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ ≤ 4 * netDen N := by
    have h1 : ((⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ : ℕ) : ℝ) ≤ ((4 * netDen N : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h1
  refine ⟨⟨⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊, by omega⟩, ?_⟩
  set q : ℝ := (⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ : ℝ) / (netDen N : ℝ) with hq
  have hq0 : (0 : ℝ) ≤ q := by rw [hq]; positivity
  have hqd : q ≤ E + 2 - κ := by rw [hq, div_le_iff₀ hd]; linarith
  have hdq : E + 2 - κ - q ≤ 1 / (netDen N : ℝ) := by
    have h1 : E + 2 - κ ≤ ((⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ : ℝ) + 1) / (netDen N : ℝ) := by
      rw [le_div_iff₀ hd]; linarith
    have h2 : ((⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊ : ℝ) + 1) / (netDen N : ℝ)
        = q + 1 / (netDen N : ℝ) := by rw [hq]; ring
    linarith [h1, h2.le, h2.ge]
  have hval : bulkNet κ N ⟨⌊(E + 2 - κ) * (netDen N : ℝ)⌋₊, by omega⟩ = -2 + κ + q := by
    rw [bulkNet, min_eq_right]
    exact (by linarith : -2 + κ + q ≤ 2 - κ)
  rw [hval, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The net has polynomially many points. -/
theorem card_bulkNet_le : ∀ᶠ N : ℕ in atTop,
    (Fintype.card (Fin (4 * netDen N + 1)) : ℝ) ≤ (N : ℝ) ^ (5 : ℝ) := by
  filter_upwards [eventually_ge_atTop 9] with N hN
  have hNR : (9 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Fintype.card_fin]
  have hstep : ((4 * netDen N + 1 : ℕ) : ℝ) = 4 * ((N : ℝ) + 1) ^ 4 + 1 := by
    rw [netDen]; push_cast; ring
  rw [hstep]
  have h5 : (N : ℝ) ^ (5 : ℝ) = (N : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast (N : ℝ) 5]; norm_num
  rw [h5]
  nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ (N:ℝ) + 1) (by linarith : (N:ℝ) + 1 ≤ 2 * N) 4,
    pow_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)) 4, pow_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)) 5]




variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The scale `W ℓ(z) η` at `η = N^{-1+θ}` is at least `N^θ / 2`**, for `0 < θ ≤ c`. -/
theorem Band.rpow_le_zScale (B : Band Ω) {θ : ℝ} (hθ0 : 0 < θ) (hθc : θ ≤ B.c) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, z.im = (N : ℝ) ^ (-1 + θ) →
      (N : ℝ) ^ θ / 2 ≤ B.zScale N z := by
  filter_upwards [B.bandwidth, B.dim, eventually_ge_atTop 1] with N hbw hdim hN1 z hz
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := by rw [hz]; exact Real.rpow_pos_of_pos hN0 _
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL0 : (0 : ℝ) < B.L N := by exact_mod_cast (B.three_le_L N).trans_lt' (by norm_num)
  have hmin : min (1 / Real.sqrt z.im) (B.L N : ℝ) ≤ ellZ (B.L N) z := by
    rw [ellZ, ellOf]; linarith
  have hkey : (N : ℝ) ^ θ / 2 ≤ (B.W N : ℝ) * min (1 / Real.sqrt z.im) (B.L N : ℝ) * z.im := by
    rcases le_total (1 / Real.sqrt z.im) (B.L N : ℝ) with h | h
    · rw [min_eq_left h]
      -- `W * η / √η = W √η ≥ N^{1/2+c} N^{(-1+θ)/2} = N^{c+θ/2} ≥ N^θ`
      have hsq : Real.sqrt z.im = (N : ℝ) ^ ((-1 + θ) / 2) := by
        rw [hz, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
        congr 1; ring
      have hval : (B.W N : ℝ) * (1 / Real.sqrt z.im) * z.im
          = (B.W N : ℝ) * Real.sqrt z.im := by
        have h1 : Real.sqrt z.im * Real.sqrt z.im = z.im := Real.mul_self_sqrt hη.le
        have h2 : Real.sqrt z.im ≠ 0 := by positivity
        field_simp
        nlinarith [h1]
      rw [hval, hsq]
      have hexp : (N : ℝ) ^ ((1 : ℝ) / 2 + B.c) * (N : ℝ) ^ ((-1 + θ) / 2)
          = (N : ℝ) ^ (B.c + θ / 2) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      have hmono : (N : ℝ) ^ θ ≤ (N : ℝ) ^ (B.c + θ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      have hpos : (0 : ℝ) < (N : ℝ) ^ ((-1 + θ) / 2) := Real.rpow_pos_of_pos hN0 _
      calc (N : ℝ) ^ θ / 2 ≤ (N : ℝ) ^ θ := by
            have := Real.rpow_pos_of_pos hN0 θ; linarith
        _ ≤ (N : ℝ) ^ (B.c + θ / 2) := hmono
        _ = (N : ℝ) ^ ((1 : ℝ) / 2 + B.c) * (N : ℝ) ^ ((-1 + θ) / 2) := hexp.symm
        _ ≤ (B.W N : ℝ) * (N : ℝ) ^ ((-1 + θ) / 2) := by gcongr
    · rw [min_eq_right h]
      -- `W L η ≥ (N/2) η = N^θ/2`
      have hWL : (N : ℝ) ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ)) := by
        have := hdim.2
        have hc : ((2 * (B.W N * B.L N) : ℕ) : ℝ) = 2 * ((B.W N : ℝ) * (B.L N : ℝ)) := by
          push_cast; ring
        calc (N : ℝ) ≤ ((2 * (B.W N * B.L N) : ℕ) : ℝ) := by exact_mod_cast this
          _ = _ := hc
      have hexp : (N : ℝ) * (N : ℝ) ^ (-1 + θ) = (N : ℝ) ^ θ := by
        nth_rewrite 1 [show (N : ℝ) = (N : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
        rw [← Real.rpow_add hN0]; congr 1; ring
      rw [hz]
      have hη' : (0 : ℝ) < (N : ℝ) ^ (-1 + θ) := Real.rpow_pos_of_pos hN0 _
      nlinarith [hη', hWL, hexp]
  calc (N : ℝ) ^ θ / 2 ≤ (B.W N : ℝ) * min (1 / Real.sqrt z.im) (B.L N : ℝ) * z.im := hkey
    _ ≤ (B.W N : ℝ) * ellZ (B.L N) z * z.im := by
        have : (0 : ℝ) ≤ (B.W N : ℝ) := hW0.le
        gcongr
    _ = B.zScale N z := rfl



/-- The mesh of the net is fine enough for the Lipschitz error: at `η = N^{-1+θ}` the error
`mesh / η = N^{-3-θ}` is below `η` itself.  Together with `RBM.card_bulkNet_le` (the net is
coarse enough for the union bound) this is the pair of competing requirements on the mesh. -/
theorem netDen_inv_div_rpow_le {θ : ℝ} (hθ : 0 ≤ θ) {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) / (netDen N : ℝ) / (N : ℝ) ^ (-1 + θ) ≤ (N : ℝ) ^ (-1 + θ) := by
  have hR0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) ^ (-1 + θ) := Real.rpow_pos_of_pos hR0 _
  have hden : (1 : ℝ) / (netDen N : ℝ) ≤ (N : ℝ) ^ (-4 : ℝ) := by
    have h4 : (N : ℝ) ^ (4 : ℕ) ≤ (netDen N : ℝ) := by
      rw [netDen]; push_cast
      exact pow_le_pow_left₀ hR0.le (by linarith) 4
    have h4pos : (0 : ℝ) < (N : ℝ) ^ (4 : ℕ) := by positivity
    have hrw : (N : ℝ) ^ (-4 : ℝ) = 1 / (N : ℝ) ^ (4 : ℕ) := by
      rw [show (-4 : ℝ) = -(4 : ℕ) by norm_num, Real.rpow_neg hR0.le, Real.rpow_natCast]
      exact (one_div _).symm
    rw [hrw]
    exact one_div_le_one_div_of_le h4pos h4
  have h1 : (1 : ℝ) / (netDen N : ℝ) / (N : ℝ) ^ (-1 + θ)
      ≤ (N : ℝ) ^ (-4 : ℝ) / (N : ℝ) ^ (-1 + θ) := by gcongr
  have h2 : (N : ℝ) ^ (-4 : ℝ) / (N : ℝ) ^ (-1 + θ) = (N : ℝ) ^ (-3 - θ) := by
    rw [← Real.rpow_sub hR0]; congr 1; ring
  have h3 : (N : ℝ) ^ (-3 - θ) ≤ (N : ℝ) ^ (-1 + θ) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  linarith [h1, h2.le, h2.ge, h3]

/-! ### The scale `W ℓ(z) η` at `η = N^{-1+θ}` -/

section Deloc

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B}

/-- **Theorem 2.2 (Delocalization), p. 8.**  Under (2.2) (`RBM.Band.bandwidth`), for any small
`κ, τ > 0` and large `D > 0`, for all large `N`,

`P( max_k ‖ψ_k‖²_∞ · 1(λ_k ∈ [-2+κ, 2-κ]) ≤ N^{-1+τ} ) > 1 - N^{-D}`,

written — as everywhere in `Flow/` — as a bound on the probability that the estimate *fails*,
with the max over `k` (and over the sites `x` inside `‖·‖_∞`) as an existential in the event.
The indicator is in the body, as in the paper.

The proof is the paper's, with the gap of p. 9 filled: `η := N^{-1+θ}` with
`θ := min(τ, min(c, 1))/2` (so `θ ≤ τ/2` and `θ ≤ c`, the latter being the paper's
`η ≤ (W/N)²`); on the net of `RBM.bulkNet κ N` the local law gives `|G_xx - m| ≤ 1` and hence
`|G_xx| ≤ 2` (`RBM.norm_msc_lt_one` and `RBM.Band.rpow_le_zScale`); the Lipschitz estimate
`RBM.sq_norm_eigenvector_le_of_norm_green_le_near` moves that to `λ_k(ω)` at a cost
`mesh/η ≤ η`; and `|ψ_k(x)|² ≤ 2η + η = 3N^{-1+θ} ≤ N^{-1+τ}`.

The hypotheses are the model (`RBM.Band`, `RBM.Sample`), the identity in law
`RBM.Transfer` (2.39) and Theorem 2.21 at an `N`-dependent energy **with (2.71) removed from
both sides** (`RBM.Thm221NoELN'`, the p. 25 variant).  `RBM.TransferLoop1` is *not* needed:
only the entrywise law (2.3) enters.

⭐ T235: the hypothesis used to be `RBM.Thm221N'`, whose `step` demands **and** produces
(2.71) = (2.62).  Theorem 2.2 never needed it: the only thing it takes from Theorem 2.21 is
(2.70) at `t = lemT z` (`RBM.SpecSeqN.boundsCoreN'`, through
`RBM.BoundsCoreN_of_Thm221NoELN'`), so the whole `expect` side — and with it every Step 6
datum — is gone from the hypothesis table of Theorem 2.2.  The conclusion is unchanged
(`rfl`-probe below). -/
theorem delocalization_of_Thm221N' (T : Transfer X) {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELN' X κ)
    {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      B.P {ω | ∃ p : B.Idx N × B.Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖(T.hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            ((T.hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  rcases lt_or_ge 2 κ with hκ2 | hκ2
  · -- the bulk is empty, so the indicator vanishes and the bad event is empty
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hempty : {ω | ∃ p : B.Idx N × B.Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖(T.hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            ((T.hermitian N ω).eigenvalues p.1)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      intro p
      have hind : Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
          ((T.hermitian N ω).eigenvalues p.1) = 0 := by
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_Icc, not_and, not_le]
        intro h; linarith
      rw [hind, mul_zero]
      exact Real.rpow_nonneg hN0 _
    rw [hempty, measure_empty]
    exact zero_le
  -- the main case `κ ≤ 2`
  have hcpos := B.c_pos
  obtain ⟨θ, hθ0, hθτ, hθc, hθ1⟩ :
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ τ / 2 ∧ θ ≤ B.c ∧ θ ≤ 1 / 2 := by
    refine ⟨min τ (min B.c 1) / 2, ?_, ?_, ?_, ?_⟩
    · have h1 : 0 < min B.c 1 := lt_min hcpos one_pos
      have h2 := lt_min hτ h1
      linarith
    · have := min_le_left τ (min B.c 1); linarith
    · have h1 := min_le_right τ (min B.c 1)
      have h2 := min_le_left B.c 1
      linarith
    · have h1 := min_le_right τ (min B.c 1)
      have h2 := min_le_right B.c 1
      linarith
  obtain ⟨η, hη0, hη1, hηN⟩ :
      ∃ η : ℕ → ℝ, (∀ N, 0 < η N) ∧ (∀ N, η N ≤ 1) ∧
        (∀ N : ℕ, 1 ≤ N → η N = (N : ℝ) ^ (-1 + θ)) := by
    refine ⟨fun N => (max (N : ℝ) 1) ^ (-1 + θ), fun N => ?_, fun N => ?_, fun N hN => ?_⟩
    · exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _
    · exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_right _ _) (by linarith)
    · have h : max (N : ℝ) 1 = (N : ℝ) := max_eq_left (by exact_mod_cast hN)
      simp only [h]
  obtain ⟨znet, hzeq⟩ : ∃ znet : ∀ N : ℕ, Fin (4 * netDen N + 1) → ℂ,
      ∀ (N : ℕ) (j : Fin (4 * netDen N + 1)),
        znet N j = ((bulkNet κ N j : ℝ) : ℂ) + ((η N : ℝ) : ℂ) * Complex.I :=
    ⟨_, fun N j => rfl⟩
  have hzre : ∀ (N : ℕ) (j : Fin (4 * netDen N + 1)), (znet N j).re = bulkNet κ N j := by
    intro N j; rw [hzeq]; simp
  have hzim : ∀ (N : ℕ) (j : Fin (4 * netDen N + 1)), (znet N j).im = η N := by
    intro N j; rw [hzeq]; simp
  have hspec : ∀ j : ∀ N, Fin (4 * netDen N + 1),
      SpecSeqN κ θ (fun N => lemE (znet N (j N))) (fun N => znet N (j N)) := by
    intro j
    refine SpecSeqN.of_z (fun N => ?_) (fun N => ?_) (fun N => ?_) ?_
    · rw [hzim]; exact hη0 N
    · rw [hzim]; exact hη1 N
    · rw [hzre]; exact abs_bulkNet_le hκ2 N (j N)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hzim, hηN N hN]
  have hsd : StochDom B.P
      (fun N (p : Fin (4 * netDen N + 1) × (B.Idx N × B.Idx N)) ω =>
        ‖(green (T.Hband N ω) (znet N p.1) -
          msc (znet N p.1) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) p.2.1 p.2.2‖)
      (fun N p _ => (B.zScale N (znet N p.1))⁻¹ ^ ((1 : ℝ) / 2)) := by
    refine StochDom.of_forall_seq (fun j => ?_) (by norm_num : (0:ℝ) ≤ 5) card_bulkNet_le
    -- the type ascription is load-bearing: without it the elaborator beta-reduces the pair
    -- projections only through a very slow `isDefEq`
    exact show StochDom B.P (fun N (v : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (znet N (j N)) -
          msc (znet N (j N)) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) v.1 v.2‖)
      (fun N (_ : B.Idx N × B.Idx N) (_ : Ω) => (B.zScale N (znet N (j N)))⁻¹ ^ ((1 : ℝ) / 2))
      from localLaw_of_boundsCoreN T hκ (hspec j) ((hspec j).boundsCoreN' X hκ hT hθ0)
  have hgood := hsd.highProb (τ := θ / 4) (by positivity)
  filter_upwards [hgood D hD, eventually_ge_atTop 1, B.rpow_le_zScale hθ0 hθc,
    eventually_le_rpow (Real.sqrt 2) (by positivity : (0:ℝ) < θ / 4),
    eventually_le_rpow 3 (half_pos hτ)] with N hN hN1 hzs hs2 h3
  refine (measure_mono ?_).trans hN
  intro ω hω hmem
  obtain ⟨p, hp⟩ := hω
  have hR0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  by_cases hIcc : (T.hermitian N ω).eigenvalues p.1 ∈ Set.Icc (-2 + κ) (2 - κ)
  swap
  · rw [Set.indicator_of_notMem hIcc, mul_zero] at hp
    exact absurd hp (not_lt.2 (Real.rpow_nonneg hR0.le _))
  simp only [Set.indicator_of_mem hIcc, mul_one] at hp
  obtain ⟨hIcc1, hIcc2⟩ := hIcc
  have habs : |(T.hermitian N ω).eigenvalues p.1| ≤ 2 - κ := abs_le.2 ⟨by linarith, hIcc2⟩
  obtain ⟨j, hj⟩ := exists_bulkNet_close hκ.le N habs
  have hzspos : (0 : ℝ) < (N : ℝ) ^ θ / 2 := by positivity
  have hzs' : (N : ℝ) ^ θ / 2 ≤ B.zScale N (znet N j) :=
    hzs (znet N j) (by rw [hzim, hηN N hN1])
  have hzpos : 0 < B.zScale N (znet N j) := lt_of_lt_of_le hzspos hzs'
  -- the local law at the net point `j`, on the diagonal entry `x = p.2`
  have hentry := hmem (j, (p.2, p.2))
  have hdiag : (green (T.Hband N ω) (znet N j) -
      msc (znet N j) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) p.2 p.2
      = green (T.Hband N ω) (znet N j) p.2 p.2 - msc (znet N j) := by
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  rw [hdiag] at hentry
  -- `N^{θ/4} (W ℓ η)^{-1/2} ≤ 1`
  have hsmall : (N : ℝ) ^ (θ / 4) * (B.zScale N (znet N j))⁻¹ ^ ((1 : ℝ) / 2) ≤ 1 := by
    have hinv : (B.zScale N (znet N j))⁻¹ ≤ 2 * (N : ℝ) ^ (-θ) := by
      have h1 : (B.zScale N (znet N j))⁻¹ ≤ ((N : ℝ) ^ θ / 2)⁻¹ := inv_anti₀ hzspos hzs'
      have h2 : ((N : ℝ) ^ θ / 2)⁻¹ = 2 * (N : ℝ) ^ (-θ) := by
        rw [Real.rpow_neg hR0.le]
        field_simp
      linarith [h1, h2.le, h2.ge]
    have e1 : (2 * (N : ℝ) ^ (-θ)) ^ ((1 : ℝ) / 2)
        = Real.sqrt 2 * (N : ℝ) ^ (-(θ / 2)) := by
      have hmul : (-θ) * ((1 : ℝ) / 2) = -(θ / 2) := by ring
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hR0.le _), ← Real.sqrt_eq_rpow,
        ← Real.rpow_mul hR0.le, hmul]
    have e2 : (N : ℝ) ^ (θ / 4) * (N : ℝ) ^ (-(θ / 2)) = (N : ℝ) ^ (-(θ / 4)) := by
      rw [← Real.rpow_add hR0]; congr 1; ring
    have e3 : (N : ℝ) ^ (θ / 4) * (N : ℝ) ^ (-(θ / 4)) = 1 := by
      rw [← Real.rpow_add hR0]; simp
    calc (N : ℝ) ^ (θ / 4) * (B.zScale N (znet N j))⁻¹ ^ ((1 : ℝ) / 2)
        ≤ (N : ℝ) ^ (θ / 4) * (2 * (N : ℝ) ^ (-θ)) ^ ((1 : ℝ) / 2) := by
          have hnn : (0 : ℝ) ≤ (B.zScale N (znet N j))⁻¹ := inv_nonneg.2 hzpos.le
          have := Real.rpow_le_rpow hnn hinv (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
          have hpn : (0 : ℝ) ≤ (N : ℝ) ^ (θ / 4) := Real.rpow_nonneg hR0.le _
          exact mul_le_mul_of_nonneg_left this hpn
      _ = Real.sqrt 2 * ((N : ℝ) ^ (θ / 4) * (N : ℝ) ^ (-(θ / 2))) := by rw [e1]; ring
      _ = Real.sqrt 2 * (N : ℝ) ^ (-(θ / 4)) := by rw [e2]
      _ ≤ (N : ℝ) ^ (θ / 4) * (N : ℝ) ^ (-(θ / 4)) := by
          have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-(θ / 4)) := Real.rpow_nonneg hR0.le _
          exact mul_le_mul_of_nonneg_right hs2 hnn
      _ = 1 := e3
  -- `|G_xx| ≤ 2` at the net point
  have hGxx : ‖green (T.Hband N ω) (znet N j) p.2 p.2‖ ≤ 2 := by
    have hm : ‖msc (znet N j)‖ < 1 := norm_msc_lt_one (by rw [hzim]; exact hη0 N)
    have hle : ‖green (T.Hband N ω) (znet N j) p.2 p.2 - msc (znet N j)‖ ≤ 1 :=
      le_trans hentry hsmall
    have hsub := norm_sub_norm_le (green (T.Hband N ω) (znet N j) p.2 p.2) (msc (znet N j))
    linarith
  rw [hzeq] at hGxx
  have hpsi := sq_norm_eigenvector_le_of_norm_green_le_near (T.hermitian N ω) (hη0 N) p.1 p.2
    (bulkNet κ N j) hj hGxx
  -- the final arithmetic
  have hηeq : η N = (N : ℝ) ^ (-1 + θ) := hηN N hN1
  have hdiv : (1 : ℝ) / (netDen N : ℝ) / η N ≤ (N : ℝ) ^ (-1 + θ) := by
    rw [hηeq]; exact netDen_inv_div_rpow_le hθ0.le hN1
  have hb : (N : ℝ) ^ (-1 + θ) * 3 ≤ (N : ℝ) ^ (-1 + τ) := by
    have e : (N : ℝ) ^ (-1 + θ) = (N : ℝ) ^ (-1 + τ) * (N : ℝ) ^ (θ - τ) := by
      rw [← Real.rpow_add hR0]; congr 1; ring
    have h1 : (N : ℝ) ^ (θ - τ) ≤ (N : ℝ) ^ (-(τ / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
    have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-(τ / 2)) := Real.rpow_nonneg hR0.le _
    have e2 : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (-(τ / 2)) = 1 := by
      rw [← Real.rpow_add hR0]; simp
    have h2 : 3 * (N : ℝ) ^ (-(τ / 2)) ≤ 1 := by nlinarith [h3, e2, hnn]
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hR0 _
    nlinarith [e, h1, h2, hpos, Real.rpow_nonneg hR0.le (θ - τ)]
  have hη2 : η N * 2 = (N : ℝ) ^ (-1 + θ) * 2 := by rw [hηeq]
  have hpos1 : (0 : ℝ) < (N : ℝ) ^ (-1 + θ) := Real.rpow_pos_of_pos hR0 _
  linarith [hp, hpsi, hdiv, hb, hη2.le, hη2.ge]


/-- **Theorem 2.2 from the paper-literal, (2.71)-free Theorem 2.21** (`RBM.Thm221NoELN`),
along `RBM.Thm221NoELN.toThm221NoELN'`. -/
theorem delocalization_of_Thm221N (T : Transfer X) {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELN X κ)
    {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      B.P {ω | ∃ p : B.Idx N × B.Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖(T.hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            ((T.hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  delocalization_of_Thm221N' T hκ (hT.toThm221NoELN' hκ) hτ hD

/-! ### Satisfiability probes for Theorem 2.2 -/

/-- **The two competing demands on the mesh are met by one and the same net.**  Finer and finer
would break the union bound, coarser and coarser would break the Lipschitz step; the net
`RBM.bulkNet κ N` of `4 (N+1)^4 + 1` points satisfies both at once, together with the
comparison `mesh / η ≤ η` at `η = N^{-1+θ}` that the proof actually uses. -/
example {κ θ : ℝ} (hκ0 : 0 ≤ κ) (hθ0 : 0 < θ) :
    ∀ᶠ N : ℕ in atTop,
      (∀ E : ℝ, |E| ≤ 2 - κ → ∃ j : Fin (4 * netDen N + 1),
        |E - bulkNet κ N j| ≤ 1 / (netDen N : ℝ)) ∧
      ((Fintype.card (Fin (4 * netDen N + 1)) : ℝ) ≤ (N : ℝ) ^ (5 : ℝ)) ∧
      (1 : ℝ) / (netDen N : ℝ) / (N : ℝ) ^ (-1 + θ) ≤ (N : ℝ) ^ (-1 + θ) := by
  filter_upwards [card_bulkNet_le, eventually_ge_atTop 1] with N hcard hN1
  exact ⟨fun E hE => exists_bulkNet_close hκ0 N hE, hcard, netDen_inv_div_rpow_le hθ0.le hN1⟩

/-- **The indicator of Theorem 2.2 is not identically zero, and the bound inside it can fail.**
For the `1 × 1` zero matrix every eigenvalue is `0`, which lies in the bulk `[-2+κ, 2-κ]` for
`0 < κ ≤ 2`, and the eigenvector has `|ψ_0(0)|² = 1 > N^{-1+τ}`.  So the event of Theorem 2.2 is
a genuine event: it is neither always true (which would make the theorem empty) nor always false
(which would make it unprovable), and the indicator really does switch on. -/
example {τ : ℝ} (hτ1 : τ < 1) {N : ℕ} (hN : 2 ≤ N) {κ : ℝ} (hκ2 : κ ≤ 2) :
    (N : ℝ) ^ (-1 + τ) <
      ‖(Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvectorBasis 0 0‖ ^ 2 *
        Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
          ((Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvalues 0) := by
  have hev : (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvalues 0 = 0 := by
    have h := (Matrix.IsHermitian.eigenvalues_eq_zero_iff
      (hA := Matrix.isHermitian_zero (n := Fin 1) (α := ℂ))).2 rfl
    exact congrFun h 0
  have hmem : (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvalues 0 ∈
      Set.Icc (-2 + κ) (2 - κ) := by
    rw [hev]; constructor <;> [linarith; linarith]
  have hsum := sum_sq_norm_eigenvectorBasis (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)) 0
  have hone : ‖(Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvectorBasis 0 0‖ ^ 2 = 1 := by
    simpa using hsum
  rw [hone, Set.indicator_of_mem hmem, mul_one]
  have hN2 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact Real.rpow_lt_one_of_one_lt_of_neg hN2 (by linarith)

/-! ### `rfl`-probe: Theorem 2.2's statement is unchanged (T235)

The hypothesis of `RBM.delocalization_of_Thm221N'` changed from `RBM.Thm221N'` to the
(2.71)-free `RBM.Thm221NoELN'`; the **conclusion** did not.  The first probe restates the
conclusion verbatim, the second pins the paper-literal version to the gained one. -/

example (T : Transfer X) {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoELN' X κ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      B.P {ω | ∃ p : B.Idx N × B.Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖(T.hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            ((T.hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  delocalization_of_Thm221N' T hκ hT hτ hD

example (T : Transfer X) {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoELN X κ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    delocalization_of_Thm221N T hκ hT hτ hD =
      delocalization_of_Thm221N' T hκ (hT.toThm221NoELN' hκ) hτ hD := rfl

end Deloc

end RBM

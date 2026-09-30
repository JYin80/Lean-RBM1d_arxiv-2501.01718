/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Moment
import RBM1D.Hierarchy.DriftDef
import RBM1D.Hierarchy.LKDecayQuant
import RBM1D.Gauss.DriftEnvelope

/-!
# Decay budgets of the `Q_u` blocks, and (7.13) through `Q_u ⊗ Q_u` along the flow

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5, (5.103), (7.13) and Lemma 7.3 (7.16).

The kernel estimates of (7.16) Case 2 need, besides the sum-zero premise (7.15), the **fast
decay (7.13) of the projected tensor**, which is the only premise that is a statement about the
*model* rather than about the kernel.  This file collects the deterministic pieces of that
premise.

## Where the decay comes from

* The drift tensor needs *no* stochastic input: `RBM.DriftDef.fastDecay_driftF` is a
  deterministic, pathwise theorem (§4b).
* For `E ⊗ E` of (5.22), `RBM.Decay.norm_eTens_le_of_far` needs every glued loop of (5.23) to
  carry two labels at distance `≥ ℓ`; the gluing cuts one `G` edge of each factor, and cutting
  does not lose a label (§5).
* The decay survives the projection `Q_u ⊗ Q_u` by Lemma 5.13 applied once per block (§6).

(7.13) itself holds only **with high probability**, never for every `ω`: at `ω` with `H = 0`
the resolvent is the constant `-z⁻¹`, `L - K` does not decay at the flow's radius, and a
pointwise-in-`ω` (7.13) is simply false.

## Main results

* `RBM.FastDecayFlow.qBlockErr`, `qBlockSize`, `qqErr` — the decay budget and the size after
  one `Q_u` block, and the budget (5.103) after `Q_u ⊗ Q_u` (§3).
* `RBM.FastDecayFlow.fastDecay_driftF_window` — (7.13) for the pinned drift `F_u` at the radius
  the kernel estimate reads it at (§4b).
* `RBM.FastDecayFlow.mem_rot_cons`, `mem_cutPairs_of_mem`, `mem_rflip` — the gluing of (5.23)
  keeps every label (§5).
* `RBM.FastDecayFlow.fastDecay_QQ` — (7.13) survives `Q_u ⊗ Q_u` (§6).
* `RBM.FastDecayFlow.cTwo52_div_pow_le`, `qBlockSizeBd`, `qBlockErrBd`, `qqErrBd`,
  `qBlockSize_scaled_le`, `qBlockErr_scaled_le`, `qqErr_le` — the budget (5.103) uniformly in
  `u` (§14).

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.FastDecayFlow

open Filter MeasureTheory Real
open RBM.SumZeroDyn

section Bridge

variable {Ω : Type*} {L : ℕ}

variable [NeZero L]

end Bridge

section Zero

variable (L : ℕ) [NeZero L]

end Zero

/-! ### §3  The decay budgets

The error `δ` in each decay statement below is the paper's `O(W^{-D})` made explicit.  Each is of
the shape "input error + (polynomial in the size) · `e^{-c₀K}`": the budget of Lemma 5.13 (5.87)
for `Q_u`, and of (5.99)/(5.100) for the commutator and the `ϑ̇` term.  They are named so that
the statements below stay readable; `ℓr` is `ℓ_u`. -/

section Budgets

/-- One `Q_u` block on one half of a doubled tensor: the error of (5.87) again, in the form
`RBM.SumZeroDyn.fastDecay_Q1` / `fastDecay_Q2` produce it. -/
noncomputable def qBlockErr (L k : ℕ) (ℓr R e δ : ℝ) : ℝ :=
  δ + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * (cTwo52 / ℓr) ^ k
      * exp (-(cZero * R / ℓr)) + (L : ℝ) ^ k * δ * (cTwo52 / ℓr) ^ k

/-- The size after one `Q_u` block (`RBM.SumZeroDyn.norm_Q1_le` / `norm_Q2_le`). -/
noncomputable def qBlockSize (L k : ℕ) (ℓr R e δ : ℝ) : ℝ :=
  e + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * (cTwo52 / ℓr) ^ k

/-- **(5.103)**: the decay budget after `Q_u ⊗ Q_u`, i.e. two nested blocks. -/
noncomputable def qqErr (L k : ℕ) (ℓr K e δ : ℝ) : ℝ :=
  qBlockErr L k ℓr (2 * (ℓr * K)) (qBlockSize L k ℓr (ℓr * K) e δ)
    (qBlockErr L k ℓr (ℓr * K) e δ)

theorem qBlockErr_nonneg (L k : ℕ) {ℓr R e δ : ℝ} (hℓ : 0 < ℓr) (hR : 0 ≤ R) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) : 0 ≤ qBlockErr L k ℓr R e δ := by
  have := cTwo52_pos
  unfold qBlockErr
  positivity

theorem qBlockSize_nonneg (L k : ℕ) {ℓr R e δ : ℝ} (hℓ : 0 < ℓr) (hR : 0 ≤ R) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) : 0 ≤ qBlockSize L k ℓr R e δ := by
  have := cTwo52_pos
  unfold qBlockSize
  positivity

theorem qqErr_nonneg (L k : ℕ) {ℓr K e δ : ℝ} (hℓ : 0 < ℓr) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) : 0 ≤ qqErr L k ℓr K e δ :=
  qBlockErr_nonneg L k hℓ (by positivity)
    (qBlockSize_nonneg L k hℓ (by positivity) he hδ) (qBlockErr_nonneg L k hℓ (by positivity) he hδ)

end Budgets

section HGd

variable {Ω : Type*}

end HGd

/-! ### §4b  The decay of the unprojected tensors along the flow

The kernel estimates ask for (7.13) of the tensor `A` itself.  For the initial datum and for
the commutator/`ϑ̇` terms `A` is `L - K`, whose decay is (5.75), delivered through (2.76).  For
the drift `A = F_u` is the pinned `RBM.DriftDef.driftF`, whose decay is a *deterministic*
theorem. -/

section Underlying

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **(7.13) for the pinned drift `F_u`**, at the radius the kernel estimate reads it at.

`RBM.DriftDef.fastDecay_driftF` is deterministic and pathwise: Lemma 5.9's decay of `K`, of
`L` and of `L - K`, with their sup bounds, is its whole input, and no `ω` is quantified over.
It produces the radius `2ℓ + 1`; at `ℓ = ℓ_u K` that is below `ℓ_u (4K)` because `ℓ_u ≥ 1/2`
and `K ≥ 1`. -/
theorem fastDecay_driftF_window (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (hL : 3 ≤ B.L N)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (Mx : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) {K δ MK MD δF : ℝ} (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (gloop (B.L N) (B.W N) Mx (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (gloop (B.L N) (B.W N) Mx (zt E u)))
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 → ‖B.Kval E N u J‖ ≤ MK)
    (hDb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 →
      ‖(gloop (B.L N) (B.W N) Mx (zt E u) - B.Kval E N u) J‖ ≤ MD)
    (hδF : (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * (MD * δ))
        + (n : ℝ) * (2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * (MK + MD))
        + 2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * MD ≤ δF) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K)) δF
      (DriftDef.driftF B E N u Mx σ) := by
  have hℓ := half_le_ellHat_real (B.L N) hL hu0 hu1
  have hℓ0 : (0 : ℝ) ≤ ellHat (B.L N) ((u : ℝ) : ℂ) := by linarith
  have hrad : 2 * (ellHat (B.L N) ((u : ℝ) : ℂ) * K) + 1
      ≤ ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K) := by nlinarith
  refine SumZeroDyn.FastDecay.mono (B.L N)
    (DriftDef.fastDecay_driftF B E N u Mx σ (by positivity) hδ hMK hMD hKd hDd hLd hKb hDb
      hδF) hrad le_rfl

end Underlying

/-! ### §5  (7.13) for `E ⊗ E`

The fifth tensor is the only one whose decay is not already packaged somewhere in the
repository.  `RBM.Decay.norm_eTens_le_of_far` bounds (5.22) by `W n L δ` **provided every
glued loop `J k b b'` of (5.23) carries two labels at distance `≥ ℓ`**, and that hypothesis is
what has to be checked: the gluing cuts one `G` edge of each factor, so one has to know that
cutting does not lose a label.

It does not.  `RBM.EEBridge.cutPairs` is `RBM.EEBridge.pairs` *rotated* to begin at the cut
edge — the cut edge's own pair is put back as the head — and `RBM.EEBridge.rflip` reverses a
chain, keeping every label and adding the closing one.  So the glued `(2m+2)`-loop contains
every label of `a` and of `a'`, and a far pair among the `2m` arguments of the doubled tensor
survives it. -/

section EEDecay

open EEBridge

variable {L : ℕ}

/-- Rotating a list to begin at its `k`-th entry keeps every element. -/
theorem mem_rot_cons {α : Type*} (l : List α) {k : ℕ} (hk : k < l.length) {x : α} (hx : x ∈ l) :
    x ∈ l[k] :: (l.drop (k + 1) ++ l.take k) := by
  have hx' : x ∈ l.take k ++ l.drop k := by rw [List.take_append_drop]; exact hx
  rcases List.mem_append.1 hx' with h | h
  · exact List.mem_cons_of_mem _ (List.mem_append.2 (Or.inr h))
  · rw [List.drop_eq_getElem_cons hk] at h
    rcases List.mem_cons.1 h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl h))

/-- **Cutting a `G` edge keeps every label.**  `RBM.EEBridge.cutPairs` puts the cut pair back
as the head, so it is `RBM.EEBridge.pairs` rotated; this is what makes the decay of the
`G`-loops survive the gluing of (5.23). -/
theorem mem_cutPairs_of_mem {I : LoopIdx (ZMod L)} (hI : I.WF) {k : ℕ} (hk : k < I.length)
    {x : ZMod L} (hx : x ∈ I.a) : x ∈ (cutPairs I k).map Prod.snd := by
  have hlen : I.σ.length = I.a.length := hI
  have hps : (pairs I).map Prod.snd = I.a := List.map_snd_zip (le_of_eq hlen.symm)
  have hpl : (pairs I).length = I.length := pairs_length hI
  have hk' : k < (pairs I).length := by rw [hpl]; exact hk
  rw [← hps] at hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hx
  have hpa : pairAt I k = (pairs I)[k] := List.getD_eq_getElem _ _ hk'
  rw [cutPairs, hpa]
  exact List.mem_map.2 ⟨p, mem_rot_cons (pairs I) hk' hp, hpx⟩

/-- **Reversing and flipping a chain keeps its labels**, and adds the closing label `c`. -/
theorem mem_rflip {t : Bool} : ∀ (l : List (Bool × ZMod L)) (c : ZMod L) {x : ZMod L},
    (x ∈ l.map Prod.snd ∨ x = c) → x ∈ (rflip t l c).map Prod.snd := by
  intro l
  induction l with
  | nil =>
      intro c x hx
      rcases hx with hx | hx
      · simp at hx
      · simp [hx]
  | cons p l ih =>
      intro c x hx
      rw [rflip_cons, List.map_append]
      rcases hx with hx | hx
      · refine List.mem_append.2 (Or.inl (ih p.2 ?_))
        rcases List.mem_cons.1 (by simpa using hx : x ∈ p.2 :: l.map Prod.snd) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact List.mem_append.2 (Or.inr (by simp [hx]))

variable {d : Gauss.Dims} {N : ℕ} {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}

end EEDecay

/-! ### §6  (7.13) for term 5: `(Q_u ⊗ Q_u) ∘ (E ⊗ E)_u`

(5.103) with the two blocks projected.  The decay survives both projections by Lemma 5.13
applied once per block (`RBM.SumZeroDyn.fastDecay_Q2`, then `fastDecay_Q1`), each doubling the
radius — so the common radius `ℓ_u (4K)` is exactly what two blocks produce. -/

section QQDecay

variable {Ω : Type*}

/-- **(7.13) survives `Q_u ⊗ Q_u`.** -/
theorem fastDecay_QQ (L : ℕ) [NeZero L] (hL : 3 ≤ L) {k : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) {K e δ : ℝ} (hK : 1 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    {Bc : LoopArg L ((k + 1) + (k + 1)) → ℂ} (hBe : ∀ c, ‖Bc c‖ ≤ e)
    (hB : FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ Bc) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * (4 * K))
      (qqErr L k (ellHat L ((u : ℝ) : ℂ)) K e δ) (QQ L ((u : ℝ) : ℂ) Bc) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by linarith
  have hR : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) * K := by nlinarith
  have h2max : ∀ c, ‖Q2 L ((u : ℝ) : ℂ) Bc c‖
      ≤ qBlockSize L k (ellHat L ((u : ℝ) : ℂ)) (ellHat L ((u : ℝ) : ℂ) * K) e δ :=
    norm_Q2_le L hL hu0 hu1 hR he hδ hBe hB
  have h2dec : FastDecay L (2 * (ellHat L ((u : ℝ) : ℂ) * K))
      (qBlockErr L k (ellHat L ((u : ℝ) : ℂ)) (ellHat L ((u : ℝ) : ℂ) * K) e δ)
      (Q2 L ((u : ℝ) : ℂ) Bc) :=
    fastDecay_Q2 L hL hu0 hu1 hR he hδ hBe hB
  have h3dec := fastDecay_Q1 L hL hu0 hu1
    (by linarith : (0 : ℝ) < 2 * (ellHat L ((u : ℝ) : ℂ) * K))
    (qBlockSize_nonneg L k hℓ0 hR.le he hδ) (qBlockErr_nonneg L k hℓ0 hR.le he hδ) h2max h2dec
  rw [QQ_eq]
  exact SumZeroDyn.FastDecay.mono L h3dec (le_of_eq (by ring)) le_rfl

end QQDecay

/-! ### §7  `E ⊗ E` along the flow

`RBM.MomentDuhamel.eeFun` is `RBM.EEBridge.eeArg` by definition, so §5 applies to it verbatim
at the flow's (Hermitian) matrix. -/

section EEFlow

variable {Ω : Type*} [MeasurableSpace Ω]

end EEFlow

section GoodEvents

variable {Ω : Type*} [MeasurableSpace Ω]

variable {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end GoodEvents

section FiveTensors

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end FiveTensors

section Discharged

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end Discharged

section Witness

variable {Ω : Type*}

end Witness

section EndToEnd

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end EndToEnd

/-! ### §14  The budget of (5.103), uniformly in `u`

The budget `qqErr` of §3 is dominated, uniformly for `u` in a closed window, by a `u`-free
quantity.  No model, no sample point, no event and no probability enter; this is elementary
calculus on the window.

**No compactness is needed.**  The `u`-dependence is entirely through `ℓ̂_u = ellHat L u`,
which enters in exactly two ways:

* as `(c₂/ℓ̂_u)^{n+1}`, bounded by `c₂^{n+1}` because `ℓ̂_u ≥ 1`
  (`RBM.FastDecayFlow.cTwo52_div_pow_le`);
* inside the exponentials, always in the combination `c₀·(ℓ̂_u·K)/ℓ̂_u`, i.e. **`ℓ̂_u` cancels**.

`qqErr` also carries the radius `ℓ̂_u K` *outside* an exponential, in the factor `(2e(R+1))^k`
of `RBM.FastDecayFlow.qBlockSize`.  There `ℓ̂_u ≤ L` is used instead, which is why `qqErrBd` is
stated at radius `L·K` rather than at `ℓ̂_u·K`.

**The dominant really depends on `N`.**  `qqErrBd` carries `L^k` and `(2e(L·K+1))^k`, so no
constant dominates it once `L N → ∞`.  Besides the exponentially small part, the two
`δ`-terms of `qBlockErr` carry no exponential. -/

section ErrBudget

open Real

/-- `(c₂/ℓ)^k ≤ c₂^k` for `ℓ ≥ 1`: the only way `ℓ̂_u` enters the budgets outside an
exponential, apart from the radius of `qqErr`. -/
theorem cTwo52_div_pow_le (k : ℕ) {ℓr : ℝ} (h : 1 ≤ ℓr) :
    (cTwo52 / ℓr) ^ k ≤ cTwo52 ^ k := by
  have h0 : (0 : ℝ) < ℓr := by linarith
  have := cTwo52_pos
  gcongr
  exact div_le_self cTwo52_pos.le h

/-- The `ℓ`-free dominant of `RBM.FastDecayFlow.qBlockSize`, read at radius `R`. -/
noncomputable def qBlockSizeBd (L k : ℕ) (R e δ : ℝ) : ℝ :=
  e + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * cTwo52 ^ k

/-- The `ℓ`-free dominant of `RBM.FastDecayFlow.qBlockErr`, read at radius `R` with the
exponential already evaluated at `R/ℓ = c`. -/
noncomputable def qBlockErrBd (L k : ℕ) (R c e δ : ℝ) : ℝ :=
  δ + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * cTwo52 ^ k * exp (-(cZero * c))
    + (L : ℝ) ^ k * δ * cTwo52 ^ k

/-- The `u`-free dominant of `RBM.FastDecayFlow.qqErr`: the two nested blocks of (5.103),
each read at the widened radius `L·K` and at the *unwidened* exponent `K`. -/
noncomputable def qqErrBd (L k : ℕ) (K e δ : ℝ) : ℝ :=
  qBlockErrBd L k (2 * ((L : ℝ) * K)) (2 * K)
    (qBlockSizeBd L k ((L : ℝ) * K) e δ) (qBlockErrBd L k ((L : ℝ) * K) K e δ)

theorem qBlockSizeBd_nonneg (L k : ℕ) {R e δ : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    0 ≤ qBlockSizeBd L k R e δ := by
  have := cTwo52_pos
  unfold qBlockSizeBd
  positivity

theorem qBlockErrBd_nonneg (L k : ℕ) {R c e δ : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    0 ≤ qBlockErrBd L k R c e δ := by
  have := cTwo52_pos
  unfold qBlockErrBd
  positivity

theorem qqErrBd_nonneg (L k : ℕ) {K e δ : ℝ} (hK : 0 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    0 ≤ qqErrBd L k K e δ :=
  qBlockErrBd_nonneg L k (by positivity)
    (qBlockSizeBd_nonneg L k (by positivity) he hδ)
    (qBlockErrBd_nonneg L k (by positivity) he hδ)

/-- One `Q_u` block's size, at the radius `c·(ℓ K)` in which (5.103) reads it, dominated
free of `ℓ`. -/
theorem qBlockSize_scaled_le (L k : ℕ) {ℓr c K e δ : ℝ} (h1l : 1 ≤ ℓr) (hlL : ℓr ≤ (L : ℝ))
    (hc : 0 ≤ c) (hK : 0 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    qBlockSize L k ℓr (c * (ℓr * K)) e δ ≤ qBlockSizeBd L k (c * ((L : ℝ) * K)) e δ := by
  have hC := cTwo52_pos
  have hl0 : (0 : ℝ) < ℓr := by linarith
  have hP : (cTwo52 / ℓr) ^ k ≤ cTwo52 ^ k := cTwo52_div_pow_le _ h1l
  unfold qBlockSize qBlockSizeBd
  gcongr

/-- One `Q_u` block's error, at the radius `c·(ℓ K)`.  The exponential `exp(-c₀ R/ℓ)` is
where `ℓ` cancels exactly; the polynomial prefactor is where `ℓ ≤ L` is spent. -/
theorem qBlockErr_scaled_le (L k : ℕ) {ℓr c K e δ e' δ' : ℝ} (h1l : 1 ≤ ℓr)
    (hlL : ℓr ≤ (L : ℝ)) (hc : 0 ≤ c) (hK : 0 ≤ K) (he : 0 ≤ e) (hee : e ≤ e')
    (hδ : 0 ≤ δ) (hδδ : δ ≤ δ') :
    qBlockErr L k ℓr (c * (ℓr * K)) e δ
      ≤ qBlockErrBd L k (c * ((L : ℝ) * K)) (c * K) e' δ' := by
  have hC := cTwo52_pos
  have hl0 : (0 : ℝ) < ℓr := by linarith
  have he'0 : 0 ≤ e' := he.trans hee
  have hδ'0 : 0 ≤ δ' := hδ.trans hδδ
  have hP : (cTwo52 / ℓr) ^ k ≤ cTwo52 ^ k := cTwo52_div_pow_le _ h1l
  have he5 : cZero * (c * (ℓr * K)) / ℓr = cZero * (c * K) := by field_simp
  unfold qBlockErr qBlockErrBd
  rw [he5]
  gcongr

/-- **(5.103) uniformly in `u`.** -/
theorem qqErr_le (L k : ℕ) {ℓr K e δ : ℝ} (h1l : 1 ≤ ℓr) (hlL : ℓr ≤ (L : ℝ))
    (hK : 0 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    qqErr L k ℓr K e δ ≤ qqErrBd L k K e δ := by
  have hl0 : (0 : ℝ) < ℓr := by linarith
  unfold qqErr qqErrBd
  have h1 : qBlockErr L k ℓr (1 * (ℓr * K)) e δ
      ≤ qBlockErrBd L k (1 * ((L : ℝ) * K)) (1 * K) e δ :=
    qBlockErr_scaled_le L k h1l hlL zero_le_one hK he le_rfl hδ le_rfl
  have h2 : qBlockSize L k ℓr (1 * (ℓr * K)) e δ
      ≤ qBlockSizeBd L k (1 * ((L : ℝ) * K)) e δ :=
    qBlockSize_scaled_le L k h1l hlL zero_le_one hK he hδ
  simp only [one_mul] at h1 h2
  exact qBlockErr_scaled_le (c := 2) L k h1l hlL zero_le_two hK
    (qBlockSize_nonneg L k hl0 (by positivity) he hδ) h2
    (qBlockErr_nonneg L k hl0 (by positivity) he hδ) h1

end ErrBudget

/-! ## Deviations from the paper

**The uniform error budget of §14 is not in the paper.**

* **Paper location.**  §7, the premise (7.13)/(7.16) of Lemma 7.3, sitting on the budgets of
  Lemma 5.13 (5.87), (5.99), (5.100) and (5.103).  The paper writes each of those
  budgets as `O(W^{-D})` and never names a common dominant; §14 supplies one for the budget
  (5.103), uniformly in the time.
* §14 proves a consequence of the paper's own formulas; no statement of the paper is
  weakened, strengthened or re-read.
-/

end RBM.FastDecayFlow

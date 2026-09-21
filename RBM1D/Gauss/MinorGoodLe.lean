/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MinorDiffGain

/-!
# The level-budgeted minor good event: `RBM.Gauss.MinorGoodLe`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4.

## Why this file exists

`RBM.Gauss.MinorGood` and `RBM.Gauss.MinorGood'` (`RBM1D/Gauss/MinorDiffGain.lean`) quantify
over **all** minor levels `S : Finset (d.Idx N)` with **one** threshold `Ψ`.  Taken literally
that is not merely hard to produce, it is false: iterating (4.9) degrades the threshold at
every level, and after `|S| ≍ Ψ⁻¹` levels nothing is left.  (It is false for a second, cruder
reason as well — see the audit of T164 in `docs/STATUS.md`: at the sample point `ω = 0` and
`E = 0` one has `‖G^{(S)}_{aa} - m‖ = u/(1-u)` for every `N`, so `MinorGood'` fails outright
once `u > 1/3`.  That second defect is *not* repaired here; it is repaired by conditioning on
the good event, which is T171.)

What the `2p`-th moment expansion actually needs is only the levels it actually reaches, and
those are bounded by the word length: `|S| ≤ 2p`.  So this file introduces a **budget** `M` and
states the four estimates only for `S.card ≤ M`.

## The logical shape

`RBM.Gauss.minorGoodLe_of_goodEvent` is a **pointwise implication**, not a hypothesis: at one
fixed sample point `ω`, *if* the full-matrix good event (4.1) holds at `ω` with threshold `Ψ`,
*then* the level-budgeted estimates hold at the same `ω` with threshold `2Ψ`.  Nothing is
assumed for all `ω`.  The produced event is therefore exactly as likely as (4.1), which is
`RBM.Gauss.highProb_goodSetFlow_of_localLaw`.

## What is proved

* `RBM.Gauss.isUnit_det_Hflow_submatrix_sub` — **invertibility of every minor is free**: it is
  `RBM.isUnit_det_sub_smul_one` applied to the (Hermitian) submatrix of `H_u`, and needs
  neither a good event nor a level restriction.  In `RBM.Gauss.MinorGood` it is a field, and
  in `RBM.Gauss.minorGood_of_half_le` an assumption `hdet`; here it is discharged.
* `RBM.Gauss.gEnt_insert_of_ne` — (4.9) at a general level, with the two hypotheses it really
  needs (`hdet` at level `S`, and `G^{(S)}_{κκ} ≠ 0`) rather than the whole of
  `RBM.Gauss.MinorGood`.  This is what makes the induction below possible: at the inductive
  step the good event is available at level `S` only, not at all levels.
* `RBM.Gauss.MinorGoodLe` and `RBM.Gauss.minorGoodLe_of_goodEvent`.

## The induction, and the constants it needs

Level `0` is exactly (4.1): `RBM.GoodEvent.norm_offdiag_le` and
`RBM.GoodEvent.norm_diag_sub_le` are verbatim `off_le` and `diag_sub_le` at `S = ∅`, via
`RBM.Gauss.greenSetMat_empty_apply`.  One level of (4.9),

  `G^{(S ∪ {κ})}_{ab} = G^{(S)}_{ab} - G^{(S)}_{aκ} G^{(S)}_{κb} (G^{(S)}_{κκ})⁻¹`,

costs `2 Ψ_j²` on both the off-diagonal and the centered diagonal entries (the `2` is the bound
on `|G^{(S)}_{κκ}|⁻¹`, which travels with the induction and is *not* separable from it — the
step mentions the inverse diagonal entry).  So the recursion is

  `Ψ_{j+1} ≤ Ψ_j + 2 Ψ_j²`.

The invariant that closes it is `RBM.Gauss.norm_gEnt_le_of_goodEvent`:

  `Ψ_j ≤ Ψ + 8 j Ψ²` for `j ≤ M`,

which needs exactly `8 M Ψ ≤ 1` (then `8 j Ψ² ≤ Ψ`, hence `Ψ_j ≤ 2Ψ`, hence the step costs
`2 Ψ_j² ≤ 8 Ψ²`, which is precisely the increment of the invariant).  The separate hypothesis
`Ψ ≤ 1/4` is used only for `inv_le`: it gives `1 - 2Ψ ≥ 1/2 ≤ |G^{(S)}_{aa}|` from `|m| = 1`
(`RBM.norm_mE`).

## Deviation from the paper

The paper states (4.2)/(4.3) at level `0` and the one-step identity (4.9); it never states a
bound on `G^{(S)}` for `|S| ≥ 2`.  The iteration to `|S| ≤ M`, the budget `M`, and the
constants `Ψ ≤ 1/4`, `8 M Ψ ≤ 1`, `Ψ ↦ 2Ψ` are Lean's construction.  Recorded in
`docs/paper-deltas.md`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix Finset

variable {d : Dims} {N : ℕ} {u : ℝ} {z m : ℂ} {ω : Ω d} {Ψ : ℝ} {M : ℕ}
variable {a b κ : d.Idx N} {S : Finset (d.Idx N)}

/-! ### Invertibility of the minors is unconditional -/

/-- **Every minor of `H_u - z` is invertible**, for every sample point and every level, as soon
as `z` is off the real axis.  `RBM.Gauss.MinorGood` carries this as a field and
`RBM.Gauss.minorGood_of_half_le` as an assumption; neither is necessary. -/
theorem isUnit_det_Hflow_submatrix_sub (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) (hz : z.im ≠ 0)
    (S : Finset (d.Idx N)) :
    IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det :=
  isUnit_det_sub_smul_one ((Hflow_isHermitian d N u ω).submatrix Subtype.val) hz

/-! ### (4.9) with the hypotheses it actually needs -/

/-- **(4.9) for the extended entries**, assuming only what one level of the identity uses: the
`S`-minor is invertible and its `κκ` entry does not vanish.  `RBM.Gauss.gEnt_insert` is the
same identity packaged behind `RBM.Gauss.MinorGood`, which asserts both at *every* level; the
induction of `RBM.Gauss.norm_gEnt_le_of_goodEvent` has them at level `S` only. -/
theorem gEnt_insert_of_ne
    (hdet : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det)
    (hκ : κ ∉ S) (hne : gEnt d N u z ω κ κ S ≠ 0)
    (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt d N u z ω a b (insert κ S)
      = gEnt d N u z ω a b S - gEnt d N u z ω a κ S * gEnt d N u z ω κ b S
          * (gEnt d N u z ω κ κ S)⁻¹ := by
  have ha' : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
  have hb' : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
  have hne' : greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0 := by
    rwa [gEnt_apply hκ hκ] at hne
  rw [gEnt_apply ha hb, gEnt_apply ha' hb', gEnt_apply ha' hκ, gEnt_apply hκ hb',
    gEnt_apply hκ hκ,
    greenSetMat_insert_apply d N u z S ω hκ hdet hne' ha hb, div_eq_mul_inv, mul_assoc]

/-! ### Level `0` is the full-matrix good event -/

/-- At `S = ∅` the extended entry is the full resolvent entry. -/
theorem gEnt_empty (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d) (a b : d.Idx N) :
    gEnt d N u z ω a b ∅ = green (Hflow d N u ω) z a b := by
  rw [gEnt_apply (Finset.notMem_empty a) (Finset.notMem_empty b),
    greenSetMat_empty_apply d N u z ω ⟨a, Finset.notMem_empty a⟩ ⟨b, Finset.notMem_empty b⟩]

/-! ### The simultaneous induction on the level -/

/-- **The recursion `Ψ_{j+1} ≤ Ψ_j + 2 Ψ_j²`, solved**: at every level `S` with
`S.card ≤ M`, the off-diagonal entries and the centered diagonal entries of `G^{(S)}` are at
most `Ψ + 8 |S| Ψ²`.

The two estimates cannot be separated, because the step of (4.9) multiplies by
`(G^{(S)}_{κκ})⁻¹`, whose bound comes from the diagonal estimate at level `S`, while the
diagonal estimate at level `S ∪ {κ}` needs the off-diagonal estimate at level `S`. -/
theorem norm_gEnt_le_of_goodEvent (hz : z.im ≠ 0) (hm : ‖m‖ = 1)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Hflow d N u ω) z) m Ψ) :
    ∀ S : Finset (d.Idx N), S.card ≤ M →
      (∀ a b : d.Idx N, a ≠ b → ‖gEnt d N u z ω a b S‖ ≤ Ψ + 8 * (S.card : ℝ) * Ψ ^ 2) ∧
      (∀ a : d.Idx N, a ∉ S → ‖gEnt d N u z ω a a S - m‖ ≤ Ψ + 8 * (S.card : ℝ) * Ψ ^ 2) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨fun a b hab => ?_, fun a _ => ?_⟩
      · rw [gEnt_empty]
        simpa using hG.norm_offdiag_le hab
      · rw [gEnt_empty]
        simpa using hG.norm_diag_sub_le a
  | insert κ s hκs ih =>
      intro hcard
      have hscard : s.card ≤ M := by
        rw [Finset.card_insert_of_notMem hκs] at hcard; omega
      obtain ⟨ihoff, ihdiag⟩ := ih hscard
      -- the bound at level `s`
      set B : ℝ := Ψ + 8 * (s.card : ℝ) * Ψ ^ 2 with hB
      have hjM : (s.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hscard
      have h8j : 8 * (s.card : ℝ) * Ψ ≤ 1 := by nlinarith
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      have hB2 : B ≤ 2 * Ψ := by rw [hB]; nlinarith
      -- `|G^{(s)}_{aa}| ≥ 1/2`, hence the bound `2` on the inverse
      have hhalf : ∀ x : d.Idx N, x ∉ s → 1 / 2 ≤ ‖gEnt d N u z ω x x s‖ := by
        intro x hx
        have h1 := ihdiag x hx
        have h2 : ‖m‖ - ‖gEnt d N u z ω x x s‖ ≤ ‖m - gEnt d N u z ω x x s‖ :=
          norm_sub_norm_le _ _
        rw [norm_sub_rev, hm] at h2
        linarith
      have hκ0 : gEnt d N u z ω κ κ s ≠ 0 := by
        intro h0
        have := hhalf κ hκs
        rw [h0, norm_zero] at this
        norm_num at this
      have hinv : ‖(gEnt d N u z ω κ κ s)⁻¹‖ ≤ 2 := by
        have h := hhalf κ hκs
        rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      -- the arithmetic of one step: `B + 2 B² ≤ Ψ + 8 (|s| + 1) Ψ²`
      have hstep : B + B * B * 2 ≤ Ψ + 8 * ((s.card : ℝ) + 1) * Ψ ^ 2 := by
        rw [hB]; nlinarith [hB0, hB2]
      have hcast : ((insert κ s).card : ℝ) = (s.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hκs]; push_cast; ring
      rw [hcast]
      refine ⟨fun a b hab => ?_, fun a ha => ?_⟩
      · by_cases ha : a ∈ insert κ s
        · rw [gEnt_eq_zero_left ha, norm_zero]
          nlinarith
        by_cases hb : b ∈ insert κ s
        · rw [gEnt_eq_zero_right hb, norm_zero]
          nlinarith
        have haκ : a ≠ κ := fun h => ha (by rw [h]; exact Finset.mem_insert_self κ s)
        have hbκ : b ≠ κ := fun h => hb (by rw [h]; exact Finset.mem_insert_self κ s)
        rw [gEnt_insert_of_ne (isUnit_det_Hflow_submatrix_sub d N u ω hz s) hκs hκ0 ha hb]
        refine le_trans (norm_sub_le _ _) (le_trans ?_ hstep)
        gcongr ?_ + ?_
        · exact ihoff a b hab
        · rw [norm_mul, norm_mul]
          have h1 := ihoff a κ haκ
          have h2 := ihoff κ b (Ne.symm hbκ)
          have n2 := norm_nonneg (gEnt d N u z ω κ b s)
          have n3 := norm_nonneg ((gEnt d N u z ω κ κ s)⁻¹)
          exact mul_le_mul (mul_le_mul h1 h2 n2 hB0) hinv n3 (by positivity)
      · have haκ : a ≠ κ := fun h => ha (by rw [h]; exact Finset.mem_insert_self κ s)
        have ha' : a ∉ s := fun h => ha (Finset.mem_insert_of_mem h)
        rw [gEnt_insert_of_ne (isUnit_det_Hflow_submatrix_sub d N u ω hz s) hκs hκ0 ha ha]
        have hre : gEnt d N u z ω a a s
              - gEnt d N u z ω a κ s * gEnt d N u z ω κ a s * (gEnt d N u z ω κ κ s)⁻¹ - m
            = (gEnt d N u z ω a a s - m)
              - gEnt d N u z ω a κ s * gEnt d N u z ω κ a s * (gEnt d N u z ω κ κ s)⁻¹ := by
          ring
        rw [hre]
        refine le_trans (norm_sub_le _ _) (le_trans ?_ hstep)
        gcongr ?_ + ?_
        · exact ihdiag a ha'
        · rw [norm_mul, norm_mul]
          have h1 := ihoff a κ haκ
          have h2 := ihoff κ a (Ne.symm haκ)
          have n2 := norm_nonneg (gEnt d N u z ω κ a s)
          have n3 := norm_nonneg ((gEnt d N u z ω κ κ s)⁻¹)
          exact mul_le_mul (mul_le_mul h1 h2 n2 hB0) hinv n3 (by positivity)

/-! ### The level-budgeted good event -/

/-- **The local law on the good event, at every minor level of size at most `M`.**

This is `RBM.Gauss.MinorGood'` with the level quantifier budgeted by `M`.  The budget is what
makes it *producible*: `RBM.Gauss.minorGoodLe_of_goodEvent` derives it, at one fixed sample
point, from the full-matrix good event (4.1) alone.

`det` needs neither the budget nor the good event
(`RBM.Gauss.isUnit_det_Hflow_submatrix_sub`), so it is stated at every level. -/
structure MinorGoodLe (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (ω : Ω d) (Ψ : ℝ) (M : ℕ)
    : Prop where
  /-- Every minor of `H_u - z` is invertible -- unconditional, and at *every* level. -/
  det : ∀ S : Finset (d.Idx N), IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det
  /-- The diagonal entries of the budgeted minors are non-zero. -/
  diag_ne : ∀ S : Finset (d.Idx N), S.card ≤ M → ∀ a : d.Idx N, a ∉ S →
    gEnt d N u z ω a a S ≠ 0
  /-- `|G^{(S)}_{aa}|⁻¹ ≤ 2` for `|S| ≤ M` -- the quantitative form of (4.1). -/
  inv_le : ∀ S : Finset (d.Idx N), S.card ≤ M → ∀ a : d.Idx N,
    ‖(gEnt d N u z ω a a S)⁻¹‖ ≤ 2
  /-- `|G^{(S)}_{ab}| ≤ Ψ` for `a ≠ b` and `|S| ≤ M` -- (4.2). -/
  off_le : ∀ S : Finset (d.Idx N), S.card ≤ M → ∀ a b : d.Idx N, a ≠ b →
    ‖gEnt d N u z ω a b S‖ ≤ Ψ
  /-- `|G^{(S)}_{aa} - m| ≤ Ψ` for `|S| ≤ M` -- (4.3). -/
  diag_sub_le : ∀ S : Finset (d.Idx N), S.card ≤ M → ∀ a : d.Idx N, a ∉ S →
    ‖gEnt d N u z ω a a S - m‖ ≤ Ψ

/-- **(4.9) inside the budget.**  The identity is available at `S ∪ {κ}` as soon as `S` itself
is within the budget; the estimate of the right-hand side then uses the fields at level `S`. -/
theorem MinorGoodLe.gEnt_insert (hg : MinorGoodLe d N u z m ω Ψ M) (hS : S.card ≤ M)
    (hκ : κ ∉ S) (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt d N u z ω a b (insert κ S)
      = gEnt d N u z ω a b S - gEnt d N u z ω a κ S * gEnt d N u z ω κ b S
          * (gEnt d N u z ω κ κ S)⁻¹ :=
  gEnt_insert_of_ne (hg.det S) hκ (hg.diag_ne S hS κ hκ) ha hb

/-- **The level-budgeted good event follows from (4.1) at the same sample point**, with the
threshold degraded from `Ψ` to `2Ψ`.

This is a pointwise implication: `ω` occurs only as the point at which the hypothesis and the
conclusion are both read.  Nothing is assumed for all `ω`. -/
theorem minorGoodLe_of_goodEvent (hz : z.im ≠ 0) (hm : ‖m‖ = 1)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Hflow d N u ω) z) m Ψ) :
    MinorGoodLe d N u z m ω (2 * Ψ) M := by
  classical
  have key := norm_gEnt_le_of_goodEvent hz hm hΨ0 hΨ4 hMΨ hG
  -- the invariant collapses to `2Ψ` inside the budget
  have hle : ∀ S : Finset (d.Idx N), S.card ≤ M →
      Ψ + 8 * (S.card : ℝ) * Ψ ^ 2 ≤ 2 * Ψ := by
    intro S hS
    have hjM : ((S.card : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hS
    nlinarith
  have hdiag : ∀ S : Finset (d.Idx N), S.card ≤ M → ∀ a : d.Idx N, a ∉ S →
      ‖gEnt d N u z ω a a S - m‖ ≤ 2 * Ψ :=
    fun S hS a ha => le_trans ((key S hS).2 a ha) (hle S hS)
  have hhalf : ∀ S : Finset (d.Idx N), S.card ≤ M → ∀ a : d.Idx N, a ∉ S →
      1 / 2 ≤ ‖gEnt d N u z ω a a S‖ := by
    intro S hS a ha
    have h1 := hdiag S hS a ha
    have h2 : ‖m‖ - ‖gEnt d N u z ω a a S‖ ≤ ‖m - gEnt d N u z ω a a S‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev, hm] at h2
    linarith
  refine
    { det := isUnit_det_Hflow_submatrix_sub d N u ω hz
      diag_ne := ?_
      inv_le := ?_
      off_le := fun S hS a b hab => le_trans ((key S hS).1 a b hab) (hle S hS)
      diag_sub_le := hdiag }
  · intro S hS a ha h0
    have := hhalf S hS a ha
    rw [h0, norm_zero] at this
    norm_num at this
  · intro S hS a
    by_cases ha : a ∉ S
    · have h := hhalf S hS a ha
      rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    · rw [gEnt_eq_zero_left (not_not.1 ha), _root_.inv_zero, norm_zero]
      norm_num

/-- **The converse at level `0`: `RBM.Gauss.MinorGoodLe` is not a vacuous statement.**  Its
level-`0` content is exactly the full-matrix good event (4.1), for *every* budget `M`
(including `M = 0`, where the two are equivalent up to the threshold).  So
`RBM.Gauss.minorGoodLe_of_goodEvent` neither assumes nor concludes something empty: it
strengthens (4.1) from one level to `M + 1` levels at the cost of a factor `2`. -/
theorem MinorGoodLe.goodEvent (hg : MinorGoodLe d N u z m ω Ψ M) :
    GoodEvent (green (Hflow d N u ω) z) m Ψ := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    have h := hg.diag_sub_le ∅ (by simp) x (Finset.notMem_empty x)
    rw [gEnt_empty] at h
    simpa using h
  · have h := hg.off_le ∅ (by simp) x y hxy
    rw [gEnt_empty] at h
    simpa [hxy] using h

/-- The shape in which the flow consumes it: `z = z_u`, `m = m_E`, where `|m_E| = 1` is
`RBM.norm_mE`. -/
theorem minorGoodLe_of_goodEvent_flow {E : ℝ} (hE : |E| ≤ 2) (hz : (zt E u).im ≠ 0)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) Ψ) :
    MinorGoodLe d N u (zt E u) (mE E) ω (2 * Ψ) M :=
  minorGoodLe_of_goodEvent hz (norm_mE hE) hΨ0 hΨ4 hMΨ hG

end RBM.Gauss

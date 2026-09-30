/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridAssemblyKerClass
import RBM1D.Gauss.GridQAlgebra
import RBM1D.Gauss.Lemma514Alt

/-!
# Case 2 class bridges for `KerClass` (the hypotheses `hDcls`/`hA0cls`)

No new paper content.  This file bridges the restricted kernel class `KerClass`
(`GridAssemblyKerClass.lean`) with the one-step drift decomposition `grid_step_Q`
(`GridQAlgebra.lean`), using the decay/sum-zero producers of `Hierarchy/SumZeroDyn.lean`
(`fastDecay_Qop`, `fastDecay_Qop_le`, `fastDecay_commS`, `SumZero_commS`,
`sumZeroAt_zero_of_sumZero`, `fastDecay_varthetaDot`, `Psum_varthetaDot`) and `sumZeroAt_Qop`
(`Lemma514Alt.lean`).

Recall `KerClass L u Kd sz δ i X ↔ FastDecay L (ellHat L (u i) · Kd) δ X ∧
(sz = true → SumZeroAt L 0 X)`, and `grid_step_Q`'s Case 2 drift
(after dividing by `Δ`) is the tensor `Qop (u j) D + commS ξ (u j) A - varthetaDot (u j) · P A`,
where `D` is the (Q-transformed) drift and `A` is the (Q-transformed) `(L-K)`-tensor at time
`u j`.  Each of the three summands is `Qop`/`commS`/`varthetaDot·P` applied to a tensor.

## Main results

* `kerClass_add`, `kerClass_mono`: `KerClass` is closed under sums (`δ` adds, via
  `FastDecay.add`/linearity of `SumZeroAt`) and monotone in the radius `ellHat L (u i) · Kd`
  and in `δ` (via `FastDecay.mono`); the index `i` may change together with `Kd` as long as the
  resulting radius only grows (this is exactly how the drift moves from the kernel's
  "generation" time `u j` to its "start" time `u (j+1)`, via `ellHat_real_mono`).
* `kerClass_Qop`, `kerClass_commS`, `kerClass_varthetaDot`: each of the three drift
  summands is in `KerClass … true …` whenever its tensor input is `FastDecay` at radius
  `ellHat L (u i) · Kd` and bounded, at the *same* index `i` as the input.
* `kerClass_caseTwo_drift`: the Case 2 drift of `grid_step_Q` (the sum of the three
  summands, each fed from a common index `j`) is in `KerClass … true …` at the *next* index
  `j + 1` — exactly the `hDcls` field shape. `kerClass_Qop_zero` records the corresponding
  `hA0cls` shape at `i = 0`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Matrix Finset RBM.SumZeroDyn

variable (L : ℕ) [NeZero L]

section KerClassAlgebra

/-! ### (T1) `KerClass` is closed under sums and monotone -/

/-- **`kerClass_add`**: `KerClass` is closed under sums at a common `(Kd, sz, i)`; the
error `δ` adds (`FastDecay.add`), and the sum-zero half is linear (`SumZeroAt` is a sum of
linear conditions). -/
theorem kerClass_add {n : ℕ} {u : ℕ → ℝ} {Kd δ₁ δ₂ : ℝ} {sz : Bool} {i : ℕ}
    {X Y : LoopArg L (n + 1) → ℂ} (hX : KerClass L u Kd sz δ₁ i X)
    (hY : KerClass L u Kd sz δ₂ i Y) :
    KerClass L u Kd sz (δ₁ + δ₂) i (X + Y) := by
  refine ⟨FastDecay.add L hX.1 hY.1, fun hsz => ?_⟩
  have h1 := hX.2 hsz
  have h2 := hY.2 hsz
  intro x
  have e : ∀ b : LoopArg L (n + 1), (if b 0 = x then (X + Y) b else (0 : ℂ))
      = (if b 0 = x then X b else 0) + (if b 0 = x then Y b else 0) := by
    intro b; by_cases hb : b 0 = x <;> simp [hb, Pi.add_apply]
  change ∑ b : LoopArg L (n + 1), (if b 0 = x then (X + Y) b else (0 : ℂ)) = 0
  simp only [e, Finset.sum_add_distrib]
  rw [h1 x, h2 x, add_zero]

/-- Negation preserves `KerClass` at the same `(Kd, sz, δ, i)` (used to turn the Case 2 drift's
subtraction into a sum, for `kerClass_add`). -/
theorem kerClass_neg {n : ℕ} {u : ℕ → ℝ} {Kd δ : ℝ} {sz : Bool} {i : ℕ}
    {X : LoopArg L (n + 1) → ℂ} (h : KerClass L u Kd sz δ i X) :
    KerClass L u Kd sz δ i (-X) := by
  refine ⟨fun a ha => by rw [Pi.neg_apply, norm_neg]; exact h.1 a ha, fun hsz => ?_⟩
  have h2 := h.2 hsz
  intro x
  have e : ∀ b : LoopArg L (n + 1), (if b 0 = x then (-X) b else (0 : ℂ))
      = -(if b 0 = x then X b else 0) := by
    intro b; by_cases hb : b 0 = x <;> simp [hb]
  change ∑ b : LoopArg L (n + 1), (if b 0 = x then (-X) b else (0 : ℂ)) = 0
  simp only [e]
  rw [Finset.sum_neg_distrib, h2 x, neg_zero]

/-- **`kerClass_mono`**: monotone in the radius `ellHat L (u i) · Kd` and in `δ`
(`FastDecay.mono`). Specializing `i = i'` gives the literal "monotone in `(Kd, δ)`" statement
(with `hR` discharged by `mul_le_mul_of_nonneg_left`); with `i ≠ i'` and `hR` discharged via
`ellHat_real_mono`, this is exactly the "class at the kernel's start time" shift used by
`kerClass_caseTwo_drift`. -/
theorem kerClass_mono {n : ℕ} {u : ℕ → ℝ} {Kd Kd' δ δ' : ℝ} {sz : Bool} {i i' : ℕ}
    {X : LoopArg L (n + 1) → ℂ} (h : KerClass L u Kd sz δ i X)
    (hR : ellHat L (u i : ℂ) * Kd ≤ ellHat L (u i' : ℂ) * Kd') (hδ : δ ≤ δ') :
    KerClass L u Kd' sz δ' i' X :=
  ⟨FastDecay.mono L h.1 hR hδ, h.2⟩

end KerClassAlgebra

section KerClassErrors

/-! ### Explicit error terms (the closed forms of the producers) -/

open Real in
/-- The `Psum` bound of `norm_Psum_le_of_fastDecay` at radius `ellHat L t · Kd`:
`(2e(ℓ̂_t Kd + 1))^n M + L^n δ`. -/
def psumBnd (n : ℕ) (t Kd M δ : ℝ) : ℝ :=
  (2 * exp 1 * (ellHat L (t : ℂ) * Kd + 1)) ^ n * M + (L : ℝ) ^ n * δ

open Real in
/-- **(T2) error**: the error of `fastDecay_Qop_le`,
`δ + ((6e·cTwo52·Kd)^n M + (2cTwo52)^n L^n δ)·exp(-cZero·Kd/2)`. -/
def deltaQop (n : ℕ) (Kd M δ : ℝ) : ℝ :=
  δ + ((6 * exp 1 * cTwo52 * Kd) ^ n * M + (2 * cTwo52) ^ n * (L : ℝ) ^ n * δ)
    * exp (-(cZero * Kd / 2))

open Real in
/-- The error of `fastDecay_commS` at radius `R` and `Psum` bound `P` (verbatim). -/
def commSErr (n : ℕ) (t R P : ℝ) : ℝ :=
  (n + 1) * ((1 - t)⁻¹ * (P * ((cTwo52 / ellHat L (t : ℂ)) ^ n
      * exp (-(cZero * (R / 2) / ellHat L (t : ℂ)))))
    + L * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ)))
      * (P * (cTwo52 / ellHat L (t : ℂ)) ^ n)))
  + (1 + n) * (1 - t)⁻¹ * P * ((cTwo52 / ellHat L (t : ℂ)) ^ n
      * exp (-(cZero * ((2 * R + 1) / 2) / ellHat L (t : ℂ))))

/-- **(T3) error**: `fastDecay_commS`'s error at `R := ellHat L t · Kd`,
`P := psumBnd = (2e(ℓ̂_t Kd + 1))^n M + L^n δ`. -/
def deltaCommS (n : ℕ) (t Kd M δ : ℝ) : ℝ :=
  commSErr L n t (ellHat L (t : ℂ) * Kd) (psumBnd L n t Kd M δ)

open Real in
/-- **(T4) error**: `fastDecay_Psum_mul ∘ fastDecay_varthetaDot` at `R := ellHat L t · 4Kd`,
`P · (3n(cTwo52/ℓ̂_t)^n (1-t)⁻¹ exp(-cZero(ℓ̂_t Kd - 1/2)/ℓ̂_t))`, with
`P := psumBnd`. -/
def deltaVD (n : ℕ) (t Kd M δ : ℝ) : ℝ :=
  psumBnd L n t Kd M δ * (3 * n * (cTwo52 / ellHat L (t : ℂ)) ^ n * (1 - t)⁻¹
    * exp (-(cZero * (ellHat L (t : ℂ) * Kd - 1 / 2) / ellHat L (t : ℂ))))

theorem psumBnd_nonneg (hL : 3 ≤ L) {n : ℕ} {t Kd M δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ) : 0 ≤ psumBnd L n t Kd M δ := by
  have hℓ := half_le_ellHat_real L hL ht0 ht1
  have : 0 ≤ ellHat L (t : ℂ) * Kd := by nlinarith
  unfold psumBnd; positivity

omit [NeZero L] in
theorem deltaQop_nonneg {n : ℕ} {Kd M δ : ℝ} (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ) :
    0 ≤ deltaQop L n Kd M δ := by
  have hc2 := cTwo52_pos
  have : 0 ≤ Kd := by linarith
  unfold deltaQop; positivity

theorem deltaCommS_nonneg (hL : 3 ≤ L) {n : ℕ} {t Kd M δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ) : 0 ≤ deltaCommS L n t Kd M δ := by
  have hP := psumBnd_nonneg L hL (n := n) ht0 ht1 hKd hM0 hδ0
  have hℓpos : 0 < ellHat L (t : ℂ) := ellHat_real_pos' L hL ht0 ht1
  have hc2 := cTwo52_pos
  have h1t : 0 < 1 - t := by linarith
  unfold deltaCommS commSErr; positivity

theorem deltaVD_nonneg (hL : 3 ≤ L) {n : ℕ} {t Kd M δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ) : 0 ≤ deltaVD L n t Kd M δ := by
  have hP := psumBnd_nonneg L hL (n := n) ht0 ht1 hKd hM0 hδ0
  have hℓpos : 0 < ellHat L (t : ℂ) := ellHat_real_pos' L hL ht0 ht1
  have hc2 := cTwo52_pos
  have h1t : 0 < 1 - t := by linarith
  unfold deltaVD; positivity

end KerClassErrors

section KerClassProducers

/-! ### (T2)–(T4) the three drift summands of `grid_step_Q` -/

/-- **`kerClass_Qop`**: if `B` is `FastDecay` at radius `ellHat L (u i) · Kd` with error
`δ` and bounded by `M`, then `Qop L (u i) B` is in `KerClass L u Kd true (deltaQop L n Kd M δ) i`
(the explicit error of `SumZeroDyn.fastDecay_Qop_le`, same radius); the sum-zero half is
unconditional, `sumZeroAt_Qop`. -/
theorem kerClass_Qop (hL : 3 ≤ L) {u : ℕ → ℝ} {i : ℕ} (hu0 : 0 ≤ u i) (hu1 : u i < 1)
    {n : ℕ} {Kd M δ : ℝ} (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ)
    {B : LoopArg L (n + 1) → ℂ} (hBM : ∀ b, ‖B b‖ ≤ M)
    (hB : FastDecay L (ellHat L (u i : ℂ) * Kd) δ B) :
    KerClass L u Kd true (deltaQop L n Kd M δ) i (Qop L (u i : ℂ) B) :=
  ⟨fastDecay_Qop_le L hL hu0 hu1 hKd hM0 hδ0 hBM hB,
    fun _ => sumZeroAt_Qop L hL (norm_ofReal_lt_one hu0 hu1) B⟩

/-- **`kerClass_commS`**: if `B` is `FastDecay` at radius `ellHat L (u i) · Kd` with error
`δ` and bounded by `M`, then `commS L ξ (u i) B` is in
`KerClass L u (4 * Kd) true (deltaCommS L n (u i) Kd M δ) i`: the explicit error of
`SumZeroDyn.fastDecay_commS` at `R = ellHat(u i)·Kd`, `P = psumBnd`, after widening the radius
`2R + 1 ≤ ℓ·(4Kd)` (`radius_le`); the sum-zero half is unconditional, `SumZero_commS` +
`sumZeroAt_zero_of_sumZero`. -/
theorem kerClass_commS (hL : 3 ≤ L) {u : ℕ → ℝ} {i : ℕ} (hu0 : 0 ≤ u i) (hu1 : u i < 1)
    {n : ℕ} {ξ : Fin (n + 1) → ℂ} (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    {Kd M δ : ℝ} (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ)
    {B : LoopArg L (n + 1) → ℂ} (hBM : ∀ b, ‖B b‖ ≤ M)
    (hB : FastDecay L (ellHat L (u i : ℂ) * Kd) δ B) :
    KerClass L u (4 * Kd) true (deltaCommS L n (u i) Kd M δ) i (commS L ξ (u i : ℂ) B) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hR0 : (0 : ℝ) < ellHat L (u i : ℂ) * Kd := by nlinarith
  have hP := norm_Psum_le_of_fastDecay L hR0 hM0 hδ0 hBM hB
  have hP0 := psumBnd_nonneg L hL (n := n) hu0 hu1 hKd hM0 hδ0
  have hFD := fastDecay_commS L hL hu0 hu1 hξ hR0 hP0 hP
  have hwiden : 2 * (ellHat L (u i : ℂ) * Kd) + 1 ≤ ellHat L (u i : ℂ) * (4 * Kd) :=
    radius_le hℓ hKd
  exact ⟨FastDecay.mono L hFD hwiden le_rfl,
    fun _ => sumZeroAt_zero_of_sumZero L
      (SumZero_commS L hL (fun k => norm_ofReal_mul_lt_one hu0 hu1 (hξ k))
        (norm_ofReal_lt_one hu0 hu1) B)⟩

/-- **`kerClass_varthetaDot`**: if `B` is `FastDecay` at radius `ellHat L (u i) · Kd` with
error `δ` and bounded by `M`, then the `ϑ̇ · P` term `fun a => Psum L B (a 0) * varthetaDot L
(u i) a` is in `KerClass L u (4 * Kd) true (deltaVD L n (u i) Kd M δ) i`: the explicit error of
`fastDecay_Psum_mul ∘ fastDecay_varthetaDot` at `R = ellHat(u i)·4Kd`; the sum-zero half is
unconditional, `Psum_mul_left` + `Psum_varthetaDot`. -/
theorem kerClass_varthetaDot (hL : 3 ≤ L) {u : ℕ → ℝ} {i : ℕ} (hu0 : 0 ≤ u i) (hu1 : u i < 1)
    {n : ℕ} {Kd M δ : ℝ} (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ)
    {B : LoopArg L (n + 1) → ℂ} (hBM : ∀ b, ‖B b‖ ≤ M)
    (hB : FastDecay L (ellHat L (u i : ℂ) * Kd) δ B) :
    KerClass L u (4 * Kd) true (deltaVD L n (u i) Kd M δ) i
      (fun a : LoopArg L (n + 1) => Psum L B (a 0) * varthetaDot L (u i) a) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hR0 : (0 : ℝ) < ellHat L (u i : ℂ) * Kd := by nlinarith
  have hP := norm_Psum_le_of_fastDecay L hR0 hM0 hδ0 hBM hB
  have hP0 := psumBnd_nonneg L hL (n := n) hu0 hu1 hKd hM0 hδ0
  have hR2 : (2 : ℝ) ≤ ellHat L (u i : ℂ) * (4 * Kd) := two_le_radius hℓ hKd
  have hVD := fastDecay_varthetaDot L hL hu0 hu1 (n := n) hR2
  have key : ellHat L (u i : ℂ) * (4 * Kd) / 4 = ellHat L (u i : ℂ) * Kd := by ring
  rw [key] at hVD
  exact ⟨fastDecay_Psum_mul L hVD hP0 hP, fun _ => sumZeroAt_zero_of_sumZero L
    (fun x => by rw [Psum_mul_left, Psum_varthetaDot L hL hu0 hu1, mul_zero])⟩

end KerClassProducers

section CaseTwoDrift

/-! ### (T5) the assembled Case 2 drift and initial datum -/

/-- **`kerClass_caseTwo_drift`**: the Case 2 drift of `grid_step_Q` — the tensor
`Qop (u j) D + commS ξ (u j) A - varthetaDot (u j) · P A` built from a common index `j` — is in
`KerClass L u (4 * Kd) true (deltaQop … + deltaCommS … + deltaVD …) (j + 1)`: exactly the
`GridAssemblyHypPW.hDcls` field type with `sz = true` and
`δD j ω :=` the explicit sum of the three errors. The uses of `kerClass_mono` shift the class
from the drift's time `u j` to the kernel's start time `u (j + 1)` (`ellHat_real_mono`),
keeping the errors unchanged. -/
theorem kerClass_caseTwo_drift (hL : 3 ≤ L) {u : ℕ → ℝ} {j : ℕ}
    (hu0 : 0 ≤ u j) (hu1 : u (j + 1) < 1) (hmono : u j ≤ u (j + 1))
    {n : ℕ} {ξ : Fin (n + 1) → ℂ} (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    {Kd MD MA δD δA : ℝ} (hKd : 1 ≤ Kd) (hMD0 : 0 ≤ MD) (hMA0 : 0 ≤ MA)
    (hδD0 : 0 ≤ δD) (hδA0 : 0 ≤ δA)
    {D A : LoopArg L (n + 1) → ℂ} (hDM : ∀ b, ‖D b‖ ≤ MD) (hAM : ∀ b, ‖A b‖ ≤ MA)
    (hD : FastDecay L (ellHat L (u j : ℂ) * Kd) δD D)
    (hA : FastDecay L (ellHat L (u j : ℂ) * Kd) δA A) :
    KerClass L u (4 * Kd) true
      (deltaQop L n Kd MD δD + deltaCommS L n (u j) Kd MA δA + deltaVD L n (u j) Kd MA δA)
      (j + 1)
      (fun a : LoopArg L (n + 1) => Qop L (u j : ℂ) D a + commS L ξ (u j : ℂ) A a
        - varthetaDot L (u j) a * Psum L A (a 0)) := by
  have huj1 : u j < 1 := lt_of_le_of_lt hmono hu1
  have hcls1 := kerClass_Qop L hL hu0 huj1 hKd hMD0 hδD0 hDM hD
  have hcls2 := kerClass_commS L hL hu0 huj1 hξ hKd hMA0 hδA0 hAM hA
  have hcls3 := kerClass_varthetaDot L hL hu0 huj1 hKd hMA0 hδA0 hAM hA
  have hℓmono : ellHat L (u j : ℂ) ≤ ellHat L (u (j + 1) : ℂ) := ellHat_real_mono L hmono hu1
  have hℓj10 : (0 : ℝ) ≤ ellHat L (u (j + 1) : ℂ) := by
    linarith [half_le_ellHat_real L hL (hu0.trans hmono) hu1]
  have hKd0 : (0 : ℝ) ≤ Kd := by linarith
  have hR1 : ellHat L (u j : ℂ) * Kd ≤ ellHat L (u (j + 1) : ℂ) * (4 * Kd) := by
    calc ellHat L (u j : ℂ) * Kd ≤ ellHat L (u (j + 1) : ℂ) * Kd :=
          mul_le_mul_of_nonneg_right hℓmono hKd0
      _ ≤ ellHat L (u (j + 1) : ℂ) * (4 * Kd) := by nlinarith
  have hR2 : ellHat L (u j : ℂ) * (4 * Kd) ≤ ellHat L (u (j + 1) : ℂ) * (4 * Kd) :=
    mul_le_mul_of_nonneg_right hℓmono (by linarith)
  have hcls1' := kerClass_mono L hcls1 hR1 le_rfl
  have hcls2' := kerClass_mono L hcls2 hR2 le_rfl
  have hcls3' := kerClass_mono L hcls3 hR2 le_rfl
  have hsum2 := kerClass_add L (kerClass_add L hcls1' hcls2') (kerClass_neg L hcls3')
  have e : (fun a : LoopArg L (n + 1) => Qop L (u j : ℂ) D a + commS L ξ (u j : ℂ) A a
        - varthetaDot L (u j) a * Psum L A (a 0))
      = Qop L (u j : ℂ) D + commS L ξ (u j : ℂ) A
        + (-(fun a : LoopArg L (n + 1) => Psum L A (a 0) * varthetaDot L (u j) a)) := by
    funext a
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rw [e]
  exact hsum2

/-- **(T5), the `hA0cls` shape**: `Qop` of a `FastDecay` initial tensor is in the class at
`i = 0` with the explicit error `deltaQop L n Kd M δ` — the special case `i := 0` of
`kerClass_Qop`, matching `GridAssemblyHypPW.hA0cls` (`GridAssemblyKerClass.lean`) with
`sz = true` and `δ0 := deltaQop L n Kd M δ`. -/
theorem kerClass_Qop_zero (hL : 3 ≤ L) {u : ℕ → ℝ} (hu0 : 0 ≤ u 0) (hu1 : u 0 < 1)
    {n : ℕ} {Kd M δ : ℝ} (hKd : 1 ≤ Kd) (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ)
    {A0 : LoopArg L (n + 1) → ℂ} (hA0M : ∀ b, ‖A0 b‖ ≤ M)
    (hA0 : FastDecay L (ellHat L (u 0 : ℂ) * Kd) δ A0) :
    KerClass L u Kd true (deltaQop L n Kd M δ) 0 (Qop L (u 0 : ℂ) A0) :=
  kerClass_Qop L hL hu0 hu1 hKd hM0 hδ0 hA0M hA0

end CaseTwoDrift

section LoopLengthTwoExample

end LoopLengthTwoExample

end RBM.Gauss.Grid

end


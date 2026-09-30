/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GreenSpectralL1

/-!
# The deterministic pair spectral precursor to (2.30)

The pair analogue of `GreenSpectralL1.lean`. There `green_spectral_identity_blockM` expands the
loop `∑_x (G(σ₁)²)_{xx} S°_{xy} G(σ₂)_{yy}` in the eigenbasis, producing the diagonal moment
`blockM hH a0 α` (after (2.31)) weighted by `|ψ_γ(y)|²`. Here we expand the *off-diagonal*
loop `∑_x (G(σ₁)²)_{xy} S°_{xy} (G(σ₂)²)_{yx}` (both resolvents squared, evaluated between `x`
and the fixed point `y`), which produces the pair moment `M_{y,α,β} := blockM2 hH a0 α β`
weighted by `conj(ψ_α(y)) ψ_β(y)`. This is the deterministic content behind (2.30)'s `L₂` term,
exactly as `GreenSpectralL1.lean` is behind (2.29)'s `L₁` term.

`measure_bad2_le_of_que` is the pair analogue of `measure_bad_le_of_que`
(`Flow/Universality.lean`): the same union bound over the three blocks `{a0-1,a0,a0+1}`,
using that `queEvent212` already quantifies over a pair of (possibly distinct) eigenvector
indices.

This file proves only the deterministic identity, its `α = β` reduction, and the probability bound
that follows from a hypothesised QUE-event bound. It asserts no stochastic domination on its own.
-/

namespace RBM

open Matrix Finset MeasureTheory

section GreenSpectralL2

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem eigenvalues_ne_of_im_ne {w : ℂ} (hw : w.im ≠ 0) :
    ∀ α, (hH.eigenvalues α : ℂ) ≠ w := by
  intro α h
  have him := congrArg Complex.im h
  simp at him
  exact hw him.symm

/-- General (off-diagonal) entries of the squared resolvent: the pair analogue of
`green_sq_apply_self` (`GreenSpectralL1.lean`). -/
private theorem green_sq_apply {w : ℂ} (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x y : n) :
    (green H w ^ 2) x y =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis α y)) := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let d : n → ℂ := fun α => spectralPole hH w α
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hG : green H w = U * diagonal d * star U := by
    simpa [U, d, spectralPole] using green_eq_spectral hH hw
  have hG2 : green H w ^ 2 = U * diagonal (fun α => d α * d α) * star U := by
    rw [hG]
    simp only [pow_two]
    calc
      (U * diagonal d * star U) * (U * diagonal d * star U) =
          U * diagonal d * (star U * U) * diagonal d * star U := by noncomm_ring
      _ = U * diagonal d * 1 * diagonal d * star U := by rw [hUU]
      _ = U * (diagonal d * diagonal d) * star U := by
        simp only [mul_one]
        rw [← Matrix.mul_assoc U (diagonal d) (diagonal d)]
      _ = U * diagonal (fun α => d α * d α) * star U := by
        rw [diagonal_mul_diagonal]
  rw [hG2, mul_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_diagonal, star_apply]
  change ((hH.eigenvectorUnitary : Matrix n n ℂ) x α * (d α * d α) *
      star ((hH.eigenvectorUnitary : Matrix n n ℂ) y α)) = _
  simp only [IsHermitian.eigenvectorUnitary_apply]
  ring

/-- General (off-diagonal) entries of `Gsig²` in the eigenbasis: the pair analogue of
`Gsig_sq_apply_self_spectral`. -/
private theorem Gsig_sq_apply_spectral (z : ℂ) (hη : 0 < z.im) (σ : Bool) (x y : n) :
    (Gsig H z σ ^ 2) x y =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis α y)) := by
  have him : (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
    by_cases hσ : σ
    · simpa [hσ] using (ne_of_gt hη)
    · rw [if_neg hσ]
      have hconj : ((starRingEnd ℂ) z).im = -z.im := by simp
      rw [hconj]
      exact neg_ne_zero.mpr (ne_of_gt hη)
  have heig := eigenvalues_ne_of_im_ne hH him
  simpa [Gsig, spectralGsigPole, spectralPole] using
    green_sq_apply hH heig x y

end GreenSpectralL2

section BlockGreenSpectralL2

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
variable (hH : Hm.IsHermitian)

local notation "Idx" => (ZMod L × Fin W)

omit [NeZero W] in
/-- `M_{y,α,β} = N · 3⁻¹ ∑_{|a - a₀| ≤ 1} ψ_β* (E_a - N⁻¹) ψ_α` for `y ∈ I_{a₀}`, the pair
analogue of `blockM` (after (2.31)). -/
noncomputable def blockM2 (a0 : ZMod L) (α β : Idx) : ℂ :=
  ((L * W : ℕ) : ℂ) * ((1 / 3 : ℂ) * ∑ a ∈ ({a0 - 1, a0, a0 + 1} : Finset (ZMod L)),
    eigOverlap hH (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) β α)

/-- `ψ_i* diag(d) ψ_j = ∑_p d_p ψ_i(p)* ψ_j(p)`, the general (non-self) version of
`eigOverlap_diagonal_self`. -/
private theorem eigOverlap_diagonal (d : Idx → ℂ) (i j : Idx) :
    eigOverlap hH (diagonal d) i j =
      ∑ p, d p * (star (hH.eigenvectorBasis i p) * hH.eigenvectorBasis j p) := by
  simp only [eigOverlap, dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **`M_{y,α,β}` as in the paper**: `blockM2 = N ∑_x ψ_α(x) ψ_β(x)* S°_{xy}`, `y = (a₀,β₀)`, the
pair analogue of `blockM_eq` (needs `L ≥ 3`). -/
private theorem blockM2_eq (hL : 3 ≤ L) (a0 : ZMod L) (β0 : Fin W) (α β : Idx) :
    blockM2 hH a0 α β = ((L * W : ℕ) : ℂ) * ∑ x, (hH.eigenvectorBasis α x *
        star (hH.eigenvectorBasis β x)) * (Svar L W x (a0, β0) - ((L * W : ℕ) : ℂ)⁻¹) := by
  set T : Finset (ZMod L) := {a0 - 1, a0, a0 + 1} with hT
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have h2 : (2 : ZMod L) ≠ 0 := two_ne_zero_zmod L hL
  have hcard : T.card = 3 := by
    have e1 : a0 - 1 ≠ a0 := fun h => h1 (by linear_combination -h)
    have e2 : a0 - 1 ≠ a0 + 1 := fun h => h2 (by linear_combination -h)
    have e3 : a0 ≠ a0 + 1 := fun h => h1 (by linear_combination -h)
    rw [hT, Finset.card_insert_of_notMem (by simp [e1, e2]),
      Finset.card_insert_of_notMem (by simp [e3]), Finset.card_singleton]
  have hmemT : ∀ b : ZMod L, b ∈ T ↔ b - a0 ∈ sbSupport L := by
    intro b
    rw [sub_mem_sbSupport_iff, hT]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · right; left; linear_combination -h
      · left; linear_combination -h
      · right; right; linear_combination -h
    · rintro (h | h | h)
      · right; left; linear_combination -h
      · left; linear_combination -h
      · right; right; linear_combination -h
  have hdiag : ∀ a : ZMod L, eigOverlap hH (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ))
      β α = ∑ p, ((if p.1 = a then (W : ℂ)⁻¹ else 0) - ((L * W : ℕ) : ℂ)⁻¹) *
        (hH.eigenvectorBasis α p * star (hH.eigenvectorBasis β p)) := by
    intro a
    rw [← queObs_singleton, queObs_eq_diagonal, eigOverlap_diagonal]
    simp only [Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.mem_singleton]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp only [blockM2, ← hT, hdiag]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, hcard]
  have hS : Svar L W p (a0, β0) = (if p.1 ∈ T then (3 : ℂ)⁻¹ else 0) * (W : ℂ)⁻¹ := by
    obtain ⟨b, γ⟩ := p
    rw [Svar_apply, SB_apply, sbKernel]
    simp only [hmemT]
  rw [hS, Finset.sum_ite_eq]
  split_ifs <;> push_cast <;> ring

/-- Exact eigenbasis expansion of the pair off-diagonal loop, before substituting `blockM2_eq`;
the pair analogue of `green_spectral_sum_variance`. -/
private theorem green_spectral_sum_variance2 (a0 : ZMod L) (β0 : Fin W) (z₁ z₂ : ℂ)
    (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx, (Gsig Hm z₁ σ₁ ^ 2) x (a0, β0) *
        (Svar L W x (a0, β0) - ((L * W : ℕ) : ℂ)⁻¹) * (Gsig Hm z₂ σ₂ ^ 2) (a0, β0) x) =
      ∑ α : Idx, ∑ β : Idx,
        (spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α) *
          (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
          (star (hH.eigenvectorBasis α (a0, β0)) * hH.eigenvectorBasis β (a0, β0)) *
          ∑ x : Idx, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) *
            (Svar L W x (a0, β0) - ((L * W : ℕ) : ℂ)⁻¹) := by
  set y0 : Idx := (a0, β0) with hy0
  set S0 : Idx → ℂ := fun x => Svar L W x y0 - ((L * W : ℕ) : ℂ)⁻¹ with hS0
  set A : Idx → Idx → ℂ := fun γ x => hH.eigenvectorBasis γ x with hA
  calc
    (∑ x : Idx, (Gsig Hm z₁ σ₁ ^ 2) x y0 * S0 x * (Gsig Hm z₂ σ₂ ^ 2) y0 x) =
        ∑ x : Idx, (∑ α : Idx, spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α *
            (A α x * star (A α y0))) * S0 x *
          ∑ β : Idx, spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β *
            (A β y0 * star (A β x)) := by
          congr 1
          funext x
          rw [Gsig_sq_apply_spectral hH z₁ hη₁ σ₁ x y0, Gsig_sq_apply_spectral hH z₂ hη₂ σ₂ y0 x]
    _ = ∑ α : Idx, ∑ β : Idx,
          (spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α) *
            (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
            (star (A α y0) * A β y0) *
            ∑ x : Idx, (A α x * star (A β x)) * S0 x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- **Exact spectral expansion of the pair off-diagonal loop**, with `M_{y,α,β}` substituted from
`blockM2_eq`: the pair analogue of `green_spectral_identity_blockM`. -/
theorem green_spectral_identity_blockM2 (hL : 3 ≤ L) (a0 : ZMod L) (β0 : Fin W) (z₁ z₂ : ℂ)
    (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx, (Gsig Hm z₁ σ₁ ^ 2) x (a0, β0) *
        (Svar L W x (a0, β0) - ((L * W : ℕ) : ℂ)⁻¹) * (Gsig Hm z₂ σ₂ ^ 2) (a0, β0) x) =
      ((L * W : ℕ) : ℂ)⁻¹ * ∑ α : Idx, ∑ β : Idx,
        spectralGsigPole hH z₁ σ₁ α ^ 2 * spectralGsigPole hH z₂ σ₂ β ^ 2 *
          blockM2 hH a0 α β * star (hH.eigenvectorBasis α (a0, β0)) *
            hH.eigenvectorBasis β (a0, β0) := by
  have hN : ((L * W : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne W))
  rw [green_spectral_sum_variance2 hH a0 β0 z₁ z₂ hη₁ hη₂ σ₁ σ₂, eq_inv_mul_iff_mul_eq₀ hN,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [blockM2_eq hH hL a0 β0 α β, pow_two, pow_two]
  ring

/-- **The bad event of (2.30) is rare, from QUE**: the pair analogue of `measure_bad_le_of_que`.
If (2.12) holds at energy `E` with window `η` and threshold `θ²` (probability `≤ ε'` for each
block `a`), then `P(∃ α β, |λ_α - E| ≤ w, |λ_β - E| ≤ w, |M_{y,α,β}| ≥ θ) ≤ 3ε'` for `w ≤ η`
(union bound over `|a - a₀| ≤ 1`, using that `queEvent212` already existentially quantifies over a
pair of eigenvector indices). -/
theorem measure_bad2_le_of_que {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {L W : ℕ}
    [NeZero L] {Hr : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : ∀ ω, (Hr ω).IsHermitian) {E w η θ ε' : ℝ} (hw : w ≤ η) (hθ : 0 ≤ θ) (a0 : ZMod L)
    (hque : ∀ a, P (queEvent212 hH a E η (θ ^ 2)) ≤ ENNReal.ofReal ε') :
    P {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ w ∧ |(hH ω).eigenvalues β - E| ≤ w ∧
      θ ≤ ‖blockM2 (hH ω) a0 α β‖} ≤ ENNReal.ofReal (3 * ε') := by
  set T : Finset (ZMod L) := {a0 - 1, a0, a0 + 1} with hT
  have hsub : {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ w ∧ |(hH ω).eigenvalues β - E| ≤ w ∧
      θ ≤ ‖blockM2 (hH ω) a0 α β‖} ⊆
      ⋃ a ∈ T, queEvent212 hH a E η (θ ^ 2) := by
    rintro ω ⟨α, β, hα, hβ, hM⟩
    set x : ZMod L → ℂ := fun a => ((L * W : ℕ) : ℂ) *
      eigOverlap (hH ω) (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) β α with hx
    have hMx : blockM2 (hH ω) a0 α β = (1 / 3 : ℂ) * ∑ a ∈ T, x a := by
      simp only [blockM2, hx, ← hT, Finset.mul_sum]; ring_nf
    have hex : ∃ a ∈ T, θ ≤ ‖x a‖ := by
      by_contra hno
      push Not at hno
      have hTne : T.Nonempty := ⟨a0, by simp [hT]⟩
      have h1 : ∑ a ∈ T, ‖x a‖ < ∑ _a ∈ T, θ := Finset.sum_lt_sum_of_nonempty hTne hno
      have h2 : T.card ≤ 3 := Finset.card_le_three
      have h3 : ‖blockM2 (hH ω) a0 α β‖ ≤ (1 / 3) * ∑ a ∈ T, ‖x a‖ := by
        rw [hMx, norm_mul]
        have : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      have h4 : (T.card : ℝ) * θ ≤ 3 * θ := mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hθ
      linarith
    obtain ⟨a, haT, ha⟩ := hex
    refine Set.mem_biUnion haT ⟨β, α, hβ.trans hw, hα.trans hw, ?_⟩
    exact pow_le_pow_left₀ hθ ha 2
  calc _ ≤ P (⋃ a ∈ T, queEvent212 hH a E η (θ ^ 2)) := measure_mono hsub
    _ ≤ ∑ a ∈ T, P (queEvent212 hH a E η (θ ^ 2)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ T, ENNReal.ofReal ε' := Finset.sum_le_sum fun a _ => hque a
    _ = T.card * ENNReal.ofReal ε' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * ENNReal.ofReal ε' := by
        gcongr
        exact_mod_cast (Finset.card_le_three : T.card ≤ 3)
    _ = ENNReal.ofReal (3 * ε') := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

end BlockGreenSpectralL2

end RBM


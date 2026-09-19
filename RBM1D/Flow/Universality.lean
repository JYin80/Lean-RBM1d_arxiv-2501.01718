/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Consequences
import RBM1D.Propagator.ZeroMode

/-!
# Theorems 2.5 (generalized QUE) and 2.6 (bulk universality)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.2–2.3 (pp. 9–14: Theorem 2.5 with
(2.11)–(2.17), Theorem 2.6 with (2.18)–(2.33)) and the end of §7.2 (pp. 81–84: (7.25)–(7.47)).
These are items (iii), (iv) of the abstract.

Everything random enters through **hypotheses** (never `axiom`): the conclusions of Theorem 2.4
(through `RBM.QDExpect`), the T65 output (7.47) (`RBM.Eq747`, a placeholder), and the external
references [51], [37]/[70] (`RBM.DBMUniversality`, `RBM.GreenComparison`).

## Theorem 2.5: the chain (2.14) → (2.17), fully proved from (2.8)/(2.9)

* **(2.14)** (deterministic, any Hermitian `H`, `A`): `RBM.imGreen` (`Im G = (G - G*)/(2i)`),
  `RBM.imGreen_eq_spectral` (`Im G = U diag(η|λ - z|⁻²) U*`), `RBM.trace_imGreen_mul_imGreen`
  (`Tr(Im G A Im G A) = ∑_{ij} η²|λ_i - z|⁻²|λ_j - z|⁻² |ψ_i* A ψ_j|²`), `RBM.sum_window_le`
  (first line of (2.14), constant `C = 4`), `RBM.sq_norm_eigOverlap_le`.
* **(2.15)**: `RBM.queObs` (`|S|⁻¹∑_{a∈S} E_a - N⁻¹`), `RBM.queObs_eq`
  (`E_a - N⁻¹ = L⁻¹ ∑_b (E_a - E_b)`), `RBM.trace_imGreen_mul_imGreen_eq` (`Im G` through
  `Tr G X G Y`, `Tr G X G* Y`), `RBM.norm_integral_trImIm_sub_le`,
  `RBM.norm_integral_trace_imGreen_queObs_le` (`|E Tr(Im G A Im G A)| ≤ 2(2ε + δ)`, `C = 2`).
* **Lemma 2.14 / (2.16)** as used: `RBM.norm_Theta_sub_Theta_le`
  (`|Θ_{ab} - Θ_{a'b'}| ≤ 288 (L + |1-ξ|^{-1/2})`, from (2.53) by telescoping),
  `RBM.norm_mul_ThetaTilde_sub_le` (same for `S̃`, via T46's `ThetaTilde_sub_ThetaTilde`),
  `RBM.msc_gap` (`|1 - |m|²|, |1 - m²| ≥ η/16`, i.e. (2.16)), `RBM.thetaOsc_Theta`,
  `RBM.thetaOsc_ThetaTilde`.
* **(2.17) + Markov**: `RBM.measure_queBad_le`, `RBM.measure_queBad_le_of_approx` (single `N`);
  the scale `RBM.queEta` (`η = N^{-1-τ*}(W²/N)^{1/3}`) and its arithmetic
  (`RBM.div_le_inv_sqrt_queEta`: `L ≤ η^{-1/2}`, i.e. `ℓ(z) = L`; `RBM.queBound_le`:
  `η²N²(ε₀ + W⁻¹ K(L + η^{-1/2})) ≲ W^δ N^{τ*-2c/3} + N^{-2τ*} + N^{-3τ*/2}`).
* **Theorem 2.5**: `RBM.que_of_QDExpect`, `RBM.que_literal_of_QDExpect` (any propagator),
  `RBM.theorem2_5_of_QDExpect` ((2.12) and (2.13) for `H`, from (2.8), (2.9)) and
  `RBM.theorem2_5_of_Thm221` (from Theorem 2.21 through `RBM.quantumDiffusion_of_Thm221`,
  via `RBM.QDExpect.of_Thm221`).

## Theorem 2.6

* Objects: `RBM.corrPairing` (`∫ O(α) ρ^{(k)}_H(E + α/N) dα`, density-free),
  `RBM.gueWeight`/`RBM.gueDensity`/`RBM.gueCorr`/`RBM.gueCorrPairing` (the explicit GUE
  correlation functions), `RBM.stieltjes` (`m_t`), `RBM.OUFlow` ((2.19)), `RBM.BulkUniversality`
  ((2.18)).
* External inputs as hypotheses: `RBM.DBMUniversality` ([51], (2.21)),
  `RBM.GreenComparison` ([37, Thm 15.3] + [70, Prop 4.17], (2.23) ⇒ (2.24)).
  The model-dependent claim (2.23) is `RBM.StepTwoClaim` (`RBM.Claim223`).
* **Theorem 2.6**: `RBM.theorem2_6_of_steps` ((2.21) + (2.24) ⇒ (2.20) = (2.18)).
* Step 3, the part formalized: `RBM.Eq747` (T65 placeholder for (7.47)),
  `RBM.que_flow_of_eq747` (**(2.27)**: Theorem 2.5 for `H_t`, `τ* = c/3`, via the zero-mode
  removal of §7.2), `RBM.blockM`/`RBM.blockM_eq` (`M_{y,α}` after (2.31)),
  `RBM.measure_bad_le_of_que`, `RBM.measure_bad_flow_of_eq747` (the bad event `B_y` of (2.29) has
  probability `≤ 3 N^{-c/18}`).

## Hypotheses (to be discharged later)

* `RBM.QDExpect B H z Θ`: (2.8), (2.9) at the spectral parameters `z_N = E_N + iη_N` of the proof,
  in the form `|E Tr G E_x G^{(*)} E_y - W⁻¹ ξ Θ(ξ)_{xy}| ≤ W^δ (N Im z)^{-3}` (paper:
  `(Wℓη)^{-3} W^δ` with `ℓ = L`), plus integrability of the loops.  For `H` it follows from
  Theorem 2.21 (`RBM.QDExpect.of_Thm221`) on a fixed energy slice of Lemma 2.8.
* `RBM.Eq747`: **T65 placeholder** for (7.47) (= `QDExpect` for `H_t` with `Θ̃`).  In the paper
  (7.47) comes from (7.29) and (7.26); (7.27), (7.28) are used only to prove (7.29) and the weak
  local law (2.26), which the formalized part does not use.
* `RBM.DBMUniversality` ([51]), `RBM.GreenComparison` ([37], [70]): external theorems.
* `RBM.StepTwoClaim`: the claim (2.23).

## Not formalized (and why)

* **(2.25)–(2.33) ⇒ (2.23)**: the Step 3 estimates of `L_1`, `L_2`.  They need [70, Lemma 4.18]
  ((2.25)) and [70, Lemma 4.20] ((2.31)), the weak local law (2.26) for `H_t` (hence the
  delocalization bound and the eigenvalue counting behind (2.32), (2.33)), and moment bounds on
  events of small probability.  Only the use of QUE in this step (the bad event `B_y`) is
  formalized (`RBM.measure_bad_flow_of_eq747`); (2.23) is the hypothesis `RBM.StepTwoClaim`.
* (2.26) from (7.28) and (7.26): not needed by the formalized part.
* The identification `corrPairing = ∫ O ρ^{(k)}` (for matrices with an eigenvalue density) and
  `H_∞ ∼ GUE`: not needed, since [51] is stated with the explicit GUE correlation function.

## Deviations from the paper

* **Uniformity in `E`.**  "`max_{|E| < 2-κ}`, for `N ≥ N₀`" in (2.12), (2.13) is rendered as "for
  every sequence of bulk energies `E_N`, eventually in `N`" (equivalent).  The matrix size is
  `N = L W` (`RBM.Band.size`); the eventual statements are in the index `N` of `RBM.Band`.
* (2.13) is stated for nonempty `A` (for `A = ∅` the displayed event is trivially sure).
* (2.14)–(2.15) constants are explicit (`C = 4`, `C = 2`); the `Θ`-oscillation bound is
  `O(L + |1-ξ|^{-1/2})` (the paper: `O(η^{-1/2})`, equal since `L ≤ η^{-1/2}`).
* `QDExpect` requires integrability of the loops (automatic in the paper since
  `‖G‖ ≤ η^{-1}`; `RBM.Transfer` records no measurability of `H`).
* **Theorem 2.6.**  `ρ^{(k)}_H` enters only through the density-free pairing `RBM.corrPairing`
  (equal to the paper's integral whenever the eigenvalues have a joint density); the GUE side is
  the literal marginal of the explicit GUE eigenvalue density (normalization `E|h_ij|² = N⁻¹`, the
  invariant law of (2.19)).  Test functions are `C^∞` with compact support.  [51] is stated with
  the GUE correlation functions directly (the paper writes `ρ_{H_∞}`, `H_∞ = H_{GUE}`); in the paper
  its input is the local law (Theorem 2.3).  (2.22) is quantified over every constant `C₀` in
  `|Re z_i - E| ≤ C₀/N`.
* **(2.27)** is proved from (7.47) for `ζ_U ≤ η/16` (T46's comparison `|1-ξ| ∼ |1-ξ(1-ζ)|` needs
  `ζ ≲ |1-ξ|`), at the scale `η = N^{-1-c/3}(W²/N)^{1/3}` of Theorem 2.5 (the paper writes
  `Im z = N^{-1+c/3}` in §7.2; both are `≥ N^{-1+c/3}`).
* **The bad event `B_y`** uses the threshold `N^{-c/36}` instead of the paper's `N^{-c/18}`: with
  (2.12) as stated (`|N ψ*Aψ|² ≥ N^{-τ*/6}`, `τ* = c/3`) the admissible threshold for `|M_{y,α}|`
  is `N^{-c/36}`; this only changes `c' = c/18` into `c/36` in (2.33).
-/

namespace RBM

open Matrix MeasureTheory Filter
open scoped ComplexConjugate

/-! ### The spectral side of (2.14) -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Im G(z) = (G(z) - G(z)*) / (2i)`, the imaginary part of the Green's function. -/
noncomputable def imGreen (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (2 * Complex.I)⁻¹ • (green H z - (green H z)ᴴ)

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- The spectral weight `η / ((λ_l - E)² + η²) = η |λ_l - z|⁻²` of `Im G(E + iη)`. -/
noncomputable def specWeight (E η : ℝ) (l : n) : ℝ :=
  η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)

/-- The overlap `ψ_i* A ψ_j` of two eigenvectors of `H` through a matrix `A`. -/
noncomputable def eigOverlap (A : Matrix n n ℂ) (i j : n) : ℂ :=
  star (fun x => hH.eigenvectorBasis i x) ⬝ᵥ (A *ᵥ fun x => hH.eigenvectorBasis j x)

theorem eigOverlap_eq (A : Matrix n n ℂ) (i j : n) :
    eigOverlap hH A i j = (star (hH.eigenvectorUnitary : Matrix n n ℂ) * A *
      (hH.eigenvectorUnitary : Matrix n n ℂ)) i j := by
  simp only [eigOverlap, dotProduct, mulVec, Matrix.mul_apply, star_apply,
    IsHermitian.eigenvectorUnitary_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `Im (λ - (E + iη))⁻¹ = η / ((λ - E)² + η²)` in the form used for `Im G`. -/
theorem two_I_inv_mul_sub_conj (lam E : ℝ) {η : ℝ} (hη : η ≠ 0) :
    (2 * Complex.I)⁻¹ * (((lam : ℂ) - (E + η * Complex.I))⁻¹ -
        conj (((lam : ℂ) - (E + η * Complex.I))⁻¹)) =
      ((η / ((lam - E) ^ 2 + η ^ 2) : ℝ) : ℂ) := by
  rw [Complex.sub_conj, Complex.inv_im]
  have hn : Complex.normSq ((lam : ℂ) - (E + η * Complex.I)) = (lam - E) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have him : ((lam : ℂ) - (E + η * Complex.I)).im = -η := by simp
  have hpos : 0 < (lam - E) ^ 2 + η ^ 2 := by positivity
  rw [hn, him]
  push_cast
  field_simp

/-- **Spectral form of `Im G`**: `Im G(E + iη) = U diag(η |λ - z|⁻²) U*`. -/
theorem imGreen_eq_spectral (E : ℝ) {η : ℝ} (hη : η ≠ 0) :
    imGreen H (E + η * Complex.I) = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => (specWeight hH E η l : ℂ))
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  set z : ℂ := E + η * Complex.I with hz
  have hz' : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp [hz] at this
    exact hη this.symm
  set d : n → ℂ := fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹ with hd
  have hG : green H z = U * diagonal d * star U := green_eq_spectral hH hz'
  have hGh : (green H z)ᴴ = U * diagonal (star d) * star U := by
    rw [hG, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star U), star_star,
      diagonal_conjTranspose, star_eq_conjTranspose, Matrix.mul_assoc]
  rw [imGreen, hGh, hG, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub,
    ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  congr 3
  funext l
  simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, hd, specWeight, hz,
    RCLike.star_def]
  exact two_I_inv_mul_sub_conj _ _ hη

/-- `Tr (Im G A Im G A) = ∑_{i,j} η² |λ_i - z|⁻² |λ_j - z|⁻² |ψ_i* A ψ_j|²` for Hermitian `A`:
the identity behind the second line of (2.14). -/
theorem trace_imGreen_mul_imGreen (E : ℝ) {η : ℝ} (hη : η ≠ 0) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    (imGreen H (E + η * Complex.I) * A * imGreen H (E + η * Complex.I) * A).trace =
      ((∑ i, ∑ j, specWeight hH E η i * specWeight hH E η j *
        ‖eigOverlap hH A i j‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := diagonal (fun l => (specWeight hH E η l : ℂ)) with hD
  set B : Matrix n n ℂ := star U * A * U with hB
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hBh : Bᴴ = B := by
    rw [hB, conjTranspose_mul, conjTranspose_mul, hA.eq, ← star_eq_conjTranspose (star U),
      star_star, star_eq_conjTranspose, Matrix.mul_assoc]
  have key : (U * D * star U * A * (U * D * star U) * A).trace = (D * B * D * B).trace := by
    have e : U * D * star U * A * (U * D * star U) * A
        = U * (D * B * D * (star U * A)) := by
      simp only [hB, Matrix.mul_assoc]
    rw [e, trace_mul_comm]
    have e2 : D * B * D * (star U * A) * U = D * B * D * B := by
      simp only [hB, Matrix.mul_assoc]
    rw [e2]
  have hentry : ∀ i, (D * B * D * B) i i
      = ∑ j, (specWeight hH E η i : ℂ) * B i j * (specWeight hH E η j : ℂ) * B j i := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hD, mul_diagonal, diagonal_mul]
  rw [imGreen_eq_spectral hH E hη, key, Matrix.trace]
  simp only [Matrix.diag, hentry]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : B j i = conj (B i j) := by
    have := congrFun (congrFun hBh j) i
    rw [conjTranspose_apply] at this
    rw [← this]; rfl
  rw [hji, eigOverlap_eq hH, ← hB, ← Complex.mul_conj' (B i j)]
  ring

/-- `η |λ - z|⁻² ≥ (2η)⁻¹` when `|λ - E| ≤ η`. -/
theorem specWeight_ge (E : ℝ) {η : ℝ} (hη : 0 < η) {l : n} (hl : |hH.eigenvalues l - E| ≤ η) :
    1 / (2 * η) ≤ specWeight hH E η l := by
  have hsq : (hH.eigenvalues l - E) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have hpos : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
  rw [specWeight, div_le_div_iff₀ (by positivity) hpos]
  nlinarith

theorem specWeight_nonneg (E : ℝ) {η : ℝ} (hη : 0 ≤ η) (l : n) : 0 ≤ specWeight hH E η l := by
  unfold specWeight; positivity

/-- **(2.14)**: `∑_{i,j} 1(λ_i, λ_j ∈ J_E) |ψ_i* A ψ_j|² ≤ 4 η² Tr (Im G A Im G A)`, with
`J_E = [E - η, E + η]` and `G = G(E + iη)` (first line: `1 ≤ 4 η⁴ |λ_i - z|⁻² |λ_j - z|⁻²` on
the window; second line: `trace_imGreen_mul_imGreen`). -/
theorem sum_window_le (E : ℝ) {η : ℝ} (hη : 0 < η) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ i, ∑ j, (if |hH.eigenvalues i - E| ≤ η ∧ |hH.eigenvalues j - E| ≤ η then
        ‖eigOverlap hH A i j‖ ^ 2 else 0) ≤
      4 * η ^ 2 *
        (imGreen H (E + η * Complex.I) * A * imGreen H (E + η * Complex.I) * A).trace.re := by
  rw [trace_imGreen_mul_imGreen hH E hη.ne' hA, Complex.ofReal_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw := specWeight_nonneg hH E hη.le
  have hb : 0 ≤ ‖eigOverlap hH A i j‖ ^ 2 := by positivity
  split_ifs with h
  · have hi := specWeight_ge hH E hη h.1
    have hj := specWeight_ge hH E hη h.2
    have h1 : 1 ≤ 4 * η ^ 2 * (specWeight hH E η i * specWeight hH E η j) := by
      have h2 : (1 / (2 * η)) * (1 / (2 * η)) ≤ specWeight hH E η i * specWeight hH E η j :=
        mul_le_mul hi hj (by positivity) (hw i)
      have h3 : 4 * η ^ 2 * ((1 / (2 * η)) * (1 / (2 * η))) = 1 := by field_simp; ring
      nlinarith
    nlinarith
  · have := hw i; have := hw j; positivity

/-- **(2.14), one pair**: for `λ_i, λ_j ∈ J_E`, `|ψ_i* A ψ_j|² ≤ 4 η² Tr (Im G A Im G A)`. -/
theorem sq_norm_eigOverlap_le (E : ℝ) {η : ℝ} (hη : 0 < η) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {i j : n} (hi : |hH.eigenvalues i - E| ≤ η) (hj : |hH.eigenvalues j - E| ≤ η) :
    ‖eigOverlap hH A i j‖ ^ 2 ≤
      4 * η ^ 2 *
        (imGreen H (E + η * Complex.I) * A * imGreen H (E + η * Complex.I) * A).trace.re := by
  refine le_trans ?_ (sum_window_le hH E hη hA)
  have hnn : ∀ i' j' : n, 0 ≤ (if |hH.eigenvalues i' - E| ≤ η ∧ |hH.eigenvalues j' - E| ≤ η then
      ‖eigOverlap hH A i' j'‖ ^ 2 else 0) := fun i' j' => by split_ifs <;> positivity
  have h1 := Finset.single_le_sum (f := fun j' => if |hH.eigenvalues i - E| ≤ η ∧
      |hH.eigenvalues j' - E| ≤ η then ‖eigOverlap hH A i j'‖ ^ 2 else 0)
    (fun j' _ => hnn i j') (Finset.mem_univ j)
  have h2 := Finset.single_le_sum (f := fun i' => ∑ j', if |hH.eigenvalues i' - E| ≤ η ∧
      |hH.eigenvalues j' - E| ≤ η then ‖eigOverlap hH A i' j'‖ ^ 2 else 0)
    (fun i' _ => Finset.sum_nonneg fun j' _ => hnn i' j') (Finset.mem_univ i)
  have e : (if |hH.eigenvalues i - E| ≤ η ∧ |hH.eigenvalues j - E| ≤ η then
      ‖eigOverlap hH A i j‖ ^ 2 else 0) = ‖eigOverlap hH A i j‖ ^ 2 := by simp [hi, hj]
  rw [← e]
  exact h1.trans h2

include hH in
/-- The trace `Tr (Im G A Im G A)` is real and nonnegative for Hermitian `A`. -/
theorem trace_imGreen_re_nonneg (E : ℝ) {η : ℝ} (hη : 0 < η) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    0 ≤ (imGreen H (E + η * Complex.I) * A * imGreen H (E + η * Complex.I) * A).trace.re := by
  rw [trace_imGreen_mul_imGreen hH E hη.ne' hA, Complex.ofReal_re]
  have hw := specWeight_nonneg hH E hη.le
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hw i) (hw j)) (by positivity)

/-- `ψ_k* diag(d) ψ_k = ∑_p d_p |ψ_k(p)|²`. -/
theorem eigOverlap_diagonal_self (d : n → ℂ) (k : n) :
    eigOverlap hH (diagonal d) k k = ∑ p, d p * ((‖hH.eigenvectorBasis k p‖ ^ 2 : ℝ) : ℂ) := by
  simp only [eigOverlap, dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  rw [← Complex.mul_conj']
  ring

/-- Eigenvectors are normalized: `∑_p |ψ_k(p)|² = 1`. -/
theorem sum_sq_norm_eigenvector (k : n) : ∑ p, ‖hH.eigenvectorBasis k p‖ ^ 2 = 1 := by
  have h := hH.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

end Spectral

/-! ### The trace algebra of (2.15) -/

section TraceAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `Tr (M* X M Y) = Tr (M Y M* X)`. -/
theorem trace_conjTranspose_mul_mul (M X Y : Matrix n n ℂ) :
    (Mᴴ * X * M * Y).trace = (M * Y * Mᴴ * X).trace := by
  rw [Matrix.mul_assoc (Mᴴ * X), trace_mul_comm, ← Matrix.mul_assoc]

omit [DecidableEq n] in
/-- `Tr (M* X M* Y) = conj Tr (M X M Y)` for Hermitian `X`, `Y`. -/
theorem trace_conjTranspose_mul_conjTranspose {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (M : Matrix n n ℂ) :
    (Mᴴ * X * Mᴴ * Y).trace = conj (M * X * M * Y).trace := by
  have h := trace_conjTranspose (M * X * M * Y)
  simp only [conjTranspose_mul, hX.eq, hY.eq] at h
  rw [RCLike.star_def] at h
  rw [← h, trace_mul_comm Y]
  simp only [Matrix.mul_assoc]

theorem two_I_inv_mul_self : (2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
  rw [← mul_inv, show (2 * Complex.I) * (2 * Complex.I) = -4 by
    ring_nf; rw [Complex.I_sq]; ring]
  norm_num

/-- **The first step of (2.15)**: with `G = G(z)`,
`Tr (Im G X Im G Y) = -¼ (Tr G X G Y - Tr G X G* Y - Tr G Y G* X + conj Tr G X G Y)` for
Hermitian `X`, `Y`. -/
theorem trace_imGreen_mul_imGreen_eq (H : Matrix n n ℂ) (z : ℂ) {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (imGreen H z * X * imGreen H z * Y).trace =
      -(1 / 4 : ℂ) * ((green H z * X * green H z * Y).trace -
        (green H z * X * (green H z)ᴴ * Y).trace - (green H z * Y * (green H z)ᴴ * X).trace +
        conj (green H z * X * green H z * Y).trace) := by
  set G := green H z
  have e : imGreen H z * X * imGreen H z * Y = ((2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹) •
      (G * X * G * Y - G * X * Gᴴ * Y - Gᴴ * X * G * Y + Gᴴ * X * Gᴴ * Y) := by
    have hI : imGreen H z = (2 * Complex.I)⁻¹ • (G - Gᴴ) := rfl
    rw [hI, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
      smul_smul]
    congr 1
    simp only [sub_mul, mul_sub]
    abel
  rw [e, trace_smul, trace_add, trace_sub, trace_sub, trace_conjTranspose_mul_mul,
    trace_conjTranspose_mul_conjTranspose hX hY, two_I_inv_mul_self, smul_eq_mul]

/-- Bilinearity: `Tr (Im G (X - X') Im G (Y - Y'))` in terms of `Tr (Im G · Im G ·)`. -/
theorem trace_imGreen_sub_sub (H : Matrix n n ℂ) (z : ℂ) (X X' Y Y' : Matrix n n ℂ) :
    (imGreen H z * (X - X') * imGreen H z * (Y - Y')).trace =
      (imGreen H z * X * imGreen H z * Y).trace - (imGreen H z * X * imGreen H z * Y').trace -
        (imGreen H z * X' * imGreen H z * Y).trace +
          (imGreen H z * X' * imGreen H z * Y').trace := by
  simp only [mul_sub, sub_mul, trace_sub]
  ring

/-- Bilinearity: `Tr (Im G A Im G A)` for `A = c ∑_p D_p`. -/
theorem trace_imGreen_smul_sum (H : Matrix n n ℂ) (z : ℂ) {ι : Type*} (P : Finset ι) (c : ℂ)
    (D : ι → Matrix n n ℂ) :
    (imGreen H z * (c • ∑ p ∈ P, D p) * imGreen H z * (c • ∑ p ∈ P, D p)).trace =
      c * c * ∑ p ∈ P, ∑ q ∈ P, (imGreen H z * D p * imGreen H z * D q).trace := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, Matrix.mul_sum,
    Matrix.sum_mul, trace_sum]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

end TraceAlgebra

/-! ### The observable `E_a - N⁻¹ I` and its averaged version -/

section Observable

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The QUE observable of (2.12)/(2.13): `|S|⁻¹ ∑_{a ∈ S} E_a - N⁻¹ I`, `N = L W` (for
`S = {a}` this is `E_a - N⁻¹ I` of (2.12)). -/
noncomputable def queObs (S : Finset (ZMod L)) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  (S.card : ℂ)⁻¹ • ∑ a ∈ S, Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)

omit [NeZero L] [NeZero W] in
theorem Eblk_isHermitian (a : ZMod L) : (Eblk L W a).IsHermitian := Eblk_conjTranspose L W a

omit [NeZero L] [NeZero W] in
theorem queObs_isHermitian (S : Finset (ZMod L)) : (queObs L W S).IsHermitian := by
  unfold queObs IsHermitian
  simp [conjTranspose_sum, Eblk_conjTranspose, conjTranspose_smul]

/-- **(2.15), the algebraic identity**:
`|S|⁻¹ ∑_{a ∈ S} E_a - N⁻¹ I = (|S| L)⁻¹ ∑_{a ∈ S} ∑_b (E_a - E_b)`
(for `S = {a}`: `E_a - N⁻¹ I = L⁻¹ ∑_b (E_a - E_b)`, the first line of (2.15)). -/
theorem queObs_eq {S : Finset (ZMod L)} (hS : S.Nonempty) :
    queObs L W S = ((S.card * L : ℕ) : ℂ)⁻¹ •
      ∑ p ∈ S ×ˢ (Finset.univ : Finset (ZMod L)), (Eblk L W p.1 - Eblk L W p.2) := by
  have hsum : ∑ p ∈ S ×ˢ (Finset.univ : Finset (ZMod L)), (Eblk L W p.1 - Eblk L W p.2) =
      (L : ℂ) • ∑ a ∈ S, Eblk L W a - (S.card : ℂ) • ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) := by
    rw [Finset.sum_product]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, sum_Eblk]
    rw [Finset.smul_sum]
    simp only [← Nat.cast_smul_eq_nsmul ℂ]
  have hS0 : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hS).ne'
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [hsum, queObs, smul_sub, smul_smul, smul_smul, smul_smul]
  have e1 : ((S.card * L : ℕ) : ℂ)⁻¹ * (L : ℂ) = (S.card : ℂ)⁻¹ := by push_cast; field_simp
  have e2 : ((S.card * L : ℕ) : ℂ)⁻¹ * (S.card : ℂ) * (W : ℂ)⁻¹ = ((L * W : ℕ) : ℂ)⁻¹ := by
    push_cast; field_simp
  rw [e1, e2]

omit [NeZero L] [NeZero W] in
theorem queObs_singleton (a : ZMod L) :
    queObs L W {a} = Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ) := by
  simp [queObs]

omit [NeZero L] [NeZero W] in
/-- `queObs S` is diagonal: `(|S|⁻¹ W⁻¹ 1(p.1 ∈ S) - N⁻¹)_p`. -/
theorem queObs_eq_diagonal (S : Finset (ZMod L)) :
    queObs L W S = diagonal (fun p => (S.card : ℂ)⁻¹ * (if p.1 ∈ S then (W : ℂ)⁻¹ else 0) -
      ((L * W : ℕ) : ℂ)⁻¹) := by
  ext p q
  simp only [queObs, Eblk, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, diagonal_apply,
    one_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp only [ite_true, mul_one]
    congr 2
    rw [Finset.sum_ite_eq]
  · simp [h]

end Observable

/-! ### (2.15): the expectation of `Tr (Im G A Im G A)` from (2.8), (2.9) -/

section Expectation

variable {L W : ℕ} [NeZero L]

/-- `Tr G E_x G E_y`, the loop of (2.9). -/
noncomputable def trGG (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (x y : ZMod L) :
    ℂ :=
  (green H z * Eblk L W x * green H z * Eblk L W y).trace

/-- `Tr G E_x G* E_y`, the loop of (2.8). -/
noncomputable def trGGs (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (x y : ZMod L) :
    ℂ :=
  (green H z * Eblk L W x * (green H z)ᴴ * Eblk L W y).trace

/-- `Tr Im G E_x Im G E_y`. -/
noncomputable def trImIm (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (x y : ZMod L) : ℂ :=
  (imGreen H z * Eblk L W x * imGreen H z * Eblk L W y).trace

theorem trImIm_eq (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (x y : ZMod L) :
    trImIm H z x y = -(1 / 4 : ℂ) * (trGG H z x y - trGGs H z x y - trGGs H z y x +
      conj (trGG H z x y)) :=
  trace_imGreen_mul_imGreen_eq H z (Eblk_isHermitian L W x) (Eblk_isHermitian L W y)

/-- `Tr (Im G A Im G A)` for `A = queObs S` as a combination of the `Tr Im G E_x Im G E_y`. -/
theorem trace_imGreen_queObs [NeZero W] (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    {S : Finset (ZMod L)} (hS : S.Nonempty) :
    (imGreen H z * queObs L W S * imGreen H z * queObs L W S).trace =
      ((S.card * L : ℕ) : ℂ)⁻¹ * ((S.card * L : ℕ) : ℂ)⁻¹ *
        ∑ p ∈ S ×ˢ (Finset.univ : Finset (ZMod L)), ∑ q ∈ S ×ˢ (Finset.univ : Finset (ZMod L)),
          (trImIm H z p.1 q.1 - trImIm H z p.1 q.2 - trImIm H z p.2 q.1 + trImIm H z p.2 q.2) := by
  rw [queObs_eq L W hS, trace_imGreen_smul_sum]
  simp only [trace_imGreen_sub_sub, trImIm]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

theorem integrable_trImIm (hGG : ∀ x y, Integrable (fun ω => trGG (H ω) z x y) P)
    (hGGs : ∀ x y, Integrable (fun ω => trGGs (H ω) z x y) P) (x y : ZMod L) :
    Integrable (fun ω => trImIm (H ω) z x y) P := by
  simp only [trImIm_eq]
  refine Integrable.const_mul ?_ _
  exact (((hGG x y).sub (hGGs x y)).sub (hGGs y x)).add
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp (hGG x y))

theorem integral_trImIm (hGG : ∀ x y, Integrable (fun ω => trGG (H ω) z x y) P)
    (hGGs : ∀ x y, Integrable (fun ω => trGGs (H ω) z x y) P) (x y : ZMod L) :
    ∫ ω, trImIm (H ω) z x y ∂P = -(1 / 4 : ℂ) * ((∫ ω, trGG (H ω) z x y ∂P) -
      (∫ ω, trGGs (H ω) z x y ∂P) - (∫ ω, trGGs (H ω) z y x ∂P) +
        conj (∫ ω, trGG (H ω) z x y ∂P)) := by
  simp only [trImIm_eq]
  rw [integral_const_mul, integral_add, integral_sub, integral_sub, integral_conj]
  · exact hGG x y
  · exact hGGs x y
  · exact (hGG x y).sub (hGGs x y)
  · exact hGGs y x
  · exact ((hGG x y).sub (hGGs x y)).sub (hGGs y x)
  · exact Complex.conjCLE.toContinuousLinearMap.integrable_comp (hGG x y)

/-- `|E_x - M_x - (E_y - M_y)| ≤ 2ε + δ` bookkeeping. -/
theorem norm_sub_le_of_approx {a b c d : ℂ} {ε δ : ℝ} (ha : ‖a - c‖ ≤ ε) (hb : ‖b - d‖ ≤ ε)
    (hcd : ‖c - d‖ ≤ δ) : ‖a - b‖ ≤ 2 * ε + δ := by
  have e : a - b = (a - c) - (b - d) + (c - d) := by ring
  rw [e]
  calc ‖(a - c) - (b - d) + (c - d)‖ ≤ ‖(a - c) - (b - d)‖ + ‖c - d‖ := norm_add_le _ _
    _ ≤ (‖a - c‖ + ‖b - d‖) + ‖c - d‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 2 * ε + δ := by linarith

/-- **(2.15), second line**: if `E Tr G E_x G E_y` and `E Tr G E_x G* E_y` are `ε`-close to
main terms `M^{++}_{xy}`, `M^{+-}_{xy}` whose oscillation over `(x, y)` is at most `δ`, then
`|E Tr Im G E_x Im G E_y - E Tr Im G E_{x'} Im G E_{y'}| ≤ 2ε + δ`. -/
theorem norm_integral_trImIm_sub_le (hGG : ∀ x y, Integrable (fun ω => trGG (H ω) z x y) P)
    (hGGs : ∀ x y, Integrable (fun ω => trGGs (H ω) z x y) P) {ε δ : ℝ}
    {Mpp Mpm : ZMod L → ZMod L → ℂ}
    (hpp : ∀ x y, ‖(∫ ω, trGG (H ω) z x y ∂P) - Mpp x y‖ ≤ ε)
    (hpm : ∀ x y, ‖(∫ ω, trGGs (H ω) z x y ∂P) - Mpm x y‖ ≤ ε)
    (hMpp : ∀ x y x' y', ‖Mpp x y - Mpp x' y'‖ ≤ δ)
    (hMpm : ∀ x y x' y', ‖Mpm x y - Mpm x' y'‖ ≤ δ) (x y x' y' : ZMod L) :
    ‖(∫ ω, trImIm (H ω) z x y ∂P) - ∫ ω, trImIm (H ω) z x' y' ∂P‖ ≤ 2 * ε + δ := by
  rw [integral_trImIm hGG hGGs, integral_trImIm hGG hGGs]
  set a := ∫ ω, trGG (H ω) z x y ∂P
  set a' := ∫ ω, trGG (H ω) z x' y' ∂P
  set b := ∫ ω, trGGs (H ω) z x y ∂P
  set b' := ∫ ω, trGGs (H ω) z x' y' ∂P
  set c := ∫ ω, trGGs (H ω) z y x ∂P
  set c' := ∫ ω, trGGs (H ω) z y' x' ∂P
  have h1 : ‖a - a'‖ ≤ 2 * ε + δ := norm_sub_le_of_approx (hpp x y) (hpp x' y') (hMpp x y x' y')
  have h2 : ‖b - b'‖ ≤ 2 * ε + δ := norm_sub_le_of_approx (hpm x y) (hpm x' y') (hMpm x y x' y')
  have h3 : ‖c - c'‖ ≤ 2 * ε + δ := norm_sub_le_of_approx (hpm y x) (hpm y' x') (hMpm y x y' x')
  have h4 : ‖conj a - conj a'‖ ≤ 2 * ε + δ := by rw [← map_sub, Complex.norm_conj]; exact h1
  have e : -(1 / 4 : ℂ) * (a - b - c + conj a) - -(1 / 4 : ℂ) * (a' - b' - c' + conj a') =
      -(1 / 4 : ℂ) * ((a - a') - (b - b') - (c - c') + (conj a - conj a')) := by ring
  rw [e, norm_mul]
  have hq : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hq]
  have h5 : ‖(a - a') - (b - b') - (c - c') + (conj a - conj a')‖ ≤ 4 * (2 * ε + δ) := by
    calc _ ≤ ‖(a - a') - (b - b') - (c - c')‖ + ‖conj a - conj a'‖ := norm_add_le _ _
      _ ≤ (‖(a - a') - (b - b')‖ + ‖c - c'‖) + ‖conj a - conj a'‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ((‖a - a'‖ + ‖b - b'‖) + ‖c - c'‖) + ‖conj a - conj a'‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ 4 * (2 * ε + δ) := by linarith
  linarith

/-- The random variable `Tr (Im G A Im G A)`, `A = queObs S`, is integrable. -/
theorem integrable_trace_imGreen_queObs [NeZero W]
    (hGG : ∀ x y, Integrable (fun ω => trGG (H ω) z x y) P)
    (hGGs : ∀ x y, Integrable (fun ω => trGGs (H ω) z x y) P) {S : Finset (ZMod L)}
    (hS : S.Nonempty) :
    Integrable (fun ω => (imGreen (H ω) z * queObs L W S * imGreen (H ω) z *
      queObs L W S).trace) P := by
  simp only [trace_imGreen_queObs _ z hS]
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => ?_
  have hI := integrable_trImIm hGG hGGs
  exact (((hI _ _).sub (hI _ _)).sub (hI _ _)).add (hI _ _)

/-- **(2.15)**: under the hypotheses of `norm_integral_trImIm_sub_le`,
`|E Tr (Im G A Im G A)| ≤ 2 (2ε + δ)` for `A = |S|⁻¹ ∑_{a ∈ S} E_a - N⁻¹ I`. -/
theorem norm_integral_trace_imGreen_queObs_le [NeZero W]
    (hGG : ∀ x y, Integrable (fun ω => trGG (H ω) z x y) P)
    (hGGs : ∀ x y, Integrable (fun ω => trGGs (H ω) z x y) P) {ε δ : ℝ}
    {Mpp Mpm : ZMod L → ZMod L → ℂ}
    (hpp : ∀ x y, ‖(∫ ω, trGG (H ω) z x y ∂P) - Mpp x y‖ ≤ ε)
    (hpm : ∀ x y, ‖(∫ ω, trGGs (H ω) z x y ∂P) - Mpm x y‖ ≤ ε)
    (hMpp : ∀ x y x' y', ‖Mpp x y - Mpp x' y'‖ ≤ δ)
    (hMpm : ∀ x y x' y', ‖Mpm x y - Mpm x' y'‖ ≤ δ) {S : Finset (ZMod L)} (hS : S.Nonempty) :
    ‖∫ ω, (imGreen (H ω) z * queObs L W S * imGreen (H ω) z * queObs L W S).trace ∂P‖ ≤
      2 * (2 * ε + δ) := by
  have hI := integrable_trImIm hGG hGGs
  have hB := norm_integral_trImIm_sub_le hGG hGGs hpp hpm hMpp hMpm
  set Q := S ×ˢ (Finset.univ : Finset (ZMod L)) with hQ
  have hQcard : (Q.card : ℝ) = ((S.card * L : ℕ) : ℝ) := by
    rw [hQ, Finset.card_product, Finset.card_univ, ZMod.card]
  have hQpos : (0 : ℝ) < Q.card := by
    rw [hQcard]; exact_mod_cast Nat.mul_pos (Finset.card_pos.2 hS) (NeZero.pos L)
  have hF : ∀ p q : ZMod L × ZMod L, Integrable (fun ω => trImIm (H ω) z p.1 q.1 -
      trImIm (H ω) z p.1 q.2 - trImIm (H ω) z p.2 q.1 + trImIm (H ω) z p.2 q.2) P :=
    fun p q => (((hI _ _).sub (hI _ _)).sub (hI _ _)).add (hI _ _)
  simp only [trace_imGreen_queObs _ z hS, ← hQ]
  rw [integral_const_mul]
  have hint : ∫ ω, ∑ p ∈ Q, ∑ q ∈ Q, (trImIm (H ω) z p.1 q.1 - trImIm (H ω) z p.1 q.2 -
      trImIm (H ω) z p.2 q.1 + trImIm (H ω) z p.2 q.2) ∂P =
      ∑ p ∈ Q, ∑ q ∈ Q, ∫ ω, (trImIm (H ω) z p.1 q.1 - trImIm (H ω) z p.1 q.2 -
      trImIm (H ω) z p.2 q.1 + trImIm (H ω) z p.2 q.2) ∂P := by
    rw [integral_finsetSum Q (f := fun p ω => ∑ q ∈ Q, (trImIm (H ω) z p.1 q.1 -
      trImIm (H ω) z p.1 q.2 - trImIm (H ω) z p.2 q.1 + trImIm (H ω) z p.2 q.2))
      (fun p _ => integrable_finsetSum Q fun q _ => hF p q)]
    exact Finset.sum_congr rfl fun p _ => integral_finsetSum Q (fun q _ => hF p q)
  rw [hint]
  have hterm : ∀ p q : ZMod L × ZMod L,
      ‖∫ ω, (trImIm (H ω) z p.1 q.1 - trImIm (H ω) z p.1 q.2 - trImIm (H ω) z p.2 q.1 +
        trImIm (H ω) z p.2 q.2) ∂P‖ ≤ 2 * (2 * ε + δ) := by
    intro p q
    rw [integral_add _ (hI _ _), integral_sub _ (hI _ _), integral_sub (hI _ _) (hI _ _)]
    · have e : (∫ ω, trImIm (H ω) z p.1 q.1 ∂P) - (∫ ω, trImIm (H ω) z p.1 q.2 ∂P) -
          (∫ ω, trImIm (H ω) z p.2 q.1 ∂P) + (∫ ω, trImIm (H ω) z p.2 q.2 ∂P) =
          ((∫ ω, trImIm (H ω) z p.1 q.1 ∂P) - (∫ ω, trImIm (H ω) z p.1 q.2 ∂P)) -
          ((∫ ω, trImIm (H ω) z p.2 q.1 ∂P) - (∫ ω, trImIm (H ω) z p.2 q.2 ∂P)) := by ring
      rw [e]
      calc _ ≤ ‖(∫ ω, trImIm (H ω) z p.1 q.1 ∂P) - (∫ ω, trImIm (H ω) z p.1 q.2 ∂P)‖ +
            ‖(∫ ω, trImIm (H ω) z p.2 q.1 ∂P) - (∫ ω, trImIm (H ω) z p.2 q.2 ∂P)‖ :=
            norm_sub_le _ _
        _ ≤ (2 * ε + δ) + (2 * ε + δ) := add_le_add (hB _ _ _ _) (hB _ _ _ _)
        _ = 2 * (2 * ε + δ) := by ring
    · exact (hI _ _).sub (hI _ _)
    · exact ((hI _ _).sub (hI _ _)).sub (hI _ _)
  rw [norm_mul]
  have hc : ‖((S.card * L : ℕ) : ℂ)⁻¹ * ((S.card * L : ℕ) : ℂ)⁻¹‖ =
      ((Q.card : ℝ) * Q.card)⁻¹ := by
    rw [hQcard, norm_mul, norm_inv, Complex.norm_natCast, mul_inv]
  rw [hc]
  calc ((Q.card : ℝ) * Q.card)⁻¹ * ‖∑ p ∈ Q, ∑ q ∈ Q, ∫ ω, (trImIm (H ω) z p.1 q.1 -
          trImIm (H ω) z p.1 q.2 - trImIm (H ω) z p.2 q.1 + trImIm (H ω) z p.2 q.2) ∂P‖
      ≤ ((Q.card : ℝ) * Q.card)⁻¹ * ∑ p ∈ Q, ∑ q ∈ Q, 2 * (2 * ε + δ) := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hterm p q)
    _ = 2 * (2 * ε + δ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp

end Expectation

/-! ### The oscillation of `Θ_ξ` (Lemma 2.14 as used in (2.16)) -/

section Oscillation

variable (L : ℕ) [NeZero L] {ξ : ℂ}

theorem Theta_apply_eq_sub_zero (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) (a b : ZMod L) :
    Theta L ξ a b = Theta L ξ (a - b) 0 := by
  have h := Theta_apply_add_right L hL hξ (a - b) 0 b
  rw [sub_add_cancel, zero_add] at h
  exact h

/-- `L / (ℓ̂ s) ≤ L + 1/s` for `ℓ̂ = min(1/s, L)`, `s > 0`. -/
theorem div_ellHat_mul_le {s : ℝ} (hs : 0 < s) :
    (L : ℝ) / (min (1 / s) (L : ℝ) * s) ≤ L + 1 / s := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  rcases min_cases (1 / s) (L : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h, one_div_mul_cancel hs.ne', div_one]
    have : 0 < 1 / s := by positivity
    linarith
  · rw [h, div_mul_eq_div_div, div_self hL0.ne']
    have : 0 ≤ (L : ℝ) := hL0.le
    linarith

/-- **The oscillation of `Θ_ξ`**: `|(Θ_ξ)_{ab} - (Θ_ξ)_{a'b'}| ≤ 288 (L + |1-ξ|^{-1/2})`,
from (2.53) (`norm_Theta_sub_shift_le_complex`) by telescoping along `ZMod L`. -/
theorem norm_Theta_sub_Theta_le (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (a b a' b' : ZMod L) :
    ‖Theta L ξ a b - Theta L ξ a' b'‖ ≤ 288 * (L + 1 / Real.sqrt ‖1 - ξ‖) := by
  set K : ℝ := 144 / (ellHat L ξ * Real.sqrt ‖1 - ξ‖) with hK
  set f : ZMod L → ℂ := fun u => Theta L ξ u 0 with hf
  have hstep : ∀ u : ZMod L, ‖f u - f (u - 1)‖ ≤ K := by
    intro u
    have h := norm_Theta_sub_shift_le_complex L hL hξ0 hξ u 0
    rw [zero_add, Theta_apply_eq_sub_zero L hL hξ u 1] at h
    exact h
  have hind : ∀ k : ℕ, ‖f (k : ZMod L) - f 0‖ ≤ k * K := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : f ((k + 1 : ℕ) : ZMod L) - f 0 =
          (f ((k + 1 : ℕ) : ZMod L) - f ((k + 1 : ℕ) - 1 : ZMod L)) + (f (k : ZMod L) - f 0) := by
        push_cast; ring_nf
      rw [e]
      calc _ ≤ ‖f ((k + 1 : ℕ) : ZMod L) - f ((k + 1 : ℕ) - 1 : ZMod L)‖ +
            ‖f (k : ZMod L) - f 0‖ := norm_add_le _ _
        _ ≤ K + k * K := add_le_add (hstep _) ih
        _ = ((k + 1 : ℕ) : ℝ) * K := by push_cast; ring
  have hK0 : 0 ≤ K := by
    have := half_le_ellHat L hL hξ
    have := Real.sqrt_nonneg ‖1 - ξ‖
    rw [hK]; positivity
  have hall : ∀ u : ZMod L, ‖f u - f 0‖ ≤ L * K := by
    intro u
    have h := hind u.val
    rw [ZMod.natCast_zmod_val] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hK0)
    exact_mod_cast (ZMod.val_lt u).le
  have hLK : (L : ℝ) * K ≤ 144 * (L + 1 / Real.sqrt ‖1 - ξ‖) := by
    have hne : (1 : ℂ) - ξ ≠ 0 := one_sub_ne_zero hξ
    have hs : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hne)
    have h := div_ellHat_mul_le L hs
    have e : (L : ℝ) * K = 144 * ((L : ℝ) / (ellHat L ξ * Real.sqrt ‖1 - ξ‖)) := by
      rw [hK]; ring
    rw [e, ellHat]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  rw [Theta_apply_eq_sub_zero L hL hξ a b, Theta_apply_eq_sub_zero L hL hξ a' b']
  have e : Theta L ξ (a - b) 0 - Theta L ξ (a' - b') 0 =
      (f (a - b) - f 0) - (f (a' - b') - f 0) := by
    simp only [hf]; ring
  rw [e]
  calc _ ≤ ‖f (a - b) - f 0‖ + ‖f (a' - b') - f 0‖ := norm_sub_le _ _
    _ ≤ L * K + L * K := add_le_add (hall _) (hall _)
    _ ≤ 288 * (L + 1 / Real.sqrt ‖1 - ξ‖) := by linarith

/-- The same for `ξ Θ_ξ` (the main terms of (2.8), (2.9) carry the factor `ξ`). -/
theorem norm_mul_Theta_sub_le (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ < 1) (a b a' b' : ZMod L) :
    ‖ξ * Theta L ξ a b - ξ * Theta L ξ a' b'‖ ≤ 288 * (L + 1 / Real.sqrt ‖1 - ξ‖) := by
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hξ.le).trans
    (norm_Theta_sub_Theta_le L hL hξ0 hξ _ _ _ _)

/-- The oscillation of `ξ Θ̃_ξ` for the variance profile `S̃^(B)` of §7.2: the zero mode drops
out (`ThetaTilde_sub_ThetaTilde`) and `|1 - ξ(1-ζ)| ≥ |1-ξ|/2` (`zeroMode_setup`). -/
theorem norm_mul_ThetaTilde_sub_le (hL : 3 ≤ L) (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ ≤ 1) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ ≤ 1 / 2) (hζξ : ζ ≤ ‖1 - ξ‖) (a b a' b' : ZMod L) :
    ‖ξ * ThetaTilde L ζ ξ a b - ξ * ThetaTilde L ζ ξ a' b'‖ ≤
      576 * (L + 1 / Real.sqrt ‖1 - ξ‖) := by
  obtain ⟨hT, hξ1, ha, hlo, -, -⟩ := zeroMode_setup (L := L) hξ hζ0 hζ1 hζξ
  have hT0 : ξ * (1 - (ζ : ℂ)) ≠ 0 := by
    refine mul_ne_zero hξ0 ?_
    rw [sub_ne_zero]
    intro h
    have : (ζ : ℝ) = 1 := by exact_mod_cast h.symm
    linarith
  rw [← mul_sub, norm_mul, ThetaTilde_sub_ThetaTilde L hL hT hξ1]
  have h1 := norm_Theta_sub_Theta_le L hL hT0 hT a b a' b'
  have hs : 0 < Real.sqrt ‖1 - ξ‖ := Real.sqrt_pos.2 ha
  have hsT : Real.sqrt ‖1 - ξ‖ ≤ 2 * Real.sqrt ‖1 - ξ * (1 - (ζ : ℂ))‖ :=
    sqrt_le_two_mul_sqrt (by linarith)
  have hinv : 1 / Real.sqrt ‖1 - ξ * (1 - (ζ : ℂ))‖ ≤ 2 * (1 / Real.sqrt ‖1 - ξ‖) := by
    have hsT0 : 0 < Real.sqrt ‖1 - ξ * (1 - (ζ : ℂ))‖ := by linarith
    rw [div_le_iff₀ hsT0]
    field_simp
    linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hpos : 0 ≤ 1 / Real.sqrt ‖1 - ξ‖ := by positivity
  calc ‖ξ‖ * ‖Theta L (ξ * (1 - ↑ζ)) a b - Theta L (ξ * (1 - ↑ζ)) a' b'‖
      ≤ 1 * (288 * (L + 1 / Real.sqrt ‖1 - ξ * (1 - (ζ : ℂ))‖)) :=
        mul_le_mul hξ h1 (norm_nonneg _) zero_le_one
    _ ≤ 576 * (L + 1 / Real.sqrt ‖1 - ξ‖) := by nlinarith

end Oscillation

/-- `N ψ_k* (|S|⁻¹ ∑_{a ∈ S} E_a - N⁻¹) ψ_k
  = N (|S| W)⁻¹ (∑_{a ∈ S} ∑_{x ∈ I_a} |ψ_k(x)|² - |S| W / N)`,
the link between (2.13) and the observable of (2.12). -/
theorem eigOverlap_queObs_self {L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) {S : Finset (ZMod L)}
    (hS : S.Nonempty) (k : ZMod L × Fin W) :
    eigOverlap hH (queObs L W S) k k = (((S.card * W : ℕ) : ℝ)⁻¹ *
      (∑ a ∈ S, ∑ x : Fin W, ‖hH.eigenvectorBasis k (a, x)‖ ^ 2 -
        (S.card * W : ℕ) / ((L * W : ℕ) : ℝ)) : ℝ) := by
  rw [queObs_eq_diagonal, eigOverlap_diagonal_self]
  have hsum := sum_sq_norm_eigenvector hH k
  have hS0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hS).ne'
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  have hsplit : ∑ p : ZMod L × Fin W, (S.card : ℂ)⁻¹ * (if p.1 ∈ S then (W : ℂ)⁻¹ else 0) *
      ((‖hH.eigenvectorBasis k p‖ ^ 2 : ℝ) : ℂ) =
      (((S.card * W : ℕ) : ℝ)⁻¹ *
        ∑ a ∈ S, ∑ x : Fin W, ‖hH.eigenvectorBasis k (a, x)‖ ^ 2 : ℝ) := by
    rw [Fintype.sum_prod_type]
    push_cast
    rw [Finset.mul_sum]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsplit, ← Finset.mul_sum]
  have h1 : ∑ p : ZMod L × Fin W, ((‖hH.eigenvectorBasis k p‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  rw [h1]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hS0' : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS0
  have hW0' : (W : ℂ) ≠ 0 := by exact_mod_cast hW0
  push_cast
  field_simp

/-! ### Theorem 2.5 at a single `N`: (2.14) + Markov -/

section SingleN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {L W : ℕ} [NeZero L] [NeZero W]
  {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

/-- **The failure event of (2.12)/(2.13)**: there are eigenvalues `λ_i, λ_j ∈ J_E = [E-η, E+η]`
with `|N ψ_i* A ψ_j|² ≥ ε`, `A = |S|⁻¹ ∑_{a ∈ S} E_a - N⁻¹ I`, `N = L W`. -/
def queBad (hH : ∀ ω, (H ω).IsHermitian) (S : Finset (ZMod L)) (E η ε : ℝ) : Set Ω :=
  {ω | ∃ i j, |(hH ω).eigenvalues i - E| ≤ η ∧ |(hH ω).eigenvalues j - E| ≤ η ∧
    ε ≤ ‖((L * W : ℕ) : ℂ) * eigOverlap (hH ω) (queObs L W S) i j‖ ^ 2}

omit [NeZero W] in
/-- **(2.14) + Markov**: `P(max_{λ_i, λ_j ∈ J_E} |N ψ_i* A ψ_j|² ≥ ε)
≤ 4 η² N² |E Tr (Im G A Im G A)| / ε`. -/
theorem measure_queBad_le [IsFiniteMeasure P] (hH : ∀ ω, (H ω).IsHermitian)
    (S : Finset (ZMod L)) (E : ℝ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hint : Integrable (fun ω => (imGreen (H ω) (E + η * Complex.I) * queObs L W S *
      imGreen (H ω) (E + η * Complex.I) * queObs L W S).trace) P) :
    P (queBad hH S E η ε) ≤ ENNReal.ofReal (4 * η ^ 2 * ((L * W : ℕ) : ℝ) ^ 2 *
      ‖∫ ω, (imGreen (H ω) (E + η * Complex.I) * queObs L W S *
        imGreen (H ω) (E + η * Complex.I) * queObs L W S).trace ∂P‖ / ε) := by
  set A := queObs L W S
  have hA : A.IsHermitian := queObs_isHermitian L W S
  set Nn : ℝ := ((L * W : ℕ) : ℝ) with hNn
  set X : Ω → ℝ := fun ω => 4 * η ^ 2 * Nn ^ 2 *
    (imGreen (H ω) (E + η * Complex.I) * A * imGreen (H ω) (E + η * Complex.I) * A).trace.re
    with hX
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => by
    have := trace_imGreen_re_nonneg (hH ω) E hη hA
    simp only [hX]; positivity
  have hXint : Integrable X P := (hint.re).const_mul _
  have hsub : queBad hH S E η ε ⊆ {ω | ε ≤ X ω} := by
    rintro ω ⟨i, j, hi, hj, hij⟩
    have h := sq_norm_eigOverlap_le (hH ω) E hη hA hi hj
    simp only [Set.mem_ofPred_eq, hX]
    refine hij.trans ?_
    rw [norm_mul, mul_pow, Complex.norm_natCast, ← hNn]
    have : 0 ≤ Nn ^ 2 := sq_nonneg _
    nlinarith
  have hM := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hX0) hXint ε
  have hIX : ∫ ω, X ω ∂P ≤ 4 * η ^ 2 * Nn ^ 2 *
      ‖∫ ω, (imGreen (H ω) (E + η * Complex.I) * A * imGreen (H ω) (E + η * Complex.I) *
        A).trace ∂P‖ := by
    simp only [hX]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := integral_re (𝕜 := ℂ) hint
    simp only [RCLike.re_to_complex] at this
    rw [this]
    exact Complex.re_le_norm _
  calc P (queBad hH S E η ε) ≤ P {ω | ε ≤ X ω} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | ε ≤ X ω}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hε, mul_comm]
        exact hM.trans hIX

/-- **Theorem 2.5 at a single `N`, from (2.8), (2.9)**: if the loops `E Tr G E_x G E_y`,
`E Tr G E_x G* E_y` are `ε₀`-close to main terms `W⁻¹ ξ Θ(ξ)_{xy}` whose oscillation is at most
`δ`, then `P(max_{λ_i, λ_j ∈ J_E} |N ψ_i* A ψ_j|² ≥ ε) ≤ 8 η² N² (2ε₀ + W⁻¹ δ) / ε`. -/
theorem measure_queBad_le_of_approx [IsFiniteMeasure P] (hH : ∀ ω, (H ω).IsHermitian)
    {S : Finset (ZMod L)} (hS : S.Nonempty) (E : ℝ) {η ε ε₀ δ : ℝ} (hη : 0 < η) (hε : 0 < ε)
    {Mpp Mpm : ZMod L → ZMod L → ℂ}
    (hGG : ∀ x y, Integrable (fun ω => trGG (H ω) (E + η * Complex.I) x y) P)
    (hGGs : ∀ x y, Integrable (fun ω => trGGs (H ω) (E + η * Complex.I) x y) P)
    (hpp : ∀ x y, ‖(∫ ω, trGG (H ω) (E + η * Complex.I) x y ∂P) - (W : ℂ)⁻¹ * Mpp x y‖ ≤ ε₀)
    (hpm : ∀ x y, ‖(∫ ω, trGGs (H ω) (E + η * Complex.I) x y ∂P) - (W : ℂ)⁻¹ * Mpm x y‖ ≤ ε₀)
    (hMpp : ∀ x y x' y', ‖Mpp x y - Mpp x' y'‖ ≤ δ)
    (hMpm : ∀ x y x' y', ‖Mpm x y - Mpm x' y'‖ ≤ δ) :
    P (queBad hH S E η ε) ≤ ENNReal.ofReal (8 * η ^ 2 * ((L * W : ℕ) : ℝ) ^ 2 *
      (2 * ε₀ + (W : ℝ)⁻¹ * δ) / ε) := by
  have hW : ∀ x y x' y', ‖(W : ℂ)⁻¹ * Mpp x y - (W : ℂ)⁻¹ * Mpp x' y'‖ ≤ (W : ℝ)⁻¹ * δ := by
    intro x y x' y'
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hMpp x y x' y') (by positivity)
  have hW' : ∀ x y x' y', ‖(W : ℂ)⁻¹ * Mpm x y - (W : ℂ)⁻¹ * Mpm x' y'‖ ≤ (W : ℝ)⁻¹ * δ := by
    intro x y x' y'
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hMpm x y x' y') (by positivity)
  have h1 := norm_integral_trace_imGreen_queObs_le hGG hGGs hpp hpm hW hW' hS
  refine (measure_queBad_le hH S E hη hε
    (integrable_trace_imGreen_queObs hGG hGGs hS)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_div_iff_of_pos_right hε]
  have : 0 ≤ 4 * η ^ 2 * ((L * W : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

end SingleN

/-! ### The scale `η = N^{-1-τ*} (W²/N)^{1/3}` of Theorem 2.5 and the arithmetic of (2.17) -/

section Scale

/-- **The spectral scale of Theorem 2.5**: `η = N^{-1-τ*} (W²/N)^{1/3}`; `J_E = [E - η, E + η]`. -/
noncomputable def queEta (N W τ : ℝ) : ℝ := N ^ (-1 - τ) * (W ^ 2 / N) ^ ((1 : ℝ) / 3)

variable {N W τ : ℝ}

theorem queEta_pos (hN : 0 < N) (hW : 0 < W) : 0 < queEta N W τ := by
  unfold queEta; positivity

theorem rpow_pow_three {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 3 = x ^ (3 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

theorem queEta_cube (hN : 0 < N) (hW : 0 < W) :
    queEta N W τ ^ 3 = N ^ (-3 - 3 * τ) * (W ^ 2 / N) := by
  unfold queEta
  rw [mul_pow, rpow_pow_three hN.le, rpow_pow_three (by positivity)]
  congr 1
  · congr 1; ring
  · rw [show (3 : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one]

theorem rpow_neg_le_one (hN : 1 ≤ N) {a : ℝ} (ha : 0 ≤ a) : N ^ (-a) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- `η ≤ 1`. -/
theorem queEta_le_one (hN : 1 ≤ N) (hW : 0 < W) (hWN : W ≤ N) (hτ : 0 ≤ τ) :
    queEta N W τ ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  have h3 : queEta N W τ ^ 3 ≤ 1 := by
    rw [queEta_cube hN0 hW]
    have h1 : W ^ 2 / N ≤ N := by
      rw [div_le_iff₀ hN0]; nlinarith
    have h2 : N ^ (-3 - 3 * τ) * N = N ^ (-(2 + 3 * τ)) := by
      rw [show -(2 + 3 * τ) = (-3 - 3 * τ) + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
    calc N ^ (-3 - 3 * τ) * (W ^ 2 / N) ≤ N ^ (-3 - 3 * τ) * N :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 := by rw [h2]; exact rpow_neg_le_one hN (by positivity)
  by_contra h
  push Not at h
  have : 1 < queEta N W τ ^ 3 := one_lt_pow₀ h (by norm_num)
  linarith

/-- `ℓ(z) = L`: `L = N/W ≤ η^{-1/2}` (the first claim after (2.15)). -/
theorem div_le_inv_sqrt_queEta (hN : 1 ≤ N) (hW : 0 < W) (hWN : N ≤ W ^ 2) (hτ : 0 ≤ τ) :
    N / W ≤ 1 / Real.sqrt (queEta N W τ) := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  have hs := Real.sqrt_pos.2 hη
  rw [le_div_iff₀ hs]
  -- square: `(N/W)² η ≤ 1`, cube: `(N/W)⁶ η³ ≤ 1`
  have h6 : ((N / W) ^ 2 * queEta N W τ) ^ 3 ≤ 1 := by
    rw [mul_pow, queEta_cube hN0 hW]
    have hp : N ^ (-3 - 3 * τ) = N ^ (-(3 * τ)) * N⁻¹ ^ 3 := by
      rw [show -3 - 3 * τ = -(3 * τ) + (-3 : ℝ) by ring, Real.rpow_add hN0,
        show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, inv_pow, _root_.zpow_neg,
        ← zpow_natCast]
      rfl
    rw [hp]
    have hq := rpow_neg_le_one hN (a := 3 * τ) (by positivity)
    have hq0 : 0 ≤ N ^ (-(3 * τ)) := by positivity
    have hkey : ((N / W) ^ 2) ^ 3 * (N⁻¹ ^ 3 * (W ^ 2 / N)) ≤ 1 := by
      rw [show ((N / W) ^ 2) ^ 3 * (N⁻¹ ^ 3 * (W ^ 2 / N)) = N ^ 2 / (W ^ 2) ^ 2 by
        field_simp]
      rw [div_le_one (by positivity)]
      nlinarith
    calc ((N / W) ^ 2) ^ 3 * (N ^ (-(3 * τ)) * N⁻¹ ^ 3 * (W ^ 2 / N))
        = N ^ (-(3 * τ)) * (((N / W) ^ 2) ^ 3 * (N⁻¹ ^ 3 * (W ^ 2 / N))) := by ring
      _ ≤ 1 * 1 := mul_le_mul hq hkey (by positivity) zero_le_one
      _ = 1 := by ring
  have h2 : (N / W) ^ 2 * queEta N W τ ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < ((N / W) ^ 2 * queEta N W τ) ^ 3 := one_lt_pow₀ h (by norm_num)
    linarith
  have hsq : Real.sqrt (queEta N W τ) ^ 2 = queEta N W τ := Real.sq_sqrt hη.le
  have hNW : 0 ≤ N / W := by positivity
  nlinarith [Real.sqrt_nonneg (queEta N W τ)]

theorem pow_three_le_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 3 ≤ b ^ 3 ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb (by norm_num)

/-- `(N η)⁻¹ ≤ N^{τ - 2c/3}` when `W² ≥ N^{1+2c}` (i.e. (2.2) `W ≥ N^{1/2+c}`). -/
theorem inv_mul_queEta_le (hN : 1 ≤ N) (hW : 0 < W) {c : ℝ} (hWc : N ^ (1 + 2 * c) ≤ W ^ 2) :
    (N * queEta N W τ)⁻¹ ≤ N ^ (τ - 2 * c / 3) := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  have hcube : N ^ (2 * c - 3 * τ) ≤ (N * queEta N W τ) ^ 3 := by
    rw [mul_pow, queEta_cube hN0 hW]
    have e1 : N ^ 3 * (N ^ (-3 - 3 * τ) * (W ^ 2 / N)) = N ^ (-(3 * τ)) * (W ^ 2 / N) := by
      rw [show (-3 - 3 * τ) = -(3 * τ) + (-3 : ℝ) by ring, Real.rpow_add hN0]
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      field_simp
    rw [e1]
    have e2 : N ^ (2 * c - 3 * τ) = N ^ (-(3 * τ)) * (N ^ (1 + 2 * c) / N) := by
      rw [show 2 * c - 3 * τ = -(3 * τ) + ((1 + 2 * c) + (-1 : ℝ)) by ring, Real.rpow_add hN0,
        Real.rpow_add hN0, Real.rpow_neg_one, div_eq_mul_inv]
    rw [e2]
    gcongr
  have hbase : N ^ ((2 * c - 3 * τ) / 3) ≤ N * queEta N W τ := by
    rw [← pow_three_le_iff (by positivity) (by positivity), rpow_pow_three hN0.le]
    rw [show 3 * ((2 * c - 3 * τ) / 3) = 2 * c - 3 * τ by ring]
    exact hcube
  calc (N * queEta N W τ)⁻¹ ≤ (N ^ ((2 * c - 3 * τ) / 3))⁻¹ :=
        inv_anti₀ (by positivity) hbase
    _ = N ^ (τ - 2 * c / 3) := by
        rw [← Real.rpow_neg hN0.le]; congr 1; ring

/-- `N² η² L / W = N³ η² / W² ≤ N^{-2τ}` when `N ≤ W²` (the `L` part of the second term of
(2.17), via `|Θ_{ab} - Θ_{a'b'}| ≲ L + |1-ξ|^{-1/2}`). -/
theorem cube_mul_queEta_sq_le (hN : 1 ≤ N) (hW : 0 < W) (hWN : N ≤ W ^ 2) :
    N ^ 3 * queEta N W τ ^ 2 / W ^ 2 ≤ N ^ (-(2 * τ)) := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  rw [← pow_three_le_iff (by positivity) (by positivity), rpow_pow_three hN0.le]
  have e : (N ^ 3 * queEta N W τ ^ 2 / W ^ 2) ^ 3 = N ^ 9 * (queEta N W τ ^ 3) ^ 2 / W ^ 6 := by
    ring
  rw [e, queEta_cube hN0 hW]
  have e2 : N ^ (-3 - 3 * τ) = N ^ (-(3 * τ)) * N⁻¹ ^ 3 := by
    rw [show -3 - 3 * τ = -(3 * τ) + (-3 : ℝ) by ring, Real.rpow_add hN0,
      show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, inv_pow,
      _root_.zpow_neg, ← zpow_natCast]
    rfl
  have e3 : N ^ (3 * -(2 * τ)) = (N ^ (-(3 * τ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  rw [e2, e3]
  have hq0 : 0 < N ^ (-(3 * τ)) := by positivity
  have key : N ^ 9 * (N⁻¹ ^ 3 * (W ^ 2 / N)) ^ 2 / W ^ 6 = N / W ^ 2 := by
    field_simp
  calc N ^ 9 * (N ^ (-(3 * τ)) * N⁻¹ ^ 3 * (W ^ 2 / N)) ^ 2 / W ^ 6
      = (N ^ (-(3 * τ))) ^ 2 * (N ^ 9 * (N⁻¹ ^ 3 * (W ^ 2 / N)) ^ 2 / W ^ 6) := by ring
    _ = (N ^ (-(3 * τ))) ^ 2 * (N / W ^ 2) := by rw [key]
    _ ≤ (N ^ (-(3 * τ))) ^ 2 * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; exact hWN
    _ = _ := mul_one _

/-- `N² η² / (W η^{1/2}) = N² η^{3/2} / W = N^{-3τ/2}` (the second term of (2.17)). -/
theorem sq_mul_queEta_sq_div_eq (hN : 1 ≤ N) (hW : 0 < W) :
    N ^ 2 * queEta N W τ ^ 2 / (W * Real.sqrt (queEta N W τ)) = N ^ (-(3 * τ / 2)) := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  have hs := Real.sqrt_pos.2 hη
  have hsq : Real.sqrt (queEta N W τ) ^ 2 = queEta N W τ := Real.sq_sqrt hη.le
  rw [← pow_left_inj₀ (by positivity) (by positivity) (two_ne_zero)]
  have e : (N ^ 2 * queEta N W τ ^ 2 / (W * Real.sqrt (queEta N W τ))) ^ 2 =
      N ^ 4 * queEta N W τ ^ 3 / W ^ 2 := by
    rw [div_pow, mul_pow (W), hsq]
    field_simp
  rw [e, queEta_cube hN0 hW]
  have e2 : (N ^ (-(3 * τ / 2))) ^ 2 = N ^ (-(3 * τ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  rw [e2]
  have e3 : N ^ (-3 - 3 * τ) = N ^ (-(3 * τ)) * N⁻¹ ^ 3 := by
    rw [show -3 - 3 * τ = -(3 * τ) + (-3 : ℝ) by ring, Real.rpow_add hN0,
      show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, inv_pow,
      _root_.zpow_neg, ← zpow_natCast]
    rfl
  rw [e3]
  field_simp

/-- **The arithmetic of (2.17)**: with `η = N^{-1-τ} (W²/N)^{1/3}`, `ε₀ = W^δ (Nη)^{-3}` (the error
of (2.8), (2.9)) and a `Θ`-oscillation `K (L + η^{-1/2})`, `L = N/W`,
`8 η² N² (2 ε₀ + W⁻¹ K (L + η^{-1/2})) ≤ 16 W^δ N^{τ - 2c/3} + 8K N^{-2τ} + 8K N^{-3τ/2}`. -/
theorem queBound_le (hN : 1 ≤ N) (hW : 0 < W) {c δ K : ℝ} (hK : 0 ≤ K)
    (hWc : N ^ (1 + 2 * c) ≤ W ^ 2) (hWN : N ≤ W ^ 2) :
    8 * queEta N W τ ^ 2 * N ^ 2 * (2 * (W ^ δ * (N * queEta N W τ)⁻¹ ^ 3) +
      W⁻¹ * (K * (N / W + 1 / Real.sqrt (queEta N W τ)))) ≤
      16 * W ^ δ * N ^ (τ - 2 * c / 3) + 8 * K * N ^ (-(2 * τ)) + 8 * K * N ^ (-(3 * τ / 2)) := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  have hs := Real.sqrt_pos.2 hη
  have hA := inv_mul_queEta_le (τ := τ) hN hW hWc
  have hB := cube_mul_queEta_sq_le (τ := τ) hN hW hWN
  have hC := sq_mul_queEta_sq_div_eq (τ := τ) hN hW
  have hWd : 0 < W ^ δ := Real.rpow_pos_of_pos hW δ
  have e1 : 8 * queEta N W τ ^ 2 * N ^ 2 * (2 * (W ^ δ * (N * queEta N W τ)⁻¹ ^ 3)) =
      16 * W ^ δ * (N * queEta N W τ)⁻¹ := by
    field_simp
    norm_num
  have e2 : 8 * queEta N W τ ^ 2 * N ^ 2 * (W⁻¹ * (K * (N / W + 1 / Real.sqrt (queEta N W τ)))) =
      8 * K * (N ^ 3 * queEta N W τ ^ 2 / W ^ 2) +
        8 * K * (N ^ 2 * queEta N W τ ^ 2 / (W * Real.sqrt (queEta N W τ))) := by
    field_simp
  rw [mul_add, e1, e2, hC]
  have h1 : 16 * W ^ δ * (N * queEta N W τ)⁻¹ ≤ 16 * W ^ δ * N ^ (τ - 2 * c / 3) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h2 : 8 * K * (N ^ 3 * queEta N W τ ^ 2 / W ^ 2) ≤ 8 * K * N ^ (-(2 * τ)) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  linarith

/-- `η ≥ N^{-1-τ+2c/3}` when `W² ≥ N^{1+2c}` (so `η ≥ N^{-1+c/3}` for `τ = c/3`). -/
theorem rpow_le_queEta (hN : 1 ≤ N) (hW : 0 < W) {c : ℝ} (hWc : N ^ (1 + 2 * c) ≤ W ^ 2) :
    N ^ (-1 - τ + 2 * c / 3) ≤ queEta N W τ := by
  have hN0 : 0 < N := by linarith
  have hη := queEta_pos (τ := τ) hN0 hW
  have h := inv_mul_queEta_le (τ := τ) hN hW hWc
  have hp : 0 < N ^ (τ - 2 * c / 3) := by positivity
  have h2 : (N ^ (τ - 2 * c / 3))⁻¹ ≤ N * queEta N W τ := by
    rw [inv_le_comm₀ hp (by positivity)]; exact h
  have e : N ^ (-1 - τ + 2 * c / 3) = N⁻¹ * (N ^ (τ - 2 * c / 3))⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
  rw [e]
  calc N⁻¹ * (N ^ (τ - 2 * c / 3))⁻¹ ≤ N⁻¹ * (N * queEta N W τ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = queEta N W τ := by field_simp

end Scale

/-! ### Theorem 2.5 along a sequence -/

section Sequence

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Band

variable (B : Band Ω)

/-- The matrix size `N = L W` (the paper's `N`; the index of `RBM.Band` is only comparable). -/
def size (N : ℕ) : ℕ := B.L N * B.W N

theorem tendsto_size : Tendsto B.size atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [B.dim, eventually_ge_atTop (2 * b)] with N hN hb
  unfold size
  rw [mul_comm]
  omega

theorem one_le_size (N : ℕ) : 1 ≤ B.size N :=
  Nat.mul_pos (by have := B.three_le_L N; omega) (B.W_pos N)

/-- (2.2) in terms of the matrix size: `W² ≥ N^{1+2c}`, `N = L W`. -/
theorem eventually_size_rpow_le_W_sq :
    ∀ᶠ N : ℕ in atTop, ((B.size N : ℕ) : ℝ) ^ (1 + 2 * B.c) ≤ (B.W N : ℝ) ^ 2 := by
  filter_upwards [B.bandwidth, B.dim] with N hbw hdim
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hnN : (B.size N : ℝ) ≤ N := by
    have : B.size N ≤ N := by unfold size; rw [mul_comm]; exact hdim.1
    exact_mod_cast this
  have h1 : ((B.size N : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + B.c) ≤ B.W N :=
    (Real.rpow_le_rpow (by linarith) hnN (by linarith [B.c_pos])).trans hbw
  calc ((B.size N : ℕ) : ℝ) ^ (1 + 2 * B.c)
      = (((B.size N : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + B.c)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        congr 1; push_cast; ring
    _ ≤ (B.W N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2

end Band

/-- The spectral scale `η_N = N^{-1-τ*} (W²/N)^{1/3}` of Theorem 2.5 at index `N` (`N = L W`). -/
noncomputable def Band.queEtaN (B : Band Ω) (τ : ℝ) (N : ℕ) : ℝ :=
  queEta (B.size N : ℝ) (B.W N : ℝ) τ

/-- The spectral parameter `z = E_N + i η_N` of the proof of Theorem 2.5. -/
noncomputable def Band.queZ (B : Band Ω) (τ : ℝ) (E : ℕ → ℝ) (N : ℕ) : ℂ :=
  (E N : ℂ) + (B.queEtaN τ N : ℂ) * Complex.I

theorem Band.queZ_im (B : Band Ω) (τ : ℝ) (E : ℕ → ℝ) (N : ℕ) :
    (B.queZ τ E N).im = B.queEtaN τ N := by
  simp [Band.queZ]

theorem Band.queZ_re (B : Band Ω) (τ : ℝ) (E : ℕ → ℝ) (N : ℕ) :
    (B.queZ τ E N).re = E N := by
  simp [Band.queZ]

/-- **(2.8), (2.9) in the form used by Theorem 2.5** (and **(7.47)**, with `Θ = Θ̃` for `H_t`),
along spectral parameters `z_N`, for a family `H` of `N × N` random matrices
(`N = L W`):  for every `δ > 0`, eventually, for all blocks `x, y`,
`|E Tr G E_x G* E_y - W⁻¹ |m|² Θ(|m|²)_{xy}| ≤ W^δ (N Im z)^{-3}` and
`|E Tr G E_x G E_y - W⁻¹ m² Θ(m²)_{xy}| ≤ W^δ (N Im z)^{-3}`, `m = m_sc(z)`, together with the
integrability of the loops (automatic in the paper since `‖G‖ ≤ (Im z)^{-1}`). -/
structure QDExpect (B : Band Ω) (H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℕ → ℂ)
    (Θ : ∀ N, ℂ → Matrix (ZMod (B.L N)) (ZMod (B.L N)) ℂ) : Prop where
  integrable_pp : ∀ N x y, Integrable (fun ω => trGG (H N ω) (z N) x y) B.P
  integrable_pm : ∀ N x y, Integrable (fun ω => trGGs (H N ω) (z N) x y) B.P
  pm : ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ x y : ZMod (B.L N),
    ‖(∫ ω, trGGs (H N ω) (z N) x y ∂B.P) - (B.W N : ℂ)⁻¹ *
      (((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) * Θ N ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) x y)‖ ≤
      (B.W N : ℝ) ^ δ * ((B.size N : ℝ) * (z N).im)⁻¹ ^ 3
  pp : ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ x y : ZMod (B.L N),
    ‖(∫ ω, trGG (H N ω) (z N) x y ∂B.P) - (B.W N : ℂ)⁻¹ *
      (msc (z N) ^ 2 * Θ N (msc (z N) ^ 2) x y)‖ ≤
      (B.W N : ℝ) ^ δ * ((B.size N : ℝ) * (z N).im)⁻¹ ^ 3

/-- **The oscillation of the main terms** (Lemma 2.14 as used in (2.16)): for `ξ = |m|², m²`,
`|ξ Θ(ξ)_{ab} - ξ Θ(ξ)_{a'b'}| ≤ K (L + (Im z)^{-1/2})`, eventually. -/
def ThetaOsc (B : Band Ω) (z : ℕ → ℂ) (Θ : ∀ N, ℂ → Matrix (ZMod (B.L N)) (ZMod (B.L N)) ℂ)
    (K : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ a b a' b' : ZMod (B.L N),
    ‖((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) * Θ N ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) a b -
      ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) * Θ N ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) a' b'‖ ≤
        K * (B.L N + 1 / Real.sqrt (z N).im) ∧
    ‖msc (z N) ^ 2 * Θ N (msc (z N) ^ 2) a b - msc (z N) ^ 2 * Θ N (msc (z N) ^ 2) a' b'‖ ≤
        K * (B.L N + 1 / Real.sqrt (z N).im)

theorem le_rpow_of_mul {n C a b : ℝ} (hn : 0 < n) (h : C ≤ n ^ (b - a)) : C * n ^ a ≤ n ^ b := by
  calc C * n ^ a ≤ n ^ (b - a) * n ^ a := mul_le_mul_of_nonneg_right h (by positivity)
    _ = n ^ b := by rw [← Real.rpow_add hn]; congr 1; ring

/-- **Theorem 2.5, (2.12)/(2.13), from (2.8)/(2.9)** (the proof on pp. 9–10: (2.14)–(2.17) and
Markov's inequality): for `0 < τ* < c/2` (2.11), energies `E_N`, `η = N^{-1-τ*} (W²/N)^{1/3}`,
`z = E_N + iη`, if (2.8), (2.9) hold at `z` (`QDExpect`) with main terms whose oscillation is
`O(L + η^{-1/2})` (`ThetaOsc`), then eventually, for every nonempty `S ⊆ ℤ_L`,
`P(max_{λ_i, λ_j ∈ J_E} |N ψ_i* (|S|⁻¹ ∑_{a ∈ S} E_a - N⁻¹) ψ_j|² ≥ N^{-τ*/6}) ≤ N^{-τ*/6}`. -/
theorem que_of_QDExpect (B : Band Ω) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < B.c / 2)
    (H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    (Θ : ∀ N, ℂ → Matrix (ZMod (B.L N)) (ZMod (B.L N)) ℂ) (E : ℕ → ℝ)
    (hQD : QDExpect B H (B.queZ τ E) Θ) {K : ℝ} (hK : 0 ≤ K)
    (hosc : ThetaOsc B (B.queZ τ E) Θ K) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset (ZMod (B.L N)), S.Nonempty →
      B.P (queBad (hH N) S (E N) (B.queEtaN τ N) ((B.size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6))) := by
  have := B.isProbabilityMeasure
  set δ : ℝ := (B.c - 2 * τ) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hsz := B.tendsto_size
  filter_upwards [hQD.pm δ hδ0, hQD.pp δ hδ0, hosc, B.eventually_size_rpow_le_W_sq,
    hsz.eventually (eventually_le_rpow 48 hδ0),
    hsz.eventually (eventually_le_rpow (24 * K) (by positivity : (0 : ℝ) < 5 * τ / 3)),
    hsz.eventually (eventually_le_rpow (24 * K) (by positivity : (0 : ℝ) < 7 * τ / 6))]
    with N hpm hpp hos hWc r1 r2 r3 S hS
  set n : ℝ := (B.size N : ℝ) with hn
  set W : ℝ := (B.W N : ℝ) with hW
  set η : ℝ := B.queEtaN τ N with hη
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast B.one_le_size N
  have hn0 : 0 < n := by linarith
  have hW0 : 0 < W := by rw [hW]; exact_mod_cast B.W_pos N
  have hWn : W ≤ n := by
    rw [hW, hn, Band.size]; push_cast
    have : (1 : ℝ) ≤ B.L N := by exact_mod_cast (show 1 ≤ B.L N by have := B.three_le_L N; omega)
    nlinarith
  have hWN2 : n ≤ W ^ 2 := by
    refine le_trans ?_ hWc
    calc n = n ^ (1 : ℝ) := (Real.rpow_one n).symm
      _ ≤ n ^ (1 + 2 * B.c) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [B.c_pos])
  have hηpos : 0 < η := queEta_pos hn0 hW0
  have hzim : (B.queZ τ E N).im = η := B.queZ_im τ E N
  have hLn : (B.L N : ℝ) = n / W := by
    have hW0' : (B.W N : ℝ) ≠ 0 := by exact_mod_cast (B.W_pos N).ne'
    rw [hn, hW, Band.size]; push_cast; field_simp
  -- the single-`N` estimate
  have hmain := measure_queBad_le_of_approx (P := B.P) (hH N) hS (E N) hηpos
    (ε := n ^ (-(τ / 6))) (ε₀ := W ^ δ * (n * η)⁻¹ ^ 3) (δ := K * (n / W + 1 / Real.sqrt η))
    (Mpp := fun x y => msc (B.queZ τ E N) ^ 2 * Θ N (msc (B.queZ τ E N) ^ 2) x y)
    (Mpm := fun x y => ((‖msc (B.queZ τ E N)‖ ^ 2 : ℝ) : ℂ) *
      Θ N ((‖msc (B.queZ τ E N)‖ ^ 2 : ℝ) : ℂ) x y)
    (by positivity) (hQD.integrable_pp N) (hQD.integrable_pm N)
    (fun x y => by have := hpp x y; rwa [hzim] at this)
    (fun x y => by have := hpm x y; rwa [hzim] at this)
    (fun x y x' y' => by have := (hos x y x' y').2; rwa [hzim, hLn] at this)
    (fun x y x' y' => by have := (hos x y x' y').1; rwa [hzim, hLn] at this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the arithmetic of (2.17)
  have hbound := queBound_le (τ := τ) (δ := δ) hn1 hW0 hK hWc hWN2
  have hWd : W ^ δ ≤ n ^ δ := Real.rpow_le_rpow hW0.le hWn hδ0.le
  have t1 : 16 * W ^ δ * n ^ (τ - 2 * B.c / 3) ≤ n ^ (-(τ / 3)) / 3 := by
    have h := le_rpow_of_mul hn0 (a := δ + (τ - 2 * B.c / 3)) (b := -(τ / 3)) (C := 48)
      (by convert r1 using 2; rw [hδ]; ring)
    rw [Real.rpow_add hn0] at h
    have : 0 ≤ n ^ (τ - 2 * B.c / 3) := by positivity
    nlinarith
  have t2 : 8 * K * n ^ (-(2 * τ)) ≤ n ^ (-(τ / 3)) / 3 := by
    have h := le_rpow_of_mul hn0 (a := -(2 * τ)) (b := -(τ / 3)) (C := 24 * K)
      (by convert r2 using 2; ring)
    linarith
  have t3 : 8 * K * n ^ (-(3 * τ / 2)) ≤ n ^ (-(τ / 3)) / 3 := by
    have h := le_rpow_of_mul hn0 (a := -(3 * τ / 2)) (b := -(τ / 3)) (C := 24 * K)
      (by convert r3 using 2; ring)
    linarith
  have hε : 0 < n ^ (-(τ / 6)) := by positivity
  rw [div_le_iff₀ hε]
  have e : n ^ (-(τ / 6)) * n ^ (-(τ / 6)) = n ^ (-(τ / 3)) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  rw [e]
  have hη2 : η = queEta n W τ := rfl
  rw [← hη2] at hbound
  rw [show ((B.L N * B.W N : ℕ) : ℝ) = n from rfl, show ((B.W N : ℕ) : ℝ) = W from rfl]
  linarith

/-! #### The oscillation hypothesis for `Θ` (Theorem 2.5) and `Θ̃` ((2.27)) -/

theorem one_div_sqrt_le_of_ge {x η : ℝ} (hη : 0 < η) (h : η / 16 ≤ x) :
    1 / Real.sqrt x ≤ 4 / Real.sqrt η := by
  have hx : 0 < x := by linarith
  have hsη := Real.sqrt_pos.2 hη
  have hsx := Real.sqrt_pos.2 hx
  have h1 : Real.sqrt (η / 16) = Real.sqrt η / 4 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16), show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h2 : Real.sqrt η / 4 ≤ Real.sqrt x := h1 ▸ Real.sqrt_le_sqrt h
  rw [div_le_div_iff₀ hsx hsη]
  linarith

/-- `‖1 - |m|²‖ ≥ η/16` and `‖1 - m²‖ ≥ η/16` in the bulk (from Lemma 2.8, `1 - t ≥ η/16`);
this is (2.16) `|m|² ≤ 1 - cη`. -/
theorem msc_gap {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz0 : 0 < z.im) (hz1 : z.im ≤ 1)
    (hre : |z.re| ≤ 2 - κ) :
    z.im / 16 ≤ ‖1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ)‖ ∧ z.im / 16 ≤ ‖1 - msc z ^ 2‖ := by
  have h := one_sub_lemT_ge hκ hz0 hz1 hre
  have hlt : ‖msc z‖ ^ 2 < 1 := by
    have := norm_msc_lt_one hz0
    nlinarith [norm_nonneg (msc z)]
  have e : ‖1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖msc z‖ ^ 2 := by
    rw [show (1 : ℂ) - ((‖msc z‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖msc z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hl : lemT z = ‖msc z‖ ^ 2 := rfl
  refine ⟨?_, ?_⟩
  · rw [e]; linarith
  · have h2 := norm_sub_norm_le (1 : ℂ) (msc z ^ 2)
    rw [norm_one, norm_pow] at h2
    linarith

/-- **`ThetaOsc` for `Θ_ξ = (1 - ξ S^{(B)})⁻¹`** at the spectral parameters of Theorem 2.5,
with `K = 1152`: from `norm_mul_Theta_sub_le` and (2.16). -/
theorem thetaOsc_Theta (B : Band Ω) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) (E : ℕ → ℝ)
    (hE : ∀ N, |E N| ≤ 2 - κ) :
    ThetaOsc B (B.queZ τ E) (fun N => Theta (B.L N)) 1152 := by
  refine Eventually.of_forall fun N a b a' b' => ?_
  set z := B.queZ τ E N
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hWn : (B.W N : ℝ) ≤ (B.size N : ℝ) := by
    rw [Band.size]; push_cast
    have : (1 : ℝ) ≤ B.L N := by exact_mod_cast (show 1 ≤ B.L N by have := B.three_le_L N; omega)
    nlinarith
  have hz0 : 0 < z.im := by rw [B.queZ_im]; exact queEta_pos (by linarith) hW0
  have hz1 : z.im ≤ 1 := by rw [B.queZ_im]; exact queEta_le_one hn1 hW0 hWn hτ
  have hre : |z.re| ≤ 2 - κ := by rw [B.queZ_re]; exact hE N
  obtain ⟨g1, g2⟩ := msc_gap hκ hz0 hz1 hre
  have hL := B.three_le_L N
  have hm0 : msc z ≠ 0 := norm_pos_iff.1 (norm_msc_pos hz0)
  have hm1 := norm_msc_lt_one hz0
  have hLpos : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
  have hsq : 0 ≤ 1 / Real.sqrt z.im := by positivity
  refine ⟨?_, ?_⟩
  · have hξ0 : ((‖msc z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos (norm_msc_pos hz0) 2).ne'
    have hξ1 : ‖((‖msc z‖ ^ 2 : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (msc z)]
    have h := norm_mul_Theta_sub_le (B.L N) hL hξ0 hξ1 a b a' b'
    have h4 := one_div_sqrt_le_of_ge hz0 g1
    calc _ ≤ 288 * ((B.L N : ℝ) + 1 / Real.sqrt ‖1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ)‖) := h
      _ ≤ 288 * ((B.L N : ℝ) + 4 / Real.sqrt z.im) := by gcongr
      _ ≤ 1152 * ((B.L N : ℝ) + 1 / Real.sqrt z.im) := by
          rw [show 4 / Real.sqrt z.im = 4 * (1 / Real.sqrt z.im) by ring]; nlinarith
  · have hξ0 : msc z ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have hξ1 : ‖msc z ^ 2‖ < 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg (msc z)]
    have h := norm_mul_Theta_sub_le (B.L N) hL hξ0 hξ1 a b a' b'
    have h4 := one_div_sqrt_le_of_ge hz0 g2
    calc _ ≤ 288 * ((B.L N : ℝ) + 1 / Real.sqrt ‖1 - msc z ^ 2‖) := h
      _ ≤ 288 * ((B.L N : ℝ) + 4 / Real.sqrt z.im) := by gcongr
      _ ≤ 1152 * ((B.L N : ℝ) + 1 / Real.sqrt z.im) := by
          rw [show 4 / Real.sqrt z.im = 4 * (1 / Real.sqrt z.im) by ring]; nlinarith

/-- **`ThetaOsc` for `Θ̃_ξ = (1 - ξ S̃^{(B)})⁻¹`** (§7.2, `S̃ = (1-ζ) S + ζ/L`), `K = 2304`,
provided eventually `0 < ζ_N ≤ 1/2` and `ζ_N ≤ η_N / 16` (in the paper `ζ_U ∼ N^{-1+τ_U} ≪ η`). -/
theorem thetaOsc_ThetaTilde (B : Band Ω) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) (E : ℕ → ℝ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (ζ : ℕ → ℝ)
    (hζ : ∀ᶠ N : ℕ in atTop, 0 < ζ N ∧ ζ N ≤ 1 / 2 ∧ ζ N ≤ B.queEtaN τ N / 16) :
    ThetaOsc B (B.queZ τ E) (fun N => ThetaTilde (B.L N) (ζ N)) 2304 := by
  filter_upwards [hζ] with N ⟨hζ0, hζ1, hζη⟩ a b a' b'
  set z := B.queZ τ E N
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hWn : (B.W N : ℝ) ≤ (B.size N : ℝ) := by
    rw [Band.size]; push_cast
    have : (1 : ℝ) ≤ B.L N := by exact_mod_cast (show 1 ≤ B.L N by have := B.three_le_L N; omega)
    nlinarith
  have hz0 : 0 < z.im := by rw [B.queZ_im]; exact queEta_pos (by linarith) hW0
  have hz1 : z.im ≤ 1 := by rw [B.queZ_im]; exact queEta_le_one hn1 hW0 hWn hτ
  have hre : |z.re| ≤ 2 - κ := by rw [B.queZ_re]; exact hE N
  have hζ' : ζ N ≤ z.im / 16 := by rw [B.queZ_im]; exact hζη
  obtain ⟨g1, g2⟩ := msc_gap hκ hz0 hz1 hre
  have hL := B.three_le_L N
  have hm0 : msc z ≠ 0 := norm_pos_iff.1 (norm_msc_pos hz0)
  have hm1 := norm_msc_lt_one hz0
  have hLpos : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
  have hsq : 0 ≤ 1 / Real.sqrt z.im := by positivity
  refine ⟨?_, ?_⟩
  · have hξ0 : ((‖msc z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos (norm_msc_pos hz0) 2).ne'
    have hξ1 : ‖((‖msc z‖ ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (msc z)]
    have h := norm_mul_ThetaTilde_sub_le (B.L N) hL hξ0 hξ1 hζ0 hζ1 (by linarith)
      a b a' b'
    have h4 := one_div_sqrt_le_of_ge hz0 g1
    calc _ ≤ 576 * ((B.L N : ℝ) + 1 / Real.sqrt ‖1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ)‖) := h
      _ ≤ 576 * ((B.L N : ℝ) + 4 / Real.sqrt z.im) := by gcongr
      _ ≤ 2304 * ((B.L N : ℝ) + 1 / Real.sqrt z.im) := by
          rw [show 4 / Real.sqrt z.im = 4 * (1 / Real.sqrt z.im) by ring]; nlinarith
  · have hξ0 : msc z ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have hξ1 : ‖msc z ^ 2‖ ≤ 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg (msc z)]
    have h := norm_mul_ThetaTilde_sub_le (B.L N) hL hξ0 hξ1 hζ0 hζ1 (by linarith)
      a b a' b'
    have h4 := one_div_sqrt_le_of_ge hz0 g2
    calc _ ≤ 576 * ((B.L N : ℝ) + 1 / Real.sqrt ‖1 - msc z ^ 2‖) := h
      _ ≤ 576 * ((B.L N : ℝ) + 4 / Real.sqrt z.im) := by gcongr
      _ ≤ 2304 * ((B.L N : ℝ) + 1 / Real.sqrt z.im) := by
          rw [show 4 / Real.sqrt z.im = 4 * (1 / Real.sqrt z.im) by ring]; nlinarith

/-! #### Theorem 2.5 in the form of (2.12), (2.13) -/

/-- The event of **(2.12)**: `max_{λ_i, λ_j ∈ J_E} |N ψ_i* (E_a - N⁻¹ I) ψ_j|² ≥ ε`. -/
def queEvent212 {L W : ℕ} [NeZero L] {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (a : ZMod L) (E η ε : ℝ) : Set Ω :=
  {ω | ∃ i j, |(hH ω).eigenvalues i - E| ≤ η ∧ |(hH ω).eigenvalues j - E| ≤ η ∧
    ε ≤ ‖((L * W : ℕ) : ℂ) *
      eigOverlap (hH ω) (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) i j‖ ^ 2}

/-- The event of **(2.13)**: `max_{λ_k ∈ J_E} |∑_{a ∈ A} ∑_{x ∈ I_a} |ψ_k(x)|² - |A| W / N|
≥ |A| W / N^{1 + τ*/12}`. -/
def queEvent213 {L W : ℕ} [NeZero L] {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (A : Finset (ZMod L)) (E η τ : ℝ) : Set Ω :=
  {ω | ∃ k, |(hH ω).eigenvalues k - E| ≤ η ∧
    (A.card * W : ℕ) / ((L * W : ℕ) : ℝ) ^ (1 + τ / 12) ≤
      |∑ a ∈ A, ∑ x : Fin W, ‖(hH ω).eigenvectorBasis k (a, x)‖ ^ 2 -
        (A.card * W : ℕ) / ((L * W : ℕ) : ℝ)|}

omit [MeasurableSpace Ω] in
theorem queEvent212_eq {L W : ℕ} [NeZero L] {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (a : ZMod L) (E η ε : ℝ) :
    queEvent212 hH a E η ε = queBad hH {a} E η ε := by
  simp only [queEvent212, queBad, queObs_singleton]

omit [MeasurableSpace Ω] in
theorem queEvent213_subset {L W : ℕ} [NeZero L] [NeZero W]
    {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : ∀ ω, (H ω).IsHermitian)
    {A : Finset (ZMod L)} (hA : A.Nonempty) (E η τ : ℝ) :
    queEvent213 hH A E η τ ⊆ queBad hH A E η (((L * W : ℕ) : ℝ) ^ (-(τ / 6))) := by
  rintro ω ⟨k, hk, hbig⟩
  refine ⟨k, k, hk, hk, ?_⟩
  set n : ℝ := ((L * W : ℕ) : ℝ) with hn
  set m : ℝ := ((A.card * W : ℕ) : ℝ) with hm
  set s : ℝ := ∑ a ∈ A, ∑ x : Fin W, ‖(hH ω).eigenvectorBasis k (a, x)‖ ^ 2
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)
  have hm0 : 0 < m := by
    rw [hm]; exact_mod_cast Nat.mul_pos (Finset.card_pos.2 hA) (NeZero.pos W)
  rw [eigOverlap_queObs_self (hH ω) hA k, ← hn, ← hm, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- `|n m⁻¹ (s - m/n)| ≥ n m⁻¹ m n^{-1-τ/12} = n^{-τ/12}`
  have hpow : n ^ (1 + τ / 12) = n * n ^ (τ / 12) := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hq : 0 < n ^ (τ / 12) := by positivity
  have hbig' : m / (n * n ^ (τ / 12)) ≤ |s - m / n| := by rw [← hpow]; exact hbig
  have hlow : (n ^ (τ / 12))⁻¹ ≤ |n * (m⁻¹ * (s - m / n))| := by
    rw [abs_mul, abs_mul, abs_of_pos hn0, abs_of_pos (inv_pos.2 hm0)]
    have : m / (n * n ^ (τ / 12)) * (n * m⁻¹) = (n ^ (τ / 12))⁻¹ := by field_simp
    rw [← this]
    have hc : 0 ≤ n * m⁻¹ := by positivity
    nlinarith
  have e : n ^ (-(τ / 6)) = ((n ^ (τ / 12))⁻¹) ^ 2 := by
    rw [← Real.rpow_neg hn0.le, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1; push_cast; ring
  rw [e]
  have h2 := pow_le_pow_left₀ (by positivity) hlow 2
  rw [sq_abs] at h2
  exact h2

/-- **Theorem 2.5 (generalized QUE), (2.12) and (2.13), from (2.8)/(2.9)-type input**, for any
main-term propagator `Θ` with oscillation `O(L + η^{-1/2})`: for `0 < τ* < c/2` (2.11) and
energies `E_N`, eventually (uniformly in `a` and in nonempty `A ⊆ ℤ_L`)
`P((2.12) fails at a) ≤ N^{-τ*/6}` and `P((2.13) fails at A) ≤ N^{-τ*/6}`, with `N = L W`,
`J_E = [E - η, E + η]`, `η = N^{-1-τ*} (W²/N)^{1/3}`. -/
theorem que_literal_of_QDExpect (B : Band Ω) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < B.c / 2)
    (H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    (Θ : ∀ N, ℂ → Matrix (ZMod (B.L N)) (ZMod (B.L N)) ℂ) (E : ℕ → ℝ)
    (hQD : QDExpect B H (B.queZ τ E) Θ) {K : ℝ} (hK : 0 ≤ K)
    (hosc : ThetaOsc B (B.queZ τ E) Θ K) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (hH N) a (E N) (B.queEtaN τ N) ((B.size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (hH N) A (E N) (B.queEtaN τ N) τ) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) := by
  have h := que_of_QDExpect B hτ0 hτ H hH Θ E hQD hK hosc
  refine ⟨h.mono fun N hN a => ?_, h.mono fun N hN A hA => ?_⟩
  · rw [queEvent212_eq]; exact hN {a} (Finset.singleton_nonempty a)
  · exact (measure_mono (queEvent213_subset (hH N) hA _ _ τ)).trans (hN A hA)

/-- **Theorem 2.5 (generalized quantum unique ergodicity)** for the band matrix `H`, assuming
Theorem 2.4's (2.8), (2.9) at the spectral parameters `z = E_N + iη` of the proof
(`QDExpect` with `Θ_ξ = (1 - ξ S^{(B)})⁻¹`): for `0 < τ* < c/2` and bulk energies
`|E_N| ≤ 2 - κ`, eventually, for all `a` and all nonempty `A ⊆ ℤ_L`,
`P(max_{λ_i, λ_j ∈ J_E} |N ψ_i* (E_a - N⁻¹) ψ_j|² ≥ N^{-τ*/6}) ≤ N^{-τ*/6}`   (2.12)
and `P(max_{λ_k ∈ J_E} |∑_{a ∈ A} ∑_{x ∈ I_a} |ψ_k(x)|² - |A| W/N| ≥ |A| W / N^{1+τ*/12})
≤ N^{-τ*/6}`   (2.13). -/
theorem theorem2_5_of_QDExpect (B : Band Ω) {κ τ : ℝ} (hκ : 0 < κ) (hτ0 : 0 < τ)
    (hτ : τ < B.c / 2) (H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ)
    (hH : ∀ N ω, (H N ω).IsHermitian) (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hQD : QDExpect B H (B.queZ τ E) (fun N => Theta (B.L N))) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (hH N) a (E N) (B.queEtaN τ N) ((B.size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (hH N) A (E N) (B.queEtaN τ N) τ) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) :=
  que_literal_of_QDExpect B hτ0 hτ H hH _ E hQD (by norm_num)
    (thetaOsc_Theta B hκ hτ0.le E hE)

/-! #### Theorem 2.5 from Theorem 2.21 (through Theorem 2.4) -/

/-- `N Im z ≤ W ℓ(z) Im z` at the spectral parameter of Theorem 2.5 (`ℓ(z) = L + 1 ≥ L`, since
`η^{-1/2} ≥ L`, the remark after (2.15)). -/
theorem Band.size_mul_im_le_zScale (B : Band Ω) {τ : ℝ} (hτ : 0 ≤ τ) (E : ℕ → ℝ) {N : ℕ}
    (hWN : ((B.size N : ℕ) : ℝ) ≤ (B.W N : ℝ) ^ 2) :
    (B.size N : ℝ) * (B.queZ τ E N).im ≤ B.zScale N (B.queZ τ E N) := by
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη := queEta_pos (τ := τ) (by linarith) hW0 (N := (B.size N : ℝ))
  have hL : (B.L N : ℝ) ≤ 1 / Real.sqrt (B.queZ τ E N).im := by
    have h := div_le_inv_sqrt_queEta (τ := τ) hn1 hW0 hWN hτ
    rw [B.queZ_im]
    have e : (B.size N : ℝ) / B.W N = B.L N := by
      have hW0' : (B.W N : ℝ) ≠ 0 := hW0.ne'
      rw [Band.size]; push_cast; field_simp
    rw [e] at h
    exact h
  have hell : (B.L N : ℝ) ≤ ellZ (B.L N) (B.queZ τ E N) := by
    rw [ellZ, ellOf, min_eq_right hL]; linarith
  rw [Band.zScale]
  have e : (B.size N : ℝ) = B.W N * B.L N := by rw [Band.size]; push_cast; ring
  rw [e, B.queZ_im]
  have := hη.le
  have : (0 : ℝ) ≤ B.W N := hW0.le
  gcongr

/-- **(2.8), (2.9) at the spectral parameters of Theorem 2.5, from Theorem 2.21**
(`quantumDiffusion_of_Thm221`), when those parameters lie on a fixed energy slice of Lemma 2.8
(`RBM.SpecSeq`, the interface restriction of `Flow/Consequences.lean`).  Integrability of the
loops is a hypothesis. -/
theorem QDExpect.of_Thm221 {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' E' : ℝ}
    (hκ : 0 < κ) (hT : Thm221 X κ) (hτ' : 0 < τ') (hτ : 0 ≤ τ) (E : ℕ → ℝ)
    (hz : SpecSeq κ τ' E' (B.queZ τ E))
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    QDExpect B T.Hband (B.queZ τ E) (fun N => Theta (B.L N)) := by
  have hB := hz.bounds X hκ hT hτ'
  have key : ∀ N, ((B.size N : ℕ) : ℝ) ≤ (B.W N : ℝ) ^ 2 →
      ((B.size N : ℝ) * (B.queZ τ E N).im)⁻¹ ^ 3 ≥ (B.zScale N (B.queZ τ E N))⁻¹ ^ 3 := by
    intro N hWN
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    have hpos : 0 < (B.size N : ℝ) * (B.queZ τ E N).im := mul_pos (by linarith) (hz.im_pos N)
    exact pow_le_pow_left₀ (inv_nonneg.2 (B.zScale_pos N (hz.im_pos N)).le)
      (inv_anti₀ hpos (B.size_mul_im_le_zScale hτ E hWN)) 3
  have hWN : ∀ᶠ N : ℕ in atTop, ((B.size N : ℕ) : ℝ) ≤ (B.W N : ℝ) ^ 2 := by
    filter_upwards [B.eventually_size_rpow_le_W_sq] with N h
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    refine le_trans ?_ h
    calc ((B.size N : ℕ) : ℝ) = ((B.size N : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [B.c_pos])
  refine ⟨hint_pp, hint_pm, fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [expect_quantumDiffusion_pm_W_of_bounds T hκ hz hB hδ, hWN] with N h hW x y
    have h1 := h (x, y)
    rw [← mul_assoc]
    refine h1.trans (mul_le_mul_of_nonneg_left (key N hW) (by positivity))
  · filter_upwards [expect_quantumDiffusion_pp_W_of_bounds T hκ hz hB hδ, hWN] with N h hW x y
    have h1 := h (x, y)
    rw [← mul_assoc]
    refine h1.trans (mul_le_mul_of_nonneg_left (key N hW) (by positivity))

/-- **Theorem 2.5 from Theorem 2.21** (Theorem 2.21 ⇒ Theorem 2.4 ⇒ Theorem 2.5), on a fixed
energy slice of Lemma 2.8 (see `QDExpect.of_Thm221`). -/
theorem theorem2_5_of_Thm221 {B : Band Ω} {X : Sample B} (T : Transfer X) {κ τ τ' E' : ℝ}
    (hκ : 0 < κ) (hT : Thm221 X κ) (hτ' : 0 < τ') (hτ0 : 0 < τ) (hτ : τ < B.c / 2)
    (E : ℕ → ℝ) (hz : SpecSeq κ τ' E' (B.queZ τ E))
    (hint_pp : ∀ N x y, Integrable (fun ω => trGG (T.Hband N ω) (B.queZ τ E N) x y) B.P)
    (hint_pm : ∀ N x y, Integrable (fun ω => trGGs (T.Hband N ω) (B.queZ τ E N) x y) B.P) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (T.hermitian N) a (E N) (B.queEtaN τ N) ((B.size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (T.hermitian N) A (E N) (B.queEtaN τ N) τ) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(τ / 6)))) :=
  theorem2_5_of_QDExpect B hκ hτ0 hτ T.Hband T.hermitian E
    (fun N => by have := hz.abs_re_le N; rwa [B.queZ_re] at this)
    (QDExpect.of_Thm221 T hκ hT hτ' hτ0.le E hz hint_pp hint_pm)

end Sequence

/-! ### Theorem 2.6: correlation functions, the OU flow, and the three-step strategy -/

section CorrelationFunctions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The pairing `∫_{ℝ^k} O(α) ρ^{(k)}_H(E + α/N) dα`** for a random Hermitian `N × N` matrix `H`,
written without densities: if the unordered eigenvalues have joint density `ρ^{(N)}_H` and
`ρ^{(k)}_H` is its `k`-marginal (the paper's definition before Theorem 2.6), then by symmetry
`∫ O(α) ρ^{(k)}_H(E + α/N) dα
  = N^k (N-k)!/N! · E ∑_{i : Fin k ↪ [N]} O(N(λ_{i_1} - E), …, N(λ_{i_k} - E))`,
which is what is defined here (it makes sense with or without a density). -/
noncomputable def corrPairing {n : Type*} [Fintype n] [DecidableEq n] (P : Measure Ω)
    (H : Ω → Matrix n n ℂ) (hH : ∀ ω, (H ω).IsHermitian) (k : ℕ) (O : (Fin k → ℝ) → ℝ)
    (E : ℝ) : ℝ :=
  (Fintype.card n : ℝ) ^ k * (((Fintype.card n - k).factorial : ℝ) / (Fintype.card n).factorial) *
    ∫ ω, ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) ∂P

theorem corrPairing_congr {n : Type*} [Fintype n] [DecidableEq n] (P : Measure Ω)
    {H H' : Ω → Matrix n n ℂ} (h : H = H') (hH : ∀ ω, (H ω).IsHermitian)
    (hH' : ∀ ω, (H' ω).IsHermitian) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    corrPairing P H hH k O E = corrPairing P H' hH' k O E := by
  subst h; rfl

/-- The unnormalized joint density of the unordered GUE eigenvalues (entries with
`E|h_ij|² = N⁻¹`, i.e. the law `∝ exp(-N Tr H²/2)`, the invariant law `H_∞` of (2.19)):
`∏_{i<j} (x_i - x_j)² exp(-(N/2) ∑_i x_i²)`. -/
noncomputable def gueWeight (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (∏ i : Fin N, ∏ j : Fin N, if i < j then (x i - x j) ^ 2 else 1) *
    Real.exp (-((N : ℝ) / 2) * ∑ i, x i ^ 2)

/-- `ρ^{(N)}_{GUE}`, the normalized joint density of the unordered GUE eigenvalues. -/
noncomputable def gueDensity (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (∫ y, gueWeight N y)⁻¹ * gueWeight N x

/-- `ρ^{(k)}_{GUE}(x) = ∫_{ℝ^{N-k}} ρ^{(N)}_{GUE}(x, y) dy` (the definition before Theorem 2.6;
meaningful for `k ≤ N`, which holds eventually for fixed `k`). -/
noncomputable def gueCorr (N k : ℕ) (x : Fin k → ℝ) : ℝ :=
  ∫ y : Fin (N - k) → ℝ, gueDensity N
    (fun i => if h : (i : ℕ) < k then x ⟨i, h⟩ else y ⟨i - k, by have := i.isLt; omega⟩)

/-- `∫_{ℝ^k} O(α) ρ^{(k)}_{GUE}(E + α/N) dα`. -/
noncomputable def gueCorrPairing (N k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) : ℝ :=
  ∫ α : Fin k → ℝ, O α * gueCorr N k (fun j => E + α j / N)

/-- The Stieltjes transform `m(z) = N⁻¹ Tr (H - z)⁻¹` (`m_t` of (2.23)). -/
noncomputable def stieltjes {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
    ℂ :=
  (Fintype.card n : ℂ)⁻¹ * (green H z).trace

end CorrelationFunctions

section TheoremTwoSix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The matrix Ornstein–Uhlenbeck flow (2.19)** `dH_t = -½ H_t dt + N^{-1/2} dB_t`, `H_0 = H`,
`H_∞ = H_{GUE}`.  As for `RBM.Sample`, only the path is recorded (Hermitian, starting at the band
matrix); its law is not formalized — everything that uses it is a hypothesis below. -/
structure OUFlow (B : Band Ω) (H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ) where
  /-- The flow `t ↦ H_t`. -/
  Ht : ∀ N, ℝ → Ω → Matrix (B.Idx N) (B.Idx N) ℂ
  hermitian : ∀ N t ω, (Ht N t ω).IsHermitian
  /-- `H_0 = H`. -/
  start : ∀ N ω, Ht N 0 ω = H N ω

/-- The times `t = N^{-1+τ}` (`t_* = N^{-1+τ_*}`, `t_U = N^{-1+τ_U}`), `N = L W`. -/
noncomputable def Band.tPow (B : Band Ω) (τ : ℝ) (N : ℕ) : ℝ := (B.size N : ℝ) ^ (-1 + τ)

/-- The test functions of Theorem 2.6: smooth with compact support. -/
def IsTestFun {k : ℕ} (O : (Fin k → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) O ∧ HasCompactSupport O

/-- **Theorem 2.6's conclusion (2.18)**: for every `|E| ≤ 2 - κ`, `k`, and smooth compactly
supported `O`, `∫ O(α) (ρ^{(k)}_H - ρ^{(k)}_{GUE})(E + α/N) dα → 0`. -/
def BulkUniversality (B : Band Ω) (H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ)
    (hH : ∀ N ω, (H N ω).IsHermitian) (κ : ℝ) : Prop :=
  ∀ E : ℝ, |E| ≤ 2 - κ → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
    Tendsto (fun N => corrPairing B.P (H N) (hH N) k O E - gueCorrPairing (B.size N) k O E)
      atTop (nhds 0)

variable {B : Band Ω} {H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ}

/-- **External input [51, Theorem 2.2] (Step 1, (2.21))** — Landon–Sosoe–Yau, fixed-energy
universality of Dyson Brownian motion — applied with the local law (Theorem 2.3) for the initial
matrix: for every `τ_* > 0`, the correlation functions of `H_{t_*}`, `t_* = N^{-1+τ_*}`, converge
to those of the GUE.  A hypothesis, not proved here. -/
def DBMUniversality (F : OUFlow B H) (κ : ℝ) : Prop :=
  ∀ τs > (0 : ℝ), ∀ E : ℝ, |E| ≤ 2 - κ → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
    Tendsto (fun N => corrPairing B.P (F.Ht N (B.tPow τs N)) (F.hermitian N _) k O E -
      gueCorrPairing (B.size N) k O E) atTop (nhds 0)

/-- **(2.23)** at energy `E`, for `n` factors, `τ_U`, `c'`, `C`: for `z_1, …, z_n` as in (2.22)
(`|Re z_i - E| ≤ C₀/N`, `N^{-1-τ_U} ≤ Im z_i ≤ N^{-1+τ_U}`),
`|E ∏ Im m_0(z_i) - E ∏ Im m_{t_U}(z_i)| ≤ N^{-c' + C n τ_U}`, `t_U = N^{-1+τ_U}`. -/
def Claim223 (F : OUFlow B H) (E : ℝ) (n : ℕ) (τU c' C : ℝ) : Prop :=
  ∀ C₀ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ z : Fin n → ℂ,
    (∀ i, |(z i).re - E| ≤ C₀ / (B.size N : ℝ) ∧ (B.size N : ℝ) ^ (-1 - τU) ≤ (z i).im ∧
      (z i).im ≤ (B.size N : ℝ) ^ (-1 + τU)) →
    |(∫ ω, ∏ i, (stieltjes (F.Ht N 0 ω) (z i)).im ∂B.P) -
      ∫ ω, ∏ i, (stieltjes (F.Ht N (B.tPow τU N) ω) (z i)).im ∂B.P| ≤
      (B.size N : ℝ) ^ (-c' + C * n * τU)

/-- **Step 2's claim (2.23)**: for every bulk `E` and every `n`, there are `c' > 0`, `C` such
that (2.23) holds for all sufficiently small `τ_U > 0`.  In the paper this is proved in Step 3 from
[70, Lemma 4.18] (2.25), the weak local law (2.26) and the weak QUE (2.27) (see
`que_flow_of_eq747` and `measure_bad_le_of_que` below). -/
def StepTwoClaim (F : OUFlow B H) (κ : ℝ) : Prop :=
  ∀ E : ℝ, |E| ≤ 2 - κ → ∀ n : ℕ, ∃ c' > (0 : ℝ), ∃ C : ℝ, ∃ τ0 > (0 : ℝ),
    ∀ τU, 0 < τU → τU ≤ τ0 → Claim223 F E n τU c' C

/-- **External input [37, Theorem 15.3] + [70, Proposition 4.17] (Step 2, (2.23) ⇒ (2.24))** —
the Green's function comparison theorem: if (2.23) holds at `E`, then for every `k` there is
`τ_U > 0` such that the `k`-point correlation functions of `H_0` and `H_{t_U}`,
`t_U = N^{-1+τ_U}`, have the same limit.  A hypothesis, not proved here. -/
def GreenComparison (F : OUFlow B H) (κ : ℝ) : Prop :=
  ∀ E : ℝ, |E| ≤ 2 - κ →
    (∀ n : ℕ, ∃ c' > (0 : ℝ), ∃ C : ℝ, ∃ τ0 > (0 : ℝ),
      ∀ τU, 0 < τU → τU ≤ τ0 → Claim223 F E n τU c' C) →
    ∀ k : ℕ, ∃ τU > (0 : ℝ), ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
      Tendsto (fun N => corrPairing B.P (F.Ht N 0) (F.hermitian N 0) k O E -
        corrPairing B.P (F.Ht N (B.tPow τU N)) (F.hermitian N _) k O E) atTop (nhds 0)

/-- **Theorem 2.6 (bulk universality)**, by the three-step strategy (pp. 11–12): Step 1 (2.21)
from [51] (`DBMUniversality`), Step 2 (2.23) ⇒ (2.24) from [37, 70] (`GreenComparison`), and the
claim (2.23) (`StepTwoClaim`); then (2.24) + (2.21) with `t_* = t_U` give (2.20) = (2.18). -/
theorem theorem2_6_of_steps (F : OUFlow B H) (hH : ∀ N ω, (H N ω).IsHermitian) {κ : ℝ}
    (h51 : DBMUniversality F κ) (hcomp : GreenComparison F κ) (h223 : StepTwoClaim F κ) :
    BulkUniversality B H hH κ := by
  intro E hE k O hO
  obtain ⟨τU, hτU, h224⟩ := hcomp E hE (h223 E hE) k
  have h221 := h51 τU hτU E hE k O hO
  have h0 : ∀ N, corrPairing B.P (F.Ht N 0) (F.hermitian N 0) k O E =
      corrPairing B.P (H N) (hH N) k O E := fun N =>
    corrPairing_congr B.P (funext (F.start N)) _ _ k O E
  have hsum := (h224 O hO).add h221
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [h0 N]
  ring

/-! #### Step 3: the weak QUE (2.27) for `H_t` from (7.47), and the bad event of (2.29) -/

/-- **T65 placeholder — (7.47)**: for the matrix `H = H_{t_N}` of the flow (2.19) (in the paper
`t = t_U`, "the cases `0 < t < t_U` are handled similarly"), at the spectral parameters of the
proof of Theorem 2.5, `E Tr G E_a G^{(*)} E_b` is approximated by `W⁻¹ ξ (1 - ξ S̃^{(B)})⁻¹_{ab}`,
`S̃^{(B)} = (1-ζ_U) S^{(B)} + ζ_U/L`, `ξ = |m|², m²`, with error `W^δ (Nη)^{-3}`.  In the paper this
follows from (7.29) (`|E L_t - E K_t| ≺ (N η_t)^{-3}`) and the identity in law (7.26), exactly as
(2.8)/(2.9) follow from (2.62)/(2.66); (7.27), (7.28) enter only through (7.29) and (2.26).
To be replaced by T65's theorem. -/
def Eq747 (F : OUFlow B H) (t : ℕ → ℝ) (τ : ℝ) (E : ℕ → ℝ) (ζ : ℕ → ℝ) : Prop :=
  QDExpect B (fun N => F.Ht N (t N)) (B.queZ τ E) (fun N => ThetaTilde (B.L N) (ζ N))

/-- **(2.27): Theorem 2.5 holds for `H_t` with `τ* = c/3`**, from the T65 placeholder (7.47) and
the zero-mode removal of §7.2 (`thetaOsc_ThetaTilde`: `ThetaTilde_sub_ThetaTilde`,
`norm_one_sub_mul_comparable`), for `ζ_U ≤ η/16` (in the paper `ζ_U ∼ N^{-1+τ_U} ≪ η`). -/
theorem que_flow_of_eq747 (F : OUFlow B H) {κ : ℝ} (hκ : 0 < κ) (t : ℕ → ℝ) (E : ℕ → ℝ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (ζ : ℕ → ℝ)
    (hζ : ∀ᶠ N : ℕ in atTop, 0 < ζ N ∧ ζ N ≤ 1 / 2 ∧ ζ N ≤ B.queEtaN (B.c / 3) N / 16)
    (h747 : Eq747 F t (B.c / 3) E ζ) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (F.hermitian N (t N)) a (E N) (B.queEtaN (B.c / 3) N)
        ((B.size N : ℝ) ^ (-(B.c / 3 / 6)))) ≤ ENNReal.ofReal ((B.size N : ℝ) ^ (-(B.c / 3 / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (F.hermitian N (t N)) A (E N) (B.queEtaN (B.c / 3) N) (B.c / 3)) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(B.c / 3 / 6)))) := by
  have hc := B.c_pos
  exact que_literal_of_QDExpect B (by positivity) (by linarith) _ (fun N => F.hermitian N (t N))
    _ E h747 (by norm_num) (thetaOsc_ThetaTilde B hκ (by positivity) E hE ζ hζ)

omit [MeasurableSpace Ω] in
/-- `M_{y,α} = N · 3⁻¹ ∑_{|a - a₀| ≤ 1} ψ_α* (E_a - N⁻¹) ψ_α` for `y ∈ I_{a₀}` (after (2.31)). -/
noncomputable def blockM {L W : ℕ} [NeZero L] {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : Hm.IsHermitian) (a0 : ZMod L) (α : ZMod L × Fin W) : ℂ :=
  ((L * W : ℕ) : ℂ) * ((1 / 3 : ℂ) * ∑ a ∈ ({a0 - 1, a0, a0 + 1} : Finset (ZMod L)),
    eigOverlap hH (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) α α)

omit [MeasurableSpace Ω] in
/-- **`M_{y,α}` as in the paper**: `blockM = N ∑_x |ψ_α(x)|² S°_{xy}`, `S° = S - N⁻¹`,
`y = (a₀, β) ∈ I_{a₀}` (the definition after (2.31); needs `L ≥ 3`). -/
theorem blockM_eq {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : Hm.IsHermitian) (a0 : ZMod L)
    (β : Fin W) (α : ZMod L × Fin W) :
    blockM hH a0 α = ((L * W : ℕ) : ℂ) * ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
      (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹) := by
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
      α α = ∑ p, ((if p.1 = a then (W : ℂ)⁻¹ else 0) - ((L * W : ℕ) : ℂ)⁻¹) *
        ((‖hH.eigenvectorBasis α p‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [← queObs_singleton, queObs_eq_diagonal, eigOverlap_diagonal_self]
    simp
  simp only [blockM, ← hT, hdiag]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, hcard]
  have hS : Svar L W p (a0, β) = (if p.1 ∈ T then (3 : ℂ)⁻¹ else 0) * (W : ℂ)⁻¹ := by
    obtain ⟨b, γ⟩ := p
    rw [Svar_apply, SB_apply, sbKernel]
    simp only [hmemT]
  rw [hS, Finset.sum_ite_eq]
  split_ifs <;> push_cast <;> ring

/-- **The bad event of (2.29) is rare, from QUE**: if (2.12) holds at energy `E` with window `η`
and threshold `θ²` (probability `≤ ε'` for each block `a`), then
`P(∃ α, |λ_α - E| ≤ w, |M_{y,α}| ≥ θ) ≤ 3ε'` for `w ≤ η` (union bound over `|a - a₀| ≤ 1`).
With (2.27) (`τ* = c/3`) this gives `P(B_y) ≤ 3 N^{-c/18}` for `θ = N^{-c/36}`. -/
theorem measure_bad_le_of_que {P : Measure Ω} {L W : ℕ} [NeZero L]
    {Hr : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian)
    {E w η θ ε' : ℝ} (hw : w ≤ η) (hθ : 0 ≤ θ) (a0 : ZMod L)
    (hque : ∀ a, P (queEvent212 hH a E η (θ ^ 2)) ≤ ENNReal.ofReal ε') :
    P {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ w ∧ θ ≤ ‖blockM (hH ω) a0 α‖} ≤
      ENNReal.ofReal (3 * ε') := by
  set T : Finset (ZMod L) := {a0 - 1, a0, a0 + 1} with hT
  have hsub : {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ w ∧ θ ≤ ‖blockM (hH ω) a0 α‖} ⊆
      ⋃ a ∈ T, queEvent212 hH a E η (θ ^ 2) := by
    rintro ω ⟨α, hα, hM⟩
    set x : ZMod L → ℂ := fun a => ((L * W : ℕ) : ℂ) *
      eigOverlap (hH ω) (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) α α with hx
    have hMx : blockM (hH ω) a0 α = (1 / 3 : ℂ) * ∑ a ∈ T, x a := by
      simp only [blockM, hx, ← hT, Finset.mul_sum]; ring_nf
    have hex : ∃ a ∈ T, θ ≤ ‖x a‖ := by
      by_contra hno
      push Not at hno
      have hTne : T.Nonempty := ⟨a0, by simp [hT]⟩
      have h1 : ∑ a ∈ T, ‖x a‖ < ∑ _a ∈ T, θ := Finset.sum_lt_sum_of_nonempty hTne hno
      have h2 : T.card ≤ 3 := Finset.card_le_three
      have h3 : ‖blockM (hH ω) a0 α‖ ≤ (1 / 3) * ∑ a ∈ T, ‖x a‖ := by
        rw [hMx, norm_mul]
        have : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      have h4 : (T.card : ℝ) * θ ≤ 3 * θ := mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hθ
      linarith
    obtain ⟨a, haT, ha⟩ := hex
    refine Set.mem_biUnion haT ⟨α, α, hα.trans hw, hα.trans hw, ?_⟩
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

/-- **The bad event of (2.29) along the flow, from (7.47)**: eventually, for every block `a₀`,
`P(∃ α, |λ_α - E| ≤ N^{-1+c/6}, |M_{y,α}| ≥ N^{-c/36}) ≤ 3 N^{-c/18}` for `H_{t_N}`.
(The paper writes the threshold `N^{-c/18}`; with (2.12) as stated the admissible threshold is
`N^{-τ*/12} = N^{-c/36}`, which only changes `c' = c/18` into `c/36` in (2.33).) -/
theorem measure_bad_flow_of_eq747 (F : OUFlow B H) {κ : ℝ} (hκ : 0 < κ) (t : ℕ → ℝ)
    (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ) (ζ : ℕ → ℝ)
    (hζ : ∀ᶠ N : ℕ in atTop, 0 < ζ N ∧ ζ N ≤ 1 / 2 ∧ ζ N ≤ B.queEtaN (B.c / 3) N / 16)
    (h747 : Eq747 F t (B.c / 3) E ζ) :
    ∀ᶠ N : ℕ in atTop, ∀ a0 : ZMod (B.L N),
      B.P {ω | ∃ α, |(F.hermitian N (t N) ω).eigenvalues α - E N| ≤
          (B.size N : ℝ) ^ (-1 + B.c / 6) ∧
        (B.size N : ℝ) ^ (-(B.c / 36)) ≤ ‖blockM (F.hermitian N (t N) ω) a0 α‖} ≤
      ENNReal.ofReal (3 * (B.size N : ℝ) ^ (-(B.c / 18))) := by
  have hc := B.c_pos
  filter_upwards [(que_flow_of_eq747 F hκ t E hE ζ hζ h747).1, B.eventually_size_rpow_le_W_sq]
    with N hN hWc a0
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hn0 : (0 : ℝ) < (B.size N : ℝ) := by linarith
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hw : (B.size N : ℝ) ^ (-1 + B.c / 6) ≤ B.queEtaN (B.c / 3) N := by
    refine le_trans ?_ (rpow_le_queEta hn1 hW0 hWc)
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hθ : ((B.size N : ℝ) ^ (-(B.c / 36))) ^ 2 = (B.size N : ℝ) ^ (-(B.c / 3 / 6)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
  have e18 : (B.size N : ℝ) ^ (-(B.c / 18)) = (B.size N : ℝ) ^ (-(B.c / 3 / 6)) := by
    congr 1; ring
  rw [e18]
  refine measure_bad_le_of_que (F.hermitian N (t N)) hw (by positivity) a0 fun a => ?_
  rw [hθ]
  exact hN a

end TheoremTwoSix

end RBM

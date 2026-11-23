module

public import RBM1D

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `RBM1D` named in its proof. The
definitions that occur in the statements are those of `RBM1D/MainDefs.lean`.
-/

section
noncomputable section
namespace RBM.Paper
open MeasureTheory Filter Topology RBM RBM.Gauss
open scoped Matrix

/-- Theorem 2.2: delocalization of the bulk eigenvectors. -/
theorem theorem_2_2 (d : Dims) {κ : ℝ} (hκ : 0 < κ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      (band d).P {ω | ∃ p : (band d).Idx N × (band d).Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖((transfer_gauss d).hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            (((transfer_gauss d).hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  theorem2_2 d hκ hτ hD

/-- Theorem 2.3: the local law. -/
theorem theorem_2_3 (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ij : (band d).Idx N × (band d).Idx N,
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) -
            msc (z N) • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ a : ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ <
        ‖((band d).W N : ℂ)⁻¹ * ∑ x : Fin ((band d).W N),
            green ((transfer_gauss d).Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ _u : Unit,
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ <
        ‖(((band d).L N * (band d).W N : ℕ) : ℂ)⁻¹ *
            (green ((transfer_gauss d).Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  theorem2_3 d hκ hτ him_pos him_le_one habs_re him_ge hτ' hD

/-- Theorem 2.4: quantum diffusion. -/
theorem theorem_2_4 (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) :=
  theorem2_4 d hκ hτ him_pos him_le_one habs_re him_ge hτ' hD

/-- Theorem 2.5: quantum unique ergodicity. -/
theorem theorem_2_5 (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ0 : 0 < τ)
    (hτ : τ < (band d).c / 2) (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod ((band d).L N),
      (band d).P (queEvent212 ((transfer_gauss d).hermitian N) a (E N)
          ((band d).queEtaN τ N) (((band d).size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod ((band d).L N)), A.Nonempty →
      (band d).P (queEvent213 ((transfer_gauss d).hermitian N) A (E N)
          ((band d).queEtaN τ N) τ) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) :=
  theorem2_5 d hκ hτ0 hτ E hE

end RBM.Paper
end

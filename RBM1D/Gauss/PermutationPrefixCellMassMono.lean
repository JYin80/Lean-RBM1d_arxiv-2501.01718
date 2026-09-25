import RBM1D.Gauss.PermutationPrefixCellMass
import RBM1D.Gauss.PermutationPrefixCellMono

/-!
Uniform mass of an actual permutation-prefix cell is antitone as more
coordinates are revealed. This is a finite measure monotonicity statement;
it does not assert a conditional law.
-/

open MeasureTheory

namespace RBM.Gauss

/-- The uniform mass of an actual-prefix cell decreases as reveal time
increases. -/
theorem uniformPerm_prefixCell_mass_antitone (W k l : ℕ) (hkl : k ≤ l)
    (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W l π} ≤
      uniformPerm W {ρ | ρ ∈ prefixCell W k π} := by
  apply measure_mono
  intro ρ hρ
  exact prefixCell_subset_of_le W k l hkl π hρ

/-- At reveal time zero, the actual-prefix cell has full uniform mass. -/
theorem uniformPerm_prefixCell_mass_antitone_zero (W : ℕ) (π : PermΩ W) :
    uniformPerm W {ρ | ρ ∈ prefixCell W 0 π} = 1 :=
  uniformPerm_prefixCell_zero_mass W π

/-- At width zero, every actual-prefix cell has mass one. -/
theorem uniformPerm_prefixCell_mass_antitone_zero_width (k : ℕ)
    (π : PermΩ 0) :
    uniformPerm 0 {ρ | ρ ∈ prefixCell 0 k π} = 1 :=
  uniformPerm_prefixCell_zero_width_mass k π

/-- For width two, revealing the first coordinate reduces the identity cell
from mass one to mass one half, so the general antitonicity can be strict. -/
theorem uniformPerm_prefixCell_mass_antitone_two_strict_witness :
    uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} = 1 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 (Equiv.refl (Fin 2))} =
        (1 : ENNReal) / 2 ∧
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 (Equiv.refl (Fin 2))} <
        uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} := by
  refine ⟨?_, ?_, ?_⟩
  · exact uniformPerm_prefixCell_zero_mass 2 _
  · exact uniformPerm_prefixCell_two_one_witness.2.2.2.1
  · calc
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 1 (Equiv.refl (Fin 2))} =
        (1 : ENNReal) / 2 :=
        uniformPerm_prefixCell_two_one_witness.2.2.2.1
      _ < 1 := by norm_num
      _ = uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} :=
        (uniformPerm_prefixCell_zero_mass 2 _).symm

#print axioms uniformPerm_prefixCell_mass_antitone
#print axioms uniformPerm_prefixCell_mass_antitone_zero
#print axioms uniformPerm_prefixCell_mass_antitone_zero_width
#print axioms uniformPerm_prefixCell_mass_antitone_two_strict_witness

end RBM.Gauss

/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.DBMInput
import RBM1D.Flow.EnergyUniformReg

/-!
# The averaged band local law from Theorem 2.21 with the `Reg` step condition

`RBM.Gauss.bandTracialLocalLaw_of_Thm221NoELNReg` derives the averaged band local law
`BandTracialLocalLaw` (Theorem 2.3) for the Gaussian sample from `RBM.Thm221NoELNReg`.

## Main declaration

* `RBM.Gauss.bandTracialLocalLaw_of_Thm221NoELNReg` — `Thm221NoELNReg (sample d) κ` gives
  `BandTracialLocalLaw d κ`, via `RBM.SpecSeqN.boundsCoreN'` and
  `RBM.localSemicircleLaw_of_boundsCoreN_of_z` (`Flow/EnergyUniform.lean`), the route that
  needs only (2.68)–(2.70), not (2.71).
-/

namespace RBM.Gauss

variable (d : Dims)

/-- **`Thm221NoELNReg` for the Gaussian sample gives the averaged band local law** (Theorem 2.3):
`RBM.Thm221NoELNReg.toThm221NoELN'` into `RBM.SpecSeqN.boundsCoreN'`, then the third conjunct
of `RBM.localSemicircleLaw_of_boundsCoreN_of_z`. -/
theorem bandTracialLocalLaw_of_Thm221NoELNReg {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELNReg (sample d) κ) : BandTracialLocalLaw d κ :=
  fun _τ hτ _z him_pos him_le_one habs_re him_ge _τ' hτ' _D hD =>
    (localSemicircleLaw_of_boundsCoreN_of_z (transfer_gauss d) (transferLoop1_gauss d) hκ
      him_pos him_le_one habs_re him_ge
      ((SpecSeqN.of_z him_pos him_le_one habs_re him_ge).boundsCoreN' (sample d) hκ
        (hT.toThm221NoELN' hκ) hτ)
      hτ' hD).2.2

end RBM.Gauss

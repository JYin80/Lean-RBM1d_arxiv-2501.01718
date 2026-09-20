/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Green.Minor

/-!
# The minor resolvent does not read row `i`

The large deviation estimates of T81/T82 rest on one structural fact: `G^(i)`, the resolvent of
`H` with row and column `i` removed, is a function of the coordinates **outside** row `i`, hence
independent of the Gaussian entries `H_{ik}`, `k ≠ i`, that multiply it.

Here that fact is proved in the form the model needs: if two sample points agree on every
coordinate whose index pair avoids `i`, then

* the entries `X_{kl}`, `k, l ≠ i`, agree (`Xentry_congr_of_ne`),
* hence the minor matrices agree (`Hflow_submatrix_congr`),
* hence, where the resolvents exist, the minor Green functions agree
  (`greenMinor_congr_of_offRow`).

The last statement is exactly "`G^(i)` is `FinDep` with a witness set avoiding row `i`", in the
concrete form used by the moment computations.
-/

namespace RBM.Gauss

open MeasureTheory

variable {d : Dims} {N : ℕ}

/-- Two sample points **agree off row `i`** when every coordinate at size `N` whose index pair
avoids `i` carries the same value. -/
def AgreeOffRow (d : Dims) (N : ℕ) (i : d.Idx N) (ω ω' : Ω d) : Prop :=
  ∀ (k l : d.Idx N) (b : Bool), k ≠ i → l ≠ i → ω ⟨N, k, l, b⟩ = ω' ⟨N, k, l, b⟩

/-- The entries of `X` away from row and column `i` only read coordinates that avoid `i`. -/
theorem Xentry_congr_of_ne {i : d.Idx N} {ω ω' : Ω d} (h : AgreeOffRow d N i ω ω')
    {k l : d.Idx N} (hk : k ≠ i) (hl : l ≠ i) :
    Xentry d N ω k l = Xentry d N ω' k l := by
  unfold Xentry
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` at `i` only reads coordinates that avoid `i`. -/
theorem Hflow_submatrix_congr (u : ℝ) {i : d.Idx N} {ω ω' : Ω d} (h : AgreeOffRow d N i ω ω') :
    (Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
      = (Hflow d N u ω').submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N) := by
  ext k l
  simp only [Matrix.submatrix_apply, Hflow_apply]
  rw [Xentry_congr_of_ne h k.2 l.2]

/-- **`G^(i)` does not read row `i`.**  Where both resolvents exist and both diagonal entries
are nonzero, the minor Green function at `i` is unchanged by the coordinates of row `i`. -/
theorem greenMinor_congr_of_offRow (u : ℝ) (z : ℂ) {i : d.Idx N} {ω ω' : Ω d}
    (h : AgreeOffRow d N i ω ω')
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hdet' : IsUnit (Hflow d N u ω' - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGii : green (Hflow d N u ω) z i i ≠ 0)
    (hGii' : green (Hflow d N u ω') z i i ≠ 0) (k l : {a : d.Idx N // a ≠ i}) :
    greenMinor (green (Hflow d N u ω) z) i k.1 l.1
      = greenMinor (green (Hflow d N u ω') z) i k.1 l.1 := by
  have e := inv_minor_resolvent hdet i hGii
  have e' := inv_minor_resolvent hdet' i hGii'
  have hsub := Hflow_submatrix_congr (d := d) (N := N) u h
  have : minorGreen (green (Hflow d N u ω) z) i = minorGreen (green (Hflow d N u ω') z) i := by
    rw [← e, ← e', hsub]
  exact congrFun (congrFun this k) l

end RBM.Gauss

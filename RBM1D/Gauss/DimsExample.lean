/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.TraceMoment

/-!
# Inhabitants of `RBM.Gauss.Dims` — the satisfiability witness of the whole Gaussian layer

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, (2.2).

Everything in `RBM1D/Gauss/` is quantified over `d : RBM.Gauss.Dims` (and everything in
`RBM1D/Flow/` over `B : RBM.Band Ω`, of which `RBM.Gauss.band d` is the Gaussian instance).
If `Dims` were empty, all of it would be **vacuously true** and the compiler would never say
so.  This file removes that risk by exhibiting inhabitants.

## The two witnesses

* `RBM.Gauss.Dims.example` — `L ≡ 3`, `W N = max 1 ⌊N/3⌋`, `c = 1/4`.  The minimal number of
  blocks allowed by `three_le_L`, with `W ∼ N/3`.
* `RBM.Gauss.Dims.exampleGrow` — `L N = max 3 ⌊√⌊√N⌋⌋ ∼ N^{1/4}`, `W N = max 1 ⌊N / L N⌋
  ∼ N^{3/4}`, `c = 1/8`.  Here **both** `W N → ∞` and `L N → ∞`
  (`RBM.Gauss.Dims.tendsto_growL`, `RBM.Gauss.Dims.tendsto_growW`), so the witness is not
  degenerate in either direction: it is a genuine one-dimensional band matrix with a growing
  number of blocks, and (2.2) `W ≥ N^{1/2+c}` holds with room to spare
  (`N^{3/4}` against the required `N^{5/8}`).

Both satisfy the four conditions of `Dims` verbatim: `W_pos`, `three_le_L`,
`dim` (`∀ᶠ N, W L ≤ N ≤ 2 W L`) and `bandwidth` (**(2.2)**, `∀ᶠ N, N^{1/2+c} ≤ W`).
**No field of `Dims` is weakened.**

## Satisfiability one level down

`Dims` being inhabited is only the zeroth condition.  The file also records, for
`Dims.example`:

* `RBM.Gauss.Dims.nonempty_Idx` — the matrix index type `ZMod (L N) × Fin (W N)` is nonempty
  (an empty index type would make every matrix statement vacuous);
* `RBM.Gauss.Dims.exists_Sblk_pos` — the variance profile `S` is **not** identically zero, so
  the Gaussian matrix `X` is genuinely random; a model with `S ≡ 0` would have `X = 0`
  pointwise and would satisfy the letter of many estimates while carrying no content.
  (This is the `ω = 0` failure mode of `docs/STATUS.md` T164.)
* `RBM.Gauss.Dims.opNormBound_example` — the structure `RBM.Gauss.OpNormBound` is inhabited at
  this `d`; it is a theorem since T109 (`RBM.Gauss.opNormBound_gauss`), not a hypothesis.

`RBM.Gauss.band d` and `RBM.Gauss.sample d` are *definitions*, so they are inhabited as soon
as `Dims` is; this is recorded as `RBM.Gauss.Dims.band_example` / `Dims.sample_example`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-! ### A `rpow`-to-`pow` bridge

The only analytic content in (2.2) for these witnesses: turning `N^{m/n} ≤ W` into the
polynomial inequality `N^m ≤ W^n`. -/

/-- `x ^ (m / n) ≤ y` follows from the polynomial inequality `x ^ m ≤ y ^ n`.
Here `x ^ (m / n)` is `Real.rpow` and `x ^ m`, `y ^ n` are `Monoid.npow`. -/
theorem rpow_div_le_of_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {m n : ℕ} (hn : n ≠ 0)
    (h : x ^ m ≤ y ^ n) : x ^ ((m : ℝ) / (n : ℝ)) ≤ y := by
  refine le_of_pow_le_pow_left₀ hn hy ?_
  have hpow : (x ^ ((m : ℝ) / (n : ℝ))) ^ n = x ^ m := by
    rw [← Real.rpow_natCast (x ^ ((m : ℝ) / (n : ℝ))) n, ← Real.rpow_mul hx,
      div_mul_cancel₀ _ (by exact_mod_cast hn : (n : ℝ) ≠ 0), Real.rpow_natCast]
  rw [hpow]
  exact h

namespace Dims

/-! ### Witness 1: `L ≡ 3`, `W = ⌊N/3⌋`, `c = 1/4` -/

/-- **(2.2) for `L ≡ 3`, `W = ⌊N/3⌋`, `c = 1/4`.**  The polynomial form is
`N^3 ≤ ⌊N/3⌋^4`, true from `N ≥ 100`. -/
theorem bandwidth_three :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 4) ≤ ((max 1 (N / 3) : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop 100] with N hN
  have hnat : 33 ≤ max 1 (N / 3) ∧ N ≤ 3 * max 1 (N / 3) + 2 := by omega
  obtain ⟨h33, hle⟩ := hnat
  set W : ℕ := max 1 (N / 3) with hW
  have hW33 : (33 : ℝ) ≤ (W : ℝ) := by exact_mod_cast h33
  have hNle : (N : ℝ) ≤ 3 * (W : ℝ) + 2 := by exact_mod_cast hle
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hexp : (1 : ℝ) / 2 + 1 / 4 = ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by norm_num
  rw [hexp]
  refine rpow_div_le_of_pow_le hN0 (by positivity) (by norm_num) ?_
  have hW0 : (0 : ℝ) < (W : ℝ) := by linarith
  have h1 : (N : ℝ) ^ (3 : ℕ) ≤ (3 * (W : ℝ) + 2) ^ (3 : ℕ) := pow_le_pow_left₀ hN0 hNle 3
  have h2 : (3 * (W : ℝ) + 2) ^ (3 : ℕ) ≤ (W : ℝ) ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hW33) (pow_nonneg hW0.le 3),
      mul_nonneg (sub_nonneg.2 hW33) (pow_nonneg hW0.le 2),
      mul_nonneg (sub_nonneg.2 hW33) hW0.le, hW33, hW0]
  linarith

/-- **An inhabitant of `RBM.Gauss.Dims`**: three blocks of size `⌊N/3⌋`, `c = 1/4`.
All four conditions hold verbatim; nothing is weakened. -/
noncomputable def «example» : Dims where
  W := fun N => max 1 (N / 3)
  L := fun _ => 3
  W_pos := fun N => by omega
  three_le_L := fun _ => le_refl 3
  dim := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    omega
  c := 1 / 4
  c_pos := by norm_num
  bandwidth := bandwidth_three

@[simp] theorem example_W (N : ℕ) : «example».W N = max 1 (N / 3) := rfl
@[simp] theorem example_L (N : ℕ) : «example».L N = 3 := rfl
@[simp] theorem example_c : «example».c = 1 / 4 := rfl

/-! ### Witness 2: `L ∼ N^{1/4}` blocks of size `W ∼ N^{3/4}`, `c = 1/8`

The point of this second witness is that `L ≡ 3` is the *minimum* allowed by `three_le_L`,
so it says nothing about models with many blocks — which is the regime the paper is about.
Here `L N → ∞` and `W N → ∞`. -/

/-- `L N = max 3 ⌊√⌊√N⌋⌋`, i.e. `≈ N^{1/4}` blocks. -/
def growL (N : ℕ) : ℕ := max 3 (Nat.sqrt (Nat.sqrt N))

/-- `W N = max 1 ⌊N / L N⌋`, i.e. blocks of size `≈ N^{3/4}`. -/
def growW (N : ℕ) : ℕ := max 1 (N / growL N)

theorem three_le_growL (N : ℕ) : 3 ≤ growL N := le_max_left _ _

/-- `L N ^ 4 ≤ N` — the defining property of "`L` is at most `N^{1/4}`". -/
theorem growL_pow_le (N : ℕ) (hN : 81 ≤ N) : growL N ^ 4 ≤ N := by
  have hq : Nat.sqrt (Nat.sqrt N) ^ 4 ≤ N := by
    have h1 : Nat.sqrt (Nat.sqrt N) ^ 2 ≤ Nat.sqrt N := Nat.sqrt_le' _
    have h2 : Nat.sqrt N ^ 2 ≤ N := Nat.sqrt_le' _
    calc Nat.sqrt (Nat.sqrt N) ^ 4 = (Nat.sqrt (Nat.sqrt N) ^ 2) ^ 2 := by ring
      _ ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ N := h2
  rcases le_total 3 (Nat.sqrt (Nat.sqrt N)) with h | h
  · rwa [growL, max_eq_right h]
  · rw [growL, max_eq_left h]; omega

theorem twentyseven_mul_growL_le (N : ℕ) (hN : 81 ≤ N) : 27 * growL N ≤ N := by
  have h3 := three_le_growL N
  have h4 := growL_pow_le N hN
  have hcube : 27 ≤ growL N ^ 3 := by simpa using Nat.pow_le_pow_left h3 3
  calc 27 * growL N ≤ growL N ^ 3 * growL N := Nat.mul_le_mul_right _ hcube
    _ = growL N ^ 4 := by ring
    _ ≤ N := h4

theorem growW_eq (N : ℕ) (hN : 81 ≤ N) : growW N = N / growL N := by
  have h3 := three_le_growL N
  have h27 := twentyseven_mul_growL_le N hN
  have hL0 : 0 < growL N := by omega
  rw [growW, max_eq_right]
  exact (Nat.one_le_div_iff hL0).2 (by omega)

theorem dim_grow :
    ∀ᶠ N : ℕ in atTop, growW N * growL N ≤ N ∧ N ≤ 2 * (growW N * growL N) := by
  filter_upwards [eventually_ge_atTop 256] with N hN
  have h3 := three_le_growL N
  have h27 := twentyseven_mul_growL_le N (by omega)
  have hL0 : 0 < growL N := by omega
  rw [growW_eq N (by omega)]
  have hmle : N / growL N * growL N ≤ N := Nat.div_mul_le_self N _
  have hmod : N % growL N + N / growL N * growL N = N := Nat.mod_add_div' N _
  have hmlt : N % growL N < growL N := Nat.mod_lt _ hL0
  omega

/-- The arithmetic core of (2.2) for the growing-`L` witness: with `a = N`, `l = L N`,
`w = W N`, the hypotheses `27 l ≤ a`, `l^4 ≤ a`, `a - l ≤ w l` and `256 ≤ a` give
`a^5 ≤ w^8`, i.e. `N^{5/8} ≤ W`. -/
theorem pow_five_le_pow_eight {a l w : ℝ} (ha256 : (256 : ℝ) ≤ a) (h27 : 27 * l ≤ a)
    (hl4 : l ^ 4 ≤ a) (hwl : a - l ≤ w * l) : a ^ 5 ≤ w ^ 8 := by
  have hal : (0 : ℝ) ≤ a - l := by linarith
  have s1 : (a - l) ^ 4 ≤ w ^ 4 * a := by
    calc (a - l) ^ 4 ≤ (w * l) ^ 4 := pow_le_pow_left₀ hal hwl 4
      _ = w ^ 4 * l ^ 4 := by ring
      _ ≤ w ^ 4 * a := mul_le_mul_of_nonneg_left hl4 (by positivity)
  have s2 : (a - l) ^ 8 ≤ w ^ 8 * a ^ 2 := by
    calc (a - l) ^ 8 = ((a - l) ^ 4) ^ 2 := by ring
      _ ≤ (w ^ 4 * a) ^ 2 := pow_le_pow_left₀ (by positivity) s1 2
      _ = w ^ 8 * a ^ 2 := by ring
  have s3 : a ^ 7 ≤ (a - l) ^ 8 := by
    have hhalf : a / 2 ≤ a - l := by linarith
    have h1 : (a / 2) ^ 8 ≤ (a - l) ^ 8 := pow_le_pow_left₀ (by linarith) hhalf 8
    have h2 : a ^ 7 ≤ (a / 2) ^ 8 := by
      have he : (a / 2) ^ 8 = a ^ 8 / 256 := by ring
      rw [he, le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
      calc a ^ 7 * 256 ≤ a ^ 7 * a := mul_le_mul_of_nonneg_left ha256 (by positivity)
        _ = a ^ 8 := by ring
    linarith
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  refine le_of_mul_le_mul_right ?_ ha2
  calc a ^ 5 * a ^ 2 = a ^ 7 := by ring
    _ ≤ (a - l) ^ 8 := s3
    _ ≤ w ^ 8 * a ^ 2 := s2

/-- **(2.2) for the growing-`L` witness**, with `c = 1/8`: `N^{5/8} ≤ W N ≈ N^{3/4}`. -/
theorem bandwidth_grow :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤ (growW N : ℝ) := by
  filter_upwards [eventually_ge_atTop 256] with N hN
  have h3 := three_le_growL N
  have h27 := twentyseven_mul_growL_le N (by omega)
  have hL4 := growL_pow_le N (by omega)
  have hL0 : 0 < growL N := by omega
  have hmod : N % growL N + N / growL N * growL N = N := Nat.mod_add_div' N _
  have hmlt : N % growL N < growL N := Nat.mod_lt _ hL0
  have hnat : N ≤ growW N * growL N + growL N := by rw [growW_eq N (by omega)]; omega
  have ha256 : (256 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h27r : 27 * (growL N : ℝ) ≤ (N : ℝ) := by exact_mod_cast h27
  have hL4r : (growL N : ℝ) ^ 4 ≤ (N : ℝ) := by exact_mod_cast hL4
  have hwl : (N : ℝ) - (growL N : ℝ) ≤ (growW N : ℝ) * (growL N : ℝ) := by
    have h : (N : ℝ) ≤ (growW N : ℝ) * (growL N : ℝ) + (growL N : ℝ) := by exact_mod_cast hnat
    linarith
  have s4 : (N : ℝ) ^ 5 ≤ (growW N : ℝ) ^ 8 := pow_five_le_pow_eight ha256 h27r hL4r hwl
  have hexp : (1 : ℝ) / 2 + 1 / 8 = ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) := by norm_num
  rw [hexp]
  exact rpow_div_le_of_pow_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) s4

/-- **A non-degenerate inhabitant of `RBM.Gauss.Dims`**: `≈ N^{1/4}` blocks of size
`≈ N^{3/4}`, `c = 1/8`.  Both `W N → ∞` and `L N → ∞`. -/
noncomputable def exampleGrow : Dims where
  W := growW
  L := growL
  W_pos := fun N => by
    have : 1 ≤ growW N := le_max_left _ _
    omega
  three_le_L := three_le_growL
  dim := dim_grow
  c := 1 / 8
  c_pos := by norm_num
  bandwidth := bandwidth_grow

@[simp] theorem exampleGrow_W (N : ℕ) : exampleGrow.W N = growW N := rfl
@[simp] theorem exampleGrow_L (N : ℕ) : exampleGrow.L N = growL N := rfl
@[simp] theorem exampleGrow_c : exampleGrow.c = 1 / 8 := rfl

/-- The number of blocks really does grow: `L N → ∞`.  (With `Dims.example` it is constant
`3`, the minimum `three_le_L` allows, which is why the second witness is here.) -/
theorem tendsto_growL : Tendsto growL atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  filter_upwards [eventually_ge_atTop (k ^ 4)] with N hN
  have h1 : k ^ 2 ≤ Nat.sqrt N :=
    Nat.le_sqrt'.2 (by calc (k ^ 2) ^ 2 = k ^ 4 := by ring
                        _ ≤ N := hN)
  exact le_trans (Nat.le_sqrt'.2 h1) (le_max_right _ _)

/-- The block size grows too: `W N ≥ L N ^ 3 → ∞`.  Together with `tendsto_growL` this says
the second witness is degenerate in neither direction. -/
theorem tendsto_growW : Tendsto growW atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  filter_upwards [tendsto_atTop.1 tendsto_growL k, eventually_ge_atTop 81] with N hk hN
  have h3 := three_le_growL N
  have hL0 : 0 < growL N := by omega
  have h4 := growL_pow_le N hN
  have hdiv : growL N ^ 3 ≤ N / growL N :=
    (Nat.le_div_iff_mul_le hL0).2 (by
      calc growL N ^ 3 * growL N = growL N ^ 4 := by ring
        _ ≤ N := h4)
  rw [growW_eq N hN]
  exact le_trans hk (le_trans (Nat.le_self_pow (by norm_num) _) hdiv)

/-! ### `Dims` is inhabited, and so is everything built on it -/

/-- **`RBM.Gauss.Dims` is inhabited.**  The zeroth satisfiability condition of the whole
Gaussian layer. -/
theorem nonempty : Nonempty Dims := ⟨«example»⟩

example : Nonempty Dims := ⟨«example»⟩

example : Nonempty Dims := ⟨exampleGrow⟩

/-- The band model of `RBM1D/Flow/Hypotheses.lean` is inhabited. -/
noncomputable def band_example : RBM.Band (Ω «example») := band «example»

/-- The `RBM.Sample` of the moment route is inhabited. -/
noncomputable def sample_example : RBM.Sample (band «example») := sample «example»

/-- The sample space is nonempty. -/
theorem nonempty_Omega : Nonempty (Ω «example») := ⟨fun _ => 0⟩

/-- **The matrix index type is nonempty**, for every `N` and every `d : Dims`.  An empty index
type would make every entrywise statement about `X` vacuous. -/
theorem nonempty_Idx (d : Dims) (N : ℕ) : Nonempty (d.Idx N) :=
  ⟨(0, ⟨0, d.W_pos N⟩)⟩

/-- **The variance profile is not identically zero.**  Since `E|X_ij|² = S_ij`
(`RBM.Gauss.integral_normSq_Xentry`), a model with `S ≡ 0` would have `X = 0` almost surely
and would satisfy the letter of most estimates while carrying no content; this rules that out
for every `d : Dims`. -/
theorem exists_Sblk_pos (d : Dims) (N : ℕ) (i : d.Idx N) :
    ∃ j : d.Idx N, 0 < Sblk (d.L N) (d.W N) i j := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ j, Sblk (d.L N) (d.W N) i j = 1 := sum_Sblk_row (d.three_le_L N) i
  have hle : ∑ j, Sblk (d.L N) (d.W N) i j ≤ 0 :=
    Finset.sum_nonpos fun j _ => hcon j
  rw [hsum] at hle
  norm_num at hle

/-- **`RBM.Gauss.OpNormBound` is inhabited** — indeed it is a theorem for every `d : Dims`
since T109 (`RBM.Gauss.opNormBound_gauss`), so the moment route no longer carries it as a
hypothesis. -/
theorem opNormBound_example : OpNormBound «example» := opNormBound_gauss _

end Dims

end RBM.Gauss

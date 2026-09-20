/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator

/-!
# The quadratic large deviation estimate (Hanson–Wright), Gaussian case — T82

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, the quadratic form of (4.7), i.e. `RBM.LDEQuad` of `RBM1D/Green/EntryBound.lean`:

`‖∑_{k,l ≠ i} H_{ik} B_{kl} H_{li} − t ∑_{k ≠ i} S_{ik} B_{kk}‖² ≺ ∑_{k,l} S_{ik}‖B_{kl}‖² S_{li}`

with `B = G^{(i)}` independent of row `i`.  The left-hand side is a **centred second order
Gaussian chaos**; this file develops it by the route the ticket prescribes — Gaussian
integration by parts (`MatrixStein`-style), producing a *moment recursion*, rather than a Wick
expansion with pairing combinatorics.

## The abstract setting: `RBM.Gauss.RowChaos`

Everything is done for an abstract *row chaos* (`RowChaos d κ`), which is exactly the data the
quadratic form at a fixed row `i` presents:

* an index type `κ` (in the application `{k // k ≠ i}`);
* two Gaussian coordinates `co k true`, `co k false` per index, all distinct, with equal
  variance `w k` — the real and imaginary parts of `H_{ik}`;
* a sign `eps k = ±1` and a scale `r` (in the application `r = √t`, since `H_t = √t X`), giving
  the row entry `h_k = r (ω_{co k tt} + ε_k i ω_{co k ff})`, hence `E|h_k|² = σ_k := 2 r² w_k`;
* a matrix `B`, continuous, **globally bounded**, and **not reading any coordinate `co k b`**.

That last field, `B_free` (together with `Ifree_free`), *is* the row independence hypothesis:
"`B` is `FinDep` with a witness set containing no row-`i` coordinate".  It is what T84
(`RBM1D/Gauss/CondRow.lean`) is to supply for `B = G^{(i)}`.

The chaos, its control and the two error terms are

* `chaos ω = ∑_{k,l} h_k B_{kl} \bar h_l − ∑_k σ_k B_{kk}`  (`Q`);
* `U_k = ∑_l B_{kl} \bar h_l`, `V_k = ∑_m h_m B_{mk}`;
* `Tq = ∑_k σ_k (‖U_k‖² + ‖V_k‖²)`  (`T`), `Rq = ∑_k σ_k U_k V_k`  (`R`), with `‖R‖ ≤ T/2`;
* `Vq = ∑_{k,l} σ_k ‖B_{kl}‖² σ_l`  — the paper's right-hand side.

## Main results

* `RBM.Gauss.RowChaos.hasDerivAt_chaos_true` / `_false` — `∂_{a_k}Q = dA_k`, `∂_{b_k}Q = dB_k`.
* `RBM.Gauss.RowChaos.sum_coord_mul_deriv` — **Euler's identity**
  `∑_α ω_α ∂_α Q = 2(Q + ∑_k σ_k B_{kk})`.
* `RBM.Gauss.RowChaos.integral_chaos_mul` — **the master integration-by-parts identity**:
  `2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q ∂_{a_k}F + ∂_{b_k}Q ∂_{b_k}F)` for every tame `F`.
* `RBM.Gauss.RowChaos.moment_recursion` — with `F = Q^q \bar Q^{q+1}`,
  `2 E|Q|^{2(q+1)} = 2q E[R Q^{q−1}\bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`.
* `RBM.Gauss.RowChaos.two_mul_mom_succ_le` — **the Hanson–Wright recursion**,
  `2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`.
* `RBM.Gauss.RowChaos.mom_succ_le` — **the moment bound**
  `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`, `p ≥ 1`: the recursion closed by the pointwise Young
  inequality `RBM.Gauss.young_pow` with the rational parameter `K = 2p−1` (no `rpow`, no
  Hölder inequality).
* `RBM.Gauss.RowChaos.integral_conj_h_mul_h` — **the row isometry**
  `E[\bar h_l h_{l'} Z] = δ_{l l'} σ_l E[Z]` for `Z` not reading the row; hence
  `integral_U_conj_U`, `integral_V_conj_V`, `momT_zero`.
* `RBM.Gauss.RowChaos.mom_one` — **the variance, the case `p = 1`**: `E|Q|² = E[Vq]`, exactly.
* `RBM.Gauss.RowChaos.norm_chaos_sq_eq_ldeQuadLHS`, `RBM.Gauss.RowChaos.Vq_eq_ldeQuadRHS` —
  the two sides are literally `RBM.ldeQuadLHS` and `t²·RBM.ldeQuadRHS` (pure reindexing);
  `RBM.Gauss.RowChaos.integral_ldeQuadLHS_eq` states the variance in the paper's notation.

## Hypotheses carried (nothing here is an `axiom`, nothing is `sorry`)

`RBM.Gauss.GaussIBP d` has two fields, both properties of the product measure `P d` alone:

* `stein` — `E[ω_c g] = gvar_c E[∂_c g]` for `Tame` `g` (continuous, finitely dependent,
  **polynomially** bounded).  This is `RBM.Gauss.MatrixStein.stein` of T70/T71 with *global
  boundedness* relaxed to polynomial growth.  The relaxation is forced: the integrands of a
  second order chaos are genuine polynomials in the Gaussian coordinates and are never
  bounded.  It is the same one-dimensional integration by parts
  (`RBM.integral_mul_gaussianReal`, proved in `RBM1D/Gauss/Stein.lean`) pushed through
  `RBM.Gauss.P_map_restrict`; from `MatrixStein` it follows by a smooth cutoff
  `χ_n(ω) = η(∑_{c ∈ I}(ω c)²/n²)`, whose derivative is `O(1/n)` on its support.
* `polyInt` — all polynomial moments of `P d` are finite.

## What is **not** done here

1. **The positive-chaos moment bound `E[T^p] ≤ C_p E[Vq^p]`.**  This is the one mathematical
   gap: `mom_succ_le` gives `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`, and `T` must still be traded for
   the paper's `Vq = ∑_{k,l}σ_k‖B_{kl}‖²σ_l`.  At `p = 1` it is an identity
   (`momT_zero`: `E[T] = 2E[Vq]`).  For general `p` the textbook proof is Jensen with the
   *random* weights `σ_k E[‖U_k‖² | B]`, which needs the conditional expectation of T84.  A
   conditioning-free proof runs the same integration by parts on `E[T^p]`: the derivation
   `D_l = r ∂_{a_l} − r ε_l i ∂_{b_l}` satisfies `D_l U_k = 0`, `D_l \bar V_k = 0`,
   `D_l \bar U_k = 2r² \bar B_{kl}`, `D_l V_k = 2r² B_{lk}`, whence
   `E[T^p] ≤ c_p E[Vq T^{p−1}]` after a Frobenius-norm bound on the cross term, and then
   `young_pow` again.  Neither is done here.
2. **The instance.**  No `RowChaos` is built for the model: that needs `co`, `eps` read off
   `RBM.Gauss.Xentry` (an `idxKey` case analysis), plus *global* continuity and boundedness of
   `ω ↦ greenMinor (green (Hflow d N u ω) z) i`, and `B_free` in unconditional form.  Those are
   T84/T85 territory; `norm_chaos_sq_eq_ldeQuadLHS` and `Vq_eq_ldeQuadRHS` are the interface
   they plug into.
3. **The `StochDom` endgame.**  Turning the moment bound into `RBM.StochDom` needs
   `RBM.Gauss.stochDom_of_momentDom` (T73), whose control is *deterministic*, while
   `RBM.LDEQuad`'s control `ldeQuadRHS` is random; `RBM.StochDom.of_det` is the shape the rest
   of `Green/EntryBound.lean` uses.

## Deviations from the paper (for `docs/paper-deltas.md`)

* The variance identity carries a factor `t²`: `E[ldeQuadLHS] = t² E[ldeQuadRHS]`, because
  `E|H_{ik}|² = t S_{ik}` for the flow `H_t = √t X` while `ldeQuadRHS` is written with `S` and
  not `tS`.  Since `t ≤ 1` this only strengthens the paper's statement (see the note at the
  head of `RBM1D/Green/EntryBound.lean`, which already records the same convention for the row
  and column estimates).
* The centring constant is `∑_k σ_k B_{kk}` with `σ_k = E|h_k|²`; the paper writes
  `t ∑_k S_{ik} B_{kk}`.  These agree in the model (`σ_k = t S_{ik}`) and the agreement is a
  hypothesis of the interface lemmas, not an assumption of the theory.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

variable {d : Dims}

/-! ### Polynomial weights -/

/-- `polyW I ω = 1 + ∑_{c ∈ I} |ω c|`, the polynomial weight used to dominate every integrand
of this file. -/
noncomputable def polyW (I : Finset (Coord d)) (ω : Ω d) : ℝ := 1 + ∑ c ∈ I, |ω c|

theorem one_le_polyW (I : Finset (Coord d)) (ω : Ω d) : 1 ≤ polyW I ω := by
  have : (0 : ℝ) ≤ ∑ c ∈ I, |ω c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold polyW; linarith

theorem polyW_pos (I : Finset (Coord d)) (ω : Ω d) : 0 < polyW I ω :=
  lt_of_lt_of_le zero_lt_one (one_le_polyW I ω)

theorem polyW_nonneg (I : Finset (Coord d)) (ω : Ω d) : 0 ≤ polyW I ω :=
  le_trans zero_le_one (one_le_polyW I ω)

theorem polyW_mono {I J : Finset (Coord d)} (h : I ⊆ J) (ω : Ω d) :
    polyW I ω ≤ polyW J ω := by
  have : ∑ c ∈ I, |ω c| ≤ ∑ c ∈ J, |ω c| :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => abs_nonneg _
  unfold polyW; linarith

theorem polyW_pow_le {I J : Finset (Coord d)} (hIJ : I ⊆ J) {n m : ℕ} (hnm : n ≤ m) (ω : Ω d) :
    polyW I ω ^ n ≤ polyW J ω ^ m :=
  le_trans (pow_le_pow_left₀ (polyW_nonneg _ _) (polyW_mono hIJ ω) n)
    (pow_le_pow_right₀ (one_le_polyW J ω) hnm)

/-! ### An elementary Young inequality with natural exponents

`(q+1) a b^q ≤ a^{q+1} + q b^{q+1}` for `a, b ≥ 0`: the arithmetic–geometric mean inequality for
the `q+1` numbers `a, b, …, b`, proved from `a^n - b^n = (a-b)∑ a^i b^{n-1-i}`.  Only natural
powers occur, which is what lets the moment recursion be closed without any `rpow`. -/
theorem young_pow (q : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((q : ℝ) + 1) * (a * b ^ q) ≤ a ^ (q + 1) + (q : ℝ) * b ^ (q + 1) := by
  have hgs : (∑ i ∈ Finset.range (q + 1), a ^ i * b ^ (q + 1 - 1 - i)) * (a - b)
      = a ^ (q + 1) - b ^ (q + 1) := geom_sum₂_mul a b (q + 1)
  set Sm := ∑ i ∈ Finset.range (q + 1), a ^ i * b ^ (q + 1 - 1 - i) with hS
  have hconst : ∑ _i ∈ Finset.range (q + 1), b ^ q = ((q : ℝ) + 1) * b ^ q := by
    rw [Finset.sum_const, Finset.card_range]
    ring
  have key : ((q : ℝ) + 1) * b ^ q * (a - b) ≤ a ^ (q + 1) - b ^ (q + 1) := by
    rcases le_total b a with hab | hab
    · have hge : ((q : ℝ) + 1) * b ^ q ≤ Sm := by
        rw [hS, ← hconst]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
        have hsplit : b ^ q = b ^ i * b ^ (q - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, show q + 1 - 1 - i = q - i from by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hab i) (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hge (sub_nonneg.mpr hab)
      rw [hgs] at hmul
      exact hmul
    · have hle : Sm ≤ ((q : ℝ) + 1) * b ^ q := by
        rw [hS, ← hconst]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
        have hsplit : b ^ q = b ^ i * b ^ (q - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, show q + 1 - 1 - i = q - i from by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab i) (by positivity)
      have hmul := mul_le_mul_of_nonpos_right hle (sub_nonpos.mpr hab)
      rw [hgs] at hmul
      exact hmul
  have expand : ((q : ℝ) + 1) * b ^ q * (a - b)
      = ((q : ℝ) + 1) * (a * b ^ q) - ((q : ℝ) + 1) * b ^ (q + 1) := by
    rw [pow_succ]; ring
  rw [expand] at key
  linarith

/-! ### Tame functions: continuous, finitely dependent, polynomially bounded

Every integrand of this file is a polynomial in finitely many Gaussian coordinates with
coefficients read off a *bounded* matrix.  `Tame` is exactly that class; it is closed under the
ring operations and under complex conjugation, and (given `GaussIBP`) every `Tame` function is
integrable. -/

/-- `f` is **tame**: continuous, reading only finitely many coordinates, and dominated by a
polynomial in finitely many coordinates. -/
structure Tame (d : Dims) (f : Ω d → ℂ) : Prop where
  /-- `f` is continuous. -/
  cont : Continuous f
  /-- `f` reads only finitely many coordinates. -/
  findep : FinDep d f
  /-- `f` is dominated by a polynomial in finitely many coordinates. -/
  poly : ∃ (I : Finset (Coord d)) (n : ℕ) (C : ℝ), ∀ ω, ‖f ω‖ ≤ C * polyW I ω ^ n

namespace Tame

variable {f g : Ω d → ℂ}

theorem const (z : ℂ) : Tame d (fun _ => z) :=
  ⟨continuous_const, ⟨∅, fun _ _ _ => rfl⟩, ⟨∅, 0, ‖z‖, fun ω => by simp⟩⟩

theorem coord (c : Coord d) : Tame d (fun ω : Ω d => (ω c : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp (continuous_apply c),
    ⟨{c}, fun ω ω' h => by
      show ((ω c : ℂ)) = ((ω' c : ℂ))
      rw [h c (Finset.mem_singleton_self c)]⟩, ⟨{c}, 1, 1, fun ω => ?_⟩⟩
  have : |ω c| ≤ polyW ({c} : Finset (Coord d)) ω := by
    unfold polyW; simp
  simpa [Complex.norm_real] using this

theorem add (hf : Tame d f) (hg : Tame d g) : Tame d (fun ω => f ω + g ω) := by
  obtain ⟨I₁, n₁, C₁, h₁⟩ := hf.poly
  obtain ⟨I₂, n₂, C₂, h₂⟩ := hg.poly
  obtain ⟨J₁, hJ₁⟩ := hf.findep
  obtain ⟨J₂, hJ₂⟩ := hg.findep
  refine ⟨hf.cont.add hg.cont, ⟨J₁ ∪ J₂, fun ω ω' h => ?_⟩,
    ⟨I₁ ∪ I₂, max n₁ n₂, C₁ + C₂, fun ω => ?_⟩⟩
  · show f ω + g ω = f ω' + g ω'
    rw [hJ₁ ω ω' fun e he => h e (Finset.mem_union_left _ he),
      hJ₂ ω ω' fun e he => h e (Finset.mem_union_right _ he)]
  · have hC₁ : 0 ≤ C₁ := by
      have hp : (0 : ℝ) < polyW I₁ ω ^ n₁ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f ω), h₁ ω]
    have hC₂ : 0 ≤ C₂ := by
      have hp : (0 : ℝ) < polyW I₂ ω ^ n₂ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (g ω), h₂ ω]
    have e₁ : C₁ * polyW I₁ ω ^ n₁ ≤ C₁ * polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ :=
      mul_le_mul_of_nonneg_left
        (polyW_pow_le Finset.subset_union_left (le_max_left _ _) ω) hC₁
    have e₂ : C₂ * polyW I₂ ω ^ n₂ ≤ C₂ * polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ :=
      mul_le_mul_of_nonneg_left
        (polyW_pow_le Finset.subset_union_right (le_max_right _ _) ω) hC₂
    calc ‖f ω + g ω‖ ≤ ‖f ω‖ + ‖g ω‖ := norm_add_le _ _
      _ ≤ C₁ * polyW I₁ ω ^ n₁ + C₂ * polyW I₂ ω ^ n₂ := add_le_add (h₁ ω) (h₂ ω)
      _ ≤ (C₁ + C₂) * polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ := by linarith

theorem mul (hf : Tame d f) (hg : Tame d g) : Tame d (fun ω => f ω * g ω) := by
  obtain ⟨I₁, n₁, C₁, h₁⟩ := hf.poly
  obtain ⟨I₂, n₂, C₂, h₂⟩ := hg.poly
  obtain ⟨J₁, hJ₁⟩ := hf.findep
  obtain ⟨J₂, hJ₂⟩ := hg.findep
  refine ⟨hf.cont.mul hg.cont, ⟨J₁ ∪ J₂, fun ω ω' h => ?_⟩,
    ⟨I₁ ∪ I₂, n₁ + n₂, C₁ * C₂, fun ω => ?_⟩⟩
  · show f ω * g ω = f ω' * g ω'
    rw [hJ₁ ω ω' fun e he => h e (Finset.mem_union_left _ he),
      hJ₂ ω ω' fun e he => h e (Finset.mem_union_right _ he)]
  · have hC₁ : 0 ≤ C₁ := by
      have hp : (0 : ℝ) < polyW I₁ ω ^ n₁ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f ω), h₁ ω]
    have hC₂ : 0 ≤ C₂ := by
      have hp : (0 : ℝ) < polyW I₂ ω ^ n₂ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (g ω), h₂ ω]
    have e₁ : polyW I₁ ω ^ n₁ ≤ polyW (I₁ ∪ I₂) ω ^ n₁ :=
      polyW_pow_le Finset.subset_union_left le_rfl ω
    have e₂ : polyW I₂ ω ^ n₂ ≤ polyW (I₁ ∪ I₂) ω ^ n₂ :=
      polyW_pow_le Finset.subset_union_right le_rfl ω
    have hp₁ : (0 : ℝ) ≤ polyW (I₁ ∪ I₂) ω ^ n₁ := le_of_lt (pow_pos (polyW_pos _ _) _)
    have hp₂ : (0 : ℝ) ≤ polyW (I₁ ∪ I₂) ω ^ n₂ := le_of_lt (pow_pos (polyW_pos _ _) _)
    calc ‖f ω * g ω‖ = ‖f ω‖ * ‖g ω‖ := norm_mul _ _
      _ ≤ (C₁ * polyW I₁ ω ^ n₁) * (C₂ * polyW I₂ ω ^ n₂) :=
          mul_le_mul (h₁ ω) (h₂ ω) (norm_nonneg _)
            (mul_nonneg hC₁ (le_of_lt (pow_pos (polyW_pos _ _) _)))
      _ ≤ (C₁ * C₂) * polyW (I₁ ∪ I₂) ω ^ (n₁ + n₂) := by
          rw [pow_add]
          have hkey := mul_le_mul e₁ e₂ (le_of_lt (pow_pos (polyW_pos _ _) _)) hp₁
          calc C₁ * polyW I₁ ω ^ n₁ * (C₂ * polyW I₂ ω ^ n₂)
              = C₁ * C₂ * (polyW I₁ ω ^ n₁ * polyW I₂ ω ^ n₂) := by ring
            _ ≤ C₁ * C₂ * (polyW (I₁ ∪ I₂) ω ^ n₁ * polyW (I₁ ∪ I₂) ω ^ n₂) :=
                mul_le_mul_of_nonneg_left hkey (mul_nonneg hC₁ hC₂)

theorem neg (hf : Tame d f) : Tame d (fun ω => -f ω) := by
  obtain ⟨I, n, C, h⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  exact ⟨hf.cont.neg, ⟨J, fun ω ω' hh => by show -f ω = -f ω'; rw [hJ ω ω' hh]⟩,
    ⟨I, n, C, fun ω => by simpa using h ω⟩⟩

theorem sub (hf : Tame d f) (hg : Tame d g) : Tame d (fun ω => f ω - g ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem conj (hf : Tame d f) : Tame d (fun ω => (starRingEnd ℂ) (f ω)) := by
  obtain ⟨I, n, C, h⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  exact ⟨Complex.continuous_conj.comp hf.cont,
    ⟨J, fun ω ω' hh => by
      show (starRingEnd ℂ) (f ω) = (starRingEnd ℂ) (f ω'); rw [hJ ω ω' hh]⟩,
    ⟨I, n, C, fun ω => by simpa using h ω⟩⟩

theorem pow (hf : Tame d f) (n : ℕ) : Tame d (fun ω => f ω ^ n) := by
  induction n with
  | zero => simpa using Tame.const (d := d) 1
  | succ n ih => simpa [_root_.pow_succ] using ih.mul hf

theorem sum {ι : Type*} (s : Finset ι) {F : ι → Ω d → ℂ} (h : ∀ i ∈ s, Tame d (F i)) :
    Tame d (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Tame.const (d := d) 0
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert hi₀] using h₀.add hs

/-- A continuous, finitely dependent, globally bounded function is tame. -/
theorem ofBdd {C : ℝ} (hc : Continuous f) (hd : FinDep d f) (hb : ∀ ω, ‖f ω‖ ≤ C) :
    Tame d f :=
  ⟨hc, hd, ∅, 0, C, fun ω => by simpa using hb ω⟩

end Tame

/-! ### The two facts about `P d` that are consumed here -/

/-- **The Gaussian calculus on `P d`**, in the form this file uses.

* `stein` is `RBM.Gauss.MatrixStein.stein` with the *global boundedness* hypotheses relaxed to
  `Tame` (continuous, finitely dependent, **polynomially** bounded).  The relaxation is
  unavoidable here: the integrands of a second order chaos are genuine polynomials in the
  Gaussian coordinates, so they are never globally bounded.  It is the same one-dimensional
  integration by parts (`RBM.integral_mul_gaussianReal`, proved in `RBM1D/Gauss/Stein.lean`)
  pushed through `RBM.Gauss.P_map_restrict`; from `MatrixStein` it follows by a smooth cutoff
  `χ_n(ω) = η(∑_{c ∈ I} (ω c)²/n²)`, whose derivative is `O(1/n)` on its support.
* `polyInt` is the statement that all polynomial moments of `P d` are finite.

Both are properties of the product measure alone, in the same family as T70's `MatrixStein`;
they are **carried as hypotheses**, exactly like `MatrixStein`, and no `axiom` is introduced. -/
structure GaussIBP (d : Dims) : Prop where
  /-- `E[ω_c · g] = gvar_c · E[∂_c g]` for tame `g`. -/
  stein : ∀ (c : Coord d) (g g' : Ω d → ℂ), Tame d g → Tame d g' →
    (∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c)) →
    ∫ ω, (ω c : ℂ) * g ω ∂(P d) = (gvar d c : ℝ) * ∫ ω, g' ω ∂(P d)
  /-- All polynomial moments of `P d` are finite. -/
  polyInt : ∀ (I : Finset (Coord d)) (n : ℕ), Integrable (fun ω => polyW I ω ^ n) (P d)

/-- Every tame function is integrable. -/
theorem Tame.integrable (hG : GaussIBP d) {f : Ω d → ℂ} (hf : Tame d f) :
    Integrable f (P d) := by
  obtain ⟨I, n, C, hb⟩ := hf.poly
  have hC : 0 ≤ C := by
    have hp : (0 : ℝ) < polyW I (fun _ => 0) ^ n := pow_pos (polyW_pos _ _) _
    nlinarith [norm_nonneg (f fun _ => 0), hb fun _ => 0]
  refine Integrable.mono ((hG.polyInt I n).const_mul C) hf.cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hp : (0 : ℝ) ≤ C * polyW I ω ^ n := mul_nonneg hC (le_of_lt (pow_pos (polyW_pos _ _) _))
  have : ‖C * polyW I ω ^ n‖ = C * polyW I ω ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
  rw [this]
  exact hb ω

/-! ### The row chaos

The data below is exactly what the quadratic form of (4.7) presents at a fixed row `i`:
an index set `κ` (in the application `{k // k ≠ i}`), two Gaussian coordinates `co k true`,
`co k false` per index (the real and imaginary parts of `H_{ik}`), a sign `eps k = ±1` (which of
`X_{ik}`, `X_{ki}` carries the coordinates), a scale `r` (`= √t`, since `H_t = √t X`), and a
matrix `B` (`= G^{(i)}`) which is **bounded** and **does not read any of the coordinates
`co k b`**.  That last property is `B_free` below, and is the row independence T84 supplies. -/

/-- The data of a *row chaos*: the Gaussian row `h_k = r(ω_{co k tt} + ε_k i ω_{co k ff})` and a
bounded matrix `B` that does not read the coordinates of the row. -/
structure RowChaos (d : Dims) (κ : Type*) [Fintype κ] [DecidableEq κ] where
  /-- The two coordinates carrying the real and imaginary part of the row entry `h_k`. -/
  co : κ → Bool → Coord d
  /-- Distinct indices and tags use distinct coordinates. -/
  co_inj : Function.Injective fun p : κ × Bool => co p.1 p.2
  /-- Both tags of `k` carry the same variance. -/
  gvar_tag : ∀ k, (gvar d (co k false) : ℝ) = (gvar d (co k true) : ℝ)
  /-- The sign `±1` fixing the orientation of the imaginary part. -/
  eps : κ → ℝ
  /-- `eps k = ±1`. -/
  eps_sq : ∀ k, eps k ^ 2 = 1
  /-- The global scale of the row (`√t` for the flow `H_t = √t X`). -/
  r : ℝ
  /-- The matrix of the quadratic form. -/
  B : Ω d → κ → κ → ℂ
  /-- `B` is continuous entrywise. -/
  B_cont : ∀ k l, Continuous fun ω => B ω k l
  /-- A global bound for `B`. -/
  Bbd : ℝ
  /-- `B` is globally bounded (in the application, by `η⁻¹`, via `norm_green_le`). -/
  B_bdd : ∀ ω k l, ‖B ω k l‖ ≤ Bbd
  /-- The witness set of coordinates `B` reads. -/
  Ifree : Finset (Coord d)
  /-- **Row independence**: the witness set contains no coordinate of the row. -/
  Ifree_free : ∀ k b, co k b ∉ Ifree
  /-- `B` is determined by the coordinates in `Ifree`. -/
  B_free : ∀ ω ω', (∀ c ∈ Ifree, ω c = ω' c) → B ω = B ω'

namespace RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : RowChaos d κ)

/-- The variance of each of the two coordinates of the index `k`. -/
noncomputable def w (k : κ) : ℝ := (gvar d (C.co k true) : ℝ)

/-- `σ_k = E|h_k|² = 2 r² w_k`; in the application `σ_k = t S_{ik}`. -/
noncomputable def sg (k : κ) : ℝ := 2 * C.r ^ 2 * C.w k

theorem w_nonneg (k : κ) : 0 ≤ C.w k := (gvar d (C.co k true)).coe_nonneg

theorem sg_nonneg (k : κ) : 0 ≤ C.sg k := by
  have := C.w_nonneg k; unfold sg; positivity

/-- The row entry `h_k = r (ω_{co k tt} + ε_k i ω_{co k ff})`. -/
noncomputable def h (ω : Ω d) (k : κ) : ℂ :=
  (C.r : ℂ) * ((ω (C.co k true) : ℂ) + ((C.eps k : ℂ) * Complex.I) * (ω (C.co k false) : ℂ))

/-- `U_k = ∑_l B_{kl} conj(h_l)`. -/
noncomputable def U (ω : Ω d) (k : κ) : ℂ := ∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)

/-- `V_k = ∑_m h_m B_{mk}`. -/
noncomputable def V (ω : Ω d) (k : κ) : ℂ := ∑ m, C.h ω m * C.B ω m k

/-- The centring constant `∑_k σ_k B_{kk}` (random, but not reading the row). -/
noncomputable def cen (ω : Ω d) : ℂ := ∑ k, (C.sg k : ℂ) * C.B ω k k

/-- **The chaos** `Q = ∑_{k,l} h_k B_{kl} conj(h_l) − ∑_k σ_k B_{kk}`. -/
noncomputable def chaos (ω : Ω d) : ℂ :=
  (∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l)) - C.cen ω

/-- `∂ Q / ∂ ω_{co k tt}`. -/
noncomputable def dA (ω : Ω d) (k : κ) : ℂ := (C.r : ℂ) * (C.U ω k + C.V ω k)

/-- `∂ Q / ∂ ω_{co k ff}`. -/
noncomputable def dB (ω : Ω d) (k : κ) : ℂ :=
  ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)

/-- `T = ∑_k σ_k (‖U_k‖² + ‖V_k‖²)`, the random control of the recursion. -/
noncomputable def Tq (ω : Ω d) : ℝ := ∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)

/-- `R = ∑_k σ_k U_k V_k`, the off-diagonal term of the recursion; `‖R‖ ≤ T/2`. -/
noncomputable def Rq (ω : Ω d) : ℂ := ∑ k, (C.sg k : ℂ) * C.U ω k * C.V ω k

theorem Tq_nonneg (ω : Ω d) : 0 ≤ C.Tq ω :=
  Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)

theorem norm_Rq_le (ω : Ω d) : ‖C.Rq ω‖ ≤ C.Tq ω / 2 := by
  have hterm : ∀ k : κ, ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖
      ≤ C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by
    intro k
    have h2 : ‖C.U ω k‖ * ‖C.V ω k‖ ≤ (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖C.U ω k‖ - ‖C.V ω k‖)]
    have := mul_le_mul_of_nonneg_left h2 (C.sg_nonneg k)
    calc ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖
        = C.sg k * (‖C.U ω k‖ * ‖C.V ω k‖) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (C.sg_nonneg k), mul_assoc]
      _ ≤ C.sg k * ((‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2) := this
      _ = C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by ring
  calc ‖C.Rq ω‖ ≤ ∑ k, ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖ := norm_sum_le _ _
    _ ≤ ∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = C.Tq ω / 2 := by rw [← Finset.sum_div]; rfl

/-! #### Elementary consequences of the data -/

theorem co_ne_of_index_ne {k m : κ} (hm : m ≠ k) (b b' : Bool) : C.co m b' ≠ C.co k b :=
  fun hh => hm (congrArg Prod.fst (C.co_inj (a₁ := (m, b')) (a₂ := (k, b)) hh))

theorem co_false_ne_co_true (k m : κ) : C.co m false ≠ C.co k true := fun hh => by
  simpa using congrArg Prod.snd (C.co_inj (a₁ := (m, false)) (a₂ := (k, true)) hh)

theorem co_true_ne_co_false (k m : κ) : C.co m true ≠ C.co k false := fun hh => by
  simpa using congrArg Prod.snd (C.co_inj (a₁ := (m, true)) (a₂ := (k, false)) hh)

/-- **Row independence in the form used**: moving a coordinate of the row does not move `B`. -/
theorem B_update (ω : Ω d) (k : κ) (b : Bool) (t : ℝ) :
    C.B (Function.update ω (C.co k b) t) = C.B ω := by
  refine C.B_free _ _ fun c hc => ?_
  have hne : c ≠ C.co k b := by
    rintro rfl
    exact C.Ifree_free k b hc
  exact Function.update_of_ne hne _ _

theorem findep_B : FinDep d C.B := ⟨C.Ifree, fun ω ω' h => C.B_free ω ω' h⟩

theorem tameB (k l : κ) : Tame d (fun ω => C.B ω k l) :=
  Tame.ofBdd (C.B_cont k l)
    ⟨C.Ifree, fun ω ω' h => congrFun (congrFun (C.B_free ω ω' h) k) l⟩
    (fun ω => C.B_bdd ω k l)

theorem tameh (k : κ) : Tame d (fun ω => C.h ω k) :=
  (Tame.const (d := d) (C.r : ℂ)).mul
    ((Tame.coord (C.co k true)).add
      ((Tame.const (d := d) ((C.eps k : ℂ) * Complex.I)).mul (Tame.coord (C.co k false))))

theorem tameU (k : κ) : Tame d (fun ω => C.U ω k) :=
  Tame.sum _ fun l _ => (C.tameB k l).mul (C.tameh l).conj

theorem tameV (k : κ) : Tame d (fun ω => C.V ω k) :=
  Tame.sum _ fun m _ => (C.tameh m).mul (C.tameB m k)

theorem tamecen : Tame d C.cen :=
  Tame.sum _ fun k _ => (Tame.const (d := d) (C.sg k : ℂ)).mul (C.tameB k k)

theorem tamechaos : Tame d C.chaos :=
  (Tame.sum _ fun k _ => Tame.sum _ fun l _ =>
    ((C.tameh k).mul (C.tameB k l)).mul (C.tameh l).conj).sub C.tamecen

theorem tamedA (k : κ) : Tame d (fun ω => C.dA ω k) :=
  (Tame.const (d := d) (C.r : ℂ)).mul ((C.tameU k).add (C.tameV k))

theorem tamedB (k : κ) : Tame d (fun ω => C.dB ω k) :=
  (Tame.const (d := d) ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)).mul
    ((C.tameU k).sub (C.tameV k))

/-! #### The coordinate derivatives -/

/-- `∂ h_m / ∂ ω_{co k tt}`. -/
noncomputable def delA (k m : κ) : ℂ := if m = k then (C.r : ℂ) else 0

/-- `∂ h_m / ∂ ω_{co k ff}`. -/
noncomputable def delB (k m : κ) : ℂ :=
  if m = k then (C.r : ℂ) * (C.eps k : ℂ) * Complex.I else 0

theorem conj_delA (k m : κ) : (starRingEnd ℂ) (C.delA k m) = C.delA k m := by
  unfold delA; split_ifs <;> simp

theorem conj_delB (k m : κ) : (starRingEnd ℂ) (C.delB k m) = -C.delB k m := by
  unfold delB; split_ifs <;> simp

theorem hasDerivAt_conj' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) f') t :=
  (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

theorem hasDerivAt_ofReal_id (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

theorem hasDerivAt_h_true (k m : κ) (ω : Ω d) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => C.h (Function.update ω (C.co k true) s) m) (C.delA k m) s₀ := by
  by_cases hm : m = k
  · subst hm
    have e : ∀ s : ℝ, C.h (Function.update ω (C.co m true) s) m
        = (C.r : ℂ) * ((s : ℂ) + ((C.eps m : ℂ) * Complex.I) * (ω (C.co m false) : ℂ)) := by
      intro s
      show (C.r : ℂ) * _ = _
      rw [Function.update_self, Function.update_of_ne (C.co_false_ne_co_true m m)]
    simp only [e]
    have h1 := (hasDerivAt_ofReal_id s₀).add_const
      (((C.eps m : ℂ) * Complex.I) * (ω (C.co m false) : ℂ))
    simpa [delA] using HasDerivAt.const_mul (C.r : ℂ) h1
  · have e : ∀ s : ℝ, C.h (Function.update ω (C.co k true) s) m = C.h ω m := by
      intro s
      show (C.r : ℂ) * _ = (C.r : ℂ) * _
      rw [Function.update_of_ne (C.co_ne_of_index_ne hm _ _),
        Function.update_of_ne (C.co_ne_of_index_ne hm _ _)]
    simp only [e, delA, ite_eq_right hm]
    exact hasDerivAt_const _ _

theorem hasDerivAt_h_false (k m : κ) (ω : Ω d) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => C.h (Function.update ω (C.co k false) s) m) (C.delB k m) s₀ := by
  by_cases hm : m = k
  · subst hm
    have e : ∀ s : ℝ, C.h (Function.update ω (C.co m false) s) m
        = (C.r : ℂ) * ((ω (C.co m true) : ℂ) + ((C.eps m : ℂ) * Complex.I) * (s : ℂ)) := by
      intro s
      show (C.r : ℂ) * _ = _
      rw [Function.update_self, Function.update_of_ne (C.co_true_ne_co_false m m)]
    simp only [e]
    have h1 := HasDerivAt.const_mul ((C.eps m : ℂ) * Complex.I) (hasDerivAt_ofReal_id s₀)
    have h2 := h1.const_add ((ω (C.co m true) : ℂ))
    have := HasDerivAt.const_mul (C.r : ℂ) h2
    simpa [delB, mul_assoc] using this
  · have e : ∀ s : ℝ, C.h (Function.update ω (C.co k false) s) m = C.h ω m := by
      intro s
      show (C.r : ℂ) * _ = (C.r : ℂ) * _
      rw [Function.update_of_ne (C.co_ne_of_index_ne hm _ _),
        Function.update_of_ne (C.co_ne_of_index_ne hm _ _)]
    simp only [e, delB, ite_eq_right hm]
    exact hasDerivAt_const _ _

theorem cen_update (ω : Ω d) (k : κ) (b : Bool) (t : ℝ) :
    C.cen (Function.update ω (C.co k b) t) = C.cen ω := by
  unfold cen
  exact Finset.sum_congr rfl fun m _ => by rw [C.B_update ω k b t]

theorem sum_ite_mul_left {a : ℂ} (k : κ) (F : κ → ℂ) :
    ∑ m, (if m = k then a else 0) * F m = a * F k := by
  have e : ∀ m : κ, (if m = k then a else 0) * F m = if m = k then a * F m else 0 := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun m _ => e m,
    Finset.sum_ite_eq' Finset.univ k fun m => a * F m]
  simp

theorem sum_mul_ite_right {a : ℂ} (k : κ) (F : κ → ℂ) :
    ∑ l, F l * (if l = k then a else 0) = F k * a := by
  have e : ∀ l : κ, F l * (if l = k then a else 0) = if l = k then F l * a else 0 := by
    intro l; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun l _ => e l,
    Finset.sum_ite_eq' Finset.univ k fun l => F l * a]
  simp

omit [DecidableEq κ] in
theorem sum_mul_const (F : κ → ℂ) (a : ℂ) : ∑ m, F m * a = (∑ m, F m) * a :=
  (Finset.sum_mul _ _ _).symm

/-- The value of the derivative of the chaos along the real tag of the row index `k`. -/
theorem sum_delA_eq (k : κ) (ω : Ω d) :
    (∑ m, ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l))) = C.dA ω k := by
  have e1 : ∀ m : κ, ∑ l, C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      = C.delA k m * C.U ω m := by
    intro m
    show _ = C.delA k m * ∑ l, C.B ω m l * (starRingEnd ℂ) (C.h ω l)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have e2 : ∀ m : κ, ∑ l, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)
      = (C.h ω m * C.B ω m k) * (C.r : ℂ) := by
    intro m
    have e : ∀ l : κ, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)
        = (C.h ω m * C.B ω m l) * (if l = k then (C.r : ℂ) else 0) := fun l => by
      rw [C.conj_delA]; rfl
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.h ω m * C.B ω m l]
  have e3 : ∑ m, C.delA k m * C.U ω m = (C.r : ℂ) * C.U ω k := by
    have e : ∀ m : κ, C.delA k m * C.U ω m = (if m = k then (C.r : ℂ) else 0) * C.U ω m :=
      fun m => rfl
    rw [Finset.sum_congr rfl fun m _ => e m, sum_ite_mul_left k fun m => C.U ω m]
  have e4 : ∑ m, (C.h ω m * C.B ω m k) * (C.r : ℂ) = (C.r : ℂ) * C.V ω k := by
    rw [sum_mul_const]
    show (C.V ω k) * (C.r : ℂ) = _
    ring
  calc (∑ m, ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)))
      = ∑ m, (C.delA k m * C.U ω m + (C.h ω m * C.B ω m k) * (C.r : ℂ)) :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, e1 m, e2 m]
    _ = (C.r : ℂ) * C.U ω k + (C.r : ℂ) * C.V ω k := by rw [Finset.sum_add_distrib, e3, e4]
    _ = C.dA ω k := by unfold dA; ring

/-- The value of the derivative of the chaos along the imaginary tag of the row index `k`. -/
theorem sum_delB_eq (k : κ) (ω : Ω d) :
    (∑ m, ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l))) = C.dB ω k := by
  set a : ℂ := (C.r : ℂ) * (C.eps k : ℂ) * Complex.I with ha
  have e1 : ∀ m : κ, ∑ l, C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      = C.delB k m * C.U ω m := by
    intro m
    show _ = C.delB k m * ∑ l, C.B ω m l * (starRingEnd ℂ) (C.h ω l)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have e2 : ∀ m : κ, ∑ l, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)
      = (C.h ω m * C.B ω m k) * (-a) := by
    intro m
    have e : ∀ l : κ, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)
        = (C.h ω m * C.B ω m l) * (if l = k then -a else 0) := by
      intro l
      rw [C.conj_delB]
      unfold delB
      split_ifs <;> simp [ha]
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.h ω m * C.B ω m l]
  have e3 : ∑ m, C.delB k m * C.U ω m = a * C.U ω k := by
    have e : ∀ m : κ, C.delB k m * C.U ω m = (if m = k then a else 0) * C.U ω m :=
      fun m => rfl
    rw [Finset.sum_congr rfl fun m _ => e m, sum_ite_mul_left k fun m => C.U ω m]
  have e4 : ∑ m, (C.h ω m * C.B ω m k) * (-a) = -a * C.V ω k := by
    rw [sum_mul_const]
    show (C.V ω k) * (-a) = _
    ring
  calc (∑ m, ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)))
      = ∑ m, (C.delB k m * C.U ω m + (C.h ω m * C.B ω m k) * (-a)) :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, e1 m, e2 m]
    _ = a * C.U ω k + -a * C.V ω k := by rw [Finset.sum_add_distrib, e3, e4]
    _ = C.dB ω k := by unfold dB; rw [ha]; ring

/-- **`∂ Q / ∂ ω_{co k tt} = dA`.** -/
theorem hasDerivAt_chaos_true (k : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k true) s))
      (C.dA ω k) (ω (C.co k true)) := by
  have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
    Function.update_eq_self _ ω
  have hterm : ∀ m l : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k true) s) m *
          C.B (Function.update ω (C.co k true) s) m l *
          (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
      (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)) (ω (C.co k true)) := by
    intro m l
    have h1 := C.hasDerivAt_h_true k m ω (ω (C.co k true))
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_true k l ω (ω (C.co k true)))
    have h2 : HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l) 0
        (ω (C.co k true)) := by
      have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l)
          = fun _ => C.B ω m l := by
        funext s; rw [C.B_update ω k true s]
      rw [hfun]; exact hasDerivAt_const _ _
    have hmul := (h1.fun_mul h2).fun_mul h3
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ))
    (A := fun m s => ∑ l, C.h (Function.update ω (C.co k true) s) m *
        C.B (Function.update ω (C.co k true) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
    (A' := fun m => ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)))
    (fun m _ => HasDerivAt.fun_sum fun l _ => hterm m l)
  have hcen : HasDerivAt (fun s : ℝ => C.cen (Function.update ω (C.co k true) s)) 0
      (ω (C.co k true)) := by
    have hfun : (fun s : ℝ => C.cen (Function.update ω (C.co k true) s)) = fun _ => C.cen ω := by
      funext s; rw [C.cen_update ω k true s]
    rw [hfun]; exact hasDerivAt_const _ _
  have := hsum.sub hcen
  rw [sub_zero, C.sum_delA_eq k ω] at this
  exact this

/-- **`∂ Q / ∂ ω_{co k ff} = dB`.** -/
theorem hasDerivAt_chaos_false (k : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k false) s))
      (C.dB ω k) (ω (C.co k false)) := by
  have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
    Function.update_eq_self _ ω
  have hterm : ∀ m l : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k false) s) m *
          C.B (Function.update ω (C.co k false) s) m l *
          (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
      (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)) (ω (C.co k false)) := by
    intro m l
    have h1 := C.hasDerivAt_h_false k m ω (ω (C.co k false))
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_false k l ω (ω (C.co k false)))
    have h2 : HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l) 0
        (ω (C.co k false)) := by
      have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l)
          = fun _ => C.B ω m l := by
        funext s; rw [C.B_update ω k false s]
      rw [hfun]; exact hasDerivAt_const _ _
    have hmul := (h1.fun_mul h2).fun_mul h3
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ))
    (A := fun m s => ∑ l, C.h (Function.update ω (C.co k false) s) m *
        C.B (Function.update ω (C.co k false) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
    (A' := fun m => ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)))
    (fun m _ => HasDerivAt.fun_sum fun l _ => hterm m l)
  have hcen : HasDerivAt (fun s : ℝ => C.cen (Function.update ω (C.co k false) s)) 0
      (ω (C.co k false)) := by
    have hfun : (fun s : ℝ => C.cen (Function.update ω (C.co k false) s)) = fun _ => C.cen ω := by
      funext s; rw [C.cen_update ω k false s]
    rw [hfun]; exact hasDerivAt_const _ _
  have := hsum.sub hcen
  rw [sub_zero, C.sum_delB_eq k ω] at this
  exact this

/-! #### The derivatives of `U`, `V`, `dA`, `dB` -/

theorem hasDerivAt_B_const (k : κ) (b : Bool) (m l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k b) s) m l) 0 (ω (C.co k b)) := by
  have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k b) s) m l) = fun _ => C.B ω m l := by
    funext s; rw [C.B_update ω k b s]
  rw [hfun]; exact hasDerivAt_const _ _

theorem hasDerivAt_U_true (k m : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.U (Function.update ω (C.co k true) s) m)
      (C.B ω m k * (C.r : ℂ)) (ω (C.co k true)) := by
  have hself := Function.update_eq_self (C.co k true) ω
  have hterm : ∀ l : κ, HasDerivAt
      (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
      (C.B ω m l * (starRingEnd ℂ) (C.delA k l)) (ω (C.co k true)) := by
    intro l
    have h2 := C.hasDerivAt_B_const k true m l ω
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_true k l ω (ω (C.co k true)))
    have hmul := h2.fun_mul h3
    simp only [hself, zero_mul, zero_add] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun l _ => hterm l
  have hval : ∑ l, C.B ω m l * (starRingEnd ℂ) (C.delA k l) = C.B ω m k * (C.r : ℂ) := by
    have e : ∀ l : κ, C.B ω m l * (starRingEnd ℂ) (C.delA k l)
        = C.B ω m l * (if l = k then (C.r : ℂ) else 0) := fun l => by rw [C.conj_delA]; rfl
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.B ω m l]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_V_true (k m : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.V (Function.update ω (C.co k true) s) m)
      ((C.r : ℂ) * C.B ω k m) (ω (C.co k true)) := by
  have hself := Function.update_eq_self (C.co k true) ω
  have hterm : ∀ j : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k true) s) j *
        C.B (Function.update ω (C.co k true) s) j m)
      (C.delA k j * C.B ω j m) (ω (C.co k true)) := by
    intro j
    have h1 := C.hasDerivAt_h_true k j ω (ω (C.co k true))
    have h2 := C.hasDerivAt_B_const k true j m ω
    have hmul := h1.fun_mul h2
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun j _ => hterm j
  have hval : ∑ j, C.delA k j * C.B ω j m = (C.r : ℂ) * C.B ω k m := by
    have e : ∀ j : κ, C.delA k j * C.B ω j m = (if j = k then (C.r : ℂ) else 0) * C.B ω j m :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => e j, sum_ite_mul_left k fun j => C.B ω j m]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_U_false (k m : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.U (Function.update ω (C.co k false) s) m)
      (C.B ω m k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I))) (ω (C.co k false)) := by
  have hself := Function.update_eq_self (C.co k false) ω
  have hterm : ∀ l : κ, HasDerivAt
      (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
      (C.B ω m l * (starRingEnd ℂ) (C.delB k l)) (ω (C.co k false)) := by
    intro l
    have h2 := C.hasDerivAt_B_const k false m l ω
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_false k l ω (ω (C.co k false)))
    have hmul := h2.fun_mul h3
    simp only [hself, zero_mul, zero_add] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun l _ => hterm l
  have hval : ∑ l, C.B ω m l * (starRingEnd ℂ) (C.delB k l)
      = C.B ω m k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) := by
    have e : ∀ l : κ, C.B ω m l * (starRingEnd ℂ) (C.delB k l)
        = C.B ω m l * (if l = k then -((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) else 0) := by
      intro l
      rw [C.conj_delB]
      unfold delB
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.B ω m l]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_V_false (k m : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.V (Function.update ω (C.co k false) s) m)
      (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k m) (ω (C.co k false)) := by
  have hself := Function.update_eq_self (C.co k false) ω
  have hterm : ∀ j : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k false) s) j *
        C.B (Function.update ω (C.co k false) s) j m)
      (C.delB k j * C.B ω j m) (ω (C.co k false)) := by
    intro j
    have h1 := C.hasDerivAt_h_false k j ω (ω (C.co k false))
    have h2 := C.hasDerivAt_B_const k false j m ω
    have hmul := h1.fun_mul h2
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun j _ => hterm j
  have hval : ∑ j, C.delB k j * C.B ω j m
      = ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k m := by
    have e : ∀ j : κ, C.delB k j * C.B ω j m
        = (if j = k then (C.r : ℂ) * (C.eps k : ℂ) * Complex.I else 0) * C.B ω j m :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => e j, sum_ite_mul_left k fun j => C.B ω j m]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_dA_true (k : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.dA (Function.update ω (C.co k true) s) k)
      (2 * (C.r : ℂ) ^ 2 * C.B ω k k) (ω (C.co k true)) := by
  have hU := C.hasDerivAt_U_true k k ω
  have hV := C.hasDerivAt_V_true k k ω
  have := HasDerivAt.const_mul (C.r : ℂ) (hU.add hV)
  have he : (C.r : ℂ) * (C.B ω k k * (C.r : ℂ) + (C.r : ℂ) * C.B ω k k)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω k k := by ring
  rw [he] at this
  exact this

theorem hasDerivAt_dB_false (k : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.dB (Function.update ω (C.co k false) s) k)
      (2 * (C.r : ℂ) ^ 2 * C.B ω k k) (ω (C.co k false)) := by
  have hU := C.hasDerivAt_U_false k k ω
  have hV := C.hasDerivAt_V_false k k ω
  have hd := HasDerivAt.const_mul ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) (hU.sub hV)
  have hes : ((C.eps k : ℂ)) ^ 2 = 1 := by
    have := C.eps_sq k
    have : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [this]
    push_cast at this
    exact this
  have he : ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) *
      (C.B ω k k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I))
        - ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k k)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω k k := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-2 * (C.r : ℂ) ^ 2 * C.B ω k k * (C.eps k : ℂ) ^ 2) * hI
      + (2 * (C.r : ℂ) ^ 2 * C.B ω k k) * hes
  rw [he] at hd
  exact hd

/-! #### The Euler identity -/

theorem conj_h (ω : Ω d) (k : κ) : (starRingEnd ℂ) (C.h ω k)
    = (C.r : ℂ) * ((ω (C.co k true) : ℂ)
      - ((C.eps k : ℂ) * Complex.I) * (ω (C.co k false) : ℂ)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * _) = _
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem coord_mul_dA_add_dB (ω : Ω d) (k : κ) :
    (ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k
      = C.h ω k * C.U ω k + (starRingEnd ℂ) (C.h ω k) * C.V ω k := by
  rw [C.conj_h ω k]
  show _ = ((C.r : ℂ) * _) * _ + _
  unfold dA dB
  ring

/-- **Euler's identity for the chaos**: `∑_α ω_α ∂_α Q = 2 (Q + ∑_k σ_k B_{kk})`. -/
theorem sum_coord_mul_deriv (ω : Ω d) :
    ∑ k, ((ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k)
      = 2 * (C.chaos ω + C.cen ω) := by
  have hD : C.chaos ω + C.cen ω
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    unfold chaos; ring
  have e1 : ∑ k, C.h ω k * C.U ω k
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) :=
    Finset.sum_congr rfl fun k _ => by
      show C.h ω k * (∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
  have e2 : ∑ k, (starRingEnd ℂ) (C.h ω k) * C.V ω k
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    have step : ∀ k : κ, (starRingEnd ℂ) (C.h ω k) * C.V ω k
        = ∑ m, C.h ω m * C.B ω m k * (starRingEnd ℂ) (C.h ω k) := by
      intro k
      show (starRingEnd ℂ) (C.h ω k) * (∑ m, C.h ω m * C.B ω m k) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun k _ => step k]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun k _ => C.coord_mul_dA_add_dB ω k, Finset.sum_add_distrib, e1, e2,
    hD]
  ring

/-! #### The master integration-by-parts identity -/

section IBP

variable (hG : GaussIBP d)
include hG

/-- **The master identity.**  For any tame `F` whose derivatives along the two coordinates of
each row index are `FA k`, `FB k`,

`2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q · ∂_{a_k}F + ∂_{b_k}Q · ∂_{b_k}F)`.

This is Gaussian integration by parts applied once to each of the `2|κ|` coordinates of the row,
using Euler's identity `∑_α ω_α ∂_α Q = 2(Q + ∑_k σ_k B_{kk})` to produce `Q` on the left and
`∂_α ∂_α Q = 2 r² B_{kk}` to cancel the centring constant. -/
theorem integral_chaos_mul {F : Ω d → ℂ} {FA FB : κ → Ω d → ℂ}
    (hF : Tame d F) (hFA : ∀ k, Tame d (FA k)) (hFB : ∀ k, Tame d (FB k))
    (hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)))
    (hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false))) :
    2 * ∫ ω, C.chaos ω * F ω ∂(P d)
      = ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d) := by
  classical
  have htB : ∀ k : κ, Tame d fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω := fun k =>
    ((Tame.const (d := d) (2 * (C.r : ℂ) ^ 2)).mul (C.tameB k k)).mul hF
  have htsg : ∀ k : κ, Tame d fun ω => (C.sg k : ℂ) * C.B ω k k * F ω := fun k =>
    ((Tame.const (d := d) ((C.sg k : ℂ))).mul (C.tameB k k)).mul hF
  have hcast : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2) = ((C.sg k : ℝ) : ℂ) := by
    intro k
    have : C.sg k = 2 * C.r ^ 2 * C.w k := rfl
    rw [this]; push_cast; ring
  -- the two Stein identities at the row index `k`
  have hIA : ∀ k : κ, ∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(P d)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(P d) := by
    intro k
    have hst := hG.stein (C.co k true) (fun ω => C.dA ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dA ω k * FA k ω)
      ((C.tamedA k).mul hF) ((htB k).add ((C.tamedA k).mul (hFA k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedA k).mul (hFA k)).integrable hG), mul_add]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dA_true k ω).fun_mul (hdFA k ω)
      simp only [hself] at hmul
      exact hmul
  have hIB : ∀ k : κ, ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(P d)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(P d) := by
    intro k
    have hst := hG.stein (C.co k false) (fun ω => C.dB ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dB ω k * FB k ω)
      ((C.tamedB k).mul hF) ((htB k).add ((C.tamedB k).mul (hFB k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG), mul_add]
      have hgv : ((gvar d (C.co k false) : ℝ) : ℂ) = ((C.w k : ℝ) : ℂ) := by
        rw [C.gvar_tag k]; rfl
      rw [hgv]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dB_false k ω).fun_mul (hdFB k ω)
      simp only [hself] at hmul
      exact hmul
  -- the left-hand side, by Euler's identity
  have hEuler : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(P d)
      = ∑ k, (∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(P d)
        + ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(P d)) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
          + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) := by
      intro ω
      rw [← C.sum_coord_mul_deriv ω, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hti : ∀ k : κ, Tame d fun ω => (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) :=
      fun k => (Tame.coord (C.co k true)).mul ((C.tamedA k).mul hF)
    have hti' : ∀ k : κ, Tame d fun ω => (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) :=
      fun k => (Tame.coord (C.co k false)).mul ((C.tamedB k).mul hF)
    calc ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(P d)
        = ∫ ω, ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(P d) := by
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = ∑ k, ∫ ω, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(P d) :=
          MeasureTheory.integral_finsetSum _ fun k _ => ((hti k).add (hti' k)).integrable hG
      _ = _ := Finset.sum_congr rfl fun k _ =>
          MeasureTheory.integral_add ((hti k).integrable hG) ((hti' k).integrable hG)
  -- the left-hand side, expanded
  have hsplit : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(P d)
      = 2 * ∫ ω, C.chaos ω * F ω ∂(P d) + 2 * ∫ ω, C.cen ω * F ω ∂(P d) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = 2 * (C.chaos ω * F ω) + 2 * (C.cen ω * F ω) := fun ω => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw),
      MeasureTheory.integral_add
        (((Tame.const (d := d) 2).mul (C.tamechaos.mul hF)).integrable hG)
        (((Tame.const (d := d) 2).mul (C.tamecen.mul hF)).integrable hG),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the centring constant
  have hcen : ∑ k, ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
      = ∫ ω, C.cen ω * F ω ∂(P d) := by
    rw [← MeasureTheory.integral_finsetSum _ fun k _ => (htsg k).integrable hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show _ = (∑ k, (C.sg k : ℂ) * C.B ω k k) * F ω
    rw [Finset.sum_mul]
  -- put everything together
  have hkey := hEuler
  rw [hsplit] at hkey
  rw [Finset.sum_congr rfl fun k _ => by rw [hIA k, hIB k]] at hkey
  have hrearr : ∑ k, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(P d))
      + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(P d)))
      = 2 * ∫ ω, C.cen ω * F ω ∂(P d)
        + ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d) := by
    have hstep : ∀ k : κ, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
          + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(P d))
        + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
          + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(P d)))
        = 2 * ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(P d)
          + (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d) := by
      intro k
      rw [MeasureTheory.integral_add (((C.tamedA k).mul (hFA k)).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG)]
      ring
    rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_add_distrib, ← Finset.mul_sum, hcen]
  rw [hrearr] at hkey
  have := hkey
  linear_combination this

end IBP

/-! #### The two quadratic sums -/

theorem eps_sq_complex (k : κ) : ((C.eps k : ℂ)) ^ 2 = 1 := by
  have h := C.eps_sq k
  have h2 : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h]
  push_cast at h2
  exact h2

theorem sg_complex (k : κ) : ((C.sg k : ℝ) : ℂ) = 2 * (C.r : ℂ) ^ 2 * ((C.w k : ℝ) : ℂ) := by
  show ((2 * C.r ^ 2 * C.w k : ℝ) : ℂ) = _
  push_cast; ring

theorem conj_dA (ω : Ω d) (k : κ) : (starRingEnd ℂ) (C.dA ω k)
    = (C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * (C.U ω k + C.V ω k)) = _
  simp [Complex.conj_ofReal]

theorem conj_dB (ω : Ω d) (k : κ) : (starRingEnd ℂ) (C.dB ω k)
    = (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
      ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) = _
  simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `∑_k w_k ((∂_{a_k}Q)² + (∂_{b_k}Q)²) = 2 R`. -/
theorem sum_w_sq (ω : Ω d) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2) = 2 * C.Rq ω := by
  have hR : (2 : ℂ) * C.Rq ω = ∑ k, 2 * (((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) := by
    show (2 : ℂ) * (∑ k, ((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) = _
    rw [Finset.mul_sum]
  rw [hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hes := C.eps_sq_complex k
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [C.sg_complex k]
  show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) ^ 2
      + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) ^ 2) = _
  linear_combination (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2
      * (C.eps k : ℂ) ^ 2) * hI
    - (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2) * hes

/-- `∑_k w_k (|∂_{a_k}Q|² + |∂_{b_k}Q|²) = T`. -/
theorem sum_w_normSq (ω : Ω d) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) = ((C.Tq ω : ℝ) : ℂ) := by
  have hstep : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))
      = ((C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) := by
    intro k
    have hU : ((‖C.U ω k‖ ^ 2 : ℝ) : ℂ) = C.U ω k * (starRingEnd ℂ) (C.U ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have hV : ((‖C.V ω k‖ ^ 2 : ℝ) : ℂ) = C.V ω k * (starRingEnd ℂ) (C.V ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    rw [Complex.ofReal_mul, Complex.ofReal_add, hU, hV, C.sg_complex k, C.conj_dA, C.conj_dB]
    have hes := C.eps_sq_complex k
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) *
          ((C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)))
        + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) *
          ((-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
            ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) = _
    linear_combination (-(((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.eps k : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k))))) * hI
      + (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) * hes
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Complex.ofReal_sum]
  rfl

theorem tameRq : Tame d C.Rq :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul (C.tameU k) |>.mul (C.tameV k)

theorem tameTq : Tame d fun ω => ((C.Tq ω : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω : ℝ) : ℂ))
      = fun ω => ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
        + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) := by
    funext ω; rw [C.sum_w_normSq ω]
  rw [hfun]
  exact Tame.sum _ fun k _ => (Tame.const (d := d) ((C.w k : ℝ) : ℂ)).mul
    (((C.tamedA k).mul (C.tamedA k).conj).add ((C.tamedB k).mul (C.tamedB k).conj))

/-! #### The moment recursion -/

section Recursion

variable (hG : GaussIBP d)
include hG

/-- **The moment recursion.**  Integration by parts once in each row coordinate, applied to
`F = Q^q \bar Q^{q+1}`, gives

`2 E[|Q|^{2(q+1)}] = 2q E[R Q^{q-1} \bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`,

with `R = ∑_k σ_k U_k V_k` and `T = ∑_k σ_k (|U_k|² + |V_k|²)`.  Since `‖R‖ ≤ T/2` this is the
Hanson–Wright recursion `E|Q|^{2p} ≤ (2p-1)/2 · E[T |Q|^{2p-2}]`. -/
theorem moment_recursion (q : ℕ) :
    2 * ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(P d)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(P d)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(P d) := by
  classical
  set F : Ω d → ℂ := fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) with hFdef
  set FA : κ → Ω d → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dA ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dA ω k)) with hFAdef
  set FB : κ → Ω d → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dB ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dB ω k)) with hFBdef
  have hFt : Tame d F := (C.tamechaos.pow q).mul (C.tamechaos.conj.pow (q + 1))
  have hFAt : ∀ k, Tame d (FA k) := fun k =>
    ((((Tame.const (d := d) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedA k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((Tame.const (d := d) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedA k).conj))
  have hFBt : ∀ k, Tame d (FB k) := fun k =>
    ((((Tame.const (d := d) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedB k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((Tame.const (d := d) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedB k).conj))
  have hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)) := by
    intro k ω
    have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_true k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false)) := by
    intro k ω
    have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_false k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hmain := C.integral_chaos_mul hG hFt hFAt hFBt hdFA hdFB
  -- the left-hand side
  have hL : ∫ ω, C.chaos ω * F ω ∂(P d)
      = ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(P d) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show C.chaos ω * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) = _
    ring
  -- the right-hand side, pointwise
  have hptw : ∀ ω : Ω d, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
      = 2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
        + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q)) := by
    intro ω
    have hsplit : ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
        = ((q : ℂ) * (C.chaos ω ^ (q - 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2))
          + (((q + 1 : ℕ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
                + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hFAdef, hFBdef]
      ring
    rw [hsplit, C.sum_w_sq ω, C.sum_w_normSq ω]
    push_cast
    ring
  -- assemble
  have htR : Tame d fun ω => C.Rq ω * (C.chaos ω ^ (q - 1)
      * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) :=
    C.tameRq.mul ((C.tamechaos.pow (q - 1)).mul (C.tamechaos.conj.pow (q + 1)))
  have htT : Tame d fun ω => ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
      * (starRingEnd ℂ) (C.chaos ω) ^ q) :=
    C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))
  have htk : ∀ k : κ, Tame d fun ω =>
      ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) := fun k =>
    (Tame.const (d := d) ((C.w k : ℝ) : ℂ)).mul
      (((C.tamedA k).mul (hFAt k)).add ((C.tamedB k).mul (hFBt k)))
  have hR : ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(P d)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(P d) := by
    calc ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d)
        = ∑ k, ∫ ω, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d) :=
          Finset.sum_congr rfl fun k _ => (MeasureTheory.integral_const_mul _ _).symm
      _ = ∫ ω, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(P d) :=
          (MeasureTheory.integral_finsetSum _ fun k _ => (htk k).integrable hG).symm
      _ = ∫ ω, (2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
              * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
              * (starRingEnd ℂ) (C.chaos ω) ^ q))) ∂(P d) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = _ := by
          rw [MeasureTheory.integral_add
            (((Tame.const (d := d) (2 * (q : ℂ))).mul htR).integrable hG)
            (((Tame.const (d := d) ((q : ℕ) + 1 : ℂ)).mul htT).integrable hG),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hL] at hmain
  rw [hmain, hR]

end Recursion

/-! #### The real form of the recursion -/

/-- `E|Q|^{2q}`. -/
noncomputable def mom (q : ℕ) : ℝ := ∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(P d)

/-- `E[T |Q|^{2q}]`, the right-hand side of the recursion. -/
noncomputable def momT (q : ℕ) : ℝ := ∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(P d)

theorem ofReal_norm_pow (ω : Ω d) (q : ℕ) :
    ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) = C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q := by
  have h2 : ((‖C.chaos ω‖ ^ 2 : ℝ) : ℂ) = C.chaos ω * (starRingEnd ℂ) (C.chaos ω) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [pow_mul, Complex.ofReal_pow, h2, mul_pow]

theorem tame_ofReal_norm_pow (q : ℕ) :
    Tame d fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q :=
    funext fun ω => C.ofReal_norm_pow ω q
  rw [hfun]
  exact (C.tamechaos.pow q).mul (C.tamechaos.conj.pow q)

theorem tame_ofReal_Tq_mul (q : ℕ) :
    Tame d fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => ((C.Tq ω : ℝ) : ℂ) *
        (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) := by
    funext ω
    rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]
  rw [hfun]
  exact C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))

omit [DecidableEq κ] in
theorem ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.sq_norm]

theorem mom_nonneg (q : ℕ) : 0 ≤ C.mom q :=
  MeasureTheory.integral_nonneg fun ω => by positivity

theorem momT_nonneg (q : ℕ) : 0 ≤ C.momT q :=
  MeasureTheory.integral_nonneg fun ω => mul_nonneg (C.Tq_nonneg ω) (by positivity)

omit [DecidableEq κ] in
theorem integral_ofReal' (f : Ω d → ℝ) :
    ∫ ω, ((f ω : ℝ) : ℂ) ∂(P d) = ((∫ ω, f ω ∂(P d) : ℝ) : ℂ) := by
  have h := _root_.integral_ofReal (𝕜 := ℂ) (f := f) (μ := P d)
  simpa using h

theorem integral_chaos_pow (q : ℕ) :
    ∫ ω, C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q ∂(P d) = ((C.mom q : ℝ) : ℂ) := by
  show _ = ((∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(P d) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => ‖C.chaos ω‖ ^ (2 * q))]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun ω => (C.ofReal_norm_pow ω q).symm)

theorem integral_Tq_chaos_pow (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(P d)
      = ((C.momT q : ℝ) : ℂ) := by
  show _ = ((∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(P d) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q)
    = ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]

section Real

variable (hG : GaussIBP d)
include hG

theorem integrable_of_tame_ofReal {f : Ω d → ℝ} (hf : Tame d fun ω => ((f ω : ℝ) : ℂ)) :
    Integrable f (P d) := by
  simpa using (hf.integrable hG).re

theorem integrable_norm_pow (q : ℕ) :
    Integrable (fun ω => ‖C.chaos ω‖ ^ (2 * q)) (P d) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_norm_pow q)

theorem integrable_Tq_mul (q : ℕ) :
    Integrable (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)) (P d) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_Tq_mul q)

/-- The cross term of the recursion is dominated by half the control. -/
theorem norm_integral_Rq_le (p : ℕ) :
    ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(P d)‖
      ≤ C.momT (p + 1) / 2 := by
  have htR : Tame d fun ω => C.Rq ω * (C.chaos ω ^ p
      * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) :=
    C.tameRq.mul ((C.tamechaos.pow p).mul (C.tamechaos.conj.pow (p + 2)))
  have hbnd : ∀ ω : Ω d,
      ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖
        ≤ 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) := by
    intro ω
    have hnorm : ‖C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)‖
        = ‖C.chaos ω‖ ^ (2 * (p + 1)) := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
      congr 1
      omega
    rw [norm_mul, hnorm]
    have h1 := C.norm_Rq_le ω
    have h2 : (0 : ℝ) ≤ ‖C.chaos ω‖ ^ (2 * (p + 1)) := by positivity
    nlinarith
  calc ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(P d)‖
      ≤ ∫ ω, ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖ ∂(P d) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) ∂(P d) :=
        MeasureTheory.integral_mono ((htR.integrable hG).norm)
          ((C.integrable_Tq_mul hG (p + 1)).const_mul _) hbnd
    _ = C.momT (p + 1) / 2 := by
        rw [MeasureTheory.integral_const_mul]
        show 1 / 2 * C.momT (p + 1) = _
        ring

/-- **The Hanson–Wright recursion, real form**:
`2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`. -/
theorem two_mul_mom_succ_le (q : ℕ) :
    2 * C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) * C.momT q := by
  have hrec := C.moment_recursion hG q
  rw [C.integral_chaos_pow (q + 1), C.integral_Tq_chaos_pow q] at hrec
  set X : ℂ := ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
    * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(P d) with hX
  have hXb : 2 * (q : ℝ) * ‖X‖ ≤ (q : ℝ) * C.momT q := by
    rcases q with _ | p
    · simp
    · have hq : ‖X‖ ≤ C.momT (p + 1) / 2 := by
        rw [hX]
        have hidx : (p + 1 : ℕ) - 1 = p := by omega
        have hidx2 : (p + 1 : ℕ) + 1 = p + 2 := by omega
        rw [hidx, hidx2]
        exact C.norm_integral_Rq_le hG p
      have hm : 0 ≤ C.momT (p + 1) := C.momT_nonneg (p + 1)
      push_cast
      nlinarith [norm_nonneg X]
  have hnorm : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖
      ≤ 2 * (q : ℝ) * ‖X‖ + ((q : ℝ) + 1) * C.momT q := by
    rw [hrec]
    have h1 : ‖2 * (q : ℂ) * X + ((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖
        ≤ ‖2 * (q : ℂ) * X‖ + ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ := norm_add_le _ _
    have h2 : ‖2 * (q : ℂ) * X‖ = 2 * (q : ℝ) * ‖X‖ := by
      rw [norm_mul, norm_mul]
      simp
    have h3 : ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ = ((q : ℝ) + 1) * C.momT q := by
      have hc : ((q : ℕ) + 1 : ℂ) = (((q : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (C.momT_nonneg q),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)]
    linarith
  have hlhs : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖ = 2 * C.mom (q + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (C.mom_nonneg (q + 1))]
    simp
  rw [hlhs] at hnorm
  linarith

/-- At `q = 0` the recursion is an identity: `2 E|Q|² = E[T]`. -/
theorem two_mul_mom_one : 2 * C.mom 1 = C.momT 0 := by
  have hrec := C.moment_recursion hG 0
  rw [C.integral_chaos_pow (0 + 1), C.integral_Tq_chaos_pow 0] at hrec
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at hrec
  have : ((2 * C.mom 1 : ℝ) : ℂ) = ((C.momT 0 : ℝ) : ℂ) := by
    push_cast
    simpa using hrec
  exact_mod_cast this

/-! #### The variance: the case `p = 1`

At `q = 0` the recursion is an identity, and the control `T` integrates to twice the paper's
right-hand side.  The result is the exact variance

`E|Q|² = E ∑_{k,l} σ_k ‖B_{kl}‖² σ_l`,

which is (4.7) with the constant `1`. -/

/-- The paper's right-hand side `∑_{k,l} σ_k ‖B_{kl}‖² σ_l` (a random quantity, since `B` is). -/
noncomputable def Vq (ω : Ω d) : ℝ := ∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l

/-- **The row isometry**: conditionally on the coordinates outside the row, the entries
`h_l` are independent centred complex Gaussians with `E|h_l|² = σ_l`. -/
theorem integral_conj_h_mul_h {Z : Ω d → ℂ} (hZ : Tame d Z)
    (hZfree : ∀ (ω : Ω d) (k : κ) (b : Bool) (t : ℝ), Z (Function.update ω (C.co k b) t) = Z ω)
    (l l' : κ) :
    ∫ ω, (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z ω) ∂(P d)
      = (if l' = l then ((C.sg l : ℝ) : ℂ) else 0) * ∫ ω, Z ω ∂(P d) := by
  have hZd : ∀ (ω : Ω d) (k : κ) (b : Bool),
      HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co k b) s)) 0 (ω (C.co k b)) := by
    intro ω k b
    have hfun : (fun s : ℝ => Z (Function.update ω (C.co k b) s)) = fun _ => Z ω :=
      funext fun s => hZfree ω k b s
    rw [hfun]; exact hasDerivAt_const _ _
  have htg : Tame d fun ω => C.h ω l' * Z ω := (C.tameh l').mul hZ
  -- the real tag
  have hA : ∫ ω, (ω (C.co l true) : ℂ) * (C.h ω l' * Z ω) ∂(P d)
      = ((C.w l : ℝ) : ℂ) * (C.delA l l' * ∫ ω, Z ω ∂(P d)) := by
    have hst := hG.stein (C.co l true) (fun ω => C.h ω l' * Z ω)
      (fun ω => C.delA l l' * Z ω) htg ((Tame.const (d := d) (C.delA l l')).mul hZ) ?_
    · rw [hst, MeasureTheory.integral_const_mul]
      rfl
    · intro ω
      have hself : Function.update ω (C.co l true) (ω (C.co l true)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_h_true l l' ω (ω (C.co l true))).fun_mul (hZd ω l true)
      simp only [hself, mul_zero, add_zero] at hmul
      exact hmul
  have hB : ∫ ω, (ω (C.co l false) : ℂ) * (C.h ω l' * Z ω) ∂(P d)
      = ((C.w l : ℝ) : ℂ) * (C.delB l l' * ∫ ω, Z ω ∂(P d)) := by
    have hst := hG.stein (C.co l false) (fun ω => C.h ω l' * Z ω)
      (fun ω => C.delB l l' * Z ω) htg ((Tame.const (d := d) (C.delB l l')).mul hZ) ?_
    · have hgv : ((gvar d (C.co l false) : ℝ) : ℂ) = ((C.w l : ℝ) : ℂ) := by
        rw [C.gvar_tag l]; rfl
      rw [hst, hgv, MeasureTheory.integral_const_mul]
    · intro ω
      have hself : Function.update ω (C.co l false) (ω (C.co l false)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_h_false l l' ω (ω (C.co l false))).fun_mul (hZd ω l false)
      simp only [hself, mul_zero, add_zero] at hmul
      exact hmul
  have hptw : ∀ ω : Ω d, (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z ω)
      = (C.r : ℂ) * ((ω (C.co l true) : ℂ) * (C.h ω l' * Z ω))
        - ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) *
          ((ω (C.co l false) : ℂ) * (C.h ω l' * Z ω)) := by
    intro ω
    rw [C.conj_h ω l]
    ring
  have hcA : Tame d fun ω => (C.r : ℂ) * ((ω (C.co l true) : ℂ) * (C.h ω l' * Z ω)) :=
    (Tame.const (d := d) (C.r : ℂ)).mul ((Tame.coord (C.co l true)).mul htg)
  have hcB : Tame d fun ω => ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) *
      ((ω (C.co l false) : ℂ) * (C.h ω l' * Z ω)) :=
    (Tame.const (d := d) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
      ((Tame.coord (C.co l false)).mul htg)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw),
    MeasureTheory.integral_sub (hcA.integrable hG) (hcB.integrable hG),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hA, hB]
  by_cases hll : l' = l
  · subst hll
    have hdA : C.delA l' l' = (C.r : ℂ) := by unfold delA; simp
    have hdB : C.delB l' l' = (C.r : ℂ) * (C.eps l' : ℂ) * Complex.I := by unfold delB; simp
    have hes := C.eps_sq_complex l'
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [hdA, hdB, ite_eq_left (rfl : l' = l'), C.sg_complex l']
    linear_combination (-(((C.w l' : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.eps l' : ℂ) ^ 2
        * ∫ ω, Z ω ∂(P d))) * hI
      + (((C.w l' : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * ∫ ω, Z ω ∂(P d)) * hes
  · have hdA : C.delA l l' = 0 := by unfold delA; exact ite_eq_right hll
    have hdB : C.delB l l' = 0 := by unfold delB; exact ite_eq_right hll
    rw [hdA, hdB, ite_eq_right hll]
    ring

/-- A double row isometry: `E ∑_{l,l'} \bar h_l h_{l'} Z_{l l'} = ∑_l σ_l E Z_{l l}`. -/
theorem integral_conj_h_sum (Z : κ → κ → Ω d → ℂ) (hZt : ∀ l l', Tame d (Z l l'))
    (hZf : ∀ (l l' : κ) (ω : Ω d) (k : κ) (b : Bool) (t : ℝ),
      Z l l' (Function.update ω (C.co k b) t) = Z l l' ω) :
    ∫ ω, ∑ l, ∑ l', (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z l l' ω) ∂(P d)
      = ∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, Z l l ω ∂(P d) := by
  have ht : ∀ l l' : κ, Tame d fun ω => (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z l l' ω) :=
    fun l l' => (C.tameh l).conj.mul ((C.tameh l').mul (hZt l l'))
  calc ∫ ω, ∑ l, ∑ l', (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z l l' ω) ∂(P d)
      = ∑ l, ∫ ω, ∑ l', (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z l l' ω) ∂(P d) :=
        MeasureTheory.integral_finsetSum _ fun l _ =>
          (Tame.sum _ fun l' _ => ht l l').integrable hG
    _ = ∑ l, ∑ l', ∫ ω, (starRingEnd ℂ) (C.h ω l) * (C.h ω l' * Z l l' ω) ∂(P d) :=
        Finset.sum_congr rfl fun l _ =>
          MeasureTheory.integral_finsetSum _ fun l' _ => (ht l l').integrable hG
    _ = ∑ l, ∑ l', (if l' = l then ((C.sg l : ℝ) : ℂ) else 0) * ∫ ω, Z l l' ω ∂(P d) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ =>
          C.integral_conj_h_mul_h hG (hZt l l') (fun ω k b t => hZf l l' ω k b t) l l'
    _ = ∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, Z l l ω ∂(P d) :=
        Finset.sum_congr rfl fun l _ =>
          sum_ite_mul_left l fun l' => ∫ ω, Z l l' ω ∂(P d)

theorem integral_U_conj_U (k : κ) :
    ∫ ω, C.U ω k * (starRingEnd ℂ) (C.U ω k) ∂(P d)
      = ∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω k l * (starRingEnd ℂ) (C.B ω k l) ∂(P d) := by
  have hptw : ∀ ω : Ω d, C.U ω k * (starRingEnd ℂ) (C.U ω k)
      = ∑ l, ∑ l', (starRingEnd ℂ) (C.h ω l) *
        (C.h ω l' * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l'))) := by
    intro ω
    show (∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)) *
        (starRingEnd ℂ) (∑ l', C.B ω k l' * (starRingEnd ℂ) (C.h ω l')) = _
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
  exact C.integral_conj_h_sum hG (fun l l' ω => C.B ω k l * (starRingEnd ℂ) (C.B ω k l'))
    (fun l l' => (C.tameB k l).mul (C.tameB k l').conj)
    (fun l l' ω m b t => by rw [C.B_update ω m b t])

theorem integral_V_conj_V (k : κ) :
    ∫ ω, C.V ω k * (starRingEnd ℂ) (C.V ω k) ∂(P d)
      = ∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω l k * (starRingEnd ℂ) (C.B ω l k) ∂(P d) := by
  have hptw : ∀ ω : Ω d, C.V ω k * (starRingEnd ℂ) (C.V ω k)
      = ∑ l, ∑ l', (starRingEnd ℂ) (C.h ω l) *
        (C.h ω l' * (C.B ω l' k * (starRingEnd ℂ) (C.B ω l k))) := by
    intro ω
    show (∑ m, C.h ω m * C.B ω m k) *
        (starRingEnd ℂ) (∑ m', C.h ω m' * C.B ω m' k) = _
    rw [map_sum, Finset.sum_mul]
    have e1 : ∀ i : κ, C.h ω i * C.B ω i k * (∑ x, (starRingEnd ℂ) (C.h ω x * C.B ω x k))
        = ∑ x, (starRingEnd ℂ) (C.h ω x) *
          (C.h ω i * (C.B ω i k * (starRingEnd ℂ) (C.B ω x k))) := by
      intro i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_comm]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
  exact C.integral_conj_h_sum hG (fun l l' ω => C.B ω l' k * (starRingEnd ℂ) (C.B ω l k))
    (fun l l' => (C.tameB l' k).mul (C.tameB l k).conj)
    (fun l l' ω m b t => by rw [C.B_update ω m b t])

omit hG in
theorem Vq_complex (ω : Ω d) : ((C.Vq ω : ℝ) : ℂ)
    = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)) := by
  show ((∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ofReal_normSq]
  ring

omit hG in
theorem tame_ofReal_Vq : Tame d fun ω => ((C.Vq ω : ℝ) : ℂ) := by
  rw [funext fun ω => C.Vq_complex ω]
  exact Tame.sum _ fun k _ => Tame.sum _ fun l _ =>
    (Tame.const (d := d) (((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ))).mul
      ((C.tameB k l).mul (C.tameB k l).conj)

omit hG in
theorem Tq_complex (ω : Ω d) : ((C.Tq ω : ℝ) : ℂ)
    = ∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.U ω k)
      + C.V ω k * (starRingEnd ℂ) (C.V ω k)) := by
  show ((∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]

/-- `E[T] = 2 E ∑_{k,l} σ_k ‖B_{kl}‖² σ_l`. -/
theorem momT_zero : C.momT 0 = 2 * ∫ ω, C.Vq ω ∂(P d) := by
  have hnB : ∀ k l : κ, Tame d fun ω => C.B ω k l * (starRingEnd ℂ) (C.B ω k l) := fun k l =>
    (C.tameB k l).mul (C.tameB k l).conj
  have htUV : ∀ k : κ, Tame d fun ω => ((C.sg k : ℝ) : ℂ) *
      (C.U ω k * (starRingEnd ℂ) (C.U ω k) + C.V ω k * (starRingEnd ℂ) (C.V ω k)) := fun k =>
    (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
      (((C.tameU k).mul (C.tameU k).conj).add ((C.tameV k).mul (C.tameV k).conj))
  have hT0 : C.momT 0 = ∫ ω, C.Tq ω ∂(P d) := by
    show ∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * 0) ∂(P d) = _
    simp
  -- the left-hand side, in complex form
  have hL : ((C.momT 0 : ℝ) : ℂ)
      = ∑ k, ((C.sg k : ℝ) : ℂ) *
        ((∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω k l * (starRingEnd ℂ) (C.B ω k l) ∂(P d))
          + ∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω l k * (starRingEnd ℂ) (C.B ω l k) ∂(P d)) := by
    rw [hT0, ← integral_ofReal' (fun ω => C.Tq ω),
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => C.Tq_complex ω),
      MeasureTheory.integral_finsetSum _ fun k _ => (htUV k).integrable hG]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
      (((C.tameU k).mul (C.tameU k).conj).integrable hG)
      (((C.tameV k).mul (C.tameV k).conj).integrable hG),
      C.integral_U_conj_U hG k, C.integral_V_conj_V hG k]
  -- the right-hand side, in complex form
  have hR : ((∫ ω, C.Vq ω ∂(P d) : ℝ) : ℂ)
      = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
        ∫ ω, C.B ω k l * (starRingEnd ℂ) (C.B ω k l) ∂(P d) := by
    rw [← integral_ofReal' (fun ω => C.Vq ω),
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => C.Vq_complex ω),
      MeasureTheory.integral_finsetSum _ fun k _ =>
        (Tame.sum _ fun l _ => (Tame.const (d := d)
          (((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ))).mul (hnB k l)).integrable hG]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MeasureTheory.integral_finsetSum _ fun l _ =>
      ((Tame.const (d := d) (((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ))).mul
        (hnB k l)).integrable hG]
    exact Finset.sum_congr rfl fun l _ => MeasureTheory.integral_const_mul _ _
  -- combine
  have hkey : ((C.momT 0 : ℝ) : ℂ) = 2 * ((∫ ω, C.Vq ω ∂(P d) : ℝ) : ℂ) := by
    rw [hL, hR]
    have e1 : ∑ k, ((C.sg k : ℝ) : ℂ) *
          (∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω k l * (starRingEnd ℂ) (C.B ω k l) ∂(P d))
        = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
          ∫ ω, C.B ω k l * (starRingEnd ℂ) (C.B ω k l) ∂(P d) :=
      Finset.sum_congr rfl fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ k, ((C.sg k : ℝ) : ℂ) *
          (∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω l k * (starRingEnd ℂ) (C.B ω l k) ∂(P d))
        = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
          ∫ ω, C.B ω k l * (starRingEnd ℂ) (C.B ω k l) ∂(P d) := by
      have step : ∀ k : κ, ((C.sg k : ℝ) : ℂ) *
            (∑ l, ((C.sg l : ℝ) : ℂ) * ∫ ω, C.B ω l k * (starRingEnd ℂ) (C.B ω l k) ∂(P d))
          = ∑ l, ((C.sg l : ℝ) : ℂ) * ((C.sg k : ℝ) : ℂ) *
            ∫ ω, C.B ω l k * (starRingEnd ℂ) (C.B ω l k) ∂(P d) := by
        intro k
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_congr rfl fun k _ => step k]
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl fun k _ => by
      rw [mul_add]]
    rw [Finset.sum_add_distrib, e1, e2]
    ring
  exact_mod_cast hkey

/-- **The variance, (4.7) at `p = 1`**: for a Gaussian row independent of `B`,

`E|Q|² = E ∑_{k,l} σ_k ‖B_{kl}‖² σ_l`

exactly (constant `1`).  This is the `p = 1` case the ticket asks for first, and it pins down
every normalization in the file. -/
theorem mom_one : C.mom 1 = ∫ ω, C.Vq ω ∂(P d) := by
  have h1 := C.two_mul_mom_one hG
  have h2 := C.momT_zero hG
  linarith

/-! #### Closing the recursion: `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` -/

/-- `E[T^q]`, the positive-chaos moment that the recursion reduces everything to. -/
noncomputable def momTpow (q : ℕ) : ℝ := ∫ ω, C.Tq ω ^ q ∂(P d)

theorem integrable_Tq_pow (q : ℕ) : Integrable (fun ω => C.Tq ω ^ q) (P d) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω => ((C.Tq ω ^ q : ℝ) : ℂ)) = fun ω => ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tameTq.pow q

omit hG in
theorem momTpow_nonneg (q : ℕ) : 0 ≤ C.momTpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Tq_nonneg ω) q

/-- **Hanson–Wright, the moment bound.**  `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` for `p ≥ 1`.

The recursion `2E|Q|^{2(q+1)} ≤ (2q+1)E[T|Q|^{2q}]` is closed by the pointwise Young inequality
`RBM.Gauss.young_pow` with the *rational* parameter `K = 2q+1`, which keeps every exponent a
natural number and needs no Hölder inequality.

What remains, to reach the paper's `∑_{k,l}σ_k‖B_{kl}‖²σ_l`, is the positive-chaos bound
`E[T^p] ≤ C_p E[Vq^p]`; see the file header. -/
theorem mom_succ_le (q : ℕ) :
    C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := by
  set K : ℝ := 2 * (q : ℝ) + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  -- the pointwise Young inequality
  have hpt : ∀ ω : Ω d, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1)) := by
    intro ω
    have hT := C.Tq_nonneg ω
    have hy := young_pow q (mul_nonneg hT hK0.le) (sq_nonneg ‖C.chaos ω‖)
    rw [mul_pow] at hy
    have hg : ∀ j : ℕ, ‖C.chaos ω‖ ^ (2 * j) = (‖C.chaos ω‖ ^ 2) ^ j := fun j => pow_mul _ 2 j
    rw [hg q, hg (q + 1)]
    have hmul : (0 : ℝ) < ((q : ℝ) + 1) * K := by positivity
    refine le_of_mul_le_mul_left ?_ hmul
    have hleft : ((q : ℝ) + 1) * K * (C.Tq ω * (‖C.chaos ω‖ ^ 2) ^ q)
        = ((q : ℝ) + 1) * (C.Tq ω * K * (‖C.chaos ω‖ ^ 2) ^ q) := by ring
    have hrhs : ((q : ℝ) + 1) * K * ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
          + ((q : ℝ) / (((q : ℝ) + 1) * K)) * (‖C.chaos ω‖ ^ 2) ^ (q + 1))
        = C.Tq ω ^ (q + 1) * K ^ (q + 1) + (q : ℝ) * (‖C.chaos ω‖ ^ 2) ^ (q + 1) := by
      field_simp
      ring
    rw [hleft, hrhs]
    exact hy
  -- integrate
  have hi1 := C.integrable_Tq_pow hG (q + 1)
  have hi2 := C.integrable_norm_pow hG (q + 1)
  have hmomT : C.momT q ≤ (K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
      + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1) := by
    calc C.momT q ≤ ∫ ω, ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
            + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1))) ∂(P d) :=
          MeasureTheory.integral_mono (C.integrable_Tq_mul hG q)
            ((hi1.const_mul _).add (hi2.const_mul _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
  -- close the recursion
  have hrec := C.two_mul_mom_succ_le hG q
  rw [← hKdef] at hrec
  have hm := C.mom_nonneg (q + 1)
  have ht := C.momTpow_nonneg (q + 1)
  have hKmul : K * ((K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1))
      = (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    field_simp
    ring
  have hchain : 2 * C.mom (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    refine hrec.trans ?_
    rw [← hKmul]
    exact mul_le_mul_of_nonneg_left hmomT hK0.le
  have hB : (q : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hq1]; linarith
  have hA : K ^ (q + 1) / ((q : ℝ) + 1) ≤ K ^ (q + 1) := by
    rw [div_le_iff₀ hq1]
    nlinarith [pow_nonneg hK0.le (q + 1), Nat.cast_nonneg (α := ℝ) q]
  have h1 : (q : ℝ) / ((q : ℝ) + 1) * C.mom (q + 1) ≤ C.mom (q + 1) := by
    nlinarith [hm, hB]
  have h3 : K ^ (q + 1) / ((q : ℝ) + 1) * C.momTpow (q + 1)
      ≤ K ^ (q + 1) * C.momTpow (q + 1) := mul_le_mul_of_nonneg_right hA ht
  linarith

end Real

/-! #### The shape of `RBM.ldeQuadLHS` and `RBM.ldeQuadRHS`

The chaos and its control are literally the two sides of the paper's quadratic large deviation
estimate, once the row chaos is indexed by `{k // k ≠ i}` with `h_k = H_{ik}` and
`σ_k = t S_{ik}`.  These two lemmas are pure reindexing (`Finset.sum_subtype`) and contain no
analysis; they are the interface through which a concrete instance — the one T84 and T85 will
build out of `greenMinor (green (Hflow d N u ω) z) i` — meets `RBM.LDEQuad`. -/

section LDEShape

variable {n : Type*} [Fintype n] [DecidableEq n] {i : n}

omit [DecidableEq κ] in
theorem sum_erase_eq {M : Type*} [AddCommMonoid M] (f : n → M) :
    ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {k : n // k ≠ i}, f k.1 :=
  Finset.sum_subtype _ (fun x => by simp [Finset.mem_erase]) _

/-- **The chaos is the left-hand side of (4.7).** -/
theorem norm_chaos_sq_eq_ldeQuadLHS (C : RowChaos d {k : n // k ≠ i}) (ω : Ω d)
    (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hh : ∀ k : {k : n // k ≠ i}, C.h ω k = H i k.1)
    (hhc : ∀ k : {k : n // k ≠ i}, (starRingEnd ℂ) (C.h ω k) = H k.1 i)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1) :
    ‖C.chaos ω‖ ^ 2 = ldeQuadLHS H G S t i := by
  have e1 : ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
        H i k * greenMinor G i k l * H l i
      = ∑ k : {k : n // k ≠ i}, ∑ l : {k : n // k ≠ i},
        C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    rw [sum_erase_eq (i := i)
      fun k => ∑ l ∈ Finset.univ.erase i, H i k * greenMinor G i k l * H l i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_erase_eq (i := i) fun l => H i k.1 * greenMinor G i k.1 l * H l i]
    exact Finset.sum_congr rfl fun l _ => by rw [hh k, hB k l, hhc l]
  have e2 : (t : ℂ) * ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) * greenMinor G i k k
      = ∑ k : {k : n // k ≠ i}, ((C.sg k : ℝ) : ℂ) * C.B ω k k := by
    rw [sum_erase_eq (i := i) fun k => (S i k : ℂ) * greenMinor G i k k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB k k, hsg k, Complex.ofReal_mul]
    ring
  show ‖C.chaos ω‖ ^ 2 = ‖_ - _‖ ^ 2
  rw [e1, e2]
  rfl

/-- **`Vq` is the right-hand side of (4.7)**, up to the factor `t²` coming from
`E|H_{ik}|² = t S_{ik}`. -/
theorem Vq_eq_ldeQuadRHS (C : RowChaos d {k : n // k ≠ i}) (ω : Ω d)
    (G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1)
    (hsg' : ∀ k : {k : n // k ≠ i}, C.sg k = t * S k.1 i) :
    C.Vq ω = t ^ 2 * ldeQuadRHS S G i := by
  show ∑ k : {k : n // k ≠ i}, ∑ l : {k : n // k ≠ i},
      C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l = _
  rw [show ldeQuadRHS S G i = ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i from rfl,
    sum_erase_eq (i := i) fun k => ∑ l ∈ Finset.univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_erase_eq (i := i) fun l => S i k.1 * ‖greenMinor G i k.1 l‖ ^ 2 * S l i,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hB k l, hsg k, hsg' l]
  ring

/-- **(4.7) at `p = 1`, in the paper's own notation.**  For the Gaussian row `i` of `H`, with
`B = G^{(i)}` independent of that row,

`E[ldeQuadLHS] = t² · E[ldeQuadRHS]`,

an exact identity.  This is the `≺` statement of `RBM.LDEQuad` at the level of second moments;
the `N^τ` of Definition 2.1 (i) is not needed at `p = 1`. -/
theorem integral_ldeQuadLHS_eq (hG : GaussIBP d) (C : RowChaos d {k : n // k ≠ i})
    (H G : Ω d → Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hh : ∀ (ω : Ω d) (k : {k : n // k ≠ i}), C.h ω k = H ω i k.1)
    (hhc : ∀ (ω : Ω d) (k : {k : n // k ≠ i}), (starRingEnd ℂ) (C.h ω k) = H ω k.1 i)
    (hB : ∀ (ω : Ω d) (k l : {k : n // k ≠ i}), C.B ω k l = greenMinor (G ω) i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1)
    (hsg' : ∀ k : {k : n // k ≠ i}, C.sg k = t * S k.1 i) :
    ∫ ω, ldeQuadLHS (H ω) (G ω) S t i ∂(P d)
      = t ^ 2 * ∫ ω, ldeQuadRHS S (G ω) i ∂(P d) := by
  have hL : ∫ ω, ldeQuadLHS (H ω) (G ω) S t i ∂(P d) = C.mom 1 := by
    show _ = ∫ ω, ‖C.chaos ω‖ ^ (2 * 1) ∂(P d)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    rw [show 2 * 1 = 2 from rfl]
    exact (C.norm_chaos_sq_eq_ldeQuadLHS ω (H ω) (G ω) S t (hh ω) (hhc ω) (hB ω) hsg).symm
  have hR : ∫ ω, C.Vq ω ∂(P d) = t ^ 2 * ∫ ω, ldeQuadRHS S (G ω) i ∂(P d) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      C.Vq_eq_ldeQuadRHS ω (G ω) S t (hB ω) hsg hsg')
  rw [hL, C.mom_one hG, hR]

end LDEShape

end RowChaos

end RBM.Gauss



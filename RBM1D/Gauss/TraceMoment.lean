/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.IBP
import RBM1D.Gauss.OpNorm

/-!
# The trace moments `E Tr(X^{2p}) ≤ C_p N` (T109)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*: the moment input
`RBM.Gauss.TraceMomentBound` of `RBM1D/Gauss/OpNorm.lean`, which was the one hypothesis left in
the chain `E Tr(X^{2p}) ≤ C_p N ⟹ ‖X‖ ≺ 1` (T100).  With it `RBM.Gauss.OpNormBound` becomes a
theorem and the openly recorded gap `paper-deltas` #49 is closed.

## The route: Gaussian integration by parts, not Wick + walk counting

T100 recorded that the moment method needs Isserlis' formula and the counting of closed walks,
neither of which Mathlib has.  Both are avoided here.  The integrand of `Tr(X^{2p})` is a
*polynomial* in the Gaussian coordinates, hence `RBM.Gauss.Tame`, so T104's
`RBM.Gauss.gaussIBP` applies to it directly.

**Step 0 (the identity, verified in this repository's real parametrization).**  `X` is affine
in each independent coordinate with slope `B_p` (`RBM.Gauss.Xmat_update`), so the coordinate
derivative of `(B_p X^m)_{aa}` is the sandwich `∑_{k+l=m-1}(B_p X^k B_p X^l)_{aa}`
(`RBM.Gauss.hasDerivAt_const_mul_Xmat_pow_update`), and the `gvar`-weighted coordinate sum of
the sandwich collapses (`RBM.Gauss.sum_gvar_Bmat_sandwich_apply`) — the two tags of an
off-diagonal pair carry `gvar = S_{ij}/2` each and their off-diagonal contributions cancel, so
the factor `2` is exactly absorbed.  The outcome is
`RBM.Gauss.integral_Xmat_pow_succ_diag`:

  `E[(X^{m+1})_{aa}] = ∑_{k+l=m-1} E[ (∑_j S_{aj}(X^k)_{jj}) · (X^l)_{aa} ]`.

At `m = 1` it degenerates to `E[(X²)_{aa}] = ∑_j S_{aj} = 1` (`RBM.Gauss.integral_colSq_one`),
which is the `p = 1` sanity check of `RBM.Gauss.traceMomentBound_one`
(`E Tr(X²) = ∑_{ij} S_{ij} = W L`).

**Closing the recursion.**  A plain Cauchy–Schwarz on `E[(X^k)_{jj}(X^l)_{ii}]` would replace
degree `k` by degree `2k` and the induction would not be well founded (`k` can be as large as
`2p-2`).  What prevents the doubling is the *log-convexity* of the column norms
`u_m(i) = ∑_r |(X^m)_{ri}|² = (X^{2m})_{ii}`: `u_m² ≤ u_{m-1} u_{m+1}` by Cauchy–Schwarz and
`u_0 = 1`, hence `u_k ≤ u_M^{k/M}` for `k ≤ M` (`RBM.Gauss.pow_le_pow_of_logConvex`), hence

  `|(X^k)_{ii}| ≤ u_M(i)^{k/(2M)}`  for every `k ≤ 2M`

(`RBM.Gauss.norm_pow_apply_diag_le_rpow`).  With `k + l = 2M` the weighted AM–GM inequality
turns the product into a convex combination,

  `|(X^k)_{jj}| |(X^l)_{ii}| ≤ (k/2M) u_M(j) + (l/2M) u_M(i)`

(`RBM.Gauss.norm_mul_norm_pow_diag_le`), and since `∑_j S_{ij} = 1` the recursion at
`m = 2M+1` has `2M+1` terms each bounded by `sup_i E u_M(i)`.  Induction on `M` gives
`E[(X^{2M})_{ii}] ≤ C_M` with `C_0 = 1`, `C_{M+1} = (2M+1) C_M`, i.e. `C_M = (2M-1)!!`
(`RBM.Gauss.integral_colSq_le`) — the double factorial, a crude but sufficient upper bound for
the Catalan number of the paper.  Summing over the `W L ≤ N` indices gives
`E Tr(X^{2p}) ≤ C_p N`.

## Main definitions

* `RBM.Gauss.colSq` — `u_m(i) = ∑_r |(A^m)_{ri}|²`, the squared norm of the `i`-th column of
  `A^m`; equals `(A^{2m})_{ii}` for Hermitian `A`.
* `RBM.Gauss.traceConst` — the constants `C_M = (2M-1)!!` of the recursion.

## Main results

* `RBM.Gauss.hasDerivAt_matPow_apply`, `RBM.Gauss.hasDerivAt_const_mul_Xmat_pow_update` — the
  Leibniz rule for `(A + rB)^m` and the coordinate derivative of `(C X^m)_{ab}`.
* `RBM.Gauss.tame_Xentry`, `RBM.Gauss.tame_Xmat_pow_apply`, `RBM.Gauss.tame_sandwich_apply` —
  every integrand here is `Tame`, hence integrable and admissible in `gaussIBP`.
* `RBM.Gauss.sum_gvar_Bmat_sandwich_apply` — the coordinate sum collapses to a row of `S`.
* `RBM.Gauss.integral_Xmat_pow_succ_diag` — **step 0**, the self-consistent recursion.
* `RBM.Gauss.pow_le_pow_of_logConvex`, `RBM.Gauss.norm_pow_apply_diag_le_rpow`,
  `RBM.Gauss.norm_mul_norm_pow_diag_le` — the deterministic half.
* `RBM.Gauss.integral_colSq_one`, `RBM.Gauss.integral_colSq_le` — the induction on `M`.
* `RBM.Gauss.traceMomentBound_gauss`, `RBM.Gauss.stochDom_norm_Xmat_gauss`,
  `RBM.Gauss.opNormBound_gauss` — `E Tr(X^{2p}) ≤ C_p N`, `‖X‖ ≺ 1` and `OpNormBound`, all
  unconditional.

No `sorry` and no `axiom`; the frozen interfaces `RBM.Gauss.TraceMomentBound`,
`RBM.Gauss.opNormBound_of_traceMomentBound` and `RBM.Gauss.OpNormBound` are untouched.

## What is **not** done here

The constant is `(2p-1)!!`, not the Catalan number `Cat_p` of the paper, and no lower bound on
the trace moments is proved; neither is used downstream.  `RBM.Gauss.Dims` still has no
inhabitant, so the whole moment route remains conditional on a concrete `W, L` — see
`RBM1D/Gauss/Model.lean`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ### The derivative of a matrix power along a line -/

section MatrixDeriv

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The derivative of an entry of `(A + r B)^m` in `r`.**  The Leibniz rule for a
noncommutative product: `d/dr (A + rB)^m = ∑_{k+l=m-1} M^k B M^l`. -/
theorem hasDerivAt_matPow_apply (A B : Matrix n n ℂ) (s : ℝ) (m : ℕ) (a b : n) :
    HasDerivAt (fun r : ℝ => ((A + r • B) ^ m) a b)
      (∑ k ∈ Finset.range m, (((A + s • B) ^ k * B * (A + s • B) ^ (m - 1 - k)) a b)) s := by
  have hofReal : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := RowChaos.hasDerivAt_ofReal_id s
  induction m generalizing a b with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact hasDerivAt_const s _
  | succ m ih =>
    set M := A + s • B with hM
    have hlin : ∀ c : n, HasDerivAt (fun r : ℝ => (A + r • B) c b) (B c b) s := by
      intro c
      have hfun : (fun r : ℝ => (A + r • B) c b) = fun r : ℝ => A c b + (r : ℂ) * B c b := by
        funext r
        simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      rw [hfun]
      simpa using (hofReal.mul_const (B c b)).const_add (A c b)
    have hfun : (fun r : ℝ => ((A + r • B) ^ (m + 1)) a b)
        = fun r : ℝ => ∑ c : n, ((A + r • B) ^ m) a c * (A + r • B) c b := by
      funext r
      rw [pow_succ, Matrix.mul_apply]
    have hval : ∑ k ∈ Finset.range (m + 1), ((M ^ k * B * M ^ (m + 1 - 1 - k)) a b)
        = ∑ c : n, ((∑ k ∈ Finset.range m, ((M ^ k * B * M ^ (m - 1 - k)) a c)) * M c b
            + (M ^ m) a c * B c b) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      congr 1
      · simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < m := Finset.mem_range.1 hk
        rw [← Matrix.mul_apply]
        have he : m - k = (m - 1 - k) + 1 := by omega
        rw [he, pow_succ, ← mul_assoc]
      · rw [Nat.sub_self, pow_zero, mul_one, Matrix.mul_apply]
    rw [hfun, hval]
    exact HasDerivAt.fun_sum fun c _ => (ih a c).mul (hlin c)

end MatrixDeriv

/-! ### Entries of powers of `X` are tame -/

section TamePow

variable {d : Dims} {N : ℕ}

/-- Every entry of `X` is tame: it is a real-linear combination of two Gaussian coordinates. -/
theorem tame_Xentry (d : Dims) (N : ℕ) (i j : d.Idx N) :
    Tame d (fun ω : Ω d => Xentry d N ω i j) := by
  unfold Xentry
  by_cases h1 : idxKey d N i < idxKey d N j
  · simp only [ite_eq_left h1]
    exact (Tame.coord _).add ((Tame.const (d := d) Complex.I).mul (Tame.coord _))
  · simp only [ite_eq_right h1]
    by_cases h2 : idxKey d N j < idxKey d N i
    · simp only [ite_eq_left h2]
      exact (Tame.coord _).sub ((Tame.const (d := d) Complex.I).mul (Tame.coord _))
    · simp only [ite_eq_right h2]
      exact Tame.coord _

/-- Every entry of `C · X^m`, for a constant matrix `C`, is tame: it is a polynomial in the
Gaussian coordinates. -/
theorem tame_const_mul_Xmat_pow_apply (d : Dims) (N : ℕ)
    (C : Matrix (d.Idx N) (d.Idx N) ℂ) (m : ℕ) (a b : d.Idx N) :
    Tame d (fun ω : Ω d => (C * Xmat d N ω ^ m) a b) := by
  have hpow : ∀ (m : ℕ) (a b : d.Idx N), Tame d (fun ω : Ω d => (Xmat d N ω ^ m) a b) := by
    intro m
    induction m with
    | zero =>
      intro a b
      simp only [pow_zero, Matrix.one_apply]
      by_cases h : a = b
      · simp only [ite_eq_left h]; exact Tame.const (d := d) 1
      · simp only [ite_eq_right h]; exact Tame.const (d := d) 0
    | succ m ih =>
      intro a b
      have he : ∀ ω : Ω d, (Xmat d N ω ^ (m + 1)) a b
          = ∑ c : d.Idx N, (Xmat d N ω ^ m) a c * Xentry d N ω c b := by
        intro ω
        rw [pow_succ, Matrix.mul_apply]
        rfl
      simp only [he]
      exact Tame.sum _ fun c _ => (ih a c).mul (tame_Xentry d N c b)
  have he : ∀ ω : Ω d, (C * Xmat d N ω ^ m) a b
      = ∑ c : d.Idx N, C a c * (Xmat d N ω ^ m) c b := by
    intro ω
    rw [Matrix.mul_apply]
  simp only [he]
  exact Tame.sum _ fun c _ => (Tame.const (d := d) (C a c)).mul (hpow m c b)

/-- Entries of powers of `X` are tame. -/
theorem tame_Xmat_pow_apply (d : Dims) (N : ℕ) (m : ℕ) (a b : d.Idx N) :
    Tame d (fun ω : Ω d => (Xmat d N ω ^ m) a b) := by
  have h := tame_const_mul_Xmat_pow_apply d N 1 m a b
  simpa using h

/-- Entries of `C · X^k · C' · X^l` are tame. -/
theorem tame_sandwich_apply (d : Dims) (N : ℕ)
    (C C' : Matrix (d.Idx N) (d.Idx N) ℂ) (k l : ℕ) (a b : d.Idx N) :
    Tame d (fun ω : Ω d => (C * (Xmat d N ω ^ k * C' * Xmat d N ω ^ l)) a b) := by
  have he : ∀ ω : Ω d, (C * (Xmat d N ω ^ k * C' * Xmat d N ω ^ l)) a b
      = ∑ c : d.Idx N, (C * Xmat d N ω ^ k) a c * (C' * Xmat d N ω ^ l) c b := by
    intro ω
    rw [← Matrix.mul_apply]
    simp only [mul_assoc]
  simp only [he]
  exact Tame.sum _ fun c _ =>
    (tame_const_mul_Xmat_pow_apply d N C k a c).mul (tame_const_mul_Xmat_pow_apply d N C' l c b)

end TamePow

/-! ### The coordinate sum of the integration-by-parts display

`∑_{p ∈ usedCoord} gvar_p (B_p M B_p M')_{aa} = (∑_j S_{aj} M_{jj}) M'_{aa}`.  This is
`RBM.Gauss.sum_gvar_Bmat_sandwich_diag` of `RBM1D/Gauss/IBP.lean` with the two resolvents
replaced by two arbitrary matrices; the proof is the same bookkeeping. -/

section Sandwich

variable {d : Dims} {N : ℕ}

/-- **The two tags of an off-diagonal coordinate.**  The off-diagonal terms carry opposite
signs and cancel; twice `M_{yy} M'_{aa}` (resp. `M_{xx} M'_{aa}`) survives. -/
theorem Bmat_sandwich_apply_add_of_ne (M M' : Matrix (d.Idx N) (d.Idx N) ℂ)
    {x y : d.Idx N} (hxy : x ≠ y) (a : d.Idx N) :
    (Bmat d N x y true * (M * Bmat d N x y true * M')) a a
      + (Bmat d N x y false * (M * Bmat d N x y false * M')) a a
      = 2 * ((if a = x then M y y * M' a a else 0)
          + (if a = y then M x x * M' a a else 0)) := by
  have hB : ∀ b : Bool, (Bmat d N x y b * (M * Bmat d N x y b * M')) a a
      = (if b then (1 : ℂ) else Complex.I)
          * ((1 : Matrix (d.Idx N) (d.Idx N) ℂ) a x * (M * Bmat d N x y b * M') y a)
        + (if b then (1 : ℂ) else -Complex.I)
          * ((1 : Matrix (d.Idx N) (d.Idx N) ℂ) a y * (M * Bmat d N x y b * M') x a) := by
    intro b
    have h := mul_Bmat_mul_apply_of_ne (M := (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
      (M' := M * Bmat d N x y b * M') hxy b a a
    rw [Matrix.one_mul] at h
    exact h
  have hKt := fun (p q : d.Idx N) => mul_Bmat_mul_apply_of_ne (M := M) (M' := M') hxy true p q
  have hKf := fun (p q : d.Idx N) => mul_Bmat_mul_apply_of_ne (M := M) (M' := M') hxy false p q
  rw [hB true, hB false, hKt, hKt, hKf, hKf]
  simp only [Bool.false_eq_true, reduceIte]
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := hxy
    rw [Matrix.one_apply_eq, Matrix.one_apply_ne hay, ite_eq_left rfl, ite_eq_right hay]
    ring_nf
    rw [Complex.I_sq]
    ring
  · by_cases hay : a = y
    · subst hay
      rw [Matrix.one_apply_eq, Matrix.one_apply_ne hax, ite_eq_left rfl, ite_eq_right hax]
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [Matrix.one_apply_ne hax, Matrix.one_apply_ne hay, ite_eq_right hax, ite_eq_right hay]
      ring

/-- **The diagonal coordinate.**  `B_{ii,true} = E_{ii}`, so the sandwich is a single term. -/
theorem Bmat_sandwich_apply_diag (M M' : Matrix (d.Idx N) (d.Idx N) ℂ) (x a : d.Idx N) :
    (Bmat d N x x true * (M * Bmat d N x x true * M')) a a
      = if a = x then M x x * M' a a else 0 := by
  have h := mul_Bmat_mul_apply_diag (M := (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
    (M' := M * Bmat d N x x true * M') x a a
  rw [Matrix.one_mul] at h
  rw [h, mul_Bmat_mul_apply_diag]
  by_cases hax : a = x
  · subst hax; simp
  · simp [hax]

/-- **The coordinate sum collapses to a row of `S`.**

`∑_{p ∈ usedCoord} gvar_p (B_p M B_p M')_{aa} = (∑_j S_{aj} M_{jj}) · M'_{aa}`: the two tags of
an off-diagonal coordinate each carry `gvar = S/2` and the squared off-diagonal terms cancel
between them, while the diagonal coordinate (real tag only, `gvar = S`) supplies
`S_{aa} M_{aa} M'_{aa}`. -/
theorem sum_gvar_Bmat_sandwich_apply (d : Dims) (N : ℕ)
    (M M' : Matrix (d.Idx N) (d.Idx N) ℂ) (a : d.Idx N) :
    ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        (Bmat d N p.1 p.2.1 p.2.2 * (M * Bmat d N p.1 p.2.1 p.2.2 * M')) a a
      = (∑ j, (Sblk (d.L N) (d.W N) a j : ℂ) * M j j) * M' a a := by
  classical
  set f : d.Idx N × d.Idx N × Bool → ℂ :=
    fun p => (Bmat d N p.1 p.2.1 p.2.2 * (M * Bmat d N p.1 p.2.1 p.2.2 * M')) a a with hf
  set h : d.Idx N → d.Idx N → ℂ :=
    fun i j => if i = a then (Sblk (d.L N) (d.W N) i j : ℂ) * M j j * M' a a else 0 with hh
  have hgv : ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • f p
      = ∑ p ∈ usedCoord d N,
        (if p.1 = p.2.1 then Sblk (d.L N) (d.W N) p.1 p.2.1
         else Sblk (d.L N) (d.W N) p.1 p.2.1 / 2) • f p :=
    Finset.sum_congr rfl fun p _ => by rw [gvar_crd]
  rw [hgv, show usedCoord d N = Finset.univ.filter
      (fun p : d.Idx N × d.Idx N × Bool =>
        idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
    sum_used_eq_sum_pairs_of_swap (idxKey d N) (idxKey_injective d N)
      (Sblk (d.L N) (d.W N)) f h ?_ ?_]
  · -- `∑_i ∑_j h i j = (∑_j S_{aj} M_{jj}) M'_{aa}`
    rw [Finset.sum_comm]
    simp only [hh, Finset.sum_ite_eq' Finset.univ a, Finset.mem_univ, ite_true, Finset.sum_mul]
  · -- the diagonal coordinate
    intro i
    simp only [hf, hh, Bmat_sandwich_apply_diag M M' i a, Complex.real_smul]
    by_cases hai : a = i
    · subst hai
      simp only [ite_true]
      ring
    · have hia : ¬ (i = a) := fun hx => hai hx.symm
      simp only [ite_eq_right hai, ite_eq_right hia]
      ring
  · -- the two tags of an off-diagonal coordinate
    intro i j hij
    simp only [hf, hh, Complex.real_smul]
    rw [← mul_add, Bmat_sandwich_apply_add_of_ne M M' hij a]
    by_cases hai : a = i
    · subst hai
      have hja : ¬ (j = a) := fun hx => hij hx.symm
      have hay : ¬ a = j := hij
      simp only [ite_true, ite_eq_right hay, ite_eq_right hja]
      push_cast
      ring
    · have hia : ¬ (i = a) := fun hx => hai hx.symm
      by_cases haj : a = j
      · subst haj
        have hja : ¬ (i = a) := hia
        simp only [ite_true, ite_eq_right hai, ite_eq_right hia]
        rw [Sblk_comm (d.L N) (d.W N) a i]
        push_cast
        ring
      · have hja : ¬ (j = a) := fun hx => haj hx.symm
        simp only [ite_eq_right hai, ite_eq_right haj, ite_eq_right hia, ite_eq_right hja]
        push_cast
        ring

end Sandwich

/-! ### Step 0: the integration by parts

Moving one Gaussian coordinate moves `X` along `B_p` (`RBM.Gauss.Xmat_update`), so Stein's
identity for the tame integrand `(B_p X^m)_{aa}` produces the sandwich
`∑_{k+l=m-1} (B_p X^k B_p X^l)_{aa}`, whose coordinate sum collapses by
`RBM.Gauss.sum_gvar_Bmat_sandwich_apply`.  The outcome is the **self-consistent recursion**

  `E[(X^{m+1})_{aa}] = ∑_{k+l=m-1} E[ (∑_j S_{aj} (X^k)_{jj}) (X^l)_{aa} ]`.

At `m = 1` it degenerates to `E[(X²)_{aa}] = ∑_j S_{aj} = 1`, which is the `p = 1` sanity
check of `RBM.Gauss.traceMomentBound_one`. -/

section IBPStep

variable {d : Dims} {N : ℕ}

/-- **The coordinate derivative of `(C X^m)_{ab}`.**  This is the analogue, for a power of `X`
in place of a resolvent, of `RBM.Gauss.hasDerivAt_green_Hflow_update`. -/
theorem hasDerivAt_const_mul_Xmat_pow_update (d : Dims) (N : ℕ) (m : ℕ)
    (C : Matrix (d.Idx N) (d.Idx N) ℂ) (a b : d.Idx N) (ω : Ω d)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    HasDerivAt (fun t : ℝ => (C * Xmat d N (Function.update ω (crd d N p) t) ^ m) a b)
      (∑ k ∈ Finset.range m,
        (C * (Xmat d N ω ^ k * Bmat d N p.1 p.2.1 p.2.2 * Xmat d N ω ^ (m - 1 - k))) a b)
      (ω (crd d N p)) := by
  set c := crd d N p with hc
  set A := Xmat d N ω with hA
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  have hupd : ∀ t : ℝ, Xmat d N (Function.update ω c t) = A + (t - ω c) • B :=
    fun t => Xmat_update d N ω hp t
  have hrow : ∀ r : d.Idx N, HasDerivAt
      (fun t : ℝ => ((A + (t - ω c) • B) ^ m) r b)
      (∑ k ∈ Finset.range m, ((A ^ k * B * A ^ (m - 1 - k)) r b)) (ω c) := by
    intro r
    have h2 := hasDerivAt_matPow_apply (A - (ω c) • B) B (ω c) m r b
    have heq : A - (ω c) • B + (ω c) • B = A := by abel
    rw [heq] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hshift : A + (t - ω c) • B = A - ω c • B + t • B := by rw [sub_smul]; abel
    show ((A + (t - ω c) • B) ^ m) r b = _
    rw [hshift]
  have hfun : (fun t : ℝ => (C * Xmat d N (Function.update ω c t) ^ m) a b)
      = fun t : ℝ => ∑ r : d.Idx N, C a r * ((A + (t - ω c) • B) ^ m) r b := by
    funext t
    rw [hupd t, Matrix.mul_apply]
  have hval : ∑ k ∈ Finset.range m, (C * (A ^ k * B * A ^ (m - 1 - k))) a b
      = ∑ r : d.Idx N, C a r * ∑ k ∈ Finset.range m, ((A ^ k * B * A ^ (m - 1 - k)) r b) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_apply]
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun r _ => HasDerivAt.const_mul (C a r) (hrow r)

/-- **The integration-by-parts recursion for a diagonal entry.**

`E[(X^{m+1})_{aa}] = ∑_{k+l=m-1} E[ (∑_j S_{aj} (X^k)_{jj}) (X^l)_{aa} ]`.

One Stein identity per independent Gaussian coordinate: `X` is affine in each coordinate with
slope `B_p`, so the derivative of `(B_p X^m)_{aa}` is the sandwich
`∑_{k+l=m-1}(B_p X^k B_p X^l)_{aa}`, and the `gvar`-weighted coordinate sum of the sandwich is
the row `∑_j S_{aj}(X^k)_{jj}` (`RBM.Gauss.sum_gvar_Bmat_sandwich_apply`). -/
theorem integral_Xmat_pow_succ_diag (d : Dims) (N : ℕ) (m : ℕ) (a : d.Idx N) :
    ∫ ω, (Xmat d N ω ^ (m + 1)) a a ∂(P d)
      = ∑ k ∈ Finset.range m, ∫ ω,
          (∑ j, (Sblk (d.L N) (d.W N) a j : ℂ) * (Xmat d N ω ^ k) j j)
            * (Xmat d N ω ^ (m - 1 - k)) a a ∂(P d) := by
  classical
  have hG : GaussIBP d := gaussIBP d
  have hintF : ∀ (p : d.Idx N × d.Idx N × Bool) (k : ℕ),
      Integrable (fun ω : Ω d => (Bmat d N p.1 p.2.1 p.2.2
        * (Xmat d N ω ^ k * Bmat d N p.1 p.2.1 p.2.2
          * Xmat d N ω ^ (m - 1 - k))) a a) (P d) :=
    fun p k => (tame_sandwich_apply d N _ _ k (m - 1 - k) a a).integrable hG
  -- Step 1: `X = ∑_p ω_p B_p`, so the integrand splits over the coordinates.
  have hpt : ∀ ω : Ω d, (Xmat d N ω ^ (m + 1)) a a
      = ∑ p ∈ usedCoord d N,
        (ω (crd d N p) : ℂ) * (Bmat d N p.1 p.2.1 p.2.2 * Xmat d N ω ^ m) a a := by
    intro ω
    have h1 : Xmat d N ω ^ (m + 1)
        = (∑ p ∈ usedCoord d N, ω (crd d N p) • Bmat d N p.1 p.2.1 p.2.2)
          * Xmat d N ω ^ m := by
      rw [← Xmat_eq_sum d N ω, ← pow_succ']
    rw [h1, Finset.sum_mul, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by
      rw [Matrix.smul_mul, Matrix.smul_apply, Complex.real_smul]
  have hstep1 : ∫ ω, (Xmat d N ω ^ (m + 1)) a a ∂(P d)
      = ∑ p ∈ usedCoord d N, ∫ ω, (ω (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * Xmat d N ω ^ m) a a ∂(P d) := by
    simp only [hpt]
    exact integral_finsetSum _ fun p _ =>
      ((Tame.coord (crd d N p)).mul (tame_const_mul_Xmat_pow_apply d N _ m a a)).integrable hG
  -- Step 2: Stein's identity, one coordinate at a time.
  have hstep2 : ∀ p ∈ usedCoord d N,
      ∫ ω, (ω (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * Xmat d N ω ^ m) a a ∂(P d)
        = ∑ k ∈ Finset.range m, ((gvar d (crd d N p) : ℝ) : ℂ) *
            ∫ ω, (Bmat d N p.1 p.2.1 p.2.2
              * (Xmat d N ω ^ k * Bmat d N p.1 p.2.1 p.2.2
                * Xmat d N ω ^ (m - 1 - k))) a a ∂(P d) := by
    intro p hp
    rw [hG.stein (crd d N p)
      (fun ω => (Bmat d N p.1 p.2.1 p.2.2 * Xmat d N ω ^ m) a a)
      (fun ω => ∑ k ∈ Finset.range m, (Bmat d N p.1 p.2.1 p.2.2
        * (Xmat d N ω ^ k * Bmat d N p.1 p.2.1 p.2.2
          * Xmat d N ω ^ (m - 1 - k))) a a)
      (tame_const_mul_Xmat_pow_apply d N _ m a a)
      (Tame.sum _ fun k _ => tame_sandwich_apply d N _ _ k (m - 1 - k) a a)
      (fun ω => hasDerivAt_const_mul_Xmat_pow_update d N m _ a a ω hp),
      integral_finsetSum _ fun k _ => hintF p k, Finset.mul_sum]
  -- Step 3: exchange the two finite sums and collapse the coordinate sum.
  rw [hstep1, Finset.sum_congr rfl hstep2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∀ p : d.Idx N × d.Idx N × Bool,
      ((gvar d (crd d N p) : ℝ) : ℂ) * ∫ ω, (Bmat d N p.1 p.2.1 p.2.2
          * (Xmat d N ω ^ k * Bmat d N p.1 p.2.1 p.2.2
            * Xmat d N ω ^ (m - 1 - k))) a a ∂(P d)
        = ∫ ω, ((gvar d (crd d N p) : ℝ) : ℂ) * (Bmat d N p.1 p.2.1 p.2.2
          * (Xmat d N ω ^ k * Bmat d N p.1 p.2.1 p.2.2
            * Xmat d N ω ^ (m - 1 - k))) a a ∂(P d) :=
    fun p => (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl fun p _ => h1 p,
    ← integral_finsetSum _ fun p _ => (hintF p k).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hsw := sum_gvar_Bmat_sandwich_apply d N (Xmat d N ω ^ k) (Xmat d N ω ^ (m - 1 - k)) a
  simp only [Complex.real_smul] at hsw
  exact hsw

end IBPStep

/-! ### The deterministic half: log-convexity of the column norms

For Hermitian `A` the numbers `u_m(i) = ∑_r |(A^m)_{ri}|² = (A^{2m})_{ii}` (the squared norm of
the `i`-th column of `A^m`) form a **log-convex** sequence with `u_0 = 1`: `u_m² ≤ u_{m-1}
u_{m+1}` by Cauchy–Schwarz.  Hence `u_k ≤ u_M^{k/M}` for `k ≤ M`, which is what converts a
diagonal entry of *any* power `A^k`, `k ≤ 2M`, into a fractional power of the single quantity
`u_M`.  This is the step that keeps the degrees from doubling when the recursion of
`RBM.Gauss.integral_Xmat_pow_succ_diag` is closed. -/

section ColSq

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared norm of the `i`-th column of `A^m`; equals `(A^{2m})_{ii}` for Hermitian `A`. -/
noncomputable def colSq (A : Matrix n n ℂ) (m : ℕ) (i : n) : ℝ := ∑ r, ‖(A ^ m) r i‖ ^ 2

theorem colSq_nonneg (A : Matrix n n ℂ) (m : ℕ) (i : n) : 0 ≤ colSq A m i := by
  unfold colSq; positivity

@[simp] theorem colSq_zero (A : Matrix n n ℂ) (i : n) : colSq A 0 i = 1 := by
  unfold colSq
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [DecidableEq n] in
/-- Cauchy–Schwarz for a Hermitian pairing of two columns. -/
theorem norm_sum_conj_mul_le (u v : n → ℂ) :
    ‖∑ r, (starRingEnd ℂ) (u r) * v r‖
      ≤ Real.sqrt (∑ r, ‖u r‖ ^ 2) * Real.sqrt (∑ r, ‖v r‖ ^ 2) := by
  have h1 : ‖∑ r, (starRingEnd ℂ) (u r) * v r‖ ≤ ∑ r, ‖u r‖ * ‖v r‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
    rw [norm_mul, RCLike.norm_conj]
  have h2 : (∑ r, ‖u r‖ * ‖v r‖) ^ 2 ≤ (∑ r, ‖u r‖ ^ 2) * ∑ r, ‖v r‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : (0 : ℝ) ≤ ∑ r, ‖u r‖ * ‖v r‖ := Finset.sum_nonneg fun r _ => by positivity
  have h4 : Real.sqrt (∑ r, ‖u r‖ ^ 2) * Real.sqrt (∑ r, ‖v r‖ ^ 2)
      = Real.sqrt ((∑ r, ‖u r‖ ^ 2) * ∑ r, ‖v r‖ ^ 2) :=
    (Real.sqrt_mul (Finset.sum_nonneg fun r _ => by positivity) _).symm
  rw [h4]
  exact h1.trans (Real.le_sqrt_of_sq_le h2)

/-- **`(A^{k+l})_{ii}` is the pairing of the `i`-th columns of `A^k` and `A^l`.** -/
theorem pow_add_apply_diag_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) (k l : ℕ) (i : n) :
    (A ^ (k + l)) i i = ∑ r, (starRingEnd ℂ) ((A ^ k) r i) * (A ^ l) r i := by
  have h1 : A ^ (k + l) = (A ^ k)ᴴ * A ^ l := by rw [hA.pow k, pow_add]
  rw [h1, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun r _ => by rw [Matrix.conjTranspose_apply, ← starRingEnd_apply]

/-- **`(A^{2m})_{ii} = ∑_r |(A^m)_{ri}|²`.** -/
theorem pow_two_mul_apply_diag {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : ℕ) (i : n) :
    (A ^ (2 * m)) i i = (colSq A m i : ℂ) := by
  have h : (2 : ℕ) * m = m + m := by ring
  rw [h, pow_add_apply_diag_eq_sum hA m m i, colSq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun r _ => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Every diagonal entry of `A^k` is bounded by the two column norms that split `k`.** -/
theorem norm_pow_apply_diag_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (k l : ℕ) (i : n) :
    ‖(A ^ (k + l)) i i‖ ≤ Real.sqrt (colSq A k i) * Real.sqrt (colSq A l i) := by
  rw [pow_add_apply_diag_eq_sum hA k l i]
  exact norm_sum_conj_mul_le _ _

/-- **Log-convexity**: `u_{m+1}² ≤ u_m · u_{m+2}`. -/
theorem colSq_sq_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : ℕ) (i : n) :
    colSq A (m + 1) i ^ 2 ≤ colSq A m i * colSq A (m + 2) i := by
  have h1 : colSq A (m + 1) i ≤ Real.sqrt (colSq A m i) * Real.sqrt (colSq A (m + 2) i) := by
    have h2 : ((colSq A (m + 1) i : ℝ) : ℂ) = (A ^ (m + (m + 2))) i i := by
      rw [show m + (m + 2) = 2 * (m + 1) by ring, pow_two_mul_apply_diag hA]
    have h3 : colSq A (m + 1) i = ‖(A ^ (m + (m + 2))) i i‖ := by
      rw [← h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (colSq_nonneg _ _ _)]
    rw [h3]
    exact norm_pow_apply_diag_le hA m (m + 2) i
  have h4 : (0 : ℝ) ≤ colSq A (m + 1) i := colSq_nonneg _ _ _
  have h5 : Real.sqrt (colSq A m i) * Real.sqrt (colSq A (m + 2) i)
      = Real.sqrt (colSq A m i * colSq A (m + 2) i) :=
    (Real.sqrt_mul (colSq_nonneg _ _ _) _).symm
  rw [h5] at h1
  have := Real.sq_sqrt (mul_nonneg (colSq_nonneg A m i) (colSq_nonneg A (m + 2) i))
  nlinarith [Real.sqrt_nonneg (colSq A m i * colSq A (m + 2) i)]

/-- Once a column of `A^m` vanishes, all later ones do. -/
theorem colSq_eq_zero_succ {A : Matrix n n ℂ} {m : ℕ} {i : n} (h : colSq A m i = 0) :
    colSq A (m + 1) i = 0 := by
  have hz : ∀ r : n, (A ^ m) r i = 0 := by
    intro r
    have hsum : ∀ r' ∈ (Finset.univ : Finset n), ‖(A ^ m) r' i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun r' _ => by positivity).1 h
    have := hsum r (Finset.mem_univ r)
    have hn : ‖(A ^ m) r i‖ = 0 := by nlinarith [norm_nonneg ((A ^ m) r i)]
    exact norm_eq_zero.1 hn
  have hz' : ∀ r : n, (A ^ (m + 1)) r i = 0 := by
    intro r
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_eq_zero fun s _ => by rw [hz s, mul_zero]
  unfold colSq
  exact Finset.sum_eq_zero fun r _ => by rw [hz' r]; simp

end ColSq

/-! ### Log-convex sequences: `w_k^M ≤ w_M^k` -/

section LogConvex

/-- **A log-convex sequence normalised at `0` has increasing average slope**: from
`w_{k+1}² ≤ w_k w_{k+2}` and `w_0 = 1` one gets `w_k^M ≤ w_M^k` for `k ≤ M`.  This is the
discrete form of "`(log w_k)/k` is nondecreasing", proved without dividing. -/
theorem pow_le_pow_of_logConvex {w : ℕ → ℝ} (hnn : ∀ k, 0 ≤ w k) (h0 : w 0 = 1)
    (hlc : ∀ k, w (k + 1) ^ 2 ≤ w k * w (k + 2)) (hz : ∀ k, w k = 0 → w (k + 1) = 0)
    (k M : ℕ) (hk : k ≤ M) : w k ^ M ≤ w M ^ k := by
  -- the one-step version `w_a^{a+1} ≤ w_{a+1}^a`
  have step : ∀ a : ℕ, w (a + 1) ^ (a + 2) ≤ w (a + 2) ^ (a + 1) := by
    intro a
    induction a with
    | zero =>
      have := hlc 0
      rw [h0, one_mul] at this
      simpa using this
    | succ a ih =>
      by_cases hA : w (a + 1) = 0
      · have h1 : w (a + 2) = 0 := hz _ hA
        rw [h1, zero_pow (by omega)]
        exact pow_nonneg (hnn _) _
      · have hApos : 0 < w (a + 1) := lt_of_le_of_ne (hnn _) (Ne.symm hA)
        by_cases hB : w (a + 2) = 0
        · rw [hB, zero_pow (by omega)]
          exact pow_nonneg (hnn _) _
        · have hBpos : 0 < w (a + 2) := lt_of_le_of_ne (hnn _) (Ne.symm hB)
          have h1 : (w (a + 2) ^ 2) ^ (a + 2) ≤ (w (a + 1) * w (a + 3)) ^ (a + 2) :=
            pow_le_pow_left₀ (by positivity) (hlc (a + 1)) _
          have h2 : (w (a + 1) * w (a + 3)) ^ (a + 2)
              = w (a + 1) ^ (a + 2) * w (a + 3) ^ (a + 2) := mul_pow _ _ _
          have h3 : w (a + 1) ^ (a + 2) * w (a + 3) ^ (a + 2)
              ≤ w (a + 2) ^ (a + 1) * w (a + 3) ^ (a + 2) :=
            mul_le_mul_of_nonneg_right ih (pow_nonneg (hnn _) _)
          have h4 : (w (a + 2) ^ 2) ^ (a + 2) = w (a + 2) ^ (a + 3) * w (a + 2) ^ (a + 1) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            omega
          have h5 : w (a + 2) ^ (a + 3) * w (a + 2) ^ (a + 1)
              ≤ w (a + 3) ^ (a + 2) * w (a + 2) ^ (a + 1) := by
            rw [← h4]
            calc (w (a + 2) ^ 2) ^ (a + 2) ≤ w (a + 1) ^ (a + 2) * w (a + 3) ^ (a + 2) := by
                  rw [← h2]; exact h1
              _ ≤ w (a + 2) ^ (a + 1) * w (a + 3) ^ (a + 2) := h3
              _ = w (a + 3) ^ (a + 2) * w (a + 2) ^ (a + 1) := by ring
          have hpos : (0 : ℝ) < w (a + 2) ^ (a + 1) := pow_pos hBpos _
          exact le_of_mul_le_mul_right (by linarith [h5]) hpos
  -- the general version, by induction from `M = k`
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [h0, one_pow, pow_zero]
  · obtain ⟨M, rfl⟩ : ∃ M', M = k + M' := ⟨M - k, by omega⟩
    clear hk
    induction M with
    | zero => simp
    | succ M ih =>
      have hkM : 1 ≤ k + M := by omega
      have hstep : w (k + M) ^ (k + M + 1) ≤ w (k + M + 1) ^ (k + M) := by
        have h := step (k + M - 1)
        have e1 : k + M - 1 + 1 = k + M := by omega
        have e2 : k + M - 1 + 2 = k + M + 1 := by omega
        rw [e1, e2] at h
        exact h
      have h1 : (w k ^ (k + M)) ^ (k + M + 1) ≤ (w (k + M) ^ k) ^ (k + M + 1) :=
        pow_le_pow_left₀ (pow_nonneg (hnn _) _) ih _
      have h2 : (w (k + M) ^ k) ^ (k + M + 1) = (w (k + M) ^ (k + M + 1)) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h3 : (w (k + M) ^ (k + M + 1)) ^ k ≤ (w (k + M + 1) ^ (k + M)) ^ k :=
        pow_le_pow_left₀ (pow_nonneg (hnn _) _) hstep _
      have h4 : (w (k + M + 1) ^ (k + M)) ^ k = (w (k + M + 1) ^ k) ^ (k + M) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h5 : (w k ^ (k + M + 1)) ^ (k + M) = (w k ^ (k + M)) ^ (k + M + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h6 : (w k ^ (k + M + 1)) ^ (k + M) ≤ (w (k + M + 1) ^ k) ^ (k + M) := by
        rw [h5, ← h4]
        calc (w k ^ (k + M)) ^ (k + M + 1) ≤ (w (k + M) ^ k) ^ (k + M + 1) := h1
          _ = (w (k + M) ^ (k + M + 1)) ^ k := h2
          _ ≤ (w (k + M + 1) ^ (k + M)) ^ k := h3
      exact le_of_pow_le_pow_left₀ (by omega) (pow_nonneg (hnn _) _) h6

end LogConvex

/-! ### The pointwise bound `|(A^k)_{ii}| ≤ u_M(i)^{k/(2M)}` -/

section ColSqRpow

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `u_k^M ≤ u_M^k` for the column norms of the powers of a Hermitian matrix. -/
theorem colSq_pow_le_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (k M : ℕ) (hk : k ≤ M) (i : n) :
    colSq A k i ^ M ≤ colSq A M i ^ k :=
  pow_le_pow_of_logConvex (fun m => colSq_nonneg A m i) (colSq_zero A i)
    (fun m => colSq_sq_le hA m i) (fun _ h => colSq_eq_zero_succ h) k M hk

/-- The `rpow` form of an integer root: `x^M ≤ y^a` gives `x ≤ y^{a/M}`. -/
theorem le_rpow_div_of_pow_le_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {a M : ℕ} (hM : 0 < M)
    (h : x ^ M ≤ y ^ a) : x ≤ y ^ ((a : ℝ) / M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : x ^ ((M : ℕ) : ℝ) ≤ y ^ ((a : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]; exact h
  have h2 : (x ^ ((M : ℕ) : ℝ)) ^ ((M : ℝ))⁻¹ ≤ (y ^ ((a : ℕ) : ℝ)) ^ ((M : ℝ))⁻¹ :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx _) h1 (by positivity)
  rwa [← Real.rpow_mul hx, ← Real.rpow_mul hy, mul_inv_cancel₀ (ne_of_gt hMr), Real.rpow_one,
    ← div_eq_mul_inv] at h2

/-- `√u_k ≤ u_M^{k/(2M)}` for `k ≤ M`. -/
theorem sqrt_colSq_le_rpow {A : Matrix n n ℂ} (hA : A.IsHermitian) {k M : ℕ} (hM : 0 < M)
    (hk : k ≤ M) (i : n) :
    Real.sqrt (colSq A k i) ≤ (colSq A M i) ^ ((k : ℝ) / (2 * M)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : colSq A k i ≤ (colSq A M i) ^ ((k : ℝ) / M) :=
    le_rpow_div_of_pow_le_pow (colSq_nonneg _ _ _) (colSq_nonneg _ _ _) hM
      (colSq_pow_le_pow hA k M hk i)
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (colSq_nonneg _ _ _)]
  congr 1
  field_simp

/-- **The pointwise bound.**  Every diagonal entry of `A^k`, `k ≤ 2M`, is bounded by the
fractional power `u_M(i)^{k/(2M)}` of the single quantity `u_M(i) = (A^{2M})_{ii}`. -/
theorem norm_pow_apply_diag_le_rpow {A : Matrix n n ℂ} (hA : A.IsHermitian) {M : ℕ} (hM : 0 < M)
    {k : ℕ} (hk : k ≤ 2 * M) (i : n) :
    ‖(A ^ k) i i‖ ≤ (colSq A M i) ^ ((k : ℝ) / (2 * M)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  obtain ⟨a, b, hab, haM, hbM⟩ : ∃ a b : ℕ, a + b = k ∧ a ≤ M ∧ b ≤ M :=
    ⟨k / 2, k - k / 2, by omega, by omega, by omega⟩
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have h1 : ‖(A ^ k) i i‖ ≤ Real.sqrt (colSq A a i) * Real.sqrt (colSq A b i) := by
    rw [← hab]; exact norm_pow_apply_diag_le hA a b i
  have hsum : ((a : ℝ) / (2 * M)) + ((b : ℝ) / (2 * M)) = (k : ℝ) / (2 * M) := by
    rw [← add_div]
    congr 1
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hab
  have hne : ((a : ℝ) / (2 * M)) + ((b : ℝ) / (2 * M)) ≠ 0 := by
    rw [hsum]
    exact ne_of_gt (div_pos hkr (by linarith))
  have h4 : (colSq A M i) ^ ((k : ℝ) / (2 * M))
      = (colSq A M i) ^ ((a : ℝ) / (2 * M)) * (colSq A M i) ^ ((b : ℝ) / (2 * M)) := by
    rw [← hsum, Real.rpow_add' (colSq_nonneg _ _ _) hne]
  rw [h4]
  exact h1.trans (mul_le_mul (sqrt_colSq_le_rpow hA hM haM i) (sqrt_colSq_le_rpow hA hM hbM i)
    (Real.sqrt_nonneg _) (Real.rpow_nonneg (colSq_nonneg _ _ _) _))

/-- **The two-index bound that closes the recursion.**  For `k + l = 2M` the product of a
diagonal entry of `A^k` at `j` and one of `A^l` at `i` is bounded by a *convex combination* of
`u_M(j)` and `u_M(i)` — the degrees do not double. -/
theorem norm_mul_norm_pow_diag_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {M : ℕ} (hM : 0 < M)
    {k l : ℕ} (hkl : k + l = 2 * M) (i j : n) :
    ‖(A ^ k) j j‖ * ‖(A ^ l) i i‖
      ≤ ((k : ℝ) / (2 * M)) * colSq A M j + ((l : ℝ) / (2 * M)) * colSq A M i := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hw : ((k : ℝ) / (2 * M)) + ((l : ℝ) / (2 * M)) = 1 := by
    rw [← add_div]
    have hc : ((k : ℝ) + (l : ℝ)) = 2 * M := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hkl
    rw [hc]
    field_simp
  have h3 : (colSq A M j) ^ ((k : ℝ) / (2 * M)) * (colSq A M i) ^ ((l : ℝ) / (2 * M))
      ≤ ((k : ℝ) / (2 * M)) * colSq A M j + ((l : ℝ) / (2 * M)) * colSq A M i :=
    Real.geom_mean_le_arith_mean2_weighted (by positivity) (by positivity)
      (colSq_nonneg _ _ _) (colSq_nonneg _ _ _) hw
  exact le_trans (mul_le_mul (norm_pow_apply_diag_le_rpow hA hM (by omega) j)
    (norm_pow_apply_diag_le_rpow hA hM (by omega) i) (norm_nonneg _)
    (Real.rpow_nonneg (colSq_nonneg _ _ _) _)) h3

end ColSqRpow

/-! ### The induction on `p`

`u_M(i) = (X^{2M})_{ii}` has expectation at most `C_M = (2M-1)!!`, uniformly in `i` and `N`.
The base `M = 1` is `E[(X²)_{ii}] = ∑_j S_{ij} = 1`, i.e. the `p = 1` case of
`RBM.Gauss.traceMomentBound_one`. -/

section Induction

variable {d : Dims} {N : ℕ}

/-- The constants of the recursion: `C_0 = 1` and `C_{M+1} = (2M+1) C_M`, i.e. `C_M = (2M-1)!!`
(the crude bound for the Catalan number `Cat_M` of the paper's `E Tr(X^{2M}) ≈ Cat_M · N`). -/
def traceConst : ℕ → ℝ
  | 0 => 1
  | M + 1 => (2 * M + 1) * traceConst M

theorem traceConst_pos : ∀ M : ℕ, 0 < traceConst M
  | 0 => by norm_num [traceConst]
  | M + 1 => by
    have := traceConst_pos M
    have h2 : (0 : ℝ) < 2 * M + 1 := by positivity
    rw [traceConst]
    positivity

theorem integrable_colSq (d : Dims) (N : ℕ) (M : ℕ) (i : d.Idx N) :
    Integrable (fun ω : Ω d => colSq (Xmat d N ω) M i) (P d) := by
  have h1 : Integrable (fun ω : Ω d => (Xmat d N ω ^ (2 * M)) i i) (P d) :=
    (tame_Xmat_pow_apply d N (2 * M) i i).integrable (gaussIBP d)
  refine h1.re.congr (Filter.Eventually.of_forall fun ω => ?_)
  show RCLike.re ((Xmat d N ω ^ (2 * M)) i i) = colSq (Xmat d N ω) M i
  rw [pow_two_mul_apply_diag (Xmat_isHermitian d N ω)]
  simp

theorem integral_pow_two_mul_diag (d : Dims) (N : ℕ) (M : ℕ) (i : d.Idx N) :
    ∫ ω, (Xmat d N ω ^ (2 * M)) i i ∂(P d)
      = ((∫ ω, colSq (Xmat d N ω) M i ∂(P d) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    pow_two_mul_apply_diag (Xmat_isHermitian d N ω) M i)

theorem integral_colSq_nonneg (d : Dims) (N : ℕ) (M : ℕ) (i : d.Idx N) :
    0 ≤ ∫ ω, colSq (Xmat d N ω) M i ∂(P d) :=
  integral_nonneg fun _ => colSq_nonneg _ _ _

/-- **`E[(X²)_{ii}] = ∑_j S_{ij} = 1`** — the base of the induction, and the check that the
normalisation of the recursion is right. -/
theorem integral_colSq_one (d : Dims) (N : ℕ) (i : d.Idx N) :
    ∫ ω, colSq (Xmat d N ω) 1 i ∂(P d) = 1 := by
  have hrow : ∑ j, Sblk (d.L N) (d.W N) i j = 1 := RBM.sum_Sblk_row (d.three_le_L N) i
  have h1 : ((∫ ω, colSq (Xmat d N ω) 1 i ∂(P d) : ℝ) : ℂ)
      = ∫ ω, (Xmat d N ω ^ (1 + 1)) i i ∂(P d) := by
    rw [show (1 : ℕ) + 1 = 2 * 1 from rfl, integral_pow_two_mul_diag]
  rw [integral_Xmat_pow_succ_diag d N 1 i] at h1
  have h2 : ∀ ω : Ω d, (∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ (0 : ℕ)) j j)
      * (Xmat d N ω ^ (1 - 1 - 0)) i i = 1 := by
    intro ω
    norm_num [Matrix.one_apply_eq, ← Complex.ofReal_sum, hrow]
  simp only [Finset.range_one, Finset.sum_singleton, h2] at h1
  rw [integral_const] at h1
  simp only [probReal_univ, one_smul] at h1
  exact_mod_cast h1

/-- **The uniform bound on the diagonal moments**: `E[(X^{2M})_{ii}] ≤ C_M`, for every index
`i` and every `N`.  This is the heart of T109: the recursion of
`RBM.Gauss.integral_Xmat_pow_succ_diag` has `2M+1` terms, each of which is bounded by the
previous constant because `RBM.Gauss.norm_mul_norm_pow_diag_le` turns the pair of diagonal
entries of total degree `2M` into a convex combination of `u_M`'s. -/
theorem integral_colSq_le (d : Dims) (N : ℕ) : ∀ (M : ℕ) (i : d.Idx N),
    ∫ ω, colSq (Xmat d N ω) M i ∂(P d) ≤ traceConst M := by
  intro M
  induction M with
  | zero =>
    intro i
    simp only [colSq_zero]
    rw [integral_const]
    simp [traceConst, probReal_univ]
  | succ M ih =>
    intro i
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · rw [integral_colSq_one]
      norm_num [traceConst]
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hrow : ∑ j, Sblk (d.L N) (d.W N) i j = 1 := RBM.sum_Sblk_row (d.three_le_L N) i
    have hCpos : 0 < traceConst M := traceConst_pos M
    -- the recursion, at `m = 2M + 1`
    have hrec := integral_Xmat_pow_succ_diag d N (2 * M + 1) i
    rw [show 2 * M + 1 + 1 = 2 * (M + 1) by ring, integral_pow_two_mul_diag] at hrec
    simp only [Nat.add_sub_cancel] at hrec
    -- each of the `2M + 1` terms is bounded by `C_M`
    have hkey : ∀ k ∈ Finset.range (2 * M + 1),
        ‖∫ ω, (∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j)
            * (Xmat d N ω ^ (2 * M - k)) i i ∂(P d)‖ ≤ traceConst M := by
      intro k hk
      have hk' : k ≤ 2 * M := by
        have := Finset.mem_range.1 hk; omega
      have hkl : k + (2 * M - k) = 2 * M := by omega
      have hc1 : (0 : ℝ) ≤ (k : ℝ) / (2 * M) := by positivity
      have hc2 : (0 : ℝ) ≤ ((2 * M - k : ℕ) : ℝ) / (2 * M) := by positivity
      have hcsum : (k : ℝ) / (2 * M) + ((2 * M - k : ℕ) : ℝ) / (2 * M) = 1 := by
        rw [← add_div]
        have hc : ((k : ℝ) + ((2 * M - k : ℕ) : ℝ)) = 2 * M := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hkl
        rw [hc]
        field_simp
      -- the pointwise bound
      have hpt : ∀ ω : Ω d,
          ‖(∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j)
              * (Xmat d N ω ^ (2 * M - k)) i i‖
            ≤ ∑ j, Sblk (d.L N) (d.W N) i j
                * ((k : ℝ) / (2 * M) * colSq (Xmat d N ω) M j
                  + ((2 * M - k : ℕ) : ℝ) / (2 * M) * colSq (Xmat d N ω) M i) := by
        intro ω
        have h1 : ‖∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j‖
            ≤ ∑ j, Sblk (d.L N) (d.W N) i j * ‖(Xmat d N ω ^ k) j j‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Sblk_nonneg (L := d.L N) (W := d.W N) i j)]
        rw [norm_mul]
        calc ‖∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j‖
              * ‖(Xmat d N ω ^ (2 * M - k)) i i‖
            ≤ (∑ j, Sblk (d.L N) (d.W N) i j * ‖(Xmat d N ω ^ k) j j‖)
              * ‖(Xmat d N ω ^ (2 * M - k)) i i‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ∑ j, Sblk (d.L N) (d.W N) i j
              * (‖(Xmat d N ω ^ k) j j‖ * ‖(Xmat d N ω ^ (2 * M - k)) i i‖) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ _ := Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left
                (norm_mul_norm_pow_diag_le (Xmat_isHermitian d N ω) hM hkl i j)
                (Sblk_nonneg (L := d.L N) (W := d.W N) i j)
      have hint1 : Integrable (fun ω : Ω d =>
          (∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j)
            * (Xmat d N ω ^ (2 * M - k)) i i) (P d) :=
        ((Tame.sum _ fun j _ => (Tame.const (d := d) _).mul (tame_Xmat_pow_apply d N k j j)).mul
          (tame_Xmat_pow_apply d N (2 * M - k) i i)).integrable (gaussIBP d)
      have hIj : ∀ j : d.Idx N, Integrable (fun ω : Ω d => Sblk (d.L N) (d.W N) i j
          * ((k : ℝ) / (2 * M) * colSq (Xmat d N ω) M j
            + ((2 * M - k : ℕ) : ℝ) / (2 * M) * colSq (Xmat d N ω) M i)) (P d) := fun j =>
        Integrable.const_mul (((integrable_colSq d N M j).const_mul _).add
          ((integrable_colSq d N M i).const_mul _)) _
      have hint2 : Integrable (fun ω : Ω d => ∑ j, Sblk (d.L N) (d.W N) i j
          * ((k : ℝ) / (2 * M) * colSq (Xmat d N ω) M j
            + ((2 * M - k : ℕ) : ℝ) / (2 * M) * colSq (Xmat d N ω) M i)) (P d) :=
        integrable_finsetSum _ fun j _ => hIj j
      calc ‖∫ ω, (∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j)
              * (Xmat d N ω ^ (2 * M - k)) i i ∂(P d)‖
          ≤ ∫ ω, ‖(∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j)
              * (Xmat d N ω ^ (2 * M - k)) i i‖ ∂(P d) := norm_integral_le_integral_norm _
        _ ≤ ∫ ω, ∑ j, Sblk (d.L N) (d.W N) i j
              * ((k : ℝ) / (2 * M) * colSq (Xmat d N ω) M j
                + ((2 * M - k : ℕ) : ℝ) / (2 * M) * colSq (Xmat d N ω) M i) ∂(P d) :=
            integral_mono hint1.norm hint2 hpt
        _ = ∑ j, Sblk (d.L N) (d.W N) i j
              * ((k : ℝ) / (2 * M) * ∫ ω, colSq (Xmat d N ω) M j ∂(P d)
                + ((2 * M - k : ℕ) : ℝ) / (2 * M) * ∫ ω, colSq (Xmat d N ω) M i ∂(P d)) := by
            rw [integral_finsetSum _ fun j _ => hIj j]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_const_mul, integral_add ((integrable_colSq d N M j).const_mul _)
              ((integrable_colSq d N M i).const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ ∑ j, Sblk (d.L N) (d.W N) i j * traceConst M := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (Sblk_nonneg (L := d.L N) (W := d.W N) i j)
            have e1 : (k : ℝ) / (2 * M) * ∫ ω, colSq (Xmat d N ω) M j ∂(P d)
                ≤ (k : ℝ) / (2 * M) * traceConst M :=
              mul_le_mul_of_nonneg_left (ih j) hc1
            have e2 : ((2 * M - k : ℕ) : ℝ) / (2 * M) * ∫ ω, colSq (Xmat d N ω) M i ∂(P d)
                ≤ ((2 * M - k : ℕ) : ℝ) / (2 * M) * traceConst M :=
              mul_le_mul_of_nonneg_left (ih i) hc2
            nlinarith [e1, e2, hcsum]
        _ = traceConst M := by rw [← Finset.sum_mul, hrow, one_mul]
    -- add up the `2M + 1` terms
    have hbd : ‖((∫ ω, colSq (Xmat d N ω) (M + 1) i ∂(P d) : ℝ) : ℂ)‖
        ≤ (2 * M + 1 : ℕ) * traceConst M := by
      rw [hrec]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Finset.range (2 * M + 1),
            ‖∫ ω, (∑ j, (Sblk (d.L N) (d.W N) i j : ℂ) * (Xmat d N ω ^ k) j j)
              * (Xmat d N ω ^ (2 * M - k)) i i ∂(P d)‖
          ≤ ∑ _k ∈ Finset.range (2 * M + 1), traceConst M := Finset.sum_le_sum hkey
        _ = (2 * M + 1 : ℕ) * traceConst M := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_colSq_nonneg d N (M + 1) i)] at hbd
    rw [traceConst]
    push_cast at hbd ⊢
    linarith

end Induction

/-! ### `TraceMomentBound`, and `‖X‖ ≺ 1` unconditionally -/

section Conclusion

/-- **The trace-moment bound `E Tr(X^{2p}) ≤ C_p N`**, the hypothesis carried by
`RBM1D/Gauss/OpNorm.lean` since T100.  Summing `RBM.Gauss.integral_colSq_le` over the `W·L ≤ N`
indices gives it with `C_p = (2p-1)!!`. -/
theorem traceMomentBound_gauss (d : Dims) : TraceMomentBound d := by
  intro p
  refine ⟨traceConst p, traceConst_pos p, ?_⟩
  filter_upwards [d.dim] with N hN
  have hfrob : ∀ ω : Ω d, frobSq (Xmat d N ω ^ p) = ∑ j, colSq (Xmat d N ω) p j := by
    intro ω
    unfold frobSq colSq
    exact Finset.sum_comm
  simp only [hfrob]
  rw [integral_finsetSum _ fun j _ => integrable_colSq d N p j]
  calc ∑ _j : d.Idx N, ∫ ω, colSq (Xmat d N ω) p _j ∂(P d)
      ≤ ∑ _j : d.Idx N, traceConst p := Finset.sum_le_sum fun j _ => integral_colSq_le d N p j
    _ = (Fintype.card (d.Idx N) : ℝ) * traceConst p := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ traceConst p * (N : ℝ) := by
        have hcard : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) := by
          have h1 : Fintype.card (d.Idx N) = d.L N * d.W N := by simp [ZMod.card]
          have h2 : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact hN.1
          rw [h1]; exact_mod_cast h2
        nlinarith [traceConst_pos p, hcard]

open scoped Matrix.Norms.L2Operator in
/-- **`‖X‖ ≺ 1`, unconditionally.**  The field `norm_X` of `RBM.Gauss.OpNormBound`. -/
theorem stochDom_norm_Xmat_gauss (d : Dims) :
    RBM.StochDom (P d) (fun N (_ : Unit) ω => ‖Xmat d N ω‖) fun _ _ _ => (1 : ℝ) :=
  stochDom_norm_Xmat (traceMomentBound_gauss d)

/-- **`RBM.Gauss.OpNormBound` is a theorem.**  This closes `paper-deltas` #49: the operator-norm
bound of the Gaussian band matrix is no longer a hypothesis anywhere in the development. -/
theorem opNormBound_gauss (d : Dims) : OpNormBound d :=
  opNormBound_of_traceMomentBound (traceMomentBound_gauss d)

end Conclusion

end RBM.Gauss

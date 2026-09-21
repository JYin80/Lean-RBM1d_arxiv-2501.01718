/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEBridge
import RBM1D.Analysis.MomentClosing

/-!
# The moment Duhamel: the interface, the propagator's time derivative (T132a)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: **(5.20) and (5.24) in moment form**, as the replacement for the pathwise
Duhamel formula plus BDG that `RBM.SumZeroDyn.Hierarchy` carries in its fields `duhamel`,
`duhamelQ`, `bdg`, `bdgQ`.

The plan, and why it is not the same statement with the martingale erased, is recorded in
`docs/STATUS.md` under T132.  In one line: the martingale terms `mart`, `martQ` are
**unconstrained data fields**, so `duhamel` is satisfiable by fiat (T74,
`RBM1D/Gauss/DischargeBDG.lean`); the moment route has no martingale at all, and the drift is
pinned down by a **pointwise identity in `(u, M)`**, so the fiat handle disappears.

## Main definitions

* `RBM.MomentDuhamel.lkFun` — `(L - K)_{u,σ,a}` as a *deterministic* function of the time `u`
  and the matrix `M`, with no `ω` anywhere; `lkFun_H` identifies it with
  `RBM.SumZeroDyn.lkT` along a flow, by `rfl`.
* `RBM.MomentDuhamel.genLK` — `𝓛 = ½ ∑_{ij} S_ij ∂_ij ∂_ji` applied to `lkFun` in the matrix
  argument.  It uses only the variance profile `S`, so it makes sense over an arbitrary
  `RBM.Band` — no Gaussian structure and no `RBM.Gauss.MatrixStein`.
* `RBM.MomentDuhamel.eeFun` — the `E ⊗ E` of Definition 5.4 as a *deterministic* function of
  `(u, M)`; along a flow it is T127's `RBM.EEBridge.eeField`, by `rfl` (`eeFun_H`,
  `EEpath_eq_eeField`).  It is a definition, not an interface field.
* `RBM.MomentDuhamel.Hyp` — the primed interface: the two moment inequalities together with
  the pointwise drift identity that determines `F`.

## Main results

* `RBM.hasDerivAt_edgeKer`, `RBM.hasDerivAt_Uker_apply` — **`∂_u U_{u,v}` is elementary.**
  The running time `u` occurs in (5.17) only through `1 - (u ξ) S^{(B)}`
  (`RBM.edgeKer`), which is *affine* in `u`; so `u ↦ U_{u,v}` is a product of affine factors
  and its derivative needs no propagator ODE, no `RBM1D/Propagator/Deriv.lean`, and no
  hypothesis at all (not even `‖v ξ‖ < 1`).
* `RBM.MomentDuhamel.Hyp.Fpath`, `RBM.MomentDuhamel.EEpath` — the drift and `E ⊗ E` read along
  a flow, in **exactly** the types of `RBM.SumZeroDyn.Hierarchy.F` and `.EE`, so that
  `RBM.SumZeroDyn.Lemma510` applies to them **verbatim**, with no restatement.
* `RBM.MomentDuhamel.Hyp.F_unique`, `Hyp.F_unique_flow` — `F` is pinned down by `drift` at
  every Hermitian matrix, hence at every matrix of the flow, hence at every argument at which
  the interface's own inequalities evaluate it.

## The fiat audit of `Hyp` (T145)

After the two repairs above, the data fields of `Hyp` are `F` and `cMD`, and nothing else.

* `F` is pinned by `drift` at every Hermitian `M` and every `u ∈ [s_N, t_N]` (`F_unique`), and
  those are *exactly* the arguments at which `momentDuhamel` and `momentDuhamelQ` evaluate it:
  the matrix is always `X.H N u ω`, Hermitian by `RBM.Sample.hermitian` (`F_unique_flow`), and
  the time always lies in `[s_N, v] ⊆ [s_N, t_N]`.  There is no argument at which `F` is both
  free and used.
* `cMD` is the one remaining degree of freedom, and it is harmless in a way worth spelling
  out.  Enlarging it does weaken the two inequalities — but its type is `ℕ → ℝ`, so it may
  depend on `p` only and **not on `N`**, and an `N`-independent constant is precisely what `≺`
  absorbs for free.  Moreover the same `H.cMD p` reappears inside the hypothesis `hrhs` of the
  only consumer here, `stochDom_of_momentDuhamel`, so a larger `cMD` makes the *consumer's*
  obligation correspondingly harder: the pair is closed, not loosened.
* every other field (`drift`, `cMD_nonneg`, `integrable`, `momentDuhamel`, `momentDuhamelQ`)
  is a `Prop` about objects that are fixed before `Hyp` is written down — `lkFun`, `genLK`,
  `Uker`, `Qop`, `eeFun`, `RBM.SumZeroDyn.lkT` — plus the two data fields just discussed.

The one way to make `Hyp` vacuous is to hand it a degenerate window `t_N < s_N`; but then no
`v` satisfying `s_N ≤ v ≤ t_N` exists, so `stochDom_of_momentDuhamel` cannot be applied
either.  This is the same degeneracy every timed interface in the repository has.

## What this file does *not* do

The Gaussian discharge of `Hyp` (the generator identity with explicit time dependence, and the
joint `C²` regularity in `(z, M)`) is T132b and lives elsewhere; nothing here assumes
`RBM.Gauss.MatrixStein`.  Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory Filter Real

/-! ### `∂_u U_{u,v}`: the propagator's time derivative is elementary -/

section Propagator

variable (L : ℕ) [NeZero L]

/-- **`∂_s edgeKer L ξ s t = -ξ (S^{(B)} Θ(tξ))`**, with *no* hypotheses whatsoever — in
particular without `‖t ξ‖ < 1`.

The point is (5.17)'s shape: `edgeKer L ξ s t = (1 - (s ξ) • S^{(B)}) * Θ(t ξ)` has the
running time `s` only in the *affine* first factor. -/
theorem hasDerivAt_edgeKer (ξ t : ℂ) (x y : ZMod L) (s : ℝ) :
    HasDerivAt (fun r : ℝ => edgeKer L ξ (r : ℂ) t x y)
      (-(ξ * (SB L * Theta L (t * ξ)) x y)) s := by
  have h : ∀ r : ℝ, edgeKer L ξ (r : ℂ) t x y
      = (Theta L (t * ξ)) x y - (r : ℂ) * (ξ * (SB L * Theta L (t * ξ)) x y) := by
    intro r
    simp only [edgeKer, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul]
    ring
  simp only [h]
  have hc : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
  have h2 : HasDerivAt
      (fun r : ℝ => (Theta L (t * ξ)) x y - (r : ℂ) * (ξ * (SB L * Theta L (t * ξ)) x y))
      (0 - 1 * (ξ * (SB L * Theta L (t * ξ)) x y)) s :=
    (hasDerivAt_const s _).sub (hc.mul_const _)
  convert h2 using 1
  ring

/-- **`∂_u U_{u,v}`**, by the Leibniz rule over the `n` edges.  Again no hypotheses: the
whole `u`-dependence of (5.17) is polynomial of degree `n`. -/
theorem hasDerivAt_Uker_apply {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) (A : LoopArg L n → ℂ)
    (a : LoopArg L n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Uker L ξ (r : ℂ) t A a)
      (∑ b : LoopArg L n,
        (∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (s : ℂ) t (a j) (b j))
            * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) * A b) s := by
  simp only [Uker]
  refine HasDerivAt.fun_sum (A' := fun b : LoopArg L n =>
    (∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (s : ℂ) t (a j) (b j))
      * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) * A b) fun b _ => ?_
  have h := (HasDerivAt.fun_finsetProd
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      hasDerivAt_edgeKer L (ξ i) t (a i) (b i) s)).mul_const (A b)
  simpa only [smul_eq_mul] using h

end Propagator

/-! ### `(L - K)` as a deterministic function of `(u, M)` -/

namespace MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`(L - K)_{u,σ,a}` as a function of the time and the matrix**, with no `ω`.

This is the object the pointwise drift identity of (5.15) is about; `RBM.SumZeroDyn.lkT` is
its value along a flow (`lkFun_H`, a `rfl`). -/
noncomputable def lkFun (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) : ℂ :=
  gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (σ, a))
    - B.Kval E N u (LoopData.idx (σ, a))

/-- **The deterministic function evaluated along a flow is `RBM.SumZeroDyn.lkT`** — by `rfl`,
which is what makes the primed interface plug into the existing `Hierarchy/` vocabulary
without any adapter. -/
theorem lkFun_H (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) :
    lkFun B E N u (X.H N u ω) σ a = SumZeroDyn.lkT X E N u ω σ a := rfl

/-- **`(E ⊗ E)_{u,σ,c}` of Definition 5.4 as a function of the time and the matrix**, with no
`ω`, i.e. `RBM.EEBridge.eeArg` at the spectral parameter `z_u`.

This is *not* a datum of the interface below: `E ⊗ E` is a completely explicit tensor built
from the resolvent of `M` at `z_u` (T127), so the moment inequalities of `Hyp` quantify over
nothing here.  Making it a data field — as `RBM.SumZeroDyn.Hierarchy.EE` is — would let an
instance take it enormous and render `momentDuhamel` vacuous, which is exactly the fiat
failure mode `Hyp` exists to close; see `docs/STATUS.md` under T145. -/
noncomputable def eeFun (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (c : LoopArg (B.L N) (m + m)) : ℂ :=
  EEBridge.eeArg B.toDims N (zt E u) M σ c

/-- **`eeFun` along a flow is T127's `RBM.EEBridge.eeField`** — by `rfl`.  Together with
`EEpath_eq_eeField` this is what makes T135's `RBM.EEBridge.stochDom_norm_eeField` a statement
*about the `E ⊗ E` of this interface*, rather than about a candidate that an instance is free
to ignore. -/
theorem eeFun_H (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    eeFun B E N u (X.H N u ω) σ c = EEBridge.eeField X E n N u ω σ c := rfl

/-- **`𝓛 Φ = ½ ∑_{ij} S_ij ∂_ij ∂_ji Φ`** applied to the matrix argument of `lkFun`.

**The weight is `RBM.Sblk`, and nothing else.**  `Sblk L W i j = sbKre L (i.1 - j.1) / W`
*already is* the variance profile `S = S^{(B)} ⊗ S_W` of Section 2.1, i.e. the `E|X_ij|²` of
the model (`RBM.Gauss.gvar_diag`, `RBM.Gauss.gvar_offDiag`), and it is exactly the weight
carried by the Gaussian generator identity `RBM.Gauss.hasDerivAt_integral_Phi_pairs`, by
`RBM.Gauss.genD` and by `RBM.Gauss.sumSblk_half_wirtPair`.  Dividing it by `W` once more — as
an earlier version of this definition did, reading `Sblk` as the *un-normalized* `S^{(B)}` —
produces `W⁻¹ 𝓛`, not `𝓛`; see `RBM.Gauss.genLK_eq`.

Only the variance profile enters, so this is defined over an arbitrary `RBM.Band`; the
Gaussian model is needed to *prove* the drift identity, not to state it.
The `RBM.Gauss.wirtSecond` on the right is transported along `RBM.Band.toDims`, whose index
types agree with `B.Idx` definitionally (`RBM.Band.toDims_Idx`).

**The direction of the second derivative.**  `∂_ij ∂_ji` is the second derivative along the
*Hermitian* direction that perturbs the entry `(i, j)` and, simultaneously, its conjugate at
`(j, i)`: this is the generator of the matrix flow (2.34), whose paths are Hermitian
(`RBM.Sample.hermitian`).  Accordingly the field `Hyp.drift` below is asserted only at
Hermitian `M`, which is where `M - z_u` is invertible and where the flow lives. -/
noncomputable def genLK (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ i : B.Idx N, ∑ j : B.Idx N,
    ((Sblk (B.L N) (B.W N) i j : ℝ) : ℂ)
      * Gauss.wirtSecond B.toDims N (fun M' => lkFun B E N u M' σ a) M i j

/-! ### The primed interface -/

/-- `‖Y‖_q = (E |Y|^q)^{1/q}`, the only norm this file uses. -/
noncomputable def momNorm (P : Measure Ω) (q : ℕ) (Y : Ω → ℝ) : ℝ :=
  (∫ ω, |Y ω| ^ q ∂P) ^ ((1 : ℝ) / q)

theorem momNorm_nonneg (P : Measure Ω) (q : ℕ) (Y : Ω → ℝ) : 0 ≤ momNorm P q Y :=
  Real.rpow_nonneg (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) _

/-- **The primed interface at loop length `n + 2`.**

Compare `RBM.SumZeroDyn.Hierarchy`.  The differences, in order of importance:

* there are **no** data fields `mart`, `martQ`.  T74's obstruction 1 — "defining `mart` as
  the residual makes `duhamel` true by construction for *any* `F`" — has no analogue here,
  because there is no residual to define;
* **`EE` is not a field at all.**  `RBM.MomentDuhamel.eeFun` *is* the `E ⊗ E` of Definition
  5.4, and it is what appears on the right of the two inequalities.  (T132a still had `EE` as
  an unconstrained datum, which reopened the fiat hole one field over: an instance could take
  it enormous and the inequality became vacuous.  T145.)  `EEpath` is `RBM.EEBridge.eeField`
  by `rfl`, so T135's `RBM.EEBridge.stochDom_norm_eeField` is a statement about it;
* `F` is a function of the **time and the matrix**, not of `ω`.  Its value along a flow,
  `Fpath`, has exactly the type of `Hierarchy.F`, so `RBM.SumZeroDyn.Lemma510` applies to it
  verbatim; likewise `EEpath` for `Hierarchy.EE`;
* the field `drift` is the **pointwise** identity (5.15),
  `(∂_u + 𝓛)(L - K) = Θ_{u,σ} ∘ (L - K) + F`, at every `(u, M)` with `M` **Hermitian**.
  Since the `u`-derivative of a function is unique where it exists, this **determines `F`
  uniquely there** (`F_unique`), and the flow is Hermitian (`RBM.Sample.hermitian`), so `F`
  is pinned down at every value it is ever evaluated at (`F_unique_flow`).  Hermiticity is
  not a weakening one could exploit: at non-Hermitian `M` the resolvent `(M - z_u)⁻¹` need
  not exist (Lean's inverse is then `0`) and the identity may simply be false.  This is the
  field T74's three obstructions have no purchase on, and it is the reason `Lemma510` stops
  being the only guard;
* the four Prop fields `duhamel`, `duhamelQ`, `bdg`, `bdgQ` are replaced by the two moment
  inequalities `momentDuhamel`, `momentDuhamelQ` — (5.20) + (5.24) and (5.91) + (5.103),
  each combined into one statement.

The constant `cMD p` is the `c = C_p / p` of the closing lemma
(`RBM.sqrt_le_of_integral_le`); `p` enters the conclusion only through it. -/
structure Hyp (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) where
  /-- The drift of (5.15) other than the `l_K = 2` term, as a function of `(u, M)`. -/
  F : ∀ N, ℝ → Matrix (B.Idx N) (B.Idx N) ℂ → (Fin (n + 2) → Bool) →
    LoopArg (B.L N) (n + 2) → ℂ
  /-- **The pointwise drift identity (5.15)**, which pins `F` down.  Asserted only at Hermitian
  `M`: that is where the resolvent exists and where the flow (2.34) lives, and it is still
  enough to determine `F` at every argument the interface evaluates it at (`F_unique_flow`). -/
  drift : ∀ N (u : ℝ), s N ≤ u → u ≤ t N →
    ∀ (M : Matrix (B.Idx N) (B.Idx N) ℂ), M.IsHermitian →
      ∀ (σ : Fin (n + 2) → Bool) a,
        ∃ dv : ℂ, HasDerivAt (fun v : ℝ => lkFun B E N v M σ a) dv u ∧
          dv + genLK B E N u M σ a
            = SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (lkFun B E N u M σ) a
              + F N u M σ a
  /-- The `p`-dependent constant of the closing step. -/
  cMD : ℕ → ℝ
  cMD_nonneg : ∀ p, 0 ≤ cMD p
  /-- Every quantity whose `2p`-th moment is taken below is integrable.  On the Gaussian
  model this is free from the deterministic envelope `‖G‖ ≤ η⁻¹` of T77
  (`RBM.Gauss.integrable_lkT_pow`).

  **Restricted to the window `[s_N, t_N]`**, exactly as `drift` is, and for the same reason:
  the envelope is a power of `(Im z_u)⁻¹ = ((1 - u) Im m_E)⁻¹`, so at `u = 1` the spectral
  parameter is real and no deterministic envelope exists at all.  Quantifying `u` over the
  whole of `ℝ` — as T132a did — made the field unsatisfiable on the Gaussian model.  Nothing
  is lost: every use below is at a time in `[s_N, v] ⊆ [s_N, t_N]`. -/
  integrable : ∀ (q N : ℕ) (u : ℝ), s N ≤ u → u ≤ t N → ∀ (σ : Fin (n + 2) → Bool) a,
    Integrable (fun ω => |‖SumZeroDyn.lkT X E N u ω σ a‖| ^ q) B.P
  /-- **(5.20) + (5.24) combined, in moment form.** -/
  momentDuhamel : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ),
    s N ≤ v → v ≤ t N → ∀ a : LoopArg (B.L N) (n + 2),
      momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
        ≤ momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N (s N) ω σ) a‖)
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (F N u (X.H N u ω) σ) a‖))
          + (cMD p * ∫ u in (s N)..v, momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (eeFun B E N u (X.H N u ω) σ) (Fin.append a a)‖)) ^ ((1 : ℝ) / 2)
  /-- **(5.91) + (5.103) combined, in moment form** (the `Q_t` route: five terms). -/
  momentDuhamelQ : ∀ (p : ℕ), 1 ≤ p → ∀ N (σ : Fin (n + 2) → Bool) (v : ℝ),
    s N ≤ v → v ≤ t N → ∀ a : LoopArg (B.L N) (n + 2),
      momNorm B.P (2 * p)
          (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
        ≤ momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω σ)) a‖)
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (Qop (B.L N) ((u : ℝ) : ℂ) (F N u (X.H N u ω) σ)) a‖))
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
                  (SumZeroDyn.lkT X E N u ω σ)) a‖))
          + 2 * (∫ u in (s N)..v, momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω σ) (b 0)
                  * SumZeroDyn.varthetaDot (B.L N) u b) a‖))
          + (cMD p * ∫ u in (s N)..v, momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) σ))
                (Fin.append a a)‖)) ^ ((1 : ℝ) / 2)

namespace Hyp

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The drift read along the flow**, in exactly the type of `RBM.SumZeroDyn.Hierarchy.F`. -/
noncomputable def Fpath (H : Hyp X E s t n) :
    ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) (n + 2) → ℂ :=
  fun N u ω σ a => H.F N u (X.H N u ω) σ a

/-- **`F` is determined by `drift`**: two drifts satisfying the pointwise identity at the same
Hermitian `(u, M, σ, a)` agree there.  This is the precise sense in which the primed interface
closes T74's obstruction 1 — there is no freedom left in `F` to absorb anything. -/
theorem F_unique (H H' : Hyp X E s t n) {N : ℕ} {u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) : H.F N u M σ a = H'.F N u M σ a := by
  obtain ⟨dv, hdv, heq⟩ := H.drift N u hsu hut M hM σ a
  obtain ⟨dv', hdv', heq'⟩ := H'.drift N u hsu hut M hM σ a
  have hdd : dv = dv' := hdv.unique hdv'
  have h2 : SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (lkFun B E N u M σ) a
        + H.F N u M σ a
      = SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (lkFun B E N u M σ) a
        + H'.F N u M σ a := by
    rw [← heq, ← heq', hdd]
  exact add_left_cancel h2

/-- **The Hermitian restriction of `drift` costs nothing**: the flow (2.34) is Hermitian
(`RBM.Sample.hermitian`), so `F` is still determined at *every* argument at which the two
moment inequalities evaluate it.  Restricting `drift` to Hermitian `M` therefore does not
reopen T74's obstruction 1 — it only drops the assertion at matrices where the resolvent
need not exist. -/
theorem F_unique_flow (H H' : Hyp X E s t n) {N : ℕ} {u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    (ω : Ω) (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2)) :
    H.Fpath N u ω σ a = H'.Fpath N u ω σ a :=
  F_unique H H' hsu hut (X.hermitian N u ω) σ a

end Hyp

/-- **`E ⊗ E` read along the flow**, in exactly the type of
`RBM.SumZeroDyn.Hierarchy.EE`.  It is a *definition*, not a field of `Hyp`. -/
noncomputable def EEpath (X : Sample B) (E : ℝ) (n : ℕ) :
    ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) ((n + 2) + (n + 2)) → ℂ :=
  fun N u ω σ c => eeFun B E N u (X.H N u ω) σ c

/-- **`EEpath` is T127's `RBM.EEBridge.eeField`**, by `rfl`.  Consequently T135's
`RBM.EEBridge.stochDom_norm_eeField` is *literally* the `EE_le` control for the `E ⊗ E` that
`momentDuhamel` uses: no field has to be chosen, and none can be chosen badly. -/
theorem EEpath_eq_eeField (X : Sample B) (E : ℝ) (n : ℕ) :
    EEpath X E n = EEBridge.eeField X E n := rfl

/-! ### From `‖·‖_{2p}` bounds to `≺` -/

/-- `(∫ |Y|^{2p})` recovered from `momNorm`: `momNorm P (2p) Y ^ (2p) = ∫ |Y|^{2p}`. -/
theorem momNorm_pow (P : Measure Ω) {q : ℕ} (hq : q ≠ 0) (Y : Ω → ℝ) :
    momNorm P q Y ^ q = ∫ ω, |Y ω| ^ q ∂P := by
  have h0 : (0 : ℝ) ≤ ∫ ω, |Y ω| ^ q ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have hne : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [momNorm, ← Real.rpow_natCast ((∫ ω, |Y ω| ^ q ∂P) ^ ((1 : ℝ) / q)) q,
    ← Real.rpow_mul h0, one_div, inv_mul_cancel₀ hne, Real.rpow_one]

/-- **The bridge from moment norms to `RBM.Gauss.MomentDom`.**

A bound `‖Y‖_{2p} ≤ C · N^{ε/2} · Φ` for every `ε > 0` and every `p ≥ 1`, eventually in `N`
and uniformly in the index, is exactly `MomentDom`: raise both sides to the `2p`.

This is the piece that turns the primed interface's conclusion into the `≺` that every
consumer of `RBM.SumZeroDyn.Hierarchy.bdg` ultimately wants — after it, T73's
`RBM.Gauss.stochDom_of_momentDom` finishes the job. -/
theorem momentDom_of_momNorm_le [IsProbabilityMeasure (B.P)] {U : ℕ → Type*}
    {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ} (hΦ0 : ∀ N q, 0 ≤ Φ N q)
    (h : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ q : U N,
      momNorm B.P (2 * p) (Y N q) ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N q)) :
    Gauss.MomentDom B.P Y Φ := by
  intro ε hε p
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨1, one_pos, Eventually.of_forall fun N q => ?_⟩
    simp
  obtain ⟨C, hC0, hN⟩ := h ε hε p hp
  refine ⟨C ^ (2 * p), by positivity, ?_⟩
  filter_upwards [hN, eventually_gt_atTop 0] with N hNq hN0 q
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hbase : 0 ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N q) := by
    have := hΦ0 N q; have : (0:ℝ) ≤ (N:ℝ) ^ (ε/2) := Real.rpow_nonneg hNr.le _
    positivity
  have hpow := pow_le_pow_left₀ (momNorm_nonneg B.P (2 * p) (Y N q)) (hNq q) (2 * p)
  rw [momNorm_pow B.P (by omega : 2 * p ≠ 0)] at hpow
  refine hpow.trans (le_of_eq ?_)
  have he : (ε / 2) * ((2 * p : ℕ) : ℝ) = ε * (p : ℝ) := by push_cast; ring
  rw [mul_pow, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)) (2 * p),
    ← Real.rpow_mul hNr.le, he]

/-- **The primed consumer, in the shape `RBM.SumZeroDyn.term1M` / `termM` are used in.**

Given the primed interface and a `‖·‖_{2p}` bound on each of the three (resp. five) terms on
the right of `momentDuhamel`, the loop difference itself is `≺ Φ`.  The hypothesis `hrhs` is
what the kernel estimates of `RBM1D/Hierarchy/SumZeroDyn.lean` together with
`RBM.SumZeroDyn.Lemma510` have to supply; **this file does not supply it** (see the module
docstring), it only shows that nothing else is needed.

Note what is *absent* from the hypotheses: no martingale, no `bdg`, no quadratic-variation
field — only the moment bound and `Lemma510`'s controls, fed through `Hyp`.

**The time is fixed.**  `RBM.Gauss.stochDom_of_momentDom` requires a `Fintype` index, and
`RBM.TimeIcc s t N` is a subtype of `ℝ`; so the moment route gives `≺` *at each time* and the
passage to a bound uniform in `u ∈ [s, t]` must go through the net engine of T124
(`stochDom_timeIcc_of_unifDom`) exactly as for every other producer in the repository.  This
is not a defect of the moment route — `RBM.SumZeroDyn.Hierarchy.bdg` gets its time uniformity
by *assuming* it. -/
theorem stochDom_of_momentDuhamel [IsProbabilityMeasure (B.P)]
    {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} (H : Hyp X E s t n)
    (v : ℕ → ℝ) (hv1 : ∀ N, s N ≤ v N) (hv2 : ∀ N, v N ≤ t N)
    {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {Φ : ∀ N, LoopData (B.L N) (n + 2) → ℝ} (hΦ : ∀ N q, 0 < Φ N q)
    (hrhs : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖)
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (H.F N u (X.H N u ω) q.1) q.2‖))
          + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N q)) :
    StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
      (fun N q _ => Φ N q) := by
  refine Gauss.stochDom_of_momentDom hcard hΦ (fun p N q => ?_) ?_
  · exact H.integrable (2 * p) N (v N) (hv1 N) (hv2 N) q.1 q.2
  refine momentDom_of_momNorm_le (fun N q => (hΦ N q).le) fun ε hε p hp => ?_
  obtain ⟨C, hC0, hN⟩ := hrhs ε hε p hp
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hN] with N hNq q
  exact (H.momentDuhamel p hp N q.1 (v N) (hv1 N) (hv2 N) q.2).trans (hNq q)

end MomentDuhamel

end RBM

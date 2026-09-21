/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6DriftEG
import RBM1D.Gauss.Step6Hyp
import RBM1D.Gauss.SteinMatrix
import RBM1D.Gauss.LoopIto
import RBM1D.Flow.Initial
import RBM1D.Flow.Iteration

/-!
# T205: the sample side of Step 6, and why (2.71) cannot yet be propagated

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8 ((5.126)–(5.136)) and §2.7 ((2.71), (2.80)).

T204 produced `RBM.Thm221NoEL`, the variant of Theorem 2.21 with (2.71) deleted from both the
hypothesis and the conclusion (the remark on p. 25).  The second pass — propagating (2.71)
itself, which is what feeds (2.62) and hence the expectation bounds (2.8), (2.9) of
Theorem 2.4 and Theorem 2.5 — has to go through Step 6, i.e. through
`RBM.sharpExpect_step6_driftEG` (T189).  This file audits the hypotheses of that theorem for
the Gaussian model `RBM.Gauss.sample`.

## The blocking result (§2 below)

Three families of hypotheses of `RBM.sharpExpect_step6_driftEG` quantify the *time* `v` over
**all of `ℝ`** rather than over the window `[s_N, t_N]`:

* `henvQ`, `henvG`, `henvLK` — the deterministic polynomial envelope;
* `hmeasQ`, `hmeasG`, `hmeasLK` — the measurability in `ω`;
* `hintL1` — the integrability of the `1`-loop.

For the envelope this is not a cosmetic over-quantification: **no such envelope exists.**
`RBM.Gauss.not_exists_env_eG` is a compiled refutation, at the energy `E = 0` and the sample
point `ω = 0` (where `H_v = 0` for every `v`, since `H_v = √v · X`), of the `henvG` family.
As `v ↑ 1` the spectral parameter `z_v = (1-v) i` tends to `0`, so the resolvent of `H_v = 0`
is `(1-v)⁻¹ i` and the integrand of (5.131) is the *real* number
`2 (w⁻¹ - 1) w⁻³ / W` with `w = 1 - v`, which is unbounded.  There is no cancellation to
rescue it: the whole `a`, `b` sum collapses through `∑_a S^{(B)}_{a a₀} = 1`
(`RBM.SumZeroDyn.sum_SB_col`) and both `k = 1, 2` terms are equal.

Consequently `RBM.sharpExpect_step6_driftEG` cannot be applied at `E = 0` in the Gaussian
model, and since Theorems 2.4/2.5 quantify over all `|E| ≤ 2 - κ`, the whole (2.71) induction
is blocked until the quantifier is restricted.  The fix is a *one-line* change in
`RBM1D/Gauss/Step6DriftSplit.lean` and `RBM1D/Gauss/Step6DriftEG.lean` — replace
`∀ (v : ℝ)` by `∀ (v : RBM.TimeIcc s t N)` in `henvQ`/`henvG`/`henvLK`/`hmeasQ`/`hmeasG`/
`hmeasLK`/`hintL1` — because the proofs use those hypotheses only at window times
(`RBM.unifDetDom_driftELK` destructs `p.1 : TimeIcc s t N` before using `henv`, and
`RBM.fastDecayHyp_driftSplit` uses them under `vv : TimeIcc s t N`).  Those two files are held
by other tickets, so the patch is handed to the coordinator rather than applied here.

## What *is* discharged here (§3)

* `RBM.Gauss.hEL_gauss` — the `hEL` slot: `∂_v E L_{v,σ,a}` is the integrated generator.  This
  is `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` (T140) fed with
  `RBM.Gauss.differentiableAt_integral_gloop_flow` (T141) and `RBM.Gauss.matrixStein` (T70);
  the ball radius is `ε = (1-v)/2` and the floor is `η = ε · Im m^{(E)}`.  No new hypothesis.
* `RBM.Gauss.hintL2_gauss` — the `hintL2` slot, `RBM.Gauss.integrable_sample_Lval` (T76).

Both of these slots are quantified over `0 < v < 1` in `RBM.sharpExpect_step6_driftEG`, so they
are *not* affected by the defect above.

## The assembly (§4)

`RBM.bounds_of_boundsCore_of_sharpExpect` is the (2.71) half of the induction step: given
(2.68)–(2.70) at `t` (which is what `RBM.Thm221NoEL` delivers) and (2.80) on `[s,t]`, it
returns the full `RBM.Bounds` at `t`.  It carries no unsatisfiable hypothesis: the Step 6
conclusion is a *hypothesis*, not a fiat.  `RBM.Gauss.bounds_witness_zero` shows the lemma is
applicable (at the degenerate window `s = t = 0`, where `RBM.Bounds_zero` is recovered through
it).  **A witness at `s > 0` still does not exist** — that is exactly what the blocked Step 6
would have produced.
-/

open MeasureTheory Filter Matrix

namespace RBM.Gauss

open RBM Finset

/-! ### §1  The sample point `ω = 0` and the loops there

`H_v(0) = √v · X(0) = 0` for every `v`, so the resolvent is the scalar `(-z_v)⁻¹` and every
loop can be evaluated in closed form with the tools of `RBM1D/Flow/Initial.lean`. -/

section ZeroPoint

variable (d : Dims) (N : ℕ)

/-- The band matrix vanishes at the origin of the Gaussian sample space. -/
theorem Xmat_zero : Xmat d N (0 : Ω d) = 0 := by
  ext i j
  simp [Xmat, Xentry]

/-- `H_v(0) = 0` for **every** time `v` — the moment-route flow is `H_v = √v · X`. -/
theorem Hflow_at_zero (v : ℝ) : Hflow d N v (0 : Ω d) = 0 := by
  simp [Hflow, Xmat_zero]

/-- `m^{(0)} = i`. -/
theorem mE_zero : mE 0 = Complex.I := by
  rw [mE]
  norm_num
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  push_cast
  ring

/-- `z_v^{(0)} = (1 - v) i`: at the energy `E = 0` the spectral parameter tends to `0` as
`v ↑ 1`, which is what makes the resolvent of `H = 0` blow up. -/
theorem zt_zero_energy (v : ℝ) : zt 0 v = ((1 - v : ℝ) : ℂ) * Complex.I := by
  rw [zt, mE_zero]
  push_cast
  ring

end ZeroPoint

section ZeroLoops

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The scalar value of `G(σ)` at `H = 0`: `(-z_σ)⁻¹`. -/
noncomputable def gZero (z : ℂ) (s : Bool) : ℂ :=
  (-(if s then z else (starRingEnd ℂ) z))⁻¹

omit [NeZero W] in
theorem Gsig_zero_eq_smul {z : ℂ} (hz : z ≠ 0) (s : Bool) :
    Gsig (0 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) z s = gZero z s • 1 := by
  cases s
  · rw [Gsig_false, gZero]
    simpa using green_zero (n := ZMod L × Fin W) (z := (starRingEnd ℂ) z) (by simpa using hz)
  · rw [Gsig_true, gZero]
    simpa using green_zero (n := ZMod L × Fin W) (z := z) hz

/-- The `1`-loop at `H = 0` is the scalar itself (`Tr E_a = 1`). -/
theorem gloop_zero_one {z : ℂ} (hz : z ≠ 0) (s : Bool) (x : ZMod L) :
    gloop L W 0 z ⟨[s], [x]⟩ = gZero z s := by
  rw [gloop, gloopProd_of_Gsig_eq_smul (fun s => Gsig_zero_eq_smul (L := L) (W := W) hz s) rfl]
  simp [trace_Eblk]

/-- The `3`-loop with equal charges at `H = 0`: nonzero only when all three block labels
agree, and then equal to `(-z_σ)^{-3} W^{-2}`. -/
theorem gloop_zero_three_const {z : ℂ} (hz : z ≠ 0) (s : Bool) (x y w : ZMod L) :
    gloop L W 0 z ⟨[s, s, s], [x, y, w]⟩
      = (if y = x ∧ w = x then gZero z s ^ 3 * ((W : ℂ)⁻¹) ^ 2 else 0) := by
  rw [gloop, gloopProd_of_Gsig_eq_smul (fun s => Gsig_zero_eq_smul (L := L) (W := W) hz s) rfl,
    prod_map_Eblk_cons]
  by_cases h : y = x ∧ w = x
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [ite_eq_left (by simp)]
    simp [trace_Eblk]
    left; ring
  · rw [ite_eq_right (by simpa using fun h1 h2 => h ⟨h1, h2⟩), ite_eq_right h]
    simp

end ZeroLoops

/-! ### §2  `henvG` has no producer: the refutation

The loop `I = ((+,+), (a₀,a₀))` is the one used below; `RBM.LoopIdx.cutGlue` at `k = 1, 2`
turns it into the two `3`-loops that the second slot of `RBM.Decay.eG` reads. -/

section EGShape

theorem loopData_const_idx (d : Dims) (N : ℕ) (a₀ : ZMod ((band d).L N)) :
    (LoopData.idx ((fun _ => true : Fin 2 → Bool),
      (fun _ => a₀ : LoopArg ((band d).L N) 2))) = ⟨[true, true], [a₀, a₀]⟩ := rfl

theorem cutGlue_one_const (d : Dims) (N : ℕ) (a₀ b : ZMod ((band d).L N)) :
    (LoopIdx.cutGlue 1 b (⟨[true, true], [a₀, a₀]⟩ : LoopIdx (ZMod ((band d).L N))))
      = ⟨[true, true, true], [b, a₀, a₀]⟩ := rfl

theorem cutGlue_two_const (d : Dims) (N : ℕ) (a₀ b : ZMod ((band d).L N)) :
    (LoopIdx.cutGlue 2 b (⟨[true, true], [a₀, a₀]⟩ : LoopIdx (ZMod ((band d).L N))))
      = ⟨[true, true, true], [a₀, b, a₀]⟩ := rfl

/-- `(L - K)` at a `1`-loop, at `ω = 0` and energy `0`: `K` at length `1` is `m(σ)`
(`RBM.Kgen_one`), so this is `(-z_v)⁻¹ - i`. -/
theorem lkPath_zero_one (d : Dims) (N : ℕ) {v : ℝ} (hz : zt 0 v ≠ 0)
    (a : ZMod ((band d).L N)) :
    lkPath (sample d) 0 N v (0 : Ω d) ⟨[true], [a]⟩ = gZero (zt 0 v) true - Complex.I := by
  show gloop ((band d).L N) ((band d).W N) ((sample d).H N v (0 : Ω d)) (zt 0 v) _
      - (band d).Kval 0 N v _ = _
  rw [show ((sample d).H N v (0 : Ω d)) = 0 from Hflow_at_zero d N v,
    gloop_zero_one (L := (band d).L N) (W := (band d).W N) hz, Band.Kval, Kgen_one]
  simp [mSigma, mE_zero]

theorem gloop_zero_cutGlue_one (d : Dims) (N : ℕ) {v : ℝ} (hz : zt 0 v ≠ 0)
    (a₀ b : ZMod ((band d).L N)) :
    gloop ((band d).L N) ((band d).W N) ((sample d).H N v (0 : Ω d)) (zt 0 v)
        ⟨[true, true, true], [b, a₀, a₀]⟩
      = (if b = a₀ then gZero (zt 0 v) true ^ 3 * ((((band d).W N : ℂ))⁻¹) ^ 2 else 0) := by
  rw [show ((sample d).H N v (0 : Ω d)) = 0 from Hflow_at_zero d N v,
    gloop_zero_three_const (L := (band d).L N) (W := (band d).W N) hz]
  by_cases h : b = a₀
  · subst h; simp only [and_self]
  · have h' : ¬ ((a₀ : ZMod ((band d).L N)) = b ∧ (a₀ : ZMod ((band d).L N)) = b) :=
      fun hh => h (Eq.symm hh.1)
    rw [ite_eq_right h', ite_eq_right h]

theorem gloop_zero_cutGlue_two (d : Dims) (N : ℕ) {v : ℝ} (hz : zt 0 v ≠ 0)
    (a₀ b : ZMod ((band d).L N)) :
    gloop ((band d).L N) ((band d).W N) ((sample d).H N v (0 : Ω d)) (zt 0 v)
        ⟨[true, true, true], [a₀, b, a₀]⟩
      = (if b = a₀ then gZero (zt 0 v) true ^ 3 * ((((band d).W N : ℂ))⁻¹) ^ 2 else 0) := by
  rw [show ((sample d).H N v (0 : Ω d)) = 0 from Hflow_at_zero d N v,
    gloop_zero_three_const (L := (band d).L N) (W := (band d).W N) hz]
  by_cases h : b = a₀
  · subst h; simp only [and_self]
  · have h' : ¬ ((b : ZMod ((band d).L N)) = a₀ ∧ (a₀ : ZMod ((band d).L N)) = a₀) :=
      fun hh => h hh.1
    rw [ite_eq_right h', ite_eq_right h]

/-- **The integrand of (5.131) at `ω = 0`, in closed form.**  The double sum over the block
labels collapses: only `b = a₀` survives in the second slot, and `∑_a S^{(B)}_{a a₀} = 1`
kills the first.  The two terms `k = 1, 2` are equal, whence the factor `2`. -/
theorem eG_at_zero (d : Dims) (N : ℕ) {v : ℝ} (hz : zt 0 v ≠ 0)
    (a₀ : ZMod ((band d).L N)) :
    Decay.eG ((band d).L N) ((band d).W N) (lkPath (sample d) 0 N v (0 : Ω d))
      (gloop ((band d).L N) ((band d).W N) ((sample d).H N v (0 : Ω d)) (zt 0 v))
      (LoopData.idx ((fun _ => true : Fin 2 → Bool),
        (fun _ => a₀ : LoopArg ((band d).L N) 2)))
      = 2 * (gZero (zt 0 v) true - Complex.I) * gZero (zt 0 v) true ^ 3
          * ((((band d).W N : ℂ))⁻¹) := by
  have hL3 : 3 ≤ (band d).L N := (band d).three_le_L N
  have hW0 : (((band d).W N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr ((band d).W_pos N).ne'
  rw [loopData_const_idx, Decay.eG]
  have hlen : (⟨[true, true], [a₀, a₀]⟩ : LoopIdx (ZMod ((band d).L N))).length = 2 := rfl
  rw [hlen, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} from rfl,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  simp only [cutGlue_one_const, cutGlue_two_const, gloop_zero_cutGlue_one d N hz,
    gloop_zero_cutGlue_two d N hz,
    show (([true, true] : List Bool).getD (1 - 1) true) = true from rfl,
    show (([true, true] : List Bool).getD (2 - 1) true) = true from rfl,
    lkPath_zero_one d N hz]
  set A : ℂ := gZero (zt 0 v) true - Complex.I with hA
  set c : ℂ := gZero (zt 0 v) true ^ 3 * ((((band d).W N : ℂ)))⁻¹ ^ 2 with hc
  have hinner : ∀ x : ZMod ((band d).L N),
      (∑ y : ZMod ((band d).L N), A * SB ((band d).L N) x y * (if y = a₀ then c else 0))
        = A * SB ((band d).L N) x a₀ * c := by
    intro x
    rw [Finset.sum_eq_single a₀]
    · rw [ite_eq_left (rfl : a₀ = a₀)]
    · intro b _ hb; rw [ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a₀) h
  have hsum : (∑ x : ZMod ((band d).L N), ∑ y : ZMod ((band d).L N),
      A * SB ((band d).L N) x y * (if y = a₀ then c else 0)) = A * c := by
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    calc (∑ x : ZMod ((band d).L N), A * SB ((band d).L N) x a₀ * c)
        = A * c * ∑ x : ZMod ((band d).L N), SB ((band d).L N) x a₀ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = A * c := by rw [SumZeroDyn.sum_SB_col _ hL3]; ring
  rw [hsum, hc]
  field_simp
  ring

/-- `(-((w) i))⁻¹ = w⁻¹ i`. -/
theorem gZero_imag {w : ℝ} (hw : w ≠ 0) :
    gZero ((w : ℂ) * Complex.I) true = ((w⁻¹ : ℝ) : ℂ) * Complex.I := by
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  show ((-((w : ℂ) * Complex.I)))⁻¹ = ((w⁻¹ : ℝ) : ℂ) * Complex.I
  refine inv_eq_of_mul_eq_one_right ?_
  push_cast
  rw [show (-((w : ℂ) * Complex.I)) * ((w : ℂ)⁻¹ * Complex.I)
      = -((w : ℂ) * (w : ℂ)⁻¹) * (Complex.I * Complex.I) by ring, Complex.I_mul_I,
    mul_inv_cancel₀ hwC]
  ring

/-- **The `E^{(G)}` integrand at `ω = 0`, `E = 0`, `v = 1 - w` is the real number
`2 (w⁻¹ - 1) w^{-3} / W`.**  In particular it is *not* bounded as `w ↓ 0`. -/
theorem eG_value (d : Dims) (N : ℕ) {w : ℝ} (hw : 0 < w) (a₀ : ZMod ((band d).L N)) :
    Decay.eG ((band d).L N) ((band d).W N) (lkPath (sample d) 0 N (1 - w) (0 : Ω d))
      (gloop ((band d).L N) ((band d).W N) ((sample d).H N (1 - w) (0 : Ω d)) (zt 0 (1 - w)))
      (LoopData.idx ((fun _ => true : Fin 2 → Bool),
        (fun _ => a₀ : LoopArg ((band d).L N) 2)))
      = ((2 * (w⁻¹ - 1) * w⁻¹ ^ 3 / ((band d).W N : ℝ) : ℝ) : ℂ) := by
  have hz : zt 0 (1 - w) = ((w : ℝ) : ℂ) * Complex.I := by
    rw [zt_zero_energy]; norm_num
  have hz0 : zt 0 (1 - w) ≠ 0 := by
    rw [hz]; simp [hw.ne', Complex.I_ne_zero]
  rw [eG_at_zero d N hz0, hz, gZero_imag hw.ne']
  have hW : (((band d).W N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr ((band d).W_pos N).ne'
  push_cast
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  field_simp
  ring_nf
  rw [hI4]
  ring

/-- **The `henvG` family of `RBM.sharpExpect_step6_driftEG` is unsatisfiable in the Gaussian
model at the energy `E = 0`.**

`henvG` asks for one real number `Env N` dominating
`‖E^{(G)}(L-K, L)_{v,σ,a}‖` for **every** `v : ℝ`, every `σ`, every `a` and every `ω`.  Taking
`ω = 0` and `v = 1 - w` with `w ↓ 0` makes the value `2(w⁻¹-1)w^{-3}/W`, which exceeds any
prescribed bound.  Hence no `Env : ℕ → ℝ` — polynomially bounded or not — can satisfy it.

Because `RBM.Steps.sharpExpect` (2.80) is needed for every `|E| ≤ 2 - κ`, this blocks the
whole (2.71) induction, not just the single energy `E = 0`.  The mechanism is generic: it is
the `v ↑ 1` divergence of the resolvent, which `Env` cannot see because the time is not
restricted to the window `[s_N, t_N]`. -/
theorem not_exists_env_eG (d : Dims) (N : ℕ) :
    ¬ ∃ Env : ℝ, ∀ (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2) (ω : Ω d),
      ‖Decay.eG ((band d).L N) ((band d).W N) (lkPath (sample d) 0 N v ω)
        (gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt 0 v))
        (LoopData.idx (σ, a))‖ ≤ Env := by
  classical
  rintro ⟨Env, hEnv⟩
  have hW0 : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
  obtain ⟨k, hk⟩ := exists_nat_gt (Env * ((band d).W N : ℝ) / 2)
  set w : ℝ := ((k : ℝ) + 1)⁻¹ with hwdef
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw : 0 < w := by rw [hwdef]; positivity
  have hwinv : w⁻¹ = (k : ℝ) + 1 := by rw [hwdef, inv_inv]
  obtain ⟨a₀⟩ : Nonempty (ZMod ((band d).L N)) := by
    have := (band d).neZeroL N
    infer_instance
  have hbound := hEnv (1 - w) (fun _ => true) (fun _ => a₀) 0
  rw [eG_value d N hw a₀, Complex.norm_real, Real.norm_eq_abs, hwinv] at hbound
  rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 2 * (k : ℝ) * ((k : ℝ) + 1) ^ 3 / ((band d).W N : ℝ))] at hbound
  have h1 : Env < 2 * (k : ℝ) / ((band d).W N : ℝ) := by
    rw [lt_div_iff₀ hW0]
    nlinarith [hk]
  have h2 : 2 * (k : ℝ) / ((band d).W N : ℝ)
      ≤ 2 * (k : ℝ) * ((k : ℝ) + 1) ^ 3 / ((band d).W N : ℝ) := by
    have hcube : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 3 :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hnum : 2 * (k : ℝ) ≤ 2 * (k : ℝ) * ((k : ℝ) + 1) ^ 3 := by nlinarith
    gcongr
  linarith

end EGShape

/-! ### §3  The Step 6 slots that *are* producible for the Gaussian model

These two are quantified over `0 < v < 1` in `RBM.sharpExpect_step6_driftEG`, so they are not
touched by §2. -/

section Analytic

/-- **`hEL` of `RBM.sharpExpect_step6_driftEG`, discharged for the Gaussian model.**

`RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` (T140) needs a ball around `v` on which
`|Im z| ≥ η`; on `|q - v| < (1-v)/2` one has `1 - q > (1-v)/2`, so `η := ((1-v)/2)·Im m^{(E)}`
works.  `hjoint` is `RBM.Gauss.differentiableAt_integral_gloop_flow` (T141) and the Stein
hypothesis is the proved `RBM.Gauss.matrixStein` (T70). -/
theorem hEL_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      HasDerivAt (fun q : ℝ => (sample d).ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm ((band d).L N) ((band d).W N) (mSigma E)
              ((sample d).H N v ω) (zt E v) (LoopData.idx (σ, b))
            + primRhs ((band d).L N) ((band d).W N) ((sample d).Lval E N v ω)
              (LoopData.idx (σ, b))) ∂(band d).P) v := by
  intro N v hv0 hv1 σ b
  have hm : 0 < (mE E).im := mE_im_pos hE
  set ε : ℝ := (1 - v) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set η : ℝ := ε * (mE E).im with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hball : ∀ q ∈ Metric.ball v ε, η ≤ |(zt E q).im| := by
    intro q hq
    rw [Metric.mem_ball, Real.dist_eq] at hq
    have hq1 : q < 1 := by
      have := (abs_lt.mp hq).2; rw [hεdef] at this; linarith
    rw [← etaT_eq_zt_im, abs_of_pos (etaT_pos hE hq1), etaT, hηdef]
    have : ε ≤ 1 - q := by
      have := (abs_lt.mp hq).2; rw [hεdef] at this ⊢; linarith
    exact mul_le_mul_of_nonneg_right this hm.le
  have hwf : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hn : 1 ≤ (LoopData.idx (σ, b)).a.length := by
    show 1 ≤ (List.ofFn b).length
    rw [List.length_ofFn]
    norm_num
  exact hasDerivAt_sample_ELval_hierarchy_gauss (matrixStein d) hv0 hη hε hball hwf hn
    (differentiableAt_integral_gloop_flow d N hv0 hη hε hball hwf hn).hasFDerivAt

/-- **`hintL2` of `RBM.sharpExpect_step6_driftEG`**, from `RBM.Gauss.integrable_sample_Lval`
(T76). -/
theorem hintL2_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      Integrable (fun ω => (sample d).Lval E N v ω (LoopData.idx (σ, b))) (band d).P := by
  intro N v _ hv1 σ b
  have hn : 1 ≤ (LoopData.idx (σ, b)).a.length := by
    show 1 ≤ (List.ofFn b).length
    rw [List.length_ofFn]
    norm_num
  exact integrable_sample_Lval (etaT_pos_of_lt_one hE hv1) (abs_im_zt E hE hv1).ge
    (LoopData.idx (σ, b)) (LoopData.idx_wf _) hn

end Analytic

end RBM.Gauss

/-! ### §4  The (2.71) half of the induction step -/

namespace RBM

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **(2.68)–(2.71) at `t` from (2.68)–(2.70) at `t` and (2.80) on `[s,t]`.**

This is the second pass of the induction of p. 24: the first pass (`RBM.Thm221NoEL`, T204)
delivers `RBM.BoundsCore` at `t`; Step 6 delivers (2.80), whose value at `u = t` is (2.71).
No hypothesis here is about the Gaussian model, and none is fiat — Step 6's conclusion is a
hypothesis, not a structure field that could be satisfied by `0`. -/
theorem bounds_of_boundsCore_of_sharpExpect (hBC : BoundsCore X E t)
    (hSE : UnifDetDom
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3))
    (hst : ∀ N, s N ≤ t N) : Bounds X E t where
  toBoundsCore := hBC
  expect := hSE.precomp_param fun N u => (TimeIcc.last hst N, u)

/-- The assembly agrees with `RBM.Bounds_of_Steps` on Steps 1–6: nothing was reshaped. -/
theorem bounds_of_boundsCore_of_sharpExpect_eq (h : Steps X E s t) (hst : ∀ N, s N ≤ t N) :
    bounds_of_boundsCore_of_sharpExpect (BoundsCore_of_Steps h hst) h.sharpExpect hst
      = Bounds_of_Steps h hst := rfl

end Assembly

end RBM

namespace RBM.Gauss

open RBM

section Witness

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

/-- (2.80) at the degenerate window `s = t = 0`: `E L_0 = K_0` exactly (2.67). -/
theorem sharpExpect_zero (X : Sample B) (hE : |E| ≤ 2) :
    UnifDetDom
      (fun N (p : TimeIcc (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) N × LoopData (B.L N) 2) =>
        X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N ((fun _ => (0 : ℝ)) N))⁻¹ ^ 3) := by
  intro τ hτ
  refine Eventually.of_forall fun N p => ?_
  have hp : (p.1 : ℝ) = 0 := le_antisymm p.1.2.2 p.1.2.1
  simp only [hp]
  rw [X.expErr_zero hE N p.2.idx p.2.idx_wf (by simp)]
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ)
    (pow_nonneg (inv_nonneg.2 (B.scale_nonneg E N zero_le_one)) 3)

/-- **Applicability witness for `RBM.bounds_of_boundsCore_of_sharpExpect`.**  Its three
hypotheses are jointly satisfiable, and the lemma then reproduces `RBM.Bounds_zero`.

This witness is *degenerate* (`s = t = 0`), and deliberately so: T202 recorded that
`RBM.Bounds` has no inhabitant at `s > 0`, and §2 of this file explains why the Step 6 route
that would produce one is currently blocked.  Nothing here pretends otherwise. -/
theorem bounds_witness_zero (X : Sample B) (hE : |E| ≤ 2) : Bounds X E (fun _ => 0) :=
  bounds_of_boundsCore_of_sharpExpect (Bounds_zero (X := X) (E := E) hE).toBoundsCore
    (sharpExpect_zero X hE) (fun _ => le_rfl)

end Witness

end RBM.Gauss


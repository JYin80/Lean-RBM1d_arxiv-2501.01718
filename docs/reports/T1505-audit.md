Auditor model: claude-opus-5-5[1m]

# T1505 audit: pathwise Z/Y decomposition of one grid step

- Ticket: `docs/tickets/T1505.md`. Prove report: `docs/reports/T1505-prove.md`.
- Branch `t/T1505` at `b8f1891`, base `ab5d007`. The diff against the base is exactly one new file, `RBM1D/Gauss/GridStepDecomp.lean` (997 lines). No other file is touched and no frozen signature is changed.
- Audit worktree: a fresh detached checkout at `/Users/junyin/Lean_proof/RBM1D-wt/T1505-audit2`. The prover's worktree was not reused. The main build cache had no `GridStepDecomp` artifact, so the module was compiled from scratch.
- Audit time: 2026-09-26 00:54 UTC.

## Overall verdict: PASS (T1 PASS, T2 PASS, T3 PASS, T4 PASS)

## 1. Math preflight
The prove report has a math preflight section for each of T1–T4, each marked PASS. It comes before the Lean section.

The report says the T1/T2 Lean draft already existed from an interrupted earlier run. The preflight was then re-derived and the draft checked against it. The statements of T1/T2 were not changed afterwards; only the proofs were repaired. I accept this ordering.

## 2. Statement vs ticket / supervisor note 2026-09-25-2045 §2 (a)–(c)

**T1: `lin_eq_fderiv`**
- Statement: `(fderiv ℝ Φ M X).re = lin N (gradMat Φ M) X` for Hermitian `X`, plus `lin_eq_fderiv_im` for `.im`.
- `gradMat Φ M := Matrix.of fun i j => wirtFirst d N Φ M j i`, so it is built from `wirtFirst`/`coordD1` as required.
- The Hermitian hypothesis on `M` and `TestFun Φ` are carried but not needed. The Lean result holds for every `M`, which is harmless.
- This goes through the complex identity `fderiv_eq_trace_gradMat` and the `Bmat` decomposition `herm_eq_sum_Bmat` of an arbitrary Hermitian `X`.
- Verdict: PASS.

**T2: `stepDecomp`**
- `stepXi` is `Σ_a U b a · Φ_a(H_{j+1}) − E[·|filt d j]`. This is item (a): the observable at the next step minus its own conditional mean.
- `stepZ` is `√(step) · lin N (Ab ω) (Xmat d N (ω (j+1)))` with `Ab ω = Σ_a (U b a) • gradMat (Φ a) (H_j ω)`. This is item (b), verbatim.
- `stepY := stepXi − stepZ`.
- The conclusion is the conjunction of four facts:
  1. the exact pointwise identity ξ = Z + Y;
  2. `Measurable[filt d j] Ab`;
  3. the a.e. bound `‖Y‖ ≤ C₂'·Δ·‖X_{j+1}‖² + E[C₂'·Δ·‖X_{j+1}‖² | F_j]`, with `C₂' = (Σ_a |U b a|)·(C₂/2)`;
  4. `E[Y|F_j] = 0` a.e.
- `hC₂ : ∀ a A, ‖D²Φ_a A‖ ≤ C₂` is exactly the `bdd₂` field shape of `BddC2C` (T133).
- The bound in (3) holds a.e. rather than for every ω. That is forced, because the conditional mean is only defined a.e.
- `Kval` does not appear anywhere. That is correct, since K is deterministic.
- Verdict: PASS.

**Deviation from the ticket's literal wording (delta `T1505a`)**
- `stepDecomp` adds `hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0`.
- It also types `U` as a real kernel, `LoopArg → LoopArg → ℝ`, where the ticket has a ℂ-linear `U : V →ₗ V`.
- Without these, the ticket's target as literally written is false. Z is real-valued, so for complex Φ or complex U the imaginary first-order term `√Δ·Im(...)` would sit inside Y. Y would then be only O(√Δ‖X‖), not O(Δ‖X‖²). So this restriction is a necessary correction, not a weakening chosen for convenience.
- It matches the case the paper uses:
  - For σ = (+,−), `ξ_i = m(σ_i) m(σ_{i+1}) = |m|²` is real. So `edgeKer = (1 − sξ S^B) Θ(tξ)` and `Uker` have real entries at real grid times.
  - The (+,−) two-loop `⟨G E_a G* E_b⟩` is real on Hermitian H.
- The dispatcher's downstream ticket T1512 is already written against `hReal` and the real kernel ("U = Uker(fun _ => 1) has real entries", T1509 (T1)).
- The prover could not write `docs/paper-deltas.md` because it was outside the ticket's sole writable file. The `T1505a` entry is still missing there. **Dispatcher action:** append it. This does not block the audit.

**T3: `stepDecomp_Y_sq`**
- Statement: `∫‖Y‖² ≤ 4·((Σ_a|U b a|)·(C₂/2))²·Δ²·∫‖Xmat(ω(j+1))‖⁴`.
- This is the ticket's `C₂²Δ²∫‖X‖⁴·4`, with the explicit `U`-row factor.
- `∫‖X_{j+1}‖⁴` does not depend on Δ: `H_{j+1} = H_j + √Δ • X_{j+1}` by `H_succ_eq`, and X is the unscaled increment. So the bound is genuinely O(Δ²).
- Integrability of `‖X‖⁴` is proved in `integrable_normPow4_incr`, and of `‖X‖²` in `integrable_normSq_incr`.
- Proof route: the pathwise bound, then `(x+y)² ≤ 2x²+2y²`, then conditional Jensen (`ConvexOn.map_condExp_le_univ`, from Mathlib), then the tower property.
- Verdict: PASS.

**T4: `stepDecomp_Z_subG`**
- The proof is literally `hasCondSubgaussianMGF_linear s t K N j (measurable_Ab …) E hE c hc hbound`, followed by `simpa only [stepZ]`.
- The hypotheses (`MeasurableSet[filt d j] E`, `0 ≤ c`, `∀ ω ∈ E, step·v N (Ab ω) ≤ c`) and the conclusion (`HasCondSubgaussianMGF (filt d j) … (E.indicator stepZ) ⟨c,hc⟩ (Pg d)`) match GridMarkov:564 exactly with `A := Ab`.
- The ticket's "pointwise c := Δ·v N (Ab ω)" cannot serve as a constant variance proxy. The event-restricted deterministic form is the one the ticket asks for.
- Verdict: PASS.

## Acceptance criteria (auditor items)
- **`Ab` is `filt d j`-measurable:** yes. See `measurable_Ab` and conjunct 2 of `stepDecomp`. The proof uses `H_measurable_filt` and the continuity of `gradMat (Φ a)` from `TestFun.continuous_fderiv`.
- **Z is exactly the `lin` form consumed by `hasCondSubgaussianMGF_linear`:** yes. `stepZ` is by definition `Real.sqrt (step s t K N) * lin N (Ab …) (Xmat d N (ω (j + 1)))`, and T4 closes by `simpa only [stepZ]` from that lemma.
- **Y bound is O(Δ) pathwise and O(Δ²) in L²:** yes. The pathwise bound is `C₂'·Δ·‖X‖²` plus its conditional mean, with `C₂' = (Σ|U b a|)·C₂/2`. The L² bound is `4C₂'²Δ²·E‖X‖⁴`.
- **Constants explicit:** yes.
- **First line of the report is `Prover model:`:** yes.

## 3. Vacuity, hidden hypotheses, cycles, boundary cases
- No structure fields carry hypotheses. Everything is in the signatures.
- **`hIntReal : Integrable stepZ`** is the only non-standard hypothesis. I checked that it is redundant, i.e. always dischargeable, with a compiled scratch lemma (`T1505Audit.hIntReal_discharge`). From `hΦ`, `hReal`, `hC₂` and `hΔ` it derives `Integrable (stepZ …)`, using `g_eq_pointwise`, `integrable_Phi_H`, `integrable_h0` and `integrable_Rlabel_sum`.
- **Nondegenerate witness, compiled.** Scratch lemma `T1505Audit.witness`:
  - `Φ a := momentFun (loopObs d N z (I a)) 1 = |L_{I_a}|²` for any family of well-formed loop indices, with `z.im ≠ 0` and `0 < η ≤ |z.im|`.
  - `TestFun` comes from `testFun_momentFun_loopObs`. `hReal` holds because `F·conj F = ‖F‖²`.
  - `C₂ := Σ_a |C_a|` from `bdd₂`. Any real `U` and any `Δ ≥ 0` are allowed.
  - All hypotheses of `stepDecomp_Y_sq` are then met, and it was applied with the discharged `hIntReal`.
  - Printed axioms for both scratch lemmas: `[propext, Classical.choice, Quot.sound]`.
  - The scratch file was deleted afterwards and no source was edited.
- The witness does not rely on any astronomically large quantity.
- Boundary cases:
  - `Δ = 0` is allowed. Then Z = 0, and the Y bounds reduce to 0.
  - `j = 0` needs no special case.
  - `LoopArg (d.L N) 2` is nonempty.
  - There is no `∀ᶠ N` and no window or index collapse; it is a single deterministic step.
- No cycles. Imports are GridMarkov (T1482), GridOneStep, GridStopFilt, LoopC2, MomentGronwall, OpNorm and Hierarchy.Kernel, all already on `main`, plus Mathlib CondJensen and Convex.Mul.
- **Name clashes at merge:** none. I checked every public declaration name in the file against all 12 `RBM.Gauss.Grid`-namespace files on current `main` (`3775cd6`).

## 4. Dependencies
Only accepted results are used: T1481, T1482 (merged), T133 `BddC2C`/`norm_fderiv2_apply_le`, `TestFun`/`wirtFirst`/`coordD1`/`Bmat` (Generator, MomentGronwall), and `integrable_norm_Xmat_pow` (OpNorm). The only external input is Mathlib.

## 5. Builds and axioms (audit worktree)
- `lake build RBM1D.Gauss.GridStepDecomp`: success (3731/3731, module rebuilt in 4.0 s). Only linter warnings; no errors.
- `lake build RBM1D`: `Build completed successfully (9652 jobs)`. The root import of this module is added only at merge, per the ticket.
- `grep` finds no `sorry`, `admit` or `axiom` in the file.
- `#print axioms` for `lin_eq_fderiv`, `lin_eq_fderiv_im`, `stepDecomp`, `stepDecomp_Y_sq`, `stepDecomp_Z_subG` and `integrable_normPow4_incr` all give `[propext, Classical.choice, Quot.sound]`.
- Four declarations use `set_option maxHeartbeats 4000000 in`, each with a stated reason. This is acceptable.

## Open items (non-blocking, for the dispatcher)
1. Append delta `T1505a` to `docs/paper-deltas.md`: the `hReal` hypothesis and the real kernel `U`, with the justification above.
2. As the prover noted, the event-wise sup bound `c` in T4 is not by itself the label-weighted `c_j^{(k,a)}` that T1504 (T1′) needs. That is T1512's scope, not a defect of T1505.

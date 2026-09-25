Auditor model: claude-opus-5-5[1m]

# T1492 audit: (4.2) => (5.57) at (2.73)-reduced strength, on one high-probability event

Branch `t/T1492` (tip `edf992b`). Diff against `main`: one new file, `RBM1D/Gauss/Step2Eq557.lean` (+561). Audit worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1492-audit` (detached at `edf992b`, because `t/T1492` is already checked out in the prover worktree).

## Verdicts

| Target | Declaration | Verdict |
|---|---|---|
| T1 | `RBM.Gauss.Step2.highProb_eq557_col` | **PASS** |
| T2 | `RBM.Gauss.Step2.highProb_eq557_colRow` | **PASS** |

## 1. Math preflight

`docs/reports/T1492-prove.md` §(a) contains a per-target math preflight with verdict PASS for T1 and T2. It is marked "written before any Lean edit" and comes before §(b), which covers declarations and build. It includes the Step-0 check the ticket asks for. Both `entryBoundFlow_floor` and `Step1.apriori` are `StochDom` statements indexed by `TimeIcc s t N × …`, so they are already uniform in `u`, and the fixed-`u` fallback was not needed. I confirmed this for `entryBoundFlow_floor` through its `EntryBoundFlow'` index type, which the proof uses directly.

## 2. Statement vs. target (M2 of `docs/reports/T1488-prove.md` §3, audited PASS in T1488-audit)

- Notation. The Lean `(band d).scale E N u` unfolds to `(B.W N) * B.ell N u * etaT E u` (Flow/Hypotheses.lean:191), which is exactly M2's `A_u = W ℓ_u η_u`. `ℓ_u = (band d).ell N u` and `ℓ_s = (band d).ell N (s N)` also match M2. `blkW r x = W⁻¹·1(r.1 = x)` (Lemma57.lean:811), so the column sum is `W⁻¹ Σ_{r∈I_x} |G_u(r,p)|`, the block average of (5.57).
- Bound. `(N:ℝ)^τ * √(ℓ_u/ℓ_s) * (√A_u)⁻¹`, i.e. `N^τ r^{1/2} A_u^{-1/2}`. This is the (2.73)-reduced exponent in M2. It is neither weakened (the only loss is `N^τ` for arbitrary `τ > 0`) nor presented as full-strength (5.57).
- The bound is not trivially true. The trivial estimate is `≤ max|G| ≲ η_u⁻¹`, whereas the target is `A_u^{-1/2}·N^τ`, and that is small in the regime `N^c ≤ A_t`.
- Column form: `∀ u : TimeIcc s t N, ∀ x y, ∀ p, p.1 = y → ∑ r, blkW r x * ‖G r p‖ ≤ …`. Row form: `∀ r, r.1 = x → ∑ p, blkW p y * ‖G r p‖ ≤ …`. Both match M2 verbatim, and T2 puts them on one `HighProb` event.
- Quantifier order: `d, κ, E, s, t`, then the hypotheses, then `τ`, then `HighProb` (its internal `∀ D > 0, ∀ᶠ N`). Fixed parameters come before `∀ᶠ N`, and `u` is inside the event, so the event is uniform over the uncountable `TimeIcc`.
- Hypotheses. They are exactly the Step-1 list. I checked this against `#check @RBM.Gauss.step1Hyp_gauss_of_scale''`: `0<κ`, `|E| ≤ 2-κ`, `BoundsCore (sample d) E s`, `∀N, 0 ≤ s N`, `∀N, s N ≤ t N`, `∀N, t N < 1`, `Cond272 (band d) E s t`, `0<c`, `∀ᶠ N, N^c ≤ (band d).scale E N (t N)`, plus `0 < τ`. Nothing is added. `Cond272Reg`, which `APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow` needs, is assembled internally as `⟨hcond, hreg⟩`. The statement holds for every `d : Dims`, not only for `exampleGrow` or a special case.
- Paper text. I could not render `paper/250520-YinJun-v2.pdf` in this environment (no poppler or PyMuPDF). The comparison with the paper therefore goes through the audited T1488 row A3 / M2, which is how the ticket defines the target.

## 3. Vacuity, hidden hypotheses, cycles

- Satisfiability. I compiled a nondegenerate witness in the audit worktree with `lake env lean` on a scratch file, and it produced no errors. From `APrimeGeneralMovingDriftSourceGeneralDims.positive_length_exampleGrow_resident` (the actual-resident companion of `eventually_commonEvent_nonempty`, which it calls; APrimeGeneralMovingDriftSourceGeneralDims.lean:127/573), I took `s ≡ 0`, `t` with `∀ᶠ N, s N < t N` (a positive-length window), `c > 0`, `Cond272Reg`, and `BoundsCore (sample exampleGrow) 0 s`. I then applied `Step2.highProb_eq557_col Dims.exampleGrow (κ := 1) … hreg.1 hc hreg.2 τ hτ` for every `τ > 0`, and it type-checks. The witness does not rely on an astronomically large quantity, and the window does not collapse.
- Boundary cases. There is no `N = 0` or empty-index loophole: `TimeIcc s t N = Icc (s N) (t N)` is nonempty because `s N ≤ t N`, and `ZMod (d.L N)` and `Fin (d.W N)` are nonempty. `HighProb` (StochDom.lean:95) is the standard `∀ D > 0, ∀ᶠ N, P(Ξ_N)ᶜ ≤ N^{-D}`.
- No structure fields are introduced, and no hypothesis is hidden in a structure field. The two private helpers (`sqrt_add_le_aux`, `blockSum_le`) are fully proved local lemmas.
- No cycle: the module imports only `Gauss.EntryBoundTime`, `Gauss.APrimeGoodSetFlowGeneralDims`, `Hierarchy.Lemma57` and `Hierarchy.EEBridge`, all accepted modules on `main`.

## 4. Dependencies

All dependencies are accepted, committed declarations: `entryBoundFlow_floor`, `Step1.apriori`, `step1Hyp_gauss_of_scale''`, `APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow`, `Lemma57.blkW`/`sum_blkW`, `Step3.ellHat_mono`, `etaT_mul_ellHat_le` and `EEBridge.eeFacts`. The branch adds only the one file.

## 5. Build, axioms, forbidden tokens, frozen signatures

- `lake build RBM1D.Gauss.Step2Eq557` succeeded ("Build completed successfully (3879 jobs)"), with no errors. The only warnings are lint warnings: the unscoped `set_option maxHeartbeats 1000000`, a deprecated `if_neg`, `show`, unused simp args, a flexible `simp at hmem`, and one line longer than 100 characters.
- `lake build RBM1D` succeeded ("Build completed successfully (9639 jobs)"). As the ticket says, the root import is added at merge (H10), so this build does not yet include the new module.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for both `highProb_eq557_col` and `highProb_eq557_colRow`.
- `grep` finds no `sorry`, `admit` or `axiom` in the file.
- No existing file is modified, so no frozen signature is touched.

## Notes for the dispatcher (non-blocking)

1. The Lean statement is the (2.73)-reduced form, `N^τ (ℓ_u/ℓ_s)^{1/2} A_u^{-1/2}`, not the paper's full (5.57) `A_u^{-1/2}(1 + J* A_u^{-1})`. This matches the ticket and M2, but CLAUDE.md §3.7 asks for a paper-deltas entry. The prover could not write that file under the ticket's sole-writable rule. Suggested tag: `T1492a`. The entry should also record the prover's warning that the short name `highProb_goodSetFlow` resolves in two namespaces, and that `APrimeGeneralMovingGoodSetFlowActual.highProb_goodSetFlow` is hard-wired to `Dims.exampleGrow`.
2. Cosmetic: `set_option maxHeartbeats 1000000` is unscoped (a linter warning). It could be turned into `set_option … in` on the theorem at merge time, but that is not required.

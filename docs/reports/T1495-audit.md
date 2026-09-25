Auditor model: claude-opus-5-5[1m]

# T1495 audit — M1: initial condition `J*_{s,D} ≺ 1` (§5.3, from (2.68)/(2.69))

Branch `t/T1495` (commit 0297d2a, merge-base with `main` = 5ef3f4a). Audit worktree:
`/Users/junyin/Lean_proof/RBM1D-wt/T1495-audit` (detached at 0297d2a; `t/T1495` is checked out in the prover worktree).
Diff vs `main`: one new file, `RBM1D/Hierarchy/Step2Init.lean` (+66). Nothing else is touched.

## Target (T1) `RBM.Step2.stochDom_jS_init` — **PASS**

### 1. Math preflight
`docs/reports/T1495-prove.md` §1 contains "Verdict: PASS", placed before §2 (Lean). It follows the Step 0 read-only check that `hinit` in `jS_highProb` is `BoundsCore.decay` composed with `decayProf_le_tT` under `1 ≤ B.scale E N (s N)`. OK.

### 2. Statement vs paper / ticket / M1
Compiled signature (`#check`):
```
∀ {Ω} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s : ℕ → ℝ},
  BoundsCore X E s → |E| < 2 → (∀ N, 0 ≤ s N) → (∀ N, s N < 1) →
  (∀ᶠ N in atTop, 1 ≤ B.scale E N (s N)) →
  ∀ D : ℝ, 0 < D → StochDom B.P (fun N _ ω => Step2.jS X E D N (s N) ω) (fun _ _ _ => 1)
```
- This matches `docs/reports/T1488-prove.md` §3 M1 and the ticket (T1) word for word: the same five hypotheses, `∀ D > 0`, the index type `Unit`, and the time `s N`.
- The bound is the literal constant `1`, so this is ≺ 1. No `N^ε` appears in the statement. The `N^τ` loss sits only inside the `StochDom` definition, whose `∀ τ > 0` the proof handles by working at `τ/2` and using `N^{τ/2}+1 ≤ N^τ` eventually.
- Quantifier order: fixed data `X, E, s`, then `D`, then the `StochDom` built-in `∀ τ, ∀ᶠ N`. This is the paper's order.
- `jS` is the accepted definition of `J*_{u,D} = sup_a |(L-K)_{u,(+,-),a}| / T_{u,D}(|a1-a2|) + 1` (`Gauss/APrimeSmoothPrefixCanonicalCore.lean:96`). (2.69) is the field `BoundsCore.decay`. `∀ D > 0` is at least as strong as the paper's "for all large D".
- `hE`, `hs0` and `hs1` are unused by the proof (linter warnings). M1 requires them, so keeping them matches the target. It is not a weakening of the conclusion.
- Not a special case. It holds for an abstract `Band`/`Sample`, any energy `|E| < 2` and any time sequence `s`. No `Dims.exampleGrow`, no fixed `D`, no `E = 0`, no first cell.

### 3. Vacuity / hidden hypotheses / cycles
- **Compiled witness** (scratch file, not in the repo; `lake env lean` in the audit worktree, no errors). For every `B : Band Ω`, every `X : Sample B` and every `|E| < 2`, the sequence `s ≡ 0` satisfies all five hypotheses at once:
  - `BoundsCore X E (fun _ => 0)` by `RBM.BoundsCore_zero X hE.le` (Flow/Thm221NoEL.lean:126, accepted);
  - `0 ≤ 0` and `0 < 1`;
  - `∀ᶠ N, 1 ≤ B.scale E N 0` from `Band.scale_zero_ge_rpow` (`N^{1/2} ≤ scale`) and `1 ≤ N^{1/2}`.

  The theorem was then applied to this witness and type-checks. The scale bound needs only `≥ 1`, while the actual scale is `≥ N^{1/2}`: no huge quantity is needed. `B.L N ≥ 3`, so the index sets are nonempty. The statement is `∀ᶠ N`, so `N = 0` plays no role.
- Caveat, recorded but not a defect: at `s ≡ 0` the conclusion is easy, because `L = K` at time 0. Positive-time instances of `BoundsCore` come from the accepted Theorem 2.21 step producers (e.g. `boundsCore_step_of_inputs_*`), which are conditional on their own inputs. The hypothesis bundle is the paper's inductive hypothesis (2.68)–(2.70), the same one the accepted `jS_highProb` uses. It is not contradictory.
- No structure fields were smuggled in. `BoundsCore` is the existing accepted structure with fields `LmK`/`decay`/`localLaw` = (2.68)/(2.69)/(2.70), unchanged.
- No cycle. The new file imports only `RBM1D.Hierarchy.Step2`.

### 4. Dependencies
The proof uses `BoundsCore.decay`, `StochDom.highProb`, `SumZeroDyn.stochDom_of_good`, `Step2.norm_lk_eq`, `Step2.decayProf_le_tT`, `Step2.jStar_le`, `eventually_le_rpow`, `UnifDetDom.rpow_half_mul_rpow_half` and `Band.W_pos`. All are already committed on `main` and in the root import closure.

Note: `main` already has an equivalent result under a different hypothesis list: `RBM.stochDom_jS_init_of_boundsCore` (Gauss/APrimeSlotFields.lean:537) takes `hst`, `ht1` and `Cond272` in place of `hAs`. So T1495 duplicates part of an existing lemma, but in the M1 form the ticket asks for. This is informational only, not a defect.

### 5. Builds, axioms, forbidden tokens
- `lake build RBM1D.Hierarchy.Step2Init`: Build completed successfully (3749 jobs). The only warnings are the three unused variables `hE`/`hs0`/`hs1`.
- `lake build RBM1D`: Build completed successfully (9639 jobs). On the branch, the root does not yet import `Step2Init`; the import is added at merge, as the ticket says.
- `#print axioms RBM.Step2.stochDom_jS_init`: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit` or `axiom` in the new file. No frozen signature is modified (the diff only adds a file).
- Paper deltas: none needed. The statement is the paper's `J*_{s,D} ≺ 1`.

## Verdict
T1495 (T1) `RBM.Step2.stochDom_jS_init`: **PASS**.

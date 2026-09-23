# STATUS — current project state

## 1. Goal and hard boundary

- Goal: formalize the full paper in Lean.
- The only permitted external mathematical input is the complex Hermitian form of [51], Theorem 2.2.
- T230 A′ passed the proof-first review T401–T406, including the raw moving-window statement, the full-time first cell (`j_G≤2`), and deterministic `Ψ²` averaging.
- General moving-window `hfamily`, universal `APrimeSlot'`, the six-step chain, and the paper are **not closed**.

## 2. Current mathematical state

### Restricted first cell

The actual fixed package now contains:

- T571: p-independent `WeightedMoment`;
- T573–T574: exact weight fields and coefficient-one cutoff transfer;
- T576: fixed `E=0`, `D=60`, first-cell `APrimeHypOn` and `APrimeSlot'`;
- T578: the corresponding fixed first-cell `JSNormDom`;
- T581: the corresponding fixed first-cell full `APrimeSlot`.

T578 and T581 were independently rebuilt (4025 jobs each). Their public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. These are nondegenerate first-cell results only; they do not satisfy the universal moving/all-`D` slot.

### General moving window

- T575 is accepted: the actual Gaussian Step-1 inputs produce one `HighProb goodSetFlow` event for arbitrary fixed moving `(E,s,t)`, with the exact `flowDelta=(Wℓ_tη_t)^(-1/6)` threshold and no exponent loss.
- T579 is accepted: one measurable common event carries T491 raw sources, T575 `goodSetFlow`, T523 centered two-charge input, and block `jG` on the same sample, retaining both endpoints, three losses and exact support-local `ratR^4`.
- T580 is accepted as the next-step audit: the first honest post-T579 theorem is the positive-cell exact evolved-QV profile behind (5.42), before deterministic simplification. It keeps `ratR^4`, repaired `W⁻¹`, quadratic-source and leakage rows, and treats `k=0` only after time integration.
- T584 is independently accepted: the general-moving positive-cell evolved-QV profile is compiled on T579's literal common event, with exact `Jbar`, `ratR^4`, repaired `2W⁻¹`, both leakage mechanisms and endpoint ratios; it is pointwise and requires `k≥1`.
- T585 and T587 are accepted as preflights. T590 implements the exact deterministic `1200=16+1152+32` absorption, while T591 implements the all-`k` widened-weight QV integral budget with the zero cell handled only by zero-length integration. Neither report supplies a moment family or stopping/BDG theorem.
- T586 is independently accepted: the general-moving drift source is compiled on the same common event, with exact centered coefficient `4N^ζr_u`, raw three-loop source, `flowDelta+W⁻¹`, literal `Jbar`, separate near/far branches and closed-prefix endpoints. It is pointwise only; the paper's integrated (5.35)/(5.41) consequence remains open.
- T590 is independently accepted: the exact deterministic QV absorption keeps `1200=16+1152+32`, literal `sourceC4`, `R_u⁻²R_v⁻²`, repaired `2W⁻¹`, both `W⁻ᴰ` leakages and the square of the full root sum; it remains pointwise on `k≥1`.
- T591 is independently accepted: the all-`k` widened-weight QV integral budget keeps T584's exact profile, pays the common-event complement from the literal `2²¹N^(2D+16)` envelope, and handles `k=0` only by equal-endpoint integration. The smooth/widened support mismatch remains open.
- T592 is accepted as the cross-bridge preflight. Its selected next theorem is T597's same-sample running `jSnorm` cap on `commonEvent ∩ smooth transition`; it does not reverse `widenedW≤smoothWeight` or claim a cross budget.
- T593 is accepted as the drift-integral preflight. The first missing implication is upstream of integration: T598 must connect T586's linear source, the exact (5.34) quadratic gluing row, `Uker` propagation and literal `driftScale`, producing a fixed-`Dims.exampleGrow` pointwise `driftAt` profile with `R_u⁻²R_v⁻²`.
- T594 is accepted as the support-mismatch preflight. The same-`δ` reverse implication is false; T599 instead proves the buffered deterministic bridge `actualWeight(δ)>0 → widenedW(δ+ξ)>0`, with the sole new loss `N^(2ξ)` and no event hypothesis.
- T595 is accepted after independent review: (5.39), T488's endpoint-uniform initial estimate, and the literal smooth-weight bounds support the thin net-indexed adapter T600 with exact `N^(5δ/32)R_v⁻²`; this does not close any moving family or slot.
- T597 is independently accepted: on the identical sample in T579's `commonEvent` and the literal smooth transition, the closed positive prefix has the exact cap `(16·exp(1)^2+1)N^(2δ)`, with both endpoints and no widened/smooth reversal. It does not prove that the event/transition intersection is inhabited or supply a cross budget.
- T596 is independently accepted only as a partial positive-grid reduction: the actual all-charge `xiLK … 2` cutoff moment is reduced with coefficient one to the explicit `4L_N²` Duhamel family, including the independent `(+,+)` sector. The uniform family absorption and the `v=s_N` endpoint branch remain open; T602 audits the next analytic step.
- T599 is independently accepted: positive literal smooth weight at `δWeight` implies positive canonical widened weight at `δWeight+ξ`, uniformly over all active `k` including `k=0`, with sole loss `N^(2ξ)` and no event. The false same-`δ` reverse implication remains rejected; T603 uses only the buffered direction.
- T598 is independently accepted: on the identical T579 common-event sample and positive widened support, the full positive-cell `driftAt` profile has exact `xiK·R_u⁻²R_v⁻²`, retains T586's near/far/residual coefficients and the literal (5.34) `Step2.jS²` row, and covers both time endpoints. It is pointwise only; T604 audits the integration step.
- T600 is independently accepted: one uniform constant-one use of T488 followed by weight monotonicity supplies the literal target-net actual-smooth initial budget for every active `k`, including `k=0`, with exact `N^(5δ/32)R_v⁻²` and no extra loss. It is only the initial term; T605 audits its consumer seam.
- T601 is independently accepted as the post-T597 cross preflight. T606 is the smallest thin transition-to-buffered-QV adapter. A full `crossPart_active_le_jointEvent` specialization still lacks the general-moving favorable `prefixGradient`, five-field regularity and global joint envelope; T607 audits the first of these.
- T603's main bridge compiles and its exponent/event ledger is correct, but acceptance is blocked: the delivered witness does not realize an active `k≥1`, one common-event resident, and positive actual smooth weight simultaneously. A fresh repair ticket must add that same-resident witness before T603 can be archived or committed.
- T602 is accepted after independent correction: the first noncircular post-T596 analytic row is the arbitrary-charge transported initial estimate T608. The raw drift route is circular through `A_u⁻³η_u⁻¹·xiLK₂²`; the domain/index witness at `s_N=0` is explicitly a zero transported-initial probe, not a nonzero-value witness.

## 3. Running work

| Ticket | State |
|---|---|
| T583 | Delivered; rejected pending T588 signature correction |
| T588 | Rejected: Eq548 existential scope and `D/Kmod` quantifier order are overstated |
| T603 | Delivered theorem; repair required before acceptance |
| T604 | Delivered: scheduler audit pending |
| T605 | Delivered: scheduler audit pending |
| T606 | Running: transition-to-buffered-QV adapter |
| T607 | Running: general-moving prefix-gradient preflight |
| T608 | Running: arbitrary-charge transported-initial row |
| T609 | Running: T603 same-resident positive-cell witness repair |
| T610 | Running: left-endpoint flow/initial connector |

Full ticket text is intentionally kept out of this file; see `docs/TASKS.md` and `docs/reports/`.

T582 is accepted as a scope audit: the fixed `E=0,D=60` first-cell slot cannot satisfy the merged consumer's `∀ E,s,t,c,D≥60` table. After T579 acceptance, its selected next theorem is exactly T584; the other five merged inputs remain sibling obligations.

T583 is rejected for using scalar `s,t`, `Cond272Reg (sample d)`, a spurious `c` argument in `Step1.Hyp`, and `d : Data`. T588 corrected those signatures but is also rejected because it overstated the existential Eq548 failure and put `Kmod` outside the required `D` dependence. T589 supersedes both for the cut-slot branch.

T589 is accepted as the corrected cut-slot preflight. The first exact analytic blocker is the arbitrary-moving-window truncated `2p`-moment family for the actual all-charge `xiLK … 2`, especially the independent `(+,+)` charge, at threshold `N^(2δ)·flowAs^(1/2)`. The event modulus, mesh and cardinality fields have noncircular sources (`Kmod=21`, `γ=1/2`, `Ccard=43`); no A′/`jSnorm` result supplies this all-charge moment.

## 4. Exact open blockers

1. Produce the general moving `WeightedMoment`/`hfamily` with one common event and the paper’s exact N/W/time powers.
2. Upgrade from one fixed first cell and `D=60` to the merged consumer’s quantifiers `∀ E,s,t,c,D≥60`.
3. Finish the actual general drift/cross/QV chain, retaining near residuals and `ratR^4`; do not substitute first-cell bounds into universal statements.
4. Supply the other five universal inputs of `thm221NoEL_of_inputs_mergedOnAll_aprime'`.
5. Only then run the six-step and whole-paper acceptance audits.

Named remaining leaves include Lemma 5.14 slot 4 (`flowXiLK_1≺1`, actual `xiRhs≺1`, `hnum`, Case 1) and the slot-5 Eq. (4.5) boundary: T326 closes only the sharp first cell, while later cells/gain inputs remain open.

## 5. Repository and acceptance discipline

- Never stage unrelated or in-flight files. In particular exclude `RBM1D/Gauss/APrimeNearRem.lean`, T280 reports, `Claude outputs/`, blueprint artifacts, and every unaudited worker file.
- A completion requires exact statement/quantifier/exponent review, boundary and common-event checks, acyclicity, nondegenerate satisfiability, full module build, and public axiom audit.
- Allowed printed axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- The scheduler does not write Lean proofs. New Codex work uses fresh task threads. No reset credit may be used without Jun’s explicit approval.
- Theorem 2.6 work starts only after the other high-risk blocks. Blueprint/Pages work remains paused.
- Keep only the current `rbm1d-lean` heartbeat active; do not revive the old `rbm1d` automation or duplicate scheduling.

## 6. Where history lives

- Completed tickets: `docs/archive/TASKS-done.md`
- Per-ticket evidence: `docs/reports/Txxx.md`
- Older project history: `docs/archive/`
- Paper/Lean statement differences: `docs/paper-deltas.md`

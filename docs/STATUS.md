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
- T603/T609 are independently accepted: the buffered actual-smooth QV bridge keeps `δWeight` distinct from `δCap=δWeight+ξ`, the identical target mesh/sample/common event and T590's complete absorbed profile. The repaired witness realizes one common-event resident, active `k=1`, widened weight one and positive actual smooth weight simultaneously. This remains a positive-cell conditional bridge, not a QV integral, cross closure, or general A-prime result.
- T606 is independently accepted only as a conditional transition-to-buffered-QV adapter: on the same resident of `commonEvent ∩ transition`, it retains `δWeight`, `δCap=δWeight+ξ`, the complete (5.42) profile and closed positive-cell endpoints. No producer yet proves that intersection inhabited, so no cross estimate or downstream closure is claimed.
- T617 is independently accepted: the event-free all-sample envelope covers every active `k` including `0`, both closed endpoints, arbitrary two-charge word/output and the same sample, with root factors `2^15·N^(D+8)` and `2^11·N^(D+8)`, product `2^26·N^(2D+16)`, and payment `N^(2D+17)`. It proves no event inhabitance, five-field regularity, cross budget or closure.
- T607 is independently accepted after fixing its API scope to private `d=Dims.exampleGrow`, `B=band d`: the first noncircular favorable-prefix producer uses same-time raw coordinate QV, every stored `j<k` including `j=0`, and the exact T333 normalization. It remains conditional on `commonEvent ∩ transition`, whose inhabitance is not proved; T613 implements only this localization.
- T618 is rejected after independent audit despite correct local statements: its transitive imports reach `Flow.Step345Producer` through `APrimeCrossJointSplit→APrimeBadSplit→APrimeDuhamelModel→APrimeModel`, and reach `Flow.FirstCell`/`APrimeOneStep` through `APrimeQVRateTime→APrimeWeight→APrimeSlotFields`. The source/report remain excluded; the required repair is an upstream core extraction, not acceptance of the cyclic leaf.
- T612 is independently accepted: the first missing cross-complement leaf is T617's event-free all-sample `prefixGradient·sqrt(qvAt)` envelope with exact exponents `D+8`, `D+8`, `2D+16`, and payment `2D+17`. The five-field regularity package remains downstream; T618's attempted measurability split was rejected for transitive downstream imports. T617 proves neither (5.42) nor the cross budget.
- T619 is the selected first noncircular repair of T596's raw-drift obstruction toward (2.77): a same-sample all-charge smooth-prefix localizer over `(j,q)` with separate smooth-max order `r` and moment order `P`, exact terminal `twoCutLevel`, `WeightC1`, plateau, and both ordinary/derivative support caps `(4e+2)·twoCutLevel`. Terminal `cutTrunc≤self` alone is insufficient; no weighted drift absorption, cross-term budget, all-charge moment or Step-3 closure is claimed.
- T614 is independently accepted after correction: T619 must build its regularized prefix maximum locally from upstream modules, fix `P` before eventual `N` and choose `r` after `N`, evaluate each stored field at `sqrt(u_j)•M`, cover only positive mesh endpoints plus the separate initial endpoint, and later intersect the norm event with the pre-Step-3 `lkPath` decay event before using the quadratic drift bound.
- T613 is independently accepted only as a conditional favorable-prefix localization: at private `Dims.exampleGrow`/`band d`, every stored `j<k` including `j=0` uses the same-time raw coordinate QV with exact `ratR⁻⁴·tT⁻¹·threshold⁻¹` normalization on the identical sample in `commonEvent∩transition`. The intersection's inhabitance, the cross estimate and all downstream closures remain open.
- T620 is independently accepted only as a corrected blocked ledger: the sharp direct integration is sound, but a future fixed-`sigPM` consumer must bound `profile+N⁻ᵝ` before deriving the `g` corollary, prove the needed `c≤1`, and wait for T625 to remove the `Flow.Step345Producer` import path. It closes no drift slot or downstream A-prime result.
- T624 was withdrawn before acceptance: the proposed imports are transitively downstream through `APrimeSlotArith→APrimeModel→Flow.Step345Producer`, so the half-drift-slot theorem is not yet a noncircular pre-Step-3 leaf even though T620's exponent ledger may remain useful.
- T625 is the replacement dependency-boundary audit: trace the exact imports and theorem ownership needed for T620's sharp drift integration and slot arithmetic, then select the smallest signature-preserving upstream core extraction. It is read-only and may not classify the half-slot theorem as dispatchable until the Step345Producer path is removed.
- T625 is delivered for independent audit: it confirms the T620 envelope API and finds five independent downstream ingress paths. T630 is the first bounded extraction step: move only `cWt`, the three one-step scalar terms, and the drift-slot prefix into clean same-namespace cores while leaving all public signatures and downstream facades intact. It proves no integral or half-slot theorem.
- T616 is independently accepted only as a conditional mathematical ledger for the arbitrary-charge QV row `R_{u,v}^4 A_u⁻⁴η_u⁻¹ flowR^5`. Implementation is doubly blocked: T621 found no simultaneous same-window `hEE`/`hapriori` witness, and the proposed module imports reach Step45/Step6/FirstCell. T626 audits a clean upstream extraction; no conditional theorem is treated as closing the all-charge QV row.
- T621 is independently accepted only as a blocked producer audit: the floored same-window `hEE` chain, length `6`, exponent `18`, and `A_u⁻⁴η_u⁻¹xiL₆` profile are correct, but no simultaneous `(2.75),(2.76)` witness exists and current imports reach Step45/Step3. T626 must extract an upstream core; neither `hEE` nor `XiLKTwoCutQV` is dispatchable.
- T626 is the file-disjoint read-only dependency audit for the T621/T616 line: preserve the flexible floored exponents and exact `A_u⁻⁴η_u⁻¹xiL₆` target while locating the smallest signature-preserving extraction below Step45/Step6/FirstCell.
- T622 audits the literal five measurable/integrable fields for `crossPart_active_le_jointEvent`, using T617's event-free product envelope but not rejected T618. It must identify a genuinely upstream measurability/core split, keep `p≥1` fixed before eventual `N`, exclude first-cell/downstream packages, leave `commonEvent∩transition` inhabitance unresolved, and make no cross-budget or closure claim.
- T622 is independently accepted only as a blocked five-field/core audit: the mathematics, `∀p≥1` order, endpoints, `k=0`, same sample and event separation are correct, but the original seven-stage split is superseded. T627 needs clean `Step2Bootstrap`; a QV-rate core must use `Gauss.quadVar_nonneg`; and the global-poly core must avoid downstream `coordWt2`. T629 audits the remaining seams before implementation.
- T615 is independently accepted: the actual-smooth weighted drift norm is integrated on every active target cell with `deltaWeight` distinct from `deltaCap`, T598's full near/far/residual and endpoint powers unchanged, the actual `Step2.jS` cap supplied by T579, and T611 used only for the all-sample complement envelope. `k=0` is handled solely by zero-length integration. This is not yet the deterministic profile absorption or drift slot.
- T619 received a dispatch-critical dependency correction from the T614 audit: it must not import `APrimeSmoothPrefix`, whose transitive chain reaches downstream `Flow.Step345Producer`; the needed regularized soft-max/ContDiff facts must be local/lower-level. Any later drift event must also include the pre-Step-3 Lemma-5.9 `LoopDecay` input, not only the norm event.
- T619 is rejected after independent audit despite correct theorem content and successful builds: its module still reaches Step45/Step3 through `Lemma514Holder`, Step6 through `Step2Bootstrap`, and downstream theorem facades through `Thm221Bare`/A-prime analytic imports. Commit `653879c` was pushed only because the worker committed directly to shared `main`; it is being reverted from the branch. A repair must first extract clean modulus, soft-max, analytic-derivative and scale-hypothesis cores.
- T623 is the preflighted nonvacuity line for the conditional T606/T613 cross route: audit the literal fixed-model `commonEvent∩transition` using Gaussian support, continuity and anti-concentration at the target mesh/canonical smoothing order. A first-cell resident or separate nonempty witnesses cannot be reused; absent a same-sample theorem, it must isolate the first honest missing producer rather than declare the cross branch inhabited.
- T623 is independently accepted only as a blocked nonvacuity audit: no admissible producer places one sample in `commonEvent∩transition`; `k=0` is empty, `k=1` is only a sample-independent plateau case, and `k=2` is the first plausible transition prefix. T628 remains read-only pending clean cores and must prove the explicit null `rawCarrier\commonEvent` difference before any positive-mass transfer. T606/T613 remain conditional.
- T602 is accepted after independent correction: the first noncircular post-T596 analytic row is the arbitrary-charge transported initial estimate T608. The raw drift route is circular through `A_u⁻³η_u⁻¹·xiLK₂²`; the domain/index witness at `s_N=0` is explicitly a zero transported-initial probe, not a nonzero-value witness.
- T608 is independently accepted: the transported-initial ratio has exact moment order `2P`, loss `N^(ε/4)`, endpoint normalization `A_v²`, kernel factor `R_{s_N,v}²`, and source `A_{s_N}⁻²`, uniformly over all two-charge words including `(+,+)` and `v=s_N`. Its positive-grid witness is a domain/index witness whose transported value is zero at `s_N=0`; no full T596 family absorption or (2.77) closure is claimed.
- T616 is the selected post-T608 design line for the arbitrary-charge QV ingredient of (2.77): it must preserve the exact (5.42) kernel factor `R_{u,v}^4` and source scale `A_u⁻⁴η_u⁻¹Ψ_E`, derive `Ψ_E` only from the pre-Step-3 `xiL_6` input, cover `v=s_N` and positive mesh points under the same sample, and exclude (2.77), all-charge Step-3 packages, `hfamily`, `APrimeSlot'`, and every first-cell shortcut.
- T604 is independently accepted: full actual-smooth drift integration must first obtain a general-moving all-sample polynomial envelope. The next exact theorem is the fixed-`Dims.exampleGrow`, `sigPM` bound `|driftAt|≤N^(D+8)` for every sample, active cell (including `k=0`) and closed running time; it is not yet the drift integral.
- T611 is independently accepted: for fixed `Dims.exampleGrow` and `sigPM`, `|driftAt|≤N^(D+8)` holds for every sample, every active cell including `k=0`, every output and both closed running-time endpoints. It is only the conservative all-sample pointwise envelope feeding T615, not a drift integral or A-prime closure.
- T605 is rejected after independent audit: the alleged initial-flow seam is already a definitional equality by bare `rfl`, for arbitrary `Dims` and without `hE`/`ht1`. T610 was stopped; no connector file or root import is needed or accepted.

## 3. Running work

| Ticket | State |
|---|---|
| T583 | Delivered; rejected pending T588 signature correction |
| T588 | Rejected: Eq548 existential scope and `D/Kmod` quantifier order are overstated |
| T618 | Rejected: statements correct but transitive imports are downstream/cyclic; upstream core extraction required |
| T619 | Rejected: compiled theorem is mathematically correct but module imports Step45/Step3/Step6; upstream extraction required |
| T624 | Withdrawn: proposed import surface reaches Step345Producer transitively |
| T625/T640 | Independently accepted after correction: nondegenerate witness provenance repaired; T630 classified as bounded/cohesive, not declaration-minimal |
| T626 | Failed independent audit: omitted genuine `LKDecayQuant/EEBridge → SumZeroDyn → Step3` producer paths; Core A remains only a bounded Step45-edge extraction |
| T627 | Independently accepted as blocked: both proposed import branches still reach Step45; no code retained |
| T628 | Independently accepted as blocked: literal `k=2` scalar crossing lies outside `‖Xmat‖≤N`; T633 tests later prefixes |
| T629 | Independently accepted: clean QV-rate and coordinate-weight/global-poly split designs compile; T636 implements the first slice |
| T630 | Independently accepted: 15 declarations preserved in three clean cores; root validation 4037 jobs; no downstream claim |
| T631/T637 | Independently accepted together: generic high-probability core extracted and missing Step6EnvWindow direct import restored; no Step3/QV closure claim |
| T632 | Independently accepted as blocked: omitted `Sample.xiL` dependency identified; prototype reverted; T634 is the corrected extraction |
| T633 | Audit failed on dependencies: scalar mathematics and endpoint obstruction pass, but cited producer surfaces are not clean; T639 corrects the boundary |
| T634 | Independently accepted: six declarations preserved in two clean cores; root validation 4042 jobs; no closure claim |
| T635 | Audit failed on quantifiers: boundary split is valid and assigned as T642, but the conditional QV card must require `s_N≤u≤v≤t_N` (current target also has net membership) |
| T636 | Independently accepted: eight public interfaces preserved in clean drift-time/QV-rate cores; no sharp profile or cross closure claim |
| T638 | Independently accepted as blocked: block-circulant class passes goodSetFlow but cannot meet centeredEvent; T643 tests the general spatial case |
| T639 | Independently accepted: corrected support boundary and selected the minimal target-mesh seam now implemented by T644 |
| T641 | Independently accepted: one-proof `Step2.tT` compatibility repair; root validation 4046 jobs |
| T642 | Independently accepted: two actual Step-3 producers isolated downstream; audited upstream closures no longer reach them |
| T643 | Independently accepted: Ward controls only signed row sums; a coupled-block ansatz passes the deterministic carrier rows, while positive Gaussian support and `measCore` retention remain open |
| T644 | Independently accepted: eight mesh declarations moved verbatim to a zero-project-import core; `targetMesh 60 N=N^258` remains eventual and exact |
| T645 | Independently accepted: clean coordinate-weight and QV global-polynomial cores preserve all nine interfaces and exact polynomial powers |
| T646 | Independently accepted: the clean first-grid witness is noncircular and nondegenerate, with `s_N=0`, eventual `t_N=1/2`, and unchanged (2.72) powers; T651 implements it |
| T647 | Independently accepted: the 49-declaration two-import smooth-prefix/canonical design preserves literal prefix semantics; T652 implements it |
| T648 | Independently accepted: finite nonzero-variance Gaussian cylinders have positive mass, zero-variance coordinates require `zeroFix`, and measurable `U⊆R` retains mass in `U∩measCore`; the global null-difference claim remains false |
| T649 | Independently accepted: the two (2.73) `Step2PP` declarations moved verbatim to a 46-module clean core with exact all-charge closed-window powers |
| T650 | Independent audit failed only on frozen namespace exactness: the QV card passes, but `netFinset*` lives in `RBM.MomentDuhamelCut`; T654 already uses the corrected names |
| T651 | Delivered locally; its clean core and signatures pass, but final facade/root validation waits for coordinated repair of T652's `Step2.lk` compatibility break |
| T652 | Blocked after core/facade extraction: `Eq548Producer` needs one compatibility unfold edit, but T654 currently owns that file; partial work remains excluded until a fresh post-T654 repair |
| T653 | Independently accepted: 12 clean finite-support/local-retention declarations, including zero-variance fixing and nondegenerate singleton witness; root rebuild is blocked only by unrelated T659-owned compatibility work |
| T654 | Stopped with corrected namespace core/facades; final validation is folded into T659 because T652 changed `Step2.lk` in the shared `Eq548Producer` consumer |
| T655 | Delivered; independent audit running on the literal carrier-cylinder boundary and proposed clean predicate extraction; implementation waits for T659 |
| T656 | Running: corrected conditional arbitrary-charge QV/moment-core preflight; no production or closure claim |
| T657 | Running: read-only ownership/build audit for one fresh repair of the entangled T651/T652/T654 partials |
| T658 | Running: exact Gaussian-coordinate encoding audit for the T643 coupled-block deterministic center |
| T659 | Running: coordinated completion of T651/T652/T654 plus the one known definitional compatibility unfold; no new mathematics |
| T660 | Running: scratch-prototype the exact carrier/transition definition core and facade compatibility before any implementation |

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

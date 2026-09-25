# V6 acceptance of T1337/T1338 — 2026-09-24

**Verdict: proved as written**, for the local Gaussian Step-2 composition
under the displayed incoming `BoundsCore` and `Cond272Reg` hypotheses.

The source SHA-256 is
`00cf95b79fd4be4c9164cad8f5d490b9e8bc7dea3d054979a5453b4f75bf0e46`.
Worker task T1337 and independent audit T1338 both ended with final PASS.
V6 read both reports and the complete source, and checked the exact accepted
T1335 slot producer, `jsNormDom_of_aprimeSlot'`, `step1Hyp_slot`, and
`step2_of_jsNormDom` interfaces. Their model, energy, window, loss and
all-D quantifiers match. The positive-window witness retains one T1335 base
carrying the full family premise and the positive-weight common-event resident.
No new unsupported analytic hypothesis is added. The proof is acyclic.

V6 independently ran `lake build RBM1D.Gauss.APrimeFreeLossGaussianStep2`
(exit 0, 4110 jobs), inspected all three public printed axiom outputs, then
point-inserted the import into `RBM1D.lean` and ran `lake build RBM1D`
(exit 0, 9580 jobs). The imported-root audit checked 19660 RBM declarations
against only `propext`, `Classical.choice`, and `Quot.sound`.
Replay logs: `/private/tmp/rbm-v6-T1337-module.log` and
`/private/tmp/rbm-v6-T1337-root.log` (ephemeral diagnostic files).

The prescribed paper's printed p.24 was text-extracted and visually checked.
Formula (2.76) places the floor outside the principal prefactor; the exact
Lean statement places it inside `decayProf`. Temporary delta T1337a records
this distinction, without asserting a separately formalized comparison.

The strongest safe outcome is the actual exampleGrow Gaussian moving local
law and two-loop decay with the literal Lean profile and a joint nondegenerate
window. This does not close the stopped hierarchy, general A′ or a full
bootstrap step. Actual producers and joint witnesses for CutHypEvOnSlot,
all-order Lemma514, Eq45FlowInputs and Eq548EntryDataEvOn' remain open.
Historical T1307/T1308 and other FAIL verdicts are unchanged.

No commit or push was made: the shared tree contains unreviewed historical
dependencies, including the previously rejected T1307 source imported by the
accepted later chain. This ticket's acceptance does not retroactively review
that dependency for publication.

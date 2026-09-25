# V6 acceptance: T1345/T1346 and T1351/T1352

Date: 2026-09-24. Scheduler acceptance after actual worker final PASS,
independent final PASS, direct source/report review, source SHA replay,
individual module builds, imported-root build and root axiom audit.

## T1351/T1352: repair of T1339

T1339/T1340 retain their historical ticket-completion FAIL. T1351 repaired
all four exact T1340 findings in the same existing source; T1352 independently
audited the repair and returned final PASS. The original all-charge xiLK2
modulus remains unchanged. The repaired positive-window witness exports
`BoundsCore` at its quantified `s`; the mesh inequality is explicitly bounded
by `Theta`; `Theta` is positive for every N; and the actual xiLK2 maximum is
nonnegative for every N, real time and sample. The moment field of
`CutHypEvOn` and full cutoff slot remain open.

Accepted source: `RBM1D/Gauss/XiLKTwoCutModulus.lean`, SHA-256
`915b22b299540e95697ffb154e5dba7cdd9f404b7224abc22442c3f115dbb6a8`.
The scheduler's own `lake build RBM1D.Gauss.XiLKTwoCutModulus` passed (3,853
jobs). All ten public printed theorem axioms are within `propext`,
`Classical.choice`, `Quot.sound`. The source has no sorry or declared axiom.
The mathematical paper comparison remains the local auxiliary maximum
modulus at (5.76), in the (2.72) time-window regime.

## T1345/T1346: actual smooth-weight plateau

T1345's actual final PASS and T1346's independent final PASS agree on the
same source SHA. The actual Gaussian canonical smooth weight equals one on
one measurable HighProb finite-net event, for every active cell and every
natural moment order simultaneously. The event uses the accepted T1337
full-time `JSNormDom`; its positive-window witness retains the incoming
`BoundsCore`, an active positive cell, the same actual weight and a
positive-probability intersection with the common source event. This is an
auxiliary same-weight localization input; the sharp moment, its unweighted
transfer and (5.48) remain open.

Accepted source: `RBM1D/Gauss/APrimeActualWeightHighProbPlateau.lean`, SHA-256
`19074865749b8edf516a926280d4af08a5052972fed6685f671c227728a34aa4`.
The scheduler's own `lake build RBM1D.Gauss.APrimeActualWeightHighProbPlateau`
passed (4,111 jobs). All six printed public theorem axioms use only the three
permitted axioms; no sorry or declared axiom occurs.

## Imported-root replay

The scheduler point-inserted the two imports in `RBM1D.lean` after the
already accepted Gaussian Step-2 import. `lake build RBM1D` passed (9,583
jobs), including `#assert_rbm_axioms`: 19,723 `RBM` declarations, all within
`propext`, `Classical.choice`, `Quot.sound`. The corresponding verification
logs are `/private/tmp/rbm-v6-T1345.log` and
`/private/tmp/rbm-v6-root-after-T1351-T1345.log`. No git commit or push was
made. T230A-prime, the stopped hierarchy and the remaining general one-step
inputs stay open.

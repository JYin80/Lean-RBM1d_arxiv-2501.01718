# V6 acceptance — T1367/T1368 generic Gaussian raw-source prerequisite

2026-09-24 UTC. **Accepted only for the arbitrary-`Dims` shared Gaussian raw 3/4/6 source carrier.** T1367 worker final PASS and T1368 independent final PASS are in `T1367.md` and `T1368.md`. Both reviewed source SHA-256 `3af0b207fc42b6758fa8f6da2ab0806631a36d8e3110843e8f3fdd29fe44d97c`; V6 confirmed that exact SHA after the final reports. Report SHAs are `3e488b11a9b54a8a18f47a891e25bd075c1bcbb79c277f650de54ae458a8d5f2` and `b5ae72c942f0d95e1311c3c853415cc006ab18c515165ae78c543921fc201a6d`.

V6 reviewed `RBM1D/Gauss/APrimeRawSourcesGeneralDims.lean` against the accepted fixed source and paper (2.2), (2.73), (5.8). Its generic event uses `Ω d`, `P d` and `sample d`, intersects the norm event with raw orders 3/4/6, is measurable and HighProb under the exact existing `BoundsCore`/`Step1.Hyp`/regime premises, and gives actual `APrimeFullQV.SourceEvent` and raw order three at every running time on the same sample. The endpoint `u=s_N` is explicit. The fixed `exampleGrow` specialization is definitional; the accepted fixed first-cell theorem yields a positive-length same-event resident. The `of_scale` wrapper constructs `Step1.Hyp` from the compiled generic Gaussian producer but remains conditional on its incoming `BoundsCore` and regime data. No generic centered/common event, T615 drift/QV/cross, cutoff or stopped-path result follows from this acceptance.

Scheduler inserted only `import RBM1D.Gauss.APrimeRawSourcesGeneralDims` in `RBM1D.lean`, then independently ran:

- `lake build RBM1D.Gauss.APrimeRawSourcesGeneralDims`: exit 0, 3,907 jobs; public `#print axioms` output for the carrier, scale wrapper, specialization, resident and endpoint lists only `propext`, `Classical.choice`, `Quot.sound`.
- `lake build RBM1D`: exit 0, 9,586 jobs. Root audit checked 19,812 `RBM` declarations and found only those three permitted axioms.

This acceptance preserves the historical T1353–T1366 scope FAILs. The next generic producer must be separately preflighted against existing proofs and independently audited; source generalization cannot be inferred from this raw carrier alone.

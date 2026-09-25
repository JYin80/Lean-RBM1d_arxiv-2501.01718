# V6 acceptance — T1347/T1348 and T1349/T1350

2026-09-24. T1347 and T1349 each delivered a final PASS. Their separately precreated independent audits T1348 and T1350 each returned final PASS. V6 reviewed the four reports and source statements, checked source SHA-256, and replayed the two module builds plus the imported root build together:

- `Lemma514PHalfNonneg.lean`: SHA-256 `4c1ce63238045cddf9426536480460a6c451590306536316e6368baf61d37ede`.
- `Lemma514FirstCellLKDecay.lean`: SHA-256 `9278c104798599333b991a94e1c63b6b46110476a496ed20947fa0e5ef6d33da`.
- `lake build RBM1D.Gauss.Lemma514PHalfNonneg RBM1D.Gauss.Lemma514FirstCellLKDecay RBM1D`: PASS, 9,585 jobs; root axiom audit of 19,779 `RBM` declarations found only `propext`, `Classical.choice`, `Quot.sound`. Each source also prints its public theorem axioms with the same whitelist.

The accepted scope is narrow. T1347 removes the artificial strict-start condition from the guarded Ward/P-half route while retaining `QGood`, lower-order `Lemma514Premises`, and `LKDecay` as inputs. Its joint actual-Gaussian witness has fixed `L=3`; it does not certify growing-dimension spatial decay. T1349 supplies actual all-charge `LKDecay` for `Dims.exampleGrow`, `E=0`, and the whole `[0,1/2]` on one measurable high-probability event, with a nonempty far-pair witness. It does not cover a moving endpoint near one or full Lemma 5.14. Paper anchors: (5.75), (5.87), (5.92), (5.96), (5.101). No paper-wide acceptance follows.

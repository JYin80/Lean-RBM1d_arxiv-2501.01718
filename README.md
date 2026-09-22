# RBM1D

A Lean 4 / Mathlib formalization of the **deterministic core** of

> Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band Matrices*,
> [arXiv:2501.01718](https://arxiv.org/abs/2501.01718).

* **[Blueprint](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/blueprint/)** — the statements and their Lean counterparts
* **[Dependency graph](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/blueprint/dep_graph_document.html)** — green nodes are formalized
* **[Interactive whole-paper map](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/overview/blueprint.html)** — live tasks and proof dependencies
* **[API documentation](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/docs/)**

## Scope

Mathlib currently has no Itô calculus for matrix-valued Brownian motion, no
matrix SDEs and no Dyson Brownian motion, so Sections 2.4, 2.6–2.7 and 5–7 of the
paper cannot presently be formalized.  What *can* be — and what this project
targets — is the deterministic backbone, which is also the paper's original
contribution:

* **Section 2.5 / Appendix B** — the propagator `Θ_ξ = (1 - ξ S^(B))⁻¹`
* **Section 3** — the tree representation of `𝒦`, Ward's identity, the sum-zero
  property

## Status

See [`docs/STATUS.md`](docs/STATUS.md).  Every result currently in the repository
is `sorry`-free; `RBM1D/Test/Sanity.lean` audits that the axiom set stays
`propext`, `Classical.choice`, `Quot.sound`.

Departures from the paper's literal statements (extra hypotheses, corrections)
are logged in [`docs/paper-deltas.md`](docs/paper-deltas.md) rather than applied
silently.

## Building

```bash
lake exe cache get
lake build
```

`./watch.sh` rebuilds on every source change and writes the result to `build.log`.

## Blueprint

```bash
pip install leanblueprint
leanblueprint web        # renders to blueprint/web/
leanblueprint checkdecls # verifies every \lean{...} tag resolves
```

Note that the dependency graph renders through a Web Worker, so it must be served
over HTTP rather than opened as a `file://` URL:

```bash
cd blueprint/web && python3 -m http.server 8000
```

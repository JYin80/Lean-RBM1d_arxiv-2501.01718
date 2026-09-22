---
usemathjax: true
---

A Lean 4 / Mathlib formalization of the deterministic core of

> Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band Matrices*,
> [arXiv:2501.01718](https://arxiv.org/abs/2501.01718).

* [Blueprint](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/blueprint/) — statements, proofs and their Lean counterparts
* [Dependency graph](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/blueprint/dep_graph_document.html) — green nodes are formalized
* [Interactive whole-paper map](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/overview/blueprint.html) — the live task and proof dependency map
* [Blueprint as pdf](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/blueprint.pdf)
* [API documentation](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/docs/)
* [Repository](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718)

## Scope

Mathlib has no Itô calculus for matrix-valued Brownian motion, no matrix SDEs and no
Dyson Brownian motion, so Sections 2.4, 2.6–2.7 and 5–7 of the paper cannot presently
be formalized. What can be — and what this project targets — is the deterministic
backbone, which is also the paper's original contribution: the propagator
$\Theta_\xi = (1 - \xi S^{(B)})^{-1}$ of Section 2.5, and the tree representation of
$\mathcal K$, Ward's identity and the sum-zero property of Section 3.

Everything in the repository is `sorry`-free, and the axiom set of every result is
audited to be exactly `propext`, `Classical.choice`, `Quot.sound`.

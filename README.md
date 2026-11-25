# Single-port graph identification in Lean

This project accompanies *Graph identification from first- and second-order
response in single-port reaction–diffusion systems*, by Mark Gladden. The
[C145 v0.6 manuscript](paper/C145_v0.6.pdf) gives the response model and exact scope.

On a fixed positive horizon, apply a scalar input through a real cyclic port
and observe the same port at the terminal time. Theorem 1 (§2.1, p. 2,
Theorem A in Lean) assumes a source spectral band, port separation and
contraction. Under those conditions, equality of the first and half-mixed
second terminal derivatives at zero in all smooth supported directions
determines the Laplacian and signed port up to one vertex permutation. The admissible competitor can have any finite size. Local
response existence and its local C² dependence are included in the formal claim.
The paper develops the local-response construction in Appendix D (pp. 14–15).

The second comparison identifies **one explicit six-vertex graph** in §10
(pp. 10–11), with literal weights and a fixed signed port at decay one. Its response hypotheses
and terminal derivative data are explicit. It also gives edge-weight
equality when the competitor has zero diagonal weights. The manuscript's
general rooted-six corollary has an analytic proof in Appendix A (p. 12).

The proof library contains all 71 mathematical modules in C145 v0.6, 57 from the main AbPh branch and 14 additional modules for the
explicit six-vertex source. `Challenge.lean` and `Solution.lean` compare
Theorem A, whose dependency closure has 39 modules.
`SixVertexChallenge.lean` and `SixVertexSolution.lean` compare the explicit
case separately. `Audit.lean` is the generated axiom-reporting driver,
outside the proof count.

Use the pinned Lean and Mathlib versions. Run
`lake build` and use separate fresh checkouts for
`lake --json comparator --config comparator.json` and
`lake --json comparator --config comparator-six-vertex.json`. Each
Challenge intentionally contains one theorem hole. The default build
targets the proof library and the two Solution modules. The audit is
available as the separate `Audit` target.

Mark Gladden designed and directed the AbPh research process, including
its catalyst concept, pipeline and prompting, and maintains this release.
OpenAI models developed the mathematics and manuscript and wrote the Lean
proofs. The work was checked by Lean and reviewed by AI models. See
`formalization.yaml` for scope and provenance.

[Validation record](VALIDATION.md) describes the two local Comparator checks and the
separate Lean Pool evidence.

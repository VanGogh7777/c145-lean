# C145 v0.6 validation

Theorem 1 in the manuscript (§2.1, p. 2) is Theorem A in the Lean pilot.
Appendix D (pp. 14–15) supplies the paper's local response construction.
The second target identifies the fixed six-vertex source described in §10.
Appendix A (p. 12) contains the analytic general rooted-six corollary.

The earlier pinned build compiled all 71 mathematical modules with Lean
4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The two local
Comparator runs passed statement matching, the axiom check, and the Lean and
NanoDa kernel checks. The primary configuration is `comparator.json`
(`Challenge.lean` and `Solution.lean`). The separate configuration is
`comparator-six-vertex.json` (`SixVertexChallenge.lean` and `SixVertexSolution.lean`).

Every v0.6 compiler input matches its recorded validated bytes, including
the four Lean 4.36.0 compatibility edits. The companion PDF is the
canonical C145 v0.6 manuscript.

The formatted Lean Pool port has its own local build, lint, signature and
axiom checks and two independently compiled Solution harnesses. The
Comparator outcomes above cover this Palomar proof implementation.

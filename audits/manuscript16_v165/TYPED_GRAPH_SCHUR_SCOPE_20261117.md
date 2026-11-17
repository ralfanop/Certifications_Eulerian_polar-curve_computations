# M16 v16.5 §13 — typed graph-domain Schur reduction

Exact author-approved ZIP SHA-256 4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e.
Exact source section hashes independently verified (16.tex lines 173–1880 and 1881–2055).
Parent main 85b659badb11ef46ced96d54d4bdd68d3b3ae39f.
Extends #330 and #345; neither scalar algebra nor numerical replay is repeated.

The formal target is equation mixed-factor-164 and the solvability reduction
in thm:dirac-maxwell-obstruction-164, with explicit distinct type parameters
D (graph-norm domain), X (ambient), and P (resonant space).
The input L:D ≃L X already incorporates the existence and continuity of
its inverse; B:D →L P is the restriction of the actual ambient B.

| Obligation | This tranche | Remaining |
|---|---|---|
| triangular domain factor | actual continuous linear equivalence on P × D | build concrete D and graph-space inverse of L |
| codomain factor | actual continuous linear equivalence on P × X | instantiate ambient Maxwell/Dirac spaces |
| block factorization | equality of continuous linear maps between distinct types | transfer to concrete block |
| solvability | equivalence of block and Schur equations for arbitrary forcing | Fredholmness, closed range, cokernel, index |
| compactness, Schatten, det4 | not claimed | ideal and determinant theory |

No new floating-point quantities; no Arb claim. Candidate until exact-HEAD
Lean compilation with audited axioms. No manuscript changes or merge.

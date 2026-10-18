# Dirac's theorem on cycles through k vertices in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A finite graph `G` is *`k`-connected* if it has more than `k` vertices and stays connected after
deleting any set of fewer than `k` vertices. All statements are in the namespace `CommonCycle`:

1. `exists_cycle_through`, **Dirac (1960)**. In a `k`-connected finite graph with `k ≥ 2`, any set
   of at most `k` vertices lies on a common cycle.
2. `exists_cycle_through_pair`. In particular, in a 2-connected finite graph any two vertices lie
   on a common cycle.

Cycles are Mathlib's `SimpleGraph.Walk.IsCycle`, and `k`-connectivity is stated directly:
`k < card V` and `(G.induce Sᶜ).Connected` for every vertex set `S` with `S.ncard < k`. Mathlib
does not have this theorem.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`DiracCycleLib/`](DiracCycleLib): the proofs.
- [`MengerHamilton/`](MengerHamilton): Menger's theorem, the fan lemma and the cyclic
  arrangements used for Chvátal–Erdős, reused unchanged from the registered entry
  [PALOMAR-2026-10-15-000020](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000020&version=1)
  ([jtraverso/menger-hamiltonian](https://github.com/jtraverso/menger-hamiltonian) @ b6cf60e).
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

Start from a cycle, which exists by 2-connectivity, and add the required vertices one at a time.
To add a vertex `x` to a cycle `C` through a set `T` of fewer than `k` required vertices, apply
the fan lemma (a consequence of Menger's theorem) to `x` and the vertices of `C`. If `C` has at
most `k` vertices, the fan reaches all of them and two consecutive endpoints give the new cycle.
Otherwise the fan has `k` endpoints on `C`; since `#T < k`, a counting argument gives two fan
endpoints with no vertex of `T` strictly between them along `C`. Splicing the two fan paths into
`C` along that gap produces a cycle through `x` and all of `T`.

## Sources

* G. A. Dirac, *In abstrakten Graphen vorhandene vollständige 4-Graphen und ihre Unterteilungen*,
  Math. Nachr. 22 (1960) 61–85, doi:10.1002/mana.19600220107.

## Authorship and use of AI

The author chose the result. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```

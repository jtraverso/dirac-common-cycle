/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Dirac's theorem: `k` vertices of a `k`-connected graph lie on a common cycle

A finite graph `G` is `k`-connected if it has more than `k` vertices and stays connected after
deleting any set of fewer than `k` vertices (`(G.induce Sᶜ).Connected` for `S.ncard < k`).

* `CommonCycle.exists_cycle_through`: **Dirac (1960).** In a `k`-connected finite graph with
  `k ≥ 2`, any set of at most `k` vertices lies on a common cycle (Mathlib's
  `SimpleGraph.Walk.IsCycle`).
* `CommonCycle.exists_cycle_through_pair`: in particular, in a `2`-connected finite graph any two
  vertices lie on a common cycle.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset SimpleGraph

namespace CommonCycle

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- **Dirac's theorem (1960).** In a `k`-connected finite graph with `k ≥ 2`, any set `S` of at
most `k` vertices lies on a common cycle. -/
theorem exists_cycle_through {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (S : Finset V)
    (hS : #S ≤ k) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support := by
  sorry

/-- In a `2`-connected finite graph, any two vertices lie on a common cycle. -/
theorem exists_cycle_through_pair (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support := by
  sorry

end CommonCycle

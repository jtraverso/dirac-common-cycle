/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import DiracCycleLib.DiracCycle

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `DiracCycleLib/DiracCycle.lean` (namespace `DiracCycle`), reusing
`MengerHamilton/` (the registered entry PALOMAR-2026-10-15-000020, included unchanged): the fan
lemma `exists_fan` (a consequence of Menger's theorem) and the cyclic arrangements `CycArr` used
there for Chvátal–Erdős. Starting from a cycle given by 2-connectivity, the required vertices
are added one at a time by a fan to the current cycle: by a counting argument two fan paths end at
cycle positions with no other required vertex strictly between them, and splicing the fan into
the cycle along that gap keeps every required vertex.
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
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support :=
  DiracCycle.exists_cycle_through G hk hn hconn S hS

/-- In a `2`-connected finite graph, any two vertices lie on a common cycle. -/
theorem exists_cycle_through_pair (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support :=
  DiracCycle.exists_cycle_through_pair G hn hconn a b

end CommonCycle

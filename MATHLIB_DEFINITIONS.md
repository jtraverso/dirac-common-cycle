# Mathlib definitions used by the Dirac cycle statements

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.Walk.support

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 118:

```lean
/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support
```

## SimpleGraph.Walk.darts

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 123:

```lean
/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts
```

## SimpleGraph.Walk.edges

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 129:

```lean
/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge
```

## SimpleGraph.Walk.IsTrail

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 69:

```lean
/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup
```

## SimpleGraph.Walk.IsCircuit

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 79:

```lean
/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends isTrail : IsTrail p where
  ne_nil : p ≠ nil
```

## SimpleGraph.Walk.IsCycle

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 84:

```lean
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup
```

## SimpleGraph.comap

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 126:

```lean
/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`). -/
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm
```

## SimpleGraph.induce

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 227:

```lean
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
```

## SimpleGraph.Reachable

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 52:

```lean
/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
```

## SimpleGraph.Preconnected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 228:

```lean
/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
```

## SimpleGraph.Connected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 314:

```lean
/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
```

## Set.encard

`Mathlib/Data/Set/Card.lean`, line 67:

```lean
/-- The cardinality of a set as a term in `ℕ∞` -/
noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s
```

## Set.ncard

`Mathlib/Data/Set/Card.lean`, line 613:

```lean
/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) : ℕ := ENat.toNat s.encard
```

/-
Copyright (c) 2026 . All rights reserved
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denny Yang
-/

-- Ok why is there such specific warnings for copyright
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-!

ear decompositions

!-/

universe u v w

variable {V : Type u} {V' : Type v}
variable (G : SimpleGraph V) (G' : SimpleGraph V')

def isEar {u v} (w: G.Walk u v) : Prop := w.IsTrail

-- An ear of H ⊆ G is a trail(path/cycle) whose
-- vertices+edges are disjoint from the vertices+edges of H except at the endpoints
def isEarOf {u v} (w : G.Walk u v) (H : G.Subgraph) : Prop :=
  w.IsTrail
  ∧ u ∈ H.verts ∧ v ∈ H.verts
  ∧ ∀ x ∈ w.support, x=u ∨ x=v ∨ x ∉ H.verts
  ∧ ∀ e ∈ w.edges, e∉ H.edgeSet

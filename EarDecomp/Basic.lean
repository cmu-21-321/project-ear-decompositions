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

def AllWalks {V : Type u} (G : SimpleGraph V) : Type _ :=
  Σ (u v : V), G.Walk u v

def generalizeWalk {u v} (w : G.Walk u v) : AllWalks G := ⟨u,v,w⟩

def specifyWalk (w : AllWalks G) : G.Walk w.1 w.2.1 := w.2.2

--TODO, its probably a missing import get Walk.toSubgraph
def WalkToSubgraph {G : SimpleGraph V} (w : AllWalks G) : G.Subgraph := sorry


def isEar {u v} (w: G.Walk u v) : Prop := w.IsTrail

-- An ear of H ⊆ G is a trail(path/cycle) whose
-- vertices+edges are disjoint from the vertices+edges of H except at the endpoints
def isEarOf {u v} (w : G.Walk u v) (H : G.Subgraph) : Prop :=
  w.IsTrail
  ∧ u ∈ H.verts ∧ v ∈ H.verts
  ∧ ∀ x ∈ w.support, x=u ∨ x=v ∨ x ∉ H.verts
  ∧ ∀ e ∈ w.edges, e∉ H.edgeSet

-- checks w is a valid ear to add onto a partial ear decomp
def isEarOf' {u v} {G : SimpleGraph V} (w : G.Walk u v) (n : ℕ) (ears : ℕ → AllWalks G) : Prop :=
  isEarOf G w (⨆ i<n, WalkToSubgraph (ears i))

structure SimpleGraph.partialEarDecomp where
  ears : ℕ → AllWalks G
  eachExtend : ∀ i : ℕ, i>0 → isEarOf' (specifyWalk G (ears i)) (i-1) ears

/-
Copyright (c) 2026 Denny Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denny Yang
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!

ear decompositions for finite graphs

For a finite graph G, an ear decomposition is a sequence
P_0, P_1,... where P_0 is a cycle and P_1,... are ears,
trails whose endpoints are in the previous ears and
whose edges are disjoint from previous ears

Since the graph is finite, the ear decomposition must be finite, so
we represent it with an inductive type.

A graph is two-edge-connected iff it has an ear decomposition
This file proves one direction (<-); it also has some lemmas that
might be useful in proving the other direction. Unfinished proofs
are in FiniteUnfinished.
!-/
public section

variable {V : Type}
variable (G : SimpleGraph V)

-- An ear of H ⊆ G is a path/cycle whose
-- vertices+edges are disjoint from the vertices+edges of H except at the endpoints
def isEarOf {u v} {G : SimpleGraph V} (w : G.Walk u v) (H : G.Subgraph) : Prop :=
  w.IsTrail
  ∧ u ∈ H.verts ∧ v ∈ H.verts
  ∧ (∀ x ∈ w.support, x = u ∨ x = v ∨ x ∉ H.verts)
  ∧ (∀ e ∈ w.edges, e ∉ H.edgeSet)

inductive partialEarDecomp (G : SimpleGraph V) : G.Subgraph → Type where
  | init {u} (w : G.Walk u u) (hw : w.IsCycle) :
      partialEarDecomp G w.toSubgraph
  | extend {H : G.Subgraph} (u v : V) (w : G.Walk u v)
      (d : partialEarDecomp G H) (h : isEarOf w H) :
      partialEarDecomp G (w.toSubgraph ⊔ H)

-- isEarOf with a partialEarDecomp
def isEarOf' {Hd u v} (w : G.Walk u v) (_ : partialEarDecomp G Hd) : Prop :=
  isEarOf w Hd

def isEarDecomp (G : SimpleGraph V) {Hd : G.Subgraph} (_ : partialEarDecomp G Hd) : Prop :=
  G.toSubgraph G (le_rfl) = Hd

lemma partialEarDecomp.two_edge_reachable {G : SimpleGraph V} {Hd : G.Subgraph}
    (d : partialEarDecomp G Hd) :
    ∀ (x y : V) (_ : x ∈ Hd.verts) (_ : y ∈ Hd.verts), G.IsEdgeReachable 2 x y := by
  induction d with
  | init c hc =>
      intro x y hx hy
      change x ∈ c.toSubgraph.verts at hx
      change y ∈ c.toSubgraph.verts at hy
      rw[c.mem_verts_toSubgraph] at hx hy
      have hcTrail : c.IsTrail := hc.isTrail
      apply hcTrail.isEdgeReachable_two hx hy
  | @extend H u v w d h ih =>
      intro x y hx hy
      rcases h with ⟨wIsTrail, uInH, vInH, _⟩
      have huv : G.IsEdgeReachable 2 u v := ih u v uInH vInH
      change x ∈ (w.toSubgraph ⊔ H).verts at hx
      change y ∈ (w.toSubgraph ⊔ H).verts at hy
      simp only [SimpleGraph.Subgraph.verts_sup, SimpleGraph.Walk.verts_toSubgraph, Set.mem_union,
        Set.mem_ofPred_eq] at hx hy
      rcases hx with hxw | hxd
      · rcases hy with hyw | hyd
        · exact wIsTrail.isEdgeReachable_two_of_isEdgeReachable_two huv hxw hyw
        · have xuTwoReachable := wIsTrail.isEdgeReachable_two_of_isEdgeReachable_two
            huv hxw w.start_mem_support
          have uyTwoReachable := ih u y uInH hyd
          exact xuTwoReachable.trans uyTwoReachable
      · rcases hy with hyw | hyd
        · have xuTwoReachable := ih x u hxd uInH
          have uyTwoReachable := wIsTrail.isEdgeReachable_two_of_isEdgeReachable_two
            huv w.start_mem_support hyw
          exact xuTwoReachable.trans uyTwoReachable
        · exact ih x y hxd hyd

--One direction
lemma ear_decomp_implies_edge_conn_two :
    (∃ (Hd : G.Subgraph) (d : partialEarDecomp G Hd) , isEarDecomp G d) → G.IsEdgeConnected 2 := by
  intro h
  rcases h with ⟨Hd, d, h⟩
  intro x y
  apply d.two_edge_reachable
  · unfold isEarDecomp at h
    rw[<-h]
    simp
  · unfold isEarDecomp at h
    rw[<-h]
    simp

-- Lemmas for the other direction
-- Nonempty 2-connected graph has a cycle. Used to get P_0 of an ear decomp.
lemma nonempty_two_edge_conn_has_cycle {G : SimpleGraph V} {e}
    (h : G.IsEdgeConnected 2) (hE : e ∈ G.edgeSet) : ¬G.IsAcyclic  := by
  intro hAcyclic
  have hAllBridge := G.isAcyclic_iff_forall_isBridge.mp hAcyclic
  have hNoBridge := G.isEdgeConnected_two_iff_forall_not_isBridge.mp h
  exact (hNoBridge e) (hAllBridge hE)

def edgeToWalk {u v} (hAdj : G.Adj u v) : G.Walk u v := .cons hAdj .nil

-- One step of the algorithm to make an ear decomposition:
-- edges between vertices already in the ears are valid ears to add
lemma single_edge_walks_are_ears {G : SimpleGraph V} {Hd : G.Subgraph} {u v : V}
  (_ : partialEarDecomp G Hd) (uInHd : u ∈ Hd.verts) (vInHd : v ∈ Hd.verts)
  (hAdj : G.Adj u v) (hNotIn : s(u, v) ∉ Hd.edgeSet) :
  isEarOf (.cons hAdj .nil) Hd := by
  constructor
  · simp
  · constructor
    · assumption
    · constructor
      · assumption
      · constructor
        · intro x xIn
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at xIn
          rcases xIn with isU | isV
          · left; exact isU
          · right; left; exact isV
        · intro e eIn
          simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
            List.not_mem_nil, or_false] at eIn
          rwa [eIn]

lemma partialEarDecomp.nonempty_verts {G : SimpleGraph V} {Hd : G.Subgraph}
    (d : partialEarDecomp G Hd) : ∃ u, u ∈ Hd.verts := by
  induction d with
  | @init u w _ =>
      exact ⟨u, by simp⟩
  | @extend H u v w _ _ ih =>
      rcases ih with ⟨x, hx⟩
      exact ⟨x, Or.inr hx⟩

lemma conn_exists_boundary_edge {G : SimpleGraph V} {H : G.Subgraph} {x w : V}
    (conn : G.Connected) (hx : x ∈ H.verts) (hw : w ∉ H.verts) :
    ∃ u z, u ∈ H.verts ∧ z ∉ H.verts ∧ G.Adj u z := by
  obtain ⟨p, pIsPath⟩ := conn.exists_isPath x w
  induction p with
  | @nil u => exfalso; exact hw hx
  | @cons x y z hxy pyz ih =>
      by_cases hy : y ∈ H.verts
      · apply ih hy hw
        exact SimpleGraph.Walk.IsPath.of_cons pIsPath
      · exact ⟨x, y , hx, hy, hxy⟩

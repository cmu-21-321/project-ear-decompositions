/-
Copyright (c) 2026 Denny Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denny Yang
-/

module

public import EarDecomp.Finite
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks


/-!

Unfinished proofs for ear decompositions of finite graphs.

!-/

variable {V : Type}

-- The other step of the algorithm to make an ear decompositon:
-- for a 2-edge-connected graph, if the ears do not yet include every vertex,
-- we can add an ear that has some new vertex
lemma can_add_vtx_in_two_edge_conn {G Hd} [Nonempty V]
  (twoConn : G.IsEdgeConnected 2) (d : partialEarDecomp G Hd) (hNotAll : ∃ w : V, w ∉ Hd.verts) :
  ∃ (u v : V) (ear : G.Walk u v), (isEarOf ear Hd ∧ ∃ z ∈ ear.support, z ∉ Hd.verts):= by
    obtain ⟨x, xIn⟩ := d.nonempty_verts
    rcases hNotAll with ⟨w, wNotIn⟩
    obtain ⟨u,w,uIn, wNotIn, huv⟩ :=
      conn_exists_boundary_edge (twoConn.connected (by trivial)) xIn wNotIn
    -- Let G' be G minus the edge
    have G'_conn: (G.deleteEdges {s(u,w)}).Connected := by
      have := G.isEdgeConnected_two_iff_forall_preconnected.mp twoConn s(u,w)
      (expose_names; exact { preconnected := this, nonempty := inst })
    obtain ⟨pG', pIsPath⟩ := G'_conn.exists_isPath w u
    have hp : ∀ e ∈ pG'.edges, e ∈ G.edgeSet := by
      intro e he
      have h1 := pG'.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at h1
      exact h1.1
    have hnot' : s(u,w) ∉ pG'.edges := by
      intro he
      have h1 := pG'.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at h1
      exact h1.2 (Set.mem_singleton _)
    obtain ⟨pG, pG_path, pG_edges⟩ :
        ∃ pG : G.Walk w u, pG.IsPath ∧ pG.edges = pG'.edges :=
      ⟨pG'.transfer G hp, pIsPath.transfer hp, by simp⟩
    have hnot : s(u,w) ∉ pG.edges := by
      exact Eq.mpr_not (congrFun (congrArg Membership.mem pG_edges) s(u, w)) hnot'
    -- Here we would "trim" the walk pG until it ends at the first member of Hd.verts
    -- combined with the edge uw, this gives an ear
    -- This proved too complicated for me to do
    -- AI can generate a proof that compiles but it made no sense to me so I'm omitting it
    sorry

theorem edge_conn_two_iff_exists_ear_decomp [Finite V] [Nontrivial V] (G : SimpleGraph V) :
    G.IsEdgeConnected 2 ↔ ∃ (Hd : G.Subgraph) (d : partialEarDecomp G Hd) , isEarDecomp G d := by
  constructor
  · -- Idea : Greedy algorithm: Add edges or add ears with new vertices until unable;
    -- result must include all vertices and edges.

    sorry
  · apply ear_decomp_implies_edge_conn_two

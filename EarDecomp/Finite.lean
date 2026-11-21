module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!

ear decompositions for finite graphs

For a finite graph G, an ear decomposition is a sequence
P_0, P_1,... where P_0 is a cycle and P_1,... are

Since the graph is finite, the ear decomposition must be finite, so
we represent it with an inductive type.
!-/

variable {V : Type} [Fintype V]
variable (G : SimpleGraph V)

def AllWalks {V : Type u} (G : SimpleGraph V) : Type _ :=
  Σ (u v : V), G.Walk u v

def generalizeWalk {u v} (w : G.Walk u v) : AllWalks G := ⟨u,v,w⟩

def specifyWalk {G : SimpleGraph V} (w : AllWalks G) : G.Walk w.1 w.2.1 := w.2.2

def WalkToSubgraph {G : SimpleGraph V} (w : AllWalks G) : G.Subgraph := (specifyWalk w).toSubgraph

-- An ear of H ⊆ G is a path/cycle whose
-- vertices+edges are disjoint from the vertices+edges of H except at the endpoints
def isEarOf {u v} {G : SimpleGraph V} (w : G.Walk u v) (H : G.Subgraph) : Prop :=
  w.IsTrail
  ∧ u ∈ H.verts ∧ v ∈ H.verts
  ∧ ∀ x ∈ w.support, x=u ∨ x=v ∨ x ∉ H.verts
  ∧ ∀ e ∈ w.edges, e∉ H.edgeSet

inductive partialEarDecomp (G : SimpleGraph V) : Type where
  | init {u} (w : G.Walk u u) : w.IsCycle -> partialEarDecomp G
  | extend (u v : V) (w : G.Walk u v) (d : partialEarDecomp G) : partialEarDecomp G

def partialEarDecomp.toSubgraph {G : SimpleGraph V} (d : partialEarDecomp G) : G.Subgraph :=
  match d with
  | partialEarDecomp.init cycle _ => cycle.toSubgraph
  | partialEarDecomp.extend _ _ w d => w.toSubgraph ⊔ d.toSubgraph

-- isEarOf with a partialEarDecomp
def isEarOf' {u v} (w : G.Walk u v) (d : partialEarDecomp G) : Prop :=
  isEarOf w d.toSubgraph

def isEarDecomp (G : SimpleGraph V) (d : partialEarDecomp G) : Prop :=
  G.toSubgraph G (le_rfl) = d.toSubgraph

lemma partialEarDecomp.two_edge_reachable {G : SimpleGraph V} (d : partialEarDecomp G)
    {x y} (hx : x ∈ d.toSubgraph.verts) (hy : y ∈ d.toSubgraph.verts)
    : G.IsEdgeReachable 2 x y := by
  induction d with
  | init c hc =>
      change x ∈ c.toSubgraph.verts at hx
      change y ∈ c.toSubgraph.verts at hy
      rw[c.mem_verts_toSubgraph] at hx hy
      have hcTrail : c.IsTrail := hc.isTrail
      apply hcTrail.isEdgeReachable_two hx hy
  | extend u v w d ih =>
      change x ∈ (w.toSubgraph ⊔ d.toSubgraph).verts at hx
      change y ∈ (w.toSubgraph ⊔ d.toSubgraph).verts at hy
      simp only [SimpleGraph.Subgraph.verts_sup, SimpleGraph.Walk.verts_toSubgraph, Set.mem_union,
        Set.mem_ofPred_eq] at hx hy
      rcases hx with hxw | hxd
      · rcases hy with hyw | hyd
        · sorry
        · sorry
      · rcases hy with hyw | hyd
        · sorry
        · exact ih hxd hyd


theorem edge_conn_two_iff_exists_ear_decomp (G : SimpleGraph V) :
    G.IsEdgeConnected 2 ↔ ∃ d : partialEarDecomp G, isEarDecomp G d := by
  constructor
  · sorry
  · intro h
    rcases h with ⟨d, h⟩
    intro x y
    apply d.two_edge_reachable
    · unfold isEarDecomp at h
      rw[<-h]
      simp
    · unfold isEarDecomp at h
      rw[<-h]
      simp

import graph_theory.basic graph_theory.path
import topology.metric_space.basic
set_option trace.check true

namespace simple_graph
    open walk

    variables {V : Type} (G : simple_graph V) [connected_graph G] (a : V) {x y z : V}

    def dists (x y) := set.range (length : walk G x y -> ℕ)

    lemma dists_ne_empty : (dists G x y).nonempty
        := set.range_nonempty_iff_nonempty.mpr (connected_graph.conn x y)

    noncomputable def dist (x y : V)
        := well_founded.min nat.lt_wf (dists G x y) (dists_ne_empty _)

    lemma upper_bound (p : mypath G x y) : dist G x y <= length p
        := not_lt.mp $ well_founded.not_lt_min _ _ _ (set.mem_range_self p)

    lemma shortest_path (x y) : ∃ p : mypath G x y, length p = dist G x y
        := well_founded.min_mem _ _ (dists_ne_empty _)

    @[simp] lemma dist_self : dist G x x = 0
        := le_antisymm (upper_bound G (nil : walk G x x)) (zero_le _)

    lemma dist_triangle : dist G x z ≤ dist G x y + dist G y z
        := by { choose f g using @shortest_path, rw [<-(g G x y),<-(g G y z),<-length_append],
            exact upper_bound _ _
        }

    lemma eq_of_dist_eq_zero (h : dist G x y = 0) : x = y
        := by { cases shortest_path G x y with p hp, cases p; finish }

    lemma dist_comm' : dist G x y <= dist G y x
        := by { cases shortest_path G y x with p h, rw [<-h, <-length_reverse p], apply upper_bound }

    lemma dist_comm : dist G x y = dist G y x
        := le_antisymm (dist_comm' G) (dist_comm' G)
end simple_graph

noncomputable instance simple_graph.has_dist {V : Type} (G : simple_graph V) [simple_graph.connected_graph G] : has_dist V
    := ⟨λ x y, simple_graph.dist G x y⟩

noncomputable instance simple_graph.metric_space {V : Type} (G : simple_graph V) [simple_graph.connected_graph G] : metric_space V
    :={ dist_self          := by { unfold dist, norm_cast, apply simple_graph.dist_self },
        eq_of_dist_eq_zero := by { unfold dist, norm_cast, apply simple_graph.eq_of_dist_eq_zero },
        dist_comm          := by { unfold dist, norm_cast, apply simple_graph.dist_comm },
        dist_triangle      := by { unfold dist, norm_cast, apply simple_graph.dist_triangle } }

import graph_theory.basic graph_theory.path
import topology.metric_space.basic
set_option trace.check true

namespace Graph
    variables {V : Type} (G : Graph V) [connected_graph G] (a : V) {x y z : V}

    def dists (x y) := set.range (path.size : path G x y -> ℕ)

    lemma dists_ne_empty : (dists G x y).nonempty
        := set.range_nonempty_iff_nonempty.mpr (path.nonempty G)

    noncomputable def dist (x y : V)
        := well_founded.min nat.lt_wf (dists G x y) (dists_ne_empty _)

    lemma upper_bound (p : path G x y) : dist G x y <= p.size
        := not_lt.mp $ well_founded.not_lt_min _ _ _ (set.mem_range_self p)

    lemma shortest_path (x y) : ∃ p : path G x y, p.size = dist G x y
        := well_founded.min_mem _ _ (dists_ne_empty _)

    @[simp] lemma dist_self : dist G x x = 0
        := le_antisymm (upper_bound G (path.point G x)) (zero_le _)

    lemma dist_triangle : dist G x z ≤ dist G x y + dist G y z
        := by { choose f g using @shortest_path, rw [<-(g G x y),<-(g G y z),<-path.size_concat],
            exact upper_bound _ _
        }

    lemma eq_of_dist_eq_zero : dist G x y = 0 -> x = y
        := by { intro h0, rcases (shortest_path G x y) with ⟨⟨⟨_|_,rfl,rfl⟩,_⟩,h⟩,
            { refl }, { rw h0 at h, cases h } }

    lemma dist_comm' : dist G x y <= dist G y x
    := begin
        cases shortest_path G y x with p h, rw <-h,
        have : (p.rev G).size = p.size := path.size_rev _, rw <-this,
        apply upper_bound
    end

    lemma dist_comm : dist G x y = dist G y x
        := le_antisymm (dist_comm' G) (dist_comm' G)
end Graph

noncomputable instance Graph.has_dist {V : Type} (G : Graph V) [Graph.connected_graph G] : has_dist V
    := ⟨λ x y, Graph.dist G x y⟩

noncomputable instance Graph.metric_space {V : Type} (G : Graph V) [Graph.connected_graph G] : metric_space V
    :={ dist_self          := by { unfold dist, norm_cast, apply Graph.dist_self },
        eq_of_dist_eq_zero := by { unfold dist, norm_cast, apply Graph.eq_of_dist_eq_zero },
        dist_comm          := by { unfold dist, norm_cast, apply Graph.dist_comm },
        dist_triangle      := by { unfold dist, norm_cast, apply Graph.dist_triangle } }

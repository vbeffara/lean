import graph_theory.basic graph_theory.path
import topology.metric_space.basic
set_option trace.check true

namespace graph
    variables {G : Graph} [connected_graph G] (a : G) {x y z : G}

    def dists (x y) := set.range (path.size : path G x y -> ℕ)

    lemma dists_ne_empty : (dists x y).nonempty
        := set.range_nonempty_iff_nonempty.mpr path.nonempty

    noncomputable def dist (x y : G)
        := well_founded.min nat.lt_wf (dists x y) dists_ne_empty

    lemma upper_bound (p : path G x y) : dist x y <= p.size
        := not_lt.mp $ well_founded.not_lt_min _ _ _ (set.mem_range_self p)
            
    lemma shortest_path (x y) : ∃ p : path G x y, p.size = dist x y
        := well_founded.min_mem _ _ dists_ne_empty

    @[simp] lemma dist_self : dist x x = 0
        := le_antisymm (upper_bound (path.point x)) (zero_le _)

    lemma dist_triangle : dist x z ≤ dist x y + dist y z 
        := by { choose f g using @shortest_path, rw [<-(g x y),<-(g y z),<-path.size_concat],
            exact upper_bound _
        }

    lemma eq_of_dist_eq_zero : dist x y = 0 -> x = y
        := by { intro h0, rcases (shortest_path x y) with ⟨⟨⟨_|_,rfl,rfl⟩,_⟩,h⟩,
            { refl }, { rw h0 at h, cases h } }

    lemma dist_comm' : dist x y <= dist y x
        := Exists.cases_on (shortest_path y x) (λ p h, eq.trans path.size_rev h ▸ upper_bound p.rev)

    lemma dist_comm : dist x y = dist y x
        := le_antisymm dist_comm' dist_comm'
end graph

noncomputable instance graph.has_dist (G : Graph) [connected_graph G] : has_dist G := ⟨λ x y, graph.dist x y⟩

noncomputable instance graph.metric_space (G : Graph) [connected_graph G] : metric_space G
    :={ dist_self          := by { unfold dist, norm_cast, apply graph.dist_self },
        eq_of_dist_eq_zero := by { unfold dist, norm_cast, apply graph.eq_of_dist_eq_zero },
        dist_comm          := by { unfold dist, norm_cast, apply graph.dist_comm },
        dist_triangle      := by { unfold dist, norm_cast, apply graph.dist_triangle } }
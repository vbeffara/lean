import graph_theory.basic graph_theory.path
import topology.metric_space.basic

namespace graph section
    parameters {G : Graph} [connected_graph G]
    variables (a : G) {x y z : G}

    def dists (x y) := set.range (sizeof : path G x y -> ℕ)

    lemma dists_ne_empty : dists x y ≠ ∅
        := nonempty.dcases_on (path.to_path (connected_graph.conn G x y))
            (λ p, set.ne_empty_of_mem (set.mem_range_self p))

    noncomputable def dist (x y : G)
        := well_founded.min nat.lt_wf (dists x y) dists_ne_empty

    lemma upper_bound (p : path G x y) : dist x y <= sizeof p
        := not_lt.mp $ well_founded.not_lt_min nat.lt_wf (dists x y) dists_ne_empty (set.mem_range_self p)
            
    lemma shortest_path (x y) : ∃ p : path G x y, sizeof p = dist x y
        := well_founded.min_mem nat.lt_wf (dists x y) dists_ne_empty

    lemma dist_self : dist x x = 0
        := le_zero_iff_eq.mp (upper_bound (path.point x))

    lemma dist_self' { h : x = y } : dist x y = 0 
        := eq.rec dist_self h

    lemma dist_triangle : dist x z ≤ dist x y + dist y z 
        := by { obtain pxy := shortest_path x y, obtain pyz := shortest_path y z, 
            have h1 : sizeof (path.concat pxy pyz) = sizeof pxy + sizeof pyz := llist.concat_size,
            rw [<-h,<-h_1,<-h1], apply upper_bound }

    lemma eq_of_dist_eq_zero : dist x y = 0 -> x = y
        := by { intro h2, rcases (shortest_path x y) with ⟨⟨⟨l,hx,hy⟩,hp⟩,h⟩,
            cases l, { rw [<-hx,<-hy], refl }, { rw h2 at h, cases h } }

    lemma dist_comm : dist x y = dist y x
        := by { have : ∀ u v : G, dist u v <= dist v u,
            { intros, obtain p := shortest_path v u, rw [<-h,<-path.sizeof_rev], exact upper_bound p.rev },
            exact le_antisymm (this x y) (this y x) }
end end graph

noncomputable instance graph.has_dist (G : Graph) [connected_graph G] : has_dist G := ⟨λ x y, graph.dist x y⟩

noncomputable instance graph.metric_space (G : Graph) [connected_graph G] : metric_space G
    :={ dist_self          := by { unfold dist, norm_cast, apply graph.dist_self },
        eq_of_dist_eq_zero := by { unfold dist, norm_cast, apply graph.eq_of_dist_eq_zero },
        dist_comm          := by { unfold dist, norm_cast, apply graph.dist_comm },
        dist_triangle      := by { unfold dist, norm_cast, apply graph.dist_triangle } }
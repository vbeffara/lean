import graph_theory.basic graph_theory.path
import topology.metric_space.basic

namespace dist section
    parameters {G : Graph} [connected_graph G]
    variables {x y z : G}

    def dists (x y) := set.range (sizeof : path G x y -> ℕ)

    lemma dists_ne_empty : dists x y ≠ ∅
        := nonempty.dcases_on (path.to_path (connected_graph.conn G x y))
            (λ p, set.ne_empty_of_mem (set.mem_range_self p))

    noncomputable def graph_dist (x y : G)
        := well_founded.min nat.lt_wf (dists x y) dists_ne_empty

    noncomputable instance : has_dist G := ⟨λ x y, graph_dist x y⟩

    lemma shortest_path (x y) : ∃ p : path G x y, sizeof p = graph_dist x y
        := well_founded.min_mem nat.lt_wf (dists x y) dists_ne_empty

    lemma upper_bound (p : path G x y) : graph_dist x y <= sizeof p
        := not_lt.mp $ well_founded.not_lt_min nat.lt_wf (dists x y) dists_ne_empty (set.mem_range_self p)
            
    lemma dist_self : dist x x = 0
        := by { unfold dist, norm_cast, exact le_zero_iff_eq.mp (upper_bound (path.point x)) }

    lemma eq_of_dist_eq_zero : dist x y = 0 → x = y
        := by { unfold dist, norm_cast, intro h2, obtain p := shortest_path x y,
            rcases p with ⟨⟨l,hx,hy⟩,hp⟩, cases l, rw [<-hx,<-hy], refl, rw h2 at h, cases h }

    lemma dist_comm : dist x y = dist y x
        := by { unfold dist, norm_cast, have : ∀ u v : G, graph_dist u v <= graph_dist v u,
            { intros, obtain p := shortest_path v u, rw [<-h,<-path.sizeof_rev], exact upper_bound p.rev },
            exact le_antisymm (this x y) (this y x) }

    lemma dist_triangle : dist x z ≤ dist x y + dist y z 
        := by { unfold dist, norm_cast, obtain pxy := shortest_path x y, obtain pyz := shortest_path y z, 
            have h1 : sizeof (path.concat pxy pyz) = sizeof pxy + sizeof pyz := llist.concat_size,
            rw [<-h,<-h_1,<-h1], apply upper_bound }

    noncomputable instance : metric_space G
        :={ dist               := λ x y, graph_dist x y,
            dist_self          := λ x, dist_self,
            eq_of_dist_eq_zero := λ x y, eq_of_dist_eq_zero,
            dist_comm          := λ x y, dist_comm,
            dist_triangle      := λ x y z, dist_triangle }
end end dist
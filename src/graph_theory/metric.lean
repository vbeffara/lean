import graph_theory.basic graph_theory.path
import topology.metric_space.basic

namespace dist section
    class connected_graph (G : Graph) := (conn : connected G)

    parameters {G : Graph} [connected_graph G]
    variables {x y z : G}

    def dists   (x y : G) := set.range (sizeof : path G x y -> ℕ)

    lemma l1 : dists x y ≠ ∅
        := by { obtain p := path.to_path (connected_graph.conn G x y),
            exact set.ne_empty_of_mem (set.mem_range_self p) }

    noncomputable def graph_dist (x y : G)
        := well_founded.min nat.lt_wf (dists x y) l1

    lemma l3 : graph_dist x y ∈ dists x y
        := well_founded.min_mem nat.lt_wf (dists x y) l1

    lemma l5 {n} : n ∈ dists x y -> graph_dist x y <= n
        := λ h, not_lt.mp (well_founded.not_lt_min nat.lt_wf (dists x y) l1 h)

    lemma l4 (p : path G x y) : graph_dist x y <= sizeof p
        := l5 (set.mem_range_self p)

    lemma l6 (x y) : ∃ p : path G x y, sizeof p = graph_dist x y
        := l3

    noncomputable instance : has_dist G := ⟨λ x y, graph_dist x y⟩

    lemma l2 {x y n} : graph_dist x y <= n <-> ∃ p : path G x y, sizeof p <= n
        := by { split, 
            { intro h, obtain p := @l6 _ _ x y, use p, rw h_1, exact h },
            { intro h, obtain p := h, transitivity (sizeof p), exact l4 p, exact h_h } }

    lemma dist_self : dist x x = 0
        := by { unfold dist, norm_cast, exact le_zero_iff_eq.mp (l4 (path.point x)) }

    lemma eq_of_dist_eq_zero : dist x y = 0 → x = y
        := by { unfold dist, norm_cast, intro h2, obtain p := l6 x y, rw h2 at h,
            rcases p with ⟨⟨l,hx,hy⟩,hp⟩, cases l, rw [<-hx,<-hy], refl, cases h }

    lemma dist_comm : dist x y = dist y x
        := by { unfold dist, norm_cast,
            have : ∀ x y : G, graph_dist x y <= graph_dist y x,
                { intros x y, obtain p := l6 y x, rw [<-h,<-path.sizeof_rev], exact l4 p.rev },
            exact le_antisymm (this x y) (this y x) }

    lemma dist_triangle : dist x z ≤ dist x y + dist y z 
        := by { unfold dist, norm_cast, obtain pxy := l6 x y, obtain pyz := l6 y z, 
            have h1 : sizeof (path.concat pxy pyz) = sizeof pxy + sizeof pyz := llist.concat_size,
            rw [<-h,<-h_1,<-h1], apply l4 }

    noncomputable instance : metric_space G
        :={ dist               := λ x y, graph_dist x y,
            dist_self          := λ x, dist_self,
            eq_of_dist_eq_zero := λ x y, eq_of_dist_eq_zero,
            dist_comm          := λ x y, dist_comm,
            dist_triangle      := λ x y z, dist_triangle }
end end dist
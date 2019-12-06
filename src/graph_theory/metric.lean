import graph_theory.basic graph_theory.path
import topology.metric_space.basic

namespace dist section
    class connected_graph (G : Graph) := (conn : connected G)

    parameters {G : Graph} [connected_graph G]
    variables {x y : G}

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

    lemma dist_self_0 {x : G} : 0 ∈ dists x x
        := exists.intro (path.point x) rfl

    noncomputable instance : metric_space G
        :={ dist := λ x y, graph_dist x y,
            -- 
            dist_self := by { intro x, let p := path.point x, 
                have h1 : graph_dist x x <= sizeof p := l4 p,
                have h4 : graph_dist x x = 0 := le_zero_iff_eq.mp h1,
                unfold dist, rw h4, refl },
            --
            eq_of_dist_eq_zero := by { intros x y h1, 
                have h2 : graph_dist x y = 0, { unfold dist at h1, finish },
                obtain p := l6 x y, rw h2 at h,
                rcases p with ⟨⟨l,hx,hy⟩,hp⟩, cases l, simp [llist.head,llist.last] at hx hy, cc, cases h },
            --
            dist_comm := by { suffices : ∀ x y : G, dist x y <= dist y x,
                    { intros, have h1 := this x y, have h2 := this y x, exact le_antisymm h1 h2 },
                intros, unfold dist, obtain p := l6 y x, rw <-h, let p' := p.rev, 
                have h1 := l4 p', rw <-path.sizeof_rev, finish },
            --
            dist_triangle := by { intros, obtain pxy := l6 x y, obtain pyz := l6 y z, 
                let p := path.concat pxy pyz,
                have h1 : sizeof p = sizeof pxy + sizeof pyz := llist.concat_size,
                have h2 : graph_dist x z <= graph_dist x y + graph_dist y z, 
                    { rw [<-h,<-h_1,<-h1], apply l4 },
                unfold dist, norm_cast, exact h2 } }
end end dist

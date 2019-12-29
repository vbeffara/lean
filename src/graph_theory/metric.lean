import graph_theory.basic graph_theory.path
import topology.metric_space.basic
set_option trace.check true

namespace graph section
    parameters {G : Graph} [connected_graph G]
    variables (a : G) {x y z : G}

    def dists (x y) := set.range (path.size : path G x y -> ℕ)

    lemma dists_ne_empty : dists x y ≠ ∅
        := set.range_ne_empty _

    noncomputable def dist (x y : G)
        := well_founded.min nat.lt_wf (dists x y) dists_ne_empty

    lemma upper_bound (p : path G x y) : dist x y <= p.size
        := not_lt.mp $ well_founded.not_lt_min nat.lt_wf (dists x y) dists_ne_empty (set.mem_range_self p)
            
    lemma shortest_path (x y) : ∃ p : path G x y, p.size = dist x y
        := well_founded.min_mem nat.lt_wf (dists x y) dists_ne_empty

    @[simp] lemma dist_self : dist x x = 0
        := le_zero_iff_eq.mp (upper_bound (path.point x))

    lemma dist_self' (h : x = y) : dist x y = 0 
        := eq.rec dist_self h

    lemma dist_triangle : dist x z ≤ dist x y + dist y z 
        := Exists.cases_on (shortest_path x y) (λ pxy hxy, 
            Exists.cases_on (shortest_path y z) (λ pyz hyz, 
                hyz ▸ hxy ▸ eq.mpr
                    (congr (congr_arg (<=) (eq.refl (dist x z))) llist.concat_size.symm)
                    (upper_bound (path.concat pxy pyz))))

    lemma eq_of_dist_eq_zero : dist x y = 0 -> x = y
        := by { intro h0, rcases (shortest_path x y) with ⟨⟨⟨l,hx,hy⟩,hp⟩,h⟩,
            cases l, { rw [<-hx,<-hy], refl }, { rw h0 at h, cases h } }

    lemma dist_comm' : dist x y <= dist y x
        := Exists.cases_on (shortest_path y x) (λ p h, eq.trans path.size_rev h ▸ upper_bound p.rev)

    lemma dist_comm : dist x y = dist y x
        := le_antisymm dist_comm' dist_comm'
end end graph

noncomputable instance graph.has_dist (G : Graph) [connected_graph G] : has_dist G := ⟨λ x y, graph.dist x y⟩

noncomputable instance graph.metric_space (G : Graph) [connected_graph G] : metric_space G
    :={ dist_self          := by { unfold dist, norm_cast, apply graph.dist_self },
        eq_of_dist_eq_zero := by { unfold dist, norm_cast, apply graph.eq_of_dist_eq_zero },
        dist_comm          := by { unfold dist, norm_cast, apply graph.dist_comm },
        dist_triangle      := by { unfold dist, norm_cast, apply graph.dist_triangle } }
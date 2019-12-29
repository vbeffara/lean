import tactic group_theory.subgroup
import graph_theory.path graph_theory.metric topology.metric_space.lipschitz

namespace cayley section
    structure genset (G : Type) [group G] :=
        (els : finset G)
        (sym : ∀ {s : G}, s ∈ els -> s⁻¹ ∈ els)
        (gen : group.closure els.to_set = set.univ)
        (nem : els ≠ ∅)

    parameters {G : Type} [group G] (S : genset G)
    variables (a : G) {x y z : G}

    instance : has_coe (genset G) (finset G) := ⟨λ S, S.els⟩
    instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩
    
    def adj (x y : G) := x⁻¹ * y ∈ S

    lemma cancel {x y a : G} : (a * x)⁻¹ * (a * y) = x⁻¹ * y 
        := by { simp [mul_assoc] }

    lemma inv_prod {x y : G} : (x⁻¹ * y)⁻¹ = y⁻¹ * x 
        := by { simp }

    lemma shift_adj {a x y : G} : adj x y -> adj (a*x) (a*y) 
        := by { rw [adj,adj,cancel], tauto }

    @[symm] lemma adj_symm {x y} : adj x y -> adj y x
        := by { rw [adj,adj], rw <-(@inv_prod _ _ x y), apply S.sym }

    def Cay : Graph := { V := G, adj := adj, sym := @adj_symm }
    
    def shift_llist := llist.map ((*) a)

    lemma shift_is_path {l : llist G} : llist.is_path adj l -> llist.is_path adj (shift_llist a l)
        := by { intro h, induction l with v v l hr, trivial,
            refine ⟨_, hr h.2⟩, rw [llist.head_map], exact shift_adj S h.1 }

    def shift_path (p : path Cay x y) : path Cay (a*x : G) (a*y : G)
        := { l := shift_llist a p.l,
            hx := by { rw [shift_llist,llist.head_map,p.hx] },
            hy := by { rw [shift_llist,llist.last_map,p.hy] },
            adj := shift_is_path _ p.adj }

    lemma shift : linked Cay x y -> linked Cay (a*x : G) (a*y : G)
        := by { intro h, induction h with b c hxb hbc hr, refl,
            exact linked.tail hr (shift_adj S hbc) }

    lemma inv : linked Cay (1:G) x -> linked Cay (1:G) (x⁻¹:G)
        := by { intro h, symmetry, convert shift S x⁻¹ h; simp }

    lemma linked_mp : linked Cay (1:G) x
        := by { have h : x ∈ group.closure S.els.to_set := S.gen.symm ▸ set.mem_univ x, induction h,
            case group.in_closure.basic : s { apply linked.edge, change 1⁻¹ * s ∈ S, rwa [one_inv,one_mul] },
            case group.in_closure.one   : { refl },
            case group.in_closure.inv   : _ _ h1y { exact inv S h1y },
            case group.in_closure.mul   : y _ _ _ h1y h1z { 
                refine linked.trans h1y _, convert shift S y h1z, rw mul_one } }
            
    theorem connected : connected Cay
        := by { suffices : ∀ x, linked (Cay S) (1:G) x,
                { intros x y, transitivity (1:G), symmetry, apply this, apply this },
            intro, apply linked_mp }

    instance : connected_graph Cay := ⟨connected⟩

    noncomputable def word_dist : G -> G -> ℕ := @graph.dist Cay _

    lemma covariant : word_dist (a*x) (a*y) = word_dist x y
        := by { 
            unfold word_dist graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
            let dists : G -> G -> set ℕ := @graph.dists (Cay S) _,
            have h2 : ∀ x y a ℓ, dists x y ℓ -> dists (a*x) (a*y) ℓ 
                := by { intros x y a ℓ h, cases h with p, use ⟨shift_path S a p, h_h ▸ llist.size_map⟩ },
            exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                h2 x y a ℓ⟩ }
end end cayley

namespace cayley section
    parameters {G : Type} [group G] (S1 S2 : genset G)
    open finset

    lemma lipschitz : ∃ K : ℕ, ∀ x y : G, word_dist S2 x y <= K * word_dist S1 x y
        := by { obtain K := max_of_ne_empty (mt image_eq_empty.1 S1.nem), use K, 
            intros x y, obtain ⟨⟨⟨l,hx,hy⟩,hp⟩,h⟩ := @graph.shortest_path (Cay S1) _ x y, 
            unfold word_dist, rw <-h, clear h, revert x y, induction l; intros,
                { subst hx, subst hy, simp },
                { let z : G := llist.head l_a_1,
                    transitivity word_dist S2 x z + word_dist S2 z y, { exact graph.dist_triangle },
                    rw [path.size,llist.size,mul_add,add_comm,mul_one],
                    apply add_le_add (l_ih z y rfl hy hp.2), rw [<-(covariant S2 x⁻¹),inv_mul_self], 
                    refine le_max_of_mem (mem_image_of_mem _ _) h, exact (hx ▸ hp.1) } }

    def id_S : Cay S1 -> Cay S2 := id

    theorem bilipschitz : ∃ K, lipschitz_with K id_S
        := by { cases lipschitz S1 S2 with K h, use K,
            intros x y, unfold dist, rw [nnreal.coe_nat_cast], norm_cast, apply h }
end end cayley
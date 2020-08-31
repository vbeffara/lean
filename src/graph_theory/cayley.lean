import tactic group_theory.subgroup
import graph_theory.path graph_theory.metric topology.metric_space.lipschitz

namespace Graph
    namespace cayley
        structure genset (G : Type) [group G] :=
            (els : finset G)
            (sym : ∀ {s : G}, s ∈ els -> s⁻¹ ∈ els)
            (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
            (nem : els.nonempty)

        variables {G : Type} [group G] (S : genset G) (a : G) {x y z : G}

        instance : has_coe (genset G) (finset G) := ⟨λ S, S.els⟩
        instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩
        
        def adj (x y : G) := x⁻¹ * y ∈ S

        @[simp] lemma cancel {x y a : G} : (a * x)⁻¹ * (a * y) = x⁻¹ * y 
            := by { simp [mul_assoc] }

        lemma inv_prod {x y : G} : (x⁻¹ * y)⁻¹ = y⁻¹ * x 
            := by { simp }

        lemma shift_adj {a x y : G} : adj S x y -> adj S (a*x) (a*y) 
            := by { rw [adj,adj,cancel], tauto }

        @[symm] lemma adj_symm {x y} : adj S x y -> adj S y x
            := by { rw [adj,adj], rw <-(@inv_prod _ _ x y), apply S.sym }

        def Cay (S : genset G) := G

        instance : group (Cay S) := by { exact _inst_1 }
        instance : Graph (Cay S) := { adj := adj S, sym := @adj_symm _ _ S }
        
        def shift_llist : llist G -> llist G := llist.map (λ v, a * v)

        lemma shift_is_path {l : llist G} (h : llist.is_path (adj S) l) : llist.is_path (adj S) (shift_llist a l)
            := by { induction l with v v l hr, trivial,
                refine ⟨_, hr h.2⟩, rw [llist.head_map], exact shift_adj S h.1 }

        def shift_path (p : path (Cay S) x y) : path (Cay S) (a*x : G) (a*y : G)
            := { l := @shift_llist _ _ a p.l,
                hx := by { rw [shift_llist,llist.head_map,p.hx] },
                hy := by { rw [shift_llist,llist.last_map,p.hy] },
                adj := shift_is_path _ _ p.adj }

        lemma shift : linked (Cay S) x y -> linked (Cay S) (a*x : G) (a*y : G)
            := by { intro h, induction h with b c hxb hbc hr, refl,
                exact linked.tail _ hr (shift_adj S hbc) }

        lemma inv : linked (Cay S) (1:G) x -> linked (Cay S) (1:G) (x⁻¹:G)
            := by { intro h, symmetry, convert shift S x⁻¹ h; simp }

        lemma linked_mp : linked (Cay S) (1:G) x
        := begin
            have h : x ∈ subgroup.closure (coe S.els) := by { rw S.gen, trivial },
            apply subgroup.closure_induction,
            { exact h, },
            { intros, apply linked.edge (Cay S), change 1⁻¹ * x_1 ∈ S, rwa [one_inv,one_mul] },
            { refl },
            { intros, refine linked.trans _ a _, convert shift _ x_1 a_1, rw mul_one, },
            { intros, apply inv, exact a },
        end
                
        theorem connected : connected (Cay S)
            := by { suffices : ∀ x, linked (Cay S) (1:G) x,
                    { intros x y, transitivity (1:G), symmetry, apply this, apply this },
                intro, apply linked_mp }

        instance : connected_graph (Cay S) := ⟨connected S⟩

        noncomputable def word_dist : G -> G -> ℕ := @Graph.dist (Cay S) _ _

        lemma covariant : word_dist S (a*x) (a*y) = word_dist S x y
            := by { unfold word_dist Graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
                let dists : G -> G -> set ℕ := @dists (Cay S) _ _,
                have h2 : ∀ x y a ℓ, dists x y ℓ -> dists (a*x) (a*y) ℓ 
                    := by { intros x y a ℓ h, cases h with p, use ⟨shift_path S a p, h_h ▸ llist.size_map⟩ },
                exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                    h2 x y a ℓ⟩ }
    end cayley

    namespace cayley
        variables {G : Type} [group G] (S1 S2 : genset G)
        open finset

        lemma lipschitz : ∃ K : ℕ, ∀ x y : G, word_dist S2 x y <= K * word_dist S1 x y
            := by { obtain K := max_of_nonempty (nonempty.image S1.nem _), cases K, use K_w, 
                intros x y, obtain ⟨⟨⟨l,rfl,rfl⟩,hp⟩,h⟩ := Graph.shortest_path (Cay S1) x y, 
                unfold word_dist, rw <-h, clear h, induction l; intros, simp,
                { let z : G := llist.head l_a_1,
                    transitivity word_dist S2 l_a z + word_dist S2 z l_a_1.last, { exact Graph.dist_triangle _ },
                    rw [path.size,llist.size,mul_add,add_comm,mul_one],
                    apply add_le_add (l_ih hp.2), rw [<-(covariant S2 l_a⁻¹),inv_mul_self], 
                    refine le_max_of_mem (mem_image_of_mem _ _) K_h, exact hp.1 } }

        def id_S : Cay S1 -> Cay S2 := id

        theorem bilipschitz : ∃ K, lipschitz_with K (id_S S1 S2)
            := by { cases lipschitz S1 S2 with K h, use K, 
                rw lipschitz_with_iff_dist_le_mul,
                simp only [id_S,id,has_dist.dist], 
                norm_cast, exact h }
    end cayley
end Graph

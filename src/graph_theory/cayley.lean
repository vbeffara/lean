import tactic group_theory.subgroup
import graph_theory.path graph_theory.metric

namespace cayley section
    class genset {G : Type} [group G] (S : finset G) := 
        (sym : ∀ {s : G}, s ∈ S -> s⁻¹ ∈ S)
        (gen : group.closure S.to_set = set.univ)
        (nem : S ≠ ∅)

    parameters {G : Type} [group G] (S : finset G) [genset S]
    variables (a : G) {x y z : G}
    
    def adj (x y : G) := x⁻¹ * y ∈ S

    lemma cancel {x y a : G} : (a * x)⁻¹ * (a * y) = x⁻¹ * y 
        := by { rw [mul_inv_rev,<-mul_assoc], simp }

    lemma inv_prod {x y : G} : (x⁻¹ * y)⁻¹ = y⁻¹ * x 
        := by { simp }

    lemma shift_adj {a x y : G} : adj x y -> adj (a*x) (a*y) 
        := by { rw [adj,adj,cancel], exact id }

    @[symm] lemma adj_symm {x y} : adj x y -> adj y x
        := by { rw [adj,adj], rw <-(@inv_prod _ _ x y), exact genset.sym }

    def span : Graph := { V := G, adj := adj, sym := @adj_symm }
    
    def shift_llist := llist.map ((*) a)

    lemma shift_is_path {l : llist G} : llist.is_path adj l -> llist.is_path adj (shift_llist a l)
        := by { intro h, induction l with v v l hr, trivial,
            refine ⟨_, hr h.2⟩, rw [llist.head_map], exact shift_adj S h.1 }

    def shift_path (p : path span x y) : path span (a*x : G) (a*y : G)
        := { l := shift_llist a p.l,
            hx := by { rw [shift_llist,llist.head_map,p.hx] },
            hy := by { rw [shift_llist,llist.last_map,p.hy] },
            adj := shift_is_path _ p.adj }

    lemma shift : linked span x y -> linked span (a*x : G) (a*y : G)
        := by { intro h, induction h with b c hxb hbc hr, refl,
            exact linked.tail hr (shift_adj S hbc) }

    lemma inv : linked span (1:G) x -> linked span (1:G) (x⁻¹:G)
        := by { intro h, symmetry, convert shift S x⁻¹ h, rw mul_one, rw mul_left_inv }

    lemma linked_mp : linked span (1:G) x
        := by { have h : x ∈ group.closure S.to_set, { rw genset.gen, trivial }, induction h,
            case group.in_closure.basic : s hs { apply linked.edge, change 1⁻¹ * s ∈ S, rwa [one_inv,one_mul] },
            case group.in_closure.one   : { refl },
            case group.in_closure.inv   : y hy h1y { exact inv S h1y },
            case group.in_closure.mul   : y z _ _ h1y h1z { 
                refine linked.trans h1y _, convert shift S y h1z, rw mul_one } }
            
    theorem connected : connected span
        := by { suffices : ∀ x, linked (span S) (1:G) x,
                { intros x y, transitivity (1:G), symmetry, apply this, apply this },
            intro, apply linked_mp }

    instance : connected_graph span := ⟨connected⟩

    noncomputable def word_dist : G -> G -> ℕ := @graph.dist span _

    lemma covariant : word_dist (a*x) (a*y) = word_dist x y
        := by { 
            unfold word_dist graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
            let dists : G -> G -> set ℕ := @graph.dists (span S) _,
            have h2 : ∀ x y a ℓ, dists x y ℓ -> dists (a*x) (a*y) ℓ 
                := by { intros x y a ℓ h, cases h with p, use ⟨shift_path S a p, h_h ▸ llist.size_map⟩ },
            exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                h2 x y a ℓ⟩ }
end end cayley

namespace cayley section
    parameters {G : Type} [group G] (S1 S2 : finset G) [genset S1] [genset S2]

    theorem lipschitz : ∃ K : ℕ, ∀ x y : G, word_dist S2 x y <= K * word_dist S1 x y
        := by { let φ : G -> ℕ := word_dist S2 1, let ls := finset.image φ S1,
            obtain K := (finset.max_of_ne_empty (mt finset.image_eq_empty.1 (genset.nem S1))), 
            use K, intros x y, unfold word_dist,
            obtain ⟨⟨⟨l,hx,hy⟩,hp⟩,h⟩ := @graph.shortest_path (span S1) _ x y, rw <-h, clear h,
            revert x y, induction l; intros,
                { convert zero_le _, apply graph.dist_self', rw [<-hx,<-hy], refl },
                { let z := llist.head l_a_1, replace l_ih := l_ih z y rfl hy hp.2, 
                    simp [sizeof,has_sizeof.sizeof,path.size,llist.size] at l_ih ⊢,
                    transitivity word_dist S2 x z + word_dist S2 z y,
                        { exact graph.dist_triangle },
                        { rw [mul_add,mul_one,<-(covariant S2 x⁻¹),inv_mul_self], 
                            convert add_le_add (finset.le_max_of_mem (finset.mem_image_of_mem _ hp.1) h) l_ih, 
                            exact hx.symm } } }
end end cayley
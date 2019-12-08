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
        := by { have h : x ∈ group.closure S.to_set, { rw genset.gen, trivial },
            induction h with s h y hs h1y y z hy hz h1y h1z,
            case group.in_closure.basic : s hs { apply linked.edge, change 1⁻¹ * s ∈ S, rwa [one_inv,one_mul] },
            case group.in_closure.one   : { refl },
            case group.in_closure.inv   : y hy h1y { exact inv S h1y },
            { refine linked.trans h1y _, convert shift S y h1z, rw mul_one } }
            
    theorem connected : connected span
        := by { suffices : ∀ x, linked (span S) (1:G) x,
                { intros x y, transitivity (1:G), symmetry, apply this, apply this },
            intro, apply linked_mp }

    instance : connected_graph span := ⟨by { exact connected S }⟩

    lemma covariant : @dist.graph_dist span _ (a*x:G) (a*y:G) = @dist.graph_dist span _ x y
        := by { 
            suffices : @dist.dists (span S) _ (a*x:G) (a*y:G) = @dist.dists (span S) _ x y,
                { unfold dist.graph_dist, congr, assumption },
            unfold dist.dists, 
            refine norm_num.mk_cong set_of 
                (λ (l : ℕ), ∃ (p : path (span S) (a * x : G) (a * y : G)), sizeof p = l)
                (λ (l : ℕ), ∃ (p : path (span S) x y), sizeof p = l) _,
            funext ℓ, rw [eq_iff_iff], split,
                { intro h, obtain p := h, set p' := shift_path S a⁻¹ p with hp',
                have : sizeof p' = ℓ, { rw hp', 
                simp [shift_path,sizeof,has_sizeof.sizeof,path.size,shift_llist,llist.size_map], exact h_h },
                use p', convert p'.hx, simp, convert p'.hy, simp, exact p'.adj, exact this },
                { intro h, obtain p := h, set p' := shift_path S a p with hp',
                have : sizeof p' = ℓ, { rw hp', 
                simp [shift_path,sizeof,has_sizeof.sizeof,path.size,shift_llist,llist.size_map], exact h_h },
                use p', exact this }
        }
end end cayley

namespace cayley section
    parameters {G : Type} [group G] (S1 S2 : finset G) [genset S1] [genset S2]
    parameters [metric_space (span S1)] [metric_space (span S2)]

    noncomputable def d (S : finset G) [genset S] [metric_space (span S)] : span S -> span S -> ℕ := dist.graph_dist

    theorem lipschitz : ∃ K : ℕ, ∀ x y : G, d S2 x y <= K * d S1 x y
        := by {
            let φ : G -> ℕ := d S2 (1:G),
            let ls : finset ℕ := finset.image φ S1,
            have h2 : S1 ≠ ∅, { exact genset.nem S1 },
            have h3 : ∃ s : G, s ∈ S1, { exact finset.exists_mem_of_ne_empty h2 },
            have h4 : ∀ s ∈ S1, φ s ∈ ls, { intros s h, exact finset.mem_image_of_mem φ h },
            have h1 : ls ≠ ∅, { obtain s := h3, exact finset.ne_empty_of_mem (h4 s h3_h) },
            have h5 : ∃ (a : ℕ), a ∈ finset.max ls:= finset.max_of_ne_empty h1,
            obtain K := h5, use K, intros x y, unfold d,
            obtain pxy := @dist.shortest_path (span S1) _ x y, rw <-h, clear h,
            rcases pxy with ⟨⟨l,hx,hy⟩,hp⟩, revert x y, induction l; intros,
                { subst hx, subst hy, simp [llist.head,llist.last], rw dist.dist_self, trivial },
                { set z := llist.head l_a_1 with hz, replace l_ih := l_ih z y rfl hy hp.2, 
                    simp [sizeof,has_sizeof.sizeof,path.size,llist.size] at l_ih ⊢,
                    transitivity d S2 x z + d S2 z y,
                        { apply dist.dist_triangle },
                        { rw [mul_add,mul_one], refine add_le_add _ l_ih, 
                            unfold d, rw [<-(covariant S2 x⁻¹),inv_mul_self],
                            have h6 := hp.1, rw [<-hz] at h6, simp [llist.head] at hx, rw [hx] at h6,
                            have h7 : x⁻¹ * z ∈ S1, by { exact h6 },
                            change φ (x⁻¹ * z) <= K,
                            exact finset.le_max_of_mem (h4 (x⁻¹ * z) h6) h5_h
                            },
                    }
        }
end end cayley
import tactic group_theory.subgroup
import graph_theory.path

namespace cayley section
    parameters {G : Type} [group G] (S : set G)
    variables (a : G) {x y z : G}

    def adj (x y : G) := x⁻¹ * y ∈ S ∨ y⁻¹ * x ∈ S

    lemma shift_adj {a x y : G} : adj x y -> adj (a*x) (a*y) 
        := by { rw [adj,adj], intro h, convert h using 2; rw [<-mul_assoc]; simp }

    @[symm] lemma adj_symm {x y} : adj x y -> adj y x
        := or.symm

    def span : Graph := { V := G, adj := adj, sym := @adj_symm }

    def shift_llist := llist.map (λ x, a * x)

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

    lemma linked_mp : x ∈ group.closure S -> linked span (1:G) x
        := by { intro h, induction h with s h y hs h1y y z hy hz h1y h1z,
            { apply linked.edge, left, rwa [one_inv,one_mul] },
            { refl },
            { exact inv S h1y },
            { have := shift S y h1z, rw mul_one at this, exact linked.trans h1y this } }
            
    lemma linked_mpr : linked span (1:G) x -> x ∈ group.closure S
        := by { intro h, induction h with b c h1b hbc hr, exact group.in_closure.one S,
            suffices : (b⁻¹:G) * c ∈ group.closure S,
                { convert group.in_closure.mul hr this, rw [mul_inv_cancel_left] },
            cases hbc; replace hbc := group.in_closure.basic hbc,
                { exact hbc },
                { convert group.in_closure.inv hbc, rw [mul_inv_rev,inv_inv] } }

    lemma cayley_connected (h : group.closure S = set.univ) : connected span
        := by {
            suffices : ∀ x, linked (span S) (1:G) x,
                { intros x y, transitivity (1:G), symmetry, apply this, apply this },
            intro, apply linked_mp, rw h, trivial }
end end cayley
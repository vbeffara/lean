import graph_theory.to_mathlib graph_theory.basic graph_theory.path
import combinatorics.simple_graph.connectivity

namespace simple_graph
    variables {V V' : Type} {x y z : V} {G G' : simple_graph V} {S : setoid V}

    def quotient_graph (G : simple_graph V) (S : setoid V) : simple_graph (quotient S) :=
    {
        adj := λ x y, x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y',
        symm := λ x y ⟨h₀,x',y',h₁,h₂,h₃⟩, ⟨h₀.symm,y',x',h₂,h₁,h₃.symm⟩,
        loopless := λ x ⟨h₀,h⟩, h₀ rfl
    }

    notation G `/` S := quotient_graph G S

    def adapted (S : setoid V) (G : simple_graph V) : Prop :=
    relation.refl_trans_gen (G.adj ⊓ S.rel) = S.rel

    namespace quotient_graph
        lemma adj_iff : (G/S).adj ⟦x⟧ ⟦y⟧ <-> ⟦x⟧ ≠ ⟦y⟧ ∧ ∃ x' y', S.rel x x' ∧ S.rel y y' ∧ G.adj x' y' :=
        begin
            simp [quotient_graph], sorry
        end

        def induced_subgraph (G : simple_graph V) (S : setoid V) : simple_graph V :=
        {
            adj := G.adj ⊓ S.rel,
            symm := λ x y ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
            loopless := λ x ⟨h,h'⟩, G.ne_of_adj h rfl,
        }

        lemma induced_le : induced_subgraph G S ≤ G :=
        λ x y h, h.1

        lemma linked : G.linked x y -> (G/S).linked ⟦x⟧ ⟦y⟧ :=
        by { intro h, induction h with u v h₁ h₂ ih, refl, refine ih.trans _,
            by_cases ⟦u⟧ = ⟦v⟧, rw h, refine linked.step ⟨h,u,v,rfl,rfl,h₂⟩ }

        lemma comp {S' : setoid (quotient S)} : G/(S.comp S') ≃g G/S/S'
        := by {
            let φ := @setoid.comp.iso V S S', refine ⟨φ,_⟩, intros a b,
            let f : V -> quotient S := quotient.mk',
            let g : quotient S -> quotient S' := quotient.mk',
            let h : V -> quotient (S.comp S') := quotient.mk',
            have p₀ : ∀ {a b}, h a = h b <-> g (f a) = g (f b) := λ a b, quotient.eq',
            refine a.induction_on' (λ a, _), refine b.induction_on' (λ b, _),
            change (G/S/S').adj (φ (h a)) (φ (h b)) ↔ (G/S.comp S').adj (h a) (h b),
            simp [quotient_graph,φ,setoid.comp.iso],
            split,
            { rintros ⟨h₁,x,h₂,y,h₃,h₄,u,h₅,v,h₆,h₇⟩, refine ⟨_,u,_,v,_,h₇⟩,
                { intro H, exact h₁ (p₀.mp H) },
                { apply p₀.mpr, change g x = g (f a) at h₂, change f u = x at h₅, rw h₅, exact h₂ },
                { apply p₀.mpr, change g y = g (f b) at h₃, change f v = y at h₆, rw h₆, exact h₃ } },
            { rintros ⟨h₁,x,h₂,y,h₃,h₄⟩, refine ⟨_,f x,_,f y,_,_,x,rfl,y,rfl,h₄⟩,
                { intro H, exact h₁ (p₀.mpr H) },
                { exact p₀.mp h₂ },
                { exact p₀.mp h₃ },
                { intro H, have := p₀.mpr (congr_arg g H), rw [<-h₂,<-h₃] at h₁, exact h₁ this } }
        }

        def iso_bot : G ≃g G/⊥ :=
        {
            to_fun := λ x, quotient.mk' x,
            inv_fun := λ y, quotient.lift_on' y id (λ _ _, id),
            left_inv := λ x, by refl,
            right_inv := λ y, by { induction y; refl },
            map_rel_iff' := λ x y, by { simp only [equiv.coe_fn_mk, quotient_graph], split,
                { rintros ⟨h₁,x',y',h₂,h₃,h₄⟩, have h₅ : x' = x := quotient.eq'.mp h₂,
                    have h₆ : y' = y := quotient.eq'.mp h₃, rwa [<-h₅,<-h₆] },
                { intro h, exact ⟨λ h',G.ne_of_adj h (quotient.eq'.mp h'),x,y,rfl,rfl,h⟩ } }
        }
    end quotient_graph
end simple_graph

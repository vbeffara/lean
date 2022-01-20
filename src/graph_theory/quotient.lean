import graph_theory.basic

variables {V : Type} {G : simple_graph V}

namespace simple_graph
    def quotient_graph (G : simple_graph V) (S : setoid V) : simple_graph (quotient S)
    := {
        adj := λ x y, x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y',
        symm := λ x y ⟨h₀,x',y',h₁,h₂,h₃⟩, ⟨h₀.symm,y',x',h₂,h₁,h₃.symm⟩,
        loopless := λ x ⟨h₀,h⟩, h₀ rfl
    }

    notation G `/` S := quotient_graph G S

    def quotient_bot' : V ≃ quotient (⊥ : setoid V)
    := {
        to_fun := λ x, @quotient.mk V ⊥ x,
        inv_fun := λ y, quotient.lift_on' y id (λ _ _, id),
        left_inv := λ x, by { refl },
        right_inv := λ y, by { induction y; refl },
    }

    def quotient_bot : G ≃g G/⊥
    := {
        to_equiv := quotient_bot',
        map_rel_iff' := λ x y, by { simp [quotient_bot',quotient_graph], split,
            { rintros ⟨h₁,x',h₂,y',h₃,h₄⟩, letI : setoid V := ⊥,
                have p : ∀ {u v : V}, ⟦u⟧ = ⟦v⟧ -> u = v := λ u v, quotient.eq.mp,
                rw [p h₂, p h₃] at h₄, exact h₄ },
            { intro h, refine ⟨_,x,rfl,y,rfl,h⟩, intro h',
                have : x = y := quotient.eq'.mp h', subst y, exact G.loopless x h }
        }
    }
end simple_graph

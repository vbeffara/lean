import graph_theory.basic graph_theory.path
import combinatorics.simple_graph.connectivity

namespace setoid
    variables {V : Type}

    def rel_gen (adj : V -> V -> Prop) (S : setoid V)
        := eqv_gen.setoid (λ x y, adj x y ∧ S.rel x y)
end setoid

namespace simple_graph
    variables {V V' : Type} {G G' : simple_graph V} {S : setoid V}

    def quotient_graph (G : simple_graph V) (S : setoid V) : simple_graph (quotient S)
    := {
        adj := λ x y, x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y',
        symm := λ x y ⟨h₀,x',y',h₁,h₂,h₃⟩, ⟨h₀.symm,y',x',h₂,h₁,h₃.symm⟩,
        loopless := λ x ⟨h₀,h⟩, h₀ rfl
    }

    notation G `/` S := quotient_graph G S

    def induced_subgraph (G : simple_graph V) (S : setoid V) : simple_graph V
    := {
        adj := λ x y, G.adj x y ∧ S.rel x y,
        symm := λ x y ⟨h₁,h₂⟩, ⟨h₁.symm,setoid.symm h₂⟩,
        loopless := λ x ⟨h₁,h₂⟩, G.ne_of_adj h₁ rfl,
    }

    lemma induced_le : induced_subgraph G S ≤ G
    := λ x y h, h.1

    def adapted (S : setoid V) (G : simple_graph V) : Prop
    := setoid.rel_gen G.adj S = S

    def adapted' (S : setoid V) (G : simple_graph V) : Prop
    := S.rel = (induced_subgraph G S).linked

    def quotient_bot' : V ≃ quotient (⊥ : setoid V)
    := {
        to_fun := λ x, quotient.mk' x,
        inv_fun := λ y, quotient.lift_on' y id (λ _ _, id),
        left_inv := λ x, by refl,
        right_inv := λ y, by { induction y; refl },
    }

    lemma quotient_bot_eq {x y : V} : @quotient.mk' _ ⊥ x = @quotient.mk' _ ⊥ y -> x = y
    := quotient.eq'.mp

    def quotient_bot : G ≃g G/⊥
    := {
        to_equiv := quotient_bot',
        map_rel_iff' := λ x y, by { split,
        { rintros ⟨h₁,x',y',h₂,h₃,h₄⟩, rw [quotient_bot_eq h₂, quotient_bot_eq h₃] at h₄, exact h₄ },
        { intro h, refine ⟨_,x,y,rfl,rfl,h⟩, intro h', rw quotient_bot_eq h' at h, exact G.loopless _ h } }
    }
end simple_graph

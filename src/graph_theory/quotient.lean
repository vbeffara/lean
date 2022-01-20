import graph_theory.basic

variables {V : Type} {G : simple_graph V}

namespace simple_graph
    def quotient (G : simple_graph V) (s : setoid V) : simple_graph (quotient s)
    := {
        adj := λ x y, x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y',
        symm := λ x y ⟨h₀,x',y',h₁,h₂,h₃⟩, ⟨h₀.symm,y',x',h₂,h₁,h₃.symm⟩,
        loopless := λ x ⟨h₀,h⟩, h₀ rfl
    }

    notation G `/` S := quotient G S
end simple_graph

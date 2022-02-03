import combinatorics.simple_graph.basic
import graph_theory.to_mathlib
open prod

variables {V V₁ V₂ V' : Type} {G₁ : simple_graph V₁} {G₂ : simple_graph V₂}

namespace simple_graph
    def tensor_product (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) : simple_graph (V₁ × V₂) :=
    {
        adj := (G₁.adj on fst) ⊓ (G₂.adj on snd),
        symm := λ _ _ ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
        loopless := λ _ ⟨h₁,h₂⟩, G₁.loopless _ h₁
    }

    infix ` × ` := tensor_product

    def cartesian_product (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) := (⊥ × G₂) ⊔ (G₁ × ⊥)

    infix ` □ `:50 := cartesian_product

    def strong_product (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) := (G₁ □ G₂) ⊔ (G₁ × G₂)

    infix ` ⊠ `:50 := strong_product
end simple_graph

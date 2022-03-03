import combinatorics.simple_graph.basic
import graph_theory.to_mathlib
open prod

variables {V V₁ V₂ V' : Type*} {G₁ : simple_graph V₁} {G₂ : simple_graph V₂}

namespace simple_graph

def tensor_product (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) : simple_graph (V₁ × V₂) :=
{ adj := (G₁.adj on fst) ⊓ (G₂.adj on snd),
  symm := λ _ _ ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
  loopless := λ _ ⟨h₁,h₂⟩, G₁.loopless _ h₁ }

infixr ` × ` := tensor_product

def cartesian_product (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) : simple_graph (V₁ × V₂) :=
{ adj := λ z z', (z.1 = z'.1 ∧ G₂.adj z.2 z'.2) ∨ (G₁.adj z.1 z'.1 ∧ z.2 = z'.2),
  symm := λ _ _ h, by { cases h, exact or.inl ⟨h.1.symm,h.2.symm⟩, exact or.inr ⟨h.1.symm,h.2.symm⟩ },
  loopless := λ x, by simp only [irrefl, and_false, false_and, or_self, not_false_iff] }

infixr ` □ `:50 := cartesian_product

def strong_product (G₁ : simple_graph V₁) (G₂ : simple_graph V₂) : simple_graph (V₁ × V₂) :=
(G₁ □ G₂) ⊔ (G₁ × G₂)

infixr ` ⊠ `:50 := strong_product
end simple_graph

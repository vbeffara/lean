import tactic
import combinatorics.simple_graph.basic combinatorics.simple_graph.degree_sum data.set.basic
import graph_theory.to_mathlib
open function classical set finset

variables {V V' V'' : Type*}
variables {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph

def is_smaller (G : simple_graph V) (G' : simple_graph V') : Prop :=
∃ f : G →g G', injective f

infix ` ≼s `:50 := is_smaller

namespace is_smaller
@[refl] lemma refl : G ≼s G :=
⟨⟨id, λ x y, id⟩, injective_id⟩

@[trans] lemma trans : G ≼s G' → G' ≼s G'' → G ≼s G''
| ⟨f₁,h₁⟩ ⟨f₂,h₂⟩ := ⟨f₂.comp f₁, injective.comp h₂ h₁⟩

lemma iso_left : G ≃g G' → G' ≼s G'' → G ≼s G''
| φ ⟨ψ,h⟩ := ⟨ψ.comp φ, (φ.to_equiv.injective_comp ⇑ψ).mpr h⟩

lemma le_left : G ≤ H → H ≼s G' → G ≼s G'
| h₁ ⟨⟨f,h₂⟩,h₃⟩ := ⟨⟨f,λ _ _ h, h₂ (h₁ h)⟩,h₃⟩

lemma iso_right : G ≼s G' → G' ≃g G'' → G ≼s G''
| ⟨ψ,h⟩ φ := ⟨φ.to_hom.comp ψ, (equiv.comp_injective ψ φ.to_equiv).mpr h⟩
end is_smaller
end simple_graph

import combinatorics.simple_graph.basic

variables {U V : Type*}

open simple_graph

def Φ₁ : (complete_bipartite_graph U V).dart → (U × V) ⊕ (V × U) :=
begin
  rintro ⟨⟨x | x, y | y⟩, h⟩; { simp at h, contradiction } <|>
    { exact sum.inl (x, y) } <|> { exact sum.inr (x, y) }
end

def Φ₂ : (U × V) ⊕ (V × U) → (complete_bipartite_graph U V).dart :=
sum.elim (λ ⟨x,y⟩, ⟨(sum.inl x, sum.inr y), by simp⟩)
         (λ ⟨x,y⟩, ⟨(sum.inr x, sum.inl y), by simp⟩)

def toto : (complete_bipartite_graph U V).dart ≃ (U × V) ⊕ (V × U) :=
{
  to_fun := Φ₁,
  inv_fun := Φ₂,
  left_inv := by { rintro ⟨⟨x | x, y | y⟩, h⟩; simp [Φ₁, Φ₂] at h ⊢; cases h },
  right_inv := λ x, by { cases x; cases x; simp [Φ₁, Φ₂] }
}

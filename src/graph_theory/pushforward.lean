import graph_theory.basic
open function

variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {f : V → V'} {g : V' → V''}

namespace simple_graph
    def pushforward (f : V → V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x' y', x' ≠ y' ∧ ∃ x y : V, f x = x' ∧ f y = y' ∧ G.adj x y,
        symm := λ x' y' ⟨h₀,x,y,h₁,h₂,h₃⟩, ⟨h₀.symm,y,x,h₂,h₁,h₃.symm⟩,
        loopless := λ _ ⟨h₀,_⟩, h₀ rfl
    }

    def pullback (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := G'.adj on f,
        symm := λ x y h, G'.symm h,
        loopless := λ _, G'.loopless _
    }

    namespace pushforward
        lemma right_inv (h : surjective f) : right_inverse (pullback f) (pushforward f) :=
        begin
            intro G', ext x' y', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₂⟩, exact h₂ },
            { intro h₁, cases h x' with x, cases h y' with y, substs x' y',
                refine ⟨G'.ne_of_adj h₁,x,y,rfl,rfl,h₁⟩ }
        end

        lemma comp : pushforward (g∘f) = pushforward g ∘ pushforward f :=
        begin
            ext x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩ },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩, exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end
    end pushforward
end simple_graph

import graph_theory.basic

variables {V V' V'' : Type} {G : simple_graph V} {f : V -> V'} {g : V' -> V''}

namespace simple_graph
    def pushforward (f : V -> V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x' y', x' ≠ y' ∧ ∃ x y : V, f x = x' ∧ f y = y' ∧ G.adj x y,
        symm := λ x' y' ⟨h₀,x,y,h₁,h₂,h₃⟩, ⟨h₀.symm,y,x,h₂,h₁,h₃.symm⟩,
        loopless := λ _ ⟨h₀,_⟩, h₀ rfl
    }

    namespace pushforward
        lemma comp : pushforward (g∘f) G = pushforward g (pushforward f G) :=
        begin
            ext x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩,
                exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩, },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩,
                exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end
    end pushforward
end simple_graph

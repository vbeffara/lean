import tactic
import combinatorics.simple_graph.basic data.set.basic
import graph_theory.to_mathlib graph_theory.pushforward

variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph
    variables
    open function classical set

    @[ext] structure step (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace step
        variables {e e' : step G}

        @[simp] def ends (e : step G) : sym2 V := ⟦( e.x, e.y )⟧
        @[simp] def flip (e : step G) : step G := ⟨e.h.symm⟩

        @[simp] lemma ends_flip : e.flip.ends = e.ends := sym2.eq_swap

        lemma same_iff : (e' = e ∨ e' = flip e) <-> e.ends = e'.ends
            := by { split; intro h,
                { cases h; subst e', rw ends_flip },
                { replace h := sym2.eq_iff.mp h, cases e with x y h1, cases e' with x' y', dsimp at h,
                    cases h; { cases h, substs x' y', simp } }
            }
    end step

    def is_smaller (G : simple_graph V) (G' : simple_graph V') : Prop := ∃ f : G →g G', injective f

    infix ` ≼s `:50 := is_smaller

    namespace is_smaller
        @[refl] lemma refl : G ≼s G := ⟨⟨id, λ x y, id⟩, injective_id⟩

        @[trans] lemma trans : G ≼s G' -> G' ≼s G'' -> G ≼s G''
            | ⟨f₁,h₁⟩ ⟨f₂,h₂⟩ := ⟨f₂.comp f₁, injective.comp h₂ h₁⟩

        lemma iso_left : G ≃g G' -> G' ≼s G'' -> G ≼s G''
            | φ ⟨ψ,h⟩ := ⟨ψ.comp φ, (φ.to_equiv.injective_comp ⇑ψ).mpr h⟩

        lemma le_left : G ≤ H -> H ≼s G' -> G ≼s G'
            | h₁ ⟨⟨f,h₂⟩,h₃⟩ := ⟨⟨f,λ _ _ h, h₂ (h₁ h)⟩,h₃⟩

        lemma select_left {pred : V → Prop} : G ≼s G' -> select G pred ≼s G'
            | ⟨⟨f,h₁⟩,h₂⟩ :=
                let g : {x // pred x} -> V' := f ∘ subtype.val
                in ⟨⟨g,λ a b,h₁⟩,h₂.comp subtype.val_injective⟩

        lemma iso_right : G ≼s G' -> G' ≃g G'' -> G ≼s G''
            | ⟨ψ,h⟩ φ := ⟨φ.to_hom.comp ψ, (equiv.comp_injective ψ φ.to_equiv).mpr h⟩
    end is_smaller
end simple_graph

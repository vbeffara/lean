import tactic
import combinatorics.simple_graph.basic data.set.basic
import graph_theory.to_mathlib

variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph
    variables
    open function classical set finset

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

    section finite
        variables [fintype V]

        noncomputable instance fintype_step : fintype G.step :=
        begin
            let f : G.step → V × V := λ e, (e.x, e.y), apply fintype.of_injective f,
            rintros ⟨x₁,y₁,h₁⟩ ⟨x₂,y₂,h₂⟩, simp only [prod.mk.inj_iff], exact id
        end

        variables [decidable_eq V] [decidable_rel G.adj]

        def number_of_edges (G : simple_graph V) [decidable_rel G.adj] : ℕ :=
        fintype.card G.edge_set

        notation `∥ ` G ` ∥` := number_of_edges G

        lemma nb_edges_of_nb_steps : fintype.card G.step = 2 * ∥ G ∥ := sorry
    end finite

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

        lemma iso_right : G ≼s G' -> G' ≃g G'' -> G ≼s G''
            | ⟨ψ,h⟩ φ := ⟨φ.to_hom.comp ψ, (equiv.comp_injective ψ φ.to_equiv).mpr h⟩
    end is_smaller
end simple_graph

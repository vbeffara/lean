import tactic
import combinatorics.simple_graph.basic combinatorics.simple_graph.degree_sum data.set.basic
import graph_theory.to_mathlib

variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph
    variables
    open function classical set finset

    @[reducible] def vertices (G : simple_graph V) : Type := V

    @[reducible] def step (G : simple_graph V) := G.dart

    namespace step
        variables {e e' : step G}

        lemma same_iff : (e' = e ∨ e' = e.rev) <-> e.edge = e'.edge
            := by { split; intro h,
                { cases h; subst e', rw dart.rev_edge },
                { replace h := sym2.eq_iff.mp h, cases e with x y h1, cases e' with x' y', dsimp at h,
                    cases h; { cases h, substs x' y', simp [flip,dart.rev] } }
            }
    end step

    section finite
        variables [fintype V]

        noncomputable instance fintype_step : fintype G.step :=
        begin
            let f : G.step → V × V := λ e, (e.fst, e.snd), apply fintype.of_injective f,
            rintros ⟨x₁,y₁,h₁⟩ ⟨x₂,y₂,h₂⟩, simp only [prod.mk.inj_iff], exact id
        end

        variables [decidable_eq V] [decidable_rel G.adj]

        def number_of_edges (G : simple_graph V) [decidable_rel G.adj] : ℕ :=
        fintype.card G.edge_set

        notation `∥ ` G ` ∥` := number_of_edges G

        lemma nb_edges_of_nb_steps : fintype.card G.step = 2 * ∥ G ∥ :=
        begin
            let φ : G.step → bool × G.edge_set := by {
                rintros ⟨x,y,h⟩,
                let xy : sym2 V := ⟦(x,y)⟧,
                let ε : bool := if xy.out = (x,y) then tt else ff,
                have := (mem_edge_set G).mpr h,
                refine (ε,⟨_,this⟩),
            },
            suffices : bijective φ, by {
                rw fintype.card_of_bijective this,
                simp [number_of_edges]
            },
            split,
            { rintros ⟨x,y,h⟩ ⟨x',y',h'⟩, simp, intros h₁ h₂,
                replace h₂ := quotient.eq.mpr h₂,
                have := sym2.eq_iff.mp h₂, cases this, exact this,
                cases this, substs x' y', rw ←h₂ at h₁,
                set xy : sym2 V := ⟦(x,y)⟧,
                have := (quotient.out_eq xy).trans h₂,
                cases xy.out,
                have := sym2.eq_iff.mp this, cases this,
                { cases this_1, substs fst snd, simp at h₁, exact h₁.symm },
                { cases this_1, substs fst snd, replace h₁ := h₁.symm, simp at h₁, exact h₁ }
            },
            { rintros ⟨ε,⟨xy,h⟩⟩, have h₁ := quotient.out_eq xy, set e := xy.out with he,
                have : e = (e.fst,e.snd) := prod.ext rfl rfl, rw this at *, rw ←h₁ at h,
                have adj := G.mem_edge_set.mp h, have hxy := @sym2.eq_swap V e.fst e.snd,
                cases ε,
                { use ⟨_,_,adj.symm⟩, simp [φ], refine ⟨_,_⟩,
                    { rw [←hxy,he,quotient.out_eq,←he], intro h, have := (prod.ext_iff.mp h).1,
                        exact G.ne_of_adj adj this },
                    { rw [←hxy], exact h₁ } },
                { use ⟨_,_,adj⟩, simp [φ] }
            }
        end
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

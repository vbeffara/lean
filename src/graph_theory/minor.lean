import tactic
import graph_theory.basic graph_theory.path
open function
open_locale classical

namespace simple_graph
    namespace contraction
        structure setup :=
            {V : Type}
            (G g : simple_graph V)
            (sub : ∀ {x y : V}, g.adj x y -> G.adj x y)

        variables (S : setup)

        instance contraction_setoid : setoid S.V := ⟨S.g.linked,simple_graph.linked.equiv⟩

        def clusters := quotient (contraction.contraction_setoid S)
    end contraction

    namespace contraction
        variables {S : setup}

        def adj (x y : clusters S) := x ≠ y ∧ ∃ x' y' : S.V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ S.G.adj x' y'

        @[symm] lemma symm (x y : clusters S) : adj x y -> adj y x
            := by { rintro ⟨h0,x',y',h1,h2,h3⟩, exact ⟨h0.symm,y',x',h2,h1,S.G.symm h3⟩ }

        def contract (S : setup) : simple_graph (clusters S) := ⟨adj, symm⟩

        lemma proj_adj {x y : S.V} (h : S.G.adj x y) : ⟦x⟧ = ⟦y⟧ ∨ (contract S).adj ⟦x⟧ ⟦y⟧
            := dite (⟦x⟧ = ⟦y⟧) or.inl (λ h', or.inr ⟨h',x,y,rfl,rfl,h⟩)

        lemma linked_of_adj {x y : S.V} (h : (contract S).adj ⟦x⟧ ⟦y⟧) : linked S.G x y
            := by { obtain ⟨h₁,a,b,h₂,h₃,h₄⟩ := h, transitivity b, transitivity a,
                exact linked_of_subgraph S.sub (quotient.eq.mp h₂.symm),
                exact linked.edge h₄,
                exact linked_of_subgraph S.sub (quotient.eq.mp h₃) }

        noncomputable def proj_path {x y : S.V} (p : path S.G x y) : path (contract S) ⟦x⟧ ⟦y⟧
            := path.rec path.point (λ a b _ h2 ih, dite (⟦a⟧ = ⟦b⟧)
                (λ h, by { rw <-h, exact ih }) (λ h, ih.step ⟨h,a,b,rfl,rfl,h2⟩)) p


        lemma project_linked {x y : S.V} (h : linked S.G x y) : linked (contract S) ⟦x⟧ ⟦y⟧
            := relation.refl_trans_gen.rec relation.refl_trans_gen.refl
                (λ _ _ _ h₂ ih, or.cases_on (proj_adj h₂) (λ h', h' ▸ ih) ih.tail) h

        lemma lift_linked' {S : setup} {xx yy : clusters S} (h : linked (contract S) xx yy) (x y : S.V)
                (hx : ⟦x⟧ = xx) (hy : ⟦y⟧ = yy) : linked S.G x y
            := by {
                induction h with x' xx' h1 h2 ih generalizing x y,
                { subst hy, exact linked_of_subgraph S.sub (quotient.eq.mp hx) },
                { obtain ⟨u, hu : ⟦u⟧ = x'⟩ := quot.exists_rep x', substs hu hx hy,
                    transitivity u, exact ih x u rfl rfl, exact linked_of_adj h2 }
            }

        lemma lift_linked {S : setup} {x y : S.V} (h : linked (contract S) ⟦x⟧ ⟦y⟧) : linked S.G x y
            := lift_linked' h _ _ rfl rfl

        lemma contract_connected_iff {S : setup} : connected S.G <-> connected (contract S)
            := {
                mp := λ h xx yy, by {
                    obtain ⟨x, hx : ⟦x⟧ = xx⟩ := quot.exists_rep xx, subst hx,
                    obtain ⟨y, hy : ⟦y⟧ = yy⟩ := quot.exists_rep yy, subst hy,
                    exact project_linked (h x y) },
                mpr := λ h x y, lift_linked (h ⟦x⟧ ⟦y⟧)
            }

        -- def is_minor (G G' : Type) [simple_graph G] [simple_graph G'] : Prop
        --     := ∃ C : chunked G', by exactI embeds_into G (contract G')
    end contraction
end simple_graph

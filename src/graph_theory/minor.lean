import tactic
import graph_theory.basic graph_theory.path_embedding
open function
open_locale classical

namespace simple_graph
    variables {V V' : Type}

    namespace contraction
        structure setup (V : Type) extends simple_graph V :=
            (g : simple_graph V)
            (sub : ∀ {x y : V}, g.adj x y -> adj x y)

        def support (S : setup V) : Type := V

        instance contraction_setoid (S : setup V) : setoid (support S) := ⟨S.g.linked,simple_graph.linked.equiv⟩

        def clusters (S : setup V) := quotient (contraction.contraction_setoid S)

        variables {S : setup V} {x y : support S}
        open path

        def adj (x y : clusters S) := x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ S.adj x' y'

        @[symm] lemma symm (x y : clusters S) : adj x y -> adj y x
            := by { rintro ⟨h0,x',y',h1,h2,h3⟩, exact ⟨h0.symm,y',x',h2,h1,h3.symm⟩ }

        def contract (S : setup V) : simple_graph (clusters S) := ⟨adj, symm⟩

        lemma proj_adj (h : S.adj x y) : ⟦x⟧ = ⟦y⟧ ∨ (contract S).adj ⟦x⟧ ⟦y⟧
            := dite (⟦x⟧ = ⟦y⟧) or.inl (λ h', or.inr ⟨h',x,y,rfl,rfl,h⟩)

        lemma linked_of_adj (h : (contract S).adj ⟦x⟧ ⟦y⟧) : linked S.to_simple_graph x y
            := by { obtain ⟨h₁,a,b,h₂,h₃,h₄⟩ := h, transitivity b, transitivity a,
                exact linked_of_subgraph S.sub (quotient.eq.mp h₂.symm),
                exact linked.edge h₄,
                exact linked_of_subgraph S.sub (quotient.eq.mp h₃) }

        noncomputable def proj_path : Π {y : V}, path S.to_simple_graph x y -> path (contract S) ⟦x⟧ ⟦y⟧
            | _ point                 := point
            | z (p · (h : S.adj y z)) := dite (⟦y⟧ = ⟦z⟧) (λ h, by { rw <-h, exact proj_path p })
                                                          (λ h', proj_path p · ⟨h',_,_,rfl,rfl,h⟩)

        lemma project_linked (h : linked S.to_simple_graph x y) : linked (contract S) ⟦x⟧ ⟦y⟧
            := relation.refl_trans_gen.rec relation.refl_trans_gen.refl
                (λ _ _ _ h₂ ih, or.cases_on (proj_adj h₂) (λ h', h' ▸ ih) ih.tail) h

        lemma lift_linked' {xx yy : clusters S} (h : linked (contract S) xx yy) (x y : V)
                (hx : ⟦x⟧ = xx) (hy : ⟦y⟧ = yy) : linked S.to_simple_graph x y
            := by {
                induction h with x' xx' h1 h2 ih generalizing x y,
                { subst hy, exact linked_of_subgraph S.sub (quotient.eq.mp hx) },
                { obtain ⟨u, hu : ⟦u⟧ = x'⟩ := quot.exists_rep x', substs hu hx hy,
                    transitivity u, exact ih x u rfl rfl, exact linked_of_adj h2 }
            }

        lemma lift_linked (h : linked (contract S) ⟦x⟧ ⟦y⟧) : linked S.to_simple_graph x y
            := lift_linked' h _ _ rfl rfl

        lemma contract_connected_iff : connected S.to_simple_graph <-> connected (contract S)
            := {
                mp := λ h xx yy, by {
                    obtain ⟨x, hx : ⟦x⟧ = xx⟩ := quot.exists_rep xx, subst hx,
                    obtain ⟨y, hy : ⟦y⟧ = yy⟩ := quot.exists_rep yy, subst hy,
                    exact project_linked (h x y) },
                mpr := λ h x y, lift_linked (h ⟦x⟧ ⟦y⟧)
            }

        def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
            := ∃ S : setup V', S.to_simple_graph = G' ∧ embeds_into G (contract S)
    end contraction
end simple_graph

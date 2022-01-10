import tactic
import graph_theory.basic graph_theory.path_embedding
open function
open_locale classical

namespace simple_graph
    open walk
    variables {V V' : Type} {G : simple_graph V}

    namespace contraction
        structure setup (G : simple_graph V) :=
            (g : simple_graph V)
            (sub : ∀ {x y : V}, g.adj x y -> G.adj x y)

        def support (S : setup G) : Type := V

        instance contraction_setoid (S : setup G) : setoid (support S) := ⟨S.g.linked,simple_graph.linked.equiv⟩

        def clusters (S : setup G) := quotient (contraction.contraction_setoid S)

        variables {S : setup G} {x y : support S}
        open mypath

        def adj (x y : clusters S) := x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y'

        @[symm] lemma symm (x y : clusters S) : adj x y -> adj y x
            | ⟨h0,x',y',h1,h2,h3⟩ := ⟨h0.symm,y',x',h2,h1,h3.symm⟩

        def contract (S : setup G) : simple_graph (clusters S) := ⟨adj, symm⟩

        lemma proj_adj (h : G.adj x y) : ⟦x⟧ = ⟦y⟧ ∨ (contract S).adj ⟦x⟧ ⟦y⟧
            := dite (⟦x⟧ = ⟦y⟧) or.inl (λ h', or.inr ⟨h',x,y,rfl,rfl,h⟩)

        lemma linked_of_adj : (contract S).adj ⟦x⟧ ⟦y⟧ -> linked G x y
            | ⟨h₁,a,b,h₂,h₃,h₄⟩ := by { transitivity b, transitivity a,
                exact linked.linked_of_subgraph S.sub (quotient.eq.mp h₂.symm),
                exact linked.step h₄,
                exact linked.linked_of_subgraph S.sub (quotient.eq.mp h₃) }

        noncomputable def proj_path : Π {x y : V}, walk G x y -> walk (contract S) ⟦x⟧ ⟦y⟧
            | _ _ nil                      := nil
            | _ z (cons (h : G.adj x y) p) := dite (⟦y⟧ = ⟦x⟧) (λ h, by { rw <-h, exact proj_path p })
                                                               (λ h', walk.cons ⟨ne.symm h',_,_,rfl,rfl,h⟩ (proj_path p))

        lemma project_linked : ∀ {x y}, linked G x y -> linked (contract S) ⟦x⟧ ⟦y⟧
            | _ _ ⟨p⟩ := by { induction p with u u v w h p ih, refl,
                cases proj_adj h with h' h', rw h', exact ih, exact ih.cons h' }

        lemma lift_linked' {xx yy : clusters S} : linked (contract S) xx yy ->
                ∀ (x y : V) (hx : ⟦x⟧ = xx) (hy : ⟦y⟧ = yy), linked G x y
            := by {
                intro h, cases h with p, induction p with u u v w h p ih; intros x y hx hy,
                { subst hy, exact linked.linked_of_subgraph S.sub (quotient.eq.mp hx) },
                { obtain ⟨a, ha : ⟦a⟧ = v⟩ := quot.exists_rep v, substs ha hx hy,
                    transitivity a, exact linked_of_adj h, exact ih a y rfl rfl }
            }

        lemma lift_linked (h : linked (contract S) ⟦x⟧ ⟦y⟧) : linked G x y
            := lift_linked' h _ _ rfl rfl

        lemma contract_connected_iff : connected G <-> connected (contract S)
            := {
                mp := λ h xx yy, by {
                    obtain ⟨x, hx : ⟦x⟧ = xx⟩ := quot.exists_rep xx, subst hx,
                    obtain ⟨y, hy : ⟦y⟧ = yy⟩ := quot.exists_rep yy, subst hy,
                    exact project_linked (h x y) },
                mpr := λ h x y, lift_linked (h ⟦x⟧ ⟦y⟧)
            }

        def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
            := ∃ S : setup G', embeds_into G (contract S)
    end contraction
end simple_graph

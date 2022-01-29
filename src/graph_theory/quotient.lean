import graph_theory.to_mathlib graph_theory.basic graph_theory.pushforward graph_theory.path
import combinatorics.simple_graph.connectivity
open function

namespace simple_graph
    variables {V V' : Type} {x y z : V} {G G' : simple_graph V} {S : setoid V}

    def quotient_graph (G : simple_graph V) (S : setoid V) : simple_graph (quotient S) :=
    push quotient.mk G

    notation G `/` S := quotient_graph G S

    def adapted (S : setoid V) (G : simple_graph V) : Prop :=
    relation.refl_trans_gen (G.adj ⊓ S.rel) = S.rel

    namespace quotient_graph
        def induced_subgraph (G : simple_graph V) (S : setoid V) : simple_graph V :=
        {
            adj := G.adj ⊓ S.rel,
            symm := λ x y ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
            loopless := λ x ⟨h,h'⟩, G.ne_of_adj h rfl,
        }

        lemma induced_le : induced_subgraph G S ≤ G :=
        λ x y h, h.1

        lemma comp_eq {S' : setoid (quotient S)} : G/S/S' = push (setoid.comp.iso S S') (G/(S.comp S')) :=
        begin
            convert congr_fun (congr_arg push (setoid.comp.eq S S')) G using 1;
            { symmetry, rw [push.comp], refl }
        end

        lemma comp {S' : setoid (quotient S)} : G/(S.comp S') ≃g G/S/S'
        := by { rw comp_eq, exact push.to_iso _ _ }

        def iso_bot : G ≃g G/⊥ :=
        {
            to_fun := λ x, quotient.mk' x,
            inv_fun := λ y, quotient.lift_on' y id (λ _ _, id),
            left_inv := λ x, by refl,
            right_inv := λ y, by { induction y; refl },
            map_rel_iff' := λ x y, by { simp only [equiv.coe_fn_mk, quotient_graph], split,
                { rintros ⟨h₁,x',y',h₂,h₃,h₄⟩, have h₅ : x' = x := quotient.eq'.mp h₂,
                    have h₆ : y' = y := quotient.eq'.mp h₃, rwa [<-h₅,<-h₆] },
                { intro h, exact ⟨λ h',G.ne_of_adj h (quotient.eq'.mp h'),x,y,rfl,rfl,h⟩ } }
        }
    end quotient_graph
end simple_graph

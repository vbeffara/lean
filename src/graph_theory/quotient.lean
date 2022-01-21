import graph_theory.basic graph_theory.path
import combinatorics.simple_graph.connectivity

namespace setoid
    variables {V : Type}

    def rel_gen (adj : V -> V -> Prop) (S : setoid V)
        := eqv_gen.setoid (λ x y, adj x y ∧ S.rel x y)
end setoid

namespace simple_graph
    variables {V V' : Type} {G G' : simple_graph V} {S : setoid V}

    def quotient_graph (G : simple_graph V) (S : setoid V) : simple_graph (quotient S)
    := {
        adj := λ x y, x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y',
        symm := λ x y ⟨h₀,x',y',h₁,h₂,h₃⟩, ⟨h₀.symm,y',x',h₂,h₁,h₃.symm⟩,
        loopless := λ x ⟨h₀,h⟩, h₀ rfl
    }

    notation G `/` S := quotient_graph G S

    def induced_subgraph (G : simple_graph V) (S : setoid V) : simple_graph V
    := {
        adj := λ x y, G.adj x y ∧ S.rel x y,
        symm := λ x y ⟨h₁,h₂⟩, ⟨h₁.symm,setoid.symm h₂⟩,
        loopless := λ x ⟨h₁,h₂⟩, G.ne_of_adj h₁ rfl,
    }

    lemma induced_le : induced_subgraph G S ≤ G
    := λ x y h, h.1

    def adapted₀ (S : setoid V) (G : simple_graph V) : Prop
    := setoid.rel_gen G.adj S = S

    def adapted₁ (S : setoid V) (G : simple_graph V) : Prop
    := ∀ x y : V, S.rel x y -> ∃ p : walk G x y, ∀ z ∈ p.support, S.rel z y

    def adapted₂ (S : setoid V) (G : simple_graph V) : Prop
    := S.rel = (induced_subgraph G S).linked

    def adapted₃ (S : setoid V) (G : simple_graph V) : Prop
    := ∀ x y : V, S.rel x y -> (induced_subgraph G S).linked x y

    def map₁ : Π {x y : V} (p : walk G x y) (h : ∀ z ∈ p.support, S.rel z y), walk (induced_subgraph G S) x y
    := by { intros, induction p with a a b c h' p ih, refl, refine walk.cons ⟨h',_⟩ _,
        { transitivity c, apply h, left, refl, symmetry, apply h, right, cases p, simp [list.mem], left, refl },
        { apply ih, intros z hz, apply h, right, exact hz } }

    def map₂ : ∀ {x y : V}, walk (induced_subgraph G S) x y -> walk G x y
        | _ _ walk.nil        := walk.nil
        | _ _ (walk.cons h p) := walk.cons h.1 (map₂ p)

    lemma map₂_rel {x y : V} {p : walk (induced_subgraph G S) x y} : ∀ z ∈ (map₂ p).support, S.rel z y
    := by { induction p with a a b c h p ih; intros z hz,
        { simp [map₂] at hz, rw hz },
        { simp [map₂] at hz, cases hz,
            { subst z, transitivity b, exact h.2, apply ih, simp [map₂] },
            { apply ih, exact hz } } }

    lemma adapted_iff₁₃ : adapted₁ S G <-> adapted₃ S G
    := by { unfold adapted₁ adapted₃, split; intros h₁ x y h₂; have h₃ := h₁ x y h₂,
        { rcases h₃ with ⟨p,h₄⟩, use map₁ p h₄ },
        { cases h₃ with p, use map₂ p, exact map₂_rel } }

    lemma adapted_iff₂₃ : adapted₂ S G <-> adapted₃ S G
    := by { unfold adapted₂ adapted₃, split,
        { intros h₁ x y, rw h₁, exact id },
        { intro h₁, ext x y, refine ⟨h₁ x y, _⟩, rintro ⟨p⟩, induction p with a a b c h p ih,
            { refl }, { transitivity b, exact h.2, exact ih } } }

    lemma adapted_iff₀₃ : adapted₀ S G <-> adapted₃ S G
    := by { unfold adapted₀ adapted₃, split,
        { intros h₁ x y h₂, rw <-h₁ at h₂, induction h₂ with a b h₃ a a b h₂ ih a b c h₂ h₃ h₄ h₅,
            { apply linked.step, exact h₃ },
            { refl },
            { exact ih.symm },
            { exact h₄.trans h₅ } },
        { intro h₁, ext, split,
            { intro h₂, unfold setoid.rel_gen at h₂, induction h₂ with a b h₃ a a b h₂ ih a b c h₂ h₃ h₄ h₅,
                { exact h₃.2 },
                { refl },
                { symmetry, exact ih },
                { transitivity b; assumption } },
            { intro h₂, have h₃ := h₁ a b h₂, cases h₃ with p, induction p with a a b c h p ih,
                { refl },
                { transitivity b, apply eqv_gen.rel, exact h, apply ih, transitivity a, symmetry,
                    exact h.2, exact h₂ } } }
    }

    def quotient_bot' : V ≃ quotient (⊥ : setoid V)
    := {
        to_fun := λ x, quotient.mk' x,
        inv_fun := λ y, quotient.lift_on' y id (λ _ _, id),
        left_inv := λ x, by refl,
        right_inv := λ y, by { induction y; refl },
    }

    lemma quotient_bot_eq {x y : V} : @quotient.mk' _ ⊥ x = @quotient.mk' _ ⊥ y -> x = y
    := quotient.eq'.mp

    def quotient_bot : G ≃g G/⊥
    := {
        to_equiv := quotient_bot',
        map_rel_iff' := λ x y, by { split,
        { rintros ⟨h₁,x',y',h₂,h₃,h₄⟩, rw [quotient_bot_eq h₂, quotient_bot_eq h₃] at h₄, exact h₄ },
        { intro h, refine ⟨_,x,y,rfl,rfl,h⟩, intro h', rw quotient_bot_eq h' at h, exact G.loopless _ h } }
    }
end simple_graph

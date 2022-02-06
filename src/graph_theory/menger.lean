import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward
open finset classical function

variables {V : Type} [decidable_eq V] [fintype V] {G : simple_graph V} [decidable_rel G.adj] {A B : finset V}

namespace simple_graph
    -- section contraction_stuff
    --     def number_of_edges (G : simple_graph V) [decidable_rel G.adj] : ℕ :=
    --     finset.sum (univ : finset V) (λ v, G.degree v)

    --     notation `∥ ` G ` ∥` := number_of_edges G

    --     def edge_setoid (e : sym2 V) : setoid V :=
    --     {
    --         r := λ x y, x = y ∨ (x ∈ e ∧ y ∈ e),
    --         iseqv := by { refine ⟨_,_,_⟩,
    --             { intro x, left, refl },
    --             { intros x y h, cases h, left, exact h.symm, right, exact h.symm },
    --             { intros x y z h₁ h₂, cases h₂, rw h₂ at h₁, exact h₁,
    --                 cases h₁, subst h₁, right, exact h₂, right, exact ⟨h₁.1,h₂.2⟩ } }
    --     }

    --     def edge_contraction (G : simple_graph V) (e : sym2 V) : simple_graph (quotient (edge_setoid e)) :=
    --     push (@quotient.mk' _ (edge_setoid e)) G

    --     infix `/` := edge_contraction

    --     noncomputable instance (V : Type) [fintype V] [decidable_eq V] (S : setoid V) : decidable_eq (quotient S) :=
    --     dec_rel _

    --     instance (V : Type) [fintype V] (S : setoid V) [decidable_eq (quotient S)] : fintype (quotient S) :=
    --     ⟨finset.image quotient.mk univ, λ x, quotient.induction_on' x $ λ a, finset.mem_image.mpr ⟨a, mem_univ a, rfl⟩⟩

    --     noncomputable instance (V : Type) [fintype V] [decidable_eq V] (G : simple_graph V) (e : G.edge_set) :
    --     decidable_rel (G/e).adj :=
    --     dec_rel _

    --     lemma lt_edges_of_contract {e : G.edge_set} : ∥ G/e ∥ < ∥ G ∥ :=
    --     begin
    --         rcases e with ⟨⟨x,y⟩,h⟩, set e := (⟨⟦(x,y)⟧,h⟩ : G.edge_set),
    --         letI : setoid V := edge_setoid e,
    --         have : (G/e).degree ⟦x⟧ + 1 = G.degree x := by {
    --             simp [degree,neighbor_finset], sorry,
    --         },
    --         sorry
    --     end
    -- end contraction_stuff

    structure AB_path (G : simple_graph V) (A B : finset V) :=
        {a b : V} (p : walk G a b)
        (ha : a ∈ A) (hb : b ∈ B)

    def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
    ∀ γ : AB_path G A B, ∃ z : V, z ∈ X ∧ z ∈ γ.p.support

    lemma separates_self : separates G A B A :=
    λ γ, ⟨γ.a, ⟨γ.ha, γ.p.start_mem_support⟩⟩

    structure cut_set (G : simple_graph V) (A B : finset V) :=
        (X : finset V)
        (sep : separates G A B X)

    lemma nonempty_cut_set : nonempty (cut_set G A B) :=
    ⟨⟨A, separates_self⟩⟩

    def cut_set_sizes (G : simple_graph V) (A B : finset V) : set ℕ :=
    set.range (λ X : cut_set G A B, X.X.card)

    noncomputable def min_cut (G : simple_graph V) [decidable_rel G.adj] (A B : finset V) : ℕ :=
    well_founded.min nat.lt_wf (cut_set_sizes G A B) $ set.range_nonempty_iff_nonempty.mpr nonempty_cut_set

    def joinable (G : simple_graph V) (A B : finset V) : Prop := nonempty (AB_path G A B)

    structure path_set (G : simple_graph V) (A B : finset V) extends finset (AB_path G A B) :=
    (disjoint : ∀ {γ₁ γ₂ : to_finset} {z : V}, z ∈ γ₁.val.p.support → z ∈ γ₂.val.p.support → γ₁ = γ₂)

    lemma path_le_cut {P : path_set G A B} {X : cut_set G A B} : P.to_finset.card ≤ X.X.card :=
    begin
        let φ : Π γ : P.to_finset, {z : V // z ∈ X.X ∧ z ∈ γ.val.p.support} :=
            λ γ, subtype_of_exists (X.sep γ),
        let ψ : P.to_finset → X.X := λ γ, ⟨φ γ, (φ γ).prop.1⟩,
        have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.p.support := λ γ, (φ γ).prop.2,
        have ψ_inj : injective ψ := λ i j h, P.disjoint (h₁ i) (by { rw h, exact h₁ j }),
        have := fintype.card_le_of_injective ψ ψ_inj,
        simp_rw [←fintype.card_coe], convert this,
    end

    lemma upper_bound (P : path_set G A B) : fintype.card P.to_finset ≤ min_cut G A B :=
    begin
        have h₁ := well_founded.min_mem nat.lt_wf (cut_set_sizes G A B)
            (set.range_nonempty_iff_nonempty.mpr nonempty_cut_set),
        obtain ⟨X,hX⟩ := subtype_of_exists h₁, simp at hX, rw [min_cut,←hX,fintype.card_coe],
        exact path_le_cut
    end

    -- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
    -- sorry
end simple_graph

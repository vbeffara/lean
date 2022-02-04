import combinatorics.simple_graph.connectivity data.finset
open finset classical function

variables {V : Type} [decidable_eq V] {G : simple_graph V} {A B : finset V}

namespace simple_graph
    structure AB_path (G : simple_graph V) (A B : finset V) := (a : A) (b : B) (p : walk G a b)

    def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
    ∀ γ : AB_path G A B, ∃ z : V, z ∈ X ∧ z ∈ γ.p.support

    structure cut_set (G : simple_graph V) (A B : finset V) extends (finset V) :=
        (disjoint : to_finset ∩ (A ∪ B) = ∅)
        (sep : separates G A B to_finset)

    def separable (G : simple_graph V) (A B : finset V) : Prop :=
    nonempty (cut_set G A B)

    def cut_set_sizes (G : simple_graph V) (A B : finset V) : set ℕ :=
    set.range (λ X : cut_set G A B, X.to_finset.card)

    noncomputable def min_cut (h : separable G A B) : ℕ :=
    well_founded.min nat.lt_wf (cut_set_sizes G A B) $ set.range_nonempty_iff_nonempty.mpr h

    def joinable (G : simple_graph V) (A B : finset V) : Prop :=
    ∃ (a : A) (b : B), nonempty (G.walk a b)

    structure path_set (G : simple_graph V) (A B : finset V) :=
        (size : ℕ)
        (path : fin size → AB_path G A B)
        (disjoint : ∀ {i j : fin size} {z : V}, z ∈ (path i).p.support → z ∈ (path j).p.support → i = j)

    lemma path_le_cut {P : path_set G A B} {X : cut_set G A B} : P.size ≤ X.to_finset.card :=
    begin
        let φ : Π i : fin P.size, {z : V // z ∈ X.to_finset ∧ z ∈ (P.path i).p.support} :=
            λ i, subtype_of_exists (X.sep (P.path i)),
        let ψ : fin P.size → X.to_finset := λ i, ⟨φ i, (φ i).prop.1⟩,
        have h₁ : ∀ i, (ψ i).val ∈ (P.path i).p.support := λ i, (φ i).prop.2,
        have ψ_inj : injective ψ := λ i j h, P.disjoint (h₁ i) (by { rw h, exact h₁ j }),
        have := fintype.card_le_of_injective ψ ψ_inj,
        simp only [fintype.card_fin, fintype.card_coe] at this, exact this
    end

    lemma upper_bound (h : separable G A B) (P : path_set G A B) : P.size ≤ min_cut h :=
    begin
        have h₁ := well_founded.min_mem nat.lt_wf (cut_set_sizes G A B) (set.range_nonempty_iff_nonempty.mpr h),
        obtain ⟨X,hX⟩ := subtype_of_exists h₁, simp at hX, rw [min_cut,←hX], exact path_le_cut
    end

    -- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
    -- sorry
end simple_graph

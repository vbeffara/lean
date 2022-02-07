import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward
open finset classical function
open_locale classical

variables {V : Type} [decidable_eq V] [fintype V] {G : simple_graph V} [decidable_rel G.adj] {A B : finset V}

namespace simple_graph
    structure AB_path (G : simple_graph V) (A B : finset V) :=
        {a b : V} (p : walk G a b) (ha : a ∈ A) (hb : b ∈ B)

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

    structure path_set (G : simple_graph V) (A B : finset V) :=
        (P : finset (AB_path G A B))
        (disjoint : ∀ {γ₁ γ₂ : P} {z : V}, z ∈ γ₁.val.p.support → z ∈ γ₂.val.p.support → γ₁ = γ₂)

    lemma path_le_cut {P : path_set G A B} {X : cut_set G A B} : P.P.card ≤ X.X.card :=
    begin
        let φ : Π γ : P.P, {z : V // z ∈ X.X ∧ z ∈ γ.val.p.support} :=
            λ γ, subtype_of_exists (X.sep γ),
        let ψ : P.P → X.X := λ γ, ⟨φ γ, (φ γ).prop.1⟩,
        have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.p.support := λ γ, (φ γ).prop.2,
        have ψ_inj : injective ψ := λ i j h, P.disjoint (h₁ i) (by { rw h, exact h₁ j }),
        have := fintype.card_le_of_injective ψ ψ_inj,
        simp_rw [←fintype.card_coe], convert this,
    end

    lemma upper_bound (P : path_set G A B) : fintype.card P.P ≤ min_cut G A B :=
    begin
        have h₁ := well_founded.min_mem nat.lt_wf (cut_set_sizes G A B)
            (set.range_nonempty_iff_nonempty.mpr nonempty_cut_set),
        obtain ⟨X,hX⟩ := subtype_of_exists h₁, simp at hX, rw [min_cut,←hX,fintype.card_coe],
        exact path_le_cut
    end

    lemma bot_iff_no_edge : ∥G∥ = 0 ↔ G = ⊥ :=
    begin
        split; intro h,
        { ext x y, simp, intro h₁, let xy : sym2 V := ⟦(x,y)⟧,
            have h₂ : xy ∈ G.edge_set := h₁,
            let e : G.edge_set := ⟨⟦(x,y)⟧,h₂⟩,
            have := fintype.card_eq_zero_iff.mp h,
            exact is_empty_iff.mp this e },
        { simp_rw h, apply fintype.card_eq_zero_iff.mpr,
            apply is_empty_iff.mpr, rintro ⟨e,h₁⟩,
            induction e, change false at h₁, contradiction, refl }
    end

    lemma bot_separates_if {X : finset V} : separates ⊥ A B X ↔ (A ∩ B) ⊆ X :=
    begin
        split; intro h,
        { rintros z hz, simp at hz,
            let γ : AB_path ⊥ A B := ⟨(walk.nil : walk ⊥ z z), hz.1, hz.2⟩,
            rcases (h γ) with ⟨x,h₁,h₂⟩, simp at h₂, subst x, exact h₁ },
        { rintro ⟨a,b,γ,ha,hb⟩, cases γ, swap, change false at γ_h, contradiction,
            simp, apply mem_of_subset h, simp, exact ⟨ha,hb⟩ }
    end

    lemma bot_min_cut : min_cut ⊥ A B = (A ∩ B).card :=
    begin
        sorry
    end

    noncomputable def bot_path_set (A B : finset V) : {P : path_set ⊥ A B // P.P.card = (A ∩ B).card} :=
    begin
        let φ : A ∩ B → AB_path ⊥ A B :=
        by { intro z,
            have h' : z.val ∈ A ∧ z.val ∈ B := mem_inter.mp z.property,
            exact AB_path.mk walk.nil h'.1 h'.2
        },
        let S := image φ univ,

        have φ_inj : injective φ := by {
            rintros ⟨x,hx⟩ ⟨y,hy⟩ h, simp [φ] at h, cases h, subst y
        },

        have good_card : S.card = (A ∩ B).card := by {
            rw card_image_of_injective univ φ_inj,
            rw finset.card_univ,
            convert fintype.card_of_finset (A ∩ B) _,
            intro z, simp, split,
            { rintros ⟨h₁,h₂⟩, exact set.mem_sep h₁ h₂ },
            { rintros h₁, exact h₁ }
        },

        refine ⟨path_set.mk S _, good_card⟩,

        rintro ⟨⟨a₁,b₁,γ₁,h₁,h₂⟩,h₃⟩, cases γ₁, swap, change false at γ₁_h, contradiction,
        rintro ⟨⟨a₂,b₂,γ₂,h₄,h₅⟩,h₆⟩, cases γ₂, swap, change false at γ₂_h, contradiction,
        simp only [walk.support_nil, list.mem_singleton, subtype.mk_eq_mk, and_self_left, forall_eq],
        intro a₁a₂, subst a₁a₂, simp only [eq_self_iff_true, heq_iff_eq, and_self]
    end

    lemma lower_bound_aux (n : ℕ) : ∀ (G : simple_graph V), ∥G∥ = n → ∃ P : path_set G A B, P.P.card = G.min_cut A B :=
    begin
        induction n using nat.strong_induction_on with n ih, simp at ih,
        by_cases (n=0),
        { subst n, intros G hG, replace hG := bot_iff_no_edge.mp hG, subst G,
            let P := bot_path_set A B, use P.val, convert P.prop, exact bot_min_cut },
        { sorry }
    end

    lemma lower_bound : ∃ P : path_set G A B, P.P.card = G.min_cut A B :=
    begin
        apply lower_bound_aux, exact rfl
    end

    -- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
    -- sorry
end simple_graph

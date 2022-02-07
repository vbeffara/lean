import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward graph_theory.basic
open finset classical function
open_locale classical

variables {V : Type} [fintype V] {G : simple_graph V}

namespace simple_graph
    namespace menger
        variables {A B X : finset V}

        structure AB_path (G : simple_graph V) (A B : finset V) :=
            {a b : V} (p : walk G a b) (ha : a ∈ A) (hb : b ∈ B)

        def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
        ∀ γ : AB_path G A B, ∃ z : V, z ∈ X ∧ z ∈ γ.p.support

        lemma separates_self : separates G A B A :=
        λ γ, ⟨γ.a, ⟨γ.ha, γ.p.start_mem_support⟩⟩

        lemma nonempty_cut_set : ∃ X : finset V, separates G A B X :=
        ⟨A, separates_self⟩

        def is_cut_set_size (G : simple_graph V) (A B : finset V) (n : ℕ) : Prop :=
        ∃ X : finset V, X.card = n ∧ separates G A B X

        noncomputable def min_cut (G : simple_graph V) (A B : finset V) : ℕ :=
        @nat.find (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩

        variables {P : finset (AB_path G A B)}

        def pairwise_disjoint (P : finset (AB_path G A B)) : Prop :=
        ∀ {γ₁ γ₂ : P} {z : V}, z ∈ γ₁.val.p.support → z ∈ γ₂.val.p.support → γ₁ = γ₂

        lemma path_le_cut {dis : pairwise_disjoint P} {sep : separates G A B X} : P.card ≤ X.card :=
        begin
            let φ : Π γ : P, {z : V // z ∈ X ∧ z ∈ γ.val.p.support} :=
                λ γ, subtype_of_exists (sep γ),
            let ψ : P → X := λ γ, ⟨φ γ, (φ γ).prop.1⟩,
            have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.p.support := λ γ, (φ γ).prop.2,
            have ψ_inj : injective ψ := λ i j h, dis (h₁ i) (by { rw h, exact h₁ j }),
            have := fintype.card_le_of_injective ψ ψ_inj,
            simp_rw [←fintype.card_coe], convert this,
        end

        lemma upper_bound (dis : pairwise_disjoint P) : P.card ≤ min_cut G A B :=
        begin
            obtain ⟨X,hX⟩ := @nat.find_spec (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
            rw [min_cut,←hX.1], apply path_le_cut, assumption, exact hX.2
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

        lemma bot_separates_iff : separates ⊥ A B X ↔ (A ∩ B) ⊆ X :=
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
            apply (nat.find_eq_iff _).mpr, simp [bot_separates_iff], split,
            { use A ∩ B, exact ⟨rfl,subset.rfl⟩ },
            { rintros n h₁ X rfl h₂, have := finset.card_le_of_subset h₂, linarith }
        end

        noncomputable def bot_path_set (A B : finset V) : {P : finset (AB_path ⊥ A B) // pairwise_disjoint P ∧ P.card = (A ∩ B).card} :=
        begin
            let φ : A ∩ B → AB_path ⊥ A B := by { intro z,
                have h' : z.val ∈ A ∧ z.val ∈ B := mem_inter.mp z.property,
                exact AB_path.mk walk.nil h'.1 h'.2 },
            have φ_inj : injective φ := λ _ _ h, by { simp only [φ] at h, ext, exact h.1 },

            refine ⟨image φ univ, _, _⟩,
            {
                rintro ⟨⟨a₁,b₁,γ₁,h₁,h₂⟩,h₃⟩, cases γ₁, swap, change false at γ₁_h, contradiction,
                rintro ⟨⟨a₂,b₂,γ₂,h₄,h₅⟩,h₆⟩, cases γ₂, swap, change false at γ₂_h, contradiction,
                simp only [walk.support_nil, list.mem_singleton, subtype.mk_eq_mk, and_self_left, forall_eq],
                intro a₁a₂, subst a₁a₂, simp only [eq_self_iff_true, heq_iff_eq, and_self]
            },
            {
                rw [card_image_of_injective univ φ_inj, finset.card_univ],
                convert fintype.card_of_finset (A ∩ B) _,
                intro z, simp, split,
                { rintros ⟨h₁,h₂⟩, exact set.mem_sep h₁ h₂ },
                { rintros h₁, exact h₁ }
            }
        end

        def proj (G : simple_graph V) (e : step G) (A : finset V) : set (G/e).vertices
            | (sum.inl x) := x.val ∈ A
            | (sum.inr _) := e.x ∈ A ∨ e.y ∈ A

        instance (e : step G) : fintype (proj G e A) := sorry

        lemma lower_bound_aux (n : ℕ) : ∀ (G : simple_graph V), ∥G∥ = n →
            ∃ P : finset (AB_path G A B), pairwise_disjoint P ∧ P.card = min_cut G A B :=
        begin
            -- We apply induction on ∥G∥.
            induction n using nat.strong_induction_on with n ih, simp at ih, by_cases (n=0),
            -- If G has no edge, then |A∩B| = k and we have k trivial AB paths.
            { subst n, intros G hG, replace hG := bot_iff_no_edge.mp hG, subst G,
                let P := bot_path_set A B, use P.val, convert P.prop, exact bot_min_cut },
            -- So we assume that G has an edge e = xy.
            { intros G hG, subst hG,
                have h₁ : 0 < ∥G∥, by { exact pos_iff_ne_zero.mpr h },
                have h₂ : 0 < fintype.card G.step, by { rw nb_edges_of_nb_steps, exact (1:ℕ).succ_mul_pos h₁ },
                have h₃ : fintype.card G.step ≠ 0, by { intro h, linarith },
                have h₄ : ¬ is_empty G.step, by { intro h, have := fintype.card_eq_zero_iff.mpr h, contradiction },
                have h₅ : nonempty G.step, by { exact not_is_empty_iff.mp h₄ },
                cases h₅ with e,
                -- If G has no k disjoint AB paths
                by_contradiction h₆, push_neg at h₆,
                have h₇ : ∀ (P : finset (AB_path G A B)), pairwise_disjoint P → finset.card P < min_cut G A B := by {
                    intros P h, apply lt_of_le_of_ne, apply upper_bound, assumption, apply h₆, assumption },
                -- then neither does G/e; here, we count the contracted vertex
                -- ve as an element of A (resp.B) in G/e if in G at least one of
                -- x,y lies in A (resp.B)
                let G₁ := G/e,
                let A₁ : finset G₁.vertices := set.to_finset (proj G e A),
                let B₁ : finset G₁.vertices := set.to_finset (proj G e B),
                let Φ : AB_path G₁ A₁ B₁ → AB_path G A B := sorry,
                have Φ_inj : injective Φ := sorry,
                have h₇ : ∀ (P₁ : finset (AB_path G₁ A₁ B₁)), pairwise_disjoint P₁ → P₁.card < min_cut G A B := by {
                    intros P₁ h₈, rw ← finset.card_image_of_injective P₁ Φ_inj, apply h₇, sorry
                },
                have h₈ : ∥G₁∥ < ∥G∥ := by sorry,
                specialize ih (∥G₁∥) h₈ G₁,
                sorry
            }
        end

        lemma lower_bound : ∃ P : finset (AB_path G A B), pairwise_disjoint P ∧ P.card = min_cut G A B :=
        begin
            apply lower_bound_aux, exact rfl
        end

        -- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
        -- sorry
    end menger
end simple_graph

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

        noncomputable def min_cut' (G : simple_graph V) (A B : finset V) :
            {n : ℕ // (is_cut_set_size G A B n) ∧ (∀ m < n, ¬is_cut_set_size G A B m) } :=
        begin
            let n := @nat.find (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
            have p₁ := @nat.find_spec (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
            have p₂ := λ m, @nat.find_eq_iff m (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
            exact ⟨n, p₁, ((p₂ n).mp rfl).2⟩
        end

        noncomputable def min_cut (G : simple_graph V) (A B : finset V) : ℕ :=
        (min_cut' G A B).val

        noncomputable lemma min_cut_set (G : simple_graph V) (A B : finset V) :
            {X : finset V // X.card = min_cut G A B ∧ separates G A B X} :=
        ⟨_,some_spec (min_cut' G A B).prop.1⟩

        variables {P : finset (AB_path G A B)}

        def pairwise_disjoint : finset (AB_path G A B) → Prop :=
        λ P, ∀ ⦃γ₁ γ₂ : P⦄ {z : V}, z ∈ γ₁.val.p.support → z ∈ γ₂.val.p.support → γ₁ = γ₂

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
            rw [min_cut], obtain ⟨n,h₁,h₂⟩ := min_cut' G A B, obtain ⟨X,rfl,h₄⟩ := h₁,
            refine path_le_cut, exact dis, exact h₄
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
        := λ z, ite (z = e.x) (e.x ∈ A ∨ e.y ∈ A) (z ∈ A)

        lemma lower_bound_aux (n : ℕ) : ∀ (G : simple_graph V), ∥G∥ = n →
            ∀ A B : finset V, ∃ P : finset (AB_path G A B), pairwise_disjoint P ∧ P.card = min_cut G A B :=
        begin
            -- We apply induction on ∥G∥.
            induction n using nat.strong_induction_on with n ih, simp at ih, by_cases (n=0),
            -- If G has no edge, then |A∩B| = k and we have k trivial AB paths.
            { subst n, intros G hG A B, replace hG := bot_iff_no_edge.mp hG, subst G,
                let P := bot_path_set A B, use P.val, convert P.prop, exact bot_min_cut },
            -- So we assume that G has an edge e = xy.
            { intros G hG A B, subst hG,
                have G_nonempty : nonempty G.step, by {
                    have : ¬ is_empty (G.edge_set) := h ∘ fintype.card_eq_zero_iff.mpr,
                    have h₁ : 0 < ∥G∥, by { exact pos_iff_ne_zero.mpr h },
                    have h₂ : 0 < fintype.card G.step, by { rw nb_edges_of_nb_steps, exact (1:ℕ).succ_mul_pos h₁ },
                    have h₃ : fintype.card G.step ≠ 0, by { intro h, linarith },
                    have h₄ : ¬ is_empty G.step := h₃ ∘ fintype.card_eq_zero_iff.mpr,
                    exact not_is_empty_iff.mp h₄
                },
                cases G_nonempty with e,

                -- If G has no k disjoint AB paths
                by_contradiction h₆, push_neg at h₆,
                replace h₆ : ∀ (P : finset (AB_path G A B)), pairwise_disjoint P → P.card < min_cut G A B := by {
                    intros P h, exact lt_of_le_of_ne (upper_bound h) (h₆ P h) },

                -- then neither does G/e; here, we count the contracted vertex
                -- ve as an element of A (resp.B) in G/e if in G at least one of
                -- x,y lies in A (resp.B)
                let G₁ := G/e,
                let A₁ : finset G₁.vertices := set.to_finset (proj G e A),
                let B₁ : finset G₁.vertices := set.to_finset (proj G e B),
                let Φ : AB_path G₁ A₁ B₁ ↪ AB_path G A B := sorry,
                have h₇ : ∀ (P₁ : finset (AB_path G₁ A₁ B₁)), pairwise_disjoint P₁ → P₁.card < min_cut G A B := by {
                    intros P₁ h₈, rw ← finset.card_image_of_injective P₁ Φ.injective, apply h₆, sorry
                },

                -- By the induction hypothesis, G/e contains an AB separator Y
                -- of fewer than k vertices.
                have h₁₂ : min_cut G₁ A₁ B₁ < min_cut G A B := by {
                    have h₈ : ∥G₁∥ < ∥G∥ := by sorry,
                    specialize ih (∥G₁∥) h₈ G₁ rfl A₁ B₁, rcases ih with ⟨P₁,h₉,h₁₀⟩,
                    rw ← h₁₀, exact h₇ P₁ h₉ },
                obtain ⟨Y,h₁₄,h₁₅⟩ := min_cut_set G₁ A₁ B₁,
                have h₁₆ : Y.card < min_cut G A B := by { rw h₁₄, exact h₁₂ },
                -- Among these must be the vertex ve, since otherwise Y ⊆ V
                -- would be an AB separator in G.
                have h₁₇ : e.x ∈ Y := by { by_contradiction, sorry },
                -- Then X := (Y-ve)∪{x,y} is an AB separator in G of exactly k
                -- vertices.
                let X := Y ∪ {e.y},
                have h₁₈ : separates G A B X := sorry,
                have h₁₉ : X.card = min_cut G A B := sorry,

                -- We now consider the graph G−e.
                let Gₑ : simple_graph V := {
                    adj := λ x y, ((x = e.x ∧ y = e.y) ∨ (x = e.y ∧ y = e.x)),
                    symm := λ x y h, by { cases h, right, exact h_1.symm, left, exact h_1.symm },
                    loopless := λ x h, by { cases h; { cases h_1, subst x, apply G.ne_of_adj e.h, rw h_1_right } }
                },
                let G₂ : simple_graph V := G \ Gₑ,
                -- Since x,y ∈ X, every AX separator in G−e is also an AB
                -- separator in G
                have h₂₀ : ∀ Z : finset V, separates G₂ A X Z → separates G A B Z := sorry,
                -- and hence contains at least k vertices
                have h₂₁ : ∀ Z : finset V, separates G₂ A X Z → min_cut G A B ≤ Z.card := sorry,
                -- So by induction there are k disjoint AX paths in G−e
                have h₂₂ : min_cut G₂ A X = min_cut G A B := sorry,
                have h₂₃ : ∃ P₂ : finset (AB_path G₂ A X), pairwise_disjoint P₂ ∧ P₂.card = min_cut G A B := by {
                    have : ∥ G₂ ∥ < ∥ G ∥ := sorry, rw ← h₂₂, apply ih (∥G₂∥) this, simp [number_of_edges] },

                -- and similarly there are k disjoint XB paths in G−e
                have h₂₄ : ∃ P₂ : finset (AB_path G₂ A X), pairwise_disjoint P₂ ∧ P₂.card = min_cut G A B := sorry,

                -- As X separates A from B, these two path systems do not meet
                -- outside X

                -- and can thus be combined to k disjoint AB paths.
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

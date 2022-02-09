import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward graph_theory.basic
open finset classical function
open_locale classical

variables {V V' : Type} {a : V} {G : simple_graph V}

namespace simple_graph
    @[ext] structure Walk (G : simple_graph V) := {a b : V} (p : G.walk a b)

    namespace Walk
        variables {e : G.step} {p q : G.Walk} {hep : e.y = p.a} {hpq : p.b = q.a}

        def nil (a : V) : G.Walk := ⟨(walk.nil : G.walk a a)⟩

        def cons (e : G.step) (p : G.Walk) (h : e.y = p.a) : G.Walk :=
        by { let h' := e.h, rw h at h', exact ⟨p.p.cons h'⟩ }

        def rec₀ {motive : G.Walk → Sort*} :
            (Π {u}, motive (Walk.nil u)) →
            (Π e p h, motive p → motive (cons e p h)) →
            Π p, motive p :=
        begin
            rintros h_nil h_cons ⟨a,b,p⟩, induction p with a a b c adj p ih,
            { exact h_nil },
            { exact h_cons ⟨adj⟩ ⟨p⟩ rfl ih }
        end

        lemma rec' {P : G.Walk → Prop} :
            (∀ {a}, P (nil a)) →
            (∀ e p h, P p → P (cons e p h)) →
            ∀ p, P p := rec₀

        def rec'' {α : Type} :
            (V → α) →
            (Π (e : G.step) (p : G.Walk) (h : e.y = p.a), α → α) →
            G.Walk → α :=
        @rec₀ _ _ (λ _, α)

        @[simp] lemma cons_a : (cons e p hep).a = e.x := rfl
        @[simp] lemma cons_b : (cons e p hep).b = p.b := rfl
        lemma cons_p : (cons e p hep).p = by { let h' := e.h, rw hep at h', exact p.p.cons h' } := rfl

        def append (p q : G.Walk) (hpq : p.b = q.a) : G.Walk :=
        by { let p' := p.p, rw hpq at p', exact ⟨p' ++ q.p⟩ }

        @[simp] lemma append_a : (append p q hpq).a = p.a := rfl
        @[simp] lemma append_b : (append p q hpq).b = q.b := rfl
        lemma append_p : (append p q hpq).p = by { let p' := p.p, rw hpq at p', exact p' ++ q.p } := rfl

        @[simp] lemma append_nil_left {haq : a = q.a} : append (nil a) q haq = q :=
        begin
            sorry
        end

        @[simp] lemma append_cons : append (cons e p hep) q hpq = cons e (append p q hpq) hep := sorry
    end Walk

    namespace menger
        variables  [fintype V] [fintype V'] {A B X : finset V}

        structure AB_path (G : simple_graph V) (A B : finset V) :=
            (p : Walk G) (ha : p.a ∈ A) (hb : p.b ∈ B)

        def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
        ∀ γ : AB_path G A B, ∃ z : V, z ∈ X ∧ z ∈ γ.p.p.support

        lemma separates_self : separates G A B A :=
        λ γ, ⟨γ.p.a, ⟨γ.ha, γ.p.p.start_mem_support⟩⟩

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
        λ P, ∀ ⦃γ₁ γ₂ : P⦄ {z : V}, z ∈ γ₁.val.p.p.support → z ∈ γ₂.val.p.p.support → γ₁ = γ₂

        lemma path_le_cut {dis : pairwise_disjoint P} {sep : separates G A B X} : P.card ≤ X.card :=
        begin
            let φ : Π γ : P, {z : V // z ∈ X ∧ z ∈ γ.val.p.p.support} :=
                λ γ, subtype_of_exists (sep γ),
            let ψ : P → X := λ γ, ⟨φ γ, (φ γ).prop.1⟩,
            have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.p.p.support := λ γ, (φ γ).prop.2,
            have ψ_inj : injective ψ := λ i j h, dis (h₁ i) (by { rw h, exact h₁ j }),
            have := fintype.card_le_of_injective ψ ψ_inj,
            simp_rw [←fintype.card_coe], convert this,
        end

        lemma upper_bound (dis : pairwise_disjoint P) : P.card ≤ min_cut G A B :=
        begin
            rw [min_cut], obtain ⟨n,h₁,h₂⟩ := min_cut' G A B, obtain ⟨X,rfl,h₄⟩ := h₁,
            refine path_le_cut, exact dis, exact h₄
        end

        lemma bot_iff_no_edge : fintype.card G.step = 0 ↔ G = ⊥ :=
        begin
            split; intro h,
            { ext x y, simp, intro h₁, exact is_empty_iff.mp (fintype.card_eq_zero_iff.mp h) ⟨h₁⟩ },
            { rw h, exact fintype.card_eq_zero_iff.mpr (is_empty_iff.mpr step.h), }
        end

        lemma bot_separates_iff : separates ⊥ A B X ↔ (A ∩ B) ⊆ X :=
        begin
            split; intro h,
            { rintros z hz, simp at hz,
                let γ : AB_path ⊥ A B := ⟨⟨walk.nil⟩, hz.1, hz.2⟩,
                rcases (h γ) with ⟨x,h₁,h₂⟩, simp at h₂, subst x, exact h₁ },
            { rintro ⟨⟨a,b,γ⟩,ha,hb⟩, cases γ, swap, change false at γ_h, contradiction,
                simp, apply mem_of_subset h, simp, exact ⟨ha,hb⟩ }
        end

        lemma bot_min_cut : min_cut ⊥ A B = (A ∩ B).card :=
        begin
            apply (nat.find_eq_iff _).mpr, simp [bot_separates_iff], split,
            { use A ∩ B, exact ⟨rfl,subset.rfl⟩ },
            { rintros n h₁ X rfl h₂, have := finset.card_le_of_subset h₂, linarith }
        end

        noncomputable def bot_path_set (A B : finset V) : {P : finset (AB_path ⊥ A B) //
                                                            pairwise_disjoint P ∧ P.card = (A ∩ B).card} :=
        begin
            let φ : A ∩ B → AB_path ⊥ A B := by { intro z,
                have h' : z.val ∈ A ∧ z.val ∈ B := mem_inter.mp z.property,
                exact ⟨⟨walk.nil⟩,h'.1,h'.2⟩ },
            have φ_inj : injective φ := λ _ _ h, by { simp only [φ] at h, ext, exact h.1 },

            refine ⟨image φ univ, _, _⟩,
            {
                rintro ⟨⟨⟨a₁,b₁,γ₁⟩,h₁,h₂⟩,h₃⟩, cases γ₁, swap, change false at γ₁_h, contradiction,
                rintro ⟨⟨⟨a₂,b₂,γ₂⟩,h₄,h₅⟩,h₆⟩, cases γ₂, swap, change false at γ₂_h, contradiction,
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

        variables {f : V → V'} {p : G.Walk}

        -- TODO this will belong in pushforward or in contraction (push_path)
        -- TODO this is one of the points where `graph` would be more natural
        noncomputable def lower (f : V → V') (x y : V) (γ : walk G x y) :
            walk (push f G) (f x) (f y) :=
        begin
            induction γ with a a b c adj p ih, refl,
            by_cases f a = f b, rw h, exact ih,
            exact walk.cons ⟨h,a,b,rfl,rfl,adj⟩ ih
        end

        noncomputable def Lower (f : V → V') (p : G.Walk) : (push f G).Walk :=
        ⟨lower f p.a p.b p.p⟩

        @[simp] lemma Lower_nil : Lower f (@Walk.nil _ G a) = Walk.nil (f a) := rfl

        @[simp] lemma Lower_a : (Lower f p).a = f p.a := rfl
        @[simp] lemma Lower_b : (Lower f p).b = f p.b := rfl
        lemma Lower_p : (Lower f p).p = lower f p.a p.b p.p := rfl

        lemma lower_cons_eq (f : V → V') (x y z : V) (h : f x = f y) (e : G.adj x y) (p : G.walk y z) :
            lower f x z (e :: p) == lower f y z p :=
        by simp [lower,h]

        lemma Lower_cons_eq (f : V → V') (e : G.step) (p : G.Walk) (h₁ : e.y = p.a) (h₂ : f e.x = f e.y) :
            Lower f (p.cons e h₁) = Lower f p :=
        by simp [Lower,lower,Walk.cons,h₁,h₂]

        lemma lower_cons_ne (f : V → V') (x y z : V) (h : f x ≠ f y) (e : G.adj x y) (p : G.walk y z) :
            lower f x z (e :: p) = ⟨h,x,y,rfl,rfl,e⟩ :: lower f y z p :=
        by simp [lower,h]

        lemma Lower_cons_ne (f : V → V') (e : G.step) (p : G.Walk) (h₁ : e.y = p.a) (h₂ : f e.x ≠ f e.y) :
            Lower f (p.cons e h₁) = Walk.cons ⟨⟨h₂,e.x,e.y,rfl,rfl,e.h⟩⟩ (Lower f p) (congr_arg f h₁) :=
        by { sorry }

        lemma lower_append (f : V → V') (x y z : V) (p₁ : G.walk x y) (p₂ : G.walk y z) :
            lower f x z (p₁ ++ p₂) = lower f x y p₁ ++ lower f y z p₂ :=
        begin
            induction p₁ with a a b c h₁ p ih, refl,
            by_cases f a = f b,
            {
                have h₂ := lower_cons_eq f a b z h h₁ (p++p₂),
                simp, apply heq_iff_eq.mp, refine h₂.trans _, rw ih p₂,
                have h₃ := lower_cons_eq f a b c h h₁ p,
                sorry },
            { sorry }
        end

        lemma Lower_append (f : V → V') (p q : G.Walk) (hpq : p.b = q.a) :
            Lower f (Walk.append p q hpq) = Walk.append (Lower f p) (Lower f q) (by simp [hpq]) :=
        begin
            revert p, refine Walk.rec' _ _,
            { simp },
            { intros e p h ih hpq, by_cases h' : f e.x = f e.y,
                { have h₁ := Lower_cons_eq f e p h h',
                    have h₂ := Lower_cons_eq f e (Walk.append p q hpq) h h',
                    simp [h₁,h₂,ih] },
                { have h₁ := Lower_cons_ne f e p h h',
                    have h₂ := Lower_cons_ne f e (Walk.append p q hpq) h h',
                    simpa [h₁,h₂,ih] } }
        end

        lemma lower_nil (f : V → V') (x y : V) (p : walk G x y) (hp : ∀ (z : V), z ∈ p.support → f z = f y) :
            lower f x y p == (walk.nil : (push f G).walk (f y) (f y)) :=
        begin
            induction p with a a b c h₁ p ih, { refl },
            { by_cases f a = f b,
                { apply (lower_cons_eq f a b c h h₁ p).trans, apply ih,
                    intros z h, apply hp, right, exact h },
                { have := lower_cons_ne f a b c h h₁ p, rw this,
                    have : f a = f c, by { apply hp, left, refl }, rw this at h,
                    have : f b = f c, by { apply hp, right, exact p.start_mem_support }, rw this at h,
                    contradiction } }
        end

        -- TODO this will belong in pushforward or in contraction (lift_path)
        noncomputable def raise (f : V → V') (hf : adapted' f G) (x' y' : V') (γ : walk (push f G) x' y')
            (x y : V) (hx : f x = x') (hy : f y = y') :
            {p : walk G x y // lower f x y p == γ} :=
        begin
            revert x y, induction γ with a a b c h₁ p ih,
            { rintros x y h₁ rfl,
                have h₂ := hf x y h₁,
                set p := some h₂ with hp, have h₃ := some_spec h₂, simp_rw ← hp at *,
                use p, exact lower_nil f x y p h₃ },
            { rintros x y rfl rfl, rcases h₁ with ⟨h₁,h₂⟩,
                set xx := some h₂ with hx, have h₃ := some_spec h₂, simp_rw ← hx at h₃,
                set yy := some h₃ with hy, have h₄ := some_spec h₃, simp_rw ← hy at h₄,
                rcases h₄ with ⟨h₄,h₅,h₆⟩,
                set p₁ := some (hf x xx h₄.symm) with hp₁, have h₇ := some_spec (hf x xx h₄.symm), simp_rw ← hp₁ at *,
                obtain ⟨p₂,hp₂⟩ := ih yy y h₅ rfl,
                use p₁.append (p₂.cons h₆), sorry }
        end

        lemma lower_raise (f : V → V') (hf : adapted' f G) (x y : V) (x' y' : V') (γ : walk (push f G) x' y')
            (hx : f x = x') (hy : f y = y') :
            lower f x y (raise f hf x' y' γ x y hx hy).val == γ :=
        (raise f hf x' y' γ x y hx hy).prop

        lemma lower_bound_aux (n : ℕ) : ∀ (G : simple_graph V), fintype.card G.step = n →
            ∀ A B : finset V, ∃ P : finset (AB_path G A B), pairwise_disjoint P ∧ P.card = min_cut G A B :=
        begin
            -- We apply induction on ∥G∥.
            induction n using nat.strong_induction_on with n ih,

            -- If G has no edge, then |A∩B| = k and we have k trivial AB paths.
            by_cases (n=0), { subst n, intros G hG A B, rw [bot_iff_no_edge.mp hG,bot_min_cut],
                exact (bot_path_set A B).exists_of_subtype },

            -- So we assume that G has an edge e = xy.
            rintros G rfl A B,
            cases not_is_empty_iff.mp (h ∘ fintype.card_eq_zero_iff.mpr) with e,

            -- If G has no k disjoint AB paths
            by_contradiction h₆, push_neg at h₆,
            replace h₆ : ∀ {P : finset (AB_path G A B)}, pairwise_disjoint P → P.card < min_cut G A B :=
                by { intros P h, exact lt_of_le_of_ne (upper_bound h) (h₆ P h) },

            -- then neither does G/e; here, we count the contracted vertex
            -- ve as an element of A (resp.B) in G/e if in G at least one of
            -- x,y lies in A (resp.B)
            let G₁ := G/e,
            let A₁ : finset G₁.vertices := set.to_finset (proj G e A),
            let B₁ : finset G₁.vertices := set.to_finset (proj G e B),

            let Φ : AB_path G₁ A₁ B₁ → AB_path G A B := sorry,
            have Φ_inj : injective Φ := sorry,
            have Φ_nip : ∀ {P}, pairwise_disjoint P → pairwise_disjoint (image Φ P) := sorry,

            have h₇ : ∀ (P₁ : finset (AB_path G₁ A₁ B₁)), pairwise_disjoint P₁ → P₁.card < min_cut G A B :=
                by { intros P₁ h₈, rw ← finset.card_image_of_injective P₁ Φ_inj, exact h₆ (Φ_nip h₈) },

            -- By the induction hypothesis, G/e contains an AB separator Y
            -- of fewer than k vertices.
            have h₁₂ : min_cut G₁ A₁ B₁ < min_cut G A B := by {
                have h₈ : fintype.card G₁.step < fintype.card G.step := by sorry,
                specialize ih (fintype.card G₁.step) h₈ G₁ rfl A₁ B₁, rcases ih with ⟨P₁,h₉,h₁₀⟩,
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
                have : fintype.card G₂.step < fintype.card G.step := sorry,
                rw ← h₂₂, apply ih (fintype.card G₂.step) this, simp [number_of_edges] },

            -- and similarly there are k disjoint XB paths in G−e
            have h₂₄ : ∃ P₂ : finset (AB_path G₂ A X), pairwise_disjoint P₂ ∧ P₂.card = min_cut G A B := sorry,

            -- As X separates A from B, these two path systems do not meet
            -- outside X

            -- and can thus be combined to k disjoint AB paths.
            sorry
        end

        lemma lower_bound : ∃ P : finset (AB_path G A B), pairwise_disjoint P ∧ P.card = min_cut G A B :=
        begin
            apply lower_bound_aux, exact rfl
        end

        -- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
        -- sorry
    end menger
end simple_graph

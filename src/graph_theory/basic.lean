import tactic
import combinatorics.simple_graph.basic

variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

namespace sym2
    variables {z z' : sym2 V} {x y : V}

    lemma eq_of_two_members (h : x ≠ y) (h1 : x ∈ z) (h2 : y ∈ z) (h3 : x ∈ z') (h4 : y ∈ z') : z = z'
        := ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm
end sym2

namespace simple_graph
    variables
    open function classical

    def adj.symm := G.symm

    @[ext] structure step (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace step
        variables {e e' : step G}

        @[simp] def ends (e : step G) : sym2 V := ⟦( e.x, e.y )⟧
        @[simp] def flip (e : step G) : step G := ⟨e.h.symm⟩

        @[simp] lemma ends_flip : e.flip.ends = e.ends := sym2.eq_swap

        lemma same_iff : (e' = e ∨ e' = flip e) <-> e.ends = e'.ends
            := by { split; intro h,
                { cases h; subst e', rw ends_flip },
                { replace h := sym2.eq_iff.mp h, cases e with x y h1, cases e' with x' y', dsimp at h,
                    cases h; { cases h, substs x' y', simp } }
            }
    end step

    def is_smaller (G : simple_graph V) (G' : simple_graph V') : Prop := ∃ f : G →g G', injective f

    infix ` ≼s `:50 := is_smaller

    def range (f : V → V') : Type := { y : V' // ∃ x : V, f x = y }

    def embed {f : V -> V'} (h : injective f) (G : simple_graph V) : simple_graph { y : V' // ∃ x : V, f x = y }
        := {
            adj := λ a b, G.adj (some a.property) (some b.property),
            symm := λ a b h, G.symm h,
            loopless := λ a, G.loopless _,
        }

    -- TODO : computable version of this taking a left inverse of f?
    noncomputable def embed_iso {f : V -> V'} {h : injective f} {G : simple_graph V} : G ≃g embed h G
        := let φ : V -> range f := λ x, ⟨f x, x, rfl⟩,
               ψ : range f -> V := λ y, some y.property in
            have left_inv : ∀ x, ψ (φ x) = x := λ x, h (some_spec (subtype.property (φ x))),
            have right_inv : ∀ y, φ (ψ y) = y := λ y, subtype.ext (some_spec y.property),
            have rel_iff : ∀ x y, G.adj (ψ (φ x)) (ψ (φ y)) <-> G.adj x y := λ x y, by rw [left_inv,left_inv],
            ⟨⟨φ,ψ,left_inv,right_inv⟩,rel_iff⟩

    def select (pred : V -> Prop) (G : simple_graph V) : simple_graph { x // pred x }
        := {
            adj := G.adj on subtype.val,
            symm := λ x y h, G.symm h,
            loopless := λ x, G.loopless _,
        }

    lemma embed_le_select {f : G →g G'} {f_inj : injective f} : embed f_inj G ≤ select (λ y, ∃ x, f x = y) G'
        := by { intros x y h, simp [select,on_fun], convert f.map_rel' h,
            exact (some_spec x.property).symm, exact (some_spec y.property).symm }

    namespace is_smaller
        @[refl] lemma refl : G ≼s G := ⟨⟨id, λ x y, id⟩, injective_id⟩

        @[trans] lemma trans : G ≼s G' -> G' ≼s G'' -> G ≼s G''
            | ⟨f₁,h₁⟩ ⟨f₂,h₂⟩ := ⟨f₂.comp f₁, injective.comp h₂ h₁⟩

        lemma iso_left : G ≃g G' -> G' ≼s G'' -> G ≼s G''
            | φ ⟨ψ,h⟩ := ⟨ψ.comp φ, (φ.to_equiv.injective_comp ⇑ψ).mpr h⟩

        lemma le_left : G ≤ H -> H ≼s G' -> G ≼s G'
            := sorry

        lemma select_left {pred : V -> Prop} : G ≼s G' -> select pred G ≼s G'
            := sorry

        lemma iso_right : G ≼s G' -> G' ≃g G'' -> G ≼s G''
            | ⟨ψ,h⟩ φ := ⟨φ.to_hom.comp ψ, (equiv.comp_injective ψ φ.to_equiv).mpr h⟩
    end is_smaller
end simple_graph

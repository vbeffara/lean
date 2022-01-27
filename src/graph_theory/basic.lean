import tactic
import combinatorics.simple_graph.basic data.set.basic
import graph_theory.to_mathlib

variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph
    variables
    open function classical set

    def image (f : V -> V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x y, x ≠ y ∧ ∃ x' y' : V, f x' = x ∧ f y' = y ∧ G.adj x' y',
        symm := λ x y ⟨h₀,x',y',h₁,h₂,h₃⟩, ⟨h₀.symm,y',x',h₂,h₁,h₃.symm⟩,
        loopless := λ x ⟨h₀,h⟩, h₀ rfl
    }

    lemma image.comp {f : V -> V'} {g : V' -> V''} : image (g∘f) G = image g (image f G) :=
    begin
        ext x'' y'', split,
        { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, refine ⟨h₁,f x,f y,rfl,rfl,_,x,y,rfl,rfl,h₄⟩,
            exact ne_of_apply_ne g h₁ },
        { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩,
            refine ⟨h₁,x,y,rfl,rfl,h₇⟩ }
    end

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

    -- TODO this does not use h really
    def embed {f : V -> V'} (h : injective f) (G : simple_graph V) : simple_graph (range f)
        := {
            adj := G.adj on (λ x, some x.prop),
            symm := λ _ _ h, G.symm h,
            loopless := λ _, G.loopless _,
        }

    -- TODO : computable version of this taking a left inverse of f?
    noncomputable def embed_iso {f : V -> V'} {f_inj : injective f} {G : simple_graph V} : G ≃g embed f_inj G
        := let  φ : V -> range f := λ x, ⟨f x, x, rfl⟩,
                ψ : range f -> V := λ y, some y.prop,
                α : ∀ x, ψ (φ x) = x := λ x, f_inj (some_spec (subtype.prop (φ x))),
                β : ∀ x y, G.adj (ψ (φ x)) (ψ (φ y)) <-> G.adj x y := λ x y, by { rw [α,α] } in {
            to_fun := φ,
            inv_fun := ψ,
            left_inv := α,
            right_inv := λ y, subtype.ext (some_spec y.prop),
            map_rel_iff' := β
        }

    def pred_on (G : simple_graph V) : Type := V -> Prop

    def select (P : pred_on G) : simple_graph (subtype P)
        := {
            adj := G.adj on subtype.val,
            symm := λ _ _ h, G.symm h,
            loopless := λ x, G.loopless _,
        }

    lemma embed_le_select {f : G →g G'} {f_inj : injective f} : embed f_inj G ≤ @select V' G' (λ y, ∃ x, f x = y)
        := by { intros x y h, simp [select,on_fun], convert f.map_rel' h,
            exact (some_spec x.property).symm, exact (some_spec y.property).symm }

    namespace is_smaller
        @[refl] lemma refl : G ≼s G := ⟨⟨id, λ x y, id⟩, injective_id⟩

        @[trans] lemma trans : G ≼s G' -> G' ≼s G'' -> G ≼s G''
            | ⟨f₁,h₁⟩ ⟨f₂,h₂⟩ := ⟨f₂.comp f₁, injective.comp h₂ h₁⟩

        lemma iso_left : G ≃g G' -> G' ≼s G'' -> G ≼s G''
            | φ ⟨ψ,h⟩ := ⟨ψ.comp φ, (φ.to_equiv.injective_comp ⇑ψ).mpr h⟩

        lemma le_left : G ≤ H -> H ≼s G' -> G ≼s G'
            | h₁ ⟨⟨f,h₂⟩,h₃⟩ := ⟨⟨f,λ _ _ h, h₂ (h₁ h)⟩,h₃⟩

        lemma select_left {pred : pred_on G} : G ≼s G' -> select pred ≼s G'
            | ⟨⟨f,h₁⟩,h₂⟩ :=
                let g : {x // pred x} -> V' := f ∘ subtype.val
                in ⟨⟨g,λ a b,h₁⟩,h₂.comp subtype.val_injective⟩

        lemma iso_right : G ≼s G' -> G' ≃g G'' -> G ≼s G''
            | ⟨ψ,h⟩ φ := ⟨φ.to_hom.comp ψ, (equiv.comp_injective ψ φ.to_equiv).mpr h⟩
    end is_smaller
end simple_graph

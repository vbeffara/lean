import combinatorics.simple_graph.basic data.set.basic
import graph_theory.to_mathlib
open function set classical

variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {f : V → V'} {g : V' → V''}

namespace simple_graph
    def pullback (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := G'.adj on f,
        symm := λ _ _ h, G'.symm h,
        loopless := λ _, G'.loopless _
    }

    namespace pullback
        lemma comp : pullback (g∘f) = pullback f ∘ pullback g :=
        by { ext G'' x y, exact iff.rfl }

        def to_iso (f : V ≃ V') (G' : simple_graph V') : pullback f G' ≃g G' :=
        ⟨f,λ x y, iff.rfl⟩

        lemma from_iso (φ : G ≃g G') : pullback φ G' = G :=
        by { ext x y, have := φ.map_rel_iff', exact this }
    end pullback

    def pushforward (f : V → V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x' y', x' ≠ y' ∧ ∃ x y : V, f x = x' ∧ f y = y' ∧ G.adj x y,
        symm := λ x' y' ⟨h₀,x,y,h₁,h₂,h₃⟩, ⟨h₀.symm,y,x,h₂,h₁,h₃.symm⟩,
        loopless := λ _ ⟨h₀,_⟩, h₀ rfl
    }

    namespace pushforward
        lemma comp : pushforward (g∘f) = pushforward g ∘ pushforward f :=
        begin
            ext G x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩ },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩, exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end

        lemma left_inv (h : injective f) : left_inverse (pullback f) (pushforward f) :=
        begin
            intro G, ext x y, split,
            { rintro ⟨-,xx,yy,h₂,h₃,h₄⟩, rw [←h h₂,←h h₃], exact h₄ },
            { intro h₁, exact ⟨h.ne (G.ne_of_adj h₁),x,y,rfl,rfl,h₁⟩ }
        end

        lemma right_inv (h : surjective f) : right_inverse (pullback f) (pushforward f) :=
        begin
            intro G', ext x' y', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₂⟩, exact h₂ },
            { intro h₁, cases h x' with x, cases h y' with y, substs x' y', exact ⟨G'.ne_of_adj h₁,x,y,rfl,rfl,h₁⟩ }
        end

        def to_iso (f : V ≃ V') (G : simple_graph V) : G ≃g pushforward f G :=
        begin
            convert ← pullback.to_iso f _, apply left_inv f.left_inv.injective
        end

        lemma from_iso (φ : G ≃g G') : G' = pushforward φ G :=
        begin
            convert ← congr_arg _ (pullback.from_iso φ), apply right_inv φ.right_inv.surjective
        end
    end pushforward

    def select (P : V → Prop) (G : simple_graph V) : simple_graph (subtype P) :=
    pullback subtype.val G

    namespace select
        def push_pred_iso (P : V → Prop) (φ : G ≃g G') : select P G ≃g select (P ∘ φ.inv_fun) G' :=
        {
            to_fun := λ x, ⟨φ x.val, by { rw [comp_app], convert x.property, apply φ.left_inv }⟩,
            inv_fun := λ y, ⟨φ.symm y.val, y.property⟩,
            left_inv := λ x, by simp only [rel_iso.symm_apply_apply,subtype.coe_eta,subtype.val_eq_coe],
            right_inv := λ x, by simp only [subtype.coe_eta,rel_iso.apply_symm_apply,subtype.val_eq_coe],
            map_rel_iff' := λ a b, by { apply φ.map_rel_iff' }
        }
    end select

    def embed (f : V → V') : simple_graph V → simple_graph (range f) :=
    select (range f) ∘ pushforward f

    namespace embed
        -- TODO : computable version of this taking a left inverse of f?
        noncomputable def iso (f_inj : injective f) : G ≃g embed f G :=
        let φ : V → range f := λ x, ⟨f x, x, rfl⟩,
            ψ : range f → V := λ y, some y.prop in
        {
            to_fun := φ,
            inv_fun := ψ,
            left_inv := λ x, f_inj (some_spec (subtype.prop (φ x))),
            right_inv := λ y, subtype.ext (some_spec y.prop),
            map_rel_iff' := by {
                simp [φ,embed,pushforward,select,pullback,on_fun],
                simp_rw [subtype.coe_mk], intros a b, split,
                { rintro ⟨h₁,x,h₂,y,h₃,h₄⟩, rwa [←f_inj h₂,←f_inj h₃] },
                { intro h₁, exact ⟨f_inj.ne (G.ne_of_adj h₁),a,rfl,b,rfl,h₁⟩ }
            }
        }

        lemma le_select {f : G →g G'} (f_inj : injective f) : embed f G ≤ select (range f) G' :=
        begin
            intros x' y', simp [embed,pushforward,select,pullback,on_fun],
            intros h₁ x h₂ y h₃, rw [←h₂,←h₃], exact f.map_rel
        end
    end embed
end simple_graph

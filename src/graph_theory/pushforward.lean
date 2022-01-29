import combinatorics.simple_graph.basic data.set.basic
import graph_theory.to_mathlib
open function set classical

variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {f : V → V'} {g : V' → V''}

namespace simple_graph
    def pushforward (f : V → V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x' y', x' ≠ y' ∧ ∃ x y : V, f x = x' ∧ f y = y' ∧ G.adj x y,
        symm := λ x' y' ⟨h₀,x,y,h₁,h₂,h₃⟩, ⟨h₀.symm,y,x,h₂,h₁,h₃.symm⟩,
        loopless := λ _ ⟨h₀,_⟩, h₀ rfl
    }

    namespace pushforward
        def to_iso (f : V ≃ V') (G : simple_graph V) : G ≃g pushforward f G :=
        {
            to_equiv := f,
            map_rel_iff' := λ x y, by { split,
                { rintro ⟨h₁,x',y',h₂,h₃,h₄⟩, rwa [←f.left_inv.injective h₂,←f.left_inv.injective h₃] },
                { intro h, exact ⟨f.left_inv.injective.ne (G.ne_of_adj h),x,y,rfl,rfl,h⟩ }
            }
        }

        lemma from_iso (φ : G ≃g G') : G' = pushforward φ G :=
        begin
            ext x' y', split,
            { intro h, refine ⟨G'.ne_of_adj h, φ.inv_fun x', φ.inv_fun y', φ.right_inv _, φ.right_inv _, _⟩,
                rw [←φ.map_rel_iff'], rwa [←φ.right_inv x',←φ.right_inv y'] at h },
            { rintro ⟨h₁,x,y,rfl,rfl,h₂⟩, rwa ←φ.map_rel_iff' at h₂ }
        end

        lemma comp : pushforward (g∘f) = pushforward g ∘ pushforward f :=
        begin
            ext x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩ },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩, exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end
    end pushforward

    def pullback (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := G'.adj on f,
        symm := λ _ _ h, G'.symm h,
        loopless := λ _, G'.loopless _
    }

    namespace pullback
        def to_iso (f : V ≃ V') (G' : simple_graph V') : pullback f G' ≃g G' :=
        ⟨f,λ x y, iff.rfl⟩

        lemma from_iso (φ : G ≃g G') : pullback φ G' = G :=
        by { ext x y, have := φ.map_rel_iff', exact this }

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
    end pullback

    def select (G : simple_graph V) (P : V → Prop) : simple_graph (subtype P) :=
    pullback subtype.val G

    namespace select
        def push_pred_iso (P : V → Prop) (φ : G ≃g G') : select G P ≃g select G' (P ∘ φ.inv_fun) :=
        {
            to_fun := λ x, ⟨φ x.val, by { rw [comp_app], convert x.property, apply φ.left_inv }⟩,
            inv_fun := λ y, ⟨φ.symm y.val, y.property⟩,
            left_inv := λ x, by simp only [rel_iso.symm_apply_apply,subtype.coe_eta,subtype.val_eq_coe],
            right_inv := λ x, by simp only [subtype.coe_eta,rel_iso.apply_symm_apply,subtype.val_eq_coe],
            map_rel_iff' := λ a b, by { apply φ.map_rel_iff' }
        }
    end select

    def embed (f : V → V') (G : simple_graph V) : simple_graph (range f) :=
    (pushforward f G).select (range f)

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

        lemma le_select {f : G →g G'} (f_inj : injective f) : embed f G ≤ select G' (λ y, ∃ x, f x = y) :=
        begin
            intros x' y', simp [embed,pushforward,select,pullback,on_fun],
            intros h₁ x h₂ y h₃, rw [←h₂,←h₃], exact f.map_rel
        end
    end embed
end simple_graph

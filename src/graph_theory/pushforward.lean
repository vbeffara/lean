import combinatorics.simple_graph.basic data.set.basic
import graph_theory.to_mathlib
open function set classical

variables {V V' V'' : Type} {G G₁ G₂ : simple_graph V} {G' G'₁ G'₂ : simple_graph V'} {f : V → V'} {g : V' → V''}

namespace simple_graph
    def pull (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := G'.adj on f,
        symm := λ _ _ h, G'.symm h,
        loopless := λ _, G'.loopless _
    }

    namespace pull
        lemma comp : pull (g∘f) = pull f ∘ pull g :=
        by { ext G'' x y, exact iff.rfl }

        def to_iso (f : V ≃ V') (G' : simple_graph V') : pull f G' ≃g G' :=
        ⟨f,λ x y, iff.rfl⟩

        lemma from_iso (φ : G ≃g G') : pull φ G' = G :=
        by { ext x y, have := φ.map_rel_iff', exact this }

        lemma mono : monotone (pull f) :=
        by { intros G'₁ G'₂ h x' y', apply h }
    end pull

    def push (f : V → V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x' y', x' ≠ y' ∧ ∃ x y : V, f x = x' ∧ f y = y' ∧ G.adj x y,
        symm := λ x' y' ⟨h₀,x,y,h₁,h₂,h₃⟩, ⟨h₀.symm,y,x,h₂,h₁,h₃.symm⟩,
        loopless := λ _ ⟨h₀,_⟩, h₀ rfl
    }

    namespace push
        lemma comp : push (g∘f) = push g ∘ push f :=
        begin
            ext G x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩ },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩, exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end

        lemma left_inv (h : injective f) : left_inverse (pull f) (push f) :=
        begin
            intro G, ext x y, split,
            { rintro ⟨-,xx,yy,h₂,h₃,h₄⟩, rw [←h h₂,←h h₃], exact h₄ },
            { intro h₁, exact ⟨h.ne (G.ne_of_adj h₁),x,y,rfl,rfl,h₁⟩ }
        end

        lemma right_inv (h : surjective f) : right_inverse (pull f) (push f) :=
        begin
            intro G', ext x' y', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₂⟩, exact h₂ },
            { intro h₁, cases h x' with x, cases h y' with y, substs x' y', exact ⟨G'.ne_of_adj h₁,x,y,rfl,rfl,h₁⟩ }
        end

        def to_iso (f : V ≃ V') (G : simple_graph V) : G ≃g push f G :=
        begin
            convert ← pull.to_iso f _, apply left_inv f.left_inv.injective
        end

        lemma from_iso (φ : G ≃g G') : G' = push φ G :=
        begin
            convert ← congr_arg _ (pull.from_iso φ), apply right_inv φ.right_inv.surjective
        end

        lemma mono : monotone (push f) :=
        by { rintros G₁ G₂ h₁ x' y' ⟨h₂,x,y,rfl,rfl,h₃⟩, exact ⟨h₂,x,y,rfl,rfl,h₁ h₃⟩ }

        lemma le {φ : G →g G'} : push φ G ≤ G' :=
        by { rintros x' y' ⟨-,x,y,rfl,rfl,h₂⟩, exact φ.map_rel h₂ }
    end push

    def select (P : V → Prop) (G : simple_graph V) : simple_graph (subtype P) :=
    pull subtype.val G

    namespace select
        lemma le {P : V -> Prop} : G₁ ≤ G₂ → select P G₁ ≤ select P G₂
        := by { apply pull.mono }

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
    select (range f) ∘ push f

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
                simp [φ,embed,push,select,pull,on_fun],
                simp_rw [subtype.coe_mk], intros a b, split,
                { rintro ⟨h₁,x,h₂,y,h₃,h₄⟩, rwa [←f_inj h₂,←f_inj h₃] },
                { intro h₁, exact ⟨f_inj.ne (G.ne_of_adj h₁),a,rfl,b,rfl,h₁⟩ }
            }
        }

        lemma le_select {f : G →g G'} (f_inj : injective f) : embed f G ≤ select (range f) G' :=
        select.le push.le
    end embed
end simple_graph

import combinatorics.simple_graph.basic combinatorics.simple_graph.connectivity data.set.basic
import graph_theory.to_mathlib
open function set classical

variables {V V' V'' : Type} {x y z : V} {f : V → V'} {g : V' → V''}
variables {G G₁ G₂ : simple_graph V} {G' G'₁ G'₂ : simple_graph V'}

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
        lemma adj (f : V → V') : G.adj x y → f x = f y ∨ (push f G).adj (f x) (f y) :=
        by { intro h₁, by_cases f x = f y, left, exact h, right, exact ⟨h,x,y,rfl,rfl,h₁⟩ }

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
        variables {P : V → Prop}

        lemma mono {P : V → Prop} : monotone (select P)
        := by { apply pull.mono }

        def push_pred_iso (P : V → Prop) (φ : G ≃g G') : select P G ≃g select (P ∘ φ.inv_fun) G' :=
        {
            to_fun := λ x, ⟨φ x.val, by { rw [comp_app], convert x.property, apply φ.left_inv }⟩,
            inv_fun := λ y, ⟨φ.symm y.val, y.property⟩,
            left_inv := λ x, by simp only [rel_iso.symm_apply_apply,subtype.coe_eta,subtype.val_eq_coe],
            right_inv := λ x, by simp only [subtype.coe_eta,rel_iso.apply_symm_apply,subtype.val_eq_coe],
            map_rel_iff' := λ a b, by { apply φ.map_rel_iff' }
        }

        def push_walk (p : walk G x y) (hp : ∀ z ∈ p.support, P z) :
            walk (select P G) ⟨x, hp x (walk.start_mem_support p)⟩ ⟨y, hp y (walk.end_mem_support p)⟩ :=
        begin
            induction p with a a b c h₁ p ih, refl,
            have hp' : ∀ z ∈ p.support, P z := by { intros z hz, apply hp, right, exact hz },
            refine walk.cons _ (ih hp'), exact h₁
        end

        def pull_walk {x y} (p : walk (select P G) x y) : walk G x.val y.val :=
        by { induction p with a a b c h₁ p ih, refl, refine walk.cons h₁ ih }

        lemma pull_walk_spec {x y} (p : walk (select P G) x y) : ∀ z ∈ (pull_walk p).support, P z :=
        by { induction p with a a b c h₁ p ih,
            { intros z hz, cases hz, rw hz, exact a.prop, cases hz },
            { intros z hz, cases hz, rw hz, exact a.prop, exact ih z hz }}
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
        select.mono push.le
    end embed

    def quotient_graph (G : simple_graph V) (S : setoid V) : simple_graph (quotient S) :=
    push quotient.mk G

    notation G `/` S := quotient_graph G S

    namespace quotient_graph
        variables {S : setoid V} {S' : setoid (quotient S)}

        lemma comp_eq : G/S/S' = push (setoid.comp.iso S S') (G/(S.comp S')) :=
        begin
            convert congr_fun (congr_arg push (setoid.comp.eq S S')) G using 1;
            { symmetry, rw [push.comp], refl }
        end

        lemma comp : G/(S.comp S') ≃g G/S/S'
        := by { rw comp_eq, exact push.to_iso _ _ }

        def iso_bot' : V ≃ quotient (⊥ : setoid V) :=
        {
            to_fun := quotient.mk',
            inv_fun := λ y, quotient.lift_on' y id (λ _ _, id),
            left_inv := λ x, by refl,
            right_inv := λ y, by { induction y; refl },
        }

        def iso_bot : G ≃g G/⊥ := push.to_iso iso_bot' G
    end quotient_graph
end simple_graph

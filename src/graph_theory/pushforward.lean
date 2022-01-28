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

    def pullback (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := G'.adj on f,
        symm := λ _ _ h, G'.symm h,
        loopless := λ _, G'.loopless _
    }

    def select (G : simple_graph V) (P : V -> Prop) : simple_graph (subtype P)
    := pullback subtype.val G

    def embed''' (f : V → V') (G : simple_graph V) : simple_graph (range f) :=
    (pushforward f G).select (range f)

    -- TODO : computable version of this taking a left inverse of f?
    noncomputable def embed'''_iso {f : V -> V'} (f_inj : injective f) {G : simple_graph V} : G ≃g embed''' f G :=
    begin
        let  φ : V -> range f := λ x, ⟨f x, x, rfl⟩,
        let  ψ : range f -> V := λ y, some y.prop,
        refine {
            to_fun := φ,
            inv_fun := ψ,
            left_inv := λ x, f_inj (some_spec (subtype.prop (φ x))),
            right_inv := λ y, subtype.ext (some_spec y.prop),
            map_rel_iff' := by {
                simp [φ,embed''',pushforward,select,pullback,on_fun],
                simp_rw [subtype.coe_mk], intros a b, split,
                { rintro ⟨h₁,x,h₂,y,h₃,h₄⟩, rwa [←f_inj h₂,←f_inj h₃] },
                { intro h₁, exact ⟨f_inj.ne (G.ne_of_adj h₁),a,rfl,b,rfl,h₁⟩ }
            }
        }
    end

    namespace pushforward
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

        lemma comp : pushforward (g∘f) = pushforward g ∘ pushforward f :=
        begin
            ext x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩ },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩, exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end
    end pushforward
end simple_graph

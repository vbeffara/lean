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

    def embed (f : V → V') (G : simple_graph V) : simple_graph (range f) :=
    {
        adj := G.adj on (λ x, some x.prop),
        symm := λ _ _ h, G.symm h,
        loopless := λ _, G.loopless _,
    }

    noncomputable def embed' (f : V → V') (G : simple_graph V) : simple_graph (range f) :=
    pullback (λ x, some x.prop) G

    example : embed f G = embed' f G := rfl

    def embed'' (f : V → V') (G : simple_graph V) : simple_graph (range f) :=
    pushforward (λ x, ⟨f x, set.mem_range_self x⟩) G

    def embed''' (f : V → V') (G : simple_graph V) : simple_graph (range f) :=
    (pushforward f G).select (λ y, ∃ x, f x = y)

    lemma embed_eq_of_inj (h : injective f) : embed' f G = embed'' f G :=
    begin
        have toto : ∀ {x h'}, some (⟨f x, h'⟩ : range f).prop = x :=
            λ x h', h (some_spec (⟨f x, h'⟩ : range f).prop),
        ext x' y',
        cases x' with x' h₁, cases h₁ with x h₁, subst x',
        cases y' with y' h₁, cases h₁ with y h₁, subst y',
        change G.adj (some (⟨f x, _⟩ : range f).prop) (some (⟨f y, _⟩ : range f).prop) ↔ (embed'' f G).adj ⟨f x, _⟩ ⟨f y, _⟩,
        rw [toto,toto], simp [toto,embed'',pushforward], split,
        { intro h', refine ⟨_,x,rfl,y,rfl,h'⟩, rw subtype.mk_eq_mk, exact h.ne (G.ne_of_adj h') },
        { rintro ⟨-,x',h₁,y',h₂,h₃⟩, rwa [←h (subtype.mk_eq_mk.mp h₁),←h (subtype.mk_eq_mk.mp h₂)] }
    end

    example : embed'' f G = embed''' f G :=
    begin
        ext x' y', cases x' with x' h₁, cases y' with y' h₂,
        simp [embed'',pullback,embed''',pushforward,select,on_fun],
        simp_rw [subtype.mk_eq_mk,subtype.coe_mk],
    end

    -- TODO : computable version of this taking a left inverse of f?
    noncomputable def embed_iso {f : V -> V'} (f_inj : injective f) {G : simple_graph V} : G ≃g embed f G
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

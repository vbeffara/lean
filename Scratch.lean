import tactic data.equiv.basic
open function

lemma setoid.r.symm {V : Type} {S : setoid V} : symmetric S.r :=
λ x y, setoid.symm

def setoid.comp {V : Type} (s : setoid V) (t : setoid (quotient s)) : setoid V :=
let f : V → quotient s := quotient.mk,
    g : quotient s → quotient t := quotient.mk
in setoid.ker (g ∘ f)

def setoid.comp.iso {V : Type} (s : setoid V) (t : setoid (quotient s)) :
    quotient (s.comp t) ≃ quotient t :=
by {
    let f : V -> quotient s := quotient.mk',
    let g : quotient s -> quotient t := quotient.mk',
    let h : V -> quotient (s.comp t) := quotient.mk',

    have p₁ : ∀ {a b}, f a = f b <-> s.rel a b := λ a b, quotient.eq',
    have p₂ : ∀ {a b}, g a = g b <-> t.rel a b := λ a b, quotient.eq',
    have p₃ : ∀ {a b}, h a = h b <-> g (f a) = g (f b) := λ a b, quotient.eq',
    have p₄ : ∀ a b, s.rel a b -> h a = h b := λ a b, by { rw [p₃,<-p₁], exact congr_arg g },

    let ζ : quotient s -> quotient (s.comp t) := λ y, y.lift_on' h p₄,

    have p₅ : ∀ a b, t.rel a b -> ζ a = ζ b := λ a b, by {
        refine a.induction_on' (λ x, _), refine b.induction_on' (λ y, _), rw [<-p₂], exact p₃.mpr
    },

    exact {
        to_fun := λ x, x.lift_on' (g ∘ f) (λ _ _, id),
        inv_fun := λ y, y.lift_on' (λ y, y.lift_on' h p₄) p₅,
        left_inv := λ x, quotient.induction_on' x (λ _, rfl),
        right_inv := λ y, quotient.induction_on' y (λ b, quotient.induction_on' b (λ _, rfl)),
    }
}

lemma setoid.comp.eq {V : Type} (s : setoid V) (t : setoid (quotient s)) :
    quotient.mk' ∘ quotient.mk' = setoid.comp.iso s t ∘ quotient.mk' := by refl

namespace quotient.quotient
    variables {V : Type*} (s : setoid V) (t : setoid (quotient s))

    def setoid.comp (s : setoid V) (t : setoid (quotient s)) : setoid V :=
        let f : V → quotient s := quotient.mk,
            g : quotient s → quotient t := quotient.mk
        in setoid.ker (g ∘ f)

    noncomputable def setoid.comp.iso : quotient (setoid.comp s t) ≃ quotient t :=
        let f : V → quotient s := quotient.mk,
            g : quotient s → quotient t := quotient.mk
        in setoid.quotient_ker_equiv_of_surjective (g ∘ f)
            ((surjective_quotient_mk (quotient s)).comp (surjective_quotient_mk V))

    noncomputable def setoid.comp.iso' : quotient (setoid.comp s t) ≃ quotient t :=
        let gof : V -> quotient t := quotient.mk ∘ quotient.mk
        in setoid.quotient_ker_equiv_of_surjective gof
            ((surjective_quotient_mk (quotient s)).comp (surjective_quotient_mk V))
end quotient.quotient

namespace v1 -- start with predicate on quotient
    variables {V : Type} {S : setoid V} {P : quotient S -> Prop}

    def lift_pred (P : quotient S -> Prop) : V -> Prop
        := P ∘ quotient.mk

    def subsetoid (P : quotient S -> Prop) : setoid (subtype (lift_pred P))
        := subtype.setoid (lift_pred P)

    def iso (S : setoid V) (P : quotient S -> Prop) : subtype P ≃ quotient (subsetoid P)
        := equiv.subtype_quotient_equiv_quotient_subtype (lift_pred P) P (λ a, iff.rfl) (λ a b, iff.rfl)
end v1

noncomputable def toto {V : Type} : V ≃ quotient (⊥ : setoid V)
:= {
        to_fun := @quotient.mk V ⊥,
        inv_fun := @quotient.out V ⊥,
        left_inv := λ y, by { letI : setoid V := ⊥, exact quotient.eq.mp (quotient.out_eq ⟦y⟧) },
        right_inv := @quotient.out_eq V ⊥,
    }

namespace tactic
    meta def take_pi_args : nat → expr → list name
    | (n+1) (expr.pi h _ _ e) := h :: take_pi_args n e
    | _ _ := []

    namespace interactive
        setup_tactic_parser

        meta def doneif (h : parse ident?) (t : parse (tk ":" *> texpr))
                        (revert : parse ( (tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure (some []))) :
        tactic unit := do
            let h := h.get_or_else `this,
            t ← i_to_expr ``(%%t : Sort*),
            (num_generalized, goal) ← retrieve (do
                assert_core h t, swap,
                num_generalized ← match revert with
                | none := revert_all
                | some revert := revert.mmap tactic.get_local >>= revert_lst
                end,
                goal ← target,
                return (num_generalized, goal)),
            tactic.assert h goal,
            goal ← target,
            (take_pi_args num_generalized goal).reverse.mmap' $ λ h,
                try (tactic.get_local h >>= tactic.clear),
            intron (num_generalized + 1)

        meta def wlog' (h : parse ident?) (t : parse (tk ":" *> texpr)) : tactic unit :=
        doneif h t none >> swap
    end interactive
end tactic

example (n : ℤ) (h : ∃ p q : ℤ, n = p * q) : n*n ≥ 0 :=
begin
    rcases h with ⟨p,q,h⟩, wlog' : p ≥ 0,
end

#reduce fintype.card ((fin 3) ⊕ (fin 4))

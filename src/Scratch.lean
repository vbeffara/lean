import tactic data.equiv.basic
open function

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

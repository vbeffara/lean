import tactic

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

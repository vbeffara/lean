import combinatorics.simple_graph.basic
import data.setoid.basic

lemma setoid.r.symm {V : Type} {S : setoid V} : symmetric S.r :=
λ x y, setoid.symm

def setoid.comp {V : Type} (s : setoid V) (t : setoid (quotient s)) : setoid V :=
let f : V → quotient s := quotient.mk,
    g : quotient s → quotient t := quotient.mk
in setoid.ker (g ∘ f)

def setoid.comp.iso {V : Type} {s : setoid V} {t : setoid (quotient s)} :
    quotient (setoid.comp s t) ≃ quotient t :=
by {
    let f : V -> quotient s := quotient.mk,
    let g : quotient s -> quotient t := quotient.mk',
    let h : V -> quotient (s.comp t) := quotient.mk',

    have p₁ : ∀ {a b}, f a = f b <-> s.rel a b := λ a b, quotient.eq',
    have p₂ : ∀ {a b}, g a = g b <-> t.rel a b := λ a b, quotient.eq',
    have p₃ : ∀ {a b}, h a = h b <-> (s.comp t).rel a b := λ a b, quotient.eq',
    have p₄ : ∀ {a b}, (s.comp t).rel a b <-> g (f a) = g (f b) := λ a b, setoid.ker_def,
    have p₅ : ∀ a b, s.rel a b -> h a = h b := λ a b, by { rw [p₃,p₄,<-p₁], apply congr_arg },

    let φ : quotient (setoid.comp s t) -> quotient t := λ x, quotient.lift_on' x (g ∘ f) (λ a b, id),
    let ζ : quotient s -> quotient (s.comp t) := λ y, quotient.lift_on' y h p₅,

    have p₆ : ∀ a b, t.rel a b -> ζ a = ζ b := λ a b, by {
        induction a, induction b, rw [<-p₂,p₃,p₄], exact id, exact (λ _, rfl), exact (λ _, rfl),
    },

    let ψ : quotient t -> quotient (s.comp t) := λ y, quotient.lift_on' y ζ p₆,

    exact {
        to_fun := φ,
        inv_fun := ψ,
        left_inv := λ x, by { induction x, refl, refl },
        right_inv := λ y, by { induction y, induction y, refl, refl, refl }
    }
}

noncomputable def setoid.comp.iso' {V : Type} {s : setoid V} {t : setoid (quotient s)} :
    quotient (setoid.comp s t) ≃ quotient t :=
let f : V → quotient s := quotient.mk,
    g : quotient s → quotient t := quotient.mk
in setoid.quotient_ker_equiv_of_surjective (g ∘ f)
    ((surjective_quotient_mk (quotient s)).comp (surjective_quotient_mk V))

def simple_graph.adj.symm {V : Type} {G : simple_graph V} := G.symm

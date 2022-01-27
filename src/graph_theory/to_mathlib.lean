import combinatorics.simple_graph.basic
import data.setoid.basic

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

def simple_graph.adj.symm {V : Type} {G : simple_graph V} := G.symm

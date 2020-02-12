import graph_theory.basic graph_theory.minor

namespace Graph.examples
    def prod {V₁ V₂ : Type} (G₁ : Graph V₁) (G₂ : Graph V₂) : Graph (V₁×V₂):= {
        adj := λ x y, (x.1 = y.1 ∧ G₂.adj x.2 y.2) ∨ (G₁.adj x.1 y.1 ∧ x.2 = y.2),
        sym := by { intros x y h, cases h,
            { left, exact ⟨h.1.symm, G₂.sym h.2⟩ },
            { right, exact ⟨G₁.sym h.1, h.2.symm⟩ } }
    }

    def Z : Graph ℤ := {
        adj := λ x y, y = x+1 ∨ x = y+1,
        sym := λ _ _, or.symm
    }

    def Z2 := prod Z Z

    def K (n : nat) : Graph (fin n) := {
        adj := λ _ _, true,
        sym := λ _ _ _, trivial
    }

    def K' (n : nat) : Graph (fin n) := {
        adj := λ x y, x ≠ y,
        sym := λ x y h1 h2, h1 h2.symm
    }
end Graph.examples

def planar {V : Type} (G : Graph V) := Graph.is_minor G Graph.examples.Z2

def colorable (n : nat) {V : Type} (G : Graph V) 
    := nonempty (Graph.hom G (Graph.examples.K' n))

-- theorem four_color {V : Type} {G : Graph V} : planar G -> colorable 4 G := sorry
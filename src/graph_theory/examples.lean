import graph_theory.basic graph_theory.minor

namespace examples section
    def prod (G₁ G₂ : Graph) : Graph := {
        V   := G₁ × G₂,
        adj := λ x y, (x.1 = y.1 ∧ G₂.adj x.2 y.2) ∨ (G₁.adj x.1 y.1 ∧ x.2 = y.2),
        sym := by { intros x y h, cases h,
            { left, exact ⟨h.1.symm, G₂.sym h.2⟩ },
            { right, exact ⟨G₁.sym h.1, h.2.symm⟩ } }
    }

    def Z : Graph := {
        V := ℤ,
        adj := λ x y, y = x+1 ∨ x = y+1,
        sym := by { tauto }
    }

    def Z2 := prod Z Z

    def K (n : nat) : Graph := {
        V := fin n,
        adj := λ _ _, true,
        sym := by { tauto }
    }

    def K' (n : nat) : Graph := {
        V := fin n,
        adj := λ x y, x ≠ y,
        sym := by { tauto }
    }
end end examples

def planar (G : Graph) := is_minor G examples.Z2

def colorable (n : nat) (G : Graph) : Prop := nonempty (Graph_hom G (examples.K' n))

-- theorem four_color {G : Graph} : planar G -> colorable 4 G := sorry
import graph_theory.basic graph_theory.minor

namespace Graph
    -- instance (G G' : Type) [Graph G] [Graph G'] : Graph (G×G') := {
    --     adj := λ x y, (x.1 = y.1 ∧ Graph.adj x.2 y.2) ∨ (Graph.adj x.1 y.1 ∧ x.2 = y.2),
    --     sym := by { intros x y h, cases h,
    --         { left, exact ⟨h.1.symm, Graph.sym h.2⟩ },
    --         { right, exact ⟨Graph.sym h.1, h.2.symm⟩ } }
    -- }

    def int_Graph : Graph ℤ := {
        adj := λ x y, y = x+1 ∨ x = y+1,
        sym := λ _ _, or.symm
    }

    -- def planar (G : Type) [Graph G] := contraction.is_minor G (ℤ×ℤ)

    -- def colorable (n : nat) (G : Type) [Graph G] := nonempty (hom G (K' n))

    -- theorem four_color {G : Type} [Graph G] : planar G -> colorable 4 G := sorry
end Graph

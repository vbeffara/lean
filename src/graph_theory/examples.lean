import graph_theory.basic graph_theory.minor

namespace simple_graph
    -- instance (G G' : Type) [simple_graph G] [simple_graph G'] : simple_graph (G×G') := {
    --     adj := λ x y, (x.1 = y.1 ∧ simple_graph.adj x.2 y.2) ∨ (simple_graph.adj x.1 y.1 ∧ x.2 = y.2),
    --     sym := by { intros x y h, cases h,
    --         { left, exact ⟨h.1.symm, simple_graph.sym h.2⟩ },
    --         { right, exact ⟨simple_graph.sym h.1, h.2.symm⟩ } }
    -- }

    def int_simple_graph : simple_graph ℤ := {
        adj := λ x y, y = x+1 ∨ x = y+1,
        symm := λ _ _, or.symm
    }

    def line_graph (n : ℕ) : simple_graph (finset.range n) := {
        adj := λ x y, y.val = x.val + 1 ∨ x.val = y.val + 1,
        symm := λ _ _, or.symm
    }

    -- def planar (G : Type) [simple_graph G] := contraction.is_minor G (ℤ×ℤ)

    -- def colorable (n : nat) (G : Type) [simple_graph G] := nonempty (hom G (K' n))

    -- theorem four_color {G : Type} [simple_graph G] : planar G -> colorable 4 G := sorry
end simple_graph

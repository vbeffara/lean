import tactic
import combinatorics.simple_graph.basic

variables {V : Type}

namespace sym2
    variables {z z' : sym2 V} {x y : V}

    lemma eq_of_two_members (h : x ≠ y) (h1 : x ∈ z) (h2 : y ∈ z) (h3 : x ∈ z') (h4 : y ∈ z') : z = z'
        := ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm
end sym2

namespace simple_graph
    variables {V': Type} {G : simple_graph V}

    def adj.symm := G.symm

    @[ext] structure step (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace step
        variables {e e' : step G}

        @[simp] def ends (e : step G) : sym2 V := ⟦( e.x, e.y )⟧
        @[simp] def flip (e : step G) : step G := ⟨e.h.symm⟩

        @[simp] lemma ends_flip : e.flip.ends = e.ends := sym2.eq_swap

        lemma same_iff : (e' = e ∨ e' = flip e) <-> e.ends = e'.ends
            := by { split; intro h,
                { cases h; subst e', rw ends_flip },
                { replace h := sym2.eq_iff.mp h, cases e with x y h1, cases e' with x' y', dsimp at h,
                    cases h; { cases h, substs x' y', simp } }
            }
    end step
end simple_graph

import tactic
import combinatorics.simple_graph.basic

namespace simple_graph
    def adj.symm {V : Type} {G : simple_graph V} := G.symm

    variables {V V': Type} {G : simple_graph V} {G' : simple_graph V'}

    @[ext] structure edge (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace edge
        variables {v : V} {e e' : edge G}

        def ends (e : edge G) : sym2 V := ⟦( e.x, e.y )⟧
        def flip (e : edge G) : edge G := ⟨e.h.symm⟩

        @[simp] lemma flip_x    :    e.flip.x  =  e.y               := rfl
        @[simp] lemma flip_y    :    e.flip.y  =  e.x               := rfl
        @[simp] lemma mem_edge  :  v ∈ e.ends <-> v = e.x ∨ v = e.y := sym2.mem_iff
        @[simp] lemma ends_flip : e.flip.ends  =  e.ends            := sym2.eq_swap

        lemma sym2_eq {x y : V} {e e' : sym2 V} (h : x ≠ y) (h1 : x ∈ e) (h2 : y ∈ e) (h3 : x ∈ e') (h4 : y ∈ e') : e = e'
            := ((sym2.mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((sym2.mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

        lemma sym2_ext_iff {z z' : sym2 V} : (∀ x, x ∈ z ↔ x ∈ z') <-> z = z'
            := ⟨sym2.ext z z', λ h _, iff_of_eq (congr_arg _ h)⟩

        lemma same_iff : (e' = e ∨ e' = flip e) <-> e.ends = e'.ends
            := by { split,
                { intros h, ext, cases h; subst e', rw ends_flip },
                { intro h, rw sym2_ext_iff.symm at h,
                    cases e with x y h1, cases e' with x' y' h2, simp at h,
                    have h3 := h x', simp at h3, have h4 := h y', simp at h4, clear h,
                    have h5 := G.loopless x',
                    cases h3; cases h4; substs x' y', contradiction, left, refl, right, refl, contradiction
                }
            }
    end edge
end simple_graph

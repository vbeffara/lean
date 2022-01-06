import tactic
import combinatorics.simple_graph.basic

namespace simple_graph
    variables {V V': Type} {x y z v : V} {G : simple_graph V} {G' : simple_graph V'}

    def adj.symm := G.symm

    @[ext] structure step (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace step
        variables {e e' : step G}

        @[simp] def ends (e : step G) : sym2 V := ⟦( e.x, e.y )⟧
        @[simp] def flip (e : step G) : step G := ⟨e.h.symm⟩

        lemma sym2_eq {e e' : sym2 V} (h : x ≠ y) (h1 : x ∈ e) (h2 : y ∈ e) (h3 : x ∈ e') (h4 : y ∈ e') : e = e'
            := ((sym2.mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((sym2.mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

        lemma sym2_ext_iff {z z' : sym2 V} : (∀ x, x ∈ z ↔ x ∈ z') <-> z = z'
            := ⟨sym2.ext z z', λ h _, iff_of_eq (congr_arg _ h)⟩

        lemma same_iff : (e' = e ∨ e' = flip e) <-> e.ends = e'.ends
            := by { split; intro h,
                { cases h; subst e', ext, simp [or.comm] },
                { rw sym2_ext_iff.symm at h,
                    cases e with x y h1, cases e' with x' y' h2, simp at h,
                    have h3 := h x', simp at h3, have h4 := h y', simp at h4, clear h,
                    have h5 := G.loopless x',
                    cases h3; cases h4; substs x' y', contradiction, left, refl, right, refl, contradiction
                }
            }
    end step
end simple_graph

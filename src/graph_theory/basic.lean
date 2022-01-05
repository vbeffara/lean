import tactic
import combinatorics.simple_graph.basic
open relation.refl_trans_gen function

namespace simple_graph
    def adj.symm {V : Type} {G : simple_graph V} := G.symm

    variables {V V': Type} {G : simple_graph V} {G' : simple_graph V'}

    def linked (G : simple_graph V) (x y : V) := relation.refl_trans_gen G.adj x y
    def connected (G : simple_graph V)        := ∀ x y, linked G x y

    lemma linked_of_subgraph {G₁ G₂ : simple_graph V} (sub : ∀ {x y : V}, G₁.adj x y -> G₂.adj x y)
            {x y : V} (h : linked G₁ x y) : linked G₂ x y
        := relation.refl_trans_gen.drec refl (λ _ _ _ h2 ih, tail ih (sub h2)) h

    class connected_graph (G : simple_graph V) := (conn : connected G)

    @[ext] structure edge (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace edge
        def ends (e : edge G) : sym2 V := ⟦( e.x, e.y )⟧

        @[simp] lemma mem_edge {v : V} {e : edge G} : v ∈ e.ends <-> v = e.x ∨ v = e.y
            := sym2.mem_iff

        def flip  (e : edge G) : edge G := ⟨G.symm e.h⟩

        @[simp] lemma flip_x (e : edge G) : e.flip.x = e.y
            := by { cases e, refl }

        @[simp] lemma flip_y (e : edge G) : e.flip.y = e.x
            := by { cases e, refl }

        @[simp] lemma ends_flip (e : edge G) : e.flip.ends = e.ends
            := sym2.eq_swap

        lemma sym2_eq {x y : V} {e e' : sym2 V} (h : x ≠ y) (h1 : x ∈ e) (h2 : y ∈ e) (h3 : x ∈ e') (h4 : y ∈ e') : e = e'
            := ((sym2.mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((sym2.mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

        lemma sym2_ext_iff {z z' : sym2 V} : (∀ x, x ∈ z ↔ x ∈ z') <-> z = z'
            := ⟨sym2.ext z z', by { intros h x, rw h }⟩

        lemma same_iff {e e' : edge G} : (e' = e ∨ e' = flip e) <-> e.ends = e'.ends
            := by { split,
                { intros h, ext, cases h; subst e', rw ends_flip },
                { intro h, rw sym2_ext_iff.symm at h,
                    cases e with x y h1, cases e' with x' y' h2, simp at h,
                    have h3 := h x', simp at h3,
                    have h4 := h y', simp at h4,
                    have h5 : ¬ G.adj x' x' := simple_graph.irrefl G,
                    cases h3; cases h4; substs x' y',
                        contradiction,
                        left, refl,
                        right, refl,
                        contradiction
                }
            }
    end edge

    namespace linked
        variables {x y z : V}

        @[refl] lemma refl : linked G x x := refl

        lemma edge : G.adj x y                  -> linked G x y := single
        lemma cons : G.adj x y -> linked G y z  -> linked G x z := head
        lemma tail : linked G x y  -> G.adj y z -> linked G x z := tail

        lemma symm : symmetric (linked G) := symmetric G.symm

        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z
            := trans

        lemma equiv : equivalence (linked G) := ⟨@refl _ _, @symm _ _, @trans _ _⟩
    end linked
end simple_graph

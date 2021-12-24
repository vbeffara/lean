import tactic
import combinatorics.simple_graph.basic
open relation.refl_trans_gen function

namespace simple_graph
    variables {V V': Type} {G : simple_graph V} {G' : simple_graph V'}

    def linked (G : simple_graph V) (x y : V) := relation.refl_trans_gen G.adj x y
    def connected (G : simple_graph V)        := ∀ x y, linked G x y

    class connected_graph (G : simple_graph V) := (conn : connected G)

    @[ext] structure edges (G : simple_graph V) := {x y : V} (h : G.adj x y)

    namespace edges
        def mem (v : V) (e : edges G) := v = e.x ∨ v = e.y
        instance : has_mem V (edges G) := ⟨mem⟩

        @[simp] lemma mem_edge {v : V} {e : edges G} : v ∈ e <-> v = e.x ∨ v = e.y := iff.rfl

        def flip  (e : edges G)    : edges G := ⟨G.symm e.h⟩
        def same  (e e' : edges G) : Prop    := e' = e ∨ e' = flip e
        def nsame (e e' : edges G) : Prop    := ¬ same e e'

        @[simp] lemma flip_x (e : edges G) : e.flip.x = e.y
            := by { cases e, refl }

        @[simp] lemma flip_y (e : edges G) : e.flip.y = e.x
            := by { cases e, refl }

        lemma strict (e : edges G) : e.x ≠ e.y
            := by { intro h, apply G.loopless e.x, convert e.h }

        lemma same_iff (e e' : edges G) : same e e' <-> ∀ x : V, x ∈ e <-> x ∈ e'
            := by { split,
                { intros h x, cases h; subst e', exact or.comm },
                { intro h, cases e with x y h1, cases e' with x' y' h2, simp at h,
                    have h3 := h x', simp at h3,
                    have h4 := h y', simp at h4,
                    cases h3; cases h4,
                        substs x' y', have := G.loopless x, contradiction,
                        substs x' y', left, refl,
                        substs x' y', right, refl,
                        substs x' y', have := G.loopless y, contradiction
                }
            }

        lemma same_of_ends (e e' : edges G) : e.x ∈ e' -> e.y ∈ e' -> same e e'
            := sorry

        lemma same_of_same_ends {e e' : edges G} {x y : V} : x ≠ y -> x ∈ e -> y ∈ e -> x ∈ e' -> y ∈ e' -> same e e'
            := sorry
    end edges

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

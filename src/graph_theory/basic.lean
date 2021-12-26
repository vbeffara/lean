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
        def ends (e : edges G) : set V := { e.x, e.y }

        @[simp] lemma mem_edge {v : V} {e : edges G} : v ∈ e.ends <-> v = e.x ∨ v = e.y := iff.rfl

        def flip  (e : edges G)    : edges G := ⟨G.symm e.h⟩
        def same  (e e' : edges G) : Prop    := e' = e ∨ e' = flip e
        def nsame (e e' : edges G) : Prop    := ¬ same e e'

        @[simp] lemma flip_x (e : edges G) : e.flip.x = e.y
            := by { cases e, refl }

        @[simp] lemma flip_y (e : edges G) : e.flip.y = e.x
            := by { cases e, refl }

        lemma strict (e : edges G) : e.x ≠ e.y
            := by { intro h, apply G.loopless e.x, convert e.h }

        lemma same_iff {e e' : edges G} : same e e' <-> ∀ x : V, x ∈ e.ends <-> x ∈ e'.ends
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

        lemma same_of_ends (e e' : edges G) : e.x ∈ e'.ends -> e.y ∈ e'.ends -> same e e'
            := by {
                intros h1 h2, apply same_iff.mpr, intro x, split,
                { intro h, cases h,
                    { subst x, assumption },
                    { cases h, assumption }
                },
                { intro h, cases h; cases h1; cases h2,
                    substs x, rw <-h1, left, refl,
                    substs x, rw <-h1, left, refl,
                    substs x, rw <-h2, right, exact rfl,
                    have : e.y = e'.y := h2, rw <-this at h1, have : e.x = e.y := h1, have := e.strict, contradiction,
                    rw <-h2 at h1, have := e.strict, contradiction,
                    replace h : x = e'.y := h, substs x, replace h2 : e.y = e'.y := h2, rw <-h2, right, exact rfl,
                    replace h : x = e'.y := h, replace h1 : e.x = e'.y := h1, substs x, rw <-h1, left, refl,
                    replace h : x = e'.y := h, substs x, replace h2 : e.y = e'.y := h2, rw <-h2, right, exact rfl }
            }

        lemma same_of_same_ends {e e' : edges G} {x y : V} : x ≠ y -> x ∈ e.ends -> y ∈ e.ends -> x ∈ e'.ends -> y ∈ e'.ends -> same e e'
            := by { intros h h1 h2 h3 h4, apply same_iff.mpr, intro z, finish }
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

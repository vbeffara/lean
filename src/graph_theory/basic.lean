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
    end edges

    namespace linked
        variables {x y z : V}

        @[refl] lemma refl : linked G x x := refl

        lemma edge : G.adj x y                  -> linked G x y := single
        lemma cons : G.adj x y -> linked G y z  -> linked G x z := head
        lemma tail : linked G x y  -> G.adj y z -> linked G x z := tail

        @[symm] lemma symm : linked G x y -> linked G y x
            := by { intro h, induction h with b c hxb hbc hbx, refl,
                apply cons, apply G.symm, exact hbc, exact hbx }

        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z
            := trans

        lemma equiv : equivalence (linked G) := ⟨@refl _ _, @symm _ _, @trans _ _⟩
    end linked
end simple_graph

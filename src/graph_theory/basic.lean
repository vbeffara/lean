import tactic
import combinatorics.simple_graph.basic
open relation.refl_trans_gen function

abbreviation Graph := simple_graph

def Graph.vertices {V : Type} (G : Graph V) := V

namespace Graph
    variables {V V': Type} {G : Graph V} {G' : Graph V'}

    structure hom (G : Graph V) (G' : Graph V') :=
        (f   : V -> V')
        (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

    structure iso (G : Graph V) (G' : Graph V') extends hom G G' :=
        (bij : bijective f)
        (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))

    def isomorphic                     := inhabited (iso G G')
    def linked (G : Graph V) (x y : V) := relation.refl_trans_gen G.adj x y
    def connected (G : Graph V)        := ∀ x y, linked G x y

    class connected_graph (G : Graph V) := (conn : connected G)

    @[ext] structure edges (G : Graph V) := {x y : V} (h : G.adj x y)

    namespace edges
        def mem (v : V) (e : edges G) := v = e.x ∨ v = e.y
        instance : has_mem V (edges G) := ⟨mem⟩

        def flip  (e : edges G)    : edges G := ⟨G.sym e.h⟩
        def same  (e e' : edges G) : Prop    := e' = e ∨ e' = flip e
        def nsame (e e' : edges G) : Prop    := ¬ same e e'
    end edges

    @[symm] lemma Graph.adj.symm : ∀ {x y : V}, G.adj x y -> G.adj y x := G.sym

    namespace linked
        variables {x y z : V}

        @[refl] lemma refl : linked G x x := refl

        lemma edge : G.adj x y                  -> linked G x y := single
        lemma cons : G.adj x y -> linked G y z  -> linked G x z := head
        lemma tail : linked G x y  -> G.adj y z -> linked G x z := tail

        @[symm] lemma symm : linked G x y -> linked G y x
            := by { intro h, induction h with b c hxb hbc hbx, refl,
                apply cons, symmetry, exact hbc, exact hbx }

        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z
            := trans

        lemma equiv : equivalence (linked G) := ⟨@refl _ _, @symm _ _, @trans _ _⟩
    end linked
end Graph

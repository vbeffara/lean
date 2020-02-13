import tactic
open relation.refl_trans_gen function

@[ext] class Graph (V : Type) := (adj : V -> V -> Prop) (sym {} : symmetric adj)

def Graph.vertices {V : Type} (G : Graph V) := V

namespace Graph
    variables (G G' : Type) [Graph G] [Graph G']

    structure hom :=
        (f   : G -> G')
        (hom : ∀ x y, Graph.adj x y -> Graph.adj (f x) (f y))

    structure iso extends hom G G' :=
        (bij : bijective f)
        (iso : ∀ x y, Graph.adj x y <-> Graph.adj (f x) (f y))

    def isomorphic       := inhabited (iso G G')
    def linked (x y : G) := relation.refl_trans_gen Graph.adj x y
    def connected        := ∀ x y, linked G x y

    class connected_graph := (conn : connected G)

    @[ext] structure edges := {x y : G} (h : Graph.adj x y)

    namespace edges
        def mem (v : G) (e : edges G) := v = e.x ∨ v = e.y
        instance : has_mem G (edges G) := ⟨mem G⟩

        def flip  {G : Type} [Graph G] (e : edges G)    : edges G := ⟨Graph.sym e.h⟩
        def same  {G : Type} [Graph G] (e e' : edges G) : Prop    := e' = e ∨ e' = e.flip
        def nsame {G : Type} [Graph G] (e e' : edges G) : Prop    := ¬ same e e'
    end edges

    @[symm] lemma Graph.adj.symm : ∀ {x y : G}, Graph.adj x y -> Graph.adj y x := Graph.sym

    namespace linked
        variables {x y z : G}

        @[refl] lemma refl : linked G x x := refl

        lemma edge : Graph.adj x y                  -> linked G x y := single
        lemma cons : Graph.adj x y -> linked G y z  -> linked G x z := head
        lemma tail : linked G x y  -> Graph.adj y z -> linked G x z := tail

        @[symm] lemma symm : linked G x y -> linked G y x
            := by { intro h, induction h with b c hxb hbc hbx, refl, 
                apply cons, symmetry, exact hbc, exact hbx }

        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z
            := trans

        lemma equiv : equivalence (linked G) := ⟨@refl G _, @symm G _, @trans G _⟩
    end linked
end Graph

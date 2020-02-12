import tactic
open relation.refl_trans_gen function

@[ext] structure Graph (V : Type) := (adj : V -> V -> Prop) (sym : symmetric adj)

def Graph.vertices {V : Type} (G : Graph V) := V

namespace Graph
    variables {V V' : Type} (G : Graph V) (G' : Graph V')

    structure hom :=
        (f   : V -> V')
        (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

    structure iso extends hom G G' :=
        (bij : bijective f)
        (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))

    def isomorphic := inhabited (iso G G')
    def linked     := relation.refl_trans_gen G.adj
    def connected  := ∀ x y, linked G x y

    class connected_graph := (conn : connected G)

    @[ext] structure edges := {x y : V} (h : G.adj x y)

    namespace edges
        def mem (v : V) (e : G.edges) := v = e.x ∨ v = e.y
        instance : has_mem V G.edges := ⟨mem G⟩

        def flip  {G : Graph V} (e : G.edges)    : G.edges := ⟨G.sym e.h⟩
        def same  {G : Graph V} (e e' : G.edges) : Prop   := e' = e ∨ e' = e.flip
        def nsame {G : Graph V} (e e' : G.edges) : Prop   := ¬ same e e'
    end edges

    @[symm] lemma Graph.adj.symm : ∀ {x y : V}, G.adj x y -> G.adj y x
        := G.sym

    namespace linked
        variables {x y z : V}

        @[refl] lemma refl : linked G x x := refl

        lemma edge : G.adj x y -> linked G x y := single

        lemma cons : G.adj x y -> linked G y z -> linked G x z := head
    
        lemma tail : linked G x y -> G.adj y z -> linked G x z := tail

        @[symm] lemma symm : linked G x y -> linked G y x
            := by { intro h, induction h with b c hxb hbc hbx, refl, 
                apply cons, symmetry, exact hbc, exact hbx }

        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z
            := trans

        lemma equiv : equivalence (linked G) := ⟨@refl V G, @symm V G, @trans V G⟩
    end linked
end Graph

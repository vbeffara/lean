import tactic
open relation.refl_trans_gen function

@[ext] structure Graph := (V : Type) (adj : V -> V -> Prop) (sym : symmetric adj)

instance : has_coe_to_sort Graph := {S := _, coe := λ G, G.V}

structure Graph_hom  (G G' : Graph) :=
    (f   : G -> G')
    (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

structure Graph_iso (G G' : Graph) extends Graph_hom G G' :=
    (bij : bijective f)
    (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))

def isomorphic (G G' : Graph) := inhabited (Graph_iso G G')

def linked    (G : Graph) := relation.refl_trans_gen G.adj
def connected (G : Graph) := ∀ x y, linked G x y

class connected_graph (G : Graph) := (conn : connected G)

@[ext] structure edge (G : Graph) := {x y : G.V} (h : G.adj x y)

namespace edge section
    parameters {G : Graph}

    def mem (v : G) (e : edge G) := v = e.x ∨ v = e.y
    instance : has_mem G.V (edge G) := ⟨mem⟩

    def flip  (e : edge G)    : edge G := ⟨G.sym e.h⟩
    def same  (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    def nsame (e e' : edge G) : Prop   := ¬ same e e'
end end edge

@[symm] lemma Graph.adj.symm {G : Graph} : ∀ {x y : G}, G.adj x y -> G.adj y x
    := G.sym

namespace linked section
    variables {G : Graph} {x y z : G}

    @[refl] lemma refl : linked G x x
        := refl

    lemma edge : G.adj x y -> linked G x y
        := single

    lemma cons : G.adj x y -> linked G y z -> linked G x z
        := head

    lemma tail : linked G x y -> G.adj y z -> linked G x z
        := tail

    @[symm] lemma symm : linked G x y -> linked G y x
        := by { intro h, induction h with b c hxb hbc hbx, refl, exact cons hbc.symm hbx }

    @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z
        := trans

    lemma equiv : equivalence (linked G)
        := ⟨@refl G, @symm G, @trans G⟩
end end linked



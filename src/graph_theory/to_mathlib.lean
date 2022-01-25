import combinatorics.simple_graph.basic
import data.setoid.basic

lemma setoid.r.symm {V : Type} {S : setoid V} : symmetric S.r :=
λ x y, setoid.symm

def simple_graph.adj.symm {V : Type} {G : simple_graph V} := G.symm

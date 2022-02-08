import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward graph_theory.basic
open finset classical function
open_locale classical

namespace simple_graph
    variables {V V' : Type} {x y z : V} {f : V → V'} {G : simple_graph V}

    inductive lazy_walk (G : simple_graph V) : V → V → Type
    | nil {u : V} : lazy_walk u u
    | cons {u v w: V} (h : u = v ∨ G.adj u v) (p : lazy_walk v w) : lazy_walk u w

    open lazy_walk

    def to_lazy (p : walk G x y) : lazy_walk G x y :=
    by { induction p with a a b c adj p ih, exact nil, exact ih.cons (or.inr adj) }

    noncomputable def from_lazy (p : lazy_walk G x y) : walk G x y :=
    begin
        induction p with a a b c adj p ih, refl,
        by_cases a = b, rw h, exact ih,
        exact ih.cons ((or_iff_right h).mp adj)
    end

    def lazy_push (f : V → V') (p : G.walk x y) : (push f G).lazy_walk (f x) (f y) :=
    begin
        induction p with a a b c adj p ih, exact nil, refine ih.cons _,
        by_cases f a = f b, exact or.inl h, refine or.inr ⟨h,a,b,rfl,rfl,adj⟩
    end
end simple_graph

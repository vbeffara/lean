import tactic
import graph_theory.basic llist

namespace simple_graph
    structure old_path {V : Type} (G : simple_graph V) (x y) extends llist' V x y
      := (adj : llist.is_path G.adj l)

    inductive path {V : Type} (G : simple_graph V) : V -> V -> Type
    | point (x : V) : path x x
    | step {x y z : V} : G.adj x y -> path y z -> path x z

    namespace path
        variables {V : Type} {G : simple_graph V} {u x y z : V}

        def mem (z : V) (p : path G x y) : Prop
            := path.rec (eq z) (λ x' _ _ _ _ ih, z = x' ∨ ih) p

        instance : has_mem V (path G x y) := ⟨mem⟩

        @[simp] lemma mem_point : z ∈ (point x : path G x x) <-> z = x
            := iff.rfl

        @[simp] lemma mem_step {h : G.adj x y} {p : path G y z} : u ∈ step h p <-> u = x ∨ u ∈ p
            := iff.refl (u ∈ step h p)

        lemma mem_head {p : path G x y} : x ∈ p
            := by { cases p, exact rfl, simp }

        lemma mem_tail {p : path G x y} : y ∈ p
            := by { induction p, exact rfl, simp, right, assumption }

        def size (p : path G x y) : nat
            := path.rec (λ _, 0) (λ _ _ _ _ _, nat.succ) p

        instance : has_sizeof (path G x y) := ⟨size⟩

        @[simp] lemma size_point : size (point x : path G x x) = 0
            := rfl

        @[simp] lemma size_step (p : path G x y) {h : G.adj z x} : size (step h p) = size p + 1
            := rfl

        def from_edge (h : G.adj x y) : path G x y
            := step h (point y)

        def append (p : path G x y) (h : G.adj y z) : path G x z
            := path.rec (λ _, from_edge) (λ _ _ _ h' _ ih, step h' ∘ ih) p h

        @[simp] lemma append_point {h : G.adj x y} : append (point x : path G x x) h = step h (point y : path G y y)
            := rfl

        @[simp] lemma append_step {h₁ : G.adj u x} {p : path G x y} {h₂ : G.adj y z} : append (step h₁ p) h₂ = step h₁ (append p h₂)
            := rfl

        @[simp] lemma mem_append {p : path G x y} {h : G.adj y z} : u ∈ append p h <-> u ∈ p ∨ u = z
            := by { induction p; simp [*], exact or.assoc.symm }

        @[simp] lemma size_append {p : path G x y} {h : G.adj y z} : size (append p h) = size p + 1
            := by { induction p, refl, simp [*] }

        def rev (p : path G x y) : path G y x
            := path.rec (point) (λ _ _ _ h _ ih, append ih (G.sym h)) p

        @[simp] lemma rev_step {h : G.adj x y} {p : path G y z} : rev (step h p) = append (rev p) (G.sym h)
            := rfl

        @[simp] lemma size_rev {p : path G x y} : size (rev p) = size p
            := by { induction p, refl, simp [*] }

        @[simp] lemma mem_rev {p : path G x y} : z ∈ rev p <-> z ∈ p
            := by { induction p, exact iff.rfl, simp [*], exact or.comm }

        def concat (p : path G x y) (p' : path G y z) : path G x z
            := path.rec (λ _, id) (λ _ _ _ h' _ ih, step h' ∘ ih) p p'

        @[simp] lemma concat_point {p : path G x y} : concat (path.point x) p = p
            := rfl

        @[simp] lemma concat_step {h : G.adj x y} {p : path G y z} {p' : path G z u} : concat (step h p) p' = step h (concat p p')
            := rfl

        @[simp] lemma size_concat {p : path G x y} {p' : path G y z} : (concat p p').size = p.size + p'.size
            := by { induction p; simp [*], linarith }

        def all_edges (p : path G x y) : list (edges G)
            := path.rec (λ _, []) (λ _ _ _ h _, list.cons ⟨h⟩) p

        @[simp] lemma all_edges_point : all_edges (point x : path G x x) = []
            := rfl

        @[simp] lemma all_edges_step {h : G.adj x y} {p : path G y z} : all_edges (step h p) = ⟨h⟩ :: all_edges p
            := rfl

        lemma mem_edges {p : path G x y} {e : edges G} : e ∈ p.all_edges -> e.x ∈ p ∧ e.y ∈ p
            := by { induction p, simp, intro hh, simp at hh, cases hh; simp [*], right, apply mem_head }

        -- lemma edges_simple {l} (h : llist.is_path G.adj l) (hs : llist.nodup l) : list.pairwise (edges.nsame) (edges_aux G l h)
        --     := by { induction l with v v l hr, { exact list.pairwise.nil },
        --         { apply list.pairwise.cons,
        --         { intros e he, rw [edges.nsame, edges.same], push_neg, have h5 := mem_edges_aux he,
        --             split; intro h6; subst h6, exact hs.1 h5.1, exact hs.1 h5.2 },
        --         { exact hr h.2 hs.2 } } }

        lemma to_path (h : linked G x y) : nonempty (path G x y)
            := by { induction h with x' y' h1 h2 ih,
                { use point x },
                { cases ih, use append ih h2 }
            }

        lemma from_path : nonempty (path G x y) -> linked G x y
            := by { intro h, cases h with p, induction p with x' x' y' z' h' p' ih,
                exact linked.refl,
                transitivity y', exact linked.edge h', exact ih }

        lemma iff_path : linked G x y <-> nonempty (path G x y)
            := ⟨to_path, from_path⟩

        def nodup (p : path G x y) : Prop
            := path.rec (λ _, true) (λ x _ _ _ p ih, x ∉ p ∧ ih) p

        @[simp] lemma nodup_point : nodup (point x : path G x x) := trivial

        @[simp] lemma nodup_step {h : G.adj x y} {p : path G y z} : nodup (step h p) <-> x ∉ p ∧ nodup p
            := ⟨id,id⟩

        @[simp] lemma nodup_append {p : path G x y} {h : G.adj y z} : nodup (append p h) <-> nodup p ∧ z ∉ p
            := by { induction p, { simp, exact ne_comm }, { split; finish } }

        lemma nodup_rev {p : path G x y} : nodup p -> nodup p.rev
            := by { induction p, obviously }
    end path

    @[ext] structure spath {V : Type} (G : simple_graph V) (x y : V)
        := (p : path G x y) (simple : path.nodup p)

    namespace spath
        variables {V : Type} {G : simple_graph V} {x y z : V}

        def mem (z : V) (p : spath G x y) := z ∈ p.p
        instance : has_mem V (spath G x y) := ⟨mem⟩

        def size (p : spath G x y) := p.p.size

        instance : has_coe (spath G x y) (path G x y) := ⟨spath.p⟩

        def rev (p : spath G x y) : spath G y x
            := ⟨p.p.rev, path.nodup_rev p.simple⟩

        -- lemma edges_simple {p : spath G x y} : list.pairwise (edges.nsame) p.to_path.all_edges
        --     := path.edges_simple G _ p.simple
    end spath
end simple_graph

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

        def from_edge (h : G.adj x y) : path G x y := step h (point y)

        def append (p : path G x y) (h : G.adj y z) : path G x z
            := path.rec (λ _, from_edge) (λ _ _ _ h' _ ih, step h' ∘ ih) p h

        def concat (p : path G x y) (p' : path G y z) : path G x z
            := path.rec (λ _, id) (λ _ _ _ h' _ ih, step h' ∘ ih) p p'

        def mem (z : V) (p : path G x y) : Prop           := path.rec (eq z)      (λ u _ _ _ _ h, z = u ∨ h)           p
        def size        (p : path G x y) : nat            := path.rec (λ _, 0)    (λ _ _ _ _ _ h, h + 1)               p
        def rev         (p : path G x y) : path G y x     := path.rec (point)     (λ _ _ _ e _ h, append h (G.symm e)) p
        def edges       (p : path G x y) : list (edges G) := path.rec (λ _, [])   (λ _ _ _ e _ h, ⟨e⟩ :: h)            p
        def to_list     (p : path G x y) : list V         := path.rec (λ u, [u])  (λ u _ _ _ _ h, u :: h)              p

        def nodup(p : path G x y) : Prop   := p.to_list.nodup
        def init (p : path G x y) : list V := p.to_list.init
        def tail (p : path G x y) : list V := p.to_list.tail

        instance : has_mem    V (path G x y) := ⟨mem⟩
        instance : has_sizeof   (path G x y) := ⟨size⟩

        @[simp] lemma to_list_point : to_list (point x : path G x x) = [x]
            := rfl

        @[simp] lemma to_list_step (p : path G x y) {h : G.adj z x} : to_list (step h p) = z :: p.to_list
            := rfl

        @[simp] lemma mem_point : z ∈ (point x : path G x x) <-> z = x
            := iff.rfl

        @[simp] lemma mem_step {h : G.adj x y} {p : path G y z} : u ∈ step h p <-> u = x ∨ u ∈ p
            := iff.refl (u ∈ step h p)

        lemma mem_to_list {p : path G x y} : u ∈ p <-> u ∈ p.to_list
            := by { induction p; simp [*] }

        lemma mem_head {p : path G x y} : x ∈ p
            := by { cases p, exact rfl, simp }

        lemma mem_tail {p : path G x y} : y ∈ p
            := by { induction p, exact rfl, simp, right, assumption }

        @[simp] lemma size_point : size (point x : path G x x) = 0
            := rfl

        @[simp] lemma size_step (p : path G x y) {h : G.adj z x} : size (step h p) = size p + 1
            := rfl

        lemma point_of_size_0 {p : path G x y} (h : size p = 0) : x = y
            := by { cases p, refl, contradiction }

        @[simp] lemma append_point {h : G.adj x y} : append (point x : path G x x) h = step h (point y : path G y y)
            := rfl

        @[simp] lemma append_step {h₁ : G.adj u x} {p : path G x y} {h₂ : G.adj y z} : append (step h₁ p) h₂ = step h₁ (append p h₂)
            := rfl

        @[simp] lemma mem_append {p : path G x y} {h : G.adj y z} : u ∈ append p h <-> u ∈ p ∨ u = z
            := by { induction p; simp [*], exact or.assoc.symm }

        @[simp] lemma size_append {p : path G x y} {h : G.adj y z} : size (append p h) = size p + 1
            := by { induction p, refl, simp [*] }

        @[simp] lemma rev_point : rev (point x : path G x x) = point x
            := rfl

        @[simp] lemma rev_step {h : G.adj x y} {p : path G y z} : rev (step h p) = append (rev p) (G.symm h)
            := rfl

        @[simp] lemma size_rev {p : path G x y} : size (rev p) = size p
            := by { induction p, refl, simp [*] }

        @[simp] lemma mem_rev {p : path G x y} : z ∈ rev p <-> z ∈ p
            := by { induction p, exact iff.rfl, simp [*], exact or.comm }

        @[simp] lemma concat_point {p : path G x y} : concat (path.point x) p = p
            := rfl

        @[simp] lemma concat_step {h : G.adj x y} {p : path G y z} {p' : path G z u} : concat (step h p) p' = step h (concat p p')
            := rfl

        @[simp] lemma concat_point' {p : path G x y} : concat p (path.point y) = p
            := by { induction p, refl, rw [concat_step,p_ih] }

        @[simp] lemma concat_append {p : path G x y} {p' : path G y z} {h : G.adj z u} :
                concat p (append p' h) = append (concat p p') h
            := by { induction p; simp [*] }

        @[simp] lemma concat_rev {p : path G x y} {p' : path G y z} : (concat p p').rev = concat p'.rev p.rev
            := by { induction p; simp [*] }

        @[simp] lemma concat_assoc {p1 : path G x y} {p2 : path G y z} {p3 : path G z u} :
                concat (concat p1 p2) p3 = concat p1 (concat p2 p3)
            := by { induction p1; simp [*] }

        @[simp] lemma size_concat {p : path G x y} {p' : path G y z} : (concat p p').size = p.size + p'.size
            := by { induction p; simp [*], linarith }

        @[simp] lemma mem_concat {p1 : path G x y} {p2 : path G y z} : u ∈ (concat p1 p2) <-> u ∈ p1 ∨ u ∈ p2
            := by { induction p1; simp,
                { refine ⟨or.inr,_⟩, intro h, cases h, convert mem_head, assumption },
                { rw p1_ih, finish }
            }

        @[simp] lemma edges_point : edges (point x : path G x x) = []
            := rfl

        @[simp] lemma edges_step {h : G.adj x y} {p : path G y z} : edges (step h p) = ⟨h⟩ :: edges p
            := rfl

        lemma mem_edges {p : path G x y} {e : G.edges} : e ∈ p.edges -> e.x ∈ p ∧ e.y ∈ p
            := by { induction p, simp, intro hh, simp at hh, cases hh; simp [*], right, apply mem_head }

        lemma mem_of_edges {p : path G x y} {h : 0 < p.size} : u ∈ p <-> ∃ e ∈ p.edges, u ∈ edges.ends e
            := by { induction p with x' x' y' z' h' p' ih, { simp at h, contradiction }, split,
                { rw mem_step, intro h1, cases h1,
                    { use ⟨h'⟩, simp [*] },
                    { cases nat.eq_zero_or_pos p'.size,
                        { cases p', simp, right, exact h1, simp at h_1, contradiction },
                        { obtain ⟨e',h2,h3⟩ := ih.mp h1, use e', simp [*], assumption }
                    }
                },
                { rw mem_step, intro h1, obtain ⟨e,h2,h3⟩ := h1, simp at h2, cases h2,
                    { subst e, simp at h3, cases h3,
                        left, exact h3,
                        right, subst u, exact mem_head },
                    { cases nat.eq_zero_or_pos p'.size,
                        { cases p', simp at h2, contradiction, simp at h_1, contradiction },
                        { right, apply ih.mpr ⟨e,h2,h3⟩; assumption }
                    }
                }
            }

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

        @[simp] lemma nodup_point : nodup (point x : path G x x)
            := by { unfold nodup, simp }

        @[simp] lemma nodup_step {h : G.adj x y} {p : path G y z} : nodup (step h p) <-> x ∉ p ∧ nodup p
            := by { unfold nodup, simp, intro, rw mem_to_list, }

        @[simp] lemma nodup_append {p : path G x y} {h : G.adj y z} : nodup (append p h) <-> nodup p ∧ z ∉ p
            := by { induction p, { simp, exact ne_comm }, { split; finish } }

        lemma nodup_rev {p : path G x y} : nodup p -> nodup p.rev
            := by { induction p, obviously }

        lemma nodup_concat {p : path G x y} {p' : path G y z} : nodup (concat p p') <-> nodup p ∧ nodup p' ∧ (∀ u, u ∈ p -> u ∈ p' -> u = y)
            := by { induction p with _ _ _ _ _ _ ih; simp, push_neg, split,
                { rintros ⟨⟨h1,h2⟩,h3⟩, replace ih := ih.mp h3, refine ⟨⟨h1,ih.1⟩,ih.2.1,_,ih.2.2⟩,
                    exact false.rec _ ∘ h2 },
                { rintros ⟨⟨h1,h2⟩,h3,h4,h5⟩, replace ih := ih.mpr ⟨h2,h3,h5⟩, refine ⟨⟨h1,_⟩,ih⟩,
                    intro h, apply h1, convert mem_tail, exact h4 h }
            }

        @[simp] lemma init_step {h : G.adj x y} {p : path G y z} : init (step h p) = x :: init p
            := by { cases p; refl }

        @[simp] lemma tail_step {h : G.adj x y} {p : path G y z} : tail (step h p) = y :: tail p
            := by { cases p; refl }
    end path
end simple_graph

import tactic
import graph_theory.basic

namespace simple_graph
    inductive path3 {V : Type} (G : simple_graph V) (x : V) : V -> Type
    | point : path3 x
    | step {y z : V} : path3 y -> G.adj y z -> path3 z

    namespace path3
        open path3
        variables {V : Type} {G : simple_graph V} {u v x y z : V} {p : path3 G x y} {h : G.adj y z} {h' : G.adj u x}

        @[simp] def from_edge (h : G.adj x y) : path3 G x y := step point h

        def cons (p : path3 G y z) (h : G.adj x y) : path3 G x z
            := path3.rec (from_edge h) (λ _ _ _ h ih, ih.step h) p

        def concat (p : path3 G x y) (p' : path3 G y z) : path3 G x z
            := path3.rec p (λ _ _ _ h q, q.step h) p'

        def mem (z : V) (p : path3 G x y) : Prop           := path3.rec (z=x) (λ _ u _ _ h, h ∨ z=u)           p
        def size        (p : path3 G x y) : ℕ              := path3.rec 0     (λ _ _ _ _ l, l+1)               p
        def rev         (p : path3 G x y) : path3 G y x    := path3.rec point (λ _ _ _ h q, q.cons (G.symm h)) p
        def edges       (p : path3 G x y) : list (edges G) := path3.rec []    (λ _ _ _ d e, e.append [⟨d⟩])    p
        def nodup       (p : path3 G x y) : Prop           := path3.rec true  (λ _ u q _ e, e ∧ ¬(mem u q))    p

        instance : has_mem    V (path3 G x y) := ⟨mem⟩
        instance : has_sizeof   (path3 G x y) := ⟨size⟩

        @[simp] lemma cons_point  :  cons (point : path3 G z z) h  =  from_edge h := rfl
        @[simp] lemma mem_point   :   u ∈ (point : path3 G x x)   <-> u = x       := iff.rfl
        @[simp] lemma size_point  :  size (point : path3 G x x)    =  0           := rfl
        @[simp] lemma rev_point   :   rev (point : path3 G x x)    =  point       := rfl
        @[simp] lemma nodup_point : nodup (point : path3 G x x)                   := trivial

        @[simp] lemma cons_step  : cons (p.step h) h'  =  step (p.cons h') h    := rfl
        @[simp] lemma mem_step   :       u ∈ p.step h <-> u ∈ p ∨ u = z         := iff.rfl
        @[simp] lemma size_step  :    (p.step h).size  =  p.size + 1            := rfl
        @[simp] lemma rev_step   :     rev (p.step h)  =  cons p.rev (G.symm h) := rfl
        @[simp] lemma nodup_step :   (p.step h).nodup <-> p.nodup ∧ z ∉ p       := iff.rfl

        lemma mem_tail : y ∈ p := by { cases p, exact rfl, right, refl }
        lemma mem_head : x ∈ p := by { induction p, exact rfl, left, assumption }

        lemma point_of_size_0 {p : path3 G x y} (h : p.size = 0) : x = y := by { cases p, refl, contradiction }

        lemma mem_cons  :    v ∈ p.cons h' <-> v = u ∨ v ∈ p := by { induction p; simp [*,or.assoc] }
        lemma size_cons : size (p.cons h')  =  size p + 1    := by { induction p; simp [*] }

        -- @[simp] lemma size_rev {p : path G x y} : size (rev p) = size p
        --     := by { induction p, refl, simp [*] }

        -- @[simp] lemma mem_rev {p : path G x y} : z ∈ rev p <-> z ∈ p
        --     := by { induction p, exact iff.rfl, simp [*], exact or.comm }

        -- @[simp] lemma concat_point {p : path G x y} : concat (path.point x) p = p
        --     := rfl

        -- @[simp] lemma concat_step {h : G.adj x y} {p : path G y z} {p' : path G z u} : concat (step h p) p' = step h (concat p p')
        --     := rfl

        -- @[simp] lemma concat_point' {p : path G x y} : concat p (path.point y) = p
        --     := by { induction p, refl, rw [concat_step,p_ih] }

        -- @[simp] lemma concat_append {p : path G x y} {p' : path G y z} {h : G.adj z u} :
        --         concat p (append p' h) = append (concat p p') h
        --     := by { induction p; simp [*] }

        -- @[simp] lemma concat_rev {p : path G x y} {p' : path G y z} : (concat p p').rev = concat p'.rev p.rev
        --     := by { induction p; simp [*] }

        -- @[simp] lemma concat_assoc {p1 : path G x y} {p2 : path G y z} {p3 : path G z u} :
        --         concat (concat p1 p2) p3 = concat p1 (concat p2 p3)
        --     := by { induction p1; simp [*] }

        -- @[simp] lemma size_concat {p : path G x y} {p' : path G y z} : (concat p p').size = p.size + p'.size
        --     := by { induction p; simp [*], linarith }

        -- @[simp] lemma mem_concat {p1 : path G x y} {p2 : path G y z} : u ∈ (concat p1 p2) <-> u ∈ p1 ∨ u ∈ p2
        --     := by { induction p1; simp,
        --         { refine ⟨or.inr,_⟩, intro h, cases h, convert mem_head, assumption },
        --         { rw p1_ih, exact or.assoc.symm }
        --     }

        -- @[simp] lemma edges_point : edges (point x : path G x x) = []
        --     := rfl

        -- @[simp] lemma edges_step {h : G.adj x y} {p : path G y z} : edges (step h p) = ⟨h⟩ :: edges p
        --     := rfl

        -- lemma mem_edges {p : path G x y} {e : G.edges} : e ∈ p.edges -> e.x ∈ p ∧ e.y ∈ p
        --     := by { induction p, simp, intro hh, simp at hh, cases hh; simp [*], right, apply mem_head }

        -- lemma mem_of_edges {p : path G x y} (h : 0 < p.size) : u ∈ p <-> ∃ e ∈ p.edges, u ∈ edges.ends e
        --     := by { induction p with x' x' y' z' h' p' ih, { simp at h, contradiction }, split,
        --         { rw mem_step, intro h1, cases h1,
        --             { use ⟨h'⟩, simp [*] },
        --             { cases nat.eq_zero_or_pos p'.size,
        --                 { cases p', simp, right, exact h1, simp at h_1, contradiction },
        --                 { obtain ⟨e',h2,h3⟩ := (ih h_1).mp h1, use e', simp [*] }
        --             }
        --         },
        --         { rw mem_step, intro h1, obtain ⟨e,h2,h3⟩ := h1, simp at h2, cases h2,
        --             { subst e, simp at h3, cases h3,
        --                 left, exact h3,
        --                 right, subst u, exact mem_head },
        --             { cases nat.eq_zero_or_pos p'.size,
        --                 { cases p', simp at h2, contradiction, simp at h_1, contradiction },
        --                 { right, apply (ih h_1).mpr ⟨e,h2,h3⟩; assumption }
        --             }
        --         }
        --     }

        -- lemma to_path (h : linked G x y) : nonempty (path G x y)
        --     := by { induction h with x' y' h1 h2 ih,
        --         { use point x },
        --         { cases ih, use append ih h2 }
        --     }

        -- noncomputable def to_path' (h : linked G x y) : path G x y
        --     := classical.choice (to_path h)

        -- lemma from_path : nonempty (path G x y) -> linked G x y
        --     := by { intro h, cases h with p, induction p with x' x' y' z' h' p' ih,
        --         exact linked.refl,
        --         transitivity y', exact linked.edge h', exact ih }

        -- lemma iff_path : linked G x y <-> nonempty (path G x y)
        --     := ⟨to_path, from_path⟩

        -- @[simp] lemma nodup_point : nodup (point x : path G x x)
        --     := by { unfold nodup, simp }

        -- @[simp] lemma nodup_append {p : path G x y} {h : G.adj y z} : nodup (append p h) <-> nodup p ∧ z ∉ p
        --     := by { induction p, { simp, exact ne_comm }, { simp, push_neg, rw [p_ih,and_assoc,and_assoc],
        --         finish } }

        -- lemma nodup_rev {p : path G x y} : nodup p -> nodup p.rev
        --     := by { induction p, obviously }

        -- lemma nodup_concat {p : path G x y} {p' : path G y z} : nodup (concat p p') <-> nodup p ∧ nodup p' ∧ (∀ u, u ∈ p -> u ∈ p' -> u = y)
        --     := by { induction p with _ _ _ _ _ _ ih; simp, push_neg, split,
        --         { rintros ⟨⟨h1,h2⟩,h3⟩, replace ih := ih.mp h3, refine ⟨⟨h1,ih.1⟩,ih.2.1,_,ih.2.2⟩,
        --             exact false.rec _ ∘ h2 },
        --         { rintros ⟨⟨h1,h2⟩,h3,h4,h5⟩, replace ih := ih.mpr ⟨h2,h3,h5⟩, refine ⟨⟨h1,_⟩,ih⟩,
        --             intro h, apply h1, convert mem_tail, exact h4 h }
        --     }

        -- def path_from_subgraph {G₁ G₂ : simple_graph V} (sub : ∀ {x y : V}, G₁.adj x y -> G₂.adj x y)
        --         (p : path G₁ x y) : path G₂ x y
        --     := path.rec point (λ _ _ _ h _, step $ sub h) p
    end path3
end simple_graph

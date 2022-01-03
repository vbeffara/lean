import tactic
import graph_theory.basic

namespace simple_graph
    inductive path3 {V : Type} (G : simple_graph V) (x : V) : V -> Type
    | point : path3 x
    | step {y z : V} : path3 y -> G.adj y z -> path3 z

    namespace path3
        open path3
        variables {V : Type} {G : simple_graph V} {u v x y z : V} {e : edges G}
        variables {p : path3 G x y} {p' : path3 G y z} {h : G.adj y z} {h' : G.adj u x} {h'' : G.adj z v}

        @[simp] def from_edge : G.adj x y -> path3 G x y := step point

        def cons (p : path3 G y z) (h : G.adj x y) : path3 G x z
            := path3.rec (from_edge h) (λ _ _ _ h ih, ih.step h) p

        def concat (p : path3 G x y) (p' : path3 G y z) : path3 G x z
            := path3.rec p (λ _ _ _ h q, q.step h) p'

        def mem (z : V) (p : path3 G x y) : Prop           := path3.rec (z=x) (λ _ u _ _ h, h ∨ z=u)           p
        def size        (p : path3 G x y) : ℕ              := path3.rec 0     (λ _ _ _ _ l, l+1)               p
        def rev         (p : path3 G x y) : path3 G y x    := path3.rec point (λ _ _ _ h q, q.cons (G.symm h)) p
        def edges       (p : path3 G x y) : list (edges G) := path3.rec []    (λ _ _ _ d e, ⟨d⟩ :: e)          p
        def nodup       (p : path3 G x y) : Prop           := path3.rec true  (λ _ u q _ e, e ∧ ¬(mem u q))    p

        instance : has_mem    V (path3 G x y) := ⟨mem⟩
        instance : has_sizeof   (path3 G x y) := ⟨size⟩

        @[simp] lemma cons_point   :         cons point h  =  from_edge h := rfl
        @[simp] lemma concat_point :       concat p point  =  p           := rfl
        @[simp] lemma mem_point    :   u ∈ (@point _ G x) <-> u = x       := iff.rfl
        @[simp] lemma size_point   :  size (@point _ G x)  =  0           := rfl
        @[simp] lemma rev_point    :   rev (@point _ G x)  =  point       := rfl
        @[simp] lemma edges_point  : edges (@point _ G x)  =  []          := rfl
        @[simp] lemma nodup_point  : nodup (@point _ G x)                 := trivial

        @[simp] lemma cons_step   :     cons (p.step h) h'  =  step (p.cons h') h     := rfl
        @[simp] lemma concat_step : concat p (p'.step h'')  =  step (concat p p') h'' := rfl
        @[simp] lemma mem_step    :           u ∈ p.step h <-> u ∈ p ∨ u = z          := iff.rfl
        @[simp] lemma size_step   :        (p.step h).size  =  p.size + 1             := rfl
        @[simp] lemma rev_step    :         rev (p.step h)  =  cons p.rev (G.symm h)  := rfl
        @[simp] lemma edges_step  :       edges (p.step h)  =  ⟨h⟩ :: edges p         := rfl
        @[simp] lemma nodup_step  :       (p.step h).nodup <-> p.nodup ∧ z ∉ p        := iff.rfl

        lemma mem_tail : y ∈ p := by { cases p, exact rfl, exact or.inr rfl }
        lemma mem_head : x ∈ p := path3.rec rfl (λ _ _ _ _, or.inl) p

        lemma point_of_size_0 : p.size = 0 -> x = y := by { intro h, cases p, refl, contradiction }

        @[simp] lemma mem_cons      :            v ∈ p.cons h' <-> v = u ∨ v ∈ p         := by { induction p; simp [*,or.assoc] }
        @[simp] lemma size_cons     :         size (p.cons h')  =  size p + 1            := by { induction p, obviously }
        @[simp] lemma size_rev      :             size (rev p)  =  size p                := by { induction p, obviously }
        @[simp] lemma mem_rev       :                z ∈ rev p <-> z ∈ p                 := by { induction p; simp [*,or.comm] }
        @[simp] lemma concat_point' :           concat point p  =  p                     := by { induction p, obviously }
        @[simp] lemma concat_step'  : concat (step point h') p  =  cons p h'             := by { induction p, obviously }
        @[simp] lemma concat_cons   :    concat (p.cons h') p'  =  cons (concat p p') h' := by { induction p', obviously }
        @[simp] lemma concat_rev    :        rev (concat p p')  =  concat p'.rev p.rev   := by { induction p', obviously }
        @[simp] lemma concat_size   :       size (concat p p')  =  p.size + p'.size      := by { induction p'; simp [*,add_assoc] }

        @[simp] lemma concat_assoc {p'' : path3 G z u} : concat (concat p p') p'' = concat p (concat p' p'') := by { induction p''; simp [*] }

        @[simp] lemma mem_concat : u ∈ concat p p' <-> u ∈ p ∨ u ∈ p'
            := by { induction p'; simp [*,or_assoc], exact ⟨or.inl,(λ h, or.cases_on h id (λ h, h.symm ▸ mem_tail))⟩ }

        lemma mem_edges : e ∈ p.edges -> e.x ∈ p ∧ e.y ∈ p
            := by { induction p; simp, intro h, cases h; simp[*], left, exact mem_tail }

        lemma mem_of_edges (h : 0 < p.size) : u ∈ p <-> ∃ e ∈ p.edges, u ∈ edges.ends e
            := by { induction p with a b p ha ih, { simp at h, contradiction }, clear h,
                cases nat.eq_zero_or_pos p.size, { cases p, simp, simp at h, contradiction },
                specialize ih h, clear h, simp at ih, split; simp,
                    { intro h1, cases h1,
                        { obtain ⟨e,h2,h3⟩ := ih.mp h1, exact ⟨e, or.inr h2, h3⟩ },
                        exact ⟨⟨ha⟩, or.inl rfl, or.inr h1⟩ },
                    exact ⟨(λ h, or.cases_on h (λ h, or.inl (h.symm ▸ mem_tail)) (λ h, or.inr h)),
                        (λ e he h1, or.inl (ih.mpr ⟨e,he,h1⟩))⟩,
            }

        lemma to_path (h : linked G x y) : nonempty (path3 G x y)
            := by { induction h with _ _ _ h2 ih, use point, cases ih, use ih.step h2 }

        noncomputable def to_path'   (h : linked G x y) : path3 G x y := classical.choice (to_path h)

        lemma from_path : nonempty (path3 G x y) -> linked G x y
            := by { intro h, cases h with p, induction p with _ _ _ h2 ih, refl, exact ih.tail h2 }

        lemma iff_path : linked G x y <-> nonempty (path3 G x y) := ⟨to_path, from_path⟩

        @[simp] lemma nodup_cons : nodup (cons p h') <-> u ∉ p ∧ nodup p
            := by { induction p with a b h1 h2 ih, simp, exact ne_comm,
                simp, push_neg, split,
                { rintros ⟨h1,h2,h3⟩, have h4 := ih.mp h1, exact ⟨⟨h4.1,h2.symm⟩,h4.2,h3⟩ },
                { rintros ⟨⟨h1,h2⟩,h3,h4⟩, exact ⟨ih.mpr ⟨h1,h3⟩,h2.symm,h4⟩ }
            }

        lemma nodup_rev : nodup p -> nodup p.rev := by { induction p; simp, obviously }

        lemma nodup_concat : nodup (concat p p') <-> nodup p ∧ nodup p' ∧ (∀ u, u ∈ p -> u ∈ p' -> u = y)
            := by { induction p' with a b q h2 ih; simp, push_neg, split,
                { rintros ⟨h1,h2,h3⟩, replace ih := ih.mp h1, refine ⟨ih.1,⟨ih.2.1,h3⟩,λ u h4 h5, _⟩,
                    cases h5, exact ih.2.2 u h4 h5, rw h5 at h4, contradiction },
                { rintros ⟨h1,⟨h2,h3⟩,h4⟩, refine ⟨ih.mpr ⟨h1,h2,_⟩,_,h3⟩,
                    intros u h5 h6, refine h4 u h5 (or.inl h6),
                    intro h5, apply h3, rw h4 b h5 (or.inr rfl), exact mem_head } }

        def path_from_subgraph {G₁ G₂ : simple_graph V} (sub : ∀ {x y : V}, G₁.adj x y -> G₂.adj x y)
                (p : path3 G₁ x y) : path3 G₂ x y
            := path3.rec point (λ _ _ _ h q, q.step (sub h)) p
    end path3
end simple_graph

import tactic
import graph_theory.basic

namespace simple_graph
    inductive path {V : Type} (G : simple_graph V) (x : V) : V -> Type
    | point : path x
    | step {y z : V} : path y -> G.adj y z -> path z

    infix ` · `:50 := path.step

    namespace path
        open path
        variables {V : Type} {G : simple_graph V} {u v x y z : V} {e : edges G}
        variables {p : path G x y} {p' : path G y z} {h : G.adj y z} {h' : G.adj u x} {h'' : G.adj z v}

        @[simp] def cons (h : G.adj x y) : Π {z : V}, path G y z -> path G x z
            | _ point    := point · h
            | _ (p · h') := cons p · h'

        infixr ` :: ` := cons

        @[simp] def concat (p : path G x y) : Π {z : V}, path G y z -> path G x z
            | _ point    := p
            | _ (p' · h) := concat p' · h

        infix ` ++ ` := concat

        @[simp] def mem (z : V) : Π {y : V}, path G x y -> Prop
            | _ point   := z = x
            | y (p · h) := mem p ∨ z = y

        instance : has_mem V (path G x y) := ⟨λ z, mem z⟩

        def size        (p : path G x y) : ℕ              := path.rec 0     (λ _ _ _ _ l, l+1)               p
        def rev         (p : path G x y) : path G y x     := path.rec point (λ _ _ _ h q, cons (G.symm h) q) p
        def edges       (p : path G x y) : list (edges G) := path.rec []    (λ _ _ _ d e, ⟨d⟩ :: e)          p
        def nodup       (p : path G x y) : Prop           := path.rec true  (λ _ u q _ e, e ∧ ¬(mem u q))    p

        instance : has_sizeof   (path G x y) := ⟨size⟩

        @[simp] lemma mem_point    :   u ∈ (@point _ G x) <-> u = x       := iff.rfl
        @[simp] lemma size_point   :  size (@point _ G x)  =  0           := rfl
        @[simp] lemma rev_point    :   rev (@point _ G x)  =  point       := rfl
        @[simp] lemma edges_point  : edges (@point _ G x)  =  []          := rfl
        @[simp] lemma nodup_point  : nodup (@point _ G x)                 := trivial

        @[simp] lemma mem_step    :            u ∈ (p · h) <-> u ∈ p ∨ u = z    := iff.rfl
        @[simp] lemma size_step   :           size (p · h)  =  size p + 1       := rfl
        @[simp] lemma rev_step    :            rev (p · h)  =  h.symm :: p.rev  := rfl
        @[simp] lemma edges_step  :          edges (p · h)  =  ⟨h⟩ :: edges p   := rfl
        @[simp] lemma nodup_step  :          nodup (p · h) <-> nodup p ∧ z ∉ p  := iff.rfl

        lemma mem_tail : y ∈ p := by { cases p, exact rfl, exact or.inr rfl }
        lemma mem_head : x ∈ p := path.rec rfl (λ _ _ _ _, or.inl) p

        lemma point_of_size_0 : p.size = 0 -> x = y := by { intro h, cases p, refl, contradiction }

        @[simp] lemma mem_cons      :              v ∈ h' :: p <-> v = u ∨ v ∈ p         := by { induction p; simp [*,or.assoc] }
        @[simp] lemma size_cons     :         size (cons h' p)  =  size p + 1            := by { induction p, obviously }
        @[simp] lemma size_rev      :             size (rev p)  =  size p                := by { induction p, obviously }
        @[simp] lemma mem_rev       :                z ∈ rev p <-> z ∈ p                 := by { induction p; simp [*,or.comm] }
        @[simp] lemma concat_point' :           concat point p  =  p                     := by { induction p, obviously }
        @[simp] lemma concat_step'  : concat (step point h') p  =  cons h' p             := by { induction p, obviously }
        @[simp] lemma concat_cons   :    concat (cons h' p) p'  =  cons h' (concat p p') := by { induction p', obviously }
        @[simp] lemma concat_rev    :        rev (concat p p')  =  concat p'.rev p.rev   := by { induction p', obviously }
        @[simp] lemma size_concat   :       size (concat p p')  =  p.size + p'.size      := by { induction p'; simp [*,add_assoc] }

        @[simp] lemma concat_assoc {p'' : path G z u} : concat (concat p p') p'' = concat p (concat p' p'') := by { induction p''; simp [*] }

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

        lemma to_path (h : linked G x y) : nonempty (path G x y)
            := by { induction h with _ _ _ h2 ih, use point, cases ih, use ih.step h2 }

        noncomputable def to_path'   (h : linked G x y) : path G x y := classical.choice (to_path h)

        lemma from_path : nonempty (path G x y) -> linked G x y
            := by { intro h, cases h with p, induction p with _ _ _ h2 ih, refl, exact ih.tail h2 }

        lemma iff_path : linked G x y <-> nonempty (path G x y) := ⟨to_path, from_path⟩

        @[simp] lemma nodup_cons : nodup (cons h' p) <-> u ∉ p ∧ nodup p
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
                (p : path G₁ x y) : path G₂ x y
            := path.rec point (λ _ _ _ h q, q.step (sub h)) p
    end path
end simple_graph

import tactic
import graph_theory.basic

namespace simple_graph
    inductive path {V : Type} (G : simple_graph V) (x : V) : V -> Type
    | point : path x
    | step {y z : V} : path y -> G.adj y z -> path z

    infix ` · `:50 := path.step

    namespace path
        open path
        variables {V : Type} {G G₁ G₂ : simple_graph V} {u v x y z : V} {e : edge G}
        variables {p : path G x y} {p' : path G y z} {p'' : path G z u} {h : G.adj y z} {h' : G.adj u x} {h'' : G.adj z v}

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
            | y (p · _) := mem p ∨ z = y

        instance : has_mem V (path G x y) := ⟨λ z, mem z⟩

        @[simp] def size : Π {y : V}, path G x y -> ℕ
            | _ point   := 0
            | _ (p · _) := size p + 1

        instance : has_sizeof (path G x y) := ⟨size⟩

        @[simp] def rev : Π {y : V}, path G x y -> path G y x
            | _ point   := point
            | _ (p · h) := h.symm :: rev p

        @[simp] def edges : Π {y : V}, path G x y -> list (edge G)
            | _ point   := []
            | _ (p · h) := ⟨h⟩ :: edges p

        @[simp] def nodup : Π {y : V}, path G x y -> Prop
            | _ point   := true
            | y (p · _) := nodup p ∧ y ∉ p

        @[simp] lemma mem_point    : u ∈ (@point _ G x) <-> u = x            := iff.rfl
        @[simp] lemma mem_step     :        u ∈ (p · h) <-> u ∈ p ∨ u = z    := iff.rfl
        @[simp] lemma mem_cons     :        v ∈ h' :: p <-> v = u ∨ v ∈ p    := by { induction p; simp[*,or_assoc] }
        @[simp] lemma size_cons    :     size (h' :: p)  =  size p + 1       := by { induction p, obviously }
        @[simp] lemma size_rev     :       size (rev p)  =  size p           := by { induction p, obviously }
        @[simp] lemma mem_rev      :          z ∈ rev p <-> z ∈ p            := by { induction p; simp [*,or.comm] }
        @[simp] lemma concat_point :         point ++ p  =  p                := by { induction p, obviously }
        @[simp] lemma concat_step  :  (point · h') ++ p  =  h' :: p          := by { induction p, obviously }
        @[simp] lemma concat_cons  :    (h' :: p) ++ p'  =  h' :: (p ++ p')  := by { induction p', obviously }
        @[simp] lemma concat_rev   :      rev (p ++ p')  =  rev p' ++ rev p  := by { induction p', obviously }
        @[simp] lemma size_concat  :     size (p ++ p')  =  size p + size p' := by { induction p'; simp [*,add_assoc] }
        @[simp] lemma concat_assoc :   (p ++ p') ++ p''  =  p ++ (p' ++ p'') := by { induction p''; simp [*] }

        lemma mem_tail : y ∈ p := by { cases p, exact rfl, exact or.inr rfl }
        lemma mem_head : x ∈ p := by { induction p, simp, left, exact p_ih }

        lemma point_of_size_0 : p.size = 0 -> x = y := by { intro h, cases p, refl, contradiction }

        @[simp] lemma mem_concat : u ∈ concat p p' <-> u ∈ p ∨ u ∈ p'
            := by { induction p'; simp [*,or_assoc], exact ⟨or.inl,(λ h, or.cases_on h id (λ h, h.symm ▸ mem_tail))⟩ }

        lemma mem_edges : e ∈ p.edges -> e.x ∈ p ∧ e.y ∈ p
            := by { induction p; simp, intro h, cases h; simp[*], left, exact mem_tail }

        lemma mem_of_edges (h : 0 < p.size) : u ∈ p <-> ∃ e ∈ p.edges, u ∈ edge.ends e
            := by { induction p with a b p ha ih, { simp at h, contradiction }, clear h,
                cases nat.eq_zero_or_pos p.size, { cases p, simp, simp at h, contradiction },
                specialize ih h, clear h, simp at ih, split; simp,
                    { intro h1, cases h1,
                        { obtain ⟨e,h2,h3⟩ := ih.mp h1, exact ⟨e, or.inr h2, h3⟩ },
                        exact ⟨⟨ha⟩, or.inl rfl, or.inr h1⟩ },
                    exact ⟨(λ h, or.cases_on h (λ h, or.inl (h.symm ▸ mem_tail)) (λ h, or.inr h)),
                        (λ e he h1, or.inl (ih.mpr ⟨e,he,h1⟩))⟩,
            }

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

        def path_from_subgraph (sub : ∀ {x y}, G₁.adj x y -> G₂.adj x y) : Π {y : V}, path G₁ x y -> path G₂ x y
            | _ point   := point
            | _ (p · h) := path_from_subgraph p · sub h
    end path

    variables {V : Type} {G : simple_graph V} {x y z : V}

    def linked    (G : simple_graph V) (x y : V) := nonempty (path G x y)
    def connected (G : simple_graph V)           := ∀ x y, linked G x y

    class connected_graph (G : simple_graph V) := (conn : connected G)

    namespace linked
        open path

        lemma edge : G.adj x y                 -> linked G x y := λ h, ⟨point · h⟩
        lemma cons : G.adj x y -> linked G y z -> linked G x z := λ e h, h.cases_on (λ p, nonempty.intro (e :: p))
        lemma step : linked G x y -> G.adj y z -> linked G x z := λ h e, h.cases_on (λ p, nonempty.intro (p · e))

        @[refl]  lemma refl  : linked G x x                                 := ⟨point⟩
        @[symm]  lemma symm  : linked G x y -> linked G y x                 := λ h, h.cases_on (λ p, nonempty.intro p.rev)
        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z := λ h₁ h₂, h₁.cases_on (λ p₁, h₂.cases_on (λ p₂, nonempty.intro (p₁ ++ p₂)))

        lemma equiv : equivalence (linked G) := ⟨@refl _ _, @symm _ _, @trans _ _⟩

        noncomputable def to_path' : linked G x y -> path G x y := classical.choice

        lemma linked_of_subgraph {G₁ G₂ : simple_graph V} (sub : ∀ {x y : V}, G₁.adj x y -> G₂.adj x y) : linked G₁ x y -> linked G₂ x y
            := by { intro h, cases h with p, induction p with a b h1 h2 ih, refl, exact ih.step (sub h2) }
    end linked
end simple_graph

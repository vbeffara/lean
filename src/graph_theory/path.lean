import tactic
import combinatorics.simple_graph.connectivity
import graph_theory.basic

namespace simple_graph
    variables {V : Type}

    def mypath (G : simple_graph V) := walk G

    infix ` · `:50 := λ p h, walk.append p (walk.cons h walk.nil)
    infixr ` :: `  := walk.cons
    infix ` ++ `   := walk.append

    namespace mypath
        open mypath walk

        variables {G G₁ G₂ : simple_graph V} {u v x y z : V} {e : edge G}
        variables {p : mypath G x y} {p' : mypath G y z} {p'' : mypath G z u} {h : G.adj y z} {h' : G.adj u x} {h'' : G.adj z v}

        @[simp] def point  {x : V} : mypath G x x                 := nil
        @[simp] def cons   (h : G.adj x y) (p : mypath G y z)     := p.cons h
        @[simp] def concat (p : mypath G x y) (p' : mypath G y z) := p.append p'
        @[simp] def mem    (z : V) (p : mypath G x y)             := z ∈ p.support
        @[simp] def size   (p : mypath G x y)                     := p.length
        @[simp] def rev    (p : mypath G x y)                     := walk.reverse p
        @[simp] def nodup  (p : mypath G x y)                     := p.support.nodup

        instance : has_mem V (walk G x y) := ⟨mem⟩
        instance : has_mem V (mypath G x y) := ⟨mem⟩
        instance : has_sizeof (mypath G x y) := ⟨size⟩

        @[simp] def myedges : Π {x y : V}, mypath G x y -> list (edge G)
            | _ _ nil             := []
            | _ _ (walk.cons h p) := ⟨h⟩ :: myedges p

        @[simp] lemma mem_point'   :   u ∈ (@nil _ G x) <-> u = x            := list.mem_singleton
        @[simp] lemma size_rev     :       size (rev p)  =  size p           := length_reverse p
        @[simp] lemma concat_rev   :      rev (p ++ p')  =  rev p' ++ rev p  := reverse_append p p'
        @[simp] lemma size_concat  :     size (p ++ p')  =  size p + size p' := length_append p p'
        @[simp] lemma concat_assoc :   (p ++ p') ++ p''  =  p ++ (p' ++ p'') := (append_assoc p p' p'').symm

        lemma mem_tail : y ∈ p := end_mem_support _
        lemma mem_head : x ∈ p := start_mem_support _

        lemma point_of_size_0 : p.size = 0 -> x = y := by { intro h, cases p, refl, contradiction }

        @[simp] lemma mem_concat : u ∈ append p p' <-> u ∈ p ∨ u ∈ p' := mem_support_append_iff p p'

        lemma mem_edges : e ∈ p.myedges -> e.x ∈ p ∧ e.y ∈ p
            := by { induction p with u u v w h p ih; simp, intro h', cases h',
                { subst e, split, exact mem_head, right, exact mem_head },
                { specialize ih h', exact ⟨or.inr ih.1, or.inr ih.2⟩ }
            }

        lemma mem_of_edges (h : 0 < p.size) : u ∈ p <-> ∃ e ∈ p.myedges, u ∈ edge.ends e := sorry
            -- := by { induction p with a b p ha ih, { simp at h, contradiction }, clear h,
            --     cases nat.eq_zero_or_pos p.size, { cases p, simp, simp at h, contradiction },
            --     specialize ih h, clear h, simp at ih, split; simp,
            --         { intro h1, cases h1,
            --             { obtain ⟨e,h2,h3⟩ := ih.mp h1, exact ⟨e, or.inr h2, h3⟩ },
            --             exact ⟨⟨ha⟩, or.inl rfl, or.inr h1⟩ },
            --         exact ⟨(λ h, or.cases_on h (λ h, or.inl (h.symm ▸ mem_tail)) (λ h, or.inr h)),
            --             (λ e he h1, or.inl (ih.mpr ⟨e,he,h1⟩))⟩,
            -- }

        @[simp] lemma nodup_cons : nodup (cons h' p) <-> u ∉ p ∧ nodup p := sorry
            -- := by { induction p with a b h1 h2 ih, simp, exact ne_comm,
            --     simp, push_neg, split,
            --     { rintros ⟨h1,h2,h3⟩, have h4 := ih.mp h1, exact ⟨⟨h4.1,h2.symm⟩,h4.2,h3⟩ },
            --     { rintros ⟨⟨h1,h2⟩,h3,h4⟩, exact ⟨ih.mpr ⟨h1,h3⟩,h2.symm,h4⟩ }
            -- }

        lemma nodup_rev : nodup p -> nodup p.rev := sorry
            -- := by { induction p; simp, obviously }

        lemma nodup_concat : nodup (append p p') <-> nodup p ∧ nodup p' ∧ (∀ u, u ∈ p -> u ∈ p' -> u = y) := sorry
            -- := by { induction p' with a b q h2 ih; simp, push_neg, split,
            --     { rintros ⟨h1,h2,h3⟩, replace ih := ih.mp h1, refine ⟨ih.1,⟨ih.2.1,h3⟩,λ u h4 h5, _⟩,
            --         cases h5, exact ih.2.2 u h4 h5, rw h5 at h4, contradiction },
            --     { rintros ⟨h1,⟨h2,h3⟩,h4⟩, refine ⟨ih.mpr ⟨h1,h2,_⟩,_,h3⟩,
            --         intros u h5 h6, refine h4 u h5 (or.inl h6),
            --         intro h5, apply h3, rw h4 b h5 (or.inr rfl), exact mem_head } }

        def path_from_subgraph (sub : ∀ {x y}, G₁.adj x y -> G₂.adj x y) : Π {x y : V}, mypath G₁ x y -> mypath G₂ x y
            | _ _ nil             := nil
            | _ _ (walk.cons h p) := walk.cons (sub h) (path_from_subgraph p)
    end mypath

    variables {G : simple_graph V} {x y z : V}

    def linked    (G : simple_graph V) (x y : V) := nonempty (mypath G x y)
    def connected (G : simple_graph V)           := ∀ x y, linked G x y

    class connected_graph (G : simple_graph V) := (conn : connected G)

    namespace linked
        open mypath

        lemma edge : G.adj x y                 -> linked G x y := λ h, ⟨walk.cons h walk.nil⟩
        lemma cons : G.adj x y -> linked G y z -> linked G x z := λ e h, h.cases_on (λ p, nonempty.intro (e :: p))
        lemma step : linked G x y -> G.adj y z -> linked G x z := λ h e, h.cases_on (λ p, nonempty.intro (p · e))

        @[refl]  lemma refl  : linked G x x                                 := ⟨point⟩
        @[symm]  lemma symm  : linked G x y -> linked G y x                 := λ h, h.cases_on (λ p, nonempty.intro p.rev)
        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z := λ h₁ h₂, h₁.cases_on (λ p₁, h₂.cases_on (λ p₂, nonempty.intro (p₁ ++ p₂)))

        lemma equiv : equivalence (linked G) := ⟨@refl _ _, @symm _ _, @trans _ _⟩

        noncomputable def to_path' : linked G x y -> mypath G x y := classical.choice

        lemma linked_of_subgraph {G₁ G₂ : simple_graph V} (sub : ∀ {x y : V}, G₁.adj x y -> G₂.adj x y) : linked G₁ x y -> linked G₂ x y
            := by { intro h, cases h with p, induction p with a b h1 h2 ih, refl, exact cons (sub ih) p_ih }
    end linked
end simple_graph

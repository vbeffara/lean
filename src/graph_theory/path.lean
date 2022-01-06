import tactic
import combinatorics.simple_graph.connectivity
import graph_theory.basic

namespace simple_graph
    variables {V : Type}

    namespace walk
        infixr ` :: ` := cons
        infix  ` ++ ` := append
    end walk

    namespace mypath
        open mypath walk

        variables {G G₁ G₂ : simple_graph V} {u v x y z : V} {e : edge G}
        variables {p : walk G x y} {p' : walk G y z} {p'' : walk G z u} {h : G.adj y z} {h' : G.adj u x} {h'' : G.adj z v}

        @[simp] def myedges : Π {x y : V}, walk G x y -> list (edge G)
            | _ _ nil             := []
            | _ _ (walk.cons h p) := ⟨h⟩ :: myedges p

        lemma point_of_size_0 : p.length = 0 -> x = y := by { intro h, cases p, refl, contradiction }

        lemma mem_edges : e ∈ myedges p -> e.x ∈ p.support ∧ e.y ∈ p.support
            := by { induction p with u u v w h p ih; simp, intro h', cases h',
                { subst e, split, left, refl, right, exact start_mem_support _ },
                { specialize ih h', exact ⟨or.inr ih.1, or.inr ih.2⟩ }
            }

        lemma mem_of_edges (h : 0 < p.length) : u ∈ p.support <-> ∃ e ∈ myedges p, u ∈ edge.ends e
            := by { induction p with u u v w h p ih, { simp at h, contradiction }, clear h,
                cases nat.eq_zero_or_pos (length p), { cases p, simp, simp at h_1, contradiction },
                specialize ih h_1, clear h_1, simp at ih, split; simp,
                    { intro h1, cases h1,
                        { subst h1, exact ⟨⟨h⟩, or.inl rfl, or.inl rfl⟩ },
                        { obtain ⟨e,h2,h3⟩ := ih.mp h1, exact ⟨e, or.inr h2, h3⟩ } },
                    exact ⟨(λ h, or.cases_on h or.inl (λ h, by { subst h, exact or.inr (start_mem_support _) })),
                        (λ e he h1, or.inr (ih.mpr ⟨e,he,h1⟩))⟩,
            }

        lemma nodup_rev : p.support.nodup -> p.reverse.support.nodup
            := by { rw (support_reverse p), exact list.nodup_reverse.mpr }

        lemma nodup_concat : (append p p').support.nodup <-> p.support.nodup ∧ p'.support.nodup ∧ (∀ u, u ∈ p.support -> u ∈ p'.support -> u = y)
            := by { induction p with a a b c h q ih; simp, push_neg, split,
                { rintros ⟨⟨h1,h2⟩,h3⟩, replace ih := ih.mp h3, refine ⟨⟨h1,ih.1⟩,ih.2.1,_,λ u h4 h5, _⟩,
                    intro, contradiction, exact ih.2.2 u h4 h5 },
                { rintros ⟨⟨h1,h2⟩,h3,h4,h5⟩, refine ⟨⟨h1,_⟩,_⟩,
                    intro h5, apply h1, rw h4 h5, exact end_mem_support _,
                    refine ih.mpr ⟨h2,h3,_⟩, intros u hu h'u, exact h5 u hu h'u } }

        def path_from_subgraph (sub : ∀ {x y}, G₁.adj x y -> G₂.adj x y) : Π {x y : V}, walk G₁ x y -> walk G₂ x y
            | _ _ nil             := nil
            | _ _ (walk.cons h p) := walk.cons (sub h) (path_from_subgraph p)
    end mypath

    variables {G : simple_graph V} {x y z : V}

    def linked    (G : simple_graph V) (x y : V) := nonempty (walk G x y)
    def connected (G : simple_graph V)           := ∀ x y, linked G x y

    class connected_graph (G : simple_graph V) := (conn : connected G)

    namespace linked
        open mypath walk

        @[refl]  lemma refl  : linked G x x                                 := ⟨nil⟩
        @[symm]  lemma symm  : linked G x y -> linked G y x                 := λ h, h.cases_on (λ p, nonempty.intro p.reverse)
        @[trans] lemma trans : linked G x y -> linked G y z -> linked G x z := λ h₁ h₂, h₁.cases_on (λ p₁, h₂.cases_on (λ p₂, nonempty.intro (p₁ ++ p₂)))

        lemma edge : G.adj x y                 -> linked G x y := λ h, ⟨walk.cons h walk.nil⟩
        lemma cons : G.adj x y -> linked G y z -> linked G x z := λ h h', trans (edge h) h'

        lemma equiv : equivalence (linked G) := ⟨@refl _ _, @symm _ _, @trans _ _⟩

        noncomputable def to_path' : linked G x y -> walk G x y := classical.choice

        lemma linked_of_subgraph {G₁ G₂ : simple_graph V} (sub : ∀ {x y : V}, G₁.adj x y -> G₂.adj x y) : linked G₁ x y -> linked G₂ x y
            := by { intro h, cases h with p, induction p with a b h1 h2 ih, refl, exact cons (sub ih) p_ih }
    end linked
end simple_graph

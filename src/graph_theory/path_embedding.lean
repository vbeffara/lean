import graph_theory.path
open function

namespace simple_graph
    variables {V V' V'': Type}

    structure path_embedding (G : simple_graph V) (G' : simple_graph V') :=
        (f        : V ↪ V')
        (df       : Π e : edges G, path G' (f e.x) (f e.y))
        --
        (nodup    : ∀ e : edges G, (df e).nodup)
        (sym      : ∀ e : edges G, df e.flip = (df e).rev)
        --
        (endpoint : ∀ {e x},    f x ∈ df e              -> x ∈ e.ends)
        (disjoint : ∀ {e e' z},   z ∈ df e -> z ∈ df e' -> e.ends = e'.ends ∨ ∃ x, z = f x)

    def embeds_into (G : simple_graph V) (G' : simple_graph V') := nonempty (path_embedding G G')

    namespace path_embedding
        variables {G : simple_graph V} {G' : simple_graph V'} (F : path_embedding G G') {x y z : V}

        lemma nop {e : edges G} : 0 < (F.df e).size
            := by {
                cases nat.eq_zero_or_pos (F.df e).size, swap, exact h, exfalso,
                exact G.ne_of_adj e.h (F.f.injective (path.point_of_size_0 h))
            }

        def follow (p : path G x y) : path G' (F.f x) (F.f y)
            := path.rec (λ _, path.point _) (λ _ _ _ h' _, path.concat (F.df ⟨h'⟩)) p

        @[simp] lemma follow_point : follow F (path.point x) = path.point (F.f x) := rfl

        @[simp] lemma follow_step {h : G.adj x y} {p : path G y z} : follow F (path.step h p) = path.concat (F.df ⟨h⟩) (follow F p) := rfl

        lemma mem_follow {z} {p : path G x y} (h : 0 < p.size) : z ∈ follow F p <-> ∃ e ∈ p.edges, z ∈ F.df e
            := by {
                revert h, induction p with x' x' y' z' h' p' ih; simp, split; intro H,
                    { cases H,
                        { exact ⟨_, or.inl rfl, H⟩ },
                        { cases p'; simp at *,
                            { convert path.mem_tail },
                            { cases (ih.mp H) with e he, exact ⟨e, or.inr he.1, he.2⟩ }
                        }
                    },
                    { obtain ⟨e,H1,H2⟩ := H, cases H1,
                        { left, subst H1, exact H2 },
                        { right, cases p',
                            { simp at H1, contradiction },
                            { refine (ih _).mpr ⟨e,H1,H2⟩, simp }
                        }
                    }
            }

        lemma follow_nodup {p : path G x y} (h : p.nodup) : (follow F p).nodup
            := by {
                induction p with x' x' y' z' h' p' ih; simp [path.nodup_concat], rw path.nodup_step at h,
                refine ⟨F.nodup _, ih h.2, _⟩, rintros u h3 h4,
                cases nat.eq_zero_or_pos p'.size with h5 h5, { cases p', exact h4, simp at h5, contradiction },
                obtain ⟨e,h7,h8⟩ := (mem_follow F h5).mp h4,
                cases path.mem_edges h7, cases F.disjoint h3 h8 with h9 h9,
                    { exfalso, apply h.1, apply (path.mem_of_edges h5).mpr ⟨e,h7,_⟩,
                        rw <-h9, exact sym2.mem_mk_left _ _ },
                    {
                        obtain ⟨v,_⟩ := h9, subst u,
                        have h10 := F.endpoint h3,
                        cases sym2.mem_iff.mp h10 with h10 h10; simp at h10; subst h10,
                        exfalso, apply h.1, cases sym2.mem_iff.mp (F.endpoint h8) with h12 h12;
                        subst h12, exact left, exact right
                    }
            }

        @[simp] lemma follow_append {p : path G x y} {h : G.adj y z} : follow F (p.append h) = (follow F p).concat (F.df ⟨h⟩)
            := by { induction p; simp [*] }

        lemma follow_rev {p : path G x y} : follow F p.rev = (follow F p).rev
            := by {
                induction p with x' x' y' z' h' p' ih, refl,
                rw [follow_step,path.rev_step,follow_append,ih,path.concat_rev], congr,
                set e : edges G := ⟨h'⟩, exact F.sym e
            }
    end path_embedding

    namespace path_embedding
        variables {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

        def comp (F : path_embedding G G') (F' : path_embedding G' G'') : path_embedding G G'' := {
            f := ⟨F'.f ∘ F.f, injective.comp F'.f.inj' F.f.inj'⟩,
            df := λ e, follow F' (F.df e),
            --
            nodup := λ e, (follow_nodup F') (F.nodup _),
            sym := by { intro e, rewrite F.sym e, apply follow_rev },
            --
            endpoint := by {
                intros e x h1, obtain ⟨e',h4,h5⟩ := (mem_follow F' (nop F)).mp h1,
                exact F.endpoint ((path.mem_of_edges (nop _)).mpr ⟨e',h4,F'.endpoint h5⟩)
            },
            --
            disjoint := by {
                intros e e' z h1 h2,
                replace h1 := (mem_follow _ (nop _)).mp h1, obtain ⟨e1,h3,h4⟩ := h1,
                replace h2 := (mem_follow _ (nop _)).mp h2, obtain ⟨e2,h5,h6⟩ := h2,
                have h7 := F'.disjoint h4 h6, cases h7,
                {
                    left, clear h4 h6,
                    replace h3 := path.mem_edges h3,
                    replace h5 := path.mem_edges h5,
                    replace h5 : e1.x ∈ F.df e' ∧ e1.y ∈ F.df e' := by {
                        cases edges.same_iff.mpr h7; subst e2,
                        exact h5, simp at h5, exact h5.symm
                    }, clear h7,
                    cases F.disjoint h3.1 h5.1 with h10 h10, exact h10,
                    obtain ⟨x,h10⟩ := h10, rw h10 at h3 h5,
                    cases F.disjoint h3.2 h5.2 with h11 h11, exact h11,
                    obtain ⟨y,h11⟩ := h11, rw h11 at h3 h5,
                    have h12 := F.endpoint h3.1,
                    have h13 := F.endpoint h3.2,
                    have h14 := F.endpoint h5.1,
                    have h15 := F.endpoint h5.2,
                    have h16 : x ≠ y := by { intro h, apply G'.ne_of_adj e1.h, convert congr_arg F.f h },
                    exact edges.sym2_eq h16 h12 h13 h14 h15
                },
                {
                    obtain ⟨y,h8⟩ := h7, subst z,
                    replace h4 := F'.endpoint h4,
                    replace h6 := F'.endpoint h6,
                    replace h3 := path.mem_edges h3,
                    replace h5 := path.mem_edges h5,
                    replace h3 : y ∈ F.df e, by { cases edges.mem_edge.mp h4; subst h, exact h3.1, exact h3.2 },
                    replace h5 : y ∈ F.df e', by { cases edges.mem_edge.mp h6; subst h, exact h5.1, exact h5.2 },
                    cases F.disjoint h3 h5 with h9 h9,
                        { left, exact h9 },
                        { obtain ⟨x,h9⟩ := h9, subst h9, right, use x, refl }
                }
            }
        }

        theorem trans : embeds_into G G' -> embeds_into G' G'' -> embeds_into G G''
            := by { intros F F', cases F, cases F', use comp F F' }
    end path_embedding
end simple_graph
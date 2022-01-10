import graph_theory.path
open function

namespace simple_graph
    variables {V V' V'': Type}

    structure path_embedding (G : simple_graph V) (G' : simple_graph V') :=
        (f        : V ↪ V')
        (df       : Π e : step G, walk G' (f e.x) (f e.y))
        --
        (nodup    : ∀ e : step G, (df e).support.nodup)
        (sym      : ∀ e : step G, df e.flip = (df e).reverse)
        --
        (endpoint : ∀ {e x},    f x ∈ (df e).support                        -> x ∈ e.ends)
        (disjoint : ∀ {e e' z},   z ∈ (df e).support -> z ∈ (df e').support -> e.ends = e'.ends ∨ ∃ x, z = f x)

    def embeds_into (G : simple_graph V) (G' : simple_graph V') := nonempty (path_embedding G G')

    namespace path_embedding
        variables {G : simple_graph V} {G' : simple_graph V'} (F : path_embedding G G')
        variables {x y z : V} {p : walk G x y} {p' : walk G y z}
        open mypath walk

        lemma nop {e : step G} : 0 < (F.df e).length
            := by { cases nat.eq_zero_or_pos (F.df e).length, swap, exact h, exfalso,
                exact G.ne_of_adj e.h (F.f.injective (mypath.point_of_size_0 h)) }

        @[simp] def follow : Π {x y : V}, walk G x y -> walk G' (F.f x) (F.f y)
            | _ _ nil        := nil
            | _ _ (cons h p) := F.df ⟨h⟩ ++ follow p

        @[simp] lemma follow_append : follow F (p ++ p') = follow F p ++ follow F p'
            := by { induction p, refl, simp [*,append_assoc] }

        lemma mem_follow {z} (h : 0 < length p) : z ∈ (follow F p).support <-> ∃ e ∈ mypath.myedges p, z ∈ (F.df e).support
            := by {
                revert h, induction p with u u v w h p ih; simp, split; intro H,
                    { cases H,
                        { exact ⟨⟨h⟩,or.inl rfl,H⟩ },
                        { cases p,
                            { simp at *, rw H, exact end_mem_support _ },
                            { simp at ih H, obtain ⟨e,h1,h2⟩ := ih.mp H, refine ⟨e,or.inr h1,h2⟩ },
                        }
                    },
                    { obtain ⟨e,H1,H2⟩ := H, cases H1,
                        { left, subst H1, exact H2 },
                        { right, cases p,
                            { simp at H1, contradiction },
                            { refine (ih _).mpr ⟨e,H1,H2⟩, simp }
                        }
                    }
            }

        lemma follow_nodup {p : walk G x y} (h : p.support.nodup) : (follow F p).support.nodup
            := by {
                induction p with u u v w h p ih; simp, simp at h, apply nodup_concat.mpr,

                refine ⟨F.nodup _, ih h.2, _⟩, rintros z h3 h4,
                cases nat.eq_zero_or_pos p.length with h5 h5, { cases p, simp at h4, exact h4, simp at h5, contradiction },
                obtain ⟨e,h7,h8⟩ := (mem_follow F h5).mp h4,
                cases mypath.mem_edges h7, cases F.disjoint h3 h8 with h9 h9,
                    { exfalso, apply h.1, apply (mypath.mem_of_edges h5).mpr ⟨e,h7,_⟩, rw <-h9, exact sym2.mem_mk_left _ _ },
                    {
                        obtain ⟨v,_⟩ := h9, subst z, have h10 := F.endpoint h3,
                        cases sym2.mem_iff.mp h10 with h10 h10; simp at h10; subst h10,
                        exfalso, apply h.1, cases sym2.mem_iff.mp (F.endpoint h8) with h12 h12;
                        subst h12, exact left, exact right
                    }
            }

        lemma follow_rev {p : walk G x y} : follow F p.reverse = (follow F p).reverse
            := by { induction p with u u v w h p ih, refl, simp [ih.symm], congr, exact F.sym ⟨h⟩ }
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
                exact F.endpoint ((mypath.mem_of_edges (nop _)).mpr ⟨e',h4,F'.endpoint h5⟩)
            },
            --
            disjoint := by {
                intros e e' z h1 h2,
                replace h1 := (mem_follow _ (nop _)).mp h1, obtain ⟨e1,h3,h4⟩ := h1,
                replace h2 := (mem_follow _ (nop _)).mp h2, obtain ⟨e2,h5,h6⟩ := h2,
                have h7 := F'.disjoint h4 h6, cases h7,
                {
                    left, clear h4 h6,
                    replace h3 := mypath.mem_edges h3,
                    replace h5 := mypath.mem_edges h5,
                    replace h5 : e1.x ∈ (F.df e').support ∧ e1.y ∈ (F.df e').support := by {
                        cases step.same_iff.mpr h7; subst e2,
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
                    exact sym2.eq_of_two_members h16 h12 h13 h14 h15
                },
                {
                    obtain ⟨y,h8⟩ := h7, subst z,
                    replace h4 := F'.endpoint h4,
                    replace h6 := F'.endpoint h6,
                    replace h3 := mypath.mem_edges h3,
                    replace h5 := mypath.mem_edges h5,
                    replace h3 : y ∈ (F.df e).support, by { simp at h4, cases h4; subst h4, exact h3.1, exact h3.2 },
                    replace h5 : y ∈ (F.df e').support, by { simp at h6, cases h6; subst h6, exact h5.1, exact h5.2 },
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

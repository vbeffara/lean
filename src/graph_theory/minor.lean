import tactic
import graph_theory.basic graph_theory.path
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
        (disjoint : ∀ {e e' z},   z ∈ df e -> z ∈ df e' -> e.same e' ∨ ∃ x, z = f x)

    def embeds_into (G : simple_graph V) (G' : simple_graph V') := nonempty (path_embedding G G')

    namespace path_embedding
        variables {G : simple_graph V} {G' : simple_graph V'} (F : path_embedding G G') {x y z : V}

        lemma nop {e : edges G} : 0 < (F.df e).size
            := by {
                cases nat.eq_zero_or_pos (F.df e).size, swap, assumption,
                have h' := F.f.injective (path.point_of_size_0 h),
                have h'' := e.h, rw h' at h'',
                have h''' := G.loopless e.y h'',
                contradiction
            }

        -- lemma endpoint_init {e : edges G} : F.f x ∈ (F.df e).p.init <-> x = e.x
        --     := sorry

        -- lemma endpoint_tail {e : edges G} : F.f x ∈ (F.df e).p.tail <-> x = e.y
        --     := sorry

        -- def follow_llist : Π (l : llist V) (h : l.is_path G.adj), llist V'
        --     | (llist.pt v)     _ := llist.pt (F.f v)
        --     | (llist.cons v l) h := llist.concat (F.df ⟨h.1⟩) (follow_llist l h.2)

        -- lemma follow_nop {l h} (hz : 0 < llist.size l) : 0 < (follow_llist F l h).size
        --     := by { cases l, { cases hz },
        --         { rw [follow_llist,llist.concat_size], apply nat.lt_add_right, apply F.nop } }

        -- @[simp] lemma follow_head {l h} : (follow_llist F l h).head = F.f l.head
        --     := by { induction l with v v l hr; rw follow_llist, { refl },
        --         { rw [llist.head_concat], exact (F.df _).hx,
        --             rw [llist.compat,hr], exact (F.df _).hy } }

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
                    { exfalso, apply h.1, cases h9; subst h9; assumption },
                    {
                        obtain ⟨v,_⟩ := h9, subst u,
                        have h10 := F.endpoint h3, cases h10; simp at h10; subst h10,
                        exfalso, apply h.1, cases F.endpoint h8 with h12 h12,
                        subst h12, assumption, replace h12 : v = e.y := h12, subst h12, assumption
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
                intros e x h1,
                apply F.endpoint,
                obtain ⟨e',h4,h5⟩ := (mem_follow F' (nop F)).mp h1,
                suffices : F.f x ∈ e'.ends, by {
                    apply path.mem_of_edges.mpr, use e', exact ⟨h4,this⟩, exact (nop F)
                },
                exact F'.endpoint h5
            },
            --
            disjoint := by {
                intros e e' z h1 h2,
                replace h1 := (mem_follow _ (nop _)).mp h1, obtain ⟨e1,h3,h4⟩ := h1,
                replace h2 := (mem_follow _ (nop _)).mp h2, obtain ⟨e2,h5,h6⟩ := h2,
                have h7 := F'.disjoint h4 h6, cases h7,
                {
                    have h8 := path.mem_edges h3,
                    have h9 := path.mem_edges h5,
                    cases h7; subst e2,
                    {
                        have h10 := F.disjoint h8.1 h9.1,
                        have h11 := F.disjoint h8.2 h9.2,
                        cases h10 with h10 h10, left, assumption,
                        cases h11 with h11 h11, left, assumption,
                        cases h10 with x h10, rw h10 at *,
                        cases h11 with y h11, rw h11 at *,
                        have h12 := F.endpoint h8.1,
                        have h13 := F.endpoint h8.2,
                        have h14 := F.endpoint h9.1,
                        have h15 := F.endpoint h9.2,
                        have h16 : x ≠ y, by { intro h, subst y, apply edges.strict e1, cc },
                        left, apply edges.same_of_same_ends h16; assumption
                    },
                    {
                        simp at h9,
                        have h10 := F.disjoint h8.1 h9.2,
                        have h11 := F.disjoint h8.2 h9.1,
                        cases h10 with h10 h10, left, assumption,
                        cases h11 with h11 h11, left, assumption,
                        cases h10 with x h10, rw h10 at *,
                        cases h11 with y h11, rw h11 at *,
                        have h12 := F.endpoint h8.1,
                        have h13 := F.endpoint h8.2,
                        have h14 := F.endpoint h9.1,
                        have h15 := F.endpoint h9.2,
                        have h16 : x ≠ y, by { intro h, subst y, apply edges.strict e1, cc },
                        left, apply edges.same_of_same_ends h16; assumption
                    }
                },
                {
                    obtain ⟨y,h8⟩ := h7, subst z,
                    replace h4 := F'.endpoint h4,
                    replace h6 := F'.endpoint h6,
                    replace h3 := path.mem_edges h3,
                    replace h5 := path.mem_edges h5,
                    have h7 : y ∈ F.df e, by { cases edges.mem_edge.mp h4; subst h, exact h3.1, exact h3.2 },
                    have h8 : y ∈ F.df e', by { cases edges.mem_edge.mp h6; subst h, exact h5.1, exact h5.2 },
                    have h9 := F.disjoint h7 h8, cases h9,
                        { left, assumption },
                        { cases h9 with x h9, subst h9, right, use x, refl }
                }
            }
        }

        theorem trans : embeds_into G G' -> embeds_into G' G'' -> embeds_into G G''
            := by { intros F F', cases F, cases F', use comp F F' }
    end path_embedding

    namespace contraction
        -- structure chunks {V : Type} (G : simple_graph V) :=
        --     (rel : V -> V -> Prop)
        --     (eqv : equivalence rel)
        --     (cmp : ∀ x y, rel x y -> linked G x y)

        -- variables {V : Type} {G : simple_graph V} (C : chunks G)

        -- instance chunked_setoid (C : chunks G) : setoid V := ⟨C.rel,C.eqv⟩

        -- def adj (x y : V) := ∃ x' y', C.rel x x' ∧ C.rel y y' ∧ G.adj x' y'

        -- @[symm] lemma rel_symm (x y : V) : C.rel x y -> C.rel y x
        --     := by { apply C.eqv.2.1 }

        -- @[symm] lemma adj_symm (x y : V) : adj C x y -> adj C y x
        --     := by { rintros ⟨x',y',h1,h2,h3⟩, exact ⟨y',x',h2,h1,G.sym h3⟩ }

        -- lemma adj_lift1 {a₁ a₂ b₁ b₂ : V} {h₁ : C.rel b₁ a₁} {h₂ : C.rel b₂ a₂} : adj C a₁ a₂ -> adj C b₁ b₂
        --     := by { rintros ⟨x',y',h1,h2,h3⟩, exact ⟨x', y', ⟨(C.eqv).2.2 h₁ h1, (C.eqv).2.2 h₂ h2, h3⟩⟩ }

        -- lemma adj_lift : ∀ (a₁ a₂ b₁ b₂ : V), C.rel b₁ a₁ → C.rel b₂ a₂ → adj C a₁ a₂ = adj C b₁ b₂
        --     := by { intros a₁ a₂ b₁ b₂ h1 h2, apply iff_iff_eq.mp, split,
        --             { apply adj_lift1; assumption },
        --             { intro h, apply adj_lift1, symmetry, assumption, symmetry, assumption, assumption } }

        -- def contract C : simple_graph (quotient (chunked_setoid C)) :=
        -- {
        --     adj := quotient.lift₂ (adj G) (adj_lift G),
        --     sym := λ x y, quotient.induction_on₂ x y (adj_symm G)
        -- }

        -- def proj_llist : llist G -> llist (contract G) := llist.map (λ x, ⟦x⟧)

        -- lemma proj_head {l : llist G} : (proj_llist G l).head = ⟦l.head⟧
        --     := llist.head_map

        -- lemma proj_last {l : llist G} : (proj_llist G l).last = ⟦l.last⟧
        --     := llist.last_map

        -- lemma proj_adj {x y : G} : simple_graph.adj x y -> @simple_graph.adj (contract G) _ ⟦x⟧ ⟦y⟧
        --     := λ h, exists.intro x (exists.intro y ⟨quotient.eq.mp rfl,quotient.eq.mp rfl,h⟩)

        -- lemma proj_is_path {l : llist G} : llist.is_path simple_graph.adj l -> llist.is_path simple_graph.adj (proj_llist G l)
        --     := by { induction l,
        --         { intro, trivial },
        --         { intro h, rw [proj_llist,llist.map,llist.is_path,llist.head_map], exact ⟨proj_adj G h.1, l_ih h.2⟩ } }

        -- def proj_path {x y} (p : path G x y) : path (contract G) ⟦x⟧ ⟦y⟧
        --     := {
        --         l := proj_llist G p.l,
        --         hx := by { rw [proj_head,p.hx] },
        --         hy := by { rw [proj_last,p.hy], },
        --         adj := proj_is_path _ p.adj
        --     }

        -- lemma contract_connected {C : chunked G} (h : connected G) : connected (contract G)
        --     := by {
        --         intro xbar, obtain ⟨x,hx⟩ := quot.exists_rep xbar, subst hx,
        --         intro ybar, obtain ⟨y,hy⟩ := quot.exists_rep ybar, subst hy,
        --         have h' := h x y, induction h', refl,
        --         exact linked.tail _ h'_ih (proj_adj _ h'_ᾰ_1) }

        -- def is_minor (G G' : Type) [simple_graph G] [simple_graph G'] : Prop
        --     := ∃ C : chunked G', by exactI embeds_into G (contract G')
    end contraction
end simple_graph

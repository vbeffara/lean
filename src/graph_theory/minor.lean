import tactic 
import graph_theory.basic graph_theory.path
open function

namespace Graph
    variables (G G' : Type) [Graph G] [Graph G']

    structure embedding :=
        (f        : G -> G')
        (df       : Π e : edges G, spath G' (f e.x) (f e.y))
        --
        (inj      : injective f)
        (nop      : ∀ e, 0 < (df e).size)
        (sym      : ∀ e : edges G, df e.flip = (df e).rev)
        --
        (endpoint : ∀ {e x},    f x ∈ df e              -> x ∈ e)
        (disjoint : ∀ {e e' z},   z ∈ df e -> z ∈ df e' -> e.same e' ∨ ∃ x, z = f x)

    def embeds_into := nonempty (embedding G G')
end Graph

namespace Graph
    namespace embedding
        variables {G G' : Type} [Graph G] [Graph G'] (F : embedding G G') {x y z : G} 

        lemma endpoint_init {e : edges G} : F.f x ∈ (F.df e).l.init <-> x = e.x
            := by { split; intro h1, 
                { have h2 : F.f x ∈ F.df e, by { apply llist.mem_init_last.mpr, left, assumption },
                    have h3 := F.endpoint h2, cases h3, assumption,
                    have h5 := llist.nodup_mem_last (F.df e).simple, 
                    rw (F.df e).hy at h5, rw h3 at h1, cases h5 h1 },
                { subst h1, convert llist.mem_head_init (F.nop e), exact (F.df e).hx.symm } }

        lemma endpoint_tail {e : edges G} : F.f x ∈ (F.df e).l.tail <-> x = e.y
            := by { split; intro h1, 
                { have h2 : F.f x ∈ F.df e, by { apply llist.mem_head_tail.mpr, right, assumption },
                    have h3 := F.endpoint h2, cases h3, swap, assumption,
                    have h5 := llist.nodup_mem_head (F.df e).simple, 
                    rw (F.df e).hx at h5, rw h3 at h1, cases h5 h1 },
                { subst h1, convert llist.mem_last_tail (F.nop e), exact (F.df e).hy.symm } }

        def follow_llist : Π (l : llist G) (h : l.is_path Graph.adj), llist G'
            | (llist.pt v)     _ := llist.pt (F.f v)
            | (llist.cons v l) h := llist.concat (F.df ⟨h.1⟩) (follow_llist l h.2)

        lemma follow_nop {l h} (hz : 0 < llist.size l) : 0 < (follow_llist F l h).size
            := by { cases l, { cases hz }, 
                { rw [follow_llist,llist.concat_size], apply nat.lt_add_right, apply F.nop } }

        @[simp] lemma follow_head {l h} : (follow_llist F l h).head = F.f l.head
            := by { induction l with v v l hr; rw follow_llist, { refl },
                { rw [llist.head_concat], exact (F.df _).hx,
                    rw [llist.compat,hr], exact (F.df _).hy } }

        @[simp] lemma follow_last {l h} : (follow_llist F l h).last = F.f l.last
            := by { induction l with v v l hr; rw follow_llist, { refl },
                { rw llist.concat_last, exact hr } }

        lemma follow_path {l h} : llist.is_path Graph.adj (follow_llist F l h)
            := by { induction l with v v l hr; rw [follow_llist],
                { trivial },
                { apply (llist.is_path_concat Graph.adj _).mpr ⟨(F.df _).adj, hr⟩, 
                    rw [llist.compat,follow_head,(F.df _).hy] } }

        def follow (p : path G x y) : path G' (F.f x) (F.f y)
            := ⟨⟨follow_llist F p.l p.adj, 
                by { rw [follow_head,p.hx] }, 
                by { rw [follow_last,p.hy] }⟩, follow_path F⟩

        lemma follow_edges {z l h} (hz : 0 < llist.size l) :
                z ∈ follow_llist F l h <-> ∃ e ∈ path.edges_aux l h, z ∈ F.df e
            := by { cases l with w w l, cases hz, clear hz, revert w,
                induction l with v v l hr; intros,
                { rw [path.edges_aux,path.edges_aux,follow_llist,follow_llist,llist.concat_nil], 
                    simp only [exists_prop, exists_eq_left, list.mem_singleton],
                    trivial, exact (F.df _).hy },
                { rw [follow_llist,path.edges_aux,llist.mem_concat],
                    swap, rw [llist.compat,follow_head], exact (F.df _).hy,
                    split,
                    { intro h1, cases h1 with h1 h1,
                        { exact ⟨⟨h.1⟩, or.inl rfl, h1⟩ },
                        { obtain ⟨e,he1,he2⟩ := (hr _).mp h1, exact ⟨e,or.inr he1,he2⟩ } },
                    { rintros ⟨e,he1,he2⟩, cases he1 with he1 he1,
                        { subst he1, left, assumption },
                        { right, apply (hr _).mpr, exact ⟨e,he1,he2⟩ } } } }

        lemma follow_edges' {z} {p : path G x y} (hz : 0 < p.size) : z ∈ follow F p <-> ∃ e ∈ p.all_edges, z ∈ F.df e
            := follow_edges F hz

        lemma follow_simple {l h} (hs : llist.nodup l) : (follow_llist F l h).nodup
            := by { cases l with w w l, trivial, revert w, 
                induction l with v v l hr; intros,
                    { convert (F.df _).simple, exact llist.concat_nil (F.df _).hy },
                rw [follow_llist,llist.concat_nodup,follow_head], 
                    swap, { rw [llist.compat,follow_head], exact (F.df _).hy },
                refine ⟨(F.df _).simple, hr v hs.2, _⟩, rintros x ⟨h6,h7⟩, rw [llist.head],
                obtain ⟨e',h8,h9⟩ := (follow_edges F _).mp h7,
                    swap, { rw llist.size, apply nat.succ_pos },
                cases F.disjoint h6 h9 with H3 H3, 
                    { cases path.edges_simple h hs with _ _ h2 h1, cases h2 e' h8 H3 },
                    { obtain ⟨u,h11⟩ := H3, subst h11, congr,
                        cases F.endpoint h6 with h12 h12, swap, exact h12,
                        suffices : u ∈ (llist.cons v l), by { rw h12 at this, cases hs.1 this },
                        cases path.mem_edges_aux h8 with h13 h14,
                        cases F.endpoint h9 with h15 h15; rw h15; assumption } }

        lemma follow_append {v l h} (h') (h'' : Graph.adj (llist.last l) v) : 
                follow_llist F (llist.append v l) h = llist.concat (follow_llist F l h') (F.df ⟨h''⟩).l
            := by { induction l with w w l hr,
                { exact llist.concat_nil (F.df _).hy },
                { revert h, rw [llist.append], intro h,
                    rw [follow_llist,follow_llist,hr h'.2 h'',llist.concat_assoc], 
                    have h3 : llist.head (llist.append v l) = llist.head l := llist.head_append,
                    congr; exact h3 } }

        lemma follow_rev {l} (h h') : (follow_llist F l h).rev = follow_llist F l.rev h'
            := by { induction l with v v l hr, refl,
                rw [follow_llist,llist.rev_concat],
                    { replace hr := hr h.2 ((llist.is_path_rev Graph.adj Graph.sym).mpr h.2),
                        rw [hr], revert h', rw llist.rev, intro h', rw follow_append, 
                        congr,
                        let e : edges G := ⟨h.1⟩,
                        have h4 : (F.df e).l.rev = (F.df e.flip).l, by { rw F.sym _, refl },
                        convert h4; exact llist.last_rev, finish },
                    { rw [llist.compat,follow_head], exact (F.df _).hy } }

        @[simp] def sfollow (p : spath G x y) : spath G' (F.f x) (F.f y)
            := ⟨follow F p.to_path, follow_simple F p.simple⟩

        @[simp] lemma sfollow_rev (p : spath G x y) : sfollow F p.rev = (sfollow F p).rev
            := by { simp only [sfollow,follow,spath.rev,path.rev], rw follow_rev }
    end embedding

    namespace embedding
        variables {G G' G'' : Type} [Graph G] [Graph G'] [Graph G'']

        def comp (F : embedding G G') (F' : embedding G' G'') : embedding G G'' := {
            f := F'.f ∘ F.f,
            df := λ e, sfollow F' (F.df e),
            --
            inj := injective.comp F'.inj F.inj, 
            sym := λ e, (F.sym e).symm ▸ (sfollow_rev F' (F.df e)),
            nop := λ e, follow_nop F' (F.nop e),
            --
            endpoint := by { 
                intros e x h1, 
                apply F.endpoint,
                obtain ⟨e',h2,h3⟩ := (follow_edges _ (F.nop _)).mp h1,
                suffices : F.f x ∈ e', by { cases path.mem_edges_aux h2, cases this; rwa this },
                exact F'.endpoint h3
                },
            --
            disjoint := by {
                intros e1 e2 z h1 h2,
                obtain ⟨e'1,h3,h4⟩ := (follow_edges' F' (F.nop e1)).mp h1, clear h1,
                obtain ⟨e'2,h5,h6⟩ := (follow_edges' F' (F.nop e2)).mp h2, clear h2,
                cases F'.disjoint h4 h6 with h7 h7,
                { left, clear h4 h6,
                    cases path.mem_edges_aux' h3 with h3l h3r, clear h3,
                    cases path.mem_edges_aux' h5 with h5l h5r, clear h5,
                    cases h7; subst h7,
                    { cases F.disjoint (llist.mem_init h3l) (llist.mem_init h5l) with h10 h10, assumption,
                        cases F.disjoint (llist.mem_tail h3r) (llist.mem_tail h5r) with h11 h11, assumption,
                        obtain ⟨x,hx⟩ := h10, rw [hx,endpoint_init F] at h3l h5l, clear hx,
                        obtain ⟨y,hy⟩ := h11, rw [hy,endpoint_tail F] at h3r h5r, clear hy,
                        left, ext; cc },
                    { rw [edges.flip] at h5l, rw [edges.flip] at h5r,
                        cases F.disjoint (llist.mem_init h3l) (llist.mem_tail h5r) with h10 h10, assumption,
                        cases F.disjoint (llist.mem_tail h3r) (llist.mem_init h5l) with h11 h11, assumption,
                        obtain ⟨x,hx⟩ := h10, unfold edges.y at h5r, rw [hx] at h3l h5r, clear hx,
                        obtain ⟨y,hy⟩ := h11, unfold edges.x at h5l, rw [hy] at h5l h3r, clear hy,
                        rw endpoint_init F at h3l h5l, rw endpoint_tail F at h3r h5r,
                        right, ext; cc }
                },
                { obtain ⟨x,hx⟩ := h7, subst hx,
                    replace h3 : x ∈ F.df e1, { cases path.mem_edges h3, cases F'.endpoint h4; rw h; assumption },
                    replace h5 : x ∈ F.df e2, { cases path.mem_edges h5, cases F'.endpoint h6; rw h; assumption },
                    cases (F.disjoint h3 h5),
                    { exact or.inl h },
                    { obtain ⟨y,h⟩ := h, right, use y, rw h } }
                }
        }

        theorem trans : embeds_into G G' -> embeds_into G' G'' -> embeds_into G G''
            := by { intros F F', cases F, cases F', use comp F F' }
    end embedding

    namespace contraction
        class chunked (G : Type) extends Graph G :=
            (rel : G -> G -> Prop)
            (eqv : equivalence rel)
            (cmp : ∀ x y, rel x y -> Graph.linked G x y)

        variables (G : Type) [chunked G]

        instance chunked_setoid : setoid G := ⟨chunked.rel,chunked.eqv⟩

        def adj (x y : G) := ∃ x' y', x' ≈ x ∧ y' ≈ y ∧ @Graph.adj G _ x' y'

        lemma adj_symm (x y : G) : adj G x y -> adj G y x
            := by { rintros ⟨x',y',h1,h2,h3⟩, exact ⟨y',x',h2,h1,Graph.sym h3⟩ }

        lemma adj_lift1 {a₁ a₂ b₁ b₂ : G} {h₁ : a₁ ≈ b₁} {h₂ : a₂ ≈ b₂} : adj G a₁ a₂ -> adj G b₁ b₂
            := by { rintros ⟨x',y',h1,h2,h3⟩, exact ⟨x', y', ⟨(chunked.eqv).2.2 h1 h₁, (chunked.eqv).2.2 h2 h₂, h3⟩⟩ }

        lemma adj_lift : ∀ (a₁ a₂ b₁ b₂ : G), a₁ ≈ b₁ → a₂ ≈ b₂ → adj G a₁ a₂ = adj G b₁ b₂
            := by { intros, apply iff_iff_eq.mp, split; 
                    apply adj_lift1; assumption <|> { symmetry, assumption } }

        def contract := @quotient G (by apply_instance)

        instance contract_graph : Graph (contract G) :=
        {
            adj := quotient.lift₂ (adj G) (adj_lift G),
            sym := λ x y, quotient.induction_on₂ x y (adj_symm G)
        }

        def proj_llist : llist G -> llist (contract G) := llist.map (λ x, ⟦x⟧)

        lemma proj_head {l : llist G} : (proj_llist G l).head = ⟦l.head⟧ 
            := llist.head_map

        lemma proj_last {l : llist G} : (proj_llist G l).last = ⟦l.last⟧
            := llist.last_map

        lemma proj_adj {x y : G} : Graph.adj x y -> @Graph.adj (contract G) _ ⟦x⟧ ⟦y⟧ 
            := λ h, exists.intro x (exists.intro y ⟨quotient.eq.mp rfl,quotient.eq.mp rfl,h⟩)

        lemma proj_is_path {l : llist G} : llist.is_path Graph.adj l -> llist.is_path Graph.adj (proj_llist G l)
            := by { induction l, 
                { intro, trivial },
                { intro h, rw [proj_llist,llist.map,llist.is_path,llist.head_map], exact ⟨proj_adj G h.1, l_ih h.2⟩ } }

        def proj_path {x y} (p : path G x y) : path (contract G) ⟦x⟧ ⟦y⟧
            := {
                l := proj_llist G p.l,
                hx := by { rw [proj_head,p.hx] },
                hy := by { rw [proj_last,p.hy], },
                adj := proj_is_path _ p.adj
            }

        lemma contract_connected {C : chunked G} (h : connected G) : connected (contract G)
            := by {
                intro xbar, obtain ⟨x,hx⟩ := quot.exists_rep xbar, subst hx, 
                intro ybar, obtain ⟨y,hy⟩ := quot.exists_rep ybar, subst hy, 
                have h' := h x y, induction h', refl,
                exact linked.tail _ h'_ih (proj_adj _ h'_ᾰ_1) }

        def is_minor (G G' : Type) [Graph G] [Graph G'] : Prop 
            := ∃ C : chunked G', by exactI embeds_into G (contract G')
    end contraction
end Graph

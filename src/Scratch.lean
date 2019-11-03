import tactic
import graph
open function

infix `~~`:50 := λ {G : graph} (x y : G), G.adj x y

namespace graph section
    variables (G₁ G₂ : graph)
    def prod : graph := {
        V   := G₁ × G₂,
        adj := λ x y, (x.1 = y.1 ∧ x.2 ~~ y.2) ∨ (x.1 ~~ y.1 ∧ x.2 = y.2),
        sym := by { intros x y h, cases h, exact or.inl ⟨h.1.symm,G₂.sym h.2⟩, exact or.inr ⟨G₁.sym h.1,h.2.symm⟩ } }
end end graph


section embedding
    structure graph_embedding (G G' : graph) :=
        (f  : G -> G')
        (df : Π (e : Edge G), spath G' (f e.1.1) (f e.1.2))
        --
        (f_inj     : injective f)
        (sym       : ∀ e : Edge G, df e.flip = (df e).rev)
        (disjoint  : ∀ e e' z, llist'.inner (df e).1.1 z ∧ llist'.inner (df e').1.1 z -> e = e' ∨ e = e'.flip)
        (endpoints : ∀ e z, (∃ v, z = f v) ∧ (z ∈ (df e).l) <-> (z = f e.1.1) ∨ (z = f e.1.2))

    def embeds_into (G G' : graph) := nonempty (graph_embedding G G')

    variables {G G' G'' : graph} (F : graph_embedding G G')

    @[simp] def follow_aux : Π {x y} (l : llist G) (hx : x = l.first) (hy : l.last = y) (h : llist.is_path G.adj l), path G' (F.f x) (F.f y)
        | x y (llist.P v)   hx hy h := ⟨⟨llist.P (F.f v), congr_arg F.f hx, congr_arg F.f hy⟩, trivial⟩
        | x y (llist.L v l) hx hy h := path.concat (F.df ⟨⟨x,l.first⟩, hx.symm ▸ h.1⟩).1 (follow_aux l rfl hy h.2)

    @[simp] def follow {x y} (p : path G x y) : path G' (F.f x) (F.f y) := follow_aux F p.l p.hx p.hy p.adj

    lemma first_follow {x y} {l : llist G} {hx : x = l.first} {hy : l.last = y} {h : llist.is_path G.adj l}
        : (follow_aux F l hx hy h).l.first = F.f x
        := by { let pp := follow_aux F l hx hy h, exact pp.hx.symm }

    lemma mem_follow_via_edges {x y v} (p : path G x y) : v ∈ (follow F p).l
                                                    <->   (p.l = llist.P x ∧ v = F.f x) ∨ (∃ e ∈ path.edges p, v ∈ (F.df e).l) :=
    begin
        rcases p with ⟨⟨l,hx,hy⟩,adj⟩, revert x y, induction l with w w l hr; intros; subst hx; subst hy; simp [follow] at *,
        have tmp := hr (eq.refl l.first) (eq.refl l.last) adj.2, clear hr, simp at tmp, split; intro,
        { let e : Edge G := ⟨⟨w,l.first⟩,adj.1⟩, cases a, use e, simpa,
            cases tmp.mp a with inl inr,
                cases inl with _ h, subst h, use e, simp, convert llist.mem_last, exact (F.df e).hy.symm,
                cases inr with e' h', use e', simp * },
        { rcases a with ⟨e',⟨h1,h2⟩⟩, cases h1,
            left, subst h1, exact h2,
            right, apply tmp.mpr, right, use e', exact ⟨h1,h2⟩ }
    end

    lemma follow_simple_aux (l : llist G) (h : llist.is_path G.adj l) (hs : llist.simple l) :
            ∀ (x y) (hx : x = l.first) (hy : l.last = y), llist.simple (follow_aux F l hx hy h).1.1 :=
    begin
        induction l with v v l hr; intros; simp at *,
        have h1 := hr h.2 hs.2 l.first y rfl hy, simp at hx, subst hx, apply (llist.concat_simple _).mpr,
        split, exact (F.df ⟨⟨x,l.first⟩, h.1⟩).2,
        split, exact h1,
        rintros v1 ⟨h3,h4⟩, have h5 := (mem_follow_via_edges F ⟨⟨l,eq.refl l.first,hy⟩,h.2⟩).mp h4, simp * at h5,
        cases h5 with inl edge, { cases inl with h5 h6, cases l with v v l; rw h6; simp },
        rcases edge with ⟨e,h5,h6⟩,

        cases (classical.em (∃ v, v1 = F.f v)) with vertex novertex,
        { have h7 := (F.endpoints _ _).mp ⟨vertex,h6⟩, have h8 := (F.endpoints _ _).mp ⟨vertex,h3⟩,
            have hh := path.edges_vertices ⟨⟨llist.L x l,hx,hy⟩,h⟩,
            have hh1 := hh h5, have hh2 := hh ⟨⟨x,l.first⟩,h.1⟩ _,
            rw first_follow,
            cases h7; cases h8; have h9 := eq.trans h7.symm h8; have H := F.f_inj h9,
            { sorry },
            { sorry },
            { sorry },
            { sorry } },
        { have h7 : path.inner (F.df e).1 v1 := sorry, sorry }
    end

    def sfollow {x y} (p : spath G x y) : spath G' (F.f x) (F.f y) := ⟨follow F p.1, by { } ⟩

    def comp (F : embedding G G') (F' : embedding G' G'') : (embedding G G'') := {
        f := F'.f ∘ F.f,
        df := λ e, follow F' (F.df e),
        --
        f_inj := _,
        sym := _,
        disjoint := _,
        endpoints := _
    }

    @[simp] def follow_ {G G'} (F : embedding G G') (p : path_ G) : path G' (F.f p.1.first) (F.f p.1.last) := by {
        cases p with l h, induction l with v v l hr, refine ⟨⟨llist.P (F.f v),_⟩,_⟩; simp,
        exact path.concat (F.df ⟨⟨v,l.first⟩, h.1⟩).1 (hr h.2)
    }

    lemma follow_cons_ {G G' v l h} {F : embedding G G'} :
            follow_ F ⟨llist.L v l, h⟩ = path.concat (F.df ⟨⟨v,l.first⟩,h.1⟩).1 (follow_ F ⟨l,h.2⟩)
        := by { simp }

    @[simp] def follow {G G' x y} (F : embedding G G') (p : path G x y) : path G' (F.f x) (F.f y)
        := by { let pf := follow_ F p.1, refine ⟨pf.1,_⟩, simp [pf.2.1, pf.2.2, p.2.1, p.2.2] }

    lemma follow_simple_ {G G'} (F : embedding G G') (p : path_ G) : p.1.simple -> (follow_ F p).1.1.simple
    := begin
        rcases p with ⟨l,hl⟩, induction l with v v l hr, simp, intro h, simp at h hl,
        rw follow_cons_, simp only [path.concat,path_.concat], sorry
    end

    theorem embed_trans : transitive embeds_into :=
    begin
        intros G G' G'' F F', cases F, cases F', refine ⟨⟨_,_,_,_,_,_⟩⟩,
        /- f     -/ { exact F'.f ∘ F.f },
        /- df    -/ { intros, exact ⟨follow F' (F.df e).1, sorry⟩ },
        /- f_inj -/ { exact injective_comp F'.f_inj F.f_inj },
        sorry,
        sorry,
        sorry
    end
end embedding

section examples
    parameters (V V₁ V₂ : Type)

    @[simp] def complete_bipartite_adj : V₁⊕V₂ -> V₁⊕V₂ -> Prop
        | (sum.inl _) (sum.inr _) := true
        | (sum.inr _) (sum.inl _) := true
        | _ _ := false

    def complete_graph     : graph := ⟨V,     (λ x y, x ≠ y),         by { finish }⟩
    def empty_graph        : graph := ⟨V,     (λ _ _, false),         by { finish }⟩
    def complete_bip_graph : graph := ⟨V₁⊕V₂, complete_bipartite_adj, by { intros x y, cases x; cases y; simp }⟩

    def infinite_line_graph : graph := by {
        refine ⟨ℤ, (λ x y, y = x+1 ∨ y = x-1), _⟩,
        intros x y h, cases h; {rw h, ring, simp}
    }
end examples

def K5  := complete_graph (fin 5)
def K33 := complete_bip_graph (fin 3) (fin 3)
def Z2  := graph.prod infinite_line_graph infinite_line_graph

-- We want something like that but the notion of planarity is wrong
theorem wagner_kuratowski (G : graph) : embeds_into G Z2 ∨ embeds_into K5 G ∨ embeds_into K33 G := sorry

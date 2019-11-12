import tactic
import llist
open function

structure graph := (V : Type) (adj : V -> V -> Prop) (sym : symmetric adj)
instance graph_to_V : has_coe_to_sort graph := {S := _, coe := λ G, G.V}

namespace graph section
    structure hom  (G G' : graph) :=
        (f   : G -> G')
        (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

    structure iso (G G' : graph) extends hom G G' :=
        (bij : bijective f)
        (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))

    structure subgraph (G' : graph) :=
        (G   : graph)
        (f   : hom G G')
        (inj : injective f.f)
end end graph

def edge (G : graph) := { e : G×G // G.adj e.1 e.2 }

namespace edge section
    parameters {G : graph}

    def mem (v : G) (e : edge G) := v = e.1.1 ∨ v = e.1.2
    instance : has_mem G.V (edge G) := ⟨mem⟩

    @[extensionality] lemma eq {e e' : edge G} : e.1.1 = e'.1.1 -> e.1.2 = e'.1.2 -> e = e'
        := by { cases e, cases e', simp at *, ext }

    lemma mem.fst {e : edge G} : e.1.1 ∈ e
        := by { simp [(∈),mem] }

    def flip  (e : edge G)    : edge G := ⟨⟨_,_⟩, G.sym e.2⟩
    def same  (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    def nsame (e e' : edge G) : Prop   := ¬ same e e'
end end edge

structure path  (G : graph) (x y) extends llist' G x y := (adj : llist.is_path G.adj l)

namespace path section
    parameters {G : graph}
    variables {x y z : G}

    instance : has_coe (path G x y) (llist' G x y) := ⟨path.to_llist'⟩

    def mem (v : G) (p : path G x y) := v ∈ p.l
    instance has_mem : has_mem G (path G x y) := ⟨mem⟩

    @[simp] lemma mem_simp {z l h} : z ∈ (⟨l,h⟩ : path G x y) <-> z ∈ l.l
        := by { simp [(∈),mem] }

    def P (v : G) : path G v v := ⟨llist'.P v, trivial⟩

    def cons (v : G) (p : path G x y) (h : G.adj v x) : path G v y
        := ⟨llist'.cons v p.1, by { simp [llist'.cons,llist.is_path], exact ⟨h,p.2⟩ }⟩

    def linked     (x y : G)        : Prop := nonempty (path G x y)
    def connected                   : Prop := ∀ x y, linked x y
    def simple     (p : path G x y) : Prop := llist.nodup p.l
    def qsimple    (p : path G x y) : Prop := llist.qnodup p.l

    def rev (p : path G x y) : path G y x
        := ⟨⟨llist.rev p.l, by simp, by simp⟩, (llist.rev_is_path G.adj G.sym).mpr p.adj⟩

    def concat (p : path G x y) (p' : path G y z) : path G x z
        := ⟨llist'.concat p.to_llist' p'.to_llist',
            by { apply (llist.concat_path G.adj llist'.compat).mpr, exact ⟨p.adj,p'.adj⟩ }⟩

    def edges_aux : Π {l : llist G} (h : llist.is_path G.adj l), list (edge G)
        | (llist.P v)   _ := []
        | (llist.L v l) h := ⟨⟨v,l.head⟩,h.1⟩ :: edges_aux h.2

    def edges (p : path G x y) : list (edge G)
        := edges_aux p.adj

    lemma mem_edges_aux' {l} {h : llist.is_path G.adj l} {e : edge G} : e ∈ edges_aux h -> e.1.1 ∈ l.init ∧ e.1.2 ∈ l.tail
        := by { induction l with v v l hr; intros he,
            { cases he },
            { cases he with he he,
                { subst he, simp[llist.init,llist.tail] },
                { replace hr := hr he, exact ⟨or.inr hr.1, or.inr hr.2⟩ } } }

    lemma mem_edges_aux {l} {h : llist.is_path G.adj l} {e : edge G} : e ∈ edges_aux h -> e.1.1 ∈ l ∧ e.1.2 ∈ l
        := by { intro h1, have h2 := mem_edges_aux' h1, split, 
            { exact llist.mem_init_last.mpr (or.inl h2.1) },
            { exact llist.mem_head_tail.mpr (or.inr h2.2) } }

    lemma mem_edges {p : path G x y} {e : edge G} : e ∈ p.edges -> e.1.1 ∈ p.l ∧ e.1.2 ∈ p.l
        := mem_edges_aux

    lemma edges_simple {l} (h : llist.is_path G.adj l) (hs : llist.nodup l) : list.pairwise edge.nsame (edges_aux h)
        := by { induction l with v v l hr; rw edges_aux, exact list.pairwise.nil,
            apply list.pairwise.cons, 
            { intros e he, rw [edge.nsame, edge.same], push_neg, have h5 := mem_edges_aux he,
                split; intro h6; subst h6, exact hs.1 h5.1, exact hs.1 h5.2 },
            { exact hr h.2 hs.2 }
        }
end end path

structure  spath (G : graph) (x y) extends path G x y := ( simple : path.simple  to_path)

namespace spath section
    parameters {G : graph}
    variables {x y z : G}

    def mem (z) (p : spath G x y) := z ∈ to_path p
    instance : has_mem G.V (spath G x y) := ⟨mem⟩

    @[simp] lemma mem_simp {z p h} : z ∈ (⟨p,h⟩ : spath G x y) <-> z ∈ p
        := by { simp [(∈),mem] }

    instance : has_coe (spath G x y) (path G x y) := ⟨spath.to_path⟩

    def rev (p : spath G x y) : spath G y x
        := ⟨p.to_path.rev, llist.rev_nodup.mpr p.simple⟩

    lemma edges_simple {p : spath G x y} : list.pairwise edge.nsame p.to_path.edges
        := path.edges_simple _ p.simple
end end spath

structure graph_embedding (G G' : graph) :=
    (f        : G -> G')
    (df       : Π (e : edge G), spath G' (f e.1.1) (f e.1.2))
    --
    (inj      : injective f)
    (nop      : ∀ e, 0 < llist.size (df e).l)
    (sym      : ∀ e : edge G, df e.flip = (df e).rev)
    --
    (endpoint : ∀ {e x},    f x ∈ df e              -> x ∈ e)
    (disjoint : ∀ {e e' z},   z ∈ df e -> z ∈ df e' -> edge.same e e' ∨ ∃ x, z = f x)

def embeds_into (G G' : graph) := nonempty (graph_embedding G G')

namespace embedding section
    parameters {G G' G'' : graph} (F : graph_embedding G G')
    variables {x y z : G} 

    lemma endpoint_init {e : edge G} : F.f x ∈ llist.init (F.df e).l <-> x = e.1.1
        := by { split; intro h1, 
            { have h2 : F.f x ∈ F.df e, by { apply llist.mem_init_last.mpr, left, assumption },
                have h3 := F.endpoint h2, cases h3, assumption,
                have h4 : F.f x = (F.df e).l.last, by { convert (F.df e).hy.symm },
                have h5 := llist.nodup_mem_last (F.df e).simple, rw <-h4 at h5, contradiction },
            { subst h1, convert llist.mem_head_init (F.nop e), simp } }

    lemma endpoint_tail {e : edge G} : F.f x ∈ llist.tail (F.df e).l <-> x = e.1.2
        := by { split; intro h1, 
            { have h2 : F.f x ∈ F.df e, by { apply llist.mem_head_tail.mpr, right, assumption },
                have h3 := F.endpoint h2, cases h3, swap, assumption,
                have h4 : F.f x = (F.df e).l.head, by { convert (F.df e).hx },
                have h5 := llist.nodup_mem_head (F.df e).simple, rw <-h4 at h5, contradiction },
            { subst h1, convert llist.mem_last_tail (F.nop e), simp } }

    def follow_llist : Π (l : llist G) (h : llist.is_path G.adj l), llist G'
        | (llist.P v)   _ := llist.P (F.f v)
        | (llist.L v l) h := llist.concat (F.df ⟨(_,_),h.1⟩) (follow_llist l h.2)

    @[simp] lemma follow_head {l h} : (follow_llist l h).head = F.f l.head
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { let e : edge G := ⟨(_,_),h.1⟩,
                rw llist.concat_head, exact (F.df e).hx.symm,
                rw [llist.compat,hr], exact (F.df e).hy } }

    @[simp] lemma follow_last {l h} : (follow_llist l h).last = F.f l.last
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { rw llist.concat_last, exact hr } }

    lemma follow_path {l h} : llist.is_path G'.adj (follow_llist l h)
        := by { induction l with v v l hr; rw [follow_llist],
            { simp [llist.is_path] },
            { apply (llist.concat_path G'.adj _).mpr ⟨(F.df _).adj, hr⟩, simp } }

    def follow (p : path G x y) : path G' (F.f x) (F.f y)
        := ⟨⟨follow_llist p.l p.adj, by simp, by simp⟩, follow_path⟩

    @[simp] lemma follow_nil : follow (path.P x) = path.P (F.f x)
        := by { simp [follow,path.P,llist'.P,follow_llist] }

    lemma follow_edges {z l} (h) (hz : 0 < llist.size l) :
            z ∈ follow_llist l h <-> ∃ e ∈ path.edges_aux h, z ∈ F.df e
        := by { induction l with v v l hr,
            { cases hz },
            { clear hz, rw [llist.is_path] at h, replace hr := hr h.2,
                have compat : (F.df ⟨(_,_),h.1⟩).l.last = F.f l.head, by simp,
                rw [follow_llist,path.edges_aux,llist.mem_concat],
                swap, rw llist.compat, convert compat, rw follow_head, split,
                { intro h1, cases h1 with h1 h1,
                    { use ⟨(_,_),h.1⟩, simpa },
                    { cases l with w w l,
                        { rw [follow_llist] at h1, use ⟨(_,_),h.1⟩, simp, convert llist.mem_last, simpa },
                        { obtain ⟨e,⟨he1,he2⟩⟩ := (hr _).mp h1, use e, finish, rw llist.size, finish } } },
                { rintros ⟨e,he1,he2⟩, cases he1 with he1 he1,
                    { subst he1, left, assumption },
                    { cases l with w w l,
                        { cases he1 },
                        { right, apply (hr _).mpr, use e, use he1, exact he2, rw llist.size, finish } } } } }

    lemma follow_simple {l} (h) (hs : llist.nodup l) : (follow_llist l h).nodup
        := by {
            induction l with v v l hr, simp [follow_llist],
            let dfe : spath G' (F.f v) (F.f l.head) := F.df ⟨(v,l.head),h.1⟩,
            replace hr := hr h.2 hs.2,
            have h1 := path.edges_simple h hs, cases h1 with _ _ h2 h1,
            have h3 : llist.compat dfe.l (follow_llist F l h.2), by simp,
            have h4 := classical.em (llist.size l = 0), cases h4 with h4 h4,
                { cases l, swap, cases h4, rw [follow_llist,follow_llist,llist.concat_nil],
                exact dfe.simple, exact dfe.hy },
            replace h4 := zero_lt_iff_ne_zero.mpr h4,
            apply (llist.concat_nodup h3).mpr, refine ⟨dfe.simple, hr, _⟩,
            rintros x ⟨h6,h7⟩, obtain ⟨e',h8,h9⟩ := (follow_edges F h.2 h4).mp h7,
            cases F.disjoint h6 h9 with h h, cases h2 e' h8 h, cases h with u h11,
            subst h11, rw follow_head, apply congr_arg,
            have h12 := F.endpoint h6, cases h12, swap, exact h12,
            suffices : u ∈ l, by { rw h12 at this, cases hs.1 this },
            cases path.mem_edges_aux h8 with h13 h14,
            cases F.endpoint h9 with h15 h15; rw h15; assumption
        }

    lemma follow_append {v l} (h) : follow_llist (llist.append v l) h =
            let hh := (llist.append_is_path G.adj).mp h in
            llist.concat (follow_llist l hh.2) (F.df ⟨(_,_),hh.1⟩).l
        := by { simp, induction l with w w l hr,
            { simp [llist.append,follow_llist], apply llist.concat_nil, exact (F.df _).hy },
            { cases h with h1 h2, replace hr := hr h2,
                simp [follow_llist,llist.append,llist.concat_assoc], rw hr,
                have h3 : llist.head (llist.append v l) = llist.head l := llist.append_head,
                congr; simp } }

    lemma follow_rev {l} (h) : (follow_llist l h).rev
        = follow_llist l.rev ((llist.rev_is_path G.adj G.sym).mpr h)
        := by {
            induction l with v v l hr,
            { simp [follow_llist, llist.rev] },
            { cases h with h1 h2, replace hr := hr h2,
                simp [follow_llist,llist.rev], rw llist.rev_concat,
                { simp [hr,follow_append], apply congr_arg,
                    let e : edge G := ⟨(_,_),h1⟩,
                    have h3 := F.sym e,
                    have h4 : (F.df e.flip).l = (F.df e).l.rev, by { finish [spath.rev,path.rev] },
                    convert h4.symm; simp },
                { rw llist.compat, convert (F.df _).hy, rw follow_head } } }

    @[simp] def sfollow (p : spath G x y) : spath G' (F.f x) (F.f y)
        := ⟨follow p.to_path, follow_simple p.adj p.simple⟩

    @[simp] lemma sfollow_rev (p : spath G x y) : sfollow p.rev = (sfollow p).rev
        := by { simp [sfollow,follow,spath.rev,path.rev], apply (follow_rev F _).symm }
end end embedding

namespace embedding section
    parameters {G G' G'' : graph} 

    def comp (F : graph_embedding G G') (F' : graph_embedding G' G'') :
                                        (graph_embedding G G'') := {
        f := F'.f ∘ F.f,
        df := λ e, sfollow F' (F.df e),
        --
        inj := injective_comp F'.inj F.inj,
        --
        sym := by { intro e, rw F.sym e, apply sfollow_rev },
        --
        nop := by { intro e, have hz := F.nop e, 
            rcases (F.df e) with ⟨⟨⟨l,hx,hy⟩,hp⟩,hs⟩, simp, intro hz,
            cases l with v v l, cases hz, rw follow, simp, rw follow_llist, simp,
            have hz' := F'.nop ⟨(_,_),hp.1⟩, apply nat.lt_add_left, assumption },
        --
        endpoint := by { intros e x h1, simp [sfollow,follow] at h1,
            rw follow_edges at h1, swap, apply F.nop, rcases h1 with ⟨e',h2,h3⟩,
            have h4 := F'.endpoint h3, have h5 := path.mem_edges_aux h2,
            have h6 : F.f x ∈ F.df e, by { cases h5, cases h4; rw h4; assumption },
            exact F.endpoint h6 },
        --
        disjoint := by {
            intros e1 e2 z h1 h2, simp [sfollow,follow] at h1 h2,
            rw follow_edges at h1, swap, apply F.nop, obtain ⟨e'1,h3,h4⟩ := h1,
            rw follow_edges at h2, swap, apply F.nop, obtain ⟨e'2,h5,h6⟩ := h2,
            cases F'.disjoint h4 h6 with h7 h7,
            { left,
                cases path.mem_edges_aux' h3 with h3l h3r,
                cases path.mem_edges_aux' h5 with h5l h5r,
                cases h7; subst h7,
                { have h10 := F.disjoint (llist.mem_init h3l) (llist.mem_init h5l),
                    have h11 := F.disjoint (llist.mem_tail h3r) (llist.mem_tail h5r),
                    cases h10, assumption, cases h11, assumption, left,
                    obtain ⟨x,hx⟩ := h10, obtain ⟨y,hy⟩ := h11, simp only [hx,hy] at *,
                    rw endpoint_init F at h3l h5l, rw endpoint_tail F at h3r h5r,
                    ext; cc },
                { simp [edge.flip] at h5l h5r,
                    have h10 := F.disjoint (llist.mem_init h3l) (llist.mem_tail h5r),
                    have h11 := F.disjoint (llist.mem_tail h3r) (llist.mem_init h5l),
                    cases h10, assumption, cases h11, assumption, right,
                    obtain ⟨x,hx⟩ := h10, obtain ⟨y,hy⟩ := h11, simp only [hx,hy] at *,
                    rw endpoint_init F at h3l h5l, rw endpoint_tail F at h3r h5r,
                    ext; cc }
            },
            { obtain ⟨x,hx⟩ := h7, subst hx,
                have h8 : x ∈ F.df e1,
                by { cases path.mem_edges_aux h3, cases F'.endpoint h4; rw h; assumption },
                have h9 : x ∈ F.df e2,
                by { cases path.mem_edges_aux h5, cases F'.endpoint h6; rw h; assumption },
                cases (F.disjoint h8 h9),
                { exact or.inl h },
                { obtain ⟨y,h⟩ := h, right, use y, rw h } }
            }
    }

    theorem embed_trans : transitive embeds_into
        := by { rw transitive, intros G G' G'' F F', cases F, cases F', use comp F F' }
end end embedding

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

    @[simp] lemma fst {x y h} : (⟨(x,y),h⟩ : edge G).val.fst = x
        := by simp

    lemma mem.fst {e : edge G} : e.1.1 ∈ e
        := by { simp [(∈),mem] }

    def flip  (e : edge G)    : edge G := ⟨⟨_,_⟩, G.sym e.2⟩
    def same  (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    def nsame (e e' : edge G) : Prop   := ¬ same e e'

    lemma same_mem {e e'} : same e e' <-> ∀ x, x ∈ e <-> x ∈ e'
        := by { rw same, split, { finish [(∈),mem] },
            simp [(∈),mem], intro,
            have h1 := a e.1.1, have h2 := a e.1.2, have h3 := a e'.1.1, have h4 := a e'.1.2,
            clear a, simp at *, cases h1, { left, ext; finish }, { right, ext; finish } }

    def ends (e : edge G) : set G := {e.1.1, e.1.2}
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
    def qsimple    (p : path G x y) : Prop := x ∉ p.l.inside ∧ y ∉ p.l.inside ∧ p.l.inside.nodup

    def rev (p : path G x y) : path G y x
        := ⟨⟨llist.rev p.l, by simp, by simp⟩, (llist.rev_is_path G.adj G.sym).mpr p.adj⟩

    def concat (p : path G x y) (p' : path G y z) : path G x z
        := ⟨llist'.concat p.to_llist' p'.to_llist',
            by { apply (llist.concat_path G.adj llist'.compat).mpr, exact ⟨p.adj,p'.adj⟩ }⟩

    def edges_aux : Π (l : llist G) (h : llist.is_path G.adj l), list (edge G)
        | (llist.P v)   _ := []
        | (llist.L v l) h := ⟨⟨_,_⟩,h.1⟩ :: edges_aux l h.2

    def edges (p : path G x y) : list (edge G)
        := edges_aux p.l p.adj

    lemma mem_edges_aux {l h} {e : edge G} : e ∈ edges_aux l h -> e.1.1 ∈ l ∧ e.1.2 ∈ l
        := by { induction l with v v l hr; intro e; cases e with he he,
            { subst he, simp },
            { replace hr := hr he, exact ⟨or.inr hr.1, or.inr hr.2⟩ } }

    lemma mem_edges_aux' {l h} {e : edge G} : e ∈ edges_aux l h -> e.1.1 ∈ l.init ∧ e.1.2 ∈ l.tail
        := by { induction l with v v l hr; intros he,
            { cases he },
            { cases he with he he,
                { subst he, simp[llist.init,llist.tail] },
                { replace hr := hr he, exact ⟨or.inr hr.1, or.inr hr.2⟩ } } }

    lemma mem_edges {p : path G x y} {e : edge G} : e ∈ p.edges -> e.1.1 ∈ p.l ∧ e.1.2 ∈ p.l
        := mem_edges_aux

    lemma edges_simple {l} (h) (hs : llist.nodup l) : list.pairwise edge.nsame (edges_aux l h)
        := by { induction l with v v l hr; rw edges_aux, exact list.pairwise.nil,
            simp, cases hs with h1 h2, cases h with h3 h4, refine ⟨_, hr h4 h2⟩,
            intros e he, have h5 := mem_edges_aux he,
            rw [edge.nsame, edge.same], push_neg, split; intro h6; subst h6,
            exact h1 h5.1, exact h1 h5.2 }
end end path

structure  spath (G : graph) (x y) extends path G x y := ( simple : path.simple  to_path)
structure qspath (G : graph) (x y) extends path G x y := (qsimple : path.qsimple to_path)

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
    (df       : Π (e : edge G), spath G' (f e.1.1) (f e.1.2)) -- problem if e.1.1 = e.1.2
    --
    (inj      : injective f)
    (nop      : ∀ e, 0 < llist.size (df e).l)
    (sym      : ∀ e : edge G, df e.flip = (df e).rev)
    --
    (endpoint : ∀ {e x},    f x ∈ df e              -> x ∈ e)
    (disjoint : ∀ {e e' z},   z ∈ df e -> z ∈ df e' -> edge.same e e' ∨ ∃ x, z = f x)

def embeds_into (G G' : graph) := nonempty (graph_embedding G G')

section embedding
    variables {G G' G'' : graph} {x y z : G} (F : graph_embedding G G')

    lemma endpoint_init {e : edge G} : F.f x ∈ llist.init (F.df e).l -> x = e.1.1
        := by { intro h1, have h2 := F.endpoint (llist.mem_init h1), cases h2, assumption,
            have lem : ∀ l : llist G', l.nodup -> l.last ∉ l.init, by {
                intro l, induction l with v v l hr,
                { simp [llist.init] },
                { simp [llist.nodup,llist.last,llist.init], intros h1 h2, push_neg, split,
                    { intro h3, apply h1, rw <-h3, exact llist.mem_last },
                    { exact hr h2 } } },
            subst h2, exfalso, apply lem (F.df e), exact (F.df e).simple,
            convert h1, exact (F.df e).hy }

    lemma endpoint_tail {e : edge G} : F.f x ∈ llist.tail (F.df e).l -> x = e.1.2
        := by { intro h1, have h2 := F.endpoint (llist.mem_tail h1), cases h2, swap, assumption,
            have lem : ∀ l : llist G', l.nodup -> l.head ∉ l.tail, by {
                intro l, induction l with v v l hr,
                { simp [llist.tail] },
                { simp [llist.nodup,llist.tail], intros h1 h2, push_neg, split,
                    { intro h3, apply h1, rw h3, exact llist.mem_head },
                    { intro h3, exact h1 (llist.mem_tail h3) }}
            },
            subst h2, exfalso, apply lem (F.df e), exact (F.df e).simple,
            convert h1, exact (F.df e).hx.symm }

    def follow_llist : Π (l : llist G) (h : llist.is_path G.adj l), llist G'
        | (llist.P v)   _ := llist.P (F.f v)
        | (llist.L v l) h := llist.concat (F.df ⟨(_,_),h.1⟩) (follow_llist l h.2)

    lemma follow_P {l h} (hp : llist.size l = 0) : follow_llist F l h = llist.P (F.f l.head)
        := by { cases l, simp [follow_llist], rw llist.size at hp, contradiction}

    @[simp] lemma follow_head {l} (h) : (follow_llist F l h).head = F.f l.head
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { let e : edge G := ⟨(_,_),h.1⟩, replace hr := hr h.2,
                rw llist.concat_head, simp, exact (F.df e).hx.symm,
                simp [llist.compat], rw hr, exact (F.df e).hy } }

    @[simp] lemma follow_last {l} (h) : (follow_llist F l h).last = F.f l.last
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { rw llist.concat_last, exact hr h.2 } }

    lemma follow_path {l} (h) : llist.is_path G'.adj (follow_llist F l h)
        := by { induction l with v v l hr; rw [follow_llist],
            { simp [llist.is_path] },
            { apply (llist.concat_path G'.adj _).mpr ⟨(F.df _).adj, hr h.2⟩, simp } }

    def follow (p : path G x y) : path G' (F.f x) (F.f y)
        := ⟨⟨follow_llist F p.l p.adj, by simp, by simp⟩, follow_path F p.adj⟩

    @[simp] lemma follow_nil : follow F (path.P x) = path.P (F.f x)
        := by { simp [follow,path.P,llist'.P,follow_llist] }

    lemma follow_edges {z l} (h) (hz : 0 < llist.size l) :
            z ∈ follow_llist F l h <-> ∃ e ∈ path.edges_aux l h, z ∈ F.df e
        := by { induction l with v v l hr,
            { rw llist.size at hz, cases hz },
            { simp [llist.is_path] at h, replace hr := hr h.2, clear hz,
                have compat : (F.df ⟨(_,_),h.1⟩).l.last = F.f l.head, by simp,
                simp [follow_llist,path.edges_aux],
                rw llist.mem_concat, swap, rw llist.compat, convert compat, rw follow_head, split,
                { intro h1, cases h1 with h1 h1,
                    { use ⟨(_,_),h.1⟩, simpa },
                    { cases l with w w l,
                        { simp [follow_llist] at h1, use ⟨(_,_),h.1⟩, simp, convert llist.mem_last, simpa },
                        { rcases (hr _).mp h1 with ⟨e,⟨he1,he2⟩⟩, use e, finish, rw llist.size, finish } } },
                { rintros ⟨e,he1,he2⟩, cases he1 with he1 he1,
                    { subst he1, left, assumption },
                    { cases l with w w l,
                        { cases he1 },
                        { right, apply (hr _).mpr, use e, use he1, exact he2, rw llist.size, finish } } } } }

    lemma follow_simple {l} (h) (hs : llist.nodup l) : (follow_llist F l h).nodup
        := by {
            induction l with v v l hr; simp [follow_llist],
            let e : edge G := ⟨(_,_),h.1⟩,
            replace hr := hr h.2 hs.2,
            have h1 := path.edges_simple h hs, cases h1 with _ _ h2 h1,
            have h3 : llist.compat (F.df e).l (follow_llist F l h.2), by simp,
            have h4 := classical.em (llist.is_P l), cases h4 with h4 h4,
                { cases l,
                    { simp [follow_llist], rw llist.concat_nil, exact (F.df _).simple, convert h3 },
                    { rw llist.is_P at h4, contradiction } },
            have hh4 : 0 < llist.size l, by { cases l, simp [llist.is_P] at h4, cases h4,
                rw llist.size, exact nat.succ_pos' },
            apply (llist.concat_nodup h3).mpr, refine ⟨(F.df _).simple, hr, _⟩,
            rintros x ⟨h6,h7⟩, rcases (follow_edges F h.2 hh4).mp h7 with ⟨e',h8,h9⟩,
            have h10 : edge.nsame e e', by { exact h2 e' h8 },
            cases F.disjoint h6 h9 with h h, cases h10 h, cases h with u h11,
            subst h11, rw follow_head, apply congr_arg,
            have h12 := F.endpoint h6, simp [(∈),edge.mem] at h12, cases h12, swap, exact h12,
            suffices : u ∈ l, by { cases hs.1 (h12 ▸ this) },
            cases path.mem_edges_aux h8 with h13 h14,
            cases F.endpoint h9 with h15 h15; rw h15; assumption
        }

    lemma follow_append {v l} (h) : follow_llist F (llist.append v l) h =
            let hh := (llist.append_is_path G.adj).mp h in
            llist.concat (follow_llist F l hh.2) (F.df ⟨(_,_),hh.1⟩).l
        := by { simp, induction l with w w l hr,
            { simp [llist.append,follow_llist], apply llist.concat_nil, exact (F.df _).hy },
            { cases h with h1 h2, replace hr := hr h2,
                simp [follow_llist,llist.append,llist.concat_assoc], rw hr,
                have h3 : llist.head (llist.append v l) = llist.head l := llist.append_head,
                congr; simp } }

    lemma follow_rev {l} (h) : (follow_llist F l h).rev
        = follow_llist F l.rev ((llist.rev_is_path G.adj G.sym).mpr h)
        := by {
            induction l with v v l hr,
            { simp [follow_llist,llist.rev] },
            { cases h with h1 h2, replace hr := hr h2,
                simp [follow_llist,llist.rev], rw llist.rev_concat,
                { simp [hr,follow_append], apply congr_arg,
                    let e : edge G := ⟨(_,_),h1⟩,
                    have h3 := F.sym e,
                    have h4 : (F.df e.flip).l = (F.df e).l.rev, by { finish [spath.rev,path.rev] },
                    convert h4.symm; simp },
                { rw llist.compat, convert (F.df _).hy, rw follow_head } } }

    -- lemma follow_cons {v : G} {p : path G x y} {h : G.adj v x} :
    --         follow F (path.cons v p h) = path.concat (F.df ⟨(v,x),h⟩).1 (follow F p)
    --     := by { simp [path.cons,llist'.cons,follow], congr; simp }

    -- @[simp] lemma follow_concat {p : path G x y} {p' : path G y z} :
    --         follow F (path.concat p p') = path.concat (follow F p) (follow F p')
    --     := by { rcases p with ⟨⟨l,hx,hy⟩,hp⟩, revert x y, induction l with v v l hr; intros,
    --         { simp [path.concat,llist'.concat,llist.concat,follow,follow_aux],
                    -- ext, simp, convert rfl; subst hx; subst hy; simp },
    --         {
    --             simp [llist.is_path] at hp,
    --             have h1 := @path.concat_cons G l.head y z v ⟨⟨l,rfl,hy⟩,hp.2⟩ p' hp.1,
    --             simp [path.cons,llist'.cons] at h1, replace h1 := congr_arg (follow F) h1,
    --         }
    --     }

    @[simp] def sfollow (p : spath G x y) : spath G' (F.f x) (F.f y)
        := ⟨follow F p.to_path, follow_simple F p.adj p.simple⟩

    @[simp] lemma sfollow_rev (p : spath G x y) : sfollow F p.rev = (sfollow F p).rev
        := by { simp [sfollow,follow,spath.rev,path.rev], apply (follow_rev F _).symm }

    def comp (F : graph_embedding G G') (F' : graph_embedding G' G'') : (graph_embedding G G'') := {
        f := F'.f ∘ F.f,
        df := λ e, sfollow F' (F.df e),
        --
        inj := injective_comp F'.inj F.inj,
        sym := by { intro e, rw F.sym e, apply sfollow_rev },
        nop := by { intro e, have hz := F.nop e, rcases (F.df e) with ⟨⟨⟨l,hx,hy⟩,hp⟩,hs⟩, simp, intro hz,
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
            rw (follow_edges F' (F.df e1).adj (F.nop e1)) at h1, rcases h1 with ⟨e'1,h3,h4⟩,
            rw (follow_edges F' (F.df e2).adj (F.nop e2)) at h2, rcases h2 with ⟨e'2,h5,h6⟩,
            have h7 := F'.disjoint h4 h6, cases h7 with h7 h7,
            {
                cases path.mem_edges_aux' h3 with h3l h3r,
                cases path.mem_edges_aux' h5 with h5l h5r,
                cases h7,
                    { subst h7,
                        have h10 := F.disjoint (llist.mem_init h3l) (llist.mem_init h5l),
                        have h11 := F.disjoint (llist.mem_tail h3r) (llist.mem_tail h5r),
                        cases h10, left, assumption, cases h11, left, assumption,
                        cases h10 with x hx, cases h11 with y hy, simp [hx,hy] at *,
                        replace h3l := endpoint_init F h3l,
                        replace h5l := endpoint_init F h5l,
                        replace h3r := endpoint_tail F h3r,
                        replace h5r := endpoint_tail F h5r,
                        left, left, ext; finish },
                    { subst h7,
                        simp [edge.flip] at h5l h5r,
                        have h10 := F.disjoint (llist.mem_init h3l) (llist.mem_tail h5r),
                        have h11 := F.disjoint (llist.mem_tail h3r) (llist.mem_init h5l),
                        cases h10, left, assumption, cases h11, left, assumption,
                        cases h10 with x hx, cases h11 with y hy, simp [hx,hy] at *,
                        replace h3l := endpoint_init F h3l,
                        replace h5l := endpoint_init F h5l,
                        replace h3r := endpoint_tail F h3r,
                        replace h5r := endpoint_tail F h5r,
                        left, right, ext; finish }
            },
            { cases h7 with x hx, subst hx,
                have h8 : x ∈ F.df e1,
                    by { cases path.mem_edges_aux h3 with h3l h3r,
                    cases F'.endpoint h4; rw h; assumption },
                have h9 : x ∈ F.df e2,
                    by { cases path.mem_edges_aux h5 with h3l h3r,
                    cases F'.endpoint h6; rw h; assumption },
                cases (F.disjoint h8 h9),
                { exact or.inl h },
                { cases h with x1 h, right, use x1, rw h } }
            }
    }

    theorem embed_trans : transitive embeds_into
        := by { rw transitive, intros G G' G'' F F', cases F, cases F', use comp F F' }
end embedding

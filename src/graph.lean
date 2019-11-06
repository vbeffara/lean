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
    def flip  {G} (e : edge G)    : edge G := ⟨⟨_,_⟩, G.sym e.2⟩
    def same  {G} (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    def nsame {G} (e e' : edge G) : Prop   := ¬ same e e'
end end edge

structure path  (G : graph) (x y) extends llist' G x y := (adj : llist.is_path G.adj l)

namespace path section
    parameters {G : graph}
    variables {x y z : G}

    instance : has_coe (path G x y) (llist' G x y) := ⟨path.to_llist'⟩

    def mem (v : G) (p : path G x y) := llist.mem v p.l
    instance has_mem : has_mem G (path G x y) := ⟨mem⟩

    def P (v : G) : path G v v := ⟨llist'.P v, trivial⟩

    def cons (v : G) (p : path G x y) (h : G.adj v x) : path G v y
        := ⟨llist'.cons v p.1, by { simp [llist'.cons,llist.is_path], exact ⟨h,p.2⟩ }⟩

    def linked     (x y : G)        : Prop := nonempty (path G x y)
    def connected                   : Prop := ∀ x y, linked x y
    def simple     (p : path G x y) : Prop := llist.nodup p.l

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

    lemma mem_edges {p : path G x y} {e : edge G} : e ∈ p.edges -> e.1.1 ∈ p.l ∧ e.1.2 ∈ p.l
        := mem_edges_aux

    lemma edges_simple {l} (h) (hs : llist.nodup l) : list.pairwise edge.nsame (edges_aux l h)
        := by { induction l with v v l hr; rw edges_aux, exact list.pairwise.nil,
            simp, cases hs with h1 h2, cases h with h3 h4, refine ⟨_, hr h4 h2⟩,
            intros e he, have h5 := mem_edges_aux he,
            rw [edge.nsame, edge.same], push_neg, split; intro h6; subst h6,
            exact h1 h5.1, exact h1 h5.2 }
end end path

structure spath (G : graph) (x y) extends path   G x y := (simple : path.simple to_path)

namespace spath section
    parameters {G : graph}
    variables {x y z : G}

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
    (sym      : ∀ e : edge G, (df e.flip) = (df e).rev)
    --
    (endpoint : ∀ e x, f x ∈ (df e).l -> x = e.1.1 ∨ x = e.1.2)
    (disjoint : ∀ e e' z, z ∈ (df e).l -> z ∈ (df e').l -> edge.same e e' ∨ ∃ x, z = f x)
    (inside   : ∀ e x, f x ∉ (df e).l.inside)

def embeds_into (G G' : graph) := nonempty (graph_embedding G G')

section embedding
    variables {G G' G'' : graph} {x y z : G} (F : graph_embedding G G')

    def follow_llist : Π (l : llist G) (h : llist.is_path G.adj l), llist G'
        | (llist.P v)   _ := llist.P (F.f v)
        | (llist.L v l) h := llist.concat (F.df ⟨(_,_),h.1⟩) (follow_llist l h.2)

    @[simp] lemma follow_head {l} (h) : llist.head (follow_llist F l h) = F.f l.head
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { let e : edge G := ⟨(_,_),h.1⟩, replace hr := hr h.2,
                rw llist.concat_head, simp, exact (F.df e).hx.symm,
                simp [llist.compat], rw hr, exact (F.df e).hy } }

    @[simp] lemma follow_last {l} (h) : llist.last (follow_llist F l h) = F.f l.last
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

    lemma follow_edges {z l} (h) (hz : l ≠ llist.P l.head) :
            z ∈ follow_llist F l h <-> ∃ e ∈ path.edges_aux l h, z ∈ (F.df e).l
        := by { induction l with v v l hr,
            { simp at hz, contradiction },
            { simp [llist.is_path] at h, replace hr := hr h.2, clear hz,
                have compat : (F.df ⟨(_,_),h.1⟩).l.last = F.f l.head, by simp,
                simp [follow_llist,path.edges_aux],
                rw llist.mem_concat, swap, rw llist.compat, convert compat, rw follow_head, split,
                { intro h1, cases h1 with h1 h1,
                    { use ⟨(_,_),h.1⟩, simpa },
                    { cases l with w w l,
                        { simp [follow_llist] at h1, use ⟨(_,_),h.1⟩, simp, convert llist.mem_last, simpa },
                        { rcases (hr _).mp h1 with ⟨e,⟨he1,he2⟩⟩, use e, finish, simp } } },
                { rintros ⟨e,he1,he2⟩, cases he1 with he1 he1,
                    { subst he1, left, assumption },
                    { cases l with w w l,
                        { cases he1 },
                        { right, apply (hr _).mpr, use e, use he1, exact he2, simp } } } } }

    lemma follow_simple {l} (h) (hs : llist.nodup l) : llist.nodup (follow_llist F l h)
        := by {
            induction l with v v l hr; simp [follow_llist],
            let e : edge G := ⟨(_,_),h.1⟩,
            replace hr := hr h.2 hs.2,
            have h1 := path.edges_simple h hs, cases h1 with _ _ h2 h1,
            have h3 : llist.compat (F.df e).l (follow_llist F l h.2), by simp,
            have h4 := classical.em (l = llist.P l.head), cases h4 with h4 h4,
                { conv {congr,congr,skip,congr,skip,rw h4}, simp [follow_llist],
                rw llist.concat_nil, exact (F.df _).simple, convert h3, simp },
            apply (llist.concat_nodup h3).mpr, refine ⟨(F.df _).simple, hr, _⟩,
            rintros x ⟨h6,h7⟩, rcases (follow_edges F h.2 h4).mp h7 with ⟨e',h8,h9⟩,
            have h10 : edge.nsame e e', by { exact h2 e' h8 },
            cases F.disjoint e e' x h6 h9 with h h, cases h10 h, cases h with u h11,
            subst h11, rw follow_head, apply congr_arg,
            have h12 := F.endpoint e u h6, simp at h12, cases h12, swap, exact h12,
            suffices : u ∈ l, by { cases hs.1 (h12 ▸ this) },
            cases path.mem_edges_aux h8 with h13 h14,
            cases F.endpoint e' u h9 with h15 h15; rw h15; assumption
        }

    lemma follow_append {v l} (h) : follow_llist F (llist.append v l) h =
            let hh := (llist.append_is_path G.adj).mp h in
            llist.concat (follow_llist F l hh.2) (F.df ⟨(_,_),hh.1⟩).l
        := by { simp, sorry }

    lemma follow_rev {l} (h) : llist.rev (follow_llist F l h) = follow_llist F l.rev ((llist.rev_is_path G.adj G.sym).mpr h)
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
        --
        endpoint := sorry,
        disjoint := sorry,
        inside := sorry
    }

    theorem embed_trans : transitive embeds_into
        := by { rw transitive, intros G G' G'' F F', cases F, cases F', use comp F F' }
end embedding

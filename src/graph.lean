import tactic
import llist
open function

structure graph := (V : Type) (adj : V -> V -> Prop) (sym : symmetric adj)
instance graph_to_V : has_coe_to_sort graph := {S := _, coe := λ G, G.V}

def edge (G : graph) := { e : G×G // G.adj e.1 e.2 }

namespace graph section
    structure hom  (G G' : graph) := (f : G -> G') (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

    structure iso (G G' : graph) extends hom G G' := (bij : bijective f) (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))

    structure subgraph (G' : graph) := (G : graph) (f : hom G G') (inj : injective f.f)
end end graph

namespace edge section
    @[simp] def flip  {G} (e : edge G)    : edge G := ⟨⟨_,_⟩, G.sym e.2⟩
    def same  {G} (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    @[simp] def nsame {G} (e e' : edge G) : Prop   := ¬ same e e'
end end edge

structure path  (G : graph) (x y) extends llist' G x y := (adj : llist.is_path G.adj l)

namespace path section
    parameters {G : graph}
    variables {x y z : G}

    lemma eq {p p' : path G x y} : p.to_llist' = p'.to_llist' -> p = p'
        := by { cases p, cases p', simp }

    def mem (v : G) (p : path G x y) := llist.mem v p.l
    instance has_mem : has_mem G (path G x y) := ⟨mem⟩

    def cons (v : G) (p : path G x y) (h : G.adj v x) : path G v y
        := ⟨llist'.cons v p.1, by { simp [llist'.cons,llist.is_path], exact ⟨h,p.2⟩ }⟩

    @[simp] def linked     (x y : G)        : Prop := nonempty (path G x y)
    @[simp] def connected                   : Prop := ∀ x y, linked x y
    def simple     (p : path G x y) : Prop := llist.nodup p.l

    @[simp] def rev (p : path G x y) : path G y x
        := { l := llist.rev p.l, hx := by simp, hy := by simp, adj := (llist.rev_is_path G.adj G.sym).mpr p.adj }

    @[simp] def concat (p : path G x y) (p' : path G y z) : path G x z
        := { to_llist' := llist'.concat p.to_llist' p'.to_llist',
            adj := by { apply (llist.concat_path G.adj llist'.compat).mpr, exact ⟨p.adj,p'.adj⟩ } }

    @[simp] def edges_aux : Π (l : llist G) (h : llist.is_path G.adj l), list (edge G)
        | (llist.P v)   _ := []
        | (llist.L v l) h := ⟨⟨_,_⟩,h.1⟩ :: edges_aux l h.2

    def edges (p : path G x y) : list (edge G) := edges_aux p.l p.adj

    lemma mem_edges {p : path G x y} {e : edge G} : e ∈ p.edges -> e.1.1 ∈ p.l ∧ e.1.2 ∈ p.l
        := by {
            rcases p with ⟨⟨l,hx,hy⟩,ha⟩, revert x y, induction l with v v l hr; intros; simp at *; cases a,
            { subst a, exact ⟨or.inl rfl, or.inr llist.mem_head⟩ },
            { have h1 := hr rfl hy ha.2 a, exact ⟨or.inr h1.1, or.inr h1.2⟩ }
        }
end end path

structure spath (G : graph) (x y) extends path   G x y := (simple : path.simple to_path)

namespace spath section
    parameters {G : graph}
    variables {x y z : G}

    lemma eq {p p' : spath G x y} : p.to_path = p'.to_path -> p = p'
        := by { cases p, cases p', simp }

    @[simp] def rev (p : spath G x y) : spath G y x
        := { to_path := path.rev p.to_path, simple := llist.rev_nodup.mpr p.simple }

    lemma edges_simple {p : spath G x y} : list.pairwise edge.nsame p.to_path.edges
        := by {
            rcases p with ⟨⟨⟨l,hx,hy⟩,ha⟩,hs⟩, revert x y, induction l with v v l hr; intros; simp at *,
            exact list.pairwise.nil, simp [path.edges], split,
            { intros e he, have h2 : e.1.1 ∈ l ∧ e.1.2 ∈ l := @path.mem_edges G _ _ ⟨⟨l,rfl,hy⟩,ha.2⟩ e he,
                rw edge.same, push_neg, split; intro h3; rw h3 at h2; simp at h2; apply hs.1; exact h2 },
            { have h1 := hr rfl hy ha.2 hs.2, exact h1 }
        }
end end spath

section embedding
    structure graph_embedding (G G' : graph) :=
        (f        : G -> G')
        (df       : Π (e : edge G), spath G' (f e.1.1) (f e.1.2))
        --
        (inj      : injective f)
        (sym      : ∀ e : edge G, df e.flip = (df e).rev)
        --
        -- (endpoint : ∀ e z, z ∈ (df e).l ∧ (∃ x, z = f x) -> z = (df e).l.head ∨ z = (df e).l.last)
        (endpoint : ∀ e x, f x ∈ (df e).l -> x = e.1.1 ∨ x = e.1.2)
        (disjoint : ∀ e e' z, z ∈ (df e).l ∧ z ∈ (df e').l -> edge.same e e' ∨ ∃ x, z = f x)
        (inside   : ∀ e x, f x ∉ llist.inside (df e).l)

    def embeds_into (G G' : graph) := nonempty (graph_embedding G G')

    variables {G G' G'' : graph} {x y z : G} (F : graph_embedding G G')

    @[simp] def follow_aux : Π {x y} (l : llist G) (hx : x = l.head) (hy : l.last = y) (h : llist.is_path G.adj l), path G' (F.f x) (F.f y)
        | x y (llist.P v)             hx hy h := ⟨⟨llist.P (F.f v), congr_arg F.f hx, congr_arg F.f hy⟩, trivial⟩
        | x y (llist.L v l)           hx hy h := path.concat (F.df ⟨⟨x,l.head⟩, hx.symm ▸ h.1⟩).1 (follow_aux l rfl hy h.2)

    def follow (p : path G x y) : path G' (F.f x) (F.f y) := follow_aux F p.l p.hx p.hy p.adj

    @[simp] lemma follow_nil : follow F ⟨⟨llist.P x, rfl, rfl⟩, trivial⟩ = ⟨⟨llist.P (F.f x), rfl, rfl⟩, trivial⟩
        := rfl

    lemma follow_cons {v : G} {p : path G x y} {h : G.adj v x} : follow F (path.cons v p h) = path.concat (F.df ⟨(v,x),h⟩).1 (follow F p)
        := by { simp [path.cons,llist'.cons,follow], congr; simp }

    @[simp] lemma follow_concat (p : path G x y) (p' : path G y z) : follow F (path.concat p p') = path.concat (follow F p) (follow F p')
        := by { sorry }

    lemma follow_edges {z} {p : path G x y} {hz : p.l ≠ llist.P y} : z ∈ follow F p <-> ∃ e ∈ path.edges p, z ∈ (F.df e).l
        := by {
            rcases p with ⟨⟨l,hx,hy⟩,hp⟩, revert x y z, induction l with v v l hr; intros; simp at *,
            { finish },
            { cases l with w w l, { simp [*,path.edges], subst hx, simp [follow,llist'.concat], finish },
                have h1 := @hr w y z rfl hy hp.2 (by {simp}), clear hr, split,
                { rintros h2, have h3 := (llist.mem_concat llist'.compat).mp h2, cases h3,
                    { use ⟨⟨_,_⟩,hp.1⟩, split, left, refl, subst hx, exact h3 },
                    { cases h1, clear h1_mpr, have h4 := h1_mp h3,
                        { rcases h4 with ⟨e,h5,h6⟩, exact ⟨e, or.inr h5, h6⟩ } } },
                { rintros h2, apply (llist.mem_concat llist'.compat).mpr,
                    { rcases h2 with ⟨e,h3,h4⟩, cases h3,
                        { subst h3, subst hx, exact or.inl h4 },
                        { exact or.inr (h1.mpr ⟨e,h3,h4⟩) }
                    }
                }
            }
        }

    lemma follow_simple {p : spath G x y} : path.simple (follow F p.to_path)
        := by {
            let sp0 := p,
            rcases p with ⟨⟨⟨l,hx,hy⟩,h⟩,hs⟩, revert x y h hs, induction l with v v l hr; intros; simp at *,

            let p0  : path G x y      := sp0.to_path,
            let es  : list (edge G)   := path.edges p0,
            let e   : edge G          := ⟨(v,l.head), h.1⟩,
            let p   : path G l.head y := ⟨⟨l,rfl,hy⟩,h.2⟩,
            let p₁  : spath G' _ _    := F.df e,

            rw llist.head at hx, subst hx,
            rw llist.last at hy, subst hy,
            cases l with w w l, { simp [follow, follow_aux, path.concat, llist'.concat], exact p₁.simple },

            have step1 : path.simple (follow F p),                      by { exact hr rfl hy h.2 hs.2 }, clear hr,
            have step2 : list.pairwise edge.nsame es,                   by { exact spath.edges_simple },
            suffices   : llist.nodup (path.concat p₁.1 (follow F p)).l, by { convert this },
            apply (llist.concat_nodup llist'.compat).mpr, simp,
            refine ⟨p₁.simple, step1, _⟩, rintros z h1 h2,
            have step3 : ∃ e' ∈ p.edges, z ∈ (F.df e').l,               by { apply (follow_edges F).mp h2, simp },
            rcases step3 with ⟨e',h3,h4⟩,
            have step4 : ¬ edge.same e e',                              by { cases step2, exact step2_a_1 e' h3 },
            have step5 : ∃ x₀ : G, z = F.f x₀,                          by { cases F.disjoint e e' z ⟨h1,h4⟩ with h h,
                                                                            exact absurd h step4, exact h },
            cases step5 with x₀ zfx, subst zfx, apply congr_arg,
            have h5 := F.endpoint e x₀ h1, simp at h5,
            cases h5, swap, exact h5,
            suffices : x₀ ∈ llist.L w l,                                by { cases hs, subst h5, contradiction },
            have h6 := F.endpoint e' x₀ h4,
            have h7 := path.mem_edges h3,
            cases h6 with h6 h6, { rw h6, exact h7.1 }, { rw h6, exact h7.2 }
        }

    @[simp] def sfollow (p : spath G x y) : spath G' (F.f x) (F.f y) := ⟨follow F p.to_path, follow_simple F⟩

    @[simp] lemma sfollow_rev (p : spath G x y) : sfollow F p.rev = (sfollow F p).rev
        := by {
            sorry
        }

    def comp (F : graph_embedding G G') (F' : graph_embedding G' G'') : (graph_embedding G G'') := {
        f := F'.f ∘ F.f,
        df := λ e, sfollow F' (F.df e),
        --
        inj := injective_comp F'.inj F.inj,
        sym := sorry,
        --
        endpoint := sorry,
        disjoint := sorry,
        inside := sorry
    }

    theorem embed_trans : transitive embeds_into := sorry
end embedding

import tactic llist
import group_theory.subgroup
open function
set_option trace.check true

structure digraph := 
    (V : Type) 
    (adj : V -> V -> Prop) 
    (sym : symmetric adj)

instance : has_coe_to_sort digraph := {S := _, coe := λ G, G.V}

namespace digraph section
    structure hom  (G G' : digraph) :=
        (f   : G -> G')
        (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

    structure iso (G G' : digraph) extends hom G G' :=
        (bij : bijective f)
        (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))
end end digraph

def isomorphic (G G' : digraph) := inhabited (digraph.iso G G')

@[ext] structure edge (G : digraph) := {x y : G} (h : G.adj x y)

namespace edge section
    parameters {G : digraph}

    def mem (v : G) (e : edge G) := v = e.x ∨ v = e.y
    instance : has_mem G.V (edge G) := ⟨mem⟩

    def flip  (e : edge G)    : edge G := ⟨G.sym e.h⟩
    def same  (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    def nsame (e e' : edge G) : Prop   := ¬ same e e'
end end edge

structure path  (G : digraph) (x y) extends llist' G x y := (adj : llist.is_path G.adj l)

namespace path section
    parameters {G : digraph}
    variables {x y z : G}

    instance : has_coe (path G x y) (llist' G x y) := ⟨path.to_llist'⟩

    def mem (v : G) (p : path G x y) := v ∈ p.l
    instance : has_mem G (path G x y) := ⟨mem⟩

    def linked     (x y : G)        : Prop := nonempty (path G x y)
    def simple     (p : path G x y) : Prop := llist.nodup p.l
    def qsimple    (p : path G x y) : Prop := llist.qnodup p.l
    def size       (p : path G x y) : nat  := llist.size p.l

    def rev (p : path G x y) : path G y x
        := ⟨⟨llist.rev p.l, by { rw [llist.rev_head,p.hy] }, by { rw [llist.rev_last,p.hx] }⟩, 
            (llist.rev_is_path G.adj G.sym).mpr p.adj⟩

    def concat (p : path G x y) (p' : path G y z) : path G x z
        := ⟨llist'.concat p.to_llist' p'.to_llist', 
            (llist.concat_path G.adj llist'.compat).mpr ⟨p.adj,p'.adj⟩⟩

    @[refl] lemma linked_refl {x : G} : linked x x
        := by { use ⟨⟨llist.P x, rfl, rfl⟩, trivial⟩ }

    @[symm] lemma linked.symm {x y : G} : linked x y -> linked y x
        := by { intro h, cases h, use h.rev }

    @[trans] lemma linked_trans {x y z : G} : linked x y -> linked y z -> linked x z
        := by { intros h1 h2, cases h1, cases h2, use concat h1 h2 }

    lemma linked_equiv : equivalence linked
        := by { exact ⟨@linked_refl _, @linked.symm _, @linked_trans _⟩ }

    def edges_aux : Π (l : llist G) (h : llist.is_path G.adj l), list (edge G)
        | (llist.P v)   _ := []
        | (llist.L v l) h := ⟨h.1⟩ :: edges_aux l h.2

    def edges (p : path G x y) : list (edge G)
        := edges_aux p.l p.adj

    lemma mem_edges_aux' {l h} {e : edge G} : e ∈ edges_aux l h -> e.x ∈ l.init ∧ e.y ∈ l.tail
        := by { induction l with v v l hr; intros he; cases he with he he,
            { subst he, split; left; refl },
            { cases hr he, split; right; assumption } }

    lemma mem_edges_aux {l h} {e : edge G} : e ∈ edges_aux l h -> e.x ∈ l ∧ e.y ∈ l
        := by { intro h1, cases mem_edges_aux' h1 with h2 h3, split, 
            { exact llist.mem_init_last.mpr (or.inl h2) },
            { exact llist.mem_head_tail.mpr (or.inr h3) } }

    lemma mem_edges {p : path G x y} {e : edge G} : e ∈ p.edges -> e.x ∈ p ∧ e.y ∈ p
        := mem_edges_aux

    lemma edges_simple {l} (h) (hs : llist.nodup l) : list.pairwise edge.nsame (edges_aux l h)
        := by { induction l with v v l hr, { exact list.pairwise.nil },
            { apply list.pairwise.cons, 
            { intros e he, rw [edge.nsame, edge.same], push_neg, have h5 := mem_edges_aux he,
                split; intro h6; subst h6, exact hs.1 h5.1, exact hs.1 h5.2 },
            { exact hr h.2 hs.2 } } }
end end path

def connected (G : digraph) : Prop := ∀ x y, @path.linked G x y

@[ext] structure  spath (G : digraph) (x y) extends path G x y := ( simple : path.simple  to_path)

namespace spath section
    parameters {G : digraph}
    variables {x y z : G}

    def mem (z) (p : spath G x y) := z ∈ to_path p
    instance : has_mem G.V (spath G x y) := ⟨mem⟩

    def size       (p : spath G x y) : nat  := p.to_path.size

    instance : has_coe (spath G x y) (path G x y) := ⟨spath.to_path⟩

    def rev (p : spath G x y) : spath G y x
        := ⟨p.to_path.rev, llist.rev_nodup.mpr p.simple⟩

    lemma edges_simple {p : spath G x y} : list.pairwise edge.nsame p.to_path.edges
        := path.edges_simple _ p.simple
end end spath

structure graph_embedding (G G' : digraph) :=
    (f        : G -> G')
    (df       : Π e : edge G, spath G' (f e.x) (f e.y))
    --
    (inj      : injective f)
    (nop      : ∀ e, 0 < (df e).size)
    (sym      : ∀ e : edge G, df e.flip = (df e).rev)
    --
    (endpoint : ∀ {e x},    f x ∈ df e              -> x ∈ e)
    (disjoint : ∀ {e e' z},   z ∈ df e -> z ∈ df e' -> edge.same e e' ∨ ∃ x, z = f x)

def embeds_into (G G' : digraph) := nonempty (graph_embedding G G')

namespace embedding section
    parameters {G G' G'' : digraph} (F : graph_embedding G G')
    variables {x y z : G} 

    lemma endpoint_init {e : edge G} : F.f x ∈ llist.init (F.df e).l <-> x = e.x
        := by { split; intro h1, 
            { have h2 : F.f x ∈ F.df e, by { apply llist.mem_init_last.mpr, left, assumption },
                have h3 := F.endpoint h2, cases h3, assumption,
                have h5 := llist.nodup_mem_last (F.df e).simple, 
                rw (F.df e).hy at h5, rw h3 at h1, cases h5 h1 },
            { subst h1, convert llist.mem_head_init (F.nop e), exact (F.df e).hx.symm } }

    lemma endpoint_tail {e : edge G} : F.f x ∈ llist.tail (F.df e).l <-> x = e.y
        := by { split; intro h1, 
            { have h2 : F.f x ∈ F.df e, by { apply llist.mem_head_tail.mpr, right, assumption },
                have h3 := F.endpoint h2, cases h3, swap, assumption,
                have h5 := llist.nodup_mem_head (F.df e).simple, 
                rw (F.df e).hx at h5, rw h3 at h1, cases h5 h1 },
            { subst h1, convert llist.mem_last_tail (F.nop e), exact (F.df e).hy.symm } }

    def follow_llist : Π (l : llist G) (h : llist.is_path G.adj l), llist G'
        | (llist.P v)   _ := llist.P (F.f v)
        | (llist.L v l) h := llist.concat (F.df ⟨h.1⟩) (follow_llist l h.2)

    lemma follow_nop {l h} (hz : 0 < llist.size l) : 0 < llist.size (follow_llist l h)
        := by { cases l, { cases hz }, 
            { rw [follow_llist,llist.concat_size], apply nat.lt_add_right, apply F.nop } }

    @[simp] lemma follow_head {l h} : (follow_llist l h).head = F.f l.head
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { rw [llist.concat_head], exact (F.df _).hx,
                rw [llist.compat,hr], exact (F.df _).hy } }

    @[simp] lemma follow_last {l h} : (follow_llist l h).last = F.f l.last
        := by { induction l with v v l hr; rw follow_llist, { refl },
            { rw llist.concat_last, exact hr } }

    lemma follow_path {l h} : llist.is_path G'.adj (follow_llist l h)
        := by { induction l with v v l hr; rw [follow_llist],
            { trivial },
            { apply (llist.concat_path G'.adj _).mpr ⟨(F.df _).adj, hr⟩, 
                rw [llist.compat,follow_head,(F.df _).hy] } }

    def follow (p : path G x y) : path G' (F.f x) (F.f y)
        := ⟨⟨follow_llist p.l p.adj, 
            by { rw [follow_head,p.hx] }, 
            by { rw [follow_last,p.hy] }⟩, follow_path⟩

    lemma follow_edges {z l h} (hz : 0 < llist.size l) :
            z ∈ follow_llist l h <-> ∃ e ∈ path.edges_aux l h, z ∈ F.df e
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

    lemma follow_edges' {z} {p : path G x y} (hz : 0 < p.size) : z ∈ follow p <-> ∃ e ∈ path.edges p, z ∈ F.df e
        := follow_edges hz

    lemma follow_simple {l h} (hs : llist.nodup l) : (follow_llist l h).nodup
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
                    suffices : u ∈ (llist.L v l), by { rw h12 at this, cases hs.1 this },
                    cases path.mem_edges_aux h8 with h13 h14,
                    cases F.endpoint h9 with h15 h15; rw h15; assumption } }

    lemma follow_append {v l h} (h') (h'' : G.adj (llist.last l) v) : 
            follow_llist (llist.append v l) h = llist.concat (follow_llist l h') (F.df ⟨h''⟩).l
        := by { induction l with w w l hr,
            { exact llist.concat_nil (F.df _).hy },
            { revert h, rw [llist.append], intro h,
                rw [follow_llist,follow_llist,hr h'.2 h'',llist.concat_assoc], 
                have h3 : llist.head (llist.append v l) = llist.head l := llist.append_head,
                congr; exact h3 } }

    lemma follow_rev {l} (h h') : (follow_llist l h).rev = follow_llist l.rev h'
        := by { induction l with v v l hr, refl,
            rw [follow_llist,llist.rev_concat],
                { replace hr := hr h.2 ((llist.rev_is_path G.adj G.sym).mpr h.2),
                    rw [hr], revert h', rw llist.rev, intro h', rw follow_append, 
                    congr,
                    let e : edge G := ⟨h.1⟩,
                    have h4 : (F.df e).l.rev = (F.df e.flip).l, by { rw F.sym _, refl },
                    convert h4; rw llist.rev_last, exact G.sym h.1 },
                { rw [llist.compat,follow_head], exact (F.df _).hy } }

    @[simp] def sfollow (p : spath G x y) : spath G' (F.f x) (F.f y)
        := ⟨follow p.to_path, follow_simple p.simple⟩

    @[simp] lemma sfollow_rev (p : spath G x y) : sfollow p.rev = (sfollow p).rev
        := by { simp only [sfollow,follow,spath.rev,path.rev], rw follow_rev }
end end embedding

namespace embedding section
    parameters {G G' G'' : digraph} 

    def comp (F : graph_embedding G G') (F' : graph_embedding G' G'') : (graph_embedding G G'') := {
        f := F'.f ∘ F.f,
        df := λ e, sfollow F' (F.df e),
        --
        inj := injective_comp F'.inj F.inj,
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
                { rw [edge.flip] at h5l, rw [edge.flip] at h5r,
                    cases F.disjoint (llist.mem_init h3l) (llist.mem_tail h5r) with h10 h10, assumption,
                    cases F.disjoint (llist.mem_tail h3r) (llist.mem_init h5l) with h11 h11, assumption,
                    obtain ⟨x,hx⟩ := h10, unfold edge.y at h5r, rw [hx] at h3l h5r, clear hx,
                    obtain ⟨y,hy⟩ := h11, unfold edge.x at h5l, rw [hy] at h5l h3r, clear hy,
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

    theorem embed_trans : transitive embeds_into
        := by { intros G G' G'' F F', cases F, cases F', use comp F F' }
end end embedding

namespace contraction section
    structure chunked extends digraph :=
        (rel : V -> V -> Prop)
        (eqv : equivalence rel)
        (cmp : ∀ x y, rel x y -> path.linked x y)

    instance {G : chunked} : setoid G.V := ⟨G.rel,G.eqv⟩

    def adj (G : chunked) (x y) : Prop := ∃ x' y', x' ≈ x ∧ y' ≈ y ∧ G.adj x' y'

    lemma adj_symm {G : chunked} (x y) : adj G x y -> adj G y x
        := by { rintros ⟨x',y',h1,h2,h3⟩, exact ⟨y',x',h2,h1,G.sym h3⟩ }

    lemma adj_lift1 {G : chunked} {a₁ a₂ b₁ b₂ : G.V} {h₁ : a₁ ≈ b₁} {h₂ : a₂ ≈ b₂} : adj G a₁ a₂ -> adj G b₁ b₂
        := by { rintros ⟨x',y',h1,h2,h3⟩, exact ⟨x', y', ⟨G.eqv.2.2 h1 h₁, G.eqv.2.2 h2 h₂, h3⟩⟩ }

    lemma adj_lift {G : chunked} : ∀ (a₁ a₂ b₁ b₂ : G.V), a₁ ≈ b₁ → a₂ ≈ b₂ → adj G a₁ a₂ = adj G b₁ b₂
        := by { intros, apply iff_iff_eq.mp, split; 
                apply adj_lift1; assumption <|> { symmetry, assumption } }

    def contract (G : chunked) : digraph :=
    {
        V   := _,
        adj := quotient.lift₂ (adj G) adj_lift,
        sym := λ x y, quotient.induction_on₂ x y adj_symm
    }

    def is_contraction (G G' : digraph) : Prop := ∃ C : chunked, C.to_digraph = G' ∧ G = contract C

    def proj_llist {G : chunked} : llist G.to_digraph -> llist (contract G) := llist.map (λ x, ⟦x⟧)

    lemma proj_head {G : chunked} {l : llist G.to_digraph} : (proj_llist l).head = ⟦l.head⟧ 
        := llist.head_map

    lemma proj_last {G : chunked} {l : llist G.to_digraph} : (proj_llist l).last = ⟦l.last⟧
        := llist.last_map

    lemma proj_adj {G : chunked} {x y} : G.adj x y -> (contract G).adj ⟦x⟧ ⟦y⟧ 
        := λ h, exists.intro x (exists.intro y ⟨quotient.eq.mp rfl,quotient.eq.mp rfl,h⟩)

    lemma proj_is_path {G : chunked} {l} : llist.is_path G.adj l -> llist.is_path (contract G).adj (proj_llist l)
        := by { induction l, 
            { intro, trivial },
            { intro h, rw [proj_llist,llist.map,llist.is_path,llist.head_map], exact ⟨proj_adj h.1, l_ih h.2⟩ } }

    def proj_path {G : chunked} {x y} (p : path G.to_digraph x y) : path (contract G) ⟦x⟧ ⟦y⟧
        := {
            l := proj_llist p.l,
            hx := by { rw [proj_head,p.hx] },
            hy := by { rw [proj_last,p.hy], },
            adj := proj_is_path p.adj
        }

    lemma contract_connected {G : chunked} (h : connected G.to_digraph) : connected (contract G)
        := by {
            intros xbar ybar,
            obtain ⟨x,hx⟩ := quot.exists_rep xbar, obtain ⟨y,hy⟩ := quot.exists_rep ybar, 
            subst hx, subst hy, obtain γ := h x y, use (proj_path γ)
        }
end end contraction

def is_minor (G G' : digraph) : Prop := ∃ C : contraction.chunked, C.to_digraph = G' ∧ embeds_into G (contraction.contract C)

namespace examples section
    def prod (G₁ G₂ : digraph) : digraph := {
        V   := G₁ × G₂,
        adj := λ x y, (x.1 = y.1 ∧ G₂.adj x.2 y.2) ∨ (G₁.adj x.1 y.1 ∧ x.2 = y.2),
        sym := by { intros x y h, cases h,
            { left, exact ⟨h.1.symm, G₂.sym h.2⟩ },
            { right, exact ⟨G₁.sym h.1, h.2.symm⟩ } }
    }

    def Z : digraph := {
        V := ℤ,
        adj := λ x y, y = x+1 ∨ x = y+1,
        sym := by { tauto }
    }

    def Z2 := prod Z Z

    def K (n : nat) : digraph := {
        V := fin n,
        adj := λ _ _, true,
        sym := by { tauto }
    }

    def K' (n : nat) : digraph := {
        V := fin n,
        adj := λ x y, x ≠ y,
        sym := by { tauto }
    }

    def planar (G : digraph) := is_minor G Z2
end end examples

namespace cayley section
    parameters {G : Type} [group G] (S : set G)

    def adj (x y : G) := ∃ s ∈ S, y = x * s ∨ x = y * s

    lemma shift_adj {a x y : G} : adj x y -> adj (a*x) (a*y) 
        := by { rintro ⟨s,h1,h2⟩, cases h2; use [s,h1],
            { left, rw [h2,mul_assoc] },
            { right, rw [h2,mul_assoc] } }

    @[symm] lemma adj_symm {x y} : adj x y -> adj y x
        := by { intro h, obtain ⟨s,h,h'⟩ := h, use ⟨s,h,h'.symm⟩ }

    def span : digraph := { V := G, adj := adj, sym := @adj_symm }

    def shift_llist (a : G) := llist.map (λ x, a * x)

    lemma shift_is_path {a : G} {l : llist G} : llist.is_path adj l -> llist.is_path adj (shift_llist a l)
        := by { intro h, induction l with v v l hr, trivial, split, 
            { convert shift_adj S h.1, rw [llist.head_map] },
            { exact hr h.2 } }

    def shift_path {x y} (a : G) (p : path span x y) : path span (a*x : G) (a*y : G)
        := { l := shift_llist a p.l,
            hx := by { rw [shift_llist,llist.head_map,p.hx] },
            hy := by { rw [shift_llist,llist.last_map,p.hy] },
            adj := shift_is_path p.adj }

    lemma shift {x y a : G} : @path.linked span x y -> @path.linked span (a*x : G) (a*y : G)
        := by { intro h, cases h, use shift_path S a h }

    lemma inv {x : G} : @path.linked span (1:G) x -> @path.linked span (1:G) (x⁻¹:G)
        := by { intro h, symmetry, rw [<-(mul_left_inv x)], convert shift S h, rw mul_one }

    lemma linked {x} : x ∈ group.closure S -> @path.linked span (1:G) x
        := by { intro h, induction h with s h y hs hl y z hsx hsy hlx hly,
            { use ⟨⟨llist.L (1:G) (llist.P s), rfl, rfl⟩,
                    ⟨s,h,or.inl (by { rw one_mul, refl })⟩, trivial⟩ },
            { refl },
            { apply inv, assumption },
            { transitivity y, assumption, convert shift S hly, rw mul_one } }
            
    lemma cayley_connected (h : group.closure S = @set.univ G) : connected (span)
        := by {
            suffices : ∀ x, @path.linked (span S) (1:G) x,
                { intros x y, exact path.linked_trans (this x).symm (this y) },
            intro, apply linked, rw h, trivial
        }
end end cayley

def planar (G : digraph) : Prop := is_minor G examples.Z2
def colorable (n : nat) (G : digraph) : Prop := nonempty (digraph.hom G (examples.K' n))

-- theorem four_color {G : digraph} : planar G -> colorable 4 G := sorry
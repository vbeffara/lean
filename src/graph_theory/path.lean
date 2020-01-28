import tactic
import graph_theory.basic llist

structure path  (G : Graph) (x y) extends llist' G x y := (adj : llist.is_path G.adj l)

namespace path section
    parameters {G : Graph}
    variables {x y z : G}

    instance : has_coe (path G x y) (llist' G x y) := ⟨path.to_llist'⟩

    def mem (v : G) (p : path G x y) := v ∈ p.l
    instance : has_mem G (path G x y) := ⟨mem⟩

    def simple     (p : path G x y) : Prop := llist.nodup p.l
    def size       (p : path G x y) : nat  := llist.size p.l

    instance : has_sizeof (path G x y) := ⟨size⟩

    def point (v : G) : path G v v
        := ⟨⟨llist.P v, rfl, rfl⟩, trivial⟩

    def from_edge {x y} (h : G.adj x y) : path G x y 
        := ⟨⟨llist.L x (llist.P y), rfl, rfl⟩, ⟨h,trivial⟩⟩

    def rev (p : path G x y) : path G y x
        := ⟨⟨llist.rev p.l, by { rw [llist.head_rev,p.hy] }, by { rw [llist.last_rev,p.hx] }⟩, 
            (llist.is_path_rev G.adj G.sym).mpr p.adj⟩

    lemma size_rev {p : path G x y} : size p.rev = size p
        := llist.size_rev

    def concat (p : path G x y) (p' : path G y z) : path G x z
        := ⟨llist'.concat p.to_llist' p'.to_llist', 
            (llist.is_path_concat G.adj llist'.compat).mpr ⟨p.adj,p'.adj⟩⟩

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

    lemma to_path : linked G x y -> nonempty (path G x y)
        := by { intro h, induction h with b c hxb hbc hr, use path.point x,
            cases hr, use path.concat hr (path.from_edge hbc) }

    lemma from_path : nonempty (path G x y) -> linked G x y
        := by { intro h, rcases h with ⟨⟨l,hx,hy⟩,hp⟩, revert x y, induction l with v v l hr,
            { intros, subst hx, subst hy, refl },
            { intros, cases hp with hp1 hp2, replace hr := hr rfl rfl hp2,
                convert linked.cons hp1 hr, subst hx, refl, subst hy, refl } }

    lemma iff_path : linked G x y <-> nonempty (path G x y)
        := ⟨to_path,from_path⟩

    instance [connected_graph G] : nonempty (path G x y) := to_path (connected_graph.conn G x y)
end end path

@[ext] structure  spath (G : Graph) (x y) extends path G x y := ( simple : path.simple  to_path)

namespace spath section
    parameters {G : Graph}
    variables {x y z : G}

    def mem (z) (p : spath G x y) := z ∈ to_path p
    instance : has_mem G.V (spath G x y) := ⟨mem⟩

    def size (p : spath G x y) : nat := p.to_path.size

    instance : has_coe (spath G x y) (path G x y) := ⟨spath.to_path⟩

    def rev (p : spath G x y) : spath G y x
        := ⟨p.to_path.rev, llist.nodup_rev.mpr p.simple⟩

    lemma edges_simple {p : spath G x y} : list.pairwise edge.nsame p.to_path.edges
        := path.edges_simple _ p.simple
end end spath

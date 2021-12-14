import tactic
import graph_theory.basic llist

namespace simple_graph
    structure path {V : Type} (G : simple_graph V) (x y) extends llist' V x y
      := (adj : llist.is_path G.adj l)

    namespace path
        variables {V : Type} (G : simple_graph V) {x y z : V}

        instance : has_coe (path G x y) (llist' V x y) := ⟨path.to_llist'⟩

        def mem {G : simple_graph V} (v : V) (p : path G x y) : Prop := v ∈ p.l

        instance : has_mem V (path G x y) := ⟨mem⟩

        def simple     (p : path G x y) : Prop := llist.nodup p.l

        def size {G : simple_graph V} (p : path G x y) : nat  := llist.size p.l

        instance : has_sizeof (path G x y) := ⟨size⟩

        def point (v : V) : path G v v
            := ⟨⟨llist.pt v, rfl, rfl⟩, trivial⟩

        def step (h : G.adj x y) (p : path G y z) : path G x z
            := by {
                refine p.cases_on (λ l', _),
                refine l'.cases_on (λ l hy hz, _),
                exact (λ hh, (⟨⟨llist.cons x l,rfl,hz⟩,⟨hy.symm ▸ h,hh⟩⟩ : path G x z))
            }

        def from_edge (h : G.adj x y) : path G x y
            := ⟨⟨llist.cons x (llist.pt y), rfl, rfl⟩, ⟨h,trivial⟩⟩

        def rev (p : path G x y) : path G y x
            := ⟨⟨llist.rev p.l, by { rw [llist.head_rev,p.hy] }, by { rw [llist.last_rev,p.hx] }⟩,
                (llist.is_path_rev G.adj G.sym).mpr p.adj⟩

        lemma size_rev {p : path G x y} : size (rev G p) = size p
            := llist.size_rev

        def concat (p : path G x y) (p' : path G y z) : path G x z
            := ⟨llist'.concat p.to_llist' p'.to_llist',
                (llist.is_path_concat G.adj llist'.compat).mpr ⟨p.adj,p'.adj⟩⟩

        @[simp] lemma size_concat {p : path G x y} {p' : path G y z} : (concat G p p').size = p.size + p'.size
            := llist.concat_size

        def edges_aux : Π (l : llist V) (h : llist.is_path G.adj l), list (edges G)
            | (llist.pt v)   _ := []
            | (llist.cons v l) h := ⟨h.1⟩ :: edges_aux l h.2

        def all_edges {G : simple_graph V} (p : path G x y) : list (edges G)
            := edges_aux G p.l p.adj

        lemma mem_edges_aux' {G : simple_graph V} {l h} {e : edges G} : e ∈ edges_aux G l h -> e.x ∈ l.init ∧ e.y ∈ l.tail
            := by { induction l with v v l hr; intros he; cases he with he he,
                { subst he, split; left; refl },
                { cases hr he, split; right; assumption } }

        lemma mem_edges_aux {G : simple_graph V} {l h} {e : edges G} : e ∈ edges_aux G l h -> e.x ∈ l ∧ e.y ∈ l
            := by { intro h1, cases mem_edges_aux' h1 with h2 h3, split,
                { exact llist.mem_init_last.mpr (or.inl h2) },
                { exact llist.mem_head_tail.mpr (or.inr h3) } }

        lemma mem_edges {G : simple_graph V} {p : path G x y} {e : edges G} : e ∈ p.all_edges -> e.x ∈ p ∧ e.y ∈ p
            := mem_edges_aux

        lemma edges_simple {l} (h : llist.is_path G.adj l) (hs : llist.nodup l) : list.pairwise (edges.nsame) (edges_aux G l h)
            := by { induction l with v v l hr, { exact list.pairwise.nil },
                { apply list.pairwise.cons,
                { intros e he, rw [edges.nsame, edges.same], push_neg, have h5 := mem_edges_aux he,
                    split; intro h6; subst h6, exact hs.1 h5.1, exact hs.1 h5.2 },
                { exact hr h.2 hs.2 } } }

        lemma to_path : linked G x y -> nonempty (path G x y)
            := by { intro h, induction h with b c hxb hbc hr, use path.point G x,
                cases hr, use path.concat G hr (path.from_edge G hbc) }

        lemma from_path : nonempty (path G x y) -> linked G x y
            := by { intro h, rcases h with ⟨⟨l,hx,hy⟩,hp⟩, revert x y, induction l with v v l hr,
                { intros, subst hx, subst hy, refl },
                { intros, cases hp with hp1 hp2, replace hr := hr rfl rfl hp2,
                    convert linked.cons hp1 hr, subst hx, refl, subst hy, refl } }

        lemma iff_path : linked G x y <-> nonempty (path G x y)
            := ⟨to_path G,from_path G⟩

        instance [connected_graph G] : nonempty (path G x y) := to_path G (connected_graph.conn x y)
    end path

    @[ext] structure spath {V : Type} (G : simple_graph V) (x y) extends path G x y
        := (simple : path.simple G to_path)

    namespace spath
        variables {V : Type} {G : simple_graph V} {x y z : V}

        def mem (z) (p : spath G x y) := z ∈ to_path p
        instance : has_mem V (spath G x y) := ⟨mem⟩

        def size (p : spath G x y) : nat := p.to_path.size

        instance : has_coe (spath G x y) (path G x y) := ⟨spath.to_path⟩

        def rev (p : spath G x y) : spath G y x
            := ⟨path.rev G p.to_path , llist.nodup_rev.mpr p.simple⟩

        lemma edges_simple {p : spath G x y} : list.pairwise (edges.nsame) p.to_path.all_edges
            := path.edges_simple G _ p.simple
    end spath
end simple_graph

namespace simple_graph
    variables {V : Type} {G : simple_graph V}

    inductive path2 (G : simple_graph V) : V -> V -> Type
    | point (x : V) : path2 x x
    | step {x y z : V} : G.adj x y -> path2 y z -> path2 x z

    def concat2 {x y z : V} (p1 : path2 G x y) (p2 : path2 G y z) : path2 G x z
    := begin
        induction p1 with x u v w h1 p'1 h2, exact p2,
        refine path2.step h1 (h2 p2)
    end

    def concat2' {x y z : V} (p1 : path2 G x y) (p2 : path2 G y z) : path2 G x z
        := path2.rec (λ _ p2, p2) (λ _ _ _ h' _ h p3, path2.step h' (h p3)) p1 p2

    def path_to_path2 {x y : V} (p : path G x y) : path2 G x y
    := begin
        rcases p with ⟨⟨l,hx,hy⟩,h⟩, simp at h, revert x y h hx hy,
        induction l with x' x' l ih; intros x y h hx hy,
        { rw [<-hx, <-hy], exact path2.point x' },
        { rw [<-hx], exact path2.step h.1 (ih h.2 rfl hy) }
    end

    #print path_to_path2

    def path2_to_path {x y : V} (p : path2 G x y) : path G x y
        := path2.rec (path.point G) (λ _ _ _ h _, path.step G h) p

    @[simp] lemma toto {x y z : V} {h : G.adj x y} {p : path2 G y z}: path2_to_path (path2.step h p) = path.step G h (path2_to_path p)
        := rfl

    @[simp] lemma toto2 {x y z : V} {h : G.adj x y} {p : path G y z}: path_to_path2 (path.step G h p) = path2.step h (path_to_path2 p)
        := by { rcases p with ⟨⟨l,hx,hy⟩,hh⟩, finish }

    lemma path2_to_path_to_path2 {x y : V} {p : path2 G x y}: path_to_path2 (path2_to_path p) = p
        := by { induction p; simpa }
end simple_graph

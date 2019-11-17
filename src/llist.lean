import tactic

inductive llist (V : Type) : Type | P : V -> llist | L : V -> llist -> llist

namespace llist section
    parameters {V : Type} (adj : V -> V -> Prop)

    def mem : V -> llist V -> Prop | x (P v) := x = v | x (L v l) := x = v ∨ mem x l
    instance has_mem_llist : has_mem V (llist V) := ⟨mem⟩

    def to_list :            llist V -> list V  |   (P v)    := [v]       |   (L v l)    := v :: to_list l
    def size    :            llist V -> nat     |   (P _)    := 0         |   (L v l)    := (size l) + 1
    def head    :            llist V -> V       |   (P v)    := v         |   (L v l)    := v
    def tail    :            llist V -> list V  |   (P v)    := []        |   (L v l)    := l.head :: tail l
    def init    :            llist V -> list V  |   (P v)    := []        |   (L v l)    := v :: init l
    def last    :            llist V -> V       |   (P v)    := v         |   (L v l)    := last l
    def inside  :            llist V -> list V  |   (P v)    := []        |   (L v l)    := init l
    def is_path :            llist V -> Prop    |   (P v)    := true      |   (L v l)    := adj v l.head ∧ is_path l
    def append  :       V -> llist V -> llist V | x (P v)    := L v (P x) | x (L v l)    := L v (append x l)
    def rev     :            llist V -> llist V |   (P v)    := (P v)     |   (L v l)    := append v (rev l)
    def nodup   :            llist V -> Prop    |   (P v)    := true      |   (L v l)    := v ∉ l ∧ nodup l
    def concat  : llist V -> llist V -> llist V |   (P _) l' := l'        |   (L v l) l' := L v (concat l l')

    @[simp] def compat (l₁ l₂ : llist V) := last l₁ = head l₂
    def qnodup (l : llist V) := head l ∉ inside l ∧ last l ∉ inside l ∧ list.nodup (inside l)

    variables {x y v w : V} {l l' l'' : llist V}

    @[simp] lemma head_P                           : head (P x)               = x
        := rfl

    @[simp] lemma head_cons                        : head (L v l)             = v
        := rfl

    @[simp] lemma last_P                           : last (P x)               = x
        := rfl

    @[simp] lemma concat_head    (h : compat l l') : head (concat l l')       = head l
        := by { cases l, { rw compat at h, rw [concat,<-h], refl }, { refl } }

    @[simp] lemma concat_last                      : last (concat l l')       = last  l'
        := by { induction l, { rw concat }, { rwa [concat,last] } }

    @[simp] lemma append_head                      : head (append v l)        = head l
        := by { cases l; refl }

    @[simp] lemma append_last                      : last (append v l)        = v
        := by { induction l, refl, rwa [append,last] }

    @[simp] lemma rev_append                       : rev  (append v l)        = L v (rev l)
        := by { induction l, refl, rw [append,rev,l_ih], refl }

    @[simp] lemma append_rev                       : rev (L v l)              = append v (rev l)
        := rfl

    @[simp] lemma rev_head                         : head (rev l)             = last l
        := by { induction l, refl, rwa [rev,append_head,last] }

    @[simp] lemma rev_last                         : last (rev l)             = head l
        := by { cases l, refl, rw [rev,append_last,head] }

    @[simp] lemma rev_rev                          : rev  (rev l)             = l
        := by { induction l, refl, rw [rev,rev_append,l_ih] }

    @[simp] lemma mem_singleton                    : x ∈ P y                <-> x = y
        := iff.rfl

    @[simp] lemma mem_cons                         : x ∈ L v l              <-> x = v ∨ x ∈ l
        := iff.rfl

    @[simp] lemma concat_path    (h : compat l l') : is_path (concat l l')  <-> is_path l ∧ is_path l'
        := by { induction l with v v l hr,
            { rw [concat,is_path], tauto },
            { replace hr := hr h, rw [concat,is_path,hr,is_path,concat_head], tauto, exact h } }

    @[simp] lemma mem_append                       : w ∈ append v l         <-> w = v ∨ w ∈ l
        := by { induction l, rw [append,mem_cons,mem_singleton,mem_singleton,or_comm],
            rw [append,mem_cons,l_ih,mem_cons], exact or.left_comm }

    @[simp] lemma mem_rev                          : v ∈ rev l              <-> v ∈ l
        := by { induction l, { rw [rev] }, { rw [rev,mem_append,l_ih,mem_cons] } }

    @[simp] lemma mem_head                         : head l ∈ l
        := by { cases l, { rw [head,mem_singleton] }, { left, refl } }

    @[simp] lemma mem_last                         : last l ∈ l
        := by { induction l, { rw [last,mem_singleton] }, { right, assumption } }

    @[simp] lemma mem_list                         : x ∈ to_list l          <-> x ∈ l
        := by { induction l, 
            { rw [to_list,mem_singleton,list.mem_singleton] }, 
            { rw [to_list,list.mem_cons_iff,l_ih,mem_cons] } }

    @[simp] lemma append_nodup                     : nodup (append x l)     <-> x ∉ l ∧ nodup l
        := by { induction l,
            { rw [append,nodup,nodup,nodup,mem_singleton,mem_singleton], tauto },
            { rw [append,nodup,l_ih,mem_append,mem_cons,nodup], tauto } }

    @[simp] lemma rev_nodup                        : nodup (rev l)          <-> nodup l
        := by { induction l, { rw [rev] }, { rw [rev,append_nodup,l_ih,mem_rev,nodup] } }

    @[simp] lemma append_is_path                   : is_path (append v l)   <-> adj (last l) v ∧ is_path l
        := by { induction l, { rw [append,is_path,head,last,is_path,is_path] }, 
            { rw [append,is_path,l_ih,last,is_path,append_head], tauto } }

    @[simp] lemma init_append                      : init (append x l)        = to_list l
        := by { induction l, { refl }, { rw [append,init,l_ih,to_list] } }

    @[simp] lemma list_head_tail                   : head l :: tail l         = to_list l
        := by { induction l, { refl }, { rw [head,tail,l_ih,to_list] } }

    @[simp] lemma list_init_last                   : init l ++ [last l]       = to_list l
        := by { induction l, { refl }, { rw [init,last,to_list,<-l_ih], refl } }

    @[simp] lemma list_head_init'                  : v :: inside (L v l) = init (L v l)
        := rfl

    @[simp] lemma list_head_init  (h : 0 < size l) : head l :: inside l       = init l
        := by { cases l, cases h, refl }

    @[simp] lemma list_tail_last'                  : inside (L v l) ++ [last (L v l)] = tail (L v l)
        := by { rw [inside,last,tail,list_init_last,list_head_tail] }

    @[simp] lemma list_tail_last  (h : 0 < size l) : inside l ++ [last l]     = tail l
        := by { cases l, cases h, exact list_tail_last' }

    @[simp] lemma inside_append                    : inside (append x l)      = tail l
        := by { cases l, refl, rw [append,inside,init_append,tail,list_head_tail] }

    @[simp] lemma tail_append                      : tail (append x l)        = tail l ++ [x]
        := by { induction l, refl, rw [append,tail,l_ih,append_head,tail], refl }

    @[simp] lemma tail_rev                         : tail (rev l)             = list.reverse (init l)
        := by { induction l, refl, rw [rev,tail_append,l_ih,init,list.reverse_cons] }

    @[simp] lemma rev_inside                       : inside (rev l)           = list.reverse (inside l)
        := by { cases l, refl, rw [rev,inside_append,tail_rev,inside] }

    @[simp] lemma rev_qnodup                       : qnodup (rev l)         <-> qnodup l
        := by { rw [qnodup,qnodup,rev_inside,list.nodup_reverse,rev_head,list.mem_reverse],
                rw [rev_last,list.mem_reverse], tauto }

    @[simp] lemma rev_is_path  (h : symmetric adj) : is_path (rev l)        <-> is_path l
        := by { induction l, rw [rev], rw [rev,append_is_path,rev_last,is_path,l_ih], rw symmetric at h, 
            exact and_congr ⟨@h _ _, @h _ _⟩ iff.rfl }

    @[simp] lemma mem_concat     (h : compat l l') : x ∈ concat l l'        <-> x ∈ l ∨ x ∈ l'
        := by { induction l, 
            { rw [concat,mem_singleton], refine ⟨or.inr, _⟩, 
                intro h1, cases h1, convert mem_head, rwa h1, exact h1 }, 
            { rw [concat,mem_cons,l_ih h,mem_cons,or.assoc] } }

    @[simp] lemma concat_nil      (h : last l = w) : concat l (P w)           = l
        := by { rw <-h, clear h, induction l, refl, { rw [concat,last,l_ih] } }

    @[simp] lemma concat_nil2                      : concat (P w) l           = l
        := rfl

    @[simp] lemma concat_size                      : size (concat l l')       = size l + size l'
        := by { induction l; rw [concat,size], { norm_num }, { rw [l_ih,size], norm_num } }

    lemma         concat_assoc                     : concat (concat l l') l'' = concat l (concat l' l'')
        := by { induction l; rw [concat,concat], rw [l_ih,concat] }

    lemma         concat_nodup   (h : compat l l') : nodup (concat l l')    <-> nodup l ∧ nodup l' ∧ (∀ x, x ∈ l ∧ x ∈ l' -> x = head l')
        := by { induction l with v v l hr; rw [concat,nodup],
            { split, { intro, refine ⟨trivial,a,_⟩, intros x h1, rw mem_singleton at h1, rwa h1.1 }, tauto },
            { rw [nodup,hr h], rw [compat,last] at h, split,
                { rintros ⟨h1,h2,h3,h4⟩, rw mem_concat h at h1, push_neg at h1, refine ⟨⟨h1.1,h2⟩,h3,_⟩,
                    rintros x ⟨h6,h7⟩, cases h6,
                    { subst h6, cases h1.2 h7 },
                    { exact h4 x ⟨h6,h7⟩ } },
                { rintros ⟨⟨h1,h2⟩,h3,h4⟩, rw mem_concat h, push_neg, refine ⟨⟨h1,_⟩,h2,h3,_⟩,
                    { intro h5, have h6 := h4 v ⟨(or.inl rfl),h5⟩, subst h6, rw <-h at h1, exact (h1 mem_last) },
                    { rintros x ⟨h5,h6⟩, exact h4 x ⟨(or.inr h5),h6⟩ } } } }

    lemma         mem_iff             (h : l = l') : x ∈ l                  <-> x ∈ l'
        := by { rw h }

    lemma         mem_init        (h : x ∈ init l) : x ∈ l
        := by { induction l, cases h, cases h, exact or.inl h, exact or.inr (l_ih h) }

    lemma         mem_head_init'                   : v ∈ init (L v l)
        := by { rw [init], left, refl }

    lemma         mem_head_init   (h : 0 < size l) : head l ∈ init l
        := by { cases l, cases h, exact mem_head_init' }

    lemma         mem_last_tail   (h : 0 < size l) : last l ∈ tail l
        := by { cases l, cases h, clear h, rw [last,tail], induction l_a_1,
            { left, refl }, { rw [last,head,tail], right, assumption } }

    lemma         mem_tail        (h : x ∈ tail l) : x ∈ l
        := by { cases l, cases h, rw [tail,list_head_tail,mem_list] at h, right, assumption }

    lemma         mem_init_last                    : x ∈ l                  <-> x ∈ init l ∨ x = last l
        := by { split,
            { intro, induction l, { right, assumption }, { cases a, { left, left, exact a },
                cases l_ih a, { left, right, assumption }, { right, rwa last } } },
            { intro, cases a, exact mem_init a, convert mem_last } }

    lemma         mem_head_tail                    : x ∈ l                  <-> x = head l ∨ x ∈ tail l
        := by { cases l, { rw [mem_singleton,head,tail], convert (or_false _).symm },
            { rw [head,tail,list_head_tail,mem_list,mem_cons] } }

    lemma         mem_init_inside (h : 0 < size l) : x ∈ init l             <-> x = head l ∨ x ∈ inside l
        := by { rw [<-(list_head_init h),list.mem_cons_iff] }

    lemma         mem_tail_inside (h : 0 < size l) : x ∈ tail l             <-> x ∈ inside l ∨ x = last l
        := by { rw [<-(list_tail_last h),list.mem_append_eq,list.mem_singleton] }

    lemma         nodup_mem_head     (h : nodup l) : head l ∉ tail l
        := by { cases l, { rw [tail,list.mem_nil_iff], trivial }, 
            { rw [head,tail,list_head_tail,mem_list], exact h.1 } }

    lemma         nodup_mem_last     (h : nodup l) : last l ∉ init l
        := by { induction l, { rw [init,list.mem_nil_iff], trivial }, 
            { rw [last,init,list.mem_cons_iff], push_neg, split,
                { intro, apply h.1, convert mem_last, exact a.symm },
                { exact l_ih h.2 } } }

    lemma         rev_compat                       : compat l l' <-> compat l'.rev l.rev
        := by { rw [compat,compat,rev_last,rev_head,eq_comm] }

    lemma         concat_append                    : append v (concat l l')  = concat l (append v l')
        := by { induction l; rw [concat,concat], rw [append,l_ih] }

    lemma         rev_concat     (h : compat l l') : rev (concat l l')       = concat (rev l') (rev l)
        := by { induction l,
            { rw [concat,rev,concat_nil], rw [rev_last], exact h.symm },
            { rw [concat,rev,l_ih h,concat_append,rev] } }

    lemma         nodup_init         (h : nodup l) : list.nodup (init l)
        := by { induction l, { exact list.pairwise.nil }, 
            { rw [init,list.nodup,list.pairwise_cons], refine ⟨_,l_ih h.2⟩, 
                intros a h1 h2, replace h := h.1, rw h2 at h, exact h (mem_init h1) } }

    lemma         nodup_qnodup       (h : nodup l) : qnodup l
        := by { induction l, 
            { exact ⟨not_false,not_false,list.pairwise.nil⟩ },
            { refine ⟨_,nodup_mem_last h.2, nodup_init h.2⟩, intro h1, exact h.1 (mem_init h1) } }

    lemma         nodup_of_init : list.nodup (init l) -> last l ∉ init l -> nodup l
        := by { induction l, { intros, trivial },
            { rw [init,last,nodup,list.nodup_cons,list.mem_cons_iff], push_neg, 
                rintros ⟨h1,h2⟩ ⟨h3,h4⟩, refine ⟨_,l_ih h2 h4⟩,
                rw mem_init_last, push_neg, exact ⟨h1,h3.symm⟩ } }

    lemma         qnodup_ne_nodup : qnodup l -> head l ≠ last l -> nodup l
        := by { cases l, { intros, trivial },
            { rw [qnodup,head,inside], intros, apply nodup_of_init, 
                { rw [init,list.nodup_cons], exact ⟨a.1,a.2.2⟩ },
                { rw [init,list.mem_cons_iff], push_neg, exact ⟨a_1.symm,a.2.1⟩ } } }
end end llist

structure llist' (V : Type) (x y : V) := (l : llist V) (hx : x = l.head) (hy : l.last = y)
instance llist'_to_llist {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' section open llist
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V}

    def mem (v : V) (l : llist' V x y) := v ∈ l.l
    instance has_mem : has_mem V (llist' V x y) := ⟨mem⟩

    @[extensionality] lemma ext {l l' : llist' V x y} : l.l = l'.l -> l = l' 
        := by { intro, cases l, cases l', congr, assumption }

    @[simp] lemma reduce {l hx hy} : (⟨l,hx,hy⟩ : llist' V x y).l = l := rfl

    @[simp] lemma mem_simp {v l hx hy} : v ∈ (⟨l,hx,hy⟩ : llist' V x y) <-> v ∈ l
        := by { trivial }

    def P    (v : V)                    : llist' V v v := ⟨P v,     rfl, rfl⟩
    def cons (v : V) (l : llist' V x y) : llist' V v y := ⟨L v l.l, rfl, l.hy⟩

    @[simp] lemma head   {l : llist' V x y}                     : l.l.head = x          := l.hx.symm
    @[simp] lemma last   {l : llist' V x y}                     : l.l.last = y          := l.hy

    lemma compat {l : llist' V x y} {l' : llist' V y z} : llist.compat l.l l'.l 
        := eq.trans l.hy l'.hx

    def concat {x y z : V} (l : llist' V x y) (l' : llist' V y z) : llist' V x z
        := ⟨llist.concat l.l l'.l, eq.trans l.hx (concat_head compat).symm, eq.trans concat_last l'.hy⟩

    @[simp] lemma concat_P {l : llist' V x y} : concat l (P y) = l
        := by { ext, exact llist.concat_nil l.hy }
end end llist'

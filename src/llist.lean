import tactic

inductive llist (V : Type) : Type | pt : V -> llist | cons : V -> llist -> llist

namespace llist section
    variables {V W : Type} (adj : V -> V -> Prop) (f : V -> W)

    def mem (x) : llist V -> Prop | (pt v) := x = v | (cons v l) := x = v ∨ mem l
    instance : has_mem V (llist V) := ⟨mem⟩

    @[simp] def to_list        : llist V -> list V  | (pt v) := [v]          | (cons v l) := v :: to_list l
    @[simp] def size           : llist V -> nat     | (pt _) := 0            | (cons v l) := (size l) + 1
    @[simp] def head           : llist V -> V       | (pt v) := v            | (cons v l) := v
    @[simp] def tail           : llist V -> list V  | (pt v) := []           | (cons v l) := l.head :: tail l
    @[simp] def init           : llist V -> list V  | (pt v) := []           | (cons v l) := v :: init l
    @[simp] def last           : llist V -> V       | (pt v) := v            | (cons v l) := last l
    @[simp] def inside         : llist V -> list V  | (pt v) := []           | (cons v l) := init l
    @[simp] def is_path        : llist V -> Prop    | (pt v) := true         | (cons v l) := adj v l.head ∧ is_path l
    @[simp] def append (x : V) : llist V -> llist V | (pt v) := cons v (pt x) | (cons v l) := cons v (append l)
    @[simp] def rev            : llist V -> llist V | (pt v) := (pt v)        | (cons v l) := append v (rev l)
    @[simp] def nodup          : llist V -> Prop    | (pt v) := true         | (cons v l) := v ∉ l ∧ nodup l
    @[simp] def map            : llist V -> llist W | (pt v) := pt (f v)      | (cons v l) := cons (f v) (map l)

    @[simp] def concat : llist V -> llist V -> llist V | (pt _) l' := l' | (cons v l) l' := cons v (concat l l')

    variables {x y v w : V} {l l' l'' : llist V}

    @[simp] def compat (l l' : llist V) := last l = head l'

    @[simp] lemma head_pt : head (pt v) = v := rfl

    @[simp] lemma head_concat : compat l l' -> head (concat l l') = head l
        := by { cases l, exact eq.symm, simp }

    @[simp] lemma concat_last : last (concat l l') = last  l'
        := by { induction l, refl, simpa }

    @[simp] lemma head_append : head (append v l) = head l
        := by { cases l; refl }

    @[simp] lemma last_append : last (append v l) = v
        := by { induction l, refl, simpa }

    @[simp] lemma rev_append : rev (append v l) = cons v (rev l)
        := by { induction l, refl, simp [l_ih] }

    @[simp] lemma head_rev : head (rev l) = last l
        := by { induction l, refl, simpa }

    @[simp] lemma last_rev : last (rev l) = head l
        := by { cases l, refl, simp }

    @[simp] lemma rev_rev : rev (rev l) = l
        := by { induction l, refl, simpa }

    @[simp] lemma mem_singleton : x ∈ pt y <-> x = y := iff.rfl
    @[simp] lemma mem_cons : x ∈ cons v l <-> x = v ∨ x ∈ l := iff.rfl

    @[simp] lemma is_path_concat (h : compat l l') : is_path adj (concat l l') <-> is_path adj l ∧ is_path adj l'
        := by { induction l, tauto, simp at h, finish [l_ih h,head_concat h] }

    @[simp] lemma mem_append : w ∈ append v l <-> w = v ∨ w ∈ l
        := by { induction l, finish, finish [l_ih] }

    @[simp] lemma mem_rev : v ∈ rev l <-> v ∈ l
        := by { induction l, refl, finish [rev] }

    @[simp] lemma head_mem : head l ∈ l
        := by { cases l; simp }

    @[simp] lemma last_mem : last l ∈ l
        := by { induction l, simp, simp [l_ih] }

    @[simp] lemma mem_list : x ∈ to_list l <-> x ∈ l
        := by { induction l, simp, simp [l_ih] }

    @[simp] lemma nodup_append : nodup (append x l) <-> x ∉ l ∧ nodup l
        := by { induction l; split; finish }

    @[simp] lemma nodup_rev : nodup (rev l) <-> nodup l
        := by { induction l, simp, simp [l_ih] }

    @[simp] lemma append_is_path : is_path adj (append v l) <-> adj (last l) v ∧ is_path adj l
        := by { induction l; finish }

    lemma init_append : init (append x l) = to_list l
        := by { induction l, refl, simpa }

    lemma head_tail : list.cons (head l) (tail l) = to_list l
        := by { induction l, refl, simpa }

    lemma init_last : init l ++ [last l] = to_list l
        := by { induction l, { refl }, { rw [init,last,to_list,<-l_ih], refl } }

    @[simp] lemma head_inside  (h : 0 < size l) : list.cons (head l) (inside l) = init l
        := by { cases l, cases h, refl }

    @[simp] lemma inside_last' : inside (cons v l) ++ [last (cons v l)] = tail (cons v l)
        := by { simp [init_last,head_tail] }

    @[simp] lemma inside_last (h : 0 < size l) : inside l ++ [last l] = tail l
        := by { cases l, cases h, exact inside_last' }

    @[simp] lemma inside_append : inside (append x l) = tail l
        := by { cases l, refl, simp [init_append,head_tail] }

    @[simp] lemma tail_append : tail (append x l) = tail l ++ [x]
        := by { induction l, refl, simpa }

    @[simp] lemma tail_rev : tail (rev l) = (init l).reverse
        := by { induction l, refl, simp [l_ih] }

    @[simp] lemma inside_rev : inside (rev l) = (inside l).reverse
        := by { cases l, refl, simp }

    @[simp] lemma is_path_rev (h : symmetric adj) : is_path adj (rev l) <-> is_path adj l
        := by { induction l, trivial, simp [l_ih], intro hh, split; apply h }

    @[simp] lemma mem_concat (h : compat l l') : x ∈ concat l l' <-> x ∈ l ∨ x ∈ l'
        := by { induction l,
            { simp at ⊢ h, subst h, cases l', simp, simp },
            { simp at ⊢ h, simp [l_ih h,or_assoc] } }

    @[simp] lemma concat_nil (h : last l = w) : concat l (pt w) = l
        := by { subst h, induction l, refl, simpa }

    @[simp] lemma concat_size : size (concat l l') = size l + size l'
        := by { induction l, simp, rw [concat,size,l_ih,size], linarith }

    lemma concat_assoc : concat (concat l l') l'' = concat l (concat l' l'')
        := by { induction l; rw [concat,concat], rw [l_ih,concat] }

    lemma concat_nodup (h : compat l l') : nodup (concat l l') <-> nodup l ∧ nodup l' ∧ (∀ x, x ∈ l ∧ x ∈ l' -> x = head l')
        := by { induction l with v v l hr; rw [concat,nodup],
            { split, { intro a, refine ⟨trivial,a,_⟩, intros x h1, rw mem_singleton at h1, rwa h1.1 }, tauto },
            { rw [nodup,hr h], rw [compat,last] at h, split,
                { rintros ⟨h1,h2,h3,h4⟩, rw mem_concat h at h1, push_neg at h1, refine ⟨⟨h1.1,h2⟩,h3,_⟩,
                    rintros x ⟨h6,h7⟩, cases h6,
                    { subst h6, cases h1.2 h7 },
                    { exact h4 x ⟨h6,h7⟩ } },
                { rintros ⟨⟨h1,h2⟩,h3,h4⟩, rw mem_concat h, push_neg, refine ⟨⟨h1,_⟩,h2,h3,_⟩,
                    { intro h5, have h6 := h4 v ⟨(or.inl rfl),h5⟩, subst h6, rw <-h at h1, exact (h1 last_mem) },
                    { rintros x ⟨h5,h6⟩, exact h4 x ⟨(or.inr h5),h6⟩ } } } }

    lemma mem_init (h : x ∈ init l) : x ∈ l
        := by { induction l, cases h, cases h, exact or.inl h, exact or.inr (l_ih h) }

    lemma mem_head_init (h : 0 < size l) : head l ∈ init l
        := by { cases l, cases h, left, refl }

    lemma mem_last_tail (h : 0 < size l) : last l ∈ tail l
        := by { cases l with v v l, cases h, induction l, simp, right, exact l_ih nat.succ_pos' }

    lemma mem_tail (h : x ∈ tail l) : x ∈ l
        := by { cases l, cases h, rw [tail,head_tail,mem_list] at h, right, assumption }

    lemma mem_init_last : x ∈ l <-> x ∈ init l ∨ x = last l
        := by { split,
            { intro a, induction l, { right, assumption }, { cases a, { left, left, exact a },
                cases l_ih a, { left, right, assumption }, { right, rwa last } } },
            { intro a, cases a, exact mem_init a, convert last_mem } }

    lemma mem_head_tail : x ∈ l <-> x = head l ∨ x ∈ tail l
        := by { cases l, { rw [mem_singleton,head,tail], convert (or_false _).symm },
            { rw [head,tail,head_tail,mem_list,mem_cons] } }

    lemma mem_init_inside (h : 0 < size l) : x ∈ init l <-> x = head l ∨ x ∈ inside l
        := by { rw [<-(head_inside h),list.mem_cons_iff] }

    lemma mem_tail_inside' : x ∈ tail (cons v l) <-> x ∈ inside (cons v l) ∨ x = last l
        := by { rw [inside,<-mem_init_last,tail,mem_head_tail], trivial }

    lemma mem_tail_inside (h : 0 < size l) : x ∈ tail l <-> x ∈ inside l ∨ x = last l
        := by { rw [<-(inside_last h),list.mem_append_eq,list.mem_singleton] }

    lemma nodup_mem_head (h : nodup l) : head l ∉ tail l
        := by { cases l, { rw [tail,list.mem_nil_iff], trivial },
            { rw [head,tail,head_tail,mem_list], exact h.1 } }

    lemma nodup_mem_last (h : nodup l) : last l ∉ init l
        := by { induction l, { rw [init,list.mem_nil_iff], trivial },
            { rw [last,init,list.mem_cons_iff], push_neg, split,
                { intro a, apply h.1, convert last_mem, exact a.symm },
                { exact l_ih h.2 } } }

    lemma rev_compat : compat l l' <-> compat l'.rev l.rev
        := by { rw [compat,compat,last_rev,head_rev,eq_comm] }

    lemma concat_append : append v (concat l l')  = concat l (append v l')
        := by { induction l; rw [concat,concat], rw [append,l_ih] }

    lemma rev_concat (h : compat l l') : rev (concat l l') = concat (rev l') (rev l)
        := by { induction l,
            { rw [concat,rev,concat_nil], rw [last_rev], exact h.symm },
            { rw [concat,rev,l_ih h,concat_append,rev] } }

    lemma nodup_init (h : nodup l) : list.nodup (init l)
        := by { induction l, { exact list.pairwise.nil },
            { rw [init,list.nodup,list.pairwise_cons], refine ⟨_,l_ih h.2⟩,
                intros a h1 h2, replace h := h.1, rw h2 at h, exact h (mem_init h1) } }

    lemma nodup_of_init : list.nodup (init l) -> last l ∉ init l -> nodup l
        := by { induction l, { intros, trivial },
            { rw [init,last,nodup,list.nodup_cons,list.mem_cons_iff], push_neg,
                rintros ⟨h1,h2⟩ ⟨h3,h4⟩, refine ⟨_,l_ih h2 h4⟩,
                rw mem_init_last, push_neg, exact ⟨h1,h3.symm⟩ } }

    lemma size_append : size (append v l) = size l + 1
        := by { induction l, refl, rw [append,size,l_ih,size] }

    lemma size_rev : size l.rev = size l
        := by { induction l, refl, rw [rev,size_append,l_ih,size], }

    lemma size_map {f : V -> W} {l : llist V} : size (map f l) = size l
        := by { induction l, refl, rw [map,size,l_ih,size] }

    lemma head_map {f : V -> W} {l : llist V} : head (map f l) = f (head l)
        := by { cases l; refl }

    lemma last_map {f : V -> W} {l : llist V} : last (map f l) = f (last l)
        := by { induction l, refl, rwa [map,last,last] }
end end llist

@[ext] structure llist' (V : Type) (x y : V) := (l : llist V) (hx : l.head = x) (hy : l.last = y)
instance {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' open llist
    variables {V : Type} (adj : V -> V -> Prop) {x y z : V}

    instance : has_mem V (llist' V x y) := ⟨λ v l, v ∈ l.l⟩

    def pt   (v : V)                    : llist' V v v := ⟨pt v,     rfl, rfl⟩
    def cons (v : V) (l : llist' V x y) : llist' V v y := ⟨cons v l, rfl, l.hy⟩

    lemma compat {l : llist' V x y} {l' : llist' V y z} : llist.compat l.l l'.l
        := eq.trans l.hy l'.hx.symm

    @[simp] def concat {x y z : V} (l : llist' V x y) (l' : llist' V y z) : llist' V x z
        := ⟨llist.concat l l', eq.trans (head_concat compat) l.hx, eq.trans concat_last l'.hy⟩

    @[simp] lemma concat_P {l : llist' V x y} : concat l (pt y) = l
        := by { ext, exact llist.concat_nil l.hy }
end llist'

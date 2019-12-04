import tactic

inductive llist (V : Type) : Type | P : V -> llist | L : V -> llist -> llist

@[ext] structure llist2 (V : Type) := (head : V) (tail : list V)

namespace llist section
    parameters {V W : Type} (adj : V -> V -> Prop)

    def mem : V -> llist V -> Prop | x (P v) := x = v | x (L v l) := x = v ∨ mem x l
    instance has_mem_llist : has_mem V (llist V) := ⟨mem⟩

    def to_list :             llist V -> list V  |   (P v)    := [v]       |   (L v l)    := v :: to_list l
    def size    :             llist V -> nat     |   (P _)    := 0         |   (L v l)    := (size l) + 1
    def head    :             llist V -> V       |   (P v)    := v         |   (L v l)    := v
    def tail    :             llist V -> list V  |   (P v)    := []        |   (L v l)    := l.head :: tail l
    def init    :             llist V -> list V  |   (P v)    := []        |   (L v l)    := v :: init l
    def last    :             llist V -> V       |   (P v)    := v         |   (L v l)    := last l
    def inside  :             llist V -> list V  |   (P v)    := []        |   (L v l)    := init l
    def is_path :             llist V -> Prop    |   (P v)    := true      |   (L v l)    := adj v l.head ∧ is_path l
    def append  :        V -> llist V -> llist V | x (P v)    := L v (P x) | x (L v l)    := L v (append x l)
    def rev     :             llist V -> llist V |   (P v)    := (P v)     |   (L v l)    := append v (rev l)
    def nodup   :             llist V -> Prop    |   (P v)    := true      |   (L v l)    := v ∉ l ∧ nodup l
    def concat  :  llist V -> llist V -> llist V |   (P _) l' := l'        |   (L v l) l' := L v (concat l l')
    def map     : (V -> W) -> llist V -> llist W | f (P v)    := P (f v)   | f (L v l)    := L (f v) (map f l)
    
    @[simp] def compat (l₁ l₂ : llist V) := last l₁ = head l₂

    variables {x y v w : V} {l l' l'' : llist V}

    @[simp] lemma concat_head    (h : compat l l') : head (concat l l')       = head l
        := by { cases l, { rw compat at h, rw [concat,<-h], refl }, { refl } }

    @[simp] lemma concat_last                      : last (concat l l')       = last  l'
        := by { induction l; rw concat, rwa [last] }

    @[simp] lemma append_head                      : head (append v l)        = head l
        := by { cases l; refl }

    @[simp] lemma append_last                      : last (append v l)        = v
        := by { induction l, refl, rwa [append,last] }

    @[simp] lemma rev_append                       : rev  (append v l)        = L v (rev l)
        := by { induction l, refl, rw [append,rev,l_ih], refl }

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
            { tauto },
            { rw [concat,is_path,hr h,is_path,concat_head], tauto, exact h } }

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

    lemma         mem_init_inside'                 : x ∈ init (L v l)       <-> x = v ∨ x ∈ inside (L v l)
        := by { rw [init,inside,list.mem_cons_iff] }

    lemma         mem_init_inside (h : 0 < size l) : x ∈ init l             <-> x = head l ∨ x ∈ inside l
        := by { rw [<-(list_head_init h),list.mem_cons_iff] }

    lemma         mem_tail_inside'                 : x ∈ tail (L v l)       <-> x ∈ inside (L v l) ∨ x = last l
        := by { rw [inside,<-mem_init_last,tail,mem_head_tail], trivial }

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

    lemma         nodup_of_init : list.nodup (init l) -> last l ∉ init l -> nodup l
        := by { induction l, { intros, trivial },
            { rw [init,last,nodup,list.nodup_cons,list.mem_cons_iff], push_neg, 
                rintros ⟨h1,h2⟩ ⟨h3,h4⟩, refine ⟨_,l_ih h2 h4⟩,
                rw mem_init_last, push_neg, exact ⟨h1,h3.symm⟩ } }
end end llist

namespace llist section
    parameters {V W : Type}

    lemma head_map {f : V -> W} {l : llist V} : head (map f l) = f (head l)
        := by { cases l; refl }

    lemma last_map {f : V -> W} {l : llist V} : last (map f l) = f (last l)
        := by { induction l, refl, rwa [map,last,last] }
end end llist

namespace llist2 section
    parameters {V W : Type} (adj : V -> V -> Prop)

    lemma cases_on' {C : llist2 V → Prop} (l : llist2 V)
                (h0 : ∀ {x}, C ⟨x,[]⟩) (h1 : ∀ {x y ys}, C ⟨x,y::ys⟩) : C l 
        := cases_on l (λ x l, list.cases_on l h0 (λ _ _, h1))

    lemma induction_on {C : llist2 V → Prop} (l : llist2 V) 
                (h0 : ∀ x, C ⟨x,[]⟩) (h1 : ∀ {x y ys} (hr : C ⟨y,ys⟩), C ⟨x,y::ys⟩) : C l 
        := cases_on l (λ x l, list.rec h0 (λ y l hr x, h1 (hr y)) l x)

    def mem (x : V) (l : llist2 V) : Prop := x = l.head ∨ x ∈ l.tail

    instance : has_mem V (llist2 V) := ⟨mem⟩
    instance : has_well_founded (llist2 V) := ⟨_, measure_wf ((λ n, n+n) ∘ list.length ∘ llist2.tail)⟩
    instance : has_sizeof (llist2 V) := ⟨λ l, list.length l.tail⟩

    def to_list (l : llist2 V) : list V := l.head :: l.tail
    
    def from_list : Π (l : list V), l ≠ [] -> llist2 V
        | [] h := absurd rfl h
        | (x::l) _ := ⟨x,l⟩

    lemma ne_nil {l : llist2 V} : to_list l ≠ []
        := by { trivial }

    def cons      (v : V) (l : llist2 V)                 : llist2 V := ⟨v,l.head::l.tail⟩
    def append    (v : V) (l : llist2 V)                 : llist2 V := ⟨l.head, l.tail ++ [v]⟩
    def concat            (l : llist2 V) (l' : llist2 V) : llist2 V := ⟨l.head, l.tail ++ l'.tail⟩
    def map2 (f : V -> W) (l : llist2 V)                 : llist2 W := ⟨f l.head, list.map f l.tail⟩

    def reverse : llist2 V -> llist2 V | ⟨x,[]⟩ := ⟨x,[]⟩ | ⟨x,y::l⟩ := append x (reverse ⟨y,l⟩)
    def last    : llist2 V -> V        | ⟨x,[]⟩ := x      | ⟨x,y::l⟩ := last ⟨y,l⟩
    def is_path : llist2 V -> Prop     | ⟨x,[]⟩ := true   | ⟨x,y::l⟩ := adj x y ∧ is_path ⟨y,l⟩
    def nodup   : llist2 V -> Prop     | ⟨x,[]⟩ := true   | ⟨x,y::l⟩ := x ∉ llist2.mk y l ∧ nodup ⟨y,l⟩
    def init    : llist2 V -> list V   | ⟨x,[]⟩ := []     | ⟨x,y::l⟩ := x :: init ⟨y,l⟩
    def inside  : llist2 V -> list V   | ⟨x,[]⟩ := []     | ⟨x,y::l⟩ := init ⟨y,l⟩

    @[simp] def compat (l₁ l₂ : llist2 V) := last l₁ = head l₂

    variables {x y v w : V} {l l' l'' : llist2 V} {xs ys zs : list V}

    @[simp] lemma head_concat : head (concat l l') = head l
        := rfl

    lemma last_is_last : last ⟨x,xs⟩ = list.last (to_list ⟨x,xs⟩) ne_nil
        := by { induction xs with y ys hr generalizing x,
            { simp [last,to_list] },
            { simp [last,to_list], exact hr } }

    lemma last_of_ne_nil {h : ys ≠ []} : last ⟨x,ys⟩ = list.last ys h
        := by { cases ys with y ys, contradiction, simp [last], exact last_is_last }

    lemma last_of_ne_nil' {h : ys ≠ []} : last ⟨x,xs++ys⟩ = list.last ys h
        := by { induction xs generalizing x,
            { cases ys, contradiction, simp [last], exact last_is_last },
            { simp [last], exact xs_ih } }

    @[simp] lemma last_concat (h : compat l l') : last (concat l l') = last  l'
        := by { cases l' with x' l', cases l' with y' l',
            { simp [concat,last] at h ⊢, convert h, cases l, refl },
            { simp [concat,last_of_ne_nil,last_of_ne_nil'] } }

    @[simp] lemma head_append : head (append v l) = head l
        := rfl

    @[simp] lemma last_append : last (append v l) = v
        := by { cases l with x l, simp [append,last,last_of_ne_nil'] }

    @[simp] lemma rev_append : reverse (append v l) = cons v (reverse l)
        := by { apply induction_on l; intros, refl, 
            simp [append,reverse] at hr ⊢, rw hr, finish }

    @[simp] lemma rev_head : head (reverse l) = last l
        := by { apply induction_on l; intros, refl, simp [reverse,append,hr,last] }

    @[simp] lemma rev_last : last (reverse l) = head l
        := by { apply cases_on' l; intros, refl, rw [reverse,last_append] }

    @[simp] lemma rev_rev : reverse (reverse l) = l
        := by { apply induction_on l; intros, refl, rw [reverse,rev_append,hr], refl }

    lemma mem_iff : x ∈ l <-> x = head l ∨ x ∈ tail l
        := by { trivial }

    @[simp] lemma mem_singleton : x ∈ (⟨y,[]⟩ : llist2 V) <-> x = y
        := by { simp [mem_iff] }

    @[simp] lemma mem_cons : x ∈ (⟨v,xs⟩ : llist2 V) <-> x = v ∨ x ∈ xs
        := mem_iff

    @[simp] lemma concat_path (h : compat l l') : is_path (concat l l') <-> is_path l ∧ is_path l'
        := by { revert h, apply induction_on l; intros, 
            { simp [is_path,concat,last] at h ⊢, subst h, cases l', trivial }, 
            { simp [concat,is_path] at hr h ⊢, rw [hr h,and.assoc] } }

    @[simp] lemma mem_append : w ∈ append v l <-> w = v ∨ w ∈ l
        := by { apply induction_on l; { intros, rw append, finish } }

    @[simp] lemma mem_rev : v ∈ reverse l <-> v ∈ l
        := by { apply induction_on l; intros, simp [reverse], simp [reverse,mem_append,hr] }

    @[simp] lemma mem_head : head l ∈ l
        := by { left, refl }

    @[simp] lemma mem_last : last l ∈ l
        := by { apply induction_on l; intros, { left, refl }, { right, assumption } }

    @[simp] lemma mem_list : x ∈ to_list l <-> x ∈ l
        := by { apply induction_on l; intros; simp [to_list] }

    @[simp] lemma append_nodup : nodup (append x l) <-> x ∉ l ∧ nodup l
        := by { apply induction_on l; intros, { simp [append,nodup], finish },
            { simp [nodup,append] at hr ⊢, rw hr, finish } }

    @[simp] lemma rev_nodup : nodup (reverse l) <-> nodup l
        := by { apply induction_on l; intros, { finish }, { simp [reverse,hr,nodup] } }

    @[simp] lemma append_is_path : is_path (append v l) <-> adj (last l) v ∧ is_path l
        := by { apply induction_on l; intros, { simp [append,is_path,last] }, 
            { simp [append,is_path,last] at hr ⊢, rw hr, finish } }

    @[simp] lemma init_append : init (append x l) = to_list l
        := by { apply induction_on l; intros, refl, { simp [append,init,to_list] at hr ⊢, exact hr } }

    @[simp] lemma list_head_tail : head l :: tail l = to_list l
        := rfl

    @[simp] lemma list_init_last : init l ++ [last l] = to_list l
        := by { apply induction_on l; intros, refl, rw [init,last,to_list], finish }

    @[simp] lemma list_head_init' : v :: inside (cons v l) = init (cons v l)
        := by { apply induction_on l; intros, refl, simp [cons,inside,init] }

    @[simp] lemma list_head_init (h : l.tail ≠ []) : head l :: inside l = init l
        := by { revert h, apply cases_on' l; intros, contradiction, refl }

    @[simp] lemma list_tail_last' : inside (cons v l) ++ [last (cons v l)] = tail (cons v l)
        := by { rw [cons,inside,last,list_init_last], refl }

    @[simp] lemma list_tail_last (h : l.tail ≠ []) : inside l ++ [last l] = tail l
        := by { cases l with x l, cases l, contradiction, simp [inside,last,to_list] }

    @[simp] lemma init_inside (h : l.tail ≠ []) : init l = (head l) :: inside l
        := by { revert h, apply induction_on l; intros, contradiction, simp [init,inside] }

    @[simp] lemma inside_append : inside (append x l) = tail l
        := by { apply induction_on l; intros, refl, simp [append,inside] at hr ⊢, assumption }

    @[simp] lemma tail_append : (append x l).tail = tail l ++ [x]
        := by { apply induction_on l; intros, refl, simp [append] }

    @[simp] lemma tail_rev : tail (reverse l) = list.reverse (init l)
        := by { apply induction_on l; intros, refl, simp [reverse], rw hr, simp [inside] }

    @[simp] lemma rev_inside : inside (reverse l) = list.reverse (inside l)
        := by { apply cases_on' l; intros, refl, simp [reverse,inside] } 

    @[simp] lemma rev_is_path (h : symmetric adj) : is_path (reverse l) <-> is_path l
        := by { apply induction_on l; intros, trivial, rw [reverse,append_is_path,hr], simp [is_path],
            exact and_congr ⟨@h _ _, @h _ _⟩ iff.rfl }

    @[simp] lemma mem_concat (h : compat l l') : x ∈ concat l l' <-> x ∈ l ∨ x ∈ l'
        := by { replace h : head l' ∈ l, by { rw compat at h, rw <-h, exact mem_last },
            have : x ∈ concat l l' <-> x ∈ l ∨ x ∈ l'.tail, 
                by { simp [concat,mem_iff], exact or.assoc.symm }, 
            rw [this,@mem_iff _ x l'], split; finish }

    @[simp] lemma concat_nil (h : last l = w) : concat l ⟨w,[]⟩ = l
        := by { revert h, apply cases_on' l; intros, refl, simp [concat] }

    @[simp] lemma concat_size : sizeof (concat l l') = sizeof l + sizeof l'
        := by { simp [concat,sizeof,has_sizeof.sizeof] }

    lemma concat_assoc : concat (concat l l') l'' = concat l (concat l' l'')
        := by { simp [concat] }

    lemma concat_nodup (h : compat l l') : nodup (concat l l') <-> nodup l ∧ nodup l' ∧ (∀ x, x ∈ l ∧ x ∈ l' -> x = head l')
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

    lemma         mem_init_inside'                 : x ∈ init (L v l)       <-> x = v ∨ x ∈ inside (L v l)
        := by { rw [init,inside,list.mem_cons_iff] }

    lemma         mem_init_inside (h : 0 < size l) : x ∈ init l             <-> x = head l ∨ x ∈ inside l
        := by { rw [<-(list_head_init h),list.mem_cons_iff] }

    lemma         mem_tail_inside'                 : x ∈ tail (L v l)       <-> x ∈ inside (L v l) ∨ x = last l
        := by { rw [inside,<-mem_init_last,tail,mem_head_tail], trivial }

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

    lemma         nodup_of_init : list.nodup (init l) -> last l ∉ init l -> nodup l
        := by { induction l, { intros, trivial },
            { rw [init,last,nodup,list.nodup_cons,list.mem_cons_iff], push_neg, 
                rintros ⟨h1,h2⟩ ⟨h3,h4⟩, refine ⟨_,l_ih h2 h4⟩,
                rw mem_init_last, push_neg, exact ⟨h1,h3.symm⟩ } }
end end llist2

namespace llist2 section
    parameters {V W : Type}

    lemma head_map {f : V -> W} {l : llist V} : head (map f l) = f (head l)
        := by { cases l; refl }

    lemma last_map {f : V -> W} {l : llist V} : last (map f l) = f (last l)
        := by { induction l, refl, rwa [map,last,last] }
end end llist2

@[ext] structure llist' (V : Type) (x y : V) := (l : llist V) (hx : l.head = x) (hy : l.last = y)
instance {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' section open llist
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V}

    def mem (v : V) (l : llist' V x y) := v ∈ l.l
    instance has_mem : has_mem V (llist' V x y) := ⟨mem⟩

    @[simp] lemma reduce {l hx hy} : (⟨l,hx,hy⟩ : llist' V x y).l = l := rfl

    @[simp] lemma mem_simp {v l hx hy} : v ∈ (⟨l,hx,hy⟩ : llist' V x y) <-> v ∈ l
        := by { trivial }

    def P    (v : V)                    : llist' V v v := ⟨P v,     rfl, rfl⟩
    def cons (v : V) (l : llist' V x y) : llist' V v y := ⟨L v l.l, rfl, l.hy⟩

    lemma compat {l : llist' V x y} {l' : llist' V y z} : llist.compat l.l l'.l 
        := eq.trans l.hy l'.hx.symm

    def concat {x y z : V} (l : llist' V x y) (l' : llist' V y z) : llist' V x z
        := ⟨llist.concat l l', eq.trans (concat_head compat) l.hx, eq.trans concat_last l'.hy⟩

    @[simp] lemma concat_P {l : llist' V x y} : concat l (P y) = l
        := by { ext, exact llist.concat_nil l.hy }
end end llist'

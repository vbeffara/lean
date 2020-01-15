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

    @[simp] lemma head_P : head (P v) = v := rfl

    @[simp] lemma last_P : last (P v) = v := rfl

    @[simp] lemma concat_head : compat l l' -> head (concat l l') = head l
        := llist.cases_on l (λ _ h, eq.trans h.symm rfl) (λ _ _ _, rfl)

    @[simp] lemma concat_last : last (concat l l') = last  l'
        := llist.rec (λ _, rfl) (λ _ _, id) l

    @[simp] lemma append_head : head (append v l) = head l
        := llist.cases_on l (λ _, rfl) (λ _ _, rfl)

    @[simp] lemma append_last : last (append v l) = v
        := llist.rec (λ _, rfl) (λ _ _, id) l

    @[simp] lemma rev_append : rev (append v l) = L v (rev l)
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

    lemma size_append : size (append v l) = size l + 1
        := by { induction l, refl, rw [append,size,l_ih,size] }

    lemma size_rev : size l.rev = size l
        := by { induction l, refl, rw [rev,size_append,l_ih,size], }
end end llist

namespace llist section
    parameters {V W : Type}

    lemma size_map {f : V -> W} {l : llist V} : size (map f l) = size l
        := by { induction l, refl, rw [map,size,l_ih,size] }

    lemma head_map {f : V -> W} {l : llist V} : head (map f l) = f (head l)
        := by { cases l; refl }

    lemma last_map {f : V -> W} {l : llist V} : last (map f l) = f (last l)
        := by { induction l, refl, rwa [map,last,last] }
end end llist

namespace llist2 section
    variables {V W : Type} (adj : V -> V -> Prop)

    lemma cases_on' {C : llist2 V → Prop} (l : llist2 V)
                (h0 : ∀ {x}, C ⟨x,[]⟩) (h1 : ∀ {x y ys}, C ⟨x,y::ys⟩) : C l 
        := cases_on l (λ x l, list.cases_on l h0 (λ _ _, h1))

    lemma induction_on {C : llist2 V → Prop} (l : llist2 V) 
                (h0 : ∀ x, C ⟨x,[]⟩) (h1 : ∀ {x y ys} (hr : C ⟨y,ys⟩), C ⟨x,y::ys⟩) : C l 
        := cases_on l (λ x l, list.rec h0 (λ y l hr x, h1 (hr y)) l x)

    def fold (f : V -> W) (g : V -> W -> W) (l : llist2 V) : W
        := llist2.cases_on l $ flip $ @list.rec V (λ _, V -> W) f (λ y ys φ x, g x (φ y))

    @[simp] lemma fold_init {f : V -> W} {g : V -> W -> W} {x} : fold f g ⟨x,[]⟩ = f x
        := rfl

    @[simp] lemma fold_step {f : V -> W} {g : V -> W -> W} {x y ys} : fold f g ⟨x,y::ys⟩ = g x (fold f g ⟨y,ys⟩)
        := rfl

    def fold' (f : V -> W) (g : V -> V -> W -> W) (l : llist2 V) : W
        := llist2.cases_on l $ flip $ @list.rec V (λ _, V -> W) f (λ y ys φ x, g x y (φ y))

    @[simp] lemma fold'_init {f : V -> W} {g : V -> V -> W -> W} {x} : fold' f g ⟨x,[]⟩ = f x
        := rfl

    @[simp] lemma fold'_step {f : V -> W} {g : V -> V -> W -> W} {x y ys} : fold' f g ⟨x,y::ys⟩ = g x y (fold' f g ⟨y,ys⟩)
        := rfl

    def fold'' (f : V -> W) (g : V -> llist2 V -> W -> W) (l : llist2 V) : W
        := llist2.cases_on l $ flip $ @list.rec V (λ _, V -> W) f (λ y ys φ x, g x ⟨y,ys⟩ (φ y))

    @[simp] lemma fold''_init {f : V -> W} {g : V -> llist2 V -> W -> W} {x} : fold'' f g ⟨x,[]⟩ = f x
        := rfl

    @[simp] lemma fold''_step {f : V -> W} {g : V -> llist2 V -> W -> W} {x y ys} : fold'' f g ⟨x,y::ys⟩ = g x ⟨y,ys⟩ (fold'' f g ⟨y,ys⟩)
        := rfl

    instance : has_well_founded (llist2 V) := ⟨_, measure_wf ((λ n, n+n) ∘ list.length ∘ llist2.tail)⟩

    def point (x : V) : llist2 V := ⟨x,[]⟩

    def mem     :        V -> llist2 V -> Prop     |     u ⟨x,l⟩   := u = x ∨ u ∈ l
    instance : has_mem V (llist2 V) := ⟨mem⟩

    def size    :             llist2 V -> nat      |       ⟨x,l⟩   := l.length
    def to_list :             llist2 V -> list V   |       ⟨x,l⟩   := x :: l
    def cons    :        V -> llist2 V -> llist2 V |     u ⟨x,l⟩   := ⟨u,x::l⟩
    def append  :        V -> llist2 V -> llist2 V |     u ⟨x,l⟩   := ⟨x, l ++ [u]⟩
    def concat  : llist2 V -> llist2 V -> llist2 V | ⟨x,l⟩ ⟨x',l'⟩ := ⟨x, l ++ l'⟩
    def map     : (V -> W) -> llist2 V -> llist2 W |     f ⟨x,l⟩   := ⟨f x, list.map f l⟩
    
    def reverse  : llist2 V -> llist2 V             := fold   point               append
    def last     : llist2 V -> V                    := fold   id                  (λ _, id)
    def init     : llist2 V -> list V               := fold   (λ _, [])           list.cons
    def concat'  : llist2 V -> llist2 V -> llist2 V := fold   (λ x y, ⟨x,y.tail⟩) ((∘)∘cons)
    def concat_' : llist2 V -> llist2 V -> llist2 V := fold   (λ _, id)           ((∘)∘cons)
    def is_path  : llist2 V -> Prop                 := fold'  (λ _, true)         (λ x, and ∘ adj x)
    def nodup    : llist2 V -> Prop                 := fold'' (λ _, true)         (λ x, and ∘ not ∘ (∈) x)

    def inside  : llist2 V -> list V   | ⟨x,[]⟩ := []     | ⟨x,y::l⟩ := init ⟨y,l⟩

    @[simp] def compat (l₁ l₂ : llist2 V) := last l₁ = head l₂

    variables {x y v w : V} {l l' l'' : llist2 V} {xs ys zs : list V}

    @[simp] lemma head_concat : head (concat l l') = head l
        := by { cases l, cases l', refl }

    @[simp] lemma head_cons : head (cons x l) = x 
        := by { rcases l with ⟨x,_|⟨y,ys⟩⟩; refl }

    @[simp] lemma head_concat' : head (concat' l l') = head l
        := by { rcases l with ⟨x,_|⟨y,ys⟩⟩, refl, simp [concat'] }

    @[simp] lemma last_concat (h : compat l l') : last (concat l l') = last l'
        := by { revert h, apply induction_on l; intros; cases l' with y l',
            { cases l' with z l', { exact h }, { simp [concat,last] } },
            { rw [<-hr h], simp [concat,last] } }

    @[simp] lemma head_append : head (append v l) = head l
        := by { cases l, refl }

    @[simp] lemma last_append : last (append v l) = v
        := by { apply induction_on l; intros, refl, simp [hr,append,last] at hr ⊢, exact hr }

    lemma append_cons : append w (cons v l) = cons v (append w l) 
        := by { cases l, refl }

    lemma append_cons' : append w ⟨x,y::ys⟩ = cons x (append w ⟨y,ys⟩) 
        := rfl

    lemma reverse_cons : reverse (cons v l) = append v (reverse l)
        := by { cases l, refl }

    lemma reverse_cons' : reverse ⟨x,y::ys⟩ = append x (reverse ⟨y,ys⟩)
        := rfl

    @[simp] lemma rev_append : reverse (append v l) = cons v (reverse l)
        := by { apply induction_on l; intros, refl, 
            rw [append_cons',reverse_cons,hr,reverse_cons',append_cons] }

    @[simp] lemma rev_head : head (reverse l) = last l
        := by { apply induction_on l; intros, refl, rw [reverse_cons',head_append,hr], refl }

    @[simp] lemma rev_last : last (reverse l) = head l
        := by { apply cases_on' l; intros, refl, rw [reverse_cons',last_append] }

    @[simp] lemma rev_rev : reverse (reverse l) = l
        := by { apply induction_on l; intros, refl, rw [reverse_cons',rev_append,hr], refl }

    lemma mem_iff : x ∈ l <-> x = head l ∨ x ∈ tail l
        := by { cases l, trivial }

    @[simp] lemma mem_singleton : x ∈ (⟨y,[]⟩ : llist2 V) <-> x = y
        := by { simp [mem_iff] }

    @[simp] lemma concat_path (h : compat l l') : is_path adj (concat l l') <-> is_path adj l ∧ is_path adj l'
        := by { revert h, apply induction_on l; intros, 
            { simp [is_path,concat,last] at h ⊢, subst h, cases l', trivial }, 
            { cases l', simp [concat,is_path] at hr h ⊢, rw [hr h,and.assoc] } }

    @[simp] lemma mem_append : w ∈ append v l <-> w = v ∨ w ∈ l
        := by { apply induction_on l; intros; simp [append,mem_iff,mem_iff,or.comm], finish }

    @[simp] lemma mem_rev : v ∈ reverse l <-> v ∈ l
        := by { apply induction_on l; intros, simp [reverse,point], 
            rw [reverse_cons',mem_append,hr,mem_iff,mem_iff], trivial }

    @[simp] lemma mem_head : head l ∈ l
        := by { cases l, left, refl }

    @[simp] lemma mem_last : last l ∈ l
        := by { apply induction_on l; intros, { left, refl }, { right, assumption } }

    @[simp] lemma mem_list : x ∈ to_list l <-> x ∈ l
        := by { cases l, trivial }

    lemma nodup_cons : nodup (cons v l) <-> v ∉ l ∧ nodup l
        := by { cases l, refl }

    lemma nodup_cons' : nodup ⟨x,y::ys⟩ <-> x ∉ (⟨y,ys⟩ : llist2 V) ∧ nodup ⟨y,ys⟩
        := by { convert nodup_cons, refl }

    @[simp] lemma append_nodup : nodup (append x l) <-> x ∉ l ∧ nodup l
        := by { apply induction_on l; intros,
            { simp [append,nodup,mem], exact ne_comm },
            { rw [append_cons',nodup_cons,hr,nodup_cons',mem_append], finish [mem_iff] } }

    @[simp] lemma rev_nodup : nodup (reverse l) <-> nodup l
        := by { apply induction_on l; intros, { trivial }, 
            { rw [reverse_cons',append_nodup,hr,mem_rev], trivial } }

    @[simp] lemma append_is_path : is_path adj (append v l) <-> adj (last l) v ∧ is_path adj l
        := by { apply induction_on l; intros, { simp [append,is_path,last] }, 
            { simp [append,is_path,last] at hr ⊢, rw hr, finish } }

    @[simp] lemma init_append : init (append x l) = to_list l
        := by { apply induction_on l; intros, refl, { simp [append,init,to_list] at hr ⊢, exact hr } }

    @[simp] lemma list_init_last : init l ++ [last l] = to_list l
        := by { apply induction_on l; intros, refl, rw [init,last,to_list], finish }

    @[simp] lemma list_head_init' : v :: inside (cons v l) = init (cons v l)
        := by { apply induction_on l; intros, refl, simp [cons,inside,init] }

    @[simp] lemma list_head_init (h : l.tail ≠ []) : head l :: inside l = init l
        := by { revert h, apply cases_on' l; intros, contradiction, refl }

    @[simp] lemma list_tail_last' : inside (cons v l) ++ [last (cons v l)] = tail (cons v l)
        := by { cases l, exact list_init_last }

    @[simp] lemma list_tail_last (h : l.tail ≠ []) : inside l ++ [last l] = tail l
        := by { cases l with x l, cases l, contradiction, exact list_init_last }

    @[simp] lemma init_inside (h : l.tail ≠ []) : init l = (head l) :: inside l
        := by { revert h, apply induction_on l; intros, contradiction, simp [init,inside] }

    @[simp] lemma inside_append : inside (append x l) = tail l
        := by { apply induction_on l; intros, refl, simp [append,inside] at hr ⊢, assumption }

    @[simp] lemma tail_append : (append x l).tail = tail l ++ [x]
        := by { apply induction_on l; intros, refl, simp [append] }

    lemma init_cons : init (cons v l) = v :: init l
        := by { cases l, refl }

    lemma init_cons' : init ⟨x,y::ys⟩ = x :: init ⟨y,ys⟩
        := rfl
 
    @[simp] lemma tail_rev : tail (reverse l) = list.reverse (init l)
        := by { apply induction_on l; intros, refl, 
            rw [reverse_cons',init_cons',list.reverse_cons,<-hr,tail_append] }

    @[simp] lemma rev_inside : inside (reverse l) = list.reverse (inside l)
        := by { apply cases_on' l; intros, refl, 
            rw [reverse_cons',inside_append,inside,tail_rev] } 

    @[simp] lemma rev_is_path (h : symmetric adj) : is_path adj (reverse l) <-> is_path adj l
        := by { apply induction_on l; intros, trivial, 
            rw [reverse_cons',append_is_path,hr,is_path,rev_last],
            exact and_congr ⟨@h _ _, @h _ _⟩ iff.rfl }

    @[simp] lemma mem_concat (h : compat l l') : x ∈ concat l l' <-> x ∈ l ∨ x ∈ l'
        := by { replace h : head l' ∈ l, by { rw compat at h, rw <-h, exact mem_last },
            have : x ∈ concat l l' <-> x ∈ l ∨ x ∈ l'.tail, 
                by { cases l, cases l', rw [concat,mem_iff], simp [or.assoc,mem_iff] }, 
            rw [this,@mem_iff _ x l'], split; finish }

    @[simp] lemma concat_nil (h : last l = w) : concat l ⟨w,[]⟩ = l
        := by { revert h, apply cases_on' l; intros, refl, simp [concat] }

    @[simp] lemma concat_nil' (h : w = head l) : concat ⟨w,[]⟩ l = l
        := by { subst h, cases l, refl }

    @[simp] lemma concat_size : size (concat l l') = size l + size l'
        := by { cases l, cases l', simp [concat,size] }

    lemma concat_assoc : concat (concat l l') l'' = concat l (concat l' l'')
        := by { cases l, cases l', cases l'', simp [concat] }

    lemma concat_nodup (h : compat l l') : nodup (concat l l')
                <-> nodup l ∧ nodup l' ∧ (∀ v, v ∈ l ∧ v ∈ l' -> v = head l')
        := by { revert h, apply induction_on l; intros,
            { simp [compat,last] at h, subst h, rw [concat_nil' rfl], simp [nodup] },
            { cases l, cases l', simp [concat] at *, rw [nodup_cons', hr h, nodup], clear hr, 
                simp [mem_iff], push_neg, split,
                { rintros ⟨⟨h1,h2,h3⟩,h4,h5,h6,h7⟩, refine ⟨⟨⟨h1,h2⟩,h4⟩,h5,_⟩, 
                    intros v h8 h9, cases h9, assumption,
                    cases h8, subst h8, contradiction,
                    cases h8, subst h8, apply h6, exact or.inr h9,
                    apply h7 v h8, exact or.inr h9 },
                { rintros ⟨⟨⟨h1,h2⟩,h3⟩,h4,h5⟩, refine ⟨⟨h1,h2,_⟩,h3,h4,_,_⟩,
                    { intro h7, have h6 := h5 x (or.inl rfl) (or.inr h7), subst h6,
                        revert h4 h7, cases l'_tail; intros, cases h7, 
                        simp at h4, apply h4.1, simp at h7, exact h7 },
                    { exact h5 y (or.inr (or.inl rfl)) },
                    { intros x, exact h5 x ∘ or.inr ∘ or.inr } } } }

    lemma mem_init (h : x ∈ init l) : x ∈ l
        := by { revert h, apply induction_on l; intros; cases h, exact or.inl h, exact or.inr (hr h) }

    lemma mem_head_init (h : l.tail ≠ []) : head l ∈ init l
        := by { revert h, apply cases_on' l; intros, simp at h, contradiction, left, refl }

    lemma mem_last_tail (h : l.tail ≠ []) : last l ∈ tail l
        := by { revert h, apply induction_on l; intros, simp at h, contradiction,
            cases ys, { left, refl }, { right, rw [last], apply hr, trivial } }

    lemma mem_tail : x ∈ tail l -> x ∈ l
        := by { rw mem_iff, exact or.inr }

    lemma last_cons : last (cons v l) = last l
        := by { cases l, refl }

    lemma last_cons' : last ⟨x,y::ys⟩ = last ⟨y,ys⟩
        := rfl

    lemma mem_init_last : x ∈ l <-> x ∈ init l ∨ x = last l
        := by { apply induction_on l; intros, simp [init,last], 
            rw [init_cons',list.mem_cons_iff,last_cons',or.assoc,<-hr], trivial }

    lemma mem_init_inside' : x ∈ init (cons v l) <-> x = v ∨ x ∈ inside (cons v l)
        := by { cases l, rw [init_cons,cons,inside,list.mem_cons_iff] }

    lemma mem_init_inside (h : l.tail ≠ []) : x ∈ init l <-> x = head l ∨ x ∈ inside l
        := by { rw [<-(list_head_init h),list.mem_cons_iff] }

    lemma mem_tail_inside' : x ∈ tail (cons v l) <-> x ∈ inside (cons v l) ∨ x = last l
        := by { cases l with u l, rw [cons,inside,<-mem_init_last], simp [mem_iff] }

    lemma mem_tail_inside (h : l.tail ≠ []) : x ∈ tail l <-> x ∈ inside l ∨ x = last l
        := by { rw [<-(list_tail_last h),list.mem_append_eq,list.mem_singleton] }

    lemma nodup_mem_head (h : nodup l) : head l ∉ tail l
        := by { revert h, apply cases_on' l; intros, simp, exact h.1 }

    lemma nodup_mem_last (h : nodup l) : last l ∉ init l
        := by { revert h, apply induction_on l; intros,
            { simp [last,init] },
            { rw [last_cons',init_cons',list.mem_cons_iff], push_neg, refine ⟨λ a, _, hr h.2⟩, 
                apply h.1, convert mem_last, exact a.symm } }

    lemma rev_compat : compat l l' <-> compat l'.reverse l.reverse
        := by { rw [compat,compat,rev_last,rev_head,eq_comm] }

    lemma concat_append : append v (concat l l')  = concat l (append v l')
        := by { cases l, cases l', simp [append,concat] } 

    lemma rev_concat (h : compat l l') : reverse (concat l l') = concat (reverse l') (reverse l)
        := by { revert h, apply induction_on l; intros,
            { simp [last] at h, subst h, cases l', 
                simp [reverse,point], rw [concat_nil], exact rev_last, },
            { replace hr := hr h, cases l', rw [reverse_cons',<-concat_append,<-hr], simp [concat,reverse] } }

    lemma nodup_init (h : nodup l) : list.nodup (init l)
        := by { revert h, apply induction_on l; intros, simp [init],
            rw [init_cons',list.nodup,list.pairwise_cons], exact ⟨λ u h1 h2, (h2 ▸ h.1) (mem_init h1), hr h.2⟩ }

    lemma nodup_of_init : list.nodup (init l) -> last l ∉ init l -> nodup l
        := by { apply induction_on l; intros, { trivial },
            { rw [nodup], 
                rw [init_cons',list.nodup_cons] at a, cases a with h3 h4,
                rw [last_cons',init_cons',list.mem_cons_iff] at a_1, push_neg at a_1, cases a_1 with h1 h2,
                refine ⟨_, hr h4 h2⟩,
                { simp, rw mem_init_last, push_neg, exact ⟨h3, λ h, h1 h.symm⟩ } } }

    lemma head_map {f : V -> W} {l : llist2 V} : head (map f l) = f (head l)
        := by { cases l, refl }

    lemma last_map {f : V -> W} {l : llist2 V} : last (map f l) = f (last l)
        := by { apply induction_on l; intros, refl, simp [map,last], exact hr }

    lemma size_append : size (append v l) = size l + 1
        := by { apply induction_on l; intros,
            { refl },
            { simp [append,size] } }

    lemma size_reverse : size l.reverse = size l
        := by { apply induction_on l; intros,
            { refl },
            { rw [reverse_cons',size_append], rw hr, refl } }
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

structure llist2' (V : Type) (x y : V) := (l : llist2 V) (hx : l.head = x) (hy : l.last = y)
instance {V : Type} {x y : V} : has_coe (llist2' V x y) (llist2 V) := ⟨llist2'.l⟩

namespace llist2' section open llist2
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V}

    def mem (v : V) (l : llist2' V x y) := v ∈ l.l
    instance has_mem : has_mem V (llist2' V x y) := ⟨mem⟩

    @[ext] lemma ext {l l' : llist2' V x y} : l.l = l'.l -> l = l'
        := by { cases l, cases l', simp }

    @[simp] lemma reduce {l hx hy} : (⟨l,hx,hy⟩ : llist2' V x y).l = l := rfl

    @[simp] lemma mem_simp {v l hx hy} : v ∈ (⟨l,hx,hy⟩ : llist2' V x y) <-> v ∈ l
        := by { trivial }

    def P    (v : V)                     : llist2' V v v := ⟨⟨v,[]⟩, rfl, rfl⟩
    def cons (v : V) (l : llist2' V x y) : llist2' V v y := ⟨cons v l.l, head_cons, by { rw last_cons, exact l.hy } ⟩

    lemma compat {l : llist2' V x y} {l' : llist2' V y z} : llist2.compat l.l l'.l 
        := eq.trans l.hy l'.hx.symm

    def concat {x y z : V} (l : llist2' V x y) (l' : llist2' V y z) : llist2' V x z
        := ⟨llist2.concat l l', eq.trans head_concat l.hx, eq.trans (last_concat compat) l'.hy⟩

    @[simp] lemma concat_P {l : llist2' V x y} : concat l (P y) = l
        := by { apply ext, exact concat_nil l.hy }
end end llist2'

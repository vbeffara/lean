import tactic

inductive llist (V : Type) : Type | P : V -> llist | L : V -> llist -> llist

namespace llist section
    parameters {V : Type} (adj : V -> V -> Prop)

    def mem : V -> llist V -> Prop | x (P v) := x = v | x (L v l) := x = v ∨ mem x l
    instance has_mem_llist : has_mem V (llist V) := ⟨mem⟩

    def to_list : llist V -> list V | (P v) := [v] | (L v l) := v :: to_list l
    instance llist_to_list : has_coe (llist V) (list V) := ⟨to_list⟩

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

    variables {x y v w : V} {l l' l'' : llist V}

    @[simp] lemma head_P                          : head (P x)              = x
        := rfl

    @[simp] lemma head_cons                       : head (L v l)            = v
        := rfl

    @[simp] lemma last_P                          : last (P x)              = x
        := rfl

    @[simp] lemma concat_head   (h : compat l l') : head (concat l l')      = head l
        := by { cases l; simp [head,last,concat], exact h.symm }

    @[simp] lemma concat_last                     : last (concat l l')      = last  l'
        := by { induction l; finish [concat, last] }

    @[simp] lemma append_head                     : head (append v l)       = head l
        := by { cases l; finish }

    @[simp] lemma append_last                     : last (append v l)       = v
        := by { induction l; finish }

    @[simp] lemma rev_append                      : rev  (append v l)       = L v (rev l)
        := by { induction l; finish [append, rev] }

    @[simp] lemma rev_head                        : head (rev l)            = last l
        := by { induction l; finish [rev] }

    @[simp] lemma rev_last                        : last (rev l)            = head l
        := by { induction l; finish [rev] }

    @[simp] lemma rev_rev                         : rev  (rev l)            = l
        := by { induction l; finish [rev] }

    @[simp] lemma mem_singleton                   : x ∈ P y               <-> x = y
        := iff.rfl

    @[simp] lemma mem_cons                        : x ∈ L v l             <-> x = v ∨ x ∈ l
        := iff.rfl

    @[simp] lemma concat_path   (h : compat l l') : is_path (concat l l') <-> is_path l ∧ is_path l'
        := by { induction l with v v l hr; simp [concat,is_path], simp [last] at h, rw [concat_head h, hr h], tauto }

    @[simp] lemma mem_append                      : w ∈ append v l        <-> w = v ∨ w ∈ l
        := by { induction l; finish [append] }

    @[simp] lemma mem_rev                         : v ∈ rev l             <-> v ∈ l
        := by { induction l; finish [rev] }

    @[simp] lemma mem_head                        : head l ∈ l
        := by { cases l; simp [head] }

    @[simp] lemma mem_last                        : last l ∈ l
        := by { induction l; finish }

    @[simp] lemma append_nodup                    : nodup (append x l)    <-> x ∉ l ∧ nodup l
        := by { induction l; finish [append, nodup] }

    @[simp] lemma append_is_path                  : is_path (append v l)  <-> adj (last l) v ∧ is_path l
        := by { induction l; finish [is_path, append] }

    @[simp] lemma rev_nodup                       : nodup (rev l)         <-> nodup l
        := by { induction l; finish [rev, nodup] }

    @[simp] lemma rev_is_path (h : symmetric adj) : is_path (rev l)       <-> is_path l
        := by { induction l; simp [rev, is_path], tidy }

    @[simp] lemma mem_concat    (h : compat l l') : x ∈ concat l l'       <-> x ∈ l ∨ x ∈ l'
        := by { induction l with v v l hr, refine ⟨or.inr, _⟩, simp, finish [compat, concat, last], finish [concat] }

    @[simp] lemma concat_nil     (h : last l = w) : concat l (P w)          = l
        := by { induction l; rw concat, { simp, exact h.symm }, finish }

    @[simp] lemma concat_nil2                     : concat (P w) l          = l
        := rfl

    lemma concat_assoc : concat (concat l l') l'' = concat l (concat l' l'')
        := by { induction l with v v l hr; simp [concat], exact hr }

    lemma concat_nodup (h : compat l l') : nodup (concat l l') <-> nodup l ∧ nodup l' ∧ (∀ x, x ∈ l ∧ x ∈ l' -> x = head l')
        := by { induction l with v v l hr,
            { rw compat at h, finish [nodup, last] },
            { simp [nodup, concat], simp [last] at h, rw [hr h], split,
                { rintros ⟨h1,h2,h3,h4⟩, rw mem_concat h at h1, push_neg at h1, refine ⟨⟨h1.1,h2⟩,h3,_⟩,
                    rintros x h6 h7, cases h6,
                    { subst h6, cases h1.2 h7 },
                    { exact h4 x ⟨h6,h7⟩ } },
                { rintros ⟨⟨h1,h2⟩,h3,h4⟩, rw mem_concat h, push_neg, refine ⟨⟨h1,_⟩,h2,h3,_⟩,
                    { intro h5, have h6 := h4 v (or.inl rfl) h5, subst h6, rw <-h at h1, exact (h1 mem_last) },
                    { rintros x ⟨h5,h6⟩, exact h4 x (or.inr h5) h6, } } } }

    lemma mem_iff : l = l' -> (x ∈ l <-> x ∈ l')
        := by { intro h, rw h }
end end llist

structure llist' (V : Type) (x y : V) := (l : llist V) (hx : x = l.head) (hy : l.last = y)
instance llist'_to_llist {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' section open llist
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V}

    def P    (v : V)                    : llist' V v v := ⟨P v,     rfl, rfl⟩
    def cons (v : V) (l : llist' V x y) : llist' V v y := ⟨L v l.l, rfl, l.hy⟩

    @[simp] lemma head   {l : llist' V x y}                     : l.l.head = x          := l.hx.symm
    @[simp] lemma last   {l : llist' V x y}                     : l.l.last = y          := l.hy

    lemma compat {l : llist' V x y} {l' : llist' V y z} : llist.compat l.l l'.l := by simp [compat]

    def concat {x y z : V} (l : llist' V x y) (l' : llist' V y z) : llist' V x z
        := ⟨llist.concat l.l l'.l, eq.trans l.hx (concat_head compat).symm, eq.trans concat_last l'.hy⟩

    @[simp] lemma concat_P {l : llist' V x y} {hx' hy'} : concat l ⟨llist.P y, hx', hy'⟩ = l
        := by { rcases l with ⟨l,hx,hy⟩, subst hx, subst hy, rw concat, simp }


    @[extensionality] lemma eq {l l' : llist' V x y} : l.l = l'.l -> l = l'
        := by { cases l, cases l', simp }
end end llist'

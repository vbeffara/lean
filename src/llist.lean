import tactic

inductive llist (V : Type) : Type | P : V -> llist | L : V -> llist -> llist

namespace llist section
    parameters {V : Type} (adj : V -> V -> Prop)

    def mem : V -> llist V -> Prop | x (P v) := x = v | x (L v l) := x = v ∨ mem x l
    instance has_mem_llist : has_mem V (llist V) := ⟨mem⟩

    def to_list : llist V -> list V | (P v) := [v] | (L v l) := v :: to_list l
    instance llist_to_list : has_coe (llist V) (list V) := ⟨to_list⟩

    def head    :           llist V -> V       |     (P v) := v         |     (L v l) := v
    def tail    :           llist V -> list V  |     (P v) := []        |     (L v l) := l.head :: tail l
    def init    :           llist V -> list V  |     (P v) := []        |     (L v l) := v :: init l
    def last    :           llist V -> V       |     (P v) := v         |     (L v l) := last l
    def inside  :           llist V -> list V  |     (P v) := []        |     (L v l) := init l
    def is_path :           llist V -> Prop    |     (P v) := true      |     (L v l) := adj v l.head ∧ is_path l
    def append  :      V -> llist V -> llist V |   x (P v) := L v (P x) |   x (L v l) := L v (append x l)
    def rev     :           llist V -> llist V |     (P v) := (P v)     |     (L v l) := append v (rev l)
    def mem2    : V -> V -> llist V -> Prop    | _ _ (P v) := false     | x y (L v l) := (x = v ∧ y ∈ l) ∨ mem2 x y l

    @[simp] def nodup   :           llist V -> Prop    |     (P v) := true      |     (L v l) := ¬ (mem v l) ∧ nodup l

    @[simp] def compat (l₁ l₂ : llist V) := last l₁ = head l₂

    @[simp] def concat : Π (l₁ l₂) (h : compat l₁ l₂), llist V
        | (P _)   l₂ _ := l₂
        | (L v l) l₂ h := L v (concat l l₂ h)

    variables {x y v w : V} {l l' : llist V}

    @[simp] lemma concat_head (h) : head (concat l l' h)  = head l               := by { induction l; finish [h.symm] }
    @[simp] lemma concat_last (h) : last  (concat l l' h) = last  l'             := by { induction l; finish [last] }
    @[simp] lemma append_head     : head (append v l)     = head l               := by { induction l; finish }
    @[simp] lemma append_last     : last  (append v l)    = v                    := by { induction l; finish }
    @[simp] lemma rev_append      : rev   (append v l)    = L v (rev l)          := by { induction l; finish [append, rev] }
    @[simp] lemma rev_head        : head (rev l)          = last l               := by { induction l; finish [rev] }
    @[simp] lemma rev_last        : last  (rev l)         = head l               := by { induction l; finish [rev] }
    @[simp] lemma rev_rev         : rev   (rev l)         = l                    := by { induction l; finish [rev] }

    @[simp] lemma mem_singleton   : mem x (P y)             <-> x = y                  := iff.rfl
    @[simp] lemma mem_cons        : mem x (L v l)           <-> x = v ∨ mem x l        := iff.rfl
    @[simp] lemma concat_path (h) : is_path (concat l l' h) <-> is_path l ∧ is_path l' := by { induction l; finish [is_path] }
    @[simp] lemma mem_append      : mem w (append v l)      <-> w = v ∨ mem w l        := by { induction l; finish [append] }
    @[simp] lemma mem_rev         : mem v (rev l)           <-> mem v l                := by { induction l; finish [rev] }
    @[simp] lemma mem_head        : mem (head l) l                                     := by { cases l; simp [head] }
    @[simp] lemma mem_last        : mem (last l) l                                     := by { induction l; finish }

    lemma mem2_nodup : nodup l <-> ¬ ∃ x, mem2 x x l
        := by { induction l with v v l hr, simp [mem2], split; simp; intro h1,
            { rintros h2 x h, cases h with h h, exact h1 (h.1 ▸ h.2), exact hr.mp h2 ⟨x,h⟩ },
            { exact ⟨λ h, h1 v (or.inl ⟨rfl, h⟩), hr.mpr (λ ⟨x,h⟩, h1 x (or.inr h))⟩ } }

    lemma mem2_nodup' : ¬ nodup l <-> ∃ x, mem2 x x l
        := by { induction l with v v l hr, simp [mem2], unfold nodup, push_neg, split; intro h1,
            { cases h1 with h1 h1, exact ⟨v, or.inl ⟨rfl,h1⟩⟩, { cases (hr.mp h1) with u hu, exact ⟨u, or.inr hu⟩ } },
            { cases h1 with x h2, cases h2 with h2 h2, exact or.inl (h2.1 ▸ h2.2), exact or.inr (hr.mpr ⟨x, h2⟩) } }

    @[simp] lemma append_nodup  : nodup (append x l)           <-> ¬ mem x l ∧ nodup l
        := by { induction l with v v l hr; simp, simp[append], exact ne_comm, push_neg, split; rintro ⟨h1,h2⟩,
            { have h4 := hr.mp h2, simp at h1, push_neg at h1, exact ⟨⟨h1.1 ∘ eq.symm, h4.1⟩, h1.2, h4.2⟩ },
            { simp [append], push_neg, exact ⟨⟨h1.1 ∘ eq.symm, h2.1⟩, hr.mpr ⟨h1.2, h2.2⟩⟩ } }

    @[simp] lemma append_is_path : is_path (append v l) <-> adj (last l) v ∧ is_path l
        := by { induction l; finish [is_path, append] }

    @[simp] lemma rev_nodup     : nodup (rev l)                    <-> nodup l
        := by { induction l with v v l hr; finish [rev] }

    @[simp] lemma rev_is_path (h : symmetric adj) : is_path (rev l) <-> is_path l
        := by { induction l with v v l hr; simp [rev], split; intro; finish [h a.1, is_path] }

    @[simp] lemma mem_concat (h) : mem x (concat l l' h) <-> mem x l ∨ mem x l'
        := by { induction l with v v l hr, refine ⟨or.inr, _⟩, simp, finish [last], finish }

    @[simp] lemma concat_nil (h) : concat l (P w) h = l
        := by { induction l with v v l hr; simp *, simp at h, exact h.symm }

    lemma concat_nodup (h) : nodup (concat l l' h) <-> nodup l ∧ nodup l' ∧ (∀ x, x ∈ l ∧ x ∈ l' -> x = head l') := by {
        induction l with v v l hr; simp,
            { tidy },
            { rw (hr h), simp at h, refine ⟨_,_⟩,
                { rintros ⟨h1,h2,h3,h4⟩, refine ⟨⟨_,h2⟩,h3,_⟩, finish, { rintros x h6, cases h6 with h6 h6; finish } },
                { rintros ⟨⟨h11,h12⟩,h2,h3⟩, refine ⟨_,h12,h2,_⟩,
                    { intro h4, apply h11, cases h4 with h5 h5,
                        { exact h5 },
                        { convert mem_last, have h6 := h3 v (or.inl rfl) h5, finish [last] } },
                    { rintros x ⟨h4,h5⟩, exact h3 x (or.inr h4) h5 } } }
    }
end end llist

structure llist' (V : Type) (x y : V) := (l : llist V) (hx : x = l.head) (hy : l.last = y)
instance llist'_to_llist {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' section open llist
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V}

    @[simp] lemma head  {l : llist' V x y}                     : l.l.head = x         := l.hx.symm
    @[simp] lemma last   {l : llist' V x y}                     : l.l.last  = y         := l.hy
    @[simp] lemma compat {l : llist' V x y} {l' : llist' V y z} : llist.compat l.l l'.l := by simp

    @[simp] def concat {x y z : V} (l : llist' V x y) (l' : llist' V y z) : llist' V x z
        := { l := llist.concat l.l l'.l compat, hx := by simp, hy := by simp }
end end llist'

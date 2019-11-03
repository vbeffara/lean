import tactic

def llist (V : Type) : Type := V × list V

@[simp] def to_list {V : Type} (l : llist V) : list V := l.fst :: l.snd

instance llist_wf      {V} : has_well_founded (llist V) := ⟨_, measure_wf (λ l, l.snd.length + l.snd.length)⟩
instance llist_to_list {V} : has_coe (llist V) (list V) := ⟨to_list⟩

namespace llist section
    parameters {V : Type} (adj : V -> V -> Prop)
    variables (v : V)

    @[simp] def mem    : llist V -> Prop    | (x,xs) := v = x ∨ v ∈ xs
    @[simp] def first  : llist V -> V       | (x,xs) := x
    @[simp] def last   : llist V -> V       | (x,xs) := list.last (x::xs) (list.cons_ne_nil _ _)
    @[simp] def tail   : llist V -> list V  | (x,xs) := xs
    @[simp] def cons   : llist V -> llist V | (x,xs) := ⟨v, x::xs⟩
    @[simp] def append : llist V -> llist V | (x,xs) := ⟨x, xs ++ [v]⟩
    @[simp] def inside : llist V -> list V  | (x,xs) := list.init xs
    @[simp] def simple : llist V -> Prop    | (x,xs) := ¬ x ∈ xs ∧ list.nodup xs

    @[simp] def is_path :           llist V -> Prop    |     (v,[]) := true   |     (v,w::l) := adj v w ∧ is_path (w,l)
    @[simp] def rev     :           llist V -> llist V |     (v,[]) := (v,[]) |     (v,w::l) := append v (rev (w,l))
    @[simp] def mem2    : V -> V -> llist V -> Prop    | _ _ (v,[]) := false  | x y (v,w::l) := (x = v ∧ y ∈ (w::l)) ∨ mem2 x y (w,l)

    @[simp] instance has_mem_llist : has_mem V (llist V) := ⟨mem⟩

    @[simp] def compat (l₁ l₂ : llist V)                    : Prop    := last l₁ = first l₂
    @[simp] def concat (l₁ l₂ : llist V) (h : compat l₁ l₂) : llist V := (l₁.fst, l₁.snd ++ l₂.snd)

    variables {x y w : V} {vs : list V} {l l₁ l₂ : llist V}

    @[simp] lemma mem_first           : first l ∈ l
        := by { cases l, simp, left, refl }

    @[simp] lemma mem_last            : last l ∈ l
        := by { cases l with v l, revert v, induction l with w l hr; intros, simp, exact or.inl rfl, tidy, finish }

    @[simp] lemma append_first        : first (append v l)           =  first l
        := by { simp }

    @[simp] lemma concat_nil      (h) : concat (x,[]) l₂ h           =  l₂
        := by { tidy }

    @[simp] lemma concat_nil'     (h) : concat l₁ (y,[]) h           =  l₁
        := by { simp }

    @[simp] lemma concat_first    (h) : first (concat l₁ l₂ h)       =  first l₁
        := by { simp }

    @[simp] lemma concat_last     (h) : last  (concat l₁ l₂ h)       =  last  l₂
        := by { cases l₁ with v l, revert v, induction l with w l, tidy }

    @[simp] lemma append_last         : last  (append v l)           =  v
        := by { cases l with u l, revert u, induction l with x l hr; intro u; simp }

    @[simp] lemma rev_append          : rev   (append v l)           =  cons v (rev l)
        := by { cases l with u l, revert u, induction l with x l hr; intro u, simp, finish }

    @[simp] lemma rev_first           : first (rev l)                =  last l
        := by { cases l with u l, revert u, induction l with x l hr; intro u, simp, simp, exact hr x }

    @[simp] lemma rev_last            : last  (rev l)                =  first l
        := by { cases l with u l, revert u, induction l with x l hr; intro u; simp }

    @[simp] lemma rev_rev             : rev   (rev l)                =  l
            := by { cases l with u l, revert u, induction l with x l hr; intro u, simp, unfold rev, rw rev_append, rw hr x, simp }

    @[simp] lemma mem_singleton       : llist.mem x (y,[])          <-> x = y
        := by { simp }

    @[simp] lemma mem_cons            : llist.mem x (v,vs)          <-> x = v ∨ x ∈ vs
        := iff.rfl

    @[simp] lemma concat_path_iff (h) : is_path (concat l₁ l₂ h)    <-> is_path l₁ ∧ is_path l₂
        := by { cases l₁ with v l, revert v, induction l with w l hr; intros, simp, have h1 := hr w h, finish }
    @[simp] lemma mem_append          : w ∈ (append v l)            <-> w = v ∨ w ∈ l
        := by { cases l with u l, revert u, induction l with x l hr; intro, tidy, finish, finish }

    @[simp] lemma mem_rev             : v ∈ rev l                   <-> v ∈ l
        := by { cases l with u l, revert u, induction l with x l hr; intro u, refl, unfold rev, rw [mem_append,hr x], exact iff.rfl }

    @[simp] lemma mem2_simple         : ¬ (∃ x, mem2 x x l)         <-> simple l
        := by { cases l with u l, simp, revert u, induction l with v l hr; intro; simp, have hrv := hr v, split,
            intro h2, split,
                have h4 := (not_or_distrib.mp (h2 u)).1, rw [eq_true_intro rfl, true_and] at h4, exact h4,
                exact hrv.mp (λ x, (not_or_distrib.mp (h2 x)).2),
            rintros ⟨h2,h3⟩ x, rw not_or_distrib, split, rintros ⟨h5,h6⟩, exact h2 (h5 ▸ h6), exact (hrv.mpr h3) x }

    @[simp] lemma mem2_simple'        : ¬ simple l                  <-> ∃ x, mem2 x x l
        := by { sorry }

    @[simp] lemma append_simple       : v ∉ l ∧ simple l            <-> simple (append v l)
        := by {
        induction l with w w l hr, finish,
        simp, push_neg, simp, intros h1 h2 h3 h4, refine ⟨_, hr h2 h4⟩,
        intro h5, cases (mem_append.mp h5), exact h1 h.symm, exact h3 h
        }

    @[simp] lemma append_is_path      : is_path l ∧ adj (last l) v  <-> is_path (append v l)
        := by { induction l; finish }

    @[simp] lemma rev_simple          : simple l                     -> simple (rev l)
        := by { induction l; finish }

    lemma rev_is_path (h : symmetric adj) : is_path l -> is_path (rev l)
        := by { induction l, simp, intros, finish [h a.1] }

    @[simp] lemma mem_concat (h) : v ∈ concat l₁ l₂ h <-> v ∈ l₁ ∨ v ∈ l₂ := by {
        cases l₁ with v₁ l₁, cases l₂ with v₂ l₂, 
    }

    lemma concat_simple : simple (concat l₁ l₂ h) <-> simple l₁ ∧ simple l₂ ∧ (∀ v, v ∈ l₁ ∧ v ∈ l₂ -> v = first l₂) := by {
        split; induction l₁ with v v l hr,
        { simp at h, simp [h] },
        { simp *, intros h1 h2,
            push_neg at h1, cases h1 with h4 h5, rcases hr h h2 with ⟨h7,h8,h9⟩, refine ⟨⟨h4,h7⟩,h8,_⟩,
            rintros v1 h10 h, cases h10 with h10 h10, exact false.rec _ (h5 (h10 ▸ h)), exact h9 v1 ⟨h10,h⟩
        },
        { simp at h, simp [h] },
        { simp at h, rintro ⟨h1,h2,h3⟩, split,
            { intro h4, apply h1.1, cases (mem_concat h).mp h4 with h5 h5,
                exact h5, exact (h3 v ⟨or.inl rfl,h5⟩).symm ▸ h ▸ mem_last },
            { apply hr, exact ⟨h1.2, h2, λ v1 h, h3 v1 ⟨or.inr h.1,h.2⟩⟩ } } }
end end llist

structure llist' (V : Type) (x y : V) := (l : llist V) (hx : x = l.first) (hy : l.last = y)
instance llist'_to_llist {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' section open llist
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V} (l l₁ : llist' V x y) (l₂ : llist' V y z)

    @[simp] lemma first : llist.first (l : llist V) = x := by { exact l.hx.symm }

    @[simp] def concat : llist' V x z :=
        let h := eq.trans l₁.hy l₂.hx
        in ⟨llist.concat l₁ l₂ h, eq.trans l₁.hx (concat_first h).symm, eq.trans (concat_last h) l₂.hy⟩

    @[simp] def inner (v) := @llist.inner V l v
end end llist'

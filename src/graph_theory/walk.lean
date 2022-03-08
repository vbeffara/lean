import tactic combinatorics.simple_graph.connectivity
import graph_theory.path graph_theory.pushforward graph_theory.contraction
open classical function

namespace simple_graph

variables {V V' : Type*} [decidable_eq V] [decidable_eq V'] {f : V → V'}
variables {G G' : simple_graph V} {x y z u v w a b c : V}

structure Walk (G : simple_graph V) := {a b : V} (p : G.walk a b)

namespace Walk

variables {e : G.dart} {p q : G.Walk} {hep : e.snd = p.a} {hpq : p.b = q.a}

def nil (a : V) : G.Walk := ⟨(walk.nil : G.walk a a)⟩

@[simp] lemma nil_a : (nil a : G.Walk).a = a := rfl
@[simp] lemma nil_b : (nil b : G.Walk).b = b := rfl

def cons (e : G.dart) (p : G.Walk) (h : e.snd = p.a) : G.Walk :=
by { let h' := e.is_adj, rw h at h', exact ⟨p.p.cons h'⟩ }

def step (e : G.dart) : G.Walk := cons e (nil e.snd) rfl

def rec₀ {motive : G.Walk → Sort*} :
  (Π u, motive (Walk.nil u)) →
  (Π e p h, motive p → motive (cons e p h)) →
  Π p, motive p :=
λ h_nil h_cons ⟨p⟩, walk.rec_on p h_nil $ λ u v w h p, h_cons ⟨⟨_,_⟩,h⟩ ⟨p⟩ rfl

@[simp] lemma rec_nil {motive h_nil h_cons} :
  @rec₀ V _ G motive h_nil h_cons (nil a) = h_nil a := rfl

@[simp] lemma rec_cons {motive h_nil h_cons h} :
  @rec₀ V _ G motive h_nil h_cons (cons e p h) =
  h_cons e p h (rec₀ h_nil h_cons p) :=
begin
  rcases e with ⟨⟨u,v⟩,e⟩, rcases p with ⟨a,b,p⟩, dsimp only at h, subst v, refl
end

@[simp] lemma cons_a : (cons e p hep).a = e.fst := rfl
@[simp] lemma cons_b : (cons e p hep).b = p.b := rfl

def range (p : G.Walk) : finset V :=
p.p.support.to_finset

@[simp] lemma range_cons : (cons e p hep).range = {e.fst} ∪ p.range :=
by simpa only [range, cons, walk.support_cons, list.to_finset_cons]

@[simp] lemma range_step : (step e).range = {e.fst, e.snd} :=
by simpa only [range, step, cons, walk.support_cons, list.to_finset_cons]

@[simp] lemma range_nonempty : p.range.nonempty :=
begin
  refine rec₀ _ _ p,
  { intro u, use u, simp [range] },
  { intros e p h q, use e.fst, simp }
end

def init : G.Walk → finset V :=
rec₀ (λ v, ∅) (λ e p h q, {e.fst} ∪ q)

@[simp] lemma init_cons : (cons e p hep).init = {e.fst} ∪ p.init := rec_cons

lemma range_eq_init_union_last : p.range = p.init ∪ {p.b} :=
by { refine rec₀ _ _ p, { intro u, refl }, { rintro e p h q, simp [q] } }

def tail : G.Walk → finset V :=
rec₀ (λ v, ∅) (λ e p h q, p.range)

@[simp] lemma tail_cons : (cons e p hep).tail = p.range := rec_cons

lemma range_eq_start_union_tail : p.range = {p.a} ∪ p.tail :=
by { refine rec₀ _ _ p, { intro, refl }, { intros, simp [*] } }

def edges : G.Walk → finset G.dart :=
rec₀ (λ v, ∅) (λ e p h q, {e} ∪ q)

@[simp] lemma edges_cons : (cons e p hep).edges = {e} ∪ p.edges := rec_cons

lemma first_edge : e ∈ (cons e p hep).edges := by simp

@[simp] lemma range_a : (nil a : G.Walk).range = {a} := rfl

@[simp] lemma start_mem_range : p.a ∈ p.range :=
by { refine rec₀ _ _ p; simp }

@[simp] lemma end_mem_range : p.b ∈ p.range :=
by { refine rec₀ _ _ p, simp, rintro e p h q, simp, right, exact q }

lemma range_eq_support : p.range = p.p.support.to_finset :=
begin
  refine rec₀ _ _ p,
  { intro u, refl },
  { intros e p h q, rw [range_cons,q], ext, simpa }
end

def append_aux (p q : G.Walk) (hpq : p.b = q.a) : {w : G.Walk // w.a = p.a ∧ w.b = q.b} :=
begin
  rcases p with ⟨a,b,p⟩, rcases q with ⟨c,d,q⟩, simp only at hpq, subst c,
  refine ⟨⟨p ++ q⟩, rfl, rfl⟩,
end

def append (p q : G.Walk) (hpq : p.b = q.a) : G.Walk :=
(append_aux p q hpq).val

@[simp] lemma append_a : (append p q hpq).a = p.a :=
(append_aux p q hpq).prop.1

@[simp] lemma append_b : (append p q hpq).b = q.b :=
(append_aux p q hpq).prop.2

@[simp] lemma append_nil_left {haq : a = q.a} : append (nil a) q haq = q :=
by { subst haq, rcases q with ⟨a,b,q⟩, refl }

@[simp] lemma append_cons :
  append (cons e p hep) q hpq = cons e (append p q hpq) (by simp [hep]) :=
begin
  rcases e with ⟨⟨u,v⟩,e⟩, rcases p with ⟨a,b,p⟩, rcases q with ⟨c,d,q⟩,
  simp at hep hpq, substs a b, refl
end

@[simp] lemma range_append : (append p q hpq).range = p.range ∪ q.range :=
begin
  revert p, refine rec₀ _ _, simp,
  intros e p h q hpq, simp at hpq, specialize @q hpq, simp, rw ←q, refl
end

lemma mem_append : z ∈ (append p q hpq).p.support ↔ z ∈ p.p.support ∨ z ∈ q.p.support :=
begin
  rcases p with ⟨a,b,p⟩, rcases q with ⟨d,c,q⟩, simp at hpq, subst d,
  rw [append, append_aux], simp only [walk.mem_support_append_iff]
end

def push_step_aux (f : V → V') (e : G.dart) :
  {w : (push f G).Walk // w.a = f e.fst ∧ w.b = f e.snd} :=
begin
  by_cases f e.fst = f e.snd,
  exact ⟨Walk.nil (f e.fst), rfl, h⟩,
  exact ⟨Walk.step ⟨⟨_,_⟩,⟨h,e.fst,e.snd,rfl,rfl,e.is_adj⟩⟩, rfl, rfl⟩
end

def push_step (f : V → V') (e : G.dart) : (push f G).Walk :=
(push_step_aux f e).val

@[simp] lemma push_step_a : (push_step f e).a = f e.fst :=
(push_step_aux f e).prop.1

@[simp] lemma push_step_b : (push_step f e).b = f e.snd :=
(push_step_aux f e).prop.2

def push_Walk_aux (f : V → V') (p : G.Walk) :
  {w : (push f G).Walk // w.a = f p.a ∧ w.b = f p.b} :=
begin
  refine rec₀ _ _ p,
  { intro u, exact ⟨Walk.nil (f u), rfl, rfl⟩ },
  { intros e p h q, simp only [cons_a, cons_b],
    let ee := push_step f e,
    let ww := ee.append q.1 (by { rw [q.2.1,←h], exact push_step_b }),
    refine ⟨ww, _, _⟩, simp,
    rw [←q.2.2], exact (ee.append_aux q.1 (by { rw [q.2.1,←h], exact push_step_b })).2.2 }
end

def push_Walk (f : V → V') (p : G.Walk) : (push f G).Walk :=
(push_Walk_aux f p).val

@[simp] lemma push_Walk_a : (push_Walk f p).a = f p.a :=
 (push_Walk_aux f p).prop.1

@[simp] lemma push_Walk_b : (push_Walk f p).b = f p.b :=
 (push_Walk_aux f p).prop.2

@[simp] lemma push_nil : push_Walk f (@Walk.nil _ _ G a) = Walk.nil (f a) := rfl

lemma push_cons (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) :
  push_Walk f (p.cons e h) = Walk.append (push_step f e) (push_Walk f p) (by simp [h]) :=
by { rcases p with ⟨a,b,p⟩, rcases e with ⟨⟨u,v⟩,e⟩, simp at h, subst a, refl }

lemma push_cons_eq (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) (h' : f e.fst = f e.snd) :
  push_Walk f (p.cons e h) = push_Walk f p :=
begin
  have : push_step f e = Walk.nil (f e.fst) := by simp [push_step,push_step_aux,h'],
  rw [push_cons], simp only [this], exact append_nil_left
end

lemma push_cons_ne (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) (h' : f e.fst ≠ f e.snd) :
  push_Walk f (p.cons e h) = Walk.cons ⟨⟨_,_⟩,⟨h',e.fst,e.snd,rfl,rfl,e.is_adj⟩⟩ (push_Walk f p) (by simp [h]) :=
begin
  have : push_step f e = Walk.step ⟨⟨_,_⟩,⟨h',e.fst,e.snd,rfl,rfl,e.is_adj⟩⟩ :=
    by simp [push_step,push_step_aux,h'],
  rw [push_cons], simp [this,step]
end

lemma push_append (f : V → V') (p q : G.Walk) (hpq : p.b = q.a) :
  push_Walk f (Walk.append p q hpq) =
  Walk.append (push_Walk f p) (push_Walk f q) (by simp [hpq]) :=
begin
  revert p, refine rec₀ (by simp) _,
  intros e p h ih hpq, by_cases h' : f e.fst = f e.snd,
  { have h₁ := push_cons_eq f e p h h',
    have h₂ := push_cons_eq f e (Walk.append p q hpq) (h.trans append_a.symm) h',
      simp only [h₁, h₂, ih, append_cons] },
  { have h₁ := push_cons_ne f e p h h',
    have h₂ := push_cons_ne f e (Walk.append p q hpq) (h.trans append_a.symm) h',
      simpa only [h₁, h₂, ih, append_cons] }
end

lemma push_eq_nil (f : V → V') (w : V') (p : G.Walk) (hp : ∀ z : V, z ∈ p.p.support → f z = w) :
  push_Walk f p = Walk.nil w :=
begin
  revert p, refine rec₀ _ _,
  { intros, specialize hp u (by simp [Walk.nil]), simp [hp] },
  { intros e p h ih hp,
    have h₁ : f e.fst = w := by { apply hp, left, refl },
    have h₂ : f e.snd = w := by { apply hp, right, rw h, exact p.p.start_mem_support },
    rw push_cons_eq f e p h (h₁.trans h₂.symm),
    apply ih, intros z hz, apply hp, right, exact hz }
end

@[simp] lemma push_step_range : (push_step f e).range = {f e.fst, f e.snd} :=
by { by_cases f e.fst = f e.snd; simp [push_step, push_step_aux, h] }

lemma push_range : (push_Walk f p).range = finset.image f p.range :=
begin
  refine rec₀ _ _ p, simp, rintro e p h q,
  rw [push_cons,range_cons,range_append,q,finset.image_union,push_step_range],
  ext, split; intro h',
  { rw finset.mem_union at h' ⊢, cases h', simp at h', cases h', left, subst a, simp,
    right, subst a, rw h, apply finset.mem_image_of_mem, exact start_mem_range,
    right, exact h' },
  { rw finset.mem_union at h' ⊢, cases h', simp at h', subst a, left, simp, right,
    exact h' }
end

variables {hf : adapted' f G} {p' : (push f G).Walk} {hx : f x = p'.a} {hy : f y = p'.b}

noncomputable def pull_Walk_aux (f : V → V') (hf : adapted' f G) (p' : (push f G).Walk) (x y : V)
  (hx : f x = p'.a) (hy : f y = p'.b) :
  {w : G.Walk // w.a = x ∧ w.b = y ∧ push_Walk f w = p'} :=
begin
  revert p' x y, refine rec₀ _ _,
  { rintros u x y hx hy, simp at hx hy, subst hy, choose p h₃ using hf x y hx,
    refine ⟨⟨p⟩,rfl,rfl,_⟩, apply push_eq_nil, exact h₃ },
  { rintros ⟨⟨u,v⟩,⟨huv,ee⟩⟩ p h ih x y hx hy,
    choose xx yy h₂ h₃ h₄ using ee, -- TODO `substs u v`
    choose p₁ h₆ using hf x xx (hx.trans h₂.symm),
    simp_rw [h₂] at h₆,
    obtain p₂ := ih yy y (h₃.trans h) hy,
    let pp := Walk.append ⟨p₁⟩ (p₂.val.cons ⟨⟨_,_⟩,h₄⟩ p₂.2.1.symm) rfl,
    refine ⟨pp, rfl, p₂.2.2.1, _⟩,
    have h₇ := push_eq_nil f u ⟨p₁⟩ h₆,
    simp [pp,push_append,h₇], rw [←h₂,←h₃] at huv,
    have h₈ := push_cons_ne f ⟨⟨_,_⟩,h₄⟩ p₂.val p₂.2.1.symm huv, refine h₈.trans _,
    simp [h₂,h₃], congr, exact p₂.2.2.2 }
end

noncomputable def pull_Walk (f : V → V') (hf : adapted' f G) (p' : (push f G).Walk) (x y : V)
  (hx : f x = p'.a) (hy : f y = p'.b) : G.Walk :=
(pull_Walk_aux f hf p' x y hx hy).val

lemma pull_Walk_a : (pull_Walk f hf p' x y hx hy).a = x :=
(pull_Walk_aux f hf p' x y hx hy).prop.1

lemma pull_Walk_b : (pull_Walk f hf p' x y hx hy).b = y :=
(pull_Walk_aux f hf p' x y hx hy).prop.2.1

lemma pull_Walk_push : push_Walk f (pull_Walk f hf p' x y hx hy) = p' :=
(pull_Walk_aux f hf p' x y hx hy).prop.2.2

def transportable_to (G' : simple_graph V) (p : G.Walk) : Prop :=
  ∀ e : G.dart, e ∈ p.edges → G'.adj e.fst e.snd

lemma transportable_to_of_le (G_le : G ≤ G') : p.transportable_to G' :=
begin
  refine rec₀ _ _ p,
  { rintro u e h, simp [edges] at h, contradiction },
  { rintro e p h q e' h', simp at h', cases h', rw h', exact G_le e.is_adj, exact q e' h' }
end

def transport (p : G.Walk) (hp : transportable_to G' p) :
  {q : G'.Walk // q.a = p.a ∧ q.b = p.b ∧ q.range = p.range ∧ q.init = p.init ∧ q.tail = p.tail} :=
begin
  revert p, refine rec₀ _ _,
  { rintro a hp, exact ⟨nil a, rfl, rfl, rfl, rfl, rfl⟩ },
  { rintro e p h ih hp,
    have : transportable_to G' p :=
      by { rintro e he, apply hp, rw [edges_cons,finset.mem_union], right, exact he },
    specialize ih this, rcases ih with ⟨q,hq⟩, rw ←hq.1 at h,
    exact ⟨cons ⟨⟨_,_⟩,hp e first_edge⟩ q h, by simp [hq]⟩ }
end

-- TODO for `(X : set V)`
noncomputable def until (p : G.Walk) (X : finset V) (hX : (p.range ∩ X).nonempty) :
  {q : G.Walk // q.a = p.a ∧ q.b ∈ X ∧
    q.range ⊆ p.range ∧ q.init ∩ X = ∅ ∧ q.init ⊆ p.init ∧ q.tail ⊆ p.tail} :=
begin
  revert p, refine rec₀ _ _,
  { rintro u hu, choose z hz using hu, simp at hz, cases hz with hz₁ hz₂, subst z,
    exact ⟨nil u, rfl, hz₂, by refl, rfl, by refl, by refl⟩ },
  { rintro e p h₁ ih h₂, by_cases e.fst ∈ X,
    { exact ⟨nil e.fst, rfl, h, by simp, rfl, by simp [init], by simp [tail]⟩ },
    { simp at h₂, choose z hz using h₂, simp at hz, cases hz with hz₁ hz₂,
      have : z ≠ e.fst := by { intro h, rw h at hz₂, contradiction },
      simp [this] at hz₁,
      have : z ∈ p.range ∩ X := finset.mem_inter.mpr ⟨hz₁,hz₂⟩,
      specialize ih ⟨z,this⟩, rcases ih with ⟨q,hq₁,hq₂,hq₃,hq₄,hq₅,hq₆⟩,
      rw ←hq₁ at h₁,
      refine ⟨cons e q h₁, rfl, hq₂, _, _, _, by simp [hq₃]⟩,
      { simp, apply finset.union_subset_union, refl, exact hq₃ },
      { simp [finset.inter_distrib_right,hq₄,h] },
      { simp, apply finset.union_subset_union, refl, exact hq₅ }
    }
  }
end

-- TODO for `(X : set V)`
noncomputable def after (p : G.Walk) (X : finset V) (hX : (p.range ∩ X).nonempty) :
  {q : G.Walk // q.a ∈ X ∧ q.b = p.b ∧
    q.range ⊆ p.range ∧ q.init ⊆ p.init ∧ q.tail ⊆ p.tail ∧ q.tail ∩ X = ∅} :=
begin
  revert p, refine rec₀ _ _,
  { rintro u hu,
    exact ⟨nil u, finset.singleton_inter_nonempty.mp hu, rfl, by refl, by refl, by refl, rfl⟩ },
  { rintro e p h₁ ih h₂, by_cases (p.range ∩ X).nonempty,
    { rcases ih h with ⟨q, hq₁, hq₂, hq₃, hq₄, hq₅, hq₆⟩,
      refine ⟨q, hq₁, hq₂, _, _, _, hq₆⟩,
      { simp, apply hq₃.trans, apply finset.subset_union_right },
      { simp, apply hq₄.trans, apply finset.subset_union_right },
      { simp, apply hq₅.trans, rw range_eq_start_union_tail, apply finset.subset_union_right }
    },
    { refine ⟨cons e p h₁, _, rfl, by refl, _⟩,
      { simp at h₂ ⊢, rcases h₂ with ⟨z,hz⟩, simp at hz, cases hz with hz₁ hz₂,
        cases hz₁, subst z, exact hz₂, exfalso, apply h, use z, simp, exact ⟨hz₁,hz₂⟩ },
      { simp at h ⊢, exact h } } }
end

noncomputable def within (p : G.Walk) (G' : simple_graph V) : {q : G'.Walk // q.a = p.a} :=
begin
  refine rec₀ _ _ p,
  { intro v, exact ⟨nil v, rfl⟩ },
  { rintro e p h q,
    by_cases h' : G'.adj e.fst e.snd,
    { rw ← q.prop at h, refine ⟨cons ⟨⟨_,_⟩,h'⟩ q h, rfl⟩ },
    { exact ⟨nil e.fst, rfl⟩ } }
end

def reverse (p : G.Walk) : G.Walk := ⟨p.p.reverse⟩

@[simp] lemma reverse_a : (reverse p).a = p.b := by simp only [reverse]
@[simp] lemma reverse_b : (reverse p).b = p.a := by simp only [reverse]

@[simp] lemma reverse_range : (reverse p).range = p.range :=
by simp only [reverse, range, walk.support_reverse, list.to_finset_reverse]

end Walk

end simple_graph

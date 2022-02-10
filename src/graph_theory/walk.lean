import tactic combinatorics.simple_graph.connectivity
import graph_theory.path graph_theory.pushforward graph_theory.contraction
open classical function
open_locale classical

namespace simple_graph

variables {V V' : Type} [decidable_eq V] [decidable_eq V'] {f : V → V'}
variables {G : simple_graph V} {x y z u v w a b c : V}

@[ext] structure Walk (G : simple_graph V) := {a b : V} (p : G.walk a b)

namespace Walk

variables {e : G.step} {p q : G.Walk} {hep : e.y = p.a} {hpq : p.b = q.a}

def nil (a : V) : G.Walk := ⟨(walk.nil : G.walk a a)⟩

@[simp] lemma nil_a : (nil a : G.Walk).a = a := rfl

@[simp] lemma nil_b : (nil b : G.Walk).b = b := rfl

def cons (e : G.step) (p : G.Walk) (h : e.y = p.a) : G.Walk :=
by { let h' := e.h, rw h at h', exact ⟨p.p.cons h'⟩ }

def step (e : G.step) : G.Walk := cons e (nil e.y) rfl

def rec₀ (motive : G.Walk → Sort*) :
  (Π u, motive (Walk.nil u)) →
  (Π e p h, motive p → motive (cons e p h)) →
  Π p, motive p :=
begin
  rintros h_nil h_cons ⟨a,b,p⟩, induction p with a a b c adj p ih,
  { exact h_nil a },
  { exact h_cons ⟨adj⟩ ⟨p⟩ rfl ih }
end

@[simp] lemma rec_nil {motive h_nil h_cons} :
  @rec₀ V _ G motive h_nil h_cons (nil a) = h_nil a := rfl

@[simp] lemma rec_cons {motive h_nil h_cons h} :
  @rec₀ V _ G motive h_nil h_cons (cons e p h) =
  h_cons e p h (rec₀ motive h_nil h_cons p) :=
begin
  rcases e with ⟨u,v,e⟩, rcases p with ⟨a,b,p⟩, simp at h, subst v, refl
end

@[simp] lemma cons_a : (cons e p hep).a = e.x := rfl

@[simp] lemma cons_b : (cons e p hep).b = p.b := rfl

lemma cons_p : (cons e p hep).p = by { let h' := e.h, rw hep at h', exact p.p.cons h' } := rfl

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
  rcases e with ⟨u,v,e⟩, rcases p with ⟨a,b,p⟩, rcases q with ⟨c,d,q⟩,
  simp at hep hpq, substs a b, refl
end

lemma mem_append : z ∈ (append p q hpq).p.support ↔ z ∈ p.p.support ∨ z ∈ q.p.support :=
begin
  rcases p with ⟨a,b,p⟩, rcases q with ⟨d,c,q⟩, simp at hpq, subst d,
  rw [append, append_aux], simp only [walk.mem_support_append_iff]
end

def push_step_aux (f : V → V') (e : G.step) :
  {w : (push f G).Walk // w.a = f e.x ∧ w.b = f e.y} :=
begin
  by_cases f e.x = f e.y,
  refine ⟨Walk.nil (f e.x), rfl, h⟩,
  refine ⟨Walk.step ⟨⟨h,e.x,e.y,rfl,rfl,e.h⟩⟩, rfl, rfl⟩
end

def push_step (f : V → V') (e : G.step) : (push f G).Walk :=
(push_step_aux f e).val

@[simp] lemma push_step_a : (push_step f e).a = f e.x :=
(push_step_aux f e).prop.1

@[simp] lemma push_step_b : (push_step f e).b = f e.y :=
(push_step_aux f e).prop.2

def push_Walk_aux (f : V → V') (p : G.Walk) :
  {w : (push f G).Walk // w.a = f p.a ∧ w.b = f p.b} :=
begin
  refine rec₀ _ _ _ p,
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

lemma push_cons (f : V → V') (e : G.step) (p : G.Walk) (h : e.y = p.a) :
  push_Walk f (p.cons e h) = Walk.append (push_step f e) (push_Walk f p) (by simp [h]) :=
by { rcases p with ⟨a,b,p⟩, rcases e with ⟨u,v,e⟩, simp at h, subst a, refl }

lemma push_cons_eq (f : V → V') (e : G.step) (p : G.Walk) (h : e.y = p.a) (h' : f e.x = f e.y) :
  push_Walk f (p.cons e h) = push_Walk f p :=
begin
  have : push_step f e = Walk.nil (f e.x) := by simp [push_step,push_step_aux,h'],
  rw [push_cons], simp only [this], exact append_nil_left
end

lemma push_cons_ne (f : V → V') (e : G.step) (p : G.Walk) (h : e.y = p.a) (h' : f e.x ≠ f e.y) :
  push_Walk f (p.cons e h) = Walk.cons ⟨⟨h',e.x,e.y,rfl,rfl,e.h⟩⟩ (push_Walk f p) (by simp [h]) :=
begin
  have : push_step f e = Walk.step ⟨⟨h',e.x,e.y,rfl,rfl,e.h⟩⟩ :=
    by simp [push_step,push_step_aux,h'],
  rw [push_cons], simp [this,step]
end

lemma push_append (f : V → V') (p q : G.Walk) (hpq : p.b = q.a) :
  push_Walk f (Walk.append p q hpq) =
  Walk.append (push_Walk f p) (push_Walk f q) (by simp [hpq]) :=
begin
  revert p, refine Walk.rec₀ _ (by simp) _,
  intros e p h ih hpq, by_cases h' : f e.x = f e.y,
  { have h₁ := push_cons_eq f e p h h',
    have h₂ := push_cons_eq f e (Walk.append p q hpq) (h.trans append_a.symm) h',
      simp only [h₁, h₂, ih, append_cons] },
  { have h₁ := push_cons_ne f e p h h',
    have h₂ := push_cons_ne f e (Walk.append p q hpq) (h.trans append_a.symm) h',
      simpa only [h₁, h₂, ih, append_cons] }
end

lemma push_eq_nil (f : V → V') (w : V') (p : G.Walk) (hp : ∀ (z : V), z ∈ p.p.support → f z = w) :
  push_Walk f p = Walk.nil w :=
begin
  revert p, refine Walk.rec₀ _ _ _,
  { intros, specialize hp u (by simp [Walk.nil]), simp [hp] },
  { intros e p h ih hp,
    have h₁ : f e.x = w := by { apply hp, left, refl },
    have h₂ : f e.y = w := by { apply hp, right, rw h, exact p.p.start_mem_support },
    rw push_cons_eq f e p h (h₁.trans h₂.symm),
    apply ih, intros z hz, apply hp, right, exact hz }
end

lemma push_support : z ∈ p.p.support → f z ∈ (push_Walk f p).p.support :=
begin
  refine rec₀ _ _ _ p,
  { intros z hz, rw nil at hz, simp at hz, simp [nil,hz] },
  { intros e p h ih z, cases e, cases p, rw cons at z, simp at z, cases z,
    { subst z,
      have : (push_Walk f (cons ⟨e_h⟩ ⟨p_p⟩ h)).a = f e_x := by simp [push_Walk_a],
      rw ← this, apply walk.start_mem_support },
    { specialize ih z_1, rw Walk.push_cons, rw mem_append, right, exact ih } }
end

variables {hf : adapted' f G} {p' : (push f G).Walk} {hx : f x = p'.a} {hy : f y = p'.b}

noncomputable def pull_Walk_aux (f : V → V') (hf : adapted' f G) (p' : (push f G).Walk) (x y : V)
  (hx : f x = p'.a) (hy : f y = p'.b) :
  {w : G.Walk // w.a = x ∧ w.b = y ∧ push_Walk f w = p'} :=
begin
  revert p' x y, refine rec₀ _ _ _,
  { rintros u x y hx hy, simp at hx hy, subst hy,
    have h₁ := hf x y hx, set p := some h₁ with hp, have h₃ := some_spec h₁, simp_rw ← hp at *,
    refine ⟨⟨p⟩,rfl,rfl,_⟩,
    apply push_eq_nil, exact h₃ },
  { rintros e p h ih x y hx hy, simp at hx hy,
    rcases e with ⟨u,v,⟨huv,ee⟩⟩, simp at hx h,
    set xx := some ee with hxx, have h₁ := some_spec ee, simp_rw ← hxx at h₁,
    set yy := some h₁ with hyy, have h₂ := some_spec h₁, simp_rw ← hyy at h₂,
    rcases h₂ with ⟨h₂,h₃,h₄⟩,
    have h₅ := hf x xx (hx.trans h₂.symm),
    set p₁ := some h₅ with hp₁, have h₆ := some_spec h₅, simp_rw [←hp₁,h₂] at h₆,
    obtain p₂ := ih yy y (h₃.trans h) hy,
    let pp := Walk.append ⟨p₁⟩ (p₂.val.cons ⟨h₄⟩ p₂.2.1.symm) rfl,
    refine ⟨pp, rfl, p₂.2.2.1, _⟩,
    have h₇ := push_eq_nil f u ⟨p₁⟩ h₆,
    simp [pp,push_append,h₇], rw [←h₂,←h₃] at huv,
    have h₈ := push_cons_ne f ⟨h₄⟩ p₂.val p₂.2.1.symm huv, refine h₈.trans _, clear h₈,
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

end Walk

end simple_graph

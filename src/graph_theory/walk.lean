import tactic combinatorics.simple_graph.connectivity
import graph_theory.basic graph_theory.path graph_theory.pushforward
open classical function
open_locale classical

namespace simple_graph
variables {V V' : Type} [decidable_eq V] [decidable_eq V'] {f : V → V'}
variables {G : simple_graph V} {x y z u v w a b c : V}

@[ext] structure Walk (G : simple_graph V) := {a b : V} (p : G.walk a b)

namespace Walk
variables {e : G.step} {p q : G.Walk} {hep : e.y = p.a} {hpq : p.b = q.a}

def nil (a : V) : G.Walk := ⟨(walk.nil : G.walk a a)⟩

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
  @rec₀ V _ G motive h_nil h_cons (cons e p h) = h_cons e p h (rec₀ motive h_nil h_cons p) :=
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

def append_aux' (p q : G.Walk) (hpq : p.b = q.a) : {w : G.Walk // w.a = p.a ∧ w.b = q.b} :=
begin
  revert p, refine rec₀ _ _ _,
  { intros, refine ⟨q,_,rfl⟩, rw ← hpq, refl },
  { intros e p hep ih h', rcases (ih h') with ⟨p',hp'₁,hp'₂⟩,
    exact ⟨cons e p' (hep.trans hp'₁.symm), rfl, hp'₂⟩ }
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
  have : push_step f e = Walk.step ⟨⟨h',e.x,e.y,rfl,rfl,e.h⟩⟩ := by simp [push_step,push_step_aux,h'],
  rw [push_cons], simp [this,step]
end

lemma push_append (f : V → V') (p q : G.Walk) (hpq : p.b = q.a) :
  push_Walk f (Walk.append p q hpq) = Walk.append (push_Walk f p) (push_Walk f q) (by simp [hpq]) :=
begin
  revert p, refine Walk.rec₀ _ (by simp) _,
  intros e p h ih hpq, by_cases h' : f e.x = f e.y,
  { have h₁ := push_cons_eq f e p h h',
    have h₂ := push_cons_eq f e (Walk.append p q hpq) (h.trans append_a.symm) h',
      simp [h₁,h₂,ih] },
  { have h₁ := push_cons_ne f e p h h',
    have h₂ := push_cons_ne f e (Walk.append p q hpq) (h.trans append_a.symm) h',
      simpa [h₁,h₂,ih] }
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

        -- TODO this will belong in pushforward or in contraction (lift_path)
        noncomputable def raise (f : V → V') (hf : adapted' f G) (x' y' : V') (γ : walk (push f G) x' y')
            (x y : V) (hx : f x = x') (hy : f y = y') :
            {p : walk G x y // lower f x y p == γ} :=
        begin
            revert x y, induction γ with a a b c h₁ p ih,
            { rintros x y h₁ rfl,
                have h₂ := hf x y h₁,
                set p := some h₂ with hp, have h₃ := some_spec h₂, simp_rw ← hp at *,
                use p, exact lower_nil f x y p h₃ },
            { rintros x y rfl rfl, rcases h₁ with ⟨h₁,h₂⟩,
                set xx := some h₂ with hx, have h₃ := some_spec h₂, simp_rw ← hx at h₃,
                set yy := some h₃ with hy, have h₄ := some_spec h₃, simp_rw ← hy at h₄,
                rcases h₄ with ⟨h₄,h₅,h₆⟩,
                set p₁ := some (hf x xx h₄.symm) with hp₁, have h₇ := some_spec (hf x xx h₄.symm), simp_rw ← hp₁ at *,
                obtain ⟨p₂,hp₂⟩ := ih yy y h₅ rfl,
                use p₁.append (p₂.cons h₆), sorry }
        end

        lemma lower_raise (f : V → V') (hf : adapted' f G) (x y : V) (x' y' : V') (γ : walk (push f G) x' y')
            (hx : f x = x') (hy : f y = y') :
            lower f x y (raise f hf x' y' γ x y hx hy).val == γ :=
        (raise f hf x' y' γ x y hx hy).prop

end Walk
end simple_graph

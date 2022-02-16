import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward graph_theory.basic graph_theory.walk
open finset classical function simple_graph.Walk
open_locale classical

variables {V V' : Type} {a : V} {G : simple_graph V}

namespace simple_graph
namespace menger
variables [fintype V] [fintype V'] {A B X Y Z : finset V}

@[ext] structure AB_walk (G : simple_graph V) (A B : finset V) :=
  (p : Walk G) (ha : p.a ∈ A) (hb : p.b ∈ B)

@[ext] structure AB_walk' (G : simple_graph V) (A B : finset V) extends AB_walk G A B :=
  (h'a : p.init ∩ B = ∅) (h'b : p.tail ∩ A = ∅)

def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
  ∀ γ : AB_walk G A B, (γ.p.range ∩ X).nonempty

lemma separates_self : separates G A B A :=
  λ γ, ⟨γ.p.a, mem_inter.mpr ⟨Walk.start_mem_range,γ.ha⟩⟩

lemma separates.symm : separates G A B X → separates G B A X :=
begin
  rintro h ⟨p,pa,pb⟩, rcases p.reverse_aux with ⟨q,qa,qb,qr⟩,
  let q' : AB_walk G A B := ⟨q, qa.symm ▸ pb, qb.symm ▸ pa⟩,
  dsimp, rw ←qr, exact h q'
end

def is_cut_set_size (G : simple_graph V) (A B : finset V) (n : ℕ) : Prop :=
  ∃ X : finset V, X.card = n ∧ separates G A B X

noncomputable def min_cut' (G : simple_graph V) (A B : finset V) :
  {n : ℕ // (is_cut_set_size G A B n) ∧ (∀ m < n, ¬is_cut_set_size G A B m) } :=
begin
  let n := @nat.find (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
  have p₁ := @nat.find_spec (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
  have p₂ := λ m, @nat.find_eq_iff m (is_cut_set_size G A B) _ ⟨A.card,⟨A,rfl,separates_self⟩⟩,
  exact ⟨n, p₁, ((p₂ n).mp rfl).2⟩
end

noncomputable def min_cut (G : simple_graph V) (A B : finset V) : ℕ :=
  (min_cut' G A B).val

noncomputable def min_cut_set (G : simple_graph V) (A B : finset V) :
  {X : finset V // X.card = min_cut G A B ∧ separates G A B X} :=
⟨_, some_spec (min_cut' G A B).prop.1⟩

lemma min_cut_spec (sep : separates G A B X) : min_cut G A B ≤ X.card :=
by { have h := mt ((min_cut' G A B).2.2 X.card), rw [not_not,not_lt] at h, exact h ⟨X,rfl,sep⟩ }

variables {P : finset (AB_walk G A B)}

def pw_disjoint (P : finset (AB_walk G A B)) : Prop :=
∀ ⦃γ₁ γ₂ : P⦄, (γ₁.val.p.range ∩ γ₂.val.p.range).nonempty → γ₁ = γ₂

def pw_disjoint' (P : finset (AB_walk' G A B)) : Prop :=
∀ ⦃γ₁ γ₂ : P⦄, (γ₁.val.p.range ∩ γ₂.val.p.range).nonempty → γ₁ = γ₂

lemma path_le_A (dis : pw_disjoint P) : P.card ≤ A.card :=
begin
  let φ : P → A := λ p, ⟨p.1.1.a, p.1.ha⟩,
  have : injective φ := by { rintro p₁ p₂ h, simp at h, apply dis, use p₁.1.1.a, simp, simp [h] },
  simp_rw [←fintype.card_coe], convert fintype.card_le_of_injective φ this,
end

lemma path_le_B (dis : pw_disjoint P) : P.card ≤ B.card :=
begin
  let φ : P → B := λ p, ⟨p.1.1.b, p.1.hb⟩,
  have : injective φ := by { rintro p₁ p₂ h, simp at h, apply dis, use p₁.1.1.b, simp, simp [h] },
  simp_rw [←fintype.card_coe], convert fintype.card_le_of_injective φ this,
end

lemma path_le_cut (dis : pw_disjoint P) (sep : separates G A B X) : P.card ≤ X.card :=
begin
  let φ : Π γ : P, γ.val.p.range ∩ X := λ γ, by { choose z hz using sep γ, exact ⟨z,hz⟩ },
  let ψ : P → X := λ γ, ⟨_, mem_of_mem_inter_right (φ γ).prop⟩,
  have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.p.range := λ γ, let z := φ γ in (mem_inter.mp z.2).1,
  have h₂ : injective ψ := λ γ γ' h, dis ⟨_, mem_inter_of_mem (h₁ γ) (by { rw h, exact (h₁ γ') })⟩,
  simp_rw [←fintype.card_coe], convert fintype.card_le_of_injective ψ h₂
end

lemma upper_bound (dis : pw_disjoint P) : P.card ≤ min_cut G A B :=
by { obtain ⟨X,h₁,h₂⟩ := min_cut_set G A B, rw ←h₁, exact path_le_cut dis h₂ }

lemma bot_iff_no_edge : fintype.card G.step = 0 ↔ G = ⊥ :=
begin
  split; intro h,
  { ext x y, simp, intro h₁, exact is_empty_iff.mp (fintype.card_eq_zero_iff.mp h) ⟨h₁⟩ },
  { rw h, exact fintype.card_eq_zero_iff.mpr (is_empty_iff.mpr step.h), }
end

lemma bot_separates_iff : separates ⊥ A B X ↔ (A ∩ B) ⊆ X :=
begin
  split; intro h,
  { rintros z hz, rw [mem_inter] at hz, let γ : AB_walk ⊥ A B := ⟨Walk.nil _, hz.1, hz.2⟩,
    have := h γ, choose z h₁ using this, simp at h₁, rw ←h₁.1, exact h₁.2 },
  { rintro ⟨⟨a,b,γ⟩,ha,hb⟩, cases γ, swap, exfalso, exact γ_h,
    simp at ha hb ⊢, use a, simp, split, exact Walk.start_mem_range,
    apply mem_of_subset h, simp, exact ⟨ha,hb⟩ }
end

lemma bot_min_cut : min_cut ⊥ A B = (A ∩ B).card :=
begin
  apply (nat.find_eq_iff _).mpr, simp [bot_separates_iff], split,
  { use A ∩ B, exact ⟨rfl,subset.rfl⟩ },
  { rintros n h₁ X rfl h₂, have := card_le_of_subset h₂, linarith }
end

noncomputable def bot_path_set (A B : finset V) :
  {P : finset (AB_walk ⊥ A B) // pw_disjoint P ∧ P.card = (A ∩ B).card} :=
begin
  let φ : A ∩ B → AB_walk ⊥ A B := λ z, let h := mem_inter.mp z.prop in ⟨⟨walk.nil⟩,h.1,h.2⟩,
  have φ_inj : injective φ := λ _ _ h, by { simp only [φ] at h, ext, exact h.1 },
  refine ⟨image φ univ, _, _⟩,
  { rintro ⟨⟨γ₁,h₁,h₂⟩,h₃⟩ ⟨⟨γ₂,h₄,h₅⟩,h₆⟩ h₇,
    have nil₁ : γ₁ = Walk.nil γ₁.a := by { cases γ₁, cases γ₁_p, refl, exfalso, exact γ₁_p_h },
    have nil₂ : γ₂ = Walk.nil γ₂.a := by { cases γ₂, cases γ₂_p, refl, exfalso, exact γ₂_p_h },
    simp at h₇ ⊢, rw [nil₁,nil₂] at h₇ ⊢, cases h₇ with z h₇, simp at h₇, rw [←h₇.1,←h₇.2] },
  { rw [card_image_of_injective univ φ_inj, card_univ],
    convert fintype.card_of_finset (A ∩ B) _, intro z, simp, split,
    { rintros ⟨h₁,h₂⟩, exact set.mem_sep h₁ h₂ },
    { rintros h₁, exact h₁ } }
end

variables {f : V → V'} {hf : adapted' f G}

noncomputable def AB_lift (f : V → V') (hf : adapted' f G) (A B : finset V) :
  AB_walk (push f G) (A.image f) (B.image f) → AB_walk G A B :=
begin
  rintro ⟨p,ha,hb⟩,
  choose a h₂ h₃ using mem_image.mp ha,
  choose b h₅ h₆ using mem_image.mp hb,
  let γ := Walk.pull_Walk_aux f hf p a b h₃ h₆,
  rw ←γ.2.1 at h₂, rw ←γ.2.2.1 at h₅, exact ⟨γ,h₂,h₅⟩
end

noncomputable def AB_push (f : V → V') (A B : finset V) :
  AB_walk G A B → AB_walk (push f G) (A.image f) (B.image f) :=
begin
  intro p, refine ⟨Walk.push_Walk f p.p, _, _⟩,
  rw Walk.push_Walk_a, exact mem_image_of_mem f p.ha,
  rw Walk.push_Walk_b, exact mem_image_of_mem f p.hb,
end

lemma AB_push_lift : left_inverse (AB_push f A B) (AB_lift f hf A B) :=
by { rintro ⟨p,ha,hb⟩, simp [AB_lift,AB_push], exact Walk.pull_Walk_push, }

lemma AB_lift_inj : injective (AB_lift f hf A B) :=
left_inverse.injective AB_push_lift

lemma AB_lift_dis (P' : finset (AB_walk (push f G) (A.image f) (B.image f))) :
  pw_disjoint P' → pw_disjoint (P'.image (AB_lift f hf A B)) :=
begin
  rintro hP' ⟨γ₁,h₁⟩ ⟨γ₂,h₂⟩ h, simp at h ⊢, choose z h using h,
  choose γ'₁ h'₁ h''₁ using mem_image.mp h₁,
  choose γ'₂ h'₂ h''₂ using mem_image.mp h₂,
  have h₃ := congr_arg (AB_push f A B) h''₁, rw AB_push_lift at h₃,
  have h₄ := congr_arg (AB_push f A B) h''₂, rw AB_push_lift at h₄,
  suffices : γ'₁ = γ'₂, { rw [←h''₁,←h''₂,this] },
  have := @hP' ⟨_,h'₁⟩ ⟨_,h'₂⟩, simp at this, apply this,
  simp [h₃,h₄,AB_push,Walk.push_range], use f z, rw mem_inter at h ⊢, split,
  exact mem_image_of_mem f h.1, exact mem_image_of_mem f h.2
end

def minus (G : simple_graph V) (e : G.step) : simple_graph V :=
{
  adj := λ x y, G.adj x y ∧ ((x ≠ e.x ∧ x ≠ e.y) ∨ (y ≠ e.x ∧ y ≠ e.y)),
  symm := λ x y ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
  loopless := λ x h, G.loopless _ h.1
}

infix `-` := minus

lemma minus_le {e : G.step} : G-e ≤ G := λ x y h, h.1

lemma minus_lt_edges {e : G.step} : fintype.card (G-e).step < fintype.card G.step :=
begin
  let φ : (G-e).step → G.step := λ e, ⟨e.h.1⟩,
  have φ_inj : injective φ := by { rintro e₁ e₂ h, simp [φ] at h, exact e₁.ext e₂ h.1 h.2 },
  suffices : e ∉ set.range φ, refine fintype.card_lt_of_injective_of_not_mem φ φ_inj this,
  intro he, rw set.mem_range at he, choose e' he using he, rcases e' with ⟨x,y,he'⟩,
  have : x = e.x := congr_arg step.x he, have : y = e.y := congr_arg step.y he,
  substs x y, simp [minus] at he', simp at he', exact he'
end

lemma sep_AB_of_sep₂_AX ⦃e : G.step⦄ (ex_in_X : e.x ∈ X) (ey_in_X : e.y ∈ X) :
  separates G A B X → separates (G-e) A X Z → separates G A B Z :=
by {
  rintro X_sep_AB Z_sep₂_AX γ,
  rcases γ.p.until X (X_sep_AB γ) with ⟨δ,δ_a,δ_b,δ_range,δ_init,-⟩,
  have : δ.transportable_to (G-e) := by {
    revert δ_init, refine Walk.rec₀ _ _ δ,
    { simp [Walk.transportable_to,Walk.edges] },
    { rintro e' p h ih h₁ e'' h₂,
      have h₃ : p.init ∩ X = ∅ :=
      by { apply subset_empty.mp, rw [←h₁], apply inter_subset_inter_right,
        rw [Walk.init_cons], apply subset_union_right },
      simp at h₂, cases h₂,
      { subst e'', simp at h₁, simp [minus,e'.h],
        have : e'.x ∉ X :=
        by { rw [inter_distrib_right, union_eq_empty_iff] at h₁, intro h,
          have : ({e'.x} ∩ X).nonempty := ⟨e'.x, by simp [h]⟩, simp [h₁.1] at this, exact this },
        refine ⟨e'.h,_⟩, left, split; { intro h, rw h at this, contradiction } },
      { exact ih h₃ e'' h₂ }
    }
  },
  rcases δ.transport this with ⟨ζ,ζ_a,ζ_b,ζ_range,-,-⟩,
  rcases Z_sep₂_AX ⟨ζ, by { rw [ζ_a,δ_a], exact γ.ha }, by { rw [ζ_b], exact δ_b }⟩ with ⟨z,hz⟩,
  rw ←ζ_range at δ_range, rw mem_inter at hz,
  exact ⟨z, mem_inter.mpr ⟨mem_of_subset δ_range hz.1, hz.2⟩⟩,
}

noncomputable def trim (p : AB_walk G A B) : {q : AB_walk' G A B // q.p.range ⊆ p.p.range} :=
begin
  rcases p with ⟨p₁, p₁a, p₁b⟩,
  have h₁ : (p₁.range ∩ A).nonempty := ⟨p₁.a, by simp [p₁a]⟩,
  rcases p₁.after A h₁ with ⟨p₂, p₂a, p₂b, p₂r, p₂i, -, p₂t⟩,
  have h₂ : (p₂.range ∩ B).nonempty := by { refine ⟨p₂.b, _⟩, simp, rwa p₂b },
  rcases p₂.until B h₂ with ⟨p₃, p₃a, p₃b, p₃r, p₃i, -, p₃t⟩,
  refine ⟨⟨⟨p₃, p₃a.symm ▸ p₂a, p₃b⟩, by simp [p₃i], _⟩, p₃r.trans p₂r⟩,
  have : p₃.tail ∩ A ⊆ p₂.tail ∩ A := inter_subset_inter_right p₃t,
  simp, rw ←subset_empty, apply this.trans, rw p₂t, refl
end

noncomputable def massage_aux {G₁ G₂ : simple_graph V} (h : G₂ ≤ G₁)
  (p : AB_walk G₂ A X) : {q : AB_walk' G₁ A X // q.p.range ⊆ p.p.range} :=
begin
  rcases trim p with ⟨⟨⟨p',p'a,p'b⟩,p'aa,p'bb⟩,hp'⟩,
  rcases p'.transport (transportable_to_of_le h) with ⟨q,qa,qb,qr,qi,qt⟩,
  use ⟨⟨q, qa.symm ▸ p'a, qb.symm ▸ p'b⟩, qi.symm ▸ p'aa, qt.symm ▸ p'bb⟩,
  simp, simp at hp', rw qr, exact hp'
end

noncomputable def massage {G₁ G₂ : simple_graph V} (h : G₂ ≤ G₁) :
  AB_walk G₂ A X → AB_walk' G₁ A X :=
λ p, (massage_aux h p).val

lemma massage_eq {G₁ G₂ : simple_graph V} {h : G₂ ≤ G₁} {P : finset (AB_walk G₂ A B)} {p₁ p₂ : P} :
  pw_disjoint P → ((massage h p₁.val).p.range ∩ (massage h p₂.val).p.range).nonempty → p₁ = p₂ :=
begin
  rintro hP h, apply hP, rcases h with ⟨z,hz⟩, use z, simp at hz ⊢, split,
  { apply (massage_aux h p₁.val).prop, exact hz.1 },
  { apply (massage_aux h p₂.val).prop, exact hz.2 }
end

lemma massage_disjoint {G₁ G₂ : simple_graph V} {h : G₂ ≤ G₁} {P : finset (AB_walk G₂ A B)} :
  pw_disjoint P → pw_disjoint' (image (massage h) P) :=
begin
  rintro h₁ ⟨p₁,hp₁⟩ ⟨p₂,hp₂⟩ h, apply subtype.ext, dsimp,
  choose q₁ hq₁ hq₁' using mem_image.mp hp₁, choose q₂ hq₂ hq₂' using mem_image.mp hp₂,
  rw [←hq₁',←hq₂'], apply congr_arg, let γ₁ : P := ⟨q₁,hq₁⟩, let γ₂ : P := ⟨q₂,hq₂⟩,
  suffices : γ₁ = γ₂, { simp only [subtype.mk_eq_mk] at this, exact this }, apply massage_eq h₁,
  rw [hq₁',hq₂'], exact h
end

lemma massage_card {G₁ G₂ : simple_graph V} {h : G₂ ≤ G₁} {P : finset (AB_walk G₂ A B)} :
  pw_disjoint P → (image (massage h) P).card = P.card :=
begin
  rintro hP, apply card_image_of_inj_on, rintro p₁ hp₁ p₂ hp₂ he,
  let q₁ : P := ⟨p₁,hp₁⟩, let q₂ : P := ⟨p₂,hp₂⟩, suffices : q₁ = q₂, simp at this, exact this,
  apply massage_eq hP, rw he, simp
end

lemma meet_sub_X {X_sep_AB : separates G A B X} (p : AB_walk' G A X) (q : AB_walk' G X B) :
  p.p.range ∩ q.p.range ⊆ X :=
begin
  rcases p with ⟨⟨p,pa,pb⟩,pa',pb'⟩, rcases q with ⟨⟨q,qa,qb⟩,qa',qb'⟩, dsimp at pa' pb' qa' qb' ⊢,
  rintro x hx, rw mem_inter at hx, cases hx with hx₁ hx₂, by_contra,

  rcases p.until {x} ⟨x, by simp [hx₁]⟩ with ⟨p', p'a, p'b, p'r, p'i, p'i2, p't⟩, simp at p'b,
  have h₁ : p'.range ∩ X = ∅ :=
  by { rw Walk.range_eq_init_union_last, by_contra', have := nonempty_of_ne_empty this,
    choose z hz using this, simp at hz, cases hz with hz₁ hz₂, cases hz₁,
    { have : p.init ∩ X ≠ ∅ := by { apply nonempty.ne_empty,
      use z, rw mem_inter, exact ⟨p'i2 hz₁, hz₂⟩ }, contradiction },
    { subst z, subst x, exact h hz₂ } },

  rcases q.after {x} ⟨x, by simp [hx₂]⟩ with ⟨q', q'a, q'b, q'r, q'i, q't, q't2⟩, simp at q'a,
  have h₂ : q'.range ∩ X = ∅ :=
  by { rw Walk.range_eq_start_union_tail, apply subset_empty.mp, rintro z hz, simp at hz ⊢,
    cases hz with hz₁ hz₂, cases hz₁,
    { substs hz₁ q'a, contradiction },
    { have : q.tail ∩ X ≠ ∅ := by { apply nonempty.ne_empty,
      use z, rw mem_inter, exact ⟨q't hz₁, hz₂⟩ }, contradiction } },

  subst q'a,
  let γ : AB_walk G A B := ⟨Walk.append p' q' p'b, by simp [p'a,pa], by simp [q'b,qb]⟩,
  choose z hz using X_sep_AB γ, rw [Walk.range_append,inter_distrib_right] at hz,
  rw mem_union at hz, cases hz; { have := ne_empty_of_mem hz, contradiction }
end

lemma lower_bound_aux (n : ℕ) : ∀ (G : simple_graph V), fintype.card G.step ≤ n →
  ∀ A B : finset V, ∃ P : finset (AB_walk G A B), pw_disjoint P ∧ P.card = min_cut G A B :=
begin
  -- We apply induction on ∥G∥.
  induction n with n ih,

  -- If G has no edge, then |A∩B| = k and we have k trivial AB paths.
  { intros G hG A B, simp at hG, rw [bot_iff_no_edge.mp hG,bot_min_cut],
    exact (bot_path_set A B).exists_of_subtype },

  -- So we assume that G has an edge e = xy.
  rintros G hG A B, by_cases (fintype.card G.step = 0), { apply ih, linarith },
  cases not_is_empty_iff.mp (h ∘ fintype.card_eq_zero_iff.mpr) with e, clear h,

  apply not_imp_self.mp, intro too_small, push_neg at too_small, replace too_small :
    ∀ P : finset (AB_walk G A B), pw_disjoint P → P.card < min_cut G A B :=
  by { intros P h, exact lt_of_le_of_ne (upper_bound h) (too_small P h) },

  -- If G has no k disjoint AB paths then neither does G/e; here, we count the contracted vertex ve
  -- as an element of A (resp.B) in G/e if in G at least one of x,y lies in A (resp.B) By the
  -- induction hypothesis, G/e contains an AB separator Y of fewer than k vertices. Among these must
  -- be the vertex ve, since otherwise Y ⊆ V would be an AB separator in G. Then X := (Y-ve)∪{x,y}
  -- is an AB separator in G, of exactly k vertices.

  have step₁ : ∃ X : finset V,
    e.x ∈ X ∧ e.y ∈ X ∧ separates G A B X ∧ X.card = min_cut G A B :=
  by {
    let G₁ := G/e,
    let A₁ : finset G₁.vertices := image (merge_edge e) A,
    let B₁ : finset G₁.vertices := image (merge_edge e) B,

    obtain ⟨Y, Y_eq_min₁, Y_sep⟩ := min_cut_set G₁ A₁ B₁, let X := Y ∪ {e.y},

    have Y_lt_min : Y.card < min_cut G A B :=
    by { have G₁_le_n : fintype.card G₁.step ≤ n :=
      by { refine nat.le_of_lt_succ (nat.lt_of_lt_of_le _ hG),
        refine fintype.card_lt_of_injective_of_not_mem _ push.lift_step_inj _,
        exact e, exact push.lift_step_ne_mem (by {simp [merge_edge]}) },
      choose P₁ P₁_dis P₁_eq_min₁ using ih G₁ G₁_le_n A₁ B₁,
      rw [Y_eq_min₁, ←P₁_eq_min₁, ←card_image_of_injective P₁ AB_lift_inj],
      apply too_small, { apply AB_lift_dis, exact P₁_dis }, { exact merge_edge_adapted } },

    have X_sep_AB : separates G A B X :=
    by { intro γ, choose z hz using Y_sep (AB_push (merge_edge e) A B γ),
      rw [mem_inter,AB_push,Walk.push_range,mem_image] at hz,
      choose x hx₁ hx₂ using hz.1, by_cases x = e.y; simp [merge_edge,h] at hx₂,
      { use x, simp, split, exact hx₁, right, exact h },
      { use x, simp, split, exact hx₁, left, rw hx₂, exact hz.2 } },

    refine ⟨X, _, _, X_sep_AB, _⟩,

    { rw [mem_union], left, by_contradiction,
      suffices : separates G A B Y, by { exact not_lt_of_le (min_cut_spec this) Y_lt_min },
      intro p, choose z hz using Y_sep (AB_push (merge_edge e) A B p), use z,
      rw mem_inter at hz ⊢, rcases hz with ⟨hz₁,hz₂⟩, refine ⟨_,hz₂⟩,
      rw [AB_push,Walk.push_range,mem_image] at hz₁, choose x hx₁ hx₂ using hz₁,
      by_cases x = e.y; simp [merge_edge,h] at hx₂,
      { rw [←hx₂] at hz₂, contradiction },
      { rwa [←hx₂] } },
    { rw [mem_union,mem_singleton], right, refl },
    { refine le_antisymm _ (min_cut_spec X_sep_AB),
      exact (card_union_le _ _).trans (nat.succ_le_of_lt Y_lt_min) }
  },

  choose X ex_in_X ey_in_X X_sep_AB X_eq_min using step₁,

  -- We now consider the graph G−e.
  let G₂ : simple_graph V := G-e,

  have G₂_le_n : fintype.card G₂.step ≤ n :=
  nat.le_of_lt_succ (nat.lt_of_lt_of_le minus_lt_edges hG),

  -- Since x,y ∈ X, every AX-separator in G−e is also an AB-separator in G and hence contains at
  -- least k vertices, so by induction there are k disjoint AX paths in G−e
  have : ∃ P : finset (AB_walk' G A X), pw_disjoint' P ∧ P.card = X.card :=
  by { choose P h₁ h₂ using ih G₂ G₂_le_n A X, use image (massage minus_le) P, split,
    { exact massage_disjoint h₁ },
    { apply (massage_card h₁).trans, rcases min_cut_set G₂ A X with ⟨Z,Z_eq_min,Z_sep₂_AB⟩,
      apply le_antisymm (path_le_B h₁), rw [X_eq_min, h₂, ←Z_eq_min], apply min_cut_spec,
      exact sep_AB_of_sep₂_AX ex_in_X ey_in_X X_sep_AB Z_sep₂_AB } },
  choose P P_dis P_eq_min using this,

  -- and similarly there are k disjoint XB paths in G−e
  have : ∃ Q : finset (AB_walk' G X B), pw_disjoint' Q ∧ Q.card = X.card :=
  by { choose Q h₁ h₂ using ih G₂ G₂_le_n X B, use image (massage minus_le) Q, split,
    { exact massage_disjoint h₁ },
    { apply (massage_card h₁).trans, rcases min_cut_set G₂ X B with ⟨Z,Z_eq_min,Z_sep₂_AB⟩,
      apply le_antisymm (path_le_A h₁), rw [X_eq_min, h₂, ←Z_eq_min], apply min_cut_spec,
      exact (sep_AB_of_sep₂_AX ex_in_X ey_in_X X_sep_AB.symm Z_sep₂_AB.symm).symm } },
  choose Q Q_dis Q_eq_min using this,

  let φ : P → X := λ p, let q := p.val.to_AB_walk in ⟨q.p.b,q.hb⟩,
  have φ_inj : injective φ :=
  by { rintro p₁ p₂ h, simp at h, apply P_dis, use p₁.val.to_AB_walk.p.b, simp, simp [h] },
  have φ_bij : bijective φ :=
  by { rw fintype.bijective_iff_injective_and_card, refine ⟨φ_inj,_⟩, simp, sorry },

  let ψ : Q → X := λ p, let q := p.val.to_AB_walk in ⟨q.p.a,q.ha⟩,
  have ψ_inj : injective ψ :=
  by { rintro p₁ p₂ h, simp at h, apply Q_dis, use p₁.val.to_AB_walk.p.a, simp, simp [h] },
  have ψ_bij : bijective ψ :=
  by { rw fintype.bijective_iff_injective_and_card, refine ⟨ψ_inj,_⟩, sorry },

  sorry
end

lemma lower_bound : ∃ P : finset (AB_walk G A B), pw_disjoint P ∧ P.card = min_cut G A B :=
lower_bound_aux (fintype.card G.step) G (le_of_eq rfl) A B

-- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h
end menger
end simple_graph

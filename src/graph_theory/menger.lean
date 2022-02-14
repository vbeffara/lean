import combinatorics.simple_graph.connectivity data.finset data.setoid.basic
import graph_theory.contraction graph_theory.pushforward graph_theory.basic graph_theory.walk
open finset classical function
open_locale classical

variables {V V' : Type} {a : V} {G : simple_graph V}

namespace simple_graph
namespace menger
variables [fintype V] [fintype V'] {A B X Y Z : finset V}

@[ext] structure AB_walk (G : simple_graph V) (A B : finset V) :=
  (p : Walk G) (ha : p.a ∈ A) (hb : p.b ∈ B)

def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
  ∀ γ : AB_walk G A B, (γ.p.range ∩ X).nonempty

lemma separates_self : separates G A B A :=
  λ γ, ⟨γ.p.a, mem_inter.mpr ⟨Walk.start_mem_range,γ.ha⟩⟩

lemma separates_trans : separates G A B X → separates G A X Z → separates G A B Z :=
begin
  rintro sep₁ sep₂ γ, choose x hx using sep₁ γ,
  rcases γ.p.until X ⟨x,hx⟩ with ⟨δ',h₁,h₂,h₃,h₄⟩,
  let δ : AB_walk G A X := ⟨δ', (by { rw h₁, exact γ.ha }), h₂⟩,
  choose z hz using sep₂ δ, use z, simp at hz ⊢,
  exact ⟨finset.mem_of_subset h₃ hz.1, hz.2⟩
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

lemma path_le_cut (dis : pw_disjoint P) (sep : separates G A B X) : P.card ≤ X.card :=
begin
  let φ : Π γ : P, γ.val.p.range ∩ X := λ γ, by { choose z hz using sep γ, exact ⟨z,hz⟩ },
  let ψ : P → X := λ γ, ⟨_, finset.mem_of_mem_inter_right (φ γ).prop⟩,
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
    apply finset.mem_of_subset h, simp, exact ⟨ha,hb⟩ }
end

lemma bot_min_cut : min_cut ⊥ A B = (A ∩ B).card :=
begin
  apply (nat.find_eq_iff _).mpr, simp [bot_separates_iff], split,
  { use A ∩ B, exact ⟨rfl,subset.rfl⟩ },
  { rintros n h₁ X rfl h₂, have := finset.card_le_of_subset h₂, linarith }
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
  { rw [card_image_of_injective univ φ_inj, finset.card_univ],
    convert fintype.card_of_finset (A ∩ B) _, intro z, simp, split,
    { rintros ⟨h₁,h₂⟩, exact set.mem_sep h₁ h₂ },
    { rintros h₁, exact h₁ } }
end

variables {f : V → V'} {hf : adapted' f G}

noncomputable def AB_lift (f : V → V') (hf : adapted' f G) (A B : finset V) :
  AB_walk (push f G) (A.image f) (B.image f) → AB_walk G A B :=
begin
  rintro ⟨p,ha,hb⟩,
  choose a h₂ h₃ using finset.mem_image.mp ha,
  choose b h₅ h₆ using finset.mem_image.mp hb,
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
  choose γ'₁ h'₁ h''₁ using finset.mem_image.mp h₁,
  choose γ'₂ h'₂ h''₂ using finset.mem_image.mp h₂,
  have h₃ := congr_arg (AB_push f A B) h''₁, rw AB_push_lift at h₃,
  have h₄ := congr_arg (AB_push f A B) h''₂, rw AB_push_lift at h₄,
  suffices : γ'₁ = γ'₂, { rw [←h''₁,←h''₂,this] },
  have := @hP' ⟨_,h'₁⟩ ⟨_,h'₂⟩, simp at this, apply this,
  simp [h₃,h₄,AB_push,Walk.push_range], use f z, rw mem_inter at h ⊢, split,
  exact mem_image_of_mem f h.1, exact mem_image_of_mem f h.2
end

noncomputable def AB_shorten (p : AB_walk G A B) (C : finset V) (hpc : (p.p.range ∩ C).nonempty) :
  AB_walk G A C :=
let q := p.p.until C hpc in ⟨q, by { rw q.prop.1, exact p.ha }, q.prop.2.1⟩

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
    let A₁ : finset G₁.vertices := finset.image (merge_edge e) A,
    let B₁ : finset G₁.vertices := finset.image (merge_edge e) B,

    obtain ⟨Y, Y_eq_min₁, Y_sep⟩ := min_cut_set G₁ A₁ B₁, let X := Y ∪ {e.y},

    have Y_lt_min : Y.card < min_cut G A B :=
    by { have G₁_le_n : fintype.card G₁.step ≤ n :=
      by { refine nat.le_of_lt_succ (nat.lt_of_lt_of_le _ hG),
        refine fintype.card_lt_of_injective_of_not_mem _ push.lift_step_inj _,
        exact e, exact push.lift_step_ne_mem (by {simp [merge_edge]}) },
      choose P₁ P₁_dis P₁_eq_min₁ using ih G₁ G₁_le_n A₁ B₁,
      rw [Y_eq_min₁, ←P₁_eq_min₁, ←finset.card_image_of_injective P₁ AB_lift_inj],
      apply too_small, { apply AB_lift_dis, exact P₁_dis }, { exact merge_edge_adapted } },

    have X_sep_AB : separates G A B X :=
    by { intro γ, choose z hz using Y_sep (AB_push (merge_edge e) A B γ),
      rw [mem_inter,AB_push,Walk.push_range,finset.mem_image] at hz,
      choose x hx₁ hx₂ using hz.1, by_cases x = e.y; simp [merge_edge,h] at hx₂,
      { use x, simp, split, exact hx₁, right, exact h },
      { use x, simp, split, exact hx₁, left, rw hx₂, exact hz.2 } },

    refine ⟨X, _, _, X_sep_AB, _⟩,

    { rw [mem_union], left, by_contradiction,
      suffices : separates G A B Y, by { exact not_lt_of_le (min_cut_spec this) Y_lt_min },
      intro p, choose z hz using Y_sep (AB_push (merge_edge e) A B p), use z,
      rw mem_inter at hz ⊢, rcases hz with ⟨hz₁,hz₂⟩, refine ⟨_,hz₂⟩,
      rw [AB_push,Walk.push_range,finset.mem_image] at hz₁, choose x hx₁ hx₂ using hz₁,
      by_cases x = e.y; simp [merge_edge,h] at hx₂,
      { rw [←hx₂] at hz₂, contradiction },
      { rwa [←hx₂] } },
    { rw [mem_union,mem_singleton], right, refl },
    { refine le_antisymm _ (min_cut_spec X_sep_AB),
      exact (finset.card_union_le _ _).trans (nat.succ_le_of_lt Y_lt_min) }
  },

  choose X ex_in_X ey_in_X X_sep_AB X_eq_min using step₁,

  -- We now consider the graph G−e.
  let G₂ : simple_graph V := {
    adj := λ x y, G.adj x y ∧ ((x ≠ e.x ∧ x ≠ e.y) ∨ (y ≠ e.x ∧ y ≠ e.y)),
    symm := λ x y ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
    loopless := λ x h, G.loopless _ h.1 },

  have G₂_le_n : fintype.card G₂.step ≤ n :=
  by { refine nat.le_of_lt_succ (nat.lt_of_lt_of_le _ hG),
    let φ : G₂.step → G.step := λ e, ⟨e.h.1⟩,
    have φ_inj : injective φ := by { rintro e₁ e₂ h, simp [φ] at h, exact e₁.ext e₂ h.1 h.2 },
    suffices : e ∉ set.range φ, refine fintype.card_lt_of_injective_of_not_mem φ φ_inj this,
    intro he, rw set.mem_range at he, choose e' he using he, rcases e' with ⟨x,y,he'⟩,
    have : x = e.x := congr_arg step.x he, have : y = e.y := congr_arg step.y he,
    substs x y, simp at he', exact he' },

  -- Since x,y ∈ X, every AX-separator in G−e is also an AB-separator in G and hence contains at
  -- least k vertices, so by induction there are k disjoint AX paths in G−e
  have sep_AB_of_sep₂_AX : separates G₂ A X ≤ separates G A B := by {
    rintro Z Z_sep₂_AX γ,
    rcases γ.p.until X (X_sep_AB γ) with ⟨δ,δ_a,δ_b,δ_range,δ_init⟩,
    have : δ.transportable_to G₂ := by {
      revert δ_init, refine Walk.rec₀ _ _ δ,
      { simp [Walk.transportable_to,Walk.edges] },
      { rintro e' p h ih h₁ e'' h₂,
        have h₃ : ¬ (p.init ∩ X).nonempty :=
        by { revert h₁, apply mt, push_neg, intro h, rcases h with ⟨z,hz⟩, use z,
          simp at hz ⊢, split, right, exact hz.1, exact hz.2 },
        specialize ih h₃,
        simp at h₂, cases h₂,
        { subst e'', simp at h₁, simp [G₂,e'.h],
          have : e'.x ∉ X :=
          by { intro h,
            have : e'.x ∈ {e'.x} ∪ p.init := by { simp },
            have := finset.mem_inter.mpr ⟨this,h⟩,
            have : (({e'.x} ∪ p.init) ∩ X).nonempty := by { use e'.x, exact this },
            rw h₁ at this, simp at this, contradiction },
            left, split; { intro h, rw h at this, contradiction } },
        { exact ih e'' h₂ }
      }
    },
    rcases δ.transport this with ⟨ζ,ζ_a,ζ_b,ζ_range⟩,
    let ζ' : AB_walk G₂ A X := ⟨ζ, by { rw [ζ_a,δ_a], exact γ.ha }, by { rw [ζ_b], exact δ_b }⟩,
    rcases Z_sep₂_AX ζ' with ⟨z,hz⟩, use z,
    rw ←ζ_range at δ_range, rw mem_inter at hz ⊢,
    exact ⟨finset.mem_of_subset δ_range hz.1, hz.2⟩,
  },

  have : ∃ P₂ : finset (AB_walk G₂ A X), pw_disjoint P₂ ∧ min_cut G A B ≤ P₂.card :=
  by { have sep_AB_of_sep₂_AX : separates G₂ A X ≤ separates G A B := sep_AB_of_sep₂_AX,
    choose P₂ h₁ h₂ using ih G₂ G₂_le_n A X, refine ⟨P₂,h₁, _⟩, rw h₂,
    rcases min_cut_set G₂ A X with ⟨Z,Z_eq_min,Z_sep₂_AB⟩, rw ←Z_eq_min,
    exact min_cut_spec (sep_AB_of_sep₂_AX Z Z_sep₂_AB) },
  choose P₂ P₂_dis P₂_eq_min using this,

  -- and similarly there are k disjoint XB paths in G−e
  have : ∃ P'₂ : finset (AB_walk G₂ X B), pw_disjoint P'₂ ∧ P'₂.card = min_cut G A B := sorry,
  choose P'₂ P'₂_dis P'₂_eq_min using this,

  -- As X separates A from B, these two path systems do not meet outside X
  have meet_sub_X : ∀ (p : AB_walk G₂ A X) (q : AB_walk G₂ X B), p.p.range ∩ q.p.range ⊆ X := sorry,

  -- and can thus be combined to k disjoint AB paths.
  sorry
end

lemma lower_bound : ∃ P : finset (AB_walk G A B), pw_disjoint P ∧ P.card = min_cut G A B :=
lower_bound_aux (fintype.card G.step) G (le_of_eq rfl) A B

-- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
-- sorry
end menger
end simple_graph

import tactic data.equiv.basic
import graph_theory.pushforward graph_theory.path
open function classical

variables {V V' V'' : Type*} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
variables {G H : simple_graph V} {G' H' : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph

def adapted (f : V → V') (G : simple_graph V) : Prop :=
∀ (z : V'), connected (level f z G)

def adapted' (f : V → V') (G : simple_graph V) : Prop :=
∀ (x y : V), f x = f y → ∃ p : walk G x y, ∀ z ∈ p.support, f z = f y

lemma merge_edge_adapted [decidable_eq V] {e : G.dart} : adapted' (merge_edge e) G :=
begin
  intros x y hxy, rcases e with ⟨⟨u,v⟩,e⟩, have : u ≠ v := G.ne_of_adj e,
  have l₁ : ∀ {z}, z = u ∨ z = v → merge_edge ⟨⟨_,_⟩,e⟩ z = u :=
    by { intros z hz, cases hz; simp [merge_edge,update,hz] },
  have l₂ : ∀ {z}, ¬(z = u ∨ z = v) → merge_edge ⟨⟨_,_⟩,e⟩ z = z :=
    by { simp [merge_edge,update], intros z hz h', simp [h'] at hz, contradiction },
  by_cases hx : x = u ∨ x = v; by_cases hy : y = u ∨ y = v,
  { cases hx; cases hy; substs x y,
    { use walk.nil, intros z hz, simp at hz, rw hz },
    { use walk.nil.cons e, intros z hz, simp at hz, cases hz; subst hz, exact hxy },
    { use walk.nil.cons e.symm, intros z hz, simp at hz, cases hz; subst hz, exact hxy },
    { use walk.nil, intros z hz, simp at hz, rw hz } },
  { rw [l₁ hx, l₂ hy] at hxy, subst hxy, simp at hy, contradiction },
  { rw [l₁ hy, l₂ hx] at hxy, subst hxy, simp at hx, contradiction },
  { rw [l₂ hx, l₂ hy] at hxy, subst y, use walk.nil, intros z hz, simp at hz, rw hz }
end

namespace adapted

lemma of_injective : injective f → adapted' f G :=
begin
  rintro hf x y h, have := hf h, subst this, use walk.nil,
  rintro z, simp only [walk.support_nil, list.mem_singleton], exact congr_arg f
end

lemma iff : adapted f G ↔ adapted' f G :=
begin
  split,
  { rintro h x y hxy, obtain ⟨p⟩ := h (f y) ⟨x,hxy⟩ ⟨y,rfl⟩,
    use select.pull_walk p, exact select.pull_walk_spec p },
  { rintros h₁ z ⟨x,hx⟩ ⟨y,rfl⟩, obtain ⟨p,hp⟩ := h₁ x y hx, use select.push_walk p hp }
end

noncomputable def lift_path_aux (hf : adapted' f G) (p : walk (map f G) x' y') :
  Π (x y : V), f x = x' → f y = y' → {q : walk G x y // ∀ z ∈ q.support, f z ∈ p.support} :=
begin
  induction p with a a b c h₁ p ih,
  { rintros x y h₁ rfl, choose p hp using hf x y h₁,
    refine ⟨p, λ z hz, _⟩, rw hp z hz, apply walk.start_mem_support },
  { rintro x y rfl rfl, cases h₁ with h₁ h₂,
    choose xx hx using h₂, choose yy hy using hx, rcases hy with ⟨h₂,h₃,h₄⟩,
    choose pp hp using hf x xx h₃.symm, use pp.append (walk.cons h₂ $ ih yy y h₄ rfl),
    rintro z hz, rw [walk.support_append, list.mem_append] at hz, cases hz,
    { left, rw hp z hz, exact h₃ },
    { rw [walk.support_cons, list.tail_cons] at hz, right, exact (ih yy y h₄ rfl).prop z hz } }
end

noncomputable def lift_path (hf : adapted' f G) (p : walk (map f G) x' y') :
  Π (x y : V), f x = x' → f y = y' → walk G x y :=
λ x y hx hy, (lift_path_aux hf p x y hx hy).val

lemma mem_lift_path {hf : adapted' f G} {p : (map f G).walk x' y'} {hx : f x = x'} {hy : f y = y'} :
  z ∈ (lift_path hf p x y hx hy).support → f z ∈ p.support :=
(lift_path_aux hf p x y hx hy).prop z

noncomputable def lift_path' (hf : adapted' f G) (p : walk (map f G) (f x) (f y)) : walk G x y :=
lift_path hf p x y rfl rfl

lemma mem_lift_path' {hf : adapted' f G} {p : (map f G).walk (f x) (f y)} :
  z ∈ (lift_path' hf p).support → f z ∈ p.support :=
mem_lift_path

lemma connected (hf : adapted' f G) : connected (map f G) → connected G :=
begin
  intros h₁ x y, obtain ⟨p⟩ := h₁ (f x) (f y), use lift_path' hf p
end

end adapted

namespace adapted'
lemma fmap (hf : adapted' f G) {P} : adapted' (select.fmap f P) (select (P ∘ f) G) :=
begin
  rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy, simp only [select.fmap, subtype.coe_mk] at hxy,
  obtain ⟨p,hp⟩ := hf x y hxy, refine ⟨select.push_walk p _, _⟩,
  { rintro z hz, rw ← hp z hz at hy, exact hy },
  rintro ⟨z,hz⟩ h, simp only [select.fmap, subtype.coe_mk],
  exact hp z (select.mem_push_walk.mp h)
end

lemma comp_push : adapted' f G → adapted' g (map f G) → adapted' (g ∘ f) G :=
begin
  rintro hf hg x y hxy, obtain ⟨p, hp⟩ := hg (f x) (f y) hxy,
  exact ⟨adapted.lift_path' hf p, λ z hz, hp (f z) (adapted.mem_lift_path' hz)⟩,
end
end adapted'

def is_contraction (G : simple_graph V) (G' : simple_graph V') : Prop :=
∃ φ : V' → V, surjective φ ∧ adapted' φ G' ∧ G = map φ G'

infix ` ≼c `:50 := is_contraction

namespace is_contraction

@[refl] lemma refl : G ≼c G :=
⟨id,surjective_id,adapted.of_injective injective_id,map.id.symm⟩

lemma of_iso : G ≃g G' → G ≼c G' :=
λ φ, let ψ := φ.symm in ⟨ψ, ψ.surjective, adapted.of_injective ψ.injective, map.from_iso ψ⟩

@[trans] lemma trans : G ≼c G' → G' ≼c G'' → G ≼c G'' :=
begin
  rintros ⟨φ,h₁,h₂,rfl⟩ ⟨ψ,h₄,h₅,rfl⟩,
  exact ⟨φ ∘ ψ, h₁.comp h₄, h₅.comp_push h₂, congr_fun map.comp.symm G''⟩,
end

lemma iso_left : G ≃g G' -> G' ≼c G'' -> G ≼c G'' :=
trans ∘ of_iso

lemma le_left_aux {f : V → V'} : H' ≤ map f G → H' = map f (G ⊓ pull' f H') :=
begin
  intro h₁, ext x' y', split,
  { intro h, rcases h₁ h with ⟨h₄,x,y,h₅,rfl,rfl⟩,
    exact ⟨h₄,x,y,⟨h₅,h₄ ∘ congr_arg f,or.inr h⟩,rfl,rfl⟩ },
  { rintros ⟨h₄,x,y,⟨-,-,h₇⟩,rfl,rfl⟩, cases h₇, contradiction, exact h₇ }
end

lemma le_left_aux2 {f : V → V'} (h₁ : H' ≤ map f G) (h₂ : surjective f) (h₃ : adapted' f G) :
  H' ≼c G ⊓ pull' f H' :=
begin
  refine ⟨f,h₂,_,le_left_aux h₁⟩,
  intros x' y' h₄, specialize h₃ x' y' h₄,
  cases h₃ with p hp, induction p with a a b c h₅ p ih,
  { use walk.nil, exact hp },
  { have h₆ : f b = f c := by { apply hp, right, exact walk.start_mem_support p },
    have h₇ : ∀ (z : V), z ∈ p.support → f z = f c := by { intros z h, apply hp, right, exact h},
    have h₈ : (G ⊓ pull' f H').adj a b :=
      by { split, exact h₅, refine ⟨G.ne_of_adj h₅,_⟩, left, rwa h₆ },
    specialize ih h₆ h₇, cases ih with q h₉, use walk.cons h₈ q,
    intros z h, cases h, rwa h, exact h₉ z h }
end

lemma le_left : H ≤ G → G ≼c G' → ∃ H' : simple_graph V', H ≼c H' ∧ H' ≤ G' :=
by { rintros h₁ ⟨f,h₂,h₃,rfl⟩, exact ⟨G' ⊓ pull' f H, le_left_aux2 h₁ h₂ h₃, λ x y h, h.1⟩ }

lemma select_left {P : V → Prop} : G ≼c G' -> ∃ P' : V' → Prop, select P G ≼c select P' G' :=
begin
  rintros ⟨f,h₁,h₂,h₃⟩, use (λ x, P (f x)), refine ⟨select.fmap f P, _, h₂.fmap, _⟩,
  { rintro ⟨x,py⟩, cases h₁ x with x', refine ⟨⟨x',_⟩,_⟩, rwa h, ext, exact h },
  { ext ⟨x,hx⟩ ⟨y,hy⟩, simp only [select, pull, on_fun, subtype.val_eq_coe], split,
    { intro h₄, rw h₃ at h₄, rcases h₄ with ⟨h₄,x',y',h₅,h₆,h₇⟩,
      simp only [subtype.coe_mk] at h₆ h₇, substs h₆ h₇,
      refine ⟨_,⟨x',hx⟩,⟨y',hy⟩,h₅,rfl,rfl⟩,
      intro h, rw subtype.ext_iff at h, contradiction },
    { rintros ⟨h₄,⟨x',hx⟩,⟨y',hy⟩,h₅,h₆,h₇⟩, rw h₃, refine ⟨_,x',y',h₅,_,_⟩,
      { intro h, rw ←subtype.ext_iff at h, contradiction },
      { simp only [select.fmap, subtype.map] at h₆, exact h₆ },
      { simp only [select.fmap, subtype.map] at h₇, exact h₇ } } }
end

end is_contraction
end simple_graph

import tactic
import graph_theory.path_embedding graph_theory.contraction
open function

namespace simple_graph
open walk classical

universe u
variables {V V' V'' : Type u}
variables {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop :=
∃ {V'' : Type u} (G'' : simple_graph V''), G ≼c G'' ∧ G'' ≼s G'

def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

infix ` ≼ `:50 := is_minor
infix ` ⋠ `:50 := is_forbidden

namespace is_minor

lemma of_iso : G ≃g G' → G ≼ G' :=
λ φ, ⟨V', G', is_contraction.of_iso φ, by refl⟩

lemma iso_left : G ≃g G' -> G' ≼ G'' -> G ≼ G'' :=
λ h₁ ⟨U,H,h₂,h₃⟩, ⟨_,_,h₂.iso_left h₁,h₃⟩

lemma le_left : G ≤ H -> H ≼ G' -> G ≼ G' :=
begin
  rintro h₁ ⟨U,H',h₂,h₃⟩,
  obtain ⟨H'',h₄,h₅⟩ := h₂.le_left h₁,
  exact ⟨_,_,h₄,h₃.le_left h₅⟩
end

lemma select_left {P : V → Prop} : G ≼ G' -> select P G ≼ G' :=
begin
  rintro ⟨U,H',h₂,h₃⟩,
  obtain ⟨P,h₄⟩ := h₂.select_left,
  exact ⟨_,_,h₄,h₃.select_left⟩
end

lemma smaller_left : G ≼s G' -> G' ≼ G'' -> G ≼ G'' :=
begin
  rintro ⟨f₁,h₁⟩ h₂,
  let H := embed f₁ G,
  let H' := select (set.range f₁) G',
  have h₃ : H' ≼ G'' := select_left h₂,
  have h₄ : H ≼ G'' := le_left (embed.le_select h₁) h₃,
  exact iso_left (embed.iso h₁) h₄
end

lemma contract_left : G ≼c G' -> G' ≼ G'' -> G ≼ G'' :=
λ h₁ ⟨U,H,h₂,h₃⟩, ⟨_,_,h₁.trans h₂,h₃⟩

@[refl] lemma refl : G ≼ G
:= ⟨_,G,is_contraction.refl,is_smaller.refl⟩

@[trans] lemma trans : G ≼ G' -> G' ≼ G'' -> G ≼ G'' :=
λ ⟨U,H,h1,h2⟩ h3, is_minor.contract_left h1 (is_minor.smaller_left h2 h3)

end is_minor
end simple_graph

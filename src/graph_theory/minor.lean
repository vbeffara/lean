import tactic
import graph_theory.basic graph_theory.path_embedding graph_theory.contraction
open function
open_locale classical

namespace simple_graph
    open walk classical
    variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ {V'' : Type} (G'' : simple_graph V''), G ≼c G'' ∧ G'' ≼s G'

    def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

    infix ` ≼ `:50 := is_minor
    infix ` ⋠ `:50 := is_forbidden

    namespace is_minor
        lemma iso_left : G ≃g G' -> G' ≼ G'' -> G ≼ G''
            | h₁ ⟨U,H,h₂,h₃⟩ := ⟨_,_,h₂.iso_left h₁,h₃⟩

        lemma le_left : G ≤ H -> H ≼ G' -> G ≼ G'
            | h₁ ⟨U,H',h₂,h₃⟩ := by {
                obtain ⟨H'',h₄,h₅⟩ := h₂.le_left h₁,
                exact ⟨_,_,h₄,h₃.le_left h₅⟩ }

        lemma select_left {P : V → Prop} : G ≼ G' -> select G P ≼ G'
            | ⟨U,H',h₂,h₃⟩ := by {
                obtain ⟨P,h₄⟩ := h₂.select_left,
                exact ⟨_,_,h₄,h₃.select_left⟩
            }

        lemma smaller_left : G ≼s G' -> G' ≼ G'' -> G ≼ G''
            | ⟨f₁,h₁⟩ h₂ :=
                let H := embed f₁ G,
                    H' := select G' (λ y, ∃ x, f₁ x = y) in
                have h₃ : H' ≼ G'' := select_left h₂,
                have h₄ : H ≼ G'' := le_left (embed_le_select h₁) h₃,
                iso_left (embed_iso h₁) h₄

        lemma contract_left : G ≼c G' -> G' ≼ G'' -> G ≼ G''
            | h₁ ⟨U,H,h₂,h₃⟩ := ⟨_,_,h₁.trans h₂,h₃⟩

        @[refl] lemma refl : G ≼ G := ⟨_,G,is_contraction.refl,is_smaller.refl⟩

        @[trans] lemma trans : G ≼ G' -> G' ≼ G'' -> G ≼ G''
            | ⟨U,H,h1,h2⟩ h3 := is_minor.contract_left h1 (is_minor.smaller_left h2 h3)
    end is_minor
end simple_graph

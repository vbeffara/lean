import tactic
import graph_theory.basic graph_theory.path_embedding graph_theory.contraction
open function
open_locale classical

namespace simple_graph
    open walk
    variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ {V'' : Type} (G'' : simple_graph V''), G ≼c G'' ∧ G'' ≼s G'

    def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

    infix ` ≼ `:50 := is_minor
    infix ` ⋠ `:50 := is_forbidden

    lemma is_minor.then_contraction : G ≼ G' -> G' ≼c G'' -> G ≼ G''
        := sorry

    lemma is_minor.then_smaller : G ≼ G' -> G' ≼s G'' -> G ≼ G''
        := sorry

    namespace minor
        lemma alt : G ≼s G' -> G' ≼c G'' -> G ≼ G''
            | ⟨f₁,h₁⟩ ⟨S,⟨f₂⟩⟩ := by {
                let U := { v // ∃ u, f₂ u = S.proj v }, use U,
                let H : simple_graph U := {
                    adj := G''.adj on subtype.val,
                    symm := λ _ _ h, G''.symm h,
                    loopless := λ _ h, G''.loopless _ h
                }, use H, split,
                {
                    let S' : contraction.setup H := {
                        g := {
                            adj := S.g.adj on subtype.val,
                            symm := λ _ _ h, S.g.symm h,
                            loopless := λ _ h, S.g.loopless _ h
                        },
                        sub := λ a b h, S.sub h
                    }, use S',
                    let φ : G ≃g H/S' := sorry, use φ
                },
                { exact ⟨⟨subtype.val, λ _ _ h, h⟩, subtype.val_injective⟩ }
            }

        @[refl] lemma refl : G ≼ G := ⟨_,G,contraction.refl,is_smaller.refl⟩

        @[trans] lemma trans : G ≼ G' -> G' ≼ G'' -> G ≼ G''
            | ⟨U,H,h1,h2⟩ ⟨U',H',h3,h4⟩ := by {
                rcases (alt h2 h3) with ⟨V,K,h5,h6⟩,
                exact ⟨V,K,h1.trans h5,h6.trans h4⟩
            }
    end minor
end simple_graph

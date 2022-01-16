import tactic
import graph_theory.basic graph_theory.path_embedding graph_theory.contraction
open function
open_locale classical

namespace simple_graph
    open walk classical
    variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ {V'' : Type} (G'' : simple_graph V''), G ≼c G'' ∧ G'' ≼s G'

    def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

    infix ` ≼ `:50 := is_minor
    infix ` ⋠ `:50 := is_forbidden

    namespace is_minor
        lemma iso_left : G ≃g G' -> G' ≼ G'' -> G ≼ G''
            := sorry

        lemma then_contraction : G ≼ G' -> G' ≼c G'' -> G ≼ G''
            := sorry

        lemma then_smaller : G ≼ G' -> G' ≼s G'' -> G ≼ G''
            := sorry
    end is_minor

    namespace minor
        lemma toto : G ≼s G' -> G' ≼c G'' -> G ≼ G''
            := by {
                rintros ⟨f₁,h₁⟩ ⟨S,⟨f₂⟩⟩,
                have h₂ := embed_iso h₁ G, refine is_minor.iso_left h₂ _,
            }

        lemma alt : G ≼s G' -> G' ≼c G'' -> G ≼ G''
            | ⟨f₁,h₁⟩ ⟨S,⟨f₂⟩⟩ := by {
                let U₀ := { y : V' // ∃ x : V, y = f₁ x },
                let G₀ : simple_graph U₀ := {
                    adj := G'.adj on subtype.val,
                    symm := λ _ _ h, G'.symm h,
                    loopless := λ _ h, G'.loopless _ h
                },

                let Φ : G ≃g G₀ := {
                    to_fun := λ x, ⟨f₁ x, x, rfl⟩,
                    inv_fun := λ y, some y.property,
                    left_inv := λ x, h₁ (some_spec (⟨f₁ x, x, rfl⟩ : U₀).property).symm ,
                    right_inv := λ y, (by { cases y with y h, cases h with x hx, subst hx,
                        simp, exact (some_spec (⟨f₁ x, x, rfl⟩ : U₀).property).symm }),
                    map_rel_iff' := λ a b, by {
                        simp, sorry -- wrong!
                    }
                },

                let U := { v : V'' // ∃ u : V, f₂ (f₁ u) = S.proj v }, use U,
                let H : simple_graph U := {
                    adj := G''.adj on subtype.val,
                    symm := λ _ _ h, G''.symm h,
                    loopless := λ _ h, G''.loopless _ h
                }, use H,

                split,
                {
                    let S' : contraction.setup H := {
                        g := {
                            adj := S.g.adj on subtype.val,
                            symm := λ _ _ h, S.g.symm h,
                            loopless := λ _ h, S.g.loopless _ h
                        },
                        sub := λ a b h, S.sub h
                    }, use S',

                    let φ₁ : V -> S'.clusters := λ v, S'.proj ⟨(f₂ (f₁ v)).out, v, (quotient.out_eq _).symm⟩,
                    let φ₂ : S'.clusters -> V := λ v, some v.out.property,

                    have ψ : ∀ (v : S'.clusters), f₂ (f₁ (φ₂ v)) = S.proj v.out.val
                        := λ v, some_spec v.out.property,

                    have p₁ : ∀ (x : V), φ₂ (φ₁ x) = x := by {
                        intro x, simp only [φ₁], apply h₁,
                        have := f₂.left_inv.injective, simp at this, apply this,
                        rw ψ _, sorry
                    },

                    have p₂ : ∀ (x : S'.clusters), φ₁ (φ₂ x) = x := by {
                        intro x, simp only [φ₁], have := ψ x, simp only [this], sorry
                    },

                    let φ : G ≃g H/S' := {
                        to_fun := φ₁,
                        inv_fun := φ₂,
                        left_inv := p₁,
                        right_inv := p₂,
                        map_rel_iff' := sorry
                    }, use φ
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

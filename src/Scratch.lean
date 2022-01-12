import init.function data.quot tactic
open function classical quotient

lemma toto : ∀ (V : Type) (s : setoid V) (s' : setoid (quotient s)),
        ∃ (s'' : setoid V) (φ : quotient s'' -> quotient s'), bijective φ

    := by { intros, cases s with r hᵣ, cases s' with r' hᵣ',

        let r'' := λ x y, r' (quot.mk r x) (quot.mk r y),

        have eqv : equivalence r''
            := ⟨λ _, hᵣ'.1 _, λ _ _ h, hᵣ'.2.1 h, λ x y z h1 h2, hᵣ'.2.2 h1 h2⟩,

        have eqv_r' : eqv_gen r' = r' := equivalence.eqv_gen_eq hᵣ',
        have eqv_r'' : eqv_gen r'' = r'' := equivalence.eqv_gen_eq eqv,

        let φ := λ xx, quot.mk r' (quot.mk r (quot.out xx)),
        let ψ := λ xx, quot.mk r'' (quot.out (quot.out xx)),

        have left_inv : left_inverse ψ φ, by {
            intro x, simp only [φ,ψ],
            refine eq.trans _ (quot.out_eq x),
            apply quot.eq.mpr,
            rw eqv_r'', simp only [r''], rw <-eqv_r',
            apply quot.eq.mp,
            rw [eqv_r',quot.out_eq,quot.out_eq] },

        have right_inv : right_inverse ψ φ, by {
            intro x, simp only [φ,ψ],
            have h0: ∀ {x y}, r'' x y = r' (quot.mk r x) (quot.mk r y) := λ x y, rfl,
            have h1 := quot.out_eq x,
            have h2 := quot.out_eq x.out,
            rw <-h1, rw <-h2,
            apply quot.eq.mpr,
            rw eqv_r', rw <-h0, rw <-eqv_r'',
            apply quot.eq.mp,
            rw [eqv_r'',quot.out_eq,quot.out_eq,quot.out_eq] },

        have : bijective φ
            := ⟨left_inverse.injective left_inv, right_inverse.surjective right_inv⟩,

        exact ⟨⟨r'',eqv⟩,φ,this⟩
    }

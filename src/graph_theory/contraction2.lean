import tactic data.equiv.basic
import graph_theory.path graph_theory.pushforward
open function classical

namespace simple_graph
    variables {V V' V'' : Type} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
    variables {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    def is_surjective_push (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ φ : V' -> V, surjective φ ∧ G = push φ G'

    lemma surjective_push_iff : (∃ S : setoid V', nonempty (G ≃g G'/S)) <-> is_surjective_push G G' :=
    begin
        split,
        { rintro ⟨S,⟨⟨f,f',h₁,h₂⟩,h₃⟩⟩,
            let φ : V' -> V := f' ∘ quotient.mk', refine ⟨φ,_,_⟩,
            { exact (left_inverse.right_inverse h₁).surjective.comp quotient.surjective_quotient_mk' },
            { ext a b, rw <-h₃, simp, split,
                { rintros ⟨p₁,x,y,p₂,p₃,p₄⟩, refine ⟨ne_of_apply_ne f p₁,x,y,_,_,p₄⟩,
                    convert congr_arg f' p₂, rw h₁, convert congr_arg f' p₃, rw h₁, },
                { rintros ⟨p₁,x,y,rfl,rfl,p₂⟩, refine ⟨h₁.injective.ne p₁,x,y,_,_,p₂⟩,
                    simp [φ], rw h₂, refl, simp [φ], rw h₂, refl } }
        },
        { rintro ⟨φ,h₁,h₂⟩, subst G,
            have K := @setoid.ker_apply_mk_out V' V φ,
            have L := surj_inv_eq h₁,
            let S : setoid V' := setoid.ker φ, use S,
            let ψ := (setoid.quotient_ker_equiv_of_surjective φ h₁).symm, refine ⟨⟨ψ,_⟩⟩,
            introv, split,
            { rintro ⟨p₁,x,y,p₂,p₃,p₄⟩, refine ⟨ne_of_apply_ne _ p₁,x,y,_,_,p₄⟩,
                simp [ψ,setoid.quotient_ker_equiv_of_surjective] at p₂,
                rw [<-K x,p₂], convert K (surj_inv h₁ a), exact (surj_inv_eq h₁ a).symm,
                simp [ψ,setoid.quotient_ker_equiv_of_surjective] at p₃,
                rw [<-K y,p₃], convert K (surj_inv h₁ b), exact (surj_inv_eq h₁ b).symm },
            { rintro ⟨p₁,x,y,rfl,rfl,p₂⟩, refine ⟨ψ.left_inv.injective.ne p₁,x,y,_,_,p₂⟩,
                simp [ψ,setoid.quotient_ker_equiv_of_surjective], apply quotient.eq.mpr,
                apply setoid.ker_def.mpr, rw L,
                simp [ψ,setoid.quotient_ker_equiv_of_surjective], apply quotient.eq.mpr,
                apply setoid.ker_def.mpr, rw L }
        }
    end

    def adapted (f : V → V') (G : simple_graph V) : Prop :=
        ∀ (z : V'), connected (level f z G)

    def adapted' (f : V → V') (G : simple_graph V) : Prop :=
        ∀ (x y : V), f x = f y → ∃ p : walk G x y, ∀ z ∈ p.support, f z = f y

    namespace adapted
        lemma of_injective : injective f → adapted f G :=
        by { rintros hf z ⟨x,hx⟩ ⟨y,rfl⟩, have := hf hx, subst this }

        lemma iff : adapted f G ↔ adapted' f G :=
        begin
            split,
            { rintros h₁ x y h₂, specialize h₁ (f y) ⟨x,h₂⟩ ⟨y,rfl⟩, obtain ⟨p⟩ := linked.linked_iff.mp h₁,
                use select.pull_walk p, exact select.pull_walk_spec p },
            { rintros h₁ z ⟨x,hx⟩ ⟨y,rfl⟩, apply linked.linked_iff.mpr,
                specialize h₁ x y hx, obtain ⟨p,hp⟩ := h₁, use select.push_walk p hp },
        end

        lemma comp_left (h : bijective g) : adapted f G → adapted (g ∘ f) G :=
        begin
            simp_rw adapted.iff, rintros h₁ x y h₂, specialize h₁ x y (h.injective h₂), cases h₁ with p h₃, use p,
            intros z h₄, have := congr_arg g (h₃ z h₄), exact this
        end

        noncomputable def lift_path (hf : adapted f G) : walk (push f G) x' y' → Π (x y : V), f x = x' → f y = y' → walk G x y :=
        begin
            rw adapted.iff at hf, intro p, induction p with a a b c h₁ p ih,
            { rintros x y h₁ rfl, have h₂ := hf x y h₁, exact (some h₂) },
            { rintros x y h₂ h₃, cases h₁ with h₄ h₅, let xx := some h₅, have h₆ := some_spec h₅,
                let yy := some h₆, have h₇ := some_spec h₆, rcases h₇ with ⟨h₇,h₈,h₉⟩,
                have h₁₀ := hf x xx (h₂.trans h₇.symm), let p₁ := some h₁₀, refine p₁.append (walk.cons h₉ _),
                exact ih yy y h₈ h₃ }
        end

        noncomputable def lift_path' (hf : adapted f G) (p : walk (push f G) (f x) (f y)) : walk G x y :=
        lift_path hf p x y rfl rfl

        lemma connected (hf : adapted f G) : connected (push f G) → connected G :=
        begin
            intros h₁ x y, cases (linked.linked_iff.mp (h₁ (f x) (f y))) with p,
            apply linked.linked_iff.mpr, use lift_path' hf p,
        end

        lemma comp_push : adapted f G → adapted g (push f G) → adapted (g ∘ f) G :=
        begin
            intros hf hg z,
            let H := select (λ x, g (f x) = z) G,
            let ff := select.map f (λ x', g x' = z),
            have hff : adapted ff H := by { rintro ⟨z',hz'⟩,
                exact connected_of_iso select.level_map.symm (hf z') },
            have hpf : (push ff H).connected := by { dsimp only [ff,H], rw ←select.of_push, exact hg z },
            exact connected hff hpf,
        end
    end adapted

    def is_contraction2 (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ φ : V' → V, surjective φ ∧ adapted φ G' ∧ G = push φ G'

    infix ` ≼cc `:50 := is_contraction2

    namespace is_contraction2
        lemma of_iso : G ≃g G' → G ≼cc G' :=
        λ φ, let ψ := φ.symm in ⟨ψ, ψ.surjective, adapted.of_injective ψ.injective, push.from_iso ψ⟩

        @[trans] lemma trans : G ≼cc G' → G' ≼cc G'' → G ≼cc G'' :=
        begin
            rintros ⟨φ,h₁,h₂,rfl⟩ ⟨ψ,h₄,h₅,rfl⟩,
            exact ⟨φ ∘ ψ, h₁.comp h₄, h₅.comp_push h₂, push.comp.symm⟩,
        end

        lemma iso_left : G ≃g G' -> G' ≼cc G'' -> G ≼cc G'' :=
        trans ∘ of_iso
    end is_contraction2
end simple_graph

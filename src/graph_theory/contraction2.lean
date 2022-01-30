import tactic data.equiv.basic
import graph_theory.path graph_theory.pushforward graph_theory.contraction
open function
open_locale classical

namespace simple_graph
    variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}
    variables {f : V → V'} {g : V' → V''}

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
        ∀ (x y : V), f x = f y → ∃ p : walk G x y, ∀ z ∈ p.support, f z = f y

    def adapted' (f : V → V') (G : simple_graph V) : Prop :=
        ∀ (z : V'), connected (select (λ x, f x = z) G)

    namespace adapted
        lemma iff {f : V → V'} : adapted f G ↔ adapted' f G :=
        begin
            split,
            { rintros h₁ z ⟨x,hx⟩ ⟨y,rfl⟩, specialize h₁ x y hx, cases h₁ with p hp,
                let := select.push_walk p hp, apply linked.linked_iff.mpr, use this },
            { rintros h₁ x y h₂, specialize h₁ (f y) ⟨x,h₂⟩ ⟨y,rfl⟩, replace h₁ := linked.linked_iff.mp h₁,
                cases h₁ with p, let := select.pull_walk p, use this, exact select.pull_walk_spec p }
        end

        lemma comp_left (h : bijective g) : adapted f G → adapted (g ∘ f) G :=
        begin
            rintros h₁ x y h₂, specialize h₁ x y (h.injective h₂), cases h₁ with p h₃, use p,
            intros z h₄, have := congr_arg g (h₃ z h₄), exact this
        end
    end adapted

    def is_contraction2 (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ φ : V' → V, surjective φ ∧ adapted φ G' ∧ G = push φ G'

    infix ` ≼cc `:50 := is_contraction2

    lemma contraction_iff : G ≼c G' ↔ G ≼cc G' :=
    begin
        split,
        { rintro ⟨S,⟨⟨f,f',h₁,h₂⟩,h₃⟩⟩, simp [contraction] at h₃, let φ : V' -> V := f' ∘ quotient.mk', refine ⟨φ,_,_,_⟩,
            { exact (left_inverse.right_inverse h₁).surjective.comp quotient.surjective_quotient_mk' },
            { rw adapted.iff, intro z, intros x y, rcases x with ⟨x,hx⟩, rcases y with ⟨y,rfl⟩, simp [φ] at hx,
                replace hx := h₂.left_inverse.injective hx, replace hx := quotient.eq.mp hx,
                replace hx := linked.linked_iff.mp hx, cases hx with p,
                suffices : ∀ z ∈ p.support, φ z = φ y, by {
                    apply linked.linked_of_subgraph (select.mono S.sub),
                    apply linked.linked_iff.mpr,
                    use select.push_walk p this },
                induction p with a a b c hi p ih,
                { intros z h, cases h, rw h, cases h },
                { intros z h, cases h, rwa h, suffices : φ a = φ b, rw this at hx, exact ih hx z h,
                    simp [φ], apply congr_arg, apply quotient.eq.mpr, apply linked.step, exact hi }
            },
            { ext a b, rw <-h₃, split,
                { rintros ⟨p₁,x,y,p₂,p₃,p₄⟩, refine ⟨ne_of_apply_ne f p₁,x,y,_,_,p₄⟩,
                    convert congr_arg f' p₂, rw h₁, convert congr_arg f' p₃, rw h₁, },
                { rintros ⟨p₁,x,y,rfl,rfl,p₂⟩, refine ⟨h₁.injective.ne p₁,x,y,_,_,p₂⟩,
                    simp [φ], rw h₂, refl, simp [φ], rw h₂, refl } }
        },
        { rintro ⟨f,h₁,h₂,h₃⟩, subst h₃,
            let g : simple_graph V' := {
                adj := λ x' y', f x' = f y' ∧ G'.adj x' y',
                symm := λ x' y' ⟨h₁,h₂⟩, ⟨h₁.symm,h₂.symm⟩,
                loopless := λ x' ⟨h₁,h₂⟩, G'.ne_of_adj h₂ rfl },
            let S : contraction.setup G' := ⟨g, λ x' y' h, h.2⟩, use S, letI : setoid V' := S.setoid,
            let preimage : V → V' := λ x, classical.some (h₁ x),
            have p₂ : ∀ x, f (preimage x) = x := λ x, classical.some_spec (h₁ x),
            let F : V → S.clusters := λ x, ⟦preimage x⟧,
            let F' : S.clusters → V := λ x, f x.out,
            have p₃ : ∀ {x y}, S.g.linked x y ↔ f x = f y := by {
                intros x y, split,
                { intro h, induction h with a b h₁ h₂ h₃, refl, exact h₃.trans h₂.1 },
                { intro h, specialize h₂ x y h, cases h₂ with p hp, apply linked.linked_iff.mpr, refine ⟨_⟩,
                    induction p with a a b c h₃ p ih, refl,
                    have h₄ : f b = f c := by { apply hp, right, apply walk.start_mem_support },
                    refine walk.cons ⟨h.trans h₄.symm,h₃⟩ _, apply ih h₄, intros z hz, apply hp, right, exact hz }
            },
            have H₁ : left_inverse F' F := by {
                intro x, simp [F',F], refine eq.trans _ (p₂ x), apply p₃.mp,
                change ⟦preimage x⟧.out ≈ (preimage x), apply quotient.eq.mp, simp },
            have H₂ : right_inverse F' F := by {
                intro x', simp [F',F], refine eq.trans _ (quotient.out_eq _),
                apply quotient.eq.mpr, apply p₃.mpr, apply p₂ },
            refine ⟨⟨⟨F,F',H₁,H₂⟩,_⟩⟩,
            simp [push,contraction,contraction.setup.setoid,quotient_graph,F], intros a b, split,
            { rintros ⟨h₁,x,h₂,y,h₃,h₄⟩, refine ⟨_,x,_,y,_,h₄⟩,
                { intro h, rw h at h₁, contradiction },
                { rw ←p₂ a, apply p₃.mp, exact quotient.eq.mp h₂ },
                { rw ←p₂ b, apply p₃.mp, exact quotient.eq.mp h₃ } },
            { rintros ⟨h₁,x,rfl,y,rfl,h₂⟩, refine ⟨_,x,_,y,_,h₂⟩,
                { intro h, have := quotient.eq.mp h, have := p₃.mp this, rw [p₂ _,p₂ _] at this, exact h₁ this },
                { apply quotient.eq.mpr, apply p₃.mpr, rw p₂ _ },
                { apply quotient.eq.mpr, apply p₃.mpr, rw p₂ _ },
            }
        }
    end

    namespace is_contraction2
        lemma iso_left : G ≃g G' -> G' ≼cc G'' -> G ≼cc G'' :=
        begin
            rintros φ ⟨ψ,h₂,h₃,h₄⟩, refine ⟨_,_,_,_⟩,
            { exact φ.inv_fun ∘ ψ },
            { refine surjective.comp _ h₂, exact φ.symm.surjective },
            { refine adapted.comp_left _ h₃, exact φ.symm.bijective },
            { rw [push.comp,comp_app,←h₄], exact push.from_iso φ.symm }
        end

        lemma le_left : H ≤ G → G ≼cc G' -> ∃ H' : simple_graph V', H ≼cc H' ∧ H' ≤ G' :=
        begin
            rintros h₁ ⟨φ,h₂,h₃,h₄⟩, let H' := G' ⊓ pull φ G, use H', split,
            { sorry },
            { intros x y h, exact h.1 }
        end
    end is_contraction2
end simple_graph

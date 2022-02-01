import tactic data.equiv.basic
import graph_theory.path
open function classical

namespace simple_graph
    variables {V V' V'' : Type} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
    variables {G H : simple_graph V} {G' H' : simple_graph V'} {G'' : simple_graph V''}

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

        lemma comp_left (g_inj : injective g) : adapted f G → adapted (g ∘ f) G :=
        begin
            rintros f_adp z'', by_cases ∃ z', g z' = z'',
            { rcases h with ⟨z',rfl⟩, exact connected_of_iso (select.level_comp g_inj).symm (f_adp z') },
            { push_neg at h, rintro ⟨z,hz⟩, specialize h (f z), contradiction }
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
            have hff : adapted ff H := by { rintro ⟨z',hz'⟩, -- TODO: reused below
                exact connected_of_iso select.level_map.symm (hf z') },
            have hpf : (push ff H).connected := by { dsimp only [ff,H], rw ←select.of_push, exact hg z },
            exact connected hff hpf,
        end
    end adapted

    def is_contraction (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ φ : V' → V, surjective φ ∧ adapted φ G' ∧ G = push φ G'

    infix ` ≼c `:50 := is_contraction

    namespace is_contraction
        @[refl] lemma refl : G ≼c G :=
        ⟨id,surjective_id,adapted.of_injective injective_id,push.push_id.symm⟩

        lemma of_iso : G ≃g G' → G ≼c G' :=
        λ φ, let ψ := φ.symm in ⟨ψ, ψ.surjective, adapted.of_injective ψ.injective, push.from_iso ψ⟩

        @[trans] lemma trans : G ≼c G' → G' ≼c G'' → G ≼c G'' :=
        begin
            rintros ⟨φ,h₁,h₂,rfl⟩ ⟨ψ,h₄,h₅,rfl⟩,
            exact ⟨φ ∘ ψ, h₁.comp h₄, h₅.comp_push h₂, push.comp.symm⟩,
        end

        lemma iso_left : G ≃g G' -> G' ≼c G'' -> G ≼c G'' :=
        trans ∘ of_iso

        lemma le_left_aux {f : V → V'} : H' ≤ push f G → H' = push f (G ⊓ pull' f H') :=
        begin
            intro h₁, ext x' y', split,
            { intro h, rcases h₁ h with ⟨h₄,x,y,rfl,rfl,h₅⟩, exact ⟨h₄,x,y,rfl,rfl,h₅,h₄ ∘ congr_arg f,or.inr h⟩ },
            { rintros ⟨h₄,x,y,rfl,rfl,-,-,h₇⟩, cases h₇, contradiction, exact h₇ }
        end

        lemma le_left_aux2 {f : V → V'} (h₁ : H' ≤ push f G) (h₂ : surjective f) (h₃ : adapted f G) : H' ≼c G ⊓ pull' f H' :=
        begin
            refine ⟨f,h₂,_,le_left_aux h₁⟩, rw adapted.iff at h₃ ⊢, intros x' y' h₄, specialize h₃ x' y' h₄,
            cases h₃ with p hp, induction p with a a b c h₅ p ih,
            { use walk.nil, exact hp },
            { have h₆ : f b = f c := by { apply hp, right, exact walk.start_mem_support p },
                have h₇ : ∀ (z : V), z ∈ p.support → f z = f c := by { intros z h, apply hp, right, exact h},
                have h₈ : (G ⊓ pull' f H').adj a b := by { split, exact h₅, refine ⟨G.ne_of_adj h₅,_⟩, left, rwa h₆ },
                specialize ih h₆ h₇, cases ih with q h₉, use walk.cons h₈ q,
                intros z h, cases h, rwa h, exact h₉ z h }
        end

        lemma le_left : H ≤ G → G ≼c G' → ∃ H' : simple_graph V', H ≼c H' ∧ H' ≤ G' :=
        by { rintros h₁ ⟨f,h₂,h₃,rfl⟩, exact ⟨G' ⊓ pull' f H, le_left_aux2 h₁ h₂ h₃, λ x y h, h.1⟩ }

        lemma select_left {P : V → Prop} : G ≼c G' -> ∃ P' : V' → Prop, select P G ≼c select P' G' :=
        begin
            rintros ⟨f,h₁,h₂,h₃⟩, use (λ x, P (f x)), refine ⟨select.map f P,_,_,_⟩,
            { rintro ⟨x,py⟩, cases h₁ x with x', refine ⟨⟨x',_⟩,_⟩, rwa h, ext, exact h },
            { rintros ⟨z,hz⟩, exact connected_of_iso select.level_map.symm (h₂ z) }, -- TODO: factor out
            { ext ⟨x,hx⟩ ⟨y,hy⟩, simp [select,pull,on_fun], split,
                { intro h₄, rw h₃ at h₄, rcases h₄ with ⟨h₄,x',y',h₅,h₆,h₇⟩,
                    simp only [subtype.coe_mk] at h₅ h₆, substs h₅ h₆,
                    refine ⟨_,⟨x',hx⟩,⟨y',hy⟩,rfl,rfl,h₇⟩,
                    intro h, rw subtype.ext_iff at h, contradiction },
                { rintros ⟨h₄,⟨x',hx⟩,⟨y',hy⟩,h₅,h₆,h₇⟩, rw h₃, refine ⟨_,x',y',_,_,h₇⟩,
                    { intro h, rw ←subtype.ext_iff at h, contradiction },
                    { simp [select.map,subtype.map] at h₅, exact h₅ },
                    { simp [select.map,subtype.map] at h₆, exact h₆ } }
            }
        end
    end is_contraction
end simple_graph

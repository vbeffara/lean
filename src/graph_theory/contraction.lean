import tactic data.equiv.basic
import graph_theory.path graph_theory.pushforward graph_theory.contraction2
open function
open_locale classical

namespace simple_graph
    variables {V V' V'' : Type} {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    namespace contraction
        @[ext] structure setup (G : simple_graph V) := (g : simple_graph V) (sub : g ≤ G)

        namespace setup
            def support (S : setup G) : Type := V

            instance setoid (S : setup G) : setoid S.support
                := ⟨S.g.linked,simple_graph.linked.equiv⟩

            def clusters (S : setup G) := _root_.quotient S.setoid

            @[simp] def proj (S : setup G) : V -> clusters S := quotient.mk
            @[simp] noncomputable def out (S : setup G) : clusters S -> V := quotient.out
            @[simp] lemma out_eq (S : setup G) : ∀ {x : clusters S}, S.proj (S.out x) = x := quotient.out_eq

            def adj (S : setup G) (x y : S.clusters) : Prop
                := x ≠ y ∧ ∃ x' y' : S.support, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y'

            @[symm] lemma symm (S : setup G) (x y : S.clusters) : S.adj x y -> S.adj y x
                | ⟨h0,x',y',h1,h2,h3⟩ := ⟨h0.symm,y',x',h2,h1,h3.symm⟩

            @[simp] def bot : setup G := ⟨⊥, λ x y, false.rec _⟩
        end setup

        def adapted (S : setoid V) (G : simple_graph V) : Prop :=
        relation.refl_trans_gen (G.adj ⊓ S.rel) = S.rel
    end contraction

    def contraction (G : simple_graph V) (S : contraction.setup G) : simple_graph S.clusters
        := G / S.setoid

    notation G `/` S := contraction G S

    def is_contraction (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ S : contraction.setup G', nonempty (G ≃g (G'/S))

    infix ` ≼c `:50 := is_contraction

    lemma contraction_iff : G ≼c G' ↔ G ≼cc G' :=
    begin
        split,
        { rintro ⟨S,⟨⟨f,f',h₁,h₂⟩,h₃⟩⟩, simp [contraction] at h₃, let φ : V' -> V := f' ∘ quotient.mk', refine ⟨φ,_,_,_⟩,
            { exact (left_inverse.right_inverse h₁).surjective.comp quotient.surjective_quotient_mk' },
            { intro z, intros x y, rcases x with ⟨x,hx⟩, rcases y with ⟨y,rfl⟩, simp [φ] at hx,
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
                { intro h, rw adapted.iff at h₂, specialize h₂ x y h, cases h₂ with p hp, apply linked.linked_iff.mpr, refine ⟨_⟩,
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

    namespace contraction
        variables {S : setup G} {S' : setup (G/S)} {x y : S.support} {xx yy : S.clusters}
        open walk quotient relation.refl_trans_gen

        namespace setup
            def linked (S : setup G) (x y : S.clusters) : Prop := (G/S).linked x y

            def comp (S : setup G) (S' : setup (G/S)) : setup G
                := {
                    g := {
                        adj := λ x y, x ≠ y ∧ (S.g.adj x y ∨ (G.adj x y ∧ S'.g.adj ⟦x⟧ ⟦y⟧)),
                        symm := λ x y, by { rintros ⟨h1,h2⟩, refine ⟨h1.symm,_⟩, cases h2, left, exact h2.symm,
                                            right, exact ⟨h2.1.symm,h2.2.symm⟩ }
                    },
                    sub := λ x y, by { rintros ⟨h1,h2⟩, cases h2, exact S.sub h2, exact h2.1 }
                }

            namespace comp
                lemma linked_mp : (S.comp S').g.linked x y -> S'.g.linked ⟦x⟧ ⟦y⟧
                    := by { intro h, induction h with a b h₁ h₂ ih, refl, refine ih.trans _, cases h₂.2 with h₂ h₂,
                            { rw (@quotient.eq S.support _ a b).mpr (tail refl h₂) },
                            { exact tail refl h₂.2 } }

                lemma linked_mpr_aux : ⟦x⟧ = ⟦y⟧ -> (S.comp S').g.linked x y
                    | h := linked.linked_of_subgraph (λ x y ha, ⟨S.g.ne_of_adj ha, or.inl ha⟩) (quotient.eq.mp h)

                lemma linked_mpr_aux' : S'.g.adj ⟦x⟧ ⟦y⟧ -> (S.comp S').g.linked x y
                    | h := by { rcases S'.sub h with ⟨h1,x',y',hx,hy,h2⟩, rw [<-hx,<-hy] at h,
                        transitivity x', exact linked_mpr_aux hx.symm,
                        transitivity y', swap, exact linked_mpr_aux hy,
                        exact linked.step ⟨G.ne_of_adj h2, or.inr ⟨h2,h⟩⟩ }

                lemma linked_mpr : S'.g.linked xx yy -> (S.comp S').g.linked xx.out yy.out
                    := by { intro h, induction h with a b h₁ h₂ ih, refl, refine ih.trans _,
                        apply linked_mpr_aux', convert h₂; apply out_eq }

                lemma linked : (S.comp S').g.linked x y <-> S'.g.linked ⟦x⟧ ⟦y⟧
                    := by { split,
                        { exact linked_mp },
                        { intro h, transitivity ⟦x⟧.out, apply linked_mpr_aux, symmetry, apply out_eq,
                            transitivity ⟦y⟧.out, exact linked_mpr h, apply linked_mpr_aux, apply out_eq } }

                lemma linked' : (S.comp S').proj x = (S.comp S').proj y <-> S'.proj (S.proj x) = S'.proj (S.proj y)
                    := by { simp only [proj,quotient.eq], exact linked }

                noncomputable def iso {S : setup G} (S' : setup (G/S)) : G/comp S S' ≃g G/S/S'
                    := by {
                        let f := S.proj, let g := S'.proj, let h := (S.comp S').proj,
                        let α := S.out, let β := S'.out, let γ := (S.comp S').out,

                        have fα : ∀ {x}, S.proj (S.out x) = x := λ _, S.out_eq,
                        have gβ : ∀ {x}, S'.proj (S'.out x) = x := λ _, S'.out_eq,
                        have hγ : ∀ {x}, (S.comp S').proj ((S.comp S').out x) = x := λ _, (S.comp S').out_eq,

                        let φ : (comp S S').clusters ≃ S'.clusters := {
                            to_fun := λ x, g (f (γ x)),
                            inv_fun := h ∘ S.out ∘ S'.out,
                            left_inv := λ _, eq.trans (linked'.mpr (by { rw [fα,gβ] })) hγ,
                            right_inv := λ _, eq.trans (linked'.mp hγ) (by { rw [fα,gβ] })
                        },

                        use φ, intros a b, split,
                        { rintro ⟨h1,xx,yy,h2,h3,h4,u,v,h5,h6,h7⟩, substs xx yy, split,
                            { exact h1 ∘ (congr_arg (g ∘ f ∘ γ)) },
                            { exact ⟨u,v,(linked'.mpr h2).trans hγ,(linked'.mpr h3).trans hγ,h7⟩ } },
                        { rintro ⟨h1,x,y,h2,h3,h4⟩, split,
                            { simpa [linked'.symm,hγ] },
                            { refine ⟨_,_,linked'.mp (h2.trans hγ.symm),linked'.mp (h3.trans hγ.symm),_,x,y,rfl,rfl,h4⟩,
                                intro h, substs a b, exact h1 (linked'.mpr (congr_arg g h)) } }
                    }
            end comp

            def fmap_isom (f : G ≃g G') (S : setup G) : setup G'
                := { g := { adj := S.g.adj on f.inv_fun,
                            symm := λ x' y' h, S.g.symm h,
                            loopless := λ x, S.g.loopless _ },
                    sub := λ x y h, by { have h2 := f.map_rel_iff', convert h2.mpr (S.sub h);
                            exact (rel_iso.apply_symm_apply f _).symm } }

            namespace fmap_isom
                variables {f : G ≃g G'}

                lemma inv : (S.fmap_isom f).fmap_isom f.symm = S
                    := by { have hf : f.symm.to_equiv.symm = f.to_equiv := by { ext, refl }, ext, split; intro h,
                        { rw [fmap_isom] at h, convert h; symmetry; exact rel_iso.symm_apply_apply _ _ },
                        { rw [fmap_isom,fmap_isom], simp only [on_fun], convert h; exact rel_iso.symm_apply_apply _ _ } }

                lemma linked : S.g.linked x y -> (S.fmap_isom f).g.linked (f x) (f y)
                    := by { intro h, induction h with a b h₁ h₂ ih, refl,
                        refine ih.trans (tail refl _), simp only [fmap_isom,on_fun], convert h₂; exact rel_iso.symm_apply_apply _ _ }

                lemma linked_iff : S.g.linked x y <-> (S.fmap_isom f).g.linked (f x) (f y)
                    := by { split, exact linked, intro h,
                        replace h := @linked V' V G' G (S.fmap_isom f) (f x) (f y) f.symm h,
                        simp only [inv,rel_iso.symm_apply_apply] at h, exact h }
            end fmap_isom
        end setup

        noncomputable def fmap_iso (f : G ≃g G') (S : setup G) : G/S ≃g G'/S.fmap_isom f
            := by {
                let f₁ : V -> S.clusters := quotient.mk,
                let f₂ : V' -> (S.fmap_isom f).clusters := quotient.mk,

                let g₁ : S.clusters -> V := quotient.out,
                let g₂ : (S.fmap_isom f).clusters -> V' := quotient.out,

                have f₁g₁ : ∀ {x}, f₁ (g₁ x) = x := λ _, S.out_eq,
                have f₂g₂ : ∀ {x}, f₂ (g₂ x) = x := λ _, (S.fmap_isom f).out_eq,

                have eqv : ∀ {x y}, f₁ x = f₁ y <-> f₂ (f x) = f₂ (f y),
                    by { intros, rw [quotient.eq,quotient.eq], exact setup.fmap_isom.linked_iff },

                let φ : S.clusters ≃ (S.fmap_isom f).clusters := {
                    to_fun := f₂ ∘ f ∘ g₁,
                    inv_fun := f₁ ∘ f.symm ∘ g₂,
                    left_inv := λ _, eq.trans (by { rw [eqv,rel_iso.apply_symm_apply,f₂g₂] }) f₁g₁,
                    right_inv := λ _, (eqv.mp f₁g₁).trans (by { rw [rel_iso.apply_symm_apply,f₂g₂] })
                },

                use φ, intros a b, rw [equiv.coe_fn_mk], split,
                { rintros ⟨h1,x',y',h2,h3,h4⟩, refine ⟨_,_⟩,
                    { intro h, rw h at h1, exact h1 rfl },
                    { refine ⟨f.symm x', f.symm y', _, _, _⟩,
                        { rw [<-@f₁g₁ a,eqv,rel_iso.apply_symm_apply], exact h2 },
                        { rw [<-@f₁g₁ b,eqv,rel_iso.apply_symm_apply], exact h3 },
                        { have := f.symm.map_rel_iff', exact this.mpr h4 } } },
                { rintros ⟨h1,x,y,h2,h3,h4⟩, refine ⟨_,_⟩,
                    { unfold ne, rw [eqv.symm,f₁g₁,f₁g₁], exact h1 },
                    { refine ⟨f x, f y, _, _, _⟩,
                        { rw [eqv.symm,f₁g₁], exact h2 },
                        { rw [eqv.symm,f₁g₁], exact h3 },
                        { have := f.map_rel_iff', exact this.mpr h4 } } }
            }

        lemma proj_adj : G.adj x y -> ⟦x⟧ = ⟦y⟧ ∨ (G/S).adj ⟦x⟧ ⟦y⟧
            | h := dite (⟦x⟧ = ⟦y⟧) or.inl (λ h', or.inr ⟨h',x,y,rfl,rfl,h⟩)

        lemma linked_of_adj : (G/S).adj ⟦x⟧ ⟦y⟧ -> linked G x y
            | ⟨h₁,a,b,h₂,h₃,h₄⟩ := by { transitivity b, transitivity a,
                exact linked.linked_of_subgraph S.sub (quotient.eq.mp h₂.symm),
                exact linked.step h₄,
                exact linked.linked_of_subgraph S.sub (quotient.eq.mp h₃) }

        lemma project_linked : linked G x y -> linked (G/S) ⟦x⟧ ⟦y⟧
            := by { intro h, induction h with u v h₁ h₂ ih, refl, letI : setoid V := S.setoid,
                refine ih.trans _, by_cases (⟦u⟧ = ⟦v⟧), rw h, apply linked.step, refine ⟨h,u,v,rfl,rfl,h₂⟩ }

        lemma lift_linked' : linked (G/S) xx yy ->
                ∀ (x y : V) (hx : ⟦x⟧ = xx) (hy : ⟦y⟧ = yy), linked G x y
            := by { intro h, induction h with aa b h₁ h₂ ih; intros x y hx hy,
                { subst hy, exact linked.linked_of_subgraph S.sub (quotient.eq.mp hx) },
                { obtain ⟨a, ha : ⟦a⟧ = aa⟩ := quot.exists_rep aa, substs ha hx hy,
                    specialize ih x a rfl rfl, refine ih.trans _, exact linked_of_adj h₂ } }

        lemma lift_linked (h : linked (G/S) ⟦x⟧ ⟦y⟧) : linked G x y
            := lift_linked' h _ _ rfl rfl

        lemma contraction_connected_iff : connected G <-> connected (G/S)
            := { mp := λ h xx yy, by {
                    obtain ⟨x, hx : ⟦x⟧ = xx⟩ := quot.exists_rep xx, subst hx,
                    obtain ⟨y, hy : ⟦y⟧ = yy⟩ := quot.exists_rep yy, subst hy,
                    exact project_linked (h x y) },
                mpr := λ h x y, lift_linked (h ⟦x⟧ ⟦y⟧) }

        lemma proj_bot_inj {x y : (@setup.bot V G).support} : ⟦x⟧ = ⟦y⟧ -> x = y
            := by { intro h, cases quotient.eq.mp h with p, refl, exfalso, assumption }

        noncomputable def proj_bot : G ≃g G/setup.bot
            := {
                to_equiv := {
                    to_fun := quotient.mk,
                    inv_fun := out,
                    left_inv := λ x, proj_bot_inj (out_eq _),
                    right_inv := out_eq,
                },
                map_rel_iff' := λ x y, by { rw [equiv.coe_fn_mk], split,
                    { rintro ⟨h1,x',y',h2,h3,h4⟩, rw [<-proj_bot_inj h2, <-proj_bot_inj h3], exact h4 },
                    { intro h, refine ⟨_,x,y,rfl,rfl,h⟩,
                        intro h1, rw proj_bot_inj h1 at h, exact G.ne_of_adj h rfl } } }
    end contraction

    namespace is_contraction
        open contraction

        @[refl] lemma refl : G ≼c G := ⟨setup.bot,⟨proj_bot⟩⟩

        lemma iso_left : G ≃g G' -> G' ≼c G'' -> G ≼c G''
        := by { simp_rw contraction_iff, exact is_contraction2.iso_left }

        lemma le_left : H ≤ G -> G ≼c G' -> ∃ H' : simple_graph V', H ≼c H' ∧ H' ≤ G'
        := by { simp_rw contraction_iff, exact is_contraction2.le_left }

        @[trans] lemma trans : G ≼c G' -> G' ≼c G'' -> G ≼c G'' :=
        by { simp_rw contraction_iff, exact is_contraction2.trans }

        lemma select_left {P : V → Prop} : G ≼c G' -> ∃ P' : V' → Prop, select P G ≼c select P' G'
        := by { simp_rw contraction_iff, exact is_contraction2.select_left }
    end is_contraction
end simple_graph

import tactic data.equiv.basic
import graph_theory.quotient graph_theory.path graph_theory.pushforward
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

        structure setup' (G : simple_graph V) := (S : setoid V) (h : adapted S G)

        namespace setup'
            open relation

            def of_rel (rel : V -> V -> Prop) (sym : symmetric rel) (sub : rel ≤ G.adj) : setup' G := {
                S := {
                    r := relation.refl_trans_gen rel,
                    iseqv := by { refine ⟨_,_,_⟩,
                        apply refl_trans_gen.refl,
                        apply refl_trans_gen.symmetric sym,
                        apply refl_trans_gen.trans }
                },
                h := by { ext a b, split; intro h₁; induction h₁ with u v h₂ h₃ ih,
                    { refl }, { refine ih.trans _, exact h₃.2 },
                    { refl }, { refine ih.trans _, refine refl_trans_gen.single _,
                        split, exact sub _ _ h₃, exact refl_trans_gen.single h₃ } }
            }

            def bot : setup' G
            := of_rel (λ x y, false) (λ x y, id) (λ x y, false.rec _)
        end setup'
    end contraction

    def contraction (G : simple_graph V) (S : contraction.setup G) : simple_graph S.clusters
        := G / S.setoid

    def contraction' (G : simple_graph V) (S : contraction.setup' G) : simple_graph (quotient S.S) := G / S.S

    notation G `/` S := contraction G S
    notation G `/` S := contraction' G S

    def is_contraction (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ S : contraction.setup G', nonempty (G ≃g (G'/S))

    def is_contraction' (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ φ : V' -> V, surjective φ ∧ G = push φ G'

    example : (∃ S : setoid V', nonempty (G ≃g G'/S)) <-> is_contraction' G G' :=
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

    infix ` ≼c `:50 := is_contraction

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

            -- TODO : comp.setoid is setoid.ker (setoid.mk ∘ setoid.mk)

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

        def proj_bot' : G ≃g G/setup'.bot
            := by { simp only [contraction'], convert quotient_graph.iso_bot;
                { ext, split; intro h₁,
                { induction h₁ with u v h₂ h₃ ih, refl, contradiction },
                { simp only [setoid.bot_def] at h₁, rw h₁ } }
            }
    end contraction

    namespace is_contraction
        open contraction

        @[refl] lemma refl : G ≼c G := ⟨setup.bot,⟨proj_bot⟩⟩

        lemma iso_left : G ≃g G' -> G' ≼c G'' -> G ≼c G''
            | φ ⟨S,⟨ψ⟩⟩ := ⟨S,⟨ψ.comp φ⟩⟩

        lemma iso_right : G ≼c G' -> G' ≃g G'' -> G ≼c G''
            | ⟨S,⟨ψ⟩⟩ φ := ⟨S.fmap_isom φ, ⟨(fmap_iso φ S).comp ψ⟩⟩

        namespace detail_le_contraction
            def lift_le {S : setup G} (H : simple_graph S.clusters) : simple_graph V
                := {
                    adj := λ x y, S.g.adj x y ∨ (G.adj x y ∧ H.adj (S.proj x) (S.proj y)),
                    symm := λ x y h, by { cases h, exact or.inl h.symm, exact or.inr ⟨h.1.symm,h.2.symm⟩ },
                    loopless := λ x h, by { cases h, exact S.g.irrefl h, exact G.irrefl h.1 }
                }

            lemma lift_le_le {S : setup G} (H : simple_graph S.clusters) : lift_le H ≤ G
                := by { intros x y h, cases h, exact S.sub h, exact h.1 }

            def lift_setup (S : setup G) (H : simple_graph S.clusters) : setup (lift_le H)
                := ⟨S.g, λ x y, or.inl⟩

            def iso {S : setup G} {H : simple_graph S.clusters} (sub : H ≤ G/S) : H ≃g (lift_le H)/(lift_setup S H)
                := {
                        to_fun := λ x, x,
                        inv_fun := λ y, y,
                        left_inv := λ x, rfl,
                        right_inv := λ y, rfl,
                        map_rel_iff' := λ x y, by { simp only [setup.adj, equiv.coe_fn_mk, contraction], split,
                            { rintros ⟨h₁,x',y',h₂,h₃,h₄⟩, substs h₂ h₃, cases h₄,
                                { have : (⟦x'⟧ : _root_.quotient (lift_setup S H).setoid) = ⟦y'⟧ := quotient.eq.mpr (linked.step h₄), contradiction },
                                { exact h₄.2 }
                            },
                            { intro h₁, refine ⟨H.ne_of_adj h₁, _⟩, rcases sub h₁ with ⟨h₂,x',y',h₃,h₄,h₅⟩,
                                substs h₃ h₄, exact ⟨x',y',rfl,rfl,or.inr ⟨h₅,h₁⟩⟩ }
                        }
                    }
        end detail_le_contraction

        lemma le_contraction {S : setup G} {H : simple_graph S.clusters} (sub : H ≤ (G/S)) : ∃ H' : simple_graph V, H ≼c H' ∧ H' ≤ G
            :=  let H' := detail_le_contraction.lift_le H,
                    ψ := detail_le_contraction.iso sub
                in ⟨H',⟨_,⟨ψ⟩⟩,detail_le_contraction.lift_le_le H⟩

        namespace le_left
            def push_iso (H : simple_graph V) (φ : V ≃ V') : simple_graph V'
                := ⟨H.adj on φ.inv_fun, λ _ _ h, H.symm h, λ _, H.loopless _⟩

            def push_iso_iso (H : simple_graph V) (φ : V ≃ V') : H ≃g push_iso H φ
                := {
                    to_equiv := φ,
                    map_rel_iff' := λ x y, by { unfold push_iso,
                        simp only [on_fun,equiv.symm_apply_apply,equiv.inv_fun_as_coe] }
                }

            lemma push_iso_le {H G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G') (sub : H ≤ G) : push_iso H φ.to_equiv ≤ G'
                := by { intros x y h, rw [<-(φ.right_inv x),<-(φ.right_inv y)] at h ⊢,
                    have h' := sub h, rw [φ.left_inv,φ.left_inv] at h', exact φ.map_rel_iff.mpr h' }
        end le_left

        lemma le_left : G ≤ H -> H ≼c G' -> ∃ H' : simple_graph V', G ≼c H' ∧ H' ≤ G'
            := by {
                rintros h₁ ⟨S,⟨φ⟩⟩,
                have sub := le_left.push_iso_le φ h₁,
                have iso := le_left.push_iso_iso G φ.to_equiv,
                set K := le_left.push_iso G φ.to_equiv,
                rcases le_contraction sub with ⟨L,L_c,L_le⟩,
                refine ⟨L, iso_left iso L_c, L_le⟩
            }

        @[trans] lemma trans : G ≼c G' -> G' ≼c G'' -> G ≼c G''
            | ⟨S,⟨f1⟩⟩ ⟨S',⟨f2⟩⟩ :=
                let T := S.fmap_isom f2,
                    f3 := fmap_iso f2 S,
                    f4 := setup.comp.iso T
                in ⟨S'.comp T,⟨f4.symm.comp (f3.comp f1)⟩⟩

        namespace select_left.detail
            variables {S : setup G} {P : S.clusters → Prop}
            open relation

            def push_pred (P : V → Prop) (φ : G ≃g G') : V' → Prop := P ∘ φ.inv_fun

            def lift_pred (P : S.clusters → Prop) : V → Prop := λ x, P ⟦x⟧

            def setup_select (S : setup G) (P' : V → Prop) : setup (select P' G)
                := ⟨select P' S.g, λ x y, by { apply S.sub }⟩

            lemma pred_of_adj {x y} : S.g.adj x y -> lift_pred P x -> lift_pred P y
                := by { intros h₁, simp only [lift_pred], rw (@quotient.eq _ S.setoid x y).mpr (linked.step h₁), exact id }

            lemma rel_iff {S : setup G} {P : S.clusters → Prop} (x y : subtype (lift_pred P)) :
                    (setup_select S (lift_pred P)).setoid.rel x y <-> S.setoid.rel x.val y.val
                := by { simp only [setup.setoid,setoid.rel], split,
                    { apply refl_trans_gen.lift, introv, exact id },
                    { intro h, cases x with x hx, cases y with y hy, change S.g.linked x y at h,
                        induction h with u v h₁ h₂ ih, refl,
                        specialize ih (pred_of_adj h₂.symm hy), refine ih.trans _, refine linked.step _, exact h₂ } }

            def iso (S : setup G) (P : S.clusters → Prop) : select P (G/S) ≃g select (lift_pred P) G/(setup_select S (lift_pred P))
                := by {
                    let φ := @equiv.subtype_quotient_equiv_quotient_subtype V (lift_pred P) S.setoid
                            (setup_select S (lift_pred P)).setoid P (λ a, iff.rfl) rel_iff,

                    have φ_mk : ∀ (x : V) (hx : P ⟦x⟧), φ ⟨⟦x⟧, hx⟩ = ⟦⟨x, hx⟩⟧
                        := equiv.subtype_quotient_equiv_quotient_subtype_mk (lift_pred P) P (λ a, iff.rfl) rel_iff,

                    exact {
                        to_equiv := φ,
                        map_rel_iff' := λ x y, by {
                            simp only [select,setup.adj,on_fun,contraction,quotient_graph,pull,push],
                            rw [ne.def,ne.def,equiv.apply_eq_iff_eq],
                            cases x with x hx, rw <-(quotient.out_eq x) at hx,
                            cases y with y hy, rw <-(quotient.out_eq y) at hy,
                            have h₃ := φ_mk x.out hx, simp only [quotient.out_eq] at h₃, rw h₃,
                            have h₄ := φ_mk y.out hy, simp only [quotient.out_eq] at h₄, rw h₄,
                            clear φ_mk h₃ h₄ φ, simp only [and.congr_right_iff], intro h₀, split,
                            { rintros ⟨x',y',H₂,H₃,H₄⟩, refine ⟨x'.val,y'.val,_,_,H₄⟩,
                                { rw <-(quotient.out_eq x), exact quotient.eq.mpr ((rel_iff _ _).mp (quotient.eq.mp H₂)) },
                                { rw <-(quotient.out_eq y), exact quotient.eq.mpr ((rel_iff _ _).mp (quotient.eq.mp H₃)) }
                            },
                            { rintros ⟨x',y',H₂,H₃,H₄⟩, rw <-(quotient.out_eq x) at H₂, rw <-(quotient.out_eq y) at H₃,
                                refine ⟨⟨x',_⟩,⟨y',_⟩,_,_,H₄⟩,
                                { rw [<-H₂] at hx, rw [lift_pred], exact hx },
                                { rw [<-H₃] at hy, rw [lift_pred], exact hy },
                                { exact quotient.eq.mpr ((rel_iff _ _).mpr (quotient.eq.mp H₂)) },
                                { exact quotient.eq.mpr ((rel_iff _ _).mpr (quotient.eq.mp H₃)) }
                            }
                        }
                    }
                }

            lemma select_contraction : select P (G/S) ≼c select (lift_pred P) G
                := ⟨_,⟨iso S P⟩⟩
        end select_left.detail

        lemma select_left {P : V → Prop} : G ≼c G' -> ∃ P' : V' → Prop, select P G ≼c select P' G'
            := by {
                rintros ⟨S,⟨φ⟩⟩,
                let P'' := select_left.detail.push_pred P φ,
                let P' := select_left.detail.lift_pred P'',
                have h₁ := select.push_pred_iso P φ,
                have h₂ := select_left.detail.select_contraction,
                exact ⟨P', trans (iso_left h₁ refl) h₂⟩
            }
    end is_contraction
end simple_graph

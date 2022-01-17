import tactic
import graph_theory.basic graph_theory.path_embedding
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

            def clusters (S : setup G) := quotient S.setoid

            @[simp] def proj (S : setup G) : V -> clusters S := quotient.mk
            @[simp] noncomputable def out (S : setup G) : clusters S -> V := quotient.out
            @[simp] lemma out_eq {S : setup G} {x : clusters S} : S.proj (S.out x) = x := quotient.out_eq x

            def adj (S : setup G) (x y : S.clusters) : Prop
                := x ≠ y ∧ ∃ x' y' : S.support, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y'

            @[symm] lemma symm (S : setup G) (x y : S.clusters) : S.adj x y -> S.adj y x
                | ⟨h0,x',y',h1,h2,h3⟩ := ⟨h0.symm,y',x',h2,h1,h3.symm⟩

            @[simp] def bot : setup G := ⟨⊥, λ x y, false.rec _⟩
            instance : has_bot (setup G) := ⟨bot⟩
        end setup
    end contraction

    def contraction (G : simple_graph V) (S : contraction.setup G) : simple_graph S.clusters
        := ⟨S.adj, S.symm⟩

    notation G `/` S := contraction G S

    def is_contraction (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ S : contraction.setup G', nonempty (G ≃g (G'/S))

    infix ` ≼c `:50 := is_contraction

    namespace contraction
        variables {S : setup G} {S' : setup (G/S)} {x y : S.support} {xx yy : S.clusters}
        open walk quotient

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
                    := by { rintro ⟨p⟩, induction p with a a b c h p ih, refl, cases h with h1 h2, cases h2,
                            { rw (@quotient.eq S.support _ a b).mpr (linked.step h2), exact ih },
                            { exact linked.cons h2.2 ih } }

                lemma linked_mpr_aux : ⟦x⟧ = ⟦y⟧ -> (S.comp S').g.linked x y
                    | h := linked.linked_of_subgraph (λ x y ha, ⟨S.g.ne_of_adj ha, or.inl ha⟩) (quotient.eq.mp h)

                lemma linked_mpr_aux' : S'.g.adj ⟦x⟧ ⟦y⟧ -> (S.comp S').g.linked x y
                    | h := by { rcases S'.sub h with ⟨h1,x',y',hx,hy,h2⟩, rw [<-hx,<-hy] at h,
                        transitivity x', exact linked_mpr_aux hx.symm,
                        transitivity y', swap, exact linked_mpr_aux hy,
                        exact linked.step ⟨G.ne_of_adj h2, or.inr ⟨h2,h⟩⟩ }

                lemma linked_mpr : S'.g.linked xx yy -> (S.comp S').g.linked xx.out yy.out
                    := by { rintro ⟨p⟩, induction p with aa aa bb cc hh pp ih,
                        { apply linked_mpr_aux, refl },
                        { transitivity bb.out, swap, exact ih, clear ih, apply linked_mpr_aux', convert hh; apply out_eq } }

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

                        have fα : ∀ {x}, S.proj (S.out x) = x, by simp [proj,out],
                        have gβ : ∀ {x}, S'.proj (S'.out x) = x, by simp [proj,out],
                        have hγ : ∀ {x}, (S.comp S').proj ((S.comp S').out x) = x, by simp [proj,out],

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

                -- def iso' {S : setup G} (S' : setup (G/S)) : G/comp S S' ≃g G/S/S'
                --     := by {
                --         let f : V -> S.clusters := quotient.mk,
                --         let g : S.clusters -> S'.clusters := quotient.mk,
                --         let h : V -> (S.comp S').clusters := quotient.mk,

                --         have eqv : ∀ {x y : V}, h x = h y <-> g (f x) = g (f y)
                --             := λ x y, iff.trans quotient.eq (iff.trans linked (@quotient.eq _ S'.setoid _ _).symm),

                --         let φ₁ : (S.comp S').clusters → S'.clusters := quotient.lift (g ∘ f) (λ a b, eqv.mp ∘ quotient.eq.mpr),
                --         let φ₂ : S.clusters -> (S.comp S').clusters := quotient.lift h (λ a b, eqv.mpr ∘ congr_arg g ∘ quotient.eq.mpr),
                --         let φ₃ := @quotient.lift _ _ S'.setoid φ₂ (by { intros a b h, dsimp [φ₂],
                --                 cases quotient.exists_rep a with x hx, cases quotient.exists_rep b with y hy, substs a b,
                --                 rw [quotient.lift_mk,quotient.lift_mk], apply eqv.mpr, replace h := quotient.eq.mpr h, exact h }),

                --         let φ : (comp S S').clusters ≃ S'.clusters := {
                --             to_fun := φ₁,
                --             inv_fun := φ₃,
                --             left_inv := sorry,
                --             right_inv := sorry
                --         },
                --         sorry
                --     }

                -- def setoid.comp (s : setoid V) (s' : setoid (quotient s)) : setoid V
                --     := let f : V -> quotient s := quotient.mk,
                --            g : quotient s -> quotient s' := quotient.mk
                --         in setoid.ker (g ∘ f)

                -- def iso'' {S : setup G} (S' : setup (G/S)) : G/comp S S' ≃g G/S/S'
                --     := by {
                --         let f₁ : (comp S S').support -> S'.clusters := S'.proj ∘ S.proj,
                --         let f₂ : (comp S S').clusters -> S'.clusters := quotient.lift f₁
                --             (by { sorry }),

                --         let φ : (comp S S').clusters ≃ S'.clusters := {
                --             to_fun := f₂,
                --             inv_fun := sorry,
                --             left_inv := sorry,
                --             right_inv := sorry
                --         },
                --         sorry
                --     }
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
                        { simp [setup.fmap_isom,hf] at h, convert h; symmetry; exact rel_iso.symm_apply_apply _ _ },
                        { simp [setup.fmap_isom,hf,on_fun], convert h; exact rel_iso.symm_apply_apply _ _ } }

                lemma linked : S.g.linked x y -> (S.fmap_isom f).g.linked (f x) (f y)
                    := by { intro h, cases h with p, induction p with a a b c h q ih, refl,
                        refine linked.cons _ ih, simp [setup.fmap_isom,on_fun], convert h; exact rel_iso.symm_apply_apply _ _ }

                lemma linked_iff : S.g.linked x y <-> (S.fmap_isom f).g.linked (f x) (f y)
                    := by { split, exact linked, intro h,
                        replace h := @linked V' V G' G (S.fmap_isom f) (f x) (f y) f.symm h,
                        simp [setup.fmap_isom.inv] at h, exact h }
            end fmap_isom
        end setup

        noncomputable def fmap_iso (f : G ≃g G') (S : setup G) : G/S ≃g G'/S.fmap_isom f
            := by {
                let f₁ : V -> S.clusters := quotient.mk,
                let f₂ : V' -> (S.fmap_isom f).clusters := quotient.mk,

                let g₁ : S.clusters -> V := quotient.out,
                let g₂ : (S.fmap_isom f).clusters -> V' := quotient.out,

                have f₁g₁ : ∀ {x}, f₁ (g₁ x) = x, by simp [f₁,g₁],
                have f₂g₂ : ∀ {x}, f₂ (g₂ x) = x, by simp [f₂,g₂],

                have eqv : ∀ {x y}, f₁ x = f₁ y <-> f₂ (f x) = f₂ (f y),
                    by { intros, rw [quotient.eq,quotient.eq], exact setup.fmap_isom.linked_iff },

                let φ : S.clusters ≃ (S.fmap_isom f).clusters := {
                    to_fun := f₂ ∘ f ∘ g₁,
                    inv_fun := f₁ ∘ f.symm ∘ g₂,
                    left_inv := λ _, eq.trans (by { rw [eqv,rel_iso.apply_symm_apply,f₂g₂] }) f₁g₁,
                    right_inv := λ _, (eqv.mp f₁g₁).trans (by { rw [rel_iso.apply_symm_apply,f₂g₂] })
                },

                use φ, intros a b, simp, split,
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

        noncomputable def proj_path : Π {x y : V}, walk G x y -> walk (G/S) ⟦x⟧ ⟦y⟧
            | _ _ nil                      := nil
            | _ z (cons (h : G.adj x y) p) := dite (⟦y⟧ = ⟦x⟧) (λ h, by { rw <-h, exact proj_path p })
                                                               (λ h', walk.cons ⟨ne.symm h',_,_,rfl,rfl,h⟩ (proj_path p))

        lemma project_linked : ∀ {x y}, linked G x y -> linked (G/S) ⟦x⟧ ⟦y⟧
            | _ _ ⟨p⟩ := by { induction p with u u v w h p ih, refl,
                cases proj_adj h with h' h', rw h', exact ih, exact ih.cons h' }

        lemma lift_linked' : linked (G/S) xx yy ->
                ∀ (x y : V) (hx : ⟦x⟧ = xx) (hy : ⟦y⟧ = yy), linked G x y
            := by {
                intro h, cases h with p, induction p with u u v w h p ih; intros x y hx hy,
                { subst hy, exact linked.linked_of_subgraph S.sub (quotient.eq.mp hx) },
                { obtain ⟨a, ha : ⟦a⟧ = v⟩ := quot.exists_rep v, substs ha hx hy,
                    transitivity a, exact linked_of_adj h, exact ih a y rfl rfl }
            }

        lemma lift_linked (h : linked (G/S) ⟦x⟧ ⟦y⟧) : linked G x y
            := lift_linked' h _ _ rfl rfl

        lemma contraction_connected_iff : connected G <-> connected (G/S)
            := { mp := λ h xx yy, by {
                    obtain ⟨x, hx : ⟦x⟧ = xx⟩ := quot.exists_rep xx, subst hx,
                    obtain ⟨y, hy : ⟦y⟧ = yy⟩ := quot.exists_rep yy, subst hy,
                    exact project_linked (h x y) },
                mpr := λ h x y, lift_linked (h ⟦x⟧ ⟦y⟧) }

        lemma proj_bot_inj {x y : (@setup.bot V G).support} : ⟦x⟧ = ⟦y⟧ -> x = y
            := by { intro h, cases quotient.eq.mp h with p, cases p, refl, simp at p_h, contradiction }

        noncomputable def proj_bot : G ≃g G/⊥
            := {
                to_equiv := {
                    to_fun := quotient.mk,
                    inv_fun := out,
                    left_inv := λ x, proj_bot_inj (out_eq _),
                    right_inv := out_eq,
                },
                map_rel_iff' := λ x y, by { simp, split,
                    { rintro ⟨h1,x',y',h2,h3,h4⟩, rw [<-proj_bot_inj h2, <-proj_bot_inj h3], exact h4 },
                    { intro h, refine ⟨_,x,y,rfl,rfl,h⟩,
                        intro h1, rw proj_bot_inj h1 at h, exact G.ne_of_adj h rfl } } }
    end contraction

    namespace is_contraction
        open contraction

        @[refl] lemma refl : G ≼c G := ⟨⊥,⟨proj_bot⟩⟩

        lemma iso_left : G ≃g G' -> G' ≼c G'' -> G ≼c G''
            | φ ⟨S,⟨ψ⟩⟩ := ⟨S,⟨ψ.comp φ⟩⟩

        lemma iso_right : G ≼c G' -> G' ≃g G'' -> G ≼c G''
            | ⟨S,⟨ψ⟩⟩ φ := ⟨S.fmap_isom φ, ⟨(fmap_iso φ S).comp ψ⟩⟩

        lemma le_left : G ≤ H -> H ≼c G' -> ∃ H' : simple_graph V', G ≼c H' ∧ H' ≤ G'
            := by {
                rintros h₁ ⟨S,⟨φ⟩⟩,
                sorry
            }

        namespace detail
            -- want : H ≼p G and G ≼c G' -> ∃ H', H ≼c H' and H' ≼p G'
            -- want : H = select pred G and G ≃g G'/S -> H ≃g (select pred' G')/S'
            -- data : (G : simple_graph V) (G' : simple_graph V') (pred : V -> Prop) (S : setup G') (φ : G ≃g G'/S)
            -- construction : (pred' : V' -> Prop) (S' : setup (select pred' G'))

            variables {P : V -> Prop} {S' : setup G'} {φ : G ≃g G'/S'}

            def cluster_pred (P : V -> Prop) (φ : G ≃g G'/S') : S'.clusters -> Prop
                := P ∘ φ.inv_fun

            def restrict_φ (P : V -> Prop) (φ : G ≃g G'/S') : subtype P -> subtype (cluster_pred P φ)
                | ⟨x,h⟩ := ⟨φ x, by { change P (φ.to_equiv.inv_fun (φ.to_equiv.to_fun x)), rw φ.left_inv, exact h }⟩

            def lift_pred (P : V -> Prop) (φ : G ≃g G'/S') : V' -> Prop
                := (cluster_pred P φ) ∘ S'.proj

            def subtype_graph (G : simple_graph V) (P : V -> Prop) : simple_graph (subtype P)
                := {
                    adj := G.adj on subtype.val,
                    symm := λ _ _ h, G.symm h,
                    loopless := λ _, G.loopless _
                }

            def subtype_setup (S : setup G) (P : V -> Prop) : setup (subtype_graph G P)
                := ⟨subtype_graph S.g P, λ _ _ h, S.sub h⟩

            lemma pred_left (S : setup G) (P : S.clusters -> Prop) : ∃ (P' : V -> Prop), ∃ (S' : setup (subtype_graph G P')),
                                                                        nonempty (subtype_graph (G/S) P ≃g (subtype_graph G P')/S')
                := by {
                    let P' : V -> Prop := P ∘ S.proj, use P',
                    let S' : setup (subtype_graph G P') := subtype_setup S P', use S',
                    let φ : subtype_graph (G/S) P ≃g subtype_graph G P'/S' := {
                        to_fun := sorry,
                        inv_fun := sorry,
                        left_inv := sorry,
                        right_inv := sorry,
                        map_rel_iff' := sorry
                    },
                    use φ
                }

            def lift_setup (P : V -> Prop) (φ : G ≃g G'/S') : setup (select (lift_pred P φ) G')
                := subtype_setup S' (lift_pred P φ)

            noncomputable def toto : (lift_setup P φ).clusters ≃ subtype (cluster_pred P φ)
                := {
                    to_fun := λ xx, ⟨S'.proj xx.out.val, xx.out.property⟩,
                    inv_fun := λ yy, (lift_setup P φ).proj ⟨yy.val.out, by { have h := yy.property, simpa [lift_pred] }⟩,
                    left_inv := λ xx, by {
                        change ((lift_setup P φ).proj ⟨(S'.proj xx.out.val).out, by { have h := xx.out.property, simpa [lift_pred] }⟩) = xx,
                        sorry
                    },
                    right_inv := λ yy, by { sorry }
                }

            def adapted (P' : V' -> Prop) (S' : setup G') : Prop := ∀ {x y : V'}, S'.proj x = S'.proj y -> (P' x <-> P' y)

            lemma lemma1 : adapted (lift_pred P φ) S'
                := λ x y h, by simp only [lift_pred,function.comp_app,h]

            noncomputable def restrict (φ : G ≃g G'/S') (P : V -> Prop) : subtype P -> (lift_setup P φ).clusters
                | ⟨x,hₓ⟩ := (lift_setup P φ).proj ⟨(φ x).out,
                    by { change P (φ.inv_fun (S'.proj (S'.out (φ.to_fun x)))), rw [setup.out_eq,φ.left_inv], exact hₓ }⟩

            -- φ.to_fun : V -> S'.clusters
            --
            def restrict' (φ : G ≃g G'/S') (P : V -> Prop) : subtype P -> (lift_setup P φ).clusters
                := by {
                    intro x, let y := φ x,
                }

            noncomputable def restrict_inv (φ : G ≃g G'/S') (P : V -> Prop) : (lift_setup P φ).clusters -> subtype P
                | y := ⟨φ.inv_fun (S'.proj y.out.val), y.out.property⟩

            lemma lemma3 {x : V} {h : P x} : restrict φ P ⟨x,h⟩ = (lift_setup P φ).proj (_ : { o : V' // P (φ.inv_fun (S'.proj o)) })

            lemma lemma2 : left_inverse (restrict_inv φ P) (restrict φ P)
                := by {
                    intro x, ext,
                    -- change φ.inv_fun (S'.proj (subtype.val ((lift_setup P φ).out (restrict φ P x)))) = x.val,
                    apply φ.left_inv.injective,
                    change φ (restrict_inv φ P (restrict φ P x)) = φ x,
                    sorry
                }

            lemma lemma3 : right_inverse (restrict_inv φ P) (restrict φ P) := sorry
        end detail

        lemma select_left {pred : V -> Prop} : G ≼c G' -> ∃ pred' : V' -> Prop, select pred G ≼c select pred' G'
            | ⟨S,⟨φ⟩⟩ := by {
                let pred' : V' -> Prop := detail.lift_pred pred φ, use pred',
                let S' := detail.lift_setup pred φ, use S',
                refine ⟨_⟩,

                --------

                have lemma3 : ∀ {x y : { y // pred' y }}, S'.g.adj x y <-> S.g.adj x.val y.val := λ x y, iff.rfl,

                have lemma1 : ∀ {x y : { y // pred' y }}, S'.g.linked x y <-> S.g.linked x.val y.val
                    := by {
                        intros x y, split,
                        { rintro ⟨p⟩, induction p with a a b c h p ih, refl, exact linked.cons (lemma3.mp h) ih },
                        { rintro ⟨p⟩, induction p with a a b c h p ih generalizing x y, sorry, sorry }
                    },

                have lemma2 : ∀ x y : { y // pred' y }, S'.proj x = S'.proj y <-> S.proj x.val = S.proj y.val := sorry,

                have := detail.lemma2,

                let Φ : select pred G ≃g (select pred' G')/S' := {
                    to_fun := detail.restrict φ pred,
                    inv_fun := detail.restrict_inv φ pred,
                    left_inv := detail.lemma2,
                    right_inv := detail.lemma3,
                    map_rel_iff' := sorry
                },

                refine ⟨S',⟨Φ⟩⟩
            }

        @[trans] lemma trans : G ≼c G' -> G' ≼c G'' -> G ≼c G''
            | ⟨S,⟨f1⟩⟩ ⟨S',⟨f2⟩⟩ :=
                let T := S.fmap_isom f2,
                    f3 := fmap_iso f2 S,
                    f4 := setup.comp.iso T
                in ⟨S'.comp T,⟨f4.symm.comp (f3.comp f1)⟩⟩
    end is_contraction
end simple_graph

import tactic
import graph_theory.basic graph_theory.path_embedding
open function
open_locale classical

namespace simple_graph
    open walk
    variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    namespace contract
        @[ext] structure setup (G : simple_graph V) :=
            (g : simple_graph V)
            (sub : ∀ {x y : V}, g.adj x y -> G.adj x y)

        namespace setup
            def support (S : setup G) : Type := V

            instance setoid (S : setup G) : setoid S.support
                := ⟨S.g.linked,simple_graph.linked.equiv⟩

            def clusters (S : setup G) := quotient S.setoid

            def adj (S : setup G) (x y : S.clusters) : Prop
                := x ≠ y ∧ ∃ x' y' : V, ⟦x'⟧ = x ∧ ⟦y'⟧ = y ∧ G.adj x' y'

            @[symm] lemma symm (S : setup G) (x y : S.clusters) : S.adj x y -> S.adj y x
                | ⟨h0,x',y',h1,h2,h3⟩ := ⟨h0.symm,y',x',h2,h1,h3.symm⟩
        end setup
    end contract

    def contract (G : simple_graph V) (S : contract.setup G) : simple_graph S.clusters := ⟨S.adj, S.symm⟩

    notation G `/` S := contract G S

    namespace contract
        variables {S : setup G} {x y : S.support} {xx yy : S.clusters}
        open classical quotient

        lemma proj_adj (h : G.adj x y) : ⟦x⟧ = ⟦y⟧ ∨ (G/S).adj ⟦x⟧ ⟦y⟧
            := dite (⟦x⟧ = ⟦y⟧) or.inl (λ h', or.inr ⟨h',x,y,rfl,rfl,h⟩)

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

        lemma contract_connected_iff : connected G <-> connected (G/S)
            := { mp := λ h xx yy, by {
                    obtain ⟨x, hx : ⟦x⟧ = xx⟩ := quot.exists_rep xx, subst hx,
                    obtain ⟨y, hy : ⟦y⟧ = yy⟩ := quot.exists_rep yy, subst hy,
                    exact project_linked (h x y) },
                mpr := λ h x y, lift_linked (h ⟦x⟧ ⟦y⟧) }


        @[simp] def bot {G : simple_graph V} : setup G := ⟨⊥, λ x y, false.rec _⟩
        instance : has_bot (setup G) := ⟨bot⟩

        lemma proj_bot_inj {x y : (@bot V G).support} : ⟦x⟧ = ⟦y⟧ -> x = y
            := by { intro h, cases quotient.eq.mp h with p, cases p, refl, simp at p_h, contradiction }

        lemma proj_bot_inj' {x y : (@bot V G).support} : G.adj x y -> ⟦x⟧ ≠ ⟦y⟧
            | h1 h2 := G.loopless y $ by { rw proj_bot_inj h2 at h1, exact h1 }

        def proj_bot : G →g G/⊥
            := {
                to_fun := λ x, ⟦x⟧,
                map_rel' := λ x y h, ⟨proj_bot_inj' h, ⟨x,y,rfl,rfl,h⟩ ⟩
            }

        def comp (S : setup G) (S' : setup (G/S)) : setup G
            := {
                g := {
                    adj := λ x y, x ≠ y ∧ (S.g.adj x y ∨ (G.adj x y ∧ S'.g.adj ⟦x⟧ ⟦y⟧)),
                    symm := λ x y, by { rintros ⟨h1,h2⟩, refine ⟨h1.symm,_⟩, cases h2, left, exact h2.symm,
                                        right, exact ⟨h2.1.symm,h2.2.symm⟩ }
                },
                sub := λ x y, by { rintros ⟨h1,h2⟩, cases h2, exact S.sub h2, exact h2.1 }
            }

        variables {S' : setup (G/S)}

        lemma comp_linked_mp : (comp S S').g.linked x y -> S'.g.linked ⟦x⟧ ⟦y⟧
            := by { rintro ⟨p⟩, induction p with a a b c h p ih, refl, cases h with h1 h2, cases h2,
                    { have := linked.step h2, have := (@quotient.eq S.support _ a b).mpr this, rw this, exact ih },
                    { refine linked.cons _ ih, exact h2.2 } }

        lemma comp_linked_mpr_aux : ⟦x⟧ = ⟦y⟧ -> (comp S S').g.linked x y
            | h := linked.linked_of_subgraph (λ x y ha, ⟨S.g.ne_of_adj ha, or.inl ha⟩) (quotient.eq.mp h)

        lemma comp_linked_mpr_aux' : S'.g.adj ⟦x⟧ ⟦y⟧ -> (comp S S').g.linked x y
            | h := by { rcases S'.sub h with ⟨h1,x',y',hx,hy,h2⟩, rw [<-hx,<-hy] at h,
                transitivity x', exact comp_linked_mpr_aux hx.symm,
                transitivity y', swap, exact comp_linked_mpr_aux hy,
                exact linked.step ⟨G.ne_of_adj h2, or.inr ⟨h2,h⟩⟩ }

        lemma comp_linked_mpr : S'.g.linked xx yy -> (comp S S').g.linked xx.out yy.out
            := by { rintro ⟨p⟩, induction p with aa aa bb cc hh pp ih,
                { apply comp_linked_mpr_aux, refl },
                { transitivity bb.out, swap, exact ih, clear ih, apply comp_linked_mpr_aux', convert hh; apply out_eq } }

        lemma comp_linked : (comp S S').g.linked x y <-> S'.g.linked ⟦x⟧ ⟦y⟧
            := by { split,
                { exact comp_linked_mp },
                { intro h, transitivity ⟦x⟧.out, apply comp_linked_mpr_aux, symmetry, apply out_eq,
                    transitivity ⟦y⟧.out, exact comp_linked_mpr h, apply comp_linked_mpr_aux, apply out_eq } }

        @[simp] lemma comp_rep_spec (S : setup G) (x : S.clusters) : ⟦x.out⟧ = x := out_eq _
        lemma comp_rep_iff (S : setup G) (x y : S.clusters) : x.out ≈ y.out <-> x = y := out_equiv_out

        lemma comp_sound {S : setup G} (S' : setup (G/S)) : nonempty (G/comp S S' ≃g G/S/S')
            := by {
                let f : (comp S S').clusters ≃ S'.clusters := {
                    to_fun := λ xxx, ⟦⟦xxx.out⟧⟧,
                    inv_fun := λ xxx, ⟦xxx.out.out⟧,
                    left_inv := λ xxx, by {
                        dsimp,
                        have := out_eq xxx,
                        set x := out xxx,
                        rw <-this,
                        apply quotient.eq.mpr,
                        apply comp_linked.mpr,
                        set z : S.support := (x : V),
                        set uu : S'.support := ⟦z⟧,
                        rw out_eq ⟦uu⟧.out,
                        change ⟦uu⟧.out ≈ uu,
                        apply mk_out
                    },
                    right_inv := λ xxx, by {
                        dsimp,
                        have h1 := out_eq xxx,
                        have h2 := out_eq xxx.out,
                        set x := xxx.out.out,
                        rw <-h1, rw <-h2,
                        apply quotient.eq.mpr,
                        apply comp_linked_mp,
                        set y : (comp S S').support := x,
                        change ⟦y⟧.out ≈ y,
                        apply mk_out
                    }
                },
                refine ⟨⟨f,_⟩⟩, intros a b, dsimp, split,
                    { rintro ⟨h1,xx,yy,h2,h3,h4,u,v,h5,h6,h7⟩, split, { intro h, rw h at h1, apply h1, refl },
                        substs xx yy, refine ⟨u,v,_,_,h7⟩,
                            rw <-out_eq a, apply quotient.eq.mpr, apply comp_linked.mpr,
                                replace h2 := quotient.eq.mp h2, exact h2,
                            rw <-out_eq b, apply quotient.eq.mpr, apply comp_linked.mpr,
                                replace h3 := quotient.eq.mp h3, exact h3 },
                    { rintro ⟨h1,x,y,h2,h3,h4⟩, split, {
                            intro h, have := quotient.eq.mp h, have h5 := comp_linked.mpr this, substs a b,
                            set x : (comp S S').support := x, set y : (comp S S').support := y,
                            change ⟦x⟧.out ≈ ⟦y⟧.out at h5, have := quotient.eq.mpr h5,
                            rw out_eq ⟦x⟧ at this, rw out_eq ⟦y⟧ at this, exact h1 this },
                        substs a b, refine ⟨⟦x⟧,⟦y⟧,_,_,_,x,y,rfl,rfl,h4⟩,
                            { apply quotient.eq.mpr, apply comp_linked.mp, set x : (comp S S').support := x,
                                change x ≈ ⟦x⟧.out, apply quotient.eq.mp, symmetry, apply out_eq },
                            { apply quotient.eq.mpr, apply comp_linked.mp, set y : (comp S S').support := y,
                                change y ≈ ⟦y⟧.out, apply quotient.eq.mp, symmetry, apply out_eq },
                            { intro h, replace h := quotient.eq.mp h, change S.g.linked x y at h,
                                have : (comp S S').g.linked x y, { apply linked.linked_of_subgraph _, exact h,
                                    intros x y h, refine ⟨_,or.inl h⟩, intro, subst y, apply S.g.ne_of_adj h, refl },
                                apply h1, apply quotient.eq.mpr, exact this } }
            }

        def extend {S' : setup G'} (f : G →g G'/S') (h : injective f) (S : setup G) : setup (G'/S')
            := {
                g := {
                    adj := λ xx yy, ∃ x y : V, xx = f x ∧ yy = f y ∧ S.g.adj x y,
                    symm := λ xx yy, by { rintros ⟨x,y,h1,h2,h3⟩, exact ⟨y,x,h2,h1,h3.symm⟩ },
                    loopless := λ xx h', by { rcases h' with ⟨x,y,h1,h2,h'⟩, subst h1, refine S.g.ne_of_adj h' (h h2) }
                },
                sub := by { rintros xx yy ⟨x,y,h1,h2,h3⟩, substs xx yy, exact f.map_rel' (S.sub h3) }
            }

        def is_contract (G : simple_graph V) (G' : simple_graph V') : Prop := ∃ S : contract.setup G', nonempty (G ≃g (G'/S))

        def contract_isom (f : G ≃g G') (S : setup G) : setup G'
            := {
                g := {
                    adj := λ x y, S.g.adj (f.inv_fun x) (f.inv_fun y),
                    symm := λ x' y' h, S.g.symm h,
                    loopless := λ x, S.g.loopless _
                },
                sub := λ x y, by { simp, intro h, have h1 := S.sub h, have h2 := f.map_rel_iff', convert h2.mpr h1,
                    have := rel_iso.apply_symm_apply f x, exact this.symm, have := rel_iso.apply_symm_apply f y, exact this.symm }
            }

        lemma contract_isom_inv (f : G ≃g G') (S : setup G) : contract_isom f.symm (contract_isom f S) = S
            := by { have hf : f.symm.to_equiv.symm = f.to_equiv := by { ext, refl }, ext, split; intro h,
                { simp [contract_isom,hf] at h, convert h; symmetry; exact rel_iso.symm_apply_apply _ _ },
                { simp [contract_isom,hf], convert h; exact rel_iso.symm_apply_apply _ _ } }

        lemma linked_isom_mp (f : G ≃g G') (S : setup G) (x y : V) : S.g.linked x y -> (contract_isom f S).g.linked (f x) (f y)
            := by {
                intro h, cases h with p, induction p with a a b c h q ih, refl,
                refine linked.cons _ ih,
                simp [contract_isom], convert h; exact rel_iso.symm_apply_apply _ _
            }

        lemma linked_isom (f : G ≃g G') (S : setup G) (x y : V) : S.g.linked x y <-> (contract_isom f S).g.linked (f x) (f y)
            := by { split, exact linked_isom_mp f S x y, intro h,
                replace h := linked_isom_mp f.symm (contract_isom f S) (f x) (f y) h,
                simp [contract_isom_inv] at h, exact h }

        noncomputable def map_isom (f : G ≃g G') (S : setup G) : (G/S) ≃g (G'/contract_isom f S)
            := {
                    to_fun := λ xx, ⟦f xx.out⟧,
                    inv_fun := λ xx', ⟦f.symm xx'.out⟧,
                    left_inv := λ xx, by {
                        transitivity ⟦xx.out⟧, swap, exact out_eq xx,
                        apply quotient.eq.mpr,
                        set x := out xx,
                        apply (linked_isom f _ _ _).mpr,
                        simp, set y : (contract_isom f S).support := f x, exact mk_out y },
                    right_inv := λ yy, by {
                        transitivity ⟦yy.out⟧, swap, exact out_eq yy,
                        apply quotient.eq.mpr,
                        set y := out yy,
                        apply (linked_isom f.symm _ _ _).mpr,
                        simp, set x : S.support := f.symm y, rw contract_isom_inv, exact mk_out x },
                    map_rel_iff' := by {
                        intros xx yy, split,
                        { intro h, rcases h with ⟨h1,x',y',h2,h3,h4⟩, refine ⟨_,_⟩,
                            intro h, rw h at h1, contradiction,
                            refine ⟨f.symm x',f.symm y',_,_,_⟩,
                                rw <-out_eq xx, apply quotient.eq.mpr, have := (linked_isom f S _ _).mpr, apply this,
                                    replace h2 := quotient.eq.mp h2, rw rel_iso.apply_symm_apply, exact h2,
                                rw <-out_eq yy, apply quotient.eq.mpr, have := (linked_isom f S _ _).mpr, apply this,
                                    replace h3 := quotient.eq.mp h3, rw rel_iso.apply_symm_apply, exact h3,
                                have := f.symm.map_rel_iff', have := this.mpr h4, exact this },
                        { intro h, rcases h with ⟨h1,x,y,h2,h3,h4⟩, refine ⟨_,_⟩,
                            simp, substs xx yy, intro h, have := linked_isom f _ _ _, have h' := this.mpr h,
                                set x : S.support := x, set y : S.support := y, have : ⟦x⟧.out ≈ ⟦y⟧.out := h',
                                have := quotient.eq.mpr this, rw [out_eq,out_eq] at this, exact h1 this,
                            simp, refine ⟨f x, _, f y, _, _⟩,
                                have := linked_isom f _ _ _, apply this.mp, symmetry, rw <-h2, set x : S.support := x, exact mk_out x,
                                have := linked_isom f _ _ _, apply this.mp, symmetry, rw <-h3, set y : S.support := y, exact mk_out y,
                                have := f.map_rel_iff', apply this.mpr, exact h4 } }
            }

        @[trans] lemma trans : is_contract G G' -> is_contract G' G'' -> is_contract G G''
            := by { rintros ⟨S,⟨f1⟩⟩ ⟨S',⟨f2⟩⟩,
                cases comp_sound (contract_isom f2 S) with φ,
                refine ⟨comp S' (contract_isom f2 S), ⟨_⟩⟩,
                refine iso.comp φ.symm _, clear φ,
                exact iso.comp (map_isom f2 S) f1 }

        def empty_setup (G : simple_graph V): setup G := { g := ⊥, sub := λ x y, false.rec _ }

        lemma eq_of_linked_bot : linked (⊥ : simple_graph V) x y -> x = y
            := by { intro h, cases h with p, induction p with a a b c h p ih, refl, simp at h, contradiction }

        lemma eq_of_same_class {x y : (empty_setup G).support} : ⟦x⟧ = ⟦y⟧ -> x = y
            | h := eq_of_linked_bot (quotient.eq.mp h)

        noncomputable def empty_iso : (G ≃g G/empty_setup G)
            := {
                to_fun := λ x, ⟦x⟧,
                inv_fun := out,
                left_inv := λ x, by { apply eq_of_same_class, simp },
                right_inv := λ xx, by simp,
                map_rel_iff' := λ x y, by { simp, split,
                    { intro h, rcases h with ⟨h1,x',y',h2,h3,h4⟩,
                        replace h2 := eq_of_same_class h2, subst x',
                        replace h3 := eq_of_same_class h3, subst y', exact h4 },
                    { intro h, refine ⟨_,x,y,rfl,rfl,h⟩,
                        intro h1, replace h1 := eq_of_same_class h1, subst y, exact G.ne_of_adj h rfl } } }

        @[refl] lemma refl : is_contract G G := ⟨empty_setup G,⟨empty_iso⟩⟩
    end contract
    open contract

    def is_smaller (G : simple_graph V) (G' : simple_graph V') : Prop := ∃ f : G →g G', injective f

    lemma smaller_refl : is_smaller G G := ⟨⟨id, λ x y, id⟩, injective_id⟩

    def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop := ∃ (V'' : Type) (G'' : simple_graph V''), is_smaller G G'' ∧ is_contract G'' G'

    lemma minor_contract : is_minor G G' -> is_contract G' G'' -> is_minor G G''
        | ⟨U,H,h3,h4⟩ h2 := ⟨U,H,h3,contract.trans h4 h2⟩

    lemma minor_smaller : is_minor G G' -> is_smaller G' G'' -> is_minor G G''
        := sorry

    def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

    infix ` ≼ `:50 := is_minor
    infix ` ⋠ `:50 := is_forbidden

    namespace minor
        open contract quotient

        @[refl] lemma refl : G ≼ G := ⟨_,G,smaller_refl,refl⟩

        @[trans] lemma trans : G ≼ G' -> G' ≼ G'' -> G ≼ G''
            | h1 ⟨U',H',h3,h4⟩ := minor_contract (minor_smaller h1 h3) h4
    end minor
end simple_graph

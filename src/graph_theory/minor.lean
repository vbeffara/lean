import tactic
import graph_theory.basic graph_theory.path_embedding
open function
open_locale classical

namespace simple_graph
    open walk
    variables {V V' : Type} {G : simple_graph V}

    namespace contract
        structure setup (G : simple_graph V) :=
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

        lemma comp_sound {S : setup G} {S' : setup (G/S)} : nonempty (G/(comp S S') ≃g (G/S)/S')
            := by {
                let f : (comp S S').clusters ≃ S'.clusters := {
                    to_fun := λ xxx, ⟦⟦xxx.out⟧⟧,
                    inv_fun := λ xxx, ⟦xxx.out.out⟧,
                    left_inv := λ xxx, by {
                        dsimp, apply out_equiv_out.mp, sorry
                    },
                    right_inv := λ xxx, by {
                        dsimp, apply out_equiv_out.mp, sorry
                    }
                },
                refine ⟨⟨f,_⟩⟩, sorry
            }
    end contract

    def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ S : contract.setup G', ∃ f : G →g G'/S, injective f

    def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

    infix ` ≼ `:50 := is_minor
    infix ` ⋠ `:50 := is_forbidden

    namespace minor
        open contract

        @[refl] lemma refl {G : simple_graph V } : G ≼ G := ⟨⊥, proj_bot, λ x y, proj_bot_inj⟩
    end minor
end simple_graph

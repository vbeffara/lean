import tactic
import graph_theory.basic graph_theory.path_embedding graph_theory.contraction
open function
open_locale classical

namespace simple_graph
    open walk
    variables {V V' V'' : Type} {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

    namespace contraction
        variables {S : setup G} {x y : S.support} {xx yy : S.clusters}
        open classical quotient

        variables {S' : setup (G/S)}

        def extend {S' : setup G'} (f : G →g G'/S') (h : injective f) (S : setup G) : setup (G'/S')
            := {
                g := {
                    adj := λ xx yy, ∃ x y : V, xx = f x ∧ yy = f y ∧ S.g.adj x y,
                    symm := λ xx yy, by { rintros ⟨x,y,h1,h2,h3⟩, exact ⟨y,x,h2,h1,h3.symm⟩ },
                    loopless := λ xx h', by { rcases h' with ⟨x,y,h1,h2,h'⟩, subst h1, refine S.g.ne_of_adj h' (h h2) }
                },
                sub := by { rintros xx yy ⟨x,y,h1,h2,h3⟩, substs xx yy, exact f.map_rel' (S.sub h3) }
            }

        lemma linked_isom_mp (f : G ≃g G') (S : setup G) (x y : V) : S.g.linked x y -> (S.fmap_isom f).g.linked (f x) (f y)
            := by {
                intro h, cases h with p, induction p with a a b c h q ih, refl,
                refine linked.cons _ ih,
                simp [setup.fmap_isom,on_fun], convert h; exact rel_iso.symm_apply_apply _ _
            }

        lemma linked_isom (f : G ≃g G') (S : setup G) (x y : V) : S.g.linked x y <-> (S.fmap_isom f).g.linked (f x) (f y)
            := by { split, exact linked_isom_mp f S x y, intro h,
                replace h := linked_isom_mp f.symm (S.fmap_isom f) (f x) (f y) h,
                simp [setup.fmap_isom.inv] at h, exact h }

        noncomputable def map_isom (f : G ≃g G') (S : setup G) : (G/S) ≃g (G'/S.fmap_isom f)
            := {
                    to_fun := λ xx, ⟦f xx.out⟧,
                    inv_fun := λ xx', ⟦f.symm xx'.out⟧,
                    left_inv := λ xx, by {
                        transitivity ⟦xx.out⟧, swap, exact out_eq xx,
                        apply quotient.eq.mpr,
                        set x := out xx,
                        apply (linked_isom f _ _ _).mpr,
                        simp, set y : (S.fmap_isom f).support := f x, exact mk_out y },
                    right_inv := λ yy, by {
                        transitivity ⟦yy.out⟧, swap, exact out_eq yy,
                        apply quotient.eq.mpr,
                        set y := out yy,
                        apply (linked_isom f.symm _ _ _).mpr,
                        simp, set x : S.support := f.symm y, rw contraction_isom_inv, exact mk_out x },
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

        @[trans] lemma trans : G ≼c G' -> G' ≼c G'' -> G ≼c G''
            | ⟨S,⟨f1⟩⟩ ⟨S',⟨f2⟩⟩ := let T := S.fmap_isom f2 in
                ⟨S'.comp T, ⟨(setup.comp.iso T).symm.comp ((map_isom f2 S).comp f1)⟩⟩

    end contraction
    open contraction

    def is_minor (G : simple_graph V) (G' : simple_graph V') : Prop
        := ∃ {V'' : Type} (G'' : simple_graph V''), G ≼s G'' ∧ G'' ≼c G'

    def is_forbidden (H : simple_graph V) (G : simple_graph V') := ¬ (is_minor H G)

    infix ` ≼ `:50 := is_minor
    infix ` ⋠ `:50 := is_forbidden

    lemma minor_contraction : G ≼ G' -> G' ≼c G'' -> G ≼ G''
        | ⟨U,H,h3,h4⟩ h2 := ⟨U,H,h3,contraction.trans h4 h2⟩

    lemma minor_smaller : G ≼ G' -> G' ≼s G'' -> G ≼ G''
        := sorry

    namespace minor
        open contraction quotient

        @[refl] lemma refl : G ≼ G := ⟨_,G,smaller_refl,refl⟩

        @[trans] lemma trans : G ≼ G' -> G' ≼ G'' -> G ≼ G''
            | h1 ⟨U',H',h3,h4⟩ := minor_contraction (minor_smaller h1 h3) h4
    end minor
end simple_graph

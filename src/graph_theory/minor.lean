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

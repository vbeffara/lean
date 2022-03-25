import tactic
import graph_theory.minor graph_theory.product analysis.complex.basic

namespace simple_graph

def Z : simple_graph ℤ :=
{ adj := λ x y, |x-y| = 1,
  symm := λ x y h, by { rw ←h, convert abs_neg _, ring },
  loopless := λ x, by simp only [sub_self, abs_zero, zero_ne_one, not_false_iff] }

variables {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'}

def plane : simple_graph (ℤ × ℤ) := Z □ Z

namespace plane
variables {x x' y y' z z' : ℤ}
open walk

def flip : plane →g plane :=
{ to_fun := prod.swap,
  map_rel' := by { rintros ⟨x,y⟩ ⟨x',y'⟩ h, cases h,
    { right, exact and.symm h },
    { left, exact and.symm h } } }

lemma horiz_path_aux : ∀ (n : ℕ), reachable plane (x,y) (x+n,y)
| 0     := by simp
| (n+1) := by { refine reachable.trans (horiz_path_aux n) (reachable.step (or.inr _)), simp [Z] }

lemma horiz_path : reachable plane (x,y) (x',y) :=
begin
  by_cases (x'-x>=0),
  { obtain ⟨n,hn⟩ := int.eq_coe_of_zero_le h, convert horiz_path_aux n, linarith },
  { replace h : x-x' ≥ 0, by linarith, obtain ⟨n,hn⟩ := int.eq_coe_of_zero_le h,
    symmetry, convert (@horiz_path_aux x' y n), linarith }
end

lemma vert_path : reachable plane (x,y) (x,y') :=
by { obtain ⟨p⟩ := horiz_path, use p.map flip }

lemma connected_plane : connected plane :=
⟨λ ⟨x,y⟩ ⟨x',y'⟩, reachable.trans horiz_path vert_path, ⟨(0,0)⟩⟩

end plane

def K5 := complete_graph (finset.range 5)
def K33 := complete_bipartite_graph (finset.range 3) (finset.range 3)

-- theorem kuratowski [fintype V] : G ≼ plane ↔ K5 ⋠ G ∧ K33 ⋠ G
end simple_graph

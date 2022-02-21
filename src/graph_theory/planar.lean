import tactic
import graph_theory.minor analysis.complex.basic

namespace simple_graph

variables {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'}

def plane.adj : ℤ × ℤ → ℤ × ℤ → Prop
| (x,y) (x',y') := (x = x' ∧ |y - y'| = 1) ∨ (|x-x'| = 1 ∧ y = y')

lemma plane.adj_symm : symmetric plane.adj
| (x,y) (x',y') (or.inl ⟨h1,h2⟩) := or.inl ⟨h1.symm, by { rw <-h2, convert abs_neg _, linarith }⟩
| (x,y) (x',y') (or.inr ⟨h1,h2⟩) := or.inr ⟨by { rw <-h1, convert abs_neg _, linarith }, h2.symm⟩

def plane : simple_graph (ℤ × ℤ) := -- TODO product of Z_as_graph
⟨plane.adj,plane.adj_symm⟩

namespace plane
variables {x x' y y' z z' : ℤ}
open walk

def flip' : ℤ × ℤ → ℤ × ℤ | (x,y) := (y,x)

def flip : plane →g plane :=
{ to_fun := flip',
  map_rel' := by { rintros ⟨x,y⟩ ⟨x',y'⟩ h, cases h,
    { right, exact and.symm h },
    { left, exact and.symm h } } }

def horiz_path_aux : ∀ (n : ℕ), linked plane (x,y) (x+n,y)
| 0     := by simp
| (n+1) := by { refine linked.trans (horiz_path_aux n) (linked.step (or.inr _)), simp }

def horiz_path : linked plane (x,y) ⟨x',y⟩ :=
begin
  by_cases (x'-x>=0),
  { obtain ⟨n,hn⟩ := int.eq_coe_of_zero_le h, convert horiz_path_aux n, linarith },
  { replace h : x-x' ≥ 0, by linarith, obtain ⟨n,hn⟩ := int.eq_coe_of_zero_le h,
    symmetry, convert (@horiz_path_aux x' y n), linarith }
end

def vert_path : linked plane (x,y) (x,y') :=
linked.fmap flip horiz_path

lemma connected_plane : connected plane :=
λ ⟨x,y⟩ ⟨x',y'⟩, linked.trans horiz_path vert_path

end plane

def K5 := complete_graph (finset.range 5)
def K33 := complete_bipartite_graph (finset.range 3) (finset.range 3)

-- theorem kuratowski [fintype V] : G ≼ plane <→ K5 ⋠ G ∧ K33 ⋠ G
end simple_graph

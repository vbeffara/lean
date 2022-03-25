import combinatorics.simple_graph.metric
import graph_theory.path

namespace simple_graph
namespace cayley

structure genset (G : Type*) [group G] :=
  (els : finset G)
  (sym : ∀ {s : G}, s ∈ els → s⁻¹ ∈ els)
  (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
  (nem : els.nonempty)
  (irr : (1:G) ∉ els)

variables {G : Type*} [group G] {S S1 S2 : genset G} {a x y z : G}

instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩

def genset.adj (S : genset G) (x y : G) := x⁻¹ * y ∈ S

lemma shift_adj ⦃x y⦄ (h : S.adj x y) : S.adj (a*x) (a*y) :=
by { unfold genset.adj, convert h using 1, group }

@[symm] lemma adj_symm ⦃x y⦄ (h : S.adj x y) : S.adj y x
:= by { unfold genset.adj, convert S.sym h, group }

def Cay (S : genset G) : simple_graph G :=
{ adj := S.adj,
  symm := adj_symm,
  loopless := λ x h, S.irr (by { convert h, group }) }

def left_shift (a : G) : Cay S →g Cay S := ⟨(*) a, shift_adj⟩

lemma shift : reachable (Cay S) x y → reachable (Cay S) (a*x) (a*y) :=
nonempty.map (walk.map (left_shift a))

lemma inv {h : reachable (Cay S) 1 x} : reachable (Cay S) 1 x⁻¹ :=
by { symmetry, convert @shift _ _ _ x⁻¹ _ _ h; group }

lemma reachable_mp : reachable (Cay S) 1 x :=
begin
  apply subgroup.closure_induction,
  { rw S.gen, trivial },
  { intros y h, apply reachable.step, simpa only [Cay,genset.adj,one_inv,one_mul] },
  { refl },
  { intros u v h1 h2, refine reachable.trans h1 _, convert shift h2, group },
  { intros y h, apply inv, exact h }
end

theorem Cay.connected : connected (Cay S) :=
⟨λ x y, reachable_mp.symm.trans reachable_mp, ⟨1⟩⟩

lemma covariant : (Cay S).dist (a*x) (a*y) = (Cay S).dist x y :=
begin
  have lem : ∀ a {x y}, (Cay S).dist (a*x) (a*y) ≤ (Cay S).dist x y :=
  by { intros a x y, obtain ⟨p,hp⟩ := Cay.connected.exists_walk_of_dist x y,
    rw [←hp,←walk.length_map], exact dist_le (p.map (left_shift a)) },
  apply le_antisymm (lem a), convert lem a⁻¹, group
end

noncomputable def distorsion (S1 S2 : genset G) :=
classical.some (finset.max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

lemma distorsion_spec : distorsion S1 S2 ∈ (finset.image ((Cay S2).dist 1) S1.els).max :=
classical.some_spec (finset.max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

lemma distorsion_le {h : (Cay S1).adj x y} : (Cay S2).dist x y ≤ distorsion S1 S2 :=
begin
  refine finset.le_max_of_mem _ distorsion_spec,
  rw [finset.mem_image], refine ⟨x⁻¹ * y, h, _⟩, convert covariant, group
end

lemma lipschitz : (Cay S2).dist x y <= (distorsion S1 S2) * (Cay S1).dist x y :=
begin
  obtain ⟨p,hp⟩ := (@Cay.connected _ _ S1).exists_walk_of_dist x y, rw <-hp, clear hp,
  induction p with u u v w h p ih,
  { simp only [dist_self, walk.length_nil, mul_zero] },
  { simp only [walk.length_cons], transitivity (Cay S2).dist u v + (Cay S2).dist v w,
    apply Cay.connected.dist_triangle, rw [mul_add,mul_one,add_comm],
    apply add_le_add ih, apply distorsion_le, exact h }
end

end cayley
end simple_graph

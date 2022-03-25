import combinatorics.simple_graph.metric
import graph_theory.path

namespace simple_graph
namespace cayley
open walk relation.refl_trans_gen classical finset

structure genset (G : Type*) [group G] :=
  (els : finset G)
  (sym : ∀ {s : G}, s ∈ els → s⁻¹ ∈ els)
  (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
  (nem : els.nonempty)
  (irr : (1:G) ∉ els)

variables {G : Type*} [group G] (S S1 S2 : genset G) (a : G) {x y z : G}

instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩

def adj (x y : G) := x⁻¹ * y ∈ S

@[simp] lemma cancel (a x y : G) : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group

lemma shift_adj {S : genset G} (h : adj S x y) : adj S (a*x) (a*y) :=
by { unfold adj, rw cancel, exact h }

@[symm] lemma adj_symm (x y) (h : adj S x y) : adj S y x
:= by { unfold adj, convert S.sym h, group }

def Cay (S : genset G) : simple_graph G :=
{ adj := adj S,
  symm := adj_symm S,
  loopless := λ x h, S.irr (by { convert h, group }) }

def left_shift : (Cay S) →g (Cay S) :=
⟨(*) a, λ x y, shift_adj a⟩

def shift_path : walk (Cay S) x y → walk (Cay S) (a*x) (a*y) :=
fmap (left_shift S a)

lemma shift : reachable (Cay S) x y → reachable (Cay S) (a*x) (a*y) :=
nonempty.map (shift_path S a)

lemma inv : reachable (Cay S) 1 x → reachable (Cay S) 1 x⁻¹ :=
by { intro h, symmetry, convert shift S x⁻¹ h; group }

lemma reachable_mp : reachable (Cay S) 1 x :=
begin
  apply subgroup.closure_induction,
  { rw S.gen, trivial },
  { intros y h, apply reachable.step, simp only [Cay,adj], convert h, group },
  { refl },
  { intros u v h1 h2, refine reachable.trans h1 _, convert shift _ u h2, group },
  { intros y h, apply inv, exact h }
end

theorem connected : connected (Cay S) :=
begin
  split,
  { intros x y, transitivity (1:G), symmetry, apply reachable_mp, apply reachable_mp },
  { use 1 }
end

instance : connected_graph (Cay S) := ⟨connected S⟩

noncomputable def word_dist : G → G → ℕ := (Cay S).dist

-- TODO this should use the simple_graph.metric API instead
def dists {V : Type*} (G : simple_graph V) (x y : V) : set ℕ :=
set.range (length : walk G x y -> ℕ)

lemma covariant : (Cay S).dist (a*x) (a*y) = (Cay S).dist x y :=
begin
  unfold simple_graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
  set dists := dists (Cay S),
  have h2 : ∀ x y a ℓ, ℓ ∈ dists x y → ℓ ∈ dists (a*x) (a*y) :=
  by { intros x y a ℓ h, cases h with p, use shift_path S a p, simpa [shift_path] },
  exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
    h2 x y a ℓ⟩
end

noncomputable def distorsion (S1 S2 : genset G) :=
some (max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

lemma distorsion_spec : distorsion S1 S2 ∈ (image ((Cay S2).dist 1) S1.els).max :=
some_spec (max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

lemma distorsion_le {h : (Cay S1).adj x y} : (Cay S2).dist x y ≤ distorsion S1 S2 :=
begin
  refine finset.le_max_of_mem _ (distorsion_spec S1 S2),
  rw [finset.mem_image], refine ⟨x⁻¹ * y, h, _⟩, convert covariant _ x⁻¹, group
end

lemma lipschitz : (Cay S2).dist x y <= (distorsion S1 S2) * (Cay S1).dist x y :=
begin
  obtain ⟨p,hp⟩ := (connected S1).exists_walk_of_dist x y, rw <-hp, clear hp,
  induction p with u u v w h p ih,
  { simp only [dist_self, walk.length_nil, mul_zero] },
  { simp only [walk.length_cons], transitivity (Cay S2).dist u v + (Cay S2).dist v w,
    apply (connected S2).dist_triangle, rw [mul_add,mul_one,add_comm],
    apply add_le_add ih, apply distorsion_le, exact h }
end

end cayley
end simple_graph

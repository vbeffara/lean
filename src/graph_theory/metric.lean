import graph_theory.path
import topology.metric_space.basic

namespace simple_graph
variables {V : Type*} {G : simple_graph V} [connected_graph G] (a : V) {x y z : V}
open walk

def dists (G : simple_graph V) (x y : V) := set.range (length : walk G x y -> ℕ)

lemma dists_ne_empty : (dists G x y).nonempty :=
set.range_nonempty_iff_nonempty.mpr (connected_graph.conn x y)

lemma exists_dist : ∃ n : ℕ, n ∈ dists G x y :=
by { cases dists_ne_empty with n hn, exact ⟨n, hn⟩, apply_instance }

noncomputable def dist (G : simple_graph V) [connected_graph G] (x y : V) : ℕ :=
by { classical, exact @nat.find (dists G x y) _ exists_dist }

lemma upper_bound (p : walk G x y) : dist G x y <= length p :=
by { apply nat.find_le, exact ⟨p, rfl⟩ }

lemma shortest_path (G : simple_graph V) [connected_graph G] (x y) :
  ∃ p : walk G x y, length p = dist G x y :=
by { apply set.mem_range.mp, apply nat.find_spec exists_dist }

@[simp] lemma dist_self : dist G x x = 0 :=
le_antisymm (upper_bound (nil : walk G x x)) (zero_le _)

lemma dist_triangle : dist G x z ≤ dist G x y + dist G y z :=
begin
  obtain ⟨p,hp⟩ := shortest_path G x y, obtain ⟨q,hq⟩ := shortest_path G y z,
  rw [<-hp,<-hq,<-length_append], exact upper_bound _
end

lemma eq_of_dist_eq_zero (h : dist G x y = 0) : x = y :=
by { obtain ⟨p,hₚ⟩ := shortest_path G x y, cases p, refl, rw h at hₚ, contradiction }

lemma dist_comm' : dist G x y <= dist G y x :=
by { obtain ⟨p,hₚ⟩ := shortest_path G y x, rw [<-hₚ, <-length_reverse p], apply upper_bound }

lemma dist_comm : dist G x y = dist G y x :=
le_antisymm dist_comm' dist_comm'

noncomputable instance has_dist (G : simple_graph V) [connected_graph G] : has_dist V :=
⟨λ x y, simple_graph.dist G x y⟩

noncomputable instance metric_space (G : simple_graph V) [connected_graph G] : metric_space V :=
{ dist_self          := λ x, by { unfold has_dist.dist, norm_cast, exact dist_self },
  eq_of_dist_eq_zero := λ x y, by { unfold has_dist.dist, norm_cast, exact eq_of_dist_eq_zero },
  dist_comm          := λ x y, by { unfold has_dist.dist, norm_cast, exact dist_comm },
  dist_triangle      := λ x y z, by { unfold has_dist.dist, norm_cast, exact dist_triangle } }

end simple_graph

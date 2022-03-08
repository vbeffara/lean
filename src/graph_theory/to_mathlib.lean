import combinatorics.simple_graph.connectivity data.finset.basic

variables {V : Type*} {G : simple_graph V}

namespace finset
@[simp] lemma singleton_inter_nonempty [decidable_eq V] {a : V} {X : finset V} :
  ({a} ∩ X).nonempty ↔ a ∈ X :=
{ mp := not_not.mp ∘ mt singleton_inter_of_not_mem ∘ nonempty_iff_ne_empty.mp,
  mpr := eq.rec (singleton_nonempty a) ∘ eq.symm ∘ singleton_inter_of_mem }
-- by { simp_rw [finset.nonempty,mem_inter,mem_singleton,exists_eq_left] }
end finset

namespace simple_graph
end simple_graph

import combinatorics.simple_graph.connectivity data.finset
open finset classical function

variables {V : Type} [decidable_eq V] {G : simple_graph V} {A B : finset V}

namespace simple_graph
def separates (G : simple_graph V) (A B : finset V) (X : finset V) : Prop :=
∀ {x : V} (hx : x ∈ A) {y : V} (hy : y ∈ B) (γ : walk G x y), ∃ z ∈ X, z ∈ γ.support

structure cut_set (G : simple_graph V) (A B : finset V) :=
    (to_set : finset V)
    (disjoint : to_set ∩ (A ∪ B) = ∅)
    (sep : separates G A B to_set)

def separable (G : simple_graph V) (A B : finset V) : Prop :=
nonempty (cut_set G A B)

def cut_set_sizes (G : simple_graph V) (A B : finset V) : set ℕ :=
set.range (λ X : cut_set G A B, X.to_set.card)

noncomputable def min_cut (h : separable G A B) : ℕ :=
well_founded.min nat.lt_wf (cut_set_sizes G A B) $ set.range_nonempty_iff_nonempty.mpr h

-- TODO: move this up
structure AB_path (G : simple_graph V) (A B : finset V) :=
    (a : A) (b : B) (p : walk G a b)

def joinable (G : simple_graph V) (A B : finset V) : Prop :=
∃ (a : A) (b : B), nonempty (G.walk a b)

structure path_set (G : simple_graph V) (A B : finset V) :=
    (size : ℕ)
    (path : fin size → AB_path G A B)
    (disjoint : ∀ i j : fin size, ∀ z : V, z ∈ (path i).p.support → z ∈ (path j).p.support → i = j)

lemma upper_bound (h : separable G A B) (P : path_set G A B) : P.size ≤ min_cut h :=
begin
    have h₁ := well_founded.min_mem nat.lt_wf (cut_set_sizes G A B) (set.range_nonempty_iff_nonempty.mpr h),
    let X := some h₁,
    have minimal := some_spec h₁, change X.to_set.card = min_cut h at minimal, rw ←minimal,
    simp at minimal,
    let φ : fin P.size → X.to_set := λ i, by {
        let γ := P.path i,
        have h₂ := X.sep γ.a.prop γ.b.prop γ.p,
        let z := some h₂,
        use z,
        have := some_spec h₂,
        use (some this)
    },
    have inp : ∀ i : fin P.size, (φ i : V) ∈ (P.path i).p.support := by {
        intro i,
        let γ := P.path i,
        have h₂ := X.sep γ.a.prop γ.b.prop γ.p,
        let z := some h₂,
        have := some_spec h₂,
        cases this,
        exact this_h
    },
    have inj : injective φ := by {
        intros i j h,
        apply P.disjoint i j (φ i),
        exact inp i,
        rw h,
        exact inp j
    },
    have := fintype.card_le_of_injective φ inj,
    simp at this, exact this
end

-- theorem menger (h : separable G A B) : max_path_number G A B = min_cut h :=
-- sorry
end simple_graph

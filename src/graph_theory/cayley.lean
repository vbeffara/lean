import tactic data.finset.lattice data.set.basic
import graph_theory.path graph_theory.metric topology.metric_space.lipschitz

namespace simple_graph
    namespace cayley
        open walk

        structure genset (G : Type) [group G] :=
            (els : finset G)
            (sym : ∀ {s : G}, s ∈ els -> s⁻¹ ∈ els)
            (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
            (nem : els.nonempty)
            (irr : (1:G) ∉ els)

        variables {G : Type} [group G] (S : genset G) (a : G) {x y z : G}

        instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩

        def adj (x y : G) := x ≠ y ∧ x⁻¹ * y ∈ S

        @[simp] lemma cancel (a x y : G) : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group

        lemma shift_adj {S : genset G} : adj S x y -> adj S (a*x) (a*y)
            | ⟨h1,h2⟩ := ⟨(mul_ne_mul_right a).mpr h1, (cancel a x y).symm ▸ h2⟩

        @[symm] lemma adj_symm (x y) : adj S x y -> adj S y x
            | ⟨h1,h2⟩ := ⟨h1.symm, by { convert S.sym h2, group }⟩

        def Cay (S : genset G) : simple_graph G
            := {
                adj := adj S,
                symm := adj_symm S,
                loopless := λ _, not_and.mpr (λ h1 _, h1 rfl)
            }

        def left_shift : (Cay S) →g (Cay S)
            := ⟨(*) a, λ x y, shift_adj a⟩

        def shift_path : walk (Cay S) x y -> walk (Cay S) (a*x) (a*y)
            := fmap (left_shift S a)

        lemma shift : linked (Cay S) x y -> linked (Cay S) (a*x) (a*y)
            | ⟨p⟩ := ⟨shift_path S a p⟩

        lemma inv : linked (Cay S) 1 x -> linked (Cay S) 1 x⁻¹
            := by { intro h, symmetry, convert shift S x⁻¹ h; group }

        lemma linked_mp : linked (Cay S) 1 x
            := by { apply subgroup.closure_induction,
                { rw S.gen, trivial },
                { intros, have := linked.step, apply this, split,
                    { intro h, rw <-h at H, exact S.irr H },
                    { convert H, group } },
                { refl },
                { intros u v h1 h2, refine linked.trans h1 _, convert shift _ u h2, group },
                { intros y h, apply inv, exact h },
            }

        theorem connected : connected (Cay S)
            | x y := by { transitivity (1:G), symmetry, apply linked_mp, apply linked_mp }

        instance : connected_graph (Cay S) := ⟨connected S⟩

        noncomputable def word_dist : G -> G -> ℕ := (Cay S).dist

        lemma covariant : (Cay S).dist (a*x) (a*y) = (Cay S).dist x y
            := by { unfold simple_graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
                set dists := dists (Cay S),
                have h2 : ∀ x y a ℓ, ℓ ∈ dists x y -> ℓ ∈ dists (a*x) (a*y)
                    := by { intros x y a ℓ h, cases h with p, use shift_path S a p, simpa [shift_path] },
                exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                    h2 x y a ℓ⟩ }
    end cayley

    namespace cayley
        variables {G : Type} [group G] (S1 S2 : genset G) {x y : G}
        open classical finset

        noncomputable def distorsion (S1 S2 : genset G) := some (max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

        lemma distorsion_spec : distorsion S1 S2 ∈ (image ((Cay S2).dist 1) S1.els).max
            := some_spec (max_of_nonempty (S1.nem.image ((Cay S2).dist 1)))

        lemma distorsion_le {h : (Cay S1).adj x y} : (Cay S2).dist x y ≤ distorsion S1 S2
            := by { refine finset.le_max_of_mem _ (distorsion_spec S1 S2),
                rw [finset.mem_image], refine ⟨x⁻¹ * y, h.2, _⟩, convert covariant _ x⁻¹, group }

        lemma lipschitz : (Cay S2).dist x y <= (distorsion S1 S2) * (Cay S1).dist x y
            := by { obtain ⟨p,hp⟩ := simple_graph.shortest_path (Cay S1) x y, rw <-hp, clear hp,
                induction p with u u v w h p ih; simp,
                transitivity (Cay S2).dist u v + (Cay S2).dist v w, apply simple_graph.dist_triangle,
                rw [mul_add,mul_one,add_comm], apply add_le_add ih, apply distorsion_le, exact h }
    end cayley
end simple_graph

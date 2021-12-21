import tactic data.finset.lattice data.set.basic
import graph_theory.path graph_theory.metric topology.metric_space.lipschitz

namespace simple_graph
    namespace cayley
        structure genset (G : Type) [group G] :=
            (els : finset G)
            (sym : ∀ {s : G}, s ∈ els -> s⁻¹ ∈ els)
            (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
            (nem : els.nonempty)
            (irr : (1:G) ∉ els)

        variables {G : Type} [group G] (S : genset G) (a : G) {x y z : G}

        instance : has_coe (genset G) (finset G) := ⟨λ S, S.els⟩
        instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩

        def adj (x y : G) := x ≠ y ∧ x⁻¹ * y ∈ S

        @[simp] lemma cancel {x y a : G} : (a * x)⁻¹ * (a * y) = x⁻¹ * y
            := by { simp [mul_assoc] }

        lemma inv_prod {x y : G} : (x⁻¹ * y)⁻¹ = y⁻¹ * x
            := by { simp }

        lemma shift_adj {a x y : G} : adj S x y -> adj S (a*x) (a*y)
        := begin
            rintro ⟨h1,h2⟩, split,
            { exact (mul_ne_mul_right a).mpr h1 },
            { rw cancel, assumption }
        end

        @[symm] lemma adj_symm {x y} : adj S x y -> adj S y x
        := begin
            rintro ⟨h1,h2⟩, refine ⟨h1.symm,_⟩,
            rw <-inv_prod, exact S.sym h2
        end

        def Cay (S : genset G) : simple_graph G := ⟨
            adj S,
            by { apply adj_symm },
            by { intro x, unfold adj, tauto }
        ⟩

        def shift_path (p : path (Cay S) x y) : path (Cay S) (a*x : G) (a*y : G)
            := path.rec (λ x', path.point (a * x'))
                        (λ _ _ _ h' _, path.step (shift_adj S h')) p

        @[simp] lemma shift_path_step (h : (Cay S).adj x y) (p : path (Cay S) y z)
        : shift_path S a (path.step h p) = path.step (shift_adj S h) (shift_path S a p)
            := rfl

        @[simp] lemma size_shift_path (p : path (Cay S) x y) : (shift_path S a p).size = p.size
            := by { induction p, refl, simp [*] }

        lemma shift (h : linked (Cay S) x y) : linked (Cay S) (a*x : G) (a*y : G)
            := by { cases (path.iff_path.mp h), refine path.iff_path.mpr _, use shift_path S _ val }

        lemma inv : linked (Cay S) (1:G) x -> linked (Cay S) (1:G) (x⁻¹:G)
            := by { intro h, symmetry, convert shift S x⁻¹ h; simp }

        lemma linked_mp : linked (Cay S) (1:G) x
        := begin
            have h : x ∈ subgroup.closure (coe S.els) := by { rw S.gen, trivial },
            apply subgroup.closure_induction,
            { exact h, },
            { intros, apply linked.edge,
                split, { intro h, rw <-h at H, exact S.irr H },
                change 1⁻¹ * x_1 ∈ S, rwa [one_inv,one_mul] },
            { refl },
            { intros u v h1 h2, refine linked.trans h1 _, convert shift _ u h2, rw mul_one, },
            { intros, apply inv, assumption },
        end

        theorem connected : connected (Cay S)
            := by { suffices : ∀ x, linked (Cay S) (1:G) x,
                    { intros x y, transitivity (1:G), symmetry, apply this, apply this },
                intro, apply linked_mp }

        instance : connected_graph (Cay S) := ⟨connected S⟩

        noncomputable def word_dist : G -> G -> ℕ := simple_graph.dist (Cay S)

        lemma covariant : word_dist S (a*x) (a*y) = word_dist S x y
            := by { unfold word_dist simple_graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
                let dists : G -> G -> set ℕ := dists (Cay S),
                have h2 : ∀ x y a ℓ, dists x y ℓ -> dists (a*x) (a*y) ℓ
                    := by { intros x y a ℓ h, cases h with p, use shift_path S a p, simpa },
                exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                    h2 x y a ℓ⟩ }
    end cayley

    namespace cayley
        variables {G : Type} [group G] (S1 S2 : genset G)
        open finset

        lemma lipschitz : ∃ K : ℕ, ∀ x y : G, word_dist S2 x y <= K * word_dist S1 x y
            := begin
                let Δ := finset.image (word_dist S2 1) S1,
                have : Δ.nonempty := finset.nonempty.image S1.nem (word_dist S2 1),
                obtain K := finset.max_of_nonempty this,
                cases K, use K_w,
                intros x y, obtain p := simple_graph.shortest_path (Cay S1) x y, cases p with p hp,
                unfold word_dist, rw <-hp, clear hp, induction p with x' x' y' z' h' p' ih, simp,
                transitivity (Cay S2).dist x' y' + (Cay S2).dist y' z', apply simple_graph.dist_triangle,
                simp, rw [mul_add,add_comm,mul_one], apply add_le_add ih,
                have : (Cay S2).dist x' y' ∈ Δ, by {
                    simp, use (x')⁻¹ * y', split, exact h'.2,
                    convert covariant S2 x'⁻¹, rw inv_mul_self
                },
                exact finset.le_max_of_mem this K_h
            end
    end cayley
end simple_graph

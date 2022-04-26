import probability.indep
open measure_theory probability_theory filter
open_locale big_operators measure_theory probability_theory topological_space

variables {α β γ : Type*} {mα : measurable_space α} {μ : measure α} [is_finite_measure μ]

namespace probability_theory

noncomputable def cov (X Y : Lp ℝ 2 μ) : ℝ := integral μ (X * Y) - integral μ X * integral μ Y

lemma indep_fun.cov_eq_zero {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  cov X Y = 0 :=
sub_eq_zero_of_eq h.integral_mul_of_Lp

noncomputable def var (X : Lp ℝ 2 μ) : ℝ := integral μ (X^2) - (integral μ X)^2

lemma indep_fun.var_add {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  var (X + Y) = var X + var Y :=
begin
  have hX : integrable X μ := Lp.integrable X,
  have hY : integrable Y μ := Lp.integrable Y,
  have h1 : integrable (X * X) μ := L2.integrable_mul X X,
  have h2 : integrable (X * Y) μ := L2.integrable_mul X Y,
  have h3 : integrable (Y * Y) μ := L2.integrable_mul Y Y,
  have h4 : ⇑(X + Y) =ᵐ[μ] X + Y := Lp.coe_fn_add X Y,
  have h5 : ⇑(X + Y) * ⇑(X + Y) =ᵐ[μ] (X + Y) * (X + Y) := h4.mul h4,

  simp_rw [var, pow_two, integral_congr_ae h4, integral_congr_ae h5, add_mul, mul_add,
    mul_comm (Y : α → ℝ) X, integral_add' (h1.add h2) (h2.add h3), integral_add' h1 h2,
    integral_add' h2 h3, integral_add' hX hY, h.integral_mul_of_integrable hX hY],
  ring
end

noncomputable def partial_avg (X : ℕ → α → ℝ) (a : α) (n : ℕ) :=
(∑ i in finset.range n, X i a) / n

theorem lln_of_nonneg
  ⦃X : ℕ → α → ℝ⦄
  (h_int : ∀ i, integrable (X i) μ)
  (h_dist : ∀ i, μ.map (X i) = μ.map (X 0))
  (h_indep : pairwise (λ i j, indep_fun (X i) (X j) μ))
  (h_pos : ∀ i, 0 ≤ᵐ[μ] X i)
  :
  ∀ᵐ a ∂μ, tendsto (partial_avg X a) at_top (𝓝 (integral μ (X 0))) :=
sorry

lemma map_map' [measurable_space β] [measurable_space γ] {g : β → γ} {f : α → β}
  (hg : measurable g) (hf : ae_measurable f μ) :
  (μ.map f).map g = μ.map (g ∘ f) :=
measure.ext $ λ s hs, by simp [hf, hg, hs, hg hs, hg.comp_ae_measurable hf, ← set.preimage_comp]

lemma bla2 {mβ : measurable_space β} {mγ : measurable_space γ}
  {X Y : α → β} (mX : ae_measurable X μ) (mY : ae_measurable Y μ) (h : μ.map X = μ.map Y)
  {φ : β → γ} (mφ : measurable φ) :
  μ.map (φ ∘ X) = μ.map (φ ∘ Y) :=
by rw [← map_map' mφ mX, ← map_map' mφ mY, h]

theorem lln
  (X : ℕ → α → ℝ)
  (h_int : ∀ i, integrable (X i) μ)
  (h_dist : ∀ i, μ.map (X i) = μ.map (X 0))
  (h_indep : pairwise (λ i j, indep_fun (X i) (X j) μ)) :
  ∀ᵐ a ∂μ, tendsto (partial_avg X a) at_top (𝓝 (integral μ (X 0))) :=
begin
  have h1 : ∀ i a, X⁺ i a - X⁻ i a = X i a := λ _ _, lattice_ordered_comm_group.pos_sub_neg _,
  have h2 : measurable (λ z : ℝ, z⁺) := measurable_id.sup_const 0,
  have h3 : measurable (λ z : ℝ, z⁻) := measurable_id.neg.sup_const 0,

  have Hp : ∀ᵐ a ∂μ, tendsto (partial_avg (X⁺) a) at_top (𝓝 (integral μ (X⁺ 0))),
    from lln_of_nonneg (λ i, (h_int i).max_zero)
      (λ i, bla2 (h_int i).1.ae_measurable (h_int 0).1.ae_measurable (h_dist i) h2)
      (h_indep.mono (λ i j hij, hij.comp h2 h2)) (λ i, ae_of_all _ (λ a, le_sup_right)),

  have Hn : ∀ᵐ a ∂μ, tendsto (partial_avg (X⁻) a) at_top (𝓝 (integral μ (X⁻ 0))),
    from lln_of_nonneg (λ i, (h_int i).neg.max_zero)
      (λ i, bla2 (h_int i).1.ae_measurable (h_int 0).1.ae_measurable (h_dist i) h3)
      (h_indep.mono (λ i j hij, hij.comp h3 h3)) (λ i, ae_of_all _ (λ a, le_sup_right)),

  refine (Hp.and Hn).mono (λ a c, _),
  convert c.1.sub c.2,
  { exact funext (λ x, by simp_rw [partial_avg, ← sub_div, ← finset.sum_sub_distrib, h1]) },
  { exact (congr_arg (integral μ) (funext (λ a, (h1 0 a).symm))).trans
    (integral_sub (h_int 0).max_zero (h_int 0).neg.max_zero) }
end

end probability_theory

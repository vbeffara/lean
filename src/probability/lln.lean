import probability.indep
open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory

variables {α : Type*} {mα : measurable_space α} {μ : measure α} [is_finite_measure μ]

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

noncomputable def partial_avg (X : ℕ → α → ℝ) (n : ℕ) : α → ℝ :=
(∑ i in finset.range n, X i) / n

noncomputable def partial_avg' (X : ℕ → α → ℝ) (a : α) (n : ℕ) : ℝ :=
(∑ i : fin n, X i a) / n

lemma fin.sum.add (n : ℕ) (f g : ℕ → ℝ) :
  ∑ i : fin n, (f i + g i) = ∑ i : fin n, f i + ∑ i : fin n, g i :=
begin
  induction n,
  { simp },
  { simp [fin.sum_univ_cast_succ, n_ih], ring }
end

lemma fin.sum.sub (n : ℕ) (f g : ℕ → ℝ) :
  ∑ i : fin n, (f i - g i) = ∑ i : fin n, f i - ∑ i : fin n, g i :=
begin
  induction n,
  { simp },
  { simp [fin.sum_univ_cast_succ, n_ih], ring }
end

lemma integral_pos_add_neg {ν : measure ℝ} (h_int : integrable id ν) :
  let pos : ℝ → ℝ := λ (x : ℝ), max x 0,
      neg : ℝ → ℝ := λ (x : ℝ), max (-x) 0
  in integral ν id = integral (measure.map pos ν) id - integral (measure.map neg ν) id :=
begin
  intros pos neg,
  rw [integral_map, integral_map, ← integral_sub],
  { simpa only [id.def, max_zero_sub_max_neg_zero_eq_self] },
  { exact h_int.max_zero },
  { exact h_int.neg.max_zero },
  { exact (measurable_neg.max measurable_const).ae_measurable },
  { exact measurable_id.ae_strongly_measurable },
  { exact (measurable_id.max measurable_const).ae_measurable },
  { exact measurable_id.ae_strongly_measurable }
end

theorem lln_of_nonneg
  (ν : measure ℝ)
  (X : ℕ → α → ℝ)
  (h_int : integrable id ν)
  (h_dist : ∀ i, measure.map (X i) μ = ν)
  (h_indep : pairwise (λ i j, indep_fun (X i) (X j) μ))
  (h_pos : ∀ᵐ (x : ℝ) ∂ν, 0 ≤ x) :
  ∀ᵐ a ∂μ, filter.tendsto (partial_avg' X a) ⊤ (nhds (integral ν id)) :=
sorry

theorem lln
  (ν : measure ℝ)
  (X : ℕ → α → ℝ)
  (h_int : integrable id ν)
  (h_meas : ∀ i, measurable (X i))
  (h_dist : ∀ i, μ.map (X i) = ν)
  (h_indep : pairwise (λ i j, indep_fun (X i) (X j) μ)) :
  ∀ᵐ a ∂μ, filter.tendsto (partial_avg' X a) ⊤ (nhds (integral ν id)) :=
begin
  let pos : ℝ → ℝ := λ x, max x 0,
  let neg : ℝ → ℝ := λ x, max (-x) 0,
  let Xp : ℕ → α → ℝ := λ n a, pos (X n a),
  let Xm : ℕ → α → ℝ := λ n a, neg (X n a),

  have h1 : integrable id (measure.map pos ν),
    from (integrable_map_measure measurable_id.ae_strongly_measurable
      (measurable_id.max measurable_const).ae_measurable).mpr h_int.max_zero,

  have h2 : ∀ (i : ℕ), measure.map (Xp i) μ = measure.map pos ν := by {
    intro i,
    rw [← h_dist i],
    exact (measure.map_map (measurable_id.max measurable_const) (h_meas i)).symm
  },

  have h3 : pairwise (λ (i j : ℕ), indep_fun (Xp i) (Xp j) μ) := sorry,
  have h4 : ∀ᵐ (x : ℝ) ∂measure.map pos ν, 0 ≤ x := sorry,

  have Hp := lln_of_nonneg (ν.map pos) Xp h1 h2 h3 h4,

  have h'1 : integrable id (measure.map neg ν),
    from (integrable_map_measure measurable_id.ae_strongly_measurable
      (measurable_neg.max measurable_const).ae_measurable).mpr h_int.neg.max_zero,

  have h'2 : ∀ (i : ℕ), measure.map (Xm i) μ = measure.map neg ν := by {
    intro i,
    rw [← h_dist i],
    exact (measure.map_map (measurable_neg.max measurable_const) (h_meas i)).symm
  },

  have h'3 : pairwise (λ (i j : ℕ), indep_fun (Xm i) (Xm j) μ) := sorry,
  have h'4 : ∀ᵐ (x : ℝ) ∂measure.map neg ν, 0 ≤ x := sorry,

  have Hn := lln_of_nonneg (ν.map neg) Xm h'1 h'2 h'3 h'4,

  apply (Hp.and Hn).mono,
  rintro a ⟨c1, c2⟩,
  convert c1.sub c2,
  { funext n,
    simp [partial_avg'],
    rw [← sub_div],
    apply congr_arg (λ (z : ℝ), z / n),
    rw [← @fin.sum.sub n (λ n, Xp n a) (λ n, Xm n a)],
    congr,
    simp },
  { exact integral_pos_add_neg h_int }
end

end probability_theory

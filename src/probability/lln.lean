import probability.indep
open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory

variables {α : Type*} {mα : measurable_space α} {μ : measure α} [is_finite_measure μ]

namespace probability_theory

noncomputable def cov (X Y : Lp ℝ 2 μ) : ℝ := integral μ (X * Y) - integral μ X * integral μ Y

lemma indep_fun.cov_eq_zero {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  cov X Y = 0 :=
sub_eq_zero_of_eq (indep_fun.integral_mul_of_Lp (le_of_lt ennreal.one_lt_two) h)

noncomputable def var (X : Lp ℝ 2 μ) : ℝ := integral μ (X^2) - (integral μ X)^2

lemma var.add {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  var (X + Y) = var X + var Y :=
begin
  have h' : indep_fun Y X μ := h.symm,
  have hX : integrable X μ := Lp.integrable (le_of_lt ennreal.one_lt_two) X,
  have hY : integrable Y μ := Lp.integrable (le_of_lt ennreal.one_lt_two) Y,
  have h1 : integrable (X * X) μ := L2.integrable_mul X X,
  have h2 : integrable (X * Y) μ := L2.integrable_mul X Y,
  have h3 : integrable (Y * X) μ := L2.integrable_mul Y X,
  have h4 : integrable (Y * Y) μ := L2.integrable_mul Y Y,
  have h5 := Lp.coe_fn_add X Y,
  have h6 := h5.mul h5,
  simp_rw [← pi.mul_apply] at h6,

  simp_rw [var, pow_two, integral_congr_ae h5, integral_congr_ae h6, add_mul, mul_add],
  rw [integral_add' (h1.add h2) (h3.add h4), integral_add' h1 h2, integral_add' h3 h4,
    integral_add' hX hY, h.integral_mul_of_integrable hX hY, h'.integral_mul_of_integrable hY hX],
  ring
end

noncomputable def partial_avg (X : ℕ → α → ℝ) (n : ℕ) : α → ℝ :=
(∑ i in finset.range n, X i) / n

end probability_theory

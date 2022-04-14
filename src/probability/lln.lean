import probability.indep
open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory

variables {α : Type*} {mα : measurable_space α} {μ : measure α}
variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

noncomputable def cov (X Y : Lp ℝ 1 μ) : ℝ := integral μ (X * Y) - integral μ X * integral μ Y

lemma cov_eq_zero_of_indep {X Y : Lp ℝ 1 μ} (h : indep_fun X Y μ) :
  cov X Y = 0 :=
sub_eq_zero_of_eq (h.integral_mul_of_integrable (L1.integrable_coe_fn X) (L1.integrable_coe_fn Y))

noncomputable def var (X : Lp ℝ 2 μ) : ℝ := integral μ (X^2) - (integral μ X)^2

lemma blah [is_finite_measure μ] (f : Lp ℝ 2 μ) : integrable f μ :=
begin
  have : (1 : ennreal) ≤ 2 := by { norm_cast, exact one_le_two },
  convert L1.integrable_coe_fn (⟨f, Lp.antitone this f.prop⟩ : Lp ℝ 1 μ)
end

lemma var.add [is_finite_measure μ] {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  var (X + Y) = var X + var Y :=
begin
  have h1 : integrable X μ := blah X,
  have h2 : integrable Y μ := blah Y,
  have h4 := indep_fun.integral_mul_of_integrable h h1 h2,
  have h5 := Lp.coe_fn_add X Y,
  have h6 := h5.mul h5, simp_rw [← pi.mul_apply] at h6,
  have h7 : indep_fun Y X μ := h.symm,
  have h8 := h7.integrable_mul h2 h1,
  have ha := @L2.integrable_inner α ℝ ℝ _ mα μ _ X X,
  have hb := @L2.integrable_inner α ℝ ℝ _ mα μ _ X Y,
  have hc := @L2.integrable_inner α ℝ ℝ _ mα μ _ Y X,
  have hd := @L2.integrable_inner α ℝ ℝ _ mα μ _ Y Y,

  simp_rw [var, pow_two, integral_congr_ae h5, integral_congr_ae h6, add_mul, mul_add],
  repeat { rw [integral_add'] },
  assumption',
  { rw [h.integral_mul_of_integrable h1 h2, h7.integral_mul_of_integrable h2 h1],
    ring },
  { exact ha.add hb },
  { exact hc.add hd },
end

noncomputable def partial_avg (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
(∑ i in finset.range n, X i) / n

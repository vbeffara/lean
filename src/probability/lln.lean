import probability.indep
open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory

variables {α : Type*} {mα : measurable_space α} {μ : measure α}
variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

noncomputable def cov (X Y : Lp ℝ 1 μ) : ℝ := integral μ (X * Y) - integral μ X * integral μ Y

lemma indep_fun.cov_eq_zero {X Y : Lp ℝ 1 μ} (h : indep_fun X Y μ) :
  cov X Y = 0 :=
sub_eq_zero_of_eq (h.integral_mul_of_integrable (L1.integrable_coe_fn X) (L1.integrable_coe_fn Y))

noncomputable def var (X : Lp ℝ 2 μ) : ℝ := integral μ (X^2) - (integral μ X)^2

lemma Lp.integrable [is_finite_measure μ] {p : ennreal} (hp : 1 ≤ p) (f : Lp ℝ p μ) :
  integrable f μ :=
by convert L1.integrable_coe_fn (⟨f, Lp.antitone hp f.prop⟩ : Lp ℝ 1 μ)

lemma var.add [is_finite_measure μ] {X Y : Lp ℝ 2 μ} (h : indep_fun X Y μ) :
  var (X + Y) = var X + var Y :=
begin
  have l2 : (1 : ennreal) ≤ 2 := by { norm_cast, exact one_le_two },
  have hh : ∀ f g : Lp ℝ 2 μ, integrable (f * g) μ := @L2.integrable_inner α ℝ ℝ _ mα μ _,
  have h' : indep_fun Y X μ := h.symm,
  have hX : integrable X μ := Lp.integrable l2 X,
  have hY : integrable Y μ := Lp.integrable l2 Y,
  have h1 : integrable (X * X) μ := hh X X,
  have h2 : integrable (X * Y) μ := hh X Y,
  have h3 : integrable (Y * X) μ := hh Y X,
  have h4 : integrable (Y * Y) μ := hh Y Y,
  have h5 := Lp.coe_fn_add X Y,
  have h6 := h5.mul h5,
  simp_rw [← pi.mul_apply] at h6,

  simp_rw [var, pow_two, integral_congr_ae h5, integral_congr_ae h6, add_mul, mul_add],
  rw [integral_add' (h1.add h2) (h3.add h4), integral_add' h1 h2, integral_add' h3 h4,
    integral_add' hX hY, h.integral_mul_of_integrable hX hY, h'.integral_mul_of_integrable hY hX],
  ring
end

noncomputable def partial_avg (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
(∑ i in finset.range n, X i) / n

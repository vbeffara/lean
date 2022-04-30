import measure_theory.integral.bochner
import measure_theory.measure.measure_space

open measure_theory measure_theory.measure
open_locale big_operators measure_theory topological_space

variables {α : Type*} [measurable_space α]

instance sum_is_finite_measure {ι : Type*} [fintype ι] {μ : ι → measure α}
  [∀ i, is_finite_measure (μ i)] : is_finite_measure (sum μ) :=
begin
  refine ⟨_⟩,
  rw [measure.sum_apply _ measurable_set.univ, @tsum_eq_sum _ _ _ _ _ _ finset.univ],
  { simp only [ennreal.sum_lt_top, measure_ne_top, ne.def, not_false_iff, implies_true_iff] },
  { simp only [finset.mem_univ, not_true, forall_false_left, implies_true_iff] },
  { apply_instance },
  { apply_instance }
end

instance [fintype α] : is_finite_measure (count : measure α) :=
by apply sum_is_finite_measure

lemma linf [fintype α] [nonempty α] (f : α → ℝ) :
  mem_ℒp f ⊤ (@count α ⊤) :=
begin
  refine ⟨measurable_from_top.ae_strongly_measurable, _⟩,
  simp [snorm_ess_sup, ess_sup, filter.limsup_eq],
  apply Inf_lt_iff.mpr,
  obtain ⟨x, hx⟩ := fintype.exists_max (λ x, ∥f x∥₊),
  refine ⟨∥f x∥₊, _, by simp only [ennreal.coe_lt_top]⟩,
  simp,
  exact @ae_of_all _ ⊤ _ _ hx
end

lemma lp [fintype α] [nonempty α] (p : ennreal) (f : α → ℝ) :
  mem_ℒp f p (@count α ⊤) :=
(linf f).mem_ℒp_of_exponent_le le_top

lemma integral_count {α : Type*} [fintype α] {f : α → ℝ} :
  ∫ a, f a ∂(@count α ⊤) = ∑ a, f a :=
begin
  simp [count],
  rw integral_finset_sum_measure,
  { congr, funext i, apply integral_dirac', exact measurable_from_top.strongly_measurable },
  { refine λ i hi, ⟨measurable_from_top.ae_strongly_measurable, _⟩,
    rw [has_finite_integral, lintegral_dirac' _ measurable_from_top],
    simp only [ennreal.coe_lt_top] }
end

lemma cauchy_schwarz {α : Type*} [fintype α] (f g : α → ℝ) :
  (∑ x, f x * g x) ^ 2 ≤ (∑ x, f x ^ 2) * (∑ x, g x ^ 2) :=
begin
  simp_rw [← integral_count], sorry
end

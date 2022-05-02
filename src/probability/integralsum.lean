import measure_theory.integral.bochner
import measure_theory.function.l2_space
import measure_theory.measure.measure_space

open measure_theory measure_theory.measure
open_locale big_operators measure_theory topological_space

variables {α : Type*} [fintype α]

instance sum_is_finite_measure {α ι : Type*} [measurable_space α] [fintype ι] {μ : ι → measure α}
  [∀ i, is_finite_measure (μ i)] : is_finite_measure (sum μ) :=
begin
  refine ⟨_⟩,
  rw [measure.sum_apply _ measurable_set.univ, @tsum_eq_sum _ _ _ _ _ _ finset.univ],
  { simp only [ennreal.sum_lt_top, measure_ne_top, ne.def, not_false_iff, implies_true_iff] },
  { simp only [finset.mem_univ, not_true, forall_false_left, implies_true_iff] },
  { apply_instance },
  { apply_instance }
end

instance [measurable_space α] : is_finite_measure (count : measure α) :=
by apply sum_is_finite_measure

lemma lp (p : ennreal) (f : α → ℝ) :
  mem_ℒp f p (@count α ⊤) :=
begin
  refine mem_ℒp.mem_ℒp_of_exponent_le _ le_top,
  suffices : ∃ b : nnreal, ∀ x : α, ∥f x∥₊ ≤ b,
  { obtain ⟨b, hb⟩ := this,
    exact mem_ℒp_top_of_bound measurable_from_top.ae_strongly_measurable _ (@ae_of_all _ ⊤ _ _ hb) },
  by_cases nonempty α,
  { obtain ⟨x, hx⟩ := by exactI fintype.exists_max (λ x, ∥f x∥₊),
    exact ⟨_, hx⟩ },
  { exact ⟨0, λ x, false.rec _ (h ⟨x⟩)⟩ }
end

lemma integral_count {f : α → ℝ} :
  ∫ a, f a ∂(@count α ⊤) = ∑ a, f a :=
begin
  simp [count],
  rw integral_finset_sum_measure,
  { congr, funext i, apply integral_dirac', exact measurable_from_top.strongly_measurable },
  { refine λ i hi, ⟨measurable_from_top.ae_strongly_measurable, _⟩,
    rw [has_finite_integral, lintegral_dirac' _ measurable_from_top],
    simp only [ennreal.coe_lt_top] }
end

lemma cauchy_schwarz (f g : α → ℝ) :
  (∑ x, f x * g x) ≤ (∑ x, f x ^ 2) ^ (2⁻¹ : ℝ) * (∑ x, g x ^ 2) ^ (2⁻¹ : ℝ) :=
begin
  simp_rw [← integral_count, pow_two],
  rw ← integral_congr_ae ((lp 2 f).coe_fn_to_Lp.mul (lp 2 g).coe_fn_to_Lp),
  rw ← integral_congr_ae ((lp 2 f).coe_fn_to_Lp.mul (lp 2 f).coe_fn_to_Lp),
  rw ← integral_congr_ae ((lp 2 g).coe_fn_to_Lp.mul (lp 2 g).coe_fn_to_Lp),
  simp,
  let ff := (lp 2 f).to_Lp f,
  let gg := (lp 2 g).to_Lp g,
  have := @real_inner_le_norm _ _ ff gg,
  convert ← this using 1,
  simp [snorm, snorm'],
  congr,
  { have := lintegral_coe_eq_integral (λ x, ∥f x∥₊^2) _,
    { simp at this,
      rw [this, ennreal.of_real_rpow_of_nonneg, ennreal.to_real_of_real],
      { simp_rw pow_two,
        congr' 1,
        convert integral_congr_ae ((lp 2 f).coe_fn_to_Lp.mul (lp 2 f).coe_fn_to_Lp).symm,
        funext,
        exact abs_mul_abs_self _},
      { apply real.rpow_nonneg_of_nonneg,
        apply integral_nonneg,
        rw pi.le_def,
        intro i,
        apply pow_two_nonneg },
      { apply integral_nonneg,
        rw pi.le_def,
        intro i,
        apply pow_two_nonneg },
      { norm_num } },
    { sorry }
  },
  sorry



  -- have := mul_le_mul this this (is_R_or_C.abs_nonneg _) _,
  -- convert ← this using 1,
  -- { simp [L2.inner_def, ← pow_two],
  --   congr' 1,
  --   apply integral_congr_ae,
  --   exact (lp 2 f).coe_fn_to_Lp.mul (lp 2 g).coe_fn_to_Lp },
  -- { simp [snorm, snorm'],

  --   sorry },
  -- { exact mul_nonneg (norm_nonneg _) (norm_nonneg _) }
end

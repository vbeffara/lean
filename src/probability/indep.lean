import probability.independence
import probability.integration
import probability.notation

open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory
noncomputable theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

namespace probability_theory

lemma indep_fun_comp_of_indep_fun {α α' β β' : Type*}
  [measurable_space α] [measurable_space α'] [measurable_space β] [measurable_space β']
  {f : Ω → α} {g : Ω → α'} (hfg : indep_fun f g)
  {φ : α → β} {ψ : α' → β'} {hφ : measurable φ} {hψ : measurable ψ} :
indep_fun (φ ∘ f) (ψ ∘ g) :=
begin
  rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩, apply hfg,
  exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩,
  exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
end

def pos_part (x : ℝ) := max x 0
def neg_part (x : ℝ) := max (-x) 0
lemma eq_pos_sub_neg (X : Ω → ℝ) : X = pos_part ∘ X - neg_part ∘ X :=
begin
  symmetry, ext ω, simp, apply max_zero_sub_max_neg_zero_eq_self
end

lemma integrable_mul_of_integrable_of_indep_fun {X Y : Ω → ℝ} {h : indep_fun X Y}
  {hXm : measurable X} {hXi : integrable X} {hYm : measurable Y} {hYi : integrable Y} :
integrable (X * Y) :=
begin
  have hXpm : measurable (λ a, ∥X a∥₊ : Ω → ennreal) := hXm.nnnorm.coe_nnreal_ennreal,
  have hYpm : measurable (λ a, ∥Y a∥₊ : Ω → ennreal) := hYm.nnnorm.coe_nnreal_ennreal,

  refine ⟨hXi.1.mul hYi.1, _⟩,
  simp_rw [has_finite_integral, pi.mul_apply, nnnorm_mul, ennreal.coe_mul],
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun hXpm hYpm _,
  simp only [pi.mul_apply] at this, rw this, clear this,
  exact ennreal.mul_lt_top_iff.mpr (or.inl ⟨hXi.2, hYi.2⟩),
  apply indep_fun_comp_of_indep_fun; try { exact measurable_coe_nnreal_ennreal },
  apply indep_fun_comp_of_indep_fun h; exact measurable_nnnorm
end

-- TODO: should work on `ae_measurable`
lemma integral_indep_of_pos {X Y : Ω → ℝ} {hXYind : indep_fun X Y}
  {hXpos : 0 ≤ X} {hXmes : measurable X} {hYpos : 0 ≤ Y} {hYmes : measurable Y}:
  𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  rw [@integral_eq_lintegral_of_nonneg_ae _ _ _ (X * Y)
      (filter.eventually_of_forall (λ ω, mul_nonneg (hXpos ω) (hYpos ω)))
      (hXmes.mul hYmes).ae_measurable,
    integral_eq_lintegral_of_nonneg_ae (filter.eventually_of_forall hXpos) hXmes.ae_measurable,
    integral_eq_lintegral_of_nonneg_ae (filter.eventually_of_forall hYpos) hYmes.ae_measurable],
  simp_rw [←ennreal.to_real_mul, pi.mul_apply, ennreal.of_real_mul (hXpos _)],
  congr,
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun
    hXmes.ennreal_of_real hYmes.ennreal_of_real (indep_fun_comp_of_indep_fun hXYind);
  exact ennreal.measurable_of_real
end

lemma integral_indep
  {X : Ω → ℝ} {hXm : measurable X} {hX : integrable X}
  {Y : Ω → ℝ} {hYm : measurable Y} {hY : integrable Y}
  {hXY : integrable (X * Y)} {h : indep_fun X Y} :
  𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  have hXpm := eq_pos_sub_neg X, have hYpm := eq_pos_sub_neg Y,
  set Xp := pos_part ∘ X, set Xm := neg_part ∘ X, set Yp := pos_part ∘ Y, set Ym := neg_part ∘ Y,

  have hp1 : 0 ≤ Xm := by { intro ω, simp [Xm,neg_part] },
  have hp2 : 0 ≤ Xp := by { intro ω, simp [Xp,pos_part] },
  have hp3 : 0 ≤ Ym := by { intro ω, simp [Ym,neg_part] },
  have hp4 : 0 ≤ Yp := by { intro ω, simp [Yp,pos_part] },

  have hm1 : measurable Xm := hXm.neg.max measurable_const,
  have hm2 : measurable Xp := hXm.max measurable_const,
  have hm3 : measurable Ym := hYm.neg.max measurable_const,
  have hm4 : measurable Yp := hYm.max measurable_const,

  have hv1 : integrable Xm := hX.neg.max_zero,
  have hv1 : integrable Xp := hX.max_zero,
  have hv1 : integrable Ym := hY.neg.max_zero,
  have hv1 : integrable Yp := hY.max_zero,

  have hi1 : indep_fun Xm Ym := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi2 : indep_fun Xp Ym := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi3 : indep_fun Xm Yp := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi4 : indep_fun Xp Yp := by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },

  have hl1 : integrable (Xm * Ym) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },
  have hl2 : integrable (Xp * Ym) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },
  have hl3 : integrable (Xm * Yp) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },
  have hl4 : integrable (Xp * Yp) := by { apply integrable_mul_of_integrable_of_indep_fun; assumption },

  simp_rw [pi.mul_apply, hXpm, hYpm, pi.sub_apply, mul_sub, sub_mul, ← pi.mul_apply],
  rw [integral_sub, integral_sub, integral_sub, integral_sub', integral_sub', sub_mul, mul_sub, mul_sub],
  rw [integral_indep_of_pos, integral_indep_of_pos, integral_indep_of_pos, integral_indep_of_pos],
  ring, all_goals { try { assumption } },
  { apply integrable.sub; assumption },
  { apply integrable.sub; assumption },
end

end probability_theory

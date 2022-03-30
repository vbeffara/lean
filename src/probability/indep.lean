import probability.independence
import probability.integration
import probability.notation

open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory
noncomputable theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

namespace probability_theory

lemma lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator'
  {α : Type*} {Mf : measurable_space α} [M : measurable_space α] (μ : measure α) (hMf : Mf ≤ M)
  (c : ennreal) {T : set α} (h_meas_T : measurable_set T)
  (h_ind : @indep_sets α M Mf.measurable_set' {T} μ)
  {f : α → ennreal} (h_meas_f : ae_measurable' Mf f μ) :
  ∫⁻ a, f a * T.indicator (λ _, c) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, T.indicator (λ _, c) a ∂μ :=
begin
  rcases h_meas_f with ⟨g,g_meas,g_ae⟩,
  rw lintegral_congr_ae g_ae,
  convert @lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
    α Mf M μ hMf c T h_meas_T h_ind g g_meas using 1,
  apply lintegral_congr_ae, apply g_ae.mul, apply ae_of_all, intro, refl
end

lemma preimage_ae_eq_of_ae_eq {α β : Type*} [measurable_space α] [measurable_space β]
  {f g : α → β} {μ : measure α} (hfg : f =ᵐ[μ] g) {B : set β} :
f ⁻¹' B =ᵐ[μ] g ⁻¹' B :=
hfg.fun_comp B

lemma indep_fun_of_indep_fun_of_ae_eq {α β : Type*} [measurable_space α] [measurable_space β]
  {f g f' g' : α → β} {μ : measure α} (hfg : indep_fun f g μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
indep_fun f' g' μ :=
begin
  rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩,
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A,
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B,
  rw [←measure_congr h1, ←measure_congr h2, ←measure_congr (h1.inter h2)],
  apply hfg, exact ⟨_,hA,rfl⟩, exact ⟨_,hB,rfl⟩
end

lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'
  {α : Type*} [measurable_space α] {μ : measure α}
  {f g : α → ennreal} (h_meas_f : ae_measurable f μ) (h_meas_g : ae_measurable g μ)
  (h_indep_fun : indep_fun f g μ) :
  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  rcases h_meas_f with ⟨f',f'_meas,f'_ae⟩,
  rcases h_meas_g with ⟨g',g'_meas,g'_ae⟩,
  have := indep_fun_of_indep_fun_of_ae_eq h_indep_fun f'_ae g'_ae,
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun f'_meas g'_meas this,
  convert this using 1,
  { apply lintegral_congr_ae, exact f'_ae.mul g'_ae },
  { rw [lintegral_congr_ae f'_ae, lintegral_congr_ae g'_ae] }
end

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

lemma integral_indep {X Y : Ω → ℝ} {h : indep_fun X Y}
  {hXm : measurable X} {hX : integrable X} {hYm : measurable Y} {hY : integrable Y} :
𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  set Xp := (λ x : ℝ, max x 0) ∘ X, -- `X⁺` would be better but it makes `simp_rw` fail
  set Xm := (λ x : ℝ, max (-x) 0) ∘ X,
  set Yp := (λ x : ℝ, max x 0) ∘ Y,
  set Ym := (λ x : ℝ, max (-x) 0) ∘ Y,

  have hXpm : X = Xp - Xm := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (X ω)).symm),
  have hYpm : Y = Yp - Ym := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm),

  have hp1 : 0 ≤ Xm := λ ω, le_max_right _ _,
  have hp2 : 0 ≤ Xp := λ ω, le_max_right _ _,
  have hp3 : 0 ≤ Ym := λ ω, le_max_right _ _,
  have hp4 : 0 ≤ Yp := λ ω, le_max_right _ _,

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

  have hl5 : integrable (Xp * Yp - Xm * Yp) := by { apply integrable.sub; assumption },
  have hl5 : integrable (Xp * Ym - Xm * Ym) := by { apply integrable.sub; assumption },

  simp_rw [hXpm, hYpm, mul_sub, sub_mul],
  repeat { rw [integral_sub'] },
  repeat { rw [integral_indep_of_pos] },
  ring,
  assumption'
end

end probability_theory

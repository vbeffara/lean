import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal

variables {α β β' γ γ' : Type*} {mα : measurable_space α} {μ : measure α}

namespace probability_theory

lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' [measurable_space α] {μ : measure α}
  {f g : α → ℝ≥0∞} (h_meas_f : ae_measurable f μ) (h_meas_g : ae_measurable g μ)
  (h_indep_fun : indep_fun f g μ) :
  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  rcases h_meas_f with ⟨f',f'_meas,f'_ae⟩,
  rcases h_meas_g with ⟨g',g'_meas,g'_ae⟩,
  have fg_ae : f * g =ᵐ[μ] f' * g' := f'_ae.mul g'_ae,
  rw [lintegral_congr_ae f'_ae, lintegral_congr_ae g'_ae, lintegral_congr_ae fg_ae],
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun f'_meas g'_meas,
  exact h_indep_fun.ae_eq f'_ae g'_ae
end

lemma indep_fun.integrable_mul [measurable_space α] {μ : measure α}
  {β : Type*} [measurable_space β] [normed_division_ring β] [borel_space β]
  {X Y : α → β} (hXY : indep_fun X Y μ) (hX : integrable X μ) (hY : integrable Y μ) :
  integrable (X * Y) μ :=
begin
  let nX : α → ennreal := λ a, ∥X a∥₊,
  let nY : α → ennreal := λ a, ∥Y a∥₊,

  have hXY' : indep_fun (λ a, ∥X a∥₊) (λ a, ∥Y a∥₊) μ :=
    hXY.comp measurable_nnnorm measurable_nnnorm,
  have hXY'' : indep_fun nX nY μ :=
    hXY'.comp measurable_coe_nnreal_ennreal measurable_coe_nnreal_ennreal,

  have hnX : ae_measurable nX μ := hX.1.ae_measurable.nnnorm.coe_nnreal_ennreal,
  have hnY : ae_measurable nY μ := hY.1.ae_measurable.nnnorm.coe_nnreal_ennreal,

  have hmul : ∫⁻ a, nX a * nY a ∂μ = ∫⁻ a, nX a ∂μ * ∫⁻ a, nY a ∂μ :=
    by convert lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' hnX hnY hXY'',

  refine ⟨hX.1.mul hY.1, _⟩,
  simp_rw [has_finite_integral, pi.mul_apply, nnnorm_mul, ennreal.coe_mul, hmul],
  exact ennreal.mul_lt_top_iff.mpr (or.inl ⟨hX.2, hY.2⟩)
end

lemma indep_fun.integral_mul_of_nonneg [measurable_space α] {μ : measure α} {X Y : α → ℝ}
  (hXY : indep_fun X Y μ) (hXp : 0 ≤ X) (hYp : 0 ≤ Y)
  (hXm : ae_measurable X μ) (hYm : ae_measurable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  have h1 : ae_measurable (λ a, ennreal.of_real (X a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hXm,
  have h2 : ae_measurable (λ a, ennreal.of_real (Y a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hYm,
  have h3 : ae_measurable (X * Y) μ := hXm.mul hYm,

  have h4 : 0 ≤ᵐ[μ] X := ae_of_all _ hXp,
  have h5 : 0 ≤ᵐ[μ] Y := ae_of_all _ hYp,
  have h6 : 0 ≤ᵐ[μ] (X * Y) := ae_of_all _ (λ ω, mul_nonneg (hXp ω) (hYp ω)),

  have h7 : ae_strongly_measurable X μ := ae_strongly_measurable_iff_ae_measurable.mpr hXm,
  have h8 : ae_strongly_measurable Y μ := ae_strongly_measurable_iff_ae_measurable.mpr hYm,
  have h9 : ae_strongly_measurable (X * Y) μ := ae_strongly_measurable_iff_ae_measurable.mpr h3,

  rw [integral_eq_lintegral_of_nonneg_ae h4 h7],
  rw [integral_eq_lintegral_of_nonneg_ae h5 h8],
  rw [integral_eq_lintegral_of_nonneg_ae h6 h9],
  simp_rw [←ennreal.to_real_mul, pi.mul_apply, ennreal.of_real_mul (hXp _)],
  congr,
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' h1 h2,
  exact hXY.comp ennreal.measurable_of_real ennreal.measurable_of_real
end

theorem indep_fun.integral_mul_of_integrable [measurable_space α] {μ : measure α} {X Y : α → ℝ}
  (hXY : indep_fun X Y μ) (hX : integrable X μ) (hY : integrable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  let pos : ℝ → ℝ := (λ x, max x 0),
  let neg : ℝ → ℝ := (λ x, max (-x) 0),
  have posm : measurable pos := measurable_id'.max measurable_const,
  have negm : measurable neg := measurable_id'.neg.max measurable_const,

  let Xp := pos ∘ X, -- `X⁺` would look better but it makes `simp_rw` below fail
  let Xm := neg ∘ X,
  let Yp := pos ∘ Y,
  let Ym := neg ∘ Y,

  have hXpm : X = Xp - Xm := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (X ω)).symm),
  have hYpm : Y = Yp - Ym := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm),

  have hp1 : 0 ≤ Xm := λ ω, le_max_right _ _,
  have hp2 : 0 ≤ Xp := λ ω, le_max_right _ _,
  have hp3 : 0 ≤ Ym := λ ω, le_max_right _ _,
  have hp4 : 0 ≤ Yp := λ ω, le_max_right _ _,

  have hm1 : ae_measurable Xm μ := hX.1.ae_measurable.neg.max ae_measurable_const,
  have hm2 : ae_measurable Xp μ := hX.1.ae_measurable.max ae_measurable_const,
  have hm3 : ae_measurable Ym μ := hY.1.ae_measurable.neg.max ae_measurable_const,
  have hm4 : ae_measurable Yp μ := hY.1.ae_measurable.max ae_measurable_const,

  have hv1 : integrable Xm μ := hX.neg.max_zero,
  have hv2 : integrable Xp μ := hX.max_zero,
  have hv3 : integrable Ym μ := hY.neg.max_zero,
  have hv4 : integrable Yp μ := hY.max_zero,

  have hi1 : indep_fun Xm Ym μ := hXY.comp negm negm,
  have hi2 : indep_fun Xp Ym μ := hXY.comp posm negm,
  have hi3 : indep_fun Xm Yp μ := hXY.comp negm posm,
  have hi4 : indep_fun Xp Yp μ := hXY.comp posm posm,

  have hl1 : integrable (Xm * Ym) μ := hi1.integrable_mul hv1 hv3,
  have hl2 : integrable (Xp * Ym) μ := hi2.integrable_mul hv2 hv3,
  have hl3 : integrable (Xm * Yp) μ := hi3.integrable_mul hv1 hv4,
  have hl4 : integrable (Xp * Yp) μ := hi4.integrable_mul hv2 hv4,
  have hl5 : integrable (Xp * Yp - Xm * Yp) μ := hl4.sub hl3,
  have hl6 : integrable (Xp * Ym - Xm * Ym) μ := hl2.sub hl1,

  simp_rw [hXpm, hYpm, mul_sub, sub_mul],
  rw [integral_sub' hl5 hl6, integral_sub' hl4 hl3, integral_sub' hl2 hl1],
  rw [integral_sub' hv2 hv1, integral_sub' hv4 hv3],
  rw [hi1.integral_mul_of_nonneg hp1 hp3 hm1 hm3, hi2.integral_mul_of_nonneg hp2 hp3 hm2 hm3],
  rw [hi3.integral_mul_of_nonneg hp1 hp4 hm1 hm4, hi4.integral_mul_of_nonneg hp2 hp4 hm2 hm4],
  ring
end

lemma indicator_preimage (f : α → β) (B : set β) :
  (B.indicator (1 : β → ℝ)) ∘ f = (f ⁻¹' B).indicator 1 :=
begin
  simp only [set.indicator], funext x,
  split_ifs with hx; { rw set.mem_preimage at hx, simp [hx] }
end

theorem indep_fun_iff_integral_mul [is_finite_measure μ] {f : α → β} {g : α → β'}
  {mβ : measurable_space β} {mβ' : measurable_space β'} {hfm : measurable f} {hgm : measurable g} :
  indep_fun f g μ ↔
  ∀ φ : β → ℝ, ∀ ψ : β' → ℝ, measurable φ → integrable (φ ∘ f) μ →
    measurable ψ → integrable (ψ ∘ g) μ →
    integral μ ((φ ∘ f) * (ψ ∘ g)) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) :=
begin
  split,
  { rintro hfg φ ψ hφ hf hψ hg,
    refine indep_fun.integral_mul_of_integrable _ hf hg,
    exact hfg.comp hφ hψ },
  { rintro h _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩,
    let φ : β → ℝ := A.indicator 1,
    let ψ : β' → ℝ := B.indicator 1,

    have hφ : measurable φ := measurable_one.indicator hA,
    have hψ : measurable ψ := measurable_one.indicator hB,

    have hf : integrable (φ ∘ f) μ :=
      by { refine integrable.indicator _ (hfm.comp measurable_id hA),
      simp, apply integrable_const },
    have hg : integrable (ψ ∘ g) μ :=
      by { refine integrable.indicator _ (hgm.comp measurable_id hB),
      simp, apply integrable_const },

    specialize h φ ψ hφ hf hψ hg,
    repeat { rw [← ennreal.to_real_eq_to_real] },
    rw ennreal.to_real_mul,

    have h4 : integral μ ((f ⁻¹' A).indicator 1) = (μ (f ⁻¹' A)).to_real :=
      by { have := integral_indicator_const (1 : ℝ) (hfm hA), simp at this, exact this },
    have h5 : integral μ ((g ⁻¹' B).indicator 1) = (μ (g ⁻¹' B)).to_real :=
      by { have := integral_indicator_const (1 : ℝ) (hgm hB), simp at this, exact this },
    have h6 : integral μ ((f ⁻¹' A ∩ g ⁻¹' B).indicator 1) = (μ (f ⁻¹' A ∩ g ⁻¹' B)).to_real :=
      by { have := integral_indicator_const (1 : ℝ) ((hfm hA).inter (hgm hB)),
        simp at this, exact this },

    rw [←h4, ←h5, ←h6, ←indicator_preimage f A, ←indicator_preimage g B, ←h],
    congr, funext, simp [φ, ψ, set.indicator],
    rw [set.mem_inter_iff, set.mem_preimage, set.mem_preimage],
    classical, convert ite_and (f x ∈ A) (g x ∈ B) (1:ℝ) 0,
    apply measure_ne_top,
    exact ennreal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _) }
end

end probability_theory

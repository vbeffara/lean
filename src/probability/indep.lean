import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory

variables {α : Type*} [measurable_space α] {μ : measure α}
variables {β β' : Type*} [measurable_space β] [measurable_space β']
variables {γ γ' : Type*} [measurable_space γ] [measurable_space γ']

namespace probability_theory

lemma indep_fun_of_indep_fun_of_ae_eq {f g f' g' : α → β} (hfg : indep_fun f g μ)
  (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') : indep_fun f' g' μ :=
begin
  rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩,
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A,
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B,
  rw [←measure_congr h1, ←measure_congr h2, ←measure_congr (h1.inter h2)],
  apply hfg, exact ⟨_,hA,rfl⟩, exact ⟨_,hB,rfl⟩
end

lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' {f g : α → ennreal}
  (h_meas_f : ae_measurable f μ) (h_meas_g : ae_measurable g μ) (h_indep_fun : indep_fun f g μ) :
  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  rcases h_meas_f with ⟨f',f'_meas,f'_ae⟩,
  rcases h_meas_g with ⟨g',g'_meas,g'_ae⟩,
  have fg_ae : f * g =ᵐ[μ] f' * g' := f'_ae.mul g'_ae,
  rw [lintegral_congr_ae f'_ae, lintegral_congr_ae g'_ae, lintegral_congr_ae fg_ae],
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun f'_meas g'_meas,
  exact indep_fun_of_indep_fun_of_ae_eq h_indep_fun f'_ae g'_ae
end

lemma indep_fun_comp_of_indep_fun {f : α → β} {g : α → β'} (hfg : indep_fun f g μ)
  {φ : β → γ} {ψ : β' → γ'} {hφ : measurable φ} {hψ : measurable ψ} :
  indep_fun (φ ∘ f) (ψ ∘ g) μ :=
begin
  rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩, apply hfg,
  exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩,
  exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
end

lemma integrable_mul_of_integrable_of_indep_fun {X Y : α → ℝ} (h : indep_fun X Y μ)
  (hX : integrable X μ) (hY : integrable Y μ) : integrable (X * Y) μ :=
begin
  refine ⟨hX.1.mul hY.1, _⟩,

  have h1 : ae_measurable (λ a, ∥X a∥₊ : α → ennreal) μ :=
    hX.1.ae_measurable.nnnorm.coe_nnreal_ennreal,
  have h2 : ae_measurable (λ a, ∥Y a∥₊ : α → ennreal) μ :=
    hY.1.ae_measurable.nnnorm.coe_nnreal_ennreal,

  simp_rw [has_finite_integral, pi.mul_apply, nnnorm_mul, ennreal.coe_mul],
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' h1 h2 _,
  simp only [pi.mul_apply] at this, rw this, clear this,
  exact ennreal.mul_lt_top_iff.mpr (or.inl ⟨hX.2, hY.2⟩),
  apply indep_fun_comp_of_indep_fun; try { exact measurable_coe_nnreal_ennreal },
  apply indep_fun_comp_of_indep_fun h; exact measurable_nnnorm
end

lemma integral_mul_eq_integral_mul_integral_of_indep_fun_of_indep_fun_of_nonneg {X Y : α → ℝ}
  {hXpos : 0 ≤ X} {hXmes : ae_measurable X μ} {hYpos : 0 ≤ Y} {hYmes : ae_measurable Y μ}
  {hXYind : indep_fun X Y μ} : integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  have h1 : ae_measurable (λ a, ennreal.of_real (X a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hXmes,
  have h2 : ae_measurable (λ a, ennreal.of_real (Y a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hYmes,
  have h3 : ae_measurable (X * Y) μ := hXmes.mul hYmes,

  have h4 : 0 ≤ᵐ[μ] X := ae_of_all _ hXpos,
  have h5 : 0 ≤ᵐ[μ] Y := ae_of_all _ hYpos,
  have h6 : 0 ≤ᵐ[μ] (X * Y) := ae_of_all _ (λ ω, mul_nonneg (hXpos ω) (hYpos ω)),

  have h7 : ae_strongly_measurable X μ := ae_strongly_measurable_iff_ae_measurable.mpr hXmes,
  have h8 : ae_strongly_measurable Y μ := ae_strongly_measurable_iff_ae_measurable.mpr hYmes,
  have h9 : ae_strongly_measurable (X*Y) μ := ae_strongly_measurable_iff_ae_measurable.mpr h3,

  have := ennreal.measurable_of_real,

  repeat { rw integral_eq_lintegral_of_nonneg_ae },
  simp_rw [←ennreal.to_real_mul, pi.mul_apply, ennreal.of_real_mul (hXpos _)],
  congr,
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun', assumption',
  apply indep_fun_comp_of_indep_fun hXYind, assumption',
end

lemma integral_mul_eq_integral_mul_integral_of_indep_fun {X Y : α → ℝ}
  (hX : integrable X μ) (hY : integrable Y μ) (h : indep_fun X Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
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

  have hm1 : ae_measurable Xm μ := hX.1.ae_measurable.neg.max ae_measurable_const,
  have hm2 : ae_measurable Xp μ := hX.1.ae_measurable.max ae_measurable_const,
  have hm3 : ae_measurable Ym μ := hY.1.ae_measurable.neg.max ae_measurable_const,
  have hm4 : ae_measurable Yp μ := hY.1.ae_measurable.max ae_measurable_const,

  have hv1 : integrable Xm μ := hX.neg.max_zero,
  have hv2 : integrable Xp μ := hX.max_zero,
  have hv3 : integrable Ym μ := hY.neg.max_zero,
  have hv4 : integrable Yp μ := hY.max_zero,

  have hi1 : indep_fun Xm Ym μ :=
    by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi2 : indep_fun Xp Ym μ :=
    by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi3 : indep_fun Xm Yp μ :=
    by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },
  have hi4 : indep_fun Xp Yp μ :=
    by { apply indep_fun_comp_of_indep_fun h; apply measurable.max, measurability },

  have hl1 : integrable (Xm * Ym) μ := integrable_mul_of_integrable_of_indep_fun hi1 hv1 hv3,
  have hl2 : integrable (Xp * Ym) μ := integrable_mul_of_integrable_of_indep_fun hi2 hv2 hv3,
  have hl3 : integrable (Xm * Yp) μ := integrable_mul_of_integrable_of_indep_fun hi3 hv1 hv4,
  have hl4 : integrable (Xp * Yp) μ := integrable_mul_of_integrable_of_indep_fun hi4 hv2 hv4,

  have hl5 : integrable (Xp * Yp - Xm * Yp) μ := hl4.sub hl3,
  have hl5 : integrable (Xp * Ym - Xm * Ym) μ := hl2.sub hl1,

  simp_rw [hXpm, hYpm, mul_sub, sub_mul],
  repeat { rw [integral_sub'] },
  repeat { rw [integral_mul_eq_integral_mul_integral_of_indep_fun_of_indep_fun_of_nonneg] },
  ring, assumption'
end

lemma integral_mul_eq_integral_mul_integral_of_indep_fun' {Ω : Type*} [measure_space Ω]
  {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} (h : indep_fun X Y) :
  𝔼[X*Y] = 𝔼[X] * 𝔼[Y] :=
by { apply integral_mul_eq_integral_mul_integral_of_indep_fun; assumption }

lemma indicator_preimage (f : α → β) (B : set β) {c : γ} [has_zero γ] :
  (B.indicator (1 : β → ℝ)) ∘ f = (f ⁻¹' B).indicator 1 :=
begin
  simp only [set.indicator], funext x,
  split_ifs with hx; { rw set.mem_preimage at hx, simp [hx] }
end

theorem indep_fun_iff_integral_mul [is_finite_measure μ]
  {f : α → β} {hfm : measurable f} {g : α → β'} {hgm : measurable g} :
  indep_fun f g μ ↔ ∀ φ : β → ℝ, ∀ ψ : β' → ℝ,
  measurable φ → integrable (φ ∘ f) μ → measurable ψ → integrable (ψ ∘ g) μ →
  integral μ ((φ ∘ f) * (ψ ∘ g)) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) :=
begin
  split,
  { rintro hfg φ ψ hφ hf hψ hg,
    apply integral_mul_eq_integral_mul_integral_of_indep_fun hf hg,
    apply indep_fun_comp_of_indep_fun hfg; assumption },
  { rintro h _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩,
    let φ : β → ℝ := A.indicator 1,
    let ψ : β' → ℝ := B.indicator 1,

    have hφ : measurable φ := measurable_one.indicator hA,
    have hψ : measurable ψ := measurable_one.indicator hB,

    have hf : integrable (φ ∘ f) μ := by {
      apply integrable.indicator, simp, apply integrable_const,
      apply hfm.comp, exact measurable_id, exact hA },
    have hg : integrable (ψ ∘ g) μ := by {
      apply integrable.indicator, simp, apply integrable_const,
      apply hgm.comp, exact measurable_id, exact hB },

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
    exact ℝ, apply_instance, exact 0, apply_instance,
    exact ℝ, apply_instance, exact 0, apply_instance,
    exact measure_ne_top μ (f ⁻¹' A ∩ g ⁻¹' B),
    exact ennreal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _) }
end

end probability_theory

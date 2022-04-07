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

end probability_theory

namespace measure_theory

lemma indicator_preimage (f : α → β) (B : set β) :
  (B.indicator (1 : β → ℝ)) ∘ f = (f ⁻¹' B).indicator 1 :=
begin
  simp only [set.indicator], funext x,
  split_ifs with hx; { rw set.mem_preimage at hx, simp [hx] }
end

lemma measurable_set.integral_indicator {E : set α} (hE : measurable_set E) :
  integral μ (E.indicator 1) = (μ E).to_real :=
begin
  convert integral_indicator_const (1 : ℝ) hE,
  simp only [algebra.id.smul_eq_mul, mul_one]
end

end measure_theory

open measure_theory

namespace probability_theory

theorem indep_fun_iff_integral_mul [is_finite_measure μ] {f : α → β} {g : α → β'}
  {mβ : measurable_space β} {mβ' : measurable_space β'} {hfm : measurable f} {hgm : measurable g} :
  indep_fun f g μ ↔
  ∀ {φ : β → ℝ} {ψ : β' → ℝ},
    measurable φ → integrable (φ ∘ f) μ → measurable ψ → integrable (ψ ∘ g) μ →
    integral μ ((φ ∘ f) * (ψ ∘ g)) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) :=
begin
  split,
  { rintro hfg φ ψ hφ hf hψ hg,
    exact indep_fun.integral_mul_of_integrable (hfg.comp hφ hψ) hf hg },
  { rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
    have hf : integrable (A.indicator (1 : β → ℝ) ∘ f) μ :=
      by { refine integrable.indicator _ (hfm.comp measurable_id hA),
      simp only [pi.one_apply], apply integrable_const },
    have hg : integrable (B.indicator (1 : β' → ℝ) ∘ g) μ :=
      by { refine integrable.indicator _ (hgm.comp measurable_id hB),
      simp only [pi.one_apply], apply integrable_const },
    rw [← ennreal.to_real_eq_to_real, ennreal.to_real_mul],
    { convert ← h (measurable_one.indicator hA) hf (measurable_one.indicator hB) hg,
      { convert ← measurable_set.integral_indicator ((hfm hA).inter (hgm hB)),
        funext,
        simp only [set.indicator, pi.one_apply, pi.mul_apply, function.comp_app, boole_mul],
        classical,
        convert ite_and (f x ∈ A) (g x ∈ B) (1:ℝ) 0 },
      { exact measurable_set.integral_indicator (hfm hA) },
      { exact measurable_set.integral_indicator (hgm hB) } },
    { apply measure_ne_top },
    { exact ennreal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _) } }
end

end probability_theory

namespace measure_theory

lemma ae_strongly_measurable.mono {m1 m2 : measurable_space α} {μ : measure α} (hm : m1 ≤ m2)
  {f : α → ℝ} :
  ae_strongly_measurable f (μ.trim hm) → ae_strongly_measurable f μ :=
by { rintro ⟨ff, h1, h2⟩, exact ⟨ff, h1.mono hm, ae_eq_of_ae_eq_trim h2⟩ }

noncomputable def Lp_trim_to_Lp {m1 m2 : measurable_space α} {μ : measure α} (hm : m1 ≤ m2) :
  Lp ℝ 1 (μ.trim hm) → Lp ℝ 1 μ :=
begin
  intro f,
  have hf := Lp.ae_strongly_measurable f,
  refine mem_ℒp.to_Lp f ⟨hf.mono hm, _⟩,
  rw ← snorm_trim_ae hm hf,
  exact Lp.snorm_lt_top f
end

lemma Lp_trim_to_Lp.ae_eq {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2}
  {f : Lp ℝ 1 (μ.trim hm)} :
  Lp_trim_to_Lp hm f =ᵐ[μ] f :=
by simp [Lp_trim_to_Lp, mem_ℒp.coe_fn_to_Lp]

lemma Lp_trim_to_Lp.continuous {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2}
  {f : Lp ℝ 1 (μ.trim hm)} :
  continuous (@Lp_trim_to_Lp α m1 m2 μ hm) :=
begin
  have : lipschitz_with 1 (@Lp_trim_to_Lp α m1 m2 μ hm) := by {
    rintro u v,
    simp [Lp_trim_to_Lp],
    have := @Lp.edist_def α ℝ m1 1 (μ.trim hm) _ u v,
  },
  apply lipschitz_with.continuous,
end

example {α : Type*} {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα} :
  continuous (λ (x : ↥(Lp ℝ 1 (μ.trim hm))), integral μ ⇑x) :=
begin
  -- have : continuous (Lp_trim_to_Lp hm), sorry,
  -- have := continuous_integral.comp this,
  sorry
end

example
  {α : Type*} {mα' : measurable_space α} {mα : measurable_space α} {μ : measure α}
  [is_finite_measure μ]
  {hm : mα' ≤ mα}
  {S : set α} {hS1 : mα.measurable_set' S} {hS : indep_sets mα'.measurable_set' {S} μ}
  {f : α → ℝ} {hf : integrable f (μ.trim hm)}
  :
  ∫ a in S, f a ∂μ = (μ S).to_real • ∫ a, f a ∂μ :=
begin
  revert f, apply integrable.induction,
  { rintro c s hs1 -,
    have hs' := hm _ hs1,
    have h1 : (μ.restrict S) s ≠ ⊤ := by { rw [measure.restrict_apply hs'], apply measure_ne_top },
    rw ← integral_congr_ae (@indicator_const_Lp_coe_fn α ℝ mα 1 μ _ s hs' (measure_ne_top _ _) c),
    rw ← integral_congr_ae (@indicator_const_Lp_coe_fn α ℝ mα 1 (μ.restrict S) _ s hs' h1 c),
    rw [integral_indicator_const_Lp, integral_indicator_const_Lp, measure.restrict_apply hs'],
    rw [hS s S hs1 (set.mem_singleton _), ennreal.to_real_mul],
    simp only [algebra.id.smul_eq_mul],
    ring },
  { rintro f g - hf hg h1 h2,
    have hf' : integrable f μ := integrable_of_integrable_trim hm hf,
    have hg' : integrable g μ := integrable_of_integrable_trim hm hg,
    rw [integral_add', integral_add' hf' hg', h1, h2, smul_add],
    { exact integrable_on_univ.mp ((integrable_on_univ.mpr hf').restrict measurable_set.univ) },
    { exact integrable_on_univ.mp ((integrable_on_univ.mpr hg').restrict measurable_set.univ) } },
  {
    simp,
    simp_rw ← @sub_eq_zero ℝ _ (integral _ _) _,
    simp_rw ← set.mem_singleton_iff,
    apply is_closed.preimage,
    apply continuous.sub,
    { sorry },
    { refine continuous_const.mul _,
      extract_goal,
      sorry },
    { exact t1_space.t1 0 }
    -- apply is_seq_closed_iff_is_closed.mp,
    -- { apply is_seq_closed_of_def,
    --   rintro f ℓ h1 h2,
    --   simp at h1 ⊢,
    --   have := (@continuous_integral α ℝ _ _ _ mα μ).tendsto,
    --   have := (continuous_integral.tendsto ℓ).comp h2, simp at this,
    --   sorry },
    -- { apply_instance }

  },
  { rintro f g hfg - h,
    have h1 : f =ᵐ[μ] g := ae_eq_of_ae_eq_trim hfg,
    have h2 : f =ᵐ[μ.restrict S] g := filter.eventually_eq.restrict h1,
    rwa [← integral_congr_ae h1, ← integral_congr_ae h2] }
end

end measure_theory

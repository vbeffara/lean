import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal

variables {α β β' γ γ' : Type*} {mα : measurable_space α} {μ : measure α}

lemma measurable_set.integral_indicator {E : set α} (hE : measurable_set E) :
  integral μ (E.indicator 1) = (μ E).to_real :=
begin
  convert ← integral_indicator_const (1 : ℝ) hE,
  exact (smul_eq_mul _).trans (mul_one _)
end

namespace probability_theory

theorem indep_fun_iff_integral_comp_mul [is_finite_measure μ] {f : α → β} {g : α → β'}
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
      { convert ← ((hfm hA).inter (hgm hB)).integral_indicator,
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
λ f, (mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f

lemma Lp_trim_to_Lp.ae_eq {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2}
  {f : Lp ℝ 1 (μ.trim hm)} : Lp_trim_to_Lp hm f =ᵐ[μ] f :=
by simp only [Lp_trim_to_Lp, mem_ℒp.coe_fn_to_Lp]

lemma continuous_integral_trim {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα} :
  continuous (λ (f : Lp ℝ 1 (μ.trim hm)), integral μ f) :=
begin
  convert continuous_integral,
  exact funext (λ f, integral_trim_ae hm (Lp.ae_strongly_measurable f))
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
      exact continuous_integral_trim },
    { exact t1_space.t1 0 }
  },
  { rintro f g hfg - h,
    have h1 : f =ᵐ[μ] g := ae_eq_of_ae_eq_trim hfg,
    have h2 : f =ᵐ[μ.restrict S] g := filter.eventually_eq.restrict h1,
    rwa [← integral_congr_ae h1, ← integral_congr_ae h2] }
end

end measure_theory

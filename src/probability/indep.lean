import algebra.indicator_function
import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal

variables {α β β' γ γ' : Type*} {mα : measurable_space α} {μ : measure α}

namespace measure_theory

noncomputable def Lp_trim_to_Lp {m1 m2 : measurable_space α} (μ : measure α) (hm : m1 ≤ m2) :
  Lp ℝ 1 (μ.trim hm) → Lp ℝ 1 μ :=
λ f, Lp_trim_to_Lp_meas ℝ ℝ 1 μ hm f

lemma Lp_trim_to_Lp.ae_eq {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2}
  {f : Lp ℝ 1 (μ.trim hm)} : Lp_trim_to_Lp μ hm f =ᵐ[μ] f :=
@Lp_trim_to_Lp_meas_ae_eq α ℝ ℝ 1 _ _ _ _ _ μ hm f

lemma Lp_trim_to_Lp.isometry {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2} :
  isometry (Lp_trim_to_Lp μ hm) :=
begin
  rintro f g,
  rw [Lp.edist_def, Lp.edist_def,
    snorm_trim_ae hm ((Lp.ae_strongly_measurable f).sub (Lp.ae_strongly_measurable g))],
  exact snorm_congr_ae (Lp_trim_to_Lp.ae_eq.sub Lp_trim_to_Lp.ae_eq)
end

lemma continuous_integral_trim {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα} :
  continuous (λ (f : Lp ℝ 1 (μ.trim hm)), integral μ f) :=
begin
  convert continuous_integral,
  exact funext (λ f, integral_trim_ae hm (Lp.ae_strongly_measurable f))
end

lemma continuous_integral_trim_restrict {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα}
  {S : set α} (hS : mα.measurable_set' S) :
  continuous (λ f : Lp ℝ 1 (μ.trim hm), ∫ a in S, f a ∂μ) :=
begin
  have h : ∀ {f}, ∫ a in S, (Lp_trim_to_Lp μ hm f) a ∂μ = ∫ a in S, f a ∂μ,
    from λ f, set_integral_congr_ae hS (Lp_trim_to_Lp.ae_eq.mono (λ _, imp_intro)),
  simp_rw ← h,
  exact (continuous_set_integral S).comp Lp_trim_to_Lp.isometry.continuous,
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
    rw [integral_indicator_const _ (hm _ hs1), integral_indicator_const _ (hm _ hs1),
      measure.restrict_apply (hm _ hs1), hS s S hs1 (set.mem_singleton _), ennreal.to_real_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (ennreal.to_real _)] },
  { rintro f g - hf hg h1 h2,
    have hfi : integrable f μ := integrable_of_integrable_trim hm hf,
    have hgi : integrable g μ := integrable_of_integrable_trim hm hg,
    have hfr : integrable f (μ.restrict S) := integrable.mono_measure hfi measure.restrict_le_self,
    have hgr : integrable g (μ.restrict S) := integrable.mono_measure hgi measure.restrict_le_self,
    rw [integral_add' hfr hgr, integral_add' hfi hgi, h1, h2, smul_add] },
  {
    simp,
    simp_rw ← @sub_eq_zero ℝ _ (integral _ _) _,
    simp_rw ← set.mem_singleton_iff,
    apply is_closed.preimage,
    apply continuous.sub,
    { exact continuous_integral_trim_restrict hS1 },
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

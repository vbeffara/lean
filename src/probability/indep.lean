import algebra.indicator_function
import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal

variables {α : Type*} {m1 m2 : measurable_space α} {p : ennreal} {μ : measure α} {hm : m1 ≤ m2}

namespace measure_theory

noncomputable def Lp_trim_to_Lp (p : ennreal) (μ : measure α) (hm : m1 ≤ m2) :
  Lp ℝ p (μ.trim hm) → Lp ℝ p μ :=
λ f, Lp_trim_to_Lp_meas ℝ ℝ p μ hm f

lemma Lp_trim_to_Lp.ae_eq {f : Lp ℝ p (μ.trim hm)} :
  Lp_trim_to_Lp p μ hm f =ᵐ[μ] f :=
@Lp_trim_to_Lp_meas_ae_eq α ℝ ℝ p _ _ _ _ _ μ hm f

lemma Lp_trim_to_Lp.snorm {f : Lp ℝ p (μ.trim hm)} :
  snorm (Lp_trim_to_Lp p μ hm f) p μ = snorm f p μ :=
snorm_congr_ae Lp_trim_to_Lp.ae_eq

lemma Lp_trim_to_Lp.isometry [fact (1 ≤ p)] :
  isometry (Lp_trim_to_Lp p μ hm) :=
begin
  rintro f g,
  rw [Lp.edist_def, Lp.edist_def],
  rw [snorm_trim_ae hm ((Lp.ae_strongly_measurable f).sub (Lp.ae_strongly_measurable g))],
  exact snorm_congr_ae (Lp_trim_to_Lp.ae_eq.sub Lp_trim_to_Lp.ae_eq)
end

@[continuity]
lemma Lp_trim_to_Lp.continuous [fact (1 ≤ p)]:
  continuous (Lp_trim_to_Lp p μ hm) :=
Lp_trim_to_Lp.isometry.continuous

@[continuity]
lemma continuous_integral_trim :
  continuous (λ (f : Lp ℝ 1 (μ.trim hm)), integral μ f) :=
begin
  simp_rw [← integral_congr_ae Lp_trim_to_Lp.ae_eq],
  exact continuous_integral.comp Lp_trim_to_Lp.isometry.continuous
end

@[continuity]
lemma continuous_set_integral_trim {S : set α} (hS : measurable_set S) :
  continuous (λ f : Lp ℝ 1 (μ.trim hm), ∫ a in S, f a ∂μ) :=
begin
  simp_rw [← integral_congr_ae Lp_trim_to_Lp.ae_eq.restrict],
  exact (continuous_set_integral S).comp Lp_trim_to_Lp.isometry.continuous,
end

example {S : set α} {hS1 : measurable_set S} {hS : indep_sets m1.measurable_set' {S} μ}
  {f : α → ℝ} {hf : integrable f (μ.trim hm)} :
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
  { apply is_closed_eq; continuity },
  { rintro f g hfg - h,
    have h1 : f =ᵐ[μ] g := ae_eq_of_ae_eq_trim hfg,
    rwa [← integral_congr_ae h1, ← integral_congr_ae h1.restrict] }
end

end measure_theory

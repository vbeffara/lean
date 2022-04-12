import probability.integration
import probability.notation
open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal

variables {α β β' γ γ' : Type*} {mα : measurable_space α} {μ : measure α}

namespace measure_theory

noncomputable def Lp_trim_to_Lp {m1 m2 : measurable_space α} (μ : measure α) (hm : m1 ≤ m2) :
  Lp ℝ 1 (μ.trim hm) → Lp ℝ 1 μ :=
λ f, (mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f

lemma Lp_trim_to_Lp.ae_eq {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2}
  {f : Lp ℝ 1 (μ.trim hm)} : Lp_trim_to_Lp μ hm f =ᵐ[μ] f :=
by simp only [Lp_trim_to_Lp, mem_ℒp.coe_fn_to_Lp]

lemma Lp_trim_to_Lp.isometry {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2} :
  isometry (Lp_trim_to_Lp μ hm) :=
begin
  rintro f g,
  rw [Lp.edist_def, Lp.edist_def,
    snorm_trim_ae hm ((Lp.ae_strongly_measurable f).sub (Lp.ae_strongly_measurable g))],
  exact snorm_congr_ae (Lp_trim_to_Lp.ae_eq.sub Lp_trim_to_Lp.ae_eq)
end

lemma Lp_trim_to_Lp.dist {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2} :
  ∀ {f g}, dist (Lp_trim_to_Lp μ hm f) (Lp_trim_to_Lp μ hm g) = dist f g :=
Lp_trim_to_Lp.isometry.dist_eq

lemma Lp_trim_to_Lp.edist {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2} :
  ∀ {f g}, edist (Lp_trim_to_Lp μ hm f) (Lp_trim_to_Lp μ hm g) = edist f g :=
Lp_trim_to_Lp.isometry.edist_eq

lemma Lp_trim_to_Lp.continuous {m1 m2 : measurable_space α} {μ : measure α} {hm : m1 ≤ m2} :
  continuous (Lp_trim_to_Lp μ hm) :=
Lp_trim_to_Lp.isometry.continuous

lemma continuous_integral_trim {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα} :
  continuous (λ (f : Lp ℝ 1 (μ.trim hm)), integral μ f) :=
begin
  convert continuous_integral,
  exact funext (λ f, integral_trim_ae hm (Lp.ae_strongly_measurable f))
end

example {P Q : Prop} : P → Q → P := by { exact imp_intro}

lemma continuous_integral_trim_restrict {mα' mα : measurable_space α} {μ : measure α} {hm : mα' ≤ mα}
  {S : set α} (hS : mα.measurable_set' S) :
  continuous (λ f : Lp ℝ 1 (μ.trim hm), ∫ a in S, f a ∂μ) :=
begin
  let Ψ := λ f : Lp ℝ 1 μ, ∫ a in S, f a ∂μ,
  have h : ∀ {f}, Ψ (Lp_trim_to_Lp μ hm f) = ∫ a in S, f a ∂μ :=
    by { intro f,
      apply set_integral_congr_ae hS,
      apply Lp_trim_to_Lp.ae_eq.mono,
      exact λ _, imp_intro },
  simp_rw ← h,
  exact (continuous_set_integral S).comp Lp_trim_to_Lp.continuous,
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

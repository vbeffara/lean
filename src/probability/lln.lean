import probability.independence
import probability.notation
import probability.integration
import measure_theory.constructions.borel_space
import measure_theory.measure.finite_measure_weak_convergence
import measure_theory.function.convergence_in_measure
import probability.indep

open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory
noncomputable theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]
variables {X : ℕ → Ω → ℝ} {n : ℕ} {μ : probability_measure ℝ}

def is_iid (μ : probability_measure ℝ) (X : ℕ → Ω → ℝ) : Prop :=
  Indep_fun (λ _, real.measurable_space) X volume ∧
  ∀ n, measure.map (X n) volume = μ

def has_first_moment (μ : probability_measure ℝ) : Prop :=
@has_finite_integral ℝ ℝ _ (by apply_instance) id μ.val

def recenter (X : Ω → ℝ) (ω : Ω) : ℝ := X ω - 𝔼[X]

lemma avg_recenter {X : Ω → ℝ} {hX : integrable X} :
𝔼[recenter X] = 0 :=
begin
  simp_rw [recenter, integral_sub hX (integrable_const (integral volume X)), integral_const],
  rw [measure_univ, ennreal.one_to_real, algebra.id.smul_eq_mul, one_mul, sub_self]
end

lemma recenter_add {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} :
  recenter (X + Y) = recenter X + recenter Y :=
begin
  ext ω, simp only [recenter, pi.add_apply], rw integral_add hX hY, ring
end

def shift (a : ℝ) (x : ℝ) : ℝ := x + a

lemma recenter_shift {X : Ω → ℝ} : recenter X = shift (- 𝔼[X]) ∘ X := rfl

lemma recenter_comap {X : Ω → ℝ} :
  measurable_space.comap (recenter X) real.measurable_space =
  measurable_space.comap X real.measurable_space :=
begin
  ext A, simp [measurable_space.comap], split,
  { rintro ⟨s,hs1,hs2⟩, use (shift (- 𝔼[X])) ⁻¹' s, split,
    { exact measurable_set_preimage (measurable_add_const _) hs1 },
    { rwa [←set.preimage_comp,←recenter_shift] } },
  { rintro ⟨s,hs1,hs2⟩, use (shift 𝔼[X]) ⁻¹' s, split,
    { exact measurable_set_preimage (measurable_add_const _) hs1 },
    { rw [←set.preimage_comp,recenter_shift,←hs2], ext, simp [shift] } }
end

lemma indep_recenter {X Y : Ω → ℝ} (h : indep_fun X Y) : indep_fun (recenter X) (recenter Y) :=
by rwa [indep_fun, recenter_comap, recenter_comap]

def cov (X Y : Ω → ℝ) : ℝ := 𝔼[recenter X * recenter Y]

lemma cov_eq_zero_of_indep {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} :
  indep_fun X Y → cov X Y = 0 :=
begin
  intro h,
  rw [cov, integral_mul_eq_integral_mul_integral_of_indep_fun, avg_recenter, zero_mul],
  { exact hX },
  { apply hX.sub, apply integrable_const },
  { apply hY.sub, apply integrable_const },
  { exact indep_recenter h }
end

noncomputable def avg' (μ : probability_measure ℝ) : ℝ :=
integral μ.val id

def has_second_moment (μ : probability_measure ℝ) : Prop :=
@has_finite_integral ℝ ℝ _ (by apply_instance) (λ x, x * x) μ.val

noncomputable def var (X : Ω → ℝ) : ℝ := 𝔼[X ^ 2] - 𝔼[X] ^ 2

noncomputable def var' (μ : probability_measure ℝ) : ℝ :=
integral μ.val (λ x, (x - avg' μ) ^ 2)

noncomputable def partial_avg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
(∑ i in finset.range n, X i ω) / n

lemma blah {f : Ω → ℝ} {hf : measurable f} : integrable (f*f) → integrable f := by
{
  rintro ⟨h1,h2⟩,
  refine ⟨hf.ae_strongly_measurable, _⟩,
  simp [has_finite_integral],
  rw [←measure_theory.snorm_one_eq_lintegral_nnnorm],
  apply lt_of_le_of_lt
    (@snorm_le_snorm_mul_rpow_measure_univ Ω ℝ _ volume _ 1 2 _ f hf.ae_strongly_measurable),
  rw snorm_eq_lintegral_rpow_nnnorm,
  simp [measure_univ],
  apply ennreal.rpow_lt_top_of_nonneg,
  norm_num,
  apply ne_top_of_lt,
  have : (2 : ℝ) = ↑(2 : ℕ) := by norm_num,
  simp_rw [this, ennreal.rpow_nat_cast, pow_two],
  convert h2, funext, simp,
  norm_num,
  norm_num,
  apply ennreal.coe_le_coe.mpr, simp
}

lemma var_sum {X Y : Ω → ℝ} {hXm : measurable X} {hYm : measurable Y}
  (h : indep_fun X Y) (hX : integrable (X*X)) (hY : integrable (Y*Y)) :
  var (X + Y) = var X + var Y :=
begin
  have h1 : integrable X := blah hX,
  have h2 : integrable Y := blah hY,
  have h3 : integrable (X*Y) := integrable_mul_of_integrable_of_indep_fun h h1 h2,
  have h4 : integrable (Y*X) := by { rw [mul_comm], exact h3 },

  have hh := integral_mul_eq_integral_mul_integral_of_indep_fun' h,

  simp_rw [pi.mul_apply] at hh,
  apply eq_of_sub_eq_zero,
  simp [var,pow_two,mul_add,add_mul],
  repeat { rw [integral_add] },
  simp_rw [@mul_comm _ _ (Y _) (X _), hh],
  ring, assumption', { exact hX.add h3 }, { exact h4.add hY },
end

lemma var_div_n {hiid : is_iid μ X} : var (partial_avg X n) = (var' μ) / n := sorry

theorem weak_law {X : ℕ → Ω → ℝ} {hiid : is_iid μ X} {hl1 : has_first_moment μ} :
  tendsto_in_measure volume (partial_avg X) filter.cofinite (λ ω, avg' μ) := sorry

theorem strong_law {X : ℕ → Ω → ℝ} {hiid : is_iid μ X} {hl1 : has_first_moment μ} :
  ∀ᵐ ω : Ω, filter.tendsto (λ n, partial_avg X n ω) filter.cofinite (nhds (avg' μ)) := sorry

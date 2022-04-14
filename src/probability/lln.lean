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

def cov (X Y : Ω → ℝ) : ℝ := 𝔼[X * Y] - 𝔼[X] * 𝔼[Y]

lemma cov_eq_zero_of_indep {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y}
  (h : indep_fun X Y) :
  cov X Y = 0 :=
by simp_rw [cov, indep_fun.integral_mul_of_integrable h hX hY, sub_self]

noncomputable def var (X : Ω → ℝ) : ℝ := 𝔼[X ^ 2] - 𝔼[X] ^ 2

noncomputable def partial_avg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
(∑ i in finset.range n, X i ω) / n

lemma blah {f : Ω → ℝ} (hf : measurable f) : integrable (f*f) → integrable f := by
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
  have h1 : integrable X := blah hXm hX,
  have h2 : integrable Y := blah hYm hY,
  have h3 : integrable (X*Y) := indep_fun.integrable_mul h h1 h2,
  have hh := indep_fun.integral_mul_of_integrable h h1 h2,

  apply eq_of_sub_eq_zero,
  simp_rw [var, pow_two, mul_add, add_mul, @mul_comm _ _ Y X],
  repeat { rw [integral_add'] },
  { ring_nf, rw [hh], ring },
  assumption',
  { exact hX.add h3 },
  { exact h3.add hY },
end

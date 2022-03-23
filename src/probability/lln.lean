import probability.independence
import measure_theory.constructions.borel_space
import measure_theory.measure.finite_measure_weak_convergence
import measure_theory.function.convergence_in_measure

open measure_theory probability_theory
open_locale big_operators
noncomputable theory

variables {Ω : Type*} [measure_space Ω] {X : ℕ → Ω → ℝ} {n : ℕ} {μ : probability_measure ℝ}

def is_independent (X : ℕ → Ω → ℝ) : Prop :=
Indep_fun (λ _, real.measurable_space) X volume

def is_identically_distributed (μ : probability_measure ℝ) (X : ℕ → Ω → ℝ) : Prop :=
∀ n, measure.map (X n) volume = μ

def is_iid (μ : probability_measure ℝ) (X : ℕ → Ω → ℝ) : Prop :=
is_independent X ∧ is_identically_distributed μ X

def is_l1_seq (X : ℕ → Ω → ℝ) : Prop := ∀ n, has_finite_integral (X n)

def has_first_moment (μ : probability_measure ℝ) : Prop :=
@has_finite_integral ℝ ℝ _ (by apply_instance) id μ.val

def avg (X : Ω → ℝ) : ℝ := integral volume X

lemma avg_add {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} : avg (X + Y) = avg X + avg Y :=
begin
  apply integral_add; assumption
end

def recenter (X : Ω → ℝ) (ω : Ω) : ℝ := X ω - avg X

lemma recenter_add {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} :
  recenter (X + Y) = recenter X + recenter Y :=
begin
  ext ω, simp [recenter], rw avg_add, ring, exact hX, exact hY
end

def shift (a : ℝ) (x : ℝ) : ℝ := x + a

lemma recenter_shift {X : Ω → ℝ} : recenter X = shift (- avg X) ∘ X := rfl

lemma recenter_comap {X : Ω → ℝ} :
  measurable_space.comap (recenter X) real.measurable_space =
  measurable_space.comap X real.measurable_space :=
begin
  ext A, simp [measurable_space.comap], split,
  { rintro ⟨s,hs1,hs2⟩, use (shift (- avg X)) ⁻¹' s, split,
    { exact measurable_set_preimage (measurable_add_const _) hs1 },
    { rwa [←set.preimage_comp,←recenter_shift] } },
  { rintro ⟨s,hs1,hs2⟩, use (shift (avg X)) ⁻¹' s, split,
    { exact measurable_set_preimage (measurable_add_const _) hs1 },
    { rw [←set.preimage_comp,recenter_shift,←hs2], ext, simp [shift] } }
end

lemma indep_recenter {X Y : Ω → ℝ} (h : indep_fun X Y) : indep_fun (recenter X) (recenter Y) :=
by rwa [indep_fun,recenter_comap,recenter_comap]

def cov (X Y : Ω → ℝ) : ℝ := avg (recenter X * recenter Y)

lemma cov_indep {X Y : Ω → ℝ} : indep_fun X Y → cov X Y = 0 :=
begin
  intro h, rw [cov,avg],
end

noncomputable def avg' (μ : probability_measure ℝ) : ℝ :=
integral μ.val id

def has_second_moment (μ : probability_measure ℝ) : Prop :=
@has_finite_integral ℝ ℝ _ (by apply_instance) (λ x, x * x) μ.val

noncomputable def var (X : Ω → ℝ) : ℝ :=
avg ((recenter X) ^ 2)

noncomputable def var' (μ : probability_measure ℝ) : ℝ :=
integral μ.val (λ x, (x - avg' μ) ^ 2)

noncomputable def partial_avg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
(∑ i in finset.range n, X i ω) / n

lemma var_sum {X Y : Ω → ℝ} : indep_fun X Y → var (X + Y) = var X + var Y :=
begin
  intro hindep,
  simp [var], rw [recenter_add,sq,sq,sq,add_mul,mul_add,mul_add,avg_add,avg_add,avg_add],
  have := calc var (X + Y) = avg (λ ω, ((X + Y) ω - avg (X + Y)) ^ 2) : rfl
    ... = avg (λ ω, (X ω + Y ω - avg (X + Y)) ^ 2) : rfl,
  sorry
end

lemma var_div_n {hiid : is_iid μ X} : var (partial_avg X n) = (var' μ) / n := sorry

theorem weak_law {X : ℕ → Ω → ℝ} {hiid : is_iid μ X} {hl1 : has_first_moment μ} :
  tendsto_in_measure volume (partial_avg X) filter.cofinite (λ ω, avg' μ) := sorry

theorem strong_law {X : ℕ → Ω → ℝ} {hiid : is_iid μ X} {hl1 : has_first_moment μ} :
  ∀ᵐ ω : Ω, filter.tendsto (λ n, partial_avg X n ω) filter.cofinite (nhds (avg' μ)) := sorry

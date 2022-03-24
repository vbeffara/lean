import probability.independence
import probability.notation
import measure_theory.constructions.borel_space
import measure_theory.measure.finite_measure_weak_convergence
import measure_theory.function.convergence_in_measure

open measure_theory probability_theory
open_locale big_operators measure_theory probability_theory
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

lemma avg_add {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} : 𝔼[X + Y] = 𝔼[X] + 𝔼[Y] :=
begin
  apply integral_add; assumption
end

def recenter (X : Ω → ℝ) (ω : Ω) : ℝ := X ω - 𝔼[X]

lemma avg_recenter {X : Ω → ℝ} {hX : integrable X} : 𝔼[recenter X] = 0 := sorry

lemma recenter_add {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} :
  recenter (X + Y) = recenter X + recenter Y :=
begin
  ext ω, simp [recenter], rw integral_add, ring, exact hX, exact hY
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
by rwa [indep_fun,recenter_comap,recenter_comap]

def cov (X Y : Ω → ℝ) : ℝ := 𝔼[recenter X * recenter Y]

def measurable' {α β : Type*} (F : set (set α)) [measurable_space β] (f : α → β) : Prop :=
∀ ⦃t : set β⦄, measurable_set t → f ⁻¹' t ∈ F

lemma indep_fun_of_indep_sets {F1 F2 : set (set Ω)} (hindep : indep_sets F1 F2)
  {X Y : Ω → ℝ} {hX : measurable' F1 X} {hY : measurable' F2 Y} : indep_fun X Y
| _ _ ⟨_,hA,rfl⟩ ⟨_,hB,rfl⟩ := hindep _ _ (hX hA) (hY hB)

lemma integral_mul_of_indep_sets {F1 F2 : set (set Ω)} (hindep : indep_sets F1 F2) {X Y : Ω → ℝ}
  {hXm : measurable' F1 X} {hXi : integrable X}
  {hYm : measurable' F2 Y} {hYi : integrable Y} :
integral volume (X * Y) = integral volume X * integral volume Y := sorry

lemma integral_indep {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y} {h : indep_fun X Y} :
  ∫ ω, (X * Y) ω = (∫ ω, X ω) * (∫ ω, Y ω) :=
begin
  apply integrable.induction (λ X : Ω → ℝ, ∫ ω, (X * Y) ω = (∫ ω, X ω) * (∫ ω, Y ω)),
  { simp, sorry },
  { simp, intros f g h1 h2 h3 h4 h5, simp_rw [add_mul], rw [integral_add,integral_add,h4,h5],
    simp [*], ring, exact h2, exact h3, sorry, sorry },
  { simp, sorry },
  { sorry },
  assumption
end

lemma cov_indep {X Y : Ω → ℝ} {hX : integrable X} : indep_fun X Y → cov X Y = 0 :=
begin
  intro h, rw [cov,integral_indep,avg_recenter], ring, exact hX, sorry, sorry, exact indep_recenter h
end

noncomputable def avg' (μ : probability_measure ℝ) : ℝ :=
integral μ.val id

def has_second_moment (μ : probability_measure ℝ) : Prop :=
@has_finite_integral ℝ ℝ _ (by apply_instance) (λ x, x * x) μ.val

noncomputable def var (X : Ω → ℝ) : ℝ := 𝔼[(recenter X) ^ 2]

noncomputable def var' (μ : probability_measure ℝ) : ℝ :=
integral μ.val (λ x, (x - avg' μ) ^ 2)

noncomputable def partial_avg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
(∑ i in finset.range n, X i ω) / n

lemma var_sum {X Y : Ω → ℝ} : indep_fun X Y → var (X + Y) = var X + var Y := sorry

lemma var_div_n {hiid : is_iid μ X} : var (partial_avg X n) = (var' μ) / n := sorry

theorem weak_law {X : ℕ → Ω → ℝ} {hiid : is_iid μ X} {hl1 : has_first_moment μ} :
  tendsto_in_measure volume (partial_avg X) filter.cofinite (λ ω, avg' μ) := sorry

theorem strong_law {X : ℕ → Ω → ℝ} {hiid : is_iid μ X} {hl1 : has_first_moment μ} :
  ∀ᵐ ω : Ω, filter.tendsto (λ n, partial_avg X n ω) filter.cofinite (nhds (avg' μ)) := sorry

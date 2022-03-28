import probability.independence
import probability.notation
import probability.integration
import measure_theory.constructions.borel_space
import measure_theory.measure.finite_measure_weak_convergence
import measure_theory.function.convergence_in_measure

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

def measurable' {α β : Type*} (F : set (set α)) [measurable_space β] (f : α → β) : Prop :=
∀ ⦃t : set β⦄, measurable_set t → f ⁻¹' t ∈ F

lemma indep_fun_of_indep_sets {F1 F2 : set (set Ω)} (hindep : indep_sets F1 F2)
  {X Y : Ω → ℝ} {hX : measurable' F1 X} {hY : measurable' F2 Y} : indep_fun X Y
| _ _ ⟨_,hA,rfl⟩ ⟨_,hB,rfl⟩ := hindep _ _ (hX hA) (hY hB)

lemma integral_mul_of_indep_sets {F1 F2 : set (set Ω)} (hindep : indep_sets F1 F2) {X Y : Ω → ℝ}
  {hXm : measurable' F1 X} {hXi : integrable X}
  {hYm : measurable' F2 Y} {hYi : integrable Y} :
𝔼[X * Y] = 𝔼[X] * 𝔼[Y] := sorry

def pos_part (x : ℝ) := max x 0
def neg_part (x : ℝ) := max (-x) 0
lemma eq_pos_sub_neg (X : Ω → ℝ) : X = pos_part ∘ X - neg_part ∘ X :=
begin
  symmetry, ext ω, simp, apply max_zero_sub_max_neg_zero_eq_self
end

lemma integral_indep_of_pos {X Y : Ω → ℝ} {hXYind : indep_fun X Y}
  {hXpos : 0 ≤ X} {hXmes : measurable X} {hYpos : 0 ≤ Y} {hYmes : measurable Y}:
  𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  rw @integral_eq_lintegral_of_nonneg_ae _ _ _ (X * Y)
    (filter.eventually_of_forall (λ ω, mul_nonneg (hXpos ω) (hYpos ω)))
    (hXmes.mul hYmes).ae_measurable,

  rw @integral_eq_lintegral_of_nonneg_ae _ _ _ X (filter.eventually_of_forall hXpos)
    hXmes.ae_measurable,

  rw @integral_eq_lintegral_of_nonneg_ae _ _ _ Y (filter.eventually_of_forall hYpos)
    hYmes.ae_measurable,

  let f : Ω → ennreal := ennreal.of_real ∘ X,
  let g : Ω → ennreal := ennreal.of_real ∘ Y,
  have := @lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun Ω _ volume f g _ _ _,
  have := congr_arg ennreal.to_real this,
  convert this,
  { funext, simp [f,g], apply ennreal.of_real_mul, apply hXpos },
  { exact ennreal.to_real_mul.symm },
  { exact measurable.ennreal_of_real hXmes },
  { exact measurable.ennreal_of_real hYmes },
  { rintro _ _ ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩, simp [f,g],
    rw @set.preimage_comp _ _ _ X ennreal.of_real _, set A' := ennreal.of_real ⁻¹' A,
    rw @set.preimage_comp _ _ _ Y ennreal.of_real _, set B' := ennreal.of_real ⁻¹' B,
    apply hXYind,
    { simp,
      apply @measurable_set_preimage _ _ _ _ real.measurable_space,
      { apply measurable.of_comap_le, simp },
      { apply measurable_set_preimage ennreal.measurable_of_real hA } },
    { simp,
      apply @measurable_set_preimage _ _ _ _ real.measurable_space,
      { apply measurable.of_comap_le, simp },
      { apply measurable_set_preimage ennreal.measurable_of_real hB } }, },
end

lemma integral_indep {X Y : Ω → ℝ} {hX : integrable X} {hY : integrable Y}
  {hXY : integrable (X * Y)} {h : indep_fun X Y} : 𝔼[X * Y] = 𝔼[X] * 𝔼[Y] :=
begin
  have hXpm := eq_pos_sub_neg X, set Xp := pos_part ∘ X, set Xm := neg_part ∘ X,
  have hYpm := eq_pos_sub_neg Y, set Yp := pos_part ∘ Y, set Ym := neg_part ∘ Y,
  simp_rw [pi.mul_apply, hXpm, hYpm, pi.sub_apply, mul_sub, sub_mul, ← pi.mul_apply],
  rw [integral_sub, integral_sub, integral_sub, integral_sub', integral_sub', sub_mul, mul_sub, mul_sub],
  rw [integral_indep_of_pos, integral_indep_of_pos, integral_indep_of_pos, integral_indep_of_pos],
  ring,

  { intro x, simp [Xm,neg_part] },
  { intro x, simp [Ym,neg_part] },
  { sorry },
  { intro x, simp [Xp,pos_part] },
  { intro x, simp [Ym,neg_part] },
  { sorry },
  { intro x, simp [Xm,neg_part] },
  { intro x, simp [Yp,pos_part] },
  { sorry },
  { intro x, simp [Xp,pos_part] },
  { intro x, simp [Yp,pos_part] },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry }

  -- simp [integral_sub],
  -- have := @lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun Ω _ volume,
  -- have := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hX,
  -- have := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hY,
  -- have := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hXY,

  -- apply integrable.induction (λ X : Ω → ℝ, ∫ ω, (X * Y) ω = (∫ ω, X ω) * (∫ ω, Y ω)),
  -- { simp, sorry },
  -- { simp, intros f g h1 h2 h3 h4 h5, simp_rw [add_mul], rw [integral_add,integral_add,h4,h5],
  --   simp [*], ring, exact h2, exact h3, sorry, sorry },
  -- { simp, sorry },
  -- { sorry },
  -- assumption
end

lemma cov_indep {X Y : Ω → ℝ} {hX : integrable X} : indep_fun X Y → cov X Y = 0 :=
begin
  intro h, rw [cov,integral_indep,avg_recenter], ring, exact hX, sorry, sorry, sorry,
  exact indep_recenter h
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

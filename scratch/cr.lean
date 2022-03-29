/-
Ce fichier a pour but de débuter l'étude du cours d'analyse complexe de Master via LEAN.
Nous allons y étudier les premières propriétés des fonctions holomorphes.
Nous passerons le sujet des fonctions analytiques car celles-ci ont été développées dans d'autres fichiers, auquels nous pourrons faire référence.

-/

-- Importons les datas qui nous seront utiles.

import data.complex.basic -- pour travailler sur ℂ
import analysis.complex.basic -- pour travailler sur ℂ
import analysis.calculus.deriv -- pour utiliser la dérivation déjà créée de façon générale
import topology.basic
import topology.metric_space.lipschitz

def rabs : ℝ → ℝ := abs

open complex
/-
Afin de gagner en concision pour ce projet, nous allons créer le caractère "être holomorphe" pour une fonction
-/

def is_C_deriv_at (Ω : set ℂ)(f : ℂ → ℂ)(z₀ : ℂ)(ho : is_open Ω)(hz : z₀ ∈ Ω) : Prop :=
∃ (f' : ℂ), has_deriv_within_at f f' Ω z₀

-- has_deriv_at

def is_C_deriv (Ω : set ℂ)(f : ℂ → ℂ)(ho : is_open Ω) : Prop :=
∃ (f' : ℂ → ℂ), ∀ z ∈ Ω, has_deriv_at f (f' z) z

-- equiv_real_prod (to_fun : ℂ → ℝ²) (inv_fun : ℝ² → ℂ)

def realify (f : ℂ → ℂ ) : (ℝ × ℝ → ℝ × ℝ) := equiv_real_prod.to_fun ∘ f ∘ equiv_real_prod.inv_fun

lemma l1 (z w : ℂ) : (realify (has_mul.mul z) (equiv_real_prod w)) = equiv_real_prod.to_fun (z * w) := rfl

lemma l2 (z1 z2 : ℂ) : equiv_real_prod (z1 - z2) = equiv_real_prod z1 - equiv_real_prod z2 := by { refl }
lemma l3 (z1 z2 : ℂ) : equiv_real_prod (z1 - z2) = equiv_real_prod.to_fun z1 - equiv_real_prod.to_fun z2 := by { refl }

lemma l6 (z : ℂ) : nnnorm (equiv_real_prod z) ≤ nnnorm z := by {
  rw prod.nnnorm_def, simp [nnnorm], simp [norm], split,
  apply abs_re_le_abs, apply abs_im_le_abs
}

lemma l7 (z : ℂ) : nnnorm z ≤ 2 * nnnorm (equiv_real_prod z) := by {
  simp [nnnorm,norm], rw ← subtype.coe_le_coe, simp,
  transitivity rabs z.re + rabs z.im,
  exact complex.abs_le_abs_re_add_abs_im z,
  rw two_mul, apply add_le_add, apply le_max_left, apply le_max_right,
}

lemma l5 {z xy : ℂ} : ∥equiv_real_prod (z * xy)∥₊ ≤ nnnorm z * 2 * ∥equiv_real_prod xy∥₊ :=
begin
  transitivity nnnorm (z * xy), apply l6,
  simp_rw mul_assoc, rw nnnorm_mul, apply mul_le_mul le_rfl,
  apply l7, apply zero_le, apply zero_le
end

example (z : ℂ) : lipschitz_with (nnnorm z * 2) (realify (has_mul.mul z)) :=
begin
  rw [lipschitz_with], intros x y,
  set x' := equiv_real_prod.inv_fun x with h1,
  set y' := equiv_real_prod.inv_fun y with h1,
  have : x = equiv_real_prod x' := by { simp [x'] }, rw this, rw l1,
  have : y = equiv_real_prod y' := by { simp [y'] }, rw this, rw l1,
  rw [edist_eq_coe_nnnorm_sub,edist_eq_coe_nnnorm_sub,←l2,←l3],
  rw ← mul_sub,
  set xy := x' - y' with hxy, rw ←hxy,
  rw ← ennreal.coe_mul,
  apply ennreal.coe_le_coe.mpr,
  exact l5
end

-- def multiplication (z : ℂ) : (ℝ × ℝ →L[ℝ] ℝ × ℝ) := by {
--   refine ⟨_,_⟩,
--   { refine ⟨_,_,_⟩,
--     { exact realify (λ w, z * w) },
--     { intros, simp [realify], split, ring, ring },
--     { intros, simp [realify], split; ring } },
--   { simp,
--     let K : nnreal := nnnorm z,
--     suffices : lipschitz_with K (realify (has_mul.mul z)),
--       exact lipschitz_with.continuous this,

--     intros z₁ z₂,
--     simp [realify],
--     rw [edist_eq_coe_nnnorm_sub],

--     calc edist (realify (has_mul.mul z) z₁) (realify (has_mul.mul z) z₂) ≤ sorry : sorry
--     ... ≤ K edist z₁ z₂ : sorry
--   },
-- }

variables {Ω : set ℂ} {f : ℂ → ℂ} {z : ℂ}

lemma cauchy_riemann (f' : ℂ) (hf : has_deriv_at f f' z) : has_fderiv_at (realify f) (multiplication f') (equiv_real_prod.to_fun z) :=
begin
  sorry
end


-- cauchy riemann dans un domaine ouvert

-- lemme de schwarz non injectif a partir de ce qui est fait

-- attaquer la suite !

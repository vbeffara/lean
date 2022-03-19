import data.polynomial.derivative

open_locale polynomial
open polynomial

lemma iterate_derivative_eq_zero {R} [comm_semiring R] {p : R[X]} {x : ℕ} (hx : p.nat_degree < x) :
  polynomial.derivative^[x] p = 0 :=
begin
  induction h : p.nat_degree using nat.strong_induction_on with _ ih generalizing p x,
  subst h,
  obtain ⟨t, rfl⟩ := nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne',
  rw [function.iterate_succ_apply],
  by_cases hp : p.derivative = 0,
  { rw [hp, polynomial.iterate_derivative_zero] },
  have := nat_degree_derivative_lt hp,
  exact ih _ this (this.trans_le $ nat.le_of_lt_succ hx) rfl
end

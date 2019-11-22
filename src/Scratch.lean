import tactic llist
open function
set_option trace.check true

structure foo := (n : ℕ) (h : 3 ∣ n)
def f (n : foo) := n.n
lemma toto (n : ℕ) : n = n + 1 - 1 := by { norm_num }

example {n : foo} : 3 ∣ f n :=
    begin
        cases n with n h,
        -- revert h,
        rw (toto n) at h, rw (toto n),
        sorry
    end

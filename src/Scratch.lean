import tactic

class myclass (X : Type) :=
(b : X)
(c : ℕ)

structure mystructure (Y : Type) :=
(b : Y)
(c : ℕ)

#check @myclass.b -- X explicit
#check @mystructure.b -- Y implicit

def A : mystructure ℕ := ⟨4, 37⟩
instance : myclass ℤ := ⟨5, 37⟩ -- no name by default

variables (P Q : Type) (s : mystructure P) [myclass Q]
-- don't have a name for the class analogue of s!

#check A.c -- works fine
-- A has type `mystructure [something]` so `A.c *means* mystructure.c A`
-- this is the powerful dot notation. It's why `h.symm` works if `h : a = b`!
#check mystructure.c A -- even prettyprinter changes it to `A.c`

#check s.c -- works fine
-- but what are the analogues for classes?

#check myclass.c Q
#check myclass.c ℤ
-- have to do it this way because no names, but X explicit in myclass.c so it's OK

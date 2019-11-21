import tactic

@[ext] structure dumb (V : Type) := (val : V)

#check dumb.ext
#check dumb.ext_iff
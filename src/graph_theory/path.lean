import tactic
import combinatorics.simple_graph.connectivity
import graph_theory.basic graph_theory.pushforward
open relation relation.refl_trans_gen

namespace simple_graph

variables {V V' : Type*} {G G₁ G₂ : simple_graph V} {G' : simple_graph V'} {u v x y z : V}
variables {e : G.dart} {p : walk G x y} {p' : walk G y z} {p'' : walk G z u}
variables {h : G.adj y z} {h' : G.adj u x} {h'' : G.adj z v}

namespace walk

infixr ` :: ` := cons
infix  ` ++ ` := append

lemma point_of_size_0 : p.length = 0 → x = y :=
by { intro h, cases p, refl, contradiction }

lemma mem_edges (h : e ∈ darts p) : e.fst ∈ p.support ∧ e.snd ∈ p.support :=
⟨p.dart_fst_mem_support_of_mem_darts h, p.dart_snd_mem_support_of_mem_darts h⟩

lemma mem_of_edges (h : 0 < p.length) : u ∈ p.support ↔ ∃ e ∈ darts p, u ∈ dart.edge e :=
begin
  induction p with u u v w h p ih,
  { simp only [length_nil, nat.not_lt_zero] at h, contradiction },
  { clear h, cases nat.eq_zero_or_pos (length p),
    { cases p,
      simp only [darts, dart.edge, support_cons, support_nil, list.mem_cons_iff,
        list.mem_singleton, sym2.mem_iff, exists_prop, exists_eq_left],
      simp only [length_cons, nat.succ_ne_zero] at h_1, contradiction },
    { specialize ih h_1, clear h_1, simp only [dart.edge, sym2.mem_iff] at ih, split,
      { simp only [darts, dart.edge, support_cons, list.mem_cons_iff, sym2.mem_iff, exists_prop],
        intro h1, cases h1,
        { subst h1, use ⟨(u,v),h⟩, simp only [eq_self_iff_true, and_self, true_or, sym2.mem_iff] },
        { obtain ⟨e,h2,h3⟩ := ih.mp h1, exact ⟨e, or.inr h2, h3⟩ } },
      { simp only [darts, dart.edge, list.mem_cons_iff, sym2.mem_iff, support_cons,
        forall_exists_index, and_imp, forall_eq_or_imp],
        exact ⟨(λ h, or.cases_on h or.inl (λ h, by { subst h, exact or.inr (start_mem_support _) })),
        (λ e he h1, or.inr (ih.mpr ⟨e,he,h1⟩))⟩ } } }
end

lemma nodup_rev : p.support.nodup → p.reverse.support.nodup :=
by { rw (support_reverse p), exact list.nodup_reverse.mpr }

lemma nodup_concat : (append p p').support.nodup ↔
  p.support.nodup ∧ p'.support.nodup ∧ (∀ u, u ∈ p.support → u ∈ p'.support → u = y) :=
begin
  induction p with a a b c h q ih,
  { simp },
  { simp only [cons_append, support_cons, list.nodup_cons, mem_support_append_iff,
    list.mem_cons_iff, forall_eq_or_imp],
    push_neg, split,
    { rintros ⟨⟨h1,h2⟩,h3⟩, replace ih := ih.mp h3, refine ⟨⟨h1,ih.1⟩,ih.2.1,_,λ u h4 h5, _⟩,
      intro, contradiction, exact ih.2.2 u h4 h5 },
    { rintros ⟨⟨h1,h2⟩,h3,h4,h5⟩, refine ⟨⟨h1,_⟩,_⟩,
      intro h5, apply h1, rw h4 h5, exact end_mem_support _,
      refine ih.mpr ⟨h2,h3,_⟩, intros u hu h'u, exact h5 u hu h'u } }
end

def path_from_subgraph (sub : ∀ {x y}, G₁.adj x y → G₂.adj x y) :
  Π {x y : V}, walk G₁ x y → walk G₂ x y
| _ _ nil        := nil
| _ _ (cons h p) := walk.cons (sub h) (path_from_subgraph p)

@[simp] def fmap (f : G →g G') : ∀ {x y}, walk G x y → walk G' (f x) (f y)
| _ _ nil        := nil
| _ _ (cons h p) := cons (f.map_rel' h) (fmap p)

@[simp] lemma length_map {f : G →g G'} : length (fmap f p) = length p :=
by { induction p, refl, simpa }

end walk

def linked    (G : simple_graph V) := refl_trans_gen G.adj
def connected (G : simple_graph V) := ∀ x y, linked G x y

class connected_graph (G : simple_graph V) := (conn : connected G)

namespace linked
open walk

@[refl] lemma refl : linked G x x :=
refl_trans_gen.refl

@[symm] lemma symm : linked G x y → linked G y x :=
λ h, refl_trans_gen.symmetric G.symm h

@[trans] lemma trans : linked G x y → linked G y z → linked G x z :=
λ h, h.trans

lemma step : G.adj x y → linked G x y :=
refl_trans_gen.single

lemma of_cons : G.adj x y → linked G y z → linked G x z :=
λ h h', trans (step h) h'

lemma equiv : equivalence (linked G) :=
⟨@refl _ _, @symm _ _, @trans _ _⟩

lemma linked_iff : linked G x y ↔ nonempty (walk G x y) :=
begin
  split; intro h₁,
  { induction h₁ with u v h₁ h₂ h₃, use nil, cases h₃ with p, use (p ++ (cons h₂ nil)) },
  { cases h₁ with p, induction p with a a b c h p ih, refl, exact (single h).trans ih }
end

lemma linked_of_subgraph (sub : G₁ ≤ G₂) : linked G₁ x y → linked G₂ x y :=
refl_trans_gen.mono sub

lemma fmap (f : G →g G') : linked G x y → linked G' (f x) (f y) :=
refl_trans_gen.lift f (λ a b, f.map_rel)

lemma push {x y : V} {f : V → V'} : G.linked x y → (push f G).linked (f x) (f y) :=
begin
  intro h, induction h with a b h₁ h₂ ih, refl, refine ih.trans _,
  cases push.adj f h₂, rw h, exact step h
end

end linked

lemma connected_of_iso : G ≃g G' → G.connected → G'.connected :=
begin
  intros φ h₂ x' y',
  specialize h₂ (φ.symm x') (φ.symm y'),
  convert ←linked.fmap φ.to_hom h₂; apply φ.right_inv
end

end simple_graph

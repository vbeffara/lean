import graph_theory.path
variables {V V' V'': Type*}
open function

namespace simple_graph
open walk

structure path_embedding (G : simple_graph V) (G' : simple_graph V') :=
  (f        : V ↪ V')
  (df       : Π e : G.dart, G'.walk (f e.fst) (f e.snd))
  --
  (nodup    : ∀ e : G.dart, (df e).support.nodup)
  (sym      : ∀ e : G.dart, df e.symm = (df e).reverse)
  --
  (endpoint : ∀ {e x}, f x ∈ (df e).support → x ∈ e.edge)
  --
  (disjoint : ∀ {e e' z}, z ∈ (df e).support → z ∈ (df e').support →
    e.edge = e'.edge ∨ ∃ x, z = f x)

def embeds_into (G : simple_graph V) (G' : simple_graph V') := nonempty (path_embedding G G')

infix ` ≼t `:50 := embeds_into -- TODO rename as topological minor

namespace path_embedding

variables {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}
variables (F : path_embedding G G')
variables {x y z : V} {x' y' z' : V'} {p : walk G x y} {p' : walk G y z}

lemma nop {e : G.dart} : 0 < (F.df e).length :=
pos_iff_ne_zero.mpr $ λ h, G.ne_of_adj e.is_adj $ F.f.injective $ point_of_size_0 h

@[simp] def follow : Π {x y : V}, walk G x y → walk G' (F.f x) (F.f y)
| _ _ nil        := nil
| _ _ (cons h p) := F.df ⟨⟨_,_⟩,h⟩ ++ follow p

@[simp] lemma follow_append : follow F (p ++ p') = follow F p ++ follow F p' :=
by { induction p, refl, simp only [cons_append,append_assoc,p_ih,follow] }

lemma mem_follow (h₁ : 0 < p.length) (h₂ : z' ∈ (follow F p).support) :
  ∃ e ∈ darts p, z' ∈ (F.df e).support :=
begin
  induction p with u u v w h p ih, {simp at h₁, contradiction}, clear h₁,
  simp only [follow, mem_support_append_iff] at h₂, cases h₂,
  { exact ⟨⟨⟨_,_⟩, h⟩, or.inl rfl, h₂⟩ },
  { cases p,
    { refine ⟨⟨⟨_,_⟩,h⟩, or.inl rfl, _⟩, simp only [follow, support_nil, list.mem_singleton] at h₂,
      rw h₂, exact end_mem_support _ },
    { specialize ih _ h₂, simp only [length_cons, nat.succ_pos'],
      choose e h₃ h₄ using ih, exact ⟨e, or.inr h₃, h₄⟩ } }
end

lemma follow_nodup {p : walk G x y} (h : p.support.nodup) : (follow F p).support.nodup :=
begin
  induction p with u u v w h p ih,
  { simp only [follow, support_nil, list.nodup_cons, list.not_mem_nil, not_false_iff,
    list.nodup_nil, and_self] },
  { simp only [follow], simp only [support_cons, list.nodup_cons] at h, apply nodup_concat.mpr,
    refine ⟨F.nodup _, ih h.2, _⟩, rintros z h3 h4,
    cases nat.eq_zero_or_pos p.length with h5 h5,
    { cases p,
      { simp only [follow, support_nil, list.mem_singleton] at h4, exact h4 },
      { simp only [length_cons, nat.succ_ne_zero] at h5, contradiction } },
    { obtain ⟨e,h7,h8⟩ := mem_follow F h5 h4,
      cases F.disjoint h3 h8 with h9 h9,
      { exfalso, apply h.1, apply (mem_of_edges h5).mpr ⟨e,h7,_⟩, rw <-h9,
        exact sym2.mem_mk_left _ _ },
      { obtain ⟨v,_⟩ := h9, subst z, have h10 := F.endpoint h3,
        cases sym2.mem_iff.mp h10 with h10 h10,
        { subst h10, exfalso, apply h.1,
          have := F.endpoint h8, rw [dart.edge] at this, rcases e with ⟨⟨ex,ey⟩,he⟩, simp at this,
          cases this with h12 h12,
          { rw h12, exact p.dart_fst_mem_support_of_mem_darts h7 },
          { rw h12, exact p.dart_snd_mem_support_of_mem_darts h7 } },
        { rw h10 } } } }
end

lemma follow_rev {p : walk G x y} : follow F p.reverse = (follow F p).reverse :=
begin
  induction p with u u v w h p ih, refl,
  simp only [ih.symm, follow, reverse_cons, follow_append, append_nil, reverse_append],
  congr, exact F.sym ⟨⟨_,_⟩,h⟩
end

def comp (F : path_embedding G G') (F' : path_embedding G' G'') : path_embedding G G'' :=
{ f := ⟨F'.f ∘ F.f, injective.comp F'.f.inj' F.f.inj'⟩,
  df := λ e, follow F' (F.df e),
  --
  nodup := λ e, (follow_nodup F') (F.nodup _),
  sym := by { intro e, rewrite F.sym e, apply follow_rev },
  --
  endpoint := by {
    intros e x h1, obtain ⟨e',h4,h5⟩ := mem_follow F' (nop F) h1,
    exact F.endpoint ((walk.mem_of_edges (nop _)).mpr ⟨e',h4,F'.endpoint h5⟩)
  },
  --
  disjoint := by {
    intros e e' z h1 h2,
    replace h1 := mem_follow _ (nop _) h1, obtain ⟨e1,h3,h4⟩ := h1,
    replace h2 := mem_follow _ (nop _) h2, obtain ⟨e2,h5,h6⟩ := h2,
    have h7 := F'.disjoint h4 h6, cases h7,
    { left, clear h4 h6, replace h3 := walk.mem_edges h3, replace h5 := walk.mem_edges h5,
      replace h5 : e1.fst ∈ (F.df e').support ∧ e1.snd ∈ (F.df e').support :=
      by { cases (dart_edge_eq_iff e1 e2).mp h7; subst e1,
        exact h5, simp only [dart.symm], exact h5.symm },
      cases F.disjoint h3.1 h5.1 with h10 h10, exact h10, obtain ⟨x,h10⟩ := h10, rw h10 at h3 h5,
      cases F.disjoint h3.2 h5.2 with h11 h11, exact h11, obtain ⟨y,h11⟩ := h11, rw h11 at h3 h5,
      have h12 := F.endpoint h3.1, have h13 := F.endpoint h3.2,
      have h14 := F.endpoint h5.1, have h15 := F.endpoint h5.2,
      have h16 : x ≠ y := by { intro h, apply G'.ne_of_adj e1.is_adj, convert congr_arg F.f h },
      exact sym2.eq_of_ne_mem h16 h12 h13 h14 h15 },
    { obtain ⟨y,h8⟩ := h7, subst z, replace h4 := F'.endpoint h4, replace h6 := F'.endpoint h6,
      replace h3 := walk.mem_edges h3, replace h5 := walk.mem_edges h5,
      replace h3 : y ∈ (F.df e).support, by { simp only [dart.edge, sym2.mem_iff] at h4,
        rcases e1 with ⟨⟨e1x,e1y⟩,e1h⟩, simp at h4,
        cases h4; subst h4, exact h3.1, exact h3.2 },
      replace h5 : y ∈ (F.df e').support, by { simp only [dart.edge, sym2.mem_iff] at h6,
        rcases e2 with ⟨⟨e2x,e2y⟩,e2h⟩, simp at h6,
        cases h6; subst h6, exact h5.1, exact h5.2 },
      cases F.disjoint h3 h5 with h9 h9,
      { left, exact h9 },
      { obtain ⟨x,h9⟩ := h9, subst h9, right, use x, refl } } } }

theorem trans : embeds_into G G' → embeds_into G' G'' → embeds_into G G'' :=
λ ⟨F⟩ ⟨F'⟩, ⟨comp F F'⟩

def from_hom (f : G →g G') (inj : injective f) : path_embedding G G' :=
{ f := ⟨f, inj⟩,
  df := λ e, cons (f.map_rel' e.is_adj) nil,
  nodup := λ e, by {
    simp only [support_cons, embedding.coe_fn_mk, support_nil, rel_hom.coe_fn_to_fun,
              list.nodup_cons, list.mem_singleton, list.not_mem_nil, not_false_iff,
              list.nodup_nil, and_true],
    exact G'.ne_of_adj (f.map_rel' e.is_adj) },
  sym := λ e, by {
    simp only [dart.symm, reverse_cons, reverse_nil, nil_append, rel_hom.coe_fn_to_fun,
              embedding.coe_fn_mk, eq_self_iff_true, heq_iff_eq, and_self], simp },
  --
  endpoint := λ e x h, by {
    simp only [embedding.coe_fn_mk, support_cons, support_nil, rel_hom.coe_fn_to_fun,
              list.mem_cons_iff, list.mem_singleton] at h,
    simp only [dart.edge, sym2.mem_iff], rcases e with ⟨⟨ex,ey⟩,eh⟩, simp,
    cases h, { left, exact inj h }, { right, exact inj h } },
  --
  disjoint := by { intros e e' z h₁ h₂, right, cases h₁, subst h₁, exact ⟨e.fst,rfl⟩,
    cases h₁, subst h₁, exact ⟨e.snd,rfl⟩, cases h₁ } }

end path_embedding
end simple_graph

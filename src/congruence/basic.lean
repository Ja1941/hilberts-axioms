import order.angle

/--A Hilbert plane extends incidence order geometry. It contains two binary relations, seg
congruence and ang congruence. Intuitionally, they correspond to lengths of two segs and
radians of two angs equal. They subject to the following axioms.
C1 : Given a seg and two distinct points `a` `b`, we find uniquely find a point `c` on the
same side with `b` to `a` such that seg `a` `c` is congruent to the seg. This axiom
corresponds to I.2 and I.3 in Elements.
C2 : seg congruence is an equivalence relation.
C3 : Two segs are congruent if their two parts are congruent.
C4 : Given a nontrivial ang `α` and points `a` `b`, we can find `c` such that `∠c a b`
     is congruent to `α`. `c` is uniquely defined given one side of line `a` `b`.
C5 : ang congruence is an equivalent relation.
C6 : Two triangs are congruent by SAS. This axiom corresponds to I.4 in Elements.
-/
class hilbert_plane extends incidence_order_geometry :=
(seg_congr : seg → seg → Prop)
(C1 : ∀ {a b : pts} {l : seg}, seg_nontrivial l → a ≠ b → ∃ c : pts, same_side_pt a b c ∧
seg_congr l (a-ₛc) ∧ ∀ x : pts, same_side_pt a b x → seg_congr l (a-ₛx) → x = c)
(C2 : (∀ {s₁ s₂ s₃ : seg}, (seg_congr s₁ s₂ → seg_congr s₁ s₃ → seg_congr s₂ s₃))
∧ ∀ (s : seg),  seg_congr s s)
(C3 : ∀ {a b c d e f: pts}, between a b c → between d e f
  → seg_congr (a-ₛb) (d-ₛe) → seg_congr (b-ₛc) (e-ₛf) → seg_congr (a-ₛc) (d-ₛf))
(ang_congr : ang → ang → Prop)
(C4 : ∀ {α : ang} {a b p : pts}, ang_nontrivial α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, ang_congr α (∠c a b) ∧ same_side_line (a-ₗb) c p
∧ ∀ x : pts, same_side_line (a-ₗb) c x → ang_congr α (∠x a b) → x ∈ (a-ᵣc).inside)
(C5 : (∀ {α β γ : ang}, (ang_congr α β → ang_congr α γ → ang_congr β γ))
∧ ∀ (α : ang), ang_congr α α)
(C6 : ∀ {a b c d e f : pts}, noncol a b c → noncol d e f → seg_congr (a-ₛb) (d-ₛe)
→ seg_congr (a-ₛc) (d-ₛf) → ang_congr (∠b a c) (∠e d f)
→ seg_congr (b-ₛc) (e-ₛf) ∧ ang_congr (∠a b c) (∠d e f) ∧ ang_congr (∠a c b) (∠d f e))

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

notation a`≅ₛ`b := seg_congr a b

lemma extend_congr_seg {s : seg} {a b : pts} (hs : seg_nontrivial s) (hab : a ≠ b) :
∃ c : pts, same_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
∧ ∀ x : pts, same_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c := C1 hs hab

lemma extend_congr_seg' {s : seg}{a b : pts}  (hs : seg_nontrivial s) (hab : a ≠ b) :
∃ c : pts, diff_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
∧ ∀ x : pts, diff_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c :=
begin
  cases between_extend hab.symm with c hbac,
  rcases extend_congr_seg hs (between_neq hbac).2.2 with ⟨d, hacd, hd, hu⟩,
  use d, split,
  exact diff_side_same_side_pt (diff_side_pt_symm (between_diff_side_pt.1 hbac)) hacd,
  split, exact hd,
  intros x habx hx,
  refine hu x _ hx,
  exact diff_side_pt_cancel (between_diff_side_pt.1 hbac) habx
end

lemma seg_congr_refl (s : seg) : s ≅ₛ s := C2.2 s

lemma seg_congr_symm {s₁ s₂ : seg} :
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₁) := λ h, C2.1 h (seg_congr_refl s₁)

lemma seg_congr_trans {s₁ s₂ s₃ : seg} : 
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₃) → (s₁ ≅ₛ s₃) := λ h₁ h₂, C2.1 (seg_congr_symm h₁) h₂

lemma seg_unique_same_side {o a b : pts} (hab : same_side_pt o a b) :
((o-ₛa) ≅ₛ (o-ₛb)) → a = b :=
begin
  intro he,
  have hoa := (same_side_pt_neq hab).1.symm,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 hoa) hoa with ⟨d, hoad, hd, hu⟩,
  rw hu b hab he, refine hu _ _ _,
  exact same_side_pt_refl hoa, exact seg_congr_refl _
end

lemma congr_seg_add {a b c d e f: pts} : between a b c → between d e f
→ ((a-ₛb) ≅ₛ (d-ₛe)) → ((b-ₛc) ≅ₛ (e-ₛf)) → ((a-ₛc) ≅ₛ (d-ₛf)) :=
λh₁ h₂ h₃ h₄, C3 h₁ h₂ h₃ h₄

lemma congr_seg_sub {a b c d e f : pts} (habc : between a b c) (hdef : same_side_pt d e f)
(habde : (a-ₛb)≅ₛ(d-ₛe)) (hacdf : (a-ₛc)≅ₛ(d-ₛf)) : between d e f ∧ ((b-ₛc)≅ₛ(e-ₛf)) :=
begin
  rcases between_extend (same_side_pt_neq hdef).1.symm with ⟨x, hdex⟩,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 (between_neq habc).2.2)
    (between_neq hdex).2.2 with ⟨f', hexf', hbcef', -⟩,
  have hdef' : between d e f',
    rcases between_col hdex with ⟨l, hl, hdl, hel, hxl⟩,
    rcases hexf'.2 with ⟨m, hm, hem, hxm, hf'm⟩,
    rw (two_pt_one_line hm hl (same_side_pt_neq hexf').1 ⟨hxm, hem⟩ ⟨hxl, hel⟩) at hf'm,
    rw [between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hf'm⟩
      (between_neq hdex).1 (same_side_pt_neq hexf').2],
    rw [between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hxl⟩
      (same_side_pt_neq hdef).1.symm (same_side_pt_neq hexf').1] at hdex,
    intro hedf', exact hdex (same_side_pt_trans hedf' (same_side_pt_symm hexf')),
  have hacdf' := C3 habc hdef' habde hbcef',
  have hff' : f = f',
    rcases extend_congr_seg (seg_nontrivial_iff_neq.2 (between_neq habc).2.1)
      (between_neq hdef').1 with ⟨f'', -, -, hf''⟩,
    rw [hf'' f hdef hacdf, hf'' f' (between_same_side_pt.mp hdef').1 hacdf'],
  rw hff', exact ⟨hdef', hbcef'⟩
end

notation a`≅ₐ`b := ang_congr a b

lemma ang_congr_refl (α : ang) : α ≅ₐ α := C5.2 α

lemma ang_congr_symm {α β : ang} :
(α ≅ₐ β) → (β ≅ₐ α) := λ h, C5.1 h (ang_congr_refl α)

lemma ang_congr_trans {α β γ : ang} : 
(α ≅ₐ β) → (β ≅ₐ γ) → (α ≅ₐ γ) := λ h₁ h₂, C5.1 (ang_congr_symm h₁) h₂

lemma extend_congr_ang {α : ang} {a b p : pts} :
ang_nontrivial α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, ang_congr α (∠ c a b) ∧ same_side_line (a-ₗb) c p
∧ ∀ x : pts, same_side_line (a-ₗb) c x → ang_congr α (∠x a b) → x ∈ (a-ᵣc).inside := C4

lemma extend_congr_ang' {α : ang} {a b p : pts} :
ang_nontrivial α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, ang_congr α (∠ c a b) ∧ diff_side_line (a-ₗb) c p :=
begin
  intros hα hab hp,
  have hpa : p ≠ a,
    intro hpa, rw hpa at hp, exact hp (pt_left_in_line a b),
  cases between_extend hpa with q hpaq,
  have haq := (between_neq hpaq).2.2,
  have haqb := col_noncol (col12 (between_col hpaq))
    (noncol_in13' hab hp) haq,
  have := (diff_side_pt_line (between_diff_side_pt.1 hpaq)).2.2.2
    (line_in_lines hab) ⟨pt_left_in_line a b, hp, noncol_in13 haqb⟩,
  rcases extend_congr_ang hα hab (noncol_in13 haqb) with ⟨c, he, hcq, hu⟩,
  use c, split, exact he,
  exact diff_side_line_symm (diff_same_side_line (line_in_lines hab) this (same_side_line_symm hcq))
end

/--A triang consists of three vertices. Note that it is defined to be ordered. -/
structure triang := (v1 : pts) (v2 : pts) (v3 : pts)

/--Two triangs are congruent if their sides and angs are equal in order. -/
def tri_congr (t₁ t₂ : triang) : Prop :=
((t₁.v1-ₛt₁.v2) ≅ₛ (t₂.v1-ₛt₂.v2)) ∧ ((t₁.v1-ₛt₁.v3) ≅ₛ (t₂.v1-ₛt₂.v3))
∧ ((t₁.v2-ₛt₁.v3) ≅ₛ (t₂.v2-ₛt₂.v3))
∧ ((∠t₁.v2 t₁.v1 t₁.v3 ≅ₐ ∠t₂.v2 t₂.v1 t₂.v3)
∧ (∠t₁.v1 t₁.v2 t₁.v3 ≅ₐ ∠t₂.v1 t₂.v2 t₂.v3)
∧ (∠t₁.v1 t₁.v3 t₁.v2 ≅ₐ ∠t₂.v1 t₂.v3 t₂.v2))

notation a`≅ₜ`b := tri_congr a b

lemma tri_congr_refl (t : triang) : t ≅ₜ t :=
⟨seg_congr_refl _, seg_congr_refl _, seg_congr_refl _,
ang_congr_refl _, ang_congr_refl _, ang_congr_refl _⟩

lemma tri_congr_symm {t₁ t₂ : triang} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₁) :=
λh, ⟨seg_congr_symm h.1, seg_congr_symm h.2.1, seg_congr_symm h.2.2.1,
ang_congr_symm h.2.2.2.1, ang_congr_symm h.2.2.2.2.1, ang_congr_symm h.2.2.2.2.2⟩

lemma tri_congr_trans {t₁ t₂ t₃ : triang} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₃) → (t₁ ≅ₜ t₃) :=
λh₁ h₂, ⟨seg_congr_trans h₁.1 h₂.1, seg_congr_trans h₁.2.1 h₂.2.1,
seg_congr_trans h₁.2.2.1 h₂.2.2.1, ang_congr_trans h₁.2.2.2.1 h₂.2.2.2.1,
ang_congr_trans h₁.2.2.2.2.1 h₂.2.2.2.2.1, ang_congr_trans h₁.2.2.2.2.2 h₂.2.2.2.2.2⟩

/--Define a triang with three vertices. -/
def three_pt_triang (a b c : pts) : triang := ⟨a, b, c⟩

notation `Δ` := three_pt_triang

lemma three_pt_triang_v1 (a b c : pts) : (Δ a b c).v1 = a := rfl

lemma three_pt_triang_v2 (a b c : pts) : (Δ a b c).v2 = b := rfl

lemma three_pt_triang_v3 (a b c : pts) : (Δ a b c).v3 = c := rfl

lemma tri_congr12 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b a c) ≅ₜ (Δ b' a' c')) :=
begin
  unfold tri_congr,
  rw [three_pt_triang_v1, three_pt_triang_v2, three_pt_triang_v3,
    three_pt_triang_v1, three_pt_triang_v2, three_pt_triang_v3],
  rw [seg_symm, seg_symm a' b'],
  rw [ang_symm a c b, ang_symm a' c' b'],
  tauto
end

lemma tri_congr13 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c b a) ≅ₜ (Δ c' b' a')) :=
begin
  unfold tri_congr,
  rw [three_pt_triang_v1, three_pt_triang_v2, three_pt_triang_v3,
    three_pt_triang_v1, three_pt_triang_v2, three_pt_triang_v3],
  rw [seg_symm, seg_symm a' b'],
  rw [seg_symm a c, seg_symm a' c'],
  rw [seg_symm b c, seg_symm b' c'],
  rw [ang_symm b a c, ang_symm b' a' c'],
  rw [ang_symm a c b, ang_symm a' c' b'],
  rw [ang_symm a b c, ang_symm a' b' c'],
  tauto
end

lemma tri_congr23 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ a c b) ≅ₜ (Δ a' c' b')) :=
begin
  unfold tri_congr,
  rw [three_pt_triang_v1, three_pt_triang_v1, three_pt_triang_v2, three_pt_triang_v2,
  three_pt_triang_v3, three_pt_triang_v3, three_pt_triang_v1, three_pt_triang_v1,
  three_pt_triang_v2, three_pt_triang_v2, three_pt_triang_v3, three_pt_triang_v3],
  rw [seg_symm, seg_symm a' b'],
  rw [seg_symm a c, seg_symm a' c'],
  rw [seg_symm b c, seg_symm b' c'],
  rw [ang_symm b a c, ang_symm b' a' c'],
  rw [ang_symm a c b, ang_symm a' c' b'],
  rw [ang_symm a b c, ang_symm a' b' c'],
  tauto
end

lemma tri_congr123 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b c a) ≅ₜ (Δ b' c' a')) := λh, tri_congr23 (tri_congr12 h)

lemma tri_congr132 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c a b) ≅ₜ (Δ c' a' b')) := λh, tri_congr23 (tri_congr13 h)

lemma tri_congr_side {a b c a' b' c': pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
((a-ₛb) ≅ₛ (a'-ₛb')) ∧ ((a-ₛc) ≅ₛ (a'-ₛc')) ∧ ((b-ₛc) ≅ₛ (b'-ₛc')) :=
begin
  unfold tri_congr three_pt_triang at h, simp at h,
  exact ⟨h.1, h.2.1, h.2.2.1⟩
end

lemma tri_congr_ang {a b c a' b' c': pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
(∠ b a c ≅ₐ ∠ b' a' c') ∧ (∠ a b c ≅ₐ ∠ a' b' c') ∧ (∠ a c b ≅ₐ ∠ a' c' b') :=
begin
  unfold tri_congr three_pt_triang at h, simp at h,
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
end

lemma SAS {ABC DEF : triang}
(h₁ : noncol ABC.v1 ABC.v2 ABC.v3) (h₂ : noncol DEF.v1 DEF.v2 DEF.v3)
(hs₁ : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2)) (hs₂ : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3))
(ha : (∠ABC.v2 ABC.v1 ABC.v3 ≅ₐ ∠DEF.v2 DEF.v1 DEF.v3)) : ABC ≅ₜ DEF :=
⟨hs₁, hs₂, (C6 h₁ h₂ hs₁ hs₂ ha).1, ha, (C6 h₁ h₂ hs₁ hs₂ ha).2.1, (C6 h₁ h₂ hs₁ hs₂ ha).2.2⟩

lemma supplementary_congr {α α' β β' : ang}
(h : supplementary α α') (h' : supplementary β β') : (α ≅ₐ β) → (α' ≅ₐ β') :=
begin
  rcases h.1 with ⟨a, b, c, d, hα, hα', hcad⟩,
  rcases h'.1 with ⟨a', b', c', d', hβ, hβ', hc'a'd'⟩,
  intro hbac,
  rw [hα, hα'] at h, rw [hβ, hβ'] at h', rw [hα, hβ] at hbac, rw [hα', hβ'],
  have ha'b' := (noncol_neq (ang_nontrivial_iff_noncol.1 h'.2.1)).1.symm,
  have ha'c' := (noncol_neq (ang_nontrivial_iff_noncol.1 h'.2.1)).2.2,
  have ha'd' := (noncol_neq (ang_nontrivial_iff_noncol.1 h'.2.2)).2.2,
  have hab := (noncol_neq (ang_nontrivial_iff_noncol.1 h.2.1)).1.symm,
  have hac := (between_neq hcad).1.symm,
  have had := (between_neq hcad).2.2,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 hab) ha'b'
    with ⟨x, ha'b'x, haba'b', -⟩,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 hac) ha'c'
    with ⟨y, ha'b'y, haca'c', -⟩,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 had) ha'd'
    with ⟨z, ha'b'z, hada'd', -⟩,
  have : (∠b' a' c') = (∠x a' y),
    unfold three_pt_ang, simp,
    rw [(two_pt_ray_eq_same_side_pt_pt.1 ha'b'x).1, (two_pt_ray_eq_same_side_pt_pt.1 ha'b'y).1],
  rw this at h' hbac,
  have : (∠b' a' d') = (∠x a' z),
    unfold three_pt_ang, simp,
    rw [(two_pt_ray_eq_same_side_pt_pt.1 ha'b'x).1, (two_pt_ray_eq_same_side_pt_pt.1 ha'b'z).1],
  rw this at h', rw this,
  rename [x b', y c', z d'],
  have h₁ : ((Δ a b c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triang; simp,
    rintros ⟨l, hl, habcl⟩, apply ang_nontrivial_iff_noncol.1 h.2.1, use l, tauto,
    rintros ⟨l, hl, habcl'⟩, apply ang_nontrivial_iff_noncol.1 h'.2.1, use l, tauto,
    exact haba'b', exact haca'c', exact hbac,
  have hcad := between_diff_side_pt.2 (between_diff_side_pt.1
    (three_pt_ang_supplementary.1 h).1),
  have hc'a'd' := between_diff_side_pt.2 (between_diff_side_pt.1
    (three_pt_ang_supplementary.1 h').1),
  have h₂ : ((Δ c b d) ≅ₜ (Δ c' b' d')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol23 (col_noncol (between_col hcad)
      (noncol13 (ang_nontrivial_iff_noncol.1 h.2.1)) (between_neq hcad).2.1),
    exact noncol23 (col_noncol (between_col hc'a'd')
      (noncol13 (ang_nontrivial_iff_noncol.1 h'.2.1)) (between_neq hc'a'd').2.1),
    rw [seg_symm, seg_symm c' _],
    exact (tri_congr_side h₁).2.2,
    refine congr_seg_add hcad hc'a'd' _ _,
    rw [seg_symm, seg_symm c' _], exact haca'c',
    exact hada'd',
    rw ←ang_eq_same_side b (between_same_side_pt.1 hcad).1,
    rw ←ang_eq_same_side b' (between_same_side_pt.1 hc'a'd').1,
    rw [ang_symm, ang_symm b' _ _],
    exact (tri_congr_ang h₁).2.2,
  have h₃ : ((Δ d b a) ≅ₜ (Δ d' b' a')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol12 (noncol23 (ang_nontrivial_iff_noncol.1 h.2.2)),
    exact noncol12 (noncol23 (ang_nontrivial_iff_noncol.1 h'.2.2)),
    rw [seg_symm, seg_symm d' _], exact (tri_congr_side h₂).2.2,
    rw [seg_symm, seg_symm d' _], exact hada'd',
    rw ←ang_eq_same_side b (between_same_side_pt.1 hcad).2,
    rw ←ang_eq_same_side b' (between_same_side_pt.1 hc'a'd').2,
    rw [ang_symm, ang_symm b' _ _], exact (tri_congr_ang h₂).2.2,
  rw [ang_symm, ang_symm b' _ _], exact (tri_congr_ang h₃).2.2
end

lemma ang_congr_same_side_unique {a b c d : pts} (h : ∠ b a c ≅ₐ ∠b a d)
(hbac : noncol b a c) : same_side_line (b-ₗa) c d → same_side_pt a c d :=
begin
  have hab := (noncol_neq hbac).1.symm,
  intro hcd,
  have hbad : noncol b a d,
    rintros ⟨l, hl, hbl, hal, hdl⟩,
    rw two_pt_one_line hl (line_in_lines hab.symm) hab ⟨hal, hbl⟩
      ⟨pt_right_in_line b a, pt_left_in_line b a⟩ at hdl,
    exact (same_side_line_not_in hcd).2 hdl,
  rcases extend_congr_ang (ang_nontrivial_iff_noncol.2 (noncol13 hbac)) hab
    (by {rw line_symm, exact noncol_in12 hbac}) with ⟨p, hpab, hpc, hu⟩,
  have h₁ := hu c hpc (ang_congr_refl _),
  rw line_symm at hcd, rw [ang_symm, ang_symm _ _ d] at h,
  have h₂ := hu d (same_side_line_trans (line_in_lines hab) hpc hcd) h,
  unfold two_pt_ray at h₁ h₂, simp at h₁ h₂,
  cases h₁ with hf h₁, exact absurd hf (noncol_neq hbac).2.2.symm,
  cases h₂ with hf h₂, exact absurd hf (noncol_neq hbad).2.2.symm,
  exact same_side_pt_trans (same_side_pt_symm h₁) h₂
end

private lemma congr_ang_add_prep1 {α : ang} {s : seg} (hs : seg_nontrivial s)
{b a c : C.pts} (hab : a ≠ b) (hbac : (∠ b a c) ≅ₐ α) :
∃ b' : C.pts, ((∠ b' a c) ≅ₐ α) ∧ ((a-ₛb') ≅ₛ s) ∧ same_side_pt a b b' :=
begin
  rcases extend_congr_seg hs hab with ⟨b', habb', hs, h⟩, use b',
  have : ∠ c a b = ∠ c a b', from ang_eq_same_side c habb',
  rw [ang_symm, ←this, ang_symm], exact ⟨hbac, seg_congr_symm hs, habb'⟩
end

private lemma congr_ang_add_prep2 {a b c d a' b' c' d' : C.pts}
(hd : inside_ang d (∠ b a c)) (hb'c' : diff_side_line (a'-ₗd') b' c') (ha'd' : a' ≠ d')
(hbad : ∠ b a d ≅ₐ ∠ b' a' d') (hdac : ∠ d a c ≅ₐ ∠ d' a' c') : noncol b' a' c' :=
begin
  have hbac := ang_nontrivial_iff_noncol.1 (inside_ang_nontrivial hd),
  rw inside_three_pt_ang at hd,
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  have had : a ≠ d,
    intro hf, rw hf at hd,
    unfold same_side_line at hd, apply hd.1,
    exact ⟨d, pt_left_in_line d b, by {unfold two_pt_seg, simp}⟩,
  intro hf, rcases hf with ⟨l, hl, hb'l, ha'l, hc'l⟩,
  have ha'b' : a' ≠ b',
    intro hf, rw hf at hb'c', exact hb'c'.2.1 (pt_left_in_line b' d'),
  have ha'c' : a' ≠ c',
    intro hf, rw hf at hb'c', exact hb'c'.2.2 (pt_left_in_line c' d'),
  cases (line_separation ⟨l, hl, ha'l, hb'l, hc'l⟩ ha'b'.symm ha'c'.symm).1 with h h,
  have : same_side_line (a'-ₗd') b' c',
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact ha'd'.symm,
    rw line_symm, exact hb'c'.2.1,
    left, exact h,
    intro hf, rw hf at hb'c', exact hb'c'.2.2 (pt_left_in_line a' d'),
  rw ←not_diff_side_line at this, exact this hb'c',
  exact hb'c'.2.1, exact hb'c'.2.2,
  have h₁ : supplementary (∠ d' a' b') (∠ d' a' c'),
    rw [three_pt_ang_supplementary, between_diff_side_pt],
    split, exact h,
    split, rintros ⟨m, hm, hd'm, ha'm, hb'm⟩,
    rw two_pt_one_line hm (line_in_lines ha'd') ha'd' ⟨ha'm, hd'm⟩
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hb'm,
    exact hb'c'.2.1 hb'm,
    rintros ⟨m, hm, hd'm, ha'm, hc'm⟩,
    rw two_pt_one_line hm (line_in_lines ha'd') ha'd' ⟨ha'm, hd'm⟩
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hc'm,
    exact hb'c'.2.2 hc'm,
  cases (between_extend hab.symm) with x hbax,
  have h₂ : supplementary (∠ d a b) (∠ d a x),
    rw three_pt_ang_supplementary, split, exact hbax,
    have : noncol d a b,
      rintros ⟨m, hm, hdm, ham, hbm⟩,
      rw two_pt_one_line hm (line_in_lines hab) hab ⟨ham, hbm⟩
        ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hdm,
      exact (same_side_line_not_in hd.1).2 hdm,
    split, exact this,
    rintros ⟨m, hm, hdm, ham, hxm⟩,
    have hax := (between_neq hbax).2.2,
    rw two_pt_one_line hm (line_in_lines hab) hax at hdm,
    exact this ⟨(a-ₗb), line_in_lines hab, hdm, pt_left_in_line a b, pt_right_in_line a b⟩,
    exact ⟨ham, hxm⟩, split, exact pt_left_in_line a b,
    rw line_symm, apply ray_in_line b a, left, exact (between_same_side_pt.1 hbax).1,
  have hdax : ((∠ d a x) ≅ₐ (∠ d a c)),
    refine ang_congr_trans _ (ang_congr_symm hdac),
    apply supplementary_congr h₂ h₁, rw [ang_symm, ang_symm d' _ _],
    exact hbad,
  rw three_pt_ang_supplementary at h₂,
  have key : same_side_pt a x c,
    refine ang_congr_same_side_unique hdax _ _, exact h₂.2.2,
    have hbx : diff_side_line (a-ₗd) b x,
      rw between_diff_side_pt at hbax, replace hbax := diff_side_pt_line hbax,
      refine hbax.2.2.2 _ _, exact line_in_lines had,
      split, exact pt_left_in_line a d,
      split, intro hf,
      exact h₂.2.1 ⟨(a-ₗd), line_in_lines had,
        pt_right_in_line a d, pt_left_in_line a d, hf⟩,
      intro hf,
      exact h₂.2.2 ⟨(a-ₗd), line_in_lines had, pt_right_in_line a d, pt_left_in_line a d, hf⟩,
    have hbc : diff_side_line (a-ₗd) b c,
      cases crossbar (inside_three_pt_ang.2 hd) with x hx, use x,
      exact ⟨(ray_in_line a d) hx.1, hx.2⟩,
      split, intro hf,
      exact h₂.2.1 ⟨(a-ₗd), line_in_lines had, pt_right_in_line a d, pt_left_in_line a d, hf⟩,
      intro hf, apply (same_side_line_not_in hd.2).2,
      rw two_pt_one_line (line_in_lines hac) (line_in_lines had) hac, exact pt_right_in_line a d,
      exact ⟨pt_left_in_line a c, pt_right_in_line a c⟩, exact ⟨pt_left_in_line a d, hf⟩,
    rw line_symm,
    exact diff_side_line_cancel (line_in_lines had) (diff_side_line_symm hbx) hbc,
  rcases between_col hbax with ⟨m, hm, hbm, ham, hxm⟩,
  rcases key.2 with ⟨n, hn, han, hxn, hcn⟩,
  have hax := (between_neq h₂.1).2.2,
  rw two_pt_one_line hn hm hax ⟨han, hxn⟩ ⟨ham, hxm⟩ at hcn,
  exact hbac ⟨m, hm, hbm, ham, hcn⟩
end

lemma congr_ang_add {a b c d a' b' c' d' : C.pts}
(hd : inside_ang d (∠ b a c)) (hb'c' : diff_side_line (a'-ₗd') b' c') (ha'd' : a' ≠ d')
(h₁ : ∠ b a d ≅ₐ ∠ b' a' d') (h₂ : ∠ d a c ≅ₐ ∠ d' a' c') :
inside_ang d' (∠ b' a' c') ∧ (∠ b a c ≅ₐ ∠ b' a' c') :=
begin
  have hbac := inside_ang_nontrivial hd, rw ang_nontrivial_iff_noncol at hbac,
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  have hbc := (noncol_neq hbac).2.1,
  have hb'a'c' := congr_ang_add_prep2 hd hb'c' ha'd' h₁ h₂,
  have wlog : ∃ p : pts, inside_ang p (∠ b a c) ∧ ∠ b a d = ∠ b a p
    ∧ ∠ d a c = ∠ p a c ∧ between b p c,
    cases crossbar hd with p hp, use p,
    rw inside_three_pt_ang at hd,
    by_cases hdp : d = p,
      rw ←hdp at hp, unfold two_pt_seg at hp, simp at hp, rcases hp.2 with hp | hp | hp,
      rw hp at hd, exact absurd (pt_right_in_line a b) (same_side_line_not_in hd.1).2,
      rw hp at hd, exact absurd (pt_right_in_line a c) (same_side_line_not_in hd.2).2,
      rw ←hdp, exact ⟨inside_three_pt_ang.2 hd, rfl, rfl, hp⟩,
    have had : a ≠ d,
      have := same_side_line_not_in hd.1,
      intro had, rw ←had at this, exact this.2 (pt_left_in_line a b),
    have hap : a ≠ p,
      intro hap, rw ←hap at hp, have : a ∈ (b-ₗc), from (seg_in_line b c) hp.2,
      exact hbac ⟨b-ₗc, line_in_lines hbc, pt_left_in_line b c, this, pt_right_in_line b c⟩,
    have ha : a ∈ ↑(line d p),
      have ha := pt_left_in_line a d,
      rw two_pt_one_line (line_in_lines had) (line_in_lines hdp) hdp
        ⟨pt_right_in_line a d, (ray_in_line a d) hp.1⟩
        ⟨pt_left_in_line d p, pt_right_in_line d p⟩ at ha,
      exact ha,
    have hadp : same_side_pt a d p,
      cases hp.1 with h h, exact h, simp at h, exact absurd h.symm hap,
    have : same_side_line (a-ₗb) d p,
      rintros ⟨x, hx⟩,
      have : (a-ₗb) ≠ (d-ₗp),
        intro hf, have := pt_left_in_line d p, rw ←hf at this,
        exact (same_side_line_not_in hd.1).2 this,
      have hax := two_line_one_pt (line_in_lines hab) (line_in_lines hdp)
        this (pt_left_in_line a b) ha hx.1 ((seg_in_line d p) hx.2),
      rw ←hax at hx,
      unfold two_pt_seg at hx, simp at hx, rcases hx.2 with hx | hx | hx,
      exact had hx, exact hap hx,
      rw [between_diff_side_pt, ←not_same_side_pt hadp.2 had.symm hap.symm] at hx,
      exact hx hadp,
    split, rw inside_three_pt_ang, split,
    exact same_side_line_trans (line_in_lines hab) hd.1 this,
    have : same_side_line (a-ₗc) d p,
      rintros ⟨x, hx⟩,
      have : (a-ₗc) ≠ (d-ₗp),
        intro hf, have := pt_left_in_line d p, rw ←hf at this,
        exact (same_side_line_not_in hd.2).2 this,
      have hax := two_line_one_pt (line_in_lines hac)
        (line_in_lines hdp) this (pt_left_in_line a c) ha hx.1 ((seg_in_line d p) hx.2),
      rw ←hax at hx,
      have : same_side_pt a d p,
        cases hp.1 with h h, exact h, simp at h, exact absurd h.symm hap,
      unfold two_pt_seg at hx, simp at hx, rcases hx.2 with hx | hx | hx,
      exact had hx, exact hap hx,
      rw [between_diff_side_pt, ←not_same_side_pt this.2 had.symm hap.symm] at hx,
      exact hx this,
    exact same_side_line_trans (line_in_lines hac) hd.2 this,
    split, exact ang_eq_same_side b hadp,
    split, rw [ang_symm, ang_eq_same_side c hadp, ang_symm],
    unfold two_pt_seg at hp, simp at hp, rcases hp.2 with hpb | hpc | hp,
    rw hpb at hp, have := pt_right_in_line a d,
    rw two_pt_one_line (line_in_lines had) (line_in_lines hab) hab ⟨pt_left_in_line a d,
      (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at this,
    exact absurd this (same_side_line_not_in hd.1).2,
    rw hpc at hp, have := pt_right_in_line a d,
    rw two_pt_one_line (line_in_lines had) (line_in_lines hac) hac ⟨pt_left_in_line a d,
      (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at this,
    exact absurd this (same_side_line_not_in hd.2).2,
    exact hp,
  rcases wlog with ⟨p, hp, hp₁, hp₂, hbpc⟩, rw hp₁ at h₁, rw hp₂ at h₂,
  clear hd hp₁ hp₂ d,
  rw inside_three_pt_ang at hp,
  rename [p d, hp hd, hbpc hbdc],
  have had : a ≠ d,
    intro had, rw ←had at hd,
    exact (same_side_line_not_in hd.1).2 (pt_left_in_line a b),
  have ha'b' := (noncol_neq hb'a'c').1.symm,
  have ha'c' := (noncol_neq hb'a'c').2.2,
  rcases congr_ang_add_prep1 (seg_nontrivial_iff_neq.2 hab) ha'b'
    (ang_congr_refl (∠ b' a' d')) with ⟨b'', hb''a'd', ha'b''ab, ha'b'b''⟩,
  rcases congr_ang_add_prep1 (seg_nontrivial_iff_neq.2 had) ha'd'
    (ang_congr_refl (∠ d' a' b'')) with ⟨d'', hd''a'b', ha'd''ad, ha'd'd''⟩,
  rcases congr_ang_add_prep1 (seg_nontrivial_iff_neq.2 hac) ha'c'
    (ang_congr_refl (∠ c' a' d')) with ⟨c'', hc''a'd', ha'c''ac, ha'c'c''⟩,
  have ha'b'' := (same_side_pt_neq ha'b'b'').2.symm,
  have ha'd'' := (same_side_pt_neq ha'd'd'').2.symm,
  have ha'c'' := (same_side_pt_neq ha'c'c'').2.symm,
  have ha'd''b'' : noncol a' d'' b'',
    rintros ⟨l, hl, ha'l, hd''l, hb''l⟩,
    rcases ha'b'b''.2 with ⟨m, hm, ha'm, hb'm, hb''m⟩,
    rcases ha'd'd''.2 with ⟨n, hn, ha'n, hd'n, hd''n⟩,
    rw two_pt_one_line hm hl ha'b'' ⟨ha'm, hb''m⟩ ⟨ha'l, hb''l⟩ at hb'm,
    rw two_pt_one_line hl hn ha'd'' ⟨ha'l, hd''l⟩ ⟨ha'n, hd''n⟩ at hb'm,
    rw two_pt_one_line hn (line_in_lines ha'd') ha'd' ⟨ha'n, hd'n⟩
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hb'm,
    exact hb'c'.2.1 hb'm,
  have ha'c'' := (same_side_pt_neq ha'c'c'').2.symm,
  have ha'd'' := (same_side_pt_neq ha'd'd'').2.symm,
  have ha'd' := (same_side_pt_neq ha'd'd'').1.symm,
  have ha'd''c'' : noncol a' d'' c'',
    rintros ⟨l, hl, ha'l, hd''l, hc''l⟩,
    rcases ha'c'c''.2 with ⟨m, hm, ha'm, hc'm, hc''m⟩,
    rcases ha'd'd''.2 with ⟨n, hn, ha'n, hd'n, hd''n⟩,
    rw two_pt_one_line hm hl ha'c'' ⟨ha'm, hc''m⟩ ⟨ha'l, hc''l⟩ at hc'm,
    rw two_pt_one_line hl hn ha'd'' ⟨ha'l, hd''l⟩ ⟨ha'n, hd''n⟩ at hc'm,
    rw two_pt_one_line hn (line_in_lines ha'd') ha'd' ⟨ha'n, hd'n⟩
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hc'm,
    exact hb'c'.2.2 hc'm,
  replace h₁ : (∠ b a d ≅ₐ ∠ b'' a' d''),
    apply ang_congr_trans (ang_congr_trans h₁ (ang_congr_symm hb''a'd')), rw ang_symm,
    apply ang_congr_trans (ang_congr_symm hd''a'b'), rw ang_symm, exact ang_congr_refl _,
  replace h₂ : (∠ d a c ≅ₐ ∠ d'' a' c''),
    apply ang_congr_trans h₂, rw ang_symm, apply ang_congr_trans (ang_congr_symm hc''a'd'),
    rw [ang_eq_same_side c'' ha'd'd'', ang_symm], exact ang_congr_refl _,
  have habd : ((Δ a b d) ≅ₜ (Δ a' b'' d'')),
    apply SAS; unfold three_pt_triang; simp,
    intro habd, exact (same_side_line_not_in hd.1).2 (col_in12 habd hab),
    exact noncol23 ha'd''b'',
    exact seg_congr_symm ha'b''ab, exact seg_congr_symm ha'd''ad, exact h₁,
  have hacd : ((Δ a c d) ≅ₜ (Δ a' c'' d'')),
    apply SAS; unfold three_pt_triang; simp,
    intro hacd, exact (same_side_line_not_in hd.2).2 (col_in12 hacd hac),
    exact noncol23 ha'd''c'',
    exact seg_congr_symm ha'c''ac, exact seg_congr_symm ha'd''ad,
    rw ang_symm, apply ang_congr_trans h₂, rw ang_symm, exact ang_congr_refl _,
  have hb''d'' : b'' ≠ d'',
    intro hb''d'', rw ←hb''d'' at ha'd'd'',
    rcases (same_side_pt_trans ha'b'b'' (same_side_pt_symm ha'd'd'')).2
      with ⟨l, hl, ha'l, hb'l, hd'l⟩,
    have ha'd' := (same_side_pt_neq ha'd'd'').1.symm,
    rw two_pt_one_line hl (line_in_lines ha'd') ha'd' ⟨ha'l, hd'l⟩
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hb'l,
    exact hb'c'.2.1 hb'l,
  cases between_extend hb''d'' with x hb''xd'',
  have ha'd''x : noncol a' d'' x,
    rintros ⟨l, hl, ha'l, hd''l, hxl⟩,
    rcases between_col hb''xd'' with ⟨m, hm, hb''m, hd''m, hxm⟩,
    have hd''x := (between_neq hb''xd'').2.2,
    rw two_pt_one_line hm hl hd''x ⟨hd''m, hxm⟩ ⟨hd''l, hxl⟩ at hb''m,
    exact ha'd''b'' ⟨l, hl, ha'l, hd''l, hb''m⟩,
  have hb''a'c'' : noncol b'' a' c'',
    rintros ⟨l, hl, hb''l, ha'l, hc''l⟩,
    rcases ha'b'b''.2 with ⟨m, hm, ha'm, hb'm, hb''m⟩,
    rcases ha'c'c''.2 with ⟨n, hn, ha'n, hc'n, hc''n⟩,
    rw two_pt_one_line hn hl ha'c'' ⟨ha'n, hc''n⟩ ⟨ha'l, hc''l⟩ at hc'n,
    rw two_pt_one_line hl hm ha'b'' ⟨ha'l, hb''l⟩ ⟨ha'm, hb''m⟩ at hc'n,
    exact hb'a'c' ⟨m, hm, hb'm, ha'm, hc'n⟩,
  have key : (∠ a' d'' x ≅ₐ ∠ a' d'' c''),
    refine ang_congr_trans _ (tri_congr_ang hacd).2.2,
    have h₁ : supplementary (∠ a d b) (∠ a d c),
      rw three_pt_ang_supplementary, split, exact hbdc,
      split, rintros ⟨l, hl, hal, hdl, hbl⟩,
      rw two_pt_one_line hl (line_in_lines hab) hab ⟨hal, hbl⟩
        ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hdl,
      exact (same_side_line_not_in hd.1).2 hdl,
      rintros ⟨l, hl, hal, hdl, hcl⟩,
      rw two_pt_one_line hl (line_in_lines hac) hac ⟨hal, hcl⟩
        ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at hdl,
      exact (same_side_line_not_in hd.2).2 hdl,
    have h₂ : supplementary (∠ a' d'' x) (∠ a' d'' b''),
      rw three_pt_ang_supplementary, split, rw between_symm, exact hb''xd'',
      exact ⟨ha'd''x, ha'd''b''⟩,
    rw supplementary_symm at h₂, apply ang_congr_symm,
    exact supplementary_congr h₁ h₂ (tri_congr_ang habd).2.2,
  have hx : x ∉ (a'-ₗd''),
    intro hx, exact ha'd''x ⟨(a'-ₗd''), line_in_lines ha'd'',
      pt_left_in_line a' d'', pt_right_in_line a' d'', hx⟩,
  have : same_side_line (a'-ₗd'') x c'',
    have hb'b'' : same_side_line (a'-ₗd'') b'' b',
      rw line_symm, refine t_shape_ray ha'd''.symm _ _ _ _,
      intro hf, exact ha'd''b'' ⟨(d''-ₗa'), line_in_lines ha'd''.symm,
        pt_right_in_line d'' a', pt_left_in_line d'' a', hf⟩,
      unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'', exact ha'b'.symm,
    have hc'c'' : same_side_line (a'-ₗd'') c'' c',
      rw line_symm, refine t_shape_ray ha'd''.symm _ _ _ _,
      intro hf, exact ha'd''c'' ⟨(d''-ₗa'), line_in_lines ha'd''.symm,
        pt_right_in_line d'' a', pt_left_in_line d'' a', hf⟩,
      unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c'', exact ha'c'.symm,
    have hb'' : b'' ∉ (a'-ₗd''),
      from λhf, ha'd''b'' ⟨(a'-ₗd''), line_in_lines ha'd'',
        pt_left_in_line a' d'', pt_right_in_line a' d'', hf⟩,
    have hx : x ∉ (a'-ₗd''),
      from λhf, ha'd''x ⟨(a'-ₗd''), line_in_lines ha'd'',
        pt_left_in_line a' d'', pt_right_in_line a' d'', hf⟩,
    have hxb'' : diff_side_line (a'-ₗd'') x b'',
    apply diff_side_line_symm,
    rw between_diff_side_pt at hb''xd'', replace hb''xd'' := diff_side_pt_line hb''xd'',
    apply hb''xd''.2.2.2 (line_in_lines ha'd''),
    exact ⟨pt_right_in_line a' d'', hb'', hx⟩,
  have hxb' := diff_same_side_line (line_in_lines ha'd'') hxb'' hb'b'',
  have : (a'-ₗd') = (a'-ₗd''),
    have : d' ∈ (a'-ₗd''),
      apply ray_in_line a' d'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact two_pt_one_line (line_in_lines ha'd') (line_in_lines ha'd'') ha'd'
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ ⟨pt_left_in_line a' d'', this⟩,
    rw this at hb'c',
  have hxc' := diff_side_line_cancel (line_in_lines ha'd'') hxb' hb'c',
  exact same_side_line_trans (line_in_lines ha'd'') hxc' (same_side_line_symm hc'c''),
  have hd''xc'' := ang_congr_same_side_unique key ha'd''x this,
  have hb''d''c'' := between_same_side_pt_between hb''xd'' hd''xc'',
  have hcab : ((Δ c a b) ≅ₜ (Δ c'' a' b'')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol13 hbac, exact noncol13 hb''a'c'',
    rw [seg_symm, seg_symm c'' _], exact seg_congr_symm ha'c''ac,
    rw between_symm at hb''d''c'' hbdc, refine congr_seg_add hbdc hb''d''c'' _ _,
    exact (tri_congr_side hacd).2.2,
    rw [seg_symm, seg_symm d'' _], exact (tri_congr_side habd).2.2,
    rw between_same_side_pt at hbdc hb''d''c'',
    rw [ang_eq_same_side a hbdc.2, ang_eq_same_side a' hb''d''c''.2],
    exact (tri_congr_ang hacd).2.1,
  have : (∠ b' a' c') = (∠ b'' a' c''),
    rw [ang_eq_same_side b' ha'c'c'', ang_symm, ang_eq_same_side c'' ha'b'b'', ang_symm],
  split, rotate,
  rw [this, ang_symm, ang_symm b'' _ _], exact (tri_congr_ang hcab).2.1,
  have hc'' : c'' ∉ (a'-ₗb''), from λhc'', hb''a'c'' ⟨(a'-ₗb''), line_in_lines ha'b'',
    pt_right_in_line a' b'', pt_left_in_line a' b'', hc''⟩,
  have hb'' : b'' ∉ (a'-ₗc''), from λhb'', hb''a'c'' ⟨(a'-ₗc''), line_in_lines ha'c'',
    hb'', pt_left_in_line a' c'', pt_right_in_line a' c''⟩,
  have hd'' : same_side_line (a'-ₗb'') c'' d'' ∧ same_side_line (a'-ₗc'') b'' d'',
    split,
    exact t_shape_ray ha'b'' hc'' d'' (by {unfold two_pt_ray, simp, right, exact same_side_pt_symm
      (between_same_side_pt.1 hb''d''c'').1}) (between_neq hb''d''c'').1.symm,
    exact t_shape_ray ha'c'' hb'' d'' (by {unfold two_pt_ray, simp, right,
      exact (between_same_side_pt.1 hb''d''c'').2}) (between_neq hb''d''c'').2.2,
  rw inside_three_pt_ang, split,
  rw two_pt_one_line (line_in_lines ha'b') (line_in_lines ha'b''),
  have hc'c'' : same_side_line (a'-ₗb'') c' c'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'b''.symm _ _ _ _,
    intro hf, exact hb''a'c'' ⟨(b''-ₗa'), line_in_lines ha'b''.symm,
      pt_left_in_line b'' a', pt_right_in_line b'' a', hf⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c'',
    exact ha'c'.symm,
  have hd'd'' : same_side_line (a'-ₗb'') d' d'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'b''.symm _ _ _ _,
    rw line_symm, intro hf,
    exact ha'd''b'' ⟨(a'-ₗb''), line_in_lines ha'b'', pt_left_in_line a' b'', hf,
      pt_right_in_line a' b''⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact ha'd'.symm,
  exact same_side_line_trans (line_in_lines ha'b'') (same_side_line_trans
    (line_in_lines ha'b'') hc'c'' hd''.1) (same_side_line_symm hd'd''),
  exact ha'b', exact ⟨pt_left_in_line a' b', pt_right_in_line a' b'⟩,
  split, exact pt_left_in_line a' b'',
  apply ray_in_line a' b'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'',
  rw two_pt_one_line (line_in_lines ha'c') (line_in_lines ha'c''),
  have hb'b'' : same_side_line (a'-ₗc'') b' b'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'c''.symm _ _ _ _,
    intro hf, exact hb''a'c'' ⟨(c''-ₗa'), line_in_lines ha'c''.symm, hf,
      pt_right_in_line c'' a', pt_left_in_line c'' a'⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'',
    exact ha'b'.symm,
  have hd'd'' : same_side_line (a'-ₗc'') d' d'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'c''.symm _ _ _ _,intro hf,
    exact ha'd''c'' ⟨(c''-ₗa'), line_in_lines ha'c''.symm,
      pt_right_in_line c'' a', hf, pt_left_in_line c'' a'⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact ha'd'.symm,
  exact same_side_line_trans (line_in_lines ha'c'')
    (same_side_line_trans (line_in_lines ha'c'') hb'b'' hd''.2) (same_side_line_symm hd'd''),
  exact ha'c', exact ⟨pt_left_in_line a' c', pt_right_in_line a' c'⟩,
  split, exact pt_left_in_line a' c'',
  apply ray_in_line a' c'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c''
end

lemma congr_ang_sub {a b c d a' b' c' d' : C.pts}
(hd : inside_ang d (∠ b a c)) (h : same_side_line (a'-ₗb') d' c')
(ha'b' : a' ≠ b') (h₁ : ∠ b a c ≅ₐ ∠ b' a' c') (h₂ : ∠ b a d ≅ₐ ∠ b' a' d') :
inside_ang d' (∠ b' a' c') ∧ (∠ d a c ≅ₐ ∠ d' a' c') :=
begin
  have hbac := inside_ang_nontrivial hd, rw ang_nontrivial_iff_noncol at hbac,
  have hb'd' : b' ≠ d',
    intro hb'd', rw ←hb'd' at h, exact (same_side_line_not_in h).1 (pt_right_in_line a' b'), 
  have ha'd' : a' ≠ d',
    intro hb'd', rw ←hb'd' at h, exact (same_side_line_not_in h).1 (pt_left_in_line a' b'), 
  cases between_extend hb'd' with x hb'xd',
  have hb'x : diff_side_line (a'-ₗd') b' x,
    rw between_diff_side_pt at hb'xd', replace hb'xd' := diff_side_pt_line hb'xd',
    refine hb'xd'.2.2.2 _ _, exact line_in_lines ha'd',
    split, exact pt_right_in_line a' d',
    have :  b' ∉ ↑(line a' d'),
      intro hf, rw two_pt_one_line (line_in_lines ha'b') (line_in_lines ha'd') ha'b'
        ⟨pt_left_in_line a' b', pt_right_in_line a' b'⟩ ⟨pt_left_in_line a' d', hf⟩ at h,
      exact (same_side_line_not_in h).1 (pt_right_in_line a' d'),
    split, exact this,
    rcases hb'xd'.1 with ⟨l, hl, hd'l, hb'l, hxl⟩,
    intro hf, rw two_pt_one_line hl (line_in_lines ha'd') hb'xd'.2.2.1 ⟨hd'l, hxl⟩
      ⟨pt_right_in_line a' d', hf⟩ at hb'l,
    exact this hb'l,
  have hdac : ang_nontrivial (∠ d a c),
    rw ang_nontrivial_iff_noncol, intro hdac,
    exact (same_side_line_not_in (inside_three_pt_ang.1 hd).2).2
      (col_in23 hdac (noncol_neq hbac).2.2),
  rcases extend_congr_ang hdac ha'd' hb'x.2.2 with ⟨c'', hdac, hc''x, -⟩,
  rw ang_symm c'' _ _ at hdac,
  have hb'c'' : diff_side_line (a'-ₗd') b' c'',
    apply diff_same_side_line (line_in_lines ha'd') hb'x,
    exact same_side_line_symm hc''x,
  have key := congr_ang_add hd hb'c'' ha'd' h₂ hdac,
  have hc'c'' : same_side_pt a' c' c'',
    apply same_side_pt_symm,
    have hb'a'c'' := ang_nontrivial_iff_noncol.1 (inside_ang_nontrivial key.1),
    rw inside_three_pt_ang at key,
    refine ang_congr_same_side_unique (ang_congr_symm (ang_congr_trans
      (ang_congr_symm h₁) key.2)) _ _,
    exact hb'a'c'',
    rw line_symm, exact same_side_line_trans (line_in_lines ha'b') key.1.1 h,
  rw [ang_eq_same_side d' hc'c'', ang_eq_same_side b' hc'c''],
  exact ⟨key.1, hdac⟩
end

/--I.15 in Elements -/
lemma vertical_ang_congr {a b a' b' o : pts} (haob : noncol a o b) :
between a o a' → between b o b' → (∠ a o b ≅ₐ ∠ a' o b') :=
begin
  intros haoa' hbob',
  rcases (between_col haoa') with ⟨l, hl, hal, hol, ha'l⟩,
  rcases (between_col hbob') with ⟨m, hm, hbm, hom, hb'm⟩,
  have h₁ : supplementary (∠ a o b) (∠ a o b'),
    rw three_pt_ang_supplementary, split, exact hbob',
    split, exact haob,
    rintros ⟨n, hn, han, hon, hb'n⟩,
    rw two_pt_one_line hm hn (between_neq hbob').2.2 ⟨hom, hb'm⟩ ⟨hon, hb'n⟩ at hbm,
    exact haob ⟨n, hn, han, hon, hbm⟩,
  have h₂ : supplementary (∠ b' o a) (∠ b' o a'),
    rw three_pt_ang_supplementary, split, exact haoa',
    split, rintros ⟨n, hn, hb'n, hon, han⟩,
    rw two_pt_one_line hm hn (between_neq hbob').2.2 ⟨hom, hb'm⟩ ⟨hon, hb'n⟩ at hbm,
    exact haob ⟨n, hn, han, hon, hbm⟩,
    rintro ⟨n, hn, hb'n, hon, ha'n⟩,
    rw two_pt_one_line hn hl (between_neq haoa').2.2 ⟨hon, ha'n⟩ ⟨hol, ha'l⟩ at hb'n,
    rw two_pt_one_line hm hl (between_neq hbob').2.2 ⟨hom, hb'm⟩ ⟨hol, hb'n⟩ at hbm,
    exact haob ⟨l, hl, hal, hol, hbm⟩,
  rw supplementary_symm at h₁, rw ang_symm a' _ _,
  apply supplementary_congr h₁ h₂, rw ang_symm, exact ang_congr_refl _
end

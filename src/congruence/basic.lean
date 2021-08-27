/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import order.angle

/-!
# Congruence of segments, angles and triangles

This file extends incidence order geometry and defines congruence of segments and angles
to make a Hilbert plane, and then formalises supplementary angles and congruence of triangles.

## Main definitions

* `hilbert_plane` is a class extended `incidence_order_geometry` and defines congruence of `seg`
  and `ang` based on some axioms.

* `triang` is a structure consisting of the three vertices in order.

* `tri_congr` means two triangles are congruence i.e. their segments and angles are congruent.

* `supplementary` means two angles "add" to 180°.

## References

* See [Geometry: Euclid and Beyond]

-/

/--A Hilbert plane extends incidence order geometry. It contains two binary relations, seg
congruence and ang congruence. Intuitionally, they correspond to lengths of two segs and
radians of two angs equal. They subject to the following axioms.
C1 : Given a seg and two distinct points `a` `b`, we find uniquely find a point `c` on the
same side with `b` to `a` such that seg `a` `c` is congruent to the seg. This axiom
corresponds to I.2 and I.3 in Elements.
C2 : seg congruence is an equivalence relation.
C3 : Two segs are congruent if their two parts are congruent.
C4 : Given a proper ang `α` and points `a` `b`, we can find `c` such that `∠c a b`
     is congruent to `α`. `c` is uniquely defined given one side of line `a` `b`.
C5 : ang congruence is an equivalent relation.
C6 : Two triangs are congruent by SAS. This axiom corresponds to I.4 in Elements.
-/
class hilbert_plane extends incidence_order_geometry :=
(seg_congr : seg → seg → Prop)
(C1 : ∀ {a b : pts} {l : seg}, seg_proper l → a ≠ b → ∃ c : pts, same_side_pt a b c ∧
seg_congr l (a-ₛc) ∧ ∀ x : pts, same_side_pt a b x → seg_congr l (a-ₛx) → x = c)
(C2 : (∀ {s₁ s₂ s₃ : seg}, (seg_congr s₁ s₂ → seg_congr s₁ s₃ → seg_congr s₂ s₃))
∧ ∀ (s : seg),  seg_congr s s)
(C3 : ∀ {a b c d e f: pts}, between a b c → between d e f
  → seg_congr (a-ₛb) (d-ₛe) → seg_congr (b-ₛc) (e-ₛf) → seg_congr (a-ₛc) (d-ₛf))
(ang_congr : ang → ang → Prop)
(C4 : ∀ {α : ang} {a b p : pts}, ang_proper α → a ≠ b → p ∉ (a-ₗb)
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

lemma extend_congr_seg {s : seg} {a b : pts} (hs : seg_proper s) (hab : a ≠ b) :
∃ c : pts, same_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
∧ ∀ x : pts, same_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c := C1 hs hab

lemma extend_congr_seg' {s : seg} {a b : pts} (hs : seg_proper s) (hab : a ≠ b) :
∃ c : pts, diff_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
∧ ∀ x : pts, diff_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c :=
begin
  cases between_extend hab.symm with c hbac,
  rcases extend_congr_seg hs (between_neq hbac).2.2 with ⟨d, hacd, hd, hu⟩,
  use d, split,
  exact diff_same_side_pt (diff_side_pt_symm (between_diff_side_pt.1 hbac)) hacd,
  split, exact hd,
  { intros x habx hx,
    apply hu x _ hx,
    exact diff_side_pt_cancel (between_diff_side_pt.1 hbac) habx }
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
  rcases extend_congr_seg (seg_proper_iff_neq.2 hoa) hoa with ⟨d, hoad, hd, hu⟩,
  rw hu b hab he,
  exact hu a (same_side_pt_refl hoa) (seg_congr_refl _)
end

lemma congr_seg_add {a b c d e f: pts} : between a b c → between d e f
→ ((a-ₛb) ≅ₛ (d-ₛe)) → ((b-ₛc) ≅ₛ (e-ₛf)) → ((a-ₛc) ≅ₛ (d-ₛf)) :=
λh₁ h₂ h₃ h₄, C3 h₁ h₂ h₃ h₄

lemma congr_seg_sub {a b c d e f : pts} (habc : between a b c) (hdef : same_side_pt d e f)
(habde : (a-ₛb)≅ₛ(d-ₛe)) (hacdf : (a-ₛc)≅ₛ(d-ₛf)) : between d e f ∧ ((b-ₛc)≅ₛ(e-ₛf)) :=
begin
  have hbc := (between_neq habc).2.2,
  have hed := (same_side_pt_neq hdef).1,
  rcases extend_congr_seg' (seg_proper_iff_neq.2 hbc) hed with ⟨f', hdef', hbcef', -⟩,
  rw ←between_diff_side_pt at hdef',
  suffices : f = f',
    rw this, exact ⟨hdef', hbcef'⟩,
  apply seg_unique_same_side,
  exact same_side_pt_trans (same_side_pt_symm hdef) (between_same_side_pt.1 hdef').1,
  apply seg_congr_trans (seg_congr_symm hacdf),
  exact congr_seg_add habc hdef' habde hbcef'
end

notation a`≅ₐ`b := ang_congr a b

lemma ang_congr_refl (α : ang) : α ≅ₐ α := C5.2 α

lemma ang_congr_symm {α β : ang} :
(α ≅ₐ β) → (β ≅ₐ α) := λ h, C5.1 h (ang_congr_refl α)

lemma ang_congr_trans {α β γ : ang} : 
(α ≅ₐ β) → (β ≅ₐ γ) → (α ≅ₐ γ) := λ h₁ h₂, C5.1 (ang_congr_symm h₁) h₂

lemma extend_congr_ang {α : ang} {a b p : pts} :
ang_proper α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, ang_congr α (∠ c a b) ∧ same_side_line (a-ₗb) c p
∧ ∀ x : pts, same_side_line (a-ₗb) c x → ang_congr α (∠x a b) → x ∈ (a-ᵣc).inside := C4

lemma extend_congr_ang' {α : ang} {a b p : pts} :
ang_proper α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, ang_congr α (∠ c a b) ∧ diff_side_line (a-ₗb) c p :=
begin
  intros hα hab hp,
  have hpa : p ≠ a,
    intro hpa, rw hpa at hp, exact hp (pt_left_in_line a b),
  cases between_extend hpa with q hpaq,
  have haq := (between_neq hpaq).2.2,
  have haqb := col_noncol (col12 (between_col hpaq))
    (noncol_in13' hab hp) haq,
  have := (diff_side_pt_line (between_diff_side_pt.1 hpaq))
    (line_in_lines hab) (pt_left_in_line a b) hp (noncol_in13 haqb),
  rcases extend_congr_ang hα hab (noncol_in13 haqb) with ⟨c, he, hcq, hu⟩,
  use c, split, exact he,
  exact diff_side_line_symm (diff_same_side_line (line_in_lines hab) this (same_side_line_symm hcq))
end

lemma ang_unique_same_side {o a b c : pts} (hoa : o ≠ a) (hbc : same_side_line (o-ₗa) b c)
(hoaboac : ∠ o a b ≅ₐ ∠ o a c) : same_side_pt a b c :=
begin
  have hoab := (same_side_line_noncol hbc hoa).1,
  rw line_symm at hbc,
  rcases extend_congr_ang (ang_proper_iff_noncol.2 hoab) hoa.symm (same_side_line_notin hbc).1
    with ⟨x, hoaboax, hxb, hu⟩,
  rw ang_symm x a o at hoaboax, rw ang_symm at hu,
  rw [ang_symm, ang_symm o a c] at hoaboac,
  have hb := hu b hxb (ang_congr_refl _),
  have hc := hu c (same_side_line_trans (line_in_lines hoa.symm) hxb hbc) hoaboac,
  have hba := (noncol_neq hoab).2.2.symm,
  have hca := (noncol_neq (same_side_line_noncol hbc hoa.symm).2).2.1.symm,
  exact same_side_pt_trans (same_side_pt_symm (ray_in_neq hba hb)) (ray_in_neq hca hc)
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

lemma tri_congr_seg {a b c a' b' c': pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
((a-ₛb) ≅ₛ (a'-ₛb')) ∧ ((a-ₛc) ≅ₛ (a'-ₛc')) ∧ ((b-ₛc) ≅ₛ (b'-ₛc')) :=
begin
  unfold tri_congr three_pt_triang at h, simp at h,
  exact ⟨h.1, h.2.1, h.2.2.1⟩
end

lemma tri_congr_ang {a b c a' b' c': pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
(∠ a b c ≅ₐ ∠ a' b' c') ∧ (∠ b a c ≅ₐ ∠ b' a' c') ∧ (∠ a c b ≅ₐ ∠ a' c' b') :=
begin
  unfold tri_congr three_pt_triang at h, simp at h,
  exact ⟨h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩
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
  intro hbacb'a'c',
  rw [hα, hα'] at h, rw [hβ, hβ'] at h',
  rw [hα, hβ] at hbacb'a'c', rw [hα', hβ'],
  have hac := (between_neq hcad).1.symm,
  have hbac := ang_proper_iff_noncol.1 h.2.1,
  have hbad := ang_proper_iff_noncol.1 h.2.2,
  have hab := (noncol_neq hbac).1.symm,
  have had := (noncol_neq hbad).2.2,
  have hcd := (between_neq hcad).2.1,
  have hb'a'c' := ang_proper_iff_noncol.1 h'.2.1,
  have hb'a'd' := ang_proper_iff_noncol.1 h'.2.2,
  have ha'b' := (noncol_neq hb'a'c').1.symm,
  have ha'c' := (noncol_neq hb'a'c').2.2,
  have ha'd' := (noncol_neq hb'a'd').2.2,
  have hab := (noncol_neq (ang_proper_iff_noncol.1 h.2.1)).1.symm,
  rcases extend_congr_seg (seg_proper_iff_neq.2 hac) ha'c' with ⟨c'', ha'c'', haca'c', -⟩,
  rcases extend_congr_seg (seg_proper_iff_neq.2 hab) ha'b' with ⟨b'', ha'b'', haba'b', -⟩,
  rcases extend_congr_seg (seg_proper_iff_neq.2 had) ha'd' with ⟨d'', ha'd'', hada'd', -⟩,
  rw [ang_eq_same_side_pt b' ha'c'', ang_symm b' a' c'', ang_eq_same_side_pt c'' ha'b''] at hbacb'a'c' h',
  rw [ang_eq_same_side_pt b' ha'd'', ang_symm b' a' d'', ang_eq_same_side_pt d'' ha'b''],
  rw [ang_eq_same_side_pt b' ha'd'', ang_symm b' a' d'', ang_eq_same_side_pt d'' ha'b''] at h',
  replace hc'a'd' : between c'' a' d'',
    rw between_diff_side_pt,
    exact diff_same_side_pt (diff_same_side_pt (between_diff_side_pt.1 hc'a'd') ha'c'') ha'd'',
  clear hα hα' hβ hβ' hb'a'c' hb'a'd' ha'b' ha'c' ha'd' ha'c'' ha'b'' ha'd'' b' c' d',
  rename [c'' c', b'' b', d'' d'],
  have hc'a'b' := ang_proper_iff_noncol.1 h'.2.1,
  have hd'a'b' := ang_proper_iff_noncol.1 h'.2.2,
  have hc'd' := (between_neq hc'a'd').2.1,
  rw ang_symm c' a' b' at hbacb'a'c',
  have h₁ : ((Δ a b c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol12 hbac, exact noncol123 hc'a'b',
    exact haba'b', exact haca'c', exact hbacb'a'c',
  have h₂ : ((Δ c b d) ≅ₜ (Δ c' b' d')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol23 (col_noncol (between_col hcad) (noncol13 hbac) hcd),
    exact noncol23 (col_noncol (between_col hc'a'd') hc'a'b' hc'd'),
    rw [seg_symm, seg_symm c' b'], exact (tri_congr_seg h₁).2.2,
    { apply congr_seg_add hcad hc'a'd' _ hada'd',
      rw [seg_symm, seg_symm c' a'], exact haca'c' },
    { rw [←ang_eq_same_side_pt b (between_same_side_pt.1 hcad).1,
        ←ang_eq_same_side_pt b' (between_same_side_pt.1 hc'a'd').1, ang_symm, ang_symm b' c' a'],
      exact (tri_congr_ang h₁).2.2 },
  have h₃ : ((Δ d a b) ≅ₜ (Δ d' a' b')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol13 hbad, exact hd'a'b',
    rw [seg_symm, seg_symm d' a'], exact hada'd',
    rw [seg_symm, seg_symm d' b'], exact (tri_congr_seg h₂).2.2,
    { rw [ang_symm, ←ang_eq_same_side_pt b (between_same_side_pt.1 hcad).2, ang_symm,
        ang_symm a' d' b', ←ang_eq_same_side_pt b' (between_same_side_pt.1 hc'a'd').2,
        ang_symm b' d' c'],
      exact (tri_congr_ang h₂).2.2 },
  rw ang_symm, exact (tri_congr_ang h₃).1
end

lemma congr_ang_add {a b c d a' b' c' d' : C.pts}
(hd : inside_ang d (∠ b a c)) (hb'c' : diff_side_line (a'-ₗd') b' c') (ha'd' : a' ≠ d')
(hbadb'a'd' : ∠ b a d ≅ₐ ∠ b' a' d') (hdacd'a'c' : ∠ d a c ≅ₐ ∠ d' a' c') :
inside_ang d' (∠ b' a' c') ∧ (∠ b a c ≅ₐ ∠ b' a' c') :=
begin
  have hbac := inside_ang_proper hd, rw ang_proper_iff_noncol at hbac,
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  have := diff_side_line_noncol hb'c' ha'd',
  have ha'b' := (noncol_neq (diff_side_line_noncol hb'c' ha'd').1).2.1,
  have ha'c' := (noncol_neq (diff_side_line_noncol hb'c' ha'd').2).2.1,
  cases crossbar hd with e he,
  have hda : e ≠ a,
    intro hf, rw hf at he, exact noncol_in13 hbac ((seg_in_line b c) he.2),
  have hdb : e ≠ b,
    intro hf, rw hf at he, apply ((same_side_line_noncol (inside_three_pt_ang.1 hd).1) hab).2,
    exact col_in13' ((ray_in_line a d) he.1),
  have hdc : e ≠ c,
    intro hf, rw hf at he, apply ((same_side_line_noncol (inside_three_pt_ang.1 hd).2) hac).2,
    exact col_in13' ((ray_in_line a d) he.1),
  have hbdc := seg_in_neq hdb hdc he.2,
  have hade := ray_in_neq hda he.1,
  replace hd := ray_inside_ang hd hade,
  rw ang_eq_same_side_pt b hade at hbadb'a'd',
  rw [ang_symm, ang_eq_same_side_pt c hade, ang_symm] at hdacd'a'c',
  clear he hade d, rename [e d],
  rw inside_three_pt_ang at hd,
  have habd := (same_side_line_noncol hd.1 hab).2,
  have hacd := (same_side_line_noncol hd.2 hac).2,
  have had := (noncol_neq habd).2.1,
  rcases extend_congr_seg (seg_proper_iff_neq.2 hac) ha'c' with ⟨c'', ha'c'c'', haca'c', -⟩,
  rcases extend_congr_seg (seg_proper_iff_neq.2 hab) ha'b' with ⟨b'', ha'b'b'', haba'b', -⟩,
  rcases extend_congr_seg (seg_proper_iff_neq.2 had) ha'd' with ⟨d'', ha'd'd'', hada'd', -⟩,
  have ha'd'' := (same_side_pt_neq ha'd'd'').2.symm,
  rw two_pt_one_line (line_in_lines ha'd') (line_in_lines ha'd'') ha'd' (pt_left_in_line a' d')
    (pt_right_in_line a' d') (pt_left_in_line a' d'') (col_in13 ha'd'd''.2 ha'd'') at hb'c',
  replace hb'c' := diff_side_line_symm (ray_diff_side_line ha'd'' hb'c' ha'b'b''),
  replace hb'c' := diff_side_line_symm (ray_diff_side_line ha'd'' hb'c' ha'c'c''),
  rw [ang_eq_same_side_pt b' ha'd'd'', ang_symm b' a' d'', ang_eq_same_side_pt d'' ha'b'b'',
    ang_symm d'' a' b''] at hbadb'a'd',
  rw [ang_eq_same_side_pt d' ha'c'c'', ang_symm d' a' c'', ang_eq_same_side_pt c'' ha'd'd'',
    ang_symm c'' a' d''] at hdacd'a'c',
  rw [ang_eq_same_side_pt b' ha'c'c'', ang_symm, ang_eq_same_side_pt c'' ha'b'b'', ang_symm],
  suffices : inside_ang d'' (∠ b'' a' c'') ∧ (∠ b a c≅ₐ∠ b'' a' c''),
    from ⟨ray_inside_ang this.1 (same_side_pt_symm ha'd'd''), this.2⟩,
  clear this ha'b' ha'c' ha'd' ha'c'c'' ha'b'b'' ha'd'd'' b' c' d',
  rename [b'' b', c'' c', d'' d', ha'd'' ha'd'],
  have ha'd'b' := (diff_side_line_noncol hb'c' ha'd').1,
  have ha'd'c' := (diff_side_line_noncol hb'c' ha'd').2,
  have h₁ : ((Δ a b d) ≅ₜ (Δ a' b' d')),
    apply SAS; unfold three_pt_triang; simp,
    exact habd, exact noncol23 ha'd'b',
    exact haba'b', exact hada'd', exact hbadb'a'd',
  have h₂ : ((Δ a d c) ≅ₜ (Δ a' d' c')),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol23 hacd, exact ha'd'c',
    exact hada'd', exact haca'c', exact hdacd'a'c',
  have hb'd' := (noncol_neq ha'd'b').2.2.symm,
  cases between_extend hb'd' with e' hb'd'e',
  have hb'e' := (between_neq hb'd'e').2.1,
  have hd'e' := (between_neq hb'd'e').2.2,
  have hb'e'a' := col_noncol (between_col hb'd'e') (noncol13 ha'd'b') hb'e',
  have hd'e'a' := col_noncol (col12 (between_col hb'd'e')) (noncol123 ha'd'b') hd'e',
  have hd'e'c' : same_side_pt d' e' c',
    apply ang_unique_same_side ha'd',
    { apply diff_side_line_cancel (line_in_lines ha'd') _ hb'c',
      apply between_diff_side_line,
      exact noncol13 hb'e'a',
      rw between_symm, exact hb'd'e' },
    apply ang_congr_trans _ (tri_congr_ang h₂).1,
    apply supplementary_congr,
    { rw three_pt_ang_supplementary,
      exact ⟨hb'd'e', ha'd'b', noncol132 hd'e'a'⟩ },
    { rw three_pt_ang_supplementary,
      exact ⟨hbdc, noncol23 habd, noncol23 hacd⟩ },
    exact ang_congr_symm (tri_congr_ang h₁).2.2,
  have hb'd'c' := between_same_side_pt' hb'd'e' hd'e'c',
  have hb'c'a' := col_noncol (between_col hb'd'c') (noncol13 ha'd'b') (between_neq hb'd'c').2.1,
  split,
  exact hypo_inside_ang (noncol23 hb'c'a') hb'd'c',
  apply (tri_congr_ang _).1,
  apply SAS; unfold three_pt_triang; simp,
  exact hbac, exact noncol23 hb'c'a',
  rw [seg_symm, seg_symm b' a'], exact haba'b',
  exact congr_seg_add hbdc hb'd'c' (tri_congr_seg h₁).2.2 (tri_congr_seg h₂).2.2,
  { rw [←ang_eq_same_side_pt a (between_same_side_pt.1 hbdc).1,
      ←ang_eq_same_side_pt a' (between_same_side_pt.1 hb'd'c').1],
    exact (tri_congr_ang h₁).1 }
end

lemma congr_ang_sub {a b c d a' b' c' d' : C.pts}
(hd : inside_ang d (∠ b a c)) (h : same_side_line (a'-ₗb') d' c')
(ha'b' : a' ≠ b') (h₁ : ∠ b a c ≅ₐ ∠ b' a' c') (h₂ : ∠ b a d ≅ₐ ∠ b' a' d') :
inside_ang d' (∠ b' a' c') ∧ (∠ d a c ≅ₐ ∠ d' a' c') :=
begin
  have hbac := ang_proper_iff_noncol.1 (inside_ang_proper hd),
  have hac := (noncol_neq hbac).2.2,
  rw inside_three_pt_ang at hd,
  have hacd := (same_side_line_noncol hd.2 hac).2,
  have ha'd' := (same_side_line_neq h).1.symm,
  have ha'b'd' := (same_side_line_noncol h ha'b').1,
  rcases extend_congr_ang' (ang_proper_iff_noncol.2 (noncol132 hacd))
    ha'd' (noncol_in13 ha'b'd') with ⟨c'', hdacd'a'c'', hc''b'⟩,
  rw ang_symm c'' a' d' at hdacd'a'c'',
  have key := congr_ang_add (inside_three_pt_ang.2 hd) (diff_side_line_symm hc''b')
    ha'd' h₂ hdacd'a'c'',
  have hc'c'' := same_side_line_trans (line_in_lines ha'b') (same_side_line_symm h)
    (same_side_line_symm (inside_three_pt_ang.1 key.1).1),
  rw line_symm at hc'c'',
  have ha'c'c'' := ang_unique_same_side ha'b'.symm hc'c''
    (ang_congr_trans (ang_congr_symm h₁) key.2),
  rw [ang_eq_same_side_pt b' ha'c'c'', ang_eq_same_side_pt d' ha'c'c''],
  exact ⟨key.1, hdacd'a'c''⟩
end

/--I.15 in Elements -/
lemma vertical_ang_congr {a b a' b' o : pts} (haob : noncol a o b) :
between a o a' → between b o b' → (∠ a o b ≅ₐ ∠ a' o b') :=
begin
  intros haoa' hbob',
  have hoa' := (between_neq haoa').2.2,
  have hob' := (between_neq hbob').2.2,
  have hoa'b := col_noncol (col12 (between_col haoa')) (noncol12 haob) hoa',
  have hob'a' := col_noncol (col12 (between_col hbob')) (noncol23 hoa'b) hob',
  rw between_symm at haoa',
  apply supplementary_congr _ _ (ang_congr_refl (∠ b o a')),
  { rw [ang_symm a o b, three_pt_ang_supplementary],
    exact ⟨haoa', noncol132 hoa'b, noncol13 haob⟩ },
  { rw [ang_symm, three_pt_ang_supplementary],
    exact ⟨hbob', noncol12 hoa'b, noncol132 hob'a'⟩ }
end
/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import congruence.ang_lt

/-!
# Right angles and perpendicularity

This file defines right angles using `supplementary` and how two lines
are perpendicular, proves that all right angles are congruent

## Main definitions

* `is_right_ang` defines a right angle.

* `perpendicular` means two lines intersects at 90°.

## References

* See [Geometry: Euclid and Beyond]

-/

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--An ang is a right ang if it is congruent to its supplementary ang. -/
def is_right_ang (α : ang) : Prop :=
ang_proper α ∧ ∀ β : ang, supplementary α β → (α ≅ₐ β)

lemma supplementary_exist {α : ang} (haob : ang_proper α) :
∃ β : ang, supplementary α β :=
begin
  rcases ang_three_pt α with ⟨a, b, h⟩,
  rw h, rw [h, ang_proper_iff_noncol] at haob, set o := α.vertex,
  have hob := (noncol_neq haob).2.2,
  cases between_extend hob.symm with c hboc,
  have hoc := (between_neq hboc).2.2,
  use (∠ a o c), rw three_pt_ang_supplementary,
  split, exact hboc,
  split, exact haob,
  exact noncol132 (col_noncol (col12 (between_col hboc))
    (noncol123 haob) hoc),
end

lemma right_ang_congr {α β : ang} :
(α ≅ₐ β) → is_right_ang α → ang_proper β → is_right_ang β :=
begin
  intros hαβ hα hβ,
  split, exact hβ,
  intros β' hββ',
  cases supplementary_exist hα.1 with α' hαα',
  exact ang_congr_trans (ang_congr_trans (ang_congr_symm hαβ) (hα.2 α' hαα'))
    (supplementary_congr hαα' hββ' hαβ),
end

lemma three_pt_ang_is_right_ang {a o b c : pts} (hboc : between b o c) :
is_right_ang (∠ a o b) ↔ ((∠ a o b) ≅ₐ (∠ a o c)) ∧ ang_proper (∠ a o b) :=
begin
  unfold is_right_ang,
  split; intro h, split,
  apply h.2, rw three_pt_ang_supplementary,
  have haob := ang_proper_iff_noncol.1 h.1,
  split, exact hboc, split, exact haob,
  exact noncol132 (col_noncol (col12 (between_col hboc))
    (noncol12 (noncol13 haob)) (between_neq hboc).2.2),
  exact h.1,
  split, exact h.2,
  intros β hβ, rcases hβ.1 with ⟨o', a', b', c', haoba'ob', ha'oc', hb'oc'⟩,
  have haob := ang_proper_iff_noncol.1 h.2,
  have haoc := noncol132 (col_noncol (col12 (between_col hboc))
    (noncol12 (noncol13 haob)) (between_neq hboc).2.2),
  have hoo' := ((three_pt_ang_eq_iff haob).1 haoba'ob').1, rw ←hoo' at *,
  cases ((three_pt_ang_eq_iff haob).1 haoba'ob').2 with H H,
  rw ha'oc',
  have : (∠ a o c) = (∠ a' o c'),
    rw three_pt_ang_eq_iff haoc, simp, left,
    split, exact H.1,
    apply diff_side_pt_cancel (between_diff_side_pt.1 hboc),
    rw between_diff_side_pt at hb'oc',
    exact diff_side_pt_symm (diff_same_side_pt hb'oc' (same_side_pt_symm H.2)),
  rw ←this, exact h.1,
  rw ha'oc', apply ang_congr_trans h.1, rw ang_symm,
  refine vertical_ang_congr _ _ _,
  exact noncol13 haoc,
  rw between_diff_side_pt, rw between_diff_side_pt at hboc,
  exact diff_same_side_pt hboc H.2,
  rw between_diff_side_pt, rw between_diff_side_pt at hb'oc',
  exact diff_side_pt_symm (diff_same_side_pt hb'oc' (same_side_pt_symm H.1))
end

lemma right_supplementary_right {α β : ang} (hα : is_right_ang α) (hαβ : supplementary α β) :
is_right_ang β :=
begin
  apply right_ang_congr,
  apply hα.2,
  exact hαβ,
  exact hα,
  exact hαβ.2.2
end

lemma all_right_ang_congr {α β : ang}
(hα : is_right_ang α) (hβ : is_right_ang β) : α ≅ₐ β :=
begin
  have wlog : ∀ α β : ang, is_right_ang α → is_right_ang β → (α <ₐ β) → false,
    intros x y hx hy hxy,
    rcases ang_three_pt y with ⟨a, b, haob⟩,
    set o := y.vertex, rw haob at hxy,
    rw haob at hy,
    have hbo := (noncol_neq (ang_proper_iff_noncol.1 hy.1)).2.2.symm,
    rw [ang_symm, three_pt_ang_lt] at hxy,
    rcases hxy with ⟨p, hpin, hp⟩,
    have hboa := ang_proper_iff_noncol.1 (inside_ang_proper hpin),
    rw inside_three_pt_ang at hpin,
    cases between_extend hbo with c hboc,
    have hco := (between_neq hboc).2.2.symm,
    rw three_pt_ang_is_right_ang hboc at hy,
    have h₁ : supplementary (∠ p o b) (∠ p o c),
      rw three_pt_ang_supplementary,
      split, exact hboc,
      have : noncol p o b,
        intro hpob,
        exact (same_side_line_notin hpin.1).2 (col_in23 hpob hbo.symm),
      split, exact this,
      exact noncol132 (col_noncol (col12 (between_col hboc))
        (noncol123 this) hco.symm),
    have h₂ : supplementary (∠ a o b) (∠ a o c),
      rw three_pt_ang_supplementary,
      split, exact hboc,
      split, exact noncol13 hboa,
      exact noncol132 ((col_noncol (col12 (between_col hboc))
        (noncol12 hboa)) hco.symm),
    have hf₁ : ((∠ p o c) <ₐ (∠ a o c)),
      have hbop : noncol b o p,
        intro hbop, rw line_symm at hpin,
        exact (same_side_line_notin hpin.1).2 (col_in12 hbop hbo),
      replace hbop := right_ang_congr (ang_congr_symm hp) hx
        (ang_proper_iff_noncol.2 hbop),
      rw ang_symm at hbop,
      have : ((∠ p o b) <ₐ (∠ a o b)),
        rw [ang_symm, ang_symm a o b, three_pt_ang_lt],
        exact ⟨p, inside_three_pt_ang.2 hpin, ang_congr_refl _⟩,
      replace h₁ := hbop.2 _ h₁,
      replace h₂ := hy.1,
      apply (ang_lt_congr h₁).1, apply (ang_lt_congr h₂).2,
      rw ang_proper_iff_noncol,
      exact noncol132 (col_noncol (col12 (between_col hboc))
        (noncol12 hboa) hco.symm),
      exact this,
    have hf₂ : ((∠ a o c) <ₐ (∠ p o c)),
      rw [ang_symm, ang_symm p o c, three_pt_ang_lt],
      use a, split,
      rw ang_symm, exact inside_ang_trans' hboc (by {rw ang_symm,
        exact inside_three_pt_ang.2 hpin}),
      exact ang_congr_refl _,
    exact (ang_tri h₁.2.2 h₂.2.2).2.2.1 ⟨hf₁, hf₂⟩,
  rcases (ang_tri hα.1 hβ.1).1 with h | h | h,
  exfalso, exact wlog α β hα hβ h,
  exact h,
  exfalso, exact wlog β α hβ hα h
end

/--Two lines are perpendicular if they form a right ang. -/
def perpendicular (l₁ l₂ : set pts) : Prop :=
(∃ (a b c : pts), a ∈ l₁ ∧ b ∈ l₂ ∧ c ∈ l₁ ∩ l₂ ∧ is_right_ang (∠ a c b))
∧ l₁ ∈ lines ∧ l₂ ∈ lines

lemma perpendicular_symm (l₁ l₂ : set pts) :
perpendicular l₁ l₂ → perpendicular l₂ l₁ :=
begin
  rintros ⟨⟨a, b, c, hal₁, hbl₂, hcl, hr⟩, hl⟩,
  rw ang_symm at hr, rw set.inter_comm at hcl, rw and_comm at hl,
  use [b, a, c],
  exact ⟨hbl₂, hal₁, hcl, hr⟩, exact hl
end

localized "notation a `⊥` b := perpendicular a b" in perp_notation
/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import order.segment

/-!
# sidedness

This file defines sidedness (two points lie on the same side of a line, or same side of
a point) using `incidence_order_geometry.between` and apply them to prove some theorems
of betweenness.

## Main definitions

* `same_side_line` defines a relation that two points lie on the same side of a line,
`diff_side_line` meaning that they lie on different side of a line.

* `same_side_pt` defines, on a line, two points lie on the same side with respect to
a point, `diff_side_pt` meaning the opposite.

## References

* See [Geometry: Euclid and Beyond]

-/

open_locale classical
open set

variable [B : incidence_order_geometry]

open incidence_geometry incidence_order_geometry

include B

/--Two points `a` `b` are on the same side of a line if seg `a` `b`
doesn't intersects with the line.
-/
def same_side_line (l : set pts) (a b : pts) : Prop := ¬(l ♥ (a-ₛb).inside)

/--seg `a` `b` intersects with the line and not at `a` or `b`. -/
def diff_side_line (l : set pts) (a b : pts) : Prop :=
(l ♥ (a-ₛb).inside) ∧ a ∉ l ∧ b ∉ l

lemma plane_separation
{l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
(same_side_line l a b ∨ diff_side_line l a b) ∧ ¬(same_side_line l a b ∧ diff_side_line l a b) :=
begin
  unfold same_side_line diff_side_line, unfold two_pt_seg,
  split,
  { apply not_or_of_imp, intro h,
    exact ⟨h, ha, hb⟩ },
  { intro hf,
    exact hf.1 hf.2.1 }
end

lemma not_same_side_line {l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
¬(same_side_line l a b) ↔ (diff_side_line l a b) :=
begin
  split,
  { intro hns,
    cases (plane_separation ha hb).1 with hs hd,
    exact absurd hs hns, exact hd },
  { intros hd hs,
    exact absurd (by exact ⟨hs, hd⟩) (plane_separation ha hb).2 }
end

lemma not_diff_side_line {l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
¬(diff_side_line l a b) ↔ (same_side_line l a b) :=
by rw [←not_iff_not.mpr (not_same_side_line ha hb), not_not]

lemma same_side_line_refl {l : set pts} {a : pts} (ha : a ∉ l) : same_side_line l a a :=
begin
  unfold same_side_line intersect, 
  rw seg_singleton, rw not_nonempty_iff_eq_empty, ext1, simp,
  intros h hxa, rw hxa at h, exact ha h
end

lemma same_side_line_symm {l : set pts} {a b : pts} :
same_side_line l a b → same_side_line l b a :=
by {unfold same_side_line, rw seg_symm, simp}

lemma diff_side_line_symm {l : set pts} {a b : pts} :
diff_side_line l a b → diff_side_line l b a :=
by {unfold diff_side_line, rw seg_symm, tauto}

lemma same_side_line_notin {x y : pts} {l : set pts} :
same_side_line l x y → x ∉ l ∧ y ∉ l :=
begin
  intro hlxy, unfold same_side_line intersect at hlxy, rw not_nonempty_iff_eq_empty at hlxy,
  split,
  { intro hxl,
    have : x ∈ l ∩ (x-ₛy).inside,
      simp, exact ⟨hxl, by {unfold two_pt_seg, simp}⟩,
    rw hlxy at this, exact this },
  { intro hyl,
    have : y ∈ l ∩ (x-ₛy).inside,
    { simp, exact ⟨hyl, by {unfold two_pt_seg, simp}⟩ },
    rw hlxy at this, exact this }
end

lemma same_side_line_neq {a b x y : pts} :
same_side_line (a-ₗb) x y → x ≠ a ∧ x ≠ b :=
begin
  intro hxy,
  split; intro hf; rw hf at hxy,
  exact (same_side_line_notin hxy).1 (pt_left_in_line a b),
  exact (same_side_line_notin hxy).1 (pt_right_in_line a b)
end

lemma same_side_line_neq' {a b x y : pts} :
same_side_line (a-ₗb) x y → y ≠ a ∧ y ≠ b :=
λhxy, same_side_line_neq (same_side_line_symm hxy)

lemma same_side_line_noncol {a b c d : pts} :
same_side_line (a-ₗb) c d → a ≠ b → noncol a b c ∧ noncol a b d :=
begin
  intros hcd hab,
  split; intro h,
  exact (same_side_line_notin hcd).1 (col_in12 h hab),
  exact (same_side_line_notin hcd).2 (col_in12 h hab)
end

lemma diff_side_line_neq {a b x y : pts} :
diff_side_line (a-ₗb) x y → x ≠ a ∧ x ≠ b :=
begin
  intro hxy,
  split; intro hf;
  rw hf at hxy,
  exact hxy.2.1 (pt_left_in_line a b),
  exact hxy.2.1 (pt_right_in_line a b)
end

lemma diff_side_line_neq' {a b x y : pts} :
diff_side_line (a-ₗb) x y → y ≠ a ∧ y ≠ b :=
λhxy, diff_side_line_neq (diff_side_line_symm hxy)

lemma diff_side_line_neq'' {a b : pts} {l : set pts}
(hlab : diff_side_line l a b) : a ≠ b :=
begin
  have hal := hlab.2.1,
  intro hab, rw ←hab at hlab,
  rw ←not_same_side_line at hlab,
  exact hlab (same_side_line_refl hal),
  exact hal, exact hal
end

lemma diff_side_line_noncol {a b c d : pts} :
diff_side_line (a-ₗb) c d → a ≠ b → noncol a b c ∧ noncol a b d :=
λhcd hab, ⟨noncol_in12' hab hcd.2.1, noncol_in12' hab hcd.2.2⟩

private lemma same_side_line_trans_noncol {l : set pts} (hl : l ∈ lines) {a b c : pts} :
noncol a b c → same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  unfold same_side_line, intros h hlab hlbc,
  rw seg_symm at hlbc, intro hlac,
  cases (pasch (noncol23 h) hl (same_side_line_notin hlab).1 (same_side_line_notin hlbc).1
    (same_side_line_notin hlab).2 hlac).1 with hf hf,
  exact hlab hf, exact hlbc hf
end

lemma same_side_line_trans {l : set pts} (hl : l ∈ lines) {a b c : pts} :
same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  by_cases col a b c; intros hlab hlbc,
    by_cases hab : a = b,
      rw ←hab at hlbc, exact hlbc,
    by_cases hbc : b = c,
      rw hbc at hlab, exact hlab,
    by_cases hac : a = c,
      rw hac, exact same_side_line_refl (same_side_line_notin hlbc).2,
    rcases h with ⟨m, hm, ham, hbm, hcm⟩,
    have hd : ∃ d : pts, d ∈ l ∧ d ∉ m,
      rcases two_pt_on_one_line hl with ⟨x, y, hxy, hxl, hyl⟩,
      have hlm : l ≠ m, intro hlm, rw ←hlm at ham, exact (same_side_line_notin hlab).1 ham,
      by_contra, push_neg at h,
      exact hxy (two_line_one_pt hl hm hlm hxl (h x hxl) hyl (h y hyl)),
    rcases hd with ⟨d, hdl, hdm⟩,
    have habd : noncol a b d,
      apply noncol_in12' hab,
      rw two_pt_one_line (line_in_lines hab) hm hab
        (pt_left_in_line a b) (pt_right_in_line a b) ham hbm,
      exact hdm,
    have had := (noncol_neq habd).2.1,
    cases between_extend had.symm with e hdae,
    have hae := (between_neq hdae).2.2,
    have hlae : same_side_line l a e,
      intro hlae, cases hlae with f hf,
      simp at hf,
      have hflae : f ∈ l ∧ f ∈ (a-ₗe),
        from ⟨hf.1, seg_in_line a e hf.2⟩,
      have hdlae : d ∈ l ∧ d ∈ (a-ₗe),
        from ⟨hdl, col_in23 (between_col hdae) hae⟩,
      have hneq : l ≠ (a-ₗe),
        intro hf, have := (same_side_line_notin hlab).1,
        rw hf at this, exact this (pt_left_in_line a e),
      have hdf := two_line_one_pt hl (line_in_lines (between_neq hdae).2.2)
        hneq hdlae.1 hdlae.2 hflae.1 hflae.2,
      rw hdf at hdae,
      unfold two_pt_seg at hf, simp at hf,
      have := between_neq hdae,
      rcases hf.2 with hf | hf | hf,
      exact this.1 hf, exact this.2.1 hf,
      exact between_contra.1 ⟨hf, hdae⟩,
    have hbae := noncol132 (col_noncol (col12 (between_col hdae)) (noncol23 habd) hae),
    have hebc := noncol132 (col_noncol ⟨m, hm, hbm, ham, hcm⟩ hbae hbc),
    have haec := noncol23 (col_noncol ⟨m, hm, ham, hbm, hcm⟩ (noncol12 hbae) hac),
    have hlbe := same_side_line_trans_noncol hl hbae (same_side_line_symm hlab) hlae,
    have hlec := same_side_line_trans_noncol hl hebc (same_side_line_symm hlbe) hlbc,
    exact same_side_line_trans_noncol hl haec hlae hlec,
  exact same_side_line_trans_noncol hl h hlab hlbc
end

/--Two points `a` `b` are on the same side of the point `o` if
they are col and `o` is not in seg `a` `b`.
-/
def same_side_pt (o a b : pts) : Prop :=
o ∉ (a-ₛb).inside ∧ col o a b

/--`o` is in seg `a` `b` but is not `a` and `b`. -/
def diff_side_pt (o a b : pts) : Prop :=
o ∈ (a-ₛb).inside ∧ a ≠ o ∧ b ≠ o

lemma same_side_pt_neq {o a b : pts} (hoab : same_side_pt o a b) : a ≠ o ∧ b ≠ o :=
begin
  unfold same_side_pt at hoab, unfold two_pt_seg at hoab,
  split,
  intro hao, rw hao at hoab,
  simp at hoab, exact hoab,
  intro hbo, rw hbo at hoab,
  simp at hoab, exact hoab
end

lemma diff_side_pt_col {o a b : pts} : diff_side_pt o a b → col o a b :=
begin
  intro hoab,
  by_cases a = b,
    rw h, exact ⟨(b-ₗo), line_in_lines hoab.2.2,
      pt_right_in_line b o, pt_left_in_line b o, pt_left_in_line b o⟩,
  exact ⟨(a-ₗb), line_in_lines h,
    (seg_in_line a b) hoab.1, pt_left_in_line a b, pt_right_in_line a b⟩
end

theorem line_separation
{p a b : pts} (hpab : col p a b) (hap : a ≠ p) (hbp : b ≠ p) : 
(same_side_pt p a b ∨ diff_side_pt p a b) ∧
¬(same_side_pt p a b ∧ diff_side_pt p a b) :=
begin
  unfold same_side_pt diff_side_pt,
  split,
  { by_cases hp : p ∈ (a-ₛb).inside,
    right, exact ⟨hp, hap, hbp⟩,
    left, exact ⟨hp, hpab⟩ },
  { push_neg,
    intros h₁ h₂, exact absurd h₂ h₁.1 }
end

lemma not_same_side_pt
{p a b : pts} (hpab : col p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬same_side_pt p a b ↔ diff_side_pt p a b) :=
begin
  have := line_separation hpab ha hb,
  split,
  intro hs,
  cases this.1 with h h,
  exact absurd h hs, exact h,
  intro hd,
  cases (not_and_distrib.mp this.2) with h h,
  exact h, exact absurd hd h
end

lemma not_diff_side_pt
{p a b : pts} (hpab : col p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬diff_side_pt p a b ↔ same_side_pt p a b) :=
by rw [←not_iff_not.mpr (not_same_side_pt hpab ha hb), not_not]

lemma same_side_pt_refl {a b : pts} (hab : a ≠ b) : same_side_pt a b b :=
begin
  split, rw seg_singleton, exact hab,
  exact ⟨a-ₗb, line_in_lines hab, pt_left_in_line a b, pt_right_in_line a b, pt_right_in_line a b⟩
end

lemma same_side_pt_symm {a b c : pts} :
same_side_pt a b c → same_side_pt a c b :=
begin
  unfold same_side_pt,
  intro habc, split,
  rw seg_symm, exact habc.1,
  rcases habc.2 with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨l, hl, hal, hcl, hbl⟩
end

lemma diff_side_pt_symm {a b c : pts} :
diff_side_pt a b c → diff_side_pt a c b :=
by { unfold diff_side_pt, rw seg_symm, tauto }

lemma same_side_pt_line {a b c : pts} (habc : same_side_pt a b c) {l : set pts}
(hl : l ∈ lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) : same_side_line l b c :=
begin
  by_cases hbc : b = c,
    rw ←hbc, exact same_side_line_refl hbl,
  rintros ⟨x, hxl, hxbc⟩,
  apply habc.1,
  have hneq : l ≠ (b-ₗc),
    intro hf, rw hf at hbl, exact hbl (pt_left_in_line b c),
  rw two_line_one_pt hl (line_in_lines hbc) hneq
    hal (col_in23 habc.2 hbc) hxl ((seg_in_line b c) hxbc),
  exact hxbc
end

lemma between_diff_side_pt {a b c : pts} :
between a b c ↔ diff_side_pt b a c :=
begin
  split,
  exact λh, ⟨by {left, exact h}, (between_neq h).1, (between_neq h).2.2.symm⟩,
  { intro h,
    rcases h.1 with h | hf | hf,
    exact h,
    exact absurd hf h.2.1.symm,
    exact absurd hf h.2.2.symm }
end

lemma diff_side_pt_neq' {a b c : pts} (habc : diff_side_pt a b c) : b ≠ c :=
by { rw ←between_diff_side_pt at habc, exact (between_neq habc).2.1 }

lemma diff_side_pt_line {a b c : pts} (habc : diff_side_pt a b c) {l : set pts}
(hl : l ∈ lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) : diff_side_line l b c :=
⟨⟨a, hal, by {left, exact between_diff_side_pt.2 habc}⟩, hbl, hcl⟩

private lemma between_same_side_pt_prep {a b c : pts} :
between a b c → same_side_pt a b c :=
begin
  intro habc,
  have hab := (between_neq habc).1,
  have hac := (between_neq habc).2.1,
  split,
  { intro hf, replace hf := seg_in_neq hab hac hf,
    exact between_contra.1 ⟨habc, hf⟩ },
  exact between_col habc
end

lemma between_same_side_pt {a b c : pts} :
between a b c ↔ same_side_pt a b c ∧ same_side_pt c a b :=
begin
  split,
  { intro habc, split,
    exact between_same_side_pt_prep habc,
    rw between_symm at habc,
    exact same_side_pt_symm (between_same_side_pt_prep habc) },
  { rintros ⟨habc, hcab⟩,
    have hab := (same_side_pt_neq habc).1.symm,
    have hac := (same_side_pt_neq habc).2.symm,
    have hbc := (same_side_pt_neq hcab).2,
    rcases between_tri habc.2 hab hac hbc with h | h | h,
    exact h,
    exfalso, apply hcab.1, left, exact h,
    exfalso, apply habc.1, left, exact h }
end

lemma same_side_line_pt {a b c : pts} (habc : col a b c) (l : set pts)
(hl : l ∈ lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) (hlbc : same_side_line l b c) :
same_side_pt a b c :=
begin
  have hba : b ≠ a,
    intro hf, rw hf at hbl, exact hbl hal,
  have hca : c ≠ a,
    intro hf, rw hf at hcl, exact hcl hal,
  rw ←(not_diff_side_pt habc hba hca),
  intro hf,
  have := (diff_side_pt_line hf) hl hal hbl hcl,
  exact (plane_separation hbl hcl).2 ⟨hlbc, this⟩
end

lemma diff_side_line_pt {a b c : pts} (habc : col a b c) (l : set pts)
(hl : l ∈ lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) (hlbc : diff_side_line l b c) :
diff_side_pt a b c :=
begin
  have hba : b ≠ a,
    intro hf, rw hf at hbl, exact hbl hal,
  have hca : c ≠ a,
    intro hf, rw hf at hcl, exact hcl hal,
  rw ←not_same_side_pt habc hba hca,
  intro hf,
  have := same_side_pt_line hf hl hal hbl hcl,
  exact (plane_separation hbl hcl).2 ⟨this, hlbc⟩
end

lemma line_pt_exist {a b c : pts} (habc : col a b c) (hab : a ≠ b) (hac : a ≠ c) : 
∃ l ∈ lines, a ∈ l ∧ b ∉ l ∧ c ∉ l :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩,
  have hd : ∃ d : pts, noncol a b d ∧ d ∉ l,
    cases noncol_exist hab with d habd, use d, split, exact habd,
    intro hdl, exact habd ⟨l, hl, hal, hbl, hdl⟩,
  rcases hd with ⟨d, habd, hdl⟩,
  have hb : b ∉ (a-ₗd),
    intro hb, exact habd ⟨(a-ₗd), line_in_lines (noncol_neq habd).2.1,
      pt_left_in_line a d, hb, pt_right_in_line a d⟩,
  have hc : c ∉ (a-ₗd),
    intro hc, rw two_pt_one_line hl (line_in_lines (noncol_neq habd).2.1)
      hac hal hcl (pt_left_in_line a d) hc at hbl,
    exact hb hbl,
  exact ⟨(a-ₗd), line_in_lines (noncol_neq habd).2.1, pt_left_in_line a d, hb, hc⟩
end

lemma same_side_pt_trans {a b c d : pts} :
same_side_pt a b c → same_side_pt a c d → same_side_pt a b d :=
begin
  intros habc hacd,
  have hac := (same_side_pt_neq habc).2.symm,
  rcases line_pt_exist habc.2 (same_side_pt_neq habc).1.symm hac
    with ⟨l, hl, hal, hbl, hcl⟩,
  have hdl : d ∉ l,
    intro hdl,
    rcases hacd.2 with ⟨m, hm, ham, hcm, hdm⟩,
    rw two_pt_one_line hm hl (same_side_pt_neq hacd).2.symm ham hdm hal hdl at hcm,
    exact hcl hcm,
  apply same_side_line_pt,
  exact col_trans (col23 habc.2) hacd.2 hac,
  exact hl, exact hal, exact hbl,
  exact hdl,
  exact same_side_line_trans hl (same_side_pt_line habc hl hal hbl hcl)
    (same_side_pt_line hacd hl hal hcl hdl)
end

lemma between_same_side_pt' {a b c d : pts} (habc : between a b c)
(hbcd : same_side_pt b c d) : between a b d :=
begin
  have hbc := (between_neq habc).2.2,
  rw [between_diff_side_pt, ←not_same_side_pt],
  { intro hf, rw [between_diff_side_pt, ←not_same_side_pt] at habc,
    exact habc (same_side_pt_trans hf (same_side_pt_symm hbcd)),
    exact (diff_side_pt_col habc),
    exact habc.2.1, exact habc.2.2 },
  exact col_trans (col123 (between_col habc)) hbcd.2 hbc,
  exact (between_neq habc).1,
  exact (same_side_pt_neq hbcd).2
end


lemma between_trans {a b c d : pts} :
between a b c → between b c d → between a b d ∧ between a c d :=
begin
  have : ∀ {a b c d : pts}, between a b c → between b c d → between a b d ,
    intros a b c d habc hbcd,
    have hab := (between_neq habc).1,
    have hbc := (between_neq habc).2.2,
    have hbd := (between_neq hbcd).2.1,
    rw [between_diff_side_pt, ←not_same_side_pt],
    { intro hf,
      have habc' := between_col habc,
      rw [between_diff_side_pt, ←not_same_side_pt] at habc,
      apply habc,
      exact (same_side_pt_trans hf (same_side_pt_symm (between_same_side_pt.1 hbcd).1)),
      exact col12 habc', exact hab, exact hbc.symm },
    exact col_trans (col123 (between_col habc)) (between_col hbcd) hbc,
    exact hab, exact hbd.symm,
  intros habc hbcd, split, exact this habc hbcd,
  rw between_symm at habc hbcd, rw between_symm,
  exact this hbcd habc
end

lemma between_trans' {a b c d : pts} :
between a b d → between b c d → between a b c ∧ between a c d :=
begin
  have : ∀ {a b c d : pts}, between a b d → between b c d → between a b c,
    intros a b c d habd hbcd,
    have hab := (between_neq habd).1,
    have hbc := (between_neq hbcd).1,
    have hbd := (between_neq hbcd).2.1,
    rw [between_diff_side_pt, ←not_same_side_pt],
    { intro hf,
      have habd' := between_col habd,
      rw [between_diff_side_pt, ←not_same_side_pt] at habd,
      apply habd,
      exact (same_side_pt_trans hf (between_same_side_pt.1 hbcd).1),
      exact col12 habd', exact hab, exact hbd.symm },
    exact col_trans (col123 (between_col habd)) (col23 (between_col hbcd)) hbd,
    exact hab, exact hbc.symm,
  intros habd hbcd,
  have habc := this habd hbcd,
  exact ⟨habc, (between_trans habc hbcd).2⟩
end

lemma same_side_pt_between {a b c : pts} :
same_side_pt a b c → b ≠ c → between a b c ∨ between a c b :=
begin
  intros habc hbc,
  rcases between_tri habc.2 (same_side_pt_neq habc).1.symm
    (same_side_pt_neq habc).2.symm hbc with h | h | h,
  left, exact h,
  right, exact h,
  { rw [between_diff_side_pt, ←not_same_side_pt habc.2] at h, exact absurd habc h,
    exact (same_side_pt_neq habc).1,
    exact (same_side_pt_neq habc).2 }
end

lemma between_same_side_pt_between {a b c d : pts} :
between a b c → same_side_pt b c d → between a b d :=
begin
  intros habc hbcd,
  by_cases hcd : c = d,
    rw hcd at habc, exact habc,
  cases same_side_pt_between hbcd hcd,
  exact (between_trans habc h).1,
  exact (between_trans' habc h).1
end

lemma diff_side_pt_cancel {a b c d : pts} :
diff_side_pt a b c → diff_side_pt a b d → same_side_pt a c d :=
begin
  intros hbac hbad,
  have hab := hbac.2.1.symm,
  have hac := hbac.2.2.symm,
  have hbc := diff_side_pt_neq' hbac,
  have hbd := diff_side_pt_neq' hbad,
  by_cases hcd : c = d,
    rw ←hcd, exact same_side_pt_refl hac,
  rw ←between_diff_side_pt at hbac hbad,
  rw [←not_diff_side_pt, ←between_diff_side_pt],
  { intro hcad,
    have hbcd := col_trans (between_col hbac) (between_col hbad) hab.symm,
    rcases between_tri hbcd hbc hbd hcd with hbcd | hbdc | hcbd,
    exact between_contra.2.1 ⟨(between_trans' hbcd hcad).1, hbac⟩,
    { rw between_symm at hcad,
      exact between_contra.2.1 ⟨(between_trans' hbdc hcad).1, hbad⟩ },
    { rw between_symm at hbac,
      exact between_contra.2.1 ⟨(between_trans' hcbd hbad).1, hbac⟩ } },
  exact col_trans (col12 (between_col hbac)) (col12 (between_col hbad)) hab,
  exact (between_neq hbac).2.2.symm,
  exact (between_neq hbad).2.2.symm,
end

lemma diff_side_line_cancel {l : set pts} (hl : l ∈ lines) {a b c : pts} :
diff_side_line l a b → diff_side_line l b c → same_side_line l a c :=
begin
  intros h₁ h₂,
  have hab : a ≠ b,
    have hal := h₁.2.1,
    intro hf, rw [←hf, ←not_same_side_line] at h₁,
    exact h₁ (same_side_line_refl hal), exact hal, exact hal,
  by_cases hac : a = c,
    rw ←hac, exact same_side_line_refl h₁.2.1,
  have hbc : b ≠ c,
    have hbl := h₁.2.2,
    intro hf, rw [←hf, ←not_same_side_line] at h₂,
    exact h₂ (same_side_line_refl hbl), exact hbl, exact hbl,
  by_cases habc : col a b c,
  { cases h₁.1 with x hx,
    cases h₂.1 with y hy,
    have hxa : x ≠ a,
      intro hf, rw hf at hx, exact h₁.2.1 hx.1,
    have hxb : x ≠ b,
      intro hf, rw hf at hx, exact h₁.2.2 hx.1,
    have haxb := seg_in_neq hxa hxb hx.2,
    have hyb : y ≠ b,
      intro hf, rw hf at hy, exact h₁.2.2 hy.1,
    have hyc : y ≠ c,
      intro hf, rw hf at hy, exact h₂.2.2 hy.1,
    have hbyc := seg_in_neq hyb hyc hy.2, 
    have hxy : x = y,
      apply two_line_one_pt hl (line_in_lines hab),
      intro hf, rw hf at h₁, exact h₁.2.2 (pt_right_in_line a b),
      exact hx.1, exact (seg_in_line a b) hx.2,
      exact hy.1, exact col_in21 (col_trans (col123 habc) (col23 (between_col hbyc)) hbc) hab,
    rw ←hxy at hbyc,
    apply same_side_pt_line,
    exact diff_side_pt_cancel (diff_side_pt_symm (between_diff_side_pt.1 haxb))
      (between_diff_side_pt.1 hbyc),
    exact hl, exact hx.1,
    exact h₁.2.1, exact h₂.2.2 },
  by_contra h₃,
  rw not_same_side_line h₁.2.1 h₂.2.2 at h₃,
  unfold diff_side_line at h₁ h₂ h₃,
  exact (pasch habc hl h₁.2.1 h₁.2.2 h₂.2.2 h₁.1).2 ⟨h₃.1, h₂.1⟩
end

lemma diff_same_side_line {l : set pts} (hl : l ∈ lines) {a b c : pts} :
diff_side_line l a b → same_side_line l b c → diff_side_line l a c :=
begin
  intros hlab hlbc,
  rw ←not_same_side_line hlab.2.1 (same_side_line_notin hlbc).2,
  rw ←not_same_side_line at hlab, intro hlac,
  exact hlab (same_side_line_trans hl hlac (same_side_line_symm hlbc)),
  exact hlab.2.1, exact hlab.2.2
end

lemma same_diff_side_line {l : set pts} (hl : l ∈ lines) {a b c : pts} :
same_side_line l a b → diff_side_line l b c → diff_side_line l a c := λhlab hlbc,
diff_side_line_symm (diff_same_side_line hl (diff_side_line_symm hlbc) (same_side_line_symm hlab))

lemma diff_same_side_pt {a b c d : pts} :
diff_side_pt a b c → same_side_pt a b d → diff_side_pt a c d :=
begin
  intros habc habd,
  rw ←not_same_side_pt, rw ←not_same_side_pt at habc,
  intro hacd, exact habc (same_side_pt_trans habd (same_side_pt_symm hacd)),
  exact (diff_side_pt_col habc), exact habc.2.1, exact habc.2.2,
  exact col_trans (diff_side_pt_col habc) habd.2 habc.2.1.symm,
  exact habc.2.2, exact (same_side_pt_neq habd).2
end

private lemma two_pt_seg_pt_prep {a b a' b' : pts} :
(a-ₛb) = (a'-ₛb') → a = a' → b = b' :=
begin
  intros haba'b' haa',
  replace haba'b' : (a-ₛb).inside = (a-ₛb').inside, rw [haba'b', ←haa'],
  by_contra hbb',
  by_cases hab : a = b, rw hab at haba'b',
  { rw seg_singleton at haba'b',
    cases (two_pt_between hbb') with x hbxb',
    have hx : x ∈ (b-ₛb').inside,
      unfold two_pt_seg, simp, right, right, exact hbxb',
    rw ←haba'b' at hx, simp at hx, exact (between_neq hbxb').1 hx.symm },
  by_cases hab' : a = b', rw hab' at haba'b',
  { rw seg_singleton at haba'b',
    cases (two_pt_between hbb') with x hbxb',
    have hx : x ∈ (b-ₛb').inside,
      unfold two_pt_seg, simp, right, right, exact hbxb',
    rw [seg_symm, haba'b'] at hx, simp at hx, exact (between_neq hbxb').2.2 hx },
  by_cases habb' : col a b b',
  { rcases between_tri habb' hab hab' hbb' with h | h | h,
    cases (two_pt_between (between_neq h).2.2) with x hbxb',
    have haxb' := (between_trans' h hbxb').2,
    have h₁ : x ∈ (a-ₛb').inside,
      unfold two_pt_seg, simp, right, right, exact haxb',
    have h₂ : x ∉ (a-ₛb).inside,
      unfold two_pt_seg, simp, intro hf,
      rcases hf with hf | hf | hf,
      exact (between_neq (between_trans' h hbxb').2).1 hf.symm,
      exact (between_neq hbxb').1 hf.symm,
      have habx := (between_trans' h hbxb').1,
      exact between_contra.2.1 ⟨hf, habx⟩,
    rw haba'b' at h₂, exact absurd h₁ h₂,
    cases (two_pt_between (between_neq h).2.2) with x hb'xb,
    have haxb := (between_trans' h hb'xb).2,
    have h₁ : x ∈ (a-ₛb).inside,
      unfold two_pt_seg, simp, right, right, exact haxb,
    have h₂ : x ∉ (a-ₛb').inside,
      unfold two_pt_seg, simp, intro hf,
      rcases hf with hf | hf | hf,
      exact (between_neq (between_trans' h hb'xb).2).1 hf.symm,
      exact (between_neq hb'xb).1 hf.symm,
      have hab'x := (between_trans' h hb'xb).1,
      exact between_contra.2.1 ⟨hf, hab'x⟩,
    rw haba'b' at h₁, exact absurd h₁ h₂,
    cases (two_pt_between hab) with x haxb,
    have h₁ : x ∈ (a-ₛb).inside,
      unfold two_pt_seg, simp, right, right, exact haxb,
    have h₂ : x ∉ (a-ₛb').inside,
      unfold two_pt_seg, simp, intro hf,
      rw between_symm at h,
      rcases hf with hf | hf | hf,
      exact (between_neq haxb).1 hf.symm,
      exact (between_neq (between_trans' h haxb).2).1 hf.symm,
      have hb'ax := (between_trans' h haxb).1,
      rw between_symm at hf,
      exact between_contra.2.1 ⟨hf, hb'ax⟩,
      rw haba'b' at h₁, exact absurd h₁ h₂ },
  cases (two_pt_between hab) with x haxb,
  have h : x ∈ (a-ₛb').inside,
    rw ←haba'b', unfold two_pt_seg, simp, right, right, exact haxb,
  unfold two_pt_seg at h, simp at h, rcases h with h | h | h,
  exact absurd h (between_neq haxb).1.symm,
  rw h at haxb, exact habb' (col23 (between_col haxb)),
  exact habb' (col_trans (between_col haxb) (between_col h) (between_neq haxb).1)
end

lemma two_pt_seg_pt {a b a' b' : B.pts} :
(a-ₛb) = (a'-ₛb') → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') :=
begin
  intros haba'b',
  by_cases haa' : a = a',
    left, exact ⟨haa', two_pt_seg_pt_prep haba'b' haa'⟩,
  by_cases hab' : a = b',
    right, rw seg_symm a' b' at haba'b', exact ⟨hab', two_pt_seg_pt_prep haba'b' hab'⟩,
  have ha'ab' := (seg_in_neq haa' hab' (by {rw ←haba'b', exact pt_left_in_seg a b })),
  by_cases ha'b : a' = b,
    right, rw seg_symm at haba'b', exact ⟨two_pt_seg_pt_prep haba'b' ha'b.symm, ha'b.symm⟩,
  have haa'b := (seg_in_neq (ne.symm haa') ha'b (by {rw haba'b', exact pt_left_in_seg a' b' })),
  by_cases hbb' : b = b',
  { rw [seg_symm, seg_symm a' b'] at haba'b',
    left, exact ⟨two_pt_seg_pt_prep haba'b' hbb', hbb'⟩ },
  have ha'bb' := (seg_in_neq (ne.symm ha'b) hbb' (by {rw ←haba'b', exact pt_right_in_seg a b })),
  rw between_symm at ha'ab',
  have hb'a'b := (between_trans ha'ab' haa'b).2,
  rw between_symm at ha'bb',
  exfalso, exact between_contra.2.1 ⟨hb'a'b, ha'bb'⟩
end

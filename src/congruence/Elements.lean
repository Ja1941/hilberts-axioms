/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import congruence.basic
import congruence.seg_lt
import congruence.ang_lt
import congruence.perpendicular

/-!
# Euclid's Elements

This file proves most propositions in Euclid's book I with some exceptions. For
instance, intersection of two circles is not guaranteed by Hilbert's axioms. Also
note that some proofs are different from Euclid's ones to fit Hilbert's axioms.

Some propositions needs reintepretation. For example, the propositions on ruler
and compass contructions are understood to be existence proof.

## References

* See [Geometry: Euclid and Beyond]

-/

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--I.5 in Elements -/
theorem isosceles {a b c : pts} (habc : noncol a b c) :
((a-ₛb) ≅ₛ (a-ₛc)) → ((∠ a b c) ≅ₐ (∠ a c b)) :=
begin
  intro habac,
  have hab := (noncol_neq habc).1,
  have hac := (noncol_neq habc).2.1,
  cases between_extend hab with d habd,
  cases between_extend hac with x hacx,
  have hbd := (between_neq habd).2.2,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 hbd)
    (between_neq hacx).2.2 with ⟨e, hcxe, hbdce, -⟩,
  have hace := between_same_side_pt_between hacx hcxe, clear hcxe hacx x,
  have had := (between_neq habd).2.1,
  have hae := (between_neq hace).2.1,
  have hadc := col_noncol (between_col habd) habc had,
  have haeb := col_noncol (between_col hace) (noncol23 habc) hae,
  have hadcaeb : ((Δ a d c) ≅ₜ (Δ a e b)),
    apply SAS; unfold three_pt_triang; simp,
    exact hadc, exact haeb,
    exact congr_seg_add habd hace habac hbdce,
    exact seg_congr_symm habac,
    rw [ang_symm, ←ang_eq_same_side c (between_same_side_pt.1 habd).1],
    rw [ang_symm, ang_symm e _ _],
    rw ang_eq_same_side b (between_same_side_pt.1 hace).1, exact ang_congr_refl _,
  have hce := (between_neq hace).2.2,
  have hdbc := col_noncol (col132 (between_col habd))
    (noncol12 hadc) hbd.symm,
  have hecb := col_noncol (col132 (between_col hace))
    (noncol12 haeb) hce.symm,
  have hdbcecb : ((Δ d b c) ≅ₜ (Δ e c b)),
    apply SAS; unfold three_pt_triang; simp,
    exact hdbc, exact hecb,
    rw [seg_symm, seg_symm e _], exact hbdce,
    exact (tri_congr_side hadcaeb).2.2,
    rw [ang_symm, ←ang_eq_same_side c (between_same_side_pt.1 habd).2],
    rw [ang_symm _ e _, ←ang_eq_same_side b (between_same_side_pt.1 hace).2],
    rw [ang_symm, ang_symm b _ _],
    exact (tri_congr_ang hadcaeb).2.1,
  have key := (tri_congr_ang hdbcecb).2.1,
  rw [ang_symm, ang_symm e _ _] at key,
  rw [ang_symm, ang_symm a _ _],
  refine supplementary_congr _ _ key;
  rw three_pt_ang_supplementary,
  rw between_symm at habd,
  exact ⟨habd, noncol13 hdbc, noncol13 habc⟩,
    rw between_symm at hace,
  exact ⟨hace, noncol13 hecb, noncol123 habc⟩
end

/--I.6 in Elements -/
theorem isosceles' {a b c : pts} (habc : noncol a b c) :
((∠ a b c) ≅ₐ (∠ a c b)) → ((a-ₛb) ≅ₛ (a-ₛc)) :=
begin
  have : ∀ {a b c : pts}, noncol a b c → ((∠ a b c) ≅ₐ (∠ a c b)) → ¬((a-ₛb) <ₛ (a-ₛc)),
    intros a b c habc he hf,
    have hab := (noncol_neq habc).1,
    have hbc := (noncol_neq habc).2.2,
    rw [seg_symm a c, two_pt_seg_lt] at hf,
    rcases hf with ⟨d, hcda, habcd⟩,
    have hcd := (between_neq hcda).1,
    have had := (between_neq hcda).2.2.symm,
    have hcdb := col_noncol (col23 (between_col hcda))
        (noncol132 habc) hcd,
    have : ((Δ b a c) ≅ₜ (Δ c d b)),
      apply SAS; unfold three_pt_triang; simp,
      exact noncol12 habc, exact hcdb,
      rw seg_symm, exact habcd,
      rw seg_symm, exact seg_congr_refl _,
      rw [ang_symm d c b, ang_eq_same_side b (between_same_side_pt.1 hcda).1,
        ang_symm b c a], exact he,
    have : ((∠ d b c) ≅ₐ (∠ a b c)),
      refine ang_congr_trans _ (ang_congr_symm he),
      rw [ang_symm, ang_symm a c b],
      exact ang_congr_symm (tri_congr_ang this).2.2,
    apply (ang_tri (ang_nontrivial_iff_noncol.2 (noncol123 hcdb))
      (ang_nontrivial_iff_noncol.2 habc)).2.1,
    split,
    rw [ang_symm a b c, three_pt_ang_lt],
    use d, split,
    rw inside_three_pt_ang, split,
    refine t_shape_seg hbc (noncol_in23 habc) _ _ hcd.symm,
    left, exact hcda,
    refine t_shape_seg hab.symm _ _ _ had.symm,
    rw line_symm, exact noncol_in12 habc,
    left, rw between_symm at hcda, exact hcda,
    rw ang_symm, exact ang_congr_refl _,
    exact this,
  intro he,
  have hab := (noncol_neq habc).1,
  have hac := (noncol_neq habc).2.1,
  rcases (seg_tri (seg_nontrivial_iff_neq.2 hab)
    (seg_nontrivial_iff_neq.2 hac)).1 with h | h | h,
  exact absurd h (this habc he),
  exact h,
  exact absurd h (this (noncol23 habc) (ang_congr_symm he))
end

/--I.8 in Elements -/
theorem SSS {ABC DEF : triang} (habc : noncol ABC.v1 ABC.v2 ABC.v3)
(ha'b'c' : noncol DEF.v1 DEF.v2 DEF.v3) (haba'b' : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2))
(haca'c' : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3)) (hbcb'c' : (ABC.v2-ₛABC.v3) ≅ₛ (DEF.v2-ₛDEF.v3)) :
ABC ≅ₜ DEF :=
begin
  set a := ABC.v1 with ha, set b := ABC.v2 with hb, set c := ABC.v3 with hc,
  set a' := DEF.v1, set b' := DEF.v2, set c' := DEF.v3,
  have hab := (noncol_neq habc).1,
  have hac := (noncol_neq habc).2.1,
  have hbc := (noncol_neq habc).2.2,
  cases between_extend hab.symm with x hbax,
  have : x ∉ (a-ₗc), from noncol_in13 (col_noncol
    (col12 (between_col hbax)) habc (between_neq hbax).2.2),
  rcases extend_congr_ang (ang_nontrivial_iff_noncol.2
    (noncol12 ha'b'c')) hac this with ⟨y, hy, hacyx, -⟩,
  have hay : a ≠ y,
    intro hay, rw ←hay at hacyx,
    exact (same_side_line_not_in hacyx).1 (pt_left_in_line a c),
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 (noncol_neq ha'b'c').1) hay
    with ⟨d, hayd, ha'b'ad, -⟩,
  have had := (same_side_pt_neq hayd).2.symm,
  have hacbd : diff_side_line (a-ₗc) b d,
    have h₁ : diff_side_line (a-ₗc) b x,
      refine (diff_side_pt_line (between_diff_side_pt.1 hbax)).2.2.2 _ _,
      exact line_in_lines hac,
      split, exact pt_left_in_line a c, split, exact noncol_in13 habc,
      exact noncol_in13 (col_noncol (col12 (between_col hbax))
        habc (between_neq hbax).2.2),
    have h₂ : same_side_line (a-ₗc) y d,
      rw line_symm, refine t_shape_ray hac.symm _ _ _ _,
      rw line_symm, exact (same_side_line_not_in hacyx).1,
      left, exact hayd, exact had.symm,
    exact diff_same_side_line (line_in_lines hac)
      (diff_same_side_line (line_in_lines hac) h₁ (same_side_line_symm hacyx)) h₂,
  have hadc : noncol a d c,
    intro hadc, exact hacbd.2.2 ((col_in13 hadc) hac),
  have hadca'b'c' : ((Δ a d c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triang; simp,
    exact hadc, exact ha'b'c',
    exact seg_congr_symm ha'b'ad, exact haca'c',
    have : ∠ y a c = ∠ d a c,
      rw [ang_symm, ang_symm d _ _],
      exact ang_eq_same_side c hayd,
    rw this at hy, exact ang_congr_symm hy,
  refine tri_congr_trans _ hadca'b'c',
  apply tri_congr12, rw [←ha, ←hb, ←hc],
  apply SAS; unfold three_pt_triang; simp,
  exact noncol12 habc, exact noncol12 hadc,
  rw seg_symm at haba'b', rw seg_symm d a,
  exact seg_congr_trans haba'b' (seg_congr_symm (tri_congr_side hadca'b'c').1),
  exact seg_congr_trans hbcb'c' (seg_congr_symm (tri_congr_side hadca'b'c').2.2),
  have had := (noncol_neq hadc).1,
  have hcd := (noncol_neq hadc).2.2.symm,
  have h₁ : ((c-ₛb) ≅ₛ (c-ₛd)),
    rw seg_symm, apply seg_congr_trans hbcb'c',
    rw seg_symm c d, exact seg_congr_symm (tri_congr_side hadca'b'c').2.2,
  have h₂ : ((a-ₛb) ≅ₛ (a-ₛd)),
    apply seg_congr_trans haba'b', exact seg_congr_symm (tri_congr_side hadca'b'c').1,
  have hbd : b ≠ d,
    intro hbd, rw hbd at hacbd, rw ←not_same_side_line at hacbd,
    exact hacbd (same_side_line_refl (noncol_in13 hadc)),
    exact noncol_in13 hadc, exact noncol_in13 hadc,
  cases hacbd.1 with o ho,
  have hbod : between b o d,
    cases ho.2, exact h,
    cases h, rw h at ho, exact absurd ho.1 (noncol_in13 habc),
    simp at h, rw h at ho, exact absurd ho.1 (noncol_in13 hadc),
  by_cases hao : a = o,
    rw ←hao at ho, rw ←hao at hbod,
    have hbad : between b a d,
      cases ho.2, exact h, cases h, exact absurd h hab, exact absurd h had,
    rw between_same_side_pt at hbad,
    rw [ang_symm, ang_eq_same_side c hbad.1],
    rw [ang_symm a _ _, ←ang_eq_same_side c hbad.2],
    apply isosceles,
    intro hcbd, exact (noncol12 hadc) ((col_trans
      (col132 (between_col hbod)) (col13 hcbd)) hbd.symm),
    exact h₁,
  by_cases hco : c = o,
    rw ←hco at ho, rw ←hco at hbod,
    have hbad : between b c d,
      cases ho.2, exact h, cases h, exact absurd h hbc.symm, exact absurd h hcd,
    rw between_same_side_pt at hbad,
    rw [ang_eq_same_side a hbad.1, ←ang_eq_same_side a hbad.2],
    apply isosceles,
    intro habd, exact (noncol123 hadc)
      ((col_trans (col132 (between_col hbod)) (col13 habd)) hbd.symm),
    exact h₂,
  have hoac : col o a c, from ⟨(a-ₗc), line_in_lines hac, ho.1,
    pt_left_in_line a c, pt_right_in_line a c⟩,
  have hbo := (between_neq hbod).1,
  have hdo := (between_neq hbod).2.2.symm,
  have hobc : noncol o b c, from λhobc, habc (col123 (col_trans
    (col132 hoac) (col132 hobc) hco)),
  have hocd : noncol o c d, from λhocd, hobc (col_trans (col123
    (between_col hbod)) (col23 hocd) hdo.symm),
  have hoab : noncol o a b,
    from λhoab, habc (col_trans (col12 hoab) (col12 hoac) hao),
  have hoad : noncol o a d, from λhoad, hoab (col_trans (col23 hoad)
    (col123 (between_col hbod)) hdo.symm),
  have H₁ : ((∠ o b c) ≅ₐ (∠ o d c)),
    rw [ang_symm, ang_eq_same_side c (between_same_side_pt.1 hbod).1],
    rw [ang_symm o d c ,←ang_eq_same_side c (between_same_side_pt.1 hbod).2],
    apply isosceles,
    intro hcbd, exact (noncol132 hocd)
      ((col_trans (col132 (between_col hbod)) (col13 hcbd)) hbd.symm),
    exact h₁,
  have H₂ : ((∠ o b a) ≅ₐ (∠ o d a)),
    rw [ang_symm, ang_eq_same_side a (between_same_side_pt.1 hbod).1],
    rw [ang_symm o d a ,←ang_eq_same_side a (between_same_side_pt.1 hbod).2],
    apply isosceles,
    intro habd, exact (noncol13 hoab) (col_trans (col123 habd)
      (col23 (between_col hbod)) hbd),
    exact h₂,
  rcases between_tri hoac (ne.symm hao) (ne.symm hco) hac with h | h | h,
  have ha₁ : inside_ang a (∠ o b c),
    rw inside_three_pt_ang,
    split, refine t_shape_seg hbo _ _ _ _,
    rw line_symm, exact noncol_in12 hobc,
    left, exact h, exact hao,
    refine t_shape_seg hbc _ _ _ _,
    exact noncol_in23 hobc, left, rw between_symm at h, exact h,
    exact hac,
  have ha₂ : same_side_line (d-ₗo) a c,
    apply same_side_line_symm, refine t_shape_seg hdo _ _ _ _,
    rw line_symm, exact noncol_in13 hocd,
    left, exact h, exact hao,
  exact (congr_ang_sub ha₁ ha₂ hdo H₁ H₂).2,
  have hc₁ : inside_ang c (∠ o b a),
    rw inside_three_pt_ang,
    split, refine t_shape_seg hbo _ _ _ _,
    rw line_symm, exact noncol_in13 hoab,
    left, exact h, exact hco,
    refine t_shape_seg hab.symm _ _ _ _,
    rw line_symm, exact noncol_in23 hoab, left, rw between_symm at h, exact h,
    exact hac.symm,
  have hc₂ : same_side_line (d-ₗo) c a,
    apply same_side_line_symm, refine t_shape_seg hdo _ _ _ _,
    rw line_symm, exact noncol_in13 hoad,
    left, exact h, exact hco,
  rw [ang_symm, ang_symm a],
  exact (congr_ang_sub hc₁ hc₂ hdo H₂ H₁).2,
  have ho₁ : inside_ang o (∠ a b c),
    rw inside_three_pt_ang,
    split, refine t_shape_seg hab.symm _ _ _ _,
    rw line_symm, exact noncol_in12 habc,
    left, exact h,
    exact ne.symm hao,
    refine t_shape_seg hbc _ _ _ _,
    exact noncol_in23 habc,
    left, rw between_symm at h, exact h,
    exact ne.symm hco,
  have ho₂ : diff_side_line (d-ₗo) a c,
    use o, exact ⟨pt_right_in_line d o, by {left, exact h}⟩,
    split, rw line_symm, exact noncol_in13 hoad,
    rw line_symm, exact noncol_in13 hocd,
  refine (congr_ang_add ho₁ ho₂ hdo _ _).2,
  rw [ang_symm, ang_symm a _ _], exact H₂,
  exact H₁
end

/--I.7 in Elements -/
lemma triang_same_side_line {a b c d : pts} (hab : a ≠ b) (hcd : same_side_line (a-ₗb) c d)
(hacad : (a-ₛc) ≅ₛ (a-ₛd)) (hbcbd : (b-ₛc) ≅ₛ (b-ₛd)) : c = d :=
begin
  have habc := (same_side_line_noncol hcd hab).1,
  have habd := (same_side_line_noncol hcd hab).2,
  have : ((Δ a b c) ≅ₜ (Δ a b d)),
    apply SSS; unfold three_pt_triang; simp,
    exact habc, exact habd,
    exact seg_congr_refl _, exact hacad, exact hbcbd,
  rw line_symm at hcd,
  have hcd := ang_congr_same_side_unique (tri_congr_ang this).1 (noncol12 habc) hcd,
  exact seg_unique_same_side hcd hacad
end

/--Existence of an isosceles triang 
NOTE : Hilbert axioms do not guarantee the existence of an equilateral triang that occurs 
frequently to prove, for example, the existence of ang bisector. We prove the existence of
an isosceles triang instead which works similarly.
-/
lemma isosceles_exist {a b c : pts} (habc : noncol a b c)
: ∃ d : pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ same_side_line (a-ₗb) c d :=
begin
  have : ∀ {a b c : pts}, noncol a b c → ((∠ c a b) <ₐ (∠ c b a))
    → ∃ d : pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ same_side_line (a-ₗb) c d,
    intros a b c habc h,
    have hab := (noncol_neq habc).1,
    rw ang_symm c b a at h,
    rcases (three_pt_ang_lt.1 h) with ⟨d, hdin, hd⟩,
    cases crossbar hdin with e he,
    have hae : a ≠ e,
      intro hae, rw ←hae at he,
      apply noncol_in12 (ang_nontrivial_iff_noncol.1
        (inside_ang_nontrivial' hdin).1),
      rw line_symm, exact ray_in_line b d he.1,
    have haeb : noncol a e b,
      from col_noncol (col_in12' ((seg_in_line a c) he.2))
        (noncol23 habc) hae,
    use e, split,
    rw [seg_symm, seg_symm b e], apply isosceles' (noncol12 haeb),
    cases seg_in_ray a c he.2 with hace hea,
    rw [ang_symm, ←ang_eq_same_side b hace],
    cases he.1 with hbde heb,
    rw [ang_symm e b a, ←ang_eq_same_side a hbde],
    rw ang_symm, exact ang_congr_symm hd,
    exact absurd heb (noncol_neq haeb).2.2,
    exact absurd hea hae.symm,
    rw line_symm, refine t_shape_seg hab.symm _ _ he.2 hae.symm,
    rw line_symm, exact noncol_in12 habc,
  rcases (ang_tri (ang_nontrivial_iff_noncol.2 (noncol132 habc))
    (ang_nontrivial_iff_noncol.2 (noncol13 habc))).1 with h | h | h,
  exact this habc h,
  use c, split,
  rw [seg_symm, seg_symm b c], exact isosceles' (noncol132 habc) h,
  exact same_side_line_refl (noncol_in12 habc),
  cases this (noncol12 habc) h with d hd,
  rw line_symm at hd, exact ⟨d, seg_congr_symm hd.1, hd.2⟩
end

lemma isosceles_exist' {a b c : pts} (habc : noncol a b c)
: ∃ d : pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ diff_side_line (a-ₗb) c d :=
begin
  cases between_extend (noncol_neq habc).2.1.symm with d hcad,
  have habd := noncol23 (col_noncol
    (col12 (between_col hcad)) (noncol23 habc) (between_neq hcad).2.2),
  cases isosceles_exist habd with e he,
  use e, split, exact he.1,
  have hab := (noncol_neq habc).1,
  apply diff_same_side_line (line_in_lines hab) _ he.2,
  apply (diff_side_pt_line (between_diff_side_pt.1 hcad)).2.2.2 (line_in_lines hab),
  exact ⟨pt_left_in_line a b, noncol_in12 habc, noncol_in12 habd⟩
end

private lemma ang_bisector_exist_prep {a b d e f : pts} : (a-ₛb ≅ₛ (a-ₛd)) → (b-ₛe ≅ₛ (d-ₛe))
→ diff_side_line (b-ₗd) a e → noncol b d a → between a f e → f ∈ (b-ₗd) ∩ (a-ₛe).inside
→ noncol a b e :=
begin
  intros habad hbede he hbda hafe hf,
  have had := (noncol_neq hbda).2.2.symm,
  have hbd := (noncol_neq hbda).1,
  have hae := (between_neq hafe).2.1,
  apply noncol23, apply col_noncol (between_col hafe),
  apply noncol13, apply col_noncol (col_in12' hf.1) hbda,
  intro hbf, rw ←hbf at hafe, 
  cases between_extend had with i hadi,
  have hdi := (between_neq hadi).2.2,
  have hbdi := noncol132 (col_noncol (col12
    (between_col hadi)) (noncol123 hbda) (between_neq hadi).2.2),
  have : ((∠ b d i) ≅ₐ (∠ b d e)),
    rw [seg_symm, seg_symm d e] at hbede,
    have hebd : noncol e b d,
      from λhebd, he.2.2 (col_in23 hebd hbd),
    rw ang_symm b d e, apply ang_congr_trans _ (isosceles hebd hbede),
    rw ang_symm e b d,
    have : ((∠ b d a) ≅ₐ (∠ d b a)),
      rw [ang_symm, ang_symm d b a],
      exact ang_congr_symm (isosceles (noncol132 hbda) habad),
    apply supplementary_congr _ _ this;
    rw three_pt_ang_supplementary,
    exact ⟨hadi, hbda, hbdi⟩,
    split, exact hafe,
    exact ⟨noncol12 hbda, noncol13 hebd⟩,
  have := ang_congr_same_side_unique this hbdi (diff_side_line_cancel (line_in_lines hbd)
    (diff_side_line_symm ((diff_side_pt_line (between_diff_side_pt.1 hadi)).2.2.2
    (line_in_lines hbd) ⟨pt_right_in_line b d, he.2.1, noncol_in12 hbdi⟩)) he),
  apply (noncol13 hbda),
  exact col_trans (col123 (col_trans (col123 (between_col hadi))
    this.2 hdi)) (col23 (between_col hafe)) hae,
  exact hae
end

lemma between_inside_ang {a b c d : pts} (hbac : noncol b a c) :
between b d c → inside_ang d (∠ b a c) :=
begin
  intro hbdc,
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  have hbd := (between_neq hbdc).1,
  have hcd := (between_neq hbdc).2.2.symm,
  rw inside_three_pt_ang, split,
  apply same_side_line_symm,
  apply (same_side_pt_line (between_same_side_pt.1 hbdc).1).2.2.2 (line_in_lines hab),
  have hadb := noncol13 (col_noncol (col23 (between_col hbdc))
    (noncol23 hbac) hbd),
  exact ⟨pt_right_in_line a b, noncol_in13 hadb, noncol_in12 (noncol12 hbac)⟩,
  apply same_side_line_symm,
  apply (same_side_pt_line (same_side_pt_symm (between_same_side_pt.1 hbdc).2)).2.2.2
    (line_in_lines hac),
  have hadc := noncol13 (col_noncol (col132 (between_col hbdc))
    (noncol132 hbac) hcd),
  exact ⟨pt_right_in_line a c, noncol_in13 hadc, noncol_in23 hbac⟩
end

/--I.9 in Elements -/
lemma ang_bisector_exist {a b c : pts} (hbac : ang_nontrivial (∠ b a c)) :
∃ d : pts, ((∠ b a d) ≅ₐ (∠ c a d)) ∧ inside_ang d (∠ b a c) :=
begin
  rw ang_nontrivial_iff_noncol at hbac,
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 hab) hac with ⟨d, hacd, habad, -⟩,
  have had := (same_side_pt_neq hacd).2.symm,
  have hbda : noncol b d a,
    from noncol13 (col_noncol hacd.2 (noncol123 hbac) had),
  have hbd := (noncol_neq hbda).1,
  rcases isosceles_exist' hbda with ⟨e, hbede, he⟩,
  cases he.1 with f hf,
  have hafe : between a f e,
    rcases hf.2 with hafe | hfa | hfe,
    exact hafe,
    rw hfa at hf, exact absurd hf.1 (noncol_in12 hbda),
    simp at hfe, rw hfe at hf,
    exact absurd hf.1 he.2.2,
  have habe := ang_bisector_exist_prep habad hbede he hbda hafe hf,
  have hade : noncol a d e,
    rw line_symm at he, rw line_symm at hf,
    exact ang_bisector_exist_prep (seg_congr_symm habad) (seg_congr_symm hbede)
      he (noncol12 hbda) hafe hf,
  have : (∠ b a f ≅ₐ ∠ c a f),
    rw [ang_eq_same_side b (between_same_side_pt.1 hafe).1,
      ang_eq_same_side c (between_same_side_pt.1 hafe).1],
    have hde := (diff_side_line_neq' he).2.symm,
    rw [ang_symm c a e, ang_eq_same_side e hacd, ang_symm e a d],
    apply (tri_congr_ang _).1, apply SSS; unfold three_pt_triang; simp,
    exact habe, exact hade,
    exact habad, exact seg_congr_refl _, exact hbede,
  use f, split, exact this,
  rw ang_eq_same_side b hacd,
  by_cases hbf : b = f,
    rw ←hbf at hafe, exact absurd (between_col hafe) habe,
  by_cases hdf : d = f,
    rw ←hdf at hafe, exact absurd (between_col hafe) hade,
  have hbdf := col_in12' hf.1,
  have hbaf := noncol23 (col_noncol hbdf hbda hbf),
  have hdaf := noncol23 (col_noncol (col12 hbdf)
    (noncol12 hbda) hdf),
  rw [ang_symm c a f, ang_eq_same_side f hacd, ang_symm f a d] at this,
  rcases between_tri (col_in12' hf.1) hbd hbf hdf with h | h | h,
  exfalso,
  apply (ang_tri (ang_nontrivial_iff_noncol.2 hbaf)
    (ang_nontrivial_iff_noncol.2 hdaf)).2.2.2,
  split, exact this,
  rw [ang_symm b a f, three_pt_ang_lt],
  use d, split, rw between_symm at h,
  exact between_inside_ang (noncol13 hbaf) h,
  rw ang_symm, exact ang_congr_refl _,
  exact between_inside_ang (noncol23 hbda) h,
  exfalso,
  apply (ang_tri (ang_nontrivial_iff_noncol.2 hbaf)
    (ang_nontrivial_iff_noncol.2 hdaf)).2.1,
  split, rw [ang_symm d a f, three_pt_ang_lt],
  use b, split, rw between_symm at h,
  exact between_inside_ang (noncol13 hdaf) h,
  rw ang_symm, exact ang_congr_refl _,
  exact this
end

/--I.10 in Elements -/
lemma midpt_exist {a b : pts} (hab : a ≠ b) : ∃ c : pts, between a c b ∧ ((a-ₛc) ≅ₛ (b-ₛc)) :=
begin
  cases noncol_exist hab with c habc,
  rcases isosceles_exist habc with ⟨d, hd, hcd⟩,
  have hadb := noncol23 (same_side_line_noncol hcd hab).2,
  rcases ang_bisector_exist (ang_nontrivial_iff_noncol.2 hadb) with ⟨e, he, hein⟩,
  cases crossbar hein with f hf,
  rcases hf.2 with h | h | h,
  use f,
  split, exact h,
  simp at h,
  have : ((Δ d a f) ≅ₜ (Δ d b f)),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol132 (col_noncol (col23 (between_col h))
      (noncol23 hadb) (between_neq h).1),
    exact noncol132 (col_noncol (col132 (between_col h))
      (noncol132 hadb) (between_neq h).2.2.symm),
    rw [seg_symm, seg_symm d b], exact hd,
    exact seg_congr_refl _,
    have : same_side_pt d e f,
      cases hf.1 with hf hf, exact hf,
      simp at hf, rw hf at h, exact absurd (between_col h) hadb,
    rw [ang_eq_same_side a this, ang_eq_same_side b this] at he,
    exact he,
  exact (tri_congr_side this).2.2,
  rw h at hf, exfalso,
  have dea := noncol12 (ang_nontrivial_iff_noncol.1
    (inside_ang_nontrivial' hein).1),
  exact noncol_in12 dea ((ray_in_line d e) hf.1),
  simp at h, rw h at hf, exfalso,
  have deb := noncol12 (ang_nontrivial_iff_noncol.1
    (inside_ang_nontrivial' hein).2),
  exact noncol_in12 deb ((ray_in_line d e) hf.1)
end

open_locale perp_notation

/--I.11 in Elements -/
lemma perpendicular_exist_same_side {l : set pts} (hl : l ∈ lines) {a : pts} (hal : a ∈ l)
{b : pts} (hbl : b ∉ l) : ∃ c : pts, (l ⊥ (a-ₗc)) ∧ same_side_line l b c := 
begin
  have : ∃ c : pts, c ∈ l ∧ a ≠ c,
    by_contra hf, push_neg at hf,
    rcases two_pt_on_one_line hl with ⟨p, q, hpq, hpl, hql⟩,
    exact hpq ((hf p hpl).symm.trans (hf q hql)),
  rcases this with ⟨c, hcl, hac⟩,
  rcases extend_congr_seg' (seg_nontrivial_iff_neq.2 hac) hac with ⟨d, hcad, hacad, -⟩,
  rw ←between_diff_side_pt at hcad,
  have hcab : noncol c a b,
    rw two_pt_one_line hl (line_in_lines hac.symm) hac at hbl,
    intro hcab, exact hbl (col_in12 hcab hac.symm),
    exact ⟨hal, hcl⟩, exact ⟨pt_right_in_line c a, pt_left_in_line c a⟩,
  have hcd := (between_neq hcad).2.1,
  have hcdb := col_noncol (between_col hcad) hcab hcd,
  rcases isosceles_exist hcdb with ⟨e, hcecd, hbe⟩,
  use e,
  rw two_pt_one_line hl (line_in_lines hcd) hac
    ⟨hal, hcl⟩ ⟨col_in13 (between_col hcad) hcd, pt_left_in_line c d⟩,
  split, rw between_symm at hcad,
  have hda := (between_neq hcad).1,
  have head : noncol e a d, from noncol13 (col_noncol (col23
    (between_col hcad)) (noncol12 (same_side_line_noncol hbe hcd).2) hda),
  use [d, e, a], rw [ang_symm, three_pt_ang_is_right_ang hcad],
  have : (Δ e a d ≅ₜ Δ e a c),
    apply SSS; unfold three_pt_triang; simp,
    exact head,
    exact noncol13 (col_noncol (col132 (between_col hcad))
      ((same_side_line_noncol hbe hcd).2) hac.symm),
    exact seg_congr_refl _,
    rw [seg_symm, seg_symm e c], exact seg_congr_symm hcecd,
    exact seg_congr_symm hacad,
  rw between_symm at hcad,
  exact ⟨pt_right_in_line c d, pt_right_in_line a e, ⟨col_in13 (between_col hcad) hcd,
    pt_left_in_line a e⟩, (tri_congr_ang this).2.1, ang_nontrivial_iff_noncol.2 head⟩,
  exact ⟨line_in_lines hcd, line_in_lines (noncol_neq head).1.symm⟩,
  exact hbe
end

/--I.12 in Elements -/
lemma drop_perpendicular {l : set pts} (hl : l ∈ lines) {a : pts} (hal : a ∉ l) :
∃ b : pts, l ⊥ (a-ₗb) :=
begin
  rcases two_pt_on_one_line hl with ⟨b, c, hbc, hbl, hcl⟩,
  rw two_pt_one_line hl (line_in_lines hbc) hbc
    ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩ at hal,
  have habc := noncol_in23' hbc hal,
  have hab := (noncol_neq habc).1,
  rcases extend_congr_ang' (ang_nontrivial_iff_noncol.2 habc) hbc hal with ⟨d, habcdbc, hda⟩,
  have hbd := (diff_side_line_neq hda).1.symm,
  rcases extend_congr_seg (seg_nontrivial_iff_neq.2 hab.symm) hbd with ⟨e, hbde, hbabe, -⟩,
  have hea : diff_side_line (b-ₗc) e a,
    apply same_diff_side_line (line_in_lines hbc) _ hda,
    apply (same_side_pt_line (same_side_pt_symm hbde)).2.2.2 (line_in_lines hbc),
    split, exact pt_left_in_line b c,
    split, exact noncol_in13 (col_noncol hbde.2
      (noncol23 (diff_side_line_noncol hda hbc).1) (same_side_pt_neq hbde).2.symm),
    exact noncol_in12 (diff_side_line_noncol hda hbc).1,
  cases hea.1 with f hf,
  rcases hf.2 with hafe | hfe | hfa,
  simp at hafe, rw between_symm at hafe,
  by_cases hbf : b = f,
    rw ←hbf at hafe, use b,
    use [c, a, b],
    split, exact hcl, split, exact pt_left_in_line a b,
    split, exact ⟨hbl, pt_right_in_line a b⟩,
    rw three_pt_ang_is_right_ang hafe,
    have : (Δ b c a ≅ₜ Δ b c e),
      apply SAS; unfold three_pt_triang; simp,
      exact noncol123 habc, exact (diff_side_line_noncol hea hbc).1,
      exact seg_congr_refl _,
      exact hbabe,
      rw [ang_eq_same_side c (same_side_pt_symm hbde), ang_symm, ang_symm c b d],
      exact habcdbc,
    exact ⟨(tri_congr_ang this).1, ang_nontrivial_iff_noncol.2 (noncol13 habc)⟩,
    exact ⟨hl, line_in_lines hab⟩,
  use f, use [b, a, f],
  split, exact hbl, split, exact pt_left_in_line a f,
  split, rw two_pt_one_line hl (line_in_lines hbc) hbc
    ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩,
  exact ⟨hf.1, pt_right_in_line a f⟩,
  rw three_pt_ang_is_right_ang hafe,
  have hfe := (between_neq hafe).2.2,
  have hbfa := col_noncol (col_in12' hf.1) (noncol123 habc) hbf,
  have hbfe := noncol132 ((col_noncol (col23 (col_in23'
      ((seg_in_line e a) hf.2))) (noncol123 hbfa)) hfe),
  have : (Δ b f a ≅ₜ Δ b f e),
    apply SAS; unfold three_pt_triang; simp,
    exact hbfa, exact hbfe,
    exact seg_congr_refl _,
    exact hbabe,
    cases (line_separation (col_in12' hf.1) hbc.symm (ne.symm hbf)).1,
    rw [ang_symm, ←ang_eq_same_side a h, ang_symm f b e, ←ang_eq_same_side e h, ang_symm e b c,
      ang_eq_same_side c (same_side_pt_symm hbde), ang_symm c b d],
    exact habcdbc,
    rw ←between_diff_side_pt at h,
    apply supplementary_congr,
    rw [ang_symm, three_pt_ang_supplementary],
    exact ⟨h, habc, noncol132 hbfa⟩,
    rw [ang_symm, three_pt_ang_supplementary],
    exact ⟨h, noncol132 (diff_side_line_noncol hea hbc).1, noncol132 hbfe⟩,
    rw [ang_symm e b c, ang_eq_same_side c (same_side_pt_symm hbde), ang_symm c b d],
    exact habcdbc,
  exact ⟨(tri_congr_ang this).2.1, ang_nontrivial_iff_noncol.2 hbfa⟩,
  exact ⟨hl, line_in_lines (between_neq hafe).1⟩,
  rw hfe at hf, exact absurd hf.1 (noncol_in12 (diff_side_line_noncol hea hbc).1),
  simp at hfa, rw hfa at hf, exact absurd hf.1 hal
end

private lemma ang_exter_lt_inter_prep {a b c d : pts} (habc : noncol a b c) (hbcd : between b c d) :
∠ b a c <ₐ ∠ a c d :=
begin
  have hac := (noncol_neq habc).2.1,
  have hcd := (between_neq hbcd).2.2,
  have hbc := (noncol_neq habc).2.2,
  have hcda := col_noncol (col12 (between_col hbcd)) (noncol13 habc) hcd,
  rcases midpt_exist hac with ⟨e, haec, he⟩,
  have hae := (between_neq haec).1,
  have hbe : b ≠ e,
    intro hbe, rw ←hbe at haec, exact habc (between_col haec),
  have hec := (between_neq haec).2.2,
  rcases extend_congr_seg' (seg_nontrivial_iff_neq.2 hbe) hbe.symm with ⟨f, hbef, hf, -⟩,
  rw ←between_diff_side_pt at hbef,
  have hef := (between_neq hbef).2.2,
  have hbf := (between_neq hbef).2.1,
  have hceb := col_noncol (col132 (between_col haec)) (noncol132 habc) hec.symm,
  have hefc := col_noncol (col12 (between_col hbef)) (noncol123 hceb) hef,
  have hcaf := col_noncol (col13 (between_col haec)) (noncol132 hefc) hac.symm,
  have haeb := col_noncol (col23 (between_col haec)) (noncol23 habc) hae,
  rw three_pt_ang_lt, use f, split,
  rw inside_three_pt_ang, split,
  apply diff_side_line_cancel (line_in_lines hac.symm),
  apply diff_side_line_symm,
  apply (diff_side_pt_line (between_diff_side_pt.1 hbcd)).2.2.2 (line_in_lines hac.symm),
  exact ⟨pt_left_in_line c a, noncol_in13 (noncol13 habc),
    noncol_in13 (col_noncol (col12 (between_col hbcd)) (noncol13 habc) hcd)⟩,
  apply (diff_side_pt_line (between_diff_side_pt.1 hbef)).2.2.2 (line_in_lines hac.symm),
  exact ⟨col_in13 (col13 (between_col haec)) hac.symm, noncol_in13 (noncol13 habc), noncol_in12 hcaf⟩,
  apply same_side_line_trans (line_in_lines hcd),
  rw line_symm,
  apply t_shape_seg hcd.symm (noncol_in12 (noncol12 hcda)),
  left, rw between_symm at haec, exact haec, exact hec,
  rw two_pt_one_line (line_in_lines hcd) (line_in_lines hbc) hbc
    ⟨col_in23 (between_col hbcd) hcd, pt_left_in_line c d⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩,
  rw line_symm, apply t_shape_ray hbc.symm,
  exact noncol_in13 hceb,
  left, exact (between_same_side_pt.1 hbef).1,
  exact hbf.symm,
  have : (Δ e a b ≅ₜ Δ e c f),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol12 haeb, exact noncol23 hefc,
    rw [seg_symm, seg_symm e c], exact he,
    rw seg_symm, exact hf,
    exact vertical_ang_congr haeb haec hbef,
  rw [ang_symm, ang_eq_same_side f (between_same_side_pt.1 haec).2,
    ←ang_eq_same_side b (between_same_side_pt.1 haec).1, ang_symm, ang_symm b a e],
  exact ang_congr_symm (tri_congr_ang this).2.1
end

/--I.16 in Elements -/
lemma ang_exter_lt_inter {a b c d : pts} (habc : noncol a b c) (hbcd : between b c d) :
(∠ b a c <ₐ ∠ a c d) ∧ (∠ a b c <ₐ ∠ a c d) :=
begin
  split, exact ang_exter_lt_inter_prep habc hbcd,
  have hac := (noncol_neq habc).2.1,
  have hcd := (between_neq hbcd).2.2,
  have hcda := col_noncol (col12 (between_col hbcd)) (noncol13 habc) hcd,
  cases between_extend hac with e hace,
  apply (ang_lt_congr _).2,
  exact (ang_nontrivial_iff_noncol.2 (noncol132 hcda)),
  exact ang_exter_lt_inter_prep (noncol12 habc) hace,
  rw ang_symm,
  apply vertical_ang_congr,
  have hce := (between_neq hace).2.2,
  exact noncol12 (col_noncol (col12 (between_col hace)) (noncol132 habc) hce),
  rw between_symm, exact hace,
  exact hbcd
end

/--I.18 in Elements -/
lemma greater_side_ang {a b c : pts} (habc : noncol a b c) (hs : (a-ₛb) <ₛ (a-ₛc)) :
∠ a c b <ₐ ∠ a b c :=
begin
  have hab := (noncol_neq habc).1,
  have hbc := (noncol_neq habc).2.2,
  rcases two_pt_seg_lt.1 hs with ⟨d, hadc, habad⟩,
  have had := (between_neq hadc).1,
  have hcd := (between_neq hadc).2.2.symm,
  apply ang_lt_trans (ang_nontrivial_iff_noncol.2 (noncol23 habc)),
  rw [ang_symm, ang_eq_same_side b (between_same_side_pt.1 hadc).2],
  rw between_symm at hadc,
  apply (ang_exter_lt_inter _ hadc).2,
  exact noncol132 (col_noncol (col23 (between_col hadc)) (noncol132 habc) hcd),
  apply (ang_lt_congr _).1,
  rw three_pt_ang_lt, use d,
  split, exact hypo_inside_ang habc hadc,
  apply isosceles,
  exact noncol23 (col_noncol (col23 (between_col hadc)) (noncol23 habc) had),
  exact habad,
  rw ang_symm, exact ang_congr_refl _
end

/--I.19 in Elements -/
lemma greater_ang_side {a b c : pts} (habc : noncol a b c) (ha : ∠ a c b <ₐ ∠ a b c) :
(a-ₛb) <ₛ (a-ₛc) :=
begin
  have hab := (noncol_neq habc).1,
  have hac := (noncol_neq habc).2.1,
  rcases (seg_tri (seg_nontrivial_iff_neq.2 hab) (seg_nontrivial_iff_neq.2 hac)).1
    with h | hf | hf,
  exact h,
  exfalso, apply (ang_tri (ang_nontrivial_iff_noncol.2 (noncol23 habc))
    (ang_nontrivial_iff_noncol.2 habc)).2.1,
  split, exact ha,
  exact isosceles (noncol23 habc) (seg_congr_symm hf),
  exfalso, apply (ang_tri (ang_nontrivial_iff_noncol.2 (noncol23 habc))
    (ang_nontrivial_iff_noncol.2 habc)).2.2.1,
  split, exact ha,
  exact greater_side_ang (noncol23 habc) hf
end

/--I.20 in Elements -/
theorem triangular_ineq {a b c d : pts} (habc : noncol a b c) (habd : between a b d)
(hbdbc : (b-ₛd) ≅ₛ (b-ₛc)) : (a-ₛc) <ₛ (a-ₛd) :=
begin
  have had := (between_neq habd).2.1,
  have hbd := (between_neq habd).2.2,
  have hadc := (col_noncol (between_col habd) habc) had,
  have hbdc := (col_noncol (col12 (between_col habd)) (noncol12 habc)) hbd,
  apply greater_ang_side (noncol23 hadc),
  rw [ang_symm a c d, three_pt_ang_lt],
  use b, rw ang_symm, split,
  exact hypo_inside_ang (noncol23 hadc) habd,
  rw [ang_symm a d c, ang_eq_same_side c (between_same_side_pt.1 habd).2, ang_symm, ang_symm c d b],
  exact isosceles (noncol23 hbdc) (seg_congr_symm hbdbc)
end

private lemma ASA_prep {a b c d e f : pts} (habc : noncol a b c) (hdef : noncol d e f)
(habcdef : ∠ a b c ≅ₐ ∠ d e f) (hbacedf : ∠ b a c ≅ₐ ∠ e d f)
(habde : (a-ₛb) ≅ₛ (d-ₛe)) : ¬((d-ₛf) <ₛ (a-ₛc)) :=
begin
  intro hf,
  rw two_pt_seg_lt at hf,
  rcases hf with ⟨x, haxc, hdfax⟩,
  have hax := (between_neq haxc).1,
  have haxb := col_noncol (col23 (between_col haxc)) (noncol23 habc) hax,
  apply (ang_tri (ang_nontrivial_iff_noncol.2 (noncol23 haxb))
    (ang_nontrivial_iff_noncol.2 habc)).2.1,
  split,
  rw three_pt_ang_lt,
  exact ⟨x, hypo_inside_ang habc haxc, ang_congr_refl _⟩,
  apply ang_congr_symm,
  apply ang_congr_trans habcdef,
  have : (Δ a b x ≅ₜ Δ d e f),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol23 haxb, exact hdef,
    exact habde,
    exact seg_congr_symm hdfax,
    rw ang_eq_same_side b (between_same_side_pt.1 haxc).1,
    exact hbacedf,
  exact ang_congr_symm (tri_congr_ang this).2.1
end

/--I.26 part one in Elements -/
theorem ASA {ABC DEF : triang} (habc : noncol ABC.v1 ABC.v2 ABC.v3)
(ha'b'c' : noncol DEF.v1 DEF.v2 DEF.v3) (haba'b' : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2))
(habca'b'c' : (∠ABC.v1 ABC.v2 ABC.v3 ≅ₐ ∠DEF.v1 DEF.v2 DEF.v3))
(hbacb'a'c' : (∠ABC.v2 ABC.v1 ABC.v3 ≅ₐ ∠DEF.v2 DEF.v1 DEF.v3)) : ABC ≅ₜ DEF :=
begin
  set a := ABC.v1 with ha, set b := ABC.v2 with hb, set c := ABC.v3 with hc,
  set a' := DEF.v1, set b' := DEF.v2, set c' := DEF.v3,
  have hac := (noncol_neq habc).2.1,
  have ha'c' := (noncol_neq ha'b'c').2.1,
  apply SAS,
  exact habc, exact ha'b'c',
  exact haba'b',
  rcases (seg_tri (seg_nontrivial_iff_neq.2 hac) (seg_nontrivial_iff_neq.2 ha'c')).1
    with hf | haca'c' | hf,
  exact absurd hf (ASA_prep ha'b'c' habc (ang_congr_symm habca'b'c') (ang_congr_symm hbacb'a'c')
    (seg_congr_symm haba'b')),
  exact haca'c',
  exact absurd hf (ASA_prep habc ha'b'c' habca'b'c' hbacb'a'c' haba'b'),
  exact hbacb'a'c'
end

private lemma AAS_prep {a b c d e f : pts} (habc : noncol a b c) (hdef : noncol d e f)
(habcdef : ∠ a b c ≅ₐ ∠ d e f) (hbacedf : ∠ b a c ≅ₐ ∠ e d f)
(hbcef : (b-ₛc) ≅ₛ (e-ₛf)) : ¬((d-ₛe) <ₛ (a-ₛb)) :=
begin
  intro hf,
  rw [seg_symm a b, two_pt_seg_lt] at hf,
  rcases hf with ⟨x, hbxa, hdebx⟩,
  have hbx := (between_neq hbxa).1,
  have hbxc := col_noncol (col23 (between_col hbxa)) (noncol12 habc) hbx,
  apply (ang_tri (ang_nontrivial_iff_noncol.2 hbxc) (ang_nontrivial_iff_noncol.2 (noncol12 habc))).2.2.2,
  split,
  apply ang_congr_trans _ (ang_congr_symm hbacedf),
  apply (tri_congr_ang _).2.1,
  apply SAS; unfold three_pt_triang; simp,
  exact hbxc, exact noncol12 hdef,
  rw seg_symm e d, exact seg_congr_symm hdebx,
  exact hbcef,
  rw [ang_symm, ang_eq_same_side c (between_same_side_pt.1 hbxa).1, ang_symm],
  exact habcdef,
  rw [ang_symm, ang_eq_same_side c (between_same_side_pt.1 hbxa).2, ang_symm b x c],
  apply (ang_exter_lt_inter _ _).2,
  have hxa := (between_neq hbxa).2.2,
  exact noncol132 (col_noncol (col132 (between_col hbxa)) habc hxa.symm),
  rw between_symm, exact hbxa
end

/--I.26 part two in Elements -/
theorem AAS {ABC DEF : triang} (habc : noncol ABC.v1 ABC.v2 ABC.v3)
(ha'b'c' : noncol DEF.v1 DEF.v2 DEF.v3) (hbcb'c' : (ABC.v2-ₛABC.v3) ≅ₛ (DEF.v2-ₛDEF.v3))
(habca'b'c' : (∠ABC.v1 ABC.v2 ABC.v3 ≅ₐ ∠DEF.v1 DEF.v2 DEF.v3))
(hbacb'a'c' : (∠ABC.v2 ABC.v1 ABC.v3 ≅ₐ ∠DEF.v2 DEF.v1 DEF.v3)) : ABC ≅ₜ DEF :=
begin
  set a := ABC.v1 with ha, set b := ABC.v2 with hb, set c := ABC.v3 with hc,
  set a' := DEF.v1, set b' := DEF.v2, set c' := DEF.v3,
  have hab := (noncol_neq habc).1,
  have ha'b' := (noncol_neq ha'b'c').1,
  apply tri_congr12, apply SAS,
  exact noncol12 habc, exact noncol12 ha'b'c',
  rcases (seg_tri (seg_nontrivial_iff_neq.2 hab) (seg_nontrivial_iff_neq.2 ha'b')).1
    with hf | haba'b' | hf,
  exact absurd hf (AAS_prep ha'b'c' habc (ang_congr_symm habca'b'c') (ang_congr_symm hbacb'a'c')
    (seg_congr_symm hbcb'c')),
  rw [seg_symm, seg_symm a' b'] at haba'b', exact haba'b',
  exact absurd hf (AAS_prep habc ha'b'c' habca'b'c' hbacb'a'c' hbcb'c'),
  exact hbcb'c',
  exact habca'b'c'
end
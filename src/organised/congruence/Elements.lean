import organised.congruence.basic
import organised.congruence.segment_lt
import organised.congruence.angle_lt
import organised.congruence.perpendicular

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--I.5 in Elements -/
theorem isosceles {a b c : pts} (habc : noncollinear a b c) :
((a-ₛb) ≅ₛ (a-ₛc)) → ((∠ a b c) ≅ₐ (∠ a c b)) :=
begin
  intro habac,
  have hab := (noncollinear_neq habc).1,
  have hac := (noncollinear_neq habc).2.1,
  cases is_between_extend hab with d habd,
  cases is_between_extend hac with x hacx,
  have hbd := (is_between_neq habd).2.2,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 hbd)
    (is_between_neq hacx).2.2 with ⟨e, hcxe, hbdce, -⟩,
  have hace := is_between_same_side_pt_is_between hacx hcxe, clear hcxe hacx x,
  have had := (is_between_neq habd).2.1,
  have hae := (is_between_neq hace).2.1,
  have hadc := collinear_noncollinear (is_between_collinear habd) habc had,
  have haeb := collinear_noncollinear (is_between_collinear hace) (noncollinear23 habc) hae,
  have hadcaeb : ((Δ a d c) ≅ₜ (Δ a e b)),
    apply SAS; unfold three_pt_triangle; simp,
    exact hadc, exact haeb,
    exact congr_segment_add habd hace habac hbdce,
    exact segment_congr_symm habac,
    rw [angle_symm, ←angle_eq_same_side c (is_between_same_side_pt.1 habd).1],
    rw [angle_symm, angle_symm e _ _],
    rw angle_eq_same_side b (is_between_same_side_pt.1 hace).1, exact angle_congr_refl _,
  have hce := (is_between_neq hace).2.2,
  have hdbc := collinear_noncollinear (collinear132 (is_between_collinear habd))
    (noncollinear12 hadc) hbd.symm,
  have hecb := collinear_noncollinear (collinear132 (is_between_collinear hace))
    (noncollinear12 haeb) hce.symm,
  have hdbcecb : ((Δ d b c) ≅ₜ (Δ e c b)),
    apply SAS; unfold three_pt_triangle; simp,
    exact hdbc, exact hecb,
    rw [segment_symm, segment_symm e _], exact hbdce,
    exact (tri_congr_side hadcaeb).2.2,
    rw [angle_symm, ←angle_eq_same_side c (is_between_same_side_pt.1 habd).2],
    rw [angle_symm _ e _, ←angle_eq_same_side b (is_between_same_side_pt.1 hace).2],
    rw [angle_symm, angle_symm b _ _],
    exact (tri_congr_angle hadcaeb).2.1,
  have key := (tri_congr_angle hdbcecb).2.1,
  rw [angle_symm, angle_symm e _ _] at key,
  rw [angle_symm, angle_symm a _ _],
  refine supplementary_congr _ _ key;
  rw three_pt_angle_supplementary,
  rw is_between_symm at habd,
  exact ⟨habd, noncollinear13 hdbc, noncollinear13 habc⟩,
    rw is_between_symm at hace,
  exact ⟨hace, noncollinear13 hecb, noncollinear123 habc⟩
end

/--I.6 in Elements -/
theorem isosceles' {a b c : pts} (habc : noncollinear a b c) :
((∠ a b c) ≅ₐ (∠ a c b)) → ((a-ₛb) ≅ₛ (a-ₛc)) :=
begin
  have : ∀ {a b c : pts}, noncollinear a b c → ((∠ a b c) ≅ₐ (∠ a c b)) → ¬((a-ₛb) <ₛ (a-ₛc)),
    intros a b c habc he hf,
    have hab := (noncollinear_neq habc).1,
    have hbc := (noncollinear_neq habc).2.2,
    rw [segment_symm a c, two_pt_segment_lt] at hf,
    rcases hf with ⟨d, hcda, habcd⟩,
    have hcd := (is_between_neq hcda).1,
    have had := (is_between_neq hcda).2.2.symm,
    have hcdb := collinear_noncollinear (collinear23 (is_between_collinear hcda))
        (noncollinear132 habc) hcd,
    have : ((Δ b a c) ≅ₜ (Δ c d b)),
      apply SAS; unfold three_pt_triangle; simp,
      exact noncollinear12 habc, exact hcdb,
      rw segment_symm, exact habcd,
      rw segment_symm, exact segment_congr_refl _,
      rw [angle_symm d c b, angle_eq_same_side b (is_between_same_side_pt.1 hcda).1,
        angle_symm b c a], exact he,
    have : ((∠ d b c) ≅ₐ (∠ a b c)),
      refine angle_congr_trans _ (angle_congr_symm he),
      rw [angle_symm, angle_symm a c b],
      exact angle_congr_symm (tri_congr_angle this).2.2,
    apply (angle_tri (angle_nontrivial_iff_noncollinear.2 (noncollinear123 hcdb))
      (angle_nontrivial_iff_noncollinear.2 habc)).2.1,
    split,
    rw [angle_symm a b c, three_pt_angle_lt],
    use d, split,
    rw inside_three_pt_angle, split,
    refine t_shape_segment hbc (noncollinear_in23 habc) _ _ hcd.symm,
    left, exact hcda,
    refine t_shape_segment hab.symm _ _ _ had.symm,
    rw line_symm, exact noncollinear_in12 habc,
    left, rw is_between_symm at hcda, exact hcda,
    rw angle_symm, exact angle_congr_refl _,
    exact this,
  intro he,
  have hab := (noncollinear_neq habc).1,
  have hac := (noncollinear_neq habc).2.1,
  rcases (segment_tri (segment_nontrivial_iff_neq.2 hab)
    (segment_nontrivial_iff_neq.2 hac)).1 with h | h | h,
  exact absurd h (this habc he),
  exact h,
  exact absurd h (this (noncollinear23 habc) (angle_congr_symm he))
end

/--I.8 in Elements -/
theorem SSS {ABC DEF : triangle} (habc : noncollinear ABC.v1 ABC.v2 ABC.v3)
(ha'b'c' : noncollinear DEF.v1 DEF.v2 DEF.v3) (haba'b' : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2))
(haca'c' : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3)) (hbcb'c' : (ABC.v2-ₛABC.v3) ≅ₛ (DEF.v2-ₛDEF.v3)) :
ABC ≅ₜ DEF :=
begin
  set a := ABC.v1 with ha, set b := ABC.v2 with hb, set c := ABC.v3 with hc,
  set a' := DEF.v1, set b' := DEF.v2, set c' := DEF.v3,
  have hab := (noncollinear_neq habc).1,
  have hac := (noncollinear_neq habc).2.1,
  have hbc := (noncollinear_neq habc).2.2,
  cases is_between_extend hab.symm with x hbax,
  have : x ∉ (a-ₗc), from noncollinear_in13 (collinear_noncollinear
    (collinear12 (is_between_collinear hbax)) habc (is_between_neq hbax).2.2),
  rcases extend_congr_angle (angle_nontrivial_iff_noncollinear.2
    (noncollinear12 ha'b'c')) hac this with ⟨y, hy, hacyx, -⟩,
  have hay : a ≠ y,
    intro hay, rw ←hay at hacyx,
    exact (same_side_line_not_in hacyx).1 (pt_left_in_line a c),
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (noncollinear_neq ha'b'c').1) hay
    with ⟨d, hayd, ha'b'ad, -⟩,
  have had := (same_side_pt_neq hayd).2.symm,
  have hacbd : diff_side_line (a-ₗc) b d,
    have h₁ : diff_side_line (a-ₗc) b x,
      refine (diff_side_pt_line (is_between_diff_side_pt.1 hbax)).2.2.2 _ _,
      exact line_in_lines hac,
      split, exact pt_left_in_line a c, split, exact noncollinear_in13 habc,
      exact noncollinear_in13 (collinear_noncollinear (collinear12 (is_between_collinear hbax))
        habc (is_between_neq hbax).2.2),
    have h₂ : same_side_line (a-ₗc) y d,
      rw line_symm, refine t_shape_ray hac.symm _ _ _ _,
      rw line_symm, exact (same_side_line_not_in hacyx).1,
      left, exact hayd, exact had.symm,
    exact diff_side_same_side_line (line_in_lines hac)
      (diff_side_same_side_line (line_in_lines hac) h₁ (same_side_line_symm hacyx)) h₂,
  have hadc : noncollinear a d c,
    intro hadc, exact hacbd.2.2 ((collinear_in13 hadc) hac),
  have hadca'b'c' : ((Δ a d c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triangle; simp,
    exact hadc, exact ha'b'c',
    exact segment_congr_symm ha'b'ad, exact haca'c',
    have : ∠ y a c = ∠ d a c,
      rw [angle_symm, angle_symm d _ _],
      exact angle_eq_same_side c hayd,
    rw this at hy, exact angle_congr_symm hy,
  refine tri_congr_trans _ hadca'b'c',
  apply tri_congr12, rw [←ha, ←hb, ←hc],
  apply SAS; unfold three_pt_triangle; simp,
  exact noncollinear12 habc, exact noncollinear12 hadc,
  rw segment_symm at haba'b', rw segment_symm d a,
  exact segment_congr_trans haba'b' (segment_congr_symm (tri_congr_side hadca'b'c').1),
  exact segment_congr_trans hbcb'c' (segment_congr_symm (tri_congr_side hadca'b'c').2.2),
  have had := (noncollinear_neq hadc).1,
  have hcd := (noncollinear_neq hadc).2.2.symm,
  have h₁ : ((c-ₛb) ≅ₛ (c-ₛd)),
    rw segment_symm, apply segment_congr_trans hbcb'c',
    rw segment_symm c d, exact segment_congr_symm (tri_congr_side hadca'b'c').2.2,
  have h₂ : ((a-ₛb) ≅ₛ (a-ₛd)),
    apply segment_congr_trans haba'b', exact segment_congr_symm (tri_congr_side hadca'b'c').1,
  have hbd : b ≠ d,
    intro hbd, rw hbd at hacbd, rw ←not_same_side_line at hacbd,
    exact hacbd (same_side_line_refl (noncollinear_in13 hadc)),
    exact noncollinear_in13 hadc, exact noncollinear_in13 hadc,
  cases hacbd.1 with o ho,
  have hbod : is_between b o d,
    cases ho.2, exact h,
    cases h, rw h at ho, exact absurd ho.1 (noncollinear_in13 habc),
    simp at h, rw h at ho, exact absurd ho.1 (noncollinear_in13 hadc),
  by_cases hao : a = o,
    rw ←hao at ho, rw ←hao at hbod,
    have hbad : is_between b a d,
      cases ho.2, exact h, cases h, exact absurd h hab, exact absurd h had,
    rw is_between_same_side_pt at hbad,
    rw [angle_symm, angle_eq_same_side c hbad.1],
    rw [angle_symm a _ _, ←angle_eq_same_side c hbad.2],
    apply isosceles,
    intro hcbd, exact (noncollinear12 hadc) ((collinear_trans
      (collinear132 (is_between_collinear hbod)) (collinear13 hcbd)) hbd.symm),
    exact h₁,
  by_cases hco : c = o,
    rw ←hco at ho, rw ←hco at hbod,
    have hbad : is_between b c d,
      cases ho.2, exact h, cases h, exact absurd h hbc.symm, exact absurd h hcd,
    rw is_between_same_side_pt at hbad,
    rw [angle_eq_same_side a hbad.1, ←angle_eq_same_side a hbad.2],
    apply isosceles,
    intro habd, exact (noncollinear123 hadc)
      ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 habd)) hbd.symm),
    exact h₂,
  have hoac : collinear o a c, from ⟨(a-ₗc), line_in_lines hac, ho.1,
    pt_left_in_line a c, pt_right_in_line a c⟩,
  have hbo := (is_between_neq hbod).1,
  have hdo := (is_between_neq hbod).2.2.symm,
  have hobc : noncollinear o b c, from λhobc, habc (collinear123 (collinear_trans
    (collinear132 hoac) (collinear132 hobc) hco)),
  have hocd : noncollinear o c d, from λhocd, hobc (collinear_trans (collinear123
    (is_between_collinear hbod)) (collinear23 hocd) hdo.symm),
  have hoab : noncollinear o a b,
    from λhoab, habc (collinear_trans (collinear12 hoab) (collinear12 hoac) hao),
  have hoad : noncollinear o a d, from λhoad, hoab (collinear_trans (collinear23 hoad)
    (collinear123 (is_between_collinear hbod)) hdo.symm),
  have H₁ : ((∠ o b c) ≅ₐ (∠ o d c)),
    rw [angle_symm, angle_eq_same_side c (is_between_same_side_pt.1 hbod).1],
    rw [angle_symm o d c ,←angle_eq_same_side c (is_between_same_side_pt.1 hbod).2],
    apply isosceles,
    intro hcbd, exact (noncollinear132 hocd)
      ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 hcbd)) hbd.symm),
    exact h₁,
  have H₂ : ((∠ o b a) ≅ₐ (∠ o d a)),
    rw [angle_symm, angle_eq_same_side a (is_between_same_side_pt.1 hbod).1],
    rw [angle_symm o d a ,←angle_eq_same_side a (is_between_same_side_pt.1 hbod).2],
    apply isosceles,
    intro habd, exact (noncollinear13 hoab) (collinear_trans (collinear123 habd)
      (collinear23 (is_between_collinear hbod)) hbd),
    exact h₂,
  rcases is_between_tri hoac (ne.symm hao) (ne.symm hco) hac with h | h | h,
  have ha₁ : inside_angle a (∠ o b c),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hbo _ _ _ _,
    rw line_symm, exact noncollinear_in12 hobc,
    left, exact h, exact hao,
    refine t_shape_segment hbc _ _ _ _,
    exact noncollinear_in23 hobc, left, rw is_between_symm at h, exact h,
    exact hac,
  have ha₂ : same_side_line (d-ₗo) a c,
    apply same_side_line_symm, refine t_shape_segment hdo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hocd,
    left, exact h, exact hao,
  exact (congr_angle_sub ha₁ ha₂ hdo H₁ H₂).2,
  have hc₁ : inside_angle c (∠ o b a),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hbo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hoab,
    left, exact h, exact hco,
    refine t_shape_segment hab.symm _ _ _ _,
    rw line_symm, exact noncollinear_in23 hoab, left, rw is_between_symm at h, exact h,
    exact hac.symm,
  have hc₂ : same_side_line (d-ₗo) c a,
    apply same_side_line_symm, refine t_shape_segment hdo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hoad,
    left, exact h, exact hco,
  rw [angle_symm, angle_symm a],
  exact (congr_angle_sub hc₁ hc₂ hdo H₂ H₁).2,
  have ho₁ : inside_angle o (∠ a b c),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hab.symm _ _ _ _,
    rw line_symm, exact noncollinear_in12 habc,
    left, exact h,
    exact ne.symm hao,
    refine t_shape_segment hbc _ _ _ _,
    exact noncollinear_in23 habc,
    left, rw is_between_symm at h, exact h,
    exact ne.symm hco,
  have ho₂ : diff_side_line (d-ₗo) a c,
    use o, exact ⟨pt_right_in_line d o, by {left, exact h}⟩,
    split, rw line_symm, exact noncollinear_in13 hoad,
    rw line_symm, exact noncollinear_in13 hocd,
  refine (congr_angle_add ho₁ ho₂ hdo _ _).2,
  rw [angle_symm, angle_symm a _ _], exact H₂,
  exact H₁
end

/--I.7 in Elements -/
lemma triangle_same_side_line {a b c d : pts} (hab : a ≠ b) (hcd : same_side_line (a-ₗb) c d)
(hacad : (a-ₛc) ≅ₛ (a-ₛd)) (hbcbd : (b-ₛc) ≅ₛ (b-ₛd)) : c = d :=
begin
  have habc := (same_side_line_noncollinear hcd hab).1,
  have habd := (same_side_line_noncollinear hcd hab).2,
  have : ((Δ a b c) ≅ₜ (Δ a b d)),
    apply SSS; unfold three_pt_triangle; simp,
    exact habc, exact habd,
    exact segment_congr_refl _, exact hacad, exact hbcbd,
  rw line_symm at hcd,
  have hcd := angle_congr_same_side_unique (tri_congr_angle this).1 (noncollinear12 habc) hcd,
  exact segment_unique_same_side hcd hacad
end

/--Existence of an isosceles triangle 
NOTE : Hilbert axioms do not guarantee the existence of an equilateral triangle that occurs 
frequently to prove, for example, the existence of angle bisector. We prove the existence of
an isosceles triangle instead which works similarly.
-/
lemma isosceles_exist {a b c : pts} (habc : noncollinear a b c)
: ∃ d : pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ same_side_line (a-ₗb) c d :=
begin
  have : ∀ {a b c : pts}, noncollinear a b c → ((∠ c a b) <ₐ (∠ c b a))
    → ∃ d : pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ same_side_line (a-ₗb) c d,
    intros a b c habc h,
    have hab := (noncollinear_neq habc).1,
    rw angle_symm c b a at h,
    rcases (three_pt_angle_lt.1 h) with ⟨d, hdin, hd⟩,
    cases crossbar hdin with e he,
    have hae : a ≠ e,
      intro hae, rw ←hae at he,
      apply noncollinear_in12 (angle_nontrivial_iff_noncollinear.1
        (inside_angle_nontrivial' hdin).1),
      rw line_symm, exact ray_in_line b d he.1,
    have haeb : noncollinear a e b,
      from collinear_noncollinear (collinear_in12' ((segment_in_line a c) he.2))
        (noncollinear23 habc) hae,
    use e, split,
    rw [segment_symm, segment_symm b e], apply isosceles' (noncollinear12 haeb),
    cases segment_in_ray a c he.2 with hace hea,
    rw [angle_symm, ←angle_eq_same_side b hace],
    cases he.1 with hbde heb,
    rw [angle_symm e b a, ←angle_eq_same_side a hbde],
    rw angle_symm, exact angle_congr_symm hd,
    exact absurd heb (noncollinear_neq haeb).2.2,
    exact absurd hea hae.symm,
    rw line_symm, refine t_shape_segment hab.symm _ _ he.2 hae.symm,
    rw line_symm, exact noncollinear_in12 habc,
  rcases (angle_tri (angle_nontrivial_iff_noncollinear.2 (noncollinear132 habc))
    (angle_nontrivial_iff_noncollinear.2 (noncollinear13 habc))).1 with h | h | h,
  exact this habc h,
  use c, split,
  rw [segment_symm, segment_symm b c], exact isosceles' (noncollinear132 habc) h,
  exact same_side_line_refl (noncollinear_in12 habc),
  cases this (noncollinear12 habc) h with d hd,
  rw line_symm at hd, exact ⟨d, segment_congr_symm hd.1, hd.2⟩
end

lemma isosceles_exist' {a b c : pts} (habc : noncollinear a b c)
: ∃ d : pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ diff_side_line (a-ₗb) c d :=
begin
  cases is_between_extend (noncollinear_neq habc).2.1.symm with d hcad,
  have habd := noncollinear23 (collinear_noncollinear
    (collinear12 (is_between_collinear hcad)) (noncollinear23 habc) (is_between_neq hcad).2.2),
  cases isosceles_exist habd with e he,
  use e, split, exact he.1,
  have hab := (noncollinear_neq habc).1,
  apply diff_side_same_side_line (line_in_lines hab) _ he.2,
  apply (diff_side_pt_line (is_between_diff_side_pt.1 hcad)).2.2.2 (line_in_lines hab),
  exact ⟨pt_left_in_line a b, noncollinear_in12 habc, noncollinear_in12 habd⟩
end

private lemma angle_bisector_exist_prep {a b d e f : pts} : (a-ₛb ≅ₛ (a-ₛd)) → (b-ₛe ≅ₛ (d-ₛe))
→ diff_side_line (b-ₗd) a e → noncollinear b d a → is_between a f e → f ∈ (b-ₗd) ∩ (a-ₛe).inside
→ noncollinear a b e :=
begin
  intros habad hbede he hbda hafe hf,
  have had := (noncollinear_neq hbda).2.2.symm,
  have hbd := (noncollinear_neq hbda).1,
  have hae := (is_between_neq hafe).2.1,
  apply noncollinear23, apply collinear_noncollinear (is_between_collinear hafe),
  apply noncollinear13, apply collinear_noncollinear (collinear_in12' hf.1) hbda,
  intro hbf, rw ←hbf at hafe, 
  cases is_between_extend had with i hadi,
  have hdi := (is_between_neq hadi).2.2,
  have hbdi := noncollinear132 (collinear_noncollinear (collinear12
    (is_between_collinear hadi)) (noncollinear123 hbda) (is_between_neq hadi).2.2),
  have : ((∠ b d i) ≅ₐ (∠ b d e)),
    rw [segment_symm, segment_symm d e] at hbede,
    have hebd : noncollinear e b d,
      from λhebd, he.2.2 (collinear_in23 hebd hbd),
    rw angle_symm b d e, apply angle_congr_trans _ (isosceles hebd hbede),
    rw angle_symm e b d,
    have : ((∠ b d a) ≅ₐ (∠ d b a)),
      rw [angle_symm, angle_symm d b a],
      exact angle_congr_symm (isosceles (noncollinear132 hbda) habad),
    apply supplementary_congr _ _ this;
    rw three_pt_angle_supplementary,
    exact ⟨hadi, hbda, hbdi⟩,
    split, exact hafe,
    exact ⟨noncollinear12 hbda, noncollinear13 hebd⟩,
  have := angle_congr_same_side_unique this hbdi (diff_side_line_cancel (line_in_lines hbd)
    (diff_side_line_symm ((diff_side_pt_line (is_between_diff_side_pt.1 hadi)).2.2.2
    (line_in_lines hbd) ⟨pt_right_in_line b d, he.2.1, noncollinear_in12 hbdi⟩)) he),
  apply (noncollinear13 hbda),
  exact collinear_trans (collinear123 (collinear_trans (collinear123 (is_between_collinear hadi))
    this.2 hdi)) (collinear23 (is_between_collinear hafe)) hae,
  exact hae
end

lemma is_between_inside_angle {a b c d : pts} (hbac : noncollinear b a c) :
is_between b d c → inside_angle d (∠ b a c) :=
begin
  intro hbdc,
  have hab := (noncollinear_neq hbac).1.symm,
  have hac := (noncollinear_neq hbac).2.2,
  have hbd := (is_between_neq hbdc).1,
  have hcd := (is_between_neq hbdc).2.2.symm,
  rw inside_three_pt_angle, split,
  apply same_side_line_symm,
  apply (same_side_pt_line (is_between_same_side_pt.1 hbdc).1).2.2.2 (line_in_lines hab),
  have hadb := noncollinear13 (collinear_noncollinear (collinear23 (is_between_collinear hbdc))
    (noncollinear23 hbac) hbd),
  exact ⟨pt_right_in_line a b, noncollinear_in13 hadb, noncollinear_in12 (noncollinear12 hbac)⟩,
  apply same_side_line_symm,
  apply (same_side_pt_line (same_side_pt_symm (is_between_same_side_pt.1 hbdc).2)).2.2.2
    (line_in_lines hac),
  have hadc := noncollinear13 (collinear_noncollinear (collinear132 (is_between_collinear hbdc))
    (noncollinear132 hbac) hcd),
  exact ⟨pt_right_in_line a c, noncollinear_in13 hadc, noncollinear_in23 hbac⟩
end

/--I.9 in Elements -/
lemma angle_bisector_exist {a b c : pts} (hbac : angle_nontrivial (∠ b a c)) :
∃ d : pts, ((∠ b a d) ≅ₐ (∠ c a d)) ∧ inside_angle d (∠ b a c) :=
begin
  rw angle_nontrivial_iff_noncollinear at hbac,
  have hab := (noncollinear_neq hbac).1.symm,
  have hac := (noncollinear_neq hbac).2.2,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 hab) hac with ⟨d, hacd, habad, -⟩,
  have had := (same_side_pt_neq hacd).2.symm,
  have hbda : noncollinear b d a,
    from noncollinear13 (collinear_noncollinear hacd.2 (noncollinear123 hbac) had),
  have hbd := (noncollinear_neq hbda).1,
  rcases isosceles_exist' hbda with ⟨e, hbede, he⟩,
  cases he.1 with f hf,
  have hafe : is_between a f e,
    rcases hf.2 with hafe | hfa | hfe,
    exact hafe,
    rw hfa at hf, exact absurd hf.1 (noncollinear_in12 hbda),
    simp at hfe, rw hfe at hf,
    exact absurd hf.1 he.2.2,
  have habe := angle_bisector_exist_prep habad hbede he hbda hafe hf,
  have hade : noncollinear a d e,
    rw line_symm at he, rw line_symm at hf,
    exact angle_bisector_exist_prep (segment_congr_symm habad) (segment_congr_symm hbede)
      he (noncollinear12 hbda) hafe hf,
  have : (∠ b a f ≅ₐ ∠ c a f),
    rw [angle_eq_same_side b (is_between_same_side_pt.1 hafe).1,
      angle_eq_same_side c (is_between_same_side_pt.1 hafe).1],
    have hde := (diff_side_line_neq' he).2.symm,
    rw [angle_symm c a e, angle_eq_same_side e hacd, angle_symm e a d],
    apply (tri_congr_angle _).1, apply SSS; unfold three_pt_triangle; simp,
    exact habe, exact hade,
    exact habad, exact segment_congr_refl _, exact hbede,
  use f, split, exact this,
  rw angle_eq_same_side b hacd,
  by_cases hbf : b = f,
    rw ←hbf at hafe, exact absurd (is_between_collinear hafe) habe,
  by_cases hdf : d = f,
    rw ←hdf at hafe, exact absurd (is_between_collinear hafe) hade,
  have hbdf := collinear_in12' hf.1,
  have hbaf := noncollinear23 (collinear_noncollinear hbdf hbda hbf),
  have hdaf := noncollinear23 (collinear_noncollinear (collinear12 hbdf)
    (noncollinear12 hbda) hdf),
  rw [angle_symm c a f, angle_eq_same_side f hacd, angle_symm f a d] at this,
  rcases is_between_tri (collinear_in12' hf.1) hbd hbf hdf with h | h | h,
  exfalso,
  apply (angle_tri (angle_nontrivial_iff_noncollinear.2 hbaf)
    (angle_nontrivial_iff_noncollinear.2 hdaf)).2.2.2,
  split, exact this,
  rw [angle_symm b a f, three_pt_angle_lt],
  use d, split, rw is_between_symm at h,
  exact is_between_inside_angle (noncollinear13 hbaf) h,
  rw angle_symm, exact angle_congr_refl _,
  exact is_between_inside_angle (noncollinear23 hbda) h,
  exfalso,
  apply (angle_tri (angle_nontrivial_iff_noncollinear.2 hbaf)
    (angle_nontrivial_iff_noncollinear.2 hdaf)).2.1,
  split, rw [angle_symm d a f, three_pt_angle_lt],
  use b, split, rw is_between_symm at h,
  exact is_between_inside_angle (noncollinear13 hdaf) h,
  rw angle_symm, exact angle_congr_refl _,
  exact this
end

/--I.10 in Elements -/
lemma midpt_exist {a b : pts} (hab : a ≠ b) : ∃ c : pts, is_between a c b ∧ ((a-ₛc) ≅ₛ (b-ₛc)) :=
begin
  cases noncollinear_exist hab with c habc,
  rcases isosceles_exist habc with ⟨d, hd, hcd⟩,
  have hadb := noncollinear23 (same_side_line_noncollinear hcd hab).2,
  rcases angle_bisector_exist (angle_nontrivial_iff_noncollinear.2 hadb) with ⟨e, he, hein⟩,
  cases crossbar hein with f hf,
  rcases hf.2 with h | h | h,
  use f,
  split, exact h,
  simp at h,
  have : ((Δ d a f) ≅ₜ (Δ d b f)),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear132 (collinear_noncollinear (collinear23 (is_between_collinear h))
      (noncollinear23 hadb) (is_between_neq h).1),
    exact noncollinear132 (collinear_noncollinear (collinear132 (is_between_collinear h))
      (noncollinear132 hadb) (is_between_neq h).2.2.symm),
    rw [segment_symm, segment_symm d b], exact hd,
    exact segment_congr_refl _,
    have : same_side_pt d e f,
      cases hf.1 with hf hf, exact hf,
      simp at hf, rw hf at h, exact absurd (is_between_collinear h) hadb,
    rw [angle_eq_same_side a this, angle_eq_same_side b this] at he,
    exact he,
  exact (tri_congr_side this).2.2,
  rw h at hf, exfalso,
  have dea := noncollinear12 (angle_nontrivial_iff_noncollinear.1
    (inside_angle_nontrivial' hein).1),
  exact noncollinear_in12 dea ((ray_in_line d e) hf.1),
  simp at h, rw h at hf, exfalso,
  have deb := noncollinear12 (angle_nontrivial_iff_noncollinear.1
    (inside_angle_nontrivial' hein).2),
  exact noncollinear_in12 deb ((ray_in_line d e) hf.1)
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
  rcases extend_congr_segment' (segment_nontrivial_iff_neq.2 hac) hac with ⟨d, hcad, hacad, -⟩,
  rw ←is_between_diff_side_pt at hcad,
  have hcab : noncollinear c a b,
    rw two_pt_one_line hl (line_in_lines hac.symm) hac at hbl,
    intro hcab, exact hbl (collinear_in12 hcab hac.symm),
    exact ⟨hal, hcl⟩, exact ⟨pt_right_in_line c a, pt_left_in_line c a⟩,
  have hcd := (is_between_neq hcad).2.1,
  have hcdb := collinear_noncollinear (is_between_collinear hcad) hcab hcd,
  rcases isosceles_exist hcdb with ⟨e, hcecd, hbe⟩,
  use e,
  rw two_pt_one_line hl (line_in_lines hcd) hac
    ⟨hal, hcl⟩ ⟨collinear_in13 (is_between_collinear hcad) hcd, pt_left_in_line c d⟩,
  split, rw is_between_symm at hcad,
  have hda := (is_between_neq hcad).1,
  have head : noncollinear e a d, from noncollinear13 (collinear_noncollinear (collinear23
    (is_between_collinear hcad)) (noncollinear12 (same_side_line_noncollinear hbe hcd).2) hda),
  use [d, e, a], rw [angle_symm, three_pt_angle_is_right_angle hcad],
  have : (Δ e a d ≅ₜ Δ e a c),
    apply SSS; unfold three_pt_triangle; simp,
    exact head,
    exact noncollinear13 (collinear_noncollinear (collinear132 (is_between_collinear hcad))
      ((same_side_line_noncollinear hbe hcd).2) hac.symm),
    exact segment_congr_refl _,
    rw [segment_symm, segment_symm e c], exact segment_congr_symm hcecd,
    exact segment_congr_symm hacad,
  rw is_between_symm at hcad,
  exact ⟨pt_right_in_line c d, pt_right_in_line a e, ⟨collinear_in13 (is_between_collinear hcad) hcd,
    pt_left_in_line a e⟩, (tri_congr_angle this).2.1, angle_nontrivial_iff_noncollinear.2 head⟩,
  exact ⟨line_in_lines hcd, line_in_lines (noncollinear_neq head).1.symm⟩,
  exact hbe
end

lemma drop_perpendicular {l : set pts} (hl : l ∈ lines) {a : pts} (hal : a ∉ l) : ∃ b : pts, l ⊥ (a-ₗb) :=
begin
  rcases two_pt_on_one_line hl with ⟨b, c, hbc, hbl, hcl⟩,
  rw two_pt_one_line hl (line_in_lines hbc) hbc ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩ at hal,
  have habc := noncollinear_in23' hbc hal,
  have hab := (noncollinear_neq habc).1,
  rcases extend_congr_angle' (angle_nontrivial_iff_noncollinear.2 habc) hbc hal with ⟨d, habcdbc, hda⟩,
  have hbd := (diff_side_line_neq hda).1.symm,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 hab.symm) hbd with ⟨e, hbde, hbabe, -⟩,
  cases hda.1 with f hf,
  rcases hf.2 with hf | hf | hf,
  simp at hf, rw is_between_symm at hf,
  by_cases hbf : b = f,
    rw ←hbf at hf, use b,
    use [c, a, b],
    split, exact hcl, split, exact pt_left_in_line a b,
    split, exact ⟨hbl, pt_right_in_line a b⟩,
    rw three_pt_angle_is_right_angle hf,
    have : (Δ b c a ≅ₜ Δ b c d),
      apply SAS; unfold three_pt_triangle; simp,
      exact noncollinear123 habc, exact (diff_side_line_noncollinear hda hbc).1,
      exact segment_congr_refl _,
      
  use f, use [b, a, f],
  split, exact hbl,
  split, exact pt_left_in_line a f,
  split, rw two_pt_one_line hl (line_in_lines hbc) hbc ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩,
  exact ⟨hf.1, pt_right_in_line a f⟩,
  simp at hf, rw is_between_symm at hf,
  rw three_pt_angle_is_right_angle hf,
end
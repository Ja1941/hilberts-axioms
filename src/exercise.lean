/-Some geometry exercises I did during high school
  I will be gradually adding more of them here -/

import congruence.Elements

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

example {a b c d e f : pts} (habc : noncol a b c) (hd : midpt d (b-ₛc)) (haed : between a e d)     
(hbef : between b e f) (hafc : between a f c) (hbeac : (b-ₛe) ≅ₛ (a-ₛc)) : (a-ₛf) ≅ₛ (e-ₛf) :=
begin
  rw midpt_two_pt at hd,
  have hbd := (between_neq hd.1).1,
  have hcd := (between_neq hd.1).2.2.symm,
  have hbda := col_noncol (col23 (between_col hd.1)) (noncol123 habc) hbd,
  have hcda := col_noncol (col132 (between_col hd.1)) (noncol13 habc) hcd,
  have hda := (noncol_neq hcda).2.2,
  rcases extend_congr_seg' (seg_proper_iff_neq.2 hda) hda with ⟨g, hadg, hdadg, -⟩,
  rw ←between_diff_side_pt at hadg,
  have hdg := (between_neq hadg).2.2,
  rw [seg_symm, seg_symm e f],
  have haf := (between_neq hafc).1,
  have hae := (between_neq haed).1,
  have haec := col_noncol (col23 (between_col haed)) (noncol13 hcda) hae,
  have hafe := col_noncol (col23 (between_col hafc)) (noncol23 haec) haf,
  have hdgb := col_noncol (col12 (between_col hadg)) (noncol123 hbda) hdg,
  apply isosceles' (noncol12 hafe),
  have : ((Δ d a c) ≅ₜ (Δ d g b)),
    apply SAS; unfold three_pt_triang; simp,
    exact noncol123 hcda, exact hdgb,
    exact hdadg,
    rw [seg_symm, seg_symm d b], exact seg_congr_symm hd.2,
    { apply vertical_ang_congr (noncol13 hcda) hadg,
      rw between_symm, exact hd.1 },
  rw [ang_symm, ang_eq_same_side_pt e (between_same_side_pt.1 hafc).1, ang_symm,
      ang_eq_same_side_pt c (between_same_side_pt.1 haed).1, ang_symm],
  apply ang_congr_trans (tri_congr_ang this).1,
  rw between_symm at haed hadg,
  have hgde := (between_trans' hadg haed).1,
  have hge := (between_neq hgde).2.1,
  have hgeb := col_noncol (between_col hgde) (noncol12 hdgb) hge,
  rw [ang_symm, ang_eq_same_side_pt b (between_same_side_pt.1 hgde).1],
  apply ang_congr_trans,
  { apply isosceles (noncol132 hgeb),
    rw seg_symm,
    exact seg_congr_trans (seg_congr_symm (tri_congr_seg this).2.2) (seg_congr_symm hbeac) },
  exact vertical_ang_congr (noncol13 hgeb) hbef (between_trans' hadg haed).2
end

example {a b c p d e f q : pts} (habc : noncol a b c) (hdef : noncol d e f) (hbpc : col b p c)
(heqf : col e q f) (hapb : is_right_ang (∠ a p b)) (hdqe : is_right_ang (∠ d q e))
(habde : (a-ₛb) ≅ₛ (d-ₛe)) (hacdf : (a-ₛc) ≅ₛ (d-ₛf)) (hapdq : (a-ₛp) ≅ₛ (d-ₛq)) :
((∠ a b c) ≅ₐ (∠ d e f)) ∨ ∃ α : ang, ((α ≅ₐ (∠ a b c)) ∧ supplementary α (∠ d e f)) :=
begin
  sorry
end

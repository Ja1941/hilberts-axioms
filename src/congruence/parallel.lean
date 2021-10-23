/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import congruence.Elements

/-!
# Parallelism

This file defines how two lines are parallel and proves properties
of parallel lines such as alternative angles.

## Main definitions

* `is_parallel` means the two lines have no intersections
* `hilbert_plane_playfair` is a class extended `hilbert_plane` with
  Playfair axiom that deals with parallelism

## References

* See [Geometry: Euclid and Beyond]

-/

/--We can add Playfair axiom to Hilbert plane so that given a line and a point,
we can find a unique parallel line containing this point. -/
class hilbert_plane_playfair extends hilbert_plane :=
(P : ∀ (a : pts) (l ∈ lines), (∃ l' ∈ lines, a ∈ l' ∧ (l ∥ₗ l'))
∧ (∀ m n ∈ lines, a ∈ m → (l ∥ₗ m) → a ∈ n → (l ∥ₗ n) → m = n))

open incidence_geometry incidence_order_geometry hilbert_plane hilbert_plane_playfair

variables [CP : hilbert_plane_playfair]

include CP

lemma parallel_exist {l : set pts} (a : pts) (hl : l ∈ lines) :
∃ l' ∈ lines, a ∈ l' ∧ (l ∥ₗ l') :=
by {rcases (P a l hl).1 with ⟨l', hl', hal', hll'⟩, exact ⟨l', hl', hal', hll'⟩}

lemma parallel_unique {a : pts} {l m n : set pts} (hl : l ∈ lines) :
m ∈ lines → n ∈ lines → a ∈ m → (l ∥ₗ m) → a ∈ n → (l ∥ₗ n) → m = n :=
(P a l hl).2 m n

private lemma correspond_eq_iff_parallel_prep {a b c d e : pts}
(hab : a ≠ b) (hcd : c ≠ d) (hcae : between c a e) (hbd : same_side_line (a-ₗc) b d) :
((∠ e a b) <ₐ (∠ a c d)) → ¬((a-ₗb) ∥ₗ (c-ₗd)) :=
begin
  have hac := (between_neq hcae).1.symm,
  intros h hf,
  rcases (three_pt_ang_lt.1 h) with ⟨p, hp, key⟩,
  rw [inside_three_pt_ang, line_symm] at hp,
  have hbp := same_side_line_trans (line_in_lines hac) hbd hp.1, 
  have hcp := (same_side_line_neq' hbp).2.symm,
  have habcp := correspond_eq_parallel hab hcp hcae hbp (ang_congr_symm key),
  have hcdcp := parallel_unique (line_in_lines hab) (line_in_lines hcd) (line_in_lines hcp)
    (pt_left_in_line c d) hf (pt_left_in_line c p) habcp,
  have hcdp : col c d p,
    apply col_in12', rw hcdcp, exact pt_right_in_line c p,
  have hacd := (same_side_line_noncol hbd hac).2,
  have hacp := (same_side_line_noncol hbp hac).2,
  have hcdp := same_side_line_pt hcdp (a-ₗc) (line_in_lines hac) (pt_right_in_line a c)
    (noncol_in12 hacd) (noncol_in12 hacp) hp.1,
  rw ←ang_eq_same_side_pt a hcdp at key,
  have hac := (between_neq hcae).1.symm,
  have hacb := (same_side_line_noncol hbd hac).1,
  have hae := (between_neq hcae).2.2,
  have haeb := col_noncol (col12 (between_col hcae)) hacb hae,
  apply (ang_tri (ang_proper_iff_noncol.2 (noncol12 haeb))
    (ang_proper_iff_noncol.2 hacd)).2.1,
  exact ⟨h, ang_congr_symm key⟩
end

lemma correspond_eq_iff_parallel {a b c d e : pts}
(hab : a ≠ b) (hcd : c ≠ d) (hcae : between c a e) (hbd : same_side_line (a-ₗc) b d) :
((∠ e a b) ≅ₐ (∠ a c d)) ↔ ((a-ₗb) ∥ₗ (c-ₗd)) :=
begin
  split; intro h,
  exact correspond_eq_parallel hab hcd hcae hbd h,
  { have hac := (between_neq hcae).1.symm,
    have hacb := (same_side_line_noncol hbd hac).1,
    have hae := (between_neq hcae).2.2,
    have haeb := col_noncol (col12 (between_col hcae)) hacb hae,
    have hacd := (same_side_line_noncol hbd hac).2,
    rcases (ang_tri (ang_proper_iff_noncol.2 (noncol12 haeb))
      (ang_proper_iff_noncol.2 hacd)).1 with hf | h | hf,
    exfalso, exact correspond_eq_iff_parallel_prep hab hcd hcae hbd hf h,
    exact h,
    { rcases between_extend hab.symm with ⟨b', hbab'⟩,
      rcases between_extend hcd.symm with ⟨d', hdcd'⟩,
      exfalso,
      have hab' := (between_neq hbab').2.2,
      have hcd' := (between_neq hdcd').2.2,
      have hab'c := col_noncol (col12 (between_col hbab')) (noncol23 hacb) hab',
      have had'c := col_noncol (col12 (between_col hdcd')) (noncol123 hacd) hcd',
      apply correspond_eq_iff_parallel_prep hab' hcd' hcae _ _ _,
      { have hbb' := diff_side_pt_line (between_diff_side_pt.1 hbab') (line_in_lines hac)
          (pt_left_in_line a c) (noncol_in12 hacb) (noncol_in13 hab'c),
        have hdd' := diff_side_pt_line (between_diff_side_pt.1 hdcd') (line_in_lines hac)
          (pt_right_in_line a c) (noncol_in12 hacd) (noncol_in31 had'c),
        apply diff_side_line_cancel (line_in_lines hac) (diff_side_line_symm hbb'),
        exact same_diff_side_line (line_in_lines hac) hbd hdd', },
      { apply ang_lt_supplementary hf; rw three_pt_ang_supplementary,
        exact ⟨hdcd', hacd, noncol132 had'c⟩,
        exact ⟨hbab', noncol12 haeb, noncol132
          (col_noncol (col12 (between_col hbab')) (noncol23 haeb) hab')⟩ },
      { rw two_pt_one_line (line_in_lines hab') (line_in_lines hab) hab (pt_left_in_line a b')
          (col_in23 (between_col hbab') hab') (pt_left_in_line a b) (pt_right_in_line a b),
        rw two_pt_one_line (line_in_lines hcd') (line_in_lines hcd) hcd (pt_left_in_line c d')
          (col_in23 (between_col hdcd') hcd') (pt_left_in_line c d) (pt_right_in_line c d),
        exact h  } } }
end

lemma alternative_eq_iff_parallel {a b c d : pts}
(hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (hbd : diff_side_line (a-ₗc) b d) :
((∠ b a c) ≅ₐ (∠ d c a)) ↔ ((a-ₗb) ∥ₗ (c-ₗd)) :=
begin
  cases between_extend hab.symm with b' hbab',
  cases between_extend hac.symm with c' hcac',
  have hab' := (between_neq hbab').2.2,
  have hbac := noncol_in23' hac hbd.2.1,
  have hab'c := col_noncol (col12 (between_col hbab')) (noncol12 hbac) hab',
  have hbd' : same_side_line (a-ₗc) b' d,
    apply diff_side_line_cancel (line_in_lines hac) _ hbd,
    apply diff_side_line_symm,
    apply diff_side_pt_line (between_diff_side_pt.1 hbab') (line_in_lines hac)
      (pt_left_in_line a c) hbd.2.1 (noncol_in13 hab'c),
  have := correspond_eq_iff_parallel hab' hcd hcac' hbd',
  rw two_pt_one_line (line_in_lines hab') (line_in_lines hab) hab (pt_left_in_line a b')
    (col_in23 (between_col hbab') hab') (pt_left_in_line a b) (pt_right_in_line a b) at this,
  rw ←this,
  have := vertical_ang_congr hbac hbab' hcac',
  split; intro h,
  rw [ang_symm, ang_symm a c d], exact ang_congr_trans (ang_congr_symm this) h,
  rw ang_symm d c a, rw ang_symm at h, exact ang_congr_trans this h
end

/--Some hints for Tchsurvives:
  1. extend_congr_seg'
  2. SAS
  3. alternative_eq_iff_parallel
  4. ASA -/
lemma midpoint {a b c d e : pts} (habc : noncol a b c) (hadb : between a d b)
(haec : between a e c) (hd : midpt d (a-ₛb)) : (midpt e (a-ₛc)) ↔ ((d-ₗe) ∥ₗ (b-ₗc)) :=
begin
  sorry
end

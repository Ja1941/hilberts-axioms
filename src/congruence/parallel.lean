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
      rcases between_extend hcd.symm with ⟨d', hdad'⟩,
      sorry } }
end

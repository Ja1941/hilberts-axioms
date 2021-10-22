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

## References

* See [Geometry: Euclid and Beyond]

-/

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--Two lines are parallel if they have no intersection. -/
def is_parallel (l₁ l₂ : set pts) : Prop :=
¬(l₁ ♥ l₂) ∧ (l₁ ∈ lines) ∧ (l₂ ∈ lines)

notation l₁`∥ₗ`l₂ := is_parallel l₁ l₂
/-
private lemma alter_eq_iff_parallel_prep {a b c d e f g p : pts} (hab : a ≠ b) (hcd : c ≠ d)
(hef : e ≠ f) (he : e ∈ (a-ₗb)) (hf : f ∈ (c-ₗd)) (hac : same_side_line (e-ₗf) a c)
(hgef : between g e f) (h : (∠ g e a) ≅ₐ (∠ e f c))
(haep : between a e p) (hcfp : between c f p) : false :=
begin
  sorry
end
-/
lemma alter_eq_iff_parallel {a b c d e f g : pts} (hab : a ≠ b) (hcd : c ≠ d)
(hef : e ≠ f) (he : e ∈ (a-ₗb)) (hf : f ∈ (c-ₗd)) (hac : same_side_line (e-ₗf) a c)
(hgef : between g e f) : ((∠ g e a) ≅ₐ (∠ e f c)) ↔ ((a-ₗb) ∥ₗ (c-ₗd)) :=
begin
  split; intro h,
  { by_contra hfa,
    unfold is_parallel intersect at hfa,
    rw [not_and_distrib, not_and_distrib, not_not] at hfa,
    rcases hfa with hfa | hfa | hfa,
    { cases set.nonempty_def.mp hfa with p hp,
      have hefa := (same_side_line_noncol hac hef).1,
      have hae := (noncol_neq hefa).2.1.symm,
      have habe := col_in12' he,
      have habp := (col_in12' hp.1),
      have haep := col_trans habe habp hab,
      have hep : e ≠ p,
        intro hep, rw ←hep at hp,
        rw two_pt_one_line (line_in_lines hef) (line_in_lines hcd) hef (pt_left_in_line e f)
          (pt_right_in_line e f) hp.2 hf at hac,
        exact (same_side_line_notin hac).2 (pt_left_in_line c d),
      have hepf := col_noncol (col12 haep) (noncol23 hefa) hep,
      rw between_symm at hgef,
      have := ang_exter_lt_inter (noncol123 hepf) hgef,
      cases (line_separation (col12 haep) hae hep.symm).1 with heap heap,
      { have hecp : same_side_pt f c p,
          sorry,
        sorry },
      { sorry } },
    exact hfa (line_in_lines hab),
    exact hfa (line_in_lines hcd) },
  { sorry }
end

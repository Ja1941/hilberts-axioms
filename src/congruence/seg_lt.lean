/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import congruence.basic

/-!
# Segment orderness

This file defines how a segment is less than another and proves basic properties such as
transitivity and trichotomy.

## References

* See [Geometry: Euclid and Beyond]

-/

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--seg `m` is less than seg `n` if "one part" of `m` is congruent to `n`.
That is, there exists a point `a` between the two endpoints of `m` such that `a`
and one of the endpoint form a seg congruent to `n`
-/
def seg_lt (m n : seg) : Prop :=
(∃ a b c : C.pts, n = (b-ₛc) ∧ between b a c ∧ (m ≅ₛ (b-ₛa)))

notation a`<ₛ`b := seg_lt a b

lemma seg_lt_proper {m n : seg} : (m <ₛ n) → seg_proper n :=
begin
  rintros ⟨a, b, c, hn, hbac, hm⟩,
  rw [hn, seg_proper_iff_neq], exact (between_neq hbac).2.1
end

lemma two_pt_seg_lt {m : seg} {a b : C.pts} :
(m <ₛ (a-ₛb)) ↔ ∃ x : C.pts, between a x b ∧ (m ≅ₛ (a-ₛx)):=
begin
  split; intro h,
  { have hab := seg_lt_proper h, rw seg_proper_iff_neq at hab,
    rcases h with ⟨x, a', b', haba'b', ha'xb', hm⟩,
    cases two_pt_seg_pt haba'b',
    { rw [←h.1, ←h.2] at ha'xb', rw ←h.1 at hm,
      exact ⟨x, ha'xb', hm⟩ },
    { rcases extend_congr_seg (seg_proper_iff_neq.2 (between_neq ha'xb').1) hab
        with ⟨y, haby, hy, -⟩,
      use y, rw [←h.1, ←h.2] at ha'xb', rw ←h.2 at hy, rw ←h.2 at hm,
      split,
      exact (congr_seg_sub ha'xb' (same_side_pt_symm haby) hy
        (by {rw seg_symm, exact seg_congr_refl _})).1,
      exact seg_congr_trans hm hy } },
  { cases h with x hx,
    use [x, a, b], exact ⟨rfl, hx.1, hx.2⟩ }
end

lemma seg_lt_congr {m n l : seg} (hmn : m ≅ₛ n) :
((m <ₛ l) → (n <ₛ l)) ∧ (seg_proper n → (l <ₛ m) → (l <ₛ n)) :=
begin
  split,
  { rintros ⟨a, b, c, hlbc, hbac, hm⟩,
    exact ⟨a, b, c, hlbc, hbac, seg_congr_trans (seg_congr_symm hmn) hm⟩ },
  { intros hn hl, rcases hl with ⟨a, b, c, hmbc, hbac, hl⟩,
    rcases seg_two_pt n with ⟨d, e, hnde⟩, rw hnde,
    rw [hnde, seg_proper_iff_neq] at hn,
    rcases extend_congr_seg (seg_proper_iff_neq.2 (between_neq hbac).1) hn
      with ⟨x, hdex, hbadx, -⟩,
    rw two_pt_seg_lt, use x,
    split,
    rw [hmbc, hnde] at hmn,
    exact (congr_seg_sub hbac (same_side_pt_symm hdex) hbadx hmn).1,
    exact seg_congr_trans hl hbadx }
end

lemma seg_lt_trans {m n l : seg} :
(m <ₛ n) → (n <ₛ l) → (m <ₛ l) :=
begin
  intros hmn hnl,
  rcases hnl with ⟨a, b, c, hl, hbac, hn⟩,
  have hab := (between_neq hbac).1.symm,
  replace hmn := (seg_lt_congr hn).2 (seg_proper_iff_neq.2 hab.symm) hmn,
  rw two_pt_seg_lt at hmn,
  rcases hmn with ⟨x, hbxa, hm⟩,
  rw [hl, two_pt_seg_lt],
  use x, rw between_symm,
  rw between_symm at hbac hbxa,
  exact ⟨(between_trans' hbac hbxa).2, hm⟩
end

lemma seg_congr_same_side_unique {a b c d : pts}
(habc : same_side_pt a b c) (habd : same_side_pt a b d) : ((a-ₛc) ≅ₛ (a-ₛd)) → c = d :=
begin
  intro hacad,
  rcases extend_congr_seg (seg_proper_iff_neq.2 (same_side_pt_neq habc).2.symm)
    (same_side_pt_neq habc).1.symm with ⟨x, habx, hacax, hu⟩,
  rw [hu c habc (seg_congr_refl _), hu d habd hacad]
end

lemma seg_tri {m n : seg} (ha'b' : seg_proper m) (hab : seg_proper n) :
((m <ₛ n) ∨ (m ≅ₛ n) ∨ (n <ₛ m))
∧ ¬((m <ₛ n) ∧ (m ≅ₛ n)) ∧ ¬((m <ₛ n) ∧ (n <ₛ m)) ∧ ¬(((m ≅ₛ n) ∧ (n <ₛ m))) :=
begin
  rcases seg_two_pt n with ⟨a, b, hn⟩,
  rw [hn, seg_proper_iff_neq] at hab,
  rcases extend_congr_seg ha'b' hab with ⟨c, habc, hm, -⟩,
  have h₁ : (m <ₛ n) ↔ same_side_pt b a c,
    rw [hn, two_pt_seg_lt], split,
    { rintros ⟨c', hac'b, hm'⟩,
      rw between_same_side_pt at hac'b,
      have : c = c',
        from seg_congr_same_side_unique habc (same_side_pt_symm hac'b.1)
        (seg_congr_trans (seg_congr_symm hm) hm'),
      rw this, exact (hac'b).2 },
    intro hbac, exact ⟨c, between_same_side_pt.2 ⟨same_side_pt_symm habc, hbac⟩, hm⟩,
  have h₂ : (m ≅ₛ n) ↔ c = b,
    rw hn, split,
    { intro hm',
      exact seg_congr_same_side_unique habc (same_side_pt_refl hab)
        (seg_congr_trans (seg_congr_symm hm) hm') },
    intro hcb, rw hcb at hm, exact hm,
  have h₃ : (n <ₛ m) ↔ diff_side_pt b a c,
    rw hn, split,
    { intro hnm,
      replace hnm := (seg_lt_congr hm).2
        (seg_proper_iff_neq.2 (same_side_pt_neq habc).2.symm) hnm,
      rw two_pt_seg_lt at hnm,
      rcases hnm with ⟨d, hadc, habad⟩,
      rw seg_congr_same_side_unique (same_side_pt_symm habc)
        (same_side_pt_symm (between_same_side_pt.1 hadc).1) habad,
      rw ←between_diff_side_pt, exact hadc },
    { intro hbac,
      apply (seg_lt_congr (seg_congr_symm hm)).2 ha'b',
      rw two_pt_seg_lt,
      exact ⟨b, between_diff_side_pt.2 hbac, seg_congr_refl _⟩ },
  rw [h₁, h₂, h₃],
  split,
  by_cases hbc : b = c,
    right, left, exact hbc.symm,
  cases (line_separation (col12 habc.2) hab (ne.symm hbc)).1,
  left, exact h,
  right, right, exact h,
  split, intro hf, exact (same_side_pt_neq hf.1).2 hf.2,
  split, intro hf, rw ←not_diff_side_pt at hf, exact hf.1 hf.2,
  exact col12 habc.2, exact hab, exact hf.2.2.2,
  intro hf, exact hf.2.2.2 hf.1
end
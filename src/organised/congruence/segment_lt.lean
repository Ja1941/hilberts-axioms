import organised.congruence.basic

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--Segment `m` is less than segment `n` if "one part" of `m` is congruent to `n`.
That is, there exists a point `a` between the two endpoints of `m` such that `a`
and one of the endpoint form a segment congruent to `n`
-/
def segment_lt (m n : segment) : Prop :=
(∃ a b c : C.pts, n = (b-ₛc) ∧ is_between b a c ∧ (m ≅ₛ (b-ₛa)))

notation a`<ₛ`b := segment_lt a b

lemma segment_lt_nontrivial {m n : segment} : (m <ₛ n) → segment_nontrivial n :=
begin
  rintros ⟨a, b, c, hn, hbac, hm⟩,
  rw [hn, segment_nontrivial_iff_neq], exact (is_between_neq hbac).2.1
end

lemma two_pt_segment_lt {m : segment} {a b : C.pts} :
(m <ₛ (a-ₛb)) ↔ ∃ x : C.pts, is_between a x b ∧ (m ≅ₛ (a-ₛx)):=
begin
  split; intro h,
  have hab := segment_lt_nontrivial h, rw segment_nontrivial_iff_neq at hab,
  rcases h with ⟨x, a', b', haba'b', ha'xb', hm⟩,
  cases two_pt_segment_pt haba'b',
  rw [←h.1, ←h.2] at ha'xb', rw ←h.1 at hm,
  exact ⟨x, ha'xb', hm⟩,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (is_between_neq ha'xb').1) hab
    with ⟨y, haby, hy, -⟩,
  use y, rw [←h.1, ←h.2] at ha'xb', rw ←h.2 at hy, rw ←h.2 at hm,
  split,
  exact (congr_segment_sub ha'xb' (same_side_pt_symm haby) hy
    (by {rw segment_symm, exact segment_congr_refl _})).1,
  exact segment_congr_trans hm hy,
  cases h with x hx,
  use [x, a, b], exact ⟨rfl, hx.1, hx.2⟩
end

lemma segment_lt_congr {m n l : segment} (hmn : m ≅ₛ n) :
((m <ₛ l) → (n <ₛ l)) ∧ (segment_nontrivial n → (l <ₛ m) → (l <ₛ n)) :=
begin
  split, rintros ⟨a, b, c, hlbc, hbac, hm⟩,
  exact ⟨a, b, c, hlbc, hbac, segment_congr_trans (segment_congr_symm hmn) hm⟩,
  intros hn hl, rcases hl with ⟨a, b, c, hmbc, hbac, hl⟩,
  rcases segment_two_pt n with ⟨d, e, hnde⟩, rw hnde,
  rw [hnde, segment_nontrivial_iff_neq] at hn,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (is_between_neq hbac).1) hn
    with ⟨x, hdex, hbadx, -⟩,
  rw two_pt_segment_lt, use x,
  split,
  rw [hmbc, hnde] at hmn,
  exact (congr_segment_sub hbac (same_side_pt_symm hdex) hbadx hmn).1,
  exact segment_congr_trans hl hbadx
end

lemma segment_lt_trans {m n l : segment} :
(m <ₛ n) → (n <ₛ l) → (m <ₛ l) :=
begin
  intros hmn hnl,
  rcases hnl with ⟨a, b, c, hl, hbac, hn⟩,
  have hab := (is_between_neq hbac).1.symm,
  replace hmn := (segment_lt_congr hn).2 (segment_nontrivial_iff_neq.2 hab.symm) hmn,
  rw two_pt_segment_lt at hmn,
  rcases hmn with ⟨x, hbxa, hm⟩,
  rw [hl, two_pt_segment_lt],
  use x, rw is_between_symm,
  rw is_between_symm at hbac hbxa,
  exact ⟨(is_between_trans' hbac hbxa).2, hm⟩
end

lemma segment_congr_same_side_unique {a b c d : pts}
(habc : same_side_pt a b c) (habd : same_side_pt a b d) : ((a-ₛc) ≅ₛ (a-ₛd)) → c = d :=
begin
  intro hacad,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (same_side_pt_neq habc).2.symm)
    (same_side_pt_neq habc).1.symm with ⟨x, habx, hacax, hu⟩,
  rw [hu c habc (segment_congr_refl _), hu d habd hacad]
end

lemma segment_tri {m n : segment} (ha'b' : segment_nontrivial m) (hab : segment_nontrivial n) :
((m <ₛ n) ∨ (m ≅ₛ n) ∨ (n <ₛ m))
∧ ¬((m <ₛ n) ∧ (m ≅ₛ n)) ∧ ¬((m <ₛ n) ∧ (n <ₛ m)) ∧ ¬(((m ≅ₛ n) ∧ (n <ₛ m))) :=
begin
  rcases segment_two_pt n with ⟨a, b, hn⟩,
  rw [hn, segment_nontrivial_iff_neq] at hab,
  rcases extend_congr_segment ha'b' hab with ⟨c, habc, hm, -⟩,
  have h₁ : (m <ₛ n) ↔ same_side_pt b a c,
    rw [hn, two_pt_segment_lt], split,
    rintros ⟨c', hac'b, hm'⟩,
    rw is_between_same_side_pt at hac'b,
    have : c = c',
      from segment_congr_same_side_unique habc (same_side_pt_symm hac'b.1)
      (segment_congr_trans (segment_congr_symm hm) hm'),
    rw this, exact (hac'b).2,
    intro hbac, exact ⟨c, is_between_same_side_pt.2 ⟨same_side_pt_symm habc, hbac⟩, hm⟩,
  have h₂ : (m ≅ₛ n) ↔ c = b,
    rw hn, split,
    intro hm',
    exact segment_congr_same_side_unique habc (same_side_pt_refl hab)
      (segment_congr_trans (segment_congr_symm hm) hm'),
    intro hcb, rw hcb at hm, exact hm,
  have h₃ : (n <ₛ m) ↔ diff_side_pt b a c,
    rw hn, split,
    intro hnm,
    replace hnm := (segment_lt_congr hm).2
      (segment_nontrivial_iff_neq.2 (same_side_pt_neq habc).2.symm) hnm,
    rw two_pt_segment_lt at hnm,
    rcases hnm with ⟨d, hadc, habad⟩,
    rw segment_congr_same_side_unique (same_side_pt_symm habc)
      (same_side_pt_symm (is_between_same_side_pt.1 hadc).1) habad,
    rw ←is_between_diff_side_pt, exact hadc,
    intro hbac,
    apply (segment_lt_congr (segment_congr_symm hm)).2 ha'b',
    rw two_pt_segment_lt,
    exact ⟨b, is_between_diff_side_pt.2 hbac, segment_congr_refl _⟩,
  rw [h₁, h₂, h₃],
  split,
  by_cases hbc : b = c,
    right, left, exact hbc.symm,
  cases (line_separation (collinear12 habc.2) hab (ne.symm hbc)).1,
  left, exact h,
  right, right, exact h,
  split, intro hf, exact (same_side_pt_neq hf.1).2 hf.2,
  split, intro hf, rw ←not_diff_side_pt at hf, exact hf.1 hf.2,
  exact collinear12 habc.2, exact hab, exact hf.2.2.2,
  intro hf, exact hf.2.2.2 hf.1
end
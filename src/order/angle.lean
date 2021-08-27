/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import order.sidedness

/-!
# Ray and angle

This file defines rays and angles using `same_side_pt` and insidedness of an angle,
and then proves some important theorems such as the crossbar theorem.

## Main definitions

* `ray` is half of a line separated by its vertex.

* `ang` is the union of two `ray` sharing the same vertex.

* `inside_ang` defines how a point can be inside `ang`.

## References

* See [Geometry: Euclid and Beyond]

-/

open set

variable [B : incidence_order_geometry]

open incidence_geometry incidence_order_geometry

include B

/--A type with a vertex and inside defined as the set consising of the vertex and
all points on the same side with a point `a` to the vertex.
-/
structure ray := (vertex : pts) (inside : set pts)
(in_eq : ∃ a : pts, inside = {x : pts | same_side_pt vertex a x} ∪ {vertex})

/--A ray can be defined by explicitly stating the vertex `o` and `a`. -/
def two_pt_ray (o a : pts) : ray := ⟨o, {x : pts | same_side_pt o a x} ∪ {o}, ⟨a, rfl⟩⟩

notation a`-ᵣ`b := two_pt_ray a b

lemma two_pt_ray_vertex (o a : pts) : (o-ᵣa).vertex = o := rfl

lemma ray_unique {r₁ r₂ : ray} (hr₁r₂ : r₁.vertex = r₂.vertex) :
(∃ x : pts, x ≠ r₁.vertex ∧ x ∈ r₁.inside ∩ r₂.inside) → r₁ = r₂ :=
begin
  rintros ⟨a, ha1, ha⟩,
  suffices : r₁.inside = r₂.inside,
    induction r₁ with v₁ I₁ hI₁, induction r₂ with v₂ I₂ hI₂ generalizing v₁ I₁ hI₁,
    simp, exact ⟨hr₁r₂, this⟩,
  cases r₁.in_eq with x h₁,
  cases r₂.in_eq with y h₂,
  replace h₁ : r₁.inside = {x : pts | same_side_pt r₁.vertex x a} ∪ {r₁.vertex},
    rw h₁, ext p, simp,
    have : same_side_pt r₁.vertex x p ↔ same_side_pt r₁.vertex p a,
      rw h₁ at ha, simp at ha, split; intro h; cases ha.1 with ha ha,
      exact absurd ha ha1, exact same_side_pt_trans (same_side_pt_symm h) ha,
      exact absurd ha ha1, exact same_side_pt_trans ha (same_side_pt_symm h),
    rw this,
  rw [h₁, h₂], ext p, simp, rw hr₁r₂,
  have : same_side_pt r₂.vertex p a ↔ same_side_pt r₂.vertex y p,
    rw h₂ at ha, simp at ha, cases ha.2 with ha ha,
    rw hr₁r₂ at ha1, exact absurd ha ha1,
    split; intro h,
    exact same_side_pt_trans ha (same_side_pt_symm h),
    exact same_side_pt_trans (same_side_pt_symm h) ha,
  rw this
end

lemma ray_eq_same_side_pt {r : ray} {a : pts}
(har : a ∈ r.inside) (hao : a ≠ r.vertex) : r = (r.vertex-ᵣa) :=
begin
  suffices : r.inside = (r.vertex-ᵣa).inside,
    induction r, unfold two_pt_ray, simp,
    unfold two_pt_ray at this, simp at this, exact this,
  cases r.in_eq with a' ha', rw ha',
  rw ha' at har, simp at har, cases har with har har,
  exact absurd har hao,
  unfold two_pt_ray, ext, simp,
  have : same_side_pt r.vertex a x ↔ same_side_pt r.vertex a' x,
    split; intro h, exact same_side_pt_trans har h,
    exact same_side_pt_trans (same_side_pt_symm har) h,
  rw this
end

lemma ray_in_neq {o a b : pts} (hbo : b ≠ o) (h : b ∈ (o-ᵣa).inside) : same_side_pt o a b :=
by { cases h, exact h, exact absurd h hbo }

lemma two_pt_ray_eq_same_side_pt {o a b : pts} (hoab : same_side_pt o a b) :
(o-ᵣa) = (o-ᵣb) :=
begin
  unfold two_pt_ray, simp only [true_and, eq_self_iff_true], ext, simp,
  have : same_side_pt o a x ↔ same_side_pt o b x,
    split; intro h, exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  rw this
end

lemma ray_singleton (a : pts) : (a-ᵣa).inside = {a} :=
begin
  ext1, unfold two_pt_ray same_side_pt, simp,
  intro hf, unfold two_pt_seg at hf, simp at hf, exfalso, exact hf
end

lemma ray_disjoint {s₁ s₂ : ray} (hvertex : s₁.vertex = s₂.vertex) :
s₁ ≠ s₂ → s₁.inside ∩ s₂.inside = {s₁.vertex} :=
begin
  contrapose!, intro h,
  refine ray_unique hvertex _,
  by_contra hf, push_neg at hf,
  apply h, apply subset.antisymm, intro y, contrapose!, exact hf y,
  simp, cases s₁.in_eq, rw h_1, cases s₂.in_eq, rw h_2, rw hvertex, simp
end

lemma in_ray_col {o a b : pts} : b ∈ (o-ᵣa).inside → col o a b :=
begin
  intro h, 
  cases h, exact h.2, simp at h, rw h,
  by_cases hao : a = o,
    rw hao, rcases one_pt_line o with ⟨l, hl, hol⟩,
    exact ⟨l, hl, hol, hol, hol⟩,
  exact ⟨(a-ₗo), line_in_lines hao,
    pt_right_in_line a o, pt_left_in_line a o, pt_right_in_line a o⟩
end

lemma ray_reconstruct (r : ray) : ∃ a : pts, r = (r.vertex-ᵣa) :=
begin
  cases r.in_eq with x hx, use x, unfold two_pt_ray,
  induction r with v I hI, simp,
  simp at hx, rw hx
end

lemma ray_singleton_iff_eq {o a p : pts} :  (o-ᵣa).inside = {p} ↔ o = a ∧ o = p :=
begin
  by_cases hoa : o = a,
    rw [hoa, ray_singleton], simp,
  split; intro h,
  have : ∀ x ∈ (o-ᵣa).inside, x = p, rw h, simp, unfold two_pt_ray at this, simp at this,
  rw this.2 a (same_side_pt_refl hoa), exact ⟨this.1, this.1⟩,
  exact absurd h.1 hoa
end

lemma pt_left_in_ray (o a : pts) : o ∈ (o-ᵣa).inside :=
by {unfold two_pt_ray, simp}

lemma pt_right_in_ray (o a : pts) : a ∈ (o-ᵣa).inside :=
begin
  by_cases hoa : o = a,
    rw [hoa, ray_singleton], exact rfl,
  unfold two_pt_ray, simp, right, exact same_side_pt_refl (hoa)
end

lemma seg_in_ray (o a : pts) : (o-ₛa).inside ⊆ (o-ᵣa).inside :=
begin
  unfold two_pt_ray, unfold two_pt_seg,
  intros x hx, simp at hx, simp,
  rcases hx with hx | hx | hx,
  rw hx, simp,
  rw hx, by_cases hao : a = o, rw hao, left, refl,
  right, split,
  rw seg_singleton, exact ne.symm hao,
  exact ⟨(a-ₗo), line_in_lines hao,
    pt_right_in_line a o, pt_left_in_line a o, pt_left_in_line a o⟩,
  right, unfold same_side_pt, unfold two_pt_seg, simp, split,
  intro hf, rcases hf with hf | hf | hf,
  rw hf at hx, exact (between_neq hx).2.1 rfl,
  exact (between_neq hx).1 hf,
  rw between_symm at hx, exact between_contra.2.1 ⟨hf, hx⟩,
  rcases (between_col hx) with ⟨l, hl, hol, hxl, hal⟩,
  exact ⟨l, hl, hol, hal, hxl⟩
end

lemma ray_in_line (o a : pts) : (o-ᵣa).inside ⊆ (o-ₗa) :=
begin
  intros x hx, cases hx,
  exact col_in12 hx.2 (same_side_pt_neq hx).1.symm,
  simp at hx, rw hx, exact pt_left_in_line o a
end

lemma two_pt_ray_eq_same_side_pt_pt {o a b : pts} :
same_side_pt o a b ↔ (o-ᵣa) = (o-ᵣb) ∧ o ≠ a ∧ o ≠ b :=
begin
  split, intro hoab, unfold two_pt_ray,
  have : {x : pts | same_side_pt o a x} = {x : pts | same_side_pt o b x},
    ext, simp, split; intro h,
    exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  exact ⟨by {simp, simp at this, rw this},
    (same_side_pt_neq hoab).1.symm, (same_side_pt_neq hoab).2.symm⟩,
  rintros ⟨hoab, hoa, hob⟩,
  cases two_pt_between hoa with x hoxa,
  have hx : x ∈ (o-ᵣb).inside,
    rw ←hoab, unfold two_pt_ray, simp,
    right, exact same_side_pt_symm (between_same_side_pt.1 hoxa).1,
  unfold two_pt_ray at hx, simp at hx,
  cases hx with hx hx, exact absurd hx (between_neq hoxa).1.symm,
  exact same_side_pt_trans (same_side_pt_symm (between_same_side_pt.1 hoxa).1)
    (same_side_pt_symm hx)
end

lemma t_shape_ray {a b c : pts} (habc : noncol a b c) :
∀ {x : pts}, same_side_pt b c x → same_side_line (a-ₗb) c x :=
begin
  intros x hbcx,
  by_cases hcx : c = x,
    rw ←hcx, exact same_side_line_refl (noncol_in12 habc),
  rintros ⟨e, heab, hecx⟩,
  have hab := (noncol_neq habc).1,
  have hbe : b = e,
    apply two_line_one_pt (line_in_lines hab) (line_in_lines hcx),
    intro hf, apply noncol_in12 habc, rw hf, exact pt_left_in_line c x,
    exact pt_right_in_line a b, exact col_in23 hbcx.2 hcx,
    exact heab, exact (seg_in_line c x) hecx,
  rw hbe at hbcx,
  have hcex := seg_in_neq (same_side_pt_neq hbcx).1.symm (same_side_pt_neq hbcx).2.symm hecx,
  rw [←not_diff_side_pt, ←between_diff_side_pt] at hbcx,
  exact hbcx hcex,
  exact hbcx.2,
  exact (same_side_pt_neq hbcx).1, exact (same_side_pt_neq hbcx).2
end

lemma t_shape_seg {a b c : pts} (habc : noncol a b c) :
∀ x : pts, between b x c → same_side_line (a-ₗb) c x :=
λ x hbxc, t_shape_ray habc (same_side_pt_symm (between_same_side_pt.1 hbxc).1)

lemma between_diff_side_line {o a b c : pts} (hoab : noncol o a b) (hacb : between a c b) :
diff_side_line (o-ₗc) a b :=
begin
  use c,
  exact ⟨pt_right_in_line o c, by {left, exact hacb}⟩,
  have hac := (between_neq hacb).1,
  have hbc := (between_neq hacb).2.2.symm,
  split,
  exact noncol_in32 (col_noncol (col23 (between_col hacb)) (noncol123 hoab) hac),
  exact noncol_in32 (col_noncol (col132 (between_col hacb)) (noncol13 hoab) hbc)
end

lemma between_same_side_line {o a b c : pts} (hoab : noncol o a b) (hacb : between a c b) :
same_side_line (o-ₗa) b c :=
begin
  have hoa := (noncol_neq hoab).1,
  have hbc := (between_neq hacb).2.2.symm,
  have hab := (between_neq hacb).2.1,
  have hac := (between_neq hacb).1,
  rintros ⟨d, hd⟩,
  have had : a = d,
    apply two_line_one_pt (line_in_lines hoa) (line_in_lines hbc),
    intro hf, apply noncol_in12 hoab, rw hf, exact pt_left_in_line b c,
    exact pt_right_in_line o a,
    exact col_in32 (between_col hacb) hbc,
    exact hd.1, exact (seg_in_line b c) hd.2,
  rw ←had at hd,
  rw between_symm at hacb,
  exact between_contra.2.1 ⟨hacb, seg_in_neq hab hac hd.2⟩
end

lemma ray_same_side_line {o a b c b' : pts} (hoa : o ≠ a) (h : same_side_line (o-ₗa) b c)
(hobb' : same_side_pt o b b') : same_side_line (o-ₗa) b' c :=
begin
  have hob' := (same_side_pt_neq hobb').2.symm,
  apply same_side_line_trans (line_in_lines hoa) _ h,
  rw line_symm, apply t_shape_ray,
  exact noncol132 (col_noncol hobb'.2 (noncol23 (same_side_line_noncol h hoa).1) hob'),
  exact same_side_pt_symm hobb'
end

lemma ray_diff_side_line {o a b c a' : pts} (hob : o ≠ b) (h : diff_side_line (o-ₗb) a c)
(hoaa' : same_side_pt o a a') : diff_side_line (o-ₗb) a' c :=
begin
  apply same_diff_side_line (line_in_lines hob) _ h,
  rw line_symm, apply t_shape_ray,
  { have hoba := (diff_side_line_noncol h hob).1,
    have hoa' := (same_side_pt_neq hoaa').2.symm,
    exact noncol132 ((col_noncol hoaa'.2 (noncol23 hoba)) hoa') },
  exact same_side_pt_symm hoaa'
end

lemma diff_same_side_line' {a o b c : pts} :
diff_side_line (o-ₗb) a c → same_side_line (o-ₗa) b c → same_side_line (o-ₗc) a b :=
begin
  intros h₁ h₂,
  have hoa := (diff_side_line_neq h₁).1.symm,
  have hoc := (diff_side_line_neq' h₁).1.symm,
  have hab := (diff_side_line_neq h₁).2,
  have hob := (same_side_line_neq h₂).1.symm,
  cases h₁.1 with b' hb',
  have hb'a : b' ≠ a,
    intro hf, rw hf at hb', exact h₁.2.1 hb'.1,
  have hb'c : b' ≠ c,
    intro hf, rw hf at hb', exact h₁.2.2 hb'.1,
  have hb'o : b' ≠ o,
    intro hf, rw hf at hb',
    exact (same_side_line_noncol h₂ hoa).2 (col_in23' ((seg_in_line a c) hb'.2)),
  have hab'c := seg_in_neq hb'a hb'c hb'.2,
  apply same_side_line_symm, apply ray_same_side_line,
  exact hoc,
  { apply same_side_line_symm, apply between_same_side_line,
    exact noncol23 (same_side_line_noncol h₂ hoa).2,
    rw between_symm at hab'c, exact hab'c },
  have hobb' := col_in13' hb'.1,
  apply same_side_line_pt,
  exact hobb', exact line_in_lines hoa,
  exact pt_left_in_line o a,
  exact noncol_in13 (col_noncol (col23 hobb') (diff_side_line_noncol h₁ hob).1 hb'o.symm),
  exact (same_side_line_notin h₂).1,
  { apply same_side_line_symm, apply same_side_line_trans (line_in_lines hoa) h₂,
    exact t_shape_seg (same_side_line_noncol h₂ hoa).2 b' hab'c }
end

/--A type given by a vertex and its inside is the union of two rays with this vertex. -/
structure ang := (vertex : pts) (inside : set pts)
(in_eq : ∃ a b : pts, inside = (vertex-ᵣa).inside ∪ (vertex-ᵣb).inside)

noncomputable def pt1 (α : ang) :
{a : pts // ∃ b : pts, α.inside = (α.vertex-ᵣa).inside ∪ (α.vertex-ᵣb).inside} :=
by {choose a h using α.in_eq, exact ⟨a, h⟩}

noncomputable def pt2 (α : ang) :
{b : pts // α.inside = (α.vertex-ᵣ(pt1 α)).inside ∪ (α.vertex-ᵣb).inside} :=
by {choose b h using (pt1 α).2, exact ⟨b, h⟩}

lemma vertex_in_ang (α : ang) : α.vertex ∈ α.inside :=
by { rcases α.in_eq with ⟨a, b, h⟩, rw h, left, exact pt_left_in_ray _ _ }

/--Define an ang by giving its vertex and two other points on the two rays. -/
def three_pt_ang (a o b : pts) : ang := ⟨o, (o-ᵣa).inside∪(o-ᵣb).inside, ⟨a, b, rfl⟩⟩

notation `∠` := three_pt_ang

lemma ang_symm (a o b : pts) : ∠ a o b = ∠ b o a :=
by {unfold three_pt_ang, simp, rw union_comm}

lemma three_pt_ang_vertex (a o b : pts) : (∠ a o b).vertex = o :=
by unfold three_pt_ang

lemma pt_left_in_three_pt_ang (a o b : pts) : a ∈ (∠ a o b).inside :=
begin
  unfold three_pt_ang two_pt_ray, simp, left,
  by_cases a = o, left, exact h,
  right, exact (same_side_pt_refl (ne.symm h))
end

lemma pt_right_in_three_pt_ang (a o b : pts) : b ∈ (∠ a o b).inside :=
by {rw ang_symm, exact pt_left_in_three_pt_ang b o a}

lemma ang_eq_same_side_pt (a : pts) {o b c : pts} (hobc : same_side_pt o b c) :
∠ a o b = ∠ a o c :=
by {unfold three_pt_ang, simp, rw two_pt_ray_eq_same_side_pt hobc}

/--An ang is proper if its two sides are noncollinear. -/
def ang_proper (α : ang) : Prop :=
∀ l ∈ lines, ¬α.inside ⊆ l

lemma ang_proper_iff_noncol {a o b : pts} :
ang_proper (∠ a o b) ↔ noncol a o b :=
begin
  split; intro h,
  { rintros ⟨l, hl, hal, hol, hbl⟩,
    apply h l hl,
    unfold three_pt_ang, simp,
    split,
    { intros x hx,
      by_cases hoa : o = a,
        rw [hoa, ray_singleton, mem_singleton_iff] at hx,
        rw hx, exact hal,
      rw two_pt_one_line hl (line_in_lines hoa) hoa hol hal
        (pt_left_in_line o a) (pt_right_in_line o a),
      exact (ray_in_line o a) hx },
    { intros x hx,
      by_cases hob : o = b,
        rw [hob, ray_singleton, mem_singleton_iff] at hx,
        rw hx, exact hbl,
      rw two_pt_one_line hl (line_in_lines hob) hob hol hbl
        (pt_left_in_line o b) (pt_right_in_line o b),
      exact (ray_in_line o b) hx } },
  { intros l hl hf,
    unfold three_pt_ang at hf, simp at hf,
    exact h ⟨l, hl, hf.1 (pt_right_in_ray o a), hf.1 (pt_left_in_ray o a),
      hf.2 (pt_right_in_ray o b)⟩ }
end

private lemma three_pt_ang_eq_iff_prep {a o b a' b' : pts} (haob : ang_proper (∠ a o b)) :
(∠ a o b) = (∠ a' o b') → same_side_pt o a a' → same_side_pt o b b' :=
begin
  intros he hoaa',
  have ha'ob' : noncol a' o b',
    rw he at haob, exact ang_proper_iff_noncol.1 haob,
  rw ang_proper_iff_noncol at haob,
  have hoa := (noncol_neq haob).1.symm,
  have hob := (noncol_neq haob).2.2,
  have hob' := (noncol_neq ha'ob').2.2,
  by_cases hbb' : b = b',
    rw ←hbb', exact same_side_pt_symm (same_side_pt_refl hob),
  have hb' : b' ∈ (∠ a o b).inside,
    rw he, unfold three_pt_ang, right, exact pt_right_in_ray o b',
  cases hb' with hb' hb',
  { exfalso, apply noncol12 ha'ob',
    exact col_trans hoaa'.2 ⟨(o-ₗa), line_in_lines hoa,
      pt_left_in_line o a, pt_right_in_line o a, (ray_in_line o a) hb'⟩ hoa },
  { cases hb' with hb' hb',
    exact hb', exact absurd hb' hob'.symm }
end

lemma three_pt_ang_eq_iff {a o b a' o' b' : pts}
(haob : noncol a o b) : (∠ a o b) = (∠ a' o' b') ↔ o = o'
∧ ((same_side_pt o a a' ∧ same_side_pt o b b') ∨ (same_side_pt o a b' ∧ same_side_pt o b a')) :=
begin
  split,
  { intro he,
    have hoo' : o = o',
      unfold three_pt_ang at he, simp at he, exact he.1,
    have ha'ob' : noncol a' o b',
      rw [←ang_proper_iff_noncol, he, ←hoo'] at haob,
      exact ang_proper_iff_noncol.1 haob,
    have ha'o := (noncol_neq ha'ob').1,
    split, exact hoo',
    rw ←hoo' at he,
    have ha' : a' ∈ (∠ a o b).inside,
      rw he, unfold three_pt_ang, left, exact pt_right_in_ray o a',
    cases ha' with ha' ha';
    cases ha' with ha' ha',
    left, exact ⟨ha', three_pt_ang_eq_iff_prep (ang_proper_iff_noncol.2 haob) he ha'⟩,
    exact absurd ha' ha'o,
    { right, rw ang_symm at he,
      exact ⟨three_pt_ang_eq_iff_prep (ang_proper_iff_noncol.2
        (noncol13 haob)) he ha', ha'⟩ },
    exact absurd ha' ha'o },
  { rintros ⟨hoo', h | h⟩,
    rw [ang_eq_same_side_pt a h.2, ang_symm, ang_eq_same_side_pt b' h.1, ang_symm, hoo'],
    rw [ang_eq_same_side_pt a h.2, ang_symm, ang_eq_same_side_pt a' h.1, hoo'] }
end

lemma ang_three_pt (α : ang) : ∃ a b : pts, α = ∠ a α.vertex b :=
begin
  rcases α.in_eq with ⟨a, b, h⟩,
  use [a, b], unfold three_pt_ang, induction α, simp, exact h
end

/--A point `p` is inside `∠ a o b` if `p` and `a` are on the same side to `o-ₗa` and
`p` and `b` are on the same side to line `o-ₗb`. -/
def inside_ang (p : pts) (α : ang) : Prop :=
(∃ a b : pts, α = ∠ a α.vertex b
∧ same_side_line (α.vertex-ₗa) b p ∧ same_side_line (α.vertex-ₗb) a p)

lemma inside_ang_proper {p : pts} {α : ang} :
inside_ang p α → ang_proper α :=
begin
  rintros ⟨a, b, hα, hbp, hap⟩,
  rw [hα, ang_proper_iff_noncol],
  intro haob,
  by_cases α.vertex = b,
    rw h at hbp,
    exact (same_side_line_notin hbp).1 (pt_left_in_line b a),
  exact (same_side_line_notin hap).1 (col_in23 haob h)
end

lemma inside_three_pt_ang {p a o b : pts}:
inside_ang p (∠ a o b) ↔ same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p :=
begin
  split,
  { intro hp,
    have haob := inside_ang_proper hp,
    rcases hp with ⟨a', b', haoba'ob', hb'p, ha'p⟩,
    rw three_pt_ang_vertex at haoba'ob' ha'p hb'p,
    have ha'ob' : noncol a' o b',
      rw [haoba'ob', ang_proper_iff_noncol] at haob, exact haob,
    rw ang_proper_iff_noncol at haob,
    have hoa := (noncol_neq haob).1.symm,
    have hoa' := (noncol_neq ha'ob').1.symm,
    have hob := (noncol_neq haob).2.2,
    have hob' := (noncol_neq ha'ob').2.2,
    cases ((three_pt_ang_eq_iff haob).1 haoba'ob').2,
    split,
    { rw two_pt_one_line (line_in_lines hoa) (line_in_lines hoa') hoa
      (pt_left_in_line o a) (pt_right_in_line o a) (pt_left_in_line o a') (col_in13 h.1.2 hoa'),
      exact ray_same_side_line hoa' hb'p (same_side_pt_symm h.2) },
    { rw two_pt_one_line (line_in_lines hob) (line_in_lines hob') hob
      (pt_left_in_line o b) (pt_right_in_line o b) (pt_left_in_line o b') (col_in13 h.2.2 hob'),
      exact ray_same_side_line hob' ha'p (same_side_pt_symm h.1) },
    split,
    { rw two_pt_one_line (line_in_lines hoa) (line_in_lines hob') hoa
      (pt_left_in_line o a) (pt_right_in_line o a) (pt_left_in_line o b') (col_in13 h.1.2 hob'),
      exact ray_same_side_line hob' ha'p (same_side_pt_symm h.2) },
    { rw two_pt_one_line (line_in_lines hob) (line_in_lines hoa') hob
      (pt_left_in_line o b) (pt_right_in_line o b) (pt_left_in_line o a') (col_in13 h.2.2 hoa'),
      exact ray_same_side_line hoa' hb'p (same_side_pt_symm h.1) } },
  { rintros ⟨hap, hbp⟩,
    use [a, b],
    rw three_pt_ang_vertex,
    exact ⟨rfl, hap, hbp⟩ }
end

lemma inside_ang_proper' {p a o b : pts} : inside_ang p (∠ a o b)
→ ang_proper (∠ p o a) ∧ ang_proper (∠ p o b) :=
begin
  intro hp,
  have haob := ang_proper_iff_noncol.1 (inside_ang_proper hp),
  have hoa := (noncol_neq haob).1.symm,
  have hob := (noncol_neq haob).2.2,
  rw inside_three_pt_ang at hp,
  split; rw ang_proper_iff_noncol; intro h,
  exact (same_side_line_notin hp.1).2 (col_in23 h hoa),
  exact (same_side_line_notin hp.2).2 (col_in23 h hob)
end

lemma hypo_inside_ang {a b c d : pts} (habc : noncol a b c) (hadc : between a d c) :
inside_ang d (∠ a b c) :=
begin
  have hab := (noncol_neq habc).1,
  have hbc := (noncol_neq habc).2.2,
  have had := (between_neq hadc).1,
  have hdc := (between_neq hadc).2.2,
  rw inside_three_pt_ang, split,
  exact t_shape_seg (noncol12 habc) d hadc,
  { rw between_symm at hadc,
    exact t_shape_seg (noncol123 habc) d hadc }
end

theorem crossbar {a b c d : pts}
(hd : inside_ang d (∠ b a c)) : (two_pt_ray a d).inside ♥ (b-ₛc).inside :=
begin
  have hbac := inside_ang_proper hd, rw ang_proper_iff_noncol at hbac,
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  rw inside_three_pt_ang at hd,
  have had := (same_side_line_neq' hd.1).1.symm,
  have hacd := ((same_side_line_noncol hd.2) hac).2,
  have habd := ((same_side_line_noncol hd.1) hab).2,
  cases between_extend hac.symm with e hcae,
  have hce := (between_neq hcae).2.1,
  have hae := (between_neq hcae).2.2,
  have hceb := col_noncol (between_col hcae) (noncol13 hbac) hce,
  have haed := col_noncol (col12 (between_col hcae)) hacd hae,
  have haeb := col_noncol (col12 (between_col hcae)) (noncol123 hbac) hae,
  have : ((a-ₗd) ♥ (c-ₛe).inside),
    from ⟨a, pt_left_in_line a d, by {left, exact hcae}⟩,
  cases (pasch hceb (line_in_lines had) (noncol_in13 hacd)
    (noncol_in13 haed) (noncol_in13 habd) this).1,
  { cases h with x hx,
    have hxa : x ≠ a,
      intro hf, rw hf at hx, exact (noncol_in31 hbac) ((seg_in_line c b) hx.2),
    have hxb : x ≠ b,
      intro hf, rw hf at hx, exact (noncol_in13 habd) hx.1,
    have hxc : x ≠ c,
      intro hf, rw hf at hx, exact (noncol_in13 hacd) hx.1,
    cases (line_separation (col_in12' hx.1) had.symm hxa).1,
    rw seg_symm, exact ⟨x, by {left, exact h}, hx.2⟩,
    { have h₁ : diff_side_line (a-ₗc) d x,
        apply diff_side_pt_line h (line_in_lines hac) (pt_left_in_line a c) (noncol_in12 hacd),
        exact noncol_in13 (col_noncol (diff_side_pt_col h) (noncol23 hacd) hxa.symm),
      have h₂ : same_side_line (a-ₗc) d x,
        apply same_side_line_symm,
        apply same_side_line_trans (line_in_lines hac) _ hd.2,
        apply same_side_line_symm,
        exact t_shape_seg (noncol123 hbac) x (seg_in_neq hxc hxb hx.2),
      rw ←not_diff_side_line at h₂, exact absurd h₁ h₂,
      exact noncol_in12 hacd, exact h₁.2.2 } },
  { cases h with x hx,
    have hxa : x ≠ a,
      intro hf, rw hf at hx, exact (noncol_in23 haeb) ((seg_in_line e b) hx.2),
    have hxb : x ≠ b,
      intro hf, rw hf at hx, exact (noncol_in13 habd) hx.1,
    have hxe : x ≠ e,
      intro hf, rw hf at hx, exact (noncol_in13 haed) hx.1,
    cases (line_separation (col_in12' hx.1) had.symm hxa).1,
    { have h₁ : same_side_line (a-ₗb) c x,
        apply same_side_line_trans (line_in_lines hab) hd.1,
        rw line_symm,
        exact t_shape_ray (noncol12 habd) h,
      have h₂ : diff_side_line (a-ₗb) c x,
        apply diff_same_side_line (line_in_lines hab),
        { apply diff_side_pt_line, exact (between_diff_side_pt.1 hcae),
          exact line_in_lines hab, exact pt_left_in_line a b,
          exact noncol_in21 hbac, exact noncol_in13 haeb },
        { apply t_shape_seg (noncol23 haeb),
          rw seg_symm at hx, exact (seg_in_neq hxb hxe hx.2) },
      rw ←not_same_side_line at h₂, exact absurd h₁ h₂,
      exact noncol_in21 hbac, exact (same_side_line_notin h₁).2 },
    { have h₁ : diff_side_line (a-ₗc) d x,
        apply diff_side_pt_line h (line_in_lines hac) (pt_left_in_line a c) (noncol_in12 hacd),
        exact noncol_in13 (col_noncol (diff_side_pt_col h) (noncol23 hacd) hxa.symm),
      have h₂ : same_side_line (a-ₗc) d x,
        apply same_side_line_trans (line_in_lines hac) (same_side_line_symm hd.2),
        rw two_pt_one_line (line_in_lines hac) (line_in_lines hae) hac (pt_left_in_line a c)
          (pt_right_in_line a c) (pt_left_in_line a e) (col_in23 (between_col hcae) hae),
        exact t_shape_seg haeb x (seg_in_neq hxe hxb hx.2),
      rw ←not_diff_side_line at h₂, exact absurd h₁ h₂,
      exact noncol_in12 hacd, exact h₁.2.2 } }
end

lemma ray_inside_ang {a o b p q : pts} :
inside_ang p (∠ a o b) → same_side_pt o p q → inside_ang q (∠ a o b) :=
begin
  intros hp hopq,
  have haob := ang_proper_iff_noncol.1 (inside_ang_proper hp),
  rw inside_three_pt_ang at hp, rw inside_three_pt_ang,
  have hoa := (noncol_neq haob).1.symm,
  have hob := (noncol_neq haob).2.2,
  split,
  { apply same_side_line_trans (line_in_lines hoa) hp.1,
    rw line_symm, apply t_shape_ray,
    exact noncol12 (same_side_line_noncol hp.1 hoa).2,
    exact hopq },
  { apply same_side_line_trans (line_in_lines hob) hp.2,
    rw line_symm, apply t_shape_ray,
    exact noncol12 (same_side_line_noncol hp.2 hob).2,
    exact hopq }
end

/--Two proper angs are supplementary if their shares one common ray and the other two
rays lie on the same line in opposite sides. -/
def supplementary (α β : ang) : Prop :=
(∃ a b c d : pts, α = ∠ b a c ∧ β = ∠ b a d ∧ between c a d)
∧ ang_proper α ∧ ang_proper β

lemma supplementary_symm {α β : ang} : supplementary α β ↔ supplementary β α :=
begin
  split; rintros ⟨⟨a, b, c, d, hbac, hbad, hcad⟩, h₁, h₂⟩;
  exact ⟨⟨a, b, d, c, hbad, hbac, by {rw between_symm, exact hcad}⟩, h₂, h₁⟩,
end

lemma three_pt_ang_supplementary {a b c d : pts} :
supplementary (∠b a c) (∠b a d) ↔ between c a d ∧ noncol b a c ∧ noncol b a d :=
begin
  split,
  { rintros ⟨⟨a', b', c', d', hbac, hbad, hc'a'd'⟩, h₁, h₂⟩,
    have h₁' : ang_proper (∠ b' a' c'),
      rw ←hbac, exact h₁,
    have h₂' : ang_proper (∠ b' a' d'),
      rw ←hbad, exact h₂,
    rw ang_proper_iff_noncol at h₁ h₁' h₂ h₂',
    have haa' := ((three_pt_ang_eq_iff h₁).1 hbac).1,
    rw ←haa' at hc'a'd',
    cases ((three_pt_ang_eq_iff h₁).1 hbac).2 with H₁ H₁;
    cases ((three_pt_ang_eq_iff h₂).1 hbad).2 with H₂ H₂,
    { have had'c := diff_same_side_pt (between_diff_side_pt.1 hc'a'd') (same_side_pt_symm H₁.2),
      have hacd := diff_same_side_pt had'c (same_side_pt_symm H₂.2),
      exact ⟨between_diff_side_pt.2 hacd, h₁, h₂⟩ },
    { have had'c := diff_same_side_pt (between_diff_side_pt.1 hc'a'd') (same_side_pt_symm H₁.2),
      have hacb := diff_same_side_pt had'c (same_side_pt_symm H₂.1),
      have hacb' := diff_same_side_pt (diff_side_pt_symm hacb) H₁.1,
      have hacd := diff_same_side_pt (diff_side_pt_symm hacb') (same_side_pt_symm H₂.2),
      exact ⟨between_diff_side_pt.2 hacd, h₁, h₂⟩ },
    { have had'b := diff_same_side_pt (between_diff_side_pt.1 hc'a'd') (same_side_pt_symm H₁.1),
      have had'b' := diff_same_side_pt (diff_side_pt_symm had'b) H₂.1,
      have hab'd := diff_same_side_pt had'b' (same_side_pt_symm H₂.2),
      have hadc := diff_same_side_pt hab'd (same_side_pt_symm H₁.2),
      exact ⟨between_diff_side_pt.2 (diff_side_pt_symm hadc), h₁, h₂⟩ },
    { have had'b := diff_same_side_pt (between_diff_side_pt.1 hc'a'd') (same_side_pt_symm H₁.1),
      rw ←not_same_side_pt at had'b, exact absurd (same_side_pt_symm H₂.1) had'b,
      exact diff_side_pt_col had'b, exact had'b.2.1, exact had'b.2.2 } },
  rintros ⟨hcad, hbac, hbad⟩,
  use [a, b, c, d],
  exact ⟨rfl, rfl, hcad⟩,
  rw [ang_proper_iff_noncol, ang_proper_iff_noncol], exact ⟨hbac, hbad⟩
end

lemma inside_ang_trans {a b c d e : pts} :
inside_ang d (∠ b a c) → inside_ang e (∠ b a d) → inside_ang e (∠ b a c) :=
begin
  intros hd he,
  have hbac := ang_proper_iff_noncol.1 (inside_ang_proper hd),
  have hab := (noncol_neq hbac).1.symm,
  have hac := (noncol_neq hbac).2.2,
  have hbc := (noncol_neq hbac).2.1,
  cases crossbar hd with d' hd',
  rw inside_three_pt_ang at hd,
  have hd'a : d' ≠ a,
    intro hf, rw hf at hd', exact (noncol_in13 hbac) ((seg_in_line b c) hd'.2),
  have hd'b : d' ≠ b,
    intro hf, rw hf at hd',
    exact (noncol_in13 (same_side_line_noncol hd.1 hab).2) ((ray_in_line a d) hd'.1),
  have hd'c : d' ≠ c,
    intro hf, rw hf at hd',
    exact (noncol_in13 (same_side_line_noncol hd.2 hac).2) ((ray_in_line a d) hd'.1),
  have hadd' := ray_in_neq hd'a hd'.1,
  have hbd'c := seg_in_neq hd'b hd'c hd'.2,
  rw ang_eq_same_side_pt b hadd' at he,
  cases crossbar he with e' he',
  have he'a : e' ≠ a,
    intro hf, rw hf at he',
    exact noncol_in13 (ang_proper_iff_noncol.1 (inside_ang_proper he))
      ((seg_in_line b d') he'.2),
  have he'b : e' ≠ b,
    intro hf, rw hf at he',
    exact noncol_in21 (ang_proper_iff_noncol.1 (inside_ang_proper' he).1)
      ((ray_in_line a e) he'.1),
  have he'd' : e' ≠ d',
    intro hf, rw hf at he',
    exact noncol_in21 (ang_proper_iff_noncol.1 (inside_ang_proper' he).2)
      ((ray_in_line a e) he'.1),
  have haee' := ray_in_neq he'a he'.1,
  have hbe'c := seg_in_neq he'b he'd' he'.2,
  apply ray_inside_ang _ (same_side_pt_symm haee'),
  apply hypo_inside_ang hbac,
  rw between_symm at hbd'c hbe'c,
  rw between_symm,
  exact (between_trans' hbd'c hbe'c).2
end

lemma inside_ang_trans' {a o b c d : pts} (hboc : between b o c) :
inside_ang d (∠ a o b) → inside_ang a (∠ d o c) :=
begin
  have hoc := (between_neq hboc).2.2,
  intro hd,
  have haob := ang_proper_iff_noncol.1 (inside_ang_proper hd),
  have hao := (noncol_neq haob).1,
  have hob := (noncol_neq haob).2.2,
  rw inside_three_pt_ang at *,
  split,
  { have hoad := (same_side_line_noncol hd.1 hao.symm).2,
    have hobd := (same_side_line_noncol hd.2 hob).2,
    have hocd := col_noncol (col12 (between_col hboc)) hobd hoc,
    have hod := (noncol_neq hocd).2.1,
    have h₁ : diff_side_line (o-ₗd) a b,
      cases crossbar (inside_three_pt_ang.2 hd) with e he,
      use e, exact ⟨(ray_in_line o d) he.1, he.2⟩,
      exact ⟨noncol_in13 hoad, noncol_in13 hobd⟩,
    have h₂ : diff_side_line (o-ₗd) b c,
      have hdo := (same_side_line_neq' hd.1).1,
      apply diff_side_pt_line (between_diff_side_pt.1 hboc)
        (line_in_lines hdo.symm) (pt_left_in_line o d) (noncol_in13 hobd) (noncol_in13 hocd),
    exact same_side_line_symm (diff_side_line_cancel (line_in_lines hod) h₁ h₂) },
  { rw two_pt_one_line (line_in_lines hoc) (line_in_lines hob) hob (pt_left_in_line o c)
      (col_in23 (between_col hboc) hoc) (pt_left_in_line o b) (pt_right_in_line o b),
    exact same_side_line_symm hd.2 }
end
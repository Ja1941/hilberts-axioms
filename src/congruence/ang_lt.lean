/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import congruence.basic

/-!
# Angle orderness

This file defines how an angle is less than another and proves basic properties such as
transitivity and trichotomy.

## References

* See [Geometry: Euclid and Beyond]

-/

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--ang `α` is less than `β` if a part of it is congruent to `β`. That is,
there exists a point inside `α` with one ray of `α` forms an ang congruent to `β`-/
def ang_lt (α β : ang) : Prop :=
 ∃ a b p : C.pts, β = (∠ a β.vertex b) ∧ inside_ang p (∠ a β.vertex b)
  ∧ ((∠ a β.vertex p) ≅ₐ α)

notation a`<ₐ`b := ang_lt a b

lemma three_pt_ang_lt {a o b : C.pts} {α : ang} :
(α <ₐ (∠ a o b)) ↔ ∃ p : C.pts, inside_ang p (∠ a o b) ∧ ((∠ a o p) ≅ₐ α):=
begin
  split,
  { rintros ⟨a', b', p, haoba'ob', hp, ha'op⟩,
    rw three_pt_ang_vertex at haoba'ob' hp ha'op,
    have ha'ob' := ang_proper_iff_noncol.1 (inside_ang_proper hp),
    have haob : noncol a o b,
      rw [←ang_proper_iff_noncol, haoba'ob'],
      exact inside_ang_proper hp,
    have hoa := (noncol_neq haob).1.symm,
    cases ((three_pt_ang_eq_iff ha'ob').1 haoba'ob'.symm).2,
    { have haopa'op : (∠ a o p) = (∠ a' o p),
        rw [ang_symm, ang_symm a' _ _ ],
        refine ang_eq_same_side_pt _ _,
        exact same_side_pt_symm h.1,
      use p, rw [haoba'ob', haopa'op],
      exact ⟨hp, ha'op⟩ },
    { rcases extend_congr_ang (inside_ang_proper' hp).1 hoa
        (noncol_in12 (noncol12 haob)) with ⟨q, ha'opqoa, hqb, -⟩,
      use q, split,
      refine (congr_ang_sub hp hqb _ _ _).1,
      exact (same_side_pt_neq h.2).2.symm,
      rw haoba'ob', exact ang_congr_refl _,
      rw [ang_symm, ang_symm a o q], exact ha'opqoa,
      rw ang_symm, rw ang_symm at ha'op,
      exact ang_congr_trans (ang_congr_symm ha'opqoa) ha'op } },
  { rintros ⟨p, hp, haopα⟩,
    use [a, b, p],
    rw three_pt_ang_vertex, exact ⟨rfl, hp, haopα⟩ }
end

lemma ang_lt_congr {α β γ : ang} (hαβ : α ≅ₐ β) :
((α <ₐ γ) → (β <ₐ γ)) ∧ (ang_proper β → (γ <ₐ α) → (γ <ₐ β)) :=
begin
  rcases ang_three_pt α with ⟨a₁, b₁, hα⟩,
  rcases ang_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases ang_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw [hα, hβ, hγ], rw [hα, hβ] at hαβ,
  set o₁ := α.vertex, set o₂ := β.vertex, set o₃ := γ.vertex,
  split,
  { intro hαγ,
    rcases three_pt_ang_lt.1 hαγ with ⟨p, hpin, hp⟩,
    rw three_pt_ang_lt, use p,
    split, exact hpin,
    exact ang_congr_trans hp hαβ },
  { intros h hγα,
    rcases three_pt_ang_lt.1 hγα with ⟨p, hpin, hp⟩,
    rw ang_proper_iff_noncol at h,
    rcases extend_congr_ang (inside_ang_proper' hpin).1 (noncol_neq h).1.symm
      (noncol_in12 (noncol12 h)) with ⟨q, hq, hqb₂, -⟩,
    rw three_pt_ang_lt,
    rw ang_symm q _ _ at hq,
    use q, split,
    apply (congr_ang_sub hpin hqb₂ _ _ _).1,
    exact (noncol_neq h).1.symm,
    exact hαβ,
    rw ang_symm, exact hq,
    rw ang_symm at hq, exact ang_congr_trans (ang_congr_symm hq) hp }
end

lemma ang_lt_trans {α β γ : ang} :
ang_proper α → (α <ₐ β) → (β <ₐ γ) → (α <ₐ γ) :=
begin
  intros hα hαβ hβγ,
  rcases ang_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases ang_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw hγ, rw hβ at hαβ, rw [hβ, hγ] at hβγ,
  set o₂ := β.vertex, set o₃ := γ.vertex,
  rcases three_pt_ang_lt.1 hαβ with ⟨p, hpin, hp⟩,
  rcases three_pt_ang_lt.1 hβγ with ⟨q, hqin, hq⟩,
  have ha₃o₃b₃ := ang_proper_iff_noncol.1 (inside_ang_proper hqin),
  rcases extend_congr_ang hα (noncol_neq ha₃o₃b₃).1.symm (noncol_in23
    (ang_proper_iff_noncol.1 (inside_ang_proper' hqin).1)) with ⟨x, hx, hxq, -⟩,
  rw three_pt_ang_lt,
  use x, split,
  apply inside_ang_trans hqin,
  apply (congr_ang_sub hpin hxq _ _ _).1,
  exact (noncol_neq (ang_proper_iff_noncol.1
    (inside_ang_proper hqin))).1.symm,
  exact ang_congr_symm hq,
  rw ang_symm at hx, exact ang_congr_trans hp hx,
  rw ang_symm, exact ang_congr_symm hx
end

lemma ang_tri {α β : ang} (ha'o'b' : ang_proper α) (haob : ang_proper β) :
((α <ₐ β) ∨ (α ≅ₐ β) ∨ (β <ₐ α))
∧ ¬((α <ₐ β) ∧ (α ≅ₐ β)) ∧ ¬((α <ₐ β) ∧ (β <ₐ α)) ∧ ¬(((α ≅ₐ β) ∧ (β <ₐ α))) :=
begin
  rcases ang_three_pt β with ⟨a, b, hβ⟩,
  rw [hβ, ang_proper_iff_noncol] at haob, set o := β.vertex,
  have hao := (noncol_neq haob).1,
  have hbo := (noncol_neq haob).2.2.symm,
  rcases extend_congr_ang ha'o'b' hao.symm (noncol_in12
    (noncol12 haob)) with ⟨x, hx, hlxb, hu⟩,
  have hxo := (same_side_line_neq hlxb).1,
  have h₁ : same_side_line (o-ₗb) x a ↔ (α <ₐ β),
    rw hβ, split; rw three_pt_ang_lt,
    intro h₁,
    use x, split,
    rw inside_three_pt_ang,
    exact ⟨same_side_line_symm hlxb, same_side_line_symm h₁⟩,
    rw ang_symm, exact ang_congr_symm hx,
    rintros ⟨y, hyin, hy⟩, rw inside_three_pt_ang at hyin, rw ang_symm at hy,
    specialize hu y (same_side_line_trans (line_in_lines hao.symm) hlxb hyin.1)
      (ang_congr_symm hy),
    have hoxb := col_noncol (col_in13' ((ray_in_line o x) hu))
      (noncol23 (same_side_line_noncol hyin.2 hbo.symm).2) hxo.symm,
    have hyo := (same_side_line_neq' hyin.1).1,
    apply same_side_line_trans (line_in_lines hbo.symm) _ (same_side_line_symm hyin.2),
    rw line_symm,
    exact t_shape_ray (noncol132 hoxb) (ray_in_neq hyo hu),
  have h₂ : x ∈ (o-ₗb) ↔ (α ≅ₐ β),
    rw hβ, split; intro h₂,
    have : (∠ x o a) = (∠ a o b),
      rw ang_symm,
      apply ang_eq_same_side_pt _ _,
      cases (line_separation ⟨(o-ₗb), line_in_lines hbo.symm,
        pt_left_in_line o b, h₂, pt_right_in_line o b⟩ hxo hbo).1,
      exact h,
      { have hx := (same_side_line_notin hlxb).1,
        have hb := (same_side_line_notin hlxb).2,
        rw ←not_diff_side_line at hlxb, exfalso, apply hlxb,
        apply diff_side_pt_line h (line_in_lines hao.symm) (pt_left_in_line o a) hx hb,
        exact hx, exact hb },
    rw ←this, exact hx,
    { rw line_symm at hlxb, rw ang_symm at hx,
      exact col_in13 (ang_unique_same_side hao hlxb
        (ang_congr_trans (ang_congr_symm hx) h₂)).2 hbo.symm },
  have h₃ : diff_side_line (o-ₗb) x a ↔ (β <ₐ α),
    split; intro h₃,
    apply (ang_lt_congr (ang_congr_symm hx)).2 ha'o'b', rw ang_symm,
    rw three_pt_ang_lt, use b,
    split,
    rw inside_three_pt_ang, split, exact hlxb,
    exact diff_same_side_line' (diff_side_line_symm h₃) (same_side_line_symm hlxb),
    rw hβ, exact ang_congr_refl _,
    have : ang_proper (∠ x o a),
      rw ang_proper_iff_noncol,
      intro hxoa, exact (same_side_line_notin hlxb).1 (col_in23 hxoa hao.symm),
    have := (ang_lt_congr hx).2 this h₃, rw [ang_symm, three_pt_ang_lt] at this,
    rcases this with ⟨p, hpin, hp⟩, rw hβ at hp,
    have hopb : same_side_pt o p b,
      rw inside_three_pt_ang at hpin,
      rw line_symm at hpin hlxb,
      exact ang_unique_same_side hao
        (same_side_line_trans (line_in_lines hao) (same_side_line_symm hpin.1) hlxb) hp,
    { have hbin := ray_inside_ang hpin hopb,
      cases crossbar hbin with y hy,
      rw seg_symm at hy,
      use y, exact ⟨(ray_in_line o b) hy.1, hy.2⟩,
      rw inside_three_pt_ang at hbin,
      exact ⟨noncol_in13 (same_side_line_noncol hbin.2 hxo.symm).2, noncol_in23 haob⟩ },
  rw [←h₁, ←h₂, ←h₃],
  split, by_cases x ∈ (o-ₗb),
  right, left, exact h,
  cases (plane_separation h (noncol_in23 haob)).1 with h h,
  left, exact h, right, right, exact h,
  split, intro hf,
  exact (same_side_line_notin hf.1).1 hf.2,
  split, intro hf, rw ←not_diff_side_line at hf, exact hf.1 hf.2,
  exact hf.2.2.1, exact hf.2.2.2,
  intro hf, exact hf.2.2.1 hf.1
end

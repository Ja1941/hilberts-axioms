import organised.congruence.basic

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--Angle `α` is less than `β` if a part of it is congruent to `β`. That is,
there exists a point inside `α` with one ray of `α` forms an angle congruent to `β`-/
def angle_lt (α β : angle) : Prop :=
 ∃ a b p : C.pts, β = (∠ a β.vertex b) ∧ inside_angle p (∠ a β.vertex b)
  ∧ ((∠ a β.vertex p) ≅ₐ α)

notation a`<ₐ`b := angle_lt a b

lemma three_pt_angle_lt {a o b : C.pts} {α : angle} :
(α <ₐ (∠ a o b)) ↔ ∃ p : C.pts, inside_angle p (∠ a o b) ∧ ((∠ a o p) ≅ₐ α):=
begin
  split,
  rintros ⟨a', b', p, haoba'ob', hp, ha'op⟩,
  rw three_pt_angle_vertex at haoba'ob' hp ha'op,
  have ha'ob' := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  have haob : noncollinear a o b,
    rw [←angle_nontrivial_iff_noncollinear, haoba'ob'],
    exact inside_angle_nontrivial hp,
  have hoa := (noncollinear_neq haob).1.symm,
  cases ((three_pt_angle_eq_iff ha'ob').1 haoba'ob'.symm).2,
  have haopa'op : (∠ a o p) = (∠ a' o p),
    rw [angle_symm, angle_symm a' _ _ ],
    refine angle_eq_same_side _ _,
    exact same_side_pt_symm h.1,
  use p, rw [haoba'ob', haopa'op],
  exact ⟨hp, ha'op⟩,
  rcases extend_congr_angle (inside_angle_nontrivial' hp).1 hoa
    (noncollinear_in12 (noncollinear12 haob)) with ⟨q, ha'opqoa, hqb, -⟩,
  use q, split,
  refine (congr_angle_sub hp hqb _ _ _).1,
  exact (same_side_pt_neq h.2).2.symm,
  rw haoba'ob', exact angle_congr_refl _,
  rw [angle_symm, angle_symm a o q], exact ha'opqoa,
  rw angle_symm, rw angle_symm at ha'op,
  exact angle_congr_trans (angle_congr_symm ha'opqoa) ha'op,
  rintros ⟨p, hp, haopα⟩,
  use [a, b, p],
  rw three_pt_angle_vertex, exact ⟨rfl, hp, haopα⟩
end

lemma angle_lt_congr {α β γ : angle} (hαβ : α ≅ₐ β) :
((α <ₐ γ) → (β <ₐ γ)) ∧ (angle_nontrivial β → (γ <ₐ α) → (γ <ₐ β)) :=
begin
  rcases angle_three_pt α with ⟨a₁, b₁, hα⟩,
  rcases angle_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases angle_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw [hα, hβ, hγ], rw [hα, hβ] at hαβ,
  set o₁ := α.vertex, set o₂ := β.vertex, set o₃ := γ.vertex,
  split, intro hαγ,
  rcases three_pt_angle_lt.1 hαγ with ⟨p, hpin, hp⟩,
  rw three_pt_angle_lt, use p,
  split, exact hpin,
  exact angle_congr_trans hp hαβ,
  intros h hγα,
  rcases three_pt_angle_lt.1 hγα with ⟨p, hpin, hp⟩,
  rw angle_nontrivial_iff_noncollinear at h,
  rcases extend_congr_angle (inside_angle_nontrivial' hpin).1 (noncollinear_neq h).1.symm
    (noncollinear_in12 (noncollinear12 h)) with ⟨q, hq, hqb₂, -⟩,
  rw three_pt_angle_lt,
  rw angle_symm q _ _ at hq,
  use q, split,
  refine (congr_angle_sub hpin hqb₂ _ _ _).1,
  exact (noncollinear_neq h).1.symm,
  exact hαβ,
  rw angle_symm, exact hq,
  rw angle_symm at hq, exact angle_congr_trans (angle_congr_symm hq) hp
end

lemma angle_lt_trans {α β γ : angle} :
angle_nontrivial α → (α <ₐ β) → (β <ₐ γ) → (α <ₐ γ) :=
begin
  intros hα hαβ hβγ,
  rcases angle_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases angle_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw hγ, rw hβ at hαβ, rw [hβ, hγ] at hβγ,
  set o₂ := β.vertex, set o₃ := γ.vertex,
  rcases three_pt_angle_lt.1 hαβ with ⟨p, hpin, hp⟩,
  rcases three_pt_angle_lt.1 hβγ with ⟨q, hqin, hq⟩,
  have ha₃o₃b₃ := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hqin),
  rcases extend_congr_angle hα (noncollinear_neq ha₃o₃b₃).1.symm (noncollinear_in23
    (angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial' hqin).1)) with ⟨x, hx, hxq, -⟩,
  rw three_pt_angle_lt,
  use x, split,
  apply inside_angle_trans hqin,
  refine (congr_angle_sub hpin hxq _ _ _).1,
  exact (noncollinear_neq (angle_nontrivial_iff_noncollinear.1
    (inside_angle_nontrivial hqin))).1.symm,
  exact angle_congr_symm hq,
  rw angle_symm at hx, exact angle_congr_trans hp hx,
  rw angle_symm, exact angle_congr_symm hx
end

lemma angle_tri {α β : angle} (ha'o'b' : angle_nontrivial α) (haob : angle_nontrivial β) :
((α <ₐ β) ∨ (α ≅ₐ β) ∨ (β <ₐ α))
∧ ¬((α <ₐ β) ∧ (α ≅ₐ β)) ∧ ¬((α <ₐ β) ∧ (β <ₐ α)) ∧ ¬(((α ≅ₐ β) ∧ (β <ₐ α))) :=
begin
  rcases angle_three_pt β with ⟨a, b, hβ⟩,
  rw [hβ, angle_nontrivial_iff_noncollinear] at haob, set o := β.vertex,
  have hao := (noncollinear_neq haob).1,
  have hbo := (noncollinear_neq haob).2.2.symm,
  rcases extend_congr_angle ha'o'b' hao.symm (noncollinear_in12
    (noncollinear12 haob)) with ⟨x, hx, hlxb, hu⟩,
  have hxo : x ≠ o,
    intro hxo, rw hxo at hlxb,
    exact (same_side_line_not_in hlxb).1 (pt_left_in_line o a),
  have h₁ : same_side_line (o-ₗb) x a ↔ (α <ₐ β),
    rw hβ, split; rw three_pt_angle_lt, intro h₁,
    use x, split,
    rw inside_three_pt_angle,
    exact ⟨same_side_line_symm hlxb, same_side_line_symm h₁⟩,
    rw angle_symm, exact angle_congr_symm hx,
    rintros ⟨y, hyin, hy⟩, rw inside_three_pt_angle at hyin, rw angle_symm at hy,
    specialize hu y (same_side_line_trans (line_in_lines hao.symm) hlxb hyin.1)
      (angle_congr_symm hy),
    refine same_side_line_trans (line_in_lines hbo.symm) _ (same_side_line_symm hyin.2),
    rw line_symm, refine t_shape_ray hbo _ _ _ _,
    intro hf, have := (collinear_trans ⟨(b-ₗo), line_in_lines hbo,
      pt_right_in_line b o, hf, pt_left_in_line b o⟩ (in_ray_collinear hu) hxo.symm),
    exact (same_side_line_not_in hyin.2).2 (collinear_in12 this hbo.symm),
    exact hu, intro hyo, rw hyo at hyin,
    exact (same_side_line_not_in hyin.2).2 (pt_left_in_line o b),
  have h₂ : x ∈ (o-ₗb) ↔ (α ≅ₐ β),
    rw hβ, split; intro h₂,
    have : (∠ x o a) = (∠ a o b),
      rw angle_symm,
      refine angle_eq_same_side _ _,
      cases (line_separation ⟨(o-ₗb), line_in_lines hbo.symm,
        pt_left_in_line o b, h₂, pt_right_in_line o b⟩ hxo hbo).1,
      exact h,
      rw ←not_diff_side_line at hlxb, exfalso, apply hlxb,
      apply (diff_side_pt_line h).2.2.2 (line_in_lines hao.symm),
      split, exact pt_left_in_line o a,
      have : b ∉ (o-ₗa),
        intro hf, exact haob ⟨(o-ₗa), line_in_lines hao.symm,
          pt_right_in_line o a, pt_left_in_line o a, hf⟩,
      split, intro hf,
      rcases (diff_side_pt_collinear h) with ⟨l, hl, hol, hxl, hbl⟩,
      rw two_pt_one_line hl (line_in_lines hao.symm) hxo ⟨hxl, hol⟩
        ⟨hf, pt_left_in_line o a⟩ at hbl,
      exact this hbl, exact this,
      exact (same_side_line_not_in hlxb).1,
      exact (same_side_line_not_in hlxb).2,
    rw ←this, exact hx,
    rw angle_symm at h₂, specialize hu b hlxb h₂,
    exact collinear_in13 (in_ray_collinear hu) hbo.symm,
  have h₃ : diff_side_line (o-ₗb) x a ↔ (β <ₐ α),
    split; intro h₃,
    apply (angle_lt_congr (angle_congr_symm hx)).2 ha'o'b', rw angle_symm,
    rw three_pt_angle_lt, use b,
    split,
    rw inside_three_pt_angle, split, exact hlxb,
    exact diff_same_side_line (diff_side_line_symm h₃) hlxb,
    rw hβ, exact angle_congr_refl _,
    have : angle_nontrivial (∠ x o a),
      rw angle_nontrivial_iff_noncollinear,
      intro hxoa, exact (same_side_line_not_in hlxb).1 (collinear_in23 hxoa hao.symm),
    have := (angle_lt_congr hx).2 this h₃, rw [angle_symm, three_pt_angle_lt] at this,
    rcases this with ⟨p, hpin, hp⟩, rw hβ at hp,
    have hopb : same_side_pt o p b,
      rw inside_three_pt_angle at hpin,
      refine angle_congr_same_side_unique hp _ _,
      intro haop, rw line_symm at hpin, exact (same_side_line_not_in hpin.1).2
        (collinear_in12 haop hao),
      rw line_symm, exact same_side_line_trans (line_in_lines hao.symm)
        (same_side_line_symm hpin.1) hlxb,
    exact diff_side_line_symm (inside_angle_diff_side_line (ray_inside_angle hpin hopb)),
  rw [←h₁, ←h₂, ←h₃],
  split, by_cases x ∈ (o-ₗb),
  right, left, exact h,
  cases (plane_separation h (noncollinear_in23 haob)).1 with h h,
  left, exact h, right, right, exact h,
  split, intro hf,
  exact (same_side_line_not_in hf.1).1 hf.2,
  split, intro hf, rw ←not_diff_side_line at hf, exact hf.1 hf.2,
  exact hf.2.2.1, exact hf.2.2.2,
  intro hf, exact hf.2.2.1 hf.1
end

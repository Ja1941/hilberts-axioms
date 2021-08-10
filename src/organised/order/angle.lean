import organised.order.sideness

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
  intro hf, unfold two_pt_segment at hf, simp at hf, exfalso, exact hf
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

lemma in_ray_collinear {o a b : pts} : b ∈ (o-ᵣa).inside → collinear o a b :=
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

lemma segment_in_ray (o a : pts) : (o-ₛa).inside ⊆ (o-ᵣa).inside :=
begin
  unfold two_pt_ray, unfold two_pt_segment,
  intros x hx, simp at hx, simp,
  rcases hx with hx | hx | hx,
  rw hx, simp,
  rw hx, by_cases hao : a = o, rw hao, left, refl,
  right, split,
  rw segment_singleton, exact ne.symm hao,
  exact ⟨(a-ₗo), line_in_lines hao,
    pt_right_in_line a o, pt_left_in_line a o, pt_left_in_line a o⟩,
  right, unfold same_side_pt, unfold two_pt_segment, simp, split,
  intro hf, rcases hf with hf | hf | hf,
  rw hf at hx, exact (is_between_not_eq hx).2.1 rfl,
  exact (is_between_not_eq hx).1 hf,
  rw is_between_symm at hx, exact (collinear_between (is_between_collinear hf)).2.1 ⟨hf, hx⟩,
  rcases (is_between_collinear hx) with ⟨l, hl, hol, hxl, hal⟩,
  exact ⟨l, hl, hol, hal, hxl⟩
end

lemma ray_in_line (o a : pts) : (o-ᵣa).inside ⊆ (o-ₗa) :=
begin
  unfold two_pt_ray same_side_pt, intros x hx,
  simp at hx, cases hx with hx hx,
  rw hx, exact pt_left_in_line o a,
  have hoa : o ≠ a, intro hoa, rw hoa at hx, unfold two_pt_segment at hx, simp at hx, exact hx,
  rcases hx.2 with ⟨l, hl, hol, hal, hxl⟩,
  rw (two_pt_one_line (line_in_lines hoa) hl hoa
    ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨hol, hal⟩),
  exact hxl
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
    right, exact same_side_pt_symm (is_between_same_side_pt.1 hoxa).1,
  unfold two_pt_ray at hx, simp at hx,
  cases hx with hx hx, exact absurd hx (is_between_not_eq hoxa).1.symm,
  exact same_side_pt_trans (same_side_pt_symm (is_between_same_side_pt.1 hoxa).1)
    (same_side_pt_symm hx)
end

lemma t_shape_ray {a b : pts} {e : pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (b-ᵣe).inside, x ≠ b → same_side_line (a-ₗb) e x :=
begin
  intros x hxbe hxb, rintros ⟨f, hfab, hfex⟩,
  have heb : e ≠ b, intro heb, rw [heb, ray_singleton] at hxbe, exact hxb hxbe,
  have hfeb : f ∈ (e-ₗb),
    have hxeb : x ∈ (e-ₗb),
      rw line_symm, from (ray_in_line b e) hxbe,
    by_cases hex : e = x, rw [←hex, segment_singleton] at hfex,
    simp at hfex, rw hfex, exact pt_left_in_line e b,
    rw (two_pt_one_line (line_in_lines heb) (line_in_lines hex)
      hex ⟨pt_left_in_line e b, hxeb⟩ ⟨pt_left_in_line e x, pt_right_in_line e x⟩),
    exact (segment_in_line e x) hfex,
  have hebab : (e-ₗb) ≠ (a-ₗb),
    intro hebab, have heeb := pt_left_in_line e b, rw hebab at heeb, exact heab heeb,
  rw (two_line_one_pt (line_in_lines heb) (line_in_lines hab)
    hebab hfeb hfab (pt_right_in_line e b) (pt_right_in_line a b)) at hfex,
  unfold two_pt_segment at hfex, unfold two_pt_ray at hxbe, simp at hxbe hfex,
  rcases hfex with hfex | hfex | hfex, exact heb.symm hfex, exact hxb.symm hfex,
  rcases hxbe with hxbe | hxbe,
  exact hxb hxbe,
  unfold same_side_pt at hxbe, unfold two_pt_segment at hxbe, simp at hxbe,
  push_neg at hxbe, exact hxbe.1.2.2 hfex
end

lemma t_shape_segment {a b : pts} {e : pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (b-ₛe).inside, x ≠ b → same_side_line (a-ₗb) e x :=
λ x hxbe hxb, t_shape_ray hab heab x ((segment_in_ray b e) hxbe) hxb

lemma diff_same_side_line {a o b x : pts} :
diff_side_line (o-ₗb) a x → same_side_line (o-ₗa) x b → same_side_line (o-ₗx) a b :=
begin
  intros h₁ h₂,
  have hoa : o ≠ a,
    intro hoa, rw hoa at h₁, exact h₁.2.1 (pt_left_in_line a b),
  have hox : o ≠ x,
    intro hox, rw ←hox at h₂, exact (same_side_line_not_in h₂).1 (pt_left_in_line o a),
  have hab : a ≠ b,
    intro hab, rw hab at h₁, exact h₁.2.1 (pt_right_in_line o b),
  have hob : o ≠ b,
    intro hob, rw hob at h₂, exact (same_side_line_not_in h₂).2 (pt_left_in_line b a),
  have hax : a ≠ x,
    intro hax, rw ←hax at h₂, exact (same_side_line_not_in h₂).1 (pt_right_in_line o a),
  cases h₁.1 with b' hb',
  have hab' : a ≠ b',
    intro hab', rw ←hab' at hb', exact h₁.2.1 hb'.1,
  have hob' : o ≠ b',
    intro hob', rw ←hob' at hb',
    rw two_pt_one_line (line_in_lines hoa) (line_in_lines hax) hoa ⟨pt_left_in_line o a,
      pt_right_in_line o a⟩ ⟨(segment_in_line a x) hb'.2, pt_left_in_line a x⟩ at h₂,
    exact (same_side_line_not_in h₂).1 (pt_right_in_line a x),
  have hb'oa : b' ∉ (o-ₗa),
    intro hob'oa, rw two_pt_one_line (line_in_lines hob) (line_in_lines hoa) hob' at h₁,
    exact h₁.2.1 (pt_right_in_line o a), exact ⟨pt_left_in_line o b, hb'.1⟩,
    exact ⟨pt_left_in_line o a, hob'oa⟩,
  have : same_side_line (o-ₗx) b b',
    rw line_symm, refine t_shape_ray _ _ _ _ _,
    exact hox.symm,
    intro hf, rw two_pt_one_line (line_in_lines hob) (line_in_lines hox.symm) hob at h₁,
    exact h₁.2.2 (pt_left_in_line x o),
    exact ⟨pt_left_in_line o b, pt_right_in_line o b⟩,
    exact ⟨pt_right_in_line x o, hf⟩,
    cases (line_separation ⟨(o-ₗb), line_in_lines hob, pt_left_in_line o b,
      pt_right_in_line o b, hb'.1⟩ hob.symm hob'.symm).1 with hobb' hobb',
    left, exact hobb',
    have := (diff_side_pt_line hobb').2.2.2 (line_in_lines hoa)
      ⟨(pt_left_in_line o a), (same_side_line_not_in h₂).2, hb'oa⟩,
    have hxoa : x ∉ (o-ₗa),
      intro hxoa, rw two_pt_one_line (line_in_lines hoa) (line_in_lines hox)
        hox ⟨pt_left_in_line o a, hxoa⟩ ⟨pt_left_in_line o x, pt_right_in_line o x⟩ at h₂,
      exact (same_side_line_not_in h₂).1 (pt_right_in_line o x),
    exfalso, apply (not_diff_side_line hxoa ((same_side_line_not_in h₂).2)).2 h₂,
    apply diff_side_line_symm ,
    apply diff_side_same_side_line (line_in_lines hoa) this,
    apply same_side_line_symm,
    refine t_shape_segment hoa hxoa _ _ _, exact hb'.2, exact hab'.symm,
    exact hob'.symm,
  apply same_side_line_symm, apply same_side_line_trans (line_in_lines hox) this,
  cases hb'.2 with hab'x hf,
  simp at hab'x, rw is_between_same_side_pt at hab'x,
  apply same_side_line_symm,
  apply (same_side_pt_line hab'x.2).2.2.2 (line_in_lines hox) _,
  split, exact pt_right_in_line o x,
  split,
  intro haox, rw two_pt_one_line (line_in_lines hoa) (line_in_lines hox)
    hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨pt_left_in_line o x, haox⟩ at h₂,
  exact (same_side_line_not_in h₂).1 (pt_right_in_line o x),
  exact (same_side_line_not_in this).2,
  cases hf with hf hf,
  exact absurd hf.symm hab',
  simp at hf, rw hf at this, exact absurd (pt_right_in_line o x) (same_side_line_not_in this).2,
end

/--A type given by a vertex and its inside is the union of two rays with this vertex. -/
structure angle := (vertex : pts) (inside : set pts)
(in_eq : ∃ a b : pts, inside = (vertex-ᵣa).inside ∪ (vertex-ᵣb).inside)

lemma vertex_in_angle (α : angle) : α.vertex ∈ α.inside :=
by { rcases α.in_eq with ⟨a, b, h⟩, rw h, left, exact pt_left_in_ray _ _ }

/--Define an angle by giving its vertex and two other points on the two rays. -/
def three_pt_angle (a o b : pts) : angle := ⟨o, (o-ᵣa).inside∪(o-ᵣb).inside, ⟨a, b, rfl⟩⟩

notation `∠` := three_pt_angle

lemma angle_symm (a o b : pts) : ∠ a o b = ∠ b o a :=
by {unfold three_pt_angle, simp, rw union_comm}

lemma three_pt_angle_vertex (a o b : pts) : (∠ a o b).vertex = o :=
by unfold three_pt_angle

lemma pt_left_in_three_pt_angle (a o b : pts) : a ∈ (∠ a o b).inside :=
begin
  unfold three_pt_angle two_pt_ray, simp, left,
  by_cases a = o, left, exact h,
  right, exact (same_side_pt_refl (ne.symm h))
end

lemma pt_right_in_three_pt_angle (a o b : pts) : b ∈ (∠ a o b).inside :=
by {rw angle_symm, exact pt_left_in_three_pt_angle b o a}

lemma angle_eq_same_side (a : pts) {o b c : pts} (hobc : same_side_pt o b c) :
∠ a o b = ∠ a o c :=
by {unfold three_pt_angle, simp, rw two_pt_ray_eq_same_side_pt hobc}

/--An angle is nontrivial if its two sides are noncollinear. -/
def angle_nontrivial (α : angle) : Prop :=
∀ l ∈ lines, ¬α.inside ⊆ l

lemma three_pt_angle_nontrivial_not_eq {a o b : pts} :
angle_nontrivial (∠ a o b) → a ≠ o ∧ a ≠ b ∧ o ≠ b :=
begin
  intro h, unfold angle_nontrivial at h,
  have h₁ : a ≠ o ∨ a ≠ b ∨ o ≠ b,
    by_contra h₁, push_neg at h₁, rw [h₁.1, h₁.2.2] at h,
    rcases one_pt_line b with ⟨l, hl, hbl⟩,
    apply h l hl, unfold three_pt_angle two_pt_ray, intros x hx,
    simp at hx, cases hx with hx hx, rw hx, exact hbl,
    exact absurd rfl (same_side_pt_neq hx).1,
  by_contra hf, rw [not_and_distrib, not_and_distrib, not_not, not_not, not_not] at hf,
  rcases h₁ with hao | hab | hob,
  rcases hf with hf | hf | hf, exact hao hf,
  rw ←hf at h, apply h (a-ₗo) (line_in_lines hao),
  unfold three_pt_angle, intros x hx, simp at hx,
  rw line_symm, exact (ray_in_line o a) hx,
  rw ←hf at h, apply h (a-ₗo) (line_in_lines hao),
  unfold three_pt_angle, intros x hx, simp at hx, cases hx with hx hx,
  rw line_symm, exact (ray_in_line o a) hx,
  rw ray_singleton at hx, simp at hx, rw hx, exact pt_right_in_line a o,
  rcases hf with hf | hf | hf,
  rw ←hf at h, apply h (a-ₗb) (line_in_lines hab),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw ray_singleton at hx, simp at hx, rw hx, exact pt_left_in_line a b,
  exact (ray_in_line a b) hx,
  exact hab hf,
  rw hf at h, apply h (a-ₗb) (line_in_lines hab),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw line_symm, exact (ray_in_line b a) hx,
  rw ray_singleton at hx, simp at hx, rw hx, exact pt_right_in_line a b,
  rcases hf with hf | hf | hf,
  rw hf at h, apply h (o-ₗb) (line_in_lines hob),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw ray_singleton at hx, simp at hx, rw hx, exact pt_left_in_line o b,
  exact (ray_in_line o b) hx,
  rw hf at h, apply h (o-ₗb) (line_in_lines hob),
  unfold three_pt_angle, intros x hx, simp at hx,
  exact (ray_in_line o b) hx,
  exact hob hf
end

lemma angle_nontrivial_iff_noncollinear {a o b : pts} :
angle_nontrivial (∠ a o b) ↔ noncollinear a o b :=
begin
  split; intro h,
  have hoa : o ≠ a, from (three_pt_angle_nontrivial_not_eq h).1.symm,
  have hob : o ≠ b, from (three_pt_angle_nontrivial_not_eq h).2.2,
  rintros ⟨l, hl, hal, hol, hbl⟩,
  unfold angle_nontrivial three_pt_angle at h, simp only at h,
  apply h l hl,
  unfold two_pt_ray, simp only, intros x hx, simp at hx,
  rcases hx with (hx | hx) | hx,
  rw hx, exact hol,
  rcases hx.2 with ⟨m, hm, hom, ham, hxm⟩,
  rw two_pt_one_line hm hl hoa ⟨hom, ham⟩ ⟨hol, hal⟩ at hxm, exact hxm,
  rcases hx.2 with ⟨m, hm, hom, hbm, hxm⟩,
  rw two_pt_one_line hm hl hob ⟨hom, hbm⟩ ⟨hol, hbl⟩ at hxm, exact hxm,
  intros l hl hf,
  have ha : a ∈ (∠ a o b).inside, from pt_left_in_three_pt_angle a o b,
  have hb : b ∈ (∠ a o b).inside, from pt_right_in_three_pt_angle a o b,
  have ho : o ∈ (∠ a o b).inside, have := vertex_in_angle (∠ a o b),
  rw three_pt_angle_vertex at this, exact this,
  exact h ⟨l, hl, hf ha, hf ho, hf hb⟩
end

private lemma three_pt_angle_eq_iff_prep {a o b a' b' : pts} (haob : angle_nontrivial (∠ a o b)) :
(∠ a o b) = (∠ a' o b') → same_side_pt o a a' → same_side_pt o b b' :=
begin
  intros he hoaa',
  have ha'ob' : noncollinear a' o b',
    rw he at haob, exact angle_nontrivial_iff_noncollinear.1 haob,
  rw angle_nontrivial_iff_noncollinear at haob,
  have hoa := (noncollinear_neq haob).1.symm,
  have hob := (noncollinear_neq haob).2.2,
  have hob' := (noncollinear_neq ha'ob').2.2,
  by_cases hbb' : b = b',
    rw ←hbb', exact same_side_pt_symm (same_side_pt_refl hob),
  have hb' : b' ∈ (∠ a o b).inside,
    rw he, unfold three_pt_angle, right, exact pt_right_in_ray o b',
  cases hb' with hb' hb',
  exfalso, apply noncollinear12 ha'ob',
  exact collinear_trans hoaa'.2 ⟨(o-ₗa), line_in_lines hoa,
    pt_left_in_line o a, pt_right_in_line o a, (ray_in_line o a) hb'⟩ hoa,
  cases hb' with hb' hb',
  exact hb', exact absurd hb' hob'.symm
end

lemma three_pt_angle_eq_iff {a o b a' o' b' : pts}
(haob : noncollinear a o b) : (∠ a o b) = (∠ a' o' b') ↔ o = o'
∧ ((same_side_pt o a a' ∧ same_side_pt o b b') ∨ (same_side_pt o a b' ∧ same_side_pt o b a')) :=
begin
  split, intro he,
  have hoo' : o = o',
    unfold three_pt_angle at he, simp at he, exact he.1,
  have ha'ob' : noncollinear a' o b',
    rw [←angle_nontrivial_iff_noncollinear, he, ←hoo'] at haob,
    exact angle_nontrivial_iff_noncollinear.1 haob,
  have ha'o := (noncollinear_neq ha'ob').1,
  split, exact hoo',
  rw ←hoo' at he,
  have ha' : a' ∈ (∠ a o b).inside,
    rw he, unfold three_pt_angle, left, exact pt_right_in_ray o a',
  cases ha' with ha' ha';
  cases ha' with ha' ha',
  left, exact ⟨ha', three_pt_angle_eq_iff_prep (angle_nontrivial_iff_noncollinear.2 haob) he ha'⟩,
  exact absurd ha' ha'o,
  right, rw angle_symm at he,
  exact ⟨three_pt_angle_eq_iff_prep (angle_nontrivial_iff_noncollinear.2
    (noncollinear13 haob)) he ha', ha'⟩,
  exact absurd ha' ha'o,
  rintros ⟨hoo', h | h⟩,
  rw [angle_eq_same_side a h.2, angle_symm, angle_eq_same_side b' h.1, angle_symm, hoo'],
  rw [angle_eq_same_side a h.2, angle_symm, angle_eq_same_side a' h.1, hoo']
end

lemma angle_three_pt (α : angle) : ∃ a b : pts, α = ∠ a α.vertex b :=
begin
  rcases α.in_eq with ⟨a, b, h⟩,
  use [a, b], unfold three_pt_angle, induction α, simp, exact h
end

/--A point `p` is inside `∠ a o b` if `p` and `a` are on the same side to `o-ₗa` and
`p` and `b` are on the same side to line `o-ₗb`. -/
def inside_angle (p : pts) (α : angle) : Prop :=
(∃ a b : pts, α = ∠ a α.vertex b
∧ same_side_line (α.vertex-ₗa) b p ∧ same_side_line (α.vertex-ₗb) a p)

lemma inside_angle_nontrivial {p : pts} {α : angle} :
inside_angle p α → angle_nontrivial α :=
begin
  rintros ⟨a, b, hα, hbp, hap⟩,
  rw [hα, angle_nontrivial_iff_noncollinear],
  intro haob,
  by_cases α.vertex = b,
    rw h at hbp,
    exact (same_side_line_not_in hbp).1 (pt_left_in_line b a),
  exact (same_side_line_not_in hap).1 (collinear_in23 haob h)
end

lemma inside_three_pt_angle {p a o b : pts}:
inside_angle p (∠ a o b) ↔ same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p :=
begin
  have : ∀ {p a o b a' b' : pts}, same_side_line (o-ₗa') b' p → same_side_line (o-ₗb') a' p
    → noncollinear a' o b' → same_side_pt o a a' ∧ same_side_pt o b b'
    → same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p,
    intros p a o b a' b' hb'p ha'p ha'ob' h,
    rw two_pt_one_line (line_in_lines (same_side_pt_neq h.1).1.symm)
      (line_in_lines (same_side_pt_neq h.1).2.symm),
    rw two_pt_one_line (line_in_lines (same_side_pt_neq h.2).1.symm)
      (line_in_lines (same_side_pt_neq h.2).2.symm),
    split, apply same_side_line_symm,
    apply same_side_line_trans (line_in_lines (same_side_pt_neq h.1).2.symm)
      (same_side_line_symm hb'p),
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact (same_side_pt_neq h.1).2,
    intro hf, exact ha'ob' ⟨(a'-ₗo), line_in_lines (same_side_pt_neq h.1).2,
      pt_left_in_line a' o, pt_right_in_line a' o, hf⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm h.2,
    exact (same_side_pt_neq h.2).1,
    apply same_side_line_symm,
    apply same_side_line_trans (line_in_lines (same_side_pt_neq h.2).2.symm)
      (same_side_line_symm ha'p),
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact (same_side_pt_neq h.2).2,
    intro hf, exact ha'ob' ⟨(b'-ₗo), line_in_lines (same_side_pt_neq h.2).2,
      hf, pt_right_in_line b' o, pt_left_in_line b' o⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm h.1,
    exact (same_side_pt_neq h.1).1,
    exact (same_side_pt_neq h.2).1, exact ⟨pt_right_in_line o b, pt_left_in_line o b⟩,
    split, apply ray_in_line o b', left, exact same_side_pt_symm h.2, exact pt_left_in_line o b',
    exact (same_side_pt_neq h.1).1, exact ⟨pt_right_in_line o a, pt_left_in_line o a⟩,
    split, apply ray_in_line o a', left, exact same_side_pt_symm h.1, exact pt_left_in_line o a',
  split, intro hp,
  have haob := inside_angle_nontrivial hp,
  rcases hp with ⟨a', b', haoba'ob', hb'p, ha'p⟩,
  rw three_pt_angle_vertex at haoba'ob' ha'p hb'p,
  have ha'ob' : noncollinear a' o b',
    rw [haoba'ob', angle_nontrivial_iff_noncollinear] at haob, exact haob,
  rw angle_nontrivial_iff_noncollinear at haob,
  cases ((three_pt_angle_eq_iff haob).1 haoba'ob').2,
  exact this hb'p ha'p ha'ob' h,
  exact this ha'p hb'p (noncollinear13 ha'ob') h,
  rintros ⟨hbp, hap⟩,
  use [a, b], rw three_pt_angle_vertex,
  exact ⟨rfl, hbp, hap⟩
end

lemma inside_angle_nontrivial' {p a o b : pts} : inside_angle p (∠ a o b)
→ angle_nontrivial (∠ p o a) ∧ angle_nontrivial (∠ p o b) :=
begin
  intro hp,
  have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  have hoa := (noncollinear_neq haob).1.symm,
  have hob := (noncollinear_neq haob).2.2,
  rw inside_three_pt_angle at hp,
  split; rw angle_nontrivial_iff_noncollinear; intro h,
  exact (same_side_line_not_in hp.1).2 (collinear_in23 h hoa),
  exact (same_side_line_not_in hp.2).2 (collinear_in23 h hob)
end

theorem crossbar {a b c d : pts}
(hd : inside_angle d (∠ b a c)) : (two_pt_ray a d).inside ♥ (b-ₛc).inside :=
begin
  have hbac := inside_angle_nontrivial hd, rw angle_nontrivial_iff_noncollinear at hbac,
  rw inside_three_pt_angle at hd,
  by_cases hac : a = c,
    rw hac, use c, unfold two_pt_ray, unfold two_pt_segment, simp,
  by_cases hab : a = b,
    rw hab, use b, unfold two_pt_ray, unfold two_pt_segment, simp,
  cases is_between_extend (ne.symm hac) with e hcae,
  have had : a ≠ d,
    intro had, rw ←had at hd, have hf := (same_side_line_not_in hd.1).2,
    have ht := pt_left_in_line a b, exact hf ht,
  have hec : e ≠ c,
    intro hec, rw hec at hcae, exact (is_between_not_eq hcae).2.1 rfl,
  have hecb : noncollinear e c b,
    rintros ⟨l, hl, hel, hcl, hbl⟩,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    rw (two_pt_one_line hm hl hec ⟨hem, hcm⟩ ⟨hel, hcl⟩) at ham,
    exact hbac ⟨l, hl, hbl, ham, hcl⟩,
  have hae : a ≠ e,
    intro hae, rw hae at hcae, exact (is_between_not_eq hcae).2.2 rfl,
  have h₁ : (((a-ₗd) ♥ (e-ₛb).inside) ∨ ((a-ₗd) ♥ (c-ₛb).inside))
    ∧ ¬(((a-ₗd) ♥ (e-ₛb).inside) ∧ ((a-ₗd) ♥ (c-ₛb).inside)),
    apply pasch hecb (line_in_lines had),
    intro haed,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    rw ←(two_pt_one_line hm (line_in_lines had) hae ⟨ham, hem⟩ ⟨pt_left_in_line a d, haed⟩) at hf,
    rw (two_pt_one_line hm (line_in_lines hac) hac ⟨ham, hcm⟩
      ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    intro hacd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac) hac
      ⟨pt_left_in_line a d, hacd⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    intro habd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab
      ⟨pt_left_in_line a d, habd⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at hf,
    unfold same_side_line at hd, apply hd.1, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    use a, split, exact pt_left_in_line a d,
    unfold two_pt_segment, simp, right, right, rw is_between_symm at hcae, exact hcae,
  have hbeab : ∀ x ∈ (b-ₛe).inside, x ≠ b → same_side_line (a-ₗb) e x,
    have heab : e ∉ (a-ₗb),
      have heac : e ∈ (a-ₗc),
        rcases (is_between_collinear hcae) with ⟨l, hl, hcl, hal, hel⟩,
        rw (two_pt_one_line (line_in_lines hac) hl hac
          ⟨pt_left_in_line a c, pt_right_in_line a c⟩ ⟨hal, hcl⟩),
        exact hel,
      intro heab,
      have habac : (a-ₗb) = (a-ₗc), from two_pt_one_line (line_in_lines hab)
        (line_in_lines hac) hae ⟨pt_left_in_line a b, heab⟩ ⟨pt_left_in_line a c, heac⟩,
      exact hbac ⟨(a-ₗb), line_in_lines hab, pt_right_in_line a b,
        pt_left_in_line a b, by {rw habac, exact pt_right_in_line a c}⟩,
    exact t_shape_segment hab heab,
  have haeac : (a-ₗe) = (a-ₗc),
    rcases (is_between_collinear hcae) with ⟨l, hl, hcl, hal, hel⟩,
    rw (two_pt_one_line (line_in_lines hae) hl hae
      ⟨pt_left_in_line a e, pt_right_in_line a e⟩ ⟨hal, hel⟩),
    rw (two_pt_one_line (line_in_lines hac) hl hac
      ⟨pt_left_in_line a c, pt_right_in_line a c⟩ ⟨hal, hcl⟩),
  have hbeac : ∀ x ∈ (b-ₛe).inside, x ≠ e → same_side_line (a-ₗc) b x,
    have hbae : b ∉ (a-ₗe),
      rw haeac, intro hf, exact hbac ⟨(a-ₗc), line_in_lines hac, hf,
        pt_left_in_line a c, pt_right_in_line a c⟩, 
    intros x hxbe hxe, rw segment_symm at hxbe, rw ←haeac,
    exact t_shape_segment hae hbae x hxbe hxe,
  have hadab : ∀ x ∈ (a-ᵣd).inside, x ≠ a → same_side_line (a-ₗb) d x,
    have hdba : d ∉ (b-ₗa), rw line_symm, from (same_side_line_not_in hd.1).2,
    rw line_symm a b, exact t_shape_ray (ne.symm hab) hdba,
  have hdbac : same_side_line (a-ₗc) d b, from same_side_line_symm hd.2,
  have h₂ : ¬((a-ₗd) ♥ (e-ₛb).inside),
    have hdcab := same_side_line_symm hd.1,
    rintros ⟨f, hf⟩, rw segment_symm at hf, simp at hf,
    have hfb : f ≠ b,
      intro hfb, rw hfb at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab
        ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at this,
      exact (same_side_line_not_in hd.1).2 this,
    have hfe : f ≠ e,
      intro hfe, rw hfe at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hae) hae
        ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this, exact (same_side_line_not_in hd.2).2 this,
    have hfa : f ≠ a,
      intro hfa, rw hfa at hf, have := pt_right_in_line e b,
      have heb := (noncollinear_neq hecb).2.1,
      rw segment_symm at hf,
      rw (two_pt_one_line (line_in_lines heb) (line_in_lines hae) hae
        ⟨segment_in_line e b hf.2, pt_left_in_line e b⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this,
      exact hbac ⟨(a-ₗc) ,line_in_lines hac, this, pt_left_in_line a c, pt_right_in_line a c⟩,
    specialize hbeab f hf.2 hfb,
    specialize hbeac f hf.2 hfe,
    have hdfac := same_side_line_trans (line_in_lines hac) hdbac hbeac,
    have hfad : f ∈ (a-ᵣd).inside,
      unfold two_pt_ray, left, unfold same_side_pt, split,
      intro hadf, apply hdfac,
      exact ⟨a, pt_left_in_line a c, hadf⟩,
      exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hf.1⟩,
    specialize hadab f hfad hfa,
    have hedab := same_side_line_trans (line_in_lines hab) hbeab (same_side_line_symm hadab),
    have hecab := same_side_line_trans (line_in_lines hab) hedab hdcab,
    apply hecab, use a, split,
    exact pt_left_in_line a b,
    unfold two_pt_segment, simp, right, right, exact (is_between_symm c a e).mp hcae,
    cases h₁.1 with h₁ h₁,
    exact absurd h₁ h₂,
  rcases h₁ with ⟨f, hfad, hfcb⟩,
  have : b ∉ (a-ₗc), from λ hf, hbac ⟨(a-ₗc), line_in_lines hac, hf,
    pt_left_in_line a c, pt_right_in_line a c⟩,
  have hcbac : ∀ x ∈ (c-ₛb).inside, x ≠ c → same_side_line (a-ₗc) b x,
    from t_shape_segment hac this,
  have hfc : f ≠ c,
    intro hfc, rw hfc at hfad, have := pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac)
      hac ⟨pt_left_in_line a d, hfad⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at this,
    exact (same_side_line_not_in hd.2).2 this,
  specialize hcbac f hfcb hfc,
  have hdfac := same_side_line_trans (line_in_lines hac) hdbac hcbac,
  use f, split,
  unfold two_pt_ray same_side_pt, simp, right, split,
  intro hf, apply hdfac, use a, exact ⟨pt_left_in_line a c, hf⟩,
  exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hfad⟩,
  rw segment_symm, exact hfcb
end

lemma ray_inside_angle {a o b p q : pts} :
inside_angle p (∠ a o b) → same_side_pt o p q → inside_angle q (∠ a o b) :=
begin
  intros hp hopq,
  have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  rw inside_three_pt_angle at hp, rw inside_three_pt_angle,
  have hoa := (noncollinear_neq haob).1.symm,
  have hob := (noncollinear_neq haob).2.2,
  have hoq := (same_side_pt_neq hopq).2.symm,
  split,
  apply same_side_line_trans (line_in_lines hoa) hp.1,
  rw line_symm, refine t_shape_ray hoa.symm _ _ _ _,
  rw line_symm, exact (same_side_line_not_in hp.1).2,
  left, exact hopq, exact hoq.symm,
  apply same_side_line_trans (line_in_lines hob) hp.2,
  rw line_symm, refine t_shape_ray hob.symm _ _ _ _,
  rw line_symm, exact (same_side_line_not_in hp.2).2,
  left, exact hopq, exact hoq.symm
end

lemma inside_angle_diff_side_line {a o b p : pts} :
inside_angle p (∠ a o b) → diff_side_line (o-ₗp) a b :=
begin
  intro hp,
  have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  have hop : o ≠ p,
    intro hop, rw [inside_three_pt_angle, hop] at hp,
    exact (same_side_line_not_in hp.1).2 (pt_left_in_line p a),
  cases crossbar hp with q hq, use q,
  exact ⟨(ray_in_line o p) hq.1, hq.2⟩,
  rw inside_three_pt_angle at hp,
  have hoa := (noncollinear_neq haob).1.symm,
  have hob := (noncollinear_neq haob).2.2,
  split, intro ha,
  exact (same_side_line_not_in hp.1).2(collinear_in23 ⟨(o-ₗp),
    line_in_lines hop, pt_right_in_line o p, pt_left_in_line o p, ha⟩ hoa),
  intro hb,
  exact (same_side_line_not_in hp.2).2 (collinear_in23 ⟨(o-ₗp),
    line_in_lines hop, pt_right_in_line o p, pt_left_in_line o p, hb⟩ hob)
end

/--Two nontrivial angles are supplementary if their shares one common ray and the other two
rays lie on the same line in opposite sides. -/
def supplementary (α β : angle) : Prop :=
(∃ a b c d : pts, α = ∠ b a c ∧ β = ∠ b a d ∧ is_between c a d)
∧ angle_nontrivial α ∧ angle_nontrivial β

lemma supplementary_symm {α β : angle} : supplementary α β ↔ supplementary β α :=
begin
  split; rintros ⟨⟨a, b, c, d, hbac, hbad, hcad⟩, h₁, h₂⟩;
  exact ⟨⟨a, b, d, c, hbad, hbac, by {rw is_between_symm, exact hcad}⟩, h₂, h₁⟩,
end

lemma three_pt_angle_supplementary {a b c d : pts} :
supplementary (∠b a c) (∠b a d) ↔ is_between c a d ∧ noncollinear b a c ∧ noncollinear b a d :=
begin
  split,
  rintros ⟨⟨a', b', c', d', hbac, hbad, hc'a'd'⟩, h₁, h₂⟩,
  have h₁' : angle_nontrivial (∠ b' a' c'), rw ←hbac, exact h₁,
  have h₂' : angle_nontrivial (∠ b' a' d'), rw ←hbad, exact h₂,
  rw angle_nontrivial_iff_noncollinear at h₁ h₁' h₂ h₂',
  have haa' : a = a', from ((three_pt_angle_eq_iff h₁).1 hbac).1,
  rw ←haa' at hc'a'd',
  cases ((three_pt_angle_eq_iff h₁).1 hbac).2 with H₁ H₁;
  cases ((three_pt_angle_eq_iff h₂).1 hbad).2 with H₂ H₂,
  split,
  rw [is_between_diff_side_pt, ←not_same_side_pt], intro hacd,
  rw [is_between_diff_side_pt, ←not_same_side_pt] at hc'a'd',
  exact hc'a'd' (same_side_pt_trans (same_side_pt_trans (same_side_pt_symm H₁.2) hacd) H₂.2),
  exact diff_side_pt_collinear hc'a'd', exact hc'a'd'.2.1, exact hc'a'd'.2.2,
  rcases H₁.2.2 with ⟨l, hl, hal, hcl, hc'l⟩,
  rcases (is_between_collinear hc'a'd') with ⟨m, hm, hc'm, ham, hd'm⟩,
  rcases H₂.2.2 with ⟨n, hn, han, hdn, hd'n⟩,
  rw ←haa' at h₁' h₂',
  rw two_pt_one_line hm hl (noncollinear_neq h₁').2.2 ⟨ham, hc'm⟩ ⟨hal, hc'l⟩ at hd'm,
  rw two_pt_one_line hn hl (noncollinear_neq h₂').2.2.symm ⟨hd'n, han⟩ ⟨hd'm, hal⟩ at hdn,
  exact ⟨l, hl, hal, hcl, hdn⟩,
  exact (noncollinear_neq h₁).2.2.symm, exact (noncollinear_neq h₂).2.2.symm,
  exact ⟨h₁, h₂⟩,
  rcases (same_side_pt_trans H₁.1 (same_side_pt_symm H₂.2)).2 with ⟨l, hl, hal, hbl, hdl⟩,
  exfalso, apply h₂, exact ⟨l, hl, hbl, hal, hdl⟩,
  rcases (same_side_pt_trans H₂.1 (same_side_pt_symm H₁.2)).2 with ⟨l, hl, hal, hbl, hcl⟩,
  exfalso, apply h₁, exact ⟨l, hl, hbl, hal, hcl⟩,
  have hf := (same_side_pt_trans (same_side_pt_symm H₁.1) H₂.1),
  rw [is_between_diff_side_pt, ←not_same_side_pt] at hc'a'd', exact absurd hf hc'a'd',
  exact diff_side_pt_collinear hc'a'd', exact hc'a'd'.2.1, exact hc'a'd'.2.2,
  rintros ⟨hcad, hbac, hbad⟩,
  use [a, b, c, d], simp, exact hcad,
  rw [angle_nontrivial_iff_noncollinear, angle_nontrivial_iff_noncollinear], exact ⟨hbac, hbad⟩
end

lemma inside_angle_trans {a b c d e : pts} :
inside_angle d (∠ b a c) → inside_angle e (∠ b a d) → inside_angle e (∠ b a c) :=
begin
  intros hd he,
  have hbac := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hd),
  have hbad := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial he),
  rw inside_three_pt_angle at *,
  have hac := (noncollinear_neq hbac).2.2,
  have hab := (noncollinear_neq hbac).1.symm,
  have hbc := (noncollinear_neq hbac).2.1,
  have hbd := (noncollinear_neq hbad).2.1,
  have had := (noncollinear_neq hbad).2.2,
  have hae : a ≠ e,
    intro hae, rw ←hae at he,
    exact (same_side_line_not_in he.1).2 (pt_left_in_line a b),
  have hade : noncollinear a d e,
    rintros ⟨l, hl, hal, hdl, hel⟩,
    rw two_pt_one_line hl (line_in_lines had) had ⟨hal, hdl⟩
      ⟨pt_left_in_line a d, pt_right_in_line a d⟩ at hel,
    exact (same_side_line_not_in he.2).2 hel,
  split, exact (same_side_line_trans (line_in_lines hab) hd.1 he.1),
  cases crossbar (inside_three_pt_angle.2 hd) with d' hd',
  have : inside_angle e (∠ b a d'),
    have : same_side_pt a d d',
      unfold two_pt_ray at hd',
      cases hd'.1, exact h,
      simp at h, rw h at hd',
      exfalso, apply hbac,
      exact ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c,
        (segment_in_line b c) hd'.2, pt_right_in_line b c⟩,
    rw [←angle_eq_same_side b this, inside_three_pt_angle], exact he,
  have hbd' : b ≠ d',
    intro hbd', rw ←hbd' at hd',
    exact hbad ⟨(a-ₗd), line_in_lines had, (ray_in_line a d) hd'.1,
      pt_left_in_line a d, pt_right_in_line a d⟩,
  cases crossbar this with e' he',
  have had' : a ≠ d',
    intro hf, rw ←hf at hd',
    exact hbac ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c,
      (segment_in_line b c) hd'.2, pt_right_in_line b c⟩,
  have he'a : e' ≠ a,
    intro he'a, rw he'a at he'a, rw he'a at he',
    have : a ∈ (b-ₗc),
      rw two_pt_one_line (line_in_lines hbc) (line_in_lines hbd') hbd',
      exact (segment_in_line b d') he'.2,
      exact ⟨pt_left_in_line b c, (segment_in_line b c) hd'.2⟩,
      exact ⟨pt_left_in_line b d', pt_right_in_line b d'⟩,
    exfalso, apply hbac,
    exact ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, this, pt_right_in_line b c⟩,
  have hdd' : same_side_line (a-ₗc) d d',
    rw line_symm, refine t_shape_ray _ _ _ _ _,
    exact hac.symm,
    rw line_symm, exact (same_side_line_not_in hd.2).2,
    exact hd'.1, exact had'.symm,
  have hbd'c : is_between b d' c,
    cases hd'.2, exact h,
    cases h, exact absurd h hbd'.symm,
    simp at h, rw h at hd', rw h at hdd',
    exact absurd (pt_right_in_line a c) (same_side_line_not_in hdd').2,
  have hbe'd' : is_between b e' d',
    cases he'.2, exact h,
    cases h, rw h at he',
    rw two_pt_one_line (line_in_lines hab) (line_in_lines hae) hab ⟨pt_left_in_line a b,
      pt_right_in_line a b⟩ ⟨pt_left_in_line a e, (ray_in_line a e) he'.1⟩ at he,
    exact absurd (pt_right_in_line a e) (same_side_line_not_in he.1).2,
    simp at h, rw h at he',
    have := pt_right_in_line a e,
    rw two_pt_one_line (line_in_lines hae) (line_in_lines had) had' at this,
    exfalso, apply hade,
    exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, this⟩,
    exact ⟨pt_left_in_line a e, (ray_in_line a e) he'.1⟩,
    exact ⟨pt_left_in_line a d, (ray_in_line a d) hd'.1⟩,
  have hee' : same_side_line (a-ₗc) e e',
    rw line_symm, apply same_side_line_symm,
    refine t_shape_ray _ _ _ _ _,
    exact hac.symm,
    rw line_symm, intro hf,
    have : e' ∈ (b-ₗc),
      rw two_pt_one_line (line_in_lines hbc) (line_in_lines hbd') hbd' ⟨pt_left_in_line b c,
        (segment_in_line b c) hd'.2⟩ ⟨pt_left_in_line b d', pt_right_in_line b d'⟩,
      exact (segment_in_line b d') he'.2,
    have hce' : c ≠ e',
      intro hce', rw ←hce' at he',
      cases he'.2 with h h, cases hd'.2 with h' h',
      exact (collinear_between (is_between_collinear h)).2.1 ⟨h, h'⟩,
      cases h' with h' h', rw h' at h, exact (is_between_not_eq h).2.1 rfl,
      simp at h', rw h' at h, exact (is_between_not_eq h).2.2 rfl,
      cases h with h h, exact hbc h.symm,
      simp at h, rw h at hdd',
      exact (same_side_line_not_in hdd').2 (pt_right_in_line a d'),
    have hb := pt_left_in_line b c,
    rw two_pt_one_line (line_in_lines hbc) (line_in_lines hac) hce'
      ⟨pt_right_in_line b c, this⟩ ⟨pt_right_in_line a c, hf⟩ at hb,
    exact hbac ⟨(a-ₗc), line_in_lines hac, hb, pt_left_in_line a c, pt_right_in_line a c⟩,
    cases he'.1 with he' hf,
    left, exact same_side_pt_symm he',
    exact absurd hf he'a,
    intro hea, rw [hea, ray_singleton] at he', exact he'a he'.1,
  suffices : same_side_line (a-ₗc) d' e',
    from same_side_line_trans (line_in_lines hac) (same_side_line_trans (line_in_lines hac)
      (same_side_line_trans (line_in_lines hac) hd.2 hdd') this)
      (same_side_line_symm hee'),
  refine t_shape_ray hac _ _ _ _,
  exact (same_side_line_not_in hdd').2,
  rw is_between_symm at hbd'c hbe'd',
  left, simp, exact (is_between_same_side_pt.1 (is_between_trans' hbd'c hbe'd').1).1,
  intro hf, rw hf at hee', exact (same_side_line_not_in hee').2 (pt_right_in_line a c)
end

lemma inside_angle_trans' {a o b c d : pts} (hboc : is_between b o c) :
inside_angle d (∠ a o b) → inside_angle a (∠ d o c) :=
begin
  intro hd, have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hd),
  rw inside_three_pt_angle,
  have hod : o ≠ d,
    intro hod, rw [hod, inside_three_pt_angle] at hd,
    exact (same_side_line_not_in hd.1).2 (pt_left_in_line d a),
  have hoc := (is_between_not_eq hboc).2.2,
  have hob := (is_between_not_eq hboc).1.symm,
  have := two_pt_one_line (line_in_lines hoc) (line_in_lines hob) hob ⟨pt_left_in_line o c,
    collinear_in23 (is_between_collinear hboc) hoc⟩ ⟨pt_left_in_line o b, pt_right_in_line o b⟩,
  rw inside_three_pt_angle at hd,
  have hoa := (noncollinear_neq haob).1.symm,
  split,
  have h₁ : diff_side_line (o-ₗd) c b,
    rw is_between_diff_side_pt at hboc, apply diff_side_line_symm,
    apply (diff_side_pt_line hboc).2.2.2 (line_in_lines hod),
    split, exact pt_left_in_line o d,
    split, intro hf, apply (same_side_line_not_in hd.2).2,
    apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d,
      hf, pt_right_in_line o d⟩,
    exact hob,
    intro hf, apply (same_side_line_not_in hd.2).2,
    rw ←this, apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod,
      pt_left_in_line o d, hf, pt_right_in_line o d⟩,
    exact hoc,
  have h₂ : diff_side_line (o-ₗd) b a,
    cases crossbar (inside_three_pt_angle.2 hd) with x hx,
    use x, rw segment_symm, exact ⟨(ray_in_line o d) hx.1, hx.2⟩,
    split, intro hf, apply (same_side_line_not_in hd.2).2,
    apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d,
      hf, pt_right_in_line o d⟩,
    exact hob, intro hf, apply (same_side_line_not_in hd.1).2,
    apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d,
      hf, pt_right_in_line o d⟩,
    exact hoa,
  exact diff_side_line_cancel (line_in_lines hod) h₁ h₂,
  rw this,
  exact same_side_line_symm hd.2
end
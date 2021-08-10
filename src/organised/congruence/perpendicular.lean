import organised.congruence.angle_lt

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

/--An angle is a right angle if it is congruent to its supplementary angle. -/
def is_right_angle (α : angle) : Prop :=
angle_nontrivial α ∧ ∀ β : angle, supplementary α β → (α ≅ₐ β)

lemma supplementary_exist {α : angle} (haob : angle_nontrivial α) :
∃ β : angle, supplementary α β :=
begin
  rcases angle_three_pt α with ⟨a, b, h⟩,
  rw h, rw [h, angle_nontrivial_iff_noncollinear] at haob, set o := α.vertex,
  have hob := (noncollinear_neq haob).2.2,
  cases is_between_extend hob.symm with c hboc,
  have hoc := (is_between_not_eq hboc).2.2,
  use (∠ a o c), rw three_pt_angle_supplementary,
  split, exact hboc,
  split, exact haob,
  exact noncollinear132 (collinear_noncollinear (collinear12 (is_between_collinear hboc))
    (noncollinear123 haob) hoc),
end

lemma right_angle_congr {α β : angle} :
(α ≅ₐ β) → is_right_angle α → angle_nontrivial β → is_right_angle β :=
begin
  intros hαβ hα hβ,
  split, exact hβ,
  intros β' hββ',
  cases supplementary_exist hα.1 with α' hαα',
  exact angle_congr_trans (angle_congr_trans (angle_congr_symm hαβ) (hα.2 α' hαα'))
    (supplementary_congr hαα' hββ' hαβ),
end

lemma three_pt_angle_is_right_angle {a o b c : pts} (hboc : is_between b o c) :
is_right_angle (∠ a o b) ↔ ((∠ a o b) ≅ₐ (∠ a o c)) ∧ angle_nontrivial (∠ a o b) :=
begin
  unfold is_right_angle,
  split; intro h, split,
  apply h.2, rw three_pt_angle_supplementary,
  have haob := angle_nontrivial_iff_noncollinear.1 h.1,
  split, exact hboc, split, exact haob,
  exact noncollinear132 (collinear_noncollinear (collinear12 (is_between_collinear hboc))
    (noncollinear12 (noncollinear13 haob)) (is_between_not_eq hboc).2.2),
  exact h.1,
  split, exact h.2,
  intros β hβ, rcases hβ.1 with ⟨o', a', b', c', haoba'ob', ha'oc', hb'oc'⟩,
  have haob := angle_nontrivial_iff_noncollinear.1 h.2,
  have haoc := noncollinear132 (collinear_noncollinear (collinear12 (is_between_collinear hboc))
    (noncollinear12 (noncollinear13 haob)) (is_between_not_eq hboc).2.2),
  have hoo' := ((three_pt_angle_eq_iff haob).1 haoba'ob').1, rw ←hoo' at *,
  cases ((three_pt_angle_eq_iff haob).1 haoba'ob').2 with H H,
  rw ha'oc',
  have : (∠ a o c) = (∠ a' o c'),
    rw three_pt_angle_eq_iff haoc, simp, left,
    split, exact H.1,
    apply diff_side_pt_cancel (is_between_diff_side_pt.1 hboc),
    rw is_between_diff_side_pt at hb'oc',
    exact diff_side_pt_symm (diff_side_same_side_pt hb'oc' (same_side_pt_symm H.2)),
  rw ←this, exact h.1,
  rw ha'oc', apply angle_congr_trans h.1, rw angle_symm,
  refine vertical_angle_congr _ _ _,
  exact noncollinear13 haoc,
  rw is_between_diff_side_pt, rw is_between_diff_side_pt at hboc,
  exact diff_side_same_side_pt hboc H.2,
  rw is_between_diff_side_pt, rw is_between_diff_side_pt at hb'oc',
  exact diff_side_pt_symm (diff_side_same_side_pt hb'oc' (same_side_pt_symm H.1))
end

lemma all_right_angle_congr {α β : angle}
(hα : is_right_angle α) (hβ : is_right_angle β) : α ≅ₐ β :=
begin
  have wlog : ∀ α β : angle, is_right_angle α → is_right_angle β → (α <ₐ β) → false,
    intros x y hx hy hxy,
    rcases angle_three_pt y with ⟨a, b, haob⟩,
    set o := y.vertex, rw haob at hxy,
    rw haob at hy,
    have hbo := (noncollinear_neq (angle_nontrivial_iff_noncollinear.1 hy.1)).2.2.symm,
    rw [angle_symm, three_pt_angle_lt] at hxy,
    rcases hxy with ⟨p, hpin, hp⟩,
    have hboa := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hpin),
    rw inside_three_pt_angle at hpin,
    cases is_between_extend hbo with c hboc,
    have hco := (is_between_not_eq hboc).2.2.symm,
    rw three_pt_angle_is_right_angle hboc at hy,
    have h₁ : supplementary (∠ p o b) (∠ p o c),
      rw three_pt_angle_supplementary,
      split, exact hboc,
      have : noncollinear p o b,
        intro hpob,
        exact (same_side_line_not_in hpin.1).2 (collinear_in23 hpob hbo.symm),
      split, exact this,
      exact noncollinear132 (collinear_noncollinear (collinear12 (is_between_collinear hboc))
        (noncollinear123 this) hco.symm),
    have h₂ : supplementary (∠ a o b) (∠ a o c),
      rw three_pt_angle_supplementary,
      split, exact hboc,
      split, exact noncollinear13 hboa,
      exact noncollinear132 ((collinear_noncollinear (collinear12 (is_between_collinear hboc))
        (noncollinear12 hboa)) hco.symm),
    have hf₁ : ((∠ p o c) <ₐ (∠ a o c)),
      have hbop : noncollinear b o p,
        intro hbop, rw line_symm at hpin,
        exact (same_side_line_not_in hpin.1).2 (collinear_in12 hbop hbo),
      replace hbop := right_angle_congr (angle_congr_symm hp) hx
        (angle_nontrivial_iff_noncollinear.2 hbop),
      rw angle_symm at hbop,
      have : ((∠ p o b) <ₐ (∠ a o b)),
        rw [angle_symm, angle_symm a o b, three_pt_angle_lt],
        exact ⟨p, inside_three_pt_angle.2 hpin, angle_congr_refl _⟩,
      replace h₁ := hbop.2 _ h₁,
      replace h₂ := hy.1,
      apply (angle_lt_congr h₁).1, apply (angle_lt_congr h₂).2,
      rw angle_nontrivial_iff_noncollinear,
      exact noncollinear132 (collinear_noncollinear (collinear12 (is_between_collinear hboc))
        (noncollinear12 hboa) hco.symm),
      exact this,
    have hf₂ : ((∠ a o c) <ₐ (∠ p o c)),
      rw [angle_symm, angle_symm p o c, three_pt_angle_lt],
      use a, split,
      rw angle_symm, exact inside_angle_trans' hboc (by {rw angle_symm,
        exact inside_three_pt_angle.2 hpin}),
      exact angle_congr_refl _,
    exact (angle_tri h₁.2.2 h₂.2.2).2.2.1 ⟨hf₁, hf₂⟩,
  rcases (angle_tri hα.1 hβ.1).1 with h | h | h,
  exfalso, exact wlog α β hα hβ h,
  exact h,
  exfalso, exact wlog β α hβ hα h
end

/--Two lines are perpendicular if they form a right angle. -/
def perpendicular (l₁ l₂ : set pts) : Prop :=
(∃ (a b c : pts), a ∈ l₁ ∧ b ∈ l₂ ∧ c ∈ l₁ ∩ l₂ ∧ is_right_angle (∠ a c b))
∧ l₁ ∈ lines ∧ l₂ ∈ lines

lemma perpendicular_symm (l₁ l₂ : set pts) :
perpendicular l₁ l₂ → perpendicular l₂ l₁ :=
begin
  rintros ⟨⟨a, b, c, hal₁, hbl₂, hcl, hr⟩, hl⟩,
  rw angle_symm at hr, rw set.inter_comm at hcl, rw and_comm at hl,
  use [b, a, c],
  exact ⟨hbl₂, hal₁, hcl, hr⟩, exact hl
end

localized "notation a `⊥` b := perpendicular a b" in perp_notation
-- type `open_locale perp_notation` to get ⊥ meaning perpendicular not bot.
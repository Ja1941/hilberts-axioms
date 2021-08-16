import main
import data.zmod.basic
import data.real.basic
import tactic.interval_cases

open incidence_geometry incidence_order_geometry hilbert_plane

-- local attribute [-class] incidence_geometry -- cannot remove attribute [class]

lemma zmod2_cases (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
  cases a with a ha, norm_num at ha,
  interval_cases a,
  left, refl, right, refl
end

lemma not_zero_iff_one (a : zmod 2) : a ≠ 0 ↔ a = 1 :=
begin
  split; intro ha,
  cases zmod2_cases a,
  exact absurd h ha, exact h,
  rw ha, simp
end 

lemma not_one_iff_zero (a : zmod 2) : a ≠ 1 ↔ a = 0 :=
by { split; contrapose!; rw not_zero_iff_one; simp }

lemma self_mul_self_add_one (x : zmod 2) : x * (x + 1) = 0 :=
begin
  cases zmod2_cases x;
  rw h; solve_by_elim
end

lemma self_add_one_mul_self (x : zmod 2) : (x + 1) * x = 0 :=
by { rw mul_comm, exact self_mul_self_add_one x }

lemma prod_zero_iff {a b : zmod 2} : a * b = 0 → a = 0 ∧ b = 0 :=
begin
  intro hab,
  cases zmod2_cases a with ha ha,
  cases 
end

lemma sum_zero_iff {a b : zmod 2} :
a + b = 0 → (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) :=
begin
  intro hab,
  cases zmod2_cases a with ha ha;
  rw ha at hab,
  simp at hab, left, exact ⟨ha, hab⟩,
  cases zmod2_cases b with hb hb;
  rw hb at hab,
  simp at hab, exfalso, exact hab,
  right, exact ⟨ha, hb⟩
end

lemma sum_zero_iff' {a b : zmod 2} :
a + b = 0 → a = b :=
by { intro hab, cases sum_zero_iff hab with h; rw [h.1, h.2] }

lemma case001 (a b : zmod 2) (hab : a ≠ 0 ∨ b ≠ 0) :
∀ {x₁ x₂ y₁ y₂ : zmod 2}, x₁ ≠ 0 ∨ y₁ ≠ 0 → x₂ ≠ 0 ∨ y₂ ≠ 0 →
a * x₁ + b * y₁ = 0 → a * x₂ + b * y₂ = 0 → x₁ = x₂ ∧ y₁ = y₂ :=
begin
  have : ∀ {a b x₁ x₂ y₁ y₂ : zmod 2}, a = 1 → x₁ ≠ 0 ∨ y₁ ≠ 0 → x₂ ≠ 0 ∨ y₂ ≠ 0 →
    a * x₁ + b * y₁ = 0 → a * x₂ + b * y₂ = 0 → x₁ = x₂ ∧ y₁ = y₂,
    intros a b x₁ x₂ y₁ y₂ ha h0₁ h0₂ h₁ h₂,
    rw ←not_and_distrib at h0₁ h0₂, push_neg at h0₁ h0₂,
    rw not_zero_iff_one at h0₁ h0₂,
    rw ha at h₁ h₂; simp at h₁ h₂,
    cases zmod2_cases b with hb hb,
    rw hb at h₁ h₂, simp at h₁ h₂,
    rw [h₁, h0₁ h₁, h₂, h0₂ h₂], simp,
    rw hb at h₁ h₂, simp at h₁ h₂,
    cases sum_zero_iff h₁ with h₁ h₁,
    specialize h0₁ h₁.1, rw h₁.2 at h0₁,
    simp at h0₁, exfalso, exact h0₁,
    cases sum_zero_iff h₂ with h₂ h₂,
    specialize h0₂ h₂.1, rw h₂.2 at h0₂,
    simp at h0₂, exfalso, exact h0₂,
    rw [h₁.1, h₁.2, h₂.1, h₂.2], simp,
  intros x₁ x₂ y₁ y₂ h0₁ h0₂ h₁ h₂,
  rw [not_zero_iff_one, not_zero_iff_one] at hab,
  cases hab with ha hb,
  exact this ha h0₁ h0₂ h₁ h₂,
  rw add_comm at h₁ h₂, rw or_comm at h0₁ h0₂,
  rw and_comm, exact this hb h0₁ h0₂ h₁ h₂
end

lemma case110 (a b c : zmod 2) (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (habc' : ¬(a = 1 ∧ b = 1 ∧ c = 0)) :
∀ {x₁ x₂ y₁ y₂ z₁ z₂ : zmod 2}, (x₁ ≠ 0 ∨ y₁ ≠ 0 ∨ z₁ ≠ 0) → (x₂ ≠ 0 ∨ y₂ ≠ 0 ∨ z₂ ≠ 0)
→ x₁ + y₁ = 0 → a * x₁ + b * y₁ + c * z₁ = 0
→ x₂ + y₂ = 0 → a * x₂ + b * y₂ + c * z₂ = 0 → x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂ :=
begin
  have : ∀ {a b c x₁ x₂ y₁ y₂ z₁ z₂ : zmod 2}, a = 1 → ¬(a = 1 ∧ b = 1 ∧ c = 0)
    → (x₁ ≠ 0 ∨ y₁ ≠ 0 ∨ z₁ ≠ 0) → (x₂ ≠ 0 ∨ y₂ ≠ 0 ∨ z₂ ≠ 0)
    → x₁ + y₁ = 0 → a * x₁ + b * y₁ + c * z₁ = 0
    → x₂ + y₂ = 0 → a * x₂ + b * y₂ + c * z₂ = 0 → x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂,
    intros a b c x₁ x₂ y₁ y₂ z₁ z₂ ha habc' hxyz₁ hxyz₂ h₁ h₁' h₂ h₂',
    rw ha at h₁' h₂', simp at h₁' h₂',
    cases zmod2_cases b with hb hb;
    rw hb at h₁' h₂'; simp at h₁' h₂';
    cases zmod2_cases c with hc hc;
    rw hc at h₁' h₂'; simp at h₁' h₂',
    rw h₁' at h₁, rw h₂' at h₂, simp at h₁ h₂,
    rw [←not_and_distrib, ←not_and_distrib] at hxyz₁ hxyz₂,
    push_neg at hxyz₁ hxyz₂, rw not_zero_iff_one at hxyz₁ hxyz₂,
    rw [h₁, h₂, h₁', h₂', hxyz₁ h₁' h₁, hxyz₂ h₂' h₂], simp,
    rw [←not_and_distrib, ←not_and_distrib] at hxyz₁ hxyz₂,
    rw [←sum_zero_iff' h₁, ←sum_zero_iff' h₁'] at hxyz₁,
    rw [←sum_zero_iff' h₂, ←sum_zero_iff' h₂'] at hxyz₂,
    simp at hxyz₁ hxyz₂,
    rw [←sum_zero_iff' h₁, ←sum_zero_iff' h₁', ←sum_zero_iff' h₂, ←sum_zero_iff' h₂'],
    rw [(not_zero_iff_one x₁).1 hxyz₁, (not_zero_iff_one x₂).1 hxyz₂], simp,
    exfalso, exact habc' ⟨ha, hb, hc⟩,
    rw [h₁, zero_add] at h₁', rw [h₂, zero_add] at h₂',
    rw [←sum_zero_iff' h₁, ←sum_zero_iff' h₂, h₁', h₂'],
    rw [←not_and_distrib, ←not_and_distrib] at hxyz₁ hxyz₂,
    push_neg at hxyz₁ hxyz₂,
    rw ←sum_zero_iff' h₁ at hxyz₁, rw ←sum_zero_iff' h₂ at hxyz₂,
    cases zmod2_cases x₁ with hx₁ hx₁,
    exact absurd h₁' (hxyz₁ hx₁ hx₁),
    cases zmod2_cases x₂ with hx₂ hx₂,
    exact absurd h₂' (hxyz₂ hx₂ hx₂),
    rw [hx₁, hx₂], simp,
  rw [not_zero_iff_one, not_zero_iff_one, not_zero_iff_one] at habc,
  intros x₁ x₂ y₁ y₂ z₁ z₂ hxyz₁ hxyz₂ h₁ h₁' h₂ h₂',
  rcases habc with ha | hb | hc,
  exact this ha habc' hxyz₁ hxyz₂ h₁ h₁' h₂ h₂',
  rw [←and_assoc, and_comm _ (b = 1), and_assoc] at habc',
  rw add_comm (a * x₁) _ at h₁', rw add_comm (a * x₂) _ at h₂',
  rw [←and_assoc, and_comm (x₁ = x₂) _, and_assoc],
  rw add_comm at h₁ h₂,
  rw [←or_assoc, or_comm (x₁ ≠ 0) _, or_assoc] at hxyz₁,
  rw [←or_assoc, or_comm (x₂ ≠ 0) _, or_assoc] at hxyz₂,
  exact this hb habc' hxyz₁ hxyz₂ h₁ h₁' h₂ h₂',
  cases zmod2_cases a with ha ha;
  cases zmod2_cases b with hb hb;
  rw [ha, hb, hc] at h₁' h₂'; simp at h₁' h₂',
  rw ←sum_zero_iff' h₁ at hxyz₁, rw ←sum_zero_iff' h₂ at hxyz₂,
  simp at hxyz₁ hxyz₂,
  rw [or_comm, ←not_and_distrib] at hxyz₁ hxyz₂, push_neg at hxyz₁ hxyz₂,
  rw not_zero_iff_one at hxyz₁ hxyz₂,
  rw [←sum_zero_iff' h₁, ←sum_zero_iff' h₂, h₁', h₂', hxyz₁ h₁', hxyz₂ h₂'], simp,
  rw [←sum_zero_iff' h₁', ←sum_zero_iff' h₁, not_zero_iff_one] at hxyz₁,
  rw [←sum_zero_iff' h₂', ←sum_zero_iff' h₂, not_zero_iff_one] at hxyz₂,
  simp at hxyz₁ hxyz₂,
  rw [←sum_zero_iff' h₁', ←sum_zero_iff' h₁, ←sum_zero_iff' h₂', ←sum_zero_iff' h₂, hxyz₁, hxyz₂], simp,
  rw [←sum_zero_iff' h₁', ←sum_zero_iff' h₁, not_zero_iff_one] at hxyz₁,
  rw [←sum_zero_iff' h₂', ←sum_zero_iff' h₂, not_zero_iff_one] at hxyz₂,
  simp at hxyz₁ hxyz₂,
  rw [←sum_zero_iff' h₁', ←sum_zero_iff' h₁, ←sum_zero_iff' h₂', ←sum_zero_iff' h₂, hxyz₁, hxyz₂], simp,
  rw [h₁, zero_add] at h₁', rw [h₂, zero_add] at h₂',
  rw [←sum_zero_iff' h₁, ←sum_zero_iff' h₂, h₁', h₂'],
  rw [←not_and_distrib, ←not_and_distrib] at hxyz₁ hxyz₂,
  push_neg at hxyz₁ hxyz₂,
  rw ←sum_zero_iff' h₁ at hxyz₁, rw ←sum_zero_iff' h₂ at hxyz₂,
  cases zmod2_cases x₁ with hx₁ hx₁,
  exact absurd h₁' (hxyz₁ hx₁ hx₁),
  cases zmod2_cases x₂ with hx₂ hx₂,
  exact absurd h₂' (hxyz₂ hx₂ hx₂),
  rw [hx₁, hx₂], simp
end

example (a : nat) : a ≠ 0 ↔ 0 ≠ a := ne_comm

example (p q r : Prop) : p ∧ q ∧ r ↔ p ∧ r ∧ q :=
begin
  rw and_comm q r,
end

-- Fano plane
example : incidence_geometry :=
{ pts := {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)},
  lines := { S : set ({x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}) | 
    ∃ y : {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}, S = { x | x.1.1 * y.1.1 + x.1.2.1 * y.1.2.1 + x.1.2.2 * y.1.2.2 = 0}},
  I1 :=
  begin
    intros a b hab,
    replace hab : ¬(a.1.1 = b.1.1 ∧ a.1.2.1 = b.1.2.1 ∧ a.1.2.2 = b.1.2.2),
      intro hf, apply hab, simp at hf,
      ext, rw hf.1, rw hf.2.1, rw hf.2.2,
    set y : {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)} :=
      ⟨((a.1.1 + 1)*(b.1.1 + 1), (a.1.2.1 + 1)*(b.1.2.1 + 1), (a.1.2.2 + 1)*(b.1.2.2 + 1)), _⟩ with hy,
    set l := {x : {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)} |
      x.1.1 * y.1.1 + x.1.2.1 * y.1.2.1 + x.1.2.2 * y.1.2.2 = 0} with hl,
    use [l, y],
    have hal : a ∈ l,
      rw hl, simp,
      repeat {rw [←mul_assoc, self_mul_self_add_one _, zero_mul]},
      rw [add_zero, add_zero],
    have hbl : b ∈ l,
      rw hl, simp,
      repeat {rw [mul_comm, mul_assoc, self_add_one_mul_self _, mul_zero]},
      rw [add_zero, add_zero],
    split, exact hal, split, exact hbl,
    intros l' hl' hal' hbl',
    cases hl' with y' hl',
    rw hl at hal hbl, rw hl' at hal' hbl',
    rw set.mem_set_of_eq at hal hbl hal' hbl',
    suffices : y.1.1 = y'.1.1 ∧ y.1.2.1 = y'.1.2.1 ∧ y.1.2.2 = y'.1.2.2,
      have : y = y',
        rw [subtype.val_eq_coe, subtype.val_eq_coe] at this, ext,
        rw this.1, rw this.2.1, rw this.2.2,
      rw [hl, hl', this],
    cases zmod2_cases a.1.1 with ha₁ ha₁;
    cases zmod2_cases a.1.2.1 with ha₂ ha₂;
    cases zmod2_cases a.1.2.2 with ha₃ ha₃,
    {exfalso, apply a.2, ext, rw ha₁, rw ha₂, rw ha₃},
    {sorry},
    {sorry},
    {sorry},
    {sorry},
    {sorry},
    {sorry},
    {sorry},
    sorry,
  end,
  I2 := sorry,
  I3 := sorry
}

-- affine plane
def affine_plane (k : Type) [field k] : incidence_geometry :=
{ pts := k × k,
  lines := {S : set (k × k) | ∃ y : k × k, y ≠ (0,0) ∧ S = {x : k × k | x.1 * y.1 + x.2 * y.2 = 0} },
  I1 := sorry,
  I2 := sorry,
  I3 := sorry
} 

def r_squared : incidence_order_geometry :=
{ is_between := λ p q r, p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ ∃ L : set (@affine_plane ℝ _).pts, L ∈ (@affine_plane ℝ _).lines ∧
  sorry, -- can't be bothered :-(
  B1 := sorry,
  B2 := sorry,
  B3 := sorry,
  B4 := sorry,
  ..affine_plane ℝ}

example : hilbert_plane :=
{ 
  segment_congr := λ s t, true,
  C1 := begin
    intros p q S,
    use q,
    split,
    sorry,
    split,

  end,
  C2 := _,
  C3 := _,
  angle_congr := _,
  C4 := _,
  C5 := _,
  C6 := _,
  ..r_squared }


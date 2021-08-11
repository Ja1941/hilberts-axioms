import organised.congruence.basic
import data.zmod.basic
import data.real.basic
import group_theory.group_action.defs

-- TODO : prove three axioms.
section Fano_example

/-- The Fano Plane. -/
def pts_Fano : Type := {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}

/--Construction of a Fano plane as an incidence geometry -/
example : incidence_geometry :=
{ pts := pts_Fano,
  lines := { S : set pts_Fano | ∃ y : pts_Fano,
    S = { x | x.1.1 * y.1.1 + x.1.2.1 * y.1.2.1 + x.1.2.2 * y.1.2.2 = 0}},
  I1 := sorry,
  I2 := sorry,
  I3 := sorry
}

end Fano_example

section affine_plane

-- affine plane
def affine_plane (k : Type) [field k] : incidence_geometry :=
{ pts := k × k,
  lines := {S : set (k × k) | ∃ u₀ u : k × k, u ≠ u₀
    ∧ S = {x : k × k | ∃ μ : k, x = u₀ + μ • (u - u₀)} },
  I1 :=
  begin
    intros a b hab,
    use {x : k × k | ∃ μ : k, x = a + μ • (b - a)},
    use [a, b], exact ⟨hab.symm, rfl⟩,
    split, exact ⟨0, by simp⟩,
    split, exact ⟨1, by simp⟩,
    intros l hl hal hbl,
    rcases hl with ⟨u₀, u, huu₀, hl⟩,
    rw hl, ext, simp,
    rw hl at hal hbl,
    cases hal with μ₁ ha, cases hbl with μ₂ hb,
    split; rintros ⟨μ, hx⟩,
    use (μ - μ₁) / (μ₂ - μ₁), rw [ha, hb],
    rw [←sub_sub, ←add_sub, add_comm u₀ (μ₂ • (u - u₀) - u₀), sub_add, sub_self, sub_zero,
      ←sub_smul, smul_smul, div_mul_cancel, add_assoc, ←add_smul, add_comm μ₁ _, sub_add, sub_self,
      sub_zero, hx],
    intro hf, rw sub_eq_zero.1 hf at hb, exact hab (ha.trans hb.symm),
    rw [ha, hb, ←sub_sub, ←add_sub, add_comm u₀ (μ₂ • (u - u₀) - u₀), sub_add, sub_self,
      sub_zero, ←sub_smul, smul_smul, add_assoc, ←add_smul] at hx,
    use μ₁ + μ * (μ₂ - μ₁), rw hx
  end,
  I2 :=
  begin
    rintros l ⟨u₀, u, huu₀, hl⟩,
    rw hl, use [u, u₀],
    exact ⟨huu₀, ⟨1, by simp⟩, ⟨0, by simp⟩⟩
  end,
  I3 :=
  begin
    use [(0, 0), (1, 0), (0, 1)],
    refine ⟨_, _, _, _⟩;
    try {simp only [prod.mk.inj_iff, ne.def, not_false_iff, zero_ne_one, false_and, and_false]},
    rintros ⟨l, hl, hal, hbl, hcl⟩,
    rcases hl with ⟨u₀, u, huu₀, hl⟩,
    rw hl at hal hbl hcl,
    cases hal with μ₁ ha, cases hbl with μ₂ hb,
    have hμ : μ₂ - μ₁ ≠ 0,
      intro hμ, rw sub_eq_zero.1 hμ at hb, rw ←ha at hb, simp at hb, exact hb,
    have h₁ : u - u₀ = (1 / (μ₂ - μ₁), 0),
      calc u - u₀ = (1 / (μ₂ - μ₁)) • (μ₂ • (u - u₀) - μ₁ • (u - u₀))
                  : by rw [←sub_smul, smul_smul, div_mul_cancel 1 hμ, one_smul]
              ... = (1 / (μ₂ - μ₁)) • ((1, 0) - (0, 0)) : by {rw [ha, hb], simp}
              ... = (1 / (μ₂ - μ₁), 0) : by simp,
    have h₂ : u₀ = (-μ₁ / (μ₂ - μ₁), 0),
      calc u₀ =  (0, 0) - μ₁ • (u - u₀) : by rw [ha, add_sub_cancel]
          ... = (-μ₁ / (μ₂ - μ₁), 0)    
              : by {rw h₁, simp, rw [inv_eq_one_div, ←mul_div_assoc, neg_div, mul_one]},
    cases hcl with μ₃ hc,
    rw [h₁, h₂] at hc, simp at hc, exact hc
  end
} 

end affine_plane

namespace r_squared

def is_between (a b c : ℝ × ℝ) : Prop :=
b ≠ c ∧ ∃ k : ℝ, 0 < k ∧ a + k • c = k • b + b

namespace is_between

variables {a b c : ℝ × ℝ}

example : module ℝ (ℝ × ℝ) := infer_instance

lemma one_ne_two (h : is_between a b c) : a ≠ b :=
begin
  rintro rfl,
  rcases h with ⟨hac, k, hkpos, hk⟩,
  rw [add_comm, add_right_cancel_iff] at hk,
  exact hac (smul_left_injective _ hkpos.ne.symm hk.symm),
end

lemma symm (h : is_between a b c) : is_between c b a := ⟨h.one_ne_two.symm,
begin
  rcases h.2 with ⟨k, hkpos, hk⟩,
  use 1 / k,
  split, exact one_div_pos.2 hkpos,
  apply smul_left_injective _ (ne_of_gt hkpos),
  simp, rw [smul_add, smul_smul, mul_inv_cancel (ne_of_gt hkpos), one_smul, smul_add, smul_smul,
    mul_inv_cancel (ne_of_gt hkpos), one_smul, add_comm, hk, add_comm],
  exact prod.no_zero_smul_divisors
end⟩

lemma two_ne_three (h : is_between a b c) : b ≠ c :=
(one_ne_two (symm h)).symm

example {a b c : ℝ} : a + b - c = a - c + b := (sub_add_eq_add_sub a c b).symm

lemma one_ne_three (h : is_between a b c) : a ≠ c :=
begin
  rcases h.2 with ⟨k, hkpos, hk⟩,
  intro hac, rw hac at hk,
  have : (1 + k) • (c - b) = 0,
    rw [add_smul, one_smul, smul_sub, add_sub, sub_add_eq_add_sub, hk], simp,
  simp at this, cases this, linarith,
  exact two_ne_three h (sub_eq_zero.1 this).symm
end

lemma collinear (h : is_between a b c) : c ∈ {x : ℝ × ℝ | ∃ (μ : ℝ), x = a + μ • (b - a)} :=
begin
  rcases h.2 with ⟨k, hkpos, hk⟩,
  use (k + 1) / k,
  rw [div_eq_mul_one_div, mul_comm, ←smul_smul, smul_sub, add_smul, one_smul, ←hk, add_comm _ (k • c),
    ←add_sub, add_smul, one_smul, add_comm _ a, ←sub_sub, sub_self, zero_sub, tactic.ring.add_neg_eq_sub,
    ←smul_sub, smul_smul, one_div_mul_cancel (ne_of_gt hkpos), one_smul, add_comm, sub_add_cancel],
end

lemma extend (hab : a ≠ b) : ∃ d : ℝ × ℝ, is_between a b d :=
begin
  use [-a + b + b], split,
  intro hf, simp at hf, apply hab, exact neg_add_eq_zero.1 hf,
  use 1, simp, ring
end

end is_between

/--Construction of ℝ × ℝ as an incidence order geometry and a Hilbert plane -/
def r_squared : incidence_order_geometry :=
{ is_between := is_between,
  B1 :=
  begin
    rintros a b c (h : r_squared.is_between a b c),
    refine ⟨is_between.symm h, is_between.one_ne_two h, is_between.one_ne_three h,
      is_between.two_ne_three h, _⟩,
    use {x : ℝ × ℝ | ∃ μ : ℝ, x = a + μ • (b - a)},
    use [a, b], exact ⟨(is_between.one_ne_two h).symm, rfl⟩,
    refine ⟨_, _, _⟩,
    exact ⟨0, by simp⟩, exact ⟨1, by simp⟩,
    exact is_between.collinear h
  end,
  B2 := λ a b hab, is_between.extend hab,
  B3 :=
  begin
    split,
    intros a b c l hl habcl hab hac hbc,
    have := collinear_in13,
    sorry,
    sorry,
  end,
  B4 :=
  begin
    sorry,
  end,
  ..affine_plane ℝ}

example : hilbert_plane :=
{ segment_congr := sorry,
  C1 := sorry,
  C2 := sorry,
  C3 := sorry,
  angle_congr := sorry,
  C4 := sorry,
  C5 := sorry,
  C6 := sorry,
  ..r_squared }

end r_squared
import congruence.basic
import data.zmod.basic
import data.real.basic
import data.real.sqrt
import group_theory.group_action.defs
import analysis.normed_space.inner_product
import analysis.normed_space.pi_Lp

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

def between (a b c : ℝ × ℝ) : Prop :=
b ≠ c ∧ ∃ k : ℝ, 0 < k ∧ a + k • c = k • b + b

namespace between

variables {a b c : ℝ × ℝ}

lemma one_ne_two (h : between a b c) : a ≠ b :=
begin
  rintro rfl,
  rcases h with ⟨hac, k, hkpos, hk⟩,
  rw [add_comm, add_right_cancel_iff] at hk,
  exact hac (smul_left_injective _ hkpos.ne.symm hk.symm),
end

lemma symm (h : between a b c) : between c b a := ⟨h.one_ne_two.symm,
begin
  rcases h.2 with ⟨k, hkpos, hk⟩,
  use 1 / k,
  split, exact one_div_pos.2 hkpos,
  apply smul_left_injective _ (ne_of_gt hkpos),
  simp, rw [smul_add, smul_smul, mul_inv_cancel (ne_of_gt hkpos), one_smul, smul_add, smul_smul,
    mul_inv_cancel (ne_of_gt hkpos), one_smul, add_comm, hk, add_comm],
  exact prod.no_zero_smul_divisors
end⟩

lemma two_ne_three (h : between a b c) : b ≠ c :=
(one_ne_two (symm h)).symm

lemma one_ne_three (h : between a b c) : a ≠ c :=
begin
  rcases h.2 with ⟨k, hkpos, hk⟩,
  intro hac, rw hac at hk,
  have : (1 + k) • (c - b) = 0,
    rw [add_smul, one_smul, smul_sub, add_sub, sub_add_eq_add_sub, hk], simp,
  simp at this, cases this, linarith,
  exact two_ne_three h (sub_eq_zero.1 this).symm
end

lemma collinear (h : between a b c) : c ∈ {x : ℝ × ℝ | ∃ (μ : ℝ), x = a + μ • (b - a)} :=
begin
  rcases h.2 with ⟨k, hkpos, hk⟩,
  use (k + 1) / k,
  rw [div_eq_mul_one_div, mul_comm, ←smul_smul, smul_sub, add_smul, one_smul, ←hk, add_comm _ (k • c),
    ←add_sub, add_smul, one_smul, add_comm _ a, ←sub_sub, sub_self, zero_sub, tactic.ring.add_neg_eq_sub,
    ←smul_sub, smul_smul, one_div_mul_cancel (ne_of_gt hkpos), one_smul, add_comm, sub_add_cancel],
end

lemma extend (hab : a ≠ b) : ∃ d : ℝ × ℝ, between a b d :=
begin
  use [-a + b + b], split,
  intro hf, simp at hf, apply hab, exact neg_add_eq_zero.1 hf,
  use 1, simp, ring
end

lemma line_rw (hab : a ≠ b) : ((@line (affine_plane ℝ) a b) : set (affine_plane ℝ).pts)
= {x : ℝ × ℝ | ∃ μ : ℝ, x = a + μ • (b - a)} :=
begin
  apply two_pt_one_line,
  exact @line_in_lines (affine_plane ℝ) a b hab,
  use [a, b], exact ⟨hab.symm, rfl⟩,
  exact hab,
  exact ⟨@pt_left_in_line (affine_plane ℝ) a b, @pt_right_in_line (affine_plane ℝ) a b⟩,
  exact ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩
end

lemma tri {μ : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hc : c = a + μ • (b - a)) :
between a b c ∨ between a c b ∨ between b a c :=
begin
  have hμ0 : μ ≠ 0,
    intro hf, rw hf at hc, simp at hc, exact hac hc.symm,
  cases lt_or_gt_of_ne hμ0 with hμneg hμpos,
  right, right, split, exact hac,
  use -1 / μ, split,
  exact div_pos_of_neg_of_neg (by linarith) hμneg,
  rw [hc, smul_add, smul_smul, div_mul_cancel _ hμ0, neg_one_smul, add_comm, add_assoc,
    neg_sub, sub_add_cancel],
  replace hc : c = (1 - μ) • a + μ • b,
    rw [hc, smul_sub, sub_smul, one_smul, sub_add, ←smul_sub, ←smul_sub,
      ←neg_sub, smul_neg, tactic.ring.add_neg_eq_sub],
  have hμ1 : μ ≠ 1,
    intro hf, rw hf at hc, simp at hc, exact hbc hc.symm,
  cases lt_or_gt_of_ne hμ1 with hμlt1 hμgt1,
  right, left, split, exact hbc.symm,
  use μ / (1 - μ), split,
  exact div_pos hμpos (by linarith),
  symmetry,
  calc (μ / (1 - μ)) • c + c
     = (μ / (1 - μ) + 1) • c : by rw [add_smul, one_smul]
 ... = (1 / (1 - μ)) • c     : by {rw [div_add', one_mul, add_comm, sub_add_cancel], linarith}
 ... = a + (μ / (1 - μ)) • b : by {rw [hc, smul_add, smul_smul, div_mul_cancel, one_smul,
                                    smul_smul, div_mul_eq_mul_div_comm, one_mul], linarith},
  left, split, exact hbc,
  use -1 / (1 - μ), split,
  exact div_pos_of_neg_of_neg (by linarith) (by linarith),
  rw [hc, smul_add, smul_smul, div_mul_cancel, ←add_assoc, neg_one_smul, tactic.ring.add_neg_eq_sub,
    sub_self, zero_add, smul_smul], symmetry,
  calc ((-1) / (1 - μ)) • b + b = ((-1) / (1 - μ) + 1) • b : by rw [add_smul, one_smul]
                            ... = ((-1) / (1 - μ) * μ) • b
  : by {rw [div_add', one_mul, add_sub, neg_add_self, zero_sub, div_mul_eq_mul_div_comm,
    ←mul_div_assoc, neg_one_mul], linarith},
  linarith
end

lemma contra (x y z : ℝ × ℝ) : ¬(between x y z ∧ between x z y) :=
begin
  intro hf,
  rcases hf.1 with ⟨hyz, k₁, hk₁pos, hk₁⟩,
  rcases hf.2 with ⟨hzy, k₂, hk₂pos, hk₂⟩,
  have : k₁ • y + y - k₁ • z = k₂ • z + z - k₂ • y,
    rw [←hk₁, ←hk₂, add_sub_cancel, add_sub_cancel],
  have : (k₁ + k₂ + 1) • (y - z) = 0,
    calc (k₁ + k₂ + 1) • (y - z)
       = (k₁ + k₂) • (y - z) + (y - z)               : by rw [add_smul, one_smul]
   ... = k₁ • y + y - k₁ • z - (k₂ • z + z - k₂ • y) : by {rw [add_smul, smul_sub, smul_sub], ring}
   ... = 0                                           : by rw [this, sub_self],
  simp at this,
  cases this with hf hf,
  linarith,
  exact hyz (sub_eq_zero.1 hf)
end

lemma line_vec_eq (hab : a ≠ b) : ∃ k₁ k₂ C : ℝ,
{x : ℝ × ℝ | ∃ (μ : ℝ), x = a + μ • (b - a)} = {x : ℝ × ℝ | k₁*x.1 + k₂*x.2 + C = 0} :=
begin
  use [b.2 - a.2, a.1 - b.1, (a.2 - b.2) * a.1 + (b.1 - a.1) * a.2],
  ext, simp, split; intro h,
  cases h with μ hx,
  have h₁ : x.1 = a.1 + μ * b.1 - μ * a.1, rw hx, simp, ring,
  have h₂ : x.2 = a.2 + μ * b.2 - μ * a.2, rw hx, simp, ring,
  rw [h₁, h₂], ring,
  by_cases h0 : a.1 - b.1 = 0,
    have : a.2 - b.2 ≠ 0,
      intro hf,
      exfalso, apply hab, rw [prod.ext_iff, sub_eq_zero.1 h0, sub_eq_zero.1 hf],
      exact ⟨rfl, rfl⟩,
    rw sub_eq_zero.1 h0 at h, simp at h,
    rw [←neg_sub b.2 a.2, ←neg_mul_eq_neg_mul, tactic.ring.add_neg_eq_sub, ←mul_sub] at h,
    simp at h, cases h,
    exfalso, apply this, rw sub_eq_zero.1 h, exact sub_self _,
    use (x.2 - a.2) / (b.2 - a.2),
    rw prod.ext_iff, simp, split,
    rw sub_eq_zero.1 h0, simp, exact sub_eq_zero.1 h,
    rw div_mul_cancel, simp,
    intro hf, apply hab, rw [prod.ext_iff, sub_eq_zero.1 h0, sub_eq_zero.1 hf],
    exact ⟨rfl, rfl⟩,
  use (x.1 - a.1) / (b.1 - a.1),
  rw prod.ext_iff, simp, split,
  rw div_mul_cancel, simp, intro hf, apply h0, rw sub_eq_zero.1 hf, exact sub_self _,
  rw [←neg_sub b.1 a.1, ←neg_sub b.2 a.2, add_assoc, add_comm (-(b.1 - a.1) * x.2) _, ←add_assoc,
    ←add_assoc, ←neg_mul_eq_neg_mul, tactic.ring.add_neg_eq_sub, ←neg_mul_eq_neg_mul,
    tactic.ring.add_neg_eq_sub, ←add_sub, ←mul_sub, ←mul_sub] at h,
  rw [div_mul_eq_mul_div, mul_comm, eq_neg_of_add_eq_zero h, mul_comm, neg_mul_eq_neg_mul,
    mul_div_cancel], ring,
  intro hf, apply h0, rw sub_eq_zero.1 hf, exact sub_self _
end

lemma between_rw : between a b c ↔ b ≠ c ∧ ∃ k : ℝ, k > 0
∧ b = (1 / (k + 1)) • a + (k / (k + 1)) • c :=
begin
  split; rintros ⟨hbc, k, hkpos, hk⟩,
  split, exact hbc,
  use k, split, exact hkpos,
  calc b = (1 / (k + 1)) • ((k + 1) • b)
         : by {rw [smul_smul, div_mul_cancel, one_smul], linarith}
     ... = (1 / (k + 1)) • (a + k • c)
         : by rw [hk, add_smul, one_smul]
     ... = (1 / (k + 1)) • a + (k / (k + 1)) • c
         : by rw [smul_add, smul_smul, div_mul_eq_mul_div, one_mul],
  split, exact hbc,
  use k, split, exact hkpos,
  symmetry,
  calc k • b + b
    = (k / (k + 1)) • a + k • (k / (k + 1)) • c + ((1 / (k + 1)) • a + (k / (k + 1)) • c)
      : by rw [hk, smul_add, smul_smul, ←mul_div_assoc, mul_one]
... = ((k / (k + 1)) • a + ((1 / (k + 1)) • a) + ((k / (k + 1)) • (k • c) + (k / (k + 1)) • c))
      : by rw [←smul_assoc, smul_smul, mul_comm, ←smul_smul, add_assoc, add_assoc,
        add_comm ((k • (k / (k + 1))) • c) _, add_assoc ((1 / (k + 1)) • a) _ _,
        add_comm ((k / (k + 1)) • c) _, smul_assoc]
... = a + (k / (k + 1) * k + k / (k + 1) * 1) • c
      : by {rw [←add_smul, ←add_div, div_self, one_smul, smul_smul, ←add_smul, mul_one], linarith}
... = a + k • c
      : by {rw [←mul_add, div_mul_cancel], linarith}
end

lemma between_equi {k₁ k₂ C : ℝ} (ha : a ∉ {x : ℝ × ℝ | k₁*x.1 + k₂*x.2 + C = 0})
(hb : b ∉ {x : ℝ × ℝ | k₁*x.1 + k₂*x.2 + C = 0}) (hab : a ≠ b) :
(∃ c : ℝ × ℝ, c ∈ {x : ℝ × ℝ | k₁*x.1 + k₂*x.2 + C = 0} ∧ between a c b) ↔ 
k₁*a.1 + k₂*a.2 + C > 0 ∧ k₁*b.1 + k₂*b.2 + C < 0
∨ k₁*a.1 + k₂*a.2 + C < 0 ∧ k₁*b.1 + k₂*b.2 + C > 0 :=
begin
  set x := k₁ * a.fst + k₂ * a.snd + C with hx,
  set y := k₁ * b.fst + k₂ * b.snd + C with hy,
  split; intro h,
  rcases h with ⟨c, hc, hacb⟩,
  rcases between_rw.1 hacb with ⟨hcb, k, hkpos, hk⟩,
  rw hk at hc, dsimp at hc,
  dsimp at ha hb,
  have : x + k * y = 0,
    rw [hx, hy, ←zero_mul (k + 1), ←hc, add_mul, add_mul, mul_assoc k₁ _ _,
      mul_comm _ (k + 1), mul_add, mul_add, mul_add, ←mul_assoc (k + 1) _ _,
      mul_one_div_cancel, one_mul, ←mul_assoc (k + 1) _ _, mul_comm (k + 1),
      div_mul_cancel, mul_assoc k₂ _ _, mul_comm _ (k + 1), mul_add, mul_add,
      mul_add, ←mul_assoc (k + 1) _ _, mul_one_div_cancel, one_mul,
      ←mul_assoc (k + 1) _ _, mul_comm (k + 1), div_mul_cancel],
      ring, all_goals {try {by linarith}},
  cases (ne.symm ha).lt_or_lt with hx hx,
  left, split, exact hx,
  suffices : k * y < 0, by_contra, push_neg at h,
  exact (not_le_of_gt this) ((zero_le_mul_left hkpos).2 h),
  linarith,
  right, split, exact hx,
  suffices : k * y > 0, by_contra, push_neg at h,
  exact (not_le_of_gt this) (linarith.mul_nonpos h hkpos),
  linarith,
  wlog h₁ : k₁ * a.1 + k₂ * a.2 + C > 0 ∧ k₁ * b.1 + k₂ * b.2 + C < 0 using [a b, b a],
  rw [←hx, ←hy], revert h, tauto,
  rw [←hx, ←hy] at h₁,
  set k := -(x / y) with hk,
  have hkpos : k > 0,
    rw hk, have := div_neg_of_pos_of_neg h₁.1 h₁.2, linarith,
  use (1 / (k + 1)) • a + (k / (k + 1)) • b,
  split, dsimp, rw ←mul_left_inj' (show k + 1 ≠ 0, by linarith),
  rw [zero_mul, add_mul, add_mul, mul_assoc, mul_comm _ (k + 1), mul_add, ←mul_assoc,
    mul_one_div_cancel, one_mul, ←mul_assoc, ←mul_div_assoc, mul_comm _ k, mul_div_cancel,
    mul_assoc, mul_comm _ (k + 1), mul_add, mul_add, ←mul_assoc, ←mul_assoc,
    mul_one_div_cancel, one_mul, ←mul_assoc, ←mul_div_assoc, mul_comm (k + 1) k, mul_div_cancel],
  suffices : x + k * y = 0,
    rw [hx, hy] at this, rw ←this, ring,
  rw hk, ring, rw [div_mul_cancel, sub_self _], exact ne_of_lt h₁.2,
  all_goals {try {by linarith}},
  rw between_rw,
  split, intro hf, apply hab,
  have : (1 / (k + 1)) • (a - b) = 0,
    calc (1 / (k + 1)) • (a - b)
       = (1 / (k + 1)) • a + (k / (k + 1)) • b - (k / (k + 1)) • b - (1 / (k + 1)) • b
       : by rw [add_sub_cancel, smul_sub]
   ... = 0
       : by {rw [hf, sub_sub, ←add_smul, div_add_div_same, div_self, one_smul, sub_self], linarith},
  simp at this, cases this, exfalso, linarith,
  exact sub_eq_zero.1 this,
  use k, exact ⟨hkpos, rfl⟩,
  rw [and_comm, and_comm (x < 0) _, or_comm, hx, hy] at h,
  cases this hb ha hab.symm rfl hx h with c hc,
  exact ⟨c, hc.1, symm hc.2⟩
end

end between

/--Construction of ℝ × ℝ as an incidence order geometry and a Hilbert plane -/
def r_squared : incidence_order_geometry :=
{ between := between,
  B1 :=
  begin
    rintros a b c (h : r_squared.between a b c),
    refine ⟨between.symm h, between.one_ne_two h, between.one_ne_three h,
      between.two_ne_three h, _⟩,
    use {x : ℝ × ℝ | ∃ μ : ℝ, x = a + μ • (b - a)},
    use [a, b], exact ⟨(between.one_ne_two h).symm, rfl⟩,
    refine ⟨_, _, _⟩,
    exact ⟨0, by simp⟩, exact ⟨1, by simp⟩,
    exact between.collinear h
  end,
  B2 := λ a b hab, between.extend hab,
  B3 :=
  begin
    split,
    intros a b c l hl habcl hab hac hbc,
    have := @col_in12 (affine_plane ℝ) a b c ⟨l, hl, habcl⟩ hab,
    rw between.line_rw hab at this,
    cases this with μ hc,
    exact between.tri hab hac hbc hc,
    intros a b c,
    split, exact between.contra a b c,
    split, intro hf, exact between.contra c b a ⟨between.symm hf.1, between.symm hf.2⟩,
    intro hf, exact between.contra b c a ⟨between.symm hf.1, hf.2⟩,
  end,
  B4 :=
  begin
    intros a b c l hl habc hal hbl hcl hd,
    rcases hd with ⟨d, hadb, hdl⟩,
    have hcd : c ≠ d, intro hcd, rw ←hcd at hdl, exact hcl hdl,
    rcases hl with ⟨u₀, u, huu₀, hl⟩,
    rcases between.line_vec_eq huu₀.symm with ⟨k₁, k₂, C, hk⟩, rw hk at hl,
    have hab := (@noncol_neq (affine_plane ℝ) a b c habc).1,
    have hac := (@noncol_neq (affine_plane ℝ) a b c habc).2.1,
    have hbc := (@noncol_neq (affine_plane ℝ) a b c habc).2.2,
    rw hl at hcl hdl hal hbl, rw hl,
    split,
    cases (between.between_equi hal hbl hab).1 ⟨d, hdl, hadb⟩;
    cases lt_or_gt_of_ne hcl with hc hc,
    cases (between.between_equi _ _ hac).2 (by {left, exact ⟨h.1, hc⟩}) with p hp,
    use p, split, exact hp.1, left, exact hp.2,
    simp, linarith, simp, linarith,
    cases (between.between_equi _ _ hbc.symm).2 (by {left, exact ⟨hc, h.2⟩}) with p hp,
    use p, split, exact hp.1, right, exact between.symm hp.2,
    simp, linarith, simp, linarith,
    cases (between.between_equi _ _ hbc).2 (by {left, exact ⟨h.2, hc⟩}) with p hp,
    use p, split, exact hp.1, right, exact hp.2,
    simp, linarith, simp, linarith,
    cases (between.between_equi _ _ hac.symm).2 (by {left, exact ⟨hc, h.1⟩}) with p hp,
    use p, split, exact hp.1, left, exact between.symm hp.2,
    simp, linarith, simp, linarith,
    intros p q hpl hql hf,
    cases (between.between_equi hal hbl hab).1 ⟨d, hdl, hadb⟩;
    cases (between.between_equi hal hcl hac).1 ⟨p, hpl, hf.1⟩;
    cases (between.between_equi hbl hcl hbc).1 ⟨q, hql, hf.2⟩;
    linarith
  end,
  ..affine_plane ℝ}

def seg_congr (s₁ s₂ : @seg r_squared) : Prop :=
∃ a b c d : r_squared.pts, s₁ = @two_pt_seg r_squared a b ∧ s₂ = @two_pt_seg r_squared c d
∧ (a.1 - b.1)^2 + (a.2 - b.2)^2 = (c.1 - d.1)^2 + (c.2 - d.2)^2

lemma two_pt_seg_congr (a b c d : r_squared.pts) :
seg_congr (@two_pt_seg r_squared a b) (@two_pt_seg r_squared c d) ↔
(a.1 - b.1)^2 + (a.2 - b.2)^2 = (c.1 - d.1)^2 + (c.2 - d.2)^2 :=
begin
  split; intro h,
  rcases h with ⟨a', b', c', d', hs₁, hs₂, h⟩,
  cases @two_pt_seg_pt r_squared a b a' b' hs₁ with hs₁ hs₁;
  cases @two_pt_seg_pt r_squared c d c' d' hs₂ with hs₂ hs₂;
  rw [hs₁.1, hs₁.2, hs₂.1, hs₂.2], exact h,
  rw [←neg_sub c'.1 d'.1, ←neg_sub c'.2 d'.2, neg_sq, neg_sq], exact h,
  rw [←neg_sub a'.1 b'.1, ←neg_sub a'.2 b'.2, neg_sq, neg_sq], exact h,
  rw [←neg_sub a'.1 b'.1, ←neg_sub a'.2 b'.2, neg_sq, neg_sq,
    ←neg_sub c'.1 d'.1, ←neg_sub c'.2 d'.2, neg_sq, neg_sq], exact h,
  exact ⟨a, b, c, d, rfl, rfl, h⟩
end

namespace seg

lemma same_side_pt_rw {a b c : ℝ × ℝ} : @same_side_pt r_squared a b c ↔ a ≠ b ∧
∃ k : ℝ, k > 0 ∧ b - a = k • (c - a) :=
begin
  by_cases hbc : b = c,
    rw hbc, split; intro h,
    exact ⟨(@same_side_pt_neq r_squared a c c h).1.symm, ⟨1, by simp⟩⟩,
    exact @same_side_pt_refl r_squared a c h.1,
  split,
  intro habc, split, exact (@same_side_pt_neq r_squared a b c habc).1.symm,
  have hab := (@same_side_pt_neq r_squared a b c habc).1.symm,
  have hac := (@same_side_pt_neq r_squared a b c habc).2.symm,
  have := @col_in13 r_squared.to_incidence_geometry a b c habc.2 hac,
  rw between.line_rw at this,
  cases this with μ hb,
  use μ, split,
  by_contra hf, push_neg at hf,
  have : μ < 0,
    apply (ne.le_iff_lt _).1 hf,
    intro hf, rw hf at hb, simp at hb, exact hab hb.symm,
  rw [←not_diff_side_pt, ←between_diff_side_pt] at habc, apply habc,
  split, exact hac,
  use -μ, split, linarith,
  rw [hb, smul_sub, add_assoc, sub_add, neg_smul, sub_neg_eq_add, add_comm (μ • a) _,
    ←sub_sub, sub_self, zero_sub, add_comm, neg_smul],
  exact habc.2, exact hab.symm, exact hac.symm,
  rw hb, simp, exact hac,
  rintros ⟨hab, k, hkpos, hk⟩,
  split, intro hf,
  rcases hf with hf | hf | hf,
  rcases hf.2 with ⟨k', hk'pos, hk'⟩,
  have : k' • (a - c) = b - a,
    calc k' • (a - c) = k' • a - k' • c           : by rw smul_sub
                  ... = k' • a - (b + k' • c - b) : by ring
                  ... = b - a                     : by {rw hk', ring},
  have : (k + k') • (c - a) = 0,
    rw [add_smul, ←hk, ←neg_sub a c, smul_neg, tactic.ring.add_neg_eq_sub, this, sub_self],
  simp at this, cases this with hf hf,
  linarith, rw [hf, smul_zero] at hk, exact hab.symm (sub_eq_zero.1 hk),
  exact hab hf, simp at hf, rw [hf, sub_self, smul_zero] at hk, exact hbc (sub_eq_zero.1 hk),
  apply col_in13', rw between.line_rw,
  use k, rw [←sub_add_cancel b a, hk, add_comm],
  intro hf, rw [hf, sub_self, smul_zero] at hk, exact hbc (sub_eq_zero.1 hk)
end

open real

lemma extend {a b : ℝ × ℝ} {l : @seg r_squared} (hl : @seg_nontrivial r_squared l)
(hab : a ≠ b) : ∃ c, @same_side_pt r_squared a b c ∧ seg_congr l (@two_pt_seg r_squared a c)
∧ ∀ (x : r_squared.pts), @same_side_pt r_squared a b x
→ seg_congr l (@two_pt_seg r_squared a x) → x = c:=
begin
  rcases @seg_two_pt r_squared l with ⟨m, n, hlmn⟩,
  rw [hlmn, seg_nontrivial_iff_neq] at hl,
  rw hlmn,
  set μ := sqrt ((m.1 - n.1)^2 + (m.2 - n.2)^2) / sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) with hμ,
  use (a.1 + μ * (b.1 - a.1), a.2 + μ * (b.2- a.2)),
  have h0 : (m.1 - n.1) ^ 2 + (m.2 - n.2) ^ 2 ≠ 0,
    intro hf,
    apply hl, rw prod.ext_iff,
    exact ⟨by nlinarith, by nlinarith⟩,
  have h0' : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 ≠ 0,
    intro hf,
    apply hab, rw prod.ext_iff,
    exact ⟨by nlinarith, by nlinarith⟩,
  have hμpos : μ > 0,
    apply div_pos,
    rw sqrt_pos, exact h0.symm.le_iff_lt.1 (by nlinarith),
    rw sqrt_pos, exact h0'.symm.le_iff_lt.1 (by nlinarith),
  split, rw same_side_pt_rw, split, exact hab,
  use 1 / μ, split,
  exact one_div_pos.2 hμpos,
  rw [prod.ext_iff, hμ], simp,
  rw [←mul_assoc, div_mul_div_cancel, div_self, one_mul, ←mul_assoc,
    div_mul_div_cancel, div_self, one_mul], exact ⟨rfl, rfl⟩,
  exact (sqrt_ne_zero (by nlinarith)).2 h0', exact (sqrt_ne_zero (by nlinarith)).2 h0,
  exact (sqrt_ne_zero (by nlinarith)).2 h0', exact (sqrt_ne_zero (by nlinarith)).2 h0,
  split,
  use [m, n, a, (a.1 + μ * (b.1 - a.1), a.2 + μ * (b.2- a.2))],
  simp, rw [←sub_sub, sub_self, zero_sub, ←sub_sub, sub_self, zero_sub, neg_sq, neg_sq, mul_pow,
    mul_pow, ←mul_add, hμ, ←sqrt_div, sq_sqrt, ←neg_sub a.1 b.1, ←neg_sub a.2 b.2, neg_sq, neg_sq,
    div_mul_cancel], exact h0', apply div_nonneg, nlinarith, nlinarith, nlinarith,
  intros x habx hx,
  rw two_pt_seg_congr at hx,
  rcases (same_side_pt_rw.1 (@same_side_pt_symm r_squared a b x habx)).2 with ⟨μ', hμ'pos, hμ'⟩,
  rw [←neg_sub x.1 a.1, ←neg_sub x.2 a.2, neg_sq, neg_sq] at hx,
  rw prod.ext_iff at hμ', simp at hμ',
  suffices : μ = μ',
    rw [this, ←hμ'.1, ←hμ'.2], simp,
  rw [hμ'.1, hμ'.2, mul_pow, mul_pow, ←mul_add] at hx,
  rw [hμ, hx, sqrt_mul, ←neg_sub a.1 b.1, ←neg_sub a.2 b.2, neg_sq, neg_sq, mul_div_cancel, sqrt_sq],
  linarith, rw sqrt_ne_zero', apply (ne.symm h0').le_iff_lt.1, nlinarith,
  nlinarith
end

lemma between_cal {a b c : ℝ × ℝ} (habc : between a b c) :
real.sqrt ((a.1 - c.1)^2 + (a.2 - c.2)^2)
= real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) + real.sqrt ((b.1 - c.1)^2 + (b.2 - c.2)^2) :=
begin
  rcases habc.2 with ⟨k, hkpos, hk⟩,
  have h₁ : a - c = k • (b - c) + (b - c),
    calc a - c = a + k • c - k • c - c : by ring
           ... = k • b + b - k • c - c : by rw hk
           ... = k • (b - c) + (b - c) : by {rw smul_sub, ring},
  have h₂ : a - b = k • (b - c) ,
    calc a - b = a + k • c - k • c - b : by ring
           ... = k • b + b - k • c - b : by rw hk
           ... = k • (b - c)           : by {rw smul_sub, ring},
  rw prod.ext_iff at h₁ h₂, simp at h₁ h₂,
  rw [h₁.1, h₁.2, h₂.1, h₂.2, mul_pow, mul_pow, ←mul_add, sqrt_mul, sqrt_sq], symmetry,
  calc k * sqrt ((b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2) + sqrt ((b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2)
     = (k + 1) * sqrt ((b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2)
     : by rw [add_mul, one_mul]
 ... = sqrt (((k + 1) * (b.1 - c.1)) ^ 2 + ((k + 1) * (b.2 - c.2)) ^ 2)
     : by {rw [mul_pow, mul_pow, ←mul_add, sqrt_mul, sqrt_sq], linarith, nlinarith}
 ... = sqrt ((k * (b.1 - c.1) + (b.1 - c.1)) ^ 2 + (k * (b.2 - c.2) + (b.2 - c.2)) ^ 2)
     : by rw [add_mul, one_mul, add_mul, one_mul],
  linarith, nlinarith
end

end seg

open real

noncomputable def cos (a o b : ℝ × ℝ) : ℝ :=
((a.1 - o.1) * (b.1 - o.1) + (a.2 - o.2) * (b.2 - o.2))
/ (sqrt ((a.1 - o.1)^2 + (a.2 - o.2)^2) * sqrt ((b.1 - o.1)^2 + (b.2 - o.2)^2))

def ang_congr (α β : @ang r_squared) : Prop :=
∃ a b c d e f : ℝ × ℝ, α = @three_pt_ang r_squared a b c ∧ β = @three_pt_ang r_squared d e f
∧ cos (a - b) (c - b) = cos (d - e) (f - e)

namespace ang

end ang

example {a b c d : euclidean_space ℝ (fin 2)} :
inner (b - a) (c - d) =
(b 0 - a 0) * (c 0 - d 0) + (b 1 - a 1) * (c 0 - d 0) :=
begin
  simp,
  sorry
end

example : hilbert_plane :=
{ seg_congr := seg_congr,
  C1 := λ a b l, seg.extend,
  C2 :=
  begin
    split,
    intros s₁ s₂ s₃ hs₁s₂ hs₁s₃,
    rcases @seg_two_pt r_squared s₁ with ⟨a, b, hs₁⟩,
    rcases @seg_two_pt r_squared s₂ with ⟨c, d, hs₂⟩,
    rcases @seg_two_pt r_squared s₃ with ⟨e, f, hs₃⟩,
    rw [hs₁, hs₂, two_pt_seg_congr] at hs₁s₂,
    rw [hs₁, hs₃, two_pt_seg_congr] at hs₁s₃,
    rw [hs₂, hs₃, two_pt_seg_congr, ←hs₁s₂, ←hs₁s₃],
    intro s,
    rcases @seg_two_pt r_squared s with ⟨a, b, hs⟩,
    exact ⟨a, b, a, b, hs, hs, rfl⟩
  end,
  C3 :=
  begin
    intros a b c d e f habc hdef habde hbcef,
    rw two_pt_seg_congr at habde hbcef, rw two_pt_seg_congr,
    apply (real.sqrt_inj _ _).1 _,
    nlinarith, nlinarith,
    rw [seg.between_cal habc, seg.between_cal hdef, habde, hbcef]
  end,
  ang_congr := ang_congr,
  C4 :=
  begin
    sorry,
  end,
  C5 :=
  begin
    split,
    intros α β γ hαβ hαγ,
    rcases hαβ with hαβ | hαβ | hαβ | hαβ,
    left, exact ⟨hαβ.2.1, ang.congr_acute hαγ hαβ.1,
      hαβ.2.2.symm.trans (ang.congr_acute_tangent hαγ hαβ.1)⟩,
    right, left,
    exact ⟨hαβ.2, ang.congr_right hαγ hαβ.1⟩,
    right, right, left, exact ⟨hαβ.2.1, ang.congr_obtuse hαγ hαβ.1,
      hαβ.2.2.symm.trans (ang.congr_obtuse_tangent hαγ hαβ.1)⟩,
    right, right, right,
    exact ⟨hαβ.2, ang.congr_trivial hαγ hαβ.1⟩,
    intro α,
    by_cases @ang_nontrivial r_squared α,
      rcases acute_right_obtuse h with h | h | h,
      left, simp, exact h,
      right, left, simp, exact h,
      right, right, left, simp, exact h,
    right, right, right, simp, exact h
  end,
  C6 := sorry,
  ..r_squared }

end r_squared

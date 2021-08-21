import congruence.basic
import data.zmod.basic
import data.real.basic
import data.real.sqrt
import group_theory.group_action.defs
import analysis.normed_space.inner_product
import analysis.normed_space.pi_Lp
import geometry.euclidean.basic

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
  rw hk, ring_nf, rw [div_mul_cancel, sub_self _], exact ne_of_lt h₁.2,
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
  have := @col_in13 (affine_plane ℝ) a b c habc.2 hac,
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

def f (a : ℝ × ℝ) : euclidean_space ℝ (fin 2) := ![a.1, a.2]

lemma f1 (a : ℝ × ℝ) : a.1 = f a 0 := rfl

lemma f2 (a : ℝ × ℝ) : a.2 = f a 1 := rfl

lemma f_add (a b : ℝ × ℝ) : f (a + b) = f a + f b := by {unfold f, simp}

lemma f_neg (a : ℝ × ℝ) : f (-a) = - f a := by {unfold f, simp}

lemma f_sub (a b : ℝ × ℝ) : f (a - b) = f a - f b :=
by rw [←tactic.ring.add_neg_eq_sub, ←tactic.ring.add_neg_eq_sub, ←f_neg, f_add]

lemma f_smul (k : ℝ) (a : ℝ × ℝ) : f (k • a) = k • (f a) := by {unfold f, simp}

lemma f_inj {a b : ℝ × ℝ} (h : f a = f b) : a = b :=
by {rw [prod.ext_iff, f1, f1, f2, f2, h], exact ⟨rfl, rfl⟩}

lemma f_zero {a : ℝ × ℝ} : f a = 0 ↔ a = 0 :=
by {unfold f, rw prod.ext_iff, simp}

lemma f_nonzero {a : ℝ × ℝ} : f a ≠ 0 ↔ a ≠ 0 :=
by {split; contrapose!; rw f_zero; simp}

lemma inner_equiv (a b : ℝ × ℝ) :
inner (f a) (f b) = a.1 * b.1 + a.2 * b.2 :=
by {unfold inner, rw [f1, f1, f2, f2, fin.sum_univ_succ,
    fin.sum_univ_succ, fin.succ_zero_eq_one], simp}

open real

lemma norm_equiv (a : ℝ × ℝ) : ∥f a∥ = sqrt (a.1^2 + a.2^2) :=
begin
  have : ∀ a : ℝ, a ^ (2 : ℝ) = a ^ 2, intro a, rw ←rpow_nat_cast, simp,
  unfold norm, rw [f1, f2, fin.sum_univ_succ],
  simp, rw [fin.succ_zero_eq_one, ←sq_abs, ←sq_abs (f a 1)],
  symmetry, rw sqrt_eq_iff_sq_eq,
  rw [←rpow_nat_cast, ←rpow_mul], simp only [inv_mul_cancel_of_invertible,
    nat.cast_bit0, rpow_one, nat.cast_one],
  rw [←rpow_nat_cast, ←rpow_nat_cast], simp,
  rw [this, this], nlinarith, nlinarith,
  apply rpow_nonneg_of_nonneg, rw [this, this], nlinarith,
end

open euclidean_geometry
open inner_product_geometry

lemma ang_eq_same_side_pt {a o c : ℝ × ℝ} (b : ℝ × ℝ) (h : @same_side_pt r_squared o a c) :
angle (f a) (f o) (f b) = angle (f c) (f o) (f b) :=
begin
  unfold euclidean_geometry.angle inner_product_geometry.angle,
  rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub],
  rcases (seg.same_side_pt_rw.1 h).2 with ⟨k, hkpos, hk⟩,
  rw [←f_sub, ←f_sub, ←f_sub, hk, f_smul, inner_smul_left, norm_smul, norm_eq_abs, abs_of_pos,
    is_R_or_C.conj_to_real, mul_assoc, mul_div_mul_left];
  linarith
end

def ang_congr (α β : @ang r_squared) : Prop := ∃ a b c d : ℝ × ℝ,
α = @three_pt_ang r_squared a (@ang.vertex r_squared α) b
∧ β = @three_pt_ang r_squared c (@ang.vertex r_squared β) d
∧ (@col (affine_plane ℝ) a (@ang.vertex r_squared α) b ↔ @col (affine_plane ℝ)
c (@ang.vertex r_squared β) d) ∧ (@noncol (affine_plane ℝ) a (@ang.vertex r_squared α) b
→ angle (f a) (f (@ang.vertex r_squared α)) (f b) = angle (f c) (f (@ang.vertex r_squared β)) (f d))

lemma three_pt_ang_congr {a o b a' o' b' : ℝ × ℝ} (haob : @noncol (affine_plane ℝ) a o b)
(he : ang_congr (@three_pt_ang r_squared a o b) (@three_pt_ang r_squared a' o' b')) :
angle (f a) (f o) (f b) = angle (f a') (f o') (f b') :=
begin
  rcases he with ⟨c, d, c', d', h₁, h₂, h, key⟩,
  rw three_pt_ang_vertex at h₁ h₂ key h, rw three_pt_ang_vertex at key h,
  have hcod := (@ang_nontrivial_iff_noncol r_squared a o b).2 haob,
  rw [h₁, ang_nontrivial_iff_noncol] at hcod,
  specialize key hcod,
  have ha'o'b' : @noncol (affine_plane ℝ) a' o' b',
    apply (@ang_nontrivial_iff_noncol r_squared a' o' b').1,
    rw [h₂, ang_nontrivial_iff_noncol], intro hf, rw ←h at hf, exact absurd hf hcod,
  have : angle (f a) (f o) (f b) = angle (f c) (f o) (f d),
    rw three_pt_ang_eq_iff at h₁,
    cases h₁.2 with h h,
    rw [ang_eq_same_side_pt b h.1, euclidean_geometry.angle_comm,
      ang_eq_same_side_pt c h.2, euclidean_geometry.angle_comm],
    rw [ang_eq_same_side_pt b h.1, euclidean_geometry.angle_comm,
      ang_eq_same_side_pt d h.2, euclidean_geometry.angle_comm],
    exact haob,
  rw [this, key],
  rw three_pt_ang_eq_iff at h₂,
  symmetry,
  cases h₂.2 with h h,
  rw [ang_eq_same_side_pt b' h.1, euclidean_geometry.angle_comm,
      ang_eq_same_side_pt c' h.2, euclidean_geometry.angle_comm],
  rw [ang_eq_same_side_pt b' h.1, euclidean_geometry.angle_comm,
    ang_eq_same_side_pt d' h.2, euclidean_geometry.angle_comm],
  exact ha'o'b'
end

namespace ang

lemma backward1 {a b x y c : ℝ} (hb : b ≠ 0)
(hab : a^2 + b^2 = 1) (hx : x = sqrt ((1 - a^2) * (1 - c^2)) + a*c)
(hy : y = -(abs b / b) * a * sqrt (1 - c^2) + b * c) : a*x + b*y = c :=
begin
  replace hx : a * x = a * sqrt (b^2 + a^2 - a^2) * sqrt (1 - c^2) + a^2 * c,
    rw [hx, mul_add, add_comm (b^2) _, hab, mul_assoc, ←sqrt_mul]; nlinarith,
  simp at hx, rw sqrt_sq_eq_abs at hx,
  rw [hx, hy, mul_add b _ _, ←mul_assoc b _ _, ←mul_assoc b _ _, mul_neg_eq_neg_mul_symm,
    ←mul_div_assoc, mul_comm b _, mul_div_cancel _ hb],
  ring_exp, rw [mul_comm, ←mul_add, hab, mul_one]
end

lemma backward2 {a b x y c : ℝ} (hb : b ≠ 0)
(hab : a^2 + b^2 = 1) (hx : x = -sqrt ((1 - a^2) * (1 - c^2)) + a*c)
(hy : y = (abs b / b) * a * sqrt (1 - c^2) + b * c) : a*x + b*y = c :=
begin
  replace hx : a * x = -a * sqrt (b^2 + a^2 - a^2) * sqrt (1 - c^2) + a^2 * c,
    rw [hx, mul_add, add_comm (b^2) _, hab, mul_assoc, ←sqrt_mul]; nlinarith,
  simp at hx, rw sqrt_sq_eq_abs at hx,
  rw [hx, hy, mul_add b _ _, ←mul_assoc b _ _, ←mul_assoc b _ _,
    ←mul_div_assoc, mul_comm b _, mul_div_cancel _ hb],
  ring_exp, rw [mul_comm, ←mul_add, hab, mul_one]
end

lemma unit1 {a b x y c : ℝ} (hb : b ≠ 0) (hc : 0 ≤ 1 - c^2)
(hab : a^2 + b^2 = 1) (hx : x = sqrt ((1 - a^2) * (1 - c^2)) + a*c)
(hy : y = -(abs b / b) * a * sqrt (1 - c^2) + b * c) : x^2 + y^2 = 1 :=
begin
  have hab' : b^2 = 1 - a^2,
    rw [←hab, add_comm, add_sub_cancel],
  have cal1 : ∀ a b c d e : ℝ, 2 * (-a * b * c) * (d * e) = -(2 * e * (a * d) * b * c),
    intros a b c d e, ring,
  have cal2 : ∀ a b c d : ℝ, 2 * (a * b) * (c * d) = 2 * d * a * c * b,
    intros a b c d, ring,
  have cal3 : ∀ a b c d : ℝ, a * (1 - b) + c + d * b + (d * (1 - b) - c + a * b) = d + a,
    intros a b c d, ring,
  rw [hx, hy, add_sq, add_sq, sq_sqrt, mul_pow, mul_pow, sq_sqrt, mul_pow, neg_sq,
    div_pow (abs b) b, sq_abs, div_self, one_mul, ←hab', sqrt_mul, sqrt_sq_eq_abs, mul_pow,
    cal1, div_mul_cancel, cal2, tactic.ring.add_neg_eq_sub, cal3, hab],
  exact hb, exact sq_nonneg _, exact pow_ne_zero 2 hb, exact hc,
  apply mul_nonneg, rw ←hab', exact sq_nonneg _, exact hc
end

lemma unit2 {a b x y c : ℝ} (hb : b ≠ 0) (hc : 0 ≤ 1 - c^2)
(hab : a^2 + b^2 = 1) (hx : x = -sqrt ((1 - a^2) * (1 - c^2)) + a*c)
(hy : y = (abs b / b) * a * sqrt (1 - c^2) + b * c) : x^2 + y^2 = 1 :=
begin
  have hab' : b^2 = 1 - a^2,
    rw [←hab, add_comm, add_sub_cancel],
  have cal1 : ∀ a b c d e : ℝ, 2 * (a * b * c) * (d * e) = 2 * e * (a * d) * b * c,
    intros a b c d e, ring,
  have cal2 : ∀ a b c d : ℝ, 2 * -(a * b) * (c * d) = -(2 * d * a * c * b),
    intros a b c d, ring,
  have cal3 : ∀ a b c d : ℝ, a * (1 - b) - c + d * b + (d * (1 - b) + c + a * b) = d + a,
    intros a b c d, ring,
  rw [hx, hy, add_sq, add_sq, neg_sq, sq_sqrt, mul_pow, mul_pow, sq_sqrt, mul_pow, 
    div_pow (abs b) b, sq_abs, div_self, one_mul, ←hab', sqrt_mul, sqrt_sq_eq_abs, mul_pow,
    cal1, div_mul_cancel, cal2, tactic.ring.add_neg_eq_sub, cal3, hab],
  exact hb, exact sq_nonneg _, exact pow_ne_zero 2 hb, exact hc,
  apply mul_nonneg, rw ←hab', exact sq_nonneg _, exact hc
end

private lemma forward_prep {a b x y c : ℝ} (hab : a^2 + b^2 = 1) (hxy : x^2 + y^2 = 1)
(he : a * x + b * y = c) : x = sqrt ((1 - a^2) * (1 - c^2)) + a * c
∨ x = -sqrt ((1 - a^2) * (1 - c^2)) + a * c :=
begin
  have key : (x - a * c)^2 = (1 - a^2) * (1 - c^2),
    rw ←sub_eq_zero,
    calc (x - a * c)^2 - (1 - a^2) * (1 - c^2)
       = b^2 * x^2 + (a * x + b * y - c - b * y)^2 + a^2 - 1 : by {ring_nf, rw hab, ring}
   ... = b^2 * (x^2 + y^2) + a^2 - 1                         : by {rw he, ring}
   ... = 0                                                   : by {rw [←hab, hxy], ring},
  have := sq_sqrt (show (1 - a^2) * (1 - c^2) ≥ 0, by nlinarith), rw ←this at key,
  cases eq_or_eq_neg_of_sq_eq_sq _ _ key;
  rw ←h; simp
end

lemma forward {a b x y c : ℝ} (hb : b ≠ 0)
(hab : a^2 + b^2 = 1) (hxy : x^2 + y^2 = 1) (he : a * x + b * y = c) :
(x = sqrt ((1 - a^2) * (1 - c^2)) + a * c ∧ y = -(abs b / b) * a * sqrt (1 - c^2) + b * c)
∨ (x = -sqrt ((1 - a^2) * (1 - c^2)) + a * c ∧ y = (abs b / b) * a * sqrt (1 - c^2) + b * c) :=
begin
  cases forward_prep hab hxy he,
  left, split, exact h,
  calc y = (c - a * x) / b
         : by rw [←he, add_comm, add_sub_cancel, mul_comm, mul_div_cancel _ hb]
     ... = ((b^2 + a^2) * c - a^2 * c - a * sqrt ((b^2 + a^2 - a^2) * (1 - c^2))) / b
         : by {rw [add_comm (b^2) _, hab, h], ring}
     ... = (b * b * c - a * (abs b) * sqrt (1 - c^2)) / b
         : by {rw [←sub_mul, add_sub_cancel, sqrt_mul, sqrt_sq_eq_abs], ring_exp, nlinarith}
     ... = -(abs b / b) * a * sqrt (1 - c^2) + b * c
         : by {rw [sub_div, mul_comm, ←mul_assoc, mul_div_cancel _ hb], ring_exp_eq},
  right, split, exact h,
  calc y = (c - a * x) / b
         : by rw [←he, add_comm, add_sub_cancel, mul_comm, mul_div_cancel _ hb]
     ... = ((b^2 + a^2) * c - a^2 * c + a * sqrt ((b^2 + a^2 - a^2) * (1 - c^2))) / b
         : by {rw [add_comm (b^2) _, hab, h], ring}
     ... = (b * b * c + a * (abs b) * sqrt (1 - c^2)) / b
         : by {rw [←sub_mul, add_sub_cancel, sqrt_mul, sqrt_sq_eq_abs], ring_exp, nlinarith}
     ... = (abs b / b) * a * sqrt (1 - c^2) + b * c
         : by {rw [add_div, mul_comm, ←mul_assoc, mul_div_cancel _ hb], ring_exp_eq}
end

lemma unit_wlog {o a : ℝ × ℝ} (hoa : o ≠ a) :
∃ b : ℝ × ℝ, @same_side_pt r_squared o a b ∧ (b.1 - o.1)^2 + (b.2 - o.2)^2 = 1 :=
begin
  sorry
end

lemma ineq {o a : ℝ × ℝ} (hao : a ≠ o) :
((a - o).1 / ∥f a - f o∥)^2 ≤ 1 ∧ ((a - o).2 / (∥f a - f o∥))^2 ≤ 1 :=
begin
  have : ∥f (a - o)∥^2 > 0,
    apply sq_pos_of_ne_zero,
    unfold f, simp, intros hf₁ hf₂,
    apply hao, rw prod.ext_iff, exact ⟨sub_eq_zero.1 hf₁, sub_eq_zero.1 hf₂⟩,
  rw ←f_sub, split,
  rw div_pow, apply le_of_mul_le_mul_right _ this,
  rw [div_mul_cancel, one_mul, norm_equiv, sq_sqrt], nlinarith, nlinarith, nlinarith,
  rw div_pow, apply le_of_mul_le_mul_right _ this,
  rw [div_mul_cancel, one_mul, norm_equiv, sq_sqrt], nlinarith, nlinarith, nlinarith
end

lemma ineq' (a b o : ℝ × ℝ) :
inner (f a -ᵥ f o) (f b -ᵥ f o) / (∥f a -ᵥ f o∥ * ∥f b -ᵥ f o∥) ≤ 1
∧ inner (f a -ᵥ f o) (f b -ᵥ f o) / (∥f a -ᵥ f o∥ * ∥f b -ᵥ f o∥) ≥ -1 :=
by {rw ←cos_angle, exact ⟨cos_le_one _, neg_one_le_cos _⟩}

lemma sq_add_sq_zero {a b : ℝ} (h : a^2 + b^2 = 0) : a = 0 ∧ b = 0 :=
begin
  have ha : a^2 ≤ a^2 + b^2, nlinarith,
  have hb : b^2 ≤ a^2 + b^2, nlinarith,
  rw h at ha hb,
  exact ⟨pow_eq_zero (le_antisymm ha (sq_nonneg a)), pow_eq_zero (le_antisymm hb (sq_nonneg b))⟩
end

lemma cos_eq_one {a b c : ℝ × ℝ} (habc : cos (angle (f a) (f b) (f c)) = 1) :
@col (affine_plane ℝ) a b c :=
begin
  cases (cos_eq_one_iff _).1 habc with n hn,
  have hpi : ↑n * (2 * real.pi) ≤ real.pi,
    rw hn, exact arccos_le_pi _,
  have h0 : 0 ≤ ↑n * (2 * real.pi),
    rw hn, exact arccos_nonneg _,
  rw mul_comm at h0,
  have hn₁ : 2 * (n : ℝ) ≥ 0,
    rw [ge_iff_le, zero_le_mul_left],
    apply nonneg_of_mul_nonneg_left h0,
    rw (zero_lt_mul_left (show (2 : ℝ) > 0, by linarith)), exact pi_pos, linarith,
  have hn₂ : 2 * (n : ℝ) ≤ 1,
    rw [←mul_le_mul_left, mul_one],
    rw [mul_comm (2 : ℝ) _, mul_comm, mul_assoc] at hpi, exact hpi,
    exact pi_pos,
  norm_cast at hn₁ hn₂,
  interval_cases (2 * n), simp at h,
  rw h at hn, simp at hn, rcases angle_eq_zero_iff.1 hn.symm with ⟨hab, k, -, h⟩,
  rw [vsub_eq_sub, vsub_eq_sub, ←f_sub, ←f_sub, ←f_smul] at h,
  rw [vsub_eq_sub, ←f_sub, f_nonzero, sub_ne_zero] at hab,
  apply col_in12', rw [line_symm, between.line_rw],
  use k, rw ←f_inj h, ring, exact hab.symm,
  have := int.le_of_dvd (by linarith) ⟨n, h.symm⟩, norm_num at this
end

lemma cos_eq_neg_one {a b c : ℝ × ℝ} (habc : cos (angle (f a) (f b) (f c)) = -1) :
@col (affine_plane ℝ) a b c :=
begin
  replace habc : -cos (angle (f a) (f b) (f c)) = 1, rw [habc, neg_neg],
  rw [←cos_sub_pi, cos_eq_one_iff] at habc,
  cases habc with n hn,
  have hpi : ↑n * (2 * real.pi) ≤ real.pi,
    rw hn, rw ←add_le_add_iff_left real.pi, simp,
    have := arccos_le_pi (inner (f a -ᵥ f b) (f c -ᵥ f b) / (∥f a -ᵥ f b∥ * ∥f c -ᵥ f b∥)),
    apply le_trans this, simp, exact le_of_lt pi_pos,
  have h0 : 0 ≤ ↑n * (2 * real.pi) + real.pi,
    rw [hn, sub_add_cancel], exact arccos_nonneg _,
  rw mul_comm at h0,
  have hn₁ : 2 * (n : ℝ) ≥ -1,
    rw [ge_iff_le, neg_le_iff_add_nonneg, ←mul_le_mul_left (pi_pos), mul_zero, mul_add, mul_one,
      ←mul_assoc, mul_comm _ (2 : ℝ)], exact h0,
  have hn₂ : 2 * (n : ℝ) ≤ 1,
    rw [←mul_le_mul_left, mul_one],
    rw [mul_comm (2 : ℝ) _, mul_comm, mul_assoc] at hpi, exact hpi,
    exact pi_pos,
  replace hn₁ : 2 * n ≥ -1, norm_cast at hn₁, exact hn₁,
  norm_cast at hn₂, interval_cases (2 * n),
  replace h : 2 * (-n) = 1, rw [mul_neg_eq_neg_mul_symm, h, neg_neg],
  have := int.le_of_dvd (by linarith) ⟨-n, h.symm⟩, norm_num at this,
  simp at h, rw h at hn, simp at hn,
  rcases angle_eq_pi_iff.1 (sub_eq_zero.1 hn.symm) with ⟨hab, k, -, h⟩,
  rw [vsub_eq_sub, vsub_eq_sub, ←f_sub, ←f_sub, ←f_smul] at h,
  rw [vsub_eq_sub, ←f_sub, f_nonzero, sub_ne_zero] at hab,
  apply col_in12', rw [line_symm, between.line_rw],
  use k, rw ←f_inj h, ring, exact hab.symm,
  have := int.le_of_dvd (by linarith) ⟨n, h.symm⟩, norm_num at this
end

example {a b c d : ℝ} : a^2 = b^2 → a = b ∨ a = - b := eq_or_eq_neg_of_sq_eq_sq a b

lemma extend {α : @ang r_squared} {o a : ℝ × ℝ} (hα : @ang_nontrivial r_squared α)
(hao : a ≠ o) : ∃ b c : ℝ × ℝ, ang_congr α (@three_pt_ang r_squared b o a)
∧ ang_congr α (@three_pt_ang r_squared c o a)
∧ @diff_side_line r_squared (@line (affine_plane ℝ) o a) b c
∧ ∀ x : ℝ × ℝ, ang_congr α (@three_pt_ang r_squared x o a) →
(@same_side_line r_squared (@line (affine_plane ℝ) o a) b x → @same_side_pt r_squared o b x)
∧ (@same_side_line r_squared (@line (affine_plane ℝ) o a) c x → @same_side_pt r_squared o c x) :=
begin
  set m := (a.1 - o.1) / (∥f a - f o∥) with hm,
  set n := (a.2 - o.2) / (∥f a - f o∥) with hn,
  have hm1 := (ineq hao).1,
  have hn1 := (ineq hao).2,
  have hmn : m^2 + n^2 = 1,
    rw [hm, hn, ←f_sub, norm_equiv, div_pow, div_pow, sq_sqrt, ←add_div,
      prod.fst_sub, prod.snd_sub, div_self],
    intro hf, apply hao, rw prod.ext_iff, have := sq_add_sq_zero hf,
    rw [sub_eq_zero, sub_eq_zero] at this, exact this,
    nlinarith,
  have hmn' : n^2 = 1 - m^2,
    rw [←hmn, add_comm, add_sub_cancel],
  have hmn'' : m / n = (a.1 - o.1) / (a.2 - o.2),
    rw [hm, hn, div_div_div_div_eq, ←div_div_eq_div_mul, mul_div_cancel],
    intro hf, apply hao, rw prod.ext_iff,
    rw [←f_sub, norm_equiv, prod.fst_sub, prod.snd_sub, sqrt_eq_zero] at hf,
    exact ⟨sub_eq_zero.1 (sq_add_sq_zero hf).1, sub_eq_zero.1 (sq_add_sq_zero hf).2⟩,
    nlinarith,
  rcases @ang_three_pt r_squared α with ⟨c, d, hcd⟩,
  rw [hcd, ang_nontrivial_iff_noncol] at hα,
  set o' := @ang.vertex r_squared α with ho',
  set C := cos (angle (f c) (f o') (f d)) with hC,
  have hC1 : C^2 ≠ 1^2,
    intro hf, cases eq_or_eq_neg_of_sq_eq_sq _ _ hf,
    rw h at hC, exact hα (cos_eq_one hC.symm),
    exact hα (cos_eq_neg_one h),
  rw one_pow at hC1,
  have hC1' := abs_cos_le_one (angle (f c) (f o') (f d)),
  replace hC1' : 0 ≤ 1 - C^2,
    rw abs_le at hC1', have := sq_le_sq' hC1'.1 hC1'.2,
    rw one_pow at this, rw sub_nonneg, exact this,
  have forward' : ∀ {b : ℝ × ℝ}, ∥f b -ᵥ f o∥ = 1 → m * (b.1 - o.1) + n * (b.2 - o.2) = C
    → @noncol (affine_plane ℝ) b o a → ang_congr α (@three_pt_ang r_squared b o a),
    intros b hb he hboa,
    use [c, d, b, a], rw [hcd, three_pt_ang_vertex, three_pt_ang_vertex], simp,
    split, exact ⟨λhf, absurd hf hα, λhf, absurd hf hboa⟩,
    intro hα,
    unfold euclidean_geometry.angle inner_product_geometry.angle,
    unfold euclidean_geometry.angle inner_product_geometry.angle at hC, rw cos_arccos at hC,
    rw [arccos_inj, ←hC, ←he, hm, hn, hb, one_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
      vsub_eq_sub, vsub_eq_sub, ←f_sub, ←f_sub, inner_equiv, add_div, mul_comm,
      mul_comm (a.2 - o.2) _, prod.fst_sub, prod.fst_sub, prod.snd_sub, prod.snd_sub],
    exact (ineq' c d o').2, exact (ineq' c d o').1,
    exact (ineq' b a o).2, exact (ineq' b a o).1,
    exact (ineq' c d o').2, exact (ineq' c d o').1,
  have backward : ∀ {b : ℝ × ℝ}, ∥f b -ᵥ f o∥ = 1 → ang_congr α (@three_pt_ang r_squared b o a)
    → @noncol (affine_plane ℝ) b o a → m * (b.1 - o.1) + n * (b.2 - o.2) = C,
    intros b hb hαboa hboa,
    rw hcd at hαboa, have := three_pt_ang_congr hα hαboa,
    unfold euclidean_geometry.angle inner_product_geometry.angle at this,
    unfold euclidean_geometry.angle inner_product_geometry.angle at hC, rw cos_arccos at hC,
    rw [arccos_inj, ←hC, hb, vsub_eq_sub, vsub_eq_sub, ←f_sub, ←f_sub, inner_equiv, one_mul] at this,
    rw [this, hm, hn, f_sub, prod.fst_sub, prod.snd_sub, prod.fst_sub, prod.snd_sub,
      div_mul_eq_mul_div_comm, div_mul_eq_mul_div_comm, add_div], ring,
    exact (ineq' c d o').2, exact (ineq' c d o').1,
    exact (ineq' b a o).2, exact (ineq' b a o).1,
    exact (ineq' c d o').2, exact (ineq' c d o').1,
  by_cases hn0 : n = 0,
    rw hn0 at hn, cases div_eq_zero_iff.1 hn.symm with hn hf,
    rw sub_eq_zero at hn,
    rw [hn0, zero_pow, add_zero] at hmn,
    have hm0 : m ≠ 0,
      intro hf, rw hf at hmn, linarith,
    have hm' : (abs m / m)^2 = 1,
      rw [div_pow, sq_abs, div_self], rw hmn, linarith,
    have hm'' : abs m = 1,
      rw [div_pow, div_eq_one_iff_eq, hmn] at hm',
      rw [←eq_of_sq_eq_sq, one_pow, hm'],
      exact abs_nonneg _, linarith, rw hmn, linarith,
    use [o + ((abs m) / m * C, sqrt (1 - C^2)), o + ((abs m) / m * C, -sqrt (1 - C^2))],
    split,
    apply forward',
    rw [vsub_eq_sub, ←f_sub, add_comm, add_sub_cancel, norm_equiv], simp,
    rw [sq_sqrt hC1', mul_pow, hm', one_mul, add_comm, sub_add_cancel, sqrt_one],
    rw [hn0, zero_mul, add_zero, prod.fst_add], simp,
    rw [←mul_assoc, mul_comm m _, div_mul_cancel _ hm0, hm'', one_mul],
    intro hf, have := @col_in23 (affine_plane ℝ) _ _ _ hf hao.symm,
    rw between.line_rw at this,
    cases this with μ hμ, simp at hμ,
    rw prod.ext_iff at hμ, simp at hμ, rw hn at hμ, simp at hμ,
    rw [sqrt_eq_zero, sub_eq_zero] at hμ, exact hC1.symm hμ.2,
    exact hC1', exact hao.symm,
    split,
    apply forward',
    rw [vsub_eq_sub, ←f_sub, add_comm, add_sub_cancel, norm_equiv], simp,
    rw [sq_sqrt hC1', add_comm, mul_pow, hm', one_mul, sub_add_cancel, sqrt_one],
    rw [hn0, zero_mul, add_zero, prod.fst_add], simp,
    rw [←mul_assoc, mul_comm m _, div_mul_cancel _ hm0, hm'', one_mul],
    intro hf, have := @col_in23 (affine_plane ℝ) _ _ _ hf hao.symm,
    rw between.line_rw at this,
    cases this with μ hμ, simp at hμ,
    rw prod.ext_iff at hμ, simp at hμ, rw hn at hμ, simp at hμ,
    rw [sqrt_eq_zero, sub_eq_zero] at hμ, exact hC1.symm hμ.2,
    exact hC1', exact hao.symm,
    have : @diff_side_line r_squared (@line (affine_plane ℝ) o a)
      (o.1 + (abs m) / m * C, o.2 + sqrt (1 - C^2)) (o.1 + (abs m) / m * C, o.2 + -sqrt (1 - C^2)),
      use ((abs m) / m * C + o.1, o.2), split,
      rw between.line_rw, use (abs m) / m *  C / (a.1 - o.1),
      rw prod.ext_iff, simp,
      rw [div_mul_cancel, add_comm, hn, sub_self], simp,
      intro hf, apply hao, rw prod.ext_iff, rw [hn, sub_eq_zero.1 hf], exact ⟨rfl, rfl⟩,
      exact hao.symm,
      left, split, intro hf, rw [prod.ext_iff, add_comm] at hf, simp at hf,
      rw [sqrt_eq_zero, sub_eq_zero] at hf, exact hC1.symm hf, exact hC1',
      use 1, rw [one_smul, prod.ext_iff], simp,
      split, rw add_comm _ ((abs m) / m * C),
      rw [add_assoc, add_comm (sqrt (1 - C^2)) _, tactic.ring.add_neg_eq_sub, sub_add_cancel],
      rw between.line_rw,
      split, rintros ⟨μ, hμ⟩,
      rw prod.ext_iff at hμ, simp at hμ, rw hn at hμ, simp at hμ,
      rw [sqrt_eq_zero, sub_eq_zero] at hμ, exact hC1.symm hμ.2,
      exact hC1',
      rintros ⟨μ, hμ⟩,
      rw prod.ext_iff at hμ, simp at hμ, rw hn at hμ, simp at hμ,
      rw [sqrt_eq_zero, sub_eq_zero] at hμ, exact hC1.symm hμ.2,
      exact hC1', exact hao.symm,
    split, exact this,
    intros x hxoa, split,
    intro hx, have hxo := (@same_side_line_neq' r_squared o a _ x hx).1,
    rcases unit_wlog hxo.symm with ⟨y, hxy, hy⟩,
    have hoy := (@same_side_pt_neq r_squared o x y hxy).2.symm,
    rw [ang_symm, @ang_eq_same_side r_squared a o x y hxy, ang_symm] at hxoa,
    have hu : ∥f y -ᵥ f o∥ = 1,
      rw [vsub_eq_sub, ←f_sub, norm_equiv, prod.fst_sub, prod.snd_sub, hy, sqrt_one],
    have hoxa := @noncol23 (affine_plane ℝ) o a x
      (@same_side_line_noncol r_squared o a _ x hx hao.symm).2,
    have hyoa := @noncol12 (affine_plane ℝ) o y a (@col_noncol (affine_plane ℝ) o x y a
      hxy.2 hoxa hoy),
    have he₁ := backward hu hxoa hyoa,
    rw [hn0, zero_mul, add_zero] at he₁,
    replace he₁ : y.1 - o.1 = C / m,
      rw [←he₁, mul_comm, mul_div_cancel _ hm0],
    have he₂ : (y.2 - o.2)^2 = sqrt (1 - C^2)^2,
      rw [sq_sqrt hC1', ←hy, he₁, div_pow, hmn, div_one, add_comm, add_sub_cancel],
    cases eq_or_eq_neg_of_sq_eq_sq _ _ he₂ with he₂ he₂,
    have hy : (o + ((abs m) / m * C, sqrt (1 - C^2))) = y,
      rw prod.ext_iff, simp,
      rw [←he₂, div_mul_comm', ←he₁, hm'', mul_one,
        add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
      exact ⟨rfl, rfl⟩,
    rw ←hy at hxy, exact @same_side_pt_symm r_squared o x _ hxy,
    have hy : (o.1 + (abs m) / m * C, o.2 + -sqrt (1 - C^2)) = y,
      rw prod.ext_iff, simp,
      rw [←he₂, div_mul_comm', ←he₁, hm'', mul_one,
        add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
      exact ⟨rfl, rfl⟩,
    rw ←not_same_side_line at this, exfalso, apply this,
    apply same_side_line_trans, exact @line_in_lines (affine_plane ℝ) o a hao.symm,
    exact hx, rw hy, apply (@same_side_pt_line r_squared o x y hxy).2.2.2,
    exact @line_in_lines (affine_plane ℝ) o a hao.symm,
    split, exact @pt_left_in_line (affine_plane ℝ) o a,
    split, exact @noncol_in13 (affine_plane ℝ) o x a hoxa,
    exact @noncol_in23 (affine_plane ℝ) y o a hyoa,
    exact this.2.1, exact this.2.2,
    intro hx, have hxo := (@same_side_line_neq' r_squared o a _ x hx).1,
    rcases unit_wlog hxo.symm with ⟨y, hxy, hy⟩,
    have hoy := (@same_side_pt_neq r_squared o x y hxy).2.symm,
    rw [ang_symm, @ang_eq_same_side r_squared a o x y hxy, ang_symm] at hxoa,
    have hu : ∥f y -ᵥ f o∥ = 1,
      rw [vsub_eq_sub, ←f_sub, norm_equiv, prod.fst_sub, prod.snd_sub, hy, sqrt_one],
    have hoxa := @noncol23 (affine_plane ℝ) o a x
      (@same_side_line_noncol r_squared o a _ x hx hao.symm).2,
    have hyoa := @noncol12 (affine_plane ℝ) o y a (@col_noncol (affine_plane ℝ) o x y a
      hxy.2 hoxa hoy),
    have he₁ := backward hu hxoa hyoa,
    rw [hn0, zero_mul, add_zero] at he₁,
    replace he₁ : y.1 - o.1 = C / m,
      rw [←he₁, mul_comm, mul_div_cancel _ hm0],
    have he₂ : (y.2 - o.2)^2 = sqrt (1 - C^2)^2,
      rw [sq_sqrt hC1', ←hy, he₁, div_pow, hmn, div_one, add_comm, add_sub_cancel],
    cases eq_or_eq_neg_of_sq_eq_sq _ _ he₂ with he₂ he₂,
    have hy : (o.1 + (abs m) / m * C, o.2 + sqrt (1 - C^2)) = y,
      rw prod.ext_iff, simp,
      rw [←he₂, div_mul_comm', ←he₁, hm'', mul_one,
        add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
      exact ⟨rfl, rfl⟩,
    rw ←not_same_side_line at this, exfalso, apply this,
    apply same_side_line_trans, exact @line_in_lines (affine_plane ℝ) o a hao.symm,
    rw hy, apply same_side_line_symm, apply (@same_side_pt_line r_squared o x y hxy).2.2.2,
    exact @line_in_lines (affine_plane ℝ) o a hao.symm,
    split, exact @pt_left_in_line (affine_plane ℝ) o a,
    split, exact @noncol_in13 (affine_plane ℝ) o x a hoxa,
    exact @noncol_in23 (affine_plane ℝ) y o a hyoa,
    apply same_side_line_symm, exact hx,
    exact this.2.1, exact this.2.2,
    have hy : (o + ((abs m) / m * C, -sqrt (1 - C^2))) = y,
      rw prod.ext_iff, simp,
      rw [←he₂, div_mul_comm', ←he₁, hm'', mul_one,
        add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
      exact ⟨rfl, rfl⟩,
    rw ←hy at hxy, exact @same_side_pt_symm r_squared o x _ hxy,
  linarith,
  rw [←f_sub, norm_eq_zero, f_zero, sub_eq_zero] at hf, exact absurd hf hao,
  have hao' : a.2 - o.2 ≠ 0,
    intro hf, rw sub_eq_zero at hf,
    rw [hf, sub_self, zero_div] at hn, exact hn0 hn,
  set x₁ := sqrt ((1 - m^2) * (1 - C^2)) + m * C with hx₁,
  set y₁ := -(abs n / n) * m * sqrt (1 - C^2) + n * C with hy₁,
  set x₂ := -sqrt ((1 - m^2) * (1 - C^2)) + m * C with hx₂,
  set y₂ := (abs n / n) * m * sqrt (1 - C^2) + n * C with hy₂,
  have h₁ : @noncol (affine_plane ℝ) (o.1 + x₁, o.2 + y₁) o a,
    intro hf, have := @col_in23 (affine_plane ℝ) _ _ _ hf hao.symm,
    rw between.line_rw at this,
    cases this with μ hμ, rw prod.ext_iff at hμ, simp at hμ,
    have hf : x₁ * (a.2 - o.2) = y₁ * (a.1 - o.1),
      rw [hμ.1, hμ.2], ring,
    rw [hx₁, hy₁, add_mul, add_mul] at hf,
    have : m * C * (a.2 - o.2) = n * C * (a.1 - o.1),
      rw [hm, hn], ring,
    rw [this, add_left_inj, ←hmn', sqrt_mul, sqrt_sq_eq_abs] at hf,
    replace hf : abs n * sqrt (1 - C^2) * (a.2 - o.2)
      = abs n * sqrt (1 - C^2) * (-(m / n) * (a.1 - o.1)),
      rw hf, ring,
    rw [mul_right_inj', hmn'', ←mul_left_inj' hao', mul_assoc,
      mul_comm (a.1 - o.1) _, ←mul_assoc, ←neg_mul_eq_neg_mul, div_mul_cancel, ←sq,
      ←neg_mul_eq_neg_mul, ←sq, ←add_eq_zero_iff_eq_neg] at hf,
    exact hao' (sq_add_sq_zero hf).1, exact hao',
    apply mul_ne_zero, exact λhf, hn0 (abs_eq_zero.1 hf),
    exact (sqrt_ne_zero hC1').2 (sub_ne_zero.2 hC1.symm),
    exact sq_nonneg n, exact hao.symm,
  have h₂ : @noncol (affine_plane ℝ) (o.1 + x₂, o.2 + y₂) o a,
    intro hf, have := @col_in23 (affine_plane ℝ) _ _ _ hf hao.symm,
    rw between.line_rw at this,
    cases this with μ hμ, rw prod.ext_iff at hμ, simp at hμ,
    have hf : x₂ * (a.2 - o.2) = y₂ * (a.1 - o.1),
      rw [hμ.1, hμ.2], ring,
    rw [hx₂, hy₂, add_mul, add_mul] at hf,
    have : m * C * (a.2 - o.2) = n * C * (a.1 - o.1),
      rw [hm, hn], ring,
    rw [this, add_left_inj, ←hmn', sqrt_mul, sqrt_sq_eq_abs, neg_mul_eq_neg_mul_symm] at hf,
    replace hf : abs n * sqrt (1 - C^2) * (a.2 - o.2)
      = abs n * sqrt (1 - C^2) * (-(m / n) * (a.1 - o.1)),
      rw [eq_neg_of_eq_neg hf.symm], ring,
    rw [mul_right_inj', hmn'', ←mul_left_inj' hao', mul_assoc,
      mul_comm (a.1 - o.1) _, ←mul_assoc, ←neg_mul_eq_neg_mul, div_mul_cancel, ←sq,
      ←neg_mul_eq_neg_mul, ←sq, ←add_eq_zero_iff_eq_neg] at hf,
    exact hao' (sq_add_sq_zero hf).1, exact hao',
    apply mul_ne_zero, exact λhf, hn0 (abs_eq_zero.1 hf),
    exact (sqrt_ne_zero hC1').2 (sub_ne_zero.2 hC1.symm),
    exact sq_nonneg n, exact hao.symm,
  use [(o.1 + x₁, o.2 + y₁), (o.1 + x₂, o.2 + y₂)],
  split, apply forward',
  rw [vsub_eq_sub, ←f_sub, norm_equiv], simp,
  rw [unit1 hn0 hC1' hmn hx₁ hy₁, sqrt_one],
  simp, exact backward1 hn0 hmn hx₁ hy₁,
  exact h₁,
  split, apply forward',
  rw [vsub_eq_sub, ←f_sub, norm_equiv], simp,
  rw [unit2 hn0 hC1' hmn hx₂ hy₂, sqrt_one],
  simp, exact backward2 hn0 hmn hx₂ hy₂,
  exact h₂,
  have : @diff_side_line r_squared (@line (affine_plane ℝ) o a)
    (o.fst + x₁, o.snd + y₁) (o.fst + x₂, o.snd + y₂),
  use (o.1 + (x₁ + x₂) / 2, o.2 + (y₁ + y₂) / 2),
  have hx : (x₁ + x₂) / 2 = m * C,
    rw [hx₁, hx₂, add_comm _ (m * C), add_assoc, ←add_assoc _ _ (m * C),
      add_neg_self, zero_add], simp,
  have hy : (y₁ + y₂) / 2 = n * C,
    rw [hy₁, hy₂, add_comm _ (n * C), add_assoc, ←add_assoc _ _ (n * C),
      add_comm _ (abs n / n * m * sqrt (1 - C^2)), ←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul,
      add_neg_self, zero_add], simp,
  split,
  rw [between.line_rw, hx, hy, hm, hn],
  use C / ∥f a - f o∥,
  rw prod.ext_iff, simp, rw [div_mul_comm', div_mul_comm' _ _ C], exact ⟨rfl, rfl⟩,
  exact hao.symm,
  left, simp, split,
  intro hf, rw prod.ext_iff at hf, simp at hf,
  rw [hx, hy] at hf, rw hf.1 at hx₂, rw hf.2 at hy₂,
  rw self_eq_add_left at hx₂ hy₂,
  rw [neg_eq_zero, sqrt_eq_zero, mul_eq_zero] at hx₂,
  rw [mul_eq_zero, mul_eq_zero, sqrt_eq_zero, div_eq_zero_iff, abs_eq_zero, or_self] at hy₂,
  cases hx₂, rw sub_eq_zero.1 hx₂ at hmn, rw add_right_eq_self at hmn,
  exact hn0 (pow_eq_zero hmn), exact hC1 (sub_eq_zero.1 hx₂).symm,
  exact hC1',
  apply mul_nonneg, rw sub_nonneg, exact hm1,
  exact hC1',
  use 1, simp, ring_nf, exact ⟨rfl, rfl⟩,
  exact ⟨@noncol_in23 (affine_plane ℝ) _ o a h₁, @noncol_in23 (affine_plane ℝ) _ o a h₂⟩,
  split, exact this,
  intros x hxoa, split,
  intro hx, have hxo := (@same_side_line_neq' r_squared o a _ x hx).1,
  rcases unit_wlog hxo.symm with ⟨y, hxy, hy⟩,
  have hoy := (@same_side_pt_neq r_squared o x y hxy).2.symm,
  rw [ang_symm, @ang_eq_same_side r_squared a o x y hxy, ang_symm] at hxoa,
  have hu : ∥f y -ᵥ f o∥ = 1,
    rw [vsub_eq_sub, ←f_sub, norm_equiv, prod.fst_sub, prod.snd_sub, hy, sqrt_one],
  have hoxa := @noncol23 (affine_plane ℝ) o a x
    (@same_side_line_noncol r_squared o a _ x hx hao.symm).2,
  have hyoa := @noncol12 (affine_plane ℝ) o y a (@col_noncol (affine_plane ℝ) o x y a
    hxy.2 hoxa hoy),
  have he₁ := backward hu hxoa hyoa,
  cases forward hn0 hmn hy he₁ with he₂ he₂,
  have hy : (o + (x₁, y₁)) = y,
      rw prod.ext_iff, simp,
      rw [hx₁, hy₁, ←he₂.1, ←he₂.2, add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
      exact ⟨rfl, rfl⟩,
    rw ←hy at hxy, exact @same_side_pt_symm r_squared o x _ hxy,
  have hy : (o.1 + x₂, o.2 + y₂) = y,
    rw prod.ext_iff, simp,
    rw [hx₂, hy₂, ←he₂.1, ←he₂.2, add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
    exact ⟨rfl, rfl⟩,
  rw ←not_same_side_line at this, exfalso, apply this,
  apply same_side_line_trans, exact @line_in_lines (affine_plane ℝ) o a hao.symm,
  exact hx, rw hy, apply (@same_side_pt_line r_squared o x y hxy).2.2.2,
  exact @line_in_lines (affine_plane ℝ) o a hao.symm,
  split, exact @pt_left_in_line (affine_plane ℝ) o a,
  split, exact @noncol_in13 (affine_plane ℝ) o x a hoxa,
  exact @noncol_in23 (affine_plane ℝ) y o a hyoa,
  exact this.2.1, exact this.2.2,
  intro hx, have hxo := (@same_side_line_neq' r_squared o a _ x hx).1,
  rcases unit_wlog hxo.symm with ⟨y, hxy, hy⟩,
  have hoy := (@same_side_pt_neq r_squared o x y hxy).2.symm,
  rw [ang_symm, @ang_eq_same_side r_squared a o x y hxy, ang_symm] at hxoa,
  have hu : ∥f y -ᵥ f o∥ = 1,
    rw [vsub_eq_sub, ←f_sub, norm_equiv, prod.fst_sub, prod.snd_sub, hy, sqrt_one],
  have hoxa := @noncol23 (affine_plane ℝ) o a x
    (@same_side_line_noncol r_squared o a _ x hx hao.symm).2,
  have hyoa := @noncol12 (affine_plane ℝ) o y a (@col_noncol (affine_plane ℝ) o x y a
    hxy.2 hoxa hoy),
  have he₁ := backward hu hxoa hyoa,
  cases forward hn0 hmn hy he₁ with he₂ he₂,
  have hy : (o.1 + x₁, o.2 + y₁) = y,
    rw prod.ext_iff, simp,
    rw [hx₁, hy₁, ←he₂.1, ←he₂.2, add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
    exact ⟨rfl, rfl⟩,
  rw ←not_same_side_line at this, exfalso, apply this,
  apply same_side_line_trans, exact @line_in_lines (affine_plane ℝ) o a hao.symm,
  rw hy,apply same_side_line_symm,
  apply (@same_side_pt_line r_squared o x y hxy).2.2.2,
  exact @line_in_lines (affine_plane ℝ) o a hao.symm,
  split, exact @pt_left_in_line (affine_plane ℝ) o a,
  split, exact @noncol_in13 (affine_plane ℝ) o x a hoxa,
  exact @noncol_in23 (affine_plane ℝ) y o a hyoa,
  apply same_side_line_symm, exact hx,
  exact this.2.1, exact this.2.2,
  have hy : (o.1 + x₂, o.2 + y₂) = y,
    rw prod.ext_iff, simp,
    rw [hx₂, hy₂, ←he₂.1, ←he₂.2, add_comm, sub_add_cancel, add_comm o.2 _, sub_add_cancel],
    exact ⟨rfl, rfl⟩,
  rw hy, apply same_side_pt_symm, exact hxy
end

end ang

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
    apply (sqrt_inj _ _).1 _,
    nlinarith, nlinarith,
    rw [seg.between_cal habc, seg.between_cal hdef, habde, hbcef]
  end,
  ang_congr := ang_congr,
  C4 :=
  begin
    intros α o a p hα hoa hp,
    rcases ang.extend hα hoa.symm with ⟨b, c, hb, hc, hbc, hu⟩,
    rcases (@plane_separation r_squared (@line (affine_plane ℝ) o a) b p hbc.2.1 hp).1 with h | h,
    use b,
    split, exact hb, split, exact h,
    intros x hbx hx,
    left, exact (hu x hx).1 hbx,
    use c,
    split, exact hc, split,
    apply diff_side_line_cancel,
    exact @line_in_lines (affine_plane ℝ) o a hoa,
    apply diff_side_line_symm, exact hbc,
    exact h,
    intros x hcx hx,
    left, exact (hu x hx).2 hcx
  end,
  C5 :=
  begin
    split,
    intros α β γ hαβ hαγ,
    rcases hαβ with ⟨a, b, c, d, hα, hβ, h₁, h₂⟩,
    rcases hαγ with ⟨a', b', e, f, hα', hγ, h₃, h₄⟩,
    use [c, d, e, f],
    split, exact hβ, split, exact hγ,
    have he := hα.symm.trans hα',
      split, rw [←h₁, ←h₃], split; contrapose!;
      intros h hf;
      have := (@ang_nontrivial_iff_noncol r_squared _ _ _).2 h,
      rw [←he, ang_nontrivial_iff_noncol] at this, exact this hf,
      rw [he, ang_nontrivial_iff_noncol] at this, exact this hf,
    rw ←not_iff_not at h₁ h₃,
    intro hcd,
    have hab := h₁.2 hcd,
    have ha'b' := (@ang_nontrivial_iff_noncol r_squared _ _ _).2 hab,
    rw [he, ang_nontrivial_iff_noncol] at ha'b',
    rw three_pt_ang_eq_iff at he, 
    rw [←h₂ hab, ←h₄ ha'b'], cases he.2,
    rw [ang_eq_same_side_pt b h.1, euclidean_geometry.angle_comm,
      ang_eq_same_side_pt a' h.2, euclidean_geometry.angle_comm],
    rw [ang_eq_same_side_pt b h.1, euclidean_geometry.angle_comm,
      ang_eq_same_side_pt b' h.2, euclidean_geometry.angle_comm],
    exact hab,
    intro α, rcases @ang_three_pt r_squared α with ⟨a, b, hα⟩,
    use [a, b, a, b], rw ←hα, simp
  end,
  C6 := sorry,
  ..r_squared }


example {p q r : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := not_iff_not.symm

end r_squared

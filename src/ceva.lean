import geometry.euclidean.triangle
import tactic

open real
open inner_product_geometry
open euclidean_geometry

open_locale euclidean_geometry real_inner_product_space real
open_locale classical

variables {V : Type*} [inner_product_space ℝ V]
variables {P : Type*} [metric_space P] [normed_add_torsor V P]
include V

-- someone pls give it a better name lol
lemma trident_model {a b c : P} (o : P) {k : ℝ} (hk : k < 0) (habc : c -ᵥ b = k • (a -ᵥ b)) : 
b -ᵥ o = (k / (k - 1)) • (a -ᵥ o) - (1 / (k - 1)) • (c -ᵥ o) :=
begin
  have : -(b -ᵥ o) = k • (a -ᵥ o) - k • (b -ᵥ o) - (c -ᵥ o),
    have : (c -ᵥ o) - (b -ᵥ o) - (c -ᵥ o) = k • (a -ᵥ o) - k • (b -ᵥ o) - (c -ᵥ o),
      have habc : (c -ᵥ o) - (b -ᵥ o) = k • (a -ᵥ o) - k • (b -ᵥ o),
        rw ←smul_sub, simpa,
      rw habc,
    rw [sub_right_comm, sub_self, zero_sub] at this,
    rw this,

  calc b -ᵥ o = ((k - 1) / (k - 1)) • (b -ᵥ o)
                : by rw [div_self (show k - 1 ≠ 0, by linarith), one_smul]
          ... = (1 / (k - 1)) • (k - 1) • (b -ᵥ o)
                : by rw [smul_smul, div_mul_eq_mul_div, one_mul]
          ... = (1 / (k - 1)) • (k • (b -ᵥ o) - (b -ᵥ o))
                : by rw [sub_smul, one_smul]
          ... = (1 / (k - 1)) • (k • (b -ᵥ o) + -(b -ᵥ o))
                : by rw ←tactic.ring.add_neg_eq_sub _ (b -ᵥ o)
          ... = (1 / (k - 1)) • (k • (b -ᵥ o) + (k • (a -ᵥ o) - k • (b -ᵥ o) - (c -ᵥ o)))
                : by rw this
          ... = (1 / (k - 1)) • (k • (a -ᵥ o) - (c -ᵥ o))
                : by rw [add_sub, add_comm, sub_add, sub_self, sub_zero]
          ... = (k / (k - 1)) • (a -ᵥ o) - (1 / (k - 1)) • (c -ᵥ o)
                : by rw [smul_sub, smul_smul, div_mul_eq_mul_div, one_mul]
end

lemma linear_ind {a b c : P} {m₁ n₁ m₂ n₂ : ℝ}
(habc : ∠ a b c < π ∧ ∠ a b c > 0) (h0 : a -ᵥ b ≠ (0 : V) ∧ c -ᵥ b ≠ (0 : V)) :
m₁ • (a -ᵥ b) + n₁ • (c -ᵥ b) = m₂ • (a -ᵥ b) + n₂ • (c -ᵥ b) → m₁ = m₂ ∧ n₁ = n₂ :=
begin
  intro hmn,
  replace hmn : m₁ • (a -ᵥ b) - m₂ • (a -ᵥ b) = n₂ • (c -ᵥ b) - n₁ • (c -ᵥ b),
    calc m₁ • (a -ᵥ b) - m₂ • (a -ᵥ b)
       = m₁ • (a -ᵥ b) + n₁ • (c -ᵥ b) - n₁ • (c -ᵥ b) - m₂ • (a -ᵥ b)
       : by simp
   ... = m₂ • (a -ᵥ b) + n₂ • (c -ᵥ b) - n₁ • (c -ᵥ b) - m₂ • (a -ᵥ b)
       : by rw hmn
   ... = n₂ • (c -ᵥ b) - n₁ • (c -ᵥ b)
       : by rw [←add_sub, add_comm, ←add_sub, sub_self, add_zero],
  rw ←sub_smul at hmn, rw ←sub_smul at hmn,
  by_contradiction hf,
  cases (not_and_distrib.mp hf) with hm hn,
  { have key : a -ᵥ b = ((n₂ - n₁) / (m₁ - m₂)) • (c -ᵥ b),
      calc a -ᵥ b = (1 / (m₁ - m₂)) • ((m₁ - m₂) • (a -ᵥ b))
                  : by rw [smul_smul, div_mul_cancel _ (sub_ne_zero.mpr hm), one_smul]
              ... = (1 / (m₁ - m₂)) • ((n₂ - n₁) • (c -ᵥ b))
                  : by rw hmn
              ... = ((n₂ - n₁) / (m₁ - m₂)) • (c -ᵥ b)
                  : by rw [smul_smul, div_mul_eq_mul_div, one_mul],
    by_cases (n₂ - n₁) / (m₁ - m₂) = 0,
    rw [key, h] at h0, simp at h0, exact h0,
    cases ((ne.symm h).lt_or_lt),
    have : ∠ a b c = 0,
      rw euclidean_geometry.angle_comm,
      apply angle_eq_zero_iff.mpr,
      exact ⟨h0.2, (n₂ - n₁) / (m₁ - m₂), (by linarith), (by rw key)⟩,
    linarith,
    have : ∠ a b c = π,
      rw euclidean_geometry.angle_comm,
      apply angle_eq_pi_iff.mpr,
      exact ⟨h0.2, (n₂ - n₁) / (m₁ - m₂), (by linarith), (by rw key)⟩,
    linarith },
  -- this argument is almost the same so I collapse it
  { have key : c -ᵥ b = ((m₁ - m₂) / (n₂ - n₁)) • (a -ᵥ b),
      calc c -ᵥ b = (1 / (n₂ - n₁)) • ((n₂ - n₁) • (c -ᵥ b))
                  : by rw [smul_smul, div_mul_cancel _ (sub_ne_zero.mpr (ne.symm hn)), one_smul]
              ... = (1 / (n₂ - n₁)) • ((m₁ - m₂) • (a -ᵥ b))
                  : by rw hmn
              ... = ((m₁ - m₂) / (n₂ - n₁)) • (a -ᵥ b)
                  : by rw [smul_smul, div_mul_eq_mul_div, one_mul],
    by_cases (m₁ - m₂) / (n₂ - n₁) = 0,
    rw [key, h] at h0, simp at h0, exact h0,
    cases ((ne.symm h).lt_or_lt),
    have : ∠ a b c = 0,
      apply angle_eq_zero_iff.mpr,
      exact ⟨h0.1, (m₁ - m₂) / (n₂ - n₁), (by linarith), (by rw key)⟩,
    linarith,
    have : ∠ a b c = π,
      apply angle_eq_pi_iff.mpr,
      exact ⟨h0.1, (m₁ - m₂) / (n₂ - n₁), (by linarith), (by rw key)⟩,
    linarith }
end

lemma collinear_1 {a b c : P} {k : ℝ} (hcba : a -ᵥ b = k • (c -ᵥ b)) (hk : k ≠ 1) :
c -ᵥ b = (1 / (1 - k)) • (c -ᵥ a) ∧ a -ᵥ b = (k / (1 - k)) • (c -ᵥ a) :=
begin
  have hk' : 1 - k ≠ 0,
    intro hf,
    have : 1 = 0 + k, from eq_add_of_sub_eq hf,
    exact hk (by rw [this, zero_add]),
  have : (1 / (1 - k)) • (c -ᵥ a) = c -ᵥ b,
   calc (1 / (1 - k)) • (c -ᵥ a)
      = (1 / (1 - k)) • ((c -ᵥ b) - (a -ᵥ b))
      : by simp
  ... = (1 / (1 - k)) • ((c -ᵥ b) - k • (c -ᵥ b))
      : by rw hcba
  ... = (1 / (1 - k) * (1 - k)) • (c -ᵥ b)
      : by rw [←smul_smul, sub_smul, one_smul]
  ... = (1 / (1 - k) * ((1 - k))) • (c -ᵥ b)
      : by simp
  ... = c -ᵥ b
      : by rw [div_mul_cancel _ hk', one_smul],
  split,
  rw this,
  rw [hcba, ←this, smul_smul, ←mul_div_assoc, mul_one]
end

lemma collinear_2 {a b c : P} (habc : ∠ a b c = π) :
∃ k : ℝ, a -ᵥ b = k • (a -ᵥ c) :=
begin
  obtain ⟨-, μ, _, habc⟩ := angle_eq_pi_iff.mp habc,
  use 1 / (1 - μ),
  calc a -ᵥ b = ((1 - μ) / (1 - μ)) • (a -ᵥ b)
              : by rw [div_self (show 1 - μ ≠ 0, by linarith), one_smul]
          ... = (1 / (1 - μ)) • ((1 - μ) • (a -ᵥ b))
              : by rw [smul_smul, div_mul_eq_mul_div, one_mul]
          ... = (1 / (1 - μ)) • ((a -ᵥ b) - μ • (a -ᵥ b))
              : by rw [sub_smul, one_smul]
          ... = (1 / (1 - μ)) • ((a -ᵥ b) - (c -ᵥ b))
              : by rw habc
          ... = (1 / (1 - μ)) • (a -ᵥ c)
              : by simp
end

lemma collinear_3 {a b c : P} (habc : ∠ a b c = π) :
∃ k : ℝ, a -ᵥ b = k • (c -ᵥ a) :=
begin
  obtain ⟨k, habc⟩ := collinear_2 habc,
  use -k,
  rw [habc, neg_smul, ←smul_neg],
  simp
end

lemma dist_pro_eq_abs_vec_pro {a b c d : P} {k : ℝ}
(hvec : a -ᵥ b = k • (c -ᵥ d)) (h0 : c -ᵥ d ≠ (0 : V)) :
dist a b/dist c d = abs k :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V],
  rw [hvec, norm_smul, mul_div_cancel],
  exact rfl,
  intro h, exact h0 (norm_eq_zero.mp h)
end

/- habc, hco0, hab0, hbc0, hac0 are not really necessary for the theorem,
   but it is so trivial because there won't be a triangle otherwise -/
theorem ceva {a b c d e f o : P}
(habc : ∠ a b c < π ∧ ∠ a b c > 0) (hco0 : c -ᵥ o ≠ (0 : V))
(hab0 : a -ᵥ b ≠ (0 : V)) (hbc0 : b -ᵥ c ≠ (0 : V)) (hac0 : a -ᵥ c ≠ (0 : V)) 
(haec' : ∠ a e c = π) (hbfa' : ∠ b f a = π) (hcdb' : ∠ c d b = π)
(haod : ∠ a o d = π) (hboe : ∠ b o e = π) :
∠ c o f = π → (dist a f/dist b f) * (dist b d/dist c d) * (dist c e/dist a e) = 1  :=
begin
  have h0 : (a -ᵥ b ≠ (0 : V) ∧ c -ᵥ b ≠ (0 : V)),
    by_contradiction hf,
    cases (not_and_distrib.mp hf) with h0 h0;
    push_neg at h0,
    { rw (eq_of_vsub_eq_zero h0) at hbfa',
      have := angle_eq_zero_of_angle_eq_pi_left hbfa',
      have := angle_eq_right f b,
      linarith },
    { rw (eq_of_vsub_eq_zero h0) at hcdb',
      have := angle_eq_zero_of_angle_eq_pi_left hcdb',
      have := angle_eq_right d b,
      linarith },
  obtain ⟨hbf0, μ₁, _, hbfa⟩ := angle_eq_pi_iff.mp hbfa',
  obtain ⟨hcd0, μ₂, _, hcdb⟩ := angle_eq_pi_iff.mp hcdb',
  obtain ⟨hae0, μ₃, _, haec⟩ := angle_eq_pi_iff.mp haec',
  obtain ⟨α, haod⟩ := collinear_2 haod,
  obtain ⟨β, hboe⟩ := collinear_2 hboe,
  have hbd := (collinear_1 hcdb (by linarith)).2,
  have hco1 : c -ᵥ o = (α - 1) • (a -ᵥ b) + ((α * μ₂) / (1 - μ₂) + 1) • (c -ᵥ b),
    calc c -ᵥ o
       = c -ᵥ b - (a -ᵥ b) + (a -ᵥ o)
       : by simp
   ... = c -ᵥ b - (a -ᵥ b) + α • (a -ᵥ d)
       : by rw haod
   ... = c -ᵥ b - (a -ᵥ b) + α • (a -ᵥ b + (b -ᵥ d))
       : by simp
   ... = (c -ᵥ b) - (a -ᵥ b) + α • (a -ᵥ b) + α • (μ₂ / (1 - μ₂)) • (c -ᵥ b)
       : by rw [hbd, smul_add, ←add_assoc]
   ... = α • (a -ᵥ b) - (a -ᵥ b) + (c -ᵥ b) + (α • (μ₂ / (1 - μ₂)) • (c -ᵥ b))
       : by rw [add_comm (c -ᵥ b - (a -ᵥ b)) _, sub_eq_add_neg, add_comm (c -ᵥ b), ←add_assoc, ←sub_eq_add_neg]
   ... = (α - 1) • (a -ᵥ b) + ((α * μ₂) / (1 - μ₂) + 1) • (c -ᵥ b)
       : by rw [sub_smul, add_smul, one_smul, one_smul, add_assoc, smul_smul, mul_div_assoc, add_comm  (c -ᵥ b) _],
  have hae := (collinear_1 haec (by linarith)).1,
  have hco2 : c -ᵥ o = (-β + (β / (1 - μ₃))) • (a -ᵥ b) + (-β / (1 - μ₃) + 1) • (c -ᵥ b),
    calc c -ᵥ o
       = c -ᵥ b + (b -ᵥ o)
       : by simp
   ... = c -ᵥ b + β • (b -ᵥ e)
       : by rw hboe
   ... = c -ᵥ b + β • (b -ᵥ a + (a -ᵥ e))
       : by simp
   ... = c -ᵥ b + β • (b -ᵥ a + (1 / (1 - μ₃)) • (a -ᵥ c))
       : by rw hae
   ... = c -ᵥ b + (β • (b -ᵥ a) + (β / (1 - μ₃)) • (a -ᵥ c))
       : by rw [smul_add, smul_smul, ←mul_div_assoc, mul_one]
   ... = c -ᵥ b + (β • (-(a -ᵥ b)) + (β / (1 - μ₃)) • (a -ᵥ b + -(c -ᵥ b)))
       : by simp
   ... = c -ᵥ b + ((-β) • (a -ᵥ b) + (β / (1 - μ₃)) • (a -ᵥ b) + (β / (1 - μ₃)) • -(c -ᵥ b))
       : by rw [←neg_one_mul, mul_comm, ←smul_smul, neg_one_smul, smul_add, add_assoc]
   ... = c -ᵥ b + ((-β) • (a -ᵥ b) + (β / (1 - μ₃)) • (a -ᵥ b) + ((-β) / (1 - μ₃)) • (c -ᵥ b))
       : by rw [←(neg_one_smul ℝ (c -ᵥ b)), smul_smul, mul_comm, ←mul_div_assoc, neg_one_mul]
   ... = (-β + (β / (1 - μ₃))) • (a -ᵥ b) + (-β / (1 - μ₃) + 1) • (c -ᵥ b)
       : by rw [add_smul, add_smul, one_smul, add_comm, ←add_assoc],
  have cal_β : -β + β / (1 - μ₃) = β * μ₃ / (1 - μ₃),
    rw [add_div', mul_sub, (norm_num.mul_neg_pos β μ₃ (β * μ₃) rfl), sub_neg_eq_add], simp, linarith,
  rw cal_β at hco2,
  cases (linear_ind habc h0 (hco2.symm.trans hco1)) with h₁ h₂,
  norm_num at h₂,
  rw [mul_comm, ←neg_mul_neg, mul_div_assoc, h₂, ←mul_div_assoc, mul_comm α _, ←mul_assoc] at h₁,
  replace h₁ :  μ₂ * μ₃ * α = -(α - 1) * (1 - μ₂),
    calc μ₂ * μ₃ * α
       = (1 - μ₂) * (-(-μ₃ * μ₂ * α) / (1 - μ₂))
       : by {rw [←mul_div_assoc, mul_comm (1 - μ₂) _, mul_div_assoc, div_self (show 1 - μ₂ ≠ 0, by linarith), mul_one], ring}
   ... = -(α - 1) * (1 - μ₂)
       : by rw [←h₁, neg_div', mul_comm],
  have pos : μ₂ * μ₃ - μ₂ + 1 > 0,
    have : μ₂ * μ₃ > 0, from mul_pos_of_neg_of_neg (by linarith) (by linarith), linarith,
  have hα : α = (1 - μ₂) / (μ₂ * μ₃ - μ₂ + 1),
    calc α = (1 / (μ₂ * μ₃ - μ₂ + 1)) * ((μ₂ * μ₃) * α - (μ₂ - 1) * α)
           : by rw [←sub_mul, ←sub_add, ←mul_assoc, div_mul_cancel _ (show μ₂ * μ₃ - μ₂ + 1 ≠ 0, by linarith), one_mul]
       ... = (1 / (μ₂ * μ₃ - μ₂ + 1)) * (α * -(1 - μ₂) + (1 - μ₂)  + (1 - μ₂) * α)
           : by {rw [h₁, neg_mul_comm, sub_mul, one_mul, sub_neg_eq_add], ring}
       ... = (1 / (μ₂ * μ₃ - μ₂ + 1)) * ((1 - μ₂) + ((1 - μ₂) * α + -(1 - μ₂) * α))
           : by rw [add_comm (α * -(1 - μ₂)), mul_comm α, add_assoc, add_comm (-(1 - μ₂) * α) _]
       ... = (1 / (μ₂ * μ₃ - μ₂ + 1)) * (1 - μ₂)
           : by rw [norm_num.mul_neg_pos (1 - μ₂) _ _ rfl, tactic.ring.add_neg_eq_sub, sub_self, add_zero]
       ... = (1 - μ₂) / (μ₂ * μ₃ - μ₂ + 1)
           : by rw [div_mul_eq_mul_div, one_mul],
  have hco : c -ᵥ o = ((-μ₂ * μ₃) / (μ₂ * μ₃ - μ₂ + 1)) • (a -ᵥ b)
                      + ((μ₂ * μ₃ + 1) / (μ₂ * μ₃ - μ₂ + 1)) • (c -ᵥ b),
    have cal1 : (1 - μ₂) / (μ₂ * μ₃ - μ₂ + 1) - 1 = (-μ₂ * μ₃) / (μ₂ * μ₃ - μ₂ + 1),
      rw [div_sub', mul_one, sub_sub, ←add_assoc, add_comm μ₂ _, sub_add, sub_self, sub_zero,
          ←sub_sub, sub_right_comm, sub_self, zero_sub, neg_mul_eq_neg_mul], linarith,
    have cal2 : (1 - μ₂) / (μ₂ * μ₃ - μ₂ + 1) * μ₂ / (1 - μ₂) + 1 = (μ₂ * μ₃ + 1) / (μ₂ * μ₃ - μ₂ + 1),
      rw [mul_div_assoc, mul_comm, ←mul_div_assoc, div_mul_cancel _ (show 1 - μ₂ ≠ 0, by linarith),
          div_add', one_mul, ←add_assoc, add_comm μ₂ _, sub_add, sub_self, sub_zero], linarith,
    rw [hco1, hα, cal1, cal2],
  have hfc : f -ᵥ c = ((-1 : ℝ) / (μ₁ - 1)) • (a -ᵥ b) + (-1 : ℝ) • (c -ᵥ b),
    calc f -ᵥ c
       = (μ₁ / (μ₁ - 1)) • (b -ᵥ c) - ((1 : ℝ ) / (μ₁ - 1)) • (a -ᵥ c)
       : trident_model c (by linarith) hbfa
   ... = (μ₁ / (μ₁ - 1)) • (-(c -ᵥ b)) - (1 / (μ₁ - 1)) • (a -ᵥ b - (c -ᵥ b))
       : by simp
   ... = (-μ₁ / (μ₁ - 1)) • (c -ᵥ b) + (-1 / (μ₁ - 1)) • (a -ᵥ b - (c -ᵥ b))
       : by rw [←neg_one_smul ℝ (c -ᵥ b), smul_smul, mul_comm, ←mul_div_assoc, neg_one_mul,
                neg_div _ (1 : ℝ), neg_smul, tactic.ring.add_neg_eq_sub _ _]
   ... = (-1 / (μ₁ - 1)) • (a -ᵥ b) + (-μ₁ / (μ₁ - 1)) • (c -ᵥ b) - (-1 / (μ₁ - 1)) • (c -ᵥ b)
       : by rw [smul_sub, add_sub, add_comm]
   ... = ((-1 : ℝ) / (μ₁ - 1)) • (a -ᵥ b) + (-1 : ℝ) • (c -ᵥ b)
       : by rw [←add_sub, ←sub_smul, neg_div _ (1 : ℝ), sub_neg_eq_add, div_add' _ _ _(show μ₁ - 1 ≠ 0, by linarith),
                div_mul_cancel _ (show μ₁ - 1 ≠ 0, by linarith), ←neg_sub, add_comm _ (1 : ℝ),
                tactic.ring.add_neg_eq_sub, div_neg (1 - μ₁), div_self (show 1 - μ₁ ≠ 0, by linarith)],
  intro hcof',
  suffices : μ₁ * μ₂ * μ₃ = -1,
    rw [(dist_pro_eq_abs_vec_pro hbfa hbf0), (dist_pro_eq_abs_vec_pro hcdb hcd0),
        (dist_pro_eq_abs_vec_pro haec hae0), ←abs_mul, ←abs_mul, this], simp,
  cases collinear_3 hcof' with k hcof,
  rw [hfc, hco, smul_add, smul_smul, smul_smul] at hcof,
  cases (linear_ind habc h0 hcof) with h₁ h₂,
  rw [(show k = -(k * -1), by simp), ←h₂, ←neg_div, div_mul_eq_mul_div, neg_div, neg_mul_neg] at h₁,
  have cancel_denom : ∀ a b c : ℝ, c ≠ 0 → a / c = b / c → a = b,
    intros a b c hc h,
    rw [←mul_div_cancel a hc, mul_comm, mul_div_assoc, h, ←mul_div_assoc, mul_comm, mul_div_cancel _ hc],
  have := cancel_denom _ _ _ (by linarith) h₁,
  calc μ₁ * μ₂ * μ₃
     = -(μ₂ * μ₃ - μ₁ * μ₂ * μ₃) + μ₂ * μ₃
     : by rw [add_comm, tactic.ring.add_neg_eq_sub, ←sub_add, sub_self, zero_add]
 ... = ((1 - μ₁) * (-μ₂ * μ₃)) + μ₂ * μ₃
     : by rw [norm_num.mul_neg_pos _ _ _ rfl, sub_mul, one_mul, neg_sub, norm_num.mul_pos_neg _ _ _ rfl,
              sub_neg_eq_add, add_comm (-(μ₂ * μ₃)) _, tactic.ring.add_neg_eq_sub, mul_assoc]
 ... = ((-1) * (μ₁ - 1) * ((μ₂ * μ₃ + 1) * (1 / (μ₁ - 1)))) + μ₂ * μ₃
     : by rw [neg_one_mul, neg_sub, this]
 ... = -1
     : by rw [mul_comm _ (1 / (μ₁ - 1)), ←mul_assoc, mul_assoc _ (μ₁ - 1) _, ←mul_div_assoc, mul_one,
              div_self (show μ₁ - 1 ≠ 0, by linarith), neg_one_mul, mul_add, neg_one_mul, mul_one, add_comm, ←add_assoc, add_neg_self, zero_add]
end

/-
I am leaving the converse of Ceva's theorem and Menelaus theorem for later.
Most reasoning is calculation but lean is bad at it lol.
-/
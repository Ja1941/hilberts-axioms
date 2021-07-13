import geometry.euclidean.triangle
import data.real.basic
import tactic

open real
open inner_product_geometry
open euclidean_geometry

open_locale euclidean_geometry real_inner_product_space real
open_locale classical

variables {V : Type*} [inner_product_space ℝ V]
variables {P : Type*} [metric_space P] [normed_add_torsor V P]
include V

variables c o f : P

#check angle_eq_zero_of_angle_eq_pi_left
#check angle_eq_zero_iff

example (μ₂ μ₃ : ℝ) : 1 - μ₂ - (μ₂ * μ₃ - μ₂ + 1) = -μ₂ * μ₃ :=
begin
   rw [sub_sub, ←add_assoc, add_comm μ₂ _, sub_add, sub_self, sub_zero, ←sub_sub,
       sub_right_comm, sub_self, zero_sub, neg_mul_eq_neg_mul]
end

#check neg_div

example (a b c : ℝ) (hc : c ≠ 0) : a + -a = 0 :=
begin
  exact add_neg_self a
end

example (μ₁ μ₂ μ₃ k : ℝ)
(h₁ : -μ₂ * μ₃ / (μ₂ * μ₃ - μ₂ + 1) = k * ((-1) / (μ₁ - 1)))
(h₂ : (μ₂ * μ₃ + 1) / (μ₂ * μ₃ - μ₂ + 1) = k * -1) : μ₁ * μ₂ * μ₃ = -1 :=
begin
  rw [(show k = -(k * -1), by simp), ←h₂, ←neg_div, div_mul_eq_mul_div, neg_div, neg_mul_neg] at h₁,
  have cancel_denom : ∀ a b c : ℝ, c ≠ 0 → a / c = b / c → a = b,
    intros a b c hc h,
    rw [←mul_div_cancel a hc, mul_comm, mul_div_assoc, h, ←mul_div_assoc, mul_comm, mul_div_cancel _ hc],
  have := cancel_denom _ _ _ (by sorry) h₁,
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
              div_self (show μ₁ - 1 ≠ 0, by sorry), neg_one_mul, mul_add, neg_one_mul, mul_one, add_comm, ←add_assoc, add_neg_self, zero_add]
end

example (k : ℝ) (hk : k ≠ 1) : 1 - k ≠ 0 :=
begin
  intro hf,
  have : 1 = 0 + k, from eq_add_of_sub_eq hf,
  exact hk (by rw [this, zero_add])
end

#check angle_eq_pi_iff
#check angle_eq_zero_iff

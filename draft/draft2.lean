import data.matrix.basic
import data.matrix.notation
import linear_algebra.matrix.to_lin
import data.zmod.basic
import linear_algebra.dimension

open_locale matrix

section

variables (k : Type) [field k]

variable x : matrix (fin 2) (fin 3) (k)

#check matrix.mul_vec_lin x
#check @dim_range_add_dim_ker
#check @dim_range_add_dim_ker k (fin 3 → k) (fin 2 → k) (by assumption) (pi.add_comm_group) (pi.module _ _ _)
#check dim_range_add_dim_ker (matrix.mul_vec_lin x)

lemma rank_nullity : module.rank (k) (matrix.mul_vec_lin x).range
+ module.rank (k) (matrix.mul_vec_lin x).ker = module.rank (k) (fin 3 → k) := dim_range_add_dim_ker _

end

lemma zmod2_cases (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
  cases a with a ha, norm_num at ha, interval_cases a,
  left, refl, right, refl
end

lemma not_zero_iff_one (a : zmod 2) : a ≠ 0 ↔ a = 1 :=
begin
  split; intro ha,
  cases zmod2_cases a,
  exact absurd h ha, exact h,
  rw ha, simp
end 

noncomputable lemma field_zmod2 : field (zmod 2) :=
begin
  refine is_field.to_field (zmod 2) _,
  fconstructor,
  exact ⟨0, 1, by simp⟩,
  exact mul_comm,
  intros a ha,
  rw not_zero_iff_one at ha,
  rw ha, exact ⟨1, by simp⟩
end

variable x : matrix (fin 2) (fin 3) (zmod 2)

#check @rank_nullity (zmod 2) (field_zmod2) x

example : module.rank (zmod 2) (matrix.mul_vec_lin x).range
+ module.rank (zmod 2) (matrix.mul_vec_lin x).ker = module.rank (zmod 2) (fin 3 → zmod 2) :=
begin
  exact @rank_nullity (zmod 2) (field_zmod2) x,
end

variables a₁ a₂ a₃ b₁ b₂ b₃ : zmod 2

#check ![![a₁, a₂, a₃], ![b₁, b₂, b₃]]

example (a₁ a₂ a₃ b₁ b₂ b₃ : zmod 2) : true :=
begin
  have := @rank_nullity (zmod 2) (field_zmod2) ![![a₁, a₂, a₃], ![b₁, b₂, b₃]],
end
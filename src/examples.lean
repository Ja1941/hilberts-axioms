import main
import data.zmod.basic
import data.real.basic

open incidence_geometry incidence_order_geometry hilbert_plane

-- local attribute [-class] incidence_geometry -- cannot remove attribute [class]

variable x : zmod 2 × zmod 2 × zmod 2
#eval ((1, 1, 1) : zmod 2 × zmod 2 × zmod 2) + (1, 1, 0)

lemma self_mul_self_add_one : ∀ x : zmod 2, x * (x + 1) = 0 :=
begin
  intro x,
  cases x with x hx,
  norm_num at hx,
  interval_cases x;
  solve_by_elim
end

lemma self_add_one_mul_self : ∀ x : zmod 2, (x + 1) * x = 0 :=
by { intro x, rw mul_comm, exact self_mul_self_add_one x }

-- Fano plane
example : incidence_geometry :=
{ pts := {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)},
  lines := { S : set ({x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}) | 
    ∃ y : {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}, S = { x | x.1.1 * y.1.1 + x.1.2.1 * y.1.2.1 + x.1.2.2 * y.1.2.2 = 0}},
  I1 :=
  begin
    intros a b hab,
    set y : {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}
      := ⟨((a.1.1 + 1)*(b.1.1 + 1), (a.1.2.1 + 1)*(b.1.2.1 + 1), (a.1.2.2 + 1)*(b.1.2.2 + 1)), _⟩ with hy,
    use {x | x.1.1 * y.1.1 + x.1.2.1 * y.1.2.1 + x.1.2.2 * y.1.2.2 = 0},
    use y, rw hy,
    split, simp, repeat {rw [←mul_assoc, self_mul_self_add_one _, zero_mul]},
    rw [add_zero, add_zero],
    split, simp, repeat {rw [mul_comm, mul_assoc, self_add_one_mul_self _, mul_zero]},
    rw [add_zero, add_zero],
    
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


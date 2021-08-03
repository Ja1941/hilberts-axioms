import main
import data.zmod.basic
import data.real.basic

open incidence_geometry -- for `pts` because it's not in root namespace

open incidence_order_geometry -- for `is_between`

open incidence_order_congruence_geometry -- for `segment_congr`

-- local attribute [-class] incidence_geometry -- cannot remove attribute [class]

-- Fano plane
example : incidence_geometry :=
{ pts := {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)},
  lines := { S : set ({x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}) | 
    ∃ y : {x : zmod 2 × zmod 2 × zmod 2 // x ≠ (0,0,0)}, S = { x | x.1.1 * y.1.1 + x.1.2.1 * y.1.2.1 + x.1.2.2 * y.1.2.2 = 0}},
  I1 := sorry,
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
example : incidence_order_congruence_geometry :=
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


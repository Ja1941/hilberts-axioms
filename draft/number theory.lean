structure incidence_order_geometry := (pts : ℕ)
structure incidence_order_congruence_geometry extends incidence_order_geometry

instance : has_coe incidence_order_congruence_geometry incidence_order_geometry
:= ⟨incidence_order_congruence_geometry.to_incidence_order_geometry⟩

variables (b : incidence_order_congruence_geometry) (f : incidence_order_geometry → ℕ)

#check b
#check f
#check f b -- ℕ
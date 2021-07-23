example {A B : set ℕ} (h : A = B) : 1 ∈ A → 1 ∈ B :=
begin
  intro hA,
  rw h at hA,
end
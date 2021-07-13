import algebra.support

open set

universes u
variable (pts : Type u)

structure incidence_geometry :=
-- A line is defined as a set of points, 'lines' here is the set of all lines
(lines : set (set pts))
-- two distinct points uniquely define a line
(I1 : ∀ a b : pts, a ≠ b → ∃ l ∈ lines,
 a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l))
-- every line contains at least two points
(I2 : ∀ l ∈ lines, ∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l)
-- there exists three noncollinear points
(I3 : ∃ a b c : pts, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l))

def line {Γ : incidence_geometry pts} (a b : pts) (hab : a ≠ b) :
  { L : set pts // L ∈ Γ.lines ∧ a ∈ L ∧ b ∈ L } :=
by {choose l hl ha hb h using (Γ.I1 a b hab), exact ⟨l, hl, ha, hb⟩}

-- Two distinct lines have at least one point in common
lemma two_line_one_common_pt {Γ : @incidence_geometry pts} :
∀ (l₁ l₂ ∈ Γ.lines) (a b : pts), l₁ ≠ l₂ → a ≠ b → ¬(a ∈ (l₁ ∩ l₂) ∧ b ∈ (l₁ ∩ l₂)) :=
begin
  intros l₁ l₂ hl₁ hl₂ a b hll hab hf,
  rcases (Γ.I1 a b hab) with ⟨l, hl, -, -, key⟩,
  exact hll ((key l₁ hl₁ (mem_of_mem_inter_left hf.1) (mem_of_mem_inter_left hf.2)).trans
            (key l₂ hl₂ (mem_of_mem_inter_right hf.1) (mem_of_mem_inter_right hf.2)).symm)
end

-- Two distinct lines with no points in common are parallel.
def is_parallel (l₁ l₂ : set pts) : Prop :=
l₁ ≠ l₂ → l₁ ∩ l₂ = ∅

@[simp] lemma parallel_refl (l : set pts) : is_parallel pts l l :=
λ hf, absurd rfl hf

@[simp] lemma parallel_symm (l₁ l₂ : set pts) :
is_parallel pts l₁ l₂ → is_parallel pts l₂ l₁ :=
λ h hll, (inter_comm l₂ l₁).trans (h hll.symm)

structure incidence_geometry_parallel extends (incidence_geometry pts) :=
(Playfair : ∀ (a : pts) (l ∈ lines), ∀ l₁ l₂ ∈ lines,
a ∈ l₁ → a ∈ l₂ → is_parallel pts l₁ l → is_parallel pts l₂ l→ l₁ = l₂)

structure incidence_geometry_with_betweenness extends incidence_geometry pts :=
(is_between : pts → pts → pts → Prop)
-- If B is between A and C, then they are on a same line
(B1 : ∀ a b c : pts, is_between a b c → (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ ∃ l ∈ lines, {a, b, c} ⊆ l)
-- Given distinct A and B, ∃ C such that B is between A and C
(B2 : ∀ a b : pts, a ≠ b → ∃ c : pts, is_between a b c)
-- Given any collinear three points, exactly one of them is between the other two.
(B3 : ∀ (a b c : pts) (l ∈ lines), {a, b, c} ⊆ l →
is_between a b c ∨ is_between a c b ∨ is_between b a c)
/- A, B, C are noncollinear and l doesn't contain any of them. If l contains D between A and B, then it
   contains a point either between A and C or B and C -/
(B4 : ∀ (a b c : pts) (l ∈ lines), (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, {a, b, c} ⊆ l))
      → a ∉ l → b ∉ l → c ∉ l → ∃ d : pts, is_between a d b → d ∈ l →
      ∃ p : pts, p ∈ l ∧ (is_between a p c ∨ is_between b p c)
      ∧ ¬(is_between a p c ∧ is_between b p c))

def segment (Γ : incidence_geometry_with_betweenness pts) (a b : pts) : set pts :=
{c : pts | Γ.is_between a c b} ∪ {a, b}

-- Segment a a is just the singleton {a}
lemma between_same_pt (Γ : incidence_geometry_with_betweenness pts) (a : pts) :
segment pts Γ a a = {a} :=
begin
  unfold segment,
  suffices : {c : pts | Γ.is_between a c a} = ∅,
    rw this, simp,
  ext1, simp, intro hf,
  exact (Γ.B1 a x a hf).2.1 (rfl)
end

def same_side_line {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (a b : pts) : Prop := 
a ∉ l ∧ b ∉ l ∧ segment pts Γ a b ∩ l = ∅

def diff_side_line {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (a b : pts) : Prop :=
a ∉ l ∧ b ∉ l ∧ segment pts Γ a b ∩ l ≠ ∅

theorem plane_separation {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (a : pts) (ha : a ∉ l) :
∀ x : pts, x ∉ l → (same_side_line pts l H a x ∨ diff_side_line pts l H a x)
∧ ¬(same_side_line pts l H a x ∧ diff_side_line pts l H a x) :=
begin
  intros x hx,
  unfold same_side_line diff_side_line segment,
  split,
  by_cases ({c : pts | Γ.is_between a c x} ∪ {a, x}) ∩ l = ∅,
  left, exact ⟨ha, hx, h⟩,
  right, exact ⟨ha, hx, h⟩,
  push_neg,
  intros h ha hx,
  exact h.2.2
end

def same_side_pt {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (p a b ∈ l) : Prop :=
a ≠ p ∧ b ≠ p ∧ p ∉ segment pts Γ a b

def diff_side_pt {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (p a b ∈ l) : Prop :=
a ≠ p ∧ b ≠ p ∧ p ∈ segment pts Γ a b

#check same_side_pt

theorem line_separation {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (p a ∈ l) (ha : a ≠ p) :
∀ x ∈ l, x ≠ p → (same_side_pt pts l (by assumption) p a x (by assumption) (by assumption) (by assumption)
                  ∨ diff_side_pt pts l (by assumption) p a x (by assumption) (by assumption)(by assumption))
∧ ¬((same_side_pt pts l (by assumption) p a x (by assumption) (by assumption) (by assumption)
    ∧ (same_side_pt pts l (by assumption) p a x (by assumption) (by assumption) (by assumption)) :=
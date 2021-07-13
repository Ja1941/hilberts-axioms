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

-- Two distinct lines have at least one point in common
lemma two_line_one_common_pt {Γ : incidence_geometry pts} :
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
(B1 : ∀ a b c : pts, is_between a b c → is_between c b a
                        ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ ∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l)
-- Given distinct A and B, ∃ C such that B is between A and C
(B2 : ∀ a b : pts, a ≠ b → ∃ c : pts, is_between a b c)
-- Given any collinear three points, exactly one of them is between the other two.
(B3 : ∀ (a b c : pts) (l ∈ lines), a ∈ l ∧ b ∈ l ∧ c ∈ l →
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
  exact (Γ.B1 a x a hf).2.2.1 (rfl)
end

def same_side_line (Γ : incidence_geometry_with_betweenness pts)
(l : set pts) (a b : pts) : Prop := segment pts Γ a b ∩ l = ∅ ∧ a ∉ l ∧ b ∉ l

def diff_side_line (Γ : incidence_geometry_with_betweenness pts)
(l : set pts) (a b : pts) : Prop := segment pts Γ a b ∩ l ≠ ∅ ∧ a ∉ l ∧ b ∉ l

theorem plane_separation {Γ : incidence_geometry_with_betweenness pts}
(l : set pts) (a : pts) (ha : a ∉ l) :
∀ x : pts, x ∉ l → (same_side_line pts Γ l a x ∨ diff_side_line pts Γ l a x)
                    ∧ ¬(same_side_line pts Γ l a x ∧ diff_side_line pts Γ l a x) :=
begin
  intros x hx,
  unfold same_side_line diff_side_line segment,
  split,
  rw ←or_and_distrib_right,
  exact ⟨em _, ha, hx⟩,
  intro hf,
  exact hf.2.1 hf.1.1
end

def collinear (Γ : incidence_geometry_with_betweenness pts) (a b c : pts) : Prop :=
∃ l ∈ Γ.lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

def same_side_pt (Γ : incidence_geometry_with_betweenness pts) (p a b : pts) : Prop :=
p ∉ segment pts Γ a b ∧ a ≠ p ∧ b ≠ p ∧ collinear pts Γ p a b

def diff_side_pt (Γ : incidence_geometry_with_betweenness pts) (p a b : pts) : Prop :=
p ∈ segment pts Γ a b ∧ a ≠ p ∧ b ≠ p ∧ collinear pts Γ p a b

theorem line_separation {Γ : incidence_geometry_with_betweenness pts}
(p a b : pts) (hpab : collinear pts Γ p a b) (ha : a ≠ p) (hb : b ≠ p)  : 
(same_side_pt pts Γ p a b ∨ diff_side_pt pts Γ p a b) ∧
¬(same_side_pt pts Γ p a b ∧ diff_side_pt pts Γ p a b) :=
begin
  unfold same_side_pt diff_side_pt segment,
  split,
  rw ←or_and_distrib_right,
  exact ⟨or.comm.mp (em _), ha, hb, hpab⟩,
  intro hf,
  exact hf.1.1 hf.2.1
end

lemma not_same_side_pt {Γ : incidence_geometry_with_betweenness pts}
(p a b : pts) (hpab : collinear pts Γ p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬same_side_pt pts Γ p a b ↔ diff_side_pt pts Γ p a b) :=
begin
  have := line_separation pts p a b hpab ha hb,
  split,
  intro hs,
  cases this.1 with h h,
  exact absurd h hs, exact h,
  intro hd,
  cases (not_and_distrib.mp this.2) with h h,
  exact h, exact absurd hd h
end

example {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := not_iff_not.symm

lemma not_diff_same_pt {Γ : incidence_geometry_with_betweenness pts}
(p a b : pts) (hpab : collinear pts Γ p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬diff_side_pt pts Γ p a b ↔ same_side_pt pts Γ p a b) :=
by rw [←not_iff_not.mpr (not_same_side_pt pts p a b hpab ha hb), not_not]

def line (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) :
  { L : set pts // L ∈ Γ.lines ∧ a ∈ L ∧ b ∈ L } :=
by {choose l hl ha hb h using (Γ.I1 a b hab), exact ⟨l, hl, ha, hb⟩}

lemma two_pt_one_line (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) :
∀ l ∈ Γ.lines, a ∈ l → b ∈ l → l = (line pts Γ a b hab).1 :=
begin
  rcases Γ.I1 a b hab with ⟨l, hl, ha, hb, h⟩,
  intros l' hl hal hbl,
  have h₁ := h (line pts Γ a b hab).1 (line pts Γ a b hab).2.1 (line pts Γ a b hab).2.2.1 (line pts Γ a b hab).2.2.2,
  have h₂ := h l' hl hal hbl,
  rw [h₁, h₂]
end

lemma line_comm (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) :
(line pts Γ b a hab.symm).1 = (line pts Γ a b hab).1 :=
two_pt_one_line pts Γ a b hab (line pts Γ b a hab.symm).1 (line pts Γ b a hab.symm).2.1
(line pts Γ b a hab.symm).2.2.2 (line pts Γ b a hab.symm).2.2.1

def ray (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) : set pts :=
(line pts Γ a b hab).1 ∩ {x : pts | same_side_pt pts Γ a b x}

def opposite_ray (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) :
{L : set pts // L ∪ ray pts Γ a b hab = (line pts Γ a b hab).1} :=
begin
  choose c hc using Γ.B2 b a hab.symm,
  use ray pts Γ a c (Γ.B1 b a c hc).2.2.2.1,
  unfold ray,
  have : (line pts Γ a c _).1 = (line pts Γ a b hab).1,
    rcases (Γ.B1 b a c hc).2.2.2.2 with ⟨l, hl, hbl, hal, hcl⟩,
    rw [←(two_pt_one_line pts Γ a b hab l hl hal hbl), ←(two_pt_one_line pts Γ a c (Γ.B1 b a c hc).2.2.2.1 l hl hal hcl)],
  rw this,
  have : {x : pts | same_side_pt pts Γ a c x} = {x : pts | diff_side_pt pts Γ a b x},
    ext1, simp,
    split; intro h,
    by_contra hf,
    
end

/-
example {a b c : set pts} (h : b ⊆ a) : a ∩ b = b := inter_eq_right_iff_subset.mpr h

lemma two_ray_line (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) :
(line pts Γ a b hab).1 = (ray pts Γ a b hab) ∪ (ray pts Γ b a hab.symm) :=
begin
  rcases Γ.I1 a b hab with ⟨l, hl, ha, hb, h⟩,
  have := h (line pts Γ a b hab).1 (line pts Γ a b hab).2.1 (line pts Γ a b hab).2.2.1 (line pts Γ a b hab).2.2.2,
  rw this, symmetry, apply h,
  unfold ray,
  rw [←line_comm pts Γ a b hab, ←inter_distrib_left],
  suffices hsub : (line pts Γ a b hab).val ⊆ ({x : pts | same_side_pt pts Γ a b x} ∪ {x : pts | same_side_pt pts Γ b a x}),
    rw inter_eq_left_iff_subset.mpr hsub, rw this, exact hl,
  
end
-/
def noncollinear (Γ : incidence_geometry_with_betweenness pts) (a b c : pts) : Prop :=
∀ l ∈ Γ.lines, ¬(a ∈ l ∧ b ∈ l ∧ c ∈ l)

lemma noncollinear_not_eq (Γ : incidence_geometry_with_betweenness pts)
{a b c : pts} (hf : noncollinear pts Γ a b c) : a ≠ b ∧ b ≠ c ∧ c ≠ a :=
begin
  have : ∀ a b : pts, ∃ l ∈ Γ.lines, a ∈ l ∧ b ∈ l,
    intros a b,
    by_cases a = b,
      rw ←h, simp,
      have : ∃ p : pts, a ≠ p,
        by_contra,
        push_neg at h,
        rcases Γ.I3 with ⟨x, y, -, hxy, -, -, -⟩,
        exact hxy ((h x).symm .trans (h y)),
      cases this with b h,
      use line pts Γ a b h,
      exact ⟨(line pts Γ a b h).2.1, (line pts Γ a b h).2.2.1⟩,
    use line pts Γ a b h,
    exact (line pts Γ a b h).2,
  split,
  intro h,
  rw h at hf,
  rcases this b c with ⟨l, hl, key⟩,
  apply hf l hl, exact ⟨key.1, key⟩,
  split,
  intro h,
  rw h at hf,
  rcases this a c with ⟨l, hl, key⟩,
  apply hf l hl, exact ⟨key.1, key.2, key.2⟩,
  intro h,
  rw h at hf,
  rcases this a b with ⟨l, hl, key⟩,
  apply hf l hl, exact ⟨key.1, key.2, key.1⟩
end

structure angle (Γ : incidence_geometry_with_betweenness pts) (a b c : pts) :=
(v := b) (p₁ := a) (p₂ := c) (noncollinear : noncollinear pts Γ a b c)
(s₁ := ray pts Γ a b) (s₂ := ray pts Γ c b)
(l₁ := line pts Γ a b (noncollinear_not_eq pts Γ noncollinear).1)
(l₂ := line pts Γ c b (noncollinear_not_eq pts Γ noncollinear).2.1.symm)
(inside := {p : pts | same_side_line pts Γ l₁ p c ∧ same_side_line pts Γ l₂ p a})

structure triangle (Γ : incidence_geometry_with_betweenness pts) (a b c : pts) :=
(v₁ := a) (v₂ := b) (v₃ := c)
(noncollinear : noncollinear pts Γ a b c)
(s₁ := segment pts Γ b c) (s₂ := segment pts Γ a c) (s₃ := segment pts Γ a b)
(a₁ : angle pts Γ b a c) (a₂ : angle pts Γ a b c) (a₃ : angle pts Γ a c b)
(inside := a₁.inside ∪ a₂.inside ∪ a₃.inside)

lemma crossbar (Γ : incidence_geometry_with_betweenness pts) {a b c d : pts} (ABC : angle pts Γ a b c)
(hd : d ∈ ABC.inside) : ray pts Γ b d ∩ segment pts Γ a c ≠ ∅ :=
begin
  sorry
end
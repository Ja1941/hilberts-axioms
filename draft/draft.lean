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

def same_side_line (Γ : incidence_geometry_with_betweenness pts)
(l : set pts) (a b : pts) : Prop
:= segment pts Γ a b ∩ l = ∅ ∧ a ∉ l ∧ b ∉ l

def diff_side_line (Γ : incidence_geometry_with_betweenness pts)
(l : set pts) (a b : pts) : Prop
:= segment pts Γ a b ∩ l ≠ ∅ ∧ a ∉ l ∧ b ∉ l

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

def same_side_pt (Γ : incidence_geometry_with_betweenness pts) (p a b : pts) : Prop :=
p ∉ segment pts Γ a b ∧ a ≠ p ∧ b ≠ p ∧ ∃ l ∈ Γ.lines, a ∈ l ∧ b ∈ l ∧ p ∈ l

def diff_side_pt (Γ : incidence_geometry_with_betweenness pts) (p a b : pts) : Prop :=
p ∈ segment pts Γ a b ∧ a ≠ p ∧ b ≠ p ∧ ∃ l ∈ Γ.lines, a ∈ l ∧ b ∈ l ∧ p ∈ l

theorem line_separation {Γ : incidence_geometry_with_betweenness pts}
(l ∈ Γ.lines) (p a ∈ l) (ha : a ≠ p) : 
∀ x ∈ l, x ≠ p → (same_side_pt pts Γ p a x ∨ diff_side_pt pts Γ p a x)
                  ∧ ¬(same_side_pt pts Γ p a x ∧ diff_side_pt pts Γ p a x) :=
begin
  intros x H hx,
  unfold same_side_pt diff_side_pt segment,
  split,
  rw ←or_and_distrib_right,
  exact ⟨or.comm.mp (em _), ha, hx, ⟨l, by assumption, by assumption, by assumption, by assumption⟩⟩,
  intro hf,
  exact hf.1.1 hf.2.1
end

def line (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) :
  { L : set pts // L ∈ Γ.lines ∧ a ∈ L ∧ b ∈ L } :=
by {choose l hl ha hb h using (Γ.I1 a b hab), exact ⟨l, hl, ha, hb⟩}

def ray (Γ : incidence_geometry_with_betweenness pts) (a b : pts) (hab : a ≠ b) : set pts :=
line pts Γ a b hab ∩ {x : pts | same_side_pt pts Γ a b x}

def noncollinear (Γ : incidence_geometry_with_betweenness pts) (a b c : pts) : Prop :=
∀ l ∈ Γ.lines, ¬(a ∈ l ∧ b ∈ l ∧ c ∈ l)

lemma noncollinear_not_eq (Γ : incidence_geometry_with_betweenness pts) :
∀ a b c : pts, noncollinear pts Γ a b c → a ≠ b ∧ b ≠ c ∧ c ≠ a :=
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
  intros a b c hf,
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

def angle (Γ : incidence_geometry_with_betweenness pts) (a b c : pts) (habc : noncollinear pts Γ a b c ) :
set pts := ray pts Γ a b (noncollinear_not_eq pts Γ a b c habc).1
           ∪ ray pts Γ c b (noncollinear_not_eq pts Γ a b c habc).2.1.symm

def inside_angle (Γ : incidence_geometry_with_betweenness pts)
{a b c : pts} {habc : noncollinear pts Γ a b c} (α : angle pts Γ a b c habc) (p : pts) : Prop
:= same_side_line pts Γ (line pts Γ a b (noncollinear_not_eq pts Γ a b c habc).1) c p
   ∧ same_side_line pts Γ (line pts Γ c b (noncollinear_not_eq pts Γ a b c habc).2.1.symm) a p

def triangle (Γ : incidence_geometry_with_betweenness pts) (a b c : pts)
(habc : noncollinear pts Γ a b c) : set pts :=
segment pts Γ a b ∪ segment pts Γ b c ∪ segment pts Γ c a

def inside_tri (Γ : incidence_geometry_with_betweenness pts) (a b c : pts)
(habc : noncollinear pts Γ a b c) (T : triangle pts Γ a b c habc) (p : pts) : Prop :=
inside_angle pts Γ (angle pts Γ a b c habc) p
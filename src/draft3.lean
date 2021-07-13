import algebra.support

open set

universes u

structure incidence_geometry :=
(pts : Type u)
-- A line is defined as a set of points, 'lines' here is the set of all lines
(lines : set (set pts))
-- two distinct points uniquely define a line
(I1 : ∀ a b : pts, a ≠ b → ∃ l ∈ lines,
 a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l))
-- every line contains at least two points
(I2 : ∀ l ∈ lines, ∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l)
-- there exists three noncollinear points
(I3 : ∃ a b c : pts, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l))

-- Two distinct lines with no points in common are parallel.
def is_parallel {Γ : incidence_geometry} (l₁ l₂ : set Γ.pts) : Prop :=
l₁ ≠ l₂ → l₁ ∩ l₂ = ∅

@[simp] lemma parallel_refl {Γ : incidence_geometry} (l : set Γ.pts) : is_parallel l l :=
λ hf, absurd rfl hf

@[simp] lemma parallel_symm {Γ : incidence_geometry} (l₁ l₂ : set Γ.pts) :
is_parallel l₁ l₂ → is_parallel l₂ l₁ :=
λ h hll, (inter_comm l₂ l₁).trans (h hll.symm)

structure incidence_geometry_parallel extends (incidence_geometry) :=
(Playfair : ∀ (a : pts) (l ∈ lines), ∀ l₁ l₂ ∈ lines,
a ∈ l₁ → a ∈ l₂ → is_parallel l₁ l → is_parallel l₂ l → l₁ = l₂)

structure incidence_geometry_betweenness extends incidence_geometry :=
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
(B4 : ∀ (a b c : pts) (l ∈ lines),
      (∀ l ∈ lines, ¬(a ∈ l ∧ b ∈ l ∧ c ∈ l)) → a ∉ l → b ∉ l → c ∉ l
      → ∃ d : pts, is_between a d b → d ∈ l →
      ∃ p : pts, p ∈ l ∧ (is_between a p c ∨ is_between b p c)
      ∧ ¬(is_between a p c ∧ is_between b p c))

lemma is_between_comm {Γ : incidence_geometry_betweenness} (a b c : Γ.pts) :
Γ.is_between a b c ↔ Γ.is_between c b a := iff.intro (λ h, (Γ.B1 _ _ _ h).1) (λ h, (Γ.B1 _ _ _ h).1)

lemma is_between_not_eq {Γ : incidence_geometry_betweenness} {a b c : Γ.pts} (h : Γ.is_between a b c) :
(a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) := ⟨(Γ.B1 a b c h).2.1, (Γ.B1 a b c h).2.2.1, (Γ.B1 a b c h).2.2.2.1⟩

def collinear {Γ : incidence_geometry_betweenness} (a b c : Γ.pts) : Prop :=
∃ l ∈ Γ.lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

lemma is_between_collinear {Γ : incidence_geometry_betweenness} (a b c : Γ.pts)
(h : Γ.is_between a b c) : collinear a b c := (Γ.B1 a b c h).2.2.2.2

lemma is_between_extend {Γ : incidence_geometry_betweenness} {a b : Γ.pts} (h : a ≠ b) :
∃ c : Γ.pts, Γ.is_between a b c := Γ.B2 a b h

def segment {Γ : incidence_geometry_betweenness} (a b : Γ.pts) : set Γ.pts :=
{c : Γ.pts | Γ.is_between a c b} ∪ {a, b}

-- Segment a a is just the singleton {a}
lemma between_same_pt {Γ : incidence_geometry_betweenness} (a : Γ.pts) :
segment a a = {a} :=
begin
  unfold segment,
  suffices : {c : Γ.pts | Γ.is_between a c a} = ∅,
    rw this, simp,
  ext1, simp, intro hf,
  exact (is_between_not_eq hf).2.1 (rfl)
end

def line {Γ : incidence_geometry_betweenness} {a b : Γ.pts} (hab : a ≠ b) :
  { L : set Γ.pts // L ∈ Γ.lines ∧ a ∈ L ∧ b ∈ L } :=
by {choose l hl ha hb h using (Γ.I1 a b hab), exact ⟨l, hl, ha, hb⟩}

lemma two_pt_one_line {Γ : incidence_geometry_betweenness} {a b : Γ.pts} (hab : a ≠ b) :
∀ l ∈ Γ.lines, a ∈ l → b ∈ l → l = (line hab).1 :=
begin
  rcases Γ.I1 a b hab with ⟨l, hl, ha, hb, h⟩,
  intros l' hl hal hbl,
  have h₁ := h (line hab).1 (line hab).2.1 (line hab).2.2.1 (line hab).2.2.2,
  have h₂ := h l' hl hal hbl,
  rw [h₁, h₂]
end

lemma line_comm {Γ : incidence_geometry_betweenness} {a b : Γ.pts} (hab : a ≠ b) :
(line hab.symm).1 = (line hab).1 :=
two_pt_one_line hab (line hab.symm).1 (line hab.symm).2.1
(line hab.symm).2.2.2 (line hab.symm).2.2.1

def same_side_line {Γ : incidence_geometry_betweenness}
(l ∈ Γ.lines) (a b : Γ.pts) : Prop := segment a b ∩ l = ∅ ∧ a ∉ l ∧ b ∉ l

def diff_side_line {Γ : incidence_geometry_betweenness}
(l ∈ Γ.lines) (a b : Γ.pts) : Prop := segment a b ∩ l ≠ ∅ ∧ a ∉ l ∧ b ∉ l

lemma same_side_line_inter {Γ : incidence_geometry_betweenness} {l ∈ Γ.lines} {a b : Γ.pts}
(h : same_side_line l H a b) : segment a b ∩ l = ∅ := h.1

lemma diff_side_line_inter {Γ : incidence_geometry_betweenness} {l ∈ Γ.lines} {a b : Γ.pts}
(h : diff_side_line l H a b) : segment a b ∩ l ≠ ∅ := h.1

lemma same_side_line_not_in {Γ : incidence_geometry_betweenness} {l ∈ Γ.lines} {a b : Γ.pts}
(h : same_side_line l H a b) : a ∉ l ∧ b ∉ l := h.2

lemma diff_side_line_not_in {Γ : incidence_geometry_betweenness} {l ∈ Γ.lines} {a b : Γ.pts}
(h : diff_side_line l H a b) : a ∉ l ∧ b ∉ l := h.2

theorem plane_separation {Γ : incidence_geometry_betweenness}
{l ∈ Γ.lines} {a b : Γ.pts} (ha : a ∉ l) (hx : b ∉ l) :
(same_side_line l H a b ∨ diff_side_line l H a b)
∧ ¬(same_side_line l H a b ∧ diff_side_line l H a b) :=
begin
  unfold same_side_line diff_side_line segment,
  split,
  rw ←or_and_distrib_right,
  exact ⟨em _, ha, hx⟩,
  intro hf,
  exact hf.2.1 hf.1.1
end

def same_side_pt {Γ : incidence_geometry_betweenness} (p a b : Γ.pts) : Prop :=
p ∉ segment a b ∧ a ≠ p ∧ b ≠ p ∧ collinear p a b

def diff_side_pt {Γ : incidence_geometry_betweenness} (p a b : Γ.pts) : Prop :=
p ∈ segment a b ∧ a ≠ p ∧ b ≠ p ∧ collinear p a b

lemma same_side_pt_inter {Γ : incidence_geometry_betweenness} {p a b : Γ.pts}
(h : same_side_pt p a b) : p ∉ segment a b := h.1

lemma diff_side_pt_inter {Γ : incidence_geometry_betweenness} {p a b : Γ.pts}
(h : diff_side_pt p a b) : p ∈ segment a b := h.1

lemma same_side_pt_not_eq {Γ : incidence_geometry_betweenness} {p a b : Γ.pts}
(h : same_side_pt p a b) : a ≠ p ∧ b ≠ p := ⟨h.2.1, h.2.2.1⟩

lemma diff_side_pt_not_eq {Γ : incidence_geometry_betweenness} {p a b : Γ.pts}
(h : diff_side_pt p a b) : a ≠ p ∧ b ≠ p := ⟨h.2.1, h.2.2.1⟩

lemma same_side_pt_collinear {Γ : incidence_geometry_betweenness} {p a b : Γ.pts}
(h : same_side_pt p a b) : collinear p a b := h.2.2.2

lemma diff_side_pt_collinear {Γ : incidence_geometry_betweenness} {p a b : Γ.pts}
(h : diff_side_pt p a b) : collinear p a b := h.2.2.2

theorem line_separation {Γ : incidence_geometry_betweenness}
{p a b : Γ.pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p)  : 
(same_side_pt p a b ∨ diff_side_pt p a b) ∧
¬(same_side_pt p a b ∧ diff_side_pt p a b) :=
begin
  unfold same_side_pt diff_side_pt segment,
  split,
  rw ←or_and_distrib_right,
  exact ⟨or.comm.mp (em _), ha, hb, hpab⟩,
  intro hf,
  exact hf.1.1 hf.2.1
end

lemma not_same_side_pt {Γ : incidence_geometry_betweenness}
{p a b : Γ.pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬same_side_pt p a b ↔ diff_side_pt p a b) :=
begin
  have := line_separation hpab ha hb,
  split,
  intro hs,
  cases this.1 with h h,
  exact absurd h hs, exact h,
  intro hd,
  cases (not_and_distrib.mp this.2) with h h,
  exact h, exact absurd hd h
end

lemma not_diff_same_pt {Γ : incidence_geometry_betweenness}
{p a b : Γ.pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬diff_side_pt p a b ↔ same_side_pt p a b) :=
by rw [←not_iff_not.mpr (not_same_side_pt hpab ha hb), not_not]

def ray {Γ : incidence_geometry_betweenness} {a b : Γ.pts} (hab : a ≠ b) : set Γ.pts :=
(line hab).1 ∩ {x : Γ.pts | same_side_pt a b x}
/-
def opposite_ray {Γ : incidence_geometry_betweenness} {p a : Γ.pts} (hpa : p ≠ a) :
{L : set Γ.pts // L ∪ ray hpa = (line hpa).1} :=
begin
  choose b hapb using is_between_extend a p hpa.symm,
  have hpb : p ≠ b, from (is_between_not_eq hapb).2.2,
  use ray hpb,
  unfold ray,
  have : (line hpb).1 = (line hpa).1,
    rcases (is_between_collinear a p b hapb) with ⟨l, hl, hal, hpl, hbl⟩,
    rw [←(two_pt_one_line hpa l hl hpl hal), ←(two_pt_one_line hpb l hl hpl hbl)],
  rw [this, ←inter_union_distrib_left],
  have : {x : Γ.pts | same_side_pt p b x} = {x : Γ.pts | diff_side_pt p a x},
    ext1, simp,
     
end
-/
/-
example {a b c : set pts} (h : b ⊆ a) : a ∩ b = b := inter_eq_right_iff_subset.mpr h

lemma two_ray_line (Γ : incidence_geometry_betweenness pts) (a b : pts) (hab : a ≠ b) :
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
def noncollinear {Γ : incidence_geometry_betweenness} (a b c : Γ.pts) : Prop :=
∀ l ∈ Γ.lines, ¬(a ∈ l ∧ b ∈ l ∧ c ∈ l)

lemma noncollinear_not_eq {Γ : incidence_geometry_betweenness}
{a b c : Γ.pts} (hf : noncollinear a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c :=
begin
  have : ∀ a b : Γ.pts, ∃ l ∈ Γ.lines, a ∈ l ∧ b ∈ l,
    intros a b,
    by_cases a = b,
      rw ←h, simp,
      have : ∃ p : Γ.pts, a ≠ p,
        by_contra,
        push_neg at h,
        rcases Γ.I3 with ⟨x, y, -, hxy, -, -, -⟩,
        exact hxy ((h x).symm .trans (h y)),
      cases this with b h,
      use line h,
      exact ⟨(line h).2.1, (line h).2.2.1⟩,
    use line h,
    exact (line h).2,
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
  rcases this b c with ⟨l, hl, key⟩,
  apply hf l hl, exact ⟨key.2, key.1, key.2⟩
end

structure angle {Γ : incidence_geometry_betweenness} (a b c : Γ.pts) :=
(v := b) (p₁ := a) (p₂ := c) (noncollinear : noncollinear a b c)
(s₁ := ray (show a ≠ b, from (noncollinear_not_eq noncollinear).1))
(s₂ := ray (show c ≠ b, from (noncollinear_not_eq noncollinear).2.1.symm))
(l₁ := line (show a ≠ b, from (noncollinear_not_eq noncollinear).1))
(l₂ := line (show c ≠ b, from (noncollinear_not_eq noncollinear).2.1.symm))
(inside := {p : Γ.pts | same_side_line l₁.1 l₁.2.1 p c ∧ same_side_line l₂.1 l₂.2.1 p a})

structure triangle {Γ : incidence_geometry_betweenness} (a b c : Γ.pts) :=
(v₁ := a) (v₂ := b) (v₃ := c)
(noncollinear : noncollinear a b c)
(s₁ := segment b c) (s₂ := segment a c) (s₃ := segment a b)
(a₁ : angle b a c) (a₂ : angle a b c) (a₃ : angle a c b)
(inside := a₁.inside ∪ a₂.inside ∪ a₃.inside)

/-
lemma crossbar {Γ : incidence_geometry_betweenness} {a b c d : Γ.pts} (T : angle a b c)
(hd : d ∈ T.inside) : ray (show b ≠ d, by sorry) ∩ segment a c ≠ ∅ :=
begin
  set BD := (line (show b ≠ d, by sorry)).1,
  cases is_between_extend (show b ≠ c, from (noncollinear_not_eq T.noncollinear).2.1) with e hbce,
  have hb4 : ¬(BD ∩ segment a e ≠ ∅) → (BD ∩ segment a c ≠ ∅),
    have := Γ.B4 c e a BD (line (show b ≠ d, by sorry)).2.1 (show noncollinear c e a, by sorry),
  sorry, --geometry is so hard, by lean prover
end
-/

structure incidence_geometry_betweenness_congruence extends incidence_geometry_betweenness :=
(segment_congr : pts → pts → pts → pts → Prop)
(c1 : ∀ a b c p : pts, )
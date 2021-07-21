import algebra.support
import set_theory.zfc

open set

universes u

structure incidence_geometry :=
(pts : Type u)
--A line is defined as a set of points, 'lines' here is the set of all lines
(lines : set (set pts))
--two distinct points uniquely define a line
(I1 : ∀ a b : pts, a ≠ b → ∃ l ∈ lines,
 a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l))
--every line contains at least two points
(I2 : ∀ l ∈ lines, ∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l)
--there exists three noncollinear points
(I3 : ∃ a b c : pts, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l))

variable {I : incidence_geometry}

noncomputable def line (a b : I.pts) :
{ L : set I.pts // (a ≠ b → L ∈ I.lines) ∧ a ∈ L ∧ b ∈ L } :=
begin
  by_cases hab : a = b, rw hab,
  exact ⟨{b}, λ hf, absurd rfl hf, by simp⟩,
  choose l hl ha hb h using (I.I1 a b hab),
  exact ⟨l, λ h, hl, ha, hb⟩
end

local notation a`-ₗ`b := (line a b : set I.pts)

def intersect (m n : set I.pts) : Prop := (m ∩ n).nonempty

notation m`$`n := intersect m n

lemma line_in_lines {a b : I.pts} (hab : a ≠ b) :
(a-ₗb) ∈ I.lines := (line a b).2.1 hab

lemma pt_left_in_line (a b : I.pts) :
a ∈ (a-ₗb) := (line a b).2.2.1

lemma pt_right_in_line (a b : I.pts) :
b ∈ (a-ₗb) := (line a b).2.2.2

lemma line_unique {a b : I.pts} (hab : a ≠ b)
{l : set I.pts} (hl : l ∈ I.lines) (ha : a ∈ l) (hb : b ∈ l) : l = (a-ₗb) :=
begin
  rcases (I.I1 a b hab) with ⟨n, hn, -, -, key⟩,
  rw [key l hl ha hb,
      key (a-ₗb) (line_in_lines hab) (pt_left_in_line a b) (pt_right_in_line a b)]
end

lemma two_pt_on_one_line {l : set I.pts} (hl : l ∈ I.lines) :
∃ a b : I.pts, a ≠ b ∧ a ∈ l ∧ b ∈ l := I.I2 l hl

lemma two_pt_one_line {l m : set I.pts} (hl : l ∈ I.lines) (hm : m ∈ I.lines) {a b : I.pts} (hab : a ≠ b) :
a ∈ l ∧ b ∈ l → a ∈ m ∧ b ∈ m → l = m :=
λ habl habm, (line_unique hab hl habl.1 habl.2).trans (line_unique hab hm habm.1 habm.2).symm

lemma line_comm (a b : I.pts) : (a-ₗb) = (b-ₗa) :=
begin
  by_cases a = b, rw h,
  exact two_pt_one_line (line_in_lines h) (line_in_lines (ne.symm h)) h ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨pt_right_in_line b a, pt_left_in_line b a⟩
end

lemma two_line_one_pt {l₁ l₂ : set I.pts} (hl₁ : l₁ ∈ I.lines) (hl₂ : l₂ ∈ I.lines) :
∀ {a b : I.pts}, l₁ ≠ l₂ → a ∈ l₁ → a ∈ l₂ → b ∈ l₁ → b ∈ l₂ → a = b :=
begin
  intros a b hll ha₁ ha₂ hb₁ hb₂,
  by_cases hab : a = b, exact hab,
  rcases (I.I1 a b hab) with ⟨l, hl, -, -, key⟩,
  exact absurd ((key l₁ hl₁ ha₁ hb₁).trans (key l₂ hl₂ ha₂ hb₂).symm) hll
end

def collinear (a b c : I.pts) : Prop :=
∃ l ∈ I.lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

def noncollinear (a b c : I.pts) : Prop := ¬collinear a b c

lemma noncollinear_exist {a b : I.pts} (hab : a ≠ b) : ∃ c : I.pts, noncollinear a b c :=
begin
  by_contra hf, unfold noncollinear collinear at hf, push_neg at hf,
  rcases I.I3 with ⟨x, y, z, hxy, hxz, hyz, hxyz⟩,
  rcases hf x with ⟨l, hl, hal, hbl, hxl⟩,
  rcases hf y with ⟨m, hm, ham, hbm, hym⟩,
  rcases hf z with ⟨n, hn, han, hbn, hzn⟩,
  rw ←two_pt_one_line hl hm hab ⟨hal, hbl⟩ ⟨ham, hbm⟩ at hym,
  rw ←two_pt_one_line hl hn hab ⟨hal, hbl⟩ ⟨han, hbn⟩ at hzn,
  exact hxyz ⟨l, hl, hxl, hym, hzn⟩
end

lemma noncollinear_not_eq {a b c : I.pts} (hf : noncollinear a b c) : a ≠ b ∧ b ≠ c ∧ c ≠ a :=
begin
  have : ∀ a b : I.pts, ∃ l ∈ I.lines, a ∈ l ∧ b ∈ l,
    intros a b,
    by_cases a = b,
      rw ←h, simp,
      have : ∃ p : I.pts, a ≠ p,
        by_contra,
        push_neg at h,
        rcases I.I3 with ⟨x, y, -, hxy, -, -, -⟩,
        exact hxy ((h x).symm .trans (h y)),
      cases this with b h,
      use line a b,
      exact ⟨line_in_lines h, pt_left_in_line a b⟩,
    use line a b,
    exact ⟨line_in_lines h, pt_left_in_line a b, pt_right_in_line a b⟩,
  split,
  intro h,
  rw h at hf,
  rcases this b c with ⟨l, hl, key⟩,
  exact hf ⟨l, hl, key.1, key.1, key.2⟩,
  split,
  intro h,
  rw h at hf,
  rcases this a c with ⟨l, hl, key⟩,
  exact hf ⟨l, hl, key.1, key.2, key.2⟩,
  intro h,
  rw h at hf,
  rcases this a b with ⟨l, hl, key⟩,
  exact hf ⟨l, hl, key.1, key.2, key.1⟩
end

structure incidence_order_geometry extends incidence_geometry :=
(is_between : pts → pts → pts → Prop)
-- If B is between A and C, then they are on a same line
(B1 : ∀ a b c : pts, is_between a b c → is_between c b a
                        ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ collinear a b c)
-- Given distinct A and B, ∃ C such that B is between A and C
(B2 : ∀ a b : pts, a ≠ b → ∃ c : pts, is_between a b c)
-- Given any collinear three points, exactly one of them is between the other two.
(B3 : ∀ (a b c : pts) (l ∈ lines), a ∈ l ∧ b ∈ l ∧ c ∈ l →
(is_between a b c ∨ is_between a c b ∨ is_between b a c)
∧ ¬(is_between a b c ∧ is_between a c b)
∧ ¬(is_between a b c ∧ is_between b a c)
∧ ¬(is_between a c b ∧ is_between b a c))
/- A, B, C are noncollinear and l doesn't contain any of them. If l contains D between A and B, then it
   contains a point either between A and C or B and C -/
(B4 : ∀ (a b c : pts) (l ∈ lines),
      (noncollinear a b c) → a ∉ l → b ∉ l → c ∉ l
      → (∃ d : pts, is_between a d b ∧ d ∈ l) →
      (∃ p : pts, p ∈ l ∧ (is_between a p c ∨ is_between b p c))
      ∧ ∀ p q : pts, p ∈ l → q ∈ l → ¬(is_between a p c ∧ is_between b q c))

variable {B : incidence_order_geometry}

local notation a`-ₗ`b := (line a b : set B.pts)

instance : has_coe incidence_order_geometry incidence_geometry :=
⟨incidence_order_geometry.to_incidence_geometry⟩

lemma is_between_symm (a b c : B.pts) :
B.is_between a b c ↔ B.is_between c b a := iff.intro (λ h, (B.B1 _ _ _ h).1) (λ h, (B.B1 _ _ _ h).1)

lemma is_between_not_eq {a b c : B.pts} (h : B.is_between a b c) :
(a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) := ⟨(B.B1 a b c h).2.1, (B.B1 a b c h).2.2.1, (B.B1 a b c h).2.2.2.1⟩

lemma is_between_collinear {a b c : B.pts}
(h : B.is_between a b c) : collinear a b c := (B.B1 a b c h).2.2.2.2

lemma is_between_extend {a b : B.pts} (h : a ≠ b) :
∃ c : B.pts, B.is_between a b c := B.B2 a b h

lemma collinear_between {a b c : B.pts} (habc : collinear a b c) :
(B.is_between a b c ∨ B.is_between a c b ∨ B.is_between b a c)
∧ ¬(B.is_between a b c ∧ B.is_between a c b)
∧ ¬(B.is_between a b c ∧ B.is_between b a c)
∧ ¬(B.is_between a c b ∧ B.is_between b a c) :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩,
  exact B.B3 a b c l hl ⟨hal, hbl, hcl⟩
end

structure segment := (pt1 : B.pts) (pt2 : B.pts)

namespace segment

def inside (s : segment) : set B.pts := {x : B.pts | B.is_between s.pt1 x s.pt2} ∪ {s.pt1, s.pt2}

def mem (x : B.pts) (s : @segment B) : Prop := x ∈ s.inside

instance : has_mem B.pts (segment) := ⟨segment.mem⟩

end segment

def two_pt_segment (a b : B.pts) : segment := ⟨a, b⟩

notation a`-ₛ`b := two_pt_segment a b

lemma segment_pt1 {a b : B.pts} : (a-ₛb).pt1 = a := rfl

lemma segment_pt2 {a b : B.pts} : (a-ₛb).pt2 = b := rfl

lemma segment_rw (s : @segment B) : (s.pt1-ₛs.pt2) = s :=
by { induction s using segment.rec_on with pt1 pt2, unfold two_pt_segment }

lemma segment_inside (s : @segment B) :
s.inside = {x : B.pts | B.is_between s.pt1 x s.pt2} ∪ {s.pt1, s.pt2} := rfl

lemma in_segment (x : B.pts) (s : @segment B) :
x ∈ s ↔ x ∈ {x : B.pts | B.is_between s.pt1 x s.pt2} ∪ {s.pt1, s.pt2} :=
by { rw ←segment_inside, refl }

lemma pt_left_in_segment (a b : B.pts) : a ∈ (a-ₛb) :=
by { unfold two_pt_segment, rw in_segment, simp }

lemma pt_right_in_segment (a b : B.pts) : b ∈ (a-ₛb) :=
by { unfold two_pt_segment, rw in_segment, simp }

lemma segment_inside_comm {a b : B.pts} : (a-ₛb).inside = (b-ₛa).inside :=
begin
  rw [segment_inside, segment_inside, segment_pt1, segment_pt1, segment_pt2, segment_pt2],
  ext, simp, rw is_between_symm, tauto
end

lemma in_segment_comm {p a b : B.pts} : p ∈ (a-ₛb) ↔ p ∈ (b-ₛa) :=
begin
  rw [in_segment, in_segment, segment_pt1, segment_pt1, segment_pt2, segment_pt2], simp,
  rw is_between_symm, tauto
end

lemma segment_singleton (a : B.pts) : (a-ₛa).inside = {a} :=
begin
  rw segment_inside, ext1, rw [segment_pt1, segment_pt2], simp,
  intro haxa, exact absurd rfl (is_between_not_eq haxa).2.1
end

lemma in_segment_singleton {x a : B.pts} : x ∈ (a-ₛa) ↔ x = a :=
begin
  rw in_segment, rw [segment_pt1, segment_pt2], simp,
  intro haxa, exact absurd rfl (is_between_not_eq haxa).2.1
end

lemma segment_in_line (a b : B.pts) : (a-ₛb).inside ⊆ (a-ₗb) :=
begin
  have hal : a ∈ (a-ₗb), from pt_left_in_line a b,
  have hbl : b ∈ (a-ₗb), from pt_right_in_line a b,
  by_cases hab : a = b,
    rw hab, rw hab at hbl, rw segment_singleton, simp, exact hbl,
  rw segment_inside,
  apply union_subset,
  intros c hc, simp at hc,
  rcases is_between_collinear hc with ⟨m, hm, ham, hcm, hbm⟩,
  rw (two_pt_one_line (line_in_lines hab) hm hab ⟨hal, hbl⟩ ⟨ham, hbm⟩), exact hcm,
  intros x hx, simp at hx, cases hx with hx hx; rw hx,
  exact hal, exact hbl
end

lemma pasch {a b c : B.pts} (habc : noncollinear a b c) {l : set B.pts} (hl : l ∈ B.lines) :
a ∉ l → b ∉ l → c ∉ l → (l $ (a-ₛb).inside) →
((l $ (a-ₛc).inside) ∨ (l $ (b-ₛc).inside)) ∧ ¬((l $ (a-ₛc).inside) ∧ (l $ (b-ₛc).inside)) :=
begin
  intros ha hb hc hlab,
  have hd : ∃ d : B.pts, B.is_between a d b ∧ d ∈ l,
    rw segment_inside at hlab, unfold intersect set.nonempty at hlab, simp at hlab,
    rcases hlab with ⟨d, hdl, da | db | hadb⟩,
    rw da at hdl, exact absurd hdl ha,
    rw db at hdl, exact absurd hdl hb,
    exact ⟨d, hadb, hdl⟩,
  split,
  rcases (B.B4 a b c l hl habc ha hb hc hd).1 with ⟨p, hpl, h⟩,
  rw segment_inside, unfold intersect set.nonempty, simp,
  cases h with h h,
  left, exact ⟨p, hpl, by {right, right, exact h}⟩,
  right, rw segment_inside, simp, exact ⟨p, hpl, by {right, right, exact h}⟩,
  unfold intersect set.nonempty, rw segment_inside,
  have := (B.B4 a b c l hl habc ha hb hc hd).2,
  intros hf, simp at hf,
  rcases hf.1 with ⟨x, hxl, hx⟩,
  rcases hf.2 with ⟨y, hyl, hy⟩,
  rcases hx with hxa | hxc | hx,
  rw segment_pt1 at hxa, rw ←hxa at ha, exact absurd hxl ha,
  rw segment_pt2 at hxc, rw ←hxc at hc, exact absurd hxl hc,
  rcases hy with hy | hyb | hyc,
  exact (this x y hxl hyl) ⟨hx, hy⟩,
  rw segment_pt1 at hyb, rw ←hyb at hb, exact absurd hyl hb,
  rw segment_pt2 at hyc, simp at hyc, rw ←hyc at hc, exact absurd hyl hc
end

def same_side_line (l : set B.pts) (a b : B.pts) : Prop := ¬(l $ (a-ₛb).inside)

def diff_side_line (l : set B.pts) (a b : B.pts) : Prop :=
(l $ (a-ₛb).inside) ∧ a ∉ l ∧ b ∉ l

theorem plane_separation
{l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} (ha : a ∉ l) (hb : b ∉ l) :
(same_side_line l a b ∨ diff_side_line l a b)
∧ ¬(same_side_line l a b ∧ diff_side_line l a b) :=
begin
  unfold same_side_line diff_side_line, rw segment_inside,
  split,
  apply not_or_of_imp, intro h,
  exact ⟨h, ha, hb⟩,
  intro hf,
  exact hf.1 hf.2.1
end

lemma same_or_diff_line_strict
{l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} (ha : a ∉ l) (hb : b ∉ l) :
(same_side_line l a b ∨ diff_side_line l a b)
∧ ¬(same_side_line l a b ∧ diff_side_line l a b) :=
begin
  unfold same_side_line diff_side_line, rw segment_inside,
  split,
  rw or_and_distrib_left,
  split, exact or.comm.mp (em _),
  right, exact ⟨ha, hb⟩,
  push_neg,
  intros hf ht, exact absurd ht hf
end

lemma not_same_side_line {l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} (ha : a ∉ l) (hb : b ∉ l) :
¬(same_side_line l a b) ↔ (diff_side_line l a b) :=
begin
  split, intro hns,
  cases (same_or_diff_line_strict hl ha hb).1 with hs hd,
  exact absurd hs hns, exact hd,
  intros hd hs,
  exact absurd (by exact ⟨hs, hd⟩) (same_or_diff_line_strict hl ha hb).2
end

lemma not_diff_side_line {l ∈ B.lines} {a b : B.pts} (ha : a ∉ l) (hb : b ∉ l) :
¬(diff_side_line l a b) ↔ (same_side_line l a b)
:= by rw [←not_iff_not.mpr (not_same_side_line H ha hb), not_not]

lemma same_side_line_refl {l : set B.pts} (hl : l ∈ B.lines) {a : B.pts} (ha : a ∉ l) :
same_side_line l a a :=
begin
  unfold same_side_line intersect, 
  rw segment_singleton, rw not_nonempty_iff_eq_empty, ext1, simp,
  intros h hxa, rw hxa at h, exact ha h
end

lemma same_side_line_symm {l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} :
same_side_line l a b → same_side_line l b a :=
begin
  unfold same_side_line,
  rw segment_inside_comm, simp
end

lemma same_side_line_not_in {x y : B.pts} {l : set B.pts} (hl : l ∈ B.lines) :
same_side_line l x y → x ∉ l ∧ y ∉ l :=
begin
  intro hlxy, unfold same_side_line intersect at hlxy, rw not_nonempty_iff_eq_empty at hlxy, split,
  intro hxl, have : x ∈ l ∩ (x-ₛy).inside, simp, exact ⟨hxl, by {rw [segment_inside, segment_pt1], simp}⟩,
  rw hlxy at this, exact this,
  intro hyl, have : y ∈ l ∩ (x-ₛy).inside, simp, exact ⟨hyl, by {rw [segment_inside, segment_pt2], simp}⟩,
  rw hlxy at this, exact this
end

private lemma same_side_line_trans_noncollinear {l : set B.pts} (hl : l ∈ B.lines) {a b c : B.pts} :
noncollinear a b c → same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  unfold same_side_line, intros h hlab hlbc,
  rw segment_inside_comm at hlbc,
  intro hlac,
  replace h : noncollinear a c b,
    unfold noncollinear collinear, unfold noncollinear collinear at h,
    intro hf, apply h, rcases hf with ⟨l, hl, hal, hcl, hbl⟩,
    exact ⟨l, hl, hal, hbl, hcl⟩, 
  cases (pasch h hl (same_side_line_not_in hl hlab).1 (same_side_line_not_in hl hlbc).1 (same_side_line_not_in hl hlab).2 hlac).1 with hf hf,
  exact hlab hf, exact hlbc hf
end

lemma same_side_line_trans {l : set B.pts} (hl : l ∈ B.lines) {a b c : B.pts} :
same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  by_cases collinear a b c; intros hlab hlbc,
  by_cases hab : a = b, rw ←hab at hlbc, exact hlbc,
  by_cases hbc : b = c, rw hbc at hlab, exact hlab,
  by_cases hac : a = c, rw hac, exact same_side_line_refl hl (same_side_line_not_in hl hlbc).2,
  rcases h with ⟨m, hm, ham, hbm, hcm⟩,
  have hd : ∃ d : B.pts, d ∈ l ∧ d ∉ m,
    rcases two_pt_on_one_line hl with ⟨x, y, hxy, hxl, hyl⟩,
    have hlm : l ≠ m, intro hlm, rw ←hlm at ham, exact (same_side_line_not_in hl hlab).1 ham,
    by_contra, push_neg at h,
    exact hxy (two_line_one_pt hl hm hlm hxl (h x hxl) hyl (h y hyl)),
  rcases hd with ⟨d, hdl, hdm⟩,
  cases is_between_extend (show d ≠ a, by {intro hda, rw hda at hdm, exact hdm ham}) with e hdae,
  have hlae : same_side_line l a e,
    intro hlae, cases hlae with f hf,
    have hflae : f ∈ l ∧ f ∈ (a-ₗe),
      simp at hf,
      exact ⟨hf.1, segment_in_line a e hf.2⟩,
    have hdlae : d ∈ l ∧ d ∈ (a-ₗe),
      simp at hf,
      split, exact hdl,
      rcases is_between_collinear hdae with ⟨n, hn, hdn, han, hen⟩,
      have := (two_pt_one_line (line_in_lines (is_between_not_eq hdae).2.2) hn ((is_between_not_eq hdae).2.2) ⟨pt_left_in_line a e, pt_right_in_line a e⟩ ⟨han, hen⟩),
      rw this, exact hdn,
    have hneq : l ≠ (a-ₗe),
      intro hf, have := (same_side_line_not_in hl hlab).1, rw hf at this, exact this (pt_left_in_line a e),
    have hdf : d = f,
      from two_line_one_pt hl (line_in_lines (is_between_not_eq hdae).2.2) hneq hdlae.1 hdlae.2 hflae.1 hflae.2,
    rw hdf at hdae,
    rw segment_inside at hf, simp at hf,
    have := is_between_not_eq hdae,
    rcases hf.2 with hf | hf | hf,
    exact this.1 hf, exact this.2.1 hf,
  exact (collinear_between (is_between_collinear hf)).2.2.1 ⟨hf, hdae⟩,
  have hbae : noncollinear b a e,
    rintros ⟨n, hn, hbn, han, hen⟩,
    have hem : e ∈ m,
      rw two_pt_one_line hm hn hab ⟨ham, hbm⟩ ⟨han, hbn⟩, exact hen,
    have hd : d ∈ (a-ₗe),
      rcases is_between_collinear hdae with ⟨n, hn, hdn, han, hen⟩,
      have := (two_pt_one_line (line_in_lines (is_between_not_eq hdae).2.2) hn ((is_between_not_eq hdae).2.2) ⟨pt_left_in_line a e, pt_right_in_line a e⟩ ⟨han, hen⟩),
      rw this, exact hdn,
    have := two_pt_one_line hm (line_in_lines (is_between_not_eq hdae).2.2) (is_between_not_eq hdae).2.2 ⟨ham, hem⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩,
    rw ←this at hd,
    exact hdm hd,
  have hebc : noncollinear e b c,
    rintros ⟨n, hn, hen, hbn, hcn⟩,
    rw ←(two_pt_one_line hm hn hbc ⟨hbm, hcm⟩ ⟨hbn, hcn⟩) at hen,
    exact hbae ⟨m, hm, hbm, ham, hen⟩,
  have haec : noncollinear a e c,
    rintros ⟨n, hn, han, hen, hcn⟩,
    rw ←(two_pt_one_line hm hn hac ⟨ham, hcm⟩ ⟨han, hcn⟩) at hen,
    exact hbae ⟨m, hm, hbm, ham, hen⟩,
  have hlbe := same_side_line_trans_noncollinear hl hbae (same_side_line_symm hl hlab) hlae,
  have hlec := same_side_line_trans_noncollinear hl hebc (same_side_line_symm hl hlbe) hlbc,
  exact same_side_line_trans_noncollinear hl haec hlae hlec,
  exact same_side_line_trans_noncollinear hl h hlab hlbc
end

def same_side_pt (o a b : B.pts) : Prop :=
o ∉ (a-ₛb) ∧ collinear o a b

def diff_side_pt (o a b : B.pts) : Prop :=
o ∈ (a-ₛb) ∧ collinear o a b ∧ a ≠ o ∧ b ≠ o

lemma same_side_pt_not_eq {o a b : B.pts} (hoab : same_side_pt o a b) : a ≠ o ∧ b ≠ o :=
begin
  unfold same_side_pt at hoab, rw in_segment at hoab,
  split,
  intro hao, rw [hao, segment_pt1] at hoab,
  simp at hoab, exact hoab,
  intro hbo, rw [hbo, segment_pt2] at hoab,
  simp at hoab, exact hoab
end

theorem line_separation
{p a b : B.pts} (hpab : collinear p a b) (hap : a ≠ p) (hbp : b ≠ p) : 
(same_side_pt p a b ∨ diff_side_pt p a b) ∧
¬(same_side_pt p a b ∧ diff_side_pt p a b) :=
begin
  unfold same_side_pt diff_side_pt,
  split, by_cases hp : p ∈ (a-ₛb),
  right, exact ⟨hp, hpab, hap, hbp⟩,
  left, exact ⟨hp, hpab⟩,
  push_neg,
  intros h₁ h₂, exact absurd h₂ h₁.1
end

lemma not_same_side_pt
{p a b : B.pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p) :
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

lemma not_diff_side_pt
{p a b : B.pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬diff_side_pt p a b ↔ same_side_pt p a b) :=
by rw [←not_iff_not.mpr (not_same_side_pt hpab ha hb), not_not]

lemma same_side_pt_refl {a b : B.pts} (hab : a ≠ b) : same_side_pt a b b :=
begin
  split, rw in_segment_singleton, exact hab,
  exact ⟨a-ₗb, line_in_lines hab, pt_left_in_line a b, pt_right_in_line a b, pt_right_in_line a b⟩
end

lemma same_side_pt_symm {a b c : B.pts} :
same_side_pt a b c → same_side_pt a c b :=
begin
  unfold same_side_pt,
  intro habc, split,
  rw in_segment_comm, exact habc.1,
  rcases habc.2 with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨l, hl, hal, hcl, hbl⟩
end

lemma same_side_line_pt {a b c : B.pts} : same_side_pt a b c
↔ collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∀ {l : set B.pts}, l ∈ B.lines → a ∈ l → l ≠ (a-ₗb) → same_side_line l b c :=
begin
  split, intro habc, split, exact habc.2,
  have hab := (same_side_pt_not_eq habc).1.symm,
  have hac := (same_side_pt_not_eq habc).2.symm,
  split, exact hab,
  split, exact hac,
  intros l hl hal hlab,
  by_cases hbc : b = c, rw ←hbc,
  have hbl : b ∉ l,
    intro hbl, apply hab,
    exact two_line_one_pt hl (line_in_lines hab) hlab hal (pt_left_in_line a b) hbl (pt_right_in_line a b),
  exact same_side_line_refl hl hbl,
  rintros ⟨x, hxl, hxbc⟩,
  have hxab : x ∈ (a-ₗb),
    rcases habc.2 with ⟨l, hl, hal, hbl, hcl⟩,
    rw (two_pt_one_line (line_in_lines hab) hl hab ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨hal, hbl⟩),
    rw (two_pt_one_line hl (line_in_lines hbc) hbc ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩),
    exact (segment_in_line b c) hxbc,
  rw ←(two_line_one_pt hl (line_in_lines hab) hlab hal (pt_left_in_line a b) hxl hxab) at hxbc,
  rw segment_inside at hxbc, simp at hxbc,
  unfold same_side_pt at habc, rw in_segment at habc, simp at habc,
  exact habc.1 hxbc,
  rintro ⟨habc, h⟩,
  have : ∃ l ∈ B.lines, a ∈ l ∧ l ≠ (a-ₗb),
    rcases noncollinear_exist h.1 with ⟨d, habd⟩,
    use (a-ₗd),
    have had : a ≠ d, from (noncollinear_not_eq habd).2.2.symm,
    split, exact line_in_lines had,
    split, exact pt_left_in_line a d,
    intro hadab,
    exact habd ⟨a-ₗb, line_in_lines h.1, pt_left_in_line a b, pt_right_in_line a b, by {rw ←hadab, exact pt_right_in_line a d}⟩,
  rcases this with ⟨l, hl, hal, hlab⟩,
  have key := h.2.2 hl hal hlab,
  split,
  intro hf, apply key, exact ⟨a, hal, hf⟩,
  exact habc
end

lemma same_side_pt_trans {a b c d : B.pts} :
same_side_pt a b c → same_side_pt a c d → same_side_pt a b d :=
begin
  rw [same_side_line_pt, same_side_line_pt, same_side_line_pt],
  intros habc hacd,
  split,
  rcases habc.1 with ⟨l, hl, hal, hbl, hcl⟩,
  rcases hacd.1 with ⟨m, hm, ham, hcm, hdm⟩,
  rw two_pt_one_line hm hl hacd.2.1 ⟨ham, hcm⟩ ⟨hal, hcl⟩ at hdm,
  exact ⟨l, hl, hal, hbl, hdm⟩,
  split, exact habc.2.1,
  split, exact hacd.2.2.1,
  intros l hl hal hlab,
  have : (a-ₗc) = (a-ₗb),
    rcases habc.1 with ⟨l, hl, hal, hbl, hcl⟩,
    rw two_pt_one_line (line_in_lines habc.2.1) hl habc.2.1 ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨hal, hbl⟩,
    rw two_pt_one_line (line_in_lines hacd.2.1) hl hacd.2.1 ⟨pt_left_in_line a c, pt_right_in_line a c⟩ ⟨hal, hcl⟩,
  rw this at hacd,
  exact same_side_line_trans hl (habc.2.2.2 hl hal hlab) (hacd.2.2.2 hl hal hlab)
end

lemma is_between_diff_side_pt {a b c : B.pts} :
B.is_between a b c ↔ diff_side_pt b a c :=
begin
  unfold diff_side_pt, rw in_segment,
  split, intro habc,
  simp, split, right, right, exact habc,
  rcases is_between_collinear habc with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨⟨l, hl, hbl, hal, hcl⟩, (is_between_not_eq habc).1, (is_between_not_eq habc).2.2.symm⟩,
  simp, intros h hbac hab hcb,
  rcases h with h | h | h,
  exact absurd h.symm hab,
  exact absurd h.symm hcb,
  exact h
end

lemma is_between_same_side_pt {a b c : B.pts} :
B.is_between a b c ↔ same_side_pt a b c ∧ same_side_pt c a b :=
begin
  split, intro habc,
  unfold same_side_pt, rw in_segment,
  simp, split; split,
  intro hf, rcases hf with hab | hac | hbac,
  exact (is_between_not_eq habc).1 hab,
  exact (is_between_not_eq habc).2.1 hac,
  exact (collinear_between (is_between_collinear habc)).2.2.1 ⟨habc, hbac⟩,
  exact (is_between_collinear habc),
  intro hf, rcases hf with hacb | hca | hcb,
  exact (collinear_between (is_between_collinear habc)).2.1 ⟨habc, hacb⟩,
  exact (is_between_not_eq habc).2.1 hca.symm,
  exact (is_between_not_eq habc).2.2 hcb.symm,
  rcases is_between_collinear habc with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨l, hl, hcl, hal, hbl⟩,
  unfold same_side_pt, rw in_segment, simp, push_neg,
  intros h₁ habc h₂ hcab,
  rcases (collinear_between habc).1 with h | h | h,
  exact h, rw in_segment at h₂, simp at h₂, push_neg at h₂,
  exact absurd h h₂.2.2, exact absurd h h₁.2.2
end

lemma is_between_trans {a b c d : B.pts} :
B.is_between a b c → B.is_between b c d → B.is_between a b d ∧ B.is_between a c d :=
begin
  have : ∀ {a b c d : B.pts}, B.is_between a b c → B.is_between b c d → B.is_between a b d ,
    intros a b c d habc hbcd,
    rcases is_between_collinear habc with ⟨l, hl, hal, hbl, hcl⟩,
    rcases is_between_collinear hbcd with ⟨m, hm, hbm, hcm, hdm⟩,
    have h₁ : ¬same_side_pt b a c,
      rw not_same_side_pt ⟨l, hl, hbl, hal, hcl⟩ (is_between_not_eq habc).1 (is_between_not_eq habc).2.2.symm,
      exact is_between_diff_side_pt.mp habc,
    have h₂ :  same_side_pt b c d, from (is_between_same_side_pt.mp hbcd).1,
    rw is_between_diff_side_pt,
    rw two_pt_one_line hm hl (is_between_not_eq habc).2.2 ⟨hbm, hcm⟩ ⟨hbl, hcl⟩ at hdm,
    rw ←not_same_side_pt ⟨l, hl, hbl, hal, hdm⟩ (is_between_not_eq habc).1 (is_between_not_eq hbcd).2.1.symm,
    intro h₃, replace h₂ := same_side_pt_symm h₂,
    exact h₁ (same_side_pt_trans h₃ h₂),
  intros habc hbcd, split, exact this habc hbcd,
  rw is_between_symm at habc hbcd, rw is_between_symm,
  exact this hbcd habc
end

lemma is_between_trans' {a b c d : B.pts} :
B.is_between a b d → B.is_between b c d → B.is_between a b c ∧ B.is_between a c d :=
begin
  have : ∀ {a b c d : B.pts}, B.is_between a b d → B.is_between b c d → B.is_between a b c ,
    intros a b c d habd hbcd,
    rcases is_between_collinear habd with ⟨l, hl, hal, hbl, hdl⟩,
    rcases is_between_collinear hbcd with ⟨m, hm, hbm, hcm ,hdm⟩,
    rw two_pt_one_line hm hl (is_between_not_eq habd).2.2 ⟨hbm, hdm⟩ ⟨hbl, hdl⟩ at hcm,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hbl, hal, hcm⟩ (is_between_not_eq habd).1 (is_between_not_eq hbcd).1.symm],
    intro hbac, have hbad := same_side_pt_trans hbac (is_between_same_side_pt.mp hbcd).1,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hbl, hal, hdl⟩] at habd,
    exact habd hbad, exact habd.2.2.1, exact habd.2.2.2,
  intros habd hbcd,
  have habc := this habd hbcd,
  exact ⟨habc, (is_between_trans habc hbcd).2⟩
end

def ray (o a : B.pts) : set B.pts :=
{x : B.pts | same_side_pt o a x} ∪ {o}

lemma ray_singleton (a : B.pts) : ray a a = {a} :=
begin
  ext1, unfold ray same_side_pt, simp,
  intro hf, rw [in_segment, segment_pt1] at hf, simp at hf, exfalso, exact hf
end

lemma segment_in_ray (o a : B.pts) : (o-ₛa).inside ⊆ ray o a :=
begin
  unfold ray, rw segment_inside,
  intros x hx, simp at hx, simp,
  rcases hx with hx | hx | hx,
  rw [hx, segment_pt1], simp,
  rw hx, by_cases hao : a = o, rw hao, left, refl,
  right, split,
  rw segment_pt2, rw in_segment_singleton, exact ne.symm hao,
  exact ⟨(a-ₗo), line_in_lines hao, pt_right_in_line a o, pt_left_in_line a o, pt_left_in_line a o⟩,
  right, unfold same_side_pt, rw in_segment, simp, split,
  intro hf, rcases hf with hf | hf | hf,
  rw hf at hx, exact (is_between_not_eq hx).2.1 rfl,
  exact (is_between_not_eq hx).1 hf,
  rw is_between_symm at hx, exact (collinear_between (is_between_collinear hf)).2.1 ⟨hf, hx⟩,
  rcases (is_between_collinear hx) with ⟨l, hl, hol, hxl, hal⟩,
  exact ⟨l, hl, hol, hal, hxl⟩
end

lemma ray_in_line (o a : B.pts) : ray o a ⊆ (o-ₗa) :=
begin
  unfold ray same_side_pt, intros x hx,
  simp at hx, cases hx with hx hx,
  rw hx, exact pt_left_in_line o a,
  have hoa : o ≠ a, intro hoa, rw hoa at hx, rw [in_segment, segment_pt1] at hx, simp at hx, exact hx,
  rcases hx.2 with ⟨l, hl, hol, hal, hxl⟩,
  rw (two_pt_one_line (line_in_lines hoa) hl hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨hol, hal⟩), exact hxl
end

--Any good names lol
lemma t_shape_ray {a b : B.pts} {e : B.pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ ray b e, x ≠ b → same_side_line (a-ₗb) e x :=
begin
  intros x hxbe hxb, rintros ⟨f, hfab, hfex⟩,
  have heb : e ≠ b, intro heb, rw [heb, ray_singleton] at hxbe, simp at hxbe, exact hxb hxbe,
  have hfeb : f ∈ (e-ₗb),
    have hxeb : x ∈ (e-ₗb),
      rw line_comm, from (ray_in_line b e) hxbe,
    by_cases hex : e = x, rw [←hex, segment_singleton] at hfex, simp at hfex, rw hfex, exact pt_left_in_line e b,
    rw (two_pt_one_line (line_in_lines heb) (line_in_lines hex) hex ⟨pt_left_in_line e b, hxeb⟩ ⟨pt_left_in_line e x, pt_right_in_line e x⟩),
    exact (segment_in_line e x) hfex,
  have hebab : (e-ₗb) ≠ (a-ₗb),
    intro hebab, have heeb := pt_left_in_line e b, rw hebab at heeb, exact heab heeb,
  rw (two_line_one_pt (line_in_lines heb) (line_in_lines hab) hebab hfeb hfab (pt_right_in_line e b) (pt_right_in_line a b)) at hfex,
  rw segment_inside at hfex, unfold ray at hxbe, simp at hxbe hfex,
  rcases hfex with hfex | hfex | hfex, exact heb.symm hfex, exact hxb.symm hfex,
  rcases hxbe with hxbe | hxbe,
  exact hxb hxbe,
  unfold same_side_pt at hxbe, rw in_segment at hxbe, simp at hxbe, push_neg at hxbe, exact hxbe.1.2.2 hfex
end

lemma t_shape_segment {a b : B.pts} {e : B.pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (b-ₛe), x ≠ b → same_side_line (a-ₗb) e x :=
λ x hxbe hxb, t_shape_ray hab heab x ((segment_in_ray b e) hxbe) hxb

structure angle := (pt1 : B.pts) (vertex : B.pts) (pt2 : B.pts)

def inside_angle (α : @angle B) : set B.pts :=
{p : B.pts | same_side_line ((α.vertex)-ₗ(α.pt1)) α.pt2 p ∧ same_side_line (α.vertex-ₗα.pt2) α.pt1 p}

def three_pt_angle (a o b : B.pts) : angle := ⟨a, o, b⟩

notation `∠` := three_pt_angle

lemma crossbar (α : @angle B) {d : B.pts} (hd : d ∈ α.inside) (hbac : noncollinear α.pt1 α.vertex α.pt2) :
ray α.vertex d $ (α.pt1-ₛα.pt2).inside :=
begin
  unfold angle.inside at hd, simp at hd,
  set b := α.pt1, set a := α.vertex, set c := α.pt2,
  by_cases hac : a = c,
    rw hac, use c, unfold ray, rw [segment_inside, segment_pt1, segment_pt2], simp,
  by_cases hab : a = b,
    rw hab, use b, unfold ray, rw [segment_inside, segment_pt1, segment_pt2], simp,
  cases is_between_extend (ne.symm hac) with e hcae,
  have had : a ≠ d,
    intro had, rw ←had at hd, have hf := (same_side_line_not_in (line_in_lines hab) hd.1).2,
    have ht := pt_left_in_line a b, exact hf ht,
  have hec : e ≠ c,
    intro hec, rw hec at hcae, exact (is_between_not_eq hcae).2.1 rfl,
  have hecb : noncollinear e c b,
    rintros ⟨l, hl, hel, hcl, hbl⟩,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    rw (two_pt_one_line hm hl hec ⟨hem, hcm⟩ ⟨hel, hcl⟩) at ham,
    exact hbac ⟨l, hl, hbl, ham, hcl⟩,
  have hae : a ≠ e,
    intro hae, rw hae at hcae, exact (is_between_not_eq hcae).2.2 rfl,
  have h₁ : (((a-ₗd) $ (e-ₛb).inside) ∨ ((a-ₗd) $ (c-ₛb).inside)) ∧ ¬(((a-ₗd) $ (e-ₛb).inside) ∧ ((a-ₗd) $ (c-ₛb).inside)),
    apply pasch hecb (line_in_lines had),
    intro haed,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    rw ←(two_pt_one_line hm (line_in_lines had) hae ⟨ham, hem⟩ ⟨pt_left_in_line a d, haed⟩) at hf,
    rw (two_pt_one_line hm (line_in_lines hac) hac ⟨ham, hcm⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2, use d, rw [segment_inside, segment_pt1, segment_pt2], exact ⟨hf, by simp⟩,
    intro hacd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac) hac ⟨pt_left_in_line a d, hacd⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2, use d, rw [segment_inside, segment_pt1, segment_pt2], exact ⟨hf, by simp⟩,
    intro habd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab ⟨pt_left_in_line a d, habd⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at hf,
    unfold same_side_line at hd, apply hd.1, use d, rw [segment_inside, segment_pt1, segment_pt2], exact ⟨hf, by simp⟩,
    use a, split, exact pt_left_in_line a d,
    rw segment_inside, simp, right, right, rw is_between_symm at hcae, exact hcae,
  have hbeab : ∀ x ∈ (b-ₛe), x ≠ b → same_side_line (a-ₗb) e x,
    have heab : e ∉ (a-ₗb),
      have heac : e ∈ (a-ₗc),
        rcases (is_between_collinear hcae) with ⟨l, hl, hcl, hal, hel⟩,
        rw (two_pt_one_line (line_in_lines hac) hl hac ⟨pt_left_in_line a c, pt_right_in_line a c⟩ ⟨hal, hcl⟩),
        exact hel,
      intro heab, have habac : (a-ₗb) = (a-ₗc), from two_pt_one_line (line_in_lines hab) (line_in_lines hac) hae ⟨pt_left_in_line a b, heab⟩ ⟨pt_left_in_line a c, heac⟩,
      exact hbac ⟨(a-ₗb), line_in_lines hab, pt_right_in_line a b, pt_left_in_line a b, by {rw habac, exact pt_right_in_line a c}⟩,
    exact t_shape_segment hab heab,
  have haeac : (a-ₗe) = (a-ₗc),
    rcases (is_between_collinear hcae) with ⟨l, hl, hcl, hal, hel⟩,
    rw (two_pt_one_line (line_in_lines hae) hl hae ⟨pt_left_in_line a e, pt_right_in_line a e⟩ ⟨hal, hel⟩),
    rw (two_pt_one_line (line_in_lines hac) hl hac ⟨pt_left_in_line a c, pt_right_in_line a c⟩ ⟨hal, hcl⟩),
  have hbeac : ∀ x ∈ (b-ₛe), x ≠ e → same_side_line (a-ₗc) b x,
    have hbae : b ∉ (a-ₗe),
      rw haeac, intro hf, exact hbac ⟨(a-ₗc), line_in_lines hac, hf, pt_left_in_line a c, pt_right_in_line a c⟩, 
    intros x hxbe hxe, rw in_segment_comm at hxbe, rw ←haeac,
    exact t_shape_segment hae hbae x hxbe hxe,
  have hadab : ∀ x ∈ ray a d, x ≠ a → same_side_line (a-ₗb) d x,
    have hdba : d ∉ (b-ₗa), rw line_comm, from (same_side_line_not_in (line_in_lines hab) hd.1).2,
    rw line_comm a b, exact t_shape_ray (ne.symm hab) hdba,
  have hdbac : same_side_line (a-ₗc) d b, from same_side_line_symm (line_in_lines hac) hd.2,
  have h₂ : ¬((a-ₗd) $ (e-ₛb).inside),
    have hdcab := same_side_line_symm (line_in_lines hab) hd.1,
    rintros ⟨f, hf⟩, rw segment_inside_comm at hf, simp at hf,
    have hfb : f ≠ b,
      intro hfb, rw hfb at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at this,
      exact (same_side_line_not_in (line_in_lines hab) hd.1).2 this,
    have hfe : f ≠ e,
      intro hfe, rw hfe at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hae) hae ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this, exact (same_side_line_not_in (line_in_lines hac) hd.2).2 this,
    have hfa : f ≠ a,
      intro hfa, rw hfa at hf, have := pt_right_in_line e b,
      have heb : e ≠ b, from (noncollinear_not_eq hecb).2.2.symm,
      rw segment_inside_comm at hf,
      rw (two_pt_one_line (line_in_lines heb) (line_in_lines hae) hae ⟨segment_in_line e b hf.2, pt_left_in_line e b⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this,
      exact hbac ⟨(a-ₗc) ,line_in_lines hac, this, pt_left_in_line a c, pt_right_in_line a c⟩,
    specialize hbeab f hf.2 hfb,
    specialize hbeac f hf.2 hfe,
    have hdfac := same_side_line_trans (line_in_lines hac) hdbac hbeac,
    have hfad : f ∈ ray a d,
      unfold ray, simp, right, unfold same_side_pt, split,
      intro hadf, apply hdfac,
      exact ⟨a, pt_left_in_line a c, hadf⟩,
      exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hf.1⟩,
    specialize hadab f hfad hfa,
    have hedab := same_side_line_trans (line_in_lines hab) hbeab (same_side_line_symm (line_in_lines hab) hadab),
    have hecab := same_side_line_trans (line_in_lines hab) hedab hdcab,
    apply hecab, use a, split,
    exact pt_left_in_line a b,
    rw segment_inside, simp, right, right, exact (is_between_symm c a e).mp hcae,
    cases h₁.1 with h₁ h₁,
    exact absurd h₁ h₂,
  rcases h₁ with ⟨f, hfad, hfcb⟩,
  have : b ∉ (a-ₗc), from λ hf, hbac ⟨(a-ₗc), line_in_lines hac, hf, pt_left_in_line a c, pt_right_in_line a c⟩,
  have hcbac : ∀ x ∈ (c-ₛb), x ≠ c → same_side_line (a-ₗc) b x,
    from t_shape_segment hac this,
  have hfc : f ≠ c,
    intro hfc, rw hfc at hfad, have := pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac) hac ⟨pt_left_in_line a d, hfad⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at this,
    exact (same_side_line_not_in (line_in_lines hac) hd.2).2 this,
  specialize hcbac f hfcb hfc,
  have hdfac := same_side_line_trans (line_in_lines hac) hdbac hcbac,
  use f, split,
  unfold ray same_side_pt, simp, right, split,
  intro hf, apply hdfac, use a, exact ⟨pt_left_in_line a c, hf⟩,
  exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hfad⟩,
  rw segment_inside_comm, exact hfcb
end

structure incidence_order_congruence_geometry extends incidence_order_geometry :=
(line_congr : segment → segment → Prop)
--For an arbitrary segment and a ray, we find a unique congruent segment on the ray
(C1 : ∀ (a b : pts) (l : segment), ∃ c : pts, same_side_pt a b c ∧
line_congr l (a-ₛc) ∧ ∀ x : pts, same_side_pt a b x → line_congr l (a-ₛx) → x = c)
--This is equivalent to congruency being an equivalent relation
(C2 : ∀ s₁ s₂ s₃ : segment,
(line_congr s₁ s₂ → line_congr s₁ s₃ → line_congr s₂ s₃) ∧ line_congr s₁ s₁)
--This axiom deals with addition of segments.
(C3 : ∀ {a b c d e f: pts}, is_between a b c → is_between d e f → line_congr (a-ₛb) (d-ₛe)
                        → line_congr (b-ₛc) (e-ₛf) → line_congr (a-ₛc) (d-ₛf))
(angle_congr : angle → angle → Prop)
--Given any angle and a ray, we find a pt that together with the ray forms a congruent angle
--Also, this pt is unique on its side w.r.t the ray
(C4 : ∀ (α : angle) (a b : pts), ∃ c : pts, angle_congr α (∠c a b)
∧ ∀ x : pts, same_side_line (↑(line a b)) c x → angle_congr α (∠x a b) → x = c)
--Similar to C2
(C5 : ∀ α β γ : angle, (angle_congr α β → angle_congr α γ → angle_congr β γ) ∧ angle_congr α α)
--SAS!!!
(C6 : ∀ a b c d e f, line_congr (a-ₛb) (d-ₛe) → line_congr (a-ₛc) (d-ₛf) → angle_congr (∠b a c) (∠e d f)
→ line_congr (b-ₛc) (e-ₛf) ∧ angle_congr (∠a b c) (∠d e f) ∧ angle_congr (∠b c a) (∠e f d))

instance : has_coe incidence_order_congruence_geometry incidence_order_geometry :=
⟨incidence_order_congruence_geometry.to_incidence_order_geometry⟩

variables {C : incidence_order_congruence_geometry}

local notation a`≅ₛ`b := C.line_congr a b

lemma extend_congr_unique (a b : C.pts) (l : segment) :
∃ c : C.pts, same_side_pt a b c ∧ (l ≅ₛ (a-ₛc))
∧ ∀ x : C.pts, same_side_pt a b x ∧ (l ≅ₛ (a-ₛx)) → x = c :=
by {simp, exact C.C1 a b l}

lemma line_congr_refl (s : segment) : s ≅ₛ s := (C.C2 s s s).2

lemma line_congr_symm {s₁ s₂ : segment} :
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₁) := λ h, (C.C2 s₁ s₂ s₁).1 h (line_congr_refl s₁)

lemma line_congr_trans {s₁ s₂ s₃ : segment} : 
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₃) → (s₁ ≅ₛ s₃) := λ h₁ h₂, (C.C2 s₂ s₁ s₃).1 (line_congr_symm h₁) h₂

noncomputable def segment_add (m n : segment) : 
{ L : segment // (m.pt1 = m.pt2 → L = (m.pt1-ₛm.pt1)) ∧
(m.pt1 ≠ m.pt2 → ∃ p : C.pts, L = (m.pt1-ₛp) ∧ C.is_between m.pt1 m.pt2 p ∧ ((m.pt2-ₛp) ≅ₛ n)) } :=
begin
  set a := m.pt1 with hm₁, set b := m.pt2 with hm₂, set c := n.pt1 with hn₁, set d := n.pt2 with hn₂,
  by_cases hab : a = b,
  use (a-ₛa), exact ⟨λ h, rfl, λ h, absurd hab h⟩, 
  choose e habe using is_between_extend hab,
  choose f hbef hcdbf hf using extend_congr_unique b e (c-ₛd),
  use (a-ₛf), split, intro h, exact absurd h hab,
  intro hab, use f, split, exact rfl,
  rcases is_between_collinear habe with ⟨l, hl, hal, hbl, hel⟩,
  rcases hbef.2 with ⟨m, hm, hbm, hem, hfm⟩,
  rw ←two_pt_one_line hl hm (same_side_pt_not_eq hbef).1 ⟨hel, hbl⟩ ⟨hem, hbm⟩ at hfm,
  split, rw [is_between_diff_side_pt, ←not_same_side_pt], intro hbaf,
  rw [is_between_diff_side_pt, ←not_same_side_pt] at habe,
  exact habe (same_side_pt_trans hbaf (same_side_pt_symm hbef)),
  exact habe.2.1, exact hab, exact (same_side_pt_not_eq hbef).1,
  exact ⟨l, hl, hbl, hal, hfm⟩, exact hab, exact (same_side_pt_not_eq hbef).2,
  rw [hn₁, hn₂, segment_rw] at hcdbf, exact line_congr_symm hcdbf
end

notation a`+ₗ`b := segment_add a b

lemma congr_sum_segment {m m' n n' : segment} (hmpt : m.pt1 ≠ m.pt2) (hm'pt : m'.pt1 ≠ m'.pt2) :
(m ≅ₛ m') → (n ≅ₛ n') → ((m +ₗ n) ≅ₛ (m' +ₗ n')) :=
begin
  intros hmm' hnn',
  rcases (m +ₗ n).2.2 hmpt with ⟨a, hm₁a, hm₁m₂a, hm₂an₁n₂⟩,
  rcases (m' +ₗ n').2.2 hm'pt with ⟨b, hn₁b, hm₁m₂b', hm₂bn₁n₂'⟩,
  simp at hm₁a hn₁b, rw [hm₁a, hn₁b],
  have := line_congr_trans (line_congr_trans hm₂an₁n₂ hnn') (line_congr_symm hm₂bn₁n₂'),
  rw [←segment_rw m, ←segment_rw m'] at hmm',
  exact C.C3 hm₁m₂a hm₁m₂b' hmm' this
end

lemma congr_sub_segment {a b c d e f : C.pts} (habc : C.is_between a b c) (hdef : same_side_pt d e f)
(habde : (a-ₛb)≅ₛ(d-ₛe)) (hacdf : (a-ₛc)≅ₛ(d-ₛf)) : C.is_between d e f ∧ ((b-ₛc)≅ₛ(e-ₛf)) :=
begin
  rcases is_between_extend (same_side_pt_not_eq hdef).1.symm with ⟨x, hdex⟩,
  rcases extend_congr_unique e x (b-ₛc) with ⟨f', hexf', hbcef', hu⟩, simp at *,
  have hdef' : C.is_between d e f',
    rcases is_between_collinear hdex with ⟨l, hl, hdl, hel, hxl⟩,
    rcases hexf'.2 with ⟨m, hm, hem, hxm, hf'm⟩,
    rw (two_pt_one_line hm hl (same_side_pt_not_eq hexf').1 ⟨hxm, hem⟩ ⟨hxl, hel⟩) at hf'm,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hf'm⟩ (is_between_not_eq hdex).1 (same_side_pt_not_eq hexf').2],
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hxl⟩ (same_side_pt_not_eq hdef).1.symm (same_side_pt_not_eq hexf').1] at hdex,
    intro hedf', exact hdex (same_side_pt_trans hedf' (same_side_pt_symm hexf')),
  have hacdf' := C.C3 habc hdef' habde hbcef',
  have hff' : f = f',
    rcases extend_congr_unique d e (a-ₛc) with ⟨f'', -, -, hf''⟩, simp at hf'',
    rw [hf'' f hdef hacdf, hf'' f' (is_between_same_side_pt.mp hdef').1 hacdf'],
  rw hff', exact ⟨hdef', hbcef'⟩
end

def segment_lt (m n : segment) : Prop :=
∃ a : C.pts, C.is_between n.pt1 a n.pt2 ∧ (m ≅ₛ (n.pt1-ₛa))

local notation a`<ₗ`b := @segment_lt C a b

lemma segment_lt_congr {m n l : segment} (hmn : m ≅ₛ n) :
((m <ₗ l) → (n <ₗ l)) ∧ ((l <ₗ m) → (l <ₗ n)) :=
begin
  unfold segment_lt, split,
  rintros ⟨a, hl₁al₂, hm⟩,
  exact ⟨a, hl₁al₂, line_congr_trans (line_congr_symm hmn) hm⟩,
  rintros ⟨a, hm₁am₂, hl⟩,
  rcases extend_congr_unique n.pt1 n.pt2 (m.pt1-ₛa) with ⟨b, hnb, hm₁an₁b, -⟩,
  use b, split,
  rw [←segment_rw m, ←segment_rw n] at hmn,
  exact (congr_sub_segment hm₁am₂ (same_side_pt_symm hnb) hm₁an₁b hmn).1,
  exact line_congr_trans hl hm₁an₁b
end

lemma segment_lt_trans {m n l : segment} :
(m <ₗ n) → (n <ₗ l) → (m <ₗ l) :=
begin
  unfold segment_lt,
  rintros ⟨a, hna, hm⟩, rintros ⟨b, hlb, hn⟩,
  rcases (segment_lt_congr hn).2 ⟨a, hna, hm⟩ with ⟨c, hlc, hm'⟩,
  unfold two_pt_segment at hlc, simp at hlc,
  rw (show (l.pt1 -ₛ b).pt1 = l.pt1, by unfold two_pt_segment) at hm',
  use c, rw is_between_symm at hlb hlc,
  exact ⟨(is_between_symm _ _ _).mp (is_between_trans' hlb hlc).2, hm'⟩
end

lemma segment_tri (m n : segment) :
(m <ₗ n) ∨ (m ≅ₛ n) ∨ (n <ₗ m) :=
begin
  rcases extend_congr_unique n.pt1 n.pt2 m with ⟨a, hna, hm, -⟩,
  by_cases ha : a = n.pt2,
  rw [ha, segment_rw] at hm, right, left, exact hm,
  rcases hna.2 with ⟨l, hl, hn₁l, hn₂l, hal⟩,
  cases (line_separation ⟨l, hl, hn₂l, hn₁l, hal⟩ (same_side_pt_not_eq hna).1.symm ha).1 with hna' hna',
  left, use a, split, rw is_between_same_side_pt, exact ⟨same_side_pt_symm hna, hna'⟩, exact hm,
  right, right, rw ←is_between_diff_side_pt at hna',
  rcases extend_congr_unique m.pt1 m.pt2 n with ⟨b, hmb, hn, -⟩,
  use b, split,
  rw ←segment_rw n at hn, rw ←segment_rw m at hm,
  exact (congr_sub_segment hna' (same_side_pt_symm hmb) hn (line_congr_symm hm)).1,
  exact hn
end

local notation a`≅ₐ`b := C.angle_congr a b

lemma angle_congr_refl (α : angle) : α ≅ₐ α := (C.C5 α α α).2

lemma angle_congr_symm {α β : angle} :
(α ≅ₐ β) → (β ≅ₐ α) := λ h, (C.C5 α β α).1 h (angle_congr_refl α)

lemma angle_congr_trans {α β γ : angle} : 
(α ≅ₐ β) → (β ≅ₐ γ) → (α ≅ₐ γ) := λ h₁ h₂, (C.C5 β α γ).1 (angle_congr_symm h₁) h₂

def supplementary (α β : @angle C.to_incidence_order_geometry) : Prop :=
α.vertex = β.vertex ∧ α.pt1 = β.pt1 ∧ diff_side_pt α.vertex α.pt2 β.pt2

lemma supplementary_congr {α β α' β' : angle}
(hαβ : supplementary α β) (hγε : supplementary α' β') (hαα' : α ≅ₐ α') : β ≅ₐ β' :=
begin
  
end
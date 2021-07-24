import algebra.support
import set_theory.zfc

open set
open_locale classical

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

lemma one_pt_line (a : I.pts) : ∃ l ∈ I.lines, a ∈ l :=
begin
  have : ∃ b : I.pts, a ≠ b,
    by_contra hf, push_neg at hf,
    rcases I.I3 with ⟨x, y, z, h, -⟩, exact h ((hf x).symm.trans (hf y)),
  cases this with b hab,
  exact ⟨line a b, line_in_lines hab, pt_left_in_line a b⟩
end

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

structure segment := (inside : set B.pts)
(in_eq : ∃ a b : B.pts, inside = {x : B.pts | B.is_between a x b} ∪ {a, b})

def two_pt_segment (a b : B.pts) : segment := ⟨{x : B.pts | B.is_between a x b} ∪ {a, b}, ⟨a, b, rfl⟩⟩

notation a`-ₛ`b := two_pt_segment a b

noncomputable def p1 (α : @segment B) :
{a : B.pts // ∃ b : B.pts, α.inside = {x : B.pts | B.is_between a x b} ∪ {a, b}} :=
by {choose a h using α.in_eq, exact ⟨a, h⟩}

noncomputable def p2 (α : @segment B) :
{b : B.pts // α.inside = {x : B.pts | B.is_between (p1 α).1 x b} ∪ {(p1 α).1, b}} :=
by {choose b h using (p1 α).2, exact ⟨b, h⟩}

lemma segment_rw (s : @segment B) : s = ((p1 s).1 -ₛ (p2 s).1) :=
begin
  have := (p2 s).2, unfold two_pt_segment,
  induction s with I hI, simp only at this,
  simp only, exact this
end

lemma segment_symm {a b : B.pts} : (a-ₛb) = (b-ₛa) :=
by {unfold two_pt_segment, simp, ext, simp, rw is_between_symm, tauto}

lemma segment_singleton (a : B.pts) : (a-ₛa).inside = {a} :=
begin
  unfold two_pt_segment, ext1, simp,
  intro haxa, exact absurd rfl (is_between_not_eq haxa).2.1
end

lemma in_segment_singleton {a x : B.pts} : x ∈ (a-ₛa).inside ↔ x = a :=
by {rw segment_singleton, simp}

lemma segment_in_line (a b : B.pts) : (a-ₛb).inside ⊆ (a-ₗb) :=
begin
  have hal : a ∈ (a-ₗb), from pt_left_in_line a b,
  have hbl : b ∈ (a-ₗb), from pt_right_in_line a b,
  by_cases hab : a = b,
    rw hab, rw hab at hbl, rw segment_singleton, simp, exact hbl,
  unfold two_pt_segment,
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
    unfold two_pt_segment at hlab, unfold intersect set.nonempty at hlab, simp at hlab,
    rcases hlab with ⟨d, hdl, da | db | hadb⟩,
    rw da at hdl, exact absurd hdl ha,
    rw db at hdl, exact absurd hdl hb,
    exact ⟨d, hadb, hdl⟩,
  split,
  rcases (B.B4 a b c l hl habc ha hb hc hd).1 with ⟨p, hpl, h⟩,
  unfold two_pt_segment, unfold intersect set.nonempty, simp,
  cases h with h h,
  left, exact ⟨p, hpl, by {right, right, exact h}⟩,
  right, exact ⟨p, hpl, by {right, right, exact h}⟩,
  unfold intersect set.nonempty,
  have := (B.B4 a b c l hl habc ha hb hc hd).2,
  intros hf, simp at hf,
  rcases hf.1 with ⟨x, hxl, hx⟩,
  rcases hf.2 with ⟨y, hyl, hy⟩,
  rcases hx with hx | hxa | hxc,
  rotate, rw ←hxa at ha, exact absurd hxl ha,
  simp at hxc, rw ←hxc at hc, exact absurd hxl hc,
  rcases hy with hy | hyb | hyc,
  exact (this x y hxl hyl) ⟨hx, hy⟩,
  rw ←hyb at hb, exact absurd hyl hb,
  simp at hyc, rw ←hyc at hc, exact absurd hyl hc
end

lemma two_pt_between {a b : B.pts} (hab : a ≠ b) : ∃ c : B.pts, B.is_between a c b :=
begin
  cases noncollinear_exist hab with c habc,
  have hac := (noncollinear_not_eq habc).2.2.symm, have hbc := (noncollinear_not_eq habc).2.1,
  cases is_between_extend hac with d hacd,
  have had : a ≠ d, from (is_between_not_eq hacd).2.1,
  have hbd : b ≠ d,
    intro hbd, rw hbd at habc,
    rcases (is_between_collinear hacd) with ⟨l, hl, hal, hcl, hdl⟩,
    exact habc ⟨l, hl, hal, hdl, hcl⟩,
  have hcd : c ≠ d, from (is_between_not_eq hacd).2.2,
  cases is_between_extend hbd with e hbde,
  have hadb : noncollinear a d b,
    rintros ⟨l, hl, hal, hdl, hbl⟩,
    rcases (is_between_collinear hacd) with ⟨m, hm, ham, hcm, hdm⟩,
    rw two_pt_one_line hm hl had ⟨ham, hdm⟩ ⟨hal, hdl⟩ at hcm,
    exact habc ⟨l, hl, hal, hbl, hcm⟩,
  have hce : c ≠ e,
    intro hce, rw ←hce at hbde,
    rcases (is_between_collinear hbde) with ⟨l, hl, hbl, hdl, hcl⟩,
    rcases (is_between_collinear hacd) with ⟨m, hm, ham, hcm, hdm⟩,
    rw two_pt_one_line hm hl hcd ⟨hcm, hdm⟩ ⟨hcl, hdl⟩ at ham,
    exact habc ⟨l, hl, ham, hbl, hcl⟩,
  have hde : d ≠ e, from (is_between_not_eq hbde).2.2,
  have hbe : b ≠ e, from (is_between_not_eq hbde).2.1,
  rcases (is_between_collinear hbde) with ⟨l, hl, hbl, hdl, hel⟩,
  rcases (is_between_collinear hacd) with ⟨m, hm, ham, hcm, hdm⟩,
  have : a ∉ ↑(line c e) ∧ d ∉ ↑(line c e) ∧ b ∉ ↑(line c e),
    split, intro hace,
    have he := pt_right_in_line c e, rw two_pt_one_line (line_in_lines hce) hm hac ⟨hace, pt_left_in_line c e⟩ ⟨ham, hcm⟩ at he,
    rw (two_pt_one_line hl hm hde ⟨hdl, hel⟩ ⟨hdm, he⟩) at hbl,
    exact habc ⟨m, hm, ham, hbl, hcm⟩,
    split, intro hdce,
    have hc := pt_left_in_line c e, rw two_pt_one_line (line_in_lines hce) hl hde ⟨hdce, pt_right_in_line c e⟩ ⟨hdl, hel⟩ at hc,
    rw two_pt_one_line hl hm hcd ⟨hc, hdl⟩ ⟨hcm, hdm⟩ at hbl,
    exact habc ⟨m, hm, ham, hbl, hcm⟩,
    intro hbce,
    have hc := pt_left_in_line c e, rw two_pt_one_line (line_in_lines hce) hl hbe ⟨hbce, pt_right_in_line c e⟩ ⟨hbl, hel⟩ at hc,
    rw two_pt_one_line hl hm hcd ⟨hc, hdl⟩ ⟨hcm, hdm⟩ at hbl,
    exact habc ⟨m, hm, ham, hbl, hcm⟩,
  have intersect : (↑(line c e)$(a-ₛd).inside),
    use c, split, exact pt_left_in_line c e,
    unfold two_pt_segment, simp, right, right, exact hacd,
  cases (pasch hadb (line_in_lines hce) this.1 this.2.1 this.2.2 intersect).1 with key hf,
  cases key with x hx, unfold two_pt_segment at hx, simp at hx,
  rcases hx.2 with hxa | hxb | haxb,
  rw hxa at hx, exact absurd hx.1 this.1,
  rw hxb at hx, exact absurd hx.1 this.2.2,
  exact ⟨x, haxb⟩,
  cases hf with x hx, unfold two_pt_segment at hx, simp at hx,
  rcases hx.2 with hxd | hxb | hdxb,
  rw hxd at hx, exact absurd hx.1 this.2.1,
  rw hxb at hx, exact absurd hx.1 this.2.2,
  have hxl : x ∈ l,
    rcases is_between_collinear hdxb with ⟨n, hn, hdn, hxn, hbn⟩,
    rw two_pt_one_line hn hl hbd ⟨hbn, hdn⟩ ⟨hbl, hdl⟩ at hxn, exact hxn,
  have hcel : (c-ₗe) ≠ l,
    intro hcel, rw ←hcel at hdl, exact absurd hdl this.2.1,
  rw [←two_line_one_pt (line_in_lines hce) hl hcel (pt_right_in_line c e) hel hx.1 hxl, is_between_symm] at hdxb,
  exfalso, exact (collinear_between (is_between_collinear hbde)).2.1 ⟨hbde, hdxb⟩
end

def same_side_line (l : set B.pts) (a b : B.pts) : Prop := ¬(l $ (a-ₛb).inside)

def diff_side_line (l : set B.pts) (a b : B.pts) : Prop :=
(l $ (a-ₛb).inside) ∧ a ∉ l ∧ b ∉ l

theorem plane_separation
{l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} (ha : a ∉ l) (hb : b ∉ l) :
(same_side_line l a b ∨ diff_side_line l a b)
∧ ¬(same_side_line l a b ∧ diff_side_line l a b) :=
begin
  unfold same_side_line diff_side_line, unfold two_pt_segment,
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
  unfold same_side_line diff_side_line, unfold two_pt_segment,
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
by {unfold same_side_line, rw segment_symm, simp}

lemma same_side_line_not_in {x y : B.pts} {l : set B.pts} (hl : l ∈ B.lines) :
same_side_line l x y → x ∉ l ∧ y ∉ l :=
begin
  intro hlxy, unfold same_side_line intersect at hlxy, rw not_nonempty_iff_eq_empty at hlxy, split,
  intro hxl, have : x ∈ l ∩ (x-ₛy).inside, simp, exact ⟨hxl, by {unfold two_pt_segment, simp}⟩,
  rw hlxy at this, exact this,
  intro hyl, have : y ∈ l ∩ (x-ₛy).inside, simp, exact ⟨hyl, by {unfold two_pt_segment, simp}⟩,
  rw hlxy at this, exact this
end

private lemma same_side_line_trans_noncollinear {l : set B.pts} (hl : l ∈ B.lines) {a b c : B.pts} :
noncollinear a b c → same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  unfold same_side_line, intros h hlab hlbc,
  rw segment_symm at hlbc,
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
    unfold two_pt_segment at hf, simp at hf,
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
o ∉ (a-ₛb).inside ∧ collinear o a b

def diff_side_pt (o a b : B.pts) : Prop :=
o ∈ (a-ₛb).inside ∧ collinear o a b ∧ a ≠ o ∧ b ≠ o

lemma same_side_pt_not_eq {o a b : B.pts} (hoab : same_side_pt o a b) : a ≠ o ∧ b ≠ o :=
begin
  unfold same_side_pt at hoab, unfold two_pt_segment at hoab,
  split,
  intro hao, rw hao at hoab,
  simp at hoab, exact hoab,
  intro hbo, rw hbo at hoab,
  simp at hoab, exact hoab
end

theorem line_separation
{p a b : B.pts} (hpab : collinear p a b) (hap : a ≠ p) (hbp : b ≠ p) : 
(same_side_pt p a b ∨ diff_side_pt p a b) ∧
¬(same_side_pt p a b ∧ diff_side_pt p a b) :=
begin
  unfold same_side_pt diff_side_pt,
  split, by_cases hp : p ∈ (a-ₛb).inside,
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
  split, rw segment_singleton, exact hab,
  exact ⟨a-ₗb, line_in_lines hab, pt_left_in_line a b, pt_right_in_line a b, pt_right_in_line a b⟩
end

lemma same_side_pt_symm {a b c : B.pts} :
same_side_pt a b c → same_side_pt a c b :=
begin
  unfold same_side_pt,
  intro habc, split,
  rw segment_symm, exact habc.1,
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
  unfold two_pt_segment at hxbc, simp at hxbc,
  unfold same_side_pt at habc, unfold two_pt_segment at habc, simp at habc,
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
  unfold diff_side_pt, unfold two_pt_segment,
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
  unfold same_side_pt, unfold two_pt_segment,
  simp, split; split,
  intro hf, rcases hf with hab | hac | hbac,
  exact (is_between_not_eq habc).1 hab,
  exact (is_between_not_eq habc).2.1 hac,
  exact (collinear_between (is_between_collinear habc)).2.2.1 ⟨habc, hbac⟩,
  exact (is_between_collinear habc),
  intro hf, rcases hf with hca | hcb | hacb,
  exact (is_between_not_eq habc).2.1 hca.symm,
  exact (is_between_not_eq habc).2.2 hcb.symm,
  exact (collinear_between (is_between_collinear habc)).2.1 ⟨habc, hacb⟩,
  rcases is_between_collinear habc with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨l, hl, hcl, hal, hbl⟩,
  unfold same_side_pt, unfold two_pt_segment, simp, push_neg,
  intros h₁ habc h₂ hcab,
  rcases (collinear_between habc).1 with h | h | h,
  exact h, exact absurd h h₂.2.2, exact absurd h h₁.2.2
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

private lemma two_pt_segment_pt_prep {a b a' b' : B.pts} :
(a-ₛb) = (a'-ₛb') → a = a' → b = b' :=
begin
  intros haba'b' haa',
  replace haba'b' : (a-ₛb).inside = (a-ₛb').inside, rw [haba'b', ←haa'],
  by_cases hab : a = b, rw hab at haba'b',
    rw segment_singleton at haba'b',
    by_contra hbb', cases (two_pt_between hbb') with x hbxb',
    have hx : x ∈ (b-ₛb').inside,
      unfold two_pt_segment, simp, right, right, exact hbxb',
    rw ←haba'b' at hx, simp at hx, exact (is_between_not_eq hbxb').1 hx.symm,
  by_cases hab' : a = b', rw hab' at haba'b',
    rw segment_singleton at haba'b',
    by_contra hbb', cases (two_pt_between hbb') with x hbxb',
    have hx : x ∈ (b-ₛb').inside,
      unfold two_pt_segment, simp, right, right, exact hbxb',
    rw [segment_symm, haba'b'] at hx, simp at hx, exact (is_between_not_eq hbxb').2.2 hx,
  by_cases habb' : collinear a b b',
    rcases (collinear_between habb').1 with h | h | h,
    cases (two_pt_between (is_between_not_eq h).2.2) with x hbxb',
    have haxb' := (is_between_trans' h hbxb').2,
    have h₁ : x ∈ (a-ₛb').inside,
      unfold two_pt_segment, simp, right, right, exact haxb',
    have h₂ : x ∉ (a-ₛb).inside,
      unfold two_pt_segment, simp, intro hf,
      rcases hf with hf | hf | hf,
      exact (is_between_not_eq (is_between_trans' h hbxb').2).1 hf.symm,
      exact (is_between_not_eq hbxb').1 hf.symm,
      have habx := (is_between_trans' h hbxb').1,
      exact (collinear_between (is_between_collinear hf)).2.1 ⟨hf, habx⟩,
    rw haba'b' at h₂, exact absurd h₁ h₂,
    cases (two_pt_between (is_between_not_eq h).2.2) with x hb'xb,
    have haxb := (is_between_trans' h hb'xb).2,
    have h₁ : x ∈ (a-ₛb).inside,
      unfold two_pt_segment, simp, right, right, exact haxb,
    have h₂ : x ∉ (a-ₛb').inside,
      unfold two_pt_segment, simp, intro hf,
      rcases hf with hf | hf | hf,
      exact (is_between_not_eq (is_between_trans' h hb'xb).2).1 hf.symm,
      exact (is_between_not_eq hb'xb).1 hf.symm,
      have hab'x := (is_between_trans' h hb'xb).1,
      exact (collinear_between (is_between_collinear hf)).2.1 ⟨hf, hab'x⟩,
    rw haba'b' at h₁, exact absurd h₁ h₂,
    cases (two_pt_between hab) with x haxb,
    have h₁ : x ∈ (a-ₛb).inside,
      unfold two_pt_segment, simp, right, right, exact haxb,
    have h₂ : x ∉ (a-ₛb').inside,
      unfold two_pt_segment, simp, intro hf,
      rw is_between_symm at h,
      rcases hf with hf | hf | hf,
      exact (is_between_not_eq haxb).1 hf.symm,
      exact (is_between_not_eq (is_between_trans' h haxb).2).1 hf.symm,
      have hb'ax := (is_between_trans' h haxb).1,
      rw is_between_symm at hf,
      exact (collinear_between (is_between_collinear hf)).2.1 ⟨hf, hb'ax⟩,
    rw haba'b' at h₁, exact absurd h₁ h₂,
    cases (two_pt_between hab) with x haxb,
    have h : x ∈ (a-ₛb').inside,
      rw ←haba'b', unfold two_pt_segment, simp, right, right, exact haxb,
    unfold two_pt_segment at h, simp at h, rcases h with h | h | h,
    exact absurd h (is_between_not_eq haxb).1.symm,
    rw h at haxb, rcases (is_between_collinear haxb) with ⟨l, hl, hal, hb'l, hbl⟩,
    exfalso, exact habb' ⟨l, hl, hal, hbl, hb'l⟩,
    rcases (is_between_collinear haxb) with ⟨l, hl, hal, hxl, hbl⟩,
    rcases (is_between_collinear h) with ⟨m, hm, ham, hxm, hb'm⟩,
    rw two_pt_one_line hm hl (is_between_not_eq haxb).1 ⟨ham, hxm⟩ ⟨hal, hxl⟩ at hb'm,
    exfalso, exact habb' ⟨l, hl, hal, hbl, hb'm⟩
end

lemma two_pt_segment_pt (a b : B.pts) :
((p1 (a-ₛb)).1 = a ∧ (p2 (a-ₛb)).1 = b)
∨ (p1 (a-ₛb)).1 = b ∧ (p2 (a-ₛb)).1 = a :=
begin
  have h₁ : (p1 (a-ₛb)).1 = a → (p2 (a-ₛb)).1 = b,
    from two_pt_segment_pt_prep (segment_rw (a-ₛb)).symm,
  have h₂ : (p1 (a-ₛb)).1 = b → (p2 (a-ₛb)).1 = a,
    rw segment_symm, from two_pt_segment_pt_prep (segment_rw (b-ₛa)).symm,
  have h₃ : (p1 (a-ₛb)).1 = a ∨ (p1 (a-ₛb)).1 = b,
    have : (a-ₛb).inside = ((p1 (a-ₛb)).val-ₛ(p2 (a-ₛb)).val).inside,
      rw ←segment_rw (a-ₛb),
    by_cases hab : a = b,
    rw hab, simp, rw hab at this,
    have hb : ↑(p1 (b-ₛb)) ∈ ((p1 (b-ₛb)).val-ₛ(p2 (b-ₛb)).val).inside,
      unfold two_pt_segment, simp,
    rw ←this at hb, exact in_segment_singleton.mp hb,
    unfold two_pt_segment at this, simp only at this,
    by_contra hf₁, push_neg at hf₁,
    have hf₂ : (p2 (a-ₛb)).val ≠ a ∧ (p2 (a-ₛb)).val ≠ b,
      have := (segment_rw (a-ₛb)), rw @segment_symm B (p1 (a-ₛb)).val _ at this,
      split; intro hf, exact hf₁.2 (two_pt_segment_pt_prep this.symm hf),
      rw segment_symm at this,
      have := two_pt_segment_pt_prep this.symm, rw segment_symm at this,
      exact hf₁.1 (this hf),
    have ha : B.is_between ↑(p1 (a-ₛb)) a ↑(p2 (a-ₛb)),
      suffices ha : a ∈ {x : B.to_incidence_geometry.pts | B.is_between a x b} ∪ {a, b},
        rw this at ha, simp at ha,
      rcases ha with ha | ha | ha,
      exact absurd ha hf₁.1.symm, exact absurd ha hf₂.1.symm, exact ha, simp,
    have hb : B.is_between ↑(p1 (a-ₛb)) b ↑(p2 (a-ₛb)),
      suffices hb : b ∈ {x : B.to_incidence_geometry.pts | B.is_between a x b} ∪ {a, b},
        rw this at hb, simp at hb,
      rcases hb with hb | hb | hb,
      exact absurd hb hf₁.2.symm, exact absurd hb hf₂.2.symm, exact hb, simp,
    rcases (is_between_collinear ha) with ⟨m, hm, h1m, ham, h2m⟩,
    rcases (is_between_collinear hb) with ⟨n, hn, h1n, hbn, h2n⟩,
    rw two_pt_one_line hm hn (is_between_not_eq ha).2.1 ⟨h1m, h2m⟩ ⟨h1n, h2n⟩ at ham,
    cases (line_separation ⟨n, hn, ham, hbn, h1n⟩ (ne.symm hab) hf₁.1).1 with hab1 hab1,
    replace hab1 : B.is_between a b ↑(p1 (a-ₛb)),
      rw is_between_same_side_pt, split, exact hab1,
      rw is_between_same_side_pt at ha hb, exact same_side_pt_trans ha.1 (same_side_pt_symm hb.1),
    cases (two_pt_between hf₁.2) with x h1xb,
    have hx : x ∈ {x : B.pts | B.is_between a x b} ∪ {a, b},
      rw this, simp, right, right, rw is_between_symm at hb h1xb,
      rw is_between_symm, exact (is_between_trans' hb h1xb).2,
    have habx : B.is_between a b x,
      rw is_between_symm at h1xb, exact (is_between_trans' hab1 h1xb).1,
    simp at hx, rcases hx with hx | hx | hx,
    exact (is_between_not_eq habx).2.1 hx.symm,
    exact (is_between_not_eq h1xb).2.2 hx,
    exact (collinear_between (is_between_collinear hx)).2.1 ⟨hx, habx⟩,
    rw ←is_between_diff_side_pt at hab1,
    cases (two_pt_between hf₁.1) with x h1xa,
    have hx : x ∈ {x : B.pts | B.is_between a x b} ∪ {a, b},
      rw this, simp, right, right,
      rw is_between_symm at ha h1xa, rw is_between_symm,
      exact (is_between_trans' ha h1xa).2,
    have hxab : B.is_between x a b,
      rw is_between_symm at h1xa, rw is_between_symm,
      exact (is_between_trans' hab1 h1xa).1,
    simp at hx, rcases hx with hx | hx | hx,
    exact (is_between_not_eq h1xa).2.2 hx,
    exact (is_between_not_eq hxab).2.1 hx,
    exact (collinear_between (is_between_collinear hx)).2.2.1 ⟨hx, hxab⟩,
  cases h₃ with h₃ h₃,
  left, exact ⟨h₃, h₁ h₃⟩,
  right, exact ⟨h₃, h₂ h₃⟩
end

structure ray := (vertex : B.pts) (inside : set B.pts)
(in_eq : ∃ a : B.pts, inside = {x : B.pts | same_side_pt vertex a x} ∪ {vertex})

def two_pt_ray (o a : B.pts) : ray := ⟨o, {x : B.pts | same_side_pt o a x} ∪ {o}, ⟨a, rfl⟩⟩

lemma two_pt_ray_vertex (o a :B.pts) : (two_pt_ray o a).vertex = o := rfl

namespace ray

def mem (x : B.pts) (s : @ray B) : Prop := x ∈ s.inside

instance : has_mem B.pts ray := ⟨ray.mem⟩

end ray

lemma ray_unique {r₁ r₂ : ray} (hr₁r₂ : r₁.vertex = r₂.vertex) :
(∃ x : B.pts, x ≠ r₁.vertex ∧ x ∈ r₁.inside ∩ r₂.inside) → r₁ = r₂ :=
begin
  rintros ⟨a, ha1, ha⟩,
  suffices : r₁.inside = r₂.inside,
    induction r₁ with v₁ I₁ hI₁, induction r₂ with v₂ I₂ hI₂ generalizing v₁ I₁ hI₁,
    simp, exact ⟨hr₁r₂, this⟩,
  cases r₁.in_eq with x h₁,
  cases r₂.in_eq with y h₂,
  replace h₁ : r₁.inside = {x : B.pts | same_side_pt r₁.vertex x a} ∪ {r₁.vertex},
    rw h₁, ext p, simp,
    have : same_side_pt r₁.vertex x p ↔ same_side_pt r₁.vertex p a,
      rw h₁ at ha, simp at ha, split; intro h; cases ha.1 with ha ha,
      exact absurd ha ha1, exact same_side_pt_trans (same_side_pt_symm h) ha,
      exact absurd ha ha1, exact same_side_pt_trans ha (same_side_pt_symm h),
    rw this,
  rw [h₁, h₂], ext p, simp, rw hr₁r₂,
  have : same_side_pt r₂.vertex p a ↔ same_side_pt r₂.vertex y p,
    rw h₂ at ha, simp at ha, cases ha.2 with ha ha,
    rw hr₁r₂ at ha1, exact absurd ha ha1,
    split; intro h,
    exact same_side_pt_trans ha (same_side_pt_symm h),
    exact same_side_pt_trans (same_side_pt_symm h) ha,
  rw this
end

lemma ray_same_side {o a b : B.pts} (hoab : same_side_pt o a b) : two_pt_ray o a = two_pt_ray o b :=
begin
  unfold two_pt_ray, simp only [true_and, eq_self_iff_true], ext, simp,
  have : same_side_pt o a x ↔ same_side_pt o b x,
    split; intro h, exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  rw this
end

lemma ray_singleton (a : B.pts) : (two_pt_ray a a).inside = {a} :=
begin
  ext1, unfold two_pt_ray same_side_pt, simp,
  intro hf, unfold two_pt_segment at hf, simp at hf, exfalso, exact hf
end

lemma ray_disjoint {s₁ s₂ : @ray B} (hvertex : s₁.vertex = s₂.vertex) :
s₁ ≠ s₂ → s₁.inside ∩ s₂.inside = {s₁.vertex} :=
begin
  contrapose!, intro h,
  refine ray_unique hvertex _,
  by_contra hf, push_neg at hf,
  apply h, apply subset.antisymm, intro y, contrapose!, exact hf y,
  simp, cases s₁.in_eq, rw h_1, cases s₂.in_eq, rw h_2, rw hvertex, simp
end

lemma ray_reconstruct (r : ray) : ∃ a : B.pts, r = two_pt_ray r.vertex a :=
begin
  cases r.in_eq with x hx, use x, unfold two_pt_ray,
  induction r with v I hI, simp,
  simp at hx, rw hx
end

lemma in_ray_singleton (x a : B.pts) : x ∈ two_pt_ray a a ↔ x = a :=
begin
  unfold two_pt_ray ray.mem, split,
  intro h, cases h with h h,
  simp at h, exfalso, exact (same_side_pt_not_eq h).1 rfl, exact h,
  intro h, right, exact h
end

lemma ray_singleton_iff_eq {o a p : B.pts} : (two_pt_ray o a).inside = {p} ↔ o = a ∧ o = p :=
begin
  by_cases hoa : o = a,
    rw [hoa, ray_singleton], simp,
  split; intro h,
  have : ∀ x ∈ (two_pt_ray o a).inside, x = p, rw h, simp, unfold two_pt_ray at this, simp at this,
  rw this.2 a (same_side_pt_refl hoa), exact ⟨this.1, this.1⟩,
  exact absurd h.1 hoa
end

lemma pt_left_in_ray (o a : B.pts) : o ∈ (two_pt_ray o a).inside :=
by {unfold two_pt_ray, simp}

lemma pt_right_in_ray (o a : B.pts) : a ∈ (two_pt_ray o a).inside :=
begin
  by_cases hoa : o = a,
    rw [hoa, ray_singleton], exact rfl,
  unfold two_pt_ray, simp, right, exact same_side_pt_refl (hoa)
end

lemma segment_in_ray (o a : B.pts) : (o-ₛa).inside ⊆ (two_pt_ray o a).inside :=
begin
  unfold two_pt_ray, unfold two_pt_segment,
  intros x hx, simp at hx, simp,
  rcases hx with hx | hx | hx,
  rw hx, simp,
  rw hx, by_cases hao : a = o, rw hao, left, refl,
  right, split,
  rw segment_singleton, exact ne.symm hao,
  exact ⟨(a-ₗo), line_in_lines hao, pt_right_in_line a o, pt_left_in_line a o, pt_left_in_line a o⟩,
  right, unfold same_side_pt, unfold two_pt_segment, simp, split,
  intro hf, rcases hf with hf | hf | hf,
  rw hf at hx, exact (is_between_not_eq hx).2.1 rfl,
  exact (is_between_not_eq hx).1 hf,
  rw is_between_symm at hx, exact (collinear_between (is_between_collinear hf)).2.1 ⟨hf, hx⟩,
  rcases (is_between_collinear hx) with ⟨l, hl, hol, hxl, hal⟩,
  exact ⟨l, hl, hol, hal, hxl⟩
end

lemma ray_in_line (o a : B.pts) : (two_pt_ray o a).inside ⊆ (o-ₗa) :=
begin
  unfold two_pt_ray same_side_pt, intros x hx,
  simp at hx, cases hx with hx hx,
  rw hx, exact pt_left_in_line o a,
  have hoa : o ≠ a, intro hoa, rw hoa at hx, unfold two_pt_segment at hx, simp at hx, exact hx,
  rcases hx.2 with ⟨l, hl, hol, hal, hxl⟩,
  rw (two_pt_one_line (line_in_lines hoa) hl hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨hol, hal⟩), exact hxl
end

lemma ray_collinear {o a b : B.pts} (hoab : same_side_pt o a b) : two_pt_ray o a = two_pt_ray o b :=
begin
  unfold two_pt_ray,
  have : {x : B.to_incidence_geometry.pts | same_side_pt o a x} = {x : B.to_incidence_geometry.pts | same_side_pt o b x},
    ext, simp, split; intro h,
    exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  simp, rw this
end

--Any good names lol
lemma t_shape_ray {a b : B.pts} {e : B.pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ two_pt_ray b e, x ≠ b → same_side_line (a-ₗb) e x :=
begin
  intros x hxbe hxb, rintros ⟨f, hfab, hfex⟩,
  have heb : e ≠ b, intro heb, rw [heb, in_ray_singleton] at hxbe, exact hxb hxbe,
  have hfeb : f ∈ (e-ₗb),
    have hxeb : x ∈ (e-ₗb),
      rw line_comm, from (ray_in_line b e) hxbe,
    by_cases hex : e = x, rw [←hex, segment_singleton] at hfex, simp at hfex, rw hfex, exact pt_left_in_line e b,
    rw (two_pt_one_line (line_in_lines heb) (line_in_lines hex) hex ⟨pt_left_in_line e b, hxeb⟩ ⟨pt_left_in_line e x, pt_right_in_line e x⟩),
    exact (segment_in_line e x) hfex,
  have hebab : (e-ₗb) ≠ (a-ₗb),
    intro hebab, have heeb := pt_left_in_line e b, rw hebab at heeb, exact heab heeb,
  rw (two_line_one_pt (line_in_lines heb) (line_in_lines hab) hebab hfeb hfab (pt_right_in_line e b) (pt_right_in_line a b)) at hfex,
  unfold two_pt_segment at hfex, unfold two_pt_ray at hxbe, simp at hxbe hfex,
  rcases hfex with hfex | hfex | hfex, exact heb.symm hfex, exact hxb.symm hfex,
  rcases hxbe with hxbe | hxbe,
  exact hxb hxbe,
  simp at hxbe, unfold same_side_pt at hxbe, unfold two_pt_segment at hxbe, simp at hxbe, push_neg at hxbe, exact hxbe.1.2.2 hfex
end

lemma t_shape_segment {a b : B.pts} {e : B.pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (b-ₛe).inside, x ≠ b → same_side_line (a-ₗb) e x :=
λ x hxbe hxb, t_shape_ray hab heab x ((segment_in_ray b e) hxbe) hxb

--set of pts, ∃ a b c ...,
structure angle := (inside : set B.pts) (vertex : B.pts)
(h_ray : ∃ r₁ r₂ : ray, r₁.vertex = vertex ∧ r₂.vertex = vertex ∧ inside = r₁.inside ∪ r₂.inside)

lemma vertex_in_angle (α : @angle B) : α.vertex ∈ α.inside :=
by {rcases α.h_ray with ⟨r₁, r₂, -, h₁, h₂⟩, rw h₂, cases r₂.in_eq, rw [h, ←h₁], simp}

noncomputable def r1 (α : @angle B) :
{r₁ : ray // ∃ r₂ : ray, r₁.vertex = α.vertex ∧ r₂.vertex = α.vertex
             ∧ α.inside = r₁.inside ∪ r₂.inside} :=
by {choose r₁ h using α.h_ray, exact ⟨r₁, h⟩}

noncomputable def r2 (α : @angle B) :
{r₂ : ray // (r1 α).1.vertex = α.vertex ∧ r₂.vertex = α.vertex
             ∧ α.inside = (r1 α).1.inside ∪ r₂.inside} :=
by {choose r₂ h using (r1 α).2, exact ⟨r₂, h⟩}

def three_pt_angle (a o b : B.pts) : angle := ⟨(two_pt_ray o a).inside∪(two_pt_ray o b).inside, o,
by {use [two_pt_ray o a, two_pt_ray o b], unfold two_pt_ray, simp}⟩

notation `∠` := three_pt_angle

lemma angle_symm {a o b : B.pts} : ∠ a o b = ∠ b o a :=
by {unfold three_pt_angle, simp, rw union_comm}

lemma r1_vertex (a o b : B.pts) : (r1 (∠a o b)).1.vertex = o :=
by {cases (r1 (∠a o b)).2 with x hx, rw hx.1, unfold three_pt_angle}

lemma r2_vertex (a o b : B.pts) : (r2 (∠a o b)).1.vertex = o :=
by {cases (r2 (∠a o b)).2 with x hx, rw hx.1, unfold three_pt_angle}

lemma three_pt_angle_vertex (a o b : B.pts) : (∠ a o b).vertex = o :=
by unfold three_pt_angle

lemma pt_left_in_three_pt_angle (a o b : B.pts) : a ∈ (∠ a o b).inside :=
begin
  unfold three_pt_angle two_pt_ray, simp, left,
  by_cases a = o, left, exact h,
  right, exact (same_side_pt_refl (ne.symm h))
end

lemma pt_right_in_three_pt_angle (a o b : B.pts) : b ∈ (∠ a o b).inside :=
by {rw angle_symm, exact pt_left_in_three_pt_angle b o a}

lemma angle_same_side (a : B.pts) {o b c : B.pts} (hobc : same_side_pt o b c) : ∠ a o b = ∠ a o c :=
by {unfold three_pt_angle, simp, rw ray_same_side hobc}

private lemma three_pt_angle_ray_prep {a b c d e f : B.pts} (h : ∠ a b c = ∠ d e f)
(hbc : b ≠ c) (hef : e ≠ f) : two_pt_ray b a = two_pt_ray e d → two_pt_ray b c = two_pt_ray e f :=
begin
  intro hbaed,
  have hbe : b = e,
    suffices : (two_pt_ray b a).vertex = (two_pt_ray e d).vertex,
      unfold two_pt_ray at this, simp at this, exact this,
    rw hbaed,
  replace h : (∠ a b c).inside = (∠ d e f).inside, rw h,
  unfold three_pt_angle at h, simp at h,
  rw ←hbe at *, rw ←hbaed at h,
  by_cases hbac : same_side_pt b a c,
    have : (two_pt_ray b a).inside = (two_pt_ray b c).inside,
      unfold two_pt_ray, simp only, ext, simp,
      split; intro h;
      cases h with h h, left, exact h,
      right, exact same_side_pt_trans (same_side_pt_symm hbac) h,
      left, exact h,
      right, exact same_side_pt_trans hbac h,
    rw [←this, eq_comm] at h, simp at h,
    have : two_pt_ray b a = two_pt_ray b c,
      unfold two_pt_ray, simp only, split, exact rfl,
      ext, simp, split; intro h;
      cases h with h h, left, exact h,
      right, exact same_side_pt_trans (same_side_pt_symm hbac) h,
      left, exact h,
      right, exact same_side_pt_trans hbac h,
    rw ←this,
    replace h := sup_eq_left.mp h, simp at h,
    refine ray_unique _ _, unfold two_pt_ray, simp,
    cases two_pt_between hef with x hbxf, use x, split,
    unfold two_pt_ray, simp, exact (is_between_not_eq hbxf).1.symm,
    split, apply h, left, simp, exact same_side_pt_symm (is_between_same_side_pt.mp hbxf).1,
    left, simp, exact same_side_pt_symm (is_between_same_side_pt.mp hbxf).1,
  cases (two_pt_between hbc) with x hbxc,
  have h₁ : x ∈ (two_pt_ray b a).inside ∪ (two_pt_ray b f).inside,
    rw ←h, simp, right, unfold two_pt_ray, simp, right,
    exact same_side_pt_symm (is_between_same_side_pt.mp hbxc).1,
  have h₂ : x ∉ (two_pt_ray b a).inside,
    intro hf, unfold two_pt_ray at hf, simp at hf,
    cases hf with hxb hbax,
    rw hxb at hbxc, exact (is_between_not_eq hbxc).1 rfl,
    exact hbac (same_side_pt_trans hbax (is_between_same_side_pt.mp hbxc).1),
  refine ray_unique _ _,
  unfold two_pt_ray, simp,
  use x, split,
  unfold two_pt_ray, simp, exact (is_between_not_eq hbxc).1.symm,
  split, rw ←h at h₁; cases h₁ with h₁ h₁, exact absurd h₁ h₂, exact h₁,
  cases h₁ with h₁ h₁, exact absurd h₁ h₂, exact h₁
end

example (a : nat) : a ∈ {1} → a = 1 := finset.mem_singleton.mp

lemma three_pt_angle_ray {a o b : B.pts} (haob : noncollinear a o b) :
((r1 (∠ a o b)).1 = two_pt_ray o a ∧ (r2 (∠ a o b)).1 = two_pt_ray o b) ∨
(r1 (∠ a o b)).1 = two_pt_ray o b ∧ (r2 (∠ a o b)).1 = two_pt_ray o a :=
begin
  cases ray_reconstruct (r1 (∠ a o b)).1 with x hx,
  cases ray_reconstruct (r2 (∠ a o b)).1 with y hy,
  rw r1_vertex at hx, rw r2_vertex at hy,
  have : ∠ x (r1 (∠ a o b)).val.vertex y = ∠ a o b,
    rw [hx, two_pt_ray_vertex],
    suffices : (∠ x o y).inside = (∠ a o b).inside,
      unfold three_pt_angle, simp, unfold three_pt_angle at this, simp at this, exact this,
    rw (r2 (∠ a o b)).2.2.2,
    unfold three_pt_angle, simp, simp at hx hy, rw [hx, hy],
  rw r1_vertex at this,
  have hoy : o ≠ y,
    intro hoy, rw ←hoy at this, unfold three_pt_angle at this, simp at this,
    rw ray_singleton at this,
    have ho : {o} ⊆ (two_pt_ray o x).inside, unfold two_pt_ray, simp,
    rw union_eq_self_of_subset_right ho at this,
    by_cases hox : o = x,
      rw [hox, ray_singleton] at this,
      have ha : (two_pt_ray x a).inside ⊆ {x}, rw this, simp,
      cases subset_singleton_iff_eq.mp ha with ha ha, have := (pt_right_in_ray x a), rw ha at this, exact this,
      have hb : (two_pt_ray x b).inside ⊆ {x}, rw this, simp,
      cases subset_singleton_iff_eq.mp hb with hb hb, have := (pt_right_in_ray x b), rw hb at this, exact this,
      rw ray_singleton_iff_eq at ha hb,
      exact (noncollinear_not_eq haob).2.2 (ha.1.symm.trans hb.1).symm,
    have ha := (ray_in_line o x) (by {rw this, left, exact pt_right_in_ray o a}),
    have hb := (ray_in_line o x) (by {rw this, right, exact pt_right_in_ray o b}),
    exact haob ⟨(o-ₗx), line_in_lines hox, ha, pt_left_in_line o x, hb⟩,
  have hox : o ≠ x,
    intro hox, rw ←hox at this, unfold three_pt_angle at this, simp at this,
    rw ray_singleton at this,
    have ho : {o} ⊆ (two_pt_ray o y).inside, unfold two_pt_ray, simp,
    rw union_eq_self_of_subset_left ho at this,
    have ha := (ray_in_line o y) (by {rw this, left, exact pt_right_in_ray o a}),
    have hb := (ray_in_line o y) (by {rw this, right, exact pt_right_in_ray o b}),
    exact haob ⟨(o-ₗy), line_in_lines hoy, ha, pt_left_in_line o y, hb⟩,
  have h₁ : (r1 (∠ a o b)).1 = two_pt_ray o a → (r2 (∠ a o b)).1 = two_pt_ray o b,
    have := three_pt_angle_ray_prep this hoy (noncollinear_not_eq haob).2.1,
    intro h, rw hy, rw hx at h, exact this h,
  have h₂ : (r1 (∠ a o b)).1 = two_pt_ray o b → (r2 (∠ a o b)).1 = two_pt_ray o a,
    rw @angle_symm B a o b at this,
    have := three_pt_angle_ray_prep this hoy (noncollinear_not_eq haob).1.symm,
    intro h, rw hy, rw hx at h, exact this h,
  have h₃ : (r1 (∠ a o b)).1 = two_pt_ray o a ∨ (r1 (∠ a o b)).1 = two_pt_ray o b,
    rw hx, by_contra h₃, push_neg at h₃,
    unfold three_pt_angle at this, simp at this,
    have hoxoa := ray_disjoint (by unfold two_pt_ray) h₃.1,
    have hoxob := ray_disjoint (by unfold two_pt_ray) h₃.2,
    cases two_pt_between hox with y hoyx,
    have hy₁ : y ∈ (two_pt_ray o x).inside,
      unfold two_pt_ray, simp, right, exact same_side_pt_symm (is_between_same_side_pt.mp hoyx).1,
    have hy₂ : y ∈ (two_pt_ray o a).inside ∪ (two_pt_ray o b).inside,
      rw ←this, left, exact hy₁,
    have hy₃ : y ∉ {(two_pt_ray o x).vertex},
      intro hy₃, unfold two_pt_ray at hy₃, simp at hy₃, exact (is_between_not_eq hoyx).1.symm (finset.mem_singleton.mp hy₃),
    apply hy₃, rw finset.mem_singleton,
    cases hy₂ with hy₂ hy₂,
    have : y ∈ (two_pt_ray o x).inside ∩ (two_pt_ray o a).inside, from ⟨hy₁, hy₂⟩,
    rw hoxoa at this, simp at this, exact this,
    have : y ∈ (two_pt_ray o x).inside ∩ (two_pt_ray o b).inside, from ⟨hy₁, hy₂⟩,
    rw hoxob at this, simp at this, exact this,
  cases h₃ with h₃ h₃,
  left, exact ⟨h₃, h₁ h₃⟩,
  right, exact ⟨h₃, h₂ h₃⟩
end

def inside_angle (p : B.pts) (a o b : B.pts): Prop :=
same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p

lemma crossbar {a b c d : B.pts} (hbac : noncollinear b a c)
(hd : inside_angle d b a c) : (two_pt_ray a d).inside $ (b-ₛc).inside :=
begin
  unfold inside_angle at hd,
  by_cases hac : a = c,
    rw hac, use c, unfold two_pt_ray, unfold two_pt_segment, simp,
  by_cases hab : a = b,
    rw hab, use b, unfold two_pt_ray, unfold two_pt_segment, simp,
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
    unfold same_side_line at hd, apply hd.2, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    intro hacd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac) hac ⟨pt_left_in_line a d, hacd⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    intro habd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab ⟨pt_left_in_line a d, habd⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at hf,
    unfold same_side_line at hd, apply hd.1, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    use a, split, exact pt_left_in_line a d,
    unfold two_pt_segment, simp, right, right, rw is_between_symm at hcae, exact hcae,
  have hbeab : ∀ x ∈ (b-ₛe).inside, x ≠ b → same_side_line (a-ₗb) e x,
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
  have hbeac : ∀ x ∈ (b-ₛe).inside, x ≠ e → same_side_line (a-ₗc) b x,
    have hbae : b ∉ (a-ₗe),
      rw haeac, intro hf, exact hbac ⟨(a-ₗc), line_in_lines hac, hf, pt_left_in_line a c, pt_right_in_line a c⟩, 
    intros x hxbe hxe, rw segment_symm at hxbe, rw ←haeac,
    exact t_shape_segment hae hbae x hxbe hxe,
  have hadab : ∀ x ∈ two_pt_ray a d, x ≠ a → same_side_line (a-ₗb) d x,
    have hdba : d ∉ (b-ₗa), rw line_comm, from (same_side_line_not_in (line_in_lines hab) hd.1).2,
    rw line_comm a b, exact t_shape_ray (ne.symm hab) hdba,
  have hdbac : same_side_line (a-ₗc) d b, from same_side_line_symm (line_in_lines hac) hd.2,
  have h₂ : ¬((a-ₗd) $ (e-ₛb).inside),
    have hdcab := same_side_line_symm (line_in_lines hab) hd.1,
    rintros ⟨f, hf⟩, rw segment_symm at hf, simp at hf,
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
      rw segment_symm at hf,
      rw (two_pt_one_line (line_in_lines heb) (line_in_lines hae) hae ⟨segment_in_line e b hf.2, pt_left_in_line e b⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this,
      exact hbac ⟨(a-ₗc) ,line_in_lines hac, this, pt_left_in_line a c, pt_right_in_line a c⟩,
    specialize hbeab f hf.2 hfb,
    specialize hbeac f hf.2 hfe,
    have hdfac := same_side_line_trans (line_in_lines hac) hdbac hbeac,
    have hfad : f ∈ two_pt_ray a d,
      unfold two_pt_ray, left, unfold same_side_pt, split,
      intro hadf, apply hdfac,
      exact ⟨a, pt_left_in_line a c, hadf⟩,
      exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hf.1⟩,
    specialize hadab f hfad hfa,
    have hedab := same_side_line_trans (line_in_lines hab) hbeab (same_side_line_symm (line_in_lines hab) hadab),
    have hecab := same_side_line_trans (line_in_lines hab) hedab hdcab,
    apply hecab, use a, split,
    exact pt_left_in_line a b,
    unfold two_pt_segment, simp, right, right, exact (is_between_symm c a e).mp hcae,
    cases h₁.1 with h₁ h₁,
    exact absurd h₁ h₂,
  rcases h₁ with ⟨f, hfad, hfcb⟩,
  have : b ∉ (a-ₗc), from λ hf, hbac ⟨(a-ₗc), line_in_lines hac, hf, pt_left_in_line a c, pt_right_in_line a c⟩,
  have hcbac : ∀ x ∈ (c-ₛb).inside, x ≠ c → same_side_line (a-ₗc) b x,
    from t_shape_segment hac this,
  have hfc : f ≠ c,
    intro hfc, rw hfc at hfad, have := pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac) hac ⟨pt_left_in_line a d, hfad⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at this,
    exact (same_side_line_not_in (line_in_lines hac) hd.2).2 this,
  specialize hcbac f hfcb hfc,
  have hdfac := same_side_line_trans (line_in_lines hac) hdbac hcbac,
  use f, split,
  unfold two_pt_ray same_side_pt, simp, right, split,
  intro hf, apply hdfac, use a, exact ⟨pt_left_in_line a c, hf⟩,
  exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hfad⟩,
  rw segment_symm, exact hfcb
end

structure incidence_order_congruence_geometry extends incidence_order_geometry :=
(segment_congr : segment → segment → Prop)
--For an arbitrary segment and a ray, we find a unique congruent segment on the ray
(C1 : ∀ (a b : pts) (l : segment), ∃ c : pts, same_side_pt a b c ∧
segment_congr l (a-ₛc) ∧ ∀ x : pts, same_side_pt a b x → segment_congr l (a-ₛx) → x = c)
--This is equivalent to congruency being an equivalent relation
(C2 : ∀ s₁ s₂ s₃ : segment,
(segment_congr s₁ s₂ → segment_congr s₁ s₃ → segment_congr s₂ s₃) ∧ segment_congr s₁ s₁)
--This axiom deals with addition of segments.
(C3 : ∀ {a b c d e f: pts}, is_between a b c → is_between d e f → segment_congr (a-ₛb) (d-ₛe)
                        → segment_congr (b-ₛc) (e-ₛf) → segment_congr (a-ₛc) (d-ₛf))
(angle_congr : angle → angle → Prop)
--Given any angle and a ray, we find a pt that together with the ray forms a congruent angle
--Also, this pt is unique on its side w.r.t the ray
(C4 : ∀ (α : angle) (a b : pts), ∃ c : pts, angle_congr α (∠c a b)
∧ ∀ x : pts, same_side_line (↑(line a b)) c x → angle_congr α (∠x a b) → x = c)
--Similar to C2
(C5 : ∀ α β γ : angle, (angle_congr α β → angle_congr α γ → angle_congr β γ) ∧ angle_congr α α)
--SAS!!!
(C6 : ∀ {a b c d e f : pts}, segment_congr (a-ₛb) (d-ₛe) → segment_congr (a-ₛc) (d-ₛf) → angle_congr (∠b a c) (∠e d f)
→ segment_congr (b-ₛc) (e-ₛf) ∧ angle_congr (∠a b c) (∠d e f) ∧ angle_congr (∠a c b) (∠d f e))

instance : has_coe incidence_order_congruence_geometry incidence_order_geometry :=
⟨incidence_order_congruence_geometry.to_incidence_order_geometry⟩

variables {C : incidence_order_congruence_geometry}

local notation a`-ₗ`b := (line a b : set C.pts)

local notation a`≅ₛ`b := C.segment_congr a b

lemma extend_congr_segment (a b : C.pts) (l : segment) :
∃ c : C.pts, same_side_pt a b c ∧ (l ≅ₛ (a-ₛc))
∧ ∀ x : C.pts, same_side_pt a b x ∧ (l ≅ₛ (a-ₛx)) → x = c :=
by {simp, exact C.C1 a b l}

lemma segment_congr_refl (s : segment) : s ≅ₛ s := (C.C2 s s s).2

lemma segment_congr_symm {s₁ s₂ : segment} :
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₁) := λ h, (C.C2 s₁ s₂ s₁).1 h (segment_congr_refl s₁)

lemma segment_congr_trans {s₁ s₂ s₃ : segment} : 
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₃) → (s₁ ≅ₛ s₃) := λ h₁ h₂, (C.C2 s₂ s₁ s₃).1 (segment_congr_symm h₁) h₂

noncomputable def segment_add (m n : segment) : 
{ L : segment // ((p1 m).1 = (p2 m).1 → L = ((p1 m).1-ₛ(p1 m).1)) ∧
((p1 m).1 ≠ (p2 m).1 → ∃ p : C.pts, L = ((p1 m).1-ₛp)
∧ C.is_between (p1 m).1 (p2 m).1 p ∧ (((p2 m).1-ₛp) ≅ₛ n)) } :=
begin
  set a := (p1 m).1 with hm₁, set b := (p2 m).1 with hm₂,
  set c := (p1 n).1 with hn₁, set d := (p2 n).1 with hn₂,
  by_cases hab : a = b,
  use (a-ₛa), exact ⟨λ h, rfl, λ h, absurd hab h⟩, 
  choose e habe using is_between_extend hab,
  choose f hbef hcdbf hf using extend_congr_segment b e (c-ₛd),
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
  rw [hn₁, hn₂, ←(segment_rw n)] at hcdbf, rw ←hm₂, exact segment_congr_symm hcdbf
end

notation a`+ₗ`b := segment_add a b

lemma segment_add_collinear {a b c d e f: C.pts} : C.is_between a b c → C.is_between d e f
→ ((a-ₛb) ≅ₛ (d-ₛe)) → ((b-ₛc) ≅ₛ (e-ₛf)) → ((a-ₛc) ≅ₛ (d-ₛf)) :=
λh₁ h₂ h₃ h₄, C.C3 h₁ h₂ h₃ h₄

lemma congr_segment_add {m m' n n' : segment} (hmpt : (p1 m).1 ≠ (p2 m).1)
(hm'pt : (p1 m').1 ≠ (p2 m').1) :
(m ≅ₛ m') → (n ≅ₛ n') → ((m +ₗ n) ≅ₛ (m' +ₗ n')) :=
begin
  intros hmm' hnn',
  rcases (m +ₗ n).2.2 hmpt with ⟨a, hm₁a, hm₁m₂a, hm₂an₁n₂⟩,
  rcases (m' +ₗ n').2.2 hm'pt with ⟨b, hn₁b, hm₁m₂b', hm₂bn₁n₂'⟩,
  simp at hm₁a hn₁b, rw [hm₁a, hn₁b],
  have := segment_congr_trans (segment_congr_trans hm₂an₁n₂ hnn') (segment_congr_symm hm₂bn₁n₂'),
  rw [segment_rw m, segment_rw m'] at hmm',
  exact C.C3 hm₁m₂a hm₁m₂b' hmm' this
end

lemma congr_segment_sub {a b c d e f : C.pts} (habc : C.is_between a b c) (hdef : same_side_pt d e f)
(habde : (a-ₛb)≅ₛ(d-ₛe)) (hacdf : (a-ₛc)≅ₛ(d-ₛf)) : C.is_between d e f ∧ ((b-ₛc)≅ₛ(e-ₛf)) :=
begin
  rcases is_between_extend (same_side_pt_not_eq hdef).1.symm with ⟨x, hdex⟩,
  rcases extend_congr_segment e x (b-ₛc) with ⟨f', hexf', hbcef', hu⟩, simp at *,
  have hdef' : C.is_between d e f',
    rcases is_between_collinear hdex with ⟨l, hl, hdl, hel, hxl⟩,
    rcases hexf'.2 with ⟨m, hm, hem, hxm, hf'm⟩,
    rw (two_pt_one_line hm hl (same_side_pt_not_eq hexf').1 ⟨hxm, hem⟩ ⟨hxl, hel⟩) at hf'm,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hf'm⟩ (is_between_not_eq hdex).1 (same_side_pt_not_eq hexf').2],
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hxl⟩ (same_side_pt_not_eq hdef).1.symm (same_side_pt_not_eq hexf').1] at hdex,
    intro hedf', exact hdex (same_side_pt_trans hedf' (same_side_pt_symm hexf')),
  have hacdf' := C.C3 habc hdef' habde hbcef',
  have hff' : f = f',
    rcases extend_congr_segment d e (a-ₛc) with ⟨f'', -, -, hf''⟩, simp at hf'',
    rw [hf'' f hdef hacdf, hf'' f' (is_between_same_side_pt.mp hdef').1 hacdf'],
  rw hff', exact ⟨hdef', hbcef'⟩
end

def segment_lt (m n : segment) : Prop :=
∃ a : C.pts, C.is_between (p1 n).1 a (p2 n).1 ∧ (m ≅ₛ ((p1 n).1-ₛa))

local notation a`<ₛ`b := @segment_lt C a b

lemma segment_lt_two_side {m : segment} {a b : C.pts} (hmab : m <ₛ (a-ₛb)) :
∃ x : C.pts, C.is_between a x b ∧ (m ≅ₛ (a-ₛx)):=
begin
  cases (two_pt_segment_pt a b) with he he,
  rcases hmab with ⟨x, h1x2, hm1x⟩,
  simp_rw [he.1, he.2] at h1x2 hm1x,
  exact ⟨x, h1x2, hm1x⟩,
  rw segment_symm at hmab he,
  rcases hmab with ⟨x, h1x2, hm1x⟩,
  simp_rw [he.1, he.2] at h1x2 hm1x,
  rcases extend_congr_segment a b (b-ₛx) with ⟨y, haby, hbxay, -⟩,
  have key := congr_segment_sub h1x2 (same_side_pt_symm haby) hbxay (by {rw segment_symm, exact segment_congr_refl _}),
  exact ⟨y, key.1, segment_congr_trans hm1x hbxay⟩
end

lemma segment_lt_congr {m n l : segment} (hmn : m ≅ₛ n) :
((m <ₛ l) → (n <ₛ l)) ∧ ((l <ₛ m) → (l <ₛ n)) :=
begin
  unfold segment_lt, split,
  rintros ⟨a, hl₁al₂, hm⟩,
  exact ⟨a, hl₁al₂, segment_congr_trans (segment_congr_symm hmn) hm⟩,
  rintros ⟨a, hm₁am₂, hl⟩,
  rcases extend_congr_segment (p1 n).1 (p2 n).1 ((p1 m).1-ₛa) with ⟨b, hnb, hm₁an₁b, -⟩,
  use b, split,
  rw [segment_rw m, segment_rw n] at hmn,
  exact (congr_segment_sub hm₁am₂ (same_side_pt_symm hnb) hm₁an₁b hmn).1,
  exact segment_congr_trans hl hm₁an₁b
end

lemma between_endpt {a b x : C.pts} :
C.is_between (p1 (a-ₛb)).1 x (p2 (a-ₛb)).1 → C.is_between a x b :=
begin
  intro h,
  cases (two_pt_segment_pt a b) with he he;
  simp_rw [he.1, he.2] at h, exact h,
  rw is_between_symm, exact h
end

lemma segment_lt_trans {m n l : segment} :
(m <ₛ n) → (n <ₛ l) → (m <ₛ l) :=
begin
  unfold segment_lt,
  rintros ⟨a, hna, hm⟩, rintros ⟨b, hlb, hn⟩,
  rcases segment_lt_two_side ((segment_lt_congr hn).2 ⟨a, hna, hm⟩) with ⟨c, h1cb, hm⟩,
  use c, rw is_between_symm at hlb h1cb, split,
  rw is_between_symm, exact (is_between_trans' hlb h1cb).2, exact hm
end

lemma segment_tri (m n : segment) :
(m <ₛ n) ∨ (m ≅ₛ n) ∨ (n <ₛ m) :=
begin
  rcases extend_congr_segment (p1 n).1 (p2 n).1 m with ⟨a, hna, hm, -⟩,
  by_cases ha : a = (p2 n).1,
  rw [ha, ←segment_rw n] at hm, right, left, exact hm,
  rcases hna.2 with ⟨l, hl, hn₁l, hn₂l, hal⟩,
  cases (line_separation ⟨l, hl, hn₂l, hn₁l, hal⟩ (same_side_pt_not_eq hna).1.symm ha).1 with hna' hna',
  left, use a, split, rw is_between_same_side_pt, exact ⟨same_side_pt_symm hna, hna'⟩, exact hm,
  right, right, rw ←is_between_diff_side_pt at hna',
  rcases extend_congr_segment (p1 m).1 (p2 m).1 n with ⟨b, hmb, hn, -⟩,
  use b, split,
  rw segment_rw n at hn, rw segment_rw m at hm,
  exact (congr_segment_sub hna' (same_side_pt_symm hmb) hn (segment_congr_symm hm)).1,
  exact hn
end

local notation a`≅ₐ`b := C.angle_congr a b

lemma angle_congr_refl (α : angle) : α ≅ₐ α := (C.C5 α α α).2

lemma angle_congr_symm {α β : angle} :
(α ≅ₐ β) → (β ≅ₐ α) := λ h, (C.C5 α β α).1 h (angle_congr_refl α)

lemma angle_congr_trans {α β γ : angle} : 
(α ≅ₐ β) → (β ≅ₐ γ) → (α ≅ₐ γ) := λ h₁ h₂, (C.C5 β α γ).1 (angle_congr_symm h₁) h₂

def angle_nontrivial (α : angle) : Prop :=
∀ l ∈ C.lines, ¬α.inside ⊆ l

def supplementary (α β : @angle C.to_incidence_order_geometry) : Prop :=
((r1 α).1 = (r1 β).1 ∧ angle_nontrivial α ∧ angle_nontrivial β ∧
∀ x ∈ (r2 α).1, ∀ y ∈ (r2 β).1, diff_side_pt α.vertex x y)

lemma three_pt_angle_nontrivial_not_eq {a o b : C.pts} :
angle_nontrivial (∠ a o b) → a ≠ o ∧ a ≠ b ∧ o ≠ b :=
begin
  intro h, unfold angle_nontrivial at h,
  have h₁ : a ≠ o ∨ a ≠ b ∨ o ≠ b,
    by_contra h₁, push_neg at h₁, rw [h₁.1, h₁.2.2] at h,
    rcases one_pt_line b with ⟨l, hl, hbl⟩,
    apply h l hl, unfold three_pt_angle two_pt_ray, intros x hx,
    simp at hx, cases hx with hx hx, rw hx, exact hbl,
    exact absurd rfl (same_side_pt_not_eq hx).1,
  by_contra hf, rw [not_and_distrib, not_and_distrib, not_not, not_not, not_not] at hf,
  rcases h₁ with hao | hab | hob,
  rcases hf with hf | hf | hf, exact hao hf,
  rw ←hf at h, apply h (a-ₗo) (line_in_lines hao),
  unfold three_pt_angle, intros x hx, simp at hx,
  rw line_comm, exact (ray_in_line o a) hx,
  rw ←hf at h, apply h (a-ₗo) (line_in_lines hao),
  unfold three_pt_angle, intros x hx, simp at hx, cases hx with hx hx,
  rw line_comm, exact (ray_in_line o a) hx,
  rw ray_singleton at hx, simp at hx, rw hx, exact pt_right_in_line a o,
  rcases hf with hf | hf | hf,
  rw ←hf at h, apply h (a-ₗb) (line_in_lines hab),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw ray_singleton at hx, simp at hx, rw hx, exact pt_left_in_line a b,
  exact (ray_in_line a b) hx,
  exact hab hf,
  rw hf at h, apply h (a-ₗb) (line_in_lines hab),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw line_comm, exact (ray_in_line b a) hx,
  rw ray_singleton at hx, simp at hx, rw hx, exact pt_right_in_line a b,
  rcases hf with hf | hf | hf,
  rw hf at h, apply h (o-ₗb) (line_in_lines hob),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw ray_singleton at hx, simp at hx, rw hx, exact pt_left_in_line o b,
  exact (ray_in_line o b) hx,
  rw hf at h, apply h (o-ₗb) (line_in_lines hob),
  unfold three_pt_angle, intros x hx, simp at hx,
  exact (ray_in_line o b) hx,
  exact hob hf
end

lemma nontrivial_iff_noncollinear {a o b : C.pts} :
angle_nontrivial (∠ a o b) ↔ noncollinear a o b :=
begin
  split; intro h,
  have hoa : o ≠ a, from (three_pt_angle_nontrivial_not_eq h).1.symm,
  have hob : o ≠ b, from (three_pt_angle_nontrivial_not_eq h).2.2,
  rintros ⟨l, hl, hal, hol, hbl⟩,
  unfold angle_nontrivial three_pt_angle at h, simp only at h,
  apply h l hl,
  unfold two_pt_ray, simp only, intros x hx, simp at hx,
  rcases hx with (hx | hx) | hx,
  rw hx, exact hol,
  rcases hx.2 with ⟨m, hm, hom, ham, hxm⟩,
  rw two_pt_one_line hm hl hoa ⟨hom, ham⟩ ⟨hol, hal⟩ at hxm, exact hxm,
  rcases hx.2 with ⟨m, hm, hom, hbm, hxm⟩,
  rw two_pt_one_line hm hl hob ⟨hom, hbm⟩ ⟨hol, hbl⟩ at hxm, exact hxm,
  intros l hl hf,
  have ha : a ∈ (∠ a o b).inside, from pt_left_in_three_pt_angle a o b,
  have hb : b ∈ (∠ a o b).inside, from pt_right_in_three_pt_angle a o b,
  have ho : o ∈ (∠ a o b).inside, have := vertex_in_angle (∠ a o b), rw three_pt_angle_vertex at this, exact this,
  exact h ⟨l, hl, hf ha, hf ho, hf hb⟩
end

lemma three_pt_supplementary {a b c d : C.pts} :
supplementary (∠ b a c) (∠ b a d) → diff_side_pt a c d :=
begin
  intro hs, unfold supplementary at hs,
  rw [nontrivial_iff_noncollinear, nontrivial_iff_noncollinear] at hs,
  cases three_pt_angle_ray hs.2.1 with h₁ h₁;
  cases three_pt_angle_ray hs.2.2.1 with h₂ h₂,
  rw [h₁.2, h₂.2] at hs,
  have := hs.2.2.2 c (pt_right_in_ray a c) d (pt_right_in_ray a d),
  rw three_pt_angle_vertex at this, exact this,
  have hf : two_pt_ray a b = two_pt_ray a d,
    rw [←h₁.1, ←h₂.1], exact hs.1,
  exfalso, apply hs.2.2.1,
  exact ⟨(b-ₗa), line_in_lines (noncollinear_not_eq hs.2.1).1, pt_left_in_line b a, pt_right_in_line b a,
  by { rw line_comm, apply ray_in_line a b, rw hf, exact pt_right_in_ray a d }⟩,
  have hf : two_pt_ray a b = two_pt_ray a c,
    rw [←h₁.1, ←h₂.1], exact hs.1.symm,
  exfalso, apply hs.2.1,
  exact ⟨(b-ₗa), line_in_lines (noncollinear_not_eq hs.2.1).1, pt_left_in_line b a, pt_right_in_line b a,
  by { rw line_comm, apply ray_in_line a b, rw hf, exact pt_right_in_ray a c }⟩,
  rw [h₁.2, h₂.2] at hs,
  have := (hs.2.2.2 a (pt_left_in_ray a b) a (pt_left_in_ray a b)),
  rw three_pt_angle_vertex at this, exact absurd rfl this.2.2.2
end

structure triangle := (v1 : C.pts) (v2 : C.pts) (v3 : C.pts)

def tri_congr (t₁ t₂ : @triangle C) : Prop :=
((t₁.v1-ₛt₁.v2) ≅ₛ (t₂.v1-ₛt₂.v2)) ∧ ((t₁.v1-ₛt₁.v3) ≅ₛ (t₂.v1-ₛt₂.v3)) ∧ ((t₁.v2-ₛt₁.v3) ≅ₛ (t₂.v2-ₛt₂.v3))
∧ ((∠t₁.v2 t₁.v1 t₁.v3 ≅ₐ ∠t₂.v2 t₂.v1 t₂.v3)
∧ (∠t₁.v1 t₁.v2 t₁.v3 ≅ₐ ∠t₂.v1 t₂.v2 t₂.v3)
∧ (∠t₁.v1 t₁.v3 t₁.v2 ≅ₐ ∠t₂.v1 t₂.v3 t₂.v2))

notation a`≅ₜ`b := tri_congr a b

def three_pt_triangle (a b c : C.pts) : triangle := ⟨a, b, c⟩

notation `Δ` := three_pt_triangle

lemma tri_congr_side {a b c a' b' c': C.pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
((a-ₛb) ≅ₛ (a'-ₛb')) ∧ ((a-ₛc) ≅ₛ (a'-ₛc')) ∧ ((b-ₛc) ≅ₛ (b'-ₛc')) :=
begin
  unfold tri_congr three_pt_triangle at h, simp at h,
  exact ⟨h.1, h.2.1, h.2.2.1⟩
end

lemma tri_congr_angle {a b c a' b' c': C.pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
((∠ b a c) ≅ₐ (∠ b' a' c')) ∧ ((∠ a b c) ≅ₐ (∠ a' b' c')) ∧ ((∠ a c b) ≅ₐ (∠ a' c' b')) :=
begin
  unfold tri_congr three_pt_triangle at h, simp at h,
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
end

lemma SAS {ABC DEF : @triangle C} (hs₁ : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2)) (hs₂ : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3))
(ha : (∠ABC.v2 ABC.v1 ABC.v3 ≅ₐ ∠DEF.v2 DEF.v1 DEF.v3)) : ABC ≅ₜ DEF :=
⟨hs₁, hs₂, (C.C6 hs₁ hs₂ ha).1, ha, (C.C6 hs₁ hs₂ ha).2.1, (C.C6 hs₁ hs₂ ha).2.2⟩

lemma supplementary_congr {a b c d a' b' c' d' : C.pts}
(h : supplementary (∠b a c) (∠b a d)) (h' : supplementary (∠b' a' c') (∠b' a' d')) :
((∠b a c) ≅ₐ (∠b' a' c')) → ((∠b a d) ≅ₐ (∠b' a' d')) :=
begin
  intro hbac,
  rcases extend_congr_segment a' b' (a-ₛb) with ⟨x, ha'b'x, haba'b', -⟩,
  rcases extend_congr_segment a' c' (a-ₛc) with ⟨y, ha'b'y, haca'c', -⟩,
  rcases extend_congr_segment a' d' (a-ₛd) with ⟨z, ha'b'z, hada'd', -⟩,
  have : (∠b' a' c') = (∠x a' y),
    unfold three_pt_angle, simp,
    rw [ray_collinear ha'b'x, ray_collinear ha'b'y],
  rw this at h' hbac,
  have : (∠b' a' d') = (∠x a' z),
    unfold three_pt_angle, simp,
    rw [ray_collinear ha'b'x, ray_collinear ha'b'z],
  rw this at h', rw this,
  clear this this ha'b'x ha'b'y ha'b'z b' c' d',
  rename [x b', y c', z d'],
  have h₁ : ((Δ a b c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triangle; simp,
    exact haba'b', exact haca'c', exact hbac,
  have h₂ : ((Δ c b d) ≅ₜ (Δ c' b' d')),
    apply SAS; unfold three_pt_triangle; simp,
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry c' _],
    exact (tri_congr_side h₁).2.2,
    have hcad := is_between_diff_side_pt.2 (three_pt_supplementary h),
    have hc'a'd' := is_between_diff_side_pt.2 (three_pt_supplementary h'),
    refine segment_add_collinear hcad hc'a'd' _ _,
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry c' _], exact haca'c',
    exact hada'd',
    have := angle_same_side b,
    have := tri_congr_angle h₁,
end
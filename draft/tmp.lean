import algebra.support
import set_theory.zfc
import tactic.wlog
import tactic

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

notation m`♥`n := intersect m n

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

lemma line_symm (a b : I.pts) : (a-ₗb) = (b-ₗa) :=
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

lemma collinear12 {a b c : I.pts} : collinear a b c → collinear b a c :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncollinear12 {a b c : I.pts} : noncollinear a b c → noncollinear b a c :=
by {unfold noncollinear, contrapose!, exact collinear12}

lemma collinear13 {a b c : I.pts} : collinear a b c → collinear c b a :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncollinear13 {a b c : I.pts} : noncollinear a b c → noncollinear c b a :=
by {unfold noncollinear, contrapose!, exact collinear13}

lemma collinear23 {a b c : I.pts} : collinear a b c → collinear a c b :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncollinear23 {a b c : I.pts} : noncollinear a b c → noncollinear a c b :=
by {unfold noncollinear, contrapose!, exact collinear23}

lemma collinear123 {a b c : I.pts} : collinear a b c → collinear b c a :=
λh, collinear23 (collinear12 h)

lemma collinear132 {a b c : I.pts} : collinear a b c → collinear c a b :=
λh, collinear23 (collinear13 h)

lemma noncollinear123 {a b c : I.pts} : noncollinear a b c → noncollinear b c a :=
by {unfold noncollinear, contrapose!, exact collinear132}

lemma noncollinear132 {a b c : I.pts} : noncollinear a b c → noncollinear c a b :=
by {unfold noncollinear, contrapose!, exact collinear123}

lemma collinear_trans {a b c d : I.pts} (habc : collinear a b c) (habd : collinear a b d) :
a ≠ b → collinear a c d :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩, rcases habd with ⟨m, hm, ham, hbm, hdm⟩,
  intro hab, rw two_pt_one_line hm hl hab ⟨ham, hbm⟩ ⟨hal, hbl⟩ at hdm,
  exact ⟨l, hl, hal, hcl, hdm⟩
end

lemma collinear_trans' {a b c d : I.pts} (habc : collinear a b c) (habd : noncollinear a b d) :
a ≠ c → noncollinear a c d :=
λhac hacd, habd (collinear_trans (collinear23 habc) hacd hac)

lemma collinear_in12 {a b c : I.pts} : collinear a b c → a ≠ b → c ∈ (a-ₗb) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hab,
  rw two_pt_one_line hl (line_in_lines hab) hab ⟨hal, hbl⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hcl,
  exact hcl
end

lemma collinear_in13 {a b c : I.pts} : collinear a b c → a ≠ c → b ∈ (a-ₗc) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hac,
  rw two_pt_one_line hl (line_in_lines hac) hac ⟨hal, hcl⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at hbl,
  exact hbl
end

lemma collinear_in23 {a b c : I.pts} : collinear a b c → b ≠ c → a ∈ (b-ₗc) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hbc,
  rw two_pt_one_line hl (line_in_lines hbc) hbc ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩ at hal,
  exact hal
end

lemma noncollinear_in12 {a b c : I.pts} : noncollinear a b c → c ∉ (a-ₗb) :=
λ habc hc, habc ⟨(a-ₗb), line_in_lines (noncollinear_not_eq habc).1, pt_left_in_line a b, pt_right_in_line a b, hc⟩

lemma noncollinear_in13 {a b c : I.pts} : noncollinear a b c → b ∉ (a-ₗc) :=
λ habc hb, habc ⟨(a-ₗc), line_in_lines (noncollinear_not_eq habc).2.2.symm, pt_left_in_line a c, hb, pt_right_in_line a c⟩

lemma noncollinear_in23 {a b c : I.pts} : noncollinear a b c → a ∉ (b-ₗc) :=
λ habc ha, habc ⟨(b-ₗc), line_in_lines (noncollinear_not_eq habc).2.1, ha, pt_left_in_line b c, pt_right_in_line b c⟩

structure incidence_order_geometry extends incidence_geometry :=
(is_between : pts → pts → pts → Prop)
-- If B is between A and C, then they are on a same line
(B1 : ∀ a b c : pts, is_between a b c → is_between c b a
                        ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ collinear a b c)
-- Given distinct A and B, ∃ C such that B is between A and C
(B2 : ∀ a b : pts, a ≠ b → ∃ c : pts, is_between a b c)
-- Given any collinear three points, exactly one of them is between the other two.
(B3 : ∀ (a b c : pts) (l ∈ lines), a ∈ l ∧ b ∈ l ∧ c ∈ l →
(a ≠ b → a ≠ c → is_between a b c ∨ is_between a c b ∨ is_between b a c)
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
(a ≠ b → a ≠ c → B.is_between a b c ∨ B.is_between a c b ∨ B.is_between b a c)
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
a ∉ l → b ∉ l → c ∉ l → (l ♥ (a-ₛb).inside) →
((l ♥ (a-ₛc).inside) ∨ (l ♥ (b-ₛc).inside)) ∧ ¬((l ♥ (a-ₛc).inside) ∧ (l ♥ (b-ₛc).inside)) :=
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
  have intersect : (↑(line c e)♥(a-ₛd).inside),
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

def same_side_line (l : set B.pts) (a b : B.pts) : Prop := ¬(l ♥ (a-ₛb).inside)

def diff_side_line (l : set B.pts) (a b : B.pts) : Prop :=
(l ♥ (a-ₛb).inside) ∧ a ∉ l ∧ b ∉ l

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

lemma diff_side_line_symm {l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} :
diff_side_line l a b → diff_side_line l b a :=
by {unfold diff_side_line, rw segment_symm, tauto}

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

lemma diff_side_pt_symm {a b c : B.pts} :
diff_side_pt a b c → diff_side_pt a c b :=
begin
  unfold diff_side_pt, rw segment_symm,
  rintros ⟨ha, habc, h⟩,
  exact ⟨ha, collinear23 habc, h.symm⟩
end

lemma same_side_pt_line {a b c : B.pts} : same_side_pt a b c
→ collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∀ {l : set B.pts}, l ∈ B.lines → a ∈ l ∧ b ∉ l ∧ c ∉ l → same_side_line l b c :=
begin
  intro habc, split, exact habc.2,
  have hab := (same_side_pt_not_eq habc).1.symm,
  have hac := (same_side_pt_not_eq habc).2.symm,
  split, exact hab,
  split, exact hac,
  intros l hl habcl,
  by_cases hbc : b = c, rw ←hbc,
  exact same_side_line_refl hl habcl.2.1,
  rintros ⟨x, hxl, hxbc⟩,
  have hlab : l ≠ (a-ₗb),
    intro hf, rw hf at habcl, exact habcl.2.1 (pt_right_in_line a b),
  have hxab : x ∈ (a-ₗb),
    rcases habc.2 with ⟨l, hl, hal, hbl, hcl⟩,
    rw (two_pt_one_line (line_in_lines hab) hl hab ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨hal, hbl⟩),
    rw (two_pt_one_line hl (line_in_lines hbc) hbc ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩),
    exact (segment_in_line b c) hxbc,
  rw ←(two_line_one_pt hl (line_in_lines hab) hlab habcl.1 (pt_left_in_line a b) hxl hxab) at hxbc,
  unfold two_pt_segment at hxbc, simp at hxbc,
  unfold same_side_pt at habc, unfold two_pt_segment at habc, simp at habc,
  exact habc.1 hxbc,
/-
  rintro ⟨habc, hab, hac, h⟩,
  rcases pt_line_exist habc hab hac with ⟨l, hl, hal, hbl, hcl⟩,
  specialize h hl ⟨hal, hbl, hcl⟩,
  rw ←(not_diff_side_pt habc hab.symm hac.symm), intro hf,
  exact h ⟨a, hal, hf.1⟩
-/
end

lemma diff_side_pt_line {a b c : B.pts} : diff_side_pt a b c
→ collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∀ {l : set B.pts}, l ∈ B.lines → a ∈ l ∧ b ∉ l ∧ c ∉ l → diff_side_line l b c :=
begin
  intro h, split, exact h.2.1, split, exact h.2.2.1.symm, split, exact h.2.2.2.symm,
  intros l hl habcl, use a,
  exact ⟨habcl.1, h.1⟩, exact ⟨habcl.2.1, habcl.2.2⟩,
/-
  rintros ⟨habc, hab, hac, h⟩,
  rcases pt_line_exist habc hab hac with ⟨l, hl, hal, hbl, hcl⟩,
  specialize h hl ⟨hal, hbl, hcl⟩,
  cases h.1 with x hx,
  have hbc : b ≠ c,
    intro hbc, rw [hbc, ←(not_same_side_line hl hcl hcl)] at h, exact h (same_side_line_refl hl hcl),
  have : x = a,
    rcases habc with ⟨m, hm, ham, hbm, hcm⟩,
    rw two_pt_one_line hm (line_in_lines hbc) hbc ⟨hbm, hcm⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩ at ham,
    have : l ≠ (b-ₗc),
      intro hf, rw hf at hbl, exact hbl (pt_left_in_line b c),
    exact two_line_one_pt hl (line_in_lines hbc) this hx.1 ((segment_in_line b c) hx.2) hal ham,
  rw this at hx,
  exact ⟨hx.2, habc, hab.symm, hac.symm⟩
  -/
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
  rcases (collinear_between habc).1 h₁.1 h₁.2.1 with h | h | h,
  exact h, exact absurd h h₂.2.2, exact absurd h h₁.2.2
end

lemma same_side_line_pt {a b c : B.pts}: (collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∃ {l : set B.pts}, l ∈ B.lines ∧ a ∈ l ∧ b ∉ l ∧ c ∉ l ∧ same_side_line l b c)
→ same_side_pt a b c :=
begin
  rintros ⟨habc, hab, hac, l, hl, hal, hbl, hcl, hlbc⟩,
  rw ←(not_diff_side_pt habc hab.symm hac.symm), intro hf,
  have := (diff_side_pt_line hf).2.2.2 hl ⟨hal, hbl, hcl⟩,
  exact (plane_separation hl hbl hcl).2 ⟨hlbc, this⟩
end

lemma diff_side_line_pt {a b c : B.pts}: (collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∃ {l : set B.pts}, l ∈ B.lines ∧ a ∈ l ∧ b ∉ l ∧ c ∉ l ∧ diff_side_line l b c)
→ diff_side_pt a b c :=
begin
  rintros ⟨habc, hab, hac, l, hl, hal, hbl, hcl, hlbc⟩,
  rw ←(not_same_side_pt habc hab.symm hac.symm), intro hf,
  have := (same_side_pt_line hf).2.2.2 hl ⟨hal, hbl, hcl⟩,
  exact (plane_separation hl hbl hcl).2 ⟨this, hlbc⟩
end

private lemma line_pt_exist {a b c : B.pts} (habc : collinear a b c) (hab : a ≠ b) (hac : a ≠ c) : 
∃ l ∈ B.to_incidence_geometry.lines, a ∈ l ∧ b ∉ l ∧ c ∉ l :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩,
  have hd : ∃ d : B.pts, noncollinear a b d ∧ d ∉ l,
    cases noncollinear_exist hab with d habd, use d, split, exact habd,
    intro hdl, exact habd ⟨l, hl, hal, hbl, hdl⟩,
  rcases hd with ⟨d, habd, hdl⟩,
  have hb : b ∉ (a-ₗd),
    intro hb, exact habd ⟨(a-ₗd), line_in_lines (noncollinear_not_eq habd).2.2.symm, pt_left_in_line a d, hb, pt_right_in_line a d⟩,
  have hc : c ∉ (a-ₗd),
    intro hc, rw two_pt_one_line hl (line_in_lines (noncollinear_not_eq habd).2.2.symm) hac ⟨hal, hcl⟩ ⟨pt_left_in_line a d, hc⟩ at hbl,
    exact hb hbl,
  exact ⟨(a-ₗd), line_in_lines (noncollinear_not_eq habd).2.2.symm, pt_left_in_line a d, hb, hc⟩
end

lemma same_side_pt_trans {a b c d : B.pts} :
same_side_pt a b c → same_side_pt a c d → same_side_pt a b d :=
begin
  intros habc hacd,
  have habc' := same_side_pt_line habc,
  have hacd' := same_side_pt_line hacd,
  apply same_side_line_pt,
  split,
  rcases habc'.1 with ⟨l, hl, hal, hbl, hcl⟩,
  rcases hacd'.1 with ⟨m, hm, ham, hcm, hdm⟩,
  rw two_pt_one_line hm hl hacd'.2.1 ⟨ham, hcm⟩ ⟨hal, hcl⟩ at hdm,
  exact ⟨l, hl, hal, hbl, hdm⟩,
  split, exact habc'.2.1,
  split, exact hacd'.2.2.1,
  rcases line_pt_exist habc'.1 habc'.2.1 habc'.2.2.1 with ⟨l, hl, hal, hbl, hcl⟩,
  have hdl : d ∉ l,
    intro hdl,
    rcases hacd'.1 with ⟨m, hm, ham, hcm, hdm⟩,
    rw two_pt_one_line hm hl hacd'.2.2.1 ⟨ham, hdm⟩ ⟨hal, hdl⟩ at hcm,
    exact hcl hcm,
  exact ⟨l, hl, hal, hbl, hdl, same_side_line_trans hl (habc'.2.2.2 hl ⟨hal, hbl, hcl⟩) (hacd'.2.2.2 hl ⟨hal, hcl, hdl⟩)⟩
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

lemma same_side_pt_between {a b c : B.pts} :
same_side_pt a b c → B.is_between a b c ∨ B.is_between a c b :=
begin
  intro habc, rcases (collinear_between habc.2).1 (same_side_pt_not_eq habc).1.symm (same_side_pt_not_eq habc).2.symm  with h | h | h,
  left, exact h, right, exact h,
  rw [is_between_diff_side_pt, ←not_same_side_pt habc.2] at h, exact absurd habc h,
  exact (same_side_pt_not_eq habc).1,
  exact (same_side_pt_not_eq habc).2
end

lemma is_between_same_side_pt_is_between {a b c d : B.pts} :
B.is_between a b c → same_side_pt b c d → B.is_between a b d :=
begin
  intros habc hbcd,
  cases same_side_pt_between hbcd,
  exact (is_between_trans habc h).1,
    exact (is_between_trans' habc h).1
end

lemma diff_side_line_cancel {l : set B.pts} (hl : l ∈ B.lines) {a b c : B.pts} :
diff_side_line l a b → diff_side_line l b c → same_side_line l a c :=
begin
  intros h₁ h₂,
  have hab : a ≠ b,
    intro hf, rw ←hf at h₁, unfold diff_side_line intersect at h₁, rw segment_singleton at h₁,
    cases h₁.1 with a' ha', simp at ha', rw ←ha'.2 at h₁, exact h₁.2.1 ha'.1,
  by_cases hac : a = c,
    rw ←hac, exact same_side_line_refl hl h₁.2.1,
  have hbc : b ≠ c,
    intro hf, rw ←hf at h₂, unfold diff_side_line intersect at h₂, rw segment_singleton at h₂,
    cases h₂.1 with b' hb', simp at hb', rw ←hb'.2 at h₂, exact h₂.2.1 hb'.1,
  by_cases habc : collinear a b c,
    cases h₁.1 with x hx,
    have : diff_side_pt x a b,
      unfold diff_side_pt, split, exact hx.2, split,
      exact ⟨a-ₗb, line_in_lines hab, (segment_in_line a b) hx.2, pt_left_in_line a b, pt_right_in_line a b⟩,
      split; intro hf; rw ←hf at hx, exact h₁.2.1 hx.1, exact h₁.2.2 hx.1,
    rw ←is_between_diff_side_pt at this,
    by_contra hlac, rw not_same_side_line at hlac, cases hlac.1 with y hy,
    have hyac := (segment_in_line a c) hy.2,
    rcases habc with ⟨m, hm, ham, hbm, hcm⟩,
    rw two_pt_one_line (line_in_lines hac) hm hac ⟨pt_left_in_line a c, pt_right_in_line a c⟩ ⟨ham, hcm⟩ at hyac,
    rw two_pt_one_line hm (line_in_lines hab) hab ⟨ham, hbm⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hyac,
    have hneq : l ≠ (a-ₗb),
      intro hf, have := pt_left_in_line a b, rw ←hf at this, exact h₁.2.1 this,
    have hxy := two_line_one_pt hl (line_in_lines hab) hneq hx.1 ((segment_in_line a b) hx.2) hy.1 hyac,
    rw ←hxy at hy, unfold two_pt_segment at hy, simp at hy,
    rcases hy.2 with hya | hyc | hy,
    exact (is_between_not_eq this).1.symm hya, rw ←hyc at hlac, exact hlac.2.2 hy.1,
    cases h₂.1 with z hz,
    have hzbc := (segment_in_line b c) hz.2,
    rw two_pt_one_line (line_in_lines hbc) hm hbc ⟨pt_left_in_line b c, pt_right_in_line b c⟩ ⟨hbm, hcm⟩ at hzbc,
    rw two_pt_one_line hm (line_in_lines hab) hab ⟨ham, hbm⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hzbc,
    have hxz := two_line_one_pt hl (line_in_lines hab) hneq hx.1 ((segment_in_line a b) hx.2) hz.1 hzbc,
    rw ←hxz at hz, unfold two_pt_segment at hz, simp at hz,
    rcases hz.2 with hzb | hzc | hz,
    exact (is_between_not_eq this).2.2 hzb, rw ←hzc at hlac, exact hlac.2.2 hz.1,
    rcases (collinear_between ⟨m, hm, ham, hbm, hcm⟩).1 hab hac with habc | hacb | hbac,
    exact (collinear_between (is_between_collinear this)).2.1 ⟨this, (is_between_trans' habc hz).1⟩,
    exact (collinear_between (is_between_collinear hy)).2.1 ⟨hy, (is_between_trans' hacb (by {rw is_between_symm, exact hz})).1⟩,
    exact (collinear_between (is_between_collinear this)).2.2.1 ⟨this, by {rw is_between_symm, exact (is_between_trans' hbac hy).1}⟩,
    exact hl, exact h₁.2.1, exact h₂.2.2,
  by_contra h₃,
  rw not_same_side_line hl h₁.2.1 h₂.2.2 at h₃,
  unfold diff_side_line at h₁ h₂ h₃,
  exact (pasch habc hl h₁.2.1 h₁.2.2 h₂.2.2 h₁.1).2 ⟨h₃.1, h₂.1⟩
end

lemma diff_side_pt_cancel {a b c d : B.pts} :
diff_side_pt a b c → diff_side_pt a b d → same_side_pt a c d :=
begin
  intros habc habd,
  replace habc := diff_side_pt_line habc,
  replace habd := diff_side_pt_line habd,
  have hacd := collinear_trans habc.1 habd.1 habc.2.1,
  apply same_side_line_pt, split,
  exact hacd,
  split, exact habc.2.2.1, split, exact habd.2.2.1,
  rcases line_pt_exist hacd habc.2.2.1 habd.2.2.1 with ⟨l, hl, hal, hcl, hdl⟩,
  have hbl : b ∉ l,
    intro hbl,
    rw two_pt_one_line hl (line_in_lines habc.2.1) habc.2.1 at hcl, exact hcl (collinear_in12 habc.1 habc.2.1),
    exact ⟨hal, hbl⟩, exact ⟨pt_left_in_line a b, pt_right_in_line a b⟩,
  have h₁ := habc.2.2.2 hl ⟨hal, hbl, hcl⟩,
  have h₂ := habd.2.2.2 hl ⟨hal, hbl, hdl⟩,
  exact ⟨l, hl, hal, hcl, hdl, diff_side_line_cancel hl (diff_side_line_symm hl h₁) h₂⟩
end

lemma diff_side_same_side_line {l : set B.pts} (hl : l ∈ B.lines) {a b c : B.pts} :
diff_side_line l a b → same_side_line l b c → diff_side_line l a c :=
begin
  intros hlab hlbc,
  rw ←(not_same_side_line hl hlab.2.1 (same_side_line_not_in hl hlbc).2),
  rw ←(not_same_side_line hl) at hlab, intro hlac,
  exact hlab (same_side_line_trans hl hlac (same_side_line_symm hl hlbc)),
  exact hlab.2.1, exact hlab.2.2
end

lemma diff_side_same_side_pt {a b c d : B.pts} :
diff_side_pt a b c → same_side_pt a b d → diff_side_pt a c d :=
begin
  intros habc habd,
  rw ←not_same_side_pt, rw ←not_same_side_pt at habc,
  intro hacd, exact habc (same_side_pt_trans habd (same_side_pt_symm hacd)),
  exact habc.2.1, exact habc.2.2.1, exact habc.2.2.2,
  exact collinear_trans habc.2.1 habd.2 habc.2.2.1.symm,
  exact habc.2.2.2, exact (same_side_pt_not_eq habd).2
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
    rcases (collinear_between habb').1 hab hab' with h | h | h,
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

lemma ray_eq_same_side_pt {r : ray} {a : B.pts}
(har : a ∈ r.inside) (hao : a ≠ r.vertex) : r = two_pt_ray r.vertex a :=
begin
  suffices : r.inside = (two_pt_ray r.vertex a).inside,
    induction r, unfold two_pt_ray, simp,
    unfold two_pt_ray at this, simp at this, exact this,
  cases r.in_eq with a' ha', rw ha',
  rw ha' at har, simp at har, cases har with har har,
  exact absurd har hao,
  unfold two_pt_ray, ext, simp,
  have : same_side_pt r.vertex a x ↔ same_side_pt r.vertex a' x,
    split; intro h, exact same_side_pt_trans har h,
    exact same_side_pt_trans (same_side_pt_symm har) h,
  rw this
end

lemma two_pt_ray_eq_same_side_pt {o a b : B.pts} (hoab : same_side_pt o a b) : two_pt_ray o a = two_pt_ray o b :=
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

lemma two_pt_ray_eq_same_side_pt_pt {o a b : B.pts} :
same_side_pt o a b ↔ two_pt_ray o a = two_pt_ray o b ∧ o ≠ a ∧ o ≠ b :=
begin
  split, intro hoab, unfold two_pt_ray,
  have : {x : B.to_incidence_geometry.pts | same_side_pt o a x} = {x : B.to_incidence_geometry.pts | same_side_pt o b x},
    ext, simp, split; intro h,
    exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  exact ⟨by {simp, simp at this, rw this},
    (same_side_pt_not_eq hoab).1.symm, (same_side_pt_not_eq hoab).2.symm⟩,
  rintros ⟨hoab, hoa, hob⟩,
  cases two_pt_between hoa with x hoxa,
  have hx : x ∈ (two_pt_ray o b).inside,
    rw ←hoab, unfold two_pt_ray, simp, right, exact same_side_pt_symm (is_between_same_side_pt.1 hoxa).1,
  unfold two_pt_ray at hx, simp at hx, cases hx with hx hx, exact absurd hx (is_between_not_eq hoxa).1.symm,
  exact same_side_pt_trans (same_side_pt_symm (is_between_same_side_pt.1 hoxa).1) (same_side_pt_symm hx)
end

--Any good names lol
lemma t_shape_ray {a b : B.pts} {e : B.pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (two_pt_ray b e).inside, x ≠ b → same_side_line (a-ₗb) e x :=
begin
  intros x hxbe hxb, rintros ⟨f, hfab, hfex⟩,
  have heb : e ≠ b, intro heb, rw [heb, ray_singleton] at hxbe, exact hxb hxbe,
  have hfeb : f ∈ (e-ₗb),
    have hxeb : x ∈ (e-ₗb),
      rw line_symm, from (ray_in_line b e) hxbe,
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
  unfold same_side_pt at hxbe, unfold two_pt_segment at hxbe, simp at hxbe, push_neg at hxbe, exact hxbe.1.2.2 hfex
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

def two_ray_angle {r₁ r₂ : @ray B} (h : r₁.vertex = r₂.vertex) : angle :=
⟨r₁.inside∪r₂.inside, r₁.vertex, ⟨r₁, r₂, rfl, h.symm.trans rfl, rfl⟩⟩

lemma two_ray_angle_three_pt_angle {a b : B.pts} {r₁ r₂ : ray} (hr₁r₂ : r₁.vertex = r₂.vertex) :
a ∈ r₁.inside → b ∈ r₂.inside → a ≠ r₁.vertex → b ≠ r₂.vertex → two_ray_angle hr₁r₂ = ∠ a (r₁.vertex) b :=
begin
  intros har₁ hbr₂ hao hbo,
  unfold two_ray_angle three_pt_angle, simp,
  rw [ray_eq_same_side_pt har₁ hao, ray_eq_same_side_pt hbr₂ hbo],
  rw [two_pt_ray_vertex, hr₁r₂]
end

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

lemma angle_eq_same_side (a : B.pts) {o b c : B.pts} (hobc : same_side_pt o b c) : ∠ a o b = ∠ a o c :=
by {unfold three_pt_angle, simp, rw two_pt_ray_eq_same_side_pt hobc}

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

lemma noncollinear_angle_eq {a o b a' o' b' : B.pts} (haob : noncollinear a o b) :
(∠ a o b) = (∠ a' o' b') → noncollinear a' o' b' :=
begin
  intro he, rintros ⟨l, hl, ha'l, ho'l, hb'l⟩,
  unfold three_pt_angle at he, simp at he,
  have : (two_pt_ray o' a').inside ∪ (two_pt_ray o' b').inside ⊆ l,
    intros x hx, unfold two_pt_ray at hx, simp at hx, rcases hx with (hx | hx) | hx,
    rw hx, exact ho'l,
    rcases hx.2 with ⟨m, hm, ho'm, ha'm, hxm⟩,
    rw two_pt_one_line hm hl (same_side_pt_not_eq hx).1 ⟨ha'm, ho'm⟩ ⟨ha'l, ho'l⟩ at hxm, exact hxm,
    rcases hx.2 with ⟨m, hm, ho'm, hb'm, hxm⟩,
    rw two_pt_one_line hm hl (same_side_pt_not_eq hx).1 ⟨hb'm, ho'm⟩ ⟨hb'l, ho'l⟩ at hxm, exact hxm,
  rw ←he.1 at this, apply haob, use l, split, exact hl,
  split, apply this, left, exact pt_right_in_ray o a,
  split, apply this, left, exact pt_left_in_ray o a,
  apply this, right, exact pt_right_in_ray o b
end

lemma three_pt_angle_eq_iff {a o b a' o' b' : B.pts}
(haob : noncollinear a o b) : (∠ a o b) = (∠ a' o' b') ↔ o = o'
∧ ((same_side_pt o a a' ∧ same_side_pt o b b') ∨ (same_side_pt o a b' ∧ same_side_pt o b a')) :=
begin
  split; intro h,
  have ha'o'b' := noncollinear_angle_eq haob h,
  cases three_pt_angle_ray haob with h₁ h₁;
  cases three_pt_angle_ray ha'o'b' with h₂ h₂;
  rw ←h at h₂,
  have hoa : two_pt_ray o a = two_pt_ray o' a', rw [←h₁.1, ←h₂.1],
  have hob : two_pt_ray o b = two_pt_ray o' b', rw [←h₁.2, ←h₂.2],
  have hoo' : o = o',
    rw [←two_pt_ray_vertex o a, ←two_pt_ray_vertex o' a'], rw hoa,
  split, exact hoo',
  left, rw [two_pt_ray_eq_same_side_pt_pt, two_pt_ray_eq_same_side_pt_pt],
  split, exact ⟨by rw [hoa, hoo'], (noncollinear_not_eq haob).1.symm, by {rw hoo', exact (noncollinear_not_eq ha'o'b').1.symm}⟩,
  exact ⟨by rw [hob, hoo'], (noncollinear_not_eq haob).2.1, by {rw hoo', exact (noncollinear_not_eq ha'o'b').2.1}⟩,
  have hoa : two_pt_ray o a = two_pt_ray o' b', rw [←h₁.1, ←h₂.1],
  have hob : two_pt_ray o b = two_pt_ray o' a', rw [←h₁.2, ←h₂.2],
  have hoo' : o = o',
    rw [←two_pt_ray_vertex o a, ←two_pt_ray_vertex o' b'], rw hoa,
  split, exact hoo',
  right, rw [two_pt_ray_eq_same_side_pt_pt, two_pt_ray_eq_same_side_pt_pt],
  split, exact ⟨by rw [hoa, hoo'], (noncollinear_not_eq haob).1.symm, by {rw hoo', exact (noncollinear_not_eq ha'o'b').2.1}⟩,
  exact ⟨by rw [hob, hoo'], (noncollinear_not_eq haob).2.1, by {rw hoo', exact (noncollinear_not_eq ha'o'b').1.symm}⟩,
  have hoa : two_pt_ray o a = two_pt_ray o' b', rw [←h₁.2, ←h₂.2],
  have hob : two_pt_ray o b = two_pt_ray o' a', rw [←h₁.1, ←h₂.1],
  have hoo' : o = o',
    rw [←two_pt_ray_vertex o a, ←two_pt_ray_vertex o' b'], rw hoa,
    split, exact hoo',
  right, rw [two_pt_ray_eq_same_side_pt_pt, two_pt_ray_eq_same_side_pt_pt],
  split, exact ⟨by rw [hoa, hoo'], (noncollinear_not_eq haob).1.symm, by {rw hoo', exact (noncollinear_not_eq ha'o'b').2.1}⟩,
  exact ⟨by rw [hob, hoo'], (noncollinear_not_eq haob).2.1, by {rw hoo', exact (noncollinear_not_eq ha'o'b').1.symm}⟩,
  have hoa : two_pt_ray o a = two_pt_ray o' a', rw [←h₁.2, ←h₂.2],
  have hob : two_pt_ray o b = two_pt_ray o' b', rw [←h₁.1, ←h₂.1],
  have hoo' : o = o',
    rw [←two_pt_ray_vertex o a, ←two_pt_ray_vertex o' a'], rw hoa,
  split, exact hoo',
  left, rw [two_pt_ray_eq_same_side_pt_pt, two_pt_ray_eq_same_side_pt_pt],
  split, exact ⟨by rw [hoa, hoo'], (noncollinear_not_eq haob).1.symm, by {rw hoo', exact (noncollinear_not_eq ha'o'b').1.symm}⟩,
  exact ⟨by rw [hob, hoo'], (noncollinear_not_eq haob).2.1, by {rw hoo', exact (noncollinear_not_eq ha'o'b').2.1}⟩,
  rw ←h.1, unfold three_pt_angle, simp,
  cases h.2 with h h,
  rw [two_pt_ray_eq_same_side_pt h.1, two_pt_ray_eq_same_side_pt h.2], rw [two_pt_ray_eq_same_side_pt h.1, two_pt_ray_eq_same_side_pt h.2, union_comm]
end

lemma angle_three_pt (α : angle) : ∃ a b : B.pts, α = ∠ a α.vertex b :=
begin
  cases ray_reconstruct (r1 α).1 with a ha,
  cases ray_reconstruct (r2 α).1 with b hb,
  cases (r1 α).2, rw h.1 at ha, clear h w, rw (r2 α).2.2.1 at hb,
  use [a, b],
  suffices : α.inside = (∠ a α.vertex b).inside,
    unfold three_pt_angle, induction α, simp at *,
    rw this, unfold three_pt_angle,
  unfold three_pt_angle, simp, rw [←ha, ←hb],
  exact (r2 α).2.2.2
end

def angle_nontrivial (α : angle) : Prop :=
∀ l ∈ B.lines, ¬α.inside ⊆ l

lemma three_pt_angle_nontrivial_not_eq {a o b : B.pts} :
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
  rw line_symm, exact (ray_in_line o a) hx,
  rw ←hf at h, apply h (a-ₗo) (line_in_lines hao),
  unfold three_pt_angle, intros x hx, simp at hx, cases hx with hx hx,
  rw line_symm, exact (ray_in_line o a) hx,
  rw ray_singleton at hx, simp at hx, rw hx, exact pt_right_in_line a o,
  rcases hf with hf | hf | hf,
  rw ←hf at h, apply h (a-ₗb) (line_in_lines hab),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw ray_singleton at hx, simp at hx, rw hx, exact pt_left_in_line a b,
  exact (ray_in_line a b) hx,
  exact hab hf,
  rw hf at h, apply h (a-ₗb) (line_in_lines hab),
  unfold three_pt_angle, intros x hx, simp at hx,
  cases hx with hx hx, rw line_symm, exact (ray_in_line b a) hx,
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

lemma nontrivial_iff_noncollinear {a o b : B.pts} :
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

def inside_angle (p : B.pts) (α : @angle B) : Prop :=
(∀ a b : B.pts, α = ∠ a α.vertex b → same_side_line (α.vertex-ₗa) b p ∧ same_side_line (α.vertex-ₗb) a p)
∧ angle_nontrivial α

lemma inside_angle_nontrivial {α : angle} :
(∃ p : B.pts, inside_angle p α) → angle_nontrivial α :=
by {rintros ⟨p, hp⟩, exact hp.2}

lemma inside_three_pt_angle {p a o b : B.pts}:
inside_angle p (∠ a o b) ↔ same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p ∧ noncollinear a o b :=
begin
  have : ∀ {a o b a' b' p : B.pts}, noncollinear a o b → (∠ a o b) = (∠ a' o b')
  → same_side_line ↑(line o a') b' p ∧ same_side_line ↑(line o b') a' p
  → same_side_pt o a a' ∧ same_side_pt o b b'
  → same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p,
    intros a o b a' b' p haob he hp h,
    have ha'ob' := noncollinear_angle_eq haob he,
    rw two_pt_one_line (line_in_lines (same_side_pt_not_eq h.1).1.symm) (line_in_lines (same_side_pt_not_eq h.1).2.symm),
    rw two_pt_one_line (line_in_lines (same_side_pt_not_eq h.2).1.symm) (line_in_lines (same_side_pt_not_eq h.2).2.symm),
    split, apply same_side_line_symm (line_in_lines (same_side_pt_not_eq h.1).2.symm),
    apply same_side_line_trans (line_in_lines (same_side_pt_not_eq h.1).2.symm) (same_side_line_symm (line_in_lines (same_side_pt_not_eq h.1).2.symm) hp.1),
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact (same_side_pt_not_eq h.1).2,
    intro hf, exact ha'ob' ⟨(a'-ₗo), line_in_lines (same_side_pt_not_eq h.1).2, pt_left_in_line a' o, pt_right_in_line a' o, hf⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm h.2,
    exact (same_side_pt_not_eq h.2).1,
    apply same_side_line_symm (line_in_lines (same_side_pt_not_eq h.2).2.symm),
    apply same_side_line_trans (line_in_lines (same_side_pt_not_eq h.2).2.symm) (same_side_line_symm (line_in_lines (same_side_pt_not_eq h.2).2.symm) hp.2),
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact (same_side_pt_not_eq h.2).2,
    intro hf, exact ha'ob' ⟨(b'-ₗo), line_in_lines (same_side_pt_not_eq h.2).2, hf, pt_right_in_line b' o, pt_left_in_line b' o⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm h.1,
    exact (same_side_pt_not_eq h.1).1,
    exact (same_side_pt_not_eq h.2).1, exact ⟨pt_right_in_line o b, pt_left_in_line o b⟩,
    split, apply ray_in_line o b', left, exact same_side_pt_symm h.2, exact pt_left_in_line o b',
    exact (same_side_pt_not_eq h.1).1, exact ⟨pt_right_in_line o a, pt_left_in_line o a⟩,
    split, apply ray_in_line o a', left, exact same_side_pt_symm h.1, exact pt_left_in_line o a',
  split; intro hp,
  rcases angle_three_pt (∠ a o b) with ⟨a', b', he⟩,
  rw three_pt_angle_vertex at he, cases hp with hp haob, rw three_pt_angle_vertex at hp,
  specialize hp a' b' he, rw nontrivial_iff_noncollinear at haob,
  cases ((three_pt_angle_eq_iff haob).1 he).2,
  exact ⟨(this haob he hp h).1, (this haob he hp h).2, haob⟩,
  rw @angle_symm B a' _ _ at he, rw and_comm at hp,
  exact ⟨(this haob he hp h).1, (this haob he hp h).2, haob⟩,
  split,
  intros a' b' he, rw three_pt_angle_vertex, rw three_pt_angle_vertex at he,
  have haob := hp.2.2,
  cases ((three_pt_angle_eq_iff haob).1 he).2,
  apply this (noncollinear_angle_eq haob he) he.symm ⟨hp.1, hp.2.1⟩,
  split; apply same_side_pt_symm, exact h.1, exact h.2,
  rw @angle_symm B a' _ _ at he, rw and_comm,
  apply this (noncollinear_angle_eq haob he) he.symm ⟨hp.1, hp.2.1⟩,
  split; apply same_side_pt_symm, exact h.1, exact h.2,
  rw nontrivial_iff_noncollinear, exact hp.2.2
end

lemma crossbar {a b c d : B.pts}
(hd : inside_angle d (∠ b a c)) : (two_pt_ray a d).inside ♥ (b-ₛc).inside :=
begin
  have hbac := hd.2, rw nontrivial_iff_noncollinear at hbac,
  rw inside_three_pt_angle at hd,
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
  have h₁ : (((a-ₗd) ♥ (e-ₛb).inside) ∨ ((a-ₗd) ♥ (c-ₛb).inside)) ∧ ¬(((a-ₗd) ♥ (e-ₛb).inside) ∧ ((a-ₗd) ♥ (c-ₛb).inside)),
    apply pasch hecb (line_in_lines had),
    intro haed,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    rw ←(two_pt_one_line hm (line_in_lines had) hae ⟨ham, hem⟩ ⟨pt_left_in_line a d, haed⟩) at hf,
    rw (two_pt_one_line hm (line_in_lines hac) hac ⟨ham, hcm⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2.1, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
    intro hacd,
    have hf : d ∈ (a-ₗd), from pt_right_in_line a d,
    rw (two_pt_one_line (line_in_lines had) (line_in_lines hac) hac ⟨pt_left_in_line a d, hacd⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩) at hf,
    unfold same_side_line at hd, apply hd.2.1, use d, unfold two_pt_segment, exact ⟨hf, by simp⟩,
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
  have hadab : ∀ x ∈ (two_pt_ray a d).inside, x ≠ a → same_side_line (a-ₗb) d x,
    have hdba : d ∉ (b-ₗa), rw line_symm, from (same_side_line_not_in (line_in_lines hab) hd.1).2,
    rw line_symm a b, exact t_shape_ray (ne.symm hab) hdba,
  have hdbac : same_side_line (a-ₗc) d b, from same_side_line_symm (line_in_lines hac) hd.2.1,
  have h₂ : ¬((a-ₗd) ♥ (e-ₛb).inside),
    have hdcab := same_side_line_symm (line_in_lines hab) hd.1,
    rintros ⟨f, hf⟩, rw segment_symm at hf, simp at hf,
    have hfb : f ≠ b,
      intro hfb, rw hfb at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at this,
      exact (same_side_line_not_in (line_in_lines hab) hd.1).2 this,
    have hfe : f ≠ e,
      intro hfe, rw hfe at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hae) hae ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this, exact (same_side_line_not_in (line_in_lines hac) hd.2.1).2 this,
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
    have hfad : f ∈ (two_pt_ray a d).inside,
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
    exact (same_side_line_not_in (line_in_lines hac) hd.2.1).2 this,
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
(C4 : ∀ (α : angle) (a b : pts), ∀ p : pts, ∃ c : pts, angle_congr α (∠c a b) ∧ same_side_line (↑(line a b)) c p
∧ ∀ x : pts, same_side_line (↑(line a b)) c x → angle_congr α (∠x a b) → x ∈ (two_pt_ray a c).inside)
--Similar to C2
(C5 : ∀ α β γ : angle, (angle_congr α β → angle_congr α γ → angle_congr β γ) ∧ angle_congr α α)
--SAS!!!
(C6 : ∀ {a b c d e f : pts}, noncollinear a b c → noncollinear d e f → segment_congr (a-ₛb) (d-ₛe) → segment_congr (a-ₛc) (d-ₛf) → angle_congr (∠b a c) (∠e d f)
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

lemma congr_segment_add {a b c d e f: C.pts} : C.is_between a b c → C.is_between d e f
→ ((a-ₛb) ≅ₛ (d-ₛe)) → ((b-ₛc) ≅ₛ (e-ₛf)) → ((a-ₛc) ≅ₛ (d-ₛf)) :=
λh₁ h₂ h₃ h₄, C.C3 h₁ h₂ h₃ h₄

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

lemma extend_congr_angle (α : angle) (a b : C.pts) :
∀ p : C.pts, ∃ c : C.pts, (α ≅ₐ (∠c a b)) ∧ same_side_line (a-ₗb) c p
∧ ∀ x : C.pts, same_side_line (a-ₗb) c x → (α ≅ₐ (∠x a b)) → x ∈ (two_pt_ray a c).inside := C.C4 α a b

def supplementary (α β : @angle C.to_incidence_order_geometry) : Prop :=
(∃ a b c d : C.pts, α = ∠ b a c ∧ β = ∠ b a d ∧ C.is_between c a d) ∧ angle_nontrivial α ∧ angle_nontrivial β

lemma supplementary_symm {α β : @angle C.to_incidence_order_geometry} : supplementary α β ↔ supplementary β α :=
begin
  split; rintros ⟨⟨a, b, c, d, hbac, hbad, hcad⟩, h₁, h₂⟩;
  exact ⟨⟨a, b, d, c, hbad, hbac, by {rw is_between_symm, exact hcad}⟩, h₂, h₁⟩,
end

lemma three_pt_angle_supplementary {a b c d : C.pts} :
supplementary (∠b a c) (∠b a d) ↔ C.is_between c a d ∧ noncollinear b a c ∧ noncollinear b a d :=
begin
  split,
  rintros ⟨⟨a', b', c', d', hbac, hbad, hc'a'd'⟩, h₁, h₂⟩,
  have h₁' : angle_nontrivial (∠ b' a' c'), rw ←hbac, exact h₁,
  have h₂' : angle_nontrivial (∠ b' a' d'), rw ←hbad, exact h₂,
  rw nontrivial_iff_noncollinear at h₁ h₁' h₂ h₂',
  have haa' : a = a', from ((three_pt_angle_eq_iff h₁).1 hbac).1,
  rw ←haa' at hc'a'd',
  cases ((three_pt_angle_eq_iff h₁).1 hbac).2 with H₁ H₁;
  cases ((three_pt_angle_eq_iff h₂).1 hbad).2 with H₂ H₂,
  split,
  rw [is_between_diff_side_pt, ←not_same_side_pt], intro hacd,
  rw [is_between_diff_side_pt, ←not_same_side_pt] at hc'a'd',
  exact hc'a'd' (same_side_pt_trans (same_side_pt_trans (same_side_pt_symm H₁.2) hacd) H₂.2),
  exact hc'a'd'.2.1, exact hc'a'd'.2.2.1, exact hc'a'd'.2.2.2,
  rcases H₁.2.2 with ⟨l, hl, hal, hcl, hc'l⟩,
  rcases (is_between_collinear hc'a'd') with ⟨m, hm, hc'm, ham, hd'm⟩,
  rcases H₂.2.2 with ⟨n, hn, han, hdn, hd'n⟩,
  rw ←haa' at h₁' h₂',
  rw two_pt_one_line hm hl (noncollinear_not_eq h₁').2.1 ⟨ham, hc'm⟩ ⟨hal, hc'l⟩ at hd'm,
  rw two_pt_one_line hn hl (noncollinear_not_eq h₂').2.1.symm ⟨hd'n, han⟩ ⟨hd'm, hal⟩ at hdn,
  exact ⟨l, hl, hal, hcl, hdn⟩,
  exact (noncollinear_not_eq h₁).2.1.symm, exact (noncollinear_not_eq h₂).2.1.symm,
  exact ⟨h₁, h₂⟩,
  rcases (same_side_pt_trans H₁.1 (same_side_pt_symm H₂.2)).2 with ⟨l, hl, hal, hbl, hdl⟩,
  exfalso, apply h₂, exact ⟨l, hl, hbl, hal, hdl⟩,
  rcases (same_side_pt_trans H₂.1 (same_side_pt_symm H₁.2)).2 with ⟨l, hl, hal, hbl, hcl⟩,
  exfalso, apply h₁, exact ⟨l, hl, hbl, hal, hcl⟩,
  have hf := (same_side_pt_trans (same_side_pt_symm H₁.1) H₂.1),
  rw [is_between_diff_side_pt, ←not_same_side_pt] at hc'a'd', exact absurd hf hc'a'd',
  exact hc'a'd'.2.1, exact hc'a'd'.2.2.1, exact hc'a'd'.2.2.2,
  rintros ⟨hcad, hbac, hbad⟩,
  use [a, b, c, d], simp, exact hcad,
  rw [nontrivial_iff_noncollinear, nontrivial_iff_noncollinear], exact ⟨hbac, hbad⟩
end

structure triangle := (v1 : C.pts) (v2 : C.pts) (v3 : C.pts)

def tri_congr (t₁ t₂ : @triangle C) : Prop :=
((t₁.v1-ₛt₁.v2) ≅ₛ (t₂.v1-ₛt₂.v2)) ∧ ((t₁.v1-ₛt₁.v3) ≅ₛ (t₂.v1-ₛt₂.v3)) ∧ ((t₁.v2-ₛt₁.v3) ≅ₛ (t₂.v2-ₛt₂.v3))
∧ ((∠t₁.v2 t₁.v1 t₁.v3 ≅ₐ ∠t₂.v2 t₂.v1 t₂.v3)
∧ (∠t₁.v1 t₁.v2 t₁.v3 ≅ₐ ∠t₂.v1 t₂.v2 t₂.v3)
∧ (∠t₁.v1 t₁.v3 t₁.v2 ≅ₐ ∠t₂.v1 t₂.v3 t₂.v2))

notation a`≅ₜ`b := tri_congr a b

lemma tri_congr_refl (t : @triangle C) : t ≅ₜ t :=
⟨segment_congr_refl _, segment_congr_refl _, segment_congr_refl _,
angle_congr_refl _, angle_congr_refl _, angle_congr_refl _⟩

lemma tri_congr_symm {t₁ t₂ : @triangle C} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₁) :=
λh, ⟨segment_congr_symm h.1, segment_congr_symm h.2.1, segment_congr_symm h.2.2.1,
angle_congr_symm h.2.2.2.1, angle_congr_symm h.2.2.2.2.1, angle_congr_symm h.2.2.2.2.2⟩

lemma tri_congr_trans {t₁ t₂ t₃ : @triangle C} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₃) → (t₁ ≅ₜ t₃) :=
λh₁ h₂, ⟨segment_congr_trans h₁.1 h₂.1, segment_congr_trans h₁.2.1 h₂.2.1, segment_congr_trans h₁.2.2.1 h₂.2.2.1,
angle_congr_trans h₁.2.2.2.1 h₂.2.2.2.1, angle_congr_trans h₁.2.2.2.2.1 h₂.2.2.2.2.1, angle_congr_trans h₁.2.2.2.2.2 h₂.2.2.2.2.2⟩

def three_pt_triangle (a b c : C.pts) : triangle := ⟨a, b, c⟩

notation `Δ` := three_pt_triangle

lemma three_pt_triangle_v1 (a b c : C.pts) : (Δ a b c).v1 = a := rfl

lemma three_pt_triangle_v2 (a b c : C.pts) : (Δ a b c).v2 = b := rfl

lemma three_pt_triangle_v3 (a b c : C.pts) : (Δ a b c).v3 = c := rfl

lemma tri_congr12 {a b c a' b' c': C.pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b a c) ≅ₜ (Δ b' a' c')) :=
begin
  unfold tri_congr, rw [three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3, three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3],
  rw [segment_symm, @segment_symm C.to_incidence_order_geometry a' b'],
  rw [@angle_symm C.to_incidence_order_geometry a c b, @angle_symm C.to_incidence_order_geometry a' c' b'],
  tauto
end

lemma tri_congr13 {a b c a' b' c': C.pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c b a) ≅ₜ (Δ c' b' a')) :=
begin
  unfold tri_congr, rw [three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3, three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3],
  rw [segment_symm, @segment_symm C.to_incidence_order_geometry a' b'],
  rw [@segment_symm C.to_incidence_order_geometry a c, @segment_symm C.to_incidence_order_geometry a' c'],
  rw [@segment_symm C.to_incidence_order_geometry b c, @segment_symm C.to_incidence_order_geometry b' c'],
  rw [@angle_symm C.to_incidence_order_geometry b a c, @angle_symm C.to_incidence_order_geometry b' a' c'],
  rw [@angle_symm C.to_incidence_order_geometry a c b, @angle_symm C.to_incidence_order_geometry a' c' b'],
  rw [@angle_symm C.to_incidence_order_geometry a b c, @angle_symm C.to_incidence_order_geometry a' b' c'],
  tauto
end

lemma tri_congr23 {a b c a' b' c': C.pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ a c b) ≅ₜ (Δ a' c' b')) :=
begin
  unfold tri_congr, rw [three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3, three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3],
  rw [segment_symm, @segment_symm C.to_incidence_order_geometry a' b'],
  rw [@segment_symm C.to_incidence_order_geometry a c, @segment_symm C.to_incidence_order_geometry a' c'],
  rw [@segment_symm C.to_incidence_order_geometry b c, @segment_symm C.to_incidence_order_geometry b' c'],
  rw [@angle_symm C.to_incidence_order_geometry b a c, @angle_symm C.to_incidence_order_geometry b' a' c'],
  rw [@angle_symm C.to_incidence_order_geometry a c b, @angle_symm C.to_incidence_order_geometry a' c' b'],
  rw [@angle_symm C.to_incidence_order_geometry a b c, @angle_symm C.to_incidence_order_geometry a' b' c'],
  tauto
end

lemma tri_congr123 {a b c a' b' c': C.pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b c a) ≅ₜ (Δ b' c' a')) := λh, tri_congr23 (tri_congr12 h)

lemma tri_congr132 {a b c a' b' c': C.pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c a b) ≅ₜ (Δ c' a' b')) := λh, tri_congr23 (tri_congr13 h)

lemma tri_congr_side {a b c a' b' c': C.pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
((a-ₛb) ≅ₛ (a'-ₛb')) ∧ ((a-ₛc) ≅ₛ (a'-ₛc')) ∧ ((b-ₛc) ≅ₛ (b'-ₛc')) :=
begin
  unfold tri_congr three_pt_triangle at h, simp at h,
  exact ⟨h.1, h.2.1, h.2.2.1⟩
end

lemma tri_congr_angle {a b c a' b' c': C.pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
(∠ b a c ≅ₐ ∠ b' a' c') ∧ (∠ a b c ≅ₐ ∠ a' b' c') ∧ (∠ a c b ≅ₐ ∠ a' c' b') :=
begin
  unfold tri_congr three_pt_triangle at h, simp at h,
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
end

lemma SAS {ABC DEF : @triangle C} (h₁ : noncollinear ABC.v1 ABC.v2 ABC.v3) (h₂ : noncollinear DEF.v1 DEF.v2 DEF.v3)
(hs₁ : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2)) (hs₂ : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3))
(ha : (∠ABC.v2 ABC.v1 ABC.v3 ≅ₐ ∠DEF.v2 DEF.v1 DEF.v3)) : ABC ≅ₜ DEF :=
⟨hs₁, hs₂, (C.C6 h₁ h₂ hs₁ hs₂ ha).1, ha, (C.C6 h₁ h₂ hs₁ hs₂ ha).2.1, (C.C6 h₁ h₂ hs₁ hs₂ ha).2.2⟩

lemma supplementary_congr {a b c d a' b' c' d' : C.pts}
(h : supplementary (∠b a c) (∠b a d)) (h' : supplementary (∠b' a' c') (∠b' a' d')) :
(∠b a c ≅ₐ ∠b' a' c') → (∠b a d ≅ₐ ∠b' a' d') :=
begin
  intro hbac,
  rcases extend_congr_segment a' b' (a-ₛb) with ⟨x, ha'b'x, haba'b', -⟩,
  rcases extend_congr_segment a' c' (a-ₛc) with ⟨y, ha'b'y, haca'c', -⟩,
  rcases extend_congr_segment a' d' (a-ₛd) with ⟨z, ha'b'z, hada'd', -⟩,
  have : (∠b' a' c') = (∠x a' y),
    unfold three_pt_angle, simp,
    rw [(two_pt_ray_eq_same_side_pt_pt.1 ha'b'x).1, (two_pt_ray_eq_same_side_pt_pt.1 ha'b'y).1],
  rw this at h' hbac,
  have : (∠b' a' d') = (∠x a' z),
    unfold three_pt_angle, simp,
    rw [(two_pt_ray_eq_same_side_pt_pt.1 ha'b'x).1, (two_pt_ray_eq_same_side_pt_pt.1 ha'b'z).1],
  rw this at h', rw this,
  clear this this ha'b'x ha'b'y ha'b'z b' c' d',
  rename [x b', y c', z d'],
  have h₁ : ((Δ a b c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triangle; simp,
    rintros ⟨l, hl, habcl⟩, apply nontrivial_iff_noncollinear.1 h.2.1, use l, tauto,
    rintros ⟨l, hl, habcl'⟩, apply nontrivial_iff_noncollinear.1 h'.2.1, use l, tauto,
    exact haba'b', exact haca'c', exact hbac,
  have hcad := is_between_diff_side_pt.2 (is_between_diff_side_pt.1 (three_pt_angle_supplementary.1 h).1),
  have hc'a'd' := is_between_diff_side_pt.2 (is_between_diff_side_pt.1 (three_pt_angle_supplementary.1 h').1),
  have h₂ : ((Δ c b d) ≅ₜ (Δ c' b' d')),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear23 (collinear_trans' (is_between_collinear hcad) (noncollinear13 (nontrivial_iff_noncollinear.1 h.2.1)) (is_between_not_eq hcad).2.1),
    exact noncollinear23 (collinear_trans' (is_between_collinear hc'a'd') (noncollinear13 (nontrivial_iff_noncollinear.1 h'.2.1)) (is_between_not_eq hc'a'd').2.1),
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry c' _],
    exact (tri_congr_side h₁).2.2,
    refine congr_segment_add hcad hc'a'd' _ _,
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry c' _], exact haca'c',
    exact hada'd',
    rw ←angle_eq_same_side b (is_between_same_side_pt.1 hcad).1,
    rw ←angle_eq_same_side b' (is_between_same_side_pt.1 hc'a'd').1,
    rw [angle_symm, @angle_symm C.to_incidence_order_geometry b' _ _],
    exact (tri_congr_angle h₁).2.2,
  have h₃ : ((Δ d b a) ≅ₜ (Δ d' b' a')),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear12 (noncollinear23 (nontrivial_iff_noncollinear.1 h.2.2)),
    exact noncollinear12 (noncollinear23 (nontrivial_iff_noncollinear.1 h'.2.2)),
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry d' _], exact (tri_congr_side h₂).2.2,
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry d' _], exact hada'd',
    rw ←angle_eq_same_side b (is_between_same_side_pt.1 hcad).2,
    rw ←angle_eq_same_side b' (is_between_same_side_pt.1 hc'a'd').2,
    rw [angle_symm, @angle_symm C.to_incidence_order_geometry b' _ _], exact (tri_congr_angle h₂).2.2,
  rw [angle_symm, @angle_symm C.to_incidence_order_geometry b' _ _], exact (tri_congr_angle h₃).2.2
end

lemma vertical_angle_congr {a b a' b' o : C.pts} (haob : noncollinear a o b) :
C.is_between a o a' → C.is_between b o b' → (∠ a o b ≅ₐ ∠ a' o b') :=
begin
  intros haoa' hbob',
  rcases (is_between_collinear haoa') with ⟨l, hl, hal, hol, ha'l⟩,
  rcases (is_between_collinear hbob') with ⟨m, hm, hbm, hom, hb'm⟩,
  have h₁ : supplementary (∠ a o b) (∠ a o b'),
    rw three_pt_angle_supplementary, split, exact hbob',
    split, exact haob,
    rintros ⟨n, hn, han, hon, hb'n⟩,
    rw two_pt_one_line hm hn (is_between_not_eq hbob').2.2 ⟨hom, hb'm⟩ ⟨hon, hb'n⟩ at hbm,
    exact haob ⟨n, hn, han, hon, hbm⟩,
  have h₂ : supplementary (∠ b' o a) (∠ b' o a'),
    rw three_pt_angle_supplementary, split, exact haoa',
    split, rintros ⟨n, hn, hb'n, hon, han⟩,
    rw two_pt_one_line hm hn (is_between_not_eq hbob').2.2 ⟨hom, hb'm⟩ ⟨hon, hb'n⟩ at hbm,
    exact haob ⟨n, hn, han, hon, hbm⟩,
    rintro ⟨n, hn, hb'n, hon, ha'n⟩,
    rw two_pt_one_line hn hl (is_between_not_eq haoa').2.2 ⟨hon, ha'n⟩ ⟨hol, ha'l⟩ at hb'n,
    rw two_pt_one_line hm hl (is_between_not_eq hbob').2.2 ⟨hom, hb'm⟩ ⟨hol, hb'n⟩ at hbm,
    exact haob ⟨l, hl, hal, hol, hbm⟩,
  rw supplementary_symm at h₁, rw @angle_symm C.to_incidence_order_geometry a' _ _,
  apply supplementary_congr h₁ h₂, rw angle_symm, exact angle_congr_refl _
end

lemma angle_eq_same_side_unique {a b c d : C.pts} (h : ∠ b a c ≅ₐ ∠b a d)
(hbac : noncollinear b a c) : same_side_line (b-ₗa) c d → same_side_pt a c d :=
begin
  have hab := (noncollinear_not_eq hbac).1.symm,
  intro hcd,
  have hbad : noncollinear b a d,
    rintros ⟨l, hl, hbl, hal, hdl⟩,
    rw two_pt_one_line hl (line_in_lines hab.symm) hab ⟨hal, hbl⟩ ⟨pt_right_in_line b a, pt_left_in_line b a⟩ at hdl,
    exact (same_side_line_not_in (line_in_lines hab.symm) hcd).2 hdl,
  rcases extend_congr_angle (∠ c a b) a b c with ⟨p, hpab, hpc, hu⟩,
  have h₁ := hu c hpc (angle_congr_refl _),
  rw line_symm at hcd, rw [angle_symm, @angle_symm C.to_incidence_order_geometry _ _ d] at h,
  have h₂ := hu d (same_side_line_trans (line_in_lines hab) hpc hcd) h,
  unfold two_pt_ray at h₁ h₂, simp at h₁ h₂,
  cases h₁ with hf h₁, exact absurd hf (noncollinear_not_eq hbac).2.1.symm,
  cases h₂ with hf h₂, exact absurd hf (noncollinear_not_eq hbad).2.1.symm,
  exact same_side_pt_trans (same_side_pt_symm h₁) h₂
end

private lemma congr_angle_add_prep1 {α : angle} (s : segment) {b a c : C.pts} (hbac : (∠ b a c) ≅ₐ α) :
∃ b' : C.pts, ((∠ b' a c) ≅ₐ α) ∧ ((a-ₛb') ≅ₛ s) ∧ same_side_pt a b b' :=
begin
  rcases extend_congr_segment a b s with ⟨b', habb', hs, h⟩, use b',
  have : ∠ c a b = ∠ c a b', from angle_eq_same_side c habb',
  rw [angle_symm, ←this, angle_symm], exact ⟨hbac, segment_congr_symm hs, habb'⟩
end

private lemma congr_angle_add_prep2 {a b c d a' b' c' d' : C.pts}
(hd : inside_angle d (∠ b a c)) (hb'c' : diff_side_line (a'-ₗd') b' c')
(hbac : noncollinear b a c) (ha'd' : a' ≠ d')
(hbad : ∠ b a d ≅ₐ ∠ b' a' d') (hdac : ∠ d a c ≅ₐ ∠ d' a' c') : noncollinear b' a' c' :=
begin
  rw inside_three_pt_angle at hd,
  have hab := (noncollinear_not_eq hbac).1.symm,
  have hac := (noncollinear_not_eq hbac).2.1,
  have had : a ≠ d,
    intro hf, rw hf at hd,
    unfold same_side_line at hd, apply hd.1,
    exact ⟨d, pt_left_in_line d b, by {unfold two_pt_segment, simp}⟩,
  intro hf, rcases hf with ⟨l, hl, hb'l, ha'l, hc'l⟩,
  have ha'b' : a' ≠ b',
    intro hf, rw hf at hb'c', exact hb'c'.2.1 (pt_left_in_line b' d'),
  have ha'c' : a' ≠ c',
    intro hf, rw hf at hb'c', exact hb'c'.2.2 (pt_left_in_line c' d'),
  cases (line_separation ⟨l, hl, ha'l, hb'l, hc'l⟩ ha'b'.symm ha'c'.symm).1 with h h,
  have : same_side_line (a'-ₗd') b' c',
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact ha'd'.symm,
    rw line_symm, exact hb'c'.2.1,
    left, exact h,
    intro hf, rw hf at hb'c', exact hb'c'.2.2 (pt_left_in_line a' d'),
  rw ←not_diff_side_line at this, exact this hb'c',
  exact (line_in_lines ha'd'), exact hb'c'.2.1, exact hb'c'.2.2,
  have h₁ : supplementary (∠ d' a' b') (∠ d' a' c'),
    rw [three_pt_angle_supplementary, is_between_diff_side_pt],
    split, exact h,
    split, rintros ⟨m, hm, hd'm, ha'm, hb'm⟩,
    rw two_pt_one_line hm (line_in_lines ha'd') ha'd' ⟨ha'm, hd'm⟩ ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hb'm,
    exact hb'c'.2.1 hb'm,
    rintros ⟨m, hm, hd'm, ha'm, hc'm⟩,
    rw two_pt_one_line hm (line_in_lines ha'd') ha'd' ⟨ha'm, hd'm⟩ ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hc'm,
    exact hb'c'.2.2 hc'm,
  cases (is_between_extend hab.symm) with x hbax,
  have h₂ : supplementary (∠ d a b) (∠ d a x),
    rw three_pt_angle_supplementary, split, exact hbax,
    have : noncollinear d a b,
      rintros ⟨m, hm, hdm, ham, hbm⟩,
      rw two_pt_one_line hm (line_in_lines hab) hab ⟨ham, hbm⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hdm,
      exact (same_side_line_not_in (line_in_lines hab) hd.1).2 hdm,
    split, exact this,
    rintros ⟨m, hm, hdm, ham, hxm⟩,
    have hax := (is_between_not_eq hbax).2.2,
    rw two_pt_one_line hm (line_in_lines hab) hax at hdm,
    exact this ⟨(a-ₗb), line_in_lines hab, hdm, pt_left_in_line a b, pt_right_in_line a b⟩,
    exact ⟨ham, hxm⟩, split, exact pt_left_in_line a b,
    rw line_symm, apply ray_in_line b a, left, exact (is_between_same_side_pt.1 hbax).1,
  have hdax : ((∠ d a x) ≅ₐ (∠ d a c)),
    refine angle_congr_trans _ (angle_congr_symm hdac),
    apply supplementary_congr h₂ h₁, rw [angle_symm, @angle_symm C.to_incidence_order_geometry d' _ _],
    exact hbad,
  rw three_pt_angle_supplementary at h₂,
  have key : same_side_pt a x c,
    refine angle_eq_same_side_unique hdax _ _, exact h₂.2.2,
    have hbx : diff_side_line (a-ₗd) b x,
      rw is_between_diff_side_pt at hbax, replace hbax := diff_side_pt_line hbax,
      refine hbax.2.2.2 _ _, exact line_in_lines had,
      split, exact pt_left_in_line a d,
      split, intro hf, exact h₂.2.1 ⟨(a-ₗd), line_in_lines had, pt_right_in_line a d, pt_left_in_line a d, hf⟩,
      intro hf, exact h₂.2.2 ⟨(a-ₗd), line_in_lines had, pt_right_in_line a d, pt_left_in_line a d, hf⟩,
    have hbc : diff_side_line (a-ₗd) b c,
      cases crossbar (inside_three_pt_angle.2 hd) with x hx, use x,
      exact ⟨(ray_in_line a d) hx.1, hx.2⟩,
      split, intro hf, exact h₂.2.1 ⟨(a-ₗd), line_in_lines had, pt_right_in_line a d, pt_left_in_line a d, hf⟩,
      intro hf, apply (same_side_line_not_in (line_in_lines hac) hd.2.1).2,
      rw two_pt_one_line (line_in_lines hac) (line_in_lines had) hac, exact pt_right_in_line a d,
      exact ⟨pt_left_in_line a c, pt_right_in_line a c⟩, exact ⟨pt_left_in_line a d, hf⟩,
    rw line_symm,
    exact diff_side_line_cancel (line_in_lines had) (diff_side_line_symm (line_in_lines had) hbx) hbc,
  rcases is_between_collinear hbax with ⟨m, hm, hbm, ham, hxm⟩,
  rcases key.2 with ⟨n, hn, han, hxn, hcn⟩,
  have hax := (is_between_not_eq h₂.1).2.2,
  rw two_pt_one_line hn hm hax ⟨han, hxn⟩ ⟨ham, hxm⟩ at hcn,
  exact hbac ⟨m, hm, hbm, ham, hcn⟩
end

lemma congr_angle_add {a b c d a' b' c' d' : C.pts}
(hd : inside_angle d (∠ b a c)) (hb'c' : diff_side_line (a'-ₗd') b' c') (ha'd' : a' ≠ d')
(h₁ : ∠ b a d ≅ₐ ∠ b' a' d') (h₂ : ∠ d a c ≅ₐ ∠ d' a' c') :
inside_angle d' (∠ b' a' c') ∧ (∠ b a c ≅ₐ ∠ b' a' c') :=
begin
  have hbac := inside_angle_nontrivial ⟨d, hd⟩, rw nontrivial_iff_noncollinear at hbac,
  have hb'a'c' := congr_angle_add_prep2 hd hb'c' hbac ha'd' h₁ h₂,
  have hab := (noncollinear_not_eq hbac).1.symm,
  have hac := (noncollinear_not_eq hbac).2.1,
  have hbc := (noncollinear_not_eq hbac).2.2.symm,
  have wtlg : ∃ p : C.pts, inside_angle p (∠ b a c) ∧ ∠ b a d = ∠ b a p ∧ ∠ d a c = ∠ p a c ∧ C.is_between b p c,
    cases crossbar hd with p hp, use p,
    rw inside_three_pt_angle at hd,
    by_cases hdp : d = p,
      rw ←hdp at hp, unfold two_pt_segment at hp, simp at hp, rcases hp.2 with hp | hp | hp,
      rw hp at hd, exact absurd (pt_right_in_line a b) (same_side_line_not_in (line_in_lines hab) hd.1).2,
      rw hp at hd, exact absurd (pt_right_in_line a c) (same_side_line_not_in (line_in_lines hac) hd.2.1).2,
      rw ←hdp, exact ⟨inside_three_pt_angle.2 hd, rfl, rfl, hp⟩,
    have had : a ≠ d,
      have := same_side_line_not_in (line_in_lines hab) hd.1,
      intro had, rw ←had at this, exact this.2 (pt_left_in_line a b),
    have hap : a ≠ p,
      intro hap, rw ←hap at hp, have : a ∈ (b-ₗc), from (segment_in_line b c) hp.2,
      exact hbac ⟨b-ₗc, line_in_lines hbc, pt_left_in_line b c, this, pt_right_in_line b c⟩,
    have ha : a ∈ ↑(line d p),
      have ha := pt_left_in_line a d,
      rw two_pt_one_line (line_in_lines had) (line_in_lines hdp) hdp
        ⟨pt_right_in_line a d, (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line d p, pt_right_in_line d p⟩ at ha,
      exact ha,
    have hadp : same_side_pt a d p,
      cases hp.1 with h h, exact h, simp at h, exact absurd h.symm hap,
    have : same_side_line (a-ₗb) d p,
      rintros ⟨x, hx⟩,
      have : (a-ₗb) ≠ (d-ₗp),
        intro hf, have := pt_left_in_line d p, rw ←hf at this,
        exact (same_side_line_not_in (line_in_lines hab) hd.1).2 this,
      have hax := two_line_one_pt (line_in_lines hab) (line_in_lines hdp) this (pt_left_in_line a b) ha hx.1 ((segment_in_line d p) hx.2),
      rw ←hax at hx,
      unfold two_pt_segment at hx, simp at hx, rcases hx.2 with hx | hx | hx,
      exact had hx, exact hap hx,
      rw [is_between_diff_side_pt, ←not_same_side_pt hadp.2 had.symm hap.symm] at hx,
      exact hx hadp,
    split, rw inside_three_pt_angle, split,
    exact same_side_line_trans (line_in_lines hab) hd.1 this,
    have : same_side_line (a-ₗc) d p,
      rintros ⟨x, hx⟩,
      have : (a-ₗc) ≠ (d-ₗp),
        intro hf, have := pt_left_in_line d p, rw ←hf at this,
        exact (same_side_line_not_in (line_in_lines hac) hd.2.1).2 this,
      have hax := two_line_one_pt (line_in_lines hac)
        (line_in_lines hdp) this (pt_left_in_line a c) ha hx.1 ((segment_in_line d p) hx.2),
      rw ←hax at hx,
      have : same_side_pt a d p,
        cases hp.1 with h h, exact h, simp at h, exact absurd h.symm hap,
      unfold two_pt_segment at hx, simp at hx, rcases hx.2 with hx | hx | hx,
      exact had hx, exact hap hx,
      rw [is_between_diff_side_pt, ←not_same_side_pt this.2 had.symm hap.symm] at hx,
      exact hx this,
    split,
    exact same_side_line_trans (line_in_lines hac) hd.2.1 this, exact hbac,
    split, exact angle_eq_same_side b hadp,
    split, rw [angle_symm, angle_eq_same_side c hadp, angle_symm],
    unfold two_pt_segment at hp, simp at hp, rcases hp.2 with hpb | hpc | hp,
    rw hpb at hp, have := pt_right_in_line a d,
    rw two_pt_one_line (line_in_lines had) (line_in_lines hab) hab
      ⟨pt_left_in_line a d, (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at this,
    exact absurd this (same_side_line_not_in (line_in_lines hab) hd.1).2,
    rw hpc at hp, have := pt_right_in_line a d,
    rw two_pt_one_line (line_in_lines had) (line_in_lines hac) hac
      ⟨pt_left_in_line a d, (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at this,
    exact absurd this (same_side_line_not_in (line_in_lines hac) hd.2.1).2,
    exact hp,
  rcases wtlg with ⟨p, hp, hp₁, hp₂, hbpc⟩, rw hp₁ at h₁, rw hp₂ at h₂, clear hd hp₁ hp₂ d,
  rw inside_three_pt_angle at hp,
  rename [p d, hp hd, hbpc hbdc],
  rcases congr_angle_add_prep1 (a-ₛb) (angle_congr_refl (∠ b' a' d')) with ⟨b'', hb''a'd', ha'b''ab, ha'b'b''⟩,
  rcases congr_angle_add_prep1 (a-ₛd) (angle_congr_refl (∠ d' a' b'')) with ⟨d'', hd''a'b', ha'd''ad, ha'd'd''⟩,
  rcases congr_angle_add_prep1 (a-ₛc) (angle_congr_refl (∠ c' a' d')) with ⟨c'', hc''a'd', ha'c''ac, ha'c'c''⟩,
  have ha'b' := (same_side_pt_not_eq ha'b'b'').1.symm,
  have ha'b'' := (same_side_pt_not_eq ha'b'b'').2.symm,
  have ha'd'' := (same_side_pt_not_eq ha'd'd'').2.symm,
  have ha'c' := (same_side_pt_not_eq ha'c'c'').1.symm,
  have ha'c'' := (same_side_pt_not_eq ha'c'c'').2.symm,
  have ha'd''b'' : noncollinear a' d'' b'',
    rintros ⟨l, hl, ha'l, hd''l, hb''l⟩,
    rcases ha'b'b''.2 with ⟨m, hm, ha'm, hb'm, hb''m⟩,
    rcases ha'd'd''.2 with ⟨n, hn, ha'n, hd'n, hd''n⟩,
    rw two_pt_one_line hm hl ha'b'' ⟨ha'm, hb''m⟩ ⟨ha'l, hb''l⟩ at hb'm,
    rw two_pt_one_line hl hn ha'd'' ⟨ha'l, hd''l⟩ ⟨ha'n, hd''n⟩ at hb'm,
    rw two_pt_one_line hn (line_in_lines ha'd') ha'd' ⟨ha'n, hd'n⟩ ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hb'm,
    exact hb'c'.2.1 hb'm,
  have ha'c'' := (same_side_pt_not_eq ha'c'c'').2.symm,
  have ha'd'' := (same_side_pt_not_eq ha'd'd'').2.symm,
  have ha'd' := (same_side_pt_not_eq ha'd'd'').1.symm,
  have ha'd''c'' : noncollinear a' d'' c'',
    rintros ⟨l, hl, ha'l, hd''l, hc''l⟩,
    rcases ha'c'c''.2 with ⟨m, hm, ha'm, hc'm, hc''m⟩,
    rcases ha'd'd''.2 with ⟨n, hn, ha'n, hd'n, hd''n⟩,
    rw two_pt_one_line hm hl ha'c'' ⟨ha'm, hc''m⟩ ⟨ha'l, hc''l⟩ at hc'm,
    rw two_pt_one_line hl hn ha'd'' ⟨ha'l, hd''l⟩ ⟨ha'n, hd''n⟩ at hc'm,
    rw two_pt_one_line hn (line_in_lines ha'd') ha'd' ⟨ha'n, hd'n⟩ ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hc'm,
    exact hb'c'.2.2 hc'm,
  replace h₁ : (∠ b a d ≅ₐ ∠ b'' a' d''),
    apply angle_congr_trans (angle_congr_trans h₁ (angle_congr_symm hb''a'd')), rw angle_symm,
    apply angle_congr_trans (angle_congr_symm hd''a'b'), rw angle_symm, exact angle_congr_refl _,
  replace h₂ : (∠ d a c ≅ₐ ∠ d'' a' c''),
    apply angle_congr_trans h₂, rw angle_symm, apply angle_congr_trans (angle_congr_symm hc''a'd'),
    rw [angle_eq_same_side c'' ha'd'd'', angle_symm], exact angle_congr_refl _,
  have habd : ((Δ a b d) ≅ₜ (Δ a' b'' d'')),
    apply SAS; unfold three_pt_triangle; simp,
    intro habd, exact (same_side_line_not_in (line_in_lines hab) hd.1).2 (collinear_in12 habd hab),
    exact noncollinear23 ha'd''b'',
    exact segment_congr_symm ha'b''ab, exact segment_congr_symm ha'd''ad, exact h₁,
  have hacd : ((Δ a c d) ≅ₜ (Δ a' c'' d'')),
    apply SAS; unfold three_pt_triangle; simp,
    intro hacd, exact (same_side_line_not_in (line_in_lines hac) hd.2.1).2 (collinear_in12 hacd hac),
    exact noncollinear23 ha'd''c'',
    exact segment_congr_symm ha'c''ac, exact segment_congr_symm ha'd''ad,
    rw angle_symm, apply angle_congr_trans h₂, rw angle_symm, exact angle_congr_refl _,
  have hb''d'' : b'' ≠ d'',
    intro hb''d'', rw ←hb''d'' at ha'd'd'',
    rcases (same_side_pt_trans ha'b'b'' (same_side_pt_symm ha'd'd'')).2 with ⟨l, hl, ha'l, hb'l, hd'l⟩,
    have ha'd' := (same_side_pt_not_eq ha'd'd'').1.symm,
    rw two_pt_one_line hl (line_in_lines ha'd') ha'd' ⟨ha'l, hd'l⟩ ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ at hb'l,
    exact hb'c'.2.1 hb'l,
  cases is_between_extend hb''d'' with x hb''xd'',
  have ha'd''x : noncollinear a' d'' x,
    rintros ⟨l, hl, ha'l, hd''l, hxl⟩,
    rcases is_between_collinear hb''xd'' with ⟨m, hm, hb''m, hd''m, hxm⟩,
    have hd''x := (is_between_not_eq hb''xd'').2.2,
    rw two_pt_one_line hm hl hd''x ⟨hd''m, hxm⟩ ⟨hd''l, hxl⟩ at hb''m,
    exact ha'd''b'' ⟨l, hl, ha'l, hd''l, hb''m⟩,
  have hb''a'c'' : noncollinear b'' a' c'',
    rintros ⟨l, hl, hb''l, ha'l, hc''l⟩,
    rcases ha'b'b''.2 with ⟨m, hm, ha'm, hb'm, hb''m⟩,
    rcases ha'c'c''.2 with ⟨n, hn, ha'n, hc'n, hc''n⟩,
    rw two_pt_one_line hn hl ha'c'' ⟨ha'n, hc''n⟩ ⟨ha'l, hc''l⟩ at hc'n,
    rw two_pt_one_line hl hm ha'b'' ⟨ha'l, hb''l⟩ ⟨ha'm, hb''m⟩ at hc'n,
    exact hb'a'c' ⟨m, hm, hb'm, ha'm, hc'n⟩,
  have key : (∠ a' d'' x ≅ₐ ∠ a' d'' c''),
    refine angle_congr_trans _ (tri_congr_angle hacd).2.2,
    have h₁ : supplementary (∠ a d b) (∠ a d c),
      rw three_pt_angle_supplementary, split, exact hbdc,
      split, rintros ⟨l, hl, hal, hdl, hbl⟩,
      rw two_pt_one_line hl (line_in_lines hab) hab ⟨hal, hbl⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hdl,
      exact (same_side_line_not_in (line_in_lines hab) hd.1).2 hdl,
      rintros ⟨l, hl, hal, hdl, hcl⟩,
      rw two_pt_one_line hl (line_in_lines hac) hac ⟨hal, hcl⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at hdl,
      exact (same_side_line_not_in (line_in_lines hac) hd.2.1).2 hdl,
    have h₂ : supplementary (∠ a' d'' x) (∠ a' d'' b''),
      rw three_pt_angle_supplementary, split, rw is_between_symm, exact hb''xd'',
      exact ⟨ha'd''x, ha'd''b''⟩,
    rw supplementary_symm at h₂, apply angle_congr_symm,
    exact supplementary_congr h₁ h₂ (tri_congr_angle habd).2.2,
  have hx : x ∉ (a'-ₗd''),
    intro hx, exact ha'd''x ⟨(a'-ₗd''), line_in_lines ha'd'', pt_left_in_line a' d'', pt_right_in_line a' d'', hx⟩,
  have : same_side_line (a'-ₗd'') x c'',
    have hb'b'' : same_side_line (a'-ₗd'') b'' b',
      rw line_symm, refine t_shape_ray ha'd''.symm _ _ _ _,
      intro hf, exact ha'd''b'' ⟨(d''-ₗa'), line_in_lines ha'd''.symm, pt_right_in_line d'' a', pt_left_in_line d'' a', hf⟩,
      unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'', exact ha'b'.symm,
    have hc'c'' : same_side_line (a'-ₗd'') c'' c',
      rw line_symm, refine t_shape_ray ha'd''.symm _ _ _ _,
      intro hf, exact ha'd''c'' ⟨(d''-ₗa'), line_in_lines ha'd''.symm, pt_right_in_line d'' a', pt_left_in_line d'' a', hf⟩,
      unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c'', exact ha'c'.symm,
    have hb'' : b'' ∉ (a'-ₗd''),
      from λhf, ha'd''b'' ⟨(a'-ₗd''), line_in_lines ha'd'', pt_left_in_line a' d'', pt_right_in_line a' d'', hf⟩,
    have hx : x ∉ (a'-ₗd''),
      from λhf, ha'd''x ⟨(a'-ₗd''), line_in_lines ha'd'', pt_left_in_line a' d'', pt_right_in_line a' d'', hf⟩,
    have hxb'' : diff_side_line (a'-ₗd'') x b'',
    apply diff_side_line_symm, exact line_in_lines ha'd'',
    rw is_between_diff_side_pt at hb''xd'', replace hb''xd'' := diff_side_pt_line hb''xd'',
    apply hb''xd''.2.2.2 (line_in_lines ha'd''),
    exact ⟨pt_right_in_line a' d'', hb'', hx⟩,
  have hxb' := diff_side_same_side_line (line_in_lines ha'd'') hxb'' hb'b'',
  have : (a'-ₗd') = (a'-ₗd''),
    have : d' ∈ (a'-ₗd''),
      apply ray_in_line a' d'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact two_pt_one_line (line_in_lines ha'd') (line_in_lines ha'd'') ha'd'
      ⟨pt_left_in_line a' d', pt_right_in_line a' d'⟩ ⟨pt_left_in_line a' d'', this⟩,
    rw this at hb'c',
  have hxc' := diff_side_line_cancel (line_in_lines ha'd'') hxb' hb'c',
  exact same_side_line_trans (line_in_lines ha'd'') hxc' (same_side_line_symm (line_in_lines ha'd'') hc'c''),
  have hd''xc'' := angle_eq_same_side_unique key ha'd''x this,
  have hb''d''c'' := is_between_same_side_pt_is_between hb''xd'' hd''xc'',
  have hcab : ((Δ c a b) ≅ₜ (Δ c'' a' b'')),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear13 hbac, exact noncollinear13 hb''a'c'',
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry c'' _], exact segment_congr_symm ha'c''ac,
    rw is_between_symm at hb''d''c'' hbdc, refine congr_segment_add hbdc hb''d''c'' _ _,
    exact (tri_congr_side hacd).2.2,
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry d'' _], exact (tri_congr_side habd).2.2,
    rw is_between_same_side_pt at hbdc hb''d''c'',
    rw [angle_eq_same_side a hbdc.2, angle_eq_same_side a' hb''d''c''.2],
    exact (tri_congr_angle hacd).2.1,
  have : (∠ b' a' c') = (∠ b'' a' c''),
    rw [angle_eq_same_side b' ha'c'c'', angle_symm, angle_eq_same_side c'' ha'b'b'', angle_symm],
  split, rotate,
  rw [this, angle_symm, @angle_symm C.to_incidence_order_geometry b'' _ _], exact (tri_congr_angle hcab).2.1,
  have hc'' : c'' ∉ (a'-ₗb''),
    from λhc'', hb''a'c'' ⟨(a'-ₗb''), line_in_lines ha'b'', pt_right_in_line a' b'', pt_left_in_line a' b'', hc''⟩,
  have hb'' : b'' ∉ (a'-ₗc''),
    from λhb'', hb''a'c'' ⟨(a'-ₗc''), line_in_lines ha'c'', hb'', pt_left_in_line a' c'', pt_right_in_line a' c''⟩,
  have hd'' : same_side_line (a'-ₗb'') c'' d'' ∧ same_side_line (a'-ₗc'') b'' d'',
    split,
    exact t_shape_ray ha'b'' hc'' d'' (by {unfold two_pt_ray, simp, right, exact same_side_pt_symm (is_between_same_side_pt.1 hb''d''c'').1}) (is_between_not_eq hb''d''c'').1.symm,
    exact t_shape_ray ha'c'' hb'' d'' (by {unfold two_pt_ray, simp, right, exact (is_between_same_side_pt.1 hb''d''c'').2}) (is_between_not_eq hb''d''c'').2.2,
  rw inside_three_pt_angle, split,
  rw two_pt_one_line (line_in_lines ha'b') (line_in_lines ha'b''),
  have hc'c'' : same_side_line (a'-ₗb'') c' c'',
    rw line_symm, apply same_side_line_symm (line_in_lines ha'b''.symm), refine t_shape_ray ha'b''.symm _ _ _ _,
    intro hf, exact hb''a'c'' ⟨(b''-ₗa'), line_in_lines ha'b''.symm, pt_left_in_line b'' a', pt_right_in_line b'' a', hf⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c'',
    exact ha'c'.symm,
  have hd'd'' : same_side_line (a'-ₗb'') d' d'',
    rw line_symm, apply same_side_line_symm (line_in_lines ha'b''.symm), refine t_shape_ray ha'b''.symm _ _ _ _,
    rw line_symm, intro hf,
    exact ha'd''b'' ⟨(a'-ₗb''), line_in_lines ha'b'', pt_left_in_line a' b'', hf, pt_right_in_line a' b''⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact ha'd'.symm,
  exact same_side_line_trans (line_in_lines ha'b'') (same_side_line_trans (line_in_lines ha'b'') hc'c'' hd''.1)
    (same_side_line_symm (line_in_lines ha'b'') hd'd''),
  exact ha'b', exact ⟨pt_left_in_line a' b', pt_right_in_line a' b'⟩,
  split, exact pt_left_in_line a' b'',
  apply ray_in_line a' b'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'',
  rw two_pt_one_line (line_in_lines ha'c') (line_in_lines ha'c''),
  have hb'b'' : same_side_line (a'-ₗc'') b' b'',
    rw line_symm, apply same_side_line_symm (line_in_lines ha'c''.symm), refine t_shape_ray ha'c''.symm _ _ _ _,
    intro hf, exact hb''a'c'' ⟨(c''-ₗa'), line_in_lines ha'c''.symm, hf, pt_right_in_line c'' a', pt_left_in_line c'' a'⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'',
    exact ha'b'.symm,
  have hd'd'' : same_side_line (a'-ₗc'') d' d'',
    rw line_symm, apply same_side_line_symm (line_in_lines ha'c''.symm), refine t_shape_ray ha'c''.symm _ _ _ _,intro hf,
    exact ha'd''c'' ⟨(c''-ₗa'), line_in_lines ha'c''.symm, pt_right_in_line c'' a', hf, pt_left_in_line c'' a'⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact ha'd'.symm,
  split,
  exact same_side_line_trans (line_in_lines ha'c'') (same_side_line_trans (line_in_lines ha'c'') hb'b'' hd''.2)
    (same_side_line_symm (line_in_lines ha'c'') hd'd''), exact hb'a'c',
  exact ha'c', exact ⟨pt_left_in_line a' c', pt_right_in_line a' c'⟩,
  split, exact pt_left_in_line a' c'',
  apply ray_in_line a' c'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c''
end

lemma congr_angle_sub {a b c d a' b' c' d' : C.pts}
(hd : inside_angle d (∠ b a c)) (h : same_side_line (a'-ₗb') d' c')
(ha'b' : a' ≠ b') (h₁ : ∠ b a c ≅ₐ ∠ b' a' c') (h₂ : ∠ b a d ≅ₐ ∠ b' a' d') :
inside_angle d' (∠ b' a' c') ∧ (∠ d a c ≅ₐ ∠ d' a' c') :=
begin
  have hbac := inside_angle_nontrivial ⟨d, hd⟩, rw nontrivial_iff_noncollinear at hbac,
  have hb'd' : b' ≠ d',
    intro hb'd', rw ←hb'd' at h, exact (same_side_line_not_in (line_in_lines ha'b') h).1 (pt_right_in_line a' b'), 
  have ha'd' : a' ≠ d',
    intro hb'd', rw ←hb'd' at h, exact (same_side_line_not_in (line_in_lines ha'b') h).1 (pt_left_in_line a' b'), 
  cases is_between_extend hb'd' with x hb'xd',
  have hb'x : diff_side_line (a'-ₗd') b' x,
    rw is_between_diff_side_pt at hb'xd', replace hb'xd' := diff_side_pt_line hb'xd',
    refine hb'xd'.2.2.2 _ _, exact line_in_lines ha'd',
    split, exact pt_right_in_line a' d',
    have :  b' ∉ ↑(line a' d'),
      intro hf, rw two_pt_one_line (line_in_lines ha'b') (line_in_lines ha'd') ha'b' ⟨pt_left_in_line a' b', pt_right_in_line a' b'⟩ ⟨pt_left_in_line a' d', hf⟩ at h,
      exact (same_side_line_not_in (line_in_lines ha'd') h).1 (pt_right_in_line a' d'),
    split, exact this,
    rcases hb'xd'.1 with ⟨l, hl, hd'l, hb'l, hxl⟩,
    intro hf, rw two_pt_one_line hl (line_in_lines ha'd') hb'xd'.2.2.1 ⟨hd'l, hxl⟩ ⟨pt_right_in_line a' d', hf⟩ at hb'l,
    exact this hb'l,
  rcases extend_congr_angle (∠ d a c) a' d' x with ⟨c'', hdac, hc''x, -⟩,
  rw @angle_symm C.to_incidence_order_geometry c'' _ _ at hdac,
  have hb'c'' : diff_side_line (a'-ₗd') b' c'',
    apply diff_side_same_side_line (line_in_lines ha'd') hb'x,
    exact same_side_line_symm (line_in_lines ha'd') hc''x,
/-
  have hxa'b' : x ∉ ↑(line a' b'),
    rw [is_between_same_side_pt, same_side_pt_line] at hb'xd',
    intro hf, rcases hb'xd'.1.1 with ⟨l, hl, hb'l, hd'l, hxl⟩,
    have : b' ≠ x,
      intro hf, have hx := hb'x.2.2,
      rw [hf, ←(not_same_side_line (line_in_lines ha'd') hx hx)] at hb'x,
      exact hb'x (same_side_line_refl (line_in_lines ha'd') hx),
    rw two_pt_one_line hl (line_in_lines ha'b') this ⟨hb'l, hxl⟩ ⟨pt_right_in_line a' b', hf⟩ at hd'l,
    exact (same_side_line_not_in (line_in_lines ha'b') h).1 hd'l,
  have hb'a'c'' : noncollinear b' a' c'',
    have h₁ : same_side_line (a'-ₗb') d' x,
      rw [is_between_same_side_pt, same_side_pt_line] at hb'xd',
      refine hb'xd'.1.2.2.2 _ _, exact line_in_lines ha'b',
      split, exact pt_right_in_line a' b',
      split, exact (same_side_line_not_in (line_in_lines ha'b') h).1,
      exact hxa'b',
-/
  have key := congr_angle_add hd hb'c'' ha'd' h₂ hdac,
  have hc'c'' : same_side_pt a' c' c'',
    apply same_side_pt_symm, rw inside_three_pt_angle at key,
    refine angle_eq_same_side_unique (angle_congr_symm (angle_congr_trans (angle_congr_symm h₁) key.2)) _ _,
    exact key.1.2.2, rw line_symm,
    exact same_side_line_trans (line_in_lines ha'b') key.1.1 h,
  rw [angle_eq_same_side d' hc'c'', angle_eq_same_side b' hc'c''],
  exact ⟨key.1, hdac⟩
end

def angle_lt (α β : angle) : Prop :=
 ∀ a b : C.pts, β = (∠ a β.vertex b)
→ ∃ p : C.pts, inside_angle p (∠ a β.vertex b) ∧ ((∠ a β.vertex p) ≅ₐ α)

local notation a`<ₐ`b := @angle_lt C a b

lemma three_pt_angle_lt {a o b : C.pts} {α : angle} :
(α <ₐ (∠ a o b)) ↔ ∃ p : C.pts, inside_angle p (∠ a o b) ∧ ((∠ a o p) ≅ₐ α):=
begin
  split, exact λh, h a b rfl,
  rintros ⟨p, hp, hα⟩,
  have haob := hp.2, rw nontrivial_iff_noncollinear at haob,
  intros a' b' he, rw three_pt_angle_vertex at he, rw three_pt_angle_vertex,
  have haop : noncollinear a o p,
    rintros ⟨l, hl, hal, hol, hpl⟩,
    rw inside_three_pt_angle at hp,
    rw two_pt_one_line hl (line_in_lines (noncollinear_not_eq haob).1.symm) at hpl,
    exact (same_side_line_not_in (line_in_lines (noncollinear_not_eq haob).1.symm) hp.1).2 hpl,
    exact (noncollinear_not_eq haob).1,
    exact ⟨hal, hol⟩, exact ⟨pt_right_in_line o a, pt_left_in_line o a⟩,
  cases ((three_pt_angle_eq_iff haob).1 he).2,
  have :  (∠ a' o p) =  (∠ a o p),
    cases ((three_pt_angle_eq_iff haob).1 he).1,
    rw [angle_symm, @angle_symm C.to_incidence_order_geometry a _ _],
    apply angle_eq_same_side, exact same_side_pt_symm h.1,
  use p, rw [←he, this], exact ⟨hp, hα⟩,
  rcases extend_congr_angle (∠ a o p) o a' b' with ⟨q, hqoa', hqb', -⟩,
  rw @angle_symm C.to_incidence_order_geometry q _ _ at hqoa',
  use q, split,
  refine (congr_angle_sub hp hqb' _ _ _).1,
  exact (same_side_pt_not_eq h.2).2.symm,
  rw he, exact angle_congr_refl _, exact hqoa',
  exact angle_congr_trans (angle_congr_symm hqoa') hα
end

/-
lemma three_pt_angle_lt {a o b : C.pts} {α : angle} (haob : noncollinear a o b) :
(α <ₐ (∠ a o b)) ↔ ∃ p : C.pts, inside_angle p (∠ a o b) ∧ ((∠ a o p) ≅ₐ α) :=
begin
  split, exact λh, h a b rfl,
  rintros ⟨p, hp, haop⟩,
  intros a' b' he, rw three_pt_angle_vertex at he, rw three_pt_angle_vertex,
  cases ((three_pt_angle_eq_iff haob).1 he).2,
  have haop : noncollinear a o p,
    rintros ⟨l, hl, hal, hol, hpl⟩,
    rw inside_three_pt_angle haob at hp,
    rw two_pt_one_line hl (line_in_lines (noncollinear_not_eq haob).1.symm) at hpl,
    exact (same_side_line_not_in (line_in_lines (noncollinear_not_eq haob).1.symm) hp.1).2 hpl,
    exact (noncollinear_not_eq haob).1,
    exact ⟨hal, hol⟩, exact ⟨pt_right_in_line o a, pt_left_in_line o a⟩,
  have :  (∠ a' o p) =  (∠ a o p),
    cases ((three_pt_angle_eq_iff haob).1 he).1,

end
-/

lemma angle_lt_congr {α β γ : angle} (hαβ : α ≅ₐ β) :
((α <ₐ γ) → (β <ₐ γ)) ∧ (angle_nontrivial β → (γ <ₐ α) → (γ <ₐ β)) :=
begin
  rcases angle_three_pt α with ⟨a₁, b₁, hα⟩,
  rcases angle_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases angle_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw [hα, hβ, hγ], rw [hα, hβ] at hαβ,
  set o₁ := α.vertex, set o₂ := β.vertex, set o₃ := γ.vertex,
  split, intro hαγ,
  rcases three_pt_angle_lt.1 hαγ with ⟨p, hpin, hp⟩,
  rw three_pt_angle_lt, use p,
  split, exact hpin,
  exact angle_congr_trans hp hαβ,
  intros h hγα,
  rcases three_pt_angle_lt.1 hγα with ⟨p, hpin, hp⟩,
  rcases extend_congr_angle (∠ a₁ o₁ p) o₂ a₂ b₂ with ⟨q, hq, hqb₂, -⟩,
  rw three_pt_angle_lt,
  rw @angle_symm C.to_incidence_order_geometry q _ _ at hq,
  use q, split,
  refine (congr_angle_sub hpin hqb₂ _ _ _).1,
  exact (noncollinear_not_eq (nontrivial_iff_noncollinear.1 h)).1.symm,
  exact hαβ, exact hq,
  exact angle_congr_trans (angle_congr_symm hq) hp
end

lemma inside_angle_trans {a b c d e : C.pts} :
inside_angle d (∠ b a c) → inside_angle e (∠ b a d) → inside_angle e (∠ b a c) :=
begin
  intros hd he,
  rw inside_three_pt_angle at *,
  have hac := (noncollinear_not_eq hd.2.2).2.1,
  have hab := (noncollinear_not_eq hd.2.2).1.symm,
  have hbc := (noncollinear_not_eq hd.2.2).2.2.symm,
  have hbd := (noncollinear_not_eq he.2.2).2.2.symm,
  have had := (noncollinear_not_eq he.2.2).2.1,
  have hae : a ≠ e,
    intro hae, rw ←hae at he,
    exact (same_side_line_not_in (line_in_lines hab) he.1).2 (pt_left_in_line a b),
  have hade : noncollinear a d e,
    rintros ⟨l, hl, hal, hdl, hel⟩,
    rw two_pt_one_line hl (line_in_lines had) had ⟨hal, hdl⟩ ⟨pt_left_in_line a d, pt_right_in_line a d⟩ at hel,
    exact (same_side_line_not_in (line_in_lines had) he.2.1).2 hel,
  split, exact (same_side_line_trans (line_in_lines hab) hd.1 he.1),
  split,
  cases crossbar (inside_three_pt_angle.2 hd) with d' hd',
  have : inside_angle e (∠ b a d'),
    have : same_side_pt a d d',
      unfold two_pt_ray at hd',
      cases hd'.1, exact h,
      simp at h, rw h at hd',
      exfalso, apply hd.2.2,
      exact ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, (segment_in_line b c) hd'.2, pt_right_in_line b c⟩,
    rw [←angle_eq_same_side b this, inside_three_pt_angle], exact he,
  have hbd' : b ≠ d',
    intro hbd', rw ←hbd' at hd',
    exact he.2.2 ⟨(a-ₗd), line_in_lines had, (ray_in_line a d) hd'.1, pt_left_in_line a d, pt_right_in_line a d⟩,
  cases crossbar this with e' he',
  have had' : a ≠ d',
    intro hf, rw ←hf at hd',
    exact hd.2.2 ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, (segment_in_line b c) hd'.2, pt_right_in_line b c⟩,
  have he'a : e' ≠ a,
    intro he'a, rw he'a at he'a, rw he'a at he',
    have : a ∈ (b-ₗc),
      rw two_pt_one_line (line_in_lines hbc) (line_in_lines hbd') hbd',
      exact (segment_in_line b d') he'.2,
      exact ⟨pt_left_in_line b c, (segment_in_line b c) hd'.2⟩,
      exact ⟨pt_left_in_line b d', pt_right_in_line b d'⟩,
    exfalso, apply hd.2.2,
    exact ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, this, pt_right_in_line b c⟩,
  have hdd' : same_side_line (a-ₗc) d d',
    rw line_symm, refine t_shape_ray _ _ _ _ _,
    exact hac.symm,
    rw line_symm, exact (same_side_line_not_in (line_in_lines hac) hd.2.1).2,
    exact hd'.1, exact had'.symm,
  have hbd'c : C.is_between b d' c,
    cases hd'.2, exact h,
    cases h, exact absurd h hbd'.symm,
    simp at h, rw h at hd', rw h at hdd',
    exact absurd (pt_right_in_line a c) (same_side_line_not_in (line_in_lines hac) hdd').2,
  have hbe'd' : C.is_between b e' d',
    cases he'.2, exact h,
    cases h, rw h at he',
    rw two_pt_one_line (line_in_lines hab) (line_in_lines hae) hab ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨pt_left_in_line a e, (ray_in_line a e) he'.1⟩ at he,
    exact absurd (pt_right_in_line a e) (same_side_line_not_in (line_in_lines hae) he.1).2,
    simp at h, rw h at he',
    have := pt_right_in_line a e,
    rw two_pt_one_line (line_in_lines hae) (line_in_lines had) had' at this,
    exfalso, apply hade,
    exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, this⟩,
    exact ⟨pt_left_in_line a e, (ray_in_line a e) he'.1⟩,
    exact ⟨pt_left_in_line a d, (ray_in_line a d) hd'.1⟩,
  have hee' : same_side_line (a-ₗc) e e',
    rw line_symm, apply same_side_line_symm (line_in_lines hac.symm),
    refine t_shape_ray _ _ _ _ _,
    exact hac.symm,
    rw line_symm, intro hf,
    have : e' ∈ (b-ₗc),
      rw two_pt_one_line (line_in_lines hbc) (line_in_lines hbd') hbd' ⟨pt_left_in_line b c, (segment_in_line b c) hd'.2⟩ ⟨pt_left_in_line b d', pt_right_in_line b d'⟩,
      exact (segment_in_line b d') he'.2,
    have hce' : c ≠ e',
      intro hce', rw ←hce' at he',
      cases he'.2 with h h, cases hd'.2 with h' h',
      exact (collinear_between (is_between_collinear h)).2.1 ⟨h, h'⟩,
      cases h' with h' h', rw h' at h, exact (is_between_not_eq h).2.1 rfl,
      simp at h', rw h' at h, exact (is_between_not_eq h).2.2 rfl,
      cases h with h h, exact hbc h.symm,
      simp at h, rw h at hdd',
      exact (same_side_line_not_in (line_in_lines had') hdd').2 (pt_right_in_line a d'),
    have hb := pt_left_in_line b c,
    rw two_pt_one_line (line_in_lines hbc) (line_in_lines hac) hce' ⟨pt_right_in_line b c, this⟩ ⟨pt_right_in_line a c, hf⟩ at hb,
    exact hd.2.2 ⟨(a-ₗc), line_in_lines hac, hb, pt_left_in_line a c, pt_right_in_line a c⟩,
    cases he'.1 with he' hf,
    left, exact same_side_pt_symm he',
    exact absurd hf he'a,
    intro hea, rw [hea, ray_singleton] at he', exact he'a he'.1,
  suffices : same_side_line (a-ₗc) d' e',
    from same_side_line_trans (line_in_lines hac) (same_side_line_trans (line_in_lines hac)
      (same_side_line_trans (line_in_lines hac) hd.2.1 hdd') this)
      (same_side_line_symm (line_in_lines hac) hee'),
  refine t_shape_ray hac _ _ _ _,
  exact (same_side_line_not_in (line_in_lines hac) hdd').2,
  rw is_between_symm at hbd'c hbe'd',
  left, simp, exact (is_between_same_side_pt.1 (is_between_trans' hbd'c hbe'd').1).1,
  intro hf, rw hf at hee', exact (same_side_line_not_in (line_in_lines hac) hee').2 (pt_right_in_line a c),
  exact hd.2.2
end

lemma angle_lt_trans {α β γ : angle} :
angle_nontrivial γ → (α <ₐ β) → (β <ₐ γ) → (α <ₐ γ) :=
begin
  intros h hαβ hβγ,
  rcases angle_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases angle_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw hγ, rw hβ at hαβ, rw [hβ, hγ] at hβγ, rw [hγ, nontrivial_iff_noncollinear] at h,
  set o₂ := β.vertex, set o₃ := γ.vertex,
  rcases three_pt_angle_lt.1 hαβ with ⟨p, hpin, hp⟩,
  rcases three_pt_angle_lt.1 hβγ with ⟨q, hqin, hq⟩,
  rcases extend_congr_angle α o₃ a₃ q with ⟨x, hx, hxq, -⟩,
  rw three_pt_angle_lt,
  use x, split,
  apply inside_angle_trans hqin,
  refine (congr_angle_sub hpin hxq _ _ _).1,
  exact (noncollinear_not_eq h).1.symm, exact angle_congr_symm hq,
  rw angle_symm at hx, exact angle_congr_trans hp hx,
  rw angle_symm, exact angle_congr_symm hx
end

lemma diff_same_side_line {a o b x : C.pts} :
diff_side_line (o-ₗb) a x → same_side_line (o-ₗa) x b → same_side_line (o-ₗx) a b :=
begin
  intros h₁ h₂,
  have hoa : o ≠ a,
    intro hoa, rw hoa at h₁, exact h₁.2.1 (pt_left_in_line a b),
  have hox : o ≠ x,
    intro hox, rw ←hox at h₂, exact (same_side_line_not_in (line_in_lines hoa) h₂).1 (pt_left_in_line o a),
  have hab : a ≠ b,
    intro hab, rw hab at h₁, exact h₁.2.1 (pt_right_in_line o b),
  have hob : o ≠ b,
    intro hob, rw hob at h₂, exact (same_side_line_not_in (line_in_lines hab.symm) h₂).2 (pt_left_in_line b a),
  have hax : a ≠ x,
    intro hax, rw ←hax at h₂, exact (same_side_line_not_in (line_in_lines hoa) h₂).1 (pt_right_in_line o a),
  cases h₁.1 with b' hb',
  have hab' : a ≠ b',
    intro hab', rw ←hab' at hb', exact h₁.2.1 hb'.1,
  have hob' : o ≠ b',
    intro hob', rw ←hob' at hb',
    rw two_pt_one_line (line_in_lines hoa) (line_in_lines hax) hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨(segment_in_line a x) hb'.2, pt_left_in_line a x⟩ at h₂,
    exact (same_side_line_not_in (line_in_lines hax) h₂).1 (pt_right_in_line a x),
  have hb'oa : b' ∉ (o-ₗa),
    intro hob'oa, rw two_pt_one_line (line_in_lines hob) (line_in_lines hoa) hob' at h₁,
    exact h₁.2.1 (pt_right_in_line o a), exact ⟨pt_left_in_line o b, hb'.1⟩,
    exact ⟨pt_left_in_line o a, hob'oa⟩,
  have : same_side_line (o-ₗx) b b',
    rw line_symm, refine t_shape_ray _ _ _ _ _,
    exact hox.symm,
    intro hf, rw two_pt_one_line (line_in_lines hob) (line_in_lines hox.symm) hob at h₁,
    exact h₁.2.2 (pt_left_in_line x o),
    exact ⟨pt_left_in_line o b, pt_right_in_line o b⟩,
    exact ⟨pt_right_in_line x o, hf⟩,
    cases (line_separation ⟨(o-ₗb), line_in_lines hob, pt_left_in_line o b, pt_right_in_line o b, hb'.1⟩ hob.symm hob'.symm).1 with hobb' hobb',
    left, exact hobb',
    have := (diff_side_pt_line hobb').2.2.2 (line_in_lines hoa) ⟨(pt_left_in_line o a), (same_side_line_not_in (line_in_lines hoa) h₂).2, hb'oa⟩,
    have hxoa : x ∉ (o-ₗa),
      intro hxoa, rw two_pt_one_line (line_in_lines hoa) (line_in_lines hox) hox ⟨pt_left_in_line o a, hxoa⟩ ⟨pt_left_in_line o x, pt_right_in_line o x⟩ at h₂,
      exact (same_side_line_not_in (line_in_lines hox) h₂).1 (pt_right_in_line o x),
    exfalso, apply (not_diff_side_line hxoa ((same_side_line_not_in (line_in_lines hoa) h₂).2)).2 h₂,
    apply diff_side_line_symm (line_in_lines hoa),
    apply diff_side_same_side_line (line_in_lines hoa) this,
    apply same_side_line_symm (line_in_lines hoa),
    refine t_shape_segment hoa hxoa _ _ _, exact hb'.2, exact hab'.symm,
    exact line_in_lines hoa, exact hob'.symm,
  apply same_side_line_symm (line_in_lines hox), apply same_side_line_trans (line_in_lines hox) this,
  cases hb'.2 with hab'x hf,
  simp at hab'x, rw is_between_same_side_pt at hab'x,
  apply same_side_line_symm (line_in_lines hox),
  apply (same_side_pt_line hab'x.2).2.2.2 (line_in_lines hox) _,
  split, exact pt_right_in_line o x,
  split,
  intro haox, rw two_pt_one_line (line_in_lines hoa) (line_in_lines hox) hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨pt_left_in_line o x, haox⟩ at h₂,
  exact (same_side_line_not_in (line_in_lines hox) h₂).1 (pt_right_in_line o x),
  exact (same_side_line_not_in (line_in_lines hox) this).2,
  cases hf with hf hf,
  exact absurd hf.symm hab',
  simp at hf, rw hf at this, exact absurd (pt_right_in_line o x) (same_side_line_not_in (line_in_lines hox) this).2,
end

lemma angle_tri {α β : angle} (ha'o'b' : angle_nontrivial α) (haob : angle_nontrivial β) :
(α <ₐ β) ∨ (α ≅ₐ β) ∨ (β <ₐ α) :=
begin
  rcases angle_three_pt β with ⟨a, b, hβ⟩,
  rw hβ, rw [hβ, nontrivial_iff_noncollinear] at haob, set o := β.vertex,
  have hao := (noncollinear_not_eq haob).1,
  have hbo := (noncollinear_not_eq haob).2.1.symm,
  rcases extend_congr_angle α o a b with ⟨x, hx, hlxb, -⟩,
  have hxo : x ≠ o,
    intro hxo, rw hxo at hlxb,
    exact (same_side_line_not_in (line_in_lines hao.symm) hlxb).1 (pt_left_in_line o a),
  by_cases h₂ : x ∈ (o-ₗb),
    right, left,
    have : (∠ x o a) = (∠ a o b),
      rw angle_symm,
      refine angle_eq_same_side _ _,
      cases (line_separation ⟨(o-ₗb), line_in_lines hbo.symm, pt_left_in_line o b, h₂, pt_right_in_line o b⟩ hxo hbo).1,
      exact h,
      rw ←not_diff_side_line at hlxb, exfalso, apply hlxb,
      apply (diff_side_pt_line h).2.2.2 (line_in_lines hao.symm),
      split, exact pt_left_in_line o a,
      have : b ∉ (o-ₗa),
        intro hf, exact haob ⟨(o-ₗa), line_in_lines hao.symm, pt_right_in_line o a, pt_left_in_line o a, hf⟩,
      split, intro hf,
      rcases h.2.1 with ⟨l, hl, hol, hxl, hbl⟩,
      rw two_pt_one_line hl (line_in_lines hao.symm) hxo ⟨hxl, hol⟩ ⟨hf, pt_left_in_line o a⟩ at hbl,
      exact this hbl, exact this,
      exact line_in_lines hao.symm,
      exact (same_side_line_not_in (line_in_lines hao.symm) hlxb).1,
      exact (same_side_line_not_in (line_in_lines hao.symm) hlxb).2,
    rw ←this, exact hx,
  have ha : a ∉ (o-ₗb),
    intro hf, exact haob ⟨(o-ₗb), line_in_lines hbo.symm, hf, pt_left_in_line o b, pt_right_in_line o b⟩,
  cases (plane_separation (line_in_lines hbo.symm) h₂ ha).1 with h₁ h₃,
  left, rw three_pt_angle_lt, use x, split,
  rw inside_three_pt_angle, exact ⟨same_side_line_symm (line_in_lines hao.symm) hlxb, same_side_line_symm (line_in_lines hbo.symm) h₁, haob⟩,
  rw angle_symm, exact angle_congr_symm hx,
  have hbin : inside_angle b (∠ x o a),
    rw inside_three_pt_angle, split, exact diff_same_side_line (diff_side_line_symm (line_in_lines hbo.symm) h₃) hlxb,
    split, exact hlxb,
    rintros ⟨l, hl, hxl, hol, hal⟩,
    rw two_pt_one_line (line_in_lines hao.symm) hl hao ⟨pt_right_in_line o a, pt_left_in_line o a⟩ ⟨hal, hol⟩ at hlxb,
    exact (same_side_line_not_in hl hlxb).1 hxl,
  right, right,
  rcases angle_three_pt α with ⟨a', b', hα⟩,
  rw hα, rw [hα, nontrivial_iff_noncollinear] at ha'o'b', set o' := α.vertex,
  have ha'o' := (noncollinear_not_eq ha'o'b').1,
  have hb'o' := (noncollinear_not_eq ha'o'b').2.1.symm,
  rcases extend_congr_angle β o' a' b' with ⟨y, hy, hlyb', -⟩,
  rw three_pt_angle_lt, use y,
  split, rw angle_symm at hbin,
  refine (congr_angle_sub hbin hlyb' ha'o'.symm _ _).1,
  rw ←hα, rw angle_symm at hx, exact angle_congr_symm hx,
  rw ←hβ, rw angle_symm at hy, exact hy,
  rw ←hβ, rw angle_symm at hy, exact angle_congr_symm hy
end

def is_right_angle (α : @angle C.to_incidence_order_geometry) : Prop :=
angle_nontrivial α ∧ ∀ β : angle, supplementary α β → (α ≅ₐ β)

lemma three_pt_angle_is_right_angle {a o b c : C.pts} (hboc : C.is_between b o c) :
is_right_angle (∠ a o b) ↔ ((∠ a o b) ≅ₐ (∠ a o c)) ∧ angle_nontrivial (∠ a o b) :=
begin
  unfold is_right_angle,
  split; intro h, split,
  apply h.2, rw three_pt_angle_supplementary,
  have haob := nontrivial_iff_noncollinear.1 h.1,
  split, exact hboc, split, exact haob,
  exact noncollinear132 (collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear12 (noncollinear13 haob)) (is_between_not_eq hboc).2.2),
  exact h.1,
  split, exact h.2,
  intros β hβ, rcases hβ.1 with ⟨o', a', b', c', haoba'ob', ha'oc', hb'oc'⟩,
  have haob := nontrivial_iff_noncollinear.1 h.2,
  have haoc := noncollinear132 (collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear12 (noncollinear13 haob)) (is_between_not_eq hboc).2.2),
  have hoo' := ((three_pt_angle_eq_iff haob).1 haoba'ob').1, rw ←hoo' at *,
  cases ((three_pt_angle_eq_iff haob).1 haoba'ob').2 with H H,
  rw ha'oc',
  have : (∠ a o c) = (∠ a' o c'),
    rw three_pt_angle_eq_iff haoc, simp, left,
    split, exact H.1,
    apply diff_side_pt_cancel (is_between_diff_side_pt.1 hboc),
    rw is_between_diff_side_pt at hb'oc',
    exact diff_side_pt_symm (diff_side_same_side_pt hb'oc' (same_side_pt_symm H.2)),
  rw ←this, exact h.1,
  rw ha'oc', apply angle_congr_trans h.1, rw angle_symm,
  refine vertical_angle_congr _ _ _,
  exact noncollinear13 haoc,
  rw is_between_diff_side_pt, rw is_between_diff_side_pt at hboc,
  exact diff_side_same_side_pt hboc H.2,
  rw is_between_diff_side_pt, rw is_between_diff_side_pt at hb'oc',
  exact diff_side_pt_symm (diff_side_same_side_pt hb'oc' (same_side_pt_symm H.1))
end

lemma right_angle_congr {α β : @angle C.to_incidence_order_geometry}
(hα : is_right_angle α) (hβ : is_right_angle β) : α = β :=
begin
  sorry
end

theorem isoceles {a b c : C.pts} (habc : noncollinear a b c) :
((a-ₛb) ≅ₛ (a-ₛc)) → ((∠ a b c) ≅ₐ (∠ a c b)) :=
begin
  intro habac,
  have hab := (noncollinear_not_eq habc).1,
  have hac := (noncollinear_not_eq habc).2.2.symm,
  cases is_between_extend hab with d habd,
  cases is_between_extend hac with x hacx,
  rcases extend_congr_segment c x (b-ₛd) with ⟨e, hcxe, hbdce, -⟩,
  have hace := is_between_same_side_pt_is_between hacx hcxe, clear hcxe hacx x,
  have had := (is_between_not_eq habd).2.1,
  have hae := (is_between_not_eq hace).2.1,
  have hadc := collinear_trans' (is_between_collinear habd) habc had,
  have haeb := collinear_trans' (is_between_collinear hace) (noncollinear23 habc) hae,
  have hadcaeb : ((Δ a d c) ≅ₜ (Δ a e b)),
    apply SAS; unfold three_pt_triangle; simp,
    exact hadc, exact haeb,
    exact congr_segment_add habd hace habac hbdce,
    exact segment_congr_symm habac,
    rw [angle_symm, ←angle_eq_same_side c (is_between_same_side_pt.1 habd).1],
    rw [angle_symm, @angle_symm C.to_incidence_order_geometry e _ _],
    rw angle_eq_same_side b (is_between_same_side_pt.1 hace).1, exact angle_congr_refl _,
  have hbd := (is_between_not_eq habd).2.2,
  have hce := (is_between_not_eq hace).2.2,
  have hdbc := collinear_trans' (collinear132 (is_between_collinear habd)) (noncollinear12 hadc) hbd.symm,
  have hecb := collinear_trans' (collinear132 (is_between_collinear hace)) (noncollinear12 haeb) hce.symm,
  have hdbcecb : ((Δ d b c) ≅ₜ (Δ e c b)),
    apply SAS; unfold three_pt_triangle; simp,
    exact hdbc, exact hecb,
    rw [segment_symm, @segment_symm C.to_incidence_order_geometry e _], exact hbdce,
    exact (tri_congr_side hadcaeb).2.2,
    rw [angle_symm, ←angle_eq_same_side c (is_between_same_side_pt.1 habd).2],
    rw [@angle_symm C.to_incidence_order_geometry _ e _, ←angle_eq_same_side b (is_between_same_side_pt.1 hace).2],
    rw [angle_symm, @angle_symm C.to_incidence_order_geometry b _ _],
    exact (tri_congr_angle hadcaeb).2.1,
  have key := (tri_congr_angle hdbcecb).2.1,
  rw [angle_symm, @angle_symm C.to_incidence_order_geometry e _ _] at key,
  rw [angle_symm, @angle_symm C.to_incidence_order_geometry a _ _],
  refine supplementary_congr _ _ key;
  rw three_pt_angle_supplementary,
  rw is_between_symm at habd,
  exact ⟨habd, noncollinear13 hdbc, noncollinear13 habc⟩,
    rw is_between_symm at hace,
  exact ⟨hace, noncollinear13 hecb, noncollinear123 habc⟩
end

lemma SSS {ABC DEF : @triangle C} (habc : noncollinear ABC.v1 ABC.v2 ABC.v3)
(ha'b'c' : noncollinear DEF.v1 DEF.v2 DEF.v3) (haba'b' : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2))
(haca'c' : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3)) (hbcb'c' : (ABC.v2-ₛABC.v3) ≅ₛ (DEF.v2-ₛDEF.v3)) :
ABC ≅ₜ DEF :=
begin
  set a := ABC.v1 with ha, set b := ABC.v2 with hb, set c := ABC.v3 with hc,
  set a' := DEF.v1, set b' := DEF.v2, set c' := DEF.v3,
  have hab := (noncollinear_not_eq habc).1,
  have hac := (noncollinear_not_eq habc).2.2.symm,
  have hbc := (noncollinear_not_eq habc).2.1,
  cases is_between_extend hab.symm with x hbax,
  rcases extend_congr_angle (∠ b' a' c') a c x with ⟨y, hy, hacyx, -⟩,
  rcases extend_congr_segment a y (a'-ₛb') with ⟨d, hayd, ha'b'ad, -⟩,
  have had := (same_side_pt_not_eq hayd).2.symm,
  have hacbd : diff_side_line (a-ₗc) b d,
    have h₁ : diff_side_line (a-ₗc) b x,
      refine (diff_side_pt_line (is_between_diff_side_pt.1 hbax)).2.2.2 _ _,
      exact line_in_lines hac,
      split, exact pt_left_in_line a c, split, exact noncollinear_in13 habc,
      apply noncollinear_in13,
      exact collinear_trans' (collinear12 (is_between_collinear hbax)) habc (is_between_not_eq hbax).2.2,
    have h₂ : same_side_line (a-ₗc) y d,
      rw line_symm, refine t_shape_ray hac.symm _ _ _ _,
      rw line_symm, exact (same_side_line_not_in (line_in_lines hac) hacyx).1,
      left, exact hayd, exact had.symm,
    exact diff_side_same_side_line (line_in_lines hac) (diff_side_same_side_line (line_in_lines hac) h₁ (same_side_line_symm (line_in_lines hac) hacyx)) h₂,
  have hadc : noncollinear a d c,
    intro hadc, exact hacbd.2.2 ((collinear_in13 hadc) hac),
  have hadca'b'c' : ((Δ a d c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triangle; simp,
    exact hadc, exact ha'b'c',
    exact segment_congr_symm ha'b'ad, exact haca'c',
    have : ∠ y a c = ∠ d a c,
      rw [angle_symm, @angle_symm C.to_incidence_order_geometry d _ _],
      exact angle_eq_same_side c hayd,
    rw this at hy, exact angle_congr_symm hy,
  clear hbax hacyx x hy hayd y,
  refine tri_congr_trans _ hadca'b'c',
  apply tri_congr12, rw [←ha, ←hb, ←hc],
  apply SAS; unfold three_pt_triangle; simp,
  exact noncollinear12 habc, exact noncollinear12 hadc,
  rw segment_symm at haba'b', rw @segment_symm C.to_incidence_order_geometry d a,
  exact segment_congr_trans haba'b' (segment_congr_symm (tri_congr_side hadca'b'c').1),
  exact segment_congr_trans hbcb'c' (segment_congr_symm (tri_congr_side hadca'b'c').2.2),
  have had := (noncollinear_not_eq hadc).1,
  have hcd := (noncollinear_not_eq hadc).2.1.symm,
  have h₁ : ((c-ₛb) ≅ₛ (c-ₛd)),
    rw segment_symm, apply segment_congr_trans hbcb'c',
    rw @segment_symm C.to_incidence_order_geometry c d, exact segment_congr_symm (tri_congr_side hadca'b'c').2.2,
  have h₂ : ((a-ₛb) ≅ₛ (a-ₛd)),
    apply segment_congr_trans haba'b', exact segment_congr_symm (tri_congr_side hadca'b'c').1,
  have hbd : b ≠ d,
    intro hbd, rw hbd at hacbd, rw ←not_same_side_line (line_in_lines hac) at hacbd,
    exact hacbd (same_side_line_refl (line_in_lines hac) (noncollinear_in13 hadc)),
    exact noncollinear_in13 hadc, exact noncollinear_in13 hadc,
  cases hacbd.1 with o ho,
  have hbod : C.is_between b o d,
    cases ho.2, exact h,
    cases h, rw h at ho, exact absurd ho.1 (noncollinear_in13 habc),
    simp at h, rw h at ho, exact absurd ho.1 (noncollinear_in13 hadc),
  by_cases hao : a = o,
    rw ←hao at ho, rw ←hao at hbod,
    have hbad : C.is_between b a d,
      cases ho.2, exact h, cases h, exact absurd h hab, exact absurd h had,
    rw is_between_same_side_pt at hbad,
    rw [angle_symm, angle_eq_same_side c hbad.1],
    rw [@angle_symm C.to_incidence_order_geometry a _ _, ←angle_eq_same_side c hbad.2],
    apply isoceles,
    intro hcbd, exact (noncollinear12 hadc) ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 hcbd)) hbd.symm),
    exact h₁,
  by_cases hco : c = o,
    rw ←hco at ho, rw ←hco at hbod,
    have hbad : C.is_between b c d,
      cases ho.2, exact h, cases h, exact absurd h hbc.symm, exact absurd h hcd,
    rw is_between_same_side_pt at hbad,
    rw [angle_eq_same_side a hbad.1, ←angle_eq_same_side a hbad.2],
    apply isoceles,
    intro habd, exact (noncollinear123 hadc) ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 habd)) hbd.symm),
    exact h₂,
  have hoac : collinear o a c, from ⟨(a-ₗc), line_in_lines hac, ho.1, pt_left_in_line a c, pt_right_in_line a c⟩,
  have hbo := (is_between_not_eq hbod).1,
  have hdo := (is_between_not_eq hbod).2.2.symm,
  have hobc : noncollinear o b c,
    from λhobc, habc (collinear123 (collinear_trans (collinear132 hoac) (collinear132 hobc) hco)),
  have hocd : noncollinear o c d,
    from λhocd, hobc (collinear_trans (collinear123 (is_between_collinear hbod)) (collinear23 hocd) hdo.symm),
  have hoab : noncollinear o a b,
    from λhoab, habc (collinear_trans (collinear12 hoab) (collinear12 hoac) hao),
  have hoad : noncollinear o a d,
    from λhoad, hoab (collinear_trans (collinear23 hoad) (collinear123 (is_between_collinear hbod)) hdo.symm),
  have H₁ : ((∠ o b c) ≅ₐ (∠ o d c)),
    rw [angle_symm, angle_eq_same_side c (is_between_same_side_pt.1 hbod).1],
    rw [@angle_symm C.to_incidence_order_geometry o d c ,←angle_eq_same_side c (is_between_same_side_pt.1 hbod).2],
    apply isoceles,
    intro hcbd, exact (noncollinear132 hocd) ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 hcbd)) hbd.symm),
    exact h₁,
  have H₂ : ((∠ o b a) ≅ₐ (∠ o d a)),
    rw [angle_symm, angle_eq_same_side a (is_between_same_side_pt.1 hbod).1],
    rw [@angle_symm C.to_incidence_order_geometry o d a ,←angle_eq_same_side a (is_between_same_side_pt.1 hbod).2],
    apply isoceles,
    intro habd, exact (noncollinear13 hoab) (collinear_trans (collinear123 habd) (collinear23 (is_between_collinear hbod)) hbd),
    exact h₂,
  rcases (collinear_between hoac).1 (ne.symm hao) (ne.symm hco) with h | h | h,
  have ha₁ : inside_angle a (∠ o b c),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hbo _ _ _ _,
    rw line_symm, exact noncollinear_in12 hobc,
    left, exact h, exact hao,
    split, refine t_shape_segment hbc _ _ _ _,
    exact noncollinear_in23 hobc, left, rw is_between_symm at h, exact h,
    exact hac, exact hobc,
  have ha₂ : same_side_line (d-ₗo) a c,
    apply same_side_line_symm (line_in_lines hdo), refine t_shape_segment hdo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hocd,
    left, exact h, exact hao,
  exact (congr_angle_sub ha₁ ha₂ hdo H₁ H₂).2,
  have hc₁ : inside_angle c (∠ o b a),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hbo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hoab,
    left, exact h, exact hco,
    split, refine t_shape_segment hab.symm _ _ _ _,
    rw line_symm, exact noncollinear_in23 hoab, left, rw is_between_symm at h, exact h,
    exact hac.symm, exact noncollinear23 hoab,
  have hc₂ : same_side_line (d-ₗo) c a,
    apply same_side_line_symm (line_in_lines hdo), refine t_shape_segment hdo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hoad,
    left, exact h, exact hco,
  rw [angle_symm, @angle_symm C.to_incidence_order_geometry a],
  exact (congr_angle_sub hc₁ hc₂ hdo H₂ H₁).2,
  have ho₁ : inside_angle o (∠ a b c),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hab.symm _ _ _ _,
    rw line_symm, exact noncollinear_in12 habc,
    left, exact h,
    exact ne.symm hao,
    split, refine t_shape_segment hbc _ _ _ _,
    exact noncollinear_in23 habc,
    left, rw is_between_symm at h, exact h,
    exact ne.symm hco, exact habc,
  have ho₂ : diff_side_line (d-ₗo) a c,
    use o, exact ⟨pt_right_in_line d o, by {left, exact h}⟩,
    split, rw line_symm, exact noncollinear_in13 hoad,
    rw line_symm, exact noncollinear_in13 hocd,
  refine (congr_angle_add ho₁ ho₂ hdo _ _).2,
  rw [angle_symm, @angle_symm C.to_incidence_order_geometry a _ _], exact H₂,
  exact H₁
end
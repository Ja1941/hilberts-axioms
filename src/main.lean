import algebra.support
import set_theory.zfc
import tactic.wlog
import tactic

open set
open_locale classical

universes u

/--An incidence geometry contains a type `pts` and a set `lines` that includes some sets of pts,
with the following axioms :
I1. Two distinct points uniquely define a line.
I2. Every line contains at least 2 distinct points.
I3. There exists 3 noncollinear points.
-/
class incidence_geometry :=
(pts : Type u) (lines : set (set pts))
(I1 : ∀ {a b : pts}, a ≠ b → ∃ l ∈ lines,
 a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l))
(I2 : ∀ l ∈ lines, ∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l)
(I3 : ∃ a b c : pts, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l))

section incidence_geometry_API

open incidence_geometry

variable [I : incidence_geometry]

include I

/--A line is a set of points defined given two points.
If two points are distinct, it is given by I1. Otherwise, it is defined as a singleton.
Note that (line a b).val ∈ lines iff the two points are distinct. -/
noncomputable def line (a b : pts) :
{ L : set pts // (a ≠ b → L ∈ lines) ∧ a ∈ L ∧ b ∈ L ∧ (a = b → L = {a}) } :=
begin
  by_cases hab : a = b, rw hab,
  exact ⟨{b}, λ hf, absurd rfl hf, by simp⟩,
  choose l hl ha hb h using (I1 hab),
  exact ⟨l, λ h, hl, ha, hb, λh, absurd h hab⟩
end

notation a`-ₗ`b := (line a b : set pts)

/--Two sets of points intersect if their intersection is nonempty. -/
def intersect [I : incidence_geometry] (m n : set pts) : Prop := (m ∩ n).nonempty

notation m`♥`n := intersect m n

lemma line_in_lines {a b : pts} (hab : a ≠ b) :
(a-ₗb) ∈ lines := (line a b).2.1 hab

lemma pt_left_in_line (a b : pts) :
a ∈ (a-ₗb) := (line a b).2.2.1

lemma pt_right_in_line (a b : pts) :
b ∈ (a-ₗb) := (line a b).2.2.2.1

lemma one_pt_line (a : pts) : ∃ l ∈ lines, a ∈ l :=
begin
  have : ∃ b : pts, a ≠ b,
    by_contra hf, push_neg at hf,
    rcases I3 with ⟨x, y, z, h, -⟩, exact h ((hf x).symm.trans (hf y)),
  cases this with b hab,
  exact ⟨line a b, line_in_lines hab, pt_left_in_line a b⟩
end

lemma line_unique {a b : pts} (hab : a ≠ b)
{l : set pts} (hl : l ∈ lines) (ha : a ∈ l) (hb : b ∈ l) : l = (a-ₗb) :=
begin
  rcases (I1 hab) with ⟨n, hn, -, -, key⟩,
  rw [key l hl ha hb,
      key (a-ₗb) (line_in_lines hab) (pt_left_in_line a b) (pt_right_in_line a b)]
end

lemma two_pt_on_one_line {l : set pts} (hl : l ∈ lines) :
∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l := I2 l hl

lemma two_pt_one_line {l m : set pts} (hl : l ∈ lines) (hm : m ∈ lines)
{a b : pts} (hab : a ≠ b) : a ∈ l ∧ b ∈ l → a ∈ m ∧ b ∈ m → l = m :=
λ habl habm, (line_unique hab hl habl.1 habl.2).trans (line_unique hab hm habm.1 habm.2).symm

lemma line_symm (a b : pts) : (a-ₗb) = (b-ₗa) :=
begin
  by_cases a = b, rw h,
  exact two_pt_one_line (line_in_lines h) (line_in_lines (ne.symm h))
    h ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨pt_right_in_line b a, pt_left_in_line b a⟩
end

lemma two_line_one_pt {l₁ l₂ : set pts} (hl₁ : l₁ ∈ lines) (hl₂ : l₂ ∈ lines) :
∀ {a b : pts}, l₁ ≠ l₂ → a ∈ l₁ → a ∈ l₂ → b ∈ l₁ → b ∈ l₂ → a = b :=
begin
  intros a b hll ha₁ ha₂ hb₁ hb₂,
  by_cases hab : a = b, exact hab,
  rcases (I1 hab) with ⟨l, hl, -, -, key⟩,
  exact absurd ((key l₁ hl₁ ha₁ hb₁).trans (key l₂ hl₂ ha₂ hb₂).symm) hll
end

/--Three points are collinear if there are on the same line. -/
def collinear (a b c : pts) : Prop :=
∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

/--Opposite to collinear -/
def noncollinear (a b c : pts) : Prop := ¬collinear a b c

lemma noncollinear_exist {a b : pts} (hab : a ≠ b) : ∃ c : pts, noncollinear a b c :=
begin
  by_contra hf, unfold noncollinear collinear at hf, push_neg at hf,
  rcases I3 with ⟨x, y, z, hxy, hxz, hyz, hxyz⟩,
  rcases hf x with ⟨l, hl, hal, hbl, hxl⟩,
  rcases hf y with ⟨m, hm, ham, hbm, hym⟩,
  rcases hf z with ⟨n, hn, han, hbn, hzn⟩,
  rw ←two_pt_one_line hl hm hab ⟨hal, hbl⟩ ⟨ham, hbm⟩ at hym,
  rw ←two_pt_one_line hl hn hab ⟨hal, hbl⟩ ⟨han, hbn⟩ at hzn,
  exact hxyz ⟨l, hl, hxl, hym, hzn⟩
end

lemma noncollinear_not_eq {a b c : pts} (hf : noncollinear a b c) : a ≠ b ∧ b ≠ c ∧ c ≠ a :=
begin
  have : ∀ a b : pts, ∃ l ∈ lines, a ∈ l ∧ b ∈ l,
    intros a b,
    by_cases a = b,
      rw ←h, simp,
      have : ∃ p : pts, a ≠ p,
        by_contra,
        push_neg at h,
        rcases I3 with ⟨x, y, -, hxy, -, -, -⟩,
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

lemma collinear12 {a b c : pts} : collinear a b c → collinear b a c :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncollinear12 {a b c : pts} : noncollinear a b c → noncollinear b a c :=
by {unfold noncollinear, contrapose!, exact collinear12}

lemma collinear13 {a b c : pts} : collinear a b c → collinear c b a :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncollinear13 {a b c : pts} : noncollinear a b c → noncollinear c b a :=
by {unfold noncollinear, contrapose!, exact collinear13}

lemma collinear23 {a b c : pts} : collinear a b c → collinear a c b :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncollinear23 {a b c : pts} : noncollinear a b c → noncollinear a c b :=
by {unfold noncollinear, contrapose!, exact collinear23}

lemma collinear123 {a b c : pts} : collinear a b c → collinear b c a :=
λh, collinear23 (collinear12 h)

lemma collinear132 {a b c : pts} : collinear a b c → collinear c a b :=
λh, collinear23 (collinear13 h)

lemma noncollinear123 {a b c : pts} : noncollinear a b c → noncollinear b c a :=
by {unfold noncollinear, contrapose!, exact collinear132}

lemma noncollinear132 {a b c : pts} : noncollinear a b c → noncollinear c a b :=
by {unfold noncollinear, contrapose!, exact collinear123}

lemma collinear_trans {a b c d : pts} (habc : collinear a b c) (habd : collinear a b d) :
a ≠ b → collinear a c d :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩, rcases habd with ⟨m, hm, ham, hbm, hdm⟩,
  intro hab, rw two_pt_one_line hm hl hab ⟨ham, hbm⟩ ⟨hal, hbl⟩ at hdm,
  exact ⟨l, hl, hal, hcl, hdm⟩
end

lemma collinear_trans' {a b c d : pts} (habc : collinear a b c) (habd : noncollinear a b d) :
a ≠ c → noncollinear a c d :=
λhac hacd, habd (collinear_trans (collinear23 habc) hacd hac)

lemma collinear_in12 {a b c : pts} : collinear a b c → a ≠ b → c ∈ (a-ₗb) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hab,
  rw two_pt_one_line hl (line_in_lines hab) hab
    ⟨hal, hbl⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at hcl,
  exact hcl
end

lemma collinear_in13 {a b c : pts} : collinear a b c → a ≠ c → b ∈ (a-ₗc) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hac,
  rw two_pt_one_line hl (line_in_lines hac) hac
    ⟨hal, hcl⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at hbl,
  exact hbl
end

lemma collinear_in23 {a b c : pts} : collinear a b c → b ≠ c → a ∈ (b-ₗc) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hbc,
  rw two_pt_one_line hl (line_in_lines hbc) hbc
    ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩ at hal,
  exact hal
end

lemma noncollinear_in12 {a b c : pts} : noncollinear a b c → c ∉ (a-ₗb) :=
λ habc hc, habc ⟨(a-ₗb), line_in_lines (noncollinear_not_eq habc).1,
  pt_left_in_line a b, pt_right_in_line a b, hc⟩

lemma noncollinear_in13 {a b c : pts} : noncollinear a b c → b ∉ (a-ₗc) :=
λ habc hb, habc ⟨(a-ₗc), line_in_lines (noncollinear_not_eq habc).2.2.symm,
  pt_left_in_line a c, hb, pt_right_in_line a c⟩

lemma noncollinear_in23 {a b c : pts} : noncollinear a b c → a ∉ (b-ₗc) :=
λ habc ha, habc ⟨(b-ₗc), line_in_lines (noncollinear_not_eq habc).2.1, ha,
  pt_left_in_line b c, pt_right_in_line b c⟩

end incidence_geometry_API

-- IF (WHEN) YOU MAKE ABOVE INTO ONE FILE, DON'T NEED SECTION

-- NEW FILE STARTS HERE!

/--An incidence order geometry is an incidence geometry with betweenness, a ternary relation
for `pts`. `is_between a b c` means `b` is between `a` and `c`, restricted by some axioms :
B1 : If a point is between the other two, they are collinear.
B2 : We can extend two distinct points.
B3 : Given 3 distinct points, exactly one of them is between the other two.
B4 : Pasch's axiom. `a`, `b`, `c` are noncollinear and for a line `l` not containing any of them,
     if `l` contains a points between `a` and `b`, it contains a points either between `a` and `c`
     r between `b` and `c`.
-/

class incidence_order_geometry extends incidence_geometry :=
(is_between : pts → pts → pts → Prop)
(B1 : ∀ {a b c : pts}, is_between a b c → is_between c b a
                        ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ collinear a b c)
(B2 : ∀ {a b : pts}, a ≠ b → ∃ c : pts, is_between a b c)
(B3 : ∀ {a b c : pts} (l ∈ lines), a ∈ l ∧ b ∈ l ∧ c ∈ l →
(a ≠ b → a ≠ c → b ≠ c → is_between a b c ∨ is_between a c b ∨ is_between b a c)
∧ ¬(is_between a b c ∧ is_between a c b)
∧ ¬(is_between a b c ∧ is_between b a c)
∧ ¬(is_between a c b ∧ is_between b a c))
(B4 : ∀ {a b c : pts} (l ∈ lines),
      (noncollinear a b c) → a ∉ l → b ∉ l → c ∉ l
      → (∃ d : pts, is_between a d b ∧ d ∈ l) →
      (∃ p : pts, p ∈ l ∧ (is_between a p c ∨ is_between b p c))
      ∧ ∀ p q : pts, p ∈ l → q ∈ l → ¬(is_between a p c ∧ is_between b q c))

section incidence_order_geometry_API

variable [B : incidence_order_geometry]

open incidence_geometry incidence_order_geometry

include B

notation a`-ₗ`b := (line a b : set pts)

lemma is_between_symm (a b c : pts) :
is_between a b c ↔ is_between c b a := iff.intro (λ h, (B1 h).1) (λ h, (B1 h).1)

lemma is_between_not_eq {a b c : pts} (h : is_between a b c) :
(a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) := ⟨(B1 h).2.1, (B1 h).2.2.1, (B1 h).2.2.2.1⟩

lemma is_between_collinear {a b c : pts}
(h : is_between a b c) : collinear a b c := (B1 h).2.2.2.2

lemma is_between_extend {a b : pts} (h : a ≠ b) :
∃ c : pts, is_between a b c := B2 h

lemma collinear_between {a b c : pts} (habc : collinear a b c) :
(a ≠ b → a ≠ c → b ≠ c → is_between a b c ∨ is_between a c b ∨ is_between b a c)
∧ ¬(is_between a b c ∧ is_between a c b)
∧ ¬(is_between a b c ∧ is_between b a c)
∧ ¬(is_between a c b ∧ is_between b a c) :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩,
  exact B3 l hl ⟨hal, hbl, hcl⟩
end

/--A type whose inside is a set containing two points and points between them. -/
structure segment := (inside : set pts)
(in_eq : ∃ a b : pts, inside = {x : pts | is_between a x b} ∪ {a, b})

/--A segment is nontrivial if its inside is not a singleton.
Equivalently, `a` and `b` are distinct. -/
def segment_nontrivial (s : segment) : Prop :=
∀ x : pts, s.inside ≠ {x}

/--Explicitly stating `a` and `b` defines a segment. -/
def two_pt_segment (a b : pts) : segment := ⟨{x : pts | is_between a x b} ∪ {a, b}, ⟨a, b, rfl⟩⟩

notation a`-ₛ`b := two_pt_segment a b

lemma pt_left_in_segment (a b : B.pts) : a ∈ (a-ₛb).inside :=
by { unfold two_pt_segment, simp }

lemma pt_right_in_segment (a b : B.pts) : b ∈ (a-ₛb).inside :=
by { unfold two_pt_segment, simp }

lemma segment_symm (a b : pts) : (a-ₛb) = (b-ₛa) :=
by {unfold two_pt_segment, simp, ext, simp, rw is_between_symm, tauto}

lemma segment_singleton (a : pts) : (a-ₛa).inside = {a} :=
begin
  unfold two_pt_segment, ext1, simp,
  intro haxa, exact absurd rfl (is_between_not_eq haxa).2.1
end

lemma segment_nontrivial_iff_neq {a b : pts} :
segment_nontrivial (a-ₛb) ↔ a ≠ b :=
begin
  split; intro h,
  by_contra hab, push_neg at hab,
  rw hab at h, exact h b (segment_singleton b),
  intros x hf,
  have := pt_left_in_segment a b, rw hf at this,
  simp at this, rw this at h,
  have := pt_right_in_segment a b, rw hf at this,
  simp at this, rw this at h,
  exact h rfl
end 

lemma segment_in_line (a b : pts) : (a-ₛb).inside ⊆ (a-ₗb) :=
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

lemma segment_two_pt (s : segment) : ∃ a b : pts, s = (a-ₛb) :=
begin
  induction s with inside in_eq,
  rcases in_eq with ⟨a, b, h⟩, use [a, b],
  unfold two_pt_segment, simp only, exact h
end

lemma pasch {a b c : pts} (habc : noncollinear a b c) {l : set pts} (hl : l ∈ lines) :
a ∉ l → b ∉ l → c ∉ l → (l ♥ (a-ₛb).inside) →
((l ♥ (a-ₛc).inside) ∨ (l ♥ (b-ₛc).inside)) ∧ ¬((l ♥ (a-ₛc).inside) ∧ (l ♥ (b-ₛc).inside)) :=
begin
  intros ha hb hc hlab,
  have hd : ∃ d : pts, is_between a d b ∧ d ∈ l,
    unfold two_pt_segment at hlab, unfold intersect set.nonempty at hlab, simp at hlab,
    rcases hlab with ⟨d, hdl, da | db | hadb⟩,
    rw da at hdl, exact absurd hdl ha,
    rw db at hdl, exact absurd hdl hb,
    exact ⟨d, hadb, hdl⟩,
  split,
  rcases (B4 l hl habc ha hb hc hd).1 with ⟨p, hpl, h⟩,
  unfold two_pt_segment, unfold intersect set.nonempty, simp,
  cases h with h h,
  left, exact ⟨p, hpl, by {right, right, exact h}⟩,
  right, exact ⟨p, hpl, by {right, right, exact h}⟩,
  unfold intersect set.nonempty,
  have := (B4 l hl habc ha hb hc hd).2,
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

lemma two_pt_between {a b : pts} (hab : a ≠ b) : ∃ c : pts, is_between a c b :=
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

/--Two points `a` `b` are on the same side of a line if segment `a` `b`
doesn't intersects with the line.
-/
def same_side_line (l : set pts) (a b : pts) : Prop := ¬(l ♥ (a-ₛb).inside)

/--Segment `a` `b` intersects with the line and not at `a` or `b`. -/
def diff_side_line (l : set pts) (a b : pts) : Prop :=
(l ♥ (a-ₛb).inside) ∧ a ∉ l ∧ b ∉ l

lemma plane_separation
{l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
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
{l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
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

lemma not_same_side_line {l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
¬(same_side_line l a b) ↔ (diff_side_line l a b) :=
begin
  split, intro hns,
  cases (same_or_diff_line_strict ha hb).1 with hs hd,
  exact absurd hs hns, exact hd,
  intros hd hs,
  exact absurd (by exact ⟨hs, hd⟩) (same_or_diff_line_strict ha hb).2
end

lemma not_diff_side_line {l : set pts} {a b : pts} (ha : a ∉ l) (hb : b ∉ l) :
¬(diff_side_line l a b) ↔ (same_side_line l a b)
:= by rw [←not_iff_not.mpr (not_same_side_line ha hb), not_not]

lemma same_side_line_refl {l : set pts} {a : pts} (ha : a ∉ l) :
same_side_line l a a :=
begin
  unfold same_side_line intersect, 
  rw segment_singleton, rw not_nonempty_iff_eq_empty, ext1, simp,
  intros h hxa, rw hxa at h, exact ha h
end

lemma same_side_line_symm {l : set pts} {a b : pts} :
same_side_line l a b → same_side_line l b a :=
by {unfold same_side_line, rw segment_symm, simp}

lemma diff_side_line_symm {l : set pts} {a b : pts} :
diff_side_line l a b → diff_side_line l b a :=
by {unfold diff_side_line, rw segment_symm, tauto}

lemma same_side_line_not_in {x y : pts} {l : set pts} :
same_side_line l x y → x ∉ l ∧ y ∉ l :=
begin
  intro hlxy, unfold same_side_line intersect at hlxy, rw not_nonempty_iff_eq_empty at hlxy, split,
  intro hxl, have : x ∈ l ∩ (x-ₛy).inside, simp, exact ⟨hxl, by {unfold two_pt_segment, simp}⟩,
  rw hlxy at this, exact this,
  intro hyl, have : y ∈ l ∩ (x-ₛy).inside, simp, exact ⟨hyl, by {unfold two_pt_segment, simp}⟩,
  rw hlxy at this, exact this
end

private lemma same_side_line_trans_noncollinear {l : set pts} (hl : l ∈ lines) {a b c : pts} :
noncollinear a b c → same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  unfold same_side_line, intros h hlab hlbc,
  rw segment_symm at hlbc,
  intro hlac,
  replace h : noncollinear a c b,
    unfold noncollinear collinear, unfold noncollinear collinear at h,
    intro hf, apply h, rcases hf with ⟨l, hl, hal, hcl, hbl⟩,
    exact ⟨l, hl, hal, hbl, hcl⟩, 
  cases (pasch h hl (same_side_line_not_in hlab).1 (same_side_line_not_in hlbc).1 (same_side_line_not_in hlab).2 hlac).1 with hf hf,
  exact hlab hf, exact hlbc hf
end

lemma same_side_line_trans {l : set pts} (hl : l ∈ lines) {a b c : pts} :
same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  by_cases collinear a b c; intros hlab hlbc,
  by_cases hab : a = b, rw ←hab at hlbc, exact hlbc,
  by_cases hbc : b = c, rw hbc at hlab, exact hlab,
  by_cases hac : a = c, rw hac, exact same_side_line_refl (same_side_line_not_in hlbc).2,
  rcases h with ⟨m, hm, ham, hbm, hcm⟩,
  have hd : ∃ d : pts, d ∈ l ∧ d ∉ m,
    rcases two_pt_on_one_line hl with ⟨x, y, hxy, hxl, hyl⟩,
    have hlm : l ≠ m, intro hlm, rw ←hlm at ham, exact (same_side_line_not_in hlab).1 ham,
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
      intro hf, have := (same_side_line_not_in hlab).1, rw hf at this, exact this (pt_left_in_line a e),
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
  have hlbe := same_side_line_trans_noncollinear hl hbae (same_side_line_symm hlab) hlae,
  have hlec := same_side_line_trans_noncollinear hl hebc (same_side_line_symm hlbe) hlbc,
  exact same_side_line_trans_noncollinear hl haec hlae hlec,
  exact same_side_line_trans_noncollinear hl h hlab hlbc
end

/--Two points `a` `b` are on the same side of the point `o` if
they are collinear and `o` is not in segment `a` `b`.
-/
def same_side_pt (o a b : pts) : Prop :=
o ∉ (a-ₛb).inside ∧ collinear o a b

/--`o` is in segment `a` `b` but is not `a` and `b`. -/
def diff_side_pt (o a b : pts) : Prop :=
o ∈ (a-ₛb).inside ∧ a ≠ o ∧ b ≠ o

lemma same_side_pt_not_eq {o a b : pts} (hoab : same_side_pt o a b) : a ≠ o ∧ b ≠ o :=
begin
  unfold same_side_pt at hoab, unfold two_pt_segment at hoab,
  split,
  intro hao, rw hao at hoab,
  simp at hoab, exact hoab,
  intro hbo, rw hbo at hoab,
  simp at hoab, exact hoab
end

lemma diff_side_pt_collinear {o a b : pts} : diff_side_pt o a b → collinear o a b :=
begin
  intro hoab,
  by_cases a = b,
    rw h, exact ⟨(b-ₗo), line_in_lines hoab.2.2,
      pt_right_in_line b o, pt_left_in_line b o, pt_left_in_line b o⟩,
  exact ⟨(a-ₗb), line_in_lines h,
    (segment_in_line a b) hoab.1, pt_left_in_line a b, pt_right_in_line a b⟩
end

theorem line_separation
{p a b : pts} (hpab : collinear p a b) (hap : a ≠ p) (hbp : b ≠ p) : 
(same_side_pt p a b ∨ diff_side_pt p a b) ∧
¬(same_side_pt p a b ∧ diff_side_pt p a b) :=
begin
  unfold same_side_pt diff_side_pt,
  split, by_cases hp : p ∈ (a-ₛb).inside,
  right, exact ⟨hp, hap, hbp⟩,
  left, exact ⟨hp, hpab⟩,
  push_neg,
  intros h₁ h₂, exact absurd h₂ h₁.1
end

lemma not_same_side_pt
{p a b : pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p) :
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
{p a b : pts} (hpab : collinear p a b) (ha : a ≠ p) (hb : b ≠ p) :
(¬diff_side_pt p a b ↔ same_side_pt p a b) :=
by rw [←not_iff_not.mpr (not_same_side_pt hpab ha hb), not_not]

lemma same_side_pt_refl {a b : pts} (hab : a ≠ b) : same_side_pt a b b :=
begin
  split, rw segment_singleton, exact hab,
  exact ⟨a-ₗb, line_in_lines hab, pt_left_in_line a b, pt_right_in_line a b, pt_right_in_line a b⟩
end

lemma same_side_pt_symm {a b c : pts} :
same_side_pt a b c → same_side_pt a c b :=
begin
  unfold same_side_pt,
  intro habc, split,
  rw segment_symm, exact habc.1,
  rcases habc.2 with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨l, hl, hal, hcl, hbl⟩
end

lemma diff_side_pt_symm {a b c : pts} :
diff_side_pt a b c → diff_side_pt a c b :=
begin
  unfold diff_side_pt, rw segment_symm, tauto
end

lemma same_side_pt_line {a b c : pts} : same_side_pt a b c
→ collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∀ {l : set pts}, l ∈ lines → a ∈ l ∧ b ∉ l ∧ c ∉ l → same_side_line l b c :=
begin
  intro habc, split, exact habc.2,
  have hab := (same_side_pt_not_eq habc).1.symm,
  have hac := (same_side_pt_not_eq habc).2.symm,
  split, exact hab,
  split, exact hac,
  intros l hl habcl,
  by_cases hbc : b = c, rw ←hbc,
  exact same_side_line_refl habcl.2.1,
  rintros ⟨x, hxl, hxbc⟩,
  have hlab : l ≠ (a-ₗb),
    intro hf, rw hf at habcl, exact habcl.2.1 (pt_right_in_line a b),
  have hxab : x ∈ (a-ₗb),
    rcases habc.2 with ⟨l, hl, hal, hbl, hcl⟩,
    rw (two_pt_one_line (line_in_lines hab) hl hab
      ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨hal, hbl⟩),
    rw (two_pt_one_line hl (line_in_lines hbc) hbc
      ⟨hbl, hcl⟩ ⟨pt_left_in_line b c, pt_right_in_line b c⟩),
    exact (segment_in_line b c) hxbc,
  rw ←(two_line_one_pt hl (line_in_lines hab) hlab habcl.1 (pt_left_in_line a b) hxl hxab) at hxbc,
  unfold two_pt_segment at hxbc, simp at hxbc,
  unfold same_side_pt at habc, unfold two_pt_segment at habc, simp at habc,
  exact habc.1 hxbc,
end

lemma diff_side_pt_line {a b c : pts} : diff_side_pt a b c
→ collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∀ {l : set pts}, l ∈ lines → a ∈ l ∧ b ∉ l ∧ c ∉ l → diff_side_line l b c :=
begin
  intro h, split, exact (diff_side_pt_collinear h),
  split, exact h.2.1.symm, split, exact h.2.2.symm,
  intros l hl habcl, use a,
  exact ⟨habcl.1, h.1⟩, exact ⟨habcl.2.1, habcl.2.2⟩,
end

lemma is_between_diff_side_pt {a b c : pts} :
is_between a b c ↔ diff_side_pt b a c :=
begin
  unfold diff_side_pt, unfold two_pt_segment,
  split, intro habc,
  simp, split, right, right, exact habc,
  rcases is_between_collinear habc with ⟨l, hl, hal, hbl, hcl⟩,
  exact ⟨(is_between_not_eq habc).1, (is_between_not_eq habc).2.2.symm⟩,
  simp, intros h hab hcb,
  rcases h with h | h | h,
  exact absurd h.symm hab,
  exact absurd h.symm hcb,
  exact h
end

lemma is_between_same_side_pt {a b c : pts} :
is_between a b c ↔ same_side_pt a b c ∧ same_side_pt c a b :=
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
  rcases (collinear_between habc).1 h₁.1 h₁.2.1 h₂.2.1.symm with h | h | h,
  exact h, exact absurd h h₂.2.2, exact absurd h h₁.2.2
end

lemma same_side_line_pt {a b c : pts}: (collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∃ {l : set pts}, l ∈ lines ∧ a ∈ l ∧ b ∉ l ∧ c ∉ l ∧ same_side_line l b c)
→ same_side_pt a b c :=
begin
  rintros ⟨habc, hab, hac, l, hl, hal, hbl, hcl, hlbc⟩,
  rw ←(not_diff_side_pt habc hab.symm hac.symm), intro hf,
  have := (diff_side_pt_line hf).2.2.2 hl ⟨hal, hbl, hcl⟩,
  exact (plane_separation hbl hcl).2 ⟨hlbc, this⟩
end

lemma diff_side_line_pt {a b c : pts}: (collinear a b c ∧ a ≠ b ∧ a ≠ c
∧ ∃ {l : set pts}, l ∈ lines ∧ a ∈ l ∧ b ∉ l ∧ c ∉ l ∧ diff_side_line l b c)
→ diff_side_pt a b c :=
begin
  rintros ⟨habc, hab, hac, l, hl, hal, hbl, hcl, hlbc⟩,
  rw ←(not_same_side_pt habc hab.symm hac.symm), intro hf,
  have := (same_side_pt_line hf).2.2.2 hl ⟨hal, hbl, hcl⟩,
  exact (plane_separation hbl hcl).2 ⟨this, hlbc⟩
end

private lemma line_pt_exist {a b c : pts} (habc : collinear a b c) (hab : a ≠ b) (hac : a ≠ c) : 
∃ l ∈ to_incidence_geometry.lines, a ∈ l ∧ b ∉ l ∧ c ∉ l :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩,
  have hd : ∃ d : pts, noncollinear a b d ∧ d ∉ l,
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

lemma same_side_pt_trans {a b c d : pts} :
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

lemma is_between_trans {a b c d : pts} :
is_between a b c → is_between b c d → is_between a b d ∧ is_between a c d :=
begin
  have : ∀ {a b c d : pts}, is_between a b c → is_between b c d → is_between a b d ,
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

lemma is_between_trans' {a b c d : pts} :
is_between a b d → is_between b c d → is_between a b c ∧ is_between a c d :=
begin
  have : ∀ {a b c d : pts}, is_between a b d → is_between b c d → is_between a b c ,
    intros a b c d habd hbcd,
    rcases is_between_collinear habd with ⟨l, hl, hal, hbl, hdl⟩,
    rcases is_between_collinear hbcd with ⟨m, hm, hbm, hcm ,hdm⟩,
    rw two_pt_one_line hm hl (is_between_not_eq habd).2.2 ⟨hbm, hdm⟩ ⟨hbl, hdl⟩ at hcm,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hbl, hal, hcm⟩ (is_between_not_eq habd).1 (is_between_not_eq hbcd).1.symm],
    intro hbac, have hbad := same_side_pt_trans hbac (is_between_same_side_pt.mp hbcd).1,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hbl, hal, hdl⟩] at habd,
    exact habd hbad, exact habd.2.1, exact habd.2.2,
  intros habd hbcd,
  have habc := this habd hbcd,
  exact ⟨habc, (is_between_trans habc hbcd).2⟩
end

lemma same_side_pt_between {a b c : pts} :
same_side_pt a b c → b ≠ c → is_between a b c ∨ is_between a c b :=
begin
  intros habc hbc,
  rcases (collinear_between habc.2).1 (same_side_pt_not_eq habc).1.symm (same_side_pt_not_eq habc).2.symm hbc with h | h | h,
  left, exact h, right, exact h,
  rw [is_between_diff_side_pt, ←not_same_side_pt habc.2] at h, exact absurd habc h,
  exact (same_side_pt_not_eq habc).1,
  exact (same_side_pt_not_eq habc).2
end

lemma is_between_same_side_pt_is_between {a b c d : pts} :
is_between a b c → same_side_pt b c d → is_between a b d :=
begin
  intros habc hbcd,
  by_cases hcd : c = d,
    rw hcd at habc, exact habc,
  cases same_side_pt_between hbcd hcd,
  exact (is_between_trans habc h).1,
    exact (is_between_trans' habc h).1
end

lemma diff_side_line_cancel {l : set pts} (hl : l ∈ lines) {a b c : pts} :
diff_side_line l a b → diff_side_line l b c → same_side_line l a c :=
begin
  intros h₁ h₂,
  have hab : a ≠ b,
    intro hf, rw ←hf at h₁, unfold diff_side_line intersect at h₁, rw segment_singleton at h₁,
    cases h₁.1 with a' ha', simp at ha', rw ←ha'.2 at h₁, exact h₁.2.1 ha'.1,
  by_cases hac : a = c,
    rw ←hac, exact same_side_line_refl h₁.2.1,
  have hbc : b ≠ c,
    intro hf, rw ←hf at h₂, unfold diff_side_line intersect at h₂, rw segment_singleton at h₂,
    cases h₂.1 with b' hb', simp at hb', rw ←hb'.2 at h₂, exact h₂.2.1 hb'.1,
  by_cases habc : collinear a b c,
    cases h₁.1 with x hx,
    have : diff_side_pt x a b,
      unfold diff_side_pt, split, exact hx.2,
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
    rcases (collinear_between ⟨m, hm, ham, hbm, hcm⟩).1 hab hac hbc with habc | hacb | hbac,
    exact (collinear_between (is_between_collinear this)).2.1 ⟨this, (is_between_trans' habc hz).1⟩,
    exact (collinear_between (is_between_collinear hy)).2.1 ⟨hy, (is_between_trans' hacb (by {rw is_between_symm, exact hz})).1⟩,
    exact (collinear_between (is_between_collinear this)).2.2.1 ⟨this, by {rw is_between_symm, exact (is_between_trans' hbac hy).1}⟩,
    exact h₁.2.1, exact h₂.2.2,
  by_contra h₃,
  rw not_same_side_line h₁.2.1 h₂.2.2 at h₃,
  unfold diff_side_line at h₁ h₂ h₃,
  exact (pasch habc hl h₁.2.1 h₁.2.2 h₂.2.2 h₁.1).2 ⟨h₃.1, h₂.1⟩
end

lemma diff_side_pt_cancel {a b c d : pts} :
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
  exact ⟨l, hl, hal, hcl, hdl, diff_side_line_cancel hl (diff_side_line_symm h₁) h₂⟩
end

lemma diff_side_same_side_line {l : set pts} (hl : l ∈ lines) {a b c : pts} :
diff_side_line l a b → same_side_line l b c → diff_side_line l a c :=
begin
  intros hlab hlbc,
  rw ←(not_same_side_line hlab.2.1 (same_side_line_not_in hlbc).2),
  rw ←not_same_side_line at hlab, intro hlac,
  exact hlab (same_side_line_trans hl hlac (same_side_line_symm hlbc)),
  exact hlab.2.1, exact hlab.2.2
end

lemma diff_side_same_side_pt {a b c d : pts} :
diff_side_pt a b c → same_side_pt a b d → diff_side_pt a c d :=
begin
  intros habc habd,
  rw ←not_same_side_pt, rw ←not_same_side_pt at habc,
  intro hacd, exact habc (same_side_pt_trans habd (same_side_pt_symm hacd)),
  exact (diff_side_pt_collinear habc), exact habc.2.1, exact habc.2.2,
  exact collinear_trans (diff_side_pt_collinear habc) habd.2 habc.2.1.symm,
  exact habc.2.2, exact (same_side_pt_not_eq habd).2
end

private lemma two_pt_segment_pt_prep {a b a' b' : pts} :
(a-ₛb) = (a'-ₛb') → a = a' → b = b' :=
begin
  intros haba'b' haa',
  replace haba'b' : (a-ₛb).inside = (a-ₛb').inside, rw [haba'b', ←haa'],
  by_contra hbb',
  by_cases hab : a = b, rw hab at haba'b',
    rw segment_singleton at haba'b',
    cases (two_pt_between hbb') with x hbxb',
    have hx : x ∈ (b-ₛb').inside,
      unfold two_pt_segment, simp, right, right, exact hbxb',
    rw ←haba'b' at hx, simp at hx, exact (is_between_not_eq hbxb').1 hx.symm,
  by_cases hab' : a = b', rw hab' at haba'b',
    rw segment_singleton at haba'b',
    cases (two_pt_between hbb') with x hbxb',
    have hx : x ∈ (b-ₛb').inside,
      unfold two_pt_segment, simp, right, right, exact hbxb',
    rw [segment_symm, haba'b'] at hx, simp at hx, exact (is_between_not_eq hbxb').2.2 hx,
  by_cases habb' : collinear a b b',
    rcases (collinear_between habb').1 hab hab' hbb' with h | h | h,
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

lemma two_pt_segment_pt {a b a' b' : B.pts} :
(a-ₛb) = (a'-ₛb') → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') :=
begin
  intros haba'b',
  have := pt_left_in_segment a b,
  rw haba'b' at this, rcases this with ha | ha | ha,
  have := pt_left_in_segment a' b',
  rw ←haba'b' at this, rcases this with ha' | ha' | ha',
  simp at ha ha',  rw is_between_symm at ha, have hf := (is_between_trans ha ha').2, 
  have := pt_right_in_segment a b,
  rw haba'b' at this, rcases this with hb | hb | hb,
  simp at hb, rw is_between_symm at hf,
  exfalso, exact (collinear_between (is_between_collinear hb)).2.2.1 ⟨hb, hf⟩,
  exact absurd hb (is_between_not_eq ha').2.2.symm,
  exact absurd hb (is_between_not_eq hf).2.1.symm,
  exact absurd ha' (is_between_not_eq ha).1,
  right, rw segment_symm at haba'b',
  simp at ha',
  exact ⟨two_pt_segment_pt_prep haba'b' ha'.symm, ha'.symm⟩,
  left,
  exact ⟨ha, two_pt_segment_pt_prep haba'b' ha⟩,
  right, simp at ha,
  rw segment_symm a' b' at haba'b',
  exact ⟨ha, two_pt_segment_pt_prep haba'b' ha⟩
end

/--A type with a vertex and inside defined as the set consising of the vertex and
all points on the same side with a point `a` to the vertex.
-/
structure ray := (vertex : pts) (inside : set pts)
(in_eq : ∃ a : pts, inside = {x : pts | same_side_pt vertex a x} ∪ {vertex})

/--A ray can be defined by explicitly stating the vertex `o` and `a`. -/
def two_pt_ray (o a : pts) : ray := ⟨o, {x : pts | same_side_pt o a x} ∪ {o}, ⟨a, rfl⟩⟩

notation a`-ᵣ`b := two_pt_ray a b

lemma two_pt_ray_vertex (o a : pts) : (o-ᵣa).vertex = o := rfl

lemma ray_unique {r₁ r₂ : ray} (hr₁r₂ : r₁.vertex = r₂.vertex) :
(∃ x : pts, x ≠ r₁.vertex ∧ x ∈ r₁.inside ∩ r₂.inside) → r₁ = r₂ :=
begin
  rintros ⟨a, ha1, ha⟩,
  suffices : r₁.inside = r₂.inside,
    induction r₁ with v₁ I₁ hI₁, induction r₂ with v₂ I₂ hI₂ generalizing v₁ I₁ hI₁,
    simp, exact ⟨hr₁r₂, this⟩,
  cases r₁.in_eq with x h₁,
  cases r₂.in_eq with y h₂,
  replace h₁ : r₁.inside = {x : pts | same_side_pt r₁.vertex x a} ∪ {r₁.vertex},
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

lemma ray_eq_same_side_pt {r : ray} {a : pts}
(har : a ∈ r.inside) (hao : a ≠ r.vertex) : r = (r.vertex-ᵣa) :=
begin
  suffices : r.inside = (r.vertex-ᵣa).inside,
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

lemma two_pt_ray_eq_same_side_pt {o a b : pts} (hoab : same_side_pt o a b) :
(o-ᵣa) = (o-ᵣb) :=
begin
  unfold two_pt_ray, simp only [true_and, eq_self_iff_true], ext, simp,
  have : same_side_pt o a x ↔ same_side_pt o b x,
    split; intro h, exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  rw this
end

lemma ray_singleton (a : pts) : (a-ᵣa).inside = {a} :=
begin
  ext1, unfold two_pt_ray same_side_pt, simp,
  intro hf, unfold two_pt_segment at hf, simp at hf, exfalso, exact hf
end

lemma ray_disjoint {s₁ s₂ : ray} (hvertex : s₁.vertex = s₂.vertex) :
s₁ ≠ s₂ → s₁.inside ∩ s₂.inside = {s₁.vertex} :=
begin
  contrapose!, intro h,
  refine ray_unique hvertex _,
  by_contra hf, push_neg at hf,
  apply h, apply subset.antisymm, intro y, contrapose!, exact hf y,
  simp, cases s₁.in_eq, rw h_1, cases s₂.in_eq, rw h_2, rw hvertex, simp
end

lemma in_ray_collinear {o a b : pts} : b ∈ (o-ᵣa).inside → collinear o a b :=
begin
  intro h, 
  cases h, exact h.2, simp at h, rw h,
  by_cases hao : a = o,
    rw hao, rcases one_pt_line o with ⟨l, hl, hol⟩,
    exact ⟨l, hl, hol, hol, hol⟩,
  exact ⟨(a-ₗo), line_in_lines hao, pt_right_in_line a o, pt_left_in_line a o, pt_right_in_line a o⟩
end

lemma ray_reconstruct (r : ray) : ∃ a : pts, r = (r.vertex-ᵣa) :=
begin
  cases r.in_eq with x hx, use x, unfold two_pt_ray,
  induction r with v I hI, simp,
  simp at hx, rw hx
end

lemma ray_singleton_iff_eq {o a p : pts} :  (o-ᵣa).inside = {p} ↔ o = a ∧ o = p :=
begin
  by_cases hoa : o = a,
    rw [hoa, ray_singleton], simp,
  split; intro h,
  have : ∀ x ∈ (o-ᵣa).inside, x = p, rw h, simp, unfold two_pt_ray at this, simp at this,
  rw this.2 a (same_side_pt_refl hoa), exact ⟨this.1, this.1⟩,
  exact absurd h.1 hoa
end

lemma pt_left_in_ray (o a : pts) : o ∈ (o-ᵣa).inside :=
by {unfold two_pt_ray, simp}

lemma pt_right_in_ray (o a : pts) : a ∈ (o-ᵣa).inside :=
begin
  by_cases hoa : o = a,
    rw [hoa, ray_singleton], exact rfl,
  unfold two_pt_ray, simp, right, exact same_side_pt_refl (hoa)
end

lemma segment_in_ray (o a : pts) : (o-ₛa).inside ⊆ (o-ᵣa).inside :=
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

lemma ray_in_line (o a : pts) : (o-ᵣa).inside ⊆ (o-ₗa) :=
begin
  unfold two_pt_ray same_side_pt, intros x hx,
  simp at hx, cases hx with hx hx,
  rw hx, exact pt_left_in_line o a,
  have hoa : o ≠ a, intro hoa, rw hoa at hx, unfold two_pt_segment at hx, simp at hx, exact hx,
  rcases hx.2 with ⟨l, hl, hol, hal, hxl⟩,
  rw (two_pt_one_line (line_in_lines hoa) hl hoa
    ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨hol, hal⟩),
  exact hxl
end

lemma two_pt_ray_eq_same_side_pt_pt {o a b : pts} :
same_side_pt o a b ↔ (o-ᵣa) = (o-ᵣb) ∧ o ≠ a ∧ o ≠ b :=
begin
  split, intro hoab, unfold two_pt_ray,
  have : {x : pts | same_side_pt o a x} = {x : pts | same_side_pt o b x},
    ext, simp, split; intro h,
    exact same_side_pt_trans (same_side_pt_symm hoab) h,
    exact same_side_pt_trans hoab h,
  exact ⟨by {simp, simp at this, rw this},
    (same_side_pt_not_eq hoab).1.symm, (same_side_pt_not_eq hoab).2.symm⟩,
  rintros ⟨hoab, hoa, hob⟩,
  cases two_pt_between hoa with x hoxa,
  have hx : x ∈ (o-ᵣb).inside,
    rw ←hoab, unfold two_pt_ray, simp, right, exact same_side_pt_symm (is_between_same_side_pt.1 hoxa).1,
  unfold two_pt_ray at hx, simp at hx, cases hx with hx hx, exact absurd hx (is_between_not_eq hoxa).1.symm,
  exact same_side_pt_trans (same_side_pt_symm (is_between_same_side_pt.1 hoxa).1) (same_side_pt_symm hx)
end

lemma t_shape_ray {a b : pts} {e : pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (b-ᵣe).inside, x ≠ b → same_side_line (a-ₗb) e x :=
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

lemma t_shape_segment {a b : pts} {e : pts} (hab : a ≠ b) (heab : e ∉ (a-ₗb)) :
∀ x ∈ (b-ₛe).inside, x ≠ b → same_side_line (a-ₗb) e x :=
λ x hxbe hxb, t_shape_ray hab heab x ((segment_in_ray b e) hxbe) hxb

/--A type given by a vertex and its inside is the union of two rays with this vertex. -/
structure angle := (vertex : pts) (inside : set pts)
(in_eq : ∃ a b : pts, inside = (vertex-ᵣa).inside ∪ (vertex-ᵣb).inside)

lemma vertex_in_angle (α : angle) : α.vertex ∈ α.inside :=
by { rcases α.in_eq with ⟨a, b, h⟩, rw h, left, exact pt_left_in_ray _ _ }

/--Define an angle by giving its vertex and two other points on the two rays. -/
def three_pt_angle (a o b : pts) : angle := ⟨o, (o-ᵣa).inside∪(o-ᵣb).inside, ⟨a, b, rfl⟩⟩

notation `∠` := three_pt_angle

lemma angle_symm (a o b : pts) : ∠ a o b = ∠ b o a :=
by {unfold three_pt_angle, simp, rw union_comm}

lemma three_pt_angle_vertex (a o b : pts) : (∠ a o b).vertex = o :=
by unfold three_pt_angle

lemma pt_left_in_three_pt_angle (a o b : pts) : a ∈ (∠ a o b).inside :=
begin
  unfold three_pt_angle two_pt_ray, simp, left,
  by_cases a = o, left, exact h,
  right, exact (same_side_pt_refl (ne.symm h))
end

lemma pt_right_in_three_pt_angle (a o b : pts) : b ∈ (∠ a o b).inside :=
by {rw angle_symm, exact pt_left_in_three_pt_angle b o a}

lemma angle_eq_same_side (a : pts) {o b c : pts} (hobc : same_side_pt o b c) : ∠ a o b = ∠ a o c :=
by {unfold three_pt_angle, simp, rw two_pt_ray_eq_same_side_pt hobc}

/--An angle is nontrivial if its two sides are noncollinear. -/
def angle_nontrivial (α : angle) : Prop :=
∀ l ∈ lines, ¬α.inside ⊆ l

lemma three_pt_angle_nontrivial_not_eq {a o b : pts} :
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

lemma angle_nontrivial_iff_noncollinear {a o b : pts} :
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

private lemma three_pt_angle_eq_iff_prep {a o b a' b' : pts} (haob : angle_nontrivial (∠ a o b)) :
(∠ a o b) = (∠ a' o b') → same_side_pt o a a' → same_side_pt o b b' :=
begin
  intros he hoaa',
  have ha'ob' : noncollinear a' o b',
    rw he at haob, exact angle_nontrivial_iff_noncollinear.1 haob,
  rw angle_nontrivial_iff_noncollinear at haob,
  have hoa := (noncollinear_not_eq haob).1.symm,
  have hob := (noncollinear_not_eq haob).2.1,
  have hob' := (noncollinear_not_eq ha'ob').2.1,
  by_cases hbb' : b = b',
    rw ←hbb', exact same_side_pt_symm (same_side_pt_refl hob),
  have hb' : b' ∈ (∠ a o b).inside,
    rw he, unfold three_pt_angle, right, exact pt_right_in_ray o b',
  cases hb' with hb' hb',
  exfalso, apply noncollinear12 ha'ob',
  exact collinear_trans hoaa'.2 ⟨(o-ₗa), line_in_lines hoa,
    pt_left_in_line o a, pt_right_in_line o a, (ray_in_line o a) hb'⟩ hoa,
  cases hb' with hb' hb',
  exact hb', exact absurd hb' hob'.symm
end

lemma three_pt_angle_eq_iff {a o b a' o' b' : pts}
(haob : noncollinear a o b) : (∠ a o b) = (∠ a' o' b') ↔ o = o'
∧ ((same_side_pt o a a' ∧ same_side_pt o b b') ∨ (same_side_pt o a b' ∧ same_side_pt o b a')) :=
begin
  split, intro he,
  have hoo' : o = o',
    unfold three_pt_angle at he, simp at he, exact he.1,
  have ha'ob' : noncollinear a' o b',
    rw [←angle_nontrivial_iff_noncollinear, he, ←hoo'] at haob, exact angle_nontrivial_iff_noncollinear.1 haob,
  have ha'o := (noncollinear_not_eq ha'ob').1,
  split, exact hoo',
  rw ←hoo' at he,
  have ha' : a' ∈ (∠ a o b).inside,
    rw he, unfold three_pt_angle, left, exact pt_right_in_ray o a',
  cases ha' with ha' ha';
  cases ha' with ha' ha',
  left, exact ⟨ha', three_pt_angle_eq_iff_prep (angle_nontrivial_iff_noncollinear.2 haob) he ha'⟩,
  exact absurd ha' ha'o,
  right, rw angle_symm at he,
  exact ⟨three_pt_angle_eq_iff_prep (angle_nontrivial_iff_noncollinear.2 (noncollinear13 haob)) he ha', ha'⟩,
  exact absurd ha' ha'o,
  rintros ⟨hoo', h | h⟩,
  rw [angle_eq_same_side a h.2, angle_symm, angle_eq_same_side b' h.1, angle_symm, hoo'],
  rw [angle_eq_same_side a h.2, angle_symm, angle_eq_same_side a' h.1, hoo']
end

lemma angle_three_pt (α : angle) : ∃ a b : pts, α = ∠ a α.vertex b :=
begin
  rcases α.in_eq with ⟨a, b, h⟩,
  use [a, b], unfold three_pt_angle, induction α, simp, exact h
end

/--A point `p` is inside `∠ a o b` if `p` and `a` are on the same side to `o-ₗa` and
`p` and `b` are on the same side to line `o-ₗb`. -/
def inside_angle (p : pts) (α : angle) : Prop :=
(∃ a b : pts, α = ∠ a α.vertex b ∧ same_side_line (α.vertex-ₗa) b p ∧ same_side_line (α.vertex-ₗb) a p)

lemma inside_angle_nontrivial {p : pts} {α : angle} :
inside_angle p α → angle_nontrivial α :=
begin
  rintros ⟨a, b, hα, hbp, hap⟩,
  rw [hα, angle_nontrivial_iff_noncollinear],
  intro haob,
  by_cases α.vertex = b,
    rw h at hbp,
    exact (same_side_line_not_in hbp).1 (pt_left_in_line b a),
  exact (same_side_line_not_in hap).1 (collinear_in23 haob h)
end

lemma inside_three_pt_angle {p a o b : pts}:
inside_angle p (∠ a o b) ↔ same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p :=
begin
  have : ∀ {p a o b a' b' : pts}, same_side_line (o-ₗa') b' p → same_side_line (o-ₗb') a' p → noncollinear a' o b'
    → same_side_pt o a a' ∧ same_side_pt o b b' → same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p,
    intros p a o b a' b' hb'p ha'p ha'ob' h,
    rw two_pt_one_line (line_in_lines (same_side_pt_not_eq h.1).1.symm) (line_in_lines (same_side_pt_not_eq h.1).2.symm),
    rw two_pt_one_line (line_in_lines (same_side_pt_not_eq h.2).1.symm) (line_in_lines (same_side_pt_not_eq h.2).2.symm),
    split, apply same_side_line_symm,
    apply same_side_line_trans (line_in_lines (same_side_pt_not_eq h.1).2.symm) (same_side_line_symm hb'p),
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact (same_side_pt_not_eq h.1).2,
    intro hf, exact ha'ob' ⟨(a'-ₗo), line_in_lines (same_side_pt_not_eq h.1).2, pt_left_in_line a' o, pt_right_in_line a' o, hf⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm h.2,
    exact (same_side_pt_not_eq h.2).1,
    apply same_side_line_symm,
    apply same_side_line_trans (line_in_lines (same_side_pt_not_eq h.2).2.symm) (same_side_line_symm ha'p),
    rw line_symm, refine t_shape_ray _ _ _ _ _, exact (same_side_pt_not_eq h.2).2,
    intro hf, exact ha'ob' ⟨(b'-ₗo), line_in_lines (same_side_pt_not_eq h.2).2, hf, pt_right_in_line b' o, pt_left_in_line b' o⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm h.1,
    exact (same_side_pt_not_eq h.1).1,
    exact (same_side_pt_not_eq h.2).1, exact ⟨pt_right_in_line o b, pt_left_in_line o b⟩,
    split, apply ray_in_line o b', left, exact same_side_pt_symm h.2, exact pt_left_in_line o b',
    exact (same_side_pt_not_eq h.1).1, exact ⟨pt_right_in_line o a, pt_left_in_line o a⟩,
    split, apply ray_in_line o a', left, exact same_side_pt_symm h.1, exact pt_left_in_line o a',
  split, intro hp,
  have haob := inside_angle_nontrivial hp,
  rcases hp with ⟨a', b', haoba'ob', hb'p, ha'p⟩,
  rw three_pt_angle_vertex at haoba'ob' ha'p hb'p,
  have ha'ob' : noncollinear a' o b',
    rw [haoba'ob', angle_nontrivial_iff_noncollinear] at haob, exact haob,
  rw angle_nontrivial_iff_noncollinear at haob,
  cases ((three_pt_angle_eq_iff haob).1 haoba'ob').2,
  exact this hb'p ha'p ha'ob' h,
  exact this ha'p hb'p (noncollinear13 ha'ob') h,
  rintros ⟨hbp, hap⟩,
  use [a, b], rw three_pt_angle_vertex,
  exact ⟨rfl, hbp, hap⟩
end

lemma inside_angle_nontrivial' {p a o b : pts} : inside_angle p (∠ a o b)
→ angle_nontrivial (∠ p o a) ∧ angle_nontrivial (∠ p o b) :=
begin
  intro hp,
  have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  have hoa := (noncollinear_not_eq haob).1.symm,
  have hob := (noncollinear_not_eq haob).2.1,
  rw inside_three_pt_angle at hp,
  split; rw angle_nontrivial_iff_noncollinear; intro h,
  exact (same_side_line_not_in hp.1).2 (collinear_in23 h hoa),
  exact (same_side_line_not_in hp.2).2 (collinear_in23 h hob)
end

theorem crossbar {a b c d : pts}
(hd : inside_angle d (∠ b a c)) : (two_pt_ray a d).inside ♥ (b-ₛc).inside :=
begin
  have hbac := inside_angle_nontrivial hd, rw angle_nontrivial_iff_noncollinear at hbac,
  rw inside_three_pt_angle at hd,
  by_cases hac : a = c,
    rw hac, use c, unfold two_pt_ray, unfold two_pt_segment, simp,
  by_cases hab : a = b,
    rw hab, use b, unfold two_pt_ray, unfold two_pt_segment, simp,
  cases is_between_extend (ne.symm hac) with e hcae,
  have had : a ≠ d,
    intro had, rw ←had at hd, have hf := (same_side_line_not_in hd.1).2,
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
  have hadab : ∀ x ∈ (a-ᵣd).inside, x ≠ a → same_side_line (a-ₗb) d x,
    have hdba : d ∉ (b-ₗa), rw line_symm, from (same_side_line_not_in hd.1).2,
    rw line_symm a b, exact t_shape_ray (ne.symm hab) hdba,
  have hdbac : same_side_line (a-ₗc) d b, from same_side_line_symm hd.2,
  have h₂ : ¬((a-ₗd) ♥ (e-ₛb).inside),
    have hdcab := same_side_line_symm hd.1,
    rintros ⟨f, hf⟩, rw segment_symm at hf, simp at hf,
    have hfb : f ≠ b,
      intro hfb, rw hfb at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hab) hab ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩) at this,
      exact (same_side_line_not_in hd.1).2 this,
    have hfe : f ≠ e,
      intro hfe, rw hfe at hf, have := pt_right_in_line a d,
      rw (two_pt_one_line (line_in_lines had) (line_in_lines hae) hae ⟨pt_left_in_line a d, hf.1⟩ ⟨pt_left_in_line a e, pt_right_in_line a e⟩) at this,
      rw haeac at this, exact (same_side_line_not_in hd.2).2 this,
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
    have hfad : f ∈ (a-ᵣd).inside,
      unfold two_pt_ray, left, unfold same_side_pt, split,
      intro hadf, apply hdfac,
      exact ⟨a, pt_left_in_line a c, hadf⟩,
      exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hf.1⟩,
    specialize hadab f hfad hfa,
    have hedab := same_side_line_trans (line_in_lines hab) hbeab (same_side_line_symm hadab),
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
    exact (same_side_line_not_in hd.2).2 this,
  specialize hcbac f hfcb hfc,
  have hdfac := same_side_line_trans (line_in_lines hac) hdbac hcbac,
  use f, split,
  unfold two_pt_ray same_side_pt, simp, right, split,
  intro hf, apply hdfac, use a, exact ⟨pt_left_in_line a c, hf⟩,
  exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, hfad⟩,
  rw segment_symm, exact hfcb
end

lemma ray_inside_angle {a o b p q : pts} :
inside_angle p (∠ a o b) → same_side_pt o p q → inside_angle q (∠ a o b) :=
begin
  intros hp hopq,
  have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  rw inside_three_pt_angle at hp, rw inside_three_pt_angle,
  have hoa := (noncollinear_not_eq haob).1.symm,
  have hob := (noncollinear_not_eq haob).2.1,
  have hoq := (same_side_pt_not_eq hopq).2.symm,
  split,
  apply same_side_line_trans (line_in_lines hoa) hp.1,
  rw line_symm, refine t_shape_ray hoa.symm _ _ _ _,
  rw line_symm, exact (same_side_line_not_in hp.1).2,
  left, exact hopq, exact hoq.symm,
  apply same_side_line_trans (line_in_lines hob) hp.2,
  rw line_symm, refine t_shape_ray hob.symm _ _ _ _,
  rw line_symm, exact (same_side_line_not_in hp.2).2,
  left, exact hopq, exact hoq.symm
end

lemma inside_angle_diff_side_line {a o b p : pts} :
inside_angle p (∠ a o b) → diff_side_line (o-ₗp) a b :=
begin
  intro hp,
  have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  have hop : o ≠ p,
    intro hop, rw [inside_three_pt_angle, hop] at hp,
    exact (same_side_line_not_in hp.1).2 (pt_left_in_line p a),
  cases crossbar hp with q hq, use q,
  exact ⟨(ray_in_line o p) hq.1, hq.2⟩,
  rw inside_three_pt_angle at hp,
  have hoa := (noncollinear_not_eq haob).1.symm,
  have hob := (noncollinear_not_eq haob).2.1,
  split, intro ha,
  exact (same_side_line_not_in hp.1).2(collinear_in23 ⟨(o-ₗp), line_in_lines hop, pt_right_in_line o p, pt_left_in_line o p, ha⟩ hoa),
  intro hb,
  exact (same_side_line_not_in hp.2).2 (collinear_in23 ⟨(o-ₗp), line_in_lines hop, pt_right_in_line o p, pt_left_in_line o p, hb⟩ hob)
end

-- This should not be a section, this should be a file, or ideally more than one file: 
-- find good subsections and break stuff up.

end incidence_order_geometry_API

/--A Hilbert plane extends incidence order geometry. It contains two binary relations, segment
congruence and angle congruence. Intuitionally, they correspond to lengths of two segments and
radians of two angles equal. They subject to the following axioms.
C1 : Given a segment and two distinct points `a` `b`, we find uniquely find a point `c` on the
same side with `b` to `a` such that segment `a` `c` is congruent to the segment.
C2 : Segment congruence is an equivalence relation.
C3 : Two segments are congruent if their two parts are congruent.
C4 : Given a nontrivial angle `α` and points `a` `b`, we can find `c` such that `∠c a b`
     is congruent to `α`. `c` is uniquely defined given one side of line `a` `b`.
C5 : Angle congruence is an equivalent relation.
C6 : Two triangles are congruent by SAS.
-/
class hilbert_plane extends incidence_order_geometry :=
(segment_congr : segment → segment → Prop)
(C1 : ∀ {a b : pts} {l : segment}, segment_nontrivial l → a ≠ b → ∃ c : pts, same_side_pt a b c ∧
segment_congr l (a-ₛc) ∧ ∀ x : pts, same_side_pt a b x → segment_congr l (a-ₛx) → x = c)
(C2 : (∀ {s₁ s₂ s₃ : segment}, (segment_congr s₁ s₂ → segment_congr s₁ s₃ → segment_congr s₂ s₃))
    ∧ ∀ (s₁ : segment),  segment_congr s₁ s₁)
(C3 : ∀ {a b c d e f: pts}, is_between a b c → is_between d e f → segment_congr (a-ₛb) (d-ₛe)
                        → segment_congr (b-ₛc) (e-ₛf) → segment_congr (a-ₛc) (d-ₛf))
(angle_congr : angle → angle → Prop)
(C4 : ∀ {α : angle} {a b p : pts}, angle_nontrivial α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, angle_congr α (∠c a b) ∧ same_side_line (a-ₗb) c p
∧ ∀ x : pts, same_side_line (a-ₗb) c x → angle_congr α (∠x a b) → x ∈ (a-ᵣc).inside)
(C5 : ∀ α β γ : angle, (angle_congr α β → angle_congr α γ → angle_congr β γ) ∧ angle_congr α α)
(C6 : ∀ {a b c d e f : pts}, noncollinear a b c → noncollinear d e f → segment_congr (a-ₛb) (d-ₛe)
→ segment_congr (a-ₛc) (d-ₛf) → angle_congr (∠b a c) (∠e d f)
→ segment_congr (b-ₛc) (e-ₛf) ∧ angle_congr (∠a b c) (∠d e f) ∧ angle_congr (∠a c b) (∠d f e))

section hilbert_plane_API

open incidence_geometry incidence_order_geometry hilbert_plane

variables [C : hilbert_plane]

include C

notation a`-ₗ`b := (line a b : set pts)

notation a`≅ₛ`b := segment_congr a b

lemma extend_congr_segment {a b : pts} {s : segment} (hs : segment_nontrivial s) (hab : a ≠ b) :
∃ c : pts, same_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
∧ ∀ x : pts, same_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c := C1 hs hab

lemma segment_congr_refl (s : segment) : s ≅ₛ s := C2.2 s

lemma segment_congr_symm {s₁ s₂ : segment} :
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₁) := λ h, C2.1 h (segment_congr_refl s₁)

lemma segment_congr_trans {s₁ s₂ s₃ : segment} : 
(s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₃) → (s₁ ≅ₛ s₃) := λ h₁ h₂, C2.1 (segment_congr_symm h₁) h₂

lemma congr_segment_add {a b c d e f: pts} : is_between a b c → is_between d e f
→ ((a-ₛb) ≅ₛ (d-ₛe)) → ((b-ₛc) ≅ₛ (e-ₛf)) → ((a-ₛc) ≅ₛ (d-ₛf)) :=
λh₁ h₂ h₃ h₄, C3 h₁ h₂ h₃ h₄

lemma congr_segment_sub {a b c d e f : pts} (habc : is_between a b c) (hdef : same_side_pt d e f)
(habde : (a-ₛb)≅ₛ(d-ₛe)) (hacdf : (a-ₛc)≅ₛ(d-ₛf)) : is_between d e f ∧ ((b-ₛc)≅ₛ(e-ₛf)) :=
begin
  rcases is_between_extend (same_side_pt_not_eq hdef).1.symm with ⟨x, hdex⟩,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (is_between_not_eq habc).2.2)
    (is_between_not_eq hdex).2.2 with ⟨f', hexf', hbcef', -⟩,
  have hdef' : is_between d e f',
    rcases is_between_collinear hdex with ⟨l, hl, hdl, hel, hxl⟩,
    rcases hexf'.2 with ⟨m, hm, hem, hxm, hf'm⟩,
    rw (two_pt_one_line hm hl (same_side_pt_not_eq hexf').1 ⟨hxm, hem⟩ ⟨hxl, hel⟩) at hf'm,
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hf'm⟩
      (is_between_not_eq hdex).1 (same_side_pt_not_eq hexf').2],
    rw [is_between_diff_side_pt, ←not_same_side_pt ⟨l, hl, hel, hdl, hxl⟩
      (same_side_pt_not_eq hdef).1.symm (same_side_pt_not_eq hexf').1] at hdex,
    intro hedf', exact hdex (same_side_pt_trans hedf' (same_side_pt_symm hexf')),
  have hacdf' := C3 habc hdef' habde hbcef',
  have hff' : f = f',
    rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (is_between_not_eq habc).2.1)
      (is_between_not_eq hdef').1 with ⟨f'', -, -, hf''⟩,
    rw [hf'' f hdef hacdf, hf'' f' (is_between_same_side_pt.mp hdef').1 hacdf'],
  rw hff', exact ⟨hdef', hbcef'⟩
end

/--Segment `m` is less than segment `n` if "one part" of `m` is congruent to `n`.
That is, there exists a point `a` between the two endpoints of `m` such that `a`
and one of the endpoint form a segment congruent to `n`
-/
def segment_lt (m n : segment) : Prop :=
(∃ a b c : C.pts, n = (b-ₛc) ∧ is_between b a c ∧ (m ≅ₛ (b-ₛa)))

notation a`<ₛ`b := segment_lt a b

lemma segment_lt_nontrivial {m n : segment} : (m <ₛ n) → segment_nontrivial n :=
begin
  rintros ⟨a, b, c, hn, hbac, hm⟩,
  rw [hn, segment_nontrivial_iff_neq], exact (is_between_not_eq hbac).2.1
end

lemma two_pt_segment_lt {m : segment} {a b : C.pts} :
(m <ₛ (a-ₛb)) ↔ ∃ x : C.pts, is_between a x b ∧ (m ≅ₛ (a-ₛx)):=
begin
  split; intro h,
  have hab := segment_lt_nontrivial h, rw segment_nontrivial_iff_neq at hab,
  rcases h with ⟨x, a', b', haba'b', ha'xb', hm⟩,
  cases two_pt_segment_pt haba'b',
  rw [←h.1, ←h.2] at ha'xb', rw ←h.1 at hm,
  exact ⟨x, ha'xb', hm⟩,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (is_between_not_eq ha'xb').1) hab
    with ⟨y, haby, hy, -⟩,
  use y, rw [←h.1, ←h.2] at ha'xb', rw ←h.2 at hy, rw ←h.2 at hm,
  split,
  exact (congr_segment_sub ha'xb' (same_side_pt_symm haby) hy
    (by {rw segment_symm, exact segment_congr_refl _})).1,
  exact segment_congr_trans hm hy,
  cases h with x hx,
  use [x, a, b], exact ⟨rfl, hx.1, hx.2⟩
end

lemma segment_lt_congr {m n l : segment} (hmn : m ≅ₛ n) :
((m <ₛ l) → (n <ₛ l)) ∧ (segment_nontrivial n → (l <ₛ m) → (l <ₛ n)) :=
begin
  split, rintros ⟨a, b, c, hlbc, hbac, hm⟩,
  exact ⟨a, b, c, hlbc, hbac, segment_congr_trans (segment_congr_symm hmn) hm⟩,
  intros hn hl, rcases hl with ⟨a, b, c, hmbc, hbac, hl⟩,
  rcases segment_two_pt n with ⟨d, e, hnde⟩, rw hnde,
  rw [hnde, segment_nontrivial_iff_neq] at hn,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (is_between_not_eq hbac).1) hn
    with ⟨x, hdex, hbadx, -⟩,
  rw two_pt_segment_lt, use x,
  split,
  rw [hmbc, hnde] at hmn,
  exact (congr_segment_sub hbac (same_side_pt_symm hdex) hbadx hmn).1,
  exact segment_congr_trans hl hbadx
end

lemma segment_lt_trans {m n l : segment} :
(m <ₛ n) → (n <ₛ l) → (m <ₛ l) :=
begin
  intros hmn hnl,
  rcases hnl with ⟨a, b, c, hl, hbac, hn⟩,
  have hab := (is_between_not_eq hbac).1.symm,
  replace hmn := (segment_lt_congr hn).2 (segment_nontrivial_iff_neq.2 hab.symm) hmn,
  rw two_pt_segment_lt at hmn,
  rcases hmn with ⟨x, hbxa, hm⟩,
  rw [hl, two_pt_segment_lt],
  use x, rw is_between_symm,
  rw is_between_symm at hbac hbxa,
  exact ⟨(is_between_trans' hbac hbxa).2, hm⟩
end

lemma segment_congr_same_side_unique {a b c d : pts}
(habc : same_side_pt a b c) (habd : same_side_pt a b d) : ((a-ₛc) ≅ₛ (a-ₛd)) → c = d :=
begin
  intro hacad,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (same_side_pt_not_eq habc).2.symm)
    (same_side_pt_not_eq habc).1.symm with ⟨x, habx, hacax, hu⟩,
  rw [hu c habc (segment_congr_refl _), hu d habd hacad]
end

lemma segment_tri {m n : segment} (ha'b' : segment_nontrivial m) (hab : segment_nontrivial n) :
((m <ₛ n) ∨ (m ≅ₛ n) ∨ (n <ₛ m))
∧ ¬((m <ₛ n) ∧ (m ≅ₛ n)) ∧ ¬((m <ₛ n) ∧ (n <ₛ m)) ∧ ¬(((m ≅ₛ n) ∧ (n <ₛ m))) :=
begin
  rcases segment_two_pt n with ⟨a, b, hn⟩,
  rw [hn, segment_nontrivial_iff_neq] at hab,
  rcases extend_congr_segment ha'b' hab with ⟨c, habc, hm, -⟩,
  have h₁ : (m <ₛ n) ↔ same_side_pt b a c,
    rw [hn, two_pt_segment_lt], split,
    rintros ⟨c', hac'b, hm'⟩,
    rw is_between_same_side_pt at hac'b,
    have : c = c',
      from segment_congr_same_side_unique habc (same_side_pt_symm hac'b.1)
      (segment_congr_trans (segment_congr_symm hm) hm'),
    rw this, exact (hac'b).2,
    intro hbac, exact ⟨c, is_between_same_side_pt.2 ⟨same_side_pt_symm habc, hbac⟩, hm⟩,
  have h₂ : (m ≅ₛ n) ↔ c = b,
    rw hn, split,
    intro hm',
    exact segment_congr_same_side_unique habc (same_side_pt_refl hab)
      (segment_congr_trans (segment_congr_symm hm) hm'),
    intro hcb, rw hcb at hm, exact hm,
  have h₃ : (n <ₛ m) ↔ diff_side_pt b a c,
    rw hn, split,
    intro hnm,
    replace hnm := (segment_lt_congr hm).2
      (segment_nontrivial_iff_neq.2 (same_side_pt_not_eq habc).2.symm) hnm,
    rw two_pt_segment_lt at hnm,
    rcases hnm with ⟨d, hadc, habad⟩,
    rw segment_congr_same_side_unique (same_side_pt_symm habc)
      (same_side_pt_symm (is_between_same_side_pt.1 hadc).1) habad,
    rw ←is_between_diff_side_pt, exact hadc,
    intro hbac,
    apply (segment_lt_congr (segment_congr_symm hm)).2 ha'b',
    rw two_pt_segment_lt,
    exact ⟨b, is_between_diff_side_pt.2 hbac, segment_congr_refl _⟩,
  rw [h₁, h₂, h₃],
  split,
  by_cases hbc : b = c,
    right, left, exact hbc.symm,
  cases (line_separation (collinear12 habc.2) hab (ne.symm hbc)).1,
  left, exact h,
  right, right, exact h,
  split, intro hf, exact (same_side_pt_not_eq hf.1).2 hf.2,
  split, intro hf, rw ←not_diff_side_pt at hf, exact hf.1 hf.2,
  exact collinear12 habc.2, exact hab, exact hf.2.2.2,
  intro hf, exact hf.2.2.2 hf.1
end

notation a`≅ₐ`b := angle_congr a b

lemma angle_congr_refl (α : angle) : α ≅ₐ α := (C5 α α α).2

lemma angle_congr_symm {α β : angle} :
(α ≅ₐ β) → (β ≅ₐ α) := λ h, (C5 α β α).1 h (angle_congr_refl α)

lemma angle_congr_trans {α β γ : angle} : 
(α ≅ₐ β) → (β ≅ₐ γ) → (α ≅ₐ γ) := λ h₁ h₂, (C5 β α γ).1 (angle_congr_symm h₁) h₂

lemma extend_congr_angle {α : angle} {a b p : pts} :
angle_nontrivial α → a ≠ b → p ∉ (a-ₗb)
→ ∃ c : pts, angle_congr α (∠ c a b) ∧ same_side_line (a-ₗb) c p
∧ ∀ x : pts, same_side_line (a-ₗb) c x → angle_congr α (∠x a b) → x ∈ (a-ᵣc).inside := C4

/--Two nontrivial angles are supplementary if their shares one common ray and the other two
rays lie on the same line in opposite sides. -/
def supplementary (α β : angle) : Prop :=
(∃ a b c d : pts, α = ∠ b a c ∧ β = ∠ b a d ∧ is_between c a d)
∧ angle_nontrivial α ∧ angle_nontrivial β

lemma supplementary_symm {α β : angle} : supplementary α β ↔ supplementary β α :=
begin
  split; rintros ⟨⟨a, b, c, d, hbac, hbad, hcad⟩, h₁, h₂⟩;
  exact ⟨⟨a, b, d, c, hbad, hbac, by {rw is_between_symm, exact hcad}⟩, h₂, h₁⟩,
end

lemma three_pt_angle_supplementary {a b c d : pts} :
supplementary (∠b a c) (∠b a d) ↔ is_between c a d ∧ noncollinear b a c ∧ noncollinear b a d :=
begin
  split,
  rintros ⟨⟨a', b', c', d', hbac, hbad, hc'a'd'⟩, h₁, h₂⟩,
  have h₁' : angle_nontrivial (∠ b' a' c'), rw ←hbac, exact h₁,
  have h₂' : angle_nontrivial (∠ b' a' d'), rw ←hbad, exact h₂,
  rw angle_nontrivial_iff_noncollinear at h₁ h₁' h₂ h₂',
  have haa' : a = a', from ((three_pt_angle_eq_iff h₁).1 hbac).1,
  rw ←haa' at hc'a'd',
  cases ((three_pt_angle_eq_iff h₁).1 hbac).2 with H₁ H₁;
  cases ((three_pt_angle_eq_iff h₂).1 hbad).2 with H₂ H₂,
  split,
  rw [is_between_diff_side_pt, ←not_same_side_pt], intro hacd,
  rw [is_between_diff_side_pt, ←not_same_side_pt] at hc'a'd',
  exact hc'a'd' (same_side_pt_trans (same_side_pt_trans (same_side_pt_symm H₁.2) hacd) H₂.2),
  exact diff_side_pt_collinear hc'a'd', exact hc'a'd'.2.1, exact hc'a'd'.2.2,
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
  exact diff_side_pt_collinear hc'a'd', exact hc'a'd'.2.1, exact hc'a'd'.2.2,
  rintros ⟨hcad, hbac, hbad⟩,
  use [a, b, c, d], simp, exact hcad,
  rw [angle_nontrivial_iff_noncollinear, angle_nontrivial_iff_noncollinear], exact ⟨hbac, hbad⟩
end

/--A triangle consists of three vertices. Note that it is defined to be ordered. -/
structure triangle := (v1 : pts) (v2 : pts) (v3 : pts)

/--Two triangles are congruent if their sides and angles are equal in order. -/
def tri_congr (t₁ t₂ : triangle) : Prop :=
((t₁.v1-ₛt₁.v2) ≅ₛ (t₂.v1-ₛt₂.v2)) ∧ ((t₁.v1-ₛt₁.v3) ≅ₛ (t₂.v1-ₛt₂.v3)) ∧ ((t₁.v2-ₛt₁.v3) ≅ₛ (t₂.v2-ₛt₂.v3))
∧ ((∠t₁.v2 t₁.v1 t₁.v3 ≅ₐ ∠t₂.v2 t₂.v1 t₂.v3)
∧ (∠t₁.v1 t₁.v2 t₁.v3 ≅ₐ ∠t₂.v1 t₂.v2 t₂.v3)
∧ (∠t₁.v1 t₁.v3 t₁.v2 ≅ₐ ∠t₂.v1 t₂.v3 t₂.v2))

notation a`≅ₜ`b := tri_congr a b

lemma tri_congr_refl (t : triangle) : t ≅ₜ t :=
⟨segment_congr_refl _, segment_congr_refl _, segment_congr_refl _,
angle_congr_refl _, angle_congr_refl _, angle_congr_refl _⟩

lemma tri_congr_symm {t₁ t₂ : triangle} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₁) :=
λh, ⟨segment_congr_symm h.1, segment_congr_symm h.2.1, segment_congr_symm h.2.2.1,
angle_congr_symm h.2.2.2.1, angle_congr_symm h.2.2.2.2.1, angle_congr_symm h.2.2.2.2.2⟩

lemma tri_congr_trans {t₁ t₂ t₃ : triangle} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₃) → (t₁ ≅ₜ t₃) :=
λh₁ h₂, ⟨segment_congr_trans h₁.1 h₂.1, segment_congr_trans h₁.2.1 h₂.2.1,
segment_congr_trans h₁.2.2.1 h₂.2.2.1, angle_congr_trans h₁.2.2.2.1 h₂.2.2.2.1,
angle_congr_trans h₁.2.2.2.2.1 h₂.2.2.2.2.1, angle_congr_trans h₁.2.2.2.2.2 h₂.2.2.2.2.2⟩

/--Define a triangle with three vertices. -/
def three_pt_triangle (a b c : pts) : triangle := ⟨a, b, c⟩

notation `Δ` := three_pt_triangle

lemma three_pt_triangle_v1 (a b c : pts) : (Δ a b c).v1 = a := rfl

lemma three_pt_triangle_v2 (a b c : pts) : (Δ a b c).v2 = b := rfl

lemma three_pt_triangle_v3 (a b c : pts) : (Δ a b c).v3 = c := rfl

lemma tri_congr12 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b a c) ≅ₜ (Δ b' a' c')) :=
begin
  unfold tri_congr, rw [three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3, three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3],
  rw [segment_symm, segment_symm a' b'],
  rw [angle_symm a c b, angle_symm a' c' b'],
  tauto
end

lemma tri_congr13 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c b a) ≅ₜ (Δ c' b' a')) :=
begin
  unfold tri_congr, rw [three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3, three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3],
  rw [segment_symm, segment_symm a' b'],
  rw [segment_symm a c, segment_symm a' c'],
  rw [segment_symm b c, segment_symm b' c'],
  rw [angle_symm b a c, angle_symm b' a' c'],
  rw [angle_symm a c b, angle_symm a' c' b'],
  rw [angle_symm a b c, angle_symm a' b' c'],
  tauto
end

lemma tri_congr23 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ a c b) ≅ₜ (Δ a' c' b')) :=
begin
  unfold tri_congr, rw [three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3, three_pt_triangle_v1, three_pt_triangle_v1, three_pt_triangle_v2, three_pt_triangle_v2, three_pt_triangle_v3, three_pt_triangle_v3],
  rw [segment_symm, segment_symm a' b'],
  rw [segment_symm a c, segment_symm a' c'],
  rw [segment_symm b c, segment_symm b' c'],
  rw [angle_symm b a c, angle_symm b' a' c'],
  rw [angle_symm a c b, angle_symm a' c' b'],
  rw [angle_symm a b c, angle_symm a' b' c'],
  tauto
end

lemma tri_congr123 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b c a) ≅ₜ (Δ b' c' a')) := λh, tri_congr23 (tri_congr12 h)

lemma tri_congr132 {a b c a' b' c': pts} :
((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c a b) ≅ₜ (Δ c' a' b')) := λh, tri_congr23 (tri_congr13 h)

lemma tri_congr_side {a b c a' b' c': pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
((a-ₛb) ≅ₛ (a'-ₛb')) ∧ ((a-ₛc) ≅ₛ (a'-ₛc')) ∧ ((b-ₛc) ≅ₛ (b'-ₛc')) :=
begin
  unfold tri_congr three_pt_triangle at h, simp at h,
  exact ⟨h.1, h.2.1, h.2.2.1⟩
end

lemma tri_congr_angle {a b c a' b' c': pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
(∠ b a c ≅ₐ ∠ b' a' c') ∧ (∠ a b c ≅ₐ ∠ a' b' c') ∧ (∠ a c b ≅ₐ ∠ a' c' b') :=
begin
  unfold tri_congr three_pt_triangle at h, simp at h,
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
end

lemma SAS {ABC DEF : triangle} (h₁ : noncollinear ABC.v1 ABC.v2 ABC.v3) (h₂ : noncollinear DEF.v1 DEF.v2 DEF.v3)
(hs₁ : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2)) (hs₂ : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3))
(ha : (∠ABC.v2 ABC.v1 ABC.v3 ≅ₐ ∠DEF.v2 DEF.v1 DEF.v3)) : ABC ≅ₜ DEF :=
⟨hs₁, hs₂, (C6 h₁ h₂ hs₁ hs₂ ha).1, ha, (C6 h₁ h₂ hs₁ hs₂ ha).2.1, (C6 h₁ h₂ hs₁ hs₂ ha).2.2⟩

lemma supplementary_congr {α α' β β' : angle}
(h : supplementary α α') (h' : supplementary β β') : (α ≅ₐ β) → (α' ≅ₐ β') :=
begin
  rcases h.1 with ⟨a, b, c, d, hα, hα', hcad⟩,
  rcases h'.1 with ⟨a', b', c', d', hβ, hβ', hc'a'd'⟩,
  intro hbac,
  rw [hα, hα'] at h, rw [hβ, hβ'] at h', rw [hα, hβ] at hbac, rw [hα', hβ'],
  have ha'b' := (noncollinear_not_eq (angle_nontrivial_iff_noncollinear.1 h'.2.1)).1.symm,
  have ha'c' := (noncollinear_not_eq (angle_nontrivial_iff_noncollinear.1 h'.2.1)).2.1,
  have ha'd' := (noncollinear_not_eq (angle_nontrivial_iff_noncollinear.1 h'.2.2)).2.1,
  have hab := (noncollinear_not_eq (angle_nontrivial_iff_noncollinear.1 h.2.1)).1.symm,
  have hac := (is_between_not_eq hcad).1.symm,
  have had := (is_between_not_eq hcad).2.2,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 hab) ha'b' with ⟨x, ha'b'x, haba'b', -⟩,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 hac) ha'c' with ⟨y, ha'b'y, haca'c', -⟩,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 had) ha'd' with ⟨z, ha'b'z, hada'd', -⟩,
  have : (∠b' a' c') = (∠x a' y),
    unfold three_pt_angle, simp,
    rw [(two_pt_ray_eq_same_side_pt_pt.1 ha'b'x).1, (two_pt_ray_eq_same_side_pt_pt.1 ha'b'y).1],
  rw this at h' hbac,
  have : (∠b' a' d') = (∠x a' z),
    unfold three_pt_angle, simp,
    rw [(two_pt_ray_eq_same_side_pt_pt.1 ha'b'x).1, (two_pt_ray_eq_same_side_pt_pt.1 ha'b'z).1],
  rw this at h', rw this,
  rename [x b', y c', z d'],
  have h₁ : ((Δ a b c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triangle; simp,
    rintros ⟨l, hl, habcl⟩, apply angle_nontrivial_iff_noncollinear.1 h.2.1, use l, tauto,
    rintros ⟨l, hl, habcl'⟩, apply angle_nontrivial_iff_noncollinear.1 h'.2.1, use l, tauto,
    exact haba'b', exact haca'c', exact hbac,
  have hcad := is_between_diff_side_pt.2 (is_between_diff_side_pt.1 (three_pt_angle_supplementary.1 h).1),
  have hc'a'd' := is_between_diff_side_pt.2 (is_between_diff_side_pt.1 (three_pt_angle_supplementary.1 h').1),
  have h₂ : ((Δ c b d) ≅ₜ (Δ c' b' d')),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear23 (collinear_trans' (is_between_collinear hcad)
      (noncollinear13 (angle_nontrivial_iff_noncollinear.1 h.2.1)) (is_between_not_eq hcad).2.1),
    exact noncollinear23 (collinear_trans' (is_between_collinear hc'a'd')
      (noncollinear13 (angle_nontrivial_iff_noncollinear.1 h'.2.1)) (is_between_not_eq hc'a'd').2.1),
    rw [segment_symm, segment_symm c' _],
    exact (tri_congr_side h₁).2.2,
    refine congr_segment_add hcad hc'a'd' _ _,
    rw [segment_symm, segment_symm c' _], exact haca'c',
    exact hada'd',
    rw ←angle_eq_same_side b (is_between_same_side_pt.1 hcad).1,
    rw ←angle_eq_same_side b' (is_between_same_side_pt.1 hc'a'd').1,
    rw [angle_symm, angle_symm b' _ _],
    exact (tri_congr_angle h₁).2.2,
  have h₃ : ((Δ d b a) ≅ₜ (Δ d' b' a')),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear12 (noncollinear23 (angle_nontrivial_iff_noncollinear.1 h.2.2)),
    exact noncollinear12 (noncollinear23 (angle_nontrivial_iff_noncollinear.1 h'.2.2)),
    rw [segment_symm, segment_symm d' _], exact (tri_congr_side h₂).2.2,
    rw [segment_symm, segment_symm d' _], exact hada'd',
    rw ←angle_eq_same_side b (is_between_same_side_pt.1 hcad).2,
    rw ←angle_eq_same_side b' (is_between_same_side_pt.1 hc'a'd').2,
    rw [angle_symm, angle_symm b' _ _], exact (tri_congr_angle h₂).2.2,
  rw [angle_symm, angle_symm b' _ _], exact (tri_congr_angle h₃).2.2
end

lemma vertical_angle_congr {a b a' b' o : pts} (haob : noncollinear a o b) :
is_between a o a' → is_between b o b' → (∠ a o b ≅ₐ ∠ a' o b') :=
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
  rw supplementary_symm at h₁, rw angle_symm a' _ _,
  apply supplementary_congr h₁ h₂, rw angle_symm, exact angle_congr_refl _
end

lemma angle_congr_same_side_unique {a b c d : pts} (h : ∠ b a c ≅ₐ ∠b a d)
(hbac : noncollinear b a c) : same_side_line (b-ₗa) c d → same_side_pt a c d :=
begin
  have hab := (noncollinear_not_eq hbac).1.symm,
  intro hcd,
  have hbad : noncollinear b a d,
    rintros ⟨l, hl, hbl, hal, hdl⟩,
    rw two_pt_one_line hl (line_in_lines hab.symm) hab ⟨hal, hbl⟩
      ⟨pt_right_in_line b a, pt_left_in_line b a⟩ at hdl,
    exact (same_side_line_not_in hcd).2 hdl,
  rcases extend_congr_angle (angle_nontrivial_iff_noncollinear.2 (noncollinear13 hbac)) hab
    (by {rw line_symm, exact noncollinear_in12 hbac}) with ⟨p, hpab, hpc, hu⟩,
  have h₁ := hu c hpc (angle_congr_refl _),
  rw line_symm at hcd, rw [angle_symm, angle_symm _ _ d] at h,
  have h₂ := hu d (same_side_line_trans (line_in_lines hab) hpc hcd) h,
  unfold two_pt_ray at h₁ h₂, simp at h₁ h₂,
  cases h₁ with hf h₁, exact absurd hf (noncollinear_not_eq hbac).2.1.symm,
  cases h₂ with hf h₂, exact absurd hf (noncollinear_not_eq hbad).2.1.symm,
  exact same_side_pt_trans (same_side_pt_symm h₁) h₂
end

private lemma congr_angle_add_prep1 {α : angle} {s : segment} (hs : segment_nontrivial s)
{b a c : C.pts} (hab : a ≠ b) (hbac : (∠ b a c) ≅ₐ α) :
∃ b' : C.pts, ((∠ b' a c) ≅ₐ α) ∧ ((a-ₛb') ≅ₛ s) ∧ same_side_pt a b b' :=
begin
  rcases extend_congr_segment hs hab with ⟨b', habb', hs, h⟩, use b',
  have : ∠ c a b = ∠ c a b', from angle_eq_same_side c habb',
  rw [angle_symm, ←this, angle_symm], exact ⟨hbac, segment_congr_symm hs, habb'⟩
end

private lemma congr_angle_add_prep2 {a b c d a' b' c' d' : C.pts}
(hd : inside_angle d (∠ b a c)) (hb'c' : diff_side_line (a'-ₗd') b' c') (ha'd' : a' ≠ d')
(hbad : ∠ b a d ≅ₐ ∠ b' a' d') (hdac : ∠ d a c ≅ₐ ∠ d' a' c') : noncollinear b' a' c' :=
begin
  have hbac := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hd),
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
  exact hb'c'.2.1, exact hb'c'.2.2,
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
      exact (same_side_line_not_in hd.1).2 hdm,
    split, exact this,
    rintros ⟨m, hm, hdm, ham, hxm⟩,
    have hax := (is_between_not_eq hbax).2.2,
    rw two_pt_one_line hm (line_in_lines hab) hax at hdm,
    exact this ⟨(a-ₗb), line_in_lines hab, hdm, pt_left_in_line a b, pt_right_in_line a b⟩,
    exact ⟨ham, hxm⟩, split, exact pt_left_in_line a b,
    rw line_symm, apply ray_in_line b a, left, exact (is_between_same_side_pt.1 hbax).1,
  have hdax : ((∠ d a x) ≅ₐ (∠ d a c)),
    refine angle_congr_trans _ (angle_congr_symm hdac),
    apply supplementary_congr h₂ h₁, rw [angle_symm, angle_symm d' _ _],
    exact hbad,
  rw three_pt_angle_supplementary at h₂,
  have key : same_side_pt a x c,
    refine angle_congr_same_side_unique hdax _ _, exact h₂.2.2,
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
      intro hf, apply (same_side_line_not_in hd.2).2,
      rw two_pt_one_line (line_in_lines hac) (line_in_lines had) hac, exact pt_right_in_line a d,
      exact ⟨pt_left_in_line a c, pt_right_in_line a c⟩, exact ⟨pt_left_in_line a d, hf⟩,
    rw line_symm,
    exact diff_side_line_cancel (line_in_lines had) (diff_side_line_symm hbx) hbc,
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
  have hbac := inside_angle_nontrivial hd, rw angle_nontrivial_iff_noncollinear at hbac,
  have hab := (noncollinear_not_eq hbac).1.symm,
  have hac := (noncollinear_not_eq hbac).2.1,
  have hbc := (noncollinear_not_eq hbac).2.2.symm,
  have hb'a'c' := congr_angle_add_prep2 hd hb'c' ha'd' h₁ h₂,
  have wlog : ∃ p : pts, inside_angle p (∠ b a c) ∧ ∠ b a d = ∠ b a p ∧ ∠ d a c = ∠ p a c ∧ is_between b p c,
    cases crossbar hd with p hp, use p,
    rw inside_three_pt_angle at hd,
    by_cases hdp : d = p,
      rw ←hdp at hp, unfold two_pt_segment at hp, simp at hp, rcases hp.2 with hp | hp | hp,
      rw hp at hd, exact absurd (pt_right_in_line a b) (same_side_line_not_in hd.1).2,
      rw hp at hd, exact absurd (pt_right_in_line a c) (same_side_line_not_in hd.2).2,
      rw ←hdp, exact ⟨inside_three_pt_angle.2 hd, rfl, rfl, hp⟩,
    have had : a ≠ d,
      have := same_side_line_not_in hd.1,
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
        exact (same_side_line_not_in hd.1).2 this,
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
        exact (same_side_line_not_in hd.2).2 this,
      have hax := two_line_one_pt (line_in_lines hac)
        (line_in_lines hdp) this (pt_left_in_line a c) ha hx.1 ((segment_in_line d p) hx.2),
      rw ←hax at hx,
      have : same_side_pt a d p,
        cases hp.1 with h h, exact h, simp at h, exact absurd h.symm hap,
      unfold two_pt_segment at hx, simp at hx, rcases hx.2 with hx | hx | hx,
      exact had hx, exact hap hx,
      rw [is_between_diff_side_pt, ←not_same_side_pt this.2 had.symm hap.symm] at hx,
      exact hx this,
    exact same_side_line_trans (line_in_lines hac) hd.2 this,
    split, exact angle_eq_same_side b hadp,
    split, rw [angle_symm, angle_eq_same_side c hadp, angle_symm],
    unfold two_pt_segment at hp, simp at hp, rcases hp.2 with hpb | hpc | hp,
    rw hpb at hp, have := pt_right_in_line a d,
    rw two_pt_one_line (line_in_lines had) (line_in_lines hab) hab
      ⟨pt_left_in_line a d, (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line a b, pt_right_in_line a b⟩ at this,
    exact absurd this (same_side_line_not_in hd.1).2,
    rw hpc at hp, have := pt_right_in_line a d,
    rw two_pt_one_line (line_in_lines had) (line_in_lines hac) hac
      ⟨pt_left_in_line a d, (ray_in_line a d) hp.1⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at this,
    exact absurd this (same_side_line_not_in hd.2).2,
    exact hp,
  rcases wlog with ⟨p, hp, hp₁, hp₂, hbpc⟩, rw hp₁ at h₁, rw hp₂ at h₂,
  clear hd hp₁ hp₂ d,
  rw inside_three_pt_angle at hp,
  rename [p d, hp hd, hbpc hbdc],
  have had : a ≠ d,
    intro had, rw ←had at hd,
    exact (same_side_line_not_in hd.1).2 (pt_left_in_line a b),
  have ha'b' := (noncollinear_not_eq hb'a'c').1.symm,
  have ha'c' := (noncollinear_not_eq hb'a'c').2.1,
  rcases congr_angle_add_prep1 (segment_nontrivial_iff_neq.2 hab) ha'b' (angle_congr_refl (∠ b' a' d')) with ⟨b'', hb''a'd', ha'b''ab, ha'b'b''⟩,
  rcases congr_angle_add_prep1 (segment_nontrivial_iff_neq.2 had) ha'd' (angle_congr_refl (∠ d' a' b'')) with ⟨d'', hd''a'b', ha'd''ad, ha'd'd''⟩,
  rcases congr_angle_add_prep1 (segment_nontrivial_iff_neq.2 hac) ha'c' (angle_congr_refl (∠ c' a' d')) with ⟨c'', hc''a'd', ha'c''ac, ha'c'c''⟩,
  have ha'b'' := (same_side_pt_not_eq ha'b'b'').2.symm,
  have ha'd'' := (same_side_pt_not_eq ha'd'd'').2.symm,
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
    intro habd, exact (same_side_line_not_in hd.1).2 (collinear_in12 habd hab),
    exact noncollinear23 ha'd''b'',
    exact segment_congr_symm ha'b''ab, exact segment_congr_symm ha'd''ad, exact h₁,
  have hacd : ((Δ a c d) ≅ₜ (Δ a' c'' d'')),
    apply SAS; unfold three_pt_triangle; simp,
    intro hacd, exact (same_side_line_not_in hd.2).2 (collinear_in12 hacd hac),
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
      exact (same_side_line_not_in hd.1).2 hdl,
      rintros ⟨l, hl, hal, hdl, hcl⟩,
      rw two_pt_one_line hl (line_in_lines hac) hac ⟨hal, hcl⟩ ⟨pt_left_in_line a c, pt_right_in_line a c⟩ at hdl,
      exact (same_side_line_not_in hd.2).2 hdl,
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
    apply diff_side_line_symm,
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
  exact same_side_line_trans (line_in_lines ha'd'') hxc' (same_side_line_symm hc'c''),
  have hd''xc'' := angle_congr_same_side_unique key ha'd''x this,
  have hb''d''c'' := is_between_same_side_pt_is_between hb''xd'' hd''xc'',
  have hcab : ((Δ c a b) ≅ₜ (Δ c'' a' b'')),
    apply SAS; unfold three_pt_triangle; simp,
    exact noncollinear13 hbac, exact noncollinear13 hb''a'c'',
    rw [segment_symm, segment_symm c'' _], exact segment_congr_symm ha'c''ac,
    rw is_between_symm at hb''d''c'' hbdc, refine congr_segment_add hbdc hb''d''c'' _ _,
    exact (tri_congr_side hacd).2.2,
    rw [segment_symm, segment_symm d'' _], exact (tri_congr_side habd).2.2,
    rw is_between_same_side_pt at hbdc hb''d''c'',
    rw [angle_eq_same_side a hbdc.2, angle_eq_same_side a' hb''d''c''.2],
    exact (tri_congr_angle hacd).2.1,
  have : (∠ b' a' c') = (∠ b'' a' c''),
    rw [angle_eq_same_side b' ha'c'c'', angle_symm, angle_eq_same_side c'' ha'b'b'', angle_symm],
  split, rotate,
  rw [this, angle_symm, angle_symm b'' _ _], exact (tri_congr_angle hcab).2.1,
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
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'b''.symm _ _ _ _,
    intro hf, exact hb''a'c'' ⟨(b''-ₗa'), line_in_lines ha'b''.symm, pt_left_in_line b'' a', pt_right_in_line b'' a', hf⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c'',
    exact ha'c'.symm,
  have hd'd'' : same_side_line (a'-ₗb'') d' d'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'b''.symm _ _ _ _,
    rw line_symm, intro hf,
    exact ha'd''b'' ⟨(a'-ₗb''), line_in_lines ha'b'', pt_left_in_line a' b'', hf, pt_right_in_line a' b''⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact ha'd'.symm,
  exact same_side_line_trans (line_in_lines ha'b'') (same_side_line_trans (line_in_lines ha'b'') hc'c'' hd''.1)
    (same_side_line_symm hd'd''),
  exact ha'b', exact ⟨pt_left_in_line a' b', pt_right_in_line a' b'⟩,
  split, exact pt_left_in_line a' b'',
  apply ray_in_line a' b'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'',
  rw two_pt_one_line (line_in_lines ha'c') (line_in_lines ha'c''),
  have hb'b'' : same_side_line (a'-ₗc'') b' b'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'c''.symm _ _ _ _,
    intro hf, exact hb''a'c'' ⟨(c''-ₗa'), line_in_lines ha'c''.symm, hf, pt_right_in_line c'' a', pt_left_in_line c'' a'⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'b'b'',
    exact ha'b'.symm,
  have hd'd'' : same_side_line (a'-ₗc'') d' d'',
    rw line_symm, apply same_side_line_symm, refine t_shape_ray ha'c''.symm _ _ _ _,intro hf,
    exact ha'd''c'' ⟨(c''-ₗa'), line_in_lines ha'c''.symm, pt_right_in_line c'' a', hf, pt_left_in_line c'' a'⟩,
    unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'd'd'',
    exact ha'd'.symm,
  exact same_side_line_trans (line_in_lines ha'c'') (same_side_line_trans (line_in_lines ha'c'') hb'b'' hd''.2)
    (same_side_line_symm hd'd''),
  exact ha'c', exact ⟨pt_left_in_line a' c', pt_right_in_line a' c'⟩,
  split, exact pt_left_in_line a' c'',
  apply ray_in_line a' c'', unfold two_pt_ray, simp, right, exact same_side_pt_symm ha'c'c''
end

lemma congr_angle_sub {a b c d a' b' c' d' : C.pts}
(hd : inside_angle d (∠ b a c)) (h : same_side_line (a'-ₗb') d' c')
(ha'b' : a' ≠ b') (h₁ : ∠ b a c ≅ₐ ∠ b' a' c') (h₂ : ∠ b a d ≅ₐ ∠ b' a' d') :
inside_angle d' (∠ b' a' c') ∧ (∠ d a c ≅ₐ ∠ d' a' c') :=
begin
  have hbac := inside_angle_nontrivial hd, rw angle_nontrivial_iff_noncollinear at hbac,
  have hb'd' : b' ≠ d',
    intro hb'd', rw ←hb'd' at h, exact (same_side_line_not_in h).1 (pt_right_in_line a' b'), 
  have ha'd' : a' ≠ d',
    intro hb'd', rw ←hb'd' at h, exact (same_side_line_not_in h).1 (pt_left_in_line a' b'), 
  cases is_between_extend hb'd' with x hb'xd',
  have hb'x : diff_side_line (a'-ₗd') b' x,
    rw is_between_diff_side_pt at hb'xd', replace hb'xd' := diff_side_pt_line hb'xd',
    refine hb'xd'.2.2.2 _ _, exact line_in_lines ha'd',
    split, exact pt_right_in_line a' d',
    have :  b' ∉ ↑(line a' d'),
      intro hf, rw two_pt_one_line (line_in_lines ha'b') (line_in_lines ha'd') ha'b' ⟨pt_left_in_line a' b', pt_right_in_line a' b'⟩ ⟨pt_left_in_line a' d', hf⟩ at h,
      exact (same_side_line_not_in h).1 (pt_right_in_line a' d'),
    split, exact this,
    rcases hb'xd'.1 with ⟨l, hl, hd'l, hb'l, hxl⟩,
    intro hf, rw two_pt_one_line hl (line_in_lines ha'd') hb'xd'.2.2.1 ⟨hd'l, hxl⟩ ⟨pt_right_in_line a' d', hf⟩ at hb'l,
    exact this hb'l,
  have hdac : angle_nontrivial (∠ d a c),
    rw angle_nontrivial_iff_noncollinear, intro hdac,
    exact (same_side_line_not_in (inside_three_pt_angle.1 hd).2).2 (collinear_in23 hdac (noncollinear_not_eq hbac).2.1),
  rcases extend_congr_angle hdac ha'd' hb'x.2.2 with ⟨c'', hdac, hc''x, -⟩,
  rw angle_symm c'' _ _ at hdac,
  have hb'c'' : diff_side_line (a'-ₗd') b' c'',
    apply diff_side_same_side_line (line_in_lines ha'd') hb'x,
    exact same_side_line_symm hc''x,
  have key := congr_angle_add hd hb'c'' ha'd' h₂ hdac,
  have hc'c'' : same_side_pt a' c' c'',
    apply same_side_pt_symm,
    have hb'a'c'' := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial key.1),
    rw inside_three_pt_angle at key,
    refine angle_congr_same_side_unique (angle_congr_symm (angle_congr_trans (angle_congr_symm h₁) key.2)) _ _,
    exact hb'a'c'',
    rw line_symm, exact same_side_line_trans (line_in_lines ha'b') key.1.1 h,
  rw [angle_eq_same_side d' hc'c'', angle_eq_same_side b' hc'c''],
  exact ⟨key.1, hdac⟩
end

/--Angle `α` is less than `β` if a part of it is congruent to `β`. That is,
there exists a point inside `α` with one ray of `α` forms an angle congruent to `β`-/
def angle_lt (α β : angle) : Prop :=
 ∃ a b p : C.pts, β = (∠ a β.vertex b) ∧ inside_angle p (∠ a β.vertex b)
  ∧ ((∠ a β.vertex p) ≅ₐ α)

notation a`<ₐ`b := angle_lt a b

lemma three_pt_angle_lt {a o b : C.pts} {α : angle} :
(α <ₐ (∠ a o b)) ↔ ∃ p : C.pts, inside_angle p (∠ a o b) ∧ ((∠ a o p) ≅ₐ α):=
begin
  split,
  rintros ⟨a', b', p, haoba'ob', hp, ha'op⟩,
  rw three_pt_angle_vertex at haoba'ob' hp ha'op,
  have ha'ob' := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hp),
  have haob : noncollinear a o b,
    rw [←angle_nontrivial_iff_noncollinear, haoba'ob'],
    exact inside_angle_nontrivial hp,
  have hoa := (noncollinear_not_eq haob).1.symm,
  cases ((three_pt_angle_eq_iff ha'ob').1 haoba'ob'.symm).2,
  have haopa'op : (∠ a o p) = (∠ a' o p),
    rw [angle_symm, angle_symm a' _ _ ],
    refine angle_eq_same_side _ _,
    exact same_side_pt_symm h.1,
  use p, rw [haoba'ob', haopa'op],
  exact ⟨hp, ha'op⟩,
  rcases extend_congr_angle (inside_angle_nontrivial' hp).1 hoa (noncollinear_in12 (noncollinear12 haob))
    with ⟨q, ha'opqoa, hqb, -⟩,
  use q, split,
  refine (congr_angle_sub hp hqb _ _ _).1,
  exact (same_side_pt_not_eq h.2).2.symm,
  rw haoba'ob', exact angle_congr_refl _,
  rw [angle_symm, angle_symm a o q], exact ha'opqoa,
  rw angle_symm, rw angle_symm at ha'op,
  exact angle_congr_trans (angle_congr_symm ha'opqoa) ha'op,
  rintros ⟨p, hp, haopα⟩,
  use [a, b, p],
  rw three_pt_angle_vertex, exact ⟨rfl, hp, haopα⟩
end

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
  rw angle_nontrivial_iff_noncollinear at h,
  rcases extend_congr_angle (inside_angle_nontrivial' hpin).1 (noncollinear_not_eq h).1.symm
    (noncollinear_in12 (noncollinear12 h)) with ⟨q, hq, hqb₂, -⟩,
  rw three_pt_angle_lt,
  rw angle_symm q _ _ at hq,
  use q, split,
  refine (congr_angle_sub hpin hqb₂ _ _ _).1,
  exact (noncollinear_not_eq h).1.symm,
  exact hαβ,
  rw angle_symm, exact hq,
  rw angle_symm at hq, exact angle_congr_trans (angle_congr_symm hq) hp
end

lemma inside_angle_trans {a b c d e : C.pts} :
inside_angle d (∠ b a c) → inside_angle e (∠ b a d) → inside_angle e (∠ b a c) :=
begin
  intros hd he,
  have hbac := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hd),
  have hbad := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial he),
  rw inside_three_pt_angle at *,
  have hac := (noncollinear_not_eq hbac).2.1,
  have hab := (noncollinear_not_eq hbac).1.symm,
  have hbc := (noncollinear_not_eq hbac).2.2.symm,
  have hbd := (noncollinear_not_eq hbad).2.2.symm,
  have had := (noncollinear_not_eq hbad).2.1,
  have hae : a ≠ e,
    intro hae, rw ←hae at he,
    exact (same_side_line_not_in he.1).2 (pt_left_in_line a b),
  have hade : noncollinear a d e,
    rintros ⟨l, hl, hal, hdl, hel⟩,
    rw two_pt_one_line hl (line_in_lines had) had ⟨hal, hdl⟩ ⟨pt_left_in_line a d, pt_right_in_line a d⟩ at hel,
    exact (same_side_line_not_in he.2).2 hel,
  split, exact (same_side_line_trans (line_in_lines hab) hd.1 he.1),
  cases crossbar (inside_three_pt_angle.2 hd) with d' hd',
  have : inside_angle e (∠ b a d'),
    have : same_side_pt a d d',
      unfold two_pt_ray at hd',
      cases hd'.1, exact h,
      simp at h, rw h at hd',
      exfalso, apply hbac,
      exact ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, (segment_in_line b c) hd'.2, pt_right_in_line b c⟩,
    rw [←angle_eq_same_side b this, inside_three_pt_angle], exact he,
  have hbd' : b ≠ d',
    intro hbd', rw ←hbd' at hd',
    exact hbad ⟨(a-ₗd), line_in_lines had, (ray_in_line a d) hd'.1, pt_left_in_line a d, pt_right_in_line a d⟩,
  cases crossbar this with e' he',
  have had' : a ≠ d',
    intro hf, rw ←hf at hd',
    exact hbac ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, (segment_in_line b c) hd'.2, pt_right_in_line b c⟩,
  have he'a : e' ≠ a,
    intro he'a, rw he'a at he'a, rw he'a at he',
    have : a ∈ (b-ₗc),
      rw two_pt_one_line (line_in_lines hbc) (line_in_lines hbd') hbd',
      exact (segment_in_line b d') he'.2,
      exact ⟨pt_left_in_line b c, (segment_in_line b c) hd'.2⟩,
      exact ⟨pt_left_in_line b d', pt_right_in_line b d'⟩,
    exfalso, apply hbac,
    exact ⟨(b-ₗc), line_in_lines hbc, pt_left_in_line b c, this, pt_right_in_line b c⟩,
  have hdd' : same_side_line (a-ₗc) d d',
    rw line_symm, refine t_shape_ray _ _ _ _ _,
    exact hac.symm,
    rw line_symm, exact (same_side_line_not_in hd.2).2,
    exact hd'.1, exact had'.symm,
  have hbd'c : is_between b d' c,
    cases hd'.2, exact h,
    cases h, exact absurd h hbd'.symm,
    simp at h, rw h at hd', rw h at hdd',
    exact absurd (pt_right_in_line a c) (same_side_line_not_in hdd').2,
  have hbe'd' : is_between b e' d',
    cases he'.2, exact h,
    cases h, rw h at he',
    rw two_pt_one_line (line_in_lines hab) (line_in_lines hae) hab ⟨pt_left_in_line a b, pt_right_in_line a b⟩ ⟨pt_left_in_line a e, (ray_in_line a e) he'.1⟩ at he,
    exact absurd (pt_right_in_line a e) (same_side_line_not_in he.1).2,
    simp at h, rw h at he',
    have := pt_right_in_line a e,
    rw two_pt_one_line (line_in_lines hae) (line_in_lines had) had' at this,
    exfalso, apply hade,
    exact ⟨(a-ₗd), line_in_lines had, pt_left_in_line a d, pt_right_in_line a d, this⟩,
    exact ⟨pt_left_in_line a e, (ray_in_line a e) he'.1⟩,
    exact ⟨pt_left_in_line a d, (ray_in_line a d) hd'.1⟩,
  have hee' : same_side_line (a-ₗc) e e',
    rw line_symm, apply same_side_line_symm,
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
      exact (same_side_line_not_in hdd').2 (pt_right_in_line a d'),
    have hb := pt_left_in_line b c,
    rw two_pt_one_line (line_in_lines hbc) (line_in_lines hac) hce' ⟨pt_right_in_line b c, this⟩ ⟨pt_right_in_line a c, hf⟩ at hb,
    exact hbac ⟨(a-ₗc), line_in_lines hac, hb, pt_left_in_line a c, pt_right_in_line a c⟩,
    cases he'.1 with he' hf,
    left, exact same_side_pt_symm he',
    exact absurd hf he'a,
    intro hea, rw [hea, ray_singleton] at he', exact he'a he'.1,
  suffices : same_side_line (a-ₗc) d' e',
    from same_side_line_trans (line_in_lines hac) (same_side_line_trans (line_in_lines hac)
      (same_side_line_trans (line_in_lines hac) hd.2 hdd') this)
      (same_side_line_symm hee'),
  refine t_shape_ray hac _ _ _ _,
  exact (same_side_line_not_in hdd').2,
  rw is_between_symm at hbd'c hbe'd',
  left, simp, exact (is_between_same_side_pt.1 (is_between_trans' hbd'c hbe'd').1).1,
  intro hf, rw hf at hee', exact (same_side_line_not_in hee').2 (pt_right_in_line a c)
end

lemma inside_angle_trans' {a o b c d : C.pts} (hboc : is_between b o c) :
inside_angle d (∠ a o b) → inside_angle a (∠ d o c) :=
begin
  intro hd, have haob := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hd),
  rw inside_three_pt_angle,
  have hod : o ≠ d,
    intro hod, rw [hod, inside_three_pt_angle] at hd,
    exact (same_side_line_not_in hd.1).2 (pt_left_in_line d a),
  have hoc := (is_between_not_eq hboc).2.2,
  have hob := (is_between_not_eq hboc).1.symm,
  have := two_pt_one_line (line_in_lines hoc) (line_in_lines hob) hob
    ⟨pt_left_in_line o c, collinear_in23 (is_between_collinear hboc) hoc⟩ ⟨pt_left_in_line o b, pt_right_in_line o b⟩,
  rw inside_three_pt_angle at hd,
  have hoa := (noncollinear_not_eq haob).1.symm,
  split,
  have h₁ : diff_side_line (o-ₗd) c b,
    rw is_between_diff_side_pt at hboc, apply diff_side_line_symm,
    apply (diff_side_pt_line hboc).2.2.2 (line_in_lines hod),
    split, exact pt_left_in_line o d,
    split, intro hf, apply (same_side_line_not_in hd.2).2,
    apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d, hf, pt_right_in_line o d⟩,
    exact hob,
    intro hf, apply (same_side_line_not_in hd.2).2,
    rw ←this, apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d, hf, pt_right_in_line o d⟩,
    exact hoc,
  have h₂ : diff_side_line (o-ₗd) b a,
    cases crossbar (inside_three_pt_angle.2 hd) with x hx,
    use x, rw segment_symm, exact ⟨(ray_in_line o d) hx.1, hx.2⟩,
    split, intro hf, apply (same_side_line_not_in hd.2).2,
    apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d, hf, pt_right_in_line o d⟩,
    exact hob, intro hf, apply (same_side_line_not_in hd.1).2,
    apply collinear_in12, exact ⟨(o-ₗd), line_in_lines hod, pt_left_in_line o d, hf, pt_right_in_line o d⟩,
    exact hoa,
  exact diff_side_line_cancel (line_in_lines hod) h₁ h₂,
  rw this,
  exact same_side_line_symm hd.2
end

lemma angle_lt_trans {α β γ : angle} :
angle_nontrivial α → (α <ₐ β) → (β <ₐ γ) → (α <ₐ γ) :=
begin
  intros hα hαβ hβγ,
  rcases angle_three_pt β with ⟨a₂, b₂, hβ⟩,
  rcases angle_three_pt γ with ⟨a₃, b₃, hγ⟩,
  rw hγ, rw hβ at hαβ, rw [hβ, hγ] at hβγ,
  set o₂ := β.vertex, set o₃ := γ.vertex,
  rcases three_pt_angle_lt.1 hαβ with ⟨p, hpin, hp⟩,
  rcases three_pt_angle_lt.1 hβγ with ⟨q, hqin, hq⟩,
  have ha₃o₃b₃ := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hqin),
  rcases extend_congr_angle hα (noncollinear_not_eq ha₃o₃b₃).1.symm
    (noncollinear_in23 (angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial' hqin).1)) with ⟨x, hx, hxq, -⟩,
  rw three_pt_angle_lt,
  use x, split,
  apply inside_angle_trans hqin,
  refine (congr_angle_sub hpin hxq _ _ _).1,
  exact (noncollinear_not_eq (angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hqin))).1.symm,
  exact angle_congr_symm hq,
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
    intro hox, rw ←hox at h₂, exact (same_side_line_not_in h₂).1 (pt_left_in_line o a),
  have hab : a ≠ b,
    intro hab, rw hab at h₁, exact h₁.2.1 (pt_right_in_line o b),
  have hob : o ≠ b,
    intro hob, rw hob at h₂, exact (same_side_line_not_in h₂).2 (pt_left_in_line b a),
  have hax : a ≠ x,
    intro hax, rw ←hax at h₂, exact (same_side_line_not_in h₂).1 (pt_right_in_line o a),
  cases h₁.1 with b' hb',
  have hab' : a ≠ b',
    intro hab', rw ←hab' at hb', exact h₁.2.1 hb'.1,
  have hob' : o ≠ b',
    intro hob', rw ←hob' at hb',
    rw two_pt_one_line (line_in_lines hoa) (line_in_lines hax) hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨(segment_in_line a x) hb'.2, pt_left_in_line a x⟩ at h₂,
    exact (same_side_line_not_in h₂).1 (pt_right_in_line a x),
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
    have := (diff_side_pt_line hobb').2.2.2 (line_in_lines hoa) ⟨(pt_left_in_line o a), (same_side_line_not_in h₂).2, hb'oa⟩,
    have hxoa : x ∉ (o-ₗa),
      intro hxoa, rw two_pt_one_line (line_in_lines hoa) (line_in_lines hox) hox ⟨pt_left_in_line o a, hxoa⟩ ⟨pt_left_in_line o x, pt_right_in_line o x⟩ at h₂,
      exact (same_side_line_not_in h₂).1 (pt_right_in_line o x),
    exfalso, apply (not_diff_side_line hxoa ((same_side_line_not_in h₂).2)).2 h₂,
    apply diff_side_line_symm ,
    apply diff_side_same_side_line (line_in_lines hoa) this,
    apply same_side_line_symm,
    refine t_shape_segment hoa hxoa _ _ _, exact hb'.2, exact hab'.symm,
    exact hob'.symm,
  apply same_side_line_symm, apply same_side_line_trans (line_in_lines hox) this,
  cases hb'.2 with hab'x hf,
  simp at hab'x, rw is_between_same_side_pt at hab'x,
  apply same_side_line_symm,
  apply (same_side_pt_line hab'x.2).2.2.2 (line_in_lines hox) _,
  split, exact pt_right_in_line o x,
  split,
  intro haox, rw two_pt_one_line (line_in_lines hoa) (line_in_lines hox) hoa ⟨pt_left_in_line o a, pt_right_in_line o a⟩ ⟨pt_left_in_line o x, haox⟩ at h₂,
  exact (same_side_line_not_in h₂).1 (pt_right_in_line o x),
  exact (same_side_line_not_in this).2,
  cases hf with hf hf,
  exact absurd hf.symm hab',
  simp at hf, rw hf at this, exact absurd (pt_right_in_line o x) (same_side_line_not_in this).2,
end

lemma angle_tri {α β : angle} (ha'o'b' : angle_nontrivial α) (haob : angle_nontrivial β) :
((α <ₐ β) ∨ (α ≅ₐ β) ∨ (β <ₐ α))
∧ ¬((α <ₐ β) ∧ (α ≅ₐ β)) ∧ ¬((α <ₐ β) ∧ (β <ₐ α)) ∧ ¬(((α ≅ₐ β) ∧ (β <ₐ α))) :=
begin
  rcases angle_three_pt β with ⟨a, b, hβ⟩,
  rw [hβ, angle_nontrivial_iff_noncollinear] at haob, set o := β.vertex,
  have hao := (noncollinear_not_eq haob).1,
  have hbo := (noncollinear_not_eq haob).2.1.symm,
  rcases extend_congr_angle ha'o'b' hao.symm (noncollinear_in12 (noncollinear12 haob)) with ⟨x, hx, hlxb, hu⟩,
  have hxo : x ≠ o,
    intro hxo, rw hxo at hlxb,
    exact (same_side_line_not_in hlxb).1 (pt_left_in_line o a),
  have h₁ : same_side_line (o-ₗb) x a ↔ (α <ₐ β),
    rw hβ, split; rw three_pt_angle_lt, intro h₁,
    use x, split,
    rw inside_three_pt_angle,
    exact ⟨same_side_line_symm hlxb, same_side_line_symm h₁⟩,
    rw angle_symm, exact angle_congr_symm hx,
    rintros ⟨y, hyin, hy⟩, rw inside_three_pt_angle at hyin, rw angle_symm at hy,
    specialize hu y (same_side_line_trans (line_in_lines hao.symm) hlxb hyin.1) (angle_congr_symm hy),
    refine same_side_line_trans (line_in_lines hbo.symm) _ (same_side_line_symm hyin.2),
    rw line_symm, refine t_shape_ray hbo _ _ _ _,
    intro hf, have := (collinear_trans ⟨(b-ₗo), line_in_lines hbo, pt_right_in_line b o, hf, pt_left_in_line b o⟩ (in_ray_collinear hu) hxo.symm),
    exact (same_side_line_not_in hyin.2).2 (collinear_in12 this hbo.symm),
    exact hu, intro hyo, rw hyo at hyin, exact (same_side_line_not_in hyin.2).2 (pt_left_in_line o b),
  have h₂ : x ∈ (o-ₗb) ↔ (α ≅ₐ β),
    rw hβ, split; intro h₂,
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
      rcases (diff_side_pt_collinear h) with ⟨l, hl, hol, hxl, hbl⟩,
      rw two_pt_one_line hl (line_in_lines hao.symm) hxo ⟨hxl, hol⟩ ⟨hf, pt_left_in_line o a⟩ at hbl,
      exact this hbl, exact this,
      exact (same_side_line_not_in hlxb).1,
      exact (same_side_line_not_in hlxb).2,
    rw ←this, exact hx,
    rw angle_symm at h₂, specialize hu b hlxb h₂,
    exact collinear_in13 (in_ray_collinear hu) hbo.symm,
  have h₃ : diff_side_line (o-ₗb) x a ↔ (β <ₐ α),
    split; intro h₃,
    apply (angle_lt_congr (angle_congr_symm hx)).2 ha'o'b', rw angle_symm,
    rw three_pt_angle_lt, use b,
    split,
    rw inside_three_pt_angle, split, exact hlxb,
    exact diff_same_side_line (diff_side_line_symm h₃) hlxb,
    rw hβ, exact angle_congr_refl _,
    have : angle_nontrivial (∠ x o a),
      rw angle_nontrivial_iff_noncollinear,
      intro hxoa, exact (same_side_line_not_in hlxb).1 (collinear_in23 hxoa hao.symm),
    have := (angle_lt_congr hx).2 this h₃, rw [angle_symm, three_pt_angle_lt] at this,
    rcases this with ⟨p, hpin, hp⟩, rw hβ at hp,
    have hopb : same_side_pt o p b,
      rw inside_three_pt_angle at hpin,
      refine angle_congr_same_side_unique hp _ _,
      intro haop, rw line_symm at hpin, exact (same_side_line_not_in hpin.1).2 (collinear_in12 haop hao),
      rw line_symm, exact same_side_line_trans (line_in_lines hao.symm) (same_side_line_symm hpin.1) hlxb,
    exact diff_side_line_symm (inside_angle_diff_side_line (ray_inside_angle hpin hopb)),
  rw [←h₁, ←h₂, ←h₃],
  split, by_cases x ∈ (o-ₗb),
  right, left, exact h,
  cases (plane_separation h (noncollinear_in23 haob)).1 with h h,
  left, exact h, right, right, exact h,
  split, intro hf,
  exact (same_side_line_not_in hf.1).1 hf.2,
  split, intro hf, rw ←not_diff_side_line at hf, exact hf.1 hf.2,
  exact hf.2.2.1, exact hf.2.2.2,
  intro hf, exact hf.2.2.1 hf.1
end

/--An angle is a right angle if it is congruent to its supplementary angle. -/
def is_right_angle (α : angle) : Prop :=
angle_nontrivial α ∧ ∀ β : angle, supplementary α β → (α ≅ₐ β)

lemma supplementary_exist {α : angle} (haob : angle_nontrivial α) :
∃ β : angle, supplementary α β :=
begin
  rcases angle_three_pt α with ⟨a, b, h⟩,
  rw h, rw [h, angle_nontrivial_iff_noncollinear] at haob, set o := α.vertex,
  have hob := (noncollinear_not_eq haob).2.1,
  cases is_between_extend hob.symm with c hboc,
  have hoc := (is_between_not_eq hboc).2.2,
  use (∠ a o c), rw three_pt_angle_supplementary,
  split, exact hboc,
  split, exact haob,
  exact noncollinear132 (collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear123 haob) hoc),
end

lemma right_angle_congr {α β : angle} :
(α ≅ₐ β) → is_right_angle α → angle_nontrivial β → is_right_angle β :=
begin
  intros hαβ hα hβ,
  split, exact hβ,
  intros β' hββ',
  cases supplementary_exist hα.1 with α' hαα',
  exact angle_congr_trans (angle_congr_trans (angle_congr_symm hαβ) (hα.2 α' hαα')) (supplementary_congr hαα' hββ' hαβ),
end

lemma three_pt_angle_is_right_angle {a o b c : pts} (hboc : is_between b o c) :
is_right_angle (∠ a o b) ↔ ((∠ a o b) ≅ₐ (∠ a o c)) ∧ angle_nontrivial (∠ a o b) :=
begin
  unfold is_right_angle,
  split; intro h, split,
  apply h.2, rw three_pt_angle_supplementary,
  have haob := angle_nontrivial_iff_noncollinear.1 h.1,
  split, exact hboc, split, exact haob,
  exact noncollinear132 (collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear12 (noncollinear13 haob)) (is_between_not_eq hboc).2.2),
  exact h.1,
  split, exact h.2,
  intros β hβ, rcases hβ.1 with ⟨o', a', b', c', haoba'ob', ha'oc', hb'oc'⟩,
  have haob := angle_nontrivial_iff_noncollinear.1 h.2,
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

lemma all_right_angle_congr {α β : angle}
(hα : is_right_angle α) (hβ : is_right_angle β) : α ≅ₐ β :=
begin
  have wlog : ∀ α β : angle, is_right_angle α → is_right_angle β → (α <ₐ β) → false,
    intros x y hx hy hxy,
    rcases angle_three_pt y with ⟨a, b, haob⟩,
    set o := y.vertex, rw haob at hxy,
    rw haob at hy,
    have hbo := (noncollinear_not_eq (angle_nontrivial_iff_noncollinear.1 hy.1)).2.1.symm,
    rw [angle_symm, three_pt_angle_lt] at hxy,
    rcases hxy with ⟨p, hpin, hp⟩,
    have hboa := angle_nontrivial_iff_noncollinear.1 (inside_angle_nontrivial hpin),
    rw inside_three_pt_angle at hpin,
    cases is_between_extend hbo with c hboc,
    have hco := (is_between_not_eq hboc).2.2.symm,
    rw three_pt_angle_is_right_angle hboc at hy,
    have h₁ : supplementary (∠ p o b) (∠ p o c),
      rw three_pt_angle_supplementary,
      split, exact hboc,
      have : noncollinear p o b,
        intro hpob,
        exact (same_side_line_not_in hpin.1).2 (collinear_in23 hpob hbo.symm),
      split, exact this,
      exact noncollinear132 (collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear123 this) hco.symm),
    have h₂ : supplementary (∠ a o b) (∠ a o c),
      rw three_pt_angle_supplementary,
      split, exact hboc,
      split, exact noncollinear13 hboa,
      exact noncollinear132 ((collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear12 hboa)) hco.symm),
    have hf₁ : ((∠ p o c) <ₐ (∠ a o c)),
      have hbop : noncollinear b o p,
        intro hbop, rw line_symm at hpin,
        exact (same_side_line_not_in hpin.1).2 (collinear_in12 hbop hbo),
      replace hbop := right_angle_congr (angle_congr_symm hp) hx (angle_nontrivial_iff_noncollinear.2 hbop),
      rw angle_symm at hbop,
      have : ((∠ p o b) <ₐ (∠ a o b)),
        rw [angle_symm, angle_symm a o b, three_pt_angle_lt],
        exact ⟨p, inside_three_pt_angle.2 hpin, angle_congr_refl _⟩,
      replace h₁ := hbop.2 _ h₁,
      replace h₂ := hy.1,
      apply (angle_lt_congr h₁).1, apply (angle_lt_congr h₂).2,
      rw angle_nontrivial_iff_noncollinear,
      exact noncollinear132 (collinear_trans' (collinear12 (is_between_collinear hboc)) (noncollinear12 hboa) hco.symm),
      exact this,
    have hf₂ : ((∠ a o c) <ₐ (∠ p o c)),
      rw [angle_symm, angle_symm p o c, three_pt_angle_lt],
      use a, split,
      rw angle_symm, exact inside_angle_trans' hboc (by {rw angle_symm, exact inside_three_pt_angle.2 hpin}),
      exact angle_congr_refl _,
    exact (angle_tri h₁.2.2 h₂.2.2).2.2.1 ⟨hf₁, hf₂⟩,
  rcases (angle_tri hα.1 hβ.1).1 with h | h | h,
  exfalso, exact wlog α β hα hβ h,
  exact h,
  exfalso, exact wlog β α hβ hα h
end

theorem isoceles {a b c : C.pts} (habc : noncollinear a b c) :
((a-ₛb) ≅ₛ (a-ₛc)) → ((∠ a b c) ≅ₐ (∠ a c b)) :=
begin
  intro habac,
  have hab := (noncollinear_not_eq habc).1,
  have hac := (noncollinear_not_eq habc).2.2.symm,
  cases is_between_extend hab with d habd,
  cases is_between_extend hac with x hacx,
  have hbd := (is_between_not_eq habd).2.2,
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 hbd) (is_between_not_eq hacx).2.2 with ⟨e, hcxe, hbdce, -⟩,
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
    rw [angle_symm, angle_symm e _ _],
    rw angle_eq_same_side b (is_between_same_side_pt.1 hace).1, exact angle_congr_refl _,
  have hce := (is_between_not_eq hace).2.2,
  have hdbc := collinear_trans' (collinear132 (is_between_collinear habd)) (noncollinear12 hadc) hbd.symm,
  have hecb := collinear_trans' (collinear132 (is_between_collinear hace)) (noncollinear12 haeb) hce.symm,
  have hdbcecb : ((Δ d b c) ≅ₜ (Δ e c b)),
    apply SAS; unfold three_pt_triangle; simp,
    exact hdbc, exact hecb,
    rw [segment_symm, segment_symm e _], exact hbdce,
    exact (tri_congr_side hadcaeb).2.2,
    rw [angle_symm, ←angle_eq_same_side c (is_between_same_side_pt.1 habd).2],
    rw [angle_symm _ e _, ←angle_eq_same_side b (is_between_same_side_pt.1 hace).2],
    rw [angle_symm, angle_symm b _ _],
    exact (tri_congr_angle hadcaeb).2.1,
  have key := (tri_congr_angle hdbcecb).2.1,
  rw [angle_symm, angle_symm e _ _] at key,
  rw [angle_symm, angle_symm a _ _],
  refine supplementary_congr _ _ key;
  rw three_pt_angle_supplementary,
  rw is_between_symm at habd,
  exact ⟨habd, noncollinear13 hdbc, noncollinear13 habc⟩,
    rw is_between_symm at hace,
  exact ⟨hace, noncollinear13 hecb, noncollinear123 habc⟩
end

theorem SSS {ABC DEF : triangle} (habc : noncollinear ABC.v1 ABC.v2 ABC.v3)
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
  have : x ∉ (a-ₗc),
    exact noncollinear_in13 (collinear_trans' (collinear12 (is_between_collinear hbax)) habc (is_between_not_eq hbax).2.2),
  rcases extend_congr_angle (angle_nontrivial_iff_noncollinear.2 (noncollinear12 ha'b'c')) hac this with ⟨y, hy, hacyx, -⟩,
  have hay : a ≠ y,
    intro hay, rw ←hay at hacyx,
    exact (same_side_line_not_in hacyx).1 (pt_left_in_line a c),
  rcases extend_congr_segment (segment_nontrivial_iff_neq.2 (noncollinear_not_eq ha'b'c').1) hay
    with ⟨d, hayd, ha'b'ad, -⟩,
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
      rw line_symm, exact (same_side_line_not_in hacyx).1,
      left, exact hayd, exact had.symm,
    exact diff_side_same_side_line (line_in_lines hac) (diff_side_same_side_line (line_in_lines hac) h₁
      (same_side_line_symm hacyx)) h₂,
  have hadc : noncollinear a d c,
    intro hadc, exact hacbd.2.2 ((collinear_in13 hadc) hac),
  have hadca'b'c' : ((Δ a d c) ≅ₜ (Δ a' b' c')),
    apply SAS; unfold three_pt_triangle; simp,
    exact hadc, exact ha'b'c',
    exact segment_congr_symm ha'b'ad, exact haca'c',
    have : ∠ y a c = ∠ d a c,
      rw [angle_symm, angle_symm d _ _],
      exact angle_eq_same_side c hayd,
    rw this at hy, exact angle_congr_symm hy,
  refine tri_congr_trans _ hadca'b'c',
  apply tri_congr12, rw [←ha, ←hb, ←hc],
  apply SAS; unfold three_pt_triangle; simp,
  exact noncollinear12 habc, exact noncollinear12 hadc,
  rw segment_symm at haba'b', rw segment_symm d a,
  exact segment_congr_trans haba'b' (segment_congr_symm (tri_congr_side hadca'b'c').1),
  exact segment_congr_trans hbcb'c' (segment_congr_symm (tri_congr_side hadca'b'c').2.2),
  have had := (noncollinear_not_eq hadc).1,
  have hcd := (noncollinear_not_eq hadc).2.1.symm,
  have h₁ : ((c-ₛb) ≅ₛ (c-ₛd)),
    rw segment_symm, apply segment_congr_trans hbcb'c',
    rw segment_symm c d, exact segment_congr_symm (tri_congr_side hadca'b'c').2.2,
  have h₂ : ((a-ₛb) ≅ₛ (a-ₛd)),
    apply segment_congr_trans haba'b', exact segment_congr_symm (tri_congr_side hadca'b'c').1,
  have hbd : b ≠ d,
    intro hbd, rw hbd at hacbd, rw ←not_same_side_line at hacbd,
    exact hacbd (same_side_line_refl (noncollinear_in13 hadc)),
    exact noncollinear_in13 hadc, exact noncollinear_in13 hadc,
  cases hacbd.1 with o ho,
  have hbod : is_between b o d,
    cases ho.2, exact h,
    cases h, rw h at ho, exact absurd ho.1 (noncollinear_in13 habc),
    simp at h, rw h at ho, exact absurd ho.1 (noncollinear_in13 hadc),
  by_cases hao : a = o,
    rw ←hao at ho, rw ←hao at hbod,
    have hbad : is_between b a d,
      cases ho.2, exact h, cases h, exact absurd h hab, exact absurd h had,
    rw is_between_same_side_pt at hbad,
    rw [angle_symm, angle_eq_same_side c hbad.1],
    rw [angle_symm a _ _, ←angle_eq_same_side c hbad.2],
    apply isoceles,
    intro hcbd, exact (noncollinear12 hadc) ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 hcbd)) hbd.symm),
    exact h₁,
  by_cases hco : c = o,
    rw ←hco at ho, rw ←hco at hbod,
    have hbad : is_between b c d,
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
    rw [angle_symm o d c ,←angle_eq_same_side c (is_between_same_side_pt.1 hbod).2],
    apply isoceles,
    intro hcbd, exact (noncollinear132 hocd) ((collinear_trans (collinear132 (is_between_collinear hbod)) (collinear13 hcbd)) hbd.symm),
    exact h₁,
  have H₂ : ((∠ o b a) ≅ₐ (∠ o d a)),
    rw [angle_symm, angle_eq_same_side a (is_between_same_side_pt.1 hbod).1],
    rw [angle_symm o d a ,←angle_eq_same_side a (is_between_same_side_pt.1 hbod).2],
    apply isoceles,
    intro habd, exact (noncollinear13 hoab) (collinear_trans (collinear123 habd) (collinear23 (is_between_collinear hbod)) hbd),
    exact h₂,
  rcases (collinear_between hoac).1 (ne.symm hao) (ne.symm hco) hac with h | h | h,
  have ha₁ : inside_angle a (∠ o b c),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hbo _ _ _ _,
    rw line_symm, exact noncollinear_in12 hobc,
    left, exact h, exact hao,
    refine t_shape_segment hbc _ _ _ _,
    exact noncollinear_in23 hobc, left, rw is_between_symm at h, exact h,
    exact hac,
  have ha₂ : same_side_line (d-ₗo) a c,
    apply same_side_line_symm, refine t_shape_segment hdo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hocd,
    left, exact h, exact hao,
  exact (congr_angle_sub ha₁ ha₂ hdo H₁ H₂).2,
  have hc₁ : inside_angle c (∠ o b a),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hbo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hoab,
    left, exact h, exact hco,
    refine t_shape_segment hab.symm _ _ _ _,
    rw line_symm, exact noncollinear_in23 hoab, left, rw is_between_symm at h, exact h,
    exact hac.symm,
  have hc₂ : same_side_line (d-ₗo) c a,
    apply same_side_line_symm, refine t_shape_segment hdo _ _ _ _,
    rw line_symm, exact noncollinear_in13 hoad,
    left, exact h, exact hco,
  rw [angle_symm, angle_symm a],
  exact (congr_angle_sub hc₁ hc₂ hdo H₂ H₁).2,
  have ho₁ : inside_angle o (∠ a b c),
    rw inside_three_pt_angle,
    split, refine t_shape_segment hab.symm _ _ _ _,
    rw line_symm, exact noncollinear_in12 habc,
    left, exact h,
    exact ne.symm hao,
    refine t_shape_segment hbc _ _ _ _,
    exact noncollinear_in23 habc,
    left, rw is_between_symm at h, exact h,
    exact ne.symm hco,
  have ho₂ : diff_side_line (d-ₗo) a c,
    use o, exact ⟨pt_right_in_line d o, by {left, exact h}⟩,
    split, rw line_symm, exact noncollinear_in13 hoad,
    rw line_symm, exact noncollinear_in13 hocd,
  refine (congr_angle_add ho₁ ho₂ hdo _ _).2,
  rw [angle_symm, angle_symm a _ _], exact H₂,
  exact H₁
end

-- this is a third file
end hilbert_plane_API

#lint
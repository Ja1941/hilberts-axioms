import set_theory.zfc

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

open incidence_geometry

variable [I : incidence_geometry]

include I

/--A line is a set of points defined given two points.
If two points are distinct, it is given by I1. Otherwise, it is defined as a singleton, but
this almost never occurs later.
-/
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

lemma two_pt_line_unique {a b : pts} (hab : a ≠ b)
{l : set pts} (hl : l ∈ lines) (ha : a ∈ l) (hb : b ∈ l) : l = (a-ₗb) :=
begin
  rcases (I1 hab) with ⟨n, hn, -, -, key⟩,
  rw [key l hl ha hb,
      key (a-ₗb) (line_in_lines hab) (pt_left_in_line a b) (pt_right_in_line a b)]
end

lemma two_pt_on_one_line {l : set pts} (hl : l ∈ lines) :
∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l := I2 l hl

-- this would be much better as a ∈ l → b ∈ l → a ∈ m → ... (all before the colon!)
lemma two_pt_one_line {l m : set pts} (hl : l ∈ lines) (hm : m ∈ lines)
{a b : pts} (hab : a ≠ b) : a ∈ l ∧ b ∈ l → a ∈ m ∧ b ∈ m → l = m :=
λ habl habm, (two_pt_line_unique hab hl habl.1 habl.2).trans
  (two_pt_line_unique hab hm habm.1 habm.2).symm

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

lemma noncollinear_neq {a b c : pts} (hf : noncollinear a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c :=
begin
  have : ∀ a b : pts, ∃ l ∈ lines, a ∈ l ∧ b ∈ l,
    intros a b, by_cases a = b,
    rw ←h, simp,
    have : ∃ p : pts, a ≠ p,
      by_contra, push_neg at h,
      rcases I3 with ⟨x, y, -, hxy, -, -, -⟩,
      exact hxy ((h x).symm .trans (h y)),
    cases this with b h,
    use (a-ₗb), exact ⟨line_in_lines h, pt_left_in_line a b⟩,
    use (a-ₗb), exact ⟨line_in_lines h, pt_left_in_line a b, pt_right_in_line a b⟩,
  split, intro h,
  rw h at hf,
  rcases this b c with ⟨l, hl, key⟩,
  exact hf ⟨l, hl, key.1, key.1, key.2⟩,
  split, intro h,
  rw h at hf,
  rcases this c b with ⟨l, hl, key⟩,
  exact hf ⟨l, hl, key.1, key.2, key.1⟩,
  intro h, rw h at hf,
  rcases this a c with ⟨l, hl, key⟩,
  exact hf ⟨l, hl, key.1, key.2, key.2⟩
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

lemma collinear_trans {a b c d : pts} (habc : collinear a b c) (habd : collinear a b d)
  (hab : a ≠ b) : collinear a c d :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩, rcases habd with ⟨m, hm, ham, hbm, hdm⟩,
  rw two_pt_one_line hm hl hab ⟨ham, hbm⟩ ⟨hal, hbl⟩ at hdm,
  exact ⟨l, hl, hal, hcl, hdm⟩
end

lemma collinear_noncollinear {a b c d : pts} (habc : collinear a b c) (habd : noncollinear a b d) :
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
λ habc hc, habc ⟨(a-ₗb), line_in_lines (noncollinear_neq habc).1,
  pt_left_in_line a b, pt_right_in_line a b, hc⟩

lemma noncollinear_in13 {a b c : pts} : noncollinear a b c → b ∉ (a-ₗc) :=
λ habc hb, habc ⟨(a-ₗc), line_in_lines (noncollinear_neq habc).2.1,
  pt_left_in_line a c, hb, pt_right_in_line a c⟩

lemma noncollinear_in23 {a b c : pts} : noncollinear a b c → a ∉ (b-ₗc) :=
λ habc ha, habc ⟨(b-ₗc), line_in_lines (noncollinear_neq habc).2.2, ha,
  pt_left_in_line b c, pt_right_in_line b c⟩

lemma collinear_in12' {a b c : pts} : c ∈ (a-ₗb) → collinear a b c :=
by { intro h, by_contra habc, exact (noncollinear_in12 habc) h }

lemma collinear_in13' {a b c : pts} : b ∈ (a-ₗc) → collinear a b c :=
by { intro h, by_contra habc, exact (noncollinear_in13 habc) h }

lemma collinear_in23' {a b c : pts} : a ∈ (b-ₗc) → collinear a b c :=
by { intro h, by_contra habc, exact (noncollinear_in23 habc) h }

lemma noncollinear_in12' {a b c : pts} (hab : a ≠ b)
: c ∉ (a-ₗb) → noncollinear a b c :=
by { contrapose!, intro h, unfold noncollinear at h, rw not_not at h,
  exact collinear_in12 h hab }

lemma noncollinear_in13' {a b c : pts} (hac : a ≠ c)
: b ∉ (a-ₗc) → noncollinear a b c :=
by { contrapose!, intro h, unfold noncollinear at h, rw not_not at h,
  exact collinear_in13 h hac }

lemma noncollinear_in23' {a b c : pts} (hbc : b ≠ c)
: a ∉ (b-ₗc) → noncollinear a b c :=
by { contrapose!, intro h, unfold noncollinear at h, rw not_not at h,
  exact collinear_in23 h hbc }
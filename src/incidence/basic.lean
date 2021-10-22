/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import set_theory.zfc

/-!
# Incidence geometry

This file defines incidence geometry as a class and proves basic lemmas about
points, lines and collinearity.

## Main definitions

* `incidence_geometry` is a class satisfying the three axioms of incidence.

* `line`, with notation `-ₗ`, is the unique line determined by the given two points.

* `col` is a ternary relation among points meaning they lie on the same line.

* `noncol` is the opposite of `col`.

## References

* See [Geometry: Euclid and Beyond]

-/

universes u

/--An incidence geometry contains a type `pts` and a set `lines` that includes some sets of pts,
with the following axioms :
I1. Two distinct points uniquely define a line.
I2. Every line contains at least 2 distinct points.
I3. There exists 3 noncol points.
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

lemma intersect_symm {m n : set pts} :
(m ♥ n) → (n ♥ m) :=
by {unfold intersect, rw set.inter_comm, simp only [imp_self]}

/--Two lines are parallel if they have no intersection. -/
def parallel (l₁ l₂ : set pts) : Prop :=
¬(l₁ ♥ l₂) ∧ (l₁ ∈ lines) ∧ (l₂ ∈ lines)

notation l₁`∥ₗ`l₂ := parallel l₁ l₂

lemma parallel_symm {l₁ l₂ : set pts} :
(l₁ ∥ₗ l₂) → (l₂ ∥ₗ l₁) :=
begin
  rintros ⟨hl₁l₂, hl₁, hl₂⟩,
  exact ⟨λhf, hl₁l₂ (intersect_symm hf), hl₂, hl₁⟩
end

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
{a b : pts} (hab : a ≠ b) (hal : a ∈ l) (hbl : b ∈ l) (ham : a ∈ m) (hbm : b ∈ m) : l = m :=
(two_pt_line_unique hab hl hal hbl).trans(two_pt_line_unique hab hm ham hbm).symm

lemma line_symm (a b : pts) : (a-ₗb) = (b-ₗa) :=
begin
  by_cases a = b, rw h,
  exact two_pt_one_line (line_in_lines h) (line_in_lines (ne.symm h))
    h (pt_left_in_line a b) (pt_right_in_line a b) (pt_right_in_line b a) (pt_left_in_line b a)
end

lemma two_line_one_pt {l₁ l₂ : set pts} (hl₁ : l₁ ∈ lines) (hl₂ : l₂ ∈ lines) :
∀ {a b : pts}, l₁ ≠ l₂ → a ∈ l₁ → a ∈ l₂ → b ∈ l₁ → b ∈ l₂ → a = b :=
begin
  intros a b hll ha₁ ha₂ hb₁ hb₂,
  by_cases hab : a = b, exact hab,
  rcases (I1 hab) with ⟨l, hl, -, -, key⟩,
  exact absurd ((key l₁ hl₁ ha₁ hb₁).trans (key l₂ hl₂ ha₂ hb₂).symm) hll
end

/--Three points are col if there are on the same line. -/
def col (a b c : pts) : Prop :=
∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

/--Opposite to col -/
def noncol (a b c : pts) : Prop := ¬col a b c

lemma noncol_exist {a b : pts} (hab : a ≠ b) : ∃ c : pts, noncol a b c :=
begin
  by_contra hf, unfold noncol col at hf, push_neg at hf,
  rcases I3 with ⟨x, y, z, hxy, hxz, hyz, hxyz⟩,
  rcases hf x with ⟨l, hl, hal, hbl, hxl⟩,
  rcases hf y with ⟨m, hm, ham, hbm, hym⟩,
  rcases hf z with ⟨n, hn, han, hbn, hzn⟩,
  rw ←two_pt_one_line hl hm hab hal hbl ham hbm at hym,
  rw ←two_pt_one_line hl hn hab hal hbl han hbn at hzn,
  exact hxyz ⟨l, hl, hxl, hym, hzn⟩
end

lemma noncol_neq {a b c : pts} (hf : noncol a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c :=
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

lemma col12 {a b c : pts} : col a b c → col b a c :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncol12 {a b c : pts} : noncol a b c → noncol b a c :=
by {unfold noncol, contrapose!, exact col12}

lemma col13 {a b c : pts} : col a b c → col c b a :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncol13 {a b c : pts} : noncol a b c → noncol c b a :=
by {unfold noncol, contrapose!, exact col13}

lemma col23 {a b c : pts} : col a b c → col a c b :=
by {rintros ⟨l, hl, habc⟩, use l, tauto}

lemma noncol23 {a b c : pts} : noncol a b c → noncol a c b :=
by {unfold noncol, contrapose!, exact col23}

lemma col123 {a b c : pts} : col a b c → col b c a :=
λh, col23 (col12 h)

lemma col132 {a b c : pts} : col a b c → col c a b :=
λh, col23 (col13 h)

lemma noncol123 {a b c : pts} : noncol a b c → noncol b c a :=
by {unfold noncol, contrapose!, exact col132}

lemma noncol132 {a b c : pts} : noncol a b c → noncol c a b :=
by {unfold noncol, contrapose!, exact col123}

lemma col_trans {a b c d : pts} (habc : col a b c) (habd : col a b d)
  (hab : a ≠ b) : col a c d :=
begin
  rcases habc with ⟨l, hl, hal, hbl, hcl⟩, rcases habd with ⟨m, hm, ham, hbm, hdm⟩,
  rw two_pt_one_line hm hl hab ham hbm hal hbl at hdm,
  exact ⟨l, hl, hal, hcl, hdm⟩
end

lemma col_noncol {a b c d : pts} (habc : col a b c) (habd : noncol a b d) :
a ≠ c → noncol a c d :=
λhac hacd, habd (col_trans (col23 habc) hacd hac)

lemma col_in12 {a b c : pts} : col a b c → a ≠ b → c ∈ (a-ₗb) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hab,
  rw two_pt_one_line hl (line_in_lines hab) hab
    hal hbl (pt_left_in_line a b) (pt_right_in_line a b) at hcl,
  exact hcl
end

lemma col_in21 {a b c : pts} : col a b c → b ≠ a → c ∈ (b-ₗa) :=
by {rw line_symm, exact λhabc hba, col_in12 habc hba.symm}

lemma col_in13 {a b c : pts} : col a b c → a ≠ c → b ∈ (a-ₗc) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hac,
  rw two_pt_one_line hl (line_in_lines hac) hac
    hal hcl (pt_left_in_line a c) (pt_right_in_line a c) at hbl,
  exact hbl
end

lemma col_in31 {a b c : pts} : col a b c → c ≠ a → b ∈ (c-ₗa) :=
by {rw line_symm, exact λhabc hca, col_in13 habc hca.symm}

lemma col_in23 {a b c : pts} : col a b c → b ≠ c → a ∈ (b-ₗc) :=
begin
  rintros ⟨l, hl, hal, hbl, hcl⟩, intro hbc,
  rw two_pt_one_line hl (line_in_lines hbc) hbc
    hbl hcl (pt_left_in_line b c) (pt_right_in_line b c) at hal,
  exact hal
end

lemma col_in32 {a b c : pts} : col a b c → c ≠ b → a ∈ (c-ₗb) :=
by {rw line_symm, exact λhabc hcb, col_in23 habc hcb.symm}

lemma noncol_in12 {a b c : pts} : noncol a b c → c ∉ (a-ₗb) :=
λ habc hc, habc ⟨(a-ₗb), line_in_lines (noncol_neq habc).1,
  pt_left_in_line a b, pt_right_in_line a b, hc⟩

lemma noncol_in21 {a b c : pts} : noncol a b c → c ∉ (b-ₗa) :=
by {rw line_symm, exact noncol_in12}

lemma noncol_in13 {a b c : pts} : noncol a b c → b ∉ (a-ₗc) :=
λ habc hb, habc ⟨(a-ₗc), line_in_lines (noncol_neq habc).2.1,
  pt_left_in_line a c, hb, pt_right_in_line a c⟩

lemma noncol_in31 {a b c : pts} : noncol a b c → b ∉ (c-ₗa) :=
by {rw line_symm, exact noncol_in13}

lemma noncol_in23 {a b c : pts} : noncol a b c → a ∉ (b-ₗc) :=
λ habc ha, habc ⟨(b-ₗc), line_in_lines (noncol_neq habc).2.2, ha,
  pt_left_in_line b c, pt_right_in_line b c⟩

lemma noncol_in32 {a b c : pts} : noncol a b c → a ∉ (c-ₗb) :=
by {rw line_symm, exact noncol_in23}

lemma col_in12' {a b c : pts} : c ∈ (a-ₗb) → col a b c :=
by { intro h, by_contra habc, exact (noncol_in12 habc) h }

lemma col_in21' {a b c : pts} : c ∈ (b-ₗa) → col a b c :=
by { rw line_symm, exact col_in12' }

lemma col_in13' {a b c : pts} : b ∈ (a-ₗc) → col a b c :=
by { intro h, by_contra habc, exact (noncol_in13 habc) h }

lemma col_in31' {a b c : pts} : b ∈ (c-ₗa) → col a b c :=
by { rw line_symm, exact col_in13' }

lemma col_in23' {a b c : pts} : a ∈ (b-ₗc) → col a b c :=
by { intro h, by_contra habc, exact (noncol_in23 habc) h }

lemma col_in32' {a b c : pts} : a ∈ (c-ₗb) → col a b c :=
by { rw line_symm, exact col_in23' }

lemma noncol_in12' {a b c : pts} (hab : a ≠ b) : c ∉ (a-ₗb) → noncol a b c :=
by { contrapose!, intro h, unfold noncol at h, rw not_not at h,
  exact col_in12 h hab }

lemma noncol_in21' {a b c : pts} (hba : b ≠ a) : c ∉ (b-ₗa) → noncol a b c :=
by { rw line_symm, exact noncol_in12' hba.symm }

lemma noncol_in13' {a b c : pts} (hac : a ≠ c) : b ∉ (a-ₗc) → noncol a b c :=
by { contrapose!, intro h, unfold noncol at h, rw not_not at h,
  exact col_in13 h hac }

lemma noncol_in31' {a b c : pts} (hca : c ≠ a) : b ∉ (c-ₗa) → noncol a b c :=
by { rw line_symm, exact noncol_in13' hca.symm }

lemma noncol_in23' {a b c : pts} (hbc : b ≠ c) : a ∉ (b-ₗc) → noncol a b c :=
by { contrapose!, intro h, unfold noncol at h, rw not_not at h,
  exact col_in23 h hbc }

lemma noncol_in32' {a b c : pts} (hcb : c ≠ b) : a ∉ (c-ₗb) → noncol a b c :=
by { rw line_symm, exact noncol_in23' hcb.symm }
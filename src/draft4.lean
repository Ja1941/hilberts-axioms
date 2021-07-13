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

notation a`~`b := (line a b).1

def intersect (m n : set I.pts) : Prop := (m ∩ n).nonempty

notation m`$`n := intersect m n

lemma line_in_line {a b : I.pts} (hab : a ≠ b) :
a~b ∈ I.lines := (line a b).2.1 hab

lemma endpt_left_in_line (a b : I.pts) :
a ∈ (a~b) := (line a b).2.2.1

lemma endpt_right_in_line (a b : I.pts) :
b ∈ (a~b) := (line a b).2.2.2

lemma line_unique {a b : I.pts} (hab : a ≠ b)
{l : set I.pts} (hl : l ∈ I.lines) (ha : a ∈ l) (hb : b ∈ l) : l = (a~b) :=
begin
  rcases (I.I1 a b hab) with ⟨n, hn, -, -, key⟩,
  rw [key l hl ha hb,
      key (a~b) (line_in_line hab) (endpt_left_in_line a b) (endpt_right_in_line a b)]
end

lemma two_pt_on_one_line {l : set I.pts} (hl : l ∈ I.lines) :
∃ a b : I.pts, a ≠ b ∧ a ∈ l ∧ b ∈ l := I.I2 l hl

lemma two_pt_one_line {l m : set I.pts} (hl : l ∈ I.lines) (hm : m ∈ I.lines) {a b : I.pts} (hab : a ≠ b) :
a ∈ l ∧ b ∈ l → a ∈ m ∧ b ∈ m → l = m :=
λ habl habm, (line_unique hab hl habl.1 habl.2).trans (line_unique hab hm habm.1 habm.2).symm

lemma two_line_one_pt {l₁ l₂ : set I.pts} (hl₁ : l₁ ∈ I.lines) (hl₂ : l₂ ∈ I.lines) :
∀ {a b : I.pts}, l₁ ≠ l₂ → a ≠ b → ¬(a ∈ (l₁ ∩ l₂) ∧ b ∈ (l₁ ∩ l₂)) :=
begin
  intros a b hll hab hf,
  rcases (I.I1 a b hab) with ⟨l, hl, -, -, key⟩,
  exact hll ((key l₁ hl₁ (mem_of_mem_inter_left hf.1) (mem_of_mem_inter_left hf.2)).trans
            (key l₂ hl₂ (mem_of_mem_inter_right hf.1) (mem_of_mem_inter_right hf.2)).symm)
end

def collinear (a b c : I.pts) : Prop :=
∃ l ∈ I.lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

def noncollinear (a b c : I.pts) : Prop := ¬collinear a b c

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

local notation a`#`b`#`c := B.is_between a b c

instance : has_coe incidence_order_geometry incidence_geometry :=
⟨incidence_order_geometry.to_incidence_geometry⟩

lemma is_between_comm (a b c : B.pts) :
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

def segment (a b : B.pts) : set B.pts :=
{c : B.pts | B.is_between a c b} ∪ {a, b}

notation a`-`b := segment a b

lemma segment_comm (a b : B.pts) : a-b = b-a :=
begin
  unfold segment,
  ext1, simp,
  rw [is_between_comm b x a, or_comm, or_assoc, or_comm _ (x=a)]
end

lemma segment_singleton (a : B.pts) : a-a = {a} :=
begin
  unfold segment,
  suffices : {c : B.pts | B.is_between a c a} = ∅,
    rw this, simp,
  ext1, simp, intro hf,
  exact (is_between_not_eq hf).2.1 (rfl)
end

lemma segment_in_line (a b : B.pts) : (a-b) ⊆ (a~b) :=
begin
  have hal : a ∈ (a~b), from endpt_left_in_line a b,
  have hbl : b ∈ (a~b), from endpt_right_in_line a b,
  by_cases hab : a = b,
    rw hab, rw hab at hbl, rw segment_singleton, simp, exact hbl,
  have hl := line_in_line hab, simp at hl,
  unfold segment,
  apply union_subset,
  intros c hc, simp at hc,
  rcases is_between_collinear hc with ⟨m, hm, ham, hcm, hbm⟩,
  simp, rw (two_pt_one_line hl hm hab ⟨hal, hbl⟩ ⟨ham, hbm⟩), exact hcm,
  intros x hx, simp at hx, cases hx with hx hx; rw hx,
  exact hal, exact hbl
end

lemma pasch {a b c : B.pts} (habc : noncollinear a b c) {l : set B.pts} (hl : l ∈ B.lines) :
a ∉ l → b ∉ l → c ∉ l → (l $ (a-b)) →
((l $ (a-c)) ∨ (l $ (b-c))) ∧ ¬((l $ (a-c)) ∧ (l $ (b-c))) :=
begin
  intros ha hb hc hlab,
  have hd : ∃ d : B.pts, B.is_between a d b ∧ d ∈ l,
    unfold segment intersect set.nonempty at hlab, simp at hlab,
    rcases hlab with ⟨d, hdl, da | db | hadb⟩,
    rw da at hdl, exact absurd hdl ha,
    rw db at hdl, exact absurd hdl hb,
    exact ⟨d, hadb, hdl⟩,
  split,
  rcases (B.B4 a b c l hl habc ha hb hc hd).1 with ⟨p, hpl, h⟩,
  unfold intersect segment set.nonempty, simp,
  cases h with h h,
  left, exact ⟨p, hpl, by {right, right, exact h}⟩,
  right, exact ⟨p, hpl, by {right, right, exact h}⟩,
  unfold intersect segment set.nonempty,
  have := (B.B4 a b c l hl habc ha hb hc hd).2,
  intros hf, simp at hf,
  rcases hf.1 with ⟨x, hxl, hx⟩,
  rcases hf.2 with ⟨y, hyl, hy⟩,
  rcases hx with hxa | hxc | hx,
  rw ←hxa at ha, exact absurd hxl ha, rw ←hxc at hc, exact absurd hxl hc,
  rcases hy with hyb | hyc | hy,
  rw ←hyb at hb, exact absurd hyl hb, rw ←hyc at hc, exact absurd hyl hc,
  exact (this x y hxl hyl) ⟨hx, hy⟩
end

def same_side_line (l : set B.pts) (a b : B.pts) : Prop := ¬(l $ (a-b))

def diff_side_line (l : set B.pts) (a b : B.pts) : Prop :=
(l $ (a-b)) ∧ a ∉ l ∧ b ∉ l

lemma same_or_diff_line_strict
{l : set B.pts} (hl : l ∈ B.lines) {a b : B.pts} (ha : a ∉ l) (hb : b ∉ l) :
(same_side_line l a b ∨ diff_side_line l a b)
∧ ¬(same_side_line l a b ∧ diff_side_line l a b) :=
begin
  unfold same_side_line diff_side_line segment,
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

example {a : set B.pts} : ¬a.nonempty → a = ∅ := not_nonempty_iff_eq_empty.mp

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
  rw segment_comm, simp
end

lemma same_side_not_in {x y : B.pts} {l : set B.pts} (hl : l ∈ B.lines) :
same_side_line l x y → x ∉ l ∧ y ∉ l :=
begin
  intro hlxy, unfold same_side_line intersect at hlxy, rw not_nonempty_iff_eq_empty at hlxy, split,
  intro hxl, have : x ∈ l ∩ (x-y), simp, exact ⟨hxl, by {unfold segment, simp}⟩,
  rw hlxy at this, exact this,
  intro hyl, have : y ∈ l ∩ (x-y), simp, exact ⟨hyl, by {unfold segment, simp}⟩,
  rw hlxy at this, exact this
end

lemma same_side_line_trans_noncollinear {l : set B.pts} (hl : l ∈ B.lines) {a b c : B.pts} :
noncollinear a b c → same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  unfold same_side_line, intros h hlab hlbc,
  rw segment_comm at hlbc,
  intro hlac,
  replace h : noncollinear a c b,
    unfold noncollinear collinear, unfold noncollinear collinear at h,
    intro hf, apply h, rcases hf with ⟨l, hl, hal, hcl, hbl⟩,
    exact ⟨l, hl, hal, hbl, hcl⟩, 
  cases (pasch h hl (same_side_not_in hl hlab).1 (same_side_not_in hl hlbc).1 (same_side_not_in hl hlab).2 hlac).1 with hf hf,
  exact hlab hf, exact hlbc hf
end

lemma same_side_line_trans {l : set B.pts} (hl : l ∈ B.lines) (a b c : B.pts) :
same_side_line l a b → same_side_line l b c → same_side_line l a c :=
begin
  by_cases collinear a b c; intros hlab hlbc,
  by_cases hab : a = b, rw ←hab at hlbc, exact hlbc,
  by_cases hbc : b = c, rw hbc at hlab, exact hlab,
  by_cases hac : a = c, rw hac, exact same_side_line_refl hl (same_side_not_in hl hlbc).2,
  rcases h with ⟨m, hm, ham, hbm, hcm⟩,
  have hd : ∃ d : B.pts, d ∈ l ∧ d ∉ m,
    rcases two_pt_on_one_line hl with ⟨x, y, hxy, hxl, hyl⟩,
    have hlm : l ≠ m, intro hlm, rw ←hlm at ham, exact (same_side_not_in hl hlab).1 ham,
    cases not_and_distrib.mp (two_line_one_pt hl hm hlm hxy) with hx hy,
    exact ⟨x, hxl, not_and.mp hx hxl⟩,
    exact ⟨y, hyl, not_and.mp hy hyl⟩,
  rcases hd with ⟨d, hdl, hdm⟩,
  cases is_between_extend (show d ≠ a, by {intro hda, rw hda at hdm, exact hdm ham}) with e hdae,
  have hlae : same_side_line l a e,
    intro hlae, cases hlae with f hf,
    have hflae : f ∈ l ∧ f ∈ (a~e),
      simp, simp at hf,
      exact ⟨hf.1, segment_in_line a e hf.2⟩,
    have hdlae : d ∈ l ∧ d ∈ (a~e),
      simp, simp at hf,
      split, exact hdl,
      rcases is_between_collinear hdae with ⟨n, hn, hdn, han, hen⟩,
      have := (two_pt_one_line (line_in_line (is_between_not_eq hdae).2.2) hn ((is_between_not_eq hdae).2.2) ⟨endpt_left_in_line a e, endpt_right_in_line a e⟩ ⟨han, hen⟩),
      simp at this, rw this, exact hdn,
    have hneq : l ≠ (a~e),
      intro hf, have := (same_side_not_in hl hlab).1, rw hf at this, exact this (endpt_left_in_line a e),
    have hdf : d = f,
      by_cases hdf : d = f, exact hdf,
      have := two_line_one_pt hl (line_in_line (is_between_not_eq hdae).2.2) hneq hdf,
      exfalso, exact this ⟨hdlae, hflae⟩,
    rw hdf at hdae,
    unfold segment at hf, simp at hf,
    have := is_between_not_eq hdae,
    rcases hf.2 with hf | hf | hf,
    exact this.1 hf, exact this.2.1 hf,
  exact (collinear_between (is_between_collinear hf)).2.2.1 ⟨hf, hdae⟩,
  have hbae : noncollinear b a e,
    rintros ⟨n, hn, hbn, han, hen⟩,
    have hem : e ∈ m,
      rw two_pt_one_line hm hn hab ⟨ham, hbm⟩ ⟨han, hbn⟩, exact hen,
    have hd : d ∈ (a~e),
      simp, rcases is_between_collinear hdae with ⟨n, hn, hdn, han, hen⟩,
      have := (two_pt_one_line (line_in_line (is_between_not_eq hdae).2.2) hn ((is_between_not_eq hdae).2.2) ⟨endpt_left_in_line a e, endpt_right_in_line a e⟩ ⟨han, hen⟩),
      simp at this, rw this, exact hdn,
    have := two_pt_one_line hm (line_in_line (is_between_not_eq hdae).2.2) (is_between_not_eq hdae).2.2 ⟨ham, hem⟩ ⟨endpt_left_in_line a e, endpt_right_in_line a e⟩,
    simp at this hd, rw ←this at hd,
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
o ∉ (a-b) ∧ collinear o a b

def diff_side_pt (o a b : B.pts) : Prop :=
o ∈ (a-b) ∧ collinear o a b

def ray (o a : B.pts) : set B.pts :=
{x : B.pts | same_side_pt o a x} ∪ {o}

def angle (a o b : B.pts) : set B.pts := (ray o a) ∪ ray o b

notation `∠` := angle

def inside_angle {a o b : B.pts} (O := angle a o b) (p : B.pts) : Prop := 
same_side_line (o~a) b p ∧ same_side_line (o~b) a p

lemma crossbar {a b c d : B.pts} (BAC := angle b a c) (hbac : noncollinear b a c)
(hd : inside_angle BAC d) : ray a d $ (b-c) :=
begin
  by_cases hac : a = c,
    rw hac, use c, unfold ray segment, simp,
  by_cases hab : a = b,
    rw hab, use b, unfold ray segment, simp,
  cases is_between_extend (ne.symm hac) with e hcae,
  have had : a ≠ d,
    intro had, rw ←had at hd, have hf := (same_side_not_in (line_in_line hab) hd.1).2,
    have ht := endpt_left_in_line a b, simp at ht hf, exact hf ht,
  have hec : e ≠ c,
    intro hec, rw hec at hcae, exact (is_between_not_eq hcae).2.1 rfl,
  have hecb : noncollinear e c b,
    rintros ⟨l, hl, hel, hcl, hbl⟩,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    rw (two_pt_one_line hm hl hec ⟨hem, hcm⟩ ⟨hel, hcl⟩) at ham,
    exact hbac ⟨l, hl, hbl, ham, hcl⟩,
  have h₁ : (((a~d) $ (e-b)) ∨ ((a~d) $ (c-b))) ∧ ¬(((a~d) $ (e-b)) ∧ ((a~d) $ (c-b))),
    apply pasch hecb (line_in_line had),
    intro haed,
    have hf : d ∈ (a~d), from endpt_right_in_line a d,
    rcases is_between_collinear hcae with ⟨m, hm, hcm, ham, hem⟩,
    have hae : a ≠ e,
      intro hae, rw hae at hcae, exact (is_between_not_eq hcae).2.2 rfl,
    rw ←(two_pt_one_line hm (line_in_line had) hae ⟨ham, hem⟩ ⟨endpt_left_in_line a d, haed⟩) at hf,
    rw (two_pt_one_line hm (line_in_line hac) hac ⟨ham, hcm⟩ ⟨endpt_left_in_line a c, endpt_right_in_line a c⟩) at hf,
    unfold inside_angle same_side_line at hd, apply hd.2, use d, unfold segment, exact ⟨hf, by simp⟩,
    intro hacd,
    have hf : d ∈ (a~d), from endpt_right_in_line a d,
    rw (two_pt_one_line (line_in_line had) (line_in_line hac) hac ⟨endpt_left_in_line a d, hacd⟩ ⟨endpt_left_in_line a c, endpt_right_in_line a c⟩) at hf,
    unfold inside_angle same_side_line at hd, apply hd.2, use d, unfold segment, exact ⟨hf, by simp⟩,
    intro habd,
    have hf : d ∈ (a~d), from endpt_right_in_line a d,
    rw (two_pt_one_line (line_in_line had) (line_in_line hab) hab ⟨endpt_left_in_line a d, habd⟩ ⟨endpt_left_in_line a b, endpt_right_in_line a b⟩) at hf,
    unfold inside_angle same_side_line at hd, apply hd.1, use d, unfold segment, exact ⟨hf, by simp⟩,
    use a, split, exact endpt_left_in_line a d,
    unfold segment, simp, right, right, rw is_between_comm at hcae, exact hcae,
    
end

structure incidence_order_congruence_geometry extends incidence_order_geometry :=
--Can I specify that set pts here is always segment?
(line_congr : set pts → set pts → Prop)
--For an arbitrary segment and a ray, we find a unique congruent segment on the ray
(C1 : ∀ a b c d : pts, ∃ e ∈ ray c d,
line_congr (a-b) (c-d) ∧ ∀ x ∈ ray c d, line_congr (a-b) (c-d) → x = e)
--This is equivalent to congruency being an equivalent relation
(C2 : ∀ a b c d e f : pts,
line_congr (a-b) (c-d) → line_congr (a-b) (e-f) → line_congr (c-d) (e-f) ∧ line_congr (a-b) (a-b))
--This axiom deals with addition of segments.
(C3 : ∀ a b c d e f: pts, is_between a b c → is_between d e f → line_congr (a-b) (c-d)
                        → line_congr (b-c) (e-f) → line_congr (a-c) (d-f))
--Same question
(angle_congr : set pts → set pts → Prop)
--Given any angle and a ray, we find a pt that together with the ray forms a congruent angle
--Also, this pt is unique on its side w.r.t the ray
(C4 : ∀ a b c d f : pts, ∃ e : pts, angle_congr (∠b a c) (∠e d f)
∧ ∀ x : pts, same_side_line (d~f) e x → angle_congr (∠b a c) (∠x d f) → x = e)
--Similar to C2
(C5 : ∀ a b c d e f g h i : pts,
angle_congr (∠a b c) (∠d e f) → angle_congr (∠a b c) (∠g h i) → angle_congr (∠d e f) (∠g h i)
∧ angle_congr (∠a b c) (∠a b c))
--SAS!!!
(C6 : ∀ a b c d e f, line_congr (a-b) (d-e) → line_congr (a-c) (d-f) → angle_congr (∠b a c) (∠e d f)
→ line_congr (b-c) (e-f) ∧ angle_congr (∠a b c) (∠d e f) ∧ angle_congr (∠b c a) (∠e f d))

instance : has_coe incidence_order_congruence_geometry incidence_order_geometry :=
⟨incidence_order_congruence_geometry.to_incidence_order_geometry⟩

variable {C : incidence_order_congruence_geometry}

local infix `≅` : 50 := λ a b, C.line_congr a b

local infix `≅` : 50 := λ a b, C.angle_congr a b

def triangle (a b c : C.pts) : set C.pts :=
(a-b) ∪ (a-c) ∪ (b-c)

notation `Δ` := triangle

def tri_congr {a b c d e f : C.pts} (ABC : Δ a b c) (DEF : Δ d e f) : Prop :=
(a-b) ≅ (d-e) ∧ (a-c) ≅ (d-f) ∧ (b-c) ≅ (e-f) ∧
(∠a b c) ≅ (∠d e f) ∧ (∠a c b) ≅ (∠d f e) ∧ (∠b a c) ≅ (∠e d f)

infix `≅` : 50 := λ a b, tri_congr a b

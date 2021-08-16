import incidence.basic

open_locale classical

/--An incidence order geometry is an incidence geometry with betweenness, a ternary relation
for `pts`. `between a b c` means `b` is between `a` and `c`, restricted by some axioms :
B1 : If a point is between the other two, they are col.
B2 : We can extend two distinct points.
B3 : Given 3 distinct points, exactly one of them is between the other two.
B4 : Pasch's axiom. `a`, `b`, `c` are noncol and for a line `l` not containing any of them,
     if `l` contains a points between `a` and `b`, it contains a points either between `a` and
     `c` or between `b` and `c`.
-/
class incidence_order_geometry extends incidence_geometry :=
(between : pts → pts → pts → Prop)
(B1 : ∀ {a b c : pts}, between a b c → between c b a
                        ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ col a b c)
(B2 : ∀ {a b : pts}, a ≠ b → ∃ c : pts, between a b c)
(B3 : (∀ {a b c : pts}, ∀ {l : set pts}, l ∈ lines → a ∈ l ∧ b ∈ l ∧ c ∈ l →
(a ≠ b → a ≠ c → b ≠ c → between a b c ∨ between a c b ∨ between b a c)) ∧
∀ a b c : pts, ¬(between a b c ∧ between a c b)
∧ ¬(between a b c ∧ between b a c) ∧ ¬(between a c b ∧ between b a c))
(B4 : ∀ {a b c : pts} (l ∈ lines),
      (noncol a b c) → a ∉ l → b ∉ l → c ∉ l
      → (∃ d : pts, between a d b ∧ d ∈ l) →
      (∃ p : pts, p ∈ l ∧ (between a p c ∨ between b p c))
      ∧ ∀ p q : pts, p ∈ l → q ∈ l → ¬(between a p c ∧ between b q c))

variable [B : incidence_order_geometry]

open incidence_geometry incidence_order_geometry

include B

lemma between_symm (a b c : pts) :
between a b c ↔ between c b a := iff.intro (λ h, (B1 h).1) (λ h, (B1 h).1)

lemma between_neq {a b c : pts} (h : between a b c) :
(a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) := ⟨(B1 h).2.1, (B1 h).2.2.1, (B1 h).2.2.2.1⟩

lemma between_col {a b c : pts}
(h : between a b c) : col a b c := (B1 h).2.2.2.2

lemma between_extend {a b : pts} (h : a ≠ b) :
∃ c : pts, between a b c := B2 h

lemma between_tri {a b c : pts} (habc : col a b c) (hab : a ≠ b) (hac : a ≠ c)
(hbc : b ≠ c) : between a b c ∨ between a c b ∨ between b a c :=
by { rcases habc with ⟨l, hl, habc⟩, exact B3.1 hl habc hab hac hbc }

lemma between_contra {a b c : pts} :
  ¬(between a b c ∧ between a c b)
∧ ¬(between a b c ∧ between b a c)
∧ ¬(between a c b ∧ between b a c) := B3.2 a b c

/--A type whose inside is a set containing two points and points between them. -/
structure seg := (inside : set pts)
(in_eq : ∃ a b : pts, inside = {x : pts | between a x b} ∪ {a, b})

/--A seg is nontrivial if its inside is not a singleton.
Equivalently, `a` and `b` are distinct. -/
def seg_nontrivial (s : seg) : Prop :=
∀ x : pts, s.inside ≠ {x}

/--Explicitly stating `a` and `b` defines a seg. -/
def two_pt_seg (a b : pts) : seg := ⟨{x : pts | between a x b} ∪ {a, b}, ⟨a, b, rfl⟩⟩

notation a`-ₛ`b := two_pt_seg a b

lemma pt_left_in_seg (a b : B.pts) : a ∈ (a-ₛb).inside :=
by { unfold two_pt_seg, simp }

lemma pt_right_in_seg (a b : B.pts) : b ∈ (a-ₛb).inside :=
by { unfold two_pt_seg, simp }

lemma seg_symm (a b : pts) : (a-ₛb) = (b-ₛa) :=
by {unfold two_pt_seg, simp, ext, simp, rw between_symm, tauto}

lemma seg_singleton (a : pts) : (a-ₛa).inside = {a} :=
begin
  unfold two_pt_seg, ext1, simp,
  intro haxa, exact absurd rfl (between_neq haxa).2.1
end

lemma seg_nontrivial_iff_neq {a b : pts} :
seg_nontrivial (a-ₛb) ↔ a ≠ b :=
begin
  split; intro h,
  by_contra hab, push_neg at hab,
  rw hab at h, exact h b (seg_singleton b),
  intros x hf,
  have := pt_left_in_seg a b, rw hf at this,
  simp at this, rw this at h,
  have := pt_right_in_seg a b, rw hf at this,
  simp at this, rw this at h,
  exact h rfl
end 

lemma seg_in_line (a b : pts) : (a-ₛb).inside ⊆ (a-ₗb) :=
begin
  have hal : a ∈ (a-ₗb), from pt_left_in_line a b,
  have hbl : b ∈ (a-ₗb), from pt_right_in_line a b,
  by_cases hab : a = b,
    rw hab, rw hab at hbl, rw seg_singleton, simp, exact hbl,
  unfold two_pt_seg,
  apply set.union_subset,
  intros c hc, simp at hc,
  exact col_in13 (between_col hc) hab,
  intros x hx, simp at hx, cases hx with hx hx; rw hx,
  exact hal, exact hbl
end

lemma seg_two_pt (s : seg) : ∃ a b : pts, s = (a-ₛb) :=
begin
  induction s with inside in_eq,
  rcases in_eq with ⟨a, b, h⟩, use [a, b],
  unfold two_pt_seg, simp only, exact h
end

theorem pasch {a b c : pts} (habc : noncol a b c) {l : set pts} (hl : l ∈ lines) :
a ∉ l → b ∉ l → c ∉ l → (l ♥ (a-ₛb).inside) →
((l ♥ (a-ₛc).inside) ∨ (l ♥ (b-ₛc).inside)) ∧ ¬((l ♥ (a-ₛc).inside) ∧ (l ♥ (b-ₛc).inside)) :=
begin
  intros ha hb hc hlab,
  have hd : ∃ d : pts, between a d b ∧ d ∈ l,
    unfold two_pt_seg at hlab, unfold intersect set.nonempty at hlab, simp at hlab,
    rcases hlab with ⟨d, hdl, da | db | hadb⟩,
    rw da at hdl, exact absurd hdl ha,
    rw db at hdl, exact absurd hdl hb,
    exact ⟨d, hadb, hdl⟩,
  split,
  rcases (B4 l hl habc ha hb hc hd).1 with ⟨p, hpl, h⟩,
  unfold two_pt_seg, unfold intersect set.nonempty, simp,
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

lemma two_pt_between {a b : pts} (hab : a ≠ b) : ∃ c : pts, between a c b :=
begin
  cases noncol_exist hab with c habc,
  have hac := (noncol_neq habc).2.1,
  have hbc := (noncol_neq habc).2.2,
  cases between_extend hac with d hacd,
  have had := (between_neq hacd).2.1,
  have hadb : noncol a d b,
    from col_noncol (between_col hacd) (noncol23 habc) had,
  have hbd := (noncol_neq hadb).2.2.symm,
  have hcd := (between_neq hacd).2.2,
  cases between_extend hbd with e hbde,
  have hce : c ≠ e,
    intro hce, rw ←hce at hbde,
    rcases (between_col hbde) with ⟨l, hl, hbl, hdl, hcl⟩,
    rcases (between_col hacd) with ⟨m, hm, ham, hcm, hdm⟩,
    rw two_pt_one_line hm hl hcd ⟨hcm, hdm⟩ ⟨hcl, hdl⟩ at ham,
    exact habc ⟨l, hl, ham, hbl, hcl⟩,
  have hde : d ≠ e, from (between_neq hbde).2.2,
  have hbe : b ≠ e, from (between_neq hbde).2.1,
  rcases (between_col hbde) with ⟨l, hl, hbl, hdl, hel⟩,
  rcases (between_col hacd) with ⟨m, hm, ham, hcm, hdm⟩,
  have : a ∉ (c-ₗe) ∧ d ∉ (c-ₗe) ∧ b ∉ (c-ₗe),
    split, intro hace,
    have he := pt_right_in_line c e, rw two_pt_one_line (line_in_lines hce)
      hm hac ⟨hace, pt_left_in_line c e⟩ ⟨ham, hcm⟩ at he,
    rw (two_pt_one_line hl hm hde ⟨hdl, hel⟩ ⟨hdm, he⟩) at hbl,
    exact habc ⟨m, hm, ham, hbl, hcm⟩,
    split, intro hdce,
    have hc := pt_left_in_line c e, rw two_pt_one_line (line_in_lines hce)
      hl hde ⟨hdce, pt_right_in_line c e⟩ ⟨hdl, hel⟩ at hc,
    rw two_pt_one_line hl hm hcd ⟨hc, hdl⟩ ⟨hcm, hdm⟩ at hbl,
    exact habc ⟨m, hm, ham, hbl, hcm⟩,
    intro hbce,
    have hc := pt_left_in_line c e, rw two_pt_one_line (line_in_lines hce)
      hl hbe ⟨hbce, pt_right_in_line c e⟩ ⟨hbl, hel⟩ at hc,
    rw two_pt_one_line hl hm hcd ⟨hc, hdl⟩ ⟨hcm, hdm⟩ at hbl,
    exact habc ⟨m, hm, ham, hbl, hcm⟩,
  have intersect : ((c-ₗe)♥(a-ₛd).inside),
    use c, split, exact pt_left_in_line c e,
    unfold two_pt_seg, simp, right, right, exact hacd,
  cases (pasch hadb (line_in_lines hce) this.1 this.2.1 this.2.2 intersect).1 with key hf,
  cases key with x hx, unfold two_pt_seg at hx, simp at hx,
  rcases hx.2 with hxa | hxb | haxb,
  rw hxa at hx, exact absurd hx.1 this.1,
  rw hxb at hx, exact absurd hx.1 this.2.2,
  exact ⟨x, haxb⟩,
  cases hf with x hx, unfold two_pt_seg at hx, simp at hx,
  rcases hx.2 with hxd | hxb | hdxb,
  rw hxd at hx, exact absurd hx.1 this.2.1,
  rw hxb at hx, exact absurd hx.1 this.2.2,
  have hxl : x ∈ l,
    rcases between_col hdxb with ⟨n, hn, hdn, hxn, hbn⟩,
    rw two_pt_one_line hn hl hbd ⟨hbn, hdn⟩ ⟨hbl, hdl⟩ at hxn, exact hxn,
  have hcel : (c-ₗe) ≠ l,
    intro hcel, rw ←hcel at hdl, exact absurd hdl this.2.1,
  rw [←two_line_one_pt (line_in_lines hce) hl hcel (pt_right_in_line c e) hel hx.1 hxl,
    between_symm] at hdxb,
  exfalso, exact between_contra.1 ⟨hbde, hdxb⟩
end
import organised.incidence.basic
import set_theory.zfc

open_locale classical

/--An incidence order geometry is an incidence geometry with betweenness, a ternary relation
for `pts`. `is_between a b c` means `b` is between `a` and `c`, restricted by some axioms :
B1 : If a point is between the other two, they are collinear.
B2 : We can extend two distinct points.
B3 : Given 3 distinct points, exactly one of them is between the other two.
B4 : Pasch's axiom. `a`, `b`, `c` are noncollinear and for a line `l` not containing any of them,
     if `l` contains a points between `a` and `b`, it contains a points either between `a` and
     `c` or between `b` and `c`.
-/
class incidence_order_geometry extends incidence_geometry :=
(is_between : pts → pts → pts → Prop)
(B1 : ∀ {a b c : pts}, is_between a b c → is_between c b a
                        ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ collinear a b c)
(B2 : ∀ {a b : pts}, a ≠ b → ∃ c : pts, is_between a b c)
(B3 : (∀ {a b c : pts}, ∀ {l : set pts}, l ∈ lines → a ∈ l ∧ b ∈ l ∧ c ∈ l →
(a ≠ b → a ≠ c → b ≠ c → is_between a b c ∨ is_between a c b ∨ is_between b a c)) ∧
∀ a b c : pts, ¬(is_between a b c ∧ is_between a c b)
∧ ¬(is_between a b c ∧ is_between b a c) ∧ ¬(is_between a c b ∧ is_between b a c))
(B4 : ∀ {a b c : pts} (l ∈ lines),
      (noncollinear a b c) → a ∉ l → b ∉ l → c ∉ l
      → (∃ d : pts, is_between a d b ∧ d ∈ l) →
      (∃ p : pts, p ∈ l ∧ (is_between a p c ∨ is_between b p c))
      ∧ ∀ p q : pts, p ∈ l → q ∈ l → ¬(is_between a p c ∧ is_between b q c))

variable [B : incidence_order_geometry]

open incidence_geometry incidence_order_geometry

include B

lemma is_between_symm (a b c : pts) :
is_between a b c ↔ is_between c b a := iff.intro (λ h, (B1 h).1) (λ h, (B1 h).1)

lemma is_between_neq {a b c : pts} (h : is_between a b c) :
(a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) := ⟨(B1 h).2.1, (B1 h).2.2.1, (B1 h).2.2.2.1⟩

lemma is_between_collinear {a b c : pts}
(h : is_between a b c) : collinear a b c := (B1 h).2.2.2.2

lemma is_between_extend {a b : pts} (h : a ≠ b) :
∃ c : pts, is_between a b c := B2 h

lemma is_between_tri {a b c : pts} (habc : collinear a b c) (hab : a ≠ b) (hac : a ≠ c)
(hbc : b ≠ c) : is_between a b c ∨ is_between a c b ∨ is_between b a c :=
by { rcases habc with ⟨l, hl, habc⟩, exact B3.1 hl habc hab hac hbc }

lemma is_between_contra {a b c : pts} :
  ¬(is_between a b c ∧ is_between a c b)
∧ ¬(is_between a b c ∧ is_between b a c)
∧ ¬(is_between a c b ∧ is_between b a c) := B3.2 a b c

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
  intro haxa, exact absurd rfl (is_between_neq haxa).2.1
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
  apply set.union_subset,
  intros c hc, simp at hc,
  exact collinear_in13 (is_between_collinear hc) hab,
  intros x hx, simp at hx, cases hx with hx hx; rw hx,
  exact hal, exact hbl
end

lemma segment_two_pt (s : segment) : ∃ a b : pts, s = (a-ₛb) :=
begin
  induction s with inside in_eq,
  rcases in_eq with ⟨a, b, h⟩, use [a, b],
  unfold two_pt_segment, simp only, exact h
end

theorem pasch {a b c : pts} (habc : noncollinear a b c) {l : set pts} (hl : l ∈ lines) :
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
  have hac := (noncollinear_neq habc).2.1,
  have hbc := (noncollinear_neq habc).2.2,
  cases is_between_extend hac with d hacd,
  have had := (is_between_neq hacd).2.1,
  have hadb : noncollinear a d b,
    from collinear_noncollinear (is_between_collinear hacd) (noncollinear23 habc) had,
  have hbd := (noncollinear_neq hadb).2.2.symm,
  have hcd := (is_between_neq hacd).2.2,
  cases is_between_extend hbd with e hbde,
  have hce : c ≠ e,
    intro hce, rw ←hce at hbde,
    rcases (is_between_collinear hbde) with ⟨l, hl, hbl, hdl, hcl⟩,
    rcases (is_between_collinear hacd) with ⟨m, hm, ham, hcm, hdm⟩,
    rw two_pt_one_line hm hl hcd ⟨hcm, hdm⟩ ⟨hcl, hdl⟩ at ham,
    exact habc ⟨l, hl, ham, hbl, hcl⟩,
  have hde : d ≠ e, from (is_between_neq hbde).2.2,
  have hbe : b ≠ e, from (is_between_neq hbde).2.1,
  rcases (is_between_collinear hbde) with ⟨l, hl, hbl, hdl, hel⟩,
  rcases (is_between_collinear hacd) with ⟨m, hm, ham, hcm, hdm⟩,
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
  rw [←two_line_one_pt (line_in_lines hce) hl hcel (pt_right_in_line c e) hel hx.1 hxl,
    is_between_symm] at hdxb,
  exfalso, exact is_between_contra.1 ⟨hbde, hdxb⟩
end
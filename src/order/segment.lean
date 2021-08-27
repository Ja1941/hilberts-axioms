/-
Copyright (c) 2021 Tianchen Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianchen Zhao
-/
import incidence.basic

/-!
# Order on incidence geometry and segments

This file formalises betweenness based on `incidence_geometry`, defines line segments
and proves some important lemmas such as Pasch's.

## Main definitions

* `incidence_order_geometry` is a class extended by `incidence_geometry` and defines
  a ternary relation `between` satisfying some axioms.

* `seg`, with notation `-ₛ`, is the unique segment determined by the given two points.

## References

* See [Geometry: Euclid and Beyond]

-/

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
∀ a b c : pts, ¬(between a b c ∧ between b a c)
∧ ¬(between a b c ∧ between a c b) ∧ ¬(between b a c ∧ between a c b))
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
  ¬(between a b c ∧ between b a c)
∧ ¬(between a b c ∧ between a c b)
∧ ¬(between b a c ∧ between a c b) := B3.2 a b c

/--A type whose inside is a set containing two points and points between them. -/
structure seg := (inside : set pts)
(in_eq : ∃ a b : pts, inside = {x : pts | between a x b} ∪ {a, b})

/--A seg is proper if its inside is not a singleton.
Equivalently, `a` and `b` are distinct. -/
def seg_proper (s : seg) : Prop :=
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

lemma seg_proper_iff_neq {a b : pts} :
seg_proper (a-ₛb) ↔ a ≠ b :=
begin
  split; intro h,
  { by_contra hab, push_neg at hab,
    rw hab at h, exact h b (seg_singleton b) },
  { intros x hf,
    have := pt_left_in_seg a b, rw hf at this,
    simp at this, rw this at h,
    have := pt_right_in_seg a b, rw hf at this,
    simp at this, rw this at h,
    exact h rfl }
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

lemma seg_in_neq {a b x : pts} (hxa : x ≠ a) (hxb : x ≠ b) (hx : x ∈ (a-ₛb).inside) :
between a x b :=
begin
  rcases hx with hx | hf | hf,
  exact hx, exact absurd hf hxa, exact absurd hf hxb
end

/--This is in fact just a rephrase of B4. -/
theorem pasch {a b c : pts} (habc : noncol a b c) {l : set pts} (hl : l ∈ lines)
(hal : a ∉ l) (hbl : b ∉ l) (hcl : c ∉ l) (hlab : l ♥ (a-ₛb).inside) :
((l ♥ (a-ₛc).inside) ∨ (l ♥ (b-ₛc).inside)) ∧ ¬((l ♥ (a-ₛc).inside) ∧ (l ♥ (b-ₛc).inside)) :=
begin
  rcases hlab with ⟨d, hdl, hadb⟩,
  have hda : d ≠ a,
    intro hf, rw hf at hdl, exact hal hdl,
  have hdb : d ≠ b,
    intro hf, rw hf at hdl, exact hbl hdl,
  replace hadb := seg_in_neq hda hdb hadb,
  rcases (B4 l hl habc hal hbl hcl ⟨d, hadb, hdl⟩) with ⟨⟨p, hpl, h₁⟩, h₂⟩,
  split,
  { cases h₁,
    left, exact ⟨p, hpl, by {left, exact h₁}⟩,
    right, exact ⟨p, hpl, by {left, exact h₁}⟩ },
  { rintros ⟨⟨p, hpl, hapc⟩, ⟨q, hql, hbqc⟩⟩,
    have : ∀ x : pts, x ∈ l → x ≠ a ∧ x ≠ b ∧ x ≠ c,
      intros x hxl,
      refine ⟨_, _, _⟩; intro hf; rw hf at hxl,
      exact hal hxl, exact hbl hxl, exact hcl hxl,
    replace hapc := seg_in_neq (this p hpl).1 (this p hpl).2.2 hapc,
    replace hbqc := seg_in_neq (this q hql).2.1 (this q hql).2.2 hbqc,
    exact (h₂ p q hpl hql) ⟨hapc, hbqc⟩ }
end

lemma two_pt_between {a b : pts} (hab : a ≠ b) : ∃ c : pts, between a c b :=
begin
  cases noncol_exist hab with c habc,
  have hac := (noncol_neq habc).2.1,
  cases between_extend hac with d hacd,
  have had := (between_neq hacd).2.1,
  have hcd := (between_neq hacd).2.2,
  have hbd : b ≠ d,
    intro hf, rw hf at habc,
    exact (noncol23 habc) (between_col hacd),
  cases between_extend hbd with e hbde,
  have hbe := (between_neq hbde).2.1,
  have hde := (between_neq hbde).2.2,
  have hadb := col_noncol (between_col hacd) (noncol23 habc) had,
  have hce : c ≠ e,
    intro hf, rw ←hf at hbde,
    apply col_noncol (col12 (between_col hacd)) (noncol132 habc) hcd,
    exact col13 (between_col hbde),
  have hbea := col_noncol (between_col hbde) (noncol13 hadb) hbe,
  have heda := col_noncol (col132 (between_col hbde)) (noncol12 hbea) hde.symm,
  have hace := col_noncol (col23 (between_col hacd)) (noncol13 heda) hac,
  have hdce := col_noncol (col132 (between_col hacd)) (noncol123 heda) hcd.symm,
  have hebc := col_noncol (col13 (between_col hbde)) (noncol132 hdce) hbe.symm,
  have : ((c-ₗe)♥(a-ₛd).inside), from ⟨c, pt_left_in_line c e, by {left, exact hacd}⟩,
  cases (pasch hadb (line_in_lines hce) (noncol_in23 hace) (noncol_in23 hdce)
    (noncol_in31 hebc) this).1,
  { cases h with x hx,
    rcases hx.2 with haxb | hf | hf,
    exact ⟨x, haxb⟩,
    rw hf at hx, exact absurd hx.1 (noncol_in23 hace),
    simp at hf, rw hf at hx, exact absurd hx.1 (noncol_in31 hebc) },
  { cases h with x hx,
    have : x = e,
      apply two_line_one_pt (line_in_lines hce) (line_in_lines hbd.symm) _ hx.1
        ((seg_in_line d b) hx.2) (pt_right_in_line c e) (col_in21 (between_col hbde) hbd.symm),
      intro hf, apply noncol_in31 hebc, rw hf, exact pt_right_in_line d b,
    rw this at hx, rcases hx.2 with hf | hf | hf,
    { rw between_symm at hbde, exfalso,
      apply between_contra.1 ⟨hf, hbde⟩ },
    exact absurd hf.symm hde,
    exact absurd hf hbe.symm }
end
import algebra.support
import set_theory.zfc
import tactic.wlog
import tactic

open set
open_locale classical

universes u

class incidence_geometry :=
(pts : Type u)
--A line is defined as a set of points, 'lines' here is the set of all lines
(lines : set (set pts))
--two distinct points uniquely define a line
(I1 : ∀ {a b : pts}, a ≠ b → ∃ l ∈ lines,
 a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l))
--every line contains at least two points
(I2 : ∀ l ∈ lines, ∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l)
--there exists three noncollinear points
(I3 : ∃ a b c : pts, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l))

section incidence_geometry_API

open incidence_geometry

variable [I : incidence_geometry]

include I

def collinear (a b c : pts) : Prop :=
∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

def line (a b : pts) (hab : a ≠ b) : set pts := {x : pts | collinear a b x}

#check @line

notation a`-ₗ`b := line a b

variables (a b : pts) [hab : a ≠ b]
#check line a b _

lemma line_in_lines (x y : pts) (hxy : x ≠ y) : (line x y _) = ∅ :=
begin
  sorry,
end

def cao (a : ℕ) [ha : a = 0] : ℕ := 0

#check cao 

end incidence_geometry_API
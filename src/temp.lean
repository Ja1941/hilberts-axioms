import congruence.basic
import data.zmod.basic
import data.real.basic
import data.real.sqrt
import group_theory.group_action.defs
import analysis.normed_space.inner_product
import analysis.normed_space.pi_Lp

example (f : (fin 2) → ℝ) :
finset.univ.sum (λ (x : fin 2), f x) = f 0 + f 1 :=
begin
  rw [fin.sum_univ_succ, fin.sum_univ_succ],
end
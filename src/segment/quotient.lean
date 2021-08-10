import main -- this should say "import segment.basic" or somethi

variable [C : incidence_order_congruence_geometry]

include C

open incidence_geometry -- for `pts` because it's not in root namespace

open incidence_order_geometry -- for `is_between`

open incidence_order_congruence_geometry -- for `segment_congr`

#check segment

variables (a b : pts)

#check a -ₛ b -- segment

variables (x y z w : pts)

variables (s t : segment)

#check s ≅ₛ t 

#print notation ⟦ ⟧ -- quotient.mk

instance : setoid segment :=
{ r := segment_congr,
  iseqv := ⟨segment_congr_refl, 
            λ _ _, segment_congr_symm,
            λ _ _ _, segment_congr_trans⟩ }

def pos_reals := quotient segment.setoid

namespace nonneg_reals

noncomputable def random_point := classical.some I3

#check trunc

#check quotient.lift


noncomputable def zero : nonneg_reals := ⟦(random_point -ₛ random_point)⟧

#check trunc.lift

def zero' : nonneg_reals := trunc.lift (λ P, ⟦(P -ₛ P)⟧ : pts → nonneg_reals)
( begin
    intros a b,
    rw quotient.eq,
    change ((a -ₛ a) ≅ₛ (b -ₛ b)), -- notation precedence issue
    
    sorry
  end) sorry
end nonneg_reals



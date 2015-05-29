/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .extra .hom .perm

namespace group
open finset algebra

section def
variables {G S : Type}
variable [g : group G]
include g
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS
variable [hom : hom_class G (perm S)]
variable [deceqG : decidable_eq G]
include deceqG
variable H : finset G
variable [h : is_subgroup (ts H)]

local attribute perm.f [coercion]

definition subg_orbit (a : S) : finset S := image (move_by a) (image hom H)
definition subg_stab (a : S) : finset G := {f ∈ H | hom f a = a} 

end def

end group

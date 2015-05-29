/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .extra .hom .perm .finsubg

namespace group
open finset algebra function

section def
variables {G S : Type}
variable [ambient_g : group G]
include ambient_g
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS
variable [hom : hom_class G (perm S)]
variable [deceqG : decidable_eq G]
include deceqG
variable H : finset G
variable [subgH : is_finsubg H]

local attribute perm.f [coercion]

definition subg_orbit (a : S) : finset S := image (move_by a) (image hom H)
definition subg_stab [reducible] (a : S) : finset G := {f ∈ H | hom f a = a} 

private lemma Hom : is_hom hom := @hom_class.is_hom G (perm S) ambient_g _ _

include subgH

lemma subg_stab_closed {a : S}
    : let stab := subg_stab H a in ∀ f g : G, f ∈ stab → g ∈ stab → f*g ∈ stab :=
      take f g, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assume Pgstab, assert Pg : hom g a = a, from of_mem_filter Pgstab,
      assert Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = perm.f ((hom f) * (hom g)) a : Hom
        ... = ((hom f) ∘ (hom g)) a : rfl
        ... = (hom f) a : Pg
        ... = a : Pf,
      assert PfginH : (f*g) ∈ H, from @is_finsubg.mul_closed G _ H _ f g (mem_of_mem_filter Pfstab) (mem_of_mem_filter Pgstab),
      mem_filter_of_mem PfginH Pfg

end def

end group

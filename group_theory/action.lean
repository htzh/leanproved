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
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS

variable hom : G → perm S
variable [of_hom : is_hom_class hom]

variable [deceqG : decidable_eq G]
include deceqG
variable H : finset G
variable [subgH : is_finsubg H]

local attribute perm.f [coercion]

definition subg_orbit (a : S) : finset S := image (move_by a) (image hom H)
definition subg_stab [reducible] (a : S) : finset G := {f ∈ H | hom f a = a} 

check @subg_stab
include subgH
include of_hom

lemma subg_stab_closed {a : S}
    : let stab := subg_stab hom H a in ∀ f g : G, f ∈ stab → g ∈ stab → f*g ∈ stab :=
      take f g, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assume Pgstab, assert Pg : hom g a = a, from of_mem_filter Pgstab,
      assert Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = perm.f ((hom f) * (hom g)) a : is_hom hom
        ... = ((hom f) ∘ (hom g)) a : rfl
        ... = (hom f) a : Pg
        ... = a : Pf,
      assert PfginH : (f*g) ∈ H, from finsubg_mul_closed H f g (mem_of_mem_filter Pfstab) (mem_of_mem_filter Pgstab),
      mem_filter_of_mem PfginH Pfg

lemma subg_stab_has_one {a : S} : 1 ∈ subg_stab hom H a :=
      assert P : hom 1 a = a, from calc
        hom 1 a = (1 : perm S) a : hom_map_one hom ▸ eq.refl (hom 1 a)
        ... = a : rfl,
      assert PoneinH : 1 ∈ H, from finsubg_has_one H,
      mem_filter_of_mem PoneinH P

end def

end group

/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .extra .hom .perm .finsubg

namespace group
open finset algebra function

local attribute perm.f [coercion]

section def
variables {G S : Type}
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS

definition subg_orbit (hom : G → perm S) (H : finset G) (a : S) : finset S :=
           image (move_by a) (image hom H)

variable [deceqG : decidable_eq G]
include deceqG -- required by {x ∈ H |p x} filtering

definition subg_stab (hom : G → perm S) (H : finset G) (a : S) : finset G :=
           {f ∈ H | hom f a = a} 

end def

section stab_is_subg
check @subg_stab
variables {G S : Type}
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS
variable [deceqG : decidable_eq G]
include deceqG

-- these are already specified by subg_stab hom H a
variables {hom : G → perm S} {H : finset G} {a : S}

variable [of_hom : is_hom_class hom]
include of_hom
variable [subgH : is_finsubg H]
include subgH

lemma subg_stab_closed : finset_mul_closed_on (subg_stab hom H a) :=
      take f g, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assume Pgstab, assert Pg : hom g a = a, from of_mem_filter Pgstab,
      assert Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = perm.f ((hom f) * (hom g)) a : is_hom hom
        ... = ((hom f) ∘ (hom g)) a : rfl
        ... = (hom f) a : Pg
        ... = a : Pf,
      assert PfginH : (f*g) ∈ H, from finsubg_mul_closed H f g (mem_of_mem_filter Pfstab) (mem_of_mem_filter Pgstab),
      mem_filter_of_mem PfginH Pfg

lemma subg_stab_has_one : 1 ∈ subg_stab hom H a :=
      assert P : hom 1 a = a, from calc
        hom 1 a = (1 : perm S) a : hom_map_one hom ▸ eq.refl (hom 1 a)
        ... = a : rfl,
      assert PoneinH : 1 ∈ H, from finsubg_has_one H,
      mem_filter_of_mem PoneinH P

lemma subg_stab_has_inv : finset_has_inv (subg_stab hom H a) :=
      take f, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assert Pfinv : hom f⁻¹ a = a, from calc
        hom f⁻¹ a = hom f⁻¹ ((hom f) a) : Pf
        ... = perm.f ((hom f⁻¹) * (hom f)) a : rfl
        ... = hom (f⁻¹ * f) a : is_hom hom
        ... = hom 1 a : mul.left_inv
        ... = (1 : perm S) a : hom_map_one hom,
      assert PfinvinH : f⁻¹ ∈ H, from finsubg_has_inv H f (mem_of_mem_filter Pfstab),
      mem_filter_of_mem PfinvinH Pfinv

definition subg_stab_is_finsubg [instance] :
           is_finsubg (subg_stab hom H a) :=
           is_finsubg.mk subg_stab_has_one subg_stab_closed subg_stab_has_inv

check @subg_stab_is_finsubg       
end stab_is_subg

section orbit_stabilizer

end orbit_stabilizer

end group

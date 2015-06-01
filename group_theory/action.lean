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

definition orbit (hom : G → perm S) (H : finset G) (a : S) : finset S :=
           image (move_by a) (image hom H)

variable [deceqG : decidable_eq G]
include deceqG -- required by {x ∈ H |p x} filtering

definition moverset (hom : G → perm S) (H : finset G) (a b : S) : finset G :=
           {f ∈ H | hom f a = b}

definition stab (hom : G → perm S) (H : finset G) (a : S) : finset G :=
           {f ∈ H | hom f a = a} 

end def

section stab_is_subg
check @stab
variables {G S : Type}
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS
variable [deceqG : decidable_eq G]
include deceqG

-- these are already specified by stab hom H a
variables {hom : G → perm S} {H : finset G} {a : S}

variable [Hom : is_hom_class hom]
include Hom

lemma exists_of_orbit {b : S} : b ∈ orbit hom H a → ∃ h, h ∈ H ∧ hom h a = b :=
      assume Pb,
      obtain p (Pp : p ∈ image hom H ∧ move_by a p = b), from exists_of_mem_image Pb,
      obtain h (Ph : h ∈ H ∧ hom h = p), from exists_of_mem_image (and.left Pp),
      assert Phab : hom h a = b, from calc
        hom h a = p a : eq.symm (and.right Ph)
        ... = b : and.right Pp,
      exists.intro h (and.intro (and.left Ph) Phab)

lemma stab_lmul {f g : G} : g ∈ stab hom H a → hom (f*g) a = hom f a :=
      assume Pgstab,
      assert Pg : hom g a = a, from of_mem_filter Pgstab, calc
        hom (f*g) a = perm.f ((hom f) * (hom g)) a : is_hom hom
        ... = ((hom f) ∘ (hom g)) a : rfl
        ... = (hom f) a : Pg

lemma stab_subset : stab hom H a ⊆ H :=
      begin
        apply subset_of_forall, intro f Pfstab, apply mem_of_mem_filter Pfstab
      end

lemma reverse_move {h g : G} : g ∈ moverset hom H a (hom h a) → hom (h⁻¹*g) a = a :=
      assume Pg,
      assert Pga : hom g a = hom h a, from of_mem_filter Pg, calc
      hom (h⁻¹*g) a = perm.f ((hom h⁻¹) * (hom g)) a : is_hom hom
      ... = ((hom h⁻¹) ∘ hom g) a : rfl
      ... = ((hom h⁻¹) ∘ hom h) a : eq.symm Pga ▸ eq.refl (((hom h⁻¹) ∘ hom h) a)
      ... = perm.f ((hom h⁻¹) * hom h) a : rfl
      ... = perm.f ((hom h)⁻¹ * hom h) a : hom_map_inv hom h
      ... = perm.f (1 : perm S) a :  mul.left_inv (hom h)
      ... = a : rfl
 
variable [subgH : is_finsubg H]
include subgH

lemma subg_moverset_inj_on_orbit : set.inj_on (moverset hom H a) (ts (orbit hom H a)) :=
      take b1 b2,
      assume Pb1, obtain h1 Ph1, from exists_of_orbit Pb1,
      assert Ph1b1 : h1 ∈ moverset hom H a b1,
        from mem_filter_of_mem (and.left Ph1) (and.right Ph1),
      assume Psetb2 Pmeq, begin
      rewrite [-(and.right Ph1)],
      rewrite Pmeq at Ph1b1,
      apply of_mem_filter Ph1b1
      end

lemma subg_stab_of_move {h g : G} :
      h ∈ H → g ∈ moverset hom H a (hom h a) → h⁻¹*g ∈ stab hom H a :=
      assume Ph Pg,
      assert Phinvg : h⁻¹*g ∈ H, from begin
        apply finsubg_mul_closed H,
          apply finsubg_has_inv H, apply Ph,
          apply mem_of_mem_filter Pg
        end,
      mem_filter_of_mem Phinvg (reverse_move Pg)
      
lemma subg_stab_closed : finset_mul_closed_on (stab hom H a) :=
      take f g, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assume Pgstab,
      assert Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = (hom f) a : stab_lmul Pgstab
        ... = a : Pf,
      assert PfginH : (f*g) ∈ H,
        from finsubg_mul_closed H f g (mem_of_mem_filter Pfstab) (mem_of_mem_filter Pgstab),
      mem_filter_of_mem PfginH Pfg

lemma subg_stab_has_one : 1 ∈ stab hom H a :=
      assert P : hom 1 a = a, from calc
        hom 1 a = (1 : perm S) a : hom_map_one hom ▸ eq.refl (hom 1 a)
        ... = a : rfl,
      assert PoneinH : 1 ∈ H, from finsubg_has_one H,
      mem_filter_of_mem PoneinH P

lemma subg_stab_has_inv : finset_has_inv (stab hom H a) :=
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
           is_finsubg (stab hom H a) :=
           is_finsubg.mk subg_stab_has_one subg_stab_closed subg_stab_has_inv

lemma subg_lcoset_eq_moverset {h : G} :
      h ∈ H → fin_lcoset (stab hom H a) h = moverset hom H a (hom h a) :=
      assume Ph, ext (take g, iff.intro
      (assume Pl, obtain f (Pf : f ∈ stab hom H a ∧ h*f = g), from exists_of_mem_image Pl,
      assert Pfstab : hom f a = a, from of_mem_filter (and.left Pf),
      assert PginH : g ∈ H, begin
        rewrite [-(and.right Pf)],
        apply finsubg_mul_closed H,
          apply Ph,
          apply mem_of_mem_filter (and.left Pf)
        end,
      assert Pga : hom g a = hom h a, from calc
        hom g a = hom (h*f) a : (and.right Pf) ▸ eq.refl (hom (h*f) a) 
        ... = hom h a : stab_lmul (and.left Pf),
      mem_filter_of_mem PginH Pga)
      (assume Pr, begin
       rewrite [↑fin_lcoset, mem_image_iff],
       apply exists.intro (h⁻¹*g),
       apply and.intro,
         exact subg_stab_of_move Ph Pr,
         apply mul_inv_cancel_left
       end))

lemma subg_moverset_of_orbit_is_lcoset_of_stab (b : S) :
      b ∈ orbit hom H a → ∃ h, h ∈ H ∧ fin_lcoset (stab hom H a) h = moverset hom H a b :=
      assume Porb,
      obtain p (Pp : p ∈ image hom H ∧ move_by a p = b), from exists_of_mem_image Porb,
      obtain h (Ph : h ∈ H ∧ hom h = p), from exists_of_mem_image (and.left Pp),
      assert Phab : hom h a = b, from by rewrite [and.right Ph]; exact and.right Pp,
      exists.intro h (and.intro (and.left Ph) (Phab ▸ subg_lcoset_eq_moverset (and.left Ph)))

lemma subg_lcoset_of_stab_is_moverset_of_orbit (h : G) :
      h ∈ H → ∃ b, b ∈ orbit hom H a ∧ moverset hom H a b = fin_lcoset (stab hom H a) h :=
      assume Ph,
      have Pha : (hom h a) ∈ orbit hom H a, by
        apply mem_image_of_mem; apply mem_image_of_mem; exact Ph,
      exists.intro (hom h a) (and.intro Pha (eq.symm (subg_lcoset_eq_moverset Ph)))
      
lemma subg_moversets_of_orbit_eq_stab_lcosets :
      image (moverset hom H a) (orbit hom H a) = fin_lcosets (stab hom H a) H :=
      ext (take s, iff.intro
      (assume Pl, obtain b Pb, from exists_of_mem_image Pl,
      obtain h Ph, from subg_moverset_of_orbit_is_lcoset_of_stab b (and.left Pb), begin
      rewrite [↑fin_lcosets, mem_image_eq],
      rewrite (and.right Pb) at Ph,
      exact exists.intro h Ph
      end)
      (assume Pr, obtain h Ph, from exists_of_mem_image Pr,
      obtain b Pb, from @subg_lcoset_of_stab_is_moverset_of_orbit G S ambientG finS deceqS deceqG hom H a Hom subgH h (and.left Ph), begin
      rewrite [mem_image_eq],
      apply exists.intro b,
      rewrite (and.right Ph) at Pb,
      exact Pb
      end))

open nat
theorem orbit_stabilizer : card H = card (orbit hom H a) * card (stab hom H a) := sorry

end stab_is_subg

section orbit_stabilizer

end orbit_stabilizer

end group

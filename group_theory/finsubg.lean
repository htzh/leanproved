/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

-- develop the concept of finite subgroups based on finsets so that the properties
-- can be used directly without translating from the set based theory first

import data algebra.group .subgroup
open function algebra finset
-- ⁻¹ in eq.ops conflicts with group ⁻¹
open eq.ops

namespace group
open ops

section subg
-- we should be able to prove properties using finsets directly
variable {G : Type}
variable [ambientG : group G]
include ambientG

definition finset_mul_closed_on [reducible] (H : finset G) : Prop :=
           ∀ (x y : G), x ∈ H → y ∈ H → x * y ∈ H
definition finset_has_inv (H : finset G) : Prop :=
           ∀ (a : G), a ∈ H → a⁻¹ ∈ H
structure is_finsubg [class] (H : finset G) : Type :=
          (has_one : 1 ∈ H)
          (mul_closed : finset_mul_closed_on H)
          (has_inv : finset_has_inv H)

definition univ_is_finsubg [instance] [finG : fintype G] : is_finsubg (@finset.univ G _) :=
is_finsubg.mk !mem_univ (λ x y Px Py, !mem_univ) (λ a Pa, !mem_univ)

lemma finsubg_has_one (H : finset G) [h : is_finsubg H] : 1 ∈ H :=
      @is_finsubg.has_one G _ H h
lemma finsubg_mul_closed (H : finset G) [h : is_finsubg H] : finset_mul_closed_on H :=
      @is_finsubg.mul_closed G _ H h
lemma finsubg_has_inv (H : finset G) [h : is_finsubg H] : finset_has_inv H :=
      @is_finsubg.has_inv G _ H h

variable [deceqG : decidable_eq G]
include deceqG

definition finsubg_to_subg [instance] {H : finset G} [h : is_finsubg H]
         : is_subgroup (ts H) :=
           is_subgroup.mk
           (mem_eq_mem_to_set H 1 ▸ finsubg_has_one H)
           (take x y, begin repeat rewrite -mem_eq_mem_to_set,
             apply finsubg_mul_closed H end)
           (take a, begin repeat rewrite -mem_eq_mem_to_set,
             apply finsubg_has_inv H end)
end subg

section lagrange
open set
-- this is work based on is_subgroup. will test is_finsubg somewhere else first.
variable {A : Type}
variable [deceq : decidable_eq A]
include deceq
variable [s : group A]
include s

definition fin_lcoset (H : finset A) (a : A) := finset.image (lmul_by a) H
definition fin_lcosets (H G : finset A) := image (fin_lcoset H) G

variable {H : finset A}

lemma fin_lcoset_eq (a : A) : ts (fin_lcoset H a) = a ∘> (ts H) := calc
      ts (fin_lcoset H a) = coset.l a (ts H) : to_set_image
      ... = a ∘> (ts H) : glcoset_eq_lcoset
lemma fin_lcoset_card (a : A) : card (fin_lcoset H a) = card H :=
      card_image_eq_of_inj_on (lmul_inj_on a (ts H))
lemma fin_lcosets_card_eq {G : finset A} : ∀ gH, gH ∈ fin_lcosets H G → card gH = card H :=
      take gH, assume Pcosets, obtain g Pg, from exists_of_mem_image Pcosets,
      and.right Pg ▸ fin_lcoset_card g

variable [is_subgH : is_subgroup (to_set H)]
include is_subgH

lemma fin_lcoset_same (x a : A) : x ∈ (fin_lcoset H a) = (fin_lcoset H x = fin_lcoset H a) :=
      begin
        rewrite mem_eq_mem_to_set,
        rewrite [eq_eq_to_set_eq, *(fin_lcoset_eq x), fin_lcoset_eq a],
        exact (subg_lcoset_same x a)
      end
lemma fin_mem_lcoset (g : A) : g ∈ fin_lcoset H g :=
      have P : g ∈ g ∘> ts H, from and.left (subg_in_coset_refl g),
      assert P1 : g ∈ ts (fin_lcoset H g), from eq.symm (fin_lcoset_eq g) ▸ P,
      eq.symm (mem_eq_mem_to_set _ g) ▸ P1
lemma fin_lcoset_subset {S : finset A} (Psub : S ⊆ H) : ∀ x, x ∈ H → fin_lcoset S x ⊆ H :=
      assert Psubs : set.subset (ts S) (ts H), from subset_eq_to_set_subset S H ▸ Psub,
      take x, assume Pxs : x ∈ ts H,
      assert Pcoset : set.subset (x ∘> ts S) (ts H), from subg_lcoset_subset_subg Psubs x Pxs,
      by rewrite [subset_eq_to_set_subset, fin_lcoset_eq x]; exact Pcoset

variable {G : finset A}
variable [is_subgG : is_subgroup (to_set G)]
include is_subgG

open finset.partition

definition fin_lcoset_partition_subg (Psub : H ⊆ G) :=
      partition.mk G (fin_lcoset H) fin_lcoset_same
        (restriction_imp_union (fin_lcoset H) fin_lcoset_same (fin_lcoset_subset Psub))

open nat

theorem lagrange_theorem (Psub : H ⊆ G) : card G = card (fin_lcosets H G) * card H := calc
        card G = nat.Sum (fin_lcosets H G) card : class_equation (fin_lcoset_partition_subg Psub)
        ... = nat.Sum (fin_lcosets H G) (λ x, card H) : nat.Sum_ext (take g P, fin_lcosets_card_eq g P)
        ... = card (fin_lcosets H G) * card H : Sum_const_eq_card_mul

end lagrange

section lcoset_fintype
open fintype list subtype

section

lemma dinj_tag {A : Type} (P : A → Prop) : dinj P tag :=
take a₁ a₂ Pa₁ Pa₂ Pteq, subtype.no_confusion Pteq (λ Pe Pqe, Pe)

end

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

variables H : finset G

definition is_fin_lcoset [reducible] (S : finset G) : Prop := ∃ g, fin_lcoset H g = S

definition list_lcosets : list (finset G) := erase_dup (map (fin_lcoset H) (elems G))

definition lcoset_type : Type := {S : finset G | is_fin_lcoset H S}

definition all_lcosets : list (lcoset_type H) :=
dmap (is_fin_lcoset H) tag (list_lcosets H)

variable {H}

lemma is_lcoset_of_mem_list_lcosets {S : finset G}
  : S ∈ list_lcosets H → is_fin_lcoset H S :=
assume Pin, obtain g Pg, from exists_of_mem_map (mem_of_mem_erase_dup Pin),
exists.intro g (and.right Pg)

lemma mem_list_lcosets_of_is_lcoset {S : finset G}
  : is_fin_lcoset H S → S ∈ list_lcosets H :=
assume Plcoset, obtain g Pg, from Plcoset,
Pg ▸ mem_erase_dup (mem_map _ (complete g))

lemma fin_lcosets_eq :
  fin_lcosets H univ = to_finset_of_nodup (list_lcosets H) !nodup_erase_dup :=
ext (take S, iff.intro
  (λ Pimg, obtain g Pg, from exists_of_mem_image Pimg,
    mem_list_lcosets_of_is_lcoset (exists.intro g (and.right Pg)))
  (λ Pl, obtain g Pg, from is_lcoset_of_mem_list_lcosets Pl,
    mem_image_of_mem_of_eq !mem_univ Pg))

lemma length_all_lcosets : length (all_lcosets H) = card (fin_lcosets H univ) :=
eq.trans
  (show length (all_lcosets H) = length (list_lcosets H), from
    assert Pmap : map elt_of (all_lcosets H) = list_lcosets H, from
      map_dmap_of_inv_of_pos (λ S P, rfl) (λ S, is_lcoset_of_mem_list_lcosets),
    by rewrite[-Pmap, length_map])
  (by rewrite fin_lcosets_eq)

definition lcoset_fintype [instance] : fintype (lcoset_type H) :=
fintype.mk (all_lcosets H)
  (dmap_nodup_of_dinj (dinj_tag (is_fin_lcoset H)) !nodup_erase_dup)
  (take s, subtype.destruct s (take S, assume PS, mem_dmap PS (mem_list_lcosets_of_is_lcoset PS)))

lemma card_lcoset_type : card (lcoset_type H) = card (fin_lcosets H univ) :=
length_all_lcosets

open nat
variable [finsubgH : is_finsubg H]
include finsubgH

theorem lagrange_theorem' : card G = card (lcoset_type H) * card H :=
calc card G = card (fin_lcosets H univ) * card H : lagrange_theorem !subset_univ
        ... = card (lcoset_type H) * card H : card_lcoset_type

end lcoset_fintype

end group

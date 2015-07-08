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

lemma fin_lcoset_compose (a b : A) : fin_lcoset (fin_lcoset H b) a = fin_lcoset H (a*b) :=
to_set.inj (by rewrite [*fin_lcoset_eq, glcoset_compose])

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

variables {A : Type} [ambientA : group A] [finA : fintype A] [deceqA : decidable_eq A]
include ambientA deceqA finA

variables G H : finset A

definition is_fin_lcoset [reducible] (S : finset A) : Prop :=
  ∃ g, g ∈ G ∧ fin_lcoset H g = S

definition to_list : list A := list.filter (λ g, g ∈ G) (elems A)

definition list_lcosets : list (finset A) := erase_dup (map (fin_lcoset H) (to_list G))

definition lcoset_type [reducible] : Type := {S : finset A | is_fin_lcoset G H S}

definition all_lcosets : list (lcoset_type G H) :=
dmap (is_fin_lcoset G H) tag (list_lcosets G H)

variables {G H} [finsubgG : is_finsubg G]

include finsubgG

definition lcoset_lmul {g : A} (Pgin : g ∈ G) (S : lcoset_type G H)
  : lcoset_type G H :=
tag (fin_lcoset (elt_of S) g)
  (obtain f Pfin Pf, from has_property S,
  exists.intro (g*f)
    (by apply and.intro;
      exact finsubg_mul_closed G _ _ Pgin Pfin;
      rewrite [-Pf, -fin_lcoset_compose]))

lemma is_lcoset_of_mem_list_lcosets {S : finset A}
  : S ∈ list_lcosets G H → is_fin_lcoset G H S :=
assume Pin, obtain g Pgin Pg, from exists_of_mem_map (mem_of_mem_erase_dup Pin),
exists.intro g (and.intro (of_mem_filter Pgin) Pg)

lemma mem_list_lcosets_of_is_lcoset {S : finset A}
  : is_fin_lcoset G H S → S ∈ list_lcosets G H :=
assume Plcoset, obtain g Pgin Pg, from Plcoset,
Pg ▸ mem_erase_dup (mem_map _ (mem_filter_of_mem (complete g) Pgin))

lemma fin_lcosets_eq :
  fin_lcosets H G = to_finset_of_nodup (list_lcosets G H) !nodup_erase_dup :=
ext (take S, iff.intro
  (λ Pimg, mem_list_lcosets_of_is_lcoset (exists_of_mem_image Pimg))
  (λ Pl, obtain g Pg, from is_lcoset_of_mem_list_lcosets Pl,
    iff.elim_right !mem_image_iff (is_lcoset_of_mem_list_lcosets Pl)))

lemma length_all_lcosets : length (all_lcosets G H) = card (fin_lcosets H G) :=
eq.trans
  (show length (all_lcosets G H) = length (list_lcosets G H), from
    assert Pmap : map elt_of (all_lcosets G H) = list_lcosets G H, from
      map_dmap_of_inv_of_pos (λ S P, rfl) (λ S, is_lcoset_of_mem_list_lcosets),
    by rewrite[-Pmap, length_map])
  (by rewrite fin_lcosets_eq)

lemma lcoset_lmul_compose {f g : A} (Pf : f ∈ G) (Pg : g ∈ G) (S : lcoset_type G H) :
lcoset_lmul Pf (lcoset_lmul Pg S) = lcoset_lmul (finsubg_mul_closed G f g Pf Pg) S :=
subtype.eq !fin_lcoset_compose

lemma lcoset_lmul_one (S : lcoset_type G H) : lcoset_lmul !finsubg_has_one S = S :=
subtype.eq (to_set.inj (by rewrite [↑lcoset_lmul, fin_lcoset_eq, glcoset_id]))

lemma lcoset_lmul_inv {g : A} {Pg : g ∈ G} (S : lcoset_type G H) :
  lcoset_lmul (finsubg_has_inv G g Pg) (lcoset_lmul Pg S) = S :=
subtype.eq (to_set.inj begin
 esimp [lcoset_lmul],
 rewrite [fin_lcoset_compose, mul.left_inv, fin_lcoset_eq, glcoset_id]
end)

lemma lcoset_lmul_inj {g : A} {Pg : g ∈ G}:
  @injective (lcoset_type G H) _ (lcoset_lmul Pg) :=
injective_of_has_left_inverse (exists.intro (lcoset_lmul (finsubg_has_inv G g Pg)) lcoset_lmul_inv)

lemma card_elt_of_lcoset_type (S : lcoset_type G H) : card (elt_of S) = card H :=
obtain f Pfin Pf, from has_property S, Pf ▸ fin_lcoset_card f

definition lcoset_fintype [instance] : fintype (lcoset_type G H) :=
fintype.mk (all_lcosets G H)
  (dmap_nodup_of_dinj (dinj_tag (is_fin_lcoset G H)) !nodup_erase_dup)
  (take s, subtype.destruct s (take S, assume PS, mem_dmap PS (mem_list_lcosets_of_is_lcoset PS)))

lemma card_lcoset_type : card (lcoset_type G H) = card (fin_lcosets H G) :=
length_all_lcosets

open nat
variable [finsubgH : is_finsubg H]
include finsubgH

theorem lagrange_theorem' (Psub : H ⊆ G) : card G = card (lcoset_type G H) * card H :=
calc card G = card (fin_lcosets H G) * card H : lagrange_theorem Psub
        ... = card (lcoset_type G H) * card H : card_lcoset_type

lemma lcoset_disjoint {S₁ S₂ : lcoset_type G H} : S₁ ≠ S₂ → elt_of S₁ ∩ elt_of S₂ = ∅ :=
obtain f₁ Pfin₁ Pf₁, from has_property S₁,
obtain f₂ Pfin₂ Pf₂, from has_property S₂,
assume Pne, inter_eq_empty_of_disjoint (disjoint.intro
  take g, begin
  rewrite [-Pf₁, -Pf₂, *fin_lcoset_same],
  intro Pgf₁, rewrite [Pgf₁, Pf₁, Pf₂],
  intro Peq, exact absurd (subtype.eq Peq) Pne
  end )

lemma card_Union_lcosets (lcs : finset (lcoset_type G H)) :
  card (Union lcs elt_of) = card lcs * card H :=
calc card (Union lcs elt_of) = ∑ lc ∈ lcs, card (elt_of lc) : card_Union_of_disjoint lcs elt_of (λ (S₁ S₂ : lcoset_type G H) P₁ P₂ Pne, lcoset_disjoint Pne)
                         ... = ∑ lc ∈ lcs, card H : Sum_ext (take lc P, card_elt_of_lcoset_type _)
                         ... = card lcs * card H : Sum_const_eq_card_mul

end lcoset_fintype

section normalizer


end normalizer

end group

/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

-- develop the concept of finite subgroups based on finsets so that the properties
-- can be used directly without translating from the set based theory first

import data algebra.group algebra.group_power data .subgroup .finfun
open function algebra set finset
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

check @finset.univ
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

section cyclic
open nat fin

definition mk_mod (n i : nat) : fin (succ n) :=
mk (i mod (succ n)) (mod_lt _ !zero_lt_succ)

definition diff [reducible] (i j : nat) :=
if (i < j) then (j - i) else (i - j)

lemma diff_eq_max_sub_min {i j : nat} : diff i j = (max i j) - min i j :=
decidable.by_cases
  (λ Plt : i < j, begin rewrite [↑max, ↑min, *(if_pos Plt)] end)
  (λ Pnlt : ¬ i < j, begin rewrite [↑max, ↑min, *(if_neg Pnlt)] end)

lemma diff_le_max {i j : nat} : diff i j ≤ max i j :=
begin rewrite diff_eq_max_sub_min, apply sub_le end

lemma diff_gt_zero_of_ne {i j : nat} : i ≠ j → diff i j > 0 :=
assume Pne, decidable.by_cases
  (λ Plt : i < j, begin rewrite [if_pos Plt], apply sub_pos_of_lt Plt end)
  (λ Pnlt : ¬ i < j, begin
    rewrite [if_neg Pnlt], apply sub_pos_of_lt,
    apply lt_of_le_and_ne (nat.le_of_not_gt Pnlt) (ne.symm Pne) end)

lemma max_lt_of_lt_of_lt {i j n : nat} : i < n → j < n → max i j < n :=
assume Pilt Pjlt, decidable.by_cases
  (λ Plt : i < j, by rewrite [↑max, if_pos Plt]; exact Pjlt)
  (λ Pnlt : ¬ i < j, by rewrite [↑max, if_neg Pnlt]; exact Pilt)

variable {A : Type}

open list
lemma zero_lt_length_of_mem {a : A} : ∀ {l : list A}, a ∈ l → 0 < length l
| []     := assume Pinnil, by contradiction
| (b::l) := assume Pin, !zero_lt_succ

variable [ambG : group A]
include ambG

lemma pow_mod {a : A} {n m : nat} : a ^ m = 1 → a ^ n = a ^ (n mod m) :=
assume Pid,
have Pm : a ^ (n div m * m) = 1, from calc
  a ^ (n div m * m) = a ^ (m * (n div m)) : {mul.comm (n div m) m}
                ... = (a ^ m) ^ (n div m) : !pow_mul
                ... = 1 ^ (n div m) : {Pid}
                ... = 1 : one_pow (n div m),
calc a ^ n = a ^ (n div m * m + n mod m) : {eq_div_mul_add_mod n m}
       ... = a ^ (n div m * m) * a ^ (n mod m) : !pow_add
       ... = 1 * a ^ (n mod m) : {Pm}
       ... = a ^ (n mod m) : !one_mul

lemma pow_sub_eq_one_of_pow_eq {a : A} {i j : nat} :
  a^i = a^j → a^(i - j) = 1 :=
assume Pe, or.elim (lt_or_ge i j)
  (assume Piltj, begin rewrite [sub_eq_zero_of_le (nat.le_of_lt Piltj)] end)
  (assume Pigej, begin rewrite [pow_sub a Pigej, Pe, mul.right_inv] end)

lemma pow_diff_eq_one_of_pow_eq {a : A} {i j : nat} :
  a^i = a^j → a^(diff i j) = 1 :=
assume Pe, decidable.by_cases
  (λ Plt : i < j, by rewrite [if_pos Plt]; exact pow_sub_eq_one_of_pow_eq (eq.symm Pe))
  (λ Pnlt : ¬ i < j, by rewrite [if_neg Pnlt]; exact pow_sub_eq_one_of_pow_eq Pe)

lemma pow_madd {a : A} {n : nat} {i j : fin (succ n)} :
  a^(succ n) = 1 → a^(val (i + j)) = a^i * a^j :=
assume Pe, calc
a^(val (i + j)) = a^((i + j) mod (succ n)) : rfl
            ... = a^(i + j) : pow_mod Pe
            ... = a^i * a^j : !pow_add

lemma mk_pow_mod {a : A} {n m : nat} : a ^ (succ m) = 1 → a ^ n = a ^ (mk_mod m n) :=
assume Pe, pow_mod Pe

variable [finA : fintype A]
include finA

open fintype

lemma card_pos : 0 < card A :=
  zero_lt_length_of_mem (mem_univ 1)

variable [deceqA : decidable_eq A]
include deceqA

lemma order_lt_card (a : A) : ∃ n, n < card A ∧ a ^ (succ n) = 1 :=
let f := (λ i : fin (succ (card A)), a ^ i) in
assert Pninj : ¬(injective f), from assume Pinj,
  absurd (card_le_of_inj _ _ (exists.intro f Pinj))
    (begin rewrite [card_fin], apply not_succ_le_self end),
obtain i₁ P₁, from exists_not_of_not_forall Pninj,
obtain i₂ P₂, from exists_not_of_not_forall P₁,
obtain Pfe Pne, from iff.elim_left not_implies_iff_and_not P₂,
assert Pvne : val i₁ ≠ val i₂, from assume Pveq, absurd (eq_of_veq Pveq) Pne,
exists.intro (pred (diff i₁ i₂)) (begin
  rewrite [succ_pred_of_pos (diff_gt_zero_of_ne Pvne)], apply and.intro,
    apply lt_of_succ_lt_succ,
    rewrite [succ_pred_of_pos (diff_gt_zero_of_ne Pvne)],
    apply nat.lt_of_le_of_lt diff_le_max (max_lt_of_lt_of_lt (is_lt i₁) (is_lt i₂)),
    apply pow_diff_eq_one_of_pow_eq Pfe
  end)

definition cyc (a : A) : finset A := {x ∈ univ | bex (card A) (λ n, a ^ n = x)}

lemma cyc_mul_closed (a : A) : finset_mul_closed_on (cyc a) :=
take g h, assume Pgin Phin,
obtain n Plt Pe, from order_lt_card a,
obtain i Pilt Pig, from of_mem_filter Pgin,
obtain j Pjlt Pjh, from of_mem_filter Phin,
begin
  rewrite [-Pig, -Pjh, -pow_add, pow_mod Pe],
  apply mem_filter_of_mem !mem_univ,
  existsi ((i + j) mod (succ n)), apply and.intro,
    apply nat.lt_of_lt_of_le (mod_lt (i+j) !zero_lt_succ) (succ_le_of_lt Plt),
    apply rfl
end

lemma cyc_has_inv (a : A) : finset_has_inv (cyc a) :=
take g, assume Pgin,
obtain n Plt Pe, from order_lt_card a,
obtain i Pilt Pig, from of_mem_filter Pgin,
let ni := -(mk_mod n i) in
assert Pinv : g*a^ni = 1, by
  rewrite [-Pig, mk_pow_mod Pe, -(pow_madd Pe), add.right_inv],
begin
  rewrite [inv_eq_of_mul_eq_one Pinv],
  apply mem_filter_of_mem !mem_univ,
  existsi ni, apply and.intro,
    apply nat.lt_of_lt_of_le (is_lt ni) (succ_le_of_lt Plt),
    apply rfl
end

lemma cyc_has_one (a : A) : 1 ∈ cyc a :=
begin
  apply mem_filter_of_mem !mem_univ,
  existsi 0, apply and.intro,
    apply card_pos,
    apply pow_zero
end

definition order (a : A) := card (cyc a)

definition cyc_is_finsubg [instance] (a : A) : is_finsubg (cyc a) :=
is_finsubg.mk (cyc_has_one a) (cyc_mul_closed a) (cyc_has_inv a)

lemma order_dvd_group_order (a : A) : order a ∣ card A :=
dvd.intro (eq.symm (!mul.comm ▸ lagrange_theorem (subset_univ (cyc a))))

end cyclic

end group

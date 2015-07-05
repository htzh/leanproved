/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

import theories.number_theory.primes data algebra.group algebra.group_power algebra.group_bigops .cyclic  .finsubg .hom .finfun .perm .action

open nat fin list algebra function subtype

namespace group

section pgroup

open finset fintype

lemma singleton_subset_of_mem {A : Type} {a : A} {S : finset A} : a ∈ S → singleton a ⊆ S :=
assume Pain, subset_of_forall take x,
  by rewrite [mem_singleton_eq]; intro P; rewrite P; assumption

lemma card_pos_of_mem {A : Type} [deceqA : decidable_eq A] {a : A} {S : finset A} :
  a ∈ S → card S > 0 :=
assume Pain, lt_of_succ_le (card_le_card_of_subset (singleton_subset_of_mem Pain))

variables {G S : Type} [ambientG : group G] [deceqG : decidable_eq G] [finS : fintype S] [deceqS : decidable_eq S]
include ambientG

definition psubg (H : finset G) (p m : nat) : Prop := prime p ∧ card H = p^(succ m)

include deceqG finS deceqS
variables {hom : G → perm S} [Hom : is_hom_class hom]
variables {H : finset G} [subgH : is_finsubg H]
include Hom subgH
open finset.partition

lemma card_mod_eq_of_action_by_psubg {p : nat} {m : nat} :
  psubg H p m → (card S) mod p = (card (fixed_points hom H)) mod p :=
take Ppsubg, begin
  rewrite [@orbit_class_equation' G S ambientG finS deceqS hom Hom H subgH],
  apply add_mod_eq_of_dvd, apply dvd_Sum_of_dvd,
  intro s Psin,
  rewrite mem_filter_iff at Psin,
  cases Psin with Psinorbs Pcardne,
  esimp [orbits, equiv_classes, orbit_partition] at Psinorbs,
  rewrite mem_image_iff at Psinorbs,
  cases Psinorbs with a Pa,
  cases Pa with Pain Porb,
  substvars,
  cases Ppsubg with Pprime PcardH,
  assert Pdvd : card (orbit hom H a) ∣ p ^ (succ m),
    rewrite -PcardH,
    apply dvd_of_eq_mul (finset.card (stab hom H a)),
    apply orbit_stabilizer_theorem,
  apply or.elim (divisor_of_prime_pow Pprime Pdvd),
    intro Pcardeq, contradiction,
    intro Ppdvd, exact Ppdvd
end

end pgroup

section cauchy

lemma Prodl_singleton {A B : Type} [mB : monoid B] {a : A} {f : A → B} : Prodl [a] f = f a :=
!one_mul

lemma Prodl_map {A B : Type} [mB : monoid B] {f : A → B} :
  ∀ {l : list A}, Prodl l f = Prodl (map f l) id
| nil    := by rewrite [map_nil]
| (a::l) := begin rewrite [map_cons, Prodl_cons f, Prodl_cons id (f a), Prodl_map] end

lemma Prodl_eq_pow_of_const {A B : Type} [mB : monoid B] {f : A → B} :
  ∀ {l : list A} b, (∀ a, a ∈ l → f a = b) → Prodl l f = b ^ length l
| nil    := take b, assume Pconst, by rewrite [length_nil, {b^0}algebra.pow_zero]
| (a::l) := take b, assume Pconst,
  assert Pconstl : ∀ a', a' ∈ l → f a' = b,
    from take a' Pa'in, Pconst a' (mem_cons_of_mem a Pa'in),
  by rewrite [Prodl_cons f, Pconst a !mem_cons, Prodl_eq_pow_of_const b Pconstl, length_cons, add_one, pow_succ' b]

lemma prodl_rotl_eq_one_of_prodl_eq_one {A B : Type} [gB : group B] {f : A → B} :
  ∀ {l : list A}, Prodl l f = 1 → Prodl (list.rotl l) f = 1
| nil := assume Peq, rfl
| (a::l) := begin
  rewrite [rotl_cons, Prodl_cons f, Prodl_append _ _ f, Prodl_singleton],
  exact mul_eq_one_of_mul_eq_one
  end

section rotl_peo

variables {A : Type} [ambA : group A]
include ambA

theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
begin rewrite [eq_inv_iff_eq_inv], apply eq.symm, exact inv_eq_of_mul_eq_one H end

variable [finA : fintype A]
include finA

variable (A)

definition all_prodl_eq_one (n : nat) : list (list A) :=
map (λ l, cons (Prodl l id)⁻¹ l) (all_lists_of_len n)

variable {A}

lemma prodl_eq_one_of_mem_all_prodl_eq_one {n : nat} {l : list A} : l ∈ all_prodl_eq_one A n → Prodl l id = 1 :=
assume Plin, obtain l' Pl' Pl, from exists_of_mem_map Plin,
by substvars; rewrite [Prodl_cons id _ l', mul.left_inv]

lemma length_of_mem_all_prodl_eq_one {n : nat} {l : list A} : l ∈ all_prodl_eq_one A n → length l = succ n :=
assume Plin, obtain l' Pl' Pl, from exists_of_mem_map Plin,
begin substvars, rewrite [length_cons, length_mem_all_lists Pl'] end

lemma nodup_all_prodl_eq_one {n : nat} : nodup (all_prodl_eq_one A n) :=
nodup_map (take l₁ l₂ Peq, tail_eq_of_cons_eq Peq) nodup_all_lists

lemma all_prodl_eq_one_complete {n : nat} : ∀ {l : list A}, length l = succ n → Prodl l id = 1 → l ∈ all_prodl_eq_one A n
| nil    := assume Pleq, by contradiction
| (a::l) := assume Pleq Pprod,
  begin
    rewrite length_cons at Pleq,
    rewrite (Prodl_cons id a l) at Pprod,
    rewrite [eq_inv_of_mul_eq_one Pprod],
    apply mem_map, apply mem_all_lists, apply succ.inj Pleq
  end

open fintype
lemma length_all_prodl_eq_one {n : nat} : length (@all_prodl_eq_one A _ _ n) = (card A)^n :=
eq.trans !length_map length_all_lists

open fin

definition prodseq {n : nat} (s : seq A n) : A := Prodl (upto n) s

definition peo [reducible] {n : nat} (s : seq A n) := prodseq s = 1

definition constseq {n : nat} (s : seq A (succ n)) := ∀ i, s i = s !zero

lemma prodseq_eq {n :nat} {s : seq A n} : prodseq s = Prodl (fun_to_list s) id :=
Prodl_map

lemma prodseq_eq_pow_of_constseq {n : nat} (s : seq A (succ n)) :
  constseq s → prodseq s = (s !zero) ^ succ n :=
assume Pc, assert Pcl : ∀ i, i ∈ upto (succ n) → s i = s !zero,
  from take i, assume Pin, Pc i,
by rewrite [↑prodseq, Prodl_eq_pow_of_const _ Pcl, fin.length_upto]

lemma seq_eq_of_constseq_of_eq {n : nat} {s₁ s₂ : seq A (succ n)} :
  constseq s₁ → constseq s₂ → s₁ !zero = s₂ !zero → s₁ = s₂ :=
assume Pc₁ Pc₂ Peq, funext take i, by rewrite [Pc₁ i,  Pc₂ i, Peq]

lemma peo_const_one : ∀ {n : nat}, peo (λ i : fin n, (1 : A))
| 0 := rfl
| (succ n) := let s := λ i : fin (succ n), (1 : A) in
  assert Pconst : constseq s, from take i, rfl,
  calc prodseq s = (s !zero) ^ succ n : prodseq_eq_pow_of_constseq s Pconst
             ... = (1 : A) ^ succ n : rfl
             ... = 1 : algebra.one_pow

variable [deceqA : decidable_eq A]
include deceqA

variable (A)

definition peo_seq [reducible] (n : nat) := {s : seq A (succ n) | peo s}

definition peo_seq_one (n : nat) : peo_seq A n :=
tag (λ i : fin (succ n), (1 : A)) peo_const_one

definition all_prodseq_eq_one (n : nat) : list (seq A (succ n)) :=
dmap (λ l, length l = card (fin (succ n))) list_to_fun (all_prodl_eq_one A n)

definition all_peo_seqs (n : nat) : list (peo_seq A n) :=
dmap peo tag (all_prodseq_eq_one A n)

variable {A}

lemma prodseq_eq_one_of_mem_all_prodseq_eq_one {n : nat} {s : seq A (succ n)} :
  s ∈ all_prodseq_eq_one A n → prodseq s = 1 :=
assume Psin, obtain l Pex, from exists_of_mem_dmap Psin,
obtain leq Pin Peq, from Pex,
by rewrite [prodseq_eq, Peq, list_to_fun_to_list, prodl_eq_one_of_mem_all_prodl_eq_one Pin]

lemma all_prodseq_eq_one_complete {n : nat} {s : seq A (succ n)} :
  prodseq s = 1 → s ∈ all_prodseq_eq_one A n :=
assume Peq,
assert Plin : map s (elems (fin (succ n))) ∈ all_prodl_eq_one A n,
  from begin
  apply all_prodl_eq_one_complete,
    rewrite [length_map], exact length_upto (succ n),
    rewrite prodseq_eq at Peq, exact Peq
  end,
assert Psin : list_to_fun (map s (elems (fin (succ n)))) (length_map_of_fintype s) ∈ all_prodseq_eq_one A n,
  from mem_dmap _ Plin,
by rewrite [fun_eq_list_to_fun_map s (length_map_of_fintype s)]; apply Psin

lemma nodup_all_prodseq_eq_one {n : nat} : nodup (all_prodseq_eq_one A n) :=
dmap_nodup_of_dinj dinj_list_to_fun nodup_all_prodl_eq_one

lemma rotl1_peo_of_peo {n : nat} {s : seq A n} : peo s → peo (rotl_fun 1 s) :=
begin rewrite [↑peo, *prodseq_eq, seq_rotl_eq_list_rotl], apply prodl_rotl_eq_one_of_prodl_eq_one end

section
local attribute perm.f [coercion]

lemma rotl_perm_peo_of_peo {n : nat} : ∀ {m} {s : seq A n}, peo s → peo (rotl_perm A n m s)
| 0        := begin rewrite [↑rotl_perm, rotl_seq_zero], intros, assumption end
| (succ m) := take s,
  assert Pmul : rotl_perm A n (m + 1) s = rotl_fun 1 (rotl_perm A n m s), from
    calc s ∘ (rotl (m + 1)) = s ∘ ((rotl m) ∘ (rotl 1)) : rotl_compose
                        ... = s ∘ (rotl m) ∘ (rotl 1) : compose.assoc,
  begin
  rewrite [-add_one, Pmul], intro P,
  exact rotl1_peo_of_peo (rotl_perm_peo_of_peo P)
  end

end

lemma nodup_all_peo_seqs {n : nat} : nodup (all_peo_seqs A n) :=
dmap_nodup_of_dinj (dinj_tag peo) nodup_all_prodseq_eq_one

lemma all_peo_seqs_complete {n : nat} : ∀ s : peo_seq A n, s ∈ all_peo_seqs A n :=
take ps, subtype.destruct ps (take s, assume Ps,
  assert Pin : s ∈ all_prodseq_eq_one A n, from all_prodseq_eq_one_complete Ps,
  mem_dmap Ps Pin)

lemma length_all_peo_seqs {n : nat} : length (all_peo_seqs A n) = (card A)^n :=
eq.trans (eq.trans
  (show length (all_peo_seqs A n) = length (all_prodseq_eq_one A n), from
    assert Pmap : map elt_of (all_peo_seqs A n) = all_prodseq_eq_one A n,
      from map_dmap_of_inv_of_pos (λ s P, rfl)
        (λ s, prodseq_eq_one_of_mem_all_prodseq_eq_one),
    by rewrite [-Pmap, length_map])
  (show length (all_prodseq_eq_one A n) = length (all_prodl_eq_one A n), from
    assert Pmap : map fun_to_list (all_prodseq_eq_one A n) = all_prodl_eq_one A n,
      from map_dmap_of_inv_of_pos list_to_fun_to_list
        (λ l Pin, by rewrite [length_of_mem_all_prodl_eq_one Pin, card_fin]),
    by rewrite [-Pmap, length_map]))
  length_all_prodl_eq_one

definition peo_seq_is_fintype [instance] {n : nat} : fintype (peo_seq A n) :=
fintype.mk (all_peo_seqs A n) nodup_all_peo_seqs all_peo_seqs_complete

lemma card_peo_seq {n : nat} : card (peo_seq A n) = (card A)^n :=
length_all_peo_seqs

section

variable (A)

local attribute perm.f [coercion]

definition rotl_peo_seq (n : nat) (m : nat) (s : peo_seq A n) : peo_seq A n :=
tag (rotl_perm A (succ n) m (elt_of s)) (rotl_perm_peo_of_peo (has_property s))

variable {A}

end

lemma rotl_peo_seq_zero {n : nat} : rotl_peo_seq A n 0 = id :=
funext take s, subtype.eq begin rewrite [↑rotl_peo_seq, ↑rotl_perm, rotl_seq_zero] end

lemma rotl_peo_seq_id {n : nat} : rotl_peo_seq A n (succ n) = id :=
funext take s, subtype.eq begin rewrite [↑rotl_peo_seq, -rotl_perm_pow_eq, rotl_perm_pow_eq_one] end

lemma rotl_peo_seq_compose {n i j : nat} :
  (rotl_peo_seq A n i) ∘ (rotl_peo_seq A n j) = rotl_peo_seq A n (j + i) :=
funext take s, subtype.eq begin rewrite [↑rotl_peo_seq, ↑rotl_perm, ↑rotl_fun, compose.assoc, rotl_compose] end

lemma rotl_peo_seq_mod {n i : nat} : rotl_peo_seq A n i = rotl_peo_seq A n (i mod succ n) :=
funext take s, subtype.eq begin rewrite [↑rotl_peo_seq, rotl_perm_mod] end

lemma rotl_peo_seq_inj {n m : nat} : injective (rotl_peo_seq A n m) :=
take ps₁ ps₂, subtype.destruct ps₁ (λ s₁ P₁, subtype.destruct ps₂ (λ s₂ P₂,
  assume Peq, tag_eq (rotl_fun_inj (dinj_tag peo _ _ Peq))))

variable (A)

definition rotl_perm_ps [reducible] (n : nat) (m : fin (succ n)) : perm (peo_seq A n) :=
perm.mk (rotl_peo_seq A n m) rotl_peo_seq_inj

variable {A}

variable {n : nat}

lemma rotl_perm_ps_eq {m : fin (succ n)} {s : peo_seq A n} : elt_of (perm.f (rotl_perm_ps A n m) s) = perm.f (rotl_perm A (succ n) m) (elt_of s) := rfl

lemma rotl_perm_ps_eq_of_rotl_perm_eq {i j : fin (succ n)} :
  (rotl_perm A (succ n) i) = (rotl_perm A (succ n) j) → (rotl_perm_ps A n i) = (rotl_perm_ps A n j) :=
assume Peq, eq_of_feq (funext take s, subtype.eq (by rewrite [*rotl_perm_ps_eq, Peq]))

lemma rotl_perm_ps_hom (i j : fin (succ n)) :
  rotl_perm_ps A n (i+j) = (rotl_perm_ps A n i) * (rotl_perm_ps A n j) :=
eq_of_feq (begin rewrite [↑rotl_perm_ps, {val (i+j)}val_madd, add.comm, -rotl_peo_seq_mod, -rotl_peo_seq_compose] end)

section
local attribute group_of_add_group [instance]

definition rotl_perm_ps_is_hom [instance] : is_hom_class (rotl_perm_ps A n) :=
is_hom_class.mk rotl_perm_ps_hom

open finset

lemma const_of_is_fixed_point {s : peo_seq A n} :
  is_fixed_point (rotl_perm_ps A n) univ s → constseq (elt_of s) :=
assume Pfp, take i, begin
  rewrite [-(Pfp i !mem_univ) at {1}, rotl_perm_ps_eq, ↑rotl_perm, ↑rotl_fun, {i}mk_mod_eq at {2}, rotl_to_zero]
end

lemma const_of_rotl_fixed_point {s : peo_seq A n} :
  s ∈ fixed_points (rotl_perm_ps A n) univ → constseq (elt_of s) :=
assume Psin, take i, begin
  apply const_of_is_fixed_point, exact is_fixed_point_of_mem_fixed_points Psin
end

lemma pow_eq_one_of_mem_fixed_points {s : peo_seq A n} :
  s ∈ fixed_points (rotl_perm_ps A n) univ → (elt_of s !zero)^(succ n) = 1 :=
assume Psin, eq.trans
  (eq.symm (prodseq_eq_pow_of_constseq (elt_of s) (const_of_rotl_fixed_point Psin)))
  (has_property s)

lemma peo_seq_one_is_fixed_point : is_fixed_point (rotl_perm_ps A n) univ (peo_seq_one A n) :=
take h, assume Pin, by esimp [rotl_perm_ps]

lemma peo_seq_one_mem_fixed_points : peo_seq_one A n ∈ fixed_points (rotl_perm_ps A n) univ :=
mem_fixed_points_of_is_fixed_point_of_exists peo_seq_one_is_fixed_point (exists.intro !zero !mem_univ)

lemma generator_of_prime_of_dvd_order {p : nat}
  : prime p → p ∣ card A → ∃ g : A, g ≠ 1 ∧ g^p = 1 :=
assume Pprime Pdvd,
let pp := nat.pred p, spp := nat.succ pp in
assert Peq : spp = p, from succ_pred_prime Pprime,
have Ppsubg : psubg (@univ (fin spp) _) spp 0,
  from and.intro (eq.symm Peq ▸ Pprime) (by rewrite [Peq, card_fin, pow_one]),
have Pcardmod : (nat.pow (card A) pp) mod p = (card (fixed_points (rotl_perm_ps A pp) univ)) mod p,
  from Peq ▸ card_peo_seq ▸ card_mod_eq_of_action_by_psubg Ppsubg,
have Pfpcardmod : (card (fixed_points (rotl_perm_ps A pp) univ)) mod p = 0,
  from eq.trans (eq.symm Pcardmod) (mod_eq_zero_of_dvd (dvd_pow_of_dvd_of_pos Pdvd (pred_prime_pos Pprime))),
have Pfpcardpos : card (fixed_points (rotl_perm_ps A pp) univ) > 0,
  from card_pos_of_mem peo_seq_one_mem_fixed_points,
have Pfpcardgt1 : card (fixed_points (rotl_perm_ps A pp) univ) > 1,
  from gt_one_of_pos_of_prime_dvd Pprime Pfpcardpos Pfpcardmod,
obtain s₁ s₂ Pin₁ Pin₂ Psnes, from exists_two_of_card_gt_one Pfpcardgt1,
decidable.by_cases
  (λ Pe₁ : elt_of s₁ !zero = 1,
    assert Pne₂ : elt_of s₂ !zero ≠ 1,
    from assume Pe₂,
      absurd
        (subtype.eq (seq_eq_of_constseq_of_eq
          (const_of_rotl_fixed_point Pin₁)
          (const_of_rotl_fixed_point Pin₂)
          (eq.trans Pe₁ (eq.symm Pe₂))))
        Psnes,
    exists.intro (elt_of s₂ !zero)
      (and.intro Pne₂ (Peq ▸ pow_eq_one_of_mem_fixed_points Pin₂)))
  (λ Pne, exists.intro (elt_of s₁ !zero)
    (and.intro Pne (Peq ▸ pow_eq_one_of_mem_fixed_points Pin₁)))

end

theorem cauchy_theorem {p : nat} : prime p → p ∣ card A → ∃ g : A, order g = p :=
assume Pprime Pdvd,
obtain g Pne Pgpow, from generator_of_prime_of_dvd_order Pprime Pdvd,
assert Porder : order g ∣ p, from order_dvd_of_pow_eq_one Pgpow,
or.elim (divisor_of_prime Pprime Porder)
  (λ Pe, absurd (eq_one_of_order_eq_one Pe) Pne)
  (λ Porderp, exists.intro g Porderp)

check @cauchy_theorem

end rotl_peo

end cauchy
end group

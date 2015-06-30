/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

import data algebra.group algebra.group_power algebra.group_bigops .cyclic  .finsubg .hom .finfun .perm

open nat fin list algebra function subtype

section
lemma dinj_tag {A : Type} (P : A → Prop) : dinj P tag :=
take a₁ a₂ Pa₁ Pa₂ Pteq, subtype.no_confusion Pteq (λ Pe Pqe, Pe)

end

namespace group
section cauchy

lemma Prodl_singleton {A B : Type} [mB : monoid B] {a : A} {f : A → B} : Prodl [a] f = f a :=
!one_mul

lemma Prodl_map {A B : Type} [mB : monoid B] {f : A → B} :
  ∀ {l : list A}, Prodl l f = Prodl (map f l) id
| nil    := by rewrite [map_nil]
| (a::l) := begin rewrite [map_cons, Prodl_cons f, Prodl_cons id (f a), Prodl_map] end

lemma prodl_rotl_eq_one_of_prodl_eq_one {A B : Type} [gB : group B] {f : A → B} :
  ∀ {l : list A}, Prodl l f = 1 → Prodl (list.rotl l) f = 1
| nil := assume Peq, rfl
| (a::l) := begin
  rewrite [rotl_cons, Prodl_cons f, Prodl_append _ _ f, Prodl_singleton],
  exact mul_eq_one_of_mul_eq_one
  end

section rotl_peo

variable {A : Type}
variable [ambA : group A]
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

variable [deceqA : decidable_eq A]
include deceqA

variable (A)

definition peo_seq [reducible] (n : nat) := {s : seq A (succ n) | peo s}

definition all_prodseq_eq_one (n : nat) : list (seq A (succ n)) :=
dmap (λ l, length l = card (fin (succ n))) list_to_fun (all_prodl_eq_one A n)

definition all_peo_seqs (n : nat) : list (peo_seq A n) :=
dmap peo tag (all_prodseq_eq_one A n)

variable {A}

lemma prodseq_eq {n :nat} {s : seq A n} : prodseq s = Prodl (fun_to_list s) id :=
Prodl_map

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

definition peo_seq_is_fintype [instance] {n : nat} : fintype (peo_seq A n) :=
fintype.mk (all_peo_seqs A n) nodup_all_peo_seqs all_peo_seqs_complete

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

local attribute group_of_add_group [instance]

definition rotl_perm_ps_is_hom [instance] : is_hom_class (rotl_perm_ps A n) :=
is_hom_class.mk rotl_perm_ps_hom

end rotl_peo

end cauchy
end group

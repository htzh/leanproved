/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

import data algebra.group algebra.group_power algebra.group_bigops .cyclic .finfun

open nat list algebra function

namespace group
section cauchy

lemma id_apply {A : Type} {a : A} : id a = a := rfl

lemma Prodl_singleton {A B : Type} [mB : monoid B] {a : A} {f : A → B} : Prodl [a] f = f a :=
!one_mul

lemma prodl_rotl_eq_one_of_prodl_eq_one {A B : Type} [gB : group B] {f : A → B} :
  ∀ {l : list A}, Prodl l f = 1 → Prodl (list.rotl l) f = 1
| nil := assume Peq, rfl
| (a::l) := begin
  rewrite [rotl_cons, Prodl_cons f, Prodl_append _ _ f, Prodl_singleton],
  exact mul_eq_one_of_mul_eq_one
  end

variable {A : Type}
variable [ambA : group A]
include ambA

variable [finA : fintype A]
include finA

definition all_prodl_eq_one (n : nat) : list (list A) :=
map (λ l, cons (Prodl l id)⁻¹ l) (all_lists_of_len n)

lemma prodl_eq_one_of_mem_all_prodl_eq_one {n : nat} {l : list A} : l ∈ all_prodl_eq_one n → Prodl l id = 1 :=
assume Plin, obtain l' Pl' Pl, from exists_of_mem_map Plin,
by substvars; rewrite [Prodl_cons id _ l', mul.left_inv]

lemma length_of_mem_all_prodl_eq_one {n : nat} {l : list A} : l ∈ all_prodl_eq_one n → length l = succ n :=
assume Plin, obtain l' Pl' Pl, from exists_of_mem_map Plin,
begin substvars, rewrite [length_cons, length_mem_all_lists Pl'] end

lemma nodup_all_prodl_eq_one {n : nat} : nodup (@all_prodl_eq_one A _ _ n) :=
nodup_map (take l₁ l₂ Peq, tail_eq_of_cons_eq Peq) nodup_all_lists

lemma complete_all_prodl_eq_one {n : nat} : ∀ {l : list A}, length l = succ n → Prodl l id = 1 → l ∈ all_prodl_eq_one n
| nil    := assume Pleq, by contradiction
| (a::l) := assume Pleq Pprod,
  begin rewrite {a::l}Prodl at Pprod end
open fin

definition prodseq {n : nat} (s : seq A n) : A := Prodl (upto n) s


end cauchy
end group

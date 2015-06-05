/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import data .extra

open nat function eq.ops

namespace list
-- this is in preparation for counting the number of finite functions
section list_of_lists
open prod
variable {A : Type}

definition cons_pair (pr : A × list A) := (pr1 pr) :: (pr2 pr)

definition cons_all_of (elts : list A) (ls : list (list A)) : list (list A) :=
           map cons_pair (product elts ls)

lemma pair_of_cons {a} {l} {pr : A × list A} : cons_pair pr = a::l → pr = (a, l) :=
      prod.destruct pr (λ p1 p2, assume Peq, list.no_confusion Peq (by intros; substvars))

lemma cons_pair_inj : has_left_inverse (@cons_pair A) := sorry
lemma nodup_of_cons_all {elts : list A} {ls : list (list A)}
      : nodup elts → nodup ls → nodup (cons_all_of elts ls) :=
      assume Pelts Pls,
      nodup_map cons_pair_inj (nodup_product Pelts Pls)

variable [finA : fintype A]
include finA

definition all_lists_of_len : ∀ (n : nat), list (list A)
| 0        := [[]]
| (succ n) := cons_all_of (elements_of A) (all_lists_of_len n)

lemma nodup_all_lists : ∀ (n : nat), nodup (@all_lists_of_len A _ n)
| 0                   := nodup_singleton []
| (succ n)            := nodup_of_cons_all (fintype.unique A) (nodup_all_lists n)

lemma mem_all_lists : ∀ (n : nat) (l : list A), length l = n → l ∈ all_lists_of_len n
| 0 []              := assume P, mem_cons [] []
| 0 (a::l)          := assume Peq, by contradiction
| (succ n) []       := assume Peq, by contradiction
| (succ n) (a::l)   := assume Peq, begin
                    apply mem_map, apply mem_product,
                      exact fintype.complete a,
                      exact mem_all_lists n l (succ_inj Peq)
                    end

lemma leq_of_mem_all_lists : ∀ {n : nat} {l : list A},
                           l ∈ all_lists_of_len n → length l = n
| 0 []             := assume P, rfl
| 0 (a::l)         := assume Pin, assert Peq : (a::l) = [], from mem_singleton Pin,
                   by contradiction
| (succ n) []      := assume Pin, obtain pr Pprin Ppr, from exists_of_mem_map Pin,
                   by contradiction
| (succ n) (a::l)  := assume Pin, obtain pr Pprin Ppr, from exists_of_mem_map Pin,
                   assert Pl : l ∈ all_lists_of_len n,
                     from mem_of_mem_product_right ((pair_of_cons Ppr) ▸ Pprin),
                   by rewrite [length_cons, leq_of_mem_all_lists Pl]

end list_of_lists
end list

        
namespace fintype
open list

section list_to_fun
variables {A B : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA
 
definition list_to_fun (l : list B) (leq : length l = card A) : A → B :=
           assume x,
           let k := find x (elements_of A) in
           have Plt : k < card A, from (find_mem (complete x)),
           have Pltl : k < length l, from leq⁻¹ ▸ Plt,
           kth _ _ Pltl

lemma list_eq_map_fun (l : list B) (leq : length l = card A)
                    : l = map (list_to_fun l leq) (elements_of A) := sorry
lemma dinj_list_to_fun : dinj (λ (l : list B), length l = card A) list_to_fun :=
      take l1 l2 Pl1 Pl2 Peq,
      by rewrite [list_eq_map_fun l1 Pl1, list_eq_map_fun l2 Pl2, Peq]

variable [finB : fintype B]
include finB
definition all_funs : list (A → B) :=
           dmap (λ l, length l = card A) list_to_fun (all_lists_of_len (card A))

end list_to_fun

section surj_inv
variables {A B : Type}
variable [finA : fintype A]
include finA

-- surj from fintype domain implies fintype range
lemma mem_map_of_surj {f : A → B} (surj : surjective f) : ∀ b, b ∈ map f (elements_of A) :=
      take b, obtain a Peq, from surj b,
      Peq ▸ mem_map f (complete a)

variable [deceqB : decidable_eq B]
include deceqB

lemma found_of_surj {f : A → B} (surj : surjective f) :
      ∀ b, let elts := elems A, k := find b (map f elts) in k < length elts :=
      λ b, let elts := elems A, img := map f elts, k := find b img in
           have Pin : b ∈ img, from mem_map_of_surj surj b,
           assert Pfound : k < length img, from find_mem (mem_map_of_surj surj b),
           len_map f elts ▸ Pfound

definition right_inv {f : A → B} (surj : surjective f) : B → A :=
           λ b, let elts := elems A, k := find b (map f elts) in
           kth k elts (found_of_surj surj b)

lemma found_of_map {f : A → B} (b : B) :
    ∀ (l : list A) (P : find b (map f l) < length l), f (kth (find b (map f l)) l P) = b
| []       := assume P, begin exact absurd P !not_lt_zero end
| (a::l)   := decidable.rec_on (deceqB b (f a))
              (assume Peq, begin
              rewrite [map_cons f a l, find_cons_of_eq _ Peq],
              intro P, rewrite [kth_zero_of_cons], exact (Peq⁻¹)
              end)
              (assume Pne, begin
              rewrite [map_cons f a l, find_cons_of_ne _ Pne],
              intro P,
              rewrite [kth_succ_of_cons (find b (map f l)) l P],
              exact found_of_map l (lt_of_succ_lt_succ P)
              end)

lemma id_of_right_inv {f : A → B} (surj : surjective f) : f ∘ (right_inv surj) = id :=
      funext (λ b, found_of_map b (elems A) (found_of_surj surj b))
end surj_inv

-- inj functions for equal card types are also surj and therefore bij
-- the right inv (since it is surj) is also the left inv
section inj
variables {A B : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA
variable [finB : fintype B]
include finB
variable [deceqB : decidable_eq B]
include deceqB
open finset

lemma surj_of_inj_eq_card : card A = card B → ∀ {f : A → B}, injective f → surjective f :=
      assume Peqcard, take f, assume Pinj,
      decidable.rec_on decidable_forall_finite
      (assume P : surjective f, P)
      (assume Pnsurj : ¬surjective f, obtain b Pne, from exists_not_of_not_forall Pnsurj,
      assert Pall : ∀ a, f a ≠ b, from forall_not_of_not_exists Pne,
      assert Pbnin : b ∉ image f univ, from λ Pin,
        obtain a Pa, from exists_of_mem_image Pin, absurd (and.right Pa) (Pall a),
      assert Puniv : finset.card (image f univ) = card A,
        from card_eq_card_image_of_inj Pinj,
      assert Punivb : finset.card (image f univ) = card B, from eq.trans Puniv Peqcard,
      assert P : image f univ = univ, from univ_of_card_eq_univ Punivb,
      absurd (P⁻¹▸ mem_univ b) Pbnin)

end inj
end fintype

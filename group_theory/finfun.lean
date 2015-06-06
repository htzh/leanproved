/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import data

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

lemma cons_pair_inj : injective (@cons_pair A) := sorry
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

section kth

variable {A : Type}

definition kth : ∀ k (l : list A), k < length l → A
| k []        := begin rewrite length_nil, intro Pltz, exact absurd Pltz !not_lt_zero end
| 0 (a::l)    := λ P, a
| (k+1) (a::l):= by rewrite length_cons; intro Plt; exact kth k l (lt_of_succ_lt_succ Plt)

lemma kth_zero_of_cons {a} (l : list A) (P : 0 < length (a::l)) : kth 0 (a::l) P = a :=
      rfl
lemma kth_succ_of_cons {a} k (l : list A) (P : k+1 < length (a::l)) : kth (succ k) (a::l) P = kth k l (lt_of_succ_lt_succ P) :=
      rfl

end kth

end list

        
namespace fintype
open list

section found

variables {A B : Type}

lemma eq_of_kth_eq [deceqA : decidable_eq A] {l1 l2 : list A} (Pleq : length l1 = length l2)
    : (∀ (k : nat) (Plt1 : k < length l1) (Plt2 : k < length l2), kth k l1 Plt1 = kth k l2 Plt2) → l1 = l2 :=
    sorry
check @eq_of_kth_eq
lemma kth_of_map {A B : Type} {f : A → B} {l : list A} {k : nat} (Plt : k < length l)
    : ∀ (Pmlt : k < length (map f l)), kth k (map f l) Pmlt = f (kth k l Plt) := sorry
lemma find_kth {A : Type} [deceqA : decidable_eq A] {l : list A} {k : nat} :
      ∀ P, find (kth k l P) l < length l  := sorry
lemma find_kth_of_nodup {A : Type} [deceqA : decidable_eq A] {l : list A} {k : nat} (Plt : k < length l)
    : nodup l → find (kth k l Plt) l = k := sorry
    
variable [finA : fintype A]
include finA

lemma found_in_range [deceqB : decidable_eq B] {f : A → B} (b : B) :
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
              exact found_in_range l (lt_of_succ_lt_succ P)
              end)

lemma found_in_domain [deceqA : decidable_eq A] {f : A → B} (a : A) :
      ∀ (l : list A) (P : find a l < length l), f (kth (find a l) l P) = f a := sorry

end found

section list_to_fun
variables {A B : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA
 
definition list_to_fun (l : list B) (leq : length l = card A) : A → B :=
           assume x,
           let k := find x (elements_of A) in
           have Plt : k < card A, from (find_lt_length (complete x)),
           have Pltl : k < length l, from leq⁻¹ ▸ Plt,
           kth _ _ Pltl

lemma list_to_fun_apply (l : list B) (leq : length l = card A) (a : A) :
      ∀ P, list_to_fun l leq a = kth (find a (elements_of A)) l P :=
      assume P, rfl

lemma list_eq_map_list_to_fun [deceqB : decidable_eq B] (l : list B) (leq : length l = card A)
                    : l = map (list_to_fun l leq) (elements_of A) :=
      begin
        apply eq_of_kth_eq ((length_map (list_to_fun l leq) (elements_of A))⁻¹ ▸ leq),
        intro k Plt Plt2,
        assert Plt1 : k < length (elements_of A), {apply leq ▸ Plt},
        assert Plt3 : find (kth k (elements_of A) Plt1) (elements_of A) < length l,
          {rewrite leq, apply find_kth},
        rewrite [kth_of_map Plt1 Plt2, list_to_fun_apply l leq (kth k (elements_of A) Plt1) Plt3],
        generalize Plt3,
        rewrite [↑elements_of, find_kth_of_nodup Plt1 (unique A)],
        intro Plt, exact rfl
      end

lemma dinj_list_to_fun [deceqB : decidable_eq B] : dinj (λ (l : list B), length l = card A) list_to_fun :=
      take l1 l2 Pl1 Pl2 Peq,
      by rewrite [list_eq_map_list_to_fun l1 Pl1, list_eq_map_list_to_fun l2 Pl2, Peq]

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
           assert Pfound : k < length img, from find_lt_length (mem_map_of_surj surj b),
           length_map f elts ▸ Pfound

definition right_inv {f : A → B} (surj : surjective f) : B → A :=
           λ b, let elts := elems A, k := find b (map f elts) in
           kth k elts (found_of_surj surj b)

lemma id_of_right_inv {f : A → B} (surj : surjective f) : f ∘ (right_inv surj) = id :=
      funext (λ b, found_in_range b (elems A) (found_of_surj surj b))
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

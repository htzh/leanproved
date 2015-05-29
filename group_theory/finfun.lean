/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import data .extra

open nat function list

namespace fintype
open eq.ops

section list_to_fun
variables {A B : Type}
variable [finA : fintype A]
include finA

definition list_to_fun [deceqA : decidable_eq A] (l : list B) (leq : length l = card A) : A → B :=
           assume x,
           let k := find x (elements_of A) in
           have Plt : k < card A, from (find_mem (complete x)),
           have Pltl : k < length l, from leq⁻¹ ▸ Plt,
           kth _ _ Pltl

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

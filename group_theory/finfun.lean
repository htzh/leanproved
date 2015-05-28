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

end fintype

/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

import algebra.group_bigops algebra.group_power
open nat algebra function binary quot subtype list finset

namespace migration
section group

lemma Prodl_singleton {A B : Type} [mB : monoid B] {a : A} {f : A → B} : Prodl [a] f = f a :=
!one_mul

lemma Prodl_map {A B : Type} [mB : monoid B] {f : A → B} :
  ∀ {l : list A}, Prodl l f = Prodl (map f l) id
| nil    := by rewrite [map_nil]
| (a::l) := begin rewrite [map_cons, Prodl_cons f, Prodl_cons id (f a), Prodl_map] end

open nat
lemma Prodl_eq_pow_of_const {A B : Type} [mB : monoid B] {f : A → B} :
  ∀ {l : list A} b, (∀ a, a ∈ l → f a = b) → Prodl l f = b ^ length l
| nil    := take b, assume Pconst, by rewrite [length_nil, {b^0}algebra.pow_zero]
| (a::l) := take b, assume Pconst,
  assert Pconstl : ∀ a', a' ∈ l → f a' = b,
    from take a' Pa'in, Pconst a' (mem_cons_of_mem a Pa'in),
  by rewrite [Prodl_cons f, Pconst a !mem_cons, Prodl_eq_pow_of_const b Pconstl, length_cons, add_one, pow_succ' b]

end group
end migration

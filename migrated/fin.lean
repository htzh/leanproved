/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import data algebra.group
open fin nat function eq.ops

namespace migration

section
variable {n : nat}

lemma eq_of_veq : ∀ {i j : fin n}, (val i) = j → i = j
| (mk iv ilt) (mk jv jlt) := assume (veq : iv = jv), begin congruence, assumption end

lemma veq_of_eq : ∀ {i j : fin n}, i = j → (val i) = j
| (mk iv ilt) (mk jv jlt) := assume Peq,
  have veq : iv = jv, from fin.no_confusion Peq (λ Pe Pqe, Pe), veq

lemma eq_iff_veq : ∀ {i j : fin n}, (val i) = j ↔ i = j :=
take i j, iff.intro eq_of_veq veq_of_eq

definition val_inj := @eq_of_veq n


definition lift_succ (i : fin n) : fin (nat.succ n) :=
lift i 1

definition maxi [reducible] : fin (succ n) :=
mk n !lt_succ_self

lemma ne_max_of_lt_max {i : fin (succ n)} : i < n → i ≠ maxi :=
by intro hlt he; substvars; exact absurd hlt (lt.irrefl n)

lemma lt_max_of_ne_max {i : fin (succ n)} : i ≠ maxi → i < n :=
assume hne  : i ≠ maxi,
assert visn : val i < nat.succ n, from val_lt i,
assert aux  : val (@maxi n) = n,   from rfl,
assert vne  : val i ≠ n, from
  assume he,
    have vivm : val i = val (@maxi n), from he ⬝ aux⁻¹,
    absurd (eq_of_veq vivm) hne,
lt_of_le_of_ne (le_of_lt_succ visn) vne

lemma lift_succ_ne_max {i : fin n} : lift_succ i ≠ maxi :=
begin
  cases i with v hlt, esimp [lift_succ, lift, max], intro he,
  injection he, substvars,
  exact absurd hlt (lt.irrefl v)
end

lemma lift_succ_inj : injective (@lift_succ n) :=
take i j, destruct i (destruct j (take iv ilt jv jlt Pmkeq,
  begin congruence, apply fin.no_confusion Pmkeq, intros, assumption end))

lemma lt_of_inj_of_max (f : fin (succ n) → fin (succ n)) :
  injective f → (f maxi = maxi) → ∀ i, i < n → f i < n :=
assume Pinj Peq, take i, assume Pilt,
assert P1 : f i = f maxi → i = maxi, from assume Peq, Pinj i maxi Peq,
have P : f i ≠ maxi, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max P

definition lift_fun : (fin n → fin n) → (fin (succ n) → fin (succ n)) :=
λ f i, dite (i = maxi) (λ Pe, maxi) (λ Pne, lift_succ (f (mk i (lt_max_of_ne_max Pne))))

definition lower_inj (f : fin (succ n) → fin (succ n)) (inj : injective f) :
  f maxi = maxi → fin n → fin n :=
assume Peq, take i, mk (f (lift_succ i)) (lt_of_inj_of_max f inj Peq (lift_succ i) (lt_max_of_ne_max lift_succ_ne_max))

lemma lift_fun_max {f : fin n → fin n} : lift_fun f maxi = maxi :=
begin rewrite [↑lift_fun, dif_pos rfl] end

lemma lift_fun_of_ne_max {f : fin n → fin n} {i} (Pne : i ≠ maxi) :
  lift_fun f i = lift_succ (f (mk i (lt_max_of_ne_max Pne))) :=
begin rewrite [↑lift_fun, dif_neg Pne] end

lemma lift_fun_eq {f : fin n → fin n} {i : fin n} :
  lift_fun f (lift_succ i) = lift_succ (f i) :=
begin
rewrite [lift_fun_of_ne_max lift_succ_ne_max], congruence, congruence,
rewrite [-eq_iff_veq, ↑lift_succ, -val_lift]
end

lemma lift_fun_of_inj {f : fin n → fin n} : injective f → injective (lift_fun f) :=
assume Pinj, take i j,
assert Pdi : decidable (i = maxi), from _, assert Pdj : decidable (j = maxi), from _,
begin
  cases Pdi with Pimax Pinmax,
    cases Pdj with Pjmax Pjnmax,
      substvars, intros, exact rfl,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pjnmax],
        intro Plmax, apply absurd Plmax⁻¹ lift_succ_ne_max,
    cases Pdj with Pjmax Pjnmax,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pinmax],
        intro Plmax, apply absurd Plmax lift_succ_ne_max,
      rewrite [lift_fun_of_ne_max Pinmax, lift_fun_of_ne_max Pjnmax],
        intro Peq, rewrite [-eq_iff_veq],
        exact veq_of_eq (Pinj (lift_succ_inj Peq))
end

lemma lift_fun_inj : injective (@lift_fun n) :=
take f₁ f₂ Peq, funext (λ i,
assert Peqi : lift_fun f₁ (lift_succ i) = lift_fun f₂ (lift_succ i), from congr_fun Peq _,
begin revert Peqi, rewrite [*lift_fun_eq], apply lift_succ_inj end)

lemma lower_inj_apply {f Pinj Pmax} (i : fin n) :
  val (lower_inj f Pinj Pmax i) = val (f (lift_succ i)) :=
by rewrite [↑lower_inj]

definition madd (i j : fin (succ n)) : fin (succ n) :=
mk ((i + j) mod (succ n)) (mod_lt _ !zero_lt_succ)

lemma val_madd : ∀ i j : fin (succ n), val (madd i j) = (i + j) mod (succ n)
| (mk iv ilt) (mk jv jlt) := rfl

lemma madd_inj : ∀ {i : fin (succ n)}, injective (madd i)
| (mk iv ilt) :=
take j₁ j₂, fin.destruct j₁ (fin.destruct j₂ (λ jv₁ jlt₁ jv₂ jlt₂, begin
  rewrite [↑madd, -eq_iff_veq],
  intro Peq, congruence,
  rewrite [-(mod_eq_of_lt jlt₁), -(mod_eq_of_lt jlt₂)],
  apply mod_eq_mod_of_add_mod_eq_add_mod_left Peq
end))

end

section zn
open nat fin eq.ops algebra
variable {n : nat}

lemma val_mod : ∀ i : fin (succ n), (val i) mod (succ n) = val i
| (mk iv ilt) := by esimp; rewrite [ mod_eq_of_lt ilt]

definition minv : ∀ i : fin (succ n), fin (succ n)
| (mk iv ilt) := mk ((succ n - iv) mod succ n) (mod_lt _ !zero_lt_succ)

lemma madd_comm (i j : fin (succ n)) : madd i j = madd j i :=
by apply eq_of_veq; rewrite [*val_madd, add.comm (val i)]

lemma zero_madd (i : fin (succ n)) : madd (zero n) i = i :=
by apply eq_of_veq; rewrite [val_madd, ↑zero, nat.zero_add, mod_eq_of_lt (is_lt i)]

lemma madd_zero (i : fin (succ n)) : madd i (zero n) = i :=
!madd_comm ▸ zero_madd i

lemma madd_assoc (i j k : fin (succ n)) : madd (madd i j) k = madd i (madd j k) :=
by apply eq_of_veq; rewrite [*val_madd, mod_add_mod, add_mod_mod, add.assoc (val i)]

lemma madd_left_inv : ∀ i : fin (succ n), madd (minv i) i = zero n
| (mk iv ilt) := eq_of_veq (by
  rewrite [val_madd, ↑minv, ↑zero, mod_add_mod, sub_add_cancel (nat.le_of_lt ilt), mod_self])

definition madd_is_comm_group [instance] : add_comm_group (fin (succ n)) :=
add_comm_group.mk madd madd_assoc (zero n) zero_madd madd_zero minv madd_left_inv madd_comm

example (i j : fin (succ n)) : i + j = j + i := add.comm i j
end zn

section unused

definition madd₁ : ∀ {n : nat} (i j : fin n), fin n
| 0 (mk iv ilt) _ := absurd ilt !not_lt_zero
| (succ n) (mk iv ilt) (mk jv jlt) := mk ((iv + jv) mod (succ n)) (mod_lt _ !zero_lt_succ)

variable {n : nat}
-- these become trivial once the group operation of madd is established
definition max_sub : fin (succ n) → fin (succ n)
| (mk iv ilt) := mk (n - iv) (sub_lt_succ n _)

definition sub_max : fin (succ n) → fin (succ n)
| (mk iv ilt) := mk (succ iv mod (succ n)) (mod_lt _ !zero_lt_succ)

lemma madd_max_sub_eq_max : ∀ i : fin (succ n), madd (max_sub i) i = maxi
| (mk iv ilt) := begin
  esimp [madd, max_sub, maxi],
  congruence,
  rewrite [@sub_add_cancel n iv (le_of_lt_succ ilt), mod_eq_of_lt !lt_succ_self]
  end

lemma madd_sub_max_eq : ∀ i : fin (succ n), madd (sub_max i) maxi = i
| (mk iv ilt) :=
  assert Pd : decidable (iv = n), from _, begin
  esimp [madd, sub_max, maxi],
  congruence,
  cases Pd with Pe Pne,
    rewrite [Pe, mod_self, zero_add n, mod_eq_of_lt !lt_succ_self],
    assert Plt : succ iv < succ n,
      apply succ_lt_succ, exact lt_of_le_and_ne (le_of_lt_succ ilt) Pne,
    check_expr mod_eq_of_lt Plt,
    rewrite [(mod_eq_of_lt Plt), succ_add, -add_succ, add_mod_self, mod_eq_of_lt ilt]
  end

end unused

end migration

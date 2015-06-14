/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .hom .perm .finsubg

namespace group
open finset algebra function

local attribute perm.f [coercion]

section def
variables {G S : Type}
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS

definition orbit (hom : G → perm S) (H : finset G) (a : S) : finset S :=
           image (move_by a) (image hom H)

variable [deceqG : decidable_eq G]
include deceqG -- required by {x ∈ H |p x} filtering

definition moverset (hom : G → perm S) (H : finset G) (a b : S) : finset G :=
           {f ∈ H | hom f a = b}

definition stab (hom : G → perm S) (H : finset G) (a : S) : finset G :=
           {f ∈ H | hom f a = a}

end def

section orbit_stabilizer

variables {G S : Type}
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS
variable [deceqG : decidable_eq G]
include deceqG

-- these are already specified by stab hom H a
variables {hom : G → perm S} {H : finset G} {a : S}

variable [Hom : is_hom_class hom]
include Hom

lemma exists_of_orbit {b : S} : b ∈ orbit hom H a → ∃ h, h ∈ H ∧ hom h a = b :=
      assume Pb,
      obtain p (Pp₁ : p ∈ image hom H) (Pp₂ : move_by a p = b), from exists_of_mem_image Pb,
      obtain h (Ph₁ : h ∈ H) (Ph₂ : hom h = p), from exists_of_mem_image Pp₁,
      assert Phab : hom h a = b, from calc
        hom h a = p a : Ph₂
            ... = b   : Pp₂,
      exists.intro h (and.intro Ph₁ Phab)

lemma stab_lmul {f g : G} : g ∈ stab hom H a → hom (f*g) a = hom f a :=
      assume Pgstab,
      assert Pg : hom g a = a, from of_mem_filter Pgstab, calc
        hom (f*g) a = perm.f ((hom f) * (hom g)) a : is_hom hom
                ... = ((hom f) ∘ (hom g)) a        : rfl
                ... = (hom f) a                    : Pg

lemma stab_subset : stab hom H a ⊆ H :=
      begin
        apply subset_of_forall, intro f Pfstab, apply mem_of_mem_filter Pfstab
      end

lemma reverse_move {h g : G} : g ∈ moverset hom H a (hom h a) → hom (h⁻¹*g) a = a :=
      assume Pg,
      assert Pga : hom g a = hom h a, from of_mem_filter Pg, calc
      hom (h⁻¹*g) a = perm.f ((hom h⁻¹) * (hom g)) a : is_hom hom
      ... = ((hom h⁻¹) ∘ hom g) a        : rfl
      ... = ((hom h⁻¹) ∘ hom h) a        : {Pga}
      ... = perm.f ((hom h⁻¹) * hom h) a : rfl
      ... = perm.f ((hom h)⁻¹ * hom h) a : hom_map_inv hom h
      ... = (1 : perm S) a               : mul.left_inv (hom h)
      ... = a                            : rfl

lemma moverset_inj_on_orbit : set.inj_on (moverset hom H a) (ts (orbit hom H a)) :=
      take b1 b2,
      assume Pb1, obtain h1 Ph1₁ Ph1₂, from exists_of_orbit Pb1,
      assert Ph1b1 : h1 ∈ moverset hom H a b1,
        from mem_filter_of_mem Ph1₁ Ph1₂,
      assume Psetb2 Pmeq, begin
        subst b1,
        rewrite Pmeq at Ph1b1,
        apply of_mem_filter Ph1b1
      end

variable [subgH : is_finsubg H]
include subgH

lemma subg_stab_of_move {h g : G} :
      h ∈ H → g ∈ moverset hom H a (hom h a) → h⁻¹*g ∈ stab hom H a :=
      assume Ph Pg,
      assert Phinvg : h⁻¹*g ∈ H, from begin
        apply finsubg_mul_closed H,
          apply finsubg_has_inv H, assumption,
          apply mem_of_mem_filter Pg
        end,
      mem_filter_of_mem Phinvg (reverse_move Pg)

lemma subg_stab_closed : finset_mul_closed_on (stab hom H a) :=
      take f g, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assume Pgstab,
      assert Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = (hom f) a : stab_lmul Pgstab
        ... = a : Pf,
      assert PfginH : (f*g) ∈ H,
        from finsubg_mul_closed H f g (mem_of_mem_filter Pfstab) (mem_of_mem_filter Pgstab),
      mem_filter_of_mem PfginH Pfg

lemma subg_stab_has_one : 1 ∈ stab hom H a :=
      assert P : hom 1 a = a, from calc
        hom 1 a = (1 : perm S) a : {hom_map_one hom}
        ... = a : rfl,
      assert PoneinH : 1 ∈ H, from finsubg_has_one H,
      mem_filter_of_mem PoneinH P

lemma subg_stab_has_inv : finset_has_inv (stab hom H a) :=
      take f, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assert Pfinv : hom f⁻¹ a = a, from calc
        hom f⁻¹ a = hom f⁻¹ ((hom f) a) : Pf
        ... = perm.f ((hom f⁻¹) * (hom f)) a : rfl
        ... = hom (f⁻¹ * f) a                : is_hom hom
        ... = hom 1 a                        : mul.left_inv
        ... = (1 : perm S) a : hom_map_one hom,
      assert PfinvinH : f⁻¹ ∈ H, from finsubg_has_inv H f (mem_of_mem_filter Pfstab),
      mem_filter_of_mem PfinvinH Pfinv

definition subg_stab_is_finsubg [instance] :
           is_finsubg (stab hom H a) :=
           is_finsubg.mk subg_stab_has_one subg_stab_closed subg_stab_has_inv

lemma subg_lcoset_eq_moverset {h : G} :
      h ∈ H → fin_lcoset (stab hom H a) h = moverset hom H a (hom h a) :=
      assume Ph, ext (take g, iff.intro
      (assume Pl, obtain f (Pf₁ : f ∈ stab hom H a) (Pf₂ : h*f = g), from exists_of_mem_image Pl,
       assert Pfstab : hom f a = a, from of_mem_filter Pf₁,
       assert PginH : g ∈ H, begin
        subst Pf₂,
        apply finsubg_mul_closed H,
          assumption,
          apply mem_of_mem_filter Pf₁
        end,
      assert Pga : hom g a = hom h a, from calc
        hom g a = hom (h*f) a : by subst g
        ... = hom h a         : stab_lmul Pf₁,
      mem_filter_of_mem PginH Pga)
      (assume Pr, begin
       rewrite [↑fin_lcoset, mem_image_iff],
       existsi h⁻¹*g,
       split,
         exact subg_stab_of_move Ph Pr,
         apply mul_inv_cancel_left
       end))

lemma subg_moverset_of_orbit_is_lcoset_of_stab (b : S) :
      b ∈ orbit hom H a → ∃ h, h ∈ H ∧ fin_lcoset (stab hom H a) h = moverset hom H a b :=
      assume Porb,
      obtain p (Pp₁ : p ∈ image hom H) (Pp₂ : move_by a p = b), from exists_of_mem_image Porb,
      obtain h (Ph₁ : h ∈ H) (Ph₂ : hom h = p), from exists_of_mem_image Pp₁,
      assert Phab : hom h a = b, from by subst p; assumption,
      exists.intro h (and.intro Ph₁ (Phab ▸ subg_lcoset_eq_moverset Ph₁))

lemma subg_lcoset_of_stab_is_moverset_of_orbit (h : G) :
      h ∈ H → ∃ b, b ∈ orbit hom H a ∧ moverset hom H a b = fin_lcoset (stab hom H a) h :=
      assume Ph,
      have Pha : (hom h a) ∈ orbit hom H a, by
        apply mem_image_of_mem; apply mem_image_of_mem; exact Ph,
      exists.intro (hom h a) (and.intro Pha (eq.symm (subg_lcoset_eq_moverset Ph)))

lemma subg_moversets_of_orbit_eq_stab_lcosets :
      image (moverset hom H a) (orbit hom H a) = fin_lcosets (stab hom H a) H :=
      ext (take s, iff.intro
      (assume Pl, obtain b Pb₁ Pb₂, from exists_of_mem_image Pl,
      obtain h Ph, from subg_moverset_of_orbit_is_lcoset_of_stab b Pb₁, begin
      rewrite [↑fin_lcosets, mem_image_eq],
      existsi h, subst Pb₂, assumption
      end)
      (assume Pr, obtain h Ph₁ Ph₂, from exists_of_mem_image Pr,
      obtain b Pb, from @subg_lcoset_of_stab_is_moverset_of_orbit G S ambientG finS deceqS deceqG hom H a Hom subgH h Ph₁, begin
      rewrite [mem_image_eq],
      existsi b, subst Ph₂, assumption
      end))

open nat

theorem orbit_stabilizer_theorem : card H = card (orbit hom H a) * card (stab hom H a) :=
        calc card H = card (fin_lcosets (stab hom H a) H) * card (stab hom H a) : lagrange_theorem stab_subset
        ... = card (image (moverset hom H a) (orbit hom H a)) * card (stab hom H a) : subg_moversets_of_orbit_eq_stab_lcosets
        ... = card (orbit hom H a) * card (stab hom H a) : card_image_eq_of_inj_on moverset_inj_on_orbit

end orbit_stabilizer

section perm_fin
open fin nat eq.ops

definition madd : ∀ {n : nat} (i j : fin n), fin n
| 0 (mk iv ilt) _ := absurd ilt !not_lt_zero
| (succ n) (mk iv ilt) (mk jv jlt) := mk ((iv + jv) mod (succ n)) (mod_lt _ !zero_lt_succ)

lemma sub_lt_succ (a b : nat) : a - b < succ a := lt_succ_of_le (sub_le a b)

variable {n : nat}

lemma mod_eq_of_add_mod_eq : ∀ (i j₁ j₂ : nat), (i + j₁) mod n = (i + j₂) mod n → j₁ mod n  = j₂ mod n := sorry
lemma mod_add_mod : ∀ (i j : nat), (i mod n + j) mod n = (i + j) mod n := sorry
lemma add_mod_mod (i j : nat) : (i + j mod n) mod n = (i + j) mod n :=
by rewrite [add.comm i, mod_add_mod, add.comm j]

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

definition max [reducible] : fin (succ n) :=
mk n !lt_succ_self

definition max_sub : fin (succ n) → fin (succ n)
| (mk iv ilt) := mk (n - iv) (sub_lt_succ n _)

definition sub_max : fin (succ n) → fin (succ n)
| (mk iv ilt) := mk (succ iv mod (succ n)) (mod_lt _ !zero_lt_succ)

lemma val_madd : ∀ i j : fin (succ n), val (madd i j) = (i + j) mod (succ n)
| (mk iv ilt) (mk jv jlt) := by rewrite [val_mk]

lemma madd_inj : ∀ {i : fin (succ n)}, injective (madd i)
| (mk iv ilt) :=
take j₁ j₂, fin.destruct j₁ (fin.destruct j₂ (λ jv₁ jlt₁ jv₂ jlt₂, begin
  rewrite [↑madd, -eq_iff_veq],
  intro Peq, congruence,
  rewrite [-(mod_eq_of_lt jlt₁), -(mod_eq_of_lt jlt₂)],
  apply mod_eq_of_add_mod_eq iv _ _ Peq
end))

lemma madd_max_sub_eq_max : ∀ i : fin (succ n), madd (max_sub i) i = max
| (mk iv ilt) := begin
  esimp [madd, max_sub, max],
  congruence,
  rewrite [@sub_add_cancel n iv (le_of_lt_succ ilt), mod_eq_of_lt !lt_succ_self]
  end

lemma madd_sub_max_eq : ∀ i : fin (succ n), madd (sub_max i) max = i
| (mk iv ilt) :=
  assert Pd : decidable (iv = n), from _, begin
  esimp [madd, sub_max, max],
  congruence,
  cases Pd with Pe Pne,
    rewrite [Pe, mod_self, zero_add n, mod_eq_of_lt !lt_succ_self],
    assert Plt : succ iv < succ n,
      apply succ_lt_succ, exact lt_of_le_and_ne (le_of_lt_succ ilt) Pne,
    check_expr mod_eq_of_lt Plt,
    rewrite [(mod_eq_of_lt Plt), succ_add, -add_succ, add_mod_self, mod_eq_of_lt ilt]
  end

lemma ne_max_of_lt_max {i : fin (succ n)} : i < n → i ≠ max :=
by intro hlt he; substvars; exact absurd hlt (lt.irrefl n)

lemma lt_max_of_ne_max {i : fin (succ n)} : i ≠ max → i < n :=
assume hne  : i ≠ max,
assert visn : val i < nat.succ n, from val_lt i,
assert aux  : val (@max n) = n,   from rfl,
assert vne  : val i ≠ n, from
  assume he,
    have vivm : val i = val (@max n), from he ⬝ aux⁻¹,
    absurd (eq_of_veq vivm) hne,
lt_of_le_of_ne (le_of_lt_succ visn) vne

lemma lift_succ_ne_max {i : fin n} : lift_succ i ≠ max :=
begin
  cases i with v hlt, esimp [lift_succ, lift, max], intro he,
  injection he, substvars,
  exact absurd hlt (lt.irrefl v)
end

lemma lift_succ_inj : injective (@lift_succ n) :=
take i j, destruct i (destruct j (take iv ilt jv jlt Pmkeq,
  begin congruence, apply fin.no_confusion Pmkeq, intros, assumption end))

lemma lt_of_inj_max (f : fin (succ n) → fin (succ n)) :
  injective f → (f max = max) → ∀ i, i < n → f i < n :=
assume Pinj Peq, take i, assume Pilt,
assert P1 : f i = f max → i = max, from assume Peq, Pinj i max Peq,
have P : f i ≠ max, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max P

definition lift_fun : (fin n → fin n) → (fin (succ n) → fin (succ n)) :=
λ f i, dite (i = max) (λ Pe, max) (λ Pne, lift_succ (f (mk i (lt_max_of_ne_max Pne))))

definition lower_inj (f : fin (succ n) → fin (succ n)) (inj : injective f) :
  f max = max → fin n → fin n :=
assume Peq, take i, mk (f (lift_succ i)) (lt_of_inj_max f inj Peq (lift_succ i) (lt_max_of_ne_max lift_succ_ne_max))

lemma lift_fun_max {f : fin n → fin n} : lift_fun f max = max :=
begin rewrite [↑lift_fun, dif_pos rfl] end

lemma lift_fun_of_ne_max {f : fin n → fin n} {i} (Pne : i ≠ max) :
  lift_fun f i = lift_succ (f (mk i (lt_max_of_ne_max Pne))) :=
begin rewrite [↑lift_fun, dif_neg Pne] end

lemma lift_fun_eq {f : fin n → fin n} {i : fin n} :
  lift_fun f (lift_succ i) = lift_succ (f i) :=
begin
rewrite [lift_fun_of_ne_max lift_succ_ne_max], congruence, congruence,
rewrite [-eq_iff_veq, val_mk, ↑lift_succ, -val_lift]
end

lemma lift_fun_of_inj {f : fin n → fin n} : injective f → injective (lift_fun f) :=
assume Pinj, take i j,
assert Pdi : decidable (i = max), from _, assert Pdj : decidable (j = max), from _,
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

definition lift_perm (p : perm (fin n)) : perm (fin (succ n)) :=
perm.mk (lift_fun p) (lift_fun_of_inj (perm.inj p))

definition lower_perm (p : perm (fin (succ n))) (P : p max = max) : perm (fin n) :=
perm.mk (lower_inj p (perm.inj p) P)
  (take i j, begin
  rewrite [-eq_iff_veq, *lower_inj_apply, eq_iff_veq],
  apply injective_compose (perm.inj p) lift_succ_inj
  end)

lemma lift_lower_eq : ∀ {p : perm (fin (succ n))} (P : p max = max),
  lift_perm (lower_perm p P) = p
| (perm.mk pf Pinj) := assume Pmax, begin
  rewrite [↑lift_perm], congruence,
  apply funext, intro i,
  assert Pfmax : pf max = max, apply Pmax,
  assert Pd : decidable (i = max),
    exact _,
    cases Pd with Pe Pne,
      rewrite [Pe, Pfmax], apply lift_fun_max,
      rewrite [lift_fun_of_ne_max Pne, ↑lower_perm, ↑lift_succ],
      rewrite [-eq_iff_veq, -val_lift, lower_inj_apply, eq_iff_veq],
      congruence, rewrite [-eq_iff_veq]
  end

lemma lift_perm_inj : injective (@lift_perm n) :=
take p1 p2, assume Peq, eq_of_feq (lift_fun_inj (feq_of_eq Peq))

lemma lift_perm_inj_on_univ : set.inj_on (@lift_perm n) (ts univ) :=
eq.symm to_set_univ ▸ iff.elim_left set.injective_iff_inj_on_univ lift_perm_inj

lemma lift_to_stab : image (@lift_perm n) univ = stab id univ max :=
ext (take (pp : perm (fin (succ n))), iff.intro
  (assume Pimg, obtain p P_ Pp, from exists_of_mem_image Pimg,
  assert Ppp : pp max = max, from calc
    pp max = lift_perm p max : {eq.symm Pp}
       ... = lift_fun p max : rfl
       ... = max : lift_fun_max,
  mem_filter_of_mem !mem_univ Ppp)
  (assume Pstab,
  assert Ppp : pp max = max, from of_mem_filter Pstab,
  mem_image_of_mem_of_eq !mem_univ (lift_lower_eq Ppp)))

definition move_from_max_to (i : fin (succ n)) : perm (fin (succ n)) :=
perm.mk (madd (sub_max i)) madd_inj

lemma orbit_max : orbit (@id (perm (fin (succ n)))) univ max = univ :=
ext (take i, iff.intro
  (assume P, !mem_univ)
  (assume P, begin
    apply mem_image_of_mem_of_eq,
      apply mem_image_of_mem_of_eq,
        apply mem_univ (move_from_max_to i), apply rfl,
      apply madd_sub_max_eq
    end))

lemma card_orbit_max : card (orbit (@id (perm (fin (succ n)))) univ max) = succ n :=
calc card (orbit (@id (perm (fin (succ n)))) univ max) = card univ : {orbit_max}
                                                   ... = succ n : card_fin (succ n)

open fintype

lemma card_lift_to_stab : card (stab (@id (perm (fin (succ n)))) univ max) = card (perm (fin n)) :=
 calc finset.card (stab (@id (perm (fin (succ n)))) univ max)
    = finset.card (image (@lift_perm n) univ) : {eq.symm lift_to_stab}
... = card univ : card_image_eq_of_inj_on lift_perm_inj_on_univ

lemma card_perm_step : card (perm (fin (succ n))) = (succ n) * card (perm (fin n)) :=
 calc card (perm (fin (succ n)))
    = card (orbit id univ max) * card (stab id univ max) : orbit_stabilizer_theorem
... = (succ n) * card (stab id univ max) : {card_orbit_max}
... = (succ n) * card (perm (fin n)) : {card_lift_to_stab}


end perm_fin

section zn
open nat fin eq.ops
variable {n : nat}

lemma val_mod : ∀ i : fin (succ n), (val i) mod (succ n) = val i
| (mk iv ilt) := by rewrite [*val_mk, mod_eq_of_lt ilt]

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
| (mk iv ilt) := eq_of_veq begin
  rewrite [val_madd, ↑minv, ↑zero, mod_add_mod, sub_add_cancel (nat.le_of_lt ilt), mod_self]
  end

definition madd_is_comm_group [instance] : add_comm_group (fin (succ n)) :=
add_comm_group.mk madd madd_assoc (zero n) zero_madd madd_zero minv madd_left_inv madd_comm

example (i j : fin (succ n)) : i + j = j + i := add.comm i j
end zn
end group

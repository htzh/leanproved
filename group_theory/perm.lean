/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .extra .finfun

open nat function list algebra


namespace group
open fintype

section perm
variable {A : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA
variable {f : A → A}

lemma perm_surj : injective f → surjective f :=
      surj_of_inj_eq_card (eq.refl (card A))

variable (perm : injective f)

definition perm_inv : A → A :=
      right_inv (perm_surj perm)
lemma perm_inv_right : f ∘ (perm_inv perm) = id :=
      id_of_right_inv (perm_surj perm)
lemma perm_inv_left : (perm_inv perm) ∘ f = id :=
      left_inv_of_right_inv_of_inj perm (perm_inv_right perm)
lemma perm_inv_inj : injective (perm_inv perm) :=
      injective_of_has_left_inverse (exists.intro f (perm_inv_right perm))
      
end perm

structure perm (A : Type) [h : fintype A] : Type :=
  (f : A → A) (inj : injective f)
local attribute perm.f [coercion]
    
section perm
variable {A : Type}
variable [finA : fintype A]
include finA

definition move_by [reducible] (a : A) (f : perm A) : A := f a

variable [deceqA : decidable_eq A]
include deceqA

lemma perm.has_decidable_eq [instance] : decidable_eq (perm A) :=
      take f g,
      perm.destruct f (λ ff finj, perm.destruct g (λ gf ginj,
      decidable.rec_on (decidable_eq_fun ff gf)
      (λ Peq, decidable.inl (by substvars))
      (λ Pne, decidable.inr begin intro P, injection P, contradiction end)))

definition perm.mul (f g : perm A) :=
           perm.mk (f∘g) (injective_compose (perm.inj f) (perm.inj g))
definition perm.one : perm A := perm.mk id id_is_inj
definition perm.inv (f : perm A) := let inj := perm.inj f in
           perm.mk (perm_inv inj) (perm_inv_inj inj)

local infix `^` := perm.mul
lemma perm.assoc (f g h : perm A) : f ^ g ^ h = f ^ (g ^ h) := rfl
lemma perm.one_mul (p : perm A) : perm.one ^ p = p :=
      perm.cases_on p (λ f inj, rfl)
lemma perm.mul_one (p : perm A) : p ^ perm.one = p :=
      perm.cases_on p (λ f inj, rfl)
lemma perm.left_inv (p : perm A) : (perm.inv p) ^ p = perm.one :=
      begin rewrite [↑perm.one], generalize @id_is_inj A,
      rewrite [-perm_inv_left (perm.inj p)], intros, exact rfl
      end
lemma perm.right_inv (p : perm A) : p ^ (perm.inv p) = perm.one :=
      begin rewrite [↑perm.one], generalize @id_is_inj A,
      rewrite [-perm_inv_right (perm.inj p)], intros, exact rfl
      end

definition perm_group [instance] : group (perm A) :=
           group.mk perm.mul perm.assoc perm.one perm.one_mul perm.mul_one perm.inv perm.left_inv
check @perm_group

end perm

section less_than

end less_than
end group


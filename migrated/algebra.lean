/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group
open algebra function eq.ops

namespace migration

section group

variables {A : Type} [ambA : group A]
include ambA

theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
begin rewrite [eq_inv_iff_eq_inv], apply eq.symm, exact inv_eq_of_mul_eq_one H end

definition conj_by (g a : A) := g * a * g⁻¹
definition is_conjugate (a b : A) := ∃ x, conj_by x b = a

-- too precious to make it wider scope. group.ops can now be openned without it.
local infixl `~` := is_conjugate
local infixr `∘c`:55 := conj_by

lemma conj_compose (f g a : A) : f ∘c g ∘c a = f*g ∘c a :=
      calc f ∘c g ∘c a = f * (g * a * g⁻¹) * f⁻¹ : rfl
      ... = f * (g * a) * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * (g⁻¹ * f⁻¹) : mul.assoc
      ... = f * g * a * (f * g)⁻¹ : mul_inv
lemma conj_id (a : A) : 1 ∘c a = a :=
      calc 1 * a * 1⁻¹ = a * 1⁻¹ : one_mul
      ... = a * 1 : one_inv
      ... = a : mul_one
lemma conj_one (g : A) : g ∘c 1 = 1 :=
      calc g * 1 * g⁻¹ = g * g⁻¹ : mul_one
      ... = 1 : mul.right_inv
lemma conj_inv_cancel (g : A) : ∀ a, g⁻¹ ∘c g ∘c a = a :=
      assume a, calc
      g⁻¹ ∘c g ∘c a = g⁻¹*g ∘c a : conj_compose
      ... = 1 ∘c a : mul.left_inv
      ... = a : conj_id

lemma conj_inv (g : A) : ∀ a, (g ∘c a)⁻¹ = g ∘c a⁻¹ :=
take a, calc
(g * a * g⁻¹)⁻¹ = g⁻¹⁻¹ * (g * a)⁻¹   : mul_inv
            ... = g⁻¹⁻¹ * (a⁻¹ * g⁻¹) : mul_inv
            ... = g⁻¹⁻¹ * a⁻¹ * g⁻¹   : mul.assoc
            ... = g * a⁻¹ * g⁻¹       : inv_inv

lemma is_conj.refl (a : A) : a ~ a := exists.intro 1 (conj_id a)
lemma is_conj.symm (a b : A) : a ~ b → b ~ a :=
      assume Pab, obtain x (Pconj : x ∘c b = a), from Pab,
      assert Pxinv : x⁻¹ ∘c x ∘c b = x⁻¹ ∘c a, from (congr_arg2 conj_by (eq.refl x⁻¹) Pconj),
      exists.intro x⁻¹ (eq.symm (conj_inv_cancel x b ▸ Pxinv))
lemma is_conj.trans (a b c : A) : a ~ b → b ~ c → a ~ c :=
      assume Pab, assume Pbc,
      obtain x (Px : x ∘c b = a), from Pab,
      obtain y (Py : y ∘c c = b), from Pbc,
      exists.intro (x*y) (calc
      x*y ∘c c = x ∘c y ∘c c : conj_compose
      ... = x ∘c b : Py
      ... = a : Px)

end group

end migration

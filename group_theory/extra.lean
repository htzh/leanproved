/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
-- These belong in the library somewhere.
import algebra.group data.set data.set.function
-- Thought this might be useful in converting different forms of Prop
theorem and_imp_curry (a b c : Prop) : (a ∧ b → c) = (a → b → c) :=
        propext (iff.intro (λ Pl a b, Pl (and.intro a b))
                           (λ Pr Pand, Pr (and.left Pand) (and.right Pand)))

definition swap {A B C : Type} (f : A → B → C) : B → A → C := λ x y, f y x

namespace set
section
open function
variables {A B C: Type}
variable {S : set A}
lemma image_subset (S H : set A) : ∀ f : A → B, S ⊆ H → f '[S] ⊆ f '[H] :=
      assume f, assume SsubH,
      begin
      esimp [image, subset, set_of, mem],
      intro x,
      intro Hex,
      cases Hex with y Img,
      exact (exists.intro y (and.intro (SsubH (and.left Img)) (and.right Img)))
      end
end
section
open function
variable {A : Type}
lemma subset.trans (a b c : set A) : a ⊆ b → b ⊆ c → a ⊆ c :=
      begin
      esimp [subset, mem],
      intro f, intro g, intro x, intro ax, exact g (f ax)
      end
end
end set

namespace algebra
section group
variable {A : Type}
variable [s : group A]
include s

lemma comm_one (a : A) : a*1 = 1*a :=
  calc a*1 = a : mul_one
  ... = 1*a : one_mul

lemma comm_mul_eq_one (a b : A) : a*b = 1 = (b*a = 1) :=
  propext (iff.intro
    (assume Pl : a*b = 1, assert Pinv : a⁻¹=b, from inv_eq_of_mul_eq_one Pl,
       by rewrite [eq.symm Pinv, mul.left_inv])
    (assume Pr : b*a = 1, assert Pinv : b⁻¹=a, from inv_eq_of_mul_eq_one Pr,
       by rewrite [eq.symm Pinv, mul.left_inv]))
end group
end algebra

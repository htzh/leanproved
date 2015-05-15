/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
-- These belong in the library somewhere.
import algebra.group data.set
-- Thought this might be useful in converting different forms of Prop
theorem and_imp_curry (a b c : Prop) : (a ∧ b → c) = (a → b → c) :=
        propext (iff.intro (λ Pl a b, Pl (and.intro a b))
                           (λ Pr Pand, Pr (and.left Pand) (and.right Pand)))
theorem and_discharge_left {a b : Prop} : a → (a ∧ b) = b :=
        assume Pa, propext (iff.intro (assume Pab, and.elim_right Pab)
                                      (assume Pb, and.intro Pa Pb))
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

namespace function
section
open set eq.ops
variables {A B C : Type}
definition bijective (f : A → B) := injective f ∧ surjective f
lemma injective_eq_inj_on_univ {f : A → B} : injective f = inj_on f univ :=
  begin
    esimp [injective, inj_on, univ, mem],
    apply propext,
-- ⊢ (∀ (a₁ a₂ : A), f a₁ = f a₂ → a₁ = a₂) ↔ ∀ ⦃x1 x2 : A⦄, true → true → f x1 = f x2 → x1 = x2
    repeat (apply forall_congr; intros),
    rewrite *true_imp
  end
lemma univ_maps_to_univ {f : A → B} : maps_to f univ univ :=
  take a, assume P, trivial
theorem injective_compose {g : B → C} {f : A → B} (Hg : injective g) (Hf : injective f) : injective (g ∘ f) :=
        eq.symm !injective_eq_inj_on_univ ▸ inj_on_compose univ_maps_to_univ (injective_eq_inj_on_univ ▸ Hg) (injective_eq_inj_on_univ ▸ Hf)

lemma surjective_eq_surj_on_univ {f : A → B} : surjective f = surj_on f univ univ :=
  begin
    esimp [surjective, surj_on, univ, image, subset, set_of, mem],
    apply propext,
    apply forall_congr, intro b,
--  ⊢ (∃ (a : A), f a = b) ↔ true → (∃ (x : A), true ∧ f x = b)
    rewrite true_imp,
    apply exists_congr, intro a,
    rewrite true_and
  end

theorem surjective_compose {g : B → C} {f : A → B} (Hg : surjective g) (Hf : surjective f) : surjective (g ∘ f) :=
        eq.symm surjective_eq_surj_on_univ ▸ surj_on_compose (surjective_eq_surj_on_univ ▸ Hg) (surjective_eq_surj_on_univ ▸ Hf)
        
lemma bijective_eq_bij_on_univ {f : A → B} : bijective f = bij_on f univ univ :=
      assert P : maps_to f univ univ, from univ_maps_to_univ, by
      rewrite [↑bijective, ↑bij_on, injective_eq_inj_on_univ, surjective_eq_surj_on_univ, and_discharge_left P]

theorem bijective_compose {g : B → C} {f : A → B} (Hg : bijective g) (Hf : bijective f) : bijective (g ∘ f) :=
        eq.symm bijective_eq_bij_on_univ ▸ bij_on_compose (bijective_eq_bij_on_univ ▸ Hg) (bijective_eq_bij_on_univ ▸ Hf)
end
end function

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

/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data.set .subgroup
namespace group_hom
open algebra
-- ⁻¹ in eq.ops conflicts with group ⁻¹
-- open eq.ops
notation H1 ▸ H2 := eq.subst H1 H2
open set
open function
open algebra.group.ops
open quot
local attribute set [reducible]

section
variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2
definition is_hom (f : A → B) := ∀ a b, f (a*b) = (f a)*(f b)
definition is_iso (f : A → B) := injective f ∧ is_hom f
variable f : A → B
variable Hom : is_hom f
definition ker : set A := {a : A | f a = 1}
theorem hom_map_one : f 1 = 1 :=
        have P : f 1 = (f 1) * (f 1), from
        calc f 1 = f (1*1) : mul_one
        ... = (f 1) * (f 1) : Hom,
        eq.symm (mul.right_inv (f 1) ▸ (mul_inv_eq_of_eq_mul P))
check hom_map_one
theorem hom_map_inv (a : A) : f a⁻¹ = (f a)⁻¹ :=
        assert P : f 1 = 1, from hom_map_one f Hom,
        assert P1 : f (a⁻¹ * a) = 1, from (eq.symm (mul.left_inv a)) ▸ P,
        assert P2 : (f a⁻¹) * (f a) = 1, from (Hom a⁻¹ a) ▸ P1,
        assert P3 : (f a⁻¹) * (f a) = (f a)⁻¹ * (f a), from eq.symm (mul.left_inv (f a)) ▸ P2,
        mul_right_cancel P3
theorem hom_map_mul_closed (H : set A) : mul_closed_on H → mul_closed_on (f '[H]) :=
        assume Pclosed, assume b1, assume b2,
        assume Pimage : b1 ∈ f '[ H] ∧ b2 ∈ f '[ H],
        obtain a1 (Pa1 : a1 ∈ H ∧ f a1 = b1), from and.left Pimage,
        obtain a2 (Pa2 : a2 ∈ H ∧ f a2 = b2), from and.right Pimage,
        assert Pa1a2 : a1 * a2 ∈ H, from Pclosed a1 a2 (and.intro (and.left Pa1) (and.left Pa2)),
        assert Pb1b2 : f (a1 * a2) = b1 * b2, from calc
        f (a1 * a2) = f a1 * f a2 : Hom a1 a2
        ... = b1 * f a2 : {and.right Pa1}
        ... = b1 * b2 : {and.right Pa2},
        in_image Pa1a2 Pb1b2
lemma ker.has_one : 1 ∈ ker f := hom_map_one f Hom
-- lean does not see Hom is used in the tactic rewrite so declare Hom explicitly
lemma ker.has_inv (Hom : is_hom f) : subgroup.has_inv (ker f) :=
      take a, assume Pa : f a = 1, calc
      f a⁻¹ = (f a)⁻¹ : by rewrite (hom_map_inv f Hom)
      ... = 1⁻¹ : by rewrite Pa
      ... = 1 : by rewrite inv_one
lemma ker.mul_closed (Hom : is_hom f) : mul_closed_on (ker f) :=
      take x y, assume Pand : f x = 1 ∧ f y = 1, calc
      f (x*y) = (f x) * (f y) : by rewrite Hom
      ... = 1 : by rewrite [and.left Pand, and.right Pand, mul_one]
lemma ker.normal (Hom : is_hom f) : same_left_right_coset (ker f) :=
      take a, funext (assume x, begin
      esimp [ker, set_of, glcoset, grcoset],
      rewrite [*Hom, comm_mul_eq_one (f a⁻¹) (f x)]
      end)
definition ker_is_normal_subgroup : is_normal_subgroup (ker f) :=
  is_normal_subgroup.mk (ker.has_one f Hom) (ker.mul_closed f Hom) (ker.has_inv f Hom)
    (ker.normal f Hom)
end
section
variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2
variable f : A → B
variable Hom : is_hom f

variable {H : set A}
variable [is_subgH : is_subgroup H]
include is_subgH
theorem hom_map_subgroup (Hom : is_hom f) : is_subgroup (f '[H]) :=
        have Pone : 1 ∈ f '[H], from in_image subg_has_one (hom_map_one f Hom),
        have Pclosed : mul_closed_on (f '[H]), from hom_map_mul_closed f Hom H subg_mul_closed,
        assert Pinv : ∀ b, b ∈ f '[H] → b⁻¹ ∈ f '[H], from
          assume b, assume Pimg,
          obtain a (Pa : a ∈ H ∧ f a = b), from Pimg,
          assert Painv : a⁻¹ ∈ H, from subg_has_inv a (and.left Pa),
          assert Pfainv : (f a)⁻¹ ∈ f '[H], from in_image Painv (hom_map_inv f Hom a),
          and.right Pa ▸ Pfainv,
        is_subgroup.mk Pone Pclosed Pinv

end

section hom_theorem
check @ker_is_normal_subgroup
variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2
structure hom_class [class] : Type :=
  (hom : A → B) (is_hom : @is_hom A B s1 s2 hom)
attribute hom_class.hom [coercion]
-- need to spell out that f is A to B otherwise it is ambiguous
variable [f : @hom_class A B _ _]
include f
-- bridge to lemmas that don't use inference but depend on the Prop directly
private lemma Hom : is_hom f := @hom_class.is_hom A B s1 s2 _
check @Hom
definition ker_nsubg [instance] : is_normal_subgroup (ker f) :=
           is_normal_subgroup.mk (ker.has_one f Hom) (ker.mul_closed f Hom)
           (ker.has_inv f Hom) (ker.normal f Hom)
definition quot_over_ker [instance] : group (coset_of (ker f)) := mk_quotient_group (ker f)
-- under the wrap the tower of concepts collapse to a simple condition
example (a x : A) : (x ∈ a ∘> ker f) = (f (a⁻¹*x) = 1) := rfl
lemma ker_coset_same_val (a b : A): same_lcoset (ker f) a b → f a = f b :=
      assume Psame,
      assert Pin : f (b⁻¹*a) = 1, from subg_same_lcoset_in_lcoset a b Psame,
      assert P : (f b)⁻¹ * (f a) = 1, from calc
      (f b)⁻¹ * (f a) = (f b⁻¹) * (f a) :  (hom_map_inv f Hom)
      ... = f (b⁻¹*a) : by rewrite Hom
      ... = 1 : by rewrite Pin,
      eq.symm (inv_inv (f b) ▸ inv_eq_of_mul_eq_one P)
definition ker_natural_map : (coset_of (ker f)) → B :=
           quot.lift f ker_coset_same_val

example (a : A) : ker_natural_map ⟦a⟧ = f a := rfl
lemma ker_coset_hom (a b : A) : ker_natural_map (⟦a⟧*⟦b⟧) = (ker_natural_map ⟦a⟧) * (ker_natural_map ⟦b⟧) := calc
      ker_natural_map (⟦a⟧*⟦b⟧) = ker_natural_map ⟦a*b⟧ : rfl
      ... = f (a*b) : rfl
      ... = (f a) * (f b) : by rewrite Hom
      ... = (ker_natural_map ⟦a⟧) * (ker_natural_map ⟦b⟧) : rfl

lemma ker_map_is_hom : is_hom (ker_natural_map : coset_of (ker f) → B) :=
  take aK bK,
      quot.ind (λ a, quot.ind (λ b, ker_coset_hom a b) bK) aK

check @subg_in_lcoset_same_lcoset
lemma ker_coset_inj (a b : A) : (ker_natural_map ⟦a⟧ = ker_natural_map ⟦b⟧) → ⟦a⟧ = ⟦b⟧ :=
      assume Pfeq : f a = f b,
      assert Painb : a ∈ b ∘> ker f, from calc
      f (b⁻¹*a) = (f b⁻¹) * (f a) : by rewrite Hom
      ... = (f b)⁻¹ * (f a) : by rewrite (hom_map_inv f Hom)
      ... = (f a)⁻¹ * (f a) : by rewrite Pfeq
      ... = 1 : by rewrite (mul.left_inv (f a)),
      quot.sound (@subg_in_lcoset_same_lcoset _ _ (ker f) _ a b Painb)

lemma ker_map_is_inj : injective (ker_natural_map : coset_of (ker f) → B) :=
  take aK bK,
      quot.ind (λ a, quot.ind (λ b, ker_coset_inj a b) bK) aK
-- a special case of the fundamental homomorphism theorem or the first isomorphism theorem
theorem first_isomorphism_theorem : is_iso (ker_natural_map : coset_of (ker f) → B) :=
  and.intro ker_map_is_inj ker_map_is_hom

end hom_theorem        
end group_hom

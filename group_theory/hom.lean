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
definition ker : set A := λ a, (f a) = 1

check f
check @ker
lemma ker.has_one (Hom : is_hom f) : 1 ∈ ker f := sorry
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
theorem hom_map_mul_closed (Hom : is_hom f) (H : set A) : mul_closed_on H → mul_closed_on (f '[H]) :=
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
end group_hom

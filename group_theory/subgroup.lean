/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data.set data.fintype .extra
open function
-- ⁻¹ in eq.ops conflicts with group ⁻¹
-- open eq.ops
notation H1 ▸ H2 := eq.subst H1 H2
open set
local attribute set [reducible]

namespace algebra

namespace coset
-- semigroup coset definition
section
variable {A : Type}
variable [s : semigroup A]
include s
definition lmul a := λ x, a * x
definition rmul a := λ x, x * a
definition l a (S : set A) := (lmul a) '[S]
definition r a (S : set A) := (rmul a) '[S]
lemma lmul_compose : ∀ a b, (lmul a) ∘ (lmul b) = lmul (a*b) :=
      take a, take b,
      funext (assume x, by
        rewrite [↑function.compose, ↑lmul, mul.assoc])
lemma rmul_compose : ∀ a b, (rmul a) ∘ (rmul b) = rmul (b*a) :=
      take a, take b,
      funext (assume x, by
        rewrite [↑function.compose, ↑rmul, mul.assoc])
lemma lcompose a b (S : set A) : l a (l b S) = l (a*b) S :=
      calc (lmul a) '[(lmul b) '[S]] = ((lmul a) ∘ (lmul b)) '[S] : image_compose
      ... = lmul (a*b) '[S] : lmul_compose
lemma rcompose a b (S : set A) : r a (r b S) = r (b*a) S :=
      calc (rmul a) '[(rmul b) '[S]] = ((rmul a) ∘ (rmul b)) '[S] : image_compose
      ... = rmul (b*a) '[S] : rmul_compose
lemma l_sub a (S H : set A) : S ⊆ H → (l a S) ⊆ (l a H) := image_subset S H (lmul a)
definition l_same S a b := l a S = l b S
definition r_same S a b := r a S = r b S
lemma l_same.refl S (a : A) : l_same S a a := rfl
lemma l_same.symm S (a b : A) : l_same S a b → l_same S b a := eq.symm
lemma l_same.trans S (a b c : A) : l_same S a b → l_same S b c → l_same S a c := eq.trans
example (S : set A) : equivalence (l_same S) := mk_equivalence (l_same S) (l_same.refl S) (l_same.symm S) (l_same.trans S)
end
end coset

section
variable {A : Type}
variable [s : group A]
include s
definition lmul_by (a : A) := λ x, a * x
definition rmul_by (a : A) := λ x, x * a
definition glcoset a (H : set A) : set A := λ x, H (a⁻¹ * x)
definition grcoset H (a : A) : set A := λ x, H (x * a⁻¹)
definition conj_by (g a : A) := g * a * g⁻¹
definition is_conjugate (a b : A) := ∃ x, conj_by x b = a
end

namespace group
  namespace ops
    infixr `∘>`:55 := glcoset -- stronger than = (50), weaker than * (70)
    infixl `<∘`:55 := grcoset
    infixr `∘c`:55 := conj_by
    infixl `~` := is_conjugate
  end ops
end group
    
open group.ops
section
variable {A : Type}
variable [s : group A]
include s

lemma conj_compose (f g a : A) : f ∘c g ∘c a = f*g ∘c a :=
      calc f ∘c g ∘c a = f * (g * a * g⁻¹) * f⁻¹ : rfl
      ... = f * (g * a) * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * (g⁻¹ * f⁻¹) : mul.assoc
      ... = f * g * a * (f * g)⁻¹ : inv_mul
lemma conj_id (a : A) : 1 ∘c a = a :=
      calc 1 * a * 1⁻¹ = a * 1⁻¹ : one_mul
      ... = a * 1 : inv_one
      ... = a : mul_one
lemma conj_one (g : A) : g ∘c 1 = 1 :=
      calc g * 1 * g⁻¹ = g * g⁻¹ : mul_one
      ... = 1 : mul.right_inv
lemma conj_inv_cancel (g : A) : ∀ a, g⁻¹ ∘c g ∘c a = a :=
      assume a, calc
      g⁻¹ ∘c g ∘c a = g⁻¹*g ∘c a : conj_compose
      ... = 1 ∘c a : mul.left_inv
      ... = a : conj_id 
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
lemma glcoset_eq_lcoset a (H : set A) : a ∘> H = coset.l a H :=
      setext
      begin
      intro x,
      rewrite [↑glcoset, ↑coset.l, ↑image, ↑set_of, ↑mem, ↑coset.lmul],
      apply iff.intro,
        intro P1,
        apply (exists.intro (a⁻¹ * x)),
        apply and.intro,
          exact P1,
          exact (mul_inv_cancel_left a x),
        show (∃ (x_1 : A), H x_1 ∧ a * x_1 = x) → H (a⁻¹ * x), from
          assume P2, obtain x_1 P3, from P2,
          have P4 : a * x_1 = x, from and.right P3,
          have P5 : x_1 = a⁻¹ * x, from eq_inv_mul_of_mul_eq P4,
          eq.subst P5 (and.left P3)  
      end
lemma grcoset_eq_rcoset a (H : set A) : H <∘ a = coset.r a H :=
      begin
        rewrite [↑grcoset, ↑coset.r, ↑image, ↑coset.rmul, ↑set_of],
        apply setext, rewrite ↑mem,
        intro x,
        apply iff.intro,
          show H (x * a⁻¹) → (∃ (x_1 : A), H x_1 ∧ x_1 * a = x), from
            assume PH,
              exists.intro (x * a⁻¹)
                           (and.intro PH (inv_mul_cancel_right x a)),
          show (∃ (x_1 : A), H x_1 ∧ x_1 * a = x) → H (x * a⁻¹), from
            assume Pex,
              obtain x_1 Pand, from Pex,
                eq.subst (eq_mul_inv_of_mul_eq (and.right Pand)) (and.left Pand)
      end
lemma glcoset_compose (a b : A) (H : set A) : a ∘> b ∘> H = a*b ∘> H :=
      begin
      rewrite [*glcoset_eq_lcoset], exact (coset.lcompose a b H)
      end
lemma grcoset_compose (a b : A) (H : set A) : H <∘ a <∘ b = H <∘ a*b :=
      begin
      rewrite [*grcoset_eq_rcoset], exact (coset.rcompose b a H)
      end
lemma glcoset_id (H : set A) : 1 ∘> H = H :=
      funext (assume x,
        calc (1 ∘> H) x = H (1⁻¹*x) : rfl
        ... = H (1*x) : {inv_one}
        ... = H x : {one_mul x})
lemma grcoset_id (H : set A) : H <∘ 1 = H :=
      funext (assume x,
        calc H (x*1⁻¹) = H (x*1) : {inv_one}
        ... = H x : {mul_one x})
--lemma glcoset_inv a (H : set A) : a⁻¹ ∘> a ∘> H = H :=
--      funext (assume x,
--        calc glcoset a⁻¹ (glcoset a H) x = H x : {mul_inv_cancel_left a⁻¹ x})
lemma glcoset_inv a (H : set A) : a⁻¹ ∘> a ∘> H = H :=
      calc a⁻¹ ∘> a ∘> H = (a⁻¹*a) ∘> H : glcoset_compose
      ... = 1 ∘> H : mul.left_inv
      ... = H : glcoset_id
lemma grcoset_inv H (a : A) : (H <∘ a) <∘ a⁻¹ = H :=
      funext (assume x,
        calc grcoset (grcoset H a) a⁻¹ x = H x : {inv_mul_cancel_right x a⁻¹})
lemma glcoset_cancel a b (H : set A) : (b*a⁻¹) ∘> a ∘> H = b ∘> H :=
      calc (b*a⁻¹) ∘> a ∘> H = b*a⁻¹*a ∘> H : glcoset_compose
      ... = b ∘> H : {inv_mul_cancel_right b a}
lemma grcoset_cancel a b (H : set A) : H <∘ a <∘ a⁻¹*b = H <∘ b :=
      calc H <∘ a <∘ a⁻¹*b = H <∘ a*(a⁻¹*b) : grcoset_compose
      ... = H <∘ b : {mul_inv_cancel_left a b}
-- test how precedence breaks tie: infixr takes hold since its encountered first
example a b (H : set A) : a ∘> H <∘ b = a ∘> (H <∘ b) := rfl
-- should be true for semigroup as well but irrelevant
lemma lcoset_rcoset_assoc a b (H : set A) : a ∘> H <∘ b = (a ∘> H) <∘ b :=
  funext (assume x, begin
  esimp [glcoset, grcoset], rewrite mul.assoc
  end)
definition mul_closed_on H := ∀ x y, (x ∈ H ∧ y ∈ H) → x * y ∈ H
lemma closed_lcontract a (H : set A) : mul_closed_on H → a ∈ H → a ∘> H ⊆ H :=
      begin
      rewrite [↑mul_closed_on, ↑glcoset, ↑subset, ↑mem],
      intro Pclosed, intro PHa, intro x, intro PHainvx,
      exact (eq.subst (mul_inv_cancel_left a x)
                      (Pclosed a (a⁻¹*x) (and.intro PHa PHainvx)))
      end
lemma closed_rcontract a (H : set A) : mul_closed_on H → a ∈ H → H <∘ a ⊆ H :=
      assume P1 : mul_closed_on H,
      assume P2 : H a,
      begin
        rewrite ↑subset,
        intro x,
        rewrite [↑grcoset, ↑mem],
        intro P3,
        exact (eq.subst (inv_mul_cancel_right x a) (P1 (x * a⁻¹) a (and.intro P3 P2)))
      end
lemma closed_lcontract_set a (H G : set A) : mul_closed_on G → H ⊆ G → a∈G → a∘>H ⊆ G :=
      assume Pclosed, assume PHsubG, assume PainG,
      assert PaGsubG : a ∘> G ⊆ G, from closed_lcontract a G Pclosed PainG,
      assert PaHsubaG : a ∘> H ⊆ a ∘> G, from
        eq.symm (glcoset_eq_lcoset a H) ▸ eq.symm (glcoset_eq_lcoset a G) ▸ (coset.l_sub a H G PHsubG),
      subset.trans _ _ _ PaHsubaG PaGsubG
definition subgroup.has_inv H := ∀ a, a ∈ H → a⁻¹ ∈ H
-- two ways to define the same equivalence relatiohship for subgroups
definition in_lcoset H a b := a ∈ b ∘> H
definition in_rcoset H a b := a ∈ H <∘ b
definition same_lcoset H a b := a ∘> H = b ∘> H
definition same_rcoset H a b := H <∘ a = H <∘ b
definition same_left_right_coset (N : set A) := ∀ x, x ∘> N = N <∘ x
structure is_subgroup [class] (H : set A) : Type :=
  (has_one : H 1)
  (mul_closed : mul_closed_on H)
  (has_inv : subgroup.has_inv H)
structure is_normal_subgroup [class] (N : set A) extends is_subgroup N :=
  (normal : same_left_right_coset N)
end

section subgroup
variable {A : Type}
variable [s : group A]
include s
variable {H : set A}
variable [is_subg : is_subgroup H]
include is_subg

lemma subg_has_one : H 1 := !is_subgroup.has_one
lemma subg_mul_closed : mul_closed_on H := @is_subgroup.mul_closed A s H is_subg
lemma subg_has_inv : subgroup.has_inv H := @is_subgroup.has_inv A s H is_subg
lemma subgroup_coset_id : ∀ a, a ∈ H → (a ∘> H = H ∧ H <∘ a = H) :=
      take a, assume PHa : H a,
      assert Pl : a ∘> H ⊆ H, from closed_lcontract a H subg_mul_closed PHa,
      assert Pr : H <∘ a ⊆ H, from closed_rcontract a H subg_mul_closed PHa,
      assert PHainv : H a⁻¹, from subg_has_inv a PHa,
      and.intro
      (setext (assume x,
        begin
          esimp [glcoset, mem],
          apply iff.intro,
            apply Pl,
            intro PHx, exact (subg_mul_closed a⁻¹ x (and.intro PHainv PHx))
        end))
      (setext (assume x,
        begin
          esimp [grcoset, mem],
          apply iff.intro,
            apply Pr,
            intro PHx, exact (subg_mul_closed x a⁻¹ (and.intro PHx PHainv))
        end))
lemma subgroup_lcoset_id : ∀ a, a ∈ H → a ∘> H = H :=
      take a, assume PHa : H a,
      and.left (subgroup_coset_id a PHa)
lemma subgroup_rcoset_id : ∀ a, a ∈ H → H <∘ a = H :=
      take a, assume PHa : H a,
      and.right (subgroup_coset_id a PHa)
lemma subg_in_coset_refl (a : A) : a ∈ a ∘> H ∧ a ∈ H <∘ a :=
      assert PH1 : H 1, from subg_has_one,
      assert PHinvaa : H (a⁻¹*a), from (eq.symm (mul.left_inv a)) ▸ PH1,
      assert PHainva : H (a*a⁻¹), from (eq.symm (mul.right_inv a)) ▸ PH1,
      and.intro PHinvaa PHainva
lemma subg_lcoset_same (a b : A) : in_lcoset H a b = (a∘>H = b∘>H) :=
      propext(iff.intro 
      (assume Pa_in_b : H (b⁻¹*a),
      have Pbinva : b⁻¹*a ∘> H = H, from subgroup_lcoset_id (b⁻¹*a) Pa_in_b,
      have Pb_binva : b ∘> b⁻¹*a ∘> H = b ∘> H, from Pbinva ▸ rfl,
      have Pbbinva : b*(b⁻¹*a)∘>H = b∘>H, from glcoset_compose b (b⁻¹*a) H ▸ Pb_binva,
      mul_inv_cancel_left b a ▸ Pbbinva)
      (assume Psame : a∘>H = b∘>H,
      assert Pa : a ∈ a∘>H, from and.left (subg_in_coset_refl a),
      by exact (Psame ▸ Pa)))
lemma subg_rcoset_same (a b : A) : in_rcoset H a b = (H<∘a = H<∘b) :=
      propext(iff.intro 
      (assume Pa_in_b : H (a*b⁻¹),
      have Pabinv : H<∘a*b⁻¹ = H, from subgroup_rcoset_id (a*b⁻¹) Pa_in_b,
      have Pabinv_b : H <∘ a*b⁻¹ <∘ b = H <∘ b, from Pabinv ▸ rfl,
      have Pabinvb : H <∘ a*b⁻¹*b = H <∘ b, from grcoset_compose (a*b⁻¹) b H ▸ Pabinv_b,
      inv_mul_cancel_right a b ▸ Pabinvb)
      (assume Psame,
      assert Pa : a ∈ H<∘a, from and.right (subg_in_coset_refl a),
      by exact (Psame ▸ Pa)))
lemma subg_same_lcoset.refl (a : A) : same_lcoset H a a := rfl
lemma subg_same_rcoset.refl (a : A) : same_rcoset H a a := rfl
lemma subg_same_lcoset.symm (a b : A) : same_lcoset H a b → same_lcoset H b a := eq.symm
lemma subg_same_rcoset.symm (a b : A) : same_rcoset H a b → same_rcoset H b a := eq.symm
lemma subg_same_lcoset.trans (a b c : A) : same_lcoset H a b → same_lcoset H b c → same_lcoset H a c :=
      by rewrite [*subg_lcoset_same]; exact eq.trans
lemma subg_same_rcoset.trans (a b c : A) : same_rcoset H a b → same_rcoset H b c → same_rcoset H a c :=
      by rewrite [*subg_rcoset_same]; exact eq.trans
end subgroup

section normal_subg
open quot
variable {A : Type}
variable [s : group A]
include s
variable {N : set A}
variable [is_nsubg : is_normal_subgroup N]
include is_nsubg
lemma nsubg_normal : same_left_right_coset N := @is_normal_subgroup.normal A s N is_nsubg
lemma nsubg_same_lcoset_product : ∀ a1 a2 b1 b2, same_lcoset N a1 b1 → same_lcoset N a2 b2 → same_lcoset N (a1*a2) (b1*b2) :=
  take a1, take a2, take b1, take b2,
  assume Psame1 : a1 ∘> N = b1 ∘> N,
  assume Psame2 : a2 ∘> N = b2 ∘> N, calc
  a1*a2 ∘> N = a1 ∘> a2 ∘> N : glcoset_compose
  ... = a1 ∘> b2 ∘> N : {Psame2}
  ... = a1 ∘> (N <∘ b2) : {nsubg_normal b2}
  ... = (a1 ∘> N) <∘ b2 : lcoset_rcoset_assoc
  ... = (b1 ∘> N) <∘ b2 : {Psame1}
  ... = N <∘ b1 <∘ b2 : {nsubg_normal b1}
  ... = N <∘ (b1*b2) : grcoset_compose
  ... = (b1*b2) ∘> N : nsubg_normal

example (a b : A) : same_lcoset N a⁻¹ b⁻¹ = (a⁻¹ ∘> N = b⁻¹ ∘> N) := rfl
lemma nsubg_same_lcoset_inv : ∀ a b, same_lcoset N a b → same_lcoset N a⁻¹ b⁻¹ :=
  take a b, assume Psame, calc
  a⁻¹ ∘> N = a⁻¹*b*b⁻¹ ∘> N    : by rewrite mul_inv_cancel_right
  ... = a⁻¹*b ∘> b⁻¹ ∘> N      : by rewrite glcoset_compose
  ... = a⁻¹*b ∘> (N <∘ b⁻¹)    : by rewrite nsubg_normal
  ... = (a⁻¹*b ∘> N) <∘ b⁻¹    : by rewrite lcoset_rcoset_assoc
  ... = (a⁻¹ ∘> b ∘> N) <∘ b⁻¹ : by rewrite glcoset_compose
  ... = (a⁻¹ ∘> a ∘> N) <∘ b⁻¹ : by rewrite Psame
  ... = N <∘ b⁻¹               : by rewrite glcoset_inv
  ... = b⁻¹ ∘> N               : by rewrite nsubg_normal
definition nsubg_setoid [instance] : setoid A :=
  setoid.mk (same_lcoset N)
  (mk_equivalence (same_lcoset N) (subg_same_lcoset.refl) (subg_same_lcoset.symm) (subg_same_lcoset.trans))
definition coset_type : Type := quot nsubg_setoid
definition coset_inv_base (a : A) : coset_type := ⟦a⁻¹⟧
definition coset_product (a b : A) : coset_type := ⟦a*b⟧
lemma coset_product_well_defined : ∀ a1 a2 b1 b2, same_lcoset N a1 b1 → same_lcoset N a2 b2 → ⟦a1*a2⟧ = ⟦b1*b2⟧ :=
      take a1 a2 b1 b2, assume P1 P2,
      quot.sound (nsubg_same_lcoset_product a1 a2 b1 b2 P1 P2)
definition coset_mul (aN bN : coset_type) : coset_type :=
  quot.lift_on₂ aN bN coset_product coset_product_well_defined
lemma coset_inv_well_defined : ∀ a b, same_lcoset N a b → ⟦a⁻¹⟧ = ⟦b⁻¹⟧ :=
      take a b, assume P, quot.sound (nsubg_same_lcoset_inv a b P)
definition coset_inv (aN : coset_type) : coset_type :=
           quot.lift_on aN coset_inv_base coset_inv_well_defined
definition coset_one :  coset_type := ⟦1⟧

local infixl `cx`:70 := coset_mul
example (a b c : A) : ⟦a⟧ cx ⟦b*c⟧ = ⟦a*(b*c)⟧ := rfl

lemma coset_product_assoc (a b c : A) : ⟦a⟧ cx ⟦b⟧ cx ⟦c⟧ = ⟦a⟧ cx (⟦b⟧ cx ⟦c⟧) := calc
      ⟦a*b*c⟧ = ⟦a*(b*c)⟧ : {mul.assoc a b c}
      ... = ⟦a⟧ cx ⟦b*c⟧ : rfl
lemma coset_product_left_id (a : A) : ⟦1⟧ cx ⟦a⟧ = ⟦a⟧ := calc
      ⟦1*a⟧ = ⟦a⟧ : {one_mul a}
lemma coset_product_right_id (a : A) : ⟦a⟧ cx ⟦1⟧ = ⟦a⟧ := calc
      ⟦a*1⟧ = ⟦a⟧ : {mul_one a}
lemma coset_product_left_inv (a : A) : ⟦a⁻¹⟧ cx ⟦a⟧ = ⟦1⟧ := calc
      ⟦a⁻¹*a⟧ = ⟦1⟧ : {mul.left_inv a}
lemma coset_mul.assoc (aN bN cN : coset_type) : aN cx bN cx cN = aN cx (bN cx cN) :=
      quot.ind (λ a, quot.ind (λ b, quot.ind (λ c, coset_product_assoc a b c) cN) bN) aN
lemma coset_mul.one_mul (aN : coset_type) : coset_one cx aN = aN :=
      quot.ind coset_product_left_id aN
lemma coset_mul.mul_one (aN : coset_type) : aN cx coset_one = aN :=
      quot.ind coset_product_right_id aN
lemma coset_mul.left_inv (aN : coset_type) : (coset_inv aN) cx aN = coset_one :=
      quot.ind coset_product_left_inv aN
definition quotient_group : group coset_type :=
           group.mk coset_mul coset_mul.assoc coset_one  coset_mul.one_mul coset_mul.mul_one coset_inv coset_mul.left_inv

end normal_subg
namespace group
namespace quotient
section
variable {A : Type}
variable [s : group A]
include s
variable {N : set A}
variable [is_nsubg : is_normal_subgroup N]
include is_nsubg
end
end quotient
end group

end algebra


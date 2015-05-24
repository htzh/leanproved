/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
-- These belong in the library somewhere.
import algebra.group data

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

theorem id_is_inj : injective (@id A) := take a1 a2,
        by rewrite ↑id; intro H; exact H
theorem id_is_surj : surjective (@id A) := take a, exists.intro a rfl
theorem id_is_bij : bijective (@id A) := and.intro id_is_inj id_is_surj
lemma left_id (f : A → B) : id ∘ f = f := rfl
lemma right_id (f : A → B) : f ∘ id = f := rfl

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

namespace finset
section image
open function
variables {A B : Type}
variables [deceqA : decidable_eq A] [deceqB : decidable_eq B]
include deceqA
include deceqB

lemma Union_insert (f : A → finset B) {a : A} {s : finset A} : Union (insert a s) f = f a ∪ Union s f :=
      match decidable_mem a s with
      | decidable.inl Pin :=
        begin
        rewrite [Union_insert_of_mem f Pin],
        apply ext,
        intro x,
        apply iff.intro,
          exact mem_union_r,
          rewrite [mem_union_eq],
          intro Por,
          exact or.elim Por
            (assume Pl, begin
              rewrite mem_Union_eq, exact (exists.intro a (and.intro Pin Pl)) end)
            (assume Pr, Pr)
        end
      | decidable.inr Pnin := Union_insert_of_not_mem f Pnin
      end
lemma image_eq_Union_index_image (s : finset A) (f : A → finset B) : Union s f = Union (image f s) id :=
      finset.induction_on s
      (begin rewrite Union_empty end)
      (take s1 a Pa IH, by rewrite [image_insert, *Union_insert, IH])

end image

section eqv
open function
open eq.ops

variable {A : Type}
variable [deceqA : decidable_eq A]
include deceqA

definition is_eqv_class (f : A → finset A) := ∀ a b, a ∈ f b = (f a = f b)
definition is_restricted_cover (s : finset A) (f : A → finset A) := s = Union s f
structure partition : Type :=
(set : finset A) (part : A → finset A) (eqv : is_eqv_class part)
      (complete : set = Union set part)
definition eqv_classes (f : partition) : finset (finset A) := image (partition.part f) (partition.set f)

lemma eqv_class_disjoint (f : partition) (a1 a2 : finset A) (Pa1 : a1 ∈ eqv_classes f) (Pa2 : a2 ∈ eqv_classes f) : a1 ≠ a2 → a1 ∩ a2 = ∅ :=
      assume Pne,
      assert Pe1 : _, from exists_of_mem_image Pa1, obtain g1 Pg1, from Pe1,
      assert Pe2 : _, from exists_of_mem_image Pa2, obtain g2 Pg2, from Pe2,
      begin
      apply inter_eq_empty_of_disjoint,
      apply disjoint.intro,
      rewrite [eq.symm (and.right Pg1), eq.symm (and.right Pg2)],
      intro x,
      rewrite [*(partition.eqv f)],
      intro Pxg1, rewrite [Pxg1, and.right Pg1, and.right Pg2],
      intro Pe, exact absurd Pe Pne      
      end
lemma class_equation (f : @partition A _) : card (partition.set f) = nat.Sum (eqv_classes f) card :=
      let s := (partition.set f), p := (partition.part f), img := image p s in calc
      card s = card (Union s p) : partition.complete f
      ... = card (Union img id) : image_eq_Union_index_image s p
      ... = card (Union (eqv_classes f) id) : rfl
      ... = nat.Sum (eqv_classes f) card : card_Union_of_disjoint _ id (eqv_class_disjoint f)

lemma eqv_class_refl {f : A → finset A} (Peqv : is_eqv_class f) : ∀ a, a ∈ f a :=
      take a, by rewrite [Peqv a a]
-- make it a little easier to prove union from restriction
lemma restriction_imp_union {s : finset A} (f : A → finset A) (Peqv : is_eqv_class f) : (∀ a, a ∈ s → f a ⊆ s) → s = Union s f :=
      assume Psub, ext (take a, iff.intro
      (assume Pains, begin
        rewrite [(Union_insert_of_mem f Pains)⁻¹, Union_insert],
        apply mem_union_l, exact eqv_class_refl Peqv a end)
      (assume Painu,
        have Pclass : ∃ x, x ∈ s ∧ a ∈ f x,
          from iff.elim_left (mem_Union_iff s f _) Painu,
        obtain x Px, from Pclass,
        have Pfx : f x ⊆ s, from Psub x (and.left Px),
        mem_of_subset_of_mem Pfx (and.right Px)))

local attribute partition.part [coercion]

end eqv
end finset

namespace list

variables {A B : Type}
lemma not_mem_cons_of_ne_and_not_mem {x y : A} {l : list A} : x ≠ y ∧ x ∉ l → x ∉ y::l :=
      assume P, not.intro (assume Pxin,
        absurd (eq_or_mem_of_mem_cons Pxin) (not_or (and.left P) (and.right P)))
lemma ne_and_not_mem_of_not_mem_cons {x y : A} {l : list A} : x ∉ y::l → x ≠ y ∧ x ∉ l :=
      assume P, and.intro (not_eq_of_not_mem P) (not_mem_of_not_mem P)

definition dinj (p : A → Prop) (f : Π a, p a → B) := ∀ ⦃a1 a2⦄ (h1 : p a1) (h2 : p a2), a1 ≠ a2 → (f a1 h1) ≠ (f a2 h2)

definition dmap (p : A → Prop) [h : decidable_pred p] (f : Π a, p a → B) : list A → list B
| []       := []
| (a::l)   := if P : (p a) then cons (f a P) (dmap l) else (dmap l)

lemma dmap_nil {p : A → Prop} [h : decidable_pred p] {f : Π a, p a → B} : dmap p f [] = [] := rfl
lemma dmap_cons_of_pos {p : A → Prop} [h : decidable_pred p] {f : Π a, p a → B} {a : A} (P : p a) : ∀ l, dmap p f (a::l) = (f a P) :: dmap p f l :=
      λ l, dif_pos P
lemma dmap_cons_of_neg {p : A → Prop} [h : decidable_pred p] {f : Π a, p a → B} {a : A} (P : ¬ p a) : ∀ l, dmap p f (a::l) = dmap p f l :=
      λ l, dif_neg P

lemma mem_of_dmap {p : A → Prop} [h : decidable_pred p] {f : Π a, p a → B} : ∀ (l : list A) {a} (Pa : p a), a ∈ l → (f a Pa) ∈ dmap p f l
| []              := take a Pa Pinnil, by contradiction
| (a::l)          := take b Pb Pbin, or.elim (eq_or_mem_of_mem_cons Pbin)
                     (assume Pbeqa, begin
                       rewrite [eq.symm Pbeqa, dmap_cons_of_pos Pb],
                       exact !mem_cons
                     end)
                     (assume Pbinl,
                       decidable.rec_on (h a)
                       (assume Pa, begin
                         rewrite [dmap_cons_of_pos Pa],
                         apply mem_cons_of_mem,
                         exact mem_of_dmap l Pb Pbinl
                       end)
                       (assume nPa, begin
                         rewrite [dmap_cons_of_neg nPa],
                         exact mem_of_dmap l Pb Pbinl
                       end))
      
lemma dinj_not_mem_of_dmap {p : A → Prop} [h : decidable_pred p] (f : Π a, p a → B) (Pdi : dinj p f) : ∀ {l : list A} {a} (Pa : p a), a ∉ l → (f a Pa) ∉ dmap p f l
| []           := take b Pb Pbnin, !not_mem_nil
| (a::l)       := take b Pb Pbnin,
                  assert Pand : b ≠ a ∧ b ∉ l, from ne_and_not_mem_of_not_mem_cons Pbnin,
                  decidable.rec_on (h a)
                  (λ Pa, begin
                    rewrite [dmap_cons_of_pos Pa],
                    apply not_mem_cons_of_ne_and_not_mem,
                    apply and.intro,
                      exact Pdi Pb Pa (and.left Pand),
                      exact dinj_not_mem_of_dmap Pb (and.right Pand)
                  end) 
                  (λ nPa, begin
                     rewrite [dmap_cons_of_neg nPa],
                     exact dinj_not_mem_of_dmap Pb (and.right Pand)
                  end)

lemma dmap_nodup_of_dinj {p : A → Prop} [h : decidable_pred p] {f : Π a, p a → B} (Pdi : dinj p f): ∀ {l : list A}, nodup l → nodup (dmap p f l)
| []                 := take P, nodup.ndnil
| (a::l)             := take Pnodup,
                        decidable.rec_on (h a)
                        (λ Pa, begin
                          rewrite [dmap_cons_of_pos Pa],
                          apply nodup_cons,
                            apply (dinj_not_mem_of_dmap f Pdi Pa),
                            exact not_mem_of_nodup_cons Pnodup,
                            exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
                        end)
                        (λ nPa, begin
                          rewrite [dmap_cons_of_neg nPa],
                          exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
                        end)
end list

namespace list
section nodup
open function
variables {A B : Type}
--lemma inj_map_nodup (f : A → B) (inj : injective f) : ∀ (l : list A), nodup l → nodup (map f l) := sorry
  
end nodup
end list

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

namespace nat
-- not sure why these are missing
lemma not_lt_of_le {a b : nat} : a ≤ b → ¬ b < a :=
      assume aleb, not.intro (assume blta, lt.irrefl a (lt_of_le_of_lt aleb blta))

end nat

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

-- classical definition of bijective, not requiring an inv
definition bijective (f : A → B) := injective f ∧ surjective f

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

-- more development of theory of finset
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

-- theory of equivalent classes developed especially for counting purposes
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

-- useful for inverting function on a finite domain
section kth
open nat
variable {A : Type}

definition kth : ∀ k (l : list A), k < length l → A
| k []        := begin rewrite length_nil, intro Pltz, exact absurd Pltz !not_lt_zero end
| 0 (a::l)    := λ P, a
| (k+1) (a::l):= by rewrite length_cons; intro Plt; exact kth k l (lt_of_succ_lt_succ Plt)

lemma kth_zero_of_cons {a} (l : list A) (P : 0 < length (a::l)) : kth 0 (a::l) P = a :=
      rfl
lemma kth_succ_of_cons {a} k (l : list A) (P : k+1 < length (a::l)) : kth (succ k) (a::l) P = kth k l (lt_of_succ_lt_succ P) :=
      rfl
  
variable [deceqA : decidable_eq A]
include deceqA

-- find_mem can be used to generate a proof of Found if a ∈ l.
-- "kth (find a l) l Found" can be used to retrieve what is found. While that may seem
-- silly since we already have what we are looking for in "a",
-- "let elts := elems A, k := find b (map f elts) in kth k elts Found"
-- would allow us to use it as a map to reverse a finite function.
lemma find_le_length : ∀ {a} {l : list A}, find a l ≤ length l
| a []        := !le.refl
| a (b::l)    := decidable.rec_on (deceqA a b)
              (assume Peq, by rewrite [find_cons_of_eq l Peq]; exact !zero_lt_succ)
              (assume Pne, begin
              rewrite [find_cons_of_ne l Pne, length_cons],
              apply succ_lt_succ, apply find_le_length
              end)
lemma find_not_mem : ∀ {a} {l : list A}, find a l = length l → a ∉ l
| a []        := assume Peq, !not_mem_nil
| a (b::l)    := decidable.rec_on (deceqA a b)
              (assume Peq, by rewrite [find_cons_of_eq l Peq, length_cons]; contradiction)
              (assume Pne, begin
              rewrite [find_cons_of_ne l Pne, length_cons, mem_cons_iff],
              intro Plen, apply (not_or Pne),
              exact find_not_mem (succ_inj Plen)
              end)
lemma find_mem {a} {l : list A} : a ∈ l → find a l < length l :=
      assume Pin, begin
      apply lt_of_le_and_ne,
        apply find_le_length,
        apply not.intro, intro Peq,
        exact absurd Pin (find_not_mem Peq)
      end
end kth

variables {A B : Type}
-- missing in list/basic
lemma not_mem_cons_of_ne_and_not_mem {x y : A} {l : list A} : x ≠ y ∧ x ∉ l → x ∉ y::l :=
      assume P, not.intro (assume Pxin,
        absurd (eq_or_mem_of_mem_cons Pxin) (not_or (and.left P) (and.right P)))
lemma ne_and_not_mem_of_not_mem_cons {x y : A} {l : list A} : x ∉ y::l → x ≠ y ∧ x ∉ l :=
      assume P, and.intro (not_eq_of_not_mem P) (not_mem_of_not_mem P)

-- missing in list/comb
/-lemma for_all_of_all {p : A → Prop} : ∀ {l}, all l p → (∀a, a ∈ l → p a)
| []     H := take a Painnil, by contradiction
| (a::l) H := begin rewrite all_cons_eq at H, end-/

-- new for list/comb dependent map theory
definition dinj (p : A → Prop) (f : Π a, p a → B) := ∀ ⦃a1 a2⦄ (h1 : p a1) (h2 : p a2), a1 ≠ a2 → (f a1 h1) ≠ (f a2 h2)

definition dmap (p : A → Prop) [h : decidable_pred p] (f : Π a, p a → B) : list A → list B
| []       := []
| (a::l)   := if P : (p a) then cons (f a P) (dmap l) else (dmap l)

-- properties of dmap
section dmap

variable {p : A → Prop}
variable [h : decidable_pred p]
include h
variable {f : Π a, p a → B}

lemma dmap_nil : dmap p f [] = [] := rfl
lemma dmap_cons_of_pos {a : A} (P : p a) : ∀ l, dmap p f (a::l) = (f a P) :: dmap p f l :=
      λ l, dif_pos P
lemma dmap_cons_of_neg {a : A} (P : ¬ p a) : ∀ l, dmap p f (a::l) = dmap p f l :=
      λ l, dif_neg P

lemma mem_of_dmap : ∀ {l : list A} {a} (Pa : p a), a ∈ l → (f a Pa) ∈ dmap p f l
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
                         exact mem_of_dmap Pb Pbinl
                       end)
                       (assume nPa, begin
                         rewrite [dmap_cons_of_neg nPa],
                         exact mem_of_dmap Pb Pbinl
                       end))

lemma map_of_dmap_inv_pos {g : B → A} (Pinv : ∀ a (Pa : p a), g (f a Pa) = a) :
                          ∀ {l : list A}, (∀ ⦃a⦄, a ∈ l → p a) → map g (dmap p f l) = l
| []                      := assume Pl, by rewrite [dmap_nil, map_nil]
| (a::l)                  := assume Pal,
                          assert Pa : p a, from Pal a !mem_cons,
                          assert Pl : ∀ a, a ∈ l → p a,
                            from take x Pxin, Pal x (mem_cons_of_mem a Pxin),
                          by rewrite [dmap_cons_of_pos Pa, map_cons, Pinv, map_of_dmap_inv_pos Pl]

lemma dinj_not_mem_of_dmap (Pdi : dinj p f) : ∀ {l : list A} {a} (Pa : p a), a ∉ l → (f a Pa) ∉ dmap p f l
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

lemma dmap_nodup_of_dinj (Pdi : dinj p f): ∀ {l : list A}, nodup l → nodup (dmap p f l)
| []                 := take P, nodup.ndnil
| (a::l)             := take Pnodup,
                        decidable.rec_on (h a)
                        (λ Pa, begin
                          rewrite [dmap_cons_of_pos Pa],
                          apply nodup_cons,
                            apply (dinj_not_mem_of_dmap Pdi Pa),
                            exact not_mem_of_nodup_cons Pnodup,
                            exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
                        end)
                        (λ nPa, begin
                          rewrite [dmap_cons_of_neg nPa],
                          exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
                        end)
end dmap

end list

namespace list
section nodup
open function
variables {A B : Type}
--lemma inj_map_nodup (f : A → B) (inj : injective f) : ∀ (l : list A), nodup l → nodup (map f l) := sorry
  
end nodup
end list

namespace finset
open eq.ops nat

-- general version of pigeon hole for finsets. we can specialize it to fintype univ.
-- note the classical property of inj is split between inj_on and maps_to, which we
-- replace with image subset instead
lemma card_le_of_inj {A : Type} [deceqA : decidable_eq A]
                     {B : Type} [deceqB : decidable_eq B]
                     (a : finset A) (b : finset B)
                   : (∃ f : A → B, set.inj_on f (ts a) ∧ (image f a ⊆ b)) → card a ≤ card b :=
      assume Pex, obtain f Pinj, from Pex,
      assert Psub : _, from and.right Pinj,
      assert Ple : card (image f a) ≤ card b, from card_le_card_of_subset Psub,
      by rewrite [(card_image_eq_of_inj_on (and.left Pinj))⁻¹]; exact Ple

end finset

namespace fintype
open eq.ops nat function list finset

definition card [reducible] (A : Type) [finA : fintype A] := finset.card (@finset.univ A _)

-- general version of pigeon hole principle. we will specialize it to less_than type later
lemma card_le_of_inj (A : Type) [finA : fintype A] [deceqA : decidable_eq A]
                     (B : Type) [finB : fintype B] [deceqB : decidable_eq B]
                   : (∃ f : A → B, injective f) → card A ≤ card B :=
      assume Pex, obtain f Pinj, from Pex,
      assert Pinj_on_univ : _, from injective_eq_inj_on_univ ▸ Pinj,
      assert Pinj_ts : _, from to_set_univ⁻¹ ▸ Pinj_on_univ,
      assert Psub : (image f univ) ⊆ univ, from !subset_univ,
      finset.card_le_of_inj univ univ (exists.intro f (and.intro Pinj_ts Psub))

-- this theory is developed so it would be easier to establish permutations on finite
-- types. In general we could hypothesize a finset of card n but since all Sn groups are
-- isomorphic there is no reason not to use a concrete list of nats. Especially since
-- we now conflate the object with the index we may be able to make the construction of
-- the inverse simpler, but that remains to be seen.
structure less_than (n : nat) :=
          (val : nat) (lt : val < n)

definition less_than.has_decidable_eq [instance] (n : nat) : decidable_eq (less_than n) :=
           take i j,
           less_than.destruct i (λ ival iltn, less_than.destruct j (λ jval jltn,
             decidable.rec_on (nat.has_decidable_eq ival jval)
               (assume Pe, decidable.inl (dcongr_arg2 less_than.mk Pe !proof_irrel))
               (assume Pne, decidable.inr (not.intro
                 (assume Pmkeq, less_than.no_confusion Pmkeq
                   (assume Pe, absurd Pe Pne))))))

namespace less_than
open decidable
-- new tactic makes the proof above more succinct
example (n : nat) : ∀ (i j : less_than n), decidable (i = j)
| (mk ival ilt) (mk jval jlt) :=
      match nat.has_decidable_eq ival jval with
      | inl veq := inl (by substvars)
      | inr vne := inr (by intro h; injection h; contradiction)
      end
end less_than

lemma lt_dinj (n : nat) : dinj (λ i, i < n) less_than.mk :=
      take a1 a2 Pa1 Pa2 Pne, not.intro
        (assume Pelt, less_than.no_confusion Pelt
          (assume Pe, absurd Pe Pne))

lemma lt_inv (n i : nat) (Plt : i < n) : less_than.val (less_than.mk i Plt) = i := rfl

definition upto [reducible] (n : nat) : list (less_than n) :=
           dmap (λ i, i < n) less_than.mk (list.upto n)

lemma upto_nodup (n : nat) : nodup (upto n) :=
                    dmap_nodup_of_dinj (lt_dinj n) (list.nodup_upto n)

check @less_than.mk

lemma upto_complete (n : nat) : ∀ (i : less_than n), i ∈ upto n :=
      take i, less_than.destruct i (
        take ival Piltn,
          assert Pin : ival ∈ list.upto n, from mem_upto_of_lt Piltn,
          mem_of_dmap Piltn Pin)

lemma upto_nil : upto 0 = [] :=
      by rewrite [↑upto, list.upto_nil, dmap_nil]

lemma upto_map_eq_upto (n : nat) : map less_than.val (upto n) = list.upto n :=
      map_of_dmap_inv_pos (lt_inv n) (@lt_of_mem_upto n)

lemma upto_length (n : nat) : length (upto n) = n := calc
      length (upto n) = length (list.upto n) : (upto_map_eq_upto n ▸ len_map less_than.val (upto n))⁻¹
      ... = n : list.length_upto n

definition fin_lt_type [instance] (n : nat) : fintype (less_than n) :=
           fintype.mk (upto n) (upto_nodup n) (upto_complete n)

local attribute less_than.val [coercion]

-- alternative definitions of upto not needed for anything
definition lt_collect (n : nat) (l : list (less_than n)) (i : nat) :=
           if H : (i < n) then cons (less_than.mk i H) l else l

definition upto₁ (n : nat) : list (less_than n) :=
           foldl (lt_collect n) [] (list.upto n)

definition lt_cons (n : nat) (i : nat) (l : list (less_than n)) : list (less_than n) :=
           if H : (i < n) then cons (less_than.mk i H) l else l

definition upto₂ (n : nat) : list (less_than n) :=
           foldr (lt_cons n) [] (list.upto n)

section pigeon_hole

variable {n : nat}

lemma card_univ_lt_type : card (less_than n) = n := upto_length n

variable {m : nat}

theorem pigeon_hole : m < n → ¬ (∃ f : less_than n → less_than m, injective f) :=
        assume Pmltn, not.intro
          (assume Pex, absurd Pmltn (not_lt_of_le (calc
            n = card (less_than n) : card_univ_lt_type
            ... ≤ card (less_than m) : card_le_of_inj (less_than n) (less_than m) Pex
            ... = m : card_univ_lt_type)))

end pigeon_hole

end fintype

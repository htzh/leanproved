/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import data
open list eq.ops

namespace migration

section basic

open function

lemma head_eq_of_cons_eq {A : Type} {h₁ h₂ : A} {t₁ t₂ : list A} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
      assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

lemma tail_eq_of_cons_eq {A : Type} {h₁ h₂ : A} {t₁ t₂ : list A} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
      assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

lemma cons_inj {A : Type} {a : A} : injective (cons a) :=
      take l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

end basic

section unused
open nat

variable {A : Type}

-- insert at all possible locations
definition insert_all (a : A) : ∀ (l : list A), list (list A)
| []       := [[a]]
| (b::l)   := (a::b::l) :: map (cons b) (insert_all l)

definition concat_all (ls : list (list A)) : list A :=
           foldr append [] ls

definition perms_of_list : ∀ (l : list A), list (list A)
| []       := [[]]
| (a::l)   := concat_all (map (insert_all a) (perms_of_list l))

lemma insert_all_cons {a b : A} {l : list A} :
      (insert_all a (b::l)) = (a::b::l) :: map (cons b) (insert_all a l) := rfl

lemma nodup_concat_all_of_disjoint_of_all_nodup_of_nodup :
      ∀ {ls : list (list A)}, nodup ls → (∀ l, l ∈ ls → nodup l) → (∀ l₁ l₂, l₁ ∈ ls → l₂ ∈ ls → l₁ ≠ l₂ → disjoint l₁ l₂) → nodup (concat_all ls) := sorry

lemma nodup_insert_all {a : A} : ∀ {l : list A}, a ∉ l → nodup (insert_all a l)
| []       := assume P, !nodup_singleton
| (b::l)   := assume Pnin, obtain Paneb Paninl, from ne_and_not_mem_of_not_mem_cons Pnin,
           nodup_cons (not.intro (assume Pablin,
             obtain t Pt Peq, from exists_of_mem_map Pablin,
             absurd (head_eq_of_cons_eq Peq)⁻¹ Paneb))
           (nodup_map cons_inj (nodup_insert_all Paninl))

lemma all_not_mem_insert_all_of_not_mem_of_ne {a : A} :
      ∀ {l : list A} {b}, b ≠ a → b ∉ l → ∀ {l'}, l' ∈ insert_all a l → b ∉ l'
| []       := take b, assume Pne Pnin, take l', assume Pl' : l' ∈ [[a]], by
           rewrite [mem_singleton Pl']; intro P; apply absurd (mem_singleton P) Pne
| (c::l)   := take b, assume Pne Pnin, take l', begin
           rewrite [insert_all_cons, mem_cons_iff], intro Pl',
           cases Pl' with Pacl Pinmap,
             rewrite Pacl, exact not_mem_cons_of_ne_of_not_mem Pne Pnin,
             assert Pex : ∃ t, t ∈ insert_all a l ∧ c :: t = l',
               apply exists_of_mem_map Pinmap,
             cases Pex with t Pt,
             rewrite [-(and.right Pt)],
             apply not_mem_cons_of_ne_of_not_mem (ne_of_not_mem_cons Pnin),
             apply all_not_mem_insert_all_of_not_mem_of_ne Pne (not_mem_of_not_mem_cons Pnin) (and.left Pt)
           end

lemma all_nodup_insert_all {a} :
      ∀ {l : list A}, a ∉ l → nodup l → ∀ {l'}, l' ∈ (insert_all a l) → nodup l'
| []       := assume Pnin Pnodup, take l', assume Pl', by
           rewrite [mem_singleton Pl']; apply nodup_singleton
| (b::l)   := assume Pnin, obtain Paneb Paninl, from ne_and_not_mem_of_not_mem_cons Pnin,
           assume Pnodup, take l', assume Pl',
           or.elim (eq_or_mem_of_mem_cons Pl')
             (assume Peq, begin
             rewrite [Peq], apply nodup_cons,
               exact not_mem_cons_of_ne_of_not_mem Paneb Paninl,
               exact Pnodup
             end)
             (assume Pin : l' ∈ map (cons b) (insert_all a l),
             obtain t Pt Peq, from exists_of_mem_map Pin, begin
             rewrite [-Peq], apply nodup_cons,
             apply all_not_mem_insert_all_of_not_mem_of_ne (ne.symm Paneb),
               apply not_mem_of_nodup_cons Pnodup, apply Pt,
               apply all_nodup_insert_all Paninl (nodup_of_nodup_cons Pnodup) Pt
             end)

lemma nodup_perms_of_nodup : ∀ {l : list A}, nodup l → nodup (perms_of_list l)
| []       := assume P, !nodup_singleton
| (a::l)   := assume Pal, sorry

lemma length_insert_all {a : A} : ∀ {l : list A}, length (insert_all a l) = length l + 1
| []       := rfl
| (b::l)   := by rewrite [insert_all_cons, length_cons, length_map, length_insert_all]


end unused

end migration

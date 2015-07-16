/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

import data

open finset function eq.ops

namespace migration

section basic
variable {A : Type}

lemma eq_of_singleton_eq {a b : A} : singleton a = singleton b → a = b :=
assume Pseq, eq_of_mem_singleton (Pseq ▸ mem_singleton a)

end basic

section partition
variables {A B : Type} [deceqA : decidable_eq A] [deceqB : decidable_eq B]
include deceqA

lemma binary_union (P : A → Prop) [decP : decidable_pred P] {S : finset A} :
  S = {a ∈ S | P a} ∪ {a ∈ S | ¬(P a)} :=
ext take a, iff.intro
  (assume Pin, decidable.by_cases
    (λ Pa : P a, mem_union_l (mem_filter_of_mem Pin Pa))
    (λ nPa, mem_union_r (mem_filter_of_mem Pin nPa)))
  (assume Pinu, or.elim (mem_or_mem_of_mem_union Pinu)
    (assume Pin, mem_of_mem_filter Pin)
    (assume Pin, mem_of_mem_filter Pin))

lemma binary_inter_empty {P : A → Prop} [decP : decidable_pred P] {S : finset A} :
  {a ∈ S | P a} ∩ {a ∈ S | ¬(P a)} = ∅ :=
inter_eq_empty (take a, assume Pa nPa, absurd (of_mem_filter Pa) (of_mem_filter nPa))

definition disjoint_sets (S : finset (finset A)) : Prop :=
  ∀ s₁ s₂ (P₁ : s₁ ∈ S) (P₂ : s₂ ∈ S), s₁ ≠ s₂ → s₁ ∩ s₂ = ∅

lemma disjoint_sets_filter_of_disjoint_sets {P : finset A → Prop} [decP : decidable_pred P] {S : finset (finset A)} :
  disjoint_sets S → disjoint_sets {s ∈ S | P s} :=
assume Pds, take s₁ s₂, assume P₁ P₂, Pds s₁ s₂ (mem_of_mem_filter P₁) (mem_of_mem_filter P₂)

lemma binary_inter_empty_Union_disjoint_sets {P : finset A → Prop} [decP : decidable_pred P] {S : finset (finset A)} :
  disjoint_sets S → Union {s ∈ S | P s} id ∩ Union {s ∈ S | ¬P s} id = ∅ :=
assume Pds, inter_eq_empty (take a, assume Pa nPa,
  obtain s Psin Pains, from iff.elim_left !mem_Union_iff Pa,
  obtain t Ptin Paint, from iff.elim_left !mem_Union_iff nPa,
  assert Pneq : s ≠ t,
    from assume Peq, absurd (Peq ▸ of_mem_filter Psin) (of_mem_filter Ptin),
  Pds s t (mem_of_mem_filter Psin) (mem_of_mem_filter Ptin) Pneq ▸ mem_inter Pains Paint)

section
include deceqB

lemma binary_Union (f : A → finset B) {P : A → Prop} [decP : decidable_pred P] {s : finset A} :
  Union s f = Union {a ∈ s | P a} f ∪ Union {a ∈ s | ¬P a} f :=
begin rewrite [binary_union P at {1}], apply Union_union, exact binary_inter_empty end

end

open nat
lemma card_binary_Union_disjoint_sets (P : finset A → Prop) [decP : decidable_pred P] {S : finset (finset A)} :
  disjoint_sets S → Sum S card = Sum {s ∈ S | P s} card + Sum {s ∈ S | ¬P s} card :=
assume Pds, calc
  Sum S card = card (Union S id) : card_Union_of_disjoint S id Pds
         ... = card (Union {s ∈ S | P s} id ∪ Union {s ∈ S | ¬P s} id) : binary_Union
         ... = card (Union {s ∈ S | P s} id) + card (Union {s ∈ S | ¬P s} id) : card_union_of_disjoint (binary_inter_empty_Union_disjoint_sets Pds)
         ... = Sum {s ∈ S | P s} card + Sum {s ∈ S | ¬P s} card : by rewrite [*(card_Union_of_disjoint _ id (disjoint_sets_filter_of_disjoint_sets Pds))]

end partition

section unused
variable {A : Type}

lemma singleton_subset_of_mem {a : A} {S : finset A} : a ∈ S → singleton a ⊆ S :=
assume Pain, subset_of_forall take x,
  by rewrite [mem_singleton_eq]; intro P; rewrite P; assumption

end unused

end migration

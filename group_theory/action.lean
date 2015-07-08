/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .hom .perm .finsubg

namespace group
open finset algebra function

local attribute perm.f [coercion]

lemma and_left_true {a b : Prop} (Pa : a) : a ∧ b ↔ b :=
by rewrite [iff_true_intro Pa, true_and]

section def
variables {G S : Type} [ambientG : group G] [finS : fintype S] [deceqS : decidable_eq S]
include ambientG finS deceqS

definition orbit (hom : G → perm S) (H : finset G) (a : S) : finset S :=
           image (move_by a) (image hom H)

definition fixed_points [reducible] (hom : G → perm S) (H : finset G) : finset S :=
{a ∈ univ | orbit hom H a = singleton a}

definition is_fixed_point (hom : G → perm S) (H : finset G) (a : S) : Prop :=
∀ h, h ∈ H → hom h a = a

variable [deceqG : decidable_eq G]
include deceqG -- required by {x ∈ H |p x} filtering

definition moverset (hom : G → perm S) (H : finset G) (a b : S) : finset G :=
           {f ∈ H | hom f a = b}

definition stab (hom : G → perm S) (H : finset G) (a : S) : finset G :=
           {f ∈ H | hom f a = a}

end def

section orbit_stabilizer

variables {G S : Type}
variable [ambientG : group G]
include ambientG
variable [finS : fintype S]
include finS
variable [deceqS : decidable_eq S]
include deceqS

section

variables {hom : G → perm S} {H : finset G} {a : S} [Hom : is_hom_class hom]
include Hom

lemma exists_of_orbit {b : S} : b ∈ orbit hom H a → ∃ h, h ∈ H ∧ hom h a = b :=
      assume Pb,
      obtain p (Pp₁ : p ∈ image hom H) (Pp₂ : move_by a p = b), from exists_of_mem_image Pb,
      obtain h (Ph₁ : h ∈ H) (Ph₂ : hom h = p), from exists_of_mem_image Pp₁,
      assert Phab : hom h a = b, from calc
        hom h a = p a : Ph₂
            ... = b   : Pp₂,
      exists.intro h (and.intro Ph₁ Phab)

lemma orbit_of_exists {b : S} : (∃ h, h ∈ H ∧ hom h a = b) → b ∈ orbit hom H a :=
assume Pex, obtain h PinH Phab, from Pex,
mem_image_of_mem_of_eq (mem_image_of_mem hom PinH) Phab

lemma is_fixed_point_of_mem_fixed_points :
  a ∈ fixed_points hom H → is_fixed_point hom H a :=
assume Pain, take h, assume Phin,
  eq_of_mem_singleton
    (of_mem_filter Pain ▸ orbit_of_exists (exists.intro h (and.intro Phin rfl)))

lemma mem_fixed_points_of_is_fixed_point_of_exists :
  is_fixed_point hom H a → (∃ h, h ∈ H) → a ∈ fixed_points hom H :=
assume Pfp Pex, mem_filter_of_mem !mem_univ
  (ext take x, iff.intro
    (assume Porb, obtain h Phin Pha, from exists_of_orbit Porb,
      by rewrite [mem_singleton_eq, -Pha, Pfp h Phin])
    (obtain h Phin, from Pex,
      by rewrite mem_singleton_eq;
         intro Peq; rewrite Peq;
         apply orbit_of_exists;
         existsi h; apply and.intro Phin (Pfp h Phin)))

end

variable [deceqG : decidable_eq G]
include deceqG

-- these are already specified by stab hom H a
variables {hom : G → perm S} {H : finset G} {a : S}

variable [Hom : is_hom_class hom]
include Hom

lemma stab_lmul {f g : G} : g ∈ stab hom H a → hom (f*g) a = hom f a :=
      assume Pgstab,
      assert Pg : hom g a = a, from of_mem_filter Pgstab, calc
        hom (f*g) a = perm.f ((hom f) * (hom g)) a : is_hom hom
                ... = ((hom f) ∘ (hom g)) a        : rfl
                ... = (hom f) a                    : Pg

lemma stab_subset : stab hom H a ⊆ H :=
      begin
        apply subset_of_forall, intro f Pfstab, apply mem_of_mem_filter Pfstab
      end

lemma reverse_move {h g : G} : g ∈ moverset hom H a (hom h a) → hom (h⁻¹*g) a = a :=
      assume Pg,
      assert Pga : hom g a = hom h a, from of_mem_filter Pg, calc
      hom (h⁻¹*g) a = perm.f ((hom h⁻¹) * (hom g)) a : is_hom hom
      ... = ((hom h⁻¹) ∘ hom g) a        : rfl
      ... = ((hom h⁻¹) ∘ hom h) a        : {Pga}
      ... = perm.f ((hom h⁻¹) * hom h) a : rfl
      ... = perm.f ((hom h)⁻¹ * hom h) a : hom_map_inv hom h
      ... = (1 : perm S) a               : mul.left_inv (hom h)
      ... = a                            : rfl

lemma moverset_inj_on_orbit : set.inj_on (moverset hom H a) (ts (orbit hom H a)) :=
      take b1 b2,
      assume Pb1, obtain h1 Ph1₁ Ph1₂, from exists_of_orbit Pb1,
      assert Ph1b1 : h1 ∈ moverset hom H a b1,
        from mem_filter_of_mem Ph1₁ Ph1₂,
      assume Psetb2 Pmeq, begin
        subst b1,
        rewrite Pmeq at Ph1b1,
        apply of_mem_filter Ph1b1
      end

variable [subgH : is_finsubg H]
include subgH

lemma subg_stab_of_move {h g : G} :
      h ∈ H → g ∈ moverset hom H a (hom h a) → h⁻¹*g ∈ stab hom H a :=
      assume Ph Pg,
      assert Phinvg : h⁻¹*g ∈ H, from begin
        apply finsubg_mul_closed H,
          apply finsubg_has_inv H, assumption,
          apply mem_of_mem_filter Pg
        end,
      mem_filter_of_mem Phinvg (reverse_move Pg)

lemma subg_stab_closed : finset_mul_closed_on (stab hom H a) :=
      take f g, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assume Pgstab,
      assert Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = (hom f) a : stab_lmul Pgstab
        ... = a : Pf,
      assert PfginH : (f*g) ∈ H,
        from finsubg_mul_closed H (mem_of_mem_filter Pfstab) (mem_of_mem_filter Pgstab),
      mem_filter_of_mem PfginH Pfg

lemma subg_stab_has_one : 1 ∈ stab hom H a :=
      assert P : hom 1 a = a, from calc
        hom 1 a = (1 : perm S) a : {hom_map_one hom}
        ... = a : rfl,
      assert PoneinH : 1 ∈ H, from finsubg_has_one H,
      mem_filter_of_mem PoneinH P

lemma subg_stab_has_inv : finset_has_inv (stab hom H a) :=
      take f, assume Pfstab, assert Pf : hom f a = a, from of_mem_filter Pfstab,
      assert Pfinv : hom f⁻¹ a = a, from calc
        hom f⁻¹ a = hom f⁻¹ ((hom f) a) : Pf
        ... = perm.f ((hom f⁻¹) * (hom f)) a : rfl
        ... = hom (f⁻¹ * f) a                : is_hom hom
        ... = hom 1 a                        : mul.left_inv
        ... = (1 : perm S) a : hom_map_one hom,
      assert PfinvinH : f⁻¹ ∈ H, from finsubg_has_inv H (mem_of_mem_filter Pfstab),
      mem_filter_of_mem PfinvinH Pfinv

definition subg_stab_is_finsubg [instance] :
           is_finsubg (stab hom H a) :=
           is_finsubg.mk subg_stab_has_one subg_stab_closed subg_stab_has_inv

lemma subg_lcoset_eq_moverset {h : G} :
      h ∈ H → fin_lcoset (stab hom H a) h = moverset hom H a (hom h a) :=
      assume Ph, ext (take g, iff.intro
      (assume Pl, obtain f (Pf₁ : f ∈ stab hom H a) (Pf₂ : h*f = g), from exists_of_mem_image Pl,
       assert Pfstab : hom f a = a, from of_mem_filter Pf₁,
       assert PginH : g ∈ H, begin
        subst Pf₂,
        apply finsubg_mul_closed H,
          assumption,
          apply mem_of_mem_filter Pf₁
        end,
      assert Pga : hom g a = hom h a, from calc
        hom g a = hom (h*f) a : by subst g
        ... = hom h a         : stab_lmul Pf₁,
      mem_filter_of_mem PginH Pga)
      (assume Pr, begin
       rewrite [↑fin_lcoset, mem_image_iff],
       existsi h⁻¹*g,
       split,
         exact subg_stab_of_move Ph Pr,
         apply mul_inv_cancel_left
       end))

lemma subg_moverset_of_orbit_is_lcoset_of_stab (b : S) :
      b ∈ orbit hom H a → ∃ h, h ∈ H ∧ fin_lcoset (stab hom H a) h = moverset hom H a b :=
      assume Porb,
      obtain p (Pp₁ : p ∈ image hom H) (Pp₂ : move_by a p = b), from exists_of_mem_image Porb,
      obtain h (Ph₁ : h ∈ H) (Ph₂ : hom h = p), from exists_of_mem_image Pp₁,
      assert Phab : hom h a = b, from by subst p; assumption,
      exists.intro h (and.intro Ph₁ (Phab ▸ subg_lcoset_eq_moverset Ph₁))

lemma subg_lcoset_of_stab_is_moverset_of_orbit (h : G) :
      h ∈ H → ∃ b, b ∈ orbit hom H a ∧ moverset hom H a b = fin_lcoset (stab hom H a) h :=
      assume Ph,
      have Pha : (hom h a) ∈ orbit hom H a, by
        apply mem_image_of_mem; apply mem_image_of_mem; exact Ph,
      exists.intro (hom h a) (and.intro Pha (eq.symm (subg_lcoset_eq_moverset Ph)))

lemma subg_moversets_of_orbit_eq_stab_lcosets :
      image (moverset hom H a) (orbit hom H a) = fin_lcosets (stab hom H a) H :=
      ext (take s, iff.intro
      (assume Pl, obtain b Pb₁ Pb₂, from exists_of_mem_image Pl,
      obtain h Ph, from subg_moverset_of_orbit_is_lcoset_of_stab b Pb₁, begin
      rewrite [↑fin_lcosets, mem_image_eq],
      existsi h, subst Pb₂, assumption
      end)
      (assume Pr, obtain h Ph₁ Ph₂, from exists_of_mem_image Pr,
      obtain b Pb, from @subg_lcoset_of_stab_is_moverset_of_orbit G S ambientG finS deceqS deceqG hom H a Hom subgH h Ph₁, begin
      rewrite [mem_image_eq],
      existsi b, subst Ph₂, assumption
      end))

open nat

theorem orbit_stabilizer_theorem : card H = card (orbit hom H a) * card (stab hom H a) :=
        calc card H = card (fin_lcosets (stab hom H a) H) * card (stab hom H a) : lagrange_theorem stab_subset
        ... = card (image (moverset hom H a) (orbit hom H a)) * card (stab hom H a) : subg_moversets_of_orbit_eq_stab_lcosets
        ... = card (orbit hom H a) * card (stab hom H a) : card_image_eq_of_inj_on moverset_inj_on_orbit

end orbit_stabilizer

section partition
variables {A B : Type} [deceqA : decidable_eq A] [deceqB : decidable_eq B]
include deceqA

lemma eq_of_singleton_eq {a b : A} : singleton a = singleton b → a = b :=
assume Pseq, eq_of_mem_singleton (Pseq ▸ mem_singleton a)

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

section orbit_partition

variables {G S : Type} [ambientG : group G] [finS : fintype S]
variables [deceqS : decidable_eq S]
include ambientG finS deceqS
variables {hom : G → perm S} [Hom : is_hom_class hom] {H : finset G} [subgH : is_finsubg H]
include Hom subgH

lemma in_orbit_refl {a : S} : a ∈ orbit hom H a :=
mem_image_of_mem_of_eq (mem_image_of_mem_of_eq (finsubg_has_one H) (hom_map_one hom)) rfl

lemma in_orbit_trans {a b c : S} :
  a ∈ orbit hom H b → b ∈ orbit hom H c → a ∈ orbit hom H c :=
assume Painb Pbinc,
obtain h PhinH Phba, from exists_of_orbit Painb,
obtain g PginH Pgcb, from exists_of_orbit Pbinc,
orbit_of_exists (exists.intro (h*g) (and.intro
  (finsubg_mul_closed H PhinH PginH)
  (calc hom (h*g) c = perm.f ((hom h) * (hom g)) c : is_hom hom
                ... = ((hom h) ∘ (hom g)) c : rfl
                ... = (hom h) b : Pgcb
                ... = a : Phba)))

lemma in_orbit_symm {a b : S} : a ∈ orbit hom H b → b ∈ orbit hom H a :=
assume Painb, obtain h PhinH Phba, from exists_of_orbit Painb,
assert Phinvab : perm.f (hom h)⁻¹ a = b, from
  calc perm.f (hom h)⁻¹ a = perm.f (hom h)⁻¹ ((hom h) b) : Phba
                      ... = perm.f ((hom h)⁻¹ * (hom h)) b : rfl
                      ... = perm.f (1 : perm S) b : mul.left_inv,
orbit_of_exists (exists.intro h⁻¹ (and.intro
  (finsubg_has_inv H PhinH)
  (calc (hom h⁻¹) a = perm.f (hom h)⁻¹ a : hom_map_inv hom h
                ... = b : Phinvab)))

lemma orbit_is_partition : is_partition (orbit hom H) :=
take a b, propext (iff.intro
  (assume Painb, obtain h PhinH Phba, from exists_of_orbit Painb,
  ext take c, iff.intro
    (assume Pcina, in_orbit_trans Pcina Painb)
    (assume Pcinb, obtain g PginH Pgbc, from exists_of_orbit Pcinb,
      in_orbit_trans Pcinb (in_orbit_symm Painb)))
  (assume Peq, Peq ▸ in_orbit_refl))

variables (hom) (H)
open nat finset.partition fintype

definition orbit_partition : @partition S _ :=
mk univ (orbit hom H) orbit_is_partition
  (restriction_imp_union (orbit hom H) orbit_is_partition (λ a Pa, !subset_univ))

definition orbits : finset (finset S) := equiv_classes (orbit_partition hom H)

definition fixed_point_orbits : finset (finset S) :=
  {cls ∈ orbits hom H | card cls = 1}

variables {hom} {H}

lemma exists_iff_mem_orbits (orb : finset S) :
  orb ∈ orbits hom H ↔ ∃ a : S, orbit hom H a = orb :=
begin
  esimp [orbits, equiv_classes, orbit_partition],
  rewrite [mem_image_iff],
  apply iff.intro,
    intro Pl,
    cases Pl with a Pa,
    rewrite (and_left_true !mem_univ) at Pa,
    existsi a, exact Pa,
    intro Pr,
    cases Pr with a Pa,
    rewrite -true_and at Pa, rewrite -(iff_true_intro (mem_univ a)) at Pa,
    existsi a, exact Pa
end

lemma exists_of_mem_orbits {orb : finset S} :
  orb ∈ orbits hom H → ∃ a : S, orbit hom H a = orb :=
iff.elim_left (exists_iff_mem_orbits orb)

lemma fixed_point_orbits_eq : fixed_point_orbits hom H = image (orbit hom H) (fixed_points hom H) :=
ext take s, iff.intro
  (assume Pin,
   obtain Psin Ps, from iff.elim_left !mem_filter_iff Pin,
   obtain a Pa, from exists_of_mem_orbits Psin,
   mem_image_of_mem_of_eq
     (mem_filter_of_mem !mem_univ (eq.symm
       (eq_of_card_eq_of_subset (by rewrite [card_singleton, Pa, Ps])
         (subset_of_forall
           take x, assume Pxin, eq_of_mem_singleton Pxin ▸ in_orbit_refl))))
     Pa)
  (assume Pin,
   obtain a Pain Porba, from exists_of_mem_image Pin,
   mem_filter_of_mem
     (begin esimp [orbits, equiv_classes, orbit_partition], rewrite [mem_image_iff],
       existsi a, exact and.intro !mem_univ Porba end)
     (begin substvars, rewrite [of_mem_filter Pain] end))

lemma orbit_inj_on_fixed_points : set.inj_on (orbit hom H) (ts (fixed_points hom H)) :=
take a₁ a₂, begin
  rewrite [-*mem_eq_mem_to_set, ↑fixed_points, *mem_filter_iff],
  intro Pa₁ Pa₂,
  rewrite [and.right Pa₁, and.right Pa₂],
  exact eq_of_singleton_eq
end

lemma card_fixed_point_orbits_eq : card (fixed_point_orbits hom H) = card (fixed_points hom H) :=
by rewrite fixed_point_orbits_eq; apply card_image_eq_of_inj_on orbit_inj_on_fixed_points

lemma orbit_class_equation : card S = Sum (orbits hom H) card :=
class_equation (orbit_partition hom H)

lemma card_fixed_point_orbits : Sum (fixed_point_orbits hom H) card = card (fixed_point_orbits hom H) :=
calc Sum _ _ = Sum (fixed_point_orbits hom H) (λ x, 1) : Sum_ext (take c Pin, of_mem_filter Pin)
         ... = card (fixed_point_orbits hom H) * 1 : Sum_const_eq_card_mul
         ... = card (fixed_point_orbits hom H) : mul_one (card (fixed_point_orbits hom H))

lemma orbit_class_equation' : card S = card (fixed_points hom H) + Sum {cls ∈ orbits hom H | card cls ≠ 1} card :=
calc card S = Sum (orbits hom H) finset.card : orbit_class_equation
        ... = Sum (fixed_point_orbits hom H) finset.card + Sum {cls ∈ orbits hom H | card cls ≠ 1} card : card_binary_Union_disjoint_sets _ (equiv_class_disjoint _)
        ... = card (fixed_point_orbits hom H) + Sum {cls ∈ orbits hom H | card cls ≠ 1} card : card_fixed_point_orbits
        ... = card (fixed_points hom H) + Sum {cls ∈ orbits hom H | card cls ≠ 1} card : card_fixed_point_orbits_eq

end orbit_partition

section cayley
variables {G : Type}
variable [ambientG : group G]
include ambientG
variable [finG : fintype G]
include finG

definition action_by_lmul : G → perm G :=
take g, perm.mk (lmul_by g) (lmul_inj g)

variable [deceqG : decidable_eq G]
include deceqG

lemma action_by_lmul_hom : homomorphic (@action_by_lmul G _ _) :=
take g₁ (g₂ : G), eq.symm (calc
      action_by_lmul g₁ * action_by_lmul g₂
    = perm.mk ((lmul_by g₁)∘(lmul_by g₂)) _ : rfl
... = perm.mk (lmul_by (g₁*g₂)) _ : by congruence; apply coset.lmul_compose)

lemma action_by_lmul_inj : injective (@action_by_lmul G _ _) :=
take g₁ g₂, assume Peq, perm.no_confusion Peq
  (λ Pfeq Pqeq,
  have Pappeq : g₁*1 = g₂*1, from congr_fun Pfeq _,
  calc g₁ = g₁ * 1 : mul_one
      ... = g₂ * 1 : Pappeq
      ... = g₂ : mul_one)

definition action_by_lmul_is_iso [instance] : is_iso_class (@action_by_lmul G _ _) :=
is_iso_class.mk action_by_lmul_hom action_by_lmul_inj

end cayley

section lcosets
open fintype subtype

section
open list set

structure finite_set (A : Type) :=
(carrier : set A) (elems : list A) (nodup : nodup elems) (complete : ∀ a, a ∈ carrier ↔ a ∈ elems)

check @finite_set.elems
definition finite_set_to_finset {A : Type} (s : finite_set A) : finset A :=
to_finset_of_nodup (finite_set.elems s) (finite_set.nodup s)

structure is_finite [class] {A : Type} (s : set A) :=
(elems : list A) (nodup : nodup elems) (complete : ∀ a, a ∈ s ↔ a ∈ elems)

definition set_to_finset {A : Type} (s : set A) [fins : is_finite s] :=
to_finset_of_nodup (is_finite.elems s) (is_finite.nodup s)

end

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

variables H : finset G

definition action_on_lcoset : G → perm (lcoset_type univ H) :=
take g, perm.mk (lcoset_lmul (mem_univ g)) lcoset_lmul_inj

variable {H}

lemma action_on_lcoset_hom : homomorphic (action_on_lcoset H) :=
take g₁ g₂, eq_of_feq (funext take S, subtype.eq
  (by rewrite [↑action_on_lcoset, ↑lcoset_lmul, -fin_lcoset_compose]))

variable [finsubgH : is_finsubg H]
include finsubgH


end lcosets

section perm_fin
open fin nat eq.ops

variable {n : nat}

definition lift_perm (p : perm (fin n)) : perm (fin (succ n)) :=
perm.mk (lift_fun p) (lift_fun_of_inj (perm.inj p))

definition lower_perm (p : perm (fin (succ n))) (P : p maxi = maxi) : perm (fin n) :=
perm.mk (lower_inj p (perm.inj p) P)
  (take i j, begin
  rewrite [-eq_iff_veq, *lower_inj_apply, eq_iff_veq],
  apply injective_compose (perm.inj p) lift_succ_inj
  end)

lemma lift_lower_eq : ∀ {p : perm (fin (succ n))} (P : p maxi = maxi),
  lift_perm (lower_perm p P) = p
| (perm.mk pf Pinj) := assume Pmax, begin
  rewrite [↑lift_perm], congruence,
  apply funext, intro i,
  assert Pfmax : pf maxi = maxi, apply Pmax,
  assert Pd : decidable (i = maxi),
    exact _,
    cases Pd with Pe Pne,
      rewrite [Pe, Pfmax], apply lift_fun_max,
      rewrite [lift_fun_of_ne_max Pne, ↑lower_perm, ↑lift_succ],
      rewrite [-eq_iff_veq, -val_lift, lower_inj_apply, eq_iff_veq],
      congruence, rewrite [-eq_iff_veq]
  end

lemma lift_perm_inj : injective (@lift_perm n) :=
take p1 p2, assume Peq, eq_of_feq (lift_fun_inj (feq_of_eq Peq))

lemma lift_perm_inj_on_univ : set.inj_on (@lift_perm n) (ts univ) :=
eq.symm to_set_univ ▸ iff.elim_left set.injective_iff_inj_on_univ lift_perm_inj

lemma lift_to_stab : image (@lift_perm n) univ = stab id univ maxi :=
ext (take (pp : perm (fin (succ n))), iff.intro
  (assume Pimg, obtain p P_ Pp, from exists_of_mem_image Pimg,
  assert Ppp : pp maxi = maxi, from calc
    pp maxi = lift_perm p maxi : {eq.symm Pp}
        ... = lift_fun p maxi : rfl
        ... = maxi : lift_fun_max,
  mem_filter_of_mem !mem_univ Ppp)
  (assume Pstab,
  assert Ppp : pp maxi = maxi, from of_mem_filter Pstab,
  mem_image_of_mem_of_eq !mem_univ (lift_lower_eq Ppp)))

definition move_from_max_to (i : fin (succ n)) : perm (fin (succ n)) :=
perm.mk (madd (i - maxi)) madd_inj

lemma orbit_max : orbit (@id (perm (fin (succ n)))) univ maxi = univ :=
ext (take i, iff.intro
  (assume P, !mem_univ)
  (assume P, begin
    apply mem_image_of_mem_of_eq,
      apply mem_image_of_mem_of_eq,
        apply mem_univ (move_from_max_to i), apply rfl,
      apply sub_add_cancel
    end))

lemma card_orbit_max : card (orbit (@id (perm (fin (succ n)))) univ maxi) = succ n :=
calc card (orbit (@id (perm (fin (succ n)))) univ maxi) = card univ : {orbit_max}
                                                    ... = succ n : card_fin (succ n)

open fintype

lemma card_lift_to_stab : card (stab (@id (perm (fin (succ n)))) univ maxi) = card (perm (fin n)) :=
 calc finset.card (stab (@id (perm (fin (succ n)))) univ maxi)
    = finset.card (image (@lift_perm n) univ) : {eq.symm lift_to_stab}
... = card univ : card_image_eq_of_inj_on lift_perm_inj_on_univ

lemma card_perm_step : card (perm (fin (succ n))) = (succ n) * card (perm (fin n)) :=
 calc card (perm (fin (succ n)))
    = card (orbit id univ maxi) * card (stab id univ maxi) : orbit_stabilizer_theorem
... = (succ n) * card (stab id univ maxi) : {card_orbit_max}
... = (succ n) * card (perm (fin n)) : {card_lift_to_stab}

end perm_fin
end group

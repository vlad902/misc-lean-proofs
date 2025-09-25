/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Subset
import Mathlib.Tactic.ENatToNat

/-!
# Dilworth's theorem

This file proves Dilworth's and Mirsky's theorems, along with the requisite definitions required to
state them.

## Definitions

* `chainHeight` / `antichainWidth`: The maximum size of any chain/antichain in a given order.
* `IsChainPartition` / `IsAntichainPartition`: A predicate for whether a given set of sets
   is a partition of the parent order into disjoint chains/antichains
* `minChainPartition` / `minAntiChainPartition`: The minimum size of a chain/antichain partition in
   a given order.

* `minChainPartition_eq_antichainWidth`: Dilworth's theorem for finite posets.
* `minAntichainPartition_eq_chainHeight`: Mirsky's theorem.
-/

-- #29833
section PR29833
variable {α} {s : Set α}
@[simp] theorem Set.encard_le_card : s.encard ≤ ENat.card α := by
  rw [← Set.encard_univ]
  exact Set.encard_le_encard (fun _ a ↦ trivial)

@[simp] theorem Set.ncard_le_card [Finite α] : s.ncard ≤ Nat.card α := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (fun _ a ↦ trivial) Set.finite_univ

theorem Set.one_le_ncard_insert (a : α) (s : Set α) [Finite ↑s] : 1 ≤ (insert a s).ncard :=
  Nat.one_le_iff_ne_zero.mpr <| Set.ncard_ne_zero_of_mem (mem_insert a s)

end PR29833

-- #29834
section PR29834

open Function Set IsAntichain

variable {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : Set α} {a b : α}

@[simp] protected theorem IsAntichain.empty : IsAntichain r ∅ :=
  pairwise_empty _

@[simp] protected theorem IsAntichain.singleton : IsAntichain r { a } :=
  pairwise_singleton _ _

protected theorem IsAntichain.union :
    IsAntichain r (s ∪ t) ↔
      IsAntichain r s ∧ IsAntichain r t ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → rᶜ a b ∧ rᶜ b a := by
  rw [IsAntichain, IsAntichain, IsAntichain, pairwise_union]

-- #29835
def IsMaxAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  IsAntichain r s ∧ ∀ ⦃t⦄, IsAntichain r t → s ⊆ t → s = t

namespace IsMaxAntichain

theorem isAntichain (h : IsMaxAntichain r s) : IsAntichain r s :=
  h.1

protected theorem image {s : β → β → Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxAntichain r c) :
    IsMaxAntichain s (e '' c) where
  left := hc.isAntichain.image _ fun _ _ ↦ e.map_rel_iff'.mp
  right t ht hf := by
    rw [← e.coe_fn_toEquiv, ← e.toEquiv.eq_preimage_iff_image_eq, preimage_equiv_eq_image_symm]
    exact hc.2 (ht.image _ fun _ _ ↦ e.symm.map_rel_iff.mp)
      ((e.toEquiv.subset_symm_image _ _).2 hf)

protected theorem isEmpty_iff (h : IsMaxAntichain r s) : IsEmpty α ↔ IsEmpty s := by
  refine ⟨fun _ ↦ isEmpty_coe_sort.mpr s.eq_empty_of_isEmpty, fun h' ↦ ?_⟩
  by_contra! hh
  obtain ⟨x⟩ := not_isEmpty_iff.mp hh
  simp only [IsMaxAntichain, isEmpty_coe_sort.mp h', IsAntichain.empty, empty_subset, forall_const,
    true_and] at h
  exact singleton_ne_empty x (h IsAntichain.singleton).symm

protected theorem nonempty_iff (h : IsMaxAntichain r s) : Nonempty α ↔ Nonempty s := by
  grind [not_nonempty_iff, IsMaxAntichain.isEmpty_iff]

protected theorem symm (h : IsMaxAntichain r s) : IsMaxAntichain (flip r) s :=
  ⟨h.isAntichain.flip, fun _ ht₁ ht₂ ↦ h.2 ht₁.flip ht₂⟩

end IsMaxAntichain

protected theorem IsMaxChain.isEmpty_iff (h : IsMaxChain r s) : IsEmpty α ↔ IsEmpty s := by
  refine ⟨fun _ ↦ isEmpty_coe_sort.mpr s.eq_empty_of_isEmpty, fun h' ↦ ?_⟩
  by_contra! hh
  obtain ⟨x⟩ := not_isEmpty_iff.mp hh
  simp only [IsMaxChain, isEmpty_coe_sort.mp h', IsChain.empty, empty_subset, forall_const,
    true_and] at h
  exact singleton_ne_empty x (h IsChain.singleton).symm

protected theorem IsMaxChain.nonempty_iff (h : IsMaxChain r s) : Nonempty α ↔ Nonempty s := by
  grind [not_nonempty_iff, IsMaxChain.isEmpty_iff]

theorem IsMaxChain.symm (h : IsMaxChain r s) : IsMaxChain (flip r) s :=
  ⟨h.isChain.symm, fun _ ht₁ ht₂ ↦ h.2 ht₁.symm ht₂⟩

end PR29834

-- mathlib4/Mathlib/Data/ENat/Basic.lean
theorem ENat.le_sub_of_add_le_right {a b c : ℕ∞} (hb : b ≠ ⊤) : a + b ≤ c → a ≤ c - b :=
  (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right

theorem ENat.le_sub_one_of_lt {a b : ℕ∞} (hab : a < b) : a ≤ b - 1 := by
  cases b
  · simp
  · exact le_sub_of_add_le_right one_ne_top <| lt_coe_add_one_iff.mp <| lt_tsub_iff_right.mp hab

-- TODO: Copy below?
theorem IsAntichain.coe_univ {α : Type*} {r : α → α → Prop} {s : Set α} (h : IsAntichain r s) :
    @IsAntichain ↑s (r ↑· ↑·) Set.univ :=
  fun a _ b _ hne ↦  @h a a.property b b.property (Subtype.coe_ne_coe.mpr hne)

theorem IsAntichain.sdiff {α : Type*} {r : α → α → Prop} {s t : Set α} (h : IsAntichain r s) :
    IsAntichain r (s \ t) :=
  fun a ha b hb hne ↦ @h a (Set.mem_of_mem_inter_left ha) b (Set.mem_of_mem_inter_left hb) hne

theorem IsChain.coe_univ {α : Type*} {r : α → α → Prop} {s : Set α} :
    @IsChain ↑s (r ↑· ↑·) Set.univ ↔ IsChain r s :=
  ⟨fun h a ha b hb hne ↦ @h ⟨a, ha⟩ (by simp) ⟨b, hb⟩ (by simp) (by simp [hne]),
   fun h a _ b _ hne ↦ @h a.1 a.2 b.1 b.2 (Subtype.coe_ne_coe.mpr hne)⟩

theorem IsChain.sdiff {α : Type*} {r : α → α → Prop} {s t : Set α} (h : IsChain r s) :
    IsChain r (s \ t) :=
  fun a ha b hb hne ↦ @h a (Set.mem_of_mem_inter_left ha) b (Set.mem_of_mem_inter_left hb) hne

section IsChain

variable {α β : Type*} {r : α → α → Prop} {l : List α} {a : α}

theorem IsChain.preimage (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
    (hf : Function.Injective f) (h : ∀ x y, s (f x) (f y) → r x y) {c : Set β} (hrc : IsChain s c) :
    IsChain r (f ⁻¹' c) := by
  intro _ ha _ hb hne
  have := hrc ha hb (fun h ↦ hne (hf h))
  grind

theorem IsChain.exists_isTop {α : Type*} [Preorder α] (s : Set α) [Finite s] (h : Nonempty s)
    (hs : IsChain (· ≤ ·) s) : ∃ x : s, IsTop x := by
  obtain ⟨x, hx₁, hx₂⟩ := s.toFinite.exists_maximal (Set.nonempty_coe_sort.mp h)
  refine ⟨⟨x, hx₁⟩, fun a ↦ ?_⟩
  by_cases h' : x = a.1
  · simp [h']
  · rcases hs hx₁ a.2 h' with h'' | h''
    · exact hx₂ a.2 h''
    · exact h''

theorem IsChain.exists_isBot {α : Type*} [Preorder α] (s : Set α) [Finite s] (h : Nonempty s)
    (hs : IsChain (· ≤ ·) s) : ∃ x : s, IsBot x :=
  hs.symm.exists_isTop (α := αᵒᵈ) s h

theorem IsMaxChain.exists_isMax {α : Type*} [Preorder α] {s : Set α} [Finite s] (h : Nonempty s)
    (hs : IsMaxChain (· ≤ ·) s) : ∃ x : α, x ∈ s ∧ IsMax x := by
  by_contra! hh
  obtain ⟨x, hx₁, hx₂⟩ := s.toFinite.exists_maximal (Set.nonempty_coe_sort.mp (by assumption))
  have := hh x hx₁
  simp only [IsMax, not_forall] at this
  obtain ⟨z, hz₁, hz₂⟩ := this
  have : IsChain (· ≤ ·) (s ∪ {z}) := by
    refine isChain_union.mpr ⟨hs.isChain, IsChain.singleton, fun a ha₁ ↦ ?_⟩
    by_cases h' : x = a
    · grind
    · rcases hs.1 hx₁ ha₁ h' with h'' | h'' <;> grind [le_trans]
  refine hz₂ (hx₂ ?_ hz₁)
  rw [hs.2 this (by simp)]
  simp

theorem IsMaxChain.exists_isMin {α : Type*} [Preorder α] (s : Set α) [Finite s] (h : Nonempty s)
    (hs : IsMaxChain (· ≤ ·) s) : ∃ x : α, x ∈ s ∧ IsMin x :=
  hs.symm.exists_isMax (α := αᵒᵈ) h

namespace IsChain

variable {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {r' : β → β → Prop} {s : Set α}

theorem image_relEmbedding (hs : IsChain r s) (φ : r ↪r r') : IsChain r' (φ '' s) := by
  intro b hb b' hb' h
  rw [Set.mem_image] at hb hb'
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  have := hs has has' (fun haa' => h (by rw [haa']))
  grind [RelEmbedding.map_rel_iff]

theorem preimage_relEmbedding {t : Set β} (ht : IsChain r' t) (φ : r ↪r r') :
    IsChain r (φ ⁻¹' t) := fun _ ha _s ha' hne => by
  have := ht ha ha' (fun h => hne (φ.injective h))
  grind [RelEmbedding.map_rel_iff]

theorem image_relIso (hs : IsChain r s) (φ : r ≃r r') : IsChain r' (φ '' s) :=
  hs.image_relEmbedding φ.toRelEmbedding

theorem preimage_relIso {t : Set β} (hs : IsChain r' t) (φ : r ≃r r') :
    IsChain r (φ ⁻¹' t) :=
  hs.preimage_relEmbedding φ.toRelEmbedding

theorem image_relEmbedding_iff {φ : r ↪r r'} : IsChain r' (φ '' s) ↔ IsChain r s :=
  ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h =>
    h.image_relEmbedding φ⟩

theorem image_relIso_iff {φ : r ≃r r'} : IsChain r' (φ '' s) ↔ IsChain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

theorem image_embedding [LE α] [LE β] (hs : IsChain (· ≤ ·) s) (φ : α ↪o β) :
    IsChain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _

theorem preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsChain (· ≤ ·) t) (φ : α ↪o β) :
    IsChain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _

theorem image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsChain (· ≤ ·) (φ '' s) ↔ IsChain (· ≤ ·) s :=
  image_relEmbedding_iff

theorem image_iso [LE α] [LE β] (hs : IsChain (· ≤ ·) s) (φ : α ≃o β) :
    IsChain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _

theorem image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsChain (· ≤ ·) (φ '' s) ↔ IsChain (· ≤ ·) s :=
  image_relEmbedding_iff

theorem preimage_iso [LE α] [LE β] {t : Set β} (ht : IsChain (· ≤ ·) t) (φ : α ≃o β) :
    IsChain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _

theorem preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsChain (· ≤ ·) (φ ⁻¹' t) ↔ IsChain (· ≤ ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩

end IsChain

section height

open ENat

variable (α : Type*) (r : α → α → Prop)

noncomputable def chainHeight : ℕ∞ := ⨆ s : {s : Set α // IsChain r s}, s.val.encard

theorem chainHeight_eq_biInf :
  chainHeight α r = ⨆ s : {s : Set α // IsChain r s}, s.val.encard := rfl

theorem chainHeight_le_card : chainHeight α r ≤ ENat.card α := by
  simp [chainHeight_eq_biInf]

theorem chainHeight_ne_top_of_finite [Finite α] : chainHeight α r ≠ ⊤ := by
  obtain ⟨n, hn₁, hn₂⟩ := le_coe_iff.mp <| card_eq_coe_natCard α ▸ (chainHeight_le_card α r)
  simp [hn₁]

theorem chainHeight_eq_zero_iff : chainHeight α r = 0 ↔ IsEmpty α := by
  constructor
  · intro h
    by_contra! hh
    obtain ⟨x⟩ := not_isEmpty_iff.mp hh
    simp only [chainHeight, iSup_eq_zero, Set.encard_eq_zero, Subtype.forall] at h
    have := h {x}
    simp at this
  · simp_all [chainHeight, Set.eq_empty_of_isEmpty]

theorem exists_of_le_chainHeight (n : ℕ) (h : n ≤ chainHeight α r) :
    ∃ s : Set α, s.encard = n ∧ IsChain r s := by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · have : ∃ s : Set α, IsChain r s ∧ n ≤ s.encard := by
      contrapose! h
      refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun s ↦ ?_⟩
      · enat_to_nat
        exact Nat.sub_one_lt h'
      · exact ENat.le_sub_one_of_lt <| h s.1 s.2
    obtain ⟨s, hs₁, hs₂⟩ := this
    obtain ⟨t, ht₁, ht₂⟩ := Set.exists_subset_encard_eq hs₂
    exact ⟨t, ht₂, hs₁.mono ht₁⟩

theorem exists_of_chainHeight_ne_top (h : chainHeight α r ≠ ⊤) :
    ∃ s : Set α, s.encard = chainHeight α r ∧ IsChain r s := by
  have : Nonempty { s // IsChain r s } := ⟨∅, by simp⟩
  obtain ⟨s, hs⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_biInf, lt_top_iff_ne_top])
  exact ⟨s.1, hs, s.2⟩

theorem exists_eq_chainHeight_of_finite [Finite α] :
    ∃ s : Set α, s.encard = chainHeight α r ∧ IsChain r s :=
  exists_of_chainHeight_ne_top α r (chainHeight_ne_top_of_finite α r)

theorem encard_le_chainHeight (s : Set α) (h : IsChain r s) : s.encard ≤ chainHeight α r :=
  le_iSup_iff.mpr fun _ a ↦ a ⟨s, h⟩

theorem finite_of_chainHeight_ne_top (s : Set α) (h₁ : IsChain r s) (h₂ : chainHeight α r ≠ ⊤) :
    s.Finite :=
  Set.encard_ne_top_iff.mp <| ne_top_of_le_ne_top h₂ <| encard_le_chainHeight α r s h₁

theorem isMaxChain_of_eq_chainHeight (s : Set α) (h₁ : IsChain r s)
    (h₂ : s.encard = chainHeight α r) (h₃ : chainHeight α r ≠ ⊤) : IsMaxChain r s := by
  refine ⟨h₁, ?_⟩
  contrapose! h₂
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := h₂
  refine ne_of_lt <| lt_iSup_iff.mpr ⟨⟨t, ht₁⟩, ?_⟩
  exact Set.Finite.encard_lt_encard (finite_of_chainHeight_ne_top α r s h₁ h₃) (by grind)

theorem encard_lt_chainHeight_of_not_isMaxChain (s : Set α) [Finite s] (h₁ : IsChain r s)
    (h₂ : ¬IsMaxChain r s) : s.encard < chainHeight α r := by
  contrapose! h₂
  refine ⟨h₁, fun t ht₁ ht₂ ↦ ?_⟩
  by_contra! hh
  have := Set.Finite.encard_lt_encard (by assumption) ⟨ht₂, by grind⟩
  have := lt_of_lt_of_le (lt_of_le_of_lt h₂ this) (encard_le_chainHeight α r t ht₁)
  simp at this

theorem chainHeight_le_of_relEmbedding (β : Type*) (r' : β → β → Prop) (e : r ↪r r') :
    chainHeight α r ≤ chainHeight β r' := by
  refine forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  obtain ⟨a, ha₁, ha₂⟩ := exists_of_le_chainHeight α r n hn
  have : (e '' a).encard = n := by rw [Function.Injective.encard_image e.injective, ha₁]
  exact this ▸ encard_le_chainHeight _ _ (e '' a) <| IsChain.image_relEmbedding_iff.mpr ha₂

theorem chainHeight_eq_of_relIso (β : Type*) (r' : β → β → Prop) (e : r ≃r r') :
    chainHeight α r = chainHeight β r' :=
  le_antisymm (chainHeight_le_of_relEmbedding α r β r' e)
    (chainHeight_le_of_relEmbedding β r' α r e.symm)

theorem chainHeight_coe_univ :
    chainHeight ↑Set.univ (r ·.val ·.val) = chainHeight α r :=
  chainHeight_eq_of_relIso (e := { toEquiv := Equiv.Set.univ α, map_rel_iff' := by simp })

theorem chainHeight_subset (s t : Set α) (h : s ⊆ t) :
    chainHeight s (r ·.val ·.val) ≤ chainHeight t (r ·.val ·.val) :=
  chainHeight_le_of_relEmbedding _ _ _ _
    { toFun := fun x ↦ ⟨x.1, h x.2⟩, inj' := Set.inclusion_injective h, map_rel_iff' := by simp }

end height

section width

open ENat

variable (α : Type*) (r : α → α → Prop)

noncomputable def antichainWidth : ℕ∞ := ⨆ s : {s : Set α // IsAntichain r s}, s.val.encard

theorem antichainWidth_eq_biInf :
  antichainWidth α r = ⨆ s : {s : Set α // IsAntichain r s}, s.val.encard := rfl

theorem antichainWidth_le_card : antichainWidth α r ≤ ENat.card α := by
  simp [antichainWidth_eq_biInf]

theorem antichainWidth_ne_top_of_finite [Finite α] : antichainWidth α r ≠ ⊤ := by
  obtain ⟨n, hn₁, hn₂⟩ := le_coe_iff.mp <| card_eq_coe_natCard α ▸ (antichainWidth_le_card α r)
  simp [hn₁]

theorem antichainWidth_eq_zero_iff : antichainWidth α r = 0 ↔ IsEmpty α := by
  constructor
  · intro h
    by_contra! hh
    obtain ⟨x⟩ := not_isEmpty_iff.mp hh
    simp only [antichainWidth, iSup_eq_zero, Set.encard_eq_zero, Subtype.forall] at h
    have := h {x}
    simp at this
  · simp_all [antichainWidth, Set.eq_empty_of_isEmpty]

theorem exists_of_le_antichainWidth (n : ℕ) (h : n ≤ antichainWidth α r) :
    ∃ s : Set α, s.encard = n ∧ IsAntichain r s := by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · have : ∃ s : Set α, IsAntichain r s ∧ n ≤ s.encard := by
      contrapose! h
      refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun s ↦ ?_⟩
      · enat_to_nat
        exact Nat.sub_one_lt h'
      · exact ENat.le_sub_one_of_lt <| h s.1 s.2
    obtain ⟨s, hs₁, hs₂⟩ := this
    obtain ⟨t, ht₁, ht₂⟩ := Set.exists_subset_encard_eq hs₂
    exact ⟨t, ht₂, hs₁.subset ht₁⟩

theorem exists_of_antichainWidth_ne_top (h : antichainWidth α r ≠ ⊤) :
    ∃ s : Set α, s.encard = antichainWidth α r ∧ IsAntichain r s := by
  have : Nonempty { s // IsAntichain r s } := ⟨∅, by simp⟩
  obtain ⟨s, hs⟩ := exists_eq_iSup_of_lt_top (by rwa [← antichainWidth_eq_biInf, lt_top_iff_ne_top])
  exact ⟨s.1, hs, s.2⟩

theorem exists_eq_antichainWidth_of_finite [Finite α] :
    ∃ s : Set α, s.encard = antichainWidth α r ∧ IsAntichain r s :=
  exists_of_antichainWidth_ne_top α r (antichainWidth_ne_top_of_finite α r)

theorem encard_le_antichainWidth (s : Set α) (h : IsAntichain r s) :
    s.encard ≤ antichainWidth α r :=
  le_iSup_iff.mpr fun _ a ↦ a ⟨s, h⟩

theorem finite_of_antichainWidth_ne_top (s : Set α) (h₁ : IsAntichain r s)
    (h₂ : antichainWidth α r ≠ ⊤) : s.Finite :=
  Set.encard_ne_top_iff.mp <| ne_top_of_le_ne_top h₂ <| encard_le_antichainWidth α r s h₁

theorem isMaxAntichain_of_eq_antichainWidth (s : Set α) (h₁ : IsAntichain r s)
    (h₂ : s.encard = antichainWidth α r) (h₃ : antichainWidth α r ≠ ⊤) : IsMaxAntichain r s := by
  refine ⟨h₁, ?_⟩
  contrapose! h₂
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := h₂
  refine ne_of_lt <| lt_iSup_iff.mpr ⟨⟨t, ht₁⟩, ?_⟩
  exact Set.Finite.encard_lt_encard (finite_of_antichainWidth_ne_top α r s h₁ h₃) (by grind)

theorem encard_lt_antichainWidth_of_not_isMaxAntichain (s : Set α) [Finite s] (h₁ : IsAntichain r s)
    (h₂ : ¬IsMaxAntichain r s) : s.encard < antichainWidth α r := by
  contrapose! h₂
  refine ⟨h₁, fun t ht₁ ht₂ ↦ ?_⟩
  by_contra! hh
  have := Set.Finite.encard_lt_encard (by assumption) ⟨ht₂, by grind⟩
  have := lt_of_lt_of_le (lt_of_le_of_lt h₂ this) (encard_le_antichainWidth α r t ht₁)
  simp at this

theorem antichainWidth_le_of_relEmbedding (β : Type*) (r' : β → β → Prop) (e : r ↪r r') :
    antichainWidth α r ≤ antichainWidth β r' := by
  refine forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  obtain ⟨a, ha₁, ha₂⟩ := exists_of_le_antichainWidth α r n hn
  have : (e '' a).encard = n := by rw [Function.Injective.encard_image e.injective, ha₁]
  exact this ▸ encard_le_antichainWidth _ _ (e '' a) <| IsAntichain.image_relEmbedding_iff.mpr ha₂

theorem antichainWidth_eq_of_relIso (β : Type*) (r' : β → β → Prop) (e : r ≃r r') :
    antichainWidth α r = antichainWidth β r' :=
  le_antisymm (antichainWidth_le_of_relEmbedding α r β r' e)
    (antichainWidth_le_of_relEmbedding β r' α r e.symm)

theorem antichainWidth_coe_univ :
    antichainWidth ↑Set.univ (r ·.val ·.val) = antichainWidth α r :=
  antichainWidth_eq_of_relIso (e := { toEquiv := Equiv.Set.univ α, map_rel_iff' := by simp })

theorem antichainWidth_subset (s t : Set α) (h : s ⊆ t) :
    antichainWidth s (r ·.val ·.val) ≤ antichainWidth t (r ·.val ·.val) :=
  antichainWidth_le_of_relEmbedding _ _ _ _
    { toFun := fun x ↦ ⟨x.1, h x.2⟩, inj' := Set.inclusion_injective h, map_rel_iff' := by simp }

end width

end IsChain

section AntichainPartition

variable (α : Type*) (r : α → α → Prop)

def IsAntichainPartition (S : Set (Set α)) :=
  (∀ x : α, ∃! s ∈ S, x ∈ s) ∧ (∀ s ∈ S, IsAntichain r s)

theorem exists_IsAntichainPartition :
    ∃ s : Set (Set α), IsAntichainPartition α r s ∧ s.encard = ENat.card α := by
  refine ⟨Set.range ({·}), ⟨fun a ↦ ⟨{a}, by simp⟩, by simp⟩, ?_⟩
  rw [← @Set.image_univ, ← Set.encard_univ α]
  exact Function.Injective.encard_image Set.singleton_injective Set.univ

theorem isAntichainPartition_sdiff_empty {s : Set (Set α)} (hs : IsAntichainPartition α r s) :
    IsAntichainPartition α r (s \ {∅}) := by
  refine ⟨fun x ↦ ?_, fun t ht ↦ hs.2 t ht.1⟩
  have := hs.1 x
  grind

theorem isAntichainPartition_image {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {s : Set (Set α)} (hs : IsAntichainPartition α r s) {f : α → β} (hf : Function.Bijective f)
    (h : ∀ ⦃a b : α⦄, r' (f a) (f b) → r a b) : IsAntichainPartition β r' ((f '' ·) '' s) := by
  refine ⟨fun x ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hf.surjective x
    obtain ⟨t, ⟨ht₁, ht₂⟩, ht₃⟩ := hs.1 y
    refine ⟨f '' t, ⟨⟨t, by simp_all⟩, ⟨y, by simp_all⟩⟩, ?_⟩
    simp only [Set.mem_image, and_imp, forall_exists_index, forall_apply_eq_imp_iff₂] at ⊢ ht₃
    exact fun a ha b hb heq ↦ Set.image_eq_image hf.injective |>.mpr <|
      ht₃ a ha (hf.injective (hy ▸ heq) ▸ hb)
  · obtain ⟨u, hu₁, hu₂⟩ := ht
    exact hu₂ ▸ IsAntichain.image (hs.2 u hu₁) _ (by grind)

theorem isAntichainPartition_preimage {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {s : Set (Set α)} (hs : IsAntichainPartition α r s) {f : β → α} (hf : Function.Bijective f)
    (h : ∀ ⦃a b : β⦄, r' a b → r (f a) (f b)) : IsAntichainPartition β r' ((f ⁻¹' ·) '' s) := by
  obtain ⟨g, hgl, hgr⟩ := Function.bijective_iff_has_inverse.mp hf
  have := Function.bijective_iff_has_inverse.mpr ⟨f, ⟨hgr, hgl⟩⟩
  have := isAntichainPartition_image (f := g) (r' := r') hs this (by grind)
  rwa [← Set.image_eq_preimage_of_inverse hgr.leftInverse hgl.rightInverse]

noncomputable def minAntichainPartition : ℕ∞ :=
  ⨅ s : {s : Set (Set α) // IsAntichainPartition α r s}, s.val.encard

theorem minAntichainPartition_eq_biSup :
  minAntichainPartition α r =
    ⨅ s : {s : Set (Set α) // IsAntichainPartition α r s}, s.val.encard := rfl

theorem minAntichainPartition_eq_zero_iff : minAntichainPartition α r = 0 ↔ IsEmpty α := by
  simp [isEmpty_iff, minAntichainPartition, IsAntichainPartition]

theorem one_le_minAntichainPartition_iff : 1 ≤ minAntichainPartition α r ↔ Nonempty α := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    grind [minAntichainPartition_eq_zero_iff, not_nonempty_iff, ENat.lt_one_iff_eq_zero]
  · by_contra! hh
    grind [minAntichainPartition_eq_zero_iff, not_nonempty_iff, ENat.lt_one_iff_eq_zero]

theorem minAntichainPartition_le_card : minAntichainPartition α r ≤ ENat.card α := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_IsAntichainPartition α r
  refine iInf_le_iff.mpr fun b hb ↦ ?_
  grw [hb ⟨s, hs₁⟩, hs₂]

theorem minAntichainPartition_ne_top_of_finite [Finite α] : minAntichainPartition α r ≠ ⊤ := by
  have := minAntichainPartition_le_card α r
  rw [ENat.card_eq_coe_natCard, ENat.le_coe_iff] at this
  obtain ⟨n, hn, _⟩ := this
  simp [hn]

theorem minAntichainPartition_le_encard (S : Set (Set α)) (h : IsAntichainPartition α r S) :
    minAntichainPartition α r ≤ S.encard :=
  iInf_le_iff.mpr fun _ hx ↦ hx ⟨S, h⟩

theorem minAntichainPartition_exists :
    ∃ (S : Set (Set α)), S.encard = minAntichainPartition α r ∧ IsAntichainPartition α r S := by
  have : Nonempty ({s : Set (Set α) // IsAntichainPartition α r s}) := by
    obtain ⟨s, hs, _⟩ := exists_IsAntichainPartition α r
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs, s.property⟩

end AntichainPartition

section ChainPartition

variable (α : Type*) (r : α → α → Prop)

def IsChainPartition (S : Set (Set α)) :=
  (∀ x : α, ∃! s ∈ S, x ∈ s) ∧ (∀ s ∈ S, IsChain r s)

theorem exists_IsChainPartition :
    ∃ s : Set (Set α), IsChainPartition α r s ∧ s.encard = ENat.card α := by
  refine ⟨Set.range ({·}), ⟨fun a ↦ ⟨{a}, by simp⟩, by simp [IsChain.singleton]⟩, ?_⟩
  rw [← @Set.image_univ, ← Set.encard_univ α]
  exact Function.Injective.encard_image Set.singleton_injective Set.univ

theorem isChainPartition_sdiff_empty {s : Set (Set α)} (hs : IsChainPartition α r s) :
    IsChainPartition α r (s \ {∅}) := by
  refine ⟨fun x ↦ ?_, fun t ht ↦ hs.2 t ht.1⟩
  have := hs.1 x
  grind

theorem isChainPartition_image {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {s : Set (Set α)} (hs : IsChainPartition α r s) {f : α → β} (hf : Function.Bijective f)
    (h : ∀ ⦃a b : α⦄, r a b → r' (f a) (f b)) : IsChainPartition β r' ((f '' ·) '' s) := by
  refine ⟨fun x ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hf.surjective x
    obtain ⟨t, ⟨ht₁, ht₂⟩, ht₃⟩ := hs.1 y
    refine ⟨f '' t, ⟨⟨t, by simp_all⟩, ⟨y, by simp_all⟩⟩, ?_⟩
    simp only [Set.mem_image, and_imp, forall_exists_index, forall_apply_eq_imp_iff₂] at ⊢ ht₃
    exact fun a ha b hb heq ↦ Set.image_eq_image hf.injective |>.mpr <|
      ht₃ a ha (hf.injective (hy ▸ heq) ▸ hb)
  · obtain ⟨u, hu₁, hu₂⟩ := ht
    exact hu₂ ▸ IsChain.image _ _ _ (by simp_all) (hs.2 u hu₁)

theorem isChainPartition_preimage {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {s : Set (Set α)} (hs : IsChainPartition α r s) {f : β → α} (hf : Function.Bijective f)
    (h : ∀ ⦃a b : β⦄, r (f a) (f b) → r' a b) : IsChainPartition β r' ((f ⁻¹' ·) '' s) := by
  obtain ⟨g, hgl, hgr⟩ := Function.bijective_iff_has_inverse.mp hf
  have := Function.bijective_iff_has_inverse.mpr ⟨f, ⟨hgr, hgl⟩⟩
  have := isChainPartition_image (f := g) (r' := r') hs this (by grind)
  rwa [← Set.image_eq_preimage_of_inverse hgr.leftInverse hgl.rightInverse]

noncomputable def minChainPartition : ℕ∞ :=
  ⨅ s : {s : Set (Set α) // IsChainPartition α r s}, s.val.encard

theorem minChainPartition_eq_biSup :
  minChainPartition α r =
    ⨅ s : {s : Set (Set α) // IsChainPartition α r s}, s.val.encard := rfl

theorem minChainPartition_eq_zero_iff : minChainPartition α r = 0 ↔ IsEmpty α := by
  simp [isEmpty_iff, minChainPartition, IsChainPartition]

theorem one_le_minChainPartition_iff : 1 ≤ minChainPartition α r ↔ Nonempty α := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    grind [minChainPartition_eq_zero_iff, not_nonempty_iff, ENat.lt_one_iff_eq_zero]
  · by_contra! hh
    grind [minChainPartition_eq_zero_iff, not_nonempty_iff, ENat.lt_one_iff_eq_zero]

theorem minChainPartition_le_card : minChainPartition α r ≤ ENat.card α := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_IsChainPartition α r
  refine iInf_le_iff.mpr fun b hb ↦ ?_
  grw [hb ⟨s, hs₁⟩, hs₂]

theorem minChainPartition_ne_top_of_finite [Finite α] : minChainPartition α r ≠ ⊤ := by
  have := minChainPartition_le_card α r
  rw [ENat.card_eq_coe_natCard, ENat.le_coe_iff] at this
  obtain ⟨n, hn, _⟩ := this
  simp [hn]

theorem minChainPartition_le_encard (S : Set (Set α)) (h : IsChainPartition α r S) :
    minChainPartition α r ≤ S.encard :=
  iInf_le_iff.mpr fun _ hx ↦ hx ⟨S, h⟩

theorem minChainPartition_exists :
    ∃ (S : Set (Set α)), S.encard = minChainPartition α r ∧ IsChainPartition α r S := by
  have : Nonempty ({s : Set (Set α) // IsChainPartition α r s}) := by
    obtain ⟨s, hs, _⟩ := exists_IsChainPartition α r
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs, s.property⟩

end ChainPartition

section mirsky

variable (α : Type*) (r : α → α → Prop)

theorem le_minAntichainPartition_of_isChain (s : Set α) (h : IsChain r s) :
    s.encard ≤ minAntichainPartition α r := by
  by_contra! hh
  obtain ⟨t, ht₁, ht₂⟩ := minAntichainPartition_exists α r
  have (a : α) (ha : a ∈ s) := Classical.choose_spec (ht₂.1 a) |>.1.1
  obtain ⟨x, hx, y, hy, hxy, _⟩ := Set.exists_ne_map_eq_of_encard_lt_of_maps_to (ht₁ ▸ hh) this
  have cc := Classical.choose_spec (ht₂.1 x)
  have := Classical.choose_spec (ht₂.1 y)
  have := (ht₂.2 _ cc.1.1) cc.1.2 (by grind) hxy
  have := (ht₂.2 _ cc.1.1) (by grind) cc.1.2 hxy.symm
  rcases h hx hy hxy <;> contradiction

theorem chainHeight_le_minAntichainPartition : chainHeight α r ≤ minAntichainPartition α r := by
  refine ENat.forall_natCast_le_iff_le.mp fun m h ↦ ?_
  obtain ⟨s, hs₁, hs₂⟩ := exists_of_le_chainHeight α r m (by simp_all)
  exact hs₁ ▸ le_minAntichainPartition_of_isChain α r s hs₂

theorem isAntiChain_isMax [PartialOrder α] : IsAntichain (· ≤ ·) {x : α | IsMax x} := by
  intro x _ y _ _
  simp only [Pi.compl_apply, compl_iff_not]
  by_cases y ≤ x <;> grind [IsMax, le_antisymm]

theorem isMax_inter_nonempty {α : Type*} [Preorder α] [Nonempty α] (hc : chainHeight α (· ≤ ·) ≠ ⊤)
    (s : Set α) (hs : IsMaxChain (· ≤ ·) s) : ({x : α | IsMax x} ∩ s).Nonempty := by
  have : Finite s := finite_of_chainHeight_ne_top α (· ≤ ·) s hs.isChain hc
  obtain ⟨k, hk₁, hk₂⟩ := hs.exists_isMax <| hs.nonempty_iff.mp (by assumption)
  exact ⟨k, Set.mem_inter (fun a ha ↦ hk₂ ha) hk₁⟩

theorem chainHeight_sdiff_add_one_le (α : Type*) [LE α] (hc : chainHeight α (· ≤ ·) ≠ ⊤) (s : Set α)
    (hs₂ : ∀ (t : Set α), IsMaxChain (· ≤ ·) t → (s ∩ t).Nonempty) :
    chainHeight ↑(Set.univ \ s) (· ≤ ·) + 1 ≤ chainHeight α (· ≤ ·) := by
  have := chainHeight_subset α (· ≤ ·) (Set.univ \ s) Set.univ (by simp)
  have hhc := lt_top_iff_ne_top.mp <| lt_of_le_of_lt
    (chainHeight_coe_univ α (· ≤ ·) ▸ this) (lt_top_iff_ne_top.mpr hc)
  obtain ⟨c, hc₁, hc₂⟩ := exists_of_chainHeight_ne_top _ (· ≤ ·) hhc
  obtain ⟨d, hd₁, hd₂⟩ := exists_of_chainHeight_ne_top α (· ≤ ·) hc
  let e₁ : Set α := Subtype.val '' c
  let e₂ : IsChain (· ≤ ·) e₁ := hc₂.image _ _ Subtype.val (fun _ _ x ↦ x)
  have : Finite e₁ := finite_of_chainHeight_ne_top α (· ≤ ·) e₁ e₂ hc
  have tt := encard_lt_chainHeight_of_not_isMaxChain α (· ≤ ·) e₁ e₂
    (by grind [Set.inter_nonempty_iff_exists_right])
  have : c.encard = e₁.encard := by simp [e₁, Function.Injective.encard_image]
  grw [← hc₁, this, Order.add_one_le_of_lt tt]

theorem minAntichainPartition_le_sdiff_add_one (α : Type*) [LE α]
    (s : Set α) (hs : IsAntichain (· ≤ ·) s) :
    minAntichainPartition α (· ≤ ·) ≤
      minAntichainPartition ↑(Set.univ \ s) (· ≤ ·) + 1 := by
  obtain ⟨S, hS₁, hS₂⟩ := minAntichainPartition_exists ↑(Set.univ \ s) (· ≤ ·)
  let T : Set (Set α) := { s } ∪ ((Subtype.val '' ·) '' S)
  have hT : T.encard ≤ minAntichainPartition ↑(Set.univ \ s) (· ≤ ·) + 1 := by
    simp only [Set.singleton_union, ← hS₁, T]
    grw [Set.encard_insert_le]
    rw [Function.Injective.encard_image Set.image_val_injective]
  have : IsAntichainPartition α (· ≤ ·) T := by
    simp only [IsAntichainPartition, Set.singleton_union, Set.mem_insert_iff,
      Set.mem_image, forall_eq_or_imp, hs, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, true_and, T]
    refine ⟨fun x ↦ ?_, fun a ha b hb c hc hbc ↦ ?_⟩
    · by_cases h' : x ∈ Set.univ \ s
      · obtain ⟨u, _, _⟩ := hS₂.1 ⟨x, h'⟩
        exact ⟨u, by grind⟩
      · exact ⟨s, by grind⟩
    · have := @hS₂.2 _ ha ⟨b, by grind⟩ (by grind) ⟨c, by grind⟩ (by grind) (by simp [hbc])
      simpa using this
  grw [minAntichainPartition_le_encard α (· ≤ ·) T this, hT]

theorem minAntichainPartition_eq_chainHeight [PartialOrder α] :
    minAntichainPartition α (· ≤ ·) = chainHeight α (· ≤ ·) := by
  refine ENat.eq_of_forall_natCast_le_iff fun m ↦
    ⟨fun h ↦ ?_, fun h ↦ le_trans h <| chainHeight_le_minAntichainPartition _ _⟩
  induction m generalizing α with
  | zero => simp
  | succ n ih =>
    by_cases h' : Nonempty α
    · by_cases hc : chainHeight α (· ≤ ·) = ⊤
      · simp [hc]
      · simp only [Nat.cast_add, Nat.cast_one]
        have := minAntichainPartition_le_sdiff_add_one α _ (isAntiChain_isMax α)
        have := ih _ <| ENat.addLECancellable_coe 1 |>.add_le_add_iff_right.mp <| le_trans h this
        grw [add_le_add_right this 1, chainHeight_sdiff_add_one_le α hc _ (isMax_inter_nonempty hc)]
    · grind [not_isEmpty_iff, chainHeight_eq_zero_iff, minAntichainPartition_eq_zero_iff]

#print axioms minAntichainPartition_eq_chainHeight

end mirsky

section dilworth

variable (α : Type*) (r : α → α → Prop)

theorem le_minChainPartition_of_isAntichain (s : Set α) (h : IsAntichain r s) :
    s.encard ≤ minChainPartition α r := by
  by_contra! hh
  obtain ⟨t, ht₁, ht₂⟩ := minChainPartition_exists α r
  have (a : α) (ha : a ∈ s) := Classical.choose_spec (ht₂.1 a) |>.1.1
  obtain ⟨x, hx, y, hy, hxy, _⟩ := Set.exists_ne_map_eq_of_encard_lt_of_maps_to (ht₁ ▸ hh) this
  have := Classical.choose_spec (ht₂.1 y)
  have := Classical.choose_spec (ht₂.1 x)
  have := (ht₂.2 _ this.1.1) this.1.2 (by grind) hxy
  have t1 := h hx hy hxy
  have t2 := h hy hx hxy.symm
  simp only [Pi.compl_apply, compl_iff_not] at t1 t2 this
  rcases this with h' | h' <;> simp [t1, t2] at h'

theorem antichainWidth_le_minChainPartition : antichainWidth α r ≤ minChainPartition α r := by
  refine ENat.forall_natCast_le_iff_le.mp fun m h ↦ ?_
  obtain ⟨s, hs₁, hs₂⟩ := exists_of_le_antichainWidth α r m (by simp_all)
  exact hs₁ ▸ le_minChainPartition_of_isAntichain α r s hs₂

theorem minChainPartition_le_sdiff_add_one (α : Type*) [LE α] (s : Set α) (hs : IsChain (· ≤ ·) s) :
    minChainPartition α (· ≤ ·) ≤ minChainPartition ↑(Set.univ \ s) (· ≤ ·) + 1 := by
  obtain ⟨S, hS₁, hS₂⟩ := minChainPartition_exists ↑(Set.univ \ s) (· ≤ ·)
  let T : Set (Set α) := {s} ∪ ((Subtype.val '' ·) '' S)
  have hT : T.encard ≤ minChainPartition ↑(Set.univ \ s) (· ≤ ·) + 1 := by
    simp only [Set.singleton_union, ← hS₁, T]
    grw [Set.encard_insert_le]
    rw [Function.Injective.encard_image Set.image_val_injective]
  have : IsChainPartition α (· ≤ ·) T := by
    simp only [IsChainPartition, Set.singleton_union, Set.mem_insert_iff, Set.mem_image,
      forall_eq_or_imp, hs, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and, T]
    refine ⟨fun x ↦ ?_, fun a ha b hb c hc hbc ↦ ?_⟩
    · by_cases h' : x ∈ Set.univ \ s
      · obtain ⟨u, _, _⟩ := hS₂.1 ⟨x, h'⟩
        exact ⟨u, by grind⟩
      · exact ⟨s, by grind⟩
    · have := @hS₂.2 _ ha ⟨b, by grind⟩ (by grind) ⟨c, by grind⟩ (by grind) (by simp [hbc])
      simpa using this
  grw [minChainPartition_le_encard α (· ≤ ·) T this, hT]

theorem pigeonhole_inter_eq {α : Type u_1} {r : α → α → Prop} {S : Set (Set α)} [Finite S]
    (hS : IsChainPartition α r S) {a : Set α} (ha₁ : a.encard = S.encard) (ha₂ : IsAntichain r a) :
    ∀ s ∈ S, ∃ x : α, (a ∩ s) = {x} := by
  intro s hs
  apply Set.ncard_eq_one.mp
  suffices (a ∩ s).encard ≠ 0 by
    have h := Set.encard_le_coe_iff_finite_ncard_le.mp <| Set.encard_le_one_iff_subsingleton.mpr <|
      inter_subsingleton_of_isAntichain_of_isChain ha₂ (hS.2 s hs)
    have := Set.Nonempty.ncard_pos h.1 (Set.encard_ne_zero.mp this)
    grind
  by_contra hh
  rw [Set.encard_eq_zero] at hh
  have hmap : Set.MapsTo (fun x ↦ Classical.choose (hS.1 x)) a (S \ {s}) := by
    grind [Set.MapsTo, Classical.choose_spec, Disjoint.notMem_of_mem_left,
      =_ Set.disjoint_iff_inter_eq_empty]
  have := Set.exists_ne_map_eq_of_encard_lt_of_maps_to (t := (S \ {s})) (s := a) ?_ hmap
  · obtain ⟨x, hx, y, hy, hxy, _⟩ := this
    have h₁ := ha₂ hx hy hxy
    have h₂ := ha₂ hy hx hxy.symm
    have := Classical.choose_spec (hS.1 y)
    have := Classical.choose_spec (hS.1 x)
    have := (hS.2 _ this.1.1) this.1.2 (by grind) hxy
    simp only [Pi.compl_apply, compl_iff_not] at h₁ h₂ this
    grind
  · rw [ha₁, Set.encard_diff_singleton_of_mem hs, ← Set.Finite.cast_ncard_eq S.toFinite]
    enat_to_nat
    exact Nat.sub_one_lt_of_lt <| Set.Nonempty.ncard_pos S.toFinite <| Set.nonempty_of_mem hs

theorem pigeonhole_delete_largest (C : Set (Set α)) (hC₁ : IsChainPartition α r C)
    (hS₂ : C.encard = antichainWidth α r) (hnetop : antichainWidth α r ≠ ⊤)
    (c d : Set α) (hd : IsChain r d) (hc : c ∈ C)
    (h : ∀ x ∈ c, ∀ a : Set α, IsAntichain r a → a.encard = antichainWidth α r → x ∈ a → x ∈ d) :
    antichainWidth α r = antichainWidth ↑(Set.univ \ d) (r · ·) + 1 := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  · obtain ⟨b, hb₁, hb₂⟩ := exists_of_antichainWidth_ne_top α r hnetop
    let n : Set ↑(Set.univ \ d) := ((fun x ↦ ⟨x.1, by grind⟩) '' (@Set.univ ↑(b \ d)))
    have hna : @IsAntichain ↑(Set.univ \ d) (r · ·) n :=
      IsAntichain.image hb₂.sdiff.coe_univ _ (fun ⦃a_1 b⦄ a ↦ a)
    have hbne : b.encard ≤ n.encard + 1 := by
      rw [Function.Injective.encard_image <| Set.inclusion_injective (by grind)]
      simp only [← Set.encard_diff_add_encard_of_subset (by grind : (b \ d) ⊆ b),
        sdiff_sdiff_right_self, Set.inf_eq_inter, Set.encard_univ_coe, add_comm (b ∩ d).encard]
      refine add_le_add_left (Set.encard_le_one_iff_subsingleton.mpr ?_) (b \ d).encard
      exact inter_subsingleton_of_isAntichain_of_isChain hb₂ hd
    grw [hn, ← hb₁, hbne, encard_le_antichainWidth _ _ _ hna]
  · grw [hn]
    have := antichainWidth_subset α r ↑(Set.univ \ d) Set.univ (by simp)
    refine Order.add_one_le_of_lt <| lt_of_le_of_ne (antichainWidth_coe_univ α r ▸ this) ?_
    by_contra! hh
    obtain ⟨a, ha₁, ha₂⟩ := exists_of_le_antichainWidth ↑(Set.univ \ d) (r · ·)
      (antichainWidth ↑(Set.univ \ d) (r · ·)).toNat (by simp [ENat.coe_toNat_le_self])
    rw [hh, ENat.coe_toNat hnetop] at ha₁
    have hnew : @IsAntichain α r a := ha₂.image Subtype.val (by simp)
    have : Finite C := by grind [Set.Finite.to_subtype, Set.encard_ne_top_iff]
    obtain ⟨x, hx⟩ := pigeonhole_inter_eq hC₁
      (by grind [Function.Injective.encard_image, Subtype.val_injective]) hnew c hc
    rw [Set.eq_singleton_iff_unique_mem] at hx
    grind [Function.Injective.encard_image, Subtype.val_injective]

abbrev overlap_antichain {α : Type*} [LE α] (C : Set (Set α)) (c : C) :=
  { x ∈ c.1 | ∃ s : Set α, x ∈ s ∧ IsAntichain (· ≤ ·) s ∧ s.encard = C.encard }

def overlap_top {α : Type*} [LE α] (C : Set (Set α)) :=
  { x | ∃ c hx, @IsTop (overlap_antichain C c) _ ⟨x, hx⟩ }

theorem isAntichain_overlap_top [PartialOrder α] (C : Set (Set α)) [Finite C]
    (hC : IsChainPartition α (· ≤ ·) C) :
    IsAntichain (· ≤ ·) (overlap_top C) := by
  intro c hc d hd hne
  simp only [overlap_top, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists] at hc hd
  obtain ⟨c₀, hc₀, hc₀mem, hc₀top⟩ := hc
  obtain ⟨d₀, hd₀, hd₀mem, hd₀top⟩ := hd
  by_cases h' : c₀ = d₀
  · subst h'
    have := Subtype.mk_eq_mk.mp <| le_antisymm (hd₀top ⟨c, hc₀mem⟩) (hc₀top ⟨d, hd₀mem⟩)
    contradiction
  · obtain ⟨j, hj1, hj2, hj3⟩ := hd₀mem.2
    obtain ⟨y, hy⟩ := pigeonhole_inter_eq hC hj3 hj2 c₀ hc₀
    rw [Set.eq_singleton_iff_unique_mem] at hy
    have sm : ¬y ≤ d := by
      by_cases h'' : y = d
      · obtain ⟨z, hz₁, hz₂⟩ := hC.1 y
        grind
      · exact hj2 (by grind) hj1 h''
    have ss : y ≤ c := hc₀top ⟨y, by grind⟩
    grw [ss] at sm
    exact sm

theorem overlap_top_encard_eq [Finite α] [PartialOrder α] (C : Set (Set α))
    (hC : IsChainPartition α (· ≤ ·) C) (A : Set α) (hA₁ : A.encard = C.encard)
    (hA₂ : IsAntichain (· ≤ ·) A) :
    (overlap_top C).encard = C.encard := by
  simp only [Subtype.exists, overlap_top]
  refine Set.encard_congr <| Equiv.ofBijective (fun b ↦ ⟨Classical.choose b.2, ?_⟩) ⟨?_, ?_⟩
  · grind [Classical.choose_spec]
  · intro b c heq
    simp at heq
    obtain ⟨sb, hsb₁, hsb₂⟩ := Classical.choose_spec b.2
    obtain ⟨sc, hsc₁, hsc₂⟩ := Classical.choose_spec c.2
    simp only [heq] at hsb₁
    simp only [← heq] at hsc₁
    exact SetCoe.ext <| by simpa using le_antisymm (hsc₂ ⟨b, hsb₁⟩) (hsb₂ ⟨c, hsc₁⟩)
  · intro b
    have (c : C) : Nonempty (overlap_antichain C c) := by
      simp only [Set.coe_setOf, nonempty_subtype]
      obtain ⟨b, hb⟩ := pigeonhole_inter_eq hC hA₁ hA₂ c.1 c.2
      rw [Set.eq_singleton_iff_unique_mem] at hb
      exact ⟨b, by grind, ⟨A, by grind, hA₂, hA₁⟩⟩
    obtain ⟨i, hi⟩ := hC.2 b.1 b.2 |>.mono (by grind) |>.exists_isTop _ (this ⟨b.1, b.2⟩)
    use ⟨i.1, by grind⟩
    obtain ⟨d, hd₁, hd₂⟩ := hC.1 i
    grind [Classical.choose_spec]

theorem minChainPartition_eq_antichainWidth [PartialOrder α] [Finite α] :
    minChainPartition α (· ≤ ·) = antichainWidth α (· ≤ ·) := by
  have (eq := hcard) card := Nat.card α
  induction card using Nat.case_strong_induction_on generalizing α with
  | hz =>
    have := Finite.card_eq_zero_iff.mp hcard.symm
    rw [antichainWidth_eq_zero_iff α _ |>.mpr this, minChainPartition_eq_zero_iff α _ |>.mpr this]
  | hi n ih =>
    refine ENat.eq_of_forall_natCast_le_iff fun m ↦ ⟨fun hm ↦ ?_,
      fun hm ↦ le_trans hm (antichainWidth_le_minChainPartition _ _)⟩
    have : Nonempty α := Nat.card_pos_iff.mp (by grind) |>.1
    obtain ⟨a, ha⟩ := (@Set.univ α).toFinite.exists_maximal (Set.nonempty_iff_univ_nonempty.mp this)
    have heq := ih n (le_refl _) ↑(Set.univ \ {a}) (by simp [hcard.symm])
    obtain ⟨C, hC₁, hC₂⟩ := minChainPartition_exists ↑(Set.univ \ {a}) (· ≤ ·)
    obtain ⟨A, hA₁, hA₂⟩ := exists_eq_antichainWidth_of_finite ↑(Set.univ \ {a}) (· ≤ ·)
    let S : Set ↑(Set.univ \ {a}) := overlap_top C
    have Santi : IsAntichain (· ≤ ·) S := isAntichain_overlap_top _ C hC₂
    by_cases h' : ∃ x : S, x.1 ≤ a
    · obtain ⟨x, hx⟩ := h'
      obtain ⟨t, ht, _⟩ := hC₂.1 x
      let Z := {z ∈ t | z ≤ x}
      have Zchain : IsChain (· ≤ ·) Z := hC₂.2 t ht.1 |>.mono (by simp [Z])
      let K := Subtype.val '' Z ∪ {a}
      have Kchain : IsChain (· ≤ ·) K := by
        refine isChain_union.mpr ⟨?_, IsChain.singleton, ?_⟩
        · exact Monotone.isChain_image (Subtype.mono_coe _) Zchain
        · simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_diff, Set.mem_univ,
            Set.mem_singleton_iff, true_and, exists_and_right, exists_eq_right, ne_eq, forall_eq,
            forall_exists_index, and_imp, Z]
          exact fun _ _ _ hle _ ↦ Or.inl <| le_trans (Subtype.coe_le_coe.mp hle) hx
      have Keq₁ := ih (n + 1 - K.ncard) (by simp [K, Set.one_le_ncard_insert]) ↑(Set.univ \ K)
        (by simp [hcard, Set.ncard_diff (s := K)])
      have Keq₂ : antichainWidth ↑(Set.univ \ K) (· ≤ ·) + 1 = A.encard:= by
        have : antichainWidth ↑(Set.univ \ K) (· ≤ ·) = antichainWidth ↑(Set.univ \ Z) (· ≤ ·) := by
          refine antichainWidth_eq_of_relIso (e := { toEquiv := ?_, map_rel_iff' := ?_ })
          · refine Equiv.ofBijective (fun x ↦ ⟨⟨x.1, by grind⟩, by grind⟩) ?_
            exact Function.bijective_iff_has_inverse.mpr ⟨fun x ↦ ⟨x.1, by grind⟩,
              by grind [Function.leftInverse_iff_comp, Function.rightInverse_iff_comp]⟩
          · simp
        have hpg := pigeonhole_delete_largest _ (· ≤ ·) C hC₂ (by grind)
          (antichainWidth_ne_top_of_finite _ _) t Z Zchain ht.1 (fun y hy s _ _ _ ↦ by
            have := x.2
            simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, overlap_top, S] at this
            obtain ⟨l, _, _, hl⟩ := this
            simpa [Z, hy] using hl ⟨y, by grind, ⟨s, by grind⟩⟩
          )
        simp [hA₁, this, hpg]
      grw [hm, minChainPartition_le_sdiff_add_one α K Kchain]
      rw [Keq₁, Keq₂, hA₁]
      exact antichainWidth_coe_univ α _ ▸ antichainWidth_subset α _ _ _ (by simp)
    · have hia : IsAntichain (· ≤ ·) (Subtype.val '' (overlap_top C) ∪ {a}) := by
        refine IsAntichain.union.mpr ⟨Santi.image _ (by simp), IsAntichain.singleton, ?_⟩
        simp only [Subtype.exists, Pi.compl_apply, compl_iff_not] at ⊢ h'
        grind [Maximal]
      have hCencard : C.encard + 1 = (Subtype.val '' S ∪ {a}).encard := by
        rw [Set.encard_union_eq (by simp), Function.Injective.encard_image (by simp)]
        simp [S, overlap_top_encard_eq _ C hC₂ A (hC₁ ▸ heq ▸ hA₁) hA₂]
      grw [hm, minChainPartition_le_sdiff_add_one α {a} (by simp),
        minChainPartition_le_encard _ _ _ hC₂, hCencard, encard_le_antichainWidth _ _ _ hia]

#print axioms minChainPartition_eq_antichainWidth

end dilworth

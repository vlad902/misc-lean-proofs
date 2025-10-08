/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/

import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import MiscLeanProofs.CayleyGraphHelperLemmas

/-!
# Cayley Graphs

Define a Cayley graph as a group with a generating set that does not include the identity
to satisfy representing the graph as a SimpleGraph.

The main results are `isFreeGroup_of_isTree` and `isTree_of_freeGroupBasis` proving that Cayley
graphs of free groups are trees and that Cayley graphs are trees if they satisfy a condition on
the generating set. conditions under which a Cayley Graph is a tree.

Some small lemmas about when Cayley graphs are connected/trees/locally finite.

Follows Clara Löh's Geometric Group Theory chapter 3.

## TODO
- @[to_additive]
-/

open SimpleGraph

structure CayleyGraph (G : Type*) [Group G] (S : Set G) where
  one_not_mem : 1 ∉ S

namespace CayleyGraph

attribute [local grind =] Walk.length_edges Walk.length_support Walk.not_nil_iff_lt_length
  Walk.drop_length
attribute [local grind =] inv_inv inv_mul_eq_one mul_inv_eq_one

section

variable {G : Type*} [Group G] {S : Set G} (CG : CayleyGraph G S)

def Graph : SimpleGraph G where
  Adj x y := x * y⁻¹ ∈ S ∨ y * x⁻¹ ∈ S
  symm _ _ h := h.symm
  loopless _ := by simp [CG.one_not_mem]

theorem adj_iff {x y} : CG.Graph.Adj x y ↔ x * y⁻¹ ∈ S ∨ y * x⁻¹ ∈ S := by
  constructor <;> exact id

theorem pushforward_group {H : Type*} [Group H] (e : G ≃* H) (CG : CayleyGraph G S) : CayleyGraph H (e '' S) :=
  ⟨fun ⟨s, hsS, hs⟩ ↦
    have : s = (1 : G) := by simpa [MulEquiv.map_one] using hs
    CG.one_not_mem (this ▸ hsS)⟩

def iso_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    CG.Graph ≃g (pushforward_group e CG).Graph where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_rel_iff' {x y} := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with ⟨s, hsS, hs⟩ | ⟨s, hsS, hs⟩
      · have : e (x * y⁻¹) = e s := by simpa using hs.symm
        simp [adj_iff, Set.mem_of_eq_of_mem (e.injective this) hsS]
      · have : e (y * x⁻¹) = e s := by simpa using hs.symm
        simp [adj_iff, Set.mem_of_eq_of_mem (e.injective this) hsS]
    · rcases h with h' | h'
      · exact Or.inl ⟨x * y⁻¹, h', by simp [MulEquiv.map_mul, MulEquiv.map_inv]⟩
      · exact Or.inr ⟨y * x⁻¹, h', by simp [MulEquiv.map_mul, MulEquiv.map_inv]⟩

theorem pushforward_generators {S₁ S₂ : Set G} (CG : CayleyGraph G S₁) (h : S₁ = S₂) : CayleyGraph G S₂ :=
  ⟨h ▸ CG.one_not_mem⟩

def iso_of_eq {S₁ S₂ : Set G} (CG : CayleyGraph G S₁) (h : S₁ = S₂) :
    CG.Graph ≃g (pushforward_generators CG h).Graph where
  toFun := id
  invFun := id
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_rel_iff' {x y} := by simp [h, Graph]

variable {CG : CayleyGraph G S}

theorem walk_darts_mul_mem {v w : G} (p : CG.Graph.Walk v w) :
    ∀ d ∈ p.darts, (d.toProd.1 * d.toProd.2⁻¹) ∈ S ∨ (d.toProd.2 * d.toProd.1⁻¹) ∈ S := by
  induction p <;> simp_all [← CG.adj_iff]

abbrev edge_to_group {v w : G} (p : CG.Graph.Walk v w) : List G :=
  p.darts.map (fun d => d.toProd.1 * d.toProd.2⁻¹)

theorem walk_darts_map_prod_eq {v w : G} (p : CG.Graph.Walk v w) :
    (edge_to_group p).prod = v * w⁻¹ := by
  induction p <;> simp_all [← mul_assoc, edge_to_group]

theorem reachable_iff_exists_list {v w : G} :
    CG.Graph.Reachable v w ↔ ∃ l : List G, (∀ y ∈ l, y ∈ S ∨ y⁻¹ ∈ S) ∧ l.prod = v * w⁻¹ := by
  refine ⟨fun ⟨h⟩ ↦ ⟨_, by simp_all [walk_darts_mul_mem h], walk_darts_map_prod_eq h⟩, ?_⟩
  rintro ⟨L, hL₁, hL₂⟩
  refine Walk.reachable ?_
  induction L generalizing v w with
  | nil =>
    simp only [← eq_mul_inv_iff_mul_eq.mp hL₂, List.prod_nil, one_mul]
    exact Walk.nil' w
  | cons head tail ih =>
    refine Walk.cons' _ (head⁻¹ * v) _ ?_ ?_
    · rcases hL₁ head (by simp) <;> simp_all [← mul_assoc, CG.adj_iff, ← hL₂]
    · exact ih (by simp_all) (by simp [mul_assoc, ← hL₂])

theorem connected_iff : CG.Graph.Connected ↔ Subgroup.closure S = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine Subgroup.eq_top_iff' _ |>.mpr (fun x ↦ ?_)
    have := reachable_iff_exists_list.mp <| h.preconnected x 1
    exact Subgroup.exists_list_of_mem_closure_iff.mpr (by simpa using this)
  · refine { preconnected := fun v w ↦ ?_, nonempty := by use 1 }
    suffices ∀ (u : G), CG.Graph.Reachable 1 u from (this v).symm.trans (this w)
    exact fun _ ↦ reachable_iff_exists_list.mpr <|
      Subgroup.exists_list_of_mem_closure_iff.mp (by simp [h])

def neighborSetMap (CG : CayleyGraph G S) (v : G) (x : (S ∪ S⁻¹ : Set G)) : CG.Graph.neighborSet v :=
  ⟨x * v, by simp [CG.adj_iff, ← Set.mem_inv, or_comm, ← Set.mem_union, Subtype.coe_prop]⟩

theorem bijective_neighborSetMap (CG : CayleyGraph G S) (v : G) :
    Function.Bijective (neighborSetMap CG v) := by
  let inv : CG.Graph.neighborSet v → (S ∪ S⁻¹ : Set G) := fun x => ⟨x.1 * v⁻¹, by
    have := x.2
    simp_all [neighborSet, CG.adj_iff, or_comm]
  ⟩
  apply Set.bijective_iff_bijOn_univ.mpr <| Set.BijOn.mk (by simp) ?_ ?_
  · exact Set.LeftInvOn.injOn (f₁' := inv) (fun x _ ↦ by simp [neighborSetMap, inv])
  · exact Set.LeftInvOn.surjOn (f := inv) (fun x _ ↦ by simp [neighborSetMap, inv]) (by simp)

noncomputable instance [Finite S] : CG.Graph.LocallyFinite := by
  letI : Finite (S⁻¹ : Set G) := Set.finite_inv.mpr (by assumption)
  exact fun v ↦ Set.Finite.fintype <| Finite.ofBijective <| bijective_neighborSetMap CG v

theorem neighborSet_ncard (CG : CayleyGraph G S)  (v : G) :
    (CG.Graph.neighborSet v).ncard = (S ∪ S⁻¹).ncard := by
  suffices (CG.Graph.neighborSet v).encard = (S ∪ S⁻¹ : Set G).encard by simp [Set.ncard_def, this]
  have := Set.univ.encard_preimage_of_bijective (bijective_neighborSetMap CG v) |>.symm
  simpa using this

theorem IsRegularOfDegree [Finite S] : CG.Graph.IsRegularOfDegree (S ∪ S⁻¹).ncard := by
  intro v
  rw [degree, neighborFinset, ← Nat.card_eq_card_toFinset, Nat.card_coe_set_eq]
  exact neighborSet_ncard CG v

private
def aux (x : S × Bool) : G := if x.2 then x.1 else x.1⁻¹

theorem walk_of_generator_list {v w : G} (l : List (S × Bool)) (h₁ : (l.map aux).prod = v * w⁻¹) :
    ∃ p : CG.Graph.Walk v w, p.support = (l.map aux).scanr (fun acc e => acc * e) w := by
  induction l generalizing v w with
  | nil =>
    have : v = w := by simp_all [eq_mul_inv_iff_mul_eq]
    subst this
    exact ⟨Walk.nil' v, by simp⟩
  | cons head tail ih =>
    have : (aux head) * (tail.map aux).prod * w = v := by simpa [eq_mul_inv_iff_mul_eq] using h₁
    subst this
    obtain ⟨L, _⟩ := @ih ((tail.map aux).prod * w) w (by simp)
    have (L : List G) : List.foldr (fun acc e => acc * e) w L = L.prod * w := by
      induction L <;> simp_all [← mul_assoc]
    have : CG.Graph.Adj ((aux head) * (tail.map aux).prod * w) ((tail.map aux).prod * w) := by
      simp only [aux, ite_mul, CG.adj_iff, mul_inv_rev]
      split <;> simp [← mul_assoc]
    exact ⟨Walk.cons' _ _ _ this L, by simp_all⟩

theorem isFreeGroup_of_isTree [DecidableEq S] (h₁ : CG.Graph.IsTree) (h₂ : ∀ s t : S, (s : G) * t ≠ 1) :
    IsFreeGroup G := by
  let ι := fun (x : S) ↦ (x : G)
  refine ⟨⟨S, ⟨⟨MulEquiv.ofBijective (FreeGroup.lift ι) ⟨?_, ?_⟩ |>.symm⟩⟩⟩⟩
  · refine (injective_iff_map_eq_one _).mpr (fun a h ↦ ?_)
    have : (a.toWord.map aux).prod = FreeGroup.lift ι a := by
      have : (a.toWord.map aux).prod = FreeGroup.lift ι (FreeGroup.mk a.toWord) := by
        congr
        grind [aux]
      rw [this, FreeGroup.mk_toWord]
    obtain ⟨p, hp⟩ := walk_of_generator_list (v := (FreeGroup.lift ι) a) (w := 1) (CG := CG)
      a.toWord (by simp [this])
    have hlen : p.length = a.toWord.length := by
      apply Nat.add_one_inj.mp
      rw [← Walk.length_support p, hp]
      induction a.toWord <;> simp
    have : p.IsPath := by
      apply Walk.IsTree.isPath_of_list_chain h₁ p |>.mpr
      by_contra hh
      obtain ⟨n, h', h''⟩ := List.exists_not_getElem_of_not_isChain hh
      have : n + 1 + 1 < p.support.length := by grind
      have := ne_of_adj _ <| p.isChain_adj_support.getElem n (by grind)
      have : p.support[n] = p.support[n + 1 + 1] := by simpa [this, p.edges_eq_zipWith_support] using h''
      simp (disch := grind) only [hp, List.getElem_scanr, ← List.prod_eq_foldr,
        List.prod_drop_succ, List.getElem_map, ← mul_assoc, right_eq_mul, aux] at this
      have := (FreeGroup.isReduced_toWord (x := a)).getElem n (by grind)
      grind
    refine FreeGroup.toWord_eq_nil_iff.mp ?_
    obtain ⟨_, _, hpath⟩ := h₁.existsUnique_path ((FreeGroup.lift ι) a) 1
    have := hpath p this
    rw [← hpath (Walk.nil.copy h.symm rfl) (by simp)] at this
    simp [List.eq_nil_iff_length_eq_zero, ← hlen, this]
  · rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure, Subtype.range_val]
    exact connected_iff.mp h₁.isConnected

end

section

variable {S : Type*} [DecidableEq S] {CG : CayleyGraph (FreeGroup S) (Set.range FreeGroup.of)}
variable {v w : FreeGroup S} (p : CG.Graph.Walk v w)

private noncomputable
def gens_of_walk : List (S × Bool) :=
  p.darts.map (fun d ↦ (d.toProd.1 * d.toProd.2⁻¹).toWord[0]'(
    Nat.pos_of_ne_zero (by simp [mul_inv_eq_one])))

@[local grind =]
private
lemma gens_of_walk_length : (gens_of_walk p).length = p.length := by simp [gens_of_walk]

private
lemma freeGroup_mk_gens_of_walk_index {n : ℕ} (h : n + 1 < p.support.length) :
    FreeGroup.mk [(gens_of_walk p)[n]'(by grind)] = (p.getVert n) * (p.getVert (n + 1))⁻¹ := by
  simp only [gens_of_walk, List.getElem_map, p.darts_eq_getVert]
  have := p.drop n |>.adj_snd (by grind)
  simp only [Walk.drop_getVert, CG.adj_iff, Set.mem_range, FreeGroup.of] at this
  rcases this with ⟨_, yh⟩ | ⟨_, yh⟩
  · simp [← yh, FreeGroup.toWord_mk]
  · rw [eq_mul_inv_iff_mul_eq] at yh
    simp [← yh, FreeGroup.invRev]

private
lemma freeGroup_mk_sublist (n : ℕ) (h : n < p.support.length) :
    FreeGroup.mk ((gens_of_walk p).take n) = v * (p.getVert n)⁻¹ := by
  induction n with
  | zero => simp [FreeGroup.one_eq_mk]
  | succ n ih =>
    simp (disch := grind) [-List.take_append_getElem, List.take_add,
      List.take_one_drop_eq_of_lt_length, ← FreeGroup.mul_mk, ih,
      freeGroup_mk_gens_of_walk_index, ← mul_assoc]

private
lemma freeGroup_mk_gens_of_walk : FreeGroup.mk (gens_of_walk p) = v * w⁻¹ := by
  have := freeGroup_mk_sublist p p.length (by grind)
  rw [Walk.getVert_length] at this
  simp [← this, ← gens_of_walk_length p]

theorem isTree_of_freeGroup (CG : CayleyGraph (FreeGroup S) (Set.range FreeGroup.of)) :
    CG.Graph.IsTree where
  isConnected := connected_iff.mpr <| FreeGroup.closure_range_of S
  IsAcyclic := by
    intro v p hh
    rw [Walk.isCycle_def, Walk.isTrail_def] at hh
    have hnil : ¬p.Nil := by
      have := hh.2.1
      contrapose! this
      exact Walk.nil_iff_eq_nil.mp this
    have : FreeGroup.IsReduced (gens_of_walk p) := by
      by_contra hhh
      obtain ⟨n, hl₁, hl₂⟩ := FreeGroup.exists_of_not_reduced hhh
      apply (List.Pairwise.isChain hh.1).getElem n (by grind)
      have := freeGroup_mk_sublist p n (by grind)
      rw [hl₂, freeGroup_mk_sublist p (n + 2) (by grind), mul_right_inj, inv_inj] at this
      simp (disch := grind) [p.edges_eq_zipWith_support, ← p.getVert_eq_support_getElem, ← this]
    have : (FreeGroup.mk (gens_of_walk p)).toWord.length ≠ 0 := by
      simp_all [FreeGroup.isReduced_iff_reduce_eq.mp this, gens_of_walk_length p]
    simp [freeGroup_mk_gens_of_walk p] at this

end

theorem isTree_of_freeGroupBasis {G S : Type*} [Group G] [DecidableEq S]
    (h : FreeGroupBasis S G) {CG : CayleyGraph G (Set.range (h.repr.symm ∘ FreeGroup.of))} :
    CG.Graph.IsTree := by
  refine (iso_of_mulEquiv CG h.repr).isTree_iff.mpr <| (iso_of_eq _ ?_).isTree_iff.mpr <|
    isTree_of_freeGroup _
  refine Set.ext fun x ↦ ⟨?_, by simp_all⟩
  exact fun ⟨y, ⟨z, hz⟩, hy⟩ ↦ hy ▸ ⟨z, h.repr.symm_apply_eq.mp hz⟩

end CayleyGraph

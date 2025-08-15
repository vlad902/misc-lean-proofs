import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import MiscLeanProofs.CayleyGraphHelperLemmas

/-!
# Cayley Graphs

Define a Cayley graph as a group with a generating set that does not include the identity,
this is to satisfy representing the graph as a SimpleGraph.

Then prove basic properties, mostly showing that Cayley graphs of free groups are trees and
that Cayley graphs of trees (with an additional condition on the generating set) represent
free groups.

Follows Clara Löh's Geometric Group Theory chapter 3.
-/

structure CayleyGraph (G : Type*) [Group G] (S : Set G) where
  h : 1 ∉ S

namespace CayleyGraph

section

variable {G : Type*} [Group G] {S : Set G} (CG : CayleyGraph G S)

def Graph : SimpleGraph G where
  Adj x y := x * y⁻¹ ∈ S ∨ y * x⁻¹ ∈ S
  symm _ _ h := Or.symm h
  loopless _ := by simp [CG.h]

theorem adj_iff {x y} : CG.Graph.Adj x y ↔ x * y⁻¹ ∈ S ∨ y * x⁻¹ ∈ S := by
  constructor <;> exact id

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
  constructor
  · rintro ⟨h⟩
    exact ⟨_, by simp_all [walk_darts_mul_mem h], walk_darts_map_prod_eq h⟩
  · rintro ⟨L, hL₁, hL₂⟩
    refine SimpleGraph.Walk.reachable ?_
    induction L generalizing v w with
    | nil =>
        rw [eq_mul_inv_iff_mul_eq] at hL₂
        simp only [← hL₂, List.prod_nil, one_mul]
        exact SimpleGraph.Walk.nil' w
    | cons head tail ih =>
        refine SimpleGraph.Walk.cons' _ (head⁻¹ * v) _ ?_ ?_
        · rcases hL₁ head (by simp) <;> simp_all [← mul_assoc, CG.adj_iff, ← hL₂]
        · exact ih (by simp_all) (by simp [mul_assoc, ← hL₂])

theorem connected_iff : CG.Graph.Connected ↔ Subgroup.closure S = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine Subgroup.eq_top_iff' _ |>.mpr (fun x => ?_)
    have := reachable_iff_exists_list.mp (h.preconnected x 1)
    exact Subgroup.exists_list_of_mem_closure_iff.mpr (by simpa using this)
  · refine { preconnected := fun v w => ?_, nonempty := by use 1 }
    suffices ∀ (u : G), CG.Graph.Reachable 1 u by exact (this v).symm.trans (this w)
    exact fun u => reachable_iff_exists_list.mpr <|
      Subgroup.exists_list_of_mem_closure_iff.mp (by simp [h])

def neighborSetMap (CG : CayleyGraph G S) (v : G) (x : (S ∪ S⁻¹ : Set G)) : CG.Graph.neighborSet v :=
  ⟨x * v, by simp [CG.adj_iff, ← Set.mem_inv, or_comm, ← Set.mem_union, Subtype.coe_prop]⟩

theorem bijective_neighborSetMap (CG : CayleyGraph G S) (v : G) :
    Function.Bijective (neighborSetMap CG v) := by
  let inv : CG.Graph.neighborSet v → (S ∪ S⁻¹ : Set G) := fun x => ⟨x.1 * v⁻¹, by
      have := x.2
      simp_all [SimpleGraph.neighborSet, CG.adj_iff, or_comm]
    ⟩
  apply Set.bijective_iff_bijOn_univ.mpr <| Set.BijOn.mk (by simp) ?_ ?_
  · exact Set.LeftInvOn.injOn (f₁' := inv) <| fun x _ => by simp [neighborSetMap, inv]
  · refine Set.LeftInvOn.surjOn (f := inv) ?_ (by simp)
    exact fun x _ => by simp [neighborSetMap, inv]

theorem neighborSet_ncard (CG : CayleyGraph G S)  (v : G) :
    (CG.Graph.neighborSet v).ncard = (S ∪ S⁻¹).ncard := by
  suffices (CG.Graph.neighborSet v).encard = (S ∪ S⁻¹ : Set G).encard by simp [Set.ncard_def, this]
  have := Set.univ.encard_preimage_of_bijective (bijective_neighborSetMap CG v) |>.symm
  simpa using this

noncomputable instance [Finite S] : CG.Graph.LocallyFinite := by
  intro v
  letI : Finite (S⁻¹ : Set G) := Set.finite_inv.mpr (by assumption)
  exact Set.Finite.fintype <| Finite.ofBijective <| bijective_neighborSetMap CG v

theorem IsRegularOfDegree [Finite S] : CG.Graph.IsRegularOfDegree (S ∪ S⁻¹).ncard := by
  intro v
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, ← Nat.card_eq_card_toFinset,
    Nat.card_coe_set_eq]
  exact neighborSet_ncard CG v

def aux (x : S × Bool) : G := if x.2 then x.1 else x.1⁻¹

theorem walk_of_generator_list {v w : G} (l : List (S × Bool)) (h₁ : (l.map aux).prod = v * w⁻¹) :
    ∃ p : CG.Graph.Walk v w, p.support = (l.map aux).scanr (fun acc e => acc * e) w := by
  induction l generalizing v w with
  | nil =>
      have : v = w := by simp_all [eq_mul_inv_iff_mul_eq]
      subst this
      exact ⟨SimpleGraph.Walk.nil' v, by simp⟩
  | cons head tail ih =>
      have : v = (aux head) * (tail.map aux).prod * w := by symm; simpa [eq_mul_inv_iff_mul_eq] using h₁
      subst this
      obtain ⟨L, hi⟩ := @ih ((tail.map aux).prod * w) w (by simp_all)
      have (L : List G) : List.foldr (fun acc e => acc * e) w L = L.prod * w := by
        induction L <;> simp_all [← mul_assoc]
      have : CG.Graph.Adj ((aux head) * (tail.map aux).prod * w) ((tail.map aux).prod * w) := by
        simp only [aux, ite_mul, CG.adj_iff, mul_inv_rev]
        split <;> simp [← mul_assoc]
      exact ⟨SimpleGraph.Walk.cons' _ _ _ this L, by simp_all⟩

theorem cayleyGraph_isFreeGroup_of_IsTree [DecidableEq S] (h₁ : CG.Graph.IsTree) (h₂ : ∀ s t : S, (s : G) * t ≠ 1) :
    IsFreeGroup G := by
  let ι := fun (x : S) => (x : G)
  refine ⟨⟨S, ⟨⟨MulEquiv.ofBijective (FreeGroup.lift ι) ⟨?_, ?_⟩ |>.symm⟩⟩⟩⟩
  · refine (injective_iff_map_eq_one _).mpr (fun a h => ?_)
    have : (a.toWord.map aux).prod = FreeGroup.lift ι a := by
      suffices (a.toWord.map aux).prod = FreeGroup.lift ι (FreeGroup.mk a.toWord) by
        rw [this, FreeGroup.mk_toWord]
      congr
      funext
      simp only [aux, Bool.ite_eq_cond_iff]
      rfl
    obtain ⟨p, hp⟩ := walk_of_generator_list (v := (FreeGroup.lift ι) a) (w := 1) (CG := CG)
      a.toWord (by simp [this])
    have hlen : p.length = a.toWord.length := by
      apply Nat.add_one_inj.mp
      rw [← SimpleGraph.Walk.length_support p, hp]
      induction a.toWord <;> simp_all
    have : p.IsPath := by
      have := p.length_edges
      have := p.length_support
      have : (a.toWord.map aux).length = a.toWord.length := by simp
      apply SimpleGraph.Walk.IsTree.isPath_of_list_chain h₁ p |>.mpr
      by_contra hh
      obtain ⟨n, h', h''⟩ := List.chain'_of_not hh
      have := SimpleGraph.ne_of_adj _ <| List.chain'_getElem (p.chain'_adj_support) n (by omega)
      simp only [this, p.edges_eq_support, Prod.mk.eta, List.getElem_map, List.getElem_zip,
        List.getElem_tail, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, false_and,
        Prod.swap_prod_mk, and_true, false_or, not_not] at h''
      contrapose h''
      simp only [hp]
      repeat rw [List.scanr_getElem (h := by omega), ← List.prod_eq_foldr]
      repeat rw [List.prod_drop_succ (p := by omega)]
      simp only [List.getElem_map, ← mul_assoc, right_eq_mul]
      simp only [aux]
      have : FreeGroup.IsReduced a.toWord := FreeGroup.isReduced_toWord
      simp only [FreeGroup.IsReduced] at this
      have hword_reduced := List.chain'_getElem this n (by omega)
      have := h₂ (a.toWord[n + 1].1) (a.toWord[n].1)
      split <;> split
      · simp [mul_inv_eq_one, inv_eq_iff_mul_eq_one, this]
      · simp only [inv_inv, inv_mul_eq_one, ne_eq]
        simp only [Bool.false_eq_true, imp_false, *] at hword_reduced
        exact Subtype.coe_ne_coe.mpr fun a_1 => hword_reduced a_1.symm
      · simp only [inv_inv, mul_inv_eq_one, ne_eq]
        simp only [Bool.true_eq_false, imp_false, *] at hword_reduced
        exact Subtype.coe_ne_coe.mpr fun a_1 => hword_reduced a_1.symm
      · simp [this]
    refine FreeGroup.toWord_eq_nil_iff.mp ?_
    obtain ⟨_, _, hpath⟩ := h₁.existsUnique_path ((FreeGroup.lift ι) a) 1
    have := hpath p this
    rw [← hpath (SimpleGraph.Walk.nil.copy h.symm rfl) (by simp)] at this
    simp [List.eq_nil_iff_length_eq_zero, ← hlen, this]
  · rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure, Subtype.range_val]
    exact connected_iff.mp h₁.isConnected

end

section

variable {S : Type*} [DecidableEq S] {CG : CayleyGraph (FreeGroup S) (Set.range FreeGroup.of)}
variable {v w : FreeGroup S} (p : CG.Graph.Walk v w)

noncomputable
def gens_of_walk : List (S × Bool) :=
  p.darts.map (fun d => (d.toProd.1 * d.toProd.2⁻¹).toWord[0]'(by
    suffices (d.toProd.1 * d.toProd.2⁻¹).toWord.length ≠ 0 by omega
    simp [mul_inv_eq_one]
  ))

theorem gens_of_walk_length : (gens_of_walk p).length = p.length := by simp [gens_of_walk]

theorem freeGroup_mk_gens_of_walk_index (n : ℕ) (h : n + 1 < p.support.length) :
    FreeGroup.mk [(gens_of_walk p)[n]'(by simp_all [gens_of_walk, p.length_support])] = (p.getVert n) * (p.getVert (n + 1))⁻¹ := by
  simp only [gens_of_walk, List.getElem_map, p.darts_toProd_eq]
  have := p.drop n |>.adj_snd (by simp_all [p.length_support, SimpleGraph.Walk.not_nil_iff_lt_length])
  simp only [SimpleGraph.Walk.drop_getVert, CG.adj_iff, Set.mem_range, FreeGroup.of] at this
  rcases this with ⟨_, yh⟩ | ⟨_, yh⟩
  · simp [← yh, FreeGroup.toWord_mk]
  · rw [eq_mul_inv_iff_mul_eq] at yh
    simp [← yh, FreeGroup.invRev]

theorem freeGroup_mk_sublist (n : ℕ) (h : n < p.support.length) :
    FreeGroup.mk ((gens_of_walk p).take n) = v * (p.getVert n)⁻¹ := by
  induction n with
  | zero => simp [FreeGroup.one_eq_mk]
  | succ n ih =>
      rw [List.take_add, List.take_one_drop_eq_of_lt_length (by simp_all [gens_of_walk, p.length_support]), ← FreeGroup.mul_mk, ih (by omega)]
      simp only [List.get_eq_getElem]
      rw [freeGroup_mk_gens_of_walk_index _ _ (by omega)]
      simp [← mul_assoc]

theorem freeGroup_mk_gens_of_walk :
    FreeGroup.mk (gens_of_walk p) = v * w⁻¹ := by
  have := freeGroup_mk_sublist p p.length (by simp [p.length_support])
  simp only [SimpleGraph.Walk.getVert_length] at this
  simp [← this, ← gens_of_walk_length p]

theorem cayleyGraph_IsTree_of_freeGroup (CG : CayleyGraph (FreeGroup S) (Set.range FreeGroup.of)) :
    CG.Graph.IsTree where
  isConnected := connected_iff.mpr <| FreeGroup.closure_range_of S
  IsAcyclic := by
    intro v p hh
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def] at hh
    have hnil : ¬p.Nil := by
      have := hh.2.1
      contrapose! this
      exact SimpleGraph.Walk.nil_iff_eq_nil.mp this
    have := gens_of_walk_length p
    have : FreeGroup.IsReduced (gens_of_walk p) := by
      have := p.length_edges
      have := p.length_support
      by_contra hh'
      obtain ⟨n, hl₁, hl₂⟩ := FreeGroup.exists_of_not_reduced hh'
      apply List.chain'_getElem (List.Pairwise.chain' hh.1) n (by omega)
      have := SimpleGraph.ne_of_adj _ <| List.chain'_getElem (p.chain'_adj_support) n (by omega)
      simp only [p.edges_eq_support, Prod.mk.eta, List.getElem_map, List.getElem_zip,
        List.getElem_tail, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, this, false_and,
        Prod.swap_prod_mk, and_true, false_or]
      rw [← p.getVert_eq_support_getElem (by omega), ← p.getVert_eq_support_getElem (by omega)]
      have := freeGroup_mk_sublist p n (by omega)
      simp only [hl₂, freeGroup_mk_sublist p (n + 2) (by omega), mul_right_inj, inv_inj] at this
      simp [← this]
    let word := FreeGroup.mk (gens_of_walk p)
    have hword : word.toWord = (gens_of_walk p) := by
      simp [word, FreeGroup.isReduced_iff_reduce_eq.mp this]
    have : word.toWord.length ≠ 0 := by
      rw [hword]
      have := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
      omega
    apply this
    have := freeGroup_mk_gens_of_walk p
    rw [mul_inv_cancel, ← hword, FreeGroup.mk_toWord] at this
    simp [this]

end

end CayleyGraph

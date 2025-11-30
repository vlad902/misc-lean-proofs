import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.FreeGroup.Reduce

-- TODO: PR 3 lemmas below
namespace FreeGroup
variable {α : Type u}

variable {L L₁ L₂ : List (α × Bool)}

theorem exists_of_not_reduced [DecidableEq α] (h : ¬IsReduced L) : ∃ n, n + 1 < L.length ∧ FreeGroup.mk (L.take n) = FreeGroup.mk (L.take (n + 2)) := by
  obtain ⟨n, hn₁, hn₂⟩ := List.exists_not_getElem_of_not_isChain h
  refine ⟨n, by omega, ?_⟩
  conv => rhs; rw [← reduce.self, List.take_add, ← reduce_append_reduce_reduce, reduce.self]
  repeat rw [← List.getElem_cons_drop (by omega), List.take_succ_cons]
  simp only [List.take_zero, reduce.cons, reduce_nil]
  split <;> simp_all [reduce.self]

end FreeGroup

namespace Submonoid

theorem exists_list_of_mem_closure_iff [Monoid M] {s : Set M} {x : M} :
    x ∈ closure s ↔ ∃ l : List M, (∀ y ∈ l, y ∈ s) ∧ l.prod = x := by
  refine ⟨fun hx ↦ ?_, fun ⟨l, hl₁, hl₂⟩ ↦ ?_⟩
  · rwa [← SetLike.mem_coe, closure_eq_image_prod, Set.mem_image] at hx
  · rw [← hl₂]
    exact list_prod_mem (closure s) <| fun x hx ↦ mem_closure.mpr fun _ a ↦ a (hl₁ x hx)

end Submonoid

namespace Subgroup

theorem exists_list_of_mem_closure_iff {G : Type*} [Group G] {s : Set G} {x : G} :
    x ∈ closure s ↔ ∃ l : List G, (∀ y ∈ l, y ∈ s ∨ y⁻¹ ∈ s) ∧ l.prod = x := by
  rw [← mem_toSubmonoid, closure_toSubmonoid]
  exact Submonoid.exists_list_of_mem_closure_iff

end Subgroup

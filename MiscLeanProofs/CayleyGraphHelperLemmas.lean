import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.FreeGroup.Reduce

-- #25812
lemma List.chain'_getElem {α : Type u} {R : α → α → Prop} {l : List α} (h : List.Chain' R l) (n : ℕ) (h' : n + 1 < l.length) :
    R l[n] l[n+1] :=
  List.chain'_pair.mp <| List.Chain'.infix h ⟨l.take n, l.drop (n + 2), by simp⟩

lemma List.chain'_of_not {α : Type u} {R : α → α → Prop} {l : List α} (h : ¬List.Chain' R l) :
    ∃ n : ℕ, ∃ h : n + 1 < l.length, ¬R l[n] l[n+1] := by
  contrapose! h
  induction l with
  | nil => simp
  | cons head tail ih =>
      refine List.chain'_cons'.mpr ⟨fun y yh ↦ ?_, ?_⟩
      · by_cases h' : tail.length = 0
        · simp [List.eq_nil_iff_length_eq_zero.mpr h'] at yh
        · simp only [head?_eq_getElem?, Option.mem_def] at yh
          obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp yh
          have := h 0 (by rw [List.length_cons]; omega)
          rwa [List.getElem_cons_zero] at this
      · refine ih (fun n h' ↦ ?_)
        have := h (n + 1) (by rw [List.length_cons]; omega)
        simpa using this

-- TODO: PR 3 lemmas below
namespace FreeGroup
variable {α : Type u}

variable {L L₁ L₂ : List (α × Bool)}

theorem exists_of_not_reduced [DecidableEq α] (h : ¬IsReduced L) : ∃ n, n + 1 < L.length ∧ FreeGroup.mk (L.take n) = FreeGroup.mk (L.take (n + 2)) := by
  obtain ⟨n, hn₁, hn₂⟩ := List.chain'_of_not h
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
    exact list_prod_mem (closure s) <| fun x hx ↦ mem_closure.mpr fun S a ↦ a (hl₁ x hx)

end Submonoid

namespace Subgroup

theorem exists_list_of_mem_closure_iff {G : Type*} [Group G] {s : Set G} {x : G} :
    x ∈ closure s ↔ ∃ l : List G, (∀ y ∈ l, y ∈ s ∨ y⁻¹ ∈ s) ∧ l.prod = x := by
  rw [← mem_toSubmonoid, closure_toSubmonoid]
  exact Submonoid.exists_list_of_mem_closure_iff

end Subgroup

namespace SimpleGraph.Walk

-- #26720
theorem darts_toProd_eq {V : Type u} {G : SimpleGraph V} {v w : V} {p : G.Walk v w} (n : ℕ) (h : n < p.darts.length) :
    p.darts[n].toProd = (p.getVert n, p.getVert (n + 1)) := by
  rw [p.length_darts] at h
  repeat rw [p.getVert_eq_support_getElem (by omega)]
  ext
  · by_cases h' : n = 0
    · simp [h', List.getElem_zero]
    · have := List.chain'_getElem p.chain'_dartAdj_darts (n - 1) (by omega)
      simp only [DartAdj, show n - 1 + 1 = n by omega] at this
      simp [← p.cons_map_snd_darts, List.getElem_cons, ← this, h']
  · simp [← p.cons_map_snd_darts]

theorem edges_eq_support {V : Type u} {G : SimpleGraph V} {v w : V} {p : G.Walk v w} :
    p.edges = (p.support.zip p.support.tail).map (fun x => s(x.1, x.2)) := by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]

-- #25814
theorem IsPath.eq_snd_of_mem_edges {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} (hp : p.IsPath) (hnil : ¬p.Nil) (hw : s(u, w) ∈ p.edges) : w = p.snd := by
  rw [← SimpleGraph.Walk.cons_tail_eq _ hnil] at hw
  simp only [edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff'] at hw
  rcases hw with h | h
  · rcases h <;> simp_all
  · have : u ∉ p.tail.support := by induction p <;> simp_all
    simp [SimpleGraph.Walk.fst_mem_support_of_mem_edges _ h] at this

theorem IsPath.eq_penultimate_of_mem_edges {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} (hp : p.IsPath) (hnil : ¬p.Nil) (hw : s(v, w) ∈ p.edges) : w = p.penultimate := by
  have := (isPath_reverse_iff p).mpr hp |>.eq_snd_of_mem_edges (w := w)
  simp_all

theorem IsTree.isPath_of_list_chain {V : Type u} {G : SimpleGraph V} (hG : G.IsTree) {v w : V} (p : G.Walk v w) :
    p.IsPath ↔ List.Chain' (fun x y => x ≠ y) p.edges := by
  classical
  constructor
  · intro hP
    rw [isPath_def] at hP
    exact List.Pairwise.chain' <| edges_nodup_of_support_nodup <| hP
  · intro hL
    induction p with
    | nil => simp
    | cons head tail ih =>
        rename_i u' v' w'
        rw [edges_cons] at hL
        have hcc := List.chain'_cons'.mp hL
        refine (cons_isPath_iff head tail).mpr ⟨ih hcc.2, ?_⟩
        rcases tail.length.eq_zero_or_pos with h' | h'
        · simp [SimpleGraph.Walk.nil_iff_support_eq.mp (nil_iff_length_eq.mpr h'), head.ne]
        · by_contra hh
          apply hG.IsAcyclic (cons head (tail.takeUntil u' hh))
          have : (cons head (tail.takeUntil u' hh)).support.tail.Nodup := by
            have : (tail.takeUntil u' hh).support <:+: tail.support :=
              ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← support_append]⟩
            exact tail.isPath_def.mp (ih hcc.2) |>.sublist this.sublist
          simp only [isCycle_def, isTrail_def, edges_cons, List.nodup_cons]
          refine ⟨⟨?_, edges_nodup_of_support_nodup this⟩, ⟨by simp, this⟩⟩
          by_contra hhh
          rw [Sym2.eq_swap] at hhh
          have := IsPath.eq_snd_of_mem_edges (IsPath.mk' this) (by simp [head.ne.symm]) hhh
          rw [snd_takeUntil head.ne] at this
          refine hcc.1 s(u', v') ?_ rfl
          rw [← tail.cons_tail_eq (by rw [not_nil_iff_lt_length]; omega)]
          simp [this]

theorem IsTree.isPath_of_isTrail {V : Type u} {G : SimpleGraph V} (hG : G.IsTree) {v w : V} (p : G.Walk v w)
    (h : p.IsTrail) : p.IsPath := by
  rw [isTrail_def] at h
  exact IsTree.isPath_of_list_chain hG p |>.mpr <| List.Pairwise.chain' h

end SimpleGraph.Walk

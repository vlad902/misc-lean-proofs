-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/golf.20request.3A.20Topologist's.20sine.20curve/with/504284804

import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Rify

open Real Filter Topology

noncomputable abbrev fn (x : ℝ) : ℝ × ℝ := ⟨x, sin x⁻¹⟩
abbrev fn_domain := Set.Ioi (0 : ℝ)
abbrev curve := fn '' fn_domain ∪ {0}

-- TODO: Come back to Jireh's comment on filters and try to plumb this through
lemma filter_sine_diverges (y : ℝ) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : ∃ᶠ x in 𝓝[>] 0, sin x⁻¹ = y := by
  apply Filter.frequently_map (m := (·⁻¹)) (P := (sin · = y)) |>.mp
  simp only [Filter.map_inv, inv_nhdsGT_zero, frequently_atTop]
  intro a
  obtain ⟨n, hn⟩ := exists_nat_gt a
  use arcsin y + n * (2 * Real.pi) + (2 * Real.pi)
  constructor
  · have := Real.monotone_arcsin hy₁
    simp only [arcsin_neg, arcsin_one] at this
    nlinarith [Real.pi_gt_d2]
  · simp [sin_arcsin' ⟨hy₁, hy₂⟩]

lemma sine_diverges (x y : ℝ) (hx : x > 0) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    ∃ z : ℝ, (0 < z ∧ z < x) ∧ sin z⁻¹ = y := by
  obtain ⟨n, hn⟩ := exists_nat_gt x⁻¹
  use (arcsin y + n * (2 * Real.pi))⁻¹
  constructor
  · have := Real.monotone_arcsin hy₁
    simp only [arcsin_neg, arcsin_one] at this
    have : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.cast_pos.mp <| lt_trans (inv_pos_of_pos hx) hn
    constructor
    · apply inv_pos.mpr
      nlinarith [Real.pi_gt_d2]
    · apply inv_lt_of_inv_lt₀ hx
      nlinarith [Real.pi_gt_d2]
  · simp [sin_arcsin' ⟨hy₁, hy₂⟩]

theorem connected : IsConnected curve := by
  refine IsConnected.subset_closure ?_ Set.subset_union_left ?_
  · apply isConnected_Ioi.image fn <| continuousOn_id.prodMk <| ContinuousOn.mono (s := {0}ᶜ) ?_ ?_
    · exact Real.continuousOn_sin.comp' continuousOn_inv₀ (Set.mapsTo'.mpr fun _ x ↦ x)
    · simp
  · refine Set.union_subset subset_closure <| Set.singleton_subset_iff.mpr <| mem_closure_iff.mpr ?_
    intro s hopen hmem
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
    obtain ⟨x, hx₁, hx₂⟩ := sine_diverges ε 0 hε (by simp) (by simp)
    use ⟨x, sin x⁻¹⟩
    suffices (x, sin x⁻¹) ∈ s by simp [hx₁, this]
    apply hball
    simp [abs_lt, hx₁, hx₂, show -ε < x by linarith]

-- TODO: Instead def a structure NormalizedPath and return that
-- TODO: generalize? does mathlib need something to simplify a curve?
lemma normalize_path {X : Type*} [TopologicalSpace X] [T1Space X] {x y : X} {F : Set X}
    (joined : JoinedIn F x y) (h : x ≠ y) : ∃ p : Path x y, (∀ i, p i ∈ F) ∧ ∀ i > 0, p i ≠ x := by
  obtain ⟨path, path_mem⟩ := joined
  let xSup := sSup (path ⁻¹' {x})
  have xSup_mem : xSup ∈ (path ⁻¹' {x}) :=
    IsClosed.sSup_mem ⟨0, by simp⟩ <| IsClosed.preimage path.continuous isClosed_singleton
  have (i : unitInterval) : (xSup : ℝ) + i * (1 - xSup) ∈ unitInterval := by
    constructor
    · nlinarith [xSup.property.1, i.property.1, unitInterval.one_minus_nonneg xSup]
    · nlinarith [unitInterval.le_one i, unitInterval.le_one xSup]
  use {
    toFun := fun i ↦ path ⟨xSup + i * (1 - xSup), this i⟩
    continuous_toFun := by fun_prop
    source' := by simpa [xSup_mem]
    target' := by simp
  }
  constructor
  · simp [path_mem]
  · intro i hi
    simp only [Path.coe_mk_mk, ne_eq]
    by_contra hh
    suffices xSup = 1 by simp [this, Ne.symm h] at xSup_mem
    have : ⟨(xSup : ℝ) + i * (1 - xSup), this i⟩ ∈ path ⁻¹' {x} := by simp [hh]
    have : (xSup : ℝ) + i * (1 - xSup) ≤ xSup := le_sSup (this)
    apply Set.Icc.coe_eq_one.mp
    nlinarith [unitInterval.one_minus_nonneg xSup, this, show 0 < (i : ℝ) from hi]

lemma curve₁_zero_lt {x : ℝ × ℝ} (h₁ : x ∈ curve) (h₂ : 0 < x.1) : x = (x.1, sin (x.1)⁻¹) := by
  simp only [fn,Set.union_singleton, Set.mem_insert_iff, Set.mem_image] at h₁
  rcases h₁ with h | ⟨y, ⟨hy₁, hy₂⟩⟩
  · exfalso
    have : x.1 = 0 := (Prod.ext_iff.mp h).1
    linarith
  · have : y = x.1 ∧ sin y⁻¹ = x.2 := Prod.ext_iff.mp hy₂
    apply Prod.ext <;> simp [← this.2, this.1]

lemma curve_values : ∀ p ∈ curve, p = 0 ∨ 0 < p.1 := by simp_all

theorem not_path_connected : ¬IsPathConnected curve := by
  by_contra hpconn
  have := hpconn.joinedIn (0, 0) (by simp) (1, sin 1) (by simp)
  obtain ⟨path, path_mem, hpath⟩ := normalize_path this (by simp [Prod.ext_iff])
  obtain ⟨δ, hδ₁, hδ₂⟩ := Metric.continuous_iff.mp path.continuous 0 1 Real.zero_lt_one
  let δstep : unitInterval := ⟨δ/2 ⊓ 1, by
    simp only [Set.mem_Icc, le_inf_iff, zero_le_one, and_true, inf_le_right]; linarith⟩
  have δstep_gt : 0 < δstep := by simp [δstep, Subtype.mk_lt_mk.mpr, hδ₁]
  have path_δstep_gt_zero : 0 < (path δstep).1 := by
    rcases curve_values (path δstep) (path_mem δstep) with h | h
    · exact False.elim (hpath δstep δstep_gt h)
    · exact h
  obtain ⟨x, hx₁, hx₂⟩ := sine_diverges (path δstep).1 1 path_δstep_gt_zero (by simp) (by simp)
  have : ∃ xinv, (0 < xinv ∧ xinv < δstep) ∧ (path xinv).1 = x := by
    have := intermediate_value_Ioo (le_of_lt δstep_gt) <|
      (continuous_fst.comp path.continuous).continuousOn
    simp only [Function.comp_apply, path.source] at this
    exact this hx₁
  obtain ⟨xinv, hxinv₁, hxinv₂⟩ := this
  have dist_xinv : dist xinv 0 < δ := by
    have : xinv < δ := lt_trans (Set.mem_Ioo.mp hxinv₁).2 (by simp [δstep, hδ₁])
    simp [dist, abs_of_nonneg, le_of_lt, Set.mem_Ioo.mp hxinv₁, this]
  have path_xinv := curve₁_zero_lt (path_mem xinv) (by simp [hxinv₂, hx₁])
  rw [hxinv₂, hx₂] at path_xinv
  specialize hδ₂ xinv dist_xinv
  simp [dist, path_xinv] at hδ₂

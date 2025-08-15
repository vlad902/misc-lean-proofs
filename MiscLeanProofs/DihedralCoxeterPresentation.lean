import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralCoxeterPresentation

open DihedralGroup

inductive generators
| a -- sr 1
| b -- sr 1 * r 1 (= sr 2 if n > 2)

open generators in
def rels (n : ℕ) : Set (FreeGroup generators) := { .of a^2, .of b^2 , (.of a * .of b)^n }
abbrev dihedralPresentation (n : ℕ) := PresentedGroup (rels n)

abbrev a {n : ℕ} : dihedralPresentation n := .of (generators.a)
abbrev b {n : ℕ} : dihedralPresentation n := .of (generators.b)
abbrev r {n : ℕ} := (@a n) * b

@[simp]
theorem a_mul_a {n : ℕ} : (@a n) * a = 1 := by
  refine PresentedGroup.mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure ?_
  simp [rels, sq]

@[simp]
theorem b_mul_b {n : ℕ} : (@b n) * b = 1 := by
  refine PresentedGroup.mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure ?_
  simp [rels, sq]

@[simp]
theorem a_inv_eq_a {n : ℕ} : (@a n)⁻¹ = a := by
  simp [inv_eq_iff_mul_eq_one]

@[simp]
theorem b_inv_eq_b {n : ℕ} : (@b n)⁻¹ = b := by
  simp [inv_eq_iff_mul_eq_one]

theorem r_pow_n {n : ℕ} : (@r n)^n = 1 := by
  refine PresentedGroup.mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure ?_
  simp [rels, sq]

theorem abx_a_aby {n : ℕ} {x y : ℤ} :
    (@r n)^x * a * r^y = a * r^(y-x) := by
  refine inv_mul_eq_iff_eq_mul.mp <| eq_of_mul_inv_eq_one ?_
  rw [a_inv_eq_a, ← mul_assoc, ← zpow_neg, neg_sub, mul_assoc, ← zpow_add, add_sub_cancel]
  suffices (@a n) * ((a * b) ^ x * a * (a * b) ^ x) = 1 by simpa [← mul_assoc] using this
  induction x with
  | zero => simp
  | succ i _ =>
    suffices (@a n) * ((a*b) ^ i * ((a*b) * a * (a*b)) * (a*b) ^ i) = 1 by
      nth_rw 2 [add_comm]
      simpa [← mul_assoc, zpow_add] using this
    suffices ((@a n)*b) * a * (a*b) = a by simp_all
    suffices (@a n) * b * a * (a * b) = a * (b * (a * a) * b) by simp [this]
    repeat rw [mul_assoc]
  | pred i _ =>
    suffices (@a n) * (((a*b) ^ i)⁻¹ * ((a*b)⁻¹ * a * (a*b)⁻¹) * ((a*b) ^ i)⁻¹) = 1 by
      nth_rw 2 [neg_sub_comm]
      simpa [← mul_assoc, zpow_sub] using this
    simp only [mul_inv_rev, b_inv_eq_b, inv_mul_cancel_right, ← mul_assoc, one_mul, b_mul_b]
    simp_all [← mul_assoc]

theorem word_eq {n : ℕ} (x : dihedralPresentation n) :
    ∃ z : ℤ, x = r^z ∨ x = a * r^(z-1) := by
  apply PresentedGroup.induction_on x <| fun z ↦ ?_
  induction z using FreeGroup.induction_on with
  | C1 => use 0; simp
  | of x =>
    rcases x
    · use 1; right; simp only [sub_self, zpow_zero, mul_one]; rfl
    · use 2; right; simp only [Int.reduceSub, zpow_one, ← mul_assoc, a_mul_a, one_mul]; rfl
  | inv_of x h =>
    rcases h with ⟨m, (h | h)⟩
    · use -m; simp [h]
    · use m; simp [h, inv_mul_eq_iff_eq_mul, ← mul_assoc, abx_a_aby]
  | mul x y hx hy =>
    rcases hx, hy with ⟨⟨mx, (h₁ | h₁)⟩, ⟨my, (h₂ | h₂)⟩⟩
    · use mx+my; simp [h₁, h₂, zpow_add]
    · use my-mx; simp [h₁, h₂, ← mul_assoc, abx_a_aby, tsub_right_comm]
    · use mx+my; simp [h₁, h₂, ← zpow_add, mul_assoc, ← zpow_add, sub_add_eq_add_sub]
    · use my-mx; simp [h₁, h₂, ← mul_assoc, abx_a_aby, mul_assoc _ (_ ^ (mx - 1))]

def mulEquivDihedralGroup {n : ℕ} : dihedralPresentation n ≃* DihedralGroup n where
  toFun :=
    PresentedGroup.toGroup (f := fun | .a => .sr 1 | .b => .sr 1 * .r 1)
      (by rintro _ (_ | (_ | _)) <;> simp_all [sq])
  invFun
    | .r j => r^(j.cast : Int)
    | .sr j => a * r^((j.cast : Int) - 1)
  left_inv := by
    intro x
    obtain ⟨y, (h | h)⟩ := word_eq x <;> simp [h, ZMod.coe_intCast]
    · exact Eq.symm (zpow_eq_zpow_emod' y r_pow_n)
    · apply mul_left_inj r |>.mp
      simp only [mul_zpow_self, sub_add_cancel]
      exact Eq.symm (zpow_eq_zpow_emod' y r_pow_n)
  right_inv := by rintro (x | x) <;> simp
  map_mul' _ _ := by simp

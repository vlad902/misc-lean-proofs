import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralPresentation

inductive generators
| s | r

open generators in
def rels (n : ℕ) : Set (FreeGroup generators) := { .of s^2, .of r^n , .of r * .of s * .of r * .of s }
abbrev dihedralPresentation (n : ℕ) := PresentedGroup (rels n)

abbrev s {n : ℕ} : dihedralPresentation n := .of .s
abbrev r {n : ℕ} : dihedralPresentation n := .of .r

theorem r_n_eq {n : ℕ} : (@r n) ^ n = 1 := by
  refine PresentedGroup.mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure ?_
  simp [rels]

theorem s_s_eq {n : ℕ} : (@s n) * s = 1 := by
  refine PresentedGroup.mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure ?_
  simp [rels, sq]

theorem s_inv_eq {n : ℕ} : (@s n)⁻¹ = s := by
  rw [inv_eq_iff_mul_eq_one, s_s_eq]

theorem rsr {n : ℕ} : r * s * r = (@s n)⁻¹ := by
  refine Eq.symm (inv_eq_of_mul_eq_one_left ?_)
  refine PresentedGroup.mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure ?_
  simp [rels]

theorem rinv_s_rinv {n : ℕ} : r⁻¹ * s * r⁻¹ = (@s n)⁻¹ := by
  simp [mul_inv_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul, ← mul_assoc, s_inv_eq, rsr]

theorem rm_s_rm {n : ℕ} (m : ℤ) : (@r n)^m * s * r^m = s⁻¹ := by
  induction m with
  | hz => simp [s_inv_eq]
  | hp i _ =>
    suffices r ^ i * (r * s * r) * r ^ i = s⁻¹ by
      nth_rw 2 [add_comm]
      simpa [← mul_assoc, zpow_add] using this
    simp_all [rsr, s_inv_eq]
  | hn i _ =>
    suffices (r ^ i)⁻¹ * (r⁻¹ * s * r⁻¹) * (r ^ i)⁻¹ = s⁻¹ by
      nth_rw 2 [neg_sub_comm]
      simpa [← mul_assoc, zpow_sub] using this
    simp_all [rinv_s_rinv, s_inv_eq]

theorem rx_s_ry {n : ℕ} {x y : ℤ} : (@r n)^x * s * r^y = s * r^(y-x) := by
  refine inv_mul_eq_iff_eq_mul.mp <| eq_of_mul_inv_eq_one ?_
  rw [s_inv_eq, ← mul_assoc, ← zpow_neg, neg_sub, mul_assoc, ← zpow_add, add_sub_cancel]
  suffices s * (r ^ x * s * r ^ x) = 1 by simpa [← mul_assoc] using this
  simp [@rm_s_rm n x]

theorem word_equiv {n : ℕ} (x : dihedralPresentation n) : ∃ z : ℤ, x = r^z ∨ x = s * r^z := by
  apply PresentedGroup.induction_on x <| fun z ↦ ?_
  induction z using FreeGroup.induction_on with
  | C1 => use 0; simp
  | Cp x =>
    rcases x
    · use 0; right; simp_all only [zpow_zero, mul_one]; rfl
    · use 1; left; simp_all only [zpow_one]; rfl
  | Ci x h =>
    rcases h with ⟨m, (_ | _)⟩
    · use -m; simp_all
    · use m; simp_all [inv_mul_eq_iff_eq_mul, ← mul_assoc, rm_s_rm]
  | Cm x y hx hy =>
    rcases hx, hy with ⟨⟨mx, (_ | _)⟩, ⟨my, (_ | _)⟩⟩
    · use mx+my; simp_all [zpow_add]
    · use my-mx; simp_all [← mul_assoc, rx_s_ry]
    · use mx+my; simp_all [zpow_add, mul_assoc]
    · use my-mx; simp_all [← mul_assoc, rx_s_ry, mul_assoc _ (r ^ mx), s_s_eq]

def equivDihedralGroup {n : ℕ} : dihedralPresentation n ≃* DihedralGroup n where
  toFun :=
    PresentedGroup.toGroup (f := fun | .s => .sr 0 | .r => .r 1)
      (by rintro _ (_ | (_ | _)) <;> simp_all [sq])
  invFun
    | .r j => r ^ (j.cast : Int)
    | .sr j => s * r ^ (j.cast : Int)
  left_inv := by
    intro x
    obtain ⟨y, (h | h)⟩ := word_equiv x
    all_goals simp [h, ZMod.coe_intCast, Eq.symm (zpow_eq_zpow_emod' y r_n_eq)]
  right_inv := by rintro (x | x) <;> simp
  map_mul' _ _ := by simp

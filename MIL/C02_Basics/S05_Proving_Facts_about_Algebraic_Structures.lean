import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    . show x ⊓ y ⊓ z ≤ x
      trans x ⊓ y
      . apply inf_le_left
      . apply inf_le_left
    . show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      . show x ⊓ y ⊓ z ≤ y
        trans x ⊓ y
        . apply inf_le_left
        . apply inf_le_right
      apply inf_le_right
  . show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    . show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
      . show x ⊓ (y ⊓ z) ≤ x
        apply inf_le_left
      . show x ⊓ (y ⊓ z) ≤ y
        trans y ⊓ z
        . apply inf_le_right
        . apply inf_le_left
    . show x ⊓ (y ⊓ z) ≤ z
      trans y ⊓ z
      . apply inf_le_right
      . apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    . show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      . apply le_sup_left
      trans y ⊔ z
      . apply le_sup_left
      apply le_sup_right
    . show z ≤ x ⊔ (y ⊔ z)
      trans y ⊔ z
      . apply le_sup_right
      apply le_sup_right
  . show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    . show x ≤ x ⊔ y ⊔ z
      trans x ⊔ y
      . apply le_sup_left
      apply le_sup_left
    . show y ⊔ z ≤ x ⊔ y ⊔ z
      apply sup_le
      . trans x ⊔ y
        apply le_sup_right
        apply le_sup_left
      apply le_sup_right

#check inf_comm
#check inf_assoc
#check sup_comm
#check sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  . show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    . apply le_refl
    apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . show x ⊔ x ⊓ y ≤ x
    apply sup_le
    . apply le_refl
    apply inf_le_left
  . show x ≤ x ⊔ x ⊓ y
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b), absorb1, inf_comm (a ⊔ b)]
  show a ⊔ b ⊓ c = a ⊔ c ⊓ (a ⊔ b)
  rw [h, ← sup_assoc, inf_comm c, inf_comm c]
  show a ⊔ b ⊓ c = a ⊔ a ⊓ c ⊔ b ⊓ c
  rw [absorb2]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, ← sup_comm a, absorb2, sup_comm (a ⊓ b)]
  show a ⊓ (b ⊔ c) = a ⊓ (c ⊔ a ⊓ b)
  rw [h, sup_comm c, sup_comm c, ← inf_assoc, absorb1]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self b, sub_eq_add_neg, sub_eq_add_neg]
  show b + -b ≤ b + -a
  apply add_le_add_left
  apply neg_le_neg
  exact h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← neg_add_cancel_left a b, ← add_assoc, ← add_comm a, add_assoc, ← add_comm b]
  show a + 0 ≤ a + (b + -a)
  apply add_le_add_left
  rw [← sub_eq_add_neg]
  exact h

#check le_sub_iff_add_le

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [← zero_add (a * c)]
  apply le_sub_iff_add_le.mp
  rw [← sub_mul]
  apply mul_nonneg
  . show 0 ≤ b - a
    apply sub_nonneg_of_le
    exact h
  exact h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  trans 2 * dist x y / 2
  apply mul_nonneg
  . rw [two_mul]
    rw [← dist_self x]
    nth_rw 3 [dist_comm]
    apply dist_triangle
  . norm_num
  norm_num

variable {Y : Type*} [Semiring Y] [LinearOrder Y] [MulPosStrictMono Y]
variable (a b : Y)

#check (nonneg_of_mul_nonneg_left : (0 ≤ a * b) → (0 < b) → 0 ≤ a)

example (x y : X) : 0 ≤ dist x y := by
  apply nonneg_of_mul_nonneg_right
  . rw [two_mul, ← dist_self x]
    nth_rw 3 [dist_comm]
    show dist x x ≤ dist x y + dist y x
    apply dist_triangle
  norm_num

end

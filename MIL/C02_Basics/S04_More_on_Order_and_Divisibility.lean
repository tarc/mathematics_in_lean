import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  . apply max_le
    . apply le_max_right
    apply le_max_left
  . apply max_le
    . apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . show min (min a b) c ≤ a
      apply le_trans _ (min_le_left a b)
      apply min_le_left
    apply le_min
    . show min (min a b) c ≤ b
      apply le_trans _ (min_le_right a b)
      apply min_le_left
    apply min_le_right
  . show min a (min b c) ≤ min (min a b) c
    apply le_min
    . show min a (min b c) ≤ min a b
      apply le_min
      . apply min_le_left
      apply le_trans _ (min_le_left b c)
      apply min_le_right
    apply le_trans _ (min_le_right b c)
    apply min_le_right

#check max_comm

example : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  . show max (max a b) c ≤ max a (max b c)
    apply max_le
    . show max a b ≤ max a (max b c)
      apply max_le
      . apply le_max_left
      apply le_trans (le_max_left b c)
      apply le_max_right
    apply le_trans (le_max_right b c)
    apply le_max_right
  . show max a (max b c) ≤ max (max a b) c
    apply max_le
    . apply le_trans (le_max_left a b)
      apply le_max_left
    apply max_le
    . apply le_trans (le_max_right a b)
      apply le_max_left
    apply le_max_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    apply add_le_add_right
    apply min_le_left
  . show min a b + c ≤ b + c
    apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm (aux a b c)
  show min (a + c) (b + c) ≤ min a b + c
  apply sub_le_iff_le_add.mp
  apply le_min
  . apply sub_le_iff_le_add.mpr
    apply min_le_left
  apply sub_le_iff_le_add.mpr
  apply min_le_right

#check (add_neg_cancel_right a b : a + b + -b = a)

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm (aux a b c)
  show min (a + c) (b + c) ≤ min a b + c
  nth_rw 2 [← add_neg_cancel_right a c]
  nth_rw 2 [← add_neg_cancel_right b c]
  apply sub_le_iff_le_add.mp
  apply aux

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check (add_sub_cancel_right : ∀ a b : Real, a + b - b = a)
#check (sub_add_cancel : ∀ a b : Real, a - b + b = a)

example : |a| - |b| ≤ |a - b| := by
  apply sub_le_iff_le_add.mpr
  nth_rw 1 [← add_sub_cancel_right a b, add_sub_right_comm]
  apply abs_add

example : |a| - |b| ≤ |a - b| := by
  apply sub_le_iff_le_add.mpr
  nth_rw 1 [← sub_add_cancel a b]
  apply abs_add

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  repeat apply dvd_add
  . apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  . apply dvd_mul_left
  . apply dvd_pow h
    norm_num

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  repeat
    apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left

end

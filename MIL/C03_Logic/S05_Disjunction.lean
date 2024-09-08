import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

#check abs_of_nonneg

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    linarith
  . rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  . rw [abs_of_nonneg h]
    apply add_le_add
    apply le_abs_self
    apply le_abs_self
  . rw [abs_of_neg h]
    rw [neg_add]
    apply add_le_add
    apply neg_le_abs_self
    apply neg_le_abs_self

#check (iff_self_or : ∀ {a b : Prop}, (a ↔ a ∨ b) ↔ b → a)
#check (iff_or_self : ∀ {a b : Prop}, (b ↔ a ∨ b) ↔ a → b)
#check (iff_comm : ∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a))

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  . rw [abs_of_nonneg h]
    show x < y ↔ x < y ∨ x < -y
    rw [iff_self_or]
    show x < -y → x < y
    intro h'
    linarith
  . rw [abs_of_neg h]
    show x < -y ↔ x < y ∨ x < -y
    rw [iff_or_self]
    show x < y → x < -y
    intro h'
    linarith

#check (iff_and_self : ∀ {p q : Prop}, (p ↔ q ∧ p) ↔ p → q)
#check (iff_self_and : ∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q)
#check neg_lt_neg_iff
#check neg_lt_of_neg_lt
#check inv_lt_inv_iff

attribute [to_additive neg_lt_of_neg_lt_iff] inv_lt'

#check neg_lt_of_neg_lt_iff

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    show x < y ↔ -y < x ∧ x < y
    rw [iff_and_self]
    show x < y → -y < x
    intro h'
    linarith
  . rw [abs_of_neg h]
    show -x < y ↔ -y < x ∧ x < y
    rw [neg_lt_of_neg_lt_iff]
    show -y < x ↔ -y < x ∧ x < y
    rw [iff_self_and]
    intro h'
    linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨ x, y, rfl, rfl ⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by linarith
  rw [← sub_eq_zero, ← add_eq_zero_iff_eq_neg, or_comm]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  exact this

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by linarith
  rw [← sub_eq_zero, ← add_eq_zero_iff_eq_neg, or_comm]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  exact this

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x + y) * (x - y) = 0 := by linarith
  rw [← sub_eq_zero, ← add_eq_zero_iff_eq_neg, or_comm]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  exact h'

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by
    calc
      (x + 1) * (x - 1) = x ^ 2 - 1 := by ring
      _ = 0 := by rw [← h]; ring
  rw [← sub_eq_zero, ← add_eq_zero_iff_eq_neg, or_comm]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  exact this

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x + y) * (x - y) = 0 := by
    calc
      (x + y) * (x - y) = x ^ 2 - y ^ 2 := by ring
      _ = 0 := by rw [← h]; ring
  rw [← sub_eq_zero, ← add_eq_zero_iff_eq_neg, or_comm]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  exact h'

end

section
variable {R : Type*} [Ring R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by
    calc
      (x + 1) * (x - 1) = x ^ 2 - 1 := by rw [mul_sub, add_mul, pow_two]; simp; rw [add_sub_add_comm]; simp
      _ = 0 := by rw [← h]; simp
  rw [← sub_eq_zero, ← add_eq_zero_iff_eq_neg, or_comm]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  exact this

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . show (P → Q) → ¬P ∨ Q
    intro h
    by_cases h' : P
    . right; apply h h'
    . left; assumption
  . rintro (h | h); intro h'; contradiction; intro; assumption

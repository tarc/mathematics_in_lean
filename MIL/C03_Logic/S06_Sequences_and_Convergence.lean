import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Abs

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext u v
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by


  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  apply εpos

section

variable {α : Type*} [LinearOrder α] {a b c : α}

#check (le_of_max_le_left : (h : max a b ≤ c) → a ≤ c)
#check (le_of_max_le_right : (h : max a b ≤ c) → b ≤ c)

end

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n ngemax
  have : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
    congr
    ring
  rw [this]

  show |s n - a + (t n - b)| < ε
  apply lt_of_le_of_lt (abs_add (s n - a) (t n - b))

  show |s n - a| + |t n - b| < ε
  convert add_lt_add (hs n (le_of_max_le_left ngemax)) (ht n (le_of_max_le_right ngemax))

  show ε = ε / 2 + ε / 2
  ring

section
variable {α : Type*} {a b c d : α}
    [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α] [MulPosMono α]
#check (mul_lt_mul_of_le_of_lt_of_pos_of_nonneg :
    (h₁ : a ≤ b) → (h₂ : c < d) → (a0 : 0 < a) → (d0 : 0 ≤ d) → a * c < b * d)
end

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  have acnonneg : ¬|c| = 0 := abs_ne_zero.mpr h
  intro ε εpos
  dsimp

  show ∃ N, ∀ n ≥ N, |c * s n - c * a| < ε

  have εcpos : 0 < ε / |c| := by simp [h, εpos]
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngeNs
  rw [← mul_sub, abs_mul]

  show |c| * |s n - a| < ε

  convert mul_lt_mul_of_le_of_lt_of_pos_of_nonneg (refl |c|) _ acpos (le_of_lt εcpos)
  . show ε = |c| * (ε / |c|)
    rw [← mul_div_assoc, mul_comm]
    simp [*]

  . show |s n - a| < ε / |c|
    exact hs n ngeNs

section
variable {α : Type*} [LinearOrderedAddCommGroup α]
#check (abs_sub_abs_le_abs_sub : (a b : α) → |a| - |b| ≤ |a - b|)
end

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngeN
  apply lt_add_of_sub_left_lt

  show |s n| - |a| < 1

  have : |s n - a| < 1 := by simp [h, ngeN]
  apply lt_of_le_of_lt (abs_sub_abs_le_abs_sub (s n) a) this

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have Bne : ¬B = 0 := by linarith
  have pos₀ : ε / B > 0 := div_pos εpos Bpos

  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngemax
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngemax
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngemax
  simp

  show |s n * t n| < ε

  have slt : |s n| < B := h₀ n ngeN₀
  have tlt : |t n - 0| < ε / B := h₁ n ngeN₁
  simp at tlt
  rw [abs_mul]

  show |s n| * |t n| < ε

  convert smul_lt_smul_of_le_of_lt' _ tlt Bpos _
  . show ε = B • (ε / B)
    rw [← smul_div_assoc]
    simp [*]

  . show |s n| ≤ B
    linarith

  . show 0 ≤ |t n|
    simp [*]

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

#check add_lt_add_of_lt_of_lt

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by apply lt_of_le_of_ne; apply abs_nonneg; intro h; apply abne; apply eq_of_abs_sub_eq_zero; simp [h]
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩

  let N := max Na Nb

  have absa : |s N - a| < |a - b| / 2 := by  apply hNa N (le_max_left _ _)

  have absb : |s N - b| < |a - b| / 2 := by apply hNb N (le_max_right _ _)

  have absasb : |s N - a| + |s N - b| < |a - b| := by
    rw [← add_halves |a - b|]
    convert (add_lt_add_of_lt_of_lt absa absb)

  have  sasbab: |a - b| ≤ |s N - a| + |s N - b| := by rw [abs_sub_comm _ a]; linarith [abs_sub_le a (s N) b]

  have : |a - b| < |a - b| := by
    apply lt_of_le_of_lt sasbab absasb

  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

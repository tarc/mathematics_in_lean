import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . simp only [subset_def]
    intro xfsxv
    intro x xs
    simp
    apply xfsxv
    use x
  . simp only [subset_def]
    intro xsxfv
    rintro y ⟨x, xs, rfl⟩
    apply (xsxfv x xs)

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x
  rintro ⟨x', x's, xeq⟩
  apply h at xeq
  rw [←xeq]
  exact x's

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xs, rfl⟩
  apply xs

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y ys
  simp
  rcases h y with ⟨x, rfl⟩
  use x

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yft
  rcases yft with ⟨x, xs, rfl⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x
  simp
  apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  . use x, xs
  . use x, xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x, ⟨xs, fxeq⟩⟩, ⟨x', ⟨xt, rfl⟩⟩⟩
  apply h at fxeq
  use x'
  rw [fxeq] at xs
  use ⟨xs, xt⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ft⟩
  use x
  constructor
  use xs
  contrapose! ft
  use x
  rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x
  simp

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  . rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  . rintro ⟨x, ⟨xs, xfv⟩, rfl⟩
    constructor
    . use x, xs
    . exact xfv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  simp at fxu
  use ⟨x, xs, rfl⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  simp at fxu
  constructor
  . use x, xs
  exact fxu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  . left
    use x, xs
  . right
    exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  . rintro ⟨x, ⟨i, xai⟩, rfl⟩
    use i, x
  . rintro ⟨i, x, xai, rfl⟩
    use x
    constructor
    . use i, xai
    . rfl

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  rintro ⟨x, h, rfl⟩
  simp at *
  intro i
  use x, (h i)

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases (h i) with ⟨x, _, rfl⟩
  use x
  constructor
  . intro i'
    rcases (h i') with ⟨x', xai', fxeq⟩
    apply injf at fxeq
    rw [fxeq] at xai'
    exact xai'
  . rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext y
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos
  intro x' x'pos
  simp at *
  intro h
  have := rpow_div_two_eq_sqrt 2 xpos
  simp at this
  rw [this]
  have := rpow_div_two_eq_sqrt 2 x'pos
  simp at this
  rw [this]
  simp [h]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos x' x'pos
  simp at *
  intro poweq
  have := sqrt_sq xpos
  rw [← sqrt_sq xpos, ← sqrt_sq x'pos]
  rw [poweq]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  simp
  constructor
  . rintro ⟨x, h, rfl⟩
    simp [*]
  . rintro ypos
    use y^2, pow_two_nonneg y
    rw [sqrt_sq ypos]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y'
  simp
  constructor
  . rintro ⟨y, rfl⟩
    apply pow_two_nonneg y
  . intro y'nn
    use √y'
    apply sq_sqrt y'nn

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

#check dif_pos

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf x
    rw [inverse, dif_pos ⟨x, refl (f x)⟩]
    apply injf
    exact @choose_spec α (fun x => f x = f _) ⟨x, refl (f x)⟩
  . intro linv x x' feq
    rw [← linv x, ← linv x', feq]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro surjf y
    rcases surjf y with ⟨x, rfl⟩
    rw [inverse, dif_pos ⟨x, refl (f x)⟩]
    exact @choose_spec _ (fun x => f x = f _) ⟨x, refl (f x)⟩
  . rintro rinv y
    exact ⟨inverse f y, rinv y⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [← h]
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨xs, xu⟩
  exact ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro  x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  . use xs; left; exact xt
  . use xs; right; exact xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  . use xs
    intro xt
    apply xntu
    left; exact xt
  . intro xu
    apply xntu
    right; exact xu

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _ ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ ⟨xs, xt⟩ => ⟨xt, xs⟩)
      (fun _ ⟨xt, xs⟩ => ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  . rintro ⟨xs, _ | _⟩
    . exact xs
    . exact xs
  . intro xs
    use xs
    left
    exact xs

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  . rintro x (xs | ⟨xs, _⟩) <;> use xs
  . intro x xs
    left; use xs

example (S T : Prop) : T ∨ S ∧ ¬T ↔ T ∨ S:= by
  calc
    T ∨ S ∧ ¬T ↔ (T ∨ S) ∧ (T ∨ ¬T) := by rw [or_and_left]
    _ ↔ T ∨ S := by simp; intro; exact or_not

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  . rintro (⟨xs, _⟩ | xt)
    . left; exact xs
    . right; exact xt
  . rintro (xs | xt)
    . simp; left; exact xs

    . right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . constructor
      . left; exact xs
      . intro xst
        apply xnt
        exact xst.2
    . constructor
      . right; exact xt
      . intro xst
        apply xns
        exact xst.1
  . rintro ⟨ xs | xt, xnst⟩
    . left; use xs; intro xt; apply xnst; exact ⟨xs, xt⟩
    . right; use xt; intro xs; apply xnst; exact ⟨xs, xt⟩

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

#check Nat.Prime.eq_two_or_odd
#check Nat.odd_iff

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro pn twoltn
  apply Nat.Prime.eq_two_or_odd at pn
  rw [Nat.odd_iff]
  rcases pn with (neq2 | odd)
  . rw [neq2] at twoltn; contradiction
  . exact odd

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  have xt : x ∈ t := ssubt xs
  constructor
  . apply h₀ x xt
  . apply h₁ x xt

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, px⟩
  use x
  use ssubt xs

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  constructor
  . -- `s ∪ (⋂ i, A i)  ⊆  ⋂ i, (A i ∪ s)` -- This side holds in general.
    show x ∈ s ∪ ⋂ i, A i → x ∈ ⋂ i, A i ∪ s
    simp only [mem_union, mem_iInter]
    rintro (xs | h) i
    . right; exact xs
    . left; exact h i
  . -- `⋂ i, (A i ∪ s)  ⊆  s ∪ (⋂ i, A i)` -- This side requires classical logic.
    show x ∈ ⋂ i, A i ∪ s → x ∈ s ∪ ⋂ i, A i
    simp only [mem_union, mem_iInter]
    intro h
    by_cases xs : x ∈ s -- `by_cases` introduces classical reasoning.
    . left; exact xs
    . right; intro i
      rcases h i with (xai | _)
      . exact xai
      . contradiction

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  simp
  intro n
  have := Nat.exists_infinite_primes n
  rcases this with ⟨p, ni, pprime⟩
  exact ⟨p, pprime, ni⟩

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end

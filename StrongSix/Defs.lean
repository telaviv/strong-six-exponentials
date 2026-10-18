/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Basic definitions: logarithms of algebraic numbers and the space `L̃`

* `StrongSix.logAlg` : the set `𝓛 = {ℓ ∈ ℂ | exp ℓ is algebraic}` of logarithms of (nonzero)
  algebraic numbers. It is a `ℚ`-vector subspace of `ℂ` (proved later).
* `StrongSix.LTilde` : the `ℚ̄`-vector space `L̃` spanned by `1` and `𝓛`, i.e. the numbers
  `β₀ + β₁ ℓ₁ + ⋯ + βₙ ℓₙ` with `βᵢ` algebraic and `ℓᵢ ∈ 𝓛`.

Main statements (proved in later files):
* `StrongSix.SixExponentials` (Lang 1966, Ramachandra 1968),
* `StrongSix.StrongSixExponentials` (Roy 1992), with `ℚ̄`-linear independence hypotheses.
-/

open Complex

namespace StrongSix

/-- `𝓛`: the complex logarithms of nonzero algebraic numbers. -/
def logAlg : Set ℂ := {ℓ | IsAlgebraic ℚ (exp ℓ)}

/-- `L̃`: the `ℚ̄`-span of `1` and `𝓛`, i.e. numbers `β₀ + Σᵢ βᵢ ℓᵢ` with algebraic `βᵢ` and
`ℓᵢ ∈ 𝓛`. -/
def LTilde : Set ℂ :=
  {z | ∃ (n : ℕ) (β : Fin (n + 1) → ℂ) (ℓ : Fin n → ℂ),
      (∀ i, IsAlgebraic ℚ (β i)) ∧ (∀ i, ℓ i ∈ logAlg) ∧
      z = β 0 + ∑ i, β i.succ * ℓ i}

/-- **Six exponentials theorem** (Lang, Ramachandra). If `x₁, x₂` are `ℚ`-linearly independent
and `y₁, y₂, y₃` are `ℚ`-linearly independent, one of the six numbers `exp (xᵢ yⱼ)` is
transcendental. -/
def SixExponentials : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j, Transcendental ℚ (exp (x i * y j))

/-- Linear independence over the field `ℚ̄` of algebraic numbers (inside `ℂ`). -/
def QbarIndep {n : ℕ} (v : Fin n → ℂ) : Prop :=
  ∀ c : Fin n → ℂ, (∀ i, IsAlgebraic ℚ (c i)) → ∑ i, c i * v i = 0 → ∀ i, c i = 0

/-- **Strong six exponentials theorem** (Roy 1992, Corollary 2). If `x₁, x₂` are linearly
independent over `ℚ̄` and `y₁, y₂, y₃` are linearly independent over `ℚ̄`, one of the six numbers
`xᵢ yⱼ` is not in `L̃`.

(Independence over `ℚ̄` is essential: `L̃` is a `ℚ̄`-vector space, so `x = (1, √2)` and
`y = (log 2, log 3, log 5)` give six products in `L̃`.) -/
def StrongSixExponentials : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), QbarIndep x → QbarIndep y →
    ∃ i j, x i * y j ∉ LTilde

end StrongSix

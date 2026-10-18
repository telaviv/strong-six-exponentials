/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Six exponentials: frequencies, points and the multiplicative identity

For `x : Fin 2 → ℂ`, `y : Fin 3 → ℂ` and natural-number index vectors `k`, `s` we set

  `μ_k = k₀ x₀ + k₁ x₁`,   `γ_s = s₀ y₀ + s₁ y₁ + s₂ y₂`.

* `ℚ`-linear independence of `x` (resp. `y`) makes `k ↦ μ_k` (resp. `s ↦ γ_s`) injective;
* `exp (μ_k γ_s) = ∏ᵢ ∏ⱼ exp (xᵢ yⱼ) ^ (kᵢ sⱼ)`, so the values of the auxiliary function at the
  points `γ_s` are polynomials in the six numbers `exp (xᵢ yⱼ)`;
* elementary size bounds for `μ_k` and `γ_s`.
-/

open Complex Finset

namespace StrongSix.SixExp

/-- Natural-number combination `∑ᵢ kᵢ vᵢ`. -/
def comb {n : ℕ} (v : Fin n → ℂ) (k : Fin n → ℕ) : ℂ := ∑ i, (k i : ℂ) * v i

theorem comb_injective {n : ℕ} {v : Fin n → ℂ} (hv : LinearIndependent ℚ v) :
    Function.Injective (comb v) := by
  intro k k' h
  unfold comb at h
  have h0 : ∑ i, (((k i : ℚ) - (k' i : ℚ)) • v i) = 0 := by
    simp only [Rat.smul_def, Rat.cast_sub, Rat.cast_natCast, sub_mul, Finset.sum_sub_distrib, h,
      sub_self]
  have := Fintype.linearIndependent_iff.mp hv _ h0
  funext i
  have hi := this i
  rw [sub_eq_zero] at hi
  exact_mod_cast hi

theorem exp_comb_mul_comb (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) :
    exp (comb x k * comb y s) = ∏ i, ∏ j, exp (x i * y j) ^ (k i * s j) := by
  unfold comb
  rw [Finset.sum_mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_comb_le {n : ℕ} (v : Fin n → ℂ) (k : Fin n → ℕ) {V : ℝ} (hV : ∀ i, ‖v i‖ ≤ V)
    {N : ℕ} (hk : ∀ i, k i ≤ N) : ‖comb v k‖ ≤ n * N * V := by
  unfold comb
  calc ‖∑ i, (k i : ℂ) * v i‖ ≤ ∑ i, ‖(k i : ℂ) * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (N : ℝ) * V := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul (by exact_mod_cast hk i) (hV i) (norm_nonneg _) (Nat.cast_nonneg _)
    _ = n * N * V := by simp [Finset.card_univ]; ring

end StrongSix.SixExp

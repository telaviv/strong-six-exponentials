/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import StrongSix.Analytic.Schwarz
import StrongSix.Analytic.ExpPoly
import StrongSix.Arith.Liouville

/-!
# The extrapolation step

Let `F = expPoly c μ` with `‖μ i‖ ≤ B`, vanishing on a finite set `Z` of points of norm `≤ r`.
If `ζ` (with `‖ζ‖ ≤ r`) is such that `D • F ζ = σ β` for an algebraic integer `β` of a number
field `K` with `house β ≤ H`, then `F ζ = 0` as soon as

  `D * ((∑ ‖c i‖) * exp (7 B r)) * (1/3) ^ #Z * H ^ ([K:ℚ] - 1) < 1`.

Analytic upper bound: Schwarz on the circle of radius `7r`, where `2r / (7r - r) = 1/3`.
Arithmetic lower bound: Liouville's inequality.
-/

open Complex NumberField

namespace StrongSix

theorem expPoly_eq_zero_of_small {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ)
    {ι : Type*} [Fintype ι] (c μ : ι → ℂ) {B : ℝ} (hB : ∀ i, ‖μ i‖ ≤ B)
    (Z : Finset ℂ) (hZ : ∀ z ∈ Z, expPoly c μ z = 0) {r : ℝ} (hr : 0 < r)
    (hZr : ∀ z ∈ Z, ‖z‖ ≤ r) {ζ : ℂ} (hζ : ‖ζ‖ ≤ r)
    {β : K} (hβ : IsIntegral ℤ β) {D : ℝ} (hD : 0 < D) (hβζ : σ β = D * expPoly c μ ζ)
    {H : ℝ} (hH : house β ≤ H)
    (hsmall : D * ((∑ i, ‖c i‖) * Real.exp (B * (7 * r))) * (1 / 3 : ℝ) ^ Z.card *
      H ^ (Module.finrank ℚ K - 1) < 1) :
    expPoly c μ ζ = 0 := by
  by_contra hne
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hβζ
    exact hne ((mul_eq_zero.mp hβζ.symm).resolve_left (by exact_mod_cast hD.ne'))
  -- analytic upper bound
  set M := (∑ i, ‖c i‖) * Real.exp (B * (7 * r)) with hM
  have hcirc : ∀ w : ℂ, ‖w‖ = 7 * r → ‖expPoly c μ w‖ ≤ M := by
    intro w hw
    have := norm_expPoly_le c μ hB w
    rwa [hw] at this
  have hF : ‖expPoly c μ ζ‖ ≤ M * (1 / 3 : ℝ) ^ Z.card := by
    have h := norm_le_of_zeros (expPoly c μ) (differentiable_expPoly c μ) Z hZ hr.le
      (by linarith : r < 7 * r) hZr hcirc hζ
    have h13 : 2 * r / (7 * r - r) = 1 / 3 := by field_simp; ring
    rwa [h13] at h
  -- arithmetic lower bound
  have hL := one_le_norm_mul_house_pow hβ hβ0 σ
  have hHn : house β ^ (Module.finrank ℚ K - 1) ≤ H ^ (Module.finrank ℚ K - 1) :=
    pow_le_pow_left₀ (house_nonneg _) hH _
  have hσ : ‖σ β‖ ≤ D * (M * (1 / 3 : ℝ) ^ Z.card) := by
    rw [hβζ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le]
    exact mul_le_mul_of_nonneg_left hF hD.le
  have hH0 : 0 ≤ H := (house_nonneg _).trans hH
  have : (1 : ℝ) ≤ D * M * (1 / 3 : ℝ) ^ Z.card * H ^ (Module.finrank ℚ K - 1) := by
    calc (1 : ℝ) ≤ ‖σ β‖ * house β ^ (Module.finrank ℚ K - 1) := hL
      _ ≤ (D * (M * (1 / 3 : ℝ) ^ Z.card)) * H ^ (Module.finrank ℚ K - 1) :=
          mul_le_mul hσ hHn (pow_nonneg (house_nonneg _) _) (by positivity)
      _ = D * M * (1 / 3 : ℝ) ^ Z.card * H ^ (Module.finrank ℚ K - 1) := by ring
  linarith

end StrongSix

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Exponential polynomials

`expPoly c μ z = ∑ i, c i * exp (μ i * z)` for finitely many coefficients `c i` and frequencies
`μ i`. We prove:

* `expPoly` is entire, with an explicit bound `‖expPoly c μ z‖ ≤ (∑ ‖c i‖) * exp (B * ‖z‖)`
  when all `‖μ i‖ ≤ B`;
* **linear independence of exponentials**: if the `μ i` are pairwise distinct and `expPoly c μ`
  vanishes identically, then `c = 0` (via the iterated derivatives at `0` and Vandermonde).
-/

open Complex Finset Matrix

namespace StrongSix

variable {ι : Type*} [Fintype ι]

/-- The exponential polynomial `z ↦ ∑ i, c i * exp (μ i * z)`. -/
noncomputable def expPoly (c μ : ι → ℂ) (z : ℂ) : ℂ := ∑ i, c i * exp (μ i * z)

theorem hasDerivAt_expPoly (c μ : ι → ℂ) (z : ℂ) :
    HasDerivAt (expPoly c μ) (expPoly (fun i => c i * μ i) μ z) z := by
  unfold expPoly
  have : ∀ i ∈ (univ : Finset ι), HasDerivAt (fun z => c i * exp (μ i * z))
      (c i * μ i * exp (μ i * z)) z := by
    intro i _
    have h := ((hasDerivAt_id z).const_mul (μ i)).cexp.const_mul (c i)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa using HasDerivAt.fun_sum this

theorem differentiable_expPoly (c μ : ι → ℂ) : Differentiable ℂ (expPoly c μ) :=
  fun z => (hasDerivAt_expPoly c μ z).differentiableAt

theorem iteratedDeriv_expPoly (c μ : ι → ℂ) (m : ℕ) :
    iteratedDeriv m (expPoly c μ) = expPoly (fun i => c i * μ i ^ m) μ := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [(hasDerivAt_expPoly _ μ z).deriv]
    simp [expPoly, pow_succ, mul_assoc]

theorem iteratedDeriv_zero_function (m : ℕ) : iteratedDeriv m (fun _ : ℂ => (0 : ℂ)) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iteratedDeriv_succ, ih]; funext z; simp

theorem expPoly_zero_arg (c μ : ι → ℂ) : expPoly c μ 0 = ∑ i, c i := by
  simp [expPoly]

/-- **Linear independence of exponentials with distinct frequencies.** -/
theorem eq_zero_of_expPoly_eq_zero {c μ : ι → ℂ} (hμ : Function.Injective μ)
    (h : ∀ z, expPoly c μ z = 0) : c = 0 := by
  classical
  -- transport to `Fin n`
  set n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  set v : Fin n → ℂ := μ ∘ e.symm
  set c' : Fin n → ℂ := c ∘ e.symm
  have hv : Function.Injective v := hμ.comp e.symm.injective
  -- all power sums vanish
  have hsum : ∀ m : ℕ, ∑ i, c' i * v i ^ m = 0 := by
    intro m
    have h0 : expPoly c μ = fun _ => 0 := funext h
    have := congrFun (iteratedDeriv_expPoly c μ m) 0
    rw [h0, iteratedDeriv_zero_function, expPoly_zero_arg, Pi.zero_apply] at this
    have hs : ∑ i, c' i * v i ^ m = ∑ i, c i * μ i ^ m :=
      Equiv.sum_comp e.symm (fun i => c i * μ i ^ m)
    rw [hs, ← this]
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hvec : c' ᵥ* Matrix.vandermonde v = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    exact hsum j
  have hc' : c' = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  funext i
  have := congrFun hc' (e i)
  simpa [c'] using this

/-- Growth bound for an exponential polynomial. -/
theorem norm_expPoly_le (c μ : ι → ℂ) {B : ℝ} (hB : ∀ i, ‖μ i‖ ≤ B) (z : ℂ) :
    ‖expPoly c μ z‖ ≤ (∑ i, ‖c i‖) * Real.exp (B * ‖z‖) := by
  unfold expPoly
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_exp]
  gcongr
  calc (μ i * z).re ≤ ‖μ i * z‖ := re_le_norm _
    _ = ‖μ i‖ * ‖z‖ := norm_mul _ _
    _ ≤ B * ‖z‖ := by gcongr; exact hB i

end StrongSix

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# A Schwarz lemma for entire functions with many zeros

If an entire function `f` vanishes at the points of a finite set `Z` contained in the closed disc
of radius `r`, and `‖f‖ ≤ M` on the circle of radius `R > r`, then on the closed disc of radius `r`

  `‖f z‖ ≤ M * (2 r / (R - r)) ^ #Z`.

This is the analytic upper bound used in every transcendence proof of Schneider type.
-/

open Complex Metric Set Finset

namespace StrongSix

/-- Factor out the zeros: an entire function vanishing on a finite set `Z` is
`∏_{z ∈ Z} (w - z)` times an entire function. -/
theorem exists_entire_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, f z = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ w, f w = (∏ z ∈ Z, (w - z)) * g w := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨f, hf, fun w => by simp⟩
  | insert a Z haZ ih =>
    obtain ⟨g, hg, hfg⟩ := ih (fun z hz => hZ z (Finset.mem_insert_of_mem hz))
    have hga : g a = 0 := by
      have h0 := hfg a
      rw [hZ a (Finset.mem_insert_self a Z)] at h0
      have hprod : (∏ z ∈ Z, (a - z)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro z hz h
        exact haZ (sub_eq_zero.mp h ▸ hz)
      exact (mul_eq_zero.mp h0.symm).resolve_left hprod
    refine ⟨dslope g a, ?_, fun w => ?_⟩
    · have := (differentiableOn_dslope (s := univ) (f := g) (c := a) Filter.univ_mem).mpr
        hg.differentiableOn
      exact fun w => (this w trivial).differentiableAt Filter.univ_mem
    · have h1 : (w - a) • dslope g a w = g w - g a := sub_smul_dslope g a w
      rw [hga, sub_zero, smul_eq_mul] at h1
      rw [hfg w, Finset.prod_insert haZ, ← h1]
      ring

/-- **Schwarz lemma with many zeros.** -/
theorem norm_le_of_zeros (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, f z = 0) {r R M : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hZr : ∀ z ∈ Z, ‖z‖ ≤ r) (hM : ∀ w : ℂ, ‖w‖ = R → ‖f w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ M * (2 * r / (R - r)) ^ Z.card := by
  obtain ⟨g, hg, hfg⟩ := exists_entire_factor f hf Z hZ
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  -- bound for `g` on the circle of radius `R`
  have hgR : ∀ w : ℂ, ‖w‖ = R → ‖g w‖ ≤ M / (R - r) ^ Z.card := by
    intro w hw
    have hlow : (R - r) ^ Z.card ≤ ‖∏ z ∈ Z, (w - z)‖ := by
      rw [norm_prod, ← Finset.prod_const (s := Z)]
      apply Finset.prod_le_prod₀ (fun _ _ => hRr.le)
      intro z hz
      have := norm_sub_norm_le w z
      linarith [hZr z hz]
    have hpos : 0 < ‖∏ z ∈ Z, (w - z)‖ := lt_of_lt_of_le (pow_pos hRr _) hlow
    rw [le_div_iff₀ (pow_pos hRr _)]
    calc ‖g w‖ * (R - r) ^ Z.card ≤ ‖g w‖ * ‖∏ z ∈ Z, (w - z)‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖f w‖ := by rw [hfg w, norm_mul, mul_comm]
      _ ≤ M := hM w hw
  -- maximum modulus principle on the ball of radius `R`
  have hgz : ‖g z‖ ≤ M / (R - r) ^ Z.card := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
      isBounded_ball hg.diffContOnCl
    · intro w hw
      rw [frontier_ball (0 : ℂ) hR.ne'] at hw
      exact hgR w (by simpa using hw)
    · rw [closure_ball (0 : ℂ) hR.ne']
      simpa using hz.trans hrR.le
  -- upper bound for the product at `z`
  have hup : ‖∏ z' ∈ Z, (z - z')‖ ≤ (2 * r) ^ Z.card := by
    rw [norm_prod]
    calc ∏ z' ∈ Z, ‖z - z'‖ ≤ ∏ _z' ∈ Z, (2 * r) := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro z' hz'
          have := norm_sub_le z z'
          linarith [hZr z' hz']
      _ = (2 * r) ^ Z.card := Finset.prod_const _
  calc ‖f z‖ = ‖∏ z' ∈ Z, (z - z')‖ * ‖g z‖ := by rw [hfg z, norm_mul]
    _ ≤ (2 * r) ^ Z.card * (M / (R - r) ^ Z.card) :=
        mul_le_mul hup hgz (norm_nonneg _) (by positivity)
    _ = M * (2 * r / (R - r)) ^ Z.card := by rw [div_pow]; ring

end StrongSix

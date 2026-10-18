/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import StrongSix.SixExp.Setup

/-!
# Six exponentials: the arithmetic side

`K` is a number field containing six numbers `aᵢⱼ` (with `σ aᵢⱼ = exp (xᵢ yⱼ)` for a fixed
embedding `σ`), and `d ≥ 1` is a common denominator: every `d * aᵢⱼ` is an algebraic integer.

* `val a k s = ∏ᵢ ∏ⱼ aᵢⱼ ^ (kᵢ sⱼ)`; its image under `σ` is `exp (μ_k γ_s)`.
* `ival d a E k s = d ^ E * val a k s` written as a manifest algebraic integer when
  `(∑ k)(∑ s) ≤ E`, with `house (ival …) ≤ (d A) ^ E`.
* `siegel_six`: Siegel's lemma produces the coefficients of the auxiliary function.
-/

open Complex Finset NumberField
open private c₁ c₂ c₂_nonneg from Mathlib.NumberTheory.NumberField.House

namespace StrongSix.SixExp

variable {K : Type*} [Field K] [NumberField K]

set_option linter.unusedSectionVars false

/-! ### Submultiplicativity of the house over finite products -/

theorem house_one' : house (1 : K) = 1 := by
  have := house_intCast (K := K) 1
  simpa using this

theorem house_natCast' (n : ℕ) : house (n : K) = n := by
  have := house_intCast (K := K) n
  simpa using this

theorem house_prod_le' {ι : Type*} (s : Finset ι) (g : ι → K) :
    house (∏ i ∈ s, g i) ≤ ∏ i ∈ s, house (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [house_one']
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (house_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (house_nonneg _))

/-! ### Values -/

/-- `v(k, s) = ∏ᵢ ∏ⱼ aᵢⱼ ^ (kᵢ sⱼ)`. -/
def val (a : Fin 2 → Fin 3 → K) (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) : K :=
  ∏ i, ∏ j, a i j ^ (k i * s j)

theorem map_val (σ : K →+* ℂ) {x : Fin 2 → ℂ} {y : Fin 3 → ℂ} {a : Fin 2 → Fin 3 → K}
    (ha : ∀ i j, σ (a i j) = exp (x i * y j)) (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) :
    σ (val a k s) = exp (comb x k * comb y s) := by
  rw [exp_comb_mul_comb, val, map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine prod_congr rfl fun j _ => ?_
  rw [map_pow, ha]

/-- The weight `(∑ᵢ kᵢ)(∑ⱼ sⱼ)`. -/
def wt (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) : ℕ := (∑ i, k i) * (∑ j, s j)

/-- `d ^ E * v(k, s)`, written so that it is visibly an algebraic integer. -/
def ival (d : ℕ) (a : Fin 2 → Fin 3 → K) (E : ℕ) (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) : K :=
  (d : K) ^ (E - wt k s) * ∏ i, ∏ j, ((d : K) * a i j) ^ (k i * s j)

theorem prod_prod_pow_const (c : K) (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) :
    ∏ i, ∏ j, c ^ (k i * s j) = c ^ wt k s := by
  simp only [prod_pow_eq_pow_sum, wt, sum_mul_sum]

theorem ival_eq (d : ℕ) (a : Fin 2 → Fin 3 → K) {E : ℕ} (k : Fin 2 → ℕ) (s : Fin 3 → ℕ)
    (h : wt k s ≤ E) : ival d a E k s = (d : K) ^ E * val a k s := by
  unfold ival val
  simp only [mul_pow, prod_mul_distrib, prod_prod_pow_const]
  rw [← mul_assoc, pow_sub_mul_pow _ h]

theorem ival_integral (d : ℕ) {a : Fin 2 → Fin 3 → K} (hint : ∀ i j, IsIntegral ℤ ((d : K) * a i j))
    (E : ℕ) (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) : IsIntegral ℤ (ival d a E k s) := by
  have hmem : ival d a E k s ∈ integralClosure ℤ K := by
    unfold ival
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ d) _) ?_
    refine Subalgebra.prod_mem _ fun i _ => Subalgebra.prod_mem _ fun j _ => ?_
    exact Subalgebra.pow_mem _ (hint i j) _
  exact hmem

theorem house_ival_le (d : ℕ) (hd : 1 ≤ d) (a : Fin 2 → Fin 3 → K) {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ i j, house (a i j) ≤ A) {E : ℕ} (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) (h : wt k s ≤ E) :
    house (ival d a E k s) ≤ ((d : ℝ) * A) ^ E := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdA : (d : ℝ) ≤ d * A := le_mul_of_one_le_right (by positivity) hA1
  have hdA0 : (0 : ℝ) ≤ d * A := by positivity
  unfold ival
  calc house ((d : K) ^ (E - wt k s) * ∏ i, ∏ j, ((d : K) * a i j) ^ (k i * s j))
      ≤ house ((d : K) ^ (E - wt k s)) * house (∏ i, ∏ j, ((d : K) * a i j) ^ (k i * s j)) :=
        house_mul_le _ _
    _ ≤ (d : ℝ) ^ (E - wt k s) * ∏ i, ∏ j, ((d : ℝ) * A) ^ (k i * s j) := by
        apply mul_le_mul
        · rw [house_pow, house_natCast']
        · refine (house_prod_le' _ _).trans (prod_le_prod₀ (fun _ _ => house_nonneg _) ?_)
          intro i _
          refine (house_prod_le' _ _).trans (prod_le_prod₀ (fun _ _ => house_nonneg _) ?_)
          intro j _
          rw [house_pow]
          refine pow_le_pow_left₀ (house_nonneg _) ?_ _
          refine (house_mul_le _ _).trans ?_
          rw [house_natCast']
          exact mul_le_mul_of_nonneg_left (hA i j) (Nat.cast_nonneg _)
        · exact house_nonneg _
        · positivity
    _ = (d : ℝ) ^ (E - wt k s) * ((d : ℝ) * A) ^ wt k s := by
        congr 1
        simp only [prod_pow_eq_pow_sum, wt, sum_mul_sum]
    _ ≤ ((d : ℝ) * A) ^ (E - wt k s) * ((d : ℝ) * A) ^ wt k s := by
        gcongr
    _ = ((d : ℝ) * A) ^ E := pow_sub_mul_pow _ h

theorem wt_le {L S : ℕ} (k : Fin 2 → Fin L) (s : Fin 3 → Fin S) :
    wt (fun i => (k i : ℕ)) (fun j => (s j : ℕ)) ≤ 6 * L * S := by
  unfold wt
  have hk : ∑ i, ((k i : ℕ)) ≤ 2 * L := by
    calc ∑ i, ((k i : ℕ)) ≤ ∑ _i : Fin 2, L := sum_le_sum fun i _ => (k i).isLt.le
      _ = 2 * L := by simp
  have hs : ∑ j, ((s j : ℕ)) ≤ 3 * S := by
    calc ∑ j, ((s j : ℕ)) ≤ ∑ _j : Fin 3, S := sum_le_sum fun j _ => (s j).isLt.le
      _ = 3 * S := by simp
  calc (∑ i, ((k i : ℕ))) * ∑ j, ((s j : ℕ)) ≤ (2 * L) * (3 * S) := Nat.mul_le_mul hk hs
    _ = 6 * L * S := by ring

/-! ### Siegel's lemma for the six exponentials problem -/

/-- Real-power bound used to simplify Siegel's estimate. -/
theorem rpow_le_one_add {b t : ℝ} (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : b ^ t ≤ 1 + b := by
  rcases le_total b 1 with h | h
  · exact (Real.rpow_le_one hb h ht0).trans (le_add_of_nonneg_right hb)
  · calc b ^ t ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ht1
      _ = b := Real.rpow_one b
      _ ≤ 1 + b := le_add_of_nonneg_left zero_le_one

/-- **Siegel's lemma, specialized.** There is a constant `C ≥ 0` depending only on `K` such that
for all `L, S` with `0 < S` and `2 S³ ≤ L²` there are algebraic integers `ξ_k`, not all zero,
with `∑_k ξ_k v(k, s) = 0` for all `s ∈ [0,S)³` and `house ξ_k ≤ C (1 + C L² (d A)^{6LS})`. -/
theorem siegel_six (d : ℕ) (hd : 1 ≤ d) (a : Fin 2 → Fin 3 → K)
    (hint : ∀ i j, IsIntegral ℤ ((d : K) * a i j)) {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ i j, house (a i j) ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L S : ℕ, 0 < S → 2 * S ^ 3 ≤ L ^ 2 →
      ∃ ξ : (Fin 2 → Fin L) → 𝓞 K, ξ ≠ 0 ∧
        (∀ s : Fin 3 → Fin S,
          ∑ k, (ξ k : K) * val a (fun i => (k i : ℕ)) (fun j => (s j : ℕ)) = 0) ∧
        ∀ k, house (ξ k : K) ≤ C * (1 + C * L ^ 2 * ((d : ℝ) * A) ^ (6 * L * S)) := by
  classical
  refine ⟨c₁ K, ?_, ?_⟩
  · unfold c₁
    exact mul_nonneg (Nat.cast_nonneg _) (c₂_nonneg K)
  intro L S hS hLS
  have hS3 : 0 < S ^ 3 := pow_pos hS 3
  have hL2 : S ^ 3 < L ^ 2 := by omega
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp at hL2
    · exact h
  set E := 6 * L * S with hE
  -- the matrix of the linear system, with algebraic integer entries
  let M : Matrix (Fin 3 → Fin S) (Fin 2 → Fin L) (𝓞 K) := fun s k =>
    ⟨ival d a E (fun i => (k i : ℕ)) (fun j => (s j : ℕ)), ival_integral d hint _ _ _⟩
  have hM0 : M ≠ 0 := by
    intro h
    have h0 := congrFun (congrFun h (fun _ => ⟨0, hS⟩)) (fun _ => ⟨0, hL⟩)
    have h1 : ((M (fun _ => ⟨0, hS⟩) (fun _ => ⟨0, hL⟩) : 𝓞 K) : K) = 0 := by
      rw [h0]; rfl
    simp only [M, ival, wt] at h1
    simp at h1
    omega
  have hcardα : Fintype.card (Fin 3 → Fin S) = S ^ 3 := by simp
  have hcardβ : Fintype.card (Fin 2 → Fin L) = L ^ 2 := by simp
  have hbound : ∀ s k, house ((algebraMap (𝓞 K) K) (M s k)) ≤ ((d : ℝ) * A) ^ E := by
    intro s k
    exact house_ival_le d hd a hA1 hA _ _ (wt_le k s)
  obtain ⟨ξ, hξ0, hMξ, hξb⟩ := house.exists_ne_zero_int_vec_house_le K M hM0 hS3 hL2 hcardβ
    hbound hcardα
  refine ⟨ξ, hξ0, ?_, ?_⟩
  · intro s
    have hs := congrFun hMξ s
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hs
    have hsK := congrArg (algebraMap (𝓞 K) K) hs
    rw [map_sum, map_zero] at hsK
    have hdE : ((d : K) ^ E) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show d ≠ 0 by omega))
    have : (d : K) ^ E * ∑ k, (ξ k : K) * val a (fun i => (k i : ℕ)) (fun j => (s j : ℕ)) = 0 := by
      rw [mul_sum, ← hsK]
      refine sum_congr rfl fun k _ => ?_
      rw [map_mul]
      change _ = ival d a E (fun i => (k i : ℕ)) (fun j => (s j : ℕ)) * (ξ k : K)
      rw [ival_eq d a _ _ (wt_le k s)]
      ring
    exact (mul_eq_zero.mp this).resolve_left hdE
  · intro k
    have hk := hξb k
    have hc : 0 ≤ c₁ K := by unfold c₁; exact mul_nonneg (Nat.cast_nonneg _) (c₂_nonneg K)
    have hp : (0 : ℝ) < S ^ 3 := by exact_mod_cast hS3
    have hqp : (0 : ℝ) < (L ^ 2 : ℕ) - (S ^ 3 : ℕ) := by
      have : (S ^ 3 : ℝ) < (L ^ 2 : ℝ) := by exact_mod_cast hL2
      push_cast; linarith
    have ht0 : (0 : ℝ) ≤ ((S ^ 3 : ℕ) : ℝ) / ((L ^ 2 : ℕ) - (S ^ 3 : ℕ)) := by
      push_cast at hqp ⊢; positivity
    have ht1 : ((S ^ 3 : ℕ) : ℝ) / ((L ^ 2 : ℕ) - (S ^ 3 : ℕ)) ≤ 1 := by
      rw [div_le_one hqp]
      have : (2 * S ^ 3 : ℝ) ≤ (L ^ 2 : ℝ) := by exact_mod_cast hLS
      push_cast; linarith
    have hb0 : 0 ≤ c₁ K * ((L ^ 2 : ℕ) : ℝ) * ((d : ℝ) * A) ^ E := by positivity
    calc house (ξ k : K) ≤ c₁ K * (c₁ K * ((L ^ 2 : ℕ) : ℝ) * ((d : ℝ) * A) ^ E) ^
          (((S ^ 3 : ℕ) : ℝ) / ((L ^ 2 : ℕ) - (S ^ 3 : ℕ))) := hk
      _ ≤ c₁ K * (1 + c₁ K * ((L ^ 2 : ℕ) : ℝ) * ((d : ℝ) * A) ^ E) :=
          mul_le_mul_of_nonneg_left (rpow_le_one_add hb0 ht0 ht1) hc
      _ = c₁ K * (1 + c₁ K * (L : ℝ) ^ 2 * ((d : ℝ) * A) ^ (6 * L * S)) := by push_cast; rfl

end StrongSix.SixExp

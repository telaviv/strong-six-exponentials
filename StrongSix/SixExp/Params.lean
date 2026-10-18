/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Six exponentials: choice of parameters

With `S = n²`, `L = 2n³` and `Hξ = C (1 + C L² G^{6LS})` (Siegel's bound), the smallness
condition of the extrapolation step,

  `G^{6LT} · (L² Hξ · e^{2LX · 7 · 3TY}) · (1/3)^{T³} · (L² Hξ G^{6LT})^{h-1} < 1`,

holds for every `T ≥ n²` once `n` is large (depending on `h, C, G, X, Y` only).
Every exponent other than `T³` is `O(n³ T) = O(T³ / n)`.
-/

open Real

namespace StrongSix.SixExp

/-- `x^m = exp (m log x)` for `x > 0`. -/
theorem pow_eq_exp_mul_log {x : ℝ} (hx : 0 < x) (m : ℕ) : x ^ m = exp (m * log x) := by
  rw [← exp_log (pow_pos hx m), log_pow]

theorem one_third_pow_le_exp_neg (N : ℕ) : (1 / 3 : ℝ) ^ N ≤ exp (-(N : ℝ)) := by
  have h3 : exp 1 ≤ 3 := (exp_one_lt_d9.le).trans (by norm_num)
  rw [exp_neg, ← exp_one_pow, one_div, inv_pow]
  apply inv_anti₀ (pow_pos (exp_pos 1) N)
  exact pow_le_pow_left₀ (exp_pos 1).le h3 N

theorem nat_le_exp (L : ℝ) : L ≤ exp L := by linarith [add_one_le_exp L]

set_option maxHeartbeats 1000000 in
/-- The main parameter inequality. -/
theorem params_exist (h : ℕ) (hh : 1 ≤ h) {C G X Y : ℝ} (hC : 0 ≤ C) (hG : 1 ≤ G)
    (hX : 0 ≤ X) (hY : 1 ≤ Y) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ T : ℕ, n ^ 2 ≤ T →
      G ^ (6 * (2 * n ^ 3) * T) *
          (((2 * n ^ 3 : ℕ) : ℝ) ^ 2 * (C * (1 + C * ((2 * n ^ 3 : ℕ) : ℝ) ^ 2 *
              G ^ (6 * (2 * n ^ 3) * n ^ 2))) *
            exp (2 * ((2 * n ^ 3 : ℕ) : ℝ) * X * (7 * (3 * T * Y)))) *
          (1 / 3 : ℝ) ^ (T ^ 3) *
          (((2 * n ^ 3 : ℕ) : ℝ) ^ 2 * (C * (1 + C * ((2 * n ^ 3 : ℕ) : ℝ) ^ 2 *
              G ^ (6 * (2 * n ^ 3) * n ^ 2))) * G ^ (6 * (2 * n ^ 3) * T)) ^ (h - 1) < 1 := by
  set a : ℝ := 1 + C with ha
  have ha1 : 1 ≤ a := by linarith
  have hG0 : 0 < G := by linarith
  have hlogG : 0 ≤ log G := log_nonneg hG
  have hloga : 0 ≤ log a := log_nonneg ha1
  set κ : ℝ := 4 * h + 12 * h * log G + 42 * X * Y with hκ
  have hκ0 : 0 ≤ κ := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * h * log a + 4 * κ)
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  refine ⟨n, hn1, fun T hT => ?_⟩
  -- abbreviations
  set L : ℕ := 2 * n ^ 3 with hL
  set S : ℕ := n ^ 2 with hS
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have : 1 ≤ L := by rw [hL]; have := Nat.one_le_pow 3 n hn1; omega
    exact_mod_cast this
  have hT1 : (1 : ℝ) ≤ T := by
    have : 1 ≤ T := le_trans (Nat.one_le_pow _ _ hn1) hT
    exact_mod_cast this
  have hST : S ≤ T := hT
  -- Step A: Siegel's bound
  set Hξ : ℝ := C * (1 + C * (L : ℝ) ^ 2 * G ^ (6 * L * S)) with hHξ
  have hGS1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 * G ^ (6 * L * S) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hG)
  have hHξ0 : 0 ≤ Hξ := by positivity
  have hHξ_le : Hξ ≤ a * (a * ((L : ℝ) ^ 2 * G ^ (6 * L * S))) := by
    have h1 : C ≤ a := by linarith
    have h2 : 1 + C * (L : ℝ) ^ 2 * G ^ (6 * L * S) ≤ a * ((L : ℝ) ^ 2 * G ^ (6 * L * S)) := by
      rw [ha]; nlinarith
    exact mul_le_mul h1 h2 (by positivity) (by linarith)
  have hGST : G ^ (6 * L * S) ≤ G ^ (6 * L * T) :=
    pow_le_pow_right₀ hG (Nat.mul_le_mul_left _ hST)
  -- P := a² L⁴ G^{6LT} bounds L² Hξ
  set P : ℝ := a ^ 2 * (L : ℝ) ^ 4 * G ^ (6 * L * T) with hP
  have hLH : (L : ℝ) ^ 2 * Hξ ≤ P := by
    calc (L : ℝ) ^ 2 * Hξ ≤ (L : ℝ) ^ 2 * (a * (a * ((L : ℝ) ^ 2 * G ^ (6 * L * S)))) :=
          mul_le_mul_of_nonneg_left hHξ_le (by positivity)
      _ = a ^ 2 * (L : ℝ) ^ 4 * G ^ (6 * L * S) := by ring
      _ ≤ P := by
          rw [hP]; exact mul_le_mul_of_nonneg_left hGST (by positivity)
  set E : ℝ := exp (2 * (L : ℝ) * X * (7 * (3 * T * Y))) with hE
  set Q : ℝ := (1 / 3 : ℝ) ^ (T ^ 3) with hQ
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hQ0 : 0 ≤ Q := by positivity
  -- Step B: replace by the cruder bound
  have hstepB : G ^ (6 * L * T) * ((L : ℝ) ^ 2 * Hξ * E) * Q *
        ((L : ℝ) ^ 2 * Hξ * G ^ (6 * L * T)) ^ (h - 1) ≤
      G ^ (6 * L * T) * (P * E) * Q * (P * G ^ (6 * L * T)) ^ (h - 1) := by
    gcongr
  -- the crude bound as a single exponential
  have hcrude : G ^ (6 * L * T) * (P * E) * Q * (P * G ^ (6 * L * T)) ^ (h - 1) ≤
      exp (2 * h * log a + 4 * h * L + 12 * h * L * T * log G + 42 * L * X * Y * T - T ^ 3) := by
    -- algebraic regrouping: everything is (a²L⁴)^h G^{12 h L T} E Q
    have hregroup : G ^ (6 * L * T) * (P * E) * Q * (P * G ^ (6 * L * T)) ^ (h - 1) =
        (a ^ 2) ^ h * ((L : ℝ) ^ 4) ^ h * G ^ (12 * h * L * T) * E * Q := by
      obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
      simp only [Nat.add_sub_cancel, hP]
      have : 12 * (m + 1) * L * T = 6 * L * T + 6 * L * T + m * (6 * L * T + 6 * L * T) := by ring
      rw [this, pow_add, pow_add, pow_mul, mul_pow, mul_pow, mul_pow, pow_succ (a ^ 2),
        pow_succ ((L : ℝ) ^ 4)]
      ring
    rw [hregroup]
    have hA : (a ^ 2) ^ h = exp (2 * h * log a) := by
      rw [← pow_mul, pow_eq_exp_mul_log (by linarith : (0 : ℝ) < a)]
      congr 1; push_cast; ring
    have hB : ((L : ℝ) ^ 4) ^ h ≤ exp (4 * h * L) := by
      rw [← pow_mul]
      calc (L : ℝ) ^ (4 * h) ≤ (exp L) ^ (4 * h) :=
            pow_le_pow_left₀ (by positivity) (nat_le_exp _) _
        _ = exp (4 * h * L) := by rw [← exp_nat_mul]; push_cast; ring_nf
    have hC' : G ^ (12 * h * L * T) = exp (12 * h * L * T * log G) := by
      rw [pow_eq_exp_mul_log hG0]; push_cast; ring_nf
    have hD : Q ≤ exp (-(T : ℝ) ^ 3) := by
      have := one_third_pow_le_exp_neg (T ^ 3)
      rw [hQ]; push_cast at this; exact this
    calc (a ^ 2) ^ h * ((L : ℝ) ^ 4) ^ h * G ^ (12 * h * L * T) * E * Q
        ≤ exp (2 * h * log a) * exp (4 * h * L) * exp (12 * h * L * T * log G) * E *
            exp (-(T : ℝ) ^ 3) := by
          rw [hA, hC']
          gcongr
      _ = exp (2 * h * log a + 4 * h * L + 12 * h * L * T * log G + 42 * L * X * Y * T -
            T ^ 3) := by
          rw [hE, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
          congr 1; ring
  -- Step D: the exponent is negative
  have hexp : 2 * h * log a + 4 * h * L + 12 * h * L * T * log G + 42 * L * X * Y * T -
      (T : ℝ) ^ 3 < 0 := by
    have hLr : (L : ℝ) = 2 * (n : ℝ) ^ 3 := by rw [hL]; push_cast; ring
    have hTn : (n : ℝ) ^ 2 ≤ T := by exact_mod_cast hT
    have hT2 : (n : ℝ) ^ 4 ≤ (T : ℝ) ^ 2 := by
      calc (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (T : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hTn 2
    -- the κ-part
    have hLT : (L : ℝ) ≤ L * T := le_mul_of_one_le_right (by positivity) hT1
    have hκpart : 4 * h * L + 12 * h * L * T * log G + 42 * L * X * Y * T ≤ κ * L * T := by
      have e : κ * L * T = 4 * h * (L * T) + 12 * h * L * T * log G + 42 * L * X * Y * T := by
        rw [hκ]; ring
      have : 4 * (h : ℝ) * L ≤ 4 * h * (L * T) :=
        mul_le_mul_of_nonneg_left hLT (by positivity)
      linarith
    have hloga4 : 0 ≤ 4 * (h : ℝ) * log a := by positivity
    have h4κ : 4 * κ ≤ n := by linarith
    have hκT : κ * L * T ≤ (T : ℝ) ^ 3 / 2 := by
      rw [hLr]
      have hT0 : (0 : ℝ) ≤ T := by linarith
      have hn3T : 0 ≤ (n : ℝ) ^ 3 * T := by positivity
      calc κ * (2 * (n : ℝ) ^ 3) * T = (2 * κ) * ((n : ℝ) ^ 3 * T) := by ring
        _ ≤ ((n : ℝ) / 2) * ((n : ℝ) ^ 3 * T) :=
            mul_le_mul_of_nonneg_right (by linarith) hn3T
        _ = (n : ℝ) ^ 4 * T / 2 := by ring
        _ ≤ (T : ℝ) ^ 2 * T / 2 := by gcongr
        _ = (T : ℝ) ^ 3 / 2 := by ring
    have hapart : 2 * h * log a < (T : ℝ) ^ 3 / 2 := by
      have h1 : 2 * (h : ℝ) * log a < (n : ℝ) / 2 := by linarith
      have h2 : (n : ℝ) ≤ (T : ℝ) ^ 3 := by
        calc (n : ℝ) ≤ (n : ℝ) ^ 2 := le_self_pow₀ hnr (by norm_num)
          _ ≤ T := hTn
          _ ≤ (T : ℝ) ^ 3 := le_self_pow₀ hT1 (by norm_num)
      linarith
    linarith
  have hfin : exp (2 * h * log a + 4 * h * L + 12 * h * L * T * log G + 42 * L * X * Y * T -
      (T : ℝ) ^ 3) < 1 := by
    rw [← exp_zero]; exact exp_lt_exp.mpr hexp
  exact lt_of_le_of_lt (hstepB.trans hcrude) hfin

end StrongSix.SixExp

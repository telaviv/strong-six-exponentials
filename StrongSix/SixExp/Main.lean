/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import StrongSix.Defs
import StrongSix.SixExp.Setup
import StrongSix.SixExp.Arith
import StrongSix.SixExp.Extrapolation
import StrongSix.SixExp.Params

/-!
# The six exponentials theorem

Proof (Lang, Ramachandra), following the classical Schneider-type argument:

1. Siegel's lemma gives `F(z) = ∑_k ξ_k e^{μ_k z}` (`ξ_k` algebraic integers, not all `0`)
   vanishing at `γ_s` for `s ∈ [0,S)³`.
2. Extrapolation: for every `T ≥ S`, `F` vanishes at `γ_s` for `s ∈ [0,T)³`
   (Schwarz + Liouville + the parameter inequality).
3. `F ≢ 0` (linear independence of exponentials), but Schwarz with `T → ∞` forces `F ≡ 0`.
-/

open Complex Finset NumberField

namespace StrongSix.SixExp

theorem wt_le_of_le {L T : ℕ} (k : Fin 2 → ℕ) (s : Fin 3 → ℕ) (hk : ∀ i, k i ≤ L)
    (hs : ∀ j, s j ≤ T) : wt k s ≤ 6 * L * T := by
  unfold wt
  have h1 : ∑ i, k i ≤ 2 * L := by
    calc ∑ i, k i ≤ ∑ _i : Fin 2, L := sum_le_sum fun i _ => hk i
      _ = 2 * L := by simp
  have h2 : ∑ j, s j ≤ 3 * T := by
    calc ∑ j, s j ≤ ∑ _j : Fin 3, T := sum_le_sum fun j _ => hs j
      _ = 3 * T := by simp
  calc (∑ i, k i) * ∑ j, s j ≤ (2 * L) * (3 * T) := Nat.mul_le_mul h1 h2
    _ = 6 * L * T := by ring

theorem fin_vec_coe_injective {n m : ℕ} :
    Function.Injective (fun k : Fin n → Fin m => (fun i => ((k i : ℕ)))) := by
  intro k k' h
  funext i
  exact Fin.ext (congrFun h i)

set_option maxHeartbeats 1000000 in
/-- **Core of the six exponentials theorem**, in a fixed number field. -/
theorem six_exp_core {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ)
    {x : Fin 2 → ℂ} {y : Fin 3 → ℂ} (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (a : Fin 2 → Fin 3 → K) (ha : ∀ i j, σ (a i j) = exp (x i * y j))
    (d : ℕ) (hd : 1 ≤ d) (hint : ∀ i j, IsIntegral ℤ ((d : K) * a i j))
    {A : ℝ} (hA1 : 1 ≤ A) (hA : ∀ i j, house (a i j) ≤ A) : False := by
  classical
  obtain ⟨C, hC0, hsiegel⟩ := siegel_six d hd a hint hA1 hA
  -- size constants
  set X : ℝ := ‖x 0‖ + ‖x 1‖ with hXdef
  set Y : ℝ := 1 + (‖y 0‖ + ‖y 1‖ + ‖y 2‖) with hYdef
  have hX0 : 0 ≤ X := by positivity
  have hY1 : 1 ≤ Y := by
    have : 0 ≤ ‖y 0‖ + ‖y 1‖ + ‖y 2‖ := by positivity
    linarith
  have hxX : ∀ i, ‖x i‖ ≤ X := by
    intro i
    fin_cases i <;> simp <;> linarith [norm_nonneg (x 0), norm_nonneg (x 1)]
  have hyY : ∀ j, ‖y j‖ ≤ Y := by
    intro j
    fin_cases j <;> simp <;> linarith [norm_nonneg (y 0), norm_nonneg (y 1), norm_nonneg (y 2)]
  set h := Module.finrank ℚ K with hhdef
  have hh : 1 ≤ h := Module.finrank_pos
  set G : ℝ := (d : ℝ) * A with hGdef
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le hd1 hA1
  obtain ⟨n, hn1, hpar⟩ := params_exist h hh hC0 hG hX0 hY1
  set L : ℕ := 2 * n ^ 3 with hL
  set S : ℕ := n ^ 2 with hS
  have hS0 : 0 < S := by positivity
  have hLS : 2 * S ^ 3 ≤ L ^ 2 := by
    rw [hS, hL]; ring_nf; omega
  obtain ⟨ξ, hξ0, hξvan, hξb⟩ := hsiegel L S hS0 hLS
  set Hξ : ℝ := C * (1 + C * (L : ℝ) ^ 2 * ((d : ℝ) * A) ^ (6 * L * S)) with hHξ
  -- the auxiliary function
  set c : (Fin 2 → Fin L) → ℂ := fun k => σ (ξ k : K) with hc
  set μ : (Fin 2 → Fin L) → ℂ := fun k => comb x (fun i => (k i : ℕ)) with hμ
  have hμB : ∀ k, ‖μ k‖ ≤ 2 * L * X := by
    intro k
    have := norm_comb_le x (fun i => (k i : ℕ)) hxX (N := L) (fun i => (k i).isLt.le)
    simpa using this
  have hcard : Fintype.card (Fin 2 → Fin L) = L ^ 2 := by simp
  have hcsum : ∑ k, ‖c k‖ ≤ (L : ℝ) ^ 2 * Hξ := by
    calc ∑ k, ‖c k‖ ≤ ∑ _k : Fin 2 → Fin L, Hξ :=
          sum_le_sum fun k _ => (norm_embedding_le_house _ σ).trans (hξb k)
      _ = (L : ℝ) ^ 2 * Hξ := by
          rw [sum_const, card_univ, hcard, nsmul_eq_mul]; push_cast; ring
  have hFval : ∀ s : Fin 3 → ℕ, expPoly c μ (comb y s) =
      σ (∑ k, (ξ k : K) * val a (fun i => (k i : ℕ)) s) := by
    intro s
    simp only [expPoly, map_sum, map_mul, map_val σ ha, hc, hμ]
  have hγ_inj : Function.Injective
      (fun t : Fin 3 → ℕ => comb y t) := comb_injective hy
  -- Step 2: vanishing at all lattice points
  have hvan : ∀ T, S ≤ T → ∀ s : Fin 3 → Fin T,
      expPoly c μ (comb y (fun j => (s j : ℕ))) = 0 := by
    intro T hT
    induction T, hT using Nat.le_induction with
    | base =>
      intro s
      rw [hFval, hξvan s, map_zero]
    | succ T hST ih =>
      intro s
      set Z : Finset ℂ :=
        Finset.univ.image (fun t : Fin 3 → Fin T => comb y (fun j => (t j : ℕ))) with hZdef
      have hZcard : Z.card = T ^ 3 := by
        have hinjT : Function.Injective (fun t : Fin 3 → Fin T => comb y (fun j => (t j : ℕ))) :=
          fun t t' h => fin_vec_coe_injective (hγ_inj h)
        rw [hZdef, Finset.card_image_of_injective _ hinjT]
        simp
      have hZ : ∀ z ∈ Z, expPoly c μ z = 0 := by
        intro z hz
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
        exact ih t
      have hT1 : (1 : ℝ) ≤ T := by
        have : 1 ≤ T := le_trans hS0 hST
        exact_mod_cast this
      set r : ℝ := 3 * T * Y with hr
      have hr0 : 0 < r := by positivity
      have hZr : ∀ z ∈ Z, ‖z‖ ≤ r := by
        intro z hz
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
        have := norm_comb_le y (fun j => (t j : ℕ)) hyY (N := T) (fun j => (t j).isLt.le)
        simpa [hr] using this
      have hsT : ∀ j, ((s j : ℕ)) ≤ T := fun j => Nat.lt_succ_iff.mp (s j).isLt
      have hζ : ‖comb y (fun j => (s j : ℕ))‖ ≤ r := by
        have := norm_comb_le y (fun j => (s j : ℕ)) hyY (N := T) hsT
        simpa [hr] using this
      set E : ℕ := 6 * L * T with hE
      set β : K := ∑ k, (ξ k : K) * ival d a E (fun i => (k i : ℕ)) (fun j => (s j : ℕ))
        with hβ
      have hwt : ∀ k : Fin 2 → Fin L, wt (fun i => (k i : ℕ)) (fun j => (s j : ℕ)) ≤ E :=
        fun k => wt_le_of_le _ _ (fun i => (k i).isLt.le) hsT
      have hβint : IsIntegral ℤ β := by
        have hmem : β ∈ integralClosure ℤ K := by
          refine Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ ?_ ?_
          · exact (ξ k).2
          · exact ival_integral d hint _ _ _
        exact hmem
      have hβσ : σ β = ((d : ℝ) ^ E : ℝ) * expPoly c μ (comb y (fun j => (s j : ℕ))) := by
        rw [hFval, hβ, map_sum, map_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [ival_eq d a _ _ (hwt k), map_mul, map_mul, map_mul, map_pow, map_natCast]
        push_cast
        ring
      have hβH : house β ≤ (L : ℝ) ^ 2 * Hξ * G ^ E := by
        calc house β ≤ ∑ k : Fin 2 → Fin L,
              house ((ξ k : K) * ival d a E (fun i => (k i : ℕ)) (fun j => (s j : ℕ))) :=
              house_sum_le_sum_house _ _
          _ ≤ ∑ _k : Fin 2 → Fin L, Hξ * G ^ E := by
              refine sum_le_sum fun k _ => (house_mul_le _ _).trans ?_
              exact mul_le_mul (hξb k) (house_ival_le d hd a hA1 hA _ _ (hwt k))
                (house_nonneg _) ((house_nonneg _).trans (hξb k))
          _ = (L : ℝ) ^ 2 * Hξ * G ^ E := by
              rw [sum_const, card_univ, hcard, nsmul_eq_mul]; push_cast; ring
      have hDpos : (0 : ℝ) < (d : ℝ) ^ E := by positivity
      refine expPoly_eq_zero_of_small σ c μ hμB Z hZ hr0 hZr hζ hβint hDpos hβσ hβH ?_
      -- the smallness condition, from the parameter inequality
      have hpT := hpar T hST
      have hdG : (d : ℝ) ^ E ≤ G ^ E :=
        pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_right (by positivity) hA1) _
      have hHξ0 : 0 ≤ Hξ := le_trans (house_nonneg _) (hξb (fun _ => ⟨0, by positivity⟩))
      rw [hZcard]
      calc (d : ℝ) ^ E * ((∑ k, ‖c k‖) * Real.exp (2 * L * X * (7 * r))) * (1 / 3 : ℝ) ^ (T ^ 3) *
            ((L : ℝ) ^ 2 * Hξ * G ^ E) ^ (h - 1)
          ≤ G ^ E * (((L : ℝ) ^ 2 * Hξ) * Real.exp (2 * L * X * (7 * r))) *
              (1 / 3 : ℝ) ^ (T ^ 3) * ((L : ℝ) ^ 2 * Hξ * G ^ E) ^ (h - 1) := by
            gcongr
        _ < 1 := by
            simpa [hr, hE, hHξ, hGdef, hL, hS, mul_assoc] using hpT
  -- Step 3: `F ≢ 0`
  obtain ⟨k₀, hk₀⟩ : ∃ k, ξ k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ0 (funext hcon)
  have hμinj : Function.Injective μ := (comb_injective hx).comp fin_vec_coe_injective
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, expPoly c μ z₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hc0 := congrFun (eq_zero_of_expPoly_eq_zero hμinj hcon) k₀
    simp only [hc, Pi.zero_apply, map_eq_zero_iff σ σ.injective] at hc0
    exact hk₀ (by exact_mod_cast hc0)
  -- Step 4: Schwarz at `z₀` with `T` large
  set P : ℝ := max 1 ((L : ℝ) ^ 2 * Hξ) with hP
  have hP1 : 1 ≤ P := le_max_left _ _
  set f0 : ℝ := ‖expPoly c μ z₀‖ with hf0
  have hf0pos : 0 < f0 := norm_pos_iff.mpr hz₀
  set Qc : ℝ := |Real.log P| + |Real.log f0| + 42 * L * X * Y + ‖z₀‖ + S + 1 with hQc
  obtain ⟨T, hTQ⟩ := exists_nat_gt Qc
  have hQ1 : 1 ≤ Qc := by
    have : 0 ≤ |Real.log P| + |Real.log f0| + 42 * L * X * Y + ‖z₀‖ + S := by positivity
    linarith
  have hTr : (1 : ℝ) ≤ T := by linarith
  have hST : S ≤ T := by
    have : (S : ℝ) < T := by
      have : (S : ℝ) ≤ Qc := by
        have : 0 ≤ |Real.log P| + |Real.log f0| + 42 * L * X * Y + ‖z₀‖ := by positivity
        linarith
      linarith
    exact_mod_cast this.le
  set Z : Finset ℂ :=
    Finset.univ.image (fun t : Fin 3 → Fin T => comb y (fun j => (t j : ℕ))) with hZdef
  have hZcard : Z.card = T ^ 3 := by
    have hinjT : Function.Injective (fun t : Fin 3 → Fin T => comb y (fun j => (t j : ℕ))) :=
      fun t t' h => fin_vec_coe_injective (hγ_inj h)
    rw [hZdef, Finset.card_image_of_injective _ hinjT]
    simp
  have hZ : ∀ z ∈ Z, expPoly c μ z = 0 := by
    intro z hz
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
    exact hvan T hST t
  set r : ℝ := 3 * T * Y with hr
  have hr0 : 0 < r := by positivity
  have hZr : ∀ z ∈ Z, ‖z‖ ≤ r := by
    intro z hz
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
    have := norm_comb_le y (fun j => (t j : ℕ)) hyY (N := T) (fun j => (t j).isLt.le)
    simpa [hr] using this
  have hz0r : ‖z₀‖ ≤ r := by
    have h1 : ‖z₀‖ ≤ T := by
      have : ‖z₀‖ ≤ Qc := by
        have : 0 ≤ |Real.log P| + |Real.log f0| + 42 * L * X * Y + (S : ℝ) + 1 := by positivity
        linarith
      linarith
    have h2 : (T : ℝ) ≤ 3 * T * Y := by nlinarith
    linarith
  have hcirc : ∀ w : ℂ, ‖w‖ = 7 * r → ‖expPoly c μ w‖ ≤ P * Real.exp (2 * L * X * (7 * r)) := by
    intro w hw
    have := norm_expPoly_le c μ hμB w
    rw [hw] at this
    exact this.trans (mul_le_mul_of_nonneg_right (hcsum.trans (le_max_right _ _))
      (Real.exp_pos _).le)
  have hschw := norm_le_of_zeros (expPoly c μ) (differentiable_expPoly c μ) Z hZ hr0.le
    (by linarith : r < 7 * r) hZr hcirc hz0r
  have h13 : 2 * r / (7 * r - r) = 1 / 3 := by field_simp; ring
  rw [h13, hZcard] at hschw
  -- `(1/3)^{T³} ≤ exp(-T³)` and the exponent is too negative
  have hthird := one_third_pow_le_exp_neg (T ^ 3)
  have hbound : f0 ≤ Real.exp (Real.log P + 42 * L * X * Y * T - (T : ℝ) ^ 3) := by
    calc f0 ≤ P * Real.exp (2 * L * X * (7 * r)) * (1 / 3 : ℝ) ^ (T ^ 3) := hschw
      _ ≤ P * Real.exp (2 * L * X * (7 * r)) * Real.exp (-((T ^ 3 : ℕ) : ℝ)) := by
          gcongr
      _ = Real.exp (Real.log P) * Real.exp (2 * L * X * (7 * r)) *
            Real.exp (-((T ^ 3 : ℕ) : ℝ)) := by
          rw [Real.exp_log (by linarith : (0 : ℝ) < P)]
      _ = Real.exp (Real.log P + 2 * L * X * (7 * r) + -((T ^ 3 : ℕ) : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ = Real.exp (Real.log P + 42 * L * X * Y * T - (T : ℝ) ^ 3) := by
          congr 1; rw [hr]; push_cast; ring
  have hexp_lt : Real.log P + 42 * L * X * Y * T - (T : ℝ) ^ 3 < Real.log f0 := by
    have hT3 : (T : ℝ) * T ≤ (T : ℝ) ^ 3 := by nlinarith
    have hTQ' : (T : ℝ) * Qc ≤ T * T := mul_le_mul_of_nonneg_left hTQ.le (by linarith)
    have hlin : Real.log P - Real.log f0 + 42 * L * X * Y * T < (T : ℝ) * Qc := by
      have e1 : Real.log P ≤ |Real.log P| := le_abs_self _
      have e2 : -Real.log f0 ≤ |Real.log f0| := neg_le_abs _
      have e3 : |Real.log P| ≤ T * |Real.log P| := le_mul_of_one_le_left (abs_nonneg _) hTr
      have e4 : |Real.log f0| ≤ T * |Real.log f0| := le_mul_of_one_le_left (abs_nonneg _) hTr
      have e5 : 0 ≤ (T : ℝ) * (‖z₀‖ + S) := by positivity
      have e6 : (T : ℝ) * Qc = T * |Real.log P| + T * |Real.log f0| + 42 * L * X * Y * T +
          T * (‖z₀‖ + S) + T := by rw [hQc]; ring
      linarith
    linarith
  have := hbound.trans_lt (Real.exp_lt_exp.mpr hexp_lt)
  rw [Real.exp_log hf0pos] at this
  exact lt_irrefl _ this

/-- **The six exponentials theorem** (Lang 1966, Ramachandra 1968). -/
theorem six_exponentials : SixExponentials := by
  intro x y hx hy
  by_contra hcon
  push Not at hcon
  -- all six numbers are algebraic
  have halg : ∀ i j, IsAlgebraic ℚ (exp (x i * y j)) := by
    intro i j
    have := hcon i j
    rwa [Transcendental, not_not] at this
  -- the number field they generate
  set Sset : Set ℂ := Set.range (fun p : Fin 2 × Fin 3 => exp (x p.1 * y p.2)) with hSset
  set K := IntermediateField.adjoin ℚ Sset with hK
  have hint' : ∀ z ∈ Sset, IsIntegral ℚ z := by
    rintro z ⟨⟨i, j⟩, rfl⟩
    exact (halg i j).isIntegral
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hint'
  have : NumberField K := ⟨⟩
  let a : Fin 2 → Fin 3 → K := fun i j =>
    ⟨exp (x i * y j), IntermediateField.subset_adjoin ℚ Sset ⟨(i, j), rfl⟩⟩
  let σ : K →+* ℂ := algebraMap K ℂ
  have ha : ∀ i j, σ (a i j) = exp (x i * y j) := fun i j => rfl
  -- a common denominator
  classical
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : Fin 2 × Fin 3 => a p.1 p.2))
  set d : ℕ := m.natAbs with hd
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm0)
  have hdint : ∀ i j, IsIntegral ℤ ((d : K) * a i j) := by
    intro i j
    have hmem := hm (a i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at hmem
    rcases Int.natAbs_eq m with h | h
    · have : (d : K) = (m : K) := by rw [hd, ← Int.cast_natCast, ← h]
      rw [this]; exact hmem
    · have : (d : K) = -(m : K) := by
        rw [hd, ← Int.cast_natCast]
        have h' : (m.natAbs : ℤ) = -m := by omega
        rw [h']; push_cast; ring
      rw [this, neg_mul]; exact hmem.neg
  -- a bound for the houses
  set A : ℝ := 1 + ∑ p : Fin 2 × Fin 3, house (a p.1 p.2) with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ ∑ p : Fin 2 × Fin 3, house (a p.1 p.2) :=
      sum_nonneg fun p _ => house_nonneg _
    linarith
  have hAb : ∀ i j, house (a i j) ≤ A := by
    intro i j
    have := single_le_sum (f := fun p : Fin 2 × Fin 3 => house (a p.1 p.2))
      (fun p _ => house_nonneg _) (Finset.mem_univ (i, j))
    simp only at this
    linarith
  exact six_exp_core σ hx hy a ha d hd1 hdint hA1 hAb

end StrongSix.SixExp

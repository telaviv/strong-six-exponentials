/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import StrongSix.M2.HDim
import StrongSix.CM.Unmixedness

/-!
# Hilbert dimension versus height, upper bound (M2, layer R3b-ii)

In `A = K[σ]` (a Cohen–Macaulay ring), every proper ideal `L` contains a sequence
`f₁, …, f_h`, `h = ht L`, such that each `f_{j+1}` is a non-zero-divisor modulo `(f₁, …, f_j)` and
`(f₁, …, f_j)` has height `j`. This uses Macaulay's unmixedness theorem and prime avoidance. Each
`f_j` strictly lowers the Hilbert dimension (`hdim_section_lt`), so

  `hdim L + ht L ≤ hdim (0) ≤ card σ`   (`hdim_add_height_le`).
-/

open MvPolynomial Module Submodule

namespace StrongSix.M2

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (K : Type*) [Field K]

local notation "A" => MvPolynomial σ K

instance isCohenMacaulayRing_mvPolynomial : IsCohenMacaulayRing A :=
  have : IsCohenMacaulayRing (MvPolynomial (Fin (Fintype.card σ)) K) :=
    MvPolynomial.isCM_of_isCM K _
  isCohenMacaulayRing_of_ringEquiv
    (MvPolynomial.renameEquiv K (Fintype.equivFin σ)).symm.toRingEquiv

theorem ofList_isUnmixed {l : List A} (h : (Ideal.ofList l).height = l.length) :
    (Ideal.ofList l).IsUnmixed :=
  (isCohenMacaulayRing_iff_unmixed.mp inferInstance) l h

variable {K}

/-- An element outside every associated prime of `I` is a non-zero-divisor modulo `I`. -/
theorem nzd_of_not_mem_ass {I : Ideal A} {f : A}
    (hf : ∀ q ∈ associatedPrimes A (A ⧸ I), f ∉ q) : ∀ Q, f * Q ∈ I → Q ∈ I := by
  intro Q hQ
  by_contra hQI
  have hmem : f ∈ ⋃ p ∈ associatedPrimes A (A ⧸ I), (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    refine ⟨Ideal.Quotient.mk I Q, fun h => hQI (Ideal.Quotient.eq_zero_iff_mem.mp h), ?_⟩
    change Ideal.Quotient.mk I (f * Q) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hmem
  obtain ⟨q, hq, hfq⟩ := hmem
  exact hf q hq hfq

/-- **Prime avoidance** for the associated primes of `I`. -/
theorem exists_avoid {I L : Ideal A} (h : ∀ q ∈ associatedPrimes A (A ⧸ I), ¬ L ≤ q) :
    ∃ f ∈ L, ∀ q ∈ associatedPrimes A (A ⧸ I), f ∉ q := by
  by_contra hcon
  push Not at hcon
  have hsub : (L : Set A) ⊆ ⋃ q ∈ associatedPrimes A (A ⧸ I), ((id q : Ideal A) : Set A) := by
    intro f hf
    obtain ⟨q, hq, hfq⟩ := hcon f hf
    exact Set.mem_iUnion₂.mpr ⟨q, hq, hfq⟩
  obtain ⟨q, hq, hLq⟩ := (Ideal.subset_union_prime_finite (f := id)
    (associatedPrimes.finite A (A ⧸ I)) ⊥ ⊥
    (fun q hq _ _ => (AssociatedPrimes.mem_iff.mp hq).isPrime)).mp hsub
  exact h q hq hLq

/-- Adding an element outside every minimal prime raises the height of a complete intersection by
one. -/
theorem height_append {rs : List A} (ht : (Ideal.ofList rs).height = rs.length) {f : A}
    (hf : ∀ q ∈ (Ideal.ofList rs).minimalPrimes, f ∉ q) (hne : Ideal.ofList (rs ++ [f]) ≠ ⊤) :
    (Ideal.ofList (rs ++ [f])).height = (rs ++ [f]).length := by
  apply le_antisymm (Ideal.ofList_height_le_length _ hne)
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun p hp => ?_
  have : p.IsPrime := hp.1.1
  have hIp : Ideal.ofList rs ≤ p :=
    le_trans (by rw [Ideal.ofList_append]; exact le_sup_left) hp.1.2
  have hfmem : f ∈ Ideal.ofList (rs ++ [f]) := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
  have hfp : f ∈ p := hp.1.2 hfmem
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hIp
  have : q.IsPrime := hq.1.1
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hf q hq (h ▸ hfp)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (Ideal.ofList rs).height ≤ q.height := Ideal.height_mono hq.1.2
  rw [ht] at h2
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
    Nat.cast_one]
  calc (rs.length : ℕ∞) + 1 ≤ q.height + 1 := by gcongr
    _ ≤ p.height := h1

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (β : σ → ι) (D : ι → ℕ)

/-- **Regular chains inside `L`.** -/
theorem exists_regular_chain (hD : ∀ i, 1 ≤ D i) {L : Ideal A} (hL : L ≠ ⊤) :
    ∀ j : ℕ, (j : ℕ∞) ≤ L.height → ∃ rs : List A, (∀ r ∈ rs, r ∈ L) ∧ rs.length = j ∧
      (Ideal.ofList rs).height = j ∧
      (hdata β D K (Ideal.ofList rs)).1 + j ≤ (hdata β D K (⊥ : Ideal A)).1 := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨[], by simp, rfl, ?_, by simp⟩
    refine le_antisymm ?_ bot_le
    simpa using Ideal.ofList_height_le_length ([] : List A) (by simp)
  | succ j ih =>
    intro hj
    obtain ⟨rs, hrsL, hlen, hht, hdim⟩ := ih (le_trans (by exact_mod_cast Nat.le_succ j) hj)
    set I := Ideal.ofList rs
    have hIL : I ≤ L := Ideal.span_le.mpr fun r hr => hrsL r hr
    have hunmix := ofList_isUnmixed K (l := rs) (by rw [hht, hlen])
    have hht' : (Ideal.ofList rs).height = rs.length := by rw [hht, hlen]
    have hass : ∀ q ∈ associatedPrimes A (A ⧸ I), ¬ L ≤ q := by
      intro q hq hLq
      have h1 : q.height = I.height := hunmix.height_eq hq
      have h2 := Ideal.height_mono hLq
      rw [h1, hht] at h2
      have := hj.trans h2
      norm_cast at this
      omega
    obtain ⟨f, hfL, hfass⟩ := exists_avoid hass
    have hnzd := nzd_of_not_mem_ass hfass
    have hmin : ∀ q ∈ I.minimalPrimes, f ∉ q := fun q hq => by
      rw [← associatedPrimes_eq_minimalPrimes_of_isUnmixed hunmix] at hq
      exact hfass q hq
    have hsubL : Ideal.ofList (rs ++ [f]) ≤ L := by
      rw [Ideal.ofList_append, Ideal.ofList_singleton]
      exact sup_le hIL (Ideal.span_le.mpr (by simpa using hfL))
    have hne : Ideal.ofList (rs ++ [f]) ≠ ⊤ := ne_top_of_le_ne_top hL hsubL
    refine ⟨rs ++ [f], fun r hr => ?_, by simp [hlen], ?_, ?_⟩
    · rcases List.mem_append.mp hr with h | h
      · exact hrsL r h
      · rw [List.mem_singleton.mp h]; exact hfL
    · rw [height_append hht' hmin hne]; simp [hlen]
    · have hlt := hdim_section_lt β D K hD (J := I) (P := f) hnzd
        (by rw [Ideal.ofList_append, Ideal.ofList_singleton]) hne
      omega

/-- **Upper bound:** `hdim L + ht L ≤ card σ`. -/
theorem hdim_add_height_le (hD : ∀ i, 1 ≤ D i) {L : Ideal A} (hL : L ≠ ⊤) :
    ((hdata β D K L).1 : ℕ∞) + L.height ≤ Fintype.card σ := by
  have hfin : L.height ≠ ⊤ := Ideal.height_ne_top hL
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨rs, hrsL, hlen, hht, hdim⟩ := exists_regular_chain β D hD hL j (le_of_eq hj)
  have hIL : Ideal.ofList rs ≤ L := Ideal.span_le.mpr fun r hr => hrsL r hr
  have hcmp := hdata_le_of_le β D K hIL hL
  have hbot := hdim_bot_le β D K (σ := σ)
  rw [← hj]
  have : (hdata β D K L).1 + j ≤ Fintype.card σ := by
    rcases hcmp with h | ⟨h, -⟩ <;> omega
  exact_mod_cast this

end StrongSix.M2

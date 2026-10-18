# StrongSix: a Lean formalization of Roy's strong six exponentials theorem

Lean 4 + Mathlib (v4.35.0). The final target is `StrongSix.StrongSixExponentials` (`StrongSix/Defs.lean`):

> If x₁, x₂ are ℚ̄-linearly independent and y₁, y₂, y₃ are ℚ̄-linearly independent complex numbers,
> then one of the six products xᵢyⱼ is not in L̃, the ℚ̄-span of 1 and the logarithms of algebraic numbers.

The roadmap is in `../BLUEPRINT.md`.

## Status

| Result | Declaration | Status |
|---|---|---|
| Six exponentials theorem (Lang, Ramachandra) | `StrongSix.SixExp.six_exponentials : SixExponentials` | **done**: standard axioms only, no sorry |
| Waldschmidt's Theorem 1 on G_a^{d₀} × G_m^{d₁} (unconditional) | `StrongSix.M2.waldschmidtTheorem1 : WaldschmidtTheorem1` | **done** (2026-10-17): standard axioms only, no sorry |
| Strong six, **conditional on Waldschmidt's Theorem 1** | `StrongSix.Roy.strongSix_of_theorem1 : WaldschmidtTheorem1 → StrongSixExponentials` | **done**: standard axioms only, no sorry |
| Waldschmidt's Theorem 1, **conditional on Philippon's multiplicity estimate** (milestone M1) | `StrongSix.Thm1.theorem1_of_multEst : MultEst Qb → WaldschmidtTheorem1` | **done** (2026-10-17): standard axioms only, no sorry |
| Strong six, conditional on the multiplicity estimate | `StrongSix.Thm1.strongSix_of_multEst : MultEst Qb → StrongSixExponentials` | **done**: standard axioms only, no sorry |
| Philippon's multiplicity estimate on G_a^{d₀} × G_m^{d₁} (milestone M2), over any algebraically closed field of characteristic 0 | `StrongSix.M2.multEst_of_isAlgClosed : MultEst K`, `StrongSix.M2.multEst_Qb : MultEst Qb` | **done** (2026-10-17): standard axioms only, no sorry. It follows Roy (DALAG Ch. 5, 8): filtered Hilbert functions, Macaulay unmixedness (ported Guan–Hu CM library, `CM/`), Bézout via complete intersections, Wüstholz's lemma by linear algebra, and the stabilizer argument with primes. Plan and notes in `../M2_PLAN.md` |
| **Roy's strong six exponentials theorem (unconditional)** | `StrongSix.M2.strongSixExponentials : StrongSixExponentials` | **done** (2026-10-17): standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), no sorry, no `native_decide`. Audit: `lake env lean Axioms.lean` |

## Layout

* `Defs.lean`: 𝓛, L̃, and the statements.
* `Analytic/Schwarz.lean`: Schwarz lemma for entire functions with many zeros.
* `Analytic/ExpPoly.lean`: exponential polynomials; linear independence of exponentials.
* `Arith/Liouville.lean`: Liouville's inequality for algebraic integers.
* `Roy/*`: Roy's §§1–4: the abstract Theorem 3, base change, the subquotient category, the realization, and Theorem 1 ⇒ strong six.
* `Thm1/*`: Waldschmidt's Theorem 1 from the multiplicity estimate, by Laurent's interpolation determinants
  (about 3.9k lines). See `../THEOREM1_PLAN.md` §5 for the file map.
* `SixExp/*`: the six exponentials theorem.
  * `Setup`: frequencies and points.
  * `Arith`: values, integrality, house bounds, Siegel.
  * `Extrapolation`: Schwarz plus Liouville.
  * `Params`: the parameter inequality.
  * `Main`: the theorem.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"; lake build
```

Axiom audit: `lake env lean Axioms.lean`. Every `#print axioms` line there, including `StrongSix.M2.strongSixExponentials`, should list only `propext`, `Classical.choice`, `Quot.sound`.

## Third-party code

`StrongSix/CM/` is a port of Nailin Guan and Yongle Hu's Cohen–Macaulay files: github.com/Thmoas-Guan/mathlib4_fork,
branch `ABS-Criterion-Project-new`, commit 0ff6e01f (Apache-2.0; arXiv:2510.24818). The files are
`Regular/Ischebeck`, `CohenMacaulay/{Basic,Catenary,Unmixed,Polynomial}`, plus lemmas from `Regular/Depth` and
`KrullDimension/Polynomial`, collected in `Compat.lean`. The original copyright headers are kept. Local changes are
marked `PORT`.

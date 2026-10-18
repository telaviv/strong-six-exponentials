# Roy's strong six exponentials theorem in Lean 4

A complete, axiom-clean Lean 4 + Mathlib proof of Roy's strong six exponentials theorem:

> **Theorem** (Roy 1992, Corollary 2). Let L̃ be the ℚ̄-vector space spanned by 1 and the logarithms of nonzero
> algebraic numbers. If x₁, x₂ ∈ ℂ are linearly independent over ℚ̄ and y₁, y₂, y₃ ∈ ℂ are linearly independent
> over ℚ̄, then at least one of the six products xᵢyⱼ is not in L̃.

In Lean this is

```lean
theorem StrongSix.M2.strongSixExponentials : StrongSix.StrongSixExponentials
```

with the statement defined in [`StrongSix/Defs.lean`](StrongSix/Defs.lean) (55 lines, worth reading first). The proof
depends only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, no
`axiom` and no `native_decide`.

Independence over ℚ̄ (not ℚ) is essential: L̃ is a ℚ̄-vector space, so x = (1, √2) and y = (log 2, log 3, log 5)
put all six products in L̃.

## Main results

| Result | Lean declaration |
|---|---|
| Roy's strong six exponentials theorem | `StrongSix.M2.strongSixExponentials : StrongSixExponentials` |
| Waldschmidt's transcendence theorem on G_a^{d₀} × G_m^{d₁}, in the form of Roy's Theorem 1 | `StrongSix.M2.waldschmidtTheorem1 : WaldschmidtTheorem1` |
| Philippon's multiplicity estimate with derivatives on G_a^{d₀} × G_m^{d₁}, over any algebraically closed field of characteristic 0 | `StrongSix.M2.multEst_of_isAlgClosed : MultEst K` (and `multEst_Qb` for K = ℚ̄) |
| The six exponentials theorem (Lang, Ramachandra), proved independently | `StrongSix.SixExp.six_exponentials : SixExponentials` |

The statements of Waldschmidt's theorem and of the multiplicity estimate are in
[`StrongSix/Roy/Theorem1.lean`](StrongSix/Roy/Theorem1.lean) and
[`StrongSix/Thm1/MultEst.lean`](StrongSix/Thm1/MultEst.lean); their docstrings give the sources and translate the
statements into the usual mathematical form.

## How the proof goes

The proof has three parts.

1. **Waldschmidt's theorem ⇒ strong six** (`StrongSix/Roy/`, about 2.7k lines). This follows D. Roy, *Matrices whose
   coefficients are linear forms in logarithms*, J. Number Theory 41 (1992), §§1–4: Roy's admissible categories,
   realized as subquotients of a fixed ambient space; his Theorems 1bis and 2bis; and the final contradiction for the
   matrix (xᵢyⱼ).
2. **Multiplicity estimate ⇒ Waldschmidt's theorem** (`StrongSix/Thm1/`, about 3.9k lines). A transcendence proof
   with Laurent's interpolation determinants. If the interpolation matrix has dependent columns, the multiplicity
   estimate gives an obstruction subgroup, which produces the map in Waldschmidt's theorem. Otherwise a nonzero minor
   is bounded above analytically (a Schwarz-type lemma) and below by Liouville's inequality, and the two bounds
   clash for large parameters.
3. **The multiplicity estimate** (`StrongSix/M2/`, about 6.6k lines, plus `StrongSix/CM/`). This follows Roy's
   affine treatment in M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer, 2000),
   Chapters 5 and 8:
   * filtered Hilbert functions on K[X, Y, Z] and their Hilbert dimension and degree;
   * `hdim L + ht L = number of variables`, from Macaulay's unmixedness theorem (`StrongSix/CM/`);
   * a Bézout inequality via complete-intersection chains (Roy's Theorem 8.4);
   * the classification of algebraic subgroups of G_a^{d₀} × G_m^{d₁} (Roy's Proposition 5.6);
   * Wüstholz's lemma by linear algebra (Roy's Lemmas 8.14–8.16, Theorem 8.18). Derivations are applied along
     words, so commutativity of the invariant derivations is never needed;
   * the main argument (Roy §8.4.1), with irreducible components replaced by prime ideals and the Nullstellensatz.

`StrongSix/SixExp/` is a separate, classical proof of the six exponentials theorem; it is not used by the
strong six proof.

## Layout

| Path | Content |
|---|---|
| `StrongSix/Defs.lean` | 𝓛, L̃, ℚ̄-independence, and the statements of six and strong six |
| `StrongSix/Roy/` | Roy's reduction; `Theorem1.lean` states Waldschmidt's theorem, `Final.lean` derives strong six from it |
| `StrongSix/Thm1/` | Waldschmidt's theorem from the multiplicity estimate; `MultEst.lean` states the estimate, `Main.lean` is the proof |
| `StrongSix/M2/` | the multiplicity estimate; `MainB.lean` is the main argument, `Final.lean` the end results |
| `StrongSix/CM/` | Cohen–Macaulay rings and the unmixedness theorem (ported, see below) |
| `StrongSix/SixExp/`, `StrongSix/Analytic/`, `StrongSix/Arith/` | six exponentials, Schwarz lemma, exponential polynomials, Liouville's inequality |
| `Axioms.lean` | `#print axioms` for the main declarations |

## Build and check

Install Lean with [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.35.0`) and Mathlib
(`v4.35.0`) are pinned in `lean-toolchain` and `lake-manifest.json`. Then:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean Axioms.lean
```

Every `#print axioms` line in `Axioms.lean` should report `[propext, Classical.choice, Quot.sound]`.

The kernel checks that the proofs are correct. Whether the theorem is the one you care about depends on the
definitions, so please read `StrongSix/Defs.lean` (and, for the intermediate results, `StrongSix/Roy/Theorem1.lean`
and `StrongSix/Thm1/MultEst.lean`).

## How this was made

The Lean code was written by AI models (Claude, Anthropic) working under the direction of the author. Apart from the
Lean kernel's check, all review so far has been done by AI systems; no human expert has yet reviewed the definitions
or the proofs. Corrections and comments are welcome.

## Third-party code

`StrongSix/CM/` is a port of Nailin Guan and Yongle Hu's Cohen–Macaulay files (arXiv:2510.24818) from
github.com/Thmoas-Guan/mathlib4_fork, branch `ABS-Criterion-Project-new`, commit 0ff6e01f (Apache-2.0). The files
are `Regular/Ischebeck`, `CohenMacaulay/{Basic,Catenary,Unmixed,Polynomial}`, plus lemmas from `Regular/Depth` and
`KrullDimension/Polynomial`, collected in `Compat.lean`. The original copyright headers are kept, and local changes
are marked `PORT`.

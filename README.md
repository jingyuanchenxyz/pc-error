# pc-error — Lean 4 proof of *Principal component error in high-dimensional factor models*

A complete, machine-checked proof of every numbered result of Bernstein, Goldberg, Gunther,
Kercheval, Lan, Lin and Yao, *Principal component error in high-dimensional factor models*
(version of September 14, 2026). Lean 4.28.0, Mathlib v4.28.0.

This is the minimal tree: only what is needed to state and prove the paper. Start from
**[`PAPER-MAP.md`](PAPER-MAP.md)** — it lists every paper result against its Lean declaration
and line number.

## What is proved

> **Assumptions 1–6 of the paper imply its Lemmas 1–6, Propositions 1–3,
> Corollaries 1–3 and Theorems 1–3.**

Nothing else is assumed. The three background facts the proofs use (Kolmogorov's strong law
for non-identically distributed summands, Weyl's inequality, eigenvector continuity) are
absent from Mathlib, so they appear as explicit hypotheses of the statements — never as
`axiom` declarations — and all three are proved in `LatentError/Facts/`.
`Facts/Unconditional.lean` restates the headline results with them discharged.

There is no `sorry` in this tree.

## Verifying it

```sh
lake exe cache get && lake build      # no errors, no sorry
lake env lean notes/Audit.lean        # 34 declarations, each only propext / Classical.choice / Quot.sound
```

The audit is the certificate: it prints the axiom dependencies of every statement. A proof
that used `sorry` anywhere would show `sorryAx`; none does.

## Layout

| Path | Contents |
|---|---|
| `LatentError/Basic.lean` | `sinSq`, `colVec`, `opNorm`, `frobSq`, `Hmat`, and the three background facts as `Prop`s |
| `LatentError/Defs.lean` | The paper's objects: `Y`, `S`, `W`, `ℓ`, `θ`, `W₀`, `λ`, `K`, `Φ̄^∞`, `N`, `M̂`, `Σ_O`, `Q`, `V⁽ᵖ⁾`, sorted spectra |
| `LatentError/Model.lean` | Assumptions 1–6, as `LoadingParams`, `NoiseModel`, `JointModel`, `Assumption5`, `Assumption6` |
| `LatentError/Statements/` | The paper's results: `Appendix.lean` (Lemmas, Propositions, Corollaries 2–3), `Main.lean` (Theorems 1–3, Corollary 1), `Conditional.lean` (§4's conditional reading) |
| `LatentError/Facts/` | The three facts, proved, plus `Unconditional.lean` |
| `LatentError/Lemmas/` | Proof infrastructure — see below |
| `LatentError/Bridge/` | Builds an instance of Ono's `AsymptoticModel` from the paper's assumptions (`exists_model`) |
| `LatentError/Ono/Solution.lean` | Ono's formalization (MIT, © 2026 Axiom Math). **Required**: Theorems 1–2 and Corollary 1 are proved by applying Ono's theorems to the model that `Bridge/Real.lean` constructs |
| `notes/Audit.lean` | The axiom audit |

### `LatentError/Lemmas/`

| File | Contents |
|---|---|
| `Basic.lean` | Adjoints, projectors `Π = bbᵀ`, `sinSq` algebra and continuity |
| `Spectral.lean` | Sorted spectra, Gram duality, simple eigenvalues, Weyl in sorted form |
| `Eigenbasis.lean` | Ordered orthonormal eigenbases; the spectrum of `U diag(d) Uᵀ` |
| `Frames.lean` | The algebra of Proposition 1, via `A = BΣ_f^{1/2}` |
| `Convergence.lean` | Lemma 2; `K⁽ᵖ⁾ → K`; `V⁽ᵖ⁾ → V`, `Φ̄ → Φ̄^∞`, `N⁽ᵖ⁾ → N` |
| `Duality.lean` | `Φ̄^∞ = QF`, the `Q` identities, Corollary 2 |
| `Noise.lean` | Noise moments, the fourth-moment bound, Lemma 4 |
| `Prop3.lean`, `Prop3Leaves.lean` | The averages of `ZᵀZ`, `BᵀZ`, `FFᵀ`; the four-term expansion `W⁽ᵖ⁾ → W` |
| `CondKernel.lean` | Exchange of quantifiers for Mathlib's kernel conditional independence, used by Lemma 5 and §4 |
| `FactorSLLN.lean`, `Lemma5Leaves.lean` | Leaves for the remark after Corollary 3, and for Lemma 5 |
| `Thm3Leaves.lean` | The orthogonal orbit and Householder construction behind Theorem 3 |
| `AlgLeaves.lean`, `ThmLeaves.lean`, `HardLeaves.lean`, `Easy.lean` | Remaining algebraic and scalar leaves |
| `NonVacuity.lean` | Witnesses that the hypothesis bundles are jointly satisfiable |

## Two things a proof assistant does not certify

1. **Fidelity of the translation.** That each Lean statement says what the paper says is a
   human judgement. Each statement carries a docstring restating the result it formalizes, so
   it can be checked by reading; `PAPER-MAP.md` is the index for doing that.
2. **Scope.** Formalized here are the paper's numbered results and the displayed identities
   (16), (20), (25). The prose, the discussion and the §8 simulation study are not.

## Licence

`LatentError/Ono/Solution.lean` is MIT, © 2026 Axiom Math — see `LatentError/Ono/LICENSE`.

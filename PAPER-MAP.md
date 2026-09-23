# Paper ↔ Lean index

Bernstein, Goldberg, Gunther, Kercheval, Lan, Lin & Yao, *Principal component error in
high-dimensional factor models*, version of September 14, 2026.

Every numbered result of the paper appears below exactly once. Each Lean declaration carries
a docstring restating the result, so a file can be read against the paper section by section.

## Main results — `LatentError/Statements/Main.lean`

| Paper | Lean declaration | Line |
|---|---|---|
| Eq. (16)/(24), exact angular split at every `p` | `exact_split` | 40 |
| Eq. (25), projection norms | `eq25_projection_norms` | 56 |
| **Theorem 1**, error decomposition (eqs. 17–19) | `theorem1_error_decomposition` | 190 |
| Eq. (20), the limit in terms of `SNRⱼ` | `thm1Limit_snr` | 289 |
| **Theorem 2**, data-driven estimate of out-of-subspace error (eqs. 38–39) | `theorem2_observable_floor` | 304 |
| **Corollary 1**, aggregate out-of-subspace error (eqs. 40–41) | `corollary1_aggregate` | 373 |
| **Theorem 3**, rotation error is not estimable | `theorem3_rotation_error_not_estimable` | 460 |

## Appendix A–B results — `LatentError/Statements/Appendix.lean`

| Paper | Lean declaration | Line |
|---|---|---|
| **Lemma 1**, Gram duality | `lemma1_gram_duality` | 42 |
| **Lemma 2(i)**, eigenpair convergence | `lemma2_i_eigenpair_convergence` | 57 |
| **Lemma 2(ii)**, sign pinning | `lemma2_ii_sign_pinning` | 72 |
| **Lemma 3**, change of basis | `lemma3_change_of_basis` | 87 |
| **Proposition 1**, principal coordinates and `V⁽ᵖ⁾` (eq. 46) | `prop1_principal_coordinates` | 112 |
| **Proposition 2**, limits of the systematic dual Grams (eqs. 50–51) | `prop2_systematic_limits` | 145 |
| Remark after Prop. 2 (`QΣ̂Qᵀ = N`, `QΣQᵀ = Λ`, `QᵀQ = G_B`) | `prop2_remark` | 173 |
| **Corollary 2**, realized duality (eq. 53) | `cor2_realized_duality` | 185 |
| **Corollary 3**, large-`n` limit of `N` | `cor3_large_n` | 221 |
| Remark after Cor. 3, item 1 (independent factors) | `cor3_remark_independent_factors` | 239 |
| **Lemma 4**, specific-return concentration | `lemma4_specific_concentration` | 260 |
| Prop. 3(b) finite-`p` identity `‖ΠZ‖_F = ‖bᵀZ‖_F` | `prop3_b_frobenius_identity` | 269 |
| **Proposition 3**(a)–(d), limit of the observable dual `W⁽ᵖ⁾` | `prop3_observable_dual` | 284 |
| **Lemma 5**, all-pairs uncorrelatedness | `lemma5_uncorrelated` | 335 |
| **Lemma 6**, indeterminacy of the principal coordinates (eqs. 59–61) | `lemma6_indeterminacy` | 406 |

## Section 4, the conditional-on-`F` reading — `LatentError/Statements/Conditional.lean`

| Paper | Lean declaration | Line |
|---|---|---|
| §4: Assumptions 1–2 give the conditional law used by the headline results | `joint_to_conditional` | 48 |
| §4: path-conditional statements upgrade by the tower property | `tower_upgrade` | 187 |

## The three background facts — `LatentError/Facts/`

Mathlib has none of the three. Following the Ono protocol they are *hypotheses* of the frozen
statements above, never `axiom` declarations — and all three are **proved** here, so nothing
is assumed beyond Assumptions 1–6.

| Fact | Lean declaration | File |
|---|---|---|
| Kolmogorov's strong law, independent non-identically distributed | `fact1_slln` | `Facts/SLLN.lean` (with `Facts/Kronecker.lean`) |
| Weyl's eigenvalue inequality | `fact2_weyl` | `Facts/Weyl.lean` |
| Eigenvector continuity at a simple eigenvalue (never used) | `fact3_eigCont` | `Facts/EigCont.lean` |

`Facts/Unconditional.lean` restates the headline results with all three discharged:
`theorem1_error_decomposition_unconditional` (25), `theorem2_observable_floor_unconditional` (47),
`theorem3_rotation_error_not_estimable_unconditional` (75), `corollary1_aggregate_unconditional` (107),
and the same for Props. 1–3 and Cor. 3.

## Assumptions and objects

| Paper | Lean |
|---|---|
| Standing: `1 ≤ k < n`, loadings nested in `p` | `LoadingParams.hk`, `.hkn` (`Model.lean`) |
| Assumption 1, factor moments | `Sf.PosDef`; joint form in `JointModel` |
| Assumption 2, specific returns (conditional on `F`) | `NoiseModel` |
| Assumption 3, average specific variance → `δ²` | `LoadingParams.A3`, `.δ2_pos` |
| Assumption 4, `BᵀB/p → G_B ≻ 0` | `LoadingParams.A4`, `.GB_posDef` |
| Assumption 5, spectrum of `K` | `Assumption5 Sf GB` |
| Assumption 6, spectrum of `W₀` | `Assumption6 GB F` |
| `Y = BF + Z` (7), `S = YYᵀ/np` (8), `W = YᵀY/np` (11) | `Ymat`, `Scov`, `Wdual` (`Defs.lean`) |
| `ℓ⁽ᵖ⁾` bulk average (37), `θⱼ⁽ᵖ⁾` | `ellBulk`, `theta` |
| `W₀ = FᵀG_BF/n` (12), `λⱼ` | `W0`, `lam` |
| `K(Σ) = Σ^{1/2}G_BΣ^{1/2}`, `Φ̄^∞` (50), `N` (51), `M̂` (58), `Σ_O` (61) | `Kmat`, `PhiBarInf`, `Nlim`, `Mhat`, `SigmaO` |
| `sin²∠(u, col b)` (10) | `sinSqSub` |

## Non-vacuity

`Lemmas/NonVacuity.lean` exhibits `B ≡ 1`, `Σ_f = G_B = 1`, `F = [1 0]` and i.i.d. Rademacher
noise satisfying every hypothesis bundle at once — `loadingParams_nonempty` (59),
`assumptions56_satisfiable` (109), `noiseModel_nonempty` (212) — so no theorem above is
vacuously true. No result depends on these.

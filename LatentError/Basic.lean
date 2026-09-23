import Mathlib

/-!
# Basic vocabulary and the three assumed background facts

The definitions below are copied verbatim from the AxiomProver formalization
(`reference/problem.lean`, Definitions 1–2), moved into the `PCError` namespace so that
our development does not import `LatentError/Ono/Solution.lean`.
`LatentError/OnoCompat.lean` checks by `rfl` that they coincide with Ono's.

Following the Ono protocol, `Fact1_SLLN`, `Fact2_Weyl m`, `Fact3_EigCont m` are
Prop-valued definitions that appear as explicit hypotheses of theorems — never as
axioms, structure fields, or sorried lemmas.  See `notes/mathlib-inventory.md` for why
these three are assumed (they are absent from Mathlib v4.28.0).
-/

open scoped BigOperators Topology Matrix MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace PCError

/-! ## Definition 1 (Sign-free acute angle between lines). -/

/-- The squared sine of the acute angle between the lines spanned by nonzero
`u, v ∈ ℝ^m`:  `sin²∠(u, v) := 1 − ⟨u, v⟩² / (‖u‖² ‖v‖²)`.  This is invariant under
`u ↦ ±u`, `v ↦ ±v` and under positive rescaling; for unit vectors it reduces to
`1 − ⟨u, v⟩²`. -/
def sinSq {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) : ℝ :=
  1 - (inner ℝ u v) ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

/-- The `j`-th column of a matrix, viewed as a Euclidean vector. -/
def colVec {p k : ℕ} (M : Matrix (Fin p) (Fin k) ℝ) (j : Fin k) :
    EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (fun i => M i j)

/-- The operator (spectral, L2) norm of a square matrix. -/
def opNorm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- The squared Frobenius norm `‖M‖_F² = Σᵢⱼ Mᵢⱼ²`. -/
def frobSq {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) : ℝ := ∑ i, ∑ j, (M i j) ^ 2

/-- Assemble the `p × k` matrix `H = [h₁ ⋯ h_k]` whose `j`-th column is `hⱼ`. -/
def Hmat {p k : ℕ} (hh : Fin k → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin k) ℝ :=
  Matrix.of (fun i j => (hh j) i)

/-! ## Definition 2 (The three assumed background facts).

These are stated exactly as classical propositions and appear as explicit
hypotheses of each theorem below.  They are NOT axioms or sorried lemmas. -/

/-- **Fact 1 (Kolmogorov SLLN for independent, non-identically distributed
summands).** For independent real random variables `{Xᵢ}_{i≥1}` with finite
variances satisfying Kolmogorov's series condition `Σ_{i=1}^∞ Var(Xᵢ)/i² < ∞`, the
centered average `(1/p) Σ_{i=1}^p (Xᵢ − E[Xᵢ])` tends to `0` almost surely as
`p → ∞`.  The sum runs over `i ∈ {1, …, p}` exactly (`Finset.Icc 1 p`), matching
the source `(1/p) Σ_{i=1}^p`. -/
def Fact1_SLLN : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, MemLp (X i) 2 μ) →
    iIndepFun X μ →
    Summable (fun i : ℕ => variance (X i) μ / ((i : ℝ)) ^ 2) →
    ∀ᵐ ω ∂μ, Tendsto
      (fun p : ℕ => (1 / (p : ℝ)) *
        ∑ i ∈ Finset.Icc 1 p, (X i ω - μ[X i]))
      atTop (𝓝 0)

/-- **Fact 2 (Weyl's eigenvalue perturbation inequality), at dimension `m`.** For
real symmetric `A, A'` and every eigenvalue index `i`, `|λᵢ(A') − λᵢ(A)| ≤
‖A' − A‖_op`, where the eigenvalues at each index are taken in *weakly decreasing
order* `λ₁ ≥ ⋯ ≥ λ_m`.  Here `σ` (resp. `σ'`) is *the* weakly decreasing
eigenvalue list of `A` (resp. `A'`): it is `Antitone` and equals Mathlib's
`eigenvalues` up to a reindexing permutation `e` (resp. `e'`), so the statement
pins down the required sorted convention.  (The stated consequence -- `A^{(p)} → A`
implies `λᵢ(A^{(p)}) → λᵢ(A)` for every `i` -- follows from this inequality.) -/
def Fact2_Weyl (m : ℕ) : Prop :=
  ∀ (A A' : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    (σ σ' : Fin m → ℝ) (e e' : Fin m ≃ Fin m),
    Antitone σ → Antitone σ' →
    (σ = fun i => hA.eigenvalues (e i)) → (σ' = fun i => hA'.eigenvalues (e' i)) →
    ∀ i : Fin m, |σ' i - σ i| ≤ opNorm (A' - A)

/-- **Fact 3 (Eigenvector continuity for a simple eigenvalue), at dimension `m`.**
If real symmetric `A^{(p)} → A` and `μ` is a simple eigenvalue of `A` with unit
eigenvector `v`, then there exist `μ^{(p)} ∈ ℝ` and unit `v^{(p)}` with, for all
large `p`, `A^{(p)} v^{(p)} = μ^{(p)} v^{(p)}`, `‖v^{(p)}‖ = 1`,
`⟨v^{(p)}, v⟩ ≥ 0`, and `μ^{(p)} → μ`, `v^{(p)} → v`. -/
def Fact3_EigCont (m : ℕ) : Prop :=
  ∀ (A : ℕ → Matrix (Fin m) (Fin m) ℝ) (Ainf : Matrix (Fin m) (Fin m) ℝ),
    (∀ p, (A p).IsHermitian) → Ainf.IsHermitian →
    Tendsto A atTop (𝓝 Ainf) →
    ∀ (μ : ℝ) (v : EuclideanSpace ℝ (Fin m)),
      ‖v‖ = 1 → Matrix.toEuclideanLin Ainf v = μ • v →
      (∀ w : EuclideanSpace ℝ (Fin m), ‖w‖ = 1 →
        Matrix.toEuclideanLin Ainf w = μ • w → w = v ∨ w = -v) →
      ∃ (μ' : ℕ → ℝ) (v' : ℕ → EuclideanSpace ℝ (Fin m)),
        (∀ᶠ p in atTop,
          Matrix.toEuclideanLin (A p) (v' p) = μ' p • v' p ∧
          ‖v' p‖ = 1 ∧ 0 ≤ (inner ℝ (v' p) v : ℝ)) ∧
        Tendsto μ' atTop (𝓝 μ) ∧ Tendsto v' atTop (𝓝 v)

end PCError

end
